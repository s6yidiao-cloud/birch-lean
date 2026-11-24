import Birch.FinalFormGradient
import Birch.V2CoverAsymptotic
import Birch.V2CoverFromWooley
import Birch.V2CoverSerre

/-! # Polynomial covers

The Serre bound counts integral pairs, with no cutoff on the cover variable.
The weighted asymptotic uses the signed cutoff `|y| ≤ B^(d/e)` and the
singular factors of the manuscript. Both use Deligne's prime-field estimate.
-/

open Filter MeasureTheory
open scoped Polynomial Topology

namespace Birch

noncomputable section

/-- The integral-pair estimate of `thm:serre` in the manuscript. -/
def FinalCoverSerreBound : Prop :=
  ∀ (d e n : ℕ) (F : IntForm n) (g : ℤ[X]) (σ : ℕ),
    2 ≤ d → 2 ≤ e → F ≠ 0 → F.IsHomogeneous d → g.natDegree = e →
    RationalGradientDimension F σ →
    (dimensionThreshold d : ℝ) * (1 / (d : ℝ) + 1 / (2 * (e : ℝ))) ≤ (n - σ : ℕ) →
    ∀ ε > 0, ∃ C > 0, ∀ᶠ B : ℝ in atTop,
      (coverIntegralCount F g B : ℝ) ≤ C * B ^ ((n : ℝ) - 1 + ε)

/-- The weighted asymptotic of `thm:cover_asymptotic` in the manuscript,
including absolute convergence of its singular factors. -/
def FinalCoverAsymptotic : Prop :=
  ∀ (d e n : ℕ) (F : IntForm n) (g : ℤ[X]) (σ : ℕ) (w : (Fin n → ℝ) → ℝ),
    2 ≤ d → 2 ≤ e → F ≠ 0 → F.IsHomogeneous d → g.natDegree = e →
    RationalGradientDimension F σ →
    (dimensionThreshold d : ℝ) * (1 - 1 / (coverMomentExponent e : ℝ)) < (n - σ : ℕ) →
    FinalWeight w → HasNonvanishingGradientOnSupport F w →
    Summable (fun q : ℕ => coverConductorMass F g (q + 1)) ∧
    Integrable (fun γ => realOscillation F w γ * coverRealOscillation g e γ) ∧
    ∃ η > 0, ∃ C > 0, ∀ᶠ B : ℝ in atTop,
      ‖(coverWeightedZeros d e F g w B : ℂ) -
        (B ^ ((n : ℝ) + (d : ℝ) / e - d) : ℝ) •
          (coverSingularSeries F g * coverSingularIntegral F g e w)‖ ≤
      C * B ^ ((n : ℝ) + (d : ℝ) / e - d - η)

/-- Deligne's estimate implies the Serre bound for integral pairs at the
closed codimension threshold. -/
theorem finalCoverSerreBound
    (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) : FinalCoverSerreBound := by
  intro d e n F g σ hd he _ hF hg hσ hν
  apply coverIntegralCount_serre_of_weilII hd he hF hg hσ
  · simpa only [mul_comm] using hν
  · exact fun r hr _ => hDeligne r hr

/-- Deligne's estimate implies the weighted cover asymptotic at the
strict codimension threshold with the manuscript's moment exponent. -/
theorem finalCoverAsymptotic
    (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) : FinalCoverAsymptotic := by
  intro d e n F g σ w hd he hne hF hg hσ hν hw _
  have hmoment : ∀ g' : ℤ[X], g'.natDegree = e → CoverMeanValueBound e g' := by
    intro g' hg'
    by_cases hsmall : e ≤ 4
    · exact coverMeanValueBound_of_degree_le_four he hsmall hg'
    · have hlarge : 5 ≤ e := by omega
      exact coverMeanValueBound_of_criticalVinogradov hlarge hg'
        (criticalVinogradovEstimate_of_wooley (by omega))
  obtain ⟨η, hη, h⟩ := v2CoverCubeAsymptoticAt_of_weilII_of_coverMoment (n := n) hd he
    (fun r hr _ => hDeligne r hr) hmoment
  rw [mul_comm] at hν
  obtain ⟨hseries, hintegral, C, hC, herr⟩ :=
    h F g σ w hne hF hg hσ hν hw.toCompactWeight hw.cubeSupported 1 zero_lt_one
  refine ⟨hseries, hintegral, η, hη, C, hC, ?_⟩
  filter_upwards [herr, eventually_gt_atTop (0 : ℝ)] with B hB hBpos
  have hcount : coverWeightedZeros d e F g w B =
      coverWeightedBoxZeros F g w B (B ^ ((d : ℝ) / e)) := by
    simpa only [Real.one_rpow, one_mul, one_smul] using
      coverWeightedZeros_eq_box_rescale (d := d) (e := e) F g w zero_lt_one hBpos
        (fun x hx i => (hw.cubeSupported x hx i).le)
  rw [hcount]
  simpa only [one_mul, coverSingularIntegralOn, coverSingularIntegral,
    coverRealOscillationOn, coverRealOscillation] using hB

end

end Birch
