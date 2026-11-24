import Birch.V2CoverMoments
import Birch.V2CoverRescaling

/-! # Combining the cover arc estimates and undoing compact-weight rescaling -/

open Filter MeasureTheory
open scoped Polynomial Topology

namespace Birch

noncomputable section

/-- The two estimates on complementary arcs give the weighted-box
asymptotic with the smaller of the two savings. -/
theorem coverWeightedBoxAsymptotic_of_arcIntegrals {d e n : ℕ} {F : IntForm n} {g : ℤ[X]}
    {w : (Fin n → ℝ) → ℝ} {B δ₁ δ₂ : ℝ} :
    let Δ := coverMajorArcExponent d e
    let T := fun P => coverYSum g (B * P ^ ((d : ℝ) / e))
    let A := coverSingularSeries F g * coverSingularIntegralOn F g e w B
    (∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (∫ α in (v2MajorArcs d Δ P)ᶜ, ‖normalizedSum F w P α * T P α‖ ∂circleMeasure) ≤
        C * P ^ ((d : ℝ) / e - d - δ₁)) →
    (∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(∫ α in v2MajorArcs d Δ P, normalizedSum F w P α * T P α ∂circleMeasure) -
        (P ^ ((d : ℝ) / e - d) : ℝ) • A‖ ≤ C * P ^ ((d : ℝ) / e - d - δ₂)) →
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(coverWeightedBoxZeros F g w P (B * P ^ ((d : ℝ) / e)) : ℂ) -
        (P ^ ((n : ℝ) + (d : ℝ) / e - d) : ℝ) • A‖ ≤
        C * P ^ ((n : ℝ) + (d : ℝ) / e - d - min δ₁ δ₂) := by
  dsimp only
  rintro ⟨C, hC, hminor⟩ ⟨D, hD, hmajor⟩
  refine ⟨C + D, add_pos hC hD, ?_⟩
  filter_upwards [hminor, hmajor, eventually_ge_atTop (1 : ℝ)] with P hminor hmajor hP
  have hp : 0 < P := zero_lt_one.trans_le hP
  let r := (d : ℝ) / e - d
  let A := coverSingularSeries F g * coverSingularIntegralOn F g e w B
  let M := v2MajorArcs d (coverMajorArcExponent d e) P
  let T := coverYSum g (B * P ^ ((d : ℝ) / e))
  let U := fun α => normalizedSum F w P α * T α
  let W := (coverWeightedBoxZeros F g w P (B * P ^ ((d : ℝ) / e)) : ℂ)
  have hU : Continuous U :=
    ((continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)).mul (continuous_coverYSum g _)
  have hi : Integrable U circleMeasure := hU.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hm : MeasurableSet M := measurableSet_v2MajorArcs _ _ _
  have hsum : ‖(∫ α, U α ∂circleMeasure) - (P ^ r : ℝ) • A‖ ≤
      (C + D) * P ^ (r - min δ₁ δ₂) := by
    rw [← integral_add_compl hm hi, add_sub_right_comm]
    apply (norm_add_le _ _).trans
    rw [add_mul, add_comm (C * _)]
    exact add_le_add
      (hmajor.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith [min_le_right δ₁ δ₂])) hD.le))
      ((norm_integral_le_integral_norm _).trans (hminor.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith [min_le_left δ₁ δ₂])) hC.le)))
  have heq : (∫ α, U α ∂circleMeasure) = (P ^ (-(n : ℝ)) : ℝ) • W := by
    dsimp only [U, normalizedSum, T, W]
    simp_rw [smul_mul_assoc]
    rw [integral_smul, integral_exponentialSum_mul_coverYSum]
  rw [heq] at hsum
  have hnorm : (P ^ (n : ℝ) : ℝ) •
      ((P ^ (-(n : ℝ)) : ℝ) • W - (P ^ r : ℝ) • A) =
      W - (P ^ ((n : ℝ) + (d : ℝ) / e - d) : ℝ) • A := by
    rw [smul_sub, smul_smul, smul_smul, ← Real.rpow_add hp, add_neg_cancel, Real.rpow_zero,
      one_smul, ← Real.rpow_add hp]
    congr 3
    dsimp [r]
    ring
  change ‖W - (P ^ ((n : ℝ) + (d : ℝ) / e - d) : ℝ) • A‖ ≤ _
  rw [← hnorm, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
  refine (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hp.le _)).trans_eq ?_
  rw [mul_left_comm, ← Real.rpow_add hp]
  congr 2
  dsimp [r]
  ring

/-- The unit-cube asymptotic with a specified moment exponent, for every
fixed multiplier of the natural interval length. -/
def V2CoverCubeAsymptoticAtExponent (d e n q : ℕ) : Prop :=
    ∃ δ > 0,
      ∀ (F : IntForm n) (g : ℤ[X]) (σ : ℕ) (w : (Fin n → ℝ) → ℝ),
        F ≠ 0 → F.IsHomogeneous d → g.natDegree = e → RationalGradientDimension F σ →
        (1 - 1 / (q : ℝ)) * dimensionThreshold d < (n - σ : ℕ) →
        CompactWeight w → CubeSupported w → ∀ B > 0,
        Summable (fun q : ℕ => coverConductorMass F g (q+1)) ∧
        Integrable (fun γ => realOscillation F w γ * coverRealOscillationOn g e B γ) ∧
        ∃ C > 0, ∀ᶠ P : ℝ in atTop,
          ‖(coverWeightedBoxZeros F g w P (B * P ^ ((d : ℝ) / e)) : ℂ) -
            (P ^ ((n : ℝ) + (d : ℝ) / e - d) : ℝ) •
              (coverSingularSeries F g * coverSingularIntegralOn F g e w B)‖ ≤
          C * P ^ ((n : ℝ) + (d : ℝ) / e - d - δ)

/-- The unit-cube asymptotic with the moment exponent selected in the manuscript. -/
def V2CoverCubeAsymptoticAt (d e n : ℕ) : Prop :=
  V2CoverCubeAsymptoticAtExponent d e n (coverMomentExponent e)

end

end Birch
