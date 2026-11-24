import Birch.V2FormAsymptotic

/-! # Form results

The weighted formula uses the strict codimension case of the circle-method
argument. The Hasse principle follows by choosing a weight near a nonsingular
real zero and using positivity of the local factors.
-/

open Filter MeasureTheory
open scoped Topology

namespace Birch

noncomputable section

/-- A smooth `[0,1]`-valued weight compactly supported in the open unit cube. -/
structure FinalWeight {n : ℕ} (w : (Fin n → ℝ) → ℝ) : Prop extends CompactWeight w where
  bounded : ∀ x, w x ≤ 1
  support_box : ∀ x ∈ tsupport w, ∀ i, |x i| < 1

theorem FinalWeight.cubeSupported {n : ℕ} {w : (Fin n → ℝ) → ℝ} (hw : FinalWeight w) :
    CubeSupported w := fun x hx => hw.support_box x (subset_tsupport w hx)

/-- The weighted form formula for a weight with one fixed nonvanishing partial derivative.
The series converges absolutely over the reduced numerators, and the saving depends only on `d,n`. -/
def FixedPartialFormAsymptotic : Prop :=
  ∀ d n : ℕ, 2 ≤ d → ∃ η > 0, ∀ (F : IntForm n) (σ : ℕ) (w : (Fin n → ℝ) → ℝ),
    F ≠ 0 → F.IsHomogeneous d → RationalGradientDimension F σ → 2 ^ (d + 1) - 3 ≤ n - σ →
    FinalWeight w → HasTransverseSupport F w →
    Summable (fun q : ℕ => formConductorMass F (q + 1)) ∧ Integrable (realOscillation F w) ∧
    ∃ C > 0, ∀ᶠ B : ℝ in atTop,
      ‖(compactWeightedZeros F w B : ℂ) -
        (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * B ^ ((n : ℝ) - d - η)

/-- Theorem `thm:main` of the manuscript for the affine gradient codimension. -/
def FinalSmoothHassePrinciple : Prop :=
  ∀ (d n : ℕ) (F : IntForm n) (σ : ℕ), 2 ≤ d →
    F ≠ 0 → F.IsHomogeneous d → RationalGradientDimension F σ → 2 ^ (d + 1) - 3 ≤ n - σ →
    SmoothHassePrinciple F

private theorem finalFormThreshold_iff {d n σ : ℕ} (hd : 2 ≤ d) :
    2 ^ (d + 1) - 3 ≤ n - σ ↔ dimensionThreshold d < n - σ := by
  have hpow : 4 ≤ 2 ^ (d + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ d + 1 by omega)
  unfold dimensionThreshold
  omega

private theorem finalWeight_full_count_eq {n : ℕ} (F : IntForm n) {w : (Fin n → ℝ) → ℝ}
    (hw : FinalWeight w) {B : ℝ} (hB : 0 < B) :
    compactWeightedZeros F w B = weightedZeros F w B := by
  simpa only [one_mul, weightedZeros] using compactWeightedZeros_eq_box F w hB
    (R := 1) (fun x hx i => (hw.cubeSupported x hx i).le)

/-- The weighted form asymptotic from the prime-field Deligne bound, using the
unit-cube form of the strict-threshold argument. -/
theorem fixedPartialFormAsymptotic_of_deligne
    (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) : FixedPartialFormAsymptotic := by
  intro d n hd
  let saving (σ : ℕ) := if dimensionThreshold d < n - σ then v2FormSaving d (n - σ) else 1
  let dims := Finset.range (n + 1)
  have hne : dims.Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ n)⟩
  refine ⟨dims.inf' hne saving, (Finset.lt_inf'_iff hne).2 ?_, ?_⟩
  · intro σ _
    by_cases hσ : dimensionThreshold d < n - σ
    · simpa [saving, hσ] using v2FormSaving_pos hd hσ
    · simp [saving, hσ]
  · intro F σ w _ hF hσ hthreshold hw htrans
    have hν := (finalFormThreshold_iff hd).mp hthreshold
    have hσmem : σ ∈ dims := Finset.mem_range.mpr (by omega)
    have hη : dims.inf' hne saving ≤ v2FormSaving d (n - σ) := by
      simpa [saving, hν] using Finset.inf'_le saving hσmem
    have hterminal : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r := fun r hr _ => hDeligne r hr
    obtain ⟨hmass, hI, C, hC, herror⟩ := v2CubeFormAsymptotic_of_weilII hd hF hσ hν
      hw.toCompactWeight hw.cubeSupported htrans hterminal
    refine ⟨hmass, hI, C, hC, ?_⟩
    filter_upwards [herror, eventually_ge_atTop (1 : ℝ)] with B hB hB₁
    rw [finalWeight_full_count_eq F hw (zero_lt_one.trans_le hB₁)]
    exact hB.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB₁ (sub_le_sub_left hη _)) hC.le)

private theorem finalSmoothHassePrinciple_of_formAsymptotic (h : FixedPartialFormAsymptotic) :
    FinalSmoothHassePrinciple := by
  intro d n F σ hd hFne hF hσ hν hloc
  obtain ⟨w, hw⟩ := exists_transverseWeight_of_nonsingularZero (by omega) hF hloc.1
  have hwFinal : FinalWeight w :=
    ⟨⟨hw.smooth, hw.compact, hw.nonnegative⟩, hw.bounded, hw.support_box⟩
  have htrans : HasTransverseSupport F w := by
    obtain ⟨i, c, hc, hi⟩ := hw.transverse
    exact ⟨i, fun x hx => abs_pos.mp (hc.trans_le (hi x hx))⟩
  obtain ⟨η, hη, hbound⟩ := h d n hd
  obtain ⟨hmass, _, C, hC, herror⟩ := hbound F σ w hFne hF hσ hν hwFinal htrans
  have hn : 0 < n := by
    have hstrict := (finalFormThreshold_iff hd).mp hν
    omega
  obtain ⟨hSpos, hSim⟩ := singularSeries_positive_of_nonsingularZeros F hn hF hloc.2
    (summable_norm_unitConductorSum_of_formConductorMass hmass)
  have hIpos := singularIntegral_pos_of_compact_transverse hw.smooth hw.compact
    hw.nonnegative htrans hw.positive_at_zero
  have hmain : 0 < (singularSeries F * singularIntegral F w).re := by
    simpa [Complex.mul_re, hSim] using mul_pos hSpos hIpos
  have herr : ∀ᶠ B : ℝ in atTop,
      ‖(weightedZeros F w B : ℂ) -
        (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * B ^ ((n : ℝ) - d - η) := by
    filter_upwards [herror, eventually_gt_atTop (0 : ℝ)] with B hB hB₀
    rwa [finalWeight_full_count_eq F hwFinal hB₀] at hB
  obtain ⟨B, hB⟩ := (eventually_weightedZeros_pos_of_asymptotic (d := d) hmain hη hC herr).exists
  exact hasNonsingularZero_rat_of_weightedZeros_pos hF htrans hB

/-- The smooth Hasse principle under the same prime-field Deligne estimate. -/
theorem finalSmoothHassePrinciple
    (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) : FinalSmoothHassePrinciple :=
  finalSmoothHassePrinciple_of_formAsymptotic (fixedPartialFormAsymptotic_of_deligne hDeligne)

end

end Birch
