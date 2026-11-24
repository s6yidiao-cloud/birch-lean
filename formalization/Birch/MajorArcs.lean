import Birch.SingularSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Major-arc tails

The integrated Poisson expansion is an explicit input. The estimates here
extend the conductor and frequency cutoffs to the full singular factors.
-/

namespace Birch

open scoped BigOperators Topology
open Set Filter MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The truncated sum of the leading Poisson terms on the major arcs.
The index `j` represents the conductor `j+1`. -/
def majorArcTruncation (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (P : ℝ) : ℂ :=
  ∑ j ∈ Finset.range ⌊P ^ (1 / 2 : ℝ)⌋₊,
    unitConductorSum F (j+1) *
      ∫ γ in Icc (-(P ^ (7/8 : ℝ) / (j+1 : ℕ))) (P ^ (7/8 : ℝ) / (j+1 : ℕ)),
        realOscillation F w γ

/-- The integrated leading-term expansion with an arbitrary power-saving error.
The expansion uses the normalized exponential sum. -/
def IntegratedMajorArcExpansion (d : ℕ) (F : IntForm n)
    (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ L > (0 : ℝ), ∃ E > (0 : ℝ), ∀ᶠ P in atTop,
    ‖(∫ α in majorArcs d P, normalizedSum F w P α ∂circleMeasure) -
      (P ^ (-(d : ℝ)) : ℝ) • majorArcTruncation F w P‖ ≤
        E * P ^ (-(d : ℝ) - L)

private theorem summable_norm_of_conductor_power {A : ℕ → ℂ} {κ C : ℝ}
    (hκ : 2 < κ) (hA : ∀ j : ℕ, ‖A j‖ ≤ C * ((j+1 : ℕ) : ℝ)^(1-κ)) :
    Summable (fun j : ℕ => ‖A j‖) := by
  have h : Summable (fun j : ℕ => ((j+1 : ℕ) : ℝ)^(1-κ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))
  exact (h.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hA

private theorem conductor_power_tail {A : ℕ → ℂ} {κ C : ℝ}
    (hκ : 2 < κ) (hC : 0 ≤ C) (hA : ∀ j : ℕ, ‖A j‖ ≤ C * ((j+1 : ℕ) : ℝ)^(1-κ))
    (Q : ℕ) (hQ : 1 ≤ Q) :
    ‖(∑' j : ℕ, A j) - ∑ j ∈ Finset.range Q, A j‖ ≤
      C / (κ-2) * (Q : ℝ)^(2-κ) := by
  have hs := summable_norm_of_conductor_power hκ hA
  have htail : Summable (fun j : ℕ => ‖A (j+Q)‖) := (summable_nat_add_iff Q).2 hs
  have hpowers : Summable (fun j : ℕ => ((j+Q+1 : ℕ) : ℝ)^(1-κ)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (Q+1)).2 ((Real.summable_nat_rpow (p := 1-κ)).2 (by linarith))
  rw [← hs.of_norm.sum_add_tsum_nat_add Q, add_sub_cancel_left]
  calc
    _ ≤ ∑' j : ℕ, ‖A (j+Q)‖ := norm_tsum_le_tsum_norm htail
    _ ≤ ∑' j : ℕ, C * ((j+Q+1 : ℕ) : ℝ)^(1-κ) :=
      htail.tsum_le_tsum (fun j => hA (j+Q)) (hpowers.mul_left C)
    _ = C * ∑' j : ℕ, ((j+Q+1 : ℕ) : ℝ)^(1-κ) := tsum_mul_left
    _ ≤ C * ∫ x : ℝ in Ioi (Q : ℝ), x^(1-κ) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hQ' : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
      apply AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x^(1-κ)) Q
      · intro x hx y _ hxy
        exact Real.rpow_le_rpow_of_nonpos (hQ'.trans_le hx) hxy (by linarith)
      · exact integrableOn_Ioi_rpow_of_lt (by linarith) hQ'
      · intro x hx
        exact Real.rpow_nonneg (le_of_lt (hQ'.trans hx)) _
    _ = _ := by
      have hQ' : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
      rw [integral_Ioi_rpow_of_lt (show 1-κ < -1 by linarith) hQ',
        show 1-κ+1 = 2-κ by ring, show 2-κ = -(κ-2) by ring, div_neg]
      simp only [neg_div, neg_neg]
      ring

private theorem oscillation_tail {I : ℝ → ℂ} (hI : Integrable I) {D T : ℝ}
    (hD : 0 ≤ D) (hT : 0 < T)
    (hDecay : ∀ t : ℝ, ‖I t‖ ≤ D * (1 + |t|)^(-4 : ℝ)) :
    ‖(∫ t in Icc (-T) T, I t) - ∫ t, I t‖ ≤ (2*D/3) * T^(-3 : ℝ) := by
  have hpInt : IntegrableOn (fun x : ℝ => D * x^(-4 : ℝ)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hT).const_mul D
  have hpower : (∫ t in Ioi T, D * t^(-4 : ℝ)) = (D/3) * T^(-3 : ℝ) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hT]
    norm_num
    ring
  have hplus : (∫ t in Ioi T, ‖I t‖) ≤ (D/3) * T^(-3 : ℝ) := by
    rw [← hpower]
    apply setIntegral_mono_on hI.norm.integrableOn hpInt measurableSet_Ioi
    intro t ht
    have ht' : 0 < t := hT.trans ht
    have h := hDecay t
    rw [abs_of_pos ht'] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht' (by linarith) (by norm_num)) hD)
  have hneg : (∫ t in Iio (-T), ‖I t‖) ≤ (D/3) * T^(-3 : ℝ) := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi, ← hpower]
    have hIn : Integrable (fun t : ℝ => ‖I (-t)‖) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hI.norm
    apply setIntegral_mono_on hIn.integrableOn hpInt measurableSet_Ioi
    intro t ht
    have ht' : 0 < t := hT.trans ht
    have h := hDecay (-t)
    rw [abs_neg, abs_of_pos ht'] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ht' (by linarith) (by norm_num)) hD)
  rw [← integral_add_compl measurableSet_Icc hI, sub_add_cancel_left, norm_neg]
  calc
    _ ≤ ∫ t in (Icc (-T) T)ᶜ, ‖I t‖ := norm_integral_le_integral_norm _
    _ = (∫ t in Iio (-T), ‖I t‖) + ∫ t in Ioi T, ‖I t‖ := by
      have hcompl : (Icc (-T) T)ᶜ = Iio (-T) ∪ Ioi T := by
        ext t
        simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
      have hd : Disjoint (Iio (-T)) (Ioi T) := by
        refine Set.disjoint_left.2 (fun {t} ht₁ ht₂ => ?_)
        have hx₁ : t < -T := ht₁
        have hx₂ : T < t := ht₂
        linarith
      rw [hcompl, setIntegral_union hd measurableSet_Ioi hI.norm.integrableOn hI.norm.integrableOn]
    _ ≤ (D/3)*T^(-3 : ℝ) + (D/3)*T^(-3 : ℝ) := add_le_add hneg hplus
    _ = _ := by ring


private theorem conductor_cutoff_power_le {κ P σ : ℝ} (hσ : 0 < σ) (hσ₁ : σ ≤ 1)
    (hσκ : σ ≤ (κ-2)/2) (hP : 1 ≤ P) :
    (⌊P ^ (1/2 : ℝ)⌋₊ : ℝ)^(2-κ) ≤ 4 * P^(-σ) := by
  let Q := ⌊P ^ (1/2 : ℝ)⌋₊
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hbase : 1 ≤ P ^ (1/2 : ℝ) := Real.one_le_rpow hP (by norm_num)
  have hQN : 1 ≤ Q := Nat.le_floor (by simpa using hbase)
  have hQ : 1 ≤ (Q : ℝ) := by exact_mod_cast hQN
  have hQ2 : P ^ (1/2 : ℝ) / 2 ≤ (Q : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (P ^ (1/2 : ℝ))
    change P ^ (1/2 : ℝ) < (Q : ℝ) + 1 at hfloor
    linarith
  calc
    (Q : ℝ)^(2-κ) ≤ (Q : ℝ)^(-2 * σ) :=
      Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
    _ ≤ (P ^ (1/2 : ℝ) / 2)^(-2 * σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hQ2 (by linarith)
    _ = (2 : ℝ)^(2 * σ) * P^(-σ) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hp.le,
        show (1/2 : ℝ)*(-2 * σ) = -σ by ring,
        show -2 * σ = -(2 * σ) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
    _ ≤ 4 * P^(-σ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        (2 : ℝ)^(2 * σ) ≤ (2 : ℝ)^(2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num [Real.rpow_two]

/-- The error when the conductor cutoff already has the needed power saving. -/
private theorem majorArcTruncation_error_of_tail_atScale {σ K D : ℝ} (hσ₁ : σ ≤ 1) (hD : 0 ≤ D)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hs : Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖))
    (hI : Integrable (realOscillation F w))
    (hDecay : ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ))
    (P : ℝ) (hP : 1 ≤ P)
    (hTail : ‖(∑ j ∈ Finset.range ⌊P^(1/2 : ℝ)⌋₊, unitConductorSum F (j+1)) -
      singularSeries F‖ ≤ K * P^(-σ)) :
    ‖majorArcTruncation F w P - singularSeries F * singularIntegral F w‖ ≤
      (((2*D/3) * (∑' j : ℕ, ‖unitConductorSum F (j+1)‖)) +
        K * ‖singularIntegral F w‖) * P^(-σ) := by
  let Q := ⌊P^(1/2 : ℝ)⌋₊
  let A (j : ℕ) := unitConductorSum F (j+1)
  let I := realOscillation F w
  let J := singularIntegral F w
  let Jcut (j : ℕ) := ∫ t in Icc (-(P^(7/8 : ℝ) / (j+1 : ℕ))) (P^(7/8 : ℝ) / (j+1 : ℕ)), I t
  let S := singularSeries F
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hf : (Q : ℝ) ≤ P^(1/2 : ℝ) := Nat.floor_le (by positivity)
  have hJcut (j : ℕ) (hj : j ∈ Finset.range Q) :
      ‖Jcut j - J‖ ≤ (2*D/3) * P^(-σ) := by
    have hj1 : (0 : ℝ) < ((j+1 : ℕ) : ℝ) := by positivity
    have hj2 : ((j+1 : ℕ) : ℝ) ≤ P^(1/2 : ℝ) :=
      (Nat.cast_le.mpr (Nat.succ_le_of_lt (Finset.mem_range.mp hj))).trans hf
    have ht : P^(3/8 : ℝ) ≤ P^(7/8 : ℝ) / ((j+1 : ℕ) : ℝ) := by
      apply (le_div_iff₀ hj1).2
      calc
        _ ≤ P^(3/8 : ℝ) * P^(1/2 : ℝ) := mul_le_mul_of_nonneg_left hj2 (by positivity)
        _ = _ := by rw [← Real.rpow_add hp]; norm_num
    have hnorm := oscillation_tail hI hD (by positivity : 0 < P^(7/8 : ℝ) / ((j+1 : ℕ) : ℝ)) hDecay
    refine hnorm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    calc
      _ ≤ (P^(3/8 : ℝ))^(-3 : ℝ) := Real.rpow_le_rpow_of_nonpos (by positivity) ht (by norm_num)
      _ ≤ P^(-σ) := by
        rw [← Real.rpow_mul hp.le]
        exact Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hSum :
      ‖∑ j ∈ Finset.range Q, A j * (Jcut j - J)‖ ≤
        ((2*D/3) * (∑' j, ‖A j‖)) * P^(-σ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range Q, ‖A j * (Jcut j - J)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range Q, ‖A j‖ * ((2*D/3) * P^(-σ)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hJcut j hj) (norm_nonneg _)
      _ = (∑ j ∈ Finset.range Q, ‖A j‖) * ((2*D/3) * P^(-σ)) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (∑' j, ‖A j‖) * ((2*D/3) * P^(-σ)) :=
        mul_le_mul_of_nonneg_right
          (hs.sum_le_tsum (Finset.range Q) (fun _ _ => norm_nonneg _)) (by positivity)
      _ = _ := by ring
  have hsplit :
      majorArcTruncation F w P - S * J =
        (∑ j ∈ Finset.range Q, A j * (Jcut j - J)) + ((∑ j ∈ Finset.range Q, A j) - S) * J := by
    change (∑ j ∈ Finset.range Q, A j * Jcut j) - S*J = _
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sub_mul]
    ring
  rw [hsplit]
  calc
    _ ≤ ‖∑ j ∈ Finset.range Q, A j * (Jcut j - J)‖ + ‖((∑ j ∈ Finset.range Q, A j) - S) * J‖ :=
      norm_add_le _ _
    _ ≤ (((2*D/3) * (∑' j, ‖A j‖)) * P^(-σ)) +
          ((K * P^(-σ)) * ‖J‖) := by
      rw [norm_mul]
      exact add_le_add hSum (mul_le_mul_of_nonneg_right hTail (norm_nonneg _))
    _ = _ := by
      change _ = (((2*D/3) * (∑' j, ‖A j‖)) + K * ‖J‖) * P^(-σ)
      ring

/-- A power bound for the absolute conductor tail suffices to extend both cutoffs. -/
theorem majorArcTruncation_error_of_absoluteTail {γ C D : ℝ}
    (hγ : 0 < γ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hs : Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖)) {Q₀ : ℕ}
    (hTail : ∀ Q ≥ Q₀, (∑' j : ℕ, ‖unitConductorSum F (j+Q+1)‖) ≤ C * (Q : ℝ)^(-γ))
    (hI : Integrable (realOscillation F w))
    (hDecay : ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ)) :
    ∀ᶠ P : ℝ in atTop,
      ‖majorArcTruncation F w P - singularSeries F * singularIntegral F w‖ ≤
        (((2*D/3) * (∑' j : ℕ, ‖unitConductorSum F (j+1)‖)) +
          (4*C) * ‖singularIntegral F w‖) * P^(-(min 1 (γ/2))) := by
  let σ := min 1 (γ/2)
  have hσ : 0 < σ := lt_min zero_lt_one (by positivity)
  have hσ₁ : σ ≤ 1 := min_le_left _ _
  have hσκ : σ ≤ ((γ+2)-2)/2 := by
    rw [add_sub_cancel_right]
    exact min_le_right (1 : ℝ) (γ/2)
  have hcut := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).eventually
    (eventually_ge_atTop (Q₀ : ℝ))
  filter_upwards [hcut, eventually_ge_atTop (1 : ℝ)] with P hcutP hP
  let Q := ⌊P^(1/2 : ℝ)⌋₊
  have hQ : Q₀ ≤ Q := Nat.le_floor hcutP
  let A (j : ℕ) := unitConductorSum F (j+1)
  have hSeries : (∑ j ∈ Finset.range Q, A j) + (∑' j : ℕ, A (j+Q)) = singularSeries F :=
    (show Summable A from hs.of_norm).sum_add_tsum_nat_add Q
  have hQPow : (Q : ℝ)^(-γ) ≤ 4 * P^(-σ) := by
    have h := conductor_cutoff_power_le (κ := γ+2) hσ hσ₁ hσκ hP
    simpa only [show 2-(γ+2) = -γ by ring] using h
  have hsShift : Summable (fun j : ℕ => ‖A (j+Q)‖) :=
    (summable_nat_add_iff (f := fun j : ℕ => ‖A j‖) Q).2 hs
  have hNorm : ‖(∑ j ∈ Finset.range Q, A j) - singularSeries F‖ ≤ (4*C) * P^(-σ) := by
    rw [norm_sub_rev, ← hSeries, add_sub_cancel_left]
    calc
      _ ≤ ∑' j, ‖A (j+Q)‖ := norm_tsum_le_tsum_norm (f := fun j : ℕ => A (j+Q)) hsShift
      _ ≤ C * (Q : ℝ)^(-γ) := hTail Q hQ
      _ ≤ C * (4 * P^(-σ)) := mul_le_mul_of_nonneg_left hQPow hC
      _ = _ := by ring
  exact majorArcTruncation_error_of_tail_atScale (K := 4*C) hσ₁ hD F w hs hI hDecay P hP hNorm

/-- Extending the cutoffs saves at least `min 1 ((κ - 2) / 2)` powers of the scale
when the conductor coefficient bound has exponent `1 - κ`. -/
theorem majorArcTruncation_error_withSaving {κ C D : ℝ} (hκ : 2 < κ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hA : ∀ j : ℕ, ‖unitConductorSum F (j+1)‖ ≤ C * ((j+1 : ℕ) : ℝ)^(1-κ))
    (hI : Integrable (realOscillation F w))
    (hDecay : ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ))
    (P : ℝ) (hP : 1 ≤ P) :
    ‖majorArcTruncation F w P - singularSeries F * singularIntegral F w‖ ≤
      (((2*D/3) * (∑' j : ℕ, ‖unitConductorSum F (j+1)‖)) +
        (4*C/(κ-2)) * ‖singularIntegral F w‖) * P^(-(min 1 ((κ-2)/2))) := by
  let σ := min 1 ((κ-2)/2)
  have hσ : 0 < σ := lt_min zero_lt_one (by linarith)
  have hσ₁ : σ ≤ 1 := min_le_left _ _
  have hσκ : σ ≤ (κ-2)/2 := min_le_right _ _
  refine majorArcTruncation_error_of_tail_atScale hσ₁ hD F w
    (summable_norm_of_conductor_power hκ hA) hI hDecay P hP ?_
  let Q := ⌊P^(1/2 : ℝ)⌋₊
  have hQN : 1 ≤ Q := Nat.le_floor (by simpa using Real.one_le_rpow hP (by norm_num : 0 ≤ (1/2 : ℝ)))
  rw [norm_sub_rev]
  have hk : 0 < κ-2 := by linarith
  refine (conductor_power_tail hκ hC hA Q hQN).trans ?_
  calc
    _ ≤ (C/(κ-2)) * (4 * P^(-σ)) :=
      mul_le_mul_of_nonneg_left (conductor_cutoff_power_le hσ hσ₁ hσκ hP) (by positivity)
    _ = _ := by ring

/-- Extending both major-arc cutoffs incurs an error of order `P⁻¹`
inside the normalized main term when `κ ≥ 4`. -/
theorem majorArcTruncation_error {κ C D : ℝ} (hκ : 4 ≤ κ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hA : ∀ j : ℕ, ‖unitConductorSum F (j+1)‖ ≤ C * ((j+1 : ℕ) : ℝ)^(1-κ))
    (hI : Integrable (realOscillation F w))
    (hDecay : ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ))
    (P : ℝ) (hP : 1 ≤ P) :
    ‖majorArcTruncation F w P - singularSeries F * singularIntegral F w‖ ≤
      (((2*D/3) * (∑' j : ℕ, ‖unitConductorSum F (j+1)‖)) +
        (4*C/(κ-2)) * ‖singularIntegral F w‖) * P^(-1 : ℝ) := by
  simpa only [min_eq_left (show (1 : ℝ) ≤ (κ-2)/2 by linarith)] using
    majorArcTruncation_error_withSaving (by linarith : 2 < κ) hC hD F w hA hI hDecay P hP

/-- Replace the truncated main term in the integrated expansion. -/
private theorem majorArcIntegral_bound_of_truncation {d : ℕ} {σ K : ℝ}
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hσ : 0 < σ) (hK : 0 ≤ K)
    (hExpansion : IntegratedMajorArcExpansion d F w)
    (hTruncation : ∀ᶠ P : ℝ in atTop,
      ‖majorArcTruncation F w P - singularSeries F * singularIntegral F w‖ ≤ K * P^(-σ)) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(∫ α in majorArcs d P, normalizedSum F w P α ∂circleMeasure) -
        (P ^ (-(d : ℝ)) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
          C * P ^ (-(d : ℝ) - σ) := by
  obtain ⟨E, hE, hPoisson⟩ := hExpansion σ hσ
  refine ⟨E+K, add_pos_of_pos_of_nonneg hE hK, ?_⟩
  filter_upwards [hPoisson, hTruncation, eventually_ge_atTop (1 : ℝ)] with P hPExpansion hT hP
  have hp : 0 < P := zero_lt_one.trans_le hP
  let Main := singularSeries F * singularIntegral F w
  let Trunc := majorArcTruncation F w P
  let Major := ∫ α in majorArcs d P, normalizedSum F w P α ∂circleMeasure
  have hsplit : Major - (P ^ (-(d : ℝ)) : ℝ) • Main =
      (Major - (P ^ (-(d : ℝ)) : ℝ) • Trunc) + (P ^ (-(d : ℝ)) : ℝ) • (Trunc - Main) := by
    rw [smul_sub]
    abel
  change ‖Major - (P ^ (-(d : ℝ)) : ℝ) • Main‖ ≤ (E+K) * P ^ (-(d : ℝ) - σ)
  rw [hsplit]
  calc
    _ ≤ ‖Major - (P ^ (-(d : ℝ)) : ℝ) • Trunc‖ +
        ‖(P ^ (-(d : ℝ)) : ℝ) • (Trunc - Main)‖ := norm_add_le _ _
    _ ≤ E * P ^ (-(d : ℝ) - σ) + (P ^ (-(d : ℝ)) : ℝ) * (K * P^(-σ)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
      exact add_le_add hPExpansion (mul_le_mul_of_nonneg_left hT (by positivity))
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hp, ← sub_eq_add_neg]
      ring

/-- The major-arc asymptotic with an absolute conductor tail of exponent `γ`. -/
theorem majorArcIntegral_bound_of_expansion_of_absoluteTail {d : ℕ} {γ : ℝ}
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hγ : 0 < γ)
    (hExpansion : IntegratedMajorArcExpansion d F w)
    (hs : Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖))
    (hTail : ∃ C > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
      (∑' j : ℕ, ‖unitConductorSum F (j+Q+1)‖) ≤ C * (Q : ℝ)^(-γ))
    (hI : Integrable (realOscillation F w))
    (hDecay : ∃ D > 0, ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ)) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(∫ α in majorArcs d P, normalizedSum F w P α ∂circleMeasure) -
        (P ^ (-(d : ℝ)) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * P ^ (-(d : ℝ) - min 1 (γ/2)) := by
  obtain ⟨C,hC,Q₀,hTail⟩ := hTail
  obtain ⟨D,hD,hDecay⟩ := hDecay
  let K := ((2*D/3) * (∑' j : ℕ, ‖unitConductorSum F (j+1)‖)) +
    (4*C) * ‖singularIntegral F w‖
  have hK : 0 ≤ K := by
    have hS : 0 ≤ ∑' j : ℕ, ‖unitConductorSum F (j+1)‖ := tsum_nonneg fun _ => norm_nonneg _
    dsimp [K]
    positivity
  exact majorArcIntegral_bound_of_truncation F w (lt_min zero_lt_one (by positivity)) hK hExpansion
    (majorArcTruncation_error_of_absoluteTail hγ hC.le hD.le F w hs hTail hI hDecay)

/-- The integrated leading-term expansion and the two decay bounds imply the
major-arc estimate with a saving of `min 1 ((κ - 2) / 2)`. -/
theorem majorArcEstimate_of_expansion_withSaving {d : ℕ} {κ : ℝ}
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hn : 1 ≤ n) (hκ : 2 < κ)
    (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hLoc : ∀ p : ℕ, ∀ _ : Fact p.Prime, HasNonzeroZero F ℚ_[p])
    (hExpansion : IntegratedMajorArcExpansion d F w)
    (hConductor : ∃ C > 0, ∀ j : ℕ, ‖unitConductorSum F (j+1)‖ ≤ C * ((j+1 : ℕ) : ℝ)^(1-κ))
    (hI : Integrable (realOscillation F w))
    (hDecay : ∃ D > 0, ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ))
    (hJ : 0 < (singularIntegral F w).re) :
    MajorArcEstimate d F w (min 1 ((κ-2)/2)) := by
  let σ := min 1 ((κ-2)/2)
  have hσ : 0 < σ := lt_min zero_lt_one (by linarith)
  obtain ⟨C, hC, hA⟩ := hConductor
  obtain ⟨D, hD, hDecay⟩ := hDecay
  have hASum := summable_norm_of_conductor_power hκ hA
  obtain ⟨hS, hSreal⟩ := singularSeries_positive_of_summable F hn hF hs hLoc hASum
  have hpositive : 0 < (singularSeries F * singularIntegral F w).re := by
    rw [Complex.mul_re, hSreal, zero_mul, sub_zero]
    exact mul_pos hS hJ
  refine ⟨hASum, hI, hpositive, ?_⟩
  let K := ((2*D/3) * (∑' j : ℕ, ‖unitConductorSum F (j+1)‖)) +
    (4*C/(κ-2)) * ‖singularIntegral F w‖
  have hK : 0 ≤ K := by
    have hSnn : 0 ≤ ∑' j : ℕ, ‖unitConductorSum F (j+1)‖ := tsum_nonneg fun _ => norm_nonneg _
    have hk : 0 < κ-2 := by linarith
    unfold K
    positivity
  apply majorArcIntegral_bound_of_truncation F w hσ hK hExpansion
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP
  exact majorArcTruncation_error_withSaving hκ hC.le hD.le F w hA hI hDecay P hP

/-- The integrated expansion and the decay bounds give the original unit
major-arc saving when `κ ≥ 4`. -/
theorem majorArcEstimate_of_expansion {d : ℕ} {κ : ℝ}
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hn : 1 ≤ n) (hκ : 4 ≤ κ)
    (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hLoc : ∀ p : ℕ, ∀ _ : Fact p.Prime, HasNonzeroZero F ℚ_[p])
    (hExpansion : IntegratedMajorArcExpansion d F w)
    (hConductor : ∃ C > 0, ∀ j : ℕ, ‖unitConductorSum F (j+1)‖ ≤ C * ((j+1 : ℕ) : ℝ)^(1-κ))
    (hI : Integrable (realOscillation F w))
    (hDecay : ∃ D > 0, ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ))
    (hJ : 0 < (singularIntegral F w).re) :
    MajorArcEstimate d F w := by
  simpa only [min_eq_left (show (1 : ℝ) ≤ (κ-2)/2 by linarith)] using
    majorArcEstimate_of_expansion_withSaving F w hn (by linarith : 2 < κ)
      hF hs hLoc hExpansion hConductor hI hDecay hJ

end

end Birch
