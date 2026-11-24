import Birch.Estimates

/-!
# Prime-denominator events

The subtraction of two interval indicators retains exactly those approximations
whose numerator is a unit at the chosen prime. A variance estimate for their count
then controls the measure on which every such approximation fails.
-/

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace Birch

noncomputable section

/-- Distance at most \(u/p\) from a rational number with denominator \(p\) and
numerator indivisible by \(p\). The integer numerator includes all lifts. -/
def primeHit (p : ℕ) (u x : ℝ) : Prop :=
  ∃ a : ℤ, ¬ (p : ℤ) ∣ a ∧ |x - (a : ℝ) / p| ≤ u / (p : ℝ)

private theorem abs_mul_sub_eq {p x : ℝ} (hp : 0 < p) (a : ℝ) :
    |p * x - a| = p * |x - a / p| := by
  calc
    _ = |p * (x - a / p)| := by
      congr 1
      field_simp
    _ = _ := by rw [abs_mul, abs_of_pos hp]

private theorem eq_of_near_same_real {u x : ℝ} (hu : u < 1 / 2) {a b : ℤ}
    (ha : |x - (a : ℝ)| ≤ u) (hb : |x - (b : ℝ)| ≤ u) : a = b := by
  have hab : (a : ℝ) - (b : ℝ) < 1 := by linarith [(abs_le.mp ha).1, (abs_le.mp hb).2]
  have hba : (b : ℝ) - (a : ℝ) < 1 := by linarith [(abs_le.mp hb).1, (abs_le.mp ha).2]
  have hab' : a - b < 1 := by exact_mod_cast hab
  have hba' : b - a < 1 := by exact_mod_cast hba
  omega

/-- Removing the integral centers from the dilated interval gives precisely the
centers with numerator indivisible by \(p\). -/
theorem primeHit_iff {p : ℕ} (hp : 0 < p) {u x : ℝ} (hu : u < 1 / 2) :
    primeHit p u x ↔ (∃ a : ℤ, |(p : ℝ) * x - (a : ℝ)| ≤ u) ∧
      ¬ ∃ z : ℤ, |x - (z : ℝ)| ≤ u / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have ha_iff (a : ℤ) : |(p : ℝ) * x - (a : ℝ)| ≤ u ↔ |x - (a : ℝ) / p| ≤ u / (p : ℝ) := by
    rw [abs_mul_sub_eq hpR, mul_comm (p : ℝ), ← le_div_iff₀ hpR]
  have hintegral (z : ℤ) : (((p : ℤ) * z : ℤ) : ℝ) / (p : ℝ) = z := by
    push_cast
    field_simp
  constructor
  · rintro ⟨a, hna, ha⟩
    refine ⟨⟨a, (ha_iff a).2 ha⟩, ?_⟩
    rintro ⟨z, hz⟩
    have hnear : |(p : ℝ) * x - (((p : ℤ) * z : ℤ) : ℝ)| ≤ u := by
      apply (ha_iff ((p : ℤ) * z)).2
      simpa only [hintegral] using hz
    exact hna ⟨z, eq_of_near_same_real hu ((ha_iff a).2 ha) hnear⟩
  · rintro ⟨⟨a, ha⟩, hnonintegral⟩
    refine ⟨a, ?_, (ha_iff a).1 ha⟩
    rintro ⟨z, rfl⟩
    refine hnonintegral ⟨z, ?_⟩
    simpa only [hintegral] using (ha_iff ((p : ℤ) * z)).1 ha

/-- The indicator of a hit by the chosen denominator. -/
def primeIndicator (p : ℕ) (u x : ℝ) : ℝ := by
  classical
  exact if primeHit p u x then 1 else 0

/-- The exact subtraction of two short-interval indicators used to count visits. -/
theorem primeIndicator_eq_sub {p : ℕ} (hp : 0 < p) {u x : ℝ} (hu : u < 1 / 2) :
    primeIndicator p u x =
      (if ∃ a : ℤ, |(p : ℝ) * x - (a : ℝ)| ≤ u then 1 else 0) -
      (if ∃ z : ℤ, |x - (z : ℝ)| ≤ u / (p : ℝ) then 1 else 0) := by
  classical
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have himp (h : ∃ z : ℤ, |x - (z : ℝ)| ≤ u / (p : ℝ)) :
      ∃ a : ℤ, |(p : ℝ) * x - (a : ℝ)| ≤ u := by
    obtain ⟨z, hz⟩ := h
    refine ⟨(p : ℤ) * z, ?_⟩
    have hcast : (((p : ℤ) * z : ℤ) : ℝ) / (p : ℝ) = z := by
      push_cast
      field_simp
    rw [abs_mul_sub_eq hpR, hcast, mul_comm (p : ℝ)]
    exact (le_div_iff₀ hpR).mp hz
  unfold primeIndicator
  rw [primeHit_iff hp hu]
  by_cases hb : ∃ z : ℤ, |x - (z : ℝ)| ≤ u / (p : ℝ)
  · simp [hb, himp hb]
  · by_cases ha : ∃ a : ℤ, |(p : ℝ) * x - (a : ℝ)| ≤ u <;> simp [ha, hb]

theorem measurableSet_primeHit (p : ℕ) (u : ℝ) :
    MeasurableSet {x | primeHit p u x} := by
  classical
  let C (a : ℤ) : Set ℝ :=
    if ¬ (p : ℤ) ∣ a then {x | |x - (a : ℝ) / p| ≤ u / (p : ℝ)} else ∅
  have hC : {x | primeHit p u x} = ⋃ a : ℤ, C a := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, primeHit]
    apply exists_congr
    intro a
    by_cases ha : (p : ℤ) ∣ a <;> simp [C, ha]
  rw [hC]
  apply MeasurableSet.iUnion
  intro a
  by_cases ha : (p : ℤ) ∣ a
  · simp [C, ha]
  · simpa [C, ha] using (isClosed_le (continuous_id.sub continuous_const).abs
      (continuous_const : Continuous (fun _ : ℝ => u / (p : ℝ)))).measurableSet

theorem measurable_primeIndicator (p : ℕ) (u : ℝ) : Measurable (primeIndicator p u) := by
  classical
  unfold primeIndicator
  exact Measurable.ite (measurableSet_primeHit p u) measurable_const measurable_const

/-- Count the hits over a finite set of pairs of denominators and dilates. -/
def eventCount (T : Finset (ℕ × ℕ)) (u α : ℝ) : ℝ :=
  ∑ b ∈ T, primeIndicator b.1 u ((b.2 : ℝ) * α)

theorem measurable_eventCount (T : Finset (ℕ × ℕ)) (u : ℝ) : Measurable (eventCount T u) :=
  Finset.measurable_sum T fun b _ =>
    (measurable_primeIndicator b.1 u).comp (measurable_const.mul measurable_id)

private theorem primeIndicator_nonneg (p : ℕ) (u x : ℝ) : 0 ≤ primeIndicator p u x := by
  unfold primeIndicator
  split_ifs <;> norm_num

private theorem primeIndicator_le_one (p : ℕ) (u x : ℝ) : primeIndicator p u x ≤ 1 := by
  unfold primeIndicator
  split_ifs <;> norm_num

theorem eventCount_eq_zero_iff {T : Finset (ℕ × ℕ)} {u α : ℝ} :
    eventCount T u α = 0 ↔ ∀ b ∈ T, ¬ primeHit b.1 u ((b.2 : ℝ) * α) := by
  classical
  unfold eventCount
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun b _ => primeIndicator_nonneg _ _ _)]
  exact forall₂_congr fun b _ => by simp [primeIndicator, ite_eq_right_iff]

/-- Chebyshev's inequality at zero for an arbitrary positive center. -/
theorem measure_zero_le_variance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {f : Ω → ℝ} {avg : ℝ} (havg : 0 < avg)
    (hint : Integrable (fun x => (f x - avg) ^ 2) μ) :
    μ {x | f x = 0} ≤ ENNReal.ofReal ((∫ x, (f x - avg) ^ 2 ∂μ) / avg ^ 2) := by
  have hsq : ∀ x, 0 ≤ (f x - avg) ^ 2 := fun x => sq_nonneg _
  have hpos : 0 < avg ^ 2 := by positivity
  have hsubset : {x | f x = 0} ⊆ {x | avg ^ 2 ≤ (f x - avg) ^ 2} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [hx, zero_sub, neg_sq]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all μ hsq) hint (avg ^ 2)
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _)
    (div_nonneg (integral_nonneg hsq) hpos.le)).2
  apply (le_div_iff₀ hpos).2
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsubset) hpos.le).trans hmarkov

theorem integrable_eventCount_sub_sq (T : Finset (ℕ × ℕ)) (u avg : ℝ) :
    Integrable (fun α => (eventCount T u α - avg) ^ 2) circleMeasure := by
  have hmeas := ((measurable_eventCount T u).sub_const avg).pow_const 2
  rw [← integrableOn_univ]
  refine Measure.integrableOn_of_bounded (M := ((T.card : ℝ) + |avg|) ^ 2)
    (measure_ne_top circleMeasure Set.univ) hmeas.aestronglyMeasurable (ae_of_all _ fun α => ?_)
  have h0 : 0 ≤ eventCount T u α := Finset.sum_nonneg fun b _ => primeIndicator_nonneg _ _ _
  have hcard : eventCount T u α ≤ (T.card : ℝ) := by
    calc
      _ ≤ ∑ _b ∈ T, (1 : ℝ) := Finset.sum_le_sum fun b _ => primeIndicator_le_one _ _ _
      _ = _ := by simp
  have habs : |eventCount T u α - avg| ≤ (T.card : ℝ) + |avg| :=
    (abs_sub _ _).trans (add_le_add_left ((abs_of_nonneg h0).trans_le hcard) _)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (eventCount T u α - avg)]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- If a single hit forces a pointwise bound, the variance of the event count bounds
the measure of the frequencies exceeding that bound. -/
theorem measure_tail_le_eventVariance {T : Finset (ℕ × ℕ)} {u avg C : ℝ} {f : ℝ → ℝ}
    (havg : 0 < avg)
    (honHit : ∀ b ∈ T, ∀ α, primeHit b.1 u ((b.2 : ℝ) * α) → f α ≤ C) :
    circleMeasure {α | C < f α} ≤
      ENNReal.ofReal ((∫ α, (eventCount T u α - avg) ^ 2 ∂circleMeasure) / avg ^ 2) := by
  apply le_trans (measure_mono ?_) (measure_zero_le_variance circleMeasure havg
    (integrable_eventCount_sub_sq T u avg))
  intro α hα
  exact eventCount_eq_zero_iff.2 fun b hb h => (not_le_of_gt hα) (honHit b hb α h)

/-- The sum of reciprocal weights for the \(d-r\) differencing steps. -/
def dilationRho (d r : ℕ) : ℝ := 2 - 2 / (2 : ℝ) ^ (d - r)

/-- A product validates the length budget at every differencing step.
The indices start at zero, so the paper's \(w_i\) is \(2^{d-r-i-1}\) here. -/
def admissibleProduct (d r : ℕ) (P Q : ℝ) (M : ℕ) : Prop :=
  ∃ m : Fin (d - r) → ℕ, (∏ i, m i) = M ∧
    ∀ i, 0 < m i ∧ (m i : ℝ) * Q ^ (1 / (2 : ℝ) ^ (d - r - (i.val + 1))) ≤ P

/-- The approximation radius in Proposition prop:completion. -/
def completionRadius (d r : ℕ) (P Q : ℝ) : ℝ :=
  P ^ (-(r : ℝ)) * Q ^ (-dilationRho d r)

/-- The prime scale in the metric argument, for \(Q=P^h\). -/
def metricPrimeScale (P h : ℝ) : ℝ := (P / P ^ h) ^ (2 : ℕ)

/-- The scale of products of the \(d-r\) dilations. -/
def metricProductScale (d r : ℕ) (P h : ℝ) : ℝ :=
  P ^ ((d : ℝ) - (r : ℝ)) * (P ^ h) ^ (-dilationRho d r)

/-- The short-interval radius used to count successful dilates. -/
def metricWindow (d r : ℕ) (P h : ℝ) : ℝ :=
  metricPrimeScale P h * completionRadius d r P (P ^ h)

private theorem metricPrimeScale_eq {P : ℝ} (hP : 0 < P) (h : ℝ) :
    metricPrimeScale P h = P ^ (2 - 2 * h) := by
  unfold metricPrimeScale
  rw [show P / P ^ h = P ^ (1 - h) by rw [Real.rpow_sub hP, Real.rpow_one],
    ← Real.rpow_mul_natCast hP.le]
  congr 1
  push_cast
  ring

private theorem metricProductScale_eq {P : ℝ} (hP : 0 < P) (d r : ℕ) (h : ℝ) :
    metricProductScale d r P h = P ^ ((d : ℝ) - r - dilationRho d r * h) := by
  unfold metricProductScale
  rw [← Real.rpow_mul hP.le, ← Real.rpow_add hP]
  congr 1
  ring

private theorem metricWindow_eq {P : ℝ} (hP : 0 < P) (d r : ℕ) (h : ℝ) :
    metricWindow d r P h = P ^ (2 - (r : ℝ) - (2 + dilationRho d r) * h) := by
  unfold metricWindow completionRadius
  rw [metricPrimeScale_eq hP, ← Real.rpow_mul hP.le, ← Real.rpow_add hP, ← Real.rpow_add hP]
  congr 1
  ring

/-- The metric count scale in the source is exactly \(P^{d-b_r(h)}\). -/
theorem metricVolumeScale_eq {P : ℝ} (hP : 0 < P) (d r : ℕ) (h : ℝ) :
    metricPrimeScale P h * metricProductScale d r P h * metricWindow d r P h =
      P ^ ((d : ℝ) - exceptionExponent d r h) := by
  rw [metricPrimeScale_eq hP, metricProductScale_eq hP, metricWindow_eq hP,
    ← Real.rpow_add hP, ← Real.rpow_add hP]
  congr 1
  unfold exceptionExponent dilationRho
  ring

theorem metricWindow_eventually {d r : ℕ} (hr : 2 ≤ r) {h : ℝ} (hh : 0 < h) :
    ∀ᶠ P in atTop, 0 < metricWindow d r P h ∧ metricWindow d r P h < 1 / 2 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hR : (1 : ℝ) ≤ (2 : ℝ) ^ (d - r) := one_le_pow₀ (by norm_num)
  have hρ : 0 ≤ dilationRho d r := by
    unfold dilationRho
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    linarith
  let e := (r : ℝ) - 2 + (2 + dilationRho d r) * h
  have he : 0 < e := add_pos_of_nonneg_of_pos (sub_nonneg.mpr hr')
    (mul_pos (by linarith) hh)
  have hsmall : ∀ᶠ P : ℝ in atTop, P ^ (-e) < 1 / 2 :=
    (tendsto_rpow_neg_atTop he).eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with P hsmall hP
  rw [metricWindow_eq hP, show 2 - (r : ℝ) - (2 + dilationRho d r) * h = -e by
    dsimp [e]; ring]
  exact ⟨Real.rpow_pos_of_pos hP _, hsmall⟩

/-- Explicit input corresponding to Proposition prop:completion. An arbitrary
integer numerator represents proximity on the circle by absorbing its period. -/
def CompletionEstimate (d n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ (r : ℕ), 2 ≤ r → r < d → ∃ C > 0, ∀ᶠ P in atTop,
    ∀ (Q : ℝ), 1 ≤ Q → Q ≤ P ^ (1 / 2 : ℝ) →
    ∀ (p M : ℕ), p.Prime → (P / Q) ^ (2 : ℕ) < (p : ℝ) →
      (p : ℝ) ≤ 2 * (P / Q) ^ (2 : ℕ) → admissibleProduct d r P Q M →
    ∀ (a : ℤ) (α : ℝ), ¬ (p : ℤ) ∣ a →
      |(M : ℝ) * α - (a : ℝ) / (p : ℝ)| ≤ completionRadius d r P Q →
        f P α ≤ C * Q ^ (-((n : ℝ) / (2 : ℝ) ^ (d - r)))

/-- A single hit at the metric choice of prime scale and approximation radius
forces the pointwise metric level under the completion bound. -/
theorem level_of_primeHit {d n r : ℕ} {h : ℝ} {f : ℝ → ℝ → ℝ}
    (hcompl : CompletionEstimate d n f) (hr : 2 ≤ r) (hrd : r < d)
    (hh : 0 < h) (hhmax : h ≤ 1 / 2) :
    ∃ C > 0, ∀ᶠ P in atTop, ∀ (p M : ℕ), p.Prime →
      metricPrimeScale P h < (p : ℝ) → (p : ℝ) ≤ 2 * metricPrimeScale P h →
      admissibleProduct d r P (P ^ h) M → ∀ α,
      primeHit p (metricWindow d r P h) ((M : ℝ) * α) →
        f P α ≤ C * P ^ (-levelExponent d n r h) := by
  obtain ⟨C, hC, hW⟩ := hcompl r hr hrd
  refine ⟨C, hC, ?_⟩
  filter_upwards [hW, eventually_ge_atTop (1 : ℝ)] with P hW hP p M hp hpL hpU hM α hhit
  obtain ⟨a, ha, hδ⟩ := hhit
  have hP' : 0 < P := by linarith
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hQ₁ : 1 ≤ P ^ h := Real.one_le_rpow hP hh.le
  have hQ₂ : P ^ h ≤ P ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP hhmax
  have hδ' : metricWindow d r P h / (p : ℝ) ≤ completionRadius d r P (P ^ h) := by
    apply (div_le_iff₀ hp').2
    unfold metricWindow
    rw [mul_comm (completionRadius _ _ _ _)]
    exact mul_le_mul_of_nonneg_right hpL.le (by unfold completionRadius; positivity)
  have hf := hW (P ^ h) hQ₁ hQ₂ p M hp hpL hpU hM a α ha (hδ.trans hδ')
  refine hf.trans_eq ?_
  rw [← Real.rpow_mul hP'.le]
  congr 2
  unfold levelExponent
  ring

/-- Supply of distinct admissible products in the metric argument. -/
def MetricProductSupply (d : ℕ) : Prop :=
  ∀ (r : ℕ) (h : ℝ), 2 ≤ r → r < d → 0 < h → h ≤ 1 / 2 →
    ∀ ε : ℝ, 0 < ε → ∃ c > 0, ∀ᶠ P : ℝ in atTop, ∃ E : Finset ℕ,
      (∀ M ∈ E, 0 < M ∧ (M : ℝ) ≤ metricProductScale d r P h ∧
        admissibleProduct d r P (P ^ h) M) ∧
      c * metricProductScale d r P h * P ^ (-ε) ≤ (E.card : ℝ)

/-- Supply of primes in the metric dyadic interval. -/
def MetricPrimeSupply : Prop :=
  ∀ (h : ℝ), 0 < h → h ≤ 1 / 2 → ∀ ε : ℝ, 0 < ε →
    ∃ c > 0, ∀ᶠ P : ℝ in atTop, ∃ primes : Finset ℕ,
      (∀ p ∈ primes, p.Prime ∧ metricPrimeScale P h < (p : ℝ) ∧
        (p : ℝ) ≤ 2 * metricPrimeScale P h) ∧
      c * metricPrimeScale P h * P ^ (-ε) ≤ (primes.card : ℝ)

theorem metricPrimeScale_bounds {P h : ℝ} (hP : 1 ≤ P) (hh : 0 ≤ h) (hhmax : h ≤ 1 / 2) :
    P ≤ metricPrimeScale P h ∧ metricPrimeScale P h ≤ P ^ (2 : ℕ) := by
  rw [metricPrimeScale_eq (show 0 < P by linarith)]
  constructor
  · calc
      P = P ^ (1 : ℝ) := (Real.rpow_one P).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hP (by norm_num; linarith)

private theorem dilationRho_nonneg (d r : ℕ) : 0 ≤ dilationRho d r := by
  have hR : (1 : ℝ) ≤ (2 : ℝ) ^ (d - r) := one_le_pow₀ (by norm_num)
  unfold dilationRho
  rw [sub_nonneg, div_le_iff₀ (by positivity)]
  linarith

theorem metricProductScale_le {d r : ℕ} (hrd : r ≤ d) {P h : ℝ}
    (hP : 1 ≤ P) (hh : 0 ≤ h) :
    metricProductScale d r P h ≤ P ^ (d - r : ℕ) := by
  rw [metricProductScale_eq (show 0 < P by linarith), ← Real.rpow_natCast,
    Nat.cast_sub hrd]
  exact Real.rpow_le_rpow_of_exponent_le hP (sub_le_self _ (mul_nonneg (dilationRho_nonneg d r) hh))

theorem metricProductScale_eventually_ge_two {d r : ℕ} (hrd : r < d) {h : ℝ}
    (hhmax : h ≤ 1 / 2) :
    ∀ᶠ P : ℝ in atTop, 2 ≤ metricProductScale d r P h := by
  have hk : (1 : ℝ) ≤ (d : ℝ) - (r : ℝ) := by
    have h : (r : ℝ) + 1 ≤ (d : ℝ) := by
      exact_mod_cast (show r + 1 ≤ d by omega)
    linarith
  have hstrict : dilationRho d r < 2 := sub_lt_self _ (by positivity)
  have hmult := mul_le_mul_of_nonneg_left hhmax (dilationRho_nonneg d r)
  have he : 0 < (d : ℝ) - (r : ℝ) - dilationRho d r * h := by linarith
  have h := (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with P h hP
  rwa [metricProductScale_eq hP]

/-- A positive frequency of size at most \(P^D\) has at most \(D\) distinct prime
denominators at least \(P\). Each denominator determines its cofactor. -/
theorem primePairMultiplicity_le (T : Finset (ℕ × ℕ)) {j D : ℕ} {P : ℝ}
    (hP : 1 < P) (hj : 0 < j) (hupper : (j : ℝ) ≤ P ^ D)
    (hp : ∀ q ∈ T, q.1.Prime ∧ P ≤ (q.1 : ℝ)) :
    (T.filter fun q => q.1 * q.2 = j).card ≤ D := by
  let U := T.filter fun q => q.1 * q.2 = j
  let S := U.image Prod.fst
  have hInj : (↑U : Set (ℕ × ℕ)).InjOn Prod.fst := by
    rintro ⟨p, m⟩ hpm ⟨q, n⟩ hqn h
    change p = q at h
    subst q
    have hm := Finset.mem_filter.1 hpm
    have hn := Finset.mem_filter.1 hqn
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (hp _ hm.1).1.pos (hm.2.trans hn.2.symm))
  have hSCard : S.card = U.card := Finset.card_image_of_injOn hInj
  have hS : S ⊆ j.primeFactors := by
    intro p hpS
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hpS
    obtain ⟨hqT, hqj⟩ := Finset.mem_filter.1 hq
    exact (hp q hqT).1.mem_primeFactors ⟨q.2, hqj.symm⟩ hj.ne'
  have hprod : (∏ p ∈ S, p) ∣ j :=
    (Finset.prod_dvd_prod_of_subset S j.primeFactors id hS).trans (Nat.prod_primeFactors_dvd j)
  have hlow : P ^ S.card ≤ ∏ p ∈ S, (p : ℝ) := by
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => by linarith)
    intro p hpS
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hpS
    exact (hp q (Finset.mem_filter.1 hq).1).2
  have hcast : (∏ p ∈ S, (p : ℝ)) ≤ (j : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hj hprod
  rw [← hSCard]
  exact (pow_le_pow_iff_right₀ hP).1 (hlow.trans (hcast.trans hupper))

end

end Birch
