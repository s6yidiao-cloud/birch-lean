import Birch.Variance
import Birch.Metric
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # Second moment of the prime-denominator count

The finite estimate separates the repeated frequencies `p*M` from the narrower
integer arcs at each prime. The hypotheses state the multiplicity and size bounds
for the two finite sets explicitly.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace Birch

noncomputable section

private abbrev unitMeasure : Measure ℝ := volume.restrict (Set.Ioc 0 1)

private lemma real_variance (u C : ℝ) (L : ℕ) (hu : 0 < u) (hu' : u < 1 / 2)
    (hL : 2 ≤ L) (c : ℕ → ℝ) (hc : ∀ j ∈ Finset.Icc 1 L, |c j| ≤ C) :
    (∫ x, (∑ j ∈ Finset.Icc 1 L, c j * centeredInterval u ((j : ℝ) * x)) ^ 2 ∂unitMeasure)
      ≤ 64 * C^2 * u * (L : ℝ) * Real.log (2 * (L : ℝ)) := by
  have h := dilated_interval_variance u C L hu hu' hL (fun j => (c j : ℂ)) (by simpa using hc)
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

private lemma integrable_square_of_bound {f : ℝ → ℝ} (hf : Measurable f) {A : ℝ}
    (hA : ∀ x, |f x| ≤ A) : Integrable (fun x => f x ^ 2) unitMeasure := by
  refine Measure.integrableOn_of_bounded (M := A^2) measure_Ioc_lt_top.ne
    (hf.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs (f x)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2

private lemma measurable_centered_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ) (k : ι → ℕ) :
    Measurable (fun x => ∑ j ∈ s, centeredInterval (u j) ((k j : ℝ) * x)) :=
  Finset.measurable_sum s fun j _ => (measurable_centeredInterval (u j)).comp (by fun_prop)

private lemma abs_centered_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℝ) (k : ι → ℕ)
    (hu : ∀ j ∈ s, 0 < u j) (hu' : ∀ j ∈ s, u j < 1/2) (x : ℝ) :
    |∑ j ∈ s, centeredInterval (u j) ((k j : ℝ) * x)| ≤ (s.card : ℝ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ s, (1:ℝ) := Finset.sum_le_sum fun j hj => abs_centeredInterval_le_one (hu j hj) (hu' j hj) _
    _ = _ := by simp

private lemma integral_sq_sub_le {A B : ℝ → ℝ}
    (hAi : Integrable (fun x => A x ^ 2) unitMeasure)
    (hBi : Integrable (fun x => B x ^ 2) unitMeasure)
    (hABi : Integrable (fun x => (A x - B x) ^ 2) unitMeasure) :
    (∫ x, (A x - B x) ^ 2 ∂unitMeasure) ≤
      2 * (∫ x, A x ^ 2 ∂unitMeasure) + 2 * (∫ x, B x ^ 2 ∂unitMeasure) := by
  calc
    _ ≤ ∫ x, 2 * (A x ^ 2 + B x ^ 2) ∂unitMeasure := by
      apply integral_mono hABi ((hAi.add hBi).const_mul 2)
      intro x
      change (A x - B x)^2 ≤ 2 * (A x ^ 2 + B x ^ 2)
      nlinarith [sq_nonneg (A x + B x)]
    _ = _ := by rw [integral_const_mul, integral_add hAi hBi, mul_add]

/-- Bound the squared integral of the two centered indicator sums in the metric
proposition. `L` bounds the dilates `p*M`, and `C` bounds their multiplicity. -/
theorem prime_frequency_second_moment (E P : Finset ℕ) {X L : ℕ} {u B C : ℝ}
    (hu : 0 < u) (hu' : u < 1/2) (hX : 2 ≤ X) (hL : 2 ≤ L)
    (hB : 1 ≤ B) (hP : ∀ p ∈ P, B < (p : ℝ)) (hcard : (P.card : ℝ) ≤ 2*B)
    (hE : E ⊆ Finset.Icc 1 X)
    (hprod : ∀ p ∈ P, ∀ M ∈ E, p*M ≤ L)
    (hcount : ∀ j ∈ Finset.Icc 1 L, (((P.product E).filter fun q => q.1*q.2 = j).card : ℝ) ≤ C) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
        (∑ q ∈ P.product E, (centeredInterval u ((q.1*q.2 : ℕ) * x) -
          centeredInterval (u/(q.1 : ℝ)) ((q.2 : ℝ)*x))) ^ 2)
      ≤ 128*C^2*u*(L : ℝ)*Real.log (2*(L : ℝ)) + 512*u*B*(X : ℝ)*Real.log (2*(X : ℝ)) := by
  let T := P.product E
  let A : ℝ → ℝ := fun x => ∑ q ∈ T, centeredInterval u ((q.1*q.2 : ℕ) * x)
  let b : ℕ → ℝ → ℝ := fun p x => ∑ M ∈ E, centeredInterval (u/(p : ℝ)) ((M : ℝ)*x)
  let D : ℝ → ℝ := fun x => ∑ q ∈ T, centeredInterval (u/(q.1 : ℝ)) ((q.2 : ℝ)*x)
  have hpPos (p : ℕ) (hp : p ∈ P) : 0 < (p : ℝ) := by linarith [hP p hp]
  have hpNPos (p : ℕ) (hp : p ∈ P) : 0 < p := by exact_mod_cast hpPos p hp
  have hpU (p : ℕ) (hp : p ∈ P) : 0 < u/(p : ℝ) := div_pos hu (hpPos p hp)
  have hpU' (p : ℕ) (hp : p ∈ P) : u/(p : ℝ) < 1/2 := by
    apply (div_lt_iff₀ (hpPos p hp)).mpr
    linarith [hP p hp]
  have hDA (x : ℝ) : D x = ∑ p ∈ P, b p x := by simp [D, T, b, Finset.sum_product]
  have hAm : Measurable A := measurable_centered_sum T (fun _ => u) (fun q => q.1*q.2)
  have hDm : Measurable D := measurable_centered_sum T (fun q => u/(q.1 : ℝ)) Prod.snd
  have hAabs (x : ℝ) : |A x| ≤ T.card := abs_centered_sum_le T (fun _ => u) (fun q => q.1*q.2)
    (fun _ _ => hu) (fun _ _ => hu') x
  have hDabs (x : ℝ) : |D x| ≤ T.card := abs_centered_sum_le T (fun q => u/(q.1 : ℝ)) Prod.snd
    (fun p hp => hpU p.1 (Finset.mem_product.mp hp).1) (fun p hp => hpU' p.1 (Finset.mem_product.mp hp).1) x
  have hAi := integrable_square_of_bound hAm hAabs
  have hDi := integrable_square_of_bound hDm hDabs
  have hADi : Integrable (fun x => (A x - D x)^2) unitMeasure :=
    integrable_square_of_bound (hAm.sub hDm) (fun x => (abs_sub _ _).trans (add_le_add (hAabs x) (hDabs x)))
  have hA : (∫ x, A x ^ 2 ∂unitMeasure) ≤ 64*C^2*u*(L : ℝ)*Real.log (2*(L : ℝ)) := by
    let mult : ℕ → ℝ := fun j => ((T.filter fun q => q.1*q.2 = j).card : ℝ)
    have hmap (q : ℕ × ℕ) (hq : q ∈ T) : q.1*q.2 ∈ Finset.Icc 1 L := by
      rcases Finset.mem_product.mp hq with ⟨hp, hM⟩
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (hpNPos _ hp) (Finset.mem_Icc.mp (hE hM)).1, hprod _ hp _ hM⟩
    have hAx (x : ℝ) : (∑ j ∈ Finset.Icc 1 L, mult j * centeredInterval u ((j : ℝ)*x)) = A x := by
      unfold A
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun q : ℕ × ℕ => q.1*q.2) hmap
        (fun q => centeredInterval u ((q.1*q.2 : ℕ)*x))]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [mult]
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro q hq
      rw [(Finset.mem_filter.mp hq).2]
    have hc (j : ℕ) (hj : j ∈ Icc 1 L) : |mult j| ≤ C := by
      rw [abs_of_nonneg (by dsimp [mult]; positivity)]
      exact hcount j hj
    simpa only [hAx] using real_variance u C L hu hu' hL mult hc
  have hbi (p : ℕ) (hp : p ∈ P) : Integrable (fun x => b p x ^ 2) unitMeasure := by
    apply integrable_square_of_bound (measurable_centered_sum E (fun _ => u/(p : ℝ)) id)
    exact abs_centered_sum_le E (fun _ => u/(p : ℝ)) id (fun _ _ => hpU p hp) (fun _ _ => hpU' p hp)
  have hb (p : ℕ) (hp : p ∈ P) :
      (∫ x, b p x ^ 2 ∂unitMeasure) ≤ 64*u/B*(X : ℝ)*Real.log (2*(X : ℝ)) := by
    classical
    let c : ℕ → ℝ := fun M => if M ∈ E then 1 else 0
    have hx (x : ℝ) : (∑ j ∈ Finset.Icc 1 X, c j * centeredInterval (u/p) ((j : ℝ)*x)) = b p x := by
      unfold b
      refine (Finset.sum_subset hE ?_).symm.trans ?_
      · intro j _ hj
        simp [c, hj]
      · apply Finset.sum_congr rfl
        intro j hj
        simp [c, hj]
    have hbnd := real_variance (u/p) 1 X (hpU p hp) (hpU' p hp) hX c (fun j _ => by dsimp [c]; split_ifs <;> norm_num)
    rw [show (1 : ℝ)^2 = 1 by norm_num, mul_one] at hbnd
    simp only [hx] at hbnd
    refine hbnd.trans ?_
    have hlog : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*X by omega))
    rw [mul_div_assoc]
    have hdiv : u/(p : ℝ) ≤ u/B := div_le_div_of_nonneg_left hu.le (by linarith) (hP p hp).le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdiv (by norm_num)) (by positivity)) hlog
  have hD : (∫ x, D x ^ 2 ∂unitMeasure) ≤ 256*u*B*(X : ℝ)*Real.log (2*(X : ℝ)) := by
    have hpoint (x : ℝ) : D x ^ 2 ≤ (P.card : ℝ) * ∑ p ∈ P, b p x ^ 2 := by
      rw [hDA]
      simpa using Finset.sum_mul_sq_le_sq_mul_sq P (fun (_ : ℕ) => (1 : ℝ)) (fun p => b p x)
    have hI : Integrable (fun x => (P.card : ℝ) * ∑ p ∈ P, b p x ^ 2) unitMeasure := by
      apply Integrable.const_mul
      apply integrable_finsetSum
      exact hbi
    have hsum := integral_mono hDi hI hpoint
    rw [integral_const_mul, integral_finsetSum P hbi] at hsum
    have hU : 0 ≤ 64*u/B*(X : ℝ)*Real.log (2*(X : ℝ)) := mul_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*X by omega)))
    refine hsum.trans ?_
    calc
      _ ≤ (P.card : ℝ) * ((P.card : ℝ) * (64*u/B*(X : ℝ)*Real.log (2*(X : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [nsmul_eq_mul] using Finset.sum_le_sum hb
      _ ≤ (2*B) * ((2*B) * (64*u/B*(X : ℝ)*Real.log (2*(X : ℝ)))) :=
        mul_le_mul hcard (mul_le_mul_of_nonneg_right hcard hU) (by positivity) (by linarith)
      _ = _ := by field_simp; ring
  simp_rw [Finset.sum_sub_distrib]
  change (∫ x, (A x - D x)^2 ∂unitMeasure) ≤ _
  exact (integral_sq_sub_le hAi hDi hADi).trans (by linarith [hA, hD])


/-- The mean of the hit count, summing the arc lengths for all prime and product pairs. -/
def expectedEventCount (T : Finset (ℕ × ℕ)) (u : ℝ) : ℝ :=
  ∑ q ∈ T, (2*u*(1 - 1/(q.1 : ℝ)))

private lemma primeIndicator_eq_intervalIndicator_sub {p : ℕ} (hp : 0 < p) {u x : ℝ}
    (hu' : u < 1/2) : primeIndicator p u x =
      intervalIndicator u ((p : ℝ)*x) - intervalIndicator (u/(p : ℝ)) x :=
  primeIndicator_eq_sub hp hu'

private lemma integrable_intervalIndicator (u : ℝ) (k : ℕ) :
    Integrable (fun x => intervalIndicator u ((k : ℝ)*x)) unitMeasure := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    ((measurable_intervalIndicator u).comp (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  unfold intervalIndicator
  split_ifs <;> simp

/-- The geometric mean of the event count is its exact integral on the circle. -/
theorem integral_eventCount_eq_expected (T : Finset (ℕ × ℕ)) {u : ℝ}
    (hu : 0 < u) (hu' : u < 1/2) (hT : ∀ q ∈ T, 0 < q.1 ∧ 0 < q.2) :
    (∫ x, eventCount T u x ∂circleMeasure) = expectedEventCount T u := by
  change (∫ x, ∑ q ∈ T, primeIndicator q.1 u ((q.2 : ℝ)*x) ∂unitMeasure) = _
  have hsplit (q : ℕ × ℕ) (hq : q ∈ T) (x : ℝ) :
      primeIndicator q.1 u ((q.2 : ℝ)*x) = intervalIndicator u ((q.1*q.2 : ℕ)*x) -
        intervalIndicator (u/(q.1 : ℝ)) ((q.2 : ℝ)*x) := by
    rw [primeIndicator_eq_intervalIndicator_sub (hT q hq).1 hu', Nat.cast_mul, mul_assoc]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro q hq
    rcases hT q hq with ⟨hp, hM⟩
    have hpR : (0 : ℝ) < q.1 := Nat.cast_pos.mpr hp
    have hupos : 0 < u/(q.1 : ℝ) := div_pos hu hpR
    have hu'new : u/(q.1 : ℝ) < 1/2 := by
      apply (div_lt_iff₀ hpR).mpr
      have hp1 : (1 : ℝ) ≤ q.1 := by exact_mod_cast hp
      linarith
    simp_rw [hsplit q hq]
    rw [integral_sub (integrable_intervalIndicator u (q.1*q.2)) (integrable_intervalIndicator _ q.2)]
    rw [integral_intervalIndicator_dilate hu hu' (Nat.mul_pos hp hM),
      integral_intervalIndicator_dilate hupos hu'new hM]
    ring
  · intro q hq
    simp_rw [hsplit q hq]
    exact (integrable_intervalIndicator u (q.1*q.2)).sub (integrable_intervalIndicator _ q.2)

private lemma eventCount_sub_expected_eq (T : Finset (ℕ × ℕ)) {u : ℝ}
    (hu' : u < 1/2) (hT : ∀ q ∈ T, 0 < q.1) (x : ℝ) :
    eventCount T u x - expectedEventCount T u =
      ∑ q ∈ T, (centeredInterval u ((q.1*q.2 : ℕ)*x) - centeredInterval (u/(q.1 : ℝ)) ((q.2 : ℝ)*x)) := by
  unfold eventCount expectedEventCount
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [primeIndicator_eq_intervalIndicator_sub (hT q hq) hu']
  simp only [centeredInterval, Nat.cast_mul, mul_assoc]
  field_simp
  ring

/-- The second-moment estimate for the prime-denominator hit count in `prop:metric`. -/
theorem eventCount_second_moment (E P : Finset ℕ) {X L : ℕ} {u B C : ℝ}
    (hu : 0 < u) (hu' : u < 1/2) (hX : 2 ≤ X) (hL : 2 ≤ L)
    (hB : 1 ≤ B) (hP : ∀ p ∈ P, B < (p : ℝ)) (hcard : (P.card : ℝ) ≤ 2*B)
    (hE : E ⊆ Finset.Icc 1 X)
    (hprod : ∀ p ∈ P, ∀ M ∈ E, p*M ≤ L)
    (hcount : ∀ j ∈ Finset.Icc 1 L, (((P.product E).filter fun q => q.1*q.2 = j).card : ℝ) ≤ C) :
    (∫ x, (eventCount (P.product E) u x - expectedEventCount (P.product E) u)^2 ∂circleMeasure)
      ≤ 128*C^2*u*(L : ℝ)*Real.log (2*(L : ℝ)) + 512*u*B*(X : ℝ)*Real.log (2*(X : ℝ)) := by
  have hT (q : ℕ × ℕ) (hq : q ∈ P.product E) : 0 < q.1 := by
    exact_mod_cast (show (0 : ℝ) < q.1 by linarith [hP q.1 (Finset.mem_product.mp hq).1])
  simp_rw [eventCount_sub_expected_eq (P.product E) hu' hT]
  exact prime_frequency_second_moment E P hu hu' hX hL hB hP hcard hE hprod hcount

/-- A positive lower bound for the mean from finite collection sizes. -/
theorem card_mul_le_expectedEventCount (E P : Finset ℕ) {u : ℝ} (hu : 0 < u)
    (hP : ∀ p ∈ P, 2 ≤ p) : ((E.card : ℝ)*P.card)*u ≤ expectedEventCount (P.product E) u := by
  change _ ≤ ∑ q ∈ P.product E, (2*u*(1 - 1/(q.1 : ℝ)))
  calc
    _ = ∑ _q ∈ P.product E, u := by simp [Finset.card_product, nsmul_eq_mul, mul_comm _ (E.card : ℝ)]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hp : (2 : ℝ) ≤ q.1 := by exact_mod_cast hP q.1 (Finset.mem_product.mp hq).1
      have hhalf : 1/(q.1 : ℝ) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp
      nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hhalf)]

/-- The explicit exceptional-measure bound from the second moment of the finite event count. -/
theorem measure_tail_le_eventCount_second_moment (E P : Finset ℕ) {X L : ℕ} {u B C K : ℝ}
    (hu : 0 < u) (hu' : u < 1/2) (hX : 2 ≤ X) (hL : 2 ≤ L)
    (hB : 1 ≤ B) (hP : ∀ p ∈ P, B < (p : ℝ)) (hcard : (P.card : ℝ) ≤ 2*B)
    (hE : E ⊆ Finset.Icc 1 X) (hEnonempty : E.Nonempty) (hPnonempty : P.Nonempty)
    (hprod : ∀ p ∈ P, ∀ M ∈ E, p*M ≤ L)
    (hcount : ∀ j ∈ Finset.Icc 1 L, (((P.product E).filter fun q => q.1*q.2 = j).card : ℝ) ≤ C)
    {f : ℝ → ℝ}
    (honHit : ∀ q ∈ P.product E, ∀ α, primeHit q.1 u ((q.2 : ℝ)*α) → f α ≤ K) :
    circleMeasure {α | K < f α} ≤ ENNReal.ofReal
      ((128*C^2*u*(L : ℝ)*Real.log (2*(L : ℝ)) + 512*u*B*(X : ℝ)*Real.log (2*(X : ℝ))) /
        (((E.card : ℝ)*P.card)*u)^2) := by
  let T := P.product E
  let avg := expectedEventCount T u
  let low := ((E.card : ℝ)*P.card)*u
  have htwo (p : ℕ) (hp : p ∈ P) : 2 ≤ p := by
    have h : (1 : ℝ) < p := hB.trans_lt (hP p hp)
    exact_mod_cast h
  have hlow : low ≤ avg := card_mul_le_expectedEventCount E P hu htwo
  have hEpos : (0 : ℝ) < E.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hEnonempty)
  have hPpos : (0 : ℝ) < P.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hPnonempty)
  have hlowpos : 0 < low := mul_pos (mul_pos hEpos hPpos) hu
  have havg : 0 < avg := hlowpos.trans_le hlow
  refine (measure_tail_le_eventVariance havg honHit).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hvar := eventCount_second_moment E P hu hu' hX hL hB hP hcard hE hprod hcount
  refine (div_le_div_of_nonneg_right hvar (sq_nonneg avg)).trans ?_
  have hLlog : 0 ≤ Real.log (2 * (L : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*L by omega))
  have hXlog : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*X by omega))
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hlowpos.le hlow 2)

end

end Birch
