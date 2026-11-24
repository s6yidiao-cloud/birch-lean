import Birch.CircleMethod
import Birch.DivisorBounds
import Birch.V2CoverMinorArcs
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The classical fourth moment for the cover sum

The proof follows the difference-count argument in Section 7 of `v2.tex`.
For a nonzero value of the difference, the shift divides that value and the
polynomial for each fixed shift has bounded degree and is nonconstant.
-/

namespace Birch

open Filter Finset MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal

noncomputable section

/-- The polynomial exponential sum with integer argument in the closed interval
of radius `L`, as used in Sections 6 and 7 of `v2.tex`. -/
def coverYSum (g : Polynomial ℤ) (L α : ℝ) : ℂ :=
  ∑ y ∈ Finset.Icc (-⌊L⌋) ⌊L⌋, phase (-α * ((g.eval y : ℤ) : ℝ))

theorem continuous_coverYSum (g : Polynomial ℤ) (L : ℝ) : Continuous (coverYSum g L) := by
  unfold coverYSum phase
  fun_prop

private theorem taylor_sub_sub_C_ne_zero (g : Polynomial ℤ) (hg : 2 ≤ g.natDegree)
    {h : ℤ} (hh : h ≠ 0) (b : ℤ) : g.taylor h - g - C b ≠ 0 := by
  let j := g.natDegree - 1
  have hj : j ≠ 0 := by dsimp [j]; omega
  let p := g.hasseDeriv j
  have hp : p.natDegree = 1 := by
    dsimp [p, j]
    rw [natDegree_hasseDeriv]
    omega
  have hp₀ : p ≠ 0 := by
    intro e
    simp [e] at hp
  have hp₁ : p.coeff 1 ≠ 0 := by
    rw [← hp, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hp₀
  have heval (y : ℤ) : p.eval y = p.coeff 1 * y + p.coeff 0 := by
    have h := congrArg (eval y) (eq_X_add_C_of_natDegree_le_one hp.le)
    simpa using h
  have hcoeff₀ : g.coeff j = p.eval 0 := by
    rw [← taylor_coeff 0 g j, taylor_zero]
  have hcoeff : (g.taylor h - g - C b).coeff j = p.coeff 1 * h := by
    rw [coeff_sub, coeff_sub, coeff_C, if_neg hj, sub_zero, taylor_coeff, hcoeff₀,
      show (hasseDeriv j g).eval h = p.eval h by rfl, heval h, heval 0]
    ring
  intro e
  rw [e, coeff_zero] at hcoeff
  exact mul_ne_zero hp₁ hh hcoeff.symm

private theorem taylor_sub_sub_C_natDegree_le (g : Polynomial ℤ) (h b : ℤ) :
    (g.taylor h - g - C b).natDegree ≤ g.natDegree := by
  have h₁ := natDegree_sub_le (g.taylor h - g) (C b)
  have h₂ := natDegree_sub_le (g.taylor h) g
  simpa using h₁.trans (max_le (by simpa using h₂) (by simp))

/-- A fiber of a nonconstant integral polynomial on a finite set is bounded by its degree. -/
theorem card_eval_fiber_le_natDegree (g : Polynomial ℤ) (hg : 0 < g.natDegree)
    (U : Finset ℤ) (b : ℤ) : (U.filter fun v => g.eval v = b).card ≤ g.natDegree := by
  have hpoly : g - C b ≠ 0 := by
    intro h
    have he := congrArg natDegree (sub_eq_zero.mp h)
    simp at he
    omega
  have hdeg : (g - C b).natDegree ≤ g.natDegree :=
    (natDegree_sub_le g (C b)).trans (max_le le_rfl (by simp))
  refine (card_le_degree_of_subset_roots (p := g - C b) ?_).trans hdeg
  intro v hv
  have he := (Finset.mem_filter.1 (Finset.mem_def.2 hv)).2
  exact (mem_roots hpoly).2 (by simp [IsRoot, he])

private theorem card_eval_shift_fiber_le_natDegree (g : Polynomial ℤ) (hg : 2 ≤ g.natDegree)
    {h : ℤ} (hh : h ≠ 0) (U : Finset ℤ) (b : ℤ) :
    (U.filter fun v => g.eval (v + h) - g.eval v = b).card ≤ g.natDegree := by
  refine (card_le_degree_of_subset_roots (p := g.taylor h - g - C b) ?_).trans
    (taylor_sub_sub_C_natDegree_le g h b)
  intro v hv
  have he := (Finset.mem_filter.1 (Finset.mem_def.2 hv)).2
  exact (mem_roots (taylor_sub_sub_C_ne_zero g hg hh b)).2 (by
    simp [IsRoot, taylor_apply, eval_comp, he])

private abbrev valueDifference (g : Polynomial ℤ) (p : ℤ × ℤ) : ℤ :=
  g.eval p.1 - g.eval p.2

private abbrev differenceFiber (g : Polynomial ℤ) (U : Finset ℤ) (b : ℤ) : Finset (ℤ × ℤ) :=
  (U ×ˢ U).filter fun p => valueDifference g p = b

private theorem card_differenceFiber_zero (g : Polynomial ℤ) (hg : 0 < g.natDegree)
    (U : Finset ℤ) : (differenceFiber g U 0).card ≤ g.natDegree * U.card := by
  apply Finset.card_le_mul_card_image_of_maps_to (f := Prod.snd) (t := U)
    (fun p hp => (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2) g.natDegree
  intro v _
  refine (Finset.card_le_card_of_injOn Prod.fst (t := U.filter fun u => g.eval u = g.eval v)
    ?_ ?_).trans (card_eval_fiber_le_natDegree g hg U (g.eval v))
  · intro p hp
    obtain ⟨hp, e⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    obtain ⟨hpU, he⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_filter.2 ⟨(Finset.mem_product.1 hpU).1,
      (sub_eq_zero.mp he).trans (congrArg g.eval e)⟩
  · intro p hp q hq e
    exact Prod.ext e ((Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2.trans
      ((Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2.symm))

private theorem card_differenceFiber_ne_zero (g : Polynomial ℤ) (hg : 2 ≤ g.natDegree)
    (U : Finset ℤ) {b : ℤ} (hb : b ≠ 0) :
    (differenceFiber g U b).card ≤ g.natDegree * (2 * b.natAbs.divisors.card) := by
  let D := b.natAbs.divisors.image fun h : ℕ => (h : ℤ)
  let H := D ∪ D.image Neg.neg
  let shift (p : ℤ × ℤ) := p.1 - p.2
  have hmaps : Set.MapsTo shift (differenceFiber g U b) H := by
    intro p hp
    have he := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    have hdvd : shift p ∣ b := by
      rw [← he]
      exact sub_dvd_eval_sub p.1 p.2 g
    have hnat : (shift p).natAbs ∣ b.natAbs :=
      Int.dvd_natCast.1 (Int.dvd_natAbs.2 hdvd)
    have hmem : (shift p).natAbs ∈ b.natAbs.divisors :=
      Nat.mem_divisors.2 ⟨hnat, Int.natAbs_ne_zero.mpr hb⟩
    have hD : ((shift p).natAbs : ℤ) ∈ D := Finset.mem_image_of_mem _ hmem
    apply Finset.mem_coe.2
    rcases Int.natAbs_eq (shift p) with h | h
    · exact Finset.mem_union_left _ (h ▸ hD)
    · exact Finset.mem_union_right _ (h ▸ Finset.mem_image_of_mem Neg.neg hD)
  have hcard : H.card ≤ 2 * b.natAbs.divisors.card := by
    calc
      _ ≤ D.card + (D.image Neg.neg).card := Finset.card_union_le _ _
      _ ≤ b.natAbs.divisors.card + b.natAbs.divisors.card :=
        Nat.add_le_add Finset.card_image_le (Finset.card_image_le.trans Finset.card_image_le)
      _ = _ := by omega
  refine (Finset.card_le_mul_card_image_of_maps_to hmaps g.natDegree ?_).trans
    (Nat.mul_le_mul_left _ hcard)
  intro h _
  by_cases hh : h = 0
  · have hempty : ((differenceFiber g U b).filter fun p => shift p = h) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro p hp
      obtain ⟨hp, hshift⟩ := Finset.mem_filter.1 hp
      have he := (Finset.mem_filter.1 hp).2
      have heq : p.1 = p.2 := sub_eq_zero.mp (hshift.trans hh)
      simp [valueDifference, heq] at he
      exact hb he.symm
    simp [hempty]
  · refine (Finset.card_le_card_of_injOn Prod.snd
      (t := U.filter fun v => g.eval (v + h) - g.eval v = b) ?_ ?_).trans
      (card_eval_shift_fiber_le_natDegree g hg hh U b)
    · intro p hp
      obtain ⟨hp, hshift⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
      obtain ⟨hpU, he⟩ := Finset.mem_filter.1 hp
      have heq : p.2 + h = p.1 := by dsimp [shift] at hshift; omega
      exact Finset.mem_filter.2 ⟨(Finset.mem_product.1 hpU).2, by simpa only [heq] using he⟩
    · intro p hp q hq e
      have hp' := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
      have hq' := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
      exact Prod.ext (by dsimp [shift] at hp' hq'; omega) e

private def differenceEnergy (g : Polynomial ℤ) (U : Finset ℤ) : ℕ :=
  (((U ×ˢ U) ×ˢ (U ×ˢ U)).filter
    fun p => valueDifference g p.1 = valueDifference g p.2).card

private theorem differenceEnergy_eq_sum (g : Polynomial ℤ) (U : Finset ℤ) :
    differenceEnergy g U =
      ∑ b ∈ insert 0 ((U ×ˢ U).image (valueDifference g)), (differenceFiber g U b).card ^ 2 := by
  classical
  unfold differenceEnergy
  let D := insert 0 ((U ×ˢ U).image (valueDifference g))
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p => valueDifference g p.1) (t := D)]
  · apply Finset.sum_congr rfl
    intro b _
    rw [sq, ← Finset.card_product]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, he⟩, h₃⟩
      exact ⟨⟨h₁, h₃⟩, h₂, he.symm.trans h₃⟩
    · rintro ⟨⟨h₁, h₃⟩, h₂, h₄⟩
      exact ⟨⟨⟨h₁, h₂⟩, h₃.trans h₄.symm⟩, h₃⟩
  · intro p hp
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1)

private theorem differenceEnergy_le {g : Polynomial ℤ} (hg : 2 ≤ g.natDegree)
    (U : Finset ℤ) (D : ℝ) (hD₀ : 0 ≤ D)
    (hD : ∀ p ∈ U ×ˢ U, valueDifference g p ≠ 0 →
      (↑(g.natDegree * (2 * (valueDifference g p).natAbs.divisors.card)) : ℝ) ≤ D) :
    (differenceEnergy g U : ℝ) ≤ ((g.natDegree : ℝ) ^ 2 + D) * (U.card : ℝ) ^ 2 := by
  classical
  let V := (U ×ˢ U).image (valueDifference g)
  let r (b : ℤ) := (differenceFiber g U b).card
  have hr : (∑ b ∈ V.erase 0, (r b : ℝ)) ≤ (U.card : ℝ) ^ 2 := by
    have hsum := Finset.card_eq_sum_card_image (valueDifference g) (U ×ˢ U)
    rw [Finset.card_product, ← sq] at hsum
    exact_mod_cast (Finset.sum_le_sum_of_subset (Finset.erase_subset 0 V)).trans hsum.symm.le
  have hrbound : ∀ b ∈ V.erase 0, (r b : ℝ) ≤ D := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_erase.1 hb).2
    have hne := (Finset.mem_erase.1 hb).1
    exact (by exact_mod_cast card_differenceFiber_ne_zero g hg U hne :
      (r (valueDifference g p) : ℝ) ≤ _).trans (hD p hp hne)
  have h₀ : (r 0 : ℝ) ≤ (g.natDegree : ℝ) * U.card := by
    exact_mod_cast card_differenceFiber_zero g (by omega) U
  have hrem : (∑ b ∈ V.erase 0, (r b : ℝ) ^ 2) ≤ D * (U.card : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ b ∈ V.erase 0, D * (r b : ℝ) :=
        Finset.sum_le_sum fun b hb => by
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hrbound b hb) (Nat.cast_nonneg _)
      _ = D * (∑ b ∈ V.erase 0, (r b : ℝ)) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hr hD₀
  rw [differenceEnergy_eq_sum]
  push_cast
  change (∑ b ∈ insert 0 V, (r b : ℝ) ^ 2) ≤ _
  rw [← Finset.insert_erase (Finset.mem_insert_self 0 V),
    Finset.erase_insert_eq_erase, Finset.sum_insert (Finset.notMem_erase _ _)]
  calc
    _ ≤ ((g.natDegree : ℝ) * U.card) ^ 2 + D * (U.card : ℝ) ^ 2 :=
      add_le_add (pow_le_pow_left₀ (Nat.cast_nonneg _) h₀ _) hrem
    _ = _ := by ring


private theorem phase_add_cover (u v : ℝ) : phase (u + v) = phase u * phase v := by
  unfold phase
  push_cast
  rw [mul_add, Complex.exp_add]

private theorem conj_phase (t : ℝ) : conj (phase t) = phase (-t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  have htwo : conj (2 : ℂ) = 2 := Complex.conj_natCast 2
  simp only [map_mul, htwo, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- A finite integral-phase sum times its conjugate is the sum over all differences. -/
theorem phase_sum_mul_conj {ι : Type*} (U : Finset ι) (b : ι → ℤ) (α : ℝ) :
    (∑ u ∈ U, phase (-α * (b u : ℝ))) * conj (∑ u ∈ U, phase (-α * (b u : ℝ))) =
      ∑ p ∈ U ×ˢ U, phase (-α * ((b p.1 - b p.2 : ℤ) : ℝ)) := by
  rw [map_sum, Finset.sum_mul, Finset.sum_product]
  simp_rw [Finset.mul_sum, conj_phase, ← phase_add_cover]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  push_cast
  ring

private theorem fourthMoment_eq_differenceEnergy (g : Polynomial ℤ) (L : ℝ) :
    (∫ α, ‖coverYSum g L α‖ ^ 4 ∂circleMeasure) =
      (differenceEnergy g (Finset.Icc (-⌊L⌋) ⌊L⌋) : ℝ) := by
  let U := Finset.Icc (-⌊L⌋) ⌊L⌋
  let E (α : ℝ) := ∑ p ∈ U ×ˢ U, phase (-α * (valueDifference g p : ℝ))
  have hE (α : ℝ) : (↑(‖coverYSum g L α‖ ^ 2) : ℂ) = E α := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    exact phase_sum_mul_conj U g.eval α
  have hphase (α : ℝ) : (↑(‖coverYSum g L α‖ ^ 4) : ℂ) =
      ∑ p ∈ (U ×ˢ U) ×ˢ (U ×ˢ U),
        phase (-α * (((valueDifference g p.1 - valueDifference g p.2 : ℤ)) : ℝ)) := by
    rw [← phase_sum_mul_conj (U ×ˢ U) (valueDifference g) α]
    change _ = E α * conj (E α)
    rw [Complex.mul_conj', ← hE, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), ← Complex.ofReal_pow, ← pow_mul]
  have horth (m : ℤ) :
      (∫ α, phase (-α * (m : ℝ)) ∂circleMeasure) = if m = 0 then 1 else 0 := by
    simpa only [Int.cast_neg, mul_neg, neg_mul, neg_eq_zero] using
      phase_integer_orthogonality (-m)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hphase]
  rw [integral_finsetSum]
  · simp_rw [horth, sub_eq_zero]
    change _ = (↑(differenceEnergy g U) : ℂ)
    rw [differenceEnergy, Finset.card_filter]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  · intro p _
    have hc : Continuous (fun α : ℝ =>
        phase (-α * ((valueDifference g p.1 - valueDifference g p.2 : ℤ) : ℝ))) := by
      unfold phase
      fun_prop
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self


/-- A polynomial of fixed degree grows at most like that power of the radius on a box. -/
theorem eval_abs_le_degree_power (g : Polynomial ℤ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ L ≥ 1, ∀ y : ℤ, |(y : ℝ)| ≤ L →
      |((g.eval y : ℤ) : ℝ)| ≤ A * L ^ g.natDegree := by
  let A : ℝ := 1 + ∑ i ∈ g.support, |(g.coeff i : ℝ)|
  have hA : 1 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨A, hA, ?_⟩
  intro L hL y hy
  have hL₀ : (0 : ℝ) ≤ L := by linarith
  rw [eval_eq_sum, Polynomial.sum_def]
  push_cast
  calc
    _ ≤ ∑ i ∈ g.support, |(g.coeff i : ℝ) * (y : ℝ) ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ g.support, |(g.coeff i : ℝ)| * L ^ g.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (abs_nonneg _) hy _).trans
          (pow_le_pow_right₀ hL (le_natDegree_of_ne_zero (mem_support_iff.1 hi)))) (abs_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg hL₀ _)

private theorem yInterval_card_le_three_mul {L : ℝ} (hL : 1 ≤ L) :
    ((Finset.Icc (-⌊L⌋) ⌊L⌋).card : ℝ) ≤ 3 * L := by
  have hfloor : 0 ≤ ⌊L⌋ := Int.floor_nonneg.mpr (by linarith)
  have hcard : ((Finset.Icc (-⌊L⌋) ⌊L⌋).card : ℝ) =
      (⌊L⌋ : ℝ) + 1 - (-(⌊L⌋ : ℝ)) := by
    exact_mod_cast Int.card_Icc_of_le (-⌊L⌋) ⌊L⌋ (by omega)
  rw [hcard]
  linarith [Int.floor_le L]

private theorem abs_le_of_mem_yInterval {L : ℝ} {y : ℤ} (hy : y ∈ Finset.Icc (-⌊L⌋) ⌊L⌋) :
    |(y : ℝ)| ≤ L := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.1 hy
  have hlow : -(⌊L⌋ : ℝ) ≤ y := by exact_mod_cast hlo
  have hhigh : (y : ℝ) ≤ ⌊L⌋ := by exact_mod_cast hhi
  exact abs_le.2 ⟨by linarith [Int.floor_le L], hhigh.trans (Int.floor_le L)⟩

/-- The classical fourth-moment estimate in Section 7 of `v2.tex`.
The exponent loss can be arbitrarily small and the implied constant
is uniform in the radius `L`. -/
theorem coverYSum_fourthMoment_le (g : Polynomial ℤ) (hg : 2 ≤ g.natDegree)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ L ≥ 1, (∫ α, ‖coverYSum g L α‖ ^ 4 ∂circleMeasure) ≤ K * L ^ (2 + ε) := by
  obtain ⟨A, hA, hAval⟩ := eval_abs_le_degree_power g
  have hg₀ : (0 : ℝ) < g.natDegree := by exact_mod_cast (show 0 < g.natDegree by omega)
  let θ := ε / (g.natDegree : ℝ)
  have hθ : 0 < θ := div_pos hε hg₀
  obtain ⟨K, hK, hdiv⟩ := card_divisors_le_rpow θ hθ
  let D := (g.natDegree : ℝ) * (2 * K * (2 * A) ^ θ)
  have hD : 0 < D := by
    dsimp [D]
    have hK₀ : 0 < K := by linarith
    have hA₀ : 0 < A := by linarith
    positivity
  refine ⟨9 * ((g.natDegree : ℝ) ^ 2 + D), by positivity, ?_⟩
  intro L hL
  have hLpos : 0 < L := by linarith
  let U := Finset.Icc (-⌊L⌋) ⌊L⌋
  have h₁ : 1 ≤ L ^ ε := Real.one_le_rpow hL hε.le
  have hLε : 0 ≤ L ^ ε := Real.rpow_nonneg hLpos.le _
  have hcard : (U.card : ℝ) ≤ 3 * L := yInterval_card_le_three_mul hL
  have hbound : ∀ p ∈ U ×ˢ U, valueDifference g p ≠ 0 →
      (↑(g.natDegree * (2 * (valueDifference g p).natAbs.divisors.card)) : ℝ) ≤ D * L ^ ε := by
    intro p hp hb
    let b := valueDifference g p
    obtain ⟨hpu, hpv⟩ := Finset.mem_product.1 hp
    have habs : (b.natAbs : ℝ) ≤ 2 * A * L ^ g.natDegree := by
      dsimp only [b, valueDifference]
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
      have hu := hAval L hL p.1 (abs_le_of_mem_yInterval hpu)
      have hv := hAval L hL p.2 (abs_le_of_mem_yInterval hpv)
      have ht := abs_sub_le ((g.eval p.1 : ℤ) : ℝ) 0 ((g.eval p.2 : ℤ) : ℝ)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      exact ht.trans (by linarith)
    have hnat : 0 < b.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hb)
    have hcast : ((b.natAbs.divisors.card : ℕ) : ℝ) ≤
        K * ((2 * A) ^ θ * L ^ ε) := by
      calc
        _ ≤ K * (b.natAbs : ℝ) ^ θ := hdiv _ hnat
        _ ≤ K * (2 * A * L ^ g.natDegree) ^ θ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) habs hθ.le)
            (zero_le_one.trans hK)
        _ = _ := by
          rw [Real.mul_rpow (by linarith) (pow_nonneg hLpos.le _), ← Real.rpow_natCast,
            ← Real.rpow_mul hLpos.le]
          have he : (g.natDegree : ℝ) * θ = ε := by dsimp [θ]; field_simp
          rw [he]
    push_cast
    change (g.natDegree : ℝ) * (2 * (b.natAbs.divisors.card : ℝ)) ≤ D * L ^ ε
    dsimp only [D]
    grw [hcast]
    ring_nf
    rfl
  rw [fourthMoment_eq_differenceEnergy]
  calc
    _ ≤ ((g.natDegree : ℝ) ^ 2 + D * L ^ ε) * (U.card : ℝ) ^ 2 :=
      differenceEnergy_le hg U _ (mul_nonneg hD.le hLε) hbound
    _ ≤ (((g.natDegree : ℝ) ^ 2 + D) * L ^ ε) * (3 * L) ^ 2 := by
      apply mul_le_mul
      · rw [add_mul]
        exact add_le_add (le_mul_of_one_le_right (sq_nonneg _) h₁) le_rfl
      · exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard _
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add hLpos, Real.rpow_two]; ring

/-- The fourth-moment input in the Serre bound, expressed on the natural
scale of the cover with any fixed radius multiplier `C ≥ 1`. -/
theorem coverYSum_fourthMoment {d e : ℕ} (hd : 0 < d) (he : 2 ≤ e)
    (g : Polynomial ℤ) (hg : g.natDegree = e) {C : ℝ} (hC : 1 ≤ C) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, (ENNReal.ofReal ‖coverYSum g (C * P ^ ((d : ℝ) / e)) α‖) ^ (4 : ℝ)
        ∂circleMeasure) (2 * (d : ℝ) / e + ε) := by
  intro ε hε
  let k := (d : ℝ) / e
  have hk : 0 < k := div_pos (by exact_mod_cast hd) (by exact_mod_cast (show 0 < e by omega))
  let ε' := ε / k
  have hε' : 0 < ε' := div_pos hε hk
  obtain ⟨K, hK, hbound⟩ := coverYSum_fourthMoment_le g (by rwa [hg]) ε' hε'
  apply coverPowerBound_of_realConstant
  refine ⟨K * C ^ (2 + ε'), mul_pos hK (Real.rpow_pos_of_pos (by linarith) _), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP
  have hPpos : 0 < P := by linarith
  let L := C * P ^ k
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hP hk.le)
  have hcont : Continuous (fun α => ‖coverYSum g L α‖ ^ (4 : ℕ)) :=
    (continuous_coverYSum g L).norm.pow 4
  have hint : Integrable (fun α => ‖coverYSum g L α‖ ^ (4 : ℕ)) circleMeasure :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpow (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := Real.rpow_natCast x 4
  simp only [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4),
    hpow]
  change (∫⁻ α, ENNReal.ofReal (‖coverYSum g L α‖ ^ (4 : ℕ)) ∂circleMeasure) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine (hbound L hL).trans_eq ?_
  dsimp only [L]
  rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hPpos.le _), ← Real.rpow_mul hPpos.le]
  have heq : k * (2 + ε') = 2 * (d : ℝ) / e + ε := by
    have hcancel : k * ε' = ε := by dsimp [ε']; field_simp
    rw [mul_add, hcancel]
    dsimp [k]
    ring
  rw [heq]
  ring

/-- The degree-two case of the cover moment in Equation `eq:cover-moment`
of `v2.tex`. The selected exponent is exactly four. -/
theorem coverYSum_coverMoment_quadratic {d : ℕ} (hd : 0 < d)
    (g : Polynomial ℤ) (hg : g.natDegree = 2) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, (ENNReal.ofReal ‖coverYSum g (P ^ ((d : ℝ) / 2)) α‖) ^
        (coverMomentExponent 2 : ℝ) ∂circleMeasure)
      ((d : ℝ) / 2 * coverMomentExponent 2 - d + ε) := by
  intro ε hε
  have h₄ : coverMomentExponent 2 = 4 := by decide
  have heq : (d : ℝ) / 2 * (4 : ℕ) - d + ε = 2 * (d : ℝ) / 2 + ε := by
    push_cast
    ring
  rw [h₄, heq]
  simpa only [Nat.cast_ofNat, one_mul] using
    coverYSum_fourthMoment hd (le_refl 2) g hg (C := 1) le_rfl ε hε


end

end Birch
