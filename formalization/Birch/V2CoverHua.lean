import Birch.V2CoverFourthMoment
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Iterated differences for Hua's lemma

The argument uses the differencing and Fourier coefficient counting in
Vaughan's *The Hardy-Littlewood Method*, Lemma 2.5. The polynomial and the
finite interval are kept explicit to cover the polynomial sums in `v2.tex`.
-/

namespace Birch

open Finset Filter MeasureTheory Polynomial
open scoped ComplexConjugate ENNReal

noncomputable section

private theorem natDegree_taylor_sub_eq (g : Polynomial ℤ) (hg : 0 < g.natDegree)
    {h : ℤ} (hh : h ≠ 0) : (g.taylor h - g).natDegree = g.natDegree - 1 := by
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.2
    intro n hn
    by_cases he : n = g.natDegree
    · subst n
      rw [coeff_sub, coeff_taylor_natDegree, coeff_natDegree, sub_self]
    · have hn' : g.natDegree < n := by omega
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt hn',
        coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_taylor]), sub_zero]
  · let j := g.natDegree - 1
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
    have hcoeff : (g.taylor h - g).coeff j = p.coeff 1 * h := by
      rw [coeff_sub, taylor_coeff, hcoeff₀,
        show (hasseDeriv j g).eval h = p.eval h by rfl, heval h, heval 0]
      ring
    exact le_natDegree_of_ne_zero (hcoeff ▸ mul_ne_zero hp₁ hh)

/-- The polynomial obtained by taking the forward differences indexed by the shifts. -/
def huaDifference (g : Polynomial ℤ) : List ℤ → Polynomial ℤ
  | [] => g
  | h :: hs => (huaDifference g hs).taylor h - huaDifference g hs

/-- The domain on which all the terms in an iterated difference are supported. -/
def huaDifferenceDomain (U : Finset ℤ) : List ℤ → Finset ℤ
  | [] => U
  | h :: hs => (huaDifferenceDomain U hs).filter fun y => y + h ∈ huaDifferenceDomain U hs

theorem eval_huaDifference_cons (g : Polynomial ℤ) (h : ℤ) (hs : List ℤ) (y : ℤ) :
    (huaDifference g (h :: hs)).eval y =
      (huaDifference g hs).eval (y + h) - (huaDifference g hs).eval y := by
  simp [huaDifference, taylor_apply, eval_comp]

/-- Each shift divides every value of the iterated difference. -/
theorem dvd_eval_huaDifference_of_mem (g : Polynomial ℤ) {hs : List ℤ}
    {h : ℤ} (hh : h ∈ hs) (y : ℤ) : h ∣ (huaDifference g hs).eval y := by
  induction hs generalizing y with
  | nil => simp at hh
  | cons k ks ih =>
    rw [eval_huaDifference_cons]
    rcases List.mem_cons.1 hh with e | hh
    · subst k
      simpa using sub_dvd_eval_sub (y + h) y (huaDifference g ks)
    · exact dvd_sub (ih hh _) (ih hh _)

/-- With nonzero shifts, each difference decreases the degree by one. -/
theorem natDegree_huaDifference (g : Polynomial ℤ) (hs : List ℤ)
    (hdeg : hs.length ≤ g.natDegree) (hzero : 0 ∉ hs) :
    (huaDifference g hs).natDegree = g.natDegree - hs.length := by
  induction hs with
  | nil => simp [huaDifference]
  | cons h hs ih =>
    have hh : h ≠ 0 := fun e => hzero (List.mem_cons.2 (Or.inl e.symm))
    have hzero' : 0 ∉ hs := fun hx => hzero (List.mem_cons.2 (Or.inr hx))
    have hlen : hs.length < g.natDegree := by simp only [List.length_cons] at hdeg; omega
    have hi := ih (Nat.le_of_lt hlen) hzero'
    have hpos : 0 < (huaDifference g hs).natDegree := by rw [hi]; omega
    rw [huaDifference, natDegree_taylor_sub_eq _ hpos hh, hi]
    simp only [List.length_cons]
    omega

theorem huaDifferenceDomain_subset (U : Finset ℤ) (hs : List ℤ) : huaDifferenceDomain U hs ⊆ U := by
  induction hs with
  | nil => exact Finset.Subset.rfl
  | cons h hs ih => exact (Finset.filter_subset _ _).trans ih

/-- At a point of the difference domain, the uniform bound for the original
polynomial increases by at most `2 ^ hs.length` under iteration. -/
theorem abs_eval_huaDifference_le (g : Polynomial ℤ) (U : Finset ℤ) (hs : List ℤ)
    {B : ℝ} (hB : ∀ y ∈ U, |((g.eval y : ℤ) : ℝ)| ≤ B) :
    ∀ y ∈ huaDifferenceDomain U hs,
      |(((huaDifference g hs).eval y : ℤ) : ℝ)| ≤ (2 : ℝ) ^ hs.length * B := by
  induction hs with
  | nil => simpa [huaDifferenceDomain, huaDifference]
  | cons h hs ih =>
    intro y hy
    obtain ⟨hy₁, hy₂⟩ := Finset.mem_filter.1 hy
    rw [eval_huaDifference_cons, Int.cast_sub, List.length_cons, pow_succ]
    have ht := abs_sub_le (((huaDifference g hs).eval (y + h) : ℤ) : ℝ)
      0 (((huaDifference g hs).eval y : ℤ) : ℝ)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    exact ht.trans (by linarith [ih _ hy₁, ih _ hy₂])

/-- All shift lists at a given differencing depth. -/
def huaShifts (H : Finset ℤ) : ℕ → Finset (List ℤ)
  | 0 => {[]}
  | j + 1 => (huaShifts H j ×ˢ H).image fun p => p.2 :: p.1

private theorem cons_swap_injective : Function.Injective (fun p : List ℤ × ℤ => p.2 :: p.1) := by
  intro p q e
  obtain ⟨e₂, e₁⟩ := List.cons.inj e
  exact Prod.ext e₁ e₂

theorem mem_huaShifts_iff {H : Finset ℤ} {j : ℕ} {hs : List ℤ} :
    hs ∈ huaShifts H j ↔ hs.length = j ∧ ∀ h ∈ hs, h ∈ H := by
  induction j generalizing hs with
  | zero => cases hs <;> simp [huaShifts]
  | succ j ih =>
    cases hs with
    | nil =>
      simp [huaShifts]
    | cons h hs =>
      simp [huaShifts, ih, List.mem_cons, forall_eq_or_imp, and_left_comm, and_assoc,
        List.cons.injEq]

theorem card_huaShifts (H : Finset ℤ) (j : ℕ) : (huaShifts H j).card = H.card ^ j := by
  induction j with
  | zero => simp [huaShifts]
  | succ j ih =>
    rw [huaShifts, Finset.card_image_of_injective _ cons_swap_injective, Finset.card_product,
      ih, pow_succ]

/-- A polynomial circle sum over a finite set of integers. -/
abbrev polynomialPhaseSum (U : Finset ℤ) (g : Polynomial ℤ) (α : ℝ) : ℂ :=
  ∑ x ∈ U, phase (-α * ((g.eval x : ℤ) : ℝ))

/-- The exponential sum over all iterated shifted polynomials with their
intersection domains. -/
def huaDifferenceSum (H U : Finset ℤ) (g : Polynomial ℤ) (j : ℕ) (α : ℝ) : ℂ :=
  ∑ hs ∈ huaShifts H j, polynomialPhaseSum (huaDifferenceDomain U hs) (huaDifference g hs) α

private theorem sq_phaseSum_eq_shiftSum (H U : Finset ℤ) (g : Polynomial ℤ) (α : ℝ)
    (hH : ∀ a ∈ U, ∀ b ∈ U, a - b ∈ H) :
    (↑(‖polynomialPhaseSum U g α‖ ^ 2) : ℂ) =
      ∑ h ∈ H, polynomialPhaseSum (huaDifferenceDomain U [h]) (huaDifference g [h]) α := by
  unfold polynomialPhaseSum
  rw [Complex.ofReal_pow, ← Complex.mul_conj', phase_sum_mul_conj]
  let shift (p : ℤ × ℤ) := p.1 - p.2
  have hm : ∀ p ∈ U ×ˢ U, shift p ∈ H := by
    intro p hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hp
    exact hH _ ha _ hb
  rw [← Finset.sum_fiberwise_of_maps_to hm
    (fun p => phase (-α * ((g.eval p.1 - g.eval p.2 : ℤ) : ℝ)))]
  apply Finset.sum_congr rfl
  intro h _
  refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpU, hs⟩ := Finset.mem_filter.1 hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hpU
    have he : p.2 + h = p.1 := by dsimp [shift] at hs; omega
    exact Finset.mem_filter.2 ⟨hb, by rwa [he]⟩
  · intro p hp q hq e
    have hp' := (Finset.mem_filter.1 hp).2
    have hq' := (Finset.mem_filter.1 hq).2
    exact Prod.ext (by dsimp [shift] at hp' hq'; omega) e
  · intro y hy
    obtain ⟨hy, hyh⟩ := Finset.mem_filter.1 hy
    refine ⟨(y + h, y), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hyh, hy⟩, ?_⟩, rfl⟩
    dsimp [shift]
    omega
  · intro p hp
    have hs := (Finset.mem_filter.1 hp).2
    have he : p.2 + h = p.1 := by dsimp [shift] at hs; omega
    simp [huaDifference, taylor_apply, eval_comp, he]

private theorem huaDifferenceSum_succ (H U : Finset ℤ) (g : Polynomial ℤ) (j : ℕ) (α : ℝ)
    (hH : ∀ a ∈ U, ∀ b ∈ U, a - b ∈ H) :
    huaDifferenceSum H U g (j + 1) α =
      (↑(∑ hs ∈ huaShifts H j,
        ‖polynomialPhaseSum (huaDifferenceDomain U hs) (huaDifference g hs) α‖ ^ 2) : ℂ) := by
  unfold huaDifferenceSum
  rw [huaShifts, Finset.sum_image (fun _ _ _ _ he => cons_swap_injective he), Finset.sum_product,
    Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro hs _
  exact (sq_phaseSum_eq_shiftSum H (huaDifferenceDomain U hs) (huaDifference g hs) α
    (fun a ha b hb => hH a (huaDifferenceDomain_subset U hs ha) b
      (huaDifferenceDomain_subset U hs hb))).symm

private theorem huaDifferenceSum_re_nonneg (H U : Finset ℤ) (g : Polynomial ℤ) {j : ℕ} (hj : 0 < j)
    (α : ℝ) (hH : ∀ a ∈ U, ∀ b ∈ U, a - b ∈ H) : 0 ≤ (huaDifferenceSum H U g j α).re := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [huaDifferenceSum_succ H U g k α hH, Complex.ofReal_re]
  positivity

/-- The Weyl differencing step in Hua's proof, with the signs kept inside the
finite exponential sum for the later integration. -/
theorem norm_phaseSum_pow_le_huaDifferenceSum (H U : Finset ℤ) (g : Polynomial ℤ)
    (hH : ∀ a ∈ U, ∀ b ∈ U, a - b ∈ H) (α : ℝ) {j : ℕ} (hj : 0 < j) :
    ‖polynomialPhaseSum U g α‖ ^ (2 ^ j : ℕ) ≤
      (H.card : ℝ) ^ (2 ^ j - j - 1) * (huaDifferenceSum H U g j α).re := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [show (1 : ℕ) = 0 + 1 by rfl, huaDifferenceSum_succ H U g 0 α hH, Complex.ofReal_re]
    simp [huaShifts, huaDifference, huaDifferenceDomain]
  | succ j hj ih =>
    let A : List ℤ → ℝ := fun hs =>
      ‖polynomialPhaseSum (huaDifferenceDomain U hs) (huaDifference g hs) α‖
    have hCauchy : (∑ hs ∈ huaShifts H j, A hs) ^ 2 ≤
        (H.card : ℝ) ^ j * ∑ hs ∈ huaShifts H j, A hs ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (huaShifts H j)
        (fun _ => (1 : ℝ)) A
      simpa [card_huaShifts] using h
    have hsum : (huaDifferenceSum H U g j α).re ≤ ∑ hs ∈ huaShifts H j, A hs :=
      (Complex.re_le_norm _).trans (norm_sum_le _ _)
    have hsquare : (huaDifferenceSum H U g j α).re ^ 2 ≤
        (H.card : ℝ) ^ j * (huaDifferenceSum H U g (j + 1) α).re := by
      rw [huaDifferenceSum_succ H U g j α hH, Complex.ofReal_re]
      exact (pow_le_pow_left₀ (huaDifferenceSum_re_nonneg H U g hj α hH) hsum 2).trans hCauchy
    calc
      _ = (‖polynomialPhaseSum U g α‖ ^ (2 ^ j : ℕ)) ^ 2 := by rw [← pow_mul, pow_succ]
      _ ≤ ((H.card : ℝ) ^ (2 ^ j - j - 1) * (huaDifferenceSum H U g j α).re) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ih _
      _ ≤ (H.card : ℝ) ^ ((2 ^ j - j - 1) * 2) *
          ((H.card : ℝ) ^ j * (huaDifferenceSum H U g (j + 1) α).re) := by
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ = _ := by
        rw [← mul_assoc, ← pow_add]
        have he := Nat.lt_two_pow_self (n := j)
        rw [pow_succ]
        congr 2
        omega


private abbrev huaSamples (H U : Finset ℤ) (j : ℕ) : Finset (List ℤ × ℤ) :=
  ((huaShifts H j) ×ˢ U).filter fun p => p.2 ∈ huaDifferenceDomain U p.1

private theorem mem_huaSamples {H U : Finset ℤ} {j : ℕ} {p : List ℤ × ℤ} :
    p ∈ huaSamples H U j ↔ p.1 ∈ huaShifts H j ∧ p.2 ∈ huaDifferenceDomain U p.1 := by
  constructor
  · intro h
    exact ⟨(Finset.mem_product.1 (Finset.mem_filter.1 h).1).1, (Finset.mem_filter.1 h).2⟩
  · rintro ⟨hshifts, hdom⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hshifts, huaDifferenceDomain_subset U p.1 hdom⟩,
      hdom⟩

private abbrev differenceFrequency (g : Polynomial ℤ) (p : List ℤ × ℤ) : ℤ :=
  (huaDifference g p.1).eval p.2

/-- The nonnegative Fourier coefficient attached to the difference frequency `b`. -/
def huaDifferenceCoefficient (H U : Finset ℤ) (g : Polynomial ℤ) (j : ℕ) (b : ℤ) : ℕ :=
  ((huaSamples H U j).filter fun p => differenceFrequency g p = b).card

private def signedDivisors (b : ℤ) : Finset ℤ :=
  let D := b.natAbs.divisors.image fun h : ℕ => (h : ℤ)
  D ∪ D.image Neg.neg

private theorem mem_signedDivisors_of_dvd {b h : ℤ} (hb : b ≠ 0) (hdvd : h ∣ b) :
    h ∈ signedDivisors b := by
  have hnat : h.natAbs ∣ b.natAbs := Int.dvd_natCast.1 (Int.dvd_natAbs.2 hdvd)
  have hmem : h.natAbs ∈ b.natAbs.divisors := Nat.mem_divisors.2 ⟨hnat, Int.natAbs_ne_zero.mpr hb⟩
  have hD : (h.natAbs : ℤ) ∈ b.natAbs.divisors.image (fun h : ℕ => (h : ℤ)) :=
    Finset.mem_image_of_mem _ hmem
  rcases Int.natAbs_eq h with e | e
  · exact Finset.mem_union_left _ (e ▸ hD)
  · exact Finset.mem_union_right _ (e ▸ Finset.mem_image_of_mem Neg.neg hD)

private theorem card_signedDivisors_le (b : ℤ) :
    (signedDivisors b).card ≤ 2 * b.natAbs.divisors.card := by
  let D := b.natAbs.divisors.image fun h : ℕ => (h : ℤ)
  calc
    _ ≤ D.card + (D.image Neg.neg).card := Finset.card_union_le _ _
    _ ≤ b.natAbs.divisors.card + b.natAbs.divisors.card :=
      Nat.add_le_add Finset.card_image_le (Finset.card_image_le.trans Finset.card_image_le)
    _ = _ := by omega

private theorem card_huaShiftFiber_le (H U : Finset ℤ) (g : Polynomial ℤ) (j : ℕ)
    (hs : List ℤ) (b : ℤ) :
    (((huaSamples H U j).filter fun p => differenceFrequency g p = b).filter
      fun p => p.1 = hs).card ≤ ((huaDifferenceDomain U hs).filter
        fun y => (huaDifference g hs).eval y = b).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    obtain ⟨hp, he⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    obtain ⟨hp, hval⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_filter.2 ⟨he ▸ (mem_huaSamples.1 hp).2, he ▸ hval⟩
  · intro p hp q hq e
    exact Prod.ext ((Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2.trans
      (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2.symm) e

/-- The nonzero-frequency coefficient is bounded by the degree times the
number of lists of signed divisors of that frequency. -/
theorem huaDifferenceCoefficient_ne_zero_le (H U : Finset ℤ) (g : Polynomial ℤ) {j : ℕ}
    (hj : j < g.natDegree) {b : ℤ} (hb : b ≠ 0) :
    huaDifferenceCoefficient H U g j b ≤ g.natDegree * (2 * b.natAbs.divisors.card) ^ j := by
  let T := (huaSamples H U j).filter fun p => differenceFrequency g p = b
  let S := huaShifts (signedDivisors b) j
  have hm : ∀ p ∈ T, p.1 ∈ S := by
    intro p hp
    obtain ⟨hmem, hf⟩ := Finset.mem_filter.1 hp
    refine mem_huaShifts_iff.2 ⟨(mem_huaShifts_iff.1 (mem_huaSamples.1 hmem).1).1, ?_⟩
    intro h hh
    exact mem_signedDivisors_of_dvd hb (hf ▸ dvd_eval_huaDifference_of_mem g hh p.2)
  refine (Finset.card_le_mul_card_image_of_maps_to hm g.natDegree ?_).trans ?_
  · intro hs hhs
    have hlen := (mem_huaShifts_iff.1 hhs).1
    by_cases hzero : 0 ∈ hs
    · have he : (T.filter fun p => p.1 = hs) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro p hp
        obtain ⟨hp, h⟩ := Finset.mem_filter.1 hp
        have he' := (Finset.mem_filter.1 hp).2
        have hdvd' := dvd_eval_huaDifference_of_mem g (h.symm ▸ hzero) p.2
        exact hb (zero_dvd_iff.1 (he' ▸ hdvd'))
      simp [he]
    · have hdeg := natDegree_huaDifference g hs (by omega) hzero
      exact (card_huaShiftFiber_le H U g j hs b).trans
        ((card_eval_fiber_le_natDegree _ (by rw [hdeg]; omega) _ _).trans (by rw [hdeg]; omega))
  · dsimp only [S]
    rw [card_huaShifts]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (card_signedDivisors_le b) _)

private abbrev zeroShifts (H : Finset ℤ) (j : ℕ) : Finset (List ℤ) :=
  (huaShifts H j).filter fun hs => (0 : ℤ) ∈ hs

private theorem card_zeroShifts_mul_le (H : Finset ℤ) (j : ℕ) :
    (zeroShifts H j).card * H.card ≤ j * H.card ^ j := by
  induction j with
  | zero => simp [zeroShifts, huaShifts]
  | succ j ih =>
    let f : List ℤ × ℤ → List ℤ := fun p => p.2 :: p.1
    let A := (zeroShifts H j ×ˢ H).image f
    let B := (huaShifts H j ×ˢ ({0} : Finset ℤ)).image f
    have hsub : zeroShifts H (j + 1) ⊆ A ∪ B := by
      intro hs hhs
      obtain ⟨hmem, hzero⟩ := Finset.mem_filter.1 hhs
      obtain ⟨⟨ks, h⟩, hp, rfl⟩ := Finset.mem_image.1 hmem
      obtain ⟨hks, hh⟩ := Finset.mem_product.1 hp
      rcases List.mem_cons.1 hzero with he | he
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
          (Finset.mem_product.2 ⟨hks, Finset.mem_singleton.2 he.symm⟩))
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _
          (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hks, he⟩, hh⟩))
    have hA : A.card ≤ (zeroShifts H j).card * H.card := by
      dsimp only [A]
      exact Finset.card_image_le.trans (Finset.card_product _ _).le
    have hB : B.card ≤ H.card ^ j := by
      dsimp only [B]
      refine Finset.card_image_le.trans ?_
      simp [card_huaShifts]
    calc
      _ ≤ (A.card + B.card) * H.card :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
      _ ≤ ((zeroShifts H j).card * H.card + H.card ^ j) * H.card :=
        Nat.mul_le_mul_right _ (Nat.add_le_add hA hB)
      _ = (zeroShifts H j).card * H.card * H.card + H.card ^ (j + 1) := by rw [add_mul, pow_succ]
      _ ≤ j * H.card ^ j * H.card + H.card ^ (j + 1) :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ ih) _
      _ = _ := by rw [pow_succ]; ring

/-- The zero-frequency coefficient is bounded even for shift lists containing
zero. Their cardinality loses one shift factor. -/
theorem huaDifferenceCoefficient_zero_le (H U : Finset ℤ) (g : Polynomial ℤ) {j : ℕ}
    (hj : j < g.natDegree) (hU : U.card ≤ H.card) :
    huaDifferenceCoefficient H U g j 0 ≤ (j + g.natDegree) * H.card ^ j := by
  classical
  let T := (huaSamples H U j).filter fun p => differenceFrequency g p = 0
  let S := huaShifts H j
  have hm : ∀ p ∈ T, p.1 ∈ S :=
    fun _ hp => (mem_huaSamples.1 (Finset.mem_filter.1 hp).1).1
  change T.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hm]
  have hfiber (hs : List ℤ) (hhs : hs ∈ S) :
      (T.filter fun p => p.1 = hs).card ≤ (if (0 : ℤ) ∈ hs then U.card else 0) + g.natDegree := by
    have hlen := (mem_huaShifts_iff.1 hhs).1
    have hf := card_huaShiftFiber_le H U g j hs 0
    by_cases hzero : 0 ∈ hs
    · have hsub : (huaDifferenceDomain U hs).filter
          (fun y => (huaDifference g hs).eval y = 0) ⊆ U :=
        (Finset.filter_subset _ _).trans (huaDifferenceDomain_subset U hs)
      exact (hf.trans (Finset.card_le_card hsub)).trans (by simp [hzero])
    · have hdeg := natDegree_huaDifference g hs (by omega) hzero
      exact hf.trans ((card_eval_fiber_le_natDegree _ (by rw [hdeg]; omega) _ _).trans
        (by rw [ite_eq_right hzero, zero_add, hdeg]; omega))
  calc
    _ ≤ ∑ hs ∈ S, ((if (0 : ℤ) ∈ hs then U.card else 0) + g.natDegree) :=
      Finset.sum_le_sum hfiber
    _ = (zeroShifts H j).card * U.card + H.card ^ j * g.natDegree := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
        Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      rw [card_huaShifts]
      rfl
    _ ≤ j * H.card ^ j + H.card ^ j * g.natDegree := by
      apply Nat.add_le_add_right
      exact (Nat.mul_le_mul_left _ hU).trans (card_zeroShifts_mul_le H j)
    _ = _ := by ring


private abbrev finitePhaseSum {ι : Type*} (A : Finset ι) (f : ι → ℤ) (α : ℝ) : ℂ :=
  ∑ a ∈ A, phase (-α * (f a : ℝ))

private theorem finitePhaseSum_mul {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) (α : ℝ) :
    finitePhaseSum A f α * finitePhaseSum B g α =
      finitePhaseSum (A ×ˢ B) (fun p => f p.1 + g p.2) α := by
  unfold finitePhaseSum
  rw [Finset.sum_mul, Finset.sum_product]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phaseSum_even_expansion (U : Finset ℤ) (g : Polynomial ℤ) (k : ℕ) :
    ∃ (ι : Type) (A : Finset ι) (f : ι → ℤ), A.card = U.card ^ (2 * k) ∧
      ∀ α, (↑(‖polynomialPhaseSum U g α‖ ^ (2 * k : ℕ)) : ℂ) = finitePhaseSum A f α := by
  induction k with
  | zero =>
    refine ⟨Unit, {()}, fun _ => 0, by simp, ?_⟩
    intro α
    simp [phase]
  | succ k ih =>
    obtain ⟨ι, A, f, hcard, hA⟩ := ih
    refine ⟨ι × (ℤ × ℤ), A ×ˢ (U ×ˢ U),
      fun p => f p.1 + (g.eval p.2.1 - g.eval p.2.2), ?_, ?_⟩
    · rw [Finset.card_product, Finset.card_product, hcard, ← sq, ← pow_add]
      congr 1
    · intro α
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, Complex.ofReal_mul, hA,
        Complex.ofReal_pow, ← Complex.mul_conj', phase_sum_mul_conj]
      exact finitePhaseSum_mul A (U ×ˢ U) f (fun p => g.eval p.1 - g.eval p.2) α

private theorem huaDifferenceSum_eq_phaseSum (H U : Finset ℤ) (g : Polynomial ℤ) (j : ℕ)
    (α : ℝ) : huaDifferenceSum H U g j α =
      finitePhaseSum (huaSamples H U j) (differenceFrequency g) α := by
  unfold huaDifferenceSum finitePhaseSum
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro hs _
  rw [← Finset.sum_filter]
  have heq : U.filter (fun y => y ∈ huaDifferenceDomain U hs) = huaDifferenceDomain U hs := by
    ext y
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨huaDifferenceDomain_subset U hs h, h⟩⟩
  rw [heq]

private theorem integral_eq_phaseFiber_card {ι : Type*} {A : Finset ι} {f : ι → ℤ}
    {F : ℝ → ℝ} (hF : ∀ α, (F α : ℂ) = finitePhaseSum A f α) :
    (∫ α, F α ∂circleMeasure) = ((A.filter fun a => f a = 0).card : ℝ) := by
  classical
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hF]
  unfold finitePhaseSum
  rw [integral_finsetSum]
  · have horth (m : ℤ) :
        (∫ α, phase (-α * (m : ℝ)) ∂circleMeasure) = if m = 0 then 1 else 0 := by
      simpa only [Int.cast_neg, mul_neg, neg_mul, neg_eq_zero] using
        phase_integer_orthogonality (-m)
    simp_rw [horth]
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> norm_num
  · intro a _
    have hc : Continuous (fun α : ℝ => phase (-α * (f a : ℝ))) := by
      unfold phase
      fun_prop
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

private theorem coeff_pair_count {ι κ : Type*} (A : Finset ι) (B : Finset κ)
    (f : ι → ℤ) (g : κ → ℤ) :
    ((A ×ˢ B).filter fun p => f p.1 + g p.2 = 0).card =
      ∑ a ∈ A, (B.filter fun b => g b = -f a).card := by
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : g b = -f a
  · simp [hb]
  · have he : f a + g b ≠ 0 := by omega
    simp [hb, he]

private theorem huaMixedMoment_le (H U : Finset ℤ) (g : Polynomial ℤ) {j : ℕ} (hj : 0 < j)
    (hH : ∀ a ∈ U, ∀ b ∈ U, a - b ∈ H) (Z R : ℝ) (hR₀ : 0 ≤ R)
    (hZ : (huaDifferenceCoefficient H U g j 0 : ℝ) ≤ Z)
    (hR : ∀ b ≠ 0, (huaDifferenceCoefficient H U g j b : ℝ) ≤ R) :
    (∫ α, ‖polynomialPhaseSum U g α‖ ^ (2 ^ j : ℕ) *
      (huaDifferenceSum H U g j α).re ∂circleMeasure) ≤
      Z * (∫ α, ‖polynomialPhaseSum U g α‖ ^ (2 ^ j : ℕ) ∂circleMeasure) +
        R * (U.card : ℝ) ^ (2 ^ j : ℕ) := by
  classical
  let f (α : ℝ) := ‖polynomialPhaseSum U g α‖ ^ (2 ^ j : ℕ)
  let D := huaDifferenceSum H U g j
  have hD (α : ℝ) : ((D α).re : ℂ) = D α := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    dsimp only [D]
    rw [hk, huaDifferenceSum_succ H U g k α hH, Complex.ofReal_re]
  have hexp : 2 * 2 ^ (j - 1) = 2 ^ j := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    simp [pow_succ, mul_comm]
  obtain ⟨ι, A, l, hAcard, hA⟩ := phaseSum_even_expansion U g (2 ^ (j - 1))
  rw [hexp] at hAcard hA
  let B := huaSamples H U j
  let m := differenceFrequency g
  have hAB (α : ℝ) : ((f α * (D α).re : ℝ) : ℂ) =
      finitePhaseSum (A ×ˢ B) (fun p => l p.1 + m p.2) α := by
    rw [Complex.ofReal_mul, hA, hD]
    dsimp only [D]
    rw [huaDifferenceSum_eq_phaseSum]
    exact finitePhaseSum_mul A B l m α
  change (∫ α, f α * (D α).re ∂circleMeasure) ≤
    Z * (∫ α, f α ∂circleMeasure) + R * (U.card : ℝ) ^ (2 ^ j : ℕ)
  rw [integral_eq_phaseFiber_card hAB, integral_eq_phaseFiber_card hA, coeff_pair_count]
  push_cast
  calc
    _ ≤ ∑ a ∈ A, ((if l a = 0 then Z else 0) + R) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : l a = 0
      · simp only [ha, neg_zero, ite_eq_left]
        exact hZ.trans (le_add_of_nonneg_right hR₀)
      · simp only [ite_eq_right ha, zero_add]
        exact hR _ (neg_ne_zero.mpr ha)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
        Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hAcard]
      push_cast
      ring


private theorem signed_divisor_power_bound {e j : ℕ} (he : 0 < e) (hj : 0 < j)
    {A : ℝ} (hA : 0 < A) {ε : ℝ} (hε : 0 < ε) :
    ∃ K > 0, ∀ L ≥ 1, ∀ b : ℤ, b ≠ 0 → (b.natAbs : ℝ) ≤ A * L ^ e →
      (2 * (b.natAbs.divisors.card : ℝ)) ^ j ≤ K * L ^ ε := by
  have he' : (0 : ℝ) < e := Nat.cast_pos.mpr he
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  let θ := ε / ((e : ℝ) * (j : ℝ))
  have hθ : 0 < θ := div_pos hε (mul_pos he' hj')
  obtain ⟨K, hK, hdiv⟩ := card_divisors_le_rpow θ hθ
  let B := (2 * K * A ^ θ) ^ j
  have hK₀ : 0 < K := zero_lt_one.trans_le hK
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro L hL b hb habs
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hnat : 0 < b.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hb)
  have hdiv' : (b.natAbs.divisors.card : ℝ) ≤ K * (A * L ^ e) ^ θ :=
    (hdiv _ hnat).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) habs hθ.le) hK₀.le)
  calc
    _ ≤ (2 * (K * (A * L ^ e) ^ θ)) ^ j := by
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hdiv' (by norm_num)) _
    _ = _ := by
      rw [Real.mul_rpow hA.le (pow_nonneg hLpos.le e), ← Real.rpow_natCast L e,
        ← Real.rpow_mul hLpos.le]
      calc
        _ = ((2 * K * A ^ θ) * L ^ ((e : ℝ) * θ)) ^ j := by congr 1; ring
        _ = B * L ^ ((e : ℝ) * θ * (j : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (L ^ _) j, ← Real.rpow_mul hLpos.le]
        _ = _ := by
          have h : (e : ℝ) * θ * (j : ℝ) = ε := by dsimp [θ]; field_simp
          rw [h]

private theorem huaDifferenceCoefficient_eventually_le (g : Polynomial ℤ) {j : ℕ}
    (hj : 0 < j) (hdeg : j < g.natDegree) {ε : ℝ} (hε : 0 < ε) :
    ∃ K > 0, ∀ L ≥ 1, ∀ (H : Finset ℤ) (b : ℤ), b ≠ 0 →
      (huaDifferenceCoefficient H (Finset.Icc (-⌊L⌋) ⌊L⌋) g j b : ℝ) ≤ K * L ^ ε := by
  obtain ⟨A, hA, hAval⟩ := eval_abs_le_degree_power g
  have hA₀ : 0 < A := zero_lt_one.trans_le hA
  have he : 0 < g.natDegree := hj.trans hdeg
  obtain ⟨K, hK, hbnd⟩ := signed_divisor_power_bound he hj
    (A := (2 : ℝ) ^ j * A) (by positivity) hε
  have he' : (0 : ℝ) < g.natDegree := Nat.cast_pos.mpr he
  refine ⟨(g.natDegree : ℝ) * K, mul_pos he' hK, ?_⟩
  intro L hL H b hb
  let U := Finset.Icc (-⌊L⌋) ⌊L⌋
  let c := huaDifferenceCoefficient H U g j b
  by_cases hc : c = 0
  · change (c : ℝ) ≤ _
    rw [hc, Nat.cast_zero]
    positivity
  have hcpos : 0 < c := Nat.pos_of_ne_zero hc
  obtain ⟨p, hp⟩ := Finset.card_pos.1 hcpos
  obtain ⟨hp, heq⟩ := Finset.mem_filter.1 hp
  obtain ⟨hp', hpU⟩ := mem_huaSamples.1 hp
  have hp' := (mem_huaShifts_iff.1 hp').1
  have hval (y : ℤ) (hy : y ∈ U) : |((g.eval y : ℤ) : ℝ)| ≤ A * L ^ g.natDegree := by
    apply hAval L hL
    obtain ⟨hy₀, hy₁⟩ := Finset.mem_Icc.1 hy
    have hl : -(⌊L⌋ : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy₀
    have hu : (y : ℝ) ≤ (⌊L⌋ : ℝ) := by exact_mod_cast hy₁
    exact abs_le.2 ⟨by linarith [Int.floor_le L], hu.trans (Int.floor_le L)⟩
  have hab : (b.natAbs : ℝ) ≤ ((2 : ℝ) ^ j * A) * L ^ g.natDegree := by
    have ht := abs_eval_huaDifference_le g U p.1 hval p.2 hpU
    change |((differenceFrequency g p : ℤ) : ℝ)| ≤ _ at ht
    rw [heq, hp'] at ht
    rwa [Nat.cast_natAbs, Int.cast_abs, mul_assoc]
  have hcount : (c : ℝ) ≤ (g.natDegree : ℝ) * (2 * (b.natAbs.divisors.card : ℝ)) ^ j := by
    exact_mod_cast huaDifferenceCoefficient_ne_zero_le H U g hdeg hb
  exact hcount.trans ((mul_le_mul_of_nonneg_left (hbnd L hL b hb hab) he'.le).trans_eq (by ring))

private theorem continuous_polynomialPhaseSum (U : Finset ℤ) (g : Polynomial ℤ) :
    Continuous (polynomialPhaseSum U g) := by
  unfold polynomialPhaseSum phase
  fun_prop

private theorem continuous_huaDifferenceSum (H U : Finset ℤ) (g : Polynomial ℤ) (j : ℕ) :
    Continuous (huaDifferenceSum H U g j) := by
  unfold huaDifferenceSum polynomialPhaseSum phase
  fun_prop

private theorem finiteInterval_radius_bounds {L : ℝ} (hL : 1 ≤ L) :
    let U := Finset.Icc (-⌊L⌋) ⌊L⌋
    let H := Finset.Icc (-(2 * ⌊L⌋)) (2 * ⌊L⌋)
    (∀ a ∈ U, ∀ b ∈ U, a - b ∈ H) ∧ U.card ≤ H.card ∧ (H.card : ℝ) ≤ 5 * L := by
  dsimp only
  have hfloor : 0 ≤ ⌊L⌋ := Int.floor_nonneg.mpr (by linarith)
  constructor
  · intro a ha b hb
    have ha := Finset.mem_Icc.1 ha
    have hb := Finset.mem_Icc.1 hb
    apply Finset.mem_Icc.2
    omega
  constructor
  · apply Finset.card_le_card
    intro t ht
    have ht := Finset.mem_Icc.1 ht
    apply Finset.mem_Icc.2
    omega
  · have hc : ((Finset.Icc (-(2 * ⌊L⌋)) (2 * ⌊L⌋)).card : ℝ) =
        2 * (⌊L⌋ : ℝ) + 1 - (-(2 * (⌊L⌋ : ℝ))) := by
      exact_mod_cast Int.card_Icc_of_le (-(2 * ⌊L⌋)) (2 * ⌊L⌋) (by omega)
    rw [hc]
    linarith [Int.floor_le L]

/-- Hua's moment bound for a fixed integral polynomial on the signed interval.
Here `j` ranges from two to the degree of the polynomial. -/
theorem coverYSum_huaMoment_le (g : Polynomial ℤ) {j : ℕ} (hj : 2 ≤ j)
    (hdeg : j ≤ g.natDegree) {ε : ℝ} (hε : 0 < ε) :
    ∃ K > 0, ∀ L ≥ 1, (∫ α, ‖coverYSum g L α‖ ^ (2 ^ j : ℕ) ∂circleMeasure) ≤
      K * L ^ (((2 ^ j - j : ℕ) : ℝ) + ε) := by
  induction j, hj using Nat.le_induction with
  | base =>
    simpa only [show (2 : ℕ) ^ 2 = 4 by decide, show (4 : ℕ) - 2 = 2 by decide, Nat.cast_ofNat]
      using coverYSum_fourthMoment_le g hdeg ε hε
  | succ j hj ih =>
    obtain ⟨K, hK, hKprev⟩ := ih (by omega)
    obtain ⟨C, hC, hCbound⟩ := huaDifferenceCoefficient_eventually_le g (show 0 < j by omega)
      (show j < g.natDegree by omega) hε
    let B : ℕ := 2 ^ j
    let a := B - j - 1
    let b := B - j
    let r : ℝ := (j + g.natDegree : ℕ)
    let K₁ : ℝ := 5 ^ a * r * 5 ^ j * K
    let K₂ : ℝ := 5 ^ a * C * 5 ^ B
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hK₁ : 0 ≤ K₁ := by dsimp [K₁]; positivity
    have hK₂ : 0 < K₂ := by dsimp [K₂]; positivity
    refine ⟨K₁ + K₂, add_pos_of_nonneg_of_pos hK₁ hK₂, ?_⟩
    intro L hL
    have hLp : 0 < L := zero_lt_one.trans_le hL
    let U := Finset.Icc (-⌊L⌋) ⌊L⌋
    let H := Finset.Icc (-(2 * ⌊L⌋)) (2 * ⌊L⌋)
    obtain ⟨hH, hU, hHmax⟩ := finiteInterval_radius_bounds hL
    let F (α : ℝ) := ‖polynomialPhaseSum U g α‖
    let D (α : ℝ) := (huaDifferenceSum H U g j α).re
    have hFcont : Continuous F := (continuous_polynomialPhaseSum U g).norm
    have hDcont : Continuous D := Complex.continuous_re.comp (continuous_huaDifferenceSum H U g j)
    have htarget : (∫ α, F α ^ (2 ^ (j + 1) : ℕ) ∂circleMeasure) ≤
        (H.card : ℝ) ^ a * (∫ α, F α ^ B * D α ∂circleMeasure) := by
      rw [← integral_const_mul]
      apply integral_mono
      · exact (hFcont.pow _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      · exact (continuous_const.mul ((hFcont.pow _).mul hDcont)).integrableOn_Icc.mono_set
          Set.Ioc_subset_Icc_self
      · intro α
        have hdiff := norm_phaseSum_pow_le_huaDifferenceSum H U g hH α (show 0 < j by omega)
        change F α ^ (2 ^ (j + 1) : ℕ) ≤ _
        calc
          _ = F α ^ B * F α ^ B := by rw [show (2 : ℕ) ^ (j + 1) = B + B by
            dsimp [B]; rw [pow_succ]; omega, pow_add]
          _ ≤ F α ^ B * ((H.card : ℝ) ^ a * D α) :=
            mul_le_mul_of_nonneg_left hdiff (pow_nonneg (norm_nonneg _) _)
          _ = _ := by ring
    have hZ : (huaDifferenceCoefficient H U g j 0 : ℝ) ≤ r * (H.card : ℝ) ^ j := by
      dsimp only [r]
      exact_mod_cast huaDifferenceCoefficient_zero_le H U g (show j < g.natDegree by omega) hU
    have hR : ∀ z ≠ 0, (huaDifferenceCoefficient H U g j z : ℝ) ≤ C * L ^ ε := by
      intro z hz
      exact hCbound L hL H z hz
    have hmix := huaMixedMoment_le H U g (show 0 < j by omega) hH
      (r * (H.card : ℝ) ^ j) (C * L ^ ε) (by positivity) hZ hR
    have hKint : (∫ α, F α ^ B ∂circleMeasure) ≤ K * L ^ ((b : ℝ) + ε) := hKprev L hL
    have hFnonneg : 0 ≤ ∫ α, F α ^ B ∂circleMeasure :=
      integral_nonneg (fun _ => by dsimp [F]; positivity)
    have hUpow : (U.card : ℝ) ≤ 5 * L := (Nat.cast_le.mpr hU).trans hHmax
    have hab : a + B = 2 ^ (j + 1) - (j + 1) := by
      have h := Nat.lt_two_pow_self (n := j)
      dsimp [a, B]
      rw [pow_succ]
      omega
    have hajb : a + j + b = 2 ^ (j + 1) - (j + 1) := by
      have h := Nat.lt_two_pow_self (n := j)
      dsimp [a, b, B]
      rw [pow_succ]
      omega
    change (∫ α, F α ^ (2 ^ (j + 1) : ℕ) ∂circleMeasure) ≤ _
    calc
      _ ≤ (H.card : ℝ) ^ a *
          (r * (H.card : ℝ) ^ j * (∫ α, F α ^ B ∂circleMeasure) +
            C * L ^ ε * (U.card : ℝ) ^ B) :=
        htarget.trans (mul_le_mul_of_nonneg_left hmix (by positivity))
      _ ≤ (5 * L) ^ a * (r * (5 * L) ^ j * (K * L ^ ((b : ℝ) + ε)) +
            C * L ^ ε * (5 * L) ^ B) := by
        gcongr
      _ = _ := by
        rw [mul_pow, mul_pow, mul_pow]
        calc
          _ = K₁ * (L ^ a * L ^ j * L ^ ((b : ℝ) + ε)) +
              K₂ * (L ^ a * L ^ B * L ^ ε) := by dsimp only [K₁, K₂]; ring
          _ = _ := by
            rw [← pow_add L a j, ← pow_add L a B, hab,
              ← Real.rpow_natCast L (a + j), ← Real.rpow_natCast L (2 ^ (j + 1) - (j + 1)),
              ← Real.rpow_add hLp, ← Real.rpow_add hLp,
              ← add_assoc, ← Nat.cast_add, hajb, add_mul]


/-- Hua's bound on the natural cover scale, with exponent `2 ^ e`. -/
theorem coverYSum_huaMoment {d e : ℕ} (hd : 0 < d) (he : 2 ≤ e)
    (g : Polynomial ℤ) (hg : g.natDegree = e) {C : ℝ} (hC : 1 ≤ C) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, (ENNReal.ofReal ‖coverYSum g (C * P ^ ((d : ℝ) / e)) α‖) ^
        ((2 ^ e : ℕ) : ℝ) ∂circleMeasure)
      ((d : ℝ) / e * ((2 ^ e : ℕ) : ℝ) - d + ε) := by
  intro ε hε
  let k := (d : ℝ) / e
  have he' : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hk : 0 < k := div_pos (by exact_mod_cast hd) he'
  let ε' := ε / k
  have hε' : 0 < ε' := div_pos hε hk
  obtain ⟨K, hK, hbound⟩ := coverYSum_huaMoment_le g he (by rw [hg]) hε'
  let M : ℕ := 2 ^ e
  let b : ℕ := M - e
  apply coverPowerBound_of_realConstant
  refine ⟨K * C ^ ((b : ℝ) + ε'), mul_pos hK (Real.rpow_pos_of_pos (by linarith) _), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP
  have hPpos : 0 < P := by linarith
  let L := C * P ^ k
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hP hk.le)
  have hcont : Continuous (fun α => ‖coverYSum g L α‖ ^ M) :=
    (continuous_coverYSum g L).norm.pow M
  have hint : Integrable (fun α => ‖coverYSum g L α‖ ^ M) circleMeasure :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  change (∫⁻ α, (ENNReal.ofReal ‖coverYSum g L α‖) ^ (M : ℝ) ∂circleMeasure) ≤ _
  simp only [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (Nat.cast_nonneg M), Real.rpow_natCast]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine (hbound L hL).trans_eq ?_
  dsimp only [L]
  rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hPpos.le _), ← Real.rpow_mul hPpos.le]
  have hme : e ≤ M := Nat.le_of_lt Nat.lt_two_pow_self
  have hb : (b : ℝ) = (M : ℝ) - e := Nat.cast_sub hme
  have heq : k * ((b : ℝ) + ε') = (d : ℝ) / e * (M : ℝ) - d + ε := by
    have hcancel : k * ε' = ε := by dsimp [ε']; field_simp
    rw [mul_add, hcancel, hb]
    dsimp [k]
    field_simp
  rw [show ((2 ^ e - e : ℕ) : ℝ) = (b : ℝ) by rfl, heq]
  ring

/-- Hua supplies the exact polynomial moment used in the cover asymptotic
when the cover degree is at most four. -/
theorem coverYSum_coverMoment_of_le_four {d e : ℕ} (hd : 0 < d) (he : 2 ≤ e)
    (he₄ : e ≤ 4) (g : Polynomial ℤ) (hg : g.natDegree = e) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, (ENNReal.ofReal ‖coverYSum g (P ^ ((d : ℝ) / e)) α‖) ^
        (coverMomentExponent e : ℝ) ∂circleMeasure)
      ((d : ℝ) / e * coverMomentExponent e - d + ε) := by
  have heq : coverMomentExponent e = 2 ^ e := by interval_cases e <;> decide
  rw [heq]
  simpa only [one_mul] using coverYSum_huaMoment hd he g hg (C := 1) le_rfl


end

end Birch
