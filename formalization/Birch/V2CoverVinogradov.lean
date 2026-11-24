import Birch.V2CoverHua

/-!
# From the Vinogradov mean value estimate to a one-polynomial moment

This reduction counts inhomogeneous power-sum fibers by the diagonal fiber
and fixes the first `e - 1` power-sum differences. The critical Vinogradov
estimate is an explicit hypothesis in the resulting Wooley moment bound.
-/

namespace Birch

open Finset MeasureTheory Polynomial
open scoped ComplexConjugate

noncomputable section

/-- The number of ordered pairs with a prescribed difference of vector values. -/
def differenceMultiplicity {ι G : Type*} [AddCommGroup G] [DecidableEq G]
    (U : Finset ι) (f : ι → G) (b : G) : ℕ :=
  ((U ×ˢ U).filter fun p => f p.1 - f p.2 = b).card

private theorem differenceMultiplicity_eq_sum {ι G : Type*} [AddCommGroup G] [DecidableEq G]
    (U : Finset ι) (f : ι → G) (b : G) :
    differenceMultiplicity U f b = ∑ v ∈ U.image f,
      (U.filter fun x => f x = v).card * (U.filter fun x => f x = v - b).card := by
  classical
  unfold differenceMultiplicity
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => f p.1) (t := U.image f)]
  · apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.card_product]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, e⟩, h₃⟩
      refine ⟨⟨h₁, h₃⟩, h₂, ?_⟩
      apply eq_sub_of_add_eq
      rw [← h₃, ← e]
      abel
    · rintro ⟨⟨h₁, h₃⟩, h₂, e⟩
      refine ⟨⟨⟨h₁, h₂⟩, ?_⟩, h₃⟩
      rw [h₃, e]
      abel
  · intro p hp
    exact Finset.mem_image_of_mem f (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1

/-- An inhomogeneous fiber of pair differences has at most the diagonal energy. -/
theorem differenceMultiplicity_le_diagonal {ι G : Type*} [AddCommGroup G] [DecidableEq G]
    (U : Finset ι) (f : ι → G) (b : G) :
    differenceMultiplicity U f b ≤ differenceMultiplicity U f 0 := by
  classical
  let V := U.image f
  let r (x : G) := (U.filter fun y => f y = x).card
  have hs : (∑ x ∈ V, (r (x - b)) ^ 2) ≤ ∑ x ∈ V, (r x) ^ 2 := by
    let W := V.image fun x => x - b
    have hW : ∑ x ∈ W, (r x) ^ 2 = ∑ x ∈ V, (r (x - b)) ^ 2 :=
      Finset.sum_image (fun x _ y _ h => sub_left_inj.1 h)
    have hz (x : G) (hx : x ∉ V) : r x = 0 := by
      apply Finset.card_eq_zero.2
      apply Finset.eq_empty_iff_forall_notMem.2
      intro y hy
      obtain ⟨hy, h⟩ := Finset.mem_filter.1 hy
      exact hx (h ▸ Finset.mem_image_of_mem f hy)
    calc
      _ = ∑ x ∈ W, (r x) ^ 2 := hW.symm
      _ = ∑ x ∈ W ∩ V, (r x) ^ 2 := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro x hx hwv
        have hxv : x ∉ V := fun h => hwv (Finset.mem_inter.2 ⟨hx, h⟩)
        simp [hz _ hxv]
      _ ≤ _ := Finset.sum_le_sum_of_subset Finset.inter_subset_right
  have h2 : 2 * (∑ x ∈ V, r x * r (x - b)) ≤ 2 * ∑ x ∈ V, r x ^ 2 := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ x ∈ V, (r x ^ 2 + r (x - b) ^ 2) := by
        apply Finset.sum_le_sum
        intro x _
        have h : 2 * ((r x : ℝ) * (r (x - b) : ℝ)) ≤
            (r x : ℝ) ^ 2 + (r (x - b) : ℝ) ^ 2 := by
          nlinarith [sq_nonneg ((r x : ℝ) - (r (x - b) : ℝ))]
        exact_mod_cast h
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, two_mul]
        exact Nat.add_le_add_left hs _
  rw [differenceMultiplicity_eq_sum, differenceMultiplicity_eq_sum]
  simp only [sub_zero, ← sq]
  change (∑ x ∈ V, r x * r (x - b)) ≤ ∑ x ∈ V, r x ^ 2
  omega

private abbrev powerSum {s : ℕ} (x : Fin s → ℤ) (j : ℕ) : ℤ := ∑ i, x i ^ j

private abbrev powerDifference {s : ℕ} (p : (Fin s → ℤ) × (Fin s → ℤ)) (j : ℕ) : ℤ :=
  powerSum p.1 j - powerSum p.2 j

/-- The vector of the first `k` power sums of a tuple. -/
def tuplePowerSums (k : ℕ) {s : ℕ} (x : Fin s → ℤ) : Fin k → ℤ :=
  fun j => powerSum x (j.val + 1)

/-- The sum of polynomial values at the entries of a tuple. -/
def tuplePolynomialSum (g : Polynomial ℤ) {s : ℕ} (x : Fin s → ℤ) : ℤ :=
  ∑ i, g.eval (x i)

private theorem tuplePolynomialSum_sub_eq {s k : ℕ} (g : Polynomial ℤ)
    (hg : g.natDegree = k + 1) (p : (Fin s → ℤ) × (Fin s → ℤ)) :
    tuplePolynomialSum g p.1 - tuplePolynomialSum g p.2 =
      ∑ j ∈ Finset.range (k + 2), g.coeff j * powerDifference p j := by
  have hEval (y : ℤ) : g.eval y = ∑ j ∈ Finset.range (k + 2), g.coeff j * y ^ j := by
    rw [eval_eq_sum_range, hg]
  have hsum (x : Fin s → ℤ) : tuplePolynomialSum g x =
      ∑ j ∈ Finset.range (k + 2), g.coeff j * powerSum x j := by
    unfold tuplePolynomialSum
    simp_rw [hEval]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hsum, hsum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  rw [mul_sub]

private theorem lastPowerDifference_eq {s k : ℕ} {g : Polynomial ℤ} (hg : g.natDegree = k + 1)
    {p q : (Fin s → ℤ) × (Fin s → ℤ)}
    (hp : tuplePolynomialSum g p.1 = tuplePolynomialSum g p.2)
    (hq : tuplePolynomialSum g q.1 = tuplePolynomialSum g q.2)
    (h : ∀ j : Fin k, powerDifference p (j.val + 1) = powerDifference q (j.val + 1)) :
    powerDifference p (k + 1) = powerDifference q (k + 1) := by
  have hP := tuplePolynomialSum_sub_eq g hg p
  have hQ := tuplePolynomialSum_sub_eq g hg q
  rw [hp, sub_self, Finset.sum_range_succ] at hP
  rw [hq, sub_self, Finset.sum_range_succ] at hQ
  have hlow : (∑ j ∈ Finset.range (k + 1), g.coeff j * powerDifference p j) =
      ∑ j ∈ Finset.range (k + 1), g.coeff j * powerDifference q j := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [powerDifference, powerSum]
    · have hj' := Finset.mem_range.1 hj
      let i : Fin k := ⟨j - 1, by omega⟩
      have he : i.val + 1 = j := by dsimp [i]; omega
      rw [← he, h i]
  have hc : g.coeff (k + 1) ≠ 0 := by
    rw [← hg, coeff_natDegree]
    have hgd : 0 < g.natDegree := by omega
    exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hgd)
  rw [hlow] at hP
  exact mul_left_cancel₀ hc (add_left_cancel (hP.symm.trans hQ))

/-- The one-polynomial diagonal moment is bounded by the number of lower
power-sum differences times the full power-sum diagonal moment. -/
theorem polynomial_diagonal_le_power_diagonal {s k : ℕ} (A : Finset (Fin s → ℤ))
    (g : Polynomial ℤ) (hg : g.natDegree = k + 1) (V : Finset (Fin k → ℤ))
    (hV : ∀ p ∈ A ×ˢ A, (fun j : Fin k => powerDifference p (j.val + 1)) ∈ V) :
    differenceMultiplicity A (tuplePolynomialSum g) 0 ≤
      differenceMultiplicity A (tuplePowerSums (k + 1)) 0 * V.card := by
  classical
  let T := (A ×ˢ A).filter fun p => tuplePolynomialSum g p.1 - tuplePolynomialSum g p.2 = 0
  let diff (p : (Fin s → ℤ) × (Fin s → ℤ)) (j : Fin k) := powerDifference p (j.val + 1)
  have hMap : ∀ p ∈ T, diff p ∈ V := fun p hp => hV p (Finset.mem_filter.1 hp).1
  refine Finset.card_le_mul_card_image_of_maps_to hMap _ ?_
  intro v _
  let S := T.filter fun p => diff p = v
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp⟩ := hS
    let w := tuplePowerSums (k + 1) p.1 - tuplePowerSums (k + 1) p.2
    have hsub : S ⊆ (A ×ˢ A).filter
        (fun q => tuplePowerSums (k + 1) q.1 - tuplePowerSums (k + 1) q.2 = w) := by
      intro q hq
      obtain ⟨hpT, hpv⟩ := Finset.mem_filter.1 hp
      obtain ⟨hqT, hqv⟩ := Finset.mem_filter.1 hq
      obtain ⟨_, hpe⟩ := Finset.mem_filter.1 hpT
      obtain ⟨hqA, hqe⟩ := Finset.mem_filter.1 hqT
      refine Finset.mem_filter.2 ⟨hqA, ?_⟩
      have hlow : ∀ j : Fin k, powerDifference q (j.val + 1) = powerDifference p (j.val + 1) :=
        congrFun (hqv.trans hpv.symm)
      have hlast := lastPowerDifference_eq hg (sub_eq_zero.1 hqe) (sub_eq_zero.1 hpe) hlow
      funext j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · exact hlow i
      · exact hlast
    exact (Finset.card_le_card hsub).trans
      (differenceMultiplicity_le_diagonal A (tuplePowerSums (k + 1)) w)
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.1 hS
    change S.card ≤ _
    rw [hz, Finset.card_empty]
    exact zero_le


/-- The finite box of tuples used in the Vinogradov mean value theorem. -/
def integerTupleBox (s : ℕ) (L : ℝ) : Finset (Fin s → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-⌊L⌋) ⌊L⌋

private def lowerDifferenceRadius (s : ℕ) (L : ℝ) (i : ℕ) : ℤ :=
  2 * (s : ℤ) * ⌊L⌋ ^ (i + 1)

private def lowerDifferenceBox (s k : ℕ) (L : ℝ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (-lowerDifferenceRadius s L i.val)
    (lowerDifferenceRadius s L i.val)

private theorem lowerDifference_mem_box {s k : ℕ} {L : ℝ} (hL : 1 ≤ L)
    {p : (Fin s → ℤ) × (Fin s → ℤ)}
    (hp : p ∈ integerTupleBox s L ×ˢ integerTupleBox s L) :
    (fun j : Fin k => powerDifference p (j.val + 1)) ∈ lowerDifferenceBox s k L := by
  have hfloor : 0 ≤ ⌊L⌋ := Int.floor_nonneg.mpr (by linarith)
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.1 hp
  apply Fintype.mem_piFinset.2
  intro j
  apply Finset.mem_Icc.2
  apply abs_le.1
  have hbound (x : Fin s → ℤ) (hx : x ∈ integerTupleBox s L) :
      |powerSum x (j.val + 1)| ≤ (s : ℤ) * ⌊L⌋ ^ (j.val + 1) := by
    calc
      _ ≤ ∑ i : Fin s, |x i ^ (j.val + 1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin s, ⌊L⌋ ^ (j.val + 1) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_le.2 (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i))) _
      _ = _ := by simp
  have ha := hbound p.1 hp₁
  have hb := hbound p.2 hp₂
  exact (abs_sub _ _).trans (by dsimp [lowerDifferenceRadius]; linarith)

/-- The first `k` power sums reduced modulo `m`. -/
def tuplePowerSumResidues (m k : ℕ) {s : ℕ} (x : Fin s → ℤ) : Fin k → ZMod m :=
  fun j => (tuplePowerSums k x j : ZMod m)

/-- At a modulus greater than the largest possible power-sum difference,
the congruence condition on a short box is the integral diagonal condition. -/
theorem tuplePowerSumResidues_eq_iff_of_mem {m s k : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hm : 2 * (s : ℤ) * ⌊L⌋ ^ k < (m : ℤ))
    {x y : Fin s → ℤ} (hx : x ∈ integerTupleBox s L) (hy : y ∈ integerTupleBox s L) :
    tuplePowerSumResidues m k x = tuplePowerSumResidues m k y ↔
      tuplePowerSums k x = tuplePowerSums k y := by
  constructor
  · intro h
    funext j
    have hj := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).1 (congrFun h j)
    have hd := Fintype.mem_piFinset.1
      (lowerDifference_mem_box (k := k) (p := (y, x)) hL (Finset.mem_product.2 ⟨hy, hx⟩)) j
    have hdiff : |tuplePowerSums k y j - tuplePowerSums k x j| ≤ lowerDifferenceRadius s L j.val :=
      abs_le.2 (Finset.mem_Icc.1 hd)
    have hL' : 1 ≤ ⌊L⌋ := Int.le_floor.2 (by simpa using hL)
    have hr : lowerDifferenceRadius s L j.val ≤ 2 * (s : ℤ) * ⌊L⌋ ^ k := by
      unfold lowerDifferenceRadius
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL' j.isLt) (by positivity)
    have habs := hdiff.trans_lt (hr.trans_lt hm)
    have hz : tuplePowerSums k y j - tuplePowerSums k x j = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hj
      have habs' : (((tuplePowerSums k y j - tuplePowerSums k x j).natAbs : ℕ) : ℤ) <
          (m : ℤ) := by rwa [Int.natCast_natAbs]
      exact_mod_cast habs'
    exact (sub_eq_zero.1 hz).symm
  · intro h
    funext j
    exact congrArg (Int.cast : ℤ → ZMod m) (congrFun h j)

/-- The diagonal count equals the complete system of congruences on any
modulus larger than the box's power-sum differences. -/
theorem powerSum_diagonal_eq_congruences {m s k : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (hm : 2 * (s : ℤ) * ⌊L⌋ ^ k < (m : ℤ)) :
    differenceMultiplicity (integerTupleBox s L) (tuplePowerSums k) 0 =
      differenceMultiplicity (integerTupleBox s L) (tuplePowerSumResidues m k) 0 := by
  unfold differenceMultiplicity
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, sub_eq_zero]
  exact and_congr_right fun hp => (tuplePowerSumResidues_eq_iff_of_mem hL hm hp.1 hp.2).symm

private theorem lowerDifferenceBox_card_le {s k : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    ((lowerDifferenceBox s k L).card : ℝ) ≤
      (4 * (s : ℝ) + 1) ^ k * L ^ (∑ j : Fin k, (j.val + 1)) := by
  have hL₀ : 0 ≤ L := by linarith
  have hfloor : 0 ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL₀
  have hc (i : Fin k) :
      ((Finset.Icc (-lowerDifferenceRadius s L i.val) (lowerDifferenceRadius s L i.val)).card : ℝ) ≤
        (4 * (s : ℝ) + 1) * L ^ (i.val + 1) := by
    let N := lowerDifferenceRadius s L i.val
    have hN : 0 ≤ N := by dsimp [N, lowerDifferenceRadius]; positivity
    have hcard : ((Finset.Icc (-N) N).card : ℝ) = (N : ℝ) + 1 - (-(N : ℝ)) := by
      exact_mod_cast Int.card_Icc_of_le (-N) N (by omega)
    change ((Finset.Icc (-N) N).card : ℝ) ≤ _
    rw [hcard]
    dsimp only [N, lowerDifferenceRadius]
    push_cast
    have hbound := pow_le_pow_left₀ (show 0 ≤ (⌊L⌋ : ℝ) by exact_mod_cast hfloor)
      (Int.floor_le L) (i.val + 1)
    have hLpow : 1 ≤ L ^ (i.val + 1) := one_le_pow₀ hL
    nlinarith [mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
  unfold lowerDifferenceBox
  rw [Fintype.card_piFinset, Nat.cast_prod]
  calc
    _ ≤ ∏ i : Fin k, (4 * (s : ℝ) + 1) * L ^ (i.val + 1) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun i _ => hc i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow_eq_pow_sum]

/-- The finite projection loses one factor for each attainable lower power sum. -/
theorem tuplePolynomialMoment_le_tuplePowerMoment {s k : ℕ} (g : Polynomial ℤ)
    (hg : g.natDegree = k + 1) {L : ℝ} (hL : 1 ≤ L) :
    (differenceMultiplicity (integerTupleBox s L) (tuplePolynomialSum g) 0 : ℝ) ≤
      ((4 * (s : ℝ) + 1) ^ k * L ^ (∑ j : Fin k, (j.val + 1))) *
        (differenceMultiplicity (integerTupleBox s L) (tuplePowerSums (k + 1)) 0 : ℝ) := by
  have h := polynomial_diagonal_le_power_diagonal (integerTupleBox s L) g hg
    (lowerDifferenceBox s k L) (fun _ hp => lowerDifference_mem_box hL hp)
  calc
    _ ≤ (differenceMultiplicity (integerTupleBox s L) (tuplePowerSums (k + 1)) 0 : ℝ) *
          ((lowerDifferenceBox s k L).card : ℝ) := by exact_mod_cast h
    _ ≤ _ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (lowerDifferenceBox_card_le hL) (Nat.cast_nonneg _)


private theorem prod_phase_neg_int {ι : Type*} (A : Finset ι) (v : ι → ℤ) (α : ℝ) :
    (∏ i ∈ A, phase (-α * (v i : ℝ))) = phase (-α * ((∑ i ∈ A, v i : ℤ) : ℝ)) := by
  classical
  induction A using Finset.induction with
  | empty => simp [phase]
  | @insert a A ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- Orthogonality identifies the even one-polynomial moment with a tuple count. -/
theorem coverYSum_evenMoment_eq_tupleCount (g : Polynomial ℤ) (s : ℕ) (L : ℝ) :
    (∫ α, ‖coverYSum g L α‖ ^ (2 * s : ℕ) ∂circleMeasure) =
      (differenceMultiplicity (integerTupleBox s L) (tuplePolynomialSum g) 0 : ℝ) := by
  classical
  let A := integerTupleBox s L
  let D (α : ℝ) := ∑ x ∈ A, phase (-α * (tuplePolynomialSum g x : ℝ))
  have hD (α : ℝ) : coverYSum g L α ^ s = D α := by
    unfold coverYSum
    rw [Finset.sum_pow']
    dsimp [D, A, integerTupleBox, tuplePolynomialSum]
    simp only [prod_phase_neg_int]
  have hnorm (α : ℝ) : (↑(‖coverYSum g L α‖ ^ (2 * s : ℕ)) : ℂ) =
      ∑ p ∈ A ×ˢ A, phase (-α * (((tuplePolynomialSum g p.1 - tuplePolynomialSum g p.2 : ℤ)) : ℝ)) := by
    rw [← phase_sum_mul_conj A (tuplePolynomialSum g)]
    change _ = D α * conj (D α)
    rw [Complex.mul_conj', ← hD, norm_pow, ← Complex.ofReal_pow, ← pow_mul, mul_comm s 2]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [hnorm]
  rw [integral_finsetSum]
  · have horth (m : ℤ) :
        (∫ α, phase (-α * (m : ℝ)) ∂circleMeasure) = if m = 0 then 1 else 0 := by
      simpa only [Int.cast_neg, mul_neg, neg_mul, neg_eq_zero] using
        phase_integer_orthogonality (-m)
    simp_rw [horth]
    change _ = (↑(differenceMultiplicity A (tuplePolynomialSum g) 0) : ℂ)
    unfold differenceMultiplicity
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> norm_num
  · intro p _
    have hc : Continuous (fun α : ℝ =>
        phase (-α * ((tuplePolynomialSum g p.1 - tuplePolynomialSum g p.2 : ℤ) : ℝ))) := by
      unfold phase
      fun_prop
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

/-- The critical number of variables on one side of the Vinogradov system. -/
def vinogradovCriticalIndex (e : ℕ) : ℕ := ∑ i : Fin e, (i.val + 1)

theorem vinogradovCriticalIndex_twice (e : ℕ) :
    2 * vinogradovCriticalIndex e = e * (e + 1) := by
  induction e with
  | zero => simp [vinogradovCriticalIndex]
  | succ e ih =>
    change 2 * (∑ i : Fin (e + 1), (i.val + 1)) = _
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    change 2 * (vinogradovCriticalIndex e + (e + 1)) = _
    rw [mul_add, ih]
    ring

/-- The critical Vinogradov mean value estimate, on a signed interval. -/
def CriticalVinogradovEstimate (e : ℕ) : Prop :=
  ∀ ε > 0, ∃ K > 0, ∀ L ≥ 1,
    (differenceMultiplicity (integerTupleBox (vinogradovCriticalIndex e) L) (tuplePowerSums e) 0 : ℝ) ≤
      K * L ^ ((vinogradovCriticalIndex e : ℝ) + ε)

private theorem exists_geometric_scale {p L : ℝ} (hp : 1 < p) (hL : 1 ≤ L) :
    ∃ H : ℕ, L ≤ p ^ H ∧ p ^ H ≤ p * L := by
  classical
  have h : ∃ H : ℕ, L ≤ p ^ H := by
    obtain ⟨H, hH⟩ := pow_unbounded_of_one_lt L hp
    exact ⟨H, hH.le⟩
  let H := Nat.find h
  refine ⟨H, Nat.find_spec h, ?_⟩
  by_cases hz : H = 0
  · rw [hz, pow_zero]
    exact one_le_mul_of_one_le_of_one_le hp.le hL
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hlt : p ^ j < L := lt_of_not_ge (Nat.find_min h (show j < H by omega))
    rw [hj, pow_succ']
    exact mul_le_mul_of_nonneg_left hlt.le (by linarith)

/-- A bound for the congruence count at the geometric sequence of lengths
`p^H` suffices for critical VMVT on every real interval length. The extra
fixed exponent `b` makes the congruence detect equality of integer sums. -/
theorem criticalVinogradovEstimate_of_primePowerCongruenceCounts {e p b : ℕ}
    (hp : 1 < p) (hb : 2 * vinogradovCriticalIndex e < p ^ b)
    (hcount : ∀ ε > 0, ∃ K > 0, ∀ H : ℕ,
      (differenceMultiplicity (integerTupleBox (vinogradovCriticalIndex e) ((p : ℝ)^H))
        (tuplePowerSumResidues (p^(H*e+b)) e) 0 : ℝ) ≤
          K * ((p : ℝ)^H) ^ ((vinogradovCriticalIndex e : ℝ) + ε)) :
    CriticalVinogradovEstimate e := by
  intro ε hε
  let s := vinogradovCriticalIndex e
  let a := (s : ℝ) + ε
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨K, hK, h⟩ := hcount ε hε
  refine ⟨K * (p : ℝ)^a, by positivity, fun L hL => ?_⟩
  obtain ⟨H, hHL, hHLe⟩ := exists_geometric_scale hpR hL
  let R := (p : ℝ)^H
  have hR : 1 ≤ R := hL.trans hHL
  have hsubset : integerTupleBox s L ⊆ integerTupleBox s R := by
    intro x hx
    apply Fintype.mem_piFinset.2
    intro i
    obtain ⟨hl, hu⟩ := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
    exact Finset.mem_Icc.2 ⟨(neg_le_neg (Int.floor_mono hHL)).trans hl, hu.trans (Int.floor_mono hHL)⟩
  have hcount_le : differenceMultiplicity (integerTupleBox s L) (tuplePowerSums e) 0 ≤
      differenceMultiplicity (integerTupleBox s R) (tuplePowerSums e) 0 := by
    unfold differenceMultiplicity
    apply Finset.card_le_card
    intro t ht
    obtain ⟨htb, ht⟩ := Finset.mem_filter.1 ht
    obtain ⟨htl, htr⟩ := Finset.mem_product.1 htb
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hsubset htl, hsubset htr⟩, ht⟩
  have hmod : 2 * (s : ℤ) * ⌊R⌋^e < ((p^(H*e+b) : ℕ) : ℤ) := by
    have hfloor : ⌊R⌋ = ((p^H : ℕ) : ℤ) := by
      have hcast : R = ((p^H : ℕ) : ℝ) := (Nat.cast_pow p H).symm
      rw [hcast]
      exact Int.floor_natCast _
    rw [hfloor]
    exact_mod_cast (show 2*s*(p^H)^e < p^(H*e+b) by
      rw [pow_add, pow_mul]
      simpa only [mul_comm] using Nat.mul_lt_mul_of_pos_right hb
        (pow_pos (pow_pos (by omega : 0 < p) _) _))
  calc
    _ ≤ (differenceMultiplicity (integerTupleBox s R) (tuplePowerSums e) 0 : ℝ) := by
      exact_mod_cast hcount_le
    _ ≤ K * R^a := by
      rw [powerSum_diagonal_eq_congruences hR hmod]
      exact h H
    _ ≤ K * ((p : ℝ)*L)^a :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hHLe ha) hK.le
    _ = _ := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (by linarith), ← mul_assoc]

/-- The one-polynomial Wooley bound follows from the critical Vinogradov
mean value estimate by fixing the first `e - 1` power-sum differences. -/
theorem coverYSum_wooleyMoment_le_of_vinogradov {e : ℕ} (he : 0 < e)
    (g : Polynomial ℤ) (hg : g.natDegree = e) (hvmvt : CriticalVinogradovEstimate e)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K > 0, ∀ L ≥ 1, (∫ α, ‖coverYSum g L α‖ ^ (e * (e + 1) : ℕ) ∂circleMeasure) ≤
      K * L ^ (((e : ℝ) ^ 2) + ε) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  let s := vinogradovCriticalIndex (k + 1)
  obtain ⟨K, hK, h⟩ := hvmvt ε hε
  let C := (4 * (s : ℝ) + 1) ^ k
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro L hL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [← vinogradovCriticalIndex_twice, coverYSum_evenMoment_eq_tupleCount]
  have heq : vinogradovCriticalIndex k + s = (k + 1) ^ 2 := by
    have hsum : 2 * (vinogradovCriticalIndex k + s) = 2 * (k + 1) ^ 2 := by
      rw [mul_add, vinogradovCriticalIndex_twice]
      dsimp only [s]
      rw [vinogradovCriticalIndex_twice]
      ring
    omega
  have heqR : (vinogradovCriticalIndex k : ℝ) + (s : ℝ) = ((k : ℝ) + 1) ^ 2 := by exact_mod_cast heq
  calc
    _ ≤ (C * L ^ vinogradovCriticalIndex k) *
          (differenceMultiplicity (integerTupleBox s L) (tuplePowerSums (k + 1)) 0 : ℝ) :=
      tuplePolynomialMoment_le_tuplePowerMoment g hg hL
    _ ≤ (C * L ^ vinogradovCriticalIndex k) * (K * L ^ ((s : ℝ) + ε)) :=
      mul_le_mul_of_nonneg_left (h L hL) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast L (vinogradovCriticalIndex k)]
      calc
        _ = C * K * (L ^ (vinogradovCriticalIndex k : ℝ) * L ^ ((s : ℝ) + ε)) := by ring
        _ = _ := by rw [← Real.rpow_add hLp, ← add_assoc, heqR]; simp


end

end Birch
