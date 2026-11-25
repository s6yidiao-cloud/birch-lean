module

public import Birch.AffineDomainHeight
public import Birch.OriginKrullDimension
public import Birch.DeligneLevelClosure
public import Birch.MvPolynomialCoefficientCompat
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

/-! # Geometric irreducibility of the affine level hypersurfaces -/

open MvPolynomial
open scoped BigOperators

namespace Birch

/-- Two equations through the origin in at least three variables have
a common zero other than the origin. -/
theorem exists_nonzero_common_zero_of_two_equations {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (hn : 3 ≤ n) (A B : MvPolynomial (Fin n) K)
    (hA : A.eval 0 = 0) (hB : B.eval 0 = 0) :
    ∃ x : Fin n → K, x ≠ 0 ∧ A.eval x = 0 ∧ B.eval x = 0 := by
  classical
  by_contra! h
  let R := MvPolynomial (Fin n) K
  let S : Set R := {A, B}
  let O := vanishingIdeal K ({0} : Set (Fin n → K))
  have hSO : S ⊆ O := by
    intro u hu
    change u ∈ vanishingIdeal K ({0} : Set (Fin n → K))
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval]
    have hu' : u = A ∨ u = B := by simpa only [S, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hu
    rcases hu' with rfl | rfl
    · exact hA
    · exact hB
  have hz : zeroLocus K (Ideal.span S) ⊆ {0} := by
    intro x hx
    rw [zeroLocus_span] at hx
    by_contra hnot
    apply h x (Set.notMem_singleton_iff.mp hnot) (hx A (by simp [S]))
    exact hx B (by simp [S])
  have hh := ringKrullDim_le_height_of_affineDomain (K := K) O
  have hN : (n : WithBot ℕ∞) ≤ (O.height : WithBot ℕ∞) := by
    simpa [O, MvPolynomial.ringKrullDim_of_isNoetherianRing] using hh
  have hS : S.encard ≤ 2 := by
    calc
      _ ≤ ({A} : Set R).encard + ({B} : Set R).encard := by
        rw [show S = {A} ∪ {B} by ext x; simp [S, or_comm]]
        exact Set.encard_union_le _ _
      _ = _ := by simp only [Set.encard_singleton, one_add_one_eq_two]
  have h2 : (n : WithBot ℕ∞) ≤ (2 : WithBot ℕ∞) := calc
    _ ≤ ringKrullDim (R ⧸ Ideal.span S) + (S.encard : WithBot ℕ∞) :=
      hN.trans (Ideal.height_le_ringKrullDim_quotient_add_encard S hSO)
    _ ≤ _ := by
      exact (add_le_add (ringKrullDim_le_zero_of_zeroLocus_subset_origin _ hz)
        (WithBot.coe_le_coe.mpr hS)).trans_eq (zero_add _)
  have hnat : n ≤ 2 := by exact_mod_cast h2
  omega

private theorem top_homogeneousComponent_mul {ι K : Type*} [CommSemiring K]
    (A B : MvPolynomial ι K) :
    homogeneousComponent (A.totalDegree + B.totalDegree) (A * B) =
      homogeneousComponent A.totalDegree A * homogeneousComponent B.totalDegree B := by
  classical
  let a := A.totalDegree
  let b := B.totalDegree
  change homogeneousComponent (a + b) (A * B) =
    homogeneousComponent a A * homogeneousComponent b B
  calc
    _ = homogeneousComponent (a + b)
        ((∑ i ∈ Finset.range (a + 1), homogeneousComponent i A) *
          (∑ j ∈ Finset.range (b + 1), homogeneousComponent j B)) := by
      rw [show a = A.totalDegree from rfl, show b = B.totalDegree from rfl,
        sum_homogeneousComponent, sum_homogeneousComponent]
    _ = _ := by
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum, map_sum]
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · exact homogeneousComponent_eq_self
            ((homogeneousComponent_isHomogeneous a A).mul (homogeneousComponent_isHomogeneous b B))
        · intro j hj hne
          have hjb : j < b := by rw [Finset.mem_range] at hj; omega
          rw [homogeneousComponent_of_mem
            ((homogeneousComponent_isHomogeneous a A).mul (homogeneousComponent_isHomogeneous j B)),
            ite_eq_right (by omega : a + b ≠ a + j)]
        · simp
      · intro i hi hne
        have hia : i < a := by rw [Finset.mem_range] at hi; omega
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_range] at hj
        rw [homogeneousComponent_of_mem
          ((homogeneousComponent_isHomogeneous i A).mul (homogeneousComponent_isHomogeneous j B)),
          ite_eq_right (by omega : a + b ≠ i + j)]
      · simp

private theorem totalDegree_pos_of_nonzero_nonunit {ι K : Type*} [Field K]
    {A : MvPolynomial ι K} (hA : A ≠ 0) (hunit : ¬IsUnit A) :
    0 < A.totalDegree := by
  by_contra! h
  let c := A.coeff 0
  have hc : A = C c := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
  rw [hc] at hunit hA
  exact hunit ((isUnit_iff_ne_zero.mpr (fun h => hA (by simp [h]))).map C)

/-- A phase in at least three variables with an isolated leading critical
point is irreducible over its algebraically closed coefficient field. -/
theorem irreducible_of_isolated_leading_critical_point {K : Type*} [Field K] [IsAlgClosed K]
    {n r : ℕ} (hn : 3 ≤ n) (hr : 0 < r)
    {G : MvPolynomial (Fin n) K} (hG : G.totalDegree ≤ r)
    (hc : ∀ x : Fin n → K,
      (∀ i, (pderiv i (homogeneousComponent r G)).eval x = 0) → x = 0) :
    Irreducible G := by
  let L := homogeneousComponent r G
  have hL : L ≠ 0 := by
    intro h
    have hx : (fun _ : Fin n => (1 : K)) = 0 := hc _ (fun i => by
      change (pderiv i L).eval _ = 0
      simp [h])
    exact one_ne_zero (congrFun hx ⟨0, by omega⟩)
  have hdeg : G.totalDegree = r := le_antisymm hG (by
    by_contra! h
    exact hL (homogeneousComponent_eq_zero r G h))
  refine ⟨fun h => ?_, fun A B he => ?_⟩
  · obtain ⟨B, hB⟩ := isUnit_iff_dvd_one.mp h
    have hB₀ : B ≠ 0 := by
      intro hz
      simp [hz] at hB
    have hG₀ : G ≠ 0 := by
      intro hz
      simp [hz] at hB
    have hmul := totalDegree_mul_of_isDomain hG₀ hB₀
    rw [← hB, totalDegree_one, hdeg] at hmul
    omega
  · by_contra! nh
    obtain ⟨hnA, hnB⟩ := nh
    have hA : A ≠ 0 := by
      intro h
      apply hL
      simp [L, he, h]
    have hB : B ≠ 0 := by
      intro h
      apply hL
      simp [L, he, h]
    have ha := totalDegree_pos_of_nonzero_nonunit hA hnA
    have hb := totalDegree_pos_of_nonzero_nonunit hB hnB
    let U := homogeneousComponent A.totalDegree A
    let V := homogeneousComponent B.totalDegree B
    have hab := totalDegree_mul_of_isDomain hA hB
    rw [← he, hdeg] at hab
    have huv : L = U * V := by
      dsimp [L, U, V]
      rw [← top_homogeneousComponent_mul A B, ← he, ← hab]
    have hU : U.eval 0 = 0 := by
      have h := eval_scale_of_homogeneous (homogeneousComponent_isHomogeneous A.totalDegree A) 0
        (0 : Fin n → K)
      simpa only [mul_zero, ← Pi.zero_def, zero_pow ha.ne', zero_mul] using h
    have hV : V.eval 0 = 0 := by
      have h := eval_scale_of_homogeneous (homogeneousComponent_isHomogeneous B.totalDegree B) 0
        (0 : Fin n → K)
      simpa only [mul_zero, ← Pi.zero_def, zero_pow hb.ne', zero_mul] using h
    obtain ⟨x, hx, hu, hv⟩ := exists_nonzero_common_zero_of_two_equations hn U V hU hV
    apply hx
    apply hc x
    intro i
    change (pderiv i L).eval x = 0
    rw [huv]
    simp [hu, hv]

/-- Every affine level of a phase with an isolated leading critical point
is geometrically irreducible in at least three ambient variables. -/
theorem irreducible_sub_C_of_isolated_leading_critical_point {K : Type*} [Field K] [IsAlgClosed K]
    {n r : ℕ} (hn : 3 ≤ n) (hr : 0 < r)
    {G : MvPolynomial (Fin n) K} (hG : G.totalDegree ≤ r)
    (hc : ∀ x : Fin n → K,
      (∀ i, (pderiv i (homogeneousComponent r G)).eval x = 0) → x = 0) (t : K) :
    Irreducible (G - C t) := by
  apply irreducible_of_isolated_leading_critical_point hn hr
    ((totalDegree_sub _ _).trans (max_le hG (by simp)))
  rw [map_sub, homogeneousComponent_eq_zero r (C t) (by simpa only [totalDegree_C] using hr),
    sub_zero]
  exact hc

/-- The affine level ring after extension to an algebraically closed field
is a domain when its leading gradient is isolated. -/
theorem isDomain_level_quotient_after_base_change {k K : Type*} [Field k] [Field K]
    [IsAlgClosed K] (φ : k →+* K)
    {n r : ℕ} (hn : 3 ≤ n) (hr : 0 < r)
    {G : MvPolynomial (Fin n) k} (hG : G.totalDegree ≤ r)
    (hc : ∀ x : Fin n → K,
      (∀ i, (pderiv i (homogeneousComponent r G)).eval₂ φ x = 0) → x = 0) (t : k) :
    IsDomain (MvPolynomial (Fin n) K ⧸ Ideal.span {MvPolynomial.map φ G - C (φ t)}) := by
  have hdeg : (MvPolynomial.map φ G).totalDegree ≤ r :=
    (Finset.sup_mono (MvPolynomial.support_map_subset φ G)).trans hG
  have hmap : homogeneousComponent r (MvPolynomial.map φ G) =
      MvPolynomial.map φ (homogeneousComponent r G) := by
    ext m
    simp only [coeff_homogeneousComponent, coeff_map]
    split_ifs <;> simp
  have hcrit : ∀ x : Fin n → K,
      (∀ i, (pderiv i (homogeneousComponent r (MvPolynomial.map φ G))).eval x = 0) → x = 0 := by
    simpa only [hmap, pderiv_map, eval_map] using hc
  have h := irreducible_sub_C_of_isolated_leading_critical_point hn hr hdeg hcrit (φ t)
  let := (Ideal.span_singleton_prime h.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp h)
  infer_instance

end Birch
