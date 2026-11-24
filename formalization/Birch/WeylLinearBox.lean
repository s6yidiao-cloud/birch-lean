import Birch.WeylFrequency
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Integer points in linear fibers of a Weyl box

A kernel of dimension r is determined by at most r coordinate projections.
The resulting integer-box bound is uniform in the linear map and the target.
-/

open Module

namespace Birch

noncomputable section

private theorem coordinate_projection_ker_aux {R : Type*} [Field R] {n : ℕ} (m : ℕ)
    (K : Submodule R (Fin n → R)) (hm : finrank R K = m) :
    ∃ I : Finset (Fin n), I.card ≤ m ∧
      ∀ x ∈ K, (∀ j ∈ I, x j = 0) → x = 0 := by
  classical
  induction m using Nat.strong_induction_on generalizing K with
  | h m ih =>
    by_cases hK : K = ⊥
    · refine ⟨∅, by simp, fun x hx _ => ?_⟩
      simpa [hK] using hx
    · obtain ⟨y, hyK, hy⟩ : ∃ y : Fin n → R, y ∈ K ∧ y ≠ 0 := by
        by_contra! h
        exact hK ((Submodule.eq_bot_iff K).mpr h)
      obtain ⟨i, hi⟩ : ∃ i : Fin n, y i ≠ 0 := by
        by_contra! h
        exact hy (funext h)
      let K₀ : Submodule R (Fin n → R) := K ⊓ LinearMap.ker (LinearMap.proj i)
      have hKle : K₀ ≤ K := inf_le_left
      have hstrict : K₀ < K := lt_of_le_of_ne hKle (by
        intro H
        have Hy : y ∈ K₀ := H.symm ▸ hyK
        exact hi (LinearMap.mem_ker.mp (Submodule.mem_inf.mp Hy).2))
      have hdim : finrank R K₀ < m := hm ▸ Submodule.finrank_lt_finrank_of_lt hstrict
      obtain ⟨I, hI, hvanish⟩ := ih _ hdim K₀ rfl
      refine ⟨insert i I, (Finset.card_insert_le _ _).trans (by omega), fun x hx hz => ?_⟩
      have hxi : x i = 0 := hz i (Finset.mem_insert_self _ _)
      have hx₀ : x ∈ K₀ := Submodule.mem_inf.mpr ⟨hx, LinearMap.mem_ker.mpr hxi⟩
      exact hvanish x hx₀ (fun j hj => hz j (Finset.mem_insert_of_mem hj))

/-- The coordinates of any subspace are determined by a subset of at most its
dimension many coordinate indices. -/
theorem exists_coordinate_projection_ker {R : Type*} [Field R] {n : ℕ} (K : Submodule R (Fin n → R)) :
    ∃ I : Finset (Fin n), I.card ≤ finrank R K ∧
      ∀ x ∈ K, (∀ j ∈ I, x j = 0) → x = 0 :=
  coordinate_projection_ker_aux (finrank R K) K rfl

/-- The number of integer points in a linear fiber with all coordinates in A is
at most the size of A to the dimension of the kernel. -/
theorem integer_fiber_card_le_finrank {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : (Fin n → ℝ) →ₗ[ℝ] V) (y : V) (A : Finset ℤ) (hA : A.Nonempty)
    (T : Finset (Fin n → ℤ)) (hcoord : ∀ x ∈ T, ∀ j, x j ∈ A) :
    letI := Classical.decEq V
    (T.filter (fun x => L (fun j => (x j : ℝ)) = y)).card ≤ A.card ^ finrank ℝ (LinearMap.ker L) := by
  classical
  obtain ⟨I, hI, hinj⟩ := exists_coordinate_projection_ker (LinearMap.ker L)
  let S := T.filter (fun x => L (fun j => (x j : ℝ)) = y)
  let f (x : Fin n → ℤ) (i : I) := x i
  have hcard : S.card ≤ (Fintype.piFinset (fun _ : I => A)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      apply Fintype.mem_piFinset.mpr
      intro i
      exact hcoord x (Finset.mem_filter.mp hx).1 i
    · intro x hx z hz he
      have hxa := (Finset.mem_filter.mp hx).2
      have hza := (Finset.mem_filter.mp hz).2
      let d : Fin n → ℝ := (fun j => (x j : ℝ)) - (fun j => (z j : ℝ))
      have hd : d ∈ LinearMap.ker L := by
        rw [LinearMap.mem_ker, show d = _ from rfl, map_sub, hxa, hza, sub_self]
      have hzero : d = 0 := hinj d hd fun j hj => by
        have hE : x j = z j := congrFun he (⟨j, hj⟩ : I)
        simp [d, hE]
      funext j
      have hE : (x j : ℝ) = (z j : ℝ) := sub_eq_zero.mp (congrFun hzero j)
      exact_mod_cast hE
  change S.card ≤ _
  refine hcard.trans ?_
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  exact Nat.pow_le_pow_right (Finset.card_pos.mpr hA) hI

/-- The Weyl box bound for an arbitrary real-linear fiber. The constant is
independent of both the coefficients of the linear map and the target value. -/
theorem integer_box_fiber_card_le {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : (Fin n → ℝ) →ₗ[ℝ] V) (y : V) {H : ℝ} (hH : 0 ≤ H) :
    letI := Classical.decEq V
    ((latticeBox n H).filter (fun x => L (fun j => (x j : ℝ)) = y)).card ≤
      (2 * H + 1) ^ finrank ℝ (LinearMap.ker L) := by
  classical
  let A : Finset ℤ := Finset.Icc (-⌊H⌋) ⌊H⌋
  have hfloor : 0 ≤ ⌊H⌋ := Int.floor_nonneg.mpr hH
  have hA : A.Nonempty := ⟨0, Finset.mem_Icc.mpr ⟨neg_nonpos.mpr hfloor, hfloor⟩⟩
  have h := integer_fiber_card_le_finrank L y A hA (latticeBox n H)
    (fun x hx j => Fintype.mem_piFinset.mp hx j)
  have hcard : (A.card : ℝ) ≤ 2 * H + 1 := by
    have he : (A.card : ℤ) = ⌊H⌋ + 1 - (-⌊H⌋) :=
      Int.card_Icc_of_le (-⌊H⌋) ⌊H⌋ (by omega)
    have her : (A.card : ℝ) = (⌊H⌋ : ℝ) + 1 - (-(⌊H⌋ : ℝ)) := by exact_mod_cast he
    linarith [Int.floor_le H]
  refine (show
      (((latticeBox n H).filter (fun x => L (fun j => (x j : ℝ)) = y)).card : ℝ) ≤
        (A.card : ℝ) ^ finrank ℝ (LinearMap.ker L) by exact_mod_cast h).trans ?_
  exact pow_le_pow_left₀ (by positivity) hcard _

end

end Birch
