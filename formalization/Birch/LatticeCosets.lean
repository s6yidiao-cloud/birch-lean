import Birch.CircleMethod
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Bounded representatives for the integral terminal slices

For an integral matrix of nonzero determinant, its image contains the lattice
of vectors divisible by the absolute determinant. Reduction to a finite coordinate
box then gives representatives for the actual quotient by the matrix image.
-/

open Matrix
open scoped Matrix

namespace Birch

private theorem mulVec_int_injective {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) : Function.Injective A.mulVec := by
  intro x y hxy
  have hz : A *ᵥ (x - y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  ext i
  by_contra hi
  have hne : (x - y) i ≠ 0 := sub_ne_zero.mpr hi
  exact hA (det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hz
    (mem_nonZeroDivisors_iff_ne_zero.mpr hne))

private theorem detAbs_mul_mem_range {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℤ) :
    ((A.det.natAbs : ℤ) • x) ∈ LinearMap.range A.mulVecLin := by
  by_cases h : 0 ≤ A.det
  · rw [Int.natAbs_of_nonneg h]
    exact ⟨A.adjugate *ᵥ x, by rw [mulVecLin_apply, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]⟩
  · have he : (A.det.natAbs : ℤ) = -A.det := by omega
    rw [he, neg_smul]
    apply (LinearMap.range A.mulVecLin).neg_mem
    exact ⟨A.adjugate *ᵥ x, by rw [mulVecLin_apply, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]⟩

/-- Every integer vector has a unique representation by a bounded representative
of the quotient and an integer vector in the coordinates of the matrix image. -/
theorem exists_bounded_lattice_cosets {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) :
    ∃ (R : Finset (Fin n → ℤ)) (e : (↑R × (Fin n → ℤ)) ≃ (Fin n → ℤ)),
      R.card ≤ A.det.natAbs ^ n ∧
      (∀ b : R, ∀ i, 0 ≤ b.val i ∧ b.val i < (A.det.natAbs : ℤ)) ∧
      ∀ (b : R) z, e (b, z) = b.val + A *ᵥ z := by
  classical
  let D : ℤ := A.det.natAbs
  have hD : 0 < D := Int.natCast_pos.mpr (Int.natAbs_pos.mpr hA)
  let S : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ => Finset.Ico 0 D)
  let L := LinearMap.range A.mulVecLin
  let q : (Fin n → ℤ) →ₗ[ℤ] ((Fin n → ℤ) ⧸ L) := L.mkQ
  have hrep : ∀ c, ∃ b ∈ S, q b = c := by
    intro c
    obtain ⟨x, rfl⟩ := L.mkQ_surjective c
    refine ⟨fun i => x i % D, Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hD.ne', Int.emod_lt_of_pos _ hD⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    refine (Submodule.Quotient.eq L).2 ?_
    have he : (fun i => x i % D) - x = -(D • (fun i => x i / D)) := by
      ext i
      change x i % D - x i = -(D * (x i / D))
      linarith [Int.emod_add_mul_ediv (x i) D]
    rw [he]
    exact L.neg_mem (detAbs_mul_mem_range A _)
  choose rep hS hrep_eq using hrep
  let R := S.image (fun x => rep (q x))
  have hRS : R ⊆ S := by
    intro b hb
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb
    exact hS _
  have hfixed {b : Fin n → ℤ} (hb : b ∈ R) : rep (q b) = b := by
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb
    rw [hrep_eq]
  have hmem (c) : rep c ∈ R := by
    refine Finset.mem_image.mpr ⟨rep c, hS c, ?_⟩
    rw [hrep_eq]
  have hqAz (z : Fin n → ℤ) : q (A *ᵥ z) = 0 :=
    (Submodule.Quotient.mk_eq_zero L).mpr ⟨z, rfl⟩
  let f : ↑R × (Fin n → ℤ) → (Fin n → ℤ) := fun bz => bz.1.val + A *ᵥ bz.2
  have hsurj : Function.Surjective f := by
    intro x
    have hdiff : x - rep (q x) ∈ L :=
      (Submodule.Quotient.eq L).mp ((hrep_eq (q x)).symm)
    obtain ⟨z, hz⟩ := hdiff
    refine ⟨(⟨rep (q x), hmem (q x)⟩, z), ?_⟩
    change rep (q x) + A.mulVecLin z = x
    rw [hz, add_sub_cancel]
  have hinj : Function.Injective f := by
    intro ⟨b, z⟩ ⟨c, v⟩ hbc
    have hm : b.val + A *ᵥ z = c.val + A *ᵥ v := hbc
    have hq : q b.val = q c.val := by
      simpa only [map_add, hqAz, add_zero] using congrArg q hm
    have he : b = c := Subtype.ext ((hfixed b.prop).symm.trans ((congrArg rep hq).trans (hfixed c.prop)))
    subst c
    exact Prod.ext rfl (mulVec_int_injective A hA (add_left_cancel hm))
  refine ⟨R, Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_, fun _ _ => rfl⟩
  · have hcard : S.card = A.det.natAbs ^ n := by
      simp only [S, Fintype.card_piFinset, Int.card_Ico, sub_zero, D, Int.toNat_natCast,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (Finset.card_le_card hRS).trans_eq hcard
  · intro b i
    exact Finset.mem_Ico.mp (Fintype.mem_piFinset.mp (hRS b.prop) i)

end Birch
