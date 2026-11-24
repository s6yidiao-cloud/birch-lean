import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Completing a section with coordinate vectors -/

open Matrix

namespace Birch

noncomputable section

private theorem exists_coordinate_extension {K : Type*} [Field K] {l s : ℕ}
    (v : Fin l → Fin (l+s) → K) (hv : LinearIndependent K v) :
    ∃ j : Fin s → Fin (l+s),
      LinearIndependent K (Fin.append v fun i => Pi.single (j i) 1) := by
  classical
  let b := Pi.basisFun K (Fin (l+s))
  let S := Set.range v
  let T := S ∪ Set.range b
  have hST : S ⊆ T := Set.subset_union_left
  have hspan : ⊤ ≤ Submodule.span K T :=
    b.span_eq.ge.trans (Submodule.span_mono Set.subset_union_right)
  let E := Module.Basis.extendLe hv.linearIndepOn_id hST hspan
  let V := hv.linearIndepOn_id.extend hST
  let J := V \ S
  have hSV : S ⊆ V := hv.linearIndepOn_id.subset_extend hST
  let e : Fin l ⊕ J ≃ V :=
    (Equiv.sumCongr (Equiv.ofInjective v hv.injective) (Equiv.refl J)).trans
      (Equiv.Set.sumDiffSubset hSV)
  have hVT : V ⊆ T := hv.linearIndepOn_id.extend_subset hST
  have hJ (x : J) : x.val ∈ Set.range b := (hVT x.prop.1).resolve_left x.prop.2
  letI : Finite V := by
    have hT : T.Finite := (Set.finite_range v).union (Set.finite_range b)
    exact (hT.subset hVT).to_subtype
  letI : Finite J := Finite.of_injective (Set.inclusion (Set.sdiff_subset : J ⊆ V))
    (Set.inclusion_injective _)
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype J := Fintype.ofFinite J
  have hcardV : Fintype.card V = l+s := by
    rw [← Module.finrank_eq_card_basis E, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hcardJ : Fintype.card J = s := by
    have h := Fintype.card_congr e
    rw [Fintype.card_sum, Fintype.card_fin, hcardV] at h
    omega
  let eJ := (Fintype.equivFinOfCardEq hcardJ).symm
  choose j hj using hJ
  refine ⟨j ∘ eJ, ?_⟩
  let e' := ((finSumFinEquiv (m := l) (n := s)).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin l)) eJ)).trans e
  have hfun : Fin.append v (fun i => Pi.single (j (eJ i)) 1) = E ∘ e' := by
    funext a
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · simp [e', e, E]
      rfl
    · simp [e', e, E]
      change Pi.single (j (eJ a)) 1 = (eJ a).val
      simpa [b] using hj (eJ a)
  change LinearIndependent K (Fin.append v fun i => Pi.single (j (eJ i)) 1)
  rw [hfun]
  exact E.linearIndependent.comp e' e'.injective

/-- The first `l` columns of the frame are the given section. The other
columns are integral coordinate vectors, chosen so the determinant is nonzero
in the residue field. -/
theorem exists_integral_section_frame {l s p : ℕ} [Fact p.Prime]
    (U : Matrix (Fin (l+s)) (Fin l) ℤ)
    (hU : LinearIndependent (ZMod p) (U.map (Int.castRingHom (ZMod p))).col) :
    ∃ j : Fin s → Fin (l+s), ∃ A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ,
      (∀ a, A.col (Fin.castAdd s a) = U.col a) ∧
      (∀ a, A.col (Fin.natAdd l a) = Pi.single (j a) 1) ∧ (A.det : ZMod p) ≠ 0 := by
  classical
  obtain ⟨j,h⟩ := exists_coordinate_extension _ hU
  let A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ :=
    Matrix.of fun i a => Fin.append U.col (fun a => Pi.single (j a) 1) a i
  refine ⟨j, A, ?_, ?_, ?_⟩
  · intro a
    ext i
    exact congrFun (Fin.append_left U.col (fun a => Pi.single (j a) 1) a) i
  · intro a
    ext i
    exact congrFun (Fin.append_right U.col (fun a => Pi.single (j a) 1) a) i
  · rw [← isUnit_iff_ne_zero]
    change IsUnit (Int.castRingHom (ZMod p) A.det)
    rw [RingHom.map_det, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    convert h using 1
    ext a i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · simp [A, Matrix.col, Fin.append_left]
    · by_cases hi : i = j a <;> simp [A, Matrix.col, Fin.append_right, hi]

/-- All integer frames with coordinates in the fixed box `[-B,B]`. -/
def boundedSectionFrames (n B : ℕ) : Finset (Matrix (Fin n) (Fin n) ℤ) :=
  Fintype.piFinset fun _ : Fin n => Fintype.piFinset fun _ : Fin n => Finset.Icc (-(B : ℤ)) B

theorem mem_boundedSectionFrames {n B : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} :
    A ∈ boundedSectionFrames n B ↔ ∀ i j, |A i j| ≤ (B : ℤ) := by
  let a : Fin n → Fin n → ℤ := A
  change a ∈ (Fintype.piFinset fun _ : Fin n =>
    Fintype.piFinset fun _ : Fin n => Finset.Icc (-(B : ℤ)) B) ↔ ∀ i j, |a i j| ≤ (B : ℤ)
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- Coordinate extension preserves a positive entry bound on the section. -/
theorem exists_bounded_integral_section_frame {l s p B : ℕ} [Fact p.Prime] (hB : 1 ≤ B)
    (U : Matrix (Fin (l+s)) (Fin l) ℤ) (hBU : ∀ i j, |U i j| ≤ (B : ℤ))
    (hU : LinearIndependent (ZMod p) (U.map (Int.castRingHom (ZMod p))).col) :
    ∃ A ∈ boundedSectionFrames (l+s) B,
      (∀ a, A.col (Fin.castAdd s a) = U.col a) ∧ (A.det : ZMod p) ≠ 0 := by
  obtain ⟨j,A,hleft,hright,hdet⟩ := exists_integral_section_frame U hU
  refine ⟨A, mem_boundedSectionFrames.mpr fun i a => ?_, hleft, hdet⟩
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a
  · change |A.col (Fin.castAdd s a) i| ≤ _
    rw [hleft a]
    exact hBU i a
  · change |A.col (Fin.natAdd l a) i| ≤ _
    rw [hright a]
    have hB' : (1 : ℤ) ≤ B := by exact_mod_cast hB
    by_cases hi : i = j a <;> simp [hi, hB']

end
end Birch
