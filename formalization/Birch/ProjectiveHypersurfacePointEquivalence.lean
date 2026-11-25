module

public import Birch.MvPolynomialCoefficientCompat

public import Birch.ProjectiveHypersurfaceBoundary
public import Birch.ProjectiveCoordinatePoints

@[expose] public section

/-! # Scheme and coordinate points of projective hypersurfaces -/

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Graded

namespace Birch

noncomputable section

universe u

variable {σ K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Dehomogenizing a degree-d homogeneous form gives a polynomial of total degree at most d. -/
theorem totalDegree_dehomogenize_le_homogeneous {F : MvPolynomial (Option σ) K}
    {d : ℕ} (hF : F.IsHomogeneous d) : (dehomogenize F).totalDegree ≤ d := by
  rw [F.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [dehomogenize_monomial]
  have hdeg := (hF.degree_eq_sum_deg_support hm).symm
  change m.degree = d at hdeg
  have hsome : m.degree = m none + m.some.degree := by
    simp only [Finsupp.degree_apply]
    exact Finsupp.sum_option_index m (fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)
  have hmon := totalDegree_monomial_le m.some (coeff m F)
  change (monomial m.some (coeff m F)).totalDegree ≤ m.some.degree at hmon
  exact hmon.trans (by omega)

/-- Homogenization in the original degree recovers the form from its affine chart. -/
theorem deligneLevelClosure_dehomogenize {F : MvPolynomial (Option σ) K}
    {d : ℕ} (hF : F.IsHomogeneous d) :
    deligneLevelClosure d (dehomogenize F) 0 = F := by
  apply sub_eq_zero.mp
  apply eq_zero_of_dehomogenize_eq_zero
    ((isHomogeneous_deligneLevelClosure d (dehomogenize F) 0).sub hF)
  rw [map_sub, dehomogenize_deligneLevelClosure (totalDegree_dehomogenize_le_homogeneous hF),
    map_zero, sub_zero, sub_self]

def polynomialProjectivePointsEquivSum {F : MvPolynomial (Option σ) K}
    {d : ℕ} (hd : 0 < d) (hF : F.IsHomogeneous d) :
    projectiveHypersurfacePoints F ≃
      {x : σ → K // (dehomogenize F).eval x = 0} ⊕
        projectiveHypersurfacePoints (setExtraCoordinateZero F) := by
  have h := deligneLevelClosure_dehomogenize hF
  have hinfinity : homogeneousComponent d (dehomogenize F) = setExtraCoordinateZero F := by
    rw [← setExtraCoordinateZero_deligneLevelClosure hd (dehomogenize F) 0, h]
  exact (Equiv.cast (congrArg projectiveHypersurfacePoints h.symm)).trans
    ((deligneLevelClosure_points_equiv hd (totalDegree_dehomogenize_le_homogeneous hF) 0).trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.cast (congrArg projectiveHypersurfacePoints hinfinity))))

def schemeProjectivePointsEquivSum {F : MvPolynomial (Option σ) K}
    {d : ℕ} (hF : F.IsHomogeneous d) :
    SchemeFieldValuedPoints (projectiveHypersurfaceToField hF) K ≃
      {x : σ → K // (dehomogenize F).eval x = 0} ⊕
        SchemeFieldValuedPoints
          (projectiveHypersurfaceToField (isHomogeneous_setExtraCoordinateZero hF)) K := by
  let f := projectiveHypersurfaceToField hF
  let i := projectiveHypersurfaceBoundaryι hF
  let j := standardHypersurfaceChartι hF
  have hij : Set.range j = (Set.range i)ᶜ := by
    change Set.range (standardHypersurfaceChartι hF) = (Set.range (projectiveHypersurfaceBoundaryι hF))ᶜ
    rw [range_projectiveHypersurfaceBoundaryι, compl_compl]
  let e := fieldValuedPointsOpenClosedEquiv (L := K) f i j hij
  exact e.symm.trans (Equiv.sumCongr
    ((fieldValuedPointsInOpenEquiv (L := K) f j).trans
      ((projectiveHypersurfaceAffinePointsEquiv hF).trans
        (Equiv.subtypeEquivRight fun x => by rw [Algebra.algebraMap_self]; rfl)))
    (Equiv.subtypeEquivRight fun _ => by
      rw [show i ≫ f = _ from projectiveHypersurfaceBoundaryι_toField hF]))

def schemeFieldValuedPointsEquivOfIso {S T : Scheme.{u}}
    {f : S ⟶ Spec (.of K)} {g : T ⟶ Spec (.of K)} (e : S ≅ T) (he : e.hom ≫ g = f) :
    SchemeFieldValuedPoints f K ≃ SchemeFieldValuedPoints g K where
  toFun x := ⟨x.val ≫ e.hom, by rw [Category.assoc, he]; exact x.prop⟩
  invFun x := ⟨x.val ≫ e.inv, by rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]; exact x.prop⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

theorem isEmpty_proj_no_variables :
    IsEmpty (Proj (homogeneousSubmodule (Fin 0) K)) := by
  constructor
  intro x
  let p : ProjectiveSpectrum (homogeneousSubmodule (Fin 0) K) := x
  apply p.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi f hf
  have h : f = 0 := by
    by_contra hnz
    obtain ⟨m, hm⟩ := exists_coeff_ne_zero hnz
    have hm0 : m = 0 := Finsupp.ext fun j => Fin.elim0 j
    have hdeg := ((show f.IsHomogeneous i from hf).degree_eq_sum_deg_support
      (mem_support_iff.mpr hm)).symm
    change m.degree = i at hdeg
    rw [hm0, map_zero] at hdeg
    omega
  exact h.symm ▸ zero_mem p.asHomogeneousIdeal

/-- For a homogeneous positive-degree equation, rational points of the
projective scheme correspond exactly to the projective coordinate points. -/
def projectiveHypersurfaceSchemePointsEquiv {K : Type} [Field K] {n d : ℕ} (hd : 0 < d)
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d) :
    SchemeFieldValuedPoints (projectiveHypersurfaceToField hF) K ≃ projectiveHypersurfacePoints F := by
  induction n with
  | zero =>
    letI : IsEmpty (Proj (homogeneousSubmodule (Fin 0) K)) := isEmpty_proj_no_variables
    letI : IsEmpty (SchemeFieldValuedPoints (projectiveHypersurfaceToField hF) K) :=
      ⟨fun x => isEmptyElim (projectiveHypersurfaceι hF (x.val default))⟩
    letI : IsEmpty (projectiveHypersurfacePoints F) :=
      ⟨fun x => x.val.rep_nonzero (funext fun j => Fin.elim0 j)⟩
    exact Equiv.equivOfIsEmpty _ _
  | succ n ih =>
    let e : Fin (n + 1) ≃ Option (Fin n) := finSuccEquiv n
    have hF' : (rename e F).IsHomogeneous d := hF.rename_isHomogeneous
    exact ((schemeFieldValuedPointsEquivOfIso (projectiveHypersurfaceRenameIso hF e)
        (projectiveHypersurfaceRenameIso_hom_toField hF e)).symm.trans
      ((schemeProjectivePointsEquivSum hF').trans
        ((Equiv.sumCongr (Equiv.refl _) (ih (isHomogeneous_setExtraCoordinateZero hF'))).trans
          (polynomialProjectivePointsEquivSum hd hF').symm))).trans
      (projectiveHypersurfacePoints_rename_equiv hF e).symm

/-- The scheme count equals the count defined by projective coordinate vectors. -/
theorem natCard_projectiveHypersurfaceSchemePoints {K : Type} [Field K] {n d : ℕ} (hd : 0 < d)
    {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous d) :
    Nat.card (SchemeFieldValuedPoints (projectiveHypersurfaceToField hF) K) =
      Nat.card (projectiveHypersurfacePoints F) :=
  Nat.card_congr (projectiveHypersurfaceSchemePointsEquiv hd hF)

/-- Changing to a finite index set preserves the same point equivalence. -/
def projectiveHypersurfaceSchemePointsEquiv_finite {σ K : Type} [Field K] [Finite σ]
    {d : ℕ} (hd : 0 < d) {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    SchemeFieldValuedPoints (projectiveHypersurfaceToField hF) K ≃ projectiveHypersurfacePoints F := by
  letI : Fintype σ := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  exact ((schemeFieldValuedPointsEquivOfIso (projectiveHypersurfaceRenameIso hF e)
    (projectiveHypersurfaceRenameIso_hom_toField hF e)).symm.trans
      (projectiveHypersurfaceSchemePointsEquiv hd hF.rename_isHomogeneous)).trans
      (projectiveHypersurfacePoints_rename_equiv hF e).symm

/-- A projective hypersurface in finitely many variables over a finite
field has finitely many rational points. -/
theorem finite_projectiveHypersurfaceSchemePoints {σ K : Type} [Field K] [Finite σ] [Finite K]
    {d : ℕ} (hd : 0 < d) {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    Finite (SchemeFieldValuedPoints (projectiveHypersurfaceToField hF) K) := by
  have : Finite (projectiveHypersurfacePoints F) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Finite.of_injective _ (projectiveHypersurfaceSchemePointsEquiv_finite hd hF).injective

end

end Birch
