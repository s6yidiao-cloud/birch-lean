/-
The finite, profinite and constant-coefficient arguments below adapt
WeilConjectures at ae6479530ccaaa19b6d7ca02bc3248cbf49611c9, Apache 2.0,
by replacing the general 2d range with Artin's affine d range.
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.AffineCohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension
public import WeilConjectures.WeilSheaf.CohomologyAdicConstant
public import WeilConjectures.WeilSheaf.CohomologyProEtale
public import WeilConjectures.WeilSheaf.TraceIsomorphism

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

open Scheme

theorem subsingleton_H_continuousSheaf_of_affine
    {K : Type u} [Field K] [IsSepClosed K] {S : Scheme.{u}} [IsAffine S] (a : S ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞))
    (A : Type) [TopologicalSpace A] [DiscreteTopology A] [AddCommGroup A] [Finite A]
    (q : ℕ) (hq : d < q) :
    Subsingleton (Sheaf.H (ProEtale.continuousSheaf S A) q) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let M := AddCommGrpCat.of (ULift.{u + 1} A)
  let Cet := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  let Cproet := (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj M
  -- the constant étale sheaf `A` is torsion, so its cohomology vanishes above `d`
  have hC : Subsingleton (Sheaf.H Cet (q + 1)) := by
    have := Scheme.subsingleton_H_of_lt_of_isAffine_of_isSepClosed d a hS
      (Etale.continuousMapSheaf S (ULift.{u + 1} A))
      (Sheaf.IsTorsion.of_forall_isAddTorsion fun U f ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2
        ⟨Nat.card (ULift.{u + 1} A), Nat.card_pos, ContinuousMap.ext fun x ↦ ?_⟩) (q + 1) hq
    · exact ((Sheaf.functorH S.smallEtaleTopology (q + 1)).mapIso
        (Etale.constantSheafIsoContinuousMapSheaf S (ULift.{u + 1} A))).addCommGroupIsoToAddEquiv
        |>.toEquiv.subsingleton_congr.2 this
    · exact card_nsmul_eq_zero'
  obtain ⟨e₁⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    (ProEt.topology S) _ (ProEt.isTerminalMkId S) Cproet q
  obtain ⟨e₂⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    S.smallEtaleTopology _ (Etale.isTerminalMkId S) Cet q
  let e₃ : ((globalSectionsFunctor AddCommGrpCat.{u + 1} S).rightDerived (q + 1)).obj Cproet ≅
      ((Etale.sectionsFunctor AddCommGrpCat.{u + 1} S).rightDerived (q + 1)).obj Cet :=
    (((globalSectionsFunctor _ S).rightDerived (q + 1)).mapIso
      ((comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app M)).symm ≪≫
      rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso _ S Cet (q + 1)
  let e₄ := (Sheaf.functorH (ProEt.topology S) (q + 1)).mapIso
    (constantSheafIsoContinuousSheaf S A)
  exact (e₄.addCommGroupIsoToAddEquiv.symm.trans (e₁.trans
    (e₃.addCommGroupIsoToAddEquiv.trans e₂.symm))).toEquiv.subsingleton

section

variable {A : Type} [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A] [CompactSpace A]

theorem subsingleton_H_continuousSheaf_of_profinite_of_affine {K : Type u} [Field K] [IsSepClosed K]
    {S : Scheme.{u}} [IsAffine S] (a : S ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (U : ℕ → OpenAddSubgroup A)
    (hU : ∀ m, U (m + 1) ≤ U m) (hU₀ : ∀ x, (∀ m, x ∈ U m) → x = 0) (q : ℕ) (hq : d < q) :
    Subsingleton (Sheaf.H (continuousSheaf S A) q) := by
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := S)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (m : ℕ) : Epi ((continuousSheafTower S U hU).map (homOfLE m.le_succ).op) := by
    rw [continuousSheafTower_map_succ]
    exact (shortExact_continuousSheafShortComplex S U hU m).epi_g
  refine Abelian.Ext.subsingleton_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht)
    (isLimitContinuousSheafCone S U hU hU₀) (d)
    (fun n q hq ↦ subsingleton_H_continuousSheaf_of_affine a d hS _ q hq) (fun n ↦ ?_) q hq
  have h := Abelian.Ext.surjective_comp_mk₀_of_shortExact
    (shortExact_continuousSheafShortComplex S U hU n) _ (d)
    (subsingleton_H_continuousSheaf_of_affine a d hS _ (d + 1) (by lia))
  rw [continuousSheafTower_map_succ]
  exact h

end

section

variable {l : ℕ} [Fact l.Prime] {S : Scheme.{u}}

theorem subsingleton_H_adicConstantSheafAb_of_affine {K : Type u} [Field K] [IsSepClosed K] [IsAffine S]
    (a : S ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (q : ℕ) (hq : d < q) :
    Subsingleton (Sheaf.H (adicConstantSheafAb l S) q) := by
  have := LocallyOfFiniteType.isLocallyNoetherian a
  have := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian S := {}
  exact Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered S
    (isColimitAdicConstantSheafCocone l S) q fun Λ ↦
      subsingleton_H_continuousSheaf_of_profinite_of_affine a d hS Λ.down.ballSubgroup
        Λ.down.ballSubgroup_succ_le Λ.down.eq_zero_of_forall_mem_ballSubgroup q hq

theorem isZero_rightDerived_Γ_adicConstantSheaf_of_affine {K : Type u} [Field K]
    [IsSepClosed K] [IsAffine S] (a : S ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (q : ℕ) (hq : d < q) :
    IsZero (((Sheaf.Γ (Scheme.ProEt.topology S) (WeilCoefficients.{u} l)).rightDerived q).obj
      (adicConstantSheaf l S)) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by lia⟩
  have hH := subsingleton_H_adicConstantSheafAb_of_affine (l := l) a d hS (q + 1) hq
  obtain ⟨e₁⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    (Scheme.ProEt.topology S) _ (Scheme.ProEt.isTerminalMkId S) (adicConstantSheafAb l S) q
  let e₂ := forgetRightDerivedGlobalSectionsIso (ULift.{u + 1} (PadicAlgCl l)) S
    (adicConstantSheaf l S) (q + 1)
  have : Subsingleton ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)))
      AddCommGrpCat.{u + 1}).obj (((globalSectionsFunctor (ModuleCat.{u + 1}
        (ULift.{u + 1} (PadicAlgCl l))) S).rightDerived (q + 1)).obj (adicConstantSheaf l S))) :=
    (e₂.addCommGroupIsoToAddEquiv.trans e₁.symm).toEquiv.subsingleton
  have : ((sheafSections (Scheme.ProEt.topology S) (WeilCoefficients.{u} l)).obj
      (op (Scheme.ProEt.mk (𝟙 S)))).Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  refine IsZero.of_iso (ModuleCat.isZero_of_subsingleton (((globalSectionsFunctor (ModuleCat.{u + 1}
    (ULift.{u + 1} (PadicAlgCl l))) S).rightDerived (q + 1)).obj (adicConstantSheaf l S)))
    (Functor.rightDerivedObjIsoOfIso (Sheaf.ΓNatIsoSheafSections _ _
      (Scheme.ProEt.isTerminalMkId S)) (q + 1) _)

end

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

variable {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [QuasiSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [IsAffine (X ↘ Spec (.of k)).geometricFiber]

/-- Artin vanishing for the ordinary cohomology of the constant Weil sheaf. -/
theorem subsingleton_cohomology_adicConstant_of_affine_of_lt (d : ℕ)
    (hdim : topologicalKrullDim (X ↘ Spec (.of k)).geometricFiber ≤ (d : WithBot ℕ∞))
    {i : ℤ} (hi : (d : ℤ) < i) :
    Subsingleton ((adicConstant k l X).cohomology i).carrier := by
  obtain ⟨r, rfl⟩ : ∃ n : ℕ, i = n := ⟨i.toNat, by omega⟩
  exact subsingleton_cohomology_of_isZero_rightDerived _ r
    (ProEtale.isZero_rightDerived_Γ_adicConstantSheaf_of_affine
      (X ↘ Spec (.of k)).geometricFiberToAlgebraicClosure d hdim r (by exact_mod_cast hi))

/-- Dual Artin vanishing below dimension for compactly supported cohomology
of a smooth affine scheme. -/
theorem subsingleton_compactlySupportedCohomology_adicConstant_of_affine_of_lt (d : ℕ)
    [IsSeparated (X ↘ Spec (.of k))] [SmoothOfRelativeDimension d (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] {i : ℤ} (hi : i < d) :
    Subsingleton ((adicConstant k l X).compactlySupportedCohomology i).carrier := by
  have hdim := topologicalKrullDim_geometricFiber_le_of_smoothOfRelativeDimension
    (X ↘ Spec (.of k)) d
  obtain ⟨P, hP, _⟩ := (poincareDuality_compactlySupportedCohomology_adicConstant k l X d).2.1
    i (2 * (d : ℤ) - i) (by omega)
  let : Subsingleton ((adicConstant k l X).cohomology (2 * (d : ℤ) - i)).carrier :=
    subsingleton_cohomology_adicConstant_of_affine_of_lt d hdim (by omega)
  refine ⟨fun x y ↦ hP.bijective_left.injective ?_⟩
  ext z
  rw [Subsingleton.elim z 0, map_zero, map_zero]

end AlgebraicGeometry.WeilSheaf
