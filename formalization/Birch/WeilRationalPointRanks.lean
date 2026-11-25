module

public import WeilConjectures.WeilSheaf.StalkRationalPoint
public import WeilConjectures.WeilSheaf.FinitePointCohomology
public import WeilConjectures.WeilSheaf.CohomologyExact
public import WeilConjectures.SixFunctors.ProEtale.Adic.IrreducibleLisse

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Birch

set_option maxHeartbeats 1200000
set_option profiler true

theorem finrank_weilCoefficients_eq_of_iso {l : ℕ} [Fact l.Prime]
    {A B : WeilCoefficients.{u} l} (e : A ≅ B) :
    Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj A) =
      Module.finrank (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj B) :=
  (WeilCoefficients.linearEquivOfIso e).finrank_eq

theorem finrank_globalSections_eq_of_iso
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    {A B : WeilSheaf k l X} (e : A ≅ B) :
    Module.finrank (PadicAlgCl l) A.globalSections.carrier =
      Module.finrank (PadicAlgCl l) B.globalSections.carrier :=
  finrank_weilCoefficients_eq_of_iso ((WeilSheaf.globalSectionsFunctor k l X).mapIso e)

theorem finrank_globalSections_eq_spec_stalk {k : Type u} [Field k] [Finite k]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    (F : WeilSheaf k l (Spec (CommRingCat.of k)))
    (x : (Spec (CommRingCat.of k)).finitePoints) :
    Module.finrank (PadicAlgCl l) F.globalSections.carrier =
      Module.finrank (PadicAlgCl l) (F.stalk x).carrier := by
  let a := Spec (CommRingCat.of k) ↘ Spec (CommRingCat.of k)
  let s := a.geometricFiberPointOfFinitePoint x
  have : IsIso a.geometricFiberToAlgebraicClosure := by
    change IsIso (WeilSheaf.geometricFiberSpecIso k).inv
    infer_instance
  have : IsIso s := isIso_of_comp_hom_eq_id _
    (a.geometricFiberPointOfFinitePoint_comp_geometricFiberToAlgebraicClosure' x)
  have : IsIso (F.globalSectionsToStalkObj s) :=
    WeilSheaf.isIso_globalSectionsToStalkObj F s
  exact finrank_weilCoefficients_eq_of_iso (asIso (F.globalSectionsToStalkObj s))

theorem finrank_stalk_eq_of_lisse
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    [IrreducibleSpace (Y ↘ Spec (CommRingCat.of k)).geometricFiber]
    (G : WeilSheaf k l Y) (hG : G.IsLisse) (x₀ x₁ : Y.finitePoints) :
    Module.finrank (PadicAlgCl l) (G.stalk x₀).carrier =
      Module.finrank (PadicAlgCl l) (G.stalk x₁).carrier :=
  ProEtale.IsAdicLisseSheaf.finrank_geometricStalkFunctor_eq
    (H := G.obj.carrier) hG
    ((Y ↘ Spec (CommRingCat.of k)).geometricFiberPointOfFinitePoint x₀)
    ((Y ↘ Spec (CommRingCat.of k)).geometricFiberPointOfFinitePoint x₁)


end Birch
