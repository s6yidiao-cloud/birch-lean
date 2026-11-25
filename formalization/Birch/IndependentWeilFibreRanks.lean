module

public import Birch.WeilRationalFibreBaseChange
public import WeilConjectures.ZetaFunction.RelativePurity
public import WeilConjectures.WeilSheaf.UpperStarConstant
public import WeilConjectures.WeilSheaf.ArtinSchreierPurity

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Birch

set_option maxHeartbeats 1200000
set_option profiler true

private abbrev rationalSpecClosedPoint (k : Type u) [Field k] [Finite k] :
    (Spec (CommRingCat.of k)).finitePoints :=
  ⟨IsLocalRing.closedPoint k, closedPoint_mem_finitePoints⟩

private theorem finrank_sections_upperStar_eq_rational_stalk
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    (s : Spec (CommRingCat.of k) ⟶ Y) [s.IsOver (Spec (CommRingCat.of k))]
    (G : WeilSheaf k l Y) (x : (Spec (CommRingCat.of k)).finitePoints) :
    Module.finrank (PadicAlgCl l) ((WeilSheaf.upperStar s).obj G).globalSections.carrier =
      Module.finrank (PadicAlgCl l)
        (G.stalk ⟨s.base x.1, Scheme.Hom.map_mem_finitePoints s x.2⟩).carrier :=
  (finrank_globalSections_eq_spec_stalk ((WeilSheaf.upperStar s).obj G) x).trans
    (WeilSheaf.finrank_stalk_upperStar s G x)

private theorem finrank_cohomology_eq_relative_stalk {k : Type u} [Field k] [Finite k]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)] {X Y X' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [X'.Over (Spec (CommRingCat.of k))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    [IsProper f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsProper (X' ↘ Spec (CommRingCat.of k))]
    (s : Spec (CommRingCat.of k) ⟶ Y) [s.IsOver (Spec (CommRingCat.of k))]
    (j : X' ⟶ X) [j.IsOver (Spec (CommRingCat.of k))]
    (h : IsPullback j (X' ↘ Spec (CommRingCat.of k)) f s) (i : ℕ) :
    Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k l X').cohomology i).carrier =
      Module.finrank (PadicAlgCl l)
        (((WeilSheaf.higherLowerStar f i).obj (WeilSheaf.adicConstant k l X)).stalk
          ⟨s.base (rationalSpecClosedPoint k).1,
            Scheme.Hom.map_mem_finitePoints s (rationalSpecClosedPoint k).2⟩).carrier := by
  have : (X' ↘ Spec (CommRingCat.of k)).IsOver (Spec (CommRingCat.of k)) := ⟨by simp⟩
  exact (finrank_cohomology_eq_rationalFiberGlobalSections_of_map (l := l)
    f (X' ↘ Spec (CommRingCat.of k)) s j h i).trans
    (finrank_sections_upperStar_eq_rational_stalk s _ (rationalSpecClosedPoint k))

/-- The ordinary rational cohomology ranks of two rational fibers of a smooth
proper family over an irreducible geometric base agree degree by degree. -/
theorem finrank_constantCohomology_eq_of_smoothProperRationalFibers
    {k : Type u} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {X Y X₀ X₁ : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] [X₀.Over (Spec (CommRingCat.of k))]
    [X₁.Over (Spec (CommRingCat.of k))]
    [IrreducibleSpace (Y ↘ Spec (CommRingCat.of k)).geometricFiber]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] [IsProper f] [Smooth f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsProper (X₀ ↘ Spec (CommRingCat.of k))] [IsProper (X₁ ↘ Spec (CommRingCat.of k))]
    (s₀ s₁ : Spec (CommRingCat.of k) ⟶ Y)
    [s₀.IsOver (Spec (CommRingCat.of k))] [s₁.IsOver (Spec (CommRingCat.of k))]
    (j₀ : X₀ ⟶ X) (j₁ : X₁ ⟶ X) [j₀.IsOver (Spec (CommRingCat.of k))]
    [j₁.IsOver (Spec (CommRingCat.of k))]
    (h₀ : IsPullback j₀ (X₀ ↘ Spec (CommRingCat.of k)) f s₀)
    (h₁ : IsPullback j₁ (X₁ ↘ Spec (CommRingCat.of k)) f s₁) (i : ℕ) :
    Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k l X₀).cohomology i).carrier =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k l X₁).cohomology i).carrier :=
  (finrank_cohomology_eq_relative_stalk (l := l) f s₀ j₀ h₀ i).trans
    ((finrank_stalk_eq_of_lisse
      ((WeilSheaf.higherLowerStar f i).obj (WeilSheaf.adicConstant k l X))
      (WeilSheaf.isLisse_higherLowerStar_of_smooth_of_isProper f
        (WeilSheaf.isLisse_adicConstant k l X) i)
      ⟨s₀.base (rationalSpecClosedPoint k).1,
        Scheme.Hom.map_mem_finitePoints s₀ (rationalSpecClosedPoint k).2⟩
      ⟨s₁.base (rationalSpecClosedPoint k).1,
        Scheme.Hom.map_mem_finitePoints s₁ (rationalSpecClosedPoint k).2⟩).trans
      (finrank_cohomology_eq_relative_stalk (l := l) f s₁ j₁ h₁ i).symm)

end Birch
