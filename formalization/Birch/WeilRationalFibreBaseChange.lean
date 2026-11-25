module

public import Birch.WeilRationalFibreLeray
public import Birch.WeilRationalFibreConstant
public import Birch.WeilRationalFibrePullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Birch

set_option maxHeartbeats 400000
set_option profiler true

theorem finrank_cohomology_eq_rationalFiberGlobalSections_of_map {k : Type u} [Field k] [Finite k]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)] {X Y X' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [X'.Over (Spec (CommRingCat.of k))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))]
    [IsProper f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    [IsProper (X' ↘ Spec (CommRingCat.of k))]
    (q : X' ⟶ Spec (CommRingCat.of k)) [q.IsOver (Spec (CommRingCat.of k))]
    [QuasiCompact q] [QuasiSeparated q] [LocallyOfFiniteType q]
    (s : Spec (CommRingCat.of k) ⟶ Y) [s.IsOver (Spec (CommRingCat.of k))]
    (j : X' ⟶ X) [j.IsOver (Spec (CommRingCat.of k))]
    (h : IsPullback j q f s) (i : ℕ) :
    Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k l X').cohomology i).carrier =
      Module.finrank (PadicAlgCl l) (((WeilSheaf.upperStar s).obj
        ((WeilSheaf.higherLowerStar f i).obj (WeilSheaf.adicConstant k l X))).globalSections).carrier :=
  (finrank_cohomology_eq_higherImageGlobalSections q (WeilSheaf.adicConstant k l X') i).trans
    ((finrank_higherImageGlobalSections_eq_of_constantPullback (l := l) q j i).symm.trans
      (finrank_higherImageGlobalSections_eq_of_rationalBaseChange f q s j h
        (WeilSheaf.adicConstant k l X) i).symm)

end Birch
