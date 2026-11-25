module

public import Birch.WeilRationalPointRanks
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.WeilSheaf.UpperStarConstant

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Birch

set_option maxHeartbeats 400000
set_option profiler true

theorem finrank_higherImageGlobalSections_eq_of_constantPullback
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {X Z : Scheme.{u}} [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (q : Z ⟶ Spec (.of k)) [q.IsOver (Spec (.of k))]
    [QuasiCompact q] [QuasiSeparated q] [LocallyOfFiniteType q]
    (j : Z ⟶ X) [j.IsOver (Spec (.of k))] (i : ℕ) :
    let R := WeilSheaf.higherLowerStar (k₀ := k) (l := l) q i
    Module.finrank (PadicAlgCl l) (R.obj ((WeilSheaf.upperStar j).obj
      (WeilSheaf.adicConstant k l X))).globalSections.carrier =
      Module.finrank (PadicAlgCl l) (R.obj (WeilSheaf.adicConstant k l Z)).globalSections.carrier :=
  finrank_globalSections_eq_of_iso ((WeilSheaf.higherLowerStar (k₀ := k) (l := l) q i).mapIso
    (WeilSheaf.upperStarAdicConstantIso j))

end Birch
