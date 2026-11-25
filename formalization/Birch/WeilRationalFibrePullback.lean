module

public import Birch.WeilRationalPointRanks
public import WeilConjectures.WeilSheaf.ProperBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Birch

set_option maxHeartbeats 400000
set_option profiler true

theorem finrank_higherImageGlobalSections_eq_of_rationalBaseChange
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {X Y Z : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (q : Z ⟶ Spec (.of k)) [q.IsOver (Spec (.of k))]
    [QuasiCompact q] [QuasiSeparated q] [LocallyOfFiniteType q]
    (s : Spec (.of k) ⟶ Y) [s.IsOver (Spec (.of k))]
    (j : Z ⟶ X) [j.IsOver (Spec (.of k))]
    (h : IsPullback j q f s) (H : WeilSheaf k l X) (i : ℕ) :
    Module.finrank (PadicAlgCl l) (((WeilSheaf.upperStar s).obj
      ((WeilSheaf.higherLowerStar f i).obj H)).globalSections).carrier =
      Module.finrank (PadicAlgCl l) (((WeilSheaf.higherLowerStar q i).obj
        ((WeilSheaf.upperStar j).obj H)).globalSections).carrier := by
  obtain ⟨e⟩ := WeilSheaf.nonempty_upperStar_higherLowerStar_iso_of_isProper
    (f := f) (f' := q) (g := s) (g' := j) (inferInstance : IsProper f) h H i
  exact finrank_globalSections_eq_of_iso e

end Birch
