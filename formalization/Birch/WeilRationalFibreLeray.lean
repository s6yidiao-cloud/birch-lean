module

public import Birch.WeilRationalPointRanks
public import WeilConjectures.WeilSheaf.FiniteLeray

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Birch

set_option maxHeartbeats 400000
set_option profiler true

theorem finrank_cohomology_eq_higherImageGlobalSections
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (q : X ⟶ Spec (.of k)) [q.IsOver (Spec (.of k))]
    [QuasiCompact q] [QuasiSeparated q] [LocallyOfFiniteType q]
    (H : WeilSheaf k l X) (i : ℕ) :
    Module.finrank (PadicAlgCl l) (H.cohomology i).carrier =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.higherLowerStar q i).obj H).globalSections.carrier := by
  obtain ⟨e⟩ := WeilSheaf.nonempty_equiv_cohomology_globalSections_higherLowerStar q H i
  exact e.toLinearEquiv.finrank_eq

end Birch
