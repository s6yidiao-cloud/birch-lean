module

public import Birch.IndependentWeilAffineVanishing
public import Birch.IndependentWeilOpenClosedComparison
public import Birch.IndependentWeilConstantOperations
public import WeilConjectures.WeilSheaf.CohomologyShift

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.WeilSheaf

set_option maxHeartbeats 2000000 in
/-- A smooth geometrically connected affine complement of dimension `d`
gives a Frobenius-equivariant comparison for the proper pair in degrees `< d-1`. -/
theorem nonempty_equiv_cohomology_adicConstant_of_smoothAffineComplement
    {k : Type u} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {U X Z : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Z ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [IsAffine (U ↘ Spec (.of k)).geometricFiber] [GeometricallyConnected (U ↘ Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d (U ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (r : ℤ) (hr : r + 1 < d) :
    Nonempty (((adicConstant k l X).cohomology r).Equiv ((adicConstant k l Z).cohomology r)) := by
  let F := adicConstant k l X
  let K := toComplex.obj F
  let U' := (WeilComplex.upperStar j).obj K
  have vanish (s : ℤ) (hs : s < d) : Subsingleton (U'.compactlySupportedCohomology s).carrier :=
    (WeilComplex.compactlySupportedCohomologyEquivOfIso
      (upperStarAdicConstantComplexIso (k := k) (l := l) j) s).toLinearEquiv.toEquiv.subsingleton_congr.2
      (subsingleton_compactlySupportedCohomology_adicConstant_of_affine_of_lt d hs)
  obtain ⟨e⟩ := WeilComplex.nonempty_equiv_compactlySupportedCohomology_of_openClosed_vanishing
    l j i hij K r (vanish r (by omega)) (vanish (r+1) hr)
  let toOrdinaryX := WeilComplex.compactlySupportedCohomologyEquivCohomologyOfProper K r
  let toOrdinaryZ := WeilComplex.compactlySupportedCohomologyEquivCohomologyOfProper
    (toComplex.obj (adicConstant k l Z)) r
  let closedCohomology := WeilComplex.compactlySupportedCohomologyEquivOfIso
    (upperStarAdicConstantComplexIso (k := k) (l := l) i) r
  exact ⟨toOrdinaryX.symm.trans (e.trans (closedCohomology.trans toOrdinaryZ))⟩

end AlgebraicGeometry.WeilSheaf
