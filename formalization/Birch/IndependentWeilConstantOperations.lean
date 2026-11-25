module

public import WeilConjectures.WeilSheaf.CohomologySequence
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek
public import WeilConjectures.WeilSheaf.UpperStarConstant

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.WeilSheaf

variable {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]

/-- Pullback preserves the constant Weil complex, compatibly with its Weil structure. -/
noncomputable def upperStarAdicConstantComplexIso (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    (WeilComplex.upperStar f).obj (toComplex.obj (adicConstant k l Y)) ≅
      toComplex.obj (adicConstant k l X) :=
  (toComplexCompUpperStarIso f).app (adicConstant k l Y) ≪≫
    toComplex.mapIso (upperStarAdicConstantIso f)

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilComplex

variable {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- On a proper scheme, compactly supported and ordinary cohomology agree
Frobenius-equivariantly. -/
noncomputable def compactlySupportedCohomologyEquivCohomologyOfProper (K : WeilComplex k l X)
    (r : ℤ) : (K.compactlySupportedCohomology r).Equiv (K.cohomology r) :=
  cohomologyEquivOfIso (derivedLowerShriekObjIsoOfIsProper K) r

end AlgebraicGeometry.WeilComplex
