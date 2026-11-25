module

public import Birch.IndependentWeilCohomologyExactness
public import WeilConjectures.WeilSheaf.OpenClosedTriangle

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.WeilComplex

/-- When the compact cohomology of the open term vanishes in two consecutive
degrees, the compact cohomology of the ambient and closed terms is
Frobenius-equivariantly isomorphic in the first degree. -/
theorem nonempty_equiv_compactlySupportedCohomology_of_openClosed_vanishing
    {k : Type u} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {U X Z : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of k))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) (K : WeilComplex k l X) (r : ℤ)
    (h₀ : Subsingleton (((upperStar j).obj K).compactlySupportedCohomology r).carrier)
    (h₁ : Subsingleton (((upperStar j).obj K).compactlySupportedCohomology (r+1)).carrier) :
    Nonempty ((K.compactlySupportedCohomology r).Equiv (((upperStar i).obj K).compactlySupportedCohomology r)) := by
  obtain ⟨α, β, γ, hT⟩ := exists_distTriang_derivedLowerShriek_structure_openClosed j i hij K
  exact ⟨WeilSheaf.cohomologyEquivOfVanishingFirstTerm (Triangle.mk α β γ) r hT h₀ h₁⟩

end AlgebraicGeometry.WeilComplex
