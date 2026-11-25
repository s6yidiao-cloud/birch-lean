module

public import Birch.IndependentWeilWeakLefschetz
public import Birch.IndependentWeilProjectiveCohomology
public import Birch.ProjectiveHypersurfaceComplementGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Ordinary cohomology of projective space in polynomial coordinates. -/
noncomputable def projectivePolynomialSpaceConstantCohomology
    {k : Type} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
    (N i : ℕ) : FrobeniusModule.{1, 0} (PadicAlgCl l) := by
  let X := Proj (homogeneousSubmodule (Fin (N+1)) k)
  let S := Spec (.of k)
  let : X.Over S := ⟨projectivePolynomialSpaceToField (Fin (N+1)) k⟩
  let : IsProper (X ↘ S) := isProper_projectivePolynomialSpaceToField
  exact (WeilSheaf.adicConstant k l X).cohomology i

/-- The low-degree cohomology of a nonzero hypersurface is identified
Frobenius-equivariantly with the ambient cohomology. -/
theorem nonempty_equiv_projectiveHypersurfaceConstantCohomology_of_lt
    {k : Type} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {N d : ℕ} {G : MvPolynomial (Fin (N+2)) k} (hG : G.IsHomogeneous d)
    (hd : 0 < d) (hG₀ : G ≠ 0) {i : ℕ} (hi : i < N) :
    Nonempty ((projectivePolynomialSpaceConstantCohomology (k := k) l (N+1) i).Equiv
      (projectiveHypersurfaceConstantCohomology l hG hd i)) := by
  let S := Spec (.of k)
  let P := Proj (homogeneousSubmodule (Fin (N+2)) k)
  let Z := projectiveHypersurface hG
  let V := Proj.basicOpen (homogeneousSubmodule (Fin (N+2)) k) G
  let U := V.toScheme
  let j : U ⟶ P := V.ι
  let z : Z ⟶ P := projectiveHypersurfaceι hG
  let a : P ⟶ S := projectivePolynomialSpaceToField (Fin (N+2)) k
  let : P.Over S := ⟨a⟩
  let : Z.Over S := ⟨projectiveHypersurfaceToField hG⟩
  let : U.Over S := ⟨j ≫ a⟩
  let : j.IsOver S := ⟨rfl⟩
  let : z.IsOver S := ⟨projectiveHypersurfaceι_toField hG⟩
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion V.ι)
  let : IsClosedImmersion z := inferInstanceAs (IsClosedImmersion (projectiveHypersurfaceι hG))
  let : IsProper (P ↘ S) := isProper_projectivePolynomialSpaceToField
  let : IsProper (Z ↘ S) := isProper_projectiveHypersurfaceToField hG hd
  obtain ⟨hu, hgi⟩ := affine_geometricallyIntegral_projectiveHypersurfaceComplement hG hd hG₀
  let : IsAffine U := hu
  let : IsAffineHom (j ≫ a) := isAffineHom_of_isAffine (j ≫ a)
  let : GeometricallyIntegral (U ↘ S) := hgi
  let : GeometricallyConnected (U ↘ S) := inferInstance
  let : IsAffine (U ↘ S).geometricFiber := by
    change IsAffine (Limits.pullback (j ≫ a)
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))
    infer_instance
  let : SmoothOfRelativeDimension (N+1) (U ↘ S) := by
    change SmoothOfRelativeDimension (N+1) (V.ι ≫ projectivePolynomialSpaceToField (Fin (N+2)) k)
    simpa only [Fintype.card_fin, show N + 2 - 1 = N + 1 by omega] using
      smoothOfRelativeDimension_projectiveHypersurfaceComplement G
  let : IsSeparated (U ↘ S) := inferInstanceAs (IsSeparated (j ≫ a))
  let : QuasiCompact (U ↘ S) := HasAffineProperty.iff_of_isAffine.mpr (by infer_instance)
  let : Smooth (U ↘ S) := SmoothOfRelativeDimension.smooth (N+1) (U ↘ S)
  let : LocallyOfFiniteType (U ↘ S) := inferInstance
  have hrange : Set.range z.base = (Set.range j.base)ᶜ := by
    change Set.range (projectiveHypersurfaceι hG) = (Set.range V.ι)ᶜ
    rw [V.range_ι]
    exact range_projectiveHypersurfaceι hG
  exact WeilSheaf.nonempty_equiv_cohomology_adicConstant_of_smoothAffineComplement
    l (N+1) j z hrange i (by exact_mod_cast Nat.add_lt_add_right hi 1)

end Birch
