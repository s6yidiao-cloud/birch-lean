module

public import Birch.ProjectiveHypersurface
public import Birch.AffineHypersurfacePoints
public import Birch.DeligneLevelClosure

@[expose] public section

/-! # Field-valued points on the affine chart of a projective level scheme -/

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

noncomputable section

universe u

/-- Setting the homogenizing coordinate to one in the projective level
equation gives the original affine equation as a polynomial. -/
theorem dehomogenize_deligneLevelClosure {σ K : Type u} [CommRing K]
    {r : ℕ} {g : MvPolynomial σ K} (hg : g.totalDegree ≤ r) (t : K) :
    dehomogenize (deligneLevelClosure r g t) = g - C t := by
  have he := eval₂_deligneLevelClosure_one hg t (C : K →+* MvPolynomial σ K) X
  have hid : (eval₂Hom (C : K →+* MvPolynomial σ K) X) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a; exact eval₂Hom_C _ _ _
    · intro i; exact eval₂Hom_X' _ _ _
  change dehomogenize (deligneLevelClosure r g t) =
    (eval₂Hom (C : K →+* MvPolynomial σ K) X) g - C t at he
  rwa [hid, RingHom.id_apply] at he

/-- The field-valued points in the distinguished projective chart are
precisely the affine solutions of its dehomogenized equation. -/
def projectiveHypersurfaceAffinePointsEquiv {σ K L : Type u} [Field K] [Field L] [Algebra K L]
    {r : ℕ} {F : MvPolynomial (Option σ) K} (hF : F.IsHomogeneous r) :
    {u : Spec (.of L) ⟶ projectiveHypersurface hF //
      u ≫ projectiveHypersurfaceToField hF = Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
        Set.range u ⊆ Set.range (standardHypersurfaceChartι hF)} ≃
      {x : σ → L // (dehomogenize F).eval₂ (algebraMap K L) x = 0} := by
  let f := standardHypersurfaceChartι hF
  let A := {u : Spec (.of L) ⟶ Spec (.of (MvPolynomial σ K ⧸ Ideal.span {dehomogenize F})) //
        u ≫ Spec.map (CommRingCat.ofHom
          (algebraMap K (MvPolynomial σ K ⧸ Ideal.span {dehomogenize F}))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))}
  let P := {u : Spec (.of L) ⟶ projectiveHypersurface hF //
    u ≫ projectiveHypersurfaceToField hF = Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      Set.range u ⊆ Set.range f}
  let inc (u : A) : P := ⟨u.val ≫ f, by
    constructor
    · rw [Category.assoc, show f ≫ _ = _ from standardHypersurfaceChartι_toField hF]
      exact u.prop
    · rintro _ ⟨x,rfl⟩
      exact ⟨u.val x, rfl⟩⟩
  refine (Equiv.ofBijective inc ?_).symm.trans (affineHypersurfacePointsEquiv (dehomogenize F))
  refine ⟨?_,?_⟩
  · intro a b hab
    exact Subtype.ext ((cancel_mono f).mp (congrArg Subtype.val hab))
  · intro u
    let v := IsOpenImmersion.lift f u.val u.prop.2
    have hf : v ≫ f = u.val := IsOpenImmersion.lift_fac f u.val u.prop.2
    have hv : v ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial σ K ⧸ Ideal.span {dehomogenize F}))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      rw [← standardHypersurfaceChartι_toField, ← Category.assoc, hf]
      exact u.prop.1
    exact ⟨⟨v,hv⟩, Subtype.ext hf⟩

/-- The affine chart of the projective level scheme over any extension field
has exactly the points satisfying the prescribed level equation. -/
def deligneLevelSchemeAffinePointsEquiv {σ K L : Type u} [Field K] [Field L] [Algebra K L]
    {r : ℕ} {g : MvPolynomial σ K} (hg : g.totalDegree ≤ r) (t : K) :
    {u : Spec (.of L) ⟶ projectiveHypersurface (isHomogeneous_deligneLevelClosure r g t) //
      u ≫ projectiveHypersurfaceToField (isHomogeneous_deligneLevelClosure r g t) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      Set.range u ⊆ Set.range (standardHypersurfaceChartι
        (isHomogeneous_deligneLevelClosure r g t))} ≃
      {x : σ → L // g.eval₂ (algebraMap K L) x = algebraMap K L t} :=
  (projectiveHypersurfaceAffinePointsEquiv (isHomogeneous_deligneLevelClosure r g t)).trans
    (Equiv.subtypeEquivRight fun x => by
      rw [dehomogenize_deligneLevelClosure hg, eval₂_sub, eval₂_C, sub_eq_zero])

end
end Birch
