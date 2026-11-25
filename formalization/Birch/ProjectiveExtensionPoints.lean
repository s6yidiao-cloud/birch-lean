module

public import Birch.ProjectiveHypersurfaceBaseChange
public import Birch.ProjectiveHypersurfacePointEquivalence

@[expose] public section

/-! # Extension-field points of a projective hypersurface -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace Birch

noncomputable section

universe u

/-- In a fiber square over a field extension, rational points of the
top scheme are extension-valued points of the original scheme. -/
def schemeFieldValuedPointsEquivBaseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of K)} {i : Y ⟶ X}
    (h : IsPullback i g f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :
    SchemeFieldValuedPoints f K ≃ SchemeFieldValuedPoints g K := by
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
    exact Scheme.Spec.map_id _
  have hlift (x : SchemeFieldValuedPoints f K) :
      x.val ≫ f = (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    simpa only [Category.id_comp] using x.prop
  refine
    { toFun := fun x => ⟨h.lift x.val (𝟙 _) (hlift x), (h.lift_snd _ _ _).trans hbase.symm⟩
      invFun := fun y => ⟨y.val ≫ i, by rw [Category.assoc, h.w, ← Category.assoc, y.prop, hbase,
        Category.id_comp]⟩
      left_inv := fun x => Subtype.ext (h.lift_fst _ _ _)
      right_inv := fun y => Subtype.ext (h.hom_ext (h.lift_fst _ _ _)
        ((h.lift_snd _ _ _).trans (y.prop.trans hbase).symm)) }

/-- Extension-field morphisms counted by the Weil theorem correspond to
the projective coordinate solutions with coefficients in that extension. -/
def overHomEquivProjectiveHypersurfacePoints {σ k K : Type} [Field k] [Field K]
    [Algebra k K] [Finite σ] {d : ℕ} {F : MvPolynomial σ k}
    (hd : 0 < d) (hF : F.IsHomogeneous d) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
      Over.mk (projectiveHypersurfaceToField hF)) ≃
      projectiveHypersurfacePoints (MvPolynomial.map (algebraMap k K) F) := by
  classical
  exact (overHomEquivSchemeFieldValuedPoints (Over.mk (projectiveHypersurfaceToField hF))).trans
    ((schemeFieldValuedPointsEquivBaseChange
        (isPullback_projectiveHypersurfaceCoefficientMap (algebraMap k K) hF)).trans
      (projectiveHypersurfaceSchemePointsEquiv_finite hd (hF.map (algebraMap k K))))

end
end Birch
