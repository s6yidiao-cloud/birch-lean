module

public import Birch.ProjectiveHypersurface

@[expose] public section

/-! # Coordinate changes for projective hypersurfaces -/

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Graded

namespace Birch

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem awayMap_fromZeroRingHom
    {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
    [AddSubgroupClass σ A] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (s : A) (c : 𝒜 0) :
    Away.map f s (fromZeroRingHom 𝒜 _ c) =
      fromZeroRingHom ℬ _ (f.gradedZeroRingHom c) := by
  apply val_injective
  change (Away.map f s (HomogeneousLocalization.mk ⟨0,c,1,one_mem _⟩)).val =
    (HomogeneousLocalization.mk ⟨0,f.gradedZeroRingHom c,1,one_mem _⟩).val
  simp only [Away.map, HomogeneousLocalization.map_mk, val_mk]
  apply congrArg (Localization.mk (f (c : A)))
  apply Subtype.ext
  exact map_one f

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of projective spectra is natural over the map of their
degree-zero coefficients. -/
theorem proj_map_toSpecZero
    {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [SetLike τ B]
    [AddSubgroupClass σ A] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s => ?_
  change (Σ i : ℕ+, ↥(𝒜 (i : ℕ))) at s
  obtain ⟨⟨i,hi⟩,a⟩ := s
  change ↥(𝒜 i) at a
  change Proj.awayι ℬ (f a) (f.map_mem a.prop) hi ≫
      Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
    Proj.awayι ℬ (f a) (f.map_mem a.prop) hi ≫
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)
  rw [Proj.awayι_comp_map_assoc f hf hi _ a.prop,
    Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext fun c => awayMap_fromZeroRingHom f a c

variable {σ τ K : Type u} [CommRing K] {d : ℕ} {F : MvPolynomial σ K}

/-- Reindexing variables yields a ring isomorphism of the homogeneous
coordinate rings. -/
def hypersurfaceRenameRingEquiv (e : σ ≃ τ) :
    HypersurfaceRing F ≃+* HypersurfaceRing (rename e F) :=
  Ideal.quotientEquiv _ _ (renameEquiv K e).toRingEquiv (by
    rw [Ideal.map_span, Set.image_singleton]
    rfl)

@[simp] theorem hypersurfaceRenameRingEquiv_apply_mk (e : σ ≃ τ)
    (p : MvPolynomial σ K) :
    hypersurfaceRenameRingEquiv (F := F) e (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename e p) := rfl

/-- The reindexing map on homogeneous coordinate rings preserves degrees. -/
def hypersurfaceRenameGradedHom (hF : F.IsHomogeneous d) (e : σ ≃ τ) :
    hypersurfaceGrading F hF →+*ᵍ hypersurfaceGrading (rename e F) hF.rename_isHomogeneous where
  __ := (hypersurfaceRenameRingEquiv (F := F) e).toRingHom
  map_mem hx := by
    obtain ⟨p,hp,rfl⟩ := hx
    exact ⟨rename e p, (show p.IsHomogeneous _ from hp).rename_isHomogeneous, rfl⟩

/-- The inverse reindexing also preserves the quotient grading. -/
def hypersurfaceRenameGradedInv (hF : F.IsHomogeneous d) (e : σ ≃ τ) :
    hypersurfaceGrading (rename e F) hF.rename_isHomogeneous →+*ᵍ hypersurfaceGrading F hF where
  __ := (hypersurfaceRenameRingEquiv (F := F) e).symm.toRingHom
  map_mem hx := by
    obtain ⟨p,hp,rfl⟩ := hx
    refine ⟨rename e.symm p, (show p.IsHomogeneous _ from hp).rename_isHomogeneous, ?_⟩
    apply (hypersurfaceRenameRingEquiv (F := F) e).injective
    change hypersurfaceRenameRingEquiv e (Ideal.Quotient.mk _ (rename e.symm p)) =
      hypersurfaceRenameRingEquiv e ((hypersurfaceRenameRingEquiv e).symm (Ideal.Quotient.mk _ p))
    rw [hypersurfaceRenameRingEquiv_apply_mk, RingEquiv.apply_symm_apply, rename_rename]
    simp

/-- Variable renaming induces an isomorphism of the projective hypersurfaces. -/
def projectiveHypersurfaceRenameIso (hF : F.IsHomogeneous d) (e : σ ≃ τ) :
    projectiveHypersurface (hF.rename_isHomogeneous (f := ⇑e)) ≅ projectiveHypersurface hF := by
  let f := hypersurfaceRenameGradedHom hF e
  let g := hypersurfaceRenameGradedInv hF e
  have hf := proj_irrelevant_le_map_of_surjective f (hypersurfaceRenameRingEquiv e).surjective
  have hg := proj_irrelevant_le_map_of_surjective g (hypersurfaceRenameRingEquiv e).symm.surjective
  have hgf : g.comp f = .id _ := by
    ext a
    exact (hypersurfaceRenameRingEquiv e).symm_apply_apply a
  have hfg : f.comp g = .id _ := by
    ext a
    exact (hypersurfaceRenameRingEquiv e).apply_symm_apply a
  refine ⟨Proj.map f hf, Proj.map g hg, ?_, ?_⟩
  · rw [← Proj.map_comp g f hg hf]
    simp only [hfg, Proj.map_id]
  · rw [← Proj.map_comp f g hf hg]
    simp only [hgf, Proj.map_id]

/-- The projective renaming isomorphism lies over the same coefficient ring. -/
@[reassoc] theorem projectiveHypersurfaceRenameIso_hom_toField (hF : F.IsHomogeneous d)
    (e : σ ≃ τ) :
    (projectiveHypersurfaceRenameIso hF e).hom ≫ projectiveHypersurfaceToField hF =
      projectiveHypersurfaceToField (hF.rename_isHomogeneous (f := ⇑e)) := by
  unfold projectiveHypersurfaceToField
  change Proj.map (hypersurfaceRenameGradedHom hF e) _ ≫ _ = _
  rw [← Category.assoc, proj_map_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change hypersurfaceRenameRingEquiv e (Ideal.Quotient.mk _ (C a)) =
    Ideal.Quotient.mk _ (C a)
  rw [hypersurfaceRenameRingEquiv_apply_mk, rename_C]

end
end Birch
