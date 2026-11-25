module

public import Birch.ProjectiveHypersurfaceRenaming
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

/-! # Coefficient change for projective hypersurfaces -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open scoped Graded

namespace Birch

noncomputable section

universe u

variable {σ k K : Type u} [CommRing k] [CommRing K] {d : ℕ} {F : MvPolynomial σ k}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coefficient change on the quotient by one polynomial. -/
def hypersurfaceCoefficientMap (φ : k →+* K) (F : MvPolynomial σ k) :
    HypersurfaceRing F →+* HypersurfaceRing (MvPolynomial.map φ F) :=
  Ideal.quotientMap _ (MvPolynomial.map φ) (by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] theorem hypersurfaceCoefficientMap_mk (φ : k →+* K)
    (F P : MvPolynomial σ k) :
    hypersurfaceCoefficientMap φ F (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (MvPolynomial.map φ P) := rfl

/-- Coefficient change preserves the grading on a hypersurface ring. -/
def hypersurfaceCoefficientGradedMap (φ : k →+* K) (hF : F.IsHomogeneous d) :
    hypersurfaceGrading F hF →+*ᵍ hypersurfaceGrading (MvPolynomial.map φ F) (hF.map φ) where
  __ := hypersurfaceCoefficientMap φ F
  map_mem hx := by
    obtain ⟨P,hP,rfl⟩ := hx
    exact ⟨MvPolynomial.map φ P, (show P.IsHomogeneous _ from hP).map φ, rfl⟩

/-- Affine hypersurface quotients commute with coefficient base change. -/
theorem isPushout_hypersurfaceCoefficientMap (φ : k →+* K) (F : MvPolynomial σ k) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap k (HypersurfaceRing F)))
      (CommRingCat.ofHom (algebraMap K (HypersurfaceRing (MvPolynomial.map φ F))))
      (CommRingCat.ofHom (hypersurfaceCoefficientMap φ F)) := by
  let A := HypersurfaceRing F
  let B := HypersurfaceRing (MvPolynomial.map φ F)
  let π := Ideal.Quotient.mk (Ideal.span {F})
  let κ := CommRingCat.ofHom φ
  let a₀ := CommRingCat.ofHom (algebraMap k A)
  let b₀ := CommRingCat.ofHom (algebraMap K B)
  let b := CommRingCat.ofHom (hypersurfaceCoefficientMap φ F)
  have hw : κ ≫ b₀ = a₀ ≫ b := by
    apply CommRingCat.hom_ext
    ext c
    change Ideal.Quotient.mk _ (C (φ c)) = hypersurfaceCoefficientMap φ F (π (C c))
    rw [hypersurfaceCoefficientMap_mk, map_C]
  let ev (S : PushoutCocone κ a₀) : MvPolynomial σ K →+* S.pt :=
    eval₂Hom S.inl.hom (fun i => S.inr.hom (π (X i)))
  have hev (S : PushoutCocone κ a₀) :
      (ev S).comp (MvPolynomial.map φ) = S.inr.hom.comp π := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc := congrArg (fun f : CommRingCat.of k ⟶ S.pt => f.hom c) S.condition
      change S.inl.hom (φ c) = S.inr.hom (π (C c)) at hc
      simp only [RingHom.comp_apply, map_C, ev, eval₂Hom_C]
      exact hc
    · intro i
      simp only [RingHom.comp_apply, map_X, ev, eval₂Hom_X']
  have hvanish (S : PushoutCocone κ a₀) : ev S (MvPolynomial.map φ F) = 0 := by
    change ((ev S).comp (MvPolynomial.map φ)) F = 0
    rw [hev, RingHom.comp_apply,
      show π F = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F),
      map_zero]
  let lift (S : PushoutCocone κ a₀) : B →+* S.pt :=
    Ideal.Quotient.lift _ (ev S) fun P hP => by
      have hle : Ideal.span {MvPolynomial.map φ F} ≤ RingHom.ker (ev S) := by
        rw [Ideal.span_singleton_le_iff_mem]
        exact hvanish S
      exact hle hP
  refine ⟨⟨hw⟩, ⟨PushoutCocone.IsColimit.mk hw
    (fun S => CommRingCat.ofHom (lift S)) ?_ ?_ ?_⟩⟩
  · intro S
    apply CommRingCat.hom_ext
    ext c
    change ev S (C c) = S.inl.hom c
    exact eval₂Hom_C _ _ c
  · intro S
    apply CommRingCat.hom_ext
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun P => ?_)
    change ev S (MvPolynomial.map φ P) = S.inr.hom (π P)
    exact DFunLike.congr_fun (hev S) P
  · intro S m hm₁ hm₂
    apply CommRingCat.hom_ext
    refine Ideal.Quotient.ringHom_ext ?_
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc := congrArg (fun f : CommRingCat.of K ⟶ S.pt => f.hom c) hm₁
      change m.hom (Ideal.Quotient.mk _ (C c)) = ev S (C c)
      change m.hom (Ideal.Quotient.mk _ (C c)) = S.inl.hom c at hc
      change m.hom (Ideal.Quotient.mk _ (C c)) = eval₂Hom S.inl.hom _ (C c)
      rw [eval₂Hom_C]
      exact hc
    · intro i
      have hc := congrArg (fun f : CommRingCat.of A ⟶ S.pt => f.hom (π (X i))) hm₂
      change m.hom (hypersurfaceCoefficientMap φ F (π (X i))) = S.inr.hom (π (X i)) at hc
      change m.hom (Ideal.Quotient.mk _ (X i)) = ev S (X i)
      rw [hypersurfaceCoefficientMap_mk, map_X] at hc
      dsimp only [ev]
      rw [eval₂Hom_X']
      exact hc

/-- The coordinate classes generate the irrelevant ideal of the homogeneous quotient. -/
theorem irrelevant_hypersurface_le_span_coordinates (hF : F.IsHomogeneous d) :
    (HomogeneousIdeal.irrelevant (hypersurfaceGrading F hF)).toIdeal ≤
      Ideal.span (Set.range fun i : σ => hypersurfaceQuotientHom hF (X i)) := by
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  refine Set.iUnion₂_subset fun i hi => ?_
  rintro _ ⟨P,hP,rfl⟩
  let π := (hypersurfaceQuotientHom hF).toRingHom
  have hmem : P ∈ idealOfVars σ k := by
    rw [← pow_one (idealOfVars σ k), mem_pow_idealOfVars_iff]
    intro m hm
    have he := (show P.IsHomogeneous i from hP).degree_eq_sum_deg_support hm
    change i = m.degree at he
    rwa [← he]
  have hh := Ideal.mem_map_of_mem π hmem
  change π P ∈ Ideal.span (Set.range fun i => π (X i))
  rw [idealOfVars, Ideal.map_span, ← Set.range_comp'] at hh
  exact hh

/-- Coefficient change induces a morphism of Proj because the images of the
coordinate variables generate the irrelevant ideal. -/
theorem hypersurfaceCoefficientGradedMap_irrelevant (φ : k →+* K)
    (hF : F.IsHomogeneous d) :
    HomogeneousIdeal.irrelevant (hypersurfaceGrading _ (hF.map φ)) ≤
      (HomogeneousIdeal.irrelevant (hypersurfaceGrading F hF)).map
        (hypersurfaceCoefficientGradedMap φ hF) := by
  change (HomogeneousIdeal.irrelevant (hypersurfaceGrading _ (hF.map φ))).toIdeal ≤
    ((HomogeneousIdeal.irrelevant (hypersurfaceGrading F hF)).map
      (hypersurfaceCoefficientGradedMap φ hF)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  refine (irrelevant_hypersurface_le_span_coordinates (hF.map φ)).trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨i,rfl⟩
  let π := hypersurfaceQuotientHom hF
  have hπ : π (X i) ∈ HomogeneousIdeal.irrelevant (hypersurfaceGrading F hF) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (π.map_mem (isHomogeneous_X k i))
  have hh := Ideal.mem_map_of_mem (hypersurfaceCoefficientGradedMap φ hF).toRingHom hπ
  change hypersurfaceCoefficientMap φ F (Ideal.Quotient.mk _ (X i)) ∈ _ at hh
  rw [hypersurfaceCoefficientMap_mk, map_X] at hh
  change Ideal.Quotient.mk _ (X i) ∈
    Ideal.map (hypersurfaceCoefficientGradedMap φ hF).toRingHom
      (HomogeneousIdeal.irrelevant (hypersurfaceGrading F hF)).toIdeal
  exact hh

/-- The morphism of homogeneous hypersurfaces induced by coefficient change. -/
def projectiveHypersurfaceCoefficientMap (φ : k →+* K) (hF : F.IsHomogeneous d) :
    projectiveHypersurface (hF.map φ) ⟶ projectiveHypersurface hF :=
  Proj.map (hypersurfaceCoefficientGradedMap φ hF)
    (hypersurfaceCoefficientGradedMap_irrelevant φ hF)

@[reassoc] theorem projectiveHypersurfaceCoefficientMap_toField (φ : k →+* K)
    (hF : F.IsHomogeneous d) :
    projectiveHypersurfaceCoefficientMap φ hF ≫ projectiveHypersurfaceToField hF =
      projectiveHypersurfaceToField (hF.map φ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold projectiveHypersurfaceToField projectiveHypersurfaceCoefficientMap
  rw [← Category.assoc, proj_map_toSpecZero, Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change hypersurfaceCoefficientMap φ F (Ideal.Quotient.mk _ (C a)) =
    Ideal.Quotient.mk _ (C (φ a))
  rw [hypersurfaceCoefficientMap_mk, map_C]

/-- Normalizing a coordinate commutes with mapping the coefficients. -/
theorem map_dehomogenize {τ : Type u} (φ : k →+* K) (P : MvPolynomial (Option τ) k) :
    MvPolynomial.map φ (dehomogenize P) = dehomogenize (MvPolynomial.map φ P) := by
  have h : (MvPolynomial.map φ).comp (dehomogenize (σ := τ) (R := k)).toRingHom =
      (dehomogenize (σ := τ) (R := K)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.map φ (dehomogenize (C c : MvPolynomial (Option τ) k)) =
        dehomogenize (MvPolynomial.map φ (C c))
      rw [dehomogenize_C, map_C, map_C, dehomogenize_C]
    · intro i
      change MvPolynomial.map φ (dehomogenize (X i : MvPolynomial (Option τ) k)) =
        dehomogenize (MvPolynomial.map φ (X i))
      rw [map_X]
      cases i with
      | none => rw [dehomogenize_X_none, dehomogenize_X_none, map_one]
      | some i => rw [dehomogenize_X_some, dehomogenize_X_some, map_X]
  exact DFunLike.congr_fun h P

end
end Birch
