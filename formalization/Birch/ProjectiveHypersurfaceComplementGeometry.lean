module

public import Birch.ProjectiveHypersurfaceBoundary
public import Birch.ProjectiveIntegralCriterion
public import Birch.ProjectiveHypersurfaceSmooth
public import Birch.ProjectiveHypersurfaceBaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

@[expose] public section

/-! # The affine complement of a projective hypersurface -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace Birch

noncomputable section

universe u

variable {σ K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structure map for projective space in polynomial coordinates. -/
def projectivePolynomialSpaceToField (σ K : Type u) [Field K] :
    Proj (homogeneousSubmodule σ K) ⟶ Spec (.of K) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (degreeZeroConstants σ K))

/-- The hypersurface immersion respects the structure maps. -/
@[reassoc] theorem projectiveHypersurfaceι_toField {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) :
    projectiveHypersurfaceι hF ≫ projectivePolynomialSpaceToField σ K =
      projectiveHypersurfaceToField hF := by
  unfold projectiveHypersurfaceι projectiveHypersurfaceToField projectivePolynomialSpaceToField
  rw [← Category.assoc, proj_map_toSpecZero, Category.assoc, ← Spec.map_comp]
  rfl

/-- The image of the hypersurface immersion is the complement of (D_+(F)). -/
theorem range_projectiveHypersurfaceι {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    Set.range (projectiveHypersurfaceι hF) =
      ((Proj.basicOpen (homogeneousSubmodule σ K) F : Set (Proj (homogeneousSubmodule σ K))))ᶜ := by
  change Set.range (Proj.map (hypersurfaceQuotientHom hF) _) = _
  rw [range_proj_map_eq_zeroLocus_ker_of_surjective _ (hypersurfaceQuotientHom_surjective hF)]
  have hker : RingHom.ker (hypersurfaceQuotientHom hF).toRingHom = Ideal.span {F} := Ideal.mk_ker
  rw [hker, ProjectiveSpectrum.zeroLocus_span]
  change _ = ((ProjectiveSpectrum.basicOpen (homogeneousSubmodule σ K) F :
    Set (ProjectiveSpectrum (homogeneousSubmodule σ K))))ᶜ
  rw [ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl]

/-- The complement is the affine standard open with coordinate ring given
by the degree-zero part of the localization at the equation. -/
def projectiveHypersurfaceComplementIsoSpec {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) (hd : 0 < d) :
    (Proj.basicOpen (homogeneousSubmodule σ K) F).toScheme ≅
      Spec (.of (HomogeneousLocalization.Away (homogeneousSubmodule σ K) F)) :=
  Proj.basicOpenIsoSpec _ F hF hd

def linearHyperplaneToCoordinates (σ K : Type u) [Field K] :
    hypersurfaceGrading (X (R := K) (none : Option σ)) (isHomogeneous_X K _) →+*ᵍ
      homogeneousSubmodule σ K where
  __ := Ideal.Quotient.lift (Ideal.span {X none}) setExtraCoordinateZero.toRingHom
    (fun _ hp => (show Ideal.span {X none} ≤ RingHom.ker setExtraCoordinateZero.toRingHom by
      rw [ker_setExtraCoordinateZero]) hp)
  map_mem := by
    rintro i _ ⟨p, hp, rfl⟩
    exact isHomogeneous_setExtraCoordinateZero hp

def coordinatesToLinearHyperplane (σ K : Type u) [Field K] :
    homogeneousSubmodule σ K →+*ᵍ
      hypersurfaceGrading (X (R := K) (none : Option σ)) (isHomogeneous_X K _) where
  __ := (hypersurfaceQuotientHom (isHomogeneous_X K _)).toRingHom.comp (rename some).toRingHom
  map_mem := by
    intro i p hp
    exact ⟨rename some p, (show p.IsHomogeneous i from hp).rename_isHomogeneous, rfl⟩

/-- Polynomial projective space is the linear hyperplane with one extra
coordinate set to zero. -/
def projectivePolynomialSpaceLinearHyperplaneIso (σ K : Type u) [Field K] :
    Proj (homogeneousSubmodule σ K) ≅ projectiveHypersurface (isHomogeneous_X K (none : Option σ)) := by
  let f := linearHyperplaneToCoordinates σ K
  let g := coordinatesToLinearHyperplane σ K
  have hfg : f.comp g = GradedRingHom.id _ := by
    apply DFunLike.ext _ _
    intro p
    exact setExtraCoordinateZero_rename_some p
  have hgf : g.comp f = GradedRingHom.id _ := by
    ext x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (rename some (setExtraCoordinateZero p)) = Ideal.Quotient.mk _ p
    rw [Ideal.Quotient.eq, ← ker_setExtraCoordinateZero, RingHom.mem_ker, map_sub]
    simp
  have hf := proj_irrelevant_le_map_of_surjective f
    (fun p => ⟨g p, DFunLike.congr_fun hfg p⟩)
  have hg := proj_irrelevant_le_map_of_surjective g
    (fun p => ⟨f p, DFunLike.congr_fun hgf p⟩)
  refine ⟨Proj.map f hf, Proj.map g hg, ?_, ?_⟩
  · rw [← Proj.map_comp g f hg hf]
    simp only [hfg, Proj.map_id]
  · rw [← Proj.map_comp f g hf hg]
    simp only [hgf, Proj.map_id]

@[reassoc] theorem projectivePolynomialSpaceLinearHyperplaneIso_hom_toField
    (σ K : Type u) [Field K] :
    (projectivePolynomialSpaceLinearHyperplaneIso σ K).hom ≫
        projectiveHypersurfaceToField (isHomogeneous_X K (none : Option σ)) =
      projectivePolynomialSpaceToField σ K := by
  unfold projectivePolynomialSpaceLinearHyperplaneIso projectiveHypersurfaceToField
    projectivePolynomialSpaceToField
  rw [← Category.assoc, proj_map_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact setExtraCoordinateZero_C a

/-- The polynomial model of projective space is smooth of the expected
relative dimension. -/
theorem smoothOfRelativeDimension_projectivePolynomialSpaceToField [Fintype σ] :
    SmoothOfRelativeDimension (Fintype.card σ - 1) (projectivePolynomialSpaceToField σ K) := by
  classical
  let hX := isHomogeneous_X K (none : Option σ)
  have hj : ∀ i : Option σ, ∃ N : ℕ, X i^N ∈ Ideal.span
      (insert (X (R := K) none) (Set.range fun j : Option σ => pderiv j (X none))) := by
    intro i
    refine ⟨0, ?_⟩
    rw [pow_zero, ← pderiv_X_self]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨none, rfl⟩)
  have h := smoothOfRelativeDimension_projectiveHypersurfaceToField hX hj
  rw [Fintype.card_option, show Fintype.card σ + 1 - 2 = Fintype.card σ - 1 by omega] at h
  let := h
  rw [← projectivePolynomialSpaceLinearHyperplaneIso_hom_toField]
  exact zero_add (Fintype.card σ - 1) ▸ (inferInstance : SmoothOfRelativeDimension
    (0 + (Fintype.card σ - 1)) ((projectivePolynomialSpaceLinearHyperplaneIso σ K).hom ≫
      projectiveHypersurfaceToField hX))

/-- The affine complement has the same smooth relative dimension as the
ambient projective space. -/
theorem smoothOfRelativeDimension_projectiveHypersurfaceComplement [Fintype σ]
    (F : MvPolynomial σ K) : SmoothOfRelativeDimension (Fintype.card σ - 1)
      ((Proj.basicOpen (homogeneousSubmodule σ K) F).ι ≫ projectivePolynomialSpaceToField σ K) := by
  let := smoothOfRelativeDimension_projectivePolynomialSpaceToField (σ := σ) (K := K)
  exact zero_add (Fintype.card σ - 1) ▸ (inferInstance : SmoothOfRelativeDimension
    (0 + (Fintype.card σ - 1)) _)

/-- The polynomial projective space is proper over the coefficient field. -/
theorem isProper_projectivePolynomialSpaceToField [Finite σ] :
    IsProper (projectivePolynomialSpaceToField σ K) := by
  let hX := isHomogeneous_X K (none : Option σ)
  have := isProper_projectiveHypersurfaceToField hX (by decide)
  rw [← projectivePolynomialSpaceLinearHyperplaneIso_hom_toField]
  infer_instance

/-- Projective space on a nonempty finite coordinate set is geometrically integral. -/
theorem geometricallyIntegral_projectivePolynomialSpaceToField {τ k : Type} [Field k]
    [Finite τ] [Nonempty τ] : GeometricallyIntegral (projectivePolynomialSpaceToField τ k) := by
  classical
  let hX := isHomogeneous_X k (none : Option τ)
  have hlinear : GeometricallyIntegral (projectiveHypersurfaceToField hX) := by
    rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
    intro L _ _ W fst snd hW
    let φ := algebraMap k L
    have hI : IsIntegral (projectiveHypersurface (hX.map φ)) := by
      have hbase : IsIntegral (Proj (homogeneousSubmodule τ L)) :=
        isIntegral_proj_of_isDomain (homogeneousSubmodule τ L) (by decide : 0 < 1)
          (isHomogeneous_X L (Classical.choice ‹Nonempty τ›)) (X_ne_zero _)
      let := hbase
      have hlin : IsIntegral (projectiveHypersurface (isHomogeneous_X L (none : Option τ))) :=
        IsIntegral.of_isIso (projectivePolynomialSpaceLinearHyperplaneIso τ L).hom
      have hEq : MvPolynomial.map φ (X (none : Option τ)) = X none := map_X _ _
      have transfer {P Q : MvPolynomial (Option τ) L} (he : P = Q)
          (hP : P.IsHomogeneous 1) (hQ : Q.IsHomogeneous 1) :
          IsIntegral (projectiveHypersurface hQ) → IsIntegral (projectiveHypersurface hP) := by
        subst Q
        exact id
      exact transfer hEq (hX.map φ) (isHomogeneous_X L none) hlin
    let := hI
    let e := (isPullback_projectiveHypersurfaceCoefficientMap φ hX).isoPullback ≪≫ hW.isoPullback.symm
    exact IsIntegral.of_isIso e.hom
  let : MorphismProperty.RespectsIso (@GeometricallyIntegral : MorphismProperty Scheme) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← projectivePolynomialSpaceLinearHyperplaneIso_hom_toField]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIntegral) _ _).mpr hlinear

private theorem geometricallyIntegral_of_nonempty_openImmersion_over_field
    {k : Type u} [Field k] {U P : Scheme.{u}} [Nonempty U]
    (j : U ⟶ P) [IsOpenImmersion j] (f : P ⟶ Spec (.of k)) [GeometricallyIntegral f] :
    GeometricallyIntegral (j ≫ f) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro L _ _ W fst snd hW
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hg : Surjective g := ⟨fun x => ⟨Classical.choice (inferInstance : Nonempty (Spec (.of L))),
    Subsingleton.elim _ _⟩⟩
  let hP := IsPullback.of_hasPullback f g
  let : IsIntegral (pullback f g) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) _ _ _ hP
  let a := hP.lift (fst ≫ j) snd (by rw [Category.assoc, hW.w])
  have hcart : IsPullback fst a j (pullback.fst f g) := hW.of_bot' hP
  have : IsOpenImmersion a := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hcart inferInstance
  have hfst : Surjective fst := MorphismProperty.of_isPullback (P := @Surjective) hW.flip hg
  let : Nonempty W := ⟨(hfst.1 (Classical.choice (inferInstance : Nonempty U))).choose⟩
  exact isIntegral_of_isOpenImmersion a

/-- The complement of a nonzero homogeneous equation of positive degree
is an affine geometrically integral open of projective space. -/
theorem affine_geometricallyIntegral_projectiveHypersurfaceComplement
    {k σ : Type} [Field k] [Fintype σ] [Nonempty σ] {d : ℕ}
    {F : MvPolynomial σ k} (hF : F.IsHomogeneous d) (hd : 0 < d) (hF₀ : F ≠ 0) :
    let U := Proj.basicOpen (homogeneousSubmodule σ k) F
    IsAffine U.toScheme ∧ GeometricallyIntegral (U.ι ≫ projectivePolynomialSpaceToField σ k) := by
  let U := Proj.basicOpen (homogeneousSubmodule σ k) F
  refine ⟨IsAffine.of_isIso (projectiveHypersurfaceComplementIsoSpec hF hd).hom, ?_⟩
  let η : ProjectiveSpectrum (homogeneousSubmodule σ k) :=
    { asHomogeneousIdeal := ⊥
      isPrime := Ideal.isPrime_bot
      not_irrelevant_le := fun h => hF₀ (by
        have hmem := HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousSubmodule σ k) hd hF
        exact h hmem) }
  let : Nonempty U.toScheme := U.nonempty_iff.mpr ⟨η, (Proj.mem_basicOpen _ _ _).mpr hF₀⟩
  let := geometricallyIntegral_projectivePolynomialSpaceToField (τ := σ) (k := k)
  exact geometricallyIntegral_of_nonempty_openImmersion_over_field U.ι _

end

end Birch
