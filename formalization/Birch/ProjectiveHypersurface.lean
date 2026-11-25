module

public import Birch.MvPolynomialCoefficientCompat

public import Birch.GradedQuotient
public import Birch.ProjectiveCharts
public import Birch.ProjectiveClosedImmersion
public import Mathlib.RingTheory.Finiteness.Quotient

@[expose] public section

/-! # Scheme models of homogeneous polynomial equations -/

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Birch

noncomputable section

universe u
variable {σ K : Type u} [CommRing K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous coordinate ring of a hypersurface. -/
abbrev HypersurfaceRing (F : MvPolynomial σ K) :=
  MvPolynomial σ K ⧸ Ideal.span {F}

/-- The grading on the homogeneous coordinate ring. -/
def hypersurfaceGrading (F : MvPolynomial σ K) {d : ℕ} (_ : F.IsHomogeneous d) :=
  GradedQuotient.grading (homogeneousSubmodule σ K) (Ideal.span {F})

theorem hypersurfaceIdeal_isHomogeneous {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) : (Ideal.span {F}).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply Ideal.homogeneous_span
  rintro _ h
  obtain rfl := Set.mem_singleton_iff.mp h
  exact ⟨d,hF⟩

instance {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    GradedRing (hypersurfaceGrading F hF) :=
  GradedQuotient.gradedRing (homogeneousSubmodule σ K) (Ideal.span {F})
    (hypersurfaceIdeal_isHomogeneous hF)

/-- The projective hypersurface `Proj(K[X]/(F))`. -/
abbrev projectiveHypersurface {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) : Scheme :=
  Proj (hypersurfaceGrading F hF)

/-- The quotient of the homogeneous coordinate ring, preserving degrees. -/
def hypersurfaceQuotientHom {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    (homogeneousSubmodule σ K) →+*ᵍ (hypersurfaceGrading F hF) where
  __ := Ideal.Quotient.mk (Ideal.span {F})
  map_mem hp := ⟨_,hp,rfl⟩

@[simp] theorem hypersurfaceQuotientHom_apply {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) (p : MvPolynomial σ K) :
    hypersurfaceQuotientHom hF p = Ideal.Quotient.mk (Ideal.span {F}) p := rfl

theorem hypersurfaceQuotientHom_surjective {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) : Function.Surjective (hypersurfaceQuotientHom hF) :=
  Ideal.Quotient.mk_surjective

/-- The degree-zero part of the homogeneous coordinate ring receives the
coefficient ring via constant polynomials. -/
def hypersurfaceConstants {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    K →+* hypersurfaceGrading F hF 0 :=
  { toFun := fun a => ⟨Ideal.Quotient.mk (Ideal.span {F}) (C a), ⟨C a,isHomogeneous_C _ _,rfl⟩⟩
    map_zero' := Subtype.ext ((Ideal.Quotient.mk (Ideal.span {F})).comp C |>.map_zero)
    map_one' := Subtype.ext ((Ideal.Quotient.mk (Ideal.span {F})).comp C |>.map_one)
    map_add' := fun a b => Subtype.ext (((Ideal.Quotient.mk (Ideal.span {F})).comp C).map_add a b)
    map_mul' := fun a b => Subtype.ext (((Ideal.Quotient.mk (Ideal.span {F})).comp C).map_mul a b) }

theorem hypersurfaceConstants_bijective {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) (hd : 0 < d) : Function.Bijective (hypersurfaceConstants hF) := by
  constructor
  · have h₀ : eval (0 : σ → K) F = 0 := by
      rw [eval_zero]
      change coeff 0 F = 0
      by_contra! h
      have hm := hF.degree_eq_sum_deg_support (mem_support_iff.mpr h)
      exact hd.ne' (by simpa using hm)
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    have h : C a ∈ Ideal.span {F} := Ideal.Quotient.eq_zero_iff_mem.mp
      (congrArg Subtype.val ha)
    have hker : Ideal.span {F} ≤ RingHom.ker (eval (0 : σ → K)) := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact h₀
    have he : eval (0 : σ → K) (C a) = 0 := hker h
    simpa using he
  · rintro ⟨y,p,hp,rfl⟩
    have hph : p.IsHomogeneous 0 := hp
    have hdeg := Nat.eq_zero_of_le_zero hph.totalDegree_le
    refine ⟨coeff 0 p, Subtype.ext ?_⟩
    change Ideal.Quotient.mk _ (C (coeff 0 p)) = Ideal.Quotient.mk _ p
    congr 1
    exact (totalDegree_eq_zero_iff_eq_C.mp hdeg).symm

/-- The structure morphism of the projective hypersurface over the coefficient ring. -/
def projectiveHypersurfaceToField {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) :
    projectiveHypersurface hF ⟶ Spec (.of K) :=
  Proj.toSpecZero (hypersurfaceGrading F hF) ≫ Spec.map (CommRingCat.ofHom (hypersurfaceConstants hF))

theorem isProper_projectiveHypersurfaceToField [Finite σ]
    {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) (hd : 0 < d) :
    IsProper (projectiveHypersurfaceToField hF) := by
  let : Algebra K (hypersurfaceGrading F hF 0) := (hypersurfaceConstants hF).toAlgebra
  let : IsScalarTower K (hypersurfaceGrading F hF 0) (HypersurfaceRing F) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType (hypersurfaceGrading F hF 0) (HypersurfaceRing F) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  let e := RingEquiv.ofBijective (hypersurfaceConstants hF) (hypersurfaceConstants_bijective hF hd)
  let : IsIso (CommRingCat.ofHom (hypersurfaceConstants hF)) := e.toCommRingCatIso.isIso_hom
  let : IsIso (Spec.map (CommRingCat.ofHom (hypersurfaceConstants hF))) := by
    change IsIso (Scheme.Spec.map (CommRingCat.ofHom (hypersurfaceConstants hF)).op)
    infer_instance
  have hproper : IsProper (Proj.toSpecZero (hypersurfaceGrading F hF)) := by infer_instance
  unfold projectiveHypersurfaceToField
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)
    (Proj.toSpecZero (hypersurfaceGrading F hF))
    (Spec.map (CommRingCat.ofHom (hypersurfaceConstants hF)))).mpr hproper

/-- The embedding into projective space given by the homogeneous equation. -/
def projectiveHypersurfaceι {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    projectiveHypersurface hF ⟶ Proj (homogeneousSubmodule σ K) :=
  Proj.map (hypersurfaceQuotientHom hF)
    (proj_irrelevant_le_map_of_surjective _ (hypersurfaceQuotientHom_surjective hF))

instance {d : ℕ} {F : MvPolynomial σ K} (hF : F.IsHomogeneous d) :
    IsClosedImmersion (projectiveHypersurfaceι hF) :=
  isClosedImmersion_proj_map_of_surjective _ (hypersurfaceQuotientHom_surjective hF)

section StandardChart

variable {d : ℕ} {F : MvPolynomial (Option σ) K} (hF : F.IsHomogeneous d)

theorem extraVariable_isHomogeneous :
    (X (R := K) (none : Option σ)).IsHomogeneous 1 :=
  isHomogeneous_X _ _

/-- The degree-zero ring of the chart where the distinguished coordinate
is invertible. -/
abbrev StandardHypersurfaceChart :=
  Away (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X none))

/-- Restrict the quotient map to the degree-zero chart. -/
def standardHypersurfaceChartMap : StandardProjectiveChart σ K →+* StandardHypersurfaceChart hF :=
  Away.map (hypersurfaceQuotientHom hF) (X none)

theorem standardHypersurfaceChartMap_surjective :
    Function.Surjective (standardHypersurfaceChartMap hF) :=
  proj_away_map_surjective_of_surjective _ (hypersurfaceQuotientHom_surjective hF)
    (i := 1) extraVariable_isHomogeneous

/-- The chart kernel is exactly the affine equation obtained by setting
the distinguished coordinate to one. -/
theorem ker_standardHypersurfaceChartMap :
    RingHom.ker (standardHypersurfaceChartMap hF) =
      Ideal.comap projectiveChartNormalize (Ideal.span {dehomogenize F}) := by
  let Δ := homogeneousSubmodule (Option σ) K
  let π := hypersurfaceQuotientHom hF
  let f := X (R := K) (none : Option σ)
  have hf : f ∈ Δ 1 := extraVariable_isHomogeneous
  ext z
  rw [RingHom.mem_ker, Ideal.mem_comap, Ideal.mem_span_singleton]
  constructor
  · obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective Δ hf z
    intro hz
    rw [standardHypersurfaceChartMap, Away.map_mk, HomogeneousLocalization.ext_iff_val,
      Away.val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨v,hv⟩ := hz
    obtain ⟨k,hk⟩ := v.prop
    change π f ^ k = (v : HypersurfaceRing F) at hk
    have hπ : π (f^k * a) = 0 := by
      rw [map_mul, map_pow, hk]
      exact hv
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hπ
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hmem
    have he := congrArg (dehomogenize (σ := σ) (R := K)) hb
    simp only [map_mul, map_pow, f, dehomogenize_X_none, one_pow, one_mul] at he
    rw [projectiveChartNormalize_fraction _ ha]
    exact ⟨dehomogenize b,he⟩
  · rintro ⟨b,hb⟩
    obtain ⟨y,hy⟩ := projectiveChartRingEquiv.surjective b
    let w := Away.mk Δ hf d F (by
      change F.IsHomogeneous (d • (1 : ℕ))
      simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using hF)
    have hw : projectiveChartNormalize w = dehomogenize F :=
      projectiveChartNormalize_fraction _ _
    have hwy : z = w * y := by
      apply projectiveChartRingEquiv.injective
      change projectiveChartNormalize z = projectiveChartNormalize (w * y)
      rw [map_mul, hw]
      exact hb.trans (congrArg (dehomogenize F * ·) hy.symm)
    have hw₀ : standardHypersurfaceChartMap hF w = 0 := by
      unfold standardHypersurfaceChartMap w
      rw [Away.map_mk, HomogeneousLocalization.ext_iff_val, Away.val_mk, val_zero]
      simp only [hypersurfaceQuotientHom_apply,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton F)),
        Localization.mk_zero]
      rfl
    rw [hwy, map_mul, hw₀, zero_mul]

/-- The standard chart of the projective hypersurface is the affine
hypersurface given by the dehomogenized polynomial. -/
def standardHypersurfaceChartEquiv :
    StandardHypersurfaceChart hF ≃+* (MvPolynomial σ K ⧸ Ideal.span {dehomogenize F}) :=
  ((standardHypersurfaceChartMap hF).quotientKerEquivOfSurjective
    (standardHypersurfaceChartMap_surjective hF)).symm.trans
    (Ideal.quotientEquiv _ _ projectiveChartRingEquiv (by
      rw [ker_standardHypersurfaceChartMap]
      exact (Ideal.map_comap_of_surjective _ projectiveChartRingEquiv.surjective _).symm))

@[simp] theorem standardHypersurfaceChartEquiv_apply_map (z : StandardProjectiveChart σ K) :
    standardHypersurfaceChartEquiv hF (standardHypersurfaceChartMap hF z) =
      Ideal.Quotient.mk _ (projectiveChartNormalize z) := by
  rw [standardHypersurfaceChartEquiv, RingEquiv.trans_apply, RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

/-- The affine hypersurface embeds as the open chart of the projective
hypersurface. -/
def standardHypersurfaceChartι :
    Spec (.of (MvPolynomial σ K ⧸ Ideal.span {dehomogenize F})) ⟶ projectiveHypersurface hF :=
  Spec.map (CommRingCat.ofHom (standardHypersurfaceChartEquiv hF).toRingHom) ≫
    Proj.awayι (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X none))
      ((hypersurfaceQuotientHom hF).map_mem extraVariable_isHomogeneous) Nat.one_pos

instance : IsOpenImmersion (standardHypersurfaceChartι hF) := by
  let e := (standardHypersurfaceChartEquiv hF).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (standardHypersurfaceChartEquiv hF).toRingHom) := e.isIso_hom
  unfold standardHypersurfaceChartι
  let : IsIso (Spec.map (CommRingCat.ofHom (standardHypersurfaceChartEquiv hF).toRingHom)) := by
    change IsIso (Scheme.Spec.map (CommRingCat.ofHom (standardHypersurfaceChartEquiv hF).toRingHom).op)
    infer_instance
  exact IsOpenImmersion.comp _ _

private theorem standardHypersurfaceChartMap_constants (a : K) :
    standardHypersurfaceChartMap hF
      (fromZeroRingHom _ _ (degreeZeroConstants (Option σ) K a)) =
    fromZeroRingHom _ _ (hypersurfaceConstants hF a) := by
  apply val_injective
  change (Away.map (hypersurfaceQuotientHom hF) (X none)
    (HomogeneousLocalization.mk ⟨0, degreeZeroConstants (Option σ) K a, 1, one_mem _⟩)).val = _
  simp only [Away.map, HomogeneousLocalization.map_mk, fromZeroRingHom, val_mk]
  rfl

/-- The open chart embedding respects its structure morphism over the coefficient ring. -/
@[reassoc] theorem standardHypersurfaceChartι_toField :
    standardHypersurfaceChartι hF ≫ projectiveHypersurfaceToField hF =
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ Ideal.span {dehomogenize F}))) := by
  unfold standardHypersurfaceChartι projectiveHypersurfaceToField
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  change standardHypersurfaceChartEquiv hF
    (fromZeroRingHom _ _ (hypersurfaceConstants hF a)) =
    Ideal.Quotient.mk _ (C a)
  rw [← standardHypersurfaceChartMap_constants, standardHypersurfaceChartEquiv_apply_map,
    projectiveChartNormalize_constants]

/-- The standard affine chart is the basic open of the distinguished coordinate. -/
theorem opensRange_standardHypersurfaceChartι {d : ℕ} {F : MvPolynomial (Option σ) K}
    (hF : F.IsHomogeneous d) :
    (standardHypersurfaceChartι hF).opensRange =
      Proj.basicOpen (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X none)) := by
  let e := (standardHypersurfaceChartEquiv hF).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (standardHypersurfaceChartEquiv hF).toRingHom) := e.isIso_hom
  unfold standardHypersurfaceChartι
  let : IsIso (Spec.map (CommRingCat.ofHom (standardHypersurfaceChartEquiv hF).toRingHom)) := by
    change IsIso (Scheme.Spec.map (CommRingCat.ofHom (standardHypersurfaceChartEquiv hF).toRingHom).op)
    infer_instance
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

end StandardChart

end
end Birch
