/-
The affine hypersurface presentation and Jacobian calculation are adapted from AxiomMath/Stacks,
StacksFrontier/RingTheory/Smooth/AffineHypersurface.lean
at revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf.
Released under Apache 2.0 as described in LICENSES/Apache-2.0.txt.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

@[expose] public section

/-! # A Jacobian criterion for affine hypersurfaces -/

open MvPolynomial

namespace Birch

universe u

noncomputable section

variable {σ k : Type*} [CommRing k]

private def affineHypersurfacePresentation (f : MvPolynomial σ k) :
    Algebra.Presentation k (MvPolynomial σ k ⧸ Ideal.span {f}) σ (Fin 1) :=
  (Algebra.Presentation.naive (v := fun _ : Fin 1 => f)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq k (by rw [Set.range_const]))

private theorem affineHypersurfacePresentation_relation (f : MvPolynomial σ k) (i : Fin 1) :
    (affineHypersurfacePresentation f).relation i = f := by
  simp [affineHypersurfacePresentation, Algebra.Presentation.ofAlgEquiv_relation]

private theorem affineHypersurfacePresentation_algebraMap (f x : MvPolynomial σ k) :
    algebraMap (affineHypersurfacePresentation f).Ring (MvPolynomial σ k ⧸ Ideal.span {f}) x =
      Ideal.Quotient.mk _ x := by
  have hval (i : σ) :
      (affineHypersurfacePresentation f).val i = Ideal.Quotient.mk (Ideal.span {f}) (X i) := by
    simp [affineHypersurfacePresentation, Algebra.Presentation.ofAlgEquiv,
      Algebra.Generators.ofAlgEquiv_val, Algebra.Generators.naive_val]
  rw [Algebra.Generators.algebraMap_apply]
  have h : (aeval (affineHypersurfacePresentation f).val : MvPolynomial σ k →ₐ[k] _) =
      Ideal.Quotient.mkₐ k (Ideal.span {f}) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hval]
  exact DFunLike.congr_fun h x

private def affineHypersurfacePreSubmersive (f : MvPolynomial σ k) (i : σ) :
    Algebra.PreSubmersivePresentation k (MvPolynomial σ k ⧸ Ideal.span {f}) σ (Fin 1) :=
  .mk (affineHypersurfacePresentation f) (fun _ => i) (fun a b _ => Subsingleton.elim a b)

private theorem affineHypersurfacePreSubmersive_jacobian (f : MvPolynomial σ k) (i : σ) :
    (affineHypersurfacePreSubmersive f i).jacobian =
      Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f) := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change algebraMap (affineHypersurfacePresentation f).Ring _
    (pderiv i ((affineHypersurfacePresentation f).relation (0 : Fin 1))) = _
  rw [affineHypersurfacePresentation_relation]
  exact affineHypersurfacePresentation_algebraMap f _

private def affineHypersurfaceSubmersiveAway (f : MvPolynomial σ k) (i : σ) :
    Algebra.SubmersivePresentation k
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)))
      (Unit ⊕ σ) (Unit ⊕ Fin 1) := by
  let A := MvPolynomial σ k ⧸ Ideal.span {f}
  let δ : A := Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f)
  let T := Localization.Away δ
  let P := affineHypersurfacePreSubmersive f i
  let Q := Algebra.PreSubmersivePresentation.localizationAway T δ
  have hδ : IsUnit (algebraMap A T δ) := IsLocalization.Away.algebraMap_isUnit δ
  have hu : IsUnit (Q.comp P).jacobian := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def]
    change IsUnit (algebraMap A T (affineHypersurfacePreSubmersive f i).jacobian *
      (Algebra.PreSubmersivePresentation.localizationAway T δ).jacobian)
    rw [affineHypersurfacePreSubmersive_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian]
    exact hδ.mul hδ
  exact { toPreSubmersivePresentation := Q.comp P, jacobian_isUnit := hu }

/-- Localizing at a partial derivative gives a standard smooth algebra. -/
theorem isStandardSmooth_away_hypersurface_pderiv [Finite σ]
    (f : MvPolynomial σ k) (i : σ) :
    Algebra.IsStandardSmooth k
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) :=
  (affineHypersurfaceSubmersiveAway f i).isStandardSmooth

/-- Each standard smooth chart of the affine hypersurface has relative
dimension one less than the number of variables. -/
theorem isStandardSmoothOfRelativeDimension_away_hypersurface_pderiv [Fintype σ]
    (f : MvPolynomial σ k) (i : σ) :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) k
      (Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) := by
  apply (affineHypersurfaceSubmersiveAway f i).isStandardSmoothOfRelativeDimension
  simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Fintype.card_sum,
    Fintype.card_unit, Fintype.card_fin]
  omega

/-- If a polynomial and its partial derivatives generate the unit ideal,
its affine hypersurface over the coefficient ring is smooth. -/
theorem smooth_quotient_of_span_eq_top_finite [Finite σ] {f : MvPolynomial σ k}
    (h : Ideal.span (insert f (Set.range fun i => pderiv i f)) = ⊤) :
    Algebra.Smooth k (MvPolynomial σ k ⧸ Ideal.span {f}) := by
  let A := MvPolynomial σ k ⧸ Ideal.span {f}
  let π : MvPolynomial σ k →+* A := Ideal.Quotient.mk (Ideal.span {f})
  have hfp : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton f)
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_), hfp⟩
  obtain ⟨i, hi⟩ : ∃ i : σ, π (pderiv i f) ∉ q.asIdeal := by
    by_contra! hall
    have hle : Ideal.span (insert f (Set.range fun i => pderiv i f)) ≤
        q.asIdeal.comap π := by
      apply Ideal.span_le.mpr
      rintro x (hx | ⟨i, rfl⟩)
      · rw [hx]
        change π f ∈ q.asIdeal
        rw [show π f = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
        exact q.asIdeal.zero_mem
      · exact hall i
    exact (inferInstance : (q.asIdeal.comap π).IsPrime).ne_top (top_le_iff.mp (h ▸ hle))
  have := isStandardSmooth_away_hypersurface_pderiv f i
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr (by infer_instance) hi

/-- The affine hypersurface morphism has the expected relative dimension
when the affine Jacobian ideal is the unit ideal. -/
theorem smoothOfRelativeDimension_spec_hypersurface_of_span_eq_top
    {ι K : Type u} [CommRing K] [Fintype ι]
    {f : MvPolynomial ι K}
    (h : Ideal.span (insert f (Set.range fun i => pderiv i f)) = ⊤) :
    AlgebraicGeometry.SmoothOfRelativeDimension (Fintype.card ι - 1)
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap K (MvPolynomial ι K ⧸ Ideal.span {f})))) := by
  let A := MvPolynomial ι K ⧸ Ideal.span {f}
  let π : MvPolynomial ι K →+* A := Ideal.Quotient.mk (Ideal.span {f})
  let δ (i : ι) := π (pderiv i f)
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension (Fintype.card ι - 1))]
  refine ⟨Set.range δ, ?_, ?_⟩
  · have hm := congrArg (Ideal.map π) h
    have hzero : π f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    rw [Ideal.map_span, Set.image_insert_eq, ← Set.range_comp', hzero, Ideal.span_insert_zero,
      Ideal.map_top] at hm
    exact hm
  · rintro t ⟨i, rfl⟩
    change RingHom.IsStandardSmoothOfRelativeDimension _
      ((algebraMap A (Localization.Away (δ i))).comp (algebraMap K A))
    rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact isStandardSmoothOfRelativeDimension_away_hypersurface_pderiv f i

/-- The affine hypersurface Jacobian criterion with variables indexed by `Fin n`. -/
theorem smooth_quotient_of_span_eq_top {n : ℕ} {f : MvPolynomial (Fin n) k}
    (h : Ideal.span (insert f (Set.range fun i => pderiv i f)) = ⊤) :
    Algebra.Smooth k (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) :=
  smooth_quotient_of_span_eq_top_finite h

end

end Birch
