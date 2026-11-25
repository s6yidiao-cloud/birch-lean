module

public import Birch.ProjectiveHypersurfaceRenaming
public import Birch.ProjectiveHypersurfaceBoundary
public import Birch.AffineHypersurfaceSmooth
public import Birch.HomogeneousDehomogenization
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

/-! # The Jacobian criterion on projective hypersurfaces -/

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ K : Type u} [CommRing K] {d : ℕ} {F : MvPolynomial σ K}

set_option maxHeartbeats 1000000 in
/-- The opens with one invertible coordinate cover the hypersurface. -/
theorem iSup_basicOpen_hypersurface_eq_top (hF : F.IsHomogeneous d) :
    (⨆ i : σ, Proj.basicOpen (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X i))) = ⊤ := by
  let π := Ideal.Quotient.mkₐ K (Ideal.span {F})
  let x : σ → HypersurfaceRing F := fun i => π (X i)
  let B := ↥(hypersurfaceGrading F hF 0)
  let : Algebra K B := (hypersurfaceConstants hF).toAlgebra
  let : IsScalarTower K B (HypersurfaceRing F) := IsScalarTower.of_algebraMap_eq' rfl
  have hK : Algebra.adjoin K (Set.range x) = ⊤ := by
    change Algebra.adjoin K (Set.range (π ∘ X)) = ⊤
    rw [Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  have hB : Algebra.adjoin B (Set.range x) = ⊤ := by
    have hs : Algebra.adjoin K (Set.range x) ≤
        (Algebra.adjoin B (Set.range x)).restrictScalars K :=
      Algebra.adjoin_le (fun _ hx => Algebra.subset_adjoin hx)
    apply top_unique
    intro a _
    exact hs (by rw [hK]; trivial)
  exact Proj.iSup_basicOpen_eq_top' _ x (fun i =>
    ⟨1,⟨X i,isHomogeneous_X K i,rfl⟩⟩) hB

variable [DecidableEq σ]

/-- Affine polynomial in the chart with coordinate `i` normalized to one. -/
abbrev pivotHypersurfacePolynomial (i : σ) (F : MvPolynomial σ K) :
    MvPolynomial {j // j ≠ i} K :=
  dehomogenize (rename (Equiv.optionSubtypeNe i).symm F)

/-- Standard affine chart of the projective hypersurface at coordinate `i`. -/
def pivotHypersurfaceChartι (hF : F.IsHomogeneous d) (i : σ) :
    Spec (.of (MvPolynomial {j // j ≠ i} K ⧸ Ideal.span {pivotHypersurfacePolynomial i F})) ⟶
      projectiveHypersurface hF :=
  standardHypersurfaceChartι (hF.rename_isHomogeneous (f := ⇑(Equiv.optionSubtypeNe i).symm)) ≫
    (projectiveHypersurfaceRenameIso hF (Equiv.optionSubtypeNe i).symm).hom

instance (hF : F.IsHomogeneous d) (i : σ) : IsOpenImmersion (pivotHypersurfaceChartι hF i) := by
  unfold pivotHypersurfaceChartι
  exact IsOpenImmersion.comp _ _

@[reassoc] theorem pivotHypersurfaceChartι_toField (hF : F.IsHomogeneous d) (i : σ) :
    pivotHypersurfaceChartι hF i ≫ projectiveHypersurfaceToField hF =
      Spec.map (CommRingCat.ofHom (algebraMap K
        (MvPolynomial {j // j ≠ i} K ⧸ Ideal.span {pivotHypersurfacePolynomial i F}))) := by
  rw [pivotHypersurfaceChartι, Category.assoc, projectiveHypersurfaceRenameIso_hom_toField,
    standardHypersurfaceChartι_toField]

omit [DecidableEq σ] in
private theorem projectiveHypersurfaceRenameIso_inv_hom_apply (hF : F.IsHomogeneous d)
    {τ : Type u} (e : σ ≃ τ) (x : projectiveHypersurface hF) :
    (projectiveHypersurfaceRenameIso hF e).hom ((projectiveHypersurfaceRenameIso hF e).inv x) = x := by
  have h := congrArg (fun f : projectiveHypersurface hF ⟶ projectiveHypersurface hF => f x)
    (projectiveHypersurfaceRenameIso hF e).inv_hom_id
  rw [Scheme.Hom.comp_apply] at h
  exact h

theorem opensRange_pivotHypersurfaceChartι (hF : F.IsHomogeneous d) (i : σ) :
    (pivotHypersurfaceChartι hF i).opensRange =
      Proj.basicOpen (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X i)) := by
  let e := (Equiv.optionSubtypeNe i).symm
  have hG : (rename e F).IsHomogeneous d := hF.rename_isHomogeneous
  let j := standardHypersurfaceChartι hG
  let s := projectiveHypersurfaceRenameIso hF e
  let U := Proj.basicOpen (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X i))
  have hpre : s.hom ⁻¹ᵁ U = j.opensRange := by
    change Proj.map (hypersurfaceRenameGradedHom hF e) _ ⁻¹ᵁ
      Proj.basicOpen (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X i)) = _
    rw [Proj.map_preimage_basicOpen, opensRange_standardHypersurfaceChartι]
    have heq : hypersurfaceRenameGradedHom hF e (hypersurfaceQuotientHom hF (X i)) =
        hypersurfaceQuotientHom hG (X none) := by
      change hypersurfaceRenameRingEquiv e (Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _ (X none)
      rw [hypersurfaceRenameRingEquiv_apply_mk, rename_X, show e i = none from Equiv.optionSubtypeNe_symm_self i]
    rw [heq]
  ext x
  change x ∈ Set.range (j ≫ s.hom) ↔ x ∈ U
  constructor
  · rintro ⟨y,rfl⟩
    change j y ∈ s.hom ⁻¹ᵁ U
    rw [hpre]
    exact ⟨y,rfl⟩
  · intro hx
    let y := s.inv x
    have hy : s.hom y = x := projectiveHypersurfaceRenameIso_inv_hom_apply hF e x
    have hy' : y ∈ s.hom ⁻¹ᵁ U := by
      change s.hom y ∈ U
      rwa [hy]
    rw [hpre] at hy'
    obtain ⟨z,hz⟩ := hy'
    exact ⟨z,by rw [Scheme.Hom.comp_apply, hz, hy]⟩

private def pivotHypersurfaceCover (hF : F.IsHomogeneous d) :
    (projectiveHypersurface hF).OpenCover :=
    Scheme.Cover.mkOfCovers σ
      (fun i => Spec (.of (MvPolynomial {j // j ≠ i} K ⧸ Ideal.span {pivotHypersurfacePolynomial i F})))
      (pivotHypersurfaceChartι hF)
      (fun x => by
        have htop := iSup_basicOpen_hypersurface_eq_top hF
        have hmem : x ∈ ⨆ i : σ, Proj.basicOpen (hypersurfaceGrading F hF)
            (hypersurfaceQuotientHom hF (X i)) := by rw [htop]; trivial
        obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
        rw [← opensRange_pivotHypersurfaceChartι hF] at hi
        obtain ⟨y,hy⟩ := hi
        exact ⟨i,y,hy⟩)

/-- A projective Jacobian certificate gives a smooth morphism on the
actual projective hypersurface scheme. -/
theorem smooth_projectiveHypersurfaceToField [Finite σ] (hF : F.IsHomogeneous d)
    (hjac : ∀ i : σ, ∃ N : ℕ,
      X i ^ N ∈ Ideal.span (insert F (Set.range fun j : σ => pderiv j F))) :
    Smooth (projectiveHypersurfaceToField hF) := by
  let : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u})
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) (pivotHypersurfaceCover hF) fun i => ?_
  change σ at i
  change Smooth (pivotHypersurfaceChartι hF i ≫ projectiveHypersurfaceToField hF)
  rw [pivotHypersurfaceChartι_toField, HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap K (MvPolynomial {j // j ≠ i} K ⧸ Ideal.span {pivotHypersurfacePolynomial i F})).Smooth
  rw [RingHom.smooth_algebraMap]
  exact smooth_quotient_of_span_eq_top_finite (span_dehomogenize_rename_eq_top i hF (hjac i))

/-- The same Jacobian criterion gives the expected relative dimension. -/
theorem smoothOfRelativeDimension_projectiveHypersurfaceToField [Fintype σ]
    (hF : F.IsHomogeneous d)
    (hjac : ∀ i : σ, ∃ N : ℕ,
      X i ^ N ∈ Ideal.span (insert F (Set.range fun j : σ => pderiv j F))) :
    SmoothOfRelativeDimension (Fintype.card σ - 2) (projectiveHypersurfaceToField hF) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} (Fintype.card σ - 2)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @SmoothOfRelativeDimension.{u} (Fintype.card σ - 2))
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{u} (Fintype.card σ - 2))
    (pivotHypersurfaceCover hF) fun i => ?_
  change σ at i
  change SmoothOfRelativeDimension (Fintype.card σ - 2)
    (pivotHypersurfaceChartι hF i ≫ projectiveHypersurfaceToField hF)
  have hc := Fintype.card_congr (Equiv.optionSubtypeNe i)
  rw [Fintype.card_option] at hc
  rw [pivotHypersurfaceChartι_toField, ← show Fintype.card {j : σ // j ≠ i} - 1 =
    Fintype.card σ - 2 by omega]
  exact smoothOfRelativeDimension_spec_hypersurface_of_span_eq_top
    (span_dehomogenize_rename_eq_top i hF (hjac i))

end
end Birch
