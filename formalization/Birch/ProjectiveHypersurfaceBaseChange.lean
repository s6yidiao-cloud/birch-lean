module

public import Birch.ProjectiveHypersurfaceCoefficientChange
public import Birch.ProjectiveHypersurfaceChartCoordinates
public import Birch.ProjectiveHypersurfaceSmooth

@[expose] public section

/-! # Base change for projective hypersurfaces -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization
open scoped Graded

namespace Birch

noncomputable section

universe u

variable {σ k K : Type u} [CommRing k] [CommRing K] {d : ℕ} {F : MvPolynomial σ k}

attribute [local instance] MvPolynomial.gradedAlgebra

variable [DecidableEq σ]

private def pivotChartRingEquivAt (hF : F.IsHomogeneous d) (i : σ)
    {s : HypersurfaceRing F} (hs : s = hypersurfaceQuotientHom hF (X i)) :
    Away (hypersurfaceGrading F hF) s ≃+* HypersurfaceRing (pivotHypersurfacePolynomial i F) :=
  hypersurfaceChartEquivOfRename hF (Equiv.optionSubtypeNe i).symm i
    (Equiv.optionSubtypeNe_symm_self i) hs

private theorem pivotChartRingEquivAt_mk (hF : F.IsHomogeneous d) (i : σ)
    {s : HypersurfaceRing F} (hs : s = hypersurfaceQuotientHom hF (X i))
    (hs' : s ∈ hypersurfaceGrading F hF 1)
    (m : ℕ) (Q : MvPolynomial σ k) (hQ : Q.IsHomogeneous (m • (1 : ℕ))) :
    pivotChartRingEquivAt hF i hs
      (Away.mk _ hs' m (hypersurfaceQuotientHom hF Q) ((hypersurfaceQuotientHom hF).map_mem hQ)) =
        Ideal.Quotient.mk _ (pivotHypersurfacePolynomial i Q) :=
  hypersurfaceChartEquivOfRename_mk hF (Equiv.optionSubtypeNe i).symm i
    (Equiv.optionSubtypeNe_symm_self i) hs hs' m Q hQ

private theorem map_pivotHypersurfacePolynomial (φ : k →+* K) (i : σ)
    (Q : MvPolynomial σ k) :
    MvPolynomial.map φ (pivotHypersurfacePolynomial i Q) =
      pivotHypersurfacePolynomial i (MvPolynomial.map φ Q) := by
  rw [pivotHypersurfacePolynomial, pivotHypersurfacePolynomial, map_dehomogenize, map_rename]

private def chartCoefficientMapTo (φ : k →+* K) {τ : Type u}
    {P : MvPolynomial τ k} {Q : MvPolynomial τ K} (h : MvPolynomial.map φ P = Q) :
    HypersurfaceRing P →+* HypersurfaceRing Q :=
  Ideal.quotientMap _ (MvPolynomial.map φ) (by
    rw [Ideal.span_singleton_le_iff_mem]
    change MvPolynomial.map φ P ∈ Ideal.span {Q}
    rw [h]
    exact Ideal.mem_span_singleton_self Q)

private theorem isPushout_chartCoefficientMapTo (φ : k →+* K) {τ : Type u}
    {P : MvPolynomial τ k} {Q : MvPolynomial τ K} (h : MvPolynomial.map φ P = Q) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (algebraMap k (HypersurfaceRing P)))
      (CommRingCat.ofHom (algebraMap K (HypersurfaceRing Q)))
      (CommRingCat.ofHom (chartCoefficientMapTo φ h)) := by
  subst Q
  exact isPushout_hypersurfaceCoefficientMap φ P

private def pivotCoefficientMap (φ : k →+* K) (i : σ) (P : MvPolynomial σ k) :
    HypersurfaceRing (pivotHypersurfacePolynomial i P) →+*
      HypersurfaceRing (pivotHypersurfacePolynomial i (MvPolynomial.map φ P)) :=
  chartCoefficientMapTo φ (map_pivotHypersurfacePolynomial φ i P)

private theorem pivotCoefficientMap_mk (φ : k →+* K) (i : σ) (P : MvPolynomial σ k)
    (Q : MvPolynomial {j // j ≠ i} k) :
    pivotCoefficientMap φ i P (Ideal.Quotient.mk _ Q) =
      Ideal.Quotient.mk _ (MvPolynomial.map φ Q) := rfl

omit [DecidableEq σ] in
private theorem coefficientGradedMap_X (φ : k →+* K) (hF : F.IsHomogeneous d) (i : σ) :
    hypersurfaceCoefficientGradedMap φ hF (hypersurfaceQuotientHom hF (X i)) =
      hypersurfaceQuotientHom (hF.map φ) (X i) := by
  change hypersurfaceCoefficientMap φ F (Ideal.Quotient.mk _ (X i)) =
    Ideal.Quotient.mk _ (X i)
  rw [hypersurfaceCoefficientMap_mk, map_X]

private theorem pivotChartRingEquivAt_awayMap_coeff (φ : k →+* K)
    (hF : F.IsHomogeneous d) (i : σ)
    (z : Away (hypersurfaceGrading F hF) (hypersurfaceQuotientHom hF (X i))) :
    pivotChartRingEquivAt (hF.map φ) i (coefficientGradedMap_X φ hF i)
        (Away.map (hypersurfaceCoefficientGradedMap φ hF) (hypersurfaceQuotientHom hF (X i)) z) =
      pivotCoefficientMap φ i F (pivotChartRingEquivAt hF i rfl z) := by
  let π := hypersurfaceQuotientHom hF
  let ψ := hypersurfaceCoefficientGradedMap φ hF
  have hq : π (X i) ∈ hypersurfaceGrading F hF 1 := π.map_mem (isHomogeneous_X k i)
  obtain ⟨m,b,hb,rfl⟩ := Away.mk_surjective _ hq z
  obtain ⟨P,hP,hEq⟩ := hb
  change π P = b at hEq
  subst b
  have hP' : P.IsHomogeneous (m • (1 : ℕ)) := hP
  change pivotChartRingEquivAt (hF.map φ) i (coefficientGradedMap_X φ hF i)
       (Away.map ψ (π (X i)) (Away.mk _ hq m (π P) (π.map_mem hP'))) =
    pivotCoefficientMap φ i F (pivotChartRingEquivAt hF i rfl
      (Away.mk _ hq m (π P) (π.map_mem hP')))
  rw [Away.map_mk, pivotChartRingEquivAt_mk hF i rfl _ m P hP', pivotCoefficientMap_mk]
  change pivotChartRingEquivAt (hF.map φ) i (coefficientGradedMap_X φ hF i)
      (Away.mk _ (ψ.map_mem hq) m (hypersurfaceQuotientHom (hF.map φ) (MvPolynomial.map φ P))
        ((hypersurfaceQuotientHom (hF.map φ)).map_mem (hP'.map φ))) = _
  rw [pivotChartRingEquivAt_mk (hF.map φ) i (coefficientGradedMap_X φ hF i) _ m _ (hP'.map φ),
    map_pivotHypersurfacePolynomial]

private theorem pivotChartRingEquivAt_fromZeroRingHom {σ L : Type u}
    [CommRing L] [DecidableEq σ] {P : MvPolynomial σ L} (hP : P.IsHomogeneous d) (i : σ)
    {s : HypersurfaceRing P} (hs : s = hypersurfaceQuotientHom hP (X i)) (a : L) :
    pivotChartRingEquivAt hP i hs
      (fromZeroRingHom _ _ (hypersurfaceConstants hP a)) =
      algebraMap L (HypersurfaceRing (pivotHypersurfacePolynomial i P)) a := by
  subst s
  have hs' : hypersurfaceQuotientHom hP (X i) ∈ hypersurfaceGrading P hP 1 :=
    (hypersurfaceQuotientHom hP).map_mem (isHomogeneous_X L i)
  have hC : (C a : MvPolynomial σ L).IsHomogeneous (0 • (1 : ℕ)) := isHomogeneous_C σ a
  have he : (fromZeroRingHom _ _ (hypersurfaceConstants hP a) :
        Away (hypersurfaceGrading P hP) (hypersurfaceQuotientHom hP (X i))) =
      Away.mk _ hs' 0 (hypersurfaceQuotientHom hP (C a))
        ((hypersurfaceQuotientHom hP).map_mem hC) := by
    apply val_injective
    simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Away.val_mk, hypersurfaceConstants, pow_zero]
    rfl
  rw [he, pivotChartRingEquivAt_mk hP i rfl hs' 0 (C a) hC]
  change Ideal.Quotient.mk _ (dehomogenize (rename (Equiv.optionSubtypeNe i).symm (C a))) =
    Ideal.Quotient.mk _ (C a)
  rw [rename_C, dehomogenize_C]

private def pivotChartConstants {σ L : Type u} [CommRing L]
    {P : MvPolynomial σ L} (hP : P.IsHomogeneous d)
    (q : HypersurfaceRing P) : L →+* Away (hypersurfaceGrading P hP) q :=
  (fromZeroRingHom _ _).comp (hypersurfaceConstants hP)

private theorem isPushout_pivotChartOfCoefficientChange (φ : k →+* K)
    (hF : F.IsHomogeneous d) (i : σ) :
    let q := hypersurfaceQuotientHom hF (X i)
    let ψ := hypersurfaceCoefficientGradedMap φ hF
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (pivotChartConstants hF q))
      (CommRingCat.ofHom (pivotChartConstants (hF.map φ) (ψ q)))
      (CommRingCat.ofHom (Away.map ψ q)) := by
  let q := hypersurfaceQuotientHom hF (X i)
  let ψ := hypersurfaceCoefficientGradedMap φ hF
  let e₁ := pivotChartRingEquivAt hF i (rfl : q = _)
  let e₂ := pivotChartRingEquivAt (hF.map φ) i (coefficientGradedMap_X φ hF i)
  have hp := isPushout_chartCoefficientMapTo φ (map_pivotHypersurfacePolynomial φ i F)
  refine hp.of_iso (.refl _) (.refl _) e₁.symm.toCommRingCatIso e₂.symm.toCommRingCatIso
    (by simp) ?_ ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change e₁.symm (algebraMap _ _ a) = fromZeroRingHom _ _ (hypersurfaceConstants hF a)
    apply e₁.injective
    rw [e₁.apply_symm_apply]
    exact (pivotChartRingEquivAt_fromZeroRingHom hF i rfl a).symm
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change e₂.symm (algebraMap _ _ a) = fromZeroRingHom _ _ (hypersurfaceConstants (hF.map φ) a)
    apply e₂.injective
    rw [e₂.apply_symm_apply]
    exact (pivotChartRingEquivAt_fromZeroRingHom (hF.map φ) i
      (coefficientGradedMap_X φ hF i) a).symm
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change e₂.symm (pivotCoefficientMap φ i F a) = Away.map ψ q (e₁.symm a)
    apply e₂.injective
    rw [e₂.apply_symm_apply]
    have he := pivotChartRingEquivAt_awayMap_coeff φ hF i (e₁.symm a)
    change e₂ (Away.map ψ q (e₁.symm a)) = pivotCoefficientMap φ i F (e₁ (e₁.symm a)) at he
    rw [e₁.apply_symm_apply] at he
    exact he.symm

private theorem awayι_comp_projectiveHypersurfaceToField {σ L : Type u} [CommRing L]
    {P : MvPolynomial σ L} (hP : P.IsHomogeneous d) {q : HypersurfaceRing P}
    (hq : q ∈ hypersurfaceGrading P hP 1) :
    Proj.awayι (hypersurfaceGrading P hP) q hq Nat.one_pos ≫
      projectiveHypersurfaceToField hP =
        Spec.map (CommRingCat.ofHom (pivotChartConstants hP q)) := by
  rw [projectiveHypersurfaceToField, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- The homogeneous quotient model commutes with scheme base change along
a ring homomorphism. The comparison is the pullback of its structure morphism. -/
theorem isPullback_projectiveHypersurfaceCoefficientMap (φ : k →+* K)
    (hF : F.IsHomogeneous d) :
    IsPullback (projectiveHypersurfaceCoefficientMap φ hF)
      (projectiveHypersurfaceToField (hF.map φ)) (projectiveHypersurfaceToField hF)
      (Spec.map (CommRingCat.ofHom φ)) := by
  let q (i : σ) := hypersurfaceQuotientHom hF (X i)
  let ψ := hypersurfaceCoefficientGradedMap φ hF
  have hψ := hypersurfaceCoefficientGradedMap_irrelevant φ hF
  have hq (i : σ) : q i ∈ hypersurfaceGrading F hF 1 :=
    (hypersurfaceQuotientHom hF).map_mem (isHomogeneous_X k i)
  let 𝒰 := (Proj.affineOpenCoverOfIrrelevantLESpan (hypersurfaceGrading F hF)
    q hq (fun _ => Nat.one_pos) (irrelevant_hypersurface_le_span_coordinates hF)).openCover
  refine Scheme.isPullback_of_openCover _ _ _ _ 𝒰 ?_
  intro i
  change σ at i
  let P := Proj.awayι (hypersurfaceGrading F hF) (q i) (hq i) Nat.one_pos
  let Q := Proj.awayι (hypersurfaceGrading _ (hF.map φ)) (ψ (q i)) (ψ.map_mem (hq i)) Nat.one_pos
  let b := Spec.map (CommRingCat.ofHom (Away.map ψ (q i)))
  have hc : IsPullback Q b (projectiveHypersurfaceCoefficientMap φ hF) P :=
    (isPullback_proj_awayι_map ψ hψ Nat.one_pos (q i) (hq i)).flip
  have hp : IsPullback b (Q ≫ projectiveHypersurfaceToField (hF.map φ))
      (P ≫ projectiveHypersurfaceToField hF) (Spec.map (CommRingCat.ofHom φ)) := by
    change IsPullback b (Proj.awayι _ _ (ψ.map_mem (hq i)) Nat.one_pos ≫ _)
      (Proj.awayι _ _ (hq i) Nat.one_pos ≫ _) _
    rw [awayι_comp_projectiveHypersurfaceToField, awayι_comp_projectiveHypersurfaceToField]
    exact (isPushout_pivotChartOfCoefficientChange φ hF i).op.map Scheme.Spec
  refine hp.of_iso hc.isoPullback (.refl _) (.refl _) (.refl _) ?_ ?_ ?_ (by simp)
  · change b ≫ 𝟙 _ = hc.isoPullback.hom ≫ pullback.snd _ P
    rw [Category.comp_id]
    exact hc.isoPullback_hom_snd.symm
  · change (Q ≫ projectiveHypersurfaceToField (hF.map φ)) ≫ 𝟙 _ =
      hc.isoPullback.hom ≫ pullback.fst _ P ≫ projectiveHypersurfaceToField (hF.map φ)
    rw [Category.comp_id, hc.isoPullback_hom_fst_assoc]
  · change (P ≫ projectiveHypersurfaceToField hF) ≫ 𝟙 _ =
      𝟙 _ ≫ P ≫ projectiveHypersurfaceToField hF
    simp

end
end Birch
