module

public import Birch.ProjectiveSmoothPencil
public import Birch.ProjectiveHypersurfaceBaseChange

@[expose] public section

/-! # The smooth proper scheme of a homogeneous pencil -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace Birch

private theorem exists_isPullback_projectiveHypersurface_of_map_eq {R K : Type}
    [CommRing R] [CommRing K] {n r : ℕ}
    {P : MvPolynomial (Fin n) R} {F : MvPolynomial (Fin n) K}
    (φ : R →+* K) (hP : P.IsHomogeneous r) (hF : F.IsHomogeneous r)
    (hEq : map φ P = F) :
    ∃ j : projectiveHypersurface hF ⟶ projectiveHypersurface hP,
      IsPullback j (projectiveHypersurfaceToField hF)
        (projectiveHypersurfaceToField hP) (Spec.map (CommRingCat.ofHom φ)) := by
  subst F
  exact ⟨_, isPullback_projectiveHypersurfaceCoefficientMap φ hP⟩

/-- Extending the coefficient field of a pencil endpoint gives the fiber at
the composed parameter specialization. -/
noncomputable def pullbackIso_of_projectivePencilEndpoint {R k K : Type}
    [CommRing R] [Field k] [Field K] {X Y : Scheme}
    {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of k)} {j : Y ⟶ X}
    (ε : R →+* k) (φ : k →+* K)
    (hj : IsPullback j g f (Spec.map (CommRingCat.ofHom ε))) :
    pullback g (Spec.map (CommRingCat.ofHom φ)) ≅
      pullback f (Spec.map (CommRingCat.ofHom (φ.comp ε))) := by
  have h := (IsPullback.of_hasPullback g (Spec.map (CommRingCat.ofHom φ))).paste_horiz hj
  rw [← Spec.map_comp] at h
  exact h.isoPullback

/-- Two geometrically noncritical homogeneous equations of the same positive
degree occur as the endpoints of a single smooth proper hypersurface family
over an integral principal open in the parameter line. -/
theorem exists_smoothProperProjectivePencil {k : Type} [Field k] {n r : ℕ}
    {F G : MvPolynomial (Fin n) k} (hr : 0 < r)
    (hF : F.IsHomogeneous r) (hG : G.IsHomogeneous r)
    (hFcrit : ∀ x : Fin n → AlgebraicClosure k,
      (∀ i, (pderiv i F).eval₂ (algebraMap k (AlgebraicClosure k)) x = 0) → x = 0)
    (hGcrit : ∀ x : Fin n → AlgebraicClosure k,
      (∀ i, (pderiv i G).eval₂ (algebraMap k (AlgebraicClosure k)) x = 0) → x = 0) :
    ∃ (h : Polynomial k) (h₀ : h.eval 0 ≠ 0) (h₁ : h.eval 1 ≠ 0),
      IsDomain (Localization.Away h) ∧
      ∃ hp : (localizedProjectivePolynomialPencil F G h).IsHomogeneous r,
      let f := projectiveHypersurfaceToField hp
      let e₀ := pencilParameterSpecialization (RingHom.id k) h 0 h₀
      let e₁ := pencilParameterSpecialization (RingHom.id k) h 1 h₁
      IsProper f ∧ SmoothOfRelativeDimension (n-2) f ∧
        (∃ j : projectiveHypersurface hF ⟶ projectiveHypersurface hp,
          IsPullback j (projectiveHypersurfaceToField hF) f (Spec.map (CommRingCat.ofHom e₀))) ∧
        (∃ j : projectiveHypersurface hG ⟶ projectiveHypersurface hp,
          IsPullback j (projectiveHypersurfaceToField hG) f (Spec.map (CommRingCat.ofHom e₁))) := by
  obtain ⟨h, h₀, h₁, hP, ⟨D, _, hpow⟩, _⟩ :=
    exists_localizedPencil_smooth_fibers.{0, 0} hF hG hFcrit hGcrit
  have hne : h ≠ 0 := fun hzero => h₀ (by simp [hzero])
  refine ⟨h,h₀,h₁,Localization.Away.isDomain hne,hP,
    isProper_projectiveHypersurfaceToField hP hr,?_,?_,?_⟩
  · have H := smoothOfRelativeDimension_projectiveHypersurfaceToField hP
      (fun i => ⟨D, Ideal.span_mono (Set.subset_insert _ _) (hpow i)⟩)
    simpa only [Fintype.card_fin] using H
  · exact exists_isPullback_projectiveHypersurface_of_map_eq _ hP hF
      (localizedProjectivePolynomialPencil_endpoints F G h h₀ h₁).1
  · exact exists_isPullback_projectiveHypersurface_of_map_eq _ hP hG
      (localizedProjectivePolynomialPencil_endpoints F G h h₀ h₁).2

end Birch
