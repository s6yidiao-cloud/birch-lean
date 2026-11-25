module

public import Birch.MvPolynomialCoefficientCompat

public import Birch.UniformGradientCertificate
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

/-! # Smooth homogeneous pencils over a principal open -/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

/-- The determinant of a square Macaulay submatrix times any degree-`D`
monomial belongs to the ideal of its equations, over any coefficient ring. -/
theorem system_monomial_det_mem_of_macaulay_minor {l q e D : ℕ}
    {R : Type*} [CommRing R]
    {g : Fin q → MvPolynomial (Fin l) R} (hg : ∀ j, (g j).IsHomogeneous e) (hD : e ≤ D)
    (sel : DegreeMonomial l D → Fin q × DegreeMonomial l (D-e))
    {m : Fin l →₀ ℕ} (hm : m.degree = D) :
    monomial m ((systemMacaulayMatrix g e D).submatrix id sel).det ∈
      Ideal.span (Set.range g) := by
  classical
  let m₀ : DegreeMonomial l D := ⟨m,hm⟩
  let J := Ideal.span (Set.range g)
  let A := (systemMacaulayMatrix g e D).submatrix id sel
  let c := A.adjugate *ᵥ Pi.single m₀ (1 : R)
  have hc : A *ᵥ c = A.det • Pi.single m₀ 1 := by
    dsimp only [c]
    rw [mulVec_mulVec, Matrix.mul_adjugate, smul_mulVec, one_mulVec]
  let f : MvPolynomial (Fin l) R := ∑ t : DegreeMonomial l D,
    c t • (monomial (sel t).2.val (1 : R) * g (sel t).1)
  have hf : f.IsHomogeneous D := by
    apply IsHomogeneous.sum
    intro t _
    have h := (isHomogeneous_monomial (1 : R) (sel t).2.prop).mul (hg (sel t).1)
    rw [Nat.sub_add_cancel hD] at h
    exact (homogeneousSubmodule (Fin l) R D).smul_mem (c t) h
  have hJ : f ∈ J := by
    apply Ideal.sum_mem
    intro t _
    rw [smul_eq_C_mul]
    exact J.mul_mem_left _ (J.mul_mem_left _ (Ideal.subset_span ⟨(sel t).1,rfl⟩))
  have he : f = monomial m A.det := by
    ext u
    by_cases hu : u.degree = D
    · let u₀ : DegreeMonomial l D := ⟨u,hu⟩
      have H := congrFun hc u₀
      have htest : u₀ = m₀ ↔ m = u :=
        ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
      simp only [A, f, mulVec, dotProduct, submatrix_apply, id_eq,
        systemMacaulayMatrix, coeff_sum, coeff_smul, smul_eq_mul, Pi.smul_apply,
        Pi.single_apply, htest, u₀, m₀, coeff_monomial] at H ⊢
      by_cases hmu : m = u
      · simpa only [ite_eq_left hmu, mul_one, one_mul, mul_comm] using H
      · simpa only [ite_eq_right hmu, mul_zero, zero_mul, mul_comm] using H
    · have hz : coeff u f = 0 := by
        by_contra hne
        apply hu
        simpa only [Finsupp.degree_apply] using
          (hf.degree_eq_sum_deg_support (mem_support_iff.mpr hne)).symm
      change AddMonoidAlgebra.coeff f u = 0 at hz
      rw [hz, coeff_monomial, ite_eq_right (fun h : m = u => hu (h ▸ hm))]
  exact he ▸ hJ

/-- The gradient version of the determinant certificate. -/
theorem gradient_monomial_det_mem_of_macaulay_minor {l r D : ℕ}
    {R : Type*} [CommRing R] {G : MvPolynomial (Fin l) R}
    (hG : G.IsHomogeneous r) (hD : r-1 ≤ D)
    (sel : DegreeMonomial l D → Fin l × DegreeMonomial l (D-(r-1)))
    {m : Fin l →₀ ℕ} (hm : m.degree = D) :
    monomial m ((sectionMacaulayMatrix G r D).submatrix id sel).det ∈
      Ideal.span (Set.range fun j : Fin l => pderiv j G) :=
  system_monomial_det_mem_of_macaulay_minor (fun _ => hG.pderiv) hD sel hm

/-- The pencil with value `F` at zero and `G` at one. -/
def projectivePolynomialPencil {σ k : Type*} [CommRing k]
    (F G : MvPolynomial σ k) : MvPolynomial σ (Polynomial k) :=
  C (1-Polynomial.X) * MvPolynomial.map Polynomial.C F +
    C Polynomial.X * MvPolynomial.map Polynomial.C G

/-- A pencil of homogeneous forms is homogeneous over the parameter ring. -/
theorem isHomogeneous_projectivePolynomialPencil {σ k : Type*} [CommRing k]
    {F G : MvPolynomial σ k} {r : ℕ} (hF : F.IsHomogeneous r) (hG : G.IsHomogeneous r) :
    (projectivePolynomialPencil F G).IsHomogeneous r := by
  unfold projectivePolynomialPencil
  exact ((hF.map _).C_mul _).add ((hG.map _).C_mul _)

/-- Specialization of the coefficients evaluates the pencil parameter. -/
theorem map_projectivePolynomialPencil {σ k K : Type*} [CommRing k] [CommRing K]
    (F G : MvPolynomial σ k) (ρ : k →+* K) (t : K) :
    MvPolynomial.map (Polynomial.eval₂RingHom ρ t) (projectivePolynomialPencil F G) =
      C (1-t) * MvPolynomial.map ρ F + C t * MvPolynomial.map ρ G := by
  have h : (Polynomial.eval₂RingHom ρ t).comp Polynomial.C = ρ :=
    RingHom.ext fun _ => Polynomial.eval₂_C _ _
  simp only [projectivePolynomialPencil, map_add, map_mul, map_C, MvPolynomial.map_map,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_X,
    h]

private abbrev pencilMinor {n r D : ℕ} {R : Type*} [CommRing R]
    (F : MvPolynomial (Fin n) R)
    (sel : DegreeMonomial n D → Fin n × DegreeMonomial n (D-(r-1))) : R :=
  ((sectionMacaulayMatrix F r D).submatrix id sel).det

private theorem map_pencilMinor {n r D : ℕ} {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (F : MvPolynomial (Fin n) R)
    (sel : DegreeMonomial n D → Fin n × DegreeMonomial n (D-(r-1))) :
    φ (pencilMinor F sel) = pencilMinor (MvPolynomial.map φ F) sel := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, sectionMacaulayMatrix_map]

/-- The homogeneous equation over the principal localization of the
parameter line. -/
def localizedProjectivePolynomialPencil {σ k : Type*} [CommRing k]
    (F G : MvPolynomial σ k) (h : Polynomial k) : MvPolynomial σ (Localization.Away h) :=
  MvPolynomial.map (algebraMap (Polynomial k) (Localization.Away h)) (projectivePolynomialPencil F G)

/-- Evaluation at a point of the principal open. -/
def pencilParameterSpecialization {k K : Type*} [CommRing k] [Field K]
    (ρ : k →+* K) (h : Polynomial k) (t : K) (ht : h.eval₂ ρ t ≠ 0) :
    Localization.Away h →+* K :=
  IsLocalization.Away.lift h (g := Polynomial.eval₂RingHom ρ t) (isUnit_iff_ne_zero.mpr ht)

/-- Every evaluation of the localized pencil is the corresponding linear
combination of its endpoints. -/
theorem map_localizedProjectivePolynomialPencil {σ k K : Type*} [CommRing k] [Field K]
    (F G : MvPolynomial σ k) (ρ : k →+* K) (h : Polynomial k) (t : K)
    (ht : h.eval₂ ρ t ≠ 0) :
    MvPolynomial.map (pencilParameterSpecialization ρ h t ht) (localizedProjectivePolynomialPencil F G h) =
      C (1-t) * MvPolynomial.map ρ F + C t * MvPolynomial.map ρ G := by
  have hcomp : (pencilParameterSpecialization ρ h t ht).comp
      (algebraMap (Polynomial k) (Localization.Away h)) = Polynomial.eval₂RingHom ρ t :=
    RingHom.ext (fun x => IsLocalization.Away.lift_eq h (isUnit_iff_ne_zero.mpr ht) x)
  rw [localizedProjectivePolynomialPencil, MvPolynomial.map_map, hcomp]
  exact map_projectivePolynomialPencil F G ρ t

private theorem exists_macaulay_minor_of_geo_isolated {k : Type*} [Field k] {n r D : ℕ}
    {F : MvPolynomial (Fin n) k} (hF : F.IsHomogeneous r)
    (hD : r-1 ≤ D) (hmem : ∀ m : Fin n →₀ ℕ, m.degree = D →
       monomial m (1 : AlgebraicClosure k) ∈ Ideal.span (Set.range fun j : Fin n =>
        pderiv j (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) F))) :
    ∃ sel : DegreeMonomial n D → Fin n × DegreeMonomial n (D-(r-1)), pencilMinor F sel ≠ 0 := by
  let φ := algebraMap k (AlgebraicClosure k)
  obtain ⟨sel,hsel⟩ := exists_macaulay_minor_of_span (MvPolynomial.map φ F) r D
    (macaulay_span_of_gradient_monomials (hF.map φ) hD hmem)
  refine ⟨sel, fun hz => hsel ?_⟩
  change pencilMinor (MvPolynomial.map φ F) sel = 0
  rw [← map_pencilMinor, hz, map_zero]

/-- Smooth homogeneous endpoints give a principal open containing both
parameters on which all degree-`D` monomials belong to the gradient
ideal of the localized pencil. The certificate is over its actual
parameter ring, before any specialization to a field. -/
theorem exists_localizedPencil_gradient_certificate {n r : ℕ} {k : Type*} [Field k]
    {F G : MvPolynomial (Fin n) k} (hF : F.IsHomogeneous r) (hG : G.IsHomogeneous r)
    (hFcrit : ∀ x : Fin n → AlgebraicClosure k,
      (∀ i, (pderiv i F).eval₂ (algebraMap k (AlgebraicClosure k)) x = 0) → x = 0)
    (hGcrit : ∀ x : Fin n → AlgebraicClosure k,
      (∀ i, (pderiv i G).eval₂ (algebraMap k (AlgebraicClosure k)) x = 0) → x = 0) :
    ∃ h : Polynomial k, h.eval 0 ≠ 0 ∧ h.eval 1 ≠ 0 ∧ ∃ D : ℕ, 0 < D ∧ r-1 ≤ D ∧
      ∀ m : Fin n →₀ ℕ, m.degree = D →
        monomial m (1 : Localization.Away h) ∈ Ideal.span
          (Set.range fun j : Fin n => pderiv j (localizedProjectivePolynomialPencil F G h)) := by
  classical
  let φ := algebraMap k (AlgebraicClosure k)
  obtain ⟨D,hD₀,hD,hcert⟩ := exists_uniform_gradient_certificate_degree n r
  have hFm := hcert (hF.map φ) (fun x hx => hFcrit x (fun i => by
    simpa only [pderiv_map, eval_map] using hx i))
  have hGm := hcert (hG.map φ) (fun x hx => hGcrit x (fun i => by
    simpa only [pderiv_map, eval_map] using hx i))
  obtain ⟨s₀,hs₀⟩ := exists_macaulay_minor_of_geo_isolated hF hD hFm
  obtain ⟨s₁,hs₁⟩ := exists_macaulay_minor_of_geo_isolated hG hD hGm
  let P := projectivePolynomialPencil F G
  let h := (1-Polynomial.X) * pencilMinor P s₀ + Polynomial.X * pencilMinor P s₁
  have he (t : k) (s : DegreeMonomial n D → Fin n × DegreeMonomial n (D-(r-1))) :
      (pencilMinor P s).eval t =
        pencilMinor (C (1-t) * F + C t * G) s := by
    change (Polynomial.eval₂RingHom (RingHom.id k) t) (pencilMinor P s) = _
    rw [map_pencilMinor, show P = projectivePolynomialPencil F G from rfl,
      map_projectivePolynomialPencil]
    simp only [MvPolynomial.map_id]
  have h₀ : h.eval 0 ≠ 0 := by
    simpa only [h, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X, sub_zero, one_mul, zero_mul, add_zero,
      he, C_0, C_1, zero_mul, one_mul] using hs₀
  have h₁ : h.eval 1 ≠ 0 := by
    simpa only [h, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_X, sub_self, one_mul, zero_mul, zero_add,
      he, C_0, C_1, zero_mul, one_mul] using hs₁
  refine ⟨h,h₀,h₁,D,hD₀,hD,?_⟩
  intro m hm
  let R := Localization.Away h
  let ρ := algebraMap (Polynomial k) R
  let P' := localizedProjectivePolynomialPencil F G h
  let J := Ideal.span (Set.range fun j : Fin n => pderiv j P')
  have hP : P'.IsHomogeneous r := (isHomogeneous_projectivePolynomialPencil hF hG).map ρ
  have H (s : DegreeMonomial n D → Fin n × DegreeMonomial n (D-(r-1))) :
      monomial m (ρ (pencilMinor P s)) ∈ J := by
    rw [map_pencilMinor]
    exact gradient_monomial_det_mem_of_macaulay_minor hP hD s hm
  have hsum := J.add_mem
    (J.mul_mem_left (C (ρ (1-Polynomial.X))) (H s₀))
    (J.mul_mem_left (C (ρ Polynomial.X)) (H s₁))
  have hsum' : C (ρ h) * monomial m (1 : R) ∈ J := by
    rw [← smul_eq_C_mul, smul_monomial, smul_eq_mul, mul_one]
    change monomial m (ρ ((1-Polynomial.X) * pencilMinor P s₀ + Polynomial.X * pencilMinor P s₁)) ∈ J
    rw [map_add, map_mul, map_mul, map_add (monomial m)]
    simpa only [← smul_eq_C_mul, smul_monomial, smul_eq_mul] using hsum
  have hu : IsUnit (C (σ := Fin n) (ρ h)) := (IsLocalization.Away.algebraMap_isUnit h).map C
  obtain ⟨u,hu⟩ := hu
  rw [← hu] at hsum'
  have hinv := J.mul_mem_left (↑u⁻¹ : MvPolynomial (Fin n) R) hsum'
  simpa [← mul_assoc] using hinv

/-- The two original equations are the fibers at zero and one. -/
theorem localizedProjectivePolynomialPencil_endpoints {σ k : Type*} [Field k]
    (F G : MvPolynomial σ k) (h : Polynomial k)
    (h₀ : h.eval 0 ≠ 0) (h₁ : h.eval 1 ≠ 0) :
    MvPolynomial.map (pencilParameterSpecialization (RingHom.id k) h 0 h₀)
      (localizedProjectivePolynomialPencil F G h) = F ∧
    MvPolynomial.map (pencilParameterSpecialization (RingHom.id k) h 1 h₁)
      (localizedProjectivePolynomialPencil F G h) = G := by
  change h.eval₂ (RingHom.id k) 0 ≠ 0 at h₀
  change h.eval₂ (RingHom.id k) 1 ≠ 0 at h₁
  constructor
  · rw [map_localizedProjectivePolynomialPencil]
    simp [MvPolynomial.map_id]
  · rw [map_localizedProjectivePolynomialPencil]
    simp [MvPolynomial.map_id]

/-- A uniform coordinate-power certificate over the coefficient ring
rules out every nonzero gradient zero in every field-valued fiber. -/
theorem eq_zero_of_gradient_coordinate_power_certificate {σ R K : Type*}
    [CommRing R] [Field K] (φ : R →+* K) {P : MvPolynomial σ R}
    {D : ℕ} (hD : 0 < D)
    (hP : ∀ i, X i ^ D ∈ Ideal.span (Set.range fun j : σ => pderiv j P))
    (x : σ → K) (hx : ∀ i, (pderiv i P).eval₂ φ x = 0) : x = 0 := by
  have hker : Ideal.span (Set.range fun j : σ => pderiv j P) ≤ RingHom.ker (eval₂Hom φ x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hx i
  funext i
  have hz : (eval₂Hom φ x) (X i ^ D) = 0 := hker (hP i)
  rw [map_pow, eval₂Hom_X'] at hz
  exact (pow_eq_zero_iff hD.ne').mp hz

/-- The homogeneous pencil over a principal open containing both endpoints
has a uniform coordinate-power certificate, and each field fiber has no
nonzero geometric critical point. -/
theorem exists_localizedPencil_smooth_fibers {n r : ℕ} {k : Type*} [Field k]
    {F G : MvPolynomial (Fin n) k} (hF : F.IsHomogeneous r) (hG : G.IsHomogeneous r)
    (hFcrit : ∀ x : Fin n → AlgebraicClosure k,
      (∀ i, (pderiv i F).eval₂ (algebraMap k (AlgebraicClosure k)) x = 0) → x = 0)
    (hGcrit : ∀ x : Fin n → AlgebraicClosure k,
      (∀ i, (pderiv i G).eval₂ (algebraMap k (AlgebraicClosure k)) x = 0) → x = 0) :
    ∃ h : Polynomial k, h.eval 0 ≠ 0 ∧ h.eval 1 ≠ 0 ∧
      let P := localizedProjectivePolynomialPencil F G h
      P.IsHomogeneous r ∧ (∃ D : ℕ, 0 < D ∧
        ∀ i, X i ^ D ∈ Ideal.span (Set.range fun j : Fin n => pderiv j P)) ∧
      ∀ (K : Type*) [Field K] (φ : Localization.Away h →+* K) (x : Fin n → K),
        (∀ i, (pderiv i P).eval₂ φ x = 0) → x = 0 := by
  obtain ⟨h,h₀,h₁,D,hD,_,hcert⟩ := exists_localizedPencil_gradient_certificate hF hG hFcrit hGcrit
  have hpow (i : Fin n) : X i ^ D ∈
      Ideal.span (Set.range fun j : Fin n => pderiv j (localizedProjectivePolynomialPencil F G h)) := by
    rw [X_pow_eq_monomial]
    exact hcert (Finsupp.single i D) (Finsupp.degree_single i D)
  exact ⟨h,h₀,h₁,(isHomogeneous_projectivePolynomialPencil hF hG).map _,
    ⟨D,hD,hpow⟩,fun _ _ φ x hx => eq_zero_of_gradient_coordinate_power_certificate φ hD hpow x hx⟩

end
end Birch
