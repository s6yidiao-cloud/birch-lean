import Birch.GradientIdealCertificate
import Birch.MacaulayMatrix
import Mathlib.RingTheory.Polynomial.Basic

/-! # Uniform homogeneous gradient certificates -/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

/-- Monomial membership in the ideal of a system supplies all the standard
basis columns as linear combinations of Macaulay columns. -/
theorem macaulay_span_of_system_monomials {l m e D : ℕ} {K : Type*} [Field K]
    {f : Fin m → MvPolynomial (Fin l) K} (hf : ∀ j, (f j).IsHomogeneous e) (hD : e ≤ D)
    (hmem : ∀ s : Fin l →₀ ℕ, s.degree = D → monomial s (1 : K) ∈ Ideal.span (Set.range f)) :
    ⊤ ≤ Submodule.span K (Set.range (systemMacaulayMatrix f e D).col) := by
  classical
  let M := systemMacaulayMatrix f e D
  let W := Submodule.span K (Set.range M.col)
  have hbasis (b : DegreeMonomial l D) : Pi.single b (1 : K) ∈ W := by
    obtain ⟨c, hcH, hc⟩ :=
      (homogeneous_monomial_mem_span_iff f hf b.prop hD).mp (hmem b.val b.prop)
    have hsum (j : Fin m) :
        (∑ t : DegreeMonomial l (D-e),
          coeff t.val (c j) • (monomial t.val (1 : K) * f j)) = c j * f j := by
      conv_rhs => rw [← sum_degreeMonomial_eq (c j) (hcH j), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
    have he : (∑ j : Fin m, ∑ t : DegreeMonomial l (D-e),
        coeff t.val (c j) • (monomial t.val (1 : K) * f j)) = monomial b.val 1 := by
      simp only [hsum, hc]
    have hvec : (∑ j : Fin m, ∑ t : DegreeMonomial l (D-e),
        coeff t.val (c j) • M.col (j,t)) = Pi.single b 1 := by
      ext x
      have h := congrArg (coeff x.val) he
      have hx : b.val = x.val ↔ x = b :=
        ⟨fun h => Subtype.ext h.symm, fun h => congrArg Subtype.val h.symm⟩
      simpa only [coeff_sum, coeff_smul, smul_eq_mul, coeff_monomial, Pi.single_apply,
        Finset.sum_apply, Pi.smul_apply, hx, M, systemMacaulayMatrix, Matrix.col_apply]
        using h
    rw [← hvec]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.sum_mem _ fun t _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j,t),rfl⟩)
  change ⊤ ≤ W
  rw [← (Pi.basisFun K (DegreeMonomial l D)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨m,rfl⟩
  simpa using hbasis m

/-- Monomial membership in a gradient ideal gives full Macaulay row rank. -/
theorem macaulay_span_of_gradient_monomials {l r D : ℕ} {K : Type*} [Field K]
    {G : MvPolynomial (Fin l) K} (hG : G.IsHomogeneous r) (hD : r-1 ≤ D)
    (hmem : ∀ m : Fin l →₀ ℕ, m.degree = D →
      monomial m (1 : K) ∈ Ideal.span (Set.range fun j : Fin l => pderiv j G)) :
    ⊤ ≤ Submodule.span K (Set.range (sectionMacaulayMatrix G r D).col) :=
  macaulay_span_of_system_monomials (fun _ => hG.pderiv) hD hmem

/-- A nonsingular maximal minor already certifies monomial membership
in its own degree, with no further increase in degree. -/
theorem system_monomial_mem_of_macaulay_minor {l q e D : ℕ} {K : Type*} [Field K]
    {g : Fin q → MvPolynomial (Fin l) K} (hg : ∀ j, (g j).IsHomogeneous e) (hD : e ≤ D)
    (sel : DegreeMonomial l D → Fin q × DegreeMonomial l (D-e))
    (hsel : ((systemMacaulayMatrix g e D).submatrix id sel).det ≠ 0)
    {m : Fin l →₀ ℕ} (hm : m.degree = D) :
    monomial m (1 : K) ∈ Ideal.span (Set.range g) := by
  classical
  let m₀ : DegreeMonomial l D := ⟨m,hm⟩
  let J := Ideal.span (Set.range g)
  let A := (systemMacaulayMatrix g e D).submatrix id sel
  let c := A⁻¹ *ᵥ Pi.single m₀ (1 : K)
  have hc : A *ᵥ c = Pi.single m₀ 1 := by
    dsimp only [c]
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hsel), one_mulVec]
  let f : MvPolynomial (Fin l) K := ∑ t : DegreeMonomial l D,
    c t • (monomial (sel t).2.val (1 : K) * g (sel t).1)
  have hf : f.IsHomogeneous D := by
    apply IsHomogeneous.sum
    intro t _
    have h := (isHomogeneous_monomial (1 : K) (sel t).2.prop).mul
      (hg (sel t).1)
    rw [Nat.sub_add_cancel hD] at h
    exact (homogeneousSubmodule (Fin l) K D).smul_mem (c t) h
  have hJ : f ∈ J := by
    apply Ideal.sum_mem
    intro t _
    rw [smul_eq_C_mul]
    exact J.mul_mem_left _ (J.mul_mem_left _ (Ideal.subset_span ⟨(sel t).1,rfl⟩))
  have he : f = monomial m (1 : K) := by
    ext u
    by_cases hu : u.degree = D
    · let u₀ : DegreeMonomial l D := ⟨u,hu⟩
      have H := congrFun hc u₀
      have htest : u₀ = m₀ ↔ m = u :=
        ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
      simpa only [A, f, mulVec, dotProduct, submatrix_apply, id_eq,
        systemMacaulayMatrix, coeff_sum, coeff_smul, smul_eq_mul, mul_comm,
        Pi.single_apply, htest, u₀, m₀, coeff_monomial] using H
    · have hz : coeff u f = 0 := by
        by_contra hne
        apply hu
        simpa only [Finsupp.degree_apply] using
          (hf.degree_eq_sum_deg_support (mem_support_iff.mpr hne)).symm
      rw [hz, coeff_monomial, if_neg (fun h : m = u => hu (h ▸ hm))]
  exact he ▸ hJ

/-- A nonsingular maximal minor certifies monomial membership in a gradient ideal. -/
theorem gradient_monomial_mem_of_macaulay_minor {l r D : ℕ} {K : Type*} [Field K]
    {G : MvPolynomial (Fin l) K} (hG : G.IsHomogeneous r) (hD : r-1 ≤ D)
    (sel : DegreeMonomial l D → Fin l × DegreeMonomial l (D-(r-1)))
    (hsel : ((sectionMacaulayMatrix G r D).submatrix id sel).det ≠ 0)
    {m : Fin l →₀ ℕ} (hm : m.degree = D) :
    monomial m (1 : K) ∈ Ideal.span (Set.range fun j : Fin l => pderiv j G) :=
  system_monomial_mem_of_macaulay_minor (fun _ => hG.pderiv) hD sel hsel hm

private def universalGradientForm (l r : ℕ) :
    MvPolynomial (Fin l) (MvPolynomial (DegreeMonomial l r) ℤ) :=
  ∑ m : DegreeMonomial l r, monomial m.val (X m)

private def gradientCoefficientSpecialization {l r : ℕ} {K : Type*} [Field K]
    (G : MvPolynomial (Fin l) K) : MvPolynomial (DegreeMonomial l r) ℤ →+* K :=
  eval₂Hom (Int.castRingHom K) fun m => coeff m.val G

private theorem map_universalGradientForm {l r : ℕ} {K : Type*} [Field K]
    {G : MvPolynomial (Fin l) K} (hG : G.IsHomogeneous r) :
    MvPolynomial.map (gradientCoefficientSpecialization (r := r) G) (universalGradientForm l r) = G := by
  simpa only [universalGradientForm, map_sum, map_monomial, gradientCoefficientSpecialization,
    coe_eval₂Hom, eval₂_X] using sum_degreeMonomial_eq G hG

private def universalGradientTests (l r N : ℕ) :
    Set (MvPolynomial (DegreeMonomial l r) ℤ) :=
  Set.range fun sel : DegreeMonomial l N → Fin l × DegreeMonomial l (N-(r-1)) =>
    ((sectionMacaulayMatrix (universalGradientForm l r) r N).submatrix id sel).det

private theorem evaluate_universalGradientTest {l r N : ℕ} {K : Type*} [Field K]
    {G : MvPolynomial (Fin l) K} (hG : G.IsHomogeneous r)
    (sel : DegreeMonomial l N → Fin l × DegreeMonomial l (N-(r-1))) :
    gradientCoefficientSpecialization (r := r) G
      ((sectionMacaulayMatrix (universalGradientForm l r) r N).submatrix id sel).det =
        ((sectionMacaulayMatrix G r N).submatrix id sel).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    sectionMacaulayMatrix_map, map_universalGradientForm hG]

/-- The certificate degree depends only on the number of variables and
the homogeneous degree, uniformly in the algebraically closed field. -/
theorem exists_uniform_gradient_certificate_degree (l r : ℕ) :
    ∃ D : ℕ, 0 < D ∧ r-1 ≤ D ∧
      ∀ {K : Type*} [Field K] [IsAlgClosed K] {G : MvPolynomial (Fin l) K},
      G.IsHomogeneous r →
      (∀ x : Fin l → K, (∀ j, (pderiv j G).eval x = 0) → x = 0) →
      ∀ m : Fin l →₀ ℕ, m.degree = D →
        monomial m (1 : K) ∈ Ideal.span (Set.range fun j : Fin l => pderiv j G) := by
  classical
  obtain ⟨D₀,hD₀⟩ := exists_uniform_specialization_test_bound
    (fun N => universalGradientTests l r (N+(r-1)))
  let D := D₀+r+1
  refine ⟨D, by dsimp [D]; omega, by dsimp [D]; omega, ?_⟩
  intro K _ _ G hG hs
  obtain ⟨N,_,hN,hspan⟩ := exists_gradient_certificate_degree (r := r) hs
  obtain ⟨sel,hsel⟩ := exists_macaulay_minor_of_span G r N <|
    macaulay_span_of_gradient_monomials hG hN (fun m hm => hspan m (le_of_eq hm.symm))
  let F := universalGradientForm l r
  let φ := gradientCoefficientSpecialization (r := r) G
  have hf : ∃ N' b, b ∈ universalGradientTests l r (N'+(r-1)) ∧ φ b ≠ 0 := by
    let b := ((sectionMacaulayMatrix F r N).submatrix id sel).det
    refine ⟨N-(r-1), b, ?_, ?_⟩
    · rw [Nat.sub_add_cancel hN]
      exact ⟨sel,rfl⟩
    · rw [show φ b = _ from evaluate_universalGradientTest hG sel]
      exact hsel
  obtain ⟨N',hN',b,⟨sel',rfl⟩,hb⟩ := hD₀ φ hf
  rw [show φ _ = _ from evaluate_universalGradientTest hG sel'] at hb
  have hcomp : r-1 ≤ N'+(r-1) := Nat.le_add_left _ _
  have hs' (m : Fin l →₀ ℕ) (hm : m.degree = N'+(r-1)) :=
    gradient_monomial_mem_of_macaulay_minor hG hcomp sel' hb hm
  intro m hm
  apply ideal_contains_monomials_of_degree_le hs'
  rw [hm]
  dsimp [D]
  omega

end
end Birch
