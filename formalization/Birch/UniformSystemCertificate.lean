import Birch.UniformGradientCertificate

/-! # Uniform Macaulay tests for homogeneous equations -/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

private def universalHomogeneousSystem (l m e : ℕ) (j : Fin m) :
    MvPolynomial (Fin l) (MvPolynomial (Fin m × DegreeMonomial l e) ℤ) :=
  ∑ s : DegreeMonomial l e, monomial s.val (X (j,s))

private def universalHomogeneousTests (l m e N : ℕ) :
    Set (MvPolynomial (Fin m × DegreeMonomial l e) ℤ) :=
  let A := systemMacaulayMatrix (universalHomogeneousSystem l m e) e (N+(e+1))
  Set.range fun sel : DegreeMonomial l (N+(e+1)) → Fin m × DegreeMonomial l (N+(e+1)-e) =>
    (A.submatrix id sel).det

/-- For systems with a fixed number of homogeneous equations of fixed degree,
finitely many Macaulay tests detect the absence of nonzero common zeros over
every algebraically closed field. The cutoff is uniform in the coefficients
and in the characteristic. -/
theorem exists_uniform_system_macaulay_bound (l m e : ℕ) :
    ∃ B : ℕ, ∀ {K : Type*} [Field K] [IsAlgClosed K]
      (f : Fin m → MvPolynomial (Fin l) K), (∀ j, (f j).IsHomogeneous e) →
      ((∀ x : Fin l → K, (∀ j, (f j).eval x = 0) → x = 0) ↔
        ∃ N ≤ B, ∃ sel : DegreeMonomial l (N+(e+1)) → Fin m × DegreeMonomial l (N+(e+1)-e),
          ((systemMacaulayMatrix f e (N+(e+1))).submatrix id sel).det ≠ 0) := by
  classical
  obtain ⟨B,hB⟩ := exists_uniform_specialization_test_bound (universalHomogeneousTests l m e)
  refine ⟨B, ?_⟩
  intro K _ _ f hf
  constructor
  · intro hzero
    let R := MvPolynomial (Fin m × DegreeMonomial l e) ℤ
    let specialize : R →+* K := eval₂Hom (Int.castRingHom K) fun js => coeff js.2.val (f js.1)
    have hmap (j : Fin m) :
        MvPolynomial.map specialize (universalHomogeneousSystem l m e j) = f j := by
      calc
        _ = ∑ s : DegreeMonomial l e, monomial s.val (coeff s.val (f j)) := by
          rw [universalHomogeneousSystem, map_sum]
          apply Finset.sum_congr rfl
          intro s _
          rw [map_monomial]
          congr 1
          change eval₂ (Int.castRingHom K) (fun js : Fin m × DegreeMonomial l e =>
            coeff js.2.val (f js.1)) (X (j,s)) = coeff s.val (f j)
          exact eval₂_X _ _ _
        _ = _ := sum_degreeMonomial_eq (f j) (hf j)
    have heval {D : ℕ} (sel : DegreeMonomial l D → Fin m × DegreeMonomial l (D-e)) :
        specialize ((systemMacaulayMatrix (universalHomogeneousSystem l m e) e D).submatrix id sel).det =
          ((systemMacaulayMatrix f e D).submatrix id sel).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
        systemMacaulayMatrix_map]
      simp only [hmap]
    obtain ⟨D,_,hD,hcert⟩ := exists_monomial_certificate_degree (Ideal.span (Set.range f)) (e+1) (by
      intro x hx
      exact hzero x fun j => hx _ (Ideal.subset_span ⟨j,rfl⟩))
    let N := D-(e+1)
    have hND : N+(e+1) = D := Nat.sub_add_cancel hD
    have hspan := macaulay_span_of_system_monomials hf (D := N+(e+1)) (by omega)
      (fun s hs => hcert s (by omega))
    obtain ⟨sel,hsel⟩ := exists_system_macaulay_minor_of_span f e (N+(e+1)) hspan
    obtain ⟨N',hN',_,⟨sel',rfl⟩,hsel'⟩ := hB specialize
      ⟨N,_,⟨sel,rfl⟩,(heval sel).trans_ne hsel⟩
    exact ⟨N',hN',sel',(heval sel').symm.trans_ne hsel'⟩
  · rintro ⟨N,_,sel,hsel⟩ x hx
    exact zero_of_system_macaulay_minor hf (by omega) (by omega) sel hsel x hx

/-- A single degree suffices for the maximal-minor test, uniformly over all
algebraically closed fields and systems of the specified shape. -/
theorem exists_uniform_system_macaulay_degree (l m e : ℕ) :
    ∃ D : ℕ, e < D ∧ ∀ {K : Type*} [Field K] [IsAlgClosed K]
      (f : Fin m → MvPolynomial (Fin l) K), (∀ j, (f j).IsHomogeneous e) →
      ((∀ x : Fin l → K, (∀ j, (f j).eval x = 0) → x = 0) ↔
        ∃ sel : DegreeMonomial l D → Fin m × DegreeMonomial l (D-e),
          ((systemMacaulayMatrix f e D).submatrix id sel).det ≠ 0) := by
  obtain ⟨B, hB⟩ := exists_uniform_system_macaulay_bound l m e
  refine ⟨B+(e+1), by omega, ?_⟩
  intro K _ _ f hf
  constructor
  · intro hzero
    obtain ⟨N,hN,sel,hsel⟩ := (hB f hf).mp hzero
    have hmem {b : Fin l →₀ ℕ} (hb : b.degree = N+(e+1)) :=
      system_monomial_mem_of_macaulay_minor hf (by omega) sel hsel hb
    apply exists_system_macaulay_minor_of_span f e
    apply macaulay_span_of_system_monomials hf (by omega)
    intro b hb
    exact ideal_contains_monomials_of_degree_le (fun _ => hmem) (by omega)
  · rintro ⟨sel,hsel⟩ x hx
    exact zero_of_system_macaulay_minor hf (by omega) (by omega) sel hsel x hx

end
end Birch
