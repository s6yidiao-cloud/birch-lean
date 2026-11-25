import Birch.MvPolynomialCoefficientCompat
import Birch.UniversalSection
import Birch.UniformGradientCertificate
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Bounded smooth sections from Macaulay determinants
-/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

variable {n l D r p : ℕ}

/-- The parameter-degree bound for a determinant certifying a good section. -/
def sectionDiscriminantDegree (l r D : ℕ) : ℕ := r * Fintype.card (DegreeMonomial l D)

/-- Every square minor of the universal section matrix has bounded parameter degree. -/
theorem macaulayMinor_totalDegree_le {R : Type*} [CommRing R] {F : IntForm n}
    (hF : F.IsHomogeneous r)
    (select : DegreeMonomial l D → Fin l × DegreeMonomial l (D-(r-1))) :
    ((sectionMacaulayMatrix (universalLinearSection R F) r D).submatrix id select).det.totalDegree ≤
      sectionDiscriminantDegree l r D := by
  classical
  let M := (sectionMacaulayMatrix (universalLinearSection R F) r D).submatrix id select
  have hm (i j : DegreeMonomial l D) : (M i j).totalDegree ≤ r := by
    change (AddMonoidAlgebra.coeff (monomial (select j).2.val 1 *
      pderiv (select j).1 (universalLinearSection R F)) i.val).totalDegree ≤ r
    rw [coeff_monomial_mul', one_mul]
    split_ifs
    · exact coeff_pderiv_universalLinearSection_totalDegree_le R F hF _ _
    · rw [totalDegree_zero]
      exact Nat.zero_le _
  change M.det.totalDegree ≤ _
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro σ _
  refine (totalDegree_mul _ _).trans ?_
  have hε : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin l) R)).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial (Fin n × Fin l) R), totalDegree_C]
  rw [hε, zero_add]
  exact (totalDegree_finsetProd ..).trans ((Finset.sum_le_sum fun i _ => hm (σ i) i).trans_eq
    (by simp [sectionDiscriminantDegree, Nat.mul_comm]))

/-- Specialization of a universal section minor evaluates its parameters in the chosen matrix. -/
theorem eval₂_macaulayMinor {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (W : Matrix (Fin n) (Fin l) L) (G : IntForm n)
    (select : DegreeMonomial l D → Fin l × DegreeMonomial l (D-(r-1))) :
    eval₂ f (fun ij : Fin n × Fin l => W ij.1 ij.2)
      ((sectionMacaulayMatrix (universalLinearSection K G) r D).submatrix id select).det =
      ((sectionMacaulayMatrix (linearSectionOver W G) r D).submatrix id select).det := by
  let ev := eval₂Hom f (fun ij : Fin n × Fin l => W ij.1 ij.2)
  change ev _ = _
  rw [RingHom.map_det]
  change (((sectionMacaulayMatrix (universalLinearSection K G) r D).map ev).submatrix id select).det = _
  rw [sectionMacaulayMatrix_map, map_universalLinearSection]

/-- A single geometric matrix with a nonsingular Macaulay minor gives a
bounded integral matrix with the same geometric nonsingularity modulo p. -/
theorem exists_bounded_smooth_section_of_macaulay_minor [Fact p.Prime]
    {G : IntForm n} (hG : G.IsHomogeneous r) (hD : r-1 ≤ D) (hD₀ : 0 < D)
    (hp : sectionDiscriminantDegree l r D < p)
    (W : Matrix (Fin n) (Fin l) (AlgebraicClosure (ZMod p)))
    (select : DegreeMonomial l D → Fin l × DegreeMonomial l (D-(r-1)))
    (hW : ((sectionMacaulayMatrix (linearSectionOver W G) r D).submatrix id select).det ≠ 0) :
    ∃ U : Matrix (Fin n) (Fin l) ℤ, (∀ i j, |U i j| ≤ (sectionDiscriminantDegree l r D : ℤ)) ∧
      ∀ x : Fin l → AlgebraicClosure (ZMod p),
        (∀ j, evalForm (pderiv j (linearSection U G)) x = 0) → x = 0 := by
  classical
  let K := ZMod p
  let L := AlgebraicClosure K
  let M := (sectionMacaulayMatrix (universalLinearSection K G) r D).submatrix id select
  have spec (W' : Matrix (Fin n) (Fin l) L) := eval₂_macaulayMinor (algebraMap K L) W' G select
  have hM : M.det ≠ 0 := by
    intro hz
    apply hW
    rw [← spec W, hz, eval₂_zero]
  obtain ⟨z, hz, hz₀⟩ := exists_eval_ne_zero_small_grid hp M.det hM (macaulayMinor_totalDegree_le hG select)
  let U : Matrix (Fin n) (Fin l) ℤ := fun i j => z (i,j)
  refine ⟨U, fun i j => ?_, ?_⟩
  · change |(z (i,j) : ℤ)| ≤ _
    rw [Int.abs_natCast]
    exact_mod_cast hz (i,j)
  let U' := U.map (Int.castRingHom L)
  have hval : ((sectionMacaulayMatrix (linearSectionOver U' G) r D).submatrix id select).det ≠ 0 := by
    rw [← spec U']
    have he := (algebraMap K L).injective.ne hz₀
    rw [map_zero] at he
    change (algebraMap K L) (eval₂ (RingHom.id K) (fun ij => (z ij : K)) M.det) ≠ 0 at he
    rw [hom_eval₂] at he
    have hU' (ij : Fin n × Fin l) : U' ij.1 ij.2 = (z ij : L) := by
      obtain ⟨i, j⟩ := ij
      change (((z (i, j) : ℕ) : ℤ) : L) = (z (i, j) : L)
      exact Int.cast_natCast _
    simpa only [K, hU', RingHom.comp_id, map_natCast] using he
  intro x hx
  apply gradient_zero_of_macaulay_minor (isHomogeneous_linearSectionOver U' hG) hD hD₀ select hval x
  intro j
  rw [← map_linearSection U G, pderiv_map, eval_map]
  exact hx j

/-- An infinite field already has a smooth section if there is one over an
algebraically closed extension. -/
theorem exists_geometric_section_over_base {K L : Type*} [Field K] [Infinite K]
    [Field L] [IsAlgClosed L] [Algebra K L] {G : IntForm n} (hG : G.IsHomogeneous r)
    (W : Matrix (Fin n) (Fin l) L)
    (hW : ∀ x : Fin l → L, (∀ j, (pderiv j (linearSectionOver W G)).eval x = 0) → x = 0) :
    ∃ U : Matrix (Fin n) (Fin l) K,
      ∀ x : Fin l → K, (∀ j, (pderiv j (linearSectionOver U G)).eval x = 0) → x = 0 := by
  obtain ⟨D, hD₀, hD, hcert⟩ := exists_uniform_gradient_certificate_degree l r
  have hGW := isHomogeneous_linearSectionOver W hG
  have hspan := macaulay_span_of_gradient_monomials hGW hD (hcert hGW hW)
  obtain ⟨select, hselect⟩ := exists_macaulay_minor_of_span _ _ _ hspan
  let M := ((sectionMacaulayMatrix (universalLinearSection K G) r D).submatrix id select).det
  have hM : M ≠ 0 := by
    intro hz
    apply hselect
    rw [← eval₂_macaulayMinor (algebraMap K L) W G select]
    change eval₂ (algebraMap K L) (fun ij : Fin n × Fin l => W ij.1 ij.2) M = 0
    rw [hz, eval₂_zero]
  have hpoint : ∃ u : Fin n × Fin l → K, M.eval u ≠ 0 := by
    by_contra! h
    apply hM
    apply MvPolynomial.funext
    intro u
    rw [h, map_zero]
  obtain ⟨u, hu⟩ := hpoint
  let U : Matrix (Fin n) (Fin l) K := fun i j => u (i,j)
  have hspec := eval₂_macaulayMinor (RingHom.id K) U G select
  change M.eval u = _ at hspec
  exact ⟨U, gradient_zero_of_macaulay_minor (isHomogeneous_linearSectionOver U hG) hD hD₀
    select (hspec ▸ hu)⟩

/-- A geometric smooth section can be chosen on a bounded integral grid for
all sufficiently large primes. The bound depends only on the dimensions and
the degree, including when the form and its geometric witness vary. -/
theorem exists_uniform_bounded_smooth_section (n l r : ℕ) (hr : 2 ≤ r) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ (p : ℕ) [Fact p.Prime], B < p →
      ∀ (G : IntForm n), G.IsHomogeneous r →
      (∃ W : Matrix (Fin n) (Fin l) (AlgebraicClosure (ZMod p)),
        ∀ x : Fin l → AlgebraicClosure (ZMod p),
          (∀ j, (pderiv j (linearSectionOver W G)).eval x = 0) → x = 0) →
      ∃ U : Matrix (Fin n) (Fin l) ℤ, (∀ i j, |U i j| ≤ (B : ℤ)) ∧
        ∀ x : Fin l → AlgebraicClosure (ZMod p),
          (∀ j, evalForm (pderiv j (linearSection U G)) x = 0) → x = 0 := by
  obtain ⟨D, hD₀, hD, hcert⟩ := exists_uniform_gradient_certificate_degree l r
  let E := sectionDiscriminantDegree l r D
  refine ⟨max r E, (by omega : 1 ≤ r).trans (le_max_left _ _), ?_⟩
  intro p _ hp G hG hW
  obtain ⟨W, hs⟩ := hW
  have hGW := isHomogeneous_linearSectionOver W hG
  have hspan := macaulay_span_of_gradient_monomials hGW hD (hcert hGW hs)
  obtain ⟨select, hselect⟩ := exists_macaulay_minor_of_span _ _ _ hspan
  obtain ⟨U, hU, hgrad⟩ := exists_bounded_smooth_section_of_macaulay_minor hG hD hD₀
    ((le_max_right r E).trans_lt hp) W select hselect
  exact ⟨U, fun i j => (hU i j).trans (by exact_mod_cast le_max_right r E), hgrad⟩

end
end Birch
