import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # The collision curves of the polynomial x^r - x -/

open MvPolynomial

namespace Birch

noncomputable section

variable {K : Type*} [Field K]

/-- The auxiliary one-variable phase used to distinguish singular level counts. -/
def morseAuxiliaryPolynomial (r : ℕ) : Polynomial K := Polynomial.X ^ r - Polynomial.X

/-- A two-variable difference of the auxiliary phase. -/
def morseAuxiliaryDifference (r : ℕ) : MvPolynomial (Fin 2) K :=
  (X 0 ^ r - X 0) - (X 1 ^ r - X 1)

/-- The homogeneous geometric sum in the residual collision curve. -/
def morseAuxiliaryResidualLeading (r : ℕ) : MvPolynomial (Fin 2) K :=
  ∑ j ∈ Finset.range r, X 0 ^ j * X 1 ^ (r - 1 - j)

@[simp] theorem map_morseAuxiliaryDifference {L : Type*} [Field L]
    (φ : K →+* L) (r : ℕ) :
    MvPolynomial.map φ (morseAuxiliaryDifference r) = morseAuxiliaryDifference r := by
  simp [morseAuxiliaryDifference, map_pow]

@[simp] theorem map_morseAuxiliaryResidualLeading {L : Type*} [Field L]
    (φ : K →+* L) (r : ℕ) :
    MvPolynomial.map φ (morseAuxiliaryResidualLeading r) = morseAuxiliaryResidualLeading r := by
  simp [morseAuxiliaryResidualLeading, map_pow]

@[simp] theorem eval_morseAuxiliaryPolynomial (r : ℕ) (x : K) :
    (morseAuxiliaryPolynomial r).eval x = x^r - x := by
  simp [morseAuxiliaryPolynomial]

@[simp] theorem eval_morseAuxiliaryDifference (r : ℕ) (x : Fin 2 → K) :
    (morseAuxiliaryDifference r).eval x =
      (morseAuxiliaryPolynomial r).eval (x 0) - (morseAuxiliaryPolynomial r).eval (x 1) := by
  simp [morseAuxiliaryDifference]

/-- The critical values are obtained from the roots of a univariate polynomial
of degree one less than the phase. -/
def morseAuxiliaryCriticalValues (r : ℕ) : Finset K := by
  classical
  exact ((Polynomial.X^(r-1) - Polynomial.C ((r : K)⁻¹)).roots.toFinset).image
    (morseAuxiliaryPolynomial r).eval

theorem card_morseAuxiliaryCriticalValues_le (r : ℕ) :
    (morseAuxiliaryCriticalValues (K := K) r).card ≤ r-1 := by
  classical
  unfold morseAuxiliaryCriticalValues
  refine Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans ?_)
  refine (Polynomial.card_roots' _).trans ?_
  exact (Polynomial.natDegree_sub_le _ _).trans (by simp)

/-- A point with zero first derivative has its value in the finite
critical-value set. -/
theorem eval_mem_morseAuxiliaryCriticalValues {r : ℕ} (hr : 2 ≤ r) (hrK : (r : K) ≠ 0)
    {x : K} (hx : (r : K) * x^(r-1) - 1 = 0) :
    (morseAuxiliaryPolynomial r).eval x ∈ morseAuxiliaryCriticalValues r := by
  classical
  unfold morseAuxiliaryCriticalValues
  refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots
    (Polynomial.X_pow_sub_C_ne_zero (by omega : 0 < r-1) _)]
  change Polynomial.eval x (Polynomial.X^(r-1) - Polynomial.C ((r : K)⁻¹)) = 0
  simp only [Polynomial.eval_sub, Polynomial.eval_X_pow, Polynomial.eval_C, sub_eq_zero]
  calc
    x^(r-1) = (r : K)⁻¹ * ((r : K) * x^(r-1)) := by rw [← mul_assoc, inv_mul_cancel₀ hrK, one_mul]
    _ = (r : K)⁻¹ := by rw [sub_eq_zero.mp hx, mul_one]

theorem pderiv_morseAuxiliaryDifference_zero (r : ℕ) :
    pderiv (0 : Fin 2) (morseAuxiliaryDifference r : MvPolynomial (Fin 2) K) =
      C (r : K) * X 0^(r-1) - 1 := by
  simp [morseAuxiliaryDifference, nsmul_eq_mul]

theorem pderiv_morseAuxiliaryDifference_one (r : ℕ) :
    pderiv (1 : Fin 2) (morseAuxiliaryDifference r : MvPolynomial (Fin 2) K) =
      - (C (r : K) * X 1^(r-1) - 1) := by
  simp [morseAuxiliaryDifference, nsmul_eq_mul]

/-- An affine critical value of the difference is a difference of two
critical values of the one-variable polynomial. -/
theorem criticalValue_morseAuxiliaryDifference {r : ℕ} (hr : 2 ≤ r) (hrK : (r : K) ≠ 0)
    (x : Fin 2 → K) (hx : ∀ i, (pderiv i (morseAuxiliaryDifference r)).eval x = 0) :
    ∃ u ∈ morseAuxiliaryCriticalValues (K := K) r,
      ∃ v ∈ morseAuxiliaryCriticalValues (K := K) r,
        (morseAuxiliaryDifference r).eval x = u - v := by
  refine ⟨_, eval_mem_morseAuxiliaryCriticalValues hr hrK ?_,
    _, eval_mem_morseAuxiliaryCriticalValues hr hrK ?_, eval_morseAuxiliaryDifference r x⟩
  · simpa only [pderiv_morseAuxiliaryDifference_zero, map_sub, map_one, map_mul, map_pow,
      eval_X, eval_C] using hx 0
  · simpa only [pderiv_morseAuxiliaryDifference_one, map_neg, neg_eq_zero, map_sub, map_one,
      map_mul, map_pow, eval_X, eval_C] using hx 1

theorem totalDegree_morseAuxiliaryDifference_le {r : ℕ} (hr : 2 ≤ r) :
    (morseAuxiliaryDifference r : MvPolynomial (Fin 2) K).totalDegree ≤ r := by
  have h (i : Fin 2) : (X i ^ r - X i : MvPolynomial (Fin 2) K).totalDegree ≤ r :=
    (totalDegree_sub _ _).trans (max_le (isHomogeneous_X_pow i r).totalDegree_le
      ((isHomogeneous_X K i).totalDegree_le.trans (by omega)))
  exact (totalDegree_sub _ _).trans (max_le (h 0) (h 1))

theorem homogeneousComponent_morseAuxiliaryDifference {r : ℕ} (hr : 2 ≤ r) :
    homogeneousComponent r (morseAuxiliaryDifference r : MvPolynomial (Fin 2) K) =
      X 0^r - X 1^r := by
  have hx (i : Fin 2) : homogeneousComponent r (X i : MvPolynomial (Fin 2) K) = 0 :=
    homogeneousComponent_eq_zero _ _ ((isHomogeneous_X K i).totalDegree_le.trans_lt (by omega))
  simp only [morseAuxiliaryDifference, map_sub, homogeneousComponent_eq_self
    (isHomogeneous_X_pow _ _), hx, sub_zero]

/-- The top degree part of the difference has only the origin as a critical point. -/
theorem eq_zero_of_critical_morseAuxiliaryLeading {r : ℕ} (hr : 2 ≤ r) (hrK : (r : K) ≠ 0)
    (x : Fin 2 → K) (hx : ∀ i, (pderiv i ((X 0^r - X 1^r) : MvPolynomial (Fin 2) K)).eval x = 0) :
    x = 0 := by
  have hpos : r-1 ≠ 0 := by omega
  have hx₀ : (r : K) * (x 0)^(r-1) = 0 := by
    simpa [pderiv_pow, nsmul_eq_mul] using hx 0
  have hx₁ : (r : K) * (x 1)^(r-1) = 0 := by
    simpa [pderiv_pow, nsmul_eq_mul] using hx 1
  funext i
  fin_cases i
  · exact (pow_eq_zero_iff hpos).mp ((mul_eq_zero.mp hx₀).resolve_left hrK)
  · exact (pow_eq_zero_iff hpos).mp ((mul_eq_zero.mp hx₁).resolve_left hrK)

/-- The residual collision polynomial is homogeneous of degree r−1
before subtracting its level. -/
theorem isHomogeneous_morseAuxiliaryResidualLeading (r : ℕ) :
    (morseAuxiliaryResidualLeading r : MvPolynomial (Fin 2) K).IsHomogeneous (r-1) := by
  apply IsHomogeneous.sum
  intro j hj
  have he : j + (r-1-j) = r-1 := by
    have := Finset.mem_range.mp hj
    omega
  simpa only [he] using ((isHomogeneous_X_pow (R := K) (0 : Fin 2) j).mul
    (isHomogeneous_X_pow (1 : Fin 2) (r-1-j)))

/-- The difference equation factors into the diagonal and the residual
collision curve. -/
theorem sub_mul_morseAuxiliaryResidualLeading (r : ℕ) :
    (X 0 - X 1 : MvPolynomial (Fin 2) K) * morseAuxiliaryResidualLeading r =
      X 0^r - X 1^r := by
  rw [mul_comm]
  exact geom_sum₂_mul _ _ r

/-- The leading form of the residual collision curve has only the origin as
a critical point. -/
theorem eq_zero_of_critical_morseAuxiliaryResidualLeading {r : ℕ} (hr : 2 ≤ r)
    (hrK : (r : K) ≠ 0) (hpK : ((r-1 : ℕ) : K) ≠ 0)
    (x : Fin 2 → K) (hx : ∀ i, (pderiv i (morseAuxiliaryResidualLeading r)).eval x = 0) :
    x = 0 := by
  have hQ : (morseAuxiliaryResidualLeading r).eval x = 0 := by
    have he := congrArg (eval x) (isHomogeneous_morseAuxiliaryResidualLeading (K := K) r).sum_X_mul_pderiv
    simp only [map_sum, map_mul, eval_X, hx, mul_zero, Finset.sum_const_zero, nsmul_eq_mul, map_natCast] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hpK
  apply eq_zero_of_critical_morseAuxiliaryLeading hr hrK x
  intro i
  rw [← sub_mul_morseAuxiliaryResidualLeading]
  simp [hQ, hx i]

/-- At level zero, the full collision locus is the union of the diagonal
and the level-one residual curve. -/
theorem eval_morseAuxiliaryDifference_eq_zero_iff (r : ℕ) (x : Fin 2 → K) :
    (morseAuxiliaryDifference r).eval x = 0 ↔
      x 0 = x 1 ∨ (morseAuxiliaryResidualLeading r).eval x = 1 := by
  have he : (morseAuxiliaryDifference r : MvPolynomial (Fin 2) K) =
      (X 0 - X 1) * (morseAuxiliaryResidualLeading r - 1) := by
    rw [mul_sub, sub_mul_morseAuxiliaryResidualLeading, mul_one]
    unfold morseAuxiliaryDifference
    ring
  rw [he, map_mul, map_sub, map_sub, eval_X, eval_X, map_one, mul_eq_zero]
  simp only [sub_eq_zero]

/-- On the diagonal, the residual equation is the critical-point equation. -/
theorem eval_morseAuxiliaryResidualLeading_diagonal (r : ℕ) (x : K) :
    (morseAuxiliaryResidualLeading r).eval (fun _ => x) = (r : K) * x^(r-1) := by
  simp only [morseAuxiliaryResidualLeading, map_sum, map_mul, map_pow, eval_X]
  exact geom_sum₂_self x r

end

end Birch
