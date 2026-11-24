import Birch.Geometry
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Polynomial identities for dilated differences

Introduce one polynomial parameter for the size of the translation. Its constant term
is the original polynomial, and its linear coefficient is the directional derivative.
Dividing by the parameter before specializing preserves integrality for every dilation.
-/

open scoped BigOperators
open MvPolynomial

namespace Birch

noncomputable section

variable {n : ℕ}

private def parametricShift (u : Fin n → ℤ) : IntForm n →ₐ[ℤ] MvPolynomial (Option (Fin n)) ℤ :=
  aeval (fun j ↦ X (some j) + C (u j) * X none)

/-- The polynomial in the shift parameter whose value at `m` is the translate by `m u`. -/
def shiftPolynomial (u : Fin n → ℤ) : IntForm n →ₐ[ℤ] Polynomial (IntForm n) :=
  (optionEquivLeft ℤ (Fin n)).toAlgHom.comp (parametricShift u)

/-- The usual directional derivative with integer coefficients. -/
def directionalDerivative (u : Fin n → ℤ) (F : IntForm n) : IntForm n :=
  ∑ i, C (u i) * pderiv i F

/-- The divided difference defined over the integers, including a specialization at zero. -/
def dilatedDifference (m : ℤ) (u : Fin n → ℤ) (F : IntForm n) : IntForm n :=
  ((shiftPolynomial u F).divX).eval (C m)

@[simp] private theorem shiftPolynomial_X (u : Fin n → ℤ) (i : Fin n) :
    shiftPolynomial u (X i) = Polynomial.C (X i) + Polynomial.C (C (u i)) * Polynomial.X := by
  simp [shiftPolynomial, parametricShift]

@[simp] private theorem shiftPolynomial_C (u : Fin n → ℤ) (a : ℤ) :
    shiftPolynomial u (C a) = Polynomial.C (C a) := by
  simp [shiftPolynomial, parametricShift]

private theorem shiftPolynomial_zeroCoeff (u : Fin n → ℤ) (F : IntForm n) :
    (shiftPolynomial u F).coeff 0 = F := by
  have h : Polynomial.constantCoeff.comp (shiftPolynomial u).toRingHom = RingHom.id (IntForm n) := by
    ext a i <;> simp
  exact congrFun (congrArg DFunLike.coe h) F

private theorem directionalDerivative_mul (u : Fin n → ℤ) (F G : IntForm n) :
    directionalDerivative u (F * G) =
      F * directionalDerivative u G + directionalDerivative u F * G := by
  unfold directionalDerivative
  simp only [Derivation.leibniz, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem shiftPolynomial_linearCoeff (u : Fin n → ℤ) (F : IntForm n) :
    (shiftPolynomial u F).coeff 1 = directionalDerivative u F := by
  induction F using MvPolynomial.induction_on with
  | C a =>
      rw [shiftPolynomial_C, Polynomial.coeff_C_of_ne_zero (by decide : (1 : ℕ) ≠ 0)]
      simp [directionalDerivative]
  | add F G hF hG =>
      simp [hF, hG, directionalDerivative, mul_add, Finset.sum_add_distrib] at *
  | mul_X F i hF =>
      have hdirX : directionalDerivative u (X i) = C (u i) := by
        classical
        simp [directionalDerivative, pderiv_X, Pi.single_apply, mul_ite]
      rw [map_mul, Polynomial.mul_coeff_one, shiftPolynomial_zeroCoeff, hF,
        directionalDerivative_mul, hdirX, shiftPolynomial_zeroCoeff, shiftPolynomial_X]
      simp

/-- The divided difference multiplied by the dilation equals the original translated
difference. This identity holds before reduction in any residue ring. -/
theorem mul_dilatedDifference (m : ℤ) (u : Fin n → ℤ) (F : IntForm n) :
    C m * dilatedDifference m u F = aeval (fun i ↦ X i + C (m * u i)) F - F := by
  let ev := Polynomial.evalRingHom (C m : IntForm n)
  have hshift : ev.comp (shiftPolynomial u).toRingHom =
      (aeval (R := ℤ) (fun i ↦ X i + C (m * u i))).toRingHom := by
    ext a i <;> simp [ev, map_mul, mul_comm]
  have heval : (shiftPolynomial u F).eval (C m) = aeval (fun i ↦ X i + C (m * u i)) F :=
    congrFun (congrArg DFunLike.coe hshift) F
  have hdiv := congrArg ev (Polynomial.X_mul_divX_add (shiftPolynomial u F))
  simp only [map_add, map_mul] at hdiv
  change Polynomial.eval (C m) Polynomial.X * (shiftPolynomial u F).divX.eval (C m) +
    Polynomial.eval (C m) (Polynomial.C ((shiftPolynomial u F).coeff 0)) =
    (shiftPolynomial u F).eval (C m) at hdiv
  rwa [Polynomial.eval_X, Polynomial.eval_C, heval, shiftPolynomial_zeroCoeff,
    ← eq_sub_iff_add_eq] at hdiv

/-- The linear shift coefficient is the specialization of the divided difference at zero. -/
theorem dilatedDifference_zero (u : Fin n → ℤ) (F : IntForm n) :
    dilatedDifference 0 u F = directionalDerivative u F := by
  simpa only [dilatedDifference, map_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX,
    zero_add] using
    shiftPolynomial_linearCoeff u F

private theorem parametricShift_totalDegree_le (u : Fin n → ℤ) (F : IntForm n) :
    (parametricShift u F).totalDegree ≤ F.totalDegree := by
  simp only [parametricShift, aeval_def, eval₂_eq, algebraMap_eq]
  apply totalDegree_finsetSum_le
  intro s hs
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd ..).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans ?_).trans (le_totalDegree hs)
  have hdeg : (X (some i) + C (u i) * X none).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_X]
    · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
  simpa only [mul_one] using Nat.mul_le_mul_left (s i) hdeg

private theorem shiftPolynomial_coeff_totalDegree_le (u : Fin n → ℤ) (F : IntForm n)
    (j : ℕ) : ((shiftPolynomial u F).coeff j).totalDegree ≤ F.totalDegree - j := by
  let f := parametricShift u F
  have hf : f.totalDegree ≤ F.totalDegree := parametricShift_totalDegree_le u F
  change ((optionEquivLeft ℤ (Fin n) f).coeff j).totalDegree ≤ F.totalDegree - j
  by_cases hj : j ≤ f.totalDegree
  · have H := totalDegree_coeff_optionEquivLeft_add_le ℤ (Fin n) f j hj
    omega
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt, totalDegree_zero]
    · exact Nat.zero_le _
    · rw [natDegree_optionEquivLeft]
      exact (degreeOf_le_totalDegree f none).trans_lt (Nat.lt_of_not_ge hj)

private theorem eval_shiftQuotient_totalDegree_le (u : Fin n → ℤ) (F : IntForm n)
    (p : Polynomial (IntForm n)) (m : ℤ) (k : ℕ)
    (hcoeff : ∀ j, p.coeff j = (shiftPolynomial u F).coeff (j + k)) :
    (p.eval (C m)).totalDegree ≤ F.totalDegree - k := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply totalDegree_finsetSum_le
  intro j _
  refine (totalDegree_mul _ _).trans ?_
  have hpow : ((C m : IntForm n) ^ j).totalDegree = 0 := by
    rw [← map_pow, totalDegree_C]
  rw [hpow, add_zero, hcoeff]
  exact (shiftPolynomial_coeff_totalDegree_le u F (j + k)).trans
    (Nat.sub_le_sub_left (Nat.le_add_left k j) _)

/-- The integer divided difference lowers total degree by at least one. -/
theorem dilatedDifference_totalDegree_le (m : ℤ) (u : Fin n → ℤ) (F : IntForm n) :
    (dilatedDifference m u F).totalDegree ≤ F.totalDegree - 1 :=
  eval_shiftQuotient_totalDegree_le u F _ m 1 (fun j ↦ Polynomial.coeff_divX (n := j))

private theorem homogeneousComponent_directionalDerivative (u : Fin n → ℤ)
    (F : IntForm n) (d : ℕ) :
    homogeneousComponent d (directionalDerivative u F) =
      directionalDerivative u (homogeneousComponent (d + 1) F) := by
  unfold directionalDerivative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [homogeneousComponent_C_mul]
  congr 1
  ext s
  rw [coeff_homogeneousComponent, coeff_pderiv, coeff_pderiv, coeff_homogeneousComponent]
  have hdeg : (s + Finsupp.single i 1).degree = s.degree + 1 := by simp
  simp only [hdeg, Nat.add_right_cancel_iff]
  split_ifs <;> simp

/-- The leading part of a dilated difference depends only on the original leading
part and the direction. In particular this identity is valid modulo primes
dividing the dilation. -/
theorem homogeneousComponent_dilatedDifference (m : ℤ) (u : Fin n → ℤ)
    (F : IntForm n) {d : ℕ} (hd : 2 ≤ d) (hF : F.totalDegree ≤ d) :
    homogeneousComponent (d - 1) (dilatedDifference m u F) =
      directionalDerivative u (homogeneousComponent d F) := by
  let p := (shiftPolynomial u F).divX
  let v := p.divX.eval (C m)
  have hdeg : v.totalDegree ≤ F.totalDegree - 2 := by
    apply eval_shiftQuotient_totalDegree_le u F _ m 2
    intro j
    simp [p, Polynomial.coeff_divX, Nat.add_assoc]
  have hdiff : dilatedDifference m u F = C m * v + directionalDerivative u F := by
    have H := congrArg (Polynomial.evalRingHom (C m : IntForm n)) (Polynomial.X_mul_divX_add p)
    simp only [map_add, map_mul] at H
    change Polynomial.eval (C m) Polynomial.X * v +
      (Polynomial.C (p.coeff 0)).eval (C m) = dilatedDifference m u F at H
    rw [Polynomial.eval_X, Polynomial.eval_C, show p.coeff 0 = (shiftPolynomial u F).coeff 1 by
      simp [p], shiftPolynomial_linearCoeff] at H
    exact H.symm
  have hlt : (C m * v).totalDegree < d - 1 := by
    refine (totalDegree_mul _ _).trans_lt ?_
    rw [totalDegree_C, zero_add]
    omega
  rw [hdiff, map_add, homogeneousComponent_eq_zero _ _ hlt, zero_add,
    homogeneousComponent_directionalDerivative, Nat.sub_add_cancel (by omega : 1 ≤ d)]

end
end Birch
