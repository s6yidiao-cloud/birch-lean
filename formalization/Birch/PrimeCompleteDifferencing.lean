import Birch.CompleteSums
import Birch.DilatedDifference

/-!
# Differencing complete sums over a residue ring

For the normalized complete sums, the squared norm is bounded by the
average of the norms of the complete sums of the translated differences.
-/

namespace Birch

open MvPolynomial ZMod
open scoped BigOperators ComplexConjugate

noncomputable section

variable {n p : ℕ} [NeZero p]

/-- The coordinatewise integer lift with representatives in `[0, p)`. -/
def residueVectorIntRep (h : Fin n → ZMod p) : Fin n → ℤ :=
  fun i => (h i).val

@[simp] theorem cast_residueVectorIntRep (h : Fin n → ZMod p) (i : Fin n) :
    (residueVectorIntRep h i : ZMod p) = h i := by
  simp only [residueVectorIntRep, Int.cast_natCast, ZMod.natCast_zmod_val]

/-- Reducing the integral difference gives the corresponding difference on the residue ring. -/
theorem residueEval_dilatedDifference_one (G : IntForm n) (h x : Fin n → ZMod p) :
    residueEval (dilatedDifference 1 (residueVectorIntRep h) G) p x =
      residueEval G p (x + h) - residueEval G p x := by
  let E := eval₂Hom (Int.castRingHom (ZMod p)) x
  have he := congrArg E (mul_dilatedDifference 1 (residueVectorIntRep h) G)
  simp only [map_sub, map_one, one_mul, E, coe_eval₂Hom] at he
  unfold residueEval
  rw [he, aeval_def, algebraMap_eq, ← eval₂_assoc]
  simp only [eval₂_add, eval₂_X, eval₂_C, Int.coe_castRingHom, cast_residueVectorIntRep]
  rfl

private theorem stdAddChar_conj (c : ZMod p) : conj (stdAddChar c) = stdAddChar (-c) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

private theorem phase_correlation (W : (Fin n → ZMod p) → ZMod p) (a : ZMod p) :
    (∑ x, stdAddChar (a * W x)) * conj (∑ x, stdAddChar (a * W x)) =
      ∑ h : Fin n → ZMod p, ∑ x : Fin n → ZMod p,
        stdAddChar (a * (W (x + h) - W x)) := by
  classical
  rw [map_sum, Finset.sum_mul_sum]
  simp_rw [stdAddChar_conj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact (Equiv.sum_comp (Equiv.addLeft x) (fun y => stdAddChar (a * (W y - W x)))).symm

/-- The exact autocorrelation identity with the normalization of `completeSum`. -/
theorem completeSum_mul_conj_eq_average_dilatedDifference (G : IntForm n) (a : ZMod p) :
    completeSum G p a * conj (completeSum G p a) =
      ((p : ℂ) ^ n)⁻¹ * ∑ h : Fin n → ZMod p,
        completeSum (dilatedDifference 1 (residueVectorIntRep h) G) p a := by
  unfold completeSum
  simp only [map_mul, map_inv₀, map_pow, Complex.conj_natCast]
  rw [mul_mul_mul_comm, phase_correlation, ← Finset.mul_sum]
  simp_rw [residueEval_dilatedDifference_one]
  ring

/-- One differencing step for normalized complete sums, valid at every nonzero modulus. -/
theorem norm_completeSum_sq_le_average_dilatedDifference (G : IntForm n) (a : ZMod p) :
    ‖completeSum G p a‖ ^ 2 ≤
      ((p : ℝ) ^ n)⁻¹ * ∑ h : Fin n → ZMod p,
        ‖completeSum (dilatedDifference 1 (residueVectorIntRep h) G) p a‖ := by
  calc
    ‖completeSum G p a‖ ^ 2 = ‖completeSum G p a * conj (completeSum G p a)‖ := by
      rw [norm_mul, Complex.norm_conj, pow_two]
    _ = ((p : ℝ) ^ n)⁻¹ * ‖∑ h : Fin n → ZMod p,
        completeSum (dilatedDifference 1 (residueVectorIntRep h) G) p a‖ := by
      rw [completeSum_mul_conj_eq_average_dilatedDifference, norm_mul, norm_inv, norm_pow,
        Complex.norm_natCast]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

end

end Birch
