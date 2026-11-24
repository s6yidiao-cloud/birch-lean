import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The singular-dimension losses in repeated differencing

This is the exponent calculation in eq:selected. It applies to an actual chain of
selected shifts whenever the one-step bounds have been established.
-/

namespace Birch

/-- Iterated differencing saves the increase in singular dimension. -/
theorem iterated_square_savings_from_dimension (k : ℕ) (A : ℕ → ℝ) (s : ℕ → ℕ)
    (Q C : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (hA : ∀ i, 0 ≤ A i)
    (hstep : ∀ i < k, (A i)^2 ≤
      C * Q ^ (-(↑(s (i + 1) - s i) : ℝ) / ((2 : ℝ) ^ (k - 1 - i))) * A (i + 1)) :
    A 0 ^ (2 ^ k : ℕ) ≤ C ^ (2 ^ k - 1 : ℕ) *
      Q ^ (-(↑(s k - s 0) : ℝ)) * A k := by
  induction k generalizing A s with
  | zero => simp
  | succ k ih =>
      have hpos : 0 < Q := zero_lt_one.trans_le hQ
      let D : ℕ := 2 ^ k
      have hD : 0 < D := by dsimp [D]; positivity
      have hDr : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
      have hnext := ih (fun i ↦ A (i + 1)) (fun i ↦ s (i + 1)) (fun i ↦ hA _) (by
        intro i hi
        have h := hstep (i + 1) (by omega)
        have hidx : k + 1 - 1 - (i + 1) = k - 1 - i := by omega
        rwa [hidx] at h)
      let a : ℕ := s 1 - s 0
      let b : ℕ := s (k + 1) - s 1
      have hfirst : (A 0)^2 ≤ C * Q ^ (-(a : ℝ) / D) * A 1 := by
        simpa [D, a] using hstep 0 k.zero_lt_succ
      have hpower : (Q ^ (-(a : ℝ) / D)) ^ D = Q ^ (-(a : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, div_mul_cancel₀ _ hDr.ne']
      have hs : (s (k + 1) - s 0 : ℕ) ≤ a + b := by dsimp [a, b]; omega
      have hscast : ((s (k + 1) - s 0 : ℕ) : ℝ) ≤ (a : ℝ) + b := by exact_mod_cast hs
      have hCD : C ^ D * C ^ (D - 1) = C ^ (2 ^ (k + 1) - 1 : ℕ) := by
        rw [← pow_add, pow_succ]
        congr 1
        change D + (D - 1) = D * 2 - 1
        omega
      calc
        A 0 ^ (2 ^ (k + 1) : ℕ) = ((A 0)^2)^D := by
          rw [← pow_mul, pow_succ, mul_comm 2]
        _ ≤ (C * Q ^ (-(a : ℝ) / D) * A 1)^D :=
          pow_le_pow_left₀ (sq_nonneg _) hfirst _
        _ = C ^ D * Q ^ (-(a : ℝ)) * (A 1 ^ D) := by rw [mul_pow, mul_pow, hpower]
        _ ≤ C ^ D * Q ^ (-(a : ℝ)) * (C ^ (D - 1) * Q ^ (-(b : ℝ)) * A (k + 1)) :=
          mul_le_mul_of_nonneg_left hnext (by positivity)
        _ = C ^ (2 ^ (k + 1) - 1 : ℕ) * Q ^ (-(a : ℝ) - b) * A (k + 1) := by
          rw [sub_eq_add_neg, Real.rpow_add hpos, ← hCD]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (hA _)
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
          exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)

/-- Iterating the differencing inequalities retains the full singular-dimension
loss. The terminal estimate at dimension `s k` then supplies the remaining
`n - s k` powers of `Q`. -/
theorem iterated_square_savings (k n : ℕ) (A : ℕ → ℝ) (s : ℕ → ℕ)
    (Q C T : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hA : ∀ i, 0 ≤ A i)
    (hs₀ : s 0 = 0) (hsn : s k ≤ n)
    (hstep : ∀ i < k, (A i)^2 ≤
      C * Q ^ (-(↑(s (i + 1) - s i) : ℝ) / ((2 : ℝ) ^ (k - 1 - i))) * A (i + 1))
    (hterminal : A k ≤ T * Q ^ (-(↑(n - s k) : ℝ))) :
    A 0 ^ (2 ^ k : ℕ) ≤ C ^ (2 ^ k - 1 : ℕ) * T * Q ^ (-(n : ℝ)) := by
  have hQpos := zero_lt_one.trans_le hQ
  have h := iterated_square_savings_from_dimension k A s Q C hQ hC hA hstep
  rw [hs₀, Nat.sub_zero] at h
  refine h.trans ((mul_le_mul_of_nonneg_left hterminal ?_).trans_eq ?_)
  · positivity
  · have he : -(s k : ℝ) + -((n - s k : ℕ) : ℝ) = -(n : ℝ) := by
      rw [Nat.cast_sub hsn]; ring
    rw [← he, Real.rpow_add hQpos]
    ring

end Birch
