import Birch.DeligneFiniteField

/-! # Extending a square-root bound across finitely many primes -/

open Filter MvPolynomial

namespace Birch

/-- The trivial bound counts one unit-norm summand per point of the affine space. -/
theorem norm_primeDeligneSum_le_card {p l : ℕ} [NeZero p]
    (g : MvPolynomial (Fin l) (ZMod p)) : ‖primeDeligneSum p g‖ ≤ (p : ℝ)^l := by
  unfold primeDeligneSum
  calc
    _ ≤ ∑ x : Fin l → ZMod p, ‖ZMod.stdAddChar (g.eval x)‖ := norm_sum_le _ _
    _ = _ := by simp [ZMod.stdAddChar_apply, ZMod.card]

/-- A fixed-dimensional square-root estimate for all sufficiently large
primes gives a uniform normalized twisted estimate at every prime. -/
theorem uniformTwistedPrimeBound_of_eventual_primeBound {r l : ℕ} (hr : 2 ≤ r) (C : ℝ)
    (h : ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], 0 < l → r < p →
      ∀ g : MvPolynomial (Fin l) (ZMod p), g.totalDegree ≤ r →
        PrimeIsolatedLeadingCriticalPoint p r g →
        ‖primeDeligneSum p g‖ ≤ C * (p : ℝ)^((l : ℝ)/2)) :
    UniformTwistedPrimeBound r l := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let B : ℝ := max 1 (max C (N : ℝ))
  have hB : 1 ≤ B := le_max_left _ _
  have hCB : C ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hNB : (N : ℝ) ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hpoint : PrimeExponentialSumBoundAtDimension r l B := by
    intro p _ _ hl hrp g hg hcrit
    have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    by_cases hp : N ≤ p
    · exact (hN p hp hl hrp g hg hcrit).trans (mul_le_mul_of_nonneg_right
        (hCB.trans (le_self_pow₀ hB hl.ne')) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    · have hpB : (p : ℝ) ≤ B := (by exact_mod_cast (le_of_lt (lt_of_not_ge hp)) :
        (p : ℝ) ≤ (N : ℝ)).trans hNB
      exact (norm_primeDeligneSum_le_card g).trans
        ((pow_le_pow_left₀ (Nat.cast_nonneg p) hpB _).trans
          (le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hp₁ (by positivity))))
  exact ⟨B^l, pow_pos (zero_lt_one.trans_le hB) _,
    twistedCompleteSum_le_of_primeExponentialSumBoundAtDimension hr hpoint⟩

end Birch
