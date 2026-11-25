import Birch.DeligneEventualPrimeBound

/-! # Normalization and small-prime bounds with a power loss -/

open Filter MvPolynomial

namespace Birch

/-- The normalized square-root estimate with a specified extra power of the prime. -/
def UniformTwistedPrimeBoundWithLoss (r l : ℕ) (δ : ℝ) : Prop :=
  ∃ C > 0, ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
    ∀ (g : IntForm l), g.totalDegree ≤ r →
      (∀ x : Fin l → AlgebraicClosure (ZMod p),
        (∀ i, evalForm (pderiv i (homogeneousComponent r g)) x = 0) → x = 0) →
      ∀ (a : ℤ), (a : ZMod p) ≠ 0 → ∀ z : Fin l → ℤ,
        ‖twistedCompleteSum g p a z‖ ≤ C * (p : ℝ)^(-(l : ℝ)/2 + δ)

/-- An exact square-root bound also gives the bound with a nonnegative power loss. -/
theorem UniformTwistedPrimeBound.withLoss {r l : ℕ} {δ : ℝ}
    (h : UniformTwistedPrimeBound r l) (hδ : 0 ≤ δ) :
    UniformTwistedPrimeBoundWithLoss r l δ := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro p _ _ hrp g hg hs a ha z
  have hp : (1 : ℝ) ≤ p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact (h p hrp g hg hs a ha z).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp (by linarith)) hC.le)

/-- Express the extra power as a multiplier on the square-root estimate. -/
theorem UniformTwistedPrimeBoundWithLoss.withMultiplier {r l : ℕ} {δ : ℝ}
    (h : UniformTwistedPrimeBoundWithLoss r l δ) :
    UniformTwistedResidueBoundWithMultiplier (fun p => p) r l (fun p => (p : ℝ)^δ) := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro p _ _ hrp g hg hs a ha z
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  rw [mul_assoc, ← Real.rpow_add hp, add_comm δ]
  exact h p hrp g hg hs a ha z

/-- A bound at sufficiently large primes transfers to all prime conductors
with its extra power unchanged. -/
theorem uniformTwistedPrimeBoundWithLoss_of_eventual {r l : ℕ}
    (hr : 2 ≤ r) {δ : ℝ} (hδ : 0 ≤ δ) (C : ℝ)
    (h : ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], r < p →
      ∀ g : MvPolynomial (Fin l) (ZMod p), g.totalDegree ≤ r →
        PrimeIsolatedLeadingCriticalPoint p r g →
        ‖primeDeligneSum p g‖ ≤ C * (p : ℝ)^((l : ℝ)/2 + δ)) :
    UniformTwistedPrimeBoundWithLoss r l δ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let B : ℝ := max 1 (max C ((N : ℝ)^l))
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro p _ _ hrp g hg hs a ha z
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hp₁ : 1 ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hpoint (f : MvPolynomial (Fin l) (ZMod p)) (hf : f.totalDegree ≤ r)
      (hcrit : PrimeIsolatedLeadingCriticalPoint p r f) :
      ‖primeDeligneSum p f‖ ≤ B * (p : ℝ)^((l : ℝ)/2 + δ) := by
    by_cases hpN : N ≤ p
    · exact (hN p hpN hrp f hf hcrit).trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (Real.rpow_nonneg hp.le _))
    · have hpN' : (p : ℝ) ≤ N := by exact_mod_cast (le_of_lt (lt_of_not_ge hpN))
      have hpow : (p : ℝ)^l ≤ B := (pow_le_pow_left₀ hp.le hpN' _).trans
        ((le_max_right _ _).trans (le_max_right _ _))
      exact (norm_primeDeligneSum_le_card f).trans (hpow.trans
        (le_mul_of_one_le_right hB.le (Real.one_le_rpow hp₁ (by positivity))))
  refine (norm_twistedCompleteSum_le_of_primeDeligneSum_le hr g hg hs a ha z hpoint).trans_eq ?_
  rw [mul_div_assoc, ← Real.rpow_natCast p l, ← Real.rpow_sub hp]
  congr 2
  ring

end Birch
