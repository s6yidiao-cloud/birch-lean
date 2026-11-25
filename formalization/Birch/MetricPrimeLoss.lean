import Birch.Metric

/-! # Moving a prime loss to the scale of the metric estimate -/

open Filter
open scoped Topology

namespace Birch

/-- The completion bound with an extra fixed power of the prime conductor. -/
def CompletionEstimateWithPrimeLoss (d n : ℕ) (f : ℝ → ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ (r : ℕ), 2 ≤ r → r < d → ∃ C > 0, ∀ᶠ P in atTop,
    ∀ (Q : ℝ), 1 ≤ Q → Q ≤ P ^ (1 / 2 : ℝ) →
    ∀ (p M : ℕ), p.Prime → (P / Q) ^ (2 : ℕ) < (p : ℝ) →
      (p : ℝ) ≤ 2 * (P / Q) ^ (2 : ℕ) → admissibleProduct d r P Q M →
    ∀ (a : ℤ) (α : ℝ), ¬ (p : ℤ) ∣ a →
      |(M : ℝ) * α - (a : ℝ) / (p : ℝ)| ≤ completionRadius d r P Q →
        f P α ≤ C * (p : ℝ)^δ * Q ^ (-((n : ℝ) / (2 : ℝ) ^ (d - r)))

/-- The prime range in completion absorbs the extra power after rescaling
the magnitude by `P ^ (-2 * δ)`. -/
theorem CompletionEstimateWithPrimeLoss.scaled {d n : ℕ} {f : ℝ → ℝ → ℝ} {δ : ℝ}
    (h : CompletionEstimateWithPrimeLoss d n f δ) (hδ : 0 ≤ δ) :
    CompletionEstimate d n (fun P α => P ^ (-(2 * δ)) * f P α) := by
  intro r hr hrd
  obtain ⟨C, hC, h⟩ := h r hr hrd
  refine ⟨C * (2 : ℝ)^δ, by positivity, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with P hP hPone
  intro Q hQ hQP p M hp hpL hpU hprod a α ha hα
  have hPpos : 0 < P := zero_lt_one.trans_le hPone
  have hPdiv : P / Q ≤ P := div_le_self hPpos.le hQ
  have hpU' : (p : ℝ) ≤ 2 * P^2 := hpU.trans (by gcongr)
  have hscale : (p : ℝ)^δ ≤ (2 : ℝ)^δ * P^(2 * δ) := by
    calc
      _ ≤ (2 * P^2)^δ := Real.rpow_le_rpow (Nat.cast_nonneg p) hpU' hδ
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
          ← Real.rpow_natCast P 2, ← Real.rpow_mul hPpos.le]
        norm_num
  have hrpow : P ^ (-(2 * δ)) * P ^ (2 * δ) = 1 := by
    rw [← Real.rpow_add hPpos, neg_add_cancel, Real.rpow_zero]
  let e := -((n : ℝ) / (2 : ℝ) ^ (d-r))
  have hbound := hP Q hQ hQP p M hp hpL hpU hprod a α ha hα
  change P ^ (-(2 * δ)) * f P α ≤ (C * (2 : ℝ)^δ) * Q^e
  calc
    _ ≤ P ^ (-(2 * δ)) * (C * (p : ℝ)^δ * Q^e) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hPpos.le _)
    _ ≤ P ^ (-(2 * δ)) * (C * ((2 : ℝ)^δ * P^(2 * δ)) * Q^e) := by
      gcongr
    _ = _ := by
      calc
        _ = (C * (2 : ℝ)^δ) * Q^e * (P^(-(2 * δ)) * P^(2 * δ)) := by ring
        _ = _ := by rw [hrpow, mul_one]

end Birch
