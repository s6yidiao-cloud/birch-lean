import Birch.V2Covers

/-! # Rescaling compact weights for polynomial covers -/

open MeasureTheory
open scoped Polynomial

namespace Birch

noncomputable section

/-- The real cover oscillation with a fixed multiplier of the natural length. -/
def coverRealOscillationOn (g : ℤ[X]) (e : ℕ) (B γ : ℝ) : ℂ :=
  ∫ t in (-B)..B, phase (-γ * (g.leadingCoeff : ℝ) * t ^ e)

def coverSingularIntegralOn {n : ℕ} (F : IntForm n) (g : ℤ[X]) (e : ℕ)
    (w : (Fin n → ℝ) → ℝ) (B : ℝ) : ℂ :=
  ∫ γ, realOscillation F w γ * coverRealOscillationOn g e B γ

/-- Rescaling the form variables multiplies the auxiliary cover length by
`R^(-d/e)`, thereby keeping the original cutoff on the integral variable. -/
theorem coverWeightedZeros_eq_box_rescale {d e n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) {R P : ℝ} (hR : 0 < R) (hP : 0 < P)
    (hbox : ∀ x, w x ≠ 0 → ∀ i, |x i| ≤ R) :
    coverWeightedZeros d e F g w P =
      coverWeightedBoxZeros F g (fun x => w (R • x)) (R * P)
        (R ^ (-((d : ℝ) / e)) * (R * P) ^ ((d : ℝ) / e)) := by
  let k := (d : ℝ) / e
  have hY : R ^ (-k) * (R * P) ^ k = P ^ k := by
    rw [Real.mul_rpow hR.le hP.le, ← mul_assoc, ← Real.rpow_add hR, neg_add_cancel,
      Real.rpow_zero, one_mul]
  change _ = coverWeightedBoxZeros F g (fun x => w (R • x)) (R * P)
    (R ^ (-k) * (R * P) ^ k)
  rw [hY]
  unfold coverWeightedZeros coverWeightedBoxZeros
  rw [finsum_eq_finsetSum_of_support_subset _ (s := latticeBox n (R * P))]
  · apply Finset.sum_congr rfl
    intro x _
    have hx : R • scaledPoint (R * P) x = scaledPoint P x := by
      funext i
      simp only [scaledPoint, Pi.smul_apply, smul_eq_mul]
      field_simp
    simp only [hx, k]
  · intro x hx
    have hwx : w (scaledPoint P x) ≠ 0 := by
      intro hzero
      apply hx
      simp [hzero]
    apply mem_latticeBox_iff_abs.mpr
    intro i
    have hi := hbox _ hwx i
    rwa [scaledPoint, abs_div, abs_of_pos hP, div_le_iff₀ hP] at hi

end

end Birch
