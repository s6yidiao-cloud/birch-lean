import Birch.V2Forms
import Birch.V2CoverLocal
import Birch.V2CoverMinorArcs
import Birch.V2CoverFourthMoment
import Mathlib.Algebra.Polynomial.Roots

/-! # The polynomial-cover statements of the v2 manuscript -/

open Filter MeasureTheory Polynomial
open scoped Polynomial Topology

namespace Birch

noncomputable section

/-- The count with compact weight on the form variables and the natural
cutoff `P^(d/e)` on the cover variable. -/
def coverWeightedZeros {n : ℕ} (d e : ℕ) (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (P : ℝ) : ℝ :=
  let Y := P ^ ((d : ℝ) / e)
  ∑ᶠ x : Fin n → ℤ,
    ∑ y ∈ Finset.Icc (-⌊Y⌋) ⌊Y⌋, if evalForm F x = g.eval y then w (scaledPoint P x) else 0

/-- Positive scales and compact support put the entire form-variable sum
in a finite box, without changing the cover-variable cutoff. -/
theorem coverWeightedZeros_eq_box {n d e : ℕ} (F : IntForm n) (g : ℤ[X])
    {w : (Fin n → ℝ) → ℝ} (hw : HasCompactSupport w) :
    ∃ R ≥ 1, ∀ P > 0, coverWeightedZeros d e F g w P =
      ∑ x ∈ latticeBox n (R * P),
        ∑ y ∈ Finset.Icc (-⌊P ^ ((d : ℝ) / e)⌋) ⌊P ^ ((d : ℝ) / e)⌋,
          if evalForm F x = g.eval y then w (scaledPoint P x) else 0 := by
  classical
  obtain ⟨B, hB⟩ := hw.isBounded.exists_norm_le
  refine ⟨max 1 B, le_max_left _ _, fun P hP => ?_⟩
  unfold coverWeightedZeros
  apply finsum_eq_finsetSum_of_support_subset
  intro x hx
  have hwx : w (scaledPoint P x) ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  apply mem_latticeBox_iff_abs.mpr
  intro i
  have hi : |scaledPoint P x i| ≤ max 1 B := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ i).trans ((hB _ (subset_tsupport _ hwx)).trans (le_max_right _ _))
  rwa [scaledPoint, abs_div, abs_of_pos hP, div_le_iff₀ hP] at hi

/-- Only the leading term survives in the continuum oscillation of the cover. -/
def coverRealOscillation (g : ℤ[X]) (e : ℕ) (γ : ℝ) : ℂ :=
  ∫ t in (-1 : ℝ)..1, phase (-γ * (g.leadingCoeff : ℝ) * t ^ e)

def coverSingularIntegral {n : ℕ} (F : IntForm n) (g : ℤ[X]) (e : ℕ)
    (w : (Fin n → ℝ) → ℝ) : ℂ :=
  ∫ γ, realOscillation F w γ * coverRealOscillation g e γ

/-- Integral pairs over the closed form-variable box. The roots are taken
without multiplicity or a cutoff on the cover variable. -/
def coverIntegralPairs {n : ℕ} (F : IntForm n) (g : ℤ[X]) (P : ℝ) :
    Finset (Σ _ : Fin n → ℤ, ℤ) :=
  (latticeBox n P).sigma fun x => (g - C (evalForm F x)).roots.toFinset

theorem mem_coverIntegralPairs {n : ℕ} (F : IntForm n) {g : ℤ[X]} (hg : 0 < g.degree)
    {P : ℝ} {x : Fin n → ℤ} {y : ℤ} :
    ⟨x, y⟩ ∈ coverIntegralPairs F g P ↔ x ∈ latticeBox n P ∧ evalForm F x = g.eval y := by
  rw [coverIntegralPairs, Finset.mem_sigma, Multiset.mem_toFinset, Polynomial.mem_roots_sub_C hg]
  exact and_congr_right fun _ => eq_comm

def coverIntegralCount {n : ℕ} (F : IntForm n) (g : ℤ[X]) (P : ℝ) : ℕ :=
  (coverIntegralPairs F g P).card

def coverWeightedBoxZeros {n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (P L : ℝ) : ℝ :=
  ∑ x ∈ latticeBox n P, ∑ y ∈ Finset.Icc (-⌊L⌋) ⌊L⌋,
    if evalForm F x = g.eval y then w (scaledPoint P x) else 0

/-- Orthogonality for the product of the form sum and the cover sum. -/
theorem integral_exponentialSum_mul_coverYSum {n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (P L : ℝ) :
    (∫ α, exponentialSum F w P α * coverYSum g L α ∂circleMeasure) =
      (coverWeightedBoxZeros F g w P L : ℂ) := by
  classical
  unfold exponentialSum coverYSum coverWeightedBoxZeros
  simp_rw [Finset.sum_mul, Finset.mul_sum, Complex.ofReal_sum]
  have hterm (x : Fin n → ℤ) (y : ℤ) :
      Integrable (fun α : ℝ =>
        (w (scaledPoint P x) : ℂ) * phase (α * ((evalForm F x : ℤ) : ℝ)) *
          phase (-α * ((g.eval y : ℤ) : ℝ))) circleMeasure := by
    have hc : Continuous (fun α : ℝ =>
        (w (scaledPoint P x) : ℂ) * phase (α * ((evalForm F x : ℤ) : ℝ)) *
          phase (-α * ((g.eval y : ℤ) : ℝ))) := by unfold phase; fun_prop
    exact hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro y _
      simp_rw [mul_assoc, ← phase_add]
      have hphase (α : ℝ) : α * ((evalForm F x : ℤ) : ℝ) + -α * ((g.eval y : ℤ) : ℝ) =
          α * ((evalForm F x - g.eval y : ℤ) : ℝ) := by push_cast; ring
      simp_rw [hphase]
      rw [integral_const_mul, phase_integer_orthogonality]
      by_cases h : evalForm F x = g.eval y <;> simp [h, sub_eq_zero]
    · exact fun y _ => hterm x y
  · exact fun x _ => integrable_finsetSum _ fun y _ => hterm x y

end

end Birch
