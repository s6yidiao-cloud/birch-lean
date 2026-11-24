import Birch.MetricTransfer
import Birch.MajorArcLatticePoisson
import Birch.CompletionConditional
import Birch.RealGaussian
import Birch.CompleteBounds
import Birch.Geometry
import Birch.Weyl
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# From circle-method estimates to the Hasse principle

The three analytic estimates in the main theorem below are hypotheses. The reduction
includes the paper's level mesh, weight selection, and exact lattice orthogonality.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Birch

noncomputable section

private theorem integral_normalizedSum_eq {n : ℕ} (F : IntForm n)
    (w : (Fin n → ℝ) → ℝ) (P : ℝ) :
    (∫ α, normalizedSum F w P α ∂circleMeasure) =
      (P ^ (-(n : ℝ)) : ℝ) • (weightedZeros F w P : ℂ) := by
  unfold normalizedSum
  rw [integral_smul, integral_exponentialSum_eq_weightedZeros]

/-- Combining bounds for the two arc integrals gives the weighted asymptotic
with the smaller of their power savings. -/
theorem weightedAsymptoticBound_of_arcIntegrals
    {d n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ} {δ σ : ℝ}
    (hMinor : ∃ K > 0, ∀ᶠ P : ℝ in atTop,
      (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤
        K * P ^ (-(d : ℝ) - δ))
    (hMajor : ∃ M > 0, ∀ᶠ P in atTop,
      ‖(∫ α in majorArcs d P, normalizedSum F w P α ∂circleMeasure) -
        (P ^ (-(d : ℝ)) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        M * P ^ (-(d : ℝ) - σ)) :
    ∃ C > 0, ∀ᶠ P in atTop,
      ‖(weightedZeros F w P : ℂ) -
        (P ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * P ^ ((n : ℝ) - d - min δ σ) := by
  let η := min δ σ
  obtain ⟨K, hK, hKbound⟩ := hMinor
  obtain ⟨M, hM, hMbound⟩ := hMajor
  refine ⟨M + K, add_pos hM hK, ?_⟩
  filter_upwards [hKbound, hMbound, eventually_ge_atTop (1 : ℝ)] with P hminorP hmajorP hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  let A := singularSeries F * singularIntegral F w
  let B := majorArcs d P
  have hIntegral : Integrable (normalizedSum F w P) circleMeasure := by
    unfold normalizedSum
    exact (integrable_exponentialSum F w P).smul (P ^ (-(n : ℝ)) : ℝ)
  have hsplit := integral_add_compl (measurableSet_majorArcs d P) hIntegral
  have hminorNorm :
      ‖∫ α in Bᶜ, normalizedSum F w P α ∂circleMeasure‖ ≤ K * P ^ (-(d : ℝ) - δ) :=
    (norm_integral_le_integral_norm _).trans hminorP
  have combined :
      ‖(∫ α, normalizedSum F w P α ∂circleMeasure) - (P ^ (-(d : ℝ)) : ℝ) • A‖ ≤
        (M + K) * P ^ (-(d : ℝ) - η) := by
    rw [← hsplit, add_sub_right_comm, add_mul]
    exact (norm_add_le _ _).trans <| add_le_add
      (hmajorP.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith [show η ≤ σ from min_le_right _ _])) hM.le))
      (hminorNorm.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith [show η ≤ δ from min_le_left _ _])) hK.le))
  rw [integral_normalizedSum_eq] at combined
  have hscale :
      (P ^ (n : ℝ) : ℝ) •
        ((P ^ (-(n : ℝ)) : ℝ) • (weightedZeros F w P : ℂ) - (P ^ (-(d : ℝ)) : ℝ) • A) =
      (weightedZeros F w P : ℂ) - (P ^ ((n : ℝ) - d) : ℝ) • A := by
    rw [smul_sub, smul_smul, smul_smul, ← Real.rpow_add hPpos, add_neg_cancel,
      Real.rpow_zero, one_smul, ← Real.rpow_add hPpos, ← sub_eq_add_neg]
  rw [← hscale, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hPpos _)]
  calc
    _ ≤ P ^ (n : ℝ) * ((M + K) * P ^ (-(d : ℝ) - η)) :=
      mul_le_mul_of_nonneg_left combined (Real.rpow_nonneg hPpos.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hPpos]
      congr 2
      ring

/-- A positive leading coefficient and a power saving make the count
strictly positive at every sufficiently large scale. -/
theorem eventually_weightedZeros_pos_of_asymptotic {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} {A : ℂ} (hA : 0 < A.re)
    {η C : ℝ} (hη : 0 < η) (hC : 0 < C)
    (h : ∀ᶠ P : ℝ in atTop,
      ‖(weightedZeros F w P : ℂ) - (P ^ ((n : ℝ) - d) : ℝ) • A‖ ≤
        C * P ^ ((n : ℝ) - d - η)) : ∀ᶠ P : ℝ in atTop, 0 < weightedZeros F w P := by
  have hsmall : ∀ᶠ P : ℝ in atTop, P ^ (-η) < A.re / C :=
    (tendsto_order.mp (tendsto_rpow_neg_atTop hη)).2 _ (div_pos hA hC)
  filter_upwards [h, hsmall, eventually_gt_atTop (0 : ℝ)] with P herror hrate hP
  have hsmall' : C * P ^ (-η) < A.re := by
    rw [lt_div_iff₀ hC] at hrate
    rwa [mul_comm]
  have hmain : C * P ^ ((n : ℝ) - d - η) < P ^ ((n : ℝ) - d) * A.re := by
    rw [sub_eq_add_neg, Real.rpow_add hP, mul_left_comm]
    exact mul_lt_mul_of_pos_left hsmall' (Real.rpow_pos_of_pos hP _)
  have hre := (Complex.abs_re_le_norm
    ((weightedZeros F w P : ℂ) - (P ^ ((n : ℝ) - d) : ℝ) • A)).trans herror
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.smul_re, smul_eq_mul] at hre
  linarith [(abs_le.mp hre).1]

end

end Birch
