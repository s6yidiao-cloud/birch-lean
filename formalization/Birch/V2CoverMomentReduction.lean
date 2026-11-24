import Birch.V2CoverMoments
import Birch.V2CoverVinogradov

/-!
# The high-degree selected cover moment

For cover degree at least five, the selected moment in `v2.tex` is
`e * (e + 1)`. The signed-interval critical Vinogradov estimate supplies
this moment through the checked one-polynomial projection.
-/

namespace Birch

open Filter MeasureTheory Polynomial
open scoped ENNReal

noncomputable section

/-- In degrees at least five, the quadratic expression is the smaller moment. -/
theorem coverMomentExponent_eq_mul_succ {e : ℕ} (he : 5 ≤ e) :
    coverMomentExponent e = e * (e + 1) := by
  have h : e * (e + 1) ≤ 2 ^ e := by
    induction e, he using Nat.le_induction with
    | base => decide
    | succ e he ih =>
      rw [pow_succ]
      calc
        _ ≤ (e + 1) * (2 * e) := Nat.mul_le_mul_left _ (by omega)
        _ = (e * (e + 1)) * 2 := by ring
        _ ≤ _ := Nat.mul_le_mul_right 2 ih
  exact min_eq_right h

/-- The selected high-degree cover moment follows from critical VMVT.
The arithmetic mean value estimate is an explicit hypothesis. -/
theorem coverMeanValueBound_of_criticalVinogradov {e : ℕ} {g : Polynomial ℤ}
    (he : 5 ≤ e) (hg : g.natDegree = e) (hvmvt : CriticalVinogradovEstimate e) :
    CoverMeanValueBound e g := by
  intro ε hε
  let m := e * (e + 1)
  obtain ⟨C, hC, hbound⟩ :=
    coverYSum_wooleyMoment_le_of_vinogradov (by omega : 0 < e) g hg hvmvt hε
  have hexp : (m : ℝ) - e + ε = (e : ℝ) ^ 2 + ε := by
    dsimp [m]
    push_cast
    ring
  rw [coverMomentExponent_eq_mul_succ he]
  change coverPowerBound
    (fun L => ∫⁻ α, ENNReal.ofReal ‖coverYSum g L α‖ ^ (m : ℝ) ∂circleMeasure)
    ((m : ℝ) - e + ε)
  rw [hexp]
  apply coverPowerBound_of_realConstant
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  have hcont : Continuous (fun α => ‖coverYSum g L α‖ ^ m) :=
    (continuous_coverYSum g L).norm.pow m
  have hint : Integrable (fun α => ‖coverYSum g L α‖ ^ m) circleMeasure :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  simp only [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (Nat.cast_nonneg m),
    Real.rpow_natCast]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => by positivity)]
  exact ENNReal.ofReal_le_ofReal (hbound L hL)

end

end Birch
