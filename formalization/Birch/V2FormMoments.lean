import Birch.V2Forms
import Birch.V2GradientReduction
import Birch.V2CoverMinorArcs
import Birch.SmoothSectionExistence
import Birch.DeligneFiniteField
import Birch.DirectionStratumCount
import Birch.WeylEstimateProof
import Birch.FinalQuadraticMetric
import Birch.UnivariateStepanov
import Birch.DelignePrimeBoundWithLoss
import Birch.MetricPrimeLoss

/-! # Weyl, completion and the critical moment at singular codimension -/

open Filter MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Topology

namespace Birch

noncomputable section

theorem cast_dimensionThreshold_eq_minorDimensionThreshold {d : ℕ} (hd : 2 ≤ d) :
    (dimensionThreshold d : ℝ) = minorDimensionThreshold d := by
  have h : 4 ≤ 2 ^ (d + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ d + 1 by omega)
  unfold dimensionThreshold minorDimensionThreshold
  push_cast [Nat.cast_sub h]
  rfl

theorem RationalGradientDimension.eventualPrimeLE {n d σ : ℕ} {F : IntForm n}
    (hσ : RationalGradientDimension F σ) (hn : 0 < n) (hd : 2 ≤ d) (hF : F.IsHomogeneous d) :
    EventualPrimeGradientDimensionLE F σ := by
  dsimp [RationalGradientDimension] at hσ
  exact eventualPrimeGradientDimensionLE_of_geometric_dimension_le hn hF hd hσ.le

/-- The square-root estimates needed in the terminal degrees of a degree-`d` form. -/
def TerminalPrimeBounds (d : ℕ) : Prop :=
  ∀ r, 3 ≤ r → r < d → ∀ l, UniformTwistedPrimeBound r l

/-- In dimensions at least two, the terminal estimate may lose a small power of the prime. -/
def TerminalPrimeBoundsWithLoss (d : ℕ) (δ : ℝ) : Prop :=
  ∀ r, 3 ≤ r → r < d → ∀ l, 2 ≤ l → UniformTwistedPrimeBoundWithLoss r l δ

theorem TerminalPrimeBoundsWithLoss.of_terminalPrimeBounds {d : ℕ} {δ : ℝ}
    (h : TerminalPrimeBounds d) (hδ : 0 ≤ δ) : TerminalPrimeBoundsWithLoss d δ :=
  fun r hr hrd l _ => (h r hr hrd l).withLoss hδ

theorem TerminalPrimeBounds.of_deligne {d : ℕ}
    (h : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) : TerminalPrimeBounds d := by
  intro r hr hrd l
  exact uniformTwistedPrimeBound_of_deligneTwistedDegree (by omega)
    (deligneTwistedDegree_of_primeDeligneEstimate (by omega) (h r hr hrd)) l

/-- Only terminal dimensions at least two remain after the Stepanov estimate. -/
theorem TerminalPrimeBounds.of_higherDimensional {d : ℕ}
    (h : ∀ r, 3 ≤ r → r < d → ∀ l, 2 ≤ l → UniformTwistedPrimeBound r l) :
    TerminalPrimeBounds d := by
  intro r hr hrd l
  rcases l with _ | _ | l
  · exact uniformTwistedPrimeBound_zero (by omega)
  · exact uniformTwistedPrimeBound_one_of_stepanov (by omega)
  · exact h r hr hrd (l + 2) (by omega)

/-- Completion from the uniform twisted prime-field bounds in terminal
degrees at least three. The quadratic stage has its own proof. -/
theorem v2CompletionEstimate_of_terminalPrimeBounds {n d σ : ℕ} {F : IntForm n}
    (hn : 0 < n) (hd : 3 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hPrime : TerminalPrimeBounds d) :
    CompletionEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖) := by
  apply completionEstimate_of_gradientDim hF (hσ.eventualPrimeLE hn (by omega) hF) hwbox
  exact completionInputs_of_direction_bound_uniform_twisted hF hw hwbox (primeDirectionBound n d)
    fun r hr hrd l _ => hPrime r hr hrd l

/-- Completion transmits the terminal power loss with a constant uniform in the prime. -/
theorem v2CompletionEstimateWithPrimeLoss {n d σ : ℕ} {F : IntForm n} {δ : ℝ}
    (hn : 0 < n) (hd : 3 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hδ : 0 ≤ δ) (hPrime : TerminalPrimeBoundsWithLoss d δ) :
    CompletionEstimateWithPrimeLoss d (n - σ) (fun P α => ‖normalizedSum F w P α‖) δ := by
  have hnonneg (p : ℕ) : 0 ≤ (p : ℝ)^δ := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hone (p : ℕ) (hp : p.Prime) : 1 ≤ (p : ℝ)^δ :=
    Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) hδ
  intro r hr hrd
  have hTwisted (l : ℕ) : UniformTwistedPrimeBoundWithLoss r l δ := by
    rcases eq_or_lt_of_le hr with rfl | hr'
    · exact (uniformTwistedPrimeBound_of_deligneTwistedDegree le_rfl
        deligneTwistedDegree_two l).withLoss hδ
    · rcases l with _ | _ | l
      · exact (uniformTwistedPrimeBound_zero hr).withLoss hδ
      · exact (uniformTwistedPrimeBound_one_of_stepanov hr).withLoss hδ
      · exact hPrime r hr' hrd (l + 2) (by omega)
  have hinput := completionInputsAt_of_uniform_primeBounds_withMultiplier hF hw hwbox hr hrd.le
    (primeDirectionBound n d)
    (primeSectionBound_of_interior hr
      (primeInteriorSectionBound_of_geometric hr (primeGeometricInteriorSections n r hr)))
    hnonneg (fun l _ => (hTwisted l).withMultiplier)
  simpa only [mul_right_comm] using
    completionEstimateAt_of_gradientDim_withMultiplier hF (hσ.eventualPrimeLE hn (by omega) hF)
      hwbox hone hinput

theorem v2CompletionEstimate_of_weilII {n d σ : ℕ} {F : IntForm n}
    (hn : 0 < n) (hd : 3 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    CompletionEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖) :=
  v2CompletionEstimate_of_terminalPrimeBounds hn hd hF hσ hw hwbox (TerminalPrimeBounds.of_deligne hWeilII)

/-- The Weyl estimate retains the gradient codimension for weights
that meet the critical locus. -/
theorem v2WeylEstimate {n d σ : ℕ} {F : IntForm n} (hν : 0 < n - σ)
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) :
    WeylEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖) :=
  weylEstimate_of_gradientDim (by omega) (by omega) F hF
    (hσ.eventualPrimeLE (by omega) (by omega) hF) w hw hwbox (primeDirectionBound n d)

theorem v2MetricDistribution_of_completion {d ν : ℕ} {f : ℝ → ℝ → ℝ} (hd : 3 ≤ d)
    (hcompl : CompletionEstimate d ν f) :
    V2MetricDistribution circleMeasure d ν (fun P α => ENNReal.ofReal (f P α)) := by
  apply V2MetricDistribution.ofReal
  intro r h hadm ε hε
  rcases hadm with ⟨hr, hrd, hh, hhmax, _⟩ | ⟨heq, _, _, _⟩
  · obtain ⟨C, hC, h⟩ := metricLevel_of_primeHit_and_supply hr hrd hh hhmax
      (level_of_primeHit hcompl hr hrd hh hhmax) (metricProductSupply d) metricPrimeSupply
    obtain ⟨K, hK, h⟩ := h ε hε
    exact ⟨C, hC, K, hK, h⟩
  · omega

/-- The level estimates for forms include the direct quadratic case. -/
theorem v2MetricDistribution_of_terminalPrimeBounds {n d σ : ℕ} {F : IntForm n}
    (hν : 0 < n - σ) (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hPrime : TerminalPrimeBounds d) :
    V2MetricDistribution circleMeasure d (n - σ)
      (fun P α => ENNReal.ofReal ‖normalizedSum F w P α‖) := by
  by_cases h₂ : d = 2
  · subst d
    apply V2MetricDistribution.ofReal
    intro r h hadm ε hε
    rcases hadm with ⟨hr, hrd, _, _, _⟩ | ⟨_, rfl, hh, hhmax⟩
    · omega
    · obtain ⟨C, hC, hlevel⟩ := quadraticLevel_of_primeHit_and_supply hν hF hσ hw hwbox hh hhmax
      obtain ⟨K, hK, hlevel⟩ := hlevel ε hε
      refine ⟨C, hC, K, hK, ?_⟩
      have hpoint : -levelExponent 2 (n - σ) 2 h = -((n - σ : ℕ) : ℝ) * h := by
        simp [levelExponent, neg_mul]
      have hexcept : exceptionExponent 2 2 h = 4 * h := by
        norm_num [exceptionExponent]
      simpa only [hpoint, hexcept, Nat.cast_ofNat] using hlevel
  · have hd₃ : 3 ≤ d := by omega
    exact v2MetricDistribution_of_completion hd₃
      (v2CompletionEstimate_of_terminalPrimeBounds (by omega) hd₃ hF hσ hw hwbox hPrime)

theorem v2MetricDistribution_of_weilII {n d σ : ℕ} {F : IntForm n}
    (hν : 0 < n - σ) (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    V2MetricDistribution circleMeasure d (n - σ)
      (fun P α => ENNReal.ofReal ‖normalizedSum F w P α‖) :=
  v2MetricDistribution_of_terminalPrimeBounds hν hd hF hσ hw hwbox (TerminalPrimeBounds.of_deligne hWeilII)

/-- The trivial bound for the normalized form sum at every frequency. -/
theorem norm_normalizedSum_eventually_bounded {n : ℕ} (F : IntForm n)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop, ∀ α, ‖normalizedSum F w P α‖ ≤ C := by
  obtain ⟨B, hB⟩ := hw.compact.exists_bound_of_continuous hw.smooth.continuous
  let K : ℝ := max 1 B
  have hK : 0 < K := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨K * 3^n, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP α
  have hp : 0 < P := zero_lt_one.trans_le hP
  have he : ‖exponentialSum F w P α‖ ≤ K * (3 * P)^n := by
    unfold exponentialSum
    calc
      _ ≤ ∑ _x ∈ latticeBox n P, K := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro x _
        rw [norm_mul, norm_phase, mul_one, Complex.norm_real]
        exact (hB _).trans (le_max_right _ _)
      _ = K * ((latticeBox n P).card : ℝ) := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left (card_latticeBox_between n hP).2 hK.le
  rw [normalizedSum, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _),
    Real.rpow_neg hp.le, Real.rpow_natCast, inv_mul_eq_div]
  refine (div_le_div_of_nonneg_right he (by positivity)).trans_eq ?_
  rw [mul_pow, ← mul_assoc, mul_div_cancel_right₀ _ (pow_ne_zero _ hp.ne')]

/-- The critical full-circle moment follows from the form's level estimates. -/
private theorem v2CriticalMoment_of_formMetric {n d σ : ℕ} {F : IntForm n}
    (hν : 0 < n - σ) (hd : 2 ≤ d) {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w)
    (hmetric : V2MetricDistribution circleMeasure d (n - σ)
      (fun P α => ENNReal.ofReal ‖normalizedSum F w P α‖)) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖normalizedSum F w P α‖ ^
        criticalMomentExponent d (n - σ) ∂circleMeasure) (-(d : ℝ) + ε) := by
  apply criticalMoment_of_metric hd hν circleMeasure
  · intro P
    unfold normalizedSum
    exact ((continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)).norm.measurable.ennreal_ofReal
  · obtain ⟨C, hC, hbound⟩ := norm_normalizedSum_eventually_bounded F hw
    exact ⟨C.toNNReal, Real.toNNReal_pos.2 hC,
      hbound.mono fun P hP α => by
        rw [ENNReal.ofNNReal_toNNReal]
        exact ENNReal.ofReal_le_ofReal (hP α)⟩
  · exact hmetric

/-- The critical moment follows from terminal completion in degree at least three. -/
theorem v2CriticalMoment_of_completion {n d σ : ℕ} {F : IntForm n}
    (hν : 0 < n - σ) (hd : 3 ≤ d) {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w)
    (hcompletion : CompletionEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖)) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖normalizedSum F w P α‖ ^
        criticalMomentExponent d (n - σ) ∂circleMeasure) (-(d : ℝ) + ε) :=
  v2CriticalMoment_of_formMetric hν (by omega) hw (v2MetricDistribution_of_completion hd hcompletion)

/-- The critical full-circle moment from the uniform terminal estimates. -/
theorem v2CriticalMoment_of_terminalPrimeBounds {n d σ : ℕ} {F : IntForm n}
    (hν : 0 < n - σ) (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    (hPrime : TerminalPrimeBounds d) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖normalizedSum F w P α‖ ^
        criticalMomentExponent d (n - σ) ∂circleMeasure) (-(d : ℝ) + ε) :=
  v2CriticalMoment_of_formMetric hν hd hw
    (v2MetricDistribution_of_terminalPrimeBounds hν hd hF hσ hw.smooth hwbox hPrime)

/-- The critical full-circle moment at the reduced gradient codimension. -/
def FormCriticalMomentBounds (d : ℕ) : Prop :=
  ∀ {n σ : ℕ} {F : IntForm n}, 0 < n - σ → 2 ≤ d →
    F.IsHomogeneous d → RationalGradientDimension F σ →
    ∀ {w : (Fin n → ℝ) → ℝ}, CompactWeight w → CubeSupported w →
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖normalizedSum F w P α‖ ^
        criticalMomentExponent d (n - σ) ∂circleMeasure) (-(d : ℝ) + ε)

theorem FormCriticalMomentBounds.of_terminalPrimeBounds {d : ℕ}
    (hPrime : TerminalPrimeBounds d) : FormCriticalMomentBounds d := by
  intro n σ F hν hd hF hσ w hw hwbox
  exact v2CriticalMoment_of_terminalPrimeBounds hν hd hF hσ hw hwbox hPrime

/-- Arbitrarily small terminal losses give the full critical-moment estimate at the same exponent. -/
theorem FormCriticalMomentBounds.of_terminalPrimeBoundsWithLoss {d : ℕ}
    (hPrime : ∀ δ : ℝ, 0 < δ → TerminalPrimeBoundsWithLoss d δ) :
    FormCriticalMomentBounds d := by
  intro n σ F hν hd hF hσ w hw hwbox
  by_cases hd₂ : d = 2
  · subst d
    exact v2CriticalMoment_of_terminalPrimeBounds hν hd hF hσ hw hwbox
      (by intro r hr hrd; omega)
  have hd₃ : 3 ≤ d := by omega
  apply criticalMoment_of_scaledMetric hd hν circleMeasure
  · intro P
    unfold normalizedSum
    exact ((continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)).norm.measurable.ennreal_ofReal
  · obtain ⟨C, hC, hbound⟩ := norm_normalizedSum_eventually_bounded F hw
    exact ⟨C.toNNReal, Real.toNNReal_pos.2 hC,
      hbound.mono fun P hP α => by
        rw [ENNReal.ofNNReal_toNNReal]
        exact ENNReal.ofReal_le_ofReal (hP α)⟩
  · intro ζ hζ
    have hδ : 0 < ζ/2 := by positivity
    have hCompletion := v2CompletionEstimateWithPrimeLoss (by omega) hd₃ hF hσ hw.smooth hwbox
      hδ.le (hPrime (ζ/2) hδ)
    simpa only [show 2 * (ζ / 2) = ζ by ring, ENNReal.ofReal_mul' (norm_nonneg _)] using
      v2MetricDistribution_of_completion hd₃ (hCompletion.scaled hδ.le)

theorem v2CriticalMoment_of_weilII {n d σ : ℕ} {F : IntForm n}
    (hν : 0 < n - σ) (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖normalizedSum F w P α‖ ^
        criticalMomentExponent d (n - σ) ∂circleMeasure) (-(d : ℝ) + ε) :=
  v2CriticalMoment_of_terminalPrimeBounds hν hd hF hσ hw hwbox (TerminalPrimeBounds.of_deligne hWeilII)

end

end Birch
