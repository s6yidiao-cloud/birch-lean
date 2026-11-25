import Birch.V2FormMoments
import Birch.V2MajorArcShells

/-! # Assembly at the sharp form threshold in v2 -/

open Filter MeasureTheory
open scoped ContDiff ENNReal NNReal Topology

namespace Birch

noncomputable section

def v2FormMinorSaving (d ν : ℕ) : ℝ :=
  weylSaving d ν * (1 - criticalMomentExponent d ν) / 2

theorem v2FormMinorSaving_pos {d ν : ℕ} (hd : 2 ≤ d) (hν : dimensionThreshold d < ν) :
    0 < v2FormMinorSaving d ν := by
  have hν₀ := Nat.zero_lt_of_lt hν
  have hcast : (dimensionThreshold d : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  rw [cast_dimensionThreshold_eq_minorDimensionThreshold hd] at hcast
  have h : criticalMomentExponent d ν < 1 :=
    (div_lt_one (by exact_mod_cast hν₀)).2 hcast
  exact div_pos (mul_pos (weylSaving_pos hd hν₀) (sub_pos.mpr h)) (by norm_num)

/-- The (L^1) minor-arc estimate for forms at the sharp singular codimension. -/
private theorem v2FormMinorIntegral_of_criticalMoment {n d σ : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hν : dimensionThreshold d < n - σ)
    {w : (Fin n → ℝ) → ℝ}
    (hWeyl : WeylEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖))
    (hcritical : ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖normalizedSum F w P α‖ ^
        criticalMomentExponent d (n - σ) ∂circleMeasure) (-(d : ℝ) + ε)) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤
        C * P ^ (-(d : ℝ) - v2FormMinorSaving d (n - σ)) := by
  have hν₀ := Nat.zero_lt_of_lt hν
  have hcast : (dimensionThreshold d : ℝ) < ((n - σ : ℕ) : ℝ) := by exact_mod_cast hν
  rw [cast_dimensionThreshold_eq_minorDimensionThreshold hd] at hcast
  have ht : criticalMomentExponent d (n - σ) < 1 :=
    (div_lt_one (by exact_mod_cast hν₀)).2 hcast
  let f := fun P α => ENNReal.ofReal ‖normalizedSum F w P α‖
  obtain ⟨B, hB, hbound⟩ := initialMinor_of_weyl hd hν₀ hWeyl
  have hW : ∃ C : ℝ≥0, 0 < C ∧
      ∀ᶠ P in atTop, ∀ α ∈ (majorArcs d P)ᶜ,
        f P α ≤ (C : ℝ≥0∞) * ENNReal.ofReal (P ^ (-weylSaving d (n-σ))) := by
    refine ⟨B.toNNReal, Real.toNNReal_pos.2 hB, hbound.mono ?_⟩
    intro P hP α hα
    rw [ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_mul hB.le]
    exact ENNReal.ofReal_le_ofReal (hP α hα)
  have hmoment := minorMoment_of_criticalMoment (criticalMomentExponent_pos hd hν₀) ht
    (weylSaving_pos hd hν₀) circleMeasure (fun P => (majorArcs d P)ᶜ)
    f (fun P => (measurableSet_majorArcs d P).compl) hW
    hcritical
  obtain ⟨C, hC, hbound⟩ := hmoment.toReal
  refine ⟨C, hC, hbound.mono fun P hP => ?_⟩
  have hcont : Continuous (normalizedSum F w P) :=
    (continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)
  simp only [ENNReal.rpow_one, f] at hP
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
    hcont.norm.aestronglyMeasurable]
  exact hP

theorem v2FormMinorIntegral_of_formCriticalMoments {n d σ : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    (hν : dimensionThreshold d < n - σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    (hCritical : FormCriticalMomentBounds d) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤
        C * P ^ (-(d : ℝ) - v2FormMinorSaving d (n - σ)) :=
  v2FormMinorIntegral_of_criticalMoment hd hν
    (v2WeylEstimate (by omega) hd hF hσ hw.smooth hwbox)
    (hCritical (by omega) hd hF hσ hw hwbox)

theorem v2FormMinorIntegral_of_terminalPrimeBounds {n d σ : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    (hν : dimensionThreshold d < n - σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    (hPrime : TerminalPrimeBounds d) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤
        C * P ^ (-(d : ℝ) - v2FormMinorSaving d (n - σ)) :=
  v2FormMinorIntegral_of_formCriticalMoments hd hF hσ hν hw hwbox
    (FormCriticalMomentBounds.of_terminalPrimeBounds hPrime)

theorem v2FormMinorIntegral_of_weilII {n d σ : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    (hν : dimensionThreshold d < n - σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤
        C * P ^ (-(d : ℝ) - v2FormMinorSaving d (n - σ)) :=
  v2FormMinorIntegral_of_terminalPrimeBounds hd hF hσ hν hw hwbox (TerminalPrimeBounds.of_deligne hWeilII)

def v2FormSaving (d ν : ℕ) : ℝ :=
  min (v2FormMinorSaving d ν) (min 1 (v2FormMinorSaving d ν / (2 / 3) / 2))

theorem v2FormSaving_pos {d ν : ℕ} (hd : 2 ≤ d) (hν : dimensionThreshold d < ν) :
    0 < v2FormSaving d ν := by
  have hδ := v2FormMinorSaving_pos hd hν
  exact lt_min hδ (lt_min zero_lt_one (by positivity))

/-- The sharp weighted asymptotic for a transverse weight in the unit cube.
The conductor tail is obtained from the minor-arc estimate. -/
theorem v2CubeFormAsymptotic_of_formCriticalMoments {n d σ : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    (hν : dimensionThreshold d < n - σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w)
    (hwbox : CubeSupported w) (htrans : HasTransverseSupport F w)
    (hCritical : FormCriticalMomentBounds d) :
    Summable (fun q : ℕ => formConductorMass F (q+1)) ∧ Integrable (realOscillation F w) ∧
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(weightedZeros F w P : ℂ) -
        (P ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * P ^ ((n : ℝ) - d - v2FormSaving d (n - σ)) := by
  have hsaving := v2FormMinorSaving_pos hd hν
  have hminor := v2FormMinorIntegral_of_formCriticalMoments hd hF hσ hν hw hwbox hCritical
  have hmass := formConductorMass_tail_of_minorArcs_atExponent hd hF hsaving
    (fun u hs hc hn hb => v2FormMinorIntegral_of_formCriticalMoments hd hF hσ hν ⟨hs, hc, hn⟩ hb hCritical)
  obtain ⟨hseries, htail⟩ := formSingularSeries_tail_of_conductorMass_tail hmass
  have hγ : 0 < v2FormMinorSaving d (n - σ) / (2 / 3 : ℝ) := by positivity
  obtain ⟨hI, hmajor⟩ := formMajorArcIntegral_bound_of_absoluteTail hd hF hw.smooth
    hw.compact hwbox htrans hγ hseries htail
  exact ⟨hmass.1, hI, weightedAsymptoticBound_of_arcIntegrals hminor hmajor⟩

theorem v2CubeFormAsymptotic_of_terminalPrimeBounds {n d σ : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    (hν : dimensionThreshold d < n - σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w)
    (hwbox : CubeSupported w) (htrans : HasTransverseSupport F w)
    (hPrime : TerminalPrimeBounds d) :
    Summable (fun q : ℕ => formConductorMass F (q+1)) ∧ Integrable (realOscillation F w) ∧
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(weightedZeros F w P : ℂ) -
        (P ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * P ^ ((n : ℝ) - d - v2FormSaving d (n - σ)) :=
  v2CubeFormAsymptotic_of_formCriticalMoments hd hF hσ hν hw hwbox htrans
    (FormCriticalMomentBounds.of_terminalPrimeBounds hPrime)

theorem v2CubeFormAsymptotic_of_weilII {n d σ : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ)
    (hν : dimensionThreshold d < n - σ)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w)
    (hwbox : CubeSupported w) (htrans : HasTransverseSupport F w)
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    Summable (fun q : ℕ => formConductorMass F (q+1)) ∧ Integrable (realOscillation F w) ∧
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(weightedZeros F w P : ℂ) -
        (P ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * P ^ ((n : ℝ) - d - v2FormSaving d (n - σ)) :=
  v2CubeFormAsymptotic_of_terminalPrimeBounds hd hF hσ hν hw hwbox htrans (TerminalPrimeBounds.of_deligne hWeilII)

end

end Birch
