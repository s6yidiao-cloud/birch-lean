import Birch.V2Covers
import Birch.V2FormMoments
import Birch.V2WeylMinor
import Birch.V2CoverHua

/-! # The cover moment and its minor-arc consequence -/

open Filter MeasureTheory
open scoped ENNReal NNReal Polynomial Topology

namespace Birch

noncomputable section

/-- The one-variable moment of the signed interval sum in v2, before
rescaling the interval to the form variable's scale. -/
def CoverMeanValueBoundAtExponent (e q : ℕ) (g : ℤ[X]) : Prop :=
  ∀ ε > 0, coverPowerBound
    (fun L => ∫⁻ α, ENNReal.ofReal ‖coverYSum g L α‖ ^ (q : ℝ) ∂circleMeasure)
    ((q : ℝ) - e + ε)

/-- The cover moment at the exponent selected in `v2.tex`. -/
def CoverMeanValueBound (e : ℕ) (g : ℤ[X]) : Prop :=
  CoverMeanValueBoundAtExponent e (coverMomentExponent e) g

theorem coverMeanValueBound_quadratic {g : ℤ[X]} (hg : g.natDegree = 2) :
    CoverMeanValueBound 2 g := by
  intro ε hε
  simpa using coverYSum_coverMoment_quadratic (d := 2) (by decide) g hg ε hε

/-- Hua's moment gives the exact selected exponent for cover degrees two
through four. -/
theorem coverMeanValueBound_of_degree_le_four {e : ℕ} {g : ℤ[X]}
    (he : 2 ≤ e) (he₄ : e ≤ 4) (hg : g.natDegree = e) : CoverMeanValueBound e g := by
  intro ε hε
  have he₀ : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  simpa only [div_self he₀, Real.rpow_one, one_mul] using
    coverYSum_coverMoment_of_le_four (d := e) (by omega) he he₄ g hg ε hε

/-- Hua's exponent is available for every cover degree at least two. -/
theorem coverMeanValueBoundAtExponent_hua {e : ℕ} {g : ℤ[X]}
    (he : 2 ≤ e) (hg : g.natDegree = e) : CoverMeanValueBoundAtExponent e (2 ^ e) g := by
  intro ε hε
  have he₀ : (e : ℝ) ≠ 0 := by exact_mod_cast (show e ≠ 0 by omega)
  simpa only [div_self he₀, Real.rpow_one, one_mul] using
    coverYSum_huaMoment (d := e) (by omega) he g hg (C := 1) le_rfl ε hε

/-- A fixed positive multiplier of the natural radius leaves the exponent
in the polynomial moment unchanged. -/
theorem CoverMeanValueBoundAtExponent.rescale {d e q : ℕ} {g : ℤ[X]}
    (hm : CoverMeanValueBoundAtExponent e q g)
    (hd : 0 < d) (he : 0 < e) {B : ℝ} (hB : 0 < B) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖coverYSum g (B * P ^ ((d : ℝ) / e)) α‖ ^
        (q : ℝ) ∂circleMeasure)
      ((d : ℝ) / e * q - d + ε) := by
  intro ε hε
  let k := (d : ℝ) / e
  have hk : 0 < k := div_pos (by exact_mod_cast hd) (by exact_mod_cast he)
  let a := (q : ℝ) - e + ε / k
  obtain ⟨C, hC, hbound⟩ := hm (ε / k) (div_pos hε hk)
  let D := C * (B ^ a).toNNReal
  have hBa : 0 < B ^ a := Real.rpow_pos_of_pos hB _
  have hD : 0 < D := mul_pos hC (Real.toNNReal_pos.2 hBa)
  refine ⟨D, hD, ?_⟩
  have ht := Tendsto.const_mul_atTop hB (tendsto_rpow_atTop hk)
  filter_upwards [ht.eventually hbound, eventually_gt_atTop (0 : ℝ)] with P hP hp
  refine hP.trans_eq ?_
  have heq : k * a = k * q - d + ε := by
    dsimp only [a]
    rw [mul_add, mul_sub, mul_div_cancel₀ _ hk.ne']
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    rw [show k * (e : ℝ) = d from div_mul_cancel₀ _ he']
  change (C : ℝ≥0∞) * ENNReal.ofReal ((B * P ^ k) ^ a) =
    (D : ℝ≥0∞) * ENNReal.ofReal (P ^ (k * q - d + ε))
  rw [Real.mul_rpow hB.le (Real.rpow_nonneg hp.le _), ← Real.rpow_mul hp.le, heq,
    ENNReal.ofReal_mul hBa.le, ← mul_assoc]
  simp only [D, ENNReal.coe_mul, ENNReal.ofNNReal_toNNReal]

/-- Rescale the cover moment at the exponent selected in `v2.tex`. -/
theorem CoverMeanValueBound.rescale {d e : ℕ} {g : ℤ[X]} (hm : CoverMeanValueBound e g)
    (hd : 0 < d) (he : 0 < e) {B : ℝ} (hB : 0 < B) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ α, ENNReal.ofReal ‖coverYSum g (B * P ^ ((d : ℝ) / e)) α‖ ^
        (coverMomentExponent e : ℝ) ∂circleMeasure)
      ((d : ℝ) / e * coverMomentExponent e - d + ε) :=
  CoverMeanValueBoundAtExponent.rescale hm hd he hB

/-- The major-arc cutoff used for the polynomial-cover theorem of v2. -/
def coverMajorArcExponent (d e : ℕ) : ℝ := min 1 ((d : ℝ) / e) / 12

theorem coverMajorArcExponent_pos {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    0 < coverMajorArcExponent d e :=
  div_pos (lt_min zero_lt_one (div_pos (by exact_mod_cast hd) (by exact_mod_cast he))) (by norm_num)

theorem coverMajorArcExponent_lt_quarter (d e : ℕ) :
    coverMajorArcExponent d e < 1 / 4 :=
  lt_of_le_of_lt (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) (by norm_num)

/-- The cover minor-arc estimate from the form moment and a one-variable
moment of exponent `q`. -/
theorem v2CoverMinorIntegral_of_formCriticalMoments_atExponent {d e q n σ : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hq : 1 < q)
    (hν : (1 - 1 / (q : ℝ)) * dimensionThreshold d < (n - σ : ℕ))
    (hCritical : FormCriticalMomentBounds d) :
    ∃ δ > 0, ∀ (F : IntForm n) (g : ℤ[X]) (w : (Fin n → ℝ) → ℝ),
      F.IsHomogeneous d → RationalGradientDimension F σ → CompactWeight w →
      CubeSupported w → CoverMeanValueBoundAtExponent e q g → ∀ B > 0, ∃ C > 0,
      ∀ᶠ P : ℝ in atTop,
        (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
          ‖normalizedSum F w P α * coverYSum g (B * P ^ ((d : ℝ) / e)) α‖ ∂circleMeasure) ≤
          C * P ^ ((d : ℝ) / e - d - δ) := by
  have hν' := hν
  rw [cast_dimensionThreshold_eq_minorDimensionThreshold hd] at hν'
  have hm : (1 : ℝ) < q := by exact_mod_cast hq
  have hν₀ : 0 < n - σ := by
    have hr : 0 ≤ 1 - 1 / (q : ℝ) :=
      sub_nonneg.mpr (by
        simpa using one_div_le_one_div_of_le zero_lt_one hm.le)
    have hnD : 0 ≤ minorDimensionThreshold d := (minorDimensionThreshold_pos hd).le
    exact_mod_cast (show (0 : ℝ) < ↑(n - σ) from (mul_nonneg hr hnD).trans_lt hν')
  let Δ := coverMajorArcExponent d e
  obtain ⟨τ, hτ, hpointwise⟩ := initialMinor_of_weyl_v2 hd
    (coverMajorArcExponent_pos (by omega : 0 < d) (by omega : 0 < e))
    (coverMajorArcExponent_lt_quarter d e)
  obtain ⟨δ, hδ, hminor⟩ := coverMinorArcBound_of_criticalMoment_atExponent (e := e) hd hm hν' hτ
  refine ⟨δ, hδ, ?_⟩
  intro F g w hF hσ hw hwbox hg B hB
  let f := fun P α => ENNReal.ofReal ‖normalizedSum F w P α‖
  let t := fun P α => ENNReal.ofReal ‖coverYSum g (B * P ^ ((d : ℝ) / e)) α‖
  have hfc (P : ℝ) : Continuous (normalizedSum F w P) :=
    (continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)
  have htc (P : ℝ) : Continuous (coverYSum g (B * P ^ ((d : ℝ) / e))) := continuous_coverYSum g _
  have hform := hCritical hν₀ hd hF hσ hw hwbox
  obtain ⟨A, hA, hAarc⟩ := hpointwise hν₀ (v2WeylEstimate hν₀ hd hF hσ hw.smooth hwbox)
  let m := fun P => (v2MajorArcs d Δ P)ᶜ
  have hweyl : ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ α ∈ m P,
      f P α ≤ (C : ℝ≥0∞) * ENNReal.ofReal (P ^ (-τ)) := by
    refine ⟨A.toNNReal, Real.toNNReal_pos.2 hA, hAarc.mono ?_⟩
    intro P hP α hα
    rw [ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_mul hA.le]
    exact ENNReal.ofReal_le_ofReal (hP α hα)
  have hmoment := hminor circleMeasure m f t (fun P => (measurableSet_v2MajorArcs d Δ P).compl)
    (fun P => (hfc P).norm.measurable.ennreal_ofReal)
    (fun P => (htc P).norm.measurable.ennreal_ofReal)
    hform hweyl (hg.rescale (by omega : 0 < d) (by omega : 0 < e) hB)
  obtain ⟨C, hC, hbound⟩ := hmoment.toReal
  refine ⟨C, hC, hbound.mono fun P hP => ?_⟩
  have hcont : Continuous (fun α => normalizedSum F w P α * coverYSum g (B * P ^ ((d : ℝ) / e)) α) :=
    (hfc P).mul (htc P)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => norm_nonneg _)
    hcont.norm.aestronglyMeasurable]
  simp_rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  exact hP

theorem v2CoverMinorIntegral_of_terminalPrimeBounds_atExponent {d e q n σ : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hq : 1 < q)
    (hν : (1 - 1 / (q : ℝ)) * dimensionThreshold d < (n - σ : ℕ))
    (hPrime : TerminalPrimeBounds d) :
    ∃ δ > 0, ∀ (F : IntForm n) (g : ℤ[X]) (w : (Fin n → ℝ) → ℝ),
      F.IsHomogeneous d → RationalGradientDimension F σ → CompactWeight w →
      CubeSupported w → CoverMeanValueBoundAtExponent e q g → ∀ B > 0, ∃ C > 0,
      ∀ᶠ P : ℝ in atTop,
        (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
          ‖normalizedSum F w P α * coverYSum g (B * P ^ ((d : ℝ) / e)) α‖ ∂circleMeasure) ≤
          C * P ^ ((d : ℝ) / e - d - δ) :=
  v2CoverMinorIntegral_of_formCriticalMoments_atExponent hd he hq hν
    (FormCriticalMomentBounds.of_terminalPrimeBounds hPrime)

theorem v2CoverMinorIntegral_of_weilII_atExponent {d e q n σ : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hq : 1 < q)
    (hν : (1 - 1 / (q : ℝ)) * dimensionThreshold d < (n - σ : ℕ))
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    ∃ δ > 0, ∀ (F : IntForm n) (g : ℤ[X]) (w : (Fin n → ℝ) → ℝ),
      F.IsHomogeneous d → RationalGradientDimension F σ → CompactWeight w →
      CubeSupported w → CoverMeanValueBoundAtExponent e q g → ∀ B > 0, ∃ C > 0,
      ∀ᶠ P : ℝ in atTop,
        (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
          ‖normalizedSum F w P α * coverYSum g (B * P ^ ((d : ℝ) / e)) α‖ ∂circleMeasure) ≤
          C * P ^ ((d : ℝ) / e - d - δ) :=
  v2CoverMinorIntegral_of_terminalPrimeBounds_atExponent hd he hq hν (TerminalPrimeBounds.of_deligne hWeilII)

/-- The minor-arc estimate at the exponent selected in `v2.tex`. -/
theorem v2CoverMinorIntegral_of_weilII {d e n σ : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e)
    (hν : (1 - 1 / (coverMomentExponent e : ℝ)) * dimensionThreshold d < (n - σ : ℕ))
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    ∃ δ > 0, ∀ (F : IntForm n) (g : ℤ[X]) (w : (Fin n → ℝ) → ℝ),
      F.IsHomogeneous d → RationalGradientDimension F σ → CompactWeight w →
      CubeSupported w → CoverMeanValueBound e g → ∀ B > 0, ∃ C > 0,
      ∀ᶠ P : ℝ in atTop,
        (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
          ‖normalizedSum F w P α * coverYSum g (B * P ^ ((d : ℝ) / e)) α‖ ∂circleMeasure) ≤
          C * P ^ ((d : ℝ) / e - d - δ) :=
  v2CoverMinorIntegral_of_weilII_atExponent hd he (one_lt_coverMomentExponent he) hν hWeilII

/-- Hua and Weil II give the cover minor-arc estimate above Hua's
codimension threshold for every degree `e ≥ 2`. -/
theorem v2CoverMinorIntegral_of_weilII_of_huaThreshold {d e n σ : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e)
    (hν : (1 - 1 / ((2 ^ e : ℕ) : ℝ)) * dimensionThreshold d < (n - σ : ℕ))
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    ∃ δ > 0, ∀ (F : IntForm n) (g : ℤ[X]) (w : (Fin n → ℝ) → ℝ),
      F.IsHomogeneous d → g.natDegree = e → RationalGradientDimension F σ →
      CompactWeight w → CubeSupported w → ∀ B > 0, ∃ C > 0,
      ∀ᶠ P : ℝ in atTop,
        (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
          ‖normalizedSum F w P α * coverYSum g (B * P ^ ((d : ℝ) / e)) α‖ ∂circleMeasure) ≤
          C * P ^ ((d : ℝ) / e - d - δ) := by
  have hq : 1 < 2 ^ e := (lt_of_lt_of_le (by decide) he).trans_le Nat.lt_two_pow_self.le
  obtain ⟨δ, hδ, hminor⟩ := v2CoverMinorIntegral_of_weilII_atExponent hd he hq hν hWeilII
  refine ⟨δ, hδ, ?_⟩
  intro F g w hF hg hσ hw hwbox
  exact hminor F g w hF hσ hw hwbox (coverMeanValueBoundAtExponent_hua he hg)

end

end Birch
