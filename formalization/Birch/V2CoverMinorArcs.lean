import Birch.MinorArcs
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Moments for the polynomial-cover argument

The critical moment and its minor-arc consequence in Proposition `prop:minor`
of `v2.tex` are stated on an arbitrary probability space. Here `ν` is the
singular codimension and the function is the normalized magnitude of the
exponential sum. The metric estimate and the initial Weyl saving are explicit
inputs.
-/

namespace Birch

open Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section

universe u

/-- The critical exponent in Proposition `prop:minor` of `v2.tex`. -/
def criticalMomentExponent (d ν : ℕ) : ℝ := minorDimensionThreshold d / ν

/-- A bound of order `P ^ a` for a nonnegative quantity as `P → ∞`. -/
def coverPowerBound (I : ℝ → ℝ≥0∞) (a : ℝ) : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, I P ≤ (C : ℝ≥0∞) * ENNReal.ofReal (P ^ a)

/-- The levels for the moment proof include direct completion in degree two. -/
def FinalMetricLevelAdmissible (d r : ℕ) (h : ℝ) : Prop :=
  levelAdmissible d r h ∨ (d = 2 ∧ r = 2 ∧ 0 < h ∧ h ≤ 1 / 2)

/-- The superlevel-set formulation of Proposition `prop:metric` of `v2.tex`. -/
def V2MetricDistribution {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (d ν : ℕ) (f : ℝ → Ω → ℝ≥0∞) : Prop :=
  ∀ r h, FinalMetricLevelAdmissible d r h → ∀ ε > 0, ∃ C : ℝ≥0, 0 < C ∧
    coverPowerBound
      (fun P => μ {x | (C : ℝ≥0∞) * ENNReal.ofReal (P ^ (-levelExponent d ν r h)) < f P x})
      (-(d : ℝ) + exceptionExponent d r h + ε)

private abbrev powerScale (P a : ℝ) : ℝ≥0∞ := ENNReal.ofReal (P ^ a)

private theorem scale_mul {P : ℝ} (hP : 0 < P) (a b : ℝ) :
    powerScale P a * powerScale P b = powerScale P (a + b) := by
  unfold powerScale
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hP.le a), Real.rpow_add hP]

private theorem scale_rpow {P q : ℝ} (hP : 0 ≤ P) (hq : 0 ≤ q) (a : ℝ) :
    powerScale P a ^ q = powerScale P (a * q) := by
  unfold powerScale
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hP a) hq, ← Real.rpow_mul hP]

private theorem scale_mono {P a b : ℝ} (hP : 1 ≤ P) (h : a ≤ b) :
    powerScale P a ≤ powerScale P b :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hP h)

/-- Real positive constants give the same power bounds for nonnegative quantities. -/
theorem coverPowerBound_of_realConstant {I : ℝ → ℝ≥0∞} {a : ℝ}
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ P in atTop, I P ≤ ENNReal.ofReal (C * P ^ a)) :
    coverPowerBound I a := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C.toNNReal, Real.toNNReal_pos.2 hC,
    h.mono fun _ hP => by simpa [ENNReal.ofNNReal_toNNReal, ENNReal.ofReal_mul hC.le] using hP⟩

/-- An `ENNReal` power bound gives an ordinary real bound after taking `toReal`. -/
theorem coverPowerBound.toReal {I : ℝ → ℝ≥0∞} {a : ℝ} (h : coverPowerBound I a) :
    ∃ C > 0, ∀ᶠ P in atTop, (I P).toReal ≤ C * P ^ a := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨(C : ℝ), NNReal.coe_pos.2 hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with P hP hPone
  have hP₀ : 0 ≤ P := by linarith
  have hfinite : (C : ℝ≥0∞) * powerScale P a ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  simpa [powerScale, ENNReal.toReal_mul, Real.rpow_nonneg hP₀] using ENNReal.toReal_mono hfinite hP

/-- Passing from a normalized power bound to its original power scale. -/
theorem coverPowerBound.scale {I : ℝ → ℝ≥0∞} {a : ℝ} (h : coverPowerBound I a) (b : ℝ) :
    coverPowerBound (fun P => ENNReal.ofReal (P ^ b) * I P) (b + a) := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with P hP hPone
  have hPpos : 0 < P := by linarith
  calc
    _ ≤ powerScale P b * ((C : ℝ≥0∞) * powerScale P a) := mul_le_mul_right hP _
    _ = (C : ℝ≥0∞) * (powerScale P b * powerScale P a) := by ac_rfl
    _ = _ := by rw [scale_mul hPpos]

/-- The metric estimate on a real magnitude gives the `ENNReal` tail interface. -/
theorem V2MetricDistribution.ofReal {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
    {d ν : ℕ} {f : ℝ → Ω → ℝ}
    (h : ∀ r h, FinalMetricLevelAdmissible d r h → ∀ ε > 0, ∃ C > 0, ∃ K > 0,
      ∀ᶠ P in atTop,
        μ {x | C * P ^ (-levelExponent d ν r h) < f P x} ≤
          ENNReal.ofReal (K * P ^ (-(d : ℝ) + exceptionExponent d r h + ε))) :
    V2MetricDistribution μ d ν (fun P x => ENNReal.ofReal (f P x)) := by
  intro r h' hr ε hε
  obtain ⟨C, hC, K, hK, h⟩ := h r h' hr ε hε
  refine ⟨C.toNNReal, Real.toNNReal_pos.2 hC, ?_⟩
  apply coverPowerBound_of_realConstant
  refine ⟨K, hK, ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with P hP hPone
  have hP₀ : 0 ≤ P := by linarith
  simp only [ENNReal.ofNNReal_toNNReal, ← ENNReal.ofReal_mul hC.le,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hP₀ _))]
  exact hP

/-- The top endpoint in Lemma `lem:bookkeeping` of `v2.tex`. -/
theorem degree_le_threshold_div_four {d : ℕ} (hd : 3 ≤ d) :
    (d : ℝ) ≤ minorDimensionThreshold d / 4 := by
  unfold minorDimensionThreshold
  have h : 4 * ((d : ℝ) + 1) ≤ (2 : ℝ) ^ (d + 1) := by
    induction d, hd using Nat.le_induction with
    | base => norm_num
    | succ d hd ih =>
      rw [pow_succ, Nat.cast_succ]
      have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
  linarith

theorem minorDimensionThreshold_pos {d : ℕ} (hd : 2 ≤ d) : 0 < minorDimensionThreshold d := by
  by_cases h₂ : d = 2
  · norm_num [h₂, minorDimensionThreshold]
  · have h₃ : 3 ≤ d := by omega
    have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    linarith [degree_le_threshold_div_four h₃]

theorem criticalMomentExponent_pos {d ν : ℕ} (hd : 2 ≤ d) (hν : 0 < ν) :
    0 < criticalMomentExponent d ν := by
  exact div_pos (minorDimensionThreshold_pos hd) (by exact_mod_cast hν)

private theorem criticalMomentLevel {d ν : ℕ} (hd : 2 ≤ d) (hν : 0 < ν)
    {z : ℝ} (hz : 0 < z) (hzle : z ≤ d) :
    ∃ r h, FinalMetricLevelAdmissible d r h ∧
      levelExponent d ν r h = z / criticalMomentExponent d ν ∧ exceptionExponent d r h ≤ z := by
  let t := criticalMomentExponent d ν
  have ht : 0 < t := criticalMomentExponent_pos hd hν
  have hν' : (0 : ℝ) < ν := by exact_mod_cast hν
  by_cases h₂ : d = 2
  · subst d
    norm_num only [Nat.cast_ofNat] at hzle
    refine ⟨2, z / 4, Or.inr ⟨rfl, rfl, by positivity, by linarith⟩, ?_, ?_⟩
    · norm_num [levelExponent, criticalMomentExponent, minorDimensionThreshold]
      field_simp [hν'.ne']
    · norm_num [exceptionExponent]
      linarith
  · have h₃ : 3 ≤ d := by omega
    have htop : z / t ≤ (ν : ℝ) / 4 := by
      apply (div_le_iff₀ ht).2
      have hcalc : (ν : ℝ) / 4 * t = minorDimensionThreshold d / 4 := by
        dsimp [t, criticalMomentExponent]
        field_simp [hν'.ne']
      rw [hcalc]
      exact hzle.trans (degree_le_threshold_div_four h₃)
    obtain ⟨r, h, hlevel, heq⟩ := minorLevels h₃ hν (div_pos hz ht) htop
    refine ⟨r, h, Or.inl hlevel, heq, (exceptionExponent_le hν hlevel).trans_eq ?_⟩
    rw [heq]
    change t * (z / t) = z
    rw [mul_comm, div_mul_cancel₀ _ ht.ne']

/-- The critical full-circle moment, Equation `eq:full-moment` of `v2.tex`,
from the superlevel-set estimate and the uniform trivial bound. -/
theorem criticalMoment_of_metric {d ν : ℕ} (hd : 2 ≤ d) (hν : 0 < ν)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ P, Measurable (f P))
    (htriv : ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, f P x ≤ (C : ℝ≥0∞))
    (hmetric : V2MetricDistribution μ d ν f) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ x, f P x ^ criticalMomentExponent d ν ∂μ) (-(d : ℝ) + ε) := by
  classical
  intro ε hε
  let t := criticalMomentExponent d ν
  have ht : 0 < t := criticalMomentExponent_pos hd hν
  let A : ℝ := d
  have hA : 0 < A := Nat.cast_pos.mpr (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (A / (ε / 2))
  have hNpos : (0 : ℝ) < N := (div_pos hA (by positivity)).trans hN
  let δ := A / N
  have hδ : 0 < δ := div_pos hA hNpos
  have hδε : δ < ε / 2 := by
    apply (div_lt_iff₀ hNpos).2
    simpa [mul_comm] using (div_lt_iff₀ (show 0 < ε / 2 by positivity)).1 hN
  let z (j : ℕ) : ℝ := (j : ℝ) * δ
  have hzN : z N = A := by
    dsimp [z, δ]
    field_simp
  have htail : ∀ i : Fin N, ∃ C : ℝ≥0, 0 < C ∧
      coverPowerBound (fun P => μ {x | (C : ℝ≥0∞) * powerScale P (-z (i + 1)) < f P x ^ t})
        (-(d : ℝ) + z (i + 1) + ε / 2) := by
    intro i
    have hzpos : 0 < z (i + 1) := by dsimp [z]; positivity
    have hzle : z (i + 1) ≤ A := by
      rw [← hzN]
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    obtain ⟨r, h, hlevel, hθ, hφ⟩ := criticalMomentLevel hd hν hzpos hzle
    have hz : t * levelExponent d ν r h = z (i + 1) := by
      rw [hθ, mul_comm]
      exact div_mul_cancel₀ _ ht.ne'
    obtain ⟨C, hC, K, hK, hmetric'⟩ := hmetric r h hlevel (ε / 2) (by positivity)
    refine ⟨C ^ t, NNReal.rpow_pos hC, K, hK, ?_⟩
    filter_upwards [hmetric', eventually_ge_atTop (1 : ℝ)] with P hP hPone
    have hP₀ : 0 ≤ P := by linarith
    have hset : {x | (↑(C ^ t) : ℝ≥0∞) * powerScale P (-z (i + 1)) < f P x ^ t} =
        {x | (C : ℝ≥0∞) * powerScale P (-levelExponent d ν r h) < f P x} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      rw [ENNReal.coe_rpow_of_nonneg C ht.le,
        ← show -levelExponent d ν r h * t = -z (i + 1) by rw [neg_mul, mul_comm _ t, hz],
        ← scale_rpow hP₀ ht.le, ← ENNReal.mul_rpow_of_nonneg _ _ ht.le,
        ENNReal.rpow_lt_rpow_iff ht]
    rw [hset]
    exact hP.trans (mul_le_mul_right (scale_mono hPone (by linarith)) _)
  choose C hC K hK htail using htail
  obtain ⟨C₀, hC₀, htriv⟩ := htriv
  let B := C₀ ^ t + ∑ i, C i
  let D := ∑ i, K i
  have hB : 0 < B := add_pos_of_pos_of_nonneg (NNReal.rpow_pos hC₀) (zero_le)
  have hBC (i : Fin N) : C i ≤ B :=
    (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le)
  have hDK (i : Fin N) : K i ≤ D :=
    Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)
  refine ⟨B + (N : ℝ≥0) * (B * D), add_pos_of_pos_of_nonneg hB (zero_le), ?_⟩
  filter_upwards [htriv, Filter.eventually_all.2 htail, eventually_ge_atTop (1 : ℝ)]
    with P hstart hbound hP
  have hPpos : 0 < P := by linarith
  let T (j : ℕ) := (B : ℝ≥0∞) * powerScale P (-z j)
  have hT₀ : ∀ x ∈ (Set.univ : Set Ω), f P x ^ t ≤ T 0 := by
    intro x _
    have h := ENNReal.rpow_le_rpow (hstart x) ht.le
    rw [← ENNReal.coe_rpow_of_nonneg C₀ ht.le] at h
    simpa [T, z, powerScale] using h.trans
      (ENNReal.coe_le_coe.2 (show C₀ ^ t ≤ B from le_self_add))
  have hTN : T N ≤ (B : ℝ≥0∞) * powerScale P (-(d : ℝ) + ε) := by
    dsimp [T]
    rw [hzN]
    exact mul_le_mul_right (scale_mono hP (by dsimp [A]; linarith)) _
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      T j * μ {x | T (j + 1) < f P x ^ t} ≤
        (↑(B * D) : ℝ≥0∞) * powerScale P (-(d : ℝ) + ε) := by
    let i : Fin N := ⟨j, Finset.mem_range.1 hj⟩
    have hsub :
        {x | T (j + 1) < f P x ^ t} ⊆
          {x | (C i : ℝ≥0∞) * powerScale P (-z (i + 1)) < f P x ^ t} := by
      intro x hx
      exact (mul_le_mul_left (ENNReal.coe_le_coe.2 (hBC i)) _).trans_lt hx
    have hm := (measure_mono hsub).trans (hbound i)
    have hzstep : z (j + 1) = z j + δ := by
      simp only [z, Nat.cast_add, Nat.cast_one]
      ring
    calc
      _ ≤ T j * ((K i : ℝ≥0∞) * powerScale P (-(d : ℝ) + z (j + 1) + ε / 2)) :=
        mul_le_mul_right hm _
      _ ≤ T j * ((D : ℝ≥0∞) * powerScale P (-(d : ℝ) + z (j + 1) + ε / 2)) :=
        mul_le_mul_right (mul_le_mul_left (ENNReal.coe_le_coe.2 (hDK i)) _) _
      _ = (↑(B * D) : ℝ≥0∞) *
          powerScale P (-z j + (-(d : ℝ) + z (j + 1) + ε / 2)) := by
        dsimp only [T]
        rw [← scale_mul hPpos (-z j) (-(d : ℝ) + z (j + 1) + ε / 2), ENNReal.coe_mul]
        ac_rfl
      _ ≤ _ := mul_le_mul_right (scale_mono hP (by linarith)) _
  calc
    _ ≤ T N + ∑ j ∈ Finset.range N, T j * μ {x | T (j + 1) < f P x ^ t} := by
      simpa only [Measure.restrict_univ] using
        lintegral_threshold_bound μ MeasurableSet.univ ((hf P).pow_const _) T hT₀ N
    _ ≤ (B : ℝ≥0∞) * powerScale P (-(d : ℝ) + ε) +
          ∑ _j ∈ Finset.range N, (↑(B * D) : ℝ≥0∞) * powerScale P (-(d : ℝ) + ε) :=
      add_le_add hTN (Finset.sum_le_sum hterm)
    _ = _ := by
      simp [Finset.sum_const, nsmul_eq_mul, add_mul, mul_assoc]

/-- A pointwise minor-arc saving promotes the critical moment to a power-saving
minor-arc moment at every larger exponent, as in `eq:minor-moment` of `v2.tex`. -/
theorem minorMoment_of_criticalMoment {d : ℕ} {t s σ : ℝ} (ht : 0 < t) (hs : t < s) (hσ : 0 < σ)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (m : ℝ → Set Ω)
    (f : ℝ → Ω → ℝ≥0∞) (hm : ∀ P, MeasurableSet (m P))
    (hweyl : ∃ C : ℝ≥0, 0 < C ∧
      ∀ᶠ P in atTop, ∀ x ∈ m P, f P x ≤ (C : ℝ≥0∞) * ENNReal.ofReal (P ^ (-σ)))
    (hfull : ∀ ε > 0, coverPowerBound (fun P => ∫⁻ x, f P x ^ t ∂μ) (-(d : ℝ) + ε)) :
    coverPowerBound (fun P => ∫⁻ x in m P, f P x ^ s ∂μ)
      (-(d : ℝ) - σ * (s - t) / 2) := by
  let ε := σ * (s - t) / 2
  have hst : 0 < s - t := sub_pos.2 hs
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨C, hC, hweyl⟩ := hweyl
  obtain ⟨K, hK, hfull⟩ := hfull ε hε
  refine ⟨C ^ (s - t) * K, mul_pos (NNReal.rpow_pos hC) hK, ?_⟩
  filter_upwards [hweyl, hfull, eventually_ge_atTop (1 : ℝ)] with P hP hPfull hPone
  have hPpos : 0 < P := by linarith
  let B := ((C : ℝ≥0∞) * powerScale P (-σ)) ^ (s - t)
  calc
    _ ≤ ∫⁻ x in m P, B * f P x ^ t ∂μ := by
      apply setLIntegral_mono' (hm P)
      intro x hx
      rw [show s = s - t + t by ring, ENNReal.rpow_add_of_nonneg _ _ hst.le ht.le]
      exact mul_le_mul_left (ENNReal.rpow_le_rpow (hP x hx) hst.le) _
    _ ≤ ∫⁻ x, B * f P x ^ t ∂μ :=
      setLIntegral_le_lintegral _ _
    _ ≤ B * ((K : ℝ≥0∞) * powerScale P (-(d : ℝ) + ε)) := by
      exact (le_of_eq (lintegral_const_mul' _ _ (by
        dsimp [B]
        finiteness))).trans (mul_le_mul_right hPfull _)
    _ = _ := by
      change B * _ = (↑(C ^ (s - t) * K) : ℝ≥0∞) * powerScale P (-(d : ℝ) - σ * (s - t) / 2)
      dsimp only [B]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hst.le, ← ENNReal.coe_rpow_of_nonneg C hst.le,
        scale_rpow hPpos.le hst.le, ENNReal.coe_mul]
      rw [← show -σ * (s - t) + (-(d : ℝ) + ε) = -(d : ℝ) - σ * (s - t) / 2 by
        dsimp [ε]; ring]
      rw [← scale_mul hPpos (-σ * (s - t)) (-(d : ℝ) + ε)]
      ac_rfl

private theorem coverPowerBound_of_eventually_le {I J : ℝ → ℝ≥0∞} {a b : ℝ}
    (hIJ : ∀ᶠ P in atTop, I P ≤ J P) (hab : a ≤ b)
    (hJ : coverPowerBound J a) : coverPowerBound I b := by
  obtain ⟨C, hC, hJ⟩ := hJ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hIJ, hJ, eventually_ge_atTop (1 : ℝ)] with P hP hJP hPone
  exact hP.trans (hJP.trans (mul_le_mul_right (scale_mono hPone hab) _))

set_option maxHeartbeats 500000 in
/-- Superlevel estimates for arbitrarily small rescalings of the magnitude
give the same critical-moment exponent. -/
theorem criticalMoment_of_scaledMetric {d ν : ℕ} (hd : 2 ≤ d) (hν : 0 < ν)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ P, Measurable (f P))
    (htriv : ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, f P x ≤ (C : ℝ≥0∞))
    (hmetric : ∀ ζ : ℝ, 0 < ζ → V2MetricDistribution μ d ν
      (fun P x => ENNReal.ofReal (P ^ (-ζ)) * f P x)) :
    ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ x, f P x ^ criticalMomentExponent d ν ∂μ) (-(d : ℝ) + ε) := by
  intro ε hε
  let t := criticalMomentExponent d ν
  have ht : 0 < t := criticalMomentExponent_pos hd hν
  let ζ := (ε/2) / t
  have hζ : 0 < ζ := div_pos (by positivity) ht
  have hζt : ζ * t = ε/2 := div_mul_cancel₀ _ ht.ne'
  let g (P : ℝ) (x : Ω) : ℝ≥0∞ := powerScale P (-ζ) * f P x
  have hg (P : ℝ) : Measurable (g P) := (hf P).const_mul _
  have hgtriv : ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, g P x ≤ (C : ℝ≥0∞) := by
    obtain ⟨C, hC, hb⟩ := htriv
    refine ⟨C, hC, ?_⟩
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with P hP hPone
    intro x
    have hs : powerScale P (-ζ) ≤ 1 := by
      simpa only [powerScale, Real.rpow_zero, ENNReal.ofReal_one] using
        scale_mono hPone (neg_nonpos.mpr hζ.le)
    calc
      g P x ≤ 1 * f P x := mul_le_mul' hs le_rfl
      _ = f P x := one_mul _
      _ ≤ _ := hP x
  have scaled := (criticalMoment_of_metric hd hν μ g hg hgtriv (hmetric ζ hζ)
    (ε/2) (by positivity)).scale (ζ*t)
  refine coverPowerBound_of_eventually_le ?_ (by rw [hζt]; linarith) scaled
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  apply le_of_eq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only [g]
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le, scale_rpow hP₀.le ht.le, ← mul_assoc,
    scale_mul hP₀, show ζ*t + -ζ*t = 0 by ring]
  simp [powerScale, t]

/-- Hölder combines a moment over the arcs with a full-circle moment.
Both exponents are expressed on the scale of the moments, before taking roots. -/
theorem coverProductBound_of_moments {p q a b : ℝ} (hpq : p.HolderConjugate q)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (m : ℝ → Set Ω)
    (f g : ℝ → Ω → ℝ≥0∞)
    (hf : ∀ P, Measurable (f P)) (hg : ∀ P, Measurable (g P))
    (hS : coverPowerBound (fun P => ∫⁻ x in m P, f P x ^ p ∂μ) a)
    (hT : coverPowerBound (fun P => ∫⁻ x, g P x ^ q ∂μ) b) :
    coverPowerBound (fun P => ∫⁻ x in m P, f P x * g P x ∂μ) (a / p + b / q) := by
  obtain ⟨A, hA, hS⟩ := hS
  obtain ⟨B, hB, hT⟩ := hT
  let C := A ^ (1 / p) * B ^ (1 / q)
  have hC : 0 < C := mul_pos (NNReal.rpow_pos hA) (NNReal.rpow_pos hB)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hS, hT, eventually_ge_atTop (1 : ℝ)] with P hSP hTP hP
  have hPpos : 0 < P := by linarith
  have hTP' : (∫⁻ x in m P, g P x ^ q ∂μ) ≤ (B : ℝ≥0∞) * powerScale P b :=
    (setLIntegral_le_lintegral _ _).trans hTP
  calc
    _ ≤ (∫⁻ x in m P, f P x ^ p ∂μ) ^ (1 / p) *
          (∫⁻ x in m P, g P x ^ q ∂μ) ^ (1 / q) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq (hf P).aemeasurable (hg P).aemeasurable
    _ ≤ ((A : ℝ≥0∞) * powerScale P a) ^ (1 / p) * ((B : ℝ≥0∞) * powerScale P b) ^ (1 / q) :=
      mul_le_mul' (ENNReal.rpow_le_rpow hSP hpq.one_div_nonneg)
        (ENNReal.rpow_le_rpow hTP' hpq.symm.one_div_nonneg)
    _ = _ := by
      change _ = (C : ℝ≥0∞) * powerScale P (a / p + b / q)
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.one_div_nonneg,
        ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.one_div_nonneg,
        scale_rpow hPpos.le hpq.one_div_nonneg, scale_rpow hPpos.le hpq.symm.one_div_nonneg,
        ← show a * (1 / p) + b * (1 / q) = a / p + b / q by ring, ← scale_mul hPpos]
      dsimp only [C]
      rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg A hpq.one_div_nonneg,
        ENNReal.coe_rpow_of_nonneg B hpq.symm.one_div_nonneg]
      ac_rfl

/-- The moment exponent in the polynomial-cover asymptotic of `v2.tex`. -/
def coverMomentExponent (e : ℕ) : ℕ := min (2 ^ e) (e * (e + 1))

theorem four_le_coverMomentExponent {e : ℕ} (he : 2 ≤ e) :
    4 ≤ coverMomentExponent e := by
  unfold coverMomentExponent
  apply le_min
  · calc
      4 = (2 : ℕ) ^ 2 := by decide
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) he
  · nlinarith

theorem one_lt_coverMomentExponent {e : ℕ} (he : 2 ≤ e) :
    1 < coverMomentExponent e :=
  lt_of_lt_of_le (by decide) (four_le_coverMomentExponent he)

/-- The cover minor-arc estimate from a cover moment of exponent `q`. The
Weyl saving and full-circle moment are explicit inputs. The resulting saving
is fixed before the probability space and sums are chosen. -/
theorem coverMinorArcBound_of_criticalMoment_atExponent {d e ν : ℕ} {q σ : ℝ}
    (hd : 2 ≤ d) (hq : 1 < q)
    (hν : (1 - 1 / q) * minorDimensionThreshold d < (ν : ℝ))
    (hσ : 0 < σ) :
    ∃ δ > 0, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (m : ℝ → Set Ω) (f g : ℝ → Ω → ℝ≥0∞),
      (∀ P, MeasurableSet (m P)) → (∀ P, Measurable (f P)) → (∀ P, Measurable (g P)) →
      (∀ ε > 0, coverPowerBound
        (fun P => ∫⁻ x, f P x ^ criticalMomentExponent d ν ∂μ) (-(d : ℝ) + ε)) →
      (∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x ∈ m P,
        f P x ≤ (C : ℝ≥0∞) * ENNReal.ofReal (P ^ (-σ))) →
      (∀ ε > 0, coverPowerBound
        (fun P => ∫⁻ x, g P x ^ q ∂μ)
        ((d : ℝ) / e * q - d + ε)) →
      coverPowerBound (fun P => ∫⁻ x in m P, f P x * g P x ∂μ) ((d : ℝ) / e - d - δ) := by
  let s := q.conjExponent
  let t := criticalMomentExponent d ν
  have hsq : s.HolderConjugate q := (Real.HolderConjugate.conjExponent hq).symm
  have hconj : 1 / s + 1 / q = 1 := by simpa using hsq.one_div_add_one_div
  have htpos : 0 < minorDimensionThreshold d := minorDimensionThreshold_pos hd
  have hνpos : (0 : ℝ) < ν := by
    have hr : 0 < 1 - 1 / q := by linarith [hsq.one_div_pos]
    exact (mul_pos hr htpos).trans hν
  have ht : 0 < t := criticalMomentExponent_pos hd (by exact_mod_cast hνpos)
  have hts : t < s := by
    apply (div_lt_iff₀ hνpos).2
    have hr : minorDimensionThreshold d / s < (ν : ℝ) := by
      calc
        _ = (1 - 1 / q) * minorDimensionThreshold d := by
          have h := show 1 / s = 1 - 1 / q by linarith
          rw [show minorDimensionThreshold d / s = (1 / s) * minorDimensionThreshold d by ring, h]
        _ < _ := hν
    simpa [mul_comm] using (div_lt_iff₀ hsq.pos).1 hr
  let η := σ * (s - t) / 2
  let δ := η / (2 * s)
  have hη : 0 < η := by dsimp [η]; exact div_pos (mul_pos hσ (sub_pos.2 hts)) (by norm_num)
  have hδ : 0 < δ := div_pos hη (mul_pos (by norm_num) hsq.pos)
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ μ _ m f g hm hf hg hfull hweyl hmoment
  have hminor := minorMoment_of_criticalMoment ht hts hσ μ m f hm hweyl hfull
  have hT := hmoment (δ * q) (mul_pos hδ hsq.symm.pos)
  have hbound := coverProductBound_of_moments hsq μ m f g hf hg hminor hT
  convert hbound using 1
  change (d : ℝ) / e - d - δ = (-(d : ℝ) - η) / s +
    ((d : ℝ) / e * q - d + δ * q) / q
  have hηs : η / s = 2 * δ := by
    dsimp only [δ]
    ring
  calc
    _ = (d : ℝ) / e - d * (1 / s + 1 / q) - η / s + δ := by rw [hconj, hηs]; ring
    _ = _ := by field_simp [hsq.ne_zero, hsq.symm.ne_zero]; ring

theorem coverMinorArcBound_of_metric_atExponent {d e ν : ℕ} {q σ : ℝ}
    (hd : 2 ≤ d) (hq : 1 < q)
    (hν : (1 - 1 / q) * minorDimensionThreshold d < (ν : ℝ))
    (hσ : 0 < σ) :
    ∃ δ > 0, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (m : ℝ → Set Ω) (f g : ℝ → Ω → ℝ≥0∞),
      (∀ P, MeasurableSet (m P)) → (∀ P, Measurable (f P)) → (∀ P, Measurable (g P)) →
      (∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, f P x ≤ (C : ℝ≥0∞)) →
      V2MetricDistribution μ d ν f →
      (∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x ∈ m P,
        f P x ≤ (C : ℝ≥0∞) * ENNReal.ofReal (P ^ (-σ))) →
      (∀ ε > 0, coverPowerBound
        (fun P => ∫⁻ x, g P x ^ q ∂μ)
        ((d : ℝ) / e * q - d + ε)) →
      coverPowerBound (fun P => ∫⁻ x in m P, f P x * g P x ∂μ) ((d : ℝ) / e - d - δ) := by
  have hfactor : 0 ≤ 1 - 1 / q := by
    exact sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le zero_lt_one hq.le)
  have hνpos : 0 < ν := by
    exact_mod_cast (show (0 : ℝ) < ν from
      (mul_nonneg hfactor (minorDimensionThreshold_pos hd).le).trans_lt hν)
  obtain ⟨δ, hδ, hminor⟩ := coverMinorArcBound_of_criticalMoment_atExponent (e := e) hd hq hν hσ
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ μ _ m f g hm hf hg htriv hmetric hweyl hmoment
  exact hminor μ m f g hm hf hg (criticalMoment_of_metric hd hνpos μ f hf htriv hmetric)
    hweyl hmoment

/-- The minor-arc estimate at the moment exponent selected in `v2.tex`. -/
theorem coverMinorArcBound_of_metric {d e ν : ℕ} {σ : ℝ}
    (hd : 2 ≤ d) (he : 2 ≤ e)
    (hν : (1 - 1 / (coverMomentExponent e : ℝ)) * minorDimensionThreshold d < (ν : ℝ))
    (hσ : 0 < σ) :
    ∃ δ > 0, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (m : ℝ → Set Ω) (f g : ℝ → Ω → ℝ≥0∞),
      (∀ P, MeasurableSet (m P)) → (∀ P, Measurable (f P)) → (∀ P, Measurable (g P)) →
      (∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, f P x ≤ (C : ℝ≥0∞)) →
      V2MetricDistribution μ d ν f →
      (∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x ∈ m P,
        f P x ≤ (C : ℝ≥0∞) * ENNReal.ofReal (P ^ (-σ))) →
      (∀ ε > 0, coverPowerBound
        (fun P => ∫⁻ x, g P x ^ (coverMomentExponent e : ℝ) ∂μ)
        ((d : ℝ) / e * coverMomentExponent e - d + ε)) →
      coverPowerBound (fun P => ∫⁻ x in m P, f P x * g P x ∂μ) ((d : ℝ) / e - d - δ) :=
  coverMinorArcBound_of_metric_atExponent hd (by exact_mod_cast one_lt_coverMomentExponent he) hν hσ


private theorem lintegral_rpow_le_of_le_exponent {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ^ s ∂μ) ≤ (∫⁻ x, f x ^ t ∂μ) ^ (s / t) := by
  rcases hst.eq_or_lt with e | hst
  · subst t
    rw [div_self hs.ne', ENNReal.rpow_one]
  let p := t / s
  have hp : 1 < p := (lt_div_iff₀ hs).2 (by simpa using hst)
  have hpq := Real.HolderConjugate.conjExponent hp
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun x => f x ^ s) (g := fun _ => 1) (hf.aemeasurable.pow_const s) aemeasurable_const
  have hsp : s * p = t := by dsimp [p]; field_simp
  have h1p : 1 / p = s / t := by dsimp [p]; rw [one_div_div]
  simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    measure_univ, ← ENNReal.rpow_mul, hsp, h1p] using h

/-- On a probability space the full moment at exponent `s` follows from the
critical moment at exponent `t` and a uniform bound. The minimum records the
two cases in the proof of Theorem `thm:clean-serre-epsilon` of `v2.tex`. -/
theorem fullMoment_of_criticalMoment {d : ℕ} {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ P, Measurable (f P))
    (htriv : ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, f P x ≤ (C : ℝ≥0∞))
    (hfull : ∀ ε > 0, coverPowerBound (fun P => ∫⁻ x, f P x ^ t ∂μ) (-(d : ℝ) + ε)) :
    ∀ ε > 0, coverPowerBound (fun P => ∫⁻ x, f P x ^ s ∂μ)
      (-(d : ℝ) * min 1 (s / t) + ε) := by
  intro ε hε
  by_cases hst : s ≤ t
  · have hr : 0 < s / t := div_pos hs ht
    rw [min_eq_right ((div_le_iff₀ ht).2 (by simpa using hst))]
    obtain ⟨C, hC, hb⟩ := hfull (ε / (s / t)) (div_pos hε hr)
    refine ⟨C ^ (s / t), NNReal.rpow_pos hC, ?_⟩
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with P hP hPone
    have hP₀ : 0 ≤ P := by linarith
    calc
      _ ≤ (∫⁻ x, f P x ^ t ∂μ) ^ (s / t) :=
        lintegral_rpow_le_of_le_exponent hs hst μ (f P) (hf P)
      _ ≤ ((C : ℝ≥0∞) * powerScale P (-(d : ℝ) + ε / (s / t))) ^ (s / t) :=
        ENNReal.rpow_le_rpow hP hr.le
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le, ← ENNReal.coe_rpow_of_nonneg C hr.le,
          scale_rpow hP₀ hr.le]
        congr 2
        field_simp
  · have hts : 0 < s - t := sub_pos.2 (lt_of_not_ge hst)
    rw [min_eq_left ((le_div_iff₀ ht).2 (by simpa using (lt_of_not_ge hst).le)), mul_one]
    obtain ⟨C, hC, htriv⟩ := htriv
    obtain ⟨K, hK, hb⟩ := hfull ε hε
    refine ⟨C ^ (s - t) * K, mul_pos (NNReal.rpow_pos hC) hK, ?_⟩
    filter_upwards [htriv, hb] with P hCP hKP
    calc
      _ ≤ ∫⁻ x, (C : ℝ≥0∞) ^ (s - t) * f P x ^ t ∂μ := by
        apply lintegral_mono
        intro x
        calc
          f P x ^ s = f P x ^ (s - t) * f P x ^ t := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ hts.le ht.le, sub_add_cancel]
          _ ≤ _ := mul_le_mul_left (ENNReal.rpow_le_rpow (hCP x) hts.le) _
      _ ≤ (C : ℝ≥0∞) ^ (s - t) * ((K : ℝ≥0∞) * powerScale P (-(d : ℝ) + ε)) := by
        rw [lintegral_const_mul _ ((hf P).pow_const t)]
        exact mul_le_mul_right hKP _
      _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg C hts.le, mul_assoc]

/-- Serre's codimension condition includes the endpoint. This is the normalized
Hölder bound in the proof of Theorem `thm:clean-serre-epsilon` of `v2.tex`.
The fourth moment is the input for the polynomial sum. -/
theorem coverSerreIntegralBound_of_criticalMoment {d e ν : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hνpos : 0 < ν)
    (hν : (1 / (d : ℝ) + 1 / (2 * e)) * minorDimensionThreshold d ≤ (ν : ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : ℝ → Ω → ℝ≥0∞) (hf : ∀ P, Measurable (f P)) (hg : ∀ P, Measurable (g P))
    (htriv : ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, f P x ≤ (C : ℝ≥0∞))
    (hfull : ∀ ε > 0, coverPowerBound
      (fun P => ∫⁻ x, f P x ^ criticalMomentExponent d ν ∂μ) (-(d : ℝ) + ε))
    (hfourth : ∀ ε > 0, coverPowerBound (fun P => ∫⁻ x, g P x ^ (4 : ℝ) ∂μ)
      (2 * (d : ℝ) / e + ε)) :
    ∀ ε > 0, coverPowerBound (fun P => ∫⁻ x, f P x * g P x ∂μ) (-1 + ε) := by
  intro ε hε
  let t := criticalMomentExponent d ν
  let s : ℝ := 4 / 3
  have ht : 0 < t := criticalMomentExponent_pos hd hνpos
  have hsq : s.HolderConjugate 4 := by
    constructor <;> norm_num [s]
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have he' : (2 : ℝ) ≤ e := by exact_mod_cast he
  have hdpos : (0 : ℝ) < d := by linarith
  have hepos : (0 : ℝ) < e := by linarith
  have hν' : (0 : ℝ) < ν := by exact_mod_cast hνpos
  have hc := minorDimensionThreshold_pos hd
  let k := 1 + (d : ℝ) / (2 * e)
  have hk₁ : k ≤ (d : ℝ) / s := by
    have hdfrac : (d : ℝ) / (2 * e) ≤ (d : ℝ) / 4 :=
      div_le_div_of_nonneg_left hdpos.le (by norm_num) (by linarith)
    dsimp [k, s]
    linarith
  have hk₂ : k ≤ (d : ℝ) / t := by
    calc
      _ = ((1 / (d : ℝ) + 1 / (2 * e)) * minorDimensionThreshold d) *
          ((d : ℝ) / minorDimensionThreshold d) := by
        dsimp [k]
        field_simp [hdpos.ne', hepos.ne', hc.ne']
      _ ≤ (ν : ℝ) * ((d : ℝ) / minorDimensionThreshold d) :=
        mul_le_mul_of_nonneg_right hν (div_pos hdpos hc).le
      _ = _ := by dsimp [t, criticalMomentExponent]; field_simp [hc.ne', hν'.ne']
  have hk : k ≤ (d : ℝ) * min 1 (s / t) / s := by
    by_cases hs : 1 ≤ s / t
    · simpa [min_eq_left hs] using hk₁
    · rw [min_eq_right (le_of_not_ge hs), show (d : ℝ) * (s / t) / s = d / t by
        field_simp [ht.ne', hsq.ne_zero]]
      exact hk₂
  have hS := fullMoment_of_criticalMoment hsq.pos ht μ f hf htriv hfull ε hε
  have hSuniv : coverPowerBound (fun P => ∫⁻ x in (Set.univ : Set Ω), f P x ^ s ∂μ)
      (-(d : ℝ) * min 1 (s / t) + ε) := by
    simpa only [Measure.restrict_univ] using hS
  have hprod := coverProductBound_of_moments hsq μ (fun _ => Set.univ) f g hf hg
    hSuniv (hfourth ε hε)
  have hexp : (-(d : ℝ) * min 1 (s / t) + ε) / s + (2 * (d : ℝ) / e + ε) / 4
      ≤ -1 + ε := by
    have hconj : 1 / s + 1 / (4 : ℝ) = 1 := by simpa using hsq.one_div_add_one_div
    have hfrac : (2 * (d : ℝ) / e) / 4 = (d : ℝ) / (2 * e) := by
      field_simp
      norm_num
    rw [add_div, add_div, hfrac, neg_mul, neg_div]
    have heps : ε / s + ε / 4 = ε := by
      calc
        _ = ε * (1 / s + 1 / 4) := by ring
        _ = _ := by rw [hconj, mul_one]
    dsimp only [k] at hk
    linarith
  exact coverPowerBound_of_eventually_le (Eventually.of_forall fun _ => le_rfl) hexp
    (by simpa only [Measure.restrict_univ] using hprod)


end

end Birch
