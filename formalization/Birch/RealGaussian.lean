import Birch.Estimates
import Birch.RealSublevel
import Birch.Geometry
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Gaussian regularization of the singular integral

A weighted lower bound for sublevel sets gives a positive singular integral
without requiring a smooth pushforward density.
-/

namespace Birch

noncomputable section

open MeasureTheory Filter Set Complex
open scoped ContDiff Topology

variable {n : ℕ}

/-- The weighted measure of the symmetric sublevel set is bounded below
by a positive constant times its radius near zero. -/
def WeightedSublevelLowerBound (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (c : ℝ), 0 < c ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
    c*r ≤ ∫ x in {x : Fin n → ℝ | |evalForm F x| ≤ r}, w x

private def gaussianScale (T γ : ℝ) : ℂ :=
  Complex.exp (-(((T^2 : ℝ)⁻¹ : ℝ) : ℂ) * (γ : ℂ)^2)

private def gaussianProfile (T u : ℝ) : ℝ :=
  Real.sqrt Real.pi * T * Real.exp (-Real.pi^2 * T^2 * u^2)

private theorem gaussianScale_norm (T γ : ℝ) :
    ‖gaussianScale T γ‖ = Real.exp (-(T^2 : ℝ)⁻¹ * γ^2) := by
  unfold gaussianScale
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.norm_exp_ofReal]

private theorem integral_gaussianScale_mul_phase {T : ℝ} (hT : 0 < T) (u : ℝ) :
    (∫ γ : ℝ, gaussianScale T γ * phase (γ*u)) = (gaussianProfile T u : ℂ) := by
  let b : ℂ := ((T^2 : ℝ)⁻¹ : ℝ)
  let t : ℂ := 2 * (Real.pi : ℂ) * (u : ℂ)
  have hb : 0 < b.re := by
    change 0 < (T^2)⁻¹
    positivity
  have hphase (γ : ℝ) : phase (γ*u) = Complex.exp (Complex.I * t * (γ : ℂ)) := by
    unfold phase t
    push_cast
    congr 1
    ring
  simp_rw [hphase, mul_comm (gaussianScale T _)]
  change (∫ γ : ℝ, Complex.exp (Complex.I * t * (γ : ℂ)) *
      Complex.exp (-b * (γ : ℂ)^2)) = _
  rw [fourierIntegral_gaussian hb]
  have hbase : (Real.pi : ℂ) / b = ((Real.pi*T^2 : ℝ) : ℂ) := by
    simp [b, div_inv_eq_mul]
  have hexp : -(t^2)/(4*b) = ((-Real.pi^2 * T^2 * u^2 : ℝ) : ℂ) := by
    unfold t b
    push_cast
    have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
    field_simp
    ring
  rw [hbase, hexp, ← Complex.ofReal_exp,
    show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul]
  congr 1
  unfold gaussianProfile
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (Real.pi_pos.le), Real.sqrt_sq hT.le]

private def gaussianRegularization (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (T : ℝ) : ℂ :=
  ∫ γ : ℝ, gaussianScale T γ * realOscillation F w γ

private theorem gaussianRegularization_eq_integral (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : Continuous w) (hcompact : HasCompactSupport w) {T : ℝ} (hT : 0 < T) :
    gaussianRegularization F w T =
      ↑(∫ x : Fin n → ℝ, w x * gaussianProfile T (evalForm F x)) := by
  let H (γ : ℝ) (x : Fin n → ℝ) :=
    gaussianScale T γ * ((w x : ℂ) * phase (γ * evalForm F x))
  have hGauss : Integrable (fun γ : ℝ => Real.exp (-(T^2 : ℝ)⁻¹ * γ^2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hwI : Integrable w := hw.integrable_of_hasCompactSupport hcompact
  have hMeas : AEStronglyMeasurable (Function.uncurry H)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    apply Continuous.aestronglyMeasurable
    have hf := (continuous_evalForm F).comp (continuous_snd : Continuous (Prod.snd : ℝ × (Fin n → ℝ) → _))
    have hG : Continuous (gaussianScale T) := by unfold gaussianScale; fun_prop
    have hP : Continuous phase := by unfold phase; fun_prop
    exact (hG.comp continuous_fst).mul
      ((Complex.continuous_ofReal.comp (hw.comp continuous_snd)).mul
        (hP.comp (continuous_fst.mul hf)))
  have hH : Integrable (Function.uncurry H)
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    apply (hGauss.mul_prod hwI.norm).mono' hMeas
    exact Eventually.of_forall fun z => by simp [Function.uncurry, H, gaussianScale_norm, norm_phase]
  unfold gaussianRegularization realOscillation
  simp_rw [← integral_const_mul]
  change (∫ γ, ∫ x, H γ x) = _
  rw [integral_integral_swap hH, ← integral_complex_ofReal]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  have hpoint (γ : ℝ) : H γ x =
      (w x : ℂ) * (gaussianScale T γ * phase (γ * evalForm F x)) := by unfold H; ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_gaussianScale_mul_phase hT, Complex.ofReal_mul]

private theorem gaussianRegularization_tendsto (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hI : Integrable (realOscillation F w)) :
    Tendsto (gaussianRegularization F w) atTop (𝓝 (singularIntegral F w)) := by
  have ht : Tendsto (fun T : ℝ => T^2) atTop atTop := tendsto_pow_atTop (by decide)
  have hi := (Real.tendsto_integral_cexp_sq_smul hI).comp ht
  convert hi using 1
  · funext T
    unfold gaussianRegularization gaussianScale
    simp only [Function.comp_apply, smul_eq_mul, Real.norm_eq_abs]
    apply integral_congr_ae
    exact Eventually.of_forall fun γ => by simp only [← Complex.ofReal_pow, sq_abs]
  · rfl

/-- The absolutely convergent singular integral of a continuous compact real weight is real. -/
theorem singularIntegral_im_eq_zero_of_compact (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : Continuous w) (hcompact : HasCompactSupport w) (hI : Integrable (realOscillation F w)) :
    (singularIntegral F w).im = 0 := by
  have ht := Complex.continuous_im.continuousAt.tendsto.comp (gaussianRegularization_tendsto F w hI)
  change Tendsto (fun T => (gaussianRegularization F w T).im) atTop (𝓝 (singularIntegral F w).im) at ht
  have he : (fun T => (gaussianRegularization F w T).im) =ᶠ[atTop] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [gaussianRegularization_eq_integral F w hw hcompact hT, Complex.ofReal_im]
  exact tendsto_nhds_unique (ht.congr' he) tendsto_const_nhds

/-- The original transverse weight gives a real-valued singular integral. -/
theorem singularIntegral_im_eq_zero (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : TransverseWeight F w) (hI : Integrable (realOscillation F w)) :
    (singularIntegral F w).im = 0 :=
  singularIntegral_im_eq_zero_of_compact F w hw.smooth.continuous hw.compact hI

private theorem gaussianProfile_lower {T u : ℝ} (hT : 0 < T) (hu : |u| ≤ T⁻¹) :
    (Real.sqrt Real.pi * Real.exp (-Real.pi^2))*T ≤ gaussianProfile T u := by
  have huSq : u^2 ≤ (T^2)⁻¹ := by
    have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
    simpa only [sq_abs, inv_pow] using h
  have huMul : T^2 * u^2 ≤ 1 := by
    calc
      _ ≤ T^2 * (T^2)⁻¹ := mul_le_mul_of_nonneg_left huSq (by positivity)
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hT.ne')
  have hExp : Real.exp (-Real.pi^2) ≤ Real.exp (-Real.pi^2*T^2*u^2) := by
    apply Real.exp_le_exp.mpr
    rw [mul_assoc]
    simpa using mul_le_mul_of_nonpos_left huMul (neg_nonpos.mpr (sq_nonneg Real.pi))
  unfold gaussianProfile
  nlinarith [mul_le_mul_of_nonneg_left hExp (show 0 ≤ Real.sqrt Real.pi * T by positivity)]

/-- Gaussian regularization transfers a positive weighted sublevel bound
to strict positivity of the singular integral. -/
theorem singularIntegral_pos_of_weightedSublevel_of_compact (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : Continuous w) (hcompact : HasCompactSupport w) (hnneg : ∀ x, 0 ≤ w x)
    (hI : Integrable (realOscillation F w))
    (hsub : WeightedSublevelLowerBound F w) :
    0 < (singularIntegral F w).re := by
  obtain ⟨c, hc, r₀, hr₀, hsub⟩ := hsub
  let K := Real.sqrt Real.pi * Real.exp (-Real.pi^2)
  have hK : 0 < K := by unfold K; positivity
  have ht := Complex.continuous_re.continuousAt.tendsto.comp (gaussianRegularization_tendsto F w hI)
  change Tendsto (fun T => (gaussianRegularization F w T).re) atTop (𝓝 (singularIntegral F w).re) at ht
  have hlower : ∀ᶠ T : ℝ in atTop, K*c ≤ (gaussianRegularization F w T).re := by
    have hr₀' : ∀ᶠ T : ℝ in atTop, T⁻¹ < r₀ :=
      (tendsto_order.mp tendsto_inv_atTop_zero).2 r₀ hr₀
    filter_upwards [eventually_gt_atTop (0 : ℝ), hr₀'] with T hT hrT
    let U := {x : Fin n → ℝ | |evalForm F x| ≤ T⁻¹}
    let J (x : Fin n → ℝ) := w x * gaussianProfile T (evalForm F x)
    have hU : MeasurableSet U := (isClosed_le (continuous_evalForm F).abs continuous_const).measurableSet
    have hJnn (x : Fin n → ℝ) : 0 ≤ J x := by
      have := hnneg x
      unfold J gaussianProfile
      positivity
    have hJI : Integrable J := by
      have hW : Integrable w := hw.integrable_of_hasCompactSupport hcompact
      have hG : Continuous (gaussianProfile T) := by unfold gaussianProfile; fun_prop
      have hJc : Continuous J := hw.mul (hG.comp (continuous_evalForm F))
      apply (hW.const_mul (Real.sqrt Real.pi*T)).mono' hJc.aestronglyMeasurable
      exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (hJnn x)]
        unfold J gaussianProfile
        have hg : Real.exp (-Real.pi^2*T^2*(evalForm F x)^2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _))
            (sq_nonneg _))
        nlinarith [mul_le_mul_of_nonneg_left hg
          (show 0 ≤ w x * (Real.sqrt Real.pi*T) by positivity [hnneg x])]
    have hW : Integrable w := hw.integrable_of_hasCompactSupport hcompact
    have hL : ∀ x ∈ U, (K*T)*w x ≤ J x := by
      intro x hx
      have he := mul_le_mul_of_nonneg_left (gaussianProfile_lower hT hx) (hnneg x)
      simpa only [K, J, mul_comm (w x)] using he
    have hA := setIntegral_mono_on (hW.const_mul (K*T)).integrableOn hJI.integrableOn hU hL
    rw [integral_const_mul] at hA
    have hB := mul_le_mul_of_nonneg_left (hsub T⁻¹ (inv_pos.mpr hT) hrT.le)
      (mul_nonneg hK.le hT.le)
    have hC : K*c = (K*T) * (c*T⁻¹) := by field_simp
    rw [gaussianRegularization_eq_integral F w hw hcompact hT, Complex.ofReal_re, hC]
    exact hB.trans (hA.trans (setIntegral_le_integral hJI (Eventually.of_forall hJnn)))
  exact (mul_pos hK hc).trans_le (ge_of_tendsto ht hlower)

/-- The original transverse weight gives positivity from a weighted sublevel bound. -/
theorem singularIntegral_pos_of_weightedSublevel (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : TransverseWeight F w) (hI : Integrable (realOscillation F w))
    (hsub : WeightedSublevelLowerBound F w) : 0 < (singularIntegral F w).re :=
  singularIntegral_pos_of_weightedSublevel_of_compact F w hw.smooth.continuous hw.compact
    hw.nonnegative hI hsub

/-- The singular integral is positive if a compact transverse weight is
positive at a real zero. -/
theorem singularIntegral_pos_of_compact_transverse {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (hnneg : ∀ x, 0 ≤ w x)
    (htrans : ∃ i : Fin n, ∀ x ∈ tsupport w, evalForm (MvPolynomial.pderiv i F) x ≠ 0)
    (hpos : ∃ x, evalForm F x = 0 ∧ 0 < w x) : 0 < (singularIntegral F w).re := by
  obtain ⟨x,hx,hwx⟩ := hpos
  obtain ⟨i,hi⟩ := htrans
  apply singularIntegral_pos_of_weightedSublevel_of_compact F w hw.continuous hcompact hnneg
    (integrable_realOscillation_of_compact_transverse hw hcompact ⟨i,hi⟩)
  exact realSublevelLowerBound_of_nonsingularZero hw.continuous hcompact hnneg hx hwx
    (hi x (subset_tsupport _ hwx.ne'))

/-- The singular integral of the transverse weight is strictly positive. -/
theorem singularIntegral_pos_of_transverseWeight {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : TransverseWeight F w) :
    0 < (singularIntegral F w).re :=
  singularIntegral_pos_of_weightedSublevel F w hw (integrable_realOscillation hw)
    (realSublevelLowerBound hw)


end

end Birch
