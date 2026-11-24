import Birch.Estimates
import Birch.Geometry
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Real oscillatory decay for transverse weights

Directional integration by parts moves each derivative from the oscillation to
the weight divided by the corresponding nonzero partial derivative. Each new
weight retains the original support, so it can be used in the next integration
by parts.
-/

open MeasureTheory Set Filter MvPolynomial
open scoped ContDiff Topology

namespace Birch

noncomputable section

/-- Evaluating an integer form gives a smooth real function. -/
theorem contDiff_evalForm {n : ℕ} (F : IntForm n) :
    ContDiff ℝ ∞ (evalForm F : (Fin n → ℝ) → ℝ) := by
  unfold evalForm
  simp only [MvPolynomial.eval₂_eq']
  fun_prop

/-- A coordinate line derivative evaluates the corresponding formal partial derivative. -/
theorem hasLineDerivAt_evalForm {n : ℕ} (F : IntForm n) (i : Fin n)
    (x : Fin n → ℝ) :
    HasLineDerivAt ℝ (evalForm F) (evalForm (pderiv i F) x) x (Pi.single i 1) := by
  classical
  let v : Fin n → ℝ := Pi.single i 1
  have hx (j : Fin n) : HasDerivAt (fun t : ℝ => (x + t • v) j) (v j) 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (v j)).const_add (x j))
  change HasDerivAt (fun t : ℝ => evalForm F (x + t • v)) (evalForm (pderiv i F) x) 0
  induction F using MvPolynomial.induction_on with
  | C a =>
    simpa only [evalForm, pderiv_C, eval₂_zero, eval₂_C] using
      (hasDerivAt_const (0 : ℝ) ((Int.castRingHom ℝ) a))
  | add p q hp hq =>
    simpa only [evalForm, map_add, eval₂_add] using hp.fun_add hq
  | mul_X p j hp =>
    have hX : evalForm (pderiv i (X j : IntForm n)) x = v j := by
      by_cases h : j = i
      · subst j
        simp [v, evalForm]
      · simp [v, pderiv_X_of_ne h, h, evalForm]
    have H := hp.mul (hx j)
    simp only [zero_smul, add_zero] at H
    rw [MvPolynomial.pderiv_mul]
    simp only [evalForm, eval₂_mul, eval₂_X, eval₂_add]
    unfold evalForm at hX H
    rw [hX]
    exact H

/-- Varying only one coordinate differentiates the evaluated form by its formal partial. -/
theorem hasDerivAt_evalForm_update {n : ℕ} (F : IntForm n) (i : Fin n)
    (x : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => evalForm F (Function.update x i s))
      (evalForm (pderiv i F) (Function.update x i t)) t := by
  let y := Function.update x i t
  let v : Fin n → ℝ := Pi.single i 1
  have h := hasLineDerivAt_evalForm F i y
  change HasDerivAt (fun s : ℝ => evalForm F (y + s • v)) (evalForm (pderiv i F) y) 0 at h
  have hs := (hasDerivAt_id t).sub_const t
  simp only [id_eq] at hs
  have hcomp := h.comp_of_eq t (h := fun s : ℝ => s - t) hs (by simp)
  rw [mul_one] at hcomp
  have hline (s : ℝ) : y + (s - t) • v = Function.update x i s := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [y, v, Pi.add_apply, Pi.smul_apply]
    · simp [y, v, Pi.add_apply, Pi.smul_apply, hj]
  change HasDerivAt (fun s : ℝ => evalForm F (y + (s - t) • v))
    (evalForm (pderiv i F) y) t at hcomp
  simpa only [hline] using hcomp

/-- The real phase has complex norm one. -/
theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- The coefficient obtained by differentiating the phase at a scaled frequency. -/
def phaseCoefficient (t : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)

/-- The phase coefficient has norm proportional to the absolute frequency. -/
theorem norm_phaseCoefficient (t : ℝ) :
    ‖phaseCoefficient t‖ = 2 * Real.pi * |t| := by
  unfold phaseCoefficient
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]

section Amplitudes

variable {n : ℕ}

local notation "V" => (Fin n → ℝ)

private def differentiateAmplitude (v : V) (ρ w : V → ℝ) : V → ℝ :=
  fun x => fderiv ℝ (fun y => w y / ρ y) x v

private theorem quotient_tsupport_subset (w ρ : V → ℝ) :
    tsupport (fun x => w x / ρ x) ⊆ tsupport w := by
  change closure _ ⊆ closure _
  apply closure_mono
  intro x hx
  apply Function.mem_support.mpr
  intro hz
  exact (Function.mem_support.mp hx) (by simp [hz])

private theorem quotient_contDiff {w ρ : V → ℝ} (hw : ContDiff ℝ ∞ w) (hρ : ContDiff ℝ ∞ ρ)
    (hρz : ∀ x ∈ tsupport w, ρ x ≠ 0) : ContDiff ℝ ∞ fun x => w x / ρ x := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport w
  · exact hw.contDiffAt.div hρ.contDiffAt (hρz x hx)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [hy]

private theorem differentiateAmplitude_tsupport (v : V) (w ρ : V → ℝ) :
    tsupport (differentiateAmplitude v ρ w) ⊆ tsupport w :=
  (tsupport_fderiv_apply_subset ℝ v).trans (quotient_tsupport_subset w ρ)

private theorem differentiateAmplitude_contDiff (v : V) {w ρ : V → ℝ}
    (hw : ContDiff ℝ ∞ w) (hρ : ContDiff ℝ ∞ ρ) (hρz : ∀ x ∈ tsupport w, ρ x ≠ 0) :
    ContDiff ℝ ∞ (differentiateAmplitude v ρ w) :=
  ((quotient_contDiff hw hρ hρz).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private def oscillation (w φ : V → ℝ) (γ : ℝ) : ℂ :=
  ∫ x, (w x : ℂ) * phase (γ * φ x)

/-- The directional derivative of a real phase evaluated in the complex character. -/
theorem phase_lineDeriv {v x : V} {φ : V → ℝ} {ρ : ℝ}
    (hφ' : HasLineDerivAt ℝ φ ρ x v) (γ : ℝ) :
    HasLineDerivAt ℝ (fun y => phase (γ * φ y))
      (phaseCoefficient γ * (ρ : ℂ) * phase (γ * φ x)) x v := by
  change HasDerivAt (fun t : ℝ => φ (x + t • v)) ρ 0 at hφ'
  have h := (((hφ'.const_mul γ).ofReal_comp.const_mul
    (2 * (Real.pi : ℂ) * Complex.I)).cexp)
  change HasDerivAt (fun t : ℝ => phase (γ * φ (x + t • v))) _ 0
  simp only [zero_smul, add_zero, Complex.ofReal_mul] at h
  unfold phase phaseCoefficient
  push_cast
  convert h using 1
  ring

private theorem oscillation_ibp {v : V} {w ρ φ : V → ℝ}
    (hw : ContDiff ℝ ∞ w) (hcw : HasCompactSupport w)
    (hρ : ContDiff ℝ ∞ ρ) (hρz : ∀ x ∈ tsupport w, ρ x ≠ 0)
    (hφ : Continuous φ) (hderiv : ∀ x, HasLineDerivAt ℝ φ (ρ x) x v)
    (γ : ℝ) :
    phaseCoefficient γ * oscillation w φ γ =
      -oscillation (differentiateAmplitude v ρ w) φ γ := by
  let A : V → ℝ := fun x => w x / ρ x
  let A' := differentiateAmplitude v ρ w
  let g : V → ℂ := fun x => phase (γ * φ x)
  let g' : V → ℂ := fun x => phaseCoefficient γ * (ρ x : ℂ) * g x
  have hA : ContDiff ℝ ∞ A := quotient_contDiff hw hρ hρz
  have hA' : ContDiff ℝ ∞ A' := differentiateAmplitude_contDiff v hw hρ hρz
  have hcA : HasCompactSupport A :=
    hcw.of_isClosed_subset (isClosed_tsupport _) (quotient_tsupport_subset w ρ)
  have hcA' : HasCompactSupport A' :=
    hcw.of_isClosed_subset (isClosed_tsupport _) (differentiateAmplitude_tsupport v w ρ)
  have hg : Continuous g := by dsimp [g, phase]; fun_prop
  have hg' : Continuous g' := by dsimp [g']; fun_prop
  have hbA (x : V) : HasLineDerivAt ℝ A (A' x) x v :=
    ((hA.differentiable (by simp)).differentiableAt.hasFDerivAt).hasLineDerivAt v
  have hbg (x : V) : HasLineDerivAt ℝ g (g' x) x v := phase_lineDeriv (hderiv x) γ
  have h :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (μ := (volume : Measure V)) (B := ContinuousLinearMap.lsmul ℝ ℝ)
      (f := A) (f' := A') (g := g) (g' := g')
      ((hA'.continuous.smul hg).integrable_of_hasCompactSupport hcA'.smul_right)
      ((hA.continuous.smul hg').integrable_of_hasCompactSupport hcA.smul_right)
      ((hA.continuous.smul hg).integrable_of_hasCompactSupport hcA.smul_right)
      (fun x _ => hbA x) (fun x _ => hbg x)
  have hpoint (x : V) : A x • g' x = phaseCoefficient γ * ((w x : ℂ) * g x) := by
    dsimp [A, g']
    rw [Complex.ofReal_div]
    by_cases hx : x ∈ tsupport w
    · have hz : (ρ x : ℂ) ≠ 0 := mod_cast hρz x hx
      field_simp
    · rw [image_eq_zero_of_notMem_tsupport hx]
      push_cast
      simp
  change (∫ x, A x • g' x) = -(∫ x, A' x • g x) at h
  simp_rw [hpoint, Complex.real_smul] at h
  rw [integral_const_mul] at h
  exact h

private def amplitudeStage (v : V) (ρ w : V → ℝ) : ℕ → V → ℝ
  | 0 => w
  | k + 1 => differentiateAmplitude v ρ (amplitudeStage v ρ w k)

private theorem amplitudeStage_properties {v : V} {ρ w : V → ℝ}
    (hw : ContDiff ℝ ∞ w) (hρ : ContDiff ℝ ∞ ρ)
    (hρz : ∀ x ∈ tsupport w, ρ x ≠ 0) (k : ℕ) :
    ContDiff ℝ ∞ (amplitudeStage v ρ w k) ∧ tsupport (amplitudeStage v ρ w k) ⊆ tsupport w := by
  induction k with
  | zero => exact ⟨hw, Subset.rfl⟩
  | succ k ih =>
    exact ⟨differentiateAmplitude_contDiff v ih.1 hρ (fun x hx => hρz x (ih.2 hx)),
      (differentiateAmplitude_tsupport _ _ _).trans ih.2⟩

private theorem norm_oscillation_le_amplitude {w φ : V → ℝ} (γ : ℝ) :
    ‖oscillation w φ γ‖ ≤ ∫ x, |w x| := by
  unfold oscillation
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp_rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_oscillation_iterate {v : V} {w ρ φ : V → ℝ}
    (hw : ContDiff ℝ ∞ w) (hcw : HasCompactSupport w) (hρ : ContDiff ℝ ∞ ρ)
    (hρz : ∀ x ∈ tsupport w, ρ x ≠ 0) (hφ : Continuous φ)
    (hderiv : ∀ x, HasLineDerivAt ℝ φ (ρ x) x v) (γ : ℝ) (k : ℕ) :
    ‖phaseCoefficient γ‖ ^ k * ‖oscillation w φ γ‖ =
      ‖oscillation (amplitudeStage v ρ w k) φ γ‖ := by
  induction k with
  | zero => simp [amplitudeStage]
  | succ k ih =>
    let a := amplitudeStage v ρ w k
    have ha := amplitudeStage_properties (v := v) hw hρ hρz k
    have hca : HasCompactSupport a := hcw.of_isClosed_subset (isClosed_tsupport _) ha.2
    have h := congrArg norm (oscillation_ibp ha.1 hca hρ
      (fun x hx => hρz x (ha.2 hx)) hφ hderiv γ)
    rw [norm_mul, norm_neg] at h
    calc
      _ = ‖phaseCoefficient γ‖ * (‖phaseCoefficient γ‖^k * ‖oscillation w φ γ‖) := by
        rw [pow_succ', mul_assoc]
      _ = _ := by rw [ih]; exact h

private theorem continuous_oscillation {w φ : V → ℝ} (hw : Continuous w) (hc : HasCompactSupport w)
    (hφ : Continuous φ) : Continuous (oscillation w φ) := by
  unfold oscillation
  refine continuous_of_dominated (bound := fun x => |w x|) (fun t => ?_)
    (fun t => ae_of_all _ fun x => ?_) (hw.integrable_of_hasCompactSupport hc).abs
    (ae_of_all _ fun x => ?_)
  · apply Continuous.aestronglyMeasurable
    unfold phase
    fun_prop
  · simp [norm_phase, Complex.norm_real, Real.norm_eq_abs]
  · unfold phase
    fun_prop

end Amplitudes

/-- Smooth compact weights supported where one partial derivative is nonzero
give rapid decay of the real oscillatory integral. -/
theorem realOscillation_rapidDecay_of_compact_transverse {n : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (htrans : ∃ i : Fin n, ∀ x ∈ tsupport w, evalForm (pderiv i F) x ≠ 0) (N : ℕ) :
    ∃ D > 0, ∀ γ, ‖realOscillation F w γ‖ ≤ D * (1 + |γ|) ^ (-(N : ℝ)) := by
  obtain ⟨i, hi⟩ := htrans
  let φ : (Fin n → ℝ) → ℝ := evalForm F
  let ρ : (Fin n → ℝ) → ℝ := evalForm (pderiv i F)
  let v : Fin n → ℝ := Pi.single i 1
  have hφ : Continuous φ := (contDiff_evalForm F).continuous
  have hρ : ContDiff ℝ ∞ ρ := contDiff_evalForm _
  have hρz (x : Fin n → ℝ) (hx : x ∈ tsupport w) : ρ x ≠ 0 := hi x hx
  have hderiv (x : Fin n → ℝ) : HasLineDerivAt ℝ φ (ρ x) x v := hasLineDerivAt_evalForm F i x
  let A0 : ℝ := ∫ x, |w x|
  let AN : ℝ := ∫ x, |amplitudeStage v ρ w N x|
  let D : ℝ := (2 : ℝ) ^ N * (A0 + AN + 1)
  have hA0 : 0 ≤ A0 := integral_nonneg fun _ => abs_nonneg _
  have hAN : 0 ≤ AN := integral_nonneg fun _ => abs_nonneg _
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro γ
  change ‖oscillation w φ γ‖ ≤ D * (1 + |γ|) ^ (-(N : ℝ))
  have hpos : 0 < 1 + |γ| := by positivity
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + |γ|) ^ N)).mpr
  have hpow₂ : 0 ≤ (2 : ℝ) ^ N := by positivity
  by_cases hγ : |γ| ≤ 1
  · have hA := norm_oscillation_le_amplitude (w := w) (φ := φ) γ
    calc
      _ ≤ A0 * (2 : ℝ) ^ N := mul_le_mul hA
        (pow_le_pow_left₀ hpos.le (by linarith) _) (by positivity) hA0
      _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith) hpow₂
  · have hγ' : 1 < |γ| := lt_of_not_ge hγ
    have hcoeff : |γ| ≤ ‖phaseCoefficient γ‖ := by
      rw [norm_phaseCoefficient]
      simpa using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * Real.pi by
        linarith [Real.pi_gt_three]) (abs_nonneg γ)
    have hdec := norm_oscillation_iterate hw hcompact hρ hρz hφ hderiv γ N
    calc
      _ ≤ ‖oscillation w φ γ‖ * (2 * |γ|) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le (by linarith) _) (norm_nonneg _)
      _ = (2 : ℝ)^N * (|γ|^N * ‖oscillation w φ γ‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ)^N * (‖phaseCoefficient γ‖ ^ N * ‖oscillation w φ γ‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg γ) hcoeff _) (norm_nonneg _)) hpow₂
      _ ≤ (2 : ℝ)^N * AN := by
        rw [hdec]
        exact mul_le_mul_of_nonneg_left (norm_oscillation_le_amplitude γ) hpow₂
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hpow₂

/-- The original transverse weight interface gives the same decay at every order. -/
theorem realOscillation_rapidDecay {n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hw : TransverseWeight F w) (N : ℕ) :
    ∃ D > 0, ∀ γ, ‖realOscillation F w γ‖ ≤ D * (1 + |γ|) ^ (-(N : ℝ)) := by
  obtain ⟨i,b,hb,hi⟩ := hw.transverse
  exact realOscillation_rapidDecay_of_compact_transverse hw.smooth hw.compact
    ⟨i, fun x hx => abs_pos.mp (hb.trans_le (hi x hx))⟩ N

/-- In particular the fourth-order decay bound used in the major arcs holds. -/
theorem realOscillation_decay {n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hw : TransverseWeight F w) :
    ∃ D > 0, ∀ γ, ‖realOscillation F w γ‖ ≤ D * (1 + |γ|) ^ (-4 : ℝ) := by
  simpa using realOscillation_rapidDecay hw 4

/-- A smooth compactly supported transverse weight has an absolutely integrable
real oscillation as a function of frequency. -/
theorem integrable_realOscillation_of_compact_transverse {n : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (htrans : ∃ i : Fin n, ∀ x ∈ tsupport w, evalForm (pderiv i F) x ≠ 0) :
    Integrable (realOscillation F w) := by
  obtain ⟨D, hD, hdec⟩ := realOscillation_rapidDecay_of_compact_transverse hw hcompact htrans 4
  have hcont : Continuous (realOscillation F w) :=
    continuous_oscillation hw.continuous hcompact (contDiff_evalForm F).continuous
  refine (integrable_inv_one_add_sq.const_mul D).mono' hcont.aestronglyMeasurable (ae_of_all _ fun γ => ?_)
  refine (hdec γ).trans (mul_le_mul_of_nonneg_left ?_ hD.le)
  have hpos : 0 < 1 + |γ| := by positivity
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  apply inv_anti₀ (by positivity)
  have hsq : 1 + γ ^ (2 : ℕ) ≤ (1 + |γ|) ^ (2 : ℕ) := by
    nlinarith [sq_abs γ, abs_nonneg γ]
  refine hsq.trans ?_
  exact pow_le_pow_right₀ (by linarith [abs_nonneg γ]) (by omega)

/-- The real oscillation is integrable for the original transverse weights. -/
theorem integrable_realOscillation {n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hw : TransverseWeight F w) : Integrable (realOscillation F w) := by
  obtain ⟨i,b,hb,hi⟩ := hw.transverse
  exact integrable_realOscillation_of_compact_transverse hw.smooth hw.compact
    ⟨i, fun x hx => abs_pos.mp (hb.trans_le (hi x hx))⟩

end
end Birch
