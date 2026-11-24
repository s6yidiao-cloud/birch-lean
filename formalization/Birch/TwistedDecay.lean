import Birch.RealOscillationDecay

/-!
# Decay of Fourier modes of the weighted real oscillation

The amplitude can include the real phase \(e(\gamma F(x))\). Each integration by
parts then introduces at most one additional power of \(1+|\gamma|\).
-/

open MeasureTheory Set MvPolynomial
open scoped BigOperators ContDiff Topology

namespace Birch

noncomputable section

/-- The real oscillatory integral with a linear Fourier twist. -/
def twistedRealOscillation {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (γ : ℝ) (ν : Fin n → ℝ) : ℂ :=
  ∫ x, (w x : ℂ) * phase (γ * evalForm F x - ∑ i, ν i * x i)

section Twisted

variable {n : ℕ}

local notation "V" => (Fin n → ℝ)

private def linearPhase (ν x : V) : ℝ := -∑ i, ν i * x i

private def twistedIntegral (F : IntForm n) (a : V → ℂ) (γ : ℝ) (ν : V) : ℂ :=
  ∫ x, a x * phase (γ * evalForm F x) * phase (linearPhase ν x)

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  push_cast
  rw [mul_add, Complex.exp_add]

private theorem twistedRealOscillation_eq_twistedIntegral (F : IntForm n) (w : V → ℝ)
    (γ : ℝ) (ν : V) :
    twistedRealOscillation F w γ ν = twistedIntegral F (fun x => (w x : ℂ)) γ ν := by
  unfold twistedRealOscillation twistedIntegral linearPhase
  simp_rw [sub_eq_add_neg, phase_add, mul_assoc]

private def coordinateDerivative (i : Fin n) (a : V → ℂ) : V → ℂ :=
  fun x => fderiv ℝ a x (Pi.single i 1)

private theorem coordinateDerivative_contDiff (i : Fin n) {a : V → ℂ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (coordinateDerivative i a) :=
  (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem coordinateDerivative_hasCompactSupport (i : Fin n) {a : V → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (coordinateDerivative i a) :=
  ha.fderiv_apply ℝ (Pi.single i 1)

private theorem linearPhase_hasLineDerivAt (ν x : V) (i : Fin n) :
    HasLineDerivAt ℝ (linearPhase ν) (-ν i) x (Pi.single i 1) := by
  let v : V := Pi.single i 1
  have hline (t : ℝ) : linearPhase ν (x + t • v) = linearPhase ν x + t * (-ν i) := by
    unfold linearPhase
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    have hsum : (∑ j, ν j * (t * v j)) = ν i * t := by
      rw [Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [v, hj]
      · simp
    rw [hsum]
    ring
  change HasDerivAt (fun t : ℝ => linearPhase ν (x + t • v)) (-ν i) 0
  simp_rw [hline]
  simpa only [id_eq, one_mul] using
    (((hasDerivAt_id (0 : ℝ)).mul_const (-ν i)).const_add (linearPhase ν x))

private theorem twistedIntegral_continuous_integrand (F : IntForm n) {a : V → ℂ}
    (ha : Continuous a) (γ : ℝ) (ν : V) :
    Continuous (fun x => a x * phase (γ * evalForm F x) * phase (linearPhase ν x)) := by
  have hF := (contDiff_evalForm F).continuous
  unfold phase linearPhase
  fun_prop

private theorem integrable_twistedIntegral_integrand (F : IntForm n) {a : V → ℂ}
    (ha : Continuous a) (hc : HasCompactSupport a) (γ : ℝ) (ν : V) :
    Integrable (fun x => a x * phase (γ * evalForm F x) * phase (linearPhase ν x)) :=
  (twistedIntegral_continuous_integrand F ha γ ν).integrable_of_hasCompactSupport
    hc.mul_right.mul_right

private theorem twistedIntegral_ibp (F : IntForm n) (i : Fin n) {a : V → ℂ}
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (γ : ℝ) (ν : V) :
    phaseCoefficient (-ν i) * twistedIntegral F a γ ν =
      -twistedIntegral F (coordinateDerivative i a) γ ν -
        phaseCoefficient γ * twistedIntegral F (fun x => a x * (evalForm (R := ℝ) (pderiv i F) x : ℂ)) γ ν := by
  let v : V := Pi.single i 1
  let ρ : V → ℝ := evalForm (pderiv i F)
  let u : V → ℂ := fun x => phase (γ * evalForm F x)
  let w : V → ℂ := fun x => phase (linearPhase ν x)
  let A : V → ℂ := fun x => a x * u x
  let D : V → ℂ := coordinateDerivative i a
  let R : V → ℂ := fun x => a x * (ρ x : ℂ)
  let A' : V → ℂ := fun x => (D x + phaseCoefficient γ * R x) * u x
  let w' : V → ℂ := fun x => phaseCoefficient (-ν i) * w x
  have hF := (contDiff_evalForm F).continuous
  have hρ := (contDiff_evalForm (pderiv i F)).continuous
  have hu : Continuous u := by dsimp [u, phase]; fun_prop
  have hw : Continuous w := by dsimp [w, phase, linearPhase]; fun_prop
  have hD := (coordinateDerivative_contDiff i ha).continuous
  have hR : Continuous R := ha.continuous.mul (Complex.continuous_ofReal.comp hρ)
  have hcD : HasCompactSupport D := coordinateDerivative_hasCompactSupport i hc
  have hcR : HasCompactSupport R := hc.mul_right
  have hA : Continuous A := ha.continuous.mul hu
  have hcA : HasCompactSupport A := hc.mul_right
  have hA' : Continuous A' :=
    (hD.add (continuous_const.mul hR)).mul hu
  have hcA' : HasCompactSupport A' := (hcD.add hcR.mul_left).mul_right
  have hw' : Continuous w' := continuous_const.mul hw
  have hwderiv (x : V) : HasLineDerivAt ℝ w (w' x) x v := by
    have hCoeff : phaseCoefficient 1 * ((-ν i : ℝ) : ℂ) = phaseCoefficient (-ν i) := by
      simp [phaseCoefficient]
    simpa only [w, w', one_mul, hCoeff] using phase_lineDeriv (linearPhase_hasLineDerivAt ν x i) 1
  have hAderiv (x : V) : HasLineDerivAt ℝ A (A' x) x v := by
    have ha' : HasLineDerivAt ℝ a (D x) x v :=
      ((ha.differentiable (by simp)).differentiableAt.hasFDerivAt).hasLineDerivAt v
    have hu' : HasLineDerivAt ℝ u (phaseCoefficient γ * (ρ x : ℂ) * u x) x v :=
      phase_lineDeriv (hasLineDerivAt_evalForm F i x) γ
    change HasDerivAt (fun t : ℝ => a (x+t • v)) (D x) 0 at ha'
    change HasDerivAt (fun t : ℝ => u (x+t • v)) _ 0 at hu'
    change HasDerivAt (fun t : ℝ => a (x+t • v) * u (x+t • v)) _ 0
    have hsum : D x * u x + a x * (phaseCoefficient γ * (ρ x : ℂ) * u x) = A' x := by
      dsimp [A', R]
      ring
    simpa only [zero_smul, add_zero, hsum] using ha'.fun_mul hu'
  have hibp :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (μ := (volume : Measure V)) (B := ContinuousLinearMap.mul ℝ ℂ)
      (f := A) (f' := A') (g := w) (g' := w')
      ((hA'.mul hw).integrable_of_hasCompactSupport hcA'.mul_right)
      ((hA.mul hw').integrable_of_hasCompactSupport hcA.mul_right)
      ((hA.mul hw).integrable_of_hasCompactSupport hcA.mul_right)
      (fun x _ => hAderiv x) (fun x _ => hwderiv x)
  change (∫ x, A x * w' x) = -(∫ x, A' x * w x) at hibp
  have hL (x : V) : A x * w' x = phaseCoefficient (-ν i) * (a x * u x * w x) := by
    dsimp [A, w']; ring
  have hR' (x : V) : A' x * w x =
      (D x * u x * w x) + phaseCoefficient γ * (R x * u x * w x) := by
    dsimp [A']; ring
  have hIntD : Integrable (fun x => D x * u x * w x) :=
    integrable_twistedIntegral_integrand F hD hcD γ ν
  have hIntR : Integrable (fun x => R x * u x * w x) :=
    integrable_twistedIntegral_integrand F hR hcR γ ν
  simp_rw [hL, hR'] at hibp
  rw [integral_add hIntD (hIntR.const_mul _), integral_const_mul, integral_const_mul, neg_add] at hibp
  exact hibp

private theorem twistedIntegral_norm_bound (F : IntForm n) (a : V → ℂ) (γ : ℝ) (ν : V) :
    ‖twistedIntegral F a γ ν‖ ≤ ∫ x, ‖a x‖ := by
  unfold twistedIntegral
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp_rw [norm_mul, norm_phase, mul_one]

private theorem twistedIntegral_coordinate_bound (F : IntForm n) (i : Fin n) (N : ℕ)
    (a : V → ℂ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∃ C > 0, ∀ (γ : ℝ) (ν : V), ‖phaseCoefficient (-ν i)‖^N * ‖twistedIntegral F a γ ν‖ ≤
      C * (1 + |γ|)^N := by
  induction N generalizing a with
  | zero =>
    have hmass : 0 ≤ (∫ x : V, ‖a x‖) := integral_nonneg (fun x => norm_nonneg (a x))
    refine ⟨(∫ x, ‖a x‖) + 1, by linarith, ?_⟩
    intro γ ν
    simpa using (twistedIntegral_norm_bound F a γ ν).trans (le_add_of_nonneg_right zero_le_one)
  | succ N ih =>
    let D : V → ℂ := coordinateDerivative i a
    let R : V → ℂ := fun x => a x * (evalForm (R := ℝ) (pderiv i F) x : ℂ)
    have hR : ContDiff ℝ ∞ R :=
      ha.mul (Complex.ofRealCLM.contDiff.comp (contDiff_evalForm _))
    obtain ⟨CD, hCD, hbD⟩ := ih D (coordinateDerivative_contDiff i ha)
      (coordinateDerivative_hasCompactSupport i hc)
    obtain ⟨CR, hCR, hbR⟩ := ih R hR hc.mul_right
    refine ⟨CD + (2 * Real.pi) * CR, by positivity, ?_⟩
    intro γ ν
    have h := congrArg norm (twistedIntegral_ibp F i ha hc γ ν)
    rw [norm_mul] at h
    have hnorm : ‖phaseCoefficient (-ν i)‖ * ‖twistedIntegral F a γ ν‖ ≤
        ‖twistedIntegral F D γ ν‖ + ‖phaseCoefficient γ‖ * ‖twistedIntegral F R γ ν‖ := by
      rw [h]
      exact (norm_sub_le _ _).trans_eq (by rw [norm_neg, norm_mul])
    have hγ : 1 ≤ 1 + |γ| := by linarith [abs_nonneg γ]
    have hγ' : |γ| ≤ 1 + |γ| := by linarith
    let S := ‖phaseCoefficient (-ν i)‖ ^ N
    let U := (1 + |γ|)^N
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hU : 0 ≤ U := by dsimp [U]; positivity
    calc
      _ = S * (‖phaseCoefficient (-ν i)‖ * ‖twistedIntegral F a γ ν‖) := by rw [pow_succ, mul_assoc]
      _ ≤ S * (‖twistedIntegral F D γ ν‖ + ‖phaseCoefficient γ‖ * ‖twistedIntegral F R γ ν‖) :=
        mul_le_mul_of_nonneg_left hnorm hS
      _ = S * ‖twistedIntegral F D γ ν‖ +
          ‖phaseCoefficient γ‖ * (S * ‖twistedIntegral F R γ ν‖) := by ring
      _ ≤ CD * U + ‖phaseCoefficient γ‖ * (CR * U) :=
        add_le_add (hbD γ ν) (mul_le_mul_of_nonneg_left (hbR γ ν) (norm_nonneg _))
      _ ≤ (CD + 2 * Real.pi * CR) * (U * (1 + |γ|)) := by
        rw [norm_phaseCoefficient]
        have h1 : CD * U ≤ CD * U * (1 + |γ|) :=
          le_mul_of_one_le_right (mul_nonneg hCD.le hU) hγ
        have h2 : 2 * Real.pi * |γ| * (CR * U) ≤
            2 * Real.pi * (1 + |γ|) * (CR * U) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγ' (by positivity)) (by positivity)
        nlinarith
      _ = _ := by rw [pow_succ]

/-- Fourier decay is uniform in both frequency parameters. The vector norm is the
sup norm on the finite product of real coordinates. -/
theorem twistedRealOscillation_decay (F : IntForm n) {w : V → ℝ}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (N : ℕ) :
    ∃ C > 0, ∀ (γ : ℝ) (ν : V), ν ≠ 0 →
      ‖twistedRealOscillation F w γ ν‖ ≤ C * ((1 + |γ|) / ‖ν‖)^N := by
  classical
  let a : V → ℂ := fun x => (w x : ℂ)
  have ha : ContDiff ℝ ∞ a := Complex.ofRealCLM.contDiff.comp hw
  have hca : HasCompactSupport a := hc.comp_left (by simp : (Complex.ofReal 0) = 0)
  choose C hC hbound using fun i => twistedIntegral_coordinate_bound F i N a ha hca
  let Ctot := 1 + ∑ i, C i
  have hCtot : 0 < Ctot := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ => (hC i).le)
  refine ⟨Ctot, hCtot, ?_⟩
  intro γ ν hν
  have hνpos : 0 < ‖ν‖ := norm_pos_iff.mpr hν
  obtain ⟨i, hi⟩ : ∃ i : Fin n, |ν i| = ‖ν‖ := by
    by_contra! h
    have ht : ‖ν‖ < ‖ν‖ := (pi_norm_lt_iff hνpos).mpr fun i => by
      rw [Real.norm_eq_abs]
      exact lt_of_le_of_ne (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ν i) (h i)
    exact (lt_irrefl _ ht)
  have hiC : C i ≤ Ctot :=
    (Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hpi : ‖ν‖ ≤ ‖phaseCoefficient (-ν i)‖ := by
    rw [← hi, norm_phaseCoefficient, abs_neg]
    simpa using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * Real.pi by
      linarith [Real.pi_gt_three]) (abs_nonneg (ν i))
  rw [twistedRealOscillation_eq_twistedIntegral, div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hνpos _)).mpr
  calc
    ‖twistedIntegral F a γ ν‖ * ‖ν‖^N ≤
        ‖phaseCoefficient (-ν i)‖^N * ‖twistedIntegral F a γ ν‖ := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hνpos.le hpi _) (norm_nonneg _)
    _ ≤ C i * (1 + |γ|)^N := hbound i γ ν
    _ ≤ _ := mul_le_mul_of_nonneg_right hiC (by positivity)

end Twisted

end

end Birch
