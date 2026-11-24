import Birch.LatticePoisson
import Birch.RealOscillationDecay
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# A quantitative Fourier bound for compactly supported amplitudes

Integration by parts in a coordinate of maximal frequency estimates the Fourier
integral using the common derivative bound on a fixed support ball.
-/

open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Birch

noncomputable section

variable {l : ℕ}

local notation "V" => (Fin l → ℝ)

private lemma smoothOrder_le_fin (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private lemma smoothOrder_lt_fin (j : ℕ) : (j : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.coe_lt_top j)

private def directionalDerivativeAtOrder (f : V → ℂ) (v : V) (j : ℕ) (x : V) : ℂ :=
  iteratedFDeriv ℝ j f x (fun _ => v)

private theorem directionalDerivativeAtOrder_continuous {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (v : V) (j : ℕ) :
    Continuous (directionalDerivativeAtOrder f v j) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => V) ℂ (fun _ => v)).continuous.comp
    (hf.continuous_iteratedFDeriv (smoothOrder_le_fin j))

private theorem directionalDerivativeAtOrder_lineDeriv {f : V → ℂ} (hf : ContDiff ℝ ∞ f)
    (v : V) (j : ℕ) (x : V) :
    HasLineDerivAt ℝ (directionalDerivativeAtOrder f v j) (directionalDerivativeAtOrder f v (j+1) x) x v := by
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => V) ℂ (fun _ => v)
  have hh := (L.hasFDerivAt.comp x
    (hf.differentiable_iteratedFDeriv (smoothOrder_lt_fin j)).differentiableAt.hasFDerivAt).hasLineDerivAt v
  have he : L (fderiv ℝ (iteratedFDeriv ℝ j f) x v) = directionalDerivativeAtOrder f v (j+1) x := by
    change (fderiv ℝ (iteratedFDeriv ℝ j f) x v) (fun _ => v) = _
    rw [fderiv_iteratedFDeriv, Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply]
    unfold directionalDerivativeAtOrder
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change HasLineDerivAt ℝ (directionalDerivativeAtOrder f v j)
    (L (fderiv ℝ (iteratedFDeriv ℝ j f) x v)) x v at hh
  simpa only [he] using hh

private theorem directionalDerivativeAtOrder_support (f : V → ℂ) (v : V) (j : ℕ) :
    Function.support (directionalDerivativeAtOrder f v j) ⊆ tsupport f := by
  intro x hx
  apply support_iteratedFDeriv_subset (𝕜 := ℝ) (f := f) j
  intro hz
  exact hx (by unfold directionalDerivativeAtOrder; rw [hz]; rfl)

private theorem directionalDerivativeAtOrder_hasCompactSupport {f : V → ℂ} (hf : HasCompactSupport f)
    (v : V) (j : ℕ) : HasCompactSupport (directionalDerivativeAtOrder f v j) := by
  apply hf.of_isClosed_subset isClosed_closure
  exact closure_minimal (directionalDerivativeAtOrder_support f v j) isClosed_closure

private def FourierLinearPhase (ν x : V) : ℝ := -∑ i, ν i * x i

private theorem FourierLinearPhase_lineDeriv (ν x : V) (i : Fin l) :
    HasLineDerivAt ℝ (FourierLinearPhase ν) (-ν i) x (Pi.single i 1) := by
  let v : V := Pi.single i 1
  have he (t : ℝ) : FourierLinearPhase ν (x+t • v) = FourierLinearPhase ν x + t*(-ν i) := by
    unfold FourierLinearPhase
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    have hsum : (∑ j, ν j * (t * v j)) = ν i * t := by
      rw [Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [v, hj]
      · simp
    rw [hsum]
    ring
  change HasDerivAt (fun t : ℝ => FourierLinearPhase ν (x + t • v)) (-ν i) 0
  simp_rw [he]
  simpa only [id_eq, one_mul] using (((hasDerivAt_id (0 : ℝ)).mul_const (-ν i)).const_add (FourierLinearPhase ν x))

private theorem fourier_directionalDerivative_ibp {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f)
    (ν : V) (i : Fin l) (j : ℕ) :
    phaseCoefficient (-ν i) * latticeFourierIntegral (directionalDerivativeAtOrder f (Pi.single i 1) j) ν =
      -latticeFourierIntegral (directionalDerivativeAtOrder f (Pi.single i 1) (j+1)) ν := by
  let v : V := Pi.single i 1
  let g : V → ℂ := directionalDerivativeAtOrder f v j
  let g' : V → ℂ := directionalDerivativeAtOrder f v (j+1)
  let e : V → ℂ := fun x => phase (FourierLinearPhase ν x)
  let e' : V → ℂ := fun x => phaseCoefficient (-ν i) * e x
  have hgc : Continuous g := directionalDerivativeAtOrder_continuous hf _ _
  have hg'c : Continuous g' := directionalDerivativeAtOrder_continuous hf _ _
  have hgs : HasCompactSupport g := directionalDerivativeAtOrder_hasCompactSupport hfs _ _
  have hg's : HasCompactSupport g' := directionalDerivativeAtOrder_hasCompactSupport hfs _ _
  have hec : Continuous e := by dsimp [e, FourierLinearPhase, phase]; fun_prop
  have he'c : Continuous e' := continuous_const.mul hec
  have heder (x : V) : HasLineDerivAt ℝ e (e' x) x v := by
    have heCoeff : phaseCoefficient 1 * ((-ν i : ℝ) : ℂ) = phaseCoefficient (-ν i) := by simp [phaseCoefficient]
    simpa only [e, e', one_mul, heCoeff] using phase_lineDeriv (FourierLinearPhase_lineDeriv ν x i) 1
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure V)) (B := ContinuousLinearMap.mul ℝ ℂ) (f := g) (f' := g') (g := e) (g' := e')
    ((hg'c.mul hec).integrable_of_hasCompactSupport hg's.mul_right)
    ((hgc.mul he'c).integrable_of_hasCompactSupport hgs.mul_right)
    ((hgc.mul hec).integrable_of_hasCompactSupport hgs.mul_right)
    (fun x _ => directionalDerivativeAtOrder_lineDeriv hf v j x) (fun x _ => heder x)
  change (∫ x, g x * e' x) = -(∫ x, g' x * e x) at h
  have hleft (x : V) : g x * e' x = phaseCoefficient (-ν i) * (e x * g x) := by unfold e'; ring
  simp_rw [hleft, integral_const_mul, mul_comm (g' _) (e _)] at h
  exact h

/-- A single derivative bound controls every Fourier frequency with a common
constant, with the support-ball volume made explicit. -/
theorem latticeFourierIntegral_decay_of_bounded_derivatives {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} {R C : ℝ} (hC : 0 ≤ C)
    (hSupport : ∀ x, f x ≠ 0 → ‖x‖ ≤ R)
    (hDerivatives : ∀ j ≤ N, ∀ x, ‖x‖ ≤ R → ‖iteratedFDeriv ℝ j f x‖ ≤ C) (ν : V) :
    ‖latticeFourierIntegral f ν‖ ≤
      ((2 : ℝ)^N * C * (volume : Measure V).real (Metric.closedBall (0 : V) R)) * (1+‖ν‖)^(-(N : ℝ)) := by
  let S := Metric.closedBall (0 : V) R
  have hS : IsCompact S := isCompact_closedBall _ _
  have hsupp : tsupport f ⊆ S := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    simpa only [S, Metric.mem_closedBall, dist_zero_right] using hSupport x hx
  have hfs : HasCompactSupport f := hS.of_isClosed_subset isClosed_closure hsupp
  let M := C*(volume : Measure V).real S
  have hM : 0 ≤ M := mul_nonneg hC measureReal_nonneg
  have hbase : ‖latticeFourierIntegral f ν‖ ≤ M := by
    unfold latticeFourierIntegral
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun x hx => by
      have h0 : f x = 0 := by by_contra h; exact hx (hsupp (subset_tsupport f h))
      simp [h0])]
    apply norm_setIntegral_le_of_norm_le_const hS.measure_lt_top
    intro x hx
    simp only [norm_mul, norm_phase, one_mul]
    have hxr : ‖x‖ ≤ R := by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hx
    simpa only [norm_iteratedFDeriv_zero] using hDerivatives 0 (by omega) x hxr
  have hhigh (i : Fin l) : ‖phaseCoefficient (-ν i)‖^N * ‖latticeFourierIntegral f ν‖ ≤ M := by
    let v : V := Pi.single i 1
    have hvec : ‖v‖ ≤ 1 := by
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro j
      by_cases h : j = i <;> simp [v, h]
    have hpow (j : ℕ) : ‖phaseCoefficient (-ν i)‖^j * ‖latticeFourierIntegral f ν‖ =
        ‖latticeFourierIntegral (directionalDerivativeAtOrder f v j) ν‖ := by
      induction j with
      | zero =>
        have hz : directionalDerivativeAtOrder f v 0 = f := by
          funext x
          simp [directionalDerivativeAtOrder, iteratedFDeriv_zero_apply]
        simp [hz]
      | succ j ih =>
        rw [pow_succ', mul_assoc, ih, ← norm_mul,
          fourier_directionalDerivative_ibp hf hfs ν i j, norm_neg]
    rw [hpow]
    unfold latticeFourierIntegral
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun x hx => by
      have h0 : directionalDerivativeAtOrder f v N x = 0 := by
        by_contra h
        exact hx (hsupp (directionalDerivativeAtOrder_support f v N h))
      simp [h0])]
    apply norm_setIntegral_le_of_norm_le_const hS.measure_lt_top
    intro x hx
    simp only [norm_mul, norm_phase, one_mul]
    unfold directionalDerivativeAtOrder
    refine ((iteratedFDeriv ℝ N f x).le_opNorm (fun _ => v)).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hD := hDerivatives N le_rfl x (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hx)
    exact (mul_le_mul_of_nonneg_right hD (by positivity)).trans
      (mul_le_of_le_one_right hC (pow_le_one₀ (norm_nonneg _) hvec))
  have hmono : ‖latticeFourierIntegral f ν‖ * (1+‖ν‖)^N ≤ (2 : ℝ)^N * M := by
    by_cases hν : ‖ν‖ ≤ 1
    · exact (mul_le_mul hbase (pow_le_pow_left₀ (by positivity) (show 1+‖ν‖ ≤ 2 by linarith) _) (by positivity) hM).trans_eq (mul_comm _ _)
    · have hν' : 0 < ‖ν‖ := lt_trans zero_lt_one (lt_of_not_ge hν)
      obtain ⟨i, hi⟩ : ∃ i : Fin l, |ν i| = ‖ν‖ := by
        by_contra! h
        have hlt : ‖ν‖ < ‖ν‖ := (pi_norm_lt_iff hν').mpr fun i => by
          rw [Real.norm_eq_abs]
          exact lt_of_le_of_ne (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ν i) (h i)
        exact (lt_irrefl _ hlt)
      have hcoeff : ‖ν‖ ≤ ‖phaseCoefficient (-ν i)‖ := by
        rw [← hi, norm_phaseCoefficient, abs_neg]
        simpa using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2*Real.pi by linarith [Real.pi_gt_three]) (abs_nonneg (ν i))
      have hcoefPow := pow_le_pow_left₀ (norm_nonneg ν) hcoeff N
      have hbound := (mul_le_mul_of_nonneg_right hcoefPow (norm_nonneg (latticeFourierIntegral f ν))).trans (hhigh i)
      calc
        _ ≤ ‖latticeFourierIntegral f ν‖ * (2*‖ν‖)^N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show 1+‖ν‖ ≤ 2*‖ν‖ by linarith [lt_of_not_ge hν]) _) (norm_nonneg _)
        _ = (2 : ℝ)^N * (‖ν‖^N * ‖latticeFourierIntegral f ν‖) := by rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [S, M, mul_assoc] using hmono

end

end Birch
