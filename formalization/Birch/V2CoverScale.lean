import Birch.FrozenCoordinates
import Birch.Geometry
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# The scale of the polynomial-cover variable

The height bound in Section 7 of `v2.tex` follows from homogeneity on a
compact real cube and the growth of an integral polynomial at both ends
of the real line.
-/

open Filter MeasureTheory Polynomial Set
open scoped Polynomial Topology

namespace Birch

noncomputable section

theorem exists_abs_form_eval_bound_on_latticeBox {n d : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (P : ℝ), 0 < P → ∀ (x : Fin n → ℤ), x ∈ latticeBox n P →
      |((evalForm F x : ℤ) : ℝ)| ≤ B * P ^ d := by
  let box : Set (Fin n → ℝ) := Set.Icc (fun _ => -1) (fun _ => 1)
  have hcompact : IsCompact box := isCompact_Icc
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn (continuous_evalForm F).continuousOn
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro P hP x hx
  let u := scaledPoint P x
  have hu : u ∈ box := by
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hi := (abs_le.mp (mem_latticeBox_iff_abs.mp hx i)).1
      change -1 ≤ (x i : ℝ) / P
      exact (le_div_iff₀ hP).2 (by simpa using hi)
    · have hi := (abs_le.mp (mem_latticeBox_iff_abs.mp hx i)).2
      change (x i : ℝ) / P ≤ 1
      exact (div_le_iff₀ hP).2 (by simpa using hi)
  have hcast := evalForm_hom (Int.castRingHom ℝ) F x
  simp only [Int.coe_castRingHom] at hcast
  have hscale : (fun i => (x i : ℝ)) = fun i => P * u i := by
    funext i
    change (x i : ℝ) = P * ((x i : ℝ) / P)
    field_simp
  rw [hcast, hscale, evalForm_scale hF, abs_mul, abs_of_nonneg (pow_nonneg hP.le d), mul_comm]
  exact mul_le_mul_of_nonneg_right
    ((by simpa only [Real.norm_eq_abs] using hB u hu : |evalForm F u| ≤ B).trans
      (le_max_right 1 B)) (pow_nonneg hP.le d)

private theorem exists_real_abs_pow_le_polynomial_eval (q : ℝ[X]) (hq : q ≠ 0) :
    ∃ D R : ℝ, 0 < D ∧ 0 ≤ R ∧ ∀ y : ℝ, R ≤ |y| →
      |y| ^ q.natDegree ≤ D * |q.eval y| := by
  obtain ⟨Ctop, hCtop, hpos⟩ := q.isEquivalent_atTop_lead.isBigO_symm.exists_pos
  obtain ⟨Cbot, hCbot, hneg⟩ := q.isEquivalent_atBot_lead.isBigO_symm.exists_pos
  obtain ⟨Rtop, hRtop⟩ := eventually_atTop.mp hpos.bound
  obtain ⟨Rbot, hRbot⟩ := eventually_atBot.mp hneg.bound
  have hlc : 0 < |q.leadingCoeff| := abs_pos.mpr (leadingCoeff_ne_zero.mpr hq)
  let D := max Ctop Cbot
  let R := max 0 (max Rtop (-Rbot))
  refine ⟨D / |q.leadingCoeff|, R, div_pos (hCtop.trans_le (le_max_left _ _)) hlc,
    le_max_left _ _, ?_⟩
  intro y hy
  have htail : ‖q.leadingCoeff * y ^ q.natDegree‖ ≤ D * ‖q.eval y‖ := by
    by_cases hy₀ : 0 ≤ y
    · rw [abs_of_nonneg hy₀] at hy
      have hytop : Rtop ≤ y := (le_max_left Rtop (-Rbot)).trans ((le_max_right 0 _).trans hy)
      exact (hRtop y hytop).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · rw [abs_of_neg (lt_of_not_ge hy₀)] at hy
      have hybot : -Rbot ≤ -y := (le_max_right Rtop (-Rbot)).trans ((le_max_right 0 _).trans hy)
      exact (hRbot y (neg_le_neg_iff.mp hybot)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  rw [Real.norm_eq_abs, abs_mul, abs_pow, Real.norm_eq_abs] at htail
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hlc).2 (by simpa only [mul_comm |q.leadingCoeff| (|y| ^ q.natDegree)] using htail)

private theorem exists_abs_pow_le_int_polynomial_eval (g : ℤ[X]) {e : ℕ}
    (he : 0 < e) (hge : g.natDegree = e) :
    ∃ D R : ℝ, 0 < D ∧ 0 ≤ R ∧ ∀ y : ℤ, R ≤ |(y : ℝ)| →
      |(y : ℝ)| ^ e ≤ D * |((g.eval y : ℤ) : ℝ)| := by
  have hg₀ : g ≠ 0 := by
    intro h
    simp [h] at hge
    omega
  let q := g.map (Int.castRingHom ℝ)
  have hlead : (Int.castRingHom ℝ) g.leadingCoeff ≠ 0 :=
    Int.cast_ne_zero.mpr (leadingCoeff_ne_zero.mpr hg₀)
  have hq : q ≠ 0 := by
    have hz : q.leadingCoeff ≠ 0 := by
      rw [leadingCoeff_map_of_leadingCoeff_ne_zero _ hlead]
      exact hlead
    exact leadingCoeff_ne_zero.mp hz
  have hqe : q.natDegree = e :=
    (natDegree_map_of_leadingCoeff_ne_zero _ hlead).trans hge
  obtain ⟨D, R, hD, hR, h⟩ := exists_real_abs_pow_le_polynomial_eval q hq
  refine ⟨D, R, hD, hR, fun y hy => ?_⟩
  have hEval := eval_intCast_map (Int.castRingHom ℝ) g y
  change q.eval (y : ℝ) = ((g.eval y : ℤ) : ℝ) at hEval
  simpa only [hqe, hEval] using h (y : ℝ) hy

/-- Every integral solution on `|x| ≤ P` has `|y| ≤ C * P^(d/e)`,
with one constant for all `P ≥ 1`. -/
theorem exists_cover_y_bound {n d e : ℕ} {F : IntForm n} (hF : F.IsHomogeneous d)
    (g : ℤ[X]) (he : 0 < e) (hge : g.natDegree = e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : ℝ), 1 ≤ P →
      ∀ (x : Fin n → ℤ) (y : ℤ), x ∈ latticeBox n P →
        evalForm F x = g.eval y → |(y : ℝ)| ≤ C * P ^ ((d : ℝ) / e) := by
  obtain ⟨B, hB, hFb⟩ := exists_abs_form_eval_bound_on_latticeBox hF
  obtain ⟨D, R, hD, hR, hGb⟩ := exists_abs_pow_le_int_polynomial_eval g he hge
  let r : ℝ := 1 / (e : ℝ)
  let C := max 1 (max R ((D * B) ^ r))
  refine ⟨C, le_max_left _ _, ?_⟩
  intro P hP x y hx hxy
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hr : 0 ≤ r := by dsimp [r]; positivity
  by_cases hy : R ≤ |(y : ℝ)|
  · have hy' : |(y : ℝ)| ^ e ≤ (D * B) * P ^ d := by
      calc
        _ ≤ D * |((g.eval y : ℤ) : ℝ)| := hGb y hy
        _ ≤ D * (B * P ^ d) := by
          rw [← hxy]
          exact mul_le_mul_of_nonneg_left (hFb P hP₀ x hx) hD.le
        _ = _ := by ring
    calc
      |(y : ℝ)| = (|(y : ℝ)| ^ e) ^ r := by
        rw [← Real.rpow_natCast_mul (abs_nonneg _), show (e : ℝ) * r = 1 by
          dsimp [r]
          field_simp, Real.rpow_one]
      _ ≤ ((D * B) * P ^ d) ^ r := Real.rpow_le_rpow (by positivity) hy' hr
      _ = (D * B) ^ r * P ^ ((d : ℝ) / e) := by
        rw [Real.mul_rpow (mul_nonneg hD.le (by linarith)) (pow_nonneg hP₀.le d),
          ← Real.rpow_natCast_mul hP₀.le]
        simp only [r, mul_one_div]
      _ ≤ C * P ^ ((d : ℝ) / e) :=
        mul_le_mul_of_nonneg_right ((le_max_right R _).trans (le_max_right 1 _)) (by positivity)
  · calc
      |(y : ℝ)| ≤ R := (lt_of_not_ge hy).le
      _ ≤ C := (le_max_left R _).trans (le_max_right 1 _)
      _ ≤ C * P ^ ((d : ℝ) / e) := by
        apply le_mul_of_one_le_right (by positivity)
        apply Real.one_le_rpow hP
        positivity


/-- After scaling, the lower coefficients contribute at most a fixed
multiple of `1 / Y` on the whole interval `[-1, 1]`. -/
theorem abs_scaledCoverPolynomial_sub_leading_le (g : ℤ[X]) {e : ℕ}
    (hge : g.natDegree = e) (Y t : ℝ) (hY : 1 ≤ Y) (ht : |t| ≤ 1) :
    |g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e - (g.leadingCoeff : ℝ) * t ^ e| ≤
      (∑ i ∈ Finset.range e, |(g.coeff i : ℝ)|) / Y := by
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  have hc : g.coeff e = g.leadingCoeff := by
    rw [← hge, leadingCoeff]
  have hlead :
      ((g.leadingCoeff : ℝ) * (Y * t) ^ e) / Y ^ e = (g.leadingCoeff : ℝ) * t ^ e := by
    rw [mul_pow]
    field_simp
  have heval :
      g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e - (g.leadingCoeff : ℝ) * t ^ e =
        ∑ i ∈ Finset.range e, ((g.coeff i : ℝ) * (Y * t) ^ i) / Y ^ e := by
    rw [eval₂_eq_sum_range, hge, Finset.sum_range_succ, Int.coe_castRingHom, hc,
      add_div, hlead, add_sub_cancel_right, Finset.sum_div]
  rw [heval, Finset.sum_div]
  calc
    _ ≤ ∑ i ∈ Finset.range e, |((g.coeff i : ℝ) * (Y * t) ^ i) / Y ^ e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range e, |(g.coeff i : ℝ)| / Y := by
      apply Finset.sum_le_sum
      intro i hi
      have hit : |t| ^ i ≤ 1 := by
        simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg t) ht i
      simp only [abs_div, abs_mul, abs_pow, abs_of_pos hY₀, mul_pow]
      calc
        _ ≤ (|(g.coeff i : ℝ)| * Y ^ i) / Y ^ e := by
          apply div_le_div_of_nonneg_right _ (pow_nonneg hY₀.le e)
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (pow_nonneg hY₀.le i) hit)
            (abs_nonneg _)
        _ ≤ |(g.coeff i : ℝ)| / Y := by
          apply (div_le_div_iff₀ (pow_pos hY₀ e) hY₀).2
          have heip : i + 1 ≤ e := Finset.mem_range.mp hi
          have hpow := pow_le_pow_right₀ hY heip
          rw [pow_succ] at hpow
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow
            (abs_nonneg (g.coeff i : ℝ))

/-- The uniform polynomial approximation on the paper's scale
`Y = P^(d/e)` for `|t| ≤ 1`. -/
theorem abs_coverScaledPhase_sub_leading_le (g : ℤ[X]) {d e : ℕ}
    (he : 0 < e) (hge : g.natDegree = e) {P t : ℝ} (hP : 1 ≤ P) (ht : |t| ≤ 1) :
    let Y := P ^ ((d : ℝ) / e)
    |P ^ (-(d : ℝ)) * g.eval₂ (Int.castRingHom ℝ) (Y * t) -
        (g.leadingCoeff : ℝ) * t ^ e| ≤ (∑ i ∈ Finset.range e, |(g.coeff i : ℝ)|) / Y := by
  let Y := P ^ ((d : ℝ) / e)
  have hY : 1 ≤ Y := Real.one_le_rpow hP (by positivity)
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have he₀ : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hYpow : Y ^ e = P ^ d := by
    dsimp [Y]
    rw [← Real.rpow_mul_natCast hP₀.le, div_mul_cancel₀ _ he₀, Real.rpow_natCast]
  have h := abs_scaledCoverPolynomial_sub_leading_le g hge Y t hY ht
  rw [hYpow, div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg hP₀.le, mul_comm] at h
  exact h


/-- The circle phase is Lipschitz with constant `2π`. -/
theorem norm_phase_sub_le (s t : ℝ) : ‖phase s - phase t‖ ≤ 2 * Real.pi * |s - t| := by
  have hprod : phase s = phase t * phase (s - t) := by
    unfold phase
    rw [← Complex.exp_add]
    push_cast
    congr 1
    ring
  have hunit : ‖phase t‖ = 1 := by
    rw [phase, Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hexp : phase (s - t) = Complex.exp (Complex.I * ((2 * Real.pi * (s - t) : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  have hdiff : phase s - phase t = phase t * (phase (s - t) - 1) := by
    rw [hprod, mul_sub, mul_one]
  rw [hdiff, norm_mul, hunit, one_mul, hexp]
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (s - t)))

/-- The integrated error when the full rescaled polynomial in the real
cover factor is replaced by its leading term. -/
theorem norm_coverIntervalIntegral_sub_leading_le (g : ℤ[X]) {d e : ℕ}
    (he : 0 < e) (hge : g.natDegree = e) {P : ℝ} (hP : 1 ≤ P) (γ : ℝ) :
    let Y := P ^ ((d : ℝ) / e)
    ‖(∫ t in (-1 : ℝ)..1,
        phase (-γ * (P ^ (-(d : ℝ)) * g.eval₂ (Int.castRingHom ℝ) (Y * t)))) -
      (∫ t in (-1 : ℝ)..1, phase (-γ * (g.leadingCoeff : ℝ) * t ^ e))‖ ≤
      4 * Real.pi * |γ| * ((∑ i ∈ Finset.range e, |(g.coeff i : ℝ)|) / Y) := by
  let Y := P ^ ((d : ℝ) / e)
  let G (t : ℝ) := P ^ (-(d : ℝ)) * g.eval₂ (Int.castRingHom ℝ) (Y * t)
  let L (t : ℝ) := (g.leadingCoeff : ℝ) * t ^ e
  let C : ℝ := (∑ i ∈ Finset.range e, |(g.coeff i : ℝ)|) / Y
  have hphase : Continuous phase := by
    unfold phase
    fun_prop
  have hG : Continuous G := by
    dsimp only [G]
    fun_prop
  have hL : Continuous L := by
    dsimp only [L]
    fun_prop
  let f (t : ℝ) := phase (-γ * G t)
  let l (t : ℝ) := phase (-γ * L t)
  have hf : Continuous f := by
    change Continuous (fun t => phase (-γ * G t))
    fun_prop
  have hl : Continuous l := by
    change Continuous (fun t => phase (-γ * L t))
    fun_prop
  suffices h : ‖(∫ t in (-1 : ℝ)..1, f t) - (∫ t in (-1 : ℝ)..1, l t)‖ ≤
      4 * Real.pi * |γ| * C by
    simpa only [Y, C, f, l, G, L, mul_assoc] using h
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hl.intervalIntegrable _ _)]
  have hpoint (t : ℝ) (ht : t ∈ Set.uIoc (-1 : ℝ) 1) :
      ‖f t - l t‖ ≤ 2 * Real.pi * |γ| * C := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    have htab : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have h := norm_phase_sub_le (-γ * G t) (-γ * L t)
    rw [← mul_sub, abs_mul, abs_neg] at h
    have hdiff : |G t - L t| ≤ C := abs_coverScaledPhase_sub_leading_le g he hge hP htab
    apply h.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdiff
      (by positivity : 0 ≤ 2 * Real.pi * |γ|)
  calc
    _ ≤ (2 * Real.pi * |γ| * C) * |(1 : ℝ) - (-1)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = _ := by norm_num; ring

end
end Birch
