import Birch.DeligneTensorPhase
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Amplification with a finite number of additive factors -/

open Filter MvPolynomial
open scoped Topology

namespace Birch

/-- Logarithmically many factors absorb a polynomial loss in the field
size, while a fixed power of the number of factors is smaller than any
positive power of the field size. -/
theorem eventually_exists_additivePowerLength (D : ℕ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ p : ℕ in atTop, ∃ k : ℕ, 2 ≤ k ∧ (p : ℝ) ≤ (Real.exp 1)^k ∧
      ((k + 1 : ℕ) : ℝ)^D ≤ c * (p : ℝ)^δ := by
  have hlog : (fun x : ℝ => (Real.log x)^D) =o[atTop] (fun x => x^δ) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (D : ℝ) hδ
  have hsmall := (hlog.bound (show 0 < c/(2 : ℝ)^D by positivity))
  have hpos : ∀ᶠ p : ℕ in atTop, (0 : ℝ) < p :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))
  have hlarge : ∀ᶠ p : ℕ in atTop, 2 ≤ Real.log (p : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hpos, hlarge, tendsto_natCast_atTop_atTop.eventually hsmall] with p hp hge hsmallp
  let k := ⌈Real.log (p : ℝ)⌉₊
  have hceil : Real.log (p : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hk : 2 ≤ k := by exact_mod_cast hge.trans hceil
  refine ⟨k, hk, ?_, ?_⟩
  · rw [← Real.exp_nat_mul, mul_one, ← Real.exp_log hp, Real.exp_le_exp]
    exact hceil
  · have hcast : ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.log (p : ℝ) := by
      push_cast
      have hlt : (k : ℝ) < Real.log (p : ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
      linarith
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hsmallp
    calc
      ((k + 1 : ℕ) : ℝ)^D ≤ (2 * Real.log (p : ℝ))^D := by gcongr
      _ ≤ (2 : ℝ)^D * (c/(2 : ℝ)^D * (p : ℝ)^δ) := by rw [mul_pow]; gcongr
      _ = _ := by
        have htwo : (2 : ℝ)^D ≠ 0 := by positivity
        field_simp

/-- Bounds for the levels at one logarithmically large power give a
square-root bound. The extra fixed power of the field size becomes a constant. -/
theorem norm_primeDeligneSum_le_of_single_power_counts {p l k : ℕ} [Fact p.Prime] [NeZero p]
    (g : MvPolynomial (Fin l) (ZMod p)) (hl : 0 < l) (hk : 0 < k)
    (hlog : (p : ℝ) ≤ (Real.exp 1)^k) {A B : ℝ} (hA : 1 ≤ A) (hB : 0 < B) (a : ℕ)
    (hcount : ∀ t : ZMod p, t ≠ 0 →
      |(affinePolynomialLevelCount (additivePowerPolynomialFin k g) t : ℝ) - (p : ℝ)^(k*l-1)| ≤
        A * (p : ℝ)^a * (B^l * (p : ℝ)^((l : ℝ)/2))^k) :
    ‖primeDeligneSum p g‖ ≤ (2 * A * Real.exp 1 ^ (a+1)) * (B^l * (p : ℝ)^((l : ℝ)/2)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  let L := B^l * (p : ℝ)^((l : ℝ)/2)
  have hL : 0 ≤ L := by positivity
  have hpow : ‖primeDeligneSum p g‖^k ≤ (2 * A) * (p : ℝ)^(a+1) * L^k := by
    have h := norm_character_sum_pow_le_of_additivePowerFiberErrors
      (Fact.out : p.Prime).one_lt (fun x => g.eval x) k
      (show 0 ≤ A * (p : ℝ)^a * L^k by positivity) (fun t ht => ?_)
    · change ‖primeDeligneSum p g‖^k ≤ _ at h
      refine h.trans_eq ?_
      rw [pow_succ]
      ring
    · rw [additivePowerFiberCount_eq_card_eval_additivePowerPolynomialFin]
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, ← pow_mul]
      have hmean : (p : ℝ)^(l*k) / p = (p : ℝ)^(k*l-1) := by
        have he : l*k = k*l-1+1 := by
          rw [Nat.mul_comm l k]
          have := Nat.mul_pos hk hl
          omega
        rw [he, pow_succ, mul_div_cancel_right₀ _ hp.ne']
      rw [hmean]
      exact hcount t ht
  apply le_of_pow_le_pow_left₀ hk.ne' (by positivity)
  refine hpow.trans ?_
  change _ ≤ ((2 * A * Real.exp 1 ^ (a+1)) * L)^k
  rw [mul_pow (2 * A * Real.exp 1 ^ (a+1)) L, mul_pow (2 * A) (Real.exp 1 ^ (a+1))]
  have hfac : 2 * A ≤ (2 * A)^k := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ (2 : ℝ) * A) (show 1 ≤ k by omega)
  have hscale : (p : ℝ)^(a+1) ≤ (Real.exp 1 ^ (a+1))^k := by
    rw [← pow_mul, Nat.mul_comm (a+1), pow_mul]
    exact pow_le_pow_left₀ hp.le hlog (a+1)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hfac hscale (by positivity) (by positivity)) (pow_nonneg hL _)

/-- Estimates on the nonzero levels of one fixed additive power give a
character-sum estimate with an explicit loss of `(a + 1) / k` in the exponent. -/
theorem norm_primeDeligneSum_le_of_fixed_power_counts {p l k a : ℕ}
    [Fact p.Prime] [NeZero p] (g : MvPolynomial (Fin l) (ZMod p)) (hl : 0 < l) (hk : 0 < k)
    {A : ℝ} (hA : 1 ≤ A)
    (hcount : ∀ t : ZMod p, t ≠ 0 →
      |(affinePolynomialLevelCount (additivePowerPolynomialFin k g) t : ℝ) -
        (p : ℝ)^(k*l-1)| ≤ A * (p : ℝ)^a * ((p : ℝ)^((l : ℝ)/2))^k) :
    ‖primeDeligneSum p g‖ ≤ (2 * A) * (p : ℝ)^((l : ℝ)/2 + ((a+1 : ℕ) : ℝ) / k) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  let L := (p : ℝ)^((l : ℝ)/2)
  have hpow : ‖primeDeligneSum p g‖^k ≤ (2 * A) * (p : ℝ)^(a+1) * L^k := by
    have h := norm_character_sum_pow_le_of_additivePowerFiberErrors
      (Fact.out : p.Prime).one_lt (fun x => g.eval x) k
      (show 0 ≤ A * (p : ℝ)^a * L^k by positivity) (fun t ht => ?_)
    · change ‖primeDeligneSum p g‖^k ≤ _ at h
      refine h.trans_eq ?_
      rw [pow_succ]
      ring
    · rw [additivePowerFiberCount_eq_card_eval_additivePowerPolynomialFin]
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, ← pow_mul]
      have hmean : (p : ℝ)^(l*k) / p = (p : ℝ)^(k*l-1) := by
        have he : l*k = k*l-1+1 := by
          rw [Nat.mul_comm l k]
          have := Nat.mul_pos hk hl
          omega
        rw [he, pow_succ, mul_div_cancel_right₀ _ hp.ne']
      rw [hmean]
      exact hcount t ht
  apply le_of_pow_le_pow_left₀ hk.ne' (by positivity)
  refine hpow.trans ?_
  let e : ℝ := ((a+1 : ℕ) : ℝ) / k
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hscale : ((p : ℝ)^e)^k = (p : ℝ)^(a+1) := by
    rw [← Real.rpow_mul_natCast hp.le, show e * (k : ℝ) = ((a+1 : ℕ) : ℝ) by
      dsimp [e]
      exact div_mul_cancel₀ _ hkR, Real.rpow_natCast]
  have hfac : 2 * A ≤ (2 * A)^k := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ (2 : ℝ) * A) (show 1 ≤ k by omega)
  rw [show (l : ℝ)/2 + ((a+1 : ℕ) : ℝ) / k = e + (l : ℝ)/2 by dsimp [e]; ring,
    Real.rpow_add hp, show (p : ℝ)^((l : ℝ)/2) = L by rfl,
    mul_pow (2*A) _, mul_pow ((p : ℝ)^e) L, hscale, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfac (by positivity)) (by positivity)

end Birch
