import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-!
# Divisor bounds for admissible products

A finite set of primes accounts for the constant in the divisor bound. Distinct
products are then counted by bounding the fibers of the tuple-to-product map.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Birch

private theorem power_dominates_succ {R : ℝ} (hR : 1 < R) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ e : ℕ, (e : ℝ) + 1 ≤ C * R ^ e := by
  have h := (isLittleO_coe_const_pow_of_one_lt (R := ℝ) hR).bound
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  let C := R + (N : ℝ) + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) N]
  refine ⟨C, hC, fun e ↦ ?_⟩
  have hRnonneg : 0 ≤ R := zero_le_one.trans hR.le
  have hpow : 1 ≤ R ^ e := one_le_pow₀ hR.le
  by_cases he : N ≤ e + 1
  · have H := hN (e + 1) he
    simp only [one_mul, Real.norm_eq_abs] at H
    rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (pow_nonneg hRnonneg _),
      Nat.cast_add, Nat.cast_one, pow_succ] at H
    refine H.trans ?_
    rw [mul_comm (R ^ e) R]
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) N])
      (pow_nonneg hRnonneg _)
  · have H : (e : ℝ) + 1 ≤ N := by exact_mod_cast (show e + 1 ≤ N by omega)
    calc
      _ ≤ C := H.trans (by dsimp [C]; linarith)
      _ ≤ _ := le_mul_of_one_le_right (zero_le_one.trans hC) hpow

/-- The fixed-loss bound for the number of positive divisors of a positive integer. -/
theorem card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 0 < N → (#N.divisors : ℝ) ≤ C * (N : ℝ) ^ ε := by
  classical
  let B : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  let R := (2 : ℝ) ^ ε
  have hR : 1 < R := Real.one_lt_rpow (by norm_num) hε
  obtain ⟨K, hK, hKexp⟩ := power_dominates_succ hR
  refine ⟨K ^ B, one_le_pow₀ hK, fun N hN ↦ ?_⟩
  let S := N.primeFactors
  let mult (p : ℕ) : ℝ := if p < B then K else 1
  let term (p : ℕ) : ℝ := ((p : ℝ) ^ N.factorization p) ^ ε
  have hterm (p : ℕ) : term p = ((p : ℝ) ^ ε) ^ N.factorization p := by
    dsimp [term]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  have hfactor : ∀ p ∈ S, (N.factorization p : ℝ) + 1 ≤ mult p * term p := by
    intro p hp
    rw [hterm]
    have hp₂ : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp₂' : (2 : ℝ) ≤ p := by exact_mod_cast hp₂
    by_cases h : p < B
    · rw [show mult p = K from ite_eq_left h]
      refine (hKexp _).trans (mul_le_mul_of_nonneg_left ?_ (zero_le_one.trans hK))
      exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (Real.rpow_le_rpow
        (by norm_num) hp₂' hε.le) _
    · rw [show mult p = 1 from ite_eq_right h, one_mul]
      have hpB : (B : ℝ) ≤ p := by exact_mod_cast (le_of_not_gt h)
      have hlarge : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        have H := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
          ((Nat.le_ceil _).trans hpB) hε.le
        rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at H
      calc
        _ ≤ (2 : ℝ) ^ N.factorization p := by exact_mod_cast
          (show N.factorization p + 1 ≤ 2 ^ N.factorization p from Nat.lt_two_pow_self)
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) hlarge _
  have hcard : #(S.filter (· < B)) ≤ B := by
    simpa using card_le_card (show S.filter (· < B) ⊆ range B from
      fun p hp ↦ mem_range.mpr (mem_filter.mp hp).2)
  have hprod : (∏ p ∈ S, mult p) ≤ K ^ B := by
    rw [show (∏ p ∈ S, mult p) = ∏ _p ∈ S.filter (· < B), K by rw [prod_filter]]
    rw [prod_const]
    exact pow_le_pow_right₀ hK hcard
  have hNprod : (∏ p ∈ S, term p) = (N : ℝ) ^ ε := by
    rw [show (∏ p ∈ S, term p) = (∏ p ∈ S, (p : ℝ) ^ N.factorization p) ^ ε from
      Real.finsetProd_rpow _ _ (by intros; positivity) _]
    norm_cast
    rw [← Nat.prod_factorization_eq_prod_primeFactors, Nat.prod_factorization_pow_eq_self hN.ne']
  calc
    (#N.divisors : ℝ) = ∏ p ∈ S, ((N.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hN.ne']
      push_cast
      rfl
    _ ≤ ∏ p ∈ S, mult p * term p :=
      prod_le_prod₀ (by intros; positivity) hfactor
    _ = (∏ p ∈ S, mult p) * (N : ℝ) ^ ε := by rw [prod_mul_distrib, hNprod]
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- For (k)-tuples of positive integers, multiplicity of every product is
(O_{k,\varepsilon}(M^\varepsilon)), uniformly in the finite family of tuples. -/
theorem card_product_fiber_le_rpow (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (Fin k → ℕ)) (M : ℕ), 0 < M →
      (#{m ∈ T | (∏ i, m i) = M} : ℝ) ≤ C * (M : ℝ) ^ ε := by
  classical
  let δ : ℝ := ε / ((k : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨K, hK, hKbound⟩ := card_divisors_le_rpow δ hδ
  refine ⟨K ^ k, pow_pos (zero_lt_one.trans_le hK) _, fun T M hM ↦ ?_⟩
  have hsub : {m ∈ T | (∏ i, m i) = M} ⊆ Fintype.piFinset (fun _ ↦ M.divisors) := by
    intro m hm
    obtain ⟨_, hm⟩ := mem_filter.mp hm
    apply Fintype.mem_piFinset.mpr
    intro i
    rw [Nat.mem_divisors]
    exact ⟨hm ▸ dvd_prod_of_mem _ (mem_univ i), hM.ne'⟩
  have hcard := card_le_card hsub
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin] at hcard
  have hMr : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  calc
    _ ≤ (#M.divisors : ℝ)^k := by exact_mod_cast hcard
    _ ≤ (K * (M : ℝ)^δ)^k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hKbound M hM) _
    _ = K^k * (M : ℝ)^(δ * k) := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hMr ?_) (by positivity)
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)]
      nlinarith

end Birch
