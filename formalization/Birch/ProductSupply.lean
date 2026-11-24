import Birch.DivisorBounds
import Birch.Metric

/-!
# Supply of distinct admissible products

Taking each factor between one and the floor of its maximum permitted size gives
enough tuples. The fixed-order divisor bound controls how many have the same product.
-/

open Filter Finset

namespace Birch

private theorem dyadic_reciprocal_sum (k : ℕ) :
    (∑ i : Fin k, 1 / (2 : ℝ) ^ (k - (i.val + 1))) = 2 - 2 / (2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_succ]
      have hswap : (∑ i : Fin k, 1 / (2 : ℝ) ^ (k + 1 - (i.succ.val + 1))) =
          (∑ i : Fin k, 1 / (2 : ℝ) ^ (k - (i.val + 1))) := by
        apply sum_congr rfl
        intro i _
        simp only [Fin.val_succ]
        congr 2
        omega
      rw [hswap, ih, pow_succ]
      simp only [Fin.val_zero, zero_add, Nat.add_sub_cancel]
      have hpow : (2 : ℝ)^k ≠ 0 := by positivity
      field_simp
      ring

/-- The metric argument has a set of distinct admissible products with the stated
lower bound for every positive power loss. -/
theorem metricProductSupply (d : ℕ) : MetricProductSupply d := by
  classical
  intro r h _ hr hh hh' ε hε
  let k := d - r
  let θ : ℝ := ε / ((k : ℝ) + 1)
  have hθ : 0 < θ := div_pos hε (by positivity)
  obtain ⟨K, hK, hKbound⟩ := card_product_fiber_le_rpow k θ hθ
  refine ⟨(1 / 2 : ℝ) ^ k / K, div_pos (by positivity) hK, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with P hP₄
  have hP : 0 < P := by linarith
  have hP₁ : 1 ≤ P := by linarith
  let Q := P ^ h
  have hQ : 1 ≤ Q := Real.one_le_rpow hP₁ hh.le
  let H (i : Fin k) : ℝ := Q ^ (1 / (2 : ℝ) ^ (k - (i.val + 1)))
  let U (i : Fin k) := P / H i
  have hH₁ (i : Fin k) : 1 ≤ H i := Real.one_le_rpow hQ (by positivity)
  have hHpos (i : Fin k) : 0 < H i := zero_lt_one.trans_le (hH₁ i)
  have hU₂ (i : Fin k) : 2 ≤ U i := by
    have hH : H i ≤ P ^ (1 / 2 : ℝ) := by
      dsimp [H, Q]
      rw [← Real.rpow_mul hP.le, mul_one_div]
      have hw : 1 ≤ (2 : ℝ) ^ (k - (i.val + 1)) := one_le_pow₀ (by norm_num)
      apply Real.rpow_le_rpow_of_exponent_le hP₁
      exact (div_le_self hh.le hw).trans hh'
    have hroot : 2 ≤ P ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      nlinarith [Real.sq_sqrt hP.le, Real.sqrt_nonneg P]
    have hrootsq : (P ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = P := by
      rw [← Real.rpow_mul_natCast hP.le]
      norm_num
    have hbound : 2 * H i ≤ P := by
      calc
        _ ≤ P ^ (1 / 2 : ℝ) * P ^ (1 / 2 : ℝ) :=
          mul_le_mul hroot hH (hHpos i).le (by positivity)
        _ = P := by rw [← sq, hrootsq]
    exact (le_div_iff₀ (hHpos i)).mpr hbound
  have hUpos (i : Fin k) : 0 < U i := lt_of_lt_of_le (by norm_num) (hU₂ i)
  have hUP (i : Fin k) : U i ≤ P := div_le_self hP.le (hH₁ i)
  have hprod : (∏ i, U i) = metricProductScale d r P h := by
    simp only [U, prod_div_distrib, prod_const, card_univ, Fintype.card_fin, H,
      ← Real.rpow_sum_of_pos (zero_lt_one.trans_le hQ), dyadic_reciprocal_sum]
    unfold metricProductScale dilationRho
    rw [div_eq_mul_inv, ← Real.rpow_neg (zero_le_one.trans hQ), ← Real.rpow_natCast, show (k : ℝ) = (d : ℝ) - r by exact Nat.cast_sub hr.le]
  let T := Fintype.piFinset (fun i : Fin k ↦ Icc 1 ⌊U i⌋₊)
  let product : (Fin k → ℕ) → ℕ := fun m ↦ ∏ i, m i
  let E := T.image product
  have hE (M : ℕ) (hM : M ∈ E) :
      0 < M ∧ (M : ℝ) ≤ metricProductScale d r P h ∧ admissibleProduct d r P Q M := by
    obtain ⟨m, hm, rfl⟩ := mem_image.mp hM
    have hi (i : Fin k) := mem_Icc.mp (Fintype.mem_piFinset.mp hm i)
    have hmi (i : Fin k) : (m i : ℝ) ≤ U i :=
      (Nat.cast_le.mpr (hi i).2).trans (Nat.floor_le (hUpos i).le)
    refine ⟨Finset.prod_pos (fun i _ ↦ (hi i).1), ?_, m, rfl, ?_⟩
    · rw [← hprod]
      dsimp only [product]
      push_cast
      exact prod_le_prod (by intros; positivity) (fun i _ ↦ hmi i)
    · intro i
      exact ⟨(hi i).1, (le_div_iff₀ (hHpos i)).mp (hmi i)⟩
  refine ⟨E, fun M hM ↦ hE M hM, ?_⟩
  have hcardT : (1 / 2 : ℝ)^k * metricProductScale d r P h ≤ (T.card : ℝ) := by
    rw [← hprod]
    have hhalf : (∏ _i : Fin k, (1 / 2 : ℝ)) = (1 / 2 : ℝ)^k := by simp
    rw [← hhalf, ← prod_mul_distrib]
    simp only [T, Fintype.card_piFinset, Nat.cast_prod, Nat.card_Icc, Nat.add_sub_cancel]
    apply prod_le_prod (by intros; positivity)
    intro i _
    linarith [Nat.sub_one_lt_floor (U i), hU₂ i]
  have hscale : metricProductScale d r P h ≤ P ^ k := by
    rw [← hprod]
    simpa using (prod_le_prod (by intro i _; exact (hUpos i).le)
      (fun i _ ↦ hUP i) : (∏ i, U i) ≤ ∏ _i : Fin k, P)
  have hθk : (k : ℝ) * θ ≤ ε := by
    dsimp [θ]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)]
    nlinarith
  have hcardT' : (T.card : ℝ) ≤ (E.card : ℝ) * (K * P^ε) := by
    rw [card_eq_sum_card_image product T, Nat.cast_sum]
    calc
      _ ≤ ∑ _M ∈ E, K * P ^ ε := by
        apply sum_le_sum
        intro M hM
        have hMbase := (hE M hM).2.1.trans hscale
        refine (hKbound T M (hE M hM).1).trans
          (mul_le_mul_of_nonneg_left ?_ hK.le)
        calc
          (M : ℝ) ^ θ ≤ (P ^ k) ^ θ := Real.rpow_le_rpow (by positivity) hMbase hθ.le
          _ = P ^ ((k : ℝ) * θ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
          _ ≤ P ^ ε := Real.rpow_le_rpow_of_exponent_le hP₁ hθk
      _ = _ := by simp [nsmul_eq_mul]
  have H := hcardT.trans hcardT'
  have H' := (div_le_iff₀ (mul_pos hK (Real.rpow_pos_of_pos hP ε))).mpr H
  rw [div_mul_eq_div_div, div_eq_mul_inv, ← Real.rpow_neg hP.le] at H'
  calc
    _ = (((1 / 2 : ℝ)^k * metricProductScale d r P h) / K) * P ^ (-ε) := by ring
    _ ≤ _ := H'

end Birch
