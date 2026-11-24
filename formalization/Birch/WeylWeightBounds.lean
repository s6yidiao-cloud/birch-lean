import Birch.WeylDifferencing
import Birch.NormalizedDifference
import Birch.WeylPartialSummation
import Mathlib.Data.Nat.Choose.Sum

/-! # Uniform seminorms of ordinarily differenced weights -/

open Finset Set
open scoped BigOperators ContDiff

namespace Birch

noncomputable section

private lemma order_le_smooth (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private theorem weight_step_smooth_bound {n N : ℕ} {C P : ℝ} {w : (Fin n → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) (hC : 0 ≤ C)
    (hB : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j w x‖ ≤ C) (u : Fin n → ℤ) :
    ContDiff ℝ ∞ (differencedWeight w P 1 u) ∧
      ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (differencedWeight w P 1 u) x‖ ≤ (2 : ℝ)^N*C*C := by
  let a : Fin n → ℝ := fun i => (1 : ℝ)*(u i : ℝ)/P
  let f : (Fin n → ℝ) → ℝ := fun y => w (y+a)
  have hf : ContDiff ℝ ∞ f := hw.comp (contDiff_id.add contDiff_const)
  have hfb (j : ℕ) (hj : j ≤ N) (x : Fin n → ℝ) : ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    unfold f
    rw [iteratedFDeriv_comp_add_right]
    exact hB j hj (x+a)
  have he : differencedWeight w P 1 u = fun x => f x * w x := by
    funext x
    simp only [differencedWeight, f, a, Int.cast_one]
    rfl
  rw [he]
  refine ⟨hf.mul hw, fun j hj x => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hf hw x (order_le_smooth j)).trans ?_
  calc
    _ ≤ ∑ i ∈ range (j+1), (j.choose i : ℝ)*C*C := by
      apply sum_le_sum
      intro i hi
      have hb₁ := hfb i (by have := mem_range.mp hi; omega) x
      have hb₂ := hB (j-i) (by omega) x
      apply mul_le_mul (mul_le_mul_of_nonneg_left hb₁ (by positivity)) hb₂ (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*C*C := by
      rw [← sum_mul, ← sum_mul]
      have H : (∑ i ∈ range (j+1), (j.choose i : ℝ)) = (2 : ℝ)^j := by exact_mod_cast Nat.sum_range_choose j
      rw [H]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hj) hC) hC

private def iteratedWeightBound (N : ℕ) : ℕ → ℝ → ℝ
  | 0, C => C
  | k+1, C => iteratedWeightBound N k ((2 : ℝ)^N*C*C)

private theorem iteratedWeightBound_pos (N k : ℕ) {C : ℝ} (hC : 0 < C) :
    0 < iteratedWeightBound N k C := by
  induction k generalizing C with
  | zero => exact hC
  | succ k ih => exact ih (by positivity)

private theorem weight_list_smooth_bound {n N : ℕ} (P : ℝ)
    (hs : List (Fin n → ℤ)) {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j w x‖ ≤ C) :
    ContDiff ℝ ∞ (weylDifferencedWeight hs w P) ∧
      ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (weylDifferencedWeight hs w P) x‖ ≤
        iteratedWeightBound N hs.length C := by
  induction hs generalizing w C with
  | nil => exact ⟨hw,hB⟩
  | cons u hs ih =>
    obtain ⟨hws, hbs⟩ := weight_step_smooth_bound (P := P) hw hC hB u
    exact ih hws (by positivity) hbs

/-- A fixed number of ordinary differences preserves uniform global derivative
bounds for smooth weights supported in the source cube. -/
theorem uniform_weylDifferencedWeight_smooth {n : ℕ} {w : (Fin n → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) (k N : ℕ) :
    ∃ C > 0, ∀ (P : ℝ) (hs : List (Fin n → ℤ)), hs.length = k →
      ContDiff ℝ ∞ (weylDifferencedWeight hs w P) ∧
        ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j (weylDifferencedWeight hs w P) x‖ ≤ C := by
  obtain ⟨C,hC,hB⟩ := exists_derivativesBoundedOnBall hw N 1
  have hglobal (j : ℕ) (hj : j ≤ N) (x : Fin n → ℝ) : ‖iteratedFDeriv ℝ j w x‖ ≤ C := by
    by_cases hx : ‖x‖ ≤ 1
    · exact hB j hj x hx
    · have hzero : iteratedFDeriv ℝ j w x = 0 := by
        by_contra hn
        have hxs : x ∈ tsupport w := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := w) j hn
        apply hx
        have ht : tsupport w ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 := by
          apply closure_minimal _ Metric.isClosed_closedBall
          intro y hy
          rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
          intro i
          rw [Real.norm_eq_abs]
          exact (hwbox y hy i).le
        simpa only [Metric.mem_closedBall, dist_zero_right] using ht hxs
      rw [hzero,norm_zero]
      exact hC.le
  refine ⟨iteratedWeightBound N k C, iteratedWeightBound_pos N k hC, fun P hs hlen => ?_⟩
  simpa only [hlen] using weight_list_smooth_bound P hs hw hC.le hglobal

/-- The linear phase bound for every terminal weight in a fixed-length
ordinary differencing chain, with a common constant. -/
theorem uniform_weylLinear_weight_bound {n : ℕ} {w : (Fin n → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) (k : ℕ) :
    ∃ C > 0, ∀ (P : ℝ), 0 < P → ∀ (hs : List (Fin n → ℤ)), hs.length = k →
      ∀ (t : Fin n → ℝ) (c : ℝ),
        ‖∑ x ∈ latticeBox n P, (weylDifferencedWeight hs w P (scaledPoint P x) : ℂ) *
            phase (c + ∑ i, (x i : ℝ)*t i)‖ ≤
          C * ∏ i, linearPhaseBound (weylIntervalLength P) (t i) := by
  obtain ⟨D,hD,hweight⟩ := uniform_weylDifferencedWeight_smooth hw hwbox k n
  refine ⟨D*(3 : ℝ)^n, by positivity, fun P hP hs hlen t c => ?_⟩
  obtain ⟨hsmooth, hbound⟩ := hweight P hs hlen
  exact norm_weighted_affine_phase_box_le hP _ hsmooth hD.le hbound t c

end
end Birch
