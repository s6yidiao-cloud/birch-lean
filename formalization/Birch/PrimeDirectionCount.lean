import Birch.GridCounting

/-! # Uniform direction counts from fixed-shape estimates -/

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

open scoped Classical in
/-- The direction bound for one degree and one stratum, at sufficiently
large primes. -/
def LargePrimeDirectionCount (n e j : ℕ) : Prop :=
  ∃ p₀ : ℕ, ∃ C > (0 : ℝ),
    ∀ (p : ℕ) (hp : p.Prime), e < p → p₀ < p →
    ∀ G : IntForm n, G.IsHomogeneous e →
    ∀ s : ℕ, s < j → PrimeGradientDimension p hp G s →
    ∀ H : ℝ, 1 ≤ H → 2 * H ≤ (p : ℝ) →
      (((differencingDirections n H).filter
        (fun u => PrimeGradientDimension p hp (directionalDerivative u G) j)).card : ℝ) ≤
        C * H^(n+s-j)

open scoped Classical in
/-- A finite family of estimates with fixed source dimension supplies a
single threshold and constant for the whole target stratum. -/
theorem largePrimeDirectionCount_of_fixed_s {n e j : ℕ}
    (hfixed : ∀ s : ℕ, s < j → ∃ p₀ : ℕ, ∃ C > (0 : ℝ),
      ∀ (p : ℕ) (hp : p.Prime), e < p → p₀ < p →
      ∀ G : IntForm n, G.IsHomogeneous e → PrimeGradientDimension p hp G s →
      ∀ H : ℝ, 1 ≤ H → 2 * H ≤ (p : ℝ) →
        (((differencingDirections n H).filter
          (fun u => PrimeGradientDimension p hp (directionalDerivative u G) j)).card : ℝ) ≤
          C * H^(n+s-j)) :
    LargePrimeDirectionCount n e j := by
  classical
  choose threshold C hC hcount using fun i : Fin j => hfixed i.val i.isLt
  let B := ∑ i : Fin j, threshold i
  let M := 1 + ∑ i : Fin j, C i
  have hM : 0 < M := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ => (hC i).le)
  refine ⟨B,M,hM,?_⟩
  intro p hp hep hBp G hG s hs hdim H hH hpH
  let i : Fin j := ⟨s,hs⟩
  have hiB : threshold i ≤ B :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (threshold k)) (Finset.mem_univ i)
  have hiM : C i ≤ M := (Finset.single_le_sum (f := C)
    (fun k _ => (hC k).le) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  exact (hcount i p hp hep (hiB.trans_lt hBp) G hG hdim H hH hpH).trans
    (mul_le_mul_of_nonneg_right hiM (by positivity))

private theorem card_filter_differencingDirections_le_trivial {n : ℕ} {H : ℝ}
    (hH : 1 ≤ H) (C : (Fin n → ℤ) → Prop) [DecidablePred C] :
    (((differencingDirections n H).filter C).card : ℝ) ≤ (3 * H)^n := by
  let I := Finset.Icc (-⌊H⌋) ⌊H⌋
  have hsub : differencingDirections n H ⊆ Fintype.piFinset (fun _ : Fin n => I) := by
    intro u hu
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi := abs_le.mp (abs_differencingDirection_lt (zero_lt_one.trans_le hH) hu i).le
    exact Finset.mem_Icc.mpr ⟨neg_le.mp (Int.le_floor.mpr (by exact_mod_cast (neg_le.mp hi.1))),
      Int.le_floor.mpr hi.2⟩
  have hc := (Finset.card_filter_le _ C).trans (Finset.card_le_card hsub)
  rw [Fintype.card_piFinset_const] at hc
  refine (show _ ≤ (I.card : ℝ)^n by exact_mod_cast hc).trans ?_
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_int_coordinateBox_le hH) n

/-- Finitely many fixed shapes supply one uniform constant. For each shape
the primes below its threshold have uniformly bounded direction boxes. -/
theorem primeDirectionBound_of_largePrimeCounts {n d : ℕ}
    (hlarge : ∀ e j : ℕ, 2 < e → e ≤ d → j ≤ n → LargePrimeDirectionCount n e j) :
    PrimeDirectionBound n d := by
  classical
  let F := (Finset.Icc 3 d).product (Finset.range (n+1))
  have hshape (i : F) : LargePrimeDirectionCount n i.val.1 i.val.2 := by
    obtain ⟨he,hj⟩ := Finset.mem_product.mp i.prop
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp he
    exact hlarge _ _ (by omega) hu (by have := Finset.mem_range.mp hj; omega)
  choose B C hC hcount using hshape
  let W (i : F) : ℝ := (3 * ((B i : ℝ) + 1))^n
  have hW (i : F) : 0 ≤ W i := by dsimp [W]; positivity
  let K : ℝ := 1 + 3^n + ∑ i : F, (C i + W i)
  have hsum : 0 ≤ ∑ i : F, (C i + W i) :=
    Finset.sum_nonneg fun i _ => add_nonneg (hC i).le (hW i)
  have hK₃ : (3 : ℝ)^n ≤ K :=
    (le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right hsum)
  have hK : 0 < K := (pow_pos (by norm_num) _).trans_le hK₃
  have hKshape (i : F) : C i + W i ≤ K := by
    refine (Finset.single_le_sum (f := fun i => C i + W i)
      (fun j _ => add_nonneg (hC j).le (hW j)) (Finset.mem_univ i)).trans ?_
    dsimp [K]
    exact le_add_of_nonneg_left (by positivity)
  refine ⟨K,hK,?_⟩
  intro p hp e he hed hdp G hG s j _ hj hs H hH hpH
  let D (u : Fin n → ℤ) := PrimeGradientDimension p hp (directionalDerivative u G) j
  have htriv := card_filter_differencingDirections_le_trivial hH D
  rw [← Nat.cast_sub ((Nat.sub_le j s).trans hj), Real.rpow_natCast]
  by_cases hsj : s < j
  · rw [show n-(j-s) = n+s-j by omega]
    let i : F := ⟨(e,j), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hed⟩, Finset.mem_range.mpr (by omega)⟩⟩
    have hKC : C i ≤ K := (le_add_of_nonneg_right (hW i)).trans (hKshape i)
    have hKW : W i ≤ K := (le_add_of_nonneg_left (hC i).le).trans (hKshape i)
    by_cases hpB : B i < p
    · exact (hcount i p hp (hed.trans_lt hdp) hpB G hG s hsj hs H hH hpH).trans
        (mul_le_mul_of_nonneg_right hKC (by positivity))
    · have hpB' : (p : ℝ) ≤ (B i : ℝ) := by exact_mod_cast (not_lt.mp hpB)
      have hHB : H ≤ (B i : ℝ) + 1 := by linarith
      have hpow : (3 * H)^n ≤ W i := by
        apply pow_le_pow_left₀ (by positivity)
        exact mul_le_mul_of_nonneg_left hHB (by norm_num)
      exact htriv.trans (hpow.trans (hKW.trans (le_mul_of_one_le_right hK.le (one_le_pow₀ hH))))
  · rw [Nat.sub_eq_zero_of_le (not_lt.mp hsj), Nat.sub_zero]
    rw [mul_pow] at htriv
    exact htriv.trans (mul_le_mul_of_nonneg_right hK₃ (by positivity))

end
end Birch
