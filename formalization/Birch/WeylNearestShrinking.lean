import Birch.WeylDifferencing
import Birch.WeylLinearExponential
import Birch.WeylShrinking

/-!
# Shrinking the nearest-integer frequencies

This is the one-block count in Browning–Prendiville, Lemma 2.2, for the
tolerances below one half used in the Weyl proof.
-/

open Finset Matrix
open scoped Matrix

namespace Birch

noncomputable section

/-- Apply the real matrix to an integral shift. -/
def realMatrixFrequency {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℤ) :
    Fin n → ℝ :=
  A *ᵥ (fun i => (x i : ℝ))

/-- Shifts with all matrix frequencies within a prescribed distance of an
integer. -/
def weylNearInputBox {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (H δ : ℝ) :
    Finset (Fin n → ℤ) := by
  classical
  exact (latticeBox n H).filter (fun x => ∀ i, nearestIntegerDistance (realMatrixFrequency A x i) ≤ δ)

theorem mem_weylNearInputBox {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {H δ : ℝ}
    {x : Fin n → ℤ} : x ∈ weylNearInputBox A H δ ↔
      (∀ i, |(x i : ℝ)| ≤ H) ∧ (∀ i, nearestIntegerDistance (realMatrixFrequency A x i) ≤ δ) := by
  classical
  rw [weylNearInputBox, Finset.mem_filter, mem_latticeBox_iff_abs]

private def weylAliases {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℤ) ↪ WeylPair n where
  toFun x := (x, fun i => round (realMatrixFrequency A x i))
  inj' _ _ h := congrArg Prod.fst h

private theorem norm_normalizedWeylPair_le_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {H δ R : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hR : 0 ≤ R) (x : WeylPair n) :
    ‖normalizedWeylPair A H δ x‖ ≤ R ↔
      (∀ i, |(x.1 i : ℝ)| ≤ H*R) ∧
        (∀ i, |realMatrixFrequency A x.1 i - (x.2 i : ℝ)| ≤ δ*R) := by
  rw [Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg hR, pi_norm_le_iff_of_nonneg hR]
  change (∀ i, ‖(x.1 i : ℝ)/H‖ ≤ R) ∧
    (∀ i, ‖(realMatrixFrequency A x.1 i - (x.2 i : ℝ))/δ‖ ≤ R) ↔ _
  simp only [Real.norm_eq_abs, abs_div, abs_of_pos hH, abs_of_pos hδ,
    div_le_iff₀ hH, div_le_iff₀ hδ, mul_comm R]

private theorem card_weylNearInputBox_le_rough {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) {H δ θ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hδ' : δ < 1/2)
    (hHδ : H*δ ≤ 1) (hθ : 0 < θ) (hθ' : θ ≤ 1) :
    ((weylNearInputBox A H δ).card : ℝ) ≤ ((8*n+1 : ℕ) : ℝ)^(2*n) *
      (1 + 4/θ)^n * ((weylNearInputBox A (θ*H) (θ*δ)).card : ℝ) := by
  let S := (weylNearInputBox A H δ).map (weylAliases A)
  let U := (weylNearInputBox A (θ*H) (θ*δ)).map (weylAliases A)
  have hS (p : WeylPair n) (hp : p ∈ S) : ‖normalizedWeylPair A H δ p‖ ≤ 1 := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
    have h := mem_weylNearInputBox.mp hx
    apply (norm_normalizedWeylPair_le_iff A hH hδ zero_le_one _).mpr
    simpa only [weylAliases, Function.Embedding.coeFn_mk, mul_one, nearestIntegerDistance] using h
  have hU (p q : WeylPair n) (hp : p ∈ S) (hq : q ∈ S)
      (hd : ‖normalizedWeylPair A H δ (p-q)‖ < θ) : p-q ∈ U := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hq
    let z := (weylAliases A x - weylAliases A y).2
    have hb := (norm_normalizedWeylPair_le_iff A hH hδ hθ.le
      (weylAliases A x - weylAliases A y)).mp hd.le
    have ha (i : Fin n) : |realMatrixFrequency A (x-y) i - (z i : ℝ)| ≤ δ*θ := hb.2 i
    have hz (i : Fin n) : round (realMatrixFrequency A (x-y) i) = z i := by
      have hs : |realMatrixFrequency A (x-y) i - (z i : ℝ)| < 1 / 2 :=
        (ha i).trans_lt ((mul_le_of_le_one_right hδ.le hθ').trans_lt hδ')
      obtain ⟨hlo,hhi⟩ := abs_lt.mp hs
      exact round_eq_iff.mpr ⟨by linarith, by linarith⟩
    refine Finset.mem_map.mpr ⟨x-y, mem_weylNearInputBox.mpr ⟨?_, ?_⟩, ?_⟩
    · intro i
      rw [mul_comm]
      exact hb.1 i
    · intro i
      rw [nearestIntegerDistance, hz, mul_comm]
      exact ha i
    · exact Prod.ext rfl (funext hz)
  simpa only [S, U, Finset.card_map] using
    symmetric_frequency_pair_card_le A hA hH hδ hθ hHδ S U hS
      (fun p hp q hq hd => hU p q hp hq hd)

/-- The one-block shrinking inequality in the exact normalization
((H^{-1}+	heta)^{-n}). -/
theorem card_weylNearInputBox_le_shrink {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) {H δ θ : ℝ} (hH : 1 ≤ H) (hδ : 0 < δ) (hδ' : δ < 1/2)
    (hHδ : H*δ ≤ 1) (hθ : 0 < θ) (hθ' : θ ≤ 1) :
    ((weylNearInputBox A H δ).card : ℝ) ≤
      (((8*n+1 : ℕ) : ℝ)^(2*n) * 10^n) *
        ((weylNearInputBox A (θ*H) (θ*δ)).card : ℝ) / (H⁻¹ + θ)^n := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hden : 0 < H⁻¹ + θ := add_pos (inv_pos.mpr hHp) hθ
  have hbase : 1 ≤ (((8*n+1 : ℕ) : ℝ)^(2*n)) := by
    apply one_le_pow₀
    exact_mod_cast (show 1 ≤ 8*n+1 by omega)
  by_cases hb : H⁻¹ ≤ θ
  · have hB : 1 + 4/θ ≤ 10/(H⁻¹+θ) := by
      have h₁ : (1 : ℝ) ≤ 1/θ := (le_div_iff₀ hθ).mpr (by simpa using hθ')
      have h₂ : 5/θ ≤ 10/(H⁻¹+θ) := (div_le_div_iff₀ hθ hden).mpr (by linarith)
      refine le_trans ?_ h₂
      rw [show (5 : ℝ) = 1 + 4 by norm_num, add_div]
      linarith
    calc
      _ ≤ (((8*n+1 : ℕ) : ℝ)^(2*n)) * (1+4/θ)^n *
          ((weylNearInputBox A (θ*H) (θ*δ)).card : ℝ) :=
        card_weylNearInputBox_le_rough A hA hHp hδ hδ' hHδ hθ hθ'
      _ ≤ (((8*n+1 : ℕ) : ℝ)^(2*n)) * (10/(H⁻¹+θ))^n *
          ((weylNearInputBox A (θ*H) (θ*δ)).card : ℝ) := by
        gcongr
      _ = _ := by rw [div_pow]; ring
  · have h₁ : 3*H ≤ 10/(H⁻¹+θ) := by
      have hh : H*θ ≤ 1 := by
        have := mul_le_mul_of_nonneg_left (le_of_not_ge hb) hHp.le
        rwa [mul_inv_cancel₀ hHp.ne'] at this
      apply (le_div_iff₀ hden).mpr
      have hHi : H*H⁻¹ = 1 := mul_inv_cancel₀ hHp.ne'
      nlinarith
    have h0 : (0 : Fin n → ℤ) ∈ weylNearInputBox A (θ*H) (θ*δ) := by
      apply mem_weylNearInputBox.mpr
      constructor
      · intro i; simp [mul_nonneg hθ.le hHp.le]
      · intro i
        have hzero : realMatrixFrequency A 0 = 0 := by
          rw [realMatrixFrequency, show (fun i => ((0 : Fin n → ℤ) i : ℝ)) = 0 by
            funext i; simp, Matrix.mulVec_zero]
        simp [hzero, nearestIntegerDistance, mul_nonneg hθ.le hδ.le]
    have hcard : (1 : ℝ) ≤ ((weylNearInputBox A (θ*H) (θ*δ)).card : ℝ) := by
      exact_mod_cast Finset.one_le_card.mpr ⟨0,h0⟩
    have hsub : weylNearInputBox A H δ ⊆ latticeBox n H := fun _ hx =>
      mem_latticeBox_iff_abs.mpr (mem_weylNearInputBox.mp hx).1
    have hC : ((weylNearInputBox A H δ).card : ℝ) ≤ ((latticeBox n H).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    calc
      _ ≤ ((latticeBox n H).card : ℝ) := hC
      _ ≤ (3*H)^n := (card_latticeBox_between n hH).2
      _ ≤ (10/(H⁻¹+θ))^n := pow_le_pow_left₀ (by positivity) h₁ _
      _ ≤ ((10/(H⁻¹+θ))^n) * (((8*n+1 : ℕ) : ℝ)^(2*n) *
          ((weylNearInputBox A (θ*H) (θ*δ)).card : ℝ)) :=
        le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hbase hcard)
      _ = _ := by rw [div_pow]; ring

end

end Birch
