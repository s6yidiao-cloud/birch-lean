import Birch.V2CoverVinogradov
import Birch.V2VinogradovRescaling

/-! # From consecutive natural intervals to signed Vinogradov boxes -/

namespace Birch

open Finset

noncomputable section

private theorem powerSums_translate {s e : ℕ} {x y : Fin s → ℤ}
    (h : tuplePowerSums e x = tuplePowerSums e y) (a : ℤ) :
    tuplePowerSums e (fun i => x i + a) = tuplePowerSums e (fun i => y i + a) := by
  have heq : ∀ j ≤ e, (∑ i, x i ^ j) ≡ (∑ i, y i ^ j) [ZMOD 0] := by
    intro j hj
    apply Int.modEq_zero_iff.2
    by_cases hz : j = 0
    · simp [hz]
    let i : Fin e := ⟨j - 1, by omega⟩
    have hi : i.val + 1 = j := by dsimp [i]; omega
    have h' := congrFun h i
    change (∑ l, x l ^ (i.val + 1)) = (∑ l, y l ^ (i.val + 1)) at h'
    simpa only [hi] using h'
  funext j
  exact Int.modEq_zero_iff.1 ((powerSum_modEq_add_iff x y a).2 heq _ j.isLt)

/-- Translating the signed interval embeds its power-sum diagonal into the
diagonal for the consecutive points `1,…,2⌊L⌋+1`. -/
theorem signedPowerSumDiagonal_le_initialInterval {s e : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    differenceMultiplicity (integerTupleBox s L) (tuplePowerSums e) 0 ≤
      differenceMultiplicity (univ : Finset (Fin s → Fin (2 * ⌊L⌋₊ + 1)))
        (fun t => tuplePowerSums e fun i => ((t i).val : ℤ) + 1) 0 := by
  let Q := 2 * ⌊L⌋₊ + 1
  let U := integerTupleBox s L
  let f (t : Fin s → Fin Q) := tuplePowerSums e (fun i => ((t i).val : ℤ) + 1)
  let A := (U ×ˢ U).filter fun z => tuplePowerSums e z.1 - tuplePowerSums e z.2 = 0
  let B := ((univ : Finset (Fin s → Fin Q)) ×ˢ univ).filter fun z => f z.1 - f z.2 = 0
  have hfloor : (⌊L⌋₊ : ℤ) = ⌊L⌋ := Int.natCast_floor_eq_floor (by linarith)
  have hQ : (Q : ℤ) = 2 * ⌊L⌋ + 1 := by
    simp only [Q, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hfloor]
  let lift (x : Fin s → ℤ) (hx : x ∈ U) (i : Fin s) : Fin Q :=
    ⟨(x i + ⌊L⌋).toNat, by
      obtain ⟨hl, hu⟩ := mem_Icc.1 (Fintype.mem_piFinset.1 hx i)
      exact (Int.toNat_lt (by omega)).2 (by omega)⟩
  have hlift (x : Fin s → ℤ) (hx : x ∈ U) (i : Fin s) :
      ((lift x hx i).val : ℤ) = x i + ⌊L⌋ := by
    have hl := (mem_Icc.1 (Fintype.mem_piFinset.1 hx i)).1
    exact Int.toNat_of_nonneg (by omega)
  let go (z : A) : B :=
    let hz := mem_filter.1 z.prop
    let hxy := mem_product.1 hz.1
    ⟨(lift z.val.1 hxy.1, lift z.val.2 hxy.2), mem_filter.2 ⟨by simp, by
      apply sub_eq_zero.2
      simpa only [f, hlift, add_assoc] using
        powerSums_translate (sub_eq_zero.1 hz.2) (⌊L⌋ + 1)⟩⟩
  have hgo : Function.Injective go := by
    intro x y hxy
    have hx := mem_product.1 (mem_filter.1 x.prop).1
    have hy := mem_product.1 (mem_filter.1 y.prop).1
    have hxy' := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have h := congrArg (fun t : (Fin s → Fin Q) × (Fin s → Fin Q) => ((t.1 i).val : ℤ)) hxy'
      change ((lift x.val.1 hx.1 i).val : ℤ) = ((lift y.val.1 hy.1 i).val : ℤ) at h
      simp only [hlift, add_left_inj] at h
      exact h
    · funext i
      have h := congrArg (fun t : (Fin s → Fin Q) × (Fin s → Fin Q) => ((t.2 i).val : ℤ)) hxy'
      change ((lift x.val.2 hx.2 i).val : ℤ) = ((lift y.val.2 hy.2 i).val : ℤ) at h
      simp only [hlift, add_left_inj] at h
      exact h
  change A.card ≤ B.card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective go hgo

/-- A critical bound on consecutive positive integers implies the signed
real-length version needed for the cover theorem. -/
theorem criticalVinogradovEstimate_of_initialInterval {e : ℕ}
    (hcount : ∀ ε > 0, ∃ K > 0, ∀ Q : ℕ, 1 ≤ Q →
      (differenceMultiplicity (univ : Finset (Fin (vinogradovCriticalIndex e) → Fin Q))
        (fun t => tuplePowerSums e fun i => ((t i).val : ℤ) + 1) 0 : ℝ) ≤
        K * (Q : ℝ) ^ ((vinogradovCriticalIndex e : ℝ) + ε)) :
    CriticalVinogradovEstimate e := by
  intro ε hε
  obtain ⟨K, hK, h⟩ := hcount ε hε
  let a : ℝ := (vinogradovCriticalIndex e : ℝ) + ε
  have ha : 0 ≤ a := by dsimp [a]; positivity
  refine ⟨K * (3 : ℝ) ^ a, by positivity, fun L hL => ?_⟩
  let Q := 2 * ⌊L⌋₊ + 1
  have hQ : (Q : ℝ) ≤ 3 * L := by
    have hfloor : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
    dsimp only [Q]
    push_cast
    linarith
  calc
    _ ≤ (differenceMultiplicity (univ : Finset (Fin (vinogradovCriticalIndex e) → Fin Q))
      (fun t => tuplePowerSums e fun i => ((t i).val : ℤ) + 1) 0 : ℝ) := by
        exact_mod_cast signedPowerSumDiagonal_le_initialInterval hL
    _ ≤ K * (Q : ℝ) ^ a := h Q (by dsimp [Q]; omega)
    _ ≤ K * (3 * L) ^ a :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hQ ha) hK.le
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by linarith), ← mul_assoc]

end

end Birch
