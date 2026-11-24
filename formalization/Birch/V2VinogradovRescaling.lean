import Birch.V2VinogradovCongruences
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Sum

/-!
# Translation and dilation of power-sum congruences

Translating an entire tuple preserves a common-modulus system of power sums.
After dividing out the scale of a residue class, the equation of degree `j`
has modulus `p ^ (B - h * j)`. The equivalence includes the equations
whose modulus becomes one.
-/

namespace Birch

open scoped BigOperators

private theorem powerSum_modEq_add {ι : Type*} [Fintype ι]
    {m : ℤ} {k : ℕ} {x y : ι → ℤ}
    (h : ∀ j ≤ k, (∑ i, x i ^ j) ≡ (∑ i, y i ^ j) [ZMOD m])
    (z : ℤ) {j : ℕ} (hj : j ≤ k) :
    (∑ i, (x i + z) ^ j) ≡ (∑ i, (y i + z) ^ j) [ZMOD m] := by
  let c (l : ℕ) : ℤ := z ^ (j - l) * j.choose l
  have expand (u : ι → ℤ) :
      (∑ i, (u i + z) ^ j) =
        ∑ l ∈ Finset.range (j + 1), (∑ i, u i ^ l) * c l := by
    simp_rw [add_pow, mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [c, Finset.sum_mul]
  rw [expand x, expand y]
  apply Int.ModEq.sum
  intro l hl
  exact (h l ((Nat.le_of_lt_succ (Finset.mem_range.1 hl)).trans hj)).mul_right _

/-- A simultaneous translation preserves the first `k` power-sum
congruences with a common modulus. -/
theorem powerSum_modEq_add_iff {ι : Type*} [Fintype ι]
    {m : ℤ} {k : ℕ} (x y : ι → ℤ) (z : ℤ) :
    (∀ j ≤ k, (∑ i, (x i + z) ^ j) ≡ (∑ i, (y i + z) ^ j) [ZMOD m]) ↔
      ∀ j ≤ k, (∑ i, x i ^ j) ≡ (∑ i, y i ^ j) [ZMOD m] := by
  constructor
  · intro h j hj
    simpa only [add_neg_cancel_right] using powerSum_modEq_add h (-z) hj
  · intro h j hj
    exact powerSum_modEq_add h z hj

private theorem primePower_mul_modEq_iff {p : ℤ} (hp : p ≠ 0) (a B : ℕ)
    (x y : ℤ) : p ^ a * x ≡ p ^ a * y [ZMOD p ^ B] ↔
      x ≡ y [ZMOD p ^ (B - a)] := by
  by_cases h : a ≤ B
  · rw [show p ^ B = p ^ a * p ^ (B - a) by rw [← pow_add, Nat.add_sub_of_le h]]
    exact Int.ModEq.mul_left_cancel_iff' (pow_ne_zero _ hp)
  · have hBa : B ≤ a := by omega
    rw [Nat.sub_eq_zero_of_le hBa, pow_zero]
    have hd : p ^ B ∣ p ^ a := pow_dvd_pow p hBa
    constructor
    · intro _
      simp [Int.modEq_iff_dvd]
    · intro _
      rw [Int.modEq_iff_dvd, ← mul_sub]
      exact hd.trans (dvd_mul_right _ _)

/-- A power-sum system on one residue class modulo `p ^ h` is exactly an
anisotropic system on the rescaled coordinates. -/
theorem powerSum_modEq_rescale_iff {ι : Type*} [Fintype ι]
    {p : ℤ} (hp : p ≠ 0) (h B k : ℕ) (x y : ι → ℤ) (z : ℤ) :
    (∀ j ≤ k, (∑ i, (p ^ h * x i + z) ^ j) ≡
      (∑ i, (p ^ h * y i + z) ^ j) [ZMOD p ^ B]) ↔
      ∀ j ≤ k, (∑ i, x i ^ j) ≡ (∑ i, y i ^ j) [ZMOD p ^ (B - h * j)] := by
  rw [powerSum_modEq_add_iff]
  simp_rw [mul_pow, ← pow_mul, ← Finset.mul_sum, primePower_mul_modEq_iff hp]

/-- In a mixed power-sum system, translating by the center of the second
block lets its degree-`j` terms vanish modulo `p ^ min B (b * j)`. -/
theorem powerSum_modEq_of_mixed_class {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p η : ℤ} {B b k : ℕ} (x y : ι → ℤ) (u v : κ → ℤ)
    (h : ∀ j ≤ k, ((∑ i, x i ^ j) + ∑ i, (p ^ b * u i + η) ^ j) ≡
      ((∑ i, y i ^ j) + ∑ i, (p ^ b * v i + η) ^ j) [ZMOD p ^ B]) :
    ∀ j ≤ k, (∑ i, (x i - η) ^ j) ≡ (∑ i, (y i - η) ^ j)
      [ZMOD p ^ min B (b * j)] := by
  let X : ι ⊕ κ → ℤ := Sum.elim x (fun i => p ^ b * u i + η)
  let Y : ι ⊕ κ → ℤ := Sum.elim y (fun i => p ^ b * v i + η)
  have hXY (j : ℕ) (hj : j ≤ k) :
      (∑ i, X i ^ j) ≡ (∑ i, Y i ^ j) [ZMOD p ^ B] := by
    simpa only [Fintype.sum_sum_type, X, Y, Sum.elim_inl, Sum.elim_inr] using h j hj
  intro j hj
  have hs := (powerSum_modEq_add hXY (-η) hj).of_dvd
    (pow_dvd_pow p (min_le_left B (b * j)))
  simp only [Fintype.sum_sum_type, X, Y, Sum.elim_inl, Sum.elim_inr,
    ← sub_eq_add_neg, add_sub_cancel_right] at hs
  apply Int.ModEq.add_right_cancel _ hs
  apply Int.ModEq.sum
  intro i _
  rw [Int.modEq_iff_dvd, mul_pow, mul_pow, ← pow_mul, ← mul_sub]
  exact (pow_dvd_pow p (min_le_right B (b * j))).trans (dvd_mul_right _ _)

end Birch
