import Birch.DeligneFiniteField

/-! # From point counts in additive powers to a character-sum estimate -/

open Finset ZMod
open scoped BigOperators

namespace Birch

noncomputable section

/-- Number of tuples whose sum under the given function equals the prescribed
value. -/
def additivePowerFiberCount {α G : Type*} [Fintype α] [AddCommMonoid G]
    (g : α → G) (k : ℕ) (t : G) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Fin k → α => (∑ i, g (x i)) = t).card

private theorem sum_additivePowerFiberCount_mul {α G R : Type*} [Fintype α] [Fintype G]
    [AddCommMonoid G] [Semiring R] (g : α → G) (k : ℕ) (w : G → R) :
    (∑ t, (additivePowerFiberCount g k t : R) * w t) = ∑ x : Fin k → α, w (∑ i, g (x i)) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun x : Fin k → α => ∑ i, g (x i))
    (fun x => w (∑ i, g (x i)))]
  apply Finset.sum_congr rfl
  intro t _
  rw [additivePowerFiberCount, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

/-- Taking powers of a character sum weights the additive fibers of the
corresponding Cartesian power. -/
theorem character_sum_pow_eq_additivePowerFiberCounts {α : Type*} [Fintype α]
    {p : ℕ} [NeZero p] (g : α → ZMod p) (k : ℕ) :
    (∑ x, stdAddChar (g x))^k =
      ∑ t : ZMod p, (additivePowerFiberCount g k t : ℂ) * stdAddChar t := by
  classical
  rw [sum_additivePowerFiberCount_mul, Finset.sum_pow', Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  let h (s : Finset (Fin k)) : Prop :=
    (∏ i ∈ s, stdAddChar (g (x i))) = stdAddChar (∑ i ∈ s, g (x i))
  have hs : ∀ s, h s := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [h]
    | insert i s hi ih =>
      dsimp [h] at ih ⊢
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, AddChar.map_add_eq_mul]
  exact hs Finset.univ

/-- The fiber over zero can be eliminated by subtracting the mean count.
This is useful when the geometric estimate applies to nonzero levels. -/
theorem character_sum_pow_eq_additivePowerFiberErrors {α : Type*} [Fintype α]
    {p : ℕ} [NeZero p] (hp : 1 < p) (g : α → ZMod p) (k : ℕ) :
    (∑ x, stdAddChar (g x))^k =
      ∑ t ∈ Finset.univ.erase (0 : ZMod p),
        ((additivePowerFiberCount g k t : ℂ) - (Fintype.card α : ℂ)^k / p) *
          (stdAddChar t - 1) := by
  classical
  let M := (Fintype.card α : ℂ)^k / p
  let E (t : ZMod p) := (additivePowerFiberCount g k t : ℂ) - M
  have hp₀ : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  let : Fact (1 < p) := ⟨hp⟩
  have hchar : (∑ t : ZMod p, stdAddChar t) = 0 := by
    apply AddChar.sum_eq_zero_of_ne_one
    intro h
    have hu : stdAddChar (1 : ZMod p) = stdAddChar (0 : ZMod p) := by rw [h]; rfl
    exact one_ne_zero (injective_stdAddChar hu)
  have hn : (∑ t : ZMod p, (additivePowerFiberCount g k t : ℂ)) =
      (Fintype.card α : ℂ)^k := by
    simpa [Fintype.card_fun] using sum_additivePowerFiberCount_mul g k (fun _ => (1 : ℂ))
  have hE : ∑ t : ZMod p, E t = 0 := by
    rw [show (∑ t : ZMod p, E t) = (∑ t : ZMod p, (additivePowerFiberCount g k t : ℂ)) -
      ∑ _t : ZMod p, M from Finset.sum_sub_distrib _ _]
    rw [hn]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, M]
    field_simp
    ring
  calc
    (∑ x, stdAddChar (g x))^k =
        ∑ t : ZMod p, (additivePowerFiberCount g k t : ℂ) * stdAddChar t :=
      character_sum_pow_eq_additivePowerFiberCounts g k
    _ = ∑ t : ZMod p, E t * stdAddChar t := by
      simp only [E, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hchar, mul_zero, sub_zero]
    _ = ∑ t : ZMod p, E t * (stdAddChar t - 1) := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hE, sub_zero]
    _ = _ := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : ZMod p))]
      simp [E, M]

/-- Bounds for the nonzero centered fibers control one power of the sum. -/
theorem norm_character_sum_pow_le_of_additivePowerFiberErrors {α : Type*} [Fintype α]
    {p : ℕ} [NeZero p] (hp : 1 < p) (g : α → ZMod p) (k : ℕ) {E₀ : ℝ} (hE₀ : 0 ≤ E₀)
    (hcount : ∀ t : ZMod p, t ≠ 0 →
      |(additivePowerFiberCount g k t : ℝ) - (Fintype.card α : ℝ)^k / p| ≤ E₀) :
    ‖∑ x, stdAddChar (g x)‖^k ≤ 2 * p * E₀ := by
  classical
  let ψ (t : ZMod p) := stdAddChar t
  let E (t : ZMod p) : ℝ := (additivePowerFiberCount g k t : ℝ) - (Fintype.card α : ℝ)^k / p
  let T := Finset.univ.erase (0 : ZMod p)
  rw [← norm_pow, character_sum_pow_eq_additivePowerFiberErrors hp g k]
  change ‖∑ t ∈ T, (↑(additivePowerFiberCount g k t) - (Fintype.card α : ℂ)^k / p) *
    (ψ t - 1)‖ ≤ _
  have hE (t : ZMod p) : (E t : ℂ) =
      (additivePowerFiberCount g k t : ℂ) - (Fintype.card α : ℂ)^k / p := by
    simp [E]
  simp_rw [← hE]
  calc
    _ ≤ ∑ t ∈ T, ‖(E t : ℂ) * (ψ t - 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ T, (E₀) * 2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have ht₀ := (Finset.mem_erase.mp ht).1
      have hψ : ‖ψ t - 1‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans_eq ?_
        norm_num [ψ, stdAddChar_apply]
      exact mul_le_mul (hcount t ht₀) hψ (norm_nonneg _) hE₀
    _ ≤ _ := by
      have hcard : (T.card : ℝ) ≤ p := by
        exact_mod_cast ((Finset.card_le_card (Finset.erase_subset _ _)).trans_eq (by simp) :
          T.card ≤ p)
      rw [Finset.sum_const, nsmul_eq_mul]
      calc
        (T.card : ℝ) * (E₀ * 2) ≤ p * (E₀ * 2) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

/-- An exponential bound for the nonzero fiber errors gives the same
exponential base as a bound for the original character sum. The fiber-error
constant may depend on the field and the original function. -/
theorem norm_character_sum_le_of_additivePowerFiberErrors {α : Type*} [Fintype α]
    {p : ℕ} [NeZero p] (hp : 1 < p) (g : α → ZMod p)
    {L C : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hcount : ∀ k : ℕ, 0 < k → ∀ t : ZMod p, t ≠ 0 →
      |(additivePowerFiberCount g k t : ℝ) - (Fintype.card α : ℝ)^k / p| ≤ C * L^k) :
    ‖∑ x, stdAddChar (g x)‖ ≤ L := by
  have hpow (k : ℕ) (hk : 0 < k) : ‖∑ x, stdAddChar (g x)‖^k ≤ (2 * p * C) * L^k := by
    rw [mul_assoc]
    exact norm_character_sum_pow_le_of_additivePowerFiberErrors hp g k
      (mul_nonneg hC (pow_nonneg hL.le _)) (hcount k hk)
  by_contra! hbig
  let ρ := ‖∑ x, stdAddChar (g x)‖ / L
  have hρ : 1 < ρ := (one_lt_div hL).mpr hbig
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2 * p * C + 1 : ℝ) hρ
  have hk₀ : 0 < k := by
    by_contra! h
    obtain rfl : k = 0 := by omega
    simp only [pow_zero] at hk
    have : 0 ≤ 2 * (p : ℝ) * C := by positivity
    linarith
  have hkle : ρ^k ≤ 2 * p * C := by
    rw [show ρ^k = ‖∑ x, stdAddChar (g x)‖^k / L^k by simp [ρ, div_pow]]
    exact (div_le_iff₀ (pow_pos hL _)).mpr (hpow k hk₀)
  linarith

/-- A point-count input for Deligne's estimate. The same constant must bound
the nonzero level errors in every additive power of the phase. -/
def PrimeExponentialFiberCounts (r : ℕ) (B : ℝ) : Prop :=
  ∀ (l p : ℕ) [Fact p.Prime] [NeZero p], 0 < l → r < p →
    ∀ g : MvPolynomial (Fin l) (ZMod p), g.totalDegree ≤ r →
      PrimeIsolatedLeadingCriticalPoint p r g →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ), 0 < k → ∀ t : ZMod p, t ≠ 0 →
        |(additivePowerFiberCount (fun x => g.eval x) k t : ℝ) - (p : ℝ)^(l*k-1)| ≤
          C * (B^l * (p : ℝ)^((l : ℝ)/2))^k

/-- The fiber count hypothesis with Deligne's sharp exponential base. -/
def PrimeDeligneFiberCounts (r : ℕ) : Prop :=
  PrimeExponentialFiberCounts r ((r : ℝ) - 1)

/-- Uniform point counts in growing dimension imply the prime-field
exponential-sum bound with the same exponential base. -/
theorem primeExponentialSumBound_of_fiberCounts {r : ℕ} {B : ℝ} (hB : 0 < B)
    (hcount : PrimeExponentialFiberCounts r B) : PrimeExponentialSumBound r B := by
  intro l p _ _ hl hp g hg hs
  have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr ((Fact.out : p.Prime).pos)
  obtain ⟨C,hC,hfib⟩ := hcount l p hl hp g hg hs
  unfold primeDeligneSum
  apply norm_character_sum_le_of_additivePowerFiberErrors
    (Fact.out : p.Prime).one_lt (fun x => g.eval x)
    (mul_pos (pow_pos hB _)
      (Real.rpow_pos_of_pos hp₀ _)) hC
  intro k hk t ht
  have hpos : 0 < l*k := Nat.mul_pos hl hk
  have hmean : (Fintype.card (Fin l → ZMod p) : ℝ)^k / p = (p : ℝ)^(l*k-1) := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, ← pow_mul,
      show l*k = (l*k-1)+1 by omega, pow_succ]
    exact mul_div_cancel_right₀ _ hp₀.ne'
  rw [hmean]
  exact hfib k hk t ht

/-- The sharp fiber estimate yields the sharp prime-field bound. -/
theorem primeDeligneEstimate_of_fiberCounts {r : ℕ} (hr : 2 ≤ r)
    (hcount : PrimeDeligneFiberCounts r) : PrimeDeligneEstimate r :=
  primeExponentialSumBound_of_fiberCounts
    (sub_pos.mpr (by exact_mod_cast (show 1 < r by omega))) hcount

end
end Birch
