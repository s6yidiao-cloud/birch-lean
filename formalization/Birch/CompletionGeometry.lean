import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Bounded parameter grids and terminal scale estimates

The grid lemma applies to the nonzero resultant polynomial in the bounded
linear-section step. The scale lemma evaluates the savings from the
smooth Fourier weights and the finite-field complete-sum bound.
-/

open MvPolynomial

namespace Birch

/-- Over a field of prime characteristic, a nonzero polynomial of total degree at most `D < p`
has a nonzero evaluation with all coordinates in the integer box `[0,D]`. -/
theorem exists_eval_ne_zero_small_grid_of_charP {K ι : Type*} [Field K] [Finite ι]
    {p D : ℕ} [Fact p.Prime] [CharP K p]
    (hp : D < p) (F : MvPolynomial ι K) (hF : F ≠ 0)
    (hdeg : F.totalDegree ≤ D) :
    ∃ z : ι → ℕ, (∀ i, z i ≤ D) ∧ F.eval (fun i ↦ (z i : K)) ≠ 0 := by
  classical
  have hp₀ : p.Prime := Fact.out
  letI : NeZero p := ⟨hp₀.ne_zero⟩
  let S := (Finset.range (D+1)).image (fun j : ℕ ↦ (j : K))
  have hS : S.card = D+1 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj he
    have hi' : i < p := by
      have hi₁ := Finset.mem_range.mp hi
      omega
    have hj' : j < p := by
      have hj₁ := Finset.mem_range.mp hj
      omega
    have hZ : (i : ZMod p) = (j : ZMod p) := ZMod.castHom_injective K (by
      simpa only [map_natCast] using he)
    simpa only [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] using congrArg ZMod.val hZ
  obtain ⟨m, hm, ht⟩ := Finset.sup_mem_of_nonempty (f := fun m : ι →₀ ℕ ↦
    m.sum fun _ e ↦ e) (support_nonempty.mpr hF)
  have hmdeg : F.totalDegree = m.degree := by simpa [totalDegree, Finsupp.degree_apply, Finsupp.sum] using ht.symm
  have hbox (i : ι) : m i < S.card := by
    have hmi : m i ≤ m.degree := by
      by_cases hi : i ∈ m.support
      · exact Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _) hi
      · rw [Finsupp.notMem_support_iff.mp hi]
        exact Nat.zero_le _
    rw [hS]
    exact Nat.lt_succ_of_le (hmi.trans (hmdeg ▸ hdeg))
  obtain ⟨x, hx, hne⟩ := combinatorial_nullstellensatz_exists_eval_nonzero F m
    (mem_support_iff.mp hm) hmdeg (fun _ ↦ S) hbox
  have hz (i : ι) : ∃ z : ℕ, z ≤ D ∧ (z : K) = x i := by
    obtain ⟨z, hz, hcast⟩ := Finset.mem_image.mp (hx i)
    exact ⟨z, Nat.le_of_lt_succ (Finset.mem_range.mp hz), hcast⟩
  choose z hz hzx using hz
  exact ⟨z, hz, (funext hzx) ▸ hne⟩

/-- Over the prime field, the same integer grid detects a nonzero polynomial. -/
theorem exists_eval_ne_zero_small_grid {ι : Type*} [Finite ι] {p D : ℕ} [Fact p.Prime]
    (hp : D < p) (F : MvPolynomial ι (ZMod p)) (hF : F ≠ 0)
    (hdeg : F.totalDegree ≤ D) :
    ∃ z : ι → ℕ, (∀ i, z i ≤ D) ∧ F.eval (fun i ↦ (z i : ZMod p)) ≠ 0 :=
  exists_eval_ne_zero_small_grid_of_charP hp F hF hdeg

/-- The normalized terminal Fourier and complete-sum bounds give a full
power of `Q⁻¹` in each free variable. -/
theorem terminalScale_bound_of_modulus_range (l : ℕ) {P Q p L : ℝ} (hL : 0 ≤ L)
    (hP : 0 < P) (hQ : 0 < Q) (hQmax : Q ≤ Real.sqrt P)
    (hpL : (P / Q)^2 ≤ p) (hpU : p ≤ L * (P / Q)^2) :
    (1 + p/P)^l * p ^ (-(l : ℝ)/2) ≤ (2 * Real.sqrt L)^l * Q ^ (-(l : ℝ)) := by
  have hpP : P ≤ p := by
    have hsqrt : Q^2 ≤ P := by
      simpa only [Real.sq_sqrt hP.le] using pow_le_pow_left₀ hQ.le hQmax 2
    have h := mul_le_mul_of_nonneg_left hsqrt hP.le
    refine le_trans ?_ hpL
    rw [div_pow, le_div_iff₀ (sq_pos_of_pos hQ), sq]
    simpa only [← sq] using h
  have hp : 0 < p := hP.trans_le hpP
  have hupper : Real.sqrt p ≤ Real.sqrt L * (P/Q) := by
    simpa only [Real.sqrt_mul hL, Real.sqrt_sq
      (div_nonneg hP.le hQ.le)] using Real.sqrt_le_sqrt hpU
  have hrootp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hrat : (1 + p/P) * (Real.sqrt p)⁻¹ ≤ (2 * Real.sqrt L) * Q⁻¹ := by
    have hPfrac : 1 ≤ p/P := (one_le_div hP).mpr hpP
    calc
      _ ≤ (2 * (p/P)) * (Real.sqrt p)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hrootp.le)
      _ = 2 * Real.sqrt p / P := by
        have H := Real.sq_sqrt hp.le
        field_simp
        nlinarith
      _ ≤ (2 * Real.sqrt L) * Q⁻¹ := by
        rw [show 2 * Real.sqrt L * Q⁻¹ = 2 * (Real.sqrt L * (P/Q)) / P by
          field_simp]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hupper (by norm_num)) hP.le
  rw [show p ^ (-(l : ℝ)/2) = ((Real.sqrt p)⁻¹)^l by
    rw [← Real.rpow_neg_one, Real.sqrt_eq_rpow, ← Real.rpow_mul hp.le,
      ← Real.rpow_mul_natCast hp.le]
    congr 1
    ring]
  rw [← mul_pow, Real.rpow_neg_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hrat _

theorem terminalScale_bound (l : ℕ) {P Q p : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hQmax : Q ≤ Real.sqrt P)
    (hpL : (P / Q)^2 ≤ p) (hpU : p ≤ 2 * (P / Q)^2) :
    (1 + p/P)^l * p ^ (-(l : ℝ)/2) ≤ (2 * Real.sqrt 2)^l * Q ^ (-(l : ℝ)) :=
  terminalScale_bound_of_modulus_range l (by norm_num) hP hQ hQmax hpL hpU

end Birch
