import Mathlib.Tactic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators

/-! Finite count definitions needed by the extracted Wooley proof.
These declarations are extracted from S. McColm's Lean monorepo,
revision 6a90ee91cdb8a4037189c1076595bd3846c96c16 (MIT No Attribution).
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

section
variable {β Γ : Type*} [AddCommGroup Γ] [DecidableEq Γ]

/-- Extracted from `FordZeroRepresentation.lean`. -/
def fordRepresentationCount (B : Finset β) (F : β → Γ) (w : Γ) : ℕ :=
  ((B ×ˢ B).filter fun xy => F xy.1 - F xy.2 = w).card

end

/-- Extracted from `FordVinogradovIntegral.lean`. -/
abbrev FordVinogradovTuple (s Q : ℕ) := Fin s → Fin Q

/-- The vector `(∑ᵢ xᵢ, ..., ∑ᵢ xᵢ^k)` attached to a source tuple. -/
def fordVinogradovPowerVector (s k Q : ℕ) (x : FordVinogradovTuple s Q) :
    Fin k → ℤ :=
  fun j => ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)

/-- Ford's shifted solution count `J_{s,k}(P; h)` with `Q = floor P`. -/
def fordVinogradovShiftedCountNat
    (s k Q : ℕ) (h : Fin k → ℤ) : ℕ :=
  fordRepresentationCount (Finset.univ : Finset (FordVinogradovTuple s Q))
    (fordVinogradovPowerVector s k Q) h

/-- The combinatorial form (1.4) of Ford's complete Vinogradov mean value. -/
def fordVinogradovMomentNat (s k Q : ℕ) : ℕ :=
  fordVinogradovShiftedCountNat s k Q 0

/-- Extracted from `FordVinogradovIntegral.lean`. -/
def fordVinogradovKappa (k : ℕ) : ℕ := k * (k + 1) / 2

/-- Extracted from `FordVinogradovIntegral.lean`. -/
theorem fordVinogradovPowerVector_bounds
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) (j : Fin k) :
    (s : ℤ) ≤ fordVinogradovPowerVector s k Q x j ∧
      fordVinogradovPowerVector s k Q x j ≤
        (s : ℤ) * (Q : ℤ) ^ ((j : ℕ) + 1) := by
  let d : ℕ := (j : ℕ) + 1
  have htermLower (i : Fin s) :
      (1 : ℤ) ≤ ((x i : ℕ) + 1 : ℤ) ^ d := by
    apply one_le_pow₀
    omega
  have htermUpper (i : Fin s) :
      ((x i : ℕ) + 1 : ℤ) ^ d ≤ (Q : ℤ) ^ d := by
    have hbase : (x i : ℕ) + 1 ≤ Q := Nat.succ_le_iff.mpr (x i).isLt
    have hpow : ((x i : ℕ) + 1) ^ d ≤ Q ^ d := Nat.pow_le_pow_left hbase d
    exact_mod_cast hpow
  constructor
  · change (s : ℤ) ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d
    calc
      (s : ℤ) = ∑ _i : Fin s, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermLower i
  · change (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
      (s : ℤ) * (Q : ℤ) ^ d
    calc
      (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
          ∑ _i : Fin s, (Q : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermUpper i
      _ = (s : ℤ) * (Q : ℤ) ^ d := by simp

/-- Extracted from `FordVinogradovIntegral.lean`. -/
theorem ford_pow_mul_conj_pow (z : ℂ) (s : ℕ) :
    z ^ s * conj z ^ s = ((‖z‖ : ℝ) : ℂ) ^ (2 * s) := by
  rw [← mul_pow, Complex.mul_conj']
  rw [← pow_mul]

/-- Extracted from `FordKDiagonal.lean`. -/
abbrev FordPowerSolution (s k Q : ℕ) :=
  {xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q //
    fordVinogradovPowerVector s k Q xy.1 =
      fordVinogradovPowerVector s k Q xy.2}

theorem card_fordPowerSolution (s k Q : ℕ) :
    Nat.card (FordPowerSolution s k Q) =
      fordVinogradovMomentNat s k Q := by
  classical
  rw [Nat.card_eq_fintype_card]
  unfold FordPowerSolution fordVinogradovMomentNat
    fordVinogradovShiftedCountNat fordRepresentationCount
  rw [Fintype.card_subtype]
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, sub_eq_zero]

/-- Extracted from `FordLemma34Parameters.lean`. -/
def fordLambda34 (s k : ℕ) (delta : ℝ) : ℝ :=
  2 * (s : ℝ) - ((k : ℝ) * (k + 1)) / 2 + delta

/-- Extracted from `FordLemma34Terminal.lean`. -/
def FordVinogradovMomentBound
    (s k : ℕ) (C delta : ℝ) : Prop :=
  ∀ Q : ℕ, 1 ≤ Q →
    (fordVinogradovMomentNat s k Q : ℝ) ≤
      C * (Q : ℝ) ^ fordLambda34 s k delta

/-- Extracted from `VinogradovCriticalReduction.lean`. -/
def VinogradovCriticalEndpointTheorem : Prop :=
  ∀ (l : ℕ) (epsilon : ℝ), 1 ≤ l → 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧
      FordVinogradovMomentBound (fordVinogradovKappa l) l C epsilon

/-- Extracted from `VinogradovCriticalReduction.lean`. -/
theorem fordVinogradovKappa_cast (l : ℕ) :
    (fordVinogradovKappa l : ℝ) =
      (l : ℝ) * ((l : ℝ) + 1) / 2 := by
  unfold fordVinogradovKappa
  rw [Nat.cast_div
    (even_iff_two_dvd.mp (Nat.even_mul_succ_self l))
    (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  rfl

end

end GafniTao
