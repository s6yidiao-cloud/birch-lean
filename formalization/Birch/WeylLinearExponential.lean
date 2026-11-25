/-
SPDX-License-Identifier: Apache-2.0

The nearest-integer geometric-sum argument is adapted from OpenAI's
SquareDifference/CircleDistance.lean and SquareDifference/PhaseBounds.lean at
4eaee87548250b2682affda7d05d947c05554bae.
https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Combinatorics/SquareDifference

The license text is in LICENSES/Apache-2.0.txt.
-/

import Birch.MajorArcLatticePoisson
import Birch.RealOscillationDecay
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Linear exponential sums on integer intervals -/

open Finset Complex

namespace Birch

noncomputable section

/-- The distance to the nearest integer, with either representative usable at
half-integers. -/
def nearestIntegerDistance (t : ℝ) : ℝ := |t - (round t : ℝ)|

theorem nearestIntegerDistance_nonneg (t : ℝ) : 0 ≤ nearestIntegerDistance t := abs_nonneg _

theorem nearestIntegerDistance_le_half (t : ℝ) : nearestIntegerDistance t ≤ 1 / 2 :=
  abs_sub_round t

theorem nearestIntegerDistance_le_abs_sub_int (t : ℝ) (a : ℤ) :
    nearestIntegerDistance t ≤ |t - (a : ℝ)| :=
  round_le t a

theorem nearestIntegerDistance_le_iff (t r : ℝ) :
    nearestIntegerDistance t ≤ r ↔ ∃ a : ℤ, |t - (a : ℝ)| ≤ r :=
  ⟨fun h => ⟨round t, h⟩, fun ⟨a, ha⟩ => (nearestIntegerDistance_le_abs_sub_int t a).trans ha⟩

private theorem phase_at_integer (a : ℤ) : phase a = 1 := by
  unfold phase
  rw [mul_comm]
  exact Complex.exp_int_mul_two_pi_mul_I a

private theorem phase_nat_mul (t : ℝ) (m : ℕ) : phase ((m : ℝ) * t) = phase t ^ m := by
  induction m with
  | zero => simp [phase]
  | succ m hm =>
    rw [Nat.cast_succ, add_mul, one_mul, phase_add, hm, pow_succ]

/-- The denominator in the geometric sum is bounded below by four times the
distance to the nearest integer. -/
theorem four_mul_nearestIntegerDistance_le_norm_phase_sub_one (t : ℝ) :
    4 * nearestIntegerDistance t ≤ ‖phase t - 1‖ := by
  let u : ℝ := t - (round t : ℝ)
  have hu : |u| ≤ 1 / 2 := nearestIntegerDistance_le_half t
  have hsin := Real.mul_abs_le_abs_sin (x := Real.pi * u)
    (by rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos])
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hmul : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by field_simp
  rw [hmul] at hsin
  have hphase : phase t = phase u := by
    rw [show t = u + (round t : ℝ) by dsimp [u]; ring, phase_add, phase_at_integer, mul_one]
  have hexp : phase u = Complex.exp (Complex.I * ((2 * Real.pi * u : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [hphase, hexp, Complex.norm_exp_I_mul_ofReal_sub_one,
    show 2 * Real.pi * u / 2 = Real.pi * u by ring, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change 4 * |u| ≤ _
  linarith

/-- The elementary linear-sum bound with its resonant case included. -/
def linearPhaseBound (L t : ℝ) : ℝ :=
  if nearestIntegerDistance t = 0 then L else min L (1 / (2 * nearestIntegerDistance t))

theorem linearPhaseBound_nonneg {L : ℝ} (hL : 0 ≤ L) (t : ℝ) : 0 ≤ linearPhaseBound L t := by
  unfold linearPhaseBound
  split_ifs
  · exact hL
  · exact le_min hL (by positivity [nearestIntegerDistance_nonneg t])

theorem linearPhaseBound_le (L t : ℝ) : linearPhaseBound L t ≤ L := by
  unfold linearPhaseBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The norm of a linear exponential sum of length N is bounded both by N
and, at a nonresonant frequency, by the reciprocal of twice the distance to
its nearest integer. -/
theorem norm_linear_phase_sum_le (t : ℝ) (N : ℕ) :
    ‖∑ m ∈ Finset.range N, phase ((m : ℝ) * t)‖ ≤ linearPhaseBound N t := by
  have htrivial : ‖∑ m ∈ Finset.range N, phase ((m : ℝ) * t)‖ ≤ N := calc
    _ ≤ ∑ m ∈ Finset.range N, ‖phase ((m : ℝ) * t)‖ := norm_sum_le _ _
    _ = N := by simp [norm_phase]
  unfold linearPhaseBound
  split_ifs with ht
  · exact htrivial
  · refine le_min htrivial ?_
    have hpos := lt_of_le_of_ne (nearestIntegerDistance_nonneg t) (Ne.symm ht)
    have hdenom := four_mul_nearestIntegerDistance_le_norm_phase_sub_one t
    have hphase : phase t ≠ 1 := by
      intro h
      rw [h, sub_self, norm_zero] at hdenom
      linarith
    simp_rw [phase_nat_mul]
    rw [geom_sum_eq hphase, norm_div]
    have hnum : ‖phase t ^ N - 1‖ ≤ 2 := calc
      _ ≤ ‖phase t ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_phase]; norm_num
    calc
      _ ≤ 2 / (4 * nearestIntegerDistance t) :=
        div_le_div₀ (by positivity) hnum (by positivity) hdenom
      _ = 1 / (2 * nearestIntegerDistance t) := by ring

/-- The same bound holds on a translated finite interval and for any constant
phase. -/
theorem norm_affine_phase_range_le (t c : ℝ) (a : ℤ) (N : ℕ) :
    ‖∑ m ∈ Finset.range N, phase (c + ((a : ℝ) + (m : ℝ)) * t)‖ ≤ linearPhaseBound N t := by
  have hsplit (m : ℕ) : c + ((a : ℝ) + (m : ℝ)) * t =
      (c + (a : ℝ) * t) + (m : ℝ) * t := by ring
  simp_rw [hsplit, phase_add (c + (a : ℝ)*t)]
  rw [← Finset.mul_sum, norm_mul, norm_phase, one_mul]
  exact norm_linear_phase_sum_le t N

/-- The finite partial sums appearing in partial summation, over any half-open
interval of integers. -/
theorem norm_affine_phase_Ico_le (t c : ℝ) (a b : ℤ) :
    ‖∑ m ∈ Finset.Ico a b, phase (c + (m : ℝ) * t)‖ ≤
      linearPhaseBound (Finset.Ico a b).card t := by
  rw [Int.card_Ico, Int.Ico_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
    Int.cast_add, Int.cast_natCast]
  exact norm_affine_phase_range_le t c a (b-a).toNat

/-- Factor the linear exponential sum on a Cartesian box and apply the
one-coordinate bound to each interval. -/
theorem norm_affine_phase_box_le {n : ℕ} (t : Fin n → ℝ) (c : ℝ)
    (a b : Fin n → ℤ) :
    ‖∑ x ∈ Fintype.piFinset (fun i => Finset.Ico (a i) (b i)),
      phase (c + ∑ i, (x i : ℝ) * t i)‖ ≤
      ∏ i, linearPhaseBound (Finset.Ico (a i) (b i)).card (t i) := by
  classical
  have hfactor (x : Fin n → ℤ) (S : Finset (Fin n)) :
      phase (∑ i ∈ S, (x i : ℝ) * t i) = ∏ i ∈ S, phase ((x i : ℝ) * t i) := by
    induction S using Finset.induction_on with
    | empty => simp [phase]
    | insert i S hi ih =>
      rw [Finset.sum_insert hi, phase_add, ih, Finset.prod_insert hi]
  simp_rw [phase_add c, hfactor]
  rw [← Finset.mul_sum, ← Finset.prod_univ_sum (fun i : Fin n => Finset.Ico (a i) (b i))
    (fun i (m : ℤ) => phase ((m : ℝ) * t i)), norm_mul, norm_phase, one_mul, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
    by simpa only [zero_add] using norm_affine_phase_Ico_le (t i) 0 (a i) (b i))

end

end Birch
