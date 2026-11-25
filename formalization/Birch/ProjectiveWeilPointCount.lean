module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! # Point-count estimates from graded Frobenius spectra -/

open Finset
open scoped BigOperators

namespace Birch

noncomputable section

/-- The point count of projective N-space over a field of size q. -/
def projectiveSpacePointCount (q N : ℕ) : ℕ :=
  ∑ j ∈ Iic N, q^j

/-- In cohomological degree 2j, projective space has the single Tate
eigenvalue q^j. Its odd cohomological degrees have empty spectrum. -/
def projectiveTateSpectrum (q i : ℕ) : Multiset ℂ :=
  if Even i then { (q : ℂ)^(i/2) } else 0

/-- The alternating trace of the Tate spectrum equals the projective-space point count. -/
theorem alternating_sum_projectiveTateSpectrum (q N : ℕ) :
    (∑ i ∈ Iic (2*N), (-1 : ℂ)^i * (projectiveTateSpectrum q i).sum) =
      (projectiveSpacePointCount q N : ℂ) := by
  classical
  rw [projectiveSpacePointCount, Nat.cast_sum]
  push_cast
  calc
    _ = ∑ i ∈ (Iic (2*N)).filter Even, (q : ℂ)^(i/2) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : Even i
      · simp [projectiveTateSpectrum, hi, hi.neg_one_pow]
      · simp [projectiveTateSpectrum, hi]
    _ = ∑ j ∈ Iic N, (q : ℂ)^j := by
      apply Finset.sum_bij (fun i _ => i/2)
      · intro i hi
        have hle := mem_Iic.mp (mem_filter.mp hi).1
        exact mem_Iic.mpr (by omega)
      · intro i hi j hj h
        obtain ⟨a, ha⟩ := (mem_filter.mp hi).2
        obtain ⟨b, hb⟩ := (mem_filter.mp hj).2
        omega
      · intro j hj
        refine ⟨2*j, ?_, by omega⟩
        have hj' := mem_Iic.mp hj
        exact mem_filter.mpr ⟨mem_Iic.mpr (by omega), ⟨j, by omega⟩⟩
      · intro i _
        rfl

/-- The degree and parity of a smooth hypersurface's classical primitive
Betti formula give an upper bound with base d - 1. -/
theorem primitiveHypersurfaceBetti_le_of_formula {d N b : ℕ} (hd : 2 ≤ d)
    (hb : (d : ℤ)*(b : ℤ) = ((d : ℤ)-1)^(N+2) + (-1 : ℤ)^N*((d : ℤ)-1)) :
    b ≤ (d-1)^(N+1) := by
  let c : ℤ := (d : ℤ)-1
  have hc : 1 ≤ c := by dsimp [c]; exact sub_le_sub_right (by exact_mod_cast hd : (2 : ℤ) ≤ d) 1
  have hsign : (-1 : ℤ)^N ≤ 1 := by
    exact (le_abs_self _).trans_eq (abs_neg_one_pow N)
  have hcb : c ≤ c^(N+1) := le_self_pow₀ hc (Nat.succ_ne_zero _)
  have hd₀ : (0 : ℤ) < d := by exact_mod_cast (show 0 < d by omega)
  have hbound : (d : ℤ)*(b : ℤ) ≤ (d : ℤ)*c^(N+1) := calc
    _ = c^(N+2)+(-1 : ℤ)^N*c := hb
    _ ≤ c^(N+2)+c^(N+1) := by
      apply add_le_add_right
      exact (mul_le_mul_of_nonneg_right hsign (by linarith)).trans (by simpa only [one_mul] using hcb)
    _ = _ := by
      rw [show N+2 = (N+1)+1 by omega, pow_succ]
      dsimp only [c]
      ring
  have hfinal := (mul_le_mul_iff_of_pos_left hd₀).mp hbound
  rw [show c = ((d-1 : ℕ):ℤ) by dsimp [c]; rw [Nat.cast_sub (by omega), Nat.cast_one],
    ← Nat.cast_pow] at hfinal
  exact_mod_cast hfinal

/-- A graded Frobenius spectrum gives the projective hypersurface count
once the ambient Tate spectrum and the primitive rank budget are supplied.
The weight normalization matches AxiomMath Weil. -/
theorem abs_sub_projectiveSpacePointCount_le_of_weilSpectrum
    {q N B count : ℕ} (A : ℕ → Multiset ℂ) (primitive : Multiset ℂ)
    (hcount : (count : ℂ) =
      ∑ i ∈ Iic (2*N), (-1 : ℂ)^i * (A i).sum)
    (hdecomp : ∀ i ≤ 2*N,
      A i = projectiveTateSpectrum q i + if i = N then primitive else 0)
    (hrank : primitive.card ≤ B)
    (hweight : ∀ α ∈ A N, ‖α‖ = Real.sqrt ((q : ℝ)^N)) :
    |(count : ℝ) - (projectiveSpacePointCount q N : ℝ)| ≤ (B : ℝ) * (q : ℝ)^((N : ℝ)/2) := by
  classical
  have hN : N ∈ Iic (2*N) := mem_Iic.mpr (by omega)
  have hsplit : (count : ℂ) = (projectiveSpacePointCount q N : ℂ) +
      (-1 : ℂ)^N * primitive.sum := by
    rw [hcount]
    calc
      _ = ∑ i ∈ Iic (2*N), (-1 : ℂ)^i * (projectiveTateSpectrum q i).sum +
          ∑ i ∈ Iic (2*N), if i = N then (-1 : ℂ)^i * primitive.sum else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdecomp i (mem_Iic.mp hi), Multiset.sum_add, mul_add]
        by_cases hiN : i = N <;> simp [hiN]
      _ = _ := by rw [alternating_sum_projectiveTateSpectrum, Finset.sum_ite_eq' _ _ _, ite_eq_left hN]
  have hterm (α : ℂ) (ha : α ∈ primitive) :
      ‖α‖ = (q : ℝ)^((N : ℝ)/2) := by
    have ha' : α ∈ A N := by
      rw [hdecomp N (mem_Iic.mp hN), ite_eq_left rfl]
      exact Multiset.mem_add.mpr (Or.inr ha)
    rw [hweight α ha', Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg q)]
    congr 1
    ring
  have hsum : ‖primitive.sum‖ ≤ (primitive.card : ℝ) * (q : ℝ)^((N : ℝ)/2) :=
    (norm_multiset_sum_le _).trans (by
      simpa only [nsmul_eq_mul, Multiset.card_map] using Multiset.sum_le_card_nsmul (primitive.map norm)
        ((q : ℝ)^((N : ℝ)/2)) (fun a ha => by
          obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp ha
          exact (hterm α hα).le))
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  rw [hsplit, add_sub_cancel_left, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) (Real.rpow_nonneg (Nat.cast_nonneg q) _))

end
end Birch
