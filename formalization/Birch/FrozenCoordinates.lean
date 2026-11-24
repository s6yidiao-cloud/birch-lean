import Birch.LatticeCosets

/-!
# Summing over frozen terminal coordinates

A bound for each slice gives the same power of the frequency parameter after
summing over the bounded-index quotient and the remaining integer coordinates.
-/

open Matrix
open scoped Matrix BigOperators

namespace Birch

noncomputable section

/-- Membership in the closed integer box is the pointwise real absolute-value bound. -/
theorem mem_latticeBox_iff_abs {n : ℕ} {P : ℝ} {x : Fin n → ℤ} :
    x ∈ latticeBox n P ↔ ∀ i, |(x i : ℝ)| ≤ P := by
  simp only [latticeBox, Fintype.mem_piFinset, Finset.mem_Icc, neg_le, Int.le_floor,
    Int.cast_neg, abs_le]

/-- A fixed inverse-coordinate bound, expressed by the integral adjugate. -/
def latticeFrameRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  1 + ((A.det.natAbs : ℝ) + 1) * ∑ i, ∑ j, |(A.adjugate i j : ℝ)|

theorem one_le_latticeFrameRadius {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    1 ≤ latticeFrameRadius A := by
  unfold latticeFrameRadius
  exact le_add_of_nonneg_right (by positivity)

theorem latticeFrame_coords_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : A.det ≠ 0) {P : ℝ} (hP : 1 ≤ P) {b x z : Fin n → ℤ}
    (hb : ∀ i, 0 ≤ b i ∧ b i < (A.det.natAbs : ℤ)) (hx : x = b + A *ᵥ z)
    (hxbox : x ∈ latticeBox n P) :
    ∀ i, |(z i : ℝ)| ≤ latticeFrameRadius A * P := by
  have hP₀ : 0 ≤ P := zero_le_one.trans hP
  have hcoord (j : Fin n) : |((x - b) j : ℝ)| ≤ ((A.det.natAbs : ℝ)+1)*P := by
    have hb₀ : (0 : ℝ) ≤ b j := by exact_mod_cast (hb j).1
    have hb₁ : (b j : ℝ) ≤ (A.det.natAbs : ℝ) := by
      simpa only [Int.cast_natCast] using
        (Int.cast_le.mpr (hb j).2.le : (b j : ℝ) ≤ ((A.det.natAbs : ℤ) : ℝ))
    rw [Pi.sub_apply, Int.cast_sub]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hb₀]
    calc
      _ ≤ P + A.det.natAbs := add_le_add (mem_latticeBox_iff_abs.mp hxbox j) hb₁
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hP (Nat.cast_nonneg (α := ℝ) A.det.natAbs)]
  have hdz : A.adjugate *ᵥ (x - b) = A.det • z := by
    rw [hx, add_comm b _, add_sub_cancel_right, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  have hdet : 1 ≤ |(A.det : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (Int.add_one_le_iff.mpr (abs_pos.mpr hA))
  intro i
  have hdz_i : (A.det : ℝ) * (z i : ℝ) =
      ∑ j, (A.adjugate i j : ℝ) * ((x - b) j : ℝ) := by
    have h := congrArg (fun v : Fin n → ℤ => (v i : ℝ)) hdz
    simpa only [mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Pi.smul_apply, smul_eq_mul] using h.symm
  let B : ℝ := ((A.det.natAbs : ℝ)+1)*P
  calc
    _ ≤ |(A.det : ℝ) * (z i : ℝ)| := by
      rw [abs_mul]
      exact le_mul_of_one_le_left (abs_nonneg _) hdet
    _ ≤ ∑ j, |(A.adjugate i j : ℝ) * ((x - b) j : ℝ)| := by
      rw [hdz_i]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(A.adjugate i j : ℝ)| * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hcoord j) (abs_nonneg _)
    _ = (∑ j, |(A.adjugate i j : ℝ)|) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, |(A.adjugate i j : ℝ)|) * B := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [B]; positivity)
      exact Finset.single_le_sum (f := fun i : Fin n => ∑ j, |(A.adjugate i j : ℝ)|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := by unfold latticeFrameRadius; dsimp [B]; nlinarith

private theorem card_frame_latticeBox_le (s : ℕ) {P C : ℝ} (hP : 1 ≤ P) (hC : 1 ≤ C) :
    ((latticeBox s (C * P)).card : ℝ) ≤ ((2*C+1)*P)^s := by
  have hCP : 0 ≤ C*P := mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hP)
  have hf : 0 ≤ ⌊C*P⌋ := Int.floor_nonneg.mpr hCP
  have hf' : -⌊C*P⌋ ≤ ⌊C*P⌋ := by omega
  simp only [latticeBox, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_pow]
  apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ _
  have hc := Int.card_Icc_of_le (-⌊C*P⌋) ⌊C*P⌋ (by omega)
  have hcZ : ((Finset.Icc (-⌊C*P⌋) ⌊C*P⌋).card : ℤ) =
      2 * ⌊C*P⌋ + 1 := hc.trans (by omega)
  have hc' : ((Finset.Icc (-⌊C*P⌋) ⌊C*P⌋).card : ℝ) =
      2 * (⌊C*P⌋ : ℤ) + 1 := by exact_mod_cast hcZ
  rw [hc']
  linarith [Int.floor_le (C * P)]

/-- Exact reindexing into the quotient representatives and frozen coordinates.
The free coordinates remain an unrestricted, finitely supported sum. -/
theorem latticeBox_sum_eq_sum_slices {l s : ℕ}
    (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) (hA : A.det ≠ 0)
    {R : Finset (Fin (l+s) → ℤ)} (e : (↑R × (Fin (l+s) → ℤ)) ≃ (Fin (l+s) → ℤ))
    (he : ∀ (b : R) z, e (b,z) = b.val + A *ᵥ z)
    (hb : ∀ b : R, ∀ i, 0 ≤ b.val i ∧ b.val i < (A.det.natAbs : ℤ))
    {P : ℝ} (hP : 1 ≤ P) (f : (Fin (l+s) → ℤ) → ℂ)
    (hf : ∀ x ∉ latticeBox (l+s) P, f x = 0) :
    ∑ x ∈ latticeBox (l+s) P, f x =
      ∑ b : R, ∑ v ∈ latticeBox s (latticeFrameRadius A * P),
        ∑' u : Fin l → ℤ, f (b.val + A *ᵥ Fin.append u v) := by
  classical
  let C := latticeFrameRadius A * P
  let e₀ := (Equiv.prodComm (Fin s → ℤ) (Fin l → ℤ)).trans (Fin.appendEquiv l s)
  let e₁ := (Equiv.prodCongr (Equiv.refl ↑R) e₀).trans e
  have happ (b : R) (v : Fin s → ℤ) (u : Fin l → ℤ) :
      e₁ (b, v, u) = b.val + A *ᵥ Fin.append u v := by
    exact he _ _
  have hs : Summable f := summable_of_ne_finset_zero hf
  have hs₁ : Summable (fun p => f (e₁ p)) := e₁.summable_iff.mpr hs
  have hs₂ (b : R) : Summable (fun p : (Fin s → ℤ) × (Fin l → ℤ) => f (e₁ (b,p))) :=
    hs₁.prod_factor b
  have ht : (∑' x, f x) = ∑ x ∈ latticeBox (l+s) P, f x := tsum_eq_sum hf
  rw [← ht, ← e₁.tsum_eq f, hs₁.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro b _
  rw [(hs₂ b).tsum_prod]
  simp_rw [happ]
  apply tsum_eq_sum
  intro v hv
  have hzero (u : Fin l → ℤ) : f (b.val + A *ᵥ Fin.append u v) = 0 := by
    by_contra hfu
    have hx : b.val + A *ᵥ Fin.append u v ∈ latticeBox (l+s) P := by
      by_contra hnot
      exact hfu (hf _ hnot)
    apply hv
    apply mem_latticeBox_iff_abs.mpr
    intro i
    simpa only [Fin.append_right] using latticeFrame_coords_le A hA hP (hb b) rfl hx (Fin.natAdd l i)
  simp_rw [hzero, tsum_zero]

/-- Combining the slice estimates costs exactly the (s) powers of (P)
from the frozen coordinates, plus a constant that depends on the fixed matrix. -/
theorem normalized_latticeBox_bound_of_slices {l s : ℕ}
    (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) (hA : A.det ≠ 0) :
    ∃ (R : Finset (Fin (l+s) → ℤ)) (C : ℝ), 0 < C ∧
      (∀ b : R, ∀ i, 0 ≤ b.val i ∧ b.val i < (A.det.natAbs : ℤ)) ∧
      ∀ {P Q D : ℝ}, 1 ≤ P → 0 < Q → 0 ≤ D →
        ∀ f : (Fin (l+s) → ℤ) → ℂ,
          (∀ x ∉ latticeBox (l+s) P, f x = 0) →
          (∀ (b : R) (v : Fin s → ℤ), v ∈ latticeBox s (latticeFrameRadius A * P) →
            ‖∑' u : Fin l → ℤ, f (b.val + A *ᵥ Fin.append u v)‖ / P^l ≤
              D * Q^(-(l : ℝ))) →
          ‖∑ x ∈ latticeBox (l+s) P, f x‖ / P^(l+s) ≤ C * D * Q^(-(l : ℝ)) := by
  classical
  obtain ⟨R, e, hR, hb, he⟩ := exists_bounded_lattice_cosets A hA
  let B := 2 * latticeFrameRadius A + 1
  let C : ℝ := (A.det.natAbs : ℝ)^(l+s) * B^s
  have hB : 0 < B := by dsimp [B]; linarith [one_le_latticeFrameRadius A]
  have hdet : (0 : ℝ) < A.det.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  refine ⟨R, C, mul_pos (pow_pos hdet _) (pow_pos hB _), hb, ?_⟩
  intro P Q D hP hQ hD f hf hs
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hQ₀ : 0 ≤ Q^(-(l : ℝ)) := Real.rpow_nonneg hQ.le _
  have hconst (b : R) (v : Fin s → ℤ) (hv : v ∈ latticeBox s (latticeFrameRadius A * P)) :
      ‖∑' u : Fin l → ℤ, f (b.val + A *ᵥ Fin.append u v)‖ ≤ D * Q^(-(l : ℝ)) * P^l :=
    (div_le_iff₀ (pow_pos hP₀ _)).mp (hs b v hv)
  have hR' : (R.card : ℝ) ≤ (A.det.natAbs : ℝ)^(l+s) := by exact_mod_cast hR
  have hcnt : ((latticeBox s (latticeFrameRadius A * P)).card : ℝ) ≤ B^s * P^s := by
    simpa only [mul_pow] using card_frame_latticeBox_le s hP (one_le_latticeFrameRadius A)
  apply (div_le_iff₀ (pow_pos hP₀ _)).mpr
  rw [latticeBox_sum_eq_sum_slices A hA e he hb hP f hf]
  calc
    _ ≤ ∑ b : R, ∑ v ∈ latticeBox s (latticeFrameRadius A * P),
        ‖∑' u : Fin l → ℤ, f (b.val + A *ᵥ Fin.append u v)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ (_b : R), ∑ _v ∈ latticeBox s (latticeFrameRadius A * P),
        D * Q^(-(l : ℝ)) * P^l :=
      Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun v hv => hconst b v hv
    _ = (R.card : ℝ) * (latticeBox s (latticeFrameRadius A * P)).card *
        (D * Q^(-(l : ℝ)) * P^l) := by simp [mul_assoc, nsmul_eq_mul]
    _ ≤ ((A.det.natAbs : ℝ)^(l+s) * (B^s*P^s)) * (D * Q^(-(l : ℝ)) * P^l) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hR' hcnt (by positivity) (by positivity)) (by positivity)
    _ = _ := by dsimp [C]; rw [pow_add]; ring

/-- A single constant applies to all nonsingular frames in a fixed finite family. -/
theorem uniform_latticeBox_bound_of_slices {l s : ℕ}
    (frames : Finset (Matrix (Fin (l+s)) (Fin (l+s)) ℤ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ A ∈ frames, A.det ≠ 0 →
      ∃ R : Finset (Fin (l+s) → ℤ),
        (∀ b : R, ∀ i, 0 ≤ b.val i ∧ b.val i < (A.det.natAbs : ℤ)) ∧
        ∀ {P Q D : ℝ}, 1 ≤ P → 0 < Q → 0 ≤ D →
          ∀ f : (Fin (l+s) → ℤ) → ℂ,
            (∀ x ∉ latticeBox (l+s) P, f x = 0) →
            (∀ (b : R) (v : Fin s → ℤ), v ∈ latticeBox s (latticeFrameRadius A * P) →
              ‖∑' u : Fin l → ℤ, f (b.val + A *ᵥ Fin.append u v)‖ / P^l ≤
                D * Q^(-(l : ℝ))) →
            ‖∑ x ∈ latticeBox (l+s) P, f x‖ / P^(l+s) ≤ C * D * Q^(-(l : ℝ)) := by
  classical
  let nonsingular := frames.filter fun A => A.det ≠ 0
  have hA (A : nonsingular) : A.val.det ≠ 0 := (Finset.mem_filter.mp A.prop).2
  choose R D₀ hD₀ hR hbound using fun A : nonsingular =>
    normalized_latticeBox_bound_of_slices A.val (hA A)
  let C := 1 + ∑ A : nonsingular, D₀ A
  refine ⟨C, add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun A _ => (hD₀ A).le), ?_⟩
  intro A hframes hdet
  let a : nonsingular := ⟨A, Finset.mem_filter.mpr ⟨hframes,hdet⟩⟩
  refine ⟨R a, hR a, ?_⟩
  intro P Q D hP hQ hD f hf hs
  have hle : D₀ a ≤ C := (Finset.single_le_sum (f := D₀)
    (fun A _ => (hD₀ A).le) (Finset.mem_univ a)).trans (le_add_of_nonneg_left zero_le_one)
  exact (hbound a hP hQ hD f hf hs).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hD)
      (Real.rpow_nonneg hQ.le _))

end
end Birch
