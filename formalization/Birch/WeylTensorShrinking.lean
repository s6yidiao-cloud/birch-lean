import Birch.WeylNearestShrinking

/-!
# Shrinking the multilinear Weyl frequency count

Fixing all but one shift block gives the symmetric matrix from the terminal
affine polynomial. The single-block estimate may then be applied independently
in each coordinate of the tuple.
-/

open Finset Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

/-- The tuples in the shift boxes whose polarized frequency vector is near
the integer lattice. -/
def weylNearTensorBox {n k : ℕ} (G : IntForm n) (α : ℝ) (H : Fin k → ℝ)
    (δ : ℝ) : Finset (Fin k → Fin n → ℤ) := by
  classical
  exact (Fintype.piFinset fun i => latticeBox n (H i)).filter fun t =>
    ∀ j, nearestIntegerDistance (α * (weylFrequency (List.ofFn t) G j : ℝ)) ≤ δ

theorem mem_weylNearTensorBox {n k : ℕ} {G : IntForm n} {α δ : ℝ} {H : Fin k → ℝ}
    {t : Fin k → Fin n → ℤ} : t ∈ weylNearTensorBox G α H δ ↔
    (∀ i, t i ∈ latticeBox n (H i)) ∧
      (∀ j, nearestIntegerDistance (α * (weylFrequency (List.ofFn t) G j : ℝ)) ≤ δ) := by
  classical
  simp only [weylNearTensorBox, Finset.mem_filter, Fintype.mem_piFinset]

private def weylBlockMatrix {n k : ℕ} (G : IntForm n) (α : ℝ)
    (r : Fin k → Fin n → ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => α * ((weylLastMatrix (List.ofFn r) G i j : ℤ) : ℝ)

private theorem weylBlockMatrix_transpose {n k : ℕ} (G : IntForm n) (α : ℝ)
    (r : Fin k → Fin n → ℤ) :
    (weylBlockMatrix G α r)ᵀ = weylBlockMatrix G α r := by
  ext i j
  have H := congrArg (fun M : Matrix (Fin n) (Fin n) ℤ => M i j)
    (weylLastMatrix_transpose (List.ofFn r) G)
  exact congrArg (fun z : ℤ => α * (z : ℝ)) H

private theorem weylBlockMatrix_frequency {n k : ℕ} (G : IntForm n) (α : ℝ)
    (i : Fin (k+1)) (r : Fin k → Fin n → ℤ) (x : Fin n → ℤ) (j : Fin n) :
    realMatrixFrequency (weylBlockMatrix G α r) x j =
      α * (weylFrequency (List.ofFn (Fin.insertNth i x r : Fin (k+1) → Fin n → ℤ)) G j : ℝ) := by
  rw [weylFrequency_ofFn_insertNth i x r G]
  simp only [realMatrixFrequency, Matrix.mulVec, dotProduct, weylBlockMatrix, Int.cast_sum,
    Int.cast_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem card_weylNearTensorBox_split {n k : ℕ} (G : IntForm n) (α δ : ℝ)
    (H : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    (weylNearTensorBox G α H δ).card =
      ∑ r ∈ Fintype.piFinset (fun j => latticeBox n (H (i.succAbove j))),
        (weylNearInputBox (weylBlockMatrix G α r) (H i) δ).card := by
  classical
  let S := weylNearTensorBox G α H δ
  let B := Fintype.piFinset (fun j => latticeBox n (H (i.succAbove j)))
  let rest (t : Fin (k+1) → Fin n → ℤ) := Fin.removeNth i t
  have hmaps : (S : Set (Fin (k+1) → Fin n → ℤ)).MapsTo rest B := by
    intro t ht
    apply Fintype.mem_piFinset.mpr
    intro j
    exact (mem_weylNearTensorBox.mp ht).1 (i.succAbove j)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro r hr
  let U := weylNearInputBox (weylBlockMatrix G α r) (H i) δ
  let e : (Fin n → ℤ) ↪ (Fin (k+1) → Fin n → ℤ) :=
    ⟨fun x => Fin.insertNth i x r, fun a b h => by
      simpa only [Fin.insertNth_apply_same] using congrFun h i⟩
  have he (x : Fin n → ℤ) : e x ∈ S ↔ x ∈ U := by
    rw [mem_weylNearTensorBox, mem_weylNearInputBox]
    let t : Fin (k+1) → Fin n → ℤ := Fin.insertNth i x r
    change ((∀ j, t j ∈ latticeBox n (H j)) ∧
      (∀ j, nearestIntegerDistance (α * (weylFrequency (List.ofFn t) G j : ℝ)) ≤ δ)) ↔ _
    dsimp only [t]
    rw [Fin.forall_iff_succAbove i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    have hrest : ∀ j, r j ∈ latticeBox n (H (i.succAbove j)) := Fintype.mem_piFinset.mp hr
    rw [mem_latticeBox_iff_abs]
    simp [hrest, weylBlockMatrix_frequency G α i]
  have hfiber : (S.filter fun t => rest t = r) = U.map e := by
    ext t
    constructor
    · intro ht
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht
      have hval : e (t i) = t := by
        change Fin.insertNth i (t i) r = t
        rw [← ht₂]
        change i.insertNth (t i) (i.removeNth t) = t
        rw [Fin.insertNth_removeNth, Function.update_eq_self]
      exact Finset.mem_map.mpr ⟨t i, (he _).mp (hval.symm ▸ ht₁), hval⟩
    · rintro ht
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ht
      exact Finset.mem_filter.mpr ⟨(he _).mpr hx, Fin.removeNth_insertNth _ _ _⟩
  change (S.filter fun t => rest t = r).card = U.card
  rw [hfiber, Finset.card_map]

set_option maxHeartbeats 600000 in
/-- Shrink one block of the multilinear Weyl count and the common residual
tolerance by the same factor. -/
theorem card_weylNearTensorBox_le_shrink_block {n k : ℕ} (G : IntForm n) (α : ℝ)
    (H : Fin (k+1) → ℝ) (i : Fin (k+1)) {δ θ : ℝ}
    (hH : 1 ≤ H i) (hδ : 0 < δ) (hδ' : δ < 1/2) (hHδ : H i*δ ≤ 1)
    (hθ : 0 < θ) (hθ' : θ ≤ 1) :
    ((weylNearTensorBox G α H δ).card : ℝ) ≤
      ((((8*n+1 : ℕ) : ℝ)^(2*n) * 10^n) / ((H i)⁻¹+θ)^n) *
        ((weylNearTensorBox G α (Function.update H i (θ*H i)) (θ*δ)).card : ℝ) := by
  rw [card_weylNearTensorBox_split G α δ H i,
    card_weylNearTensorBox_split G α (θ*δ) _ i]
  have hradii (j : Fin k) : Function.update H i (θ*H i) (i.succAbove j) =
      H (i.succAbove j) := Function.update_of_ne (i.succAbove_ne j) _ _
  simp only [hradii, Function.update_self, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  have h := card_weylNearInputBox_le_shrink (weylBlockMatrix G α r)
    (weylBlockMatrix_transpose G α r) hH hδ hδ' hHδ hθ hθ'
  exact h.trans_eq (by ring)

/-- Shrink every block by the same factor. The tolerance is multiplied by that
factor once for each block. -/
theorem card_weylNearTensorBox_le_shrink_all {n k : ℕ} (G : IntForm n) (α : ℝ)
    {P θ : ℝ} (hP : 4 ≤ P) (hθ : 0 < θ) (hθ' : θ ≤ 1) :
    ((weylNearTensorBox (k := k) G α (fun _ => P) (1/P)).card : ℝ) ≤
      ((((8*n+1 : ℕ) : ℝ)^(2*n) * 10^n) / (P⁻¹+θ)^n)^k *
        ((weylNearTensorBox (k := k) G α (fun _ => θ*P) (θ^k/P)).card : ℝ) := by
  classical
  cases k with
  | zero =>
    have h : (fun _ : Fin 0 => P) = (fun _ : Fin 0 => θ*P) := funext fun i => i.elim0
    simp [h]
  | succ k =>
    let C : ℝ := (((8*n+1 : ℕ) : ℝ)^(2*n) * 10^n) / (P⁻¹+θ)^n
    let R (S : Finset (Fin (k+1))) (i : Fin (k+1)) := if i ∈ S then θ*P else P
    let T (S : Finset (Fin (k+1))) := θ^S.card / P
    let N (S : Finset (Fin (k+1))) := ((weylNearTensorBox G α (R S) (T S)).card : ℝ)
    have hp : 0 < P := by linarith
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hstep (S : Finset (Fin (k+1))) (i : Fin (k+1)) (hi : i ∉ S) :
        N S ≤ C * N (insert i S) := by
      have hRi : R S i = P := ite_eq_right hi
      have hTpos : 0 < T S := div_pos (pow_pos hθ _) hp
      have hTle : T S ≤ 1/P := div_le_div_of_nonneg_right (pow_le_one₀ hθ.le hθ') hp.le
      have hTsmall : T S < 1/2 := hTle.trans_lt ((div_lt_iff₀ hp).mpr (by linarith))
      have hHδ : R S i * T S ≤ 1 := by
        rw [hRi]
        exact (mul_le_mul_of_nonneg_left hTle hp.le).trans_eq (by field_simp)
      have hupdate : Function.update (R S) i (θ * R S i) = R (insert i S) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [R, hi]
        · simp [R, hji]
      have htol : θ*T S = T (insert i S) := by
        dsimp [T]
        rw [Finset.card_insert_of_notMem hi, pow_succ', mul_div_assoc]
      dsimp only [N]
      have hh := card_weylNearTensorBox_le_shrink_block G α (R S) i
        (hRi ▸ (by linarith : 1 ≤ P)) hTpos hTsmall hHδ hθ hθ'
      rwa [hupdate, htol, hRi] at hh
    have hiter (S : Finset (Fin (k+1))) : N ∅ ≤ C^S.card * N S := by
      induction S using Finset.induction_on with
      | empty => simp
      | @insert i S hi ih =>
        refine ih.trans ((mul_le_mul_of_nonneg_left (hstep S i hi) (pow_nonneg hC _)).trans_eq ?_)
        rw [Finset.card_insert_of_notMem hi, pow_succ, mul_assoc]
    have h := hiter (Finset.univ : Finset (Fin (k+1)))
    simpa [N, R, T, C, Fintype.card_fin] using h


end

end Birch
