import Birch.FrozenCoordinates
import Birch.LatticeSummable
import Birch.DifferencingChain
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Affine coordinates on terminal slices -/

open Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

private def realFrameMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ((Int.castRingHom ℝ).mapMatrix A).mulVecLin.toContinuousLinearMap

private theorem realFrameMap_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (x : Fin n → ℝ) :
    realFrameMap A x = (Int.castRingHom ℝ).mapMatrix A *ᵥ x := rfl

private def appendFreeMap (l s : ℕ) : (Fin l → ℝ) →L[ℝ] (Fin (l+s) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Fin.append x 0
      map_add' := by
        intro x y
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
      map_smul' := by
        intro a x
        funext i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp }

/-- The continuous linear map given by the free columns of the frame. -/
def freeFrameMap {l s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) :
    (Fin l → ℝ) →L[ℝ] (Fin (l+s) → ℝ) :=
  (realFrameMap A).comp (appendFreeMap l s)

private theorem freeFrameMap_apply {l s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ)
    (x : Fin l → ℝ) : freeFrameMap A x = realFrameMap A (Fin.append x 0) := rfl

/-- The representative and the frozen columns contribute only an affine offset. -/
def frozenFrameOffset {l s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ)
    (c : Fin (l+s) → ℤ) (v : Fin s → ℤ) (P : ℝ) : Fin (l+s) → ℝ :=
  P⁻¹ • latticeVector (c + A *ᵥ Fin.append (0 : Fin l → ℤ) v)

private theorem latticeVector_add {n : ℕ} (x y : Fin n → ℤ) :
    latticeVector (x + y) = latticeVector x + latticeVector y := by
  ext i
  simp [latticeVector]

private theorem latticeVector_append {l s : ℕ} (x : Fin l → ℤ) (v : Fin s → ℤ) :
    latticeVector (Fin.append x v) = Fin.append (latticeVector x) (latticeVector v) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [latticeVector]

private theorem latticeVector_zero {n : ℕ} : latticeVector (0 : Fin n → ℤ) = 0 := by
  ext i
  simp [latticeVector]

private theorem latticeVector_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (z : Fin n → ℤ) : latticeVector (A *ᵥ z) = realFrameMap A (latticeVector z) := by
  ext i
  simp [latticeVector, realFrameMap_apply, mulVec, dotProduct, RingHom.mapMatrix_apply]

/-- The normalized real lattice point equals the affine map of the normalized
free coordinate. -/
theorem frozenFrameOffset_add_freeFrameMap {l s : ℕ}
    (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) (c : Fin (l+s) → ℤ) (v : Fin s → ℤ)
    (P : ℝ) (u : Fin l → ℤ) :
    frozenFrameOffset A c v P + freeFrameMap A (P⁻¹ • latticeVector u) =
      P⁻¹ • latticeVector (c + A *ᵥ Fin.append u v) := by
  have happ : Fin.append (latticeVector u) (latticeVector v) =
      Fin.append (0 : Fin l → ℝ) (latticeVector v) +
        Fin.append (latticeVector u) (0 : Fin s → ℝ) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [map_smul, freeFrameMap_apply, frozenFrameOffset, ← smul_add]
  simp only [latticeVector_add, latticeVector_mulVec, latticeVector_append, latticeVector_zero,
    happ, map_add, add_assoc]

private def frameOffsetBound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  (A.det.natAbs : ℝ) + ‖realFrameMap A‖ * latticeFrameRadius A

private theorem frameOffsetBound_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    0 ≤ frameOffsetBound A := by
  unfold frameOffsetBound
  exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (norm_nonneg _)
    (zero_le_one.trans (one_le_latticeFrameRadius A)))

private theorem norm_frozenFrameOffset_le {l s : ℕ}
    (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) {P : ℝ} (hP : 1 ≤ P) (c : Fin (l+s) → ℤ)
    (hc : ∀ i, 0 ≤ c i ∧ c i < (A.det.natAbs : ℤ)) (v : Fin s → ℤ)
    (hv : v ∈ latticeBox s (latticeFrameRadius A * P)) :
    ‖frozenFrameOffset A c v P‖ ≤ frameOffsetBound A := by
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hR : 0 ≤ latticeFrameRadius A := zero_le_one.trans (one_le_latticeFrameRadius A)
  have hc' : ‖latticeVector c‖ ≤ (A.det.natAbs : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
    intro i
    have hi : (0 : ℝ) ≤ (c i : ℝ) := by exact_mod_cast (hc i).1
    simp only [latticeVector, Real.norm_eq_abs, abs_of_nonneg hi]
    simpa only [Int.cast_natCast] using
      (Int.cast_le.mpr (hc i).2.le : (c i : ℝ) ≤ (↑(A.det.natAbs : ℤ) : ℝ))
  have hv' : ∀ i, |(v i : ℝ)| ≤ latticeFrameRadius A * P := by
    simpa only [latticeBox, Fintype.mem_piFinset, Finset.mem_Icc, neg_le, Int.le_floor,
      Int.cast_neg, abs_le] using hv
  have happ : ‖Fin.append (0 : Fin l → ℝ) (latticeVector v)‖ ≤ latticeFrameRadius A * P := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hR hp.le)).mpr
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using mul_nonneg hR hp.le
    · simpa [latticeVector, Real.norm_eq_abs] using hv' j
  rw [frozenFrameOffset, latticeVector_add, latticeVector_mulVec, latticeVector_append,
    latticeVector_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), ← div_eq_inv_mul]
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ‖latticeVector c‖ + ‖realFrameMap A (Fin.append (0 : Fin l → ℝ) (latticeVector v))‖ :=
      norm_add_le _ _
    _ ≤ (A.det.natAbs : ℝ) + ‖realFrameMap A‖ * (latticeFrameRadius A * P) :=
      add_le_add hc' (((realFrameMap A).le_opNorm _).trans (mul_le_mul_of_nonneg_left happ (norm_nonneg _)))
    _ ≤ frameOffsetBound A * P := by
      unfold frameOffsetBound
      rw [add_mul, mul_assoc]
      exact add_le_add (le_mul_of_one_le_right (Nat.cast_nonneg _) hP) le_rfl

private theorem norm_le_adjugate_freeFrameMap {l s : ℕ}
    (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) (hA : A.det ≠ 0) (x : Fin l → ℝ) :
    ‖x‖ ≤ ‖realFrameMap A.adjugate‖ * ‖freeFrameMap A x‖ := by
  have hdet : 1 ≤ |(A.det : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast (Int.add_one_le_iff.mpr (abs_pos.mpr hA))
  have hleft : realFrameMap A.adjugate (freeFrameMap A x) =
      (A.det : ℝ) • Fin.append x (0 : Fin s → ℝ) := by
    rw [freeFrameMap_apply, realFrameMap_apply, realFrameMap_apply, mulVec_mulVec,
      RingHom.map_adjugate, adjugate_mul, smul_mulVec, one_mulVec, ← RingHom.map_det]
    rfl
  calc
    ‖x‖ ≤ ‖Fin.append x (0 : Fin s → ℝ)‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      simpa using (norm_le_pi_norm (Fin.append x (0 : Fin s → ℝ)) (Fin.castAdd s i))
    _ ≤ ‖(A.det : ℝ) • Fin.append x (0 : Fin s → ℝ)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact le_mul_of_one_le_left (norm_nonneg _) hdet
    _ ≤ _ := hleft ▸ (realFrameMap A.adjugate).le_opNorm (freeFrameMap A x)

/-- All affine slices from the finite family have uniformly bounded linear
parts, offsets, and real supports for cube-supported weights. -/
theorem uniform_affineFrame_bounds {l s : ℕ}
    (frames : Finset (Matrix (Fin (l+s)) (Fin (l+s)) ℤ)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ A ∈ frames, A.det ≠ 0 →
      ‖freeFrameMap A‖ ≤ R ∧
        ∀ {P : ℝ}, 1 ≤ P → ∀ (c : Fin (l+s) → ℤ),
          (∀ i, 0 ≤ c i ∧ c i < (A.det.natAbs : ℤ)) → ∀ (v : Fin s → ℤ),
          v ∈ latticeBox s (latticeFrameRadius A * P) →
          ‖frozenFrameOffset A c v P‖ ≤ R ∧
            ∀ (w : (Fin (l+s) → ℝ) → ℝ), CubeSupported w →
              ∀ x, w (frozenFrameOffset A c v P + freeFrameMap A x) ≠ 0 → ‖x‖ ≤ R := by
  classical
  let cost (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) : ℝ :=
    ‖freeFrameMap A‖ + frameOffsetBound A +
      ‖realFrameMap A.adjugate‖ * (1 + frameOffsetBound A)
  have hcost (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) : 0 ≤ cost A := by
    have := frameOffsetBound_nonneg A
    dsimp [cost]
    positivity
  let R : ℝ := 1 + ∑ A ∈ frames, cost A
  refine ⟨R, le_add_of_nonneg_right (Finset.sum_nonneg fun A _ => hcost A), ?_⟩
  intro A hframes hA
  have hAR : cost A ≤ R :=
    (Finset.single_le_sum (fun B _ => hcost B) hframes).trans (le_add_of_nonneg_left zero_le_one)
  have hB := frameOffsetBound_nonneg A
  have h1B : 0 ≤ 1 + frameOffsetBound A := by positivity
  have hAdj : 0 ≤ ‖realFrameMap A.adjugate‖ * (1 + frameOffsetBound A) := by positivity
  have hL' : ‖freeFrameMap A‖ ≤ cost A := le_add_of_nonneg_right (add_nonneg hB hAdj) |>.trans_eq
    (add_assoc _ _ _).symm
  have hb' : frameOffsetBound A ≤ cost A :=
    (le_add_of_nonneg_left (norm_nonneg (freeFrameMap A))).trans (le_add_of_nonneg_right hAdj)
  refine ⟨hL'.trans hAR, ?_⟩
  intro P hP c hc v hv
  let b := frozenFrameOffset A c v P
  have hb : ‖b‖ ≤ frameOffsetBound A := norm_frozenFrameOffset_le A hP c hc v hv
  refine ⟨(hb.trans hb').trans hAR, ?_⟩
  intro w hw x hx
  have hball : ‖b + freeFrameMap A x‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
      simpa [Real.norm_eq_abs] using (hw _ hx i).le
  have hLx : ‖freeFrameMap A x‖ ≤ 1 + frameOffsetBound A := by
    calc
      _ = ‖b + freeFrameMap A x - b‖ := by rw [add_comm b, add_sub_cancel_right]
      _ ≤ ‖b + freeFrameMap A x‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hball hb
  calc
    ‖x‖ ≤ ‖realFrameMap A.adjugate‖ * ‖freeFrameMap A x‖ :=
      norm_le_adjugate_freeFrameMap A hA x
    _ ≤ ‖realFrameMap A.adjugate‖ * (1 + frameOffsetBound A) :=
      mul_le_mul_of_nonneg_left hLx (norm_nonneg _)
    _ ≤ cost A := le_add_of_nonneg_left (add_nonneg (norm_nonneg _) hB)
    _ ≤ R := hAR

end
end Birch
