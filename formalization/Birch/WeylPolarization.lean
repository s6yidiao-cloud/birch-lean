import Birch.DilatedDifference
import Birch.HessianCoordinateRing
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The terminal affine polynomial in Weyl differencing

The polynomial identity and the symmetric linear map used in Browning–
Prendiville, Lemma 3.3, equations (3.4) and (3.7), are checked over the integers.
The coefficient bound is uniform in the shift boxes.
-/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

variable {n : ℕ}

/-- Ordinary differences, applied from left to right along the list of shifts. -/
def weylDifference (hs : List (Fin n → ℤ)) (G : IntForm n) : IntForm n :=
  hs.foldl (fun g h => dilatedDifference 1 h g) G

/-- The successive directional derivatives of the leading form. -/
def weylDirectionalDerivative (hs : List (Fin n → ℤ)) (G : IntForm n) : IntForm n :=
  hs.foldl (fun g h => directionalDerivative h g) G

@[simp] theorem weylDifference_nil (G : IntForm n) : weylDifference [] G = G := rfl
@[simp] theorem weylDifference_cons (h : Fin n → ℤ) (hs : List (Fin n → ℤ)) (G : IntForm n) :
    weylDifference (h :: hs) G = weylDifference hs (dilatedDifference 1 h G) := rfl
@[simp] theorem weylDirectionalDerivative_nil (G : IntForm n) :
    weylDirectionalDerivative [] G = G := rfl
@[simp] theorem weylDirectionalDerivative_cons (h : Fin n → ℤ) (hs : List (Fin n → ℤ)) (G : IntForm n) :
    weylDirectionalDerivative (h :: hs) G = weylDirectionalDerivative hs (directionalDerivative h G) := rfl

theorem weylDirectionalDerivative_append (hs ts : List (Fin n → ℤ)) (G : IntForm n) :
    weylDirectionalDerivative (hs ++ ts) G =
      weylDirectionalDerivative ts (weylDirectionalDerivative hs G) :=
  List.foldl_append

/-- After each ordinary difference the degree drops by at least one. -/
theorem weylDifference_totalDegree_le (hs : List (Fin n → ℤ)) (G : IntForm n) :
    (weylDifference hs G).totalDegree ≤ G.totalDegree - hs.length := by
  induction hs generalizing G with
  | nil => simp
  | cons h hs ih =>
    exact (ih _).trans (by
      have hd := dilatedDifference_totalDegree_le 1 h G
      simp only [List.length_cons]
      omega)

/-- The prescribed top component is the iterated directional derivative,
including when the component drops to zero. -/
theorem homogeneousComponent_weylDifference (hs : List (Fin n → ℤ)) (G : IntForm n)
    {d : ℕ} (hd : hs.length < d) (hG : G.totalDegree ≤ d) :
    homogeneousComponent (d - hs.length) (weylDifference hs G) =
      weylDirectionalDerivative hs (homogeneousComponent d G) := by
  induction hs generalizing d G with
  | nil => simp
  | cons h hs ih =>
    have hlen : hs.length < d-1 := by simp at hd; omega
    have hd₂ : 2 ≤ d := by simp at hd; omega
    have hde := (dilatedDifference_totalDegree_le 1 h G).trans (Nat.sub_le_sub_right hG 1)
    simp only [weylDifference_cons, weylDirectionalDerivative_cons, List.length_cons]
    rw [show d - (hs.length + 1) = d - 1 - hs.length by omega, ih _ hlen hde,
      homogeneousComponent_dilatedDifference 1 h G hd₂ hG]

private def directionalDerivativeOp (h : Fin n → ℤ) : IntForm n →ₗ[ℤ] IntForm n :=
  ∑ i, h i • (pderiv i).toLinearMap

private theorem directionalDerivativeOp_apply (h : Fin n → ℤ) (G : IntForm n) :
    directionalDerivativeOp h G = directionalDerivative h G := by
  simp [directionalDerivativeOp, directionalDerivative, Algebra.smul_def, MvPolynomial.algebraMap_eq]

private def weylDerivativeOp : List (Fin n → ℤ) → IntForm n →ₗ[ℤ] IntForm n
  | [] => LinearMap.id
  | h :: hs => (weylDerivativeOp hs).comp (directionalDerivativeOp h)

private theorem weylDerivativeOp_apply (hs : List (Fin n → ℤ)) (G : IntForm n) :
    weylDerivativeOp hs G = weylDirectionalDerivative hs G := by
  induction hs generalizing G with
  | nil => rfl
  | cons h hs ih =>
    simp only [weylDerivativeOp, LinearMap.comp_apply, directionalDerivativeOp_apply,
      weylDirectionalDerivative_cons, ih]

private theorem pderiv_directionalDerivative (i : Fin n) (h : Fin n → ℤ) (G : IntForm n) :
    pderiv i (directionalDerivative h G) = directionalDerivative h (pderiv i G) := by
  unfold directionalDerivative
  simp only [map_sum, pderiv_C_mul, hessian_pderiv_swap _ i]

private theorem directionalDerivative_commute (h u : Fin n → ℤ) (G : IntForm n) :
    directionalDerivative h (directionalDerivative u G) =
      directionalDerivative u (directionalDerivative h G) := by
  calc
    _ = ∑ i, ∑ j, C (h i) * (C (u j) * pderiv j (pderiv i G)) := by
      simp only [directionalDerivative, map_sum, pderiv_C_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hessian_pderiv_swap G i j]
    _ = ∑ j, ∑ i, C (u j) * (C (h i) * pderiv i (pderiv j G)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hessian_pderiv_swap G j i, ← mul_assoc, ← mul_assoc, mul_comm (C (u j))]
    _ = _ := by
      simp only [directionalDerivative, map_sum, pderiv_C_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hessian_pderiv_swap G i j]

/-- The leading directional derivatives are invariant under any reordering
of the differencing directions. -/
theorem weylDirectionalDerivative_perm {hs ts : List (Fin n → ℤ)} (h : hs.Perm ts) (G : IntForm n) :
    weylDirectionalDerivative hs G = weylDirectionalDerivative ts G := by
  induction h generalizing G with
  | nil => rfl
  | cons a _ ih => simpa only [weylDirectionalDerivative_cons] using ih (directionalDerivative a G)
  | swap a b hs => simp only [weylDirectionalDerivative_cons, directionalDerivative_commute a b]
  | trans _ _ ih₁ ih₂ => exact (ih₁ G).trans (ih₂ G)


/-- The polarized leading form has its expected homogeneous degree. -/
theorem weylDirectionalDerivative_homogeneous (hs : List (Fin n → ℤ)) {G : IntForm n}
    {e : ℕ} (hG : G.IsHomogeneous e) :
    (weylDirectionalDerivative hs G).IsHomogeneous (e-hs.length) := by
  induction hs generalizing G e with
  | nil => simpa
  | cons h hs ih =>
    have h₀ : (directionalDerivative h G).IsHomogeneous (e-1) := by
      unfold directionalDerivative
      apply IsHomogeneous.sum
      intro j _
      exact (hG.pderiv (i := j)).C_mul _
    simpa only [weylDirectionalDerivative_cons, List.length_cons,
      show e-1-hs.length = e-(hs.length+1) by omega] using ih h₀

/-- The coefficient of the base point in the terminal affine phase, computed
from the leading form alone. -/
def weylFrequency (hs : List (Fin n → ℤ)) (G : IntForm n) (i : Fin n) : ℤ :=
  MvPolynomial.aeval (0 : Fin n → ℤ) (pderiv i (weylDirectionalDerivative hs G))

private def weylFrequencyOp (hs : List (Fin n → ℤ)) (i : Fin n) : IntForm n →ₗ[ℤ] ℤ :=
  (MvPolynomial.aeval (0 : Fin n → ℤ)).toLinearMap.comp
    ((pderiv i).toLinearMap.comp (weylDerivativeOp hs))

private theorem weylFrequencyOp_apply (hs : List (Fin n → ℤ)) (G : IntForm n) (i : Fin n) :
    weylFrequencyOp hs i G = weylFrequency hs G i := by
  simp [weylFrequencyOp, weylFrequency, weylDerivativeOp_apply]

theorem weylFrequency_cons (h : Fin n → ℤ) (hs : List (Fin n → ℤ)) (G : IntForm n) (i : Fin n) :
    weylFrequency (h :: hs) G i = ∑ j, h j * weylFrequency hs (pderiv j G) i := by
  change weylFrequency hs (directionalDerivative h G) i = _
  simp_rw [← weylFrequencyOp_apply, ← directionalDerivativeOp_apply, directionalDerivativeOp,
    LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
    map_sum, map_smul, smul_eq_mul]

theorem weylFrequency_perm {hs ts : List (Fin n → ℤ)} (h : hs.Perm ts) (G : IntForm n) :
    weylFrequency hs G = weylFrequency ts G := by
  funext i
  simp only [weylFrequency, weylDirectionalDerivative_perm h G]

theorem weylFrequency_append (hs ts : List (Fin n → ℤ)) (G : IntForm n) :
    weylFrequency (hs ++ ts) G = weylFrequency ts (weylDirectionalDerivative hs G) := by
  funext i
  simp only [weylFrequency, weylDirectionalDerivative_append]

/-- The integer matrix of the last-shift frequency map. -/
def weylLastMatrix (hs : List (Fin n → ℤ)) (G : IntForm n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => MvPolynomial.aeval (0 : Fin n → ℤ)
    (pderiv i (pderiv j (weylDirectionalDerivative hs G)))

/-- The linear matrix used when shrinking one active shift block is symmetric. -/
theorem weylLastMatrix_transpose (hs : List (Fin n → ℤ)) (G : IntForm n) :
    (weylLastMatrix hs G)ᵀ = weylLastMatrix hs G := by
  ext i j
  simp only [Matrix.transpose_apply, weylLastMatrix, hessian_pderiv_swap _ j i]

theorem weylFrequency_append_singleton (hs : List (Fin n → ℤ)) (h : Fin n → ℤ) (G : IntForm n) :
    weylFrequency (hs ++ [h]) G = weylLastMatrix hs G *ᵥ h := by
  funext i
  rw [weylFrequency_append, weylFrequency_cons]
  simp only [Matrix.mulVec, dotProduct, weylLastMatrix, weylFrequency, weylDirectionalDerivative_nil]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Any shift block is a symmetric linear variable, with the matrix depending
only on the other blocks. -/
theorem weylFrequency_block (hs ts : List (Fin n → ℤ)) (h : Fin n → ℤ) (G : IntForm n) :
    weylFrequency (hs ++ h :: ts) G = weylLastMatrix (hs ++ ts) G *ᵥ h := by
  have hperm : (hs ++ h :: ts).Perm ((hs ++ ts) ++ [h]) := by
    have hh : (hs ++ h :: ts).Perm (h :: (hs ++ ts)) := List.perm_middle
    exact hh.trans (by simpa using (List.perm_append_comm : ([h] ++ (hs ++ ts)).Perm ((hs ++ ts) ++ [h])))
  rw [weylFrequency_perm hperm G, weylFrequency_append_singleton]

/-- The symmetric-block formula with an arbitrary finite tuple index as pivot. -/
theorem weylFrequency_ofFn_insertNth {k : ℕ} (i : Fin (k+1))
    (u : Fin n → ℤ) (ts : Fin k → Fin n → ℤ) (G : IntForm n) :
    weylFrequency (List.ofFn (Fin.insertNth i u ts : Fin (k+1) → Fin n → ℤ)) G =
      weylLastMatrix (List.ofFn ts) G *ᵥ u := by
  let e : Equiv.Perm (Fin (k+1)) := (finSuccEquiv k).trans (finSuccEquiv' i).symm
  have hf : (Fin.insertNth i u ts : Fin (k+1) → Fin n → ℤ) ∘ e = Fin.cons u ts := by
    funext j
    refine Fin.cases ?_ (fun a => ?_) j
    · simp [e, finSuccEquiv_zero, finSuccEquiv'_symm_none, Fin.insertNth_apply_same]
    · simp [e, finSuccEquiv_succ, finSuccEquiv'_symm_some, Fin.insertNth_apply_succAbove]
  have hp := e.ofFn_comp_perm (Fin.insertNth i u ts : Fin (k+1) → Fin n → ℤ)
  rw [hf, List.ofFn_succ] at hp
  simp only [Fin.cons_zero, Fin.cons_succ] at hp
  rw [weylFrequency_perm hp.symm G]
  simpa using weylFrequency_block [] (List.ofFn ts) u G

private def weylFrequencyBound : ℕ → IntForm n → ℝ
  | 0, G => 1 + ∑ i, |(weylFrequency [] G i : ℝ)|
  | k+1, G => 1 + ∑ i, weylFrequencyBound k (pderiv i G)

private theorem weylFrequencyBound_pos (k : ℕ) (G : IntForm n) :
    0 < weylFrequencyBound k G := by
  induction k generalizing G with
  | zero =>
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  | succ k ih =>
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => (ih _).le)

private theorem nonneg_list_prod_of_weylShiftBounds {hs : List (Fin n → ℤ)} {H : List ℝ}
    (hh : List.Forall₂ (fun h R => 0 ≤ R ∧ ∀ j, |(h j : ℝ)| ≤ R) hs H) : 0 ≤ H.prod := by
  induction hh with
  | nil => simp
  | cons hb _ ih => exact mul_nonneg hb.1 ih

/-- The fixed polynomial coefficients give a uniform bound proportional to
the product of the real shift radii. -/
theorem abs_weylFrequency_le (G : IntForm n) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (hs : List (Fin n → ℤ)) (H : List ℝ),
      hs.length = k →
      List.Forall₂ (fun h R => 0 ≤ R ∧ ∀ j, |(h j : ℝ)| ≤ R) hs H →
      ∀ i, |(weylFrequency hs G i : ℝ)| ≤ B * H.prod := by
  refine ⟨weylFrequencyBound k G, weylFrequencyBound_pos k G, ?_⟩
  intro hs H hk hh
  subst k
  induction hh generalizing G with
  | nil =>
    intro i
    simp only [List.length_nil, List.prod_nil, mul_one, weylFrequencyBound]
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (weylFrequency [] G j : ℝ))
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
  | @cons h R hs H hh₀ hh ih =>
    intro i
    simp only [weylFrequency_cons, Int.cast_sum, Int.cast_mul, List.length_cons, List.prod_cons]
    calc
      _ ≤ ∑ j, |(h j : ℝ) * (weylFrequency hs (pderiv j G) i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, R * (weylFrequencyBound hs.length (pderiv j G) * H.prod) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hh₀.2 j) (ih (pderiv j G) i) (abs_nonneg _) hh₀.1
      _ = (∑ j, weylFrequencyBound hs.length (pderiv j G)) * (R * H.prod) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
        exact mul_nonneg hh₀.1 (nonneg_list_prod_of_weylShiftBounds hh)


private theorem pderiv_homogeneous_one_eq_const {L : IntForm n} (hL : L.IsHomogeneous 1)
    (i : Fin n) : pderiv i L = C (aeval (0 : Fin n → ℤ) (pderiv i L)) := by
  have hd := (hL.pderiv (i := i)).totalDegree_le
  obtain ⟨a,ha⟩ : ∃ a : ℤ, pderiv i L = C a :=
    ⟨_, totalDegree_eq_zero_iff_eq_C.mp (show (pderiv i L).totalDegree = 0 by omega)⟩
  rw [ha]
  simp

/-- At degree one the zero frequency vector is equivalent to the zero
polarized leading form. -/
theorem weylFrequency_zero_iff (hs : List (Fin n → ℤ)) {G : IntForm n}
    {e : ℕ} (hG : G.IsHomogeneous e) (he : hs.length+1 = e) :
    (∀ i, weylFrequency hs G i = 0) ↔ weylDirectionalDerivative hs G = 0 := by
  have hH : (weylDirectionalDerivative hs G).IsHomogeneous 1 := by
    simpa only [show e - hs.length = 1 by omega] using weylDirectionalDerivative_homogeneous hs hG
  constructor
  · intro h
    have hz (i : Fin n) : pderiv i (weylDirectionalDerivative hs G) = 0 := by
      rw [pderiv_homogeneous_one_eq_const hH, ← weylFrequency, h, map_zero]
    simpa only [hz, mul_zero, Finset.sum_const_zero, one_nsmul] using hH.sum_X_mul_pderiv.symm
  · intro h i
    simp [weylFrequency, h]

private theorem evalForm_eq_int_aeval (G : IntForm n) (x : Fin n → ℤ) :
    evalForm G x = aeval x G := by
  rw [evalForm, aeval_def]
  congr

private theorem eval_affine_form (g : IntForm n) (hg : g.totalDegree ≤ 1) (x : Fin n → ℤ) :
    evalForm g x = g.coeff 0 +
      ∑ i, x i * aeval (0 : Fin n → ℤ) (pderiv i (homogeneousComponent 1 g)) := by
  let L := homogeneousComponent 1 g
  have heq : g = C (g.coeff 0) + L := by
    rw [← homogeneousComponent_zero]
    have hs := (sum_homogeneousComponent g).symm
    rcases (show g.totalDegree = 0 ∨ g.totalDegree = 1 by omega) with hzero | hone
    · have hL : L = 0 := homogeneousComponent_eq_zero _ _ (by omega)
      simpa [hzero, hL, L, Finset.sum_range_succ] using hs
    · simpa [hone, L, Finset.sum_range_succ] using hs
  have hLhom : L.IsHomogeneous 1 := homogeneousComponent_isHomogeneous 1 g
  have heval (i : Fin n) :
      aeval x (pderiv i L) = aeval (0 : Fin n → ℤ) (pderiv i L) := by
    rw [pderiv_homogeneous_one_eq_const hLhom]
    simp
  have hlinear := congrArg (fun z => aeval x z) hLhom.sum_X_mul_pderiv
  simp only [map_sum, map_mul, aeval_X, heval, one_nsmul] at hlinear
  rw [evalForm_eq_int_aeval]
  calc
    _ = aeval x (C (g.coeff 0) + L) := congrArg (fun z => aeval x z) heq
    _ = _ := by rw [map_add, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, ← hlinear]

/-- After exactly \(d-1\) shifts, the actual integer polynomial has a constant
term and the frequencies obtained by polarizing its prescribed degree-d part. -/
theorem eval_weylDifference_affine (hs : List (Fin n → ℤ)) (G : IntForm n)
    {d : ℕ} (hd : hs.length + 1 = d) (hG : G.totalDegree ≤ d) (x : Fin n → ℤ) :
    evalForm (weylDifference hs G) x =
      (weylDifference hs G).coeff 0 +
        ∑ i, x i * weylFrequency hs (homogeneousComponent d G) i := by
  have ht : (weylDifference hs G).totalDegree ≤ 1 :=
    (weylDifference_totalDegree_le hs G).trans (by omega)
  have hL := homogeneousComponent_weylDifference hs G (by omega : hs.length < d) hG
  rw [show d - hs.length = 1 by omega] at hL
  simp only [eval_affine_form _ ht, hL, weylFrequency]


end

end Birch
