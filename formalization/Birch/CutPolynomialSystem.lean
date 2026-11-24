import Birch.ConeHyperplane
import Birch.MacaulayMatrix
import Mathlib.Algebra.MvPolynomial.Coeff

/-! # Macaulay tests for polynomial systems cut by linear equations -/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

variable {n m k e D : ℕ} {K L : Type*} [CommRing K] [CommRing L]

/-- Add the prescribed linear equations in the same homogeneous degree
as the original system. -/
def cutPolynomialSystem (f : Fin m → MvPolynomial (Fin n) K) (c : K)
    (a : Fin k → Fin n → K) (e : ℕ) : Fin (m+k) → MvPolynomial (Fin n) K :=
  Fin.append f (fun j => C c * (normalLinearForm (a j))^e)

theorem normalLinearForm_isHomogeneous (a : Fin n → K) : (normalLinearForm a).IsHomogeneous 1 := by
  unfold normalLinearForm
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ i

theorem cutPolynomialSystem_isHomogeneous
    (f : Fin m → MvPolynomial (Fin n) K) (c : K) (a : Fin k → Fin n → K)
    (hf : ∀ i, (f i).IsHomogeneous e) (j : Fin (m+k)) :
    (cutPolynomialSystem f c a e j).IsHomogeneous e := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [cutPolynomialSystem, Fin.append_left] using hf i
  · have h := (isHomogeneous_C (Fin n) c).mul ((normalLinearForm_isHomogeneous (a i)).pow e)
    simpa only [cutPolynomialSystem, Fin.append_right, zero_add, one_mul] using h

/-- A nonzero multiplier and positive powers preserve the common zero set
of the system together with its linear cuts. -/
theorem eval_cutPolynomialSystem_eq_zero_iff [NoZeroDivisors K]
    (f : Fin m → MvPolynomial (Fin n) K) {c : K} (hc : c ≠ 0)
    (a : Fin k → Fin n → K) (he : 0 < e) (x : Fin n → K) :
    (∀ j, (cutPolynomialSystem f c a e j).eval x = 0) ↔
      (∀ i, (f i).eval x = 0) ∧ (∀ j, (normalLinearForm (a j)).eval x = 0) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simpa only [cutPolynomialSystem, Fin.append_left] using h (Fin.castAdd k i)
    · have hj := h (Fin.natAdd m j)
      simp only [cutPolynomialSystem, Fin.append_right, eval_mul, eval_C, eval_pow] at hj
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hj).resolve_left hc)
  · rintro ⟨hf, ha⟩ j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [cutPolynomialSystem, Fin.append_left] using hf i
    · simp only [cutPolynomialSystem, Fin.append_right, eval_mul, eval_C, eval_pow,
        ha, zero_pow he.ne', mul_zero]

theorem normalLinearForm_map (φ : K →+* L) (a : Fin n → K) :
    MvPolynomial.map φ (normalLinearForm a) = normalLinearForm (φ ∘ a) := by
  simp only [normalLinearForm, map_sum, map_mul, map_C, map_X, Function.comp_apply]

/-- Coefficient specialization preserves the linear cuts and their powers. -/
theorem cutPolynomialSystem_map (φ : K →+* L) (f : Fin m → MvPolynomial (Fin n) K) (c : K)
    (a : Fin k → Fin n → K) (e : ℕ) :
    (fun j => MvPolynomial.map φ (cutPolynomialSystem f c a e j)) =
      cutPolynomialSystem (fun i => MvPolynomial.map φ (f i)) (φ c) (fun j => φ ∘ a j) e := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [cutPolynomialSystem, Fin.append_left]
  · simp only [cutPolynomialSystem, Fin.append_right, map_mul, map_C, map_pow, normalLinearForm_map]

/-- The determinant of a maximal Macaulay minor commutes with coefficient
specialization. -/
theorem map_systemMacaulayMinor (φ : K →+* L) (f : Fin m → MvPolynomial (Fin n) K) (e D : ℕ)
    (sel : DegreeMonomial n D → Fin m × DegreeMonomial n (D-e)) :
    φ ((systemMacaulayMatrix f e D).submatrix id sel).det =
      ((systemMacaulayMatrix (fun i => MvPolynomial.map φ (f i)) e D).submatrix id sel).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, systemMacaulayMatrix_map]

theorem map_cutPolynomialSystem_macaulayMinor (φ : K →+* L)
    (f : Fin m → MvPolynomial (Fin n) K) (c : K) (a : Fin k → Fin n → K) (e D : ℕ)
    (sel : DegreeMonomial n D → Fin (m+k) × DegreeMonomial n (D-e)) :
    φ ((systemMacaulayMatrix (cutPolynomialSystem f c a e) e D).submatrix id sel).det =
      ((systemMacaulayMatrix
        (cutPolynomialSystem (fun i => MvPolynomial.map φ (f i)) (φ c) (fun j => φ ∘ a j) e)
        e D).submatrix id sel).det := by
  rw [map_systemMacaulayMinor, cutPolynomialSystem_map]

/-- A maximal minor has degree at most the coefficient bound times its size. -/
theorem systemMacaulayMinor_totalDegree_le {σ R : Type*} [CommRing R]
    (f : Fin m → MvPolynomial (Fin n) (MvPolynomial σ R)) (e D B : ℕ)
    (hcoeff : ∀ j b, (coeff b (f j)).totalDegree ≤ B)
    (sel : DegreeMonomial n D → Fin m × DegreeMonomial n (D-e)) :
    ((systemMacaulayMatrix f e D).submatrix id sel).det.totalDegree ≤
      B * Fintype.card (DegreeMonomial n D) := by
  classical
  let M := (systemMacaulayMatrix f e D).submatrix id sel
  have hM (i j : DegreeMonomial n D) : (M i j).totalDegree ≤ B := by
    change (coeff i.val (monomial (sel j).2.val 1 * f (sel j).1)).totalDegree ≤ B
    rw [coeff_monomial_mul', one_mul]
    split_ifs
    · exact hcoeff _ _
    · rw [totalDegree_zero]
      exact Nat.zero_le _
  change M.det.totalDegree ≤ _
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro perm _
  refine (totalDegree_mul _ _).trans ?_
  have hs : (((Equiv.Perm.sign perm : ℤ) : MvPolynomial σ R)).totalDegree = 0 := by
    rw [← map_intCast (C : R →+* MvPolynomial σ R), totalDegree_C]
  rw [hs, zero_add]
  exact (totalDegree_finsetProd ..).trans ((Finset.sum_le_sum fun i _ => hM (perm i) i).trans_eq
    (by simp [Nat.mul_comm]))

/-- Powers of parameter-valued linear forms increase the bound on coefficient
degrees at most proportionally to the exponent. -/
theorem coeff_normalLinearForm_pow_totalDegree_le {σ R : Type*} [CommRing R]
    (a : Fin n → MvPolynomial σ R) {B : ℕ} (ha : ∀ i, (a i).totalDegree ≤ B)
    (b : Fin n →₀ ℕ) (e : ℕ) :
    (coeff b ((normalLinearForm a)^e)).totalDegree ≤ e * B := by
  classical
  have hl : normalLinearForm a = ∑ i, a i • X i := by
    simp only [normalLinearForm, smul_eq_C_mul]
  rw [hl, coeff_linearCombination_X_pow_of_fintype]
  split_ifs with h
  · refine (totalDegree_mul _ _).trans ?_
    have hc : ((b.multinomial : ℕ) : MvPolynomial σ R).totalDegree = 0 := by
      rw [← map_natCast (C : R →+* MvPolynomial σ R), totalDegree_C]
    rw [hc, zero_add]
    change (∏ i ∈ b.support, a i ^ b i).totalDegree ≤ e * B
    refine (totalDegree_finsetProd ..).trans ?_
    calc
      _ ≤ ∑ i ∈ b.support, b i * B := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (Nat.mul_le_mul_left (b i) (ha i))
      _ = e * B := by
        rw [← Finset.sum_mul]
        exact congrArg (· * B) h
  · rw [totalDegree_zero]
    exact Nat.zero_le _

/-- A bound on the original coefficient degrees and the normal entries gives
a bound for all coefficients after adjoining the cuts. -/
theorem coeff_cutPolynomialSystem_totalDegree_le {σ R : Type*} [CommRing R]
    (f : Fin m → MvPolynomial (Fin n) (MvPolynomial σ R)) (c : MvPolynomial σ R)
    (a : Fin k → Fin n → MvPolynomial σ R) (e : ℕ) {B A : ℕ}
    (hf : ∀ i b, (coeff b (f i)).totalDegree ≤ B)
    (ha : ∀ j i, (a j i).totalDegree ≤ A) (j : Fin (m+k)) (b : Fin n →₀ ℕ) :
    (coeff b (cutPolynomialSystem f c a e j)).totalDegree ≤ max B (c.totalDegree + e*A) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [cutPolynomialSystem, Fin.append_left]
    exact (hf i b).trans (le_max_left _ _)
  · rw [cutPolynomialSystem, Fin.append_right, coeff_C_mul]
    exact ((totalDegree_mul _ _).trans
      (add_le_add le_rfl (coeff_normalLinearForm_pow_totalDegree_le (a i) (ha i) b e))).trans
        (le_max_right _ _)

end
end Birch
