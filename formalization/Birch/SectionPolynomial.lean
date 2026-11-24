import Birch.DilatedDifference
import Birch.MajorArcLatticePoisson
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Integral polynomial restrictions to affine sections

The restricted leading form uses only the matrix of the section. Translates
from lattice cosets and frozen coordinates enter only in lower degrees.
-/

open MvPolynomial Matrix ZMod
open scoped BigOperators Matrix

namespace Birch

noncomputable section

variable {n l r : ℕ}

/-- Substitute the integral affine map `x ↦ U x + c` into a polynomial. -/
def affineSection (U : Matrix (Fin n) (Fin l) ℤ) (c : Fin n → ℤ) : IntForm n →ₐ[ℤ] IntForm l :=
  aeval fun i => (∑ j, C (U i j) * X j) + C (c i)

/-- Substitute the linear part of an affine section. -/
def linearSection (U : Matrix (Fin n) (Fin l) ℤ) : IntForm n →ₐ[ℤ] IntForm l :=
  aeval fun i => ∑ j, C (U i j) * X j

@[simp] theorem linearSection_X (U : Matrix (Fin n) (Fin l) ℤ) (i : Fin n) :
    linearSection U (X i) = ∑ j, C (U i j) * X j := by simp [linearSection]

@[simp] theorem linearSection_C (U : Matrix (Fin n) (Fin l) ℤ) (c : ℤ) :
    linearSection U (C c) = C c := by simp [linearSection]

/-- Evaluation commutes with the affine section over any coefficient ring. -/
theorem evalForm_affineSection {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin l) ℤ) (c : Fin n → ℤ) (F : IntForm n) (x : Fin l → R) :
    evalForm (affineSection U c F) x =
      evalForm F (fun i => (∑ j, (U i j : R) * x j) + (c i : R)) := by
  rw [affineSection, aeval_def, algebraMap_eq, evalForm, ← eval₂_assoc]
  simp only [evalForm, eval₂_add, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom]

/-- Evaluation after linear substitution is evaluation at the matrix product. -/
theorem evalForm_linearSection {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) (x : Fin l → R) :
    evalForm (linearSection U F) x = evalForm F (fun i => ∑ j, (U i j : R) * x j) := by
  rw [linearSection, aeval_def, algebraMap_eq, evalForm, ← eval₂_assoc]
  simp only [evalForm, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom]

private theorem aeval_totalDegree_le (g : Fin n → IntForm l) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (F : IntForm n) : (aeval g F).totalDegree ≤ F.totalDegree := by
  simp only [aeval_def, eval₂_eq, algebraMap_eq]
  apply totalDegree_finsetSum_le
  intro s hs
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd ..).trans ?_
  refine (Finset.sum_le_sum fun i _ ↦ (totalDegree_pow _ _).trans ?_).trans (le_totalDegree hs)
  simpa only [mul_one] using Nat.mul_le_mul_left (s i) (hg i)

private theorem sectionCoordinates_homogeneous (U : Matrix (Fin n) (Fin l) ℤ) (i : Fin n) :
    (∑ j, C (U i j) * X j : IntForm l).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ 1 fun _ _ => isHomogeneous_C_mul_X _ _

/-- Affine substitution preserves a bound for the total degree. -/
theorem affineSection_totalDegree_le (U : Matrix (Fin n) (Fin l) ℤ) (c : Fin n → ℤ) (F : IntForm n) :
    (affineSection U c F).totalDegree ≤ F.totalDegree := by
  apply aeval_totalDegree_le
  intro i
  exact (totalDegree_add _ _).trans <|
    max_le (sectionCoordinates_homogeneous U i).totalDegree_le (by rw [totalDegree_C]; exact Nat.zero_le _)

/-- Linear substitution preserves a bound for the total degree. -/
theorem linearSection_totalDegree_le (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) :
    (linearSection U F).totalDegree ≤ F.totalDegree :=
  aeval_totalDegree_le _ (fun i => (sectionCoordinates_homogeneous U i).totalDegree_le) F

/-- A homogeneous polynomial stays homogeneous under linear substitution. -/
theorem isHomogeneous_linearSection (U : Matrix (Fin n) (Fin l) ℤ) {F : IntForm n}
    (hF : F.IsHomogeneous r) : (linearSection U F).IsHomogeneous r := by
  simpa only [linearSection, one_mul] using hF.aeval _ (sectionCoordinates_homogeneous U)

/-- Every homogeneous component commutes with linear substitution. -/
theorem homogeneousComponent_linearSection (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) (r : ℕ) :
    homogeneousComponent r (linearSection U F) = linearSection U (homogeneousComponent r F) := by
  have hs := sum_homogeneousComponent F
  have hterm (i : ℕ) :
      homogeneousComponent r (linearSection U (homogeneousComponent i F)) =
        linearSection U (homogeneousComponent r (homogeneousComponent i F)) := by
    rw [homogeneousComponent_of_mem (isHomogeneous_linearSection U (homogeneousComponent_isHomogeneous i F)),
      homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous i F)]
    split_ifs <;> simp
  calc
    _ = homogeneousComponent r (linearSection U (∑ i ∈ Finset.range (F.totalDegree + 1),
          homogeneousComponent i F)) := congrArg (fun G => homogeneousComponent r (linearSection U G)) hs.symm
    _ = linearSection U (homogeneousComponent r (∑ i ∈ Finset.range (F.totalDegree + 1),
          homogeneousComponent i F)) := by simp only [map_sum, hterm]
    _ = _ := congrArg (fun G => linearSection U (homogeneousComponent r G)) hs

private theorem affineSection_comp_translate (U : Matrix (Fin n) (Fin l) ℤ) (c : Fin n → ℤ) :
    (linearSection U).comp (aeval (fun i => X i + C (c i))) = affineSection U c := by
  ext i
  simp [affineSection]

/-- The top homogeneous component of an affine restriction depends only on
its linear matrix and the top homogeneous component of the original polynomial. -/
theorem homogeneousComponent_affineSection (U : Matrix (Fin n) (Fin l) ℤ) (c : Fin n → ℤ)
    (F : IntForm n) (hF : F.totalDegree ≤ r) :
    homogeneousComponent r (affineSection U c F) = linearSection U (homogeneousComponent r F) := by
  by_cases hr : r = 0
  · subst r
    have hconst := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hF)
    rw [hconst]
    simp only [affineSection, aeval_C, algebraMap_eq, homogeneousComponent_zero, linearSection_C,
      coeff_C]
  have htranslate := mul_dilatedDifference 1 c F
  simp only [map_one, one_mul] at htranslate
  have hshift : aeval (fun i => X i + C (c i)) F = F + dilatedDifference 1 c F := by
    rw [htranslate]; ring
  have hless : (dilatedDifference 1 c F).totalDegree < r :=
    (dilatedDifference_totalDegree_le 1 c F).trans_lt (by omega)
  rw [← affineSection_comp_translate, AlgHom.comp_apply, hshift, homogeneousComponent_linearSection,
    map_add, homogeneousComponent_eq_zero _ _ hless, add_zero]

private theorem pderiv_linearSection_X (U : Matrix (Fin n) (Fin l) ℤ) (i : Fin n) (j : Fin l) :
    pderiv j (linearSection U (X i)) = C (U i j) := by
  classical
  simp [pderiv_X, Pi.single_apply, mul_ite]

/-- The partial derivative of the restriction satisfies the matrix chain rule. -/
theorem pderiv_linearSection (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) (j : Fin l) :
    pderiv j (linearSection U F) = ∑ i, C (U i j) * linearSection U (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG =>
    simp only [map_add, hF, hG, mul_add, Finset.sum_add_distrib]
  | mul_X F k hF =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hF, pderiv_linearSection_X, map_add,
      mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single k]
      · simp [pderiv_X]
        ring
      · intro i _ hi
        simp [pderiv_X, Pi.single_eq_of_ne hi.symm]
      · simp
    · apply Finset.sum_congr rfl
      intro i _
      ring

/-- Evaluated chain rule for an integral linear matrix in any coefficient ring. -/
theorem evalForm_pderiv_linearSection {K : Type*} [CommRing K]
    (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) (j : Fin l) (x : Fin l → K) :
    evalForm (pderiv j (linearSection U F)) x =
      ∑ i, (U i j : K) * evalForm (pderiv i F) ((U.map (fun c : ℤ => (c : K))) *ᵥ x) := by
  rw [pderiv_linearSection]
  change (eval₂Hom (Int.castRingHom K) x) (∑ i, C (U i j) * linearSection U (pderiv i F)) = _
  simp only [map_sum, map_mul, coe_eval₂Hom, eval₂_C, Int.coe_castRingHom]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact evalForm_linearSection U (pderiv i F) x

/-- A section with a smooth leading restriction has independent columns over
any coefficient ring on which its gradient vanishes only at the origin. -/
theorem linearSection_mulVec_injective {K : Type*} [CommRing K]
    (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) (hr : 2 ≤ r) (hF : F.IsHomogeneous r)
    (hs : ∀ x : Fin l → K, (∀ j, evalForm (pderiv j (linearSection U F)) x = 0) → x = 0) :
    Function.Injective (fun x : Fin l → K => (U.map (fun c : ℤ => (c : K))) *ᵥ x) := by
  let A := U.map (fun c : ℤ => (c : K))
  have hz (i : Fin n) : evalForm (pderiv i F) (0 : Fin n → K) = 0 := by
    have h := evalForm_scale (R := K) (F := pderiv i F) hF.pderiv 0 (0 : Fin n → K)
    have h0 : (fun j : Fin n => (0 : K) * (0 : Fin n → K) j) = 0 := by ext j; simp
    rwa [h0, zero_pow (show r - 1 ≠ 0 by omega), zero_mul] at h
  intro x y hxy
  change A *ᵥ x = A *ᵥ y at hxy
  have hn : A *ᵥ (x-y) = 0 := by rw [mulVec_sub, hxy, sub_self]
  apply sub_eq_zero.mp
  apply hs
  intro j
  rw [evalForm_pderiv_linearSection]
  change (∑ i, (U i j : K) * evalForm (pderiv i F) (A *ᵥ (x-y))) = 0
  simp only [hn, hz, mul_zero, Finset.sum_const_zero]

/-- Geometric nonsingularity of the leading restriction implies injectivity
of its matrix over the prime field. -/
theorem linearSection_mulVec_injective_of_geometric {p : ℕ} [Fact p.Prime]
    (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) (hr : 2 ≤ r) (hF : F.IsHomogeneous r)
    (hs : ∀ x : Fin l → AlgebraicClosure (ZMod p),
      (∀ j, evalForm (pderiv j (linearSection U F)) x = 0) → x = 0) :
    Function.Injective (fun x : Fin l → ZMod p => (U.map (fun c : ℤ => (c : ZMod p))) *ᵥ x) := by
  apply linearSection_mulVec_injective U F hr hF
  intro x hx
  let f := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  have hzero (j : Fin l) :
      evalForm (pderiv j (linearSection U F)) (fun i => f (x i)) = 0 := by
    rw [← evalForm_map, hx j, map_zero]
  have H := hs _ hzero
  funext i
  apply f.injective
  simpa only [Pi.zero_apply, map_zero] using congrFun H i

/-- A geometrically smooth section has linearly independent columns over the prime field. -/
theorem linearSection_cols_linearIndependent {p : ℕ} [Fact p.Prime]
    (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) (hr : 2 ≤ r) (hF : F.IsHomogeneous r)
    (hs : ∀ x : Fin l → AlgebraicClosure (ZMod p),
      (∀ j, evalForm (pderiv j (linearSection U F)) x = 0) → x = 0) :
    LinearIndependent (ZMod p) (U.map (Int.castRingHom (ZMod p))).col :=
  Matrix.mulVec_injective_iff.mp (linearSection_mulVec_injective_of_geometric U F hr hF hs)

/-- The matrix in the free coordinates of a full lattice frame. -/
def sectionFreeColumns {s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) :
    Matrix (Fin (l+s)) (Fin l) ℤ := fun i j => A i (Fin.castAdd s j)

/-- The free-column matrix of a frame extending `U` is `U`. -/
theorem sectionFreeColumns_eq_of_cols {s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ)
    (U : Matrix (Fin (l+s)) (Fin l) ℤ) (h : ∀ j, A.col (Fin.castAdd s j) = U.col j) :
    sectionFreeColumns A = U := by
  ext i j
  exact congrFun (h j) i

/-- The offset in a slice of a lattice coset after the last coordinates are frozen. -/
def sectionFrozenOffset {s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ)
    (b : Fin (l+s) → ℤ) (v : Fin s → ℤ) : Fin (l+s) → ℤ :=
  fun i => b i + ∑ j, A i (Fin.natAdd l j) * v j

/-- Splitting a lattice frame into free columns and a fixed offset recovers each slice point. -/
theorem sectionFrozenOffset_add_mulVec {s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ)
    (b : Fin (l+s) → ℤ) (v : Fin s → ℤ) (x : Fin l → ℤ) :
    sectionFrozenOffset A b v + sectionFreeColumns A *ᵥ x = b + A *ᵥ Fin.append x v := by
  funext i
  simp only [sectionFreeColumns, sectionFrozenOffset, Pi.add_apply, mulVec, dotProduct,
    Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  ring

/-- The affine substitution on a slice agrees with evaluation in the full lattice frame. -/
theorem evalForm_affineSection_frozen {s : ℕ} (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ)
    (b : Fin (l+s) → ℤ) (v : Fin s → ℤ) (F : IntForm (l+s)) (x : Fin l → ℤ) :
    evalForm (affineSection (sectionFreeColumns A) (sectionFrozenOffset A b v) F) x =
      evalForm F (b + A *ᵥ Fin.append x v) := by
  rw [← sectionFrozenOffset_add_mulVec, evalForm_affineSection]
  congr 1
  funext i
  simp only [Int.cast_id, Pi.add_apply, mulVec, dotProduct, add_comm]

/-- The exact phase on an integral point in the section, expressed via its residue. -/
theorem phase_evalForm_affineSection {q : ℕ} [NeZero q]
    (U : Matrix (Fin n) (Fin l) ℤ) (c : Fin n → ℤ) (F : IntForm n)
    (a : ℤ) (x : Fin l → ℤ) :
    phase ((a : ℝ) / (q : ℝ) * ((evalForm F (c + U *ᵥ x) : ℤ) : ℝ)) =
      stdAddChar ((a : ZMod q) * residueEval (affineSection U c F) q (fun i => (x i : ZMod q))) := by
  have he : evalForm (affineSection U c F) x = evalForm F (c + U *ᵥ x) := by
    rw [evalForm_affineSection]
    congr 1
    funext i
    simp [mulVec, dotProduct, add_comm]
  rw [← he]
  have hcast (G : IntForm l) : ((evalForm G x : ℤ) : ZMod q) =
      residueEval G q (fun i => (x i : ZMod q)) := evalForm_map (Int.castRingHom (ZMod q)) G x
  rw [div_mul_eq_mul_div, ← Int.cast_mul, phase_int_div, Int.cast_mul, hcast]

/-- The rational phase in a frozen-coordinate slice is the residue weight of its affine polynomial. -/
theorem phase_evalForm_affineSection_frozen {q s : ℕ} [NeZero q]
    (A : Matrix (Fin (l+s)) (Fin (l+s)) ℤ) (b : Fin (l+s) → ℤ) (v : Fin s → ℤ)
    (F : IntForm (l+s)) (a : ℤ) (x : Fin l → ℤ) :
    phase ((a : ℝ) / (q : ℝ) * ((evalForm F (b + A *ᵥ Fin.append x v) : ℤ) : ℝ)) =
      stdAddChar ((a : ZMod q) * residueEval
        (affineSection (sectionFreeColumns A) (sectionFrozenOffset A b v) F) q (fun i => (x i : ZMod q))) := by
  rw [← sectionFrozenOffset_add_mulVec, phase_evalForm_affineSection]

/-- The finite character factor on a section, with the positive Poisson phase. -/
theorem section_twistedCompleteSum {q : ℕ} [NeZero q]
    (U : Matrix (Fin n) (Fin l) ℤ) (c : Fin n → ℤ) (F : IntForm n) (a : ℤ) (z : Fin l → ℤ) :
    ((q : ℂ)^l)⁻¹ * ∑ t : Fin l → ZMod q,
      stdAddChar ((a : ZMod q) * residueEval (affineSection U c F) q t) *
        phase (∑ i, (z i : ℝ) * ((t i).val : ℝ) / (q : ℝ)) =
      twistedCompleteSum (affineSection U c F) q a z :=
  (twistedCompleteSum_unfold_char _ _ _).symm

end
end Birch
