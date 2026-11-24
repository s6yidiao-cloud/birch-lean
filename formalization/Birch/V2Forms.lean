import Birch.Main
import Birch.FrozenCoordinates
import Birch.SingularSeries
import Mathlib.Algebra.BigOperators.Finprod

/-! # Forms with arbitrary singular codimension

The v2 manuscript allows compact weights on all of real affine space
and assumes nonsingularity only at the local zeros.
-/

open Filter MeasureTheory MvPolynomial Set
open scoped ContDiff Topology

namespace Birch

noncomputable section

/-- Dimension of the affine gradient locus over the algebraic closure of `ℚ`. -/
def RationalGradientDimension {n : ℕ} (F : IntForm n) (σ : ℕ) : Prop :=
  let K := AlgebraicClosure ℚ
  let J : Ideal (MvPolynomial (Fin n) K) := Ideal.span
    (Set.range fun i : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv i F))
  ringKrullDim (MvPolynomial (Fin n) K ⧸ J) = (σ : ℕ∞)

/-- The weight class shared by the form and the polynomial-cover asymptotics. -/
structure CompactWeight {n : ℕ} (w : (Fin n → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  nonnegative : ∀ x, 0 ≤ w x

/-- One fixed partial derivative is nonzero throughout the support. -/
def HasTransverseSupport {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ i : Fin n, ∀ x ∈ tsupport w, evalForm (pderiv i F) x ≠ 0

/-- The full weighted count, whose summand has finite support for a compact weight
at positive scale. -/
def compactWeightedZeros {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (P : ℝ) : ℝ :=
  ∑ᶠ x : Fin n → ℤ, if evalForm F x = 0 then w (scaledPoint P x) else 0

/-- A box containing the dilation of the support computes the full weighted count. -/
theorem compactWeightedZeros_eq_box {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    {P R : ℝ} (hP : 0 < P)
    (hR : ∀ y, w y ≠ 0 → ∀ i, |y i| ≤ R) :
    compactWeightedZeros F w P =
      ∑ x ∈ latticeBox n (R * P), if evalForm F x = 0 then w (scaledPoint P x) else 0 := by
  unfold compactWeightedZeros
  apply finsum_eq_finsetSum_of_support_subset
  intro x hx
  have hwx : w (scaledPoint P x) ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  apply mem_latticeBox_iff_abs.mpr
  intro i
  have hi := hR _ hwx i
  rwa [scaledPoint, abs_div, abs_of_pos hP, div_le_iff₀ hP] at hi

/-- A positive weighted count with transverse support yields a nonsingular
integral zero. -/
theorem hasNonsingularZero_int_of_weightedZeros_pos {n d : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) {w : (Fin n → ℝ) → ℝ} (hw : HasTransverseSupport F w)
    {P : ℝ} (hcount : 0 < weightedZeros F w P) : HasNonsingularZero F ℤ := by
  classical
  have hex : ∃ x ∈ latticeBox n P, evalForm F x = 0 ∧ w (scaledPoint P x) ≠ 0 := by
    by_contra! h
    have hzero : weightedZeros F w P = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hFx : evalForm F x = 0
      · simp [hFx, h x hx hFx]
      · simp [hFx]
    exact hcount.ne' hzero
  obtain ⟨x, _, hFx, hwx⟩ := hex
  obtain ⟨i, hi⟩ := hw
  let z : Fin n → ℝ := fun j => x j
  refine ⟨x, hFx, i, fun hsing => ?_⟩
  have hz : evalForm (pderiv i F) z = 0 := by
    have h := congrArg (Int.castRingHom ℝ) hsing
    rw [evalForm_hom, map_zero] at h
    exact h
  have hscaled : scaledPoint P x = (fun j => P⁻¹ * z j) := by
    funext j
    simp [scaledPoint, z, div_eq_mul_inv, mul_comm]
  exact hi _ (subset_tsupport _ hwx)
    (by rw [hscaled, evalForm_scale hF.pderiv, hz, mul_zero])

/-- A positive weighted count with transverse support yields a nonsingular
rational zero. -/
theorem hasNonsingularZero_rat_of_weightedZeros_pos {n d : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) {w : (Fin n → ℝ) → ℝ} (hw : HasTransverseSupport F w)
    {P : ℝ} (hcount : 0 < weightedZeros F w P) : HasNonsingularZero F ℚ := by
  obtain ⟨x, hFx, i, hi⟩ := hasNonsingularZero_int_of_weightedZeros_pos hF hw hcount
  refine ⟨fun j => (x j : ℚ), ?_, i, ?_⟩
  · have h := congrArg (Int.castRingHom ℚ) hFx
    rw [evalForm_hom, map_zero] at h
    exact h
  · intro h
    apply hi
    have hCast : (Int.castRingHom ℚ) (evalForm (pderiv i F) x) = 0 :=
      (evalForm_hom (Int.castRingHom ℚ) (pderiv i F) x).trans h
    exact Int.cast_eq_zero.mp hCast

end

end Birch
