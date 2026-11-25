module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-!
# Forms, nonsingular zeros, and the dimension threshold

All polynomial evaluations below use the canonical integer coefficient map. The smoothness
condition is the projective Jacobian criterion for a nonzero homogeneous hypersurface.
-/

namespace Birch

abbrev IntForm (n : ℕ) := MvPolynomial (Fin n) ℤ

/-- Evaluate an integral polynomial after mapping its coefficients into the target ring. -/
noncomputable def evalForm {n : ℕ} {R : Type*} [CommRing R]
    (F : IntForm n) (x : Fin n → R) : R :=
  F.eval₂ (Int.castRingHom R) x

/-- There is a zero whose coordinate vector is nonzero. -/
def HasNonzeroZero {n : ℕ} (F : IntForm n) (R : Type*) [CommRing R] : Prop :=
  ∃ x : Fin n → R, x ≠ 0 ∧ evalForm F x = 0

/-- A zero at which at least one partial derivative is nonzero. -/
def HasNonsingularZero {n : ℕ} (F : IntForm n) (R : Type*) [CommRing R] : Prop :=
  ∃ x : Fin n → R, evalForm F x = 0 ∧
    ∃ i : Fin n, evalForm (MvPolynomial.pderiv i F) x ≠ 0

/-- Nonsingular local zeros imply a nonsingular rational zero. -/
def SmoothHassePrinciple {n : ℕ} (F : IntForm n) : Prop :=
  (HasNonsingularZero F ℝ ∧ ∀ (p : ℕ) [Fact p.Prime], HasNonsingularZero F ℚ_[p]) →
    HasNonsingularZero F ℚ

/-- Every projective geometric zero has a nonzero partial derivative. -/
def ProjectivelySmooth {n : ℕ} (F : IntForm n) : Prop :=
  ∀ x : Fin n → AlgebraicClosure ℚ, x ≠ 0 → evalForm F x = 0 →
    ∃ i : Fin n, evalForm (MvPolynomial.pderiv i F) x ≠ 0

/-- Nonzero local zeros at the real place and at every finite prime of `ℚ`. -/
def EverywhereLocallySoluble {n : ℕ} (F : IntForm n) : Prop :=
  HasNonzeroZero F ℝ ∧ ∀ p : ℕ, ∀ _ : Fact p.Prime, HasNonzeroZero F ℚ_[p]

/-- Dimension threshold of the main theorem. -/
def dimensionThreshold (d : ℕ) : ℕ := 2 ^ (d + 1) - 4

end Birch
