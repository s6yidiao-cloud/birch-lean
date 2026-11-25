module

public import Birch.Statement
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Weighted exponential sums and orthogonality

We represent integration over the circle by Lebesgue integration on the unit interval
`(0,1]`. All the paper's frequency sets and exponential sums are 1-periodic.
-/

open MeasureTheory Set Filter Complex
open scoped BigOperators Topology ContDiff

namespace Birch

noncomputable section

/-- The character exp(2πit) on the real line. -/
def phase (t : ℝ) : ℂ :=
  Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))

/-- The probability measure on the chosen fundamental domain of the circle. -/
def circleMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure circleMeasure := by
  constructor
  simp [circleMeasure, Real.volume_Ioc]

/-- The integer points of the closed box of radius `P`. -/
def latticeBox (n : ℕ) (P : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ ↦ Finset.Icc (-⌊P⌋) ⌊P⌋)

/-- The scaled lattice coordinates at which the weight is evaluated. -/
def scaledPoint {n : ℕ} (P : ℝ) (x : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ (x i : ℝ) / P

/-- The lattice exponential sum from the introduction. -/
def exponentialSum {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (P α : ℝ) : ℂ :=
  ∑ x ∈ latticeBox n P, (w (scaledPoint P x) : ℂ) * phase (α * ((evalForm F x : ℤ) : ℝ))

/-- The weighted number of lattice zeros. -/
def weightedZeros {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (P : ℝ) : ℝ :=
  ∑ x ∈ latticeBox n P, if evalForm F x = 0 then w (scaledPoint P x) else 0

/-- The admissible weights chosen near a transverse real zero in the introduction. -/
structure TransverseWeight {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  nonnegative : ∀ x, 0 ≤ w x
  bounded : ∀ x, w x ≤ 1
  support_box : tsupport w ⊆ {x | ∀ i, |x i| < 1}
  support_avoids_origin : (0 : Fin n → ℝ) ∉ tsupport w
  positive_at_zero : ∃ x, evalForm F x = 0 ∧ 0 < w x
  transverse : ∃ i : Fin n, ∃ c : ℝ, 0 < c ∧
    ∀ x ∈ tsupport w, c ≤ |evalForm (MvPolynomial.pderiv i F) x|

/-- The major arcs, represented as a periodic subset of the real line. -/
def majorArcs (d : ℕ) (P : ℝ) : Set ℝ :=
  {α | ∃ (q : ℕ) (a : ℤ), 0 < q ∧ (q : ℝ) ≤ P ^ (1 / 2 : ℝ) ∧
    a.natAbs.Coprime q ∧ |α - (a : ℝ) / q| ≤ P ^ (-(d : ℝ) + 7 / 8) / q}

theorem measurableSet_majorArcs (d : ℕ) (P : ℝ) :
    MeasurableSet (majorArcs d P) := by
  classical
  let A (q : ℕ) (a : ℤ) : Set ℝ :=
    if 0 < q ∧ (q : ℝ) ≤ P ^ (1 / 2 : ℝ) ∧ a.natAbs.Coprime q then
      {α | |α - (a : ℝ) / q| ≤ P ^ (-(d : ℝ) + 7 / 8) / q}
    else ∅
  have hA : majorArcs d P = ⋃ (q : ℕ) (a : ℤ), A q a := by
    ext α
    simp only [majorArcs, Set.mem_ofPred_eq, mem_iUnion]
    refine exists_congr fun q ↦ exists_congr fun a ↦ ?_
    by_cases h : 0 < q ∧ (q : ℝ) ≤ P ^ (1 / 2 : ℝ) ∧ a.natAbs.Coprime q
    · simp only [A, ite_eq_left h, Set.mem_ofPred_eq]
      exact ⟨fun hh ↦ hh.2.2.2, fun hh ↦ ⟨h.1, h.2.1, h.2.2, hh⟩⟩
    · simp only [A, ite_eq_right h, notMem_empty, iff_false]
      exact fun hh ↦ h ⟨hh.1, hh.2.1, hh.2.2.1⟩
  rw [hA]
  refine MeasurableSet.iUnion fun q ↦ MeasurableSet.iUnion fun a ↦ ?_
  dsimp only [A]
  split_ifs
  · exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
  · exact MeasurableSet.empty

theorem continuous_exponentialSum {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (P : ℝ) : Continuous (exponentialSum F w P) := by
  unfold exponentialSum phase
  fun_prop

theorem integrable_exponentialSum {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (P : ℝ) : Integrable (exponentialSum F w P) circleMeasure :=
  (continuous_exponentialSum F w P).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The circle integral of the character of integer frequency `m`. -/
theorem phase_integer_orthogonality (m : ℤ) :
    (∫ α, phase (α * (m : ℝ)) ∂circleMeasure) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp [phase]
  have hcoef : (2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by simp [Real.pi_ne_zero]))
      Complex.I_ne_zero) (by exact_mod_cast hm)
  have hphase (α : ℝ) :
      phase (α * (m : ℝ)) = Complex.exp
        (((2 * (Real.pi : ℂ) * Complex.I) * (m : ℂ)) * (α : ℂ)) := by
    unfold phase
    push_cast
    ring_nf
  simp_rw [ite_eq_right hm, hphase, circleMeasure, ← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_exp_mul_complex hcoef]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) = 1 := by
    rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I), Complex.exp_int_mul_two_pi_mul_I]
  simp [hexp]

/-- Integrating the lattice exponential sum retains exactly the terms with zero phase. -/
theorem integral_exponentialSum_eq_weightedZeros {n : ℕ}
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (P : ℝ) :
    (∫ α, exponentialSum F w P α ∂circleMeasure) = (weightedZeros F w P : ℂ) := by
  classical
  unfold exponentialSum weightedZeros
  rw [integral_finsetSum]
  · push_cast
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul, phase_integer_orthogonality]
    split_ifs <;> simp
  · intro x _
    have h : Continuous (fun α : ℝ ↦ (w (scaledPoint P x) : ℂ) *
        phase (α * ((evalForm F x : ℤ) : ℝ))) := by unfold phase; fun_prop
    exact h.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- A strictly positive weighted count with the origin excluded exhibits a nonzero zero. -/
theorem hasNonzeroZero_of_weightedZeros_pos {n : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hω : TransverseWeight F w) {P : ℝ}
    (hpos : 0 < weightedZeros F w P) : HasNonzeroZero F ℤ := by
  classical
  by_contra! h
  have hsum : weightedZeros F w P = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x = 0
    · subst x
      have hω₀ : w 0 = 0 := by
        by_contra hn
        exact hω.support_avoids_origin (subset_tsupport _ hn)
      have hz : scaledPoint P (0 : Fin n → ℤ) = 0 := by ext i; simp [scaledPoint]
      simp [hz, hω₀]
    · have hFx : evalForm F x ≠ 0 := fun he ↦ h ⟨x, hx, he⟩
      simp [hFx]
  linarith

end
end Birch
