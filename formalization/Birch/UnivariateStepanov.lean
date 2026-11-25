import Birch.UnivariateStepanovReduction
import Birch.UnivariatePrimeBound
import StacksFrontier.RingTheory.Polynomial.StepanovBound

/-! # Univariate Deligne bounds from the affine Stepanov bound -/

open scoped BigOperators

namespace Birch

/-- The pinned affine Stepanov result supplies the uniform lower point bound. -/
theorem affinePlanePointCountLowerBound_of_stepanov (d : ℕ) :
    AffinePlanePointCountLowerBound d :=
  MvPolynomial.exists_card_zeroSet_ge_of_absolutelyIrreducible.{0} d

/-- The sharp prime-field additive bound for one-variable polynomials of
positive degree less than the characteristic. -/
theorem norm_univariate_characterSum_le_of_stepanov {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : Polynomial (ZMod p)) (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    {a : ZMod p} (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p :=
  norm_univariate_characterSum_le_of_affinePlaneLowerBound
    (affinePlanePointCountLowerBound_of_stepanov p) f hr hp ha

/-- The one-dimensional prime Deligne bound, including arbitrary lower terms. -/
theorem primeExponentialSumBoundAtDimension_one_of_stepanov {r : ℕ} (hr : 2 ≤ r) :
    PrimeExponentialSumBoundAtDimension r 1 ((r : ℝ)-1) := by
  apply primeExponentialSumBoundAtDimension_one_of_univariate hr
  intro p _ _ f h₁ h₂
  simpa only [one_mul] using norm_univariate_characterSum_le_of_stepanov f h₁ h₂
    (show (1 : ZMod p) ≠ 0 from one_ne_zero)

/-- A zero-dimensional twisted sum is bounded by one. -/
theorem uniformTwistedPrimeBound_zero {r : ℕ} (hr : 2 ≤ r) :
    UniformTwistedPrimeBound r 0 := by
  have h : PrimeExponentialSumBoundAtDimension r 0 1 := by
    intro _ _ _ hdim
    omega
  refine ⟨1, one_pos, ?_⟩
  simpa only [pow_zero] using twistedCompleteSum_le_of_primeExponentialSumBoundAtDimension hr h

/-- The resulting normalized Fourier-twisted bound for terminal dimension one. -/
theorem uniformTwistedPrimeBound_one_of_stepanov {r : ℕ} (hr : 2 ≤ r) :
    UniformTwistedPrimeBound r 1 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  exact ⟨((r : ℝ)-1)^1, pow_pos (by linarith) _,
    twistedCompleteSum_le_of_primeExponentialSumBoundAtDimension hr
      (primeExponentialSumBoundAtDimension_one_of_stepanov hr)⟩

private theorem stdAddChar_finset_sum {p : ℕ} [NeZero p] {ι : Type*}
    (s : Finset ι) (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

/-- A simultaneous bijective change of coordinates preserves the exact
factorization of an additive character sum with separated phase. -/
theorem separatedPrimeCharacterSum_eq_prod {l p : ℕ} [NeZero p]
    (e : (Fin l → ZMod p) ≃ (Fin l → ZMod p)) (f : Fin l → Polynomial (ZMod p))
    (a c : ZMod p) :
    (∑ x : Fin l → ZMod p, ZMod.stdAddChar (c + a * ∑ i, (f i).eval (e x i))) =
      ZMod.stdAddChar c * ∏ i, ∑ t : ZMod p, ZMod.stdAddChar (a * (f i).eval t) := by
  calc
    _ = ∑ x : Fin l → ZMod p, ZMod.stdAddChar (c + a * ∑ i, (f i).eval (x i)) :=
      Equiv.sum_comp e _
    _ = _ := by
      simp_rw [AddChar.map_add_eq_mul, Finset.mul_sum, stdAddChar_finset_sum]
      rw [← Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum (κ := fun _ : Fin l => ZMod p)
        (fun i t => ZMod.stdAddChar (a * (f i).eval t))).symm

/-- The sharp square-root estimate for degrees at least one below the
characteristic, with arbitrary lower terms in the separated coordinates. -/
theorem norm_separatedPrimeCharacterSum_le_of_stepanov {l p : ℕ}
    [Fact p.Prime] [NeZero p]
    (e : (Fin l → ZMod p) ≃ (Fin l → ZMod p)) (f : Fin l → Polynomial (ZMod p))
    (hdeg₀ : ∀ i, 0 < (f i).natDegree) (hdeg₁ : ∀ i, (f i).natDegree < p)
    {a : ZMod p} (ha : a ≠ 0) (c : ZMod p) :
    ‖∑ x : Fin l → ZMod p, ZMod.stdAddChar (c + a * ∑ i, (f i).eval (e x i))‖ ≤
      (∏ i, (((f i).natDegree - 1 : ℕ) : ℝ)) * (p : ℝ) ^ ((l : ℝ)/2) := by
  rw [separatedPrimeCharacterSum_eq_prod e f a c, norm_mul, AddChar.norm_apply, one_mul, norm_prod]
  calc
    _ ≤ ∏ i, (((f i).natDegree - 1 : ℕ) : ℝ) * Real.sqrt (p : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => norm_univariate_characterSum_le_of_stepanov (f i) (hdeg₀ i) (hdeg₁ i) ha)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      rw [show (1/2 : ℝ) * (l : ℝ) = (l : ℝ) / 2 by ring]

end Birch
