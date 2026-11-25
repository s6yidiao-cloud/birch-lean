import Birch.CompletionConditional
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-! # A dimension-zero gradient cone -/

open MvPolynomial

namespace Birch

noncomputable section

private theorem evalForm_polynomial_C {n : ℕ} {K : Type*} [Field K]
    (G : IntForm n) (x : Fin n → K) :
    evalForm G (fun i => Polynomial.C (x i)) = Polynomial.C (evalForm G x) := by
  unfold evalForm
  rw [eval₂_comp_left]
  congr 1

/-- A nonzero critical point of a homogeneous polynomial produces a line in
its gradient locus, forcing the gradient quotient to have dimension at least one. -/
theorem one_le_gradientQuotient_dim_of_nonzero_critical {n d : ℕ} {K : Type*} [Field K]
    {G : IntForm n} (hG : G.IsHomogeneous d) {x : Fin n → K}
    (hx : x ≠ 0) (hgrad : ∀ j, evalForm (pderiv j G) x = 0) :
    1 ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span
      (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv j G))) := by
  classical
  let J : Ideal (MvPolynomial (Fin n) K) := Ideal.span
    (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv j G))
  let e : MvPolynomial (Fin n) K →ₐ[K] Polynomial K :=
    aeval (fun i => Polynomial.X * Polynomial.C (x i))
  have hJ : J ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change aeval (fun i => Polynomial.X * Polynomial.C (x i))
      (MvPolynomial.map (Int.castRingHom K) (pderiv j G)) = 0
    rw [aeval_def, eval₂_map]
    have hcast : (algebraMap K (Polynomial K)).comp (Int.castRingHom K) =
        Int.castRingHom (Polynomial K) := by
      ext a
      simp
    rw [hcast, ← evalForm, evalForm_scale hG.pderiv, evalForm_polynomial_C, hgrad, map_zero,
      mul_zero]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  let g : Polynomial K →ₐ[K] MvPolynomial (Fin n) K :=
    Polynomial.aeval (C (x i)⁻¹ * X i)
  have hcomp : e.comp g = AlgHom.id K (Polynomial K) := by
    apply Polynomial.algHom_ext
    simp only [e, g, AlgHom.comp_apply, Polynomial.aeval_X, map_mul, aeval_C, aeval_X,
      Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply, AlgHom.id_apply]
    rw [mul_left_comm, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]
  have he : Function.Surjective e :=
    fun p => ⟨g p, DFunLike.congr_fun hcomp p⟩
  let f := Ideal.Quotient.lift J e.toRingHom hJ
  have hf : Function.Surjective f := Ideal.Quotient.lift_surjective_of_surjective J hJ he
  have hP : 1 ≤ ringKrullDim (Polynomial K) := by
    have h := ringKrullDim_succ_le_ringKrullDim_polynomial (R := K)
    rwa [ringKrullDim_eq_zero_of_field K, zero_add] at h
  exact hP.trans (ringKrullDim_le_of_surjective f hf)

/-- A homogeneous gradient cone of dimension zero has no nonzero critical
point over the algebraic closure of the prime field. -/
theorem critical_eq_zero_of_primeGradientDimension_zero {n d p : ℕ} (hp : p.Prime)
    {G : IntForm n} (hG : G.IsHomogeneous d) (hdim : PrimeGradientDimension p hp G 0) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ x : Fin n → AlgebraicClosure (ZMod p), (∀ j, evalForm (pderiv j G) x = 0) → x = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  intro x hgrad
  by_contra hx
  have h := one_le_gradientQuotient_dim_of_nonzero_critical hG hx hgrad
  unfold PrimeGradientDimension at hdim
  simp only [Nat.cast_zero] at hdim
  rw [hdim] at h
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) h

end
end Birch
