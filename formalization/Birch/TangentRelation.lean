import Birch.AffineTranscendence
import Birch.HyperplaneRestriction

/-! # Algebraic relation for the normals to a homogeneous hypersurface -/

open MvPolynomial
open scoped BigOperators Cardinal nonZeroDivisors

namespace Birch

noncomputable section

private theorem dimension_hypersurface_le {n : ℕ} {K : Type} [Field K]
    {G : MvPolynomial (Fin (n+1)) K} (hG : G ≠ 0) :
    ringKrullDim (MvPolynomial (Fin (n+1)) K ⧸ Ideal.span {G}) ≤ (n : WithBot ℕ∞) := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_iff_ne_zero.mpr hG)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K,
    zero_add, Nat.card_fin] at h
  by_contra! h_bad
  have h₁ := ENat.WithBot.add_one_le_iff.mpr h_bad
  have h₂ := (add_le_add h₁ (le_rfl (a := (1 : WithBot ℕ∞)))).trans h
  have h₃ : (n+1)+1 ≤ n+1 := by exact_mod_cast h₂
  omega

private theorem exists_relation_mod_prime {n : ℕ} {K : Type} [Field K]
    {G : MvPolynomial (Fin (n+1)) K} (hG : G ≠ 0)
    (P : Ideal (MvPolynomial (Fin (n+1)) K)) [P.IsPrime] (hP : G ∈ P) :
    ∃ T : MvPolynomial (Fin (n+1)) K, T ≠ 0 ∧ aeval (fun i => pderiv i G) T ∈ P := by
  let R := MvPolynomial (Fin (n+1)) K
  let J : Ideal R := Ideal.span {G}
  let A := R ⧸ P
  let π : R →ₐ[K] A := Ideal.Quotient.mkₐ K P
  let grad : Fin (n+1) → A := fun i => π (pderiv i G)
  have hJP : J ≤ P := by
    apply Ideal.span_le.mpr
    intro f hf
    rwa [Set.mem_singleton_iff.mp hf]
  let q : R ⧸ J →+* A := Ideal.Quotient.factor hJP
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective hJP
  have hA : ringKrullDim A ≤ (n : WithBot ℕ∞) :=
    (ringKrullDim_le_of_surjective q hq).trans (dimension_hypersurface_le hG)
  obtain ⟨s,hs,_,hb⟩ := exists_affine_transcendence_basis (K := K) (A := A)
  have hsn : s ≤ n := by exact_mod_cast hs.trans hA
  have hdep : ¬ AlgebraicIndependent K grad := by
    intro hi
    have H := hi.cardinalMk_le_trdeg
    rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fin, Cardinal.mk_fin] at H
    have hn : n + 1 ≤ s := by exact_mod_cast H
    omega
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨T,hT,hT₀⟩ := hdep
  refine ⟨T,hT₀,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change π (aeval (fun i => pderiv i G) T) = 0
  rwa [comp_aeval_apply]

private theorem exists_tangent_relation {n : ℕ} {K : Type} [Field K]
    {G : MvPolynomial (Fin (n+1)) K} (hG : G ≠ 0) :
    ∃ T : MvPolynomial (Fin (n+1)) K, T ≠ 0 ∧
      ∀ y : Fin (n+1) → K, G.eval y = 0 → T.eval (fun i => (pderiv i G).eval y) = 0 := by
  classical
  let J : Ideal (MvPolynomial (Fin (n+1)) K) := Ideal.span {G}
  letI : Fintype J.minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ J).fintype
  have ht (P : J.minimalPrimes) :
      ∃ T : MvPolynomial (Fin (n+1)) K, T ≠ 0 ∧ aeval (fun i => pderiv i G) T ∈ P.val := by
    letI : P.val.IsPrime := P.prop.1.1
    exact exists_relation_mod_prime hG P.val (P.prop.1.2 (Ideal.subset_span (Set.mem_singleton G)))
  choose V hV hgrad using ht
  let T := ∏ P : J.minimalPrimes, V P
  refine ⟨T,Finset.prod_ne_zero_iff.mpr (fun P _ => hV P),?_⟩
  intro y hy
  let M : Ideal (MvPolynomial (Fin (n+1)) K) := vanishingIdeal K {y}
  have hJ : J ≤ M := by
    apply Ideal.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact (mem_vanishingIdeal_singleton_iff y G).mpr (by simpa only [aeval_eq_eval] using hy)
  obtain ⟨P,hP,hPM⟩ := Ideal.exists_minimalPrimes_le (I := J) (J := M) hJ
  let p : J.minimalPrimes := ⟨P,hP⟩
  have hz := (mem_vanishingIdeal_singleton_iff y _).mp (hPM (hgrad p))
  rw [comp_aeval_apply (fun i : Fin (n+1) => pderiv i G) (aeval y)] at hz
  simp only [aeval_eq_eval] at hz
  change (eval (fun i => (eval y) ((pderiv i) G))) T = 0
  dsimp only [T]
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ p) hz

private theorem homogeneousComponent_tangent_relation {n r : ℕ} {K : Type}
    [Field K] [IsAlgClosed K] [Infinite K] {G : MvPolynomial (Fin (n+1)) K} (hG : G.IsHomogeneous r)
    (hr : 2 ≤ r) {T : MvPolynomial (Fin (n+1)) K}
    (hT : ∀ y : Fin (n+1) → K, G.eval y = 0 → T.eval (fun i => (pderiv i G).eval y) = 0)
    (j : ℕ) (hj : j ≤ T.totalDegree) (y : Fin (n+1) → K) (hy : G.eval y = 0) :
    (homogeneousComponent j T).eval (fun i => (pderiv i G).eval y) = 0 := by
  let v := fun i : Fin (n+1) => (pderiv i G).eval y
  have hv (t : K) : T.eval (fun i => t * v i) = 0 := by
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq t (by omega : 0 < r-1)
    have hz := hT (fun i => u * y i) (by rw [eval_homogeneous_scale hG, hy, mul_zero])
    simpa only [eval_homogeneous_scale hG.pderiv, hu, v] using hz
  let Q : Polynomial K := ∑ i ∈ Finset.range (T.totalDegree+1),
    Polynomial.C ((homogeneousComponent i T).eval v) * Polynomial.X^i
  have hQeval (t : K) : Q.eval t = 0 := by
    have h := hv t
    conv_lhs at h => rw [← sum_homogeneousComponent T]
    simp only [map_sum] at h
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [eval_homogeneous_scale (homogeneousComponent_isHomogeneous i T), mul_comm]
  have hQ : Q = 0 := Polynomial.zero_of_eval_zero _ hQeval
  have hcoeff : Q.coeff j = (homogeneousComponent j T).eval v := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
  rw [hQ, Polynomial.coeff_zero] at hcoeff
  exact hcoeff.symm

/-- The gradient normals at the zeros of a homogeneous polynomial satisfy
a nonzero homogeneous relation over its algebraically closed coefficient field. -/
theorem exists_homogeneous_tangent_relation {n r : ℕ} {K : Type}
    [Field K] [IsAlgClosed K] [Infinite K] {G : MvPolynomial (Fin (n+1)) K}
    (hG : G.IsHomogeneous r) (hr : 2 ≤ r) :
    ∃ e : ℕ, ∃ T : MvPolynomial (Fin (n+1)) K, T.IsHomogeneous e ∧ T ≠ 0 ∧
      ∀ y : Fin (n+1) → K, G.eval y = 0 → T.eval (fun i => (pderiv i G).eval y) = 0 := by
  classical
  by_cases hG₀ : G = 0
  · refine ⟨1,X 0,isHomogeneous_X (R := K) 0,X_ne_zero _,?_⟩
    simp [hG₀]
  obtain ⟨T,hT,hv⟩ := exists_tangent_relation hG₀
  obtain ⟨j,hj,hj₀⟩ : ∃ j ≤ T.totalDegree, homogeneousComponent j T ≠ 0 := by
    by_contra! hn
    apply hT
    rw [← sum_homogeneousComponent T]
    apply Finset.sum_eq_zero
    intro j h
    exact hn j (Nat.le_of_lt_succ (Finset.mem_range.mp h))
  exact ⟨j, _, homogeneousComponent_isHomogeneous _ _, hj₀,
    homogeneousComponent_tangent_relation hG hr hv j hj⟩

end
end Birch
