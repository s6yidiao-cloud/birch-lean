import Birch.AffineTranscendence
import Birch.HessianCoordinateRing

/-! # Every irreducible component of a homogeneous cone contains the origin -/

open MvPolynomial
open scoped BigOperators

namespace Birch

private theorem eval₂_mul_coords {ι K R : Type*} [Fintype ι] [CommRing K] [CommRing R]
    {G : MvPolynomial ι K} {d : ℕ} (hG : G.IsHomogeneous d)
    (f : K →+* R) (c : R) (x : ι → R) :
    eval₂ f (fun i => c*x i) G = c^d * eval₂ f x G := by
  classical
  simp only [eval₂_eq', mul_pow, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, Finsupp.degree_apply,
    ← hG.degree_eq_sum_deg_support hs]
  ring

set_option maxHeartbeats 600000 in
/-- In the spectrum of a polynomial ring, every minimal prime over a
homogeneously generated ideal lies under the origin. The proof scales the
coordinates by one polynomial indeterminate and evaluates at `1` and at `0`. -/
theorem minimalPrime_le_coneOrigin {K ι σ : Type*} [Field K] [Fintype ι]
    (f : σ → MvPolynomial ι K) (d : σ → ℕ) (hf : ∀ j, (f j).IsHomogeneous (d j))
    {Q : Ideal (MvPolynomial ι K)} (hQ : (Ideal.span (Set.range f)).IsMinimalPrime Q) :
    Q ≤ RingHom.ker (eval₂Hom (RingHom.id K) (0 : ι → K)) := by
  let R := MvPolynomial ι K
  letI : Q.IsPrime := hQ.isPrime
  let q := Ideal.Quotient.mk Q
  let Cq : K →+* R ⧸ Q := q.comp C
  let ψ : R →+* Polynomial (R ⧸ Q) := eval₂Hom (Polynomial.C.comp Cq)
    (fun i => Polynomial.X * Polynomial.C (q (X i)))
  have hconst (g : R) : eval₂ (Polynomial.C.comp Cq) (fun i => Polynomial.C (q (X i))) g =
      Polynomial.C (q g) := by
    have h : eval₂Hom (Polynomial.C.comp Cq) (fun i => Polynomial.C (q (X i))) =
        Polynomial.C.comp q := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [Cq]
      · intro i
        simp
    exact DFunLike.congr_fun h g
  have hI : Ideal.span (Set.range f) ≤ RingHom.ker ψ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    apply RingHom.mem_ker.mpr
    change eval₂ _ (fun i => Polynomial.X * Polynomial.C (q (X i))) (f j) = 0
    rw [eval₂_mul_coords (hf j) (Polynomial.C.comp Cq) Polynomial.X
        (fun i => Polynomial.C (q (X i))), hconst, Ideal.Quotient.eq_zero_iff_mem.mpr
      (hQ.le (Ideal.subset_span (Set.mem_range_self j))), map_zero, mul_zero]
  let e₀ : R →+* K := eval₂Hom (RingHom.id K) (0 : ι → K)
  have h1 : (Polynomial.evalRingHom (1 : R ⧸ Q)).comp ψ = q := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [ψ, Cq]
  have h0 : (Polynomial.evalRingHom (0 : R ⧸ Q)).comp ψ = Cq.comp e₀ := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [ψ, Cq, e₀]
  have hker : RingHom.ker ψ ≤ Q := by
    intro g hg
    have h := DFunLike.congr_fun h1 g
    rw [RingHom.comp_apply, RingHom.mem_ker.mp hg, map_zero] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h.symm
  have heq : Q ≤ RingHom.ker ψ := hQ.2 ⟨RingHom.ker_isPrime ψ, hI⟩ hker
  intro g hg
  have h := DFunLike.congr_fun h0 g
  rw [RingHom.comp_apply, RingHom.mem_ker.mp (heq hg), map_zero, RingHom.comp_apply] at h
  exact RingHom.mem_ker.mpr (Cq.injective (h.symm.trans (map_zero Cq).symm))

/-- The Hessian incidence is a homogeneous cone, so every one of its
irreducible components contains the origin on the diagonal. -/
theorem hessianIncidence_minimalPrime_le_origin {K : Type*} [Field K] {n e : ℕ}
    {G : MvPolynomial (Fin n) K} (hG : G.IsHomogeneous e) (he : 2 ≤ e)
    {Q : Ideal (MvPolynomial (Fin n ⊕ Fin n) K)} (hQ : (hessianIncidenceIdeal G).IsMinimalPrime Q) :
    Q ≤ RingHom.ker (eval₂Hom (RingHom.id K) (0 : Fin n ⊕ Fin n → K)) := by
  apply minimalPrime_le_coneOrigin (hessianIncidenceEquation G) (fun _ => e-1) _ hQ
  intro i
  unfold hessianIncidenceEquation
  apply IsHomogeneous.sum
  intro j _
  have hh : (pderiv j (pderiv i G)).IsHomogeneous (e-1-1) := hG.pderiv.pderiv
  have hh' := (isHomogeneous_X (R := K) (Sum.inr j)).mul (hh.rename_isHomogeneous (f := Sum.inl))
  simpa only [show 1+(e-1-1) = e-1 by omega] using hh'

/-- The Hessian incidence has dimension at most the gradient dimension plus
the number of variables, the diagonal dimension estimate of Browning–Heath-Brown. -/
theorem ringKrullDim_hessianIncidence_le {K : Type*} [Field K] {n e : ℕ}
    {G : MvPolynomial (Fin n) K} (hG : G.IsHomogeneous e) (he : 2 ≤ e)
    (hchar : ((e-1 : ℕ) : K) ≠ 0) :
    ringKrullDim (MvPolynomial (Fin n ⊕ Fin n) K ⧸ hessianIncidenceIdeal G) ≤
      ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i => pderiv i G)) + n := by
  let R := MvPolynomial (Fin n ⊕ Fin n) K
  let I := hessianIncidenceIdeal G
  let π := Ideal.Quotient.mk I
  let ev : R →+* K := eval₂Hom (RingHom.id K) (0 : Fin n ⊕ Fin n → K)
  have hX (j : Fin n ⊕ Fin n) : ev (X j) = 0 := by
    change eval₂ (RingHom.id K) (0 : Fin n ⊕ Fin n → K) (X j) = 0
    exact eval₂_X (f := RingHom.id K) (g := (0 : Fin n ⊕ Fin n → K)) j
  have heI : I ≤ RingHom.ker ev := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    apply RingHom.mem_ker.mpr
    simp only [hessianIncidenceEquation, map_sum, map_mul, hX, zero_mul, Finset.sum_const_zero]
  let e₀ : R ⧸ I →+* K := Ideal.Quotient.lift I ev heI
  let m := RingHom.ker e₀
  have hs : Function.Surjective e₀ := fun c => ⟨π (C c), by simp [e₀, π, ev]⟩
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective e₀ hs
  have hdiag (j : Fin n) : π (X (Sum.inl j) - X (Sum.inr j)) ∈ m := by
    apply RingHom.mem_ker.mpr
    simp [e₀, π, ev]
  have hmin (q : Ideal (R ⧸ I)) (hq : q ∈ minimalPrimes (R ⧸ I)) : q ≤ m := by
    have hQ := Ideal.minimalPrimes_comap_of_surjective (f := π) Ideal.Quotient.mk_surjective hq
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hQ
    have hp := hessianIncidence_minimalPrime_le_origin hG he hQ
    intro y hy
    obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective y
    exact RingHom.mem_ker.mpr (RingHom.mem_ker.mp (hp hy))
  exact (ringKrullDim_le_height_of_affine_components (K := K) m hmin).trans
    (hessianIncidence_height_le_on_diagonal hG hchar m hdiag)

end Birch
