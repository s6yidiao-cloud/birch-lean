import Birch.DeligneFiniteField

/-! # The one-dimensional prime-field sum interface -/

namespace Birch

private theorem natDegree_uniqueAlgEquiv_eq_totalDegree {σ R : Type*} [CommRing R] [Unique σ]
    (g : MvPolynomial σ R) :
    (MvPolynomial.uniqueAlgEquiv R σ g).natDegree = g.totalDegree := by
  classical
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    change g.totalDegree < (Finsupp.single (default : σ) n).degree
    simpa only [Finsupp.degree_single] using hn
  · unfold MvPolynomial.totalDegree
    apply Finset.sup_le
    intro m hm
    have hq : (MvPolynomial.uniqueAlgEquiv R σ g).coeff (m default) ≠ 0 := by
      rw [MvPolynomial.coeff_uniqueAlgEquiv, ← Finsupp.unique_single m]
      exact MvPolynomial.mem_support_iff.mp hm
    have hm' : m.degree = m default := by
      conv_lhs => rw [Finsupp.unique_single m]
      simp
    change m.degree ≤ _
    rw [hm']
    exact Polynomial.le_natDegree_of_ne_zero hq

/-- Transfer a univariate estimate to the one-dimensional multivariate interface. -/
theorem primeExponentialSumBoundAtDimension_one_of_univariate {r : ℕ}
    (hr : 2 ≤ r)
    (hUnivariate : ∀ (p : ℕ) [Fact p.Prime] [NeZero p], ∀ (f : Polynomial (ZMod p)),
      0 < f.natDegree → f.natDegree < p →
        ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤
          ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p) :
    PrimeExponentialSumBoundAtDimension r 1 ((r : ℝ)-1) := by
  intro p _ _ _ hrp g hg hcrit
  let q := MvPolynomial.uniqueAlgEquiv (ZMod p) (Fin 1) g
  have hd : q.natDegree = r := (natDegree_uniqueAlgEquiv_eq_totalDegree g).trans
    (totalDegree_eq_of_primeIsolatedLeadingCriticalPoint (by decide) g hg hcrit)
  have hsum : primeDeligneSum p g = ∑ x : ZMod p, ZMod.stdAddChar (q.eval x) := by
    unfold primeDeligneSum
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod p)) _ _ (fun x => ?_)
    apply congrArg ZMod.stdAddChar
    simpa only [q, Equiv.funUnique_apply, MvPolynomial.eval₂_id, Polynomial.eval₂_id] using
      (MvPolynomial.eval₂_uniqueAlgEquiv (f := g) (φ := RingHom.id (ZMod p)) (a := x)).symm
  rw [hsum]
  have h := hUnivariate p q (hd.symm ▸ (by omega : 0 < r)) (hd.symm ▸ hrp)
  simpa only [hd, Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one, pow_one,
    Real.sqrt_eq_rpow] using h

end Birch
