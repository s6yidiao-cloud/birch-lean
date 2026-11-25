module

public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

/-- The pre-4.35 argument order for coefficient extraction. -/
abbrev MvPolynomial.coeff {σ R : Type*} [CommSemiring R]
    (d : σ →₀ ℕ) (p : MvPolynomial σ R) : R := AddMonoidAlgebra.coeff p d
