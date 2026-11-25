module

public import Birch.DeligneCriticalLocus
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

open MvPolynomial

namespace Birch

/-- The leading homogeneous part has no nonzero critical points over the
algebraic closure of the prime field. -/
def PrimeIsolatedLeadingCriticalPoint {l : ℕ} (p : ℕ) [Fact p.Prime] (r : ℕ)
    (g : MvPolynomial (Fin l) (ZMod p)) : Prop :=
  let K := AlgebraicClosure (ZMod p)
  ∀ x : Fin l → K,
    (∀ i, (pderiv i (homogeneousComponent r g)).eval₂ (algebraMap (ZMod p) K) x = 0) → x = 0

end Birch
