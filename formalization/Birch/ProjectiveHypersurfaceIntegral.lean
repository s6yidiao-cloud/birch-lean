module

public import Birch.ProjectiveSmoothIntegral
public import Birch.ProjectiveJacobianCertificate
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

/-! # Integral projective hypersurfaces from Jacobian certificates -/

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped BigOperators

namespace Birch

noncomputable section

universe u

/-- Nonzero homogeneous levels meet the geometric integrality hypothesis
of the smooth proper Weil theorem. -/
theorem geometricallyIntegral_deligneLevelClosureFin {n p d : ℕ}
    [Fact p.Prime] (hn : 2 ≤ n) (hd : 2 ≤ d) (hdp : d < p) {g : MvPolynomial (Fin n) (ZMod p)}
    (hg : g.IsHomogeneous d) (hcrit : PrimeIsolatedLeadingCriticalPoint p d g)
    {t : ZMod p} (ht : t ≠ 0) :
    GeometricallyIntegral (projectiveHypersurfaceToField (isHomogeneous_deligneLevelClosureFin d g t)) := by
  have hdk : (d : ZMod p) ≠ 0 := by
    intro h
    exact hdp.not_ge (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff (ZMod p) p d).mp h))
  exact geometricallyIntegral_projectiveHypersurfaceToField (by omega) hd hdk
    (isHomogeneous_deligneLevelClosureFin d g t)
    (exists_deligneLevelClosureFin_jacobianCertificate_of_homogeneous (by omega) hdp hg hcrit ht)

end
end Birch
