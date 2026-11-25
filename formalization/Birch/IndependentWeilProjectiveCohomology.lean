module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import Birch.ProjectiveHypersurface

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

/-- The Frobenius module for the constant-coefficient ordinary cohomology of
an explicit projective hypersurface over a finite field. -/
noncomputable def projectiveHypersurfaceConstantCohomology {k : Type} [Field k] [Finite k]
    (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] {m d : ℕ}
    {G : MvPolynomial (Fin m) k} (hG : G.IsHomogeneous d) (hd : 0 < d) (i : ℕ) :
    FrobeniusModule.{1, 0} (PadicAlgCl l) := by
  let S := Spec (CommRingCat.of k)
  let X := projectiveHypersurface hG
  letI : X.Over S := ⟨projectiveHypersurfaceToField hG⟩
  letI : IsProper (X ↘ S) := isProper_projectiveHypersurfaceToField hG hd
  exact (WeilSheaf.adicConstant k l X).cohomology i

end Birch
