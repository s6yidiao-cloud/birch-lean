module

public import Birch.ProjectiveHypersurfaceComplementGeometry
public import Birch.ProjectiveExtensionPoints
public import Birch.ProjectiveWeilPointCount

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace Birch

noncomputable section

universe u

variable {σ K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem natCard_linearCoordinateHyperplanePoints [Fintype σ] [Finite K] :
    Nat.card (projectiveHypersurfacePoints (X (R := K) (none : Option σ))) =
      Nat.card (ℙ K (σ → K)) := by
  let g : MvPolynomial σ K := 0
  have hG : deligneLevelClosure 1 g (-1) = X none := by
    rw [deligneLevelClosure_of_homogeneous (show g.IsHomogeneous 1 from isHomogeneous_zero σ K 1)]
    simp [g]
  let : IsEmpty {x : σ → K // g.eval x = -1} := ⟨fun x => by simpa [g] using x.property⟩
  let : Finite (projectiveHypersurfacePoints (homogeneousComponent 1 g)) :=
    inferInstanceAs (Finite {P : ℙ K (σ → K) // _})
  have hTop : homogeneousComponent 1 g = 0 := map_zero _
  rw [← hG, Nat.card_congr (deligneLevelClosure_points_equiv (by decide)
    (show g.totalDegree ≤ 1 by simp [g]) (-1)), Nat.card_sum, hTop]
  rw [Nat.card_of_isEmpty, zero_add]
  exact Nat.card_congr (Equiv.subtypeUnivEquiv fun x : ℙ K (σ → K) => map_zero (eval x.rep))

/-- Scheme-valued extension points of the ambient projective space have the
classical exact count, expressed in the convention of the Weil theorem. -/
theorem natCard_overHom_projectivePolynomialSpace {k L : Type} [Field k] [Field L] [Algebra k L] [Finite L]
    (N : ℕ) :
    Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
      Over.mk (projectivePolynomialSpaceToField (Fin (N+1)) k)) =
        projectiveSpacePointCount (Nat.card L) N := by
  let σ := Fin (N+1)
  let hX := isHomogeneous_X k (none : Option σ)
  let e : Over.mk (projectivePolynomialSpaceToField σ k) ≅ Over.mk (projectiveHypersurfaceToField hX) :=
    Over.isoMk (projectivePolynomialSpaceLinearHyperplaneIso σ k)
      (projectivePolynomialSpaceLinearHyperplaneIso_hom_toField σ k)
  rw [Nat.card_congr ((Iso.refl _).homCongr e),
    Nat.card_congr (overHomEquivProjectiveHypersurfacePoints (K := L) (by decide) hX), map_X,
    natCard_linearCoordinateHyperplanePoints, Projectivization.card_of_finrank L _
      (n := N+1) (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]),
    projectiveSpacePointCount, Nat.range_succ_eq_Iic]

end

end Birch
