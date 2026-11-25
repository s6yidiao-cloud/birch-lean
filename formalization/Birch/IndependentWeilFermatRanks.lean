module

public import Birch.IndependentWeilFibreRanks
public import Birch.IndependentWeilProjectiveCohomology
public import Birch.PencilParameterGeometricallyIntegral
public import Birch.PencilParameterScheme
public import Birch.RelativeFermatPencil

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace Birch

/-- In characteristic prime to the degree, the smooth proper Fermat pencil
transports the cohomology ranks of an explicit hypersurface to its Fermat model. -/
theorem finrank_projectiveHypersurfaceConstantCohomology_eq_fermat
    {k : Type} [Field k] [Finite k] (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)]
    {N d : ℕ} {G : MvPolynomial (Fin (N+2)) k} (hd : (d : k) ≠ 0)
    (hG : G.IsHomogeneous d)
    (hjac : ∀ j : Fin (N+2), ∃ e : ℕ, X j ^ e ∈
      Ideal.span (insert G (Set.range fun i : Fin (N+2) => pderiv i G))) (i : ℕ) :
    Module.finrank (PadicAlgCl l) (projectiveHypersurfaceConstantCohomology l hG
      (Nat.pos_of_ne_zero (fun hz => hd (by simp [hz]))) i).carrier =
    Module.finrank (PadicAlgCl l) (projectiveHypersurfaceConstantCohomology l
      (isHomogeneous_fermatPolynomial k N d) (Nat.pos_of_ne_zero (fun hz => hd (by simp [hz]))) i).carrier := by
  obtain ⟨h, h0, h1, _, hP, hproper, hsmooth, ⟨j0, hj0⟩, ⟨j1, hj1⟩⟩ :=
    exists_smoothProperFermatPencil hd hG hjac
  let S := Spec (CommRingCat.of k)
  let Y := Spec (CommRingCat.of (Localization.Away h))
  let q : Y ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))
  let X := projectiveHypersurface hP
  let X0 := projectiveHypersurface hG
  let hF := isHomogeneous_fermatPolynomial k N d
  let X1 := projectiveHypersurface hF
  let f : X ⟶ Y := projectiveHypersurfaceToField hP
  let g0 : X0 ⟶ S := projectiveHypersurfaceToField hG
  let g1 : X1 ⟶ S := projectiveHypersurfaceToField hF
  let s0 : S ⟶ Y := Spec.map (CommRingCat.ofHom
    (pencilParameterSpecialization (RingHom.id k) h 0 h0))
  let s1 : S ⟶ Y := Spec.map (CommRingCat.ofHom
    (pencilParameterSpecialization (RingHom.id k) h 1 h1))
  let : Y.Over S := ⟨q⟩
  let : X.Over S := ⟨f ≫ q⟩
  let : X0.Over S := ⟨g0⟩
  let : X1.Over S := ⟨g1⟩
  let : f.IsOver S := ⟨rfl⟩
  let : IsProper f := hproper
  let : SmoothOfRelativeDimension N f := hsmooth
  let : Smooth f := SmoothOfRelativeDimension.smooth N f
  let : LocallyOfFiniteType (Y ↘ S) := locallyOfFiniteType_pencilParameter h
  let : QuasiCompact (Y ↘ S) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))))
  have hh : h ≠ 0 := fun hz => h0 (by simp [hz])
  let : IsIntegral (Y ↘ S).geometricFiber :=
    isIntegral_pencilParameterBaseChange (K := AlgebraicClosure k) hh
  let : IrreducibleSpace (Y ↘ S).geometricFiber := inferInstance
  have hpos : 0 < d := Nat.pos_of_ne_zero (fun hz => hd (by simp [hz]))
  let : IsProper (X0 ↘ S) := isProper_projectiveHypersurfaceToField hG hpos
  let : IsProper (X1 ↘ S) := isProper_projectiveHypersurfaceToField hF hpos
  have hs0 : s0 ≫ q = 𝟙 S := pencilParameterSpecialization_specMap_comp 0 h0
  have hs1 : s1 ≫ q = 𝟙 S := pencilParameterSpecialization_specMap_comp 1 h1
  let : s0.IsOver S := ⟨hs0⟩
  let : s1.IsOver S := ⟨hs1⟩
  change IsPullback j0 g0 f s0 at hj0
  change IsPullback j1 g1 f s1 at hj1
  let : j0.IsOver S := ⟨by
    change j0 ≫ (f ≫ q) = g0
    rw [← Category.assoc, hj0.w, Category.assoc, hs0, Category.comp_id]⟩
  let : j1.IsOver S := ⟨by
    change j1 ≫ (f ≫ q) = g1
    rw [← Category.assoc, hj1.w, Category.assoc, hs1, Category.comp_id]⟩
  exact finrank_constantCohomology_eq_of_smoothProperRationalFibers l f s0 s1 j0 j1 hj0 hj1 i

end Birch
