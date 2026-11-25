module

public import Birch.RelativeSmoothPencil
public import Birch.FermatModel
public import Birch.ProjectiveJacobianCriterion

@[expose] public section

/-! # A smooth proper pencil from a hypersurface to the Fermat hypersurface -/

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

/-- A Jacobian-certified hypersurface can be joined to the Fermat
hypersurface by a smooth proper pencil in characteristic prime to the
degree. Both endpoints are identified by scheme pullback over the field. -/
theorem exists_smoothProperFermatPencil {k : Type} [Field k] {N d : ℕ}
    {G : MvPolynomial (Fin (N+2)) k} (hd : (d : k) ≠ 0) (hG : G.IsHomogeneous d)
    (hjac : ∀ j : Fin (N+2), ∃ e : ℕ, X j ^ e ∈
      Ideal.span (insert G (Set.range fun i : Fin (N+2) => pderiv i G))) :
    ∃ (h : Polynomial k) (h₀ : h.eval 0 ≠ 0) (h₁ : h.eval 1 ≠ 0),
      IsDomain (Localization.Away h) ∧
      ∃ hp : (localizedProjectivePolynomialPencil G (fermatPolynomial k N d) h).IsHomogeneous d,
        let f := projectiveHypersurfaceToField hp
        let hF := isHomogeneous_fermatPolynomial k N d
        let e₀ := pencilParameterSpecialization (RingHom.id k) h 0 h₀
        let e₁ := pencilParameterSpecialization (RingHom.id k) h 1 h₁
        IsProper f ∧ SmoothOfRelativeDimension N f ∧
          (∃ j : projectiveHypersurface hG ⟶ projectiveHypersurface hp,
            IsPullback j (projectiveHypersurfaceToField hG) f (Spec.map (CommRingCat.ofHom e₀))) ∧
          (∃ j : projectiveHypersurface hF ⟶ projectiveHypersurface hp,
            IsPullback j (projectiveHypersurfaceToField hF) f (Spec.map (CommRingCat.ofHom e₁))) := by
  let φ := algebraMap k (AlgebraicClosure k)
  let hF := isHomogeneous_fermatPolynomial k N d
  have hd' : (d : AlgebraicClosure k) ≠ 0 := by
    rw [← map_natCast φ]
    intro h
    exact hd (φ.injective (h.trans (map_zero φ).symm))
  have hdpos : 0 < d := by
    by_contra! h
    apply hd
    simp [Nat.eq_zero_of_le_zero h]
  have H := exists_smoothProperProjectivePencil hdpos hG hF
    (eq_zero_of_projectiveJacobianCertificate φ hd' hG hjac)
    (eq_zero_of_projectiveJacobianCertificate φ hd' hF (exists_projectiveJacobianCertificate_fermat N d hd))
  simpa only [Nat.add_sub_cancel] using H

end Birch
