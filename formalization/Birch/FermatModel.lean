module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

/-- The diagonal Fermat equation with (N+2) homogeneous variables. -/
def fermatPolynomial (F : Type*) [Field F] (N d : ℕ) : MvPolynomial (Fin (N+2)) F :=
  ∑ i, X i ^ d

theorem isHomogeneous_fermatPolynomial (F : Type*) [Field F] (N d : ℕ) :
    (fermatPolynomial F N d).IsHomogeneous d :=
  IsHomogeneous.sum Finset.univ _ d fun i _ => by
    simpa only [one_mul] using (isHomogeneous_X F i).pow d

@[simp] theorem eval_fermatPolynomial (F : Type*) [Field F] {N d : ℕ} (x : Fin (N+2) → F) :
    (fermatPolynomial F N d).eval x = ∑ i, x i ^ d := by
  simp [fermatPolynomial]

/-- The Fermat equation has the projective Jacobian certificate when
the characteristic does not divide its degree. -/
theorem exists_projectiveJacobianCertificate_fermat {F : Type*} [Field F]
    (N d : ℕ) (hd : (d : F) ≠ 0) :
    let G := fermatPolynomial F N d
    ∀ i : Fin (N+2), ∃ e : ℕ,
      X i ^ e ∈ Ideal.span (insert G (Set.range fun j : Fin (N+2) => pderiv j G)) := by
  intro G i
  have hdiff : pderiv i G = C (d : F) * X i ^ (d-1) := by
    change pderiv i (∑ j : Fin (N+2), X j ^ d) = _
    rw [map_sum, Finset.sum_eq_single i]
    · rw [pderiv_pow, pderiv_X_self, mul_one]
      rfl
    · intro j _ hji
      rw [pderiv_pow, pderiv_X_of_ne hji, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  let J := Ideal.span (insert G (Set.range fun j : Fin (N+2) => pderiv j G))
  have hmem : pderiv i G ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i,rfl⟩)
  refine ⟨d-1,?_⟩
  have h := J.mul_mem_left (C (d : F)⁻¹) hmem
  rw [hdiff, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd, map_one, one_mul] at h
  exact h

/-- The Fermat coefficients are unchanged by a field extension. -/
theorem map_fermatPolynomial {F L : Type*} [Field F] [Field L] (φ : F →+* L)
    (N d : ℕ) : MvPolynomial.map φ (fermatPolynomial F N d) = fermatPolynomial L N d := by
  simp [fermatPolynomial]

end

end Birch
