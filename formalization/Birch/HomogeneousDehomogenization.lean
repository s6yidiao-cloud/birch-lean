/-
Adapted from AxiomMath/Stacks, StacksFrontier/AlgebraicGeometry/ProjectiveSpace/HypersurfaceSmooth.lean
at revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf.
Released under Apache 2.0 as described in LICENSES/Apache-2.0.txt.
-/
module

public import Birch.ProjectiveCharts
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

/-! # Jacobian ideals of dehomogenized polynomials -/

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

variable {σ R : Type*} [CommRing R]

/-- Substituting one for the distinguished coordinate commutes with all
partial derivatives in the remaining coordinates. -/
theorem pderiv_dehomogenize (i : σ) (F : MvPolynomial (Option σ) R) :
    pderiv i (dehomogenize F) = dehomogenize (pderiv (some i) F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    cases j with
    | none => simp [hp]
    | some j =>
      by_cases h : i = j
      · subst j
        simp [hp]
      · simp [hp, h, Ne.symm]

/-- Euler's identity after the distinguished coordinate is set to one. -/
theorem dehomogenize_pderiv_none [Fintype σ] {d : ℕ} {F : MvPolynomial (Option σ) R}
    (hF : F.IsHomogeneous d) :
    dehomogenize (pderiv none F) =
      d • dehomogenize F - ∑ i, X i * pderiv i (dehomogenize F) := by
  have h := congrArg (dehomogenize (σ := σ) (R := R)) hF.sum_X_mul_pderiv
  rw [map_sum, map_nsmul, Fintype.sum_option] at h
  simp only [map_mul, dehomogenize_X_none, one_mul, dehomogenize_X_some,
    ← pderiv_dehomogenize] at h
  exact eq_sub_of_add_eq h

/-- Dehomogenization carries the homogeneous Jacobian ideal into the
Jacobian ideal of the affine equation. -/
theorem dehomogenize_mem_span_pderiv [Fintype σ] {d : ℕ}
    {F G : MvPolynomial (Option σ) R} (hF : F.IsHomogeneous d)
    (hG : G ∈ Ideal.span (insert F (Set.range fun i => pderiv i F))) :
    dehomogenize G ∈ Ideal.span (insert (dehomogenize F)
      (Set.range fun i => pderiv i (dehomogenize F))) := by
  let J := Ideal.span (insert (dehomogenize F) (Set.range fun i => pderiv i (dehomogenize F)))
  have hf : dehomogenize F ∈ J := Ideal.subset_span (Set.mem_insert _ _)
  have hp (i : σ) : pderiv i (dehomogenize F) ∈ J :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self i))
  have hle : Ideal.span (insert F (Set.range fun i => pderiv i F)) ≤
      J.comap dehomogenize.toRingHom := by
    apply Ideal.span_le.mpr
    rintro p (h | ⟨i, rfl⟩)
    · rw [h]
      exact hf
    · change dehomogenize (pderiv i F) ∈ J
      cases i with
      | none =>
        rw [dehomogenize_pderiv_none hF]
        exact J.sub_mem (nsmul_mem hf d) (J.sum_mem fun i _ => J.mul_mem_left _ (hp i))
      | some i =>
        rw [← pderiv_dehomogenize]
        exact hp i
  exact hle hG

/-- A coordinate power in the homogeneous Jacobian ideal gives the unit
ideal on that standard affine chart. -/
theorem span_dehomogenize_rename_eq_top [Finite σ] [DecidableEq σ] (i : σ) {d : ℕ}
    {F : MvPolynomial σ R} (hF : F.IsHomogeneous d)
    (hjac : ∃ N : ℕ, X i ^ N ∈ Ideal.span (insert F (Set.range fun j => pderiv j F))) :
    let g := dehomogenize (rename (Equiv.optionSubtypeNe i).symm F)
    Ideal.span (insert g (Set.range fun j => pderiv j g)) = ⊤ := by
  classical
  let : Fintype σ := Fintype.ofFinite σ
  let e := (Equiv.optionSubtypeNe i).symm
  let P := rename e F
  let J := Ideal.span (insert P (Set.range fun j => pderiv j P))
  have hle : Ideal.span (insert F (Set.range fun j => pderiv j F)) ≤
      J.comap (rename e).toRingHom := by
    apply Ideal.span_le.mpr
    rintro p (h | ⟨j, rfl⟩)
    · rw [h]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · change rename e (pderiv j F) ∈ J
      rw [← pderiv_rename e.injective]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self (e j)))
  obtain ⟨N, hN⟩ := hjac
  have hpow : X none ^ N ∈ J := by
    have h := hle hN
    change rename e (X i ^ N) ∈ J at h
    simpa only [map_pow, rename_X, e, Equiv.optionSubtypeNe_symm_self] using h
  have ht := dehomogenize_mem_span_pderiv hF.rename_isHomogeneous hpow
  rw [map_pow, dehomogenize_X_none, one_pow] at ht
  rwa [Ideal.eq_top_iff_one]

end

end Birch
