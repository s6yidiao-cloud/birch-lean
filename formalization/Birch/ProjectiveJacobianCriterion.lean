module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

open MvPolynomial

namespace Birch

noncomputable section

/-- When the degree is nonzero in the evaluation field, the projective
Jacobian certificate excludes all nonzero critical vectors. -/
theorem eq_zero_of_projectiveJacobianCertificate {σ k K : Type*} [Fintype σ]
    [Field k] [Field K] (φ : k →+* K) {d : ℕ} (hd : (d : K) ≠ 0)
    {G : MvPolynomial σ k} (hG : G.IsHomogeneous d)
    (hjac : ∀ j : σ, ∃ N : ℕ, X j ^ N ∈
      Ideal.span (insert G (Set.range fun i : σ => pderiv i G)))
    (x : σ → K) (hx : ∀ i, (pderiv i G).eval₂ φ x = 0) :
    x = 0 := by
  let ε := eval₂Hom φ x
  change ∀ i, ε (pderiv i G) = 0 at hx
  have hG₀ : ε G = 0 := by
    have h := congrArg ε hG.sum_X_mul_pderiv
    simp only [map_sum, map_mul, map_natCast, hx,
      mul_zero, Finset.sum_const_zero, nsmul_eq_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hd
  have hle : Ideal.span (insert G (Set.range fun i => pderiv i G)) ≤ RingHom.ker ε := by
    apply Ideal.span_le.mpr
    rintro P (h | ⟨i, rfl⟩)
    · rw [h]
      exact hG₀
    · exact hx i
  funext j
  obtain ⟨N, hN⟩ := hjac j
  have hz : ε (X j ^ N) = 0 := hle hN
  rw [map_pow, eval₂Hom_X'] at hz
  exact eq_zero_of_pow_eq_zero hz

end

end Birch
