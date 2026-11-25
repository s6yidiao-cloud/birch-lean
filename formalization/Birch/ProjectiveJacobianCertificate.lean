module

public import Birch.ProjectiveJacobianCriterion
public import Birch.PrimeCriticalPoint
public import Birch.MvPolynomialCoefficientCompat
public import Birch.DeligneLevelClosure
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

/-! # Base-field ideal certificates for smooth projective level sets -/

open MvPolynomial

namespace Birch

noncomputable section

/-- A projective Jacobian with no nonzero geometric zeros supplies the
base-field powers of the coordinate variables used by the scheme criterion.
The Nullstellensatz here allows distinct coefficient and evaluation fields. -/
theorem exists_projectiveJacobianCertificate {σ k K : Type*} [Finite σ]
    [Field k] [Field K] [Algebra k K] [IsAlgClosed K] (G : MvPolynomial σ k)
    (hG : ∀ x : σ → K, G.eval₂ (algebraMap k K) x = 0 →
      (∀ i, (pderiv i G).eval₂ (algebraMap k K) x = 0) → x = 0) :
    ∀ j : σ, ∃ N : ℕ, X j ^ N ∈ Ideal.span (insert G (Set.range fun i : σ => pderiv i G)) := by
  let J := Ideal.span (insert G (Set.range fun i : σ => pderiv i G))
  intro j
  apply Ideal.mem_radical_iff.mp
  change X j ∈ J.radical
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
  intro x hx
  have hzero : x = 0 := hG x (hx G (Ideal.subset_span (Set.mem_insert _ _)))
    (fun i => hx (pderiv i G) (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)))
  simp [hzero]

/-- Taking a homogeneous component commutes with changing coefficients. -/
theorem homogeneousComponent_map_ringHom {σ R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : MvPolynomial σ R) (d : ℕ) :
    MvPolynomial.map φ (homogeneousComponent d g) = homogeneousComponent d (MvPolynomial.map φ g) := by
  ext m
  simp only [coeff_map, coeff_homogeneousComponent]
  split_ifs <;> simp

/-- The level closure commutes with change of coefficients. -/
theorem map_deligneLevelClosure {σ R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (g : MvPolynomial σ R) (t : R) :
    MvPolynomial.map φ (deligneLevelClosure d g t) =
      deligneLevelClosure d (MvPolynomial.map φ g) (φ t) := by
  simp only [deligneLevelClosure, degreeHomogenization, map_sum, map_mul, map_pow,
    map_X, map_rename, homogeneousComponent_map_ringHom, map_sub, map_C]

/-- The projective level equation with coordinates indexed by Fin (n + 1). -/
def deligneLevelClosureFin {n : ℕ} {R : Type*} [CommRing R]
    (d : ℕ) (g : MvPolynomial (Fin n) R) (t : R) : MvPolynomial (Fin (n + 1)) R :=
  rename (finSuccEquiv n).symm (deligneLevelClosure d g t)

/-- The reordered projective equation is homogeneous of the stated degree. -/
theorem isHomogeneous_deligneLevelClosureFin {n : ℕ} {R : Type*} [CommRing R]
    (d : ℕ) (g : MvPolynomial (Fin n) R) (t : R) :
    (deligneLevelClosureFin d g t).IsHomogeneous d :=
  (isHomogeneous_deligneLevelClosure d g t).rename_isHomogeneous

/-- Over a nonzero level, the homogeneous projective equation is nonzero. -/
theorem deligneLevelClosureFin_ne_zero_of_homogeneous {n : ℕ} {K : Type*} [Field K]
    {d : ℕ} (hd : 0 < d) {g : MvPolynomial (Fin n) K} (hg : g.IsHomogeneous d)
    {t : K} (ht : t ≠ 0) : deligneLevelClosureFin d g t ≠ 0 := by
  intro hz
  unfold deligneLevelClosureFin at hz
  have hz' : deligneLevelClosure d g t = 0 := by
    apply rename_injective (R := K) _ (finSuccEquiv n).symm.injective
    simpa only [map_zero] using hz
  have he := eval₂_deligneLevelClosure_one hg.totalDegree_le t (RingHom.id K) (0 : Fin n → K)
  rw [hz', eval₂_zero] at he
  have hg0 : g.eval₂ (RingHom.id K) 0 = 0 := by
    change g.eval 0 = 0
    rw [eval_zero]
    exact hg.coeff_eq_zero (by simp [hd.ne])
  simp only [hg0, RingHom.id_apply, zero_sub] at he
  exact ht (neg_eq_zero.mp he.symm)

/-- Nonzero levels of a homogeneous prime-field phase with an isolated
leading critical point satisfy the ideal-form Jacobian criterion over the
prime field. -/
theorem exists_deligneLevelClosureFin_jacobianCertificate_of_homogeneous {n p d : ℕ}
    [Fact p.Prime] (hd : 0 < d) (hdp : d < p) {g : MvPolynomial (Fin n) (ZMod p)}
    (hg : g.IsHomogeneous d) (hcrit : PrimeIsolatedLeadingCriticalPoint p d g)
    {t : ZMod p} (ht : t ≠ 0) :
    let G := deligneLevelClosureFin d g t
    ∀ j : Fin (n + 1), ∃ N : ℕ, X j ^ N ∈
      Ideal.span (insert G (Set.range fun i : Fin (n + 1) => pderiv i G)) := by
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  let G := deligneLevelClosureFin d g t
  apply exists_projectiveJacobianCertificate (K := K) G
  intro x _ hx
  let y : Option (Fin n) → K := x ∘ (finSuccEquiv n).symm
  have hdK : (d : K) ≠ 0 := by
    intro h
    exact hdp.not_ge (Nat.le_of_dvd hd ((CharP.cast_eq_zero_iff K p d).mp h))
  have hcrit' : ∀ z : Fin n → K, (∀ i, (pderiv i (MvPolynomial.map φ g)).eval z = 0) →
      z = 0 := by
    intro z hz
    apply hcrit z
    intro i
    rw [homogeneousComponent_eq_self hg]
    simpa only [pderiv_map, eval_map] using hz i
  have hy : y = 0 := by
    apply eq_zero_of_deligneLevelClosure_critical_of_homogeneous hd hdK (hg.map φ) hcrit'
      ((map_ne_zero φ).mpr ht)
    intro j
    have hh := hx ((finSuccEquiv n).symm j)
    change (pderiv ((finSuccEquiv n).symm j)
      (rename (finSuccEquiv n).symm (deligneLevelClosure d g t))).eval₂ φ x = 0 at hh
    rw [pderiv_rename (finSuccEquiv n).symm.injective, eval₂_rename] at hh
    rw [← map_deligneLevelClosure, pderiv_map, eval_map]
    exact hh
  funext j
  simpa only [y, Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using
    congrFun hy (finSuccEquiv n j)

end
end Birch
