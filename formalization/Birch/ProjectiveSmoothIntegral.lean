module

public import Birch.ProjectiveIntegralCriterion

public import Birch.DeligneLevelIrreducible
public import Birch.ProjectiveHypersurfaceBaseChange
public import Birch.ProjectiveJacobianCriterion
public import Birch.MvPolynomialCoefficientCompat
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

/-- The projective Jacobian certificate forces a homogeneous polynomial
in at least three variables to remain irreducible over algebraically
closed coefficient extensions of characteristic prime to the degree. -/
theorem irreducible_map_of_projectiveJacobianCertificate {k K : Type} [Field k] [Field K]
    [IsAlgClosed K] (φ : k →+* K) {n d : ℕ} (hn : 3 ≤ n) (hd : 0 < d)
    (hdK : (d : K) ≠ 0) {F : MvPolynomial (Fin n) k} (hF : F.IsHomogeneous d)
    (hjac : ∀ j : Fin n, ∃ N : ℕ, X j ^ N ∈
      Ideal.span (insert F (Set.range fun i : Fin n => pderiv i F))) :
    Irreducible (MvPolynomial.map φ F) := by
  let G := MvPolynomial.map φ F
  have hG : G.IsHomogeneous d := hF.map φ
  apply irreducible_of_isolated_leading_critical_point hn hd hG.totalDegree_le
  rw [homogeneousComponent_eq_self hG]
  intro x hx
  exact eq_zero_of_projectiveJacobianCertificate φ hdK hF hjac x
    (fun i => by simpa only [G, pderiv_map, eval_map] using hx i)

/-- An irreducible homogeneous polynomial of degree at least two
defines an integral projective hypersurface. -/
theorem isIntegral_projectiveHypersurface_of_irreducible {K : Type} [Field K]
    {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d)
    {G : MvPolynomial (Fin n) K} (hG : G.IsHomogeneous d) (hirr : Irreducible G) :
    IsIntegral (projectiveHypersurface hG) := by
  let := (Ideal.span_singleton_prime hirr.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  let : IsDomain (HypersurfaceRing G) := inferInstance
  let j : Fin n := ⟨0,hn⟩
  let π := hypersurfaceQuotientHom hG
  have hj : π (X j) ≠ 0 := by
    intro hh
    have hmem : X j ∈ Ideal.span {G} := Ideal.Quotient.eq_zero_iff_mem.mp hh
    obtain ⟨W,hW⟩ := Ideal.mem_span_singleton.mp hmem
    have hW₀ : W ≠ 0 := by
      intro hw
      have hz : X j = (0 : MvPolynomial (Fin n) K) := hW.trans (by rw [hw, mul_zero])
      exact X_ne_zero j hz
    have he := totalDegree_mul_of_isDomain hirr.ne_zero hW₀
    rw [← hW, totalDegree_X, hG.totalDegree hirr.ne_zero] at he
    omega
  exact isIntegral_proj_of_isDomain (hypersurfaceGrading G hG) (by decide : 0 < 1)
    (π.map_mem (isHomogeneous_X K j)) hj

/-- Over any algebraically closed coefficient extension where the degree
is nonzero, the projective hypersurface of a Jacobian-certified form is integral. -/
theorem isIntegral_projectiveHypersurface_map_of_projectiveJacobianCertificate
    {k K : Type} [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K)
    {n d : ℕ} (hn : 3 ≤ n) (hd : 2 ≤ d) (hdK : (d : K) ≠ 0)
    {F : MvPolynomial (Fin n) k} (hF : F.IsHomogeneous d)
    (hjac : ∀ j : Fin n, ∃ N : ℕ, X j ^ N ∈
      Ideal.span (insert F (Set.range fun i : Fin n => pderiv i F))) :
    IsIntegral (projectiveHypersurface (hF.map φ)) :=
  isIntegral_projectiveHypersurface_of_irreducible (by omega) hd (hF.map φ)
    (irreducible_map_of_projectiveJacobianCertificate φ hn (by omega) hdK hF hjac)

private theorem isLocalHom_mvPolynomial_map {σ k K : Type*} [Field k] [Field K]
    (φ : k →+* K) : IsLocalHom (MvPolynomial.map (σ := σ) φ) where
  map_nonunit P h := by
    rw [MvPolynomial.isUnit_iff] at h ⊢
    refine ⟨?_, fun i hi => ?_⟩
    · have hc := isUnit_iff_ne_zero.mp h.1
      rw [coeff_map] at hc
      exact isUnit_iff_ne_zero.mpr ((map_ne_zero φ).mp hc)
    · have hc := isNilpotent_iff_eq_zero.mp (h.2 i hi)
      rw [coeff_map] at hc
      exact isNilpotent_iff_eq_zero.mpr ((map_eq_zero φ).mp hc)

/-- A Jacobian-certified hypersurface of positive dimension is geometrically
integral when its degree is nonzero in the coefficient field. -/
theorem geometricallyIntegral_projectiveHypersurfaceToField {k : Type} [Field k]
    {n d : ℕ} (hn : 3 ≤ n) (hd : 2 ≤ d) (hdk : (d : k) ≠ 0)
    {F : MvPolynomial (Fin n) k} (hF : F.IsHomogeneous d)
    (hjac : ∀ j : Fin n, ∃ N : ℕ, X j ^ N ∈
      Ideal.span (insert F (Set.range fun i : Fin n => pderiv i F))) :
    GeometricallyIntegral (projectiveHypersurfaceToField hF) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd hY
  let φ := algebraMap k K
  let ψ := algebraMap K (AlgebraicClosure K)
  have hd' : (d : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (ψ.comp φ)]
    exact (map_ne_zero (ψ.comp φ)).mpr hdk
  have hi := irreducible_map_of_projectiveJacobianCertificate (ψ.comp φ) hn (by omega) hd' hF hjac
  let := isLocalHom_mvPolynomial_map (σ := Fin n) ψ
  have hm : Irreducible (MvPolynomial.map φ F) := by
    apply Irreducible.of_map (f := MvPolynomial.map ψ)
    rw [MvPolynomial.map_map]
    exact hi
  let : IsIntegral (projectiveHypersurface (hF.map φ)) :=
    isIntegral_projectiveHypersurface_of_irreducible (by omega) hd (hF.map φ) hm
  let e := (isPullback_projectiveHypersurfaceCoefficientMap φ hF).isoPullback ≪≫ hY.isoPullback.symm
  exact IsIntegral.of_isIso e.hom

end
end Birch
