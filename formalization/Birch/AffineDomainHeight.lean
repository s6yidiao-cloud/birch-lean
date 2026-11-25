module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

@[expose] public section

/-! # Heights of maximal ideals in affine domains -/

open Algebra MvPolynomial

namespace Birch

/- The height argument follows the Noether-normalization and going-down proof
in AxiomMath/Stacks, RingTheory/KrullDimension/FiniteTypeOverField.lean at
f56a316ddf7a930906d88b78d6f9a2668cffd0cf (Apache-2.0, see LICENSES). -/

private theorem height_maximal_mvPolynomial {K : Type*} [Field K] {n : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsMaximal] : P.height = n := by
  induction n with
  | zero =>
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := P) Ideal.IsPrime.ne_top'
    have hz : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by simp
    rw [hz] at h
    exact le_antisymm (by exact_mod_cast h) (by simp)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let Q := Ideal.map e P
    let q := Q.comap Polynomial.C
    have : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    have : Q.LiesOver q := ⟨by rw [Ideal.under_def, Polynomial.algebraMap_eq]⟩
    rw [← RingEquiv.height_map e P, Polynomial.height_eq_height_add_one q Q, ih q]
    push_cast
    rfl

/-- Any maximal ideal in a finitely generated domain over a field has height
at least the dimension of the domain. -/
theorem ringKrullDim_le_height_of_affineDomain {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ringKrullDim A ≤ (m.height : WithBot ℕ∞) := by
  obtain ⟨s,g,hg,hint⟩ := exists_integral_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral R A := algebraMap_isIntegral_iff.mp hint
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let q := m.comap (algebraMap R A)
  have : q.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  have : m.LiesOver q := ⟨rfl⟩
  have hq : q.height = s := height_maximal_mvPolynomial q
  have hh : (s : ℕ∞) ≤ m.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q m, hq]
    exact le_self_add
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap R A)) := by
    intro a b hab
    let : a.asIdeal.IsPrime := a.isPrime
    exact Ideal.IsIntegral.under_lt_under (R := R) (A := A) hab
  have h : ringKrullDim A ≤ ringKrullDim R := Order.krullDim_le_of_strictMono _ hmono
  have hr : ringKrullDim R = (s : WithBot ℕ∞) := by
    simp [R]
  rw [hr] at h
  exact h.trans (WithBot.coe_le_coe.mpr hh)

end Birch
