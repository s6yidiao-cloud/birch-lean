module

/-
The affine Spec–algebra correspondence is adapted from AxiomMath/Stacks,
StacksFrontier/AlgebraicGeometry/FundamentalGroup/SchemesEtalePoint/Basic.lean,
at revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf.
Released under Apache 2.0 as described in LICENSES/Apache-2.0.txt.
-/
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-! # Field-valued points of affine hypersurfaces -/

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

noncomputable section

universe u

/-- A map between affine schemes over the spectrum of the base ring
corresponds to an algebra map in the opposite direction. -/
def specOverEquivAlgHom {K A L : Type u} [CommRing K] [CommRing A] [CommRing L]
    [Algebra K A] [Algebra K L] :
    {f : Spec (.of L) ⟶ Spec (.of A) //
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))} ≃ (A →ₐ[K] L) where
  toFun f :=
    { toRingHom := (Spec.homEquiv f.val).hom
      commutes' := fun k => by
        have h := congrArg Spec.preimage f.prop
        rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at h
        exact congrArg (fun a : CommRingCat.of K ⟶ CommRingCat.of L => a.hom k) h }
  invFun a := ⟨Spec.map (CommRingCat.ofHom a.toRingHom), by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext k
    exact a.commutes k⟩
  left_inv f := Subtype.ext (Spec.homEquiv.symm_apply_apply f.val)
  right_inv a := by
    ext y
    simp

/-- An algebra homomorphism out of the quotient by one polynomial is
evaluation at a solution of that polynomial. -/
def hypersurfaceQuotientAlgHomEquiv {σ K L : Type u} [CommRing K] [CommRing L]
    [Algebra K L] (g : MvPolynomial σ K) :
    ((MvPolynomial σ K ⧸ Ideal.span {g}) →ₐ[K] L) ≃
      {x : σ → L // g.eval₂ (algebraMap K L) x = 0} := by
  let I : Ideal (MvPolynomial σ K) := Ideal.span {g}
  let q := Ideal.Quotient.mkₐ K I
  have hgzero : q g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton g))
  have heval (a : (MvPolynomial σ K ⧸ I) →ₐ[K] L) :
      a.comp q = aeval (fun i => a (q (X i))) :=
    MvPolynomial.algHom_ext fun i => by rw [AlgHom.comp_apply, aeval_X]
  have hvanish (x : {x : σ → L // g.eval₂ (algebraMap K L) x = 0})
      (P : MvPolynomial σ K) (hP : P ∈ I) : aeval x.val P = 0 := by
    have h : I ≤ RingHom.ker (aeval x.val).toRingHom :=
      (RingHom.ker (aeval x.val).toRingHom).span_singleton_le_iff_mem.mpr <|
        RingHom.mem_ker.mpr ((aeval_def x.val g).trans x.prop)
    exact RingHom.mem_ker.mp (h hP)
  let lift (x : {x : σ → L // g.eval₂ (algebraMap K L) x = 0}) :
      (MvPolynomial σ K ⧸ I) →ₐ[K] L :=
    Ideal.Quotient.liftₐ I (aeval x.val) (hvanish x)
  have hlift (x : {x : σ → L // g.eval₂ (algebraMap K L) x = 0}) :
      (lift x).comp q = aeval x.val :=
    Ideal.Quotient.liftₐ_comp I (aeval x.val) (hvanish x)
  exact
    { toFun := fun a => ⟨fun i => a (q (X i)), by
        rw [← aeval_def, ← heval a, AlgHom.comp_apply, hgzero, map_zero]⟩
      invFun := lift
      left_inv := fun a => by
        apply Ideal.Quotient.algHom_ext
        exact (hlift _).trans (heval a).symm
      right_inv := fun x => by
        apply Subtype.ext
        funext i
        exact (congrArg (fun e : MvPolynomial σ K →ₐ[K] L => e (X i))
          (hlift x)).trans (aeval_X x.val i) }

/-- The field-valued points of an affine hypersurface over the base field
are exactly the coordinate vectors satisfying its defining equation.
The source subtype is AxiomMath/Stacks' `fieldValuedPoints`. -/
def affineHypersurfacePointsEquiv {σ K L : Type u} [Field K] [Field L]
    [Algebra K L] (g : MvPolynomial σ K) :
    {f : Spec (.of L) ⟶ Spec (.of (MvPolynomial σ K ⧸ Ideal.span {g})) //
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ Ideal.span {g}))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))} ≃
      {x : σ → L // g.eval₂ (algebraMap K L) x = 0} :=
  specOverEquivAlgHom.trans (hypersurfaceQuotientAlgHomEquiv g)

/-- Over a finite field the scheme point count equals the affine equation count. -/
theorem natCard_affineHypersurfacePoints_eq_card_filter {σ K L : Type u} [Field K] [Field L]
    [Algebra K L] [Fintype σ] [Fintype L] (g : MvPolynomial σ K) :
    Nat.card {f : Spec (.of L) ⟶ Spec (.of (MvPolynomial σ K ⧸ Ideal.span {g})) //
      f ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K ⧸ Ideal.span {g}))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L))} =
      (by classical exact
        (Finset.univ.filter fun x : σ → L => g.eval₂ (algebraMap K L) x = 0).card) := by
  classical
  rw [Nat.card_congr (affineHypersurfacePointsEquiv (L := L) g),
    Nat.card_eq_fintype_card, Fintype.card_subtype]

end

end Birch
