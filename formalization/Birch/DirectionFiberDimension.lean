import Birch.ConeOrigin
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! # Dimension of the bad-direction fibers -/

open Algebra MvPolynomial
open scoped Cardinal

namespace Birch

noncomputable section

/-- A chain of prime ideals can be retained in the domain quotient by its
first term. -/
theorem exists_primeQuotient_of_dim_ge {A : Type*} [CommRing A] {j : ℕ}
    (hj : (j : WithBot ℕ∞) ≤ ringKrullDim A) :
    ∃ P : PrimeSpectrum A, (j : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ P.asIdeal) := by
  obtain ⟨c,hc⟩ := Order.le_krullDim_iff.mp hj
  let P := c.head
  let e := P.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  let c' : LTSeries (PrimeSpectrum (A ⧸ P.asIdeal)) :=
    { length := c.length
      toFun := fun i => e.symm ⟨c i, c.head_le i⟩
      step := fun i => e.symm.strictMono (c.step i) }
  exact ⟨P, Order.le_krullDim_iff.mpr ⟨c',hc⟩⟩

/-- Affine domains have a transcendence basis whose cardinality is their
Krull dimension. -/
theorem exists_affine_transcendence_basis_with_dim {K A : Type} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, ringKrullDim A = (s : WithBot ℕ∞) ∧
      ∃ x : Fin s → A, IsTranscendenceBasis K x := by
  obtain ⟨s,hs,x,hx⟩ := exists_affine_transcendence_basis (K := K) (A := A)
  obtain ⟨m,g,hg,hint⟩ := exists_integral_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin m) K
  let : Algebra R A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral R A := algebraMap_isIntegral_iff.mp hint
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap R A)) := by
    intro p q hpq
    let : p.asIdeal.IsPrime := p.isPrime
    exact Ideal.IsIntegral.under_lt_under (R := R) (A := A) hpq
  have hupper : ringKrullDim A ≤ ringKrullDim R := Order.krullDim_le_of_strictMono _ hmono
  have hm : ringKrullDim R = (m : WithBot ℕ∞) := by
    simp [R]
  have hy : AlgebraicIndependent K (g ∘ X) := by
    rw [algebraicIndependent_iff_injective_aeval, show aeval (g ∘ X) = g by ext i; simp]
    exact hg
  have hms := hy.cardinalMk_le_trdeg
  rw [← hx.cardinalMk_eq_trdeg, Cardinal.mk_fin, Cardinal.mk_fin] at hms
  have hms' : m ≤ s := by exact_mod_cast hms
  rw [hm] at hupper
  exact ⟨s, le_antisymm (hupper.trans (by exact_mod_cast hms')) hs, x, hx⟩

/-- The coordinate algebra of an affine point has transcendence degree
at most the dimension of the ambient affine quotient. -/
theorem trdeg_affineCoordinates_le {ι K A : Type} [Finite ι] [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] {D : ℕ}
    (I : Ideal (MvPolynomial ι K)) (w : ι → A) (hw : I ≤ RingHom.ker (aeval w).toRingHom)
    (hI : ringKrullDim (MvPolynomial ι K ⧸ I) ≤ (D : WithBot ℕ∞)) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range w)) ≤ (D : Cardinal) := by
  let e : MvPolynomial ι K →ₐ[K] A := aeval w
  let e₀ := e.rangeRestrict
  have he₀ : Function.Surjective e₀ := e.rangeRestrict_surjective
  have hker : I ≤ RingHom.ker e₀.toRingHom := by
    intro a ha
    apply RingHom.mem_ker.mpr
    exact Subtype.ext (RingHom.mem_ker.mp (hw ha))
  let f := Ideal.Quotient.lift I e₀.toRingHom hker
  have hf : Function.Surjective f := Ideal.Quotient.lift_surjective_of_surjective I hker he₀
  have hd : ringKrullDim e.range ≤ (D : WithBot ℕ∞) := (ringKrullDim_le_of_surjective f hf).trans hI
  let : Algebra.FiniteType K e.range := Algebra.FiniteType.of_surjective e₀ he₀
  obtain ⟨s,hs,z,hz⟩ := exists_affine_transcendence_basis (K := K) (A := e.range)
  have hsD : s ≤ D := by exact_mod_cast hs.trans hd
  rw [← aeval_range, ← hz.cardinalMk_eq_trdeg, Cardinal.mk_fin]
  exact_mod_cast hsD

/-- Substitute a point of the parameter space while keeping the fiber
variables free. -/
def affineFiberSubstitution {α β K L : Type} [Field K] [Field L] [Algebra K L]
    (u : β → L) : MvPolynomial (α ⊕ β) K →ₐ[K] MvPolynomial α L :=
  aeval (Sum.elim X (C ∘ u))

/-- Equations for the fiber over a field-valued parameter point. -/
def affineFiberIdeal {α β K L : Type} [Field K] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (u : β → L) : Ideal (MvPolynomial α L) :=
  I.map (affineFiberSubstitution u).toRingHom


/-- A fiber of dimension at least `j` contributes at least `j` to the
transcendence degree of an incidence point above the parameter. -/
theorem trdeg_parameters_add_le_of_fiber_dim {α β K L : Type} [Finite α] [Finite β]
    [Field K] [Field L] [Algebra K L] {D j : ℕ}
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (u : β → L)
    (hI : ringKrullDim (MvPolynomial (α ⊕ β) K ⧸ I) ≤ (D : WithBot ℕ∞))
    (hj : (j : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial α L ⧸ affineFiberIdeal I u)) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range u)) + (j : Cardinal) ≤ (D : Cardinal) := by
  let J := affineFiberIdeal I u
  let B := MvPolynomial α L ⧸ J
  obtain ⟨P,hP⟩ := exists_primeQuotient_of_dim_ge hj
  let : P.asIdeal.IsPrime := P.isPrime
  let A := B ⧸ P.asIdeal
  let e₁ : MvPolynomial α L →ₐ[L] B := Ideal.Quotient.mkₐ L J
  let e₂ : B →ₐ[L] A := Ideal.Quotient.mkₐ L P.asIdeal
  let e : MvPolynomial α L →ₐ[L] A := e₂.comp e₁
  have he : Function.Surjective e := Ideal.Quotient.mkₐ_surjective L P.asIdeal |>.comp
    (Ideal.Quotient.mkₐ_surjective L J)
  let x : α → A := e ∘ X
  let w : α ⊕ β → A := Sum.elim x (algebraMap L A ∘ u)
  have hxe : aeval x = e := by ext i; simp [x]
  have heK : aeval w = (e.restrictScalars K).comp (affineFiberSubstitution u) := by
    ext i
    cases i <;> simp [w, x, affineFiberSubstitution]
  have hw : I ≤ RingHom.ker (aeval w).toRingHom := by
    intro f hf
    change aeval w f = 0
    rw [heK]
    change e₂ (e₁ (affineFiberSubstitution u f)) = 0
    have hf' : affineFiberSubstitution u f ∈ J := Ideal.mem_map_of_mem _ hf
    have hz : e₁ (affineFiberSubstitution u f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf'
    rw [hz, map_zero]
  let U := Algebra.adjoin K (Set.range u)
  have : Algebra.FiniteType K U := by
    change Algebra.FiniteType K (Algebra.adjoin K (Set.range u))
    rw [← aeval_range]
    exact Algebra.FiniteType.of_surjective (aeval (R := K) u).rangeRestrict
      (aeval (R := K) u).rangeRestrict_surjective
  obtain ⟨b,_,bu,hbu⟩ := exists_affine_transcendence_basis (K := K) (A := U)
  let : Algebra.FiniteType L A := Algebra.FiniteType.of_surjective e he
  obtain ⟨t,ht,bx,hbx⟩ := exists_affine_transcendence_basis_with_dim (K := L) (A := A)
  have hjt : j ≤ t := by
    have h : (j : WithBot ℕ∞) ≤ ringKrullDim A := hP
    rw [ht] at h
    exact_mod_cast h
  have hxTop : Algebra.adjoin L (Set.range x) = ⊤ := by
    rw [← aeval_range, hxe]
    exact (AlgHom.range_eq_top e).mpr he
  let : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range x)) A := by
    let : Algebra.IsIntegral (Algebra.adjoin L (Set.range x)) A := by
      apply Algebra.isIntegral_of_surjective
      intro a
      exact ⟨⟨a, by rw [hxTop]; exact Algebra.mem_top⟩, rfl⟩
    exact Algebra.IsIntegral.isAlgebraic
  let : FaithfulSMul L A := (faithfulSMul_iff_algebraMap_injective L A).mpr
    (algebraMap L A).injective
  obtain ⟨T,hTsub,hT⟩ := exists_isTranscendenceBasis_subset (R := L) (Set.range x)
  let buL : Fin b → L := U.val ∘ bu
  have hbuL : AlgebraicIndependent K buL :=
    hbu.1.map' (f := U.val) Subtype.val_injective
  let v : T ⊕ Fin b → A := Sum.elim Subtype.val (algebraMap L A ∘ buL)
  have hv : AlgebraicIndependent K v := hbuL.sumElim_comp hT.1
  let W := Algebra.adjoin K (Set.range w)
  have huW : U ≤ W.comap (IsScalarTower.toAlgHom K L A) := by
    apply Algebra.adjoin_le
    rintro _ ⟨i,rfl⟩
    exact Algebra.subset_adjoin ⟨Sum.inr i,rfl⟩
  have hW (z : T ⊕ Fin b) : v z ∈ W := by
    cases z with
    | inl q =>
      obtain ⟨i,hi⟩ := hTsub q.prop
      exact Algebra.subset_adjoin ⟨Sum.inl i,hi⟩
    | inr i =>
      exact huW (bu i).prop
  let vW : T ⊕ Fin b → W := fun z => ⟨v z,hW z⟩
  have hvW : AlgebraicIndependent K vW := AlgebraicIndependent.of_comp W.val hv
  have hsum := hvW.cardinalMk_le_trdeg
  have hTcard : Cardinal.mk T = (t : Cardinal) := hT.cardinalMk_eq_trdeg.trans
    (hbx.cardinalMk_eq_trdeg.symm.trans (Cardinal.mk_fin t))
  have hbcard : (b : Cardinal) = Algebra.trdeg K U :=
    (Cardinal.mk_fin b).symm.trans hbu.cardinalMk_eq_trdeg
  rw [Cardinal.mk_sum, hTcard, Cardinal.mk_fin, hbcard, add_comm] at hsum
  simp only [Cardinal.lift_id] at hsum
  have hjtC : (j : Cardinal) ≤ (t : Cardinal) := by exact_mod_cast hjt
  exact (add_le_add le_rfl hjtC).trans
    (hsum.trans (trdeg_affineCoordinates_le I w hw hI))


/-- If the fiber dimension is at least `j` at every geometric point of an
affine parameter scheme, its dimension is at most the total dimension
bound minus `j`. -/
theorem ringKrullDim_parameters_le_of_fiber_dim {α β K : Type} [Finite α] [Finite β]
    [Field K] {D j : ℕ}
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (J : Ideal (MvPolynomial β K))
    (hI : ringKrullDim (MvPolynomial (α ⊕ β) K ⧸ I) ≤ (D : WithBot ℕ∞))
    (hJ : ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosed L], ∀ u : β → L,
      J ≤ RingHom.ker (aeval u).toRingHom →
        (j : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial α L ⧸ affineFiberIdeal I u)) :
    ringKrullDim (MvPolynomial β K ⧸ J) ≤ ((D-j : ℕ) : WithBot ℕ∞) := by
  by_contra! h
  have hd : ((D-j+1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial β K ⧸ J) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ENat.WithBot.add_one_le_iff.mpr h
  let B := MvPolynomial β K ⧸ J
  obtain ⟨P,hP⟩ := exists_primeQuotient_of_dim_ge hd
  let : P.asIdeal.IsPrime := P.isPrime
  let A := B ⧸ P.asIdeal
  let q : MvPolynomial β K →ₐ[K] A :=
    (Ideal.Quotient.mkₐ K P.asIdeal).comp (Ideal.Quotient.mkₐ K J)
  have hq : Function.Surjective q :=
    (Ideal.Quotient.mkₐ_surjective K P.asIdeal).comp (Ideal.Quotient.mkₐ_surjective K J)
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective q hq
  obtain ⟨s,hs,xs,hxs⟩ := exists_affine_transcendence_basis_with_dim (K := K) (A := A)
  have hs₀ : D-j+1 ≤ s := by
    have H : ((D-j+1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := hP
    rw [hs] at H
    exact_mod_cast H
  let F := FractionRing A
  let L := AlgebraicClosure F
  let ρ : A →ₐ[K] L := (IsScalarTower.toAlgHom K F L).comp (IsScalarTower.toAlgHom K A F)
  have hρ : Function.Injective ρ :=
    (algebraMap F L).injective.comp (IsFractionRing.injective A F)
  let f := ρ.comp q
  let u : β → L := f ∘ X
  have he : aeval u = f := by ext i; simp [u]
  have hu : J ≤ RingHom.ker (aeval u).toRingHom := by
    intro g hg
    change aeval u g = 0
    rw [he]
    have hz : Ideal.Quotient.mkₐ K J g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hg
    simp only [f, q, AlgHom.comp_apply, hz, map_zero]
  let U := Algebra.adjoin K (Set.range u)
  have hm (x : A) : ρ x ∈ U := by
    obtain ⟨g,rfl⟩ := hq x
    change ρ (q g) ∈ Algebra.adjoin K (Set.range u)
    rw [← aeval_range, he]
    exact ⟨g,rfl⟩
  let zs : Fin s → U := fun i => ⟨ρ (xs i), hm (xs i)⟩
  have hz : AlgebraicIndependent K zs := AlgebraicIndependent.of_comp U.val
    (hxs.1.map' (f := ρ) hρ)
  have hc := hz.cardinalMk_le_trdeg
  rw [Cardinal.mk_fin] at hc
  have H := trdeg_parameters_add_le_of_fiber_dim I u hI (hJ L u hu)
  have H' : (s : Cardinal) + (j : Cardinal) ≤ (D : Cardinal) :=
    (add_le_add hc le_rfl).trans H
  have H'' : s+j ≤ D := by exact_mod_cast H'
  omega

private theorem affineFiberSubstitution_eq_aeval_map {α β K L : Type}
    [Field K] [Field L] [Algebra K L] (u : β → L) (f : MvPolynomial (α ⊕ β) K) :
    affineFiberSubstitution u f =
      aeval (Sum.elim X (C ∘ u)) (MvPolynomial.map (algebraMap K L) f) := by
  rw [affineFiberSubstitution, aeval_def, aeval_def, eval₂_map]
  congr 1

/-- The incidence fiber over a field-valued direction is the gradient
scheme of the directional derivative after extension of scalars. -/
theorem affineFiberIdeal_hessianIncidence {K L : Type} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (G : MvPolynomial (Fin n) K) (u : Fin n → L) :
    affineFiberIdeal (hessianIncidenceIdeal G) u =
      Ideal.span (Set.range fun i : Fin n =>
        pderiv i (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G))) := by
  have hmap (i : Fin n) : MvPolynomial.map (algebraMap K L) (hessianIncidenceEquation G i) =
      hessianIncidenceEquation (MvPolynomial.map (algebraMap K L) G) i := by
    simp only [hessianIncidenceEquation, map_sum, map_mul, map_X, map_rename, pderiv_map]
  have heq (i : Fin n) : affineFiberSubstitution u (hessianIncidenceEquation G i) =
      pderiv i (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G)) := by
    rw [affineFiberSubstitution_eq_aeval_map, hmap]
    exact hessianIncidenceEquation_specialize _ i u
  unfold affineFiberIdeal hessianIncidenceIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  change Ideal.span (Set.range fun i : Fin n =>
    affineFiberSubstitution u (hessianIncidenceEquation G i)) = _
  rw [funext heq]

/-- The affine direction stratum where the derivative gradient has dimension
at least `j` has dimension at most `n+s-j` when it is cut out by equations
valid on all algebraically closed extensions. -/
theorem ringKrullDim_hessianDirectionStratum_le {K : Type} [Field K] {n e s j : ℕ}
    {G : MvPolynomial (Fin n) K} (hG : G.IsHomogeneous e) (he : 2 ≤ e)
    (hchar : ((e-1 : ℕ) : K) ≠ 0)
    (hs : ringKrullDim (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range fun i => pderiv i G)) ≤ (s : WithBot ℕ∞))
    (J : Ideal (MvPolynomial (Fin n) K))
    (hJ : ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosed L], ∀ u : Fin n → L,
      J ≤ RingHom.ker (aeval u).toRingHom →
      (j : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) L ⧸
        Ideal.span (Set.range fun i : Fin n =>
          pderiv i (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G))))) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ J) ≤ ((n+s-j : ℕ) : WithBot ℕ∞) := by
  apply ringKrullDim_parameters_le_of_fiber_dim (hessianIncidenceIdeal G) J
  · have H := (ringKrullDim_hessianIncidence_le hG he hchar).trans (add_le_add hs le_rfl)
    simpa only [Nat.cast_add, add_comm] using H
  · intro L _ _ _ u hu
    rw [affineFiberIdeal_hessianIncidence]
    exact hJ L u hu

end
end Birch
