import Birch.CompletionConditional
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization

/-! # Transcendence degree of affine coordinate rings -/

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
    haveI : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    haveI : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    haveI : Q.LiesOver q := ⟨by rw [Ideal.under_def, Polynomial.algebraMap_eq]⟩
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
  letI : Algebra R A := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral R A := algebraMap_isIntegral_iff.mp hint
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let q := m.comap (algebraMap R A)
  haveI : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  haveI : m.LiesOver q := ⟨rfl⟩
  have hq : q.height = s := height_maximal_mvPolynomial q
  have hh : (s : ℕ∞) ≤ m.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q m, hq]
    exact le_self_add
  have hmono : StrictMono (PrimeSpectrum.comap (algebraMap R A)) := by
    intro a b hab
    letI : a.asIdeal.IsPrime := a.isPrime
    exact Ideal.IsIntegral.comap_lt_comap (R := R) (A := A) hab
  have h : ringKrullDim A ≤ ringKrullDim R := Order.krullDim_le_of_strictMono _ hmono
  have hr : ringKrullDim R = (s : WithBot ℕ∞) := by
    simp [R, MvPolynomial.ringKrullDim_of_isNoetherianRing]
  rw [hr] at h
  exact h.trans (WithBot.coe_le_coe.mpr hh)

/-- A maximal ideal of an affine algebra has full height when it lies on
each irreducible component. -/
theorem ringKrullDim_le_height_of_affine_components {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal]
    (hm : ∀ q ∈ minimalPrimes A, q ≤ m) : ringKrullDim A ≤ (m.height : WithBot ℕ∞) := by
  classical
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  letI : p.head.asIdeal.IsPrime := p.head.isPrime
  obtain ⟨q,hq,hqle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := p.head.asIdeal) bot_le
  letI : q.IsPrime := hq.isPrime
  let π := Ideal.Quotient.mk q
  let M := Ideal.map π m
  have hqm : q ≤ m := hm q hq
  haveI : M.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rwa [Ideal.mk_ker])
  have hM : M.comap π = m := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hqm]
  let P : PrimeSpectrum (A ⧸ q) := ⟨M,inferInstance⟩
  have hh : M.height ≤ m.height := by
    have h := Order.height_le_height_apply_of_strictMono _
      (RingHom.strictMono_comap_of_surjective (f := π) Ideal.Quotient.mk_surjective) P
    rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
    rwa [show (PrimeSpectrum.comap π P).asIdeal = m from hM] at h
  have hd := ringKrullDim_le_height_of_affineDomain (K := K) M
  let e := q.primeSpectrumQuotientOrderIsoZeroLocus
  have hp (i : Fin (p.length+1)) : p i ∈ PrimeSpectrum.zeroLocus (q : Set A) :=
    hqle.trans (p.head_le i)
  let p' : LTSeries (PrimeSpectrum (A ⧸ q)) :=
    { length := p.length
      toFun := fun i => e.symm ⟨p i,hp i⟩
      step := fun i => e.symm.strictMono (p.step i) }
  have hchain : (p.length : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) :=
    le_iSup (fun c : LTSeries (PrimeSpectrum (A ⧸ q)) => (c.length : WithBot ℕ∞)) p'
  exact hchain.trans (hd.trans (WithBot.coe_le_coe.mpr hh))

private theorem ringKrullDim_le_of_integral_injective {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hf : Function.Injective (algebraMap R S)) : ringKrullDim R ≤ ringKrullDim S := by
  let f := algebraMap R S
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hf
  have liftChain (p : LTSeries (PrimeSpectrum R)) :
      ∃ q : LTSeries (PrimeSpectrum S), q.length = p.length ∧
        q.last.asIdeal.comap f = p.last.asIdeal := by
    induction p using RelSeries.inductionOn' with
    | singleton P =>
      haveI : P.asIdeal.IsPrime := P.isPrime
      let q := Classical.choice (show Nonempty (P.asIdeal.primesOver S) from inferInstance)
      refine ⟨RelSeries.singleton _ ⟨q.val, q.prop.1⟩, rfl, ?_⟩
      exact ((Ideal.liesOver_iff _ _).mp q.prop.2).symm
    | snoc p P h ih =>
      obtain ⟨q,hql,hq⟩ := ih
      letI : P.asIdeal.IsPrime := P.isPrime
      letI : q.last.asIdeal.IsPrime := q.last.isPrime
      have hle : q.last.asIdeal.comap f ≤ P.asIdeal := hq.trans_le h.le
      obtain ⟨Q,hQ,hQp,hQe⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
        P.asIdeal q.last.asIdeal hle
      have hQlt : q.last < (⟨Q,hQp⟩ : PrimeSpectrum S) := by
        refine lt_of_le_of_ne hQ ?_
        intro he
        have he' := congrArg (fun x : PrimeSpectrum S => x.asIdeal.comap f) he
        rw [hq, hQe] at he'
        exact h.ne (PrimeSpectrum.ext he')
      exact ⟨q.snoc ⟨Q,hQp⟩ hQlt, by simp [hql], by simpa using hQe⟩
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q,hq,_⟩ := liftChain p
  exact hq ▸ le_iSup (fun q : LTSeries (PrimeSpectrum S) => (q.length : WithBot ℕ∞)) q

/-- A finitely generated domain over a field has a transcendence basis
whose size is at most its Krull dimension. -/
theorem exists_affine_transcendence_basis {K A : Type} [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, (s : WithBot ℕ∞) ≤ ringKrullDim A ∧
      ∃ x : Fin s → A, IsTranscendenceBasis K x := by
  obtain ⟨s,g,hg,hint⟩ := exists_integral_inj_algHom_of_fg K A
  let x : Fin s → A := g ∘ X
  have hadj : Algebra.adjoin K (Set.range x) = g.range := by
    rw [show Set.range x = g '' Set.range (X : Fin s → MvPolynomial (Fin s) K) from
      Set.range_comp g X, Algebra.adjoin_image, adjoin_range_X, Algebra.map_top]
  have hspan : Algebra.IsIntegral g.range A := by
    constructor
    intro y
    obtain ⟨f,hf,hy⟩ := hint y
    let gr := g.rangeRestrict.toRingHom
    have hgr : (algebraMap g.range A).comp gr = g.toRingHom := rfl
    exact ⟨f.map gr, hf.map _, by rwa [Polynomial.eval₂_map, hgr]⟩
  have htb : IsTranscendenceBasis K x := by
    apply isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr
    refine ⟨?_, ?_⟩
    · have he : aeval x = g := by ext i; simp [x]
      change Function.Injective (aeval x)
      rwa [he]
    · rw [hadj]
      letI := hspan
      infer_instance
  letI := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := algebraMap_isIntegral_iff.mp hint
  have hdim := ringKrullDim_le_of_integral_injective hg
  have hpoly : ringKrullDim (MvPolynomial (Fin s) K) = (s : WithBot ℕ∞) := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  rw [hpoly] at hdim
  exact ⟨s, hdim, x, htb⟩

/-- Coordinates of a point of an affine scheme generate a field of
transcendence degree at most the dimension of that scheme. The algebra they
generate already has that bound. -/
theorem trdeg_affinePoint_le {K L : Type} [Field K] [Field L] [Algebra K L]
    {n m : ℕ} (J : Ideal (MvPolynomial (Fin n) K)) (x : Fin n → L)
    (hx : J ≤ RingHom.ker (aeval x).toRingHom)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ J) ≤ (m : WithBot ℕ∞)) :
    Algebra.trdeg K (Algebra.adjoin K (Set.range x)) ≤ m := by
  let e : MvPolynomial (Fin n) K →ₐ[K] L := aeval x
  let e₀ : MvPolynomial (Fin n) K →ₐ[K] e.range := e.rangeRestrict
  have he₀ : Function.Surjective e₀ := e.rangeRestrict_surjective
  have hker : J ≤ RingHom.ker e₀.toRingHom := by
    intro a ha
    apply RingHom.mem_ker.mpr
    exact Subtype.ext (RingHom.mem_ker.mp (hx ha))
  let f := Ideal.Quotient.lift J e₀.toRingHom hker
  have hf : Function.Surjective f := Ideal.Quotient.lift_surjective_of_surjective J hker he₀
  have hd : ringKrullDim e.range ≤ (m : WithBot ℕ∞) := (ringKrullDim_le_of_surjective f hf).trans hdim
  letI : Algebra.FiniteType K e.range := Algebra.FiniteType.of_surjective e₀ he₀
  obtain ⟨s,hs,y,hy⟩ := exists_affine_transcendence_basis (K := K) (A := e.range)
  have hsm : s ≤ m := by exact_mod_cast hs.trans hd
  rw [← aeval_range, ← hy.cardinalMk_eq_trdeg, Cardinal.mk_fin]
  exact_mod_cast hsm

/-- A point of a nonzero affine hypersurface has at most `n-1` independent coordinates. -/
theorem trdeg_hypersurfacePoint_le {K L : Type} [Field K] [Field L] [Algebra K L]
    {n : ℕ} (hn : 0 < n) (G : MvPolynomial (Fin n) K) (hG : G ≠ 0) (x : Fin n → L)
    (hx : aeval x G = 0) : Algebra.trdeg K (Algebra.adjoin K (Set.range x)) ≤ ((n-1 : ℕ) : Cardinal) := by
  let J : Ideal (MvPolynomial (Fin n) K) := Ideal.span {G}
  have hJ : J ≤ RingHom.ker (aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    intro f hf
    rw [Set.mem_singleton_iff.mp hf]
    exact RingHom.mem_ker.mpr hx
  have hdim := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_iff_ne_zero.mpr hG)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field K,
    zero_add, Nat.card_fin] at hdim
  have hb : ringKrullDim (MvPolynomial (Fin n) K ⧸ J) ≤ ((n-1 : ℕ) : WithBot ℕ∞) := by
    rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m,rfl⟩
    rw [Nat.succ_sub_one]
    by_contra! h
    have h1 : ((m : WithBot ℕ∞) + 1) ≤ ringKrullDim (MvPolynomial (Fin (m+1)) K ⧸ J) :=
      ENat.WithBot.add_one_le_iff.mpr h
    have h2 := (add_le_add h1 (le_rfl (a := (1 : WithBot ℕ∞)))).trans hdim
    have h3 : (m+1)+1 ≤ m.succ := by exact_mod_cast h2
    omega
  exact trdeg_affinePoint_le J x hJ hb

/-- The ambient point at the singular part of the section incidence has the
transcendence-degree bound given by its prime-field gradient dimension. -/
theorem trdeg_primeGradientPoint_le {n p s : ℕ} (hp : p.Prime) (G : IntForm n)
    (hdim : PrimeGradientDimension p hp G s) :
    letI : Fact p.Prime := ⟨hp⟩
    let K := AlgebraicClosure (ZMod p)
    ∀ (L : Type) [Field L] [Algebra K L] (x : Fin n → L),
      (∀ j, evalForm (pderiv j G) x = 0) →
      Algebra.trdeg K (Algebra.adjoin K (Set.range x)) ≤ s := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  change ∀ (L : Type) [Field L] [Algebra K L] (x : Fin n → L),
    (∀ j, evalForm (pderiv j G) x = 0) → Algebra.trdeg K (Algebra.adjoin K (Set.range x)) ≤ s
  intro L _ _ x hx
  let J : Ideal (MvPolynomial (Fin n) K) := Ideal.span
    (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv j G))
  apply trdeg_affinePoint_le J x _ hdim.le
  apply Ideal.span_le.mpr
  rintro _ ⟨j,rfl⟩
  apply RingHom.mem_ker.mpr
  change aeval x (MvPolynomial.map (Int.castRingHom K) (pderiv j G)) = 0
  rw [aeval_def, eval₂_map,
    show (algebraMap K L).comp (Int.castRingHom K) = Int.castRingHom L by ext; simp]
  exact hx j

end Birch
