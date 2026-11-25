import Birch.DeligneGoodLevelCounts
import Birch.DeligneSchemeChart
import Birch.ProjectiveHypersurfaceIntegral
import StacksFrontier.RingTheory.Polynomial.StepanovBound

/-! # Regular plane level counts from Stepanov bounds -/

namespace Birch

section

open Polynomial Polynomial.Bivariate
open scoped Polynomial.Bivariate

/-- The existing Stepanov bound for good vertical fibres and the plane
intersection bound give a prime-uniform upper bound for a plane curve. -/
theorem exists_planeAffinePointCount_upper_of_stepanov (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℕ) [Fact p.Prime] [NeZero p], d + 1 < p →
      ∀ f : MvPolynomial (Fin 2) (ZMod p), f.totalDegree ≤ d →
        Irreducible (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) →
        ({x : Fin 2 → ZMod p | MvPolynomial.eval x f = 0}.ncard : ℝ) ≤
          (p : ℝ) + C * Real.sqrt p := by
  classical
  choose C hC using fun m => Polynomial.Bivariate.exists_card_le_add_mul_sqrt.{0} m 1 1
  let C₀ : ℝ := ∑ m ∈ Finset.range (d+1), |C m|
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C₀ + 2*(d : ℝ)^3, by positivity, ?_⟩
  intro p _ _ hp f hd hirr
  obtain ⟨g, hg, hgm, hdeg, hgw, hgd, hgi, hcard⟩ :=
    MvPolynomial.exists_monic_normalization f hirr (by rw [ZMod.card]; omega)
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  let : CharP K p := charP_of_injective_algebraMap φ.injective p
  let Ψ : K[X][X] := g.map (Polynomial.mapRingHom φ)
  have hΨ : Ψ.Monic := hg.map _
  have hmap : Function.Injective (Polynomial.mapRingHom φ) := Polynomial.map_injective _ φ.injective
  have hΨdeg : Ψ.natDegree = g.natDegree := Polynomial.natDegree_map_eq_of_injective hmap g
  have hΨder : Polynomial.derivative Ψ ≠ 0 := by
    dsimp [Ψ]
    rw [Polynomial.derivative_map]
    intro h
    apply hgd
    apply Polynomial.map_injective _ hmap
    rw [Polynomial.map_zero]
    exact h
  have hΨw : WeightedDegreeLE 1 Ψ.natDegree Ψ := by
    intro j hj
    rw [hΨdeg]
    rw [show Ψ.coeff j = (g.coeff j).map φ by simp [Ψ, Polynomial.coeff_map]] at hj ⊢
    exact (Nat.add_le_add_right Polynomial.natDegree_map_le _).trans
      (hgw j (fun h => hj (by simp [h])))
  let ψ : ZMod p × ZMod p ↪ K × K :=
    ⟨fun x => (φ x.1, φ x.2), fun _ _ h =>
      Prod.ext (φ.injective (congrArg Prod.fst h)) (φ.injective (congrArg Prod.snd h))⟩
  let U : Finset (ZMod p × ZMod p) :=
    Finset.univ.filter fun x => g.evalEval x.1 x.2 = 0
  let T := U.map ψ
  let S := T.filter fun x => (derivative Ψ).evalEval x.1 x.2 ≠ 0
  let E := T.filter fun x => ¬ (derivative Ψ).evalEval x.1 x.2 ≠ 0
  have hT {x : K × K} (hx : x ∈ T) :
      Ψ.evalEval x.1 x.2 = 0 ∧ x.1 ^ p = x.1 ∧ x.2 ^ p = x.2 := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy₀ := (Finset.mem_filter.mp hy).2
    change Ψ.evalEval (φ y.1) (φ y.2) = 0 ∧ (φ y.1)^p = φ y.1 ∧ (φ y.2)^p = φ y.2
    refine ⟨(map_mapRingHom_evalEval φ g y.1 y.2).trans (by simp [hy₀]), ?_, ?_⟩
    · rw [← map_pow]
      exact congrArg φ (by simpa only [ZMod.card] using FiniteField.pow_card y.1)
    · rw [← map_pow]
      exact congrArg φ (by simpa only [ZMod.card] using FiniteField.pow_card y.2)
  have hwdX : WeightedDegreeLE 1 1 (X : K[X][X]) := by
    simpa only [Polynomial.C_1, pow_one, one_mul] using
      (WeightedDegreeLE.C_mul_X_pow (w := 1) (n := 1) (a := (1 : K[X])) (j := 1) (by simp))
  have hgood := hC g.natDegree K p 1 (by decide) Ψ X 1 hΨ hgi hΨder hΨdeg
    (by simpa only [one_mul, hΨdeg] using hΨw) hwdX WeightedDegreeLE.one S (fun x hx => by
      obtain ⟨hval, hx₁, hx₂⟩ := hT (Finset.mem_filter.mp hx).1
      refine ⟨hval, (Finset.mem_filter.mp hx).2, by simpa only [pow_one] using hx₁, ?_, ?_⟩
      · simp
      · simpa [evalEval_X] using hx₂)
  have hderdeg : (derivative Ψ).natDegree < Ψ.natDegree :=
    Polynomial.natDegree_derivative_lt (show Ψ.natDegree ≠ 0 from (hΨdeg.symm ▸ hgm).ne')
  have hnotdvd : ¬ Ψ ∣ derivative Ψ := fun h =>
    (Nat.not_le_of_lt hderdeg)
      (Polynomial.natDegree_le_of_dvd h hΨder)
  have hbad : E.card ≤ 2*d^3 := by
    apply card_le_of_evalEval_eq_zero_of_not_dvd hgi hnotdvd
      (fun j => (hΨw.coeff_natDegree_le j).trans (hΨdeg.trans_le (hdeg.trans_le hd)))
      (fun j => (hΨw.derivative.coeff_natDegree_le j).trans (hΨdeg.trans_le (hdeg.trans_le hd)))
      (hΨdeg.trans_le (hdeg.trans_le hd))
      (hderdeg.le.trans (hΨdeg.trans_le (hdeg.trans_le hd))) E
    intro x hx
    exact ⟨(hT (Finset.mem_filter.mp hx).1).1, not_not.mp (Finset.mem_filter.mp hx).2⟩
  have hpart : S.card + E.card = T.card :=
    Finset.card_filter_add_card_filter_not (s := T) _
  have hcard' : ({P : ZMod p × ZMod p | g.evalEval P.1 P.2 = 0}.ncard : ℝ) = T.card := by
    have he : {P : ZMod p × ZMod p | g.evalEval P.1 P.2 = 0} = (U : Set _) := by
      ext x
      simp [U]
    rw [he, Set.ncard_coe_finset, Finset.card_map]
  have hCdom : C g.natDegree ≤ C₀ :=
    (le_abs_self _).trans (Finset.single_le_sum (fun m _ => abs_nonneg (C m))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (hdeg.trans_le hd))))
  have hbadR : (E.card : ℝ) ≤ 2*(d : ℝ)^3 := by exact_mod_cast hbad
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by simpa using hp₁)
  rw [hcard, hcard', ← hpart, Nat.cast_add]
  simp only [pow_one] at hgood
  linarith [mul_le_mul_of_nonneg_right hCdom (Real.sqrt_nonneg (p : ℝ)),
    le_mul_of_one_le_right (show 0 ≤ 2*(d : ℝ)^3 by positivity) hsqrt]


end

open Filter MvPolynomial HomogeneousLocalization

/-- A smooth-leading regular plane level is absolutely irreducible.
The affine coordinate ring is the degree-zero chart of the integral
projective closure. -/
theorem irreducible_map_plane_regularLevel {p r : ℕ} [Fact p.Prime]
    (hr : 2 ≤ r) (hrp : r < p) {g : MvPolynomial (Fin 2) (ZMod p)}
    (hg : g.totalDegree ≤ r) (hcrit : PrimeIsolatedLeadingCriticalPoint p r g)
    {t : ZMod p} (ht : IsPrimeRegularLevel g t) :
    Irreducible ((g - C t).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) := by
  classical
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  let G := g.map φ
  let H := deligneLevelClosure r G (φ t)
  have hH := isHomogeneous_deligneLevelClosure r G (φ t)
  let e := (finSuccEquiv 2).symm
  have hrK : (r : K) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff K p r).mp h
    exact hrp.not_ge (Nat.le_of_dvd (by omega) hdiv)
  have hjac := exists_deligneLevelClosureFin_jacobianCertificate_of_regularLevel
    (show 0 < r by omega) hg hcrit ht
  have hI := irreducible_map_of_projectiveJacobianCertificate φ (by decide : 3 ≤ 2+1)
    (show 0 < r by omega) hrK (isHomogeneous_deligneLevelClosureFin r g t) hjac
  have hrename : Irreducible (rename e H) := by
    simpa only [deligneLevelClosureFin, MvPolynomial.map_rename, map_deligneLevelClosure,
      e, H, G, φ] using hI
  have hirr : Irreducible H := (MulEquiv.irreducible_iff (renameEquiv K e)).mp hrename
  let : (Ideal.span {H}).IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  let : IsDomain (HypersurfaceRing H) := inferInstance
  let q := hypersurfaceQuotientHom hH (X none)
  have hq : q ≠ 0 := by
    intro hq
    have hmem : X (none : Option (Fin 2)) ∈ Ideal.span {H} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hq
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hmem
    have hb₀ : b ≠ 0 := by
      intro hz
      have he : X (none : Option (Fin 2)) = (0 : MvPolynomial _ K) :=
        hb.trans (by simp [hz])
      exact X_ne_zero _ he
    have hd := totalDegree_mul_of_isDomain hirr.ne_zero hb₀
    rw [← hb, totalDegree_X, hH.totalDegree hirr.ne_zero] at hd
    omega
  let : IsDomain (Localization.Away q) := IsLocalization.Away.isDomain (S := Localization.Away q) hq
  let v : StandardHypersurfaceChart hH →+* Localization.Away q :=
    { toFun := HomogeneousLocalization.val
      map_zero' := HomogeneousLocalization.val_zero
      map_one' := HomogeneousLocalization.val_one
      map_add' := HomogeneousLocalization.val_add
      map_mul' := HomogeneousLocalization.val_mul }
  let : IsDomain (StandardHypersurfaceChart hH) :=
    Function.Injective.isDomain v (HomogeneousLocalization.val_injective _)
  have hQ : IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span {dehomogenize H}) :=
    Function.Injective.isDomain (standardHypersurfaceChartEquiv hH).symm.toRingHom
      (standardHypersurfaceChartEquiv hH).symm.injective
  have hG : G.totalDegree ≤ r :=
    (Finset.sup_mono (MvPolynomial.support_map_subset φ g)).trans hg
  rw [show dehomogenize H = G - C (φ t) from dehomogenize_deligneLevelClosure hG (φ t)] at hQ
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hQ
  have hne : G - C (φ t) ≠ 0 := by
    intro hzero
    have hdeg : g.totalDegree = r :=
      totalDegree_eq_of_primeIsolatedLeadingCriticalPoint (by decide) g hg hcrit
    have hgC : g = C t := MvPolynomial.map_injective φ φ.injective
      (by simpa only [G, map_C] using sub_eq_zero.mp hzero)
    rw [hgC, totalDegree_C] at hdeg
    omega
  have hprime' := (Ideal.span_singleton_prime hne).mp hprime
  rw [map_sub, map_C]
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mpr hprime'

/-- The auxiliary regular plane curves have the square-root count used
by Gram recovery in every degree. The constants depend only on the degree. -/
theorem eventual_regularPlaneLevelCounts_of_stepanov (r : ℕ) (hr : 2 ≤ r) :
    ∃ C₀ ≥ (1 : ℝ), ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], r < p →
      ∀ (g : MvPolynomial (Fin 2) (ZMod p)), g.totalDegree ≤ r →
      PrimeIsolatedLeadingCriticalPoint p r g → ∀ (t : ZMod p), IsPrimeRegularLevel g t →
      |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)| ≤ C₀ * Real.sqrt p := by
  classical
  obtain ⟨A, hA⟩ := MvPolynomial.exists_card_zeroSet_ge_of_absolutelyIrreducible.{0} r
  obtain ⟨B, _, hB⟩ := exists_planeAffinePointCount_upper_of_stepanov r
  let C₀ := max 1 (max A B)
  refine ⟨C₀, le_max_left _ _, ?_⟩
  filter_upwards [eventually_gt_atTop (r+1)] with p hp
  intro _ _ hrp g hg hcrit t ht
  let f := g - C t
  have hf : f.totalDegree ≤ r := (totalDegree_sub _ _).trans (max_le hg (by simp))
  have hirr := irreducible_map_plane_regularLevel hr hrp hg hcrit ht
  have hcount : {x : Fin 2 → ZMod p | f.eval x = 0}.ncard = affinePolynomialLevelCount g t := by
    unfold affinePolynomialLevelCount
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [f, sub_eq_zero]
  have hlow := hA (ZMod p) f hf hirr
  rw [ZMod.card, hcount] at hlow
  have hupp := hB p hp f hf hirr
  rw [hcount] at hupp
  have hA₀ : A ≤ C₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hB₀ : B ≤ C₀ := (le_max_right _ _).trans (le_max_right _ _)
  rw [abs_le]
  constructor
  · linarith [mul_le_mul_of_nonneg_right hA₀ (Real.sqrt_nonneg (p : ℝ))]
  · linarith [mul_le_mul_of_nonneg_right hB₀ (Real.sqrt_nonneg (p : ℝ))]

end Birch
