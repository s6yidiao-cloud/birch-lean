import Birch.UnivariateLFunction
import Birch.ArtinSchreierCounts
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Artin–Schreier counts and extension-field phase traces -/

open Polynomial Algebra Filter
open scoped IntermediateField Topology

namespace Birch

noncomputable section

variable {p : ℕ} [Fact p.Prime] [NeZero p]
variable {K : Type*} [Field K] [Finite K] [Algebra (ZMod p) K]

/-- The sum for the character of the prime-field trace at an extension field. -/
def extensionCharacterSum (g : K → K) (a : ZMod p) : ℂ :=
  letI : Fintype K := Fintype.ofFinite K
  ∑ x : K, ZMod.stdAddChar (a * trace (ZMod p) K (g x))

/-- For each extension, the Artin–Schreier affine point count is the field size
plus the sum over all nonzero additive characters. -/
theorem artinSchreier_affineCount_eq_field_card_add_characterSums (g : K → K) :
    (artinSchreierTwistCount (p := p) g 0 : ℂ) =
      (Nat.card K : ℂ) + ∑ a ∈ Finset.univ.erase (0 : ZMod p), extensionCharacterSum g a := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨s, hs⟩ := (Algebra.trace_surjective (ZMod p) K).hasRightInverse
  let lift (a : ZMod p) := if a = 0 then 0 else s a
  have hlift (a : ZMod p) : trace (ZMod p) K (lift a) = a := by
    by_cases h : a = 0
    · simp [lift, h]
    · simp [lift, h, hs a]
  have hz : lift 0 = 0 := by simp [lift]
  have hOrth (t : ZMod p) : (∑ a : ZMod p, ZMod.stdAddChar (a * t)) =
      if t = 0 then (p : ℂ) else 0 := by
    by_cases h : t = 0
    · simp [h, ZMod.card]
    · simp only [ite_eq_right h]
      simpa only [AddChar.mulShift_apply, mul_comm] using
        AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p h)
  have hsum : (∑ a : ZMod p, extensionCharacterSum g a) =
      (artinSchreierTwistCount (p := p) g 0 : ℂ) := by
    unfold extensionCharacterSum
    simp_rw [character_sum_eq_artinSchreier_counts g _ lift hlift]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hOrth, mul_ite, mul_zero]
    rw [Finset.sum_eq_single 0]
    · rw [ite_eq_left rfl, hz]
      have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      field_simp
    · intro a _ ha
      rw [ite_eq_right ha]
    · simp
  have hcount : extensionCharacterSum g (0 : ZMod p) = (Nat.card K : ℂ) := by
    simp [extensionCharacterSum, Nat.card_eq_fintype_card]
  rw [← hsum, ← hcount, add_comm]
  exact (Finset.sum_erase_add Finset.univ (extensionCharacterSum g)
    (Finset.mem_univ (0 : ZMod p))).symm

private theorem trace_eval_gen_eq_polynomialRootPhase
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (pb : PowerBasis k L) (f : k[X]) :
    trace k L (aeval pb.gen f) = polynomialRootPhase f (minpoly k pb.gen) := by
  classical
  let E := AlgebraicClosure k
  let φ := algebraMap k E
  have hnodup : ((minpoly k pb.gen).aroots E).Nodup :=
    nodup_roots ((separable_map _).mpr (Algebra.IsSeparable.isSeparable k pb.gen))
  apply φ.injective
  rw [map_polynomialRootPhase_eq_sum_roots φ f (minpoly.monic pb.isIntegral_gen)]
  change φ (trace k L (aeval pb.gen f)) = (((minpoly k pb.gen).aroots E).map (f.eval₂ φ)).sum
  rw [trace_eq_sum_embeddings E]
  calc
    _ = ∑ x : {x // x ∈ (minpoly k pb.gen).aroots E}, f.eval₂ φ x.val := by
      refine Fintype.sum_equiv pb.liftEquiv' _ _ ?_
      intro σ
      change σ (aeval pb.gen f) = aeval (pb.liftEquiv' σ).val f
      rw [PowerBasis.liftEquiv'_apply_coe, Polynomial.aeval_algHom_apply]
    _ = _ := by
      rw [Finset.sum_mem_multiset, Finset.sum_eq_multiset_sum, Multiset.toFinset_val,
        Multiset.dedup_eq_self.mpr hnodup]
      intro x
      rfl

/-- The trace of a phase at a finite separable extension point is the root phase
of its minimal polynomial, weighted by the residual extension degree. -/
theorem trace_eval_eq_finrank_mul_polynomialRootPhase
    {k L : Type*} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (f : k[X]) (x : L) :
    trace k L (aeval x f) = (Module.finrank k⟮x⟯ L : k) *
      polynomialRootPhase f (minpoly k x) := by
  have hx := Algebra.IsSeparable.isIntegral k x
  let J := k⟮x⟯
  let pb := IntermediateField.adjoin.powerBasis hx
  have hgen : algebraMap J L pb.gen = x := by
    rw [IntermediateField.adjoin.powerBasis_gen hx, IntermediateField.AdjoinSimple.algebraMap_gen]
  have hmin : minpoly k pb.gen = minpoly k x :=
    (minpoly.algebraMap_eq (algebraMap J L).injective pb.gen).symm.trans (congrArg (minpoly k) hgen)
  let : Algebra.IsSeparable k J := Algebra.isSeparable_tower_bot_of_isSeparable k J L
  rw [← trace_trace (S := J)]
  conv_lhs => arg 2; arg 2; rw [← hgen]
  have hEval : aeval (algebraMap J L pb.gen) f = algebraMap J L (aeval pb.gen f) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom k J L) pb.gen f
  rw [hEval, trace_algebraMap, LinearMap.map_smul_of_tower,
    trace_eval_gen_eq_polynomialRootPhase pb f, hmin, nsmul_eq_mul]

/-- The Euler product relation between the extension-field sums of a phase
and the reciprocal roots of its additive L-polynomials. -/
def AdditiveLSeriesExtensionPowerSums (p : ℕ) [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) : Prop :=
  ∀ (a : ZMod p), a ≠ 0 → ∀ L : ℂ[X], (L : PowerSeries ℂ) = additiveLSeries f a →
    ∀ m : ℕ, 0 < m →
      extensionCharacterSum (K := GaloisField p m) (fun x => aeval x f) a =
        -(L.reverse.roots.map (fun z => z^m)).sum

/-- The finite coefficient recurrence of the Euler product. The antidiagonal
contains the terms with both indices positive; the index-zero L-coefficient
contributes the separate extension character sum. -/
def AdditiveLSeriesCoefficientRecurrence (p : ℕ) [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) : Prop :=
  ∀ (a : ZMod p), a ≠ 0 → ∀ m : ℕ, 0 < m →
    (m : ℂ) * additiveLSeriesCoeff f a m =
      extensionCharacterSum (K := GaloisField p m) (fun x => aeval x f) a +
        ∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal m).filter (fun ij => 0 < ij.1 ∧ ij.1 < m),
          additiveLSeriesCoeff f a ij.1 *
            extensionCharacterSum (K := GaloisField p ij.2) (fun x => aeval x f) a

/-- The finite recurrence implies all the extension power sum identities. -/
theorem additiveLSeriesExtensionPowerSums_of_coefficient_recurrence
    {p : ℕ} [Fact p.Prime] [NeZero p] (f : (ZMod p)[X])
    (hrec : AdditiveLSeriesCoefficientRecurrence p f) : AdditiveLSeriesExtensionPowerSums p f := by
  intro a ha L hL
  have hL₀ : L.coeff 0 = 1 := by
    rw [← Polynomial.constantCoeff_coe, hL, constantCoeff_additiveLSeries]
  have hcoeff (m : ℕ) : L.coeff m = additiveLSeriesCoeff f a m := by
    rw [← Polynomial.coeff_coe, hL, additiveLSeries, PowerSeries.coeff_mk]
  apply neg_reciprocalPowerSums_eq_of_coefficient_recurrence L hL₀
  intro m hm
  simp only [hcoeff]
  exact hrec a ha m hm

/-- The affine Artin–Schreier point count differs from the field size by
the negative of the combined power sum of the additive reciprocal roots. -/
theorem artinSchreier_affineCount_eq_primePow_sub_reciprocalPowerSums
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (hL : AdditiveLSeriesExtensionPowerSums p f)
    (L : ZMod p → ℂ[X]) (hL' : ∀ a ≠ 0, (L a : PowerSeries ℂ) = additiveLSeries f a)
    (m : ℕ) (hm : 0 < m) :
    (artinSchreierTwistCount (p := p) (fun x : GaloisField p m => aeval x f) 0 : ℂ) =
      (p : ℂ)^m - ∑ a ∈ Finset.univ.erase (0 : ZMod p),
        (((L a).reverse.roots).map (fun z => z^m)).sum := by
  classical
  have h := artinSchreier_affineCount_eq_field_card_add_characterSums
    (p := p) (fun x : GaloisField p m => aeval x f)
  rw [GaloisField.card p m hm.ne', Nat.cast_pow] at h
  have hs : ∑ a ∈ Finset.univ.erase (0 : ZMod p),
      extensionCharacterSum (K := GaloisField p m) (fun x => aeval x f) a =
      ∑ a ∈ Finset.univ.erase (0 : ZMod p), -(((L a).reverse.roots.map (fun z => z^m)).sum) := by
    apply Finset.sum_congr rfl
    intro a ha
    have hane := (Finset.mem_erase.mp ha).1
    exact hL a hane (L a) (hL' a hane) m hm
  simpa only [hs, Finset.sum_neg_distrib, sub_eq_add_neg] using h

/-- An Artin–Schreier curve's weight-one spectrum, with its single point
at infinity removed, supplies the univariate bound through the Euler product. -/
theorem norm_univariate_characterSum_le_of_artinSchreier_spectrum
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    (A : Multiset ℂ) (hA : ∀ z ∈ A, ‖z‖ = Real.sqrt p)
    (hcurve : ∀ m : ℕ, 0 < m →
      (artinSchreierTwistCount (p := p) (fun x : GaloisField p m => aeval x f) 0 : ℂ) =
        (p : ℂ)^m - (A.map (fun z => z^m)).sum)
    (hL : AdditiveLSeriesExtensionPowerSums p f)
    {a : ZMod p} (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p := by
  apply norm_univariate_characterSum_le_of_curve_powerSums f hr hp A hA ?_ ha
  intro L hL' m hm
  have h := (hcurve m hm).symm.trans
    (artinSchreier_affineCount_eq_primePow_sub_reciprocalPowerSums f hL L hL' m hm)
  exact sub_right_inj.mp h

/-- Square-root growth of the affine curve's point-count errors over
extensions suffices for the sharp univariate sum over the prime field. -/
theorem norm_univariate_characterSum_le_of_artinSchreier_countGrowth
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    (C : ℝ) (hcount : ∀ᶠ m : ℕ in atTop,
      |(artinSchreierTwistCount (p := p) (fun x : GaloisField p m => aeval x f) 0 : ℝ) -
        (p : ℝ)^m| ≤ C * (Real.sqrt p)^m)
    (hL : AdditiveLSeriesExtensionPowerSums p f)
    {a : ZMod p} (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p := by
  apply norm_univariate_characterSum_le_of_additiveLSeriesGrowth f hr hp C ?_ ha
  intro L hL'
  filter_upwards [eventually_gt_atTop (0 : ℕ), hcount] with m hm hcountm
  have h := artinSchreier_affineCount_eq_primePow_sub_reciprocalPowerSums f hL L hL' m hm
  have herr : (((artinSchreierTwistCount (p := p) (fun x : GaloisField p m => aeval x f) 0 : ℝ) -
      (p : ℝ)^m : ℝ) : ℂ) = -(∑ a ∈ Finset.univ.erase (0 : ZMod p),
        (((L a).reverse.roots).map (fun z => z^m)).sum) := by
    push_cast
    linear_combination h
  rw [← norm_neg (∑ _ ∈ _, _), ← herr, Complex.norm_real, Real.norm_eq_abs]
  exact hcountm

end

end Birch
