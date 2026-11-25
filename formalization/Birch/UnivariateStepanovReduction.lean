import Birch.ArtinSchreierIrreducible
import Birch.UnivariateEulerCoefficient

/-! # Sharp univariate sums from the affine Stepanov point bound -/

open scoped BigOperators Polynomial

namespace Birch

noncomputable section

private def artinSchreierPlanePolynomial {K : Type*} [Field K] (p : ℕ)
    (f : Polynomial K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 1 ^ p - MvPolynomial.X 1 - f.toMvPolynomial 0

private theorem totalDegree_toMvPolynomial_le {K σ : Type*} [Field K]
    (i : σ) (f : Polynomial K) : (f.toMvPolynomial i).totalDegree ≤ f.natDegree := by
  conv_lhs => rw [f.as_sum_support_C_mul_X_pow]
  simp only [map_sum, map_mul, Polynomial.toMvPolynomial_C, map_pow, Polynomial.toMvPolynomial_X]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, zero_add]
    exact Polynomial.le_natDegree_of_mem_supp j hj)

private theorem totalDegree_artinSchreierPlanePolynomial_le {K : Type*} [Field K]
    {p : ℕ} (hp : 0 < p) {f : Polynomial K} (hf : f.natDegree ≤ p) :
    (artinSchreierPlanePolynomial p f).totalDegree ≤ p := by
  unfold artinSchreierPlanePolynomial
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_X, max_eq_left hp]
  · exact (totalDegree_toMvPolynomial_le 0 f).trans hf

private theorem map_toMvPolynomial_zero {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (f : Polynomial K) :
    MvPolynomial.map φ (f.toMvPolynomial (0 : Fin 2)) = (f.map φ).toMvPolynomial 0 := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial j x => simp [← Polynomial.C_mul_X_pow_eq_monomial]

private theorem irreducible_map_artinSchreierPlanePolynomial {K : Type*} [Field K]
    {p : ℕ} [Fact p.Prime] [CharP K p] {f : Polynomial K}
    (hf : 0 < f.natDegree) (hfp : f.natDegree < p) :
    Irreducible ((artinSchreierPlanePolynomial p f).map (algebraMap K (AlgebraicClosure K))) := by
  let φ := algebraMap K (AlgebraicClosure K)
  have hdeg : (f.map φ).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective φ.injective f
  have hirr := irreducible_artinSchreierBinaryPolynomial (p := p) (f.map φ)
    (hdeg.symm ▸ hf) (by rw [hdeg]; exact Nat.not_dvd_of_pos_of_lt hf hfp)
  let e := MvPolynomial.renameEquiv (AlgebraicClosure K) finTwoEquiv.symm
  have h := (MulEquiv.irreducible_iff e).mpr hirr
  have ht : finTwoEquiv.symm true = (1 : Fin 2) := by decide
  have hF : finTwoEquiv.symm false = (0 : Fin 2) := by decide
  unfold artinSchreierPlanePolynomial
  rw [map_sub, map_sub, map_pow, MvPolynomial.map_X, map_toMvPolynomial_zero]
  simpa only [e, map_sub, map_pow, MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    MvPolynomial.rename_toMvPolynomial, ht, hF] using h

private theorem ncard_zeroSet_artinSchreierPlanePolynomial {p : ℕ} [Fact p.Prime]
    {K : Type*} [Field K] [Finite K] [Algebra (ZMod p) K] (f : Polynomial K) (c : K) :
    {xy : Fin 2 → K | (artinSchreierPlanePolynomial p (f - Polynomial.C c)).eval xy = 0}.ncard =
      artinSchreierTwistCount (p := p) f.eval c := by
  rw [← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply (finTwoArrowEquiv K).subtypeEquiv
  intro xy
  change _ = 0 ↔ xy 1 ^ p - xy 1 = f.eval (xy 0) - c
  simp only [artinSchreierPlanePolynomial, map_sub, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_toMvPolynomial, Polynomial.eval_C, sub_eq_zero]

/-- The affine square-root lower bound for absolutely irreducible plane curves of
bounded degree, uniform over finite fields and the equation. -/
def AffinePlanePointCountLowerBound (d : ℕ) : Prop :=
    ∃ c : ℝ, ∀ (F : Type) [Field F] [Fintype F] (f : MvPolynomial (Fin 2) F),
      f.totalDegree ≤ d → Irreducible (f.map (algebraMap F (AlgebraicClosure F))) →
      (Fintype.card F : ℝ) - c * Real.sqrt (Fintype.card F) ≤
        ({p : Fin 2 → F | MvPolynomial.eval p f = 0}.ncard : ℝ)

/-- The lower Stepanov bound applied to all trace translates bounds the
untwisted affine count on both sides, uniformly over finite extensions. -/
theorem artinSchreier_countGrowth_of_affinePlaneLowerBound {p : ℕ} [Fact p.Prime] [NeZero p]
    (hlowerBound : AffinePlanePointCountLowerBound p) :
    ∃ C : ℝ, ∀ (K : Type) [Field K] [Fintype K] [Algebra (ZMod p) K]
      (f : Polynomial K), 0 < f.natDegree → f.natDegree < p →
      |(artinSchreierTwistCount (p := p) f.eval 0 : ℝ) - Fintype.card K| ≤
        C * Real.sqrt (Fintype.card K) := by
  obtain ⟨B, hB⟩ := hlowerBound
  let D := max B 0
  have hD : 0 ≤ D := le_max_right B 0
  refine ⟨(p : ℝ) * D, ?_⟩
  intro K _ _ _ f hf hfp
  classical
  let : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  let q : ℝ := Fintype.card K
  have hlower (c : K) :
      q - D * Real.sqrt q ≤ (artinSchreierTwistCount (p := p) f.eval c : ℝ) := by
    let g := f - Polynomial.C c
    have hdeg : g.natDegree = f.natDegree := Polynomial.natDegree_sub_C
    have h := hB K (artinSchreierPlanePolynomial p g)
      (totalDegree_artinSchreierPlanePolynomial_le (Fact.out : p.Prime).pos (hdeg.symm ▸ hfp.le))
      (irreducible_map_artinSchreierPlanePolynomial (hdeg.symm ▸ hf) (hdeg.symm ▸ hfp))
    rw [ncard_zeroSet_artinSchreierPlanePolynomial] at h
    exact le_trans (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_left B 0)
      (Real.sqrt_nonneg q)) q) h
  choose lift hlift using Algebra.trace_surjective (ZMod p) K
  let c (t : ZMod p) : K := if t = 0 then 0 else lift t
  have hc (t : ZMod p) : Algebra.trace (ZMod p) K (c t) = t := by
    by_cases ht : t = 0 <;> simp [c, ht, hlift]
  let M (t : ZMod p) : ℝ := artinSchreierTwistCount (p := p) f.eval (c t)
  have hcount := character_sum_eq_artinSchreier_counts (p := p) f.eval 0 c hc
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsum : ∑ t : ZMod p, M t = (p : ℝ) * q := by
    apply Complex.ofReal_injective
    push_cast
    change (∑ t : ZMod p, (artinSchreierTwistCount (p := p) f.eval (c t) : ℂ)) =
      (p : ℂ) * (Fintype.card K : ℂ)
    simp at hcount
    calc
      _ = (p : ℂ) * ((p : ℂ)⁻¹ * ∑ t : ZMod p,
          (artinSchreierTwistCount (p := p) f.eval (c t) : ℂ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hpC, one_mul]
      _ = _ := by rw [← hcount]
  have hsumLower : (((p - 1 : ℕ) : ℝ) * (q - D * Real.sqrt q)) ≤
      ∑ t ∈ Finset.univ.erase (0 : ZMod p), M t := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card] using
      (Finset.sum_le_sum (s := Finset.univ.erase (0 : ZMod p)) (fun t _ => hlower (c t)))
  have hsplit := Finset.sum_erase_add Finset.univ M (Finset.mem_univ (0 : ZMod p))
  rw [hsum] at hsplit
  have hple : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hcoef : 0 ≤ D * Real.sqrt q := mul_nonneg hD (Real.sqrt_nonneg q)
  have hzero : M 0 = artinSchreierTwistCount (p := p) f.eval 0 := by simp [M, c]
  change |(artinSchreierTwistCount (p := p) f.eval 0 : ℝ) - q| ≤ _
  rw [← hzero, abs_le]
  rw [Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one] at hsumLower
  constructor
  · have h := hlower (0 : K)
    rw [← hzero] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hple) hcoef]
  · nlinarith

/-- The degree minus one bound for a nontrivial additive sum of a
polynomial of positive degree less than the characteristic. -/
theorem norm_univariate_characterSum_le_of_affinePlaneLowerBound {p : ℕ} [Fact p.Prime]
    [NeZero p] (hlowerBound : AffinePlanePointCountLowerBound p) (f : Polynomial (ZMod p)) (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    {a : ZMod p} (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p := by
  obtain ⟨C, hcount⟩ := artinSchreier_countGrowth_of_affinePlaneLowerBound hlowerBound
  refine norm_univariate_characterSum_le_of_artinSchreier_countGrowth f hr hp C ?_
    (additiveLSeriesExtensionPowerSums_holds f) ha
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with m hm
  let K := GaloisField p m
  let : Fintype K := Fintype.ofFinite K
  let g := f.map (algebraMap (ZMod p) K)
  have hd : g.natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod p) K).injective f
  have h := hcount K g (hd.symm ▸ hr) (hd.symm ▸ hp)
  have hg : g.eval = fun x : K => Polynomial.aeval x f := by
    funext x
    exact Polynomial.eval_map_algebraMap f x
  have hk : Fintype.card K = p^m := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p m hm.ne']
  have hsqrt : Real.sqrt ((p : ℝ)^m) = (Real.sqrt p)^m := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p), Real.sqrt_eq_rpow,
      ← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    congr 1
    ring
  rwa [hg, hk, Nat.cast_pow, hsqrt] at h

end

end Birch
