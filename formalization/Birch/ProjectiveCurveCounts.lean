import Birch.DimwiseProjectiveCounts
import Birch.PlaneRegularLevelCounts

open Filter MvPolynomial HomogeneousLocalization

namespace Birch

universe u

private theorem not_X_dvd_of_irreducible_homogeneous {K σ : Type*} [Field K]
    {r : ℕ} (hr : 2 ≤ r) {H : MvPolynomial (Option σ) K} (hH : H.IsHomogeneous r)
    (hirr : Irreducible H) : ¬ X none ∣ H := by
  rintro ⟨W, hW⟩
  have hW₀ : W ≠ 0 := by
    intro h
    exact hirr.ne_zero (by simp [hW, h])
  have hunit := hirr.isUnit_or_isUnit hW
  have hWunit : IsUnit W := hunit.resolve_left (fun hx => by
    have hd := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hx).2
    rw [totalDegree_X] at hd
    omega)
  have hWd := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hWunit).2
  have he := totalDegree_mul_of_isDomain (X_ne_zero (R := K) none) hW₀
  rw [← hW, hH.totalDegree hirr.ne_zero, totalDegree_X, hWd] at he
  omega

private theorem irreducible_dehomogenize_of_irreducible_homogeneous {K σ : Type u} [Field K]
    {r : ℕ} (hr : 2 ≤ r) {H : MvPolynomial (Option σ) K} (hH : H.IsHomogeneous r)
    (hirr : Irreducible H) : Irreducible (dehomogenize H) := by
  let : (Ideal.span {H}).IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  let : IsDomain (HypersurfaceRing H) := inferInstance
  let q := hypersurfaceQuotientHom hH (X none)
  have hq : q ≠ 0 := by
    intro hq
    have hmem : X (none : Option σ) ∈ Ideal.span {H} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hq
    obtain ⟨W,hW⟩ := Ideal.mem_span_singleton.mp hmem
    have hW₀ : W ≠ 0 := by
      intro h
      have hz : X (none : Option σ) = (0 : MvPolynomial (Option σ) K) :=
        hW.trans (by rw [h, mul_zero])
      exact X_ne_zero _ hz
    have hd := totalDegree_mul_of_isDomain hirr.ne_zero hW₀
    rw [← hW, totalDegree_X, hH.totalDegree hirr.ne_zero] at hd
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
  have hQ : IsDomain (MvPolynomial σ K ⧸ Ideal.span {dehomogenize H}) :=
    Function.Injective.isDomain (standardHypersurfaceChartEquiv hH).symm.toRingHom
      (standardHypersurfaceChartEquiv hH).symm.injective
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hQ
  have hne : dehomogenize H ≠ 0 := fun hz =>
    hirr.ne_zero (eq_zero_of_dehomogenize_eq_zero hH hz)
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mpr
    ((Ideal.span_singleton_prime hne).mp hprime)

private theorem homogeneousComponent_dehomogenize_ne_zero {K σ : Type u} [Field K]
    {r : ℕ} (hr : 2 ≤ r) {H : MvPolynomial (Option σ) K} (hH : H.IsHomogeneous r)
    (hirr : Irreducible H) : homogeneousComponent r (dehomogenize H) ≠ 0 := by
  intro hz
  apply not_X_dvd_of_irreducible_homogeneous hr hH hirr
  have hrec : deligneLevelClosure r (dehomogenize H) 0 = H :=
    deligneLevelClosure_dehomogenize hH
  rw [← hrec]
  unfold deligneLevelClosure degreeHomogenization
  simp only [map_zero, sub_zero]
  apply Finset.dvd_sum
  intro j hj
  by_cases he : j = r
  · simp [he, hz]
  · have hjr : 0 < r-j := by have := Finset.mem_range.mp hj; omega
    exact (dvd_pow_self _ hjr.ne').trans (dvd_mul_right _ _)

/-- Stepanov's bound on the affine chart and the binary bound at infinity
supply the dimensionwise projective estimate for smooth plane curves. -/
theorem eventual_primeSmoothProjectiveCountAtDimension_three_of_stepanov
    {r : ℕ} (hr : 2 ≤ r) : EventualPrimeSmoothProjectiveCountAtDimension r 3 := by
  classical
  obtain ⟨A, hA⟩ := MvPolynomial.exists_card_zeroSet_ge_of_absolutelyIrreducible.{0} r
  obtain ⟨B, hB₀, hB⟩ := exists_planeAffinePointCount_upper_of_stepanov r
  let C₀ := max A B
  have hC₀ : 0 ≤ C₀ := hB₀.trans (le_max_right _ _)
  refine ⟨C₀ + (r : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (r+1)] with p hp
  intro _ _ hrp G hG _ hjac
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  have hrK : (r : K) ≠ 0 := fun hz =>
    hrp.not_ge (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff K p r).mp hz))
  have hI := irreducible_map_of_projectiveJacobianCertificate φ (by decide : 3 ≤ 3)
    (show 0 < r by omega) hrK hG hjac
  let e := finSuccEquiv 2
  let H := rename e G
  have hH : H.IsHomogeneous r := hG.rename_isHomogeneous
  have hHI : Irreducible (H.map φ) := by
    change Irreducible ((rename e G).map φ)
    rw [MvPolynomial.map_rename]
    exact (MulEquiv.irreducible_iff (renameEquiv K e)).mpr hI
  let g := dehomogenize H
  have hg : g.totalDegree ≤ r := totalDegree_dehomogenize_le_homogeneous hH
  have hgi : Irreducible (g.map φ) := by
    rw [map_dehomogenize]
    exact irreducible_dehomogenize_of_irreducible_homogeneous hr (hH.map φ) hHI
  have hAff : {x : Fin 2 → ZMod p | g.eval x = 0}.ncard = affinePolynomialLevelCount g 0 := by
    unfold affinePolynomialLevelCount
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp
  have hl := hA (ZMod p) g hg hgi
  rw [ZMod.card, hAff] at hl
  have hu := hB p hp g hg hgi
  rw [hAff] at hu
  have hc := natCard_deligneLevelClosure_points (show 0 < r by omega) hg 0
  rw [deligneLevelClosure_dehomogenize hH] at hc
  have hleading : homogeneousComponent r g ≠ 0 := by
    intro hzero
    have h := congrArg (MvPolynomial.map φ) hzero
    rw [homogeneousComponent_map_ringHom, map_zero] at h
    change homogeneousComponent r ((dehomogenize H).map φ) = 0 at h
    rw [map_dehomogenize] at h
    exact homogeneousComponent_dehomogenize_ne_zero hr (hH.map φ) hHI h
  have hinf := natCard_projectiveHypersurfacePoints_fin_two_le_degree
    (homogeneousComponent_isHomogeneous r g) hleading
  have hcount := (Nat.card_congr (projectiveHypersurfacePoints_rename_equiv hG e)).trans hc
  have hP : projectiveSpacePointCount p 1 = 1 + p := by
    simp [projectiveSpacePointCount, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]
  rw [hcount, Nat.cast_add, show 3-2 = 1 by decide, hP, Nat.cast_add, Nat.cast_one]
  change _ ≤ (C₀ + (r : ℝ) + 1) * (p : ℝ) ^ ((1 : ℝ) / 2)
  rw [← Real.sqrt_eq_rpow]
  have hs := Real.sqrt_nonneg (p : ℝ)
  have hs₁ : (1 : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by
    simpa using (show (1 : ℝ) ≤ p by exact_mod_cast (Fact.out : p.Prime).one_lt.le))
  have hA₀ := mul_le_mul_of_nonneg_right (le_max_left A B) hs
  have hB₁ := mul_le_mul_of_nonneg_right (le_max_right A B) hs
  have hi₀ : (0 : ℝ) ≤ Nat.card (projectiveHypersurfacePoints (homogeneousComponent r g)) := by positivity
  have hi₁ : (Nat.card (projectiveHypersurfacePoints (homogeneousComponent r g)) : ℝ) ≤ r := by
    exact_mod_cast hinf
  have he : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) * Real.sqrt p := by
    exact le_mul_of_one_le_right (by positivity) hs₁
  rw [abs_le]
  constructor <;> nlinarith only [hl, hu, hA₀, hB₁, hi₀, hi₁, he]

end Birch
