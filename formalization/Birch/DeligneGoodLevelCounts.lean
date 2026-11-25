import Birch.BinaryProjectivePointCount
import Birch.DeligneCriticalValues
import Birch.DeligneProjectivePointCounts
import Birch.ProjectiveHypersurfaceBoundary

/-! # Counts for regular affine levels -/

open Filter MvPolynomial

namespace Birch

/-- A level is regular when its value is outside the image of the geometric
critical locus of the phase. -/
def IsPrimeRegularLevel {p n : ℕ} [Fact p.Prime] (g : MvPolynomial (Fin n) (ZMod p))
    (t : ZMod p) : Prop :=
  let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  φ t ∉ criticalValues (MvPolynomial.map φ g)

/-- Regular-level point counts at one fixed dimension and prime. -/
def PrimeRegularAffineLevelBoundAtDimension (r n p : ℕ) [Fact p.Prime] [NeZero p]
    (C : ℝ) : Prop :=
  ∀ (g : MvPolynomial (Fin n) (ZMod p)), g.totalDegree ≤ r →
    PrimeIsolatedLeadingCriticalPoint p r g → ∀ (t : ZMod p), IsPrimeRegularLevel g t →
      |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤
        C * (p : ℝ)^(((n-1 : ℕ) : ℝ)/2)

/-- Uniform regular-level counts in each dimension separately, with
dimension-dependent constants and prime cutoffs. -/
def EventualPrimeRegularAffineLevelCountsAtDimension (r n : ℕ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], r < p →
      PrimeRegularAffineLevelBoundAtDimension r n p C

/-- A prime-uniform estimate in the dimension of the regular level. -/
def PrimeGoodAffineLevelPointCounts (r : ℕ) (B : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
    ∀ (n : ℕ), 2 ≤ n → ∀ (g : MvPolynomial (Fin n) (ZMod p)), g.totalDegree ≤ r →
      PrimeIsolatedLeadingCriticalPoint p r g → ∀ (t : ZMod p), IsPrimeRegularLevel g t →
      |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤
        B^n * (p : ℝ)^(((n-1 : ℕ) : ℝ)/2)

/-- The exceptional geometric levels in additive powers grow polynomially,
with an exponent independent of the prime and the coefficients. -/
theorem exists_uniform_prime_criticalValues_additivePower_bound (n r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℕ, ∀ (p : ℕ) [Fact p.Prime] {g : MvPolynomial (Fin n) (ZMod p)},
      g.totalDegree ≤ r → PrimeIsolatedLeadingCriticalPoint p r g → ∀ k : ℕ,
      ∃ E : Finset (AlgebraicClosure (ZMod p)),
        (E : Set (AlgebraicClosure (ZMod p))) = criticalValues (MvPolynomial.map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (additivePowerPolynomialFin k g)) ∧
        E.card ≤ (k+1)^D := by
  obtain ⟨D, hD⟩ := exists_uniform_critical_value_bound n r hr
  refine ⟨D, ?_⟩
  intro p _ g hg hcrit k
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  let G := MvPolynomial.map φ g
  have hgK : G.totalDegree ≤ r :=
    (Finset.sup_mono (MvPolynomial.support_map_subset φ g)).trans hg
  have hcritK (z : Fin n → K) :
      (∀ i, (pderiv i (homogeneousComponent r G)).eval z = 0) → z = 0 := by
    simpa only [G, ← homogeneousComponent_map_ringHom, pderiv_map, eval_map] using hcrit z
  obtain ⟨hfinite, hcard⟩ := hD hgK hcritK
  obtain ⟨hpowfinite, hpowcard⟩ := finite_criticalValues_additivePowerPolynomialFin k G hfinite
  refine ⟨hpowfinite.toFinset, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset, map_additivePowerPolynomialFin]
  · rw [← Set.ncard_eq_toFinset_card _ hpowfinite]
    exact hpowcard.trans (Nat.pow_le_pow_right (by omega) hcard)

/-- A regular level with smooth leading form has a smooth projective closure. -/
theorem exists_deligneLevelClosureFin_jacobianCertificate_of_regularLevel {n p r : ℕ}
    [Fact p.Prime] (hr : 0 < r) {g : MvPolynomial (Fin n) (ZMod p)} (hg : g.totalDegree ≤ r)
    (hcrit : PrimeIsolatedLeadingCriticalPoint p r g) {t : ZMod p} (ht : IsPrimeRegularLevel g t) :
    let G := deligneLevelClosureFin r g t
    ∀ j : Fin (n + 1), ∃ N : ℕ, X j ^ N ∈
      Ideal.span (insert G (Set.range fun i : Fin (n + 1) => pderiv i G)) := by
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  let G := deligneLevelClosureFin r g t
  let e := (finSuccEquiv n).symm
  let gK := MvPolynomial.map φ g
  let H := deligneLevelClosure r gK (φ t)
  have hgK : gK.totalDegree ≤ r :=
    (Finset.sup_mono (MvPolynomial.support_map_subset φ g)).trans hg
  have hcritK (z : Fin n → K) :
      (∀ i, (pderiv i (homogeneousComponent r gK)).eval z = 0) → z = 0 := by
    simpa only [gK, ← homogeneousComponent_map_ringHom, pderiv_map, eval_map] using hcrit z
  apply exists_projectiveJacobianCertificate (K := K) G
  intro x hx hgrad
  by_contra! hnz
  let y := x ∘ e
  have hynz : y ≠ 0 := fun h => hnz (by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact congrFun h i)
  have hy : H.eval y = 0 := by
    change (rename e (deligneLevelClosure r g t)).eval₂ φ x = 0 at hx
    rw [eval₂_rename] at hx
    change (deligneLevelClosure r (MvPolynomial.map φ g) (φ t)).eval y = 0
    rwa [← map_deligneLevelClosure, eval_map]
  have hyd (j : Option (Fin n)) : (pderiv j H).eval y = 0 := by
    have h := hgrad (e j)
    change (pderiv (e j) (rename e (deligneLevelClosure r g t))).eval₂ φ x = 0 at h
    rw [pderiv_rename e.injective, eval₂_rename] at h
    change (pderiv j (deligneLevelClosure r (MvPolynomial.map φ g) (φ t))).eval y = 0
    rwa [← map_deligneLevelClosure, pderiv_map, eval_map]
  obtain ⟨z, _, hz, hdz⟩ := exists_affine_representative_of_deligneLevelClosure_singular
    hr gK (φ t) hcritK y hynz hy hyd
  obtain ⟨hlev, hgz⟩ := (deligneLevelClosure_affine_singular_iff hgK (φ t) z).mp ⟨hz, hdz⟩
  exact ht ⟨z, hgz, hlev⟩

/-- Subtract the smooth projective boundary of a regular level, using the
degree bound for the zero-dimensional boundary of a plane curve. -/
theorem primeGoodAffineLevelPointCounts_of_uniformSmoothCountsWithBase {r : ℕ} (hr : 2 ≤ r)
    {A : ℝ} (hrA : (r : ℝ)-1 ≤ A) (hcount : UniformPrimeSmoothHypersurfacePointCountsWithBase r A) :
    PrimeGoodAffineLevelPointCounts r (2 * A) := by
  intro p _ _ hrp n hn g hg hcrit t ht
  let Q := homogeneousComponent r g
  let E : ℝ := A^n * (p : ℝ)^(((n-1 : ℕ) : ℝ)/2)
  have hr₀ : 0 < r := by omega
  have hA : 1 ≤ A := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hQ : Q ≠ 0 := by
    intro hz
    have h := hcrit (fun _ => 1) (by
      change ∀ i, (pderiv i Q).eval₂ _ _ = 0
      simp [hz])
    exact one_ne_zero (congrFun h ⟨0, by omega⟩)
  have hH : deligneLevelClosureFin r g t ≠ 0 := by
    intro hz
    have hz' : deligneLevelClosure r g t = 0 := by
      apply rename_injective (R := ZMod p) _ (finSuccEquiv n).symm.injective
      simpa only [map_zero, deligneLevelClosureFin] using hz
    have h := setExtraCoordinateZero_deligneLevelClosure hr₀ g t
    rw [hz', map_zero] at h
    exact hQ h.symm
  have hc := hcount p hrp (n+1) (by omega) _ (isHomogeneous_deligneLevelClosureFin r g t) hH
    (exists_deligneLevelClosureFin_jacobianCertificate_of_regularLevel hr₀ hg hcrit ht)
  rw [show n+1-1 = n by omega, show n+1-2 = n-1 by omega] at hc
  have hb : |(Nat.card (projectiveHypersurfacePoints Q) : ℝ) -
      (projectiveSpacePointCount p (n-2) : ℝ)| ≤ E := by
    by_cases hn₃ : 3 ≤ n
    · have hcQ := hcount p hrp n hn₃ Q (homogeneousComponent_isHomogeneous r g) hQ
        (exists_projectiveJacobianCertificate (K := AlgebraicClosure (ZMod p)) Q
          (fun x _ hx => hcrit x hx))
      exact hcQ.trans (mul_le_mul
        (pow_le_pow_right₀ hA (Nat.sub_le _ _))
        (Real.rpow_le_rpow_of_exponent_le hp (by
          gcongr
          omega)) (by positivity) (by positivity))
    · obtain rfl : n = 2 := by omega
      have hbnd := natCard_projectiveHypersurfacePoints_fin_two_le_degree
        (homogeneousComponent_isHomogeneous r g) hQ
      have hbnd' : (Nat.card (projectiveHypersurfacePoints Q) : ℝ) ≤ r := by exact_mod_cast hbnd
      have hbase : A ≤ E := by
        refine (show A ≤ A^2 by nlinarith).trans ?_
        exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hp (by positivity))
      rw [show projectiveSpacePointCount p (2-2) = 1 by
        rw [show 2 - 2 = 0 by omega, projectiveSpacePointCount, ← Nat.range_succ_eq_Iic]
        simp, Nat.cast_one]
      exact (abs_le.mpr ⟨by linarith, by linarith⟩ :
        |(Nat.card (projectiveHypersurfacePoints Q) : ℝ) - 1| ≤ A).trans hbase
  have h := abs_sub_affinePolynomialLevelCount_le_of_projectiveCounts hn hr₀ hg t
    (by simpa only [ZMod.card] using (show _ ≤ E from hc))
    (by simpa only [ZMod.card] using hb)
  rw [ZMod.card] at h
  refine h.trans ?_
  have htwo : (2 : ℝ) ≤ 2^n := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ n by omega))
  calc
    E + E = 2 * A^n * (p : ℝ)^(((n-1 : ℕ) : ℝ)/2) := by dsimp [E]; ring
    _ ≤ 2^n * A^n * (p : ℝ)^(((n-1 : ℕ) : ℝ)/2) := by gcongr
    _ = _ := by rw [← mul_pow]

/-- The classical smooth projective estimate supplies regular affine counts. -/
theorem primeGoodAffineLevelPointCounts_of_uniformSmoothCounts {r : ℕ} (hr : 2 ≤ r)
    (hcount : UniformPrimeSmoothHypersurfacePointCounts r) :
    PrimeGoodAffineLevelPointCounts r (2 * ((r : ℝ)-1)) :=
  primeGoodAffineLevelPointCounts_of_uniformSmoothCountsWithBase hr le_rfl hcount

end Birch
