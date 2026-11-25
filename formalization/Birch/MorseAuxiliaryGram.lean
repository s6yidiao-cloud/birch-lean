import Birch.MorseAuxiliaryCounts
import Birch.DeligneGoodLevelCounts

/-! # Correlation bounds from regular level curves -/

open MvPolynomial

namespace Birch

noncomputable section

private theorem natCast_ne_zero_algebraicClosure_zmod {p j : ℕ} [Fact p.Prime]
    (hj : 0 < j) (hjp : j < p) : (j : AlgebraicClosure (ZMod p)) ≠ 0 := by
  rw [← map_natCast (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))), map_ne_zero]
  exact fun h => (Nat.not_dvd_of_pos_of_lt hj hjp) ((ZMod.natCast_eq_zero_iff _ _).mp h)

/-- The pure top-degree difference is geometrically nonsingular. -/
theorem primeIsolatedLeadingCriticalPoint_morseAuxiliaryDifference {p r : ℕ} [Fact p.Prime]
    (hr : 2 ≤ r) (hrp : r < p) :
    PrimeIsolatedLeadingCriticalPoint p r (morseAuxiliaryDifference r) := by
  intro x hx
  apply eq_zero_of_critical_morseAuxiliaryLeading hr
    (natCast_ne_zero_algebraicClosure_zmod (by omega) hrp) x
  intro i
  have h := hx i
  rw [homogeneousComponent_morseAuxiliaryDifference hr, ← eval_map, ← pderiv_map] at h
  simpa only [map_sub, map_pow, map_X] using h

/-- The residual collision curve has a geometrically nonsingular leading form. -/
theorem primeIsolatedLeadingCriticalPoint_morseAuxiliaryResidualLeading {p r : ℕ} [Fact p.Prime]
    (hr : 2 ≤ r) (hrp : r < p) :
    PrimeIsolatedLeadingCriticalPoint p (r-1) (morseAuxiliaryResidualLeading r) := by
  intro x hx
  apply eq_zero_of_critical_morseAuxiliaryResidualLeading hr
    (natCast_ne_zero_algebraicClosure_zmod (by omega) hrp)
    (natCast_ne_zero_algebraicClosure_zmod (by omega) (by omega)) x
  intro i
  have h := hx i
  rwa [homogeneousComponent_eq_self (isHomogeneous_morseAuxiliaryResidualLeading r),
    ← eval_map, ← pderiv_map, map_morseAuxiliaryResidualLeading] at h

/-- The level-one residual collision curve is regular over the algebraic closure. -/
theorem isPrimeRegularLevel_morseAuxiliaryResidualLeading_one {p r : ℕ} [Fact p.Prime]
    (hr : 2 ≤ r) (hrp : r < p) :
    IsPrimeRegularLevel (morseAuxiliaryResidualLeading r : MvPolynomial (Fin 2) (ZMod p)) 1 := by
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  change φ 1 ∉ criticalValues (MvPolynomial.map φ (morseAuxiliaryResidualLeading r))
  rw [map_one, map_morseAuxiliaryResidualLeading]
  rintro ⟨x,hx,ht⟩
  have hzero : x = 0 :=
    eq_zero_of_critical_morseAuxiliaryResidualLeading hr
      (natCast_ne_zero_algebraicClosure_zmod (by omega) hrp)
      (natCast_ne_zero_algebraicClosure_zmod (by omega) (by omega)) x hx
  rw [hzero] at ht
  have hpos : r-1 ≠ 0 := by omega
  have he := eval_scale_of_homogeneous (isHomogeneous_morseAuxiliaryResidualLeading (K := K) r)
    (0 : K) (0 : Fin 2 → K)
  have hval : (morseAuxiliaryResidualLeading r).eval (0 : Fin 2 → K) = 0 := by
    simpa only [zero_mul, ← Pi.zero_def, zero_pow hpos] using he
  exact zero_ne_one (hval.symm.trans ht)

/-- Avoiding differences of auxiliary critical values ensures the shifted
difference curve is regular. -/
theorem isPrimeRegularLevel_morseAuxiliaryDifference_of_avoidance {p r : ℕ} [Fact p.Prime]
    (hr : 2 ≤ r) (hrp : r < p) (t : ZMod p)
    (havoid : let K := AlgebraicClosure (ZMod p)
      ∀ u ∈ morseAuxiliaryCriticalValues (K := K) r,
        ∀ w ∈ morseAuxiliaryCriticalValues (K := K) r,
          algebraMap (ZMod p) K t ≠ u-w) :
    IsPrimeRegularLevel (morseAuxiliaryDifference r) t := by
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  change φ t ∉ criticalValues (MvPolynomial.map φ (morseAuxiliaryDifference r))
  rw [map_morseAuxiliaryDifference]
  rintro ⟨x,hx,ht⟩
  obtain ⟨u,hu,w,hw,he⟩ := criticalValue_morseAuxiliaryDifference hr
    (natCast_ne_zero_algebraicClosure_zmod (by omega) hrp) x hx
  exact havoid u hu w hw (ht.symm.trans he)

/-- The same-degree auxiliary phase makes the Gram diagonal at least
(p-O_r(sqrt p)), with off-diagonal terms (O_r(sqrt p)). -/
theorem morseAuxiliaryGram_of_curveCounts {p r : ℕ} [Fact p.Prime] [NeZero p]
    (hr : 3 ≤ r) (hrp : r < p) {B Bprev : ℝ}
    (hcount : PrimeRegularAffineLevelBoundAtDimension r 2 p (B^2))
    (hcountprev : PrimeRegularAffineLevelBoundAtDimension (r-1) 2 p (Bprev^2))
    (E : Finset (ZMod p)) {scale : ZMod p} (hscale : scale ≠ 0)
    (havoid : let K := AlgebraicClosure (ZMod p)
      ∀ s ∈ E, ∀ v ∈ E, s ≠ v →
        ∀ u ∈ morseAuxiliaryCriticalValues (K := K) r,
          ∀ w ∈ morseAuxiliaryCriticalValues (K := K) r,
            algebraMap (ZMod p) K ((v-s)/scale) ≠ u-w) :
    (∀ s ∈ E, (p : ℝ) - Bprev^2 * (p : ℝ)^((1 : ℝ)/2) - ((r-1 : ℕ) : ℝ) ≤
      ∑ t : ZMod p, (centeredMorseValueCount r scale (t-s))^2) ∧
    (∀ s ∈ E, ∀ v ∈ E, s ≠ v →
      |∑ t : ZMod p, centeredMorseValueCount r scale (t-s) *
        centeredMorseValueCount r scale (t-v)| ≤ B^2 * (p : ℝ)^((1 : ℝ)/2)) := by
  have hr₁ : 2 ≤ r := by omega
  have hres := hcountprev
    (morseAuxiliaryResidualLeading r) (isHomogeneous_morseAuxiliaryResidualLeading r).totalDegree_le
    (primeIsolatedLeadingCriticalPoint_morseAuxiliaryResidualLeading hr₁ hrp) 1
    (isPrimeRegularLevel_morseAuxiliaryResidualLeading_one hr₁ hrp)
  norm_num at hres
  have hdiag := affinePolynomialLevelCount_morseAuxiliaryDifference_zero_lower (K := ZMod p) hr₁
  rw [ZMod.card] at hdiag
  have hdiag' : (p : ℝ) + (affinePolynomialLevelCount
      (morseAuxiliaryResidualLeading (K := ZMod p) r) 1 : ℝ) ≤
      (affinePolynomialLevelCount (morseAuxiliaryDifference (K := ZMod p) r) 0 : ℝ) +
        ((r-1 : ℕ) : ℝ) := by exact_mod_cast hdiag
  constructor
  · intro s _
    simp only [pow_two]
    rw [centeredMorseValueCount_correlation r hscale s s, sub_self, zero_div, ZMod.card]
    rw [abs_le] at hres
    linarith [hres.1]
  · intro s hs v hv hsv
    rw [centeredMorseValueCount_correlation r hscale, ZMod.card]
    have hh := hcount (morseAuxiliaryDifference r)
      (totalDegree_morseAuxiliaryDifference_le hr₁)
      (primeIsolatedLeadingCriticalPoint_morseAuxiliaryDifference hr₁ hrp)
      ((v-s)/scale) (isPrimeRegularLevel_morseAuxiliaryDifference_of_avoidance hr₁ hrp _
        (havoid s hs v hv hsv))
    norm_num at hh
    exact hh

/-- Uniform estimates at all primes supply the two plane correlations. -/
theorem morseAuxiliaryGram_of_goodLevelCounts {p r : ℕ} [Fact p.Prime] [NeZero p]
    (hr : 3 ≤ r) (hrp : r < p) {B Bprev : ℝ}
    (hcount : PrimeGoodAffineLevelPointCounts r B)
    (hcountprev : PrimeGoodAffineLevelPointCounts (r-1) Bprev)
    (E : Finset (ZMod p)) {scale : ZMod p} (hscale : scale ≠ 0)
    (havoid : let K := AlgebraicClosure (ZMod p)
      ∀ s ∈ E, ∀ v ∈ E, s ≠ v →
        ∀ u ∈ morseAuxiliaryCriticalValues (K := K) r,
          ∀ w ∈ morseAuxiliaryCriticalValues (K := K) r,
            algebraMap (ZMod p) K ((v-s)/scale) ≠ u-w) :
    (∀ s ∈ E, (p : ℝ) - Bprev^2 * (p : ℝ)^((1 : ℝ)/2) - ((r-1 : ℕ) : ℝ) ≤
      ∑ t : ZMod p, (centeredMorseValueCount r scale (t-s))^2) ∧
    (∀ s ∈ E, ∀ v ∈ E, s ≠ v →
      |∑ t : ZMod p, centeredMorseValueCount r scale (t-s) *
        centeredMorseValueCount r scale (t-v)| ≤ B^2 * (p : ℝ)^((1 : ℝ)/2)) :=
  morseAuxiliaryGram_of_curveCounts hr hrp (hcount p hrp 2 le_rfl)
    (hcountprev p (by omega) 2 le_rfl) E hscale havoid

end

end Birch
