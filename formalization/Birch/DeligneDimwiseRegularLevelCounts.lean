import Birch.DeligneAmplificationBounds
import Birch.DeligneAuxiliaryPhase
import Birch.DelignePrimeBoundWithLoss
import Birch.MorseGramArithmetic
import Birch.PlaneRegularLevelCounts

/-! # Fixed tensor powers of a phase and regular-level point counts -/

open Filter MvPolynomial
open scoped Topology BigOperators

namespace Birch

/-- Fixed-dimensional regular-level point counts yield square-root
cancellation with any prescribed power loss in the field size. -/
theorem eventual_primeDeligneSum_bound_of_dimwise_regularLevels {r l : ℕ}
    (hr : 3 ≤ r) (hl : 0 < l)
    (hcount : ∀ n ≥ 3, EventualPrimeRegularAffineLevelCountsAtDimension r n)
    (hcurve : EventualPrimeRegularAffineLevelCountsAtDimension r 2)
    (hprev : EventualPrimeRegularAffineLevelCountsAtDimension (r-1) 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 1, ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], r < p →
      ∀ g : MvPolynomial (Fin l) (ZMod p), g.totalDegree ≤ r →
        PrimeIsolatedLeadingCriticalPoint p r g →
        ‖primeDeligneSum p g‖ ≤ C * (p : ℝ)^((l : ℝ)/2 + ε) := by
  classical
  obtain ⟨k, hkmax⟩ := exists_nat_gt (max (2 : ℝ) (2 / ε))
  have hkg : 2 < k := by exact_mod_cast (le_max_left _ _).trans_lt hkmax
  have hk : 3 ≤ k := hkg
  have hkloss : (2 : ℝ) / k ≤ ε := by
    have hkpos : (0 : ℝ) < k := by positivity
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hkmax)
    exact (div_le_iff₀ hkpos).mpr (by linarith)
  let n := k*l
  have hn : 3 ≤ n := by
    dsimp [n]
    calc
      3 ≤ k := hk
      _ = k * 1 := (mul_one k).symm
      _ ≤ k * l := Nat.mul_le_mul_left _ hl
  obtain ⟨A₂, hA₂, hc₂⟩ := hcurve
  obtain ⟨Aprev, hAprev, hcprev⟩ := hprev
  obtain ⟨A, hA, hc⟩ := hcount n hn
  obtain ⟨A₁, hA₁, hc₁⟩ := hcount (n+1) (by omega)
  let B := max (max A₂ Aprev) (max A A₁)
  have hB : 1 ≤ B := hA.trans ((le_max_left _ _).trans (le_max_right _ _))
  have hA₂B : A₂ ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hAprevB : Aprev ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hAB : A ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hA₁B : A₁ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  let D₀ : ℝ := (2*B+2*r+1) * B
  have hD₀ : 1 ≤ D₀ := by
    have h : (1 : ℝ) ≤ 2*B+2*r+1 := by linarith [show 0 ≤ (r : ℝ) by positivity]
    exact one_le_mul_of_one_le_of_one_le h hB
  refine ⟨2*D₀, by linarith, ?_⟩
  obtain ⟨D, hD⟩ := exists_uniform_prime_criticalValues_additivePower_bound l r (by omega)
  have hlarge : ∀ᶠ p : ℕ in atTop, ((k+1 : ℕ) : ℝ)^D ≤ (p : ℝ)^((1 : ℝ)/8) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/8)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hmargin := tendsto_natCast_atTop_atTop.eventually (eventually_morseGram_margin r B B)
  filter_upwards [hlarge, hmargin, hc₂, hcprev, hc, hc₁] with p hlarge hm hp₂ hpprev hpn hpn₁
  intro _ _ hrp g hg hcrit
  obtain ⟨Ealg, hEalg, hEcard⟩ := hD p hg hcrit k
  let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  let E : Finset (ZMod p) := Finset.univ.filter (fun s => φ s ∈ Ealg)
  have hmem (s : ZMod p) : s ∈ E ↔ φ s ∈ Ealg := by simp [E]
  let G := additivePowerPolynomialFin k g
  have hG : G.totalDegree ≤ r := (totalDegree_additivePowerPolynomialFin_le k g).trans hg
  have hcritG : PrimeIsolatedLeadingCriticalPoint p r G :=
    primeIsolatedLeadingCriticalPoint_additivePowerPolynomialFin k g hcrit
  have hEreal : (Ealg.card : ℝ) ≤ (p : ℝ)^((1 : ℝ)/8) :=
    (show (Ealg.card : ℝ) ≤ ((k+1 : ℕ) : ℝ)^D by exact_mod_cast hEcard).trans hlarge
  have hErational : E.card ≤ Ealg.card := Finset.card_le_card_of_injOn φ
    (fun s hs => (hmem s).mp hs) φ.injective.injOn
  have hErational' : (E.card : ℝ) ≤ (p : ℝ)^((1 : ℝ)/8) :=
    (show (E.card : ℝ) ≤ Ealg.card by exact_mod_cast hErational).trans hEreal
  have havCard : E.card^2 * (r-1)^2 + 1 < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact_mod_cast (hm E.card 0 hErational' (by simp only [Nat.cast_zero]; positivity)).2
  obtain ⟨b, hb, havoid⟩ := exists_scale_avoiding_morse_critical_differences φ r E havCard
  let J := morseExceptionalRows φ r Ealg b
  have hJ : (J.card : ℝ) ≤ ((r-1 : ℕ) : ℝ) * (p : ℝ)^((1 : ℝ)/8) := by
    calc
      _ ≤ ((r-1 : ℕ) : ℝ) * Ealg.card := by
        exact_mod_cast (card_morseExceptionalRows_le φ r Ealg b).trans_eq (Nat.mul_comm _ _)
      _ ≤ _ := by gcongr
  let x (s : ZMod p) : ℝ := (affinePolynomialLevelCount G s : ℝ) - (p : ℝ)^(n-1)
  let S : ℝ := B * (p : ℝ)^((n : ℝ)/2)
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hsmall (s : ZMod p) (hs : s ∉ E) : |x s| ≤ S := by
    have hreg : IsPrimeRegularLevel G s := by
      change φ s ∉ criticalValues (MvPolynomial.map φ G)
      rw [← hEalg]
      exact fun h => hs ((hmem s).mpr h)
    refine (hpn hrp G hG hcritG s hreg).trans ?_
    apply mul_le_mul hAB
    · apply Real.rpow_le_rpow_of_exponent_le hp1
      gcongr
      omega
    · positivity
    · positivity
  have hrows (t : ZMod p) (ht : t ∉ J) :
      |∑ i : ZMod p, x i * centeredMorseValueCount r b (t-i)| ≤ B*S := by
    dsimp only [x]
    rw [affinePolynomialLevelCount_adjoinMorsePhase, ZMod.card]
    have hsub : n+1-1 = n := by omega
    have hc := hpn₁ hrp (adjoinMorsePhase r b G)
      (totalDegree_adjoinMorsePhase_le (by omega) b hG)
      (primeIsolatedLeadingCriticalPoint_adjoinMorsePhase (by omega) hrp hb hcritG) t
      (isPrimeRegularLevel_adjoinMorsePhase (by omega) hrp hb Ealg (by rw [hEalg]) ht)
    rw [hsub] at hc
    change _ ≤ B * (B * (p : ℝ)^((n : ℝ)/2))
    rw [← mul_assoc, ← pow_two]
    exact hc.trans (mul_le_mul_of_nonneg_right
      (hA₁B.trans (le_self_pow₀ hB (by decide))) (by positivity))
  have hBsq : B ≤ B^2 := le_self_pow₀ hB (by decide)
  have hcurves : PrimeRegularAffineLevelBoundAtDimension r 2 p (B^2) :=
    fun g hg hcrit t ht => (hp₂ hrp g hg hcrit t ht).trans
      (mul_le_mul_of_nonneg_right (hA₂B.trans hBsq) (by positivity))
  have hcurveprev : PrimeRegularAffineLevelBoundAtDimension (r-1) 2 p (B^2) :=
    fun g hg hcrit t ht => (hpprev (by omega) g hg hcrit t ht).trans
      (mul_le_mul_of_nonneg_right (hAprevB.trans hBsq) (by positivity))
  have hAll := abs_le_of_morseGram_and_observed_at_prime hr hrp (zero_le_one.trans hB)
    (show 0 ≤ S by positivity) hcurves hcurveprev E J hb havoid x hsmall hrows
    (hm E.card J.card hErational' hJ).1
  have hS : S = B * ((p : ℝ)^((l : ℝ)/2))^k := by
    dsimp [S, n]
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hp1), Nat.cast_mul]
    congr 2
    ring
  have hsum := norm_primeDeligneSum_le_of_fixed_power_counts (a := 1) g hl
    (show 0 < k by omega) hD₀ (fun t _ => by
      have ht := hAll t
      dsimp only [x, G, n] at ht
      rw [hS] at ht
      simpa only [pow_one, D₀, mul_assoc, mul_left_comm] using ht)
  refine hsum.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1 ?_) (by positivity))
  norm_num
  linarith

/-- With the plane-curve inputs supplied by the in-tree Stepanov proofs,
the remaining input is square-root counting on regular levels in higher
dimensions, with a separate constant in each dimension. -/
theorem eventual_primeDeligneSum_bound_of_higher_dimwise_regularLevels {r l : ℕ}
    (hr : 3 ≤ r) (hl : 0 < l)
    (hcount : ∀ n ≥ 3, EventualPrimeRegularAffineLevelCountsAtDimension r n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 1, ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], r < p →
      ∀ g : MvPolynomial (Fin l) (ZMod p), g.totalDegree ≤ r →
        PrimeIsolatedLeadingCriticalPoint p r g →
        ‖primeDeligneSum p g‖ ≤ C * (p : ℝ)^((l : ℝ)/2 + ε) := by
  have hcurve (s : ℕ) (hs : 2 ≤ s) : EventualPrimeRegularAffineLevelCountsAtDimension s 2 := by
    obtain ⟨C, hC, h⟩ := eventual_regularPlaneLevelCounts_of_stepanov s hs
    refine ⟨C, hC, ?_⟩
    filter_upwards [h] with p hp
    intro _ _ hsp
    simpa only [PrimeRegularAffineLevelBoundAtDimension, show 2-1 = (1 : ℕ) by decide,
      Nat.cast_one, pow_one, Real.sqrt_eq_rpow] using hp hsp
  exact eventual_primeDeligneSum_bound_of_dimwise_regularLevels hr hl hcount
    (hcurve r (by omega)) (hcurve (r-1) (by omega)) hε

/-- Higher-dimensional regular-level counts supply twisted square-root
bounds with an arbitrarily small power loss. -/
theorem uniformTwistedPrimeBoundWithLoss_of_higher_dimwise_regularLevels {r l : ℕ}
    (hr : 3 ≤ r) (hl : 0 < l)
    (hcount : ∀ n ≥ 3, EventualPrimeRegularAffineLevelCountsAtDimension r n)
    {ε : ℝ} (hε : 0 < ε) :
    UniformTwistedPrimeBoundWithLoss r l ε := by
  obtain ⟨C, _, h⟩ := eventual_primeDeligneSum_bound_of_higher_dimwise_regularLevels hr hl hcount hε
  exact uniformTwistedPrimeBoundWithLoss_of_eventual (by omega) hε.le C h

end Birch
