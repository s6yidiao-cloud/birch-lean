import Birch.Metric
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # A lower bound for the number of primes in a dyadic interval

The central-binomial-coefficient argument in Mathlib's Bertrand module gives a
linear lower bound for the sum of logarithms of the primes in `(B, 2*B]`.
Here we retain the prime factors in that interval and bound each contribution by
`log (2*B)` to obtain the cardinality bound required in `prop:metric`.
-/

open Finset Filter Real
open scoped BigOperators Topology

namespace Birch

noncomputable section

/-- The primes in the real interval `(B,2*B]`. -/
def dyadicPrimes (B : ℝ) : Finset ℕ := (Finset.Ioc ⌊B⌋₊ ⌊2*B⌋₊).filter Nat.Prime

theorem mem_dyadicPrimes {B : ℝ} (hB : 0 ≤ B) {p : ℕ} :
    p ∈ dyadicPrimes B ↔ p.Prime ∧ B < (p : ℝ) ∧ (p : ℝ) ≤ 2*B := by
  simp only [dyadicPrimes, Finset.mem_filter, Finset.mem_Ioc, Nat.lt_iff_add_one_le]
  constructor
  · rintro ⟨⟨hp, hp'⟩, hprime⟩
    have hfloor : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
    exact ⟨hprime, (Nat.lt_floor_add_one B).trans_le (by simpa using hfloor),
      (Nat.cast_le.mpr hp').trans (Nat.floor_le (by positivity))⟩
  · rintro ⟨hprime, hlow, hupp⟩
    exact ⟨⟨Nat.succ_le_of_lt (Nat.floor_lt hB |>.mpr hlow),
      Nat.le_floor hupp⟩, hprime⟩

theorem dyadicPrimes_card_le {B : ℝ} (hB : 0 ≤ B) : ((dyadicPrimes B).card : ℝ) ≤ 2*B := by
  calc
    _ ≤ ((Finset.Ioc ⌊B⌋₊ ⌊2*B⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (s := Finset.Ioc ⌊B⌋₊ ⌊2*B⌋₊) (p := Nat.Prime)
    _ ≤ (⌊2*B⌋₊ : ℕ) := by rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le _ _
    _ ≤ _ := Nat.floor_le (by positivity)

private def primeBand (n : ℕ) : Finset ℕ := (Finset.Ioc n (2*n)).filter Nat.Prime

private lemma centralBinom_le_primeBand (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤ (2*n)^((2*n).sqrt) * 4^(2*n/3) * (2*n)^(primeBand n).card := by
  let S := {p ∈ Finset.range (2*n/3 + 1) | Nat.Prime p}
  let T := primeBand n
  let f : ℕ → ℕ := fun p => p ^ n.centralBinom.factorization p
  have hS (p : ℕ) : p ∈ S ↔ p ≤ 2*n/3 ∧ p.Prime := by
    simp only [S, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  have hT (p : ℕ) : p ∈ T ↔ (n < p ∧ p ≤ 2*n) ∧ p.Prime := by
    simp only [T, primeBand, Finset.mem_filter, Finset.mem_Ioc]
  have hdis : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hpS hpT
    have h₁ := ((hS p).mp hpS).1
    have h₂ := ((hT p).mp hpT).1.1
    omega
  have hsub : S ∪ T ⊆ Finset.range (2*n + 1) := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · have := ((hS p).mp hp).1
      exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((hT p).mp hp).1.2)
  have hfact : n.centralBinom = (∏ p ∈ S, f p) * ∏ p ∈ T, f p := by
    rw [← Finset.prod_union hdis, ← n.prod_pow_factorization_centralBinom]
    symm
    apply Finset.prod_subset hsub
    intro p hp hnot
    have hle : p ≤ 2*n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    by_cases hp' : p.Prime
    · have hn' : p ≤ n := by
        by_contra! h
        exact hnot (Finset.mem_union_right _ ((hT p).mpr ⟨⟨h, hle⟩, hp'⟩))
      have hlower : 2*n/3 < p := by
        by_contra! h
        exact hnot (Finset.mem_union_left _ ((hS p).mpr ⟨h, hp'⟩))
      unfold f
      rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hn' (by omega), pow_zero]
    · unfold f
      rw [Nat.factorization_eq_zero_of_not_prime n.centralBinom hp', pow_zero]
  have hn2 : 1 ≤ 2*n := by omega
  have hsmall : (∏ p ∈ S, f p) ≤ (2*n)^((2*n).sqrt) * 4^(2*n/3) := by
    rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ (2*n).sqrt)]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod fun p _ => (?_ : f p ≤ 2*n)).trans ?_
      · exact Nat.pow_factorization_choose_le (by omega)
      rw [Finset.prod_const]
      apply pow_right_mono₀ hn2
      have hsubs : S.filter (· ≤ (2*n).sqrt) ⊆ Finset.Icc 1 (2*n).sqrt := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hpS, hup⟩
        exact Finset.mem_Icc.mpr ⟨((hS p).mp hpS).2.one_lt.le, hup⟩
      simpa using Finset.card_le_card hsubs
    · refine le_trans ?_ (primorial_le_four_pow (2*n/3))
      refine (Finset.prod_le_prod fun p hp => (?_ : f p ≤ p)).trans ?_
      · rcases Finset.mem_filter.mp hp with ⟨hpS, hpSize⟩
        refine (pow_right_mono₀ ((hS p).mp hpS).2.one_lt.le ?_).trans (pow_one p).le
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp hpSize))
      exact Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _) fun p hp _ =>
        (Finset.mem_filter.mp hp).2.one_lt.le
  have hlarge : (∏ p ∈ T, f p) ≤ (2*n)^T.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod fun _ _ => Nat.pow_factorization_choose_le (by omega)
  rw [hfact]
  exact mul_le_mul' hsmall hlarge

private theorem eventually_primeBand_count_mul_log :
    ∀ᶠ n : ℕ in atTop, Real.log 4 / 6 * (n : ℝ) ≤ (primeBand n).card * Real.log (2*(n : ℝ)) := by
  have hc : 0 < Real.log 4 / 24 := by positivity
  have hlt := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).bound hc
  have hcast : Tendsto (fun n : ℕ => 2*(n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hlt, eventually_ge_atTop (4 : ℕ)] with n hlog hn
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr : (0 : ℝ) < n := by linarith
  have h2n : (1 : ℝ) ≤ 2*(n : ℝ) := by linarith
  have hlog2n : 0 ≤ Real.log (2*(n : ℝ)) := Real.log_nonneg h2n
  have hs : (1 : ℝ) ≤ (2*(n : ℝ)).sqrt := by
    have := Real.sqrt_le_sqrt h2n
    simpa using this
  have hsq : (2*(n : ℝ)).sqrt ^ 2 = 2*(n : ℝ) := Real.sq_sqrt (by positivity)
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog2n] at hlog
  rw [← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at hlog
  have herror : Real.log (n : ℝ) + (2*(n : ℝ)).sqrt * Real.log (2*(n : ℝ)) ≤
      Real.log 4 / 6 * (n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (2*(n : ℝ)))
    have hle : Real.log (n : ℝ) ≤ (2*(n : ℝ)).sqrt * Real.log (2*(n : ℝ)) :=
      (Real.log_le_log hnr (by linarith)).trans (le_mul_of_one_le_left hlog2n hs)
    have hprod : (2*(n : ℝ)).sqrt * (Real.log 4 / 24 * (2*(n : ℝ)).sqrt) = Real.log 4 / 12 * (n : ℝ) := by
      calc
        _ = Real.log 4 / 24 * (2*(n : ℝ)).sqrt ^ 2 := by ring
        _ = _ := by rw [hsq]; ring
    rw [hprod] at hm
    linarith
  have hbin := (Nat.four_pow_lt_mul_centralBinom n hn).le.trans
    (Nat.mul_le_mul_left n (centralBinom_le_primeBand n (by omega)))
  have hbinR : (4 : ℝ)^n ≤ (n : ℝ) * ((2*(n : ℝ))^((2*n : ℕ).sqrt) *
      4^(2*n/3 : ℕ) * (2*(n : ℝ))^(primeBand n).card) := by exact_mod_cast hbin
  have hlogbin := Real.log_le_log (by positivity) hbinR
  rw [Real.log_pow] at hlogbin
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at hlogbin
  simp only [Real.log_pow] at hlogbin
  have hsqrt : ((2*n : ℕ).sqrt : ℝ) ≤ (2*(n : ℝ)).sqrt := by
    exact_mod_cast (Real.nat_sqrt_le_real_sqrt (a := 2*n))
  have hthird : ((2*n/3 : ℕ) : ℝ) ≤ 2*(n : ℝ)/3 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
    exact_mod_cast (Nat.div_mul_le_self (2*n) 3)
  have hsqrtlog := mul_le_mul_of_nonneg_right hsqrt hlog2n
  have hthirdlog := mul_le_mul_of_nonneg_right hthird (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
  linarith

/-- For all sufficiently large real `B`, there are at least a positive constant times
`B / log (2*B)` primes in `(B,2*B]`. -/
theorem eventually_dyadicPrimes_lower : ∀ᶠ B : ℝ in atTop,
    Real.log 4 / 12 * B / Real.log (2*B) ≤ ((dyadicPrimes B).card : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_primeBand_count_mul_log
  filter_upwards [eventually_ge_atTop (max 2 (N : ℝ))] with B hB
  let n := ⌊B⌋₊
  have hB2 : 2 ≤ B := (le_max_left _ _).trans hB
  have hNn : N ≤ n := Nat.le_floor ((le_max_right _ _).trans hB)
  have hnB : (n : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hhalf : B / 2 ≤ n := by
    have h := Nat.lt_floor_add_one B
    change B < (n : ℝ) + 1 at h
    linarith
  have hn : (0 : ℝ) < n := by linarith
  have hsubs : primeBand n ⊆ dyadicPrimes B := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpI, hpP⟩
    rcases Finset.mem_Ioc.mp hpI with ⟨hlo, hhi⟩
    apply (mem_dyadicPrimes (by linarith)).mpr
    have hlow : ((n+1 : ℕ) : ℝ) ≤ p := by exact_mod_cast (Nat.succ_le_of_lt hlo)
    have hhigh : (p : ℝ) ≤ 2*(n : ℝ) := by exact_mod_cast hhi
    refine ⟨hpP, (Nat.lt_floor_add_one B).trans_le (by simpa using hlow), ?_⟩
    linarith
  have hlog : 0 < Real.log (2*B) := Real.log_pos (by linarith)
  apply (div_le_iff₀ hlog).mpr
  have hcard : ((primeBand n).card : ℝ) ≤ (dyadicPrimes B).card := by exact_mod_cast Finset.card_le_card hsubs
  calc
    _ ≤ Real.log 4 / 6 * (n : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hhalf (show 0 ≤ Real.log 4 from Real.log_nonneg (by norm_num))]
    _ ≤ ((primeBand n).card : ℝ) * Real.log (2*(n : ℝ)) := hN n hNn
    _ ≤ ((primeBand n).card : ℝ) * Real.log (2*B) :=
      mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hlog.le


/-- The dyadic prime supply used in the metric estimate, with an arbitrarily small power loss. -/
theorem metricPrimeSupply : MetricPrimeSupply := by
  intro h hh hhmax ε hε
  let c : ℝ := Real.log 4 / 12
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c / 4, by positivity, ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_dyadicPrimes_lower
  have hlog := (isLittleO_log_rpow_atTop hε).bound zero_lt_one
  filter_upwards [eventually_ge_atTop (max 2 N), hlog] with P hP hsmall
  have hP2 : 2 ≤ P := (le_max_left _ _).trans hP
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  let B := metricPrimeScale P h
  have hbounds : P ≤ B ∧ B ≤ P ^ (2 : ℕ) := metricPrimeScale_bounds hP1 hh.le hhmax
  have hBpos : 0 < B := hPpos.trans_le hbounds.1
  refine ⟨dyadicPrimes B, fun p hp => (mem_dyadicPrimes hBpos.le).mp hp, ?_⟩
  change c / 4 * B * P ^ (-ε) ≤ _
  have hlogB : 0 < Real.log (2*B) := Real.log_pos (by linarith [hbounds.1])
  have hPε : 0 ≤ P ^ ε := Real.rpow_nonneg hPpos.le _
  have hPε1 : 1 ≤ P ^ ε := Real.one_le_rpow hP1 hε.le
  have hlogP : Real.log P ≤ P ^ ε := by
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hP1), abs_of_nonneg hPε] using hsmall
  have hlog2 : Real.log 2 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogUpper : Real.log (2*B) ≤ 4 * P ^ ε := by
    rw [Real.log_mul (by norm_num) hBpos.ne']
    have hmono := Real.log_le_log hBpos hbounds.2
    rw [Real.log_pow] at hmono
    norm_num at hmono
    linarith
  have hBlarge : N ≤ B := ((le_max_right _ _).trans hP).trans hbounds.1
  refine le_trans ?_ (hN B hBlarge)
  change c / 4 * B * P ^ (-ε) ≤ c * B / Real.log (2*B)
  rw [Real.rpow_neg hPpos.le]
  have hrewrite : c / 4 * B * (P ^ ε)⁻¹ = c*B / (4*P^ε) := by
    field_simp
  rw [hrewrite]
  exact div_le_div_of_nonneg_left (by positivity) hlogB hlogUpper

end

end Birch
