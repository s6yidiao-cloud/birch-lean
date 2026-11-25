import Birch.FiniteGramDeconvolution
import Birch.MorseAuxiliaryGram
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Quantitative recovery from the auxiliary correlations -/

open Filter
open scoped Topology BigOperators

namespace Birch

/-- When the exceptional rows and columns are sufficiently sparse, the
correlation margin is at least half the field size and a suitable
auxiliary scale exists. -/
theorem eventually_morseGram_margin (r : ℕ) (B Bprev : ℝ) :
    ∀ᶠ P : ℝ in atTop, ∀ e j : ℕ, (e : ℝ) ≤ P^((1 : ℝ)/8) →
      (j : ℝ) ≤ ((r-1 : ℕ) : ℝ) * P^((1 : ℝ)/8) →
      let L := (j : ℝ) * (r : ℝ)^2
      P/2 ≤ P - Bprev^2 * P^((1 : ℝ)/2) - ((r-1 : ℕ) : ℝ) - L -
        (B^2 * P^((1 : ℝ)/2) + L) * (e : ℝ) ∧
      (((e^2 * (r-1)^2 + 1 : ℕ)) : ℝ) < P := by
  let c : ℝ := (r-1 : ℕ)
  let D : ℝ := Bprev^2 + c + 2*c*(r : ℝ)^2 + B^2 + (c^2+2)
  have hc : 0 ≤ c := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/8)).eventually_ge_atTop (2*D)] with P hP hD
  intro e j he hj L
  have hP₀ : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have h5 : 0 < P^((5 : ℝ)/8) := by positivity
  have h1 : 1 ≤ P^((5 : ℝ)/8) := Real.one_le_rpow hP (by norm_num)
  have h18 : P^((1 : ℝ)/8) ≤ P^((5 : ℝ)/8) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  have h14 : P^((1 : ℝ)/4) ≤ P^((5 : ℝ)/8) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  have h12 : P^((1 : ℝ)/2) ≤ P^((5 : ℝ)/8) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
  have hpow : P^((5 : ℝ)/8) * P^((3 : ℝ)/8) = P := by
    rw [← Real.rpow_add hP₀]
    norm_num
  have hhalf : D * P^((5 : ℝ)/8) ≤ P/2 := by
    have hh := mul_le_mul_of_nonneg_right hD h5.le
    rw [mul_comm (P^((3 : ℝ)/8)), hpow] at hh
    linarith
  have hL : L ≤ c * (r : ℝ)^2 * P^((1 : ℝ)/8) := by
    dsimp [L]
    have h := mul_le_mul_of_nonneg_right hj (sq_nonneg (r : ℝ))
    exact h.trans_eq (by dsimp [c]; ring)
  have hL' : L ≤ c * (r : ℝ)^2 * P^((5 : ℝ)/8) :=
    hL.trans (mul_le_mul_of_nonneg_left h18 (by positivity))
  have hLe : L * (e : ℝ) ≤ c * (r : ℝ)^2 * P^((5 : ℝ)/8) := by
    calc
      _ ≤ (c * (r : ℝ)^2 * P^((1 : ℝ)/8)) * P^((1 : ℝ)/8) :=
        mul_le_mul hL he (by positivity) (by positivity)
      _ = c * (r : ℝ)^2 * P^((1 : ℝ)/4) := by
        rw [mul_assoc _ (P^((1 : ℝ)/8)), ← Real.rpow_add hP₀]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left h14 (by positivity)
  have hBe : (B^2 * P^((1 : ℝ)/2)) * (e : ℝ) ≤ B^2 * P^((5 : ℝ)/8) := by
    calc
      _ ≤ (B^2 * P^((1 : ℝ)/2)) * P^((1 : ℝ)/8) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hP₀]; norm_num
  constructor
  · change P/2 ≤ P - Bprev^2 * P^((1 : ℝ)/2) - c - L -
      (B^2 * P^((1 : ℝ)/2) + L) * (e : ℝ)
    have hp1 := mul_le_mul_of_nonneg_left h12 (sq_nonneg Bprev)
    have hpc := mul_le_mul_of_nonneg_left h1 hc
    have heq : D * P^((5 : ℝ)/8) =
        Bprev^2 * P^((5 : ℝ)/8) + c * P^((5 : ℝ)/8) +
        (c * (r : ℝ)^2 * P^((5 : ℝ)/8)) * 2 + B^2 * P^((5 : ℝ)/8) +
        (c^2 + 2) * P^((5 : ℝ)/8) := by dsimp [D]; ring
    rw [heq] at hhalf
    rw [add_mul]
    linarith [mul_nonneg (show 0 ≤ c^2+2 by positivity) h5.le]
  · push_cast
    change (e : ℝ)^2*c^2+1 < P
    have he2 : (e : ℝ)^2 ≤ P^((1 : ℝ)/4) := by
      calc
        _ ≤ (P^((1 : ℝ)/8))^2 := pow_le_pow_left₀ (by positivity) he 2
        _ = _ := by rw [pow_two, ← Real.rpow_add hP₀]; norm_num
    have he' := mul_le_mul_of_nonneg_right (he2.trans h14) (sq_nonneg c)
    have hD' : c^2+1 ≤ D := by dsimp [D]; nlinarith [mul_nonneg hc (sq_nonneg (r : ℝ))]
    have hx : (e : ℝ)^2*c^2+1 ≤ D*P^((5 : ℝ)/8) := by
      calc
        _ ≤ (c^2+1)*P^((5 : ℝ)/8) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hD' h5.le
    linarith

/-- The finite Gram estimate turns bounds outside the exceptional sets
into a bound at every value once the correlation margin is large enough. -/
theorem abs_le_of_morseGram_and_observed_at_prime {p r : ℕ} [Fact p.Prime] [NeZero p]
    (hr : 3 ≤ r) (hrp : r < p) {B Bprev S : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hcount : PrimeRegularAffineLevelBoundAtDimension r 2 p (B^2))
    (hcountprev : PrimeRegularAffineLevelBoundAtDimension (r-1) 2 p (Bprev^2))
    (E J : Finset (ZMod p)) {scale : ZMod p} (hscale : scale ≠ 0)
    (havoid : let K := AlgebraicClosure (ZMod p)
      ∀ s ∈ E, ∀ v ∈ E, s ≠ v →
        ∀ u ∈ morseAuxiliaryCriticalValues (K := K) r,
          ∀ w ∈ morseAuxiliaryCriticalValues (K := K) r,
            algebraMap (ZMod p) K ((v-s)/scale) ≠ u-w)
    (x : ZMod p → ℝ) (hsmall : ∀ i ∉ E, |x i| ≤ S)
    (hrows : ∀ t ∉ J, |∑ i : ZMod p, x i * centeredMorseValueCount r scale (t-i)| ≤ B*S)
    (hgap : let L := (J.card : ℝ) * (r : ℝ)^2
      (p : ℝ)/2 ≤ (p : ℝ) - Bprev^2 * (p : ℝ)^((1 : ℝ)/2) - ((r-1 : ℕ) : ℝ) - L -
        (B^2 * (p : ℝ)^((1 : ℝ)/2) + L) * (E.card : ℝ)) :
    ∀ i : ZMod p, |x i| ≤ (2*B + 2*r + 1) * (p : ℝ) * S := by
  intro i
  have hp : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hr₀ : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hA : (1 : ℝ) ≤ 2*B + 2*r + 1 := by linarith
  have hAp : (1 : ℝ) ≤ (2*B + 2*r + 1) * (p : ℝ) := one_le_mul_of_one_le_of_one_le hA hp
  by_cases hi : i ∈ E
  · let w (s t : ZMod p) := centeredMorseValueCount r scale (t-s)
    let M := (p : ℝ) - Bprev^2 * (p : ℝ)^((1 : ℝ)/2) - ((r-1 : ℕ) : ℝ)
    let μ := B^2 * (p : ℝ)^((1 : ℝ)/2)
    let L := (J.card : ℝ) * (r : ℝ)^2
    let gap := M - L - (μ+L) * (E.card : ℝ)
    have hhalf : (p : ℝ)/2 ≤ gap := hgap
    have hgap₀ : 0 < gap := lt_of_lt_of_le (by linarith) hhalf
    obtain ⟨hd, ho⟩ := morseAuxiliaryGram_of_curveCounts hr hrp hcount hcountprev E hscale havoid
    have hw (s t : ZMod p) : |w s t| ≤ (r : ℝ) :=
      abs_centeredMorseValueCount_le (by omega) hscale (t-s)
    have hrec := abs_coefficient_le_of_full_gram_bounds E J w x
      (M := M) (μ := μ) (R := (r : ℝ)) (ε := S) (η := B*S)
      (by dsimp [μ]; positivity) (by positivity) hS hw hd ho hsmall hrows hgap₀ i hi
    rw [ZMod.card] at hrec
    let δ := B*S + (p : ℝ)*S*(r : ℝ)
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    change |x i| ≤ Real.sqrt ((p : ℝ) * δ^2 / gap) at hrec
    have hratio : (p : ℝ) * δ^2 / gap ≤ (2*δ)^2 := by
      apply (div_le_iff₀ hgap₀).mpr
      have hh := mul_le_mul_of_nonneg_right hhalf (sq_nonneg δ)
      nlinarith [mul_nonneg hgap₀.le (sq_nonneg δ)]
    refine hrec.trans ((Real.sqrt_le_sqrt hratio).trans ?_)
    rw [Real.sqrt_sq (mul_nonneg (by norm_num) hδ)]
    dsimp [δ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg hB hS),
      mul_nonneg (show 0 ≤ (p : ℝ) by positivity) hS]
  · exact (hsmall i hi).trans (le_mul_of_one_le_left hS hAp)


/-- Apply the finite Gram estimate using uniform regular-level counts. -/
theorem abs_le_of_morseGram_and_observed {p r : ℕ} [Fact p.Prime] [NeZero p]
    (hr : 3 ≤ r) (hrp : r < p) {B Bprev S : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S)
    (hcount : PrimeGoodAffineLevelPointCounts r B)
    (hcountprev : PrimeGoodAffineLevelPointCounts (r-1) Bprev)
    (E J : Finset (ZMod p)) {scale : ZMod p} (hscale : scale ≠ 0)
    (havoid : let K := AlgebraicClosure (ZMod p)
      ∀ s ∈ E, ∀ v ∈ E, s ≠ v →
        ∀ u ∈ morseAuxiliaryCriticalValues (K := K) r,
          ∀ w ∈ morseAuxiliaryCriticalValues (K := K) r,
            algebraMap (ZMod p) K ((v-s)/scale) ≠ u-w)
    (x : ZMod p → ℝ) (hsmall : ∀ i ∉ E, |x i| ≤ S)
    (hrows : ∀ t ∉ J, |∑ i : ZMod p, x i * centeredMorseValueCount r scale (t-i)| ≤ B*S)
    (hgap : let L := (J.card : ℝ) * (r : ℝ)^2
      (p : ℝ)/2 ≤ (p : ℝ) - Bprev^2 * (p : ℝ)^((1 : ℝ)/2) - ((r-1 : ℕ) : ℝ) - L -
        (B^2 * (p : ℝ)^((1 : ℝ)/2) + L) * (E.card : ℝ)) :
    ∀ i : ZMod p, |x i| ≤ (2*B + 2*r + 1) * (p : ℝ) * S :=
  abs_le_of_morseGram_and_observed_at_prime hr hrp hB hS (hcount p hrp 2 le_rfl)
    (hcountprev p (by omega) 2 le_rfl) E J hscale havoid x hsmall hrows hgap

end Birch
