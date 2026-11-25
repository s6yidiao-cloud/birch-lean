import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-!
# Minor-arc exponents for dilated differencing

The distribution estimate in the source attaches two exponents to each terminal degree and
height. The inequalities here put the exceptional-set exponent below a single linear
function of the pointwise exponent throughout the required range.
-/

namespace Birch

noncomputable section

/-- The power saving in the pointwise estimate, denoted (a_r(h)) in the source. -/
def levelExponent (d n r : ℕ) (h : ℝ) : ℝ :=
  (n : ℝ) * h / 2 ^ (d - r)

/-- The exponent (b_r(h)) in the exceptional measure (P^{-d+b_r(h)+arepsilon}). -/
def exceptionExponent (d r : ℕ) (h : ℝ) : ℝ :=
  2 * (r : ℝ) - 4 + (8 - 4 / 2 ^ (d - r)) * h

/-- The height ranges used in the minor-arc argument. -/
def levelAdmissible (d r : ℕ) (h : ℝ) : Prop :=
  2 ≤ r ∧ r < d ∧ 0 < h ∧ h ≤ 1 / 2 ∧ (r = 2 ∨ 1 / 4 ≤ h)

/-- The critical dimension, viewed as a real number for exponent comparisons. -/
def minorDimensionThreshold (d : ℕ) : ℝ :=
  2 ^ (d + 1) - 4

private theorem terminal_pow_bound (r : ℕ) (hr : 2 ≤ r) :
    8 * (r : ℝ) - 8 ≤ (2 : ℝ) ^ (r + 1) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [show r + 1 + 1 = (r + 1) + 1 by rfl, pow_succ, Nat.cast_succ]
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith

/-- The dimension hypothesis places the last pointwise level above the integral's target. -/
theorem degree_lt_topLevel {d n : ℕ} (hd : 3 ≤ d)
    (hn : minorDimensionThreshold d < (n : ℝ)) : (d : ℝ) < n / 4 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hp := terminal_pow_bound d (by omega)
  unfold minorDimensionThreshold at hn
  linarith

private theorem covers_by_power_intervals {v t : ℝ} (hv : 0 < v) (ht : 0 < t)
    (htop : t ≤ v / 4) (j : ℕ) (hj : 1 ≤ j) :
    ∃ k : ℕ, ∃ h : ℝ, 1 ≤ k ∧ k ≤ j ∧ 0 < h ∧ h ≤ 1 / 2 ∧
      (k = j ∨ 1 / 4 ≤ h) ∧ v * h / 2 ^ k = t := by
  induction j, hj using Nat.le_induction with
  | base =>
    refine ⟨1, t * 2 / v, le_rfl, le_rfl, div_pos (by positivity) hv, ?_,
      Or.inl rfl, ?_⟩
    · apply (div_le_iff₀ hv).2
      linarith
    · rw [pow_one]
      field_simp
  | succ j hj ih =>
    let R : ℝ := 2 ^ j
    have hR : 0 < R := by dsimp [R]; positivity
    have hp : (2 : ℝ) ^ (j + 1) = 2 * R := by simp [R, pow_succ, mul_comm]
    by_cases hb : t ≤ v / (4 * R)
    · refine ⟨j + 1, t * (2 * R) / v, by omega, le_rfl, div_pos (by positivity) hv, ?_,
        Or.inl rfl, ?_⟩
      · apply (div_le_iff₀ hv).2
        have h' := (le_div_iff₀ (show 0 < 4 * R by positivity)).1 hb
        linarith
      · rw [hp]
        field_simp
    · obtain ⟨k, h, hk, hkj, hh, hhmax, hmin, heq⟩ := ih
      refine ⟨k, h, hk, by omega, hh, hhmax, Or.inr ?_, heq⟩
      rcases hmin with rfl | hmin
      · have hlow := (div_lt_iff₀ (show 0 < 4 * R by positivity)).1 (lt_of_not_ge hb)
        have hprod := (div_eq_iff (ne_of_gt hR)).1 heq
        by_contra! hsmall
        have hm := mul_lt_mul_of_pos_left hsmall hv
        linarith
      · exact hmin

/-- Every saving in ((0,n/4]) is realized by one of the admissible levels. -/
theorem minorLevels {d n : ℕ} (hd : 3 ≤ d) (hn : 0 < n)
    {t : ℝ} (ht : 0 < t) (htop : t ≤ (n : ℝ) / 4) :
    ∃ r h, levelAdmissible d r h ∧ levelExponent d n r h = t := by
  obtain ⟨k, h, hk, hkd, hh, hhmax, hmin, heq⟩ :=
    covers_by_power_intervals (by exact_mod_cast hn) ht htop (d - 2) (by omega)
  refine ⟨d - k, h, ⟨by omega, by omega, hh, hhmax, ?_⟩, ?_⟩
  · exact hmin.imp (fun hkj => by omega) id
  · unfold levelExponent
    rwa [show d - (d - k) = k by omega]

/-- Over the full minor-arc range the exceptional exponent is bounded by the pointwise
exponent times the critical dimension divided by the actual dimension. -/
theorem exceptionExponent_le {d n r : ℕ} {h : ℝ} (hn : 0 < n)
    (ha : levelAdmissible d r h) :
    exceptionExponent d r h ≤ minorDimensionThreshold d / n * levelExponent d n r h := by
  obtain ⟨hr, hrd, hh, _, hmin⟩ := ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let R : ℝ := 2 ^ (d - r)
  have hR : 0 < R := by dsimp [R]; positivity
  have hpow : (2 : ℝ) ^ (d + 1) = R * 2 ^ (r + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hgap : 2 * (r : ℝ) - 4 ≤ ((2 : ℝ) ^ (r + 1) - 8) * h := by
    rcases hmin with rfl | hmin
    · norm_num
    · have hp := terminal_pow_bound r hr
      have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      have hcoef : 0 ≤ (2 : ℝ) ^ (r + 1) - 8 := by linarith
      have hm := mul_le_mul_of_nonneg_left hmin hcoef
      linarith
  unfold exceptionExponent minorDimensionThreshold levelExponent
  change 2 * (r : ℝ) - 4 + (8 - 4 / R) * h ≤
    ((2 : ℝ) ^ (d + 1) - 4) / n * ((n : ℝ) * h / R)
  rw [hpow]
  have heq : (R * (2 : ℝ) ^ (r + 1) - 4) / n * ((n : ℝ) * h / R) -
      (2 * (r : ℝ) - 4 + (8 - 4 / R) * h) =
      ((2 : ℝ) ^ (r + 1) - 8) * h - (2 * (r : ℝ) - 4) := by
    field_simp
    ring
  linarith

open Filter MeasureTheory
open scoped BigOperators ENNReal

universe u

/-- An explicit mesh with one common saving. Its construction is independent of
the functions and their distribution constants. -/
private theorem minorMesh {d n : ℕ} {σ : ℝ} (hd : 3 ≤ d)
    (hn : minorDimensionThreshold d < (n : ℝ)) (hσ : 0 < σ) :
    ∃ η > 0, ∃ ε > 0, ∃ N : ℕ, ∃ t : ℕ → ℝ,
      t 0 ≤ σ ∧ t N = (n : ℝ) / 4 ∧ (d : ℝ) + η ≤ t N ∧
      (∀ j ≤ N, 0 < t j ∧ t j ≤ (n : ℝ) / 4) ∧
      ∀ j < N, minorDimensionThreshold d / n * t (j + 1) + ε + η ≤ t j := by
  have htop := degree_lt_topLevel hd hn
  let A : ℝ := (n : ℝ) / 4
  have hA : 0 < A := by
    dsimp [A]
    have hd' : (0 : ℝ) ≤ d := by positivity
    linarith
  have hn' : (0 : ℝ) < n := by
    dsimp [A] at hA
    linarith
  let a := min (σ / 2) (A / 2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haσ : a ≤ σ := (min_le_left _ _).trans (by linarith)
  have haA : a < A := (min_le_right _ _).trans_lt (by linarith)
  let c := minorDimensionThreshold d / n
  have hc : 0 < 1 - c := by
    have h' : c < 1 := (div_lt_iff₀ hn').2 (by simpa using hn)
    linarith
  let g := (1 - c) * a
  have hg : 0 < g := mul_pos hc ha
  let η := min (g / 4) ((A - d) / 2)
  have hη : 0 < η := lt_min (by positivity) (by dsimp [A]; linarith)
  have hηg : η ≤ g / 4 := min_le_left _ _
  have hηA : (d : ℝ) + η ≤ A := by
    have h' : η ≤ (A - d) / 2 := min_le_right _ _
    change (d : ℝ) < A at htop
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((A - a) / (g / 4))
  have hNpos : (0 : ℝ) < N :=
    (div_pos (sub_pos.mpr haA) (by positivity)).trans hN
  let e := (A - a) / N
  have he : 0 < e := div_pos (sub_pos.mpr haA) hNpos
  have heg : e < g / 4 := by
    apply (div_lt_iff₀ hNpos).2
    have h' := (div_lt_iff₀ (show 0 < g / 4 by positivity)).1 hN
    simpa [mul_comm] using h'
  let t : ℕ → ℝ := fun j => a + (j : ℝ) * e
  have ht0 : t 0 = a := by simp [t]
  have htN : t N = A := by
    dsimp [t, e]
    field_simp
    ring
  have htmon : Monotone t := fun _ _ hj => by
    dsimp [t]
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) he.le
  refine ⟨η, hη, g / 4, by positivity, N, t, ht0 ▸ haσ, htN, htN ▸ hηA, ?_, ?_⟩
  · intro j hj
    constructor
    · exact ha.trans_le (ht0 ▸ htmon (Nat.zero_le j))
    · exact (htmon hj).trans_eq htN
  · intro j hj
    change c * t (j + 1) + g / 4 + η ≤ t j
    have hstep : t (j + 1) = t j + e := by simp only [t, Nat.cast_add, Nat.cast_one]; ring
    have hge : g ≤ (1 - c) * t (j + 1) :=
      mul_le_mul_of_nonneg_left (ht0 ▸ htmon (Nat.zero_le _)) hc.le
    rw [sub_mul, one_mul] at hge
    linarith

/-- Pointwise bound by the last threshold and all the crossed thresholds. -/
private theorem threshold_bound {x : ℝ≥0∞} (T : ℕ → ℝ≥0∞) (h₀ : x ≤ T 0)
    (N : ℕ) :
    x ≤ T N + ∑ j ∈ Finset.range N, if T (j + 1) < x then T j else 0 := by
  induction N with
  | zero => simpa using h₀
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases h : x ≤ T (N + 1)
    · exact h.trans le_self_add
    · rw [ite_eq_left (lt_of_not_ge h)]
      calc
        x ≤ T N + ∑ j ∈ Finset.range N, if T (j + 1) < x then T j else 0 := ih
        _ ≤ _ := by
          rw [add_comm (∑ j ∈ Finset.range N, if T (j + 1) < x then T j else 0)]
          exact le_add_left le_rfl

/-- For a finite mesh, bound the integral by the final threshold and the exceptional
measure at each successive threshold, times the preceding threshold. -/
theorem lintegral_threshold_bound {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : Set Ω} (hm : MeasurableSet m)
    {f : Ω → ℝ≥0∞} (hf : Measurable f) (T : ℕ → ℝ≥0∞)
    (h₀ : ∀ x ∈ m, f x ≤ T 0) (N : ℕ) :
    (∫⁻ x in m, f x ∂μ) ≤
      T N + ∑ j ∈ Finset.range N, T j * μ {x | T (j + 1) < f x} := by
  let E : ℕ → Set Ω := fun j => {x | T (j + 1) < f x}
  let G : ℕ → Ω → ℝ≥0∞ := fun j => (E j).indicator (fun _ => T j)
  have hE : ∀ j, MeasurableSet (E j) := fun _ => measurableSet_lt measurable_const hf
  have hG : ∀ j, Measurable (G j) := fun j => measurable_const.indicator (hE j)
  calc
    (∫⁻ x in m, f x ∂μ) ≤ ∫⁻ x in m, T N + ∑ j ∈ Finset.range N, G j x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hm (μ := μ)] with x hx
      have hGx (j : ℕ) : G j x = if T (j + 1) < f x then T j else 0 := by
        by_cases hj : T (j + 1) < f x <;> simp [G, E, hj]
      simp_rw [hGx]
      exact threshold_bound T (h₀ x hx) N
    _ = T N * (μ.restrict m) Set.univ +
        ∑ j ∈ Finset.range N, T j * (μ.restrict m) (E j) := by
      rw [lintegral_add_left measurable_const, lintegral_const, lintegral_finsetSum]
      · apply congrArg (fun z => T N * (μ.restrict m) Set.univ + z)
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [G]
        rw [lintegral_indicator (hE j), setLIntegral_const]
      · intro j _
        exact hG j
    _ ≤ T N + ∑ j ∈ Finset.range N, T j * μ (E j) := by
      apply add_le_add
      · simpa using mul_le_mul_right (Measure.restrict_le_self (s := m) (μ := μ) Set.univ) (T N)
      · exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_right (Measure.restrict_le_self (s := m) (μ := μ) (E j)) (T j)

/-- The minor-arc power saving from the initial pointwise bound and the metric
distribution bounds. The saving is chosen using only the dimensions and the initial
saving. Each level's constants and eventual scale can be chosen independently. -/
theorem minorArcs_of_distribution_of_exception_le {d n : ℕ} {σ : ℝ}
    {b : ℕ → ℝ → ℝ} (hd : 3 ≤ d)
    (hn : minorDimensionThreshold d < (n : ℝ)) (hσ : 0 < σ)
    (hcomparison : ∀ r h, levelAdmissible d r h →
      b r h ≤ minorDimensionThreshold d / n * levelExponent d n r h) :
    ∃ η > 0, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (m : ℝ → Set Ω) (f : ℝ → Ω → ℝ),
      (∀ P, MeasurableSet (m P)) →
      (∀ P, Measurable (f P)) →
      (∀ P x, 0 ≤ f P x) →
      (∃ C > 0, ∀ᶠ P in atTop, ∀ x ∈ m P, f P x ≤ C * P ^ (-σ)) →
      (∀ r h, levelAdmissible d r h → ∀ ε > 0, ∃ C > 0, ∃ K > 0,
        ∀ᶠ P in atTop,
          μ {x | C * P ^ (-levelExponent d n r h) < f P x} ≤
            ENNReal.ofReal (K * P ^ (-(d : ℝ) + b r h + ε))) →
      ∃ K > 0, ∀ᶠ P in atTop, (∫ x in m P, f P x ∂μ) ≤ K * P ^ (-(d : ℝ) - η) := by
  classical
  obtain ⟨η, hη, ε, hε, N, t, ht0, _, htop, ht, hstep⟩ := minorMesh hd hn hσ
  refine ⟨η, hη, ?_⟩
  intro Ω _ μ _ m f hm hf hnonneg hinitial hmetric
  obtain ⟨A₀, hA₀, hinitial⟩ := hinitial
  have hn₀ : 0 < n := by
    have htop' := degree_lt_topLevel hd hn
    have hd' : (0 : ℝ) ≤ d := by positivity
    exact_mod_cast (show (0 : ℝ) < (n : ℝ) by linarith)
  let c := minorDimensionThreshold d / n
  have htail : ∀ i : Fin (N + 1), ∃ A > 0, ∃ B > 0, ∀ᶠ P in atTop,
      μ {x | A * P ^ (-t i) < f P x} ≤
        ENNReal.ofReal (B * P ^ (-(d : ℝ) + c * t i + ε)) := by
    intro i
    obtain ⟨r, h, hrh, heq⟩ := minorLevels hd hn₀ (ht i (by omega)).1 (ht i (by omega)).2
    obtain ⟨A, hA, B, hB, hdist⟩ := hmetric r h hrh ε hε
    refine ⟨A, hA, B, hB, ?_⟩
    filter_upwards [hdist, eventually_ge_atTop (1 : ℝ)] with P hP hP₁
    rw [heq] at hP
    refine hP.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hB.le))
    apply Real.rpow_le_rpow_of_exponent_le hP₁
    have hbound := hcomparison r h hrh
    rw [heq] at hbound
    change b r h ≤ c * t i at hbound
    linarith
  choose A hA B hB hdist using htail
  let C := A₀ + ∑ i, A i
  let D := ∑ i, B i
  have hC : 0 < C := add_pos_of_pos_of_nonneg hA₀ (Finset.sum_nonneg fun i _ => (hA i).le)
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => (hB i).le
  have hA₀C : A₀ ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (hA i).le)
  have hAC (i : Fin (N + 1)) : A i ≤ C :=
    (Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left hA₀.le)
  have hBD (i : Fin (N + 1)) : B i ≤ D :=
    Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
  let L := C + ∑ _j ∈ Finset.range N, C * D
  have hL : 0 < L := add_pos_of_pos_of_nonneg hC
    (Finset.sum_nonneg fun _ _ => mul_nonneg hC.le hD)
  refine ⟨L, hL, ?_⟩
  filter_upwards [hinitial, Filter.eventually_all.2 hdist, eventually_ge_atTop (1 : ℝ)]
    with P hstart hall hP
  have hPr (z : ℝ) : 0 ≤ P ^ z := Real.rpow_nonneg (by linarith) _
  have hPpos : 0 < P := by linarith
  let T : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (C * P ^ (-t j))
  have hT₀ : ∀ x ∈ m P, ENNReal.ofReal (f P x) ≤ T 0 := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    calc
      f P x ≤ A₀ * P ^ (-σ) := hstart x hx
      _ ≤ C * P ^ (-σ) := mul_le_mul_of_nonneg_right hA₀C (hPr _)
      _ ≤ C * P ^ (-t 0) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) hC.le
  have hterm (j : ℕ) (hj : j ∈ Finset.range N) :
      T j * μ {x | T (j + 1) < ENNReal.ofReal (f P x)} ≤
        ENNReal.ofReal (C * D * P ^ (-(d : ℝ) - η)) := by
    let i : Fin (N + 1) := ⟨j + 1, by have := Finset.mem_range.1 hj; omega⟩
    have hsub :
        {x | T (j + 1) < ENNReal.ofReal (f P x)} ⊆
          {x | A i * P ^ (-t i) < f P x} := by
      intro x hx
      change ENNReal.ofReal (C * P ^ (-t i)) < ENNReal.ofReal (f P x) at hx
      have hcross : C * P ^ (-t i) < f P x := lt_of_not_ge fun h =>
        (not_le_of_gt hx) (ENNReal.ofReal_le_ofReal h)
      exact (mul_le_mul_of_nonneg_right (hAC i) (hPr _)).trans_lt hcross
    have hm' := (measure_mono hsub).trans (hall i)
    have hexp : -t j + (-(d : ℝ) + c * t i + ε) ≤ -(d : ℝ) - η := by
      have hs := hstep j (Finset.mem_range.1 hj)
      change c * t i + ε + η ≤ t j at hs
      linarith
    calc
      T j * μ {x | T (j + 1) < ENNReal.ofReal (f P x)} ≤
          T j * ENNReal.ofReal (B i * P ^ (-(d : ℝ) + c * t i + ε)) :=
        mul_le_mul_right hm' _
      _ = ENNReal.ofReal (C * B i * P ^ (-t j + (-(d : ℝ) + c * t i + ε))) := by
        dsimp [T]
        rw [← ENNReal.ofReal_mul (mul_nonneg hC.le (hPr _)),
          Real.rpow_add hPpos (-t j) (-(d : ℝ) + c * t i + ε)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (C * D * P ^ (-(d : ℝ) - η)) := by
        exact ENNReal.ofReal_le_ofReal (mul_le_mul
          (mul_le_mul_of_nonneg_left (hBD i) hC.le)
          (Real.rpow_le_rpow_of_exponent_le hP hexp)
          (hPr _) (mul_nonneg hC.le hD))
  let q : ℝ := P ^ (-(d : ℝ) - η)
  have hq : 0 ≤ q := hPr _
  have hTf : T N ≤ ENNReal.ofReal (C * q) := ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) hC.le)
  have hb : (∫⁻ x in m P, ENNReal.ofReal (f P x) ∂μ) ≤ ENNReal.ofReal (L * q) := by
    calc
      _ ≤ T N + ∑ j ∈ Finset.range N,
          T j * μ {x | T (j + 1) < ENNReal.ofReal (f P x)} :=
        lintegral_threshold_bound μ (hm P) (ENNReal.measurable_ofReal.comp (hf P)) T hT₀ N
      _ ≤ ENNReal.ofReal (C * q) + ∑ _j ∈ Finset.range N, ENNReal.ofReal (C * D * q) :=
        add_le_add hTf (Finset.sum_le_sum hterm)
      _ = ENNReal.ofReal (L * q) := by
        have hsum : L * q = C * q + ∑ _j ∈ Finset.range N, C * D * q := by
          change (C + ∑ _j ∈ Finset.range N, C * D) * q = _
          rw [add_mul, Finset.sum_mul]
        have hnonneg' : ∀ j ∈ Finset.range N, 0 ≤ C * D * q :=
          fun _ _ => mul_nonneg (mul_nonneg hC.le hD) hq
        rw [hsum, ENNReal.ofReal_add (mul_nonneg hC.le hq) (Finset.sum_nonneg hnonneg'),
          ENNReal.ofReal_sum_of_nonneg hnonneg']
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnonneg P))
    (hf P).aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hL.le hq))

/-- The manuscript's exceptional exponents supply the distribution estimates
for the original minor-arc argument. -/
theorem minorArcs_of_distribution {d n : ℕ} {σ : ℝ} (hd : 3 ≤ d)
    (hn : minorDimensionThreshold d < (n : ℝ)) (hσ : 0 < σ) :
    ∃ η > 0, ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (m : ℝ → Set Ω) (f : ℝ → Ω → ℝ),
      (∀ P, MeasurableSet (m P)) →
      (∀ P, Measurable (f P)) →
      (∀ P x, 0 ≤ f P x) →
      (∃ C > 0, ∀ᶠ P in atTop, ∀ x ∈ m P, f P x ≤ C * P ^ (-σ)) →
      (∀ r h, levelAdmissible d r h → ∀ ε > 0, ∃ C > 0, ∃ K > 0,
        ∀ᶠ P in atTop,
          μ {x | C * P ^ (-levelExponent d n r h) < f P x} ≤
            ENNReal.ofReal (K * P ^ (-(d : ℝ) + exceptionExponent d r h + ε))) →
      ∃ K > 0, ∀ᶠ P in atTop, (∫ x in m P, f P x ∂μ) ≤ K * P ^ (-(d : ℝ) - η) := by
  have htop : (d : ℝ) < (n : ℝ) / 4 := degree_lt_topLevel hd hn
  have hn₀ : 0 < n := by
    exact_mod_cast (show (0 : ℝ) < (n : ℝ) by linarith)
  exact minorArcs_of_distribution_of_exception_le hd hn hσ
    (fun _ _ ha => exceptionExponent_le hn₀ ha)

end

end Birch
