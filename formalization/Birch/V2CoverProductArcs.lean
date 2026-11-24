import Birch.V2CoverProduct

/-!
# Concrete arc approximations for the cover product

The joint Poisson and interval approximation specializes to the fixed-width
major arcs and to the small frequencies used to estimate the real tail.
-/

namespace Birch

open Filter MeasureTheory
open scoped ComplexConjugate Polynomial Topology

noncomputable section

/-- The normalized cover product has period one in the frequency. -/
theorem coverNormalizedProduct_periodic {n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (P Y L : ℝ) :
    Function.Periodic (coverNormalizedProduct F g w P Y L) 1 :=
  normalizedCoverProduct_periodic F g w P Y L

/-- The error on the fixed-width major arcs is uniform in the denominator
and numerator. Its exponent leaves room for summing the major intervals. -/
theorem coverNormalizedProduct_approx_majorArcs {n d e : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) (g : ℤ[X]) (he : 0 < e) (hg : g.natDegree = e)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    {B : ℝ} (hB : 0 < B) :
    let Δ := coverMajorArcExponent d e
    ∃ E > 0, ∀ᶠ P : ℝ in atTop, ∀ (q : ℕ) (a : ℤ), 0 < q → (q : ℝ) ≤ P ^ Δ →
      ∀ α ∈ fixedWidthMajorInterval (P ^ (-(d : ℝ) + Δ)) q a,
        let Y := P ^ ((d : ℝ) / e)
        let γ := P ^ d * (α - (a : ℝ) / q)
        ‖coverNormalizedProduct F g w P Y (B * Y) α -
          coverCompleteProductAt F g q a *
            (realOscillation F w γ * coverRealOscillationOn g e B γ)‖ ≤
          E * P ^ (-(10 * Δ)) := by
  let Δ := coverMajorArcExponent d e
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ, coverMajorArcExponent]
    exact div_nonneg (le_min zero_le_one (by positivity)) (by norm_num)
  obtain ⟨E, hE, happrox⟩ := coverNormalizedProduct_approx_smallHeight hF g he hg hw hwbox hB
  refine ⟨E, hE, ?_⟩
  filter_upwards [happrox, eventually_ge_atTop (1 : ℝ)] with P hP hP₁
  intro q a hq hqQ α hα
  letI : NeZero q := ⟨hq.ne'⟩
  have hp : 0 < P := zero_lt_one.trans_le hP₁
  let γ := P ^ d * (α - (a : ℝ) / q)
  let Q := P ^ Δ
  have hQ : 1 ≤ Q := Real.one_le_rpow hP₁ hΔ
  have hγ : |γ| ≤ Q := by
    dsimp only [γ, Q]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hp.le _)]
    refine (mul_le_mul_of_nonneg_left (mem_fixedWidthMajorInterval.mp hα)
      (pow_nonneg hp.le _)).trans_eq ?_
    rw [← Real.rpow_natCast P d, ← Real.rpow_add hp]
    congr 1
    ring
  have hheight : (1 + |γ|) * (q : ℝ) ≤ 4 * P ^ (2 * Δ) := by
    have hpos : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    calc
      _ ≤ (1 + Q) * Q := mul_le_mul (add_le_add_right hγ _) hqQ hpos (by linarith)
      _ ≤ 4 * (Q * Q) := by nlinarith [mul_nonneg (show 0 ≤ Q by linarith) (sub_nonneg.mpr hQ)]
      _ = _ := by
        dsimp only [Q]
        rw [← Real.rpow_add hp]
        congr 2
        ring
  have hαeq : (a : ℝ) / q + γ / P ^ d = α := by
    dsimp only [γ]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hp.ne')]
    ring
  simpa only [hαeq] using hP q a γ hheight

/-- The approximation at denominator one has a power error in the form
factor and the original interval error in the cover factor. -/
theorem coverNormalizedProduct_approx_realFrequency {n d e : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) (g : ℤ[X]) (he : 0 < e) (hg : g.natDegree = e)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    {B : ℝ} (hB : 0 < B) :
    let a := min 1 ((d : ℝ) / e) / 3
    ∃ E > 0, ∀ᶠ P : ℝ in atTop, ∀ γ : ℝ, |γ| ≤ 2 * P ^ a →
      let Y := P ^ ((d : ℝ) / e)
      ‖coverNormalizedProduct F g w P Y (B * Y) (γ / P ^ d) -
          realOscillation F w γ * coverRealOscillationOn g e B γ‖ ≤
        E * ((1 + |γ|) / Y + P ^ (-1 : ℝ)) := by
  let a := min 1 ((d : ℝ) / e) / 3
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have ha : a ≤ 1 / 3 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hPoisson := majorArcPoissonIdentity_of_smooth_cubeSupported hF hw.smooth hw.compact hwbox
  obtain ⟨E, hE, happrox⟩ := coverNormalizedProduct_approx_of_poisson_ratio g he hg hw hPoisson
    hB (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 2 / 3) 1
  refine ⟨E, hE, ?_⟩
  filter_upwards [happrox, eventually_ge_atTop (1 : ℝ)] with P hP hP₁
  intro γ hγ
  have hp : 0 < P := zero_lt_one.trans_le hP₁
  have hPa : 1 ≤ P ^ a := Real.one_le_rpow hP₁ ha₀
  have hratio : (1 + |γ|) / (P / (1 : ℕ)) ≤ 3 * P ^ (-(2 / 3 : ℝ)) := by
    rw [Nat.cast_one, div_one]
    calc
      _ ≤ (3 * P ^ a) / P := div_le_div_of_nonneg_right (by linarith) hp.le
      _ = 3 * P ^ (a - 1) := by
        rw [Real.rpow_sub hp, Real.rpow_one, mul_div_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)) (by norm_num)
  have h1 : coverCompleteProductAt F g 1 (0 : ℤ) = 1 := by
    rw [coverCompleteProductAt_eq, ← completeSum_coverPolynomial, completeSum_one]
  have h := hP 1 0 γ hratio
  simpa only [Nat.cast_one, Int.cast_zero, zero_div, zero_add, h1, one_mul, mul_one_div,
    add_comm (P ^ (-1 : ℝ))] using h

private theorem phase_neg_eq_conj (t : ℝ) : phase (-t) = conj (phase t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  have htwo : conj (2 : ℂ) = 2 := Complex.conj_natCast 2
  simp only [map_mul, htwo, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem realOscillation_neg_eq_conj {n : ℕ} (F : IntForm n)
    (w : (Fin n → ℝ) → ℝ) (γ : ℝ) :
    realOscillation F w (-γ) = conj (realOscillation F w γ) := by
  unfold realOscillation
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  rw [map_mul, Complex.conj_ofReal, ← phase_neg_eq_conj, neg_mul]

theorem coverRealOscillationOn_neg_eq_conj (g : ℤ[X]) (e : ℕ) (B γ : ℝ) :
    coverRealOscillationOn g e B (-γ) = conj (coverRealOscillationOn g e B γ) := by
  unfold coverRealOscillationOn
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro t _
  change phase (-(-γ) * (g.leadingCoeff : ℝ) * t ^ e) =
    conj (phase (-γ * (g.leadingCoeff : ℝ) * t ^ e))
  rw [← phase_neg_eq_conj]
  congr 1
  ring

/-- The absolute value of the limiting real product is even. -/
theorem norm_coverRealProduct_even {n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (e : ℕ) (B γ : ℝ) :
    ‖realOscillation F w (-γ) * coverRealOscillationOn g e B (-γ)‖ =
      ‖realOscillation F w γ * coverRealOscillationOn g e B γ‖ := by
  rw [realOscillation_neg_eq_conj, coverRealOscillationOn_neg_eq_conj, ← map_mul]
  exact Complex.norm_conj _

end

end Birch
