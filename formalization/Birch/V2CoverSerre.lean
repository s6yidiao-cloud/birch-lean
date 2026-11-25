import Birch.V2Covers
import Birch.V2FormMoments
import Birch.V2CoverScale
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # The Serre bound for polynomial covers -/

open Filter MeasureTheory MvPolynomial
open scoped ContDiff ENNReal NNReal Polynomial Topology

namespace Birch

noncomputable section

private theorem exists_serreWeight (n : ℕ) :
    ∃ w : (Fin n → ℝ) → ℝ, CompactWeight w ∧ CubeSupported w ∧ ∀ x,
      ‖x‖ ≤ 1 / 2 → w x = 1 := by
  let f : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  refine ⟨f, ⟨f.contDiff, f.hasCompactSupport, f.nonneg'⟩, ?_, ?_⟩
  · intro x hx i
    have hm : x ∈ Function.support (f : (Fin n → ℝ) → ℝ) := hx
    rw [f.support_eq, Metric.mem_ball, dist_zero_right] at hm
    have hi : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    exact hi.trans_lt (hm.trans (by norm_num [f]))
  · intro x hx
    apply f.one_of_mem_closedBall
    simpa [f, Metric.mem_closedBall, dist_zero_right] using hx

private theorem coverIntegralCount_le_weightedBox {n : ℕ} (F : IntForm n) (g : ℤ[X])
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w)
    (hwone : ∀ x, ‖x‖ ≤ 1 / 2 → w x = 1) {P L : ℝ} (hP : 1 ≤ P)
    (hbound : ∀ (x : Fin n → ℤ) (y : ℤ), x ∈ latticeBox n P →
      evalForm F x = g.eval y → |(y : ℝ)| ≤ L) :
    (coverIntegralCount F g P : ℝ) ≤ coverWeightedBoxZeros F g w (2 * P) L := by
  classical
  have hP₀ : 0 < 2 * P := by linarith
  have hboxes : latticeBox n P ⊆ latticeBox n (2 * P) := by
    intro x hx
    apply mem_latticeBox_iff_abs.mpr
    intro i
    exact (mem_latticeBox_iff_abs.mp hx i).trans (by linarith)
  rw [coverIntegralCount, coverIntegralPairs, Finset.card_sigma, Nat.cast_sum]
  unfold coverWeightedBoxZeros
  calc
    _ ≤ ∑ x ∈ latticeBox n P, ∑ y ∈ Finset.Icc (-⌊L⌋) ⌊L⌋,
        if evalForm F x = g.eval y then w (scaledPoint (2 * P) x) else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      let Y := (g - Polynomial.C (evalForm F x)).roots.toFinset
      have hsol {y} (hy : y ∈ Y) : evalForm F x = g.eval y :=
        ((Polynomial.mem_roots_sub_C').mp (Multiset.mem_toFinset.mp hy)).2.symm
      have hsubset : Y ⊆ Finset.Icc (-⌊L⌋) ⌊L⌋ := by
        intro y hy
        have h := hbound x y hx (hsol hy)
        simpa only [Finset.mem_Icc, neg_le, Int.le_floor, Int.cast_neg, ← abs_le] using h
      have hval : w (scaledPoint (2 * P) x) = 1 := by
        apply hwone
        apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
        intro i
        rw [Real.norm_eq_abs, scaledPoint, abs_div, abs_of_pos hP₀, div_le_iff₀ hP₀]
        have hi := mem_latticeBox_iff_abs.mp hx i
        linarith
      change (Y.card : ℝ) ≤ _
      calc
        _ = ∑ _y ∈ Y, (1 : ℝ) := by simp
        _ = ∑ y ∈ Y, if evalForm F x = g.eval y then w (scaledPoint (2 * P) x) else 0 := by
          apply Finset.sum_congr rfl
          intro y hy
          simp [hsol hy, hval]
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ => by
            split_ifs
            · exact hw.nonnegative _
            · exact le_rfl)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hboxes
      (fun _ _ _ => Finset.sum_nonneg fun _ _ => by
        split_ifs
        · exact hw.nonnegative _
        · exact le_rfl)

private theorem normalized_coverIntegralBound {d n e σ : ℕ} {F : IntForm n} {g : ℤ[X]}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hν : 0 < n - σ)
    (hthreshold : (1 / (d : ℝ) + 1 / (2 * e)) * minorDimensionThreshold d ≤
      ((n - σ : ℕ) : ℝ))
    (hF : F.IsHomogeneous d) (hσ : RationalGradientDimension F σ) (hg : g.natDegree = e)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    {B : ℝ} (hB : 1 ≤ B)
    (hCritical : FormCriticalMomentBounds d) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖∫ α, exponentialSum F w P α * coverYSum g (B * P ^ ((d : ℝ) / e)) α ∂circleMeasure‖ ≤
        C * P ^ ((n : ℝ) - 1 + ε) := by
  let f := fun P α => ENNReal.ofReal ‖normalizedSum F w P α‖
  let t := fun P α => ENNReal.ofReal ‖coverYSum g (B * P ^ ((d : ℝ) / e)) α‖
  have hf (P : ℝ) : Measurable (f P) :=
    ((continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)).norm.measurable.ennreal_ofReal
  have ht (P : ℝ) : Measurable (t P) :=
    (continuous_coverYSum g _).norm.measurable.ennreal_ofReal
  obtain ⟨K, hK, hKbound⟩ := norm_normalizedSum_eventually_bounded F hw
  have htriv : ∃ C : ℝ≥0, 0 < C ∧ ∀ᶠ P in atTop, ∀ x, f P x ≤ (C : ℝ≥0∞) :=
    ⟨K.toNNReal, Real.toNNReal_pos.2 hK, hKbound.mono fun _ hP x => by
      rw [ENNReal.ofNNReal_toNNReal]
      exact ENNReal.ofReal_le_ofReal (hP x)⟩
  have hcritical := hCritical hν hd hF hσ hw hwbox
  have hholder := coverSerreIntegralBound_of_criticalMoment hd he hν hthreshold
    circleMeasure f t hf ht htriv hcritical (coverYSum_fourthMoment (by omega) he g hg hB)
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ :=
    ((hholder ε hε).scale (n : ℝ)).toReal
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCbound, eventually_gt_atTop (0 : ℝ)] with P hP hP₀
  let T := coverYSum g (B * P ^ ((d : ℝ) / e))
  have hcont : Continuous (fun α => exponentialSum F w P α * T α) :=
    (continuous_exponentialSum F w P).mul (continuous_coverYSum g _)
  have heq : ENNReal.ofReal (P ^ (n : ℝ)) * (∫⁻ α, f P α * t P α ∂circleMeasure) =
      ∫⁻ α, ENNReal.ofReal ‖exponentialSum F w P α * T α‖ ∂circleMeasure := by
    have hm : Measurable (fun α => f P α * t P α) := (hf P).mul (ht P)
    rw [← lintegral_const_mul _ hm]
    apply lintegral_congr
    intro α
    unfold f t normalizedSum
    rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hP₀.le _),
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hP₀.le _), ← mul_assoc,
      ← Real.rpow_add hP₀, add_neg_cancel, Real.rpow_zero, one_mul,
      ENNReal.ofReal_mul (norm_nonneg _)]
  change (ENNReal.ofReal (P ^ (n : ℝ)) * (∫⁻ α, f P α * t P α ∂circleMeasure)).toReal ≤ _ at hP
  rw [heq, ← integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun _ => norm_nonneg _) hcont.norm.aestronglyMeasurable] at hP
  have hnorm := norm_integral_le_integral_norm (μ := circleMeasure)
    (fun α => exponentialSum F w P α * T α)
  exact hnorm.trans (by simpa only [← add_assoc, sub_eq_add_neg] using hP)

/-- Serre's bound for integral pairs, with an unrestricted cover variable. -/
theorem coverIntegralCount_serre_of_formCriticalMoments {d e n σ : ℕ} {F : IntForm n} {g : ℤ[X]}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hF : F.IsHomogeneous d) (hg : g.natDegree = e)
    (hσ : RationalGradientDimension F σ)
    (hthreshold : (1 / (d : ℝ) + 1 / (2 * (e : ℝ))) * dimensionThreshold d ≤ (n - σ : ℕ))
    (hCritical : FormCriticalMomentBounds d) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (coverIntegralCount F g P : ℝ) ≤ C * P ^ ((n : ℝ) - 1 + ε) := by
  have hthreshold' := hthreshold
  rw [cast_dimensionThreshold_eq_minorDimensionThreshold hd] at hthreshold'
  have hν : 0 < n - σ := by
    have hD : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hE : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
    have hnD := minorDimensionThreshold_pos hd
    exact_mod_cast (show (0 : ℝ) < ↑(n - σ) from
      (mul_pos (by positivity) hnD).trans_le hthreshold')
  obtain ⟨w, hw, hwbox, hwone⟩ := exists_serreWeight n
  obtain ⟨B, hB, hcutoff⟩ := exists_cover_y_bound hF g (by omega) hg
  intro ε hε
  obtain ⟨C, hC, hcount⟩ := normalized_coverIntegralBound hd he hν hthreshold'
    hF hσ hg hw hwbox hB hCritical ε hε
  let a := (n : ℝ) - 1 + ε
  refine ⟨C * (2 : ℝ)^a, by positivity, ?_⟩
  have hscale := Tendsto.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)
    (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hlarge := hscale.eventually hcount
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℝ)] with P hlarge hP
  let L := B * (2 * P) ^ ((d : ℝ) / e)
  have hdata : ∀ (x : Fin n → ℤ) (y : ℤ), x ∈ latticeBox n P → evalForm F x = g.eval y →
      |(y : ℝ)| ≤ L := by
    intro x y hx hy
    refine (hcutoff P hP x y hx hy).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)) (by linarith)
  have hbox := coverIntegralCount_le_weightedBox F g hw hwone hP hdata
  change ‖∫ α, exponentialSum F w (2 * P) α * coverYSum g L α ∂circleMeasure‖ ≤
    C * (2 * P)^a at hlarge
  rw [integral_exponentialSum_mul_coverYSum, Complex.norm_real, Real.norm_eq_abs,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith), ← mul_assoc] at hlarge
  exact hbox.trans ((le_abs_self _).trans hlarge)

theorem coverIntegralCount_serre_of_terminalPrimeBounds {d e n σ : ℕ} {F : IntForm n} {g : ℤ[X]}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hF : F.IsHomogeneous d) (hg : g.natDegree = e)
    (hσ : RationalGradientDimension F σ)
    (hthreshold : (1 / (d : ℝ) + 1 / (2 * (e : ℝ))) * dimensionThreshold d ≤ (n - σ : ℕ))
    (hPrime : TerminalPrimeBounds d) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (coverIntegralCount F g P : ℝ) ≤ C * P ^ ((n : ℝ) - 1 + ε) :=
  coverIntegralCount_serre_of_formCriticalMoments hd he hF hg hσ hthreshold
    (FormCriticalMomentBounds.of_terminalPrimeBounds hPrime)

theorem coverIntegralCount_serre_of_weilII {d e n σ : ℕ} {F : IntForm n} {g : ℤ[X]}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hF : F.IsHomogeneous d) (hg : g.natDegree = e)
    (hσ : RationalGradientDimension F σ)
    (hthreshold : (1 / (d : ℝ) + 1 / (2 * (e : ℝ))) * dimensionThreshold d ≤ (n - σ : ℕ))
    (hWeilII : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    ∀ ε > 0, ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      (coverIntegralCount F g P : ℝ) ≤ C * P ^ ((n : ℝ) - 1 + ε) :=
  coverIntegralCount_serre_of_terminalPrimeBounds hd he hF hg hσ hthreshold (TerminalPrimeBounds.of_deligne hWeilII)

end

end Birch
