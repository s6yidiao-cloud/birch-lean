import Birch.V2CoverAsymptoticAssembly
import Birch.V2CoverMajorTails
import Birch.V2CoverMomentReduction
import Birch.V2CoverProductArcs
import Birch.V2CoverRealTail

/-! # The weighted cover asymptotic from the one-variable moment -/

open Filter MeasureTheory Set
open scoped Polynomial Topology

namespace Birch

noncomputable section

private def coverThreshold (d q n σ : ℕ) : Prop :=
  (1 - 1 / (q : ℝ)) * dimensionThreshold d < (n - σ : ℕ)

private theorem exists_uniformCoverMinorSaving {n d e q : ℕ} (hd : 2 ≤ d) (he : 2 ≤ e)
    (hq : 1 < q)
    (hWeil : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r) :
    let Δ := coverMajorArcExponent d e
    ∃ η > 0, η ≤ Δ ∧ ∀ (σ : ℕ), coverThreshold d q n σ →
      ∀ (F : IntForm n) (g : ℤ[X]) (w : (Fin n → ℝ) → ℝ),
        F.IsHomogeneous d → RationalGradientDimension F σ → CompactWeight w →
        CubeSupported w → CoverMeanValueBoundAtExponent e q g → ∀ B > 0, ∃ C > 0,
        ∀ᶠ P : ℝ in atTop,
          (∫ α in (v2MajorArcs d Δ P)ᶜ,
            ‖normalizedSum F w P α * coverYSum g (B * P^((d : ℝ)/e)) α‖ ∂circleMeasure) ≤
            C * P^((d : ℝ)/e-d-η) := by
  classical
  let Δ := coverMajorArcExponent d e
  have hΔ : 0 < Δ := coverMajorArcExponent_pos (by omega) (by omega)
  let P (σ : ℕ) (η : ℝ) : Prop := ∀ (F : IntForm n) (g : ℤ[X]) (w : (Fin n → ℝ) → ℝ),
    F.IsHomogeneous d → RationalGradientDimension F σ → CompactWeight w →
    CubeSupported w → CoverMeanValueBoundAtExponent e q g → ∀ B > 0, ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      (∫ α in (v2MajorArcs d Δ X)ᶜ,
        ‖normalizedSum F w X α * coverYSum g (B * X^((d : ℝ)/e)) α‖ ∂circleMeasure) ≤
        C * X^((d : ℝ)/e-d-η)
  have hs : ∀ σ, ∃ η > 0, coverThreshold d q n σ → P σ η := by
    intro σ
    by_cases hν : coverThreshold d q n σ
    · obtain ⟨δ,hδ,h⟩ := v2CoverMinorIntegral_of_weilII_atExponent hd he hq hν hWeil
      exact ⟨δ,hδ,fun _ => h⟩
    · exact ⟨1,zero_lt_one,fun h => (hν h).elim⟩
  choose η hη hsaving using hs
  let S := Finset.range (n+1)
  have hS : S.Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  let δ := min Δ (S.inf' hS η)
  have hδ : 0 < δ := lt_min hΔ ((Finset.lt_inf'_iff hS).2 (fun s _ => hη s))
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro σ hσ F g w hF hFσ hw hwbox hg B hB
  have hnonneg : (0 : ℝ) ≤ (1 - 1/(q : ℝ)) * dimensionThreshold d := by
    have hm : (1 : ℝ) < q := by exact_mod_cast hq
    exact mul_nonneg (sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le zero_lt_one hm.le))
      (Nat.cast_nonneg _)
  have hnσ : 0 < n - σ := by
    exact_mod_cast (show (0 : ℝ) < ((n - σ : ℕ) : ℝ) from hnonneg.trans_lt hσ)
  have hmem : σ ∈ S := Finset.mem_range.mpr (by omega)
  have hδle : δ ≤ η σ := (min_le_right _ _).trans (Finset.inf'_le η hmem)
  obtain ⟨C,hC,hest⟩ := hsaving σ hσ F g w hF hFσ hw hwbox hg B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hest, eventually_ge_atTop (1 : ℝ)] with X hX hX₁
  exact hX.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX₁ (by linarith)) hC.le)

private theorem coverMajorIntegral_unnormalize {n d e : ℕ} {F : IntForm n} {g : ℤ[X]}
    {w : (Fin n → ℝ) → ℝ} {B δ C : ℝ}
    (h : ∀ᶠ P : ℝ in atTop,
      let Y := P^((d : ℝ)/e)
      ‖(∫ α in v2MajorArcs d (coverMajorArcExponent d e) P,
          coverNormalizedProduct F g w P Y (B*Y) α ∂circleMeasure) -
          (P^(-(d : ℝ)) : ℝ) •
            (coverSingularSeries F g * coverSingularIntegralOn F g e w B)‖ ≤ C * P^(-(d : ℝ)-δ)) :
    ∀ᶠ P : ℝ in atTop,
      ‖(∫ α in v2MajorArcs d (coverMajorArcExponent d e) P,
          normalizedSum F w P α * coverYSum g (B*P^((d : ℝ)/e)) α ∂circleMeasure) -
          (P^((d : ℝ)/e-d) : ℝ) •
            (coverSingularSeries F g * coverSingularIntegralOn F g e w B)‖ ≤ C * P^((d : ℝ)/e-d-δ) := by
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with P hP hp
  let k := (d : ℝ)/e
  let Y := P^k
  have hY : 0 < Y := Real.rpow_pos_of_pos hp _
  have heq (α : ℝ) : normalizedSum F w P α * coverYSum g (B*Y) α =
      Y • coverNormalizedProduct F g w P Y (B*Y) α := by
    rw [coverNormalizedProduct, Algebra.smul_def]
    change _ = (Y : ℂ) * (normalizedSum F w P α * ((Y : ℂ)⁻¹ * coverYSum g (B*Y) α))
    have hh : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
    field_simp
  have hpow : P^(k-d) = Y * P^(-(d : ℝ)) := by
    change P^(k-d) = P^k * P^(-(d : ℝ))
    rw [← Real.rpow_add hp, sub_eq_add_neg]
  change ‖(∫ α in _, normalizedSum F w P α * coverYSum g (B*Y) α ∂circleMeasure) -
      (P^(k-d) : ℝ) • (coverSingularSeries F g * coverSingularIntegralOn F g e w B)‖ ≤ _
  simp_rw [heq, integral_smul]
  rw [hpow, ← smul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hY]
  refine (mul_le_mul_of_nonneg_left hP hY.le).trans_eq ?_
  dsimp only [Y, k]
  rw [mul_left_comm, ← Real.rpow_add hp]
  congr 2
  ring

/-- The cover asymptotic on the unit cube at the threshold associated with the
given one-variable moment. -/
theorem v2CoverCubeAsymptoticAtExponent_of_weilII_of_coverMoment {n d e q : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e) (hq : 1 < q)
    (hWeil : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r)
    (hmoment : ∀ g : ℤ[X], g.natDegree = e → CoverMeanValueBoundAtExponent e q g) :
    V2CoverCubeAsymptoticAtExponent d e n q := by
  let k := (d : ℝ)/e
  let Δ := coverMajorArcExponent d e
  let a := min 1 k / 3
  have hΔ : 0 < Δ := coverMajorArcExponent_pos (by omega) (by omega)
  have hΔ₁ : Δ ≤ 1/4 := (coverMajorArcExponent_lt_quarter d e).le
  have hk : 0 < k := by
    dsimp only [k]
    exact div_pos (by exact_mod_cast (show 0 < d by omega)) (by exact_mod_cast (show 0 < e by omega))
  have ha : 0 < a := div_pos (lt_min zero_lt_one hk) (by norm_num)
  obtain ⟨η,hη,hηΔ,hminor⟩ := exists_uniformCoverMinorSaving (n := n) hd he hq hWeil
  let γ := η / (2*Δ)
  let τ := min η a / a
  let ξ := min (10*Δ-3*Δ) (min (γ*Δ) (τ*Δ))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hτ : 0 < τ := div_pos (lt_min hη ha) ha
  have hξ : 0 < ξ := lt_min (by linarith) (lt_min (mul_pos hγ hΔ) (mul_pos hτ hΔ))
  refine ⟨min η ξ, lt_min hη hξ, ?_⟩
  intro F g σ w _ hF hg hσ hν hw hwbox B hB
  have he₀ : 0 < e := by omega
  have hmg := hmoment g hg
  let f P := coverNormalizedProduct F g w P (P^k) (B*P^k)
  let I t := realOscillation F w t * coverRealOscillationOn g e B t
  have hf P : Continuous (f P) := continuous_coverNormalizedProduct F g w _ _ _
  have hIc : Continuous I :=
    (continuous_realOscillation_of_compact F hw.smooth.continuous hw.compact).mul
      (continuous_coverRealOscillationOn g e hB.le)
  have hnormminor (u : (Fin n → ℝ) → ℝ) (hu : CompactWeight u) (hubox : CubeSupported u)
      (b : ℝ) (hb : 0 < b) :
      ∃ D > 0, ∀ᶠ P : ℝ in atTop,
        (∫ α in (v2MajorArcs d Δ P)ᶜ,
          ‖coverNormalizedProduct F g u P (P^k) (b*P^k) α‖ ∂circleMeasure) ≤
          D * P^(-(d : ℝ)-η) := by
    obtain ⟨D,hD,h⟩ := hminor σ hν F g u hF hσ hu hubox hmg b hb
    exact ⟨D,hD,coverNormalizedProduct_minorBound_of_minorIntegral h⟩
  obtain ⟨hs,hSeries⟩ := coverConductorMass_tail_of_coverNormalizedMinor hd hF g he₀ hg hη hηΔ
    (fun u hu hubox => by simpa only [one_mul] using hnormminor u hu hubox 1 zero_lt_one)
  obtain ⟨C,hC,hCminor⟩ := hnormminor w hw hwbox B hB
  obtain ⟨E,hE,happrox⟩ := coverNormalizedProduct_approx_realFrequency hF g he₀ hg hw hwbox hB
  obtain ⟨hI,K,hK,hReal⟩ := integrable_and_absTail_of_productMinor_atExponent hd hf hIc
    (norm_coverRealProduct_even F g w e B) hk hC.le hE.le hη hCminor (by
      simpa only [Real.rpow_neg_one] using happrox)
  have hReal' : ∃ C' > 0, ∀ᶠ T : ℝ in atTop,
      (∫ t in (Icc (-T) T)ᶜ, ‖I t‖) ≤ C' * T^(-τ) := by
    refine ⟨K,hK,(eventually_ge_atTop 1).mono fun T hT => ?_⟩
    have heq : (Icc (-T) T)ᶜ = {t : ℝ | T < |t|} := by
      ext t
      change (¬ (-T ≤ t ∧ t ≤ T)) ↔ T < |t|
      rw [← abs_le, not_le]
    rw [heq]
    exact hReal T hT
  have hpoint : ∃ E' > 0, ∀ᶠ P : ℝ in atTop, ∀ (q : ℕ) (b : ℤ),
      0 < q → (q : ℝ) ≤ P^Δ → b.natAbs.Coprime q →
      ∀ α ∈ fixedWidthMajorInterval (P^(-(d : ℝ)+Δ)) q b,
        ‖f P α - coverCompleteProductAt F g q b * I (P^d*(α-(b : ℝ)/q))‖ ≤ E' * P^(-(10*Δ)) := by
    obtain ⟨E',hE',h⟩ := coverNormalizedProduct_approx_majorArcs hF g he₀ hg hw hwbox hB
    exact ⟨E',hE',h.mono fun P hP q b hq hqQ _ α hα => hP q b hq hqQ α hα⟩
  obtain ⟨_,D,hD,hMajor⟩ := coverMajorIntegralBound_of_pointwise_of_tails F g hd
    hΔ hΔ₁ (by linarith : 3*Δ < 10*Δ) hγ hτ f
    (fun P => coverNormalizedProduct_periodic F g w P _ _) hf I hIc hI hpoint hs hSeries hReal'
  have hmajor := coverMajorIntegral_unnormalize (d := d) (e := e) (C := D) (δ := ξ) (B := B)
    (F := F) (g := g) (w := w) hMajor
  exact ⟨hs, hI,
    coverWeightedBoxAsymptotic_of_arcIntegrals
      (hminor σ hν F g w hF hσ hw hwbox hmg B hB) ⟨D,hD,hmajor⟩⟩

/-- The cover asymptotic on the unit cube at the manuscript threshold. -/
theorem v2CoverCubeAsymptoticAt_of_weilII_of_coverMoment {n d e : ℕ}
    (hd : 2 ≤ d) (he : 2 ≤ e)
    (hWeil : ∀ r, 3 ≤ r → r < d → PrimeDeligneEstimate r)
    (hmoment : ∀ g : ℤ[X], g.natDegree = e → CoverMeanValueBound e g) :
    V2CoverCubeAsymptoticAt d e n :=
  v2CoverCubeAsymptoticAtExponent_of_weilII_of_coverMoment hd he (one_lt_coverMomentExponent he)
    hWeil hmoment

end

end Birch
