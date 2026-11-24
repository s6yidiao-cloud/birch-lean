import Birch.V2CoverMajor

/-! # The completed cover main term on the major arcs -/

open Filter MeasureTheory Set
open scoped BigOperators Polynomial Topology

namespace Birch

noncomputable section

private theorem cover_cutoff_power_le {X γ : ℝ} (hX : 1 ≤ X) (hγ : 0 < γ) :
    (⌊X⌋₊ : ℝ)^(-γ) ≤ (2 : ℝ)^γ * X^(-γ) := by
  let Q := ⌊X⌋₊
  have hQ : 1 ≤ Q := Nat.le_floor (by simpa using hX)
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQhalf : X/2 ≤ (Q : ℝ) := by
    have h := Nat.lt_floor_add_one X
    change X < (Q : ℝ) + 1 at h
    linarith
  calc
    _ ≤ (X/2)^(-γ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hQhalf (neg_nonpos.mpr hγ.le)
    _ = _ := by
      rw [Real.div_rpow (by positivity : 0 ≤ X) (by norm_num : 0 ≤ (2 : ℝ)),
        Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)), div_inv_eq_mul, mul_comm]

private theorem norm_coverConductorTruncation_le_mass {n : ℕ}
    (F : IntForm n) (g : ℤ[X]) (Q : ℕ)
    (hs : Summable (fun j : ℕ => coverConductorMass F g (j+1))) :
    ‖∑ j ∈ Finset.range Q, coverConductorSum F g (j+1)‖ ≤
      ∑' j : ℕ, coverConductorMass F g (j+1) := by
  calc
    _ ≤ ∑ j ∈ Finset.range Q, ‖coverConductorSum F g (j+1)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range Q, coverConductorMass F g (j+1) :=
      Finset.sum_le_sum fun j _ => norm_coverConductorSum_le_mass F g (j+1)
    _ ≤ _ := hs.sum_le_tsum _ fun j _ => coverConductorMass_nonneg F g (j+1)

private theorem norm_realIntegralTruncation_sub_le_absTail {I : ℝ → ℂ}
    (hI : Integrable I) (T : ℝ) :
    ‖(∫ t in Icc (-T) T, I t) - ∫ t, I t‖ ≤
      ∫ t in (Icc (-T) T)ᶜ, ‖I t‖ := by
  rw [norm_sub_rev, ← integral_add_compl measurableSet_Icc hI, add_sub_cancel_left]
  exact norm_integral_le_integral_norm _

/-- The normalized cover major-arc estimate follows from a pointwise
approximation and absolute power tails for both local factors. -/
theorem coverMajorIntegralBound_of_pointwise_of_tails {n d : ℕ}
    (F : IntForm n) (g : ℤ[X]) (hd : 2 ≤ d) {Δ L γ τ : ℝ}
    (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/4) (hL : 3*Δ < L) (hγ : 0 < γ) (hτ : 0 < τ)
    (f : ℝ → ℝ → ℂ) (hperiodic : ∀ P, Function.Periodic (f P) 1)
    (hf : ∀ P, Continuous (f P)) (I : ℝ → ℂ) (hIc : Continuous I) (hI : Integrable I)
    (hPoint : ∃ E > 0, ∀ᶠ P : ℝ in atTop,
      ∀ (q : ℕ) (a : ℤ), 0 < q → (q : ℝ) ≤ P^Δ → a.natAbs.Coprime q →
        ∀ α ∈ fixedWidthMajorInterval (P^(-(d : ℝ)+Δ)) q a,
          ‖f P α - coverCompleteProductAt F g q a * I (P^d*(α-(a : ℝ)/q))‖ ≤ E * P^(-L))
    (hs : Summable (fun j : ℕ => coverConductorMass F g (j+1)))
    (hSeries : ∃ A > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
      (∑' j : ℕ, coverConductorMass F g (j+Q+1)) ≤ A * (Q : ℝ)^(-γ))
    (hReal : ∃ B > 0, ∀ᶠ T : ℝ in atTop,
      (∫ t in (Icc (-T) T)ᶜ, ‖I t‖) ≤ B * T^(-τ)) :
    let σ := min (L-3*Δ) (min (γ*Δ) (τ*Δ))
    0 < σ ∧ ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(∫ α in v2MajorArcs d Δ P, f P α ∂circleMeasure) -
        (P^(-(d : ℝ)) : ℝ) • (coverSingularSeries F g * ∫ t, I t)‖ ≤
        C * P^(-(d : ℝ)-σ) := by
  let σ := min (L-3*Δ) (min (γ*Δ) (τ*Δ))
  have hσ : 0 < σ := lt_min (sub_pos.mpr hL) (lt_min (mul_pos hγ hΔ) (mul_pos hτ hΔ))
  have hσL : σ ≤ L-3*Δ := min_le_left _ _
  have hσγ : σ ≤ γ*Δ := (min_le_right _ _).trans (min_le_left _ _)
  have hστ : σ ≤ τ*Δ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨E,hE,hPoint⟩ := hPoint
  obtain ⟨A,hA,Q₀,hSeries⟩ := hSeries
  obtain ⟨B,hB,hReal⟩ := hReal
  let S := coverSingularSeries F g
  let M := ∑' j : ℕ, coverConductorMass F g (j+1)
  let J := ∫ t, I t
  let K := M*B + A * (2 : ℝ)^γ * ‖J‖
  have hM : 0 ≤ M := tsum_nonneg fun j => coverConductorMass_nonneg F g (j+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨hσ,4*E+K,by positivity,?_⟩
  have htend := tendsto_rpow_atTop hΔ
  filter_upwards [hPoint, htend.eventually hReal,
    htend.eventually (eventually_ge_atTop (Q₀ : ℝ)), eventually_ge_atTop (2 : ℝ)] with
    P hPoint hReal hLarge hP
  have hP₁ : 1 ≤ P := by linarith
  have hP₀ : 0 < P := by linarith
  let U₀ := P^Δ
  let Q := ⌊U₀⌋₊
  let SQ := ∑ j ∈ Finset.range Q, coverConductorSum F g (j+1)
  let JQ := ∫ t in Icc (-U₀) U₀, I t
  let U := ∫ α in v2MajorArcs d Δ P, f P α ∂circleMeasure
  have hSQ : ‖SQ‖ ≤ M := norm_coverConductorTruncation_le_mass F g Q hs
  have hX : 1 ≤ U₀ := Real.one_le_rpow hP₁ hΔ.le
  have hQ : Q₀ ≤ Q := Nat.le_floor hLarge
  have hboundJ : ‖JQ-J‖ ≤ B*P^(-σ) := by
    calc
      _ ≤ ∫ t in (Icc (-U₀) U₀)ᶜ, ‖I t‖ := norm_realIntegralTruncation_sub_le_absTail hI U₀
      _ ≤ B * U₀^(-τ) := hReal
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        dsimp [U₀]
        rw [← Real.rpow_mul hP₀.le]
        exact Real.rpow_le_rpow_of_exponent_le hP₁ (by nlinarith)
  have hboundS : ‖SQ-S‖ ≤ (A*(2 : ℝ)^γ)*P^(-σ) := by
    rw [norm_sub_rev]
    calc
      _ ≤ ∑' j : ℕ, coverConductorMass F g (j+Q+1) :=
        norm_coverSingularSeries_sub_truncation_le_massTail F g Q hs
      _ ≤ A * (Q : ℝ)^(-γ) := hSeries Q hQ
      _ ≤ A * ((2 : ℝ)^γ * U₀^(-γ)) := mul_le_mul_of_nonneg_left (cover_cutoff_power_le hX hγ) hA.le
      _ = (A*(2 : ℝ)^γ)*U₀^(-γ) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [U₀]
        rw [← Real.rpow_mul hP₀.le]
        exact Real.rpow_le_rpow_of_exponent_le hP₁ (by nlinarith)
  have hcut : ‖SQ*JQ-S*J‖ ≤ K*P^(-σ) := by
    rw [show SQ*JQ-S*J = SQ*(JQ-J)+(SQ-S)*J by ring]
    calc
      _ ≤ ‖SQ*(JQ-J)‖+‖(SQ-S)*J‖ := norm_add_le _ _
      _ ≤ M*(B*P^(-σ))+((A*(2 : ℝ)^γ)*P^(-σ))*‖J‖ := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul hSQ hboundJ (norm_nonneg _) hM)
          (mul_le_mul_of_nonneg_right hboundS (norm_nonneg _))
      _ = _ := by dsimp [K]; ring
  have hmajor := norm_integral_v2MajorArcs_sub_main_le hd hΔ.le hΔ₁ hP
    (hperiodic P) (hf P) (coverCompleteProductAt F g) hIc (by positivity) hPoint
  rw [coverCompleteProduct_sum_eq_truncation F g hP₁ hΔ.le] at hmajor
  have herr : ‖U - (P^(-(d : ℝ)) : ℝ) • (SQ*JQ)‖ ≤ (4*E)*P^(-(d : ℝ)-σ) := by
    refine hmajor.trans ?_
    calc
      _ = (4*E) * (P^(-L) * P^(-(d : ℝ)+3*Δ)) := by ring
      _ ≤ _ := by
        rw [← Real.rpow_add hP₀]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)) (by positivity)
  change ‖U-(P^(-(d : ℝ)) : ℝ) • (S*J)‖ ≤ (4*E+K)*P^(-(d : ℝ)-σ)
  rw [show U-(P^(-(d : ℝ)) : ℝ) • (S*J) =
    (U-(P^(-(d : ℝ)) : ℝ) • (SQ*JQ))+(P^(-(d : ℝ)) : ℝ) • (SQ*JQ-S*J) by rw [smul_sub]; abel]
  calc
    _ ≤ ‖U-(P^(-(d : ℝ)) : ℝ) • (SQ*JQ)‖+‖(P^(-(d : ℝ)) : ℝ) • (SQ*JQ-S*J)‖ :=
      norm_add_le _ _
    _ ≤ (4*E)*P^(-(d : ℝ)-σ) + P^(-(d : ℝ))*(K*P^(-σ)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hP₀ _)]
      exact add_le_add herr (mul_le_mul_of_nonneg_left hcut (by positivity))
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hP₀, ← sub_eq_add_neg]
      ring

end

end Birch
