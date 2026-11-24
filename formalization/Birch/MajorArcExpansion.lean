import Birch.MajorArcs
import Birch.MajorArcDisjoint
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# From lifted-arc Poisson estimates to the integrated expansion
-/

namespace Birch

noncomputable section

open scoped BigOperators Topology
open Set Filter MeasureTheory

variable {n : ℕ}

private def completeSumAt (F : IntForm n) (q : ℕ) (a : ℤ) : ℂ :=
  if h : q = 0 then 0 else @completeSum n F q ⟨h⟩ (a : ZMod q)

private theorem completeSumAt_eq (F : IntForm n) (q : ℕ) [NeZero q] (a : ℤ) :
    completeSumAt F q a = completeSum F q (a : ZMod q) := dif_neg (NeZero.ne q)

/-- The pointwise leading-term Poisson estimate on each lifted major interval.
The error is measured for the normalized lattice sum. -/
def PointwiseMajorArcExpansion (d : ℕ) (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ L > (0 : ℝ), ∃ E > (0 : ℝ), ∀ᶠ P in atTop,
    ∀ (q : ℕ) [NeZero q], ∀ (a : ℤ), (q : ℝ) ≤ P^(1/2 : ℝ) →
      a.natAbs.Coprime q → ∀ α ∈ liftedMajorArc d P q a,
      ‖normalizedSum F w P α - completeSum F q (a : ZMod q) *
        realOscillation F w (P^d * (α - (a : ℝ)/q))‖ ≤ E * P^(-(d : ℝ)-L)

private theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- The oscillatory integral is continuous in frequency for any continuous compact weight. -/
theorem continuous_realOscillation_of_compact (F : IntForm n) {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hcompact : HasCompactSupport w) : Continuous (realOscillation F w) := by
  unfold realOscillation
  apply continuous_of_dominated (bound := fun x => ‖w x‖)
  · intro γ
    apply Continuous.aestronglyMeasurable
    apply (Complex.continuous_ofReal.comp hw).mul
    have h := continuous_evalForm F
    have h' : Continuous (fun t : ℝ => phase t) := by unfold phase; fun_prop
    exact h'.comp (continuous_const.mul h)
  · intro γ
    exact Eventually.of_forall fun x => by simp [norm_phase]
  · exact (hw.integrable_of_hasCompactSupport hcompact).norm
  · exact Eventually.of_forall fun x => by unfold phase; fun_prop

/-- Continuity for a transverse weight. -/
theorem continuous_realOscillation (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : TransverseWeight F w) : Continuous (realOscillation F w) :=
  continuous_realOscillation_of_compact F hw.smooth.continuous hw.compact

/-- The quartic Fourier decay bound makes the singular integral absolutely
convergent for a transverse weight. -/
theorem integrable_realOscillation_of_quartic_decay (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : TransverseWeight F w) {D : ℝ}
    (hDecay : ∀ t, ‖realOscillation F w t‖ ≤ D * (1 + |t|)^(-4 : ℝ)) :
    Integrable (realOscillation F w) := by
  have hmajorant : Integrable (fun t : ℝ => (1 + |t|)^(-4 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := 4) (by simp))
  exact (hmajorant.const_mul D).mono' (continuous_realOscillation F w hw).aestronglyMeasurable
    (Eventually.of_forall hDecay)

private theorem unitConductorSum_eq_numeratorSum (F : IntForm n) (q : ℕ) [NeZero q] :
    unitConductorSum F q =
      ∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q), completeSumAt F q (a : ℤ) := by
  unfold unitConductorSum
  refine Finset.sum_bij (fun u _ => (u.val : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime u⟩
  · intro a _ b _ he
    exact Units.ext (ZMod.val_injective q he)
  · intro a ha
    obtain ⟨hlt, hc⟩ := Finset.mem_filter.mp ha
    refine ⟨ZMod.unitOfCoprime a hc, Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hlt)
  · intro u _
    rw [completeSumAt_eq, Int.cast_natCast, ZMod.natCast_zmod_val]

private theorem sum_interiorMajorCenters (F : IntForm n) (P : ℝ) (J : ℕ → ℂ) :
    (∑ t ∈ interiorMajorCenters P, completeSumAt F t.1 (t.2 : ℤ) * J t.1) =
      ∑ q ∈ Finset.Icc 2 ⌊P^(1/2 : ℝ)⌋₊, singularSeriesTerm F q * J q := by
  unfold interiorMajorCenters
  rw [Finset.sum_filter]
  let g (a : ℕ × ℕ) := if a.2 < a.1 ∧ a.2.Coprime a.1 then completeSumAt F a.1 a.2 * J a.1 else 0
  change (∑ a ∈ (Finset.Icc 2 ⌊P^(1/2 : ℝ)⌋₊) ×ˢ (Finset.Icc 1 ⌊P^(1/2 : ℝ)⌋₊), g a) = _
  rw [Finset.sum_product]
  dsimp only [g]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hq₂, hqQ⟩ := Finset.mem_Icc.mp hq
  have hq₀ : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq₀⟩
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 ⌊P^(1/2 : ℝ)⌋₊).filter (fun a => a < q ∧ a.Coprime q) =
        (Finset.range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · tauto
    · rintro ⟨ha, hc⟩
      have ha₀ : a ≠ 0 := by
        rintro rfl
        simp at hc
        omega
      exact ⟨⟨by omega, ha.le.trans hqQ⟩, ha, hc⟩
  rw [hfilter, ← Finset.sum_mul, ← unitConductorSum_eq_numeratorSum]
  simp only [singularSeriesTerm, dif_neg hq₀]

private theorem majorArcTruncation_eq_centers (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (P : ℝ) (hP : 1 ≤ P) :
    majorArcTruncation F w P =
      completeSumAt F 1 0 * (∫ γ in Icc (-(P^(7/8 : ℝ))) (P^(7/8 : ℝ)), realOscillation F w γ) +
        ∑ t ∈ interiorMajorCenters P, completeSumAt F t.1 (t.2 : ℤ) *
          ∫ γ in Icc (-(P^(7/8 : ℝ) / (t.1 : ℝ))) (P^(7/8 : ℝ) / (t.1 : ℝ)), realOscillation F w γ := by
  let Q := ⌊P^(1/2 : ℝ)⌋₊
  let J (q : ℕ) : ℂ :=
    ∫ γ in Icc (-(P^(7/8 : ℝ)/(q : ℝ))) (P^(7/8 : ℝ)/(q : ℝ)), realOscillation F w γ
  have hQ : 1 ≤ Q := Nat.le_floor (by simpa using Real.one_le_rpow hP (by norm_num : 0 ≤ (1/2 : ℝ)))
  have hcut : (∫ γ in Icc (-(P^(7/8 : ℝ))) (P^(7/8 : ℝ)), realOscillation F w γ) = J 1 := by
    simp [J]
  rw [hcut, sum_interiorMajorCenters F P J, completeSumAt_eq, completeSum_one, one_mul]
  let A (q : ℕ) : ℂ := singularSeriesTerm F q * J q
  have hA₁ : A 1 = J 1 := by
    simp [A, singularSeriesTerm, unitConductorSum_one]
  have hshift : (∑ j ∈ Finset.range Q, A (j+1)) = ∑ q ∈ Finset.Icc 1 Q, A q := by
    rw [← Finset.Ico_succ_right_eq_Icc 1 Q]
    change _ = ∑ q ∈ Finset.Ico 1 (Q+1), A q
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm]
  have hinsert : Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hseries : majorArcTruncation F w P = ∑ j ∈ Finset.range Q, A (j+1) := by
    unfold majorArcTruncation
    apply Finset.sum_congr rfl
    intro j _
    simp only [A, J, singularSeriesTerm, dif_neg (Nat.succ_ne_zero j)]
  rw [hseries, hshift, hinsert, Finset.sum_insert, hA₁]
  simp


private theorem norm_integrated_liftedArc_error {d q : ℕ} {P ε : ℝ} [NeZero q]
    (hd : 2 ≤ d) (hP : 4 ≤ P) (hε : 0 ≤ ε) (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hI : Continuous (realOscillation F w)) (a : ℤ)
    (hpoint : ∀ α ∈ liftedMajorArc d P q a,
      ‖normalizedSum F w P α - completeSumAt F q a *
        realOscillation F w (P^d * (α - (a : ℝ)/q))‖ ≤ ε) :
    ‖(∫ α in liftedMajorArc d P q a, normalizedSum F w P α) -
      (P^(-(d : ℝ)) : ℝ) • (completeSumAt F q a *
        ∫ γ in Icc (-(P^(7/8 : ℝ)/(q : ℝ))) (P^(7/8 : ℝ)/(q : ℝ)), realOscillation F w γ)‖ ≤ ε := by
  let A := liftedMajorArc d P q a
  let S := normalizedSum F w P
  let M := fun α => completeSumAt F q a * realOscillation F w (P^d * (α - (a : ℝ)/q))
  have hp : 0 < P := by linarith
  have hcS : Continuous S :=
    (continuous_exponentialSum F w P).const_smul (P^(-(n : ℝ)) : ℝ)
  have hcM : Continuous M := continuous_const.mul (hI.comp (by fun_prop))
  have hSI : IntegrableOn S A := by
    unfold A
    rw [liftedMajorArc_eq_Icc]
    exact hcS.integrableOn_Icc
  have hMI : IntegrableOn M A := by
    unfold A
    rw [liftedMajorArc_eq_Icc]
    exact hcM.integrableOn_Icc
  have hmain :
      (∫ α in A, M α) = (P^(-(d : ℝ)) : ℝ) • (completeSumAt F q a *
        ∫ γ in Icc (-(P^(7/8 : ℝ)/(q : ℝ))) (P^(7/8 : ℝ)/(q : ℝ)), realOscillation F w γ) := by
    unfold M A
    rw [integral_const_mul, integral_liftedMajorArc_substitution d hp (NeZero.pos q) a]
    simp only [Complex.real_smul]
    ring
  rw [← hmain, ← integral_sub hSI hMI]
  have hfinit : volume A < ⊤ := by unfold A; rw [liftedMajorArc_eq_Icc]; exact measure_Icc_lt_top
  refine (norm_setIntegral_le_of_norm_le_const hfinit hpoint).trans ?_
  have hwidth : 0 < majorArcWidth d P ∧ majorArcWidth d P < 1/2 :=
    majorArcWidth_pos_lt_half hd hP
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq' : (0 : ℝ) < q := by linarith
  have hhalf : majorArcWidth d P / (q : ℝ) ≤ 1/2 :=
    (div_le_self hwidth.1.le hq).trans hwidth.2.le
  have hmeas : volume.real A ≤ 1 := by
    unfold A
    rw [liftedMajorArc_eq_Icc, Real.volume_real_Icc_of_le]
    · linarith
    · linarith [div_pos hwidth.1 hq']
  exact (mul_le_mul_of_nonneg_left hmeas hε).trans_eq (mul_one _)

private theorem interiorMajorCenters_card_le (P : ℝ) (hP : 0 ≤ P) :
    ((interiorMajorCenters P).card : ℝ) ≤ P := by
  let Q := ⌊P^(1/2 : ℝ)⌋₊
  have hsub : interiorMajorCenters P ⊆ (Finset.Icc 1 Q).product (Finset.Icc 1 Q) := by
    rintro ⟨q,a⟩ h
    obtain ⟨hq, hqP, ha, haq, _⟩ := (mem_interiorMajorCenters hP).1 h
    have hqQ := Nat.le_floor hqP
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hqQ⟩, Finset.mem_Icc.mpr ⟨ha, haq.le.trans hqQ⟩⟩
  have hn := Finset.card_le_card hsub
  change (interiorMajorCenters P).card ≤ ((Finset.Icc 1 Q) ×ˢ (Finset.Icc 1 Q)).card at hn
  rw [Finset.card_product, Nat.card_Icc] at hn
  simp only [add_tsub_cancel_right] at hn
  calc
    _ ≤ (Q : ℝ)^2 := by exact_mod_cast (show (interiorMajorCenters P).card ≤ Q^2 from by rwa [pow_two])
    _ ≤ (P^(1/2 : ℝ))^2 := by gcongr; exact Nat.floor_le (by positivity)
    _ = P := by rw [← Real.rpow_natCast, ← Real.rpow_mul hP]; norm_num

/-- Pointwise Poisson error bounds on all lifted major arcs give the integrated
expansion used in the cutoff estimates. -/
theorem integratedMajorArcExpansion_of_pointwise_of_continuous {d : ℕ} (hd : 2 ≤ d)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hI : Continuous (realOscillation F w))
    (hpoint : PointwiseMajorArcExpansion d F w) :
    IntegratedMajorArcExpansion d F w := by
  intro L hL
  obtain ⟨E, hE, hbound⟩ := hpoint (L+1) (by linarith)
  refine ⟨2*E, by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (4 : ℝ)] with P hAtP hP
  have hp : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  let δ := E * P^(-(d : ℝ)-(L+1))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  let D := P^(-(d : ℝ))
  let S := normalizedSum F w P
  let A (q : ℕ) (a : ℤ) := ∫ α in liftedMajorArc d P q a, S α
  let B (q : ℕ) (a : ℤ) := completeSumAt F q a *
      ∫ γ in Icc (-(P^(7/8 : ℝ)/(q : ℝ))) (P^(7/8 : ℝ)/(q : ℝ)), realOscillation F w γ
  have herror (q : ℕ) [NeZero q] (a : ℤ) (hqP : (q : ℝ) ≤ P^(1/2 : ℝ)) (ha : a.natAbs.Coprime q) :
      ‖A q a - D • B q a‖ ≤ δ := by
    apply norm_integrated_liftedArc_error hd hP hδ F w hI
    intro α hα
    rw [completeSumAt_eq]
    exact hAtP q a hqP ha α hα
  have hε₁ : ‖A 1 0 - D • B 1 0‖ ≤ δ := by
    apply herror
    · simpa using Real.one_le_rpow hP1 (by norm_num : 0 ≤ (1/2 : ℝ))
    · simp
  have hε (j : ℕ × ℕ) (hj : j ∈ interiorMajorCenters P) :
      ‖A j.1 (j.2 : ℤ) - D • B j.1 (j.2 : ℤ)‖ ≤ δ := by
    obtain ⟨hq, hqP, _, _, hcop⟩ := (mem_interiorMajorCenters hp.le).mp hj
    letI : NeZero j.1 := ⟨by omega⟩
    exact herror _ _ hqP (by simpa)
  have hperiodic : Function.Periodic S 1 := fun x => by
    unfold S normalizedSum
    rw [exponentialSum_periodic]
  have hcontinuous : Continuous S :=
    (continuous_exponentialSum F w P).const_smul (P^(-(n : ℝ)) : ℝ)
  have hzero : liftedMajorArc d P 1 0 =
      Icc (-majorArcWidth d P) (majorArcWidth d P) := by
    rw [liftedMajorArc_eq_Icc]
    simp
  have hM :
      (∫ α in majorArcs d P, S α ∂circleMeasure) =
        A 1 0 + ∑ j ∈ interiorMajorCenters P, A j.1 (j.2 : ℤ) := by
    rw [integral_majorArcs_eq_sum hd hP hperiodic hcontinuous, ← hzero]
  have hB :
      majorArcTruncation F w P = B 1 0 + ∑ j ∈ interiorMajorCenters P, B j.1 (j.2 : ℤ) := by
    rw [majorArcTruncation_eq_centers F w P hP1]
    simp only [B, Nat.cast_one, div_one]
  change ‖(∫ α in majorArcs d P, S α ∂circleMeasure) - D • majorArcTruncation F w P‖ ≤ _
  rw [hM, hB, smul_add, Finset.smul_sum, add_sub_add_comm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ‖A 1 0 - D • B 1 0‖ +
        ∑ j ∈ interiorMajorCenters P, ‖A j.1 (j.2 : ℤ) - D • B j.1 (j.2 : ℤ)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ δ + ∑ _j ∈ interiorMajorCenters P, δ :=
      add_le_add hε₁ (Finset.sum_le_sum hε)
    _ = (1 + ((interiorMajorCenters P).card : ℝ)) * δ := by
      rw [Finset.sum_const, nsmul_eq_mul, add_mul, one_mul]
    _ ≤ (2*P)*δ := mul_le_mul_of_nonneg_right (by linarith [interiorMajorCenters_card_le P hp.le]) hδ
    _ = 2*E*P^(-(d : ℝ)-L) := by
      dsimp [δ]
      have hp' : P * P^(-(d : ℝ)-(L+1)) = P^(-(d : ℝ)-L) := by
        calc
          _ = P^(1 : ℝ) * P^(-(d : ℝ)-(L+1)) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hp]; congr 1; ring
      rw [show 2*P*(E*P^(-(d : ℝ)-(L+1))) =
        2*E*(P * P^(-(d : ℝ)-(L+1))) by ring, hp']

/-- The integrated expansion for the original transverse weights. -/
theorem integratedMajorArcExpansion_of_pointwise {d : ℕ} (hd : 2 ≤ d)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hw : TransverseWeight F w)
    (hpoint : PointwiseMajorArcExpansion d F w) : IntegratedMajorArcExpansion d F w :=
  integratedMajorArcExpansion_of_pointwise_of_continuous hd F w (continuous_realOscillation F w hw) hpoint

end

end Birch
