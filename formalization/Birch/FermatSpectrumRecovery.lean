module

public import Birch.FermatPointCounts
public import Birch.ProjectiveHypersurfaceComplement
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.BigOperators.Field
public import Birch.PowerSumRank

@[expose] public section

/-! # Reading Frobenius weights from Fermat point counts -/

open Filter CategoryTheory
open scoped Topology BigOperators

namespace Birch

noncomputable section

private def powerSum (S : Multiset ℂ) (m : ℕ) : ℂ := (S.map (· ^ m)).sum

private def traceError (A T : ℕ → Multiset ℂ) (I : Finset ℕ) (m : ℕ) : ℂ :=
  ∑ i ∈ I, (-1 : ℂ)^i * (powerSum (A i) m - powerSum (T i) m)

private def normalizeSpectrum (ρ : ℝ) (S : Multiset ℂ) : Multiset ℂ :=
  S.map (fun z => z / (ρ : ℂ))

private theorem powerSum_normalize (ρ : ℝ) (S : Multiset ℂ) (m : ℕ) :
    powerSum (normalizeSpectrum ρ S) m = powerSum S m / (ρ : ℂ)^m := by
  simp only [powerSum, normalizeSpectrum, Multiset.map_map, Function.comp_def, div_pow]
  exact Multiset.sum_map_div S (· ^ m) ((ρ : ℂ)^m)

private theorem traceError_normalize (A T : ℕ → Multiset ℂ) (I : Finset ℕ) (ρ : ℝ) (m : ℕ) :
    traceError A T I m / (ρ : ℂ)^m =
      traceError (fun i => normalizeSpectrum ρ (A i)) (fun i => normalizeSpectrum ρ (T i)) I m := by
  simp only [traceError, Finset.sum_div, mul_div_assoc, sub_div, powerSum_normalize]

private theorem sqrt_natCast_pow (q i : ℕ) :
    Real.sqrt ((q : ℝ)^i) = (Real.sqrt (q : ℝ))^i := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg q), Real.sqrt_eq_rpow,
    ← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
  congr 1
  ring

private theorem projectiveTateValue_eq_weight {q i : ℕ} (hi : Even i) :
    (q : ℂ)^(i/2) = (((Real.sqrt (q : ℝ))^i : ℝ) : ℂ) := by
  obtain ⟨a, ha⟩ := hi
  have he : i = 2*a := by omega
  rw [he, pow_mul, Real.sq_sqrt (Nat.cast_nonneg q),
    show 2*a/2 = a by omega, Complex.ofReal_pow, Complex.ofReal_natCast]

private theorem norm_mem_projectiveTateSpectrum {q i : ℕ} {z : ℂ}
    (hz : z ∈ projectiveTateSpectrum q i) : ‖z‖ = (Real.sqrt (q : ℝ))^i := by
  by_cases hi : Even i
  · rw [projectiveTateSpectrum, ite_eq_left hi, Multiset.mem_singleton] at hz
    rw [hz, projectiveTateValue_eq_weight hi, Complex.norm_real, Real.norm_of_nonneg]
    positivity
  · simp [projectiveTateSpectrum, hi] at hz

private theorem normalize_projectiveTateSpectrum {q i : ℕ} (hq : 0 < q) :
    normalizeSpectrum ((Real.sqrt (q : ℝ))^i) (projectiveTateSpectrum q i) =
      if Even i then {1} else 0 := by
  by_cases hi : Even i
  · have hn : ((((Real.sqrt (q : ℝ))^i) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (Real.sqrt (q : ℝ))^i ≠ 0 by positivity)
    rw [projectiveTateSpectrum, ite_eq_left hi, normalizeSpectrum, Multiset.map_singleton,
      projectiveTateValue_eq_weight hi, div_self hn, ite_eq_left hi]
  · simp [projectiveTateSpectrum, hi, normalizeSpectrum]

private theorem norm_mem_normalizeSpectrum {ρ : ℝ} (hρ : 0 ≤ ρ)
    {S : Multiset ℂ} {R : ℝ} (hS : ∀ z ∈ S, ‖z‖ = R)
    {z : ℂ} (hz : z ∈ normalizeSpectrum ρ S) : ‖z‖ = R / ρ := by
  rcases Multiset.mem_map.mp hz with ⟨u, hu, rfl⟩
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ, hS u hu]

private theorem recover_grade_above_cutoff {q cut j : ℕ} (hq : 1 < q) (hj : cut < j)
    (I : Finset ℕ) (hmem : j ∈ I) (A : ℕ → Multiset ℂ) (C : ℝ)
    (hweight : ∀ i ∈ I, ∀ z ∈ A i, ‖z‖ = (Real.sqrt (q : ℝ))^i)
    (hhigh : ∀ i ∈ I, j < i → A i = projectiveTateSpectrum q i)
    (herr : ∀ᶠ m : ℕ in atTop,
      ‖traceError A (projectiveTateSpectrum q) I m‖ ≤ C * ((Real.sqrt (q : ℝ))^cut)^m) :
    A j = projectiveTateSpectrum q j := by
  classical
  let R := Real.sqrt (q : ℝ)
  have hR : 1 < R := by
    dsimp [R]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hq)
  let ρ := R^j
  have hρ : 0 < ρ := pow_pos (lt_trans zero_lt_one hR) _
  let An (i : ℕ) := normalizeSpectrum ρ (A i)
  let Tn (i : ℕ) := normalizeSpectrum ρ (projectiveTateSpectrum q i)
  have hratio {i : ℕ} (hi : i < j) : R^i/ρ < 1 :=
    (div_lt_one hρ).mpr (pow_lt_pow_right₀ hR hi)
  have htotal : Tendsto (traceError An Tn I) atTop (𝓝 0) := by
    have hb : ∀ᶠ m : ℕ in atTop, ‖traceError An Tn I m‖ ≤ C * (R^cut/ρ)^m := by
      filter_upwards [herr] with m hm
      rw [← traceError_normalize, norm_div, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hρ.le, div_pow, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hm (pow_nonneg hρ.le _)
    have hsmall : ‖R^cut/ρ‖ < 1 := by rw [Real.norm_of_nonneg (by positivity)]; exact hratio hj
    refine squeeze_zero_norm' hb ?_
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall).const_mul C
  have hrest : Tendsto (traceError An Tn (I.erase j)) atTop (𝓝 0) := by
    have hterm (i : ℕ) (hi : i ∈ I.erase j) :
        Tendsto (fun m => (-1 : ℂ)^i * (powerSum (An i) m - powerSum (Tn i) m)) atTop (𝓝 0) := by
      rcases lt_or_gt_of_ne (Finset.mem_erase.mp hi).1 with hil | hih
      · have hAn : ∀ z ∈ An i, ‖z‖ < 1 := fun z hz => (norm_mem_normalizeSpectrum hρ.le
          (hweight i (Finset.mem_erase.mp hi).2) hz).trans_lt (hratio hil)
        have hTn : ∀ z ∈ Tn i, ‖z‖ < 1 := fun z hz => (norm_mem_normalizeSpectrum hρ.le
          (fun u hu => norm_mem_projectiveTateSpectrum hu) hz).trans_lt (hratio hil)
        simpa only [powerSum, sub_self, mul_zero] using
          ((tendsto_powSum_zero_of_norm_lt_one _ hAn).sub
            (tendsto_powSum_zero_of_norm_lt_one _ hTn)).const_mul ((-1 : ℂ)^i)
      · have he : An i = Tn i := congrArg _ (hhigh i (Finset.mem_erase.mp hi).2 hih)
        simpa only [he, sub_self, mul_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    change Tendsto (fun m => ∑ i ∈ I.erase j,
      (-1 : ℂ)^i * (powerSum (An i) m - powerSum (Tn i) m)) atTop (𝓝 0)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum (I.erase j) hterm
  have hgrade (m : ℕ) : (-1 : ℂ)^j * (powerSum (An j) m - powerSum (Tn j) m) =
      traceError An Tn I m - traceError An Tn (I.erase j) m := by
    rw [traceError, traceError, Finset.sum_erase_eq_sub hmem]
    ring
  have hlim : Tendsto (fun m => (-1 : ℂ)^j * (powerSum (An j) m - powerSum (Tn j) m)) atTop (𝓝 0) := by
    simpa only [← hgrade, sub_self] using htotal.sub hrest
  have hsign : (-1 : ℂ)^j ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hlim' : Tendsto (fun m => powerSum (An j) m - powerSum (Tn j) m) atTop (𝓝 0) := by
    convert hlim.const_mul (((-1 : ℂ)^j)⁻¹) using 1
    · funext m
      simp only [← mul_assoc, inv_mul_cancel₀ hsign, one_mul]
    · simp
  have hAn : ∀ z ∈ An j, ‖z‖ = 1 :=
    fun z hz => (norm_mem_normalizeSpectrum hρ.le (hweight j hmem) hz).trans (div_self hρ.ne')
  have hTn : Tn j = if Even j then {1} else 0 := normalize_projectiveTateSpectrum (by omega)
  have hTsum (m : ℕ) : powerSum (Tn j) m = if Even j then 1 else 0 := by
    rw [hTn]
    by_cases he : Even j <;> simp [powerSum, he]
  have hAnLim : Tendsto (powerSum (An j)) atTop (𝓝 (if Even j then 1 else 0)) := by
    rw [show powerSum (An j) =
      fun m => (powerSum (An j) m - powerSum (Tn j) m) + (if Even j then 1 else 0) by
        funext m; rw [← hTsum m, sub_add_cancel]]
    simpa only [zero_add] using hlim'.add tendsto_const_nhds
  change Tendsto (fun m => ((An j).map (· ^ m)).sum) atTop
    (𝓝 (if Even j then 1 else 0)) at hAnLim
  have he : An j = Tn j := by
    have h := eq_tateUnitSpectrum_of_tendsto_powSum (An j) hAn (decide (Even j))
      (by simpa only [decide_eq_true_eq] using hAnLim)
    simpa only [hTn, decide_eq_true_eq] using h
  exact Multiset.map_injective
    (fun _ _ h => (div_left_inj' (show (ρ : ℂ) ≠ 0 by exact_mod_cast hρ.ne')).mp h) he


private theorem projectiveTateSpectrum_dual {q N j : ℕ} (hq : 0 < q) (hj : j ≤ 2*N) :
    (projectiveTateSpectrum q j).map ((q : ℂ)^N / ·) = projectiveTateSpectrum q (2*N-j) := by
  by_cases he : Even j
  · obtain ⟨i, hi⟩ := he
    have he : Even j := ⟨i,hi⟩
    have hj' : j = 2*i := by omega
    have hiN : i ≤ N := by omega
    have hcomp : Even (2*N-j) := ⟨N-i, by omega⟩
    rw [projectiveTateSpectrum, ite_eq_left he, projectiveTateSpectrum, ite_eq_left hcomp,
      Multiset.map_singleton, show j/2 = i by omega, show (2*N-j)/2 = N-i by omega]
    exact congrArg (fun x : ℂ => ({x} : Multiset ℂ))
      (by simpa only [div_eq_mul_inv] using (pow_sub₀ (q : ℂ)
        (by exact_mod_cast hq.ne') hiN).symm)
  · have hcomp : ¬Even (2*N-j) := by
      rintro ⟨i, hi⟩
      exact he ⟨N-i, by omega⟩
    simp [projectiveTateSpectrum, he, hcomp]

private theorem map_pow_projectiveTateSpectrum (q i m : ℕ) :
    (projectiveTateSpectrum q i).map (· ^ m) = projectiveTateSpectrum (q^m) i := by
  by_cases he : Even i
  · rw [projectiveTateSpectrum, ite_eq_left he, projectiveTateSpectrum, ite_eq_left he,
      Multiset.map_singleton, Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  · simp [projectiveTateSpectrum, he]

private theorem middle_rank_bound_of_traceError {q N : ℕ} (hq : 1 < q)
    (A : ℕ → Multiset ℂ) (C : ℝ)
    (hW : ∀ z ∈ A N, ‖z‖ = (Real.sqrt (q : ℝ))^N)
    (houter : ∀ i ≤ 2*N, i ≠ N → A i = projectiveTateSpectrum q i)
    (herror : ∀ᶠ m : ℕ in atTop, ‖traceError A (projectiveTateSpectrum q) (Finset.Iic (2*N)) m‖ ≤
      C * ((Real.sqrt (q : ℝ))^N)^m) :
    ((A N).card : ℝ) ≤ C + 1 := by
  classical
  let ρ := (Real.sqrt (q : ℝ))^N
  let S := normalizeSpectrum ρ (A N)
  let a : ℂ := if Even N then 1 else 0
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hS : ∀ z ∈ S, ‖z‖ = 1 :=
    fun z hz => (norm_mem_normalizeSpectrum hρ.le hW hz).trans (div_self hρ.ne')
  have hp (m : ℕ) : powerSum (normalizeSpectrum ρ (projectiveTateSpectrum q N)) m = a := by
    change powerSum (normalizeSpectrum ((Real.sqrt (q : ℝ))^N) (projectiveTateSpectrum q N)) m = _
    rw [normalize_projectiveTateSpectrum (by omega)]
    by_cases he : Even N <;> simp [powerSum, a, he]
  have he (m : ℕ) : traceError A (projectiveTateSpectrum q) (Finset.Iic (2*N)) m / (ρ : ℂ)^m =
      (-1 : ℂ)^N * (powerSum S m - a) := by
    rw [traceError_normalize, traceError, Finset.sum_eq_single N]
    · rw [hp]
    · intro i hi hne
      simp only [houter i (Finset.mem_Iic.mp hi) hne, sub_self, mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_Iic.mpr (by omega)))
  have hn (m : ℕ) : ‖traceError A (projectiveTateSpectrum q) (Finset.Iic (2*N)) m‖ / ρ^m =
      ‖powerSum S m - a‖ := by
    have h := congrArg norm (he m)
    simpa only [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hρ.le, norm_mul,
      norm_neg, norm_one, one_pow, one_mul] using h
  have hbound : ∀ᶠ m : ℕ in atTop, ‖powerSum S m - a‖ ≤ C := by
    filter_upwards [herror] with m hm
    rw [← hn, div_le_iff₀ (pow_pos hρ _)]
    exact hm
  have hrank := norm_sub_card_le_of_eventually_norm_powSum_le S hS a C
    (show ∀ᶠ m : ℕ in atTop, ‖powerSum S m-a‖ ≤ C from hbound)
  have ha : ‖a‖ ≤ 1 := by
    by_cases ht : Even N <;> simp [a, ht]
  have hs : (S.card : ℝ) ≤ C + 1 := by
    calc
      (S.card : ℝ) = ‖(S.card : ℂ)‖ := by exact (Complex.norm_natCast _).symm
      _ = ‖(S.card : ℂ) - a + a‖ := by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hrank ha)
  simpa only [S, normalizeSpectrum, Multiset.card_map] using hs

private theorem traceError_eventually_le_of_projectivePowerTrace {q N cut : ℕ}
    (A : ℕ → Multiset ℂ) (C : ℝ)
    (herror : ∀ᶠ m : ℕ in atTop,
      ‖(∑ i ∈ Finset.Iic (2*N), (-1 : ℂ)^i * ((A i).map (· ^ m)).sum) -
        (projectiveSpacePointCount (q^m) N : ℂ)‖ ≤ C * (Real.sqrt ((q : ℝ)^cut))^m) :
    ∀ᶠ m : ℕ in atTop,
      ‖traceError A (projectiveTateSpectrum q) (Finset.Iic (2*N)) m‖ ≤
        C * ((Real.sqrt (q : ℝ))^cut)^m := by
  filter_upwards [herror] with m hm
  rw [traceError]
  simp_rw [powerSum, map_pow_projectiveTateSpectrum, mul_sub, Finset.sum_sub_distrib]
  rw [alternating_sum_projectiveTateSpectrum]
  simpa only [sqrt_natCast_pow] using hm

private theorem tateSpectrum_above_cutoff_of_power_trace {q N cut : ℕ} (hq : 1 < q)
    (A : ℕ → Multiset ℂ) (C : ℝ)
    (hweight : ∀ i ≤ 2*N, ∀ z ∈ A i, ‖z‖ = Real.sqrt ((q : ℝ)^i))
    (herror : ∀ᶠ m : ℕ in atTop,
      ‖(∑ i ∈ Finset.Iic (2*N), (-1 : ℂ)^i * ((A i).map (· ^ m)).sum) -
        (projectiveSpacePointCount (q^m) N : ℂ)‖ ≤ C * (Real.sqrt ((q : ℝ)^cut))^m) :
    ∀ i ≤ 2*N, cut < i → A i = projectiveTateSpectrum q i := by
  classical
  let I := Finset.Iic (2*N)
  have hErr := traceError_eventually_le_of_projectivePowerTrace A C herror
  have hW (i : ℕ) (hi : i ∈ I) (z : ℂ) (hz : z ∈ A i) :
      ‖z‖ = (Real.sqrt (q : ℝ))^i := (hweight i (Finset.mem_Iic.mp hi) z hz).trans (sqrt_natCast_pow q i)
  intro i hi hicut
  by_contra hc
  let J := I.filter (fun j => cut < j ∧ A j ≠ projectiveTateSpectrum q j)
  have hmem : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hi, hicut, hc⟩
  let j := J.max' ⟨i,hmem⟩
  have hj : j ∈ J := Finset.max'_mem _ _
  obtain ⟨hjI, hjcut, hjbad⟩ := Finset.mem_filter.mp hj
  apply hjbad
  refine recover_grade_above_cutoff hq hjcut I hjI A C hW (fun t ht htj => ?_) hErr
  by_contra hne
  have htJ : t ∈ J := Finset.mem_filter.mpr ⟨ht, hjcut.trans htj, hne⟩
  exact htj.not_ge (J.le_max' t htJ)

/-- The exact extension-field counts of projective space determine its
entire graded Frobenius spectrum from the weight formula. -/
theorem eq_projectiveTateSpectrum_of_exact_power_trace {q N : ℕ} (hq : 1 < q)
    (A : ℕ → Multiset ℂ) (hzero : A 0 = {1})
    (hweight : ∀ i ≤ 2*N, ∀ z ∈ A i, ‖z‖ = Real.sqrt ((q : ℝ)^i))
    (htrace : ∀ᶠ m : ℕ in atTop,
      (∑ i ∈ Finset.Iic (2*N), (-1 : ℂ)^i * ((A i).map (· ^ m)).sum) =
        (projectiveSpacePointCount (q^m) N : ℂ)) :
    ∀ i ≤ 2*N, A i = projectiveTateSpectrum q i := by
  intro i hi
  by_cases h : i = 0
  · subst i
    simpa [projectiveTateSpectrum] using hzero
  · apply tateSpectrum_above_cutoff_of_power_trace (cut := 0) hq A 0 hweight _ i hi (by omega)
    filter_upwards [htrace] with m hm
    simp [hm]

/-- A graded Frobenius trace with the growth of a smooth hypersurface
agrees with projective space outside the middle degree. The same growth
bounds the total middle multiplicity, including its possible Tate term. -/
theorem tateSpectrum_and_middleRank_of_power_trace {q N : ℕ} (hq : 1 < q)
    (A : ℕ → Multiset ℂ) (C : ℝ)
    (hweight : ∀ i ≤ 2*N, ∀ z ∈ A i, ‖z‖ = Real.sqrt ((q : ℝ)^i))
    (hdual : ∀ i ≤ 2*N, A (2*N-i) = (A i).map ((q : ℂ)^N / ·))
    (herror : ∀ᶠ m : ℕ in atTop,
      ‖(∑ i ∈ Finset.Iic (2*N), (-1 : ℂ)^i * ((A i).map (· ^ m)).sum) -
        (projectiveSpacePointCount (q^m) N : ℂ)‖ ≤ C * (Real.sqrt ((q : ℝ)^N))^m) :
    (∀ i ≤ 2*N, i ≠ N → A i = projectiveTateSpectrum q i) ∧
      ((A N).card : ℝ) ≤ C + 1 := by
  have hupper := tateSpectrum_above_cutoff_of_power_trace hq A C hweight herror
  have houter (i : ℕ) (hi : i ≤ 2*N) (hiN : i ≠ N) : A i = projectiveTateSpectrum q i := by
    rcases lt_or_gt_of_ne hiN with hlt | hgt
    · let j := 2*N-i
      have hj : j ≤ 2*N := by dsimp [j]; omega
      have hjN : N < j := by dsimp [j]; omega
      have he : 2*N-j = i := by dsimp [j]; omega
      rw [← he, hdual j hj, hupper j hj hjN, projectiveTateSpectrum_dual (by omega) hj]
    · exact hupper i hi hgt
  exact ⟨houter, middle_rank_bound_of_traceError hq A C
    (fun z hz => (hweight N (by omega) z hz).trans (sqrt_natCast_pow q N)) houter
    (traceError_eventually_le_of_projectivePowerTrace A C herror)⟩


/-- The graded spectrum of the Fermat hypersurface supplied by the smooth
proper Weil theorem has the ambient Tate eigenvalues outside the middle
degree, and its middle rank is bounded uniformly in the prime. -/
theorem tateSpectrum_and_middleRank_of_fermat_trace {p d N : ℕ} [Fact p.Prime]
    (hd : 0 < d) (A : ℕ → Multiset ℂ)
    (hweight : ∀ i ≤ 2*N, ∀ z ∈ A i, ‖z‖ = Real.sqrt ((p : ℝ)^i))
    (hdual : ∀ i ≤ 2*N, A (2*N-i) = (A i).map ((p : ℂ)^N / ·))
    (htrace : ∀ (E : Type) [Field E] [Algebra (ZMod p) E] [FiniteDimensional (ZMod p) E],
      let X := CategoryTheory.Over.mk
        (projectiveHypersurfaceToField (isHomogeneous_fermatPolynomial (ZMod p) N d))
      (Nat.card (CategoryTheory.Over.mk
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) E))) ⟶ X) : ℂ) =
        ∑ i ∈ Finset.Iic (2*N), (-1 : ℂ)^i * ((A i).map (· ^ Module.finrank (ZMod p) E)).sum) :
    (∀ i ≤ 2*N, i ≠ N → A i = projectiveTateSpectrum p i) ∧
      (A N).card ≤ (d-1)^(N+2) + 1 := by
  suffices h : (∀ i ≤ 2*N, i ≠ N → A i = projectiveTateSpectrum p i) ∧
      ((A N).card : ℝ) ≤ ((d : ℝ)-1)^(N+2) + 1 by
    refine ⟨h.1, ?_⟩
    have hrank : ((A N).card : ℝ) ≤ (((d-1)^(N+2) + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_sub (Nat.succ_le_of_lt hd), Nat.cast_one]
        using h.2
    exact_mod_cast hrank
  apply tateSpectrum_and_middleRank_of_power_trace (Fact.out : p.Prime).one_lt A
    (((d : ℝ)-1)^(N+2)) hweight hdual
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  let E := GaloisField p m
  have ht := htrace E
  dsimp only at ht
  rw [GaloisField.finrank p hm.ne'] at ht
  have h := abs_sub_projectiveSpacePointCount_overHom_fermat_le
    (F := ZMod p) (L := E) hd N
  dsimp only at h
  rw [GaloisField.card p m hm.ne'] at h
  rw [← ht]
  have hp0 := (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have he : (((p^m : ℕ) : ℝ))^((N : ℝ)/2) = (Real.sqrt ((p : ℝ)^N))^m := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast_mul hp0, ← Real.rpow_mul_natCast hp0]
    congr 1
    ring
  rw [he] at h
  simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

/-- The Weil trace of the ambient projective model gives exactly the Tate spectrum. -/
theorem tateSpectrum_of_projectivePolynomialSpace_trace {p N : ℕ} [Fact p.Prime]
    (A : ℕ → Multiset ℂ) (hzero : A 0 = {1})
    (hweight : ∀ i ≤ 2*N, ∀ z ∈ A i, ‖z‖ = Real.sqrt ((p : ℝ)^i))
    (htrace : ∀ (E : Type) [Field E] [Algebra (ZMod p) E] [FiniteDimensional (ZMod p) E],
      let X := CategoryTheory.Over.mk (projectivePolynomialSpaceToField (Fin (N+1)) (ZMod p))
      (Nat.card (CategoryTheory.Over.mk
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) E))) ⟶ X) : ℂ) =
        ∑ i ∈ Finset.Iic (2*N), (-1 : ℂ)^i * ((A i).map (· ^ Module.finrank (ZMod p) E)).sum) :
    ∀ i ≤ 2*N, A i = projectiveTateSpectrum p i := by
  apply eq_projectiveTateSpectrum_of_exact_power_trace (Fact.out : p.Prime).one_lt A hzero hweight
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  let E := GaloisField p m
  have h := htrace E
  dsimp only at h
  rw [natCard_overHom_projectivePolynomialSpace, GaloisField.card p m hm.ne',
    GaloisField.finrank p hm.ne'] at h
  exact h.symm

/-- The Weil trace on the Fermat model, rank comparison with that model,
and inclusion of the ambient eigenvalues determine the outer spectrum and
bound the middle rank of an arbitrary smooth hypersurface. -/
theorem tateSpectrum_and_middleRank_of_fermat_comparison {p d N : ℕ} [Fact p.Prime]
    (hd : 0 < d) (A AF : ℕ → Multiset ℂ)
    (hFweight : ∀ i ≤ 2 * N, ∀ z ∈ AF i, ‖z‖ = Real.sqrt ((p : ℝ)^i))
    (hFdual : ∀ i ≤ 2 * N, AF (2 * N - i) = (AF i).map ((p : ℂ)^N / ·))
    (hFtrace : ∀ (E : Type) [Field E] [Algebra (ZMod p) E] [FiniteDimensional (ZMod p) E],
      let X := Over.mk (projectiveHypersurfaceToField (isHomogeneous_fermatPolynomial (ZMod p) N d))
      (Nat.card (Over.mk (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) E))) ⟶ X) : ℂ) =
        ∑ i ∈ Finset.Iic (2 * N), (-1 : ℂ)^i * ((AF i).map (· ^ Module.finrank (ZMod p) E)).sum)
    (hrank : ∀ i ≤ 2 * N, (A i).card = (AF i).card)
    (hamb : ∀ i ≤ 2 * N, i ≠ N → projectiveTateSpectrum p i ≤ A i) :
    (∀ i ≤ 2 * N, i ≠ N → A i = projectiveTateSpectrum p i) ∧
      (A N).card ≤ (d - 1)^(N + 2) + 1 := by
  obtain ⟨houter, hmiddle⟩ := tateSpectrum_and_middleRank_of_fermat_trace hd AF hFweight hFdual hFtrace
  refine ⟨?_, (hrank N (by omega)).trans_le hmiddle⟩
  intro i hi hiN
  exact (Multiset.eq_of_le_of_card_le (hamb i hi hiN) (by rw [hrank i hi, houter i hi hiN])).symm

end

end Birch
