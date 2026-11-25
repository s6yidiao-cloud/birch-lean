import Birch.V2MajorArcShells
import Birch.V2CoverFourthMoment

/-! # Fixed-width major arcs for polynomial covers -/

open Set MeasureTheory
open scoped BigOperators Interval Polynomial

namespace Birch

noncomputable section

/-- The cover exponential sum is one-periodic in the frequency. -/
theorem coverYSum_periodic (g : ℤ[X]) (L : ℝ) : Function.Periodic (coverYSum g L) 1 := by
  intro α
  unfold coverYSum
  apply Finset.sum_congr rfl
  intro y _
  let m := g.eval y
  have hinter : -(α+1)*(m : ℝ) = -α*(m : ℝ) + ((-m : ℤ) : ℝ) := by push_cast; ring
  have hinteger : phase ((-m : ℤ) : ℝ) = 1 := by
    unfold phase
    have hcast : (((( -m : ℤ) : ℝ) : ℂ)) = ((-m : ℤ) : ℂ) := by push_cast; rfl
    rw [hcast, mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I (-m)
  change phase (-(α+1)*(m : ℝ)) = phase (-α*(m : ℝ))
  rw [hinter, phase_add, hinteger, mul_one]

/-- The normalized product of the form and cover sums is one-periodic. -/
theorem normalizedCoverProduct_periodic {n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (P Y L : ℝ) : Function.Periodic
      (fun α => normalizedSum F w P α * ((Y : ℂ)⁻¹ * coverYSum g L α)) 1 := by
  intro α
  dsimp only [normalizedSum]
  rw [exponentialSum_periodic, coverYSum_periodic]

/-- A single real lift of a fixed-width major interval. -/
def fixedWidthMajorInterval (W : ℝ) (q : ℕ) (a : ℤ) : Set ℝ :=
  Icc ((a : ℝ)/q-W) ((a : ℝ)/q+W)

theorem mem_fixedWidthMajorInterval {W α : ℝ} {q : ℕ} {a : ℤ} :
    α ∈ fixedWidthMajorInterval W q a ↔ |α-(a : ℝ)/q| ≤ W := by
  rw [fixedWidthMajorInterval, mem_Icc, abs_le]
  exact ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

/-- The reduced numerator and denominator pairs with centers in the open unit interval. -/
def v2InteriorMajorCenters (Δ P : ℝ) : Finset (ℕ × ℕ) :=
  interiorMajorCenters (P^(2*Δ))

theorem mem_v2InteriorMajorCenters {Δ P : ℝ} (hP : 0 ≤ P) {q a : ℕ} :
    (q,a) ∈ v2InteriorMajorCenters Δ P ↔
      2 ≤ q ∧ (q : ℝ) ≤ P^Δ ∧ 1 ≤ a ∧ a < q ∧ a.Coprime q := by
  rw [v2InteriorMajorCenters, mem_interiorMajorCenters (Real.rpow_nonneg hP _),
    ← Real.rpow_mul hP, show (2*Δ)*(1/2 : ℝ) = Δ by ring]

private theorem fixedWidthMajorIntervals_disjoint {Q W : ℝ} (hW : 0 ≤ W)
    (hsmall : (2*W)*Q^2 < 1) {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (hqQ : (q : ℝ) ≤ Q) (hsQ : (s : ℝ) ≤ Q) {a b : ℤ}
    (hne : (a : ℝ)/q ≠ (b : ℝ)/s) :
    Disjoint (fixedWidthMajorInterval W q a) (fixedWidthMajorInterval W s b) := by
  apply Set.disjoint_left.mpr
  intro α ha hb
  have hsep := rational_centers_separated hq hs a b hne
  have ht := abs_sub_le ((a : ℝ)/q) α ((b : ℝ)/s)
  rw [abs_sub_comm ((a : ℝ)/q) α] at ht
  have hdist := ht.trans (add_le_add (mem_fixedWidthMajorInterval.mp ha)
    (mem_fixedWidthMajorInterval.mp hb))
  have hprod : (q : ℝ)*s ≤ Q^2 := by
    rw [pow_two]
    exact mul_le_mul hqQ hsQ (Nat.cast_nonneg _) ((Nat.cast_nonneg q).trans hqQ)
  exact hsmall.not_ge (hsep.trans (mul_le_mul (by linarith) hprod (by positivity) (by positivity)))

private theorem fixedWidthMajorInterval_subset_Ioo {W : ℝ} {q a : ℕ}
    (hq : 2 ≤ q) (ha : 1 ≤ a) (haq : a < q) (hcop : a.Coprime q)
    (hsmall : W*(q : ℝ) < 1) : fixedWidthMajorInterval W q (a : ℤ) ⊆ Ioo 0 1 := by
  let Y := (q : ℝ)/2
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have he : 2*Y = (q : ℝ) := by dsimp [Y]; ring
  have hmem : (q,a) ∈ rationalShellCenters Y := by
    apply (mem_rationalShellCenters hY).2
    exact ⟨hq, by dsimp [Y]; linarith, he.ge, ha, haq, hcop⟩
  have hs := rationalShellInterval_subset_Ioo hY (he ▸ hsmall) hmem
  simpa only [fixedWidthMajorInterval, rationalShellInterval, Int.cast_natCast] using hs

private theorem fixedWidthUnitArcs_inter_Ioc {W : ℝ} (hW : 0 < W) (hW₁ : W < 1/2) :
    (⋃ a : ℤ, fixedWidthMajorInterval W 1 a) ∩ Ioc 0 1 =
      Ioc 0 W ∪ Icc (1-W) 1 := by
  ext α
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_fixedWidthMajorInterval, Nat.cast_one, div_one,
    Set.mem_Ioc, Set.mem_Icc, Set.mem_union]
  constructor
  · rintro ⟨⟨a,ha⟩,hα,hα'⟩
    rw [abs_le] at ha
    have ha0 : 0 ≤ a := by
      by_contra! h
      have h' : (a : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast (show a ≤ -1 by omega)
      linarith [ha.2]
    have ha1 : a ≤ 1 := by
      by_contra! h
      have h' : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
      linarith [ha.1]
    have hcases : a = 0 ∨ a = 1 := by omega
    rcases hcases with rfl | rfl
    · left
      push_cast at ha
      exact ⟨hα, by linarith [ha.2]⟩
    · right
      push_cast at ha
      exact ⟨by linarith [ha.1], hα'⟩
  · rintro (⟨hα,hα'⟩ | ⟨hα,hα'⟩)
    · refine ⟨⟨0, ?_⟩, hα, by linarith⟩
      simpa using (abs_le.mpr ⟨by linarith, hα'⟩ : |α| ≤ W)
    · refine ⟨⟨1, ?_⟩, by linarith, hα'⟩
      push_cast
      exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem integral_fixedWidthUnitArcs {W : ℝ} (hW : 0 < W) (hW₁ : W < 1/2)
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hfc : Continuous f) :
    (∫ α in ⋃ a : ℤ, fixedWidthMajorInterval W 1 a, f α ∂circleMeasure) =
      ∫ α in Icc (-W) W, f α := by
  have hdis : Disjoint (Ioc 0 W) (Icc (1-W) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.2, hy.1]
  have hInt₁ : IntegrableOn f (Ioc 0 W) := hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hInt₂ : IntegrableOn f (Icc (1-W) 1) := hfc.integrableOn_Icc
  have hmeas : MeasurableSet (⋃ a : ℤ, fixedWidthMajorInterval W 1 a) :=
    MeasurableSet.iUnion fun _ => measurableSet_Icc
  unfold circleMeasure
  rw [Measure.restrict_restrict hmeas, fixedWidthUnitArcs_inter_Ioc hW hW₁,
    setIntegral_union hdis measurableSet_Icc hInt₁ hInt₂,
    integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hW.le,
    ← intervalIntegral.integral_of_le (by linarith : 1-W ≤ 1),
    ← intervalIntegral.integral_of_le (by linarith : -W ≤ W)]
  have hwrap : (∫ α in (1-W)..1, f α) = ∫ α in (-W)..0, f α := by
    have h := intervalIntegral.integral_comp_add_right (a := -W) (b := 0) f 1
    rw [show (fun α : ℝ => f (α+1)) = f from funext hf] at h
    rw [show 1-W = -W+1 by ring]
    simpa only [zero_add] using h.symm
  rw [hwrap, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals (hfc.intervalIntegrable _ _)
    (hfc.intervalIntegrable _ _)

private theorem v2MajorWidth_bounds {d : ℕ} (hd : 2 ≤ d) {Δ P : ℝ} (hΔ : 0 ≤ Δ)
    (hΔ₁ : Δ ≤ 1/4) (hP : 2 ≤ P) :
    1 ≤ P^Δ ∧ 0 < P^(-(d : ℝ)+Δ) ∧ (2*P^(-(d : ℝ)+Δ)) * (P^Δ)^2 < 1 := by
  have hP₀ : 0 < P := by linarith
  have hP₁ : 1 < P := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨Real.one_le_rpow hP₁.le hΔ, Real.rpow_pos_of_pos hP₀ _, ?_⟩
  have hp : (P^Δ)^2 = P^(2*Δ) := by
    rw [← Real.rpow_mul_natCast hP₀.le]
    congr 1
    norm_num [mul_comm]
  rw [hp, mul_assoc, ← Real.rpow_add hP₀]
  have hs : P^(-(d : ℝ)+Δ+2*Δ) < P^(-1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hP₁ (by linarith)
  have hb : P^(-1 : ℝ) ≤ 1/2 := by
    rw [Real.rpow_neg_one, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hP
  linarith

private theorem fixedWidthDenom_bound {W Q q : ℝ} (hW : 0 ≤ W) (hQ : 1 ≤ Q)
    (hq : q ≤ Q) (hsmall : (2*W)*Q^2 < 1) : W*q < 1 := by
  have hQQ : Q ≤ Q^2 := by nlinarith
  calc
    _ ≤ W*Q^2 := mul_le_mul_of_nonneg_left (hq.trans hQQ) hW
    _ ≤ (2*W)*Q^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ < 1 := hsmall

/-- On the fundamental interval, the only wrapped major interval is the one
at unit conductor. Every other interval is attached to a finite reduced pair. -/
theorem v2MajorArcs_inter_Ioc {d : ℕ} (hd : 2 ≤ d) {Δ P : ℝ} (hΔ : 0 ≤ Δ)
    (hΔ₁ : Δ ≤ 1/4) (hP : 2 ≤ P) :
    let W := P^(-(d : ℝ)+Δ)
    v2MajorArcs d Δ P ∩ Ioc 0 1 =
      ((⋃ a : ℤ, fixedWidthMajorInterval W 1 a) ∩ Ioc 0 1) ∪
        ⋃ j ∈ v2InteriorMajorCenters Δ P, fixedWidthMajorInterval W j.1 (j.2 : ℤ) := by
  let W := P^(-(d : ℝ)+Δ)
  obtain ⟨hQ,hW,hsmall⟩ := v2MajorWidth_bounds hd hΔ hΔ₁ hP
  have hP₀ : 0 ≤ P := by linarith
  ext α
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨hα,hαI⟩
    obtain ⟨q,a,hq,hqQ,hcop,hnear⟩ := hα
    by_cases hq₁ : q = 1
    · subst q
      exact Or.inl ⟨⟨a,mem_fixedWidthMajorInterval.mpr hnear⟩,hαI⟩
    have hq₂ : 2 ≤ q := by omega
    have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
    have hbound := fixedWidthDenom_bound hW.le hQ hqQ hsmall
    have hdist : |(q : ℝ)*α-a| ≤ W*q := by
      rw [show (q : ℝ)*α-a = (α-(a : ℝ)/q)*q by field_simp,
        abs_mul, abs_of_pos hqpos]
      exact mul_le_mul_of_nonneg_right hnear hqpos.le
    have hlo : 0 < (q : ℝ)*α := mul_pos hqpos hαI.1
    have hhi : (q : ℝ)*α ≤ q := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hαI.2 hqpos.le
    rw [abs_le] at hdist
    have ha₀ : 0 ≤ a := by
      by_contra! h
      have h' : (a : ℝ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
      linarith [hdist.2]
    have ha₁ : a ≤ q := by
      by_contra! h
      have h' : (q : ℝ) + 1 ≤ a := by exact_mod_cast (show (q : ℤ)+1 ≤ a by omega)
      linarith [hdist.1]
    obtain ⟨a,rfl⟩ : ∃ b : ℕ, a = (b : ℤ) := ⟨a.toNat,(Int.toNat_of_nonneg ha₀).symm⟩
    simp only [Int.natAbs_natCast] at hcop
    have hap : 1 ≤ a := by
      by_contra! h
      have hz : a = 0 := by omega
      simp [hz] at hcop
      exact hq₁ hcop
    have haq : a < q := by
      by_contra! h
      have h' : a ≤ q := by exact_mod_cast ha₁
      have he : a = q := by omega
      simp [he] at hcop
      exact hq₁ hcop
    exact Or.inr ⟨(q,a), (mem_v2InteriorMajorCenters hP₀).mpr ⟨hq₂,hqQ,hap,haq,hcop⟩,
      mem_fixedWidthMajorInterval.mpr hnear⟩
  · rintro (⟨⟨a,ha⟩,hαI⟩ | ⟨⟨q,a⟩,hmem,hnear⟩)
    · exact ⟨⟨1,a,zero_lt_one,by exact_mod_cast hQ,Nat.coprime_one_right _,
        mem_fixedWidthMajorInterval.mp ha⟩,hαI⟩
    · obtain ⟨hq,hqQ,ha,haq,hcop⟩ := (mem_v2InteriorMajorCenters hP₀).mp hmem
      have hαI := fixedWidthMajorInterval_subset_Ioo hq ha haq hcop
        (fixedWidthDenom_bound hW.le hQ hqQ hsmall) hnear
      exact ⟨⟨q,a,by omega,hqQ,by simpa using hcop,mem_fixedWidthMajorInterval.mp hnear⟩,
        Ioo_subset_Ioc_self hαI⟩

/-- Integrating a continuous periodic function on the fixed-width major arcs
reduces to ordinary real integrals over the finite reduced centers. -/
theorem integral_v2MajorArcs_eq_sum {d : ℕ} (hd : 2 ≤ d) {Δ P : ℝ}
    (hΔ : 0 ≤ Δ) (hΔ₁ : Δ ≤ 1/4) (hP : 2 ≤ P) {f : ℝ → ℂ}
    (hf : Function.Periodic f 1) (hfc : Continuous f) :
    let W := P^(-(d : ℝ)+Δ)
    (∫ α in v2MajorArcs d Δ P, f α ∂circleMeasure) =
      (∫ α in Icc (-W) W, f α) +
        ∑ j ∈ v2InteriorMajorCenters Δ P, ∫ α in fixedWidthMajorInterval W j.1 (j.2 : ℤ), f α := by
  let W := P^(-(d : ℝ)+Δ)
  let unit := ⋃ a : ℤ, fixedWidthMajorInterval W 1 a
  let A (j : ℕ × ℕ) := fixedWidthMajorInterval W j.1 (j.2 : ℤ)
  let U := v2InteriorMajorCenters Δ P
  have hP₀ : 0 ≤ P := by linarith
  obtain ⟨hQ,hW,hsmall⟩ := v2MajorWidth_bounds hd hΔ hΔ₁ hP
  have hQsq : (1 : ℝ) ≤ (P^Δ)^2 := one_le_pow₀ hQ
  have hhalf : W < 1/2 := by
    have h := mul_le_mul_of_nonneg_left hQsq (by positivity : 0 ≤ 2*W)
    rw [mul_one] at h
    linarith [h.trans_lt hsmall]
  have hmeasUnit : MeasurableSet unit := MeasurableSet.iUnion fun _ => measurableSet_Icc
  have hmeas (j : ℕ × ℕ) : MeasurableSet (A j) := measurableSet_Icc
  have hint (j : ℕ × ℕ) : IntegrableOn f (A j) := hfc.integrableOn_Icc
  have hpair : Set.Pairwise (↑U) (fun j k => Disjoint (A j) (A k)) := by
    rintro ⟨q,a⟩ hj ⟨s,b⟩ hk hne
    obtain ⟨hq,hqQ,_,_,ha⟩ := (mem_v2InteriorMajorCenters hP₀).mp hj
    obtain ⟨hs,hsQ,_,_,hb⟩ := (mem_v2InteriorMajorCenters hP₀).mp hk
    have hq₀ : 0 < q := by omega
    have hs₀ : 0 < s := by omega
    apply fixedWidthMajorIntervals_disjoint hW.le hsmall hq₀ hs₀ hqQ hsQ
    intro he
    have hqs := denominator_dvd_of_fraction_eq hq₀ hs₀ (by simpa using ha) he
    have hsq := denominator_dvd_of_fraction_eq hs₀ hq₀ (by simpa using hb) he.symm
    obtain rfl := Nat.dvd_antisymm hqs hsq
    have he' := (div_left_inj' (by positivity : (q : ℝ) ≠ 0)).mp he
    exact hne (Prod.ext rfl (by exact_mod_cast he'))
  have hunitSep : Disjoint (unit ∩ Ioc 0 1) (⋃ j ∈ U, A j) := by
    apply Set.disjoint_left.mpr
    intro α hα hu
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hα.1
    obtain ⟨⟨q,b⟩,hh⟩ := Set.mem_iUnion.mp hu
    obtain ⟨hm,hb⟩ := Set.mem_iUnion.mp hh
    obtain ⟨hq,hqQ,_,_,hcop⟩ := (mem_v2InteriorMajorCenters hP₀).mp hm
    have hq₀ : 0 < q := by omega
    have hneq : (a : ℝ)/(1 : ℕ) ≠ ((b : ℤ) : ℝ)/q := by
      intro he
      have hdiv := denominator_dvd_of_fraction_eq hq₀ Nat.zero_lt_one (by simpa using hcop) he.symm
      have hb₁ := Nat.le_of_dvd Nat.zero_lt_one hdiv
      omega
    exact Set.disjoint_left.mp
      (fixedWidthMajorIntervals_disjoint hW.le hsmall Nat.zero_lt_one hq₀ (by exact_mod_cast hQ) hqQ hneq)
      ha hb
  have hIntUnit : IntegrableOn f (unit ∩ Ioc 0 1) :=
    hfc.integrableOn_Icc.mono_set (inter_subset_right.trans Ioc_subset_Icc_self)
  have hwrap : (∫ α in unit ∩ Ioc 0 1, f α) = ∫ α in Icc (-W) W, f α := by
    have hu := integral_fixedWidthUnitArcs hW hhalf hf hfc
    unfold circleMeasure at hu
    rwa [Measure.restrict_restrict hmeasUnit] at hu
  unfold circleMeasure
  rw [Measure.restrict_restrict (measurableSet_v2MajorArcs d Δ P), v2MajorArcs_inter_Ioc hd hΔ hΔ₁ hP,
    setIntegral_union hunitSep (U.measurableSet_biUnion (fun j _ => hmeas j)) hIntUnit
      (integrableOn_finset_iUnion.2 fun j _ => hint j),
    hwrap, integral_biUnion_finset U (fun j _ => hmeas j) hpair (fun j _ => hint j)]

/-- The change of variables on a fixed-width major arc has Jacobian
`P^(-d)` and frequency cutoff `P^Δ`, independent of the denominator. -/
theorem integral_fixedWidthMajorInterval_substitution (d : ℕ) (Δ : ℝ) {P : ℝ} (hP : 0 < P)
    (q : ℕ) (a : ℤ) (f : ℝ → ℂ) :
    (∫ α in fixedWidthMajorInterval (P^(-(d : ℝ)+Δ)) q a, f (P^d * (α-(a : ℝ)/q))) =
      (P^(-(d : ℝ)) : ℝ) • ∫ γ in Icc (-P^Δ) (P^Δ), f γ := by
  let c := (a : ℝ)/q
  let W := P^(-(d : ℝ)+Δ)
  have hW : 0 < W := Real.rpow_pos_of_pos hP _
  have hv : 0 < P^Δ := Real.rpow_pos_of_pos hP _
  have hscale : P^d * W = P^Δ := by
    dsimp [W]
    rw [← Real.rpow_natCast, ← Real.rpow_add hP]
    congr 1
    ring
  rw [fixedWidthMajorInterval, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  change (∫ α in Ioc (c-W) (c+W), f (P^d*(α-c))) =
    (P^(-(d : ℝ)) : ℝ) • ∫ γ in Ioc (-P^Δ) (P^Δ), f γ
  rw [← intervalIntegral.integral_of_le (by linarith : c-W ≤ c+W),
    ← intervalIntegral.integral_of_le (by linarith : -P^Δ ≤ P^Δ)]
  rw [intervalIntegral.integral_comp_sub_right (fun x => f (P^d*x)) c,
    show c-W-c = -W by ring, show c+W-c = W by ring,
    intervalIntegral.integral_comp_mul_left f (pow_ne_zero _ hP.ne'),
    mul_neg, hscale, Real.rpow_neg hP.le, Real.rpow_natCast]

/-- The interior rational centers have at most the square of the denominator cutoff. -/
theorem v2InteriorMajorCenters_card_le {Δ P : ℝ} (hP : 0 ≤ P) :
    ((v2InteriorMajorCenters Δ P).card : ℝ) ≤ (P^Δ)^2 := by
  let Q := ⌊P^Δ⌋₊
  have hsub : v2InteriorMajorCenters Δ P ⊆ (Finset.Icc 1 Q).product (Finset.Icc 1 Q) := by
    rintro ⟨q,a⟩ h
    obtain ⟨hq,hqP,ha,haq,_⟩ := (mem_v2InteriorMajorCenters hP).mp h
    have hqQ := Nat.le_floor hqP
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hqQ⟩,
      Finset.mem_Icc.mpr ⟨ha,haq.le.trans hqQ⟩⟩
  have hn := Finset.card_le_card hsub
  simp only [Finset.product_eq_sprod, Finset.card_product, Nat.card_Icc,
    add_tsub_cancel_right] at hn
  calc
    _ ≤ (Q : ℝ)*(Q : ℝ) := by exact_mod_cast hn
    _ ≤ (P^Δ)^2 := by
      rw [pow_two]
      have hQ := Nat.floor_le (Real.rpow_nonneg hP Δ)
      exact mul_le_mul hQ hQ (by positivity) (by positivity)

/-- The finite sum over interior major centers grouped by denominator. -/
theorem sum_v2InteriorMajorCenters_by_denominator {A : Type*} [AddCommMonoid A]
    {Δ P : ℝ} (hP : 0 ≤ P) (f : ℕ → ℕ → A) :
    (∑ j ∈ v2InteriorMajorCenters Δ P, f j.1 j.2) =
      ∑ q ∈ Finset.Icc 2 ⌊P^Δ⌋₊,
        ∑ a ∈ (Finset.Ico 1 q).filter (fun a => a.Coprime q), f q a := by
  classical
  rw [Finset.sum_sigma']
  have hs (q a : ℕ) : (q,a) ∈ v2InteriorMajorCenters Δ P ↔
      (⟨q,a⟩ : Σ _ : ℕ, ℕ) ∈ (Finset.Icc 2 ⌊P^Δ⌋₊).sigma
        (fun s => (Finset.Ico 1 s).filter (fun b => b.Coprime s)) := by
    rw [mem_v2InteriorMajorCenters hP]
    simp only [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ico,
      Nat.le_floor_iff (Real.rpow_nonneg hP Δ), and_assoc]
  apply Finset.sum_bij (fun j _ => (⟨j.1,j.2⟩ : Σ _ : ℕ, ℕ))
  · intro j hj
    exact (hs j.1 j.2).mp hj
  · intro j _ j' _ he
    exact Prod.ext (congrArg Sigma.fst he) (congrArg (fun s : Σ _ : ℕ, ℕ => s.2) he)
  · rintro ⟨q,a⟩ hj
    exact ⟨(q,a),(hs q a).mpr hj,rfl⟩
  · intros
    rfl

/-- The product of the form and cover complete sums, extended by zero at modulus zero. -/
def coverCompleteProductAt {n : ℕ} (F : IntForm n) (g : ℤ[X]) (q : ℕ) (a : ℤ) : ℂ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    completeSum F q (a : ZMod q) * coverCompleteSum g q (a : ZMod q)

theorem coverCompleteProductAt_eq {n q : ℕ} [NeZero q] (F : IntForm n) (g : ℤ[X]) (a : ℤ) :
    coverCompleteProductAt F g q a = completeSum F q (a : ZMod q) * coverCompleteSum g q (a : ZMod q) :=
  dite_eq_right (NeZero.ne q)

/-- The summed coefficients in the fixed-width cover arcs are exactly the
initial terms of the cover singular series. -/
theorem coverCompleteProduct_sum_eq_truncation {n : ℕ} (F : IntForm n) (g : ℤ[X])
    {Δ P : ℝ} (hP : 1 ≤ P) (hΔ : 0 ≤ Δ) :
    coverCompleteProductAt F g 1 0 +
        ∑ j ∈ v2InteriorMajorCenters Δ P, coverCompleteProductAt F g j.1 (j.2 : ℤ) =
      ∑ j ∈ Finset.range ⌊P^Δ⌋₊, coverConductorSum F g (j+1) := by
  let Q := ⌊P^Δ⌋₊
  let A := singularSeriesTerm (coverPolynomial F g)
  have hP₀ : 0 ≤ P := zero_le_one.trans hP
  have hQ : 1 ≤ Q := Nat.le_floor (by simpa using Real.one_le_rpow hP hΔ)
  have hone : coverCompleteProductAt F g 1 0 = A 1 := by
    rw [coverCompleteProductAt_eq, ← completeSum_coverPolynomial, completeSum_one]
    simp [A,singularSeriesTerm,unitConductorSum_one]
  have hsum : (∑ j ∈ v2InteriorMajorCenters Δ P,
      coverCompleteProductAt F g j.1 (j.2 : ℤ)) = ∑ q ∈ Finset.Icc 2 Q, A q := by
    rw [sum_v2InteriorMajorCenters_by_denominator hP₀ (fun q a => coverCompleteProductAt F g q (a : ℤ))]
    apply Finset.sum_congr rfl
    intro q hq
    have hq₂ := (Finset.mem_Icc.mp hq).1
    have hq₀ : q ≠ 0 := by omega
    let : NeZero q := ⟨hq₀⟩
    simp only [coverCompleteProductAt_eq, Int.cast_natCast, A, singularSeriesTerm, dite_eq_right hq₀,
      ← coverConductorSum_eq_unitConductorSum, coverConductorSum]
    exact (sum_zmod_units_eq_reducedNumerators q hq₂
      (fun a => completeSum F q a * coverCompleteSum g q a)).symm
  have hins : Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hshift : (∑ j ∈ Finset.range Q, A (j+1)) = ∑ q ∈ Finset.Icc 1 Q, A q := by
    rw [← Finset.Ico_succ_right_eq_Icc 1 Q]
    change _ = ∑ q ∈ Finset.Ico 1 (Q+1), A q
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm]
  have hseries : (∑ j ∈ Finset.range Q, coverConductorSum F g (j+1)) =
      ∑ j ∈ Finset.range Q, A (j+1) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [A, singularSeriesTerm, dite_eq_right (Nat.succ_ne_zero j), coverConductorSum_eq_unitConductorSum]
  rw [hone,hsum,hseries,hshift,hins,Finset.sum_insert]
  simp

/-- A uniform pointwise error on the fixed-width arcs gives the corresponding
integrated error, with one factor for the total length of the arcs. -/
theorem norm_integral_v2MajorArcs_sub_main_le {d : ℕ} (hd : 2 ≤ d) {Δ P : ℝ}
    (hΔ : 0 ≤ Δ) (hΔ₁ : Δ ≤ 1/4) (hP : 2 ≤ P)
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hfc : Continuous f)
    (coeff : ℕ → ℤ → ℂ) {I : ℝ → ℂ} (hI : Continuous I) {E : ℝ} (hE : 0 ≤ E)
    (hpoint : ∀ (q : ℕ) (a : ℤ), 0 < q → (q : ℝ) ≤ P^Δ → a.natAbs.Coprime q →
      ∀ α ∈ fixedWidthMajorInterval (P^(-(d : ℝ)+Δ)) q a,
        ‖f α - coeff q a * I (P^d * (α-(a : ℝ)/q))‖ ≤ E) :
    ‖(∫ α in v2MajorArcs d Δ P, f α ∂circleMeasure) -
      (P^(-(d : ℝ)) : ℝ) • ((coeff 1 0 +
        ∑ j ∈ v2InteriorMajorCenters Δ P, coeff j.1 (j.2 : ℤ)) *
          ∫ γ in Icc (-P^Δ) (P^Δ), I γ)‖ ≤ 4*E*P^(-(d : ℝ)+3*Δ) := by
  have hP₀ : 0 < P := by linarith
  let Q := P^Δ
  let W := P^(-(d : ℝ)+Δ)
  let U := v2InteriorMajorCenters Δ P
  let J := ∫ γ in Icc (-Q) Q, I γ
  let A (q : ℕ) (a : ℤ) := ∫ α in fixedWidthMajorInterval W q a, f α
  let main (q : ℕ) (a : ℤ) := (P^(-(d : ℝ)) : ℝ) • (coeff q a * J)
  obtain ⟨hQ,hW,_⟩ := v2MajorWidth_bounds hd hΔ hΔ₁ hP
  have hl (q : ℕ) (a : ℤ) (hq : 0 < q) (hqQ : (q : ℝ) ≤ Q) (ha : a.natAbs.Coprime q) :
      ‖A q a - main q a‖ ≤ E*(2*W) := by
    let M (α : ℝ) := coeff q a * I (P^d*(α-(a : ℝ)/q))
    let arc := fixedWidthMajorInterval W q a
    have hM : Continuous M := continuous_const.mul (hI.comp (by fun_prop))
    have hMain : (∫ α in arc, M α) = main q a := by
      have hcut : (∫ γ in Icc (-Q) Q, coeff q a * I γ) = coeff q a * J := integral_const_mul _ _
      change (∫ α in arc, M α) = (P^(-(d : ℝ)) : ℝ) • (coeff q a * J)
      rw [← hcut]
      exact integral_fixedWidthMajorInterval_substitution d Δ hP₀ q a (fun γ => coeff q a * I γ)
    have hfI : IntegrableOn f arc := hfc.integrableOn_Icc
    have hMI : IntegrableOn M arc := hM.integrableOn_Icc
    have hfin : volume arc < ⊤ := measure_Icc_lt_top
    have hvol : volume.real arc = 2*W := by
      dsimp [arc,fixedWidthMajorInterval]
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring
    change ‖(∫ α in arc, f α) - main q a‖ ≤ _
    rw [← hMain, ← integral_sub hfI hMI]
    exact (norm_setIntegral_le_of_norm_le_const hfin (hpoint q a hq hqQ ha)).trans_eq
      (by rw [hvol])
  have hun : ‖A 1 0 - main 1 0‖ ≤ E*(2*W) := hl 1 0 zero_lt_one (by exact_mod_cast hQ)
    (Nat.coprime_one_right _)
  have hl' (j : ℕ × ℕ) (hj : j ∈ U) : ‖A j.1 (j.2 : ℤ) - main j.1 (j.2 : ℤ)‖ ≤ E*(2*W) := by
    obtain ⟨q,a⟩ := j
    obtain ⟨hq,hqQ,_,_,hcop⟩ := (mem_v2InteriorMajorCenters hP₀.le).mp hj
    exact hl q a (by omega) hqQ (by simpa using hcop)
  have hsplit : (∫ α in v2MajorArcs d Δ P, f α ∂circleMeasure) =
      A 1 0 + ∑ j ∈ U, A j.1 (j.2 : ℤ) := by
    rw [integral_v2MajorArcs_eq_sum hd hΔ hΔ₁ hP hf hfc]
    have he : fixedWidthMajorInterval W 1 0 = Icc (-W) W := by simp [fixedWidthMajorInterval]
    unfold A
    rw [he]
  have hMSplit : (P^(-(d : ℝ)) : ℝ) •
      ((coeff 1 0 + ∑ j ∈ U, coeff j.1 (j.2 : ℤ))*J) =
        main 1 0 + ∑ j ∈ U, main j.1 (j.2 : ℤ) := by
    rw [add_mul, Finset.sum_mul, smul_add, Finset.smul_sum]
  change ‖(∫ α in v2MajorArcs d Δ P, f α ∂circleMeasure) -
    (P^(-(d : ℝ)) : ℝ) • ((coeff 1 0 + ∑ j ∈ U, coeff j.1 (j.2 : ℤ))*J)‖ ≤ _
  rw [hsplit, hMSplit, add_sub_add_comm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ‖A 1 0 - main 1 0‖ + ∑ j ∈ U, ‖A j.1 (j.2 : ℤ) - main j.1 (j.2 : ℤ)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ E*(2*W) + ∑ _j ∈ U, E*(2*W) := add_le_add hun (Finset.sum_le_sum hl')
    _ = (1+(U.card : ℝ)) * (E*(2*W)) := by rw [Finset.sum_const,nsmul_eq_mul,add_mul,one_mul]
    _ ≤ (2*Q^2) * (E*(2*W)) := by
      have hcard : (U.card : ℝ) ≤ Q^2 := v2InteriorMajorCenters_card_le hP₀.le
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [one_le_pow₀ hQ (n := 2)]
    _ = _ := by
      have hq : Q^2 = P^(2*Δ) := by
        dsimp [Q]
        rw [← Real.rpow_mul_natCast hP₀.le]
        congr 1
        norm_num [mul_comm]
      rw [hq]
      dsimp [W]
      rw [show -(d : ℝ)+3*Δ = 2*Δ + (-(d : ℝ)+Δ) by ring,
        Real.rpow_add hP₀ (2*Δ) (-(d : ℝ)+Δ)]
      ring

end

end Birch
