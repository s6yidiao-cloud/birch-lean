import Birch.CircleMethod

/-!
# Separation and the unit denominator on the major arcs

The arc estimate compares distinct lifted rational centers. The sole reduced
conductor-one center is also treated at the boundary of the interval used to
represent the circle.
-/

open MeasureTheory Set
open scoped BigOperators Interval

namespace Birch

noncomputable section

/-- The numerator in the major-arc radius. -/
def majorArcWidth (d : ℕ) (P : ℝ) : ℝ := P ^ (-(d : ℝ) + 7 / 8)

/-- The major interval around one particular real lift of the reduced fraction. -/
def liftedMajorArc (d : ℕ) (P : ℝ) (q : ℕ) (a : ℤ) : Set ℝ :=
  {α | |α - (a : ℝ) / q| ≤ majorArcWidth d P / q}

theorem majorArcWidth_pos_lt_half {d : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 4 ≤ P) :
    0 < majorArcWidth d P ∧ majorArcWidth d P < 1 / 2 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hP' : 1 < P := by linarith
  unfold majorArcWidth
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  calc
    _ < P ^ (-1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hP' (by linarith)
    _ ≤ _ := by
      rw [Real.rpow_neg_one, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- Distinct lifted rational centers below the denominator cutoff have disjoint
major intervals. The denominator bound and width are those in the source. -/
theorem liftedMajorArcs_disjoint {d : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 4 ≤ P)
    {q s : ℕ} (hq : 0 < q) (hs : 0 < s) (hq' : (q : ℝ) ≤ P^(1/2 : ℝ))
    (hs' : (s : ℝ) ≤ P^(1/2 : ℝ)) {a b : ℤ}
    (hdistinct : (a : ℝ) / q ≠ (b : ℝ) / s) :
    Disjoint (liftedMajorArc d P q a) (liftedMajorArc d P s b) := by
  have hPpos : 0 < P := by linarith
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hqs := mul_pos hqR hsR
  let W := majorArcWidth d P
  have hW := (majorArcWidth_pos_lt_half hd hP).1
  change 0 < W at hW
  let m : ℤ := a * (s : ℤ) - b * (q : ℤ)
  have hcast : (m : ℝ) = ((a : ℝ) / q - (b : ℝ) / s) * ((q : ℝ) * s) := by
    dsimp [m]
    push_cast
    field_simp
  have hm : m ≠ 0 := by
    intro hm
    rw [hm, Int.cast_zero, eq_comm] at hcast
    exact (mul_ne_zero (sub_ne_zero.mpr hdistinct) hqs.ne') hcast
  have hunit : 1 ≤ |(m : ℝ)| := by
    by_contra! h
    obtain ⟨hl, hu⟩ := abs_lt.mp h
    have hl' : (-1 : ℤ) < m := by exact_mod_cast hl
    have hu' : m < (1 : ℤ) := by exact_mod_cast hu
    exact hm (by omega)
  refine Set.disjoint_left.mpr fun α hα hβ => ?_
  change |α - (a : ℝ) / q| ≤ W / q at hα
  change |α - (b : ℝ) / s| ≤ W / s at hβ
  have htriangle : |(a : ℝ) / q - (b : ℝ) / s| ≤ W / q + W / s := by
    have htri := abs_sub_le ((a : ℝ) / q) α ((b : ℝ) / s)
    rw [abs_sub_comm ((a : ℝ) / q) α] at htri
    exact htri.trans (add_le_add hα hβ)
  have hbound : 1 ≤ (2 : ℝ) * P ^ (-(d : ℝ) + 11 / 8) := by
    calc
      1 ≤ |(m : ℝ)| := hunit
      _ = |(a : ℝ) / q - (b : ℝ) / s| * ((q : ℝ) * s) := by
        rw [hcast, abs_mul, abs_of_pos hqs]
      _ ≤ (W / q + W / s) * ((q : ℝ) * s) := mul_le_mul_of_nonneg_right htriangle hqs.le
      _ = ((q : ℝ) + s) * W := by
        field_simp
        ring
      _ ≤ (2 * P^(1/2 : ℝ)) * W := mul_le_mul_of_nonneg_right (by linarith) hW.le
      _ = _ := by
        dsimp [W, majorArcWidth]
        rw [mul_assoc, ← Real.rpow_add hPpos]
        congr 2
        ring
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hexp : P ^ (-(d : ℝ) + 11 / 8) < P ^ (-(1/2) : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  have hsmall : 2 * P ^ (-(1/2) : ℝ) ≤ 1 := by
    rw [Real.rpow_neg hPpos.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    apply (div_le_one (Real.sqrt_pos.2 hPpos)).2
    exact (show (2 : ℝ) ≤ Real.sqrt 4 by norm_num).trans (Real.sqrt_le_sqrt hP)
  exact (not_lt_of_ge hbound) ((mul_lt_mul_of_pos_left hexp (by norm_num)).trans_le hsmall)

/-- A fraction strictly between zero and one has its entire major interval in
the interior of the fundamental domain. -/
theorem liftedMajorArc_subset_Ioo {d : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 4 ≤ P)
    {q : ℕ} (hq : 0 < q) {a : ℤ} (ha : 0 < a) (haq : a < (q : ℤ)) :
    liftedMajorArc d P q a ⊆ Ioo 0 1 := by
  let W := majorArcWidth d P
  have hW : W < 1 / 2 := (majorArcWidth_pos_lt_half hd hP).2
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have haqR : (a : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (show a + 1 ≤ (q : ℤ) by omega)
  intro α hα
  change |α - (a : ℝ) / q| ≤ W / q at hα
  have hlin : |(q : ℝ) * α - (a : ℝ)| ≤ W := by
    have heq : (q : ℝ) * (α - (a : ℝ) / q) = (q : ℝ) * α - a := by field_simp
    rw [← heq, abs_mul, abs_of_pos hqR, mul_comm (q : ℝ)]
    exact (le_div_iff₀ hqR).mp hα
  have hαlo : 0 < (q : ℝ) * α := by linarith [(abs_le.mp hlin).1]
  have hαhi : (q : ℝ) * α < q := by linarith [(abs_le.mp hlin).2]
  exact ⟨(mul_pos_iff_of_pos_left hqR).mp hαlo,
    (mul_lt_mul_iff_of_pos_left hqR).mp (by simpa using hαhi)⟩

/-- The conductor-one arcs on the fundamental interval form two pieces. -/
theorem liftedUnitArcs_inter_Ioc {d : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 4 ≤ P) :
    (⋃ a : ℤ, liftedMajorArc d P 1 a) ∩ Ioc 0 1 =
      Ioc 0 (majorArcWidth d P) ∪ Icc (1 - majorArcWidth d P) 1 := by
  let W := majorArcWidth d P
  have hW : 0 < W ∧ W < 1 / 2 := majorArcWidth_pos_lt_half hd hP
  ext α
  simp only [Set.mem_inter_iff, Set.mem_iUnion, liftedMajorArc, Set.mem_ofPred_eq,
    Nat.cast_one, div_one, Set.mem_Ioc, Set.mem_Icc, Set.mem_union]
  change ((∃ a : ℤ, |α - (a : ℝ)| ≤ W) ∧ 0 < α ∧ α ≤ 1) ↔
    (0 < α ∧ α ≤ W) ∨ (1 - W ≤ α ∧ α ≤ 1)
  constructor
  · rintro ⟨⟨a, ha⟩, hα, hα'⟩
    rw [abs_le] at ha
    have ha0 : 0 ≤ a := by
      by_contra! h
      have h' : (a : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast (show a ≤ -1 by omega)
      linarith [hW.2]
    have ha1 : a ≤ 1 := by
      by_contra! h
      have h' : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
      linarith [hW.2]
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · left
      push_cast at ha
      exact ⟨hα, by linarith [ha.2]⟩
    · right
      push_cast at ha
      exact ⟨by linarith [ha.1], hα'⟩
  · rintro (⟨hα, hα'⟩ | ⟨hα, hα'⟩)
    · refine ⟨⟨0, ?_⟩, hα, by linarith [hW.2]⟩
      simpa using (abs_le.mpr ⟨by linarith [hW.1], hα'⟩ : |α| ≤ W)
    · refine ⟨⟨1, ?_⟩, by linarith [hW.2], hα'⟩
      push_cast
      exact abs_le.mpr ⟨by linarith, by linarith [hW.1]⟩

/-- Integration of a continuous periodic function on the conductor-one arcs
agrees with its integral on the single centered interval. -/
theorem integral_liftedUnitArcs {d : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 4 ≤ P)
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hfc : Continuous f) :
    (∫ α in ⋃ a : ℤ, liftedMajorArc d P 1 a, f α ∂circleMeasure) =
      ∫ α in Icc (-majorArcWidth d P) (majorArcWidth d P), f α := by
  let W := majorArcWidth d P
  have hW : 0 < W ∧ W < 1 / 2 := majorArcWidth_pos_lt_half hd hP
  have hdis : Disjoint (Ioc 0 W) (Icc (1 - W) 1) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.2, hy.1, hW.2]
  have hInt₁ : IntegrableOn f (Ioc 0 W) := hfc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hInt₂ : IntegrableOn f (Icc (1 - W) 1) := hfc.integrableOn_Icc
  have hInt₁' : IntervalIntegrable f volume 0 W := hfc.intervalIntegrable _ _
  have hInt₂' : IntervalIntegrable f volume (-W) 0 := hfc.intervalIntegrable _ _
  have hmeas : MeasurableSet (⋃ a : ℤ, liftedMajorArc d P 1 a) :=
    MeasurableSet.iUnion fun _ =>
      (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
  unfold circleMeasure
  rw [Measure.restrict_restrict hmeas, liftedUnitArcs_inter_Ioc hd hP]
  rw [setIntegral_union hdis measurableSet_Icc hInt₁ hInt₂]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hW.1.le,
    ← intervalIntegral.integral_of_le (by linarith [hW.1] : 1 - W ≤ 1),
    ← intervalIntegral.integral_of_le (by linarith [hW.1] : -W ≤ W)]
  have hwrap : (∫ α in (1 - W)..1, f α) = ∫ α in (-W)..0, f α := by
    have h := intervalIntegral.integral_comp_add_right (a := -W) (b := 0) f 1
    have hshift : (fun α : ℝ => f (α + 1)) = f := funext hf
    rw [hshift] at h
    rw [show 1 - W = -W + 1 by ring]
    simpa only [zero_add] using h.symm
  rw [hwrap, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals hInt₂' hInt₁'

/-- The exponential sum is one-periodic in the frequency as every lattice phase
has integral coefficient. -/
theorem exponentialSum_periodic {n : ℕ} (F : IntForm n)
    (w : (Fin n → ℝ) → ℝ) (P : ℝ) : Function.Periodic (exponentialSum F w P) 1 := by
  intro α
  unfold exponentialSum
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  unfold phase
  let m := evalForm F x
  change Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((α + 1) * (m : ℝ) : ℝ) : ℂ)) =
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((α * (m : ℝ) : ℝ) : ℂ))
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (((α : ℂ) + 1) * (m : ℂ)) =
    2 * (Real.pi : ℂ) * Complex.I * ((α : ℂ) * (m : ℂ)) +
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Reduced pairs of denominator and numerator with centers in the interior. -/
def interiorMajorCenters (P : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 ⌊P ^ (1 / 2 : ℝ)⌋₊).product
    (Finset.Icc 1 ⌊P ^ (1 / 2 : ℝ)⌋₊)).filter
      (fun t => t.2 < t.1 ∧ t.2.Coprime t.1)

/-- The finite index set records the denominator cutoff and the reduced interior numerator. -/
theorem mem_interiorMajorCenters {P : ℝ} (hP : 0 ≤ P) {q a : ℕ} :
    (q, a) ∈ interiorMajorCenters P ↔
      2 ≤ q ∧ (q : ℝ) ≤ P ^ (1 / 2 : ℝ) ∧ 1 ≤ a ∧ a < q ∧ a.Coprime q := by
  constructor
  · intro h
    obtain ⟨hprod, haq, hcop⟩ := Finset.mem_filter.mp h
    obtain ⟨hq, ha⟩ := Finset.mem_product.mp hprod
    exact ⟨(Finset.mem_Icc.mp hq).1,
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le (Real.rpow_nonneg hP _)),
      (Finset.mem_Icc.mp ha).1, haq, hcop⟩
  · rintro ⟨hq, hqP, ha, haq, hcop⟩
    have hqle := Nat.le_floor hqP
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq, hqle⟩, Finset.mem_Icc.mpr ⟨ha, haq.le.trans hqle⟩⟩,
      haq, hcop⟩

private theorem liftedMajorArc_measurable (d : ℕ) (P : ℝ) (q : ℕ) (a : ℤ) :
    MeasurableSet (liftedMajorArc d P q a) :=
  (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet

/-- A lifted major interval has endpoints one radius from its center. -/
theorem liftedMajorArc_eq_Icc (d : ℕ) (P : ℝ) (q : ℕ) (a : ℤ) :
    liftedMajorArc d P q a = Icc ((a : ℝ) / q - majorArcWidth d P / q)
      ((a : ℝ) / q + majorArcWidth d P / q) := by
  ext α
  rw [liftedMajorArc, Set.mem_ofPred_eq, mem_Icc, abs_le]
  constructor
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem nat_reduced_fraction_inj {q s a b : ℕ} (hq : 0 < q) (hs : 0 < s)
    (haq : a.Coprime q) (hbs : b.Coprime s)
    (h : (a : ℝ) / (q : ℝ) = (b : ℝ) / (s : ℝ)) : (q, a) = (s, b) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hm : a * s = b * q := by exact_mod_cast (div_eq_div_iff hqR.ne' hsR.ne').mp h
  have hqs : q ∣ s := haq.symm.dvd_mul_left.mp (by rw [hm]; exact dvd_mul_left q b)
  have hsq : s ∣ q := hbs.symm.dvd_mul_left.mp (by rw [← hm]; exact dvd_mul_left s a)
  obtain rfl := Nat.dvd_antisymm hqs hsq
  exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_right hq hm)

/-- In the fundamental interval, all non-unit conductors have reduced centers
strictly inside the interval, so only the unit conductor requires a wrap. -/
theorem majorArcs_inter_Ioc {d : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 4 ≤ P) :
    majorArcs d P ∩ Ioc 0 1 =
      ((⋃ a : ℤ, liftedMajorArc d P 1 a) ∩ Ioc 0 1) ∪
        ⋃ j ∈ interiorMajorCenters P, liftedMajorArc d P j.1 (j.2 : ℤ) := by
  have hP₀ : 0 ≤ P := by linarith
  have hP₁ : 1 ≤ P := by linarith
  have hW := (majorArcWidth_pos_lt_half hd hP).2
  ext α
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hα, hαI⟩
    obtain ⟨q, a, hq, hqP, hcop, hnear⟩ := hα
    by_cases hq₁ : q = 1
    · subst q
      exact Or.inl ⟨⟨a, hnear⟩, hαI⟩
    · have hq₂ : 2 ≤ q := by omega
      have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
      have haNear : |(q : ℝ) * α - (a : ℝ)| ≤ majorArcWidth d P := by
        have heq : (q : ℝ) * (α - (a : ℝ) / q) = (q : ℝ) * α - a := by field_simp
        rw [← heq, abs_mul, abs_of_pos hqR, mul_comm (q : ℝ)]
        exact (le_div_iff₀ hqR).mp hnear
      have hlo := mul_pos hqR hαI.1
      have hhi : (q : ℝ) * α ≤ q := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hαI.2 hqR.le
      rw [abs_le] at haNear
      have ha₀ : 0 ≤ a := by
        by_contra! h
        have h' : (a : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast (show a ≤ -1 by omega)
        linarith [haNear.2]
      have haU : a ≤ (q : ℤ) := by
        by_contra! h
        have h' : (q : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast (show (q : ℤ) + 1 ≤ a by omega)
        linarith [haNear.1]
      obtain ⟨a, rfl⟩ : ∃ a' : ℕ, a = (a' : ℤ) :=
        ⟨a.toNat, (Int.toNat_of_nonneg ha₀).symm⟩
      simp only [Int.natAbs_natCast] at hcop
      have ha1 : 1 ≤ a := by
        by_contra! H
        have haz : a = 0 := by omega
        simp [haz] at hcop
        exact hq₁ hcop
      have haq : a < q := by
        have h' : a ≤ q := by exact_mod_cast haU
        by_contra! h
        have haeq : a = q := by omega
        simp [haeq] at hcop
        exact hq₁ hcop
      exact Or.inr ⟨(q, a), (mem_interiorMajorCenters hP₀).mpr ⟨hq₂, hqP, ha1, haq, hcop⟩,
        hnear⟩
  · rintro (⟨⟨a, ha⟩, hI⟩ | ⟨⟨q, a⟩, jmem, hj⟩)
    · exact ⟨⟨1, a, zero_lt_one, by exact_mod_cast Real.one_le_rpow hP₁ (by norm_num : 0 ≤ (1/2 : ℝ)),
        Nat.coprime_one_right _, ha⟩, hI⟩
    · obtain ⟨hq, hcut, ha, haq, hcop⟩ := (mem_interiorMajorCenters hP₀).mp jmem
      have hq₀ : 0 < q := by omega
      have ha' : (0 : ℤ) < (a : ℤ) := by exact_mod_cast (show 0 < a by omega)
      have haq' : (a : ℤ) < (q : ℤ) := by exact_mod_cast haq
      exact ⟨⟨q, a, hq₀, hcut, by simpa using hcop, hj⟩,
        Ioo_subset_Ioc_self (liftedMajorArc_subset_Ioo hd hP hq₀ ha' haq' hj)⟩

/-- The major-arc integral splits into the centered unit-conductor interval and
the finitely many interior reduced intervals. -/
theorem integral_majorArcs_eq_sum {d : ℕ} (hd : 2 ≤ d) {P : ℝ} (hP : 4 ≤ P)
    {f : ℝ → ℂ} (hf : Function.Periodic f 1) (hfc : Continuous f) :
    (∫ α in majorArcs d P, f α ∂circleMeasure) =
      (∫ α in Icc (-majorArcWidth d P) (majorArcWidth d P), f α) +
        ∑ j ∈ interiorMajorCenters P, ∫ α in liftedMajorArc d P j.1 (j.2 : ℤ), f α := by
  let unit := ⋃ a : ℤ, liftedMajorArc d P 1 a
  let A (j : ℕ × ℕ) := liftedMajorArc d P j.1 (j.2 : ℤ)
  let U := interiorMajorCenters P
  have hP₀ : 0 ≤ P := by linarith
  have hP₁ : 1 ≤ P := by linarith
  have hmeasUnit : MeasurableSet unit :=
    MeasurableSet.iUnion fun i => liftedMajorArc_measurable d P 1 i
  have hmeas (j : ℕ × ℕ) : MeasurableSet (A j) := liftedMajorArc_measurable _ _ _ _
  have hint (j : ℕ × ℕ) : IntegrableOn f (A j) := by
    change IntegrableOn f (liftedMajorArc d P j.1 (j.2 : ℤ))
    rw [liftedMajorArc_eq_Icc]
    exact hfc.integrableOn_Icc
  have hpair : Set.Pairwise (↑U) (fun j l => Disjoint (A j) (A l)) := by
    intro j hj l hl hne
    obtain ⟨q, a⟩ := j
    obtain ⟨s, b⟩ := l
    obtain ⟨hq, hqP, _, _, hcop⟩ := (mem_interiorMajorCenters hP₀).mp hj
    obtain ⟨hs, hsP, _, _, hcop'⟩ := (mem_interiorMajorCenters hP₀).mp hl
    have hq' : 0 < q := by omega
    have hs' : 0 < s := by omega
    apply liftedMajorArcs_disjoint hd hP hq' hs' hqP hsP
    intro h
    push_cast at h
    exact hne (nat_reduced_fraction_inj hq' hs' hcop hcop' h)
  have hunitSep : Disjoint (unit ∩ Ioc 0 1) (⋃ j ∈ U, A j) := by
    apply Set.disjoint_left.mpr
    intro α hα hj
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hα.1
    obtain ⟨⟨q, b⟩, hh⟩ := Set.mem_iUnion.mp hj
    obtain ⟨ht, hnear⟩ := Set.mem_iUnion.mp hh
    obtain ⟨hq, hqP, hb, hbq, _⟩ := (mem_interiorMajorCenters hP₀).mp ht
    have hq₀ : 0 < q := by omega
    have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq₀
    have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hbqR : (b : ℝ) < (q : ℝ) := by exact_mod_cast hbq
    have hx₀ : 0 < (b : ℝ) / (q : ℝ) := div_pos hbR hqR
    have hx₁ : (b : ℝ) / (q : ℝ) < 1 := (div_lt_one hqR).2 hbqR
    have hneq : (a : ℝ) / (1 : ℕ) ≠ ((b : ℤ) : ℝ) / (q : ℝ) := by
      push_cast
      rw [div_one]
      intro h
      have h₀ : (0 : ℤ) < a := by exact_mod_cast (h ▸ hx₀)
      have h₁ : a < (1 : ℤ) := by exact_mod_cast (h ▸ hx₁)
      omega
    have hs := liftedMajorArcs_disjoint hd hP (q := 1) (s := q)
      zero_lt_one hq₀ (by exact_mod_cast Real.one_le_rpow hP₁ (by norm_num : 0 ≤ (1/2 : ℝ))) hqP hneq
    exact Set.disjoint_left.mp hs ha hnear
  have hintUnit : IntegrableOn f (unit ∩ Ioc 0 1) :=
    hfc.integrableOn_Icc.mono_set (inter_subset_right.trans Ioc_subset_Icc_self)
  have hwrap : (∫ α in unit ∩ Ioc 0 1, f α) =
      ∫ α in Icc (-majorArcWidth d P) (majorArcWidth d P), f α := by
    have hw := integral_liftedUnitArcs hd hP hf hfc
    unfold circleMeasure at hw
    rwa [Measure.restrict_restrict hmeasUnit] at hw
  unfold circleMeasure
  rw [Measure.restrict_restrict (measurableSet_majorArcs d P), majorArcs_inter_Ioc hd hP]
  rw [setIntegral_union hunitSep (U.measurableSet_biUnion (fun j _ => hmeas j)) hintUnit
    (integrableOn_finset_iUnion.2 fun j _ => hint j)]
  rw [hwrap, integral_biUnion_finset U (fun j _ => hmeas j) hpair (fun j _ => hint j)]

/-- The change to the variable \(\gamma=P^d(\alpha-a/q)\) on a lifted major arc
has the exact Jacobian \(P^{-d}\) and cutoff \(P^{7/8}/q\). -/
theorem integral_liftedMajorArc_substitution (d : ℕ) {P : ℝ} (hP : 0 < P)
    {q : ℕ} (hq : 0 < q) (a : ℤ) (f : ℝ → ℂ) :
    (∫ α in liftedMajorArc d P q a, f (P ^ d * (α - (a : ℝ) / q))) =
      (P ^ (-(d : ℝ)) : ℝ) •
        ∫ γ in Icc (-(P ^ (7 / 8 : ℝ) / (q : ℝ))) (P ^ (7 / 8 : ℝ) / (q : ℝ)), f γ := by
  let c : ℝ := (a : ℝ) / q
  let W := majorArcWidth d P / (q : ℝ)
  let v : ℝ := P ^ (7 / 8 : ℝ) / (q : ℝ)
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hW : 0 < W := div_pos (Real.rpow_pos_of_pos hP _) hqR
  have hv : 0 < v := div_pos (Real.rpow_pos_of_pos hP _) hqR
  have hscale : P^d * W = v := by
    dsimp only [W, v, majorArcWidth]
    rw [← mul_div_assoc, ← Real.rpow_natCast, ← Real.rpow_add hP]
    congr 2
    ring
  rw [liftedMajorArc_eq_Icc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  change (∫ α in Ioc (c - W) (c + W), f (P ^ d * (α - c))) =
    (P ^ (-(d : ℝ)) : ℝ) • ∫ γ in Ioc (-v) v, f γ
  rw [← intervalIntegral.integral_of_le (by linarith : c - W ≤ c + W),
    ← intervalIntegral.integral_of_le (by linarith : -v ≤ v)]
  rw [intervalIntegral.integral_comp_sub_right (fun x => f (P ^ d * x)) c,
    show c - W - c = -W by ring, show c + W - c = W by ring,
    intervalIntegral.integral_comp_mul_left f (pow_ne_zero _ hP.ne'),
    mul_neg, hscale, Real.rpow_neg hP.le, Real.rpow_natCast]

end

end Birch
