import Birch.MajorArcLatticePoisson
import Birch.V2CoverLocal

/-! # Disjoint intervals around rational frequencies beyond the major arcs -/

open Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace Birch

noncomputable section

/-- Reduced fractions strictly between zero and one in a dyadic denominator interval. -/
def rationalShellCenters (X : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 2 ⌊2 * X⌋₊).product (Finset.Icc 1 ⌊2 * X⌋₊)).filter
    (fun j => X < (j.1 : ℝ) ∧ j.2 < j.1 ∧ j.2.Coprime j.1)

theorem mem_rationalShellCenters {X : ℝ} (hX : 0 ≤ X) {q a : ℕ} :
    (q, a) ∈ rationalShellCenters X ↔
      2 ≤ q ∧ X < (q : ℝ) ∧ (q : ℝ) ≤ 2 * X ∧ 1 ≤ a ∧ a < q ∧ a.Coprime q := by
  constructor
  · intro hj
    obtain ⟨hprod, hXq, haq, hcop⟩ := Finset.mem_filter.mp hj
    obtain ⟨hq, ha⟩ := Finset.mem_product.mp hprod
    obtain ⟨hq₂, hq⟩ := Finset.mem_Icc.mp hq
    exact ⟨hq₂, hXq, (Nat.cast_le.mpr hq).trans (Nat.floor_le (by positivity)),
      (Finset.mem_Icc.mp ha).1, haq, hcop⟩
  · rintro ⟨hq₂, hXq, hq, ha, haq, hcop⟩
    have hq' := Nat.le_floor hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hq₂, hq'⟩, Finset.mem_Icc.mpr ⟨ha, haq.le.trans hq'⟩⟩,
      hXq, haq, hcop⟩

/-- The sum over rational centers can be collected by denominator. -/
theorem sum_rationalShellCenters_by_denominator {A : Type*} [AddCommMonoid A]
    (Q : ℕ) (hQ : 1 ≤ Q) (f : ℕ → ℕ → A) :
    (∑ j ∈ rationalShellCenters (Q : ℝ), f j.1 j.2) =
      ∑ q ∈ Finset.Ioc Q (2*Q), ∑ a ∈ (Finset.Ico 1 q).filter (fun a => a.Coprime q), f q a := by
  classical
  rw [Finset.sum_sigma']
  have hs (q a : ℕ) : (q,a) ∈ rationalShellCenters (Q : ℝ) ↔
      (⟨q,a⟩ : Σ _ : ℕ, ℕ) ∈ (Finset.Ioc Q (2*Q)).sigma
        (fun s => (Finset.Ico 1 s).filter (fun b => b.Coprime s)) := by
    rw [mem_rationalShellCenters (Nat.cast_nonneg _)]
    simp only [Finset.mem_sigma, Finset.mem_Ioc, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨_, hq, hs, ha, hat, hc⟩
      exact ⟨⟨by exact_mod_cast hq, by exact_mod_cast hs⟩, ⟨ha, hat⟩, hc⟩
    · rintro ⟨⟨hq, hs⟩, ⟨ha, hat⟩, hc⟩
      exact ⟨Nat.succ_le_of_lt (hQ.trans_lt hq), by exact_mod_cast hq, by exact_mod_cast hs, ha, hat, hc⟩
  apply Finset.sum_bij (fun j _ => (⟨j.1,j.2⟩ : Σ _ : ℕ, ℕ))
  · intro j hj
    exact (hs j.1 j.2).mp hj
  · intro j _ j' _ he
    exact Prod.ext (congrArg Sigma.fst he) (congrArg (fun s : Σ _ : ℕ, ℕ => s.2) he)
  · rintro ⟨q,a⟩ hj
    exact ⟨(q,a), (hs q a).mpr hj, rfl⟩
  · intros
    rfl

/-- The closed interval of radius `R` around a rational frequency. -/
def rationalShellInterval (R : ℝ) (j : ℕ × ℕ) : Set ℝ :=
  Icc ((j.2 : ℝ) / j.1 - R) ((j.2 : ℝ) / j.1 + R)

theorem mem_rationalShellInterval {R α : ℝ} {q a : ℕ} :
    α ∈ rationalShellInterval R (q, a) ↔ |α - (a : ℝ) / q| ≤ R := by
  rw [rationalShellInterval, mem_Icc, abs_le]
  exact ⟨fun h => ⟨by linarith [h.1], by linarith [h.2]⟩,
    fun h => ⟨by linarith [h.1], by linarith [h.2]⟩⟩

/-- Distinct fractions have distance at least the reciprocal of the product
of their positive denominators. -/
theorem rational_centers_separated {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    (a b : ℤ) (hne : (a : ℝ) / q ≠ (b : ℝ) / s) :
    1 ≤ |(a : ℝ) / q - (b : ℝ) / s| * ((q : ℝ) * s) := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  let m : ℤ := a * (s : ℤ) - b * (q : ℤ)
  have hm : (m : ℝ) = ((a : ℝ) / q - (b : ℝ) / s) * ((q : ℝ) * s) := by
    dsimp [m]
    push_cast
    field_simp
  have hm₀ : m ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hm
    exact (mul_ne_zero (sub_ne_zero.mpr hne) (mul_pos hqR hsR).ne') hm.symm
  have hm₁ : (1 : ℤ) ≤ |m| := by
    have hh := abs_pos.mpr hm₀
    omega
  have hm₂ : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast hm₁
  rwa [hm, abs_mul, abs_of_pos (mul_pos hqR hsR)] at hm₂

/-- The denominator of a reduced fraction divides every other denominator
representing the same rational number. -/
theorem denominator_dvd_of_fraction_eq {q s : ℕ} (hq : 0 < q) (hs : 0 < s)
    {a b : ℤ} (hcop : a.natAbs.Coprime q) (h : (a : ℝ) / q = (b : ℝ) / s) : q ∣ s := by
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hsR : (s : ℝ) ≠ 0 := by positivity
  have hab : a * (s : ℤ) = b * (q : ℤ) := by
    exact_mod_cast (div_eq_div_iff hqR hsR).mp h
  have hN : a.natAbs * s = b.natAbs * q := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hab
  exact hcop.symm.dvd_mul_left.mp (by rw [hN]; exact dvd_mul_left q b.natAbs)

theorem rationalShellIntervals_pairwiseDisjoint {X R : ℝ} (hX : 0 ≤ X) (hR : 0 ≤ R)
    (hsmall : (2 * R) * (2 * X)^2 < 1) :
    (↑(rationalShellCenters X) : Set (ℕ × ℕ)).PairwiseDisjoint (rationalShellInterval R) := by
  rintro ⟨q,a⟩ hqmem ⟨s,b⟩ hsmem hne
  obtain ⟨hq, _, hqX, _, _, hcop⟩ := (mem_rationalShellCenters hX).mp hqmem
  obtain ⟨hs, _, hsX, _, _, hcop'⟩ := (mem_rationalShellCenters hX).mp hsmem
  have hq₀ : 0 < q := by omega
  have hs₀ : 0 < s := by omega
  have hdistinct : (a : ℝ) / q ≠ (b : ℝ) / s := by
    intro h
    have hcast : ((a : ℤ) : ℝ) / q = ((b : ℤ) : ℝ) / s := by
      simpa only [Int.cast_natCast] using h
    have hqs := denominator_dvd_of_fraction_eq hq₀ hs₀ (a := (a : ℤ)) (b := (b : ℤ))
      (by simpa using hcop) hcast
    have hsq := denominator_dvd_of_fraction_eq hs₀ hq₀ (a := (b : ℤ)) (b := (a : ℤ))
      (by simpa using hcop') hcast.symm
    obtain rfl := Nat.dvd_antisymm hqs hsq
    have hab : (a : ℝ) = b := (div_left_inj' (by positivity : (q : ℝ) ≠ 0)).mp h
    exact hne (Prod.ext rfl (by exact_mod_cast hab))
  apply Set.disjoint_left.mpr
  intro α ha hb
  have hsep := rational_centers_separated hq₀ hs₀ (a : ℤ) (b : ℤ)
    (by simpa only [Int.cast_natCast] using hdistinct)
  push_cast at hsep
  have htri : |(a : ℝ) / q - (b : ℝ) / s| ≤ 2 * R := by
    have ht := abs_sub_le ((a : ℝ) / q) α ((b : ℝ) / s)
    rw [abs_sub_comm ((a : ℝ) / q) α] at ht
    exact ht.trans (by simpa only [two_mul] using
      (add_le_add (mem_rationalShellInterval.mp ha) (mem_rationalShellInterval.mp hb)))
  have hprod : (q : ℝ) * s ≤ (2 * X)^2 := by
    rw [pow_two]
    exact mul_le_mul hqX hsX (by positivity) (by positivity)
  exact (not_lt_of_ge (hsep.trans (mul_le_mul htri hprod (by positivity) (by positivity)))) hsmall

theorem rationalShellInterval_subset_Ioo {X R : ℝ} (hX : 0 ≤ X)
    (hsmall : R * (2 * X) < 1) {j : ℕ × ℕ} (hj : j ∈ rationalShellCenters X) :
    rationalShellInterval R j ⊆ Ioo 0 1 := by
  obtain ⟨q,a⟩ := j
  obtain ⟨hq, _, hqX, ha, haq, _⟩ := (mem_rationalShellCenters hX).mp hj
  have hq₀ : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have ha₀ : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha₁ : (a : ℝ) + 1 ≤ q := by exact_mod_cast (show a + 1 ≤ q by omega)
  intro α hα
  have h := mem_rationalShellInterval.mp hα
  have hrad : R * (q : ℝ) < 1 := by
    by_cases hR : 0 ≤ R
    · exact (mul_le_mul_of_nonneg_left hqX hR).trans_lt hsmall
    · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hR) hq₀.le).trans_lt zero_lt_one
  have hmul (u : ℝ) : (u - (a : ℝ) / q) * (q : ℝ) = u * q - a := by
    field_simp
  have hlo := mul_le_mul_of_nonneg_right (abs_le.mp h).1 hq₀.le
  have hhi := mul_le_mul_of_nonneg_right (abs_le.mp h).2 hq₀.le
  rw [hmul, neg_mul] at hlo
  rw [hmul] at hhi
  exact ⟨(mul_pos_iff_of_pos_right hq₀).mp (by linarith),
    (mul_lt_mul_iff_of_pos_right hq₀).mp (by simpa using (show α * q < (q : ℝ) by linarith))⟩

/-- A shell interval excludes every smaller denominator whose radius, multiplied by
its denominator, is at most `W`. This applies to both fixed and varying radii. -/
theorem rationalShellInterval_avoids {X R Q W : ℝ} (hX : 0 ≤ X) (hR : 0 ≤ R)
    (hQ : Q ≤ X) (hsmall : (R * Q + W) * (2 * X) < 1)
    {q a : ℕ} (hj : (q,a) ∈ rationalShellCenters X) {α : ℝ}
    (hα : α ∈ rationalShellInterval R (q,a)) {s : ℕ} (hs : 0 < s)
    (hsQ : (s : ℝ) ≤ Q) (b : ℤ) :
    W < |α - (b : ℝ) / s| * (s : ℝ) := by
  obtain ⟨hq, hXq, hqX, _, _, hcop⟩ := (mem_rationalShellCenters hX).mp hj
  have hq₀ : 0 < q := by omega
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq₀
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hsq : s < q := by exact_mod_cast ((hsQ.trans hQ).trans_lt hXq)
  have hneq : (((a : ℤ) : ℝ) / q) ≠ (b : ℝ) / s := by
    intro he
    exact (not_le_of_gt hsq) (Nat.le_of_dvd hs
      (denominator_dvd_of_fraction_eq hq₀ hs (by simpa using hcop) he))
  have hsep := rational_centers_separated hq₀ hs (a : ℤ) b hneq
  push_cast at hsep
  by_contra! hnear
  have hW : 0 ≤ W := (mul_nonneg (abs_nonneg _) hsR.le).trans hnear
  have hRQW : 0 ≤ R * Q + W := add_nonneg (mul_nonneg hR (hsR.le.trans hsQ)) hW
  have ht := abs_sub_le ((a : ℝ) / q) α ((b : ℝ) / s)
  rw [abs_sub_comm ((a : ℝ) / q) α] at ht
  have h₁ : |(a : ℝ) / q - (b : ℝ) / s| * (s : ℝ) ≤ R * Q + W := by
    refine (mul_le_mul_of_nonneg_right ht hsR.le).trans ?_
    rw [add_mul]
    exact add_le_add (mul_le_mul (mem_rationalShellInterval.mp hα) hsQ hsR.le hR) hnear
  rw [mul_comm (q : ℝ) (s : ℝ), ← mul_assoc] at hsep
  exact (not_lt_of_ge (hsep.trans (mul_le_mul h₁ hqX hqR.le hRQW))) hsmall

/-- On a whole shell interval the lower estimate for a coefficient can be
integrated and summed. The error is charged once per rational center. -/
theorem rationalShell_sum_le_minorIntegral {X R : ℝ} (hX : 0 ≤ X) (hR : 0 ≤ R)
    (hpair : (2 * R) * (2 * X)^2 < 1) (hinside : R * (2 * X) < 1)
    (minor : Set ℝ)
    (hsub : ∀ j ∈ rationalShellCenters X, rationalShellInterval R j ⊆ minor)
    (f : ℝ → ℝ) (hf : Continuous f) (hf₀ : ∀ α, 0 ≤ f α)
    (coeff : ℕ × ℕ → ℝ) (c error : ℝ)
    (hpoint : ∀ j ∈ rationalShellCenters X, ∀ α ∈ rationalShellInterval R j,
      c * coeff j ≤ f α + error) :
    (2 * R) * (c * ∑ j ∈ rationalShellCenters X, coeff j) ≤
      (∫ α in minor, f α ∂circleMeasure) +
        (2 * R) * ((rationalShellCenters X).card : ℝ) * error := by
  classical
  let S := rationalShellCenters X
  let A := rationalShellInterval R
  let U := ⋃ j ∈ S, A j
  have hA (j : ℕ × ℕ) : MeasurableSet (A j) := measurableSet_Icc
  have hUm : U ⊆ minor := by
    intro α hα
    simp only [U, Set.mem_iUnion] at hα
    obtain ⟨j, hj, hα⟩ := hα
    exact hsub j hj hα
  have hAI (j : ℕ × ℕ) (hj : j ∈ S) : A j ⊆ Ioc 0 1 :=
    (rationalShellInterval_subset_Ioo hX hinside hj).trans Ioo_subset_Ioc_self
  have hint : Integrable f circleMeasure := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hconst (j : ℕ × ℕ) (hj : j ∈ S) (v : ℝ) :
      (∫ _α in A j, v ∂circleMeasure) = (2 * R) * v := by
    have hinter : A j ∩ Ioc 0 1 = A j := inter_eq_left.mpr (hAI j hj)
    rw [circleMeasure, Measure.restrict_restrict (hA j), hinter, setIntegral_const]
    change (volume (Icc _ _)).toReal • v = _
    rw [Real.volume_Icc, show _ + R - (_ - R) = 2 * R by ring,
      ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  have hlocal (j : ℕ × ℕ) (hj : j ∈ S) :
      (2 * R) * (c * coeff j) ≤ (∫ α in A j, f α ∂circleMeasure) + (2 * R) * error := by
    rw [← hconst j hj (c * coeff j), ← hconst j hj error,
      ← integral_add hint.integrableOn (integrable_const error)]
    exact setIntegral_mono_on (integrable_const _) (hint.integrableOn.add (integrable_const _))
      (hA j) (hpoint j hj)
  calc
    _ = ∑ j ∈ S, (2 * R) * (c * coeff j) := by simp only [Finset.mul_sum, S]
    _ ≤ ∑ j ∈ S, ((∫ α in A j, f α ∂circleMeasure) + (2 * R) * error) :=
      Finset.sum_le_sum hlocal
    _ = (∫ α in U, f α ∂circleMeasure) + (2 * R) * (S.card : ℝ) * error := by
      rw [Finset.sum_add_distrib, integral_biUnion_finset S (fun j _ => hA j)
        (rationalShellIntervals_pairwiseDisjoint hX hR hpair) (fun _ _ => hint.integrableOn),
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := add_le_add
      (setIntegral_mono_set hint.integrableOn (ae_of_all _ hf₀) (Eventually.of_forall hUm)) le_rfl

/-- The number of reduced centers in the shell is at most the square of the
number of possible integers in either position. -/
theorem rationalShellCenters_card_le (X : ℝ) (hX : 0 ≤ X) :
    ((rationalShellCenters X).card : ℝ) ≤ (2 * X + 1)^2 := by
  let N := ⌊2 * X⌋₊ + 1
  have hsub : rationalShellCenters X ⊆ (Finset.range N).product (Finset.range N) := by
    rintro ⟨q,a⟩ hj
    obtain ⟨_, _, hq, _, haq, _⟩ := (mem_rationalShellCenters hX).mp hj
    have hq' := Nat.le_floor hq
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [N]; omega),
      Finset.mem_range.mpr (by dsimp [N]; omega)⟩
  have hcard := Finset.card_le_card hsub
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range] at hcard
  rw [pow_two]
  have hN : (N : ℝ) ≤ 2 * X + 1 := by
    dsimp [N]
    push_cast
    linarith [Nat.floor_le (show 0 ≤ 2 * X by positivity)]
  exact (show ((rationalShellCenters X).card : ℝ) ≤ (N : ℝ) * N by exact_mod_cast hcard).trans
    (mul_le_mul hN hN (by positivity) (by positivity))

/-- Denominators of order `P^(2/3)` are separated from the earlier
circle-method major arcs and from one another on the `P^(-d)` scale. -/
theorem oldMajorArcShell_geometry {d : ℕ} (hd : 2 ≤ d) {P c : ℝ} (hP : 4096 ≤ P)
    (hc : 0 ≤ c) (hc₁ : c ≤ 1) :
    let X := P^(2/3 : ℝ)
    let R := c * P^(-(d : ℝ))
    (2 * R) * (2 * X)^2 < 1 ∧ R * (2 * X) < 1 ∧
      ∀ j ∈ rationalShellCenters X, rationalShellInterval R j ⊆ (majorArcs d P)ᶜ := by
  let X := P^(2/3 : ℝ)
  let Q := P^(1/2 : ℝ)
  let R := c * P^(-(d : ℝ))
  let W := majorArcWidth d P
  have hP₁ : 1 ≤ P := by linarith
  have hP₀ : 0 < P := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hX : 0 ≤ X := Real.rpow_nonneg hP₀.le _
  have hQ : Q ≤ X := Real.rpow_le_rpow_of_exponent_le hP₁ (by norm_num)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hslow {a : ℝ} (ha : a ≤ -(1/3)) : P^a ≤ 1 / 16 := by
    calc
      _ ≤ P^(-(1/3) : ℝ) := Real.rpow_le_rpow_of_exponent_le hP₁ ha
      _ ≤ (4096 : ℝ)^(-(1/3) : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hP (by norm_num)
      _ = _ := by
        rw [show (4096 : ℝ) = (16 : ℝ) ^ (3 : ℕ) by norm_num,
          ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        norm_num [Real.rpow_neg_one]
  have hpair : (2 * R) * (2 * X)^2 < 1 := by
    have heq : (2 * R) * (2 * X)^2 = (8 * c) * P^(-(d : ℝ) + 4 / 3) := by
      dsimp [R, X]
      rw [show (2 * P^(2/3 : ℝ))^2 = 4 * P^(4/3 : ℝ) by
        rw [mul_pow, ← Real.rpow_mul_natCast hP₀.le]; norm_num]
      calc
        _ = (8 * c) * (P^(-(d : ℝ)) * P^(4/3 : ℝ)) := by ring
        _ = _ := by rw [← Real.rpow_add hP₀]
    rw [heq]
    have hb := mul_le_mul (show 8 * c ≤ (8 : ℝ) by linarith)
      (hslow (a := -(d : ℝ) + 4 / 3) (by linarith)) (by positivity : 0 ≤ P^(-(d : ℝ) + 4 / 3))
      (by norm_num : 0 ≤ (8 : ℝ))
    linarith
  have hinside : R * (2 * X) < 1 := by
    have heq : R * (2 * X) = (2 * c) * P^(-(d : ℝ) + 2 / 3) := by
      dsimp [R, X]
      rw [Real.rpow_add hP₀]
      ring
    rw [heq]
    have hb := mul_le_mul (show 2 * c ≤ (2 : ℝ) by linarith)
      (hslow (a := -(d : ℝ) + 2 / 3) (by linarith)) (by positivity : 0 ≤ P^(-(d : ℝ) + 2 / 3))
      (by norm_num : 0 ≤ (2 : ℝ))
    linarith
  have hav : (R * Q + W) * (2 * X) < 1 := by
    have hRQ : R * Q ≤ W := calc
      _ = c * P^(-(d : ℝ) + 1 / 2) := by dsimp [R, Q]; rw [Real.rpow_add hP₀, mul_assoc]
      _ ≤ 1 * P^(-(d : ℝ) + 1 / 2) := mul_le_mul_of_nonneg_right hc₁ (by positivity)
      _ ≤ W := by
        rw [one_mul, show W = P^(-(d : ℝ) + 7 / 8) from rfl]
        exact Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
    calc
      _ ≤ (2 * W) * (2 * X) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 4 * P^(-(d : ℝ) + 37 / 24) := by
        dsimp [W, X, majorArcWidth]
        rw [show -(d : ℝ) + 37 / 24 = -(d : ℝ) + 7 / 8 + 2 / 3 by ring]
        simp only [Real.rpow_add hP₀]
        ring
      _ < 1 := by linarith [hslow (a := -(d : ℝ) + 37 / 24) (by linarith)]
  refine ⟨hpair, hinside, ?_⟩
  rintro ⟨q,a⟩ hj α hα ⟨s,b,hs,hsQ,_,hnear⟩
  have hs₀ : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  exact (not_lt_of_ge ((le_div_iff₀ hs₀).mp hnear))
    (rationalShellInterval_avoids hX hR hQ hav hj hα hs hsQ b)

/-- The fixed-width major arcs of v2, represented by all real lifts. -/
def v2MajorArcs (d : ℕ) (Δ P : ℝ) : Set ℝ :=
  {α | ∃ (q : ℕ) (a : ℤ), 0 < q ∧ (q : ℝ) ≤ P^Δ ∧
    a.natAbs.Coprime q ∧ |α - (a : ℝ) / q| ≤ P^(-(d : ℝ) + Δ)}

theorem measurableSet_v2MajorArcs (d : ℕ) (Δ P : ℝ) : MeasurableSet (v2MajorArcs d Δ P) := by
  classical
  let A (q : ℕ) (a : ℤ) : Set ℝ := if 0 < q ∧ (q : ℝ) ≤ P^Δ ∧ a.natAbs.Coprime q then
    {α | |α - (a : ℝ) / q| ≤ P^(-(d : ℝ) + Δ)} else ∅
  have heq : v2MajorArcs d Δ P = ⋃ (q : ℕ) (a : ℤ), A q a := by
    ext α
    simp only [v2MajorArcs, mem_setOf_eq, mem_iUnion]
    refine exists_congr fun q => exists_congr fun a => ?_
    by_cases h : 0 < q ∧ (q : ℝ) ≤ P^Δ ∧ a.natAbs.Coprime q
    · simp only [A, if_pos h, mem_setOf_eq]
      exact ⟨fun hh => hh.2.2.2, fun hh => ⟨h.1, h.2.1, h.2.2, hh⟩⟩
    · simp only [A, if_neg h, notMem_empty, iff_false]
      exact fun hh => h ⟨hh.1, hh.2.1, hh.2.2.1⟩
  rw [heq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  dsimp only [A]
  split_ifs
  · exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
  · exact MeasurableSet.empty

/-- The smaller fixed-width cutoff admits shells of order `P^(2Δ)`.
These are short enough to handle both variables of a polynomial cover. -/
theorem v2MajorArcShell_geometry {d : ℕ} (hd : 2 ≤ d) {P c Δ : ℝ} (hP : 16 ≤ P)
    (hc : 0 ≤ c) (hc₁ : c ≤ 1) (hΔ : 0 ≤ Δ) (hΔ₁ : Δ ≤ 1 / 4) :
    let X := P^(2 * Δ)
    let R := c * P^(-(d : ℝ))
    (2 * R) * (2 * X)^2 < 1 ∧ R * (2 * X) < 1 ∧
      ∀ j ∈ rationalShellCenters X, rationalShellInterval R j ⊆ (v2MajorArcs d Δ P)ᶜ := by
  let X := P^(2 * Δ)
  let Q := P^Δ
  let R := c * P^(-(d : ℝ))
  let W := P^(-(d : ℝ) + 2 * Δ)
  have hP₁ : 1 ≤ P := by linarith
  have hP₀ : 0 < P := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hX : 0 ≤ X := Real.rpow_nonneg hP₀.le _
  have hQ : Q ≤ X := Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsmall : 8 * P^(-1 : ℝ) < 1 := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, div_lt_one hP₀]
    linarith
  have hpair' : (2 * R) * (2 * X)^2 < 1 := by
    have heq : (2 * R) * (2 * X)^2 = (8 * c) * P^(-(d : ℝ) + 4 * Δ) := by
      dsimp [R, X]
      rw [mul_pow, ← Real.rpow_mul_natCast hP₀.le,
        show 2 * Δ * (↑(2 : ℕ) : ℝ) = 4 * Δ by push_cast; ring]
      rw [Real.rpow_add hP₀]
      ring
    rw [heq]
    exact (mul_le_mul (by linarith : 8*c ≤ 8)
      (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith))
      (by positivity) (by norm_num)).trans_lt hsmall
  have hinside' : R * (2 * X) < 1 := by
    have heq : R * (2 * X) = (2 * c) * P^(-(d : ℝ) + 2 * Δ) := by
      dsimp [R, X]
      rw [Real.rpow_add hP₀]
      ring
    rw [heq]
    have hbound : (2 * c) * P^(-(d : ℝ) + 2 * Δ) ≤ 8 * P^(-1 : ℝ) := by
      exact mul_le_mul (by linarith) (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith))
        (by positivity) (by norm_num)
    exact hbound.trans_lt hsmall
  have hav : (R * Q + W) * (2 * X) < 1 := by
    have hRQ : R * Q ≤ W := calc
      _ = c * P^(-(d : ℝ) + Δ) := by dsimp [R, Q]; rw [Real.rpow_add hP₀, mul_assoc]
      _ ≤ 1 * P^(-(d : ℝ) + Δ) := mul_le_mul_of_nonneg_right hc₁ (by positivity)
      _ ≤ W := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
    calc
      _ ≤ (2 * W) * (2 * X) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 4 * P^(-(d : ℝ) + 4 * Δ) := by
        dsimp [W, X]
        rw [show -(d : ℝ) + 4 * Δ = (-(d : ℝ) + 2 * Δ) + 2 * Δ by ring,
          Real.rpow_add hP₀ (-(d : ℝ) + 2 * Δ) (2 * Δ)]
        ring
      _ ≤ 4 * P^(-1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)) (by norm_num)
      _ < 1 := by
        rw [Real.rpow_neg_one, ← one_div, mul_one_div, div_lt_one hP₀]
        linarith
  refine ⟨hpair', hinside', ?_⟩
  rintro ⟨q,a⟩ hj α hα ⟨s,b,hs,hsQ,_,hnear⟩
  have hnear' : |α - (b : ℝ) / s| * (s : ℝ) ≤ W := by
    calc
      _ ≤ P^(-(d : ℝ) + Δ) * Q := mul_le_mul hnear hsQ (by positivity) (by positivity)
      _ = W := by
        dsimp [W, Q]
        rw [← Real.rpow_add hP₀]
        congr 1
        ring
  exact (not_lt_of_ge hnear') (rationalShellInterval_avoids hX hR hQ hav hj hα hs hsQ b)

/-- A bound proved at the scale `X = P^a` yields a power bound at every large `X`. -/
theorem rationalShell_decay_of_scale {a η C : ℝ} {A : ℝ → ℝ} (ha : 0 < a)
    (h : ∀ᶠ P in atTop, A (P^a) ≤ C * P^(-η)) :
    ∀ᶠ X in atTop, A X ≤ C * X^(-η/a) := by
  filter_upwards [(tendsto_rpow_atTop (inv_pos.mpr ha)).eventually h,
    eventually_ge_atTop (0 : ℝ)] with X hX hX₀
  change A ((X^(a⁻¹))^a) ≤ C * (X^(a⁻¹))^(-η) at hX
  rw [← Real.rpow_mul hX₀, inv_mul_cancel₀ ha.ne', Real.rpow_one, ← Real.rpow_mul hX₀,
    show a⁻¹ * (-η) = -η/a by rw [div_eq_mul_inv, mul_comm]] at hX
  exact hX

/-- A minor-arc integral saving and an accurate pointwise approximation on
the shell imply power decay of the sum of the absolute coefficients. -/
theorem rationalShell_decay_of_minorIntegral {d : ℕ} {a r c D E η L : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) (hD : 0 < D) (hE : 0 ≤ E)
    (hL : 2*a + η ≤ L)
    (minor : ℝ → Set ℝ) (f : ℝ → ℝ → ℝ) (coeff : ℕ × ℕ → ℝ)
    (hf : ∀ P, Continuous (f P)) (hf₀ : ∀ P α, 0 ≤ f P α)
    (hgeometry : ∀ᶠ P : ℝ in atTop,
      let X := P^a
      let R := r * P^(-(d : ℝ))
      (2*R) * (2*X)^2 < 1 ∧ R * (2*X) < 1 ∧
        ∀ j ∈ rationalShellCenters X, rationalShellInterval R j ⊆ minor P)
    (hminor : ∀ᶠ P : ℝ in atTop, (∫ α in minor P, f P α ∂circleMeasure) ≤ D * P^(-(d : ℝ)-η))
    (hpoint : ∀ᶠ P : ℝ in atTop, ∀ j ∈ rationalShellCenters (P^a),
      ∀ α ∈ rationalShellInterval (r * P^(-(d : ℝ))) j,
        c * coeff j ≤ f P α + E * P^(-L)) :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      (∑ j ∈ rationalShellCenters X, coeff j) ≤ C * X^(-η/a) := by
  let C := (D/(2*r) + 9*E) / c
  refine ⟨C, by dsimp [C]; positivity, rationalShell_decay_of_scale ha ?_⟩
  filter_upwards [hgeometry, hminor, hpoint, eventually_ge_atTop (1 : ℝ)] with
    P hgeom hsmall happrox hP
  let X := P^a
  let R := r * P^(-(d : ℝ))
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hX₁ : 1 ≤ X := Real.one_le_rpow hP ha.le
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨hpair, hinside, hsub⟩ := hgeom
  have hcount : ((rationalShellCenters X).card : ℝ) ≤ 9 * P^(2*a) := by
    calc
      _ ≤ (2*X+1)^2 := rationalShellCenters_card_le X (zero_le_one.trans hX₁)
      _ ≤ (3*X)^2 := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := by
        dsimp [X]
        rw [mul_pow, ← Real.rpow_mul_natCast hP₀.le,
          show a * ((2 : ℕ) : ℝ) = 2*a by norm_num [mul_comm]]
        norm_num
  have herror : ((rationalShellCenters X).card : ℝ) * (E * P^(-L)) ≤ 9*E*P^(-η) := by
    calc
      _ ≤ (9 * P^(2*a)) * (E * P^(-L)) := mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = (9*E) * (P^(2*a) * P^(-L)) := by ring
      _ ≤ _ := by
        rw [← Real.rpow_add hP₀]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) (by positivity)
  have hb := rationalShell_sum_le_minorIntegral (zero_le_one.trans hX₁) hR.le
    hpair hinside (minor P) hsub (f P) (hf P) (hf₀ P) coeff c (E * P^(-L)) happrox
  have hb' : (2*R) * (c * ∑ j ∈ rationalShellCenters X, coeff j) ≤
      D * P^(-(d : ℝ)-η) + (2*R) * (9*E*P^(-η)) := by
    refine hb.trans (add_le_add hsmall ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left herror (by positivity)
  have hscale : (2*R) * (D/(2*r) * P^(-η)) = D * P^(-(d : ℝ)-η) := by
    dsimp [R]
    rw [sub_eq_add_neg, Real.rpow_add hP₀]
    field_simp
  rw [← hscale, ← mul_add] at hb'
  have hresult := le_of_mul_le_mul_left hb' (by positivity : 0 < 2*R)
  apply le_of_mul_le_mul_right _ hc
  rw [show C * P^(-η) * c = D/(2*r) * P^(-η) + 9*E*P^(-η) by dsimp [C]; field_simp]
  simpa only [mul_comm c] using hresult

/-- A power bound on positive dyadic blocks gives a power bound on the full tail. -/
theorem summable_and_tsum_tail_le_of_dyadic {f : ℕ → ℝ} (hf : ∀ q, 0 ≤ f q)
    {C γ : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ) {Q₀ : ℕ}
    (h : ∀ Q ≥ Q₀, (∑ q ∈ Finset.Ioc Q (2 * Q), f q) ≤ C * (Q : ℝ)^(-γ)) :
    Summable f ∧ ∀ Q ≥ max 1 Q₀,
      (∑' j : ℕ, f (j + Q + 1)) ≤ C * (Q : ℝ)^(-γ) * (1 - (2 : ℝ)^(-γ))⁻¹ := by
  let z : ℝ := (2 : ℝ)^(-γ)
  have hz₀ : 0 ≤ z := Real.rpow_nonneg (by norm_num) _
  have hz₁ : z < 1 := by
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_zero.mpr hγ)
  have hcut (a b : ℕ) (hab : a ≤ b) :
      (∑ q ∈ Finset.Ioc a b, f q) =
        (∑ q ∈ Finset.range (b+1), f q) - (∑ q ∈ Finset.range (a+1), f q) := by
    have he : Finset.Ioc a b = Finset.Ico (a+1) (b+1) := by
      ext q
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [he, Finset.sum_Ico_eq_sub _ (by omega)]
  have htails (Q : ℕ) (hQ : max 1 Q₀ ≤ Q) :
      Summable (fun j : ℕ => f (j + Q + 1)) ∧
        (∑' j : ℕ, f (j + Q + 1)) ≤ C * (Q : ℝ)^(-γ) * (1 - z)⁻¹ := by
    have hQ₁ : 1 ≤ Q := (le_max_left _ _).trans hQ
    have hQ₂ : Q₀ ≤ Q := (le_max_right _ _).trans hQ
    let q (k : ℕ) : ℕ := Q * 2^k
    let D : ℝ := C * (Q : ℝ)^(-γ)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hq (k : ℕ) : Q ≤ q k := by
      dsimp [q]
      exact le_mul_of_one_le_right (by positivity : 0 ≤ Q) (one_le_pow₀ (by norm_num))
    have hqnext (k : ℕ) : q (k+1) = 2 * q k := by
      dsimp [q]
      rw [pow_succ]
      ring
    have hscale (k : ℕ) : C * (q k : ℝ)^(-γ) = D * z^k := by
      have hpow : (((2 : ℝ)^k) ^ (-γ : ℝ)) = ((2 : ℝ)^(-γ))^k := by
        rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
          mul_comm (k : ℝ) (-γ), Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.rpow_natCast]
      dsimp [q, D, z]
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Real.mul_rpow (by positivity) (by positivity),
        hpow, mul_assoc]
    have hblock (k : ℕ) : (∑ i ∈ Finset.Ioc Q (q k), f i) ≤ ∑ i ∈ Finset.range k, D * z^i := by
      induction k with
      | zero => simp [q]
      | succ k ih =>
        have hkk : q k ≤ q (k+1) := by rw [hqnext]; omega
        have hadd : (∑ i ∈ Finset.Ioc Q (q (k+1)), f i) =
            (∑ i ∈ Finset.Ioc Q (q k), f i) + (∑ i ∈ Finset.Ioc (q k) (q (k+1)), f i) := by
          rw [hcut _ _ (hq _), hcut _ _ (hq _), hcut _ _ hkk]
          ring
        have hlast := h (q k) (hQ₂.trans (hq k))
        rw [← hqnext k, hscale] at hlast
        rw [hadd, Finset.sum_range_succ]
        exact add_le_add ih hlast
    have hg := (summable_geometric_of_lt_one hz₀ hz₁).mul_left D
    have hbound (L : ℕ) : (∑ j ∈ Finset.range L, f (j + Q + 1)) ≤ D * (1-z)⁻¹ := by
      have hshift : (∑ j ∈ Finset.range L, f (j + Q + 1)) =
          ∑ j ∈ Finset.Ioc Q (Q+L), f j := by
        apply Finset.sum_bij (fun j _ => j + Q + 1)
        · intro j hj
          have hj' := Finset.mem_range.mp hj
          exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        · intro j _ i _ he
          omega
        · intro j hj
          obtain ⟨hj₀, hj₁⟩ := Finset.mem_Ioc.mp hj
          exact ⟨j - Q - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intros
          rfl
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((Q+L : ℕ) : ℝ) (by norm_num : 1 < (2 : ℝ))
      have hk' : Q+L ≤ 2^k := by exact_mod_cast hk.le
      have hk'' : Q+L ≤ q k := hk'.trans (by
        dsimp [q]
        exact le_mul_of_one_le_left (by positivity) hQ₁)
      rw [hshift]
      calc
        _ ≤ ∑ j ∈ Finset.Ioc Q (q k), f j := Finset.sum_le_sum_of_subset_of_nonneg
          (fun j hj => Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hj).1,
            (Finset.mem_Ioc.mp hj).2.trans hk''⟩) (fun j _ _ => hf j)
        _ ≤ ∑ i ∈ Finset.range k, D * z^i := hblock k
        _ ≤ ∑' i : ℕ, D * z^i := hg.sum_le_tsum _ (fun _ _ => by positivity)
        _ = D * (1-z)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hz₀ hz₁]
    exact ⟨summable_of_sum_range_le (fun _ => hf _) hbound,
      Real.tsum_le_of_sum_range_le (fun _ => hf _) hbound⟩
  refine ⟨?_, fun Q hQ => (htails Q hQ).2⟩
  simpa only [Nat.add_assoc] using
    (summable_nat_add_iff (max 1 Q₀ + 1)).1 (htails (max 1 Q₀) le_rfl).1

/-- A nonnegative compact weight of positive mass has a transform bounded
away from zero on a sufficiently short interval about zero. -/
theorem realOscillation_lower_near_zero {n : ℕ} (F : IntForm n) {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hcompact : HasCompactSupport w) (hw₀ : ∀ x, 0 ≤ w x)
    (hne : ∃ x, w x ≠ 0) :
    ∃ r ∈ Ioc (0 : ℝ) 1, ∃ c > 0, ∀ γ : ℝ, |γ| ≤ r → c ≤ ‖realOscillation F w γ‖ := by
  obtain ⟨x, hx⟩ := hne
  let m := ∫ x, w x
  have hm : 0 < m :=
    hw.integral_pos_of_hasCompactSupport_nonneg_nonzero hcompact hw₀ hx
  have hzero : realOscillation F w 0 = (m : ℂ) := by
    have hphase : phase 0 = 1 := by simp [phase]
    unfold realOscillation
    simp only [zero_mul, hphase, mul_one]
    exact integral_complex_ofReal (f := w)
  let U := {t : ℝ | m/2 < ‖realOscillation F w t‖}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_realOscillation_of_compact _ hw hcompact).norm
  have hU₀ : (0 : ℝ) ∈ U := by
    change m / 2 < ‖realOscillation F w 0‖
    rw [hzero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    linarith
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU 0 hU₀
  let r := min 1 (δ/2)
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  refine ⟨r, ⟨hr, min_le_left _ _⟩, m/2, by positivity, ?_⟩
  intro γ hγ
  have hγδ : γ ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (hγ.trans (min_le_right _ _)).trans_lt (by linarith)
  exact (hδU hγδ).le

/-- A fixed auxiliary smooth weight can be used for the real lower bound,
independently of the weight in the final asymptotic. -/
theorem exists_cubeWeight_positive_realOscillation {n : ℕ} (F : IntForm n) :
    ∃ w : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
      (∀ x, 0 ≤ w x) ∧ (∀ y, w y ≠ 0 → ∀ i, |y i| < 1) ∧
      ∃ r ∈ Ioc (0 : ℝ) 1, ∃ c > 0, ∀ γ : ℝ, |γ| ≤ r → c ≤ ‖realOscillation F w γ‖ := by
  let U := {y : Fin n → ℝ | ∀ i, |y i| < 1}
  have hU : IsOpen U := by
    rw [show U = ⋂ i : Fin n, {y : Fin n → ℝ | |y i| < 1} by ext; simp [U]]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  have hzero : (0 : Fin n → ℝ) ∈ U := by simp [U]
  obtain ⟨w, hwU, hcompact, hwd, hrange, hwzero⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds hzero)
  have hw₀ (x : Fin n → ℝ) : 0 ≤ w x := (hrange ⟨x, rfl⟩).1
  refine ⟨w, hwd, hcompact, hw₀, fun y hy => hwU (subset_tsupport _ hy), ?_⟩
  exact realOscillation_lower_near_zero F hwd.continuous hcompact hw₀ ⟨0, by rw [hwzero]; norm_num⟩

/-- The absolute form complete sum at a rational center, with zero value at
the unused denominator zero. -/
def formCompleteSumNormAt {n : ℕ} (F : IntForm n) (q a : ℕ) : ℝ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ‖completeSum F q (a : ZMod q)‖

/-- Sum of the absolute complete sums over all unit numerators at conductor `q`. -/
def formConductorMass {n : ℕ} (F : IntForm n) (q : ℕ) : ℝ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ∑ a : (ZMod q)ˣ, ‖completeSum F q a.val‖

private theorem formConductorMass_nonneg {n : ℕ} (F : IntForm n) (q : ℕ) :
    0 ≤ formConductorMass F q := by
  unfold formConductorMass
  split_ifs with h
  · exact le_rfl
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem norm_unitConductorSum_le_formConductorMass {n : ℕ} (F : IntForm n) (q : ℕ) [NeZero q] :
    ‖unitConductorSum F q‖ ≤ formConductorMass F q := by
  rw [formConductorMass, dif_neg (NeZero.ne q), unitConductorSum]
  exact norm_sum_le _ _

/-- Absolute convergence over reduced numerators implies convergence of the
grouped conductor coefficients. -/
theorem summable_norm_unitConductorSum_of_formConductorMass {n : ℕ} {F : IntForm n}
    (hs : Summable (fun j : ℕ => formConductorMass F (j + 1))) :
    Summable (fun j : ℕ => ‖unitConductorSum F (j + 1)‖) :=
  hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => norm_unitConductorSum_le_formConductorMass F (j + 1))

private theorem formCompleteSumNormAt_shell_eq {n Q : ℕ} (hQ : 1 ≤ Q) (F : IntForm n) :
    (∑ j ∈ rationalShellCenters (Q : ℝ), formCompleteSumNormAt F j.1 j.2) =
      ∑ q ∈ Finset.Ioc Q (2*Q), formConductorMass F q := by
  rw [sum_rationalShellCenters_by_denominator Q hQ]
  apply Finset.sum_congr rfl
  intro q hq
  have hq₂ := Nat.succ_le_of_lt (hQ.trans_lt (Finset.mem_Ioc.mp hq).1)
  have hq₀ : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq₀⟩
  simp only [formConductorMass, formCompleteSumNormAt, dif_neg hq₀]
  exact (sum_zmod_units_eq_reducedNumerators q hq₂ (fun a => ‖completeSum F q a‖)).symm

private theorem formConductorMass_tail_of_shell_decay {n : ℕ} (F : IntForm n)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C)
    (h : ∀ᶠ X : ℝ in atTop,
      (∑ j ∈ rationalShellCenters X, formCompleteSumNormAt F j.1 j.2) ≤ C * X^(-γ)) :
    Summable (fun j : ℕ => formConductorMass F (j+1)) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, formConductorMass F (j+Q+1)) ≤ D * (Q : ℝ)^(-γ) := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp h
  let Q₀ := max 1 ⌈B⌉₊
  have hd (Q : ℕ) (hQ : Q₀ ≤ Q) :
      (∑ q ∈ Finset.Ioc Q (2*Q), formConductorMass F q) ≤ C * (Q : ℝ)^(-γ) := by
    have hBQ : B ≤ (Q : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 1 ⌈B⌉₊).trans hQ)
    rw [← formCompleteSumNormAt_shell_eq ((le_max_left _ _).trans hQ) F]
    exact hB _ hBQ
  obtain ⟨hs, htail⟩ := summable_and_tsum_tail_le_of_dyadic (formConductorMass_nonneg F) hC.le hγ hd
  have hpos : 0 < 1 - (2 : ℝ)^(-γ) := by
    apply sub_pos.mpr
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_zero.mpr hγ)
  refine ⟨(summable_nat_add_iff 1).2 hs, C * (1 - (2 : ℝ)^(-γ))⁻¹, by positivity,
    max 1 Q₀, fun Q hQ => ?_⟩
  have hh := htail Q hQ
  rwa [mul_right_comm] at hh

theorem formSingularSeries_tail_of_conductorMass_tail {n : ℕ} {F : IntForm n} {γ : ℝ}
    (h : Summable (fun j : ℕ => formConductorMass F (j+1)) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, formConductorMass F (j+Q+1)) ≤ D * (Q : ℝ)^(-γ)) :
    Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, ‖unitConductorSum F (j+Q+1)‖) ≤ D * (Q : ℝ)^(-γ) := by
  obtain ⟨hs₁, D, hD, Q₀, htail⟩ := h
  have hs₂ := summable_norm_unitConductorSum_of_formConductorMass hs₁
  refine ⟨hs₂, D, hD, Q₀, fun Q hQ => ?_⟩
  have hQ₁ := (summable_nat_add_iff Q).2 hs₁
  have hQ₂ := (summable_nat_add_iff Q).2 hs₂
  calc
    _ ≤ ∑' j : ℕ, formConductorMass F (j+Q+1) := hQ₂.tsum_le_tsum
      (fun j => norm_unitConductorSum_le_formConductorMass F (j+Q+1)) hQ₁
    _ ≤ _ := htail Q hQ

/-- The coefficient bound over shells implies absolute convergence and a
power-saving tail for the form singular series. -/
theorem formSingularSeries_tail_of_shell_decay {n : ℕ} (F : IntForm n)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C)
    (h : ∀ᶠ X : ℝ in atTop,
      (∑ j ∈ rationalShellCenters X, formCompleteSumNormAt F j.1 j.2) ≤ C * X^(-γ)) :
    Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, ‖unitConductorSum F (j+Q+1)‖) ≤ D * (Q : ℝ)^(-γ) :=
  formSingularSeries_tail_of_conductorMass_tail (formConductorMass_tail_of_shell_decay F hγ hC h)

/-- A minor-arc bound for the form, with a compact test weight of positive
mass, bounds all complete sums in a dyadic block in absolute value. -/
theorem formCompleteSumShell_decay_of_minorIntegral {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : MvPolynomial.IsHomogeneous F d)
    (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (hbox : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1)
    {b r c D η : ℝ} (hb : 0 < b) (hb₁ : b < 1) (hr : 0 < r) (hc : 0 < c) (hD : 0 < D)
    (hI : ∀ γ : ℝ, |γ| ≤ r → c ≤ ‖realOscillation F w γ‖)
    (minor : ℝ → Set ℝ)
    (hgeometry : ∀ᶠ P : ℝ in atTop,
      let X := P^b
      let R := r*P^(-(d : ℝ))
      (2*R) * (2*X)^2 < 1 ∧ R * (2*X) < 1 ∧
        ∀ j ∈ rationalShellCenters X, rationalShellInterval R j ⊆ minor P)
    (hminor : ∀ᶠ P : ℝ in atTop,
      (∫ α in minor P, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤ D * P^(-(d : ℝ)-η)) :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop,
      (∑ j ∈ rationalShellCenters X, formCompleteSumNormAt F j.1 j.2) ≤ C * X^(-η/b) := by
  let K : ℝ := 2*(1+r)
  have hK : 0 < K := by dsimp [K]; positivity
  have hτ : 0 < 1-b := sub_pos.mpr hb₁
  let L := 2*b+η
  have hPoisson := majorArcPoissonIdentity_of_smooth_cubeSupported hF hw hcompact hbox
  obtain ⟨E,hE,hbound⟩ := norm_normalizedSum_sub_complete_le_of_poisson_ratio hw hcompact
    hPoisson hK hτ L
  have hcont (P : ℝ) : Continuous (fun α : ℝ => ‖normalizedSum F w P α‖) :=
    ((continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)).norm
  refine rationalShell_decay_of_minorIntegral (E := E) (L := L) hb hr hc hD hE.le le_rfl
    minor (fun P α => ‖normalizedSum F w P α‖) (fun j => formCompleteSumNormAt F j.1 j.2)
    hcont (fun _ _ => norm_nonneg _) hgeometry hminor ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP
  rintro ⟨q,a⟩ hj α hα
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hX : 0 ≤ P^b := Real.rpow_nonneg hP₀.le _
  obtain ⟨hq, _, hqP, _, _, _⟩ := (mem_rationalShellCenters hX).mp hj
  have hq₀ : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq₀⟩
  have hqR : (0 : ℝ) < q := by positivity
  let γ := P^d * (α - (a : ℝ)/q)
  have hγ : |γ| ≤ r := by
    dsimp only [γ]
    rw [abs_mul, abs_of_pos (pow_pos hP₀ _)]
    calc
      _ ≤ P^d * (r*P^(-(d : ℝ))) := mul_le_mul_of_nonneg_left
        (mem_rationalShellInterval.mp hα) (by positivity)
      _ = r * (P^(d : ℝ) * P^(-(d : ℝ))) := by rw [Real.rpow_natCast]; ring
      _ = r := by rw [← Real.rpow_add hP₀, add_neg_cancel, Real.rpow_zero, mul_one]
  have hratio : (1+|γ|) / (P / (q : ℝ)) ≤ K * P^(-(1-b)) := by
    rw [div_div_eq_mul_div]
    calc
      _ ≤ ((1+r) * (2*P^b)) / P := div_le_div_of_nonneg_right
        (mul_le_mul (by linarith) hqP hqR.le (by linarith)) hP₀.le
      _ = K * (P^b / P) := by dsimp [K]; ring
      _ = _ := by rw [← Real.rpow_sub_one hP₀.ne', show b-1 = -(1-b) by ring]
  have herror := hbound P hP q (a : ℤ) α (by simpa only [γ, Int.cast_natCast] using hratio)
  push_cast at herror
  have hosc := hI γ hγ
  let U := normalizedSum F w P α
  let V := completeSum F q (a : ZMod q) * realOscillation F w γ
  have htriangle : ‖V‖ ≤ ‖U‖ + E * P^(-L) := by
    have htri := norm_sub_le U (U-V)
    rw [sub_sub_cancel] at htri
    exact htri.trans (add_le_add le_rfl herror)
  calc
    _ = c * ‖completeSum F q (a : ZMod q)‖ := by simp [formCompleteSumNormAt, hq₀]
    _ ≤ ‖V‖ := by
      dsimp [V]
      rw [norm_mul, mul_comm c]
      exact mul_le_mul_of_nonneg_left hosc (norm_nonneg _)
    _ ≤ _ := htriangle

private theorem formConductorMass_tail_of_weighted_minorArcs {n d : ℕ} {F : IntForm n} (hd : 2 ≤ d)
    (hF : MvPolynomial.IsHomogeneous F d)
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (hbox : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1) {r c η D : ℝ}
    (hr : r ∈ Ioc (0 : ℝ) 1) (hc : 0 < c) (hη : 0 < η) (hD : 0 < D)
    (hI : ∀ γ : ℝ, |γ| ≤ r → c ≤ ‖realOscillation F w γ‖)
    (hestimate : ∀ᶠ P : ℝ in atTop,
      (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤ D*P^(-(d : ℝ)-η)) :
    Summable (fun j : ℕ => formConductorMass F (j+1)) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, formConductorMass F (j+Q+1)) ≤ D * (Q : ℝ)^(-(η/(2/3))) := by
  have hgeometry : ∀ᶠ P : ℝ in atTop,
      let X := P^(2/3 : ℝ)
      let R := r*P^(-(d : ℝ))
      (2*R) * (2*X)^2 < 1 ∧ R * (2*X) < 1 ∧
        ∀ j ∈ rationalShellCenters X, rationalShellInterval R j ⊆ (majorArcs d P)ᶜ := by
    filter_upwards [eventually_ge_atTop (4096 : ℝ)] with P hP
    exact oldMajorArcShell_geometry hd hP hr.1.le hr.2
  obtain ⟨C,hC,h⟩ := formCompleteSumShell_decay_of_minorIntegral hF hw hcompact hbox
    (b := 2/3) (by norm_num) (by norm_num) hr.1 hc hD hI (fun P => (majorArcs d P)ᶜ)
    hgeometry hestimate
  have hγ : 0 < η/(2/3 : ℝ) := by positivity
  rw [show -η/(2/3 : ℝ) = -(η/(2/3 : ℝ)) by ring] at h
  exact formConductorMass_tail_of_shell_decay F hγ hC h

/-- A weight-independent minor-arc saving controls the absolute tail over
all reduced numerators. -/
theorem formConductorMass_tail_of_minorArcs_atExponent {n d : ℕ} {F : IntForm n} (hd : 2 ≤ d)
    (hF : MvPolynomial.IsHomogeneous F d) {η : ℝ} (hη : 0 < η)
    (hminor : ∀ w : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w →
      (∀ x, 0 ≤ w x) → (∀ y, w y ≠ 0 → ∀ i, |y i| < 1) →
      ∃ D > 0, ∀ᶠ P : ℝ in atTop,
        (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤ D*P^(-(d : ℝ)-η)) :
    Summable (fun j : ℕ => formConductorMass F (j+1)) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, formConductorMass F (j+Q+1)) ≤ D * (Q : ℝ)^(-(η/(2/3))) := by
  obtain ⟨w, hw, hcompact, hnneg, hbox, r, hr, c, hc, hI⟩ := exists_cubeWeight_positive_realOscillation F
  obtain ⟨D,hD,hestimate⟩ := hminor w hw hcompact hnneg hbox
  exact formConductorMass_tail_of_weighted_minorArcs hd hF hw hcompact hbox hr hc hη hD hI hestimate

/-- A weight-independent minor-arc saving gives an explicit conductor tail exponent. -/
theorem formSingularSeries_tail_of_minorArcs_atExponent {n d : ℕ} {F : IntForm n} (hd : 2 ≤ d)
    (hF : MvPolynomial.IsHomogeneous F d) {η : ℝ} (hη : 0 < η)
    (hminor : ∀ w : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w →
      (∀ x, 0 ≤ w x) → (∀ y, w y ≠ 0 → ∀ i, |y i| < 1) →
      ∃ D > 0, ∀ᶠ P : ℝ in atTop,
        (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤ D*P^(-(d : ℝ)-η)) :
    Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, ‖unitConductorSum F (j+Q+1)‖) ≤ D * (Q : ℝ)^(-(η/(2/3))) :=
  formSingularSeries_tail_of_conductorMass_tail (formConductorMass_tail_of_minorArcs_atExponent hd hF hη hminor)

/-- The form singular series and a power-saving absolute tail follow from
the minor-arc estimate for smooth weights in the unit cube. -/
theorem formSingularSeries_tail_of_minorArcs {n d : ℕ} {F : IntForm n} (hd : 2 ≤ d)
    (hF : MvPolynomial.IsHomogeneous F d)
    (hminor : ∀ w : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w →
      (∀ x, 0 ≤ w x) → (∀ y, w y ≠ 0 → ∀ i, |y i| < 1) →
      ∃ η > 0, ∃ D > 0, ∀ᶠ P : ℝ in atTop,
        (∫ α in (majorArcs d P)ᶜ, ‖normalizedSum F w P α‖ ∂circleMeasure) ≤ D*P^(-(d : ℝ)-η)) :
    Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖) ∧
      ∃ γ : ℝ, 0 < γ ∧ ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, ‖unitConductorSum F (j+Q+1)‖) ≤ D * (Q : ℝ)^(-γ) := by
  obtain ⟨w, hw, hcompact, hnneg, hbox, r, hr, c, hc, hI⟩ := exists_cubeWeight_positive_realOscillation F
  obtain ⟨η,hη,D,hD,hestimate⟩ := hminor w hw hcompact hnneg hbox
  obtain ⟨hs,hTail⟩ := formSingularSeries_tail_of_conductorMass_tail
    (formConductorMass_tail_of_weighted_minorArcs hd hF hw hcompact hbox hr hc hη hD hI hestimate)
  exact ⟨hs, η/(2/3 : ℝ), by positivity, hTail⟩

/-- The major-arc term for a compact transverse cube weight, with the
singular-series convergence supplied by the absolute conductor tail. -/
theorem formMajorArcIntegral_bound_of_absoluteTail {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hd : 2 ≤ d) (hF : MvPolynomial.IsHomogeneous F d)
    (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (hbox : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1)
    (htrans : ∃ i : Fin n, ∀ x ∈ tsupport w, evalForm (MvPolynomial.pderiv i F) x ≠ 0)
    {γ : ℝ} (hγ : 0 < γ) (hs : Summable (fun j : ℕ => ‖unitConductorSum F (j+1)‖))
    (hTail : ∃ C > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
      (∑' j : ℕ, ‖unitConductorSum F (j+Q+1)‖) ≤ C * (Q : ℝ)^(-γ)) :
    Integrable (realOscillation F w) ∧ ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ‖(∫ α in majorArcs d P, normalizedSum F w P α ∂circleMeasure) -
        (P ^ (-(d : ℝ)) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * P ^ (-(d : ℝ) - min 1 (γ/2)) := by
  have hPoisson := majorArcPoissonIdentity_of_smooth_cubeSupported hF hw hcompact hbox
  have hPoint := pointwiseMajorArcExpansion_of_poisson_of_compact hw hcompact hPoisson
  have hExp := integratedMajorArcExpansion_of_pointwise_of_continuous hd F w
    (continuous_realOscillation_of_compact F hw.continuous hcompact) hPoint
  have hI := integrable_realOscillation_of_compact_transverse hw hcompact htrans
  have hDecay : ∃ D > 0, ∀ t, ‖realOscillation F w t‖ ≤ D*(1+|t|)^(-4 : ℝ) := by
    simpa using realOscillation_rapidDecay_of_compact_transverse hw hcompact htrans 4
  exact ⟨hI, majorArcIntegral_bound_of_expansion_of_absoluteTail F w hγ hExp hs hTail hI hDecay⟩

end

end Birch
