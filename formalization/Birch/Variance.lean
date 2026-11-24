import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Variance of visits by integer dilates

The proof uses Hermite's floor identity to bound the discrepancy of a translated
rational grid. Averaging over one of the dilates bounds the covariance without a
logarithmic dependence on the interval width.
-/

open scoped BigOperators ComplexConjugate
open Filter Finset Function MeasureTheory Set

namespace Birch

noncomputable section

/-- The indicator of the closed interval of radius `u` on `ℝ / ℤ`, lifted to `ℝ`. -/
def intervalIndicator (u x : ℝ) : ℝ := by
  classical
  exact if ∃ z : ℤ, |x - (z : ℝ)| ≤ u then 1 else 0

/-- The centered indicator of the closed interval of radius `u` on `ℝ / ℤ`, lifted to `ℝ`. -/
def centeredInterval (u x : ℝ) : ℝ := intervalIndicator u x - 2 * u

theorem measurable_intervalIndicator (u : ℝ) : Measurable (intervalIndicator u) := by
  classical
  unfold intervalIndicator
  apply Measurable.ite _ measurable_const measurable_const
  have hs : {x : ℝ | ∃ z : ℤ, |x - (z : ℝ)| ≤ u} = ⋃ z : ℤ, {x : ℝ | |x - (z : ℝ)| ≤ u} := by
    ext x
    simp
  rw [hs]
  apply MeasurableSet.iUnion
  intro z
  exact (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet

theorem measurable_centeredInterval (u : ℝ) : Measurable (centeredInterval u) :=
  (measurable_intervalIndicator u).sub_const _

theorem abs_centeredInterval_le_one {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2) (x : ℝ) :
    |centeredInterval u x| ≤ 1 := by
  classical
  unfold centeredInterval intervalIndicator
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- An indicator with one boundary point of the interval removed. Floors make its
rational-grid discrepancy exact. -/
private def near (u x : ℝ) : ℝ := (⌊x + u⌋ : ℤ) - (⌊x - u⌋ : ℤ)

private def centered (u x : ℝ) : ℝ := near u x - 2 * u

private lemma near_periodic (u : ℝ) : Periodic (near u) 1 := by
  intro x
  unfold near
  rw [add_right_comm x 1 u, add_sub_right_comm]
  simp [Int.floor_add_one]

private lemma centered_periodic (u : ℝ) : Periodic (centered u) 1 := by
  intro x
  simp only [centered, near_periodic u x]

private lemma measurable_near (u : ℝ) : Measurable (near u) := by
  unfold near
  exact (measurable_of_countable (Int.cast : ℤ → ℝ)).comp ((measurable_id.add_const u).floor) |>.sub
    ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp ((measurable_id.sub_const u).floor))

private lemma measurable_centered (u : ℝ) : Measurable (centered u) :=
  (measurable_near u).sub_const _

private lemma near_eq_one_iff {u x : ℝ} (hu' : u < 1 / 2) :
    near u x = 1 ↔ ∃ z : ℤ, x - u < z ∧ (z : ℝ) ≤ x + u := by
  constructor
  · intro h
    refine ⟨⌊x + u⌋, ?_, Int.floor_le _⟩
    have hlt := Int.lt_floor_add_one (x - u)
    unfold near at h
    linarith
  · rintro ⟨z, hz, hz'⟩
    have hfz : ⌊x + u⌋ = z := Int.floor_eq_iff.mpr ⟨hz', by linarith⟩
    have hfz' : ⌊x - u⌋ = z - 1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by
      push_cast; linarith⟩
    simp [near, hfz, hfz']

private lemma near_nonneg {u : ℝ} (hu : 0 < u) (x : ℝ) : 0 ≤ near u x := by
  have h : ⌊x - u⌋ ≤ ⌊x + u⌋ := Int.floor_mono (by linarith)
  exact sub_nonneg.mpr (by exact_mod_cast h)

private lemma near_eq_zero_or_one {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2) (x : ℝ) :
    near u x = 0 ∨ near u x = 1 := by
  have h₁ := Int.floor_mono (show x - u ≤ x + u by linarith)
  have h₂ := Int.floor_mono (show x + u ≤ x - u + 1 by linarith)
  rw [Int.floor_add_one] at h₂
  have h : ⌊x + u⌋ - ⌊x - u⌋ = 0 ∨ ⌊x + u⌋ - ⌊x - u⌋ = 1 := by omega
  rcases h with h | h
  · left
    unfold near
    exact_mod_cast h
  · right
    unfold near
    exact_mod_cast h

private lemma abs_centered_le_one {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2) (x : ℝ) :
    |centered u x| ≤ 1 := by
  unfold centered
  rcases near_eq_zero_or_one hu hu' x with h | h <;> rw [h] <;> rw [abs_le] <;> constructor <;> linarith

private lemma intervalIntegrable_of_measurable_bound {f : ℝ → ℝ} {A : ℝ}
    (hm : Measurable f) (hA : ∀ x, |f x| ≤ A) (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine intervalIntegrable_iff.mpr (Measure.integrableOn_of_bounded (M := A) ?_
    hm.aestronglyMeasurable (ae_of_all _ fun x => ?_))
  · rw [uIoc]
    exact measure_Ioc_lt_top.ne
  · simpa only [Real.norm_eq_abs] using hA x

private lemma intervalIntegrable_near {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {f : ℝ → ℝ} (hf : Measurable f) (a b : ℝ) :
    IntervalIntegrable (fun x => near u (f x)) volume a b := by
  apply intervalIntegrable_of_measurable_bound ((measurable_near u).comp hf) (A := 1) ?_
  intro x
  rcases near_eq_zero_or_one hu hu' (f x) with h | h <;> simp [h]

private lemma intervalIntegrable_centered {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {f : ℝ → ℝ} (hf : Measurable f) (a b : ℝ) :
    IntervalIntegrable (fun x => centered u (f x)) volume a b :=
  intervalIntegrable_of_measurable_bound ((measurable_centered u).comp hf)
    (fun x => abs_centered_le_one hu hu' (f x)) a b

private lemma floor_grid_sum (b : ℕ) (hb : 0 < b) (x : ℝ) :
    ∑ k ∈ range b, ⌊x + (k : ℝ) / b⌋ = ⌊(b : ℝ) * x⌋ := by
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  let F : ℝ → ℤ := fun y => ∑ k ∈ range b, ⌊y + (k : ℝ) / b⌋ - ⌊(b : ℝ) * y⌋
  have hF : Periodic F (1 / b) := by
    intro y
    have hshift (k : ℕ) : y + 1 / (b : ℝ) + (k : ℝ) / b = y + ((k + 1 : ℕ) : ℝ) / b := by
      push_cast
      rw [add_comm (k : ℝ) 1, add_div]
      ring
    have hlin : (b : ℝ) * (y + 1 / b) = (b : ℝ) * y + 1 := by
      field_simp
    change (∑ k ∈ range b, ⌊y + 1 / (b : ℝ) + (k : ℝ) / b⌋) -
      ⌊(b : ℝ) * (y + 1 / b)⌋ = (∑ k ∈ range b, ⌊y + (k : ℝ) / b⌋) - ⌊(b : ℝ) * y⌋
    simp_rw [hshift, hlin, Int.floor_add_one]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
    rw [Finset.sum_range_succ (f := fun k => ⌊y + ((k + 1 : ℕ) : ℝ) / (m + 1 : ℕ)⌋),
      Finset.sum_range_succ' (f := fun k => ⌊y + (k : ℝ) / (m + 1 : ℕ)⌋)]
    have hM : ((m + 1 : ℕ) : ℝ) ≠ 0 := hB.ne'
    rw [div_self hM, Int.floor_add_one]
    simp only [Nat.cast_succ, Nat.cast_zero, zero_div, add_zero]
    ring
  let z : ℤ := ⌊(b : ℝ) * x⌋
  let y : ℝ := x - (z : ℝ) / b
  have hy : 0 ≤ y := by
    have hz : (z : ℝ) ≤ (b : ℝ) * x := Int.floor_le _
    dsimp [y]
    exact sub_nonneg.mpr ((div_le_iff₀ hB).mpr (by linarith))
  have hy' : y < 1 / b := by
    have hz : (b : ℝ) * x < z + 1 := Int.lt_floor_add_one _
    dsimp [y]
    rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hB]
    linarith
  have hlin : 0 ≤ (b : ℝ) * y ∧ (b : ℝ) * y < 1 := by
    refine ⟨mul_nonneg hB.le hy, ?_⟩
    rw [lt_div_iff₀ hB] at hy'
    simpa [mul_comm] using hy'
  have hs : ∑ k ∈ range b, ⌊y + (k : ℝ) / b⌋ = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    apply Int.floor_eq_iff.mpr
    have hk' : (k : ℝ) + 1 ≤ b := by exact_mod_cast (Finset.mem_range.mp hk)
    constructor
    · simpa using add_nonneg hy (div_nonneg (Nat.cast_nonneg k) hB.le)
    · have h : (1 : ℝ) / b + (k : ℝ) / b ≤ 1 := by
        rw [← add_div, div_le_iff₀ hB]
        linarith
      simp only [Int.cast_zero, zero_add]
      linarith
  have hyF : F y = 0 := by
    dsimp [F]
    have hzero : ⌊(b : ℝ) * y⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr (by simpa using hlin)
    rw [hs, hzero, sub_self]
  have hxy : y + z • (1 / (b : ℝ)) = x := by
    simp only [y, zsmul_eq_mul, div_eq_mul_inv, one_mul, sub_add_cancel]
  have hFx := hF.zsmul z y
  rw [hxy, hyF] at hFx
  exact sub_eq_zero.mp hFx


private lemma centered_grid_bound (u x : ℝ) {b : ℕ} (hb : 0 < b) :
    |∑ k ∈ range b, centered u (x + (k : ℝ) / b)| ≤ 1 := by
  have heq : (∑ k ∈ range b, centered u (x + (k : ℝ) / b)) =
      (⌊(b : ℝ) * (x + u)⌋ : ℝ) - (⌊(b : ℝ) * (x - u)⌋ : ℝ) - (b : ℝ) * (2 * u) := by
    simp only [centered, near, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have heq1 (k : ℕ) : x + (k : ℝ) / b + u = x + u + (k : ℝ) / b := by ring
    have heq2 (k : ℕ) : x + (k : ℝ) / b - u = x - u + (k : ℝ) / b := by ring
    simp_rw [heq1, heq2, ← Int.cast_sum, floor_grid_sum b hb]
  rw [heq, abs_le]
  constructor <;> linarith [Int.floor_le ((b : ℝ) * (x + u)),
    Int.floor_le ((b : ℝ) * (x - u)), Int.lt_floor_add_one ((b : ℝ) * (x + u)),
    Int.lt_floor_add_one ((b : ℝ) * (x - u))]

private lemma centered_coprime_grid (u x : ℝ) {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b) :
    (∑ k ∈ range b, centered u (x + (a : ℝ) * k / b)) =
       ∑ k ∈ range b, centered u (x + (k : ℝ) / b) := by
  let f : ℕ → ℕ := fun k => (a * k) % b
  have hmem : ∀ k ∈ range b, f k ∈ range b := fun k _ => mem_range.mpr (Nat.mod_lt _ hb)
  have hinj : (↑(Finset.range b) : Set ℕ).InjOn f := by
    intro k hk l hl hkl
    exact (Nat.ModEq.cancel_left_of_coprime hab.symm hkl).eq_of_lt_of_lt
      (mem_range.mp hk) (mem_range.mp hl)
  have himage : (range b).image f = range b := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
      exact hmem _ hl
    · rw [Finset.card_image_of_injOn hinj]
  apply Finset.sum_nbij f hmem hinj
  · intro k hk
    have hk' : k ∈ (range b).image f := himage.symm ▸ hk
    exact Finset.mem_image.mp hk'
  · intro k _
    have hB : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    have hcast : (f k : ℝ) + (b : ℝ) * ((a*k)/b : ℕ) = (a : ℝ) * k := by
      exact_mod_cast Nat.mod_add_div (a*k) b
    have hx : x + (a : ℝ) * k / b = (x + (f k : ℝ) / b) + ((a*k)/b : ℕ) • (1 : ℝ) := by
      rw [nsmul_eq_mul, mul_one]
      field_simp
      linarith
    rw [hx]
    exact (centered_periodic u).nsmul ((a*k)/b) (x + (f k : ℝ) / b)

private lemma integral_periodic_dilate {f : ℝ → ℝ} (hf : Periodic f 1)
    (hfi : ∀ a b, IntervalIntegrable f volume a b) {k : ℕ} (hk : 0 < k) :
    (∫ x in (0 : ℝ)..1, f ((k : ℝ) * x)) = ∫ x in (0 : ℝ)..1, f x := by
  have hK : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have h := hf.intervalIntegral_add_zsmul_eq (k : ℤ) 0 hfi
  simp only [natCast_zsmul, zero_add, nsmul_eq_mul, mul_one] at h
  simp_rw [mul_comm (k : ℝ), intervalIntegral.integral_comp_mul_right f hK, zero_mul, one_mul, h,
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]


private lemma integral_near {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2) :
    (∫ x in (0 : ℝ)..1, near u x) = 2 * u := by
  have hInt := intervalIntegrable_near hu hu' (f := id) measurable_id
  calc
    (∫ x in (0 : ℝ)..1, near u x) = ∫ x in (-u)..(1 - u), near u x := by
      simpa [sub_eq_add_neg, add_comm] using (near_periodic u).intervalIntegral_add_eq 0 (-u)
    _ = (∫ x in (-u)..u, near u x) + ∫ x in u..(1 - u), near u x :=
      (intervalIntegral.integral_add_adjacent_intervals (hInt (-u) u) (hInt u (1 - u))).symm
    _ = (∫ _ in (-u)..u, (1 : ℝ)) + ∫ _ in u..(1 - u), (0 : ℝ) := by
      congr 1
      · apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro x hx
        exact (near_eq_one_iff hu').mpr ⟨0, by push_cast; linarith [hx.2], by push_cast; linarith [hx.1]⟩
      · apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro x hx
        refine (near_eq_zero_or_one hu hu' x).resolve_right fun h => ?_
        rcases (near_eq_one_iff hu').mp h with ⟨z, hz1, hz2⟩
        have hz : (0 : ℤ) < z := by exact_mod_cast (show (0 : ℝ) < z by linarith [hx.1])
        have hz' : z < (1 : ℤ) := by exact_mod_cast (show (z : ℝ) < 1 by linarith [hx.2])
        omega
    _ = 2 * u := by simp; ring

private lemma integral_near_dilate {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2) {k : ℕ} (hk : 0 < k) :
    (∫ x in (0 : ℝ)..1, near u ((k : ℝ) * x)) = 2 * u := by
  rw [integral_periodic_dilate (near_periodic u)
    (intervalIntegrable_near hu hu' (f := id) measurable_id) hk, integral_near hu hu']

private lemma integral_centered_dilate {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2) {k : ℕ} (hk : 0 < k) :
    (∫ x in (0 : ℝ)..1, centered u ((k : ℝ) * x)) = 0 := by
  unfold centered
  rw [intervalIntegral.integral_sub (intervalIntegrable_near hu hu' (by fun_prop) _ _)
    intervalIntegrable_const, integral_near_dilate hu hu' hk]
  simp

private lemma abs_near_le_one {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2) (x : ℝ) :
    |near u x| ≤ 1 := by
  rcases near_eq_zero_or_one hu hu' x with h | h <;> simp [h]

private lemma integral_centered_mul_near {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {a b : ℕ} (ha : 0 < a) :
    (∫ x in (0 : ℝ)..1, centered u ((a : ℝ) * x) * centered u ((b : ℝ) * x)) =
      ∫ x in (0 : ℝ)..1, centered u ((a : ℝ) * x) * near u ((b : ℝ) * x) := by
  have hL : IntervalIntegrable (fun x => centered u ((a : ℝ) * x) * near u ((b : ℝ) * x)) volume 0 1 := by
    apply intervalIntegrable_of_measurable_bound
      (((measurable_centered u).comp (by fun_prop)).mul ((measurable_near u).comp (by fun_prop)))
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [abs_mul]
    exact mul_le_one₀ (abs_centered_le_one hu hu' _) (abs_nonneg _) (abs_near_le_one hu hu' _)
  have hR := (intervalIntegrable_centered hu hu' (f := fun x => (a : ℝ) * x) (by fun_prop) 0 1).mul_const (2 * u)
  change (∫ x in (0 : ℝ)..1, centered u ((a : ℝ) * x) * (near u ((b : ℝ) * x) - 2*u)) = _
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hL hR, intervalIntegral.integral_mul_const, integral_centered_dilate hu hu' ha]
  simp

private lemma integral_coprime_covariance {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    |∫ x in (0 : ℝ)..1, centered u ((a : ℝ) * x) * centered u ((b : ℝ) * x)| ≤ 2 * u / b := by
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  let φ : ℝ → ℝ := fun x => centered u ((a : ℝ) * x) * near u ((b : ℝ) * x)
  have hφ : Periodic φ 1 := by
    intro x
    simp only [φ, mul_add, mul_one]
    have ha' := (centered_periodic u).nsmul a ((a : ℝ) * x)
    have hb' := (near_periodic u).nsmul b ((b : ℝ) * x)
    simp only [nsmul_eq_mul, mul_one] at ha' hb'
    rw [ha', hb']
  let ψ : ℕ → ℝ → ℝ := fun k x => near u ((b : ℝ) * x) * centered u ((a : ℝ) * x + (a : ℝ) * k / b)
  have hshift (k : ℕ) (x : ℝ) : ψ k x = φ (x + (k : ℝ) / b) := by
    dsimp only [φ, ψ]
    rw [mul_comm, mul_add (a : ℝ), ← mul_div_assoc, mul_add (b : ℝ), ← mul_div_assoc,
      mul_div_cancel_left₀ (k : ℝ) hB.ne']
    congr 1
    simpa [nsmul_eq_mul] using ((near_periodic u).nsmul k ((b : ℝ) * x)).symm
  have hshiftIntegral (k : ℕ) : (∫ x in (0 : ℝ)..1, ψ k x) = ∫ x in (0 : ℝ)..1, φ x := by
    simp_rw [hshift, intervalIntegral.integral_comp_add_right φ]
    simpa [add_comm] using hφ.intervalIntegral_add_eq ((k : ℝ) / b) 0
  have hψi (k : ℕ) : IntervalIntegrable (ψ k) volume 0 1 := by
    apply intervalIntegrable_of_measurable_bound
      (((measurable_near u).comp (by fun_prop)).mul ((measurable_centered u).comp (by fun_prop)))
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [abs_mul]
    exact mul_le_one₀ (abs_near_le_one hu hu' _) (abs_nonneg _) (abs_centered_le_one hu hu' _)
  have havg : (b : ℝ) * (∫ x in (0 : ℝ)..1, φ x) =
      ∫ x in (0 : ℝ)..1, ∑ k ∈ range b, ψ k x := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => hψi k)]
    simp [hshiftIntegral, nsmul_eq_mul]
  have hpoint (x : ℝ) : |∑ k ∈ range b, ψ k x| ≤ near u ((b : ℝ) * x) := by
    simp only [ψ, ← Finset.mul_sum, abs_mul, abs_of_nonneg (near_nonneg hu _)]
    rw [centered_coprime_grid u _ hb hab]
    exact mul_le_of_le_one_right (near_nonneg hu _) (centered_grid_bound u _ hb)
  have hNorm : IntervalIntegrable (fun x => |∑ k ∈ range b, ψ k x|) volume 0 1 := by
    simpa only [Finset.sum_apply] using (IntervalIntegrable.sum (range b) (fun k _ => hψi k)).abs
  rw [integral_centered_mul_near hu hu' ha]
  apply (le_div_iff₀ hB).mpr
  change |∫ x in (0 : ℝ)..1, φ x| * (b : ℝ) ≤ 2 * u
  calc
    _ = |(b : ℝ) * ∫ x in (0 : ℝ)..1, φ x| := by rw [abs_mul, abs_of_pos hB, mul_comm]
    _ ≤ 2*u := ?_
  rw [havg]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  rw [← integral_near_dilate hu hu' hb]
  exact intervalIntegral.integral_mono_on zero_le_one hNorm
    (intervalIntegrable_near hu hu' (by fun_prop) _ _) (fun x _ => hpoint x)


private lemma interval_covariance {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    |∫ x in (0 : ℝ)..1, centered u ((i : ℝ) * x) * centered u ((j : ℝ) * x)| ≤
      (2 * u) * ((i.gcd j : ℝ) / j) := by
  let g := i.gcd j
  let a := i / g
  let b := j / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hi
  have hga : g * a = i := Nat.mul_div_cancel' (Nat.gcd_dvd_left i j)
  have hgb : g * b = j := Nat.mul_div_cancel' (Nat.gcd_dvd_right i j)
  have ha : 0 < a := Nat.pos_of_ne_zero fun ha => hi.ne' (by simpa [ha] using hga.symm)
  have hb : 0 < b := Nat.pos_of_ne_zero fun hb => hj.ne' (by simpa [hb] using hgb.symm)
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hg
  let f : ℝ → ℝ := fun x => centered u ((a : ℝ) * x) * centered u ((b : ℝ) * x)
  have hf : Periodic f 1 := by
    intro x
    simp only [f, mul_add, mul_one]
    have ha' := (centered_periodic u).nsmul a ((a : ℝ) * x)
    have hb' := (centered_periodic u).nsmul b ((b : ℝ) * x)
    simp only [nsmul_eq_mul, mul_one] at ha' hb'
    rw [ha', hb']
  have hfi : ∀ x y, IntervalIntegrable f volume x y := by
    apply intervalIntegrable_of_measurable_bound
      (((measurable_centered u).comp (by fun_prop)).mul ((measurable_centered u).comp (by fun_prop)))
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [abs_mul]
    exact mul_le_one₀ (abs_centered_le_one hu hu' _) (abs_nonneg _) (abs_centered_le_one hu hu' _)
  have hga' : (g : ℝ) * a = i := by exact_mod_cast hga
  have hgb' : (g : ℝ) * b = j := by exact_mod_cast hgb
  have hInt : (∫ x in (0 : ℝ)..1, centered u ((i : ℝ) * x) * centered u ((j : ℝ) * x)) =
      ∫ x in (0 : ℝ)..1, f x := by
    rw [← integral_periodic_dilate hf hfi hg]
    simp [f, ← mul_assoc, mul_comm (a : ℝ) (g : ℝ), mul_comm (b : ℝ) (g : ℝ), hga', hgb']
  rw [hInt]
  refine (integral_coprime_covariance hu hu' ha hb hab).trans_eq ?_
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  change 2 * u / (b : ℝ) = (2 * u) * ((g : ℝ) / j)
  rw [← hgb']
  field_simp

private lemma card_positive_multiples (N d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 N).filter (fun i => d ∣ i)).card = N / d := by
  have himage : (Finset.Icc 1 (N / d)).image (fun k => d * k) =
      (Finset.Icc 1 N).filter (fun i => d ∣ i) := by
    ext i
    constructor
    · intro hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      have hk' := Finset.mem_Icc.mp hk
      have hpos : 0 < d * k := Nat.mul_pos hd (by omega)
      have hle := (Nat.le_div_iff_mul_le hd).mp hk'.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by simpa [mul_comm] using hle⟩,
        dvd_mul_right d k⟩
    · intro hi
      obtain ⟨hi, k, rfl⟩ := Finset.mem_filter.mp hi
      have hi' := Finset.mem_Icc.mp hi
      have hpos : 1 ≤ k := by
        by_contra! hk
        have hk0 : k = 0 := by omega
        simp [hk0] at hi'
      have hle := (Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using hi'.2 : k * d ≤ N)
      exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hpos, hle⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ (fun _ _ => Nat.eq_of_mul_eq_mul_left hd), Nat.card_Icc]
  simp

private lemma sum_gcd_le (j : ℕ) (hj : 0 < j) :
    (∑ i ∈ Finset.Icc 1 j, (i.gcd j : ℝ)) ≤
      (j : ℝ) * ∑ d ∈ Finset.Icc 1 j, if d ∣ j then (1 : ℝ) else 0 := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 j, ∑ d ∈ Finset.Icc 1 j, if d ∣ j then (if d ∣ i then (d : ℝ) else 0) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      have hmem : i.gcd j ∈ Finset.Icc 1 j :=
        Finset.mem_Icc.mpr ⟨Nat.gcd_pos_of_pos_right _ hj, Nat.gcd_le_right _ hj⟩
      apply le_trans ?_ (Finset.single_le_sum (f := fun d => if d ∣ j then (if d ∣ i then (d : ℝ) else 0) else 0)
        (fun d _ => by split_ifs <;> positivity) hmem)
      simp [Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ = ∑ d ∈ Finset.Icc 1 j, ∑ i ∈ Finset.Icc 1 j, if d ∣ j then (if d ∣ i then (d : ℝ) else 0) else 0 :=
      Finset.sum_comm
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      by_cases hdvd : d ∣ j
      · simp only [hdvd, if_true, mul_one, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [card_positive_multiples _ _ (Finset.mem_Icc.mp hd).1]
        exact_mod_cast (Nat.div_mul_le_self j d)
      · simp [hdvd]

private lemma sum_divisor_counts_le (L : ℕ) :
    (∑ j ∈ Finset.Icc 1 L, ∑ d ∈ Finset.Icc 1 j, if d ∣ j then (1 : ℝ) else 0) ≤
      (L : ℝ) * (harmonic L : ℝ) := by
  classical
  have hrecip : (∑ d ∈ Finset.Icc 1 L, (d : ℝ)⁻¹) = (harmonic L : ℝ) := by
    rw [harmonic, Rat.cast_sum]
    simp only [Rat.cast_inv, Rat.cast_natCast]
    symm
    apply Finset.sum_nbij' (fun d => d + 1) (fun d => d - 1)
    · intro d hd
      simp only [Finset.mem_range] at hd
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro d hd
      have h := Finset.mem_Icc.mp hd
      exact Finset.mem_range.mpr (by omega)
    · intro d _
      omega
    · intro d hd
      have h := Finset.mem_Icc.mp hd
      omega
    · intro d _
      rfl
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 L, ∑ d ∈ Finset.Icc 1 L, if d ∣ j then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc_right (Finset.mem_Icc.mp hj).2
      · intro d _ _
        split_ifs <;> positivity
    _ = ∑ d ∈ Finset.Icc 1 L, ∑ j ∈ Finset.Icc 1 L, if d ∣ j then (1 : ℝ) else 0 := Finset.sum_comm
    _ ≤ _ := by
      rw [← hrecip, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      have hd' : 0 < d := (Finset.mem_Icc.mp hd).1
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, card_positive_multiples _ _ hd']
      rw [← div_eq_mul_inv, le_div_iff₀ (by exact_mod_cast hd')]
      exact_mod_cast Nat.div_mul_le_self L d


private lemma sum_gcd_div_max_le (L : ℕ) :
    (∑ j ∈ Finset.Icc 1 L, ∑ i ∈ Finset.Icc 1 L, (i.gcd j : ℝ) / (max i j : ℕ)) ≤
      2 * (L : ℝ) * (harmonic L : ℝ) := by
  let s := Finset.Icc 1 L
  let T : ℕ → ℕ → ℝ := fun i j => if i ≤ j then (i.gcd j : ℝ) / j else 0
  have hpoint (i j : ℕ) : (i.gcd j : ℝ) / (max i j : ℕ) ≤ T i j + T j i := by
    rcases le_total i j with hij | hji
    · have hEq : T i j = (i.gcd j : ℝ) / j := if_pos hij
      rw [max_eq_right hij, ← hEq]
      apply le_add_of_nonneg_right
      dsimp [T]
      split_ifs <;> positivity
    · have hEq : T j i = (j.gcd i : ℝ) / i := if_pos hji
      rw [max_eq_left hji, Nat.gcd_comm i j, ← hEq]
      apply le_add_of_nonneg_left
      dsimp [T]
      split_ifs <;> positivity
  have ht (j : ℕ) (hj : j ∈ s) :
      (∑ i ∈ s, T i j) ≤ ∑ d ∈ Finset.Icc 1 j, if d ∣ j then (1 : ℝ) else 0 := by
    have hj' := Finset.mem_Icc.mp hj
    have hfilter : s.filter (fun i => i ≤ j) = Finset.Icc 1 j := by
      ext i
      simp only [s, Finset.mem_filter, Finset.mem_Icc]
      omega
    simp only [T, ← Finset.sum_filter, hfilter, ← Finset.sum_div]
    have hJ : (0 : ℝ) < j := by exact_mod_cast hj'.1
    apply (div_le_iff₀ hJ).mpr
    rw [mul_comm]
    simpa only [Finset.sum_filter] using sum_gcd_le j hj'.1
  calc
    _ ≤ ∑ j ∈ s, ∑ i ∈ s, (T i j + T j i) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hpoint i j
    _ = 2 * ∑ j ∈ s, ∑ i ∈ s, T i j := by
      simp_rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun j i => T j i)]
      ring
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (Finset.sum_le_sum ht).trans (sum_divisor_counts_le L)

private lemma covariance_le_gcd_div_max {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    |∫ x in (0 : ℝ)..1, centered u ((i : ℝ) * x) * centered u ((j : ℝ) * x)| ≤
      2 * u * ((i.gcd j : ℝ) / (max i j : ℕ)) := by
  rcases le_total i j with hij | hji
  · rw [max_eq_right hij]
    exact interval_covariance hu hu' hi hj
  · rw [max_eq_left hji, Nat.gcd_comm i j]
    simp_rw [mul_comm (centered u ((i : ℝ) * _)) (centered u ((j : ℝ) * _))]
    exact interval_covariance hu hu' hj hi

private lemma ae_centeredInterval_eq_centered {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {k : ℕ} (hk : 0 < k) : (fun x => centeredInterval u ((k : ℝ) * x)) =ᵐ[volume]
      fun x => centered u ((k : ℝ) * x) := by
  classical
  have hK : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  filter_upwards [(Set.countable_range (fun z : ℤ => ((z : ℝ) + u) / k)).ae_notMem volume] with x hx
  have hx' (z : ℤ) : (k : ℝ) * x - u ≠ z := by
    intro h
    apply hx
    refine ⟨z, (div_eq_iff hK).mpr ?_⟩
    linarith
  have heq : (∃ z : ℤ, |(k : ℝ) * x - (z : ℝ)| ≤ u) ↔
      ∃ z : ℤ, (k : ℝ) * x - u < z ∧ (z : ℝ) ≤ (k : ℝ) * x + u := by
    constructor
    · rintro ⟨z, hz⟩
      rw [abs_le] at hz
      exact ⟨z, lt_of_le_of_ne (by linarith) (hx' z), by linarith⟩
    · rintro ⟨z, hz₁, hz₂⟩
      exact ⟨z, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  simp only [centeredInterval, intervalIndicator, centered]
  by_cases h : ∃ z : ℤ, |(k : ℝ) * x - (z : ℝ)| ≤ u
  · rw [if_pos h, (near_eq_one_iff hu').mpr (heq.mp h)]
  · rw [if_neg h, (near_eq_zero_or_one hu hu' _).resolve_right fun h' =>
       h (heq.mpr ((near_eq_one_iff hu').mp h'))]


/-- Positive integer dilates of the interval have mean equal to its length. -/
theorem integral_intervalIndicator_dilate {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {k : ℕ} (hk : 0 < k) :
    (∫ x in Set.Ioc (0 : ℝ) 1, intervalIndicator u ((k : ℝ) * x)) = 2 * u := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_congr_ae (g := fun x => near u ((k : ℝ) * x))
    ((ae_centeredInterval_eq_centered hu hu' hk).mono fun x hx _ => by
      change intervalIndicator u ((k : ℝ) * x) - 2*u = near u ((k : ℝ) * x) - 2*u at hx
      linarith only [hx])]
  exact integral_near_dilate hu hu' hk

/-- The centered interval indicator has mean zero after any positive integer dilation. -/
theorem integral_centeredInterval_dilate {u : ℝ} (hu : 0 < u) (hu' : u < 1 / 2)
    {k : ℕ} (hk : 0 < k) :
    (∫ x in Set.Ioc (0 : ℝ) 1, centeredInterval u ((k : ℝ) * x)) = 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_congr_ae (g := fun x => centered u ((k : ℝ) * x))
    ((ae_centeredInterval_eq_centered hu hu' hk).mono fun _ hx _ => hx)]
  exact integral_centered_dilate hu hu' hk

/-- The variance estimate of `lem:variance`, with the logarithm in the interval width removed.
`Ioc 0 1` realizes normalized Lebesgue measure on the circle, and the finite sum runs over
all positive dilates up to `L`. -/
theorem dilated_interval_variance (u C : ℝ) (L : ℕ) (hu : 0 < u) (hu' : u < 1 / 2)
    (hL : 2 ≤ L) (c : ℕ → ℂ) (hc : ∀ j ∈ Finset.Icc 1 L, ‖c j‖ ≤ C) :
    (∫ x in Set.Ioc (0 : ℝ) 1, ‖∑ j ∈ Finset.Icc 1 L, c j * (centeredInterval u ((j : ℝ) * x) : ℂ)‖ ^ 2)
       ≤ 64 * C^2 * u * (L : ℝ) * Real.log (2 * (L : ℝ)) := by
  let s := Finset.Icc 1 L
  let f : ℕ → ℝ → ℝ := fun j x => centered u ((j : ℝ) * x)
  let w : ℕ → ℕ → ℝ := fun i j => (c i * conj (c j)).re
  have hC : 0 ≤ C := (norm_nonneg _).trans (hc 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩))
  have haec : ∀ᵐ x ∂volume, ∀ j ∈ s, centeredInterval u ((j : ℝ) * x) = f j x := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j ∈ s
    · filter_upwards [ae_centeredInterval_eq_centered hu hu' (Finset.mem_Icc.mp hj).1] with x hx
      exact fun _ => hx
    · exact ae_of_all _ fun _ hj' => (hj hj').elim
  rw [← intervalIntegral.integral_of_le zero_le_one]
  rw [intervalIntegral.integral_congr_ae (g := fun x => ‖∑ j ∈ s, c j * (f j x : ℂ)‖ ^ 2)
    (haec.mono fun x hx _ => by
      apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
      exact Finset.sum_congr rfl (fun j hj => by rw [hx j hj]))]
  have hpoint (x : ℝ) :
      ‖∑ i ∈ s, c i * (f i x : ℂ)‖ ^ 2 = ∑ j ∈ s, ∑ i ∈ s, w i j * (f i x * f j x) := by
    let z : ℂ := ∑ i ∈ s, c i * (f i x : ℂ)
    change ‖z‖ ^ 2 = _
    have hz : ‖z‖ ^ 2 = (z * conj z).re := by rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    rw [hz]
    simp only [z, map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    have heq : (c i * (f i x : ℂ)) * (conj (c j) * (f j x : ℂ)) =
        (↑(f i x * f j x) : ℂ) * (c i * conj (c j)) := by push_cast; ring
    rw [heq, Complex.re_ofReal_mul]
    simp [w, mul_comm]
  have hint (i j : ℕ) : IntervalIntegrable (fun x => w i j * (f i x * f j x)) volume 0 1 := by
    apply IntervalIntegrable.const_mul
    apply intervalIntegrable_of_measurable_bound
      (((measurable_centered u).comp (by fun_prop)).mul ((measurable_centered u).comp (by fun_prop)))
    intro x
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [abs_mul]
    exact mul_le_one₀ (abs_centered_le_one hu hu' _) (abs_nonneg _) (abs_centered_le_one hu hu' _)
  have houter (j : ℕ) : IntervalIntegrable (fun x => ∑ i ∈ s, w i j * (f i x * f j x)) volume 0 1 := by
    have hEq : (∑ i ∈ s, fun x => w i j * (f i x * f j x)) =
        (fun x => ∑ i ∈ s, w i j * (f i x * f j x)) := by
      ext x
      exact Finset.sum_apply x _ _
    rw [← hEq]
    exact IntervalIntegrable.sum s (fun i _ => hint i j)
  simp_rw [hpoint, intervalIntegral.integral_finsetSum (fun j _ => houter j),
    intervalIntegral.integral_finsetSum (fun i _ => hint i _), intervalIntegral.integral_const_mul]
  have hterm (i j : ℕ) (hi : i ∈ s) (hj : j ∈ s) :
      w i j * (∫ x in (0 : ℝ)..1, f i x * f j x) ≤ (2 * C^2 * u) * ((i.gcd j : ℝ) / (max i j : ℕ)) := by
    have hw : |w i j| ≤ C^2 := by
      unfold w
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [Complex.norm_mul, Complex.norm_conj, pow_two]
      exact mul_le_mul (hc i hi) (hc j hj) (norm_nonneg _) hC
    calc
      _ ≤ |w i j| * |∫ x in (0 : ℝ)..1, f i x * f j x| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ C^2 * (2 * u * ((i.gcd j : ℝ) / (max i j : ℕ))) :=
        mul_le_mul hw (covariance_le_gcd_div_max hu hu' (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1)
          (abs_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hLn : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hH : (harmonic L : ℝ) ≤ 2 * Real.log (2 * (L : ℝ)) := by
    refine (harmonic_le_one_add_log L).trans ?_
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith [Real.log_two_gt_d9, Real.log_nonneg hLn]
  calc
    _ ≤ ∑ j ∈ s, ∑ i ∈ s, (2 * C^2 * u) * ((i.gcd j : ℝ) / (max i j : ℕ)) :=
      Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => hterm i j hi hj
    _ ≤ (2 * C^2 * u) * (2 * (L : ℝ) * (harmonic L : ℝ)) := by
      simp_rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_gcd_div_max_le L) (by positivity)
    _ ≤ (2 * C^2 * u) * (2 * (L : ℝ) * (2 * Real.log (2 * (L : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH (by positivity)) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg C) hu.le)
      (show (0 : ℝ) ≤ L by positivity)) (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * L))]

end

end Birch
