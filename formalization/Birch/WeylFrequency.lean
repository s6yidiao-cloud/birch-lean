import Birch.Weyl

/-!
# Shrinking near-zero linear frequencies in the Weyl argument

One common shrinkage works for all the differencing directions. The reciprocal
power of the shrunken height is exactly the simpler Weyl bracket used in the
source. The frequency count in the shrunken box is then an exact kernel count.
-/

open scoped BigOperators Classical

namespace Birch

noncomputable section

/-- Set the product of the shrinking factors to the reciprocal of this quantity.
The parameter E is the error in the given rational approximation. -/
def weylShrinkDenominator (k : ℕ) (P H E q : ℝ) : ℝ :=
  1 + 2 * E * H * P^k + 2 * q / P + H * P^k / q

/-- The common height reached by shrinking each of the k equal input boxes. -/
def weylShrunkenHeight (k : ℕ) (P H E q : ℝ) : ℝ :=
  P / (weylShrinkDenominator k P H E q) ^ (1 / (k : ℝ))

/-- The near-zero frequency tolerance after all k shrinking steps. -/
def weylShrunkenTolerance (k : ℕ) (P H E q : ℝ) : ℝ :=
  1 / (P * weylShrinkDenominator k P H E q)

theorem weylShrinkDenominator_pos (k : ℕ) {P H E q : ℝ}
    (hP : 0 < P) (hH : 0 < H) (hE : 0 ≤ E) (hq : 0 < q) :
    0 < weylShrinkDenominator k P H E q := by
  unfold weylShrinkDenominator
  positivity

theorem weylShrunkenHeight_pos_le (k : ℕ) {P H E q : ℝ}
    (hP : 0 < P) (hH : 0 < H) (hE : 0 ≤ E) (hq : 0 < q) :
    0 < weylShrunkenHeight k P H E q ∧ weylShrunkenHeight k P H E q ≤ P := by
  have hD : 1 ≤ weylShrinkDenominator k P H E q := by
    unfold weylShrinkDenominator
    apply le_trans (le_add_of_nonneg_right (by positivity : 0 ≤ 2 * E * H * P^k)) _
    exact le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))
  have hA := weylShrinkDenominator_pos k hP hH hE hq
  unfold weylShrunkenHeight
  exact ⟨div_pos hP (Real.rpow_pos_of_pos hA _),
    div_le_self hP.le (Real.one_le_rpow hD (by positivity))⟩

private theorem weylShrunkenHeight_pow {k : ℕ} (hk : 0 < k) {P H E q : ℝ}
    (hP : 0 < P) (hH : 0 < H) (hE : 0 ≤ E) (hq : 0 < q) :
    (weylShrunkenHeight k P H E q)^k = P^k / weylShrinkDenominator k P H E q := by
  have hD := weylShrinkDenominator_pos k hP hH hE hq
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold weylShrunkenHeight
  rw [div_pow, ← Real.rpow_mul_natCast hD.le, one_div_mul_cancel hkR, Real.rpow_one]

/-- The actual common shrink factor relating the frequency tolerance to the
coordinate height. -/
theorem weylShrunkenTolerance_eq {k : ℕ} (hk : 0 < k) {P H E q : ℝ}
    (hP : 0 < P) (hH : 0 < H) (hE : 0 ≤ E) (hq : 0 < q) :
    weylShrunkenTolerance k P H E q = (weylShrunkenHeight k P H E q / P)^k / P := by
  have hD := weylShrinkDenominator_pos k hP hH hE hq
  unfold weylShrunkenTolerance
  rw [div_pow, weylShrunkenHeight_pow hk hP hH hE hq]
  field_simp

/-- The reciprocal k-th power of the shrunken height is the Weyl bracket with
fixed leading-form height. -/
theorem weylShrunkenHeight_inv_pow_eq {k : ℕ} (hk : 0 < k) {P H E q : ℝ}
    (hP : 0 < P) (hH : 0 < H) (hE : 0 ≤ E) (hq : 0 < q) :
    ((weylShrunkenHeight k P H E q)⁻¹)^k =
      (P⁻¹)^k + 2 * H * E + 2 * q / P^(k+1) + H/q := by
  have hD := weylShrinkDenominator_pos k hP hH hE hq
  rw [inv_pow, weylShrunkenHeight_pow hk hP hH hE hq, inv_div, inv_pow, pow_succ]
  unfold weylShrinkDenominator
  field_simp

/-- At the shrunken scales, a near-integer frequency with the prescribed integer
coefficient bound has zero coefficient. The strict determinant inequalities
follow from positive slack in the denominator of the shrink factor. -/
theorem weyl_linear_frequency_zero_of_shrink {k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {P H α : ℝ} (hP : 0 < P) (hH : 0 < H) (a m b : ℤ)
    (hcop : a.natAbs.Coprime q)
    (hm : |(m : ℝ)| ≤ H * (weylShrunkenHeight k P H |(q : ℝ) * α - a| q)^k)
    (hnear : |(m : ℝ) * α - b| ≤ weylShrunkenTolerance k P H |(q : ℝ) * α - a| q) :
    m = 0 := by
  let E := |(q : ℝ) * α - a|
  let D := weylShrinkDenominator k P H E q
  have hE : 0 ≤ E := abs_nonneg _
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hD : 0 < D := weylShrinkDenominator_pos k hP hH hE hqR
  have hPpow : 0 < P^k := pow_pos hP _
  have hbound : |(m : ℝ)| ≤ (H * P^k) / D := by
    change |(m : ℝ)| ≤ H * (weylShrunkenHeight k P H E q)^k at hm
    rw [weylShrunkenHeight_pow hk hP hH hE hqR, ← mul_div_assoc] at hm
    exact hm
  have hD1 : 2 * (H * P^k * E) < D := by
    dsimp only [D, weylShrinkDenominator]
    have hqP : 0 < 2 * (q : ℝ) / P := by positivity
    have hHPq : 0 < H * P^k / q := by positivity
    linarith
  have hD2 : (2 * (q : ℝ)) / P < D := by
    dsimp only [D, weylShrinkDenominator]
    have h0 : 0 ≤ 2 * E * H * P^k := by positivity
    have hHPq : 0 < H * P^k / q := by positivity
    linarith
  have hD3 : H * P^k / (q : ℝ) < D := by
    dsimp only [D, weylShrinkDenominator]
    have h0 : 0 ≤ 2 * E * H * P^k := by positivity
    have hqP : 0 < 2 * (q : ℝ) / P := by positivity
    linarith
  apply primitive_frequency_separation hq a m b hcop
  · change |(m : ℝ)| * E < 1/2
    refine (mul_le_mul_of_nonneg_right hbound hE).trans_lt ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    linarith
  · change |(m : ℝ) * α - b| ≤ 1 / (P * D) at hnear
    refine (mul_le_mul_of_nonneg_left hnear hqR.le).trans_lt ?_
    rw [mul_one_div, div_lt_iff₀ (mul_pos hP hD)]
    have H := (div_lt_iff₀ hP).mp hD2
    nlinarith
  · left
    have hl : |(m : ℝ)| < q := hbound.trans_lt
      ((div_lt_iff₀ hD).mpr (by
        have H := (div_lt_iff₀ hqR).mp hD3
        simpa only [mul_comm] using H))
    have hlZ : |m| < (q : ℤ) := by exact_mod_cast hl
    rw [← Int.natCast_natAbs] at hlZ
    exact_mod_cast hlZ

/-- On a finite shrunken box, the near-zero frequency filter is exactly the
kernel filter. The coefficient bound can come from any bound on a multilinear
map in the differencing variables. -/
theorem weyl_nearFrequency_filter_eq_kernel {ι A : Type*} [Finite ι] {k q : ℕ}
    (hk : 0 < k) (hq : 0 < q) {P H α : ℝ} (hP : 0 < P) (hH : 0 < H) (a : ℤ)
    (hcop : a.natAbs.Coprime q) (T : Finset A) (M : A → ι → ℤ)
    (hbound : ∀ t ∈ T, ∀ j,
      |(M t j : ℝ)| ≤ H * (weylShrunkenHeight k P H |(q : ℝ) * α - a| q)^k) :
    T.filter (fun t => ∀ j, ∃ b : ℤ,
      |(M t j : ℝ) * α - b| ≤ weylShrunkenTolerance k P H |(q : ℝ) * α - a| q) =
        T.filter (fun t => ∀ j, M t j = 0) := by
  ext t
  simp only [Finset.mem_filter]
  refine and_congr_right fun ht => ?_
  constructor
  · intro h j
    obtain ⟨b, hb⟩ := h j
    exact weyl_linear_frequency_zero_of_shrink hk hq hP hH a (M t j) b hcop (hbound t ht j) hb
  · intro h j
    refine ⟨0, ?_⟩
    have hA := weylShrinkDenominator_pos k hP hH (abs_nonneg ((q : ℝ) * α - a))
      (Nat.cast_pos.mpr hq)
    simp only [h j, Int.cast_zero, zero_mul, sub_zero, abs_zero]
    unfold weylShrunkenTolerance
    positivity

/-- A frequency cell in a linear block has at most as many points as the
near-zero cell in a box containing the differences of all pairs of points. -/
theorem weyl_frequencyCell_card_le {ι A : Type*} [AddCommGroup A]
    (T U : Finset A) (M : A →+ (ι → ℤ)) (lower : ι → ℝ) (α ε : ℝ)
    (hdiff : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ U) :
    (T.filter (fun x => ∀ j, ∃ b : ℤ,
        lower j ≤ (M x j : ℝ) * α - b ∧ (M x j : ℝ) * α - b ≤ lower j + ε)).card ≤
      (U.filter (fun x => ∀ j, ∃ b : ℤ, |(M x j : ℝ) * α - b| ≤ ε)).card := by
  let S := T.filter (fun x => ∀ j, ∃ b : ℤ,
    lower j ≤ (M x j : ℝ) * α - b ∧ (M x j : ℝ) * α - b ≤ lower j + ε)
  change S.card ≤ _
  by_cases hs : S.Nonempty
  · obtain ⟨y, hy⟩ := hs
    have hy' := Finset.mem_filter.mp hy
    apply Finset.card_le_card_of_injOn (fun x => x - y)
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨hdiff x hx'.1 y hy'.1, ?_⟩
      intro j
      obtain ⟨b, hbl, hbu⟩ := hx'.2 j
      obtain ⟨c, hcl, hcu⟩ := hy'.2 j
      refine ⟨b - c, ?_⟩
      rw [map_sub, Pi.sub_apply, Int.cast_sub, Int.cast_sub]
      apply abs_le.mpr
      constructor <;> linarith
    · intro x _ z _ he
      exact sub_left_inj.mp he
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.card_empty]
    exact Nat.zero_le _

/-- Following the common shrinkage, any translated frequency cell in a linear
block is controlled by the number of exact zero coefficients in the difference
box. -/
theorem weyl_shrunkenFrequencyCell_card_le_kernel {ι A : Type*} [Finite ι] [AddCommGroup A]
    {k q : ℕ} (hk : 0 < k) (hq : 0 < q) {P H α : ℝ} (hP : 0 < P) (hH : 0 < H) (a : ℤ)
    (hcop : a.natAbs.Coprime q) (T U : Finset A) (M : A →+ (ι → ℤ)) (lower : ι → ℝ)
    (hdiff : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ U)
    (hbound : ∀ t ∈ U, ∀ j,
      |(M t j : ℝ)| ≤ H * (weylShrunkenHeight k P H |(q : ℝ) * α - a| q)^k) :
    let ε := weylShrunkenTolerance k P H |(q : ℝ) * α - a| q
    (T.filter (fun x => ∀ j, ∃ b : ℤ,
        lower j ≤ (M x j : ℝ) * α - b ∧ (M x j : ℝ) * α - b ≤ lower j + ε)).card ≤
      (U.filter (fun x => ∀ j, M x j = 0)).card := by
  let ε := weylShrunkenTolerance k P H |(q : ℝ) * α - a| q
  have h := weyl_frequencyCell_card_le T U M lower α ε hdiff
  rw [weyl_nearFrequency_filter_eq_kernel hk hq hP hH a hcop U M hbound] at h
  exact h

end

end Birch
