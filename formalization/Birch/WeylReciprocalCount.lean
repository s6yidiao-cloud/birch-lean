import Birch.WeylPartialSummation
import Birch.WeylFrequency
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# From reciprocal-distance weights to near-integer frequencies

Partition the signed residue of each frequency coordinate into bins of width
`1/B`. The mass of the majorant over those bins costs one logarithm per
coordinate, and the differences of each bin contribute to the near-zero count.
-/

open Finset
open scoped BigOperators Classical

namespace Birch

noncomputable section

private def signedFrequencyBin (B : ℕ) (t : ℝ) : ℤ :=
  ⌊(B : ℝ) * (t - (round t : ℝ))⌋

private theorem signedFrequencyBin_mem (B : ℕ) (t : ℝ) :
    signedFrequencyBin B t ∈ Icc (-(B : ℤ)) (B : ℤ) := by
  have hr := abs_le.mp (nearestIntegerDistance_le_half t)
  change -(1/2 : ℝ) ≤ t - (round t : ℝ) ∧ t - (round t : ℝ) ≤ 1/2 at hr
  have hlo := mul_le_mul_of_nonneg_left hr.1 (Nat.cast_nonneg (α := ℝ) B)
  have hhi := mul_le_mul_of_nonneg_left hr.2 (Nat.cast_nonneg (α := ℝ) B)
  unfold signedFrequencyBin
  apply mem_Icc.mpr
  constructor
  · apply Int.le_floor.mpr
    push_cast
    linarith
  · have hh := (Int.floor_le ((B : ℝ) * (t - (round t : ℝ)))).trans (hhi.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) B] : (B : ℝ) * (1/2) ≤ B))
    exact_mod_cast hh

private theorem signedFrequencyBin_bounds {B : ℕ} (hB : 0 < B) (t : ℝ) :
    (signedFrequencyBin B t : ℝ)/(B : ℝ) ≤ t - (round t : ℝ) ∧
      t - (round t : ℝ) ≤ (signedFrequencyBin B t : ℝ)/(B : ℝ) + 1/(B : ℝ) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  constructor
  · apply (div_le_iff₀ hBR).mpr
    unfold signedFrequencyBin
    rw [mul_comm]
    exact Int.floor_le _
  · rw [← add_div]
    apply (le_div_iff₀ hBR).mpr
    unfold signedFrequencyBin
    rw [mul_comm]
    exact (Int.lt_floor_add_one _).le

private def harmonicBinMajorant (B : ℕ) (b : ℤ) : ℝ :=
  6*(B : ℝ)/(1+(b.natAbs : ℝ))

private theorem linearPhaseBound_le_bin {B : ℕ} (hB : 0 < B) {L : ℝ} (hL : L ≤ 3*(B : ℝ))
    (t : ℝ) : linearPhaseBound L t ≤ harmonicBinMajorant B (signedFrequencyBin B t) := by
  let b := signedFrequencyBin B t
  let u := t - (round t : ℝ)
  let δ := nearestIntegerDistance t
  have hB₀ : (0 : ℝ) < B := by exact_mod_cast hB
  have hb₀ : (b : ℝ) ≤ (B : ℝ)*u := Int.floor_le _
  have hb₁ : (B : ℝ)*u < (b : ℝ)+1 := Int.lt_floor_add_one _
  have habs : (b.natAbs : ℝ) ≤ (B : ℝ)*δ + 1 := by
    have hd : |(b : ℝ)-(B : ℝ)*u| ≤ 1 := abs_le.mpr (by constructor <;> linarith)
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    calc
      _ = |(B : ℝ)*u + ((b : ℝ)-(B : ℝ)*u)| := by congr 1; ring
      _ ≤ |(B : ℝ)*u| + |(b : ℝ)-(B : ℝ)*u| := abs_add_le _ _
      _ ≤ (B : ℝ)*δ + 1 := by
        rw [abs_mul, abs_of_nonneg hB₀.le]
        exact add_le_add_right hd _
  by_cases hb : b.natAbs ≤ 1
  · have hbR : (b.natAbs : ℝ) ≤ 1 := by exact_mod_cast hb
    refine (linearPhaseBound_le _ _).trans (hL.trans ?_)
    unfold harmonicBinMajorant
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1+(b.natAbs : ℝ))).mpr
    nlinarith only [mul_nonneg hB₀.le (sub_nonneg.mpr hbR)]
  · have hbR : (2 : ℝ) ≤ (b.natAbs : ℝ) := by exact_mod_cast (by omega : 2 ≤ b.natAbs)
    have hδ : 0 < δ := by
      have hp := nearestIntegerDistance_nonneg t
      by_contra! h
      have he : δ = 0 := le_antisymm h hp
      rw [he, mul_zero, zero_add] at habs
      linarith
    unfold linearPhaseBound harmonicBinMajorant
    rw [if_neg hδ.ne']
    refine (min_le_right _ _).trans ?_
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*δ)
      (by positivity : (0 : ℝ) < 1+(b.natAbs : ℝ))).mpr
    have hmul : 1 ≤ (B : ℝ)*δ := by linarith
    nlinarith only [habs, hmul]

private theorem harmonicBinMajorant_sum_le (B : ℕ) :
    (∑ b ∈ Icc (-(B : ℤ)) (B : ℤ), harmonicBinMajorant B b) ≤
      12*(B : ℝ)*(1+Real.log ((B : ℝ)+1)) := by
  let J := range (B+1)
  let f (k : ℤ) : ℝ := 1/(1+(k.natAbs : ℝ))
  let U := J.image (fun j : ℕ => (j : ℤ))
  let V := J.image (fun j : ℕ => -(j : ℤ))
  have hs : Icc (-(B : ℤ)) (B : ℤ) ⊆ U ∪ V := by
    intro k hk
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hk
    by_cases h : 0 ≤ k
    · exact mem_union_left _ (mem_image.mpr ⟨k.toNat, mem_range.mpr (by omega), Int.toNat_of_nonneg h⟩)
    · refine mem_union_right _ (mem_image.mpr ⟨(-k).toNat, mem_range.mpr (by omega), ?_⟩)
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ -k), neg_neg]
  have hnon (k : ℤ) : 0 ≤ f k := by unfold f; positivity
  have hsum : (∑ j ∈ J, ((1 : ℝ)+j)⁻¹) ≤ 1+Real.log ((B : ℝ)+1) := by
    calc
      _ = ∑ j ∈ J, ((j : ℝ)+1)⁻¹ := by
        apply sum_congr rfl
        intro j _
        rw [add_comm]
      _ ≤ _ := by
        simpa only [J, harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_one,
          Rat.cast_natCast, Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (B+1)
  have hU : (∑ k ∈ U, f k) = ∑ j ∈ J, ((1 : ℝ)+j)⁻¹ := by
    rw [show U = J.image (fun j : ℕ => (j : ℤ)) from rfl,
      sum_image (by intro x _ y _; exact Int.ofNat.inj)]
    simp only [f, Int.natAbs_natCast, one_div]
  have hV : (∑ k ∈ V, f k) = ∑ j ∈ J, ((1 : ℝ)+j)⁻¹ := by
    rw [show V = J.image (fun j : ℕ => -(j : ℤ)) from rfl,
      sum_image (by intro x _ y _ h; exact Int.ofNat.inj (neg_injective h))]
    simp only [f, Int.natAbs_neg, Int.natAbs_natCast, one_div]
  have htwo : (∑ k ∈ U ∪ V, f k) ≤ (∑ k ∈ U, f k) + ∑ k ∈ V, f k := by
    have h : (∑ k ∈ U ∪ V, f k) + (∑ k ∈ U ∩ V, f k) =
        (∑ k ∈ U, f k) + ∑ k ∈ V, f k := sum_union_inter
    have h₀ : 0 ≤ ∑ k ∈ U ∩ V, f k := sum_nonneg fun k _ => hnon k
    linarith
  have hfb : (∑ b ∈ Icc (-(B : ℤ)) (B : ℤ), f b) ≤ 2*(1+Real.log ((B : ℝ)+1)) := by
    calc
      _ ≤ ∑ k ∈ U ∪ V, f k := sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => hnon k)
      _ ≤ (∑ k ∈ U, f k) + ∑ k ∈ V, f k := htwo
      _ ≤ _ := by rw [hU,hV]; linarith
  calc
    _ = 6*(B : ℝ) * ∑ b ∈ Icc (-(B : ℤ)) (B : ℤ), f b := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      simp only [harmonicBinMajorant, f, div_eq_mul_inv, one_mul]
    _ ≤ 6*(B : ℝ) * (2*(1+Real.log ((B : ℝ)+1))) :=
      mul_le_mul_of_nonneg_left hfb (by positivity)
    _ = _ := by ring

/-- The reciprocal-distance product summed over a finite block is bounded by
one logarithm per coordinate times the near-zero count in its difference box.
The slack in the frequency width can be chosen through the bin parameter. -/
theorem sum_linearPhaseBound_le_frequency_count {A : Type*} [AddCommGroup A]
    {n B : ℕ} (hB : 0 < B) {L : ℝ} (hL₀ : 0 ≤ L) (hL : L ≤ 3*(B : ℝ))
    (T U : Finset A) (M : A →+ (Fin n → ℤ)) (α : ℝ)
    (hdiff : ∀ x ∈ T, ∀ y ∈ T, x-y ∈ U) :
    (∑ x ∈ T, ∏ i, linearPhaseBound L ((M x i : ℝ)*α)) ≤
      (12*(B : ℝ)*(1+Real.log ((B : ℝ)+1)))^n *
        ((U.filter (fun x => ∀ j, ∃ b : ℤ,
          |(M x j : ℝ)*α - b| ≤ 1/(B : ℝ))).card : ℝ) := by
  classical
  let bin (x : A) (i : Fin n) := signedFrequencyBin B ((M x i : ℝ)*α)
  let W (v : Fin n → ℤ) := ∏ i, harmonicBinMajorant B (v i)
  let J := latticeBox n (B : ℝ)
  let Y := U.filter (fun x => ∀ j, ∃ b : ℤ, |(M x j : ℝ)*α - b| ≤ 1/(B : ℝ))
  have hbin (x : A) (_ : x ∈ T) : bin x ∈ J := by
    apply Fintype.mem_piFinset.mpr
    intro i
    simpa only [Int.floor_natCast] using signedFrequencyBin_mem B ((M x i : ℝ)*α)
  have hW (v : Fin n → ℤ) : 0 ≤ W v :=
    prod_nonneg fun _ _ => by unfold harmonicBinMajorant; positivity
  have hcard (v : Fin n → ℤ) : (T.filter (fun x => bin x = v)).card ≤ Y.card := by
    let lower (i : Fin n) : ℝ := (v i : ℝ)/(B : ℝ)
    let C := T.filter (fun x => ∀ j, ∃ b : ℤ, lower j ≤ (M x j : ℝ)*α-b ∧
      (M x j : ℝ)*α-b ≤ lower j + 1/(B : ℝ))
    have hCY : C.card ≤ Y.card := by
      have H := weyl_frequencyCell_card_le T U M lower α (1/(B : ℝ)) hdiff
      convert H using 1 <;> congr 1 <;> apply Finset.ext <;> intro x <;>
        simp only [C, Y, Finset.mem_filter]
    refine (card_le_card ?_).trans hCY
    intro x hx
    obtain ⟨hxT,hbinx⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hxT, fun i => ?_⟩
    refine ⟨round ((M x i : ℝ)*α), ?_⟩
    have he : signedFrequencyBin B ((M x i : ℝ)*α) = v i := congrFun hbinx i
    simpa only [he, lower] using signedFrequencyBin_bounds hB ((M x i : ℝ)*α)
  have hfiber : (∑ x ∈ T, W (bin x)) =
      ∑ v ∈ J, ((T.filter (fun x => bin x = v)).card : ℝ) * W v := by
    rw [← sum_fiberwise_of_maps_to hbin]
    apply sum_congr rfl
    intro v _
    calc
      _ = ∑ _x ∈ T.filter (fun x => bin x = v), W v := by
        apply sum_congr rfl
        intro x hx
        rw [(mem_filter.mp hx).2]
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  calc
    _ ≤ ∑ x ∈ T, W (bin x) := sum_le_sum fun x _ =>
      prod_le_prod (fun i _ => linearPhaseBound_nonneg hL₀ _) (fun i _ => linearPhaseBound_le_bin hB hL _)
    _ = ∑ v ∈ J, ((T.filter (fun x => bin x = v)).card : ℝ) * W v := hfiber
    _ ≤ ∑ v ∈ J, (Y.card : ℝ) * W v :=
      sum_le_sum fun v _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v) (hW v)
    _ = (Y.card : ℝ) * (∑ b ∈ Icc (-(B : ℤ)) (B : ℤ), harmonicBinMajorant B b)^n := by
      rw [← mul_sum]
      congr 1
      have he : J = Fintype.piFinset (fun _ : Fin n => Icc (-(B : ℤ)) (B : ℤ)) := by
        simp only [J, latticeBox, Int.floor_natCast]
      rw [he]
      dsimp only [W]
      rw [← Finset.prod_univ_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (Y.card : ℝ) * (12*(B : ℝ)*(1+Real.log ((B : ℝ)+1)))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (sum_nonneg fun _ _ => by unfold harmonicBinMajorant; positivity)
        (harmonicBinMajorant_sum_le B) n) (Nat.cast_nonneg Y.card)
    _ = _ := mul_comm _ _

/-- At the Weyl box scale, the logarithmic factor can be absorbed into any
prescribed positive power of `P`. The frequency width remains `1/(2P)`. -/
theorem sum_weylIntervalPhaseBound_le_frequency_count {A : Type*} [AddCommGroup A]
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ C > 0, ∀ (P : ℝ), 1 ≤ P →
      ∀ (T U : Finset A) (M : A →+ (Fin n → ℤ)) (α : ℝ),
      (∀ x ∈ T, ∀ y ∈ T, x-y ∈ U) →
      (∑ x ∈ T, ∏ i, linearPhaseBound (weylIntervalLength P) ((M x i : ℝ)*α)) ≤
        (C * P^ε * P^n) * ((U.filter (fun x => ∀ j, ∃ b : ℤ,
          |(M x j : ℝ)*α-b| ≤ 1/(2*P))).card : ℝ) := by
  classical
  let γ := ε/((n : ℝ)+1)
  let c := 36*(1+(4 : ℝ)^γ/γ)
  have hγ : 0 < γ := div_pos hε (by positivity)
  have hc : 0 < c := by unfold c; positivity
  refine ⟨c^n, pow_pos hc _, fun P hP T U M α hdiff => ?_⟩
  let B : ℕ := ⌈2*P⌉₊
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hB₁ : 2*P ≤ (B : ℝ) := Nat.le_ceil _
  have hB₀ : 0 < (B : ℝ) := (by positivity : 0 < 2*P).trans_le hB₁
  have hB : 0 < B := Nat.cast_pos.mp hB₀
  have hB₂ : (B : ℝ) ≤ 3*P := by
    have H := Nat.ceil_lt_add_one (show 0 ≤ 2*P by positivity)
    change (B : ℝ) < 2*P+1 at H
    linarith
  have hL : (weylIntervalLength P : ℝ) ≤ 3*(B : ℝ) :=
    (weylIntervalLength_le_three hP).trans (by linarith)
  let U₀ := U.filter (fun x => ∀ j, ∃ b : ℤ, |(M x j : ℝ)*α-b| ≤ 1/(B : ℝ))
  let U₁ := U.filter (fun x => ∀ j, ∃ b : ℤ, |(M x j : ℝ)*α-b| ≤ 1/(2*P))
  have hU : U₀.card ≤ U₁.card := by
    apply card_le_card
    intro x hx
    obtain ⟨hu,hx₀⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hu, fun j => ?_⟩
    obtain ⟨b,hb⟩ := hx₀ j
    exact ⟨b,hb.trans (one_div_le_one_div_of_le (by positivity) hB₁)⟩
  have hlog : Real.log ((B : ℝ)+1) ≤ ((4 : ℝ)^γ/γ) * P^γ := by
    calc
      _ ≤ Real.log (4*P) := Real.log_le_log (by positivity) (by linarith)
      _ ≤ (4*P)^γ/γ := Real.log_le_rpow_div (by positivity) hγ
      _ = _ := by rw [Real.mul_rpow (by norm_num : 0 ≤ (4 : ℝ)) hP₀.le]; ring
  have hPγ : 1 ≤ P^γ := Real.one_le_rpow hP hγ.le
  have hlogNonneg : 0 ≤ 1+Real.log ((B : ℝ)+1) :=
    add_nonneg zero_le_one (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) B]))
  have hterm : 12*(B : ℝ)*(1+Real.log ((B : ℝ)+1)) ≤ c*P*P^γ := by
    calc
      _ ≤ 12*(3*P)*(1+Real.log ((B : ℝ)+1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB₂ (by norm_num))
          hlogNonneg
      _ ≤ 12*(3*P)*((1+(4 : ℝ)^γ/γ)*P^γ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hPγ, hlog]
      _ = _ := by unfold c; ring
  have hγn : γ*(n : ℝ) ≤ ε := by
    unfold γ
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hε.le])
  have hpow : ((P^γ)^n) ≤ P^ε := by
    rw [← Real.rpow_mul_natCast hP₀.le]
    exact Real.rpow_le_rpow_of_exponent_le hP hγn
  have hbound : (12*(B : ℝ)*(1+Real.log ((B : ℝ)+1)))^n ≤ c^n*P^ε*P^n := by
    calc
      _ ≤ (c*P*P^γ)^n := pow_le_pow_left₀ (mul_nonneg (by positivity) hlogNonneg) hterm _
      _ = (c^n*P^n)*(P^γ)^n := by rw [mul_pow,mul_pow]
      _ ≤ (c^n*P^n)*P^ε := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hC := sum_linearPhaseBound_le_frequency_count hB
    (L := (weylIntervalLength P : ℝ)) (Nat.cast_nonneg _) hL T U M α hdiff
  calc
    _ ≤ (12*(B : ℝ)*(1+Real.log ((B : ℝ)+1)))^n * (U₀.card : ℝ) := by
      convert hC using 2
    _ ≤ (c^n*P^ε*P^n) * (U₁.card : ℝ) :=
      mul_le_mul hbound (by exact_mod_cast hU)
        (Nat.cast_nonneg U₀.card) (by positivity)
    _ = _ := by congr 2

end
end Birch
