import Birch.WeylPacking
import Birch.WeylSymplectic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Shrinking a symmetric linear frequency box

The integer pairs encoding the frequencies are split into a fixed number of
congruence classes. Translated differences in each class span an isotropic
subspace of dimension at most the number of input variables. Packing in that
subspace gives the shrinking exponent.
-/

open Set Finset Matrix MeasureTheory Measure Module
open scoped BigOperators Matrix

namespace Birch

noncomputable section

/-- Integer inputs and their nearest-integer aliases in a linear Weyl block. -/
abbrev WeylPair (n : ℕ) := (Fin n → ℤ) × (Fin n → ℤ)

private def weylRealVector {n : ℕ} (u : Fin n → ℤ) : Fin n → ℝ := fun i => u i

/-- The normalized input and residual blocks, with radii H and δ. -/
def normalizedWeylPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (H δ : ℝ)
    (x : WeylPair n) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => (x.1 i : ℝ)/H, fun i => ((A *ᵥ weylRealVector x.1) i - (x.2 i : ℝ))/δ)

theorem normalizedWeylPair_sub {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (H δ : ℝ)
    (x y : WeylPair n) :
    normalizedWeylPair A H δ (x-y) = normalizedWeylPair A H δ x - normalizedWeylPair A H δ y := by
  have hv : weylRealVector (x.1-y.1) = weylRealVector x.1 - weylRealVector y.1 := by
    funext i
    simp [weylRealVector]
  apply Prod.ext
  · funext i
    simp [normalizedWeylPair, sub_div]
  · funext i
    simp only [normalizedWeylPair, Prod.fst_sub, Prod.snd_sub, hv, Matrix.mulVec_sub,
      Pi.sub_apply, Int.cast_sub]
    ring

private def integerWeylSymplectic {n : ℕ} (x y : WeylPair n) : ℤ :=
  ∑ i, (x.2 i * y.1 i - x.1 i * y.2 i)

private theorem integerWeylSymplectic_eq_residual {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) (x y : WeylPair n) :
    (integerWeylSymplectic x y : ℝ) =
      ∑ i, ((x.1 i : ℝ) * ((A *ᵥ weylRealVector y.1) i - (y.2 i : ℝ)) -
        ((A *ᵥ weylRealVector x.1) i - (x.2 i : ℝ)) * (y.1 i : ℝ)) := by
  have hsym := Matrix.dotProduct_transpose_mulVec A (weylRealVector x.1) (weylRealVector y.1)
  rw [hA, dotProduct_comm (weylRealVector y.1)] at hsym
  unfold integerWeylSymplectic
  push_cast
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  change (∑ i, (x.2 i : ℝ) * (y.1 i : ℝ)) - (∑ i, (x.1 i : ℝ) * (y.2 i : ℝ)) =
    ((weylRealVector x.1) ⬝ᵥ (A *ᵥ weylRealVector y.1) - (∑ i, (x.1 i : ℝ) * (y.2 i : ℝ))) -
      ((A *ᵥ weylRealVector x.1) ⬝ᵥ (weylRealVector y.1) - (∑ i, (x.2 i : ℝ) * (y.1 i : ℝ)))
  rw [hsym]
  ring

private theorem weylSymplectic_normalizedWeylPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) (H δ : ℝ) (x y : WeylPair n) :
    weylSymplectic n (normalizedWeylPair A H δ x) (normalizedWeylPair A H δ y) =
      (H*δ)⁻¹ * (integerWeylSymplectic x y : ℝ) := by
  rw [weylSymplectic_apply, integerWeylSymplectic_eq_residual A hA, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [normalizedWeylPair, div_eq_mul_inv, mul_inv]
  ring

private theorem normalizedWeylPair_bounds {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {H δ R : ℝ} (hH : 0 < H) (hδ : 0 < δ) (x : WeylPair n)
    (hx : ‖normalizedWeylPair A H δ x‖ ≤ R) (i : Fin n) :
    |(x.1 i : ℝ)| ≤ H*R ∧ |(A *ᵥ weylRealVector x.1) i - (x.2 i : ℝ)| ≤ δ*R := by
  let e := normalizedWeylPair A H δ x
  have h₁ : ‖e.1‖ ≤ R := (le_max_left _ _).trans hx
  have h₂ : ‖e.2‖ ≤ R := (le_max_right _ _).trans hx
  have h₁' := (norm_le_pi_norm e.1 i).trans h₁
  have h₂' := (norm_le_pi_norm e.2 i).trans h₂
  simp only [e, normalizedWeylPair, Real.norm_eq_abs, abs_div, abs_of_pos hH, abs_of_pos hδ,
    div_le_iff₀ hH, div_le_iff₀ hδ] at h₁' h₂'
  exact ⟨by simpa only [mul_comm H R] using h₁', by simpa only [mul_comm δ R] using h₂'⟩

private def weylCongruenceModulus (n : ℕ) : ℕ := 8*n+1

private def weylCongruence {n : ℕ} (x : WeylPair n) :
    (Fin n → ZMod (weylCongruenceModulus n)) × (Fin n → ZMod (weylCongruenceModulus n)) :=
  (fun i => x.1 i, fun i => x.2 i)

private theorem weylCongruence_sub {n : ℕ} (x y : WeylPair n) :
    weylCongruence (x-y) = weylCongruence x - weylCongruence y := by
  apply Prod.ext <;> funext i <;> simp [weylCongruence]

private theorem abs_integerWeylSymplectic_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (x y : WeylPair n)
    (hx : ‖normalizedWeylPair A H δ x‖ ≤ 2) (hy : ‖normalizedWeylPair A H δ y‖ ≤ 2) :
    |(integerWeylSymplectic x y : ℝ)| ≤ 8 * (n : ℝ) * (H * δ) := by
  rw [integerWeylSymplectic_eq_residual A hA]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin n, ((H*2)*(δ*2)+(δ*2)*(H*2)) := by
      apply sum_le_sum
      intro i _
      have hx' := normalizedWeylPair_bounds A hH hδ x hx i
      have hy' := normalizedWeylPair_bounds A hH hδ y hy i
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hx'.1 hy'.2 (abs_nonneg _) (by positivity))
        (mul_le_mul hx'.2 hy'.1 (abs_nonneg _) (by positivity))
    _ = _ := by simp [nsmul_eq_mul]; ring

private theorem weylSymplectic_normalized_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) {H δ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hsmall : H*δ ≤ 1)
    (x y : WeylPair n)
    (hx : ‖normalizedWeylPair A H δ x‖ ≤ 2) (hy : ‖normalizedWeylPair A H δ y‖ ≤ 2)
    (hcong : weylCongruence x = 0) :
    weylSymplectic n (normalizedWeylPair A H δ x) (normalizedWeylPair A H δ y) = 0 := by
  let c := weylCongruenceModulus n
  let J := integerWeylSymplectic x y
  have hc : 0 < c := by simp [c, weylCongruenceModulus]
  let : NeZero c := ⟨hc.ne'⟩
  have ha₁ (i : Fin n) : (x.1 i : ZMod c) = 0 :=
    congrArg (fun p => p.1 i) hcong
  have ha₂ (i : Fin n) : (x.2 i : ZMod c) = 0 :=
    congrArg (fun p => p.2 i) hcong
  have hJ : (J : ZMod c) = 0 := by
    dsimp only [J, integerWeylSymplectic]
    push_cast
    simp [ha₁, ha₂]
  have hdiv : (c : ℤ) ∣ J := (CharP.intCast_eq_zero_iff (ZMod c) c J).mp hJ
  have hlt : |(J : ℝ)| < (c : ℝ) := by
    refine (abs_integerWeylSymplectic_le A hA hH hδ x y hx hy).trans_lt ?_
    have hbound : 8 * (n : ℝ) * (H * δ) ≤ 8 * (n : ℝ) := mul_le_of_le_one_right (by positivity) hsmall
    refine hbound.trans_lt ?_
    dsimp [c, weylCongruenceModulus]
    push_cast
    linarith
  have hz : J = 0 := by
    by_contra! h
    have hnat : c ∣ J.natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hdiv
    have hle : c ≤ J.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr h) hnat
    have hleR : (c : ℝ) ≤ |(J : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
      exact_mod_cast hle
    exact hlt.not_ge hleR
  rw [weylSymplectic_normalizedWeylPair A hA, show integerWeylSymplectic x y = 0 from hz,
    Int.cast_zero, mul_zero]

/-- Davenport's shrinking exponent for a symmetric frequency matrix. If
normalized pairs in the large box are closer than θ, their differences must
belong to the small box U. The resulting exponent is n, although the pairs
have 2n coordinates. -/
theorem symmetric_frequency_pair_card_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : Aᵀ = A) {H δ θ : ℝ} (hH : 0 < H) (hδ : 0 < δ) (hθ : 0 < θ)
    (hsmall : H * δ ≤ 1) (S U : Finset (WeylPair n))
    (hS : ∀ x ∈ S, ‖normalizedWeylPair A H δ x‖ ≤ 1)
    (hU : ∀ x ∈ S, ∀ y ∈ S, ‖normalizedWeylPair A H δ (x - y)‖ < θ → x - y ∈ U) :
    (S.card : ℝ) ≤ ((8 * n + 1 : ℕ) : ℝ) ^ (2 * n) *
      (1 + 4 / θ) ^ n * (U.card : ℝ) := by
  classical
  let c := weylCongruenceModulus n
  have hc : 0 < c := by simp [c, weylCongruenceModulus]
  let : NeZero c := ⟨hc.ne'⟩
  let T := S.image weylCongruence
  let C a := S.filter (fun x => weylCongruence x = a)
  have hC (a) (ha : a ∈ T) : ((C a).card : ℝ) ≤ (1 + 4 / θ) ^ n * (U.card : ℝ) := by
    obtain ⟨x₀, hx₀, hr₀⟩ := Finset.mem_image.mp ha
    let f (x : WeylPair n) := normalizedWeylPair A H δ (x - x₀)
    let D := f '' (↑(C a) : Set (WeylPair n))
    let V := Submodule.span ℝ D
    have hCS {x} (hx : x ∈ C a) : x ∈ S := (Finset.mem_filter.mp hx).1
    have hfr {x} (hx : x ∈ C a) : ‖f x‖ ≤ 2 := by
      dsimp only [f]
      rw [normalizedWeylPair_sub]
      exact (norm_sub_le _ _).trans (by linarith [hS x (hCS hx), hS x₀ hx₀])
    have hz {x} (hx : x ∈ C a) : weylCongruence (x - x₀) = 0 := by
      rw [weylCongruence_sub, hr₀, (Finset.mem_filter.mp hx).2, sub_self]
    have hV : finrank ℝ V ≤ n := by
      apply finrank_span_le_of_weylSymplectic_zero
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact weylSymplectic_normalized_zero A hA hH hδ hsmall (x - x₀) (y - x₀)
        (hfr hx) (hfr hy) (hz hx)
    let g (x : (C a : Finset (WeylPair n))) : V :=
      ⟨f x.val, Submodule.subset_span ⟨x.val, x.property, rfl⟩⟩
    let : MeasurableSpace V := borel V
    let : BorelSpace V := ⟨rfl⟩
    have hpack := finset_card_le_cover_times_differences (Module.finBasis ℝ V).addHaar
      (C a) U g (R := 2) (by norm_num) hθ (fun x => hfr x.property) (by
        intro x y hxy
        apply hU x.val (hCS x.property) y.val (hCS y.property)
        rw [dist_eq_norm_sub] at hxy
        change ‖f x.val - f y.val‖ < θ at hxy
        rwa [← normalizedWeylPair_sub, sub_sub_sub_cancel_right] at hxy)
    norm_num at hpack
    refine hpack.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    exact pow_le_pow_right₀ (by linarith [div_pos (show (0 : ℝ) < 4 by norm_num) hθ]) hV
  have hcard : (T.card : ℝ) ≤ (c : ℝ) ^ (2 * n) := by
    have hraw : T.card ≤ Fintype.card ((Fin n → ZMod c) × (Fin n → ZMod c)) :=
      Finset.card_le_univ T
    simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_add] at hraw
    rw [← two_mul] at hraw
    exact_mod_cast hraw
  change (S.card : ℝ) ≤ (c : ℝ) ^ (2 * n) * (1 + 4 / θ) ^ n * (U.card : ℝ)
  rw [Finset.card_eq_sum_card_image weylCongruence S, Nat.cast_sum, mul_assoc]
  change (∑ a ∈ T, ((C a).card : ℝ)) ≤ _
  calc
    _ ≤ ∑ _a ∈ T, ((1 + 4 / θ) ^ n * (U.card : ℝ)) := Finset.sum_le_sum hC
    _ = (T.card : ℝ) * ((1 + 4 / θ) ^ n * (U.card : ℝ)) := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end

end Birch
