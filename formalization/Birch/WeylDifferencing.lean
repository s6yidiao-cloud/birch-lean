import Birch.WeylPolarization
import Birch.DifferencingChain
import Birch.FrozenCoordinates
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Fin.Tuple.Finset

/-! # Repeated Weyl differencing on the supported lattice box -/

open Finset
open scoped BigOperators

namespace Birch

noncomputable section

variable {n : ℕ}

/-- The weight after the ordinary differencing shifts have been applied from
left to right. -/
def weylDifferencedWeight (hs : List (Fin n → ℤ)) (w : (Fin n → ℝ) → ℝ) (P : ℝ) :
    (Fin n → ℝ) → ℝ :=
  hs.foldl (fun v h => differencedWeight v P 1 h) w

@[simp] theorem weylDifferencedWeight_nil (w : (Fin n → ℝ) → ℝ) (P : ℝ) :
    weylDifferencedWeight [] w P = w := rfl

@[simp] theorem weylDifferencedWeight_cons (h : Fin n → ℤ) (hs : List (Fin n → ℤ))
    (w : (Fin n → ℝ) → ℝ) (P : ℝ) :
    weylDifferencedWeight (h :: hs) w P =
      weylDifferencedWeight hs (differencedWeight w P 1 h) P := rfl

/-- The iterated weights remain supported in the original cube. -/
theorem weylDifferencedWeight_cubeSupported (hs : List (Fin n → ℤ))
    (w : (Fin n → ℝ) → ℝ) (P : ℝ) (hw : CubeSupported w) :
    CubeSupported (weylDifferencedWeight hs w P) := by
  induction hs generalizing w with
  | nil => exact hw
  | cons h hs ih =>
    apply ih
    intro y hy
    apply hw y
    intro hzero
    exact hy (by simp [differencedWeight, hzero])

/-- The Cartesian product of the closed boxes for the ordinary differences. -/
def weylShiftBox (n k : ℕ) (P : ℝ) : Finset (Fin k → Fin n → ℤ) :=
  Fintype.piFinset (fun _ => latticeBox n P)

theorem card_weylShiftBox (n k : ℕ) (P : ℝ) :
    (weylShiftBox n k P).card = (latticeBox n P).card^k :=
  Fintype.card_piFinset_const _ _

/-- The integer box volume is comparable to the geometric scale. -/
theorem card_latticeBox_between (n : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    P^n ≤ ((latticeBox n P).card : ℝ) ∧ ((latticeBox n P).card : ℝ) ≤ (3*P)^n := by
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hfloor : 0 ≤ ⌊P⌋ := Int.floor_nonneg.mpr hp.le
  have hcard : ((Finset.Icc (-⌊P⌋) ⌊P⌋).card : ℝ) =
      (⌊P⌋ : ℝ) + 1 - (-(⌊P⌋ : ℝ)) := by
    exact_mod_cast Int.card_Icc_of_le (-⌊P⌋) ⌊P⌋ (by omega)
  unfold latticeBox
  rw [Fintype.card_piFinset_const, Nat.cast_pow, hcard]
  exact ⟨pow_le_pow_left₀ hp.le (by linarith [Int.lt_floor_add_one P]) _,
    pow_le_pow_left₀ (by linarith [Int.floor_nonneg.mpr hp.le]) (by linarith [Int.floor_le P]) _⟩

private theorem norm_normalizedSum_eq_div {P : ℝ} (hP : 0 < P)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (α : ℝ) :
    ‖normalizedSum F w P α‖ = ‖exponentialSum F w P α‖ / P^n := by
  rw [normalizedSum, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.rpow_neg hP.le, Real.rpow_natCast, div_eq_mul_inv, mul_comm]

private theorem norm_normalizedSum_sq_le_weylAverage {P : ℝ} (hP : 1 ≤ P)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hw : CubeSupported w) (α : ℝ) :
    ‖normalizedSum F w P α‖^2 ≤ (30 : ℝ)^n *
      𝔼 h ∈ latticeBox n P, ‖normalizedSum (dilatedDifference 1 h F) (differencedWeight w P 1 h) P α‖ := by
  have hp : 0 < P := zero_lt_one.trans_le hP
  have hh := exponentialSum_differencing (n := n) (P := P) (H := P) (m := 1)
    hP hp (by norm_num) (by norm_num) F w hw α
  simp only [Int.cast_one, one_mul, ← norm_normalizedSum_eq_div hp] at hh
  have hsub : differencingDirections n P ⊆ latticeBox n P := by
    intro x hx
    exact mem_latticeBox_iff_abs.mpr (fun i => (abs_differencingDirection_lt hp hx i).le)
  let V (h : Fin n → ℤ) := ‖normalizedSum (dilatedDifference 1 h F) (differencedWeight w P 1 h) P α‖
  have hc : (((10 : ℝ)^n / P^n) * ((latticeBox n P).card : ℝ)) ≤ (30 : ℝ)^n := calc
    _ ≤ ((10 : ℝ)^n / P^n) * (3*P)^n :=
      mul_le_mul_of_nonneg_left (card_latticeBox_between n hP).2 (by positivity)
    _ = _ := by
      rw [mul_pow, ← mul_assoc, div_mul_eq_mul_div, ← mul_pow]
      norm_num
      exact div_mul_cancel₀ _ (pow_ne_zero _ hp.ne')
  calc
    _ ≤ ((10 : ℝ)^n / P^n) * ∑ h ∈ differencingDirections n P, V h := hh
    _ ≤ ((10 : ℝ)^n / P^n) * ∑ h ∈ latticeBox n P, V h :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)) (by positivity)
    _ = (((10 : ℝ)^n / P^n) * ((latticeBox n P).card : ℝ)) *
        (𝔼 h ∈ latticeBox n P, V h) := by rw [mul_assoc, Finset.card_mul_expect]
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Finset.expect_nonneg fun _ _ => norm_nonneg _)

private theorem pow_expect_le_expect_pow {T : Type*} (s : Finset T) (hs : s.Nonempty)
    (g : T → ℝ) (hg : ∀ x ∈ s, 0 ≤ g x) (k : ℕ) :
    (𝔼 x ∈ s, g x)^k ≤ 𝔼 x ∈ s, (g x)^k := by
  let w : ℝ := (s.card : ℝ)⁻¹
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  have h := Real.pow_arith_mean_le_arith_mean_pow s (fun _ => w) g
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) (by simp [w, nsmul_eq_mul, hcard]) hg k
  simp only [w, Finset.expect_eq_sum_div_card, div_eq_inv_mul, ← Finset.mul_sum] at h ⊢
  exact h

private theorem expect_weylShiftBox_succ {k : ℕ} (P : ℝ)
    (g : (Fin (k+1) → Fin n → ℤ) → ℝ) :
    (𝔼 t ∈ weylShiftBox n (k+1) P, g t) =
      𝔼 h ∈ latticeBox n P, 𝔼 t ∈ weylShiftBox n k P, g (Fin.cons h t) := by
  let e := Fin.consEquiv (fun _ : Fin (k+1) => Fin n → ℤ)
  have he (x : (Fin n → ℤ) × (Fin k → Fin n → ℤ)) :
      x ∈ (latticeBox n P).product (weylShiftBox n k P) ↔ e x ∈ weylShiftBox n (k+1) P := by
    have hx : x ∈ (latticeBox n P).product (weylShiftBox n k P) ↔
        x.1 ∈ latticeBox n P ∧ x.2 ∈ weylShiftBox n k P := Finset.mem_product
    rw [hx]
    change _ ↔ Fin.cons x.1 x.2 ∈ Fintype.piFinset (fun _ : Fin (k+1) => latticeBox n P)
    rw [Fin.mem_piFinset_iff_zero_tail]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rfl
  calc
    _ = 𝔼 x ∈ (latticeBox n P).product (weylShiftBox n k P), g (e x) :=
      (Finset.expect_equiv e he (fun _ _ => rfl)).symm
    _ = _ := Finset.expect_product _ _ _

/-- The repeated Cauchy bound (3.5), first as an average of the actual normalized
terminal magnitudes on the Cartesian product of shift boxes. -/
theorem norm_normalizedSum_pow_le_weylAverage (k : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hw : CubeSupported w) (α : ℝ) :
    ‖normalizedSum F w P α‖^(2^k : ℕ) ≤ ((30 : ℝ)^n)^(2^k-1 : ℕ) *
      (𝔼 t ∈ weylShiftBox n k P,
        ‖normalizedSum (weylDifference (List.ofFn t) F) (weylDifferencedWeight (List.ofFn t) w P) P α‖) := by
  let C : ℝ := 30^n
  have hC : 0 ≤ C := by positivity
  have hbox : (latticeBox n P).Nonempty := ⟨0, mem_latticeBox_iff_abs.mpr (by
    simp only [Pi.zero_apply, Int.cast_zero, abs_zero]
    exact fun _ => zero_le_one.trans hP)⟩
  induction k generalizing F w with
  | zero =>
    have hs : (weylShiftBox n 0 P).Nonempty := ⟨Fin.elim0, Fintype.mem_piFinset.mpr
      (fun i => i.elim0)⟩
    simp [hs]
  | succ k ih =>
    let B (h : Fin n → ℤ) : ℝ :=
      ‖normalizedSum (dilatedDifference 1 h F) (differencedWeight w P 1 h) P α‖
    let T (h : Fin n → ℤ) (t : Fin k → Fin n → ℤ) : ℝ :=
      ‖normalizedSum (weylDifference (List.ofFn t) (dilatedDifference 1 h F))
        (weylDifferencedWeight (List.ofFn t) (differencedWeight w P 1 h) P) P α‖
    have hstep : ‖normalizedSum F w P α‖^2 ≤ C * (𝔼 h ∈ latticeBox n P, B h) :=
      norm_normalizedSum_sq_le_weylAverage hP F w hw α
    have hsupport (h : Fin n → ℤ) : CubeSupported (differencedWeight w P 1 h) := by
      simpa using weylDifferencedWeight_cubeSupported [h] w P hw
    have hrec (h : Fin n → ℤ) : B h^(2^k : ℕ) ≤ C^(2^k-1 : ℕ) *
        (𝔼 t ∈ weylShiftBox n k P, T h t) :=
      ih (dilatedDifference 1 h F) (differencedWeight w P 1 h) (hsupport h)
    rw [show (2 : ℕ)^(k+1) = 2 * 2^k by rw [pow_succ'], pow_mul]
    calc
      _ ≤ (C * (𝔼 h ∈ latticeBox n P, B h))^(2^k : ℕ) :=
        pow_le_pow_left₀ (by positivity) hstep _
      _ = C^(2^k : ℕ) * (𝔼 h ∈ latticeBox n P, B h)^(2^k : ℕ) := mul_pow _ _ _
      _ ≤ C^(2^k : ℕ) * (𝔼 h ∈ latticeBox n P, B h^(2^k : ℕ)) :=
        mul_le_mul_of_nonneg_left (pow_expect_le_expect_pow _ hbox B
          (fun _ _ => norm_nonneg _) _) (pow_nonneg hC _)
      _ ≤ C^(2^k : ℕ) * (𝔼 h ∈ latticeBox n P, C^(2^k-1 : ℕ) *
          (𝔼 t ∈ weylShiftBox n k P, T h t)) :=
        mul_le_mul_of_nonneg_left (Finset.expect_le_expect (fun h _ => hrec h)) (pow_nonneg hC _)
      _ = _ := by
        change _ = C^(2 * 2^k - 1 : ℕ) * _
        rw [← Finset.mul_expect (latticeBox n P) (fun h => 𝔼 t ∈ weylShiftBox n k P, T h t),
          ← mul_assoc, ← pow_add,
          show (2 : ℕ)^k + (2^k-1) = 2 * 2^k - 1 by have := pow_pos (by norm_num : 0 < (2 : ℕ)) k; omega,
          expect_weylShiftBox_succ]
        simp only [T, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, weylDifference_cons, weylDifferencedWeight_cons]

/-- Repeated Weyl differencing in the paper's sum normalization. The
Cartesian box can be used in place of the smaller strict difference box,
since the magnitudes are nonnegative. -/
theorem norm_normalizedSum_pow_le_weylSum (k : ℕ) {P : ℝ} (hP : 1 ≤ P)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (hw : CubeSupported w) (α : ℝ) :
    ‖normalizedSum F w P α‖^(2^k : ℕ) ≤ ((30 : ℝ)^n)^(2^k-1 : ℕ) *
      ((∑ t ∈ weylShiftBox n k P,
        ‖normalizedSum (weylDifference (List.ofFn t) F) (weylDifferencedWeight (List.ofFn t) w P) P α‖) /
        P^(n*k)) := by
  refine (norm_normalizedSum_pow_le_weylAverage k hP F w hw α).trans
    (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Finset.expect_eq_sum_div_card, card_weylShiftBox, Nat.cast_pow, pow_mul]
  apply div_le_div_of_nonneg_left (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · positivity
  · exact pow_le_pow_left₀ (by positivity) (card_latticeBox_between n hP).1 _


end

end Birch
