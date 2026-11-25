import Birch.WeylLinearExponential
import Birch.NormalizedDifference
import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Partial summation for linear lattice phases

Coordinate by coordinate, Abel summation uses one bounded derivative of the
smooth weight. The interval length and the spacing of its scaled lattice
points compensate each other.
-/

open Finset Set
open scoped BigOperators ContDiff

namespace Birch

noncomputable section

private theorem linearPhaseBound_mono {L M t : ℝ} (h : L ≤ M) :
    linearPhaseBound L t ≤ linearPhaseBound M t := by
  unfold linearPhaseBound
  split_ifs
  · exact h
  · exact min_le_min h le_rfl

private theorem abel_sum_vector {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (g : ℕ → ℂ) (v : ℕ → Y) (N : ℕ) :
    (∑ m ∈ range N, g m • v m) =
      (∑ m ∈ range N, g m) • v (N-1) -
        ∑ m ∈ range (N-1), (∑ l ∈ range (m+1), g l) • (v (m+1) - v m) := by
  cases N with
  | zero => simp
  | succ N =>
    simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ (fun m => g m • v m) (N+1), ih,
        sum_range_succ g (N+1),
        sum_range_succ (fun m => (∑ l ∈ range (m+1), g l) • (v (m+1) - v m)) N]
      simp only [add_smul, smul_sub]
      abel

private theorem norm_abel_affine_sum {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (v : ℕ → Y) (a : ℤ) (t : ℝ) (N : ℕ) {C D : ℝ}
    (hv : ‖v (N-1)‖ ≤ C) (hstep : ∀ m < N-1, ‖v (m+1) - v m‖ ≤ D) :
    ‖∑ m ∈ range N, phase (((a : ℝ) + (m : ℝ)) * t) • v m‖ ≤
      (C + ((N-1 : ℕ) : ℝ)*D) * linearPhaseBound N t := by
  let g (m : ℕ) := phase (((a : ℝ) + (m : ℝ)) * t)
  have hGN (M : ℕ) (hMN : M ≤ N) : ‖∑ m ∈ range M, g m‖ ≤ linearPhaseBound N t := by
    have h := norm_affine_phase_range_le t 0 a M
    exact (by simpa only [zero_add] using h : ‖∑ m ∈ range M, g m‖ ≤ linearPhaseBound M t).trans
      (linearPhaseBound_mono (by exact_mod_cast hMN))
  change ‖∑ m ∈ range N, g m • v m‖ ≤ _
  rw [abel_sum_vector]
  calc
    _ ≤ ‖(∑ m ∈ range N, g m) • v (N-1)‖ +
          ∑ m ∈ range (N-1), ‖(∑ l ∈ range (m+1), g l) • (v (m+1)-v m)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ linearPhaseBound N t * C + ∑ m ∈ range (N-1), linearPhaseBound N t * D := by
      simp only [norm_smul (α := ℂ)]
      refine add_le_add (mul_le_mul (hGN N le_rfl) hv (norm_nonneg _)
        (linearPhaseBound_nonneg (by positivity) _)) (sum_le_sum fun m hm => ?_)
      exact mul_le_mul (hGN (m+1) (by have := mem_range.mp hm; omega)) (hstep m (mem_range.mp hm))
        (norm_nonneg _) (linearPhaseBound_nonneg (by positivity) _)
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

private lemma weylSmoothOrder_le (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
private lemma weylSmoothOrder_lt (j : ℕ) : (j : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private def affineSumOperator (P : ℝ) (a : ℤ) (N : ℕ) (v : X) (t : ℝ)
    (f : X → ℂ) (x : X) : ℂ :=
  ∑ m ∈ range N, phase (((a : ℝ) + (m : ℝ)) * t) • f (x + (((a : ℝ) + (m : ℝ))/P) • v)

private theorem affineSumOperator_contDiff {P : ℝ} {a : ℤ} {N : ℕ} {v : X} {t : ℝ}
    {f : X → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (affineSumOperator P a N v t f) := by
  unfold affineSumOperator
  let f' (m : ℕ) (x : X) := phase (((a : ℝ) + (m : ℝ)) * t) •
    f (x + (((a : ℝ) + (m : ℝ))/P) • v)
  change ContDiff ℝ ∞ (fun x => ∑ m ∈ range N, f' m x)
  have h (m : ℕ) : ContDiff ℝ ∞ (f' m) := by
    unfold f'
    exact (hf.comp (contDiff_id.add contDiff_const)).const_smul _
  simpa only [Finset.sum_apply] using (ContDiff.sum (s := range N) (fun m _ => h m))

private theorem affineSumOperator_derivatives {P : ℝ} (hP : 0 < P) {a : ℤ} {N : ℕ}
    {v : X} (hv : ‖v‖ ≤ 1) {t : ℝ} {f : X → ℂ} (hf : ContDiff ℝ ∞ f)
    {k : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ j ≤ k+1, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (affineSumOperator P a N v t f) x‖ ≤
      (C * (1 + ((N-1 : ℕ) : ℝ)/P)) * linearPhaseBound N t := by
  intro j hj x
  let x' (m : ℕ) := x + (((a : ℝ) + (m : ℝ))/P) • v
  let b (m : ℕ) := iteratedFDeriv ℝ j f (x' m)
  have hder : ∀ y ∈ (univ : Set X), DifferentiableAt ℝ (iteratedFDeriv ℝ j f) y :=
    fun y _ => (hf.differentiable_iteratedFDeriv (weylSmoothOrder_lt j)).differentiableAt
  have hn : ∀ y ∈ (univ : Set X), ‖fderiv ℝ (iteratedFDeriv ℝ j f) y‖ ≤ C := by
    intro y _
    rw [norm_fderiv_iteratedFDeriv]
    exact hB (j+1) (by omega) y
  have hstep (m : ℕ) : ‖b (m+1) - b m‖ ≤ C/P := by
    have H := (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
      hder hn (mem_univ (x' m)) (mem_univ (x' (m+1)))
    have hd : x' (m+1) - x' m = P⁻¹ • v := by
      simp only [x', Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      field_simp
      ring
    rw [hd, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hP.le)] at H
    refine H.trans ?_
    rw [div_eq_mul_inv, ← mul_assoc]
    exact mul_le_of_le_one_right (mul_nonneg hC (inv_nonneg.mpr hP.le)) hv
  have hterm (m : ℕ) (_hm : m ∈ range N) :
      ContDiffAt ℝ j
        (fun y => phase (((a : ℝ) + (m : ℝ)) * t) • f (y + (((a : ℝ)+(m : ℝ))/P) • v)) x :=
    (((hf.comp (contDiff_id.add contDiff_const)).const_smul _).of_le (weylSmoothOrder_le j)).contDiffAt
  unfold affineSumOperator
  rw [iteratedFDeriv_fun_sum_apply hterm]
  have hrew (m : ℕ) :
      iteratedFDeriv ℝ j
          (fun y => phase (((a : ℝ) + (m : ℝ)) * t) • f (y + (((a : ℝ)+(m : ℝ))/P) • v)) x =
        phase (((a : ℝ) + (m : ℝ)) * t) • b m := by
    let g (y : X) := f (y + (((a : ℝ)+(m : ℝ))/P) • v)
    have hg : ContDiffAt ℝ j g x := by
      have hh : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
      exact (hh.of_le (weylSmoothOrder_le j)).contDiffAt
    change iteratedFDeriv ℝ j (fun y => phase (((a : ℝ) + (m : ℝ)) * t) • g y) x = _
    rw [iteratedFDeriv_const_smul_apply' hg]
    dsimp [g, b, x']
    rw [iteratedFDeriv_comp_add_right]
  simp_rw [hrew]
  refine (norm_abel_affine_sum b a t N (hB j (by omega) _) (fun m _ => hstep m)).trans_eq ?_
  congr 1
  ring

private def affineGridSum (P : ℝ) (a : ℤ) (N : ℕ) {k : ℕ} (v : Fin k → X) (t : Fin k → ℝ)
    (f : X → ℂ) (x : X) : ℂ :=
  ∑ m : Fin k → Fin N,
    phase (∑ i, ((a : ℝ) + (m i : ℕ)) * t i) *
      f (x + ∑ i, (((a : ℝ) + (m i : ℕ))/P) • v i)

private theorem affineGridSum_succ (P : ℝ) (a : ℤ) (N : ℕ) {k : ℕ}
    (v : Fin (k+1) → X) (t : Fin (k+1) → ℝ) (f : X → ℂ) (x : X) :
    affineGridSum P a N v t f x =
      affineGridSum P a N (fun i => v i.succ) (fun i => t i.succ)
        (affineSumOperator P a N (v 0) (t 0) f) x := by
  let e : (Fin N × (Fin k → Fin N)) ≃ (Fin (k+1) → Fin N) :=
    Fin.consEquiv (fun _ : Fin (k+1) => Fin N)
  let G (m : Fin (k+1) → Fin N) := phase (∑ i, ((a : ℝ) + (m i : ℕ)) * t i) *
    f (x + ∑ i, (((a : ℝ) + (m i : ℕ))/P) • v i)
  change (∑ m, G m) = _
  rw [← Equiv.sum_comp e G, Fintype.sum_prod_type, Finset.sum_comm, affineGridSum]
  apply Finset.sum_congr rfl
  intro m _
  rw [affineSumOperator, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m₀ _
  change G (Fin.cons m₀ m) = _
  simp only [G, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, smul_eq_mul, phase_add]
  rw [← add_assoc, add_right_comm, mul_left_comm, mul_assoc]

private theorem norm_affineGridSum_le {P : ℝ} (hP : 0 < P) (a : ℤ) (N : ℕ)
    {k : ℕ} (v : Fin k → X) (hv : ∀ i, ‖v i‖ ≤ 1) (t : Fin k → ℝ)
    (f : X → ℂ) (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C) (x : X) :
    ‖affineGridSum P a N v t f x‖ ≤ C * (1 + ((N-1 : ℕ) : ℝ)/P)^k *
      ∏ i, linearPhaseBound N (t i) := by
  induction k generalizing f C with
  | zero =>
    simpa [affineGridSum, norm_phase, norm_iteratedFDeriv_zero] using hB 0 le_rfl x
  | succ k ih =>
    rw [affineGridSum_succ]
    refine (ih _ (fun i => hv i.succ) _ _ (affineSumOperator_contDiff hf) (by
      exact mul_nonneg (mul_nonneg hC (by positivity)) (linearPhaseBound_nonneg (by positivity) _))
      (affineSumOperator_derivatives hP (hv 0) hf hC hB)).trans_eq ?_
    rw [Fin.prod_univ_succ, pow_succ]
    ring

/-- Number of integer coordinates in the closed interval of radius `P`. -/
def weylIntervalLength (P : ℝ) : ℕ := (2*⌊P⌋+1).toNat

private theorem weylIntervalLength_sub_one_le {P : ℝ} (hP : 0 ≤ P) :
    ((weylIntervalLength P - 1 : ℕ) : ℝ) ≤ 2*P := by
  have hp : 0 ≤ ⌊P⌋ := Int.floor_nonneg.mpr hP
  have h : ((weylIntervalLength P - 1 : ℕ) : ℤ) = 2*⌊P⌋ := by
    unfold weylIntervalLength
    omega
  have hr : ((weylIntervalLength P - 1 : ℕ) : ℝ) = 2*(⌊P⌋ : ℝ) := by exact_mod_cast h
  rw [hr]
  linarith [Int.floor_le P]

/-- For P at least one the integer interval length is at most `3 * P`. -/
theorem weylIntervalLength_le_three {P : ℝ} (hP : 1 ≤ P) :
    (weylIntervalLength P : ℝ) ≤ 3*P := by
  have hp : 0 ≤ ⌊P⌋ := Int.floor_nonneg.mpr (zero_le_one.trans hP)
  have hN : (weylIntervalLength P : ℤ) = 2*⌊P⌋+1 :=
    Int.toNat_of_nonneg (by omega)
  have hR : (weylIntervalLength P : ℝ) = 2*(⌊P⌋ : ℝ)+1 := by exact_mod_cast hN
  rw [hR]
  linarith [Int.floor_le P]

private theorem latticeBox_sum_eq_grid {n : ℕ} {P : ℝ} (hP : 0 ≤ P)
    (g : (Fin n → ℤ) → ℂ) :
    (∑ x ∈ latticeBox n P, g x) =
      ∑ m : Fin n → Fin (weylIntervalLength P), g (fun i => -⌊P⌋ + (m i : ℕ)) := by
  classical
  let a := ⌊P⌋
  let N := weylIntervalLength P
  have ha : 0 ≤ a := Int.floor_nonneg.mpr hP
  have hN : (N : ℤ) = 2*a+1 := Int.toNat_of_nonneg (show 0 ≤ 2*a+1 by omega)
  symm
  refine Finset.sum_bij (fun m _ i => -a + (m i : ℕ)) ?_ ?_ ?_ ?_
  · intro m _
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hi := (m i).isLt
    omega
  · intro m _ z _ h
    funext i
    have hi := congrFun h i
    apply Fin.ext
    omega
  · intro x hx
    have hx' (i : Fin n) : -a ≤ x i ∧ x i ≤ a := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hx) i)
    let m (i : Fin n) : Fin N := ⟨(x i+a).toNat, by have := hx' i; omega⟩
    refine ⟨m, mem_univ _, ?_⟩
    funext i
    have := hx' i
    change -a + ((x i+a).toNat : ℤ) = x i
    omega
  · intro m _
    rfl

/-- Partial summation for a smooth real weight and an affine phase on the
integer box, uniformly in the constant and all linear frequencies. -/
theorem norm_weighted_affine_phase_box_le {n : ℕ} {P : ℝ} (hP : 0 < P)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j w x‖ ≤ C)
    (t : Fin n → ℝ) (c : ℝ) :
    ‖∑ x ∈ latticeBox n P, (w (scaledPoint P x) : ℂ) * phase (c + ∑ i, (x i : ℝ) * t i)‖ ≤
      C * (3 : ℝ)^n * ∏ i, linearPhaseBound (weylIntervalLength P) (t i) := by
  classical
  let a : ℤ := -⌊P⌋
  let N := weylIntervalLength P
  let v (i : Fin n) : Fin n → ℝ := Pi.single i 1
  let f (x : Fin n → ℝ) : ℂ := w x
  have hv (i : Fin n) : ‖v i‖ ≤ 1 := by simp [v, Pi.norm_single]
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hw
  have hfb (j : ℕ) (hj : j ≤ n) (x : Fin n → ℝ) : ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    have H := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (x := x) hw.contDiffAt (weylSmoothOrder_le j)
    rw [Complex.ofRealCLM_norm, one_mul] at H
    exact H.trans (hB j hj x)
  have he : (∑ x ∈ latticeBox n P, (w (scaledPoint P x) : ℂ) *
      phase (c + ∑ i, (x i : ℝ) * t i)) = phase c * affineGridSum P a N v t f 0 := by
    rw [latticeBox_sum_eq_grid hP.le, affineGridSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hm : scaledPoint P (fun i => a + (m i : ℕ)) =
        ∑ i, (((a : ℝ) + (m i : ℕ))/P) • v i := by
      funext i
      simp only [scaledPoint, Int.cast_add, Int.cast_natCast, Finset.sum_apply, Pi.smul_apply, v,
        Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ i, ite_eq_left (Finset.mem_univ i)]
    simp only [← hm, zero_add, f, Int.cast_add, Int.cast_natCast, phase_add, a]
    ring
  rw [he, norm_mul, norm_phase, one_mul]
  have hL : 1 + ((N-1 : ℕ) : ℝ)/P ≤ 3 := by
    have h := (div_le_iff₀ hP).mpr (weylIntervalLength_sub_one_le hP.le)
    linarith
  exact (norm_affineGridSum_le hP a N v hv t f hf hC hfb 0).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hL n) hC)
      (prod_nonneg fun i _ => linearPhaseBound_nonneg (by positivity) (t i)))

end
end Birch
