import Birch.DifferencingChain
import Birch.Metric
import Birch.LatticeSummable
import Birch.RealOscillationDecay
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform derivatives of the rescaled differenced phase

A normalized step is the divided difference along a vector of sup norm at most
one. The mean value estimate for each iterated derivative bounds it by the next
order derivative before differencing, on a ball enlarged by one.
-/

open Finset Set
open scoped BigOperators ContDiff Topology

namespace Birch

noncomputable section

private lemma smoothOrder_le (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private lemma smoothOrder_lt (j : ℕ) : (j : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)

/-- A common norm bound for derivatives through order `N` on a closed ball. -/
def DerivativesBoundedOnBall {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (N : ℕ) (R C : ℝ) : Prop :=
  ∀ j ≤ N, ∀ x, ‖x‖ ≤ R → ‖iteratedFDeriv ℝ j f x‖ ≤ C

/-- A finite collection of derivative orders is bounded on every fixed closed ball. -/
theorem exists_derivativesBoundedOnBall {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [ProperSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : X → Y}
    (hf : ContDiff ℝ ∞ f) (N : ℕ) (R : ℝ) :
    ∃ C > 0, DerivativesBoundedOnBall f N R C := by
  have hb (j : ℕ) : ∃ B ≥ 0, ∀ x, ‖x‖ ≤ R → ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
    have hc : Continuous (fun x => ‖iteratedFDeriv ℝ j f x‖) :=
      (hf.continuous_iteratedFDeriv (smoothOrder_le j)).norm
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : X) R).bddAbove_image hc.continuousOn
    refine ⟨max B 0, le_max_right _ _, fun x hx => (hB ?_).trans (le_max_left _ _)⟩
    exact ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩
  choose B hBnonneg hB using hb
  refine ⟨1 + ∑ j ∈ range (N+1), B j, add_pos_of_pos_of_nonneg zero_lt_one
    (sum_nonneg (fun j _ => hBnonneg j)), ?_⟩
  intro j hj x hx
  refine (hB j x hx).trans ?_
  exact (single_le_sum (fun i _ => hBnonneg i) (mem_range.mpr (Nat.lt_succ_iff.mpr hj))).trans (by linarith)

/-- A normalized real divided difference at a nonzero step. -/
def normalizedDifference {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (a : ℝ) (v : X) (f : X → Y) : X → Y :=
  fun x => a⁻¹ • (f (x + a • v) - f x)

/-- A normalized difference costs one derivative with no small-step loss. -/
theorem derivativesBoundedOnBall_normalizedDifference {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} (hf : ContDiff ℝ ∞ f) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1)
    {v : X} (hv : ‖v‖ ≤ 1) {N : ℕ} {R C : ℝ} (hC : 0 ≤ C)
    (hB : DerivativesBoundedOnBall f (N+1) (R+1) C) :
    DerivativesBoundedOnBall (normalizedDifference a v f) N R C := by
  intro j hj x hx
  let g : X → Y := fun y => f (y + a • v) - f y
  have hshift : ContDiff ℝ ∞ (fun y => f (y + a • v)) := hf.comp (contDiff_id.add contDiff_const)
  have hg : ContDiff ℝ ∞ g := hshift.sub hf
  have hdiff : ‖iteratedFDeriv ℝ j f (x + a • v) - iteratedFDeriv ℝ j f x‖ ≤ C * a := by
    let U := Metric.closedBall (0 : X) (R+1)
    have hxU : x ∈ U := by simpa [U, Metric.mem_closedBall, dist_zero_right] using (show ‖x‖ ≤ R+1 by linarith)
    have hxa : ‖a • v‖ ≤ a := by rw [norm_smul, Real.norm_of_nonneg ha.le]; exact mul_le_of_le_one_right ha.le hv
    have hyU : x + a • v ∈ U := by
      have H := (norm_add_le x (a • v)).trans (add_le_add hx (hxa.trans ha'))
      simpa only [U, Metric.mem_closedBall, dist_zero_right] using H
    have hder : ∀ y ∈ U, DifferentiableAt ℝ (iteratedFDeriv ℝ j f) y :=
      fun y _ => (hf.differentiable_iteratedFDeriv (smoothOrder_lt j)).differentiableAt
    have hn : ∀ y ∈ U, ‖fderiv ℝ (iteratedFDeriv ℝ j f) y‖ ≤ C := by
      intro y hy
      rw [norm_fderiv_iteratedFDeriv]
      apply hB (j+1) (by omega) y
      simpa only [U, Metric.mem_closedBall, dist_zero_right] using hy
    refine ((convex_closedBall (0 : X) (R+1)).norm_image_sub_le_of_norm_fderiv_le hder hn hxU hyU).trans ?_
    rw [add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left hxa hC
  change ‖iteratedFDeriv ℝ j (fun y => a⁻¹ • g y) x‖ ≤ C
  rw [iteratedFDeriv_const_smul_apply' ((hg.of_le (smoothOrder_le j)).contDiffAt), norm_smul]
  change ‖a⁻¹‖ * ‖iteratedFDeriv ℝ j ((fun y => f (y + a • v)) - f) x‖ ≤ C
  rw [iteratedFDeriv_sub_apply (hshift.of_le (smoothOrder_le j)).contDiffAt
    (hf.of_le (smoothOrder_le j)).contDiffAt, iteratedFDeriv_comp_add_right]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
  exact (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr ha.le)).trans_eq (by field_simp)


private theorem evalForm_mul_dilatedDifference_real {n : ℕ} (g : IntForm n) (m : ℤ)
    (u : Fin n → ℤ) (x : Fin n → ℝ) :
    (m : ℝ) * evalForm (dilatedDifference m u g) x =
      evalForm g (x + (m : ℝ) • latticeVector u) - evalForm g x := by
  let ev : IntForm n →ₐ[ℤ] ℝ := MvPolynomial.aeval x
  have h := congrArg (fun p => ev p) (mul_dilatedDifference m u g)
  change ev (MvPolynomial.C m * dilatedDifference m u g) =
    ev (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (m * u i)) g - g) at h
  rw [map_mul, map_sub, MvPolynomial.comp_aeval_apply] at h
  simp only [ev, MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_add, map_mul] at h
  have hmap : algebraMap ℤ ℝ = Int.castRingHom ℝ := Subsingleton.elim _ _
  have hv : x + (m : ℝ) • latticeVector u = fun i => x i + (m : ℝ) * (u i : ℝ) := rfl
  rw [hv]
  simpa only [MvPolynomial.aeval_def, hmap, Int.coe_castRingHom, evalForm, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, latticeVector] using h

private def phaseScale (d k : ℕ) (P Q : ℝ) (i : ℕ) : ℝ :=
  P^(d-i) * ∏ j ∈ range i, differencingHeight k Q j

private theorem phaseScale_pos {d k i : ℕ} {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) :
    0 < phaseScale d k P Q i :=
  mul_pos (pow_pos hP _) (prod_pos (fun _ _ => Real.rpow_pos_of_pos hQ _))

private def normalizedChainForm {n : ℕ} (d k : ℕ) (P Q : ℝ)
    (t : ℕ → PolynomialDifferencingState n) (i : ℕ) (x : Fin n → ℝ) : ℝ :=
  (phaseScale d k P Q i)⁻¹ * evalForm (t i).form (P • x)

private theorem normalizedChainForm_contDiff {n : ℕ} (d k : ℕ) (P Q : ℝ)
    (t : ℕ → PolynomialDifferencingState n) (i : ℕ) :
    ContDiff ℝ ∞ (normalizedChainForm d k P Q t i) :=
  contDiff_const.mul ((contDiff_evalForm (t i).form).comp
    (show ContDiff ℝ ∞ (fun x : Fin n → ℝ => P • x) by fun_prop))

private theorem normalizedChainForm_succ {n d k : ℕ} {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (m : ℕ → ℤ) (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ)
    (i : ℕ) (hi : i < d) (hm : 0 < m i) (ht : t (i+1) = (t i).step P (m i) (u i)) :
    normalizedChainForm d k P Q t (i+1) =
      normalizedDifference (((m i : ℤ) : ℝ) * differencingHeight k Q i / P)
        ((differencingHeight k Q i)⁻¹ • latticeVector (u i)) (normalizedChainForm d k P Q t i) := by
  let H := differencingHeight k Q i
  let a := (m i : ℝ) * H / P
  let v := H⁻¹ • latticeVector (u i)
  have hH : 0 < H := Real.rpow_pos_of_pos hQ _
  have hmR : 0 < (m i : ℝ) := by exact_mod_cast hm
  have ha : 0 < a := div_pos (mul_pos hmR hH) hP
  let S := phaseScale d k P Q i
  let S' := phaseScale d k P Q (i+1)
  have hS : 0 < S := phaseScale_pos hP hQ
  have hS' : 0 < S' := phaseScale_pos hP hQ
  have hscale : (m i : ℝ)*S' = a*S := by
    dsimp [S, S', phaseScale, a, H]
    rw [prod_range_succ, show d-i = d-(i+1)+1 by omega, pow_succ]
    field_simp
  funext x
  have htrans : P • (x + a • v) = P • x + (m i : ℝ) • latticeVector (u i) := by
    rw [smul_add, smul_smul]
    dsimp [v]
    rw [smul_smul]
    congr 1
    dsimp [a]
    field_simp
  have hg : (m i : ℝ) * evalForm (t (i+1)).form (P • x) =
      evalForm (t i).form (P • (x + a • v)) - evalForm (t i).form (P • x) := by
    rw [htrans, ht]
    exact evalForm_mul_dilatedDifference_real (t i).form (m i) (u i) (P • x)
  change S'⁻¹ * evalForm (t (i+1)).form (P • x) = a⁻¹ •
    (S⁻¹ * evalForm (t i).form (P • (x + a • v)) - S⁻¹ * evalForm (t i).form (P • x))
  have hcancel : a⁻¹ * S⁻¹ * (m i : ℝ) = S'⁻¹ := by
    field_simp
    nlinarith only [hscale]
  rw [smul_eq_mul, ← mul_sub, ← hg, ← mul_assoc a⁻¹, ← mul_assoc (a⁻¹ * S⁻¹), hcancel]

private theorem dyadicHeightReciprocalSum (k : ℕ) :
    (∑ i : Fin k, 1 / (2 : ℝ) ^ (k - 1 - i.val)) = 2 - 2 / (2 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    have hrest : (∑ i : Fin k, 1 / (2 : ℝ) ^ (k+1-1-i.succ.val)) =
        ∑ i : Fin k, 1 / (2 : ℝ) ^ (k-1-i.val) := by
      apply sum_congr rfl
      intro i _
      simp only [Fin.val_succ]
      congr 2
      omega
    rw [hrest, ih, pow_succ]
    simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero]
    have ht : (2 : ℝ)^k ≠ 0 := by positivity
    field_simp
    ring

private theorem prod_differencingHeights {k : ℕ} {Q : ℝ} (hQ : 0 < Q) :
    (∏ j ∈ range k, differencingHeight k Q j) = Q ^ (2 - 2/(2 : ℝ)^k) := by
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [differencingHeight, ← Real.rpow_sum_of_pos hQ, dyadicHeightReciprocalSum]

/-- The near-resonance part of the terminal polynomial phase has bounded
seminorms on each fixed ball, uniformly over the scales and every admissible chain. -/
theorem uniform_terminal_phase_derivatives {n d r : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) (hrd : r ≤ d) (N : ℕ) (R : ℝ) :
    ∃ C > 0, ∀ (P Q : ℝ), 0 < P → 0 < Q → ∀ (m : ℕ → ℤ),
      (∀ i < d-r, 0 < m i ∧ (m i : ℝ)*differencingHeight (d-r) Q i ≤ P) →
      ∀ (w : (Fin n → ℝ) → ℝ) (α : ℝ) (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
        IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
        ∀ β : ℝ, |β| ≤ completionRadius d r P Q →
        DerivativesBoundedOnBall (fun y => β * evalForm (t (d-r)).form (P • y)) N R C := by
  let k := d-r
  obtain ⟨C, hC, hbase⟩ := exists_derivativesBoundedOnBall (contDiff_evalForm F) (N+k) (R+k)
  refine ⟨C, hC, ?_⟩
  intro P Q hP hQ m hm w α t u ht β hβ
  let G := normalizedChainForm d k P Q t
  have hG (i : ℕ) (hi : i ≤ k) : DerivativesBoundedOnBall (G i) (N+(k-i)) (R+(k-i : ℕ)) C := by
    induction i with
    | zero =>
      have hzero : G 0 = (evalForm F : (Fin n → ℝ) → ℝ) := by
        funext x
        simp only [G, normalizedChainForm, phaseScale, ht.1, Nat.sub_zero, prod_range_zero, mul_one]
        change (P^d)⁻¹ * evalForm F (fun i => P * x i) = evalForm F x
        rw [evalForm_scale hF]
        exact inv_mul_cancel_left₀ (pow_ne_zero _ hP.ne') _
      simpa only [hzero, Nat.sub_zero] using hbase
    | succ i ih =>
      have hi' : i < k := by omega
      let H := differencingHeight k Q i
      let a := (m i : ℝ)*H/P
      let v := H⁻¹ • latticeVector (u i)
      have hH : 0 < H := Real.rpow_pos_of_pos hQ _
      have hmR : 0 < (m i : ℝ) := by exact_mod_cast (hm i hi').1
      have ha : 0 < a := div_pos (mul_pos hmR hH) hP
      have ha' : a ≤ 1 := (div_le_one hP).mpr (hm i hi').2
      have hu : ‖latticeVector (u i)‖ ≤ H := by
        apply (pi_norm_le_iff_of_nonneg hH.le).mpr
        intro j
        simpa only [latticeVector, Real.norm_eq_abs] using (abs_differencingDirection_lt hH (ht.2 i hi').1 j).le
      have hv : ‖v‖ ≤ 1 := by
        dsimp [v]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hH.le), inv_mul_eq_div]
        exact (div_le_one hH).mpr hu
      have he : k-i = (k-(i+1))+1 := by omega
      have hb := ih (by omega)
      rw [he, ← Nat.add_assoc, Nat.cast_add, Nat.cast_one, ← add_assoc] at hb
      rw [show G (i+1) = normalizedDifference a v (G i) from
        normalizedChainForm_succ hP hQ m t u i (by dsimp [k] at hi'; omega) (hm i hi').1 (ht.2 i hi').2]
      exact derivativesBoundedOnBall_normalizedDifference (normalizedChainForm_contDiff d k P Q t i)
        ha ha' hv hC.le hb
  have hbound : DerivativesBoundedOnBall (G k) N R C := by
    simpa only [Nat.sub_self, Nat.add_zero, Nat.cast_zero, add_zero] using hG k le_rfl
  have hscale : phaseScale d k P Q k = P^r * Q ^ (dilationRho d r) := by
    unfold phaseScale dilationRho
    rw [prod_differencingHeights hQ, show d-k=r by dsimp [k]; omega]
  have hspos : 0 < phaseScale d k P Q k := phaseScale_pos hP hQ
  let c := β * phaseScale d k P Q k
  have hc : |c| ≤ 1 := by
    unfold c
    rw [abs_mul, abs_of_pos hspos]
    refine (mul_le_mul_of_nonneg_right hβ hspos.le).trans_eq ?_
    rw [completionRadius, hscale, Real.rpow_neg hP.le, Real.rpow_natCast, Real.rpow_neg hQ.le]
    field_simp
  have heq : (fun y => β * evalForm (t k).form (P • y)) = fun y => c • G k y := by
    funext y
    unfold c G normalizedChainForm
    rw [smul_eq_mul]
    field_simp
  change DerivativesBoundedOnBall (fun y => β * evalForm (t k).form (P • y)) N R C
  rw [heq]
  intro j hj x hx
  rw [iteratedFDeriv_const_smul_apply' (((normalizedChainForm_contDiff d k P Q t k).of_le (smoothOrder_le j)).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hbound j hj x hx) (abs_nonneg _)).trans (mul_le_of_le_one_left hC.le hc)

end

end Birch
