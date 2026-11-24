import Birch.WeylWeightBounds
import Birch.WeylReciprocalCount
import Birch.WeylTensorShrinking

/-! # Bounding the Weyl sum by the multilinear near-frequency count -/

open Finset Matrix MvPolynomial
open scoped BigOperators ContDiff Matrix

namespace Birch

noncomputable section

private theorem sum_weylShiftBox_cons {n k : ℕ} (P : ℝ) (f : (Fin (k+1) → Fin n → ℤ) → ℝ) :
    (∑ t ∈ weylShiftBox n (k+1) P, f t) =
      ∑ r ∈ weylShiftBox n k P, ∑ x ∈ latticeBox n P, f (Fin.cons x r) := by
  let e := Fin.consEquiv (fun _ : Fin (k+1) => Fin n → ℤ)
  have hE : weylShiftBox n (k+1) P = ((latticeBox n P) ×ˢ weylShiftBox n k P).map e.toEmbedding := by
    have H := Finset.filter_piFinset_eq_map_consEquiv
      (fun _ : Fin (k+1) => latticeBox n P) (fun _ => True)
    simp only [Finset.filter_true] at H
    change _ = ((latticeBox n P) ×ˢ Fintype.piFinset
      (Fin.tail (fun _ : Fin (k+1) => latticeBox n P))).map e.toEmbedding
    exact H
  rw [hE, Finset.sum_map, Finset.sum_product, Finset.sum_comm]
  rfl

/-- One final linear block is enough to convert the whole product of
reciprocal-distance weights to the multilinear near-frequency count. -/
theorem sum_weylTensor_linearPhaseBound_le_nearCount {n k : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (P : ℝ), 1 ≤ P → ∀ (F : IntForm n) (α : ℝ),
      (∑ t ∈ weylShiftBox n (k+1) P, ∏ i,
        linearPhaseBound (weylIntervalLength P) (α * (weylFrequency (List.ofFn t) F i : ℝ))) ≤
        (C*P^ε*P^n) *
          ((weylNearTensorBox (k := k+1) F α (fun _ => 2*P) (1/(2*P))).card : ℝ) := by
  classical
  obtain ⟨C,hC,hfreq⟩ := sum_weylIntervalPhaseBound_le_frequency_count (A := Fin n → ℤ) n hε
  refine ⟨C,hC,fun P hP F α => ?_⟩
  let B := latticeBox n P
  let U := latticeBox n (2*P)
  let T := weylShiftBox n k P
  let M (r : Fin k → Fin n → ℤ) : (Fin n → ℤ) →+ (Fin n → ℤ) :=
    (weylLastMatrix (List.ofFn r) F).mulVecLin.toAddMonoidHom
  have hM (r : Fin k → Fin n → ℤ) (x : Fin n → ℤ) :
      weylFrequency (List.ofFn (Fin.cons x r)) F = M r x := by
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    exact weylFrequency_block [] (List.ofFn r) x F
  have hdiff : ∀ x ∈ B, ∀ y ∈ B, x-y ∈ U := by
    intro x hx y hy
    apply mem_latticeBox_iff_abs.mpr
    intro i
    simp only [Pi.sub_apply, Int.cast_sub]
    exact (abs_sub _ _).trans (by
      have hx₀ := mem_latticeBox_iff_abs.mp hx i
      have hy₀ := mem_latticeBox_iff_abs.mp hy i
      linarith)
  let N (r : Fin k → Fin n → ℤ) := U.filter (fun x => ∀ j, ∃ b : ℤ,
    |(M r x j : ℝ)*α-b| ≤ 1/(2*P))
  let S := weylNearTensorBox (k := k+1) F α (fun _ => 2*P) (1/(2*P))
  have hins : (∑ r ∈ T, (N r).card) ≤ S.card := by
    rw [← Finset.card_sigma]
    apply card_le_card_of_injOn (fun z : Sigma fun _ : Fin k → Fin n → ℤ => Fin n → ℤ => Fin.cons z.2 z.1)
    · intro z hz
      obtain ⟨hr,hx⟩ := Finset.mem_sigma.mp hz
      obtain ⟨hxU,hnear⟩ := Finset.mem_filter.mp hx
      refine mem_weylNearTensorBox.mpr ⟨?_, fun j => ?_⟩
      · intro i
        refine Fin.cases ?_ (fun a => ?_) i
        · exact hxU
        · apply mem_latticeBox_iff_abs.mpr
          intro b
          have hz := mem_latticeBox_iff_abs.mp ((Fintype.mem_piFinset.mp hr) a) b
          exact hz.trans (by linarith)
      · rw [hM, mul_comm α]
        exact (nearestIntegerDistance_le_iff _ _).mpr (hnear j)
    · intro x _ y _ h
      have hfst : x.1 = y.1 := funext fun i => congrFun h i.succ
      have hsnd : x.2 = y.2 := congrFun h 0
      exact Sigma.ext hfst (heq_of_eq hsnd)
  rw [sum_weylShiftBox_cons]
  calc
    _ ≤ ∑ r ∈ T, (C*P^ε*P^n) * ((N r).card : ℝ) := by
      apply sum_le_sum
      intro r _
      have h := hfreq P hP B U (M r) α hdiff
      simpa only [hM, mul_comm α, B, N] using h
    _ = (C*P^ε*P^n) * ((∑ r ∈ T, (N r).card) : ℝ) := by
      exact (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast hins) (by positivity)

/-- All analytic steps of the Weyl argument up to the multilinear
near-frequency count, with the normalization of the paper. -/
theorem norm_normalizedSum_pow_le_weylNearTensor {n k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (F : IntForm n) (hF : F.IsHomogeneous (k+2))
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) :
    ∃ C > 0, ∀ (P : ℝ), 1 ≤ P → ∀ α : ℝ,
      ‖normalizedSum F w P α‖^(2^(k+1) : ℕ) ≤
        C*P^ε*((weylNearTensorBox (k := k+1) F α (fun _ => 2*P) (1/(2*P))).card : ℝ)/P^(n*(k+1)) := by
  obtain ⟨C,hC,hfreq⟩ := sum_weylTensor_linearPhaseBound_le_nearCount (n := n) (k := k) hε
  obtain ⟨D,hD,hweight⟩ := uniform_weylLinear_weight_bound hw hwbox (k+1)
  let E : ℝ := ((30 : ℝ)^n)^(2^(k+1)-1 : ℕ)
  refine ⟨E*(D*C),by positivity, fun P hP α => ?_⟩
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  let N : ℝ := (weylNearTensorBox (k := k+1) F α (fun _ => 2*P) (1/(2*P))).card
  let B := weylShiftBox n (k+1) P
  let a (t : Fin (k+1) → Fin n → ℤ) :=
    ‖normalizedSum (weylDifference (List.ofFn t) F) (weylDifferencedWeight (List.ofFn t) w P) P α‖
  let b (t : Fin (k+1) → Fin n → ℤ) := ∏ i,
    linearPhaseBound (weylIntervalLength P) (α * (weylFrequency (List.ofFn t) F i : ℝ))
  have hb (t : Fin (k+1) → Fin n → ℤ) : a t ≤ (P^n)⁻¹*D*b t := by
    let g := weylDifference (List.ofFn t) F
    let w' := weylDifferencedWeight (List.ofFn t) w P
    let c := α * ((g.coeff 0 : ℤ) : ℝ)
    let β (i : Fin n) := α * (weylFrequency (List.ofFn t) F i : ℝ)
    have hh (x : Fin n → ℤ) : α * ((evalForm g x : ℤ) : ℝ) = c + ∑ i, (x i : ℝ)*β i := by
      rw [show evalForm g x = _ from eval_weylDifference_affine (List.ofFn t) F
        (by simp) hF.totalDegree_le x, homogeneousComponent_eq_self hF]
      push_cast
      unfold c β
      rw [mul_add, mul_sum]
      congr 1
      exact sum_congr rfl fun _ _ => by ring
    change ‖normalizedSum g w' P α‖ ≤ _
    rw [normalizedSum, norm_smul, Real.norm_of_nonneg (by positivity), Real.rpow_neg hP₀.le,
      Real.rpow_natCast, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simp only [exponentialSum, hh]
    exact hweight P hP₀ (List.ofFn t) (by simp) β c
  have hsum : (∑ t ∈ B, a t) ≤ (D*C)*P^ε*N := by
    calc
      _ ≤ ∑ t ∈ B, (P^n)⁻¹*D*b t := sum_le_sum fun t _ => hb t
      _ = ((P^n)⁻¹*D)*(∑ t ∈ B, b t) := by rw [mul_sum]
      _ ≤ ((P^n)⁻¹*D)*((C*P^ε*P^n)*N) := mul_le_mul_of_nonneg_left
        (hfreq P hP F α) (by positivity)
      _ = _ := by field_simp
  refine (norm_normalizedSum_pow_le_weylSum (k+1) hP F w hwbox α).trans ?_
  have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum (by positivity : 0 ≤ P^(n*(k+1))))
    (by positivity : 0 ≤ E)
  exact h.trans_eq (by ring)

end
end Birch
