import Birch.MajorArcExpansion
import Birch.CompleteBounds
import Birch.LatticeSummable
import Birch.TwistedDecay

/-!
# The nonzero Fourier modes on the major arcs

The exact Poisson identity in residue classes and uniform decay of the twisted
oscillatory integral give arbitrary power savings after summing the modes.
-/

open MvPolynomial MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace Birch

noncomputable section

/-- A normalized complete sum with the integral linear Fourier twist. -/
def twistedCompleteSum {n : ℕ} (F : IntForm n) (q : ℕ) [NeZero q]
    (a : ℤ) (m : Fin n → ℤ) : ℂ :=
  completeSum (C a * F + ∑ i, C (m i) * X i) q 1

theorem twistedCompleteSum_zero {n q : ℕ} [NeZero q] (F : IntForm n) (a : ℤ) :
    twistedCompleteSum F q a 0 = completeSum F q (a : ZMod q) := by
  unfold twistedCompleteSum completeSum residueEval
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, add_zero, eval₂_mul,
    eval₂_C, one_mul]
  rfl

/-- Poisson summation in residue classes, in the normalization of Section 5. -/
def MajorArcPoissonIdentity {n : ℕ} (d : ℕ) (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ (q : ℕ) [NeZero q] (a : ℤ) (β : ℝ),
    normalizedSum F w P ((a : ℝ)/q + β) = ∑' m : Fin n → ℤ,
      twistedCompleteSum F q a m *
        twistedRealOscillation F w (P^d * β) (fun i ↦ (P/q)*(m i : ℝ))

private theorem majorArcRatio_bound {d q : ℕ} [NeZero q] {P α : ℝ} (a : ℤ)
    (hP : 1 ≤ P) (hq : (q : ℝ) ≤ P ^ (1/2 : ℝ)) (ha : α ∈ liftedMajorArc d P q a) :
    (1 + |P^d * (α - (a : ℝ)/q)|) / (P / q) ≤ 2 * P ^ (-1/8 : ℝ) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hγ : |P^d * (α - (a : ℝ)/q)| ≤ P ^ (7/8 : ℝ) / q := by
    change |α - (a : ℝ)/q| ≤ P ^ (-(d : ℝ) + 7/8) / q at ha
    rw [abs_mul, abs_of_pos (pow_pos hPpos _)]
    refine (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq ?_
    rw [← mul_div_assoc, ← Real.rpow_natCast, ← Real.rpow_add hPpos]
    congr 2
    ring
  have hq' : (q : ℝ) ≤ P ^ (7/8 : ℝ) :=
    hq.trans (Real.rpow_le_rpow_of_exponent_le hP (by norm_num))
  apply (div_le_iff₀ (div_pos hPpos hqpos)).mpr
  apply (le_div_iff₀ hqpos).mp at hγ
  have hpowers : P ^ (-1/8 : ℝ) * P = P ^ (7/8 : ℝ) := by
    conv_lhs => arg 2; rw [← Real.rpow_one P]
    rw [← Real.rpow_add hPpos]
    congr 1
    norm_num
  have he : (2 * P ^ (-1/8 : ℝ)) * (P / (q : ℝ)) = (2 * P ^ (7/8 : ℝ)) / q := by
    rw [← mul_div_assoc, mul_assoc, hpowers]
  rw [he]
  apply (le_div_iff₀ hqpos).mpr
  rw [add_mul, one_mul]
  linarith

/-- The nonzero Fourier modes give arbitrary power savings whenever the ratio of
the rescaled oscillation to the reciprocal lattice spacing decreases by a power. -/
theorem norm_normalizedSum_sub_complete_le_of_poisson_ratio {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (hPoisson : MajorArcPoissonIdentity d F w) {K₀ τ : ℝ} (hK₀ : 0 < K₀) (hτ : 0 < τ)
    (L : ℝ) :
    ∃ E > 0, ∀ (P : ℝ), 1 ≤ P → ∀ (q : ℕ) [NeZero q] (a : ℤ) (α : ℝ),
      (1 + |P^d * (α - (a : ℝ)/q)|) / (P / q) ≤ K₀ * P^(-τ) →
      ‖normalizedSum F w P α - completeSum F q (a : ZMod q) *
        realOscillation F w (P^d * (α - (a : ℝ)/q))‖ ≤ E * P^(-L) := by
  classical
  let N := max (n+1) ⌈L / τ⌉₊
  have hN : n < N := Nat.lt_of_succ_le (le_max_left _ _)
  have hNB : L ≤ (N : ℝ) * τ := (div_le_iff₀ hτ).mp ((Nat.le_ceil _).trans (by
    exact_mod_cast (le_max_right (n+1) ⌈L / τ⌉₊)))
  obtain ⟨C, hC, hdecay⟩ := twistedRealOscillation_decay F hw hcompact N
  let A (m : Fin n → ℤ) : ℝ := ‖latticeVector m‖ ^ (-(N : ℝ))
  have hA : Summable A := summable_latticeVector_rpow hN
  let K : ℝ := C * K₀^N
  let E : ℝ := K * ((∑' m, A m) + 1)
  have hApos : 0 ≤ ∑' m, A m := tsum_nonneg (fun _ ↦ by dsimp [A]; positivity)
  have hK : 0 < K := mul_pos hC (by positivity)
  have hE : 0 < E := mul_pos hK (by linarith)
  refine ⟨E, hE, ?_⟩
  intro P hP q _ a α hratio
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hqpos : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  let β := α - (a : ℝ)/q
  let γ := P^d * β
  let ν (m : Fin n → ℤ) : Fin n → ℝ := fun i ↦ (P/q)*(m i : ℝ)
  let f (m : Fin n → ℤ) := twistedCompleteSum F q a m * twistedRealOscillation F w γ (ν m)
  let tail (m : Fin n → ℤ) := if m = 0 then 0 else f m
  have hf (m : Fin n → ℤ) (hm : m ≠ 0) :
      ‖f m‖ ≤ (K * P ^ (-L)) * A m := by
    have hL0 : latticeVector (0 : Fin n → ℤ) = 0 := by ext i; simp [latticeVector]
    have hL : latticeVector m ≠ 0 := fun h ↦ hm (latticeVector_injective n (h.trans hL0.symm))
    have hν_eq : ν m = (P/(q : ℝ)) • latticeVector m := rfl
    have hs : 0 < P/(q : ℝ) := div_pos hPpos hqpos
    have hnorm : ‖ν m‖ = (P/(q : ℝ)) * ‖latticeVector m‖ := by
      rw [hν_eq, norm_smul, Real.norm_of_nonneg hs.le]
    have hν : ν m ≠ 0 := by
      apply norm_pos_iff.mp
      rw [hnorm]
      exact mul_pos hs (norm_pos_iff.mpr hL)
    have hnumber : ((1 + |γ|) / ‖ν m‖) ≤
        (K₀ * P ^ (-τ)) / ‖latticeVector m‖ := by
      rw [hnorm, div_mul_eq_div_div]
      exact div_le_div_of_nonneg_right hratio (norm_nonneg _)
    have hfactor : ‖twistedCompleteSum F q a m‖ ≤ 1 :=
      norm_completeSum_le_one _ _
    rw [show f m = _ from rfl, norm_mul]
    calc
      _ ≤ 1 * ‖twistedRealOscillation F w γ (ν m)‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ C * ((1 + |γ|) / ‖ν m‖)^N := by simpa only [one_mul] using hdecay γ (ν m) hν
      _ ≤ C * ((K₀ * P ^ (-τ)) / ‖latticeVector m‖)^N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnumber _) hC.le
      _ = (K * P ^ (-(N : ℝ) * τ)) * A m := by
        dsimp only [K, A]
        rw [div_pow, mul_pow, ← Real.rpow_mul_natCast hPpos.le, Real.rpow_neg (norm_nonneg _),
          Real.rpow_natCast, div_eq_mul_inv]
        rw [show (-τ) * N = -(N : ℝ) * τ by ring]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [A]; positivity)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) hK.le
  have ht (m : Fin n → ℤ) : ‖tail m‖ ≤ (K * P ^ (-L)) * A m := by
    by_cases hm : m = 0
    · simp only [tail, if_pos hm, norm_zero]
      dsimp [A]
      positivity
    · simpa only [tail, if_neg hm] using hf m hm
  have htNorm : Summable (fun m ↦ ‖tail m‖) :=
    (hA.mul_left (K * P ^ (-L))).of_nonneg_of_le (fun _ ↦ norm_nonneg _) ht
  have htSum : Summable tail := htNorm.of_norm
  have hfSum : Summable f := by
    have hsingle : Summable (fun m : Fin n → ℤ ↦ if m = 0 then f 0 else 0) :=
      summable_of_ne_finset_zero (s := {0}) (by
        intro m hm
        have hm₀ : m ≠ (0 : Fin n → ℤ) := by simpa only [Finset.mem_singleton] using hm
        exact if_neg hm₀)
    apply (hsingle.add htSum).congr
    intro m
    by_cases hm : m = 0 <;> simp [tail, hm]
  have hsum : normalizedSum F w P α = f 0 + ∑' m, tail m := by
    have H := hPoisson P hPpos q a β
    rw [show (a : ℝ)/q + β = α by dsimp [β]; ring] at H
    change normalizedSum F w P α = ∑' m, f m at H
    rw [H, hfSum.tsum_eq_add_tsum_ite 0]
  have hzero : f 0 = completeSum F q (a : ZMod q) * realOscillation F w γ := by
    unfold f
    rw [twistedCompleteSum_zero]
    congr 1
    have hv : ν 0 = 0 := by ext i; simp [ν]
    rw [hv]
    simp [twistedRealOscillation, realOscillation]
  change ‖normalizedSum F w P α - completeSum F q (a : ZMod q) *
    realOscillation F w γ‖ ≤ E * P ^ (-L)
  rw [← hzero, hsum, add_sub_cancel_left]
  calc
    _ ≤ ∑' m, ‖tail m‖ := norm_tsum_le_tsum_norm htNorm
    _ ≤ ∑' m, (K * P ^ (-L)) * A m :=
      htNorm.tsum_le_tsum ht (hA.mul_left _)
    _ = K * (∑' m, A m) * P ^ (-L) := by rw [tsum_mul_left]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) hK.le

/-- The earlier major-arc expansion follows from the reciprocal lattice bound
on the original arcs. -/
theorem pointwiseMajorArcExpansion_of_poisson_of_compact {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w)
    (hPoisson : MajorArcPoissonIdentity d F w) : PointwiseMajorArcExpansion d F w := by
  intro B _
  obtain ⟨E, hE, hbound⟩ := norm_normalizedSum_sub_complete_le_of_poisson_ratio
    hw hcompact hPoisson (K₀ := 2) (τ := 1/8) (by norm_num) (by norm_num) ((d : ℝ)+B)
  refine ⟨E, hE, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with P hP q _ a hq _ α ha
  have hratio := majorArcRatio_bound a hP hq ha
  rw [show (-1 / 8 : ℝ) = -(1 / 8 : ℝ) by ring] at hratio
  simpa only [show -((d : ℝ) + B) = -(d : ℝ) - B by ring] using hbound P hP q a α hratio

/-- The pointwise expansion for the original transverse weights. -/
theorem pointwiseMajorArcExpansion_of_poisson {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : TransverseWeight F w)
    (hPoisson : MajorArcPoissonIdentity d F w) : PointwiseMajorArcExpansion d F w :=
  pointwiseMajorArcExpansion_of_poisson_of_compact hw.smooth hw.compact hPoisson

end
end Birch
