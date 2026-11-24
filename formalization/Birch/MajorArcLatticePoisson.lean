import Birch.LatticePoisson
import Birch.MajorPoissonTail
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The major-arc Poisson identity -/

open MvPolynomial ZMod MeasureTheory
open scoped BigOperators ContDiff

namespace Birch

noncomputable section

/-- Addition of arguments becomes multiplication of circle phases. -/
lemma phase_add (u v : ℝ) : phase (u+v) = phase u * phase v := by
  unfold phase
  push_cast
  rw [mul_add, Complex.exp_add]

/-- An integer phase at denominator `q` is the standard residue character. -/
lemma phase_int_div {q : ℕ} [NeZero q] (z : ℤ) :
    phase ((z : ℝ)/(q : ℝ)) = stdAddChar (z : ZMod q) := by
  rw [stdAddChar_coe]
  unfold phase
  push_cast
  ring_nf

/-- Evaluation of an integral form commutes with a ring homomorphism. -/
lemma evalForm_map {n : ℕ} {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (F : IntForm n) (x : Fin n → A) :
    f (evalForm F x) = evalForm F (fun i => f (x i)) := by
  unfold evalForm
  rw [MvPolynomial.hom_eval₂]
  congr 1
  ext i
  simp

private lemma eval_cast_residue_aux {n q : ℕ} (F : IntForm n) (x : Fin n → ℤ) :
    ((evalForm F x : ℤ) : ZMod q) = residueEval F q (fun i => (x i : ZMod q)) :=
  evalForm_map (Int.castRingHom (ZMod q)) F x

private lemma phase_linear_twist {n q : ℕ} [NeZero q] (z : Fin n → ℤ) (t : Fin n → ZMod q) :
    phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(q : ℝ)) =
      stdAddChar (∑ i, (z i : ZMod q)*t i) := by
  rw [← Finset.sum_div]
  have hs : (∑ i, (z i : ℝ)*((t i).val : ℝ)) = ((∑ i, z i * ((t i).val : ℤ) : ℤ) : ℝ) := by push_cast; rfl
  rw [hs, phase_int_div]
  congr 1
  push_cast
  simp

/-- Expand the normalized twisted sum in the positive Poisson phase convention. -/
lemma twistedCompleteSum_unfold_char {n q : ℕ} [NeZero q] (F : IntForm n)
    (a : ℤ) (z : Fin n → ℤ) :
    twistedCompleteSum F q a z = ((q : ℂ)^n)⁻¹ * ∑ t : Fin n → ZMod q,
      stdAddChar ((a : ZMod q) * residueEval F q t) *
        phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(q : ℝ)) := by
  unfold twistedCompleteSum completeSum
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [phase_linear_twist, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [residueEval, one_mul, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_sum]
  rfl

private lemma latticeFourierIntegral_amplitude {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (γ : ℝ) (ν : Fin n → ℝ) :
    latticeFourierIntegral (fun x => (w x : ℂ)*phase (γ * evalForm F x)) ν =
      twistedRealOscillation F w γ ν := by
  unfold latticeFourierIntegral twistedRealOscillation
  apply congrArg (fun g : (Fin n → ℝ) → ℂ => ∫ x, g x)
  funext x
  rw [sub_eq_add_neg, phase_add]
  ring

private lemma summable_twistedRealOscillation_lattice {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hcompact : HasCompactSupport w) (γ c : ℝ) (hc : 0 < c) :
    Summable (fun z : Fin n → ℤ => ‖twistedRealOscillation F w γ (c • latticeVector z)‖) := by
  classical
  let N := n+1
  obtain ⟨K, hK, hdecay⟩ := twistedRealOscillation_decay F hw hcompact N
  let B := K * ((1 + |γ|) / c)^N
  let f (z : Fin n → ℤ) := ‖twistedRealOscillation F w γ (c • latticeVector z)‖
  let f0 (z : Fin n → ℤ) := if z = 0 then f z else 0
  let ft (z : Fin n → ℤ) := if z = 0 then 0 else f z
  have ht : Summable ft := by
    apply ((summable_latticeVector_rpow (show n < N by omega)).mul_left B).of_nonneg_of_le
    · intro z
      dsimp [ft]
      split_ifs <;> positivity
    · intro z
      by_cases hz : z = 0
      · rw [show ft z = 0 by simp [ft,hz]]; positivity
      · have hz' : latticeVector z ≠ 0 := fun h => hz (latticeVector_injective n (h.trans (by ext i; simp [latticeVector])))
        have hν : c • latticeVector z ≠ 0 := smul_ne_zero hc.ne' hz'
        have h := hdecay γ (c • latticeVector z) hν
        rw [norm_smul, Real.norm_of_nonneg hc.le, div_mul_eq_div_div, div_pow] at h
        rw [show ft z = f z by simp [ft,hz]]
        dsimp only [f,B]
        rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← div_eq_mul_inv]
        exact (h.trans_eq (by rw [← mul_div_assoc]))
  have h0 : Summable f0 := summable_of_ne_finset_zero (s := {0}) (by
    intro z hz
    have hn : z ≠ 0 := fun h => hz (Finset.mem_singleton.mpr h)
    simp [f0, hn])
  convert h0.add ht using 1
  funext z
  by_cases hz : z = 0 <;> simp [f0,ft,f,hz]

private lemma exponentialSum_as_tsum {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1) {P : ℝ} (hP : 0 < P) (α : ℝ) :
    exponentialSum F w P α = ∑' x : Fin n → ℤ, (w (P⁻¹ • latticeVector x) : ℂ)*
      phase (α * ((evalForm F x : ℤ) : ℝ)) := by
  have hscale (x : Fin n → ℤ) : scaledPoint P x = P⁻¹ • latticeVector x := by
    ext i
    simp [scaledPoint, latticeVector, div_eq_mul_inv, mul_comm]
  unfold exponentialSum
  simp_rw [hscale]
  symm
  apply tsum_eq_sum
  intro x hx
  have hxw : w (scaledPoint P x) = 0 := by
    by_contra hne
    apply hx
    have hsupport := hw _ hne
    apply Fintype.mem_piFinset.mpr
    intro i
    have hi := (hsupport i).le
    unfold scaledPoint at hi
    rw [abs_div, abs_of_pos hP, div_le_iff₀ hP, one_mul] at hi
    obtain ⟨a,b⟩ := abs_le.mp hi
    apply Finset.mem_Icc.mpr
    refine ⟨?_, Int.le_floor.mpr b⟩
    rw [neg_le]
    exact Int.le_floor.mpr (by push_cast; linarith)
  rw [hscale] at hxw
  simp [hxw]

/-- Residue-class Poisson summation for a smooth compactly supported weight in the unit cube. -/
theorem majorArcPoissonIdentity_of_smooth_cubeSupported {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hw : ContDiff ℝ ∞ w)
    (hcompact : HasCompactSupport w) (hbox : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1) :
    MajorArcPoissonIdentity d F w := by
  intro P hP q _ a β
  let γ := P^d * β
  let f (x : Fin n → ℝ) := (w x : ℂ)*phase (γ * evalForm F x)
  let weight (t : Fin n → ZMod q) := stdAddChar ((a : ZMod q)*residueEval F q t)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hf : Continuous f := by
    apply (Complex.continuous_ofReal.comp hw.continuous).mul
    have hc : Continuous (fun t : ℝ => phase t) := by unfold phase; fun_prop
    exact hc.comp (continuous_const.mul (continuous_evalForm F))
  have hfs : HasCompactSupport f := (hcompact.comp_left (by simp : Complex.ofReal 0 = 0)).mul_right
  have hFsamples : Summable (fun z : Fin n → ℤ => ‖latticeFourierIntegral f ((P/(q : ℝ)) • latticeVector z)‖) := by
    simp_rw [show ∀ ν, latticeFourierIntegral f ν = twistedRealOscillation F w γ ν from
      latticeFourierIntegral_amplitude F w γ]
    exact summable_twistedRealOscillation_lattice F w hw hcompact γ _ (div_pos hP hq)
  have hterm (x : Fin n → ℤ) : (w (P⁻¹ • latticeVector x) : ℂ) *
      phase (((a : ℝ)/q + β)*((evalForm F x : ℤ) : ℝ)) =
      weight (fun i => (x i : ZMod q)) * f (P⁻¹ • latticeVector x) := by
    have hcast : ((evalForm F x : ℤ) : ℝ) = evalForm F (latticeVector x) :=
      evalForm_map (Int.castRingHom ℝ) F x
    have hvec : latticeVector x = fun i => P*(P⁻¹ • latticeVector x) i := by
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    have hpoly : ((evalForm F x : ℤ) : ℝ) = P^d * evalForm F (P⁻¹ • latticeVector x) := by
      rw [hcast]
      exact (congrArg (evalForm F) hvec).trans (evalForm_scale hF _ _)
    have harg : ((a : ℝ)/q + β)*((evalForm F x : ℤ) : ℝ) =
        ((a * evalForm F x : ℤ) : ℝ)/q + γ*evalForm F (P⁻¹ • latticeVector x) := by
      push_cast
      dsimp [γ]
      apply Eq.trans (by ring : _ = (a : ℝ) * ((evalForm F x : ℤ) : ℝ)/q + β * ((evalForm F x : ℤ) : ℝ))
      rw [hpoly]
      ring
    rw [harg, phase_add, phase_int_div]
    simp only [weight, f, Int.cast_mul, eval_cast_residue_aux]
    ring
  unfold normalizedSum
  rw [exponentialSum_as_tsum F w hbox hP]
  simp_rw [hterm]
  rw [poisson_lattice_weighted_residues hf hfs hP q weight hFsamples, smul_smul,
    show P ^ (-(n : ℝ)) * ((P/(q : ℝ))^n) = ((q : ℝ)^n)⁻¹ by
      rw [Real.rpow_neg hP.le, Real.rpow_natCast, div_pow]
      field_simp]
  simp only [Algebra.smul_def, ← tsum_mul_left]
  apply tsum_congr
  intro z
  rw [latticeFourierIntegral_amplitude, twistedCompleteSum_unfold_char]
  have hz : (algebraMap ℝ (Fin n → ℝ) (P/(q : ℝ)) * latticeVector z) =
      fun i => (P/(q : ℝ))*(z i : ℝ) := rfl
  rw [hz]
  dsimp only [γ, weight]
  change (((((q : ℝ)^n)⁻¹ : ℝ) : ℂ) * _) = _
  push_cast
  rw [mul_assoc]

/-- The exact residue-class Poisson identity for the transverse weights. -/
theorem majorArcPoissonIdentity_of_transverseWeight {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hw : TransverseWeight F w) :
    MajorArcPoissonIdentity d F w :=
  majorArcPoissonIdentity_of_smooth_cubeSupported hF hw.smooth hw.compact
    (fun _ hy => hw.support_box (subset_tsupport w hy))

end

end Birch
