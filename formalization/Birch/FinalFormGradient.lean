import Birch.FinalForms
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Form weights on the noncritical locus -/

open Filter MeasureTheory MvPolynomial
open scoped ContDiff Manifold Topology

namespace Birch

noncomputable section

/-- The gradient of the form is nowhere zero on the support of the weight. -/
def HasNonvanishingGradientOnSupport {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ tsupport w, ∃ i : Fin n, evalForm (pderiv i F) x ≠ 0

theorem HasTransverseSupport.nonvanishingGradient {n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (h : HasTransverseSupport F w) : HasNonvanishingGradientOnSupport F w := by
  obtain ⟨i, hi⟩ := h
  exact fun x hx => ⟨i, hi x hx⟩

/-- A smooth partition of unity splits the weight into one admissible piece for
each partial derivative. -/
private theorem FinalWeight.exists_gradientPartition {n : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : FinalWeight w) (hgrad : HasNonvanishingGradientOnSupport F w) :
    ∃ v : Fin n → (Fin n → ℝ) → ℝ,
      (∀ i, FinalWeight (v i) ∧ HasTransverseSupport F (v i)) ∧
      (∀ x, ∑ i, v i x = w x) := by
  let U (i : Fin n) : Set (Fin n → ℝ) := {x | evalForm (pderiv i F) x ≠ 0}
  have hU : ∀ i, IsOpen (U i) := fun i =>
    isOpen_ne_fun (continuous_evalForm (pderiv i F)) continuous_const
  have hcover : tsupport w ⊆ ⋃ i, U i := fun x hx => Set.mem_iUnion.mpr (hgrad x hx)
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, Fin n → ℝ))
    (isClosed_tsupport w) U hU hcover
  let v (i : Fin n) : (Fin n → ℝ) → ℝ := w * ⇑(ρ i)
  refine ⟨v, ?_, ?_⟩
  · intro i
    have hs : tsupport (v i) ⊆ tsupport w := tsupport_mul_subset_left
    have hp : tsupport (v i) ⊆ tsupport (ρ i) := tsupport_mul_subset_right
    have hsmooth : ContDiff ℝ ∞ (ρ i) := contMDiff_iff_contDiff.mp (ρ i).contMDiff
    refine ⟨⟨⟨hw.smooth.mul hsmooth, hw.compact.mul_right, ?_⟩, ?_, ?_⟩, ⟨i, ?_⟩⟩
    · exact fun x => mul_nonneg (hw.nonnegative x) (ρ.nonneg i x)
    · intro x
      change w x * ρ i x ≤ 1
      simpa only [one_mul] using
        mul_le_mul (hw.bounded x) (ρ.le_one i x) (ρ.nonneg i x) zero_le_one
    · exact fun x hx => hw.support_box x (hs hx)
    · exact fun x hx => hρ i (hp hx)
  · intro x
    change ∑ i, w x * ρ i x = w x
    rw [← Finset.mul_sum]
    by_cases hx : x ∈ tsupport w
    · rw [← finsum_eq_sum_of_fintype, ρ.sum_eq_one hx, mul_one]
    · rw [Function.notMem_support.mp (fun h => hx (subset_tsupport w h)), zero_mul]

private theorem realOscillation_eq_sum {n : ℕ} (F : IntForm n)
    {w : (Fin n → ℝ) → ℝ} {v : Fin n → (Fin n → ℝ) → ℝ}
    (hv : ∀ i, FinalWeight (v i)) (hsum : ∀ x, ∑ i, v i x = w x) (γ : ℝ) :
    realOscillation F w γ = ∑ i, realOscillation F (v i) γ := by
  unfold realOscillation
  have hphase : Continuous (fun x : Fin n → ℝ => phase (γ * evalForm F x)) := by
    have hp : Continuous phase := by unfold phase; fun_prop
    exact hp.comp (continuous_const.mul (continuous_evalForm F))
  have hterm (i : Fin n) : Integrable (fun x => (v i x : ℂ) * phase (γ * evalForm F x)) := by
    have hc : HasCompactSupport (fun x => (v i x : ℂ)) := by
      have heq : Function.support (fun x => (v i x : ℂ)) = Function.support (v i) := by
        ext x
        simp [Function.mem_support]
      unfold HasCompactSupport tsupport
      rw [heq]
      exact (hv i).compact
    have hcont := (Complex.continuous_ofReal.comp (hv i).smooth.continuous).mul hphase
    exact hcont.integrable_of_hasCompactSupport hc.mul_right
  rw [← integral_finsetSum _ (fun i _ => hterm i)]
  exact integral_congr_ae (ae_of_all _ fun x => by
    change (w x : ℂ) * phase (γ * evalForm F x) =
      ∑ i, (v i x : ℂ) * phase (γ * evalForm F x)
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hsum])

private theorem compactWeightedZeros_eq_sum {n : ℕ} (F : IntForm n)
    {w : (Fin n → ℝ) → ℝ} {v : Fin n → (Fin n → ℝ) → ℝ}
    (hw : FinalWeight w) (hv : ∀ i, FinalWeight (v i))
    (hsum : ∀ x, ∑ i, v i x = w x) {B : ℝ} (hB : 0 < B) :
    compactWeightedZeros F w B = ∑ i, compactWeightedZeros F (v i) B := by
  classical
  have hbox (u : (Fin n → ℝ) → ℝ) (hu : FinalWeight u) :
      compactWeightedZeros F u B =
        ∑ x ∈ latticeBox n B, if evalForm F x = 0 then u (scaledPoint B x) else 0 := by
    simpa only [one_mul] using compactWeightedZeros_eq_box F u hB (R := 1)
      (fun x hx i => (hu.cubeSupported x hx i).le)
  rw [hbox w hw]
  simp_rw [fun i => hbox (v i) (hv i)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp [hsum]

/-- A common power saving for weights with one fixed transverse derivative
gives the same saving for weights supported anywhere on the noncritical locus. -/
theorem formAsymptotic_of_gradientPartition {n d : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hn : 0 < n) (hw : FinalWeight w) (hgrad : HasNonvanishingGradientOnSupport F w) {η : ℝ}
    (hlocal : ∀ u : (Fin n → ℝ) → ℝ, FinalWeight u → HasTransverseSupport F u →
      Summable (fun q : ℕ => formConductorMass F (q + 1)) ∧ Integrable (realOscillation F u) ∧
      ∃ C > 0, ∀ᶠ B : ℝ in atTop,
        ‖(compactWeightedZeros F u B : ℂ) -
          (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F u)‖ ≤
          C * B ^ ((n : ℝ) - d - η)) :
    Summable (fun q : ℕ => formConductorMass F (q + 1)) ∧ Integrable (realOscillation F w) ∧
    ∃ C > 0, ∀ᶠ B : ℝ in atTop,
      ‖(compactWeightedZeros F w B : ℂ) -
        (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * B ^ ((n : ℝ) - d - η) := by
  obtain ⟨v, hv, hsum⟩ := hw.exists_gradientPartition hgrad
  have hdata (i : Fin n) := hlocal (v i) (hv i).1 (hv i).2
  have hI (i : Fin n) := (hdata i).2.1
  have hreal : realOscillation F w = fun γ => ∑ i, realOscillation F (v i) γ :=
    funext (realOscillation_eq_sum F (fun i => (hv i).1) hsum)
  have hIw : Integrable (realOscillation F w) := by
    rw [hreal]
    exact integrable_finsetSum _ fun i _ => hI i
  have hJ : singularIntegral F w = ∑ i, singularIntegral F (v i) := by
    unfold singularIntegral
    rw [hreal]
    exact integral_finsetSum _ fun i _ => hI i
  choose C hC herror using fun i => (hdata i).2.2
  have hCsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ => (hC i).le
  refine ⟨(hdata ⟨0, hn⟩).1, hIw, 1 + ∑ i, C i, by linarith, ?_⟩
  filter_upwards [Filter.eventually_all.2 herror, eventually_gt_atTop (0 : ℝ)] with B hB hB₀
  have hsplit : (compactWeightedZeros F w B : ℂ) -
      (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w) =
      ∑ i, ((compactWeightedZeros F (v i) B : ℂ) -
        (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F (v i))) := by
    rw [compactWeightedZeros_eq_sum F hw (fun i => (hv i).1) hsum hB₀, Complex.ofReal_sum, hJ]
    simp only [Finset.mul_sum, Finset.smul_sum, Finset.sum_sub_distrib]
  rw [hsplit]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => hB i).trans ?_)
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- The weighted form asymptotic in the manuscript for a weight supported on
the noncritical locus. -/
def FinalFormAsymptotic : Prop :=
  ∀ d n : ℕ, 2 ≤ d → ∃ η > 0,
    ∀ (F : IntForm n) (σ : ℕ) (w : (Fin n → ℝ) → ℝ),
      F ≠ 0 → F.IsHomogeneous d → RationalGradientDimension F σ → 2 ^ (d + 1) - 3 ≤ n - σ →
      FinalWeight w → HasNonvanishingGradientOnSupport F w →
      Summable (fun q : ℕ => formConductorMass F (q + 1)) ∧ Integrable (realOscillation F w) ∧
      ∃ C > 0, ∀ᶠ B : ℝ in atTop,
        ‖(compactWeightedZeros F w B : ℂ) -
          (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
          C * B ^ ((n : ℝ) - d - η)

/-- Deligne's prime-field estimate gives the weighted form asymptotic with
the manuscript's full support condition. -/
theorem finalFormAsymptotic
    (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) : FinalFormAsymptotic := by
  intro d n hd
  obtain ⟨η, hη, hfixed⟩ := fixedPartialFormAsymptotic_of_deligne hDeligne d n hd
  refine ⟨η, hη, ?_⟩
  intro F σ w hFne hF hσ hν hw hgrad
  have hn : 0 < n := by
    have hpow : 4 ≤ 2 ^ (d + 1) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ d + 1 by omega)
    omega
  exact formAsymptotic_of_gradientPartition hn hw hgrad
    (fun u hu htrans => hfixed F σ u hFne hF hσ hν hu htrans)

end

end Birch
