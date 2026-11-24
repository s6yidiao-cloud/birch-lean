import Birch.NormalizedDifference
import Birch.UniformFourier
import Mathlib.Data.Nat.Choose.Sum

/-!
# Uniform Fourier decay of the actual terminal amplitude

The differenced weights have bounded derivatives globally. The polynomial part
has bounded derivatives on each fixed ball after the near-resonance factor is
absorbed. A bounded affine restriction then has the required Fourier decay.
-/

open Set Finset MeasureTheory
open scoped BigOperators ContDiff Topology Nat

namespace Birch

noncomputable section

private lemma smoothOrder_le_terminal (j : ℕ) : (j : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

/-- Uniform derivative bounds on a ball also bound the derivatives of a product. -/
theorem bounded_derivatives_mul {X A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedRing A] [NormedAlgebra ℝ A] {f g : X → A} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} {R C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : DerivativesBoundedOnBall f N R C) (hc : DerivativesBoundedOnBall g N R D) :
    DerivativesBoundedOnBall (fun x => f x * g x) N R ((2 : ℝ)^N*C*D) := by
  intro j hj x hx
  refine (norm_iteratedFDeriv_mul_le hf hg x (smoothOrder_le_terminal j)).trans ?_
  calc
    _ ≤ ∑ i ∈ range (j+1), (j.choose i : ℝ) * C * D := by
      apply sum_le_sum
      intro i hi
      have h₁ := hb i (by have := mem_range.mp hi; omega) x hx
      have h₂ := hc (j-i) (by omega) x hx
      exact mul_le_mul (mul_le_mul_of_nonneg_left h₁ (by positivity)) h₂ (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*C*D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have he : (∑ i ∈ range (j+1), (j.choose i : ℝ)) = (2 : ℝ)^j := by exact_mod_cast Nat.sum_range_choose j
      rw [he]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hC) hD

/-- Every weight in any chain starting from the same smooth cube-supported weight
has global derivative bounds depending only on the length and derivative order. -/
theorem uniform_differencedWeight_derivatives {n k : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w) (hb : CubeSupported w) (N : ℕ) :
    ∃ C > 0, ∀ (P Q : ℝ) (m : ℕ → ℤ) (α : ℝ)
      (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
      IsPolynomialDifferencingChain (k := k) P Q m F w α t u →
      ∀ R : ℝ, DerivativesBoundedOnBall (t k).weight N R C := by
  obtain ⟨C, hC, hBw⟩ := exists_derivativesBoundedOnBall hw N 1
  let D : ℕ → ℝ := Nat.rec C (fun _ C' => (2 : ℝ)^N*C'*C')
  have hD (i : ℕ) : 0 < D i := by
    induction i with
    | zero => exact hC
    | succ i ih => change 0 < (2 : ℝ)^N*D i*D i; positivity
  have hsupp : tsupport w ⊆ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    have h : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
      simpa only [Real.norm_eq_abs] using (hb x hx i).le
    simpa only [Metric.mem_closedBall, dist_zero_right] using h
  refine ⟨D k,hD k,?_⟩
  intro P Q m α t u ht
  have hall (i : ℕ) (hi : i ≤ k) (R : ℝ) : DerivativesBoundedOnBall (t i).weight N R (D i) := by
    induction i generalizing R with
    | zero =>
      rw [ht.1]
      intro j hj x _
      change ‖iteratedFDeriv ℝ j w x‖ ≤ C
      by_cases h : ‖x‖ ≤ 1
      · exact hBw j hj x h
      · have hz : iteratedFDeriv ℝ j w x = 0 := by
          by_contra hn
          have hb' : x ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
            hsupp (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := w) j hn)
          apply h
          simpa only [Metric.mem_closedBall, dist_zero_right] using hb'
        rw [hz, norm_zero]
        exact hC.le
    | succ i ih =>
      have hi' : i < k := by omega
      have hsm := ht.contDiff_weight hw hi'.le
      let a : Fin n → ℝ := fun j => (m i : ℝ)*(u i j : ℝ)/P
      have hTrans : ContDiff ℝ ∞ (fun x => (t i).weight (x+a)) := hsm.comp (contDiff_id.add contDiff_const)
      have hTransBound : DerivativesBoundedOnBall (fun x => (t i).weight (x+a)) N R (D i) := by
        intro j hj x _
        rw [iteratedFDeriv_comp_add_right]
        exact ih (by omega) ‖x+a‖ j hj (x+a) le_rfl
      rw [(ht.2 i hi').2]
      change DerivativesBoundedOnBall (fun x => (t i).weight (x+a) * (t i).weight x) N R ((2 : ℝ)^N*D i*D i)
      exact bounded_derivatives_mul hTrans hsm (hD i).le (hD i).le hTransBound (ih (by omega) R)
  exact hall k le_rfl

/-- Uniform derivative bounds on a real phase give derivative bounds on its character. -/
theorem bounded_derivatives_comp_phase {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ} (hf : ContDiff ℝ ∞ f) {N : ℕ} {R C D : ℝ}
    (hD : 0 ≤ D) (hfB : DerivativesBoundedOnBall f N R C)
    (hphaseB : DerivativesBoundedOnBall phase N C D) :
    DerivativesBoundedOnBall (fun x => phase (f x)) N R ((N.factorial : ℝ)*D*(max 1 C)^N) := by
  intro j hj x hx
  have hPhase : ContDiff ℝ ∞ phase := by
    unfold phase
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hfx : ‖f x‖ ≤ C := by simpa only [norm_iteratedFDeriv_zero] using hfB 0 (by omega) x hx
  let T := max 1 C
  have hT : 1 ≤ T := le_max_left _ _
  have hp (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : ‖iteratedFDeriv ℝ i f x‖ ≤ T^i :=
    (hfB i (hij.trans hj) x hx).trans ((le_max_right _ _).trans (le_self_pow₀ hT (by omega)))
  have ht := norm_iteratedFDeriv_comp_le hPhase hf (smoothOrder_le_terminal j) x
    (fun i hij => hphaseB i (hij.trans hj) (f x) hfx) hp
  exact ht.trans (mul_le_mul (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hD)
    (pow_le_pow_right₀ hT hj) (by positivity) (by positivity))

/-- A bounded affine change of space variables preserves uniform derivative bounds. -/
theorem bounded_derivatives_affine {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {f : Y → Z}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} {R C : ℝ} (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hB : DerivativesBoundedOnBall f N (R+R^2) C)
    (L : X →L[ℝ] Y) (b : Y) (hL : ‖L‖ ≤ R) (hb : ‖b‖ ≤ R) :
    DerivativesBoundedOnBall (fun x => f (b+L x)) N R (C*R^N) := by
  intro j hj x hx
  let g : Y → Z := fun y => f (b+y)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  change ‖iteratedFDeriv ℝ j (g ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hg x (smoothOrder_le_terminal j)]
  refine ((iteratedFDeriv ℝ j g (L x)).norm_compContinuousLinearMap_le (fun _ => L)).trans ?_
  have hpt : ‖b+L x‖ ≤ R+R^2 := by
    exact (norm_add_le _ _).trans (add_le_add hb ((L.le_opNorm x).trans (by
      rw [pow_two]; exact mul_le_mul hL hx (norm_nonneg _) (by positivity))))
  have hnorm : ‖iteratedFDeriv ℝ j g (L x)‖ ≤ C := by
    unfold g
    rw [iteratedFDeriv_comp_add_left]
    exact hB j hj (b+L x) hpt
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul hnorm ((pow_le_pow_left₀ (norm_nonneg _) hL _).trans (pow_le_pow_right₀ hR hj))
    (by positivity) hC

/-- The normalized amplitude on an affine slice of the terminal lattice sum. -/
def terminalSliceAmplitude {n l : ℕ} (t : PolynomialDifferencingState n) (P β : ℝ)
    (L : (Fin l → ℝ) →L[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ) (x : Fin l → ℝ) : ℂ :=
  (t.weight (b+L x) : ℂ) * phase (β * evalForm t.form (P • (b+L x)))

/-- The actual terminal amplitude, restricted to a bounded affine slice, has a
Fourier-decay constant independent of the scale, shifts, phase and frozen coordinates. -/
theorem uniform_terminalSliceAmplitude_decay {n d r l : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hrd : r ≤ d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) (N : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C > 0, ∀ (P Q : ℝ), 0 < P → 0 < Q → ∀ (m : ℕ → ℤ),
      (∀ i < d-r, 0 < m i ∧ (m i : ℝ)*differencingHeight (d-r) Q i ≤ P) →
      ∀ (α : ℝ) (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
        IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
        ∀ (β : ℝ), |β| ≤ completionRadius d r P Q →
        ∀ (L : (Fin l → ℝ) →L[ℝ] (Fin n → ℝ)) (b : Fin n → ℝ), ‖L‖ ≤ R → ‖b‖ ≤ R →
        (∀ x, (t (d-r)).weight (b+L x) ≠ 0 → ‖x‖ ≤ R) →
        ContDiff ℝ ∞ (terminalSliceAmplitude (t (d-r)) P β L b) ∧
        HasCompactSupport (terminalSliceAmplitude (t (d-r)) P β L b) ∧
        ∀ ν, ‖latticeFourierIntegral (terminalSliceAmplitude (t (d-r)) P β L b) ν‖ ≤ C*(1+‖ν‖)^(-(N : ℝ)) := by
  let B := R+R^2
  obtain ⟨A,hA,hAb⟩ := uniform_terminal_phase_derivatives hF hrd N B
  obtain ⟨D,hD,hDb⟩ := uniform_differencedWeight_derivatives (F := F) (k := d-r) hw hwbox N
  have hphase : ContDiff ℝ ∞ phase := by
    unfold phase
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  obtain ⟨E,hE,hEb⟩ := exists_derivativesBoundedOnBall hphase N A
  let T := (2 : ℝ)^N * (‖Complex.ofRealCLM‖*D) * ((N.factorial : ℝ)*E*(max 1 A)^N)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  let K := (2 : ℝ)^N * (T*R^N) * (volume : Measure (Fin l → ℝ)).real (Metric.closedBall (0 : Fin l → ℝ) R)
  refine ⟨1+K, add_pos_of_pos_of_nonneg zero_lt_one (by dsimp [K]; positivity),?_⟩
  intro P Q hP hQ m hm α t u ht β hβ L b hL hb hbs
  let a : (Fin n → ℝ) → ℝ := fun y => β * evalForm (t (d-r)).form (P • y)
  let c : (Fin n → ℝ) → ℂ := fun y => ((t (d-r)).weight y : ℂ)
  let f : (Fin n → ℝ) → ℂ := fun y => c y * phase (a y)
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul ((contDiff_evalForm _).comp
    (show ContDiff ℝ ∞ (fun y : Fin n → ℝ => P • y) by fun_prop))
  have hw' := ht.contDiff_weight hw le_rfl
  have hcc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp hw'
  have hfc : ContDiff ℝ ∞ f := hcc.mul (hphase.comp ha)
  have hab : DerivativesBoundedOnBall a N B A := hAb P Q hP hQ m hm w α t u ht β hβ
  have hcb : DerivativesBoundedOnBall c N B (‖Complex.ofRealCLM‖*D) := by
    intro j hj x hx
    have H := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (hw'.contDiffAt (x := x)) (smoothOrder_le_terminal j)
    exact H.trans (mul_le_mul_of_nonneg_left (hDb P Q m α t u ht B j hj x hx) (norm_nonneg _))
  have hfb : DerivativesBoundedOnBall f N B T := bounded_derivatives_mul hcc (hphase.comp ha)
    (by positivity) (by positivity) hcb (bounded_derivatives_comp_phase ha hE.le hab hEb)
  have hB := bounded_derivatives_affine hfc hR hT hfb L b hL hb
  have hf'c : ContDiff ℝ ∞ (terminalSliceAmplitude (t (d-r)) P β L b) :=
    hfc.comp (contDiff_const.add L.contDiff)
  have hx : ∀ x, terminalSliceAmplitude (t (d-r)) P β L b x ≠ 0 → ‖x‖ ≤ R := by
    intro x h
    apply hbs x
    intro hz
    exact h (by simp [terminalSliceAmplitude, hz])
  have hcompact : HasCompactSupport (terminalSliceAmplitude (t (d-r)) P β L b) := by
    apply (isCompact_closedBall (0 : Fin l → ℝ) R).of_isClosed_subset isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx'
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx x hx'
  refine ⟨hf'c, hcompact, ?_⟩
  intro ν
  have ht := latticeFourierIntegral_decay_of_bounded_derivatives hf'c (by positivity : 0 ≤ T*R^N) hx hB ν
  exact ht.trans (mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) (by positivity))

end

end Birch
