import Birch.PhaseDifferencing
import Birch.CompletionReduction

/-! # Iterating the selected polynomial differencing step

The chain records the polynomial, translated weight, and frequency after each
actual choice of lattice direction. The finite direction counts remain an
explicit input to the construction.
-/

open scoped BigOperators ContDiff

namespace Birch

noncomputable section

/-- Weights vanishing outside the open unit cube. -/
def CubeSupported {n : ℕ} (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ y, w y ≠ 0 → ∀ i, |y i| < 1

/-- Height of the zero-indexed step `i` of a chain of length `k`. -/
def differencingHeight (k : ℕ) (Q : ℝ) (i : ℕ) : ℝ := Q ^ (1 / (2 : ℝ) ^ (k-1-i))

/-- The data in the exponential sum at a selected step. -/
structure PolynomialDifferencingState (n : ℕ) where
  form : IntForm n
  weight : (Fin n → ℝ) → ℝ
  frequency : ℝ

namespace PolynomialDifferencingState

/-- Perform the dilated difference with a specified direction. -/
def step {n : ℕ} (P : ℝ) (m : ℤ) (u : Fin n → ℤ) (t : PolynomialDifferencingState n) :
    PolynomialDifferencingState n :=
  ⟨dilatedDifference m u t.form, differencedWeight t.weight P m u, (m : ℝ) * t.frequency⟩

/-- The normalized magnitude at this step. -/
def magnitude {n : ℕ} (P : ℝ) (t : PolynomialDifferencingState n) : ℝ :=
  ‖exponentialSum t.form t.weight P t.frequency‖ / P^n

theorem step_cubeSupported {n : ℕ} {t : PolynomialDifferencingState n} (hw : CubeSupported t.weight)
    (P : ℝ) (m : ℤ) (u : Fin n → ℤ) : CubeSupported (t.step P m u).weight := by
  intro y hy
  apply hw y
  intro hy0
  exact hy (by simp [step, differencedWeight, hy0])

end PolynomialDifferencingState

/-- The sequence uses exactly the chosen directions and their admissible boxes. -/
def IsPolynomialDifferencingChain {n k : ℕ} (P Q : ℝ) (m : ℕ → ℤ)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (α : ℝ)
    (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ) : Prop :=
  t 0 = ⟨F,w,α⟩ ∧ ∀ i < k,
    u i ∈ differencingDirections n (differencingHeight k Q i) ∧ t (i+1) = (t i).step P (m i) (u i)

/-- The frequency of a chain is the original frequency multiplied by its dilation product. -/
theorem IsPolynomialDifferencingChain.frequency {n k : ℕ} {P Q : ℝ} {m : ℕ → ℤ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} {α : ℝ}
    {t : ℕ → PolynomialDifferencingState n} {u : ℕ → Fin n → ℤ}
    (ht : IsPolynomialDifferencingChain (k := k) P Q m F w α t u) {i : ℕ} (hi : i ≤ k) :
    (t i).frequency = (∏ j ∈ Finset.range i, (m j : ℝ)) * α := by
  induction i with
  | zero => simp [ht.1]
  | succ i ih =>
      rw [(ht.2 i (by omega)).2, PolynomialDifferencingState.step, ih (by omega), Finset.prod_range_succ]
      ring


/-- The normalized chain starts within the cube supplied by the transverse weight. -/
theorem TransverseWeight.cubeSupported {n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hw : TransverseWeight F w) : CubeSupported w := by
  intro y hy
  exact hw.support_box (subset_tsupport w hy)

/-- All actual differenced weights vanish outside the same open cube. -/
theorem IsPolynomialDifferencingChain.cubeSupported_weight {n k : ℕ} {P Q : ℝ} {m : ℕ → ℤ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} {α : ℝ}
    {t : ℕ → PolynomialDifferencingState n} {u : ℕ → Fin n → ℤ}
    (ht : IsPolynomialDifferencingChain (k := k) P Q m F w α t u)
    (hw : CubeSupported w) {i : ℕ} (hi : i ≤ k) : CubeSupported (t i).weight := by
  induction i with
  | zero => simpa only [ht.1] using hw
  | succ i ih =>
      rw [(ht.2 i (by omega)).2]
      exact PolynomialDifferencingState.step_cubeSupported (ih (by omega)) _ _ _

/-- Each step drops the degree bound by one. -/
theorem IsPolynomialDifferencingChain.totalDegree_le {n d k : ℕ} {P Q : ℝ} {m : ℕ → ℤ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} {α : ℝ}
    {t : ℕ → PolynomialDifferencingState n} {u : ℕ → Fin n → ℤ}
    (ht : IsPolynomialDifferencingChain (k := k) P Q m F w α t u)
    (hF : F.totalDegree ≤ d) {i : ℕ} (hi : i ≤ k) : (t i).form.totalDegree ≤ d-i := by
  induction i with
  | zero => simpa only [ht.1, Nat.sub_zero] using hF
  | succ i ih =>
      rw [(ht.2 i (by omega)).2]
      exact (dilatedDifference_totalDegree_le _ _ _).trans (by have h := ih (by omega); omega)

/-- The leading homogeneous forms in an actual chain are the successive directional derivatives. -/
theorem IsPolynomialDifferencingChain.leadingForm_step {n d k : ℕ} {P Q : ℝ} {m : ℕ → ℤ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} {α : ℝ}
    {t : ℕ → PolynomialDifferencingState n} {u : ℕ → Fin n → ℤ}
    (ht : IsPolynomialDifferencingChain (k := k) P Q m F w α t u)
    (hF : F.totalDegree ≤ d) {i : ℕ} (hi : i < k) (hd : 2 ≤ d-i) :
    MvPolynomial.homogeneousComponent (d-(i+1)) (t (i+1)).form =
      directionalDerivative (u i) (MvPolynomial.homogeneousComponent (d-i) (t i).form) := by
  have he : d-(i+1) = (d-i)-1 := by omega
  rw [(ht.2 i hi).2, he]
  exact homogeneousComponent_dilatedDifference _ _ _ hd (ht.totalDegree_le hF hi.le)

/-- The weight stays smooth under the successive translated products. -/
theorem IsPolynomialDifferencingChain.contDiff_weight {n k : ℕ} {P Q : ℝ} {m : ℕ → ℤ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} {α : ℝ}
    {t : ℕ → PolynomialDifferencingState n} {u : ℕ → Fin n → ℤ}
    (ht : IsPolynomialDifferencingChain (k := k) P Q m F w α t u)
    (hw : ContDiff ℝ ∞ w) {i : ℕ} (hi : i ≤ k) : ContDiff ℝ ∞ (t i).weight := by
  induction i with
  | zero => simpa only [ht.1] using hw
  | succ i ih =>
      rw [(ht.2 i (by omega)).2]
      have h := ih (by omega)
      exact (h.comp (by fun_prop)).mul h

/-- Each singular-dimension class satisfies the required cardinality bound. The
function `s` attaches the supplied dimension to the indicated state form and step. -/
def PolynomialDirectionCounts {n k : ℕ} (d : ℕ) (Q : ℝ) (m : ℕ → ℤ) (s : ℕ → IntForm n → Fin (n+1))
    (K : ℝ) : Prop :=
  ∀ i < k, ∀ (g : IntForm n), g.totalDegree ≤ d-i → ∀ (j : Fin (n+1)),
    (((differencingDirections n (differencingHeight k Q i)).filter
      (fun u => s (i+1) (dilatedDifference (m i) u g) = j)).card : ℝ) ≤
        K * (differencingHeight k Q i) ^ ((n : ℝ) - ((j.val - (s i g).val : ℕ) : ℝ))

/-- `eq:selected` conditional on the finite direction counts. A genuine sequence
of directions attains the claimed power saving and keeps the transformed weights
in the original support cube. -/
theorem exists_selectedPolynomialChain_from_dimension {n d k : ℕ} {P Q K : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hK : 0 ≤ K)
    (m : ℕ → ℤ) (hm : ∀ i < k, 0 < m i ∧ (m i : ℝ) * differencingHeight k Q i ≤ P)
    (F : IntForm n) (hF : F.totalDegree ≤ d) (w : (Fin n → ℝ) → ℝ) (hw : CubeSupported w) (α : ℝ)
    (s : ℕ → IntForm n → Fin (n+1))
    (hcount : PolynomialDirectionCounts (k := k) d Q m s K) :
    ∃ (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
      IsPolynomialDifferencingChain (k := k) P Q m F w α t u ∧
      (∀ i, CubeSupported (t i).weight) ∧
      (‖exponentialSum F w P α‖ / P^n)^(2^k : ℕ) ≤
        ((10 : ℝ)^n * ((n : ℝ)+1) * K)^(2^k-1 : ℕ) *
          Q ^ (-(((s k (t k).form).val - (s 0 F).val : ℕ) : ℝ)) *
            (t k).magnitude P := by
  classical
  let C : ℝ := (10 : ℝ)^n * ((n : ℝ)+1) * K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hpos (i : ℕ) : 0 < differencingHeight k Q i := Real.rpow_pos_of_pos hQpos _
  have heach (i : ℕ) (hi : i < k) (a : PolynomialDifferencingState n) (hWa : CubeSupported a.weight)
      (hDa : a.form.totalDegree ≤ d-i) :
      ∃ v ∈ differencingDirections n (differencingHeight k Q i),
        (a.magnitude P)^2 ≤ C * (differencingHeight k Q i) ^
          (-((((s (i+1) (a.step P (m i) v).form).val - (s i a.form).val : ℕ) : ℝ))) *
            (a.step P (m i) v).magnitude P :=
    exponentialSum_differencing_of_direction_counts hP (hpos i) (hm i hi).1 (hm i hi).2
      a.form a.weight hWa a.frequency (fun v => s (i+1) (dilatedDifference (m i) v a.form))
      (s i a.form).val K (hcount i hi a.form hDa)
  let pick (i : ℕ) (a : PolynomialDifferencingState n) : Fin n → ℤ :=
    if h : i < k ∧ CubeSupported a.weight ∧ a.form.totalDegree ≤ d-i then
      Classical.choose (heach i h.1 a h.2.1 h.2.2) else 0
  have hpick (i : ℕ) (hi : i < k) (a : PolynomialDifferencingState n) (hWa : CubeSupported a.weight)
      (hDa : a.form.totalDegree ≤ d-i) :
      pick i a ∈ differencingDirections n (differencingHeight k Q i) ∧
        (a.magnitude P)^2 ≤ C * (differencingHeight k Q i) ^
          (-((((s (i+1) (a.step P (m i) (pick i a)).form).val - (s i a.form).val : ℕ) : ℝ))) *
            (a.step P (m i) (pick i a)).magnitude P := by
    unfold pick
    rw [dite_eq_left ⟨hi, hWa, hDa⟩]
    exact Classical.choose_spec (heach i hi a hWa hDa)
  let t : ℕ → PolynomialDifferencingState n :=
    Nat.rec ⟨F,w,α⟩ fun i a => a.step P (m i) (pick i a)
  let u := fun i => pick i (t i)
  have htS (i : ℕ) : t (i+1) = (t i).step P (m i) (u i) := rfl
  have hbox (i : ℕ) : CubeSupported (t i).weight := by
    induction i with
    | zero => exact hw
    | succ i ih => rw [htS]; exact PolynomialDifferencingState.step_cubeSupported ih _ _ _
  have hdegree (i : ℕ) : (t i).form.totalDegree ≤ d-i := by
    induction i with
    | zero =>
      change F.totalDegree ≤ d - 0
      exact hF
    | succ i ih =>
      rw [htS i]
      exact (dilatedDifference_totalDegree_le _ _ _).trans (by omega)
  have hchain : IsPolynomialDifferencingChain (k := k) P Q m F w α t u :=
    ⟨rfl, fun i hi => ⟨(hpick i hi (t i) (hbox i) (hdegree i)).1, htS i⟩⟩
  let A (i : ℕ) := (t i).magnitude P
  let dim (i : ℕ) := (s i (t i).form).val
  have hA (i : ℕ) : 0 ≤ A i := by dsimp [A, PolynomialDifferencingState.magnitude]; positivity
  have hstep (i : ℕ) (hi : i < k) : (A i)^2 ≤
      C * Q ^ (-(↑(dim (i+1) - dim i) : ℝ) / ((2 : ℝ)^(k-1-i))) * A (i+1) := by
    have hh := (hpick i hi (t i) (hbox i) (hdegree i)).2
    change (A i)^2 ≤ C * (differencingHeight k Q i) ^
      (-((((s (i+1) ((t i).step P (m i) (u i)).form).val - dim i : ℕ) : ℝ))) *
        ((t i).step P (m i) (u i)).magnitude P at hh
    rw [← htS] at hh
    change (A i)^2 ≤ C * (differencingHeight k Q i) ^ (-(↑(dim (i+1) - dim i) : ℝ)) * A (i+1) at hh
    have hpower : (differencingHeight k Q i) ^ (-(↑(dim (i+1) - dim i) : ℝ)) =
        Q ^ (-(↑(dim (i+1) - dim i) : ℝ) / ((2 : ℝ)^(k-1-i))) := by
      rw [differencingHeight, ← Real.rpow_mul hQpos.le]
      congr 1
      ring
    rwa [hpower] at hh
  exact ⟨t, u, hchain, hbox,
    iterated_square_savings_from_dimension k A dim Q C hQ hC hA hstep⟩

/-- At initial gradient dimension zero the saving uses the terminal dimension. -/
theorem exists_selectedPolynomialChain {n d k : ℕ} {P Q K : ℝ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hK : 0 ≤ K)
    (m : ℕ → ℤ) (hm : ∀ i < k, 0 < m i ∧ (m i : ℝ) * differencingHeight k Q i ≤ P)
    (F : IntForm n) (hF : F.totalDegree ≤ d) (w : (Fin n → ℝ) → ℝ) (hw : CubeSupported w) (α : ℝ)
    (s : ℕ → IntForm n → Fin (n+1)) (hs₀ : (s 0 F).val = 0)
    (hcount : PolynomialDirectionCounts (k := k) d Q m s K) :
    ∃ (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
      IsPolynomialDifferencingChain (k := k) P Q m F w α t u ∧
      (∀ i, CubeSupported (t i).weight) ∧
      (‖exponentialSum F w P α‖ / P^n)^(2^k : ℕ) ≤
        ((10 : ℝ)^n * ((n : ℝ)+1) * K)^(2^k-1 : ℕ) *
          Q ^ (-((s k (t k).form).val : ℝ)) * (t k).magnitude P := by
  simpa only [hs₀, Nat.sub_zero] using
    exists_selectedPolynomialChain_from_dimension hP hQ hK m hm F hF w hw α s hcount

end

end Birch
