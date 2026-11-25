import Birch.MorseAuxiliaryPhase
import Birch.DeligneTensorPhase

/-! # Finite correlations of translated auxiliary value counts -/

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

/-- The number of preimages of a single value of a function on a finite set. -/
def finiteValueCount {α β : Type*} [Fintype α] (h : α → β) (t : β) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => h x = t).card

private theorem finiteValueCount_eq_sum {α β : Type*} [Fintype α] [DecidableEq β]
    (h : α → β) (t : β) :
    (finiteValueCount h t : ℝ) = ∑ x : α, if h x = t then 1 else 0 := by
  classical
  rw [finiteValueCount, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem sum_finiteValueCount {α β : Type*} [Fintype α] [Fintype β]
    (h : α → β) : ∑ t : β, (finiteValueCount h t : ℝ) = Fintype.card α := by
  classical
  simp_rw [finiteValueCount_eq_sum]
  rw [Finset.sum_comm]
  simp

theorem sum_finiteValueCount_shift {α β : Type*} [Fintype α] [Fintype β] [AddCommGroup β]
    (h : α → β) (s : β) :
    ∑ t : β, (finiteValueCount h (t-s) : ℝ) = Fintype.card α := by
  calc
    _ = ∑ t : β, (finiteValueCount h t : ℝ) :=
      Fintype.sum_equiv (Equiv.subRight s) _ _ fun _ => rfl
    _ = _ := sum_finiteValueCount h

/-- The two translated histograms correlate by counting the differences
of the underlying function values. -/
theorem sum_mul_finiteValueCount_shift {α β : Type*} [Fintype α] [Fintype β] [AddCommGroup β]
    (h : α → β) (s v : β) :
    ∑ t : β, (finiteValueCount h (t-s) : ℝ) * (finiteValueCount h (t-v) : ℝ) =
      (finiteValueCount (fun z : α × α => h z.1 - h z.2) (v-s) : ℝ) := by
  classical
  simp_rw [finiteValueCount_eq_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have he (t : β) : (h x = t - s) ↔ t = h x + s := by
    constructor
    · intro ht
      rw [ht]
      abel
    · rintro rfl
      abel
  simp_rw [he, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 1
  apply propext
  constructor
  · intro he
    rw [he]
    abel
  · intro he
    calc
      h y = h x - (h x - h y) := by abel
      _ = _ := by rw [he]; abel

/-- When the domain and range have equal cardinality, centering the
histograms by one subtracts exactly the size of the range from each
correlation. -/
theorem sum_mul_centered_finiteValueCount_shift {α β : Type*}
    [Fintype α] [Fintype β] [AddCommGroup β]
    (hcard : Fintype.card α = Fintype.card β) (h : α → β) (s v : β) :
    ∑ t : β, ((finiteValueCount h (t-s) : ℝ)-1) * ((finiteValueCount h (t-v) : ℝ)-1) =
      (finiteValueCount (fun z : α × α => h z.1 - h z.2) (v-s) : ℝ) - Fintype.card β := by
  have h (t : β) : ((finiteValueCount h (t-s) : ℝ)-1) *
      ((finiteValueCount h (t-v) : ℝ)-1) =
      ((finiteValueCount h (t-s) : ℝ) * (finiteValueCount h (t-v) : ℝ) -
      (finiteValueCount h (t-s) : ℝ) - (finiteValueCount h (t-v) : ℝ)) + 1 := by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_mul_finiteValueCount_shift, sum_finiteValueCount_shift, sum_finiteValueCount_shift]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
  ring


variable {K : Type*} [Field K] [Fintype K]

private theorem finiteValueCount_eq_card {α β : Type*} [Fintype α] [DecidableEq β]
    (h : α → β) (s : β) :
    finiteValueCount h s = Fintype.card {x : α // h x = s} := by
  classical
  rw [finiteValueCount, Fintype.card_subtype]
  exact congrArg Finset.card (Finset.ext fun _ => by simp)

/-- The centered histogram for the scaled Morse auxiliary phase. -/
def centeredMorseValueCount (r : ℕ) (scale t : K) : ℝ :=
  (finiteValueCount (fun z : K => scale * (morseAuxiliaryPolynomial r).eval z) t : ℝ) - 1

/-- The correlation of two columns is the affine difference-curve
error at the corresponding difference of their shifts. -/
theorem centeredMorseValueCount_correlation (r : ℕ) {scale : K} (hscale : scale ≠ 0) (s v : K) :
    ∑ t : K, centeredMorseValueCount r scale (t-s) * centeredMorseValueCount r scale (t-v) =
      (affinePolynomialLevelCount (morseAuxiliaryDifference r) ((v-s)/scale) : ℝ) -
        Fintype.card K := by
  classical
  let h (z : K) := scale * (morseAuxiliaryPolynomial r).eval z
  change (∑ t : K, ((finiteValueCount h (t-s) : ℝ)-1) *
      ((finiteValueCount h (t-v) : ℝ)-1)) = _
  rw [sum_mul_centered_finiteValueCount_shift rfl, finiteValueCount_eq_card]
  unfold affinePolynomialLevelCount
  rw [← Fintype.card_subtype]
  congr 2
  apply Fintype.card_congr
  apply (finTwoArrowEquiv K).symm.subtypeEquiv
  intro z
  change h z.1 - h z.2 = v-s ↔
    (morseAuxiliaryDifference r).eval ((finTwoArrowEquiv K).symm z) = (v-s)/scale
  simp only [h, eval_morseAuxiliaryDifference, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [← mul_sub, eq_div_iff hscale]
  rw [mul_comm scale]

/-- The diagonal of the translated Gram matrix includes all residual
collision points, except for at most r−1 points on the diagonal. -/
theorem affinePolynomialLevelCount_morseAuxiliaryDifference_zero_lower {r : ℕ} (hr : 2 ≤ r) :
    Fintype.card K + affinePolynomialLevelCount (morseAuxiliaryResidualLeading (K := K) r) 1 ≤
      affinePolynomialLevelCount (morseAuxiliaryDifference (K := K) r) 0 + (r-1) := by
  classical
  let d : Finset (Fin 2 → K) := Finset.univ.filter (fun x => x 0 = x 1)
  let c : Finset (Fin 2 → K) := Finset.univ.filter
    (fun x => (morseAuxiliaryResidualLeading r).eval x = 1)
  have hd : d = Finset.univ.image (fun z : K => fun _ : Fin 2 => z) := by
    ext x
    simp only [d, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨x 0, ?_⟩
      funext i
      fin_cases i
      · rfl
      · exact h
    · rintro ⟨_, rfl⟩
      rfl
  have hdc : d.card = Fintype.card K := by
    rw [hd, Finset.card_image_of_injective Finset.univ (fun _ _ h => congrFun h 0), Finset.card_univ]
  have hu : d ∪ c = Finset.univ.filter
      (fun x => (morseAuxiliaryDifference r).eval x = 0) := by
    ext x
    simpa only [d, c, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using
      (eval_morseAuxiliaryDifference_eq_zero_iff r x).symm
  have hi : (d ∩ c).card ≤ r-1 := by
    let P : Polynomial K := Polynomial.C (r : K) * Polynomial.X^(r-1) - 1
    have hP : P ≠ 0 := by
      intro hz
      have h := congrArg (Polynomial.eval (0 : K)) hz
      have hpos : r-1 ≠ 0 := by omega
      simp [P, hpos] at h
    have hm : Set.MapsTo (fun x : Fin 2 → K => x 0) (↑(d ∩ c) : Set (Fin 2 → K))
        (↑P.roots.toFinset : Set K) := by
      intro x hx
      simp only [Finset.mem_coe, Finset.mem_inter, d, c, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      have he : x = fun _ => x 0 := by
        funext i
        fin_cases i
        · rfl
        · exact hx.1.symm
      have hvalue := hx.2
      rw [he, eval_morseAuxiliaryResidualLeading_diagonal] at hvalue
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
      simpa [P, sub_eq_zero] using hvalue
    refine (Finset.card_le_card_of_injOn _ hm ?_).trans ?_
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
      have hy' := (Finset.mem_filter.mp (Finset.mem_inter.mp hy).1).2
      funext i
      fin_cases i
      · exact hxy
      · exact hx'.symm.trans (hxy.trans hy')
    · refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans ?_)
      exact (Polynomial.natDegree_sub_le _ _).trans
        (max_le (Polynomial.natDegree_mul_le.trans (by simp)) (by simp))
  have hsum := Finset.card_union_add_card_inter d c
  rw [hu, hdc] at hsum
  change affinePolynomialLevelCount (morseAuxiliaryDifference r) 0 + (d ∩ c).card =
    Fintype.card K + affinePolynomialLevelCount (morseAuxiliaryResidualLeading r) 1 at hsum
  omega


/-- The centered histogram is bounded in absolute value by the degree. -/
theorem abs_centeredMorseValueCount_le {r : ℕ} (hr : 2 ≤ r) {scale : K}
    (hscale : scale ≠ 0) (t : K) : |centeredMorseValueCount r scale t| ≤ (r : ℝ) := by
  classical
  let P : Polynomial K := morseAuxiliaryPolynomial r - Polynomial.C (t / scale)
  have hm : (morseAuxiliaryPolynomial (K := K) r).natDegree = r := by
    unfold morseAuxiliaryPolynomial
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    simpa only [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] using
      (show 1 < r by omega)
  have hd : P.natDegree = r := by
    unfold P
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt, hm]
    rw [Polynomial.natDegree_C, hm]
    omega
  have hP : P ≠ 0 := by intro h; rw [h, Polynomial.natDegree_zero] at hd; omega
  have hcount : finiteValueCount (fun z : K => scale * (morseAuxiliaryPolynomial r).eval z) t ≤ r := by
    unfold finiteValueCount
    refine (Finset.card_le_card (t := P.roots.toFinset) ?_).trans
      ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hd.le))
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    dsimp only [P]
    rw [Polynomial.eval_sub, Polynomial.eval_C, sub_eq_zero, eq_div_iff hscale, mul_comm]
    exact hx
  rw [abs_le]
  constructor
  · have h1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    unfold centeredMorseValueCount
    linarith [show (0 : ℝ) ≤ finiteValueCount
      (fun z : K => scale * (morseAuxiliaryPolynomial r).eval z) t by positivity]
  · unfold centeredMorseValueCount
    have : (finiteValueCount (fun z : K => scale * (morseAuxiliaryPolynomial r).eval z) t : ℝ) ≤ r :=
      by exact_mod_cast hcount
    linarith


/-- A scale can be chosen so that nonzero differences of exceptional levels
avoid all differences of auxiliary critical values. -/
theorem exists_scale_avoiding_morse_critical_differences
    {F L : Type*} [Field F] [Fintype F] [Field L] (φ : F →+* L)
    (r : ℕ) (E : Finset F)
    (hcard : E.card^2 * (r-1)^2 + 1 < Fintype.card F) :
    ∃ scale : F, scale ≠ 0 ∧ ∀ s ∈ E, ∀ v ∈ E, s ≠ v →
      ∀ u ∈ morseAuxiliaryCriticalValues (K := L) r,
        ∀ w ∈ morseAuxiliaryCriticalValues (K := L) r,
          φ ((v-s) / scale) ≠ u-w := by
  classical
  let C := morseAuxiliaryCriticalValues (K := L) r
  let R : Finset L := ((E.product E).product (C.product C)).image
    (fun z => φ (z.1.2 - z.1.1) / (z.2.1 - z.2.2))
  let T : Finset F := Finset.univ.filter (fun b => φ b ∈ R)
  have hT : T.card ≤ R.card :=
    Finset.card_le_card_of_injOn φ (fun _ hz => (Finset.mem_filter.mp hz).2)
      φ.injective.injOn
  have hR : R.card ≤ E.card^2 * (r-1)^2 := by
    unfold R
    refine Finset.card_image_le.trans ?_
    change ((E ×ˢ E) ×ˢ (C ×ˢ C)).card ≤ _
    rw [Finset.card_product, Finset.card_product, Finset.card_product, ← pow_two, ← pow_two]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (card_morseAuxiliaryCriticalValues_le r) 2)
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert 0 T) (t := Finset.univ) (by
      rw [Finset.card_univ]
      exact ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hT.trans hR) 1)).trans_lt hcard)
  rw [Finset.mem_insert, not_or] at hb
  refine ⟨b, hb.1, fun s hs v hv hsv u hu w hw he => ?_⟩
  apply hb.2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
  refine ⟨((s,v),(u,w)), Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨hs,hv⟩, Finset.mem_product.mpr ⟨hu,hw⟩⟩, ?_⟩
  change φ (v-s) / (u-w) = φ b
  have hnum : φ (v-s) ≠ 0 := (map_ne_zero φ).mpr (sub_ne_zero.mpr hsv.symm)
  rw [map_div₀] at he
  have hden : u-w ≠ 0 := fun h => (div_ne_zero hnum ((map_ne_zero φ).mpr hb.1)) (he.trans h)
  apply (div_eq_iff hden).mpr
  rw [← he, mul_comm (φ b), div_mul_cancel₀ _ ((map_ne_zero φ).mpr hb.1)]

/-- The prime-field values hit by an algebraic critical value of the
original phase plus a scaled auxiliary critical value. -/
def morseExceptionalRows {F L : Type*} [Field F] [Fintype F] [Field L]
    (φ : F →+* L) (r : ℕ) (D : Finset L) (scale : F) : Finset F := by
  classical
  exact Finset.univ.filter fun t => φ t ∈
    (D.product (morseAuxiliaryCriticalValues (K := L) r)).image
      (fun uv => uv.1 + φ scale * uv.2)

theorem mem_morseExceptionalRows_iff {F L : Type*} [Field F] [Fintype F] [Field L]
    (φ : F →+* L) (r : ℕ) (D : Finset L) (scale : F) (t : F) :
    t ∈ morseExceptionalRows φ r D scale ↔
      ∃ u ∈ D, ∃ w ∈ morseAuxiliaryCriticalValues (K := L) r, φ t = u + φ scale * w := by
  classical
  unfold morseExceptionalRows
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨u,w⟩,hm,h⟩
    obtain ⟨hu,hw⟩ := Finset.mem_product.mp hm
    exact ⟨u,hu,w,hw,h.symm⟩
  · rintro ⟨u,hu,w,hw,h⟩
    exact ⟨(u,w),Finset.mem_product.mpr ⟨hu,hw⟩,h.symm⟩

theorem card_morseExceptionalRows_le {F L : Type*} [Field F] [Fintype F] [Field L]
    (φ : F →+* L) (r : ℕ) (D : Finset L) (scale : F) :
    (morseExceptionalRows φ r D scale).card ≤ D.card * (r-1) := by
  classical
  unfold morseExceptionalRows
  refine (Finset.card_le_card_of_injOn φ (fun _ ht => (Finset.mem_filter.mp ht).2)
    φ.injective.injOn).trans (Finset.card_image_le.trans ?_)
  change (D ×ˢ morseAuxiliaryCriticalValues (K := L) r).card ≤ _
  rw [Finset.card_product]
  exact Nat.mul_le_mul_left _ (card_morseAuxiliaryCriticalValues_le r)


/-- Addition of independent finite variables convolves their value counts. -/
theorem sum_mul_finiteValueCount_add {α γ β : Type*}
    [Fintype α] [Fintype γ] [Fintype β] [AddCommGroup β] (g : α → β) (h : γ → β) (t : β) :
    ∑ s : β, (finiteValueCount g s : ℝ) * (finiteValueCount h (t-s) : ℝ) =
      (finiteValueCount (fun z : α × γ => g z.1 + h z.2) t : ℝ) := by
  classical
  simp_rw [finiteValueCount_eq_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  congr 1
  apply propext
  exact eq_sub_iff_add_eq'.trans (by rw [add_comm])

/-- The centered auxiliary histogram sends any choice of centered input
counts to the centered count of the summed phase. -/
theorem sum_mul_centeredMorseValueCount {α : Type*} [Fintype α]
    (g : α → K) (r : ℕ) (scale t : K) (m : ℝ) :
    ∑ s : K, ((finiteValueCount g s : ℝ)-m) * centeredMorseValueCount r scale (t-s) =
      (finiteValueCount (fun z : α × K =>
        g z.1 + scale * (morseAuxiliaryPolynomial r).eval z.2) t : ℝ) - Fintype.card α := by
  let h (z : K) := scale * (morseAuxiliaryPolynomial r).eval z
  have he (s : K) : ((finiteValueCount g s : ℝ)-m) * centeredMorseValueCount r scale (t-s) =
      (finiteValueCount g s : ℝ) * (finiteValueCount h (t-s) : ℝ) -
        (finiteValueCount g s : ℝ) - m * ((finiteValueCount h (t-s) : ℝ) - 1) := by
    unfold centeredMorseValueCount
    change ((finiteValueCount g s : ℝ)-m) * ((finiteValueCount h (t-s) : ℝ)-1) = _
    ring
  have hmass : ∑ s : K, (finiteValueCount h (t-s) : ℝ) = Fintype.card K := by
    calc
      _ = ∑ s : K, (finiteValueCount h s : ℝ) :=
        Fintype.sum_equiv (Equiv.subLeft t) _ _ fun _ => rfl
      _ = _ := sum_finiteValueCount h
  simp_rw [he, Finset.sum_sub_distrib]
  rw [sum_mul_finiteValueCount_add, sum_finiteValueCount, ← Finset.mul_sum,
    Finset.sum_sub_distrib, hmass]
  simp [h]

theorem finiteValueCount_comp_equiv {α β γ : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (g : β → γ) (t : γ) :
    finiteValueCount (g ∘ e) t = finiteValueCount g t := by
  classical
  rw [finiteValueCount_eq_card, finiteValueCount_eq_card]
  exact Fintype.card_congr (e.subtypeEquiv fun _ => Iff.rfl)

theorem finiteValueCount_eval_eq_affinePolynomialLevelCount {n : ℕ}
    (g : MvPolynomial (Fin n) K) (t : K) :
    finiteValueCount (fun x => g.eval x) t = affinePolynomialLevelCount g t := rfl

end

end Birch
