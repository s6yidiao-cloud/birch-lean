import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Recovering coefficients from a finite family with small correlations -/

namespace Birch

open scoped BigOperators

/-- If the diagonal correlations of a finite real family are at least `M`
and the off-diagonal correlations have absolute value at most `μ`, then
the squared norm of each linear combination controls its coefficients. -/
theorem gram_diagonal_dominance {ι α : Type*} (E : Finset ι) (U : Finset α)
    (w : ι → α → ℝ) (x : ι → ℝ) (M μ : ℝ) (hμ : 0 ≤ μ)
    (hdiag : ∀ i ∈ E, M ≤ ∑ a ∈ U, (w i a)^2)
    (hoff : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → |∑ a ∈ U, w i a * w j a| ≤ μ) :
    (M - μ * (E.card : ℝ)) * (∑ i ∈ E, (x i)^2) ≤
      ∑ a ∈ U, (∑ i ∈ E, x i * w i a)^2 := by
  classical
  let G (i j : ι) : ℝ := ∑ a ∈ U, w i a * w j a
  have hentry (i : ι) (hi : i ∈ E) (j : ι) (hj : j ∈ E) :
      (if i = j then M * (x i)^2 else 0) - (μ / 2) * ((x i)^2 + (x j)^2) ≤
        (x i * x j) * G i j := by
    by_cases he : i = j
    · subst j
      simp only [ite_true, ← pow_two (x i)]
      have hG : M ≤ G i i := by simpa only [G, pow_two] using hdiag i hi
      have hmul := mul_le_mul_of_nonneg_left hG (sq_nonneg (x i))
      nlinarith [mul_nonneg hμ (sq_nonneg (x i))]
    · simp only [ite_eq_right he, zero_sub]
      have hG : |G i j| ≤ μ := hoff i hi j hj he
      have hprod : |x i * x j| ≤ ((x i)^2 + (x j)^2) / 2 := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
      have huv : |(x i * x j) * G i j| ≤ (μ / 2) * ((x i)^2 + (x j)^2) := by
        rw [abs_mul]
        calc
          _ ≤ (((x i)^2 + (x j)^2) / 2) * μ :=
            mul_le_mul hprod hG (abs_nonneg _) (by positivity)
          _ = _ := by ring
      exact (neg_le_neg huv).trans (neg_abs_le _)
  have hsum := Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hentry i hi j hj
  calc
    _ = ∑ i ∈ E, ∑ j ∈ E,
        ((if i = j then M * (x i)^2 else 0) - (μ / 2) * ((x i)^2 + (x j)^2)) := by
      have hd : (∑ i ∈ E, ∑ j ∈ E, if i = j then M * (x i)^2 else 0) =
          M * ∑ i ∈ E, (x i)^2 := by
        simp_rw [Finset.sum_ite_eq]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi => ite_eq_left hi
      have hp : (∑ i ∈ E, ∑ j ∈ E, (μ / 2) * (x i)^2) =
          (E.card : ℝ) * (μ / 2) * ∑ i ∈ E, (x i)^2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc, Finset.mul_sum]
      have hswap : (∑ i ∈ E, ∑ j ∈ E, (μ / 2) * (x j)^2) =
          ∑ i ∈ E, ∑ _j ∈ E, (μ / 2) * (x i)^2 := Finset.sum_comm
      simp_rw [Finset.sum_sub_distrib, mul_add, Finset.sum_add_distrib]
      rw [hd, hswap, hp]
      ring
    _ ≤ ∑ i ∈ E, ∑ j ∈ E, (x i * x j) * G i j := hsum
    _ = _ := by
      simp_rw [G, Finset.mul_sum]
      trans ∑ i ∈ E, ∑ a ∈ U, ∑ j ∈ E, (x i * x j) * (w i a * w j a)
      · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring


/-- Uniform bounds on the observed rows recover each coefficient
when the diagonal correlations exceed the total off-diagonal allowance. -/
theorem abs_coefficient_le_of_gram_bounds {ι α : Type*} (E : Finset ι) (U : Finset α)
    (w : ι → α → ℝ) (x : ι → ℝ) {M μ ε : ℝ} (hμ : 0 ≤ μ)
    (hgap : 0 < M - μ * (E.card : ℝ))
    (hdiag : ∀ i ∈ E, M ≤ ∑ a ∈ U, (w i a)^2)
    (hoff : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → |∑ a ∈ U, w i a * w j a| ≤ μ)
    (hrows : ∀ a ∈ U, |∑ i ∈ E, x i * w i a| ≤ ε) {i : ι} (hi : i ∈ E) :
    |x i| ≤ Real.sqrt ((U.card : ℝ) * ε^2 / (M - μ * (E.card : ℝ))) := by
  have hsingle : (x i)^2 ≤ ∑ j ∈ E, (x j)^2 :=
    Finset.single_le_sum (f := fun j => (x j)^2) (fun j _ => sq_nonneg (x j)) hi
  have hsum : (∑ a ∈ U, (∑ j ∈ E, x j * w j a)^2) ≤ (U.card : ℝ) * ε^2 := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro a ha
    rw [← sq_abs (∑ j ∈ E, x j * w j a)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hrows a ha) _
  have h := (mul_le_mul_of_nonneg_left hsingle hgap.le).trans
    ((gram_diagonal_dominance E U w x M μ hμ hdiag hoff).trans hsum)
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact (le_div_iff₀ hgap).mpr (by rwa [mul_comm])

/-- Recover a coefficient at an exceptional index from full correlations
and row bounds available off an exceptional set. The omitted rows affect
each correlation by at most the number omitted times the squared bound
on a matrix entry. -/
theorem abs_coefficient_le_of_full_gram_bounds {ι α : Type*} [Fintype ι] [Fintype α]
    (E : Finset ι) (J : Finset α) (w : ι → α → ℝ) (x : ι → ℝ)
    {M μ R ε η : ℝ} (hμ : 0 ≤ μ) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hw : ∀ i a, |w i a| ≤ R)
    (hdiag : ∀ i ∈ E, M ≤ ∑ a : α, (w i a)^2)
    (hoff : ∀ i ∈ E, ∀ j ∈ E, i ≠ j → |∑ a : α, w i a * w j a| ≤ μ)
    (hsmall : ∀ i ∉ E, |x i| ≤ ε)
    (hrows : ∀ a ∉ J, |∑ i : ι, x i * w i a| ≤ η) :
    let L := (J.card : ℝ) * R^2
    let gap := M - L - (μ + L) * (E.card : ℝ)
    0 < gap → ∀ i ∈ E,
      |x i| ≤ Real.sqrt ((Fintype.card α : ℝ) * (η + (Fintype.card ι : ℝ) * ε * R)^2 / gap) := by
  classical
  intro L gap hgap i hi
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hU {j k : ι} : |∑ a ∈ J, w j a * w k a| ≤ L := by
    dsimp [L]
    calc
      _ ≤ ∑ a ∈ J, |w j a * w k a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ J, R^2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [abs_mul, pow_two]
        exact mul_le_mul (hw j a) (hw k a) (abs_nonneg _) hR
      _ = _ := by simp
  have hJ (v : α → ℝ) : (∑ a ∈ J, v a) + (∑ a ∈ Jᶜ, v a) = ∑ a, v a :=
    Finset.sum_add_sum_compl J v
  have hdiag' (j : ι) (hj : j ∈ E) : M - L ≤ ∑ a ∈ Jᶜ, (w j a)^2 := by
    have hsplit := hJ (fun a => (w j a)^2)
    have hupper : (∑ a ∈ J, (w j a)^2) ≤ L := by
      exact (le_abs_self _).trans (by simpa only [pow_two] using hU (j := j) (k := j))
    linarith [hdiag j hj]
  have hoff' (j : ι) (hj : j ∈ E) (k : ι) (hk : k ∈ E) (hjk : j ≠ k) :
      |∑ a ∈ Jᶜ, w j a * w k a| ≤ μ + L := by
    have hs : (∑ a ∈ Jᶜ, w j a * w k a) =
        (∑ a : α, w j a * w k a) - ∑ a ∈ J, w j a * w k a :=
      eq_sub_of_add_eq (by rw [add_comm]; exact hJ _)
    rw [hs]
    exact (abs_sub _ _).trans (add_le_add (hoff j hj k hk hjk) hU)
  have hrows' (a : α) (ha : a ∈ Jᶜ) :
      |∑ j ∈ E, x j * w j a| ≤ η + (Fintype.card ι : ℝ) * ε * R := by
    have hs : (∑ j ∈ E, x j * w j a) =
        (∑ j : ι, x j * w j a) - ∑ j ∈ Eᶜ, x j * w j a :=
      eq_sub_of_add_eq (Finset.sum_add_sum_compl E _)
    rw [hs]
    refine (abs_sub _ _).trans (add_le_add (hrows a (Finset.mem_compl.mp ha)) ?_)
    calc
      _ ≤ ∑ j ∈ Eᶜ, |x j * w j a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Eᶜ, ε * R := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul (hsmall j (Finset.mem_compl.mp hj)) (hw j a) (abs_nonneg _) hε
      _ = ((Eᶜ).card : ℝ) * (ε * R) := by simp
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ Eᶜ) (by positivity)
  refine (abs_coefficient_le_of_gram_bounds E Jᶜ w x (add_nonneg hμ hL)
    hgap hdiag' hoff' hrows' hi).trans (Real.sqrt_le_sqrt ?_)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Finset.card_le_univ Jᶜ) (sq_nonneg _)) hgap.le

end Birch
