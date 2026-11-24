import Birch.LatticeSummable
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Summing terminal Fourier weights

A product of one-dimensional reciprocal-square weights bounds the weight
with the sup norm used in the terminal completion.
-/

namespace Birch

open scoped BigOperators
noncomputable section

private def coordWeight (θ : ℝ) (j : ℤ) : ℝ :=
  (1 + θ * |(j : ℝ)|)^(-2 : ℝ)

private theorem coordWeight_nonneg {θ : ℝ} (hθ : 0 < θ) (j : ℤ) :
    0 ≤ coordWeight θ j := Real.rpow_nonneg (by positivity) _

private theorem coordWeight_tail {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun j : ℕ => coordWeight θ ((j+1 : ℕ) : ℤ)) ∧
      (∑' j : ℕ, coordWeight θ ((j+1 : ℕ) : ℤ)) ≤ θ⁻¹ := by
  let b (j : ℕ) := (1 + θ * (j : ℝ))⁻¹ / θ
  have hb (j : ℕ) : 0 ≤ b j := by unfold b; positivity
  have hstep (j : ℕ) : coordWeight θ ((j+1 : ℕ) : ℤ) ≤ b j - b (j+1) := by
    let A := 1 + θ * (j : ℝ)
    let B := 1 + θ * (j+1 : ℝ)
    have hA : 0 < A := by unfold A; positivity
    have hB : 0 < B := by unfold B; positivity
    have hAB : B-A = θ := by unfold A B; ring
    have hABle : A ≤ B := by linarith
    have he (z : ℝ) (hz : 0 < z) : z^(-2 : ℝ) = 1/(z^2) := by
      rw [Real.rpow_neg hz.le, Real.rpow_two, one_div]
    unfold coordWeight
    push_cast
    rw [abs_of_nonneg (by positivity : 0 ≤ (j : ℝ)+1)]
    change B^(-2 : ℝ) ≤ b j-b (j+1)
    rw [he B hB]
    calc
      _ ≤ 1/(A*B) := by
        apply one_div_le_one_div_of_le (mul_pos hA hB)
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hABle hB.le
      _ = _ := by
        have hsucc : b (j+1) = B⁻¹ / θ := by unfold b B; push_cast; rfl
        rw [hsucc]
        change 1/(A*B) = A⁻¹ / θ - B⁻¹ / θ
        field_simp
        linarith
  have hsums (k : ℕ) : (∑ j ∈ Finset.range k, coordWeight θ ((j+1 : ℕ) : ℤ)) ≤ θ⁻¹ := by
    calc
      _ ≤ ∑ j ∈ Finset.range k, (b j - b (j+1)) := Finset.sum_le_sum fun j _ => hstep j
      _ = b 0 - b k := by
        induction k with
        | zero => simp
        | succ k ih => rw [Finset.sum_range_succ, ih]; ring
      _ ≤ θ⁻¹ := by
        have hzero : b 0 = θ⁻¹ := by simp [b, one_div]
        rw [hzero]
        exact sub_le_self _ (hb _)
  exact ⟨summable_of_sum_range_le (fun _ => coordWeight_nonneg hθ _) hsums,
    Real.tsum_le_of_sum_range_le (fun _ => coordWeight_nonneg hθ _) hsums⟩

private theorem coordWeight_sum {θ : ℝ} (hθ : 0 < θ) :
    Summable (coordWeight θ) ∧ (∑' j : ℤ, coordWeight θ j) ≤ 1 + 2 / θ := by
  obtain ⟨hs, hbound⟩ := coordWeight_tail hθ
  have hEven : Function.Even (coordWeight θ) := by
    intro j
    simp [coordWeight]
  have hsNat : Summable (fun j : ℕ => coordWeight θ (j : ℤ)) :=
    (summable_nat_add_iff 1).mp (by simpa using hs)
  have hsInt : Summable (coordWeight θ) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    exact ⟨hsNat, hsNat.congr fun j => (hEven (j : ℤ)).symm⟩
  refine ⟨hsInt, ?_⟩
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hEven hsInt]
  have hzero : coordWeight θ 0 = 1 := by simp [coordWeight]
  rw [hzero]
  have htail : (∑' j : ℕ+, coordWeight θ (j : ℤ)) ≤ θ⁻¹ :=
    (tsum_pnat_eq_tsum_succ (f := fun j : ℕ => coordWeight θ (j : ℤ))).trans_le hbound
  rw [div_eq_mul_inv, nsmul_eq_mul]
  norm_num
  linarith

private theorem sum_pi_prod {g : ℤ → ℝ} (hg : Summable g) (hg₀ : ∀ j, 0 ≤ g j) (l : ℕ) :
    Summable (fun x : Fin l → ℤ => ∏ i, g (x i)) ∧
      (∑' x : Fin l → ℤ, ∏ i, g (x i)) = (∑' j : ℤ, g j)^l := by
  induction l with
  | zero =>
    letI : Unique (Fin 0 → ℤ) := ⟨⟨fun _ => 0⟩, fun _ => funext fun i => i.elim0⟩
    have h0 : HasSum (fun _ : Fin 0 → ℤ => (1 : ℝ)) 1 := by
      simpa only [Fintype.sum_unique] using (hasSum_fintype (fun _ : Fin 0 → ℤ => (1 : ℝ)))
    simp only [Finset.univ_eq_empty, Finset.prod_empty, pow_zero]
    exact ⟨h0.summable, h0.tsum_eq⟩
  | succ l ih =>
    obtain ⟨hs, hsum⟩ := ih
    let e := Fin.consEquiv (fun _ : Fin (l+1) => ℤ)
    let F (x : Fin (l+1) → ℤ) := ∏ i, g (x i)
    let G (p : ℤ × (Fin l → ℤ)) := g p.1 * ∏ i, g (p.2 i)
    have he (p : ℤ × (Fin l → ℤ)) : F (e p) = G p := by
      rw [show F (e p) = ∏ i, g (e p i) from rfl, Fin.prod_univ_succ]
      rfl
    have hprod : 0 ≤ (fun x : Fin l → ℤ => ∏ i, g (x i)) :=
      fun x => Finset.prod_nonneg fun i _ => hg₀ (x i)
    have hG : Summable G := by
      exact Summable.mul_of_nonneg (f := g) (g := fun x : Fin l → ℤ => ∏ i, g (x i))
        hg hs hg₀ hprod
    have hFe : Summable (fun p : ℤ × (Fin l → ℤ) => F (e p)) :=
      hG.congr fun p => (he p).symm
    have hF : Summable F := (e.summable_iff (f := F)).mp hFe
    refine ⟨hF, ?_⟩
    calc
      _ = ∑' p, G p := by rw [← e.tsum_eq F]; exact tsum_congr he
      _ = (∑' i, g i) * ∑' x : Fin l → ℤ, ∏ i, g (x i) := by
        rw [hG.tsum_prod]
        simp only [G, tsum_mul_left, tsum_mul_right]
      _ = _ := by rw [hsum, pow_succ, mul_comm]

/-- The lattice sum of Fourier weights is absolutely summable and bounded
by the product of the one-dimensional reciprocal-square bounds. -/
theorem terminal_fourier_weight_sum {θ : ℝ} (hθ : 0 < θ) {l N : ℕ} (hN : 2*l ≤ N) :
    Summable (fun m : Fin l → ℤ => (1 + θ * ‖latticeVector m‖)^(-(N : ℝ))) ∧
      (∑' m : Fin l → ℤ, (1 + θ * ‖latticeVector m‖)^(-(N : ℝ))) ≤ (1 + 2/θ)^l := by
  obtain ⟨hsG, hBG⟩ := coordWeight_sum hθ
  obtain ⟨hs, hsum⟩ := sum_pi_prod hsG (coordWeight_nonneg hθ) l
  let F (m : Fin l → ℤ) := (1 + θ * ‖latticeVector m‖)^(-(N : ℝ))
  have hF₀ (m : Fin l → ℤ) : 0 ≤ F m := Real.rpow_nonneg (by positivity) _
  have hcomp (m : Fin l → ℤ) : F m ≤ ∏ i, coordWeight θ (m i) := by
    let A := 1 + θ * ‖latticeVector m‖
    have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
    have hpow : -(N : ℝ) ≤ -2 * (l : ℝ) := by
      have hreal : (2 : ℝ) * (l : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    calc
      F m ≤ A^(-2 * (l : ℝ)) := Real.rpow_le_rpow_of_exponent_le hA hpow
      _ = (A^(-2 : ℝ))^l := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ A)]
      _ = ∏ _i : Fin l, A^(-2 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => Real.rpow_nonneg (by positivity) _)
        intro i _
        have hi : |(m i : ℝ)| ≤ ‖latticeVector m‖ := by
          simpa only [latticeVector, Real.norm_eq_abs] using norm_le_pi_norm (latticeVector m) i
        exact Real.rpow_le_rpow_of_nonpos (by positivity)
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hi hθ.le)) (by norm_num)
  have hsF : Summable F := hs.of_nonneg_of_le hF₀ hcomp
  refine ⟨hsF, ?_⟩
  calc
    _ ≤ ∑' m : Fin l → ℤ, ∏ i, coordWeight θ (m i) := hsF.tsum_le_tsum hcomp hs
    _ = (∑' j : ℤ, coordWeight θ j)^l := hsum
    _ ≤ (1 + 2/θ)^l := pow_le_pow_left₀ (tsum_nonneg (coordWeight_nonneg hθ)) hBG _

end

end Birch
