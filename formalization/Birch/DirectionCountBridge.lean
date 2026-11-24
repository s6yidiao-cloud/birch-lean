import Birch.CompletionConditional

/-! # From prime-field direction counts to differencing -/

open MvPolynomial

namespace Birch

noncomputable section

open scoped Classical in
/-- The uniform bad-direction bound for homogeneous forms reduced at a prime.
The real box radius is at least one and is at most half the characteristic. -/
def PrimeDirectionCountAt (n d : ℕ) (K : ℝ) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (e : ℕ), 2 < e → e ≤ d → d < p →
    ∀ G : IntForm n, G.IsHomogeneous e →
    ∀ s j : ℕ, s ≤ n → j ≤ n → PrimeGradientDimension p hp G s →
    ∀ H : ℝ, 1 ≤ H → 2 * H ≤ (p : ℝ) →
      (((differencingDirections n H).filter
        (fun u => PrimeGradientDimension p hp (directionalDerivative u G) j)).card : ℝ) ≤
          K * H ^ ((n : ℝ) - ((j-s : ℕ) : ℝ))

/-- The bad-direction count with an implied constant depending only on the
ambient dimension and the degree bound. -/
def PrimeDirectionBound (n d : ℕ) : Prop :=
  ∃ K > 0, PrimeDirectionCountAt n d K

/-- In the completion range the prime exceeds the size of the original box. -/
theorem completion_scale_le_prime {P Q : ℝ} {p : ℕ}
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hQmax : Q ≤ Real.sqrt P)
    (hp : (P/Q)^2 < (p : ℝ)) : P < (p : ℝ) := by
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hQ₀ : 0 < Q := zero_lt_one.trans_le hQ
  have hQsq : Q^2 ≤ P := by
    simpa only [Real.sq_sqrt hP₀.le] using pow_le_pow_left₀ hQ₀.le hQmax 2
  refine lt_of_le_of_lt ?_ hp
  rw [div_pow, le_div_iff₀ (pow_pos hQ₀ 2)]
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hQsq hP₀.le

/-- All differencing heights lie between one and the scale parameter. -/
theorem one_le_differencingHeight_le {Q : ℝ} (hQ : 1 ≤ Q) (k i : ℕ) :
    1 ≤ differencingHeight k Q i ∧ differencingHeight k Q i ≤ Q := by
  unfold differencingHeight
  refine ⟨Real.one_le_rpow hQ (by positivity), ?_⟩
  conv_rhs => rw [← Real.rpow_one Q]
  apply Real.rpow_le_rpow_of_exponent_le hQ
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

/-- A differencing direction box lies below half the characteristic once
the scale is at least four. -/
theorem two_mul_differencingHeight_le_prime {P Q : ℝ} {p : ℕ}
    (hP : 4 ≤ P) (hQ : 1 ≤ Q) (hQmax : Q ≤ Real.sqrt P)
    (hp : (P/Q)^2 < (p : ℝ)) (k i : ℕ) :
    2 * differencingHeight k Q i ≤ (p : ℝ) := by
  have hP₀ : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 4).trans hP
  have hpL := completion_scale_le_prime hP₀ hQ hQmax hp
  have hsqrt : 2 ≤ Real.sqrt P := by
    have h := Real.sqrt_le_sqrt hP
    simpa only [show Real.sqrt (4 : ℝ) = 2 by norm_num] using h
  have hsq : 2 * Real.sqrt P ≤ P := calc
    _ ≤ Real.sqrt P * Real.sqrt P := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg P)
    _ = P := Real.mul_self_sqrt (by positivity)
  calc
    _ ≤ 2 * Q := mul_le_mul_of_nonneg_left (one_le_differencingHeight_le hQ k i).2 (by norm_num)
    _ ≤ 2 * Real.sqrt P := mul_le_mul_of_nonneg_left hQmax (by norm_num)
    _ ≤ P := hsq
    _ ≤ (p : ℝ) := hpL.le

/-- Leading homogeneous components convert the prime-field count into the
finite direction counts whenever all box radii are at most half the prime. -/
theorem polynomialDirectionCounts_of_primeBound_of_two_mul_le {n d r p : ℕ} {K Q : ℝ}
    (hcount : PrimeDirectionCountAt n d K) (hr : 2 ≤ r) (hdp : d < p) (hp : p.Prime)
    (hQ : 1 ≤ Q) (hpQ : 2 * Q ≤ (p : ℝ)) (m : ℕ → ℤ) (s : ℕ → IntForm n → Fin (n+1))
    (hdim : ∀ i ≤ d-r, ∀ g : IntForm n,
      PrimeGradientDimension p hp (homogeneousComponent (d-i) g) (s i g).val) :
    PolynomialDirectionCounts (k := d-r) d Q m s K := by
  classical
  intro i hi g hg j
  let H := differencingHeight (d-r) Q i
  let G := homogeneousComponent (d-i) g
  have hie : 2 < d-i := by omega
  have hdg : PrimeGradientDimension p hp G (s i g).val := hdim i hi.le g
  have hchild (u : Fin n → ℤ) :
      PrimeGradientDimension p hp (directionalDerivative u G)
        (s (i+1) (dilatedDifference (m i) u g)).val := by
    have h := hdim (i+1) (by omega) (dilatedDifference (m i) u g)
    rwa [show d-(i+1) = (d-i)-1 by omega,
      homogeneousComponent_dilatedDifference (m i) u g (by omega) hg] at h
  have hb := hcount p hp (d-i) hie (Nat.sub_le _ _) hdp G
    (homogeneousComponent_isHomogeneous _ _) (s i g).val j.val
    (Nat.lt_succ_iff.mp (s i g).isLt) (Nat.lt_succ_iff.mp j.isLt) hdg
    H (one_le_differencingHeight_le hQ (d-r) i).1
    ((mul_le_mul_of_nonneg_left (one_le_differencingHeight_le hQ (d-r) i).2
      (by norm_num)).trans hpQ)
  refine le_trans ?_ hb
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro u hu
  obtain ⟨hu, hs⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨hu, by simpa only [hs] using hchild u⟩

/-- The prime completion range supplies the box condition for the direction count. -/
theorem polynomialDirectionCounts_of_primeBound {n d r p : ℕ} {K : ℝ} {P Q : ℝ}
    (hcount : PrimeDirectionCountAt n d K) (hr : 2 ≤ r) (hdp : d < p) (hp : p.Prime)
    (hP : 4 ≤ P) (hQ : 1 ≤ Q) (hQmax : Q ≤ Real.sqrt P)
    (hpL : (P/Q)^2 < (p : ℝ)) (m : ℕ → ℤ) (s : ℕ → IntForm n → Fin (n+1))
    (hdim : ∀ i ≤ d-r, ∀ g : IntForm n,
      PrimeGradientDimension p hp (homogeneousComponent (d-i) g) (s i g).val) :
    PolynomialDirectionCounts (k := d-r) d Q m s K := by
  have hpQ : 2 * Q ≤ (p : ℝ) := by
    have hsub : d-r-1-(d-r) = 0 := Nat.sub_eq_zero_of_le (Nat.sub_le _ _)
    simpa [differencingHeight, hsub] using
      two_mul_differencingHeight_le_prime hP hQ hQmax hpL (d-r) (d-r)
  exact polynomialDirectionCounts_of_primeBound_of_two_mul_le hcount hr hdp hp hQ hpQ m s hdim

end
end Birch
