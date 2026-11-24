import Birch.SingularSeries
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Nonarchimedean local factors for polynomial covers

Section 6 of `v2.tex` uses the complete sums and congruence counts of
`F(x) = g(y)`. The coordinate `y` is appended as the last variable.
-/

namespace Birch

open scoped BigOperators Topology Polynomial
open Filter ZMod

noncomputable section

variable {n : ℕ}

/-- The polynomial `F(x) - g(y)` with `y` in the last coordinate. -/
def coverPolynomial (F : IntForm n) (g : ℤ[X]) : IntForm (n + 1) :=
  MvPolynomial.rename Fin.castSucc F -
    g.eval₂ MvPolynomial.C (MvPolynomial.X (Fin.last n))

theorem evalForm_coverPolynomial {R : Type*} [CommRing R]
    (F : IntForm n) (g : ℤ[X]) (z : Fin (n + 1) → R) :
    evalForm (coverPolynomial F g) z =
      evalForm F (Fin.init z) - g.eval₂ (Int.castRingHom R) (z (Fin.last n)) := by
  unfold evalForm coverPolynomial
  rw [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename]
  congr 1
  change (MvPolynomial.eval₂Hom (Int.castRingHom R) z)
    (g.eval₂ MvPolynomial.C (MvPolynomial.X (Fin.last n))) = _
  rw [Polynomial.hom_eval₂, MvPolynomial.eval₂Hom_X']
  congr 2
  exact Subsingleton.elim _ _

/-- Unit numerators at `q ≥ 2` have unique reduced representatives in `[1, q)`. -/
theorem sum_zmod_units_eq_reducedNumerators {A : Type*} [AddCommMonoid A]
    (q : ℕ) [NeZero q] (hq : 2 ≤ q) (f : ZMod q → A) :
    (∑ u : (ZMod q)ˣ, f u.val) =
      ∑ a ∈ (Finset.Ico 1 q).filter (fun a => a.Coprime q), f (a : ZMod q) := by
  refine Finset.sum_bij (fun u _ => (u.val : ZMod q).val) ?_ ?_ ?_ ?_
  · intro u _
    have hc := ZMod.val_coe_unit_coprime u
    have hpos : 1 ≤ (u : ZMod q).val := by
      by_contra! hpos
      have hzero : (u : ZMod q).val = 0 := by omega
      simp [hzero] at hc
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hpos, ZMod.val_lt _⟩, hc⟩
  · intro a _ b _ he
    exact Units.ext (ZMod.val_injective q he)
  · intro a ha
    obtain ⟨hlt, hc⟩ := Finset.mem_filter.mp ha
    refine ⟨ZMod.unitOfCoprime a hc, Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_Ico.mp hlt).2
  · intro u _
    rw [ZMod.natCast_zmod_val]

/-- The normalized one-variable complete sum `V_q(a)` of Section 6. -/
def coverCompleteSum (g : ℤ[X]) (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  (q : ℂ)⁻¹ * ∑ y : ZMod q, stdAddChar (-(a * g.eval₂ (Int.castRingHom (ZMod q)) y))

/-- The coefficient `A_g(q)` of the cover singular series. -/
def coverConductorSum (F : IntForm n) (g : ℤ[X]) (q : ℕ) [NeZero q] : ℂ :=
  ∑ a : (ZMod q)ˣ, completeSum F q a.val * coverCompleteSum g q a.val

/-- The cover singular series, indexed by `q = j + 1`. -/
def coverSingularSeries (F : IntForm n) (g : ℤ[X]) : ℂ :=
  ∑' j : ℕ, coverConductorSum F g (j + 1)

/-- The number of residue pairs satisfying `F(x) = g(y)`. -/
def coverCongruenceCount (F : IntForm n) (g : ℤ[X]) (q : ℕ) [NeZero q] : ℕ := by
  classical
  exact Fintype.card {xy : (Fin n → ZMod q) × ZMod q //
    residueEval F q xy.1 = g.eval₂ (Int.castRingHom (ZMod q)) xy.2}

/-- The two normalized complete sums multiply because the variables are disjoint. -/
theorem completeSum_coverPolynomial (F : IntForm n) (g : ℤ[X])
    (q : ℕ) [NeZero q] (a : ZMod q) :
    completeSum (coverPolynomial F g) q a =
      completeSum F q a * coverCompleteSum g q a := by
  unfold completeSum coverCompleteSum
  change ((q : ℂ) ^ (n + 1))⁻¹ * (∑ z : Fin (n + 1) → ZMod q,
    stdAddChar (a * evalForm (coverPolynomial F g) z)) = _
  simp_rw [evalForm_coverPolynomial, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  let e := Fin.snocEquiv (fun _ : Fin (n + 1) => ZMod q)
  have he (y : ZMod q) (x : Fin n → ZMod q) : e (y, x) = Fin.snoc x y := rfl
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [he, Fin.init_snoc, Fin.snoc_last]
  change ((q : ℂ) ^ (n + 1))⁻¹ * (∑ y : ZMod q, ∑ x : Fin n → ZMod q,
    stdAddChar (a * residueEval F q x) *
      stdAddChar (-(a * g.eval₂ (Int.castRingHom (ZMod q)) y))) = _
  simp_rw [← Finset.sum_mul]
  rw [← Finset.mul_sum, pow_succ, mul_inv]
  ring

theorem coverConductorSum_eq_unitConductorSum (F : IntForm n) (g : ℤ[X])
    (q : ℕ) [NeZero q] :
    coverConductorSum F g q = unitConductorSum (coverPolynomial F g) q := by
  simp only [coverConductorSum, unitConductorSum, completeSum_coverPolynomial]

theorem coverSingularSeries_eq_singularSeries (F : IntForm n) (g : ℤ[X]) :
    coverSingularSeries F g = singularSeries (coverPolynomial F g) := by
  simp only [coverSingularSeries, singularSeries, coverConductorSum_eq_unitConductorSum]

theorem coverCongruenceCount_eq_residueZeroCount (F : IntForm n) (g : ℤ[X])
    (q : ℕ) [NeZero q] :
    coverCongruenceCount F g q = residueZeroCount (coverPolynomial F g) q := by
  classical
  let e := (Equiv.prodComm (Fin n → ZMod q) (ZMod q)).trans
    (Fin.snocEquiv (fun _ : Fin (n + 1) => ZMod q))
  rw [coverCongruenceCount, residueZeroCount, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv e (by
    intro xy
    change _ ↔ (evalForm (coverPolynomial F g) (Fin.snoc xy.1 xy.2) = 0)
    rw [evalForm_coverPolynomial, Fin.init_snoc, Fin.snoc_last, sub_eq_zero]
    rfl))

/-- CRT multiplicativity of `A_g(q)` at coprime moduli. -/
theorem coverConductorSum_mul (F : IntForm n) (g : ℤ[X])
    {q r : ℕ} [NeZero q] [NeZero r] (h : q.Coprime r) :
    coverConductorSum F g (q * r) = coverConductorSum F g q * coverConductorSum F g r := by
  simp only [coverConductorSum_eq_unitConductorSum]
  exact unitConductorSum_mul (coverPolynomial F g) h

/-- The exact finite density at `p^k`, including the unit conductor at `j = 0`. -/
theorem coverPrimePower_density_eq_sum (F : IntForm n) (g : ℤ[X])
    (p k : ℕ) [Fact p.Prime] [NeZero p] :
    (((p ^ k : ℕ) : ℂ) ^ n)⁻¹ * (coverCongruenceCount F g (p ^ k) : ℂ) =
      ∑ j ∈ Finset.range (k + 1), coverConductorSum F g (p ^ j) := by
  simp only [coverCongruenceCount_eq_residueZeroCount, coverConductorSum_eq_unitConductorSum]
  exact primePower_density_eq_sum (coverPolynomial F g) p k (by omega)


/-- Sum of the absolute values of the individual terms at conductor `q`. -/
def coverConductorMass (F : IntForm n) (g : ℤ[X]) (q : ℕ) [NeZero q] : ℝ :=
  ∑ a : (ZMod q)ˣ, ‖completeSum F q a.val * coverCompleteSum g q a.val‖

theorem coverConductorMass_nonneg (F : IntForm n) (g : ℤ[X]) (q : ℕ) [NeZero q] :
    0 ≤ coverConductorMass F g q :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_coverConductorSum_le_mass (F : IntForm n) (g : ℤ[X]) (q : ℕ) [NeZero q] :
    ‖coverConductorSum F g q‖ ≤ coverConductorMass F g q := norm_sum_le _ _

theorem norm_coverCompleteSum_le_one (g : ℤ[X]) (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖coverCompleteSum g q a‖ ≤ 1 := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hnorm (x : ZMod q) : ‖stdAddChar x‖ = 1 := by
    rw [stdAddChar_apply]
    exact (toCircle (N := q) x).norm_coe
  rw [coverCompleteSum, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ y : ZMod q,
        ‖stdAddChar (-(a * g.eval₂ (Int.castRingHom (ZMod q)) y))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = 1 := by
      simp only [hnorm, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ hq

theorem coverConductorMass_le_of_completeSum_bound (F : IntForm n) (g : ℤ[X])
    (q : ℕ) [NeZero q] {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a : (ZMod q)ˣ, ‖completeSum F q a.val‖ ≤ B) :
    coverConductorMass F g q ≤ (q : ℝ) * B := by
  classical
  have hcard : Fintype.card (ZMod q)ˣ ≤ q := by
    calc
      _ ≤ Fintype.card (ZMod q) := Fintype.card_le_of_injective _ Units.val_injective
      _ = q := ZMod.card q
  calc
    coverConductorMass F g q ≤ ∑ _ : (ZMod q)ˣ, B := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul]
      calc
        _ ≤ ‖completeSum F q a.val‖ * 1 :=
          mul_le_mul_of_nonneg_left (norm_coverCompleteSum_le_one g q a.val) (norm_nonneg _)
        _ ≤ B := by simpa only [mul_one] using h a
    _ ≤ (q : ℝ) * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

theorem coverConductorMass_le_of_completeSum_power (F : IntForm n) (g : ℤ[X])
    {κ C : ℝ} (hC : 0 ≤ C) (q : ℕ) [NeZero q]
    (h : ∀ a : (ZMod q)ˣ, ‖completeSum F q a.val‖ ≤ C * (q : ℝ) ^ (-κ)) :
    coverConductorMass F g q ≤ C * (q : ℝ) ^ (1 - κ) := by
  refine (coverConductorMass_le_of_completeSum_bound F g q (by positivity) h).trans_eq ?_
  rw [show 1 - κ = (1 : ℝ) + -κ by ring,
    Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)), Real.rpow_one]
  ring

/-- Absolute convergence of the sum over both the conductors and the reduced numerators. -/
theorem summable_coverConductorMass_of_completeSum_power (F : IntForm n) (g : ℤ[X])
    {κ C : ℝ} (hC : 0 ≤ C) (hκ : 2 < κ)
    (h : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ), ‖completeSum F q a.val‖ ≤ C * (q : ℝ) ^ (-κ)) :
    Summable (fun j : ℕ => coverConductorMass F g (j + 1)) := by
  have hp : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (1 - κ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith))
  exact (hp.mul_left C).of_nonneg_of_le (fun _ => coverConductorMass_nonneg F g _)
    (fun j => coverConductorMass_le_of_completeSum_power F g hC (j + 1) (h (j + 1)))

/-- The estimate for the absolute tail after any positive integer cutoff `Q`. -/
theorem coverConductorMass_tail_of_completeSum_power (F : IntForm n) (g : ℤ[X])
    {κ C : ℝ} (hC : 0 ≤ C) (hκ : 2 < κ)
    (h : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ), ‖completeSum F q a.val‖ ≤ C * (q : ℝ) ^ (-κ))
    (Q : ℕ) (hQ : 1 ≤ Q) :
    (∑' j : ℕ, coverConductorMass F g (j + Q + 1)) ≤ C / (κ - 2) * (Q : ℝ) ^ (2 - κ) := by
  have hQ' : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hs := summable_coverConductorMass_of_completeSum_power F g hC hκ h
  have hpowers : Summable (fun j : ℕ => ((j + Q + 1 : ℕ) : ℝ) ^ (1 - κ)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (Q + 1)).2 ((Real.summable_nat_rpow (p := 1 - κ)).2 (by linarith))
  calc
    _ ≤ ∑' j : ℕ, C * ((j + Q + 1 : ℕ) : ℝ) ^ (1 - κ) :=
      ((summable_nat_add_iff Q).2 hs).tsum_le_tsum
        (fun j => coverConductorMass_le_of_completeSum_power F g hC (j + Q + 1) (h (j + Q + 1)))
        (hpowers.mul_left C)
    _ = C * ∑' j : ℕ, ((j + Q + 1 : ℕ) : ℝ) ^ (1 - κ) := tsum_mul_left
    _ ≤ C * ∫ x : ℝ in Set.Ioi (Q : ℝ), x ^ (1 - κ) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (1 - κ)) Q
      · intro x hx y _ hxy
        exact Real.rpow_le_rpow_of_nonpos (hQ'.trans_le hx) hxy (by linarith)
      · exact integrableOn_Ioi_rpow_of_lt (by linarith) hQ'
      · intro x hx
        exact Real.rpow_nonneg (le_of_lt (hQ'.trans hx)) _
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (show 1 - κ < -1 by linarith) hQ',
        show 1 - κ + 1 = 2 - κ by ring, show 2 - κ = -(κ - 2) by ring, div_neg]
      simp only [neg_div, neg_neg]
      ring

theorem summable_norm_coverConductorSum_of_mass (F : IntForm n) (g : ℤ[X])
    (hs : Summable (fun j : ℕ => coverConductorMass F g (j + 1))) :
    Summable (fun j : ℕ => ‖coverConductorSum F g (j + 1)‖) :=
  hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => norm_coverConductorSum_le_mass F g (j + 1))

/-- Euler product for the cover, with local factors given by the conductor series. -/
theorem hasProd_coverLocalFactors (F : IntForm n) (g : ℤ[X])
    (hs : Summable (fun j : ℕ => ‖coverConductorSum F g (j + 1)‖)) :
    HasProd (localSeriesFactor (coverPolynomial F g)) (coverSingularSeries F g) := by
  rw [coverSingularSeries_eq_singularSeries]
  exact hasProd_localSeriesFactor _ (by simpa only [coverConductorSum_eq_unitConductorSum] using hs)

set_option maxHeartbeats 800000 in
/-- The prime factor in the Euler product is the limit of normalized congruence counts. -/
theorem tendsto_coverPrimePower_density (F : IntForm n) (g : ℤ[X])
    (hs : Summable (fun j : ℕ => ‖coverConductorSum F g (j + 1)‖)) (p : Nat.Primes)
    [NeZero (p : ℕ)] :
    Tendsto (fun k : ℕ => ((((p : ℕ) ^ k : ℕ) : ℂ) ^ n)⁻¹ *
      (coverCongruenceCount F g ((p : ℕ) ^ k) : ℂ)) atTop
      (𝓝 (localSeriesFactor (coverPolynomial F g) p)) := by
  letI : Fact (p : ℕ).Prime := ⟨p.prop⟩
  let A := singularSeriesTerm (coverPolynomial F g)
  have hA : Summable (fun q : ℕ => ‖A q‖) := by
    rw [← summable_nat_add_iff 1]
    have h_eq (j : ℕ) : A (j+1) = coverConductorSum F g (j+1) := by
      rw [coverConductorSum_eq_unitConductorSum]
      exact dif_neg (Nat.succ_ne_zero j)
    simpa only [h_eq] using hs
  have hAn : Summable (fun q : ℕ => ‖A q‖₊) := NNReal.summable_coe.mp hA
  have hprime : Summable (fun k : ℕ => ‖A ((p : ℕ)^k)‖) :=
    NNReal.summable_coe.mpr (NNReal.summable_comp_injective hAn
      (Nat.pow_right_injective p.prop.two_le))
  have h_eq (j : ℕ) : A ((p : ℕ) ^ j) = coverConductorSum F g ((p : ℕ) ^ j) := by
    rw [coverConductorSum_eq_unitConductorSum]
    exact dif_neg (NeZero.ne _)
  simp_rw [coverPrimePower_density_eq_sum, ← h_eq]
  exact hprime.of_norm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)


/-- The absolute tail controls the error in truncating the cover singular series. -/
theorem norm_coverSingularSeries_sub_truncation_le_massTail
    (F : IntForm n) (g : ℤ[X]) (Q : ℕ)
    (hs : Summable (fun j : ℕ => coverConductorMass F g (j + 1))) :
    ‖coverSingularSeries F g - ∑ j ∈ Finset.range Q, coverConductorSum F g (j + 1)‖ ≤
      ∑' j : ℕ, coverConductorMass F g (j + Q + 1) := by
  have hnorm := summable_norm_coverConductorSum_of_mass F g hs
  have hmassTail := (summable_nat_add_iff Q).2 hs
  have hnormTail := (summable_nat_add_iff Q).2 hnorm
  unfold coverSingularSeries
  rw [← hnorm.of_norm.sum_add_tsum_nat_add Q, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hnormTail).trans
    (hnormTail.tsum_le_tsum (fun j => norm_coverConductorSum_le_mass F g (j + Q + 1)) hmassTail)

/-- The weighted-cover threshold leaves room for an exponent greater than two in
the complete-sum bound of Section 5. Here `m` is the cover moment. -/
theorem exists_coverCompleteSumExponent {d ν m : ℕ}
    (hd : 3 ≤ d) (hm : 4 ≤ m)
    (hν : (1 - (1 : ℝ) / m) * dimensionThreshold d < ν) :
    ∃ κ : ℝ, 2 < κ ∧ κ < (ν : ℝ) / (2 * (d - 1 : ℝ)) := by
  have hthreshold : 16 * (d - 1) ≤ 3 * dimensionThreshold d := by
    unfold dimensionThreshold
    have hpow : 16 * (d - 1) + 12 ≤ 3 * 2 ^ (d + 1) := by
      clear hν
      induction d, hd using Nat.le_induction with
      | base => norm_num
      | succ d hd ih =>
        calc
          _ ≤ 2 * (16 * (d - 1) + 12) := by omega
          _ ≤ 2 * (3 * 2 ^ (d + 1)) := Nat.mul_le_mul_left 2 ih
          _ = _ := by rw [pow_succ]; ring
    omega
  have hd' : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have ht : 16 * ((d : ℝ) - 1) ≤ 3 * (dimensionThreshold d : ℝ) := by
    have hc : 16 * ((d - 1 : ℕ) : ℝ) ≤ 3 * (dimensionThreshold d : ℝ) := by
      exact_mod_cast hthreshold
    simpa only [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] using hc
  have hm' : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hfrac : 3 / 4 ≤ 1 - (1 : ℝ) / m := by
    have : (1 : ℝ) / m ≤ 1 / 4 := (div_le_iff₀ hmpos).2 (by linarith)
    linarith
  apply exists_between
  apply (lt_div_iff₀ (by linarith : 0 < 2 * ((d : ℝ) - 1))).2
  have hquarter := mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg (dimensionThreshold d))
  linarith

end
end Birch
