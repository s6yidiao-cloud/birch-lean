import Birch.Geometry
import Birch.CompleteSums
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Hensel lifting and positivity of local densities

A nonzero partial derivative at an integral p-adic zero gives a uniform
lower bound for the density of zeros at every sufficiently deep conductor.
-/

namespace Birch

noncomputable section

open scoped BigOperators
open MvPolynomial Filter
open scoped Topology

variable {n p : ℕ}

private def specializeCoordinate {R : Type*} [CommRing R] (F : IntForm n)
    (x : Fin n → R) (i : Fin n) : Polynomial R :=
  F.eval₂ (Int.castRingHom (Polynomial R)) (fun j => if j = i then Polynomial.X else Polynomial.C (x j))

private theorem eval_specializeCoordinate {R : Type*} [CommRing R]
    (F : IntForm n) (x : Fin n → R) (i : Fin n) (z : R) :
    (specializeCoordinate F x i).eval z = evalForm F (Function.update x i z) := by
  unfold specializeCoordinate evalForm
  rw [MvPolynomial.polynomial_eval_eval₂]
  congr 1
  · ext
    simp
  · funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj, Function.update_of_ne]

private theorem derivative_specializeCoordinate {R : Type*} [CommRing R]
    (F : IntForm n) (x : Fin n → R) (i : Fin n) :
    (specializeCoordinate F x i).derivative = specializeCoordinate (pderiv i F) x i := by
  induction F using induction_on with
  | C a =>
    simp only [specializeCoordinate, eval₂_C, pderiv_C, eval₂_zero]
    change Polynomial.derivative (a : Polynomial R) = 0
    rw [← Polynomial.C_eq_intCast, Polynomial.derivative_C]
  | add F G ihF ihG =>
    simp only [specializeCoordinate, map_add, eval₂_add] at ihF ihG ⊢
    rw [ihF, ihG]
  | mul_X F j ih =>
    simp only [specializeCoordinate, pderiv_mul, eval₂_add, eval₂_mul, eval₂_X,
      Polynomial.derivative_mul] at ih ⊢
    rw [ih]
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj, pderiv_X_of_ne hj]

private theorem norm_sub_le_of_toZModPow_eq [Fact p.Prime]
    {x y : ℤ_[p]} {k : ℕ} (h : PadicInt.toZModPow k x = PadicInt.toZModPow k y) :
    ‖x - y‖ ≤ (p : ℝ)^(-(k : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, sub_eq_zero]
  exact h

/-- Perturbing the coordinates modulo `p^(2v+1)` still allows the selected
coordinate to be solved by Hensel, where `v` is the valuation of that partial. -/
theorem exists_padic_zero_update_of_congruent [Fact p.Prime]
    (F : IntForm n) (x y : Fin n → ℤ_[p]) (i : Fin n)
    (hx : evalForm F x = 0) (hi : evalForm (pderiv i F) x ≠ 0)
    (hy : let k := 2 * (evalForm (pderiv i F) x).valuation + 1
          ∀ j, PadicInt.toZModPow k (y j) = PadicInt.toZModPow k (x j)) :
    ∃ z : ℤ_[p], evalForm F (Function.update y i z) = 0 := by
  let v := (evalForm (pderiv i F) x).valuation
  let k := 2 * v + 1
  have hn (G : IntForm n) :
      ‖evalForm G y - evalForm G x‖ ≤ (p : ℝ)^(-(k : ℤ)) := by
    apply norm_sub_le_of_toZModPow_eq
    rw [evalForm_hom, evalForm_hom]
    congr 1
    exact funext hy
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hup : (p : ℝ)^(-(k : ℤ)) < ‖evalForm (pderiv i F) x‖ := by
    rw [PadicInt.norm_eq_zpow_neg_valuation hi]
    exact (zpow_lt_zpow_iff_right₀ hp).2 (by change -(k : ℤ) < -(v : ℤ); dsimp [k]; omega)
  have hup2 : (p : ℝ)^(-(k : ℤ)) < ‖evalForm (pderiv i F) x‖^2 := by
    rw [PadicInt.norm_eq_zpow_neg_valuation hi, ← zpow_natCast (n := 2), ← zpow_mul]
    exact (zpow_lt_zpow_iff_right₀ hp).2 (by change -(k : ℤ) < -(v : ℤ) * 2; dsimp [k]; omega)
  have hdiff := (hn (pderiv i F)).trans_lt hup
  have hnorm :
      ‖evalForm (pderiv i F) y‖ = ‖evalForm (pderiv i F) x‖ := by
    apply Padic.norm_eq_of_norm_sub_lt_right
    simpa only [← PadicInt.coe_sub, ← PadicInt.norm_def] using hdiff
  let G := specializeCoordinate F y i
  have he (z : ℤ_[p]) : G.aeval z = evalForm F (Function.update y i z) := by
    change (specializeCoordinate F y i).eval z = _
    exact eval_specializeCoordinate F y i z
  have hd : G.derivative.aeval (y i) = evalForm (pderiv i F) y := by
    change (specializeCoordinate F y i).derivative.eval (y i) = _
    rw [derivative_specializeCoordinate, eval_specializeCoordinate, Function.update_eq_self]
  have hG : ‖G.aeval (y i)‖ < ‖G.derivative.aeval (y i)‖^2 := by
    rw [he, Function.update_eq_self, hd, hnorm]
    have hFy := hn F
    rw [hx, sub_zero] at hFy
    exact hFy.trans_lt hup2
  obtain ⟨z, hz, _⟩ := hensels_lemma hG
  exact ⟨z, (he z).symm.trans hz⟩


private theorem liftDigit_injective (p m k : ℕ) [NeZero p] (hkm : k ≤ m) :
    Function.Injective (fun a : ZMod (p^(m-k)) => ((p^k*a.val : ℕ) : ZMod (p^m))) := by
  intro a b hab
  have hval (c : ZMod (p^(m-k))) : p^k*c.val < p^m := by
    conv_rhs => rw [← Nat.add_sub_of_le hkm, pow_add]
    exact Nat.mul_lt_mul_of_pos_left c.val_lt (pow_pos (NeZero.pos p) _)
  have he := congrArg ZMod.val hab
  rw [ZMod.val_natCast_of_lt (hval a), ZMod.val_natCast_of_lt (hval b)] at he
  exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left (pow_pos (NeZero.pos p) _) he)

/-- The exact lower bound for the finite zero counts in the major-arc section.
Here `k = 2v+1` and `v` is the valuation of a nonzero partial derivative
at the integral p-adic zero. -/
theorem primePower_zeroCount_lower_of_padicInt_zero [Fact p.Prime] [NeZero p]
    (F : IntForm n) (x : Fin n → ℤ_[p]) (i : Fin n)
    (hx : evalForm F x = 0) (hi : evalForm (pderiv i F) x ≠ 0)
    (m : ℕ) (hm : 2 * (evalForm (pderiv i F) x).valuation + 1 ≤ m) :
    p ^ ((m - (2 * (evalForm (pderiv i F) x).valuation + 1)) * (n - 1)) ≤
      residueZeroCount F (p^m) := by
  classical
  let k := 2 * (evalForm (pderiv i F) x).valuation + 1
  let others := {j : Fin n // j ≠ i}
  let Digits := others → ZMod (p^(m-k))
  let y (b : Digits) (j : Fin n) : ℤ_[p] :=
    if hj : j ≠ i then x j + (p : ℤ_[p])^k * ((b ⟨j, hj⟩).val : ℤ_[p]) else x j
  have hstepZero : (PadicInt.toZModPow k) ((p : ℤ_[p])^k) = 0 := by
    rw [← Nat.cast_pow, map_natCast, ZMod.natCast_self]
  have hy (b : Digits) (j : Fin n) :
      PadicInt.toZModPow k (y b j) = PadicInt.toZModPow k (x j) := by
    unfold y
    split_ifs <;> simp [hstepZero]
  have hex (b : Digits) : ∃ z : ℤ_[p], evalForm F (Function.update (y b) i z) = 0 :=
    exists_padic_zero_update_of_congruent F x (y b) i hx hi (hy b)
  choose z hz using hex
  let out (b : Digits) (j : Fin n) : ZMod (p^m) :=
    PadicInt.toZModPow m (Function.update (y b) i (z b) j)
  have hsol (b : Digits) : residueEval F (p^m) (out b) = 0 := by
    change evalForm F (fun j => PadicInt.toZModPow m (Function.update (y b) i (z b) j)) = 0
    rw [← evalForm_hom, hz, map_zero]
  let zeros := Finset.univ.filter (fun a : Fin n → ZMod (p^m) => residueEval F (p^m) a = 0)
  let lift (b : Digits) : zeros := ⟨out b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsol b⟩⟩
  have hc (b : Digits) (j : others) :
      out b j.val = PadicInt.toZModPow m (x j.val) +
        ((p^k*(b j).val : ℕ) : ZMod (p^m)) := by
    simp only [out, Function.update_of_ne j.prop, y, dite_eq_left j.prop, map_add, map_mul,
      map_pow, map_natCast, Nat.cast_pow, Nat.cast_mul]
    rfl
  have hinj : Function.Injective lift := by
    intro b c h
    funext j
    have ha : out b j.val = out c j.val :=
      congrArg (fun a : zeros => a.val j.val) h
    rw [hc, hc] at ha
    exact liftDigit_injective p m k hm (add_left_cancel ha)
  have hothers : Fintype.card others = n - 1 := by
    unfold others
    rw [Fintype.card_subtype_compl (fun j : Fin n => j = i), Fintype.card_fin,
      Fintype.card_subtype_eq]
  have hcard := Fintype.card_le_of_injective lift hinj
  change Fintype.card (others → ZMod (p^(m-k))) ≤ Fintype.card zeros at hcard
  rw [Fintype.card_fun, ZMod.card, hothers, ← pow_mul, Fintype.card_coe] at hcard
  exact hcard

/-- A nonsingular local zero of a homogeneous form gives a fixed depth
shift in the lower bound for every sufficiently deep zero count. -/
theorem primePower_zeroCount_lower_of_nonsingularZero [Fact p.Prime] [NeZero p]
    {d : ℕ} (F : IntForm n) (hF : F.IsHomogeneous d)
    (hloc : HasNonsingularZero F ℚ_[p]) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      p ^ ((m-k)*(n-1)) ≤ residueZeroCount F (p^m) := by
  obtain ⟨x, hFx, i, hi⟩ := hloc
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ‖x‖ hp
  let c : ℚ_[p] := (p : ℚ_[p])^K
  have hc : c ≠ 0 := pow_ne_zero K (by exact_mod_cast NeZero.ne p)
  have hb (j : Fin n) : ‖c * x j‖ ≤ 1 := by
    have hp0 : (0 : ℝ) < p := by positivity
    have hK0 : 0 < (p : ℝ)^K := pow_pos hp0 _
    rw [norm_mul, show c = _ from rfl, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    exact (inv_mul_le_one₀ hK0).2 ((norm_le_pi_norm x j).trans hK.le)
  let y (j : Fin n) : ℤ_[p] := ⟨c * x j, hb j⟩
  let incl : ℤ_[p] →+* ℚ_[p] := algebraMap _ _
  have hy : evalForm F y = 0 := by
    apply PadicInt.coe_eq_zero.mp
    change incl (evalForm F y) = 0
    rw [evalForm_hom]
    change evalForm F (fun j => c * x j) = 0
    rw [evalForm_scale hF, hFx, mul_zero]
  have hyi : evalForm (pderiv i F) y ≠ 0 := by
    intro hzero
    have hh := congrArg incl hzero
    rw [evalForm_hom, map_zero] at hh
    change evalForm (pderiv i F) (fun j => c * x j) = 0 at hh
    rw [evalForm_scale hF.pderiv] at hh
    exact (mul_ne_zero (pow_ne_zero _ hc) hi) hh
  exact ⟨2 * (evalForm (pderiv i F) y).valuation + 1, fun m hm =>
    primePower_zeroCount_lower_of_padicInt_zero F y i hy hyi m hm⟩

/-- The nonsingular local zero is automatic for a nonzero local zero of a
geometrically smooth homogeneous form. -/
theorem primePower_zeroCount_lower_of_localSoluble [Fact p.Prime] [NeZero p]
    {d : ℕ} (F : IntForm n) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hloc : HasNonzeroZero F ℚ_[p]) :
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      p ^ ((m-k)*(n-1)) ≤ residueZeroCount F (p^m) := by
  obtain ⟨x, hx, hFx⟩ := hloc
  exact primePower_zeroCount_lower_of_nonsingularZero F hF
    ⟨x, hFx, hs.nonsingular_over x hx hFx⟩

/-- A nonsingular local zero makes the local factor positive once its
conductor series is summable. -/
theorem primePower_localFactor_pos_of_nonsingularZero [Fact p.Prime] [NeZero p]
    {d : ℕ} (F : IntForm n) (hn : 1 ≤ n) (hF : F.IsHomogeneous d)
    (hloc : HasNonsingularZero F ℚ_[p])
    (hSummable : Summable (fun j : ℕ => unitConductorSum F (p^j))) :
    0 < (∑' j : ℕ, unitConductorSum F (p^j)).re := by
  obtain ⟨k, hk⟩ := primePower_zeroCount_lower_of_nonsingularZero F hF hloc
  let s (m : ℕ) := ∑ j ∈ Finset.range (m+1), unitConductorSum F (p^j)
  have hsT : Tendsto s atTop (𝓝 (∑' j : ℕ, unitConductorSum F (p^j))) :=
    hSummable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hreT : Tendsto (fun m => (s m).re) atTop (𝓝 ((∑' j : ℕ, unitConductorSum F (p^j)).re)) :=
    Complex.continuous_re.continuousAt.tendsto.comp hsT
  have hpR : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  let B : ℝ := ((p : ℝ)^(k*(n-1)))⁻¹
  have hB : 0 < B := inv_pos.mpr (pow_pos hpR _)
  have hlower : ∀ᶠ m : ℕ in atTop, B ≤ (s m).re := by
    filter_upwards [eventually_ge_atTop k] with m hm
    have hraw := hk m hm
    have hreal : ((p : ℝ)^((m-k)*(n-1))) ≤ (residueZeroCount F (p^m) : ℝ) := by
      exact_mod_cast hraw
    have hsum :
        (s m).re = ((p : ℝ) ^ (m*(n-1)))⁻¹ * (residueZeroCount F (p^m) : ℝ) := by
      dsimp [s]
      rw [← primePower_density_eq_sum F p m hn]
      push_cast
      rw [← pow_mul]
      norm_cast
      simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [hsum]
    have hexp : m*(n-1) = k*(n-1)+(m-k)*(n-1) := by
      rw [← Nat.add_mul, Nat.add_sub_of_le hm]
    have hden : 0 < (p : ℝ)^((m-k)*(n-1)) := pow_pos hpR _
    rw [hexp, pow_add, mul_inv, mul_assoc]
    have hratio : 1 ≤ ((p : ℝ)^((m-k)*(n-1)))⁻¹ * (residueZeroCount F (p^m) : ℝ) := by
      rw [inv_mul_eq_div, one_le_div hden]
      exact hreal
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hB.le
  exact hB.trans_le (ge_of_tendsto hreT hlower)

/-- A nonzero local zero suffices for a geometrically smooth form. -/
theorem primePower_localFactor_pos_of_summable [Fact p.Prime] [NeZero p]
    {d : ℕ} (F : IntForm n) (hn : 1 ≤ n) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hloc : HasNonzeroZero F ℚ_[p])
    (hSummable : Summable (fun j : ℕ => unitConductorSum F (p^j))) :
    0 < (∑' j : ℕ, unitConductorSum F (p^j)).re := by
  obtain ⟨x, hx, hFx⟩ := hloc
  exact primePower_localFactor_pos_of_nonsingularZero F hn hF
    ⟨x, hFx, hs.nonsingular_over x hx hFx⟩ hSummable

end

end Birch
