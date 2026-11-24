import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Complete exponential sums and prime-power densities

This file uses the normalization of the major-arc section of
`Proof_Birch_General.tex`.
-/

namespace Birch

open scoped BigOperators
open ZMod

noncomputable section

variable {n : ℕ}

/-- Reduction and evaluation of an integral polynomial over the residue ring. -/
def residueEval (F : MvPolynomial (Fin n) ℤ) (q : ℕ) (x : Fin n → ZMod q) : ZMod q :=
  F.eval₂ (Int.castRingHom (ZMod q)) x

/-- The complete sum at numerator `a`, averaged over all residue vectors. -/
def completeSum (F : MvPolynomial (Fin n) ℤ) (q : ℕ) [NeZero q] (a : ZMod q) : ℂ :=
  ((q : ℂ) ^ n)⁻¹ * ∑ x : Fin n → ZMod q, stdAddChar (a * residueEval F q x)

/-- The contribution of precisely the unit numerators at a given conductor. -/
def unitConductorSum (F : MvPolynomial (Fin n) ℤ) (q : ℕ) [NeZero q] : ℂ :=
  ∑ a : (ZMod q)ˣ, completeSum F q a

/-- Number of residue vectors satisfying the polynomial congruence. -/
def residueZeroCount (F : MvPolynomial (Fin n) ℤ) (q : ℕ) [NeZero q] : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Fin n → ZMod q => residueEval F q x = 0).card

private theorem sum_stdAddChar_mul {q : ℕ} [NeZero q] (t : ZMod q) :
    (∑ a : ZMod q, stdAddChar (t * a)) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar q h)

/-- Orthogonality at a fixed modulus, including every numerator. -/
theorem sum_completeSum_eq_density (F : MvPolynomial (Fin n) ℤ)
    (q : ℕ) [NeZero q] (hn : 1 ≤ n) :
    (∑ a : ZMod q, completeSum F q a) =
      ((q : ℂ) ^ (n - 1))⁻¹ * (residueZeroCount F q : ℂ) := by
  classical
  unfold completeSum
  simp_rw [mul_comm _ (residueEval F q _)]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [sum_stdAddChar_mul, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, residueZeroCount]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hn' : n = (n - 1) + 1 := by omega
  have hpow : (q : ℂ) ^ n = (q : ℂ) ^ (n - 1) * q :=
    (congrArg (fun k : ℕ => (q : ℂ) ^ k) hn').trans (pow_succ _ _)
  rw [hpow]
  field_simp

/-- Recombination by a quotient digit and a residue digit. -/
private def residueDigits (t q : ℕ) [NeZero t] [NeZero q] :
    ZMod t × ZMod q ≃ ZMod (t * q) :=
  ((Equiv.prodCongr (ZMod.finEquiv t).symm.toEquiv (ZMod.finEquiv q).symm.toEquiv).trans
    finProdFinEquiv).trans (ZMod.finEquiv (t * q)).toEquiv

private theorem finEquiv_val {q : ℕ} [NeZero q] (x : Fin q) :
    (ZMod.finEquiv q x).val = x.val := by
  cases q with
  | zero => exact Fin.elim0 x
  | succ q => rfl

private theorem residueDigits_val {t q : ℕ} [NeZero t] [NeZero q]
    (y : ZMod t × ZMod q) :
    (residueDigits t q y).val = y.2.val + q * y.1.val := by
  change (ZMod.finEquiv (t * q) (finProdFinEquiv
    ((ZMod.finEquiv t).symm y.1, (ZMod.finEquiv q).symm y.2))).val = _
  rw [finEquiv_val]
  change ((ZMod.finEquiv q).symm y.2).val + q * ((ZMod.finEquiv t).symm y.1).val = _
  have h₁ := finEquiv_val ((ZMod.finEquiv t).symm y.1)
  have h₂ := finEquiv_val ((ZMod.finEquiv q).symm y.2)
  simpa using congrArg₂ (fun a b : ℕ => b + q * a) h₁.symm h₂.symm

/-- Reduction along the divisor `q ∣ t*q`. -/
def reduceResidue (t q : ℕ) : ZMod (t * q) →+* ZMod q :=
  ZMod.castHom (dvd_mul_left q t) (ZMod q)

private theorem reduceResidue_residueDigits {t q : ℕ} [NeZero t] [NeZero q]
    (y : ZMod t × ZMod q) :
    reduceResidue t q (residueDigits t q y) = y.2 := by
  rw [← ZMod.natCast_zmod_val (residueDigits t q y), map_natCast, residueDigits_val]
  simp

/-- Evaluation commutes with maps between residue rings. -/
theorem hom_residueEval (F : MvPolynomial (Fin n) ℤ) {Q q : ℕ}
    (red : ZMod Q →+* ZMod q) (x : Fin n → ZMod Q) :
    red (residueEval F Q x) = residueEval F q (fun j => red (x j)) := by
  unfold residueEval
  rw [MvPolynomial.hom_eval₂]
  congr 1
  ext
  simp

private theorem stdAddChar_of_mul_lift {t q : ℕ} [NeZero t] [NeZero q]
    (a : ZMod (t * q)) :
    stdAddChar ((t : ZMod (t * q)) * a) = stdAddChar (reduceResidue t q a) := by
  obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [map_natCast, ← Nat.cast_mul]
  have hchar (N k : ℕ) [NeZero N] :
      stdAddChar (k : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * k / N) := by
    simpa only [Int.cast_natCast] using stdAddChar_coe (N := N) (k : ℤ)
  rw [hchar, hchar]
  congr 1
  push_cast
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp

private def digitVectors (t q : ℕ) [NeZero t] [NeZero q] :
    (Fin n → ZMod t) × (Fin n → ZMod q) ≃ (Fin n → ZMod (t * q)) :=
  (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ZMod t) (fun _ => ZMod q)).symm.trans
    (Equiv.piCongrRight (fun _ => residueDigits t q))

private theorem sum_reduceResidue {A : Type*} [Semiring A] {t q : ℕ} [NeZero t] [NeZero q]
    (f : (Fin n → ZMod q) → A) :
    (∑ x : Fin n → ZMod (t * q), f (fun j => reduceResidue t q (x j))) =
      (t : A) ^ n * ∑ y : Fin n → ZMod q, f y := by
  rw [← (digitVectors t q).sum_comp]
  have h (y : (Fin n → ZMod t) × (Fin n → ZMod q)) :
      (fun j => reduceResidue t q (digitVectors t q y j)) = y.2 := by
    funext j
    exact reduceResidue_residueDigits (y.1 j, y.2 j)
  simp_rw [h]
  rw [Fintype.sum_prod_type]
  change (∑ _x : Fin n → ZMod t, ∑ y : Fin n → ZMod q, f y) = _
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [ZMod.card]

/-- A numerator lifted by multiplication by `t` gives the same normalized
complete sum at modulus `t*q` as its original value at modulus `q`. -/
theorem completeSum_of_mul_lift (F : MvPolynomial (Fin n) ℤ)
    (t q : ℕ) [NeZero t] [NeZero q] (b : ZMod (t * q)) :
    completeSum F (t*q) ((t : ZMod (t*q)) * b) =
      completeSum F q (reduceResidue t q b) := by
  unfold completeSum
  simp_rw [mul_assoc, stdAddChar_of_mul_lift, map_mul, hom_residueEval]
  rw [sum_reduceResidue (fun x => stdAddChar (reduceResidue t q b * residueEval F q x))]
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  push_cast
  rw [mul_pow]
  field_simp


private theorem mul_lift_val {t q : ℕ} [NeZero t] [NeZero q] (b : ZMod q) :
    ((t * b.val : ℕ) : ZMod (t * q)).val = t * b.val :=
  ZMod.val_natCast_of_lt (Nat.mul_lt_mul_of_pos_left b.val_lt (NeZero.pos t))

private def multiplesOfEquiv {t q : ℕ} [NeZero t] [NeZero q] :
    ZMod q ≃ {a : ZMod (t * q) // t ∣ a.val} :=
  Equiv.ofBijective
    (fun b => ⟨((t * b.val : ℕ) : ZMod (t * q)),
      by rw [mul_lift_val]; exact dvd_mul_right t b.val⟩)
    ⟨by
        intro b c h
        have hv := congrArg (fun a : {a : ZMod (t * q) // t ∣ a.val} => a.val.val) h
        change ((t * b.val : ℕ) : ZMod (t * q)).val =
          ((t * c.val : ℕ) : ZMod (t * q)).val at hv
        rw [mul_lift_val, mul_lift_val] at hv
        have hbc : b.val = c.val := Nat.eq_of_mul_eq_mul_left (NeZero.pos t) hv
        exact (ZMod.val_injective q) hbc,
      by
        intro a
        obtain ⟨b, hb⟩ := a.property
        have hlt := a.val.val_lt
        rw [hb] at hlt
        have hbq : b < q := Nat.lt_of_mul_lt_mul_left hlt
        refine ⟨(b : ZMod q), Subtype.ext ?_⟩
        change ((t * (b : ZMod q).val : ℕ) : ZMod (t * q)) = a.val
        rw [ZMod.val_natCast_of_lt hbq, ← hb, ZMod.natCast_zmod_val]⟩

private def unitsEquivIsUnit (q : ℕ) : (ZMod q)ˣ ≃ {a : ZMod q // IsUnit a} where
  toFun a := ⟨a, a.isUnit⟩
  invFun a := a.prop.unit
  left_inv a := Units.ext a.isUnit.unit_spec
  right_inv a := Subtype.ext a.prop.unit_spec

private theorem sum_completeSum_step (F : MvPolynomial (Fin n) ℤ)
    (t q : ℕ) [NeZero t] [NeZero q]
    (hunit : ∀ a : ZMod (t * q), ¬IsUnit a ↔ t ∣ a.val) :
    (∑ a : ZMod (t * q), completeSum F (t * q) a) =
      unitConductorSum F (t * q) + ∑ b : ZMod q, completeSum F q b := by
  classical
  let e : ZMod q ≃ {a : ZMod (t * q) // ¬IsUnit a} :=
    multiplesOfEquiv.trans (Equiv.subtypeEquivRight (fun a => (hunit a).symm))
  have he (b : ZMod q) : (e b).val = ((t * b.val : ℕ) : ZMod (t * q)) := rfl
  have hnonunit : (∑ a : {a : ZMod (t*q) // ¬IsUnit a}, completeSum F (t*q) a.val) =
      ∑ b : ZMod q, completeSum F q b := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    rw [he, Nat.cast_mul, completeSum_of_mul_lift, map_natCast, ZMod.natCast_zmod_val]
  unfold unitConductorSum
  rw [← (Fintype.sum_subtype_add_sum_subtype IsUnit (completeSum F (t*q))), hnonunit]
  congr 1
  exact (unitsEquivIsUnit (t*q)).sum_comp (fun a => completeSum F (t*q) a.val) |>.symm

private theorem sum_completeSum_primePower_step
    (F : MvPolynomial (Fin n) ℤ) (p m : ℕ) [Fact p.Prime] [NeZero p] :
    (∑ a : ZMod (p ^ (m + 1)), completeSum F (p ^ (m + 1)) a) =
      unitConductorSum F (p ^ (m + 1)) + ∑ b : ZMod (p ^ m), completeSum F (p ^ m) b := by
  have hunit (s : ℕ) [NeZero s] (hs : s = p ^ (m + 1)) (a : ZMod s) :
      ¬ IsUnit a ↔ p ∣ a.val := by
    subst s
    exact (congrArg IsUnit (ZMod.natCast_zmod_val a).symm).to_iff.not.trans
      ((ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (Nat.succ_pos m)).not.trans not_not)
  have hstep (s : ℕ) [NeZero s] (hs : s = p * p ^ m) :
      (∑ a : ZMod s, completeSum F s a) =
        unitConductorSum F s + ∑ b : ZMod (p ^ m), completeSum F (p ^ m) b := by
    subst s
    exact sum_completeSum_step F p (p ^ m) (hunit _ (pow_succ' _ _).symm)
  exact hstep _ (pow_succ' _ _)

private theorem sum_completeSum_primePowers (F : MvPolynomial (Fin n) ℤ)
    (p m : ℕ) [Fact p.Prime] [NeZero p] :
    (∑ a : ZMod (p ^ m), completeSum F (p ^ m) a) =
      ∑ j ∈ Finset.range (m + 1), unitConductorSum F (p ^ j) := by
  induction m with
  | zero =>
    rw [Finset.sum_range_one]
    change (∑ a : ZMod 1, completeSum F 1 a) = unitConductorSum F 1
    unfold unitConductorSum
    rw [Fintype.sum_unique, Fintype.sum_unique]
    exact congrArg (completeSum F 1) (Subsingleton.elim _ _)
  | succ m ih =>
    rw [sum_completeSum_primePower_step, ih, Finset.sum_range_succ (n := m + 1)]
    exact add_comm _ _

/-- Orthogonality followed by splitting the numerators by their exact conductor.

This is the normalized zero-count identity in the major-arc section, including
the level `j = 0` and the case `m = 0`.
-/
theorem primePower_density_eq_sum (F : MvPolynomial (Fin n) ℤ)
    (p m : ℕ) [Fact p.Prime] [NeZero p] (hn : 1 ≤ n) :
    (((p ^ m : ℕ) : ℂ) ^ (n - 1))⁻¹ * (residueZeroCount F (p ^ m) : ℂ) =
      ∑ j ∈ Finset.range (m + 1), unitConductorSum F (p ^ j) := by
  rw [← sum_completeSum_eq_density F (p ^ m) hn]
  exact sum_completeSum_primePowers F p m


/-- Pair the gradient evaluated at `x` with the vector `z`. -/
def directionEval (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (x z : Fin n → ZMod q) : ZMod q :=
  ∑ i, z i * residueEval (MvPolynomial.pderiv i F) q x

private theorem directionEval_add (F G : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (x z : Fin n → ZMod q) :
    directionEval (F + G) q x z = directionEval F q x z + directionEval G q x z := by
  simp only [directionEval, residueEval, map_add, MvPolynomial.eval₂_add, mul_add, Finset.sum_add_distrib]

private theorem directionEval_mul (F G : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (x z : Fin n → ZMod q) :
    directionEval (F * G) q x z =
      directionEval F q x z * residueEval G q x + residueEval F q x * directionEval G q x z := by
  simp only [directionEval, residueEval, MvPolynomial.pderiv_mul,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

private theorem directionEval_X (q : ℕ) (x z : Fin n → ZMod q) (j : Fin n) :
    directionEval (MvPolynomial.X j) q x z = z j := by
  classical
  unfold directionEval
  rw [Finset.sum_eq_single j]
  · simp [residueEval]
  · intro i _ hij
    rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
    simp [residueEval]
  · simp

/-- First-order Taylor expansion in a residue ring when the step has square zero. -/
theorem residueEval_add_squareZero (F : MvPolynomial (Fin n) ℤ) (q : ℕ)
    (x z : Fin n → ZMod q) (s : ZMod q) (hs : s*s = 0) :
    residueEval F q (fun i => x i + s * z i) =
      residueEval F q x + s * directionEval F q x z := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [residueEval, directionEval, MvPolynomial.pderiv_C, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_zero, mul_zero, Finset.sum_const_zero, add_zero]
  | add F G ihF ihG =>
    rw [directionEval_add]
    simp only [residueEval, MvPolynomial.eval₂_add] at ihF ihG ⊢
    rw [ihF, ihG]
    ring
  | mul_X F j ih =>
    rw [directionEval_mul, directionEval_X]
    simp only [residueEval, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at ih ⊢
    rw [ih]
    calc
      _ = (MvPolynomial.eval₂ (Int.castRingHom (ZMod q)) x F * x j +
          s * (directionEval F q x z * x j +
            MvPolynomial.eval₂ (Int.castRingHom (ZMod q)) x F * z j)) +
          (s*s) * (directionEval F q x z * z j) := by ring
      _ = _ := by rw [hs, zero_mul, add_zero]


private theorem sum_stdAddChar_dot {p : ℕ} [NeZero p] (g : Fin n → ZMod p) :
    (∑ z : Fin n → ZMod p, stdAddChar (∑ i, z i * g i)) =
      if g = 0 then (p : ℂ)^n else 0 := by
  classical
  let ψ : AddChar (Fin n → ZMod p) ℂ :=
    { toFun := fun z => stdAddChar (∑ i, z i * g i)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro a b
        simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul] }
  split_ifs with hg
  · simp [hg, ZMod.card, nsmul_eq_mul]
  · change (∑ z, ψ z) = 0
    apply AddChar.sum_eq_zero_of_ne_one
    intro hψ
    have hg' : ∃ i, g i ≠ 0 := by
      by_contra! h
      exact hg (funext h)
    obtain ⟨i, hi⟩ := hg'
    have hsingle : ψ (Pi.single i 1) = stdAddChar (g i) := by
      change stdAddChar (∑ j, Pi.single i 1 j * g j) = _
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    have hc := congrArg (fun χ : AddChar (Fin n → ZMod p) ℂ => χ (Pi.single i 1)) hψ
    rw [hsingle, AddChar.one_apply] at hc
    exact hi (ZMod.injective_stdAddChar (hc.trans (AddChar.map_zero_eq_one _).symm))


/-- A square-zero digit average cancels a weighted sum supported in nonstationary
classes, provided the weight is invariant under the digit translations. -/
theorem weightedSum_eq_zero_of_nonstationary (F : MvPolynomial (Fin n) ℤ) {t q Q : ℕ}
    [NeZero t] [NeZero q] [NeZero Q] (hQ : Q = t * q) (hdiv : q ∣ t) (hred : q ∣ Q)
    (a : ZMod Q) (ha : IsUnit (ZMod.castHom hred (ZMod q) a))
    (w : (Fin n → ZMod Q) → ℂ)
    (hw : ∀ x (z : Fin n → ZMod q),
      w (x + fun i => (t : ZMod Q) * (z i).val) = w x)
    (hgrad : ∀ x, w x ≠ 0 → ∃ i, residueEval (MvPolynomial.pderiv i F) q
      (fun j => ZMod.castHom hred (ZMod q) (x j)) ≠ 0) :
    (∑ x : Fin n → ZMod Q, w x * stdAddChar (a * residueEval F Q x)) = 0 := by
  classical
  subst Q
  change IsUnit (reduceResidue t q a) at ha
  change ∀ x, w x ≠ 0 → ∃ i, residueEval (MvPolynomial.pderiv i F) q
    (fun j => reduceResidue t q (x j)) ≠ 0 at hgrad
  let Q := t * q
  let s : ZMod Q := t
  let f (x : Fin n → ZMod Q) := w x * stdAddChar (a * residueEval F Q x)
  let shift (z : Fin n → ZMod q) : Fin n → ZMod Q := fun i => s * ↑(z i).val
  let grad (x : Fin n → ZMod Q) (i : Fin n) :=
    reduceResidue t q a * residueEval (MvPolynomial.pderiv i F) q (fun j => reduceResidue t q (x j))
  have hs : s*s = 0 := by
    change (t : ZMod Q) * (t : ZMod Q) = 0
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.mul_dvd_mul_left _ hdiv
  have hshift (x : Fin n → ZMod Q) (z : Fin n → ZMod q) :
      f (x + shift z) = f x * stdAddChar (∑ i, z i * grad x i) := by
    unfold f
    rw [hw]
    change w x * stdAddChar (a * residueEval F Q (fun i => x i + s * ↑(z i).val)) = _
    rw [residueEval_add_squareZero _ _ _ _ _ hs, mul_add, AddChar.map_add_eq_mul, mul_assoc]
    congr 1
    rw [mul_left_comm a s, stdAddChar_of_mul_lift]
    simp only [grad, directionEval, map_mul, map_sum, map_natCast,
      ZMod.natCast_zmod_val]
    rw [Finset.mul_sum]
    apply congrArg (fun t : ZMod q => stdAddChar (a * residueEval F Q x) * stdAddChar t)
    apply Finset.sum_congr rfl
    intro i _
    rw [hom_residueEval]
    ring
  have hpoint (x : Fin n → ZMod Q) : (∑ z : Fin n → ZMod q, f (x + shift z)) = 0 := by
    simp_rw [hshift, ← Finset.mul_sum, sum_stdAddChar_dot]
    by_cases hx : w x = 0
    · simp [f, hx]
    · obtain ⟨i, hi⟩ := hgrad x hx
      have hg : grad x ≠ 0 := by
        intro h
        have H := congrFun h i
        change reduceResidue t q a * _ = 0 at H
        exact hi ((IsUnit.mul_right_eq_zero ha).mp H)
      rw [if_neg hg, mul_zero]
  have htranslate (z : Fin n → ZMod q) :
      (∑ x : Fin n → ZMod Q, f (x + shift z)) = ∑ x, f x :=
    Equiv.sum_comp (Equiv.addRight (shift z)) f
  have havg : (q : ℂ)^n * (∑ x : Fin n → ZMod Q, f x) =
      ∑ x : Fin n → ZMod Q, ∑ z : Fin n → ZMod q, f (x + shift z) := by
    rw [Finset.sum_comm]
    simp_rw [htranslate]
    simp [ZMod.card, nsmul_eq_mul]
  simp only [hpoint, Finset.sum_const_zero] at havg
  refine (mul_eq_zero.mp havg).resolve_left ?_
  exact pow_ne_zero _ (by exact_mod_cast NeZero.ne q)

/-- Reduction of residues modulo a prime power of exponent at least two to its underlying prime. -/
def reduceAtPrime (p k : ℕ) : ZMod (p^(k+2)) →+* ZMod p :=
  reduceResidue (p^(k+1)) p

/-- The last-digit average leaves only the stationary residue classes. -/
theorem completeSum_eq_stationary (F : MvPolynomial (Fin n) ℤ) (p k : ℕ)
    [Fact p.Prime] [NeZero p] (a : ZMod (p^(k+2))) (ha : reduceAtPrime p k a ≠ 0) :
    completeSum F (p^(k+2)) a = ((p^(k+2) : ℂ)^n)⁻¹ *
      ∑ x : Fin n → ZMod (p^(k+2)),
        if (∀ i, residueEval (MvPolynomial.pderiv i F) p (fun j => reduceAtPrime p k (x j)) = 0)
        then stdAddChar (a * residueEval F (p^(k+2)) x) else 0 := by
  classical
  let q : ℕ := p^(k+2)
  let s : ZMod q := ((p^(k+1) : ℕ) : ZMod q)
  let phase (x : Fin n → ZMod q) := stdAddChar (a * residueEval F q x)
  let shift (z : Fin n → ZMod p) : Fin n → ZMod q := fun i => s * ↑(z i).val
  let grad (x : Fin n → ZMod q) (i : Fin n) :=
    residueEval (MvPolynomial.pderiv i F) p (fun j => reduceAtPrime p k (x j))
  let weightedGrad (x : Fin n → ZMod q) (i : Fin n) := reduceAtPrime p k a * grad x i
  have hs : s*s = 0 := by
    change ((p^(k+1) : ℕ) : ZMod q) * ((p^(k+1) : ℕ) : ZMod q) = 0
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, ← pow_add]
    exact Nat.pow_dvd_pow _ (by omega)
  have hshift (x : Fin n → ZMod q) (z : Fin n → ZMod p) :
      phase (x + shift z) = phase x * stdAddChar (∑ i, z i * weightedGrad x i) := by
    change stdAddChar (a * residueEval F q (fun i => x i + s * ↑(z i).val)) = _
    rw [residueEval_add_squareZero _ _ _ _ _ hs, mul_add, AddChar.map_add_eq_mul]
    congr 1
    rw [mul_left_comm a s]
    change stdAddChar (((p^(k+1) : ℕ) : ZMod q) *
      (a * directionEval F q x (fun i => ↑(z i).val))) = _
    have hLift : stdAddChar (N := q) (((p^(k+1) : ℕ) : ZMod q) *
        (a * directionEval F q x (fun i => ↑(z i).val))) =
        stdAddChar (reduceResidue (p^(k+1)) p (a * directionEval F q x (fun i => ↑(z i).val))) :=
      stdAddChar_of_mul_lift (t := p^(k+1)) (q := p) _
    rw [hLift]
    let red : ZMod q →+* ZMod p := reduceAtPrime p k
    change stdAddChar (red (a * directionEval F q x (fun i => ↑(z i).val))) = _
    simp only [directionEval, map_mul, map_sum, map_natCast, hom_residueEval,
      ZMod.natCast_zmod_val, weightedGrad, grad]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum_shift (z : Fin n → ZMod p) :
      (∑ x : Fin n → ZMod q, phase (x + shift z)) = ∑ x, phase x :=
    Equiv.sum_comp (Equiv.addRight (shift z)) phase
  have havg : (p : ℂ)^n * (∑ x : Fin n → ZMod q, phase x) =
      ∑ x : Fin n → ZMod q, ∑ z : Fin n → ZMod p, phase (x + shift z) := by
    rw [Finset.sum_comm]
    simp_rw [hsum_shift]
    simp [ZMod.card, nsmul_eq_mul]
  have hcriterion (x : Fin n → ZMod q) : weightedGrad x = 0 ↔ ∀ i, grad x i = 0 := by
    simp only [funext_iff, weightedGrad, Pi.zero_apply, mul_eq_zero, ha, false_or]
  have hpoint (x : Fin n → ZMod q) :
      (∑ z : Fin n → ZMod p, phase (x + shift z)) =
        (p : ℂ)^n * (if (∀ i, grad x i = 0) then phase x else 0) := by
    simp_rw [hshift, ← Finset.mul_sum, sum_stdAddChar_dot, hcriterion]
    split_ifs <;> simp [mul_comm]
  simp_rw [hpoint, ← Finset.mul_sum] at havg
  have hp : (p : ℂ)^n ≠ 0 := pow_ne_zero _ (by exact_mod_cast NeZero.ne p)
  have heq := mul_left_cancel₀ hp havg
  unfold completeSum
  push_cast
  exact congrArg (fun z : ℂ => (((p : ℂ)^(k+2))^n)⁻¹ * z) heq

/-- A complete sum at a prime square is bounded by the number of critical
residues of the phase over the prime field, divided by `p^n`. -/
theorem norm_completeSum_primeSquare_le {p : ℕ} [Fact p.Prime] [NeZero p]
    (F : MvPolynomial (Fin n) ℤ) (a : ZMod (p^2)) (ha : reduceAtPrime p 0 a ≠ 0) :
    ‖completeSum F (p^2) a‖ ≤
      ((Finset.univ.filter (fun x : Fin n → ZMod p =>
        ∀ i, residueEval (MvPolynomial.pderiv i F) p x = 0)).card : ℝ) / (p : ℝ)^n := by
  classical
  let critical (x : Fin n → ZMod p) := ∀ i, residueEval (MvPolynomial.pderiv i F) p x = 0
  let indicator (x : Fin n → ZMod p) : ℝ := if critical x then 1 else 0
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  have hsum : (∑ x : Fin n → ZMod (p^2), indicator (fun j => reduceAtPrime p 0 (x j))) =
      (p : ℝ)^n * ((Finset.univ.filter critical).card : ℝ) := by
    rw [show ((Finset.univ.filter critical).card : ℝ) = ∑ x, indicator x by
      unfold indicator
      rw [← Finset.sum_filter]
      simp]
    change (∑ x : Fin n → ZMod (p^1 * p),
      indicator (fun j => reduceResidue (p^1) p (x j))) = _
    rw [sum_reduceResidue, pow_one]
  rw [completeSum_eq_stationary F p 0 a ha, norm_mul, norm_inv, norm_pow, norm_pow,
    Complex.norm_natCast]
  have hbound := norm_sum_le (Finset.univ : Finset (Fin n → ZMod (p^2)))
    (fun x => if critical (fun j => reduceAtPrime p 0 (x j))
      then stdAddChar (a * residueEval F (p^2) x) else 0)
  have hnorm (v : ZMod (p^2)) : ‖stdAddChar v‖ = 1 := by simp [stdAddChar_apply]
  simp only [apply_ite norm, norm_zero, hnorm] at hbound
  change ‖∑ x : Fin n → ZMod (p^2), if critical (fun j => reduceAtPrime p 0 (x j))
    then stdAddChar (a * residueEval F (p^2) x) else 0‖ ≤ _ at hbound
  rw [hsum] at hbound
  refine (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq ?_
  rw [← pow_mul, show 2 * n = n + n by omega, pow_add]
  field_simp
  congr 1


private theorem sum_divisible_vectors {t q Q : ℕ} [NeZero t] [NeZero q] [NeZero Q]
    (hQ : Q = t*q) (f : (Fin n → ZMod Q) → ℂ) :
    (∑ x : Fin n → ZMod Q, if (∀ i, t ∣ (x i).val) then f x else 0) =
      ∑ y : Fin n → ZMod q, f (fun i => ((t*(y i).val : ℕ) : ZMod Q)) := by
  subst Q
  classical
  let ePi : (Fin n → {a : ZMod (t*q) // t ∣ a.val}) ≃
      {x : Fin n → ZMod (t*q) // ∀ i, t ∣ (x i).val} :=
    { toFun := fun x => ⟨fun i => (x i).val, fun i => (x i).prop⟩
      invFun := fun x i => ⟨x.val i, x.prop i⟩
      left_inv := by intro x; funext i; rfl
      right_inv := by intro x; rfl }
  let e : (Fin n → ZMod q) ≃ {x : Fin n → ZMod (t*q) // ∀ i, t ∣ (x i).val} :=
    (Equiv.piCongrRight (fun _ : Fin n => multiplesOfEquiv)).trans ePi
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  calc
    _ = ∑ y : Fin n → ZMod q, f (e y).val :=
      (Equiv.sum_comp e (fun x => f x.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rfl

private theorem residueEval_mul_coordinates (F : MvPolynomial (Fin n) ℤ) (d q : ℕ)
    (hF : F.IsHomogeneous d) (y : Fin n → ZMod q) (c : ZMod q) :
    residueEval F q (fun i => c * y i) = c^d * residueEval F q y := by
  unfold residueEval
  rw [F.as_sum]
  simp only [MvPolynomial.eval₂_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hdeg : v.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hF (MvPolynomial.mem_support_iff.mp hv)
  simp only [MvPolynomial.eval₂_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hdeg]
  ring


/-- Lifting a numerator by the modulus ratio preserves the standard character. -/
theorem stdAddChar_mul_factor {t q Q : ℕ} [NeZero t] [NeZero q] [NeZero Q]
    (hQ : Q = t*q) (h : q ∣ Q) (a : ZMod Q) :
    stdAddChar ((t : ZMod Q) * a) = stdAddChar (ZMod.castHom h (ZMod q) a) := by
  subst Q
  exact stdAddChar_of_mul_lift a

private theorem reduceResidue_cast_lift {q Q M : ℕ} [NeZero M]
    (h : q ∣ Q) (b : ZMod M) (hq : q ∣ M) :
    ZMod.castHom h (ZMod q) (b.val : ZMod Q) = ZMod.castHom hq (ZMod q) b := by
  conv_rhs => rw [← ZMod.natCast_zmod_val b]
  simp only [map_natCast]

private theorem sum_reduce_of_factor {t q M : ℕ} [NeZero t] [NeZero q] [NeZero M]
    (hM : M = t*q) (h : q ∣ M) (f : (Fin n → ZMod q) → ℂ) :
    (∑ x : Fin n → ZMod M, f (fun i => ZMod.castHom h (ZMod q) (x i))) =
      (t : ℂ)^n * ∑ x : Fin n → ZMod q, f x := by
  subst M
  exact sum_reduceResidue f

private theorem reduceAtPrime_eq_zero_iff (p k : ℕ) [NeZero p] (x : ZMod (p^(k+2))) :
    reduceAtPrime p k x = 0 ↔ p ∣ x.val := by
  have h : reduceAtPrime p k x = (x.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    exact map_natCast _ _
  rw [h, ZMod.natCast_eq_zero_iff]

/-- Homogeneous scaling on the vectors divisible by the underlying prime. -/
theorem divisibleVectorSum_eq_completeSum (F : MvPolynomial (Fin n) ℤ) (p k d : ℕ)
    [NeZero p] (hF : F.IsHomogeneous d) (hd : 1 ≤ d) (a : ℤ) :
    ((p^(k+2) : ℂ)^n)⁻¹ *
      (∑ x : Fin n → ZMod (p^(k+2)),
        if (∀ i, p ∣ (x i).val) then stdAddChar ((a : ZMod (p^(k+2))) *
          residueEval F (p^(k+2)) x) else 0) =
      ((p : ℂ)^n)⁻¹ * completeSum F (p^(k+2-d)) (a : ZMod (p^(k+2-d))) := by
  classical
  let m := k+2
  let e := min d m
  let q := p^(m-d)
  let t := p^(e-1)
  have hmodulus : p^m = p * p^(k+1) := pow_succ' _ _
  rw [sum_divisible_vectors hmodulus
    (fun x => stdAddChar ((a : ZMod (p^m)) * residueEval F (p^m) x))]
  have hfactor : p^m = p^e * q := by
    dsimp [q]
    rw [← pow_add]
    congr 1
    dsimp [e]
    omega
  have hqQ : q ∣ p^m := Nat.pow_dvd_pow _ (Nat.sub_le _ _)
  have hqM : q ∣ p^(k+1) := Nat.pow_dvd_pow _ (by dsimp [m]; omega)
  have hr : p^(k+1) = t*q := by
    dsimp [t,q]
    rw [← pow_add]
    congr 1
    dsimp [e,m]
    omega
  have hpowe : ((p : ZMod (p^m))^d) = ((p^e : ℕ) : ZMod (p^m)) := by
    rw [← Nat.cast_pow]
    by_cases hdm : d ≤ m
    · rw [show e = d from min_eq_left hdm]
    · have he : e = m := min_eq_right (by omega)
      rw [he, ZMod.natCast_self]
      exact (ZMod.natCast_eq_zero_iff _ _).2 (Nat.pow_dvd_pow _ (by omega))
  have hphase (y : Fin n → ZMod (p^(k+1))) :
      stdAddChar ((a : ZMod (p^m)) * residueEval F (p^m)
          (fun i => ((p*(y i).val : ℕ) : ZMod (p^m)))) =
        stdAddChar ((a : ZMod q) * residueEval F q
          (fun i => ZMod.castHom hqM (ZMod q) (y i))) := by
    simp only [Nat.cast_mul, residueEval_mul_coordinates F d (p^m) hF]
    rw [mul_left_comm (a : ZMod (p^m)), hpowe, stdAddChar_mul_factor hfactor hqQ,
      map_mul, map_intCast]
    congr 2
    rw [residueEval, MvPolynomial.hom_eval₂]
    change F.eval₂ ((ZMod.castHom hqQ (ZMod q)).comp (Int.castRingHom (ZMod (p^m)))) _ =
      F.eval₂ (Int.castRingHom (ZMod q)) _
    congr 1
    · ext
      simp
    · funext i
      exact reduceResidue_cast_lift hqQ (y i) hqM
  simp_rw [hphase]
  rw [sum_reduce_of_factor hr hqM (fun x => stdAddChar ((a : ZMod q) * residueEval F q x))]
  unfold completeSum
  change (((p : ℂ)^m)^n)⁻¹ *
      ((t : ℂ)^n * ∑ x : Fin n → ZMod q, stdAddChar ((a : ZMod q) * residueEval F q x)) =
    ((p : ℂ)^n)⁻¹ *
      (((q : ℂ)^n)⁻¹ * ∑ x : Fin n → ZMod q, stdAddChar ((a : ZMod q) * residueEval F q x))
  have hQ : p^m = p*(t*q) := by rw [← hr]; exact hmodulus
  have hQc : (p : ℂ)^m = (p : ℂ)*((t : ℂ)*(q : ℂ)) := by exact_mod_cast hQ
  rw [hQc]
  simp only [mul_pow]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  field_simp

private theorem completeSum_primePower_recurrence_aux (F : MvPolynomial (Fin n) ℤ) (p k d : ℕ)
    [Fact p.Prime] [NeZero p] (hF : F.IsHomogeneous d) (hd : 1 ≤ d)
    (hsmooth : ∀ x : Fin n → ZMod p,
      (∀ i, residueEval (MvPolynomial.pderiv i F) p x = 0) ↔ x = 0)
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    completeSum F (p^(k+2)) (a : ZMod (p^(k+2))) =
      ((p : ℂ)^n)⁻¹ * completeSum F (p^(k+2-d)) (a : ZMod (p^(k+2-d))) := by
  classical
  have hred : reduceAtPrime p k (a : ZMod (p^(k+2))) ≠ 0 := by
    rwa [map_intCast]
  rw [completeSum_eq_stationary F p k _ hred]
  simp_rw [hsmooth, funext_iff, Pi.zero_apply, reduceAtPrime_eq_zero_iff]
  exact divisibleVectorSum_eq_completeSum F p k d hF hd a


/-- The unique character and residue vector at conductor one give sum one. -/
theorem completeSum_one (F : MvPolynomial (Fin n) ℤ) (a : ZMod 1) :
    completeSum F 1 a = 1 := by
  have h (x : Fin n → ZMod 1) : a * residueEval F 1 x = 0 := Subsingleton.elim _ _
  simp only [completeSum, h, AddChar.map_zero_eq_one, Fintype.sum_unique, Nat.cast_one,
    one_pow, inv_one, one_mul]

/-- The conductor-one term of the singular series is one. -/
theorem unitConductorSum_one (F : MvPolynomial (Fin n) ℤ) : unitConductorSum F 1 = 1 := by
  simp only [unitConductorSum, Fintype.sum_unique, completeSum_one]

/-- Good-prime recurrence for every depth at least two. In the notation of
`lem:complete-all-primes-clean`, the depth on the right is `max (m - d) 0`. -/
theorem completeSum_primePower_recurrence (F : MvPolynomial (Fin n) ℤ) (p m d : ℕ)
    [Fact p.Prime] [NeZero p] (hm : 2 ≤ m) (hF : F.IsHomogeneous d) (hd : 1 ≤ d)
    (hsmooth : ∀ x : Fin n → ZMod p,
      (∀ i, residueEval (MvPolynomial.pderiv i F) p x = 0) ↔ x = 0)
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    completeSum F (p^m) (a : ZMod (p^m)) =
      ((p : ℂ)^n)⁻¹ * completeSum F (p^(m-d)) (a : ZMod (p^(m-d))) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k+2 := ⟨m-2, by omega⟩
  exact completeSum_primePower_recurrence_aux F p k d hF hd hsmooth a ha

/-- Good-prime initial values in `lem:complete-all-primes-clean`. -/
theorem completeSum_primePower_initial (F : MvPolynomial (Fin n) ℤ) (p m d : ℕ)
    [Fact p.Prime] [NeZero p] (hm : 2 ≤ m) (hmd : m ≤ d) (hF : F.IsHomogeneous d)
    (hsmooth : ∀ x : Fin n → ZMod p,
      (∀ i, residueEval (MvPolynomial.pderiv i F) p x = 0) ↔ x = 0)
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    completeSum F (p^m) (a : ZMod (p^m)) = ((p : ℂ)^n)⁻¹ := by
  rw [completeSum_primePower_recurrence F p m d hm hF (by omega) hsmooth a ha]
  have hone (q : ℕ) [NeZero q] (hq : q = 1) :
      completeSum F q (a : ZMod q) = 1 := by
    subst q
    exact completeSum_one _ _
  rw [hone _ (by simp [Nat.sub_eq_zero_of_le hmd]), mul_one]

end

end Birch
