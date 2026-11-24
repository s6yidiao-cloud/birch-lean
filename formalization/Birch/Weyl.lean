import Birch.CircleMethod
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The initial minor-arc bound

The fixed-height Weyl estimate from Browning–Prendiville, Lemma 3.3, is an explicit
input. Dirichlet approximation and the deduction of a power saving are proved here.
-/

open Filter
open scoped Topology

namespace Birch

noncomputable section

/-- The rational-approximation separation used in Weyl differencing.
This is the integer determinant step of Browning--Prendiville, Lemma 2.3. -/
theorem primitive_frequency_separation {α : ℝ} {q : ℕ} (hq : 0 < q) (a m b : ℤ)
    (hcop : a.natAbs.Coprime q)
    (h₁ : |(m : ℝ)| * |(q : ℝ) * α - a| < 1/2)
    (h₂ : (q : ℝ) * |(m : ℝ) * α - b| < 1/2)
    (hsmall : m.natAbs < q ∨ |(m : ℝ) * α - b| < |(q : ℝ) * α - a|) :
    m = 0 := by
  have hqr : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hdetR : |(m : ℝ)*a-(q : ℝ)*b| < 1 := by
    calc
      _ = |(q : ℝ)*((m : ℝ)*α-b)-(m : ℝ)*((q : ℝ)*α-a)| := by congr 1; ring
      _ ≤ |(q : ℝ)*((m : ℝ)*α-b)| + |(m : ℝ)*((q : ℝ)*α-a)| := abs_sub _ _
      _ < 1 := by rw [abs_mul, abs_mul, abs_of_nonneg hqr]; linarith
  have hdetZ : |m*a-(q : ℤ)*b| < 1 := by exact_mod_cast hdetR
  have hdet := abs_lt.mp hdetZ
  have hma : m*a = (q : ℤ)*b := by omega
  have hcopZ : IsCoprime (q : ℤ) a := Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa only [Int.gcd, Int.natAbs_natCast] using hcop.symm)
  have hmdiv : (q : ℤ) ∣ m := hcopZ.dvd_of_dvd_mul_right ⟨b, hma⟩
  by_contra hm
  rcases hsmall with hsmall | hsmall
  · have hdiv : q ∣ m.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hmdiv
    exact hsmall.not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hm) hdiv)
  · obtain ⟨k, hk⟩ := hmdiv
    have hk₀ : k ≠ 0 := by intro h; exact hm (by simp [hk, h])
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have hb : b = k*a := by
      rw [hk, mul_assoc] at hma
      exact (mul_left_cancel₀ hqZ hma).symm
    have hkR : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hkZ : (1 : ℤ) ≤ |k| := by
        have h := abs_pos.mpr hk₀
        omega
      exact_mod_cast hkZ
    have H : |(m : ℝ)*α-b| = |(k : ℝ)| * |(q : ℝ)*α-a| := by
      rw [hk, hb]
      push_cast
      rw [show (q : ℝ)*k*α-k*a = k*((q : ℝ)*α-a) by ring, abs_mul]
    rw [H] at hsmall
    exact hsmall.not_ge (le_mul_of_one_le_left (abs_nonneg _) hkR)

/-- The fixed-leading-form Weyl bound used in the source. A reduced numerator
within distance one half is a nearest integer, including the possible tie. -/
def WeylEstimate (d n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C > 0, ∀ᶠ P in atTop, ∀ (α : ℝ) (a : ℤ) (q : ℕ),
    0 < q → a.natAbs.Coprime q → |(q : ℝ) * α - a| ≤ 1 / 2 →
      (f P α) ^ (2 ^ (d - 1) : ℕ) ≤ C * P ^ ε *
        (P ^ (1 - (d : ℝ)) + |(q : ℝ) * α - a| + q * P ^ (-(d : ℝ)) +
          1 / (q : ℝ)) ^ ((n : ℝ) / ((d : ℝ) - 1))

/-- An explicit initial saving depending only on the degree and dimension. -/
def weylSaving (d n : ℕ) : ℝ :=
  (n : ℝ) / (4 * ((d : ℝ) - 1) * ((2 ^ (d - 1) : ℕ) : ℝ))

theorem weylSaving_pos {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) : 0 < weylSaving d n := by
  have hD : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  unfold weylSaving
  positivity

/-- Dirichlet approximation at scale (P^{d-1/2}) provides a reduced approximant
with a denominator beyond the major-arc cutoff. -/
theorem exists_minorArc_approximation {d : ℕ} (hd : 2 ≤ d) {P α : ℝ}
    (hP : 2 ≤ P) (hα : α ∈ (majorArcs d P)ᶜ) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ a.natAbs.Coprime q ∧
      P ^ (1 / 2 : ℝ) < (q : ℝ) ∧ (q : ℝ) ≤ P ^ ((d : ℝ) - 1 / 2) ∧
      |(q : ℝ) * α - a| ≤ P ^ (-(d : ℝ) + 1 / 2) := by
  let Q : ℝ := P ^ ((d : ℝ) - 1 / 2)
  let N : ℕ := ⌊Q⌋₊
  have hP₁ : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : 2 ≤ Q := by
    calc
      2 ≤ P := hP
      _ = P ^ (1 : ℝ) := (Real.rpow_one P).symm
      _ ≤ Q := Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
  have hN : 0 < N := by
    apply Nat.floor_pos.mpr
    linarith
  obtain ⟨b, hb, hbN⟩ := Real.exists_rat_abs_sub_le_and_den_le α hN
  have hq : (0 : ℝ) < b.den := Nat.cast_pos.mpr b.pos
  have hNQ : (N : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hqQ : (b.den : ℝ) ≤ Q := (Nat.cast_le.mpr hbN).trans hNQ
  have hbcast : (b : ℝ) = (b.num : ℝ) / (b.den : ℝ) := Rat.cast_def b
  have hmul :
      |(b.den : ℝ) * α - b.num| = |α - (b : ℝ)| * (b.den : ℝ) := by
    calc
      _ = |(α - (b : ℝ)) * (b.den : ℝ)| := by
        congr 1
        rw [hbcast]
        field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hq]
  have hNplus : Q < (N : ℝ) + 1 := Nat.lt_floor_add_one Q
  have hqNplus : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have herror : |(b.den : ℝ) * α - b.num| ≤ P ^ (-(d : ℝ) + 1 / 2) := by
    calc
      _ = |α - (b : ℝ)| * (b.den : ℝ) := hmul
      _ ≤ (1 / (((N : ℝ) + 1) * (b.den : ℝ))) * (b.den : ℝ) :=
        mul_le_mul_of_nonneg_right hb hq.le
      _ = 1 / ((N : ℝ) + 1) := by field_simp
      _ ≤ 1 / Q := one_div_le_one_div_of_le (by linarith) hNplus.le
      _ = _ := by
        change 1 / P ^ ((d : ℝ) - 1 / 2) = _
        rw [show -(d : ℝ) + 1 / 2 = -((d : ℝ) - 1 / 2) by ring,
          Real.rpow_neg hPpos.le, one_div]
  refine ⟨b.num, b.den, b.pos, b.reduced, ?_, hqQ, herror⟩
  by_contra! hsmall
  apply hα
  refine ⟨b.den, b.num, b.pos, hsmall, b.reduced, ?_⟩
  rw [le_div_iff₀ hq, ← hbcast, ← hmul]
  exact herror.trans (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith))

/-- The initial pointwise saving throughout the minor arcs, conditional on the stated
fixed-height Weyl estimate. -/
theorem initialMinor_of_weyl {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    {f : ℝ → ℝ → ℝ} (hW : WeylEstimate d n f) :
    ∃ K > 0, ∀ᶠ P in atTop, ∀ α ∈ (majorArcs d P)ᶜ,
      f P α ≤ K * P ^ (-weylSaving d n) := by
  let D : ℕ := 2 ^ (d - 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₁ : 0 < (d : ℝ) - 1 := by linarith
  let θ := (n : ℝ) / ((d : ℝ) - 1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨C, hC, hbound⟩ := hW (θ / 4) (by positivity)
  let A := C * (4 : ℝ) ^ θ
  have hA : 0 < A := by dsimp [A]; positivity
  let K := A ^ ((D : ℝ)⁻¹)
  have hK : 0 < K := Real.rpow_pos_of_pos hA _
  have hKpow : K ^ D = A := by
    dsimp only [K]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le, inv_mul_cancel₀ hDr.ne', Real.rpow_one]
  have hσD : -weylSaving d n * (D : ℝ) = -(θ / 4) := by
    change -((n : ℝ) / (4 * ((d : ℝ) - 1) * (D : ℝ))) * (D : ℝ) = -(_ / (_ - 1) / 4)
    field_simp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (2 : ℝ)] with P hPbound hP α hα
  have hP₁ : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  obtain ⟨a, q, hqp, hcop, hql, hqu, herr⟩ := exists_minorArc_approximation hd hP hα
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hqp
  have hpow : P ^ (-(d : ℝ) + 1 / 2) ≤ P ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
  have hnear : |(q : ℝ) * α - a| ≤ 1 / 2 := by
    have h' : P ^ (-(d : ℝ) + 1 / 2) ≤ P ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
    have hhalf : P ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hP
    exact herr.trans (h'.trans hhalf)
  have hfirst : P ^ (1 - (d : ℝ)) ≤ P ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
  have hthird : (q : ℝ) * P ^ (-(d : ℝ)) ≤ P ^ (-1 / 2 : ℝ) := by
    refine (mul_le_mul_of_nonneg_right hqu (Real.rpow_nonneg hPpos.le _)).trans_eq ?_
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hlast : 1 / (q : ℝ) ≤ P ^ (-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hPpos.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos _) hql.le
  have hbracket :
      P ^ (1 - (d : ℝ)) + |(q : ℝ) * α - a| + (q : ℝ) * P ^ (-(d : ℝ)) + 1 / q ≤
        4 * P ^ (-1 / 2 : ℝ) := by linarith [herr.trans hpow]
  apply le_of_pow_le_pow_left₀ hD.ne' (show 0 ≤ K * P ^ (-weylSaving d n) by positivity)
  calc
    _ ≤ C * P ^ (θ / 4) *
        (P ^ (1 - (d : ℝ)) + |(q : ℝ) * α - a| + (q : ℝ) * P ^ (-(d : ℝ)) + 1 / q) ^ θ :=
      hPbound α a q hqp hcop hnear
    _ ≤ C * P ^ (θ / 4) * (4 * P ^ (-1 / 2 : ℝ)) ^ θ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbracket hθ.le) (by positivity)
    _ = A * P ^ (-(θ / 4)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hPpos.le _),
        ← Real.rpow_mul hPpos.le]
      dsimp only [A]
      rw [show (-1 / 2 : ℝ) * θ = -(θ / 4) - θ / 4 by ring, sub_eq_add_neg,
        Real.rpow_add hPpos]
      have hprod : (P ^ (θ / 4) : ℝ) * P ^ (-(θ / 4)) = 1 := by
        rw [← Real.rpow_add hPpos, add_neg_cancel, Real.rpow_zero]
      calc
        _ = C * (4 : ℝ) ^ θ * P ^ (-(θ / 4)) * (P ^ (θ / 4) * P ^ (-(θ / 4))) := by ring
        _ = _ := by rw [hprod, mul_one]
    _ = _ := by rw [mul_pow, hKpow, ← Real.rpow_natCast, ← Real.rpow_mul hPpos.le, hσD]

end

end Birch
