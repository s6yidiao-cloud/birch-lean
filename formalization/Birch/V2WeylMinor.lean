import Birch.Weyl
import Birch.V2MajorArcShells

/-!
# The initial Weyl saving on the v2 minor arcs

The major arcs in `v2.tex` have fixed width. Using Dirichlet's theorem at
scale `P ^ (d - Δ)` forces the minor-arc approximant's denominator to exceed
`P ^ Δ`. This gives the initial saving from the repository's Weyl estimate.
-/

namespace Birch

open Filter

noncomputable section

/-- A reduced Dirichlet approximant to a frequency on the v2 minor arcs. -/
theorem exists_v2MinorArc_approximation {d : ℕ} (hd : 2 ≤ d) {Δ P α : ℝ}
    (hΔ : Δ < 1 / 4) (hP : 2 ≤ P) (hα : α ∈ (v2MajorArcs d Δ P)ᶜ) :
    ∃ (a : ℤ) (q : ℕ), 0 < q ∧ a.natAbs.Coprime q ∧
      P ^ Δ < (q : ℝ) ∧ (q : ℝ) ≤ P ^ ((d : ℝ) - Δ) ∧
      |(q : ℝ) * α - a| ≤ P ^ (-(d : ℝ) + Δ) := by
  let Q := P ^ ((d : ℝ) - Δ)
  let N := ⌊Q⌋₊
  have hP₁ : 1 ≤ P := by linarith
  have hP₀ : 0 < P := by linarith
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hQ : 2 ≤ Q :=
    hP.trans ((Real.rpow_one P).symm.trans_le
      (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)))
  have hN : 0 < N := Nat.floor_pos.mpr (by linarith)
  obtain ⟨b, hb, hbN⟩ := Real.exists_rat_abs_sub_le_and_den_le α hN
  have hq : (0 : ℝ) < b.den := Nat.cast_pos.mpr b.pos
  have hqQ : (b.den : ℝ) ≤ Q :=
    (Nat.cast_le.mpr hbN).trans (Nat.floor_le (by linarith))
  have hcast : (b : ℝ) = (b.num : ℝ) / b.den := Rat.cast_def b
  have hmul : |(b.den : ℝ) * α - b.num| = |α - (b : ℝ)| * b.den := by
    calc
      _ = |(α - (b : ℝ)) * b.den| := by congr 1; rw [hcast]; field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hq]
  have herror : |(b.den : ℝ) * α - b.num| ≤ P ^ (-(d : ℝ) + Δ) := by
    calc
      _ = |α - (b : ℝ)| * b.den := hmul
      _ ≤ (1 / (((N : ℝ) + 1) * (b.den : ℝ))) * b.den :=
        mul_le_mul_of_nonneg_right hb hq.le
      _ = 1 / ((N : ℝ) + 1) := by field_simp
      _ ≤ 1 / Q := one_div_le_one_div_of_le (by linarith) (Nat.lt_floor_add_one Q).le
      _ = _ := by
        dsimp only [Q]
        rw [show -(d : ℝ) + Δ = -((d : ℝ) - Δ) by ring, Real.rpow_neg hP₀.le, one_div]
  refine ⟨b.num, b.den, b.pos, b.reduced, ?_, hqQ, herror⟩
  by_contra! hsmall
  apply hα
  refine ⟨b.den, b.num, b.pos, hsmall, b.reduced, ?_⟩
  rw [← hcast]
  have hq₁ : (1 : ℝ) ≤ b.den := by exact_mod_cast b.pos
  exact (le_mul_of_one_le_right (abs_nonneg _) hq₁).trans (hmul.symm ▸ herror)

/-- A uniform pointwise saving on the v2 minor arcs, conditional on the
fixed-height Weyl estimate. The saving requires only the degree and arc
parameter. The positive exponent parameter `ν` can be the singular
codimension. -/
theorem initialMinor_of_weyl_v2 {d : ℕ} (hd : 2 ≤ d) {Δ : ℝ}
    (hΔ₀ : 0 < Δ) (hΔ : Δ < 1 / 4) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ {ν : ℕ}, 0 < ν → ∀ {f : ℝ → ℝ → ℝ}, WeylEstimate d ν f →
      ∃ K > 0, ∀ᶠ P in atTop, ∀ α ∈ (v2MajorArcs d Δ P)ᶜ,
        f P α ≤ K * P ^ (-σ) := by
  let D : ℕ := 2 ^ (d - 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₁ : 0 < (d : ℝ) - 1 := by linarith
  let δ := Δ / (2 * ((d : ℝ) - 1))
  have hδ : 0 < δ := div_pos hΔ₀ (by positivity)
  let σ := δ / D
  refine ⟨σ, div_pos hδ hDr, ?_⟩
  intro ν hν f hW
  let θ := (ν : ℝ) / ((d : ℝ) - 1)
  have hθ : 0 < θ := div_pos (Nat.cast_pos.mpr hν) hd₁
  have hδθ : 2 * δ ≤ Δ * θ := by
    have hν₁ : (1 : ℝ) ≤ ν := by exact_mod_cast hν
    have h := mul_le_mul_of_nonneg_left hν₁ hΔ₀.le
    calc
      _ = Δ / ((d : ℝ) - 1) := by dsimp [δ]; field_simp
      _ ≤ (Δ * (ν : ℝ)) / ((d : ℝ) - 1) := by
        apply div_le_div_of_nonneg_right _ hd₁.le
        simpa only [mul_one] using h
      _ = _ := by dsimp [θ]; ring
  obtain ⟨C, hC, hbound⟩ := hW δ hδ
  let A := C * (4 : ℝ) ^ θ
  have hA : 0 < A := by dsimp [A]; positivity
  let K := A ^ ((D : ℝ)⁻¹)
  have hK : 0 < K := Real.rpow_pos_of_pos hA _
  have hKpow : K ^ D = A := by
    dsimp only [K]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le, inv_mul_cancel₀ hDr.ne', Real.rpow_one]
  have hσD : -σ * (D : ℝ) = -δ := by dsimp [σ]; field_simp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (2 : ℝ)] with P hPbound hP α hα
  have hP₁ : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  obtain ⟨a, q, hqp, hcop, hql, hqu, herr⟩ := exists_v2MinorArc_approximation hd hΔ hP hα
  have hnear : |(q : ℝ) * α - a| ≤ 1 / 2 := by
    have h' : P ^ (-(d : ℝ) + Δ) ≤ P ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
    have hhalf : P ^ (-1 : ℝ) ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hP
    exact herr.trans (h'.trans hhalf)
  have hfirst : P ^ (1 - (d : ℝ)) ≤ P ^ (-Δ) :=
    Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)
  have herror : |(q : ℝ) * α - a| ≤ P ^ (-Δ) :=
    herr.trans (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith))
  have hthird : (q : ℝ) * P ^ (-(d : ℝ)) ≤ P ^ (-Δ) := by
    refine (mul_le_mul_of_nonneg_right hqu (Real.rpow_nonneg hPpos.le _)).trans_eq ?_
    rw [← Real.rpow_add hPpos]
    congr 1
    ring
  have hlast : 1 / (q : ℝ) ≤ P ^ (-Δ) := by
    rw [Real.rpow_neg hPpos.le, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hPpos _) hql.le
  have hbracket :
      P ^ (1 - (d : ℝ)) + |(q : ℝ) * α - a| + (q : ℝ) * P ^ (-(d : ℝ)) + 1 / q ≤
        4 * P ^ (-Δ) := by linarith
  apply le_of_pow_le_pow_left₀ hD.ne' (show 0 ≤ K * P ^ (-σ) by positivity)
  calc
    _ ≤ C * P ^ δ *
        (P ^ (1 - (d : ℝ)) + |(q : ℝ) * α - a| + (q : ℝ) * P ^ (-(d : ℝ)) + 1 / q) ^ θ :=
      hPbound α a q hqp hcop hnear
    _ ≤ C * P ^ δ * (4 * P ^ (-Δ)) ^ θ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbracket hθ.le) (by positivity)
    _ = A * P ^ (δ - Δ * θ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hPpos.le _),
        ← Real.rpow_mul hPpos.le, sub_eq_add_neg, Real.rpow_add hPpos, neg_mul]
      dsimp only [A]
      ring
    _ ≤ A * P ^ (-δ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)) hA.le
    _ = _ := by rw [mul_pow, hKpow, ← Real.rpow_natCast, ← Real.rpow_mul hPpos.le, hσD]

end

end Birch
