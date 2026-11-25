import Birch.V2MajorArcShells

/-! # Cover singular-series convergence from the minor-arc integral -/

open Filter MeasureTheory Set
open scoped Polynomial Topology

namespace Birch

noncomputable section

/-- Absolute value of one term in the cover conductor sum. -/
def coverCompleteSumNormAt {n : ℕ} (F : IntForm n) (g : ℤ[X]) (q a : ℕ) : ℝ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ‖completeSum F q (a : ZMod q) * coverCompleteSum g q (a : ZMod q)‖

private def coverConductorMassAt {n : ℕ} (F : IntForm n) (g : ℤ[X]) (q : ℕ) : ℝ :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    coverConductorMass F g q

private theorem coverConductorMassAt_eq {n q : ℕ} [NeZero q] (F : IntForm n) (g : ℤ[X]) :
    coverConductorMassAt F g q = coverConductorMass F g q := by
  rw [coverConductorMassAt, dite_eq_right (NeZero.ne q)]

private theorem coverConductorMassAt_nonneg {n : ℕ} (F : IntForm n) (g : ℤ[X]) (q : ℕ) :
    0 ≤ coverConductorMassAt F g q := by
  unfold coverConductorMassAt
  split_ifs with hq
  · exact le_rfl
  · let : NeZero q := ⟨hq⟩
    exact coverConductorMass_nonneg F g q

/-- The absolute values over a rational shell sum to the conductor masses
of exactly the denominators in that shell. -/
private theorem coverCompleteSumNormAt_shell_eq {n Q : ℕ} (hQ : 1 ≤ Q)
    (F : IntForm n) (g : ℤ[X]) :
    (∑ j ∈ rationalShellCenters (Q : ℝ), coverCompleteSumNormAt F g j.1 j.2) =
      ∑ q ∈ Finset.Ioc Q (2*Q), coverConductorMassAt F g q := by
  rw [sum_rationalShellCenters_by_denominator Q hQ]
  apply Finset.sum_congr rfl
  intro q hq
  have hq₂ := Nat.succ_le_of_lt (hQ.trans_lt (Finset.mem_Ioc.mp hq).1)
  have hq₀ : q ≠ 0 := by omega
  let : NeZero q := ⟨hq₀⟩
  simp only [coverConductorMassAt_eq, coverConductorMass, coverCompleteSumNormAt, dite_eq_right hq₀]
  exact (sum_zmod_units_eq_reducedNumerators q hq₂
    (fun a => ‖completeSum F q a * coverCompleteSum g q a‖)).symm

/-- A power saving for the cover complete sums over each denominator shell
gives absolute convergence and a tail estimate for the conductor masses. -/
theorem coverConductorMass_tail_of_shell_decay {n : ℕ} (F : IntForm n) (g : ℤ[X])
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C)
    (h : ∀ᶠ X : ℝ in atTop,
      (∑ j ∈ rationalShellCenters X, coverCompleteSumNormAt F g j.1 j.2) ≤ C * X^(-γ)) :
    Summable (fun j : ℕ => coverConductorMass F g (j+1)) ∧
      ∃ D > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, coverConductorMass F g (j+Q+1)) ≤ D * (Q : ℝ)^(-γ) := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp h
  let Q₀ := max 1 ⌈B⌉₊
  have hd (Q : ℕ) (hQ : Q₀ ≤ Q) :
      (∑ q ∈ Finset.Ioc Q (2*Q), coverConductorMassAt F g q) ≤ C * (Q : ℝ)^(-γ) := by
    have hBQ : B ≤ (Q : ℝ) := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right 1 ⌈B⌉₊).trans hQ)
    rw [← coverCompleteSumNormAt_shell_eq ((le_max_left _ _).trans hQ) F g]
    exact hB _ hBQ
  obtain ⟨hs,htail⟩ := summable_and_tsum_tail_le_of_dyadic
    (coverConductorMassAt_nonneg F g) hC.le hγ hd
  have hs' : Summable (fun j : ℕ => coverConductorMass F g (j+1)) := by
    simpa only [coverConductorMassAt_eq] using (summable_nat_add_iff 1).2 hs
  have hpos : 0 < 1 - (2 : ℝ)^(-γ) := by
    apply sub_pos.mpr
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_zero.mpr hγ)
  refine ⟨hs', C * (1 - (2 : ℝ)^(-γ))⁻¹, by positivity, max 1 Q₀, fun Q hQ => ?_⟩
  have hh := htail Q hQ
  rw [mul_right_comm] at hh
  simpa only [coverConductorMassAt_eq] using hh

/-- For the fixed-width major arcs of v2, a minor-arc estimate for the
normalized product and its pointwise lower bound on the rational intervals
give an absolute tail for the cover singular series. -/
theorem coverConductorMass_tail_of_v2MinorIntegral {n d : ℕ} (hd : 2 ≤ d)
    (F : IntForm n) (g : ℤ[X]) {Δ r c D E η L : ℝ}
    (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/4) (hr : 0 < r) (hr₁ : r ≤ 1)
    (hc : 0 < c) (hD : 0 < D) (hE : 0 ≤ E) (hη : 0 < η) (hL : 4*Δ + η ≤ L)
    (f : ℝ → ℝ → ℝ) (hf : ∀ P, Continuous (f P)) (hf₀ : ∀ P α, 0 ≤ f P α)
    (hminor : ∀ᶠ P : ℝ in atTop,
      (∫ α in (v2MajorArcs d Δ P)ᶜ, f P α ∂circleMeasure) ≤ D * P^(-(d : ℝ)-η))
    (hpoint : ∀ᶠ P : ℝ in atTop, ∀ j ∈ rationalShellCenters (P^(2*Δ)),
      ∀ α ∈ rationalShellInterval (r*P^(-(d : ℝ))) j,
        c * coverCompleteSumNormAt F g j.1 j.2 ≤ f P α + E * P^(-L)) :
    Summable (fun j : ℕ => coverConductorMass F g (j+1)) ∧
      ∃ C > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, coverConductorMass F g (j+Q+1)) ≤ C * (Q : ℝ)^(-(η/(2*Δ))) := by
  have hgeometry : ∀ᶠ P : ℝ in atTop,
      let X := P^(2*Δ)
      let R := r*P^(-(d : ℝ))
      (2*R) * (2*X)^2 < 1 ∧ R * (2*X) < 1 ∧
        ∀ j ∈ rationalShellCenters X, rationalShellInterval R j ⊆ (v2MajorArcs d Δ P)ᶜ := by
    filter_upwards [eventually_ge_atTop (16 : ℝ)] with P hP
    exact v2MajorArcShell_geometry hd hP hr.le hr₁ hΔ.le hΔ₁
  obtain ⟨C,hC,h⟩ := rationalShell_decay_of_minorIntegral (d := d) (a := 2*Δ)
    (by positivity) hr hc hD hE (by linarith)
    (fun P => (v2MajorArcs d Δ P)ᶜ) f (fun j => coverCompleteSumNormAt F g j.1 j.2)
    hf hf₀ hgeometry hminor hpoint
  rw [show -η/(2*Δ) = -(η/(2*Δ)) by ring] at h
  exact coverConductorMass_tail_of_shell_decay F g (by positivity) hC h

end

end Birch
