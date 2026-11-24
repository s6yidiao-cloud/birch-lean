import Birch.DilatedDifference
import Birch.VanDerCorput

/-! # One differencing step for the polynomial phase

The correlation of a lattice summand with its dilated translate is a summand
for the divided-difference polynomial. Its frequency is multiplied by the
integer dilation, and its weight is a product of two translates of the old weight.
-/

open MvPolynomial
open scoped BigOperators ComplexConjugate

namespace Birch

noncomputable section

/-- The value of the divided difference, after multiplication by the integer dilation. -/
theorem eval_dilatedDifference {n : ℕ} (F : IntForm n) (m : ℤ) (u x : Fin n → ℤ) :
    m * evalForm (dilatedDifference m u F) x = evalForm F (x + m • u) - evalForm F x := by
  let ev : IntForm n →ₐ[ℤ] ℤ := MvPolynomial.aeval x
  have h := congrArg (fun p => ev p) (mul_dilatedDifference m u F)
  change ev (C m * dilatedDifference m u F) =
    ev (aeval (fun i => X i + C (m * u i)) F - F) at h
  rw [map_mul, map_sub, MvPolynomial.comp_aeval_apply] at h
  simp only [ev, aeval_C, aeval_X, map_add, Algebra.algebraMap_self, RingHom.id_apply] at h
  exact h

private theorem phase_mul_conj (x y : ℝ) : phase x * conj (phase y) = phase (x-y) := by
  unfold phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  ring

/-- The new weight obtained by translating and multiplying the original weight. -/
def differencedWeight {n : ℕ} (w : (Fin n → ℝ) → ℝ) (P : ℝ) (m : ℤ) (u : Fin n → ℤ)
    (y : Fin n → ℝ) : ℝ := w (fun i => y i + (m : ℝ)*(u i : ℝ)/P) * w y

private def latticeTerm {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (P α : ℝ) (x : Fin n → ℤ) : ℂ :=
  (w (scaledPoint P x) : ℂ) * phase (α * ((evalForm F x : ℤ) : ℝ))

private theorem latticeTerm_correlation {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (P α : ℝ) (m : ℤ) (u x : Fin n → ℤ) :
    latticeTerm F w P α (x + m • u) * conj (latticeTerm F w P α x) =
      latticeTerm (dilatedDifference m u F) (differencedWeight w P m u) P ((m : ℝ)*α) x := by
  unfold latticeTerm differencedWeight
  have hshift : scaledPoint P (x + m • u) = fun i => scaledPoint P x i + (m : ℝ)*(u i : ℝ)/P := by
    ext i
    simp only [scaledPoint, Pi.add_apply, Pi.smul_apply, Int.zsmul_eq_mul, Int.cast_add, Int.cast_mul, add_div]
  have heval := congrArg (Int.cast : ℤ → ℝ) (eval_dilatedDifference F m u x)
  push_cast at heval
  have harg : α * ((evalForm F (x+m • u) : ℤ) : ℝ) - α * ((evalForm F x : ℤ) : ℝ) =
      (m : ℝ)*α*((evalForm (dilatedDifference m u F) x : ℤ) : ℝ) := by
    calc
      _ = α * (((evalForm F (x+m • u) : ℤ) : ℝ) - ((evalForm F x : ℤ) : ℝ)) := by ring
      _ = _ := by rw [← heval]; ring
  have hcast : ∀ (a b c d : ℂ), (a*b)*(c*d) = (a*c)*(b*d) := by intros; ring
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul, hcast, hshift, phase_mul_conj, harg]

private theorem latticeTerm_ne_zero_mem_box {n : ℕ} {P : ℝ} (hP : 1 ≤ P)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1) (α : ℝ)
    (x : Fin n → ℤ) (hx : latticeTerm F w P α x ≠ 0) : x ∈ latticeBox n P := by
  have hp : 0 < P := by linarith
  have hwt : w (scaledPoint P x) ≠ 0 := by
    intro h
    exact hx (by simp [latticeTerm, h])
  refine Fintype.mem_piFinset.mpr fun i => ?_
  have Hx := (hw (scaledPoint P x) hwt i).le
  unfold scaledPoint at Hx
  rw [abs_div, abs_of_pos hp, div_le_iff₀ hp, one_mul] at Hx
  have hi := abs_le.mp Hx
  apply Finset.mem_Icc.mpr
  refine ⟨?_, Int.le_floor.mpr hi.2⟩
  rw [neg_le]
  exact Int.le_floor.mpr (by push_cast; linarith [hi.1])

/-- The normalized differencing inequality before selecting a direction. -/
theorem exponentialSum_differencing {n : ℕ} {P H : ℝ} {m : ℤ}
    (hP : 1 ≤ P) (hH : 0 < H) (hm : 0 < m) (hmH : (m : ℝ)*H ≤ P)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1) (α : ℝ) :
    (‖exponentialSum F w P α‖ / P^n)^2 ≤ ((10 : ℝ)^n / H^n) *
      ∑ u ∈ differencingDirections n H,
        (‖exponentialSum (dilatedDifference m u F) (differencedWeight w P m u) P ((m : ℝ)*α)‖ / P^n) := by
  have h := vanDerCorput_normalized_latticeBox hP hH hm hmH (latticeTerm F w P α)
    (latticeTerm_ne_zero_mem_box hP F w hw α)
  simp only [latticeTerm_correlation] at h
  simpa only [latticeTerm, exponentialSum] using h

/-- Insert the actual polynomial and weight into the selected differencing estimate.
The direction-count input is the singular-dimension estimate from `prop:completion`. -/
theorem exponentialSum_differencing_of_direction_counts {n : ℕ} {P H : ℝ} {m : ℤ}
    (hP : 1 ≤ P) (hH : 0 < H) (hm : 0 < m) (hmH : (m : ℝ)*H ≤ P)
    (F : IntForm n) (w : (Fin n → ℝ) → ℝ)
    (hw : ∀ y, w y ≠ 0 → ∀ i, |y i| < 1) (α : ℝ)
    (s : (Fin n → ℤ) → Fin (n+1)) (s₀ : ℕ) (K : ℝ)
    (hcount : ∀ j : Fin (n+1),
      (((differencingDirections n H).filter (fun u => s u = j)).card : ℝ) ≤
        K * H ^ ((n : ℝ) - ((j.val - s₀ : ℕ) : ℝ))) :
    ∃ u ∈ differencingDirections n H,
      (‖exponentialSum F w P α‖ / P^n)^2 ≤
        ((10 : ℝ)^n * ((n : ℝ)+1) * K) * H ^ (-(((s u).val - s₀ : ℕ) : ℝ)) *
          (‖exponentialSum (dilatedDifference m u F) (differencedWeight w P m u) P ((m : ℝ)*α)‖ / P^n) := by
  have hf := latticeTerm_ne_zero_mem_box hP F w hw α
  obtain ⟨u, hu, huv⟩ := normalized_differencing_of_direction_counts hP hH hm hmH
    (latticeTerm F w P α) hf s s₀ K hcount
  refine ⟨u, hu, ?_⟩
  simp only [latticeTerm_correlation] at huv
  simpa only [latticeTerm, exponentialSum] using huv

end

end Birch
