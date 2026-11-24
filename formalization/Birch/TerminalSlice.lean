import Birch.LatticePoisson
import Birch.TerminalFourierTail
import Birch.CompletionGeometry

/-! # Completion of a single weighted slice -/

open scoped BigOperators

namespace Birch

noncomputable section

/-- The completed slice gains one power of `Q⁻¹` per free coordinate, provided
its Euclidean Fourier decay and normalized complete-sum estimate are available. -/
theorem terminal_slice_bound_of_modulus_range {l N : ℕ} {f : (Fin l → ℝ) → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) {P Q L : ℝ} (hL : 0 ≤ L)
    (hP : 0 < P) (hQ : 0 < Q) (hQmax : Q ≤ Real.sqrt P)
    (p : ℕ) [NeZero p] (hpL : (P/Q)^2 ≤ (p : ℝ)) (hpU : (p : ℝ) ≤ L*(P/Q)^2)
    (weight : (Fin l → ZMod p) → ℂ) {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hN : 2*l ≤ N)
    (hChar : ∀ z : Fin l → ℤ, ‖((p : ℂ)^l)⁻¹ * ∑ t : Fin l → ZMod p,
        weight t * phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(p : ℝ))‖ ≤ D * (p : ℝ)^(-(l : ℝ)/2))
    (hDecay : ∀ ν : Fin l → ℝ, ‖latticeFourierIntegral f ν‖ ≤ E * (1 + ‖ν‖)^(-(N : ℝ))) :
    ‖∑' x : Fin l → ℤ, weight (fun i => (x i : ZMod p)) * f (P⁻¹ • latticeVector x)‖ / P^l ≤
      (D * E * (4 * Real.sqrt L)^l) * Q ^ (-(l : ℝ)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  let θ := P/(p : ℝ)
  have hθ : 0 < θ := div_pos hP hp
  let A (z : Fin l → ℤ) := ‖latticeFourierIntegral f (θ • latticeVector z)‖
  let T (z : Fin l → ℤ) := (1 + θ * ‖latticeVector z‖)^(-(N : ℝ))
  obtain ⟨hTS, hTbound⟩ := terminal_fourier_weight_sum hθ hN
  have hpoint (z : Fin l → ℤ) : A z ≤ E * T z := by
    have h := hDecay (θ • latticeVector z)
    rw [norm_smul, Real.norm_of_nonneg hθ.le] at h
    exact h
  have hAS : Summable A := (hTS.mul_left E).of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  have hT : (∑' z, A z) ≤ E * (1+2/θ)^l := by
    refine (hAS.tsum_le_tsum hpoint (hTS.mul_left E)).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hTbound hE
  have hcmp : (1+2/θ)^l ≤ (2 : ℝ)^l * (1+(p : ℝ)/P)^l := by
    have ht : 2/θ = 2*((p : ℝ)/P) := by dsimp [θ]; field_simp
    rw [ht, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc
    _ ≤ (D * (p : ℝ)^(-(l : ℝ)/2)) * (∑' z, A z) :=
      normalized_lattice_residue_bound hc hs hP p weight hChar hAS
    _ ≤ (D * (p : ℝ)^(-(l : ℝ)/2)) * (E * (1+2/θ)^l) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (D * (p : ℝ)^(-(l : ℝ)/2)) * (E * ((2 : ℝ)^l * (1+(p : ℝ)/P)^l)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcmp hE) (by positivity)
    _ = (D * E * (2 : ℝ)^l) * ((1+(p : ℝ)/P)^l * (p : ℝ)^(-(l : ℝ)/2)) := by ring
    _ ≤ (D * E * (2 : ℝ)^l) * ((2 * Real.sqrt L)^l * Q^(-(l : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (terminalScale_bound_of_modulus_range l hL hP hQ hQmax hpL hpU) (by positivity)
    _ = _ := by
      rw [show (4 * Real.sqrt L)^l = (2 : ℝ)^l * (2 * Real.sqrt L)^l by rw [← mul_pow]; congr 1; ring]
      ring

theorem terminal_slice_bound {l N : ℕ} {f : (Fin l → ℝ) → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) {P Q : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hQmax : Q ≤ Real.sqrt P)
    (p : ℕ) [NeZero p] (hpL : (P/Q)^2 ≤ (p : ℝ)) (hpU : (p : ℝ) ≤ 2*(P/Q)^2)
    (weight : (Fin l → ZMod p) → ℂ) {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E) (hN : 2*l ≤ N)
    (hChar : ∀ z : Fin l → ℤ, ‖((p : ℂ)^l)⁻¹ * ∑ t : Fin l → ZMod p,
        weight t * phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(p : ℝ))‖ ≤ D * (p : ℝ)^(-(l : ℝ)/2))
    (hDecay : ∀ ν : Fin l → ℝ, ‖latticeFourierIntegral f ν‖ ≤ E * (1 + ‖ν‖)^(-(N : ℝ))) :
    ‖∑' x : Fin l → ℤ, weight (fun i => (x i : ZMod p)) * f (P⁻¹ • latticeVector x)‖ / P^l ≤
      (D * E * (4 * Real.sqrt 2)^l) * Q ^ (-(l : ℝ)) :=
  terminal_slice_bound_of_modulus_range hc hs (by norm_num) hP hQ hQmax p hpL hpU weight
    hD hE hN hChar hDecay

end

end Birch
