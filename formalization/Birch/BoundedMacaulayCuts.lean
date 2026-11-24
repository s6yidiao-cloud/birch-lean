import Birch.CompletionGeometry
import Birch.ConeDimensionTest
import Birch.CutPolynomialSystem

/-! # Bounded linear cuts of homogeneous systems -/

open MvPolynomial Matrix

namespace Birch

set_option maxHeartbeats 1600000 in
/-- If a fixed Macaulay degree detects systems supported at the origin,
then linear cuts of the prescribed dimension can be chosen on a uniform
integer grid in sufficiently large characteristic. -/
theorem exists_bounded_macaulay_cuts {K : Type} [Field K] [IsAlgClosed K]
    {n m k e D p : ℕ} [Fact p.Prime] [CharP K p] (i₀ : Fin n)
    (he : 0 < e) (hp : e * Fintype.card (DegreeMonomial n D) < p)
    (f : Fin m → MvPolynomial (Fin n) K) (hf : ∀ i, (f i).IsHomogeneous e)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range f)) ≤ (k : WithBot ℕ∞)) {c : K} (hc : c ≠ 0)
    (hcert : ∀ g : Fin (m+k) → MvPolynomial (Fin n) K, (∀ j, (g j).IsHomogeneous e) →
      (∀ x : Fin n → K, (∀ j, (g j).eval x = 0) → x = 0) →
      ∃ sel : DegreeMonomial n D → Fin (m+k) × DegreeMonomial n (D-e),
        ((systemMacaulayMatrix g e D).submatrix id sel).det ≠ 0) :
    ∃ a : Fin k → Fin n → ℕ, (∀ j i, a j i ≤ e * Fintype.card (DegreeMonomial n D)) ∧
      ∃ sel : DegreeMonomial n D → Fin (m+k) × DegreeMonomial n (D-e),
        ((systemMacaulayMatrix
          (cutPolynomialSystem f c (fun j i => (a j i : K)) e) e D).submatrix id sel).det ≠ 0 := by
  obtain ⟨a,ha⟩ := (homogeneousSystem_dim_le_iff_linear_cuts i₀ f he hf).mp hdim
  obtain ⟨sel,hsel⟩ := hcert _ (cutPolynomialSystem_isHomogeneous f c a hf) fun x hx => by
    obtain ⟨hfx,hax⟩ := (eval_cutPolynomialSystem_eq_zero_iff f hc a he x).mp hx
    exact ha x hfx hax
  let R := MvPolynomial (Fin k × Fin n) K
  let f₀ (i : Fin m) := MvPolynomial.map (C : K →+* R) (f i)
  let a₀ (j : Fin k) (i : Fin n) : R := X (j,i)
  let g₀ := cutPolynomialSystem f₀ (C c) a₀ e
  let T := ((systemMacaulayMatrix g₀ e D).submatrix id sel).det
  have heval (x : Fin k × Fin n → K) : T.eval x =
      ((systemMacaulayMatrix (cutPolynomialSystem f c (fun j i => x (j,i)) e)
        e D).submatrix id sel).det := by
    change eval₂Hom (RingHom.id K) x T = _
    unfold T g₀
    rw [map_cutPolynomialSystem_macaulayMinor]
    have hf₀ (i : Fin m) : MvPolynomial.map (eval₂Hom (RingHom.id K) x) (f₀ i) = f i := by
      unfold f₀
      rw [MvPolynomial.map_map]
      have hcomp : (eval₂Hom (RingHom.id K) x).comp C = RingHom.id K := by ext t; simp
      rw [hcomp, MvPolynomial.map_id]
    have ha₀ (j : Fin k) : (eval₂Hom (RingHom.id K) x) ∘ a₀ j = fun i => x (j,i) := by
      funext i
      change eval₂ (RingHom.id K) x (X (j,i)) = x (j,i)
      exact eval₂_X _ _ _
    simp only [hf₀, eval₂Hom_C, RingHom.id_apply, ha₀]
  have hT : T ≠ 0 := by
    intro hz
    have h := heval (fun ji => a ji.1 ji.2)
    rw [hz, map_zero] at h
    exact hsel h.symm
  have hdeg : T.totalDegree ≤ e * Fintype.card (DegreeMonomial n D) := by
    refine systemMacaulayMinor_totalDegree_le g₀ e D e ?_ sel
    intro i b
    have h := coeff_cutPolynomialSystem_totalDegree_le f₀ (C c) a₀ e
      (B := 0) (A := 1)
      (fun j s => by
        change (coeff s (MvPolynomial.map (C : K →+* R) (f j))).totalDegree ≤ 0
        rw [coeff_map, totalDegree_C])
      (fun j l => by
        change (X (R := K) (j,l)).totalDegree ≤ 1
        rw [totalDegree_X]) i b
    simpa only [totalDegree_C, zero_add, Nat.mul_one, zero_max] using h
  obtain ⟨z,hz,hz₀⟩ := exists_eval_ne_zero_small_grid_of_charP hp T hT hdeg
  rw [heval] at hz₀
  exact ⟨fun j i => z (j,i), fun j i => hz (j,i), sel, hz₀⟩

end Birch
