module

public import Birch.ProjectiveHypersurface
public import Birch.ProjectiveWeilPointCount
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! # Frobenius spectral data for projective hypersurfaces -/

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

private theorem map_div_projectiveTateSpectrum {q N j : ℕ} (hq : 0 < q) (hj : j ≤ 2 * N) :
    (projectiveTateSpectrum q j).map ((q : ℂ) ^ N / ·) = projectiveTateSpectrum q (2 * N - j) := by
  by_cases he : Even j
  · obtain ⟨i, hi⟩ := he
    have he : Even j := ⟨i, hi⟩
    have hcomp : Even (2 * N - j) := ⟨N - i, by omega⟩
    simp only [projectiveTateSpectrum, ite_eq_left he, ite_eq_left hcomp, Multiset.map_singleton,
      show j / 2 = i by omega, show (2 * N - j) / 2 = N - i by omega]
    exact congrArg (fun x : ℂ => ({x} : Multiset ℂ))
      (by simpa only [div_eq_mul_inv] using
        (pow_sub₀ (q : ℂ) (by exact_mod_cast hq.ne') (show i ≤ N by omega)).symm)
  · have hcomp : ¬ Even (2 * N - j) := by
      rintro ⟨i, hi⟩
      exact he ⟨N - i, by omega⟩
    simp [projectiveTateSpectrum, he, hcomp]

/-- Poincaré duality carries the Tate spectrum in degrees below the middle
degree to the Tate spectrum in the corresponding degrees above it. -/
theorem eq_projectiveTateSpectrum_of_lower_and_duality {q N : ℕ}
    (hq : 0 < q) (A : ℕ → Multiset ℂ)
    (hlower : ∀ i < N, A i = projectiveTateSpectrum q i)
    (hdual : ∀ i ≤ 2 * N, A (2 * N - i) = (A i).map ((q : ℂ) ^ N / ·)) :
    ∀ i ≤ 2 * N, i ≠ N → A i = projectiveTateSpectrum q i := by
  intro i hi hne
  by_cases hlt : i < N
  · exact hlower i hlt
  · let j := 2 * N - i
    have hj : j ≤ 2 * N := by dsimp [j]; omega
    have hjlt : j < N := by dsimp [j]; omega
    have hback : 2 * N - j = i := by dsimp [j]; omega
    rw [← hback, hdual j hj, hlower j hjlt, map_div_projectiveTateSpectrum hq hj]

/-- The scheme point count and Weil weights together with the outer Tate
terms and the Fermat-sized bound for the middle Betti number. -/
def PrimeSmoothHypersurfaceMiddleSpectralData (d : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero p], d < p →
    ∀ (m : ℕ), 3 ≤ m →
      ∀ (G : MvPolynomial (Fin m) (ZMod p)) (hG : G.IsHomogeneous d), G ≠ 0 →
        (∀ j : Fin m, ∃ N : ℕ, X j ^ N ∈
          Ideal.span (insert G (Set.range fun i : Fin m => pderiv i G))) →
        ∃ A : ℕ → Multiset ℂ,
          (Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p)))) ⟶
            Over.mk (projectiveHypersurfaceToField hG)) : ℂ) =
            ∑ i ∈ Finset.Iic (2*(m-2)), (-1 : ℂ)^i * (A i).sum ∧
          (∀ i ≤ 2*(m-2), i ≠ m-2 → A i = projectiveTateSpectrum p i) ∧
          (A (m-2)).card ≤ (d-1) ^ m + 1 ∧
          (∀ α ∈ A (m-2), ‖α‖ = Real.sqrt ((p : ℝ)^(m-2)))

end Birch
