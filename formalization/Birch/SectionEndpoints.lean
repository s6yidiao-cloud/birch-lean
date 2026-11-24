import Birch.GradientCone
import Birch.SectionLine
import Birch.TerminalAssembly

/-! # Endpoint cases of the smooth-section step -/

open Matrix MvPolynomial

namespace Birch

private theorem linearSection_identity {n : ℕ} (G : IntForm n) :
    linearSection (1 : Matrix (Fin n) (Fin n) ℤ) G = G := by
  have he : linearSection (1 : Matrix (Fin n) (Fin n) ℤ) = AlgHom.id ℤ (IntForm n) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [linearSection_X, AlgHom.id_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Matrix.one_apply_ne hji.symm]
    · simp
  rw [he, AlgHom.id_apply]

/-- A zero-dimensional gradient cone needs no restriction. -/
theorem boundedSmoothSection_full {n r p B : ℕ} [Fact p.Prime] (hB : 1 ≤ B)
    {G : IntForm n} (hG : G.IsHomogeneous r) (hdim : PrimeGradientDimension p Fact.out G 0) :
    BoundedSmoothSection p n B G := by
  refine ⟨1, ?_, ?_⟩
  · intro i j
    have hB' : (1 : ℤ) ≤ B := by exact_mod_cast hB
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hB']
  · rw [linearSection_identity]
    exact critical_eq_zero_of_primeGradientDimension_zero Fact.out hG hdim

/-- The three endpoint cases use only matrices whose entries are at most `r`
in absolute value. The remaining sections have `2 ≤ n-s < n`. -/
theorem boundedSmoothSection_of_endpoint {n p r s : ℕ} [Fact p.Prime] {G : IntForm n}
    (hG : G.IsHomogeneous r) (hr : 2 ≤ r) (hp : r < p)
    (hdim : PrimeGradientDimension p Fact.out G s) (h : n-s ≤ 1 ∨ s = 0) :
    BoundedSmoothSection p (n-s) r G := by
  rcases h with h | rfl
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h₀ | h₁
    · rw [h₀]
      exact boundedSmoothSection_zero G
    · rw [h₁]
      exact exists_small_smooth_line hG hr hp hdim (by omega)
  · rw [Nat.sub_zero]
    exact boundedSmoothSection_full (by omega) hG hdim

end Birch
