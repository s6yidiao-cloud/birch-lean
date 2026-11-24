import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

open LinearMap (BilinForm)
open Set Module
open scoped BigOperators

namespace Birch

noncomputable section

local notation "W" n => ((Fin n → ℝ) × (Fin n → ℝ))

/-- The standard alternating form on two coordinate blocks. -/
def weylSymplectic (n : ℕ) : BilinForm ℝ (W n) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, (x.1 i * y.2 i - x.2 i * y.1 i))
    (by
      intro x y z
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c x y
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (c * x.1 i) * y.2 i - (c * x.2 i) * y.1 i = _
      ring)
    (by
      intro x y z
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c x y
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change x.1 i * (c * y.2 i) - x.2 i * (c * y.1 i) = _
      ring)

theorem weylSymplectic_apply {n : ℕ} (x y : W n) :
    weylSymplectic n x y = ∑ j, (x.1 j * y.2 j - x.2 j * y.1 j) := rfl

private theorem weylSymplectic_antisymm {n : ℕ} (x y : W n) :
    weylSymplectic n x y = -(weylSymplectic n y x) := by
  rw [weylSymplectic_apply, weylSymplectic_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem weylSymplectic_separates {n : ℕ} (x : W n)
    (hx : ∀ y, weylSymplectic n x y = 0) : x = 0 := by
  have hsum (v : Fin n → ℝ) (i : Fin n) : (∑ j, v j * (Pi.single i 1 : Fin n → ℝ) j) = v i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  apply Prod.ext
  · funext i
    change x.1 i = 0
    have h := hx (0, Pi.single i 1)
    simpa only [weylSymplectic_apply, Pi.zero_apply, mul_zero, sub_zero, hsum] using h
  · funext i
    change x.2 i = 0
    have h := hx (Pi.single i 1, 0)
    simpa only [weylSymplectic_apply, Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib,
      hsum, neg_eq_zero] using h

theorem weylSymplectic_nondegenerate (n : ℕ) : (weylSymplectic n).Nondegenerate := by
  refine ⟨weylSymplectic_separates, fun x hx => weylSymplectic_separates x ?_⟩
  intro y
  rw [weylSymplectic_antisymm, hx y, neg_zero]

/-- An isotropic span for the standard pairing has dimension at most one coordinate block. -/
theorem finrank_span_le_of_weylSymplectic_zero {n : ℕ} {S : Set (W n)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, weylSymplectic n x y = 0) :
    finrank ℝ (Submodule.span ℝ S) ≤ n := by
  let B := weylSymplectic n
  let K := Submodule.span ℝ S
  have hrow {x : W n} (hx : x ∈ S) : K ≤ LinearMap.ker (B x) :=
    Submodule.span_le.mpr fun y hy => LinearMap.mem_ker.mpr (hS x hx y hy)
  have hiso : K ≤ B.orthogonal K := by
    intro y hy
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    have hcol : K ≤ LinearMap.ker (B.flip y) := Submodule.span_le.mpr fun x hx =>
      LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp (hrow hx hy))
    exact fun x hx => LinearMap.mem_ker.mp (hcol hx)
  have hd := Submodule.finrank_mono hiso
  rw [LinearMap.BilinForm.finrank_orthogonal (weylSymplectic_nondegenerate n)] at hd
  have hW : finrank ℝ (W n) = n + n := by
    simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  rw [hW] at hd
  change finrank ℝ K ≤ n
  omega

end
end Birch
