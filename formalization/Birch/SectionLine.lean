import Birch.GradientCone
import Birch.CompletionGeometry
import Birch.SectionPolynomial
import Birch.SectionFrame

/-! # A bounded smooth section of dimension one -/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

private theorem map_ne_zero_of_gradientDimension_lt {n p s : ℕ} [Fact p.Prime]
    {G : IntForm n} (hdim : PrimeGradientDimension p Fact.out G s) (hs : s < n) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) G ≠ 0 := by
  intro hG
  let K := AlgebraicClosure (ZMod p)
  let R := MvPolynomial (Fin n) K
  let J : Ideal R := Ideal.span
    (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv j G))
  have hcoeff : (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) = Int.castRingHom K := by
    ext a
    simp
  have hGK : MvPolynomial.map (Int.castRingHom K) G = 0 := by
    rw [← hcoeff, ← MvPolynomial.map_map, hG, map_zero]
  have hJ : J = ⊥ := by
    apply le_antisymm _ bot_le
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change MvPolynomial.map (Int.castRingHom K) (pderiv j G) ∈ (⊥ : Ideal R)
    rw [← pderiv_map, hGK, map_zero]
    exact Ideal.zero_mem _
  change ringKrullDim (R ⧸ J) = (s : ℕ∞) at hdim
  rw [hJ, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)] at hdim
  have hn := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (R := K) (Fin n)
  rw [ringKrullDim_eq_zero_of_field K, zero_add, Nat.card_fin] at hn
  change ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R at hn
  rw [hdim, WithBot.coe_le_coe] at hn
  have hns : n ≤ s := by exact_mod_cast hn
  exact (not_le_of_gt hs) hns

/-- When the gradient dimension is less than the ambient dimension,
a bounded integer line has a geometrically nonsingular restriction. -/
theorem exists_small_smooth_line {n p r s : ℕ} [Fact p.Prime]
    {G : IntForm n} (hG : G.IsHomogeneous r) (hr : 2 ≤ r) (hp : r < p)
    (hdim : PrimeGradientDimension p Fact.out G s) (hs : s < n) :
    ∃ U : Matrix (Fin n) (Fin 1) ℤ, (∀ i j, |U i j| ≤ (r : ℤ)) ∧
      ∀ x : Fin 1 → AlgebraicClosure (ZMod p),
        (∀ j, evalForm (pderiv j (linearSection U G)) x = 0) → x = 0 := by
  let K := AlgebraicClosure (ZMod p)
  let A := MvPolynomial.map (Int.castRingHom (ZMod p)) G
  have hdeg : A.totalDegree ≤ r := by
    calc
      A.totalDegree ≤ G.totalDegree :=
        Finset.sup_mono (support_map_subset _ _)
      _ ≤ r := hG.totalDegree_le
  obtain ⟨z, hz, hz₀⟩ := exists_eval_ne_zero_small_grid hp A
    (map_ne_zero_of_gradientDimension_lt hdim hs) hdeg
  let U : Matrix (Fin n) (Fin 1) ℤ := fun i _ => (z i : ℤ)
  refine ⟨U, fun i _ => ?_, ?_⟩
  · change |(z i : ℤ)| ≤ (r : ℤ)
    rw [Int.abs_natCast]
    exact_mod_cast hz i
  let H := linearSection U G
  have hH : H.IsHomogeneous r := isHomogeneous_linearSection U hG
  have hval : evalForm H (1 : Fin 1 → K) ≠ 0 := by
    have hz₁ : evalForm G (fun i => (z i : ZMod p)) ≠ 0 := by
      simpa only [A, evalForm, MvPolynomial.eval_map] using hz₀
    have hz₂ := (algebraMap (ZMod p) K).injective.ne hz₁
    rw [evalForm_map, map_zero] at hz₂
    rw [show H = linearSection U G from rfl, evalForm_linearSection]
    simpa [U] using hz₂
  have hr_K : (r : K) ≠ 0 := by
    have hr_p : (r : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact fun hdvd => (not_le_of_gt hp) (Nat.le_of_dvd (by omega) hdvd)
    have he := (algebraMap (ZMod p) K).injective.ne hr_p
    simpa using he
  have hderiv : evalForm (pderiv (0 : Fin 1) H) (1 : Fin 1 → K) ≠ 0 := by
    intro hzero
    let e := eval₂Hom (Int.castRingHom K) (1 : Fin 1 → K)
    have he := congrArg e hH.sum_X_mul_pderiv
    change e (∑ j : Fin 1, X j * pderiv j H) = e (r • H) at he
    rw [map_sum, Fin.sum_univ_one, map_mul, map_nsmul,
      show e (X (0 : Fin 1)) = 1 by simp [e]] at he
    change (1 : K) * evalForm (pderiv (0 : Fin 1) H) (1 : Fin 1 → K) =
      r • evalForm H (1 : Fin 1 → K) at he
    rw [hzero, mul_zero, nsmul_eq_mul] at he
    exact (mul_ne_zero hr_K hval) he.symm
  intro x hpde
  have hx (j : Fin 1) : x j = x 0 := congrArg x (Subsingleton.elim _ _)
  by_contra hne
  have hx₀ : x 0 ≠ 0 := by
    intro hzero
    apply hne
    funext j
    exact (hx j).trans hzero
  have he := evalForm_scale (R := K) (F := pderiv (0 : Fin 1) H) hH.pderiv (x 0) (1 : Fin 1 → K)
  have hfun : (fun i : Fin 1 => x 0 * (1 : Fin 1 → K) i) = x := by
    funext j
    simp only [Pi.one_apply, mul_one, hx j]
  rw [hfun, hpde 0] at he
  exact (mul_ne_zero (pow_ne_zero _ hx₀) hderiv) he.symm

/-- A terminal form with exactly one free variable admits a smooth section
within the fixed bounded family of integral frames. -/
theorem exists_bounded_smooth_line_frame {p r s : ℕ} [Fact p.Prime]
    {G : IntForm (1+s)} (hG : G.IsHomogeneous r) (hr : 2 ≤ r) (hp : r < p)
    (hdim : PrimeGradientDimension p Fact.out G s) :
    ∃ A ∈ boundedSectionFrames (1+s) r, (A.det : ZMod p) ≠ 0 ∧
      ∀ x : Fin 1 → AlgebraicClosure (ZMod p),
        (∀ j, evalForm (pderiv j (linearSection (sectionFreeColumns A) G)) x = 0) → x = 0 := by
  obtain ⟨U,hU,hs⟩ := exists_small_smooth_line hG hr hp hdim (by omega : s < 1+s)
  obtain ⟨A,hA,hcols,hdet⟩ := exists_bounded_integral_section_frame (by omega : 1 ≤ r) U hU
    (linearSection_cols_linearIndependent U G hr hG hs)
  exact ⟨A,hA,hdet,by rwa [sectionFreeColumns_eq_of_cols A U hcols]⟩

end
end Birch
