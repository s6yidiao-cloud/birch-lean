module

public import Birch.CircleMethod
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.Nullstellensatz

@[expose] public section

/-!
# Transverse weights for geometrically smooth hypersurfaces
-/

open Set Filter MvPolynomial
open scoped ContDiff Topology BigOperators

namespace Birch

noncomputable section

theorem evalForm_hom {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (F : IntForm n) (x : Fin n → R) :
    f (evalForm F x) = evalForm F (fun j => f (x j)) := by
  unfold evalForm
  rw [MvPolynomial.hom_eval₂]
  congr 1
  ext
  simp

theorem evalForm_scale {n d : ℕ} {R : Type*} [CommRing R]
    {F : IntForm n} (hF : F.IsHomogeneous d) (c : R) (x : Fin n → R) :
    evalForm F (fun i ↦ c * x i) = c ^ d * evalForm F x := by
  classical
  simp only [evalForm, MvPolynomial.eval₂_eq', mul_pow, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, Finsupp.degree_apply, ← hF.degree_eq_sum_deg_support hs]
  ring

theorem eval_rational_coefficients {n : ℕ} {K : Type*}
    [Field K] [Algebra ℚ K] (F : IntForm n) (x : Fin n → K) :
    aeval x (MvPolynomial.map (Int.castRingHom ℚ) F) = evalForm F x := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1
  ext a
  simp

/-- A geometrically smooth form has a nonzero partial at every nonzero zero
over every field extending the rationals. -/
theorem ProjectivelySmooth.nonsingular_over {n : ℕ} {F : IntForm n}
    (hs : ProjectivelySmooth F) {K : Type*} [Field K] [Algebra ℚ K]
    (x : Fin n → K) (hx : x ≠ 0) (hFx : evalForm F x = 0) :
    ∃ i, evalForm (pderiv i F) x ≠ 0 := by
  classical
  by_contra! hz
  let f := MvPolynomial.map (Int.castRingHom ℚ) F
  let g (i : Fin n) := MvPolynomial.map (Int.castRingHom ℚ) (pderiv i F)
  let J := Ideal.span ({f} ∪ range g)
  have hgeom : zeroLocus (AlgebraicClosure ℚ) J ⊆ ({0} : Set (Fin n → AlgebraicClosure ℚ)) := by
    intro y hy
    by_contra! hyne
    have hf : evalForm F y = 0 := by
      rw [← eval_rational_coefficients]
      exact hy f (Ideal.subset_span (Or.inl rfl))
    obtain ⟨i, hi⟩ := hs y hyne hf
    apply hi
    rw [← eval_rational_coefficients]
    exact hy (g i) (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
  have hxJ : x ∈ zeroLocus K J := by
    rw [show J = Ideal.span ({f} ∪ range g) from rfl, zeroLocus_span]
    rintro p (hp | ⟨i, rfl⟩)
    · obtain rfl : p = f := hp
      exact (eval_rational_coefficients F x).trans hFx
    · exact (eval_rational_coefficients (pderiv i F) x).trans (hz i)
  apply hx
  ext i
  have hX : X i ∈ J.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℚ)]
    intro y hy
    have hy0 : y = 0 := hgeom hy
    subst y
    simp
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hX
  have hxi : x i ^ k = 0 := by simpa using hxJ ((X i)^k) hk
  exact eq_zero_of_pow_eq_zero hxi

theorem continuous_evalForm {n : ℕ} (F : IntForm n) :
    Continuous (evalForm F : (Fin n → ℝ) → ℝ) := by
  unfold evalForm
  simp only [MvPolynomial.eval₂_eq']
  fun_prop

/-- Every partial derivative vanishes at the origin in degree at least two. -/
theorem evalForm_pderiv_origin {n d : ℕ} {R : Type*} [CommRing R] {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (i : Fin n) :
    evalForm (pderiv i F) (0 : Fin n → R) = 0 := by
  have he : (fun _ : Fin n => (0 : R)) = 0 := rfl
  simpa [zero_pow (show d - 1 ≠ 0 by omega), he] using
    (evalForm_scale (R := R) (F := pderiv i F) hF.pderiv 0 (0 : Fin n → R))

theorem HasNonsingularZero.hasNonzeroZero {n d : ℕ} {R : Type*} [CommRing R]
    {F : IntForm n} (h : HasNonsingularZero F R) (hd : 2 ≤ d) (hF : F.IsHomogeneous d) :
    HasNonzeroZero F R := by
  obtain ⟨x, hFx, i, hi⟩ := h
  exact ⟨x, fun hzero => hi (hzero ▸ evalForm_pderiv_origin hd hF i), hFx⟩

private theorem exists_transverseWeight_aux {n d : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) (z : Fin n → ℝ) (hz : z ≠ 0)
    (hzF : evalForm F z = 0) (i : Fin n) (hi : evalForm (pderiv i F) z ≠ 0) :
    ∃ w, TransverseWeight F w := by
  let c : ℝ := (1 + ‖z‖)⁻¹
  have hc : 0 < c := inv_pos.mpr (by positivity)
  let x : Fin n → ℝ := fun j ↦ c * z j
  have hx : x ≠ 0 := by
    intro he
    apply hz
    ext j
    have H := congrFun he j
    exact (mul_eq_zero.mp H).resolve_left hc.ne'
  have hxF : evalForm F x = 0 := by rw [evalForm_scale hF c z, hzF, mul_zero]
  have hxi : evalForm (pderiv i F) x ≠ 0 := by
    rw [evalForm_scale hF.pderiv c z]
    exact mul_ne_zero (pow_ne_zero _ hc.ne') hi
  have hxcube : ∀ j, |x j| < 1 := by
    intro j
    rw [show x j = c * z j from rfl, abs_mul, abs_of_pos hc]
    have hle : |z j| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z j
    calc
      _ ≤ c * ‖z‖ := mul_le_mul_of_nonneg_left hle hc.le
      _ < 1 := by
        dsimp [c]
        rw [inv_mul_eq_div, div_lt_one (by positivity)]
        linarith
  let b : ℝ := |evalForm (pderiv i F) x| / 2
  have hb : 0 < b := half_pos (abs_pos.mpr hxi)
  let U : Set (Fin n → ℝ) :=
    {y | ∀ j, |y j| < 1} ∩ ({0} : Set (Fin n → ℝ))ᶜ ∩
      {y | b < |evalForm (pderiv i F) y|}
  have hopenBox : IsOpen {y : Fin n → ℝ | ∀ j, |y j| < 1} := by
    rw [show {y : Fin n → ℝ | ∀ j, |y j| < 1} =
        ⋂ j : Fin n, {y : Fin n → ℝ | |y j| < 1} by ext; simp]
    exact isOpen_iInter_of_finite (fun j ↦ isOpen_lt (continuous_apply j).abs continuous_const)
  have hopen : IsOpen U :=
    (hopenBox.inter isClosed_singleton.isOpen_compl).inter
      (isOpen_lt continuous_const (continuous_evalForm _).abs)
  have hxU : x ∈ U := ⟨⟨hxcube, hx⟩, half_lt_self (abs_pos.mpr hxi)⟩
  obtain ⟨w, hω, hcompact, hsmooth, hrange, hval⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hopen.mem_nhds hxU)
  refine ⟨w, hsmooth, hcompact, fun y ↦ (hrange ⟨y, rfl⟩).1,
    fun y ↦ (hrange ⟨y, rfl⟩).2, fun y hy ↦ (hω hy).1.1, ?_,
    ⟨x, hxF, hval ▸ zero_lt_one⟩, ⟨i, b, hb, fun y hy ↦ (hω hy).2.le⟩⟩
  exact fun hzω ↦ (hω hzω).1.2 rfl

/-- Construct a transverse weight from a single nonsingular real zero. -/
theorem exists_transverseWeight_of_nonsingularZero {n d : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hreal : HasNonsingularZero F ℝ) :
    ∃ w, TransverseWeight F w := by
  obtain ⟨z, hzF, i, hi⟩ := hreal
  exact exists_transverseWeight_aux hF z
    (fun hzero => hi (hzero ▸ evalForm_pderiv_origin hd hF i)) hzF i hi

/-- Construct the weight supported near the rescaled smooth real zero. -/
theorem exists_transverseWeight {n d : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F) (hreal : HasNonzeroZero F ℝ) :
    ∃ w, TransverseWeight F w := by
  obtain ⟨z, hz, hzF⟩ := hreal
  obtain ⟨i, hi⟩ := hs.nonsingular_over z hz hzF
  exact exists_transverseWeight_aux hF z hz hzF i hi

end
end Birch
