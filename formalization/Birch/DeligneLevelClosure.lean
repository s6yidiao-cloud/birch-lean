module

public import Birch.DeligneCriticalLocus
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

/-! # Projective closures of affine level sets -/

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

/-- Homogenize the components of degrees at most r using the variable indexed by none. -/
def degreeHomogenization {σ R : Type*} [CommSemiring R] (r : ℕ)
    (g : MvPolynomial σ R) : MvPolynomial (Option σ) R :=
  ∑ j ∈ Finset.range (r + 1), X none ^ (r - j) * rename some (homogeneousComponent j g)

/-- The degree-r equation for the projective closure of the level g = t. -/
def deligneLevelClosure {σ R : Type*} [CommRing R] (r : ℕ)
    (g : MvPolynomial σ R) (t : R) : MvPolynomial (Option σ) R :=
  degreeHomogenization r (g - C t)

/-- Homogenization produces a homogeneous polynomial of the chosen degree. -/
theorem isHomogeneous_degreeHomogenization {σ R : Type*} [CommSemiring R]
    (r : ℕ) (g : MvPolynomial σ R) :
    (degreeHomogenization r g).IsHomogeneous r := by
  unfold degreeHomogenization
  apply IsHomogeneous.sum
  intro j hj
  have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have h : (X none ^ (r-j) * rename some (homogeneousComponent j g)).IsHomogeneous
      (r-j+j) := (isHomogeneous_X_pow (R := R) none (r-j)).mul
        (homogeneousComponent_isHomogeneous j g).rename_isHomogeneous
  rwa [Nat.sub_add_cancel hjr] at h

/-- The level closure equation is homogeneous of degree r. -/
theorem isHomogeneous_deligneLevelClosure {σ R : Type*} [CommRing R]
    (r : ℕ) (g : MvPolynomial σ R) (t : R) :
    (deligneLevelClosure r g t).IsHomogeneous r :=
  isHomogeneous_degreeHomogenization r (g - C t)

/-- Evaluation after adjoining a homogenizing coordinate. -/
theorem eval₂_degreeHomogenization {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (r : ℕ) (g : MvPolynomial σ R) (φ : R →+* S) (z : S) (x : σ → S) :
    (degreeHomogenization r g).eval₂ φ (fun j => j.elim z x) =
      ∑ j ∈ Finset.range (r + 1), z ^ (r - j) * (homogeneousComponent j g).eval₂ φ x := by
  simp only [degreeHomogenization, eval₂_sum, eval₂_mul, eval₂_pow, eval₂_X,
    Option.elim_none, eval₂_rename, Function.comp_def, Option.elim_some]

private theorem sum_homogeneousComponent_of_degree_le {σ R : Type*} [CommSemiring R]
    {r : ℕ} {g : MvPolynomial σ R} (hg : g.totalDegree ≤ r) :
    (∑ j ∈ Finset.range (r + 1), homogeneousComponent j g) = g := by
  refine (Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hg)) (fun j _ hj =>
    homogeneousComponent_eq_zero j g (by simpa only [Finset.mem_range, not_lt,
      Nat.succ_le_iff] using hj))).symm.trans (sum_homogeneousComponent g)

private theorem totalDegree_sub_C_le {σ R : Type*} [CommRing R]
    {r : ℕ} {g : MvPolynomial σ R} (hg : g.totalDegree ≤ r) (t : R) :
    (g - C t).totalDegree ≤ r := by
  exact (totalDegree_sub _ _).trans (max_le hg (by simp))

private theorem homogeneousComponent_sub_C_of_pos {σ R : Type*} [CommRing R]
    {r : ℕ} (hr : 0 < r) (g : MvPolynomial σ R) (t : R) :
    homogeneousComponent r (g - C t) = homogeneousComponent r g := by
  rw [map_sub, homogeneousComponent_eq_zero r (C t) (by simpa only [totalDegree_C] using hr),
    sub_zero]

/-- The affine chart of the closure is the level equation g(x) - t. -/
theorem eval₂_deligneLevelClosure_one {σ R S : Type*} [CommRing R] [CommRing S]
    {r : ℕ} {g : MvPolynomial σ R} (hg : g.totalDegree ≤ r)
    (t : R) (φ : R →+* S) (x : σ → S) :
    (deligneLevelClosure r g t).eval₂ φ (fun j => j.elim 1 x) = g.eval₂ φ x - φ t := by
  rw [deligneLevelClosure, eval₂_degreeHomogenization]
  simp only [one_pow, one_mul, ← eval₂_sum, sum_homogeneousComponent_of_degree_le (totalDegree_sub_C_le hg t),
    eval₂_sub, eval₂_C]

/-- The equation at infinity is the leading homogeneous component. -/
theorem eval₂_deligneLevelClosure_zero {σ R S : Type*} [CommRing R] [CommRing S]
    {r : ℕ} (hr : 0 < r) (g : MvPolynomial σ R) (t : R) (φ : R →+* S) (x : σ → S) :
    (deligneLevelClosure r g t).eval₂ φ (fun j => j.elim 0 x) =
      (homogeneousComponent r g).eval₂ φ x := by
  rw [deligneLevelClosure, eval₂_degreeHomogenization, Finset.sum_eq_single r]
  · simp [homogeneousComponent_sub_C_of_pos hr]
  · intro j hj hne
    have hp : 0 < r-j := by have := Finset.mem_range.mp hj; omega
    simp [zero_pow hp.ne']
  · simp

/-- Differentiation in an original variable commutes with its chart evaluation. -/
theorem eval₂_pderiv_some_degreeHomogenization {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (r : ℕ) (g : MvPolynomial σ R) (φ : R →+* S) (z : S) (x : σ → S) (i : σ) :
    (pderiv (some i) (degreeHomogenization r g)).eval₂ φ (fun j => j.elim z x) =
      ∑ j ∈ Finset.range (r + 1), z ^ (r - j) * (pderiv i (homogeneousComponent j g)).eval₂ φ x := by
  simp only [degreeHomogenization, map_sum, eval₂_sum, pderiv_mul, pderiv_pow,
    pderiv_X_of_ne (show (none : Option σ) ≠ some i by simp), mul_zero, zero_mul, zero_add,
    pderiv_rename (Option.some_injective σ), eval₂_mul, eval₂_pow, eval₂_X, Option.elim_none,
    eval₂_rename, Function.comp_def, Option.elim_some]

/-- The original partial derivatives on the affine chart equal those of g. -/
theorem eval₂_pderiv_some_deligneLevelClosure_one {σ R S : Type*} [CommRing R] [CommRing S]
    {r : ℕ} {g : MvPolynomial σ R} (hg : g.totalDegree ≤ r)
    (t : R) (φ : R →+* S) (x : σ → S) (i : σ) :
    (pderiv (some i) (deligneLevelClosure r g t)).eval₂ φ (fun j => j.elim 1 x) =
      (pderiv i g).eval₂ φ x := by
  rw [deligneLevelClosure, eval₂_pderiv_some_degreeHomogenization]
  simp only [one_pow, one_mul, ← eval₂_sum]
  have hsum := congrArg (pderiv i) (sum_homogeneousComponent_of_degree_le (totalDegree_sub_C_le hg t))
  rw [map_sum] at hsum
  rw [hsum, map_sub, pderiv_C, sub_zero]

/-- At infinity the original partial derivatives are those of the leading form. -/
theorem eval₂_pderiv_some_deligneLevelClosure_zero {σ R S : Type*} [CommRing R] [CommRing S]
    {r : ℕ} (hr : 0 < r) (g : MvPolynomial σ R) (t : R) (φ : R →+* S) (x : σ → S) (i : σ) :
    (pderiv (some i) (deligneLevelClosure r g t)).eval₂ φ (fun j => j.elim 0 x) =
      (pderiv i (homogeneousComponent r g)).eval₂ φ x := by
  rw [deligneLevelClosure, eval₂_pderiv_some_degreeHomogenization, Finset.sum_eq_single r]
  · simp [homogeneousComponent_sub_C_of_pos hr]
  · intro j hj hne
    have hp : 0 < r-j := by have := Finset.mem_range.mp hj; omega
    simp [zero_pow hp.ne']
  · simp

/-- An isolated leading critical point rules out nonzero critical vectors at infinity. -/
theorem eq_zero_of_deligneLevelClosure_infinity_critical {σ R S : Type*}
    [CommRing R] [CommRing S] {r : ℕ} (hr : 0 < r) (g : MvPolynomial σ R) (t : R)
    (φ : R →+* S)
    (hg : ∀ x : σ → S, (∀ i, (pderiv i (homogeneousComponent r g)).eval₂ φ x = 0) → x = 0)
    (x : Option σ → S) (hx₀ : x none = 0)
    (hx : ∀ i, (pderiv (some i) (deligneLevelClosure r g t)).eval₂ φ x = 0) :
    x = 0 := by
  have hchart : x = fun j => j.elim 0 (x ∘ some) := funext fun j => by
    cases j with
    | none => exact hx₀
    | some i => rfl
  have h := hg (x ∘ some) (fun i => by
    have hi := hx i
    rw [hchart, eval₂_pderiv_some_deligneLevelClosure_zero hr] at hi
    exact hi)
  funext j
  cases j with
  | none => exact hx₀
  | some i => exact congrFun h i


/-- The Jacobian conditions in the affine chart are exactly the level equation
and vanishing of the affine partial derivatives. -/
theorem deligneLevelClosure_affine_singular_iff {σ K : Type*} [Fintype σ] [CommRing K]
    {r : ℕ} {g : MvPolynomial σ K} (hg : g.totalDegree ≤ r) (t : K) (x : σ → K) :
    ((deligneLevelClosure r g t).eval (fun j => j.elim 1 x) = 0 ∧
      ∀ j, (pderiv j (deligneLevelClosure r g t)).eval (fun j => j.elim 1 x) = 0) ↔
      g.eval x = t ∧ ∀ i, (pderiv i g).eval x = 0 := by
  let H := deligneLevelClosure r g t
  let u : Option σ → K := fun j => j.elim 1 x
  have hval : H.eval u = g.eval x - t := eval₂_deligneLevelClosure_one hg t (RingHom.id K) x
  have hpartial (i : σ) : (pderiv (some i) H).eval u = (pderiv i g).eval x :=
    eval₂_pderiv_some_deligneLevelClosure_one hg t (RingHom.id K) x i
  change (H.eval u = 0 ∧ ∀ j, (pderiv j H).eval u = 0) ↔ _
  constructor
  · rintro ⟨hz, hd⟩
    exact ⟨sub_eq_zero.mp (hval.symm.trans hz), fun i => (hpartial i).symm.trans (hd (some i))⟩
  · rintro ⟨hz, hd⟩
    have hH0 : H.eval u = 0 := hval.trans (sub_eq_zero.mpr hz)
    have hsome (i : σ) : (pderiv (some i) H).eval u = 0 := (hpartial i).trans (hd i)
    refine ⟨hH0, fun j => ?_⟩
    cases j with
    | some i => exact hsome i
    | none =>
      have heuler := congrArg (eval u) (isHomogeneous_deligneLevelClosure r g t).sum_X_mul_pderiv
      change eval u (∑ j : Option σ, X j * pderiv j H) = eval u (r • H) at heuler
      simpa only [Fintype.sum_option, map_add, map_sum, map_mul, eval_X,
        show u none = 1 from rfl, one_mul, hsome, mul_zero, Finset.sum_const_zero,
        add_zero, map_nsmul, hH0, nsmul_zero]
        using heuler

private def affineCriticalPointEmbedding {K : Type*} [Field K] {n : ℕ}
    (g : MvPolynomial (Fin n) K) :
    {x : Fin n → K | ∀ i, (pderiv i g).eval x = 0} ↪
      ((MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i : Fin n => pderiv i g)) →ₐ[K] K) := by
  let J := Ideal.span (Set.range fun i : Fin n => pderiv i g)
  let T := {x : Fin n → K | ∀ i, (pderiv i g).eval x = 0}
  have hvanish (x : T) (f : MvPolynomial (Fin n) K) (hf : f ∈ J) :
      aeval x.val f = 0 := by
    have hj : J ≤ RingHom.ker (aeval x.val).toRingHom := Ideal.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      apply RingHom.mem_ker.mpr
      change aeval x.val (pderiv i g) = 0
      rw [aeval_eq_eval]
      exact x.property i)
    exact RingHom.mem_ker.mp (hj hf)
  let E (x : T) : (MvPolynomial (Fin n) K ⧸ J) →ₐ[K] K :=
    Ideal.Quotient.liftₐ J (aeval x.val) (hvanish x)
  have hE (x : T) (i : Fin n) : E x (Ideal.Quotient.mk J (X i)) = x.val i :=
    (DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp J (aeval x.val) (hvanish x)) (X i)).trans
      (aeval_X x.val i)
  refine ⟨E, ?_⟩
  intro x y h
  apply Subtype.ext
  funext i
  rw [← hE x i, ← hE y i, h]

/-- Uniformly in the field and the coefficients, the number of geometric
critical points is bounded in terms of the degree and number of variables. -/
theorem exists_uniform_affine_critical_point_bound (n r : ℕ) (hr : 2 ≤ r) :
    ∃ B : ℕ, ∀ {K : Type*} [Field K] [IsAlgClosed K] {g : MvPolynomial (Fin n) K},
      g.totalDegree ≤ r →
      (∀ x : Fin n → K, (∀ i, (pderiv i (homogeneousComponent r g)).eval x = 0) → x = 0) →
      let T := {x : Fin n → K | ∀ i, (pderiv i g).eval x = 0}
      T.Finite ∧ T.ncard ≤ B := by
  obtain ⟨B, hB⟩ := exists_uniform_gradient_quotient_bound n r hr
  refine ⟨B, ?_⟩
  intro K _ _ g hg hcrit T
  let A := MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i : Fin n => pderiv i g)
  have h := hB hg hcrit
  let : Module.Finite K A := h.1
  let E := affineCriticalPointEmbedding g
  let : Finite T := Finite.of_injective E E.injective
  exact ⟨Set.toFinite T, (Nat.card_le_card_of_injective E E.injective).trans
    ((card_algHom_le_finrank K A K).trans h.2)⟩

/-- An isolated leading critical point makes the affine critical locus finite
over the algebraically closed coefficient field. -/
theorem finite_affine_critical_points_of_isolated_leading_critical_point
    {K : Type*} [Field K] [IsAlgClosed K] {n r : ℕ} (hr : 2 ≤ r)
    {g : MvPolynomial (Fin n) K} (hg : g.totalDegree ≤ r)
    (hcrit : ∀ x : Fin n → K, (∀ i, (pderiv i (homogeneousComponent r g)).eval x = 0) → x = 0) :
    Set.Finite {x : Fin n → K | ∀ i, (pderiv i g).eval x = 0} :=
  let ⟨_, hB⟩ := exists_uniform_affine_critical_point_bound n r hr
  (hB hg hcrit).1

/-- The normalized affine representatives of the singular locus of a level
closure form a finite set. The leading-critical-point hypothesis also
excludes singular projective points at infinity. -/
theorem finite_deligneLevelClosure_affine_singular_points {K : Type*} [Field K] [IsAlgClosed K]
    {n r : ℕ} (hr : 2 ≤ r) {g : MvPolynomial (Fin n) K} (hg : g.totalDegree ≤ r)
    (hcrit : ∀ x : Fin n → K, (∀ i, (pderiv i (homogeneousComponent r g)).eval x = 0) → x = 0)
    (t : K) :
    Set.Finite {x : Fin n → K |
      (deligneLevelClosure r g t).eval (fun j => j.elim 1 x) = 0 ∧
        ∀ j, (pderiv j (deligneLevelClosure r g t)).eval (fun j => j.elim 1 x) = 0} := by
  apply (finite_affine_critical_points_of_isolated_leading_critical_point hr hg hcrit).subset
  intro x hx
  exact ((deligneLevelClosure_affine_singular_iff hg t x).mp hx).2


/-- For a homogeneous phase, level homogenization introduces one pure power of
the new coordinate. -/
theorem deligneLevelClosure_of_homogeneous {σ K : Type*} [CommRing K]
    {r : ℕ} {g : MvPolynomial σ K} (hg : g.IsHomogeneous r) (t : K) :
    deligneLevelClosure r g t = rename some g - X none ^ r * C t := by
  have hg' : degreeHomogenization r g = rename some g := by
    rw [degreeHomogenization, Finset.sum_eq_single r]
    · simp [homogeneousComponent_eq_self hg]
    · intro j _ hj
      simp [homogeneousComponent_of_mem hg, hj]
    · simp
  have ht' : degreeHomogenization r (C t : MvPolynomial σ K) = X none ^ r * C t := by
    rw [degreeHomogenization, Finset.sum_eq_single 0]
    · simp [homogeneousComponent_eq_self (isHomogeneous_C σ t)]
    · intro j _ hj
      simp [homogeneousComponent_of_mem (isHomogeneous_C σ t), hj]
    · simp
  unfold deligneLevelClosure
  calc
    _ = degreeHomogenization r g - degreeHomogenization r (C t) := by
      simp only [degreeHomogenization, map_sub, mul_sub, Finset.sum_sub_distrib]
    _ = _ := by rw [hg', ht']

/-- For a homogeneous phase, differentiating in the new coordinate only
differentiates the adjoined pure power. -/
theorem eval_pderiv_none_deligneLevelClosure_of_homogeneous {σ K : Type*} [CommRing K]
    {r : ℕ} {g : MvPolynomial σ K} (hg : g.IsHomogeneous r) (t : K)
    (x : Option σ → K) :
    (pderiv none (deligneLevelClosure r g t)).eval x = -((r : K) * t * x none^(r-1)) := by
  have hz : pderiv none (rename some g) = 0 := by
    apply pderiv_eq_zero_of_notMem_vars
    intro h
    obtain ⟨i, _, hi⟩ := mem_vars_rename some g h
    cases hi
  rw [deligneLevelClosure_of_homogeneous hg t, map_sub, hz, zero_sub,
    pderiv_mul, pderiv_C, mul_zero, add_zero, pderiv_pow, pderiv_X_self, mul_one]
  simp only [map_neg, map_mul, map_natCast, map_pow, eval_X, eval_C]
  ring

/-- A nonzero level of a homogeneous phase with isolated critical point has
no nonzero projective critical vector when the degree is nonzero in the field. -/
theorem eq_zero_of_deligneLevelClosure_critical_of_homogeneous {σ K : Type*} [Field K]
    {r : ℕ} (hr : 0 < r) (hrK : (r : K) ≠ 0) {g : MvPolynomial σ K}
    (hg : g.IsHomogeneous r)
    (hcrit : ∀ x : σ → K, (∀ i, (pderiv i g).eval x = 0) → x = 0)
    {t : K} (ht : t ≠ 0) (x : Option σ → K)
    (hx : ∀ j, (pderiv j (deligneLevelClosure r g t)).eval x = 0) : x = 0 := by
  have hz := hx none
  rw [eval_pderiv_none_deligneLevelClosure_of_homogeneous hg] at hz
  have hx₀ : x none = 0 := by
    by_contra hne
    exact (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hrK ht) (pow_ne_zero _ hne))) hz
  refine eq_zero_of_deligneLevelClosure_infinity_critical hr g t (RingHom.id K) ?_ x hx₀
    (fun i => hx (some i))
  rw [homogeneousComponent_eq_self hg]
  exact hcrit


/-- Evaluating a homogeneous polynomial on a scaled vector multiplies its value by the degree power. -/
theorem eval_scale_of_homogeneous {σ K : Type*} [CommRing K] {r : ℕ}
    {g : MvPolynomial σ K} (hg : g.IsHomogeneous r) (a : K) (x : σ → K) :
    g.eval (fun i => a * x i) = a^r * g.eval x := by
  classical
  change g.eval₂ (RingHom.id K) (fun i => a * x i) = a^r * g.eval₂ (RingHom.id K) x
  simp only [eval₂_eq, mul_pow, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.prod_pow_eq_pow_sum, ← hg.degree_eq_sum_deg_support hm]
  ring

/-- Every nonzero singular representative of the projective level closure
has a normalized affine representative satisfying the same Jacobian conditions. -/
theorem exists_affine_representative_of_deligneLevelClosure_singular {σ K : Type*} [Field K]
    {r : ℕ} (hr : 0 < r) (g : MvPolynomial σ K) (t : K)
    (hcrit : ∀ x : σ → K,
      (∀ i, (pderiv i (homogeneousComponent r g)).eval x = 0) → x = 0)
    (v : Option σ → K) (hv : v ≠ 0)
    (hlevel : (deligneLevelClosure r g t).eval v = 0)
    (hgrad : ∀ j, (pderiv j (deligneLevelClosure r g t)).eval v = 0) :
    ∃ x : σ → K, v = (fun j => v none * j.elim 1 x) ∧
      (deligneLevelClosure r g t).eval (fun j => j.elim 1 x) = 0 ∧
      ∀ j, (pderiv j (deligneLevelClosure r g t)).eval (fun j => j.elim 1 x) = 0 := by
  have hz : v none ≠ 0 := fun h =>
    hv (eq_zero_of_deligneLevelClosure_infinity_critical hr g t (RingHom.id K)
      hcrit v h (fun i => hgrad (some i)))
  let x : σ → K := fun i => (v none)⁻¹ * v (some i)
  have hchart : (fun j : Option σ => j.elim 1 x) = fun j => (v none)⁻¹ * v j := by
    funext j
    cases j with
    | none => exact (inv_mul_cancel₀ hz).symm
    | some i => rfl
  refine ⟨x, ?_, ?_, fun j => ?_⟩
  · funext i
    rw [show i.elim 1 x = (v none)⁻¹ * v i from congrFun hchart i,
      ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  · rw [hchart, eval_scale_of_homogeneous (isHomogeneous_deligneLevelClosure r g t), hlevel, mul_zero]
  · rw [hchart, eval_scale_of_homogeneous (isHomogeneous_deligneLevelClosure r g t).pderiv,
      hgrad, mul_zero]

end
end Birch
