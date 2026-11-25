module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Homogeneous gradient certificates -/

open MvPolynomial
open scoped BigOperators

namespace Birch

/-- If an ideal contains all monomials at one degree, it contains every
monomial of greater degree. -/
theorem ideal_contains_monomials_of_degree_le {ι R : Type*} [CommRing R]
    {J : Ideal (MvPolynomial ι R)} {D : ℕ}
    (hD : ∀ m : ι →₀ ℕ, m.degree = D → monomial m (1 : R) ∈ J)
    {m : ι →₀ ℕ} (hm : D ≤ m.degree) : monomial m (1 : R) ∈ J := by
  classical
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
  induction k generalizing m with
  | zero => exact hD m (by simpa only [add_zero] using hk)
  | succ k ih =>
      have hm₀ : m ≠ 0 := by
        intro h
        rw [h, map_zero] at hk
        omega
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra! h
        exact hm₀ (Finsupp.ext h)
      let a := Finsupp.single i (1 : ℕ)
      have ha : a ≤ m := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
      have he : m-a+a = m := tsub_add_cancel_of_le ha
      have hdeg := congrArg Finsupp.degree he
      rw [map_add, Finsupp.degree_single] at hdeg
      have hma : (m-a).degree = D+k := by omega
      rw [← he, monomial_add_single, pow_one]
      exact J.mul_mem_right _ (ih (by omega) hma)

/-- An ideal whose zero locus is contained in the origin contains every
monomial in sufficiently large degree. -/
theorem exists_monomial_certificate_degree {l : ℕ} {K : Type*}
    [Field K] [IsAlgClosed K] (J : Ideal (MvPolynomial (Fin l) K)) (b : ℕ)
    (hs : zeroLocus K J ⊆ {0}) :
    ∃ D : ℕ, 0 < D ∧ b ≤ D ∧
      ∀ m : Fin l →₀ ℕ, D ≤ m.degree → monomial m (1 : K) ∈ J := by
  classical
  have hX (i : Fin l) : X i ∈ J.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have hx₀ : x = 0 := hs hx
    simp [hx₀]
  choose k hk using fun i => Ideal.mem_radical_iff.mp (hX i)
  let D := b + (∑ i, k i) + 1
  refine ⟨D, by dsimp [D]; omega, by dsimp [D]; omega, ?_⟩
  intro m hm
  obtain ⟨i, hi⟩ : ∃ i : Fin l, k i ≤ m i := by
    by_contra! h
    have hle : m.degree ≤ ∑ i, k i := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.sum_le_sum fun i _ => (h i).le
    dsimp [D] at hm
    omega
  let a := Finsupp.single i (k i)
  have ha : a ≤ m := Finsupp.single_le_iff.mpr hi
  have he : m-a+a = m := tsub_add_cancel_of_le ha
  rw [← he, monomial_add_single]
  exact J.mul_mem_left _ (hk i)

/-- A gradient locus contained in the origin yields an ideal certificate
in every sufficiently large homogeneous degree. -/
theorem exists_gradient_certificate_degree {l r : ℕ} {K : Type*}
    [Field K] [IsAlgClosed K] {G : MvPolynomial (Fin l) K}
    (hs : ∀ x : Fin l → K, (∀ j, (pderiv j G).eval x = 0) → x = 0) :
    ∃ D : ℕ, 0 < D ∧ r-1 ≤ D ∧
      ∀ m : Fin l →₀ ℕ, D ≤ m.degree →
        monomial m (1 : K) ∈ Ideal.span (Set.range fun j : Fin l => pderiv j G) := by
  apply exists_monomial_certificate_degree _ (r-1)
  intro x hx
  exact hs x fun j => hx _ (Ideal.subset_span ⟨j, rfl⟩)

private theorem homogeneousComponent_mul_homogeneous {ι R : Type*} [CommRing R]
    {D e : ℕ} (hD : e ≤ D) (f : MvPolynomial ι R) {g : MvPolynomial ι R}
    (hg : g.IsHomogeneous e) :
    homogeneousComponent D (f*g) = (homogeneousComponent (D-e) f)*g := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [Finset.sum_mul, map_sum]
  rw [Finset.sum_eq_single (D-e)]
  · rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous (D-e) f).mul hg),
      Nat.sub_add_cancel hD, ite_eq_left rfl]
  · intro j _ hj
    rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous j f).mul hg),
      ite_eq_right (by omega : D ≠ j+e)]
  · intro hn
    have hlt : f.totalDegree < D-e := by
      rw [Finset.mem_range] at hn
      omega
    rw [homogeneousComponent_eq_zero _ _ hlt, zero_mul, map_zero]

/-- Monomial membership in a homogeneous ideal may be witnessed by
coefficients of exactly the complementary homogeneous degree. -/
theorem homogeneous_monomial_mem_span_iff {ι R : Type*} [CommRing R] {l D e : ℕ}
    (f : Fin l → MvPolynomial ι R) (hf : ∀ j, (f j).IsHomogeneous e)
    {m : ι →₀ ℕ} (hm : m.degree = D) (hD : e ≤ D) :
    monomial m (1 : R) ∈ Ideal.span (Set.range f) ↔
      ∃ c : Fin l → MvPolynomial ι R, (∀ j, (c j).IsHomogeneous (D-e)) ∧
        ∑ j, c j * f j = monomial m (1 : R) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
    have hh := congrArg (homogeneousComponent D) hc
    rw [map_sum, homogeneousComponent_eq_self (isHomogeneous_monomial 1 hm)] at hh
    simp_rw [homogeneousComponent_mul_homogeneous hD _ (hf _)] at hh
    exact ⟨fun j => homogeneousComponent (D-e) (c j), fun _ => homogeneousComponent_isHomogeneous _ _, hh⟩
  · rintro ⟨c, _, h⟩
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨c,h⟩

/-- Over a Noetherian coefficient ring, uniformly many levels of an indexed
family of algebraic tests suffice to detect nonvanishing after specialization. -/
theorem exists_uniform_specialization_test_bound {R : Type*} [CommRing R] [IsNoetherianRing R]
    (tests : ℕ → Set R) :
    ∃ D : ℕ, ∀ {K : Type*} [CommRing K] (f : R →+* K),
      (∃ N b, b ∈ tests N ∧ f b ≠ 0) → ∃ N ≤ D, ∃ b, b ∈ tests N ∧ f b ≠ 0 := by
  let J (D : ℕ) : Ideal R := Ideal.span {b | ∃ N ≤ D, b ∈ tests N}
  have hJ : Monotone J := by
    intro n m hnm
    apply Ideal.span_mono
    rintro b ⟨N,hN,hb⟩
    exact ⟨N,hN.trans hnm,hb⟩
  obtain ⟨D,hD⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstanceAs (IsNoetherian R R))
    ⟨J,hJ⟩
  refine ⟨D, ?_⟩
  rintro K _ f ⟨N,b,hb,hf⟩
  by_contra! h
  have hker : J D ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro a ⟨M,hM,ha⟩
    exact h M hM a ha
  have hm : b ∈ J (max N D) := Ideal.subset_span ⟨N,le_max_left _ _,hb⟩
  have hstable : J D = J (max N D) := hD _ (le_max_right _ _)
  exact hf (hker (hstable ▸ hm))

end Birch
