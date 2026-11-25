module

public import Birch.GradientIdealCertificate
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! # Counting a fiber from a homogeneous monomial certificate -/

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

private def evalOnFinset {ι K : Type*} [Field K] (T : Finset (ι → K)) :
    MvPolynomial ι K →ₐ[K] (T → K) :=
  aeval (fun i x => x.val i)

private theorem evalOnFinset_apply {ι K : Type*} [Field K]
    (T : Finset (ι → K)) (F : MvPolynomial ι K) (x : T) :
    evalOnFinset T F x = F.eval x.val := by
  have h : (Pi.evalAlgHom K (fun _ : T => K) x).comp (evalOnFinset T) = aeval x.val := by
    ext i
    simp [evalOnFinset]
  have hh := DFunLike.congr_fun h F
  change evalOnFinset T F x = aeval x.val F at hh
  simpa only [aeval_eq_eval] using hh

private theorem evalOnFinset_surjective {ι K : Type*} [Field K] (T : Finset (ι → K)) :
    Function.Surjective (evalOnFinset T) := by
  classical
  have hδ (p : T) : ∃ F : MvPolynomial ι K, ∀ q : T, F.eval q.val = if q = p then 1 else 0 := by
    let S := Finset.univ.erase p
    have hdiff (q : S) : ∃ i : ι, p.val i ≠ q.val.val i := by
      by_contra! hn
      have he : p = q.val := Subtype.ext (funext hn)
      exact (Finset.mem_erase.mp q.prop).1 he.symm
    choose i hi using hdiff
    let g (q : S) : MvPolynomial ι K :=
      C ((p.val (i q) - q.val.val (i q))⁻¹) * (X (i q) - C (q.val.val (i q)))
    refine ⟨∏ q : S, g q, ?_⟩
    intro q
    rw [map_prod]
    split_ifs with hq
    · subst q
      apply Finset.prod_eq_one
      intro q _
      simp only [g, eval_mul, eval_C, eval_sub, eval_X]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (hi q))
    · let q' : S := ⟨q, Finset.mem_erase.mpr ⟨hq, Finset.mem_univ _⟩⟩
      apply Finset.prod_eq_zero (Finset.mem_univ q')
      simp [g, q']
  choose F hF using hδ
  intro y
  refine ⟨∑ p : T, C (y p) * F p, ?_⟩
  funext q
  simp [evalOnFinset_apply, hF, mul_ite]


private def smallMonomialEmbedding (n D : ℕ) : {a : Fin n →₀ ℕ // a.degree < D} ↪ (Fin n → Fin D) := by
  classical
  let g (a : {a : Fin n →₀ ℕ // a.degree < D}) (i : Fin n) : Fin D :=
    ⟨a.val i, (by
      have h : a.val i ≤ a.val.degree := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.single_le_sum (f := a.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      exact h.trans_lt a.prop)⟩
  refine ⟨g, ?_⟩
  intro a b he
  apply Subtype.ext
  apply Finsupp.ext
  intro i
  exact congrArg Fin.val (congrFun he i)

/-- Monomials of degree less than `D` use exponents less than `D` in every
coordinate. -/
theorem card_monomials_degree_lt_le_pow (n D : ℕ) :
    Nat.card {a : Fin n →₀ ℕ // a.degree < D} ≤ D^n := by
  have h := Nat.card_le_card_of_injective (smallMonomialEmbedding n D)
    (smallMonomialEmbedding n D).injective
  have hcard : Nat.card (Fin n → Fin D) = D^n := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  exact h.trans_eq hcard

private theorem small_monomials_span_of_reduction {n D : ℕ} {K A : Type*} [Field K]
    [Semiring A] [Algebra K A] (E : MvPolynomial (Fin n) K →ₐ[K] A)
    (hE : Function.Surjective E)
    (hred : ∀ a : Fin n →₀ ℕ, a.degree = D →
      ∃ F : MvPolynomial (Fin n) K, F.totalDegree < D ∧
        E F = E (monomial a 1)) :
    Submodule.span K (Set.range fun a : {a : Fin n →₀ ℕ // a.degree < D} =>
      E (monomial a.val (1 : K))) = ⊤ := by
  classical
  let S := {a : Fin n →₀ ℕ // a.degree < D}
  let v (a : S) := E (monomial a.val (1 : K))
  let B := Submodule.span K (Set.range v)
  have hcoeff (a : Fin n →₀ ℕ) (c : K) (h : E (monomial a 1) ∈ B) :
      E (monomial a c) ∈ B := by
    have H := B.smul_mem c h
    rwa [← map_smul E, smul_monomial, smul_eq_mul, mul_one] at H
  have hmon (q : ℕ) : ∀ a : Fin n →₀ ℕ, a.degree = q → E (monomial a 1) ∈ B := by
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro a ha
      by_cases hlt : q < D
      · exact Submodule.subset_span ⟨⟨a,ha ▸ hlt⟩,rfl⟩
      obtain ⟨b,hba,hb⟩ := Finsupp.exists_le_degree_eq a D (ha.symm ▸ Nat.le_of_not_gt hlt)
      obtain ⟨P,hP,hPeval⟩ := hred b hb
      let R := monomial (a-b) (1 : K) * P
      have hsub : a-b+b = a := tsub_add_cancel_of_le hba
      have hdeg := congrArg Finsupp.degree hsub
      rw [map_add, hb, ha] at hdeg
      have hmdeg : (monomial (a-b) (1 : K)).totalDegree ≤ (a-b).degree := by
        simpa only [Finsupp.degree_apply, Finsupp.sum, id_eq] using totalDegree_monomial_le (a-b) (1 : K)
      have hR : R.totalDegree < q := calc
        _ ≤ (monomial (a-b) (1 : K)).totalDegree + P.totalDegree := totalDegree_mul _ _
        _ < (a-b).degree + D := add_lt_add_of_le_of_lt hmdeg hP
        _ = q := hdeg
      have hR_eval : E R = E (monomial a 1) := by
        change E (monomial (a-b) 1 * P) = _
        rw [map_mul, hPeval, ← map_mul, MvPolynomial.monomial_mul_monomial, mul_one, hsub]
      rw [← hR_eval, R.as_sum, map_sum]
      apply Submodule.sum_mem
      intro m hm
      have hmd : m.degree ≤ R.totalDegree := le_totalDegree hm
      exact hcoeff m _ (ih m.degree (hmd.trans_lt hR) m rfl)
  apply top_unique
  intro g _
  obtain ⟨P,rfl⟩ := hE g
  change E P ∈ B
  rw [P.as_sum, map_sum]
  apply Submodule.sum_mem
  intro a _
  exact hcoeff a _ (hmon a.degree a rfl)

private theorem card_le_small_monomials_of_eval_reduction {n D : ℕ} {K : Type*} [Field K]
    (T : Finset (Fin n → K))
    (hred : ∀ a : Fin n →₀ ℕ, a.degree = D →
      ∃ F : MvPolynomial (Fin n) K, F.totalDegree < D ∧
        evalOnFinset T F = evalOnFinset T (monomial a 1)) :
    T.card ≤ Nat.card {a : Fin n →₀ ℕ // a.degree < D} := by
  let S := {a : Fin n →₀ ℕ // a.degree < D}
  let : Fintype S := Fintype.ofInjective (smallMonomialEmbedding n D)
    (smallMonomialEmbedding n D).injective
  have htop := small_monomials_span_of_reduction (evalOnFinset T) (evalOnFinset_surjective T) hred
  have hcard := finrank_le_of_span_eq_top htop
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hcard
  simpa only [Nat.card_eq_fintype_card, S] using hcard

/-- A monomial certificate for the top forms bounds the dimension of the
quotient by their lower-degree perturbations. -/
theorem finite_quotient_and_finrank_le_of_perturbed_homogeneous_system
    {n m e D : ℕ} {K : Type*} [Field K]
    (he : 0 < e) (hD : e ≤ D) (f g : Fin m → MvPolynomial (Fin n) K)
    (hf : ∀ i, (f i).IsHomogeneous e) (hg : ∀ i, (g i).totalDegree < e)
    (hmem : ∀ a : Fin n →₀ ℕ, a.degree = D → monomial a (1 : K) ∈ Ideal.span (Set.range f)) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i => f i - g i)) ∧
    Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i => f i - g i)) ≤ D ^ n := by
  classical
  let J := Ideal.span (Set.range fun i => f i - g i)
  let E := Ideal.Quotient.mkₐ K J
  have hfE (i : Fin m) : E (f i) = E (g i) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  have H := small_monomials_span_of_reduction (D := D) E Ideal.Quotient.mk_surjective
    (fun a ha => by
      obtain ⟨b,hb,hbsum⟩ := (homogeneous_monomial_mem_span_iff f hf ha hD).mp (hmem a ha)
      let P := ∑ i, b i * g i
      refine ⟨P, ?_, ?_⟩
      · refine (totalDegree_finsetSum_le (s := Finset.univ) (f := fun i => b i * g i)
          (d := D-1) ?_).trans_lt (by omega)
        intro i _
        exact (totalDegree_mul _ _).trans (by have := (hb i).totalDegree_le; have := hg i; omega)
      · rw [← hbsum, map_sum, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_mul, map_mul, hfE])
  let S := {a : Fin n →₀ ℕ // a.degree < D}
  let : Fintype S := Fintype.ofInjective (smallMonomialEmbedding n D)
    (smallMonomialEmbedding n D).injective
  have : Module.Finite K (MvPolynomial (Fin n) K ⧸ J) := by
    constructor
    rw [← H]
    exact Submodule.fg_span (Set.finite_range _)
  refine ⟨inferInstance, ?_⟩
  have hcard := finrank_le_of_span_eq_top H
  exact (show Module.finrank K (MvPolynomial (Fin n) K ⧸ J) ≤ Nat.card S by
    simpa only [Nat.card_eq_fintype_card] using hcard).trans (card_monomials_degree_lt_le_pow n D)

/-- A quotient with the stated monomial certificate is finite-dimensional. -/
theorem finite_quotient_of_perturbed_homogeneous_system {n m e D : ℕ} {K : Type*} [Field K]
    (he : 0 < e) (hD : e ≤ D) (f g : Fin m → MvPolynomial (Fin n) K)
    (hf : ∀ i, (f i).IsHomogeneous e) (hg : ∀ i, (g i).totalDegree < e)
    (hmem : ∀ a : Fin n →₀ ℕ, a.degree = D → monomial a (1 : K) ∈ Ideal.span (Set.range f)) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i => f i - g i)) :=
  (finite_quotient_and_finrank_le_of_perturbed_homogeneous_system he hD f g hf hg hmem).1

/-- The degree-`D` certificate bounds the size of any set of solutions over
a fixed value of the linear projection. -/
theorem card_le_small_monomials_of_monomial_certificate {n m k e D : ℕ} {K : Type*} [Field K]
    (he : 0 < e) (hD : e ≤ D)
    (f : Fin m → MvPolynomial (Fin n) K) (l : Fin k → MvPolynomial (Fin n) K) (c : Fin k → K)
    (hf : ∀ i, (f i).IsHomogeneous e) (hl : ∀ j, (l j).IsHomogeneous 1)
    (hmem : ∀ a : Fin n →₀ ℕ, a.degree = D → monomial a (1 : K) ∈
      Ideal.span (Set.range (Fin.append f (fun j => l j ^ e))))
    (T : Finset (Fin n → K))
    (hT : ∀ x ∈ T, (∀ i, (f i).eval x = 0) ∧ (∀ j, (l j).eval x = c j)) :
    T.card ≤ Nat.card {a : Fin n →₀ ℕ // a.degree < D} := by
  apply card_le_small_monomials_of_eval_reduction T
  intro a ha
  let g := Fin.append f (fun j => l j ^ e)
  have hg (i : Fin (m+k)) : (g i).IsHomogeneous e := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [g, Fin.append_left] using hf j
    · simpa only [g, Fin.append_right, one_mul] using (hl j).pow e
  obtain ⟨b,hb,hbsum⟩ := (homogeneous_monomial_mem_span_iff g hg ha hD).mp (hmem a ha)
  let P : MvPolynomial (Fin n) K := ∑ j : Fin k, C ((c j)^e) * b (Fin.natAdd m j)
  have hP : P.totalDegree ≤ D-e := by
    apply totalDegree_finsetSum_le
    intro j _
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (hb (Fin.natAdd m j)).totalDegree_le
  refine ⟨P,hP.trans_lt (by omega),?_⟩
  funext x
  simp only [evalOnFinset_apply, P, eval_sum, eval_mul, eval_C]
  rw [← hbsum, eval_sum, Fin.sum_univ_add]
  have hx := hT x.val x.prop
  simp only [g, Fin.append_left, Fin.append_right, eval_mul, hx.1, hx.2, mul_zero,
    Finset.sum_const_zero, zero_add, eval_pow]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- A uniform bound for the size of any finite subset of the fiber. -/
theorem card_le_pow_of_monomial_certificate {n m k e D : ℕ} {K : Type*} [Field K]
    (he : 0 < e) (hD : e ≤ D)
    (f : Fin m → MvPolynomial (Fin n) K) (l : Fin k → MvPolynomial (Fin n) K) (c : Fin k → K)
    (hf : ∀ i, (f i).IsHomogeneous e) (hl : ∀ j, (l j).IsHomogeneous 1)
    (hmem : ∀ a : Fin n →₀ ℕ, a.degree = D → monomial a (1 : K) ∈
      Ideal.span (Set.range (Fin.append f (fun j => l j ^ e))))
    (T : Finset (Fin n → K))
    (hT : ∀ x ∈ T, (∀ i, (f i).eval x = 0) ∧ (∀ j, (l j).eval x = c j)) :
    T.card ≤ D^n :=
  (card_le_small_monomials_of_monomial_certificate he hD f l c hf hl hmem T hT).trans
    (card_monomials_degree_lt_le_pow n D)

end
end Birch
