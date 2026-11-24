import Birch.ConeHyperplane
import Birch.UniversalSection
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.KrullDimension.Field

/-! # Gradient dimensions under hyperplane restriction -/

open MvPolynomial
open scoped BigOperators Matrix

namespace Birch

noncomputable section

/-- A surjective polynomial substitution carrying the second zero locus into
the first cannot increase the dimension of the corresponding coordinate ring. -/
theorem ringKrullDim_quotient_le_of_substitution {ι κ K : Type*} [Finite κ] [Field K] [IsAlgClosed K]
    (φ : MvPolynomial ι K →ₐ[K] MvPolynomial κ K) (hφ : Function.Surjective φ)
    (I : Ideal (MvPolynomial ι K)) (J : Ideal (MvPolynomial κ K))
    (hzero : ∀ y ∈ zeroLocus K J, (fun i => aeval y (φ (X i))) ∈ zeroLocus K I) :
    ringKrullDim (MvPolynomial κ K ⧸ J) ≤ ringKrullDim (MvPolynomial ι K ⧸ I) := by
  let f := (Ideal.Quotient.mk J.radical).comp φ.toRingHom
  have hker : I ≤ RingHom.ker f := by
    intro F hF
    change Ideal.Quotient.mk J.radical (φ F) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro y hy
    have he : (aeval y).comp φ = aeval (fun i => aeval y (φ (X i))) := by
      ext i
      simp
    exact (DFunLike.congr_fun he F).trans <| hzero y hy F hF
  let q := Ideal.Quotient.lift I f hker
  have hs : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hφ
  have hq : Function.Surjective q := Ideal.Quotient.lift_surjective_of_surjective I hker hs
  have hdim : ringKrullDim (MvPolynomial κ K ⧸ J.radical) ≤
      ringKrullDim (MvPolynomial ι K ⧸ I) := ringKrullDim_le_of_surjective q hq
  rwa [ringKrullDim_quotient J.radical, PrimeSpectrum.zeroLocus_radical,
    ← ringKrullDim_quotient J] at hdim

/-- The point of the hyperplane with the prescribed last coordinates. -/
def hyperplanePoint {n : ℕ} {K : Type*} [Field K] (a : Fin (n+1) → K) (x : Fin n → K) :
    Fin (n+1) → K :=
  Fin.cons (-((∑ j, a j.succ * x j) / a 0)) x

/-- Substitute that hyperplane into a polynomial over the coefficient field. -/
def hyperplaneSubstitution {n : ℕ} {K : Type*} [Field K] (a : Fin (n+1) → K) :
    MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (Fin.cons (∑ j, C (-(a j.succ / a 0)) * X j) X)

theorem hyperplaneSubstitution_surjective {n : ℕ} {K : Type*} [Field K] (a : Fin (n+1) → K) :
    Function.Surjective (hyperplaneSubstitution a) := by
  have he : (hyperplaneSubstitution a).comp (rename Fin.succ) = AlgHom.id K _ := by
    ext j
    simp [hyperplaneSubstitution]
  exact fun G => ⟨rename Fin.succ G, DFunLike.congr_fun he G⟩

theorem eval_hyperplaneSubstitution_X {n : ℕ} {K : Type*} [Field K] (a : Fin (n+1) → K)
    (x : Fin n → K) (i : Fin (n+1)) :
    aeval x (hyperplaneSubstitution a (X i)) = hyperplanePoint a x i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [hyperplaneSubstitution, aeval_X, Fin.cons_zero, map_sum, map_mul, aeval_C,
      Algebra.algebraMap_self_apply, hyperplanePoint, neg_mul]
    rw [Finset.sum_neg_distrib, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [hyperplaneSubstitution, hyperplanePoint]

theorem eval_hyperplaneSubstitution {n : ℕ} {K : Type*} [Field K] (a : Fin (n+1) → K)
    (x : Fin n → K) (G : MvPolynomial (Fin (n+1)) K) :
    (hyperplaneSubstitution a G).eval x = G.eval (hyperplanePoint a x) := by
  have he : (aeval x).comp (hyperplaneSubstitution a) = aeval (hyperplanePoint a x) := by
    ext i
    simpa only [AlgHom.comp_apply, aeval_X] using eval_hyperplaneSubstitution_X a x i
  simpa only [AlgHom.comp_apply, aeval_eq_eval] using DFunLike.congr_fun he G

theorem eval_normalLinearForm_hyperplanePoint {n : ℕ} {K : Type*} [Field K]
    {a : Fin (n+1) → K} (ha : a 0 ≠ 0) (x : Fin n → K) :
    (normalLinearForm a).eval (hyperplanePoint a x) = 0 := by
  rw [eval_normalLinearForm, Fin.sum_univ_succ]
  simp only [hyperplanePoint, Fin.cons_zero, Fin.cons_succ]
  field_simp
  ring


/-- The chain rule on the first-coordinate chart for a hyperplane. -/
theorem pderiv_hyperplaneSubstitution {n : ℕ} {K : Type*} [Field K] (a : Fin (n+1) → K)
    (j : Fin n) (G : MvPolynomial (Fin (n+1)) K) :
    pderiv j (hyperplaneSubstitution a G) =
      C (-(a j.succ / a 0)) * hyperplaneSubstitution a (pderiv 0 G) +
        hyperplaneSubstitution a (pderiv j.succ G) := by
  classical
  let φ := hyperplaneSubstitution a
  have hX (i : Fin (n+1)) : pderiv j (φ (X i)) =
      C (-(a j.succ / a 0)) * φ (pderiv 0 (X i)) + φ (pderiv j.succ (X i)) := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [φ, hyperplaneSubstitution, Derivation.leibniz, smul_eq_mul, pderiv_X, Pi.single_apply, mul_ite]
    · simp [φ, hyperplaneSubstitution, pderiv_X, Pi.single_apply]
  change pderiv j (φ G) = C (-(a j.succ / a 0)) * φ (pderiv 0 G) + φ (pderiv j.succ G)
  induction G using MvPolynomial.induction_on with
  | C c => simp [φ, hyperplaneSubstitution]
  | add F G hF hG => simp only [map_add, hF, hG]; ring
  | mul_X F i hF =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hF, hX]
    ring

/-- Substitution of linear coordinates into a homogeneous form preserves its degree. -/
theorem isHomogeneous_hyperplaneSubstitution {n r : ℕ} {K : Type*} [Field K]
    (a : Fin (n+1) → K) {G : MvPolynomial (Fin (n+1)) K} (hG : G.IsHomogeneous r) :
    (hyperplaneSubstitution a G).IsHomogeneous r := by
  let A : Fin (n+1) → MvPolynomial (Fin n) K :=
    Fin.cons (∑ j, C (-(a j.succ / a 0)) * X j) X
  change (aeval A G).IsHomogeneous r
  have hh (i : Fin (n+1)) : (A i).IsHomogeneous 1 := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∑ j : Fin n, C (-(a j.succ / a 0)) * X j).IsHomogeneous 1
      exact IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ j)
    · change (X j : MvPolynomial (Fin n) K).IsHomogeneous 1
      exact isHomogeneous_X (R := K) j
  simpa only [one_mul] using hG.aeval _ hh

theorem eval_homogeneous_scale {n r : ℕ} {K : Type*} [Field K]
    {G : MvPolynomial (Fin n) K} (hG : G.IsHomogeneous r) (t : K) (x : Fin n → K) :
    G.eval (fun i => t * x i) = t^r * G.eval x := by
  classical
  simp only [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq',
    RingHom.id_apply, mul_pow, Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, Finsupp.degree_apply,
    ← hG.degree_eq_sum_deg_support hs]
  ring

/-- The ideal of the gradient equations over the coefficient field. -/
def gradientIdealOver {n : ℕ} {K : Type*} [Field K] (G : MvPolynomial (Fin n) K) :
    Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range fun i : Fin n => pderiv i G)

/-- On a hyperplane transversal to the smooth points, all new critical
points come from intersecting the old gradient locus with the hyperplane. -/
theorem gradient_dim_hyperplaneSubstitution_le {n r e : ℕ} {K : Type*} [Field K] [IsAlgClosed K]
    {a : Fin (n+1) → K} (ha : a 0 ≠ 0) {G T : MvPolynomial (Fin (n+1)) K}
    (hG : G.IsHomogeneous r) (hr : (r : K) ≠ 0) (hT : T.IsHomogeneous e)
    (htangent : ∀ y : Fin (n+1) → K, G.eval y = 0 →
      T.eval (fun i => (pderiv i G).eval y) = 0)
    (hnT : T.eval a ≠ 0) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ gradientIdealOver (hyperplaneSubstitution a G)) ≤
      ringKrullDim (MvPolynomial (Fin (n+1)) K ⧸
        (gradientIdealOver G ⊔ Ideal.span {normalLinearForm a})) := by
  let I := gradientIdealOver G
  let φ := hyperplaneSubstitution a
  apply ringKrullDim_quotient_le_of_substitution φ (hyperplaneSubstitution_surjective a)
  intro x hx
  simp_rw [show ∀ i, aeval x (φ (X i)) = hyperplanePoint a x i from
    eval_hyperplaneSubstitution_X a x]
  let y := hyperplanePoint a x
  change y ∈ zeroLocus K (I ⊔ Ideal.span {normalLinearForm a})
  have hx₀ (j : Fin n) : (pderiv j (φ G)).eval x = 0 := by
    have H := hx _ (Ideal.subset_span ⟨j,rfl⟩)
    simpa only [aeval_eq_eval] using H
  let c := (pderiv (0 : Fin (n+1)) G).eval y / a 0
  have hc (i : Fin (n+1)) : (pderiv i G).eval y = c * a i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (div_mul_cancel₀ _ ha).symm
    · have hj := hx₀ j
      rw [pderiv_hyperplaneSubstitution, eval_add, eval_mul, eval_C,
        eval_hyperplaneSubstitution, eval_hyperplaneSubstitution] at hj
      change -(a j.succ / a 0) * (pderiv (0 : Fin (n+1)) G).eval y +
        (pderiv j.succ G).eval y = 0 at hj
      rw [neg_mul, neg_add_eq_sub, sub_eq_zero] at hj
      rw [hj]
      unfold c
      ring
  have hy0 := eval_normalLinearForm_hyperplanePoint ha x
  rw [eval_normalLinearForm] at hy0
  change (∑ i, a i * y i) = 0 at hy0
  have hyG : G.eval y = 0 := by
    have he := congrArg (fun f : MvPolynomial (Fin (n+1)) K => f.eval y) hG.sum_X_mul_pderiv
    simp only [eval_sum, eval_mul, eval_X, hc, map_nsmul] at he
    rw [nsmul_eq_mul] at he
    have hz : (∑ i, y i * (c * a i)) = 0 := by
      calc
        _ = c * ∑ i, a i * y i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [hy0, mul_zero]
    rw [hz] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hr
  have hc₀ : c = 0 := by
    by_contra h
    have he := htangent y hyG
    simp only [hc, eval_homogeneous_scale hT] at he
    exact (mul_ne_zero (pow_ne_zero _ h) hnT) he
  have hIg : I ≤ vanishingIdeal K {y} := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change pderiv i G ∈ vanishingIdeal K {y}
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval, hc, hc₀, zero_mul]
  have hIh : Ideal.span {normalLinearForm a} ≤ vanishingIdeal K {y} := by
    apply Ideal.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    change normalLinearForm a ∈ vanishingIdeal K {y}
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval, eval_normalLinearForm]
    exact hy0
  intro f hf
  exact (sup_le hIg hIh hf) y rfl


/-- A hyperplane avoiding the tangent relation drops the gradient dimension. -/
theorem exists_hyperplaneSubstitution_dim_drop {n r s e : ℕ} {K : Type*}
    [Field K] [IsAlgClosed K] [Infinite K] {G T : MvPolynomial (Fin (n+1)) K}
    (hG : G.IsHomogeneous r) (hr : (r : K) ≠ 0) (hT : T.IsHomogeneous e) (hT₀ : T ≠ 0)
    (htangent : ∀ y : Fin (n+1) → K, G.eval y = 0 →
      T.eval (fun i => (pderiv i G).eval y) = 0)
    (hdim : ringKrullDim (MvPolynomial (Fin (n+1)) K ⧸ gradientIdealOver G) ≤
      ((s+1 : ℕ) : WithBot ℕ∞)) :
    ∃ a : Fin (n+1) → K, a 0 ≠ 0 ∧
      ringKrullDim (MvPolynomial (Fin n) K ⧸ gradientIdealOver (hyperplaneSubstitution a G)) ≤
        (s : WithBot ℕ∞) := by
  obtain ⟨a,ha,hnT,hcut⟩ := exists_normalLinearForm_dim_drop 0 (gradientIdealOver G) hT₀ hdim
  exact ⟨a,ha,(gradient_dim_hyperplaneSubstitution_le ha hG hr hT htangent hnT).trans hcut⟩

/-- The matrix of the first-coordinate hyperplane chart. -/
def hyperplaneMatrix {n : ℕ} {K : Type*} [Field K] (a : Fin (n+1) → K) :
    Matrix (Fin (n+1)) (Fin n) K :=
  fun i j => Fin.cases (-(a j.succ / a 0)) (fun k => if k = j then 1 else 0) i

theorem hyperplaneMatrix_mulVec {n : ℕ} {K : Type*} [Field K]
    (a : Fin (n+1) → K) (x : Fin n → K) :
    hyperplaneMatrix a *ᵥ x = hyperplanePoint a x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [hyperplaneMatrix, hyperplanePoint, Matrix.mulVec, dotProduct,
      Fin.cases_zero, Fin.cons_zero, neg_mul, Finset.sum_neg_distrib, Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp [hyperplaneMatrix, hyperplanePoint, Matrix.mulVec, dotProduct, ite_mul]

/-- Successive linear sections are assembled by multiplying their matrices. -/
theorem hyperplaneSubstitution_linearSectionOver {m n : ℕ} {K : Type*} [Field K] [Infinite K]
    (a : Fin (n+1) → K) (U : Matrix (Fin m) (Fin (n+1)) K) (F : IntForm m) :
    hyperplaneSubstitution a (linearSectionOver U F) =
      linearSectionOver (U * hyperplaneMatrix a) F := by
  apply MvPolynomial.funext
  intro x
  rw [eval_hyperplaneSubstitution, eval_linearSectionOver, eval_linearSectionOver,
    ← hyperplaneMatrix_mulVec, Matrix.mulVec_mulVec]


/-- The gradient ideal of the mapped polynomial is the ideal generated by
the mapped integral derivatives. -/
theorem gradientIdealOver_map_int {n : ℕ} {K : Type*} [Field K] (G : IntForm n) :
    gradientIdealOver (MvPolynomial.map (Int.castRingHom K) G) =
      Ideal.span (Set.range fun i : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv i G)) := by
  unfold gradientIdealOver
  simp only [pderiv_map]

/-- An affine cone of dimension at most zero is contained in the origin. -/
theorem zeroLocus_subset_origin_of_dim_le_zero {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (hcone : ∀ x ∈ zeroLocus K I, ∀ a : K, (fun i => a * x i) ∈ zeroLocus K I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ I) ≤ 0) : zeroLocus K I ⊆ {0} := by
  classical
  intro x hxI
  change x = 0
  by_contra hx
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  let φ : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin 1) K :=
    aeval (fun j => C (x j) * X 0)
  let ψ : MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial (Fin n) K :=
    aeval (fun _ => C (x i)⁻¹ * X i)
  have hcomp : φ.comp ψ = AlgHom.id K _ := by
    ext j
    simp only [φ, ψ, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
    have hj : j = 0 := Subsingleton.elim _ _
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, one_mul, hj]
  have hφ : Function.Surjective φ := fun f => ⟨ψ f, DFunLike.congr_fun hcomp f⟩
  have hzero (y : Fin 1 → K) (_ : y ∈ zeroLocus K (⊥ : Ideal (MvPolynomial (Fin 1) K))) :
      (fun j => aeval y (φ (X j))) ∈ zeroLocus K I := by
    have he (j : Fin n) : aeval y (φ (X j)) = y 0 * x j := by
      simp [φ, mul_comm]
    rw [funext he]
    exact hcone x hxI (y 0)
  have h := ringKrullDim_quotient_le_of_substitution φ hφ I ⊥ hzero
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at h
  have hl := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (R := K) (Fin 1)
  rw [ringKrullDim_eq_zero_of_field K, Nat.card_fin, Nat.cast_one, zero_add] at hl
  exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) ((hl.trans h).trans hdim)

/-- A homogeneous gradient cone of dimension at most zero has
no critical points other than the origin. -/
theorem critical_eq_zero_of_gradientIdealOver_dim_le_zero {n r : ℕ} {K : Type*}
    [Field K] [IsAlgClosed K] {G : MvPolynomial (Fin n) K} (hG : G.IsHomogeneous r)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ gradientIdealOver G) ≤ 0)
    (x : Fin n → K) (hcrit : ∀ i, (pderiv i G).eval x = 0) : x = 0 := by
  suffices h : zeroLocus K (gradientIdealOver G) ⊆ {0} by
    apply h
    rw [gradientIdealOver, zeroLocus_span]
    rintro _ ⟨i,rfl⟩
    exact hcrit i
  apply zeroLocus_subset_origin_of_dim_le_zero (gradientIdealOver G) _ hdim
  intro y hy a
  rw [gradientIdealOver, zeroLocus_span] at hy ⊢
  rintro _ ⟨i,rfl⟩
  change (pderiv i G).eval (fun j => a * y j) = 0
  rw [eval_homogeneous_scale hG.pderiv, show (pderiv i G).eval y = 0 from hy _ ⟨i,rfl⟩,
    mul_zero]

end
end Birch
