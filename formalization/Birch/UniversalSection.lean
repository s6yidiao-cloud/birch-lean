import Birch.SectionPolynomial
import Birch.CompletionGeometry

/-!
# The universal restricted gradient

The coefficient of each free-coordinate monomial in a linear section of a
form of degree `r` is homogeneous of degree `r` in the matrix entries.
The same degree bound holds for each gradient coefficient.
-/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

variable {n l r : ℕ}

/-- Linear substitution with entries in a coefficient ring. -/
def linearSectionOver {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin l) R) (F : IntForm n) : MvPolynomial (Fin l) R :=
  eval₂ (C.comp (Int.castRingHom R)) (fun i => ∑ j, C (U i j) * X j) F

/-- Linear substitution with coefficient-ring entries preserves homogeneity. -/
theorem isHomogeneous_linearSectionOver {K : Type*} [CommRing K]
    (U : Matrix (Fin n) (Fin l) K) {F : IntForm n} (hF : F.IsHomogeneous r) :
    (linearSectionOver U F).IsHomogeneous r := by
  have H := hF.eval₂ (C.comp (Int.castRingHom K))
    (fun i => ∑ j, C (U i j) * X j) (fun a => isHomogeneous_C _ _) (n := 1)
    (fun i => IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (U i j) j)
  simpa only [linearSectionOver, one_mul] using H

/-- A restriction with one independent parameter for each matrix entry. -/
def universalLinearSection (R : Type*) [CommRing R] (F : IntForm n) :
    MvPolynomial (Fin l) (MvPolynomial (Fin n × Fin l) R) :=
  linearSectionOver (fun i j => X (i,j)) F

/-- Specializing the matrix parameters gives the prescribed section. -/
theorem map_universalLinearSection {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (U : Matrix (Fin n) (Fin l) S) (F : IntForm n) :
    MvPolynomial.map (eval₂Hom f (fun ij : Fin n × Fin l => U ij.1 ij.2))
      (universalLinearSection R F) = linearSectionOver U F := by
  unfold universalLinearSection linearSectionOver
  rw [hom_eval₂]
  congr 1
  · ext a
    simp only [RingHom.comp_apply, Int.coe_castRingHom, map_intCast]
  · funext i
    simp only [map_sum, map_mul, map_C, map_X, coe_eval₂Hom, eval₂_X]

/-- Specializing a matrix with integer entries agrees with integral substitution
followed by reduction of the coefficients. -/
theorem map_linearSection {R : Type*} [CommRing R]
    (U : Matrix (Fin n) (Fin l) ℤ) (F : IntForm n) :
    MvPolynomial.map (Int.castRingHom R) (linearSection U F) =
      linearSectionOver (U.map (Int.castRingHom R)) F := by
  rw [linearSection, aeval_def, algebraMap_eq, hom_eval₂]
  congr 1
  · ext a
    simp
  · funext i
    simp only [map_sum, map_mul, map_C, map_X, Matrix.map_apply]

private abbrev CoefficientsHomogeneous {σ τ R : Type*} [CommRing R]
    (P : MvPolynomial σ (MvPolynomial τ R)) (d : ℕ) : Prop :=
  ∀ s, (AddMonoidAlgebra.coeff P s).IsHomogeneous d

private theorem coeffsHomogeneous_C {σ τ R : Type*} [CommRing R] {a : MvPolynomial τ R}
    {d : ℕ} (ha : a.IsHomogeneous d) : CoefficientsHomogeneous (C (σ := σ) a) d := by
  classical
  intro s
  by_cases hs : s = 0
  · subst s
    simpa only [coeff_C, ite_true] using ha
  · rw [coeff_C_of_ne_zero hs]
    exact isHomogeneous_zero _ _ _

private theorem coeffsHomogeneous_mul {σ τ R : Type*} [CommRing R]
    {P Q : MvPolynomial σ (MvPolynomial τ R)} {d e : ℕ}
    (hP : CoefficientsHomogeneous P d) (hQ : CoefficientsHomogeneous Q e) :
    CoefficientsHomogeneous (P*Q) (d+e) := by
  classical
  intro s
  rw [coeff_mul]
  exact IsHomogeneous.sum _ _ _ fun a _ => (hP a.1).mul (hQ a.2)

private theorem coeffsHomogeneous_pow {σ τ R : Type*} [CommRing R]
    {P : MvPolynomial σ (MvPolynomial τ R)} {d : ℕ} (hP : CoefficientsHomogeneous P d) (k : ℕ) :
    CoefficientsHomogeneous (P^k) (d*k) := by
  induction k with
  | zero =>
    simp only [pow_zero, mul_zero, ← map_one C]
    exact coeffsHomogeneous_C (isHomogeneous_one _ _)
  | succ k hk =>
    simpa only [pow_succ, Nat.mul_succ] using coeffsHomogeneous_mul hk hP

private theorem coeffsHomogeneous_prod {ι σ τ R : Type*} [CommRing R] (s : Finset ι)
    (P : ι → MvPolynomial σ (MvPolynomial τ R)) (d : ι → ℕ)
    (h : ∀ i ∈ s, CoefficientsHomogeneous (P i) (d i)) :
    CoefficientsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, ← map_one C]
    exact coeffsHomogeneous_C (isHomogeneous_one _ _)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact coeffsHomogeneous_mul (h _ (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Coefficients of a symbolic restriction have parameter degree equal to the
homogeneous degree of its source, or vanish. -/
theorem coeff_universalLinearSection_isHomogeneous (R : Type*) [CommRing R]
    (F : IntForm n) (hF : F.IsHomogeneous r) (s : Fin l →₀ ℕ) :
    (AddMonoidAlgebra.coeff (universalLinearSection R F) s).IsHomogeneous r := by
  classical
  let A := MvPolynomial (Fin n × Fin l) R
  let g : Fin n → MvPolynomial (Fin l) A := fun i => ∑ j : Fin l, C (X (i,j)) * X j
  have hg (i : Fin n) : CoefficientsHomogeneous (g i) 1 := by
    intro u
    rw [show g i = _ from rfl, coeff_sum]
    apply IsHomogeneous.sum
    intro j _
    rw [coeff_C_mul, coeff_X]
    split_ifs <;> simp [isHomogeneous_X, isHomogeneous_zero]
  have hterm (m : Fin n →₀ ℕ) (hm : m ∈ F.support) :
      CoefficientsHomogeneous
        (C (C ((AddMonoidAlgebra.coeff F m : ℤ) : R)) * ∏ i ∈ m.support, g i ^ m i) r := by
    have H := coeffsHomogeneous_prod m.support (fun i => g i ^ m i) (fun i => 1 * m i)
      (fun i _ => coeffsHomogeneous_pow (hg i) (m i))
    have hC : CoefficientsHomogeneous (C (σ := Fin l) (C ((AddMonoidAlgebra.coeff F m : ℤ) : R) : A)) 0 :=
      coeffsHomogeneous_C (isHomogeneous_C _ _)
    have hdeg : (∑ i ∈ m.support, 1 * m i) = r := by
      have Hdeg : (Finsupp.weight (fun _ : Fin n => (1 : ℕ))) m = r :=
        hF (mem_support_iff.mp hm)
      rw [← Finsupp.degree_eq_weight_one] at Hdeg
      simpa only [one_mul, Finsupp.degree_apply, Finsupp.sum] using Hdeg
    simpa only [hdeg, zero_add] using coeffsHomogeneous_mul hC H
  simp only [universalLinearSection, linearSectionOver, eval₂_eq, RingHom.comp_apply, Int.coe_castRingHom]
  rw [coeff_sum]
  exact IsHomogeneous.sum _ _ _ fun m hm => hterm m hm s

/-- Gradient coefficients of the symbolic restriction also have parameter
degree bounded by the homogeneous degree of the source. -/
theorem coeff_pderiv_universalLinearSection_totalDegree_le (R : Type*) [CommRing R]
    (F : IntForm n) (hF : F.IsHomogeneous r) (j : Fin l) (s : Fin l →₀ ℕ) :
    (AddMonoidAlgebra.coeff (pderiv j (universalLinearSection R F)) s).totalDegree ≤ r := by
  rw [coeff_pderiv, ← Nat.cast_succ, ← map_natCast C]
  have h := coeff_universalLinearSection_isHomogeneous (l := l) R F hF (s + Finsupp.single j 1)
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, add_zero]
  exact h.totalDegree_le

/-- Evaluating the restricted form agrees with evaluating the original form at
its matrix product. -/
theorem eval_linearSectionOver {K : Type*} [CommRing K]
    (U : Matrix (Fin n) (Fin l) K) (F : IntForm n) (x : Fin l → K) :
    (linearSectionOver U F).eval x = evalForm F (U *ᵥ x) := by
  unfold linearSectionOver MvPolynomial.eval evalForm
  rw [hom_eval₂]
  congr 1
  · ext a
    simp
  · funext i
    simp only [coe_eval₂Hom, eval₂_sum, eval₂_mul, eval₂_X, eval₂_C, RingHom.id_apply,
      mulVec, dotProduct]

/-- The matrix chain rule for a restriction over any coefficient ring. -/
theorem pderiv_linearSectionOver {K : Type*} [CommRing K]
    (U : Matrix (Fin n) (Fin l) K) (F : IntForm n) (j : Fin l) :
    pderiv j (linearSectionOver U F) =
      ∑ i, C (U i j) * linearSectionOver U (pderiv i F) := by
  classical
  let L : IntForm n →+* MvPolynomial (Fin l) K :=
    eval₂Hom (C.comp (Int.castRingHom K)) (fun i => ∑ j, C (U i j) * X j)
  change pderiv j (L F) = ∑ i, C (U i j) * L (pderiv i F)
  have hX (i : Fin n) : L (X i) = ∑ j, C (U i j) * X j := by simp [L]
  have hDX (i : Fin n) : pderiv j (L (X i)) = C (U i j) := by
    rw [hX]
    simp [pderiv_X, Pi.single_apply, mul_ite]
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F G hF hG =>
    simp only [map_add, hF, hG, mul_add, Finset.sum_add_distrib]
  | mul_X F k hF =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hF, hDX, map_add,
      mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single k]
      · simp [pderiv_X]
        ring
      · intro i _ hi
        simp [pderiv_X, Pi.single_eq_of_ne hi.symm]
      · simp
    · apply Finset.sum_congr rfl
      intro i _
      ring

/-- The evaluated gradient of the restriction is the pullback of the original
polynomial's gradient by the transpose of the section matrix. -/
theorem eval_pderiv_linearSectionOver {K : Type*} [CommRing K]
    (U : Matrix (Fin n) (Fin l) K) (F : IntForm n) (j : Fin l) (x : Fin l → K) :
    (pderiv j (linearSectionOver U F)).eval x =
      ∑ i, U i j * evalForm (pderiv i F) (U *ᵥ x) := by
  rw [pderiv_linearSectionOver]
  simp only [eval_sum, eval_mul, eval_C, eval_linearSectionOver]


end
end Birch
