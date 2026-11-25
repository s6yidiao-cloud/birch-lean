import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! # Cutting the dimension of an affine cone by one hyperplane -/

open MvPolynomial

namespace Birch

/-- An element avoiding the minimal primes of an ideal, apart from a single
maximal ideal, cuts the positive-dimensional prime chains by one. -/
theorem ringKrullDim_sup_span_singleton_le_of_avoids_minimal {R : Type*} [CommRing R]
    {I M : Ideal R} (hM : M.IsMaximal) {s : ℕ} {f : R}
    (hdim : ringKrullDim (R ⧸ I) ≤ ((s+1 : ℕ) : WithBot ℕ∞))
    (havoid : ∀ P ∈ I.minimalPrimes, f ∈ P → P = M) :
    ringKrullDim (R ⧸ (I ⊔ Ideal.span {f})) ≤ (s : WithBot ℕ∞) := by
  classical
  rw [ringKrullDim_quotient] at hdim ⊢
  apply ENat.WithBot.lt_add_one_iff.mp
  rw [← Nat.cast_succ, Order.krullDim_lt_coe_iff]
  intro L
  let J := I ⊔ Ideal.span {f}
  have hj (x : PrimeSpectrum.zeroLocus (R := R) J) : J ≤ x.val.asIdeal := x.prop
  let e : PrimeSpectrum.zeroLocus (R := R) J → PrimeSpectrum.zeroLocus (R := R) I :=
    fun x => ⟨x.val, show I ≤ x.val.asIdeal from le_sup_left.trans (hj x)⟩
  have he : StrictMono e := fun _ _ h => h
  let L₀ := L.map e he
  let P := L.head.val.asIdeal
  let : P.IsPrime := L.head.val.isPrime
  have hPI : I ≤ P := (e L.head).prop
  have hf : f ∈ P := (le_sup_right.trans (hj L.head)) (Ideal.subset_span (Set.mem_singleton f))
  obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_minimalPrimes_le hPI
  by_cases hEq : Q = P
  · have hPM : P = M := hEq.symm.trans (havoid Q hQ (hEq ▸ hf))
    by_contra! hlen
    let i : Fin L.length := ⟨0, by omega⟩
    have hstep := L.step i
    have hc : L i.castSucc = L.head := rfl
    rw [hc] at hstep
    have hlt : P < (L i.succ).val.asIdeal := hstep
    rw [hPM] at hlt
    have H := hM.eq_of_le (L i.succ).val.isPrime.ne_top hlt.le
    exact hlt.ne H
  · let Q' : PrimeSpectrum.zeroLocus (R := R) I := ⟨⟨Q,hQ.1.1⟩,hQ.1.2⟩
    have hlt : Q' < L₀.head := lt_of_le_of_ne hQP
      (fun h => hEq (congrArg (fun x => x.val.asIdeal) h))
    let L₁ := L₀.cons Q' hlt
    have hdim' : Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) <
        ((s+2 : ℕ) : WithBot ℕ∞) := hdim.trans_lt (by exact_mod_cast (by omega : s+1 < s+2))
    have h := Order.krullDim_lt_coe_iff.mp hdim' L₁
    have hlen : L₁.length = L.length + 1 := by simp [L₁, L₀]
    rw [hlen] at h
    omega


noncomputable section

open scoped BigOperators

/-- The linear polynomial with the prescribed hyperplane normal. -/
def normalLinearForm {n : ℕ} {K : Type*} [CommRing K] (a : Fin n → K) :
    MvPolynomial (Fin n) K :=
  ∑ i, C (a i) * X i

@[simp] theorem eval_normalLinearForm {n : ℕ} {K : Type*} [CommRing K] (a x : Fin n → K) :
    (normalLinearForm a).eval x = ∑ i, a i * x i := by
  simp [normalLinearForm]

private def normalLinearFormMap (n : ℕ) (K : Type*) [Field K] :
    (Fin n → K) →ₗ[K] MvPolynomial (Fin n) K :=
  { toFun := normalLinearForm
    map_add' := by
      intro a b
      simp [normalLinearForm, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c a
      rw [normalLinearForm, normalLinearForm, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [smul_eq_C_mul, mul_assoc] }

private theorem normalLinearForm_single {n : ℕ} {K : Type*} [Field K] (i : Fin n) :
    normalLinearForm (Pi.single i (1 : K)) = X i := by
  classical
  rw [normalLinearForm, Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [Pi.single_eq_of_ne h]
  · simp

private theorem vanishingIdeal_origin_eq_idealOfVars {n : ℕ} (K : Type*) [Field K] :
    vanishingIdeal K ({0} : Set (Fin n → K)) = idealOfVars (Fin n) K := by
  ext f
  rw [mem_vanishingIdeal_singleton_iff, aeval_zero, Algebra.algebraMap_self, RingHom.id_apply,
    ← pow_one (idealOfVars (Fin n) K), mem_pow_idealOfVars_iff']
  change f.coeff 0 = 0 ↔ _
  constructor
  · intro h m hm
    have hm₀ : m.degree = 0 := by omega
    rw [Finsupp.degree_eq_zero_iff] at hm₀
    exact hm₀ ▸ h
  · intro h
    exact h 0 (by simp)

private theorem exists_normalAvoidancePolynomial {n : ℕ} {K : Type*} [Field K]
    (P : Ideal (MvPolynomial (Fin n) K)) (hP : P.IsPrime)
    (hP₀ : P ≠ vanishingIdeal K ({0} : Set (Fin n → K))) :
    ∃ T : MvPolynomial (Fin n) K, T ≠ 0 ∧
      ∀ a : Fin n → K, normalLinearForm a ∈ P → T.eval a = 0 := by
  classical
  let W := (P.restrictScalars K).comap (normalLinearFormMap n K)
  obtain ⟨i, hi⟩ : ∃ i : Fin n, X i ∉ P := by
    by_contra! h
    apply hP₀
    symm
    have hmax : (vanishingIdeal K ({0} : Set (Fin n → K))).IsMaximal := inferInstance
    refine hmax.eq_of_le hP.ne_top ?_
    rw [vanishingIdeal_origin_eq_idealOfVars]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact h j
  have hnot : Pi.single i (1 : K) ∉ W := by
    change normalLinearForm (Pi.single i (1 : K)) ∉ P
    rwa [normalLinearForm_single]
  obtain ⟨φ,hφ,hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  let T : MvPolynomial (Fin n) K := normalLinearForm fun j => φ (Pi.single j (1 : K))
  have heval (a : Fin n → K) : T.eval a = φ a := by
    have hrepr : ∑ j : Fin n, a j • Pi.single j (1 : K) = a := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, mul_ite]
    conv_rhs => rw [← hrepr]
    simp only [T, eval_normalLinearForm, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  refine ⟨T, ?_, ?_⟩
  · intro h
    apply hφ
    rw [← heval, h, map_zero]
  · intro a ha
    have hw : a ∈ W := ha
    have hφa : φ a ∈ W.map φ := Submodule.mem_map.mpr ⟨a,hw,rfl⟩
    rw [hW, Submodule.mem_bot] at hφa
    exact (heval a).trans hφa

/-- A generic hyperplane drops the Krull dimension by one. Its normal
may also be chosen away from the zero set of a prescribed nonzero polynomial
and within any chosen projective coordinate chart. -/
theorem exists_normalLinearForm_dim_drop {n s : ℕ} {K : Type*} [Field K] [Infinite K]
    (i₀ : Fin n) (I : Ideal (MvPolynomial (Fin n) K)) {T : MvPolynomial (Fin n) K}
    (hT : T ≠ 0)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ I) ≤ ((s+1 : ℕ) : WithBot ℕ∞)) :
    ∃ a : Fin n → K, a i₀ ≠ 0 ∧ T.eval a ≠ 0 ∧
      ringKrullDim (MvPolynomial (Fin n) K ⧸ (I ⊔ Ideal.span {normalLinearForm a})) ≤
        (s : WithBot ℕ∞) := by
  classical
  let M : Ideal (MvPolynomial (Fin n) K) := vanishingIdeal K ({0} : Set (Fin n → K))
  let S := {P : Ideal (MvPolynomial (Fin n) K) | P ∈ I.minimalPrimes ∧ P ≠ M}
  let : Fintype S :=
    (I.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) |>.subset
      (fun _ hp => hp.1)).fintype
  choose V hV hsep using fun P : S =>
    exists_normalAvoidancePolynomial P.val P.prop.1.1.1 P.prop.2
  let B := T * X i₀ * ∏ P : S, V P
  have hB : B ≠ 0 :=
    mul_ne_zero (mul_ne_zero hT (X_ne_zero i₀))
      (Finset.prod_ne_zero_iff.mpr (fun P _ => hV P))
  obtain ⟨a,ha⟩ : ∃ a : Fin n → K, B.eval a ≠ 0 := by
    by_contra! h
    exact hB (MvPolynomial.funext (fun x => by simpa only [map_zero] using h x))
  simp only [B, map_mul, eval_X, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at ha
  refine ⟨a, ha.1.2, ha.1.1, ?_⟩
  apply ringKrullDim_sup_span_singleton_le_of_avoids_minimal (M := M) inferInstance hdim
  intro P hp hP
  by_contra hPM
  let P' : S := ⟨P,hp,hPM⟩
  exact ha.2 P' (Finset.mem_univ _) (hsep P' a hP)

end
end Birch
