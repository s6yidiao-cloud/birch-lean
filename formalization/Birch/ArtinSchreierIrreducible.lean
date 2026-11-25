import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic

/-! # Irreducibility for Artin–Schreier curves of prime-to-characteristic degree -/

open Polynomial

namespace Birch

noncomputable section

/-- The defining polynomial of an Artin–Schreier extension. -/
def artinSchreierPolynomial {K : Type*} [Ring K] (p : ℕ) (c : K) : K[X] :=
  X^p - (X + C c)

theorem monic_artinSchreierPolynomial {K : Type*} [Ring K] [Nontrivial K] {p : ℕ} (hp : 1 < p) (c : K) :
    (artinSchreierPolynomial p c).Monic := by
  apply monic_X_pow_sub
  rw [degree_X_add_C]
  exact_mod_cast hp

theorem natDegree_artinSchreierPolynomial {K : Type*} [Field K] {p : ℕ} (hp : 1 < p) (c : K) :
    (artinSchreierPolynomial p c).natDegree = p := by
  unfold artinSchreierPolynomial
  rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_add_C, natDegree_X_pow]
  exact hp

private theorem eval₂_artinSchreierPolynomial {K E : Type*} [Field K] [Field E]
    (p : ℕ) (c : K) (φ : K →+* E) (y : E) :
    (artinSchreierPolynomial p c).eval₂ φ y = y^p - y - φ c := by
  simp only [artinSchreierPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_add, eval₂_C]
  ring

private theorem exists_map_eq_artinSchreier_root_difference
    {K E : Type*} [Field K] [Field E] {p : ℕ} [Fact p.Prime] [CharP E p]
    (φ : K →+* E) {c : E} {x y : E} (hx : x^p-x = c) (hy : y^p-y = c) :
    ∃ z : K, φ z = x-y := by
  have h : (x-y)^p = x-y := by
    rw [sub_pow_char]
    linear_combination hx - hy
  have hz := (Subfield.mem_bot_iff_pow_eq_self E p).mpr h
  exact (bot_le : (⊥ : Subfield E) ≤ φ.fieldRange) hz

/-- Over a field of characteristic p, an Artin–Schreier polynomial with
no root in the field is irreducible. A proper monic factor would express a
root over the base field by averaging its root multiset. -/
theorem irreducible_artinSchreierPolynomial_of_no_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) (hn : ∀ y : K, y^p-y ≠ c) : Irreducible (artinSchreierPolynomial p c) := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  let A := artinSchreierPolynomial p c
  have hA := monic_artinSchreierPolynomial hp c
  have hAd : A.natDegree = p := natDegree_artinSchreierPolynomial hp c
  have hAnu : ¬ IsUnit A := not_isUnit_of_natDegree_pos A (hAd.symm ▸ zero_lt_one.trans hp)
  apply (irreducible_iff_lt_natDegree_lt hA.ne_zero hAnu).mpr
  intro Q hQ hD hdiv
  obtain ⟨hQpos,hQle⟩ := Finset.mem_Ioc.mp hD
  have hd : Q.natDegree < p := by
    change Q.natDegree ≤ A.natDegree / 2 at hQle
    omega
  let E := AlgebraicClosure K
  let φ := algebraMap K E
  have hQ' : (Q.map φ).Monic := hQ.map φ
  let s := (Q.map φ).roots
  have hs : s.card = Q.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree.trans (natDegree_map_eq_of_injective φ.injective Q)
  have hspos : 0 < s.card := hs ▸ hQpos
  obtain ⟨y,hy⟩ := Multiset.card_pos_iff_exists_mem.mp hspos
  have hroot (z : E) (hz : z ∈ s) : z^p-z = φ c := by
    have hr : IsRoot (Q.map φ) z := (mem_roots hQ'.ne_zero).mp hz
    have hf := dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hr).trans
      ((map_dvd_map' φ).mpr hdiv))
    change (A.map φ).eval z = 0 at hf
    rw [eval_map, eval₂_artinSchreierPolynomial, sub_eq_zero] at hf
    exact hf
  have hdiff (z : E) (hz : z ∈ s) : (z-y) ∈ φ.fieldRange :=
    exists_map_eq_artinSchreier_root_difference φ (hroot z hz) (hroot y hy)
  have hsumDiff : (s.map (fun z => z-y)).sum ∈ φ.fieldRange := by
    apply φ.fieldRange.multiset_sum_mem
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hz
    exact hdiff x hx
  obtain ⟨b,hb⟩ := hsumDiff
  have hsum : φ (-Q.nextCoeff) = s.sum := by
    rw [map_neg, ← nextCoeff_map φ.injective Q,
      (IsAlgClosed.splits (Q.map φ)).nextCoeff_eq_neg_sum_roots_of_monic hQ', neg_neg]
  have hd₀ : (Q.natDegree : E) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt hQpos hd) ((CharP.cast_eq_zero_iff E p _).mp h)
  let z := ((-Q.nextCoeff) - b) / (Q.natDegree : K)
  have hzφ : φ z = y := by
    dsimp only [z]
    rw [map_div₀, map_sub, hsum, hb, map_natCast, Multiset.sum_map_sub]
    simp only [Multiset.map_id', sub_sub_cancel, Multiset.map_const', Multiset.sum_replicate, hs, nsmul_eq_mul]
    exact mul_div_cancel_left₀ y hd₀
  apply hn z
  apply φ.injective
  rw [map_sub, map_pow, hzφ]
  exact hroot y hy

private theorem ratFunc_intDegree_pow {K : Type*} [Field K] {y : RatFunc K}
    (hy : y ≠ 0) (k : ℕ) : (y^k).intDegree = (k : ℤ) * y.intDegree := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero k hy) hy, ih, Nat.cast_succ, add_mul, one_mul]

/-- The pole order at infinity of an Artin–Schreier difference, if positive,
is a multiple of p. Hence a positive-degree polynomial of degree prime to p
cannot be such a difference in the rational function field. -/
theorem ratFunc_artinSchreier_ne_polynomial_of_not_dvd_degree
    {K : Type*} [Field K] {p : ℕ} (hp : 1 < p)
    (f : K[X]) (hd₀ : 0 < f.natDegree) (hd : ¬ p ∣ f.natDegree) (y : RatFunc K) :
    y^p - y ≠ algebraMap K[X] (RatFunc K) f := by
  let F := algebraMap K[X] (RatFunc K) f
  have hfPos : 0 < F.intDegree := by
    rw [RatFunc.intDegree_polynomial]
    exact_mod_cast hd₀
  have hf₀ : F ≠ 0 := by intro h; simp [h] at hfPos
  intro he
  change y^p - y = F at he
  have hy : y ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : p ≠ 0), sub_zero] at he
    exact hf₀ he.symm
  have hpdeg := ratFunc_intDegree_pow hy p
  have hdeg : F.intDegree ≤ max ((p : ℤ) * y.intDegree) y.intDegree := by
    have hn : y^p + (-y) ≠ 0 := by rw [← sub_eq_add_neg, he]; exact hf₀
    have h := RatFunc.intDegree_add_le (neg_ne_zero.mpr hy) hn
    rw [← sub_eq_add_neg, he, hpdeg, RatFunc.intDegree_neg] at h
    exact h
  have hyPos : 0 < y.intDegree := by
    by_contra! h
    have hp₀ : 0 ≤ (p : ℤ) := Nat.cast_nonneg p
    have hpd : (p : ℤ) * y.intDegree ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp₀ h
    exact (not_lt_of_ge (hdeg.trans (max_le hpd h))) hfPos
  have hyLt : y.intDegree < (p : ℤ) * y.intDegree := by
    have hpow : (1 : ℤ) < p := by exact_mod_cast hp
    simpa only [one_mul] using mul_lt_mul_of_pos_right hpow hyPos
  have hf_le : F.intDegree ≤ (p : ℤ) * y.intDegree := hdeg.trans_eq (max_eq_left hyLt.le)
  have hback : F + y = y^p := by rw [← he, sub_add_cancel]
  have hback₀ : F + y ≠ 0 := hback.symm ▸ pow_ne_zero p hy
  have hle := RatFunc.intDegree_add_le hy hback₀
  rw [hback, hpdeg] at hle
  have hdiv : F.intDegree = (p : ℤ) * y.intDegree := le_antisymm hf_le
    ((le_max_iff.mp hle).resolve_right (not_le_of_gt hyLt))
  rw [RatFunc.intDegree_polynomial] at hdiv
  apply hd
  exact Int.natCast_dvd_natCast.mp ⟨y.intDegree, hdiv⟩

/-- The Artin–Schreier polynomial over the rational function field is
irreducible for any positive degree prime to the characteristic. -/
theorem irreducible_artinSchreierPolynomial_ratFunc
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) (hd₀ : 0 < f.natDegree) (hd : ¬ p ∣ f.natDegree) :
    Irreducible (artinSchreierPolynomial p (algebraMap K[X] (RatFunc K) f)) :=
  irreducible_artinSchreierPolynomial_of_no_root _
    (ratFunc_artinSchreier_ne_polynomial_of_not_dvd_degree (Fact.out : p.Prime).one_lt f hd₀ hd)

/-- The affine Artin–Schreier equation is already irreducible over the
polynomial coefficient ring; its rational function extension detects this
because it is monic in the Artin–Schreier variable. -/
theorem irreducible_artinSchreierPolynomial_over_polynomial
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) (hd₀ : 0 < f.natDegree) (hd : ¬ p ∣ f.natDegree) :
    Irreducible (artinSchreierPolynomial p f) := by
  let φ := algebraMap K[X] (RatFunc K)
  apply Monic.irreducible_of_irreducible_map φ _
    (monic_artinSchreierPolynomial (Fact.out : p.Prime).one_lt f)
  have h := irreducible_artinSchreierPolynomial_ratFunc f hd₀ hd
  simpa only [artinSchreierPolynomial, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_add, Polynomial.map_C] using h

/-- The affine coordinate ring of the Artin–Schreier curve is a domain.
The result holds over algebraic closures as well, with the same degree. -/
theorem isDomain_artinSchreierAffineRing
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) (hd₀ : 0 < f.natDegree) (hd : ¬ p ∣ f.natDegree) :
    IsDomain (AdjoinRoot (artinSchreierPolynomial p f)) :=
  AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_artinSchreierPolynomial_over_polynomial f hd₀ hd))

private def binaryCoordinateEquiv : Bool ≃ Option PUnit where
  toFun b := if b then none else some ()
  invFun a := a.isNone
  left_inv b := by cases b <;> rfl
  right_inv a := by cases a with
    | none => rfl
    | some u => cases u; rfl

/-- Identify the two variables of an affine Artin–Schreier curve with the
coefficient variable x and the outer variable y in the polynomial ring. -/
def artinSchreierBinaryCoordinateEquiv (K : Type*) [Field K] :
    MvPolynomial Bool K ≃ₐ[K] (K[X])[X] :=
  (MvPolynomial.renameEquiv K binaryCoordinateEquiv).trans
    ((MvPolynomial.optionEquivLeft K PUnit).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K PUnit)))

/-- The defining equation in the two affine coordinates is irreducible
over any coefficient field of the indicated characteristic. -/
theorem irreducible_artinSchreierBinaryPolynomial
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) (hd₀ : 0 < f.natDegree) (hd : ¬ p ∣ f.natDegree) :
    Irreducible (MvPolynomial.X true ^ p - MvPolynomial.X true - Polynomial.toMvPolynomial false f) := by
  let e := artinSchreierBinaryCoordinateEquiv K
  have htrue : e (MvPolynomial.X true) = Polynomial.X := by
    simp [e, artinSchreierBinaryCoordinateEquiv, binaryCoordinateEquiv]
  have hfalse : e (MvPolynomial.X false) = Polynomial.C Polynomial.X := by
    simp [e, artinSchreierBinaryCoordinateEquiv, binaryCoordinateEquiv]
  have hcomp : e.toAlgHom.comp (Polynomial.toMvPolynomial (R := K) false) =
      (Polynomial.CAlgHom : K[X] →ₐ[K] (K[X])[X]) :=
    Polynomial.algHom_ext (by simp [Polynomial.toMvPolynomial, hfalse])
  have hf : e (Polynomial.toMvPolynomial false f) = Polynomial.C f :=
    DFunLike.congr_fun hcomp f
  apply (MulEquiv.irreducible_iff e).mp
  rw [map_sub, map_sub, map_pow, htrue, hf, sub_sub]
  exact irreducible_artinSchreierPolynomial_over_polynomial f hd₀ hd

/-- The affine coordinate scheme's ring is a domain in the geometric
coordinates used to count its field-valued points. -/
theorem isDomain_artinSchreierBinaryQuotient
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (f : K[X]) (hd₀ : 0 < f.natDegree) (hd : ¬ p ∣ f.natDegree) :
    IsDomain (MvPolynomial Bool K ⧸ Ideal.span
      {MvPolynomial.X true ^ p - MvPolynomial.X true - Polynomial.toMvPolynomial false f}) := by
  have h := irreducible_artinSchreierBinaryPolynomial (p := p) f hd₀ hd
  let := (Ideal.span_singleton_prime h.ne_zero).mpr (UniqueFactorizationMonoid.irreducible_iff_prime.mp h)
  infer_instance

end

end Birch
