import Birch.PowerSumRank
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.List.OfFn
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-!
# Polynomiality of one-variable additive-character L-series

The coefficient construction uses Newton's identities for the phase evaluated
at the roots of monic polynomials. Varying one coefficient gives additive
orthogonality in degrees at or above the phase degree. The relation with the
Artin–Schreier curve numerator is the Euler product step of Kowalski,
*Exponential sums over finite fields, I*, §5.3.
-/

open Filter Finset Polynomial
open scoped Topology

namespace Birch

noncomputable section

private theorem multiset_powerSum_newton {K : Type*} [CommRing K] (s : Multiset K)
    {k : ℕ} (hk : 0 < k) :
    (s.map (fun x => x ^ k)).sum =
      (-1 : K) ^ (k + 1) * k * s.esymm k -
        ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
          (-1 : K) ^ a.1 * s.esymm a.1 * (s.map (fun x => x ^ a.2)).sum := by
  classical
  refine Quotient.inductionOn s (fun l => ?_)
  let y : Fin l.length → K := l.get
  have hs : (Finset.univ : Finset (Fin l.length)).val.map y = (l : Multiset K) := by
    rw [Fin.univ_val_map, List.ofFn_get l]
  have h := congrArg (MvPolynomial.aeval y)
    (MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin l.length) K k hk)
  simp only [map_sub, map_mul, map_pow, map_neg, map_one, map_natCast, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Set.mem_Ioo] at h
  have hpower (j : ℕ) : MvPolynomial.aeval y (MvPolynomial.psum (Fin l.length) K j) =
      ((l : Multiset K).map (fun x => x ^ j)).sum := by
    rw [← hs, Multiset.map_map]
    rw [MvPolynomial.psum, map_sum]
    simp only [map_pow, MvPolynomial.aeval_X, Finset.sum_eq_multiset_sum, Function.comp_apply]
  change (Multiset.map (fun x => x ^ k) (l : Multiset K)).sum =
    (-1 : K) ^ (k + 1) * k * (l : Multiset K).esymm k -
      ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
        (-1 : K) ^ a.1 * (l : Multiset K).esymm a.1 *
          ((l : Multiset K).map (fun x => x ^ a.2)).sum
  simpa only [hpower, hs] using h

/-- The coefficient indexed from the leading term of a monic polynomial. -/
def descendingCoeff {K : Type*} [Semiring K] (P : K[X]) (i : ℕ) : K :=
  if i ≤ P.natDegree then P.coeff (P.natDegree - i) else 0

/-- Newton sums computed from the coefficients, including the degree as the power sum at zero. -/
def newtonPowerSum {K : Type*} [CommRing K] (P : K[X]) (k : ℕ) : K :=
  if 0 < k then
    -(k : K) * descendingCoeff P k -
      ∑ a ∈ ((antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k)).attach,
        descendingCoeff P a.1.1 * newtonPowerSum P a.1.2
  else P.natDegree
termination_by k
decreasing_by
  have ha := Finset.mem_filter.mp a.2
  have h := mem_antidiagonal.mp ha.1
  omega

private theorem newtonPowerSum_pos {K : Type*} [CommRing K] (P : K[X])
    {k : ℕ} (hk : 0 < k) :
    newtonPowerSum P k = -(k : K) * descendingCoeff P k -
      ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
        descendingCoeff P a.1 * newtonPowerSum P a.2 := by
  rw [newtonPowerSum, ite_eq_left hk]
  congr 1
  exact Finset.sum_attach _ (fun a : ℕ × ℕ => descendingCoeff P a.1 * newtonPowerSum P a.2)

private theorem newtonPowerSum_zero {K : Type*} [CommRing K] (P : K[X]) :
    newtonPowerSum P 0 = P.natDegree := by
  rw [newtonPowerSum]
  simp

private theorem newtonPowerSum_sub_of_coeff_eq {K : Type*} [CommRing K] {P Q : K[X]}
    (hdeg : P.natDegree = Q.natDegree) (k : ℕ)
    (hc : ∀ i < k, descendingCoeff P i = descendingCoeff Q i) :
    newtonPowerSum P k - newtonPowerSum Q k =
      -(k : K) * (descendingCoeff P k - descendingCoeff Q k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : 0 < k
    · rw [newtonPowerSum_pos P hk, newtonPowerSum_pos Q hk]
      have hsum :
          ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
            descendingCoeff P a.1 * newtonPowerSum P a.2 =
          ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
            descendingCoeff Q a.1 * newtonPowerSum Q a.2 := by
        apply Finset.sum_congr rfl
        intro a ha
        obtain ⟨had, hp, hlt⟩ := mem_filter.mp ha
        have hs := mem_antidiagonal.mp had
        have ha2 : a.2 < k := by omega
        have he := ih a.2 ha2 (fun i hi => hc i (hi.trans ha2))
        rw [hc a.2 ha2, sub_self, mul_zero] at he
        rw [hc a.1 hlt, sub_eq_zero.mp he]
      rw [hsum]
      ring
    · have h0 : k = 0 := by omega
      subst k
      simp [newtonPowerSum_zero, hdeg]

private theorem descendingCoeff_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (P : K[X]) (i : ℕ) :
    descendingCoeff (P.map φ) i = φ (descendingCoeff P i) := by
  simp only [descendingCoeff, natDegree_map_eq_of_injective φ.injective]
  split_ifs with hi <;> simp

private theorem newtonPowerSum_map {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (P : K[X]) (i : ℕ) :
    newtonPowerSum (P.map φ) i = φ (newtonPowerSum P i) := by
  induction i using Nat.strong_induction_on with
  | h i hi =>
    rcases i.eq_zero_or_pos with rfl | hpos
    · simp [newtonPowerSum_zero, natDegree_map_eq_of_injective φ.injective]
    · rw [newtonPowerSum_pos _ hpos, newtonPowerSum_pos _ hpos, map_sub, map_mul, map_neg,
        map_natCast, descendingCoeff_map, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨had, ha₁, _⟩ := mem_filter.mp ha
      have hs := mem_antidiagonal.mp had
      rw [descendingCoeff_map, map_mul, hi a.2 (by omega)]

private theorem descendingCoeff_eq_esymm_roots {K : Type*} [Field K] [IsAlgClosed K]
    {P : K[X]} (hP : P.Monic) (i : ℕ) :
    descendingCoeff P i = (-1 : K)^i * P.roots.esymm i := by
  have hcard : P.roots.card = P.natDegree := IsAlgClosed.card_roots_eq_natDegree
  by_cases hi : i ≤ P.natDegree
  · rw [descendingCoeff, ite_eq_left hi, coeff_eq_esymm_roots_of_card hcard (Nat.sub_le ..),
      Nat.sub_sub_self hi, hP.leadingCoeff, one_mul]
  · rw [descendingCoeff, ite_eq_right hi, Multiset.esymm, Multiset.powersetCard_eq_empty i
      (hcard.symm ▸ Nat.lt_of_not_ge hi)]
    simp

/-- Newton sums over an algebraically closed field are the power sums of the roots,
counted with multiplicity. -/
theorem newtonPowerSum_eq_roots {K : Type*} [Field K] [IsAlgClosed K]
    {P : K[X]} (hP : P.Monic) (i : ℕ) :
    newtonPowerSum P i = (P.roots.map (fun x => x^i)).sum := by
  induction i using Nat.strong_induction_on with
  | h i hi =>
    rcases i.eq_zero_or_pos with rfl | hpos
    · simp [newtonPowerSum_zero, IsAlgClosed.card_roots_eq_natDegree]
    · rw [newtonPowerSum_pos _ hpos, multiset_powerSum_newton P.roots hpos,
        descendingCoeff_eq_esymm_roots hP i]
      have hsum :
          ∑ a ∈ (antidiagonal i).filter (fun a => 0 < a.1 ∧ a.1 < i),
            descendingCoeff P a.1 * newtonPowerSum P a.2 =
          ∑ a ∈ (antidiagonal i).filter (fun a => 0 < a.1 ∧ a.1 < i),
            (-1 : K) ^ a.1 * P.roots.esymm a.1 * (P.roots.map (fun x => x ^ a.2)).sum := by
        apply Finset.sum_congr rfl
        intro a ha
        obtain ⟨had, ha₁, _⟩ := mem_filter.mp ha
        have hs := mem_antidiagonal.mp had
        rw [descendingCoeff_eq_esymm_roots hP, hi a.2 (by omega)]
      rw [hsum, pow_succ]
      ring

/-- The sum of the values of a phase on the roots, computed over the
coefficient ring using Newton's identities. -/
def polynomialRootPhase {K : Type*} [CommRing K] (f P : K[X]) : K :=
  ∑ i ∈ range (f.natDegree + 1), f.coeff i * newtonPowerSum P i

private theorem multiset_sum_map_finset_sum {α β K : Type*} [AddCommMonoid K]
    (s : Multiset α) (t : Finset β) (f : α → β → K) :
    (s.map fun a => ∑ b ∈ t, f a b).sum = ∑ b ∈ t, (s.map (fun a => f a b)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih, Finset.sum_add_distrib]

/-- The phase is the sum of the values at the geometric roots of the monic
polynomial, with multiplicity. The value descends to the base field. -/
theorem map_polynomialRootPhase_eq_sum_roots {K L : Type*} [Field K] [Field L] [IsAlgClosed L]
    (φ : K →+* L) (f : K[X]) {P : K[X]} (hP : P.Monic) :
    φ (polynomialRootPhase f P) = ((P.map φ).roots.map (f.eval₂ φ)).sum := by
  simp only [polynomialRootPhase, map_sum, map_mul, ← newtonPowerSum_map φ P,
    newtonPowerSum_eq_roots (hP.map φ)]
  simp_rw [Polynomial.eval₂_eq_sum_range]
  rw [multiset_sum_map_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Multiset.sum_map_mul_left]

/-- Disjoint union of the root multisets makes the root phase additive
under multiplication of monic polynomials. -/
theorem polynomialRootPhase_mul {K : Type*} [Field K] (f : K[X]) {P Q : K[X]}
    (hP : P.Monic) (hQ : Q.Monic) :
    polynomialRootPhase f (P * Q) = polynomialRootPhase f P + polynomialRootPhase f Q := by
  let φ := algebraMap K (AlgebraicClosure K)
  apply φ.injective
  rw [map_add, map_polynomialRootPhase_eq_sum_roots φ f (hP.mul hQ),
    map_polynomialRootPhase_eq_sum_roots φ f hP, map_polynomialRootPhase_eq_sum_roots φ f hQ,
    Polynomial.map_mul, roots_mul ((hP.map φ).mul (hQ.map φ)).ne_zero,
    Multiset.map_add, Multiset.sum_add]

/-- A linear monic polynomial has the phase value of its single root. -/
theorem polynomialRootPhase_X_sub_C {K : Type*} [Field K] (f : K[X]) (x : K) :
    polynomialRootPhase f (X-C x) = f.eval x := by
  let φ := algebraMap K (AlgebraicClosure K)
  apply φ.injective
  rw [map_polynomialRootPhase_eq_sum_roots φ f (monic_X_sub_C x),
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, roots_X_sub_C]
  simp

private theorem polynomialRootPhase_sub_of_coeff_eq {K : Type*} [CommRing K] {f P Q : K[X]}
    (r : ℕ) (hr : f.natDegree = r) (hdeg : P.natDegree = Q.natDegree)
    (hc : ∀ i < r, descendingCoeff P i = descendingCoeff Q i) :
    polynomialRootPhase f P - polynomialRootPhase f Q =
      (-(r : K) * f.coeff r) * (descendingCoeff P r - descendingCoeff Q r) := by
  rw [polynomialRootPhase, polynomialRootPhase, hr, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single r]
  · rw [← mul_sub, newtonPowerSum_sub_of_coeff_eq hdeg r hc]
    ring
  · intro i hi hir
    have hil : i < r := by have := mem_range.mp hi; omega
    rw [← mul_sub, newtonPowerSum_sub_of_coeff_eq hdeg i (fun j hj => hc j (hj.trans hil)),
      hc i hil, sub_self, mul_zero, mul_zero]
  · simp

/-- The monic polynomial with a specified vector of lower coefficients. -/
def monicWithCoefficients {K : Type*} [Field K] [DecidableEq K] {n : ℕ}
    (c : Fin n → K) : K[X] := Polynomial.ofFn n c + X ^ n

private theorem monicWithCoefficients_mem {K : Type*} [Field K] [DecidableEq K]
    {n : ℕ} (c : Fin n → K) : (monicWithCoefficients c).coeff n = 1 ∧
    ∀ i > n, (monicWithCoefficients c).coeff i = 0 := by
  refine ⟨by simp [monicWithCoefficients], fun i hi => ?_⟩
  have hne : n ≠ i := Nat.ne_of_lt hi
  simp [monicWithCoefficients, hi.le, Ne.symm hne]

theorem monicWithCoefficients_monic {K : Type*} [Field K] [DecidableEq K]
    {n : ℕ} (c : Fin n → K) : (monicWithCoefficients c).Monic :=
  (show MonicDegreeEq K n from ⟨monicWithCoefficients c, monicWithCoefficients_mem c⟩).monic

theorem monicWithCoefficients_natDegree {K : Type*} [Field K] [DecidableEq K]
    {n : ℕ} (c : Fin n → K) : (monicWithCoefficients c).natDegree = n :=
  (show MonicDegreeEq K n from ⟨monicWithCoefficients c, monicWithCoefficients_mem c⟩).natDegree

private theorem coeff_monicWithCoefficients {K : Type*} [Field K] [DecidableEq K]
    {n k : ℕ} (c : Fin n → K) (hk : k < n) :
    (monicWithCoefficients c).coeff k = c ⟨k, hk⟩ := by
  simp [monicWithCoefficients, hk, hk.ne]

private theorem descendingCoeff_monicWithCoefficients {K : Type*} [Field K] [DecidableEq K]
    {n k : ℕ} (c : Fin n → K) (hk : 0 < k) (hkn : k ≤ n) :
    descendingCoeff (monicWithCoefficients c) k = c ⟨n - k, by omega⟩ := by
  rw [descendingCoeff, monicWithCoefficients_natDegree, ite_eq_left hkn,
    coeff_monicWithCoefficients]

/-- Coefficient vectors enumerate the monic polynomials of a fixed degree. -/
def monicWithCoefficientsEquiv {K : Type*} [Field K] [DecidableEq K]
    (n : ℕ) : (Fin n → K) ≃ MonicDegreeEq K n where
  toFun c := ⟨monicWithCoefficients c, monicWithCoefficients_mem c⟩
  invFun P i := P.1.coeff i
  left_inv c := funext fun i => coeff_monicWithCoefficients c i.isLt
  right_inv P := by
    apply Subtype.ext
    apply Polynomial.ext
    intro j
    by_cases hj : j < n
    · exact coeff_monicWithCoefficients _ hj
    · have hk : n ≤ j := by omega
      let Q : MonicDegreeEq K n := ⟨_, monicWithCoefficients_mem (fun i => P.1.coeff i)⟩
      exact (Q.coeff_of_ge _ hk).trans (P.coeff_of_ge _ hk).symm

/-- Phase weights of monic polynomials of a given degree. -/
def additiveLSeriesCoeff {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (a : ZMod p) (n : ℕ) : ℂ :=
  ∑ c : Fin n → ZMod p, ZMod.stdAddChar (a * polynomialRootPhase f (monicWithCoefficients c))

/-- The coefficient vanishes in each degree at or above the phase degree.
This is the cancellation giving polynomiality of the additive L-series. -/
theorem additiveLSeriesCoeff_eq_zero_of_degree_le {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) {a : ZMod p} (ha : a ≠ 0)
    (hr : 0 < f.natDegree) (hp : f.natDegree < p) {n : ℕ} (hn : f.natDegree ≤ n) :
    additiveLSeriesCoeff f a n = 0 := by
  classical
  let r := f.natDegree
  let i : Fin n := ⟨n-r, by omega⟩
  let E := Equiv.piSplitAt i (fun _ => ZMod p)
  have hf₀ : f ≠ 0 := by intro h; simp [h] at hr
  have hr₀ : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hr hp
  let slope := -(r : ZMod p) * f.coeff r
  have hslope : slope ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hr₀)
    (leadingCoeff_ne_zero.mpr hf₀)
  have hphase (b : (j : {j : Fin n // j ≠ i}) → ZMod p) (t : ZMod p) :
      polynomialRootPhase f (monicWithCoefficients (E.symm (t,b))) =
        slope * t + polynomialRootPhase f (monicWithCoefficients (E.symm (0,b))) := by
    have h := polynomialRootPhase_sub_of_coeff_eq r rfl
      (show (monicWithCoefficients (E.symm (t,b))).natDegree =
        (monicWithCoefficients (E.symm (0,b))).natDegree by simp [monicWithCoefficients_natDegree])
       (fun j hj => ?_)
    · rw [descendingCoeff_monicWithCoefficients _ hr hn,
        descendingCoeff_monicWithCoefficients _ hr hn] at h
      have ht : (E.symm (t,b)) i = t := by simp [E, Equiv.piSplitAt]
      have hzero : (E.symm (0,b)) i = 0 := by simp [E, Equiv.piSplitAt]
      change _ - _ = slope * ((E.symm (t,b)) i - (E.symm (0,b)) i) at h
      rw [ht, hzero, sub_zero] at h
      exact eq_add_of_sub_eq h
    · by_cases hj0 : j = 0
      · subst j
        simp [descendingCoeff, monicWithCoefficients_natDegree, monicWithCoefficients_mem]
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hneq : (⟨n-j, by omega⟩ : Fin n) ≠ i := by
          intro h
          have he := congrArg Fin.val h
          change n-j = n-r at he
          omega
        rw [descendingCoeff_monicWithCoefficients _ hjpos (hj.le.trans hn),
          descendingCoeff_monicWithCoefficients _ hjpos (hj.le.trans hn)]
        simp [E, Equiv.piSplitAt, hneq]
  unfold additiveLSeriesCoeff
  rw [← E.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  calc
    _ = ∑ t : ZMod p, ZMod.stdAddChar ((a * slope) * t) *
        ZMod.stdAddChar (a * polynomialRootPhase f (monicWithCoefficients (E.symm (0,b)))) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hphase, mul_add, AddChar.map_add_eq_mul, ← mul_assoc]
    _ = 0 := by
      rw [← Finset.sum_mul, show (∑ t : ZMod p, ZMod.stdAddChar ((a * slope) * t)) = 0 from
        AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p (mul_ne_zero ha hslope)),
        zero_mul]

/-- Coefficient series of the one-variable additive-character L-function. -/
def additiveLSeries {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (a : ZMod p) : PowerSeries ℂ :=
  PowerSeries.mk (additiveLSeriesCoeff f a)

/-- The degree-zero coefficient of the additive-character series is one. -/
theorem constantCoeff_additiveLSeries {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (a : ZMod p) : PowerSeries.constantCoeff (additiveLSeries f a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, additiveLSeries, PowerSeries.coeff_mk]
  have hphase : polynomialRootPhase f 1 = 0 := by
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    apply φ.injective
    rw [map_polynomialRootPhase_eq_sum_roots φ f monic_one]
    simp
  simp [additiveLSeriesCoeff, monicWithCoefficients, hphase]

/-- The coefficient of T is the prime-field additive-character sum. -/
theorem coeff_one_additiveLSeries {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (a : ZMod p) :
    PowerSeries.coeff 1 (additiveLSeries f a) = ∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x) := by
  rw [additiveLSeries, PowerSeries.coeff_mk, additiveLSeriesCoeff]
  let E : (Fin 1 → ZMod p) ≃ ZMod p := (Equiv.funUnique (Fin 1) (ZMod p)).trans (Equiv.neg _)
  rw [← E.sum_comp]
  apply Finset.sum_congr rfl
  intro c _
  have hc : monicWithCoefficients c = X - C (E c) := by
    simp [monicWithCoefficients, Polynomial.ofFn_eq_sum_monomial, E, sub_eq_add_neg, add_comm]
  rw [hc, polynomialRootPhase_X_sub_C]

/-- The one-variable additive-character L-series is a polynomial of degree
at most one less than the degree of its phase. -/
theorem additiveLSeries_isPolynomial {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) {a : ZMod p} (ha : a ≠ 0)
    (hr : 0 < f.natDegree) (hp : f.natDegree < p) :
    ∃ L : ℂ[X], L.natDegree ≤ f.natDegree - 1 ∧ (L : PowerSeries ℂ) = additiveLSeries f a := by
  refine ⟨∑ i ∈ range f.natDegree, monomial i (additiveLSeriesCoeff f a i), ?_, ?_⟩
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      show ¬ j < f.natDegree by omega]
  · ext j
    rw [Polynomial.coeff_coe, additiveLSeries, PowerSeries.coeff_mk,
      Polynomial.finsetSum_coeff]
    by_cases hj : j ∈ range f.natDegree
    · rw [Finset.sum_eq_single_of_mem j hj]
      · simp
      · exact fun i _ hi => by simp [Polynomial.coeff_monomial, hi]
    · have hn : f.natDegree ≤ j := Nat.le_of_not_gt (fun h => hj (mem_range.mpr h))
      rw [additiveLSeriesCoeff_eq_zero_of_degree_le f ha hr hp hn]
      apply Finset.sum_eq_zero
      intro i hi
      have hne : i ≠ j := fun h => hj (h ▸ hi)
      simp [Polynomial.coeff_monomial, hne]


/-- The first coefficient of a polynomial with constant coefficient one
is bounded by its degree times a bound on the modulus of reciprocal roots. -/
theorem norm_coeff_one_le_of_reciprocal_roots {L W : ℂ[X]} (hL : L.coeff 0 = 1)
    (hW : W ≠ 0) (hdiv : L ∣ W) {B : ℝ} (hB : ∀ z ∈ W.reverse.roots, ‖z‖ ≤ B) :
    ‖L.coeff 1‖ ≤ (L.natDegree : ℝ) * B := by
  have hL₀ : L.coeff 0 ≠ 0 := hL.symm ▸ one_ne_zero
  have ht : L.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hL₀)
  have hd : L.reverse.natDegree = L.natDegree := by simp [reverse_natDegree, ht]
  have hm : L.reverse.Monic := by
    rw [Monic, reverse_leadingCoeff, trailingCoeff, ht, hL]
  have hrevdiv : L.reverse ∣ W.reverse := by
    obtain ⟨Q, hQ⟩ := hdiv
    exact ⟨Q.reverse, hQ ▸ reverse_mul_of_domain L Q⟩
  have hWrev : W.reverse ≠ 0 := fun h => hW (reverse_eq_zero.mp h)
  have hroot (z : ℂ) (hz : z ∈ L.reverse.roots) : ‖z‖ ≤ B :=
    hB z ((mem_roots hWrev).mpr
      (dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr ((mem_roots hm.ne_zero).mp hz)).trans hrevdiv)))
  have hsum : ‖L.reverse.roots.sum‖ ≤ (L.reverse.roots.card : ℝ) * B :=
    (norm_multiset_sum_le _).trans (by
      simpa only [nsmul_eq_mul, Multiset.card_map] using
        Multiset.sum_le_card_nsmul (L.reverse.roots.map norm) B (fun b hb => by
          obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hb
          exact hroot z hz))

  rw [IsAlgClosed.card_roots_eq_natDegree, hd] at hsum
  have hcoeff : L.coeff 1 = -L.reverse.roots.sum := by
    have hn := (IsAlgClosed.splits L.reverse).nextCoeff_eq_neg_sum_roots_of_monic hm
    by_cases hp : 0 < L.natDegree
    · rw [nextCoeff_of_natDegree_pos (hd ▸ hp), coeff_reverse,
        revAt_le (by omega), hd,
        show L.natDegree - (L.natDegree - 1) = 1 by omega] at hn
      exact hn
    · have hzero : L.natDegree = 0 := by omega
      have hR : L.reverse.natDegree = 0 := hd.trans hzero
      have hroots : L.reverse.roots.sum = 0 := by
        rw [eq_C_of_natDegree_eq_zero hR]
        simp
      rw [hroots, neg_zero]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hcoeff, norm_neg]
  exact hsum

/-- A Weil numerator containing the additive L-polynomial supplies the
sharp univariate estimate. The divisor relation is the Artin–Schreier
zeta-factorization input. -/
theorem norm_univariate_characterSum_le_of_curve_factor {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) {a : ZMod p} (ha : a ≠ 0)
    (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    (W : ℂ[X]) (hW : W ≠ 0) (hB : ∀ z ∈ W.reverse.roots, ‖z‖ ≤ Real.sqrt p)
    (hfactor : ∀ L : ℂ[X], (L : PowerSeries ℂ) = additiveLSeries f a → L ∣ W) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p := by
  obtain ⟨L, hdegree, hL⟩ := additiveLSeries_isPolynomial f ha hr hp
  have hL₀ : L.coeff 0 = 1 := by
    rw [← Polynomial.constantCoeff_coe, hL, constantCoeff_additiveLSeries]
  rw [← coeff_one_additiveLSeries, ← hL, Polynomial.coeff_coe]
  exact (norm_coeff_one_le_of_reciprocal_roots hL₀ hW (hfactor L hL) hB).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree) (Real.sqrt_nonneg _))


private theorem nonzero_esymm_card {K : Type*} [Field K] (A : Multiset K)
    (hne : ∀ x ∈ A, x ≠ 0) : A.esymm A.card ≠ 0 := by
  rw [Multiset.esymm, Multiset.powersetCard_self, Multiset.map_singleton, Multiset.sum_singleton]
  exact Multiset.prod_ne_zero (fun hz => hne 0 hz rfl)

/-- The positive power sums determine a finite multiset of nonzero complex numbers. -/
theorem multiset_eq_of_equal_positive_powerSums {K : Type*} [Field K] [CharZero K]
    (A B : Multiset K) (hA : ∀ x ∈ A, x ≠ 0) (hB : ∀ x ∈ B, x ≠ 0)
    (h : ∀ k : ℕ, 0 < k → (A.map (fun x => x^k)).sum = (B.map (fun x => x^k)).sum) :
    A = B := by
  have he (k : ℕ) : A.esymm k = B.esymm k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      rcases k.eq_zero_or_pos with rfl | hk
      · simp [Multiset.esymm]
      · have hAs := multiset_powerSum_newton A hk
        have hBs := multiset_powerSum_newton B hk
        rw [h k hk] at hAs
        have hs :
            ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
              (-1 : K) ^ a.1 * A.esymm a.1 * (A.map (fun x => x ^ a.2)).sum =
            ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
              (-1 : K) ^ a.1 * B.esymm a.1 * (B.map (fun x => x ^ a.2)).sum := by
          apply Finset.sum_congr rfl
          intro a ha
          obtain ⟨had, _, ha₁⟩ := mem_filter.mp ha
          have hs := mem_antidiagonal.mp had
          rw [ih a.1 ha₁, h a.2 (by omega)]
        rw [hs] at hAs
        exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
          (Nat.cast_ne_zero.mpr hk.ne')) (sub_left_inj.mp (hAs.symm.trans hBs))
  have hc : A.card = B.card := by
    apply le_antisymm
    · by_contra! hd
      have hz : B.esymm A.card = 0 := by
        simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ hd]
      exact nonzero_esymm_card A hA ((he A.card).trans hz)
    · by_contra! hd
      have hz : A.esymm B.card = 0 := by
        simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ hd]
      exact nonzero_esymm_card B hB ((he B.card).symm.trans hz)
  have hprod : (A.map fun z => X - C z).prod = (B.map fun z => X - C z).prod := by
    simp only [Multiset.prod_X_sub_X_eq_sum_esymm, hc, he]
  simpa only [Polynomial.roots_multiset_prod_X_sub_C] using congrArg Polynomial.roots hprod

private theorem norm_coeff_one_le_of_reciprocal_root_bound {L : ℂ[X]} (hL : L.coeff 0 = 1)
    {B : ℝ} (hB : ∀ z ∈ L.reverse.roots, ‖z‖ ≤ B) :
    ‖L.coeff 1‖ ≤ (L.natDegree : ℝ) * B := by
  have hn : L ≠ 0 := by intro h; simp [h] at hL
  exact norm_coeff_one_le_of_reciprocal_roots hL hn dvd_rfl hB

/-- A square-root growth bound for the combined reciprocal-root power sums
of the additive L-polynomials gives the sharp bound for each additive sum. -/
theorem norm_univariate_characterSum_le_of_additiveLSeriesGrowth {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    (C : ℝ) (hGrowth : ∀ (L : ZMod p → ℂ[X]),
      (∀ a ≠ 0, (L a : PowerSeries ℂ) = additiveLSeries f a) →
      ∀ᶠ k : ℕ in atTop, ‖∑ a ∈ (Finset.univ.erase (0 : ZMod p)),
        (((L a).reverse.roots).map (fun z => z ^ k)).sum‖ ≤ C * (Real.sqrt p)^k)
    {a : ZMod p} (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p := by
  classical
  have hchoose (a : ZMod p) : ∃ L : ℂ[X], a ≠ 0 →
      L.natDegree ≤ f.natDegree - 1 ∧ (L : PowerSeries ℂ) = additiveLSeries f a := by
    by_cases ha : a = 0
    · exact ⟨0, fun hn => (hn ha).elim⟩
    · obtain ⟨L, hL₁, hL₂⟩ := additiveLSeries_isPolynomial f ha hr hp
      exact ⟨L, fun _ => ⟨hL₁, hL₂⟩⟩
  choose L hL using hchoose
  have hL₀ (a : ZMod p) (ha : a ≠ 0) : (L a).coeff 0 = 1 := by
    rw [← Polynomial.constantCoeff_coe, (hL a ha).2, constantCoeff_additiveLSeries]
  let T := Finset.univ.erase (0 : ZMod p)
  let S : Multiset ℂ := ∑ a ∈ T, (L a).reverse.roots
  have hS : ∀ z ∈ S, ‖z‖ ≤ Real.sqrt p := by
    apply norm_mem_le_of_eventually_powSum_le S (Real.sqrt_nonneg _) C
    filter_upwards [hGrowth L (fun a ha => (hL a ha).2)] with k hk
    have hw (U : Finset (ZMod p)) :
        ((∑ a ∈ U, (L a).reverse.roots).map (fun z => z^k)).sum =
          ∑ a ∈ U, (((L a).reverse.roots).map (fun z => z^k)).sum := by
      induction U using Finset.induction_on with
      | empty => simp
      | insert a U ha ih => simp [Finset.sum_insert ha, Multiset.map_add, ih]
    simpa only [S, hw T] using hk
  have hB (z : ℂ) (hz : z ∈ (L a).reverse.roots) : ‖z‖ ≤ Real.sqrt p := by
    exact hS z (Multiset.mem_sum.mpr ⟨a, Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, hz⟩)
  rw [← coeff_one_additiveLSeries, ← (hL a ha).2, Polynomial.coeff_coe]
  exact (norm_coeff_one_le_of_reciprocal_root_bound (hL₀ a ha) hB).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (hL a ha).1) (Real.sqrt_nonneg _))

/-- The Artin–Schreier curve's weight-one spectrum supplies the required
growth if its positive power sums agree with the combined reciprocal roots. -/
theorem norm_univariate_characterSum_le_of_curve_powerSums {p : ℕ} [Fact p.Prime] [NeZero p]
    (f : (ZMod p)[X]) (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    (A : Multiset ℂ) (hA : ∀ z ∈ A, ‖z‖ = Real.sqrt p)
    (hApower : ∀ (L : ZMod p → ℂ[X]),
      (∀ a ≠ 0, (L a : PowerSeries ℂ) = additiveLSeries f a) →
      ∀ k : ℕ, 0 < k →
        (A.map (fun z => z ^ k)).sum =
          ∑ a ∈ (Finset.univ.erase (0 : ZMod p)),
            (((L a).reverse.roots).map (fun z => z ^ k)).sum)
    {a : ZMod p} (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p := by
  apply norm_univariate_characterSum_le_of_additiveLSeriesGrowth f hr hp A.card ?_ ha
  intro L hL
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  rw [← hApower L hL k hk]
  refine (norm_multiset_sum_le _).trans ?_
  simpa only [Multiset.card_map, nsmul_eq_mul] using
    Multiset.sum_le_card_nsmul ((A.map fun z => z^k).map norm) ((Real.sqrt p)^k) (fun b hb => by
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hb
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
      rw [norm_pow, hA z hz])


/-- The coefficient recurrence for the logarithmic derivative of a
polynomial with constant coefficient one identifies its reciprocal powers.
This form works directly with finite coefficient sums. -/
theorem neg_reciprocalPowerSums_eq_of_coefficient_recurrence
    {K : Type*} [Field K] [IsAlgClosed K] (L : K[X]) (hL : L.coeff 0 = 1)
    (s : ℕ → K)
    (hrec : ∀ k : ℕ, 0 < k → (k : K) * L.coeff k =
      s k + ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
        L.coeff a.1 * s a.2) :
    ∀ k : ℕ, 0 < k → s k = -(L.reverse.roots.map (fun z => z^k)).sum := by
  have hL₀ : L.coeff 0 ≠ 0 := hL.symm ▸ one_ne_zero
  have ht : L.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hL₀)
  have hd : L.reverse.natDegree = L.natDegree := by simp [reverse_natDegree, ht]
  have hm : L.reverse.Monic := by rw [Monic, reverse_leadingCoeff, trailingCoeff, ht, hL]
  have hc (k : ℕ) : descendingCoeff L.reverse k = L.coeff k := by
    by_cases hk : k ≤ L.natDegree
    · rw [descendingCoeff, hd, ite_eq_left hk, coeff_reverse, revAt_le (Nat.sub_le ..),
        Nat.sub_sub_self hk]
    · rw [descendingCoeff, hd, ite_eq_right hk, coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hk)]
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    rw [← newtonPowerSum_eq_roots hm, newtonPowerSum_pos _ hk, hc]
    have hsum :
        ∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k),
          descendingCoeff L.reverse a.1 * newtonPowerSum L.reverse a.2 =
        -∑ a ∈ (antidiagonal k).filter (fun a => 0 < a.1 ∧ a.1 < k), L.coeff a.1 * s a.2 := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨had, hapos, halt⟩ := mem_filter.mp ha
      have hsum := mem_antidiagonal.mp had
      have he := ih a.2 (by omega) (by omega)
      rw [← newtonPowerSum_eq_roots hm] at he
      have he' := congrArg (fun t : K => -t) he
      simp only [neg_neg] at he'
      rw [hc, ← he', mul_neg]
    rw [hsum, neg_mul, hrec k hk]
    ring


end

end Birch
