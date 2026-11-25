import Birch.UnivariateClosedPoints
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! # Counting weighted factorizations over the affine line -/

open Polynomial Finset UniqueFactorizationMonoid

namespace Birch

noncomputable section

variable {p : ℕ} [Fact p.Prime] [NeZero p]

/-- The monic polynomials of the specified degree over the prime field. -/
def monicDegreePolynomials (p : ℕ) [Fact p.Prime] [NeZero p] (k : ℕ) :
    Finset (ZMod p)[X] :=
  Finset.univ.image fun c : Fin k → ZMod p => monicWithCoefficients c

theorem mem_monicDegreePolynomials {k : ℕ} {P : (ZMod p)[X]} :
    P ∈ monicDegreePolynomials p k ↔ P.Monic ∧ P.natDegree = k := by
  unfold monicDegreePolynomials
  constructor
  · intro h
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨monicWithCoefficients_monic c, monicWithCoefficients_natDegree c⟩
  · rintro ⟨hM, hD⟩
    let Q := MonicDegreeEq.mk P hM hD
    obtain ⟨c,hc⟩ := (monicWithCoefficientsEquiv k).surjective Q
    exact mem_image.mpr ⟨c, mem_univ _, congrArg Subtype.val hc⟩

private theorem additiveLSeriesCoeff_eq_sum_monic_polynomials
    (f : (ZMod p)[X]) (a : ZMod p) (k : ℕ) :
    additiveLSeriesCoeff f a k =
      ∑ P ∈ monicDegreePolynomials p k, ZMod.stdAddChar (a * polynomialRootPhase f P) := by
  classical
  rw [additiveLSeriesCoeff, monicDegreePolynomials, Finset.sum_image]
  intro x _ y _ h
  exact (monicWithCoefficientsEquiv k).injective (Subtype.ext h)

omit [NeZero p] in
private theorem pow_dvd_iff_le_normalizedFactors_count {Q P : (ZMod p)[X]}
    (hQ : Q.Monic) (hP : P.Monic) (hI : Irreducible P) (j : ℕ) :
    P^j ∣ Q ↔ j ≤ (normalizedFactors Q).count P := by
  rw [pow_dvd_iff_le_emultiplicity,
    emultiplicity_eq_count_normalizedFactors hI hQ.ne_zero,
    normalize_eq_self_iff_monic hP.ne_zero |>.mpr hP]
  exact ENat.natCast_le_natCast

omit [NeZero p] in
private theorem natDegree_eq_sum_normalized_factors {P : (ZMod p)[X]} (hP : P.Monic) :
    P.natDegree =
      ∑ Q ∈ (normalizedFactors P).toFinset,
        ∑ _j ∈ Finset.Icc 1 ((normalizedFactors P).count Q), Q.natDegree := by
  have hprod := leadingCoeff_mul_prod_normalizedFactors P
  rw [hP.leadingCoeff, map_one, one_mul] at hprod
  conv_lhs => rw [← hprod, natDegree_multiset_prod _ (zero_notMem_normalizedFactors _)]
  rw [Finset.sum_multiset_map_count]
  apply Finset.sum_congr rfl
  intro Q hQ
  simp [Nat.card_Icc]

private abbrev LeftTuple (p : ℕ) := Σ _ij : ℕ × ℕ, (ZMod p)[X] × (ZMod p)[X]
private abbrev RightTuple (p : ℕ) := Σ _Q : (ZMod p)[X], Σ _P : (ZMod p)[X], ℕ

private def factorRecurrenceLeft (p : ℕ) [Fact p.Prime] [NeZero p] (k : ℕ) : Finset (LeftTuple p) :=
  ((antidiagonal k).filter (fun ij => 0 < ij.2)).sigma fun ij =>
    (affineLineClosedPoints (p := p) ij.2).product (monicDegreePolynomials p ij.1)

private def factorRecurrenceRight (p : ℕ) [Fact p.Prime] [NeZero p] (k : ℕ) : Finset (RightTuple p) :=
  (monicDegreePolynomials p k).sigma fun Q =>
    (normalizedFactors Q).toFinset.sigma fun P => Finset.Icc 1 ((normalizedFactors Q).count P)

private def weightPhase (f P : (ZMod p)[X]) (a : ZMod p) : ℂ :=
  ZMod.stdAddChar (a * polynomialRootPhase f P)

private theorem weightPhase_one (f : (ZMod p)[X]) (a : ZMod p) : weightPhase f 1 a = 1 := by
  have hphase : polynomialRootPhase f 1 = 0 := by
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    apply φ.injective
    rw [map_polynomialRootPhase_eq_sum_roots φ f monic_one]
    simp
  simp [weightPhase, hphase]

private theorem weightPhase_mul (f : (ZMod p)[X]) (a : ZMod p)
    {P Q : (ZMod p)[X]} (hP : P.Monic) (hQ : Q.Monic) :
    weightPhase f (P*Q) a = weightPhase f P a * weightPhase f Q a := by
  rw [weightPhase, polynomialRootPhase_mul f hP hQ, mul_add, AddChar.map_add_eq_mul]
  rfl

private theorem weightPhase_pow (f : (ZMod p)[X]) (a : ZMod p)
    {P : (ZMod p)[X]} (hP : P.Monic) (j : ℕ) :
    weightPhase f (P^j) a = weightPhase f P a ^ j := by
  induction j with
  | zero => simp [weightPhase_one]
  | succ j ih => rw [pow_succ, pow_succ, weightPhase_mul f a (hP.pow j) hP, ih]

private theorem mem_factorRecurrenceLeft {k : ℕ} {x : LeftTuple p} :
    x ∈ factorRecurrenceLeft p k ↔
      x.1.1 + x.1.2 = k ∧ 0 < x.1.2 ∧ x.2.1.Monic ∧ Irreducible x.2.1 ∧
        x.2.1.natDegree ∣ x.1.2 ∧ x.2.2.Monic ∧ x.2.2.natDegree = x.1.1 := by
  rcases x with ⟨ij,P,Q⟩
  rw [factorRecurrenceLeft, Finset.mem_sigma, Finset.mem_filter, mem_antidiagonal]
  change (_ ∧ (P,Q) ∈ affineLineClosedPoints (p := p) ij.2 ×ˢ monicDegreePolynomials p ij.1) ↔ _
  rw [Finset.mem_product, mem_monicDegreePolynomials]
  constructor
  · rintro ⟨⟨hij,hj⟩,hP,hQ,hD⟩
    obtain ⟨hM,hI,hd⟩ := (mem_affineLineClosedPoints hj).mp hP
    exact ⟨hij,hj,hM,hI,hd,hQ,hD⟩
  · rintro ⟨hij,hj,hM,hI,hd,hQ,hD⟩
    exact ⟨⟨hij,hj⟩, (mem_affineLineClosedPoints hj).mpr ⟨hM,hI,hd⟩, hQ,hD⟩

private theorem mem_factorRecurrenceRight {k : ℕ} {y : RightTuple p} :
    y ∈ factorRecurrenceRight p k ↔
      y.1.Monic ∧ y.1.natDegree = k ∧ y.2.1.Monic ∧ Irreducible y.2.1 ∧
        0 < y.2.2 ∧ y.2.1 ^ y.2.2 ∣ y.1 := by
  rw [factorRecurrenceRight, Finset.mem_sigma, Finset.mem_sigma, mem_monicDegreePolynomials,
    Multiset.mem_toFinset, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hM,hD⟩,hP,hj,hpow⟩
    obtain ⟨hI,hPm,_⟩ := (Polynomial.mem_normalizedFactors_iff hM.ne_zero).mp hP
    exact ⟨hM,hD,hPm,hI,hj,(pow_dvd_iff_le_normalizedFactors_count hM hPm hI _).mpr hpow⟩
  · rintro ⟨hM,hD,hPm,hI,hj,hpow⟩
    have hd : y.2.1 ∣ y.1 := (dvd_pow (dvd_refl _) hj.ne').trans hpow
    exact ⟨⟨hM,hD⟩, (Polynomial.mem_normalizedFactors_iff hM.ne_zero).mpr ⟨hI,hPm,hd⟩,
      hj, (pow_dvd_iff_le_normalizedFactors_count hM hPm hI _).mp hpow⟩

private def factorRecurrenceMap (x : LeftTuple p) : RightTuple p :=
  ⟨x.2.1 ^ (x.1.2 / x.2.1.natDegree) * x.2.2, ⟨x.2.1, x.1.2 / x.2.1.natDegree⟩⟩

private theorem factorRecurrenceMap_mem {k : ℕ} {x : LeftTuple p}
    (hx : x ∈ factorRecurrenceLeft p k) : factorRecurrenceMap x ∈ factorRecurrenceRight p k := by
  obtain ⟨hij,hj,hPm,hI,hd,hQ,hD⟩ := mem_factorRecurrenceLeft.mp hx
  have hpow := hPm.pow (x.1.2 / x.2.1.natDegree)
  apply mem_factorRecurrenceRight.mpr
  refine ⟨hpow.mul hQ, ?_,hPm,hI, Nat.div_pos (Nat.le_of_dvd hj hd) hI.natDegree_pos, ⟨x.2.2,rfl⟩⟩
  simp only [factorRecurrenceMap, natDegree_mul hpow.ne_zero hQ.ne_zero,
    natDegree_pow, Nat.div_mul_cancel hd, hD]
  omega

private theorem factorRecurrenceMap_inj {k : ℕ} {x y : LeftTuple p}
    (hx : x ∈ factorRecurrenceLeft p k) (hy : y ∈ factorRecurrenceLeft p k)
    (he : factorRecurrenceMap x = factorRecurrenceMap y) : x = y := by
  obtain ⟨hxi, _, hPx, _, hdx, _, _⟩ := mem_factorRecurrenceLeft.mp hx
  obtain ⟨hyi, _, _, _, hdy, _, _⟩ := mem_factorRecurrenceLeft.mp hy
  have hP := congrArg (fun z : RightTuple p => z.2.1) he
  have hj := congrArg (fun z : RightTuple p => z.2.2) he
  have hR := congrArg (fun z : RightTuple p => z.1) he
  simp only [factorRecurrenceMap] at hP hj hR
  have hν : x.1.2 = y.1.2 := by
    calc
      _ = (x.1.2 / x.2.1.natDegree) * x.2.1.natDegree := (Nat.div_mul_cancel hdx).symm
      _ = (y.1.2 / y.2.1.natDegree) * y.2.1.natDegree := by rw [hj,hP]
      _ = _ := Nat.div_mul_cancel hdy
  have hμ : x.1.1 = y.1.1 := by omega
  have hQ : x.2.2 = y.2.2 := by
    rw [← hj, ← hP] at hR
    exact mul_left_cancel₀ (pow_ne_zero _ hPx.ne_zero) hR
  rcases x with ⟨⟨ix,jx⟩,Px,Qx⟩
  rcases y with ⟨⟨iy,jy⟩,Py,Qy⟩
  simp only [Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq]
  exact ⟨⟨hμ,hν⟩,hP,hQ⟩

private theorem factorRecurrenceMap_surj {k : ℕ} {y : RightTuple p}
    (hy : y ∈ factorRecurrenceRight p k) :
    ∃ x ∈ factorRecurrenceLeft p k, factorRecurrenceMap x = y := by
  obtain ⟨hM,hD,hP,hI,hj,hpow⟩ := mem_factorRecurrenceRight.mp hy
  obtain ⟨Q,hQ⟩ := hpow
  let j := y.2.2 * y.2.1.natDegree
  have hmQ : Q.Monic := (hP.pow y.2.2).of_mul_monic_left (hQ ▸ hM)
  have htot : j + Q.natDegree = k := by
    rw [hQ, natDegree_mul (hP.pow _).ne_zero hmQ.ne_zero, natDegree_pow] at hD
    exact hD
  let x : LeftTuple p := ⟨(Q.natDegree, j), y.2.1, Q⟩
  have hj' : 0 < j := Nat.mul_pos hj hI.natDegree_pos
  have hdj : y.2.1.natDegree ∣ j := dvd_mul_left _ _
  have hcancel : j / y.2.1.natDegree = y.2.2 := Nat.mul_div_cancel _ hI.natDegree_pos
  refine ⟨x, mem_factorRecurrenceLeft.mpr ⟨by change Q.natDegree + j = k; omega,
    hj', hP, hI, hdj, hmQ, rfl⟩, ?_⟩
  have he : factorRecurrenceMap x =
      ⟨y.1, ⟨y.2.1,y.2.2⟩⟩ := by
    simp only [factorRecurrenceMap, x, hcancel, hQ]
  simpa using he

private theorem sum_factorRecurrence (f : (ZMod p)[X]) (a : ZMod p) (k : ℕ) :
    (∑ x ∈ factorRecurrenceLeft p k, (x.2.1.natDegree : ℂ) *
      (weightPhase f x.2.1 a) ^ (x.1.2 / x.2.1.natDegree) * weightPhase f x.2.2 a) =
    ∑ y ∈ factorRecurrenceRight p k, (y.2.1.natDegree : ℂ) * weightPhase f y.1 a := by
  apply Finset.sum_bij (fun x _ => factorRecurrenceMap x)
  · exact fun _ hx => factorRecurrenceMap_mem hx
  · exact fun _ hx _ hy h => factorRecurrenceMap_inj hx hy h
  · intro y hy
    obtain ⟨x,hx,he⟩ := factorRecurrenceMap_surj hy
    exact ⟨x,hx,he⟩
  · intro x hx
    obtain ⟨_,_,hP,_,_,hQ,_⟩ := mem_factorRecurrenceLeft.mp hx
    simp only [factorRecurrenceMap, weightPhase_mul f a (hP.pow _) hQ, weightPhase_pow f a hP,
      mul_assoc]

private theorem sum_factorRecurrenceLeft_eq (f : (ZMod p)[X]) (a : ZMod p) (k : ℕ) :
    (∑ x ∈ factorRecurrenceLeft p k, (x.2.1.natDegree : ℂ) *
      (weightPhase f x.2.1 a) ^ (x.1.2 / x.2.1.natDegree) * weightPhase f x.2.2 a) =
    ∑ ij ∈ (antidiagonal k).filter (fun ij => 0 < ij.2),
      additiveLSeriesCoeff f a ij.1 *
        extensionCharacterSum (K := GaloisField p ij.2) (fun x => aeval x f) a := by
  rw [factorRecurrenceLeft, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro ij hij
  change (∑ x ∈ affineLineClosedPoints (p := p) ij.2 ×ˢ monicDegreePolynomials p ij.1,
    (x.1.natDegree : ℂ) * (weightPhase f x.1 a) ^ (ij.2 / x.1.natDegree) *
      weightPhase f x.2 a) = _
  rw [Finset.sum_product, additiveLSeriesCoeff_eq_sum_monic_polynomials,
    extensionCharacterSum_eq_closedPoint_powers (mem_filter.mp hij).2]
  conv_rhs => rw [mul_comm]
  simp only [Finset.sum_mul, Finset.mul_sum, weightPhase]
  rw [Finset.sum_comm]

private theorem sum_factorRecurrenceRight_eq (f : (ZMod p)[X]) (a : ZMod p) (k : ℕ) :
    (∑ y ∈ factorRecurrenceRight p k, (y.2.1.natDegree : ℂ) * weightPhase f y.1 a) =
      (k : ℂ) * additiveLSeriesCoeff f a k := by
  rw [factorRecurrenceRight, Finset.sum_sigma, additiveLSeriesCoeff_eq_sum_monic_polynomials,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [Finset.sum_sigma]
  have he := natDegree_eq_sum_normalized_factors (mem_monicDegreePolynomials.mp hQ).1
  have hD := (mem_monicDegreePolynomials.mp hQ).2
  rw [hD] at he
  have h := congrArg (fun n : ℕ => (n : ℂ)) he
  push_cast at h
  rw [h]
  simp only [Finset.sum_mul, weightPhase]

/-- Unique factorization of monic polynomials gives the Euler relation
in each coefficient, without convergence or an infinite product. -/
theorem additiveLSeriesCoefficientRecurrence_holds (f : (ZMod p)[X]) :
    AdditiveLSeriesCoefficientRecurrence p f := by
  intro a _ k hk
  let s := (antidiagonal k).filter (fun ij => 0 < ij.2)
  let H (ij : ℕ × ℕ) := additiveLSeriesCoeff f a ij.1 *
    extensionCharacterSum (K := GaloisField p ij.2) (fun x => aeval x f) a
  have he : (k : ℂ) * additiveLSeriesCoeff f a k = ∑ ij ∈ s, H ij :=
    (sum_factorRecurrenceRight_eq f a k).symm.trans
      ((sum_factorRecurrence f a k).symm.trans (sum_factorRecurrenceLeft_eq f a k))
  have h0 : (0,k) ∈ s := mem_filter.mpr ⟨mem_antidiagonal.mpr (zero_add k), hk⟩
  have hs : s.erase (0,k) = (antidiagonal k).filter (fun ij => 0 < ij.1 ∧ ij.1 < k) := by
    ext ij
    rcases ij with ⟨i,j⟩
    dsimp only [s]
    rw [mem_erase, mem_filter, mem_filter, mem_antidiagonal]
    constructor
    · rintro ⟨hne,hij,hj⟩
      have hi : 0 < i := by
        by_contra! h
        have hii : i = 0 := by omega
        have hjj : j = k := by
          change i + j = k at hij
          omega
        exact hne (Prod.ext hii hjj)
      change i + j = k at hij
      exact ⟨hij,hi,by omega⟩
    · rintro ⟨hij,hi,hik⟩
      change i + j = k at hij
      exact ⟨fun h => hi.ne' (congrArg Prod.fst h),hij,by omega⟩
  have hc := constantCoeff_additiveLSeries f a
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, additiveLSeries, PowerSeries.coeff_mk] at hc
  rw [he, ← Finset.sum_erase_add s H h0, hs, add_comm]
  simp only [H, hc, one_mul]

/-- The extension moments of the additive L-polynomial are the extension
character sums with the logarithmic-derivative sign. -/
theorem additiveLSeriesExtensionPowerSums_holds (f : (ZMod p)[X]) :
    AdditiveLSeriesExtensionPowerSums p f :=
  additiveLSeriesExtensionPowerSums_of_coefficient_recurrence f
    (additiveLSeriesCoefficientRecurrence_holds f)

/-- The sharp univariate character estimate follows from the Artin–Schreier
curve's weight-one spectrum and affine point-count identity. -/
theorem norm_univariate_characterSum_le_of_artinSchreierCurve
    (f : (ZMod p)[X]) (hr : 0 < f.natDegree) (hp : f.natDegree < p)
    (A : Multiset ℂ) (hA : ∀ z ∈ A, ‖z‖ = Real.sqrt p)
    (hcurve : ∀ m : ℕ, 0 < m →
      (artinSchreierTwistCount (p := p) (fun x : GaloisField p m => aeval x f) 0 : ℂ) =
        (p : ℂ)^m - (A.map (fun z => z^m)).sum)
    {a : ZMod p} (ha : a ≠ 0) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (a * f.eval x)‖ ≤
      ((f.natDegree - 1 : ℕ) : ℝ) * Real.sqrt p :=
  norm_univariate_characterSum_le_of_artinSchreier_spectrum f hr hp A hA hcurve
    (additiveLSeriesExtensionPowerSums_holds f) ha

end

end Birch
