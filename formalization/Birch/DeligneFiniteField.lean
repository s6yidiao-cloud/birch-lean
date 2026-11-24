import Birch.TerminalAssembly
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The prime-field form of Deligne's exponential-sum estimate

These adapters compare the unnormalized standard-character estimate in
Deligne, La conjecture de Weil I, Theorem 8.4, with the integral twisted
complete sums used in the circle method. The spectral data correspond to the
signed trace in (8.4.2) and the dimension in Lemma 8.5(i).

https://www.numdam.org/item/PMIHES_1974__43__273_0/
-/

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

/-- The standard additive character sum, without normalization. -/
def primeDeligneSum {l : ℕ} (p : ℕ) [NeZero p] (g : MvPolynomial (Fin l) (ZMod p)) : ℂ :=
  ∑ x : Fin l → ZMod p, ZMod.stdAddChar (g.eval x)

/-- The leading homogeneous part has no nonzero critical points over the
algebraic closure of the prime field. -/
def PrimeIsolatedLeadingCriticalPoint {l : ℕ} (p : ℕ) [Fact p.Prime] (r : ℕ)
    (g : MvPolynomial (Fin l) (ZMod p)) : Prop :=
  let K := AlgebraicClosure (ZMod p)
  ∀ x : Fin l → K,
    (∀ i, (pderiv i (homogeneousComponent r g)).eval₂ (algebraMap (ZMod p) K) x = 0) → x = 0

/-- A square-root estimate for the standard nontrivial additive character
in one fixed dimension. -/
def PrimeExponentialSumBoundAtDimension (r l : ℕ) (B : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero p], 0 < l → r < p →
    ∀ g : MvPolynomial (Fin l) (ZMod p), g.totalDegree ≤ r →
      PrimeIsolatedLeadingCriticalPoint p r g →
      ‖primeDeligneSum p g‖ ≤ B^l * (p : ℝ)^((l : ℝ)/2)

/-- The same exponential base applies to all dimensions. -/
def PrimeExponentialSumBound (r : ℕ) (B : ℝ) : Prop :=
  ∀ l : ℕ, PrimeExponentialSumBoundAtDimension r l B

/-- The unnormalized prime-field instance of Deligne's exponential-sum
estimate (Weil I, Theorem 8.4, and Weil II, (3.7.2.1)). -/
def PrimeDeligneEstimate (r : ℕ) : Prop :=
  PrimeExponentialSumBound r ((r : ℝ) - 1)

private theorem homogeneousComponent_map_coefficients {σ R S : Type*}
    [CommSemiring R] [CommSemiring S] (φ : R →+* S) (G : MvPolynomial σ R) (r : ℕ) :
    homogeneousComponent r (MvPolynomial.map φ G) =
      MvPolynomial.map φ (homogeneousComponent r G) := by
  ext b
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

private theorem totalDegree_map_coefficients_le {σ R S : Type*}
    [CommSemiring R] [CommSemiring S] (φ : R →+* S) (G : MvPolynomial σ R) :
    (MvPolynomial.map φ G).totalDegree ≤ G.totalDegree := by
  unfold totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset φ G)

private theorem primeIsolatedLeadingCriticalPoint_reduce_iff {l p r : ℕ} [Fact p.Prime]
    (G : IntForm l) :
    PrimeIsolatedLeadingCriticalPoint p r (MvPolynomial.map (Int.castRingHom (ZMod p)) G) ↔
      ∀ x : Fin l → AlgebraicClosure (ZMod p),
        (∀ i, evalForm (pderiv i (homogeneousComponent r G)) x = 0) → x = 0 := by
  let K := AlgebraicClosure (ZMod p)
  have hcomp : (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) = Int.castRingHom K := by
    ext
    simp
  unfold PrimeIsolatedLeadingCriticalPoint
  simp only [homogeneousComponent_map_coefficients, pderiv_map, eval₂_map]
  rw [hcomp]
  rfl

/-- A positive-dimensional polynomial in the input of the estimate has
actual degree r. -/
theorem totalDegree_eq_of_primeIsolatedLeadingCriticalPoint {l p r : ℕ} [Fact p.Prime]
    (hl : 0 < l) (g : MvPolynomial (Fin l) (ZMod p)) (hg : g.totalDegree ≤ r)
    (hs : PrimeIsolatedLeadingCriticalPoint p r g) : g.totalDegree = r := by
  by_contra h
  have hz := homogeneousComponent_eq_zero r g (lt_of_le_of_ne hg h)
  let K := AlgebraicClosure (ZMod p)
  have hx : (fun _ : Fin l => (1 : K)) = 0 := hs (fun _ => 1) (by simp [hz])
  exact one_ne_zero (congrFun hx ⟨0,hl⟩)

/-- In the characteristic range of the estimate, the leading-gradient
condition is equivalent to the projective Jacobian criterion on the
leading homogeneous hypersurface. -/
theorem primeIsolatedLeadingCriticalPoint_iff_projectiveJacobian {l p r : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hrp : r < p) (g : MvPolynomial (Fin l) (ZMod p)) :
    PrimeIsolatedLeadingCriticalPoint p r g ↔
      let K := AlgebraicClosure (ZMod p)
      ∀ x : Fin l → K,
        (homogeneousComponent r g).eval₂ (algebraMap (ZMod p) K) x = 0 →
        (∀ i, (pderiv i (homogeneousComponent r g)).eval₂ (algebraMap (ZMod p) K) x = 0) →
        x = 0 := by
  let K := AlgebraicClosure (ZMod p)
  let Q := homogeneousComponent r g
  have hrK : (r : K) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff K p r).mp h
    exact hrp.not_ge (Nat.le_of_dvd hr hdiv)
  constructor
  · exact fun h x _ hx => h x hx
  · intro h x hx
    let ev : MvPolynomial (Fin l) (ZMod p) →+* K := eval₂Hom (algebraMap (ZMod p) K) x
    have hzero (i : Fin l) : ev (pderiv i Q) = 0 := hx i
    have hEuler := congrArg ev (homogeneousComponent_isHomogeneous r g).sum_X_mul_pderiv
    change ev (∑ i, X i * pderiv i Q) = ev (r • Q) at hEuler
    rw [nsmul_eq_mul, map_mul, map_natCast, map_sum] at hEuler
    simp only [map_mul, hzero, mul_zero, Finset.sum_const_zero] at hEuler
    exact h x ((mul_eq_zero.mp hEuler.symm).resolve_left hrK) hx

private theorem norm_completeSum_one_eq_primeDeligneSum {l p : ℕ} [NeZero p] (G : IntForm l) :
    ‖completeSum G p 1‖ =
      ‖primeDeligneSum p (MvPolynomial.map (Int.castRingHom (ZMod p)) G)‖ / (p : ℝ)^l := by
  unfold completeSum primeDeligneSum
  simp only [one_mul, residueEval, eval_map, ← div_eq_inv_mul, norm_div, norm_pow,
    Complex.norm_natCast]

private theorem deligne_normalization (B : ℝ) (l : ℕ) {p : ℝ} (hp : 0 < p) :
    (B^l * p^((l:ℝ)/2)) / p^l = B^l * p^(-(l:ℝ)/2) := by
  rw [mul_div_assoc, ← Real.rpow_natCast p l, ← Real.rpow_sub hp]
  congr 2
  ring

/-- The standard-character estimate supplies the manuscript's normalized
estimate with any nonzero numerator and any linear twist. -/
theorem twistedCompleteSum_le_of_primeExponentialSumBoundAtDimension {r l : ℕ} {B : ℝ} (hr : 2 ≤ r)
    (h : PrimeExponentialSumBoundAtDimension r l B) :
    ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
      ∀ (g : IntForm l), g.totalDegree ≤ r →
        (∀ x : Fin l → AlgebraicClosure (ZMod p),
          (∀ i, evalForm (pderiv i (homogeneousComponent r g)) x = 0) → x = 0) →
        ∀ (a : ℤ), (a : ZMod p) ≠ 0 → ∀ z : Fin l → ℤ,
          ‖twistedCompleteSum g p a z‖ ≤ B^l * (p : ℝ)^(-(l : ℝ)/2) := by
  intro p _ _ hrp g hg hs a ha z
  let L : IntForm l := ∑ i, C (z i) * X i
  let G : IntForm l := C a * g + L
  change ‖completeSum G p 1‖ ≤ _
  rw [norm_completeSum_one_eq_primeDeligneSum]
  by_cases hl : 0 < l
  · have hL : L.IsHomogeneous 1 := by
      apply IsHomogeneous.sum
      intro i _
      exact isHomogeneous_C_mul_X (z i) i
    have hG : G.totalDegree ≤ r :=
      (totalDegree_add _ _).trans (max_le
        ((totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hg))
        (hL.totalDegree_le.trans (by omega)))
    have htop : homogeneousComponent r G = C a * homogeneousComponent r g := by
      unfold G
      rw [map_add, homogeneousComponent_C_mul,
        homogeneousComponent_eq_zero _ _ (hL.totalDegree_le.trans_lt (by omega)), add_zero]
    have hcrit : PrimeIsolatedLeadingCriticalPoint p r
        (MvPolynomial.map (Int.castRingHom (ZMod p)) G) := by
      apply (primeIsolatedLeadingCriticalPoint_reduce_iff G).mpr
      intro x hx
      let K := AlgebraicClosure (ZMod p)
      have haK : (a : K) ≠ 0 := by
        rw [← map_intCast (algebraMap (ZMod p) K)]
        exact (map_ne_zero (algebraMap (ZMod p) K)).mpr ha
      apply hs x
      intro i
      have hi := hx i
      rw [htop, pderiv_C_mul] at hi
      change (C a * pderiv i (homogeneousComponent r g)).eval₂ (Int.castRingHom K) x = 0 at hi
      rw [eval₂_mul, eval₂_C, Int.coe_castRingHom] at hi
      exact (mul_eq_zero.mp hi).resolve_left haK
    have hmain := h p hl hrp _ ((totalDegree_map_coefficients_le _ _).trans hG) hcrit
    have hp : (0:ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
    exact (div_le_div_of_nonneg_right hmain (pow_nonneg hp.le _)).trans_eq
      (deligne_normalization B l hp)
  · have hl₀ : l = 0 := by omega
    subst l
    simp [primeDeligneSum, ZMod.stdAddChar_apply]

/-- A uniform estimate in each dimension gives the normalized twisted bound
with the same exponential base in every dimension. -/
theorem twistedCompleteSum_le_of_primeExponentialSumBound {r : ℕ} {B : ℝ} (hr : 2 ≤ r)
    (h : PrimeExponentialSumBound r B) :
    ∀ (l p : ℕ) [Fact p.Prime] [NeZero p], r < p →
      ∀ (g : IntForm l), g.totalDegree ≤ r →
        (∀ x : Fin l → AlgebraicClosure (ZMod p),
          (∀ i, evalForm (pderiv i (homogeneousComponent r g)) x = 0) → x = 0) →
        ∀ (a : ℤ), (a : ZMod p) ≠ 0 → ∀ z : Fin l → ℤ,
          ‖twistedCompleteSum g p a z‖ ≤ B^l * (p : ℝ)^(-(l : ℝ)/2) :=
  fun l => twistedCompleteSum_le_of_primeExponentialSumBoundAtDimension hr (h l)

/-- The sharp prime-field estimate gives Deligne's normalized twisted bound. -/
theorem deligneTwistedDegree_of_primeDeligneEstimate {r : ℕ} (hr : 2 ≤ r)
    (h : PrimeDeligneEstimate r) : DeligneTwistedDegree r :=
  twistedCompleteSum_le_of_primeExponentialSumBound hr h

/-- Any positive exponential base gives a uniform square-root bound at each
fixed slice dimension. -/
theorem uniformTwistedPrimeBound_of_primeExponentialSumBound {r : ℕ} {B : ℝ}
    (hr : 2 ≤ r) (hB : 0 < B) (h : PrimeExponentialSumBound r B) (l : ℕ) :
    UniformTwistedPrimeBound r l :=
  ⟨B^l, pow_pos hB _, twistedCompleteSum_le_of_primeExponentialSumBound hr h l⟩

private theorem exists_integral_lift_totalDegree {l p : ℕ} [NeZero p]
    (g : MvPolynomial (Fin l) (ZMod p)) :
    ∃ G : IntForm l, MvPolynomial.map (Int.castRingHom (ZMod p)) G = g ∧
      G.totalDegree ≤ g.totalDegree := by
  classical
  refine ⟨∑ b ∈ g.support, monomial b ((g.coeff b).val : ℤ), ?_, ?_⟩
  · simp only [map_sum, map_monomial, Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact g.as_sum.symm
  · apply totalDegree_finsetSum_le
    intro b hb
    exact (totalDegree_monomial_le _ _).trans (le_totalDegree hb)

/-- Integral coefficient lifts recover the usual prime-field formulation
from the normalized twisted estimate. -/
theorem primeDeligneEstimate_of_deligneTwistedDegree {r : ℕ}
    (h : DeligneTwistedDegree r) : PrimeDeligneEstimate r := by
  intro l p _ _ _ hrp g hg hs
  obtain ⟨G,hG,hdeg⟩ := exists_integral_lift_totalDegree g
  have hcrit : ∀ x : Fin l → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i (homogeneousComponent r G)) x = 0) → x = 0 :=
    (primeIsolatedLeadingCriticalPoint_reduce_iff G).mp (hG.symm ▸ hs)
  have hb := h l p hrp G (hdeg.trans hg) hcrit 1 (by simp) 0
  rw [twistedCompleteSum_zero, Int.cast_one, norm_completeSum_one_eq_primeDeligneSum, hG] at hb
  have hp : (0:ℝ) < p := Nat.cast_pos.mpr (NeZero.pos p)
  rw [← deligne_normalization ((r : ℝ) - 1) l hp] at hb
  exact (div_le_div_iff_of_pos_right (pow_pos hp l)).mp hb

/-- Over degrees at least two, the two forms of Deligne's estimate have the
same content for this project. -/
theorem primeDeligneEstimate_iff_deligneTwistedDegree {r : ℕ} (hr : 2 ≤ r) :
    PrimeDeligneEstimate r ↔ DeligneTwistedDegree r :=
  ⟨deligneTwistedDegree_of_primeDeligneEstimate hr, primeDeligneEstimate_of_deligneTwistedDegree⟩

/-- The finite spectral data used by Deligne's trace argument. The norm
bound is the consequence of weights at most l needed for the estimate. -/
def PrimeDeligneSpectralData (r : ℕ) : Prop :=
  ∀ (l p : ℕ) [Fact p.Prime] [NeZero p], 0 < l → r < p →
    ∀ g : MvPolynomial (Fin l) (ZMod p), g.totalDegree ≤ r →
      PrimeIsolatedLeadingCriticalPoint p r g →
      ∃ roots : Fin ((r-1)^l) → ℂ,
        primeDeligneSum p g = (-1 : ℂ)^l * (∑ j, roots j) ∧
        ∀ j, ‖roots j‖ ≤ (p : ℝ)^((l:ℝ)/2)

/-- The signed spectral sum gives the unnormalized bound by the triangle
inequality, with the exact multiplicity. -/
theorem primeDeligneEstimate_of_spectralData {r : ℕ} (hr : 2 ≤ r)
    (h : PrimeDeligneSpectralData r) : PrimeDeligneEstimate r := by
  intro l p _ _ hl hp g hg hs
  obtain ⟨roots,hroots,hw⟩ := h l p hl hp g hg hs
  rw [hroots, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  calc
    _ ≤ ∑ j, ‖roots j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin ((r-1)^l), (p:ℝ)^((l:ℝ)/2) := Finset.sum_le_sum (fun j _ => hw j)
    _ = _ := by
      simp [nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ r)]
/-- The prime-field spectral input supplies the twisted estimate directly. -/
theorem deligneTwistedDegree_of_primeDeligneSpectralData {r : ℕ} (hr : 2 ≤ r)
    (h : PrimeDeligneSpectralData r) : DeligneTwistedDegree r :=
  deligneTwistedDegree_of_primeDeligneEstimate hr (primeDeligneEstimate_of_spectralData hr h)


end

end Birch
