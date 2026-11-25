import Birch.CharacterSumAmplification
import Birch.DeligneFiniteField

/-! # Polynomial phases on Cartesian powers -/

open MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

/-- The sum of (k) copies of a polynomial in disjoint variable blocks. -/
def additivePowerPolynomial {σ R : Type*} [CommSemiring R] (k : ℕ)
    (g : MvPolynomial σ R) : MvPolynomial (Fin k × σ) R :=
  ∑ j : Fin k, rename (Prod.mk j) g

/-- Evaluation of the additive power is the sum of its block evaluations. -/
theorem eval₂_additivePowerPolynomial {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (k : ℕ) (g : MvPolynomial σ R) (φ : R →+* S) (x : Fin k × σ → S) :
    (additivePowerPolynomial k g).eval₂ φ x = ∑ j : Fin k, g.eval₂ φ (fun i => x (j, i)) := by
  simp only [additivePowerPolynomial, eval₂_sum, eval₂_rename_prod_mk]

/-- Additive powers preserve the upper bound on the total degree. -/
theorem totalDegree_additivePowerPolynomial_le {σ R : Type*} [CommSemiring R]
    (k : ℕ) (g : MvPolynomial σ R) :
    (additivePowerPolynomial k g).totalDegree ≤ g.totalDegree := by
  exact totalDegree_finsetSum_le (fun j _ => totalDegree_rename_le (Prod.mk j) g)

/-- A homogeneous component is formed separately in each block. -/
theorem homogeneousComponent_additivePowerPolynomial {σ R : Type*} [CommSemiring R]
    (k r : ℕ) (g : MvPolynomial σ R) :
    homogeneousComponent r (additivePowerPolynomial k g) =
      additivePowerPolynomial k (homogeneousComponent r g) := by
  simp only [additivePowerPolynomial, map_sum, rename_homogeneousComponent]

/-- A renamed polynomial is constant in coordinates outside the renaming. -/
theorem pderiv_rename_eq_zero_of_not_mem_range {σ τ R : Type*} [CommSemiring R]
    (f : σ → τ) (j : τ) (hj : j ∉ Set.range f) (g : MvPolynomial σ R) :
    pderiv j (rename f g) = 0 := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    have hi : j ≠ f i := fun eq => hj ⟨i, eq.symm⟩
    simp [Derivation.leibniz, Ne.symm hi, hp]

/-- A partial derivative on the additive power only differentiates its own block. -/
theorem pderiv_additivePowerPolynomial {σ R : Type*} [CommSemiring R] {k : ℕ}
    (g : MvPolynomial σ R) (j : Fin k) (i : σ) :
    pderiv (j, i) (additivePowerPolynomial k g) = rename (Prod.mk j) (pderiv i g) := by
  classical
  unfold additivePowerPolynomial
  rw [map_sum, Finset.sum_eq_single j]
  · exact pderiv_rename (fun _ _ h => congrArg Prod.snd h) i g
  · intro a _ ha
    apply pderiv_rename_eq_zero_of_not_mem_range
    rintro ⟨b, hb⟩
    exact ha (congrArg Prod.fst hb)
  · simp

/-- The leading partial derivative is the corresponding leading derivative in its block. -/
theorem pderiv_homogeneousComponent_additivePowerPolynomial {σ R : Type*} [CommSemiring R]
    {k : ℕ} (r : ℕ) (g : MvPolynomial σ R) (j : Fin k) (i : σ) :
    pderiv (j, i) (homogeneousComponent r (additivePowerPolynomial k g)) =
      rename (Prod.mk j) (pderiv i (homogeneousComponent r g)) := by
  rw [homogeneousComponent_additivePowerPolynomial, pderiv_additivePowerPolynomial]

/-- Over any evaluation ring, a zero of the leading gradient on the power
restricts to a zero of the leading gradient in every block. -/
theorem additivePowerPolynomial_isolatedLeadingCriticalPoint {σ R S : Type*}
    [CommSemiring R] [CommSemiring S] (k r : ℕ) (g : MvPolynomial σ R) (φ : R →+* S)
    (hg : ∀ x : σ → S, (∀ i, (pderiv i (homogeneousComponent r g)).eval₂ φ x = 0) → x = 0)
    (x : Fin k × σ → S)
    (hx : ∀ b, (pderiv b (homogeneousComponent r (additivePowerPolynomial k g))).eval₂ φ x = 0) :
    x = 0 := by
  funext b
  rcases b with ⟨j, i⟩
  have hblock : (fun a => x (j, a)) = 0 := hg _ (fun a => by
    simpa only [pderiv_homogeneousComponent_additivePowerPolynomial, eval₂_rename_prod_mk]
      using hx (j, a))
  exact congrFun hblock i


/-- The additive power written with (k l) linearly indexed variables. -/
def additivePowerPolynomialFin {l : ℕ} {R : Type*} [CommSemiring R] (k : ℕ)
    (g : MvPolynomial (Fin l) R) : MvPolynomial (Fin (k * l)) R :=
  rename finProdFinEquiv (additivePowerPolynomial k g)

/-- Forming an additive power commutes with changing the coefficients. -/
theorem map_additivePowerPolynomialFin {l : ℕ} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (k : ℕ) (g : MvPolynomial (Fin l) R) :
    MvPolynomial.map φ (additivePowerPolynomialFin k g) =
      additivePowerPolynomialFin k (MvPolynomial.map φ g) := by
  simp only [additivePowerPolynomialFin, additivePowerPolynomial, map_rename, map_sum]

/-- Evaluation after reindexing gives the sum of the independent block values. -/
theorem eval₂_additivePowerPolynomialFin {l : ℕ} {R S : Type*} [CommSemiring R]
    [CommSemiring S] (k : ℕ) (g : MvPolynomial (Fin l) R) (φ : R →+* S)
    (x : Fin (k * l) → S) :
    (additivePowerPolynomialFin k g).eval₂ φ x =
      ∑ j : Fin k, g.eval₂ φ (fun i => x (finProdFinEquiv (j, i))) := by
  simp only [additivePowerPolynomialFin, eval₂_rename, eval₂_additivePowerPolynomial,
    Function.comp_apply]

/-- Reindexing the additive power preserves the total-degree bound. -/
theorem totalDegree_additivePowerPolynomialFin_le {l : ℕ} {R : Type*} [CommSemiring R]
    (k : ℕ) (g : MvPolynomial (Fin l) R) :
    (additivePowerPolynomialFin k g).totalDegree ≤ g.totalDegree :=
  (totalDegree_rename_le finProdFinEquiv _).trans (totalDegree_additivePowerPolynomial_le k g)

/-- The isolated critical-point hypothesis of the prime-field estimate is
preserved by taking an additive power and reindexing its variables. -/
theorem primeIsolatedLeadingCriticalPoint_additivePowerPolynomialFin {l p r : ℕ}
    [Fact p.Prime] (k : ℕ) (g : MvPolynomial (Fin l) (ZMod p))
    (hg : PrimeIsolatedLeadingCriticalPoint p r g) :
    PrimeIsolatedLeadingCriticalPoint p r (additivePowerPolynomialFin k g) := by
  intro x hx
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  have h := additivePowerPolynomial_isolatedLeadingCriticalPoint k r g φ hg
    (x ∘ finProdFinEquiv) (fun b => ?_)
  · funext i
    obtain ⟨b, rfl⟩ := finProdFinEquiv.surjective i
    exact congrFun h b
  · have hz := hx (finProdFinEquiv b)
    change (pderiv (finProdFinEquiv b)
      (homogeneousComponent r (rename finProdFinEquiv (additivePowerPolynomial k g)))).eval₂
        φ x = 0 at hz
    rw [← rename_homogeneousComponent, pderiv_rename finProdFinEquiv.injective,
      eval₂_rename] at hz
    exact hz

/-- The count of additive power fibers is exactly the count of level sets
of the polynomial on the reindexed coordinates. -/
theorem additivePowerFiberCount_eq_card_eval_additivePowerPolynomialFin {l : ℕ}
    {R : Type*} [CommSemiring R] [Fintype R] (k : ℕ) (g : MvPolynomial (Fin l) R) (t : R) :
    additivePowerFiberCount (fun x => g.eval x) k t =
      (by
        classical
        exact (Finset.univ.filter fun x : Fin (k * l) → R =>
          (additivePowerPolynomialFin k g).eval x = t).card) := by
  classical
  let e : (Fin (k * l) → R) ≃ (Fin k → Fin l → R) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl R)).trans (Equiv.curry _ _ _)
  have hval (x : Fin (k * l) → R) :
      ∑ j, g.eval (e x j) = (additivePowerPolynomialFin k g).eval x := by
    exact (eval₂_additivePowerPolynomialFin k g (RingHom.id R) x).symm
  symm
  unfold additivePowerFiberCount
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hval, hx]
  · intro x _ y _ h
    exact e.injective h
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rwa [← hval, e.apply_symm_apply]


/-- The number of points in a level set of a polynomial over a finite ring. -/
def affinePolynomialLevelCount {n : ℕ} {R : Type*} [CommSemiring R] [Fintype R]
    (g : MvPolynomial (Fin n) R) (t : R) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Fin n → R => g.eval x = t).card

/-- A uniform affine level-set estimate over a prime field. The constant may
depend on the prime and degree, and applies in every ambient dimension. -/
def PrimeAffineLevelPointCountsWithBase (r : ℕ) (B : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      ∀ (g : MvPolynomial (Fin n) (ZMod p)), g.totalDegree ≤ r →
        PrimeIsolatedLeadingCriticalPoint p r g → ∀ (t : ZMod p), t ≠ 0 →
        |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤
          C * (B^n * (p : ℝ)^((n : ℝ)/2))

/-- Uniform affine level counts with Deligne's sharp exponential base. -/
def PrimeAffineLevelPointCounts (r : ℕ) : Prop :=
  PrimeAffineLevelPointCountsWithBase r ((r : ℝ) - 1)

/-- A bound in dimensions at least `N` suffices, since the lower dimensions
can be counted trivially with a constant depending on the prime. -/
theorem primeAffineLevelPointCountsWithBase_of_large_dimension {r : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (N : ℕ)
    (hcount : ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n → N ≤ n →
        ∀ (g : MvPolynomial (Fin n) (ZMod p)), g.totalDegree ≤ r →
          PrimeIsolatedLeadingCriticalPoint p r g → ∀ (t : ZMod p), t ≠ 0 →
          |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤
            C * (B^n * (p : ℝ)^((n : ℝ)/2))) : PrimeAffineLevelPointCountsWithBase r B := by
  classical
  intro p _ _ hp
  obtain ⟨C,hC,hlarge⟩ := hcount p hp
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  refine ⟨C+(p : ℝ)^N, by positivity, ?_⟩
  intro n hn g hg hcrit t ht
  by_cases hN : N ≤ n
  · exact (hlarge n hn hN g hg hcrit t ht).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity))
  · have hsize : (affinePolynomialLevelCount g t : ℝ) ≤ (p : ℝ)^n := by
      have hc : affinePolynomialLevelCount g t ≤ p^n := by
        have hcard : (Finset.univ : Finset (Fin n → ZMod p)).card = p^n := by
          simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
        rw [← hcard, affinePolynomialLevelCount]
        apply Finset.card_le_card
        exact fun x _ => Finset.mem_univ x
      exact_mod_cast hc
    have hmean : (p : ℝ)^(n-1) ≤ (p : ℝ)^n := pow_le_pow_right₀ hp₁ (Nat.sub_le _ _)
    have hdiff : |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤ (p : ℝ)^n := by
      refine abs_le.mpr ⟨?_,?_⟩ <;>
        linarith [show (0 : ℝ) ≤ (affinePolynomialLevelCount g t : ℝ) by positivity,
          show (0 : ℝ) ≤ (p : ℝ)^(n-1) by positivity]
    refine hdiff.trans ((pow_le_pow_right₀ hp₁ (Nat.le_of_not_ge hN)).trans ?_)
    have hbase : (1 : ℝ) ≤ B^n * (p : ℝ)^((n : ℝ)/2) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) (Real.one_le_rpow hp₁ (by positivity))
    exact (le_add_of_nonneg_left hC).trans (le_mul_of_one_le_right (by positivity) hbase)

/-- The sharp-base affine bound may be restricted to large dimensions. -/
theorem primeAffineLevelPointCounts_of_large_dimension {r : ℕ} (hr : 2 ≤ r) (N : ℕ)
    (hcount : ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n → N ≤ n →
        ∀ (g : MvPolynomial (Fin n) (ZMod p)), g.totalDegree ≤ r →
          PrimeIsolatedLeadingCriticalPoint p r g → ∀ (t : ZMod p), t ≠ 0 →
          |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤
            C * (((r : ℝ)-1)^n * (p : ℝ)^((n : ℝ)/2))) : PrimeAffineLevelPointCounts r :=
  primeAffineLevelPointCountsWithBase_of_large_dimension
    (by
      have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
      linarith) N hcount

/-- The uniform level-set bound applies to each of the additive powers of
the original phase, with the same constant. -/
theorem primeExponentialFiberCounts_of_affineLevelPointCountsWithBase {r : ℕ} {B : ℝ}
    (hcount : PrimeAffineLevelPointCountsWithBase r B) : PrimeExponentialFiberCounts r B := by
  intro l p _ _ hl hrp g hg hcrit
  obtain ⟨C, hC, hcount⟩ := hcount p hrp
  refine ⟨C, hC, fun k hk t ht => ?_⟩
  have hscale :
      B^(k*l) * (p : ℝ)^(((k*l : ℕ) : ℝ)/2) = (B^l * (p : ℝ)^((l : ℝ)/2))^k := by
    rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (Nat.cast_nonneg p),
      Nat.mul_comm k l, Nat.cast_mul]
    congr 2
    ring
  have hlevel : additivePowerFiberCount (fun x => g.eval x) k t =
      affinePolynomialLevelCount (additivePowerPolynomialFin k g) t := by
    rw [additivePowerFiberCount_eq_card_eval_additivePowerPolynomialFin,
      affinePolynomialLevelCount]
  rw [hlevel, ← hscale, Nat.mul_comm l k]
  exact hcount (k*l) (Nat.mul_pos hk hl) (additivePowerPolynomialFin k g)
    ((totalDegree_additivePowerPolynomialFin_le k g).trans hg)
    (primeIsolatedLeadingCriticalPoint_additivePowerPolynomialFin k g hcrit) t ht

/-- Sharp-base affine counts give the sharp additive fiber counts. -/
theorem primeDeligneFiberCounts_of_affineLevelPointCounts {r : ℕ}
    (hcount : PrimeAffineLevelPointCounts r) : PrimeDeligneFiberCounts r :=
  primeExponentialFiberCounts_of_affineLevelPointCountsWithBase hcount

/-- An exponential affine bound gives the prime-field sum estimate with
that same base. -/
theorem primeExponentialSumBound_of_affineLevelPointCountsWithBase {r : ℕ} {B : ℝ}
    (hB : 0 < B) (hcount : PrimeAffineLevelPointCountsWithBase r B) : PrimeExponentialSumBound r B :=
  primeExponentialSumBound_of_fiberCounts hB
    (primeExponentialFiberCounts_of_affineLevelPointCountsWithBase hcount)

/-- Uniform affine level counts imply the sharp prime-field character-sum estimate. -/
theorem primeDeligneEstimate_of_affineLevelPointCounts {r : ℕ} (hr : 2 ≤ r)
    (hcount : PrimeAffineLevelPointCounts r) : PrimeDeligneEstimate r :=
  primeDeligneEstimate_of_fiberCounts hr (primeDeligneFiberCounts_of_affineLevelPointCounts hcount)

end
end Birch
