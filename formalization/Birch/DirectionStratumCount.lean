import Birch.BoundedProjectionCount
import Birch.DirectionStratumEquations
import Birch.PrimeDirectionCount
import Birch.UniformSystemCertificate

/-! # Uniform counts for the homogeneous direction strata -/

open MvPolynomial Matrix

namespace Birch

open scoped Classical in
set_option maxHeartbeats 1000000 in
/-- The same projection certificate controls integer boxes and the whole
prime-field direction space. -/
private theorem directionStratumCounts {n r j s : ℕ} (hr : 2 < r) (hj : j ≤ n)
    (hsj : s < j) :
    ∃ B D C : ℕ, 0 < D ∧ 0 < C ∧ ∀ (p : ℕ) (hp : p.Prime), r < p → B < p →
      ∀ G : IntForm n, G.IsHomogeneous r → PrimeGradientDimension p hp G s →
      letI : NeZero p := ⟨hp.ne_zero⟩
      (∀ H : ℝ, 1 ≤ H → 2 * H ≤ (p : ℝ) →
        (((differencingDirections n H).filter
          (fun u => PrimeGradientDimension p hp (directionalDerivative u G) j)).card : ℝ) ≤
          (C : ℝ) * H^(n+s-j)) ∧
      (Finset.univ.filter (fun u : Fin n → ZMod p =>
        PrimeGradientDimension p hp (directionalDerivative (fun i => (u i).val) G) j)).card ≤
          D * p^(n+s-j) := by
  classical
  let i₀ : Fin n := ⟨0, by omega⟩
  let k := j-1
  let l := n+s-j
  have hk : k < n := by dsimp [k]; omega
  have hjk : k+1 = j := by dsimp [k]; omega
  obtain ⟨D,hD,htest⟩ := exists_uniform_system_macaulay_degree n (n+k) (r-2)
  let q := Fintype.card (DegreeMonomial n D)
  have hq : 0 < q := Fintype.card_pos_iff.mpr ⟨⟨Finsupp.single i₀ D,Finsupp.degree_single _ _⟩⟩
  let B := (r-2)*q
  let I := DirectionTestIndex n k (r-2) D B
  let m := Fintype.card I
  let index : Fin m ≃ I := (Fintype.equivFin I).symm
  obtain ⟨D',hD',htest'⟩ := exists_uniform_system_macaulay_degree n (m+l) q
  let B' := q * Fintype.card (DegreeMonomial n D')
  have hD'pos : 0 < D' := hq.trans hD'
  refine ⟨max B B', D'^n, D'^n * (3*(n*B'+1))^l, by positivity, by positivity, ?_⟩
  intro p hp hrp hpmax G hG hs
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let g : MvPolynomial (Fin n) K := MvPolynomial.map (Int.castRingHom K) G
  let f (i : Fin m) : MvPolynomial (Fin n) K := directionTest g (index i)
  let J := Ideal.span (Set.range f)
  have hgp : g.IsHomogeneous r := hG.map _
  have hfp (i : Fin m) : (f i).IsHomogeneous q := directionTest_isHomogeneous g (index i)
  have hBn : B < p := (le_max_left _ _).trans_lt hpmax
  have hB'n : B' < p := (le_max_right _ _).trans_lt hpmax
  have hchar : ((r-1 : ℕ) : K) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff K p (r-1)).mp h
    have hlep := Nat.le_of_dvd (by omega : 0 < r-1) hdiv
    omega
  have hsg : ringKrullDim (MvPolynomial (Fin n) K ⧸
      Ideal.span (Set.range fun i => pderiv i g)) ≤ (s : WithBot ℕ∞) := by
    have hfun : (fun i : Fin n => pderiv i g) =
        fun i => MvPolynomial.map (Int.castRingHom K) (pderiv i G) :=
      funext fun _ => pderiv_map
    rw [hfun]
    exact hs.le
  have hexact {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] (u : Fin n → L) :
      (∀ a : I, aeval u (directionTest g a) = 0) ↔
        (j : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) L ⧸
          Ideal.span (Set.range fun i : Fin n => pderiv i
            (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) g)))) := by
    letI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
    have h := directionTests_zero_iff hgp hr hk hD hBn (fun v hv => (htest v hv).mp) u
    rwa [hjk] at h
  have hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ J) ≤ (l : WithBot ℕ∞) := by
    apply ringKrullDim_hessianDirectionStratum_le hgp (by omega) hchar hsg J
    intro L _ _ _ u hu
    apply (hexact u).mp
    intro a
    change directionTest g a ∈ RingHom.ker (aeval u).toRingHom
    exact hu (Ideal.subset_span ⟨index.symm a, by simp [f]⟩)
  obtain ⟨b,hb,sel,hsel⟩ := exists_bounded_macaulay_cuts i₀ hq hB'n f hfp hdim
    (one_ne_zero : (1 : K) ≠ 0) (fun v hv => (htest' v hv).mp)
  have hmem (a : Fin n →₀ ℕ) (ha : a.degree = D') : monomial a (1 : K) ∈
      Ideal.span (Set.range (Fin.append f
        (fun j => (normalLinearForm (fun i => (b j i : K))) ^ q))) := by
    have hmem := system_monomial_mem_of_macaulay_minor
      (cutPolynomialSystem_isHomogeneous f 1 (fun j i => (b j i : K)) hfp) hD'.le sel hsel ha
    simpa only [cutPolynomialSystem, map_one, one_mul] using hmem
  have hzero (u : Fin n → ℤ) (hu : PrimeGradientDimension p hp (directionalDerivative u G) j)
      (i : Fin m) : (f i).eval (fun k => (u k : K)) = 0 := by
    have hbad := mem_primeBadDirectionLocus_of_dim G u hu
    let uK (j : Fin n) : K := u j
    have huK : (j : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸
        Ideal.span (Set.range fun i : Fin n => pderiv i
          (directionalDerivativeOver uK (MvPolynomial.map (algebraMap K K) g)))) := by
      rw [Algebra.algebraMap_self, MvPolynomial.map_id]
      exact hbad
    change (f i).eval uK = 0
    rw [← aeval_eq_eval]
    exact (hexact uK).mpr huK (index i)
  letI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · intro H hH hpH
    let P (u : Fin n → ℤ) := PrimeGradientDimension p hp (directionalDerivative u G) j
    have hcount := card_differencingDirections_subset_le_of_projection hH hpH hq hD'.le
      f hfp b hb hmem ((differencingDirections n H).filter P) (Finset.filter_subset _ _)
      (fun u hu => hzero u (Finset.mem_filter.mp hu).2)
    push_cast
    exact hcount
  · let φ := algebraMap (ZMod p) K
    let b₀ (j : Fin l) (i : Fin n) : ZMod p := b j i
    have hb₀ (j : Fin l) : φ ∘ b₀ j = fun i => (b j i : K) := by
      ext i
      exact map_natCast φ _
    have hproj := card_finiteField_subset_le_of_projection φ hq hD'.le f hfp b₀
      (by simpa only [hb₀] using hmem)
      (Finset.univ.filter (fun u : Fin n → ZMod p =>
        PrimeGradientDimension p hp (directionalDerivative (fun i => (u i).val) G) j))
      (fun u hu i => by
        have H := hzero (fun i => (u i).val) (Finset.mem_filter.mp hu).2 i
        have heq : (fun i => (((u i).val : ℤ) : K)) = φ ∘ u := by
          ext i
          dsimp [φ, Function.comp_def]
          rw [Int.cast_natCast, ← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_zmod_val]
        rw [← heq]
        exact H)
    simpa only [ZMod.card] using hproj

/-- The direction loci have the uniform counting bound required by the
completion step. -/
theorem largePrimeDirectionCount {n r j : ℕ} (hr : 2 < r) (hj : j ≤ n) :
    LargePrimeDirectionCount n r j := by
  classical
  apply largePrimeDirectionCount_of_fixed_s
  intro s hsj
  obtain ⟨B, _, C, _, hC, h⟩ := directionStratumCounts hr hj hsj
  exact ⟨B, C, Nat.cast_pos.mpr hC, fun p hp hrp hpmax G hG hs =>
    (h p hp hrp hpmax G hG hs).1⟩

open scoped Classical in
/-- If a direction raises the gradient dimension from `s` to `j`, its
stratum has codimension at least `j-s` over all sufficiently large primes. -/
theorem finiteFieldDirectionCount {n r j s : ℕ} (hr : 2 < r) (hj : j ≤ n)
    (hsj : s < j) :
    ∃ B D : ℕ, 0 < D ∧ ∀ (p : ℕ) (hp : p.Prime), r < p → B < p →
      ∀ G : IntForm n, G.IsHomogeneous r → PrimeGradientDimension p hp G s →
      letI : NeZero p := ⟨hp.ne_zero⟩
      (Finset.univ.filter (fun u : Fin n → ZMod p =>
        PrimeGradientDimension p hp (directionalDerivative (fun i => (u i).val) G) j)).card ≤
          D * p^(n+s-j) := by
  obtain ⟨B, D, _, hD, _, h⟩ := directionStratumCounts hr hj hsj
  exact ⟨B, D, hD, fun p hp hrp hpmax G hG hs => (h p hp hrp hpmax G hG hs).2⟩

/-- The dimension-jump count holds at every prime in the completion range. -/
theorem primeDirectionBound (n d : ℕ) : PrimeDirectionBound n d :=
  primeDirectionBound_of_largePrimeCounts (fun _ _ he _ hj => largePrimeDirectionCount he hj)

end Birch
