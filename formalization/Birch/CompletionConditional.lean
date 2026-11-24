import Birch.DifferencingChain
import Birch.GoodReduction
import Birch.Metric
import Mathlib.RingTheory.KrullDimension.Basic

/-! # Completion conditional on geometric direction counts and the terminal estimate

The finite shift selection and the full differencing chain are checked here.
The two analytic inputs are the direction counts attached to geometric singular
dimensions and the completed terminal sum with its uniform power of `Q`.
-/

open Filter MvPolynomial
open scoped BigOperators Topology

namespace Birch

noncomputable section

/-- The dimension of the critical locus of `G` over the algebraic closure of the
prime field, using the coordinate ring of the gradient equations. -/
def PrimeGradientDimension {n : ℕ} (p : ℕ) (hp : p.Prime) (G : IntForm n) (s : ℕ) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let J : Ideal (MvPolynomial (Fin n) K) := Ideal.span
    (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom K) (MvPolynomial.pderiv j G))
  ringKrullDim (MvPolynomial (Fin n) K ⧸ J) = (s : ℕ∞)

/-- The gradient dimension over the algebraic closure of the prime field
is at most `σ` at every sufficiently large prime. -/
def EventualPrimeGradientDimensionLE {n : ℕ} (F : IntForm n) (σ : ℕ) : Prop :=
  ∃ B : ℕ, ∀ p > B, ∀ hp : p.Prime, ∃ s ≤ σ, PrimeGradientDimension p hp F s


/-- A gradient locus consisting of the origin has dimension zero. -/
theorem primeGradientDimension_zero_of_goodReduction {n p : ℕ} (hp : p.Prime) (G : IntForm n)
    (hgrad : ∀ (K : Type) [Field K] [CharP K p], ∀ x : Fin n → K,
      (∀ j, evalForm (pderiv j G) x = 0) ↔ x = 0) : PrimeGradientDimension p hp G 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let R := MvPolynomial (Fin n) K
  let J : Ideal R := Ideal.span
    (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom K) (MvPolynomial.pderiv j G))
  let I : Ideal R := MvPolynomial.vanishingIdeal K ({0} : Set (Fin n → K))
  have hmap (g : IntForm n) (x : Fin n → K) :
      MvPolynomial.aeval x (MvPolynomial.map (Int.castRingHom K) g) = evalForm g x := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, evalForm]
    congr 1
  have hzero : MvPolynomial.zeroLocus K J = ({0} : Set (Fin n → K)) := by
    ext x
    rw [Set.mem_singleton_iff, ← hgrad K x, show J = Ideal.span _ from rfl, MvPolynomial.zeroLocus_span]
    simp only [Set.mem_setOf_eq, Set.forall_mem_range, hmap]
  have hrad : J.radical = I := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K), hzero]
  have hmax : I.IsMaximal := inferInstance
  have hproper : J ≠ ⊤ := by
    intro h
    apply hmax.ne_top
    rw [← hrad, h, Ideal.radical_top]
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  letI : Nonempty (PrimeSpectrum (R ⧸ J)) := PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance
  let e := Ideal.Quotient.mk J
  have he (x : PrimeSpectrum (R ⧸ J)) : I = x.asIdeal.comap e := by
    have hx : (x.asIdeal.comap e).IsPrime := inferInstance
    apply hmax.eq_of_le hx.ne_top
    rw [← hrad, ← hx.radical]
    apply Ideal.radical_mono
    intro g hg
    change e g ∈ x.asIdeal
    rw [show e g = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hg]
    exact Ideal.zero_mem _
  letI : Subsingleton (PrimeSpectrum (R ⧸ J)) := ⟨fun x y => by
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective e Ideal.Quotient.mk_surjective
    exact (he x).symm.trans (he y)⟩
  change ringKrullDim (R ⧸ J) = 0
  exact Order.krullDim_eq_zero

/-- Direction and terminal estimates at a single terminal degree. -/
def CompletionInputsAt {n : ℕ} (d r : ℕ) (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ K > 0, ∃ T > 0,
    ∀ᶠ P : ℝ in atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ P ^ (1 / 2 : ℝ) →
    ∀ p : ℕ, ∀ hp : p.Prime, (P / Q) ^ (2 : ℕ) < (p : ℝ) → (p : ℝ) ≤ 2 * (P / Q) ^ (2 : ℕ) →
    ∃ s : ℕ → IntForm n → Fin (n+1),
      (∀ i ≤ d-r, ∀ g : IntForm n,
        PrimeGradientDimension p hp (homogeneousComponent (d-i) g) (s i g).val) ∧
      ∀ m : ℕ → ℤ, (∀ i < d-r, 0 < m i ∧ (m i : ℝ) * differencingHeight (d-r) Q i ≤ P) →
        PolynomialDirectionCounts (k := d-r) d Q m s K ∧
        ∀ (a : ℤ) (α : ℝ), ¬ (p : ℤ) ∣ a →
          |(∏ j ∈ Finset.range (d-r), (m j : ℝ)) * α - (a : ℝ)/(p : ℝ)| ≤ completionRadius d r P Q →
          ∀ (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
            IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
              (t (d-r)).magnitude P ≤ T * Q ^ (-((n - (s (d-r) (t (d-r)).form).val : ℕ) : ℝ))

/-- The remaining inputs for `prop:completion`. The dimension is attached to the
specified leading homogeneous component. The terminal bound is uniform over
all chains obeying the actual shift budgets. -/
def CompletionInputs {n : ℕ} (d : ℕ) (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ r : ℕ, 2 ≤ r → r < d → CompletionInputsAt d r F w

/-- An admissible product gives an integral chain with the required step budgets. -/
lemma factors_of_admissibleProduct {d r M : ℕ} {P Q : ℝ}
    (h : admissibleProduct d r P Q M) :
    ∃ m : ℕ → ℤ, (∏ j ∈ Finset.range (d-r), (m j : ℝ)) = (M : ℝ) ∧
      ∀ i < d-r, 0 < m i ∧ (m i : ℝ) * differencingHeight (d-r) Q i ≤ P := by
  obtain ⟨m₀, hmprod, hm₀⟩ := h
  let m : ℕ → ℤ := fun i => if h : i < d-r then (m₀ ⟨i,h⟩ : ℤ) else 1
  refine ⟨m, ?_, ?_⟩
  · rw [← Fin.prod_univ_eq_prod_range]
    have hm (i : Fin (d-r)) : (m i : ℝ) = (m₀ i : ℝ) := by simp [m, i.isLt]
    simp_rw [hm]
    exact_mod_cast hmprod
  · intro i hi
    obtain ⟨hmi, hmb⟩ := hm₀ ⟨i,hi⟩
    have he : d-r-(i+1) = d-r-1-i := by omega
    refine ⟨?_, ?_⟩
    · simpa [m, hi] using hmi
    · simpa [m, hi, differencingHeight, he] using hmb

/-- At one terminal degree the completed sum and the direction counts give
the full differencing estimate at the starting codimension. -/
theorem completionBound_of_gradientDim {d n r σ : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.totalDegree ≤ d) (hw : CubeSupported w)
    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    ∃ C > 0, ∀ {P Q : ℝ}, 1 ≤ P → 1 ≤ Q → ∀ {M : ℕ},
      admissibleProduct d r P Q M → ∀ (α : ℝ) (s : ℕ → IntForm n → Fin (n+1)),
      (s 0 F).val ≤ σ →
      (∀ m : ℕ → ℤ, (∏ j ∈ Finset.range (d-r), (m j : ℝ)) = (M : ℝ) →
        (∀ i < d-r, 0 < m i ∧ (m i : ℝ) * differencingHeight (d-r) Q i ≤ P) →
        PolynomialDirectionCounts (k := d-r) d Q m s K ∧
          ∀ (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
            IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
            (t (d-r)).magnitude P ≤ T * Q ^ (-((n - (s (d-r) (t (d-r)).form).val : ℕ) : ℝ))) →
      ‖normalizedSum F w P α‖ ≤ C * Q ^ (-(((n - σ : ℕ) : ℝ) / (2 : ℝ)^(d-r))) := by
  let k := d-r
  let R : ℕ := 2^k
  let C₀ : ℝ := (10 : ℝ)^n * ((n : ℝ)+1) * K
  let D : ℝ := C₀^(R-1) * T
  let C : ℝ := D ^ (1/(R : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  have hR' : (0 : ℝ) < R := Nat.cast_pos.mpr hR
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := Real.rpow_pos_of_pos hD _
  have hCpow : C^R = D := by
    dsimp only [C]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, one_div, inv_mul_cancel₀ hR'.ne', Real.rpow_one]
  refine ⟨C, hC, ?_⟩
  intro P Q hP hQ M hM α s hs₀ hstates
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  obtain ⟨m, hmprod, hm⟩ := factors_of_admissibleProduct hM
  obtain ⟨hcount, hterminal⟩ := hstates m hmprod hm
  obtain ⟨t,u,hchain,_,hselected⟩ :=
    exists_selectedPolynomialChain_from_dimension hP hQ hK.le m hm F hF w hw α s hcount
  have hterm := hterminal t u hchain
  let l : ℕ := (s k (t k).form).val
  have hl : l ≤ n := Nat.lt_succ_iff.mp (s k (t k).form).isLt
  let j : ℕ := l - (s 0 F).val
  let ν : ℕ := n - σ
  have hν : ν ≤ j + (n-l) := by
    dsimp [ν, j]
    omega
  have he : -(j : ℝ) + -((n-l : ℕ) : ℝ) ≤ -(ν : ℝ) := by
    have h := (Nat.cast_le (α := ℝ)).mpr hν
    push_cast at h
    linarith
  have hbound : (‖exponentialSum F w P α‖ / P^n)^R ≤ D * Q ^ (-(ν : ℝ)) := by
    change (‖exponentialSum F w P α‖ / P^n)^R ≤
      C₀^(R-1) * Q ^ (-(j : ℝ)) * (t k).magnitude P at hselected
    refine hselected.trans ?_
    calc
      _ ≤ C₀^(R-1) * Q ^ (-(j : ℝ)) * (T * Q ^ (-((n-l : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = D * Q ^ (-(j : ℝ) + -((n-l : ℕ) : ℝ)) := by
        rw [Real.rpow_add hQpos]
        dsimp [D]
        ring
      _ ≤ D * Q ^ (-(ν : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ he) hD.le
  have hqpow : (Q ^ (-((ν : ℝ) / (2 : ℝ)^k)))^R = Q ^ (-(ν : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
    congr 1
    have hRcast : (R : ℝ) = (2 : ℝ)^k := by dsimp [R]; push_cast; rfl
    rw [hRcast]
    field_simp
  have hnorm : ‖normalizedSum F w P α‖ = ‖exponentialSum F w P α‖ / P^n := by
    rw [normalizedSum, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hPpos.le _),
      Real.rpow_neg hPpos.le, Real.rpow_natCast, inv_mul_eq_div]
  rw [hnorm]
  change ‖exponentialSum F w P α‖ / P^n ≤ C * Q ^ (-((ν : ℝ)/(2 : ℝ)^k))
  apply le_of_pow_le_pow_left₀ hR.ne' (by positivity)
  rwa [mul_pow, hCpow, hqpow]

/-- The original completion bound at initial gradient dimension zero. -/
theorem completionBound_of_directionCounts_terminal {d n r : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.totalDegree ≤ d) (hw : CubeSupported w)
    {K T : ℝ} (hK : 0 < K) (hT : 0 < T) :
    ∃ C > 0, ∀ {P Q : ℝ}, 1 ≤ P → 1 ≤ Q → ∀ {M : ℕ},
      admissibleProduct d r P Q M → ∀ (α : ℝ) (s : ℕ → IntForm n → Fin (n+1)),
      (s 0 F).val = 0 →
      (∀ m : ℕ → ℤ, (∏ j ∈ Finset.range (d-r), (m j : ℝ)) = (M : ℝ) →
        (∀ i < d-r, 0 < m i ∧ (m i : ℝ) * differencingHeight (d-r) Q i ≤ P) →
        PolynomialDirectionCounts (k := d-r) d Q m s K ∧
          ∀ (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
            IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
            (t (d-r)).magnitude P ≤ T * Q ^ (-((n - (s (d-r) (t (d-r)).form).val : ℕ) : ℝ))) →
      ‖normalizedSum F w P α‖ ≤ C * Q ^ (-((n : ℝ) / (2 : ℝ)^(d-r))) := by
  obtain ⟨C, hC, h⟩ := completionBound_of_gradientDim (r := r) (σ := 0) hF hw hK hT
  refine ⟨C, hC, ?_⟩
  intro P Q hP hQ M hM α s hs₀ hstates
  simpa only [Nat.sub_zero] using h hP hQ hM α s hs₀.le hstates

/-- At a fixed terminal degree, the completion inputs give the prime-denominator
estimate for forms of bounded reduced gradient dimension. -/
theorem completionEstimateAt_of_gradientDim {d n r σ : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hs : EventualPrimeGradientDimensionLE F σ)
    (hw : CubeSupported w) (hinput : CompletionInputsAt d r F w) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ∀ (Q : ℝ), 1 ≤ Q → Q ≤ P ^ (1 / 2 : ℝ) →
      ∀ (p M : ℕ), p.Prime → (P / Q) ^ (2 : ℕ) < (p : ℝ) →
        (p : ℝ) ≤ 2 * (P / Q) ^ (2 : ℕ) → admissibleProduct d r P Q M →
      ∀ (a : ℤ) (α : ℝ), ¬ (p : ℤ) ∣ a →
        |(M : ℝ) * α - (a : ℝ) / (p : ℝ)| ≤ completionRadius d r P Q →
        ‖normalizedSum F w P α‖ ≤ C * Q ^ (-(((n - σ : ℕ) : ℝ) / (2 : ℝ) ^ (d - r))) := by
  obtain ⟨K, hK, T, hT, hinput⟩ := hinput
  obtain ⟨C, hC, hcomplete⟩ := completionBound_of_gradientDim
    (r := r) (σ := σ) hF.totalDegree_le hw hK hT
  obtain ⟨B, hgood⟩ := hs
  refine ⟨C, hC, ?_⟩
  filter_upwards [hinput, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (B : ℝ)] with
    P hscales hP hPB Q hQ hQ' p M hp hpL hpU hM a α ha hclose
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  obtain ⟨s, hdim, hstates⟩ := hscales Q hQ hQ' p hp hpL hpU
  have hQsq : Q^2 ≤ P := by
    have := pow_le_pow_left₀ hQpos.le hQ' 2
    rwa [← Real.sqrt_eq_rpow, Real.sq_sqrt hPpos.le] at this
  have hPp : P ≤ (P/Q)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hQsq hPpos.le
  have hBp : B < p := by
    exact_mod_cast hPB.trans_lt (hPp.trans_lt hpL)
  have hdim0 : PrimeGradientDimension p hp F (s 0 F).val := by
    simpa only [Nat.sub_zero, homogeneousComponent_eq_self hF] using hdim 0 (Nat.zero_le _) F
  obtain ⟨j, hjσ, hj⟩ := hgood p hBp hp
  have heq : (s 0 F).val = j := by
    unfold PrimeGradientDimension at hdim0 hj
    exact_mod_cast hdim0.symm.trans hj
  have hs₀ : (s 0 F).val ≤ σ := heq ▸ hjσ
  exact hcomplete hP hQ hM α s hs₀ (fun m hmprod hm => by
    obtain ⟨hcount, hterminal⟩ := hstates m hm
    exact ⟨hcount, hterminal a α ha (by rwa [hmprod])⟩)

/-- The completion inputs retain the starting codimension in all terminal degrees. -/
theorem completionEstimate_of_gradientDim {d n σ : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d)
    (hs : EventualPrimeGradientDimensionLE F σ)
    (hw : CubeSupported w) (hinput : CompletionInputs d F w) :
    CompletionEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖) := by
  intro r hr hrd
  exact completionEstimateAt_of_gradientDim hF hs hw (hinput r hr hrd)

/-- The prime-denominator estimate for a geometrically smooth form. -/
theorem completionEstimateAt_of_directionCounts_terminal {d n r : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hw : CubeSupported w) (hinput : CompletionInputsAt d r F w) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop,
      ∀ (Q : ℝ), 1 ≤ Q → Q ≤ P ^ (1 / 2 : ℝ) →
      ∀ (p M : ℕ), p.Prime → (P / Q) ^ (2 : ℕ) < (p : ℝ) →
        (p : ℝ) ≤ 2 * (P / Q) ^ (2 : ℕ) → admissibleProduct d r P Q M →
      ∀ (a : ℤ) (α : ℝ), ¬ (p : ℤ) ∣ a →
        |(M : ℝ) * α - (a : ℝ) / (p : ℝ)| ≤ completionRadius d r P Q →
        ‖normalizedSum F w P α‖ ≤ C * Q ^ (-((n : ℝ) / (2 : ℝ) ^ (d - r))) := by
  obtain ⟨B, hgood⟩ := hs.eventually_goodReduction hF hd
  have hdim : EventualPrimeGradientDimensionLE F 0 :=
    ⟨B, fun p hp hprime => ⟨0, le_rfl,
      primeGradientDimension_zero_of_goodReduction hprime F (hgood p hp)⟩⟩
  simpa only [Nat.sub_zero] using completionEstimateAt_of_gradientDim hF hdim hw hinput

/-- Proposition `prop:completion` follows from the direction counts and the terminal
estimate in `CompletionInputs`. Good reduction makes the initial gradient dimension zero. -/
theorem completionEstimate_of_directionCounts_terminal {d n : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hw : CubeSupported w) (hinput : CompletionInputs d F w) :
    CompletionEstimate d n (fun P α => ‖normalizedSum F w P α‖) := by
  intro r hr hrd
  exact completionEstimateAt_of_directionCounts_terminal (by omega) hF hs hw (hinput r hr hrd)

end

end Birch
