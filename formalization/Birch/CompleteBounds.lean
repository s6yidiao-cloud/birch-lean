import Birch.BadPrimes
import Birch.SingularSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Uniform complete-sum bounds from the conductor-one estimate

The input is decay at conductor one outside a finite set of primes.
The deduction to prime powers and composite moduli accounts for each
exceptional prime only once. Deligne's estimate supplies one such input.
-/

open Filter MeasureTheory MvPolynomial ZMod
open scoped Topology

namespace Birch

noncomputable section

/-- Deligne's conductor-one estimate in the normalization of Section 5.
The leading form is homogeneous of degree `d` in the applications. -/
def DeligneConductorOne {n : ℕ} (d : ℕ) (F : IntForm n) : Prop :=
  ∀ (p : ℕ) (_ : Fact p.Prime) [NeZero p], d < p →
    (∀ x : Fin n → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i F) x = 0) ↔ x = 0) →
    ∀ a : ZMod p, a ≠ 0 →
      ‖completeSum F p a‖ ≤ ((d : ℝ) - 1) ^ n * (p : ℝ) ^ (-(n : ℝ) / 2)

/-- The conductor-one sum has decay with exponent `s` and a constant
uniform in the prime and unit numerator. The form and its dimension are fixed. -/
def UniformConductorOnePowerBound {n : ℕ} (d : ℕ) (F : IntForm n) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) (_ : Fact p.Prime) [NeZero p], d < p →
    (∀ x : Fin n → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i F) x = 0) ↔ x = 0) →
    ∀ a : ZMod p, a ≠ 0 →
      ‖completeSum F p a‖ ≤ C * (p : ℝ)^(-s)

/-- The square-root case of uniform conductor-one decay. -/
abbrev UniformConductorOneBound {n : ℕ} (d : ℕ) (F : IntForm n) : Prop :=
  UniformConductorOnePowerBound d F ((n : ℝ)/2)

/-- The conductor-one decay of exponent `κ` outside finitely many primes. -/
def EventualConductorOnePowerBound {n : ℕ} (d : ℕ) (F : IntForm n) (κ : ℝ) : Prop :=
  ∃ B : ℕ, ∀ (p : ℕ) (_ : Fact p.Prime) [NeZero p], B < p → d < p →
    (∀ x : Fin n → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i F) x = 0) ↔ x = 0) →
    ∀ a : ZMod p, a ≠ 0 → ‖completeSum F p a‖ ≤ (p : ℝ)^(-κ)

/-- The decay at conductor one used in the manuscript's modulus factorization. -/
abbrev EventualConductorOneBound {n : ℕ} (d : ℕ) (F : IntForm n) : Prop :=
  EventualConductorOnePowerBound d F ((n : ℝ) / d)

/-- The explicit Deligne constant supplies the uniform square-root bound. -/
theorem uniformConductorOneBound_of_deligne {n d : ℕ} {F : IntForm n}
    (hDel : DeligneConductorOne d F) : UniformConductorOneBound d F := by
  refine ⟨max 1 (((d : ℝ)-1)^n), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro p hp _ hdp hgood a ha
  rw [← neg_div]
  exact (hDel p hp hdp hgood a ha).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- A strict power saving over the conductor exponent absorbs any fixed
leading constant into a finite set of exceptional primes. -/
theorem eventualConductorOneBound_of_uniform_power {n d : ℕ} {F : IntForm n}
    {s : ℝ} (hs : (n : ℝ)/d < s) (h : UniformConductorOnePowerBound d F s) :
    EventualConductorOneBound d F := by
  obtain ⟨C, _, hC⟩ := h
  let θ : ℝ := s - (n : ℝ)/d
  have hθ : 0 < θ := sub_pos.mpr hs
  obtain ⟨Y, hY⟩ := eventually_atTop.mp <|
    (tendsto_rpow_atTop hθ).eventually_ge_atTop C
  refine ⟨⌈Y⌉₊, fun p hp _ hlarge hdp hgood a ha => (hC p hp hdp hgood a ha).trans ?_⟩
  have hCp : C ≤ (p : ℝ)^θ := hY _ ((Nat.le_ceil _).trans (by exact_mod_cast hlarge.le))
  calc
    _ ≤ (p : ℝ)^θ * (p : ℝ)^(-s) := mul_le_mul_of_nonneg_right hCp (by positivity)
    _ = _ := by
      rw [← Real.rpow_add (Nat.cast_pos.mpr hp.out.pos)]
      congr 1
      dsimp [θ]
      ring

/-- In degree at least three, a uniform square-root bound has enough
decay for the large-prime conductor-one input. -/
theorem eventualConductorOneBound_of_uniform {n d : ℕ} {F : IntForm n}
    (hd : 3 ≤ d) (hn : 0 < n) (h : UniformConductorOneBound d F) :
    EventualConductorOneBound d F := by
  apply eventualConductorOneBound_of_uniform_power _ h
  have hh : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hnn : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < d)]
  nlinarith

/-- The trivial bound for an average of values of a unitary character. -/
theorem norm_completeSum_le_one {n q : ℕ} [NeZero q] (F : IntForm n) (a : ZMod q) :
    ‖completeSum F q a‖ ≤ 1 := by
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hf (x : Fin n → ZMod q) : ‖stdAddChar (a * residueEval F q x)‖ = 1 := by
    rw [stdAddChar_apply]
    exact (toCircle (N := q) (a * residueEval F q x)).norm_coe
  rw [completeSum, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ ((q : ℝ)^n)⁻¹ * ∑ x : Fin n → ZMod q, ‖stdAddChar (a * residueEval F q x)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = 1 := by
      simp only [hf, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_pi,
        ZMod.card, Finset.prod_const, Fintype.card_fin, Nat.cast_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ hq.ne')

private theorem norm_of_power_recurrence (d n D p : ℕ) (hD : d ≤ D) (hd : 0 < d)
    (hp : 1 ≤ p) (A : ℕ → ℂ) (C κ : ℝ) (hC : 0 ≤ C) (hκ : (d : ℝ) * κ ≤ n)
    (hbase : ∀ m < D, ‖A m‖ ≤ C * (p : ℝ)^(-((m : ℝ) * κ)))
    (hrec : ∀ m, D ≤ m → A m = ((p : ℂ)^n)⁻¹ * A (m - d)) :
    ∀ m, ‖A m‖ ≤ C * (p : ℝ)^(-((m : ℝ) * κ)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m < D
      · exact hbase _ hm
      have hdm := hD.trans (Nat.le_of_not_gt hm)
      have hr : 0 < (p : ℝ) := Nat.cast_pos.mpr (by omega)
      have he : -(n : ℝ) + -((↑(m - d) : ℝ) * κ) ≤ -((m : ℝ) * κ) := by
        rw [Nat.cast_sub hdm]
        linarith
      rw [hrec _ (Nat.le_of_not_gt hm), norm_mul, norm_inv, norm_pow, Complex.norm_natCast,
        ← Real.rpow_natCast, ← Real.rpow_neg hr.le]
      calc
        _ ≤ (p : ℝ)^(-(n : ℝ)) *
            (C * (p : ℝ)^(-((↑(m - d) : ℝ) * κ))) :=
          mul_le_mul_of_nonneg_left (ih _ (Nat.sub_lt (hd.trans_le hdm) hd)) (by positivity)
        _ ≤ _ := by
          rw [mul_left_comm, ← Real.rpow_add hr]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) he) hC

private theorem badPrime_norm_le {n d p : ℕ} [Fact p.Prime] [NeZero p]
    {F : IntForm n} (hs : ProjectivelySmooth F) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (m : ℕ) (a : ℤ), (a : ZMod p) ≠ 0 →
      ‖completeSum F (p ^ m) (a : ZMod (p ^ m))‖ ≤
        C * (p : ℝ)^(-((m : ℝ) * ((n : ℝ) / d))) := by
  obtain ⟨j, hj, hgrad⟩ := hs.exists_stationaryDepth hF hd p
  let D := max d (2 * j)
  have hp : p.Prime := Fact.out
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  let C := (p : ℝ)^((D : ℝ) * ((n : ℝ) / d))
  refine ⟨C, Real.one_le_rpow hpr (by positivity), fun m a ha ↦ ?_⟩
  have hκ : (d : ℝ) * ((n : ℝ) / d) ≤ n := by
    rw [mul_comm, div_mul_cancel₀ _ (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]
  apply norm_of_power_recurrence d n D p (le_max_left _ _) hd hp.one_lt.le
    (fun m ↦ completeSum F (p ^ m) (a : ZMod (p ^ m))) C _ (by positivity) hκ ?_ ?_ m
  · intro l hl
    refine (norm_completeSum_le_one _ _).trans ?_
    unfold C
    rw [← Real.rpow_add (Nat.cast_pos.mpr hp.pos)]
    apply Real.one_le_rpow hpr
    have hl' : (l : ℝ) ≤ D := by exact_mod_cast hl.le
    linarith [mul_le_mul_of_nonneg_right hl' (by positivity : 0 ≤ (n : ℝ) / d)]
  · intro l hl
    exact completeSum_primePower_recurrence_of_stationaryDepth F p l d j hj
      ((le_max_right _ _).trans hl) hF hd hgrad a ha

private theorem goodPrime_norm_le {n d p : ℕ} [Fact p.Prime] [NeZero p]
    {F : IntForm n} (hF : F.IsHomogeneous d) (hd : 1 ≤ d)
    {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ : (d : ℝ) * κ ≤ n)
    (hgrad : ∀ x : Fin n → ZMod p, (∀ i, residueEval (pderiv i F) p x = 0) ↔ x = 0)
    (a : ℤ) (ha : (a : ZMod p) ≠ 0)
    (hfirst : ‖completeSum F p (a : ZMod p)‖ ≤ (p : ℝ)^(-κ)) :
    ∀ m, ‖completeSum F (p ^ m) (a : ZMod (p ^ m))‖ ≤
      (p : ℝ)^(-((m : ℝ) * κ)) := by
  have hp : p.Prime := Fact.out
  have hpr : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  intro m
  have H := norm_of_power_recurrence d n (d + 1) p (by omega) hd hp.one_lt.le
    (fun m ↦ completeSum F (p ^ m) (a : ZMod (p ^ m))) 1 κ zero_le_one hκ ?_ ?_ m
  · simpa only [one_mul] using H
  · intro l hl
    rcases l with _ | l
    · simp [completeSum_one]
    rcases l with _ | l
    · have H (q : ℕ) [NeZero q] (hq : q = p) :
          ‖completeSum F q (a : ZMod q)‖ ≤ (p : ℝ)^(-κ) := by
        subst q
        exact hfirst
      simpa only [Nat.zero_add, Nat.cast_one, one_mul] using H (p^1) (pow_one p)
    have hld : l + 2 ≤ d := by omega
    rw [completeSum_primePower_initial F p (l+2) d (by omega) hld hF hgrad a ha,
      norm_inv, norm_pow, Complex.norm_natCast, ← Real.rpow_natCast,
      ← Real.rpow_neg (by positivity), one_mul]
    apply Real.rpow_le_rpow_of_exponent_le hpr
    have hld' : ((l + 2 : ℕ) : ℝ) ≤ d := by exact_mod_cast hld
    have hm : ((l + 2 : ℕ) : ℝ) * κ ≤ (n : ℝ) :=
      (mul_le_mul_of_nonneg_right hld' hκ₀).trans hκ
    linarith
  · intro l hl
    exact completeSum_primePower_recurrence F p l d (by omega) hF hd hgrad a ha

/-- Eventual prime decay with exponent at most `n/d` extends to every modulus
with a constant independent of the modulus and numerator. -/
theorem completeSum_decay_of_eventual_conductorOne_power {n d : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ : κ ≤ (n : ℝ) / d)
    (hConductor : EventualConductorOnePowerBound d F κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      ‖completeSum F q a.val‖ ≤ C * (q : ℝ)^(-κ) := by
  classical
  have hκd : (d : ℝ) * κ ≤ n := by
    rw [mul_comm]
    exact (le_div_iff₀ (by exact_mod_cast (show 0 < d by omega))).mp hκ
  obtain ⟨Z, hZ⟩ := hs.eventually_goodReduction hF hd
  obtain ⟨Y, hY⟩ := hConductor
  let B := max Z (max d Y)
  have hB₁ (p : ℕ) (hp : B < p) : Z < p := (le_max_left _ _).trans_lt hp
  have hB₂ (p : ℕ) (hp : B < p) : d < p := (le_max_left _ _).trans
    (le_max_right Z (max d Y)) |>.trans_lt hp
  have hB₃ (p : ℕ) (hp : B < p) : Y < p :=
    ((le_max_right d Y).trans (le_max_right Z _)).trans_lt hp
  have hpoint : ∀ p : ℕ, ∃ K : ℝ, 1 ≤ K ∧ (B < p → K = 1) ∧
      ∀ (_ : Fact p.Prime) [NeZero p] (m : ℕ), 0 < m →
        ∀ a : (ZMod (p^m))ˣ, ‖completeSum F (p^m) a.val‖ ≤ K * (p^m : ℝ)^(-κ) := by
    intro p
    by_cases hprime : p.Prime
    · let : Fact p.Prime := ⟨hprime⟩
      let : NeZero p := ⟨hprime.ne_zero⟩
      let bound (K : ℝ) := ∀ (m : ℕ) (a : ℤ), (a : ZMod p) ≠ 0 →
        ‖completeSum F (p ^ m) (a : ZMod (p ^ m))‖ ≤ K * (p : ℝ)^(-((m : ℝ) * κ))
      have toUnit (K : ℝ) (hK : bound K) (m : ℕ) (hm : 0 < m) (a : (ZMod (p^m))ˣ) :
          ‖completeSum F (p^m) a.val‖ ≤ K * (p^m : ℝ)^(-κ) := by
        let red := ZMod.castHom (dvd_pow_self p hm.ne') (ZMod p)
        have ha : (a.val.val : ZMod p) ≠ 0 := by
          have H := (a.isUnit.map red).ne_zero
          rw [← ZMod.natCast_zmod_val a.val, map_natCast] at H
          exact H
        have H := hK m (a.val.val : ℤ) (by simpa only [Int.cast_natCast] using ha)
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at H
        convert H using 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 2
        ring
      by_cases hlarge : B < p
      · refine ⟨1, le_rfl, fun _ ↦ rfl, fun _ _ m hm a ↦ toUnit 1 ?_ m hm a⟩
        intro l b hb
        have hgrad : ∀ x : Fin n → ZMod p,
            (∀ i, residueEval (pderiv i F) p x = 0) ↔ x = 0 := hZ p (hB₁ p hlarge) (ZMod p)
        have hAlg : ∀ x : Fin n → AlgebraicClosure (ZMod p),
            (∀ i, evalForm (pderiv i F) x = 0) ↔ x = 0 :=
          hZ p (hB₁ p hlarge) (AlgebraicClosure (ZMod p))
        have hfirst := hY p (Fact.mk hprime) (hB₃ p hlarge) (hB₂ p hlarge)
          hAlg (b : ZMod p) hb
        simpa only [one_mul] using goodPrime_norm_le hF (by omega) hκ₀ hκd hgrad b hb hfirst l
      · obtain ⟨K, hK, hpow⟩ := badPrime_norm_le (p := p) hs hF (by omega)
        refine ⟨K, hK, fun h ↦ (hlarge h).elim, fun _ _ m hm a ↦ toUnit K ?_ m hm a⟩
        intro l b hb
        refine (hpow l b hb).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hprime.one_lt.le)
        exact neg_le_neg (mul_le_mul_of_nonneg_left hκ (by positivity))
    · exact ⟨1, le_rfl, fun _ ↦ rfl, fun h _ _ _ _ ↦ (hprime h.out).elim⟩
  choose K hK hKlarge hKpow using hpoint
  let L (q : ℕ) := ∏ p ∈ q.primeFactors, K p
  have hmul : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      ‖completeSum F q a.val‖ ≤ L q * (q : ℝ)^(-κ) := by
    intro q
    induction q using Nat.recOnPrimePow with
    | zero =>
        intro _
        exact (NeZero.ne (0 : ℕ) rfl).elim
    | one =>
        intro _ a
        simp [L, completeSum_one]
    | prime_pow_mul q p m hp hnot hm ih =>
        intro _ a
        let : NeZero p := ⟨hp.ne_zero⟩
        have hq₀ : q ≠ 0 := fun h ↦ hnot (h ▸ dvd_zero _)
        let : NeZero q := ⟨hq₀⟩
        have hcop : (p^m).Coprime q := (hp.coprime_iff_not_dvd.mpr hnot).pow_left m
        obtain ⟨b, c, hbc⟩ := completeSum_units_product F hcop a
        rw [hbc, norm_mul]
        have H := mul_le_mul (hKpow p (Fact.mk hp) m hm b) (ih c) (norm_nonneg _)
          (mul_nonneg (zero_le_one.trans (hK p)) (by positivity))
        refine H.trans_eq ?_
        unfold L
        rw [Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hq₀,
          Nat.primeFactors_prime_pow hm.ne' hp, Finset.singleton_union,
          Finset.prod_insert (fun h ↦ hnot (Nat.dvd_of_mem_primeFactors h)), Nat.cast_mul, Nat.cast_pow,
          Real.mul_rpow (by positivity) (by positivity)]
        ring
  let C := ∏ p ∈ Finset.range (B + 1), K p
  have hC : 1 ≤ C := Finset.one_le_prod₀ (fun p _ ↦ hK p)
  refine ⟨C, hC, fun q _ a ↦ (hmul q a).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hfilter : L q = ∏ p ∈ q.primeFactors.filter (· < B + 1), K p := by
    symm
    apply Finset.prod_filter_of_ne
    intro p _ hp
    by_contra! hv
    exact hp (hKlarge p (by omega))
  rw [hfilter]
  apply Finset.prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  · intro p _
    exact zero_le_one.trans (hK p)
  · intro p _ _
    exact hK p

/-- Eventual conductor-one decay gives the uniform complete-sum decay of Section 5. -/
theorem completeSum_decay_of_eventual_conductorOne {n d : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hConductor : EventualConductorOneBound d F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      ‖completeSum F q a.val‖ ≤ C * (q : ℝ)^(-((n : ℝ) / d)) :=
  completeSum_decay_of_eventual_conductorOne_power hd hF hs (by positivity) le_rfl hConductor

/-- A square-root bound uniform in the prime supplies the uniform
complete-sum decay over all moduli. -/
theorem completeSum_decay_of_uniform_conductorOne {n d : ℕ} {F : IntForm n}
    (hd : 3 ≤ d) (hn : 0 < n) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (h : UniformConductorOneBound d F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      ‖completeSum F q a.val‖ ≤ C * (q : ℝ)^(-((n : ℝ) / d)) :=
  completeSum_decay_of_eventual_conductorOne (by omega) hF hs
    (eventualConductorOneBound_of_uniform hd hn h)

/-- The uniform complete-sum power bound from Deligne's conductor-one estimate. -/
theorem completeSum_decay_of_deligne {n d : ℕ} {F : IntForm n} (hd : 3 ≤ d)
    (hn : 0 < n) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hDeligne : DeligneConductorOne d F) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      ‖completeSum F q a.val‖ ≤ C * (q : ℝ)^(-((n : ℝ) / d)) :=
  completeSum_decay_of_uniform_conductorOne hd hn hF hs
    (uniformConductorOneBound_of_deligne hDeligne)

/-- Summing the unit numerators gives the decay of singular-series coefficients. -/
theorem conductorSum_decay_of_eventual_conductorOne_power {n d : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ : κ ≤ (n : ℝ) / d)
    (h : EventualConductorOnePowerBound d F κ) :
    ∃ C > 0, ∀ j : ℕ, ‖unitConductorSum F (j + 1)‖ ≤
      C * ((j + 1 : ℕ) : ℝ) ^ (1 - κ) := by
  obtain ⟨C, hC, hbound⟩ := completeSum_decay_of_eventual_conductorOne_power hd hF hs hκ₀ hκ h
  refine ⟨C, zero_lt_one.trans_le hC, fun j ↦ ?_⟩
  let q := j + 1
  have hq : 0 < (q : ℝ) := by dsimp [q]; positivity
  have hcard : Fintype.card ((ZMod q)ˣ) ≤ q := by
    have h := Fintype.card_le_of_injective (fun a : (ZMod q)ˣ ↦ a.val) Units.val_injective
    simpa only [ZMod.card] using h
  unfold unitConductorSum
  calc
    _ ≤ ∑ a : (ZMod q)ˣ, ‖completeSum F q a.val‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ, C * (q : ℝ) ^ (-κ) :=
      Finset.sum_le_sum fun a _ ↦ hbound q a
    _ ≤ (q : ℝ) * (C * (q : ℝ) ^ (-κ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by
      rw [mul_left_comm]
      congr 1
      rw [sub_eq_add_neg, Real.rpow_add hq, Real.rpow_one]

/-- The singular-series coefficient decay of Section 5. -/
theorem conductorSum_decay_of_eventual_conductorOne {n d : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (h : EventualConductorOneBound d F) :
    ∃ C > 0, ∀ j : ℕ, ‖unitConductorSum F (j + 1)‖ ≤
      C * ((j + 1 : ℕ) : ℝ) ^ (1 - (n : ℝ) / d) :=
  conductorSum_decay_of_eventual_conductorOne_power hd hF hs (by positivity) le_rfl h

/-- The singular-series coefficient bound from a uniform square-root estimate. -/
theorem conductorSum_decay_of_uniform_conductorOne {n d : ℕ} {F : IntForm n}
    (hd : 3 ≤ d) (hn : 0 < n) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (h : UniformConductorOneBound d F) :
    ∃ C > 0, ∀ j : ℕ, ‖unitConductorSum F (j + 1)‖ ≤
      C * ((j + 1 : ℕ) : ℝ) ^ (1 - (n : ℝ) / d) :=
  conductorSum_decay_of_eventual_conductorOne (by omega) hF hs
    (eventualConductorOneBound_of_uniform hd hn h)

/-- The singular-series coefficient bound from Deligne's conductor-one estimate. -/
theorem conductorSum_decay_of_deligne {n d : ℕ} {F : IntForm n} (hd : 3 ≤ d)
    (hn : 0 < n) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hDeligne : DeligneConductorOne d F) :
    ∃ C > 0, ∀ j : ℕ, ‖unitConductorSum F (j + 1)‖ ≤
      C * ((j + 1 : ℕ) : ℝ) ^ (1 - (n : ℝ) / d) :=
  conductorSum_decay_of_uniform_conductorOne hd hn hF hs
    (uniformConductorOneBound_of_deligne hDeligne)

end
end Birch
