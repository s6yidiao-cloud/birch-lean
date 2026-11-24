import Birch.DirectionStratumCount
import Birch.SmoothSectionExistence
import Birch.V2Forms
import Birch.V2GradientReduction

/-! # The zero-difference completion and quadratic level distribution -/

open Filter MvPolynomial
open scoped ContDiff ENNReal Topology

namespace Birch

noncomputable section

/-- For a quadratic form the prime completion works directly, with no
differencing steps or higher-degree exponential-sum input. -/
theorem quadraticPointwiseEstimate {n σ : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hn : 0 < n) (hF : F.IsHomogeneous 2) (hσ : RationalGradientDimension F σ)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) :
    ∃ C > 0, ∀ᶠ B : ℝ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ B ^ (1 / 2 : ℝ) →
      ∀ p : ℕ, p.Prime → (B / T)^2 < (p : ℝ) → (p : ℝ) ≤ 2 * (B / T)^2 →
      ∀ (a : ℤ) (α : ℝ), ¬ (p : ℤ) ∣ a →
        |α - (a : ℝ) / (p : ℝ)| ≤ B ^ (-(2 : ℝ)) →
        ‖normalizedSum F w B α‖ ≤ C * T ^ (-((n - σ : ℕ) : ℝ)) := by
  have hred : EventualPrimeGradientDimensionLE F σ :=
    eventualPrimeGradientDimensionLE_of_geometric_dimension_le hn hF le_rfl hσ.le
  have hsection := primeSectionBound_of_interior le_rfl
    (primeInteriorSectionBound_of_geometric le_rfl (primeGeometricInteriorSections n 2 le_rfl))
  have hin := completionInputsAt_of_uniform_primeBounds hF hw hwbox le_rfl le_rfl
    (primeDirectionBound n 2) hsection
    (fun l _ => uniformTwistedPrimeBound_of_deligneTwistedDegree le_rfl deligneTwistedDegree_two l)
  obtain ⟨C, hC, h⟩ := completionEstimateAt_of_gradientDim hF hred hwbox hin
  refine ⟨C, hC, h.mono ?_⟩
  intro B hB T hT hTmax p hp hpL hpU a α ha hα
  have hprod : admissibleProduct 2 2 B T 1 := by
    refine ⟨fun _ => 1, by simp, ?_⟩
    exact fun i => i.elim0
  have hclose : |(1 : ℝ) * α - (a : ℝ) / (p : ℝ)| ≤ completionRadius 2 2 B T := by
    simpa [completionRadius, dilationRho] using hα
  simpa using hB T hT hTmax p 1 hp hpL hpU hprod a α ha (by simpa only [Nat.cast_one] using hclose)

/-- The quadratic metric estimate is uniform in all levels `1 ≤ T ≤ sqrt B`. -/
theorem quadraticMetricDistribution_uniform {n σ : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hν : 0 < n - σ) (hF : F.IsHomogeneous 2)
    (hσ : RationalGradientDimension F σ) (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) :
    ∃ C > 0, ∀ ε > 0, ∃ K > 0, ∀ᶠ B : ℝ in atTop, ∀ T : ℝ, 1 ≤ T →
      T ≤ B ^ (1 / 2 : ℝ) →
      circleMeasure {α | C * T ^ (-((n - σ : ℕ) : ℝ)) < ‖normalizedSum F w B α‖} ≤
        ENNReal.ofReal (K * B ^ (-(2 : ℝ) + ε) * T^4) := by
  obtain ⟨C, hC, hpoint⟩ := quadraticPointwiseEstimate (by omega : 0 < n) hF hσ hw hwbox
  refine ⟨C, hC, ?_⟩
  intro ε hε
  let e := ε / 3
  have he : 0 < e := by dsimp [e]; positivity
  let b : ℝ := Real.log 4 / 48
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp eventually_dyadicPrimes_lower
  refine ⟨24000 / b^2, by positivity, ?_⟩
  have heventlog := (isLittleO_log_rpow_atTop he).bound zero_lt_one
  filter_upwards [hpoint, eventually_ge_atTop (max 2 A₀), heventlog] with B hpt hBmax hlog T hT hTmax
  have hB : 2 ≤ B := (le_max_left _ _).trans hBmax
  have hB₁ : 1 ≤ B := by linarith
  have hBpos : 0 < B := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let A := (B/T)^2
  let u := min (1/4 : ℝ) (T^2)⁻¹
  let L : ℕ := ⌊2 * A⌋₊
  have hupos : 0 < u := lt_min (by norm_num) (by positivity)
  have hu₀ : u < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hT₂ : T^2 ≤ B := by
    rw [← Real.sqrt_eq_rpow] at hTmax
    exact (pow_le_pow_left₀ hTpos.le hTmax 2).trans_eq (Real.sq_sqrt hBpos.le)
  have hA : B ≤ A ∧ A ≤ B^2 := by
    constructor
    · change B ≤ (B/T)^2
      rw [div_pow, le_div_iff₀ (by positivity)]
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hT₂ hBpos.le
    · exact pow_le_pow_left₀ (by positivity) (div_le_self hBpos.le hT) 2
  have hApos : 0 < A := hBpos.trans_le hA.1
  have hA₁ : 1 ≤ A := hB₁.trans hA.1
  let primes := dyadicPrimes A
  have hband (p : ℕ) (hp : p ∈ primes) :
      p.Prime ∧ A < (p : ℝ) ∧ (p : ℝ) ≤ 2*A :=
    (mem_dyadicPrimes hApos.le).mp hp
  have hpow : 1 ≤ B^e := Real.one_le_rpow hB₁ he.le
  have hlogB : Real.log B ≤ B^e := by
    simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hB₁),
      abs_of_nonneg (Real.rpow_nonneg hBpos.le _)] using hlog
  have hsupply : b * A * B ^ (-e) ≤ (primes.card : ℝ) := by
    have hlogA : Real.log (2 * A) ≤ 4 * B^e := by
      have hlog2 : Real.log 2 ≤ 2 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [Real.log_mul (by norm_num) hApos.ne']
      rw [show Real.log A = 2 * Real.log (B / T) by simp [A, Real.log_pow]]
      have hmono := Real.log_le_log (div_pos hBpos hTpos) (div_le_self hBpos.le hT)
      linarith
    have hbound := hA₀ A (((le_max_right _ _).trans hBmax).trans hA.1)
    refine le_trans ?_ hbound
    rw [show b * A * B^(-e) = (Real.log 4 / 12 * A) / (4*B^e) by
      rw [Real.rpow_neg hBpos.le]
      dsimp only [b]
      field_simp
      norm_num]
    exact div_le_div_of_nonneg_left (by positivity) (Real.log_pos (by linarith)) hlogA
  have hL : (L : ℝ) ≤ 2 * A := Nat.floor_le (by positivity)
  have hL₂ : 2 ≤ L := Nat.le_floor (by push_cast; linarith [hA.1])
  have hbandL (p : ℕ) (hp : p ∈ primes) : A < (p : ℝ) := (hband p hp).2.1
  have hbandU (p : ℕ) (hp : p ∈ primes) : p ≤ L := Nat.le_floor (hband p hp).2.2
  have hcard : (primes.card : ℝ) ≤ 2 * A := dyadicPrimes_card_le hApos.le
  have hpc : primes.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (show (0 : ℝ) < primes.card from
      (show 0 < b * A * B^(-e) by positivity).trans_le hsupply)
  have hmul (q : ℕ × ℕ) (hq : q ∈ primes.product {1}) : q.2 = 1 :=
    Finset.mem_singleton.mp (Finset.mem_product.mp hq).2
  have hmult (j : ℕ) (_ : j ∈ Finset.Icc 1 L) :
      (((primes.product {1}).filter fun q => q.1 * q.2 = j).card : ℝ) ≤ 1 := by
    apply Nat.cast_le_one.mpr
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha, ha'⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hb'⟩ := Finset.mem_filter.mp hb
    have ha2 := hmul a ha
    have hb2 := hmul b hb
    exact Prod.ext (by simpa [ha2, hb2, mul_one] using ha'.trans hb'.symm) (ha2.trans hb2.symm)
  have hProduct (p : ℕ) (hp : p ∈ primes) (M : ℕ) (hM : M ∈ ({1} : Finset ℕ)) : p * M ≤ L := by
    simpa only [Finset.mem_singleton.mp hM, mul_one] using hbandU p hp
  have hactual (p : ℕ) (hp : p ∈ primes) (α : ℝ) (hhit : primeHit p u α) :
      ‖normalizedSum F w B α‖ ≤ C * T ^ (-((n - σ : ℕ) : ℝ)) := by
    have hp₀ := (hband p hp).1
    have hpA := hbandL p hp
    obtain ⟨a, ha, hα⟩ := hhit
    have huDiv : u / (p : ℝ) ≤ B ^ (-(2 : ℝ)) := by
      have hu_le : u ≤ A * B ^ (-(2 : ℝ)) := by
        refine (min_le_right _ _).trans_eq ?_
        rw [Real.rpow_neg hBpos.le, Real.rpow_two]
        unfold A
        field_simp
      exact (div_le_iff₀ (by exact_mod_cast hp₀.pos)).2
        (hu_le.trans (by
          rw [mul_comm (B ^ (-(2 : ℝ)))]
          exact mul_le_mul_of_nonneg_right hpA.le (by positivity)))
    exact hpt T hT hTmax p hp₀ hpA (hband p hp).2.2 a α ha (hα.trans huDiv)
  have ht := measure_tail_le_eventCount_second_moment {1} primes (u := u) (B := A)
    (X := 2) (L := L) (C := 1) (K := C * T ^ (-((n - σ : ℕ) : ℝ)))
    hupos hu₀ (by decide) hL₂ hA₁ hbandL hcard (by decide)
    (Finset.singleton_nonempty _) hpc hProduct hmult (fun q hq α hh => by
      obtain ⟨hp, hM⟩ := Finset.mem_product.mp hq
      simpa [hmul q hq] using hactual q.1 hp α (by simpa [hmul q hq] using hh))
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [one_pow, mul_one, Nat.cast_ofNat, Finset.card_singleton, Nat.cast_one, one_mul]
  have hlog4 : Real.log 4 ≤ 4 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hlogL : Real.log (2 * (L : ℝ)) ≤ 6 * B^e := by
    calc
      _ ≤ Real.log (4 * B^2) := Real.log_le_log (by positivity) (by linarith [hL, hA.2])
      _ = Real.log 4 + 2 * Real.log B := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      _ ≤ _ := by linarith
  have hlogL₀ : 0 ≤ Real.log (2 * (L : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * L by omega))
  have hnum : 128 * u * (L : ℝ) * Real.log (2 * (L : ℝ)) + 512 * u * A * 2 * Real.log (2*2) ≤
      6000 * (A * u) * B^e := by
    calc
      _ ≤ 128 * u * (2 * A) * (6 * B^e) + 512 * u * A * 2 * (4 * B^e) := by
        have hlog22 : Real.log (2*2) ≤ 4 * B^e := by
          rw [show (2:ℝ)*2=4 by norm_num]
          linarith
        gcongr
      _ ≤ _ := by nlinarith [show 0 ≤ (A * u) * B^e by positivity]
  have hlow : 0 < b * (A * u) * B^(-e) := by positivity
  have hcountlow : b * (A * u) * B^(-e) ≤ (primes.card : ℝ) * u := by
    calc
      _ = (b * A * B^(-e)) * u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hsupply hupos.le
  have hTpow : (T^2)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ hT)
  have hquarter : (1/4 : ℝ) * (T^2)⁻¹ ≤ u := by
    exact le_min
      (mul_le_of_le_one_right (by norm_num) hTpow)
      (mul_le_of_le_one_left (by positivity) (by norm_num))
  have hvol : B^2 / (4*T^4) ≤ A*u := by
    calc
      _ = A * ((1/4) * (T^2)⁻¹) := by
        dsimp only [A]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hquarter hApos.le
  have hvolpos : 0 < B^2 / (4*T^4) := by positivity
  calc
    _ ≤ 6000 * (A * u) * B^e / ((primes.card : ℝ) * u)^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ 6000 * (A * u) * B^e / (b * (A * u) * B^(-e))^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlow)
        (pow_le_pow_left₀ hlow.le hcountlow 2)
    _ = (6000 / b^2) * (B^e / ((A * u) * (B^(-e))^2)) := by
      have hu₀ : u ≠ 0 := hupos.ne'
      field_simp
    _ ≤ (6000 / b^2) * (B^e / ((B^2 / (4*T^4)) * (B^(-e))^2)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
        (by positivity) (mul_le_mul_of_nonneg_right hvol (by positivity))) (by positivity)
    _ = _ := by
      have hp : B^e / (B^2 * (B^(-e))^2) = B^(-(2 : ℝ) + ε) := by
        rw [← Real.rpow_natCast (B^(-e)), ← Real.rpow_mul hBpos.le, ← Real.rpow_natCast B,
          ← Real.rpow_add hBpos, ← Real.rpow_sub hBpos]
        congr 1
        dsimp [e]
        norm_num
        ring
      rw [← hp]
      field_simp
      ring


/-- The prime-only second moment gives the quadratic distribution estimate at
each fixed level (T=B^h), up to (h=1/2). -/
theorem quadraticLevel_of_primeHit_and_supply {n σ : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hν : 0 < n - σ) (hF : F.IsHomogeneous 2)
    (hσ : RationalGradientDimension F σ) (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    {h : ℝ} (hh : 0 < h) (hhmax : h ≤ 1 / 2) :
    ∃ C > 0, ∀ ε > 0, ∃ K > 0, ∀ᶠ B : ℝ in atTop,
      circleMeasure {α | C * B ^ (-(n - σ : ℕ) * h) < ‖normalizedSum F w B α‖} ≤
        ENNReal.ofReal (K * B ^ (-(2 : ℝ) + 4 * h + ε)) := by
  obtain ⟨C, hC, hmetric⟩ := quadraticMetricDistribution_uniform hν hF hσ hw hwbox
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := hmetric ε hε
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with B hB hB₁
  have hBpos : 0 < B := zero_lt_one.trans_le hB₁
  have hlevel : (B^h) ^ (-((n - σ : ℕ) : ℝ)) = B ^ (-(n - σ : ℕ) * h) := by
    rw [← Real.rpow_mul hBpos.le, mul_comm h]
  have hscale : K * B ^ (-(2 : ℝ) + ε) * (B^h)^4 = K * B ^ (-(2 : ℝ) + 4 * h + ε) := by
    rw [mul_assoc, ← Real.rpow_natCast (B^h), ← Real.rpow_mul hBpos.le, ← Real.rpow_add hBpos]
    congr 2
    norm_num
    ring
  rw [← hlevel, ← hscale]
  exact hB _ (Real.one_le_rpow hB₁ hh.le) (Real.rpow_le_rpow_of_exponent_le hB₁ hhmax)

end

end Birch
