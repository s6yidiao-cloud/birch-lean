import Birch.DyadicPrimes
import Birch.MetricSecondMoment
import Birch.ProductSupply

/-!
# Metric exceptional-set estimate

Finite frequency multiplicities come from factoring each frequency. The second
moment and the two supply estimates then give the exceptional exponent in the
source, with an arbitrarily small loss.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace Birch

noncomputable section

private theorem log_eventually_le_rpow {e : ℝ} (he : 0 < e) :
    ∀ᶠ P : ℝ in atTop, Real.log P ≤ P ^ e := by
  have h := (isLittleO_log_rpow_atTop he).bound zero_lt_one
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with P hP hP'
  simpa only [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hP'),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ P) e)] using hP

private theorem metric_ratio {P a b V e w : ℝ} (hP : 0 < P) (ha : 0 < a) (hb : 0 < b) :
    V * P ^ w * P ^ e / ((a * b) * P ^ w * (P ^ (-e)) ^ (2 : ℕ)) ^ (2 : ℕ) =
      (V / (a * b) ^ (2 : ℕ)) * P ^ (-w + 5 * e) := by
  have hw : 0 < P ^ w := Real.rpow_pos_of_pos hP _
  have he : 0 < P ^ e := Real.rpow_pos_of_pos hP _
  calc
    _ = V / (a * b) ^ (2 : ℕ) * ((P ^ (-w)) * (P ^ e) ^ (5 : ℕ)) := by
      rw [Real.rpow_neg hP.le e, Real.rpow_neg hP.le w]
      field_simp
    _ = _ := by
      rw [← Real.rpow_mul_natCast hP.le, ← Real.rpow_add hP]
      congr 2
      push_cast
      ring

/-- At one prescribed level, the hit estimate and product and prime supplies
give the exceptional-set bound. -/
theorem metricLevel_of_primeHit_and_supply {d n r : ℕ} {h : ℝ} {f : ℝ → ℝ → ℝ}
    (hr : 2 ≤ r) (hrd : r < d) (hh : 0 < h) (hhmax : h ≤ 1 / 2)
    (hhit : ∃ C > 0, ∀ᶠ P in atTop, ∀ (p M : ℕ), p.Prime →
      metricPrimeScale P h < (p : ℝ) → (p : ℝ) ≤ 2 * metricPrimeScale P h →
      admissibleProduct d r P (P ^ h) M → ∀ α,
      primeHit p (metricWindow d r P h) ((M : ℝ) * α) →
        f P α ≤ C * P ^ (-levelExponent d n r h))
    (hE : MetricProductSupply d) (hprimes : MetricPrimeSupply) :
    ∃ C > 0, ∀ ε > 0, ∃ K > 0, ∀ᶠ P in atTop,
      circleMeasure {α | C * P ^ (-levelExponent d n r h) < f P α} ≤
        ENNReal.ofReal (K * P ^ (-(d : ℝ) + exceptionExponent d r h + ε)) := by
  obtain ⟨C, hC, hhit⟩ := hhit
  refine ⟨C, hC, ?_⟩
  intro ε hε
  let e := ε / 5
  have he : 0 < e := by dsimp [e]; linarith
  let k := d - r
  let D := k + 3
  let G : ℝ := 4 + ((k + 2 : ℕ) : ℝ)
  let V : ℝ := (256 * (D : ℝ) ^ (2 : ℕ) + 512) * G
  have hG : 0 < G := by dsimp [G]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  obtain ⟨a, ha, heventE⟩ := hE r h hr hrd hh hhmax e he
  obtain ⟨b, hb, heventP⟩ := hprimes h hh hhmax e he
  refine ⟨V / (a * b) ^ (2 : ℕ), by positivity, ?_⟩
  filter_upwards [hhit, heventE, heventP, metricWindow_eventually hr hh (d := d),
    metricProductScale_eventually_ge_two hrd hhmax, eventually_ge_atTop (2 : ℝ),
    log_eventually_le_rpow he] with P hhit heventE heventP hu hX hP hlogP
  obtain ⟨E, hEdata, hEcard⟩ := heventE
  obtain ⟨primes, hprimedata, hprimecard⟩ := heventP
  let B := metricPrimeScale P h
  let X := metricProductScale d r P h
  let u := metricWindow d r P h
  let XL : ℕ := ⌊X⌋₊
  let L : ℕ := ⌊2 * B * X⌋₊
  have hP₁ : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  have hBbounds := metricPrimeScale_bounds hP₁ hh.le hhmax
  change P ≤ B ∧ B ≤ P ^ (2 : ℕ) at hBbounds
  have hB₁ : 1 ≤ B := hP₁.trans hBbounds.1
  have hBpos : 0 < B := zero_lt_one.trans_le hB₁
  change 2 ≤ X at hX
  have hXpos : 0 < X := by linarith
  change 0 < u ∧ u < 1 / 2 at hu
  have huPos := hu.1
  have hXupper : X ≤ P ^ k := metricProductScale_le hrd.le hP₁ hh.le
  have hXX : X ≤ 2 * B * X := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * B by linarith) hXpos.le
  have hXL₂ : 2 ≤ XL := Nat.le_floor (by simpa using hX)
  have hL₂ : 2 ≤ L := Nat.le_floor (by simpa using hX.trans hXX)
  have hXLleL : XL ≤ L := Nat.floor_mono hXX
  have hXLreal : (XL : ℝ) ≤ X := Nat.floor_le hXpos.le
  have hLreal : (L : ℝ) ≤ 2 * B * X := Nat.floor_le (by positivity)
  have hBX : B * X ≤ P ^ (k + 2 : ℕ) := by
    refine (mul_le_mul hBbounds.2 hXupper hXpos.le (by positivity)).trans_eq ?_
    rw [← pow_add, add_comm (2 : ℕ)]
  have hLbound : (L : ℝ) ≤ 2 * P ^ (k + 2 : ℕ) := by
    refine hLreal.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hBX (by norm_num)
  have hLP : (L : ℝ) ≤ P ^ D := by
    refine hLbound.trans ?_
    have hPmul : P ^ D = P * P ^ (k + 2 : ℕ) := by
      change P ^ (k + 3 : ℕ) = _
      rw [show k + 3 = 1 + (k + 2) by omega, pow_add, pow_one]
    rw [hPmul]
    exact mul_le_mul_of_nonneg_right hP (by positivity)
  have hPL (p : ℕ) (hp : p ∈ primes) : B < (p : ℝ) := (hprimedata p hp).2.1
  have hPupper : (primes.card : ℝ) ≤ 2 * B := by
    have hs : primes ⊆ Finset.Icc 1 ⌊2 * B⌋₊ := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨(hprimedata p hp).1.pos, Nat.le_floor (hprimedata p hp).2.2⟩
    have hc := Finset.card_le_card hs
    rw [Nat.card_Icc] at hc
    have hc' : primes.card ≤ ⌊2 * B⌋₊ := by omega
    exact (Nat.cast_le.mpr hc').trans (Nat.floor_le (by positivity))
  have hEfin : E ⊆ Finset.Icc 1 XL := by
    intro M hM
    exact Finset.mem_Icc.mpr ⟨(hEdata M hM).1, Nat.le_floor (hEdata M hM).2.1⟩
  have hprod (p : ℕ) (hp : p ∈ primes) (M : ℕ) (hM : M ∈ E) : p * M ≤ L := by
    apply Nat.le_floor
    push_cast
    exact mul_le_mul (hprimedata p hp).2.2 (hEdata M hM).2.1 (by positivity) (by positivity)
  have hcount (j : ℕ) (hj : j ∈ Finset.Icc 1 L) :
      (((primes.product E).filter fun q => q.1 * q.2 = j).card : ℝ) ≤ D := by
    have hj' := Finset.mem_Icc.mp hj
    apply Nat.cast_le.mpr
    refine primePairMultiplicity_le _ (by linarith) hj'.1 ((Nat.cast_le.mpr hj'.2).trans hLP) ?_
    intro q hq
    obtain ⟨hp, _⟩ := Finset.mem_product.mp hq
    exact ⟨(hprimedata q.1 hp).1, hBbounds.1.trans (hPL q.1 hp).le⟩
  have hEpos : 0 < E.card := by
    exact_mod_cast (show (0 : ℝ) < E.card from
      (show 0 < a * X * P ^ (-e) by positivity).trans_le hEcard)
  have hprimepos : 0 < primes.card := by
    exact_mod_cast (show (0 : ℝ) < primes.card from
      (show 0 < b * B * P ^ (-e) by positivity).trans_le hprimecard)
  have ht :=
    measure_tail_le_eventCount_second_moment E primes hu.1 hu.2 hXL₂ hL₂ hB₁ hPL hPupper
      hEfin (Finset.card_pos.mp hEpos) (Finset.card_pos.mp hprimepos) hprod hcount
      (fun q hq α hqhit => by
        obtain ⟨hp, hM⟩ := Finset.mem_product.mp hq
        obtain ⟨hprime, hlow, hupp⟩ := hprimedata q.1 hp
        exact hhit q.1 q.2 hprime hlow hupp (hEdata q.2 hM).2.2 α hqhit)
  refine ht.trans (ENNReal.ofReal_le_ofReal ?_)
  have hPe : 1 ≤ P ^ e := Real.one_le_rpow hP₁ he.le
  have hLlog : Real.log (2 * (L : ℝ)) ≤ G * P ^ e := by
    have hlpos : 0 < 2 * (L : ℝ) := by positivity
    calc
      _ ≤ Real.log (4 * P ^ (k + 2 : ℕ)) :=
        Real.log_le_log hlpos (by linarith)
      _ = Real.log 4 + ((k + 2 : ℕ) : ℝ) * Real.log P := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      _ ≤ 4 * P ^ e + ((k + 2 : ℕ) : ℝ) * P ^ e := by
        apply add_le_add
        · linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
        · exact mul_le_mul_of_nonneg_left hlogP (by positivity)
      _ = _ := by unfold G; ring
  have hXLlog : Real.log (2 * (XL : ℝ)) ≤ G * P ^ e := by
    refine (Real.log_le_log (show 0 < 2 * (XL : ℝ) by positivity) ?_).trans hLlog
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hXLleL) (by norm_num)
  have hLlognonneg : 0 ≤ Real.log (2 * (L : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * L by omega))
  have hXLlognonneg : 0 ≤ Real.log (2 * (XL : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * XL by omega))
  let W := B * X * u
  have hW : 0 < W := mul_pos (mul_pos hBpos hXpos) hu.1
  let numerator := 128 * (D : ℝ)^2 * u * (L : ℝ) * Real.log (2 * (L : ℝ)) +
    512 * u * B * (XL : ℝ) * Real.log (2 * (XL : ℝ))
  let countLower := ((E.card : ℝ) * primes.card) * u
  have hnum : numerator ≤ V * W * P ^ e := by
    calc
      _ ≤ 128 * (D : ℝ)^2 * u * (2 * B * X) * (G * P ^ e) +
          512 * u * B * X * (G * P ^ e) := by
        apply add_le_add
        · exact mul_le_mul
            (mul_le_mul_of_nonneg_left hLreal (by positivity)) hLlog hLlognonneg (by positivity)
        · exact mul_le_mul
            (mul_le_mul_of_nonneg_left hXLreal (by positivity)) hXLlog hXLlognonneg (by positivity)
      _ = _ := by dsimp only [V, W]; ring
  let lower := (a * b) * W * (P ^ (-e)) ^ (2 : ℕ)
  have hlower : 0 < lower := by dsimp only [lower]; positivity
  have hcountLower : lower ≤ countLower := by
    calc
      _ = (a * X * P ^ (-e)) * (b * B * P ^ (-e)) * u := by dsimp only [lower, W]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hEcard hprimecard (by positivity) (by positivity)) hu.1.le
  change numerator / countLower ^ (2 : ℕ) ≤ V / (a * b) ^ (2 : ℕ) *
    P ^ (-(d : ℝ) + exceptionExponent d r h + ε)
  calc
    _ ≤ V * W * P ^ e / countLower ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _ ≤ V * W * P ^ e / lower ^ (2 : ℕ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ hlower.le hcountLower _)
    _ = _ := by
      have hvolume : W = P ^ ((d : ℝ) - exceptionExponent d r h) := metricVolumeScale_eq hPpos d r h
      dsimp only [lower]
      rw [hvolume, metric_ratio hPpos ha hb]
      congr 2
      unfold e
      ring

/-- Proposition prop:metric follows from the completion estimate and the supplies
of admissible products and primes. -/
theorem metricEstimate_of_completion_and_supply {d n : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ}
    (hcompl : CompletionEstimate d n (fun P α => ‖normalizedSum F w P α‖))
    (hE : MetricProductSupply d) (hprimes : MetricPrimeSupply) :
    MetricEstimate d F w :=
  fun _ _ hr hrd hh hhmax => metricLevel_of_primeHit_and_supply hr hrd hh hhmax
    (level_of_primeHit hcompl hr hrd hh hhmax) hE hprimes

/-- Proposition prop:metric conditional on the completion bound. The supplies
of products and dyadic primes are proved in the imported modules. -/
theorem metricEstimate_of_completion {d n : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ}
    (hcompl : CompletionEstimate d n (fun P α => ‖normalizedSum F w P α‖)) :
    MetricEstimate d F w :=
  metricEstimate_of_completion_and_supply hcompl (metricProductSupply d) metricPrimeSupply

end

end Birch
