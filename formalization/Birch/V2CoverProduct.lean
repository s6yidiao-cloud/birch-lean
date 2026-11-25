import Birch.V2CoverMajor
import Birch.V2CoverMoments
import Birch.V2CoverRescaling
import Birch.V2CoverRiemann
import Birch.V2CoverShells

/-! # Pointwise approximation for the product in the cover problem -/

open Filter MeasureTheory Set
open scoped BigOperators Interval NNReal Polynomial Topology

namespace Birch

noncomputable section

/-- The product divided by the form-variable volume and the natural length
of the cover-variable sum. -/
def coverNormalizedProduct {n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (P Y L α : ℝ) : ℂ :=
  normalizedSum F w P α * ((Y : ℂ)⁻¹ * coverYSum g L α)

theorem continuous_coverNormalizedProduct {n : ℕ} (F : IntForm n) (g : ℤ[X])
    (w : (Fin n → ℝ) → ℝ) (P Y L : ℝ) : Continuous (coverNormalizedProduct F g w P Y L) :=
  ((continuous_exponentialSum F w P).const_smul (P ^ (-(n : ℝ)) : ℝ)).mul
    ((continuous_coverYSum g L).const_mul _)

theorem norm_coverRealOscillationOn_le (g : ℤ[X]) (e : ℕ) {B : ℝ} (hB : 0 ≤ B) (γ : ℝ) :
    ‖coverRealOscillationOn g e B γ‖ ≤ 2 * B := by
  unfold coverRealOscillationOn
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -B) (b := B) (C := 1) (f := fun t => phase (-γ * (g.leadingCoeff : ℝ) * t ^ e))
    (fun t _ => (norm_phase _).le)
  rw [one_mul, abs_of_nonneg (by linarith)] at h
  simpa only [sub_neg_eq_add, two_mul] using h

theorem continuous_coverRealOscillationOn (g : ℤ[X]) (e : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    Continuous (coverRealOscillationOn g e B) := by
  let C := 2 * Real.pi * |(g.leadingCoeff : ℝ)| * B ^ e
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply (show LipschitzWith (⟨C * (2 * B), by positivity⟩ : ℝ≥0)
      (coverRealOscillationOn g e B) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro γ γ'
  rw [dist_eq_norm, Real.dist_eq]
  let f (γ t : ℝ) := phase (-γ * (g.leadingCoeff : ℝ) * t ^ e)
  have hc (γ : ℝ) : Continuous (f γ) := by dsimp [f, phase]; fun_prop
  have hi (γ : ℝ) : IntervalIntegrable (f γ) volume (-B) B :=
    (hc γ).intervalIntegrable _ _
  change ‖(∫ t in (-B)..B, f γ t) - (∫ t in (-B)..B, f γ' t)‖ ≤ (C * (2 * B)) * |γ - γ'|
  rw [← intervalIntegral.integral_sub (hi γ) (hi γ')]
  have ha : -B ≤ B := by linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -B) (b := B) (C := C * |γ - γ'|) (f := fun t => f γ t - f γ' t) (by
      intro t ht
      rw [uIoc_of_le ha] at ht
      have ht' : |t| ≤ B := abs_le.mpr ⟨ht.1.le, ht.2⟩
      have hp := norm_phase_sub_le (-γ * (g.leadingCoeff : ℝ) * t ^ e)
        (-γ' * (g.leadingCoeff : ℝ) * t ^ e)
      dsimp only [f]
      refine hp.trans ?_
      rw [show -γ * (g.leadingCoeff : ℝ) * t ^ e - -γ' * (g.leadingCoeff : ℝ) * t ^ e =
        -(γ - γ') * (g.leadingCoeff : ℝ) * t ^ e by ring, abs_mul, abs_mul, abs_neg, abs_pow]
      dsimp only [C]
      calc
        _ = (2 * Real.pi * |(g.leadingCoeff : ℝ)| * |γ - γ'|) * |t| ^ e := by ring
        _ ≤ (2 * Real.pi * |(g.leadingCoeff : ℝ)| * |γ - γ'|) * B ^ e :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ht' _) (by positivity)
        _ = _ := by ring)
  rw [abs_of_nonneg (sub_nonneg.mpr ha), sub_neg_eq_add, ← two_mul] at h
  exact h.trans_eq (by ring)

/-- Poisson summation for the form, and the residue-class Riemann sums for
the polynomial, give a joint pointwise approximation. -/
theorem coverNormalizedProduct_approx_of_poisson_ratio {n d e : ℕ} {F : IntForm n}
    (g : ℤ[X]) (he : 0 < e) (hg : g.natDegree = e) {w : (Fin n → ℝ) → ℝ}
    (hw : CompactWeight w) (hPoisson : MajorArcPoissonIdentity d F w)
    {B K τ : ℝ} (hB : 0 < B) (hK : 0 < K) (hτ : 0 < τ) (L : ℝ) :
    ∃ C > 0, ∀ᶠ P : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (a : ℤ) (γ : ℝ),
      (1 + |γ|) / (P / q) ≤ K * P ^ (-τ) →
      let Y := P ^ ((d : ℝ) / e)
      ‖coverNormalizedProduct F g w P Y (B * Y) ((a : ℝ)/q + γ/P^d) -
          coverCompleteProductAt F g q a *
            (realOscillation F w γ * coverRealOscillationOn g e B γ)‖ ≤
        C * (P ^ (-L) + (1 + |γ|) * ((q : ℝ) / Y)) := by
  obtain ⟨E, hE, hform⟩ := norm_normalizedSum_sub_complete_le_of_poisson_ratio
    hw.smooth hw.compact hPoisson hK hτ L
  obtain ⟨D, hD, hcover⟩ := coverYSum_major_approximation_at_scale g (d := d) he hg hB
  obtain ⟨M, hM, hsum⟩ := norm_normalizedSum_eventually_bounded F hw
  let A := 4 * Real.pi * B * (∑ i ∈ Finset.range e, |(g.coeff i : ℝ)| * B ^ i)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := M * (D + A) + E * (2 * B)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsum] with P hP hS
  intro q _ a γ hratio
  let Y := P ^ ((d : ℝ) / e)
  let α := (a : ℝ)/q + γ/P^d
  let u := normalizedSum F w P α
  let v := (Y : ℂ)⁻¹ * coverYSum g (B * Y) α
  let U := completeSum F q (a : ZMod q) * realOscillation F w γ
  let V := coverCompleteSum g q (a : ZMod q)
  let J := coverRealOscillationOn g e B γ
  let J₀ := coverFiniteRealOscillation g e B Y γ
  let b := (1 + |γ|) * ((q : ℝ) / Y)
  have hP₀ : 0 < P := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hY : 1 ≤ Y := Real.one_le_rpow hP (by positivity)
  have hY₀ : 0 < Y := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hγα : P^d * (α - (a : ℝ)/q) = γ := by
    dsimp [α]
    rw [add_sub_cancel_left, mul_div_cancel₀ _ (pow_ne_zero _ hP₀.ne')]
  have hu : ‖u - U‖ ≤ E * P ^ (-L) := by
    simpa only [hγα] using hform P hP q a α (by simpa only [hγα] using hratio)
  have hv : ‖v - V * J₀‖ ≤ D * b := by
    simpa only [mul_assoc] using hcover P hP q a γ
  have hJ : ‖J₀ - J‖ ≤ A * b := by
    refine (norm_coverFiniteRealOscillation_sub_leading_le g hg hB hY γ).trans ?_
    have hγq : |γ| ≤ (1 + |γ|) * (q : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg γ)]
    have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hγq hY₀.le) hA
    dsimp [A, b] at h ⊢
    convert h using 1 <;> ring
  have hV : ‖V‖ ≤ 1 := norm_coverCompleteSum_le_one g q _
  have hJbound : ‖J‖ ≤ 2 * B := norm_coverRealOscillationOn_le g e hB.le γ
  have hv' : ‖v - V * J‖ ≤ (D + A) * b := by
    rw [show v - V * J = (v - V*J₀) + V*(J₀ - J) by ring, add_mul]
    refine (norm_add_le _ _).trans (add_le_add hv ?_)
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul hV hJ (norm_nonneg _) zero_le_one
  change ‖u * v - coverCompleteProductAt F g q a * (realOscillation F w γ * J)‖ ≤ _
  rw [coverCompleteProductAt_eq]
  change ‖u*v - (completeSum F q (a : ZMod q)*V) * (realOscillation F w γ*J)‖ ≤ _
  rw [show u*v - (completeSum F q (a : ZMod q)*V)*(realOscillation F w γ*J) =
      u * (v - V*J) + (u - U)*(V*J) by dsimp [U]; ring]
  refine (norm_add_le _ _).trans ?_
  simp only [norm_mul]
  have hu' := mul_le_mul (hS α) hv' (norm_nonneg _) hM.le
  have hb' : ‖V‖ * ‖J‖ ≤ 2 * B := by
    simpa only [one_mul] using mul_le_mul hV hJbound (norm_nonneg _) zero_le_one
  have hv'' := mul_le_mul hu hb' (by positivity) (by positivity : 0 ≤ E * P^(-L))
  have h := add_le_add hu' hv''
  change _ ≤ C * (P^(-L) + b)
  refine h.trans ?_
  dsimp [C]
  nlinarith [mul_nonneg (mul_nonneg hM.le (add_nonneg hD.le hA)) (Real.rpow_nonneg hP₀.le (-L)),
    mul_nonneg (mul_nonneg hE.le (show 0 ≤ 2 * B by positivity)) hb]

/-- The same power bound applies on the major arcs and on the larger
denominator shells used to estimate the conductor tail. -/
theorem coverNormalizedProduct_approx_smallHeight {n d e : ℕ} {F : IntForm n}
    (hF : F.IsHomogeneous d) (g : ℤ[X]) (he : 0 < e) (hg : g.natDegree = e)
    {w : (Fin n → ℝ) → ℝ} (hw : CompactWeight w) (hwbox : CubeSupported w)
    {B : ℝ} (hB : 0 < B) :
    let Δ := coverMajorArcExponent d e
    ∃ C > 0, ∀ᶠ P : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (a : ℤ) (γ : ℝ),
      (1 + |γ|) * (q : ℝ) ≤ 4 * P^(2*Δ) →
      let Y := P ^ ((d : ℝ) / e)
      ‖coverNormalizedProduct F g w P Y (B * Y) ((a : ℝ)/q + γ/P^d) -
          coverCompleteProductAt F g q a *
            (realOscillation F w γ * coverRealOscillationOn g e B γ)‖ ≤ C * P^(-(10*Δ)) := by
  let Δ := coverMajorArcExponent d e
  let k := (d : ℝ) / e
  have hΔ := coverMajorArcExponent_lt_quarter d e
  have hk : 12 * Δ ≤ k := by
    dsimp [Δ, coverMajorArcExponent, k]
    linarith [min_le_right (1 : ℝ) ((d : ℝ) / e)]
  have hτ : 0 < 1-2*Δ := by change Δ < 1/4 at hΔ; linarith
  have hPoisson := majorArcPoissonIdentity_of_smooth_cubeSupported hF hw.smooth hw.compact hwbox
  obtain ⟨C, hC, happrox⟩ := coverNormalizedProduct_approx_of_poisson_ratio g he hg hw hPoisson
    hB (by norm_num : (0 : ℝ) < 4) hτ (10*Δ)
  refine ⟨5*C, by positivity, ?_⟩
  filter_upwards [happrox, eventually_ge_atTop (1 : ℝ)] with P hP hP₁
  intro q _ a γ hheight
  have hp : 0 < P := zero_lt_one.trans_le hP₁
  have hratio : (1 + |γ|) / (P / q) ≤ 4 * P ^ (-(1-2*Δ)) := by
    rw [div_div_eq_mul_div]
    refine (div_le_div_of_nonneg_right hheight hp.le).trans_eq ?_
    rw [mul_div_assoc]
    congr 1
    conv_lhs => rhs; rw [← Real.rpow_one P]
    rw [← Real.rpow_sub hp]
    congr 1
    ring
  have h := hP q a γ hratio
  refine h.trans ?_
  have hb : (1 + |γ|) * ((q : ℝ) / P^k) ≤ 4 * P^(-(10*Δ)) := by
    rw [← mul_div_assoc]
    calc
      _ ≤ (4 * P^(2*Δ))/P^k := div_le_div_of_nonneg_right hheight (by positivity)
      _ = 4 * P^(2*Δ-k) := by rw [mul_div_assoc, ← Real.rpow_sub hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP₁ (by linarith)) (by norm_num)
  change C * (P^(-(10*Δ)) + (1 + |γ|) * ((q : ℝ) / P^k)) ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hb hC.le]

theorem coverNormalizedProduct_minorBound_of_minorIntegral {n d e : ℕ} {F : IntForm n}
    {g : ℤ[X]} {w : (Fin n → ℝ) → ℝ} {B η C : ℝ}
    (h : ∀ᶠ P : ℝ in atTop,
      (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
        ‖normalizedSum F w P α * coverYSum g (B * P^((d : ℝ)/e)) α‖ ∂circleMeasure) ≤
        C * P^((d : ℝ)/e-d-η)) :
    ∀ᶠ P : ℝ in atTop,
      (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
        ‖coverNormalizedProduct F g w P (P^((d : ℝ)/e)) (B * P^((d : ℝ)/e)) α‖
          ∂circleMeasure) ≤ C * P^(-(d : ℝ)-η) := by
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with P hP hp
  let k := (d : ℝ)/e
  let Y := P^k
  have hY : 0 < Y := Real.rpow_pos_of_pos hp _
  have hnorm (α : ℝ) :
      ‖coverNormalizedProduct F g w P Y (B*Y) α‖ =
        Y⁻¹ * ‖normalizedSum F w P α * coverYSum g (B*Y) α‖ := by
    rw [coverNormalizedProduct, norm_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hY, norm_mul]
    ring
  change (∫ α in _, ‖coverNormalizedProduct F g w P Y (B*Y) α‖ ∂circleMeasure) ≤ _
  simp_rw [hnorm, integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hY.le)).trans_eq ?_
  change (P^k)⁻¹ * (C * P^(k-d-η)) = _
  rw [← Real.rpow_neg hp.le, mul_left_comm, ← Real.rpow_add hp]
  congr 2
  ring

theorem coverRealOscillationOn_lower_near_zero (g : ℤ[X]) (e : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ r > 0, ∀ γ : ℝ, |γ| ≤ r → B ≤ ‖coverRealOscillationOn g e B γ‖ := by
  have hzero : ‖coverRealOscillationOn g e B 0‖ = 2 * B := by
    have h : coverRealOscillationOn g e B 0 = (B - -B : ℝ) • (1 : ℂ) := by
      simp [coverRealOscillationOn, phase]
    rw [h, norm_smul, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ B - -B)]
    ring
  let U := {γ | B < ‖coverRealOscillationOn g e B γ‖}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_coverRealOscillationOn g e hB.le).norm
  have hzeroU : 0 ∈ U := by change B < _; rw [hzero]; linarith
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU 0 hzeroU
  refine ⟨δ/2, by positivity, fun γ hγ => (hδU ?_).le⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  linarith

/-- The normalized minor-arc integral, tested with an auxiliary positive
weight, controls absolute convergence and the tail of the cover series. -/
theorem coverConductorMass_tail_of_coverNormalizedMinor {n d e : ℕ} {F : IntForm n}
    (hd : 2 ≤ d) (hF : F.IsHomogeneous d) (g : ℤ[X]) (he : 0 < e) (hg : g.natDegree = e)
    {η : ℝ} (hη : 0 < η) (hηΔ : η ≤ coverMajorArcExponent d e)
    (hminor : ∀ w : (Fin n → ℝ) → ℝ, CompactWeight w → CubeSupported w →
      ∃ D > 0, ∀ᶠ P : ℝ in atTop,
        (∫ α in (v2MajorArcs d (coverMajorArcExponent d e) P)ᶜ,
          ‖coverNormalizedProduct F g w P (P^((d : ℝ)/e)) (P^((d : ℝ)/e)) α‖
            ∂circleMeasure) ≤ D * P^(-(d : ℝ)-η)) :
    let Δ := coverMajorArcExponent d e
    Summable (fun j : ℕ => coverConductorMass F g (j+1)) ∧
      ∃ C > 0, ∃ Q₀ : ℕ, ∀ Q ≥ Q₀,
        (∑' j : ℕ, coverConductorMass F g (j+Q+1)) ≤ C * (Q : ℝ)^(-(η/(2*Δ))) := by
  let Δ := coverMajorArcExponent d e
  let k := (d : ℝ)/e
  have hΔ : 0 < Δ := coverMajorArcExponent_pos (by omega) he
  have hΔ₁ : Δ ≤ 1/4 := (coverMajorArcExponent_lt_quarter d e).le
  obtain ⟨w, hws, hwc, hwn, hwbox, rI, hrI, c, hc, hI⟩ :=
    exists_cubeWeight_positive_realOscillation F
  have hw : CompactWeight w := ⟨hws,hwc,hwn⟩
  obtain ⟨rJ, hrJ, hJ⟩ := coverRealOscillationOn_lower_near_zero g e (B := 1) zero_lt_one
  let r := min rI rJ
  have hr : 0 < r := lt_min hrI.1 hrJ
  have hr₁ : r ≤ 1 := (min_le_left _ _).trans hrI.2
  obtain ⟨D,hD,hDtail⟩ := hminor w hw hwbox
  obtain ⟨E,hE,happrox⟩ := coverNormalizedProduct_approx_smallHeight hF g he hg hw hwbox
    (B := 1) zero_lt_one
  let f P α := ‖coverNormalizedProduct F g w P (P^k) (P^k) α‖
  apply coverConductorMass_tail_of_v2MinorIntegral hd F g hΔ hΔ₁ hr hr₁ hc hD hE.le hη
    (L := 10*Δ) (by linarith) f
    (fun _ => (continuous_coverNormalizedProduct _ _ _ _ _ _).norm)
    (fun _ _ => norm_nonneg _) hDtail
  filter_upwards [happrox, eventually_ge_atTop (1 : ℝ)] with P hP hP₁
  rintro ⟨q,a⟩ hj α hα
  have hp : 0 < P := by linarith
  obtain ⟨hq, _, hqB, _, _, _⟩ := (mem_rationalShellCenters (by positivity)).1 hj
  let : NeZero q := ⟨by omega⟩
  let γ := P^d * (α - (a : ℝ)/q)
  have ha := (mem_rationalShellInterval (R := r*P^(-(d : ℝ))) (q := q) (a := a)).1 hα
  have hγ : |γ| ≤ r := by
    dsimp [γ]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ P ^ d)]
    refine (mul_le_mul_of_nonneg_left ha (by positivity)).trans_eq ?_
    rw [← Real.rpow_natCast P d, mul_left_comm, ← Real.rpow_add hp, add_neg_cancel, Real.rpow_zero, mul_one]
  have hheight : (1 + |γ|) * (q : ℝ) ≤ 4 * P^(2*Δ) :=
    (mul_le_mul (by linarith [hγ.trans hr₁] : 1 + |γ| ≤ 2) hqB (by positivity)
      (by norm_num)).trans_eq (by ring)
  have hαeq : (a : ℝ)/q + γ/P^d = α := by
    dsimp [γ]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero _ hp.ne'), add_sub_cancel]
  have herr := hP q (a : ℤ) γ hheight
  dsimp only at herr
  simp only [Int.cast_natCast, one_mul, hαeq] at herr
  let M := coverCompleteProductAt F g q (a : ℤ) *
    (realOscillation F w γ * coverRealOscillationOn g e 1 γ)
  have hcoeff : coverCompleteSumNormAt F g q a = ‖coverCompleteProductAt F g q (a : ℤ)‖ := by
    simp [coverCompleteSumNormAt, NeZero.ne q, coverCompleteProductAt_eq]
  change c * coverCompleteSumNormAt F g q a ≤ f P α + E*P^(-(10*Δ))
  calc
    _ ≤ ‖M‖ := by
      dsimp only [M]
      rw [hcoeff, mul_comm c, norm_mul, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa using mul_le_mul (hI γ (hγ.trans (min_le_left _ _)))
        (hJ γ (hγ.trans (min_le_right _ _))) zero_le_one (norm_nonneg _)
    _ = ‖coverNormalizedProduct F g w P (P^k) (P^k) α +
        (M - coverNormalizedProduct F g w P (P^k) (P^k) α)‖ := by congr 1; ring
    _ ≤ _ := by
      have hmerr : ‖M - coverNormalizedProduct F g w P (P^k) (P^k) α‖ ≤ E*P^(-(10*Δ)) := by
        rw [norm_sub_rev]
        exact herr
      exact (norm_add_le _ _).trans (add_le_add le_rfl hmerr)

end

end Birch
