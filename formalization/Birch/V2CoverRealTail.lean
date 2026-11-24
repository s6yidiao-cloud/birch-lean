import Birch.V2MajorArcShells
import Birch.V2CoverRiemann
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Real tails for polynomial-cover major arcs
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Birch

noncomputable section

private theorem integrableOn_Ioi_and_tail_of_shell_decay {f : ℝ → ℂ}
    (hf : Continuous f) {C c T : ℝ} (hc : 0 < c) (hT : 0 < T)
    (h : ∀ X ≥ T, (∫ γ in Ioc X (2 * X), ‖f γ‖) ≤ C * X ^ (-c)) :
    IntegrableOn f (Ioi T) ∧
      (∫ γ in Ioi T, ‖f γ‖) ≤ C * T ^ (-c) * (1 - (2 : ℝ) ^ (-c))⁻¹ := by
  let q (k : ℕ) : ℝ := T * 2 ^ k
  let S (k : ℕ) := Ioc (q k) (q (k + 1))
  let z : ℝ := (2 : ℝ) ^ (-c)
  let D : ℝ := C * T ^ (-c)
  have hq₀ : q 0 = T := by simp [q]
  have hq (k : ℕ) : T ≤ q k :=
    le_mul_of_one_le_right hT.le (one_le_pow₀ (by norm_num))
  have hnext (k : ℕ) : q (k + 1) = 2 * q k := by
    dsimp only [q]
    rw [pow_succ]
    ring
  have hmono : Monotone q := fun i j hij =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hij) hT.le
  have hunion : (⋃ k : ℕ, S k) = Ioi T := by
    have hub : ¬BddAbove (Set.range q) := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (x / T) (by norm_num : 1 < (2 : ℝ))
      exact ((div_lt_iff₀ hT).mp hk).not_ge
        (by simpa only [q, mul_comm] using hx (Set.mem_range_self k))
    have he := iUnion_Ioc_map_succ_eq_Ioi (f := q) (fun k => by simpa only [Nat.bot_eq_zero, hq₀] using hq k) hub
    change (⋃ k : ℕ, Ioc (q k) (q (k + 1))) = Ioi (q 0) at he
    simpa only [S, hq₀] using he
  have hz₀ : 0 ≤ z := by dsimp only [z]; positivity
  have hz₁ : z < 1 := by
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_zero.mpr hc)
  have hs (k : ℕ) : (∫ γ in S k, ‖f γ‖) ≤ D * z ^ k := by
    dsimp only [S]
    rw [hnext]
    refine (h (q k) (hq k)).trans_eq ?_
    have hpow : (((2 : ℝ) ^ k) ^ (-c : ℝ)) = ((2 : ℝ) ^ (-c)) ^ k := by
      rw [← Real.rpow_natCast_mul (by norm_num : 0 ≤ (2 : ℝ)),
        mul_comm (k : ℝ) (-c), Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))]
    dsimp only [q, D, z]
    rw [Real.mul_rpow hT.le (by positivity), hpow, mul_assoc]
  have hint (k : ℕ) : IntegrableOn f (S k) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgeo := (summable_geometric_of_lt_one hz₀ hz₁).mul_left D
  have hsum : Summable (fun k : ℕ => ∫ γ in S k, ‖f γ‖) :=
    hgeo.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hs
  have htail : IntegrableOn f (Ioi T) := by
    rw [← hunion]
    exact integrableOn_iUnion_of_summable_integral_norm hint hsum
  refine ⟨htail, ?_⟩
  have hdisj : Pairwise (fun i j => Disjoint (S i) (S j)) :=
    hmono.pairwise_disjoint_on_Ioc_succ
  rw [← hunion] at htail ⊢
  rw [integral_iUnion (fun _ => measurableSet_Ioc) hdisj htail.norm]
  exact (hsum.tsum_le_tsum hs hgeo).trans_eq (by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hz₀ hz₁])

private theorem absTail_eq_two_mul_Ioi {f : ℝ → ℂ} (hf : Integrable f)
    (heven : ∀ γ, ‖f (-γ)‖ = ‖f γ‖) {T : ℝ} (hT : 0 ≤ T) :
    (∫ γ in {γ : ℝ | T < |γ|}, ‖f γ‖) = 2 * ∫ γ in Ioi T, ‖f γ‖ := by
  have hset : {γ : ℝ | T < |γ|} = Iio (-T) ∪ Ioi T := by
    ext x
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have hh : ¬x < -T := by linarith
      simp only [hh, false_or]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have hh : ¬T < x := by linarith
      simp only [hh, or_false]
      constructor <;> intro h <;> linarith
  have hneg : (∫ γ in Iio (-T), ‖f γ‖) = ∫ γ in Ioi T, ‖f γ‖ := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
    simp_rw [heven]
  have hd : Disjoint (Iio (-T)) (Ioi T) := by
    refine Set.disjoint_left.mpr (fun x hx hy => ?_)
    exact (not_lt_of_ge (by linarith : -T ≤ T)) ((mem_Ioi.mp hy).trans (mem_Iio.mp hx))
  rw [hset, setIntegral_union hd measurableSet_Ioi hf.norm.integrableOn hf.norm.integrableOn,
    hneg, two_mul]

/-- A power saving on the positive dyadic shells implies absolute
integrability and a power-saving tail on both sides. -/
theorem integrable_and_absTail_of_dyadic_norm {f : ℝ → ℂ}
    (hf : Continuous f) (heven : ∀ γ, ‖f (-γ)‖ = ‖f γ‖)
    {C c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ T : ℝ in atTop, (∫ γ in Ioc T (2 * T), ‖f γ‖) ≤ C * T ^ (-c)) :
    Integrable f ∧ ∃ K > 0, ∀ T ≥ 1,
      (∫ γ in {γ : ℝ | T < |γ|}, ‖f γ‖) ≤ K * T ^ (-c) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp h
  let T₀ := max 1 A
  have hT₀ : 0 < T₀ := zero_lt_one.trans_le (le_max_left _ _)
  have hpos := (integrableOn_Ioi_and_tail_of_shell_decay hf hc hT₀
    (fun X hX => hA X ((le_max_right _ _).trans hX))).1
  have hpre : (fun x : ℝ => -x) ⁻¹' Ioi T₀ = Iio (-T₀) := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro h <;> linarith
  have hnegNorm := ((Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Ioi T₀) measurableSet_Ioi).integrable_comp_of_integrable hpos.norm
  have hneg : IntegrableOn f (Iio (-T₀)) := by
    apply (integrable_norm_iff hf.aestronglyMeasurable).mp
    change IntegrableOn (fun x : ℝ => ‖f (-x)‖) ((fun x : ℝ => -x) ⁻¹' Ioi T₀) at hnegNorm
    simpa only [IntegrableOn, heven, hpre] using hnegNorm
  have huniv : Iio (-T₀) ∪ Icc (-T₀) T₀ ∪ Ioi T₀ = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases hleft : x < -T₀
    · exact Or.inl (Or.inl hleft)
    · rcases le_or_gt x T₀ with hright | hright
      · exact Or.inl (Or.inr ⟨le_of_not_gt hleft, hright⟩)
      · exact Or.inr hright
  have hint : Integrable f := by
    have hmid : IntegrableOn f (Icc (-T₀) T₀) := hf.integrableOn_Icc
    have ht := (hneg.union hmid).union hpos
    rwa [huniv, integrableOn_univ] at ht
  let D₁ : ℝ := 2 * C * (1 - (2 : ℝ) ^ (-c))⁻¹
  let D₂ : ℝ := (∫ γ, ‖f γ‖) * T₀ ^ c
  refine ⟨hint, max 1 (max D₁ D₂), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro T hT
  by_cases hTlarge : T₀ ≤ T
  · obtain ⟨_, htail⟩ := integrableOn_Ioi_and_tail_of_shell_decay hf hc
      (zero_lt_one.trans_le hT) (fun X hX => hA X ((le_max_right _ _).trans (hTlarge.trans hX)))
    rw [absTail_eq_two_mul_Ioi hint heven (zero_le_one.trans hT)]
    calc
      _ ≤ 2 * (C * T ^ (-c) * (1 - (2 : ℝ) ^ (-c))⁻¹) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = D₁ * T ^ (-c) := by dsimp only [D₁]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_max_left D₁ D₂).trans (le_max_right 1 _)) (by positivity)
  · have hbase : 1 ≤ T₀ ^ c * T ^ (-c) := by
      rw [Real.rpow_neg (zero_le_one.trans hT), ← div_eq_mul_inv]
      exact (one_le_div (Real.rpow_pos_of_pos (zero_lt_one.trans_le hT) c)).mpr
        (Real.rpow_le_rpow (zero_le_one.trans hT) (le_of_not_ge hTlarge) hc.le)
    calc
      _ ≤ ∫ γ, ‖f γ‖ := setIntegral_le_integral hint.norm (Eventually.of_forall fun _ => norm_nonneg _)
      _ ≤ (∫ γ, ‖f γ‖) * (T₀ ^ c * T ^ (-c)) :=
        le_mul_of_one_le_right (integral_nonneg (fun _ => norm_nonneg _)) hbase
      _ = D₂ * T ^ (-c) := by dsimp only [D₂]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_max_right D₁ D₂).trans (le_max_right 1 _)) (by positivity)


/-- After division by `P^d`, a small positive dyadic frequency shell is
inside the circle domain and outside every major arc. -/
theorem coverFrequencyShell_mem_minor {d : ℕ} (hd : 2 ≤ d) {a Δ P γ : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1 / 3) (hΔ : Δ < a) (hP : 4 ≤ P)
    (hγ : γ ∈ Ioc (P ^ a) (2 * P ^ a)) :
    γ / P ^ d ∈ Ioc (0 : ℝ) 1 ∧ γ / P ^ d ∉ v2MajorArcs d Δ P := by
  let A := P ^ a
  let Q := P ^ Δ
  let D := P ^ d
  have hP₁ : 1 ≤ P := by linarith
  have hP₀ : 0 < P := by linarith
  have hA : 0 < A := Real.rpow_pos_of_pos hP₀ _
  have hA₁ : 1 ≤ A := Real.one_le_rpow hP₁ ha.le
  have hQ : 0 ≤ Q := Real.rpow_nonneg hP₀.le _
  have hD : 0 < D := pow_pos hP₀ _
  have hAQ : Q ≤ A := Real.rpow_le_rpow_of_exponent_le hP₁ hΔ.le
  have hγ₀ : 0 < γ := hA.trans hγ.1
  have hγ₂ : γ ≤ 2 * A := hγ.2
  have hdiff : (a + a + 1 : ℝ) ≤ d := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlarge : 3 * A ^ 2 < D := by
    calc
      _ < P * A ^ 2 := mul_lt_mul_of_pos_right (by linarith) (pow_pos hA 2)
      _ = P ^ (a + a + 1) := by
        calc
          _ = (P ^ a * P ^ a) * P ^ (1 : ℝ) := by dsimp only [A]; rw [pow_two, Real.rpow_one, mul_comm]
          _ = _ := by rw [← Real.rpow_add hP₀, ← Real.rpow_add hP₀]
      _ ≤ _ := by
        dsimp only [D]
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hP₁ hdiff
  have hα : 0 < γ / D := div_pos hγ₀ hD
  refine ⟨⟨hα, ?_⟩, ?_⟩
  · apply (div_le_iff₀ hD).2
    rw [one_mul]
    have hAA : A ≤ A ^ 2 := by nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hA₁)]
    linarith [hγ₂, hlarge, hAA]
  · rintro ⟨q, b, hq, hqQ, _, hclose⟩
    have hq₀ : 0 < (q : ℝ) := by exact_mod_cast hq
    have hwidth : P ^ (-(d : ℝ) + Δ) = Q / D := by
      rw [show -(d : ℝ) + Δ = Δ - d by ring, Real.rpow_sub hP₀, Real.rpow_natCast]
    rw [hwidth] at hclose
    change |γ / D - (b : ℝ) / q| ≤ Q / D at hclose
    by_cases hb : b = 0
    · simp only [hb, Int.cast_zero, zero_div, sub_zero, abs_of_pos hα] at hclose
      exact (lt_of_le_of_lt hAQ hγ.1).not_ge ((div_le_div_iff_of_pos_right hD).mp hclose)
    · have hb₁ : 1 ≤ |(b : ℝ)| := by
        have hbi : (1 : ℤ) ≤ |b| := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast (Int.natAbs_pos.mpr hb : (1 : ℕ) ≤ b.natAbs)
        exact_mod_cast hbi
      have hlower : 1 / (q : ℝ) ≤ |(b : ℝ) / q| := by
        rw [abs_div, abs_of_pos hq₀]
        exact div_le_div_of_nonneg_right hb₁ hq₀.le
      have hupper : |(b : ℝ) / q| ≤ (γ + Q) / D := by
        calc
          _ = |((b : ℝ) / q - γ / D) + γ / D| := by congr 1; ring
          _ ≤ |(b : ℝ) / q - γ / D| + |γ / D| := abs_add_le _ _
          _ ≤ Q / D + γ / D := by
            rw [abs_sub_comm ((b : ℝ) / q), abs_of_pos hα]
            exact add_le_add hclose le_rfl
          _ = _ := by rw [← add_div, add_comm Q γ]
      have hdq : D ≤ (q : ℝ) * (γ + Q) := by
        have h := (div_le_div_iff₀ hq₀ hD).mp (hlower.trans hupper)
        simpa only [one_mul, mul_comm (γ + Q)] using h
      have hdA : D ≤ 3 * A ^ 2 := by
        refine hdq.trans ?_
        calc
          _ ≤ Q * (γ + Q) := mul_le_mul_of_nonneg_right hqQ (add_nonneg hγ₀.le hQ)
          _ ≤ A * (3 * A) := mul_le_mul hAQ (by linarith)
            (add_nonneg hγ₀.le hQ) hA.le
          _ = _ := by ring
      exact hlarge.not_ge hdA


/-- The positive real shell, after the change of variables, is dominated
by the minor-arc integral on the circle. -/
theorem coverShellIntegral_le_minor {d : ℕ} (hd : 2 ≤ d) {a Δ P : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1 / 3) (hΔ : Δ < a) (hP : 4 ≤ P)
    {G : ℝ → ℂ} (hG : Continuous G) :
    (∫ γ in Ioc (P ^ a) (2 * P ^ a), ‖G (γ / P ^ d)‖) ≤
      P ^ d * ∫ α in (v2MajorArcs d Δ P)ᶜ, ‖G α‖ ∂circleMeasure := by
  let A := P ^ a
  let D := P ^ d
  let S := Ioc (A / D) (2 * A / D)
  have hP₀ : 0 < P := by linarith
  have hA : 0 < A := Real.rpow_pos_of_pos hP₀ a
  have hD : 0 < D := pow_pos hP₀ d
  have hA₂ : A ≤ 2 * A := by linarith
  have hSD : A / D ≤ 2 * A / D := div_le_div_of_nonneg_right hA₂ hD.le
  have hS (x : ℝ) (hx : x ∈ S) : x ∈ Ioc (0 : ℝ) 1 ∧ x ∈ (v2MajorArcs d Δ P)ᶜ := by
    have hx' : D * x ∈ Ioc A (2 * A) := by
      refine ⟨?_, ?_⟩
      · simpa only [mul_comm] using (div_lt_iff₀ hD).mp hx.1
      · simpa only [mul_comm] using (le_div_iff₀ hD).mp hx.2
    have ht := coverFrequencyShell_mem_minor hd ha ha₁ hΔ hP hx'
    change (D * x) / D ∈ Ioc (0 : ℝ) 1 ∧ (D * x) / D ∉ v2MajorArcs d Δ P at ht
    simpa only [mul_div_cancel_left₀ _ hD.ne', mem_compl_iff] using ht
  have hS₁ : S ⊆ Ioc (0 : ℝ) 1 := fun x hx => (hS x hx).1
  have hS₂ : S ⊆ (v2MajorArcs d Δ P)ᶜ := fun x hx => (hS x hx).2
  have hchange :
      (∫ γ in Ioc A (2 * A), ‖G (γ / D)‖) = D * ∫ α in S, ‖G α‖ := by
    rw [← intervalIntegral.integral_of_le hA₂,
      intervalIntegral.integral_comp_div (fun x : ℝ => ‖G x‖) hD.ne',
      intervalIntegral.integral_of_le hSD, smul_eq_mul]
  have hcirc : (∫ α in S, ‖G α‖ ∂circleMeasure) = ∫ α in S, ‖G α‖ := by
    unfold circleMeasure
    rw [Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.mpr hS₁]
  have hInt : Integrable (fun x => ‖G x‖) circleMeasure :=
    hG.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  change (∫ γ in Ioc A (2 * A), ‖G (γ / D)‖) ≤
    D * ∫ α in (v2MajorArcs d Δ P)ᶜ, ‖G α‖ ∂circleMeasure
  rw [hchange, ← hcirc]
  apply mul_le_mul_of_nonneg_left _ hD.le
  exact setIntegral_mono_set hInt.integrableOn (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall hS₂)


private theorem coverShell_pointwiseError_le {P a μ E : ℝ}
    (hP : 1 ≤ P) (ha : 0 ≤ a) (ha₃ : 3 * a ≤ 1) (hμ : 3 * a ≤ μ) (hE : 0 ≤ E) :
    P ^ a * (E * ((1 + 2 * P ^ a) / P ^ μ + P⁻¹)) ≤ (4 * E) * P ^ (-a) := by
  let A := P ^ a
  let Y := P ^ μ
  have hP₀ : 0 < P := zero_lt_one.trans_le hP
  have hA₀ : 0 < A := Real.rpow_pos_of_pos hP₀ _
  have hY₀ : 0 < Y := Real.rpow_pos_of_pos hP₀ _
  have hA₁ : 1 ≤ A := Real.one_le_rpow hP ha
  have h₃ : A ^ 3 ≤ Y := by
    dsimp only [A, Y]
    rw [← Real.rpow_mul_natCast hP₀.le]
    exact Real.rpow_le_rpow_of_exponent_le hP (by push_cast; linarith)
  have h₂ : A ^ 2 ≤ P := by
    dsimp only [A]
    rw [← Real.rpow_mul_natCast hP₀.le]
    exact (Real.rpow_le_rpow_of_exponent_le hP (by push_cast; linarith : a * (2 : ℕ) ≤ 1)).trans_eq
      (Real.rpow_one P)
  have hfirst : A * ((1 + 2 * A) / Y) ≤ 3 / A := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hY₀ hA₀).2
    have hsmall : A * (1 + 2 * A) ≤ 3 * A ^ 2 := by
      nlinarith [mul_nonneg hA₀.le (sub_nonneg.mpr hA₁)]
    calc
      _ ≤ (3 * A ^ 2) * A := mul_le_mul_of_nonneg_right hsmall hA₀.le
      _ = 3 * A ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h₃ (by norm_num)
  have hsecond : A * P⁻¹ ≤ 1 / A := by
    rw [← div_eq_mul_inv]
    exact (div_le_div_iff₀ hP₀ hA₀).2 (by rwa [one_mul, ← sq])
  rw [Real.rpow_neg hP₀.le]
  change A * (E * ((1 + 2 * A) / Y + P⁻¹)) ≤ (4 * E) * A⁻¹
  calc
    _ = E * (A * ((1 + 2 * A) / Y) + A * P⁻¹) := by ring
    _ ≤ E * (3 / A + 1 / A) := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hE
    _ = _ := by ring

/-- Transfer a power-saving minor-arc product moment to the matching
positive real shell. The major-arc cutoff is `Δ = min(1, μ) / 12`. -/
theorem coverRealShell_decay_of_productMinor_atExponent {d : ℕ} (hd : 2 ≤ d)
    {G : ℝ → ℝ → ℂ} {H : ℝ → ℂ} (hG : ∀ P, Continuous (G P)) (hH : Continuous H)
    {μ C E η : ℝ} (hμ : 0 < μ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hη : 0 < η)
    (hminor : ∀ᶠ P : ℝ in atTop, (∫ α in (v2MajorArcs d (min 1 μ / 12) P)ᶜ,
      ‖G P α‖ ∂circleMeasure) ≤ C * P ^ (-(d : ℝ) - η))
    (happrox : ∀ᶠ P : ℝ in atTop, ∀ γ : ℝ, |γ| ≤ 2 * P ^ (min 1 μ / 3) →
      ‖G P (γ / P ^ d) - H γ‖ ≤ E * ((1 + |γ|) / P ^ μ + P⁻¹)) :
    let a := min 1 μ / 3
    let c := min η a / a
    0 < c ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop,
      (∫ γ in Ioc T (2 * T), ‖H γ‖) ≤ K * T ^ (-c) := by
  let a := min 1 μ / 3
  let Δ := min 1 μ / 12
  let η₀ := min η a
  have ha : 0 < a := div_pos (lt_min zero_lt_one hμ) (by norm_num)
  have ha₃ : 3 * a ≤ 1 := by dsimp only [a]; linarith [min_le_left (1 : ℝ) μ]
  have haμ : 3 * a ≤ μ := by dsimp only [a]; linarith [min_le_right (1 : ℝ) μ]
  have ha₁ : a ≤ 1 / 3 := by linarith
  have hΔ : Δ < a := by
    dsimp only [Δ, a]
    linarith [lt_min zero_lt_one hμ]
  have hη₀ : 0 < η₀ := lt_min hη ha
  have hPbound : ∀ᶠ P : ℝ in atTop,
      (∫ γ in Ioc (P ^ a) (2 * P ^ a), ‖H γ‖) ≤ (C + 4 * E) * P ^ (-η₀) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), hminor, happrox] with P hP hm hp
    let A := P ^ a
    let S := Ioc A (2 * A)
    let err := E * ((1 + 2 * A) / P ^ μ + P⁻¹)
    have hP₁ : 1 ≤ P := by linarith
    have hP₀ : 0 < P := zero_lt_one.trans_le hP₁
    have hA : 0 < A := Real.rpow_pos_of_pos hP₀ _
    have hA₂ : A ≤ 2 * A := by linarith
    have hull : IntegrableOn (fun γ => ‖G P (γ / P ^ d)‖) S :=
      ((hG P).comp (continuous_id.div_const (P ^ d))).norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have herr : IntegrableOn (fun _ : ℝ => err) S :=
      continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hHInt : IntegrableOn (fun γ => ‖H γ‖) S :=
      hH.norm.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hpoint (γ : ℝ) (hγ : γ ∈ S) : ‖H γ‖ ≤ ‖G P (γ / P ^ d)‖ + err := by
      have hγ₀ : 0 ≤ γ := hA.le.trans hγ.1.le
      have hγa : |γ| ≤ 2 * A := by rw [abs_of_nonneg hγ₀]; exact hγ.2
      have htt : ‖H γ‖ ≤ ‖G P (γ / P ^ d)‖ + ‖G P (γ / P ^ d) - H γ‖ := by
        simpa only [sub_sub_cancel] using norm_sub_le (G P (γ / P ^ d)) (G P (γ / P ^ d) - H γ)
      refine htt.trans (add_le_add le_rfl ((hp γ hγa).trans ?_))
      apply mul_le_mul_of_nonneg_left _ hE
      exact add_le_add (div_le_div_of_nonneg_right (add_le_add le_rfl hγa) (by positivity)) le_rfl
    have hsum := setIntegral_mono_on hHInt (hull.add herr) measurableSet_Ioc hpoint
    simp only [Pi.add_apply] at hsum
    rw [integral_add hull herr, setIntegral_const, Real.volume_real_Ioc_of_le hA₂, smul_eq_mul,
      show 2 * A - A = A by ring] at hsum
    have hM : (∫ γ in S, ‖G P (γ / P ^ d)‖) ≤ C * P ^ (-η) := by
      refine (coverShellIntegral_le_minor hd ha ha₁ hΔ hP (hG P)).trans
        ((mul_le_mul_of_nonneg_left hm (pow_nonneg hP₀.le d)).trans_eq ?_)
      rw [← Real.rpow_natCast P d, mul_left_comm, ← Real.rpow_add hP₀]
      congr 2
      ring
    have heErr : A * err ≤ (4 * E) * P ^ (-a) :=
      coverShell_pointwiseError_le hP₁ ha.le ha₃ haμ hE
    change (∫ γ in S, ‖H γ‖) ≤ _
    calc
      _ ≤ C * P ^ (-η) + (4 * E) * P ^ (-a) := hsum.trans (add_le_add hM heErr)
      _ ≤ C * P ^ (-η₀) + (4 * E) * P ^ (-η₀) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hP₁ (neg_le_neg (min_le_left _ _))) hC
        · exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hP₁ (neg_le_neg (min_le_right _ _))) (by positivity)
      _ = _ := by ring
  refine ⟨div_pos hη₀ ha, C + 4 * E, by positivity, ?_⟩
  simpa only [neg_div] using rationalShell_decay_of_scale
    (A := fun T => ∫ γ in Ioc T (2 * T), ‖H γ‖) ha hPbound

/-- Absolute convergence and a full real tail from the minor product moment
and its continuum approximation. -/
theorem integrable_and_absTail_of_productMinor_atExponent {d : ℕ} (hd : 2 ≤ d)
    {G : ℝ → ℝ → ℂ} {H : ℝ → ℂ} (hG : ∀ P, Continuous (G P)) (hH : Continuous H)
    (heven : ∀ γ, ‖H (-γ)‖ = ‖H γ‖)
    {μ C E η : ℝ} (hμ : 0 < μ) (hC : 0 ≤ C) (hE : 0 ≤ E) (hη : 0 < η)
    (hminor : ∀ᶠ P : ℝ in atTop, (∫ α in (v2MajorArcs d (min 1 μ / 12) P)ᶜ,
      ‖G P α‖ ∂circleMeasure) ≤ C * P ^ (-(d : ℝ) - η))
    (happrox : ∀ᶠ P : ℝ in atTop, ∀ γ : ℝ, |γ| ≤ 2 * P ^ (min 1 μ / 3) →
      ‖G P (γ / P ^ d) - H γ‖ ≤ E * ((1 + |γ|) / P ^ μ + P⁻¹)) :
    let a := min 1 μ / 3
    let c := min η a / a
    Integrable H ∧ ∃ K : ℝ, 0 < K ∧ ∀ T ≥ 1,
      (∫ γ in {γ : ℝ | T < |γ|}, ‖H γ‖) ≤ K * T ^ (-c) := by
  obtain ⟨hc, K, _, hs⟩ :=
    coverRealShell_decay_of_productMinor_atExponent hd hG hH hμ hC hE hη hminor happrox
  exact integrable_and_absTail_of_dyadic_norm hH heven hc hs

end
end Birch
