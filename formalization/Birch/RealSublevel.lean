import Birch.RealOscillationDecay
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# A transverse real zero supplies sublevel mass

Over a small box the weight is bounded below and the derivative along the
transverse coordinate is bounded. The intermediate value theorem supplies a
zero in every slice, and the upper derivative bound supplies an interval in the
sublevel set. Fubini gives a uniform linear lower bound for the weighted volume.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Birch

noncomputable section

private theorem exists_ball_preserving_slice_signs {X : Type*} [MetricSpace X]
    {f : ℝ → X → ℝ} (hf : Continuous (fun z : ℝ × X => f z.1 z.2))
    {y₀ : X} {δ tLeft tRight : ℝ} (hδ : 0 < δ)
    (hleft : f tLeft y₀ < 0) (hright : 0 < f tRight y₀) :
    ∃ u : ℝ, 0 < u ∧ ∀ y ∈ Metric.ball y₀ u,
      (y ∈ Metric.ball y₀ δ ∧ f tLeft y < 0) ∧ 0 < f tRight y := by
  have hslices (t : ℝ) : Continuous (fun y : X => f t y) := by
    have hpair : Continuous (fun y : X => (t, y)) := continuous_const.prodMk continuous_id
    change Continuous ((fun z : ℝ × X => f z.1 z.2) ∘ fun y : X => (t, y))
    exact hf.comp hpair
  let V : Set X := Metric.ball y₀ δ ∩ {y | f tLeft y < 0} ∩ {y | 0 < f tRight y}
  have hleftOpen : IsOpen {y : X | f tLeft y < 0} :=
    isOpen_lt (hslices tLeft) continuous_const
  have hrightOpen : IsOpen {y : X | 0 < f tRight y} :=
    isOpen_lt continuous_const (hslices tRight)
  have hV : IsOpen V := (Metric.isOpen_ball.inter hleftOpen).inter hrightOpen
  have hV₀ : y₀ ∈ V := ⟨⟨Metric.mem_ball_self hδ, hleft⟩, hright⟩
  exact Metric.isOpen_iff.mp hV y₀ hV₀

private theorem realSublevel_succ {n : ℕ} {F : IntForm (n+1)} {w : (Fin (n+1) → ℝ) → ℝ}
    (hw : Continuous w) (hcompact : HasCompactSupport w) (hnneg : ∀ x, 0 ≤ w x)
    (x₀ : Fin (n+1) → ℝ) (hx₀ : evalForm F x₀ = 0) (hw₀ : 0 < w x₀)
    (i : Fin (n+1)) (hi : evalForm (MvPolynomial.pderiv i F) x₀ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → c*r ≤ ∫ x in {x | |evalForm F x| ≤ r}, w x := by
  classical
  let X := Fin n → ℝ
  let e : ℝ × X ≃ᵐ (Fin (n+1) → ℝ) := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i).symm
  have hpres : MeasurePreserving e (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
  let t₀ := x₀ i
  let y₀ : X := fun j ↦ x₀ (i.succAbove j)
  have he₀ : e (t₀, y₀) = x₀ := e.apply_symm_apply x₀
  have he (t : ℝ) (y : X) : e (t,y) = i.insertNth t y := rfl
  have heC : Continuous e := by
    apply continuous_pi
    intro j
    cases j using Fin.succAboveCases i with
    | x => simpa only [he, Fin.insertNth_apply_same] using continuous_fst
    | p k =>
      simp only [he, Fin.insertNth_apply_succAbove]
      exact (continuous_apply k).comp continuous_snd
  let d₀ := evalForm (MvPolynomial.pderiv i F) x₀
  have hd₀ : 0 < |d₀| := abs_pos.mpr hi
  let σ : ℝ := if 0 < d₀ then 1 else -1
  have hσ : |σ| = 1 := by dsimp [σ]; split_ifs <;> norm_num
  have hσd : 0 < σ*d₀ := by
    dsimp [σ]
    split_ifs with h
    · simpa using h
    · have hne := abs_pos.mp hd₀
      simpa using lt_of_le_of_ne (le_of_not_gt h) hne
  let A := w x₀ / 2
  have hA : 0 < A := half_pos hw₀
  let L := |d₀| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  let f (t : ℝ) (y : X) := σ * evalForm F (e (t,y))
  let df (t : ℝ) (y : X) := σ * evalForm (MvPolynomial.pderiv i F) (e (t,y))
  have hcF : Continuous (fun z : ℝ × X ↦ f z.1 z.2) :=
    continuous_const.mul ((continuous_evalForm F).comp heC)
  have hcD : Continuous (fun z : ℝ × X ↦ df z.1 z.2) :=
    continuous_const.mul ((continuous_evalForm _).comp heC)
  have hf₀ : f t₀ y₀ = 0 := by simp [f, he₀, hx₀]
  have hderiv (t : ℝ) (y : X) : HasDerivAt (fun s ↦ f s y) (df t y) t := by
    have hupdate (s : ℝ) : Function.update (e (t,y)) i s = e (s,y) := by
      ext j
      cases j using Fin.succAboveCases i with
      | x => simp [he]
      | p k => simp [he, Fin.succAbove_ne]
    simpa only [f, df, hupdate] using
      (hasDerivAt_evalForm_update F i (e (t,y)) t).const_mul σ
  let U : Set (ℝ × X) :=
    {z | A < w (e z)} ∩ {z | 0 < df z.1 z.2} ∩ {z | |df z.1 z.2| < L}
  have hU : IsOpen U := ((isOpen_lt continuous_const (hw.comp heC)).inter
    (isOpen_lt continuous_const hcD)).inter (isOpen_lt hcD.abs continuous_const)
  have hxU : (t₀,y₀) ∈ U := by
    have ha : A < w x₀ := half_lt_self hw₀
    have hd : |σ*d₀| < L := by rw [abs_mul, hσ, one_mul]; dsimp [L]; linarith
    change (A < w (e (t₀,y₀)) ∧ 0 < df t₀ y₀) ∧ |df t₀ y₀| < L
    exact ⟨⟨by rwa [he₀], by simpa only [df, he₀] using hσd⟩,
      by simpa only [df, he₀] using hd⟩
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU _ hxU
  let a := δ / 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hbox {t : ℝ} {y : X} (ht : t ∈ Icc (t₀ - 2*a) (t₀ + 2*a))
      (hy : y ∈ Metric.ball y₀ δ) : (t,y) ∈ U := by
    apply hδU
    rw [← ball_prod_same]
    refine ⟨?_, hy⟩
    change dist t t₀ < δ
    rw [Real.dist_eq, abs_lt]
    constructor <;> dsimp [a] at ht <;> linarith [ht.1, ht.2]
  have hy₀ : y₀ ∈ Metric.ball y₀ δ := Metric.mem_ball_self hδ
  have hmono : StrictMonoOn (fun t ↦ f t y₀) (Icc (t₀-a) (t₀+a)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((hcF.comp (continuous_id.prodMk continuous_const)).continuousOn)
    intro t ht
    change 0 < deriv (fun s ↦ f s y₀) t
    rw [(hderiv t y₀).deriv]
    have ht' := interior_subset ht
    exact (hbox ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ hy₀).1.2
  have hleft : f (t₀-a) y₀ < 0 := by
    rw [← hf₀]
    exact hmono ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hright : 0 < f (t₀+a) y₀ := by
    rw [← hf₀]
    exact hmono ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  obtain ⟨u, hu, huV⟩ :=
    exists_ball_preserving_slice_signs (f := f) hcF hδ hleft hright
  let B := Metric.ball y₀ u
  have hBmeas : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hBpos : 0 < volume B := Metric.measure_ball_pos volume y₀ hu
  have hBfinite : volume B ≠ ∞ := measure_ball_lt_top.ne
  let c := 2 * A / L * (volume B).toReal
  have hc : 0 < c := mul_pos (div_pos (by positivity) hL) (ENNReal.toReal_pos hBpos.ne' hBfinite)
  refine ⟨c, hc, a*L, mul_pos ha hL, fun r hr hr₀ ↦ ?_⟩
  let E : Set (Fin (n+1) → ℝ) := {x | |evalForm F x| ≤ r}
  have hE : MeasurableSet E := (isClosed_le (continuous_evalForm F).abs continuous_const).measurableSet
  let g (x : Fin (n+1) → ℝ) : ℝ := E.indicator w x
  have hg : Measurable g := hw.measurable.indicator hE
  have hgnonneg (x) : 0 ≤ g x := indicator_nonneg (s := E) (fun x _ ↦ hnneg x) x
  have hgint : Integrable g := (hw.integrable_of_hasCompactSupport hcompact).indicator hE
  let G (z : ℝ × X) : ℝ≥0∞ := ENNReal.ofReal (g (e z))
  have hG : Measurable G := ENNReal.measurable_ofReal.comp (hg.comp e.measurable)
  have hslice (y : X) (hy : y ∈ B) : ENNReal.ofReal (2*A*r/L) ≤ ∫⁻ t, G (t,y) := by
    have hyV := huV y hy
    obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (by linarith : t₀-a ≤ t₀+a)
      ((hcF.comp (continuous_id.prodMk continuous_const)).continuousOn)
      (show (0 : ℝ) ∈ Icc (f (t₀-a) y) (f (t₀+a) y) from ⟨hyV.1.2.le, hyV.2.le⟩)
    change f t y = 0 at hzero
    let J := Icc (t-r/L) (t+r/L)
    have hdist : r/L ≤ a := (div_le_iff₀ hL).mpr hr₀
    have hJ : J ⊆ Icc (t₀-2*a) (t₀+2*a) := by
      intro s hs
      exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have ht' : t ∈ Icc (t₀-2*a) (t₀+2*a) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hpoint (s : ℝ) (hs : s ∈ J) : ENNReal.ofReal A ≤ G (s,y) := by
      have hd : |s-t| ≤ r/L := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have H := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun v _ ↦ (hderiv v y).differentiableAt) (fun v hv ↦ by
          rw [(hderiv v y).deriv, Real.norm_eq_abs]
          exact (hbox hv hyV.1.1).2.le)
        (convex_Icc (t₀-2*a) (t₀+2*a)) ht' (hJ hs)
      have hf : |evalForm F (e (s,y))| ≤ r := by
        rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at H
        change |σ * evalForm F (e (s,y))| ≤ L * |s-t| at H
        rw [abs_mul, hσ, one_mul] at H
        exact H.trans ((mul_le_mul_of_nonneg_left hd hL.le).trans_eq (by field_simp))
      exact ENNReal.ofReal_le_ofReal (by
        change A ≤ E.indicator w (e (s,y))
        rw [indicator_of_mem (show e (s,y) ∈ E from hf)]
        exact (hbox (hJ hs) hyV.1.1).1.1.le)
    calc
      ENNReal.ofReal (2*A*r/L) = volume J * ENNReal.ofReal A := by
        have hwidth : 0 ≤ t+r/L-(t-r/L) := by linarith [div_pos hr hL]
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul hwidth]
        congr 1
        ring
      _ = ∫⁻ s, J.indicator (fun _ ↦ ENNReal.ofReal A) s := by
        rw [lintegral_indicator measurableSet_Icc, lintegral_const, mul_comm]
        simp [J]
      _ ≤ _ := by
        apply lintegral_mono
        intro s
        by_cases hs : s ∈ J
        · rw [indicator_of_mem hs]
          exact hpoint s hs
        · simp [indicator_of_notMem hs]
  have hmass :
      ENNReal.ofReal (c*r) ≤ ∫⁻ x, ENNReal.ofReal (g x) := by
    have hlin : (∫⁻ x, ENNReal.ofReal (g x)) = ∫⁻ y : X, ∫⁻ t : ℝ, G (t,y) := by
      calc
        _ = ∫⁻ z : ℝ × X, G z ∂(volume.prod volume) :=
          (hpres.lintegral_comp (f := fun x => ENNReal.ofReal (g x))
            (ENNReal.measurable_ofReal.comp hg)).symm
        _ = _ := lintegral_prod_symm G hG.aemeasurable
    rw [hlin]
    calc
      _ = ENNReal.ofReal (2*A*r/L) * volume B := by
        rw [← ENNReal.ofReal_toReal hBfinite, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [c]
        ring
      _ = ∫⁻ y, B.indicator (fun _ ↦ ENNReal.ofReal (2*A*r/L)) y := by
        rw [lintegral_indicator hBmeas, lintegral_const]
        simp
      _ ≤ _ := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ B
        · rw [indicator_of_mem hy]
          exact hslice y hy
        · simp [indicator_of_notMem hy]
  have hfinite : (∫⁻ x, ENNReal.ofReal (g x)) ≠ ∞ := by
    convert (hasFiniteIntegral_iff_ofReal (ae_of_all _ hgnonneg)).mp hgint.2 |>.ne using 1
  rw [← integral_indicator hE]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hgnonneg) hgint.aestronglyMeasurable]
  exact (ENNReal.toReal_mono hfinite hmass).trans_eq' (ENNReal.toReal_ofReal (mul_nonneg hc.le hr.le))

/-- A nonsingular real zero of positive weight gives a linear lower bound for
the weighted sublevel volume. -/
theorem realSublevelLowerBound_of_nonsingularZero {n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hw : Continuous w) (hcompact : HasCompactSupport w) (hnneg : ∀ x, 0 ≤ w x)
    {x₀ : Fin n → ℝ} (hx₀ : evalForm F x₀ = 0) (hw₀ : 0 < w x₀)
    {i : Fin n} (hi : evalForm (MvPolynomial.pderiv i F) x₀ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → c*r ≤ ∫ x in {x | |evalForm F x| ≤ r}, w x := by
  cases n with
  | zero => exact i.elim0
  | succ n => exact realSublevel_succ hw hcompact hnneg x₀ hx₀ hw₀ i hi

/-- The original transverse weights supply the weighted sublevel lower bound. -/
theorem realSublevelLowerBound {n : ℕ} {F : IntForm n} {w : (Fin n → ℝ) → ℝ}
    (hw : TransverseWeight F w) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ → c*r ≤ ∫ x in {x | |evalForm F x| ≤ r}, w x := by
  obtain ⟨x₀,hx₀,hw₀⟩ := hw.positive_at_zero
  obtain ⟨i,b,hb,hi⟩ := hw.transverse
  exact realSublevelLowerBound_of_nonsingularZero hw.smooth.continuous hw.compact hw.nonnegative
    hx₀ hw₀ (abs_pos.mp (hb.trans_le (hi x₀ (subset_tsupport _ hw₀.ne'))))

end
end Birch
