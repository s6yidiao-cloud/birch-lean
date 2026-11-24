import Birch.CircleMethod
import Birch.LatticeSummable
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Poisson summation on the integer lattice

Periodization of a compactly supported function is locally a finite sum. Its torus
Fourier coefficients are the lattice samples of the Euclidean Fourier integral.
-/

open Finset Filter Function MeasureTheory Set Topology
open scoped BigOperators

namespace Birch

noncomputable section

/-- The dot-product convention for the Fourier integral on real coordinate space. -/
def latticeFourierIntegral {n : ℕ} (f : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) : ℂ :=
  ∫ x, phase (-∑ i, ξ i * x i) * f x

private def torusProjection {n : ℕ} (x : Fin n → ℝ) : UnitAddTorus (Fin n) := fun i => x i

private theorem torusProjection_openQuotient (n : ℕ) :
    IsOpenQuotientMap (torusProjection (n := n)) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

private theorem torusProjection_add_lattice {n : ℕ} (x : Fin n → ℝ) (z : Fin n → ℤ) :
    torusProjection (x + latticeVector z) = torusProjection x := by
  funext i
  change (((x i + (z i : ℝ)) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have h : (((z i : ℤ) : ℝ) : UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨z i, by simp⟩
  rw [h, add_zero]

private def periodizeLattice {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) : ℂ :=
  ∑' z : Fin n → ℤ, f (x + latticeVector z)

private theorem periodizeLattice_add {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (x : Fin n → ℝ) (z : Fin n → ℤ) : periodizeLattice f (x + latticeVector z) = periodizeLattice f x := by
  unfold periodizeLattice
  have he (v : Fin n → ℤ) : (x + latticeVector z) + latticeVector v =
      x + latticeVector (z+v) := by
    ext i
    simp only [latticeVector, Pi.add_apply, Int.cast_add, add_assoc]
  simp_rw [he]
  exact (Equiv.addLeft z).tsum_eq (fun v : Fin n → ℤ => f (x + latticeVector v))

private theorem mem_latticeBox_abs_aux {n : ℕ} {R : ℝ} {x : Fin n → ℤ} :
    x ∈ latticeBox n R ↔ ∀ i, |(x i : ℝ)| ≤ R := by
  unfold latticeBox
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, neg_le, Int.le_floor, Int.cast_neg, abs_le]

private theorem periodizeLattice_bound {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : HasCompactSupport f) (R : ℝ) :
    ∃ S : Finset (Fin n → ℤ), ∀ x : Fin n → ℝ, ‖x‖ ≤ R →
      ∀ z ∉ S, f (x + latticeVector z) = 0 := by
  obtain ⟨B, hB⟩ := hf.isBounded.subset_closedBall (0 : Fin n → ℝ)
  refine ⟨latticeBox n (B+R), fun x hx z hz => ?_⟩
  by_contra hn
  have hnorm : ‖x + latticeVector z‖ ≤ B := by
    have hm := hB (subset_tsupport f hn)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hm
  have hnormZ : ‖latticeVector z‖ ≤ B+R := by
    calc
      _ = ‖(x + latticeVector z) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x + latticeVector z‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add hnorm hx
  apply hz (mem_latticeBox_abs_aux.mpr fun i => ?_)
  exact (by simpa only [Real.norm_eq_abs, latticeVector] using norm_le_pi_norm (latticeVector z) i :
    |(z i : ℝ)| ≤ ‖latticeVector z‖).trans hnormZ

private theorem continuous_periodizeLattice {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) : Continuous (periodizeLattice f) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨S, hS⟩ := periodizeLattice_bound hs (‖x‖+1)
  have hcont : Continuous (fun y => ∑ z ∈ S, f (y + latticeVector z)) := by
    exact continuous_finsetSum _ (fun z _ => hc.comp (continuous_id.add continuous_const))
  apply hcont.continuousAt.congr
  filter_upwards [Metric.closedBall_mem_nhds x zero_lt_one] with y hy
  have hnorm : ‖y‖ ≤ ‖x‖+1 := by
    have h₁ : ‖y-x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    linarith [norm_sub_norm_le y x]
  exact (tsum_eq_sum (fun z hz => hS y hnorm z hz)).symm

private def representativeTorus {n : ℕ} (x : UnitAddTorus (Fin n)) : Fin n → ℝ :=
  fun i => (AddCircle.equivIoc 1 0 (x i)).val

private theorem torusLift_periodize_eq {n : ℕ} (f : (Fin n → ℝ) → ℂ) (x : Fin n → ℝ) :
    periodizeLattice f (representativeTorus (torusProjection x)) = periodizeLattice f x := by
  let y := representativeTorus (torusProjection x)
  have hz (i : Fin n) : ∃ z : ℤ, (z : ℝ) = x i - y i := by
    have hc : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, show (y i : UnitAddCircle) = (x i : UnitAddCircle) from AddCircle.coe_equivIoc, sub_self]
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hc
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  have hxy : x = y + latticeVector z := by
    ext i
    simp only [Pi.add_apply, latticeVector, hz]
    ring
  change periodizeLattice f y = periodizeLattice f x
  rw [hxy]
  exact (periodizeLattice_add f y z).symm

private def latticePeriodization {n : ℕ} (f : (Fin n → ℝ) → ℂ)
    (hc : Continuous f) (hs : HasCompactSupport f) : C(UnitAddTorus (Fin n), ℂ) where
  toFun := periodizeLattice f ∘ representativeTorus
  continuous_toFun := by
    apply (torusProjection_openQuotient n).isQuotientMap.continuous_iff.mpr
    have hEq : ((periodizeLattice f ∘ representativeTorus) ∘ torusProjection) = periodizeLattice f :=
      funext (torusLift_periodize_eq f)
    rw [hEq]
    exact continuous_periodizeLattice hc hs

private def latticeCube {n : ℕ} : Set (Fin n → ℝ) := {x | ∀ i, x i ∈ Set.Ioc 0 1}

private local instance latticeTranslationAction (n : ℕ) : AddAction (Fin n → ℤ) (Fin n → ℝ) where
  vadd z x := x + latticeVector z
  zero_vadd x := by
    change x + latticeVector 0 = x
    ext i
    simp [latticeVector]
  add_vadd u v x := by
    change x + latticeVector (u+v) = (x + latticeVector v) + latticeVector u
    ext i
    simp only [latticeVector, Pi.add_apply, Int.cast_add]
    ring

private theorem lattice_vadd_eq {n : ℕ} (z : Fin n → ℤ) (x : Fin n → ℝ) : z +ᵥ x = x + latticeVector z := rfl

private local instance latticeTranslationMeasurable (n : ℕ) : MeasurableConstVAdd (Fin n → ℤ) (Fin n → ℝ) :=
  ⟨fun _ => measurable_id.add_const _⟩

private local instance latticeTranslationInvariant (n : ℕ) :
    VAddInvariantMeasure (Fin n → ℤ) (Fin n → ℝ) (volume : Measure (Fin n → ℝ)) := by
  constructor
  intro z s _
  simpa only [lattice_vadd_eq, add_comm] using measure_preimage_add volume (latticeVector z) s

private theorem latticeCube_fundamental (n : ℕ) :
    IsAddFundamentalDomain (Fin n → ℤ) (latticeCube (n := n)) := by
  refine IsAddFundamentalDomain.mk' (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)).nullMeasurableSet ?_
  intro x
  let z : Fin n → ℤ := fun i => 1 - ⌈x i⌉
  have hz : z +ᵥ x ∈ latticeCube := by
    intro i
    simp only [lattice_vadd_eq, Pi.add_apply, latticeVector, z, Int.cast_sub, Int.cast_one, Set.mem_Ioc]
    constructor
    · linarith [Int.ceil_lt_add_one (x i)]
    · linarith [Int.le_ceil (x i)]
  refine ⟨z,hz,?_⟩
  intro w hw
  ext i
  have hw' : x i + (w i : ℝ) ∈ Set.Ioc 0 1 := hw i
  have hz' : x i + (z i : ℝ) ∈ Set.Ioc 0 1 := hz i
  have hlt : ((w i - z i : ℤ) : ℝ) < 1 := by push_cast; linarith [hw'.2,hz'.1]
  have hgt : (-1 : ℝ) < ((w i - z i : ℤ) : ℝ) := by push_cast; linarith [hw'.1,hz'.2]
  have ha : (w i - z i : ℤ) < 1 := by exact_mod_cast hlt
  have hb : (-1 : ℤ) < w i - z i := by exact_mod_cast hgt
  omega

private theorem mFourier_torusProjection {n : ℕ} (z : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier z (torusProjection x) = phase (∑ i, (z i : ℝ)*x i) := by
  unfold UnitAddTorus.mFourier torusProjection phase
  simp only [ContinuousMap.coe_mk]
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  simp only [fourier_coe_apply, Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_one, div_one]
  ring_nf

private theorem latticePeriodization_coeff {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) (z : Fin n → ℤ) :
    UnitAddTorus.mFourierCoeff (latticePeriodization f hc hs) z =
      latticeFourierIntegral f (latticeVector z) := by
  let e : (Fin n → ℝ) → ℂ := fun x => UnitAddTorus.mFourier (-z) (torusProjection x)
  have he : Continuous e := (UnitAddTorus.mFourier (-z)).continuous.comp (torusProjection_openQuotient n).continuous
  have hl x w : e (x+latticeVector w) = e x := by unfold e; rw [torusProjection_add_lattice]
  obtain ⟨S,hS⟩ := periodizeLattice_bound hs 1
  have hnorm (x : Fin n → ℝ) (hx : x ∈ latticeCube) : ‖x‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hx i).1.le]
    exact (hx i).2
  have hintegrable : Integrable (fun x => e x * f x) :=
    (he.mul hc).integrable_of_hasCompactSupport hs.mul_left
  calc
    _ = ∫ x in latticeCube, e x * periodizeLattice f x := by
      rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ 0]
      simp only [Pi.zero_apply, zero_add]
      apply setIntegral_congr_fun (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc))
      intro x _
      simp only [latticePeriodization, ContinuousMap.coe_mk, Function.comp_apply, smul_eq_mul, e]
      change e x * periodizeLattice f (representativeTorus (torusProjection x)) = e x * periodizeLattice f x
      rw [torusLift_periodize_eq]
    _ = ∫ x in latticeCube, ∑ w ∈ S, e (x+latticeVector w) * f (x+latticeVector w) := by
      apply setIntegral_congr_fun (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc))
      intro x hx
      change e x * (∑' w : Fin n → ℤ, f (x + latticeVector w)) = _
      rw [tsum_eq_sum (fun w hw => hS x (hnorm x hx) w hw), Finset.mul_sum]
      simp_rw [hl]
    _ = ∑ w ∈ S, ∫ x in latticeCube, e (x+latticeVector w) * f (x+latticeVector w) := by
      apply integral_finsetSum
      intro w _
      have hint : IntegrableOn (fun x => e (x+latticeVector w) * f (x+latticeVector w))
          (Set.Icc (0 : Fin n → ℝ) 1) := ((he.mul hc).comp (continuous_id.add continuous_const)).integrableOn_Icc
      exact hint.mono_set (fun x hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩)
    _ = ∑' w : Fin n → ℤ, ∫ x in latticeCube, e (x+latticeVector w) * f (x+latticeVector w) := by
      symm
      apply tsum_eq_sum
      intro w hw
      refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      rw [hS x (hnorm x hx) w hw, mul_zero]
    _ = ∫ x, e x * f x := ((latticeCube_fundamental n).integral_eq_tsum'' _ hintegrable).symm
    _ = _ := by
      unfold latticeFourierIntegral
      simp only [e, mFourier_torusProjection, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
        latticeVector]

/-- Poisson summation for a compactly supported continuous amplitude whose lattice
Fourier samples are summable. The character and Fourier-sign conventions agree
with the lattice phase in the paper. -/
theorem poisson_lattice_of_summable {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f)
    (hF : Summable (fun k : Fin n → ℤ => latticeFourierIntegral f (latticeVector k)))
    (x : Fin n → ℝ) :
    (∑' k : Fin n → ℤ, f (x+latticeVector k)) =
      ∑' z : Fin n → ℤ, latticeFourierIntegral f (latticeVector z) *
        phase (∑ i, (z i : ℝ)*x i) := by
  let F := latticePeriodization f hc hs
  have hcoeff (z : Fin n → ℤ) : UnitAddTorus.mFourierCoeff F z =
      latticeFourierIntegral f (latticeVector z) := latticePeriodization_coeff hc hs z
  have hfun : UnitAddTorus.mFourierCoeff F = fun k => latticeFourierIntegral f (latticeVector k) :=
    funext hcoeff
  have hseries := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (f := F) (hfun.symm ▸ hF) (torusProjection x)
  have hvalue : F (torusProjection x) = ∑' k : Fin n → ℤ, f (x+latticeVector k) := torusLift_periodize_eq f x
  rw [← hvalue, ← hseries.tsum_eq]
  simp only [hcoeff, mFourier_torusProjection, smul_eq_mul]


private theorem latticeFourierIntegral_comp_smul {n : ℕ} {f : (Fin n → ℝ) → ℂ} {c : ℝ}
    (hc : 0 < c) (ξ : Fin n → ℝ) :
    latticeFourierIntegral (fun x => f (c • x)) ξ =
      (c^n)⁻¹ • latticeFourierIntegral f (c⁻¹ • ξ) := by
  let g : (Fin n → ℝ) → ℂ := fun y => phase (-∑ i, (c⁻¹ • ξ) i * y i) * f y
  have he (x : Fin n → ℝ) : phase (-∑ i, ξ i * x i) * f (c • x) = g (c • x) := by
    unfold g
    congr 3
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  unfold latticeFourierIntegral
  simp_rw [he]
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Fin n → ℝ)) g c (hR := hc.le)
  simpa [g, Module.finrank_fintype_fun_eq_card] using h

private def intResidueEquiv (q : ℕ) [NeZero q] : ℤ ≃ ZMod q × ℤ where
  toFun z := ((z : ZMod q), z / (q : ℤ))
  invFun p := (p.1.val : ℤ) + (q : ℤ)*p.2
  left_inv z := by dsimp; rw [ZMod.val_intCast, Int.emod_add_mul_ediv]
  right_inv p := by
    apply Prod.ext
    · exact (ZMod.intCast_eq_iff q _ p.1).mpr ⟨p.2, rfl⟩
    · change ((p.1.val : ℤ) + (q : ℤ)*p.2) / (q : ℤ) = p.2
      have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
      rw [Int.add_mul_ediv_left _ _ hq, Int.ediv_eq_zero_of_lt (by positivity)
        (by exact_mod_cast ZMod.val_lt p.1), zero_add]

private def intResidueVectorEquiv (q n : ℕ) [NeZero q] :
    ((Fin n → ZMod q) × (Fin n → ℤ)) ≃ (Fin n → ℤ) :=
  (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ZMod q) (fun _ => ℤ)).symm.trans
    (Equiv.piCongrRight fun _ => (intResidueEquiv q).symm)

private lemma norm_lattice_phase (t : ℝ) : ‖phase t‖ = 1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- Apply Poisson summation after splitting the integer lattice by residue classes.
The finite transform of the periodic multiplier uses the positive sign in the
exponent. `f` is sampled at scale `1/P`, and the Fourier frequencies are `P/q`
times integer vectors. -/
theorem poisson_lattice_weighted_residues {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) {P : ℝ} (hP : 0 < P)
    (q : ℕ) [NeZero q] (weight : (Fin n → ZMod q) → ℂ)
    (hFourier : Summable (fun z : Fin n → ℤ => ‖latticeFourierIntegral f ((P/(q : ℝ)) • latticeVector z)‖)) :
    (∑' x : Fin n → ℤ, weight (fun i => (x i : ZMod q)) * f (P⁻¹ • latticeVector x)) =
      ((P/(q : ℝ))^n : ℝ) • ∑' z : Fin n → ℤ,
        (∑ t : Fin n → ZMod q, weight t * phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(q : ℝ))) *
          latticeFourierIntegral f ((P/(q : ℝ)) • latticeVector z) := by
  let H (x : Fin n → ℤ) : ℂ := weight (fun i => (x i : ZMod q)) * f (P⁻¹ • latticeVector x)
  let A (x : Fin n → ℝ) := f ((q/P : ℝ) • x)
  let R (t : Fin n → ZMod q) : Fin n → ℝ := fun i => ((t i).val : ℝ)/(q : ℝ)
  let C := (P/(q : ℝ))^n
  let L (z : Fin n → ℤ) := latticeFourierIntegral f ((P/(q : ℝ)) • latticeVector z)
  let E (z : Fin n → ℤ) (t : Fin n → ZMod q) := phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(q : ℝ))
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hscale : 0 < (q/P : ℝ) := div_pos hq hP
  have hA : Continuous A := hc.comp (show Continuous (fun x : Fin n → ℝ => (q/P : ℝ) • x) by fun_prop)
  have hAc : HasCompactSupport A := hs.comp_smul hscale.ne'
  have hSamp (z : Fin n → ℤ) : latticeFourierIntegral A (latticeVector z) = C • L z := by
    rw [latticeFourierIntegral_comp_smul hscale, ← inv_pow, inv_div]
  have hsumA : Summable (fun z : Fin n → ℤ => latticeFourierIntegral A (latticeVector z)) := by
    simp_rw [hSamp]
    exact Summable.const_smul C hFourier.of_norm
  have hpoint (t : Fin n → ZMod q) :
      (∑' x : Fin n → ℤ, A (R t + latticeVector x)) = C • ∑' z : Fin n → ℤ, L z * E z t := by
    rw [poisson_lattice_of_summable hA hAc hsumA]
    simp_rw [hSamp, Algebra.smul_def, mul_assoc, tsum_mul_left, R, E, mul_div_assoc]
  have hH : Summable H := by
    obtain ⟨S,hS⟩ := periodizeLattice_bound (hs.comp_smul (inv_ne_zero hP.ne')) 0
    apply summable_of_ne_finset_zero (s := S)
    intro x hx
    have hx' := hS 0 (by simp) x hx
    simp only [zero_add] at hx'
    simp [H, hx']
  let equiv := intResidueVectorEquiv q n
  have hequiv (t : Fin n → ZMod q) (v : Fin n → ℤ) : H (equiv (t,v)) =
      weight t * A (R t + latticeVector v) := by
    have hreindex (i : Fin n) : equiv (t,v) i = ((t i).val : ℤ) + (q : ℤ)*v i := rfl
    unfold H A
    congr 2
    · funext i
      rw [hreindex]
      exact (ZMod.intCast_eq_iff q _ (t i)).mpr ⟨v i, rfl⟩
    · ext i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, latticeVector, hreindex,
        Int.cast_add, Int.cast_natCast, Int.cast_mul, R]
      field_simp
  have hsplit : (∑' x : Fin n → ℤ, H x) =
      ∑ t : Fin n → ZMod q, weight t * ∑' v : Fin n → ℤ, A (R t + latticeVector v) := by
    rw [← equiv.tsum_eq H]
    have hh : Summable (fun p => H (equiv p)) := equiv.summable_iff.mpr hH
    rw [hh.tsum_prod, tsum_fintype]
    simp_rw [hequiv, tsum_mul_left]
  have hterm (t : Fin n → ZMod q) : Summable (fun z : Fin n → ℤ => weight t * (L z * E z t)) := by
    apply Summable.of_norm
    simp only [norm_mul, E, norm_lattice_phase, mul_one]
    exact hFourier.mul_left _
  calc
    _ = ∑ t : Fin n → ZMod q, weight t * ∑' v : Fin n → ℤ, A (R t + latticeVector v) := hsplit
    _ = C • ∑' z : Fin n → ℤ, ∑ t : Fin n → ZMod q, weight t * (L z * E z t) := by
      simp_rw [hpoint, mul_smul_comm, ← Finset.smul_sum, ← tsum_mul_left]
      rw [Summable.tsum_finsetSum (fun t _ => hterm t)]
    _ = _ := by
      apply congrArg (C • ·)
      apply tsum_congr
      intro z
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      ring


/-- Completing a periodic lattice sum bounds its normalized magnitude by a bound
for the normalized periodic Fourier coefficients times the sum of the norms of
the sampled Euclidean Fourier transform. -/
theorem normalized_lattice_residue_bound {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hc : Continuous f) (hs : HasCompactSupport f) {P : ℝ} (hP : 0 < P)
    (q : ℕ) [NeZero q] (weight : (Fin n → ZMod q) → ℂ) {D : ℝ}
    (hD : ∀ z : Fin n → ℤ, ‖((q : ℂ)^n)⁻¹ * ∑ t : Fin n → ZMod q,
        weight t * phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(q : ℝ))‖ ≤ D)
    (hFourier : Summable (fun z : Fin n → ℤ => ‖latticeFourierIntegral f ((P/(q : ℝ)) • latticeVector z)‖)) :
    ‖∑' x : Fin n → ℤ, weight (fun i => (x i : ZMod q)) * f (P⁻¹ • latticeVector x)‖ / P^n ≤
      D * ∑' z : Fin n → ℤ, ‖latticeFourierIntegral f ((P/(q : ℝ)) • latticeVector z)‖ := by
  let S := ∑' x : Fin n → ℤ, weight (fun i => (x i : ZMod q)) * f (P⁻¹ • latticeVector x)
  let c (z : Fin n → ℤ) : ℂ := ((q : ℂ)^n)⁻¹ * ∑ t : Fin n → ZMod q,
    weight t * phase (∑ i, (z i : ℝ)*((t i).val : ℝ)/(q : ℝ))
  let A (z : Fin n → ℤ) := latticeFourierIntegral f ((P/(q : ℝ)) • latticeVector z)
  have hExact : (P^n)⁻¹ • S = ∑' z : Fin n → ℤ, c z * A z := by
    have heq := poisson_lattice_weighted_residues hc hs hP q weight hFourier
    change S = _ at heq
    rw [heq, smul_smul, show (P^n)⁻¹ * (P/(q : ℝ))^n = ((q : ℝ)^n)⁻¹ by
      rw [div_pow]
      field_simp]
    simp only [Algebra.smul_def, ← tsum_mul_left]
    apply tsum_congr
    intro z
    unfold c A
    change ((((q : ℝ)^n)⁻¹ : ℝ) : ℂ) * _ = _
    push_cast
    rw [mul_assoc]
    rfl
  have hpoint (z : Fin n → ℤ) : ‖c z * A z‖ ≤ D * ‖A z‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hD z) (norm_nonneg _)
  have hsum : Summable (fun z : Fin n → ℤ => ‖c z * A z‖) :=
    (hFourier.mul_left D).of_nonneg_of_le (fun z => norm_nonneg _) hpoint
  change ‖S‖ / P^n ≤ _
  calc
    _ = ‖(P^n)⁻¹ • S‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
    _ ≤ ∑' z : Fin n → ℤ, ‖c z * A z‖ := hExact ▸ norm_tsum_le_tsum_norm hsum
    _ ≤ _ := by rw [← tsum_mul_left]; exact hsum.tsum_le_tsum hpoint (hFourier.mul_left D)

end

end Birch
