module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Multiset.Fintype
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-! # Rank from power sums on a circle -/

open Filter
open scoped Topology BigOperators

namespace Birch

/-- A finite family of points on the unit circle has arbitrarily large
simultaneous return times to (1). -/
theorem exists_tendsto_pow_one_of_norm_eq_one {ι : Type*} [Finite ι]
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      ∀ i, Tendsto (fun m => z i ^ k m) atTop (𝓝 1) := by
  let S : Set (ι → ℂ) := {y | ∀ i, y i ∈ Metric.sphere 0 1}
  let x : ℕ → ι → ℂ := fun m i => z i ^ m
  have hS : IsCompact S := isCompact_pi_infinite (fun _ => isCompact_sphere _ _)
  have hx (m : ℕ) : x m ∈ S := by
    intro i
    simp only [Metric.mem_sphere, dist_zero_right, x, norm_pow, hz, one_pow]
  obtain ⟨y,hy,φ,hφ,ht⟩ := hS.tendsto_subseq hx
  let k (m : ℕ) := φ (m + m) - φ m
  have hk : Tendsto k atTop atTop := tendsto_atTop_mono
    (fun m => Nat.le_sub_of_add_le (hφ.add_le_nat m m)) tendsto_id
  refine ⟨k,hk,?_⟩
  intro i
  have hyi : y i ≠ 0 := by
    have h : ‖y i‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hy i
    exact norm_ne_zero_iff.mp (h.trans_ne one_ne_zero)
  have hφ' : Tendsto (fun m => z i ^ φ m) atTop (𝓝 (y i)) :=
    (tendsto_pi_nhds.mp ht) i
  have hdouble : Tendsto (fun m : ℕ => m + m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_add_right m m) tendsto_id
  have hd := (hφ'.comp hdouble).div hφ' hyi
  simp only [div_self hyi] at hd
  convert hd using 1
  funext m
  have hne : z i ≠ 0 := norm_ne_zero_iff.mp ((hz i).trans_ne one_ne_zero)
  change z i ^ (φ (m + m) - φ m) = z i ^ φ (m + m) / z i ^ φ m
  rw [div_eq_mul_inv]
  exact pow_sub₀ (z i) hne (hφ.monotone (Nat.le_add_right m m))

/-- Along a sequence of indices tending to infinity, the power sums of a
unit-circle multiset converge to its cardinality with multiplicity. -/
theorem exists_tendsto_powSum_card (A : Multiset ℂ) (hA : ∀ z ∈ A, ‖z‖ = 1) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      Tendsto (fun m => (A.map (· ^ k m)).sum) atTop (𝓝 (A.card : ℂ)) := by
  classical
  obtain ⟨k,hk,hz⟩ := exists_tendsto_pow_one_of_norm_eq_one
    (fun z : A => (z : ℂ)) (fun z => hA z Multiset.coe_mem)
  refine ⟨k,hk,?_⟩
  have hs := tendsto_finsetSum (s := (Finset.univ : Finset A)) fun z _ => hz z
  have hterms (m : ℕ) : ∑ z : A, (z : ℂ) ^ k m = (A.map (· ^ k m)).sum := by
    change ((Finset.univ : Finset A).val.map (fun z : A => (z : ℂ) ^ k m)).sum = _
    exact congrArg Multiset.sum (Multiset.map_univ A (fun z : ℂ => z ^ k m))
  have hconst : ∑ _ : A, (1 : ℂ) = (A.card : ℂ) := by simp
  simp_rw [hterms, hconst] at hs
  exact hs

/-- If the powers of a unit-circle multiset have bounded sums after
subtracting a fixed scalar, the same bound holds at the cardinality. -/
theorem norm_sub_card_le_of_eventually_norm_powSum_le (A : Multiset ℂ)
    (hA : ∀ z ∈ A, ‖z‖ = 1) (a : ℂ) (C : ℝ)
    (hbound : ∀ᶠ m : ℕ in atTop, ‖(A.map (· ^ m)).sum - a‖ ≤ C) :
    ‖(A.card : ℂ) - a‖ ≤ C := by
  obtain ⟨k,hk,h⟩ := exists_tendsto_powSum_card A hA
  exact le_of_tendsto ((h.sub tendsto_const_nhds).norm) (hk.eventually hbound)

/-- Any limit of the full sequence of unit-circle power sums is the
cardinality of the multiset. -/
theorem eq_card_of_tendsto_powSum (A : Multiset ℂ) (hA : ∀ z ∈ A, ‖z‖ = 1)
    {a : ℂ} (hlim : Tendsto (fun m : ℕ => (A.map (· ^ m)).sum) atTop (𝓝 a)) :
    a = (A.card : ℂ) := by
  obtain ⟨k,hk,h⟩ := exists_tendsto_powSum_card A hA
  exact tendsto_nhds_unique (hlim.comp hk) h

/-- A finite spectrum strictly inside the unit circle has power sums tending to zero. -/
theorem tendsto_powSum_zero_of_norm_lt_one (A : Multiset ℂ)
    (hA : ∀ z ∈ A, ‖z‖ < 1) :
    Tendsto (fun m : ℕ => (A.map (· ^ m)).sum) atTop (𝓝 0) := by
  induction A using Multiset.induction_on with
  | empty =>
    change Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)
    exact tendsto_const_nhds
  | cons a A ih =>
    simpa only [Multiset.map_cons, Multiset.sum_cons, zero_add] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hA a (Multiset.mem_cons_self a A))).add
        (ih fun z hz => hA z (Multiset.mem_cons_of_mem hz))

/-- An exponential bound on the power sums of a finite complex spectrum
bounds every individual root by the same exponential base. -/
theorem norm_mem_le_of_eventually_powSum_le (A : Multiset ℂ) {B : ℝ} (hB : 0 ≤ B) (C : ℝ)
    (hbound : ∀ᶠ m : ℕ in atTop, ‖(A.map (· ^ m)).sum‖ ≤ C * B^m) :
    ∀ z ∈ A, ‖z‖ ≤ B := by
  classical
  intro z hz
  by_contra! hbig
  have hn : A.toFinset.Nonempty := ⟨z, Multiset.mem_toFinset.mpr hz⟩
  let R := A.toFinset.sup' hn norm
  have hmax (w : ℂ) (hw : w ∈ A) : ‖w‖ ≤ R := Finset.le_sup' norm (Multiset.mem_toFinset.mpr hw)
  have hBR : B < R := hbig.trans_le (hmax z hz)
  have hR : 0 < R := hB.trans_lt hBR
  let top := A.filter (fun w => ‖w‖ = R)
  let rest := A.filter (fun w => ‖w‖ ≠ R)
  let scale (S : Multiset ℂ) : Multiset ℂ := S.map (fun w => w / (R : ℂ))
  have hsplit : top + rest = A := Multiset.filter_add_not _ _
  have hnorm (w : ℂ) : ‖w / (R : ℂ)‖ = ‖w‖ / R := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have htop (w : ℂ) (hw : w ∈ scale top) : ‖w‖ = 1 := by
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    rw [hnorm, (Multiset.mem_filter.mp hu).2, div_self hR.ne']
  have hrest (w : ℂ) (hw : w ∈ scale rest) : ‖w‖ < 1 := by
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    obtain ⟨hu, hne⟩ := Multiset.mem_filter.mp hu
    rw [hnorm, div_lt_one hR]
    exact lt_of_le_of_ne (hmax u hu) hne
  have hscaled : Tendsto (fun m : ℕ => ((scale A).map (· ^ m)).sum) atTop (𝓝 0) := by
    have hgrow : ∀ᶠ m : ℕ in atTop, ‖((scale A).map (· ^ m)).sum‖ ≤ C * (B/R)^m := by
      filter_upwards [hbound] with m hm
      simp only [scale, Multiset.map_map, Function.comp_def, div_pow]
      rw [Multiset.sum_map_div, norm_div, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hR.le, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hm (pow_nonneg hR.le m)
    have hratio : ‖B/R‖ < 1 := by
      rw [Real.norm_of_nonneg (div_nonneg hB hR.le), div_lt_one hR]
      exact hBR
    refine squeeze_zero_norm' hgrow ?_
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hratio).const_mul C
  have hsub (m : ℕ) : ((scale A).map (· ^ m)).sum - ((scale rest).map (· ^ m)).sum =
      ((scale top).map (· ^ m)).sum := by
    rw [← hsplit]
    change ((scale (top + rest)).map (· ^ m)).sum - ((scale rest).map (· ^ m)).sum = _
    simp only [scale, Multiset.map_add, Multiset.sum_add, add_sub_cancel_right]
  have hlim := hscaled.sub (tendsto_powSum_zero_of_norm_lt_one (scale rest) hrest)
  simp only [hsub, sub_zero] at hlim
  have hcard := eq_card_of_tendsto_powSum (scale top) htop hlim
  have hempty : scale top = 0 := Multiset.card_eq_zero.mp (by exact_mod_cast hcard.symm)
  obtain ⟨w, hw, heq⟩ := Finset.exists_mem_eq_sup' hn norm
  have hwTop : w ∈ top := Multiset.mem_filter.mpr ⟨Multiset.mem_toFinset.mp hw, heq.symm⟩
  have hmem : w / (R : ℂ) ∈ scale top := Multiset.mem_map.mpr ⟨w, hwTop, rfl⟩
  rw [hempty] at hmem
  exact Multiset.notMem_zero _ hmem

/-- A unit-circle spectrum whose power sums converge to the Tate
reference in a given parity is exactly that Tate spectrum. -/
theorem eq_tateUnitSpectrum_of_tendsto_powSum (A : Multiset ℂ)
    (hA : ∀ z ∈ A, ‖z‖ = 1) (evenDegree : Bool)
    (hlim : Tendsto (fun m : ℕ => (A.map (· ^ m)).sum) atTop
      (𝓝 (if evenDegree then (1 : ℂ) else 0))) :
    A = if evenDegree then {1} else 0 := by
  have hcard := eq_card_of_tendsto_powSum A hA hlim
  cases evenDegree with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hcard ⊢
    exact Multiset.card_eq_zero.mp (by exact_mod_cast hcard.symm)
  | true =>
    simp only [ite_true] at hcard hlim ⊢
    have hc : A.card = 1 := by exact_mod_cast hcard.symm
    obtain ⟨z,rfl⟩ := Multiset.card_eq_one.mp hc
    simp only [Multiset.map_singleton, Multiset.sum_singleton] at hlim
    have hsucc : Tendsto (fun m : ℕ => m + 1) atTop atTop :=
      tendsto_atTop_mono (fun m => Nat.le_add_right m 1) tendsto_id
    have hzlim : Tendsto (fun m : ℕ => z ^ (m+1)) atTop (𝓝 z) := by
      simpa only [pow_succ, one_mul] using hlim.mul_const z
    have hz : z = 1 := tendsto_nhds_unique hzlim (hlim.comp hsucc)
    rw [hz]

end Birch
