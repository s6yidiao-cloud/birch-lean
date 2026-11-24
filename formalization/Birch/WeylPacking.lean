import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

open MeasureTheory Measure Metric Set Module

namespace Birch

noncomputable section

/-- A finite set in a radius-R ball has at most the standard volume ratio many
points at pairwise distance at least δ. -/
theorem separated_finset_card_le_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (T : Finset E) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hT : ∀ x ∈ T, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → δ ≤ dist x y) :
    (T.card : ℝ) ≤ (1 + 2 * R / δ)^finrank ℝ E := by
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  let r : ℝ := δ/2
  have hr : 0 < r := half_pos hδ
  have hRr : 0 < R + r := by linarith
  have hdis : Set.PairwiseDisjoint (↑T : Set E) (fun x => ball x r) := by
    intro x hx y hy hxy
    apply Set.disjoint_left.mpr
    intro z hxz hyz
    have hxz' : dist z x < r := mem_ball.mp hxz
    have hyz' : dist z y < r := mem_ball.mp hyz
    have htri := dist_triangle x z y
    rw [dist_comm x z] at htri
    have hrδ : r + r = δ := by dsimp [r]; ring
    linarith [hsep x hx y hy hxy]
  have hsubset : (⋃ x ∈ T, ball x r) ⊆ ball (0 : E) (R+r) := by
    intro z hz
    simp only [mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    apply mem_ball.mpr
    have htri := dist_triangle z x (0 : E)
    simp only [dist_zero_right] at htri ⊢
    linarith [mem_ball.mp hz, hT x hx]
  have hvol : 0 < μ.real (ball (0 : E) 1) := by
    have hp : 0 < μ (ball (0 : E) 1) := isOpen_ball.measure_pos μ ⟨0, mem_ball_self zero_lt_one⟩
    exact ENNReal.toReal_pos hp.ne' (measure_ball_lt_top.ne)
  have hreal (x : E) {s : ℝ} (hs : 0 < s) :
      μ.real (ball x s) = s^finrank ℝ E * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, addHaar_ball_of_pos _ _ hs, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hm : μ.real (⋃ x ∈ T, ball x r) ≤ μ.real (ball (0 : E) (R+r)) :=
    measureReal_mono hsubset measure_ball_lt_top.ne
  rw [measureReal_biUnion_finset hdis (fun _ _ => measurableSet_ball)
    (fun _ _ => measure_ball_lt_top.ne), hreal _ hRr] at hm
  simp_rw [hreal _ hr] at hm
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at hm
  have hm' := le_of_mul_le_mul_right hm hvol
  have hexp : (R + r) / r = 1 + 2 * R / δ := by
    dsimp [r]
    field_simp
    ring
  rw [← hexp, div_pow]
  exact (le_div_iff₀ (pow_pos hr _)).mpr hm'

/-- A maximal separated subfamily covers a finite set with the sharp dimension
exponent in its covering bound. -/
theorem exists_finite_ball_cover_card_le_pow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ] (T : Finset E) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hT : ∀ x ∈ T, ‖x‖ ≤ R) :
    ∃ S : Finset E, S ⊆ T ∧ (∀ x ∈ T, ∃ y ∈ S, dist x y < δ) ∧
      (S.card : ℝ) ≤ (1 + 2 * R / δ)^finrank ℝ E := by
  classical
  let f (S : Finset E) := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y
  let U := T.powerset.filter f
  have hU : U.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    simp [f]
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image U Finset.card hU
  have hST := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hSf := (Finset.mem_filter.mp hS).2
  refine ⟨S, hST, ?_, separated_finset_card_le_pow μ S hR hδ (fun x hx => hT x (hST hx)) hSf⟩
  intro x hx
  by_contra! h
  have hxS : x ∉ S := fun H => (not_le_of_gt hδ) ((dist_self x).symm ▸ h x H)
  have hIns : insert x S ∈ U := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hST), ?_⟩
    intro y hy z hz hyz
    by_cases hyx : y = x
    · subst y
      exact h z ((Finset.mem_insert.mp hz).resolve_left hyz.symm)
    · have hyS := (Finset.mem_insert.mp hy).resolve_left hyx
      by_cases hzx : z = x
      · subst z
        rw [dist_comm]
        exact h y hyS
      · exact hSf y hyS z ((Finset.mem_insert.mp hz).resolve_left hzx) hyz
  have hle := hmax (insert x S) hIns
  rw [Finset.card_insert_of_notMem hxS] at hle
  omega

/-- A finite collection whose close pairs have differences in U has at most
the covering bound times the cardinality of U. -/
theorem finset_card_le_cover_times_differences {G E : Type*} [AddCommGroup G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]
    (T U : Finset G) (f : (↑T : Type _) → E) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ) (hTf : ∀ t, ‖f t‖ ≤ R)
    (hdiff : ∀ x y : (↑T : Type _), dist (f x) (f y) < δ → x.val - y.val ∈ U) :
    (T.card : ℝ) ≤ (1 + 2 * R / δ)^finrank ℝ E * (U.card : ℝ) := by
  classical
  let A := (Finset.univ : Finset (↑T : Type _)).image f
  have hA (a : E) (ha : a ∈ A) : ‖a‖ ≤ R := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ha
    exact hTf t
  obtain ⟨B, hBA, hcover, hBcard⟩ := exists_finite_ball_cover_card_le_pow μ A hR hδ hA
  have hrep (b : B) : ∃ t : (↑T : Type _), f t = b.val := by
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hBA b.property)
    exact ⟨t, ht⟩
  choose rep hrep using hrep
  have hchoose (t : (↑T : Type _)) : ∃ b : B, dist (f t) b.val < δ := by
    obtain ⟨b, hb, hdist⟩ := hcover (f t) (Finset.mem_image_of_mem f (Finset.mem_univ t))
    exact ⟨⟨b, hb⟩, hdist⟩
  choose pick hpick using hchoose
  let g (t : (↑T : Type _)) : (↑B : Type _) × (↑U : Type _) :=
    ⟨pick t, ⟨t.val - (rep (pick t)).val,
      hdiff t (rep (pick t)) (by rw [hrep]; exact hpick t)⟩⟩
  have hg : Function.Injective g := by
    intro x y h
    have h₁ : pick x = pick y := congrArg Prod.fst h
    have h₂ : x.val - (rep (pick x)).val = y.val - (rep (pick y)).val :=
      congrArg (fun p => p.2.val) h
    rw [h₁] at h₂
    exact Subtype.ext (sub_left_inj.mp h₂)
  have hcard : T.card ≤ B.card * U.card := by
    simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective g hg
  refine (show (T.card : ℝ) ≤ (B.card : ℝ) * (U.card : ℝ) by exact_mod_cast hcard).trans ?_
  exact mul_le_mul_of_nonneg_right hBcard (Nat.cast_nonneg _)

end
end Birch
