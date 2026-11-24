import Birch.CircleMethod
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Finite translation differencing

Translate a finitely supported function by each selected shift and apply
Cauchy–Schwarz on the translated support window. The second coordinate of a pair
of shifts determines that pair when its difference is fixed.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Birch

noncomputable section

private lemma sum_translate_window {G A : Type*} [AddCommGroup G] [DecidableEq G]
    [AddCommMonoid A] (f : G → A) (support window : Finset G) (v : G)
    (hf : ∀ x, f x ≠ 0 → x ∈ support) (hw : ∀ x ∈ support, x - v ∈ window) :
    (∑ x ∈ window, f (x+v)) = ∑ x ∈ support, f x := by
  have hinj : Function.Injective (fun x : G => x+v) := fun x y h => add_right_cancel h
  rw [← Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
  symm
  apply Finset.sum_subset
  · intro x hx
    exact Finset.mem_image.mpr ⟨x-v, hw x hx, sub_add_cancel _ _⟩
  · intro x _ hxs
    by_contra hne
    exact hxs (hf x hne)

/-- A finite van der Corput inequality with an explicit bound on the multiplicity
of each shift difference. The finite window contains the support of every translate. -/
theorem vanDerCorput_finite {G : Type*} [AddCommGroup G] [DecidableEq G]
    (f : G → ℂ) (support shifts window : Finset G)
    (hf : ∀ x, f x ≠ 0 → x ∈ support)
    (hwindow : ∀ x ∈ support, ∀ v ∈ shifts, x - v ∈ window)
    (hshift : shifts.Nonempty) :
    ‖∑ x ∈ support, f x‖^2 ≤ ((window.card : ℝ)/(shifts.card : ℝ)) *
      ∑ u ∈ (shifts.product shifts).image (fun q => q.1 - q.2),
        ‖∑ x ∈ support, f (x+u) * conj (f x)‖ := by
  let A : G → ℂ := fun x => ∑ v ∈ shifts, f (x+v)
  let pairs := shifts.product shifts
  let diff : G × G → G := fun q => q.1 - q.2
  let diffs := pairs.image diff
  let corr (u : G) : ℂ := ∑ x ∈ support, f (x+u) * conj (f x)
  have hcard : (0 : ℝ) < shifts.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hshift)
  have havg : (∑ x ∈ window, A x) = (shifts.card : ℂ) * ∑ x ∈ support, f x := by
    unfold A
    rw [Finset.sum_comm]
    calc
      _ = ∑ _v ∈ shifts, ∑ x ∈ support, f x := by
        apply Finset.sum_congr rfl
        intro v hv
        exact sum_translate_window f support window v hf (fun x hx => hwindow x hx v hv)
      _ = _ := by simp [nsmul_eq_mul]
  have hCauchy : ‖∑ x ∈ window, A x‖^2 ≤ (window.card : ℝ) * ∑ x ∈ window, ‖A x‖^2 := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le window A) 2).trans ?_
    simpa using Finset.sum_mul_sq_le_sq_mul_sq window (fun _ => (1 : ℝ)) (fun x => ‖A x‖)
  have hproduct (x : G) : ((‖A x‖^2 : ℝ) : ℂ) =
      ∑ q ∈ pairs, f (x+q.1) * conj (f (x+q.2)) := by
    rw [Complex.sq_norm, ← Complex.mul_conj]
    simp only [A, map_sum, Finset.sum_mul, Finset.mul_sum]
    exact (Finset.sum_product_right' shifts shifts (fun v w => f (x+v) * conj (f (x+w)))).symm
  have hcorr (q : G × G) (hq : q ∈ pairs) :
      (∑ x ∈ window, f (x+q.1) * conj (f (x+q.2))) = corr (diff q) := by
    have hv : q.2 ∈ shifts := (Finset.mem_product.mp hq).2
    let F : G → ℂ := fun x => f (x+diff q) * conj (f x)
    have hF (x : G) (hx : F x ≠ 0) : x ∈ support := by
      apply hf x
      intro h
      exact hx (by simp [F, h])
    have h := sum_translate_window F support window q.2 hF (fun x hx => hwindow x hx _ hv)
    simpa only [F, diff, add_assoc, add_sub_cancel, corr] using h
  have hsum : ((∑ x ∈ window, ‖A x‖^2 : ℝ) : ℂ) = ∑ q ∈ pairs, corr (diff q) := by
    simp_rw [Complex.ofReal_sum, hproduct]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl hcorr
  have hnorm : (∑ x ∈ window, ‖A x‖^2) ≤ ∑ q ∈ pairs, ‖corr (diff q)‖ := by
    have hn : 0 ≤ ∑ x ∈ window, ‖A x‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      _ = ‖((∑ x ∈ window, ‖A x‖^2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
      _ = ‖∑ q ∈ pairs, corr (diff q)‖ := by rw [hsum]
      _ ≤ _ := norm_sum_le _ _
  have hmult (u : G) : (pairs.filter (fun q => diff q = u)).card ≤ shifts.card := by
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro q hq
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
    · intro a ha b hb h
      have hdiff : diff a = diff b := ((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp hb).2).symm
      apply Prod.ext _ h
      dsimp only [diff] at hdiff
      rw [show a.2 = b.2 from h] at hdiff
      exact sub_left_inj.mp hdiff
  have hgroup : (∑ q ∈ pairs, ‖corr (diff q)‖) ≤ (shifts.card : ℝ) * ∑ u ∈ diffs, ‖corr u‖ := by
    rw [← Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem diff hq)
      (fun q => ‖corr (diff q)‖), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u _
    calc
      _ = ∑ _q ∈ pairs.filter (fun q => diff q = u), ‖corr u‖ := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.mp hq).2]
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmult u) (norm_nonneg _)
  rw [havg, Complex.norm_mul, Complex.norm_natCast] at hCauchy
  change ‖∑ x ∈ support, f x‖^2 ≤ ((window.card : ℝ)/(shifts.card : ℝ)) * ∑ u ∈ diffs, ‖corr u‖
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hcard).mpr
  apply le_of_mul_le_mul_right _ hcard
  calc
    _ = ((shifts.card : ℝ) * ‖∑ x ∈ support, f x‖)^2 := by ring
    _ ≤ (window.card : ℝ) * ∑ x ∈ window, ‖A x‖^2 := hCauchy
    _ ≤ (window.card : ℝ) * ((shifts.card : ℝ) * ∑ u ∈ diffs, ‖corr u‖) :=
      mul_le_mul_of_nonneg_left (hnorm.trans hgroup) (by positivity)
    _ = _ := by ring


/-- The lattice differencing inequality with integer dilation `m`. In the sum of
correlations, `u` is the difference of the undilated shifts. -/
theorem vanDerCorput_dilatedLattice {n : ℕ}
    (f : (Fin n → ℤ) → ℂ) (support shifts window : Finset (Fin n → ℤ))
    {m : ℤ} (hm : m ≠ 0) (hf : ∀ x, f x ≠ 0 → x ∈ support)
    (hw : ∀ x ∈ support, ∀ v ∈ shifts, x - m • v ∈ window)
    (hshift : shifts.Nonempty) :
    ‖∑ x ∈ support, f x‖^2 ≤ ((window.card : ℝ)/(shifts.card : ℝ)) *
      ∑ u ∈ (shifts.product shifts).image (fun q => q.1 - q.2),
        ‖∑ x ∈ support, f (x+m • u) * conj (f x)‖ := by
  classical
  let dil : (Fin n → ℤ) → (Fin n → ℤ) := fun v => m • v
  let V := shifts.image dil
  have hinj : Function.Injective dil := by
    intro v w h
    ext i
    have hi := congrFun h i
    change m * v i = m * w i at hi
    exact mul_left_cancel₀ hm hi
  have hV : ∀ x ∈ support, ∀ v ∈ V, x - v ∈ window := by
    intro x hx v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    exact hw x hx y hy
  have h := vanDerCorput_finite f support V window hf hV (hshift.image dil)
  have hcard : V.card = shifts.card := Finset.card_image_of_injective shifts hinj
  rw [hcard] at h
  let δ : (Fin n → ℤ) × (Fin n → ℤ) → (Fin n → ℤ) := fun q => q.1 - q.2
  have hD : (V.product V).image δ = ((shifts.product shifts).image δ).image dil := by
    ext u
    constructor
    · intro hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
      obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp hq₁
      obtain ⟨b, hb, hqb⟩ := Finset.mem_image.mp hq₂
      exact Finset.mem_image.mpr ⟨δ (a,b), Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, rfl⟩,
        by dsimp [δ, dil] at *; rw [zsmul_sub, hqa, hqb]⟩
    · intro hu
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hqa, hqb⟩ := Finset.mem_product.mp hq
      refine Finset.mem_image.mpr ⟨(dil q.1, dil q.2), Finset.mem_product.mpr ?_, ?_⟩
      · exact ⟨Finset.mem_image_of_mem _ hqa, Finset.mem_image_of_mem _ hqb⟩
      · exact (zsmul_sub q.1 q.2 m).symm
  change ‖∑ x ∈ support, f x‖^2 ≤ ((window.card : ℝ)/(shifts.card : ℝ)) *
      ∑ u ∈ (V.product V).image δ, ‖∑ x ∈ support, f (x+u) * conj (f x)‖ at h
  rw [hD, Finset.sum_image (fun _ _ _ _ h => hinj h)] at h
  exact h


/-- The integer shifts in the paper's half-open box `[0,H/2)^n`. -/
def differencingShifts (n : ℕ) (H : ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Ico 0 ⌈H / 2⌉)

/-- Differences of pairs of shifts in `[0,H/2)^n`. -/
def differencingDirections (n : ℕ) (H : ℝ) : Finset (Fin n → ℤ) :=
  ((differencingShifts n H).product (differencingShifts n H)).image (fun q => q.1 - q.2)

private lemma mem_differencingShifts {n : ℕ} {H : ℝ} {v : Fin n → ℤ} :
    v ∈ differencingShifts n H ↔ ∀ i, 0 ≤ (v i : ℝ) ∧ (v i : ℝ) < H/2 := by
  simp only [differencingShifts, Fintype.mem_piFinset, Finset.mem_Ico, Int.lt_ceil]
  exact forall_congr' fun _ => and_congr_left' (by exact_mod_cast (Iff.rfl : (0 : ℤ) ≤ _ ↔ (0 : ℤ) ≤ _))

private lemma mem_latticeBox_abs {n : ℕ} {R : ℝ} {x : Fin n → ℤ} :
    x ∈ latticeBox n R ↔ ∀ i, |(x i : ℝ)| ≤ R := by
  unfold latticeBox
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, neg_le, Int.le_floor, Int.cast_neg, abs_le]

/-- Each point of the closed box is the difference of two nonnegative shifts
in the half-open box of radius `U + 1`. -/
theorem latticeBox_subset_differencingDirections {n : ℕ} {U : ℝ} (hU : 0 ≤ U) :
    latticeBox n U ⊆ differencingDirections n (2*U+2) := by
  intro x hx
  let v : Fin n → ℤ := fun i => max (x i) 0
  let w : Fin n → ℤ := fun i => max (-(x i)) 0
  have hv : v ∈ differencingShifts n (2*U+2) := mem_differencingShifts.mpr fun i => by
    have H := abs_le.mp (mem_latticeBox_abs.mp hx i)
    simp only [v, Int.cast_max, Int.cast_zero, le_max_iff, max_lt_iff]
    exact ⟨Or.inr le_rfl, by linarith, by linarith⟩
  have hw : w ∈ differencingShifts n (2*U+2) := mem_differencingShifts.mpr fun i => by
    have H := abs_le.mp (mem_latticeBox_abs.mp hx i)
    simp only [w, Int.cast_max, Int.cast_neg, Int.cast_zero, le_max_iff, max_lt_iff]
    exact ⟨Or.inr le_rfl, by linarith, by linarith⟩
  apply Finset.mem_image.mpr
  exact ⟨(v,w), Finset.mem_product.mpr ⟨hv,hw⟩, funext fun i => by
    change max (x i) 0 - max (-(x i)) 0 = x i
    omega⟩

/-- Every coordinate of a differencing direction lies strictly between `-H` and `H`. -/
theorem abs_differencingDirection_lt {n : ℕ} {H : ℝ} (hH : 0 < H) {u : Fin n → ℤ}
    (hu : u ∈ differencingDirections n H) (i : Fin n) : |(u i : ℝ)| < H := by
  rcases Finset.mem_image.mp hu with ⟨⟨v,w⟩, hp, rfl⟩
  rcases Finset.mem_product.mp hp with ⟨hv, hw⟩
  obtain ⟨hv₁, hv₂⟩ := mem_differencingShifts.mp hv i
  obtain ⟨hw₁, hw₂⟩ := mem_differencingShifts.mp hw i
  simp only [Pi.sub_apply, Int.cast_sub, abs_lt]
  constructor <;> linarith

private lemma card_differencingShifts_bound (n : ℕ) {H : ℝ} (hH : 0 < H) :
    (H/2)^n ≤ ((differencingShifts n H).card : ℝ) := by
  unfold differencingShifts
  rw [Fintype.card_piFinset_const, Nat.cast_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hceil : (0 : ℤ) ≤ ⌈H / 2⌉ := (Int.ceil_pos.mpr (by positivity : 0 < H/2)).le
  have hcardZ := Int.card_Ico_of_le _ _ hceil
  have hcard : (((Finset.Ico (0 : ℤ) ⌈H/2⌉).card : ℕ) : ℝ) = (⌈H/2⌉ : ℤ) := by
    exact_mod_cast (by simpa only [sub_zero] using hcardZ)
  rw [hcard]
  exact Int.le_ceil (H/2)

private lemma card_window_bound (n : ℕ) {P : ℝ} (hP : 1 ≤ P) :
    ((latticeBox n (2*P)).card : ℝ) ≤ (5*P)^n := by
  unfold latticeBox
  rw [Fintype.card_piFinset_const, Nat.cast_pow]
  apply pow_le_pow_left₀ (by positivity)
  have h0 := Int.floor_nonneg.mpr (show (0 : ℝ) ≤ 2*P by linarith)
  have hEnd : -⌊2*P⌋ ≤ ⌊2*P⌋ + 1 := by omega
  have hcard : (((Finset.Icc (-⌊2*P⌋) ⌊2*P⌋).card : ℕ) : ℝ) = (⌊2*P⌋ : ℝ) + 1 - (-(⌊2*P⌋ : ℝ)) := by
    exact_mod_cast Int.card_Icc_of_le _ _ hEnd
  rw [hcard]
  linarith [Int.floor_le (2*P)]

/-- One normalized lattice differencing step, with the explicit support and cardinality
bounds for the paper's choice of translations. -/
theorem vanDerCorput_normalized_latticeBox {n : ℕ} {P H : ℝ} {m : ℤ}
    (hP : 1 ≤ P) (hH : 0 < H) (hm : 0 < m) (hmH : (m : ℝ)*H ≤ P)
    (f : (Fin n → ℤ) → ℂ) (hf : ∀ x, f x ≠ 0 → x ∈ latticeBox n P) :
    (‖∑ x ∈ latticeBox n P, f x‖ / P^n)^2 ≤ ((10 : ℝ)^n / H^n) *
      ∑ u ∈ differencingDirections n H, (‖∑ x ∈ latticeBox n P, f (x + m • u) * conj (f x)‖ / P^n) := by
  let T := latticeBox n P
  let V := differencingShifts n H
  let W := latticeBox n (2*P)
  let D := differencingDirections n H
  let R (u : Fin n → ℤ) : ℝ := ‖∑ x ∈ T, f (x + m • u) * conj (f x)‖
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hwindow (x : Fin n → ℤ) (hx : x ∈ T) (v : Fin n → ℤ) (hv : v ∈ V) : x - m • v ∈ W := by
    apply mem_latticeBox_abs.mpr
    intro i
    have hxi := mem_latticeBox_abs.mp hx i
    obtain ⟨hvi₁, hvi₂⟩ := mem_differencingShifts.mp hv i
    have hp := mul_le_mul_of_nonneg_left hvi₂.le hmR.le
    simp only [Pi.sub_apply, Pi.smul_apply, Int.zsmul_eq_mul, Int.cast_sub, Int.cast_mul]
    apply abs_le.mpr
    obtain ⟨h₁, h₂⟩ := abs_le.mp hxi
    constructor <;> nlinarith [mul_nonneg hmR.le hvi₁]
  have hVsmall : (H/2)^n ≤ (V.card : ℝ) := card_differencingShifts_bound n hH
  have hVpos : (0 : ℝ) < V.card := lt_of_lt_of_le (by positivity) hVsmall
  have hVn : V.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hVpos)
  have hvdc : ‖∑ x ∈ T, f x‖^2 ≤ ((W.card : ℝ)/(V.card : ℝ)) * ∑ u ∈ D, R u :=
    vanDerCorput_dilatedLattice f T V W (ne_of_gt hm) hf hwindow hVn
  have hratio : (W.card : ℝ)/(V.card : ℝ) ≤ (5*P)^n/(H/2)^n :=
    (div_le_div_of_nonneg_right (card_window_bound n hP) hVpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hVsmall)
  have hS : 0 ≤ ∑ u ∈ D, R u := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hV := hvdc.trans (mul_le_mul_of_nonneg_right hratio hS)
  change (‖∑ x ∈ T, f x‖ / P^n)^2 ≤ ((10 : ℝ)^n / H^n) * ∑ u ∈ D, (R u / P^n)
  rw [div_pow]
  refine (div_le_div_of_nonneg_right hV (by positivity)).trans_eq ?_
  have hPn : P^n ≠ 0 := pow_ne_zero _ (by linarith)
  have hHn : H^n ≠ 0 := pow_ne_zero _ hH.ne'
  have h5 : (5 : ℝ)^n * 2^n = 10^n := by rw [← mul_pow]; norm_num
  rw [← Finset.sum_div, mul_pow, div_pow]
  calc
    _ = ((5 : ℝ)^n * 2^n) / H^n * ((∑ u ∈ D, R u) / P^n) := by field_simp
    _ = _ := by rw [h5]


/-- Choose a term using the largest capped contribution across the finitely many classes. -/
theorem exists_direction_of_class_bounds {G J : Type*} [DecidableEq J] [Fintype J]
    (D : Finset G) (hD : D.Nonempty) (s : G → J) (a : G → ℝ) (cap : J → ℝ)
    (ha : ∀ u ∈ D, 0 ≤ a u)
    (hcap : ∀ j, ((D.filter (fun u => s u = j)).card : ℝ) ≤ cap j) :
    ∃ u ∈ D, (∑ v ∈ D, a v) ≤ (Fintype.card J : ℝ) * (cap (s u) * a u) := by
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image D (fun u => cap (s u) * a u) hD
  refine ⟨u, hu, ?_⟩
  have hnonneg : 0 ≤ cap (s u) * a u :=
    mul_nonneg ((Nat.cast_nonneg _).trans (hcap _)) (ha u hu)
  have hfiber (j : J) : (∑ v ∈ D.filter (fun u => s u = j), a v) ≤ cap (s u) * a u := by
    let Dj := D.filter (fun u => s u = j)
    by_cases hDj : Dj.Nonempty
    · obtain ⟨v, hv, hmaxj⟩ := Finset.exists_max_image Dj a hDj
      rcases Finset.mem_filter.mp hv with ⟨hvD, hvj⟩
      calc
        _ ≤ ∑ _w ∈ Dj, a v := Finset.sum_le_sum hmaxj
        _ = (Dj.card : ℝ) * a v := by simp [nsmul_eq_mul]
        _ ≤ cap j * a v := mul_le_mul_of_nonneg_right (hcap j) (ha v hvD)
        _ ≤ _ := hvj ▸ hmax v hvD
    · have hEmpty : Dj = ∅ := Finset.not_nonempty_iff_eq_empty.mp hDj
      change (∑ v ∈ Dj, a v) ≤ _
      simpa [hEmpty] using hnonneg
  calc
    _ = ∑ j ∈ (Finset.univ : Finset J), ∑ v ∈ D.filter (fun u => s u = j), a v :=
      (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) a).symm
    _ ≤ ∑ _j ∈ (Finset.univ : Finset J), cap (s u) * a u := Finset.sum_le_sum fun j _ => hfiber j
    _ = _ := by simp [nsmul_eq_mul]

/-- A normalized differencing step retaining the loss from the chosen direction's
singular-dimension class, once the cardinality bounds for the classes are supplied. -/
theorem normalized_differencing_of_direction_counts {n : ℕ} {P H : ℝ} {m : ℤ}
    (hP : 1 ≤ P) (hH : 0 < H) (hm : 0 < m) (hmH : (m : ℝ)*H ≤ P)
    (f : (Fin n → ℤ) → ℂ) (hf : ∀ x, f x ≠ 0 → x ∈ latticeBox n P)
    (s : (Fin n → ℤ) → Fin (n+1)) (s₀ : ℕ) (K : ℝ)
    (hcount : ∀ j : Fin (n+1),
      (((differencingDirections n H).filter (fun u => s u = j)).card : ℝ) ≤
        K * H ^ ((n : ℝ) - ((j.val - s₀ : ℕ) : ℝ))) :
    ∃ u ∈ differencingDirections n H,
      (‖∑ x ∈ latticeBox n P, f x‖ / P^n)^2 ≤
        ((10 : ℝ)^n * ((n : ℝ)+1) * K) * H ^ (-(((s u).val - s₀ : ℕ) : ℝ)) *
          (‖∑ x ∈ latticeBox n P, f (x + m • u) * conj (f x)‖ / P^n) := by
  let D := differencingDirections n H
  let R (u : Fin n → ℤ) : ℝ := ‖∑ x ∈ latticeBox n P, f (x + m • u) * conj (f x)‖ / P^n
  have hD : D.Nonempty := by
    have hz : (0 : Fin n → ℤ) ∈ differencingShifts n H := by
      apply mem_differencingShifts.mpr
      intro i
      simp [hH]
    exact ⟨0, Finset.mem_image.mpr ⟨(0,0), Finset.mem_product.mpr ⟨hz,hz⟩, sub_zero _⟩⟩
  have hR (u : Fin n → ℤ) (_ : u ∈ D) : 0 ≤ R u := by
    dsimp [R]
    positivity
  obtain ⟨u, hu, hbnd⟩ := exists_direction_of_class_bounds D hD s R
    (fun j => K * H ^ ((n : ℝ) - ((j.val - s₀ : ℕ) : ℝ))) hR hcount
  refine ⟨u, hu, (vanDerCorput_normalized_latticeBox hP hH hm hmH f hf).trans ?_⟩
  refine (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans_eq ?_
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one, Real.rpow_sub hH, Real.rpow_natCast,
    Real.rpow_neg hH.le]
  change _ = ((10 : ℝ)^n * ((n : ℝ)+1) * K) * (H ^ (((s u).val - s₀ : ℕ) : ℝ))⁻¹ * R u
  field_simp

end

end Birch
