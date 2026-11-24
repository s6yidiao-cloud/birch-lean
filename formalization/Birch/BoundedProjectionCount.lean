import Birch.GridCounting
import Birch.ConeHyperplane
import Birch.MacaulayFiberCount

/-! # Counting integer directions by bounded linear projections -/

open MvPolynomial
open scoped BigOperators

namespace Birch

/-- Over a finite field the same certificate gives at most `D^n` points
over each of the `#F^k` values of the projection. -/
theorem card_finiteField_subset_le_of_projection
    {F K : Type*} [Field F] [Fintype F] [Field K] {n m k e D : ℕ}
    (φ : F →+* K) (he : 0 < e) (hD : e ≤ D)
    (f : Fin m → MvPolynomial (Fin n) K) (hf : ∀ i, (f i).IsHomogeneous e)
    (b : Fin k → Fin n → F)
    (hmem : ∀ a : Fin n →₀ ℕ, a.degree = D → monomial a (1 : K) ∈
      Ideal.span (Set.range (Fin.append f (fun j => (normalLinearForm (φ ∘ b j)) ^ e))))
    (S : Finset (Fin n → F)) (hzero : ∀ u ∈ S, ∀ i, (f i).eval (φ ∘ u) = 0) :
    S.card ≤ D^n * Fintype.card F^k := by
  classical
  let L (j : Fin k) := normalLinearForm (φ ∘ b j)
  let project (u : Fin n → F) (j : Fin k) : F := ∑ i, b j i * u i
  have hL (j : Fin k) : (L j).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X _ i
  have hproject (u : Fin n → F) (j : Fin k) :
      (L j).eval (φ ∘ u) = φ (project u j) := by
    simp [L, project, normalLinearForm]
  have hfiber (v : Fin k → F) : (S.filter (fun u => project u = v)).card ≤ D^n := by
    let T := S.filter (fun u => project u = v)
    let reduce (u : Fin n → F) : Fin n → K := φ ∘ u
    have hcast : T.card ≤ (T.image reduce).card := by
      apply Finset.card_le_card_of_injOn reduce
      · exact fun u hu => Finset.mem_image_of_mem reduce hu
      · intro u _ v _ huv
        exact funext fun i => φ.injective (congrFun huv i)
    refine hcast.trans (card_le_pow_of_monomial_certificate he hD f L
      (φ ∘ v) hf hL hmem (T.image reduce) ?_)
    intro x hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hu,huv⟩ := Finset.mem_filter.mp hu
    refine ⟨hzero u hu, fun j => ?_⟩
    change (L j).eval (φ ∘ u) = φ (v j)
    rw [hproject, huv]
  calc
    S.card = ∑ v ∈ S.image project, (S.filter (fun u => project u = v)).card :=
      Finset.card_eq_sum_card_image project S
    _ ≤ ∑ _v ∈ S.image project, D^n := Finset.sum_le_sum fun v _ => hfiber v
    _ ≤ D^n * Fintype.card F^k := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_comm (D^n)]
      apply Nat.mul_le_mul_right
      simpa only [Fintype.card_pi_const, Fintype.card_fin] using (S.image project).card_le_univ

/-- A homogeneous certificate bounds fibers of an integral projection by
`D^n`. Bounded coefficients control the size of the projection box. -/
theorem card_differencingDirections_subset_le_of_projection
    {K : Type} [Field K] {n p m k e D B : ℕ} [CharP K p]
    {H : ℝ} (hH : 1 ≤ H) (hpH : 2 * H ≤ p) (he : 0 < e) (hD : e ≤ D)
    (f : Fin m → MvPolynomial (Fin n) K) (hf : ∀ i, (f i).IsHomogeneous e)
    (b : Fin k → Fin n → ℕ) (hb : ∀ j i, b j i ≤ B)
    (hmem : ∀ a : Fin n →₀ ℕ, a.degree = D → monomial a (1 : K) ∈
      Ideal.span (Set.range (Fin.append f (fun j => (normalLinearForm (fun i => (b j i : K))) ^ e))))
    (S : Finset (Fin n → ℤ)) (hS : S ⊆ differencingDirections n H)
    (hzero : ∀ u ∈ S, ∀ i, (f i).eval (fun j => (u j : K)) = 0) :
    (S.card : ℝ) ≤ (D : ℝ)^n * (3 * (n * B + 1))^k * H^k := by
  classical
  let L (j : Fin k) := normalLinearForm (fun i => (b j i : K))
  let reduce (u : Fin n → ℤ) (i : Fin n) : K := u i
  let project (u : Fin n → ℤ) (j : Fin k) : ℤ := ∑ i, (b j i : ℤ) * u i
  let R : ℝ := (n * B + 1) * H
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  have hR : 1 ≤ R := hH.trans (le_mul_of_one_le_left hH₀.le
    (le_add_of_nonneg_left (by positivity)))
  have hl (j : Fin k) : (L j).IsHomogeneous 1 := by
    apply IsHomogeneous.sum
    intro i _
    exact isHomogeneous_C_mul_X _ i
  have hproject (u : Fin n → ℤ) (j : Fin k) :
      (L j).eval (reduce u) = (project u j : K) := by
    simp [L, project, reduce]
  have hbox (u : Fin n → ℤ) (hu : u ∈ S) (j : Fin k) :
      |(project u j : ℝ)| ≤ R := by
    simp only [project, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    calc
      |∑ i, (b j i : ℝ) * (u i : ℝ)| ≤ ∑ i, |(b j i : ℝ) * (u i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (B : ℝ) * H := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul (Nat.cast_le.mpr (hb j i))
          (abs_differencingDirection_lt hH₀ (hS hu) i).le (abs_nonneg _) (Nat.cast_nonneg _)
      _ ≤ R := by
        simp [R, mul_assoc, add_mul, hH₀.le]
  let A := Finset.Icc (-⌊R⌋) ⌊R⌋
  have hA : S.image project ⊆ Fintype.piFinset (fun _ : Fin k => A) := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    refine Fintype.mem_piFinset.mpr fun j => Finset.mem_Icc.mpr ?_
    obtain ⟨h₁,h₂⟩ := abs_le.mp (hbox u hu j)
    exact ⟨neg_le.mp (Int.le_floor.mpr (by exact_mod_cast (neg_le.mp h₁))),
      Int.le_floor.mpr h₂⟩
  have hfiber (v : Fin k → ℤ) : (S.filter (fun u => project u = v)).card ≤ D^n := by
    let T := S.filter (fun u => project u = v)
    have hcast : T.card ≤ (T.image reduce).card := by
      apply Finset.card_le_card_of_injOn reduce
      · intro u hu
        exact Finset.mem_image_of_mem reduce hu
      · apply (injOn_cast_differencingDirections (K := K) hH₀ hpH).mono
        intro u hu
        exact hS (Finset.mem_filter.mp hu).1
    refine hcast.trans (card_le_pow_of_monomial_certificate he hD f L
      (fun j => (v j : K)) hf hl hmem (T.image reduce) ?_)
    intro x hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hu,huv⟩ := Finset.mem_filter.mp hu
    refine ⟨hzero u hu, fun j => ?_⟩
    rw [hproject, huv]
  have hcount : S.card ≤ A.card^k * D^n := by
    calc
      _ = ∑ v ∈ S.image project, (S.filter (fun u => project u = v)).card :=
        Finset.card_eq_sum_card_image project S
      _ ≤ ∑ _v ∈ S.image project, D^n := Finset.sum_le_sum fun v _ => hfiber v
      _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
        apply Nat.mul_le_mul_right
        simpa only [Fintype.card_piFinset_const] using Finset.card_le_card hA
  calc
    (S.card : ℝ) ≤ (A.card : ℝ)^k * (D : ℝ)^n := by exact_mod_cast hcount
    _ ≤ (3 * R)^k * (D : ℝ)^n :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (card_int_coordinateBox_le hR) k)
        (by positivity)
    _ = _ := by rw [show 3 * R = (3 * (n * B + 1)) * H by simp [R, mul_assoc], mul_pow]; ring

end Birch
