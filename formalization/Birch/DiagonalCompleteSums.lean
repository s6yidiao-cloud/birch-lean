module

public import Birch.CompleteSums
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Complete sums for diagonal homogeneous polynomials

The one-dimensional bound expands the power-map range indicator in characters
of the quotient of the group of units. The trivial character cancels the
term at zero, and each remaining Gauss sum has square-root size.
-/

open scoped BigOperators

namespace Birch

noncomputable section

private theorem norm_gaussSum_eq_sqrt_card {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (AddChar.IsPrimitive.of_ne_one hψ)
  rw [← star_gaussSum_eq, Complex.star_def, Complex.mul_conj'] at h
  have hs : ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow, Complex.ofReal_natCast] using h
  exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    (hs.trans (Real.sq_sqrt (Nat.cast_nonneg _)).symm)

private theorem sum_field_eq_zero_add_units {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (f : F → ℂ) :
    ∑ x : F, f x = f 0 + ∑ u : Fˣ, f u := by
  classical
  rw [Fintype.sum_eq_add_sum_compl 0]
  congr 1
  calc
    _ = ∑ x : {x : F // x ≠ 0}, f x := by
      apply Finset.sum_subtype
      simp
    _ = _ := Fintype.sum_equiv unitsEquivNeZero.symm _ _ (fun x => by
      rw [← unitsEquivNeZero_apply_coe, Equiv.apply_symm_apply])

private theorem sum_hom_eq_weighted {G : Type*} [Group G] [Fintype G]
    (P : G →* G) (f w : G → ℂ)
    (hon : ∀ t ∈ P.range, w t = (Nat.card P.ker : ℂ))
    (hoff : ∀ t ∉ P.range, w t = 0) :
    (∑ x : G, f (P x)) = ∑ t : G, w t * f t := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ P (fun x => f (P x))]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t ∈ P.range
  · rw [hon t ht]
    have hsum : (∑ x ∈ Finset.univ.filter (fun x => P x = t), f (P x)) =
        ∑ _x ∈ Finset.univ.filter (fun x => P x = t), f t := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    have hc : (Finset.univ.filter fun x => P x = t).card = Nat.card P.ker := by
      obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp ht
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr (P.fiberEquivKer z)
    rw [hsum, Finset.sum_const, nsmul_eq_mul, hc]
  · rw [hoff t ht, zero_mul]
    apply Finset.sum_eq_zero
    intro x hx
    exact (ht (MonoidHom.mem_range.mpr ⟨x, (Finset.mem_filter.mp hx).2⟩)).elim

/-- A nontrivial additive character summed over a power map on a finite field. -/
theorem norm_sum_addChar_pow_le {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (hd : 0 < d) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    ‖∑ x : F, ψ (x ^ d)‖ ≤ ((d : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
  classical
  let P : Fˣ →* Fˣ := powMonoidHom d
  let Q := Fˣ ⧸ P.range
  let g := Nat.card Q
  have hg₀ : 0 < g := Nat.card_pos
  let : NeZero g := ⟨hg₀.ne'⟩
  have hg₁ : g ≤ d := by
    change Nat.card (Fˣ ⧸ (powMonoidHom d : Fˣ →* Fˣ).range) ≤ d
    rw [← Subgroup.index_eq_card, IsCyclic.index_powMonoidHom_range]
    exact Nat.gcd_le_right _ hd
  have hQ : IsCyclic Q := isCyclic_of_surjective (QuotientGroup.mk' P.range)
    (QuotientGroup.mk'_surjective P.range)
  let E : Multiplicative (ZMod g) ≃* Q := zmodCyclicMulEquiv hQ
  let q : Fˣ →* Multiplicative (ZMod g) := E.symm.toMonoidHom.comp (QuotientGroup.mk' P.range)
  have hq : Function.Surjective q := E.symm.surjective.comp (QuotientGroup.mk'_surjective P.range)
  let χ (j : ZMod g) : MulChar F ℂ :=
    MulChar.ofUnitHom (((ZMod.stdAddChar.mulShift j).toMonoidHom.toHomUnits).comp q)
  have hχ (j : ZMod g) (u : Fˣ) :
      χ j u = ZMod.stdAddChar (j * (q u).toAdd) := by
    simp only [χ, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits,
      AddChar.toMonoidHom_apply, AddChar.mulShift_apply]
  have hχzero : χ 0 = 1 := by
    apply MulChar.ext
    intro u
    rw [hχ, zero_mul, AddChar.map_zero_eq_one, MulChar.one_apply u.isUnit]
  have hχne (j : ZMod g) (hj : j ≠ 0) : χ j ≠ 1 := by
    intro he
    obtain ⟨u, hu⟩ := hq (Multiplicative.ofAdd (1 : ZMod g))
    apply hj
    apply ZMod.injective_stdAddChar
    have hh := DFunLike.congr_fun he (u : F)
    rw [hχ, hu, toAdd_ofAdd, mul_one, MulChar.one_apply u.isUnit,
      ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := g))] at hh
    exact hh
  have hzero (u : Fˣ) : (q u).toAdd = 0 ↔ u ∈ P.range := by
    change q u = 1 ↔ _
    rw [show q u = 1 ↔ (QuotientGroup.mk' P.range) u = 1 from
      ⟨fun h => E.symm.injective (h.trans E.symm.map_one.symm),
        fun h => (congrArg E.symm h).trans E.symm.map_one⟩]
    exact QuotientGroup.eq_one_iff u
  have horth (u : Fˣ) : (∑ j : ZMod g, χ j u) =
      if u ∈ P.range then (g : ℂ) else 0 := by
    simp_rw [hχ]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar g)]
    by_cases hu : u ∈ P.range
    · simp only [ite_eq_left hu, ite_eq_left ((hzero u).mpr hu), ZMod.card]
    · simp only [ite_eq_right hu, ite_eq_right (hu ∘ (hzero u).mp), Nat.cast_zero]
  have hker : g = Nat.card P.ker := by
    change Nat.card (Fˣ ⧸ (powMonoidHom d : Fˣ →* Fˣ).range) =
      Nat.card (powMonoidHom d : Fˣ →* Fˣ).ker
    rw [← Subgroup.index_eq_card, IsCyclic.index_powMonoidHom_range,
      IsCyclic.card_powMonoidHom_ker]
  have hdecomp : (∑ x : F, ψ (x ^ d)) = 1 + ∑ j : ZMod g, gaussSum (χ j) ψ := by
    rw [sum_field_eq_zero_add_units, zero_pow hd.ne', AddChar.map_zero_eq_one]
    congr 1
    calc
      _ = ∑ x : Fˣ, ψ (↑(P x) : F) := by simp only [P, powMonoidHom_apply,
        Units.val_pow_eq_pow_val]
      _ = ∑ u : Fˣ, (∑ j : ZMod g, χ j u) * ψ u := by
        refine sum_hom_eq_weighted P (fun u : Fˣ => ψ u)
          (fun u : Fˣ => ∑ j : ZMod g, χ j u) ?_ ?_
        · intro t ht
          rw [horth, ite_eq_left ht, hker]
        · intro t ht
          rw [horth, ite_eq_right ht]
      _ = ∑ j : ZMod g, gaussSum (χ j) ψ := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [gaussSum, sum_field_eq_zero_add_units (fun u : F => χ j u * ψ u)]
        simp only [MulChar.map_zero, zero_mul, zero_add]
  rw [hdecomp, Fintype.sum_eq_add_sum_compl (0 : ZMod g), hχzero, gaussSum_one_left hψ]
  have hc : (({0} : Finset (ZMod g))ᶜ.card : ℝ) ≤ (d : ℝ) - 1 := by
    rw [Finset.card_compl, Finset.card_singleton, ZMod.card, Nat.cast_sub (Nat.one_le_of_lt hg₀),
      Nat.cast_one]
    exact sub_le_sub_right (Nat.cast_le.mpr hg₁) 1
  calc
    _ = ‖∑ j ∈ ({0} : Finset (ZMod g))ᶜ, gaussSum (χ j) ψ‖ := by
      rw [← add_assoc, add_neg_cancel, zero_add]
    _ ≤ ∑ j ∈ ({0} : Finset (ZMod g))ᶜ, ‖gaussSum (χ j) ψ‖ := norm_sum_le _ _
    _ = (({0} : Finset (ZMod g))ᶜ.card : ℝ) * Real.sqrt (Fintype.card F : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro j hj
      exact norm_gaussSum_eq_sqrt_card (hχne j (by simpa using hj)) hψ
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)

private theorem addChar_finset_sum {A ι : Type*} [AddCommMonoid A]
    (ψ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

/-- The diagonal sum factors into one-dimensional complete sums. -/
theorem diagonal_addChar_sum_eq_prod {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) {l : ℕ} (c : Fin l → F) (d : ℕ) :
    (∑ x : Fin l → F, ψ (∑ i, c i * x i ^ d)) =
      ∏ i, ∑ t : F, ψ (c i * t ^ d) := by
  simp_rw [addChar_finset_sum]
  exact (Fintype.prod_sum (κ := fun _ : Fin l => F) (fun i t => ψ (c i * t ^ d))).symm

/-- The additive complete-sum bound for a diagonal form with nonzero
coefficients. -/
theorem norm_sum_stdAddChar_diagonal_le {p l d : ℕ} [Fact p.Prime] [NeZero p]
    (hd : 0 < d) (c : Fin l → ZMod p) (hc : ∀ i, c i ≠ 0) :
    ‖∑ x : Fin l → ZMod p, ZMod.stdAddChar (∑ i, c i * x i^d)‖ ≤
      ((d : ℝ) - 1) ^ l * (p : ℝ) ^ ((l : ℝ) / 2) := by
  rw [diagonal_addChar_sum_eq_prod, norm_prod]
  have hbound (i : Fin l) : ‖∑ x : ZMod p, ZMod.stdAddChar (c i * x ^ d)‖ ≤
      ((d : ℝ) - 1) * Real.sqrt (p : ℝ) := by
    let ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar.mulShift (c i)
    have hψ : ψ ≠ 1 := ZMod.isPrimitive_stdAddChar p (hc i)
    simpa only [ψ, AddChar.mulShift_apply, ZMod.card] using norm_sum_addChar_pow_le hd ψ hψ
  calc
    _ ≤ ∏ _i : Fin l, ((d : ℝ) - 1) * Real.sqrt (p : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hbound i)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      rw [show (1 / 2 : ℝ) * (l : ℝ) = (l : ℝ) / 2 by ring]

/-- The prime-conductor estimate for an integral diagonal form, with the
normalization used in the circle method. -/
theorem norm_completeSum_diagonal {p l d : ℕ} [Fact p.Prime] [NeZero p]
    (hd : 0 < d) (c : Fin l → ℤ) (hc : ∀ i, (c i : ZMod p) ≠ 0)
    (a : ZMod p) (ha : a ≠ 0) :
    ‖completeSum (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i ^ d) p a‖ ≤
      ((d : ℝ) - 1) ^ l * (p : ℝ) ^ (-(l : ℝ) / 2) := by
  let b (i : Fin l) := a * (c i : ZMod p)
  have hb (i : Fin l) : b i ≠ 0 := mul_ne_zero ha (hc i)
  have heval (x : Fin l → ZMod p) :
      a * residueEval (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i ^ d) p x =
        ∑ i, b i * x i ^ d := by
    simp only [residueEval, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X_pow, Int.coe_castRingHom, Finset.mul_sum,
      b, mul_assoc]
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  unfold completeSum
  simp only [heval, ← div_eq_inv_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (((d : ℝ) - 1) ^ l * (p : ℝ) ^ ((l : ℝ) / 2)) / (p : ℝ) ^ l :=
      div_le_div_of_nonneg_right (norm_sum_stdAddChar_diagonal_le hd b hb)
        (pow_nonneg hp.le _)
    _ = _ := by
      rw [mul_div_assoc, ← Real.rpow_natCast p l, ← Real.rpow_sub hp]
      congr 2
      ring

end
end Birch
