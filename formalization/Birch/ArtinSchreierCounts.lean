import Birch.CompleteSums
import Mathlib.FieldTheory.Finite.Trace

/-!
# Artin–Schreier point counts and prime-field character sums

The translates of the Artin–Schreier equation separate the trace fibers. The
result identifies the finite point counts from which the additive-character
component can be recovered over every finite extension of the prime field.
-/

open scoped BigOperators

namespace Birch

noncomputable section

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Finite K] [Algebra (ZMod p) K]

private abbrev artinSchreierLinear (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod p) K] : K →ₗ[ZMod p] K :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K).toLinearMap - LinearMap.id

private theorem artinSchreier_apply (x : K) : artinSchreierLinear p K x = x^p - x := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  change FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K x - x = _
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]

private theorem artinSchreier_ker :
    LinearMap.ker (artinSchreierLinear p K) =
      LinearMap.range (Algebra.linearMap (ZMod p) K) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hsub : (algebraMap (ZMod p) K).fieldRange = (⊥ : Subfield K) := by
    rw [← ZMod.fieldRange_castHom_eq_bot p]
    congr 1
    ext x
    exact Subsingleton.elim (algebraMap (ZMod p) K) (ZMod.castHom dvd_rfl K) ▸ rfl
  ext x
  rw [LinearMap.mem_ker, artinSchreier_apply, sub_eq_zero,
    ← Subfield.mem_bot_iff_pow_eq_self K p, ← hsub]
  rfl

private theorem artinSchreier_range :
    LinearMap.range (artinSchreierLinear p K) = LinearMap.ker (Algebra.trace (ZMod p) K) := by
  let δ := artinSchreierLinear p K
  let Tr := Algebra.trace (ZMod p) K
  have hδTr (y : K) : Tr (δ y) = 0 := by
    change Tr (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K y - y) = 0
    rw [map_sub, sub_eq_zero]
    exact Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K) y
  have hle : δ.range ≤ Tr.ker := by
    rintro x ⟨y,rfl⟩
    exact LinearMap.mem_ker.mpr (hδTr y)
  have hdker : Module.finrank (ZMod p) δ.ker = 1 := by
    rw [show δ.ker = _ from artinSchreier_ker, LinearMap.finrank_range_of_inj
      (algebraMap (ZMod p) K).injective, Module.finrank_self]
  have hTrRange : Module.finrank (ZMod p) Tr.range = 1 := by
    rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective (ZMod p) K),
      finrank_top, Module.finrank_self]
  apply Submodule.eq_of_le_of_finrank_le hle
  have hd := δ.finrank_range_add_finrank_ker
  have htr := Tr.finrank_range_add_finrank_ker
  omega

/-- A trace-zero fiber of the Artin–Schreier map has exactly p elements.
A fiber with nonzero trace is empty. -/
theorem card_artinSchreier_fiber (b : K) :
    Nat.card {y : K // y^p-y = b} = if Algebra.trace (ZMod p) K b = 0 then p else 0 := by
  classical
  let δ := artinSchreierLinear p K
  by_cases hTr : Algebra.trace (ZMod p) K b = 0
  · rw [ite_eq_left hTr]
    have hb : b ∈ δ.range := by
      rw [show δ.range = _ from artinSchreier_range (p := p) (K := K)]
      exact LinearMap.mem_ker.mpr hTr
    obtain ⟨z, hz⟩ := hb
    let e : {y : K // y^p-y = b} ≃ δ.ker :=
      { toFun := fun y => ⟨y.val - z, by
          apply LinearMap.mem_ker.mpr
          rw [map_sub, artinSchreier_apply, y.prop, hz, sub_self]⟩
        invFun := fun k => ⟨k.val + z, by
          rw [← artinSchreier_apply, map_add,
            LinearMap.mem_ker.mp k.prop, hz, zero_add]⟩
        left_inv := fun y => Subtype.ext (sub_add_cancel y.val z)
        right_inv := fun k => Subtype.ext (add_sub_cancel_right k.val z) }
    rw [Nat.card_congr e, show δ.ker = _ from artinSchreier_ker]
    exact (Nat.card_congr (LinearEquiv.ofInjective (Algebra.linearMap (ZMod p) K)
      (algebraMap (ZMod p) K).injective).toEquiv.symm).trans (Nat.card_zmod p)
  · rw [ite_eq_right hTr, Nat.card_eq_zero]
    left
    refine ⟨fun ⟨y,hy⟩ => hTr ?_⟩
    rw [← LinearMap.mem_ker, ← artinSchreier_range (p := p)]
    exact ⟨y, (artinSchreier_apply y).trans hy⟩

/-- The affine point count for a translate of an Artin–Schreier equation. -/
def artinSchreierTwistCount {α : Type*} (g : α → K) (h : K) : ℕ :=
  Nat.card {xy : α × K // (xy.2)^p - xy.2 = g xy.1 - h}

omit [Fact p.Prime] [Algebra (ZMod p) K] in
private theorem artinSchreierTwistCount_eq_sum {α : Type*} [Fintype α]
    (g : α → K) (h : K) :
    artinSchreierTwistCount (p := p) g h = ∑ x, Nat.card {y : K // y^p-y = g x-h} := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let e : {xy : α × K // xy.2^p - xy.2 = g xy.1 - h} ≃
      Σ x : α, {y : K // y^p-y = g x-h} :=
    { toFun := fun xy => ⟨xy.val.1, xy.val.2, xy.prop⟩
      invFun := fun xy => ⟨(xy.1,xy.2.val), xy.2.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [artinSchreierTwistCount, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Nat.card_eq_fintype_card]

/-- Recover the additive-character sum as a linear combination of affine point
counts. The lifts can come from any right inverse of the trace, which is
surjective even when the extension degree is divisible by p. -/
theorem character_sum_eq_artinSchreier_counts [NeZero p] {α : Type*} [Fintype α]
    (g : α → K) (a : ZMod p) (lift : ZMod p → K)
    (hlift : ∀ t, Algebra.trace (ZMod p) K (lift t) = t) :
    (∑ x, ZMod.stdAddChar (a * Algebra.trace (ZMod p) K (g x))) =
      (p : ℂ)⁻¹ * ∑ t : ZMod p, (artinSchreierTwistCount (p := p) g (lift t) : ℂ) *
        ZMod.stdAddChar (a * t) := by
  classical
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp_rw [artinSchreierTwistCount_eq_sum, Nat.cast_sum, card_artinSchreier_fiber,
    map_sub, hlift, sub_eq_zero, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (Algebra.trace (ZMod p) K (g x))]
  · simp [hp]
  · intro t _ ht
    simp [Ne.symm ht]
  · simp

/-- At conductor one the trace lifts are the prime-field elements themselves. -/
theorem completeSum_eq_artinSchreier_counts [NeZero p] {n : ℕ}
    (F : MvPolynomial (Fin n) ℤ) (a : ZMod p) :
    completeSum F p a = ((p : ℂ) ^ (n+1))⁻¹ * ∑ t : ZMod p,
      (artinSchreierTwistCount (p := p) (residueEval F p) t : ℂ) * ZMod.stdAddChar (a * t) := by
  have hsum := character_sum_eq_artinSchreier_counts (p := p) (K := ZMod p)
    (residueEval F p) a id (by simp)
  simp only [Algebra.trace_self_apply, id_eq] at hsum
  rw [completeSum, hsum, pow_succ, mul_inv_rev]
  ring

end
end Birch
