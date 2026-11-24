import Birch.CompletionConditional
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial

/-! # Gradient dimensions as finite indices -/

open MvPolynomial

namespace Birch

/-- A homogeneous gradient locus in affine `n`-space has an integer dimension
between `0` and `n`. The lower bound uses the critical point at the origin. -/
theorem exists_primeGradientDimension {n d p : ℕ} (hp : p.Prime) {G : IntForm n}
    (hG : G.IsHomogeneous d) (hd : 2 ≤ d) :
    ∃ s : Fin (n+1), PrimeGradientDimension p hp G s.val := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let R := MvPolynomial (Fin n) K
  let J : Ideal R := Ideal.span
    (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv j G))
  let e : R →ₐ[K] K := aeval (0 : Fin n → K)
  have hzero (j : Fin n) : evalForm (pderiv j G) (0 : Fin n → K) = 0 := by
    have h := evalForm_scale (F := pderiv j G) hG.pderiv (0 : K) (0 : Fin n → K)
    have he : (fun _ : Fin n => (0 : K)) = 0 := rfl
    simpa [zero_pow (show d-1 ≠ 0 by omega), he] using h
  have hJ : J ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change aeval (0 : Fin n → K) (MvPolynomial.map (Int.castRingHom K) (pderiv j G)) = 0
    rw [aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]
    exact hzero j
  have hproper : J ≠ ⊤ := by
    intro h
    have he : (1 : R) ∈ RingHom.ker e.toRingHom := hJ (by simp [h])
    simp at he
  letI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hmin : 0 ≤ ringKrullDim (R ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  have hmax : ringKrullDim (R ⧸ J) ≤ (n : ℕ∞) := by
    refine (ringKrullDim_le_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).trans_eq ?_
    change ringKrullDim (MvPolynomial (Fin n) K) = _
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  change ∃ s : Fin (n+1), ringKrullDim (R ⧸ J) = (s.val : ℕ∞)
  generalize hdim : ringKrullDim (R ⧸ J) = N at hmin hmax ⊢
  cases N using WithBot.recBotCoe with
  | bot => exact (not_le_of_gt (WithBot.bot_lt_coe 0) hmin).elim
  | coe a =>
    have ha := WithBot.coe_le_coe.mp hmax
    have hfin : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) ha
    have he : (a.toNat : ℕ∞) = a := ENat.coe_toNat hfin
    have hle : a.toNat ≤ n := by exact_mod_cast (he.symm ▸ ha)
    exact ⟨⟨a.toNat, Nat.lt_succ_of_le hle⟩, congrArg WithBot.some he.symm⟩

end Birch
