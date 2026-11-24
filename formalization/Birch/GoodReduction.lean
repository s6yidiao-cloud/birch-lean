import Birch.Geometry
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Data.ZMod.Basic

/-!
# Good reduction of the gradient

The homogeneous Euler identity makes the geometric gradient zero locus consist
only of the origin. The Nullstellensatz over the rational coefficient field gives
powers of the coordinate functions in the rational gradient ideal. Clearing
denominators once gives identities valid in every remaining characteristic.
-/

open MvPolynomial Set

namespace Birch

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Integer certificates for the absence of nonzero common gradient zeros. -/
theorem ProjectivelySmooth.gradient_certificates {n d : ℕ} {F : IntForm n}
    (hs : ProjectivelySmooth F) (hF : F.IsHomogeneous d) (hd : 0 < d) :
    ∀ i : Fin n, ∃ (a : ℤ) (k : ℕ), 0 < a ∧
      C a * (X i : IntForm n) ^ k ∈ Ideal.span (range fun j : Fin n ↦ pderiv j F) := by
  classical
  let J : Ideal (IntForm n) := Ideal.span (range fun j : Fin n ↦ pderiv j F)
  let JQ := J.map (algebraMap (IntForm n) (MvPolynomial (Fin n) ℚ))
  let K := AlgebraicClosure ℚ
  have hEuler (x : Fin n → K) :
      (∑ i, x i * evalForm (pderiv i F) x) = (d : K) * evalForm F x := by
    have H := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom K) x) hF.sum_X_mul_pderiv
    simpa [evalForm, nsmul_eq_mul] using H
  have hgeom : zeroLocus (AlgebraicClosure ℚ) JQ ⊆
      ({0} : Set (Fin n → AlgebraicClosure ℚ)) := by
    intro x hx
    have hgrad (j : Fin n) : evalForm (pderiv j F) x = 0 := by
      have hmem : algebraMap (IntForm n) (MvPolynomial (Fin n) ℚ) (pderiv j F) ∈ JQ :=
        Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
      have he := hx _ hmem
      rw [MvPolynomial.algebraMap_def,
        show algebraMap ℤ ℚ = Int.castRingHom ℚ from Subsingleton.elim _ _,
        eval_rational_coefficients] at he
      exact he
    have hzero : evalForm F x = 0 := by
      have he := hEuler x
      simp only [hgrad, mul_zero, Finset.sum_const_zero] at he
      have hdn : (d : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hd.ne'
      exact (mul_eq_zero.mp he.symm).resolve_left hdn
    by_contra! hx₀
    obtain ⟨j, hj⟩ := hs x hx₀ hzero
    exact hj (hgrad j)
  intro i
  have hX : (X i : MvPolynomial (Fin n) ℚ) ∈ JQ.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure ℚ)]
    intro x hx
    have he : x = 0 := hgeom hx
    simp [he]
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hX
  have hk' : algebraMap (IntForm n) (MvPolynomial (Fin n) ℚ) (X i ^ k) ∈ JQ := by
    simpa only [MvPolynomial.algebraMap_def, map_pow, map_X] using hk
  let M : Submonoid (IntForm n) :=
    (Submonoid.pos ℤ).map (C (σ := Fin n))
  obtain ⟨m, hm, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M (MvPolynomial (Fin n) ℚ) J _).mp hk'
  obtain ⟨a, ha, rfl⟩ := hm
  exact ⟨a, k, ha, hmem⟩

/-- In every prime characteristic beyond a fixed bound, the gradient vanishes only
at the origin over every field of that characteristic. -/
theorem ProjectivelySmooth.eventually_goodReduction {n d : ℕ} {F : IntForm n}
    (hs : ProjectivelySmooth F) (hF : F.IsHomogeneous d) (hd : 2 ≤ d) :
    ∃ B : ℕ, ∀ (p : ℕ), B < p → ∀ (K : Type*) [Field K] [CharP K p],
      ∀ x : Fin n → K, (∀ j, evalForm (pderiv j F) x = 0) ↔ x = 0 := by
  classical
  choose a k ha hcert using hs.gradient_certificates hF (by omega)
  let B : ℕ := Finset.univ.sup fun i ↦ (a i).natAbs
  refine ⟨B, fun p hp K _ _ x ↦ ⟨?_, ?_⟩⟩
  · intro hgrad
    ext i
    let ev : IntForm n →+* K := eval₂Hom (Int.castRingHom K) x
    have hspan : Ideal.span (range fun j : Fin n ↦ pderiv j F) ≤ RingHom.ker ev := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgrad j
    have he : (a i : K) * x i ^ k i = 0 := by
      have H : ev (C (a i) * X i ^ k i) = 0 := hspan (hcert i)
      simp only [ev, map_mul, map_pow, coe_eval₂Hom, eval₂_C, eval₂_X] at H
      exact H
    have haK : (a i : K) ≠ 0 := by
      intro h
      have hdvd := (CharP.intCast_eq_zero_iff K p (a i)).mp h
      have hbound : (a i).natAbs ≤ B := Finset.le_sup (f := fun j : Fin n ↦ (a j).natAbs) (Finset.mem_univ i)
      have hpos : 0 < (a i).natAbs := Int.natAbs_pos.mpr (ha i).ne'
      have hp_le : p ≤ (a i).natAbs := Nat.le_of_dvd hpos (by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hdvd)
      omega
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp he).resolve_left haK)
  · rintro rfl j
    have h := evalForm_scale (R := K) (F := pderiv j F) hF.pderiv 0 (0 : Fin n → K)
    have h0 : (fun i : Fin n ↦ (0 : K) * (0 : Fin n → K) i) = 0 := by
      ext i
      simp
    rwa [h0, zero_pow (show d - 1 ≠ 0 by omega), zero_mul] at h

end
end Birch
