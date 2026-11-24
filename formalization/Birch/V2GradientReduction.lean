import Birch.ConeDimensionTest
import Birch.CutPolynomialSystem
import Birch.GradientDimensionIndex
import Birch.UniformSystemCertificate
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Good reduction of the gradient dimension

Linear sections and an integral Macaulay minor transfer a dimension bound
from characteristic zero to all but finitely many prime characteristics.
-/

open MvPolynomial

namespace Birch

noncomputable section

private theorem exists_integral_linearCuts_macaulayMinor
    {n m k e : ℕ} (i₀ : Fin n) (he : 0 < e) (f : Fin m → IntForm n)
    (hf : ∀ j, (f j).IsHomogeneous e)
    (hdim : ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure ℚ) ⧸
      Ideal.span (Set.range fun j => MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
        (f j))) ≤ (k : WithBot ℕ∞)) :
    ∃ D > e, ∃ a : Fin k → Fin n → ℤ,
      ∃ sel : DegreeMonomial n D → Fin (m + k) × DegreeMonomial n (D - e),
        ((systemMacaulayMatrix (cutPolynomialSystem f 1 a e) e D).submatrix id sel).det ≠ 0 := by
  classical
  let K := AlgebraicClosure ℚ
  let fK (j : Fin m) := MvPolynomial.map (Int.castRingHom K) (f j)
  have hfK (j : Fin m) : (fK j).IsHomogeneous e := (hf j).map _
  obtain ⟨a, ha⟩ := (homogeneousSystem_dim_le_iff_linear_cuts i₀ fK he hfK).mp hdim
  obtain ⟨D, hD, hcert⟩ := exists_uniform_system_macaulay_degree n (m + k) e
  obtain ⟨sel, hsel⟩ := (hcert (cutPolynomialSystem fK 1 a e)
    (cutPolynomialSystem_isHomogeneous fK 1 a hfK)).mp (fun x hx => by
      obtain ⟨hf₀, ha₀⟩ := (eval_cutPolynomialSystem_eq_zero_iff fK one_ne_zero a he x).mp hx
      exact ha x hf₀ ha₀)
  let R := MvPolynomial (Fin k × Fin n) ℤ
  let f₀ (j : Fin m) := MvPolynomial.map (C : ℤ →+* R) (f j)
  let a₀ (j : Fin k) (i : Fin n) : R := X (j, i)
  let T : R := ((systemMacaulayMatrix (cutPolynomialSystem f₀ 1 a₀ e) e D).submatrix id sel).det
  have heval {L : Type} [CommRing L] (φ : ℤ →+* L) (z : Fin k × Fin n → L) :
      T.eval₂ φ z =
      ((systemMacaulayMatrix (cutPolynomialSystem (fun j => MvPolynomial.map φ (f j))
        1 (fun j i => z (j, i)) e) e D).submatrix id sel).det := by
    change eval₂Hom φ z T = _
    unfold T
    rw [map_cutPolynomialSystem_macaulayMinor]
    have hf₀ (j : Fin m) : MvPolynomial.map (eval₂Hom φ z) (f₀ j) = MvPolynomial.map φ (f j) := by
      unfold f₀
      rw [MvPolynomial.map_map]
      have hcomp : (eval₂Hom φ z).comp C = φ := by ext t; simp
      rw [hcomp]
    have ha₀ (j : Fin k) : (eval₂Hom φ z) ∘ a₀ j = fun i => z (j, i) := by
      funext i
      exact eval₂_X _ _ _
    simp only [hf₀, map_one, ha₀]
  have hT : T ≠ 0 := by
    intro hz
    have h := heval (Int.castRingHom K) (fun ji => a ji.1 ji.2)
    rw [hz, eval₂_zero] at h
    exact hsel h.symm
  obtain ⟨z, hz⟩ : ∃ z : Fin k × Fin n → ℤ, T.eval z ≠ 0 := by
    by_contra! h
    apply hT
    apply MvPolynomial.funext
    intro x
    rw [map_zero, h]
  refine ⟨D, hD, fun j i => z (j, i), sel, ?_⟩
  have h := heval (RingHom.id ℤ) z
  rw [eval₂_id] at h
  simp only [MvPolynomial.map_id] at h
  rwa [← h]

/-- An upper bound for the dimension of an integral homogeneous system over
the algebraic closure of the rationals holds over the algebraic closure
of every sufficiently large prime field. -/
theorem exists_goodReduction_homogeneousSystem
    {n m k e : ℕ} (i₀ : Fin n) (he : 0 < e) (f : Fin m → IntForm n)
    (hf : ∀ j, (f j).IsHomogeneous e)
    (hdim : ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure ℚ) ⧸
      Ideal.span (Set.range fun j => MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
        (f j))) ≤ (k : WithBot ℕ∞)) :
    ∃ B : ℕ, ∀ p > B, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      let K := AlgebraicClosure (ZMod p)
      ringKrullDim (MvPolynomial (Fin n) K ⧸
        Ideal.span (Set.range fun j => MvPolynomial.map (Int.castRingHom K)
          (f j))) ≤ (k : WithBot ℕ∞) := by
  classical
  obtain ⟨D, hD, a, sel, hdet⟩ := exists_integral_linearCuts_macaulayMinor i₀ he f hf hdim
  let det : ℤ := ((systemMacaulayMatrix (cutPolynomialSystem f 1 a e) e D).submatrix id sel).det
  refine ⟨det.natAbs, ?_⟩
  intro p hB hp
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let fK (j : Fin m) := MvPolynomial.map (Int.castRingHom K) (f j)
  let aK (j : Fin k) (i : Fin n) : K := (a j i : K)
  have hdetK : (det : K) ≠ 0 := by
    intro h
    have hdvd := (CharP.intCast_eq_zero_iff K p det).mp h
    have hp_le : p ≤ det.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hdet)
      (by exact_mod_cast Int.natAbs_dvd_natAbs.mpr hdvd)
    exact (not_le_of_gt hB) hp_le
  have hspec := map_cutPolynomialSystem_macaulayMinor (Int.castRingHom K) f 1 a e D sel
  simp only [Int.coe_castRingHom, Int.cast_one] at hspec
  change (det : K) =
    ((systemMacaulayMatrix (cutPolynomialSystem fK 1 aK e) e D).submatrix id sel).det at hspec
  have hfK (j : Fin m) : (fK j).IsHomogeneous e := (hf j).map _
  change ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fK)) ≤ _
  apply (homogeneousSystem_dim_le_iff_linear_cuts i₀ fK he hfK).mpr
  refine ⟨aK, fun x hfx hax => ?_⟩
  exact zero_of_system_macaulay_minor (cutPolynomialSystem_isHomogeneous fK 1 aK hfK)
    hD.le (he.trans hD) sel (hspec.symm.trans_ne hdetK) x
    ((eval_cutPolynomialSystem_eq_zero_iff fK one_ne_zero aK he x).mpr ⟨hfx, hax⟩)

/-- The geometric dimension bound supplies the prime-gradient dimension
interface used by completion of the exponential sums. -/
theorem eventualPrimeGradientDimensionLE_of_geometric_dimension_le
    {n d σ : ℕ} {F : IntForm n} (hn : 0 < n) (hF : F.IsHomogeneous d) (hd : 2 ≤ d)
    (hdim : ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure ℚ) ⧸
      Ideal.span (Set.range fun j : Fin n => MvPolynomial.map (Int.castRingHom (AlgebraicClosure ℚ))
        (pderiv j F))) ≤ (σ : WithBot ℕ∞)) :
    EventualPrimeGradientDimensionLE F σ := by
  obtain ⟨B, hB⟩ := exists_goodReduction_homogeneousSystem (⟨0, hn⟩ : Fin n)
    (show 0 < d - 1 by omega) (fun j : Fin n => pderiv j F) (fun _ => hF.pderiv) hdim
  refine ⟨B, ?_⟩
  intro p hp hp'
  letI : Fact p.Prime := ⟨hp'⟩
  obtain ⟨s, hs⟩ := exists_primeGradientDimension hp' hF hd
  refine ⟨s.val, ?_, hs⟩
  have hbound := hB p hp hp'
  have heq := hs
  dsimp [PrimeGradientDimension] at heq
  dsimp only at hbound
  rw [heq] at hbound
  exact_mod_cast hbound

end
end Birch
