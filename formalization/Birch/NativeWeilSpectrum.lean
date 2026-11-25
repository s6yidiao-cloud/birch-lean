import WeilConjectures.LeanEval.WeilConjectures
import WeilConjectures.ZetaFunction.FinalTheorems

open AlgebraicGeometry CategoryTheory Polynomial

universe u

namespace Birch

/-- The complex Weil spectra, together with their actual ordinary étale
cohomological ranks for every coefficient prime different from the characteristic. -/
theorem nativeWeilSpectrumWithRanks
    (k : Type u) [Field k] [Finite k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (d : ℕ)
    [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension d (X ↘ Spec (.of k))]
    [GeometricallyConnected (X ↘ Spec (.of k))] :
    ∃ (P : Fin (2 * d + 1) → ℤ[X]) (A : ℕ → Multiset ℂ),
      (∀ i : Fin (2 * d + 1), Scheme.IsIntegralFrobeniusFactor k X (i : ℕ) (P i)) ∧
      A = weilInverseRoots P ∧ A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map ((Nat.card k : ℂ)^d / ·)) ∧
      (∀ i ≤ 2 * d, ∀ z ∈ A i, ‖z‖ = Real.sqrt ((Nat.card k : ℝ)^i)) ∧
      (∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k ≠ l)] (i : ℕ), i ≤ 2 * d →
        (A i).card = Module.finrank (PadicAlgCl l)
          ((WeilSheaf.adicConstant k l X).cohomology (i : ℤ)).carrier) ∧
      (∀ n : ℕ, 0 < n →
        ((X ↘ Spec (.of k)).pointCount n : ℂ) =
          ∑ i ∈ Finset.Iic (2 * d), (-1 : ℂ)^i * ((A i).map (· ^ n)).sum) ∧
      ∀ (E : Type u) [Field E] [Algebra k E] [FiniteDimensional k E],
        (Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k E))) ⟶
            Over.mk (X ↘ Spec (.of k))) : ℂ) =
          ∑ i ∈ Finset.Iic (2 * d), (-1 : ℂ)^i *
            ((A i).map (· ^ Module.finrank k E)).sum := by
  obtain ⟨P, hP, hfact, hrank, _⟩ := Scheme.weil_betti k X d
  obtain ⟨_, hfe, hrh⟩ := Scheme.isWeilFactorization_of_isIntegralFrobeniusFactor k X d hP
  obtain ⟨hzero, hspec⟩ := hfact.inverseRoots_spec Nat.card_pos hfe hrh
  refine ⟨P, weilInverseRoots P, hP, rfl, hzero, fun i hi => (hspec i hi).1,
    fun i hi z hz => ((hspec i hi).2.2 z hz).2, ?_, ?_, ?_⟩
  · intro l _ _ i hi
    have hi' : i < 2 * d + 1 := by omega
    rw [weilInverseRoots_of_lt P hi', Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree,
      Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hrank l ⟨i, hi'⟩
  · intro n hn
    exact (X ↘ Spec (.of k)).pointCount_eq_sum_inverseRoots hfact hn.ne'
  · intro E _ _ _
    let f : X ⟶ Spec (.of k) := X ↘ Spec (.of k)
    rw [Nat.card_congr (Scheme.Hom.overHomEquivFieldPoints (Over.mk f) E)]
    change (Nat.card (f.fieldPoints E) : ℂ) = _
    rw [Scheme.Hom.nat_card_fieldPoints_eq_pointCount f E]
    exact f.pointCount_eq_sum_inverseRoots hfact Module.finrank_pos.ne'

end Birch


namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    {i : ℤ} {P Q : Polynomial ℤ}

/-- A Frobenius-equivariant cohomology isomorphism at one auxiliary prime
identifies the integral Frobenius factors. -/
theorem integralFrobeniusFactor_eq_of_cohomologyEquiv
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    (hP : IsIntegralFrobeniusFactor k X i P)
    (hQ : IsIntegralFrobeniusFactor k Y i Q)
    (e : ((WeilSheaf.adicConstant k l X).cohomology i).Equiv
      ((WeilSheaf.adicConstant k l Y).cohomology i)) :
    P = Q := by
  apply Polynomial.map_injective _ (RingHom.injective_int (Int.castRingHom (PadicAlgCl l)))
  rw [hP l, hQ l, frobeniusCharpolyRev_def, frobeniusCharpolyRev_def]
  exact e.localPolynomial_eq

/-- In a grade identified by Frobenius-equivariant cohomology, the complex
Weil multisets agree, including multiplicities. -/
theorem weilInverseRoots_eq_of_cohomologyEquiv {dX dY i : ℕ}
    {PX : Fin (2 * dX + 1) → Polynomial ℤ}
    {PY : Fin (2 * dY + 1) → Polynomial ℤ}
    (hiX : i ≤ 2 * dX) (hiY : i ≤ 2 * dY)
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    (hX : ∀ j : Fin (2 * dX + 1), IsIntegralFrobeniusFactor k X (j : ℕ) (PX j))
    (hY : ∀ j : Fin (2 * dY + 1), IsIntegralFrobeniusFactor k Y (j : ℕ) (PY j))
    (e : ((WeilSheaf.adicConstant k l X).cohomology i).Equiv
      ((WeilSheaf.adicConstant k l Y).cohomology i)) :
    weilInverseRoots PX i = weilInverseRoots PY i := by
  have hiX' : i < 2 * dX + 1 := Nat.lt_succ_of_le hiX
  have hiY' : i < 2 * dY + 1 := Nat.lt_succ_of_le hiY
  rw [weilInverseRoots_of_lt _ hiX', weilInverseRoots_of_lt _ hiY',
    integralFrobeniusFactor_eq_of_cohomologyEquiv (hX ⟨i, hiX'⟩) (hY ⟨i, hiY'⟩) e]

end AlgebraicGeometry.Scheme
