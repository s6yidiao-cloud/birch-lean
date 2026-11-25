import Birch.FermatSpectrumRecovery
import Birch.HypersurfaceSpectralData

open AlgebraicGeometry CategoryTheory

namespace Birch

/-- The middle rank from the Fermat comparison and the lower Frobenius
spectrum from the ambient projective space determine the inputs for counting
points on a smooth hypersurface. Poincaré duality supplies the upper grades. -/
theorem tateSpectrum_and_middleRank_of_fermat_and_ambient {p d N : ℕ} [Fact p.Prime]
    (hd : 0 < d) (A F P : ℕ → Multiset ℂ)
    (hFweight : ∀ i ≤ 2 * N, ∀ z ∈ F i, ‖z‖ = Real.sqrt ((p : ℝ)^i))
    (hFdual : ∀ i ≤ 2 * N, F (2 * N - i) = (F i).map ((p : ℂ)^N / ·))
    (hFtrace : ∀ (E : Type) [Field E] [Algebra (ZMod p) E] [FiniteDimensional (ZMod p) E],
      let X := Over.mk (projectiveHypersurfaceToField (isHomogeneous_fermatPolynomial (ZMod p) N d))
      (Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) E))) ⟶ X) : ℂ) =
        ∑ i ∈ Finset.Iic (2 * N), (-1 : ℂ)^i * ((F i).map (· ^ Module.finrank (ZMod p) E)).sum)
    (hPzero : P 0 = {1})
    (hPweight : ∀ i ≤ 2 * (N + 1), ∀ z ∈ P i, ‖z‖ = Real.sqrt ((p : ℝ)^i))
    (hPtrace : ∀ (E : Type) [Field E] [Algebra (ZMod p) E] [FiniteDimensional (ZMod p) E],
      let X := Over.mk (projectivePolynomialSpaceToField (Fin (N + 2)) (ZMod p))
      (Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) E))) ⟶ X) : ℂ) =
        ∑ i ∈ Finset.Iic (2 * (N + 1)), (-1 : ℂ)^i * ((P i).map (· ^ Module.finrank (ZMod p) E)).sum)
    (hdual : ∀ i ≤ 2 * N, A (2 * N - i) = (A i).map ((p : ℂ)^N / ·))
    (hlower : ∀ i < N, A i = P i)
    (hrank : (A N).card = (F N).card) :
    (∀ i ≤ 2 * N, i ≠ N → A i = projectiveTateSpectrum p i) ∧
      (A N).card ≤ (d - 1)^(N + 2) + 1 := by
  have hTate := tateSpectrum_of_projectivePolynomialSpace_trace (N := N + 1)
    P hPzero hPweight hPtrace
  obtain ⟨_, hmiddle⟩ := tateSpectrum_and_middleRank_of_fermat_trace hd F hFweight hFdual hFtrace
  refine ⟨eq_projectiveTateSpectrum_of_lower_and_duality (Fact.out : p.Prime).pos A ?_ hdual,
    hrank.trans_le hmiddle⟩
  exact fun i hi => (hlower i hi).trans (hTate i (by omega))

end Birch
