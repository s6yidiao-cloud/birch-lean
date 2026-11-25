module

public import Birch.ProjectiveHypersurface
public import Mathlib.AlgebraicGeometry.Properties

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped BigOperators

namespace Birch

noncomputable section

universe u

/-- The zero homogeneous prime is the generic point of a projective
spectrum of a domain whenever a positive-degree element survives. -/
theorem isIntegral_proj_of_isDomain {A α : Type u} [CommRing A] [IsDomain A]
    [SetLike α A] [AddSubgroupClass α A] (𝒜 : ℕ → α) [GradedRing 𝒜]
    {i : ℕ} (hi : 0 < i) {f : A} (hf : f ∈ 𝒜 i) (hf₀ : f ≠ 0) :
    IsIntegral (Proj 𝒜) := by
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := Ideal.isPrime_bot
      not_irrelevant_le := fun h => hf₀ (by
        have hf' : f ∈ HomogeneousIdeal.irrelevant 𝒜 := by
          exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi hf
        exact h hf') }
  have hη : Dense ({η} : Set (ProjectiveSpectrum 𝒜)) := by
    intro x
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η x).mp (by
      rw [← ProjectiveSpectrum.as_ideal_le_as_ideal 𝒜]
      exact bot_le)
  have hirr : IrreducibleSpace (ProjectiveSpectrum 𝒜) :=
    (irreducibleSpace_def _).mpr (by
      change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
      rw [← hη.closure_eq]
      exact (isIrreducible_singleton (x := η)).closure)
  refine (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨hirr, ?_⟩
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  let : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let R := AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal
  have hR : _root_.IsReduced R := by
    apply isReduced_of_injective (algebraMap R (Localization.AtPrime x.asHomogeneousIdeal.toIdeal))
    exact HomogeneousLocalization.val_injective _
  have : _root_.IsReduced (CommRingCat.of R) := hR
  exact isReduced_of_injective (Proj.stalkIso 𝒜 x).hom.hom
    (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv.injective

end
end Birch
