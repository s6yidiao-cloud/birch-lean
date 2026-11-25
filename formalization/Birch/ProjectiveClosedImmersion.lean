/-
Adapted from AxiomMath/Stacks, StacksFrontier/AlgebraicGeometry/Limits/ProjGradedSurjection01N0.lean
and StacksFrontier/AlgebraicGeometry/Blowup/ProjBaseChangeGlobal.lean
at revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf.
Released under Apache 2.0 as described in LICENSES/Apache-2.0.txt.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

@[expose] public section

/-! # Closed immersions induced by surjections on projective spectra -/

open CategoryTheory Limits AlgebraicGeometry
open HomogeneousIdeal HomogeneousLocalization Graded CommRingCat

namespace Birch

universe u

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The standard chart of the source of a projective morphism is the
inverse image of the corresponding standard chart of the target. -/
theorem isPullback_proj_awayι_map (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    IsPullback (Spec.map (ofHom (Away.map f s))) (Proj.awayι ℬ (f s) (map_mem f hs) hi)
      (Proj.awayι 𝒜 s hs hi) (Proj.map f hf) :=
  IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map f hf hi s hs) <| by
    rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    exact Proj.map_preimage_basicOpen f hf s

private theorem exists_homogeneous_preimage (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {i : ℕ} {b : B} (hb : b ∈ ℬ i) : ∃ a ∈ 𝒜 i, f a = b := by
  obtain ⟨a, ha⟩ := hf b
  exact ⟨DirectSum.decompose 𝒜 a i, SetLike.coe_mem _, by
    rw [GradedRingHom.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same ℬ hb]⟩

/-- Surjectivity supplies the irrelevant-ideal condition for the global morphism of Proj. -/
theorem proj_irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi x hx
  obtain ⟨a, ha, rfl⟩ := exists_homogeneous_preimage f hf hx
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hi ha)

/-- A surjective graded homomorphism is surjective on the standard chart rings. -/
theorem proj_away_map_surjective_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) : Function.Surjective (Away.map f s) := by
  intro y
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (map_mem f hs) y
  obtain ⟨a, ha, rfl⟩ := exists_homogeneous_preimage f hf hb
  exact ⟨Away.mk 𝒜 hs n a ha, by rw [Away.map_mk]⟩

private theorem closedImmersion_pullback_snd {W X Y Z : Scheme.{u}} {fst : W ⟶ X}
    {snd : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (hs : IsClosedImmersion snd) : IsClosedImmersion (pullback.snd f g) := by
  rw [← h.isoPullback_hom_snd] at hs
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsClosedImmersion)
    h.isoPullback.hom _).mp hs

/-- The morphism of projective spectra induced by a surjective graded ring
homomorphism is a closed immersion. -/
theorem isClosedImmersion_proj_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    IsClosedImmersion (Proj.map f (proj_irrelevant_le_map_of_surjective f hf)) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (Proj.affineOpenCover 𝒜).openCover ?_
  rintro ⟨i, a⟩
  exact closedImmersion_pullback_snd
    (isPullback_proj_awayι_map f (proj_irrelevant_le_map_of_surjective f hf) i.2 (a : A) a.2).flip
    (IsClosedImmersion.spec_of_surjective _ (proj_away_map_surjective_of_surjective f hf a.2))

end Birch
