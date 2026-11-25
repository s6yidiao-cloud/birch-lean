module

public import Birch.ProjectiveHypersurfaceRenaming

@[expose] public section

/-! # Coordinate changes on affine projective charts -/

open MvPolynomial HomogeneousLocalization
open scoped Graded

set_option backward.isDefEq.respectTransparency false

namespace Birch

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

def standardChartRingEquivAt {τ ℓ : Type u} [CommRing ℓ]
    {P : MvPolynomial (Option τ) ℓ} (hP : P.IsHomogeneous d)
    {s : HypersurfaceRing P} (hs : s = hypersurfaceQuotientHom hP (X none)) :
    Away (hypersurfaceGrading P hP) s ≃+* HypersurfaceRing (dehomogenize P) := by
  subst s
  exact standardHypersurfaceChartEquiv hP

private theorem standardChartRingEquivAt_mk {τ ℓ : Type u} [CommRing ℓ]
    {P : MvPolynomial (Option τ) ℓ} (hP : P.IsHomogeneous d)
    {s : HypersurfaceRing P} (hs : s = hypersurfaceQuotientHom hP (X none))
    (hs' : s ∈ hypersurfaceGrading P hP 1)
    (m : ℕ) (Q : MvPolynomial (Option τ) ℓ) (hQ : Q.IsHomogeneous (m • (1 : ℕ))) :
    standardChartRingEquivAt hP hs
      (Away.mk _ hs' m (hypersurfaceQuotientHom hP Q) ((hypersurfaceQuotientHom hP).map_mem hQ)) =
        Ideal.Quotient.mk _ (dehomogenize Q) := by
  subst s
  change standardHypersurfaceChartEquiv hP
    (Away.map (hypersurfaceQuotientHom hP) (X none)
      (Away.mk _ (isHomogeneous_X ℓ (none : Option τ)) m Q hQ)) = _
  rw [show Away.map (hypersurfaceQuotientHom hP) (X none) =
      standardHypersurfaceChartMap hP by rfl, standardHypersurfaceChartEquiv_apply_map,
    projectiveChartNormalize_fraction]

theorem away_map_injective_of_injective
    {A B τ υ : Type u} {ι : Type*} [CommRing A] [CommRing B]
    [AddCommMonoid ι] [DecidableEq ι]
    [SetLike τ A] [AddSubgroupClass τ A] [SetLike υ B] [AddSubgroupClass υ B]
    {𝒜 : ι → τ} {ℬ : ι → υ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Injective f) (s : A) :
    Function.Injective (Away.map f s) := by
  let W := Submonoid.powers s
  let V := Submonoid.powers (f s)
  have hWV : W.map f.toRingHom = V := Submonoid.map_powers f.toRingHom s
  let : IsLocalization (W.map f.toRingHom) (Localization V) :=
    hWV.symm ▸ Localization.isLocalization
  have hWV' : W ≤ V.comap f.toRingHom := W.le_comap_of_map_le hWV.le
  let g : Localization W →+* Localization V :=
    IsLocalization.map (Localization V) f.toRingHom hWV'
  have hg : Function.Injective g := by
    have h := IsLocalization.map_injective_of_injective W (Localization W) (Localization V)
      (g := f.toRingHom) hf
    rwa [show IsLocalization.map (Localization V) f.toRingHom W.le_comap_map = g from rfl] at h
  intro x y he
  apply val_injective
  apply hg
  have hm (z : Away 𝒜 s) : g z.val = (Away.map f s z).val := by
    obtain ⟨r,rfl⟩ := HomogeneousLocalization.mk_surjective z
    simp [g, W, V, Away.map, map_mk, val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [hm, hm, he]

variable {σ τ k : Type u} [CommRing k]

def chartRenameGradedHom (e : σ ≃ Option τ) :
    homogeneousSubmodule σ k →+*ᵍ homogeneousSubmodule (Option τ) k where
  __ := (rename e : MvPolynomial σ k →ₐ[k] MvPolynomial (Option τ) k).toRingHom
  map_mem hp := (show IsHomogeneous _ _ from hp).rename_isHomogeneous

def standardProjectiveChartEquivAt {s : MvPolynomial (Option τ) k} (hs : s = X none) :
    Away (homogeneousSubmodule (Option τ) k) s ≃+* MvPolynomial τ k := by
  subst s
  exact projectiveChartRingEquiv

private theorem standardProjectiveChartEquivAt_mk {s : MvPolynomial (Option τ) k}
    (hs : s = X none) (hs' : s ∈ homogeneousSubmodule (Option τ) k 1)
    (m : ℕ) (p : MvPolynomial (Option τ) k) (hp : p.IsHomogeneous (m • (1 : ℕ))) :
    standardProjectiveChartEquivAt hs (Away.mk _ hs' m p hp) = dehomogenize p := by
  subst s
  exact projectiveChartNormalize_fraction _ hp

/-- A polynomial projective chart is expressed in coordinates in which
the inverted variable has index `none`. -/
def projectiveChartEquivOfRename (e : σ ≃ Option τ) (i : σ) (hi : e i = none) :
    Away (homogeneousSubmodule σ k) (X i) ≃+* MvPolynomial τ k := by
  let f := chartRenameGradedHom (k := k) e
  have hx : f (X i) = X none := by
    change rename e (X i) = X none
    rw [rename_X, hi]
  have hb : Function.Bijective f := (renameEquiv k e).bijective
  exact (RingEquiv.ofBijective _ ⟨away_map_injective_of_injective f hb.1 (X i),
    proj_away_map_surjective_of_surjective f hb.2 (isHomogeneous_X k i)⟩).trans
      (standardProjectiveChartEquivAt hx)

theorem projectiveChartEquivOfRename_mk (e : σ ≃ Option τ) (i : σ) (hi : e i = none)
    (m : ℕ) (p : MvPolynomial σ k) (hp : p.IsHomogeneous (m • (1 : ℕ))) :
    projectiveChartEquivOfRename e i hi (Away.mk _ (isHomogeneous_X k i) m p hp) =
      dehomogenize (rename e p) := by
  unfold projectiveChartEquivOfRename
  rw [RingEquiv.trans_apply, RingEquiv.ofBijective_apply, Away.map_mk]
  exact standardProjectiveChartEquivAt_mk _ _ _ _ hp.rename_isHomogeneous

variable {d : ℕ} {F : MvPolynomial σ k}

/-- The localization at a hypersurface coordinate agrees with the quotient
of the dehomogenized polynomial after renaming that coordinate to `none`. -/
def hypersurfaceChartEquivOfRename (hF : F.IsHomogeneous d) (e : σ ≃ Option τ)
    (i : σ) (hi : e i = none) {s : HypersurfaceRing F}
    (hs : s = hypersurfaceQuotientHom hF (X i)) :
    Away (hypersurfaceGrading F hF) s ≃+* HypersurfaceRing (dehomogenize (rename e F)) := by
  subst s
  let g := hypersurfaceRenameGradedHom hF e
  have hx : g (hypersurfaceQuotientHom hF (X i)) =
      hypersurfaceQuotientHom hF.rename_isHomogeneous (X none) := by
    change Ideal.Quotient.mk _ (rename e (X i)) = Ideal.Quotient.mk _ (X none)
    rw [rename_X, hi]
  have hg : Function.Bijective g := (hypersurfaceRenameRingEquiv e).bijective
  have hinj := away_map_injective_of_injective g hg.1 (hypersurfaceQuotientHom hF (X i))
  have hsurj := proj_away_map_surjective_of_surjective g hg.2
    ((hypersurfaceQuotientHom hF).map_mem (isHomogeneous_X k i))
  exact (RingEquiv.ofBijective _ ⟨hinj, hsurj⟩).trans
    (standardChartRingEquivAt hF.rename_isHomogeneous hx)

theorem hypersurfaceChartEquivOfRename_mk (hF : F.IsHomogeneous d) (e : σ ≃ Option τ)
    (i : σ) (hi : e i = none) {s : HypersurfaceRing F}
    (hs : s = hypersurfaceQuotientHom hF (X i)) (hs' : s ∈ hypersurfaceGrading F hF 1)
    (m : ℕ) (p : MvPolynomial σ k) (hp : p.IsHomogeneous (m • (1 : ℕ))) :
    hypersurfaceChartEquivOfRename hF e i hi hs
      (Away.mk _ hs' m (hypersurfaceQuotientHom hF p) ((hypersurfaceQuotientHom hF).map_mem hp)) =
        Ideal.Quotient.mk _ (dehomogenize (rename e p)) := by
  subst s
  unfold hypersurfaceChartEquivOfRename
  rw [RingEquiv.trans_apply, RingEquiv.ofBijective_apply, Away.map_mk]
  exact standardChartRingEquivAt_mk _ _ _ _ _ hp.rename_isHomogeneous

end

end Birch
