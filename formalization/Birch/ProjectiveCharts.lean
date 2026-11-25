module

public import Birch.MvPolynomialCoefficientCompat

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-! # Standard affine charts of projective space -/

open MvPolynomial HomogeneousLocalization
open scoped BigOperators

namespace Birch

noncomputable section

variable {σ R : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Set the extra homogeneous variable to one and keep every other variable. -/
def dehomogenize : MvPolynomial (Option σ) R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i : Option σ => i.elim 1 X)

@[simp] theorem dehomogenize_X_none :
    dehomogenize (X (R := R) (none : Option σ)) = (1 : MvPolynomial σ R) := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_X_some (i : σ) :
    dehomogenize (X (R := R) (some i)) = X i := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_C (c : R) :
    dehomogenize (C c : MvPolynomial (Option σ) R) = C c := by
  simp [dehomogenize]

theorem dehomogenize_monomial (m : Option σ →₀ ℕ) (c : R) :
    dehomogenize (monomial m c) = monomial m.some c := by
  rw [dehomogenize, aeval_monomial, Finsupp.prod_option_index]
  · rw [monomial_eq]
    simp only [Option.elim_some, Option.elim_none, one_pow, one_mul, algebraMap_eq]
  · simp
  · intro i a b
    exact pow_add _ _ _

private theorem degree_option (m : Option σ →₀ ℕ) :
    m.degree = m none + m.some.degree := by
  simp only [Finsupp.degree_apply]
  exact Finsupp.sum_option_index m (fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)

/-- A fixed homogeneous degree can be recovered after setting one variable
to one. -/
theorem coeff_dehomogenize_of_isHomogeneous {p : MvPolynomial (Option σ) R}
    {m : Option σ →₀ ℕ} (hp : p.IsHomogeneous m.degree) :
    AddMonoidAlgebra.coeff (dehomogenize p) m.some = AddMonoidAlgebra.coeff p m := by
  classical
  conv_lhs => rw [p.as_sum, map_sum, coeff_sum]
  by_cases hm : m ∈ p.support
  · rw [Finset.sum_eq_single_of_mem m hm]
    · simp [dehomogenize_monomial]
    · intro b hb hne
      have hd := (hp.degree_eq_sum_deg_support hb).symm
      change b.degree = m.degree at hd
      have hs : b.some ≠ m.some := by
        intro h
        apply hne
        have h₀ : b none = m none := by rw [degree_option b, degree_option m, h] at hd; omega
        exact Finsupp.optionEquiv.injective (Prod.ext h₀ h)
      simp [dehomogenize_monomial, coeff_monomial, hs]
  · rw [notMem_support_iff.mp hm]
    apply Finset.sum_eq_zero
    intro b hb
    have hd := (hp.degree_eq_sum_deg_support hb).symm
    change b.degree = m.degree at hd
    have hs : b.some ≠ m.some := by
      intro h
      apply hm
      have h₀ : b none = m none := by rw [degree_option b, degree_option m, h] at hd; omega
      exact (Finsupp.optionEquiv.injective (Prod.ext h₀ h)) ▸ hb
    simp [dehomogenize_monomial, coeff_monomial, hs]

theorem eq_zero_of_dehomogenize_eq_zero {p : MvPolynomial (Option σ) R} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : dehomogenize p = 0) : p = 0 := by
  by_contra! hp₀
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hp₀
  have hdeg := (hp.degree_eq_sum_deg_support (mem_support_iff.mpr hm)).symm
  change m.degree = d at hdeg
  exact hm (by rw [← coeff_dehomogenize_of_isHomogeneous (hdeg ▸ hp), h]; simp)

/-- The degree-zero homogeneous localization at the extra variable. -/
abbrev StandardProjectiveChart (σ R : Type*) [CommRing R] :=
  Away (homogeneousSubmodule (Option σ) R) (X none)

/-- The canonical map to the chart obtained by normalizing the distinguished
coordinate to one. -/
def projectiveChartNormalize : StandardProjectiveChart σ R →+* MvPolynomial σ R :=
  (Localization.awayLift (dehomogenize (σ := σ) (R := R)).toRingHom (X none)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)).comp (algebraMap _ _)

theorem projectiveChartNormalize_fraction (d : ℕ) {p : MvPolynomial (Option σ) R}
    (hp : p ∈ homogeneousSubmodule (Option σ) R (d • (1 : ℕ))) :
    projectiveChartNormalize
      (Away.mk _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R (none : Option σ))) d p hp) =
        dehomogenize p := by
  unfold projectiveChartNormalize
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk,
    Localization.awayLift_mk, one_pow, mul_one]
  · rfl
  · change dehomogenize (X (R := R) (none : Option σ)) * 1 = 1
    simp

/-- The copy of the coefficient ring in the degree-zero component. -/
def degreeZeroConstants (σ R : Type*) [CommRing R] : R →+* homogeneousSubmodule σ R 0 :=
  { toFun := fun a => ⟨C a, isHomogeneous_C σ a⟩
    map_zero' := Subtype.ext (map_zero C)
    map_one' := Subtype.ext (map_one C)
    map_add' := fun a b => Subtype.ext (map_add C a b)
    map_mul' := fun a b => Subtype.ext (map_mul C a b) }

theorem degreeZeroConstants_bijective (σ R : Type*) [CommRing R] :
    Function.Bijective (degreeZeroConstants σ R) := by
  refine ⟨fun a b h => C_injective σ R (congrArg Subtype.val h), ?_⟩
  intro f
  have hf : (f : MvPolynomial σ R).IsHomogeneous 0 := f.prop
  exact ⟨coeff 0 (f : MvPolynomial σ R), Subtype.ext
    (totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hf.totalDegree_le)).symm⟩

theorem projectiveChartNormalize_constants (a : R) :
    projectiveChartNormalize
      (fromZeroRingHom _ _ (degreeZeroConstants (Option σ) R a) : StandardProjectiveChart σ R) =
        (C a : MvPolynomial σ R) := by
  have ha : (C a : MvPolynomial (Option σ) R) ∈
      homogeneousSubmodule (Option σ) R (0 • (1 : ℕ)) := by
    rw [zero_nsmul]
    exact isHomogeneous_C (Option σ) a
  have h : (fromZeroRingHom _ _ (degreeZeroConstants (Option σ) R a) : StandardProjectiveChart σ R) =
      Away.mk _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R (none : Option σ))) 0 (C a) ha := by
    apply val_injective
    rw [Away.val_mk]
    change Localization.mk (C a) 1 = _
    congr 1
  exact h ▸ (projectiveChartNormalize_fraction 0 ha).trans (dehomogenize_C a)

/-- The affine coordinates, as the homogeneous fractions Xᵢ / X₀. -/
def projectiveChartCoordinate (i : σ) : StandardProjectiveChart σ R :=
  Away.mk _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R (none : Option σ))) 1 (X (some i)) ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R (some i)))

@[simp] theorem projectiveChartNormalize_coordinate (i : σ) :
    projectiveChartNormalize (projectiveChartCoordinate i : StandardProjectiveChart σ R) = (X i : MvPolynomial σ R) := by
  exact (projectiveChartNormalize_fraction 1 ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R (some i)))).trans
    (dehomogenize_X_some i)

/-- The degree-zero chart ring is the polynomial ring in the affine
coordinates. -/
def projectiveChartRingEquiv : StandardProjectiveChart σ R ≃+* MvPolynomial σ R :=
  RingEquiv.ofBijective projectiveChartNormalize (by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro z hz
      obtain ⟨d,p,hp,rfl⟩ := Away.mk_surjective _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R (none : Option σ))) z
      have hp' : p.IsHomogeneous d := by
        simpa only [nsmul_eq_mul, mul_one, Nat.cast_id, mem_homogeneousSubmodule] using hp
      rw [projectiveChartNormalize_fraction d hp] at hz
      have hzero := eq_zero_of_dehomogenize_eq_zero hp' hz
      apply val_injective
      simp [hzero, Localization.mk_zero]
    · let f : MvPolynomial σ R →+* StandardProjectiveChart σ R :=
        eval₂Hom ((fromZeroRingHom _ _).comp (degreeZeroConstants (Option σ) R))
          projectiveChartCoordinate
      have h : projectiveChartNormalize.comp f = RingHom.id _ := by
        apply ringHom_ext
        · intro x
          simp only [RingHom.comp_apply, f, eval₂Hom_C, projectiveChartNormalize_constants, RingHom.id_apply]
        · intro i
          change projectiveChartNormalize (f (X i)) = X i
          rw [show f (X i) = projectiveChartCoordinate i from eval₂Hom_X' _ _ _,
            projectiveChartNormalize_coordinate]
      intro p
      exact ⟨f p, DFunLike.congr_fun h p⟩)

end
end Birch
