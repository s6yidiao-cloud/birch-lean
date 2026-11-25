module

public import Birch.FermatModel
public import Birch.DiagonalCompleteSums
public import Birch.ProjectiveExtensionPoints
public import Birch.ProjectiveSmoothIntegral
public import Birch.ProjectiveHypersurfaceSmooth
public import Birch.ProjectiveWeilPointCount
public import Mathlib.NumberTheory.LegendreSymbol.Complex

@[expose] public section

/-! # Projective point counts of Fermat hypersurfaces -/

open AlgebraicGeometry MvPolynomial
open scoped BigOperators LinearAlgebra.Projectivization

namespace Birch

noncomputable section

/-- The zero vectors of a homogeneous equation are its origin and the
units times representatives of its projective points. -/
theorem natCard_affineHomogeneousZeros_eq {σ F : Type*} [Field F] [Fintype F] [Finite σ]
    {G : MvPolynomial σ F} {d : ℕ} (hG : G.IsHomogeneous d) (hd : 0 < d) :
    Nat.card {x : σ → F // G.eval x = 0} =
      Nat.card (projectiveHypersurfacePoints G) * (Fintype.card F - 1) + 1 := by
  classical
  let A := {x : σ → F // G.eval x = 0}
  let B := {x : A // x.val ≠ 0}
  let P := projectiveHypersurfacePoints G
  have hzero : G.eval 0 = 0 := by
    rw [eval_zero]
    exact hG.coeff_eq_zero (by simpa only [map_zero] using hd.ne)
  let ϕ (p : P × Fˣ) : B :=
    ⟨⟨p.2 • p.1.val.rep, by
      change G.eval (fun j => (p.2 : F) * p.1.val.rep j) = 0
      rw [eval_scale_of_homogeneous hG, p.1.prop, mul_zero]⟩,
      smul_ne_zero (Units.ne_zero p.2) p.1.val.rep_nonzero⟩
  have hP (p : P × Fˣ) :
      Projectivization.mk F (ϕ p).val.val (ϕ p).prop = p.1.val := by
    convert Projectivization.mk_rep p.1.val using 1
    exact (Projectivization.mk_eq_mk_iff' F _ _ _ _).mpr ⟨↑p.2, rfl⟩
  have hb : Function.Bijective ϕ := by
    constructor
    · intro p q h
      have ha : p.1 = q.1 := Subtype.ext ((hP p).symm.trans ((congrArg
        (fun r : B => Projectivization.mk F r.val.val r.prop) h).trans (hP q)))
      have hz : p.2 • p.1.val.rep = q.2 • q.1.val.rep :=
        congrArg (fun r : B => r.val.val) h
      rw [← ha] at hz
      have hu : p.2 = q.2 := by
        apply Units.ext
        change (p.2 : F) • p.1.val.rep = (q.2 : F) • p.1.val.rep at hz
        exact smul_left_injective F p.1.val.rep_nonzero hz
      exact Prod.ext ha hu
    · intro x
      let p : P := ⟨Projectivization.mk F x.val.val x.prop,
        (eval_rep_mk_eq_zero_iff hG _ _).mpr x.val.prop⟩
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := F) x.val.val x.prop
      have hval : a • x.val.val = p.val.rep := ha
      refine ⟨(p,a⁻¹),Subtype.ext (Subtype.ext ?_)⟩
      change a⁻¹ • p.val.rep = x.val.val
      exact inv_smul_eq_iff.mpr hval.symm
  have heq : Nat.card B = Nat.card P * (Fintype.card F - 1) := by
    rw [← Nat.card_congr (Equiv.ofBijective ϕ hb), Nat.card_prod,
      Nat.card_eq_fintype_card (α := Fˣ), Fintype.card_units]
  let C := {x : A // ¬ x.val ≠ 0}
  let : Unique C :=
    { default := ⟨⟨0,hzero⟩,not_not_intro rfl⟩
      uniq := fun x => Subtype.ext (Subtype.ext (not_not.mp x.prop)) }
  change Nat.card A = _
  rw [← Nat.card_congr (Equiv.sumCompl (fun x : A => x.val ≠ 0)), Nat.card_sum,
    show Nat.card C = 1 from Nat.card_unique, heq]

/-- Additive orthogonality counts the zeros of any function on a finite set. -/
private theorem card_zeros_mul_eq_sum_addChar {F ι : Type*} [Field F] [Fintype F] [Fintype ι]
    (f : ι → F) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (Fintype.card F : ℂ) * (Nat.card {x : ι // f x = 0} : ℂ) =
      ∑ a : F, ∑ x : ι, ψ (a * f x) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [AddChar.sum_mulShift _ hψ]
  push_cast
  rw [← Finset.sum_filter, Finset.sum_const, ← Fintype.card_subtype,
    nsmul_eq_mul, Nat.card_eq_fintype_card, mul_comm]

/-- In any finite field, each nontrivial character sum of a diagonal
polynomial factors into one-variable Gauss sums. -/
theorem norm_sum_addChar_diagonal_le {F : Type*} [Field F] [Fintype F] {l d : ℕ}
    (hd : 0 < d) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (c : Fin l → F)
    (hc : ∀ i, c i ≠ 0) :
    ‖∑ x : Fin l → F, ψ (∑ i, c i * x i ^ d)‖ ≤
      ((d : ℝ) - 1) ^ l * (Fintype.card F : ℝ)^((l : ℝ) / 2) := by
  rw [diagonal_addChar_sum_eq_prod, norm_prod]
  have hbound (i : Fin l) : ‖∑ x : F, ψ (c i * x ^ d)‖ ≤
      ((d : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by
    simpa only [AddChar.mulShift_apply, mul_comm (c i)] using
      norm_sum_addChar_pow_le hd (ψ.mulShift (c i)) (hψ (hc i))
  calc
    _ ≤ ∏ _i : Fin l, ((d : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hbound i)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg (Fintype.card F))]
      congr 2
      ring

/-- Square-root bounds on the nonzero additive twists of a homogeneous
equation give square-root error in its projective point count. -/
theorem abs_sub_projectiveSpacePointCount_le_of_addChar {F : Type*} [Field F] [Fintype F]
    {N d : ℕ} (hd : 0 < d) {G : MvPolynomial (Fin (N+2)) F} (hG : G.IsHomogeneous d)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (C : ℝ)
    (hbound : ∀ a : F, a ≠ 0 →
      ‖∑ x : Fin (N+2) → F, ψ (a * G.eval x)‖ ≤ C * (Fintype.card F : ℝ)^(((N+2 : ℕ) : ℝ)/2)) :
    |(Nat.card (projectiveHypersurfacePoints G) : ℝ) -
      (projectiveSpacePointCount (Fintype.card F) N : ℝ)| ≤
        C * (Fintype.card F : ℝ)^((N : ℝ)/2) := by
  classical
  let q := Fintype.card F
  let A := Nat.card {x : Fin (N+2) → F // G.eval x = 0}
  let P := Nat.card (projectiveHypersurfacePoints G)
  let B := projectiveSpacePointCount q N
  have hq : 1 < q := Fintype.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hcard : A = P * (q-1) + 1 :=
    natCard_affineHomogeneousZeros_eq hG hd
  have hgeom : q^(N+1) = B * (q-1) + 1 := by
    have hp := Projectivization.card' F (Fin (N+1) → F)
    rw [Projectivization.card_of_finrank F _ (by simp : Module.finrank F (Fin (N+1) → F) = N+1),
      Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card] at hp
    simpa only [B, q, projectiveSpacePointCount, Nat.range_succ_eq_Iic] using hp
  let S (a : F) := ∑ x : Fin (N+2) → F, ψ (a * G.eval x)
  have hS₀ : S 0 = (q : ℂ)^(N+2) := by
    simp [S, q]
  have hsum : ∑ a ∈ ({0} : Finset F)ᶜ, S a =
      ((q : ℝ) * ((q : ℝ)-1) * ((P : ℝ) - B) : ℝ) := by
    have h := card_zeros_mul_eq_sum_addChar (fun x : Fin (N+2) → F => G.eval x) ψ hψ
    change (q : ℂ) * (A : ℂ) = ∑ a : F, S a at h
    have hc : ((q - 1 : ℕ) : ℂ) = (q : ℂ) - 1 := by rw [Nat.cast_sub hq.le, Nat.cast_one]
    have hgeomC : (q : ℂ) ^ (N+1) = (B : ℂ) * ((q : ℂ) - 1) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, hc] using
        congrArg (fun x : ℕ => (x : ℂ)) hgeom
    rw [Fintype.sum_eq_add_sum_compl 0, hS₀, hcard, pow_succ, hgeomC] at h
    push_cast [hc] at h ⊢
    linear_combination -h
  have hB : ‖∑ a ∈ ({0} : Finset F)ᶜ, S a‖ ≤
      ((q : ℝ)-1) * (C * (q : ℝ)^(((N+2 : ℕ) : ℝ)/2)) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _a ∈ ({0} : Finset F)ᶜ,
          C * (q : ℝ)^(((N+2 : ℕ) : ℝ)/2) :=
        Finset.sum_le_sum (fun a ha => hbound a (by simpa using ha))
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_compl, Finset.card_singleton,
          Nat.cast_sub hq.le, Nat.cast_one]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (q : ℝ) * ((q : ℝ)-1))] at hB
  have hrpow : (q : ℝ)^(((N+2 : ℕ) : ℝ)/2) = (q : ℝ) * (q : ℝ)^((N : ℝ)/2) := by
    rw [show ((N+2 : ℕ) : ℝ) / 2 = 1 + (N : ℝ)/2 by push_cast; ring,
      Real.rpow_add (by positivity), Real.rpow_one]
  rw [hrpow] at hB
  change |(P : ℝ) - B| ≤ _
  exact (mul_le_mul_iff_of_pos_left (by positivity : 0 < (q : ℝ) * ((q : ℝ)-1))).mp
    (hB.trans_eq (by ring))

/-- Over every finite field, the Fermat equation in `N+2` variables
has the expected projective point count up to square-root error. -/
theorem abs_sub_projectiveSpacePointCount_fermat_le {F : Type*} [Field F] [Fintype F]
    {d : ℕ} (hd : 0 < d) (N : ℕ) :
    |(Nat.card (projectiveHypersurfacePoints (fermatPolynomial F N d)) : ℝ) -
      (projectiveSpacePointCount (Fintype.card F) N : ℝ)| ≤
        ((d : ℝ) - 1)^(N+2) * (Fintype.card F : ℝ)^((N : ℝ)/2) := by
  let ψ := AddChar.FiniteField.primitiveChar_to_Complex F
  apply abs_sub_projectiveSpacePointCount_le_of_addChar hd
    (isHomogeneous_fermatPolynomial F N d) ψ
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F)
  intro a ha
  have h := norm_sum_addChar_diagonal_le hd ψ
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F)
    (fun _ : Fin (N+2) => a) (fun _ => ha)
  simpa only [eval_fermatPolynomial, Finset.mul_sum] using h

/-- The Weil theorem for a Fermat hypersurface uses precisely these
extension-field point counts. -/
theorem abs_sub_projectiveSpacePointCount_overHom_fermat_le
    {F L : Type} [Field F] [Field L] [Algebra F L] [Finite L]
    {d : ℕ} (hd : 0 < d) (N : ℕ) :
    let S := CategoryTheory.Over.mk
      (projectiveHypersurfaceToField (isHomogeneous_fermatPolynomial F N d))
    |(Nat.card (CategoryTheory.Over.mk
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap F L))) ⟶ S) : ℝ) -
        (projectiveSpacePointCount (Nat.card L) N : ℝ)| ≤
        ((d : ℝ) - 1)^(N+2) * (Nat.card L : ℝ)^((N : ℝ)/2) := by
  let := Fintype.ofFinite L
  dsimp only
  rw [Nat.card_congr (overHomEquivProjectiveHypersurfacePoints hd
    (isHomogeneous_fermatPolynomial F N d)), map_fermatPolynomial]
  simpa only [Nat.card_eq_fintype_card (α := L)] using
    abs_sub_projectiveSpacePointCount_fermat_le (F := L) hd N

/-- The Fermat scheme in positive dimension meets the geometric hypotheses
of the smooth proper Weil theorem. -/
theorem fermat_hypersurface_geometry {F : Type} [Field F]
    {N d : ℕ} (hN : 0 < N) (hd : 2 ≤ d) (hcast : (d : F) ≠ 0) :
    let f := projectiveHypersurfaceToField (isHomogeneous_fermatPolynomial F N d)
    IsProper f ∧ SmoothOfRelativeDimension N f ∧ GeometricallyIrreducible f := by
  let hG := isHomogeneous_fermatPolynomial F N d
  let f := projectiveHypersurfaceToField hG
  have hjac := exists_projectiveJacobianCertificate_fermat N d hcast
  have : GeometricallyIntegral f :=
    geometricallyIntegral_projectiveHypersurfaceToField (by omega) hd hcast hG hjac
  refine ⟨isProper_projectiveHypersurfaceToField hG (by omega),?_,inferInstance⟩
  simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
    smoothOfRelativeDimension_projectiveHypersurfaceToField hG hjac

end
end Birch
