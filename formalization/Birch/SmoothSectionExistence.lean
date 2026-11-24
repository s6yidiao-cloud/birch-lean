import Birch.CompletionClassical
import Birch.HyperplaneRestriction
import Birch.TangentRelation

/-! # Iterating smooth hyperplane cuts of a gradient cone -/

open Matrix MvPolynomial
open scoped Matrix BigOperators ContDiff

namespace Birch

noncomputable section

private theorem linearSectionOver_one {K : Type*} [Field K] [Infinite K] {n : ℕ} (F : IntForm n) :
    linearSectionOver (1 : Matrix (Fin n) (Fin n) K) F = map (Int.castRingHom K) F := by
  apply MvPolynomial.funext
  intro x
  rw [eval_linearSectionOver, one_mulVec, MvPolynomial.eval_map, evalForm]

/-- A homogeneous relation among tangent normals lets us make successive
smooth hyperplane cuts until the remaining gradient locus is the origin. -/
theorem exists_geometricSection_of_tangentRelations {K : Type} [Field K] [IsAlgClosed K] [Infinite K]
    {n l s r : ℕ} (hn : n = l+s) (F : IntForm n) (hF : F.IsHomogeneous r) (hr : (r : K) ≠ 0)
    (htangent : ∀ (m : ℕ) (G : MvPolynomial (Fin (m+1)) K), G.IsHomogeneous r →
      ∃ e : ℕ, ∃ T : MvPolynomial (Fin (m+1)) K, T.IsHomogeneous e ∧ T ≠ 0 ∧
        ∀ y : Fin (m+1) → K, G.eval y = 0 → T.eval (fun i => (pderiv i G).eval y) = 0)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ gradientIdealOver (map (Int.castRingHom K) F)) ≤
      (s : WithBot ℕ∞)) :
    ∃ U : Matrix (Fin n) (Fin l) K,
      ∀ x : Fin l → K, (∀ j, (pderiv j (linearSectionOver U F)).eval x = 0) → x = 0 := by
  have aux (k : ℕ) (U : Matrix (Fin n) (Fin (l+k)) K)
      (hdim : ringKrullDim (MvPolynomial (Fin (l+k)) K ⧸ gradientIdealOver (linearSectionOver U F)) ≤
        (k : WithBot ℕ∞)) :
      ∃ V : Matrix (Fin n) (Fin l) K,
        ∀ x : Fin l → K, (∀ j, (pderiv j (linearSectionOver V F)).eval x = 0) → x = 0 := by
    induction k with
    | zero =>
      exact ⟨U, critical_eq_zero_of_gradientIdealOver_dim_le_zero
        (isHomogeneous_linearSectionOver U hF) (by simpa using hdim)⟩
    | succ k ih =>
      let G := linearSectionOver U F
      have hG := isHomogeneous_linearSectionOver U hF
      obtain ⟨e,T,hT,hT₀,hvanish⟩ := htangent (l+k) G hG
      obtain ⟨a,_,ha⟩ := exists_hyperplaneSubstitution_dim_drop hG hr hT hT₀ hvanish hdim
      rw [hyperplaneSubstitution_linearSectionOver] at ha
      exact ih (U * hyperplaneMatrix a) ha
  subst n
  exact aux s 1 (by rwa [linearSectionOver_one])

/-- Smooth sections over the algebraic closure exist in every required
interior dimension. Each cut avoids a homogeneous relation on tangent normals. -/
theorem primeGeometricInteriorSections (n r : ℕ) (hr : 2 ≤ r) :
    PrimeGeometricInteriorSections n r := by
  intro p hp hpr F hF s _ _ hdim
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  have hchar : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hrK : (r : K) ≠ 0 := by
    intro h
    exact hpr.not_ge (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff K p r).mp h))
  have hn : n = (n-s.val)+s.val := (Nat.sub_add_cancel (Nat.lt_succ_iff.mp s.isLt)).symm
  apply exists_geometricSection_of_tangentRelations (K := K) hn F hF hrK
    (fun _ _ hG => exists_homogeneous_tangent_relation hG hr)
  rw [gradientIdealOver_map_int]
  exact hdim.le

/-- Completion follows from the direction counts and uniform square-root
bounds in the terminal degrees at least three. -/
theorem completionInputs_of_direction_bound_uniform_twisted {n d : ℕ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hDirection : PrimeDirectionBound n d)
    (hTwisted : ∀ r, 3 ≤ r → r < d → ∀ l ≤ n, UniformTwistedPrimeBound r l) :
    CompletionInputs d F w := by
  apply completionInputs_of_uniform_primeBounds hF hw hwbox hDirection
  · exact fun r hr _ => primeSectionBound_of_interior hr
      (primeInteriorSectionBound_of_geometric hr (primeGeometricInteriorSections n r hr))
  · intro r hr hrd l hl
    rcases eq_or_lt_of_le hr with he | hlt
    · exact he ▸ uniformTwistedPrimeBound_of_deligneTwistedDegree le_rfl deligneTwistedDegree_two l
    · exact hTwisted r hlt hrd l hl

/-- Deligne's estimates in terminal degrees supply the completion bound. -/
theorem completionInputs_of_direction_bound_deligne {n d : ℕ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hDirection : PrimeDirectionBound n d)
    (hDeligne : ∀ r, 3 ≤ r → r < d → DeligneTwistedDegree r) : CompletionInputs d F w :=
  completionInputs_of_direction_bound_uniform_twisted hF hw hwbox hDirection fun r hr hrd l _ =>
    uniformTwistedPrimeBound_of_deligneTwistedDegree (by omega) (hDeligne r hr hrd) l

/-- The intermediate slicing interface supplies the direction-count input. -/
theorem completionInputs_of_direction_slicing_deligne {n d : ℕ}
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hDirection : PrimeDirectionIntermediateSlicing n d)
    (hDeligne : ∀ r, 3 ≤ r → r < d → DeligneTwistedDegree r) : CompletionInputs d F w :=
  completionInputs_of_direction_bound_deligne hF hw hwbox
    (primeDirectionBound_of_intermediate_slicing hDirection) hDeligne

end

end Birch
