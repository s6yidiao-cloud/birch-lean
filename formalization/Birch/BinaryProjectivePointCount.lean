import Birch.ProjectiveHypersurfacePointEquivalence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.SetTheory.Cardinal.NatCard

/-! # A projective root count for binary forms -/

namespace Birch

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

variable {K : Type} [Field K]

private theorem projectiveRep_fin_one_apply_ne_zero (P : ℙ K (Fin 1 → K)) :
    P.rep 0 ≠ 0 := by
  intro h
  apply P.rep_nonzero
  funext i
  rw [Fin.eq_zero i]
  exact h

private theorem subsingleton_projectivization_fin_one : Subsingleton (ℙ K (Fin 1 → K)) := by
  refine ⟨fun P Q => ?_⟩
  rw [← Projectivization.mk_rep P, ← Projectivization.mk_rep Q]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
  refine ⟨P.rep 0 / Q.rep 0, ?_⟩
  funext i
  rw [Fin.eq_zero i]
  change (P.rep 0 / Q.rep 0) * Q.rep 0 = P.rep 0
  exact div_mul_cancel₀ _ (projectiveRep_fin_one_apply_ne_zero Q)

private theorem eval_uniqueAlgEquiv_fin_one (g : MvPolynomial (Fin 1) K) (v : Fin 1 → K) :
    (MvPolynomial.uniqueAlgEquiv K (Fin 1) g).eval (v 0) = g.eval v := by
  rw [← Fin.eq_zero (default : Fin 1)]
  simpa only [Polynomial.eval₂_id, MvPolynomial.eval₂_id] using
    (MvPolynomial.eval₂_uniqueAlgEquiv (f := g) (φ := RingHom.id K) (a := v))

private theorem natDegree_uniqueAlgEquiv_fin_one_le {g : MvPolynomial (Fin 1) K}
    {r : ℕ} (h : g.totalDegree ≤ r) :
    (MvPolynomial.uniqueAlgEquiv K (Fin 1) g).natDegree ≤ r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  change g.totalDegree < (Finsupp.single (default : Fin 1) i).degree
  simpa only [Finsupp.degree_single] using h.trans_lt hi

private theorem uniqueAlgEquiv_homogeneousComponent_fin_one (g : MvPolynomial (Fin 1) K)
    (r : ℕ) :
    MvPolynomial.uniqueAlgEquiv K (Fin 1) (homogeneousComponent r g) =
      Polynomial.C ((MvPolynomial.uniqueAlgEquiv K (Fin 1) g).coeff r) * Polynomial.X^r := by
  apply Polynomial.ext
  intro j
  rw [MvPolynomial.coeff_uniqueAlgEquiv, coeff_homogeneousComponent, Finsupp.degree_single,
    Polynomial.coeff_C_mul_X_pow]
  by_cases h : r = j
  · subst j
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
  · simp only [ite_eq_right (Ne.symm h)]

private theorem natCard_projectiveHypersurfacePoints_option_fin_one_le_degree {r : ℕ}
    {F : MvPolynomial (Option (Fin 1)) K} (hr : 0 < r)
    (hF : F.IsHomogeneous r) (hF₀ : F ≠ 0) :
    Nat.card (projectiveHypersurfacePoints F) ≤ r := by
  classical
  let g := dehomogenize F
  let q := MvPolynomial.uniqueAlgEquiv K (Fin 1) g
  let U := {x : Fin 1 → K // g.eval x = 0}
  let V := projectiveHypersurfacePoints (homogeneousComponent r g)
  have hgrec : deligneLevelClosure r g 0 = F := deligneLevelClosure_dehomogenize hF
  have hg : g.totalDegree ≤ r := totalDegree_dehomogenize_le_homogeneous hF
  have hg₀ : g ≠ 0 := fun h => hF₀ (eq_zero_of_dehomogenize_eq_zero hF h)
  have hq₀ : q ≠ 0 := fun h => hg₀ ((MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective
    (h.trans (map_zero _).symm))
  have hq : q.natDegree ≤ r := natDegree_uniqueAlgEquiv_fin_one_le hg
  let e : U ≃ {x : K // x ∈ q.roots.toFinset} :=
    (Equiv.funUnique (Fin 1) K).subtypeEquiv (by
      intro x
      change g.eval x = 0 ↔ x 0 ∈ q.roots.toFinset
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hq₀]
      change g.eval x = 0 ↔ q.eval (x 0) = 0
      rw [eval_uniqueAlgEquiv_fin_one g x])
  let : Finite U := Finite.of_equiv _ e.symm
  let : Subsingleton (ℙ K (Fin 1 → K)) := subsingleton_projectivization_fin_one
  have : Subsingleton V := inferInstanceAs (Subsingleton (Subtype _))
  have hU : Nat.card U ≤ q.natDegree := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' q)
  have hV : Nat.card V ≤ 1 :=
    (Finite.card_le_one_iff_subsingleton (α := V)).mpr inferInstance
  have hc : Nat.card (projectiveHypersurfacePoints F) = Nat.card U + Nat.card V := by
    rw [← hgrec, Nat.card_congr (deligneLevelClosure_points_equiv hr hg 0), Nat.card_sum]
  rw [hc]
  by_cases hz : q.coeff r = 0
  · have hn : q.natDegree ≠ r := by
      intro h
      rw [← h, Polynomial.coeff_natDegree] at hz
      exact hq₀ (Polynomial.leadingCoeff_eq_zero.mp hz)
    omega
  · have : IsEmpty V := ⟨fun P => by
      have he := eval_uniqueAlgEquiv_fin_one (homogeneousComponent r g) P.val.rep
      rw [uniqueAlgEquiv_homogeneousComponent_fin_one, P.property] at he
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X_pow] at he
      exact (mul_ne_zero hz (pow_ne_zero _ (projectiveRep_fin_one_apply_ne_zero P.val))) he⟩
    simpa using hU.trans hq

/-- A nonzero homogeneous binary form of degree `r` has at most `r`
projective roots over any coefficient field. -/
theorem natCard_projectiveHypersurfacePoints_fin_two_le_degree {r : ℕ}
    {G : MvPolynomial (Fin 2) K} (hG : G.IsHomogeneous r) (hG₀ : G ≠ 0) :
    Nat.card (projectiveHypersurfacePoints G) ≤ r := by
  by_cases hr : 0 < r
  · let e := finSuccEquiv 1
    rw [Nat.card_congr (projectiveHypersurfacePoints_rename_equiv hG e)]
    have hG' : rename e G ≠ 0 := fun h => hG₀
      (rename_injective (R := K) e e.injective (h.trans (map_zero _).symm))
    exact natCard_projectiveHypersurfacePoints_option_fin_one_le_degree hr hG.rename_isHomogeneous hG'
  · have h : G = C (coeff 0 G) := totalDegree_eq_zero_iff_eq_C.mp (by
      have := hG.totalDegree hG₀
      omega)
    have hcoef : coeff 0 G ≠ 0 := fun hc => hG₀ (h.trans (by rw [hc, map_zero]))
    have : IsEmpty (projectiveHypersurfacePoints G) := ⟨fun P => hcoef (by
      let v := P.val.rep
      have hp : G.eval v = 0 := P.property
      have he := congrArg (eval v) h
      rw [he, eval_C] at hp
      exact hp)⟩
    simp

end

end Birch
