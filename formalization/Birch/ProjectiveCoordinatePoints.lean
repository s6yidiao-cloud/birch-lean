module

public import Birch.DeligneLevelClosure
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

@[expose] public section

/-! # Coordinate projective points and their affine and infinite parts -/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace Birch

noncomputable section

/-- The rational projective points satisfying a homogeneous polynomial
equation. For a homogeneous polynomial, zero evaluation is independent of
the representative. -/
def projectiveHypersurfacePoints {σ K : Type*} [Field K] (G : MvPolynomial σ K) :=
  {v : ℙ K (σ → K) // G.eval v.rep = 0}

/-- Test a projective point using any nonzero representative vector. -/
theorem eval_rep_mk_eq_zero_iff {σ K : Type*} [Field K] {d : ℕ}
    {G : MvPolynomial σ K} (hG : G.IsHomogeneous d) (v : σ → K) (hv : v ≠ 0) :
    G.eval (Projectivization.mk K v hv).rep = 0 ↔ G.eval v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep (K := K) v hv
  rw [← ha, Units.smul_def]
  change G.eval (fun i => (a : K) * v i) = 0 ↔ _
  rw [eval_scale_of_homogeneous hG, mul_eq_zero]
  simp only [pow_ne_zero _ (Units.ne_zero a), false_or]

def atInfinity {σ K : Type*} [Field K] : (σ → K) →ₗ[K] (Option σ → K) where
  toFun x j := j.elim 0 x
  map_add' x y := funext fun j => by cases j <;> simp
  map_smul' a x := funext fun j => by cases j <;> simp

theorem atInfinity_injective {σ K : Type*} [Field K] :
    Function.Injective (atInfinity (σ := σ) (K := K)) :=
  fun _ _ h => funext fun j => congrFun h (some j)

theorem affineRepresentative_ne_zero {σ K : Type*} [Field K] (x : σ → K) :
    (fun j : Option σ => j.elim 1 x) ≠ 0 := by
  intro h
  exact one_ne_zero (congrFun h none)

/-- A projective level set splits into its affine chart and the projective
hypersurface defined by the leading form at infinity. -/
def deligneLevelClosure_points_equiv {σ K : Type*} [Field K] {d : ℕ}
    (hd : 0 < d) {g : MvPolynomial σ K} (hg : g.totalDegree ≤ d) (t : K) :
    projectiveHypersurfacePoints (deligneLevelClosure d g t) ≃
      {x : σ → K // g.eval x = t} ⊕ projectiveHypersurfacePoints (homogeneousComponent d g) := by
  let H := deligneLevelClosure d g t
  let Q := homogeneousComponent d g
  have hH : H.IsHomogeneous d := isHomogeneous_deligneLevelClosure d g t
  have hQ : Q.IsHomogeneous d := homogeneousComponent_isHomogeneous d g
  let e := atInfinity (σ := σ) (K := K)
  have hE := atInfinity_injective (σ := σ) (K := K)
  let affine (x : {x : σ → K // g.eval x = t}) : projectiveHypersurfacePoints H :=
    ⟨Projectivization.mk K (fun j : Option σ => j.elim 1 x.val) (affineRepresentative_ne_zero _),
      (eval_rep_mk_eq_zero_iff hH _ _).mpr (by
        change H.eval₂ (RingHom.id K) (fun j : Option σ => j.elim 1 x.val) = 0
        rw [eval₂_deligneLevelClosure_one hg]
        exact sub_eq_zero.mpr x.property)⟩
  let infinity (P : projectiveHypersurfacePoints Q) : projectiveHypersurfacePoints H :=
    ⟨Projectivization.map e hE P.val, by
      conv_lhs => rw [← Projectivization.mk_rep P.val, Projectivization.map_mk]
      apply (eval_rep_mk_eq_zero_iff hH _ _).mpr
      change H.eval₂ (RingHom.id K) (fun j : Option σ => j.elim 0 P.val.rep) = 0
      rw [eval₂_deligneLevelClosure_zero hd]
      exact P.property⟩
  refine (Equiv.ofBijective (Sum.elim affine infinity) ⟨?_, ?_⟩).symm
  · have hdisjoint (x : {x : σ → K // g.eval x = t}) (P : projectiveHypersurfacePoints Q) :
        affine x ≠ infinity P := by
      intro h
      have hp := congrArg Subtype.val h
      change Projectivization.mk K (fun j : Option σ => j.elim 1 x.val) _ =
        Projectivization.map e hE P.val at hp
      rw [← Projectivization.mk_rep P.val, Projectivization.map_mk] at hp
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hp
      have h0 := congrFun ha none
      change a * 0 = (1 : K) at h0
      exact (zero_ne_one : (0 : K) ≠ 1) (by simpa only [mul_zero] using h0)
    intro u v huv
    cases u with
    | inl x =>
      cases v with
      | inl y =>
        apply congrArg Sum.inl
        apply Subtype.ext
        have hh := congrArg Subtype.val huv
        change Projectivization.mk K (fun j : Option σ => j.elim 1 x.val) _ =
          Projectivization.mk K (fun j : Option σ => j.elim 1 y.val) _ at hh
        obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp hh
        have h0 := congrFun ha none
        change a * 1 = (1 : K) at h0
        simp only [mul_one] at h0
        funext j
        have hj := congrFun ha (some j)
        rw [h0, one_smul] at hj
        exact hj.symm
      | inr y => exact (hdisjoint x y huv).elim
    | inr x =>
      cases v with
      | inl y => exact (hdisjoint y x huv.symm).elim
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        exact Projectivization.map_injective e hE (congrArg Subtype.val huv)
  · intro P
    let v := P.val.rep
    have hv : v ≠ 0 := P.val.rep_nonzero
    have hP : H.eval v = 0 := P.property
    by_cases hz : v none = 0
    · let x := v ∘ some
      have he : e x = v := funext fun j => by
        cases j with
        | none => exact hz.symm
        | some i => rfl
      have hx : x ≠ 0 := fun h => hv (he.symm.trans (h ▸ map_zero e))
      let R : projectiveHypersurfacePoints Q :=
        ⟨Projectivization.mk K x hx, (eval_rep_mk_eq_zero_iff hQ _ _).mpr (by
          rw [← he] at hP
          change H.eval₂ (RingHom.id K) (fun j : Option σ => j.elim 0 x) = 0 at hP
          rw [eval₂_deligneLevelClosure_zero hd] at hP
          exact hP)⟩
      refine ⟨Sum.inr R, Subtype.ext ?_⟩
      change Projectivization.map e hE (Projectivization.mk K x hx) = P.val
      rw [Projectivization.map_mk]
      calc
        _ = Projectivization.mk K v hv :=
          (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨1, by rw [one_smul, he]⟩
        _ = _ := Projectivization.mk_rep _
    · let x : σ → K := fun i => (v none)⁻¹ * v (some i)
      have he : (fun j : Option σ => j.elim 1 x) = (v none)⁻¹ • v := funext fun j => by
        cases j with
        | none => exact (inv_mul_cancel₀ hz).symm
        | some i => rfl
      have hx : g.eval x = t := by
        have heval : H.eval (fun j : Option σ => j.elim 1 x) = 0 := by
          rw [he]
          change H.eval (fun j => (v none)⁻¹ * v j) = 0
          rw [eval_scale_of_homogeneous hH, hP, mul_zero]
        change H.eval₂ (RingHom.id K) (fun j : Option σ => j.elim 1 x) = 0 at heval
        rw [eval₂_deligneLevelClosure_one hg] at heval
        exact sub_eq_zero.mp heval
      refine ⟨Sum.inl ⟨x, hx⟩, Subtype.ext ?_⟩
      change Projectivization.mk K (fun j : Option σ => j.elim 1 x) _ = P.val
      calc
        _ = Projectivization.mk K v hv :=
          (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨(v none)⁻¹, he.symm⟩
        _ = _ := Projectivization.mk_rep _

/-- A renaming by a coordinate equivalence preserves the projective point set. -/
def projectiveHypersurfacePoints_rename_equiv {σ τ K : Type*} [Field K] {d : ℕ}
    {G : MvPolynomial σ K} (hG : G.IsHomogeneous d) (e : σ ≃ τ) :
    projectiveHypersurfacePoints G ≃ projectiveHypersurfacePoints (rename e G) := by
  let E := LinearEquiv.piCongrLeft' K (fun _ : σ => K) e
  let f := Projectivization.map E.toLinearMap E.injective
  have hrep (v : σ → K) (hv : v ≠ 0) :
      (rename e G).eval (f (Projectivization.mk K v hv)).rep = 0 ↔ G.eval v = 0 := by
    dsimp only [f]
    rw [Projectivization.map_mk, eval_rep_mk_eq_zero_iff hG.rename_isHomogeneous]
    change (rename e G).eval₂ (RingHom.id K) (fun j => v (e.symm j)) = 0 ↔ _
    rw [eval₂_rename]
    simp [Function.comp_def]
  have htest (P : ℙ K (σ → K)) :
      (rename e G).eval (f P).rep = 0 ↔ G.eval P.rep = 0 := by
    conv_lhs => rw [← Projectivization.mk_rep P]
    exact hrep P.rep P.rep_nonzero
  refine Equiv.ofBijective (fun P => ⟨f P.val, (htest P.val).mpr P.property⟩) ⟨?_, ?_⟩
  · exact fun P Q h => Subtype.ext (Projectivization.map_injective E.toLinearMap E.injective
      (congrArg Subtype.val h))
  · intro Q
    obtain ⟨v, hv⟩ := E.surjective Q.val.rep
    have hv₀ : v ≠ 0 := by
      intro h
      exact Q.val.rep_nonzero (by rw [← hv, h, map_zero])
    let P := Projectivization.mk K v hv₀
    have hfQ : f P = Q.val := by
      change Projectivization.map E.toLinearMap E.injective
        (Projectivization.mk K v hv₀) = Q.val
      rw [Projectivization.map_mk]
      exact ((Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr
        ⟨1, by
          change (1 : K) • Q.val.rep = E v
          rw [one_smul]
          exact hv.symm⟩).trans (Projectivization.mk_rep Q.val)
    refine ⟨⟨P, (htest P).mp ?_⟩, Subtype.ext hfQ⟩
    rw [hfQ]
    exact Q.property

end
end Birch
