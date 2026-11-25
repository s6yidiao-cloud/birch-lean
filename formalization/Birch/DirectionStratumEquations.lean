import Birch.MvPolynomialCoefficientCompat
import Birch.BoundedMacaulayCuts
import Birch.DirectionFiberDimension

/-! # Homogeneous equations for direction strata -/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

variable {K : Type} [Field K] {n : ℕ}

/-- The gradient of a directional derivative, with direction coordinates
as parameters. -/
def parameterGradientSystem (G : MvPolynomial (Fin n) K) (i : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (Fin n) K) :=
  ∑ j, C (X j) * MvPolynomial.map C (pderiv i (pderiv j G))

private theorem parameterGradientSystem_eval {L : Type} [Field L] [Algebra K L]
    (G : MvPolynomial (Fin n) K) (u : Fin n → L) (i : Fin n) :
    MvPolynomial.map (aeval u).toRingHom (parameterGradientSystem G i) =
      pderiv i (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G)) := by
  have hcomp : (aeval u).toRingHom.comp (C : K →+* MvPolynomial (Fin n) K) =
      algebraMap K L := by
    ext t
    exact aeval_C u t
  simp only [AlgHom.toRingHom_eq_coe] at hcomp
  simp only [parameterGradientSystem, directionalDerivativeOver, map_sum, map_mul, map_C,
    aeval_X, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.map_map, hcomp,
    pderiv_map, pderiv_C_mul]

set_option maxHeartbeats 650000 in
private theorem parameterGradientSystem_coeff_homogeneous
    (G : MvPolynomial (Fin n) K) (i : Fin n) (b : Fin n →₀ ℕ) :
    (AddMonoidAlgebra.coeff (parameterGradientSystem G i) b).IsHomogeneous 1 := by
  simp only [parameterGradientSystem, coeff_sum, coeff_C_mul, coeff_map]
  apply IsHomogeneous.sum
  intro j _
  rw [mul_comm]
  exact isHomogeneous_C_mul_X _ j

/-- The finite tests on each direction chart consist of the bounded integer
linear cuts and the maximal minors of the Macaulay matrix. -/
abbrev DirectionTestIndex (n k e D B : ℕ) :=
  Fin n × (Fin k → Fin n → Fin (B+1)) ×
    (DegreeMonomial n D → Fin (n+k) × DegreeMonomial n (D-e))

/-- Cut tests are homogenized in the direction coordinate of the chosen chart. -/
def directionTest (G : MvPolynomial (Fin n) K) {k e D B : ℕ}
    (a : DirectionTestIndex n k e D B) : MvPolynomial (Fin n) K :=
  ((systemMacaulayMatrix
    (cutPolynomialSystem (parameterGradientSystem G) (X a.1)
      (fun j i => C ((a.2.1 j i).val : K)) e) e D).submatrix id a.2.2).det

set_option maxHeartbeats 850000 in
theorem directionTest_isHomogeneous (G : MvPolynomial (Fin n) K) {k e D B : ℕ}
    (a : DirectionTestIndex n k e D B) :
    (directionTest G a).IsHomogeneous (Fintype.card (DegreeMonomial n D)) := by
  classical
  let R := MvPolynomial (Fin n) K
  let l (j : Fin k) (i : Fin n) : K := (a.2.1 j i).val
  let g := cutPolynomialSystem (parameterGradientSystem G) (X a.1) (fun j i => C (l j i)) e
  have hg (j : Fin (n+k)) (b : Fin n →₀ ℕ) :
      (AddMonoidAlgebra.coeff (g j) b).IsHomogeneous 1 := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [g, cutPolynomialSystem, Fin.append_left] using
        parameterGradientSystem_coeff_homogeneous G i b
    · have hl : normalLinearForm (fun i' => C (l i i')) =
          MvPolynomial.map (C : K →+* R) (normalLinearForm (l i)) := by
        rw [normalLinearForm_map]
        rfl
      simp only [g, cutPolynomialSystem, Fin.append_right, coeff_C_mul, hl, ← map_pow, coeff_map]
      rw [mul_comm]
      exact isHomogeneous_C_mul_X _ _
  let A := (systemMacaulayMatrix g e D).submatrix id a.2.2
  have hA (i j : DegreeMonomial n D) : (A i j).IsHomogeneous 1 := by
    change (AddMonoidAlgebra.coeff
      (monomial (a.2.2 j).2.val 1 * g (a.2.2 j).1) i.val).IsHomogeneous 1
    rw [coeff_monomial_mul', one_mul]
    split_ifs
    · exact hg _ _
    · exact isHomogeneous_zero _ _ _
  change A.det.IsHomogeneous _
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro perm _
  have hprod := IsHomogeneous.prod Finset.univ (fun i => A (perm i) i)
    (fun _ => 1) (fun i _ => hA _ _)
  have hs := hprod.C_mul ((Equiv.Perm.sign perm : ℤ) : K)
  rw [map_intCast] at hs
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] using hs

theorem aeval_directionTest {L : Type} [Field L] [Algebra K L]
    (G : MvPolynomial (Fin n) K) {k e D B : ℕ}
    (a : DirectionTestIndex n k e D B) (u : Fin n → L) :
    aeval u (directionTest G a) =
      ((systemMacaulayMatrix
        (cutPolynomialSystem
          (fun i => pderiv i (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G)))
          (u a.1) (fun j i => ((a.2.1 j i).val : L)) e) e D).submatrix id a.2.2).det := by
  change (aeval u).toRingHom (directionTest G a) = _
  unfold directionTest
  rw [map_cutPolynomialSystem_macaulayMinor]
  have ha (j : Fin k) :
      (aeval u).toRingHom ∘ (fun i : Fin n => C ((a.2.1 j i).val : K)) =
        fun i => ((a.2.1 j i).val : L) := by
    funext i
    change aeval u (C ((a.2.1 j i).val : K)) = _
    rw [aeval_C, map_natCast]
  have hX : (aeval (R := K) u).toRingHom (X a.1) = u a.1 := aeval_X u a.1
  simp only [parameterGradientSystem_eval, ha, hX]

private theorem directionGradient_isHomogeneous {L : Type} [Field L] [Algebra K L]
    {G : MvPolynomial (Fin n) K} {r : ℕ} (hG : G.IsHomogeneous r)
    (u : Fin n → L) (i : Fin n) :
    (pderiv i (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G))).IsHomogeneous
      (r-2) := by
  have h : (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G)).IsHomogeneous
      (r-1) := by
    apply IsHomogeneous.sum
    intro j _
    exact ((hG.map (algebraMap K L)).pderiv (i := j)).C_mul _
  simpa only [Nat.sub_sub] using h.pderiv (i := i)

set_option maxHeartbeats 650000 in
/-- Over every algebraically closed extension, the tests vanish exactly when
the gradient fiber has dimension at least `k+1`. -/
theorem directionTests_zero_iff {L : Type} [Field L] [Algebra K L] [IsAlgClosed L]
    {p r k D : ℕ} [Fact p.Prime] [CharP L p]
    {G : MvPolynomial (Fin n) K} (hG : G.IsHomogeneous r)
    (hr : 2 < r) (hk : k < n) (hD : r-2 < D)
    (hp : (r-2) * Fintype.card (DegreeMonomial n D) < p)
    (hcert : ∀ g : Fin (n+k) → MvPolynomial (Fin n) L, (∀ i, (g i).IsHomogeneous (r-2)) →
      (∀ x : Fin n → L, (∀ j, (g j).eval x = 0) → x = 0) →
      ∃ sel : DegreeMonomial n D → Fin (n+k) × DegreeMonomial n (D-(r-2)),
        ((systemMacaulayMatrix g (r-2) D).submatrix id sel).det ≠ 0)
    (u : Fin n → L) :
    (∀ a : DirectionTestIndex n k (r-2) D ((r-2) * Fintype.card (DegreeMonomial n D)),
      aeval u (directionTest G a) = 0) ↔
      ((k+1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) L ⧸
        Ideal.span (Set.range fun i : Fin n => pderiv i
          (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G)))) := by
  let f (i : Fin n) := pderiv i (directionalDerivativeOver u (MvPolynomial.map (algebraMap K L) G))
  let I := Ideal.span (Set.range f)
  let B := (r-2) * Fintype.card (DegreeMonomial n D)
  let i₀ : Fin n := ⟨0, by omega⟩
  have he : 0 < r-2 := by omega
  have hf : ∀ i, (f i).IsHomogeneous (r-2) := directionGradient_isHomogeneous hG u
  change (∀ a : DirectionTestIndex n k (r-2) D B, aeval u (directionTest G a) = 0) ↔
    ((k+1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) L ⧸ I)
  constructor
  · intro h
    by_contra! hdim
    have hd := ENat.WithBot.lt_add_one_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hdim)
    change ringKrullDim (MvPolynomial (Fin n) L ⧸ I) ≤ (k : WithBot ℕ∞) at hd
    have hu : u ≠ 0 := by
      intro hu
      have hI : I = ⊥ := by
        unfold I
        apply le_antisymm _ bot_le
        apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        simp [f, hu, directionalDerivativeOver]
      rw [hI, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hd
      have hn : ringKrullDim (MvPolynomial (Fin n) L) = (n : WithBot ℕ∞) := by
        simp
      rw [hn] at hd
      exact (not_le_of_gt hk) (by exact_mod_cast hd)
    obtain ⟨i,hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra! hh
      exact hu (funext hh)
    obtain ⟨a,ha,sel,hsel⟩ := exists_bounded_macaulay_cuts i₀ he hp f hf hd hi hcert
    let a' (j : Fin k) (i : Fin n) : Fin (B+1) := ⟨a j i, Nat.lt_succ_of_le (ha j i)⟩
    have H := h ⟨i,a',sel⟩
    rw [aeval_directionTest] at H
    exact hsel H
  · intro hdim a
    rw [aeval_directionTest]
    by_contra! hsel
    let l (j : Fin k) (i : Fin n) : L := (a.2.1 j i).val
    have hzero (x : Fin n → L) (hx : ∀ i, (f i).eval x = 0)
        (hl : ∀ j, (normalLinearForm (l j)).eval x = 0) : x = 0 := by
      apply zero_of_system_macaulay_minor
        (cutPolynomialSystem_isHomogeneous f (u a.1) l hf) (by omega) (by omega)
        a.2.2 hsel x
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [cutPolynomialSystem, Fin.append_left] using hx i
      · simp only [cutPolynomialSystem, Fin.append_right, eval_mul, eval_C, eval_pow, hl,
          zero_pow he.ne', mul_zero]
    have hle := (homogeneousSystem_dim_le_iff_linear_cuts i₀ f he hf).mpr ⟨l,hzero⟩
    have hbad := hdim.trans hle
    exact (Nat.not_succ_le_self k) (by exact_mod_cast hbad)

end
end Birch
