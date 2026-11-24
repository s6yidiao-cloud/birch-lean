import Birch.DilatedDifference
import Birch.CompleteBounds
import Birch.MajorPoissonTail
import Birch.CompletionConditional
import Birch.MaximalDirectionStratum
import Birch.PrimeCompleteDifferencing
import Mathlib.FieldTheory.Finiteness

/-!
# Quadratic complete sums

The quadratic terminal estimate follows from character orthogonality and
one differencing step. Lower-degree terms are allowed.
-/

namespace Birch

open MvPolynomial ZMod
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

variable {n p : ℕ}

private theorem evalForm_dilatedDifference_one {R : Type*} [CommRing R]
    (F : IntForm n) (u : Fin n → ℤ) (x : Fin n → R) :
    evalForm (dilatedDifference 1 u F) x =
      evalForm F (fun i => x i + (u i : R)) - evalForm F x := by
  let E := eval₂Hom (Int.castRingHom R) x
  have hh := congrArg E (mul_dilatedDifference 1 u F)
  simp only [map_sub, map_one, one_mul, E, coe_eval₂Hom] at hh
  unfold evalForm
  rw [hh, aeval_def, algebraMap_eq, ← eval₂_assoc]
  simp only [eval₂_add, eval₂_X, eval₂_C, Int.coe_castRingHom]

private theorem homogeneousComponents_affine (G : IntForm n) (hG : G.totalDegree ≤ 1) :
    G = homogeneousComponent 0 G + homogeneousComponent 1 G := by
  have hs := sum_homogeneousComponent G
  by_cases h₀ : G.totalDegree = 0
  · simp only [h₀, zero_add, Finset.sum_range_one] at hs
    rw [homogeneousComponent_eq_zero _ _ (by omega : G.totalDegree < 1), add_zero]
    exact hs.symm
  · have h₁ : G.totalDegree = 1 := by omega
    rw [h₁] at hs
    rw [Finset.sum_range_succ, Finset.sum_range_one] at hs
    exact hs.symm

private theorem evalForm_directionalDerivative {R : Type*} [CommRing R]
    (G : IntForm n) (u : Fin n → ℤ) (h : Fin n → R) :
    evalForm (directionalDerivative u G) h =
      ∑ i, (u i : R) * evalForm (pderiv i G) h := by
  unfold directionalDerivative evalForm
  simp only [eval₂_sum, eval₂_mul, eval₂_C, Int.coe_castRingHom]

private theorem evalForm_affine_sub_at_zero {R : Type*} [CommRing R]
    (G : IntForm n) (hG : G.totalDegree ≤ 1) (h : Fin n → R) :
    evalForm G h - evalForm G (0 : Fin n → R) = evalForm (homogeneousComponent 1 G) h := by
  have hhom := homogeneousComponent_isHomogeneous 1 G
  have hz : evalForm (homogeneousComponent 1 G) (0 : Fin n → R) = 0 := by
    have hh := evalForm_scale hhom (0 : R) (0 : Fin n → R)
    change evalForm (homogeneousComponent 1 G) (fun _ => 0) = 0
    simpa only [zero_mul, pow_one] using hh
  have hE (v : Fin n → R) :
      evalForm G v = ((coeff 0 G : ℤ) : R) + evalForm (homogeneousComponent 1 G) v := by
    have H := congrArg (fun U : IntForm n => evalForm U v) (homogeneousComponents_affine G hG)
    rw [homogeneousComponent_zero] at H
    unfold evalForm at H ⊢
    rw [eval₂_add, eval₂_C] at H
    exact H
  rw [hE h, hE 0, hz, add_zero, add_sub_cancel_left]

/-- Mixed differences of a polynomial of degree at most two depend precisely
on the gradient of its quadratic homogeneous component. -/
theorem quadratic_residue_mixedDifference [NeZero p]
    (F : IntForm n) (hF : F.totalDegree ≤ 2) (x h : Fin n → ZMod p) :
    residueEval F p (x+h) - residueEval F p x =
      residueEval F p h - residueEval F p 0 +
        ∑ i, x i * residueEval (pderiv i (homogeneousComponent 2 F)) p h := by
  let u : Fin n → ℤ := fun i => (x i).val
  let G := dilatedDifference 1 u F
  have hu (i : Fin n) : (u i : ZMod p) = x i := by
    simp only [u, Int.cast_natCast, ZMod.natCast_zmod_val]
  have he (y : Fin n → ZMod p) : evalForm G y = evalForm F (y+x) - evalForm F y := by
    rw [show G = dilatedDifference 1 u F from rfl, evalForm_dilatedDifference_one]
    simp only [hu]
    rfl
  have hG : G.totalDegree ≤ 1 := (dilatedDifference_totalDegree_le 1 u F).trans (by omega)
  have hlin : homogeneousComponent 1 G = directionalDerivative u (homogeneousComponent 2 F) :=
    homogeneousComponent_dilatedDifference 1 u F (d := 2) le_rfl hF
  have hD := evalForm_affine_sub_at_zero G hG h
  rw [hlin, evalForm_directionalDerivative, he, he, zero_add] at hD
  simp only [hu] at hD
  change evalForm F (x+h) - evalForm F x =
    evalForm F h - evalForm F 0 + ∑ i, x i * evalForm (pderiv i (homogeneousComponent 2 F)) h
  rw [← hD, add_comm h x]
  ring

private theorem stdAddChar_conjugate [NeZero p] (c : ZMod p) :
    conj (stdAddChar c) = stdAddChar (-c) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

private theorem sum_stdAddChar_linear_eq_zero [NeZero p] (g : Fin n → ZMod p)
    (hg : g ≠ 0) : (∑ x : Fin n → ZMod p, stdAddChar (∑ i, x i * g i)) = 0 := by
  classical
  let ψ : AddChar (Fin n → ZMod p) ℂ :=
    { toFun := fun x => stdAddChar (∑ i, x i * g i)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := by
        intro x y
        simp [Pi.add_apply, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul] }
  change (∑ x, ψ x) = 0
  apply AddChar.sum_eq_zero_of_ne_one
  intro hψ
  have hg' : ∃ i, g i ≠ 0 := by
    by_contra! h
    exact hg (funext h)
  obtain ⟨i, hi⟩ := hg'
  have hsingle : ψ (Pi.single i 1) = stdAddChar (g i) := by
    change stdAddChar (∑ j, Pi.single i 1 j * g j) = _
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have hc := congrArg (fun χ : AddChar (Fin n → ZMod p) ℂ => χ (Pi.single i 1)) hψ
  rw [hsingle, AddChar.one_apply] at hc
  exact hi (ZMod.injective_stdAddChar (hc.trans (AddChar.map_zero_eq_one _).symm))

private theorem sum_stdAddChar_quadratic_mixed_eq_zero [Fact p.Prime] [NeZero p]
    (F : IntForm n) (hF : F.totalDegree ≤ 2) (a : ZMod p) (ha : a ≠ 0)
    (h : Fin n → ZMod p)
    (hh : ¬ ∀ i, residueEval (pderiv i (homogeneousComponent 2 F)) p h = 0) :
    (∑ x : Fin n → ZMod p,
      stdAddChar (a * (residueEval F p (h + x) - residueEval F p x))) = 0 := by
  let g (i : Fin n) := a * residueEval (pderiv i (homogeneousComponent 2 F)) p h
  have hg : g ≠ 0 := by
    intro heq
    apply hh
    intro i
    have hc : g i = 0 := congrFun heq i
    exact (mul_eq_zero.mp hc).resolve_left ha
  have hchar (x : Fin n → ZMod p) :
      stdAddChar (a * (residueEval F p (h + x) - residueEval F p x)) =
        stdAddChar (a * (residueEval F p h - residueEval F p 0)) *
          stdAddChar (∑ i, x i * g i) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    rw [add_comm h x, quadratic_residue_mixedDifference F hF, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold g
    ring
  simp_rw [hchar, ← Finset.mul_sum]
  rw [sum_stdAddChar_linear_eq_zero g hg, mul_zero]

private theorem sum_stdAddChar_quadratic_correlation [Fact p.Prime] [NeZero p]
    (F : IntForm n) (hF : F.totalDegree ≤ 2)
    (hs : ∀ h : Fin n → ZMod p,
      (∀ i, residueEval (pderiv i (homogeneousComponent 2 F)) p h = 0) → h = 0)
    (a : ZMod p) (ha : a ≠ 0) :
    let Z := ∑ x : Fin n → ZMod p, stdAddChar (a * residueEval F p x)
    Z * conj Z = (p : ℂ)^n := by
  classical
  let V := Fin n → ZMod p
  let W (x : V) := residueEval F p x
  let e : V × V ≃ V × V :=
    { toFun := fun z => (z.1 + z.2, z.2)
      invFun := fun z => (z.1 - z.2, z.2)
      left_inv := by intro z; simp
      right_inv := by intro z; simp }
  let H (z : V × V) := stdAddChar (a * (W z.1 - W z.2))
  have hsquare :
      (∑ x : V, stdAddChar (a * W x)) * conj (∑ y : V, stdAddChar (a * W y)) =
        ∑ h : V, ∑ x : V, stdAddChar (a * (W (h+x) - W x)) := by
    rw [map_sum, Finset.sum_mul_sum]
    simp_rw [stdAddChar_conjugate, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
    change (∑ x : V, ∑ y : V, H (x,y)) = ∑ h : V, ∑ x : V, H (e (h,x))
    calc
      _ = ∑ z : V × V, H z := (Fintype.sum_prod_type H).symm
      _ = ∑ z : V × V, H (e z) := (Equiv.sum_comp e H).symm
      _ = _ := Fintype.sum_prod_type (fun z : V × V => H (e z))
  change (∑ x : V, stdAddChar (a * W x)) * conj (∑ x : V, stdAddChar (a * W x)) = _
  rw [hsquare, Finset.sum_eq_single 0]
  · simp
    change (↑(Fintype.card (Fin n → ZMod p)) : ℂ) = (p : ℂ)^n
    simp [ZMod.card]
  · intro h _ hh
    exact sum_stdAddChar_quadratic_mixed_eq_zero F hF a ha h (fun hg => hh (hs h hg))
  · simp

/-- The quadratic terminal estimate with arbitrary lower terms, in the
normalized convention of the paper. -/
theorem norm_completeSum_quadratic [Fact p.Prime] [NeZero p]
    (F : IntForm n) (hF : F.totalDegree ≤ 2)
    (hs : ∀ h : Fin n → ZMod p,
      (∀ i, residueEval (pderiv i (homogeneousComponent 2 F)) p h = 0) → h = 0)
    (a : ZMod p) (ha : a ≠ 0) :
    ‖completeSum F p a‖ = (p : ℝ)^(-(n : ℝ) / 2) := by
  let Z := ∑ x : Fin n → ZMod p, stdAddChar (a * residueEval F p x)
  have hsquare := sum_stdAddChar_quadratic_correlation F hF hs a ha
  change Z * conj Z = (p : ℂ)^n at hsquare
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    Complex.ofReal_inj] at hsquare
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hnorm : ‖Z‖ = (p : ℝ)^((n : ℝ)/2) := by
    have hb : 0 ≤ (p : ℝ)^((n : ℝ)/2) := by positivity
    rw [← abs_of_nonneg (norm_nonneg Z), ← abs_of_nonneg hb, ← sq_eq_sq_iff_abs_eq_abs]
    rw [hsquare, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hp.le]
    norm_num
  change ‖((p : ℂ)^n)⁻¹ * Z‖ = _
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, hnorm,
    ← Real.rpow_natCast, ← Real.rpow_neg hp.le, ← Real.rpow_add hp]
  congr 1
  ring

private theorem evalForm_homogeneous_one {R : Type*} [CommRing R] (G : IntForm n)
    (hG : G.IsHomogeneous 1) (x : Fin n → R) :
    evalForm G x = ∑ j, ((G.coeff (Finsupp.single j 1) : ℤ) : R) * x j := by
  classical
  have hdecomp : G = ∑ j, C (G.coeff (Finsupp.single j 1)) * X j := by
    ext m
    simp only [C_mul_X_eq_monomial, coeff_sum, coeff_monomial]
    by_cases hm : ∃ j : Fin n, m = Finsupp.single j 1
    · obtain ⟨j, rfl⟩ := hm
      simp [Finsupp.single_left_inj Nat.one_ne_zero]
    · have hzero : G.coeff m = 0 := by
        by_contra hne
        have hd : m.degree = 1 := by
          simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hG hne
        have hmem : m ∈ Set.range (fun j : Fin n => Finsupp.single j 1) := by
          rw [Finsupp.range_single_one]
          exact hd
        exact hm (by simpa only [Set.mem_range, eq_comm] using hmem)
      rw [hzero, Finset.sum_eq_zero]
      intro j _
      exact if_neg fun hj => hm ⟨j, hj.symm⟩
  conv_lhs => rw [hdecomp]
  simp only [evalForm, eval₂_sum, eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom]

/-- The gradient kernel of a quadratic form of geometric gradient dimension `s`
contains at most `p^s` residue vectors. -/
theorem card_quadratic_gradient_locus_le [Fact p.Prime] [NeZero p] (Q : IntForm n)
    (hQ : Q.IsHomogeneous 2) {s : ℕ} (hs : PrimeGradientDimension p Fact.out Q s) :
    (Finset.univ.filter fun h : Fin n → ZMod p => ∀ i, residueEval (pderiv i Q) p h = 0).card ≤
      p ^ s := by
  classical
  let K := AlgebraicClosure (ZMod p)
  let φ : ZMod p →+* K := algebraMap (ZMod p) K
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => (pderiv i Q).coeff (Finsupp.single j 1)
  let M₀ : Matrix (Fin n) (Fin n) (ZMod p) := M.map (Int.castRingHom _)
  let M₁ : Matrix (Fin n) (Fin n) K := M₀.map φ
  have hM₁ : M₁ = M.map (Int.castRingHom K) := by
    ext i j
    simp [M₁, M₀, φ]
  have heval {R : Type} [CommRing R] (x : Fin n → R) (i : Fin n) :
      ((M.map (Int.castRingHom R)) *ᵥ x) i = evalForm (pderiv i Q) x := by
    exact (evalForm_homogeneous_one _ hQ.pderiv x).symm
  let W := LinearMap.ker M₀.mulVecLin
  let l := Module.finrank (ZMod p) W
  let b := (Module.finBasis (ZMod p) W).equivFun
  let E : (Fin l → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) := W.subtype.comp b.symm.toLinearMap
  have hE : LinearMap.ker E = ⊥ :=
    LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp b.symm.injective)
  let U := LinearMap.toMatrix' E
  let V := LinearMap.toMatrix' E.leftInverse
  have hVU : V * U = 1 := by
    rw [← LinearMap.toMatrix'_comp, E.leftInverse_comp_of_inj hE, LinearMap.toMatrix'_id]
  have hMU : M₀ * U = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_zero]
    exact LinearMap.ext fun x => (b.symm x).property
  let E₁ : (Fin l → K) →ₗ[K] (Fin n → K) := (U.map φ).mulVecLin
  have hinj : Function.Injective E₁ := by
    refine Function.LeftInverse.injective (g := (V.map φ).mulVecLin) ?_
    intro x
    change V.map φ *ᵥ (U.map φ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hVU]
    rw [Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
  let Q₁ := MvPolynomial.map (Int.castRingHom K) Q
  have hW (x : Fin n → K) (hx : x ∈ LinearMap.range E₁) (i : Fin n) :
      eval x (pderiv i Q₁) = 0 := by
    obtain ⟨y, rfl⟩ := hx
    rw [show pderiv i Q₁ = MvPolynomial.map (Int.castRingHom K) (pderiv i Q) from pderiv_map,
      eval_map]
    change evalForm (pderiv i Q) (E₁ y) = 0
    rw [← heval (E₁ y) i, ← hM₁]
    change (M₀.map φ *ᵥ (U.map φ *ᵥ y)) i = 0
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hMU]
    simp
  have hd := finrank_le_gradientDimension_of_subspace Q₁ (LinearMap.range E₁) hW
  have hrank : Module.finrank K (LinearMap.range E₁) = l := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hgrad : (fun i : Fin n => pderiv i Q₁) =
      fun i => MvPolynomial.map (Int.castRingHom K) (pderiv i Q) :=
    funext fun _ => pderiv_map
  have hd' : (l : WithBot ℕ∞) ≤ (s : ℕ∞) := by
    rw [hrank, hgrad] at hd
    exact hd.trans_eq hs
  have hl : l ≤ s := by exact_mod_cast hd'
  have heq (x : Fin n → ZMod p) : x ∈ W ↔ ∀ i, residueEval (pderiv i Q) p x = 0 := by
    change M₀ *ᵥ x = 0 ↔ _
    rw [_root_.funext_iff]
    simp only [M₀, heval, Pi.zero_apply, residueEval, evalForm]
  have hcard :
      (Finset.univ.filter fun h : Fin n → ZMod p => ∀ i, residueEval (pderiv i Q) p h = 0).card =
        p ^ l := by
    simp_rw [← heq, ← Fintype.card_subtype]
    rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  rw [hcard]
  exact Nat.pow_le_pow_right (NeZero.pos p) hl

/-- The complete-sum estimate for a quadratic polynomial, with the exponent
given by the codimension of the gradient locus of its quadratic part. -/
theorem norm_completeSum_quadratic_of_primeGradientDimension [Fact p.Prime] [NeZero p]
    (F : IntForm n) (hF : F.totalDegree ≤ 2) {s : ℕ}
    (hs : PrimeGradientDimension p Fact.out (homogeneousComponent 2 F) s)
    (a : ZMod p) (ha : a ≠ 0) :
    ‖completeSum F p a‖ ≤ (p : ℝ) ^ (-((n : ℝ) - s) / 2) := by
  classical
  let Q := homogeneousComponent 2 F
  let S : Finset (Fin n → ZMod p) := Finset.univ.filter fun h =>
    ∀ i, residueEval (pderiv i Q) p h = 0
  let B (h : Fin n → ZMod p) := completeSum (dilatedDifference 1 (residueVectorIntRep h) F) p a
  have hS : S.card ≤ p ^ s := card_quadratic_gradient_locus_le Q (homogeneousComponent_isHomogeneous 2 F) hs
  have hcancel (h : Fin n → ZMod p) (hh : h ∉ S) : B h = 0 := by
    unfold B completeSum
    simp_rw [residueEval_dilatedDifference_one, add_comm _ h]
    have hz := sum_stdAddChar_quadratic_mixed_eq_zero F hF a ha h
      (by simpa [S, Q] using hh)
    rw [hz, mul_zero]
  have hsum : (∑ h, ‖B h‖) ≤ (p : ℝ)^s := calc
    _ = ∑ h ∈ S, ‖B h‖ := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro h _ hh
      rw [hcancel h hh, norm_zero]
    _ ≤ ∑ _ ∈ S, (1 : ℝ) := Finset.sum_le_sum fun h _ => norm_completeSum_le_one _ a
    _ = S.card := by simp
    _ ≤ _ := by exact_mod_cast hS
  have hbound : ‖completeSum F p a‖ ^ 2 ≤ ((p : ℝ)^n)⁻¹ * (p : ℝ)^s :=
    (norm_completeSum_sq_le_average_dilatedDifference F a).trans
      (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hpow : ((p : ℝ)^n)⁻¹ * (p : ℝ)^s = ((p : ℝ)^(-((n : ℝ) - s) / 2)) ^ 2 := by
    rw [← Real.rpow_natCast _ n, ← Real.rpow_neg hp.le, ← Real.rpow_natCast _ s,
      ← Real.rpow_natCast _ 2, ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
    congr 1
    ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hbound.trans_eq hpow)

private theorem residue_gradient_zero_of_geometric [Fact p.Prime]
    (Q : IntForm n)
    (hs : ∀ x : Fin n → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i Q) x = 0) → x = 0)
    (h : Fin n → ZMod p) (hh : ∀ i, residueEval (pderiv i Q) p h = 0) : h = 0 := by
  let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  let x : Fin n → AlgebraicClosure (ZMod p) := fun i => φ (h i)
  have hmap (G : IntForm n) : φ (residueEval G p h) = evalForm G x := by
    unfold residueEval evalForm x
    rw [MvPolynomial.hom_eval₂]
    congr 1
  have hx : x = 0 := hs x (fun i => by rw [← hmap, hh, map_zero])
  funext i
  apply φ.injective
  simpa only [Pi.zero_apply, map_zero] using congrFun hx i

/-- The degree-two terminal estimate, including every linear Fourier twist.
Geometric smoothness of the top quadratic form is sufficient. -/
theorem norm_twistedCompleteSum_quadratic [Fact p.Prime] [NeZero p]
    (F : IntForm n) (hF : F.totalDegree ≤ 2)
    (hs : ∀ h : Fin n → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i (homogeneousComponent 2 F)) h = 0) → h = 0)
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) (m : Fin n → ℤ) :
    ‖twistedCompleteSum F p a m‖ = (p : ℝ)^(-(n : ℝ) / 2) := by
  let L : IntForm n := ∑ i, C (m i) * X i
  let G : IntForm n := C a * F + L
  have hL : L.totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
  have hA : (C a * F).totalDegree ≤ 2 :=
    (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hF)
  have hG : G.totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le hA (hL.trans (by decide)))
  have htop : homogeneousComponent 2 G = C a * homogeneousComponent 2 F := by
    unfold G
    rw [map_add, homogeneousComponent_C_mul, homogeneousComponent_eq_zero 2 L (by omega), add_zero]
  have hg (h : Fin n → ZMod p)
      (hh : ∀ i, residueEval (pderiv i (homogeneousComponent 2 G)) p h = 0) : h = 0 := by
    apply residue_gradient_zero_of_geometric _ hs h
    intro i
    have hz := hh i
    rw [htop, pderiv_C_mul] at hz
    have hmul : (a : ZMod p) * residueEval (pderiv i (homogeneousComponent 2 F)) p h = 0 := by
      simpa only [residueEval, eval₂_mul, eval₂_C, Int.coe_castRingHom] using hz
    exact (mul_eq_zero.mp hmul).resolve_left ha
  exact norm_completeSum_quadratic G hG hg 1 one_ne_zero

/-- The conductor-one Deligne interface holds unconditionally for homogeneous
quadratic forms by the elementary character argument. -/
theorem deligneConductorOne_quadratic (F : IntForm n) (hF : F.IsHomogeneous 2) :
    DeligneConductorOne 2 F := by
  intro p hp hp₀ _ hs a ha
  letI : Fact p.Prime := hp
  have hFdeg : F.totalDegree ≤ 2 := hF.totalDegree_le
  have hg (x : Fin n → ZMod p)
      (hx : ∀ i, residueEval (pderiv i (homogeneousComponent 2 F)) p x = 0) : x = 0 := by
    rw [homogeneousComponent_eq_self hF] at hx
    exact residue_gradient_zero_of_geometric F (fun y hy => (hs y).mp hy) x hx
  rw [norm_completeSum_quadratic F hFdeg hg a ha]
  norm_num

end

end Birch
