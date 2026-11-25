import Birch.HessianCoordinateRing
import Birch.WeylLinearBox
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# The maximal-dimensional bad-direction stratum

When a directional derivative has full-dimensional gradient locus, its
gradient is identically zero. In the manuscript's characteristic range Euler's
identity then makes the directional derivative zero. Such directions form a
linear kernel lying in the original gradient locus.
-/

open MvPolynomial Matrix Module
open scoped BigOperators Matrix nonZeroDivisors

namespace Birch

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

private def fieldLinearSection {l : ℕ} (U : Matrix (Fin n) (Fin l) K) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin l) K :=
  aeval fun i => ∑ j, C (U i j) * X j

private theorem aeval_fieldLinearSection {l : ℕ} (U : Matrix (Fin n) (Fin l) K)
    (x : Fin l → K) (G : MvPolynomial (Fin n) K) :
    aeval x (fieldLinearSection U G) = aeval (U *ᵥ x) G := by
  have hcomp : (aeval x).comp (fieldLinearSection U) = aeval (U *ᵥ x) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [fieldLinearSection, Matrix.mulVec, dotProduct]
  exact DFunLike.congr_fun hcomp G

private theorem eval_fieldLinearSection {l : ℕ} (U : Matrix (Fin n) (Fin l) K)
    (x : Fin l → K) (G : MvPolynomial (Fin n) K) :
    eval x (fieldLinearSection U G) = eval (U *ᵥ x) G :=
  aeval_fieldLinearSection U x G

/-- The dimension of a linear subspace contained in an affine gradient locus
is bounded by the Krull dimension of the corresponding gradient ring. -/
theorem finrank_le_gradientDimension_of_subspace [Infinite K] (G : MvPolynomial (Fin n) K)
    (W : Submodule K (Fin n → K)) (hW : ∀ u ∈ W, ∀ i, eval u (pderiv i G) = 0) :
    finrank K W ≤ ringKrullDim
      (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i => pderiv i G)) := by
  let l := finrank K W
  let E : (Fin l → K) →ₗ[K] (Fin n → K) :=
    W.subtype.comp (Module.finBasis K W).equivFun.symm.toLinearMap
  have hE : LinearMap.ker E = ⊥ := LinearMap.ker_eq_bot.mpr
    (Subtype.val_injective.comp (Module.finBasis K W).equivFun.symm.injective)
  let U := LinearMap.toMatrix' E
  let V := LinearMap.toMatrix' E.leftInverse
  let R := MvPolynomial (Fin n) K
  let R₀ := MvPolynomial (Fin l) K
  let φ : R →ₐ[K] R₀ := fieldLinearSection U
  let ψ : R₀ →ₐ[K] R := fieldLinearSection V
  have hInv : φ.comp ψ = AlgHom.id K R₀ := by
    apply MvPolynomial.algHom_ext
    intro i
    apply MvPolynomial.funext
    intro x
    change eval x (fieldLinearSection U (fieldLinearSection V (X i))) = eval x (X i)
    rw [eval_fieldLinearSection, eval_fieldLinearSection, show U *ᵥ x = E x
      from LinearMap.toMatrix'_mulVec _ _, show V *ᵥ E x = E.leftInverse (E x)
      from LinearMap.toMatrix'_mulVec _ _, LinearMap.leftInverse_apply_of_inj hE]
  have hφ : Function.Surjective φ := fun z => ⟨ψ z, DFunLike.congr_fun hInv z⟩
  let J : Ideal R := Ideal.span (Set.range fun i => pderiv i G)
  have hJ : J ≤ RingHom.ker φ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply RingHom.mem_ker.mpr
    apply MvPolynomial.funext
    intro x
    change eval x (fieldLinearSection U (pderiv i G)) = eval x 0
    rw [eval_fieldLinearSection, show U *ᵥ x = E x from LinearMap.toMatrix'_mulVec _ _, map_zero]
    exact hW (E x) ((Module.finBasis K W).equivFun.symm x).property i
  let f : R ⧸ J →+* R₀ := Ideal.Quotient.lift J φ.toRingHom fun _ hg =>
    RingHom.mem_ker.mp (hJ hg)
  have hf : Function.Surjective f := Ideal.Quotient.lift_surjective_of_surjective J _ hφ
  have hb := ringKrullDim_le_of_surjective f hf
  simpa [R₀, R, J, l, ringKrullDim_eq_zero_of_field K] using hb

private theorem pderiv_eq_zero_of_full_gradientDimension (G : MvPolynomial (Fin n) K)
    (hdim : (n : ℕ∞) ≤ ringKrullDim
      (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i => pderiv i G))) (i : Fin n) :
    pderiv i G = 0 := by
  by_contra hi
  let I := Ideal.span ({pderiv i G} : Set (MvPolynomial (Fin n) K))
  let J := Ideal.span (Set.range fun j => pderiv j G)
  have hIJ : I ≤ J := Ideal.span_le.mpr
    (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst x; exact Ideal.subset_span ⟨i, rfl⟩)
  have h := ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIJ)
  have h' := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hi)
  have hdim' : (n : ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ I) := hdim.trans h
  have hwrong := (add_le_add_left hdim' 1).trans h'
  have hc : (((n+1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
    simpa [ringKrullDim_eq_zero_of_field K, Nat.cast_add, WithBot.coe_add] using hwrong
  exact Nat.not_succ_le_self n (by exact_mod_cast hc)

private def directionalDerivativeLinearOver (G : MvPolynomial (Fin n) K) :
    (Fin n → K) →ₗ[K] MvPolynomial (Fin n) K where
  toFun u := directionalDerivativeOver u G
  map_add' u v := by
    simp only [directionalDerivativeOver, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    simp [directionalDerivativeOver, Pi.smul_apply, smul_eq_mul, Algebra.smul_def, algebraMap_eq,
      Finset.mul_sum, mul_assoc]

private theorem directionalDerivativeOver_homogeneous {G : MvPolynomial (Fin n) K} {e : ℕ}
    (hG : G.IsHomogeneous e) (u : Fin n → K) :
    (directionalDerivativeOver u G).IsHomogeneous (e - 1) := by
  apply IsHomogeneous.sum
  intro i _
  exact (hG.pderiv (i := i)).C_mul _

private theorem diagonal_eval_of_kernel {G : MvPolynomial (Fin n) K} {e : ℕ}
    (hG : G.IsHomogeneous e) (he : ((e-1 : ℕ) : K) ≠ 0)
    (u : Fin n → K) (hu : directionalDerivativeOver u G = 0) (i : Fin n) :
    eval u (pderiv i G) = 0 := by
  have h₁ : (aeval u).comp (aeval (Sum.elim X (fun j => C (u j)))) = aeval (Sum.elim u u) := by
    apply MvPolynomial.algHom_ext
    rintro (j | j) <;> simp
  have h₂ : (aeval (R := K) u).comp (rename (R := K) (Sum.elim id id)) =
      aeval (R := K) (Sum.elim u u) := by
    apply MvPolynomial.algHom_ext
    rintro (j | j) <;> simp [rename_X]
  have h : (e-1) • aeval u (pderiv i G) = 0 := by
    calc
      _ = aeval u (rename (Sum.elim id id) (hessianIncidenceEquation G i)) := by
        rw [hessianIncidenceEquation_diagonal hG, map_nsmul]
      _ = aeval u (aeval (Sum.elim X (fun j => C (u j))) (hessianIncidenceEquation G i)) :=
        DFunLike.congr_fun (h₂.trans h₁.symm) _
      _ = 0 := by rw [hessianIncidenceEquation_specialize, hu, map_zero, map_zero]
  rw [nsmul_eq_mul, mul_eq_zero] at h
  exact h.resolve_left he

private theorem eq_zero_of_full_directional_gradientDimension {G : MvPolynomial (Fin n) K}
    {e : ℕ} (hG : G.IsHomogeneous e) (he : ((e-1 : ℕ) : K) ≠ 0) (u : Fin n → K)
    (h : (n : ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span
      (Set.range fun i => pderiv i (directionalDerivativeOver u G)))) :
    directionalDerivativeOver u G = 0 := by
  let g := directionalDerivativeOver u G
  have hz (i : Fin n) : pderiv i g = 0 := pderiv_eq_zero_of_full_gradientDimension g h i
  have hEuler := (directionalDerivativeOver_homogeneous hG u).sum_X_mul_pderiv
  change (∑ i, X i * pderiv i g) = (e-1) • g at hEuler
  simp only [hz, mul_zero, Finset.sum_const_zero, nsmul_eq_mul] at hEuler
  have hn : ((e-1 : ℕ) : MvPolynomial (Fin n) K) ≠ 0 := by
    rw [← map_natCast (C : K →+* MvPolynomial (Fin n) K)]
    exact fun h => he (C_injective (Fin n) K (by simpa only [map_zero] using h))
  exact (mul_eq_zero.mp hEuler.symm).resolve_left hn


private theorem full_directional_gradientDimension_iff {G : MvPolynomial (Fin n) K}
    {e : ℕ} (hG : G.IsHomogeneous e) (he : ((e-1 : ℕ) : K) ≠ 0) (u : Fin n → K) :
    ((n : ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span
      (Set.range fun i => pderiv i (directionalDerivativeOver u G)))) ↔
      directionalDerivativeOver u G = 0 := by
  refine ⟨eq_zero_of_full_directional_gradientDimension hG he u, ?_⟩
  intro h
  rw [h]
  have hpzero : (fun i : Fin n => pderiv i (0 : MvPolynomial (Fin n) K)) =
      (fun _ => 0) := funext fun _ => map_zero _
  rw [hpzero]
  have hbot : Ideal.span (Set.range (fun _ : Fin n => (0 : MvPolynomial (Fin n) K))) = ⊥ := by
    refine le_antisymm (Ideal.span_le.mpr ?_) bot_le
    rintro _ ⟨i, rfl⟩
    exact Ideal.zero_mem _
  rw [hbot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)]
  simp

private theorem CoordinateSlicing.of_injective_coordinate_projection {K : Type*} {l : ℕ}
    (I : Finset (Fin n)) (hI : I.card ≤ l) (V : Set (Fin n → K))
    (hV : ∀ x ∈ V, ∀ y ∈ V, (∀ i ∈ I, x i = y i) → x = y) :
    CoordinateSlicing l 1 V := by
  classical
  induction I using Finset.induction_on generalizing l V with
  | empty =>
      by_cases h : V.Nonempty
      · obtain ⟨x,hx⟩ := h
        exact .finite {x} (fun y hy => Finset.mem_singleton.mpr
          (hV y hy x hx (by simp))) (by simp)
      · exact .finite ∅ (by simpa only [Set.not_nonempty_iff_eq_empty.mp h] using Set.empty_subset _)
          (by simp)
  | @insert i I hi ih =>
      obtain ⟨l,rfl⟩ : ∃ k, l = k + 1 := by
        rw [Finset.card_insert_of_notMem hi] at hI
        exact ⟨l-1, by omega⟩
      apply CoordinateSlicing.coordinate i
      intro a
      apply ih (l := l)
      · simpa only [Finset.card_insert_of_notMem hi, Nat.add_le_add_iff_right] using hI
      · intro x hx y hy hxy
        apply hV x hx.1 y hy.1
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hx.2.trans hy.2.symm
        · exact hxy j hj

/-- The bad locus where the derivative has full-dimensional gradient is
linear and admits a coordinate-slicing certificate of degree one. -/
theorem primeBadDirectionLocus_maximal_slicing {n p e s : ℕ} (hp : p.Prime)
    (G : IntForm n) (hG : G.IsHomogeneous e) (he : 2 ≤ e) (hep : e ≤ p)
    (hdim : PrimeGradientDimension p hp G s) :
    letI : Fact p.Prime := ⟨hp⟩
    CoordinateSlicing s 1 (primeBadDirectionLocus p G n) := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let g := MvPolynomial.map (Int.castRingHom K) G
  let L := directionalDerivativeLinearOver g
  let W := LinearMap.ker L
  have hG' : g.IsHomogeneous e := hG.map _
  have hne : ((e-1 : ℕ) : K) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff K p (e-1)).mp h
    have hlep := Nat.le_of_dvd (by omega : 0 < e-1) hdiv
    omega
  have hdim' : ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span
      (Set.range fun i => pderiv i g)) = (s : ℕ∞) := by
    have hfun : (fun i : Fin n => pderiv i g) =
        fun i => MvPolynomial.map (Int.castRingHom K) (pderiv i G) :=
      funext fun _ => pderiv_map
    rw [hfun]
    exact hdim
  have hW : finrank K W ≤ s := by
    have h := finrank_le_gradientDimension_of_subspace g W fun u hu =>
      diagonal_eval_of_kernel hG' hne u (LinearMap.mem_ker.mp hu)
    rw [hdim'] at h
    exact_mod_cast h
  have hbad : primeBadDirectionLocus p G n = (W : Set (Fin n → K)) := by
    ext u
    have hlin : L u = 0 ↔ u ∈ W := LinearMap.mem_ker.symm
    exact (full_directional_gradientDimension_iff hG' hne u).trans hlin
  obtain ⟨I,hI,hinj⟩ := exists_coordinate_projection_ker W
  apply CoordinateSlicing.of_injective_coordinate_projection I (hI.trans hW)
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  rw [hbad] at hx hy
  apply hinj _ (W.sub_mem hx hy)
  intro i hi
  exact sub_eq_zero.mpr (hxy i hi)

/-- The geometric certificate is needed only for the intermediate strata
whose gradient dimension increases but is still below the ambient dimension. -/
def PrimeDirectionIntermediateSlicing (n d : ℕ) : Prop :=
  ∃ D : ℕ, ∀ (p : ℕ) (hp : p.Prime) (e : ℕ), 2 < e → e ≤ d → d < p →
    ∀ (G : IntForm n), G.IsHomogeneous e → ∀ s j : ℕ, s < j → j < n →
      PrimeGradientDimension p hp G s →
      letI : Fact p.Prime := ⟨hp⟩
      CoordinateSlicing (n - (j - s)) D (primeBadDirectionLocus p G j)

/-- The maximal dimensional stratum and the intermediate certificates supply
all the direction counts required by the differencing chain. -/
theorem primeDirectionBound_of_intermediate_slicing {n d : ℕ}
    (hintermediate : PrimeDirectionIntermediateSlicing n d) : PrimeDirectionBound n d := by
  obtain ⟨D, hD⟩ := hintermediate
  refine primeDirectionBound_of_slicing ⟨D+1, ?_⟩
  intro p hp e he hed hdp G hG s j hs hj hsj hdim
  let : Fact p.Prime := ⟨hp⟩
  have hmono {l A B : ℕ} {V : Set (Fin n → AlgebraicClosure (ZMod p))}
      (hV : CoordinateSlicing l A V) (hAB : A ≤ B) : CoordinateSlicing l B V := by
    exact .cover (fun _ : Fin 1 => V) (fun _ => A)
      (fun _ hx => Set.mem_iUnion.mpr ⟨0, hx⟩) (by simpa using hAB) (fun _ => hV)
  rcases hj.lt_or_eq with hj | hEq
  · exact hmono (hD p hp e he hed hdp G hG s j hsj hj hdim) (Nat.le_succ D)
  · subst j
    rw [show n - (n - s) = s by omega]
    exact hmono (primeBadDirectionLocus_maximal_slicing hp G hG (by omega) (by omega) hdim)
      (Nat.succ_pos D)

end

end Birch
