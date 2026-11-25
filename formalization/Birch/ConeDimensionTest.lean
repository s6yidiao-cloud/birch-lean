import Birch.ConeOrigin
import Birch.OriginKrullDimension
import Birch.HyperplaneRestriction

/-! # Testing the dimension of a homogeneous cone with linear cuts -/

open MvPolynomial

namespace Birch

noncomputable section

variable {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]

omit [IsAlgClosed K] in
private theorem mem_zeroLocus_ideal_sup {I J : Ideal (MvPolynomial (Fin n) K)}
    {x : Fin n → K} : x ∈ zeroLocus K (I ⊔ J) ↔ x ∈ zeroLocus K I ∧ x ∈ zeroLocus K J := by
  change I ⊔ J ≤ RingHom.ker (aeval x) ↔ I ≤ RingHom.ker (aeval x) ∧ J ≤ RingHom.ker (aeval x)
  exact sup_le_iff

private def linearCutIdeal {k : ℕ} (a : Fin k → Fin n → K) : Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span (Set.range fun i => normalLinearForm (a i))

omit [IsAlgClosed K] in
private theorem linearCutIdeal_cons {k : ℕ} (a : Fin n → K) (b : Fin k → Fin n → K) :
    linearCutIdeal (Fin.cons a b) = Ideal.span {normalLinearForm a} ⊔ linearCutIdeal b := by
  rw [linearCutIdeal, linearCutIdeal, ← Ideal.span_union]
  congr 1
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · exact Or.inr ⟨j,rfl⟩
  · rintro (rfl | ⟨i,rfl⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨i.succ,rfl⟩

private theorem exists_linear_cuts_of_dim_le (i₀ : Fin n) {k : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (hcone : ∀ x ∈ zeroLocus K I, ∀ a : K, (fun i => a * x i) ∈ zeroLocus K I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) K ⧸ I) ≤ (k : WithBot ℕ∞)) :
    ∃ a : Fin k → Fin n → K, zeroLocus K (I ⊔ linearCutIdeal a) ⊆ {0} := by
  induction k generalizing I with
  | zero =>
    let a : Fin 0 → Fin n → K := Fin.elim0
    refine ⟨a, ?_⟩
    intro x hx
    exact zeroLocus_subset_origin_of_dim_le_zero I hcone (by simpa using hdim)
      (mem_zeroLocus_ideal_sup.mp hx).1
  | succ k ih =>
    obtain ⟨a,_,_,hd⟩ := exists_normalLinearForm_dim_drop i₀ I
      (T := 1) one_ne_zero hdim
    let J : Ideal (MvPolynomial (Fin n) K) := Ideal.span {normalLinearForm a}
    have hcone' : ∀ x ∈ zeroLocus K (I ⊔ J), ∀ c : K,
        (fun i => c * x i) ∈ zeroLocus K (I ⊔ J) := by
      intro x hx c
      obtain ⟨hxI,hxJ⟩ := mem_zeroLocus_ideal_sup.mp hx
      apply mem_zeroLocus_ideal_sup.mpr ⟨hcone x hxI c, ?_⟩
      rw [show J = Ideal.span {normalLinearForm a} from rfl, zeroLocus_span] at hxJ ⊢
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      have h : (normalLinearForm a).eval x = 0 := hxJ _ rfl
      change (normalLinearForm a).eval (fun i => c * x i) = 0
      simp only [eval_normalLinearForm] at h ⊢
      rw [show (∑ i, a i * (c * x i)) = c * ∑ i, a i * x i by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring, h, mul_zero]
    obtain ⟨b,hb⟩ := ih (I ⊔ J) hcone' hd
    exact ⟨Fin.cons a b, by rwa [linearCutIdeal_cons, ← sup_assoc]⟩

private theorem dim_le_of_linear_cuts {m e k : ℕ}
    (f : Fin m → MvPolynomial (Fin n) K) (he : 0 < e) (hf : ∀ i, (f i).IsHomogeneous e)
    (a : Fin k → Fin n → K)
    (hz : zeroLocus K (Ideal.span (Set.range f) ⊔ linearCutIdeal a) ⊆ {0}) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f)) ≤ (k : WithBot ℕ∞) := by
  let R := MvPolynomial (Fin n) K
  let I : Ideal R := Ideal.span (Set.range f)
  let O : Ideal R := vanishingIdeal K ({0} : Set (Fin n → K))
  let π := Ideal.Quotient.mk I
  let p := O.map π
  have hI : I ≤ O := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change f i ∈ vanishingIdeal K ({0} : Set (Fin n → K))
    rw [mem_vanishingIdeal_singleton_iff]
    change (f i).eval 0 = 0
    simpa only [mul_zero, ← Pi.zero_def, zero_pow he.ne', zero_mul] using
      eval_homogeneous_scale (hf i) 0 (0 : Fin n → K)
  have hker : RingHom.ker π ≤ O := by rwa [Ideal.mk_ker]
  let : p.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
  have hcomap : Ideal.comap π p = O := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  have hmin (q : Ideal (R ⧸ I)) (hq : q ∈ minimalPrimes (R ⧸ I)) : q ≤ p := by
    have hQ := Ideal.minimalPrimes_comap_of_surjective (f := π) Ideal.Quotient.mk_surjective hq
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hQ
    have hq₀ := minimalPrime_le_coneOrigin f (fun _ => e) hf hQ
    have hq₁ : Ideal.comap π q ≤ O := by
      intro g hg
      change g ∈ vanishingIdeal K ({0} : Set (Fin n → K))
      rw [mem_vanishingIdeal_singleton_iff, aeval_def, Algebra.algebraMap_self]
      exact hq₀ hg
    rw [← hcomap] at hq₁
    exact (Ideal.comap_le_comap_iff_of_surjective _ Ideal.Quotient.mk_surjective q p).mp hq₁
  refine (ringKrullDim_le_height_of_affine_components (K := K) p hmin).trans ?_
  let S := Set.range fun i => π (normalLinearForm (a i))
  have hS : S ⊆ p := by
    rintro _ ⟨i,rfl⟩
    apply Ideal.mem_map_of_mem π
    rw [mem_vanishingIdeal_singleton_iff, aeval_eq_eval, eval_normalLinearForm]
    simp
  have hS' : Ideal.span S = Ideal.map π (linearCutIdeal a) := by
    rw [linearCutIdeal, Ideal.map_span, ← Set.range_comp]
    rfl
  have hcard : S.encard ≤ (k : ℕ∞) := by
    change (Set.range (fun i => π (normalLinearForm (a i)))).encard ≤ _
    rw [← Set.image_univ]
    simpa using Set.encard_image_le (fun i => π (normalLinearForm (a i))) Set.univ
  have hheight := Ideal.height_le_ringKrullDim_quotient_add_encard (p := p) S hS
  rw [hS', ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I (linearCutIdeal a))] at hheight
  exact hheight.trans ((add_le_add (ringKrullDim_le_zero_of_zeroLocus_subset_origin _ hz)
    (WithBot.coe_le_coe.mpr hcard)).trans_eq (zero_add _))

/-- A homogeneous system has dimension at most k exactly when some k linear
cuts leave only the origin as a possible common zero. -/
theorem homogeneousSystem_dim_le_iff_linear_cuts {m e k : ℕ} (i₀ : Fin n)
    (f : Fin m → MvPolynomial (Fin n) K) (he : 0 < e) (hf : ∀ i, (f i).IsHomogeneous e) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range f)) ≤ (k : WithBot ℕ∞) ↔
      ∃ a : Fin k → Fin n → K, ∀ x : Fin n → K,
        (∀ j, (f j).eval x = 0) → (∀ j, (normalLinearForm (a j)).eval x = 0) → x = 0 := by
  have hcone : ∀ x ∈ zeroLocus K (Ideal.span (Set.range f)), ∀ c : K,
      (fun i => c * x i) ∈ zeroLocus K (Ideal.span (Set.range f)) := by
    intro x hx c
    rw [zeroLocus_span] at hx ⊢
    rintro _ ⟨j,rfl⟩
    change (f j).eval (fun i => c * x i) = 0
    rw [eval_homogeneous_scale (hf j), show (f j).eval x = 0 from hx _ ⟨j,rfl⟩, mul_zero]
  constructor
  · intro hd
    obtain ⟨a,ha⟩ := exists_linear_cuts_of_dim_le i₀ _ hcone hd
    refine ⟨a, fun x hf₀ ha₀ => ha (mem_zeroLocus_ideal_sup.mpr ⟨?_,?_⟩)⟩
    · rw [zeroLocus_span]; rintro _ ⟨j,rfl⟩; exact hf₀ j
    · rw [linearCutIdeal, zeroLocus_span]; rintro _ ⟨j,rfl⟩; exact ha₀ j
  · rintro ⟨a,ha⟩
    refine dim_le_of_linear_cuts f he hf a fun x hx => ?_
    obtain ⟨hxf,hxa⟩ := mem_zeroLocus_ideal_sup.mp hx
    exact ha x (fun j => hxf _ (Ideal.subset_span ⟨j,rfl⟩))
      (fun j => hxa _ (Ideal.subset_span ⟨j,rfl⟩))

end
end Birch
