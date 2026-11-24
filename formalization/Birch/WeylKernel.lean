import Birch.WeylDifferencing
import Birch.MaximalDirectionStratum
import Birch.GradientDimensionIndex
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The shrunken Weyl kernel count via good reduction

An auxiliary good prime can be chosen larger than the shift box. An integral
tuple in the frequency kernel satisfies the same vanishing condition at
that prime. The successive bounds on the dimension jumps are the ones used
for completion; the final jump to a zero linear form is the maximal stratum.
-/

open MvPolynomial Finset
open scoped BigOperators

namespace Birch

noncomputable section

/-- The tuples with zero terminal homogeneous form. -/
def weylKernelBox {n : ℕ} (G : IntForm n) (k : ℕ) (U : ℝ) :
    Finset (Fin k → Fin n → ℤ) := by
  classical
  exact (weylShiftBox n k U).filter fun h => weylDirectionalDerivative (List.ofFn h) G = 0

theorem mem_weylKernelBox {n k : ℕ} {G : IntForm n} {U : ℝ} {h : Fin k → Fin n → ℤ} :
    h ∈ weylKernelBox G k U ↔
      (∀ i, h i ∈ latticeBox n U) ∧ weylDirectionalDerivative (List.ofFn h) G = 0 := by
  classical
  simp only [weylKernelBox, Finset.mem_filter, weylShiftBox, Fintype.mem_piFinset]

theorem card_weylKernelBox_succ {n k : ℕ} (G : IntForm n) (U : ℝ) :
    (weylKernelBox G (k+1) U).card =
      ∑ h ∈ latticeBox n U, (weylKernelBox (directionalDerivative h G) k U).card := by
  classical
  let T := weylKernelBox G (k+1) U
  let D := latticeBox n U
  have hmap : (T : Set (Fin (k+1) → Fin n → ℤ)).MapsTo (fun t => t 0) D :=
    fun _ ht => (mem_weylKernelBox.mp ht).1 0
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro h hh
  let e : (Fin k → Fin n → ℤ) ↪ (Fin (k+1) → Fin n → ℤ) :=
    ⟨fun t => Fin.cons h t, fun _ _ hf => by
      simpa only [Fin.tail_cons] using
        congrArg (fun t : Fin (k+1) → Fin n → ℤ => Fin.tail t) hf⟩
  let S := weylKernelBox (directionalDerivative h G) k U
  have hs (t : Fin k → Fin n → ℤ) : e t ∈ T ↔ t ∈ S := by
    rw [mem_weylKernelBox, mem_weylKernelBox]
    change ((∀ i : Fin (k+1),
      (Fin.cons h t : Fin (k+1) → Fin n → ℤ) i ∈ latticeBox n U) ∧
      weylDirectionalDerivative (List.ofFn (Fin.cons h t : Fin (k+1) → Fin n → ℤ)) G = 0) ↔ _
    have hhD : h ∈ latticeBox n U := hh
    simp [Fin.forall_fin_succ, hhD, List.ofFn_succ]
  have he : (T.filter fun t => t 0 = h) = S.map e := by
    ext t
    constructor
    · intro ht
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht
      have heq : e (Fin.tail t) = t := by
        change Fin.cons h (Fin.tail t) = t
        rw [← ht₂, Fin.cons_self_tail]
      exact Finset.mem_map.mpr ⟨Fin.tail t, (hs _).mp (heq.symm ▸ ht₁), heq⟩
    · intro ht
      obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ht
      exact Finset.mem_filter.mpr ⟨(hs _).mpr hx, rfl⟩
  rw [he, Finset.card_map]

private theorem primeGradientDimension_zero_eq_ambient {n p : ℕ} (hp : p.Prime) :
    PrimeGradientDimension p hp (0 : IntForm n) n := by
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let R := MvPolynomial (Fin n) K
  have hfun :
      (fun i : Fin n => MvPolynomial.map (Int.castRingHom K) (pderiv i (0 : IntForm n))) =
        (fun _ => (0 : R)) := funext fun _ => by simp
  change ringKrullDim (R ⧸ Ideal.span (Set.range _)) = (n : ℕ∞)
  rw [hfun]
  have hbot : Ideal.span (Set.range (fun _ : Fin n => (0 : R))) = ⊥ := by
    refine le_antisymm (Ideal.span_le.mpr ?_) bot_le
    rintro _ ⟨i,rfl⟩
    exact Ideal.zero_mem _
  rw [hbot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)]
  simp [R]

private theorem kernel_bound_one {n p s : ℕ} (hp : p.Prime) (hp₂ : 2 ≤ p)
    {G : IntForm n} (hG : G.IsHomogeneous 2) (hs : s ≤ n)
    (hdim : PrimeGradientDimension p hp G s) {U : ℝ} (hU : 0 ≤ U)
    (hpU : 2*(2*U+2) ≤ p) :
    ((weylKernelBox G 1 U).card : ℝ) ≤ (3 : ℝ)^n * (2*U+2)^s := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let C := fun u : Fin n → ℤ => PrimeGradientDimension p hp (directionalDerivative u G) n
  let S := (differencingDirections n (2*U+2)).filter C
  have hC (t : Fin 1 → Fin n → ℤ) (ht : t ∈ weylKernelBox G 1 U) : t 0 ∈ S := by
    obtain ⟨hbox,hzero⟩ := mem_weylKernelBox.mp ht
    have hz : directionalDerivative (t 0) G = 0 := by
      simpa only [List.ofFn_succ, List.ofFn_zero, weylDirectionalDerivative_cons,
        weylDirectionalDerivative_nil] using hzero
    refine Finset.mem_filter.mpr ⟨latticeBox_subset_differencingDirections hU (hbox 0), ?_⟩
    simpa only [C, hz] using primeGradientDimension_zero_eq_ambient (n := n) hp
  have hcard : ((weylKernelBox G 1 U).card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun (t : Fin 1 → Fin n → ℤ) => t 0) hC
      (fun x _ y _ h => funext fun i => by simpa only [Subsingleton.elim i 0] using h)
  have hcut := card_filter_differencingDirections_le_of_slicing (by linarith : 1 ≤ 2*U+2) hpU C
    (primeBadDirectionLocus_maximal_slicing hp G hG (by norm_num) hp₂ hdim)
    (fun u _ hu => mem_primeBadDirectionLocus_of_dim G u hu)
  refine hcard.trans (hcut.trans ?_)
  rw [Nat.cast_one, one_mul]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) hs)
    (by positivity)

private theorem kernel_bound_at_prime {n d p : ℕ} (hp : p.Prime) (hpd : d < p)
    {K : ℝ} (hK : 0 < K) (hcount : PrimeDirectionCountAt n d K)
    {U : ℝ} (hU : 0 ≤ U) (hpU : 2*(2*U+2) ≤ p)
    (k : ℕ) (hk : 0 < k) (hkd : k+1 ≤ d)
    (G : IntForm n) (hG : G.IsHomogeneous (k+1)) (s : Fin (n+1))
    (hdim : PrimeGradientDimension p hp G s.val) :
    ((weylKernelBox G k U).card : ℝ) ≤
      (((n:ℝ)+1)*(K+3^n+1))^k * (2*U+2)^(n*(k-1)+s.val) := by
  classical
  let H : ℝ := 2*U+2
  let C : ℝ := ((n:ℝ)+1)*(K+3^n+1)
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  induction k generalizing G s with
  | zero => omega
  | succ k ih =>
    by_cases hk₀ : k = 0
    · subst k
      have hb := kernel_bound_one hp (by omega) hG (Nat.lt_succ_iff.mp s.isLt) hdim hU hpU
      simpa only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, pow_one] using
        hb.trans (mul_le_mul_of_nonneg_right (show (3 : ℝ)^n ≤ C by
          dsimp [C]
          have h : (1 : ℝ) ≤ (n:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
          exact (show (3:ℝ)^n ≤ K+3^n+1 by linarith).trans
            (le_mul_of_one_le_left (by positivity) h)) (by positivity))
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk₀
    have hhomo (u : Fin n → ℤ) : (directionalDerivative u G).IsHomogeneous (k+1) := by
      simpa only [weylDirectionalDerivative_cons, weylDirectionalDerivative_nil, List.length_singleton,
        Nat.add_sub_cancel] using weylDirectionalDerivative_homogeneous [u] hG
    have hExists (u : Fin n → ℤ) : ∃ j : Fin (n+1),
        PrimeGradientDimension p hp (directionalDerivative u G) j.val :=
      exists_primeGradientDimension hp (hhomo u) (by omega)
    choose Γ hΓ using hExists
    let D := latticeBox n U
    let f (u : Fin n → ℤ) := ((weylKernelBox (directionalDerivative u G) k U).card : ℝ)
    rw [card_weylKernelBox_succ, Nat.cast_sum]
    change (∑ u ∈ D, f u) ≤ C^(k+1) * H^(n*(k+1-1)+s.val)
    have hfiber :
        ∑ j : Fin (n+1), ∑ u ∈ D.filter (fun u => Γ u = j), f u = ∑ u ∈ D, f u :=
      Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) f
    rw [← hfiber]
    let A : ℝ := K * C^k * H^(n*k+s.val)
    have hclass (j : Fin (n+1)) :
        ∑ u ∈ D.filter (fun u => Γ u = j), f u ≤ A := by
      let E := D.filter (fun u => Γ u = j)
      have hj : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
      have hd : j.val - s.val ≤ n := (Nat.sub_le _ _).trans hj
      have hclassCount := hcount p hp (k+1+1) (by omega) hkd hpd G hG s.val j.val
        (Nat.lt_succ_iff.mp s.isLt) hj hdim H hH hpU
      rw [← Nat.cast_sub hd, Real.rpow_natCast] at hclassCount
      have hm : (E.card : ℝ) ≤ K * H^(n-(j.val-s.val)) := by
        refine (show (E.card : ℝ) ≤ _ from Nat.cast_le.mpr (Finset.card_le_card ?_)).trans hclassCount
        intro u hu
        obtain ⟨hub,hus⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨latticeBox_subset_differencingDirections hU hub,
          hus ▸ hΓ u⟩
      have hf (u : Fin n → ℤ) (hu : u ∈ E) :
          f u ≤ C^k * H^(n*(k-1)+j.val) := by
        have hj' := (Finset.mem_filter.mp hu).2
        have hh := ih hkpos (by omega) (directionalDerivative u G) (hhomo u) (Γ u) (hΓ u)
        simpa only [C, H, hj'] using hh
      calc
        _ ≤ ∑ u ∈ E, C^k*H^(n*(k-1)+j.val) := Finset.sum_le_sum hf
        _ = (E.card : ℝ)*(C^k*H^(n*(k-1)+j.val)) := by simp [nsmul_eq_mul]
        _ ≤ (K*H^(n-(j.val-s.val)))*(C^k*H^(n*(k-1)+j.val)) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = K * C^k * H^((n-(j.val-s.val))+(n*(k-1)+j.val)) := by rw [pow_add]; ring
        _ ≤ A := by
          have hexp : (n-(j.val-s.val))+(n*(k-1)+j.val) ≤ n*k+s.val := by
            have he : n*k = n*(k-1)+n := by
              rw [← Nat.mul_succ]
              congr 1
              omega
            omega
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH hexp) (by positivity)
    calc
      _ ≤ ∑ _j : Fin (n+1), A := Finset.sum_le_sum (fun j _ => hclass j)
      _ = ((n:ℝ)+1) * (K * C^k * H^(n*k+s.val)) := by simp [A, nsmul_eq_mul]
      _ ≤ C^(k+1) * H^(n*(k+1-1)+s.val) := by
        rw [pow_succ', Nat.add_sub_cancel]
        have hc : ((n:ℝ)+1)*K ≤ C := by
          dsimp [C]
          exact mul_le_mul_of_nonneg_left (by
            have h : (0:ℝ) ≤ 3^n := by positivity
            linarith) (by positivity)
        have hn := mul_le_mul_of_nonneg_right hc (show 0 ≤ C^k*H^(n*k+s.val) by positivity)
        nlinarith

/-- The Weyl frequency kernel grows with exponent `n*(d-2)+σ` when the
reduced gradient dimension is at most `σ` at every sufficiently large prime. -/
theorem exists_card_weylKernelBox_le_of_gradientDim {n d σ : ℕ} {F : IntForm n} (hd : 2 ≤ d)
    (hF : F.IsHomogeneous d) (hσ : σ ≤ n) (hs : EventualPrimeGradientDimensionLE F σ)
    (hdir : PrimeDirectionBound n d) :
    ∃ B : ℝ, 0 < B ∧ ∀ U : ℝ, 0 ≤ U →
      ((weylKernelBox F (d-1) U).card : ℝ) ≤ B * (1+U)^(n*(d-2)+σ) := by
  obtain ⟨K,hK,hcount⟩ := hdir
  obtain ⟨b,hgood⟩ := hs
  let k := d-1
  let C : ℝ := ((n:ℝ)+1)*(K+3^n+1)
  let E := n*(d-2)+σ
  refine ⟨C^k * 2^E, by dsimp [C]; positivity, ?_⟩
  intro U hU
  let N := max (b+1) (max (d+1) ⌈2*(2*U+2)⌉₊)
  obtain ⟨p,hpN,hp⟩ := Nat.exists_infinite_primes N
  have hpb : b < p := (Nat.lt_succ_self b).trans_le ((le_max_left _ _).trans hpN)
  have hpd : d < p := (Nat.lt_succ_self d).trans_le
    ((le_max_left _ _).trans ((le_max_right _ _).trans hpN))
  have hpU : 2*(2*U+2) ≤ (p:ℝ) := (Nat.le_ceil (2*(2*U+2))).trans
    (Nat.cast_le.mpr ((le_max_right _ _).trans ((le_max_right _ _).trans hpN)))
  obtain ⟨s, hsσ, hdim⟩ := hgood p hpb hp
  let sIndex : Fin (n+1) := ⟨s, Nat.lt_succ_of_le (hsσ.trans hσ)⟩
  have hk : 0 < k := by dsimp [k]; omega
  have hkd : k+1 = d := by dsimp [k]; omega
  have hG : F.IsHomogeneous (k+1) := hkd.symm ▸ hF
  have h := kernel_bound_at_prime hp hpd hK hcount hU hpU k hk hkd.le F hG sIndex hdim
  change ((weylKernelBox F k U).card : ℝ) ≤ _ 
  change ((weylKernelBox F k U).card : ℝ) ≤ (C^k*2^E)*(1+U)^E
  have hC : 0 ≤ C^k := by dsimp [C]; positivity
  have hE : n*(k-1)+s ≤ E := by
    change n*(d-1-1)+s ≤ n*(d-2)+σ
    rw [Nat.sub_sub]
    exact Nat.add_le_add_left hsσ _
  have hpow := pow_le_pow_right₀ (by linarith : 1 ≤ 2*U+2) hE
  refine h.trans ((mul_le_mul_of_nonneg_left hpow hC).trans_eq ?_)
  rw [show (2*U+2 : ℝ) = 2*(1+U) by ring, mul_pow (2 : ℝ) (1+U) E, mul_assoc]

/-- The Weyl frequency kernel at a smooth form has starting gradient
dimension zero. -/
theorem exists_card_weylKernelBox_le {n d : ℕ} {F : IntForm n} (hd : 2 ≤ d)
    (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hdir : PrimeDirectionBound n d) :
    ∃ B : ℝ, 0 < B ∧ ∀ U : ℝ, 0 ≤ U →
      ((weylKernelBox F (d-1) U).card : ℝ) ≤ B * (1+U)^(n*(d-2)) := by
  obtain ⟨b, hgood⟩ := hs.eventually_goodReduction hF hd
  have hgrad : EventualPrimeGradientDimensionLE F 0 :=
    ⟨b, fun p hp hprime =>
      ⟨0, le_rfl, primeGradientDimension_zero_of_goodReduction hprime F
        (fun K _ _ => hgood p hp K)⟩⟩
  simpa only [Nat.add_zero] using
    exists_card_weylKernelBox_le_of_gradientDim hd hF (Nat.zero_le n) hgrad hdir

end

end Birch
