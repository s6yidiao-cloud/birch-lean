import Birch.DirectionCountBridge
import Birch.GradientDimensionIndex
import Birch.Main
import Birch.MaximalDirectionStratum
import Birch.SectionDiscriminant
import Birch.SectionEndpoints

/-! # The completion proposition from its classical inputs -/

open Filter MvPolynomial
open scoped ContDiff Topology BigOperators

namespace Birch

noncomputable section

/-- A smooth section of the required codimension can be chosen with an entry
bound depending only on the ambient dimension and degree. -/
def PrimeSectionBound (n r : ℕ) : Prop :=
  ∃ B : ℕ, 1 ≤ B ∧ ∃ p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
    ∀ (G : IntForm n), G.IsHomogeneous r → ∀ s : Fin (n+1),
      PrimeGradientDimension p hp G s.val →
        letI : Fact p.Prime := ⟨hp⟩
        BoundedSmoothSection p (n-s.val) B G

/-- Only the interior dimensions require the general section argument. -/
def PrimeInteriorSectionBound (n r : ℕ) : Prop :=
  ∃ B p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
    ∀ (G : IntForm n), G.IsHomogeneous r → ∀ s : Fin (n+1),
      0 < s.val → 2 ≤ n-s.val → PrimeGradientDimension p hp G s.val →
        letI : Fact p.Prime := ⟨hp⟩
        BoundedSmoothSection p (n-s.val) B G

/-- Geometric smooth sections over the algebraic closure in the interior
dimensions. The matrices here have no integrality or entry bound. -/
def PrimeGeometricInteriorSections (n r : ℕ) : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), r < p → ∀ (G : IntForm n), G.IsHomogeneous r →
    ∀ s : Fin (n+1), 0 < s.val → 2 ≤ n-s.val → PrimeGradientDimension p hp G s.val →
      letI : Fact p.Prime := ⟨hp⟩
      let K := AlgebraicClosure (ZMod p)
      ∃ W : Matrix (Fin n) (Fin (n-s.val)) K,
        ∀ x : Fin (n-s.val) → K,
          (∀ j, (pderiv j (linearSectionOver W G)).eval x = 0) → x = 0

/-- A geometric section suffices for one fixed integral entry bound, across
all sufficiently large primes and all forms of the given degree. -/
theorem primeInteriorSectionBound_of_geometric {n r : ℕ} (hr : 2 ≤ r)
    (hgeom : PrimeGeometricInteriorSections n r) : PrimeInteriorSectionBound n r := by
  classical
  choose B hB hbound using fun l : Fin (n+1) => exists_uniform_bounded_smooth_section n l.val r hr
  let B₀ := ∑ l, B l
  have hle (l : Fin (n+1)) : B l ≤ B₀ :=
    Finset.single_le_sum (f := B) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  refine ⟨B₀,max B₀ r,?_⟩
  intro p hp hp₀ G hG s hs hl hdim
  let : Fact p.Prime := ⟨hp⟩
  let l : Fin (n+1) := ⟨n-s.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hpB : B l < p := (hle l).trans_lt ((le_max_left B₀ r).trans_lt hp₀)
  have hpr : r < p := (le_max_right B₀ r).trans_lt hp₀
  obtain ⟨U,hU,hsmooth⟩ := hbound l p hpB G hG (hgeom p hp hpr G hG s hs hl hdim)
  exact ⟨U, fun i j => (hU i j).trans (by exact_mod_cast hle l), hsmooth⟩

/-- The zero-, one-, and full-dimensional sections complete the interior section bound. -/
theorem primeSectionBound_of_interior {n r : ℕ} (hr : 2 ≤ r)
    (h : PrimeInteriorSectionBound n r) : PrimeSectionBound n r := by
  obtain ⟨B,p₀,h⟩ := h
  refine ⟨max B r, (by omega), max p₀ r, ?_⟩
  intro p hp hlarge G hG s hdim
  let : Fact p.Prime := ⟨hp⟩
  have hp₀ : p₀ < p := (le_max_left _ _).trans_lt hlarge
  have hpr : r < p := (le_max_right _ _).trans_lt hlarge
  obtain ⟨U, hU, hgrad⟩ : ∃ M : Matrix (Fin n) (Fin (n-s.val)) ℤ,
      (∀ i j, |M i j| ≤ ((max B r : ℕ) : ℤ)) ∧
      ∀ x : Fin (n-s.val) → AlgebraicClosure (ZMod p),
        (∀ i, evalForm (pderiv i (linearSection M G)) x = 0) → x = 0 := by
    by_cases hedge : n-s.val ≤ 1 ∨ s.val = 0
    · obtain ⟨M,hM,hcrit⟩ := boundedSmoothSection_of_endpoint hG hr hpr hdim hedge
      exact ⟨M, fun i j => (hM i j).trans (by exact_mod_cast le_max_right B r), hcrit⟩
    · obtain ⟨M,hM,hcrit⟩ := h p hp hp₀ G hG s (by omega) (by omega) hdim
      exact ⟨M, fun i j => (hM i j).trans (by exact_mod_cast le_max_left B r), hcrit⟩
  exact ⟨U,hU,hgrad⟩

/-- At a single terminal degree, the direction, section, and twisted sum
bounds yield the corresponding completion inputs. -/
theorem completionInputsAt_of_uniform_primeBounds_withMultiplier {n d r : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hw : ContDiff ℝ ∞ w)
    (hwbox : CubeSupported w) (hr : 2 ≤ r) (hrd : r ≤ d) (hdir : PrimeDirectionBound n d)
    (hsection : PrimeSectionBound n r)
    {multiplier : ℕ → ℝ} (hMultiplier : ∀ p, 0 ≤ multiplier p)
    (hTwisted : ∀ l ≤ n, UniformTwistedResidueBoundWithMultiplier (fun p => p) r l multiplier) :
    CompletionInputsAtWithMultiplier d r F w multiplier := by
  obtain ⟨K,hK,hcount⟩ := hdir
  obtain ⟨B,hB,p₀,hsection⟩ := hsection
  choose T hT hterminal using fun l : Fin (n+1) =>
    terminal_chain_bound_of_bounded_sections_of_residue_bound_with_multiplier (B := B)
      (Nat.lt_succ_iff.mp l.isLt) hB hF hr hrd hw hwbox (modulus := fun p => p) (L := 2)
      (by norm_num) multiplier hMultiplier (hTwisted l.val (Nat.lt_succ_iff.mp l.isLt))
  let T₀ := 1 + ∑ l, T l
  have hT₀ : 0 < T₀ := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun l _ => (hT l).le)
  have hTle (l : Fin (n+1)) : T l ≤ T₀ :=
    (Finset.single_le_sum (f := T) (fun j _ => (hT j).le) (Finset.mem_univ l)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨K,hK,T₀,hT₀,?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ), eventually_ge_atTop (d : ℝ),
    eventually_ge_atTop (p₀ : ℝ)] with P hP hdP hp₀P Q hQ hQmax p hp hpL hpU
  have hP₁ : 1 ≤ P := by linarith
  have hQsqrt : Q ≤ Real.sqrt P := Real.sqrt_eq_rpow P ▸ hQmax
  have hPp : P < (p : ℝ) := completion_scale_le_prime hP₁ hQ hQsqrt hpL
  have hdp : d < p := by exact_mod_cast hdP.trans_lt hPp
  have hp₀p : p₀ < p := by exact_mod_cast hp₀P.trans_lt hPp
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hsExists (i : ℕ) (hi : i ≤ d-r) (g : IntForm n) : ∃ s : Fin (n+1),
      PrimeGradientDimension p hp (homogeneousComponent (d-i) g) s.val :=
    exists_primeGradientDimension hp (homogeneousComponent_isHomogeneous _ _) (by omega)
  let s (i : ℕ) (g : IntForm n) : Fin (n+1) :=
    if hi : i ≤ d-r then Classical.choose (hsExists i hi g) else 0
  have hdim (i : ℕ) (hi : i ≤ d-r) (g : IntForm n) :
      PrimeGradientDimension p hp (homogeneousComponent (d-i) g) (s i g).val := by
    rw [show s i g = Classical.choose (hsExists i hi g) by simp [s,hi]]
    exact Classical.choose_spec (hsExists i hi g)
  refine ⟨s,hdim,?_⟩
  intro m hm
  refine ⟨polynomialDirectionCounts_of_primeBound hcount hr hdp hp hP hQ hQsqrt hpL m s hdim,?_⟩
  intro a α ha hclose t u ht
  let k := d-r
  let s₀ := s k (t k).form
  let l : Fin (n+1) := ⟨n-s₀.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hgrad : PrimeGradientDimension p hp (homogeneousComponent r (t k).form) s₀.val := by
    have he : d-k = r := by dsimp [k]; omega
    simpa only [he] using hdim k le_rfl (t k).form
  have hsec := hsection p hp hp₀p _ (homogeneousComponent_isHomogeneous _ _) s₀ hgrad
  have hfclose : |(t k).frequency - (a : ℝ)/(p : ℝ)| ≤ completionRadius d r P Q := by
    rwa [ht.frequency (i := k) le_rfl]
  have ha' : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have h := hterminal l hP₁ hQ hQsqrt p (hrd.trans_lt hdp) hpL.le hpU m hm α a ha'
    t u ht hfclose hsec
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hTle l) (Real.rpow_nonneg (zero_le_one.trans hQ) _))
    (hMultiplier p))

/-- A uniform square-root bound suffices with multiplier one. -/
theorem completionInputsAt_of_uniform_primeBounds {n d r : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hw : ContDiff ℝ ∞ w)
    (hwbox : CubeSupported w) (hr : 2 ≤ r) (hrd : r ≤ d) (hdir : PrimeDirectionBound n d)
    (hsection : PrimeSectionBound n r)
    (hTwisted : ∀ l ≤ n, UniformTwistedPrimeBound r l) : CompletionInputsAt d r F w := by
  simpa only [CompletionInputsAt, CompletionInputsAtWithMultiplier, mul_one] using
    completionInputsAt_of_uniform_primeBounds_withMultiplier hF hw hwbox hr hrd hdir hsection
      (multiplier := fun _ => 1) (fun _ => zero_le_one)
      (fun l hl => by
        simpa only [UniformTwistedPrimeBound, UniformTwistedResidueBound,
          UniformTwistedResidueBoundWithMultiplier, mul_one] using hTwisted l hl)

/-- Uniform direction counts, bounded smooth sections, and uniform square-root
estimates in the terminal slice dimensions supply the completion input. -/
theorem completionInputs_of_uniform_primeBounds {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hw : ContDiff ℝ ∞ w)
    (hwbox : CubeSupported w) (hdir : PrimeDirectionBound n d)
    (hsection : ∀ r, 2 ≤ r → r < d → PrimeSectionBound n r)
    (hTwisted : ∀ r, 2 ≤ r → r < d → ∀ l ≤ n, UniformTwistedPrimeBound r l) :
    CompletionInputs d F w := by
  intro r hr hrd
  exact completionInputsAt_of_uniform_primeBounds hF hw hwbox hr hrd.le hdir
    (hsection r hr hrd) (hTwisted r hr hrd)

/-- Deligne's bound supplies the uniform finite-field estimate in each
terminal slice dimension. -/
theorem completionInputs_of_primeBounds {n d : ℕ} {F : IntForm n}
    {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hw : ContDiff ℝ ∞ w)
    (hwbox : CubeSupported w) (hdir : PrimeDirectionBound n d)
    (hsection : ∀ r, 2 ≤ r → r < d → PrimeSectionBound n r)
    (hDeligne : ∀ r, 2 ≤ r → r < d → DeligneTwistedDegree r) : CompletionInputs d F w :=
  completionInputs_of_uniform_primeBounds hF hw hwbox hdir hsection fun r hr hrd l _ =>
    uniformTwistedPrimeBound_of_deligneTwistedDegree hr (hDeligne r hr hrd) l

end

end Birch
