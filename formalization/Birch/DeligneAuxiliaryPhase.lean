import Birch.DeligneGoodLevelCounts
import Birch.MorseAuxiliaryCounts

/-! # A regular auxiliary phase in one more variable -/

open MvPolynomial

namespace Birch

noncomputable section

/-- Adjoin the scaled polynomial `z^r-z` in coordinate zero. -/
def adjoinMorsePhase {K : Type*} [Field K] {n : ℕ}
    (r : ℕ) (b : K) (g : MvPolynomial (Fin n) K) : MvPolynomial (Fin (n+1)) K :=
  rename Fin.succ g + C b * (X 0 ^ r - X 0)

theorem map_adjoinMorsePhase {F K : Type*} [Field F] [Field K] {n : ℕ} (φ : F →+* K)
    (r : ℕ) (b : F) (g : MvPolynomial (Fin n) F) :
    MvPolynomial.map φ (adjoinMorsePhase r b g) = adjoinMorsePhase r (φ b) (MvPolynomial.map φ g) := by
  simp only [adjoinMorsePhase, map_add, map_rename, map_mul, map_C, map_sub, map_pow, map_X]

theorem eval_adjoinMorsePhase {K : Type*} [Field K] {n : ℕ} (r : ℕ) (b : K)
    (g : MvPolynomial (Fin n) K) (x : Fin (n+1) → K) :
    (adjoinMorsePhase r b g).eval x = g.eval (x ∘ Fin.succ) + b * (morseAuxiliaryPolynomial r).eval (x 0) := by
  simp [adjoinMorsePhase, eval_rename]

theorem totalDegree_adjoinMorsePhase_le {K : Type*} [Field K] {n r : ℕ}
    (hr : 2 ≤ r) (b : K) {g : MvPolynomial (Fin n) K} (hg : g.totalDegree ≤ r) :
    (adjoinMorsePhase r b g).totalDegree ≤ r := by
  have hr₁ : 1 ≤ r := by omega
  apply (totalDegree_add _ _).trans
  apply max_le ((totalDegree_rename_le Fin.succ g).trans hg)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_sub _ _).trans (max_le (isHomogeneous_X_pow _ _).totalDegree_le
    ((isHomogeneous_X _ _).totalDegree_le.trans hr₁))

private theorem pderiv_succ_adjoinMorsePhase {K : Type*} [Field K] {n : ℕ}
    (r : ℕ) (b : K) (g : MvPolynomial (Fin n) K) (i : Fin n) :
    pderiv i.succ (adjoinMorsePhase r b g) = rename Fin.succ (pderiv i g) := by
  simp [adjoinMorsePhase, pderiv_rename (Fin.succ_injective n)]

private theorem pderiv_zero_adjoinMorsePhase {K : Type*} [Field K] {n : ℕ}
    (r : ℕ) (b : K) (g : MvPolynomial (Fin n) K) :
    pderiv 0 (adjoinMorsePhase r b g) = C b * (C (r : K) * X 0 ^ (r-1) - 1) := by
  simp [adjoinMorsePhase, pderiv_rename_eq_zero_of_not_mem_range Fin.succ 0 (by simp),
    nsmul_eq_mul]

private theorem leading_adjoinMorsePhase {K : Type*} [Field K] {n r : ℕ} (hr : 2 ≤ r)
    (b : K) (g : MvPolynomial (Fin n) K) :
    homogeneousComponent r (adjoinMorsePhase r b g) =
      rename Fin.succ (homogeneousComponent r g) + C b * X 0^r := by
  have hx : homogeneousComponent r (X (0 : Fin (n+1)) : MvPolynomial (Fin (n+1)) K) = 0 :=
    homogeneousComponent_eq_zero _ _ ((isHomogeneous_X K _).totalDegree_le.trans_lt (by omega))
  simp only [adjoinMorsePhase, mul_sub, map_add, map_sub, rename_homogeneousComponent,
    homogeneousComponent_C_mul, homogeneousComponent_eq_self (isHomogeneous_X_pow _ _),
    hx, mul_zero, sub_zero]

/-- Adjoining the auxiliary variable preserves the isolated leading critical point. -/
theorem primeIsolatedLeadingCriticalPoint_adjoinMorsePhase {p n r : ℕ} [Fact p.Prime]
    (hr : 2 ≤ r) (hrp : r < p) {b : ZMod p} (hb : b ≠ 0) {g : MvPolynomial (Fin n) (ZMod p)}
    (hcrit : PrimeIsolatedLeadingCriticalPoint p r g) :
    PrimeIsolatedLeadingCriticalPoint p r (adjoinMorsePhase r b g) := by
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  intro x hx
  have htop := leading_adjoinMorsePhase hr b g
  have hbK : φ b ≠ 0 := (map_ne_zero φ).mpr hb
  have hrK : (r : K) ≠ 0 := fun hz =>
    (not_le_of_gt hrp) (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff K p r).mp hz))
  have hx0 : x 0 = 0 := by
    have hz := hx 0
    rw [htop] at hz
    have h : φ b * ((r : K) * (x 0)^(r-1)) = 0 := by
      simpa [pderiv_rename_eq_zero_of_not_mem_range Fin.succ 0 (by simp), pderiv_C_mul,
        pderiv_pow, nsmul_eq_mul] using hz
    exact (pow_eq_zero_iff (show r-1 ≠ 0 by omega)).mp
      ((mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hbK)).resolve_left hrK)
  have hxs : x ∘ Fin.succ = 0 := hcrit _ (fun i => by
    have hz := hx i.succ
    rw [htop] at hz
    simpa [pderiv_rename (Fin.succ_injective n), eval₂_rename] using hz)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hx0
  · exact congrFun hxs j

/-- Rows outside the sum of the two geometric critical-value sets are regular. -/
theorem isPrimeRegularLevel_adjoinMorsePhase {p n r : ℕ} [Fact p.Prime] [NeZero p]
    (hr : 2 ≤ r) (hrp : r < p) {b : ZMod p} (hb : b ≠ 0)
    {g : MvPolynomial (Fin n) (ZMod p)} {t : ZMod p}
    (E : Finset (AlgebraicClosure (ZMod p)))
    (hE : criticalValues (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) g) ⊆ E)
    (ht : t ∉ morseExceptionalRows (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) r E b) :
    IsPrimeRegularLevel (adjoinMorsePhase r b g) t := by
  let K := AlgebraicClosure (ZMod p)
  let φ := algebraMap (ZMod p) K
  let G := MvPolynomial.map φ g
  change φ t ∉ criticalValues (MvPolynomial.map φ (adjoinMorsePhase r b g))
  rw [map_adjoinMorsePhase]
  rintro ⟨x, hx, heval⟩
  have hz : ∀ i, (pderiv i G).eval (x ∘ Fin.succ) = 0 := fun i => by
    simpa only [pderiv_succ_adjoinMorsePhase, eval_rename] using hx i.succ
  have hbK : φ b ≠ 0 := (map_ne_zero φ).mpr hb
  have hrK : (r : K) ≠ 0 := fun h =>
    (not_le_of_gt hrp) (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff K p r).mp h))
  have hscalar : φ b * ((r : K) * (x 0)^(r-1) - 1) = 0 := by
    simpa only [pderiv_zero_adjoinMorsePhase, map_mul, map_pow, map_sub, eval_C, eval_X, map_one]
      using hx 0
  apply ht
  exact (mem_morseExceptionalRows_iff φ r E b t).mpr
    ⟨_, hE ⟨x ∘ Fin.succ, hz, rfl⟩, _,
      eval_mem_morseAuxiliaryCriticalValues hr hrK ((mul_eq_zero.mp hscalar).resolve_left hbK),
      by rw [← heval]; exact eval_adjoinMorsePhase r (φ b) G x⟩

/-- Decomposing a tuple into its distinguished coordinate and its remaining
coordinates identifies the centered joined counts with a convolution. -/
theorem affinePolynomialLevelCount_adjoinMorsePhase {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (r : ℕ) (b : K) (g : MvPolynomial (Fin n) K) (t : K) (m : ℝ) :
    ∑ s : K, ((affinePolynomialLevelCount g s : ℝ) - m) * centeredMorseValueCount r b (t-s) =
      (affinePolynomialLevelCount (adjoinMorsePhase r b g) t : ℝ) - (Fintype.card K : ℝ)^n := by
  let e : (Fin (n+1) → K) ≃ (Fin n → K) × K :=
    (Fin.consEquiv (fun _ => K)).symm.trans (Equiv.prodComm K (Fin n → K))
  let f (z : (Fin n → K) × K) : K := g.eval z.1 + b * (morseAuxiliaryPolynomial r).eval z.2
  have hf : f ∘ e = fun x => (adjoinMorsePhase r b g).eval x := by
    funext x
    exact (eval_adjoinMorsePhase r b g x).symm
  have hcount := finiteValueCount_comp_equiv e f t
  rw [hf, finiteValueCount_eval_eq_affinePolynomialLevelCount] at hcount
  have h := sum_mul_centeredMorseValueCount (fun x => g.eval x) r b t m
  change _ = (finiteValueCount f t : ℝ) - Fintype.card (Fin n → K) at h
  simpa only [finiteValueCount_eval_eq_affinePolynomialLevelCount, ← hcount, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow] using h

end

end Birch
