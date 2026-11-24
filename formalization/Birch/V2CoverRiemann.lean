import Birch.MajorArcLatticePoisson
import Birch.RealOscillationDecay
import Birch.V2CoverFourthMoment
import Birch.V2CoverLocal
import Birch.V2CoverScale
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Riemann sums on the major arcs for a polynomial cover

The finite-scale univariate approximation in Section 6 of `v2.tex` holds
for a polynomial of degree `e`, a fixed radius multiplier `B > 0`, every
`Y ≥ 1`, and every nonzero modulus. The proof uses interval integration
and an elementary Lipschitz bound on the polynomial phase.
-/

open Filter MeasureTheory Polynomial Set ZMod
open scoped Polynomial

namespace Birch

noncomputable section

/-- Left endpoint sums on a grid that covers the interval up to one step
at each endpoint. -/
theorem norm_intervalRiemann_sub_integral_le {f : ℝ → ℂ}
    (hf : Continuous f) (hunit : ∀ t, ‖f t‖ ≤ 1)
    {B L h b : ℝ} {N : ℕ} (hh : 0 < h) (hhB : h ≤ B) (hL : 0 ≤ L)
    (hlip : ∀ s ∈ Icc (-B) (2 * B), ∀ t ∈ Icc (-B) (2 * B),
      ‖f s - f t‖ ≤ L * |s - t|)
    (hb₁ : -B ≤ b) (hb₂ : b ≤ -B + h)
    (hN₁ : B ≤ b + h * N) (hN₂ : b + h * N ≤ B + h) :
    ‖h • (∑ k ∈ Finset.range N, f (b + h * k)) - ∫ t in (-B)..B, f t‖ ≤
      (2 + 3 * B * L) * h := by
  let z (k : ℕ) := b + h * k
  have hz₀ : z 0 = b := by simp [z]
  have hdist (k : ℕ) : z (k + 1) - z k = h := by
    dsimp only [z]
    push_cast
    ring
  have hmono : Monotone z := fun _ _ hkm =>
    add_le_add (le_refl b) (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkm) hh.le)
  have hbox (k : ℕ) (hk : k ≤ N) : z k ∈ Icc (-B) (2 * B) :=
    ⟨hb₁.trans (hz₀ ▸ hmono (Nat.zero_le k)), (hmono hk).trans (by
      dsimp only [z]
      linarith)⟩
  have hcell (k : ℕ) (hk : k < N) :
      ‖h • f (z k) - ∫ t in (z k)..(z (k + 1)), f t‖ ≤ L * h ^ 2 := by
    have hconst : (∫ _ in (z k)..(z (k + 1)), f (z k)) = h • f (z k) := by
      rw [intervalIntegral.integral_const, hdist]
    rw [← hconst, ← intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)]
    have hpoint (t : ℝ) (ht : t ∈ uIoc (z k) (z (k + 1))) :
        ‖f (z k) - f t‖ ≤ L * h := by
      rw [uIoc_of_le (hmono (Nat.le_succ k))] at ht
      have htbox : t ∈ Icc (-B) (2 * B) :=
        ⟨(hbox k hk.le).1.trans ht.1.le, ht.2.trans (hbox (k + 1) hk).2⟩
      apply (hlip (z k) (hbox k hk.le) t htbox).trans
      apply mul_le_mul_of_nonneg_left _ hL
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.1.le), ← hdist k]
      exact sub_le_sub_right ht.2 _
    have hcell := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [hdist, abs_of_pos hh] at hcell
    simpa only [pow_two, mul_assoc] using hcell
  have hsum : ‖h • (∑ k ∈ Finset.range N, f (z k)) - ∫ t in b..(z N), f t‖ ≤
      (N : ℝ) * (L * h ^ 2) := by
    rw [← hz₀, ← intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hf.intervalIntegrable (z k) (z (k + 1))), Finset.smul_sum, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ Finset.range N, ‖h • f (z k) - ∫ t in (z k)..(z (k + 1)), f t‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range N, L * h ^ 2 :=
        Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
      _ = _ := by simp [nsmul_eq_mul]
  have hsum' : ‖h • (∑ k ∈ Finset.range N, f (z k)) - ∫ t in b..(z N), f t‖ ≤
      3 * B * L * h := by
    apply hsum.trans
    have hlength : (N : ℝ) * h ≤ 3 * B := by linarith [hN₂, hb₁, hhB]
    calc
      _ = ((N : ℝ) * h) * (L * h) := by ring
      _ ≤ (3 * B) * (L * h) := mul_le_mul_of_nonneg_right hlength (mul_nonneg hL hh.le)
      _ = _ := by ring
  have hdiff : (∫ t in b..(z N), f t) - (∫ t in (-B)..B, f t) =
      (∫ t in b..(-B), f t) + (∫ t in B..(z N), f t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable b B)
      (hf.intervalIntegrable B (z N)),
      ← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable b (-B))
        (hf.intervalIntegrable (-B) B)]
    abel
  have hedge₁ : ‖∫ t in b..(-B), f t‖ ≤ h := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t (_ : t ∈ uIoc b (-B)) => hunit t)
    rw [one_mul, abs_of_nonpos (sub_nonpos.mpr hb₁)] at he
    exact he.trans (by linarith)
  have hedge₂ : ‖∫ t in B..(z N), f t‖ ≤ h := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t (_ : t ∈ uIoc B (z N)) => hunit t)
    rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hN₁)] at he
    exact he.trans (by change b + h * (N : ℝ) - B ≤ h; linarith)
  have hedge : ‖(∫ t in b..(z N), f t) - (∫ t in (-B)..B, f t)‖ ≤ h + h := by
    rw [hdiff]
    exact (norm_add_le _ _).trans (add_le_add hedge₁ hedge₂)
  change ‖h • (∑ k ∈ Finset.range N, f (z k)) - ∫ t in (-B)..B, f t‖ ≤ _
  calc
    _ = ‖(h • (∑ k ∈ Finset.range N, f (z k)) - ∫ t in b..(z N), f t) +
        ((∫ t in b..(z N), f t) - ∫ t in (-B)..B, f t)‖ := by
          congr 1
          abel
    _ ≤ (3 * B * L * h) + (h + h) := (norm_add_le _ _).trans (add_le_add hsum' hedge)
    _ = _ := by ring


private theorem mem_intBox_div_iff {B Y : ℝ} (hY : 0 < Y) (y : ℤ) :
    y ∈ Finset.Icc (-⌊B * Y⌋) ⌊B * Y⌋ ↔ -B ≤ (y : ℝ) / Y ∧ (y : ℝ) / Y ≤ B := by
  rw [Finset.mem_Icc, neg_le, Int.le_floor, Int.le_floor, Int.cast_neg,
    le_div_iff₀ hY, div_le_iff₀ hY]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, h₂⟩

/-- Riemann approximation for a single residue class, on the physical
interval of radius `B` after dividing the lattice points by `Y`. -/
theorem norm_coverResidueSum_sub_integral_le {f : ℝ → ℂ}
    (hf : Continuous f) (hunit : ∀ t, ‖f t‖ ≤ 1)
    {B L Y : ℝ} (hY : 0 < Y) (hL : 0 ≤ L)
    (hlip : ∀ s ∈ Icc (-B) (2 * B), ∀ t ∈ Icc (-B) (2 * B),
      ‖f s - f t‖ ≤ L * |s - t|)
    {q : ℕ} [NeZero q] (hstep : (q : ℝ) / Y ≤ B) (v : ZMod q) :
    ‖((q : ℝ) / Y) • (∑ y ∈ (Finset.Icc (-⌊B * Y⌋) ⌊B * Y⌋).filter
      (fun y : ℤ => (y : ZMod q) = v), f ((y : ℝ) / Y)) - ∫ t in (-B)..B, f t‖ ≤
        (2 + 3 * B * L) * ((q : ℝ) / Y) := by
  let h : ℝ := (q : ℝ) / Y
  have hh : 0 < h := div_pos (by exact_mod_cast NeZero.pos q) hY
  let r : ℤ := v.val
  let s : ℝ := (r : ℝ) / Y
  let m : ℤ := ⌈(-B - s) / h⌉
  let M : ℤ := ⌊(B - s) / h⌋ + 1
  have hm₁ : -B - s ≤ (m : ℝ) * h :=
    (div_le_iff₀ hh).mp (Int.le_ceil _)
  have hm₂ : (m : ℝ) * h < -B - s + h := by
    apply (lt_div_iff₀ hh).mp
    rw [add_div, div_self hh.ne']
    exact Int.ceil_lt_add_one _
  have hM₁ : B - s < (M : ℝ) * h := by
    apply (div_lt_iff₀ hh).mp
    simpa only [M, Int.cast_add, Int.cast_one] using Int.lt_floor_add_one ((B - s) / h)
  have hM₂ : (M : ℝ) * h ≤ B - s + h := by
    apply (le_div_iff₀ hh).mp
    rw [add_div, div_self hh.ne']
    simp only [M, Int.cast_add, Int.cast_one]
    exact add_le_add (Int.floor_le _) (le_refl 1)
  have hmM : m ≤ M := by
    have hB : h ≤ B := hstep
    exact_mod_cast (le_of_lt (lt_of_mul_lt_mul_right (by linarith [hm₂, hM₁]) hh.le) :
      (m : ℝ) ≤ (M : ℝ))
  let N := (M - m).toNat
  have hNint : (N : ℤ) = M - m := Int.toNat_of_nonneg (sub_nonneg.mpr hmM)
  have hNreal : (N : ℝ) = (M : ℝ) - (m : ℝ) := by exact_mod_cast hNint
  let b : ℝ := s + h * (m : ℝ)
  have hb₁ : -B ≤ b := by dsimp only [b]; linarith [hm₁]
  have hb₂ : b ≤ -B + h := by dsimp only [b]; linarith [hm₂]
  have hend : b + h * N = s + h * (M : ℝ) := by
    rw [hNreal]
    dsimp only [b]
    ring
  have hN₁ : B ≤ b + h * N := by rw [hend]; linarith [hM₁]
  have hN₂ : b + h * N ≤ B + h := by rw [hend]; linarith [hM₂]
  have hcast (k : ℤ) : ((r + (q : ℤ) * k : ℤ) : ℝ) / Y = s + h * (k : ℝ) := by
    simp only [h, s, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    ring
  have hgrid (k : ℤ) : (r + (q : ℤ) * k) ∈ Finset.Icc (-⌊B * Y⌋) ⌊B * Y⌋ ↔
      m ≤ k ∧ k < M := by
    have hkM : k < M ↔ (k : ℝ) ≤ (B - s) / h := by
      dsimp only [M]
      rw [Int.lt_add_one_iff, Int.le_floor]
    rw [mem_intBox_div_iff hY, hcast, hkM]
    dsimp only [m]
    rw [Int.ceil_le, div_le_iff₀ hh, le_div_iff₀ hh]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, by linarith⟩
  have hr : (r : ZMod q) = v := by
    simp only [r, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hsum : (∑ i ∈ Finset.range N, f (b + h * i)) =
      ∑ y ∈ (Finset.Icc (-⌊B * Y⌋) ⌊B * Y⌋).filter (fun y : ℤ => (y : ZMod q) = v),
        f ((y : ℝ) / Y) := by
    refine Finset.sum_bij (fun i _ => r + (q : ℤ) * (m + (i : ℤ))) ?_ ?_ ?_ ?_
    · intro i hi
      have hi' : (i : ℤ) < (N : ℤ) := by exact_mod_cast Finset.mem_range.mp hi
      refine Finset.mem_filter.mpr ⟨(hgrid _).mpr ⟨by omega, by omega⟩, ?_⟩
      simp [hr]
    · intro i _ j _ hij
      have hq : (q : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne q
      have he := mul_left_cancel₀ hq (add_left_cancel hij)
      omega
    · intro y hy
      obtain ⟨hybox, hyv⟩ := Finset.mem_filter.mp hy
      have hdiv : (q : ℤ) ∣ y - r :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub r y q).mp (hr.trans hyv.symm)
      obtain ⟨k, hk⟩ := hdiv
      have hyk : y = r + (q : ℤ) * k := by omega
      have hkm := (hgrid k).mp (hyk ▸ hybox)
      let i := (k - m).toNat
      have hi : (i : ℤ) = k - m := Int.toNat_of_nonneg (sub_nonneg.mpr hkm.1)
      have hil : (i : ℤ) < (N : ℤ) := by omega
      refine ⟨i, Finset.mem_range.mpr (by exact_mod_cast hil), ?_⟩
      rw [hyk, show m + (i : ℤ) = k by omega]
    · intro i _
      apply congrArg f
      rw [hcast, Int.cast_add, Int.cast_natCast]
      dsimp only [b]
      ring
  rw [← hsum]
  exact norm_intervalRiemann_sub_integral_le hf hunit hh hstep hL hlip hb₁ hb₂ hN₁ hN₂


/-- The real factor using the whole polynomial at finite scale. -/
def coverFiniteRealOscillation (g : ℤ[X]) (e : ℕ) (B Y γ : ℝ) : ℂ :=
  ∫ t in (-B)..B, phase (-γ * (g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e))

private def coverPolynomialSlopeBound (g : ℤ[X]) (e : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (e + 1), |(g.coeff i : ℝ)| * (i : ℝ) * (2 * B) ^ (i - 1)

private theorem coverPolynomialSlopeBound_nonneg (g : ℤ[X]) (e : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ coverPolynomialSlopeBound g e B := by
  apply Finset.sum_nonneg
  intro i _
  positivity

private theorem scaledCoverPolynomial_eq_sum {g : ℤ[X]} {e : ℕ}
    (hg : g.natDegree = e) (Y t : ℝ) :
    g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e =
      ∑ i ∈ Finset.range (e + 1), ((g.coeff i : ℝ) * (Y ^ i / Y ^ e)) * t ^ i := by
  rw [eval₂_eq_sum_range, hg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_pow, Int.coe_castRingHom]
  ring

private theorem abs_scaledCoverPolynomial_sub_le {g : ℤ[X]} {e : ℕ}
    (hg : g.natDegree = e) {B Y s t : ℝ} (hB : 0 ≤ B) (hY : 1 ≤ Y)
    (hs : s ∈ Icc (-B) (2 * B)) (ht : t ∈ Icc (-B) (2 * B)) :
    |g.eval₂ (Int.castRingHom ℝ) (Y * s) / Y ^ e -
        g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e| ≤ coverPolynomialSlopeBound g e B * |s - t| := by
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  have hsabs : |s| ≤ 2 * B := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have htabs : |t| ≤ 2 * B := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  rw [scaledCoverPolynomial_eq_sum hg Y s, scaledCoverPolynomial_eq_sum hg Y t,
    ← Finset.sum_sub_distrib, coverPolynomialSlopeBound, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hie : i ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hratio : Y ^ i / Y ^ e ≤ 1 := by
    apply (div_le_iff₀ (pow_pos hY₀ _)).2
    simpa only [one_mul] using pow_le_pow_right₀ hY hie
  have hpow : |s ^ i - t ^ i| ≤ |s - t| * (i : ℝ) * (2 * B) ^ (i - 1) := by
    apply (abs_pow_sub_pow_le (a := s) (b := t) (n := i)).trans
    gcongr
    exact max_le hsabs htabs
  rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Y ^ i / Y ^ e)]
  calc
    _ ≤ |(g.coeff i : ℝ)| * |s ^ i - t ^ i| :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) hratio) (abs_nonneg _)
    _ ≤ |(g.coeff i : ℝ)| * (|s - t| * (i : ℝ) * (2 * B) ^ (i - 1)) :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ = _ := by ring


private theorem cast_eval_intPolynomial {R : Type*} [CommRing R] (g : ℤ[X]) (y : ℤ) :
    ((g.eval y : ℤ) : R) = g.eval₂ (Int.castRingHom R) (y : R) := by
  rw [eval₂_eq_eval_map]
  exact (eval_intCast_map (Int.castRingHom R) g y).symm

private theorem norm_coverYSum_le_box (g : ℤ[X]) {L : ℝ} (hL : 0 ≤ L) (α : ℝ) :
    ‖coverYSum g L α‖ ≤ 2 * L + 1 := by
  let I := Finset.Icc (-⌊L⌋) ⌊L⌋
  have hfloor : 0 ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL
  have hcard : (I.card : ℝ) = (⌊L⌋ : ℝ) + 1 - (-⌊L⌋ : ℤ) := by
    have h := Int.card_Icc_of_le (a := -⌊L⌋) (b := ⌊L⌋) (by omega)
    exact_mod_cast h
  calc
    _ ≤ ∑ y ∈ I, ‖phase (-α * ((g.eval y : ℤ) : ℝ))‖ := norm_sum_le _ _
    _ = (I.card : ℝ) := by simp [norm_phase]
    _ ≤ _ := by rw [hcard]; push_cast; linarith [Int.floor_le L]

private theorem coverYSum_eq_residueSums (g : ℤ[X]) (e : ℕ) {B Y : ℝ} (hY : 0 < Y)
    (q : ℕ) [NeZero q] (a : ℤ) (γ : ℝ) :
    let f (t : ℝ) := phase (-γ * (g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e))
    let χ (v : ZMod q) := stdAddChar (-((a : ZMod q) * g.eval₂ (Int.castRingHom (ZMod q)) v))
    coverYSum g (B * Y) ((a : ℝ) / q + γ / Y ^ e) =
      ∑ v : ZMod q, χ v * ∑ y ∈ (Finset.Icc (-⌊B * Y⌋) ⌊B * Y⌋).filter
        (fun y : ℤ => (y : ZMod q) = v), f ((y : ℝ) / Y) := by
  let f (t : ℝ) := phase (-γ * (g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e))
  let χ (v : ZMod q) := stdAddChar (-((a : ZMod q) * g.eval₂ (Int.castRingHom (ZMod q)) v))
  let I := Finset.Icc (-⌊B * Y⌋) ⌊B * Y⌋
  have hterm (y : ℤ) :
      phase (-((a : ℝ) / q + γ / Y ^ e) * ((g.eval y : ℤ) : ℝ)) =
        χ (y : ZMod q) * f ((y : ℝ) / Y) := by
    have harg :
        -((a : ℝ) / q + γ / Y ^ e) * ((g.eval y : ℤ) : ℝ) =
          ((-a * g.eval y : ℤ) : ℝ) / q +
            -γ * (g.eval₂ (Int.castRingHom ℝ) (Y * ((y : ℝ) / Y)) / Y ^ e) := by
      rw [show Y * ((y : ℝ) / Y) = (y : ℝ) by field_simp [hY.ne'],
        ← cast_eval_intPolynomial]
      push_cast
      ring
    rw [harg, phase_add, phase_int_div]
    simp only [χ, f, Int.cast_mul, Int.cast_neg, cast_eval_intPolynomial g y, neg_mul]
  change (∑ y ∈ I, phase (-((a : ℝ) / q + γ / Y ^ e) * ((g.eval y : ℤ) : ℝ))) = _
  simp_rw [hterm, Finset.mul_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun y : ℤ => (y : ZMod q))
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y hy
  rw [(Finset.mem_filter.mp hy).2]

/-- The normalized cover sum on a major arc has the expected complete sum
and finite-scale real factor, with error uniform in the numerator and modulus. -/
theorem coverYSum_major_approximation (g : ℤ[X]) {e : ℕ} (hg : g.natDegree = e)
    {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ), 1 ≤ Y → ∀ (q : ℕ) [NeZero q] (a : ℤ) (γ : ℝ),
      ‖(Y : ℂ)⁻¹ * coverYSum g (B * Y) ((a : ℝ) / q + γ / Y ^ e) -
          coverCompleteSum g q (a : ZMod q) * coverFiniteRealOscillation g e B Y γ‖ ≤
        C * (1 + |γ|) * ((q : ℝ) / Y) := by
  let K := 2 * Real.pi * coverPolynomialSlopeBound g e B
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity) (coverPolynomialSlopeBound_nonneg g e hB.le)
  refine ⟨5 + 3 * B * K, by linarith [mul_nonneg hB.le hK], ?_⟩
  intro Y hY q _ a γ
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  let h : ℝ := (q : ℝ) / Y
  have hh : 0 < h := div_pos hq hY₀
  let f (t : ℝ) := phase (-γ * (g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e))
  let J : ℂ := coverFiniteRealOscillation g e B Y γ
  have hJ : ‖J‖ ≤ 2 * B := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t (_ : t ∈ uIoc (-B) B) => (norm_phase (-γ *
        (g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e))).le)
    simpa only [J, coverFiniteRealOscillation, one_mul, sub_neg_eq_add,
      abs_of_nonneg (add_nonneg hB.le hB.le), two_mul] using hi
  by_cases hstep : h ≤ B
  · let χ (v : ZMod q) := stdAddChar (-((a : ZMod q) * g.eval₂ (Int.castRingHom (ZMod q)) v))
    let S (v : ZMod q) := ∑ y ∈ (Finset.Icc (-⌊B * Y⌋) ⌊B * Y⌋).filter
      (fun y : ℤ => (y : ZMod q) = v), f ((y : ℝ) / Y)
    have hf : Continuous f := by
      dsimp only [f, phase]
      fun_prop
    have hχ (v : ZMod q) : ‖χ v‖ = 1 := by
      dsimp only [χ]
      rw [stdAddChar_apply]
      exact (ZMod.toCircle (N := q) _).norm_coe
    have hlip : ∀ s ∈ Icc (-B) (2 * B), ∀ t ∈ Icc (-B) (2 * B),
        ‖f s - f t‖ ≤ (K * |γ|) * |s - t| := by
      intro s hs t ht
      unfold f
      have he := norm_phase_sub_le (-γ * (g.eval₂ (Int.castRingHom ℝ) (Y * s) / Y ^ e))
        (-γ * (g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e))
      rw [← mul_sub, abs_mul, abs_neg] at he
      apply he.trans
      have hp := abs_scaledCoverPolynomial_sub_le hg hB.le hY hs ht
      have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * Real.pi * |γ|)
      dsimp only [K]
      convert hh using 1 <;> ring
    have hres (v : ZMod q) : ‖h • S v - J‖ ≤ (2 + 3 * B * (K * |γ|)) * h :=
      norm_coverResidueSum_sub_integral_le hf (fun t => (norm_phase _).le)
        hY₀ (mul_nonneg hK (abs_nonneg _)) hlip hstep v
    have hT : coverYSum g (B * Y) ((a : ℝ) / q + γ / Y ^ e) =
        ∑ v, χ v * S v := coverYSum_eq_residueSums g e hY₀ q a γ
    have hV : coverCompleteSum g q (a : ZMod q) = (q : ℂ)⁻¹ * ∑ v, χ v := rfl
    have hsmul (v : ZMod q) :
        (Y : ℂ)⁻¹ * (χ v * S v) = (q : ℂ)⁻¹ * (χ v * (h • S v)) := by
      simp only [h, Algebra.smul_def]
      change (Y : ℂ)⁻¹ * (χ v * S v) =
        (q : ℂ)⁻¹ * (χ v * ((((q : ℝ) / Y : ℝ) : ℂ) * S v))
      rw [Complex.ofReal_div, Complex.ofReal_natCast]
      have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
      have hY' : (Y : ℂ) ≠ 0 := by exact_mod_cast hY₀.ne'
      field_simp
    have heq : (Y : ℂ)⁻¹ * coverYSum g (B * Y) ((a : ℝ) / q + γ / Y ^ e) -
        coverCompleteSum g q (a : ZMod q) * J =
        (q : ℂ)⁻¹ * ∑ v, χ v * (h • S v - J) := by
      rw [hT, hV, Finset.mul_sum]
      simp_rw [hsmul]
      rw [← Finset.mul_sum, mul_assoc, ← mul_sub,
        Finset.sum_mul, ← Finset.sum_sub_distrib]
      simp only [mul_sub]
    change ‖_ - _ * J‖ ≤ _
    rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
    have hbody : ‖∑ v, χ v * (h • S v - J)‖ ≤
        (q : ℝ) * ((2 + 3 * B * (K * |γ|)) * h) := by
      calc
        _ ≤ ∑ v, ‖χ v * (h • S v - J)‖ := norm_sum_le _ _
        _ ≤ ∑ _ : ZMod q, (2 + 3 * B * (K * |γ|)) * h := by
          apply Finset.sum_le_sum
          intro v _
          rw [norm_mul, hχ, one_mul]
          exact hres v
        _ = _ := by simp [ZMod.card, nsmul_eq_mul]
    calc
      _ ≤ (q : ℝ)⁻¹ * ((q : ℝ) * ((2 + 3 * B * (K * |γ|)) * h)) :=
        mul_le_mul_of_nonneg_left hbody (inv_nonneg.mpr hq.le)
      _ = (2 + 3 * B * (K * |γ|)) * h := by
        rw [← mul_assoc, inv_mul_cancel₀ hq.ne', one_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        nlinarith [mul_nonneg hB.le hK, abs_nonneg γ]
  · let α := (a : ℝ) / q + γ / Y ^ e
    have hsum : ‖(Y : ℂ)⁻¹ * coverYSum g (B * Y) α‖ ≤ 2 * B + Y⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY₀]
      calc
        _ ≤ Y⁻¹ * (2 * (B * Y) + 1) :=
          mul_le_mul_of_nonneg_left (norm_coverYSum_le_box g (by positivity) α) (by positivity)
        _ = _ := by field_simp
    have hcomplete : ‖coverCompleteSum g q (a : ZMod q) * J‖ ≤ 2 * B := by
      rw [norm_mul]
      exact (mul_le_mul (norm_coverCompleteSum_le_one g q (a : ZMod q)) hJ
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hInv : Y⁻¹ ≤ h := by
      have hq₁ : 1 ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
      rw [← one_div]
      exact div_le_div_of_nonneg_right hq₁ hY₀.le
    calc
      _ ≤ (2 * B + Y⁻¹) + 2 * B := (norm_sub_le _ _).trans (add_le_add hsum hcomplete)
      _ ≤ 5 * h := by linarith [lt_of_not_ge hstep]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        nlinarith [mul_nonneg hB.le hK, abs_nonneg γ]

/-- The same approximation on the scale `Y = P^(d/e)` of Section 6. -/
theorem coverYSum_major_approximation_at_scale (g : ℤ[X]) {d e : ℕ}
    (he : 0 < e) (hg : g.natDegree = e) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℝ), 1 ≤ P → ∀ (q : ℕ) [NeZero q] (a : ℤ) (γ : ℝ),
      let Y : ℝ := P ^ ((d : ℝ) / e)
      ‖(Y : ℂ)⁻¹ * coverYSum g (B * Y) ((a : ℝ) / q + γ / P ^ d) -
          coverCompleteSum g q (a : ZMod q) * coverFiniteRealOscillation g e B Y γ‖ ≤
        C * (1 + |γ|) * ((q : ℝ) / Y) := by
  obtain ⟨C, hC, hbound⟩ := coverYSum_major_approximation g hg hB
  refine ⟨C, hC, ?_⟩
  intro P hP q _ a γ
  let Y := P ^ ((d : ℝ) / e)
  have hY : 1 ≤ Y := Real.one_le_rpow hP (by positivity)
  have he₀ : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hpow : Y ^ e = P ^ d := by
    dsimp only [Y]
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ P), div_mul_cancel₀ _ he₀, Real.rpow_natCast]
  simpa only [hpow] using hbound Y hY q a γ


private theorem abs_scaledCoverPolynomial_sub_leading_le_on_box {g : ℤ[X]} {e : ℕ}
    (hg : g.natDegree = e) {B Y t : ℝ} (hY : 1 ≤ Y) (ht : |t| ≤ B) :
    |g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e - (g.leadingCoeff : ℝ) * t ^ e| ≤
      (∑ i ∈ Finset.range e, |(g.coeff i : ℝ)| * B ^ i) / Y := by
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  have hcoeff : g.coeff e = g.leadingCoeff := by rw [← hg, leadingCoeff]
  rw [scaledCoverPolynomial_eq_sum hg Y t, Finset.sum_range_succ, hcoeff,
    div_self (pow_ne_zero _ hY₀.ne'), mul_one, add_sub_cancel_right, Finset.sum_div]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hratio : Y ^ i / Y ^ e ≤ Y⁻¹ := by
    rw [← one_div]
    apply (div_le_div_iff₀ (pow_pos hY₀ _) hY₀).2
    rw [one_mul, ← pow_succ]
    exact pow_le_pow_right₀ hY (Finset.mem_range.mp hi)
  have hpow : |t| ^ i ≤ B ^ i := pow_le_pow_left₀ (abs_nonneg _) ht i
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Y ^ i / Y ^ e), abs_pow]
  calc
    _ ≤ |(g.coeff i : ℝ)| * Y⁻¹ * B ^ i :=
      mul_le_mul (mul_le_mul_of_nonneg_left hratio (abs_nonneg _)) hpow
        (pow_nonneg (abs_nonneg _) _) (by positivity)
    _ = _ := by ring

/-- The integral with the full polynomial differs from its leading-term
version by the lower-coefficient contribution on the physical interval. -/
theorem norm_coverFiniteRealOscillation_sub_leading_le (g : ℤ[X]) {e : ℕ}
    (hg : g.natDegree = e) {B Y : ℝ} (hB : 0 < B) (hY : 1 ≤ Y) (γ : ℝ) :
    ‖coverFiniteRealOscillation g e B Y γ -
        ∫ t in (-B)..B, phase (-γ * (g.leadingCoeff : ℝ) * t ^ e)‖ ≤
      4 * Real.pi * B * |γ| * ((∑ i ∈ Finset.range e, |(g.coeff i : ℝ)| * B ^ i) / Y) := by
  let G (t : ℝ) := g.eval₂ (Int.castRingHom ℝ) (Y * t) / Y ^ e
  let L (t : ℝ) := (g.leadingCoeff : ℝ) * t ^ e
  let C : ℝ := (∑ i ∈ Finset.range e, |(g.coeff i : ℝ)| * B ^ i) / Y
  let f (t : ℝ) := phase (-γ * G t)
  let l (t : ℝ) := phase (-γ * L t)
  have hf : Continuous f := by
    dsimp only [f, G, phase]
    fun_prop
  have hl : Continuous l := by
    dsimp only [l, L, phase]
    fun_prop
  suffices h : ‖(∫ t in (-B)..B, f t) - (∫ t in (-B)..B, l t)‖ ≤
      4 * Real.pi * B * |γ| * C by
    simpa only [coverFiniteRealOscillation, C, f, l, G, L, mul_assoc] using h
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hl.intervalIntegrable _ _)]
  have hpoint (t : ℝ) (ht : t ∈ uIoc (-B) B) : ‖f t - l t‖ ≤ 2 * Real.pi * |γ| * C := by
    rw [uIoc_of_le (by linarith : -B ≤ B)] at ht
    have htab : |t| ≤ B := abs_le.mpr ⟨ht.1.le, ht.2⟩
    have h := norm_phase_sub_le (-γ * G t) (-γ * L t)
    rw [← mul_sub, abs_mul, abs_neg] at h
    have hdiff : |G t - L t| ≤ C := abs_scaledCoverPolynomial_sub_leading_le_on_box hg hY htab
    apply h.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdiff
      (by positivity : 0 ≤ 2 * Real.pi * |γ|)
  calc
    _ ≤ (2 * Real.pi * |γ| * C) * |B - (-B)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = _ := by
      rw [sub_neg_eq_add, abs_of_nonneg (add_nonneg hB.le hB.le)]
      ring

end
end Birch
