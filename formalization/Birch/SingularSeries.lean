import Birch.Estimates
import Birch.LocalDensity
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The singular series and its local factors
-/

namespace Birch

open scoped BigOperators Topology
open Filter ZMod Nat

noncomputable section

variable {n q r : ℕ}

private def unitsCongr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Rˣ ≃ Sˣ where
  toFun := Units.map e.toMonoidHom
  invFun := Units.map e.symm.toMonoidHom
  left_inv u := Units.ext (e.symm_apply_apply u.val)
  right_inv u := Units.ext (e.apply_symm_apply u.val)

private def scaledUnitsCRT (h : q.Coprime r) : (ZMod q)ˣ × (ZMod r)ˣ ≃ (ZMod (q*r))ˣ :=
  let u := ((ZMod.isUnit_iff_coprime r q).2 h.symm).unit
  let v := ((ZMod.isUnit_iff_coprime q r).2 h).unit
  (Equiv.prodCongr (Equiv.mulLeft u) (Equiv.mulLeft v)).trans
    (MulEquiv.prodUnits.symm.toEquiv.trans (unitsCongr (ZMod.chineseRemainder h).symm))

private theorem scaledUnitsCRT_val [NeZero q] [NeZero r] (h : q.Coprime r)
    (u : (ZMod q)ˣ × (ZMod r)ˣ) :
    (scaledUnitsCRT h u).val = (r : ZMod (q*r))*↑u.1.val.val + (q : ZMod (q*r))*↑u.2.val.val := by
  apply (ZMod.chineseRemainder h).injective
  change (ZMod.chineseRemainder h) ((ZMod.chineseRemainder h).symm
    ((((ZMod.isUnit_iff_coprime r q).2 h.symm).unit * u.1).val,
     (((ZMod.isUnit_iff_coprime q r).2 h).unit * u.2).val)) = _
  rw [RingEquiv.apply_symm_apply]
  simp only [map_add, map_mul, map_natCast, Units.val_mul, IsUnit.unit_spec]
  apply Prod.ext
  · change (r : ZMod q) * ↑u.1 = (r : ZMod q) * (u.1.val.val : ZMod q) +
        (q : ZMod q) * (u.2.val.val : ZMod q)
    simp
  · change (q : ZMod r) * ↑u.2 = (r : ZMod r) * (u.1.val.val : ZMod r) +
        (q : ZMod r) * (u.2.val.val : ZMod r)
    simp

private theorem crt_fst_eq_castHom (h : q.Coprime r) (x : ZMod (q*r)) :
    (ZMod.chineseRemainder h x).1 = ZMod.castHom (dvd_mul_right q r) (ZMod q) x := by
  have hs : (RingHom.fst _ _).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_right q r) (ZMod q) := Subsingleton.elim _ _
  exact RingHom.congr_fun hs x

private theorem crt_snd_eq_castHom (h : q.Coprime r) (x : ZMod (q*r)) :
    (ZMod.chineseRemainder h x).2 = ZMod.castHom (dvd_mul_left r q) (ZMod r) x := by
  have hs : (RingHom.snd _ _).comp (ZMod.chineseRemainder h).toRingHom =
      ZMod.castHom (dvd_mul_left r q) (ZMod r) := Subsingleton.elim _ _
  exact RingHom.congr_fun hs x

private def vectorsCRT (h : q.Coprime r) :
    (Fin n → ZMod (q*r)) ≃ (Fin n → ZMod q) × (Fin n → ZMod r) :=
  (Equiv.piCongrRight (fun _ => (ZMod.chineseRemainder h).toEquiv)).trans
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => ZMod q) (fun _ => ZMod r))

/-- Chinese remainder decomposition with the unit numerator scaled in each factor. -/
theorem completeSum_crt_scaled [NeZero q] [NeZero r] (F : IntForm n) (h : q.Coprime r)
    (a : ZMod q) (b : ZMod r) :
    completeSum F (q*r) ((r : ZMod (q*r))*(a.val : ZMod (q*r)) +
      (q : ZMod (q*r))*(b.val : ZMod (q*r))) =
      completeSum F q a * completeSum F r b := by
  unfold completeSum
  let e := vectorsCRT (n := n) h
  let P (x : Fin n → ZMod q) := stdAddChar (a * residueEval F q x)
  let Q (x : Fin n → ZMod r) := stdAddChar (b * residueEval F r x)
  have hphase (x : Fin n → ZMod (q*r)) :
      stdAddChar (((r : ZMod (q*r))*(a.val : ZMod (q*r)) +
        (q : ZMod (q*r))*(b.val : ZMod (q*r))) * residueEval F (q*r) x) =
        P (e x).1 * Q (e x).2 := by
    rw [add_mul, AddChar.map_add_eq_mul]
    simp only [mul_assoc]
    rw [stdAddChar_mul_factor (Nat.mul_comm q r) (dvd_mul_right q r),
      stdAddChar_mul_factor rfl (dvd_mul_left r q)]
    simp only [map_mul, map_natCast, ZMod.natCast_zmod_val, hom_residueEval, P, Q]
    simp_rw [← crt_fst_eq_castHom h, ← crt_snd_eq_castHom h]
    rfl
  simp_rw [hphase]
  rw [← Equiv.sum_comp e.symm]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  push_cast
  rw [mul_pow]
  change (((q : ℂ)^n * (r : ℂ)^n))⁻¹ * ((∑ x, P x) * (∑ x, Q x)) =
    (((q : ℂ)^n)⁻¹ * (∑ x, P x)) * (((r : ℂ)^n)⁻¹ * (∑ x, Q x))
  field_simp

/-- A complete sum with a unit numerator factors at coprime moduli,
with unit numerators in both factors. -/
theorem completeSum_units_product [NeZero q] [NeZero r] (F : IntForm n) (h : q.Coprime r)
    (a : (ZMod (q*r))ˣ) :
    ∃ (b : (ZMod q)ˣ) (c : (ZMod r)ˣ),
      completeSum F (q*r) a.val = completeSum F q b.val * completeSum F r c.val := by
  obtain ⟨⟨b, c⟩, rfl⟩ := (scaledUnitsCRT h).surjective a
  refine ⟨b, c, ?_⟩
  rw [scaledUnitsCRT_val]
  exact completeSum_crt_scaled F h b.val c.val

/-- The conductor coefficients of the singular series are multiplicative. -/
theorem unitConductorSum_mul [NeZero q] [NeZero r] (F : IntForm n) (h : q.Coprime r) :
    unitConductorSum F (q*r) = unitConductorSum F q * unitConductorSum F r := by
  unfold unitConductorSum
  rw [← (scaledUnitsCRT h).sum_comp]
  simp_rw [scaledUnitsCRT_val, completeSum_crt_scaled F h]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]


/-- The conductor coefficient extended to all naturals by setting the value at zero to zero. -/
def singularSeriesTerm (F : IntForm n) (m : ℕ) : ℂ :=
  if h : m = 0 then 0 else @unitConductorSum n F m ⟨h⟩

private theorem singularSeriesTerm_posModulus (F : IntForm n) (m : ℕ) [NeZero m] :
    singularSeriesTerm F m = unitConductorSum F m := dite_eq_right (NeZero.ne m)

private theorem summable_norm_singularSeriesTerm (F : IntForm n)
    (hA : Summable (fun m : ℕ => ‖unitConductorSum F (m+1)‖)) :
    Summable (fun m : ℕ => ‖singularSeriesTerm F m‖) := by
  rw [← summable_nat_add_iff 1]
  simpa only [singularSeriesTerm_posModulus] using hA

private theorem tsum_singularSeriesTerm (F : IntForm n)
    (hA : Summable (fun m : ℕ => ‖singularSeriesTerm F m‖)) :
    (∑' m : ℕ, singularSeriesTerm F m) = singularSeries F := by
  rw [hA.of_norm.tsum_eq_zero_add]
  simp only [singularSeriesTerm, dite_eq_left, zero_add]
  rfl

private theorem singularSeriesTerm_mul (F : IntForm n) {a b : ℕ} (h : a.Coprime b) :
    singularSeriesTerm F (a*b) = singularSeriesTerm F a * singularSeriesTerm F b := by
  by_cases ha : a = 0
  · simp [ha, singularSeriesTerm]
  by_cases hb : b = 0
  · simp [hb, singularSeriesTerm]
  let : NeZero a := ⟨ha⟩
  let : NeZero b := ⟨hb⟩
  simpa only [singularSeriesTerm_posModulus] using unitConductorSum_mul F h

/-- The prime factor given by the conductor series of its powers. -/
def localSeriesFactor (F : IntForm n) (p : Nat.Primes) : ℂ :=
  ∑' j : ℕ, singularSeriesTerm F ((p : ℕ)^j)

/-- The Euler product identity for the absolutely convergent singular series. -/
theorem hasProd_localSeriesFactor (F : IntForm n)
    (hA : Summable (fun m : ℕ => ‖unitConductorSum F (m+1)‖)) :
    HasProd (localSeriesFactor F) (singularSeries F) := by
  have hsum := summable_norm_singularSeriesTerm F hA
  have hOne : singularSeriesTerm F 1 = 1 := by
    rw [singularSeriesTerm_posModulus, unitConductorSum_one]
  unfold localSeriesFactor
  rw [← tsum_singularSeriesTerm F hsum]
  exact EulerProduct.eulerProduct_hasProd hOne (fun h => singularSeriesTerm_mul F h)
    hsum (by simp [singularSeriesTerm])

private theorem primePowerSucc_injective :
    Function.Injective (fun x : Σ _ : Nat.Primes, ℕ => (x.1 : ℕ) ^ (x.2 + 1)) := by
  rintro ⟨p,i⟩ ⟨q,j⟩ h
  change (p : ℕ)^(i+1) = (q : ℕ)^(j+1) at h
  have hpq : (p : ℕ) ∣ (q : ℕ) := p.prop.dvd_of_dvd_pow (h ▸ dvd_pow_self _ (Nat.succ_ne_zero i))
  have hqp : (q : ℕ) ∣ (p : ℕ) := q.prop.dvd_of_dvd_pow (h.symm ▸ dvd_pow_self _ (Nat.succ_ne_zero j))
  have he : p = q := Subtype.ext (dvd_antisymm hpq hqp)
  subst q
  have he' : i+1 = j+1 := Nat.pow_right_injective p.prop.two_le h
  have hij : i=j := Nat.succ_inj.mp he'
  subst j
  rfl

set_option maxHeartbeats 600000 in
private theorem summable_primePowerTails (F : IntForm n)
    (hA : Summable (fun m : ℕ => ‖singularSeriesTerm F m‖)) :
    (∀ p : Nat.Primes, Summable (fun k : ℕ => ‖singularSeriesTerm F ((p : ℕ)^(k+1))‖)) ∧
      Summable (fun p : Nat.Primes => ∑' k : ℕ, ‖singularSeriesTerm F ((p : ℕ)^(k+1))‖) := by
  have hn : Summable (fun m : ℕ => ‖singularSeriesTerm F m‖₊) := NNReal.summable_coe.mp hA
  have hσ : Summable (fun x : Σ _ : Nat.Primes, ℕ =>
      ‖singularSeriesTerm F ((x.1 : ℕ)^(x.2+1))‖) :=
    NNReal.summable_coe.mpr (NNReal.summable_comp_injective hn primePowerSucc_injective)
  exact (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mp hσ

private theorem localSeriesFactor_of_posModulus (F : IntForm n) (p : Nat.Primes)
    [NeZero (p : ℕ)] :
    localSeriesFactor F p = ∑' j : ℕ, unitConductorSum F ((p : ℕ)^j) := by
  simp only [localSeriesFactor, singularSeriesTerm_posModulus]

private theorem localSeriesFactor_im_zero (F : IntForm n) (p : Nat.Primes) (hn : 1 ≤ n)
    (hS : Summable (fun j : ℕ => singularSeriesTerm F ((p : ℕ)^j))) :
    (localSeriesFactor F p).im = 0 := by
  let : Fact (p : ℕ).Prime := ⟨p.prop⟩
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hT : Tendsto (fun m => ∑ j ∈ Finset.range (m+1), singularSeriesTerm F ((p : ℕ)^j))
      atTop (𝓝 (localSeriesFactor F p)) :=
    hS.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hImT := Complex.continuous_im.continuousAt.tendsto.comp hT
  have him : (fun m => (∑ j ∈ Finset.range (m+1), singularSeriesTerm F ((p : ℕ)^j)).im) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext m
    simp only [singularSeriesTerm_posModulus]
    rw [← primePower_density_eq_sum F (p : ℕ) m hn]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, Complex.ofReal_im]
  change Tendsto (fun m => (∑ j ∈ Finset.range (m+1), singularSeriesTerm F ((p : ℕ)^j)).im)
    atTop (𝓝 (localSeriesFactor F p).im) at hImT
  rw [him] at hImT
  exact tendsto_nhds_unique hImT tendsto_const_nhds

/-- Absolute convergence and nonsingular zeros at all finite places make
the singular series a strictly positive real number. -/
theorem singularSeries_positive_of_nonsingularZeros {d : ℕ} (F : IntForm n) (hn : 1 ≤ n)
    (hF : F.IsHomogeneous d)
    (hLoc : ∀ (p : ℕ) [Fact p.Prime], HasNonsingularZero F ℚ_[p])
    (hA : Summable (fun m : ℕ => ‖unitConductorSum F (m+1)‖)) :
    0 < (singularSeries F).re ∧ (singularSeries F).im = 0 := by
  obtain ⟨hTail, hTails⟩ := summable_primePowerTails F (summable_norm_singularSeriesTerm F hA)
  have hPrime (p : Nat.Primes) : Summable (fun j : ℕ => singularSeriesTerm F ((p : ℕ)^j)) := by
    rw [← summable_nat_add_iff 1]
    exact (hTail p).of_norm
  have hError : Summable (fun p : Nat.Primes => ‖localSeriesFactor F p - 1‖) := by
    refine hTails.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    have hOne : singularSeriesTerm F 1 = 1 := by rw [singularSeriesTerm_posModulus, unitConductorSum_one]
    unfold localSeriesFactor
    rw [(hPrime p).tsum_eq_zero_add, pow_zero, hOne, add_sub_cancel_left]
    exact norm_tsum_le_tsum_norm (hTail p)
  have hpPos (p : Nat.Primes) : 0 < (localSeriesFactor F p).re := by
    let : Fact (p : ℕ).Prime := ⟨p.prop⟩
    let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
    rw [localSeriesFactor_of_posModulus F p]
    apply primePower_localFactor_pos_of_nonsingularZero F hn hF (hLoc p)
    simpa only [singularSeriesTerm_posModulus] using hPrime p
  have hnonzero : singularSeries F ≠ 0 := by
    rw [← (hasProd_localSeriesFactor F hA).tprod_eq]
    simpa only [add_sub_cancel] using
      (tprod_one_add_ne_zero_of_summable (f := fun p : Nat.Primes => localSeriesFactor F p - 1)
        (fun p => by
          rw [add_sub_cancel]
          intro hp
          have hp' := hpPos p
          simp only [hp, Complex.zero_re, lt_self_iff_false] at hp') hError)
  have hreal (p : Nat.Primes) : localSeriesFactor F p = ((localSeriesFactor F p).re : ℂ) :=
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact localSeriesFactor_im_zero F p hn (hPrime p))
  let M (s : Finset Nat.Primes) := ∏ p ∈ s, localSeriesFactor F p
  have hM : Tendsto M atTop (𝓝 (singularSeries F)) := hasProd_localSeriesFactor F hA
  have hMreal (s : Finset Nat.Primes) :
      M s = ((∏ p ∈ s, (localSeriesFactor F p).re) : ℝ) := by
    unfold M
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun p _ => hreal p
  have hImT := Complex.continuous_im.continuousAt.tendsto.comp hM
  have hzero : (fun s => (M s).im) = (fun _ : Finset Nat.Primes => (0 : ℝ)) :=
    funext fun s => by rw [hMreal, Complex.ofReal_im]
  change Tendsto (fun s => (M s).im) atTop (𝓝 (singularSeries F).im) at hImT
  rw [hzero] at hImT
  have hIm := tendsto_nhds_unique hImT tendsto_const_nhds
  have hReT : Tendsto (fun s => (M s).re) atTop (𝓝 (singularSeries F).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hM
  refine ⟨lt_of_le_of_ne (ge_of_tendsto' hReT ?_) ?_, hIm⟩
  · intro s
    rw [hMreal, Complex.ofReal_re]
    exact Finset.prod_nonneg fun p _ => (hpPos p).le
  · intro hRe
    apply hnonzero
    exact Complex.ext (hRe.symm.trans Complex.zero_re.symm) (hIm.trans Complex.zero_im.symm)

/-- For a geometrically smooth form, nonzero local zeros are nonsingular. -/
theorem singularSeries_positive_of_summable {d : ℕ} (F : IntForm n) (hn : 1 ≤ n)
    (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (hLoc : ∀ p : ℕ, ∀ _ : Fact p.Prime, HasNonzeroZero F ℚ_[p])
    (hA : Summable (fun m : ℕ => ‖unitConductorSum F (m+1)‖)) :
    0 < (singularSeries F).re ∧ (singularSeries F).im = 0 := by
  refine singularSeries_positive_of_nonsingularZeros F hn hF (fun p _ => ?_) hA
  obtain ⟨x, hx, hFx⟩ := hLoc p inferInstance
  exact ⟨x, hFx, hs.nonsingular_over x hx hFx⟩

end

end Birch
