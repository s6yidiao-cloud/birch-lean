import Birch.CompleteSums
import Birch.GoodReduction

/-!
# Stationary phase at the finitely many bad primes

The same integral gradient certificates bound the depth at which the gradient
is nonzero on the unit sphere. A square-zero digit average then eliminates
the sphere at all sufficiently high conductors.
-/

open MvPolynomial Set ZMod

namespace Birch

noncomputable section

/-- There is a depth beyond which a vector with stationary gradient must lie
in the residue classes divisible by the underlying prime. -/
theorem ProjectivelySmooth.exists_stationaryDepth {n d : ℕ} {F : IntForm n}
    (hs : ProjectivelySmooth F) (hF : F.IsHomogeneous d) (hd : 0 < d)
    (p : ℕ) [Fact p.Prime] :
    ∃ j : ℕ, 0 < j ∧ ∀ x : Fin n → ZMod (p ^ j),
      (∀ i, residueEval (pderiv i F) (p ^ j) x = 0) → ∀ i, p ∣ (x i).val := by
  classical
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  choose a k ha hc using hs.gradient_certificates hF hd
  let B : ℕ := Finset.univ.sup fun i ↦ (a i).natAbs
  let j := B + 1
  have hj : 0 < j := Nat.succ_pos _
  refine ⟨j, hj, fun x hx i ↦ ?_⟩
  let ev : IntForm n →+* ZMod (p ^ j) := eval₂Hom (Int.castRingHom _) x
  have hspan : Ideal.span (range fun i : Fin n ↦ pderiv i F) ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    exact hx l
  have he : (a i : ZMod (p ^ j)) * x i ^ k i = 0 := by
    have H : ev (C (a i) * X i ^ k i) = 0 := hspan (hc i)
    simp only [ev, map_mul, map_pow, coe_eval₂Hom, eval₂_C, eval₂_X] at H
    exact H
  have hnonzero : (a i : ZMod (p ^ j)) ≠ 0 := by
    intro h
    have dvdint := (CharP.intCast_eq_zero_iff (ZMod (p ^ j)) _ _).mp h
    have dvdnat : p ^ j ∣ (a i).natAbs := by exact_mod_cast Int.natAbs_dvd_natAbs.mpr dvdint
    have hapos : 0 < (a i).natAbs := Int.natAbs_pos.mpr (ha i).ne'
    have hbound : (a i).natAbs ≤ B :=
      Finset.le_sup (f := fun l : Fin n ↦ (a l).natAbs) (Finset.mem_univ i)
    have hpow : 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left hp.two_le _
    have hB : B < 2 ^ j := B.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by
      dsimp [j]; omega))
    exact (hB.trans_le hpow).not_ge ((Nat.le_of_dvd hapos dvdnat).trans hbound)
  by_contra hn
  have hu : IsUnit (x i) := by
    rw [← ZMod.natCast_zmod_val (x i)]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hj).mpr hn
  exact hnonzero ((hu.pow _).mul_left_eq_zero.mp he)

/-- The recurrence at any prime once the conductor is high enough for the
nonstationary unit-sphere classes to cancel. -/
theorem completeSum_primePower_recurrence_of_stationaryDepth {n : ℕ} (F : IntForm n)
    (p m d j : ℕ) [Fact p.Prime] [NeZero p] (hj : 0 < j) (hm : 2 * j ≤ m)
    (hF : F.IsHomogeneous d) (hd : 0 < d)
    (hgrad : ∀ x : Fin n → ZMod (p ^ j), (∀ i, residueEval (pderiv i F) (p ^ j) x = 0) →
      ∀ i, p ∣ (x i).val)
    (a : ℤ) (ha : (a : ZMod p) ≠ 0) :
    completeSum F (p ^ m) (a : ZMod (p ^ m)) =
      ((p : ℂ) ^ n)⁻¹ * completeSum F (p ^ (m - d)) (a : ZMod (p ^ (m - d))) := by
  classical
  let Q := p ^ m
  let q := p ^ j
  let t := p ^ (m - j)
  have hp : p.Prime := Fact.out
  have hQ : Q = t * q := by
    dsimp [Q, t, q]
    rw [← pow_add, Nat.sub_add_cancel (by omega : j ≤ m)]
  have hq : q ∣ Q := Nat.pow_dvd_pow _ (by omega)
  have hqt : q ∣ t := Nat.pow_dvd_pow _ (by omega)
  have hpq : p ∣ q := dvd_pow_self _ hj.ne'
  have hpt : p ∣ t := hpq.trans hqt
  let red := ZMod.castHom hq (ZMod q)
  let red₁ := ZMod.castHom (hpq.trans hq) (ZMod p)
  let red₂ := ZMod.castHom hpq (ZMod p)
  have hred (x : ZMod Q) : red₂ (red x) = red₁ x :=
    congrFun (congrArg DFunLike.coe (Subsingleton.elim (red₂.comp red) red₁)) x
  have hred₁ (x : ZMod Q) : red₁ x = 0 ↔ p ∣ x.val := by
    rw [show red₁ x = (x.val : ZMod p) by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      simp [red₁], ZMod.natCast_eq_zero_iff]
  have hred₂ (x : ZMod q) : red₂ x = 0 ↔ p ∣ x.val := by
    rw [show red₂ x = (x.val : ZMod p) by
      conv_lhs => rw [← ZMod.natCast_zmod_val x]
      simp [red₂], ZMod.natCast_eq_zero_iff]
  have hunit : IsUnit (red (a : ZMod Q)) := by
    let z := red (a : ZMod Q)
    have hnot : ¬ p ∣ z.val := by
      intro H
      have hz := (hred₂ z).mpr H
      rw [show red₂ z = red₁ (a : ZMod Q) from hred _, map_intCast] at hz
      exact ha hz
    change IsUnit z
    rw [← ZMod.natCast_zmod_val z]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hj).mpr hnot
  let w (x : Fin n → ZMod Q) : ℂ := if (∀ i, p ∣ (x i).val) then 0 else 1
  have hw (x : Fin n → ZMod Q) (z : Fin n → ZMod q) :
      w (x + fun i => (t : ZMod Q) * ↑(z i).val) = w x := by
    unfold w
    simp only [← hred₁, Pi.add_apply, map_add, map_mul, map_natCast,
      (ZMod.natCast_eq_zero_iff t p).mpr hpt, zero_mul, add_zero]
  have hg (x : Fin n → ZMod Q) (hx : w x ≠ 0) :
      ∃ i, residueEval (pderiv i F) q (fun j => red (x j)) ≠ 0 := by
    by_contra! h
    have hxdiv : ∀ i, p ∣ (x i).val := by
      intro i
      rw [← hred₁, ← hred, hred₂]
      exact hgrad (fun i => red (x i)) h i
    exact hx (ite_eq_left hxdiv)
  have hc := weightedSum_eq_zero_of_nonstationary F hQ hqt hq (a : ZMod Q) hunit w hw hg
  let f (x : Fin n → ZMod Q) := stdAddChar ((a : ZMod Q) * residueEval F Q x)
  have hpart : (∑ x : Fin n → ZMod Q, f x) =
      ∑ x : Fin n → ZMod Q, if (∀ i, p ∣ (x i).val) then f x else 0 := by
    have H : (∑ x : Fin n → ZMod Q, f x) =
        (∑ x : Fin n → ZMod Q, if (∀ i, p ∣ (x i).val) then f x else 0) +
          ∑ x : Fin n → ZMod Q, w x * f x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      unfold w
      split_ifs <;> simp
    exact H.trans (by rw [show (∑ x, w x * f x) = 0 from hc, add_zero])
  have hnorm : completeSum F (p ^ m) (a : ZMod (p ^ m)) =
      ((p ^ m : ℂ) ^ n)⁻¹ * ∑ x : Fin n → ZMod (p ^ m),
        if (∀ i, p ∣ (x i).val) then stdAddChar ((a : ZMod (p ^ m)) *
          residueEval F (p ^ m) x) else 0 := by
    unfold completeSum
    push_cast
    exact congrArg (fun z : ℂ => ((p ^ m : ℂ) ^ n)⁻¹ * z) hpart
  rw [hnorm]
  clear hnorm hpart hc hw hg hunit hred₁ hred₂ hred f w red₁ red₂ red hpt hpq hqt hq hQ t q Q
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  exact divisibleVectorSum_eq_completeSum F p k d hF hd a

end
end Birch
