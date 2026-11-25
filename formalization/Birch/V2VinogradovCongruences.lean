import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Power-sum congruences in fixed residue classes

A block of consecutive power sums determines the coordinates modulo a prime
power when the coordinate classes are fixed and distinct modulo the prime.
For a block starting above degree one, the classes must also be nonzero.
The proof uses the Vandermonde matrix of divided differences modulo the prime.
-/

namespace Birch

open scoped BigOperators Matrix

noncomputable section

/-- Reduce a residue modulo a positive prime power to a residue modulo its base. -/
abbrev primePowerReduction (p B : ℕ) (hB : 0 < B) : ZMod (p ^ B) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hB.ne') (ZMod p)

/-- A residue modulo a prime power is a unit if its reduction modulo the
prime is nonzero. -/
theorem isUnit_of_primePowerReduction_ne_zero {p B : ℕ} [Fact p.Prime] (hB : 0 < B)
    {z : ZMod (p ^ B)} (hz : primePowerReduction p B hB z ≠ 0) : IsUnit z := by
  have hp : p.Prime := Fact.out
  let : NeZero (p ^ B) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hzval : z = (z.val : ZMod (p ^ B)) := (ZMod.natCast_zmod_val z).symm
  rw [hzval, map_natCast] at hz
  rw [hzval]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp hB).2
  intro h
  exact hz ((ZMod.natCast_eq_zero_iff _ _).2 h)

private abbrev dividedPower {R : Type*} [CommRing R] (s : ℕ) (x y : R) : R :=
  ∑ l ∈ Finset.range (s + 1), x ^ l * y ^ (s - l)

private theorem dividedPower_mul_sub {R : Type*} [CommRing R] (s : ℕ) (x y : R) :
    dividedPower s x y * (x - y) = x ^ (s + 1) - y ^ (s + 1) := by
  simpa only [Nat.add_sub_cancel] using geom_sum₂_mul x y (s + 1)

private theorem map_dividedPower_at_equal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {x y : R} {a : S} (hx : f x = a) (hy : f y = a) (s : ℕ) :
    f (dividedPower s x y) = ((s + 1 : ℕ) : S) * a ^ s := by
  simp only [dividedPower, map_sum, map_mul, map_pow, hx, hy]
  calc
    _ = ∑ _l ∈ Finset.range (s + 1), a ^ s := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [← pow_add, Nat.add_sub_of_le (by
        have := Finset.mem_range.1 hl
        omega)]
    _ = _ := by simp [nsmul_eq_mul]

/-- A consecutive block of power-sum congruences modulo `p ^ B` is
injective on tuples restricted to fixed, pairwise distinct classes modulo
`p`. For an offset `m` the block consists of degrees `m+1,…,m+k`, and
the factor `a i ^ m` must be nonzero at each of the fixed residues. -/
theorem zmod_primePower_eq_of_powerSumBlock {p B k m : ℕ} [Fact p.Prime]
    (hB : 0 < B) (hkp : m + k < p)
    (a : Fin k → ZMod p) (ha : Function.Injective a) (haz : ∀ i, a i ^ m ≠ 0)
    (x y : Fin k → ZMod (p ^ B))
    (hx : ∀ i, primePowerReduction p B hB (x i) = a i)
    (hy : ∀ i, primePowerReduction p B hB (y i) = a i)
    (hpow : ∀ j : Fin k,
      (∑ i, x i ^ (m + j.val + 1)) = ∑ i, y i ^ (m + j.val + 1)) :
    x = y := by
  let red := primePowerReduction p B hB
  let A : Matrix (Fin k) (Fin k) (ZMod (p ^ B)) :=
    Matrix.of fun j i => dividedPower (m + j.val) (x i) (y i)
  let d₁ (j : Fin k) : ZMod p := (((m + j.val + 1 : ℕ) : ZMod p))
  let d₂ (i : Fin k) : ZMod p := a i ^ m
  have hred : A.map red = Matrix.diagonal d₁ * (Matrix.vandermonde a)ᵀ * Matrix.diagonal d₂ := by
    ext j i
    change red (dividedPower (m + j.val) (x i) (y i)) =
      (Matrix.diagonal d₁ * (Matrix.vandermonde a)ᵀ * Matrix.diagonal d₂) j i
    rw [map_dividedPower_at_equal red (hx i) (hy i), Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.transpose_apply, Matrix.vandermonde_apply]
    dsimp only [d₁, d₂]
    rw [pow_add]
    ring
  have hd₁ (j : Fin k) : d₁ j ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).1 hz
    have hlt : m + j.val + 1 < p := by omega
    exact hlt.not_ge (Nat.le_of_dvd (by omega) hdvd)
  have hdet : (A.map red).det ≠ 0 := by
    rw [hred, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Matrix.det_transpose]
    exact mul_ne_zero
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 (fun j _ => hd₁ j))
        (Matrix.det_vandermonde_ne_zero_iff.2 ha))
      (Finset.prod_ne_zero_iff.2 (fun i _ => haz i))
  have hdetUnit : IsUnit A.det := by
    apply isUnit_of_primePowerReduction_ne_zero hB
    rw [RingHom.map_det]
    exact hdet
  have hinj := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).2 hdetUnit)
  have hker : A.mulVec (x - y) = 0 := by
    funext j
    change (∑ i, dividedPower (m + j.val) (x i) (y i) * (x i - y i)) = 0
    simp_rw [dividedPower_mul_sub, Finset.sum_sub_distrib, hpow j, sub_self]
  exact sub_eq_zero.mp (hinj (hker.trans (Matrix.mulVec_zero A).symm))

/-- The power-sum congruences of degrees `1,…,k` determine a tuple modulo
`p ^ B` on fixed distinct coordinate residue classes. -/
theorem zmod_primePower_eq_of_powerSums {p B k : ℕ} [Fact p.Prime]
    (hB : 0 < B) (hkp : k < p)
    (a : Fin k → ZMod p) (ha : Function.Injective a)
    (x y : Fin k → ZMod (p ^ B))
    (hx : ∀ i, primePowerReduction p B hB (x i) = a i)
    (hy : ∀ i, primePowerReduction p B hB (y i) = a i)
    (hpow : ∀ j : Fin k, (∑ i, x i ^ (j.val + 1)) = ∑ i, y i ^ (j.val + 1)) :
    x = y :=
  zmod_primePower_eq_of_powerSumBlock (m := 0) hB (by simpa using hkp)
    a ha (fun _ => by simp) x y hx hy (by simpa using hpow)

/-- If the powers in a consecutive block agree with different prime-power
moduli, the smallest modulus in that block determines the coordinate
classes, provided their fixed residues are distinct. -/
theorem int_modEq_of_powerSumBlock_of_exponent_le {p B k m : ℕ} [Fact p.Prime]
    (hB : 0 < B) (hkp : m + k < p) (b : Fin k → ℕ) (hb : ∀ j, B ≤ b j)
    (a : Fin k → ZMod p) (ha : Function.Injective a) (haz : ∀ i, a i ^ m ≠ 0)
    (x y : Fin k → ℤ) (hx : ∀ i, (x i : ZMod p) = a i)
    (hy : ∀ i, (y i : ZMod p) = a i)
    (hpow : ∀ j : Fin k, (∑ i, x i ^ (m + j.val + 1)) ≡
      (∑ i, y i ^ (m + j.val + 1)) [ZMOD (p ^ b j : ℕ)]) :
    ∀ i, x i ≡ y i [ZMOD (p ^ B : ℕ)] := by
  let x' (i : Fin k) : ZMod (p ^ B) := x i
  let y' (i : Fin k) : ZMod (p ^ B) := y i
  have hx' (i : Fin k) : primePowerReduction p B hB (x' i) = a i := by
    dsimp only [x']
    rw [map_intCast]
    exact hx i
  have hy' (i : Fin k) : primePowerReduction p B hB (y' i) = a i := by
    dsimp only [y']
    rw [map_intCast]
    exact hy i
  have hpow' (j : Fin k) :
      (∑ i, x' i ^ (m + j.val + 1)) = ∑ i, y' i ^ (m + j.val + 1) := by
    have hdvd : (p ^ B : ℕ) ∣ p ^ b j := pow_dvd_pow p (hb j)
    have hdvdZ : ((p ^ B : ℕ) : ℤ) ∣ ((p ^ b j : ℕ) : ℤ) := by
      exact_mod_cast hdvd
    have hm := (hpow j).of_dvd hdvdZ
    have hr := (ZMod.intCast_eq_intCast_iff _ _ (p ^ B)).2 hm
    simpa only [Int.cast_sum, Int.cast_pow, x', y'] using hr
  have heq := zmod_primePower_eq_of_powerSumBlock hB hkp a ha haz x' y' hx' hy' hpow'
  intro i
  exact (ZMod.intCast_eq_intCast_iff (x i) (y i) (p ^ B)).1 (congrFun heq i)

/-- For the anisotropic moduli `p ^ (b*j)`, the `k` consecutive
equations starting at degree `m+1` give coordinatewise congruence modulo
`p ^ (b*(m+1))` in the fixed distinct residue classes. -/
theorem int_modEq_of_powerSumBlock_anisotropic {p b k m : ℕ} [Fact p.Prime]
    (hb : 0 < b) (hkp : m + k < p)
    (a : Fin k → ZMod p) (ha : Function.Injective a) (haz : ∀ i, a i ^ m ≠ 0)
    (x y : Fin k → ℤ) (hx : ∀ i, (x i : ZMod p) = a i)
    (hy : ∀ i, (y i : ZMod p) = a i)
    (hpow : ∀ j : Fin k, (∑ i, x i ^ (m + j.val + 1)) ≡
      (∑ i, y i ^ (m + j.val + 1)) [ZMOD (p ^ (b * (m + j.val + 1)) : ℕ)]) :
    ∀ i, x i ≡ y i [ZMOD (p ^ (b * (m + 1)) : ℕ)] :=
  int_modEq_of_powerSumBlock_of_exponent_le
    (Nat.mul_pos hb (Nat.succ_pos _)) hkp (fun j => b * (m + j.val + 1))
    (fun j => Nat.mul_le_mul_left _ (by omega)) a ha haz x y hx hy hpow

end

end Birch
