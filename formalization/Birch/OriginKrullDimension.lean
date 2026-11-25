module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

@[expose] public section

open MvPolynomial

namespace Birch

variable {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]

/-- A zero locus contained in the origin has dimension at most zero. -/
theorem ringKrullDim_le_zero_of_zeroLocus_subset_origin (I : Ideal (MvPolynomial (Fin n) K))
    (hz : zeroLocus K I ⊆ {0}) : ringKrullDim (MvPolynomial (Fin n) K ⧸ I) ≤ 0 := by
  let O : Ideal (MvPolynomial (Fin n) K) := vanishingIdeal K ({0} : Set (Fin n → K))
  have hO : O ≤ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    exact vanishingIdeal_anti_mono hz
  have hprime (p : PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) K) I) :
      p.val.asIdeal = O := by
    have hp : O ≤ p.val.asIdeal := hO.trans (p.val.isPrime.radical_le_iff.mpr p.prop)
    exact ((inferInstance : O.IsMaximal).eq_of_le p.val.isPrime.ne_top hp).symm
  let : Subsingleton (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) K) I) :=
    ⟨fun p q => Subtype.ext (PrimeSpectrum.ext ((hprime p).trans (hprime q).symm))⟩
  rw [ringKrullDim_quotient]
  exact Order.krullDim_nonpos_of_subsingleton

end Birch
