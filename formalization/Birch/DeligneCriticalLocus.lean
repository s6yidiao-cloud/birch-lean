module

public import Birch.MvPolynomialCoefficientCompat
public import Birch.MacaulayFiberCount
public import Birch.UniformGradientCertificate

@[expose] public section

/-! # Finite critical schemes for phases with smooth leading forms -/

open MvPolynomial

namespace Birch

private theorem totalDegree_pderiv_sub_leading_lt {K : Type*} [Field K]
    {n r : ℕ} (hr : 2 ≤ r) {G : MvPolynomial (Fin n) K} (hG : G.totalDegree ≤ r)
    (i : Fin n) :
    (pderiv i (G - homogeneousComponent r G)).totalDegree < r-1 := by
  classical
  have hpos : (⊥ : ℕ) < r-1 := by change 0 < r-1; omega
  rw [totalDegree, Finset.sup_lt_iff hpos]
  intro b hb
  have hnz := mem_support_iff.mp hb
  rw [coeff_pderiv, coeff_sub, coeff_homogeneousComponent] at hnz
  change b.degree < r-1
  by_contra! hdeg
  let a := b + Finsupp.single i 1
  have ha : a.degree = b.degree+1 := by simp [a]
  change (coeff a G - (if a.degree = r then coeff a G else 0)) * ((b i : K) + 1) ≠ 0 at hnz
  by_cases hea : a.degree = r
  · simp [hea] at hnz
  · have hcoef : coeff a G = 0 := by
      by_contra hne
      have hle := le_totalDegree (mem_support_iff.mpr hne)
      change a.degree ≤ G.totalDegree at hle
      omega
    simp [hea, hcoef] at hnz

/-- At fixed degree and dimension, the length of the affine critical scheme
is uniformly bounded when the leading gradient vanishes only at the origin. -/
theorem exists_uniform_gradient_quotient_bound (n r : ℕ) (hr : 2 ≤ r) :
    ∃ B : ℕ, ∀ {K : Type*} [Field K] [IsAlgClosed K] {G : MvPolynomial (Fin n) K},
      G.totalDegree ≤ r →
      (∀ x : Fin n → K, (∀ i, (pderiv i (homogeneousComponent r G)).eval x = 0) → x = 0) →
      Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i : Fin n => pderiv i G)) ∧
      Module.finrank K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i : Fin n => pderiv i G)) ≤ B := by
  obtain ⟨D, _, hD, hcert⟩ := exists_uniform_gradient_certificate_degree n r
  refine ⟨D ^ n, ?_⟩
  intro K _ _ G hG hcrit
  let L := homogeneousComponent r G
  let f (i : Fin n) := pderiv i L
  let g (i : Fin n) := -pderiv i (G-L)
  have hL : L.IsHomogeneous r := homogeneousComponent_isHomogeneous r G
  have hg (i : Fin n) : (g i).totalDegree < r-1 := by
    change (-pderiv i (G-L)).totalDegree < r-1
    rw [totalDegree_neg]
    exact totalDegree_pderiv_sub_leading_lt hr hG i
  have hfinite := finite_quotient_and_finrank_le_of_perturbed_homogeneous_system
    (by omega) hD f g (fun _ => hL.pderiv) hg (hcert hL hcrit)
  have he (i : Fin n) : f i - g i = pderiv i G := by
    simp [f, g]
  rw [funext he] at hfinite
  exact hfinite

/-- When the top-degree gradient vanishes only at the origin, the affine
critical scheme of the full phase is finite over the coefficient field. -/
theorem finite_gradient_quotient_of_isolated_leading_critical_point
    {K : Type*} [Field K] [IsAlgClosed K] {n r : ℕ} (hr : 2 ≤ r)
    {G : MvPolynomial (Fin n) K} (hG : G.totalDegree ≤ r)
    (hcrit : ∀ x : Fin n → K, (∀ i, (pderiv i (homogeneousComponent r G)).eval x = 0) → x = 0) :
    Module.Finite K (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range fun i : Fin n => pderiv i G)) :=
  let ⟨_, hB⟩ := exists_uniform_gradient_quotient_bound n r hr
  (hB hG hcrit).1

end Birch
