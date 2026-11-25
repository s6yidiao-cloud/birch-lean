module

public import Birch.MvPolynomialCoefficientCompat
public import Birch.Geometry
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Bounding a smooth section using a Macaulay minor

A nonsingular square submatrix of the gradient Macaulay matrix certifies
smoothness and permits interpolation on a fixed grid.
-/

open MvPolynomial Matrix
open scoped BigOperators Matrix

namespace Birch

noncomputable section

variable {l D r : ℕ}

/-- The exponents of monomials of a given degree in the section coordinates. -/
abbrev DegreeMonomial (l D : ℕ) := {s : Fin l →₀ ℕ // s.degree = D}

instance : Finite (DegreeMonomial l D) := by
  let e (s : DegreeMonomial l D) (i : Fin l) : Fin (D+1) :=
    ⟨s.val i, Nat.lt_succ_of_le ((Finsupp.le_degree i s.val).trans_eq s.prop)⟩
  exact Finite.of_injective e fun a b h => Subtype.ext (Finsupp.ext fun i =>
    congrArg Fin.val (congrFun h i))

instance : Fintype (DegreeMonomial l D) := Fintype.ofFinite _

/-- Expand a homogeneous form in its fixed-degree monomial basis. -/
theorem sum_degreeMonomial_eq {K : Type*} [CommRing K]
    (G : MvPolynomial (Fin l) K) (hG : G.IsHomogeneous D) :
    (∑ s : DegreeMonomial l D, monomial s.val (coeff s.val G)) = G := by
  classical
  ext s
  rw [coeff_sum]
  by_cases hs : s.degree = D
  · rw [Finset.sum_eq_single (⟨s, hs⟩ : DegreeMonomial l D)]
    · simp [coeff_monomial]
    · rintro ⟨t, ht⟩ _ hne
      have hst : t ≠ s := fun h => hne (Subtype.ext h)
      simp [coeff_monomial, hst]
    · simp
  · have hz : coeff s G = 0 := by
      by_contra hn
      apply hs
      rw [Finsupp.degree_eq_weight_one]
      exact hG hn
    change AddMonoidAlgebra.coeff G s = 0 at hz
    rw [hz]
    apply Finset.sum_eq_zero
    rintro ⟨t, ht⟩ _
    have hst : t ≠ s := fun h => hs (h ▸ ht)
    simp [coeff_monomial, hst]

/-- The degree-D matrix of monomial multiples of equations of degree e. -/
def systemMacaulayMatrix {m : ℕ} {K : Type*} [CommRing K]
    (f : Fin m → MvPolynomial (Fin l) K) (e D : ℕ) :
    Matrix (DegreeMonomial l D) (Fin m × DegreeMonomial l (D-e)) K :=
  fun s t => coeff s.val (monomial t.2.val 1 * f t.1)

/-- The degree-D matrix whose columns are monomial multiples of partial derivatives. -/
abbrev sectionMacaulayMatrix {K : Type*} [CommRing K]
    (G : MvPolynomial (Fin l) K) (r D : ℕ) :
    Matrix (DegreeMonomial l D) (Fin l × DegreeMonomial l (D-(r-1))) K :=
  systemMacaulayMatrix (fun i => pderiv i G) (r-1) D

/-- Macaulay matrices commute with coefficient specialization. -/
theorem systemMacaulayMatrix_map {m : ℕ} {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (f : Fin m → MvPolynomial (Fin l) K) (e D : ℕ) :
    (systemMacaulayMatrix f e D).map φ =
      systemMacaulayMatrix (fun i => MvPolynomial.map φ (f i)) e D := by
  ext i j
  change φ (coeff i.val (monomial j.2.val 1 * f j.1)) =
    coeff i.val (monomial j.2.val 1 * MvPolynomial.map φ (f j.1))
  rw [← coeff_map, map_mul, map_monomial, map_one]

/-- Specialization commutes with assembling the Macaulay matrix. -/
theorem sectionMacaulayMatrix_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (G : MvPolynomial (Fin l) K) (r D : ℕ) :
    (sectionMacaulayMatrix G r D).map f = sectionMacaulayMatrix (MvPolynomial.map f G) r D := by
  ext i j
  change f (coeff i.val (monomial j.2.val 1 * pderiv j.1 G)) =
    coeff i.val (monomial j.2.val 1 * pderiv j.1 (MvPolynomial.map f G))
  rw [← coeff_map, map_mul, map_monomial, map_one, pderiv_map]

private theorem macaulayColumn_isHomogeneous {m e : ℕ} {K : Type*} [CommRing K]
    {f : Fin m → MvPolynomial (Fin l) K} (hf : ∀ i, (f i).IsHomogeneous e) (hD : e ≤ D)
    (t : Fin m × DegreeMonomial l (D-e)) :
    (monomial t.2.val 1 * f t.1).IsHomogeneous D := by
  have hm : (monomial t.2.val (1 : K)).IsHomogeneous (D-e) := by
    apply isHomogeneous_monomial
    exact t.2.prop
  simpa only [Nat.sub_add_cancel hD] using hm.mul (hf t.1)

/-- A nonsingular square Macaulay submatrix rules out nonzero common zeros. -/
theorem zero_of_system_macaulay_minor {m e : ℕ} {K : Type*} [Field K]
    {f : Fin m → MvPolynomial (Fin l) K} (hf : ∀ i, (f i).IsHomogeneous e)
    (hD : e ≤ D) (hD₀ : 0 < D)
    (select : DegreeMonomial l D → Fin m × DegreeMonomial l (D-e))
    (hdet : ((systemMacaulayMatrix f e D).submatrix id select).det ≠ 0)
    (x : Fin l → K) (hx : ∀ j, (f j).eval x = 0) : x = 0 := by
  classical
  let A := (systemMacaulayMatrix f e D).submatrix id select
  let v (i : DegreeMonomial l D) := (monomial i.val (1 : K)).eval x
  have hz : v ᵥ* A = 0 := by
    funext j
    let t := select j
    let P := monomial t.2.val (1 : K) * f t.1
    have hP : P.IsHomogeneous D := macaulayColumn_isHomogeneous hf hD t
    have he := congrArg (eval x) (sum_degreeMonomial_eq P hP)
    change eval x (∑ i : DegreeMonomial l D, monomial i.val (coeff i.val P)) =
      eval x (monomial t.2.val 1 * f t.1) at he
    simp only [eval_sum, eval_monomial, one_mul, eval_mul, hx, mul_zero] at he
    change (∑ i : DegreeMonomial l D, (monomial i.val (1 : K)).eval x * coeff i.val P) = 0
    simpa only [eval_monomial, one_mul, mul_comm] using he
  have hv : v = 0 := Matrix.vecMul_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)) (hz.trans (zero_vecMul A).symm)
  funext i
  let j : DegreeMonomial l D := ⟨Finsupp.single i D, Finsupp.degree_single i D⟩
  have he : v j = 0 := congrFun hv j
  change (monomial (Finsupp.single i D) (1 : K)).eval x = 0 at he
  have hp : x i ^ D = 0 := by simpa [eval_monomial, Finsupp.prod_single_index] using he
  exact (pow_eq_zero_iff hD₀.ne').mp hp

/-- A nonsingular square Macaulay submatrix forces the restricted gradient to
have no nonzero common zero. -/
theorem gradient_zero_of_macaulay_minor {K : Type*} [Field K]
    {G : MvPolynomial (Fin l) K} (hG : G.IsHomogeneous r) (hD : r-1 ≤ D) (hD₀ : 0 < D)
    (select : DegreeMonomial l D → Fin l × DegreeMonomial l (D-(r-1)))
    (hdet : ((sectionMacaulayMatrix G r D).submatrix id select).det ≠ 0)
    (x : Fin l → K) (hx : ∀ j, (pderiv j G).eval x = 0) : x = 0 :=
  zero_of_system_macaulay_minor (fun _ => hG.pderiv) hD hD₀ select hdet x hx

/-- A spanning family in the row coordinate space admits a square nonsingular minor. -/
theorem exists_system_macaulay_minor_of_span {m : ℕ} {K : Type*} [Field K]
    (f : Fin m → MvPolynomial (Fin l) K) (e D : ℕ)
    (hs : ⊤ ≤ Submodule.span K (Set.range (systemMacaulayMatrix f e D).col)) :
    ∃ select : DegreeMonomial l D → Fin m × DegreeMonomial l (D-e),
      ((systemMacaulayMatrix f e D).submatrix id select).det ≠ 0 := by
  classical
  let A := systemMacaulayMatrix f e D
  let B := Module.Basis.ofSpan hs
  let : Finite (Set.range B) := ((Set.finite_range A.col).subset (Module.Basis.ofSpan_subset hs)).to_subtype
  let eB := Equiv.ofInjective B B.injective
  let := Finite.of_injective eB eB.injective
  let b := Pi.basisFun K (DegreeMonomial l D)
  have hc := (Module.finrank_eq_nat_card_basis B).symm.trans (Module.finrank_eq_nat_card_basis b)
  obtain ⟨e⟩ := Finite.card_eq.mp hc.symm
  have hcol (i : DegreeMonomial l D) : B (e i) ∈ Set.range A.col :=
    Module.Basis.ofSpan_subset hs (Set.mem_range_self (e i))
  choose f hf using hcol
  refine ⟨f, isUnit_iff_ne_zero.mp ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
  change LinearIndependent K (A.col ∘ f)
  have he : A.col ∘ f = B ∘ e := funext hf
  rw [he]
  exact B.linearIndependent.comp e e.injective

/-- A spanning family of partial-derivative columns admits a nonsingular minor. -/
theorem exists_macaulay_minor_of_span {K : Type*} [Field K]
    (G : MvPolynomial (Fin l) K) (r D : ℕ)
    (hs : ⊤ ≤ Submodule.span K (Set.range (sectionMacaulayMatrix G r D).col)) :
    ∃ select : DegreeMonomial l D → Fin l × DegreeMonomial l (D-(r-1)),
      ((sectionMacaulayMatrix G r D).submatrix id select).det ≠ 0 :=
  exists_system_macaulay_minor_of_span (fun i => pderiv i G) (r-1) D hs

end
end Birch
