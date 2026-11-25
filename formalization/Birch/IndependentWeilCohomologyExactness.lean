module

public import WeilConjectures.WeilSheaf.CohomologySequence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.WeilSheaf

noncomputable def cohomologyEquivOfVanishingFirstTerm
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime] [Fact (ringChar k ≠ l)]
    (T : Triangle (WeilComplex k l (Spec (.of k)))) (r : ℤ)
    (hT : T ∈ distTriang (WeilComplex k l (Spec (.of k))))
    (hU₀ : Subsingleton (T.obj₁.cohomologyFrobeniusModule r).carrier)
    (hU₁ : Subsingleton (T.obj₁.cohomologyFrobeniusModule (r+1)).carrier) :
    (T.obj₂.cohomologyFrobeniusModule r).Equiv (T.obj₃.cohomologyFrobeniusModule r) := by
  let _ := hU₀
  let _ := hU₁
  let βr := WeilComplex.cohomologyMap T.mor₂ r
  have hinj : Function.Injective βr := by
    intro x y hxy
    have hzero : βr (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (WeilComplex.exact_cohomologyMap T r hT (x-y)).1 hzero
    apply sub_eq_zero.mp
    rw [← hz, Subsingleton.elim z 0, map_zero]
  have hsurj : Function.Surjective βr := fun z =>
    (WeilComplex.exact_cohomologyδ_left T r (r+1) rfl hT z).1 (Subsingleton.elim _ _)
  exact ⟨LinearEquiv.ofBijective βr ⟨hinj, hsurj⟩,
    WeilComplex.cohomologyMap_frobenius T.mor₂ r⟩

end AlgebraicGeometry.WeilSheaf
