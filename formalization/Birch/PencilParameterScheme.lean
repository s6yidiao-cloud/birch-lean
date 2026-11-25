module

public import Birch.RelativeFermatPencil
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace Birch

/-- Each rational specialization is a section of the parameter's structure morphism. -/
theorem pencilParameterSpecialization_specMap_comp {k : Type} [Field k]
    {h : Polynomial k} (t : k) (ht : h.eval₂ (RingHom.id k) t ≠ 0) :
    Spec.map (CommRingCat.ofHom (pencilParameterSpecialization (RingHom.id k) h t ht)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h))) = 𝟙 _ := by
  have he : (pencilParameterSpecialization (RingHom.id k) h t ht).comp
      (algebraMap k (Localization.Away h)) = RingHom.id k := by
    apply RingHom.ext
    intro x
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away h)]
    have hx := IsLocalization.Away.lift_eq (S := Localization.Away h) h
      (g := Polynomial.eval₂RingHom (RingHom.id k) t) (isUnit_iff_ne_zero.mpr ht)
      (algebraMap k (Polynomial k) x)
    exact hx.trans (by
      change (Polynomial.C x).eval₂ (RingHom.id k) t = x
      simp)
  have hc := congrArg CommRingCat.ofHom he
  change CommRingCat.ofHom (algebraMap k (Localization.Away h)) ≫
    CommRingCat.ofHom (pencilParameterSpecialization (RingHom.id k) h t ht) = 𝟙 _ at hc
  rw [← Spec.map_comp, hc, Spec.map_id]

/-- The parameter scheme is of finite type over its coefficient field. -/
theorem locallyOfFiniteType_pencilParameter {k : Type} [Field k] (h : Polynomial k) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  rw [CommRingCat.hom_ofHom, RingHom.finiteType_algebraMap]
  infer_instance

end Birch
