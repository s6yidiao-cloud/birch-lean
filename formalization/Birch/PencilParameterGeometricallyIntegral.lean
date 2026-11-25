module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

namespace Birch

universe u

/-- Extension of any coefficient field preserves integrality of the
principal open in the affine line used for the pencil parameter. -/
theorem isIntegral_pencilParameterBaseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] {h : Polynomial k} (hh : h ≠ 0) :
    IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h))))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  let ep : K ⊗[k] Polynomial k ≃ₐ[K] MvPolynomial (Fin 1) K :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K)
      (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm).trans
        (MvPolynomial.algebraTensorAlgEquiv k K)
  let : IsDomain (K ⊗[k] Polynomial k) :=
    Function.Injective.isDomain ep.toRingHom ep.injective
  have hg : (1 : K) ⊗ₜ[k] h ≠ 0 := by
    let ι : Polynomial k →ₐ[k] K ⊗[k] Polynomial k := Algebra.TensorProduct.includeRight
    change ι h ≠ 0
    exact (map_ne_zero_iff _ (Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective)).mpr hh
  let : IsDomain (Localization.Away ((1 : K) ⊗ₜ[k] h)) := Localization.Away.isDomain hg
  let e := IsLocalization.Away.tensorProductEquivTMulRight k K h (Localization.Away h)
  let : IsDomain (K ⊗[k] Localization.Away h) := Function.Injective.isDomain e.toRingHom e.injective
  let e' := Algebra.TensorProduct.comm k (Localization.Away h) K
  let : IsDomain (Localization.Away h ⊗[k] K) := Function.Injective.isDomain e'.toRingHom e'.injective
  exact IsIntegral.of_isIso (pullbackSpecIso k (Localization.Away h) K).inv

/-- The pencil parameter is geometrically integral, so the relative
cohomology ranks can be compared on its irreducible geometric base. -/
theorem geometricallyIntegral_pencilParameter {k : Type u} [Field k]
    {h : Polynomial k} (hh : h ≠ 0) :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away h)))) := by
  rw [GeometricallyIntegral.eq_geometrically, geometrically_iff_of_commRing]
  intro K _ _ Y fst snd hY
  let := isIntegral_pencilParameterBaseChange (K := K) hh
  exact IsIntegral.of_isIso hY.isoPullback.inv

end Birch
