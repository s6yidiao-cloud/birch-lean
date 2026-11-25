module

/-
Adapted from AxiomMath/Stacks,
StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/OpenClosedPointReduction.lean,
at revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf.
Released under Apache 2.0 as described in LICENSES/Apache-2.0.txt.
-/
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField

@[expose] public section

/-! # Field-valued points of an open subscheme and its closed complement -/

open AlgebraicGeometry CategoryTheory

namespace Birch

noncomputable section

universe u

/-- A point over a field whose image lies in a preimmersion factors
through that preimmersion. -/
theorem exists_fieldPoint_lift_of_isPreimmersion {L : Type u} [Field L]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsPreimmersion i]
    (g : Spec (.of L) ⟶ X) (z : Z) (hz : i z = g default) :
    ∃ g' : Spec (.of L) ⟶ Z, g' ≫ i = g := by
  have hsurj : Function.Surjective (i.residueFieldMap z) := by
    have hs : Function.Surjective (i.stalkMap z ≫ Z.residue z) :=
      (Z.residue_surjective z).comp (i.stalkMap_surjective z)
    rw [← Scheme.residue_residueFieldMap i z] at hs
    intro y
    obtain ⟨a, ha⟩ := hs y
    exact ⟨X.residue (i z) a, ha⟩
  let r := RingEquiv.ofBijective (i.residueFieldMap z).hom
    ⟨(i.residueFieldMap z).hom.injective, hsurj⟩
  let e : Z.residueField z ≅ X.residueField (i z) := r.toCommRingCatIso.symm
  have he : i.residueFieldMap z ≫ e.hom = 𝟙 _ := by
    ext a
    exact r.symm_apply_apply a
  have hd := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X g
  refine ⟨Spec.map (e.hom ≫
      (X.residueFieldCongr (hz.trans (congrArg _ (Subsingleton.elim _ _)))).hom ≫
      X.descResidueField (Scheme.stalkClosedPointTo g)) ≫ Z.fromSpecResidueField z, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, ← Spec.map_comp, reassoc_of% he, Spec.map_comp,
    Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField, hd]

/-- Morphisms from the spectrum of the extension field over the base field. -/
abbrev SchemeFieldValuedPoints {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (L : Type u) [Field L] [Algebra K L] :=
  {g : Spec (.of L) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))}

/-- The type of morphisms counted by the Weil theorem is the type of
extension-field-valued points of the scheme. -/
def overHomEquivSchemeFieldValuedPoints {k L : Type u} [Field k] [Field L] [Algebra k L]
    (X : Over (Spec (.of k))) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶ X) ≃
      SchemeFieldValuedPoints X.hom L where
  toFun f := ⟨f.left, Over.w f⟩
  invFun x := Over.homMk x.1 x.2
  left_inv f := by ext; rfl
  right_inv x := rfl

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {U Z X : Scheme.{u}} (f : X ⟶ Spec (.of K))

def fieldPointMap {W : Scheme.{u}} (a : W ⟶ X)
    (x : SchemeFieldValuedPoints (a ≫ f) L) : SchemeFieldValuedPoints f L :=
  ⟨x.val ≫ a, (Category.assoc _ _ _).trans x.prop⟩

/-- A field-valued point of the open subscheme is the same as a point of
the whole scheme whose image lies in that open. -/
def fieldValuedPointsInOpenEquiv (j : U ⟶ X) [IsOpenImmersion j] :
    SchemeFieldValuedPoints (j ≫ f) L ≃
      {g : Spec (.of L) ⟶ X //
        g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
          Set.range g ⊆ Set.range j} := by
  let e (g : SchemeFieldValuedPoints (j ≫ f) L) :
      {g : Spec (.of L) ⟶ X //
        g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
          Set.range g ⊆ Set.range j} :=
    ⟨g.val ≫ j, (fieldPointMap f j g).prop, by rintro _ ⟨x, rfl⟩; exact ⟨g.val x, rfl⟩⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext ((cancel_mono j).mp (congrArg Subtype.val h))
  · intro x
    let g := IsOpenImmersion.lift j x.val x.prop.2
    have hg : g ≫ j = x.val := IsOpenImmersion.lift_fac j x.val x.prop.2
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [← Category.assoc, hg]
    exact x.prop.1

/-- Field-valued points of a scheme are partitioned by an open
subscheme and a closed complement. -/
def fieldValuedPointsOpenClosedEquiv (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] (hij : Set.range j = (Set.range i)ᶜ) :
    SchemeFieldValuedPoints (j ≫ f) L ⊕ SchemeFieldValuedPoints (i ≫ f) L ≃
      SchemeFieldValuedPoints f L := by
  have hdisj (a : Spec (.of L) ⟶ U) (b : Spec (.of L) ⟶ Z) : a ≫ j ≠ b ≫ i := by
    intro h
    have ha : j (a default) ∈ Set.range j := ⟨_, rfl⟩
    rw [hij] at ha
    apply ha
    refine ⟨b default, ?_⟩
    exact (congrArg (fun m : Spec (.of L) ⟶ X => m default) h).symm
  refine Equiv.ofBijective (Sum.elim (fieldPointMap f j) (fieldPointMap f i)) ⟨?_, ?_⟩
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr, fieldPointMap] at h
    · exact congrArg Sum.inl (Subtype.ext ((cancel_mono j).mp (congrArg Subtype.val h)))
    · exact (hdisj a.val b.val (congrArg Subtype.val h)).elim
    · exact (hdisj b.val a.val (congrArg Subtype.val h).symm).elim
    · exact congrArg Sum.inr (Subtype.ext ((cancel_mono i).mp (congrArg Subtype.val h)))
  · intro x
    by_cases hx : x.val default ∈ Set.range j
    · obtain ⟨z, hz⟩ := hx
      obtain ⟨g, hg⟩ := exists_fieldPoint_lift_of_isPreimmersion j x.val z hz
      refine ⟨Sum.inl ⟨g, ?_⟩, Subtype.ext hg⟩
      rw [← Category.assoc, hg]
      exact x.prop
    · rw [hij, Set.notMem_compl_iff] at hx
      obtain ⟨z, hz⟩ := hx
      obtain ⟨g, hg⟩ := exists_fieldPoint_lift_of_isPreimmersion i x.val z hz
      refine ⟨Sum.inr ⟨g, ?_⟩, Subtype.ext hg⟩
      rw [← Category.assoc, hg]
      exact x.prop

end

end

end Birch
