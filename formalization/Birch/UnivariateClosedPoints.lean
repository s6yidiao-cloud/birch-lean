import Birch.UnivariateArtinSchreierTrace
import Mathlib.RingTheory.AdjoinRoot

/-! # Closed points of the affine line in finite extensions -/

open Polynomial Algebra Finset
open scoped IntermediateField

namespace Birch

noncomputable section

/-- Root fields of a monic irreducible polynomial are embedded in a finite
extension in exactly the degrees dividing the extension degree. -/
theorem natCard_minpoly_fiber_eq_of_monic_irreducible
    {k L : Type*} [Field k] [Field L] [Algebra k L] [Finite L]
    (P : k[X]) (hP : P.Monic) (hI : Irreducible P) :
    Nat.card {x : L // minpoly k x = P} =
      if P.natDegree ∣ Module.finrank k L then P.natDegree else 0 := by
  let : Fact (Irreducible P) := ⟨hI⟩
  let J := AdjoinRoot P
  let pb : PowerBasis k J := AdjoinRoot.powerBasis hP.ne_zero
  have hmin : minpoly k pb.gen = P := AdjoinRoot.minpoly_powerBasis_gen_of_monic hP
  have hdeg : Module.finrank k J = P.natDegree := pb.finrank
  let e : (J →ₐ[k] L) ≃ {x : L // minpoly k x = P} := pb.liftEquiv.trans
    ((Equiv.refl L).subtypeEquiv (fun x => by
      simp only [Equiv.refl_apply, hmin]
      exact (minpoly.eq_iff_aeval_eq_zero hI hP).symm.trans eq_comm))
  rw [Nat.card_congr e.symm]
  by_cases hd : P.natDegree ∣ Module.finrank k L
  · rw [ite_eq_left hd, FiniteField.natCard_algHom_of_finrank_dvd (show Module.finrank k J ∣
        Module.finrank k L from hdeg.symm ▸ hd), hdeg]
  · let : IsEmpty (J →ₐ[k] L) := ⟨fun e => hd (hdeg ▸
      (FiniteField.nonempty_algHom_iff_finrank_dvd).mp ⟨e⟩)⟩
    rw [Nat.card_of_isEmpty, ite_eq_right hd]


private def minpolyImage (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod p) K] : Finset (ZMod p)[X] := by
  classical
  letI : Fintype K := Fintype.ofFinite _
  exact Finset.univ.image (fun x : K => minpoly (ZMod p) x)

/-- The closed points of the affine line whose residue degrees divide m. -/
def affineLineClosedPoints {p : ℕ} [Fact p.Prime] (m : ℕ) : Finset (ZMod p)[X] :=
  minpolyImage p (GaloisField p m)

/-- Closed points are represented by their unique monic irreducible polynomial. -/
theorem mem_affineLineClosedPoints {p m : ℕ} [Fact p.Prime] (hm : 0 < m)
    {P : (ZMod p)[X]} :
    P ∈ affineLineClosedPoints (p := p) m ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ∣ m := by
  classical
  let K := GaloisField p m
  let : Fintype K := Fintype.ofFinite K
  change P ∈ Finset.univ.image (fun x : K => minpoly (ZMod p) x) ↔ _
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    have hx : IsIntegral (ZMod p) x := IsIntegral.of_finite _ _
    have hM := minpoly.monic hx
    have hI := minpoly.irreducible hx
    refine ⟨hM, hI, ?_⟩
    have hb := natCard_minpoly_fiber_eq_of_monic_irreducible (L := K) _ hM hI
    rw [GaloisField.finrank p hm.ne'] at hb
    by_contra hd
    rw [ite_eq_right hd] at hb
    have hpos : 0 < Nat.card {y : K // minpoly (ZMod p) y = minpoly (ZMod p) x} :=
      Finite.card_pos_iff.mpr ⟨⟨x, rfl⟩⟩
    omega
  · rintro ⟨hM, hI, hd⟩
    have hb := natCard_minpoly_fiber_eq_of_monic_irreducible (L := K) _ hM hI
    rw [GaloisField.finrank p hm.ne', ite_eq_left hd] at hb
    have hn : 0 < Nat.card {x : K // minpoly (ZMod p) x = P} := hb ▸ hI.natDegree_pos
    obtain ⟨x⟩ := Finite.card_pos_iff.mp hn
    exact Finset.mem_image.mpr ⟨x.val, Finset.mem_univ _, x.property⟩


private theorem extensionCharacterSum_eq_minpolyImage
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod p) K]
    (f : (ZMod p)[X]) (a : ZMod p) :
    extensionCharacterSum (K := K) (fun x => aeval x f) a =
      ∑ P ∈ minpolyImage p K, (P.natDegree : ℂ) * ZMod.stdAddChar (a * polynomialRootPhase f P) ^
        (Module.finrank (ZMod p) K / P.natDegree) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let π (x : K) := minpoly (ZMod p) x
  let m := Module.finrank (ZMod p) K
  let w (P : (ZMod p)[X]) := ZMod.stdAddChar (a * polynomialRootPhase f P) ^ (m / P.natDegree)
  have hv (x : K) : ZMod.stdAddChar (a * trace (ZMod p) K (aeval x f)) = w (π x) := by
    have hx : IsIntegral (ZMod p) x := IsIntegral.of_finite _ _
    have hdeg : Module.finrank (ZMod p) (ZMod p)⟮x⟯ = (π x).natDegree :=
      (IntermediateField.adjoin.powerBasis hx).finrank
    let d := Module.finrank (ZMod p)⟮x⟯ K
    have hM : (π x).natDegree * d = m := by
      rw [← hdeg, Module.finrank_mul_finrank]
    have hdiv : m / (π x).natDegree = d := calc
      _ = ((π x).natDegree * d) / (π x).natDegree :=
        congrArg (fun j => j / (π x).natDegree) hM.symm
      _ = _ := Nat.mul_div_cancel_left _ (minpoly.irreducible hx).natDegree_pos
    have ht : trace (ZMod p) K (aeval x f) = (d : ZMod p) * polynomialRootPhase f (π x) :=
      trace_eval_eq_finrank_mul_polynomialRootPhase f x
    rw [ht, mul_left_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
    simp only [w, hdiv]
  change (∑ x : K, ZMod.stdAddChar (a * trace (ZMod p) K (aeval x f))) = _
  calc
    _ = ∑ x : K, w (π x) := Finset.sum_congr rfl (fun x _ => hv x)
    _ = ∑ P ∈ minpolyImage p K, (P.natDegree : ℂ) * w P := by
      rw [← Finset.sum_fiberwise_of_maps_to' (t := minpolyImage p K)
        (fun x _ => Finset.mem_image_of_mem π (Finset.mem_univ x)) w]
      apply Finset.sum_congr rfl
      intro P hP
      change P ∈ Finset.univ.image π at hP
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hP
      have hy : IsIntegral (ZMod p) y := IsIntegral.of_finite _ _
      have hg := natCard_minpoly_fiber_eq_of_monic_irreducible (L := K) _
        (minpoly.monic hy) (minpoly.irreducible hy)
      have hpos : 0 < Nat.card {x : K // π x = π y} := Finite.card_pos_iff.mpr ⟨⟨y, rfl⟩⟩
      have hd : (π y).natDegree ∣ Module.finrank (ZMod p) K := by
        by_contra hd
        rw [ite_eq_right hd] at hg
        change Nat.card {x : K // π x = π y} = 0 at hg
        omega
      have hcard : (Finset.univ.filter (fun x : K => π x = π y)).card = (π y).natDegree := by
        rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
        exact hg.trans (ite_eq_left hd)
      rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- The extension sum grouped by its monic irreducible minimal polynomial.
Each degree-d closed point contributes d copies of its phase value raised
to the extension-degree quotient. -/
theorem extensionCharacterSum_eq_closedPoint_powers
    {p m : ℕ} [Fact p.Prime] [NeZero p] (hm : 0 < m)
    (f : (ZMod p)[X]) (a : ZMod p) :
    extensionCharacterSum (K := GaloisField p m) (fun x => aeval x f) a =
      ∑ P ∈ affineLineClosedPoints (p := p) m,
        (P.natDegree : ℂ) * ZMod.stdAddChar (a * polynomialRootPhase f P) ^ (m / P.natDegree) := by
  rw [extensionCharacterSum_eq_minpolyImage, GaloisField.finrank p hm.ne']
  rfl

end

end Birch
