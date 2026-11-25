import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Tactic

/-! Summability of negative powers of the sup norm on the integer lattice. -/

namespace Birch

/-- The coordinate-wise real inclusion of the integer lattice. -/
def latticeVector {n : ℕ} (m : Fin n → ℤ) : Fin n → ℝ := fun i ↦ (m i : ℝ)

theorem latticeVector_injective (n : ℕ) : Function.Injective (latticeVector (n := n)) := by
  intro a b h
  funext i
  have hi : (a i : ℝ) = (b i : ℝ) := congrFun h i
  exact_mod_cast hi

theorem summable_latticeVector_rpow {n N : ℕ} (hN : n < N) :
    Summable (fun m : Fin n → ℤ ↦ ‖latticeVector m‖ ^ (-(N : ℝ))) := by
  classical
  let b := Pi.basisFun ℝ (Fin n)
  let L := Submodule.span ℤ (Set.range b)
  let : DiscreteTopology L := ZSpan.discreteTopology_pi_basisFun
  let : IsZLattice ℝ L := instIsZLatticeRealSpan b
  let e (m : Fin n → ℤ) : L := ⟨latticeVector m, by
    apply (Module.Basis.mem_span_iff_repr_mem ℤ b _).mpr
    intro i
    exact ⟨m i, by simp [latticeVector, b]⟩⟩
  have he : Function.Injective e := fun _ _ h ↦ latticeVector_injective n (congrArg Subtype.val h)
  have hdim : Module.finrank ℤ L = n := by
    rw [ZLattice.rank ℝ L, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  apply (ZLattice.summable_norm_rpow L (-(N : ℝ)) ?_).comp_injective he
  rw [hdim]
  exact neg_lt_neg (by exact_mod_cast hN)

end Birch
