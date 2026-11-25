import Birch.DeligneLevelClosure
import Birch.DeligneTensorPhase

/-! # Critical values of powers of polynomial phases -/

open MvPolynomial

namespace Birch

noncomputable section

/-- Over the chosen coefficient field, take the image of the affine critical locus. -/
def criticalValues {σ K : Type*} [CommRing K] (g : MvPolynomial σ K) : Set K :=
  (fun x => eval x g) '' {x : σ → K | ∀ i, (pderiv i g).eval x = 0}

/-- Smooth leading forms give a bound independent of the field and coefficients. -/
theorem exists_uniform_critical_value_bound (n r : ℕ) (hr : 2 ≤ r) :
    ∃ D : ℕ, ∀ {K : Type*} [Field K] [IsAlgClosed K] {g : MvPolynomial (Fin n) K},
      g.totalDegree ≤ r →
      (∀ x : Fin n → K, (∀ i, (pderiv i (homogeneousComponent r g)).eval x = 0) → x = 0) →
      (criticalValues g).Finite ∧ (criticalValues g).ncard ≤ D := by
  obtain ⟨D, hD⟩ := exists_uniform_affine_critical_point_bound n r hr
  refine ⟨D, ?_⟩
  intro K _ _ g hg hcrit
  obtain ⟨hfinite, hcard⟩ := hD hg hcrit
  exact ⟨hfinite.image _, (Set.ncard_image_le hfinite).trans hcard⟩

/-- A sum of `k` elements of a finite set is determined by their multiplicities. -/
theorem ncard_range_sum_le {A : Type*} [AddCommMonoid A] (S : Set A) (hS : S.Finite)
    (k : ℕ) :
    (Set.range fun a : Fin k → S => ∑ i, (a i : A)).ncard ≤ (k + 1) ^ S.ncard := by
  classical
  let := hS.fintype
  let hist (a : Fin k → S) (s : S) : Fin (k + 1) :=
    ⟨(Finset.univ.filter (fun i => a i = s)).card,
      Nat.lt_succ_of_le (by simpa using Finset.card_filter_le Finset.univ (fun i => a i = s))⟩
  let value (m : S → Fin (k + 1)) : A := ∑ s, (m s : ℕ) • (s : A)
  have hsubset : (Set.range fun a : Fin k → S => ∑ i, (a i : A)) ⊆ Set.range value := by
    rintro _ ⟨a, rfl⟩
    refine ⟨hist a, ?_⟩
    change (∑ s : S, (Finset.univ.filter (fun i => a i = s)).card • (s : A)) = _
    simp_rw [← Finset.sum_const]
    exact Finset.sum_fiberwise' Finset.univ a (fun s => (s : A))
  have hcard : (Set.range value).ncard ≤ (Set.univ : Set (S → Fin (k + 1))).ncard := by
    simpa only [Set.image_univ] using
      (Set.ncard_image_le (f := value) (Set.finite_univ : (Set.univ : Set (S → Fin (k + 1))).Finite))
  refine (Set.ncard_le_ncard hsubset (Set.finite_range value)).trans (hcard.trans_eq ?_)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- Every critical value of an additive power is a sum of critical values of
the original phase, including when the power is written with linear indices. -/
theorem criticalValues_additivePowerPolynomialFin_subset {K : Type*} [CommRing K] {n : ℕ}
    (k : ℕ) (g : MvPolynomial (Fin n) K) :
    criticalValues (additivePowerPolynomialFin k g) ⊆
      Set.range (fun a : Fin k → criticalValues g => ∑ j, (a j : K)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hblock (j : Fin k) (i : Fin n) :
      (pderiv i g).eval (fun a => x (finProdFinEquiv (j, a))) = 0 := by
    have hz := hx (finProdFinEquiv (j, i))
    change (pderiv (finProdFinEquiv (j, i))
      (rename finProdFinEquiv (additivePowerPolynomial k g))).eval x = 0 at hz
    rw [pderiv_rename finProdFinEquiv.injective, pderiv_additivePowerPolynomial] at hz
    change (rename finProdFinEquiv (rename (Prod.mk j) (pderiv i g))).eval₂ (RingHom.id K) x = 0 at hz
    rw [eval₂_rename, eval₂_rename, eval₂_id] at hz
    exact hz
  refine ⟨fun j => ⟨g.eval (fun a => x (finProdFinEquiv (j, a))),
    ⟨fun a => x (finProdFinEquiv (j, a)), hblock j, rfl⟩⟩, ?_⟩
  exact (eval₂_additivePowerPolynomialFin k g (RingHom.id K) x).symm

/-- The number of critical levels of the power grows at most polynomially
in the number of copies, with exponent the number of critical values. -/
theorem finite_criticalValues_additivePowerPolynomialFin {K : Type*} [CommRing K] {n : ℕ}
    (k : ℕ) (g : MvPolynomial (Fin n) K) (hfinite : (criticalValues g).Finite) :
    (criticalValues (additivePowerPolynomialFin k g)).Finite ∧
    (criticalValues (additivePowerPolynomialFin k g)).ncard ≤
      (k + 1) ^ (criticalValues g).ncard := by
  let := hfinite.fintype
  have hsum := Set.finite_range (fun a : Fin k → criticalValues g => ∑ j, (a j : K))
  have hsubset := criticalValues_additivePowerPolynomialFin_subset k g
  exact ⟨hsum.subset hsubset, (Set.ncard_le_ncard hsubset hsum).trans
    (ncard_range_sum_le (criticalValues g) hfinite k)⟩

end

end Birch
