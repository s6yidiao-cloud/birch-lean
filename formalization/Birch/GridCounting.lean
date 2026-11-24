import Birch.DirectionCountBridge

/-!
# Coordinate slicing and the direction box

The finite grid bound is derived from the coordinate slicing used in the proof
of Browning–Heath-Brown, Lemma 4 (bound (3.8)). Its input records the geometric
facts used by the induction: decomposition into components and the budgets on
the zero-dimensional slices. Reduction of the integer direction box is
injective throughout the height range in the completion argument.
-/

open Finset Set MvPolynomial
open scoped BigOperators

namespace Birch

noncomputable section

/-- A finite coordinate-slicing certificate, with dimension and degree budgets.
A component with a nonconstant coordinate is handled by slicing in that
coordinate, with the same budget in each fiber and one less dimension. -/
inductive CoordinateSlicing {K : Type*} {n : ℕ} : ℕ → ℕ → Set (Fin n → K) → Prop
  | finite {l D : ℕ} {V : Set (Fin n → K)}
      (T : Finset (Fin n → K)) (hV : V ⊆ ↑T) (hT : T.card ≤ D) :
      CoordinateSlicing l D V
  | cover {l D m : ℕ} {V : Set (Fin n → K)}
      (parts : Fin m → Set (Fin n → K)) (cost : Fin m → ℕ)
      (hV : V ⊆ ⋃ j, parts j) (hD : ∑ j, cost j ≤ D)
      (hparts : ∀ j, CoordinateSlicing l (cost j) (parts j)) :
      CoordinateSlicing l D V
  | coordinate {l D : ℕ} {V : Set (Fin n → K)}
      (i : Fin n) (hslice : ∀ a : K, CoordinateSlicing l D (V ∩ {x | x i = a})) :
      CoordinateSlicing (l+1) D V

/-- The points of a subset visible in the Cartesian power of a finite alphabet. -/
def coordinateGrid {K : Type*} {n : ℕ} (S : Finset K) (V : Set (Fin n → K)) :
    Finset (Fin n → K) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin n => S)).filter (fun x => x ∈ V)

theorem mem_coordinateGrid {K : Type*} {n : ℕ} {S : Finset K}
    {V : Set (Fin n → K)} {x : Fin n → K} :
    x ∈ coordinateGrid S V ↔ (∀ i, x i ∈ S) ∧ x ∈ V := by
  classical
  simp [coordinateGrid]

/-- The coordinate slices and a total degree budget D give at most D |S|^l
points on the grid. -/
theorem CoordinateSlicing.card_coordinateGrid_le {K : Type*} {n l D : ℕ}
    {V : Set (Fin n → K)} (hV : CoordinateSlicing l D V) (S : Finset K) (hS : S.Nonempty) :
    (coordinateGrid S V).card ≤ D * S.card ^ l := by
  classical
  induction hV with
  | @finite l D V T hV hT =>
      have hsub : coordinateGrid S V ⊆ T := fun _ hx => hV (mem_coordinateGrid.mp hx).2
      exact ((Finset.card_le_card hsub).trans hT).trans
        (Nat.le_mul_of_pos_right _ (pow_pos (Finset.card_pos.mpr hS) _))
  | @cover l D m V parts cost hV hD _ ih =>
      let grid (j : Fin m) := coordinateGrid S (parts j)
      have hsub : coordinateGrid S V ⊆ Finset.univ.biUnion grid := by
        intro x hx
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hV (mem_coordinateGrid.mp hx).2)
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, mem_coordinateGrid.mpr
          ⟨(mem_coordinateGrid.mp hx).1, hj⟩⟩
      calc
        _ ≤ (Finset.univ.biUnion grid).card := Finset.card_le_card hsub
        _ ≤ ∑ j, (grid j).card := Finset.card_biUnion_le
        _ ≤ ∑ j, cost j * S.card ^ l := Finset.sum_le_sum (fun j _ => ih j)
        _ ≤ _ := by
          rw [← Finset.sum_mul]
          exact Nat.mul_le_mul_right _ hD
  | @coordinate l D V i _ ih =>
      let grid (a : K) := coordinateGrid S (V ∩ {x | x i = a})
      have hsub : coordinateGrid S V ⊆ S.biUnion grid := by
        intro x hx
        obtain ⟨hgrid, hxV⟩ := mem_coordinateGrid.mp hx
        exact Finset.mem_biUnion.mpr ⟨x i, hgrid i, mem_coordinateGrid.mpr ⟨hgrid, hxV, rfl⟩⟩
      calc
        _ ≤ (S.biUnion grid).card := Finset.card_le_card hsub
        _ ≤ ∑ a ∈ S, (grid a).card := Finset.card_biUnion_le
        _ ≤ ∑ _a ∈ S, (D * S.card ^ l) := Finset.sum_le_sum (fun a _ => ih a)
        _ = _ := by simp [pow_succ, mul_left_comm, mul_comm]

theorem card_int_coordinateBox_le {H : ℝ} (hH : 1 ≤ H) :
    ((Finset.Icc (-⌊H⌋) ⌊H⌋).card : ℝ) ≤ 3 * H := by
  have h0 := Int.floor_nonneg.mpr (zero_le_one.trans hH)
  have hEnd : -⌊H⌋ ≤ ⌊H⌋ + 1 := by omega
  have hcard : ((Finset.Icc (-⌊H⌋) ⌊H⌋).card : ℝ) =
      (⌊H⌋ : ℝ) + 1 - (-(⌊H⌋ : ℝ)) := by
    exact_mod_cast Int.card_Icc_of_le _ _ hEnd
  rw [hcard]
  linarith [Int.floor_le H]

/-- Reduction into any field of characteristic p is injective on the directions
of the differencing step when their coordinate diameter is at most p. -/
theorem injOn_cast_differencingDirections {K : Type*} [Field K] {n p : ℕ} [CharP K p]
    {H : ℝ} (hH : 0 < H) (hpH : 2 * H ≤ p) :
    Set.InjOn (fun (u : Fin n → ℤ) (i : Fin n) => (u i : K))
      (differencingDirections n H : Set (Fin n → ℤ)) := by
  intro u hu v hv huv
  funext i
  have hzero : ((u i - v i : ℤ) : K) = 0 := by
    have hi : (u i : K) = (v i : K) := congrFun huv i
    rw [Int.cast_sub, hi, sub_self]
  have hdiv : (p : ℤ) ∣ u i - v i := (CharP.intCast_eq_zero_iff K p _).mp hzero
  have habs : |((u i - v i : ℤ) : ℝ)| < (p : ℝ) := by
    rw [Int.cast_sub]
    exact ((abs_sub _ _).trans_lt (add_lt_add
      (abs_differencingDirection_lt hH hu i) (abs_differencingDirection_lt hH hv i))).trans_le
        (by linarith)
  have hcast : (↑((u i - v i).natAbs) : ℝ) = |((u i - v i : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hlt : (u i - v i).natAbs < p := by
    exact_mod_cast (hcast.symm ▸ habs)
  exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv (by simpa using hlt))

/-- A geometric slicing certificate on the reductions bounds the cardinality of
any matching subset of the actual integer directions. -/
theorem card_filter_differencingDirections_le_of_slicing {K : Type*} [Field K]
    {n p l D : ℕ} [CharP K p] {H : ℝ} (hH : 1 ≤ H) (hpH : 2 * H ≤ p)
    (condition : (Fin n → ℤ) → Prop) [DecidablePred condition]
    {V : Set (Fin n → K)} (hV : CoordinateSlicing l D V)
    (hcover : ∀ u ∈ differencingDirections n H, condition u →
      (fun i => (u i : K)) ∈ V) :
    (((differencingDirections n H).filter condition).card : ℝ) ≤
      (D : ℝ) * (3 : ℝ)^l * H^l := by
  classical
  let Z := Finset.Icc (-⌊H⌋) ⌊H⌋
  let S := Z.image (fun j : ℤ => (j : K))
  have hS : S.Nonempty := by
    refine ⟨0, Finset.mem_image.mpr ⟨0, mem_Icc.mpr ?_, Int.cast_zero⟩⟩
    have hfloor := Int.floor_nonneg.mpr (zero_le_one.trans hH)
    exact ⟨neg_nonpos.mpr hfloor, hfloor⟩
  have hScard : (S.card : ℝ) ≤ 3 * H := by
    have hImage : S.card ≤ Z.card := Finset.card_image_le
    exact (show (S.card : ℝ) ≤ Z.card by exact_mod_cast hImage).trans (card_int_coordinateBox_le hH)
  have hcard :
      ((differencingDirections n H).filter condition).card ≤ (coordinateGrid S V).card := by
    apply Finset.card_le_card_of_injOn (fun (u : Fin n → ℤ) (i : Fin n) => (u i : K))
    · intro u hu
      obtain ⟨hu, huc⟩ := Finset.mem_filter.mp hu
      apply mem_coordinateGrid.mpr
      refine ⟨fun i => Finset.mem_image.mpr ⟨u i, mem_Icc.mpr ?_, rfl⟩, hcover u hu huc⟩
      have hi := (abs_differencingDirection_lt (zero_lt_one.trans_le hH) hu i).le
      rw [abs_le] at hi
      exact ⟨neg_le.mp (Int.le_floor.mpr (by exact_mod_cast (neg_le.mp hi.1))),
        Int.le_floor.mpr hi.2⟩
    · exact (injOn_cast_differencingDirections (K := K) (zero_lt_one.trans_le hH) hpH).mono
        (fun _ hx => (Finset.mem_filter.mp hx).1)
  have hcard' := hcard.trans (hV.card_coordinateGrid_le S hS)
  have hreal : (((differencingDirections n H).filter condition).card : ℝ) ≤
      (D : ℝ) * (S.card : ℝ)^l := by exact_mod_cast hcard'
  refine hreal.trans ?_
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hScard _) (Nat.cast_nonneg _)

/-- Directional differentiation with coefficients and directions in the same
field. -/
def directionalDerivativeOver {K : Type*} [CommRing K] {n : ℕ}
    (u : Fin n → K) (G : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K :=
  ∑ i, C (u i) * pderiv i G

theorem map_directionalDerivative {K : Type*} [CommRing K] {n : ℕ}
    (u : Fin n → ℤ) (G : IntForm n) :
    MvPolynomial.map (Int.castRingHom K) (directionalDerivative u G) =
      directionalDerivativeOver (fun i => (u i : K)) (MvPolynomial.map (Int.castRingHom K) G) := by
  simp [directionalDerivative, directionalDerivativeOver, pderiv_map]

/-- The geometric bad-direction locus, given by the dimension of the affine
gradient fiber over the algebraic closure. -/
def primeBadDirectionLocus {n : ℕ} (p : ℕ) [Fact p.Prime]
    (G : IntForm n) (j : ℕ) : Set (Fin n → AlgebraicClosure (ZMod p)) :=
  let K := AlgebraicClosure (ZMod p)
  let R := MvPolynomial (Fin n) K
  let g := MvPolynomial.map (Int.castRingHom K) G
  {u | (j : ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span
    (Set.range fun i : Fin n => pderiv i (directionalDerivativeOver u g)))}

theorem mem_primeBadDirectionLocus_of_dim {n p j : ℕ} [hp : Fact p.Prime] (G : IntForm n)
    (u : Fin n → ℤ) (hdim : PrimeGradientDimension p hp.out (directionalDerivative u G) j) :
    (fun i => (u i : AlgebraicClosure (ZMod p))) ∈ primeBadDirectionLocus p G j := by
  let K := AlgebraicClosure (ZMod p)
  let A := MvPolynomial (Fin n) K
  let uK (i : Fin n) : K := u i
  let M : IntForm n →+* A := MvPolynomial.map (Int.castRingHom K)
  let J : Ideal A := Ideal.span (Set.range fun i => pderiv i (directionalDerivativeOver uK (M G)))
  let I : Ideal A := Ideal.span (Set.range fun i => M (pderiv i (directionalDerivative u G)))
  have hf : (fun i => pderiv i (directionalDerivativeOver uK (M G))) =
      (fun i => M (pderiv i (directionalDerivative u G))) := by
    funext i
    change pderiv i (directionalDerivativeOver (fun j => (u j : K))
      (MvPolynomial.map (Int.castRingHom K) G)) =
      MvPolynomial.map (Int.castRingHom K) (pderiv i (directionalDerivative u G))
    rw [← map_directionalDerivative, pderiv_map]
  have hJI : J = I := by unfold J I; rw [hf]
  change ringKrullDim (A ⧸ I) = (j : ℕ∞) at hdim
  change (j : ℕ∞) ≤ ringKrullDim (A ⧸ J)
  rw [hJI]
  exact hdim.ge

/-- The remaining geometric input to the direction count. The bad loci admit
the coordinate-slicing budgets from the degree bound in Browning–Heath-Brown,
Lemma 1, with the affine dimensions from Browning–Prendiville, Lemma 2.4. -/
def PrimeDirectionSlicing (n d : ℕ) : Prop :=
  ∃ D : ℕ, ∀ (p : ℕ) (hp : p.Prime) (e : ℕ), 2 < e → e ≤ d → d < p →
    ∀ (G : IntForm n), G.IsHomogeneous e → ∀ s j : ℕ, s ≤ n → j ≤ n →
      s < j → PrimeGradientDimension p hp G s →
      letI : Fact p.Prime := ⟨hp⟩
      CoordinateSlicing (n - (j - s)) D (primeBadDirectionLocus p G j)

/-- The geometric bound, composed with reduction and coordinate slicing, yields
the one-prime direction estimate in the integer differencing box. -/
theorem primeDirectionBound_of_slicing {n d : ℕ} (hgeom : PrimeDirectionSlicing n d) :
    PrimeDirectionBound n d := by
  classical
  obtain ⟨D, hD⟩ := hgeom
  refine ⟨((D : ℝ) + 1) * 3^n, by positivity, ?_⟩
  intro p hp e he hed hdp G hG s j hs hj hdim H hH hpH
  letI : Fact p.Prime := ⟨hp⟩
  have hle : j - s ≤ n := (Nat.sub_le _ _).trans hj
  rw [← Nat.cast_sub hle, Real.rpow_natCast]
  by_cases hsj : s < j
  · have hcut := card_filter_differencingDirections_le_of_slicing hH hpH
      (fun u => PrimeGradientDimension p hp (directionalDerivative u G) j)
      (hD p hp e he hed hdp G hG s j hs hj hsj hdim)
      (fun u _ hu => mem_primeBadDirectionLocus_of_dim G u hu)
    exact hcut.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (le_add_of_nonneg_right zero_le_one)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.sub_le _ _))
        (by positivity) (by positivity))
      (by positivity))
  · rw [Nat.sub_eq_zero_of_le (not_lt.mp hsj), Nat.sub_zero]
    let I := Finset.Icc (-⌊H⌋) ⌊H⌋
    have hsub : differencingDirections n H ⊆ Fintype.piFinset (fun _ : Fin n => I) := by
      intro u hu
      apply Fintype.mem_piFinset.mpr
      intro i
      have hi := abs_le.mp (abs_differencingDirection_lt (zero_lt_one.trans_le hH) hu i).le
      exact mem_Icc.mpr ⟨neg_le.mp (Int.le_floor.mpr (by exact_mod_cast (neg_le.mp hi.1))),
        Int.le_floor.mpr hi.2⟩
    have hc := (Finset.card_filter_le (differencingDirections n H)
      (fun u => PrimeGradientDimension p hp (directionalDerivative u G) j)).trans
      (Finset.card_le_card hsub)
    rw [Fintype.card_piFinset_const] at hc
    refine (show _ ≤ (I.card : ℝ)^n by exact_mod_cast hc).trans ?_
    refine (pow_le_pow_left₀ (Nat.cast_nonneg _) (card_int_coordinateBox_le hH) n).trans ?_
    rw [mul_pow, mul_assoc]
    exact le_mul_of_one_le_left (by positivity) (le_add_of_nonneg_left (Nat.cast_nonneg _))

end

end Birch
