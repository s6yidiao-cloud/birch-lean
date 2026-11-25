import Birch.DeligneTensorPhase
import Birch.ProjectiveCoordinatePoints
import Birch.ProjectiveJacobianCertificate
import Birch.ProjectiveWeilPointCount
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! # Finite projective point counts for polynomial level sets -/

open MvPolynomial
open scoped BigOperators LinearAlgebra.Projectivization

namespace Birch

noncomputable section

/-- The boundary and the affine level partition the projective point count. -/
theorem natCard_deligneLevelClosure_points {n d : ℕ} {K : Type*} [Field K] [Fintype K]
    (hd : 0 < d) {g : MvPolynomial (Fin n) K} (hg : g.totalDegree ≤ d) (t : K) :
    Nat.card (projectiveHypersurfacePoints (deligneLevelClosure d g t)) =
      affinePolynomialLevelCount g t +
        Nat.card (projectiveHypersurfacePoints (homogeneousComponent d g)) := by
  classical
  let : Finite (projectiveHypersurfacePoints (homogeneousComponent d g)) :=
    inferInstanceAs (Finite {P : ℙ K (Fin n → K) // _})
  rw [Nat.card_congr (deligneLevelClosure_points_equiv hd hg t), Nat.card_sum]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

/-- The projective closure counted in linear coordinates has the same
affine and infinite parts. -/
theorem natCard_deligneLevelClosureFin_points {n d : ℕ} {K : Type*} [Field K] [Fintype K]
    (hd : 0 < d) {g : MvPolynomial (Fin n) K} (hg : g.totalDegree ≤ d) (t : K) :
    Nat.card (projectiveHypersurfacePoints (deligneLevelClosureFin d g t)) =
      affinePolynomialLevelCount g t +
        Nat.card (projectiveHypersurfacePoints (homogeneousComponent d g)) := by
  rw [deligneLevelClosureFin, ← Nat.card_congr
    (projectiveHypersurfacePoints_rename_equiv (isHomogeneous_deligneLevelClosure d g t)
      (finSuccEquiv n).symm)]
  exact natCard_deligneLevelClosure_points hd hg t

/-- Each increase in projective dimension adds its new affine chart. -/
theorem projectiveSpacePointCount_succ (q N : ℕ) :
    projectiveSpacePointCount q (N + 1) = projectiveSpacePointCount q N + q^(N+1) := by
  simp only [projectiveSpacePointCount, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]

/-- Subtracting the projective boundary cancels all but the top term in
the projective-space main term. -/
theorem abs_sub_affinePolynomialLevelCount_le_of_projectiveCounts {n d : ℕ}
    {K : Type*} [Field K] [Fintype K] (hn : 2 ≤ n) (hd : 0 < d)
    {g : MvPolynomial (Fin n) K} (hg : g.totalDegree ≤ d) (t : K) {E₁ E₂ : ℝ}
    (hclosure : |(Nat.card (projectiveHypersurfacePoints (deligneLevelClosureFin d g t)) : ℝ) -
      (projectiveSpacePointCount (Fintype.card K) (n-1) : ℝ)| ≤ E₁)
    (hboundary : |(Nat.card (projectiveHypersurfacePoints (homogeneousComponent d g)) : ℝ) -
      (projectiveSpacePointCount (Fintype.card K) (n-2) : ℝ)| ≤ E₂) :
    |(affinePolynomialLevelCount g t : ℝ) - (Fintype.card K : ℝ)^(n-1)| ≤ E₁ + E₂ := by
  let A := (Nat.card (projectiveHypersurfacePoints (deligneLevelClosureFin d g t)) : ℝ) -
      (projectiveSpacePointCount (Fintype.card K) (n-1) : ℝ)
  let B := (Nat.card (projectiveHypersurfacePoints (homogeneousComponent d g)) : ℝ) -
      (projectiveSpacePointCount (Fintype.card K) (n-2) : ℝ)
  have hmain : projectiveSpacePointCount (Fintype.card K) (n-1) =
      projectiveSpacePointCount (Fintype.card K) (n-2) + (Fintype.card K)^(n-1) := by
    have he : n-2+1 = n-1 := by omega
    simpa only [he] using projectiveSpacePointCount_succ (Fintype.card K) (n-2)
  have he : (affinePolynomialLevelCount g t : ℝ) - (Fintype.card K : ℝ)^(n-1) = A - B := by
    have hcount := congrArg (fun m : ℕ => (m : ℝ)) (natCard_deligneLevelClosureFin_points hd hg t)
    have hmean := congrArg (fun m : ℕ => (m : ℝ)) hmain
    push_cast at hcount hmean
    dsimp only [A,B]
    linarith
  rw [he]
  calc
    |A-B| ≤ |A| + |B| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le A (-B)
    _ ≤ E₁ + E₂ := add_le_add hclosure hboundary

/-- The smooth projective estimate needed for homogeneous phases.
The constant may depend on the degree and the prime but is uniform in the
number of variables. The ideal certificate is the projective Jacobian criterion. -/
def PrimeSmoothHypersurfacePointCounts (d : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero p], d < p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ), 3 ≤ m →
      ∀ G : MvPolynomial (Fin m) (ZMod p), G.IsHomogeneous d → G ≠ 0 →
        (∀ j : Fin m, ∃ N : ℕ, X j ^ N ∈
          Ideal.span (insert G (Set.range fun i : Fin m => pderiv i G))) →
        |(Nat.card (projectiveHypersurfacePoints G) : ℝ) -
          (projectiveSpacePointCount p (m-2) : ℝ)| ≤
            C * (((d : ℝ) - 1)^(m-1) * (p : ℝ)^(((m-2 : ℕ) : ℝ)/2))

/-- The smooth projective estimate with a fixed exponential base in dimension,
uniform in the prime and equation. -/
def UniformPrimeSmoothHypersurfacePointCountsWithBase (d : ℕ) (B : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero p], d < p →
    ∀ (m : ℕ), 3 ≤ m →
      ∀ G : MvPolynomial (Fin m) (ZMod p), G.IsHomogeneous d → G ≠ 0 →
        (∀ j : Fin m, ∃ N : ℕ, X j ^ N ∈
          Ideal.span (insert G (Set.range fun i : Fin m => pderiv i G))) →
        |(Nat.card (projectiveHypersurfacePoints G) : ℝ) -
          (projectiveSpacePointCount p (m-2) : ℝ)| ≤
            B^(m-1) * (p : ℝ)^(((m-2 : ℕ) : ℝ)/2)

/-- The classical uniform estimate with exponential base `d - 1`. -/
abbrev UniformPrimeSmoothHypersurfacePointCounts (d : ℕ) : Prop :=
  UniformPrimeSmoothHypersurfacePointCountsWithBase d ((d : ℝ) - 1)

/-- The degree-`d` projective Frobenius spectra with their ambient Tate
contributions and exact primitive middle multiplicities. -/
def PrimeSmoothHypersurfaceSpectralData (d : ℕ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [NeZero p], d < p →
    ∀ (m : ℕ), 3 ≤ m →
      ∀ G : MvPolynomial (Fin m) (ZMod p), G.IsHomogeneous d → G ≠ 0 →
        (∀ j : Fin m, ∃ N : ℕ, X j ^ N ∈
          Ideal.span (insert G (Set.range fun i : Fin m => pderiv i G))) →
        ∃ (A : ℕ → Multiset ℂ) (primitive : Multiset ℂ),
          (Nat.card (projectiveHypersurfacePoints G) : ℂ) =
            ∑ i ∈ Finset.Iic (2*(m-2)), (-1 : ℂ)^i * (A i).sum ∧
          (∀ i ≤ 2*(m-2),
            A i = projectiveTateSpectrum p i + if i = m-2 then primitive else 0) ∧
          (d : ℤ)*(primitive.card : ℤ) =
            ((d : ℤ)-1)^((m-2)+2) + (-1 : ℤ)^(m-2)*((d : ℤ)-1) ∧
          (∀ α ∈ A (m-2), ‖α‖ = Real.sqrt ((p : ℝ)^(m-2)))

/-- The Weil trace and weights, ambient Tate spectrum, and primitive Betti
formula give the uniform projective estimate with constant one.
The trace hypothesis uses the cardinality of the projective polynomial point
set, so applying a scheme trace theorem requires transporting its point count. -/
theorem uniformPrimeSmoothHypersurfacePointCounts_of_weilSpectrum {d : ℕ} (hd : 2 ≤ d)
    (hspectrum : PrimeSmoothHypersurfaceSpectralData d) :
    UniformPrimeSmoothHypersurfacePointCounts d := by
  intro p _ _ hdp m hm G hG hG₀ hcert
  obtain ⟨A, primitive, htrace, hTate, hBetti, hweight⟩ := hspectrum p hdp m hm G hG hG₀ hcert
  have h := abs_sub_projectiveSpacePointCount_le_of_weilSpectrum A primitive
    htrace hTate (primitiveHypersurfaceBetti_le_of_formula hd hBetti) hweight
  rw [Nat.cast_pow, Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one,
    show m-2+1 = m-1 by omega] at h
  exact h

/-- A bound uniform in the prime supplies the homogeneous amplification input. -/
theorem primeSmoothHypersurfacePointCounts_of_uniform {d : ℕ}
    (hcount : UniformPrimeSmoothHypersurfacePointCounts d) : PrimeSmoothHypersurfacePointCounts d := by
  intro p _ _ hdp
  refine ⟨1, zero_le_one, ?_⟩
  simpa only [one_mul] using hcount p hdp

/-- A smooth projective trace and spectrum control homogeneous character sums
through the smooth projective point-count estimate. -/
theorem primeSmoothHypersurfacePointCounts_of_weilSpectrum {d : ℕ} (hd : 2 ≤ d)
    (hspectrum : PrimeSmoothHypersurfaceSpectralData d) : PrimeSmoothHypersurfacePointCounts d :=
  primeSmoothHypersurfacePointCounts_of_uniform
    (uniformPrimeSmoothHypersurfacePointCounts_of_weilSpectrum hd hspectrum)

/-- Nonzero levels of homogeneous phases inherit the uniform square-root
bound from the smooth projective closure and its smooth boundary. -/
theorem prime_homogeneousAffineLevelPointCounts_of_smoothHypersurfacePointCounts
    {d : ℕ} (hd : 2 ≤ d) (hcount : PrimeSmoothHypersurfacePointCounts d)
    (p : ℕ) [Fact p.Prime] [NeZero p] (hdp : d < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n →
      ∀ g : MvPolynomial (Fin n) (ZMod p), g.IsHomogeneous d →
        PrimeIsolatedLeadingCriticalPoint p d g → ∀ (t : ZMod p), t ≠ 0 →
        |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤
          C * (((d : ℝ)-1)^n * (p : ℝ)^((n : ℝ)/2)) := by
  classical
  obtain ⟨C, hC, hproj⟩ := hcount p hdp
  have hd₀ : 0 < d := by omega
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hd₁ : (1 : ℝ) ≤ (d : ℝ)-1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨2*C+(p : ℝ)^2, by positivity, ?_⟩
  intro n hn g hg hcrit t ht
  let A : ℝ := ((d : ℝ)-1)^n * (p : ℝ)^((n : ℝ)/2)
  change |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤ (2*C+(p : ℝ)^2)*A
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd₁)
    (Real.one_le_rpow hp₁ (by positivity))
  by_cases hn₃ : 3 ≤ n
  · let K := AlgebraicClosure (ZMod p)
    have hbcrit (x : Fin n → K) :
        (∀ i, (pderiv i g).eval₂ (algebraMap (ZMod p) K) x = 0) → x = 0 := by
      have h := hcrit x
      change (∀ i, (pderiv i (homogeneousComponent d g)).eval₂
        (algebraMap (ZMod p) K) x = 0) → x = 0 at h
      rw [homogeneousComponent_eq_self hg] at h
      exact h
    have hg₀ : g ≠ 0 := by
      intro hz
      have h := hbcrit (fun _ => 1) (by simp [hz])
      exact one_ne_zero (congrFun h ⟨0, hn⟩)
    have hboundary := hproj n hn₃ g hg hg₀
      (exists_projectiveJacobianCertificate g (fun x _ hx => hbcrit x hx))
    have hclosure := hproj (n+1) (by omega) (deligneLevelClosureFin d g t)
      (isHomogeneous_deligneLevelClosureFin d g t)
      (deligneLevelClosureFin_ne_zero_of_homogeneous hd₀ hg ht)
      (exists_deligneLevelClosureFin_jacobianCertificate_of_homogeneous hd₀ hdp hg hcrit ht)
    have hscale (m : ℕ) (hm : m ≤ n+1) :
        C * (((d : ℝ)-1)^(m-1) * (p : ℝ)^(((m-2 : ℕ) : ℝ)/2)) ≤ C*A := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul
      · exact pow_le_pow_right₀ hd₁ (by omega)
      · apply Real.rpow_le_rpow_of_exponent_le hp₁
        have hle : ((m-2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show m-2 ≤ n by omega)
        linarith
      · positivity
      · positivity
    have hab := hboundary.trans (hscale n (by omega))
    have hac := hclosure.trans (hscale (n+1) le_rfl)
    rw [show n+1-2 = n-1 by omega] at hac
    rw [← homogeneousComponent_eq_self hg] at hab
    have h := abs_sub_affinePolynomialLevelCount_le_of_projectiveCounts (by omega) hd₀
      hg.totalDegree_le t (by simpa only [ZMod.card] using hac) (by simpa only [ZMod.card] using hab)
    rw [ZMod.card] at h
    refine h.trans ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (p : ℝ)]) (zero_le_one.trans hA)
  · have hsize : (affinePolynomialLevelCount g t : ℝ) ≤ (p : ℝ)^n := by
      have hc : affinePolynomialLevelCount g t ≤ p^n := by
        have hcard : (Finset.univ : Finset (Fin n → ZMod p)).card = p^n := by
          simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
        rw [← hcard, affinePolynomialLevelCount]
        apply Finset.card_le_card
        exact fun x _ => Finset.mem_univ x
      exact_mod_cast hc
    have hmean : (p : ℝ)^(n-1) ≤ (p : ℝ)^n := pow_le_pow_right₀ hp₁ (Nat.sub_le _ _)
    have hdiff : |(affinePolynomialLevelCount g t : ℝ) - (p : ℝ)^(n-1)| ≤ (p : ℝ)^n := by
      refine abs_le.mpr ⟨?_,?_⟩ <;>
        linarith [show (0 : ℝ) ≤ (affinePolynomialLevelCount g t : ℝ) by positivity,
          show (0 : ℝ) ≤ (p : ℝ)^(n-1) by positivity]
    refine hdiff.trans ((pow_le_pow_right₀ hp₁ (show n ≤ 2 by omega)).trans ?_)
    exact (le_add_of_nonneg_left (by positivity)).trans
      (le_mul_of_one_le_right (by positivity) hA)

/-- The exact prime-field character estimate restricted to homogeneous phases. -/
theorem primeHomogeneousDeligneEstimate_of_smoothHypersurfacePointCounts {r : ℕ}
    (hr : 2 ≤ r) (hcount : PrimeSmoothHypersurfacePointCounts r)
    {l p : ℕ} [Fact p.Prime] [NeZero p] (hl : 0 < l) (hrp : r < p)
    (g : MvPolynomial (Fin l) (ZMod p)) (hg : g.IsHomogeneous r)
    (hcrit : PrimeIsolatedLeadingCriticalPoint p r g) :
    ‖primeDeligneSum p g‖ ≤ ((r : ℝ)-1)^l * (p : ℝ)^((l : ℝ)/2) := by
  obtain ⟨C,hC,hfib⟩ := prime_homogeneousAffineLevelPointCounts_of_smoothHypersurfacePointCounts
    hr hcount p hrp
  have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr ((Fact.out : p.Prime).pos)
  have hr₀ : (2 : ℝ) ≤ r := by exact_mod_cast hr
  unfold primeDeligneSum
  apply norm_character_sum_le_of_additivePowerFiberErrors
    (Fact.out : p.Prime).one_lt (fun x => g.eval x)
    (mul_pos (pow_pos (sub_pos.mpr (lt_of_lt_of_le one_lt_two hr₀)) _)
      (Real.rpow_pos_of_pos hp₀ _)) hC
  intro k hk t ht
  have hpos : 0 < l*k := Nat.mul_pos hl hk
  have hmean : (Fintype.card (Fin l → ZMod p) : ℝ)^k / p = (p : ℝ)^(l*k-1) := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, ← pow_mul,
      show l*k = (l*k-1)+1 by omega, pow_succ]
    exact mul_div_cancel_right₀ _ hp₀.ne'
  have hscale :
      ((r : ℝ)-1)^(k*l) * (p : ℝ)^(((k*l : ℕ) : ℝ)/2) =
        (((r : ℝ)-1)^l * (p : ℝ)^((l : ℝ)/2))^k := by
    rw [mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (Nat.cast_nonneg p),
      Nat.mul_comm k l, Nat.cast_mul]
    congr 2
    ring
  have hlevel : additivePowerFiberCount (fun x => g.eval x) k t =
      affinePolynomialLevelCount (additivePowerPolynomialFin k g) t := by
    rw [additivePowerFiberCount_eq_card_eval_additivePowerPolynomialFin,
      affinePolynomialLevelCount]
  have hhom : (additivePowerPolynomialFin k g).IsHomogeneous r := by
    apply IsHomogeneous.rename_isHomogeneous
    apply IsHomogeneous.sum
    exact fun j _ => hg.rename_isHomogeneous (f := Prod.mk j)
  rw [hmean, hlevel, ← hscale, Nat.mul_comm l k]
  exact hfib (k*l) (Nat.mul_pos hk hl) _ hhom
    (primeIsolatedLeadingCriticalPoint_additivePowerPolynomialFin k g hcrit) t ht

/-- The smooth projective point-count theorem suffices for the conductor-one
input for a homogeneous integral form. -/
theorem deligneConductorOne_of_smoothHypersurfacePointCounts {n d : ℕ}
    {F : IntForm n} (hF : F.IsHomogeneous d) (hd : 2 ≤ d)
    (hcount : PrimeSmoothHypersurfacePointCounts d) : DeligneConductorOne d F := by
  intro p _ _ hdp hcrit a ha
  by_cases hn : 0 < n
  · let f := MvPolynomial.map (Int.castRingHom (ZMod p)) F
    let g := C a * f
    have hg : g.IsHomogeneous d := (hF.map _).C_mul a
    have hgcrit : PrimeIsolatedLeadingCriticalPoint p d g := by
      intro x hx
      let K := AlgebraicClosure (ZMod p)
      let φ := algebraMap (ZMod p) K
      have hφ : φ.comp (Int.castRingHom (ZMod p)) = Int.castRingHom K := by
        ext
        simp [φ]
      apply (hcrit x).mp
      intro i
      have hi := hx i
      change (pderiv i (homogeneousComponent d g)).eval₂ φ x = 0 at hi
      rw [homogeneousComponent_eq_self hg, show g = C a * f by rfl, pderiv_C_mul,
        eval₂_mul, eval₂_C] at hi
      have h := (mul_eq_zero.mp hi).resolve_left ((map_ne_zero φ).mpr ha)
      change (pderiv i (MvPolynomial.map (Int.castRingHom (ZMod p)) F)).eval₂ φ x = 0 at h
      rw [pderiv_map, eval₂_map, hφ] at h
      exact h
    have hsum := primeHomogeneousDeligneEstimate_of_smoothHypersurfacePointCounts
      hd hcount hn hdp g hg hgcrit
    have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
    have hnorm : ‖completeSum F p a‖ = ‖primeDeligneSum p g‖ / (p : ℝ)^n := by
      simp only [completeSum, primeDeligneSum, g, f, residueEval, map_mul, eval_C,
        eval_map, ← div_eq_inv_mul, norm_div, norm_pow, Complex.norm_natCast]
    rw [hnorm]
    refine (div_le_div_of_nonneg_right hsum (by positivity)).trans_eq ?_
    rw [mul_div_assoc, ← Real.rpow_natCast (p : ℝ) n, ← Real.rpow_sub hp₀]
    congr 2
    ring
  · obtain rfl : n = 0 := by omega
    simpa using norm_completeSum_le_one F a

end
end Birch
