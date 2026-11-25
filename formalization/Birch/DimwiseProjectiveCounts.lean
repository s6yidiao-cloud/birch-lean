import Birch.DeligneGoodLevelCounts
import Birch.SmoothHypersurfaceSpectrum

open AlgebraicGeometry CategoryTheory Filter MvPolynomial

namespace Birch

/-- A fixed-dimensional projective point count. The bound and prime cutoff
may vary with both the degree and the number of projective coordinates. -/
def EventualPrimeSmoothProjectiveCountAtDimension (r m : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], r < p →
      ∀ (G : MvPolynomial (Fin m) (ZMod p)), G.IsHomogeneous r → G ≠ 0 →
        (∀ j : Fin m, ∃ N : ℕ, X j ^ N ∈
          Ideal.span (insert G (Set.range fun i : Fin m => pderiv i G))) →
        |(Nat.card (projectiveHypersurfacePoints G) : ℝ) -
          (projectiveSpacePointCount p (m-2) : ℝ)| ≤ C * (p : ℝ)^(((m-2 : ℕ) : ℝ)/2)

/-- Only the smooth projective closure and its smooth boundary occur in a
regular affine-level count. Their constants need no relation to one another. -/
theorem eventual_primeRegularAffineLevelCountsAtDimension_of_projectiveCounts
    {r n : ℕ} (hr : 2 ≤ r) (hn : 3 ≤ n)
    (hclosure : EventualPrimeSmoothProjectiveCountAtDimension r (n+1))
    (hboundary : EventualPrimeSmoothProjectiveCountAtDimension r n) :
    EventualPrimeRegularAffineLevelCountsAtDimension r n := by
  obtain ⟨A, hA, hAcount⟩ := hclosure
  obtain ⟨B, hB, hBcount⟩ := hboundary
  refine ⟨max 1 (A+B), le_max_left _ _, ?_⟩
  filter_upwards [hAcount, hBcount] with p hpA hpB
  intro _ _ hrp g hg hcrit t ht
  let Q := homogeneousComponent r g
  have hr₀ : 0 < r := by omega
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hQ : Q ≠ 0 := by
    intro hz
    have h := hcrit (fun _ => 1) (by
      change ∀ i, (pderiv i Q).eval₂ _ _ = 0
      simp [hz])
    exact one_ne_zero (congrFun h ⟨0, by omega⟩)
  have hH : deligneLevelClosureFin r g t ≠ 0 := by
    intro hz
    have hz' : deligneLevelClosure r g t = 0 := by
      apply rename_injective (R := ZMod p) _ (finSuccEquiv n).symm.injective
      simpa only [map_zero, deligneLevelClosureFin] using hz
    have h := setExtraCoordinateZero_deligneLevelClosure hr₀ g t
    rw [hz', map_zero] at h
    exact hQ h.symm
  have hA' := hpA hrp _ (isHomogeneous_deligneLevelClosureFin r g t) hH
    (exists_deligneLevelClosureFin_jacobianCertificate_of_regularLevel hr₀ hg hcrit ht)
  rw [show n+1-2 = n-1 by omega] at hA'
  have hB' := hpB hrp Q (homogeneousComponent_isHomogeneous r g) hQ
    (exists_projectiveJacobianCertificate (K := AlgebraicClosure (ZMod p)) Q
      (fun x _ hx => hcrit x hx))
  let E := (p : ℝ)^(((n-1 : ℕ) : ℝ)/2)
  have hB'' : |(Nat.card (projectiveHypersurfacePoints Q) : ℝ) -
      (projectiveSpacePointCount p (n-2) : ℝ)| ≤ B * E := by
    refine hB'.trans (mul_le_mul_of_nonneg_left ?_ hB)
    exact Real.rpow_le_rpow_of_exponent_le hp (by gcongr; omega)
  have h := abs_sub_affinePolynomialLevelCount_le_of_projectiveCounts (by omega : 2 ≤ n)
    hr₀ hg t (by simpa only [ZMod.card] using (show _ ≤ A * E from hA'))
    (by simpa only [ZMod.card] using hB'')
  rw [ZMod.card] at h
  refine h.trans ?_
  change A * E + B * E ≤ max 1 (A+B) * E
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by dsimp [E]; positivity)

/-- The part of the Weil spectrum needed in a single projective dimension.
The middle rank has a prime-uniform bound that can depend on the dimension. -/
def EventualPrimeSmoothProjectiveSpectrumAtDimension (r m : ℕ) : Prop :=
  ∃ b : ℕ, ∀ᶠ p : ℕ in atTop, ∀ [Fact p.Prime] [NeZero p], r < p →
    ∀ (G : MvPolynomial (Fin m) (ZMod p)) (hG : G.IsHomogeneous r), G ≠ 0 →
      (∀ j : Fin m, ∃ N : ℕ, X j ^ N ∈
        Ideal.span (insert G (Set.range fun i : Fin m => pderiv i G))) →
      ∃ A : ℕ → Multiset ℂ,
        (Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p)))) ⟶
          Over.mk (projectiveHypersurfaceToField hG)) : ℂ) =
          ∑ i ∈ Finset.Iic (2*(m-2)), (-1 : ℂ)^i * (A i).sum ∧
        (∀ i ≤ 2*(m-2), i ≠ m-2 → A i = projectiveTateSpectrum p i) ∧
        (A (m-2)).card ≤ b ∧
        (∀ α ∈ A (m-2), ‖α‖ = Real.sqrt ((p : ℝ)^(m-2)))

/-- A dimensionwise bound for the middle spectrum suffices once the outer
Tate terms have been identified. -/
theorem eventual_primeSmoothProjectiveCountAtDimension_of_spectrum
    {r m : ℕ} (hr : 2 ≤ r)
    (hdata : EventualPrimeSmoothProjectiveSpectrumAtDimension r m) :
    EventualPrimeSmoothProjectiveCountAtDimension r m := by
  obtain ⟨b, hb⟩ := hdata
  refine ⟨(b : ℝ)+1, by positivity, ?_⟩
  filter_upwards [hb] with p hp
  intro _ _ hrp G hG hG₀ hjac
  obtain ⟨A, ht, hout, hrank, hw⟩ := hp hrp G hG hG₀ hjac
  have hpoints := Nat.card_congr
    (overHomEquivProjectiveHypersurfacePoints (K := ZMod p) (by omega) hG)
  rw [show algebraMap (ZMod p) (ZMod p) = RingHom.id _ from rfl, MvPolynomial.map_id] at hpoints
  rw [← hpoints]
  exact (abs_sub_projectiveSpacePointCount_le_of_middleRank A ht hout hw).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hrank 1) (by positivity))

/-- Dimwise Weil spectra for smooth projective hypersurfaces supply
every higher-dimensional regular affine level count in the same degree. -/
theorem eventual_primeRegularAffineLevelCountsAtDimension_of_projectiveSpectrum
    {r n : ℕ} (hr : 2 ≤ r) (hn : 3 ≤ n)
    (hclosure : EventualPrimeSmoothProjectiveSpectrumAtDimension r (n+1))
    (hboundary : EventualPrimeSmoothProjectiveSpectrumAtDimension r n) :
    EventualPrimeRegularAffineLevelCountsAtDimension r n :=
  eventual_primeRegularAffineLevelCountsAtDimension_of_projectiveCounts hr hn
    (eventual_primeSmoothProjectiveCountAtDimension_of_spectrum hr hclosure)
    (eventual_primeSmoothProjectiveCountAtDimension_of_spectrum hr hboundary)

end Birch
