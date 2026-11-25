import Birch.DeligneProjectivePointCounts
import Birch.HypersurfaceSpectralData
import Birch.ProjectiveExtensionPoints
import Birch.ProjectiveSmoothIntegral
import Birch.ProjectiveHypersurfaceSmooth

/-! # Smooth projective estimates from outer Tate terms and a middle rank bound -/

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Birch

/-- The prime-field hypersurface defined by a Jacobian-certified equation
has the geometric hypotheses of the smooth proper Weil theorem. -/
theorem smoothHypersurface_weilGeometry {p m d : ℕ} [Fact p.Prime]
    (hm : 3 ≤ m) (hd : 2 ≤ d) (hdp : d < p)
    {G : MvPolynomial (Fin m) (ZMod p)} (hG : G.IsHomogeneous d)
    (hjac : ∀ j : Fin m, ∃ N : ℕ, X j ^ N ∈
      Ideal.span (insert G (Set.range fun i : Fin m => pderiv i G))) :
    IsProper (projectiveHypersurfaceToField hG) ∧
    GeometricallyIrreducible (projectiveHypersurfaceToField hG) ∧
    SmoothOfRelativeDimension (m-2) (projectiveHypersurfaceToField hG) := by
  have hd₀ : (d : ZMod p) ≠ 0 := fun h => hdp.not_ge
    (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff d p).mp h))
  let := geometricallyIntegral_projectiveHypersurfaceToField hm hd hd₀ hG hjac
  exact ⟨isProper_projectiveHypersurfaceToField hG (by omega), inferInstance, by
    simpa only [Fintype.card_fin] using smoothOfRelativeDimension_projectiveHypersurfaceToField hG hjac⟩

/-- Outside the middle degree, cancellation of the ambient Tate spectrum
leaves an error bounded by the middle rank plus one. -/
theorem abs_sub_projectiveSpacePointCount_le_of_middleRank {q N count : ℕ}
    (A : ℕ → Multiset ℂ)
    (htrace : (count : ℂ) = ∑ i ∈ Finset.Iic (2*N), (-1 : ℂ)^i * (A i).sum)
    (hTate : ∀ i ≤ 2*N, i ≠ N → A i = projectiveTateSpectrum q i)
    (hweight : ∀ α ∈ A N, ‖α‖ = Real.sqrt ((q : ℝ)^N)) :
    |(count : ℝ) - (projectiveSpacePointCount q N : ℝ)| ≤
      ((A N).card + 1 : ℝ) * (q : ℝ)^((N : ℝ)/2) := by
  let R := (q : ℝ)^((N : ℝ)/2)
  have hR : 0 ≤ R := by positivity
  have hcount : (count : ℂ) - (projectiveSpacePointCount q N : ℂ) =
      (-1 : ℂ)^N * ((A N).sum - (projectiveTateSpectrum q N).sum) := by
    rw [htrace, ← alternating_sum_projectiveTateSpectrum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single N, ← mul_sub]
    · intro i hi h
      rw [hTate i (Finset.mem_Iic.mp hi) h, sub_self]
    · intro h
      exact (h (Finset.mem_Iic.mpr (by omega))).elim
  have hsum : ‖(A N).sum‖ ≤ ((A N).card : ℝ) * R := by
    refine (norm_multiset_sum_le _).trans ?_
    have h := Multiset.sum_le_card_nsmul ((A N).map norm) R (fun a ha => by
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp ha
      rw [hweight α hα, Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (Nat.cast_nonneg q)]
      exact le_of_eq (by dsimp [R]; congr 1; ring))
    simpa only [nsmul_eq_mul, Multiset.card_map] using h
  have hTateN : ‖(projectiveTateSpectrum q N).sum‖ ≤ R := by
    by_cases h : Even N
    · simp only [projectiveTateSpectrum, ite_eq_left h, Multiset.sum_singleton, norm_pow, Complex.norm_natCast]
      have he : ((N/2 : ℕ) : ℝ) = (N : ℝ)/2 := by
        obtain ⟨a, ha⟩ := h
        have hhalf : N / 2 = a := by omega
        rw [hhalf, ha, Nat.cast_add]
        ring
      rw [← Real.rpow_natCast, he]
    · simpa only [projectiveTateSpectrum, ite_eq_right h, Multiset.sum_zero, norm_zero] using hR
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  push_cast
  rw [hcount, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact (norm_sub_le _ _).trans ((add_le_add hsum hTateN).trans_eq (by rw [add_mul, one_mul]))

/-- The outer Tate terms and a coarse middle-rank bound suffice for the
prime-uniform projective count, without the exact primitive Betti formula. -/
theorem uniformPrimeSmoothHypersurfacePointCountsWithBase_of_middleSpectralData {d : ℕ}
    (hd : 2 ≤ d) (hdata : PrimeSmoothHypersurfaceMiddleSpectralData d) :
    UniformPrimeSmoothHypersurfacePointCountsWithBase d (3*((d : ℝ)-1)^2) := by
  intro p _ _ hdp m hm G hG hG₀ hjac
  obtain ⟨A, ht, hout, hrank, hw⟩ := hdata p hdp m hm G hG hG₀ hjac
  have hpoints := Nat.card_congr
    (overHomEquivProjectiveHypersurfacePoints (K := ZMod p) (by omega) hG)
  rw [show algebraMap (ZMod p) (ZMod p) = RingHom.id _ from rfl, MvPolynomial.map_id] at hpoints
  rw [← hpoints]
  refine (abs_sub_projectiveSpacePointCount_le_of_middleRank A ht hout hw).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  let B : ℝ := (d : ℝ)-1
  have hB : 1 ≤ B := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
    dsimp [B]
    linarith
  have hC : ((A (m-2)).card : ℝ) ≤ B ^ m + 1 := by
    have h := (show ((A (m-2)).card : ℝ) ≤ (((d-1)^m+1 : ℕ) : ℝ) by exact_mod_cast hrank)
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, Nat.cast_sub (show 1 ≤ d by omega), B] using h
  change _ ≤ (3*B^2)^(m-1)
  rw [mul_pow, ← pow_mul]
  calc
    _ ≤ 3 * B^m := by linarith [one_le_pow₀ hB (n := m)]
    _ ≤ _ := mul_le_mul
      (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (show 1 ≤ m-1 by omega))
      (pow_le_pow_right₀ hB (by omega)) (by positivity) (by positivity)

/-- The supplied base is at least the classical rate needed for the
zero-dimensional boundary estimates. -/
theorem exists_uniformSmoothCountsWithBase_of_middleSpectralData {d : ℕ} (hd : 2 ≤ d)
    (hdata : PrimeSmoothHypersurfaceMiddleSpectralData d) :
    ∃ B : ℝ, (d : ℝ)-1 ≤ B ∧ UniformPrimeSmoothHypersurfacePointCountsWithBase d B := by
  refine ⟨_, ?_, uniformPrimeSmoothHypersurfacePointCountsWithBase_of_middleSpectralData hd hdata⟩
  have h : (2 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (d : ℝ)-1 by linarith)
    (show (0 : ℝ) ≤ (d : ℝ)-2 by linarith)]

end Birch
