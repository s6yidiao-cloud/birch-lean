import Birch.NativeWeilSpectrum
import Birch.IndependentWeilHypersurfaceLefschetz
import Birch.IndependentWeilFermatRanks
import Birch.FermatAmbientComparison

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Filter MvPolynomial

namespace Birch

attribute [local instance] MvPolynomial.gradedAlgebra

theorem nativeSmoothHypersurfaceSpectrum {d : ℕ} (hd : 2 ≤ d) :
    PrimeSmoothHypersurfaceMiddleSpectralData d := by
  intro p _ _ hdp m hm G hG hG₀ hjac
  obtain ⟨N, rfl⟩ : ∃ N, m = N+2 := ⟨m-2, by omega⟩
  let k := ZMod p
  let S := Spec (CommRingCat.of k)
  let X := projectiveHypersurface hG
  let hF := isHomogeneous_fermatPolynomial k N d
  let F := projectiveHypersurface hF
  let P := Proj (homogeneousSubmodule (Fin (N+2)) k)
  let fX : X ⟶ S := projectiveHypersurfaceToField hG
  let fF : F ⟶ S := projectiveHypersurfaceToField hF
  let fP : P ⟶ S := projectivePolynomialSpaceToField (Fin (N+2)) k
  let : X.Over S := ⟨fX⟩
  let : F.Over S := ⟨fF⟩
  let : P.Over S := ⟨fP⟩
  have hdk : (d : k) ≠ 0 := by
    intro h
    exact hdp.not_ge (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff k p d).mp h))
  have hd₀ : 0 < d := by omega
  have hXproper : IsProper (X ↘ S) := isProper_projectiveHypersurfaceToField hG hd₀
  have hXsmooth : SmoothOfRelativeDimension N (X ↘ S) := by
    change SmoothOfRelativeDimension N (projectiveHypersurfaceToField hG)
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
      smoothOfRelativeDimension_projectiveHypersurfaceToField hG hjac
  have hXint : GeometricallyIntegral (X ↘ S) :=
    geometricallyIntegral_projectiveHypersurfaceToField hm hd hdk hG hjac
  have hXconn : GeometricallyConnected (X ↘ S) :=
    GeometricallyIntegral.geometricallyConnected (X ↘ S)
  have hjacF := exists_projectiveJacobianCertificate_fermat (F := k) N d hdk
  have : IsProper (F ↘ S) := isProper_projectiveHypersurfaceToField hF hd₀
  have : SmoothOfRelativeDimension N (F ↘ S) := by
    change SmoothOfRelativeDimension N (projectiveHypersurfaceToField hF)
    simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
      smoothOfRelativeDimension_projectiveHypersurfaceToField hF hjacF
  have : GeometricallyIntegral (F ↘ S) :=
    geometricallyIntegral_projectiveHypersurfaceToField hm hd hdk hF hjacF
  have hFconn : GeometricallyConnected (F ↘ S) :=
    GeometricallyIntegral.geometricallyConnected (F ↘ S)
  have hPproper : IsProper (P ↘ S) := isProper_projectivePolynomialSpaceToField
  have hPsmooth : SmoothOfRelativeDimension (N+1) (P ↘ S) := by
    change SmoothOfRelativeDimension (N+1) (projectivePolynomialSpaceToField (Fin (N+2)) k)
    simpa only [Fintype.card_fin, show N + 2 - 1 = N + 1 by omega] using
      (smoothOfRelativeDimension_projectivePolynomialSpaceToField (σ := Fin (N+2)) (K := k))
  have hPint : GeometricallyIntegral (P ↘ S) := geometricallyIntegral_projectivePolynomialSpaceToField
  have hPconn : GeometricallyConnected (P ↘ S) :=
    GeometricallyIntegral.geometricallyConnected (P ↘ S)
  have hl : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkl : Fact (ringChar k ≠ 2) := ⟨by
    change ringChar (ZMod p) ≠ 2
    rw [ZMod.ringChar_zmod_n]
    omega⟩
  have hkcard : Nat.card k = p := by
    change Nat.card (ZMod p) = p
    rw [Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨QX, AX, hQX, hAX, _, hXdual, hXweight, hXrank, _, hXtrace⟩ :=
    nativeWeilSpectrumWithRanks k X N
  obtain ⟨_, AF, _, _, _, hFdual, hFweight, hFrank, _, hFtrace⟩ :=
    nativeWeilSpectrumWithRanks k F N
  obtain ⟨QP, AP, hQP, hAP, hPzero, _, hPweight, _, _, hPtrace⟩ :=
    nativeWeilSpectrumWithRanks k P (N+1)
  have hlower (i : ℕ) (hi : i < N) : AX i = AP i := by
    obtain ⟨e⟩ := nonempty_equiv_projectiveHypersurfaceConstantCohomology_of_lt
      2 hG hd₀ hG₀ hi
    rw [hAX, hAP]
    exact Scheme.weilInverseRoots_eq_of_cohomologyEquiv
      (dX := N) (dY := N + 1) (i := i) (l := 2) (by omega) (by omega) hQX hQP e.symm
  have hRank : (AX N).card = (AF N).card := by
    rw [hXrank 2 N (by omega), hFrank 2 N (by omega)]
    exact finrank_projectiveHypersurfaceConstantCohomology_eq_fermat 2 hdk hG hjac N
  rw [hkcard] at hXdual hXweight hFdual hFweight hPweight
  obtain ⟨hout, hmid⟩ := tateSpectrum_and_middleRank_of_fermat_and_ambient hd₀ AX AF AP
    hFweight hFdual hFtrace hPzero hPweight hPtrace hXdual hlower hRank
  refine ⟨AX, ?_, ?_, ?_, ?_⟩
  · rw [show N + 2 - 2 = N by omega]
    change (Nat.card (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k))) ⟶
      Over.mk (X ↘ Spec (.of k))) : ℂ) = _
    simpa only [Module.finrank_self, pow_one, Multiset.map_id'] using hXtrace k
  · simpa only [Nat.add_sub_cancel] using hout
  · simpa only [Nat.add_sub_cancel] using hmid
  · exact fun α hα => by
      simpa only [Nat.add_sub_cancel] using hXweight N (by omega) α
        (by simpa only [Nat.add_sub_cancel] using hα)

end Birch
