import Birch.FinalCovers
import Birch.DeligneDimwiseRegularLevelCounts
import Birch.ProjectiveCurveCounts

/-! # The main results from regular level counts over prime fields -/

namespace Birch

/-- Square-root point counts on regular affine levels suffice in every terminal degree. -/
theorem finalResults_of_regularAffineLevelCounts
    (hcount : ∀ r, 3 ≤ r → ∀ n, 3 ≤ n →
      EventualPrimeRegularAffineLevelCountsAtDimension r n) :
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧
      FinalCoverAsymptotic := by
  apply finalResults_of_terminalPrimeBoundsWithLoss
  intro d δ hδ r hr _ l hl
  exact uniformTwistedPrimeBoundWithLoss_of_higher_dimwise_regularLevels hr (by omega)
    (hcount r hr) hδ

/-- For regular affine levels it suffices to supply smooth projective hypersurface
spectra with the ambient Tate terms and a dimensionwise middle-rank bound.
Projective curves are handled by the plane Stepanov bound. -/
theorem finalResults_of_smoothProjectiveSpectrum
    (hSpectrum : ∀ r, 3 ≤ r → ∀ m, 4 ≤ m →
      EventualPrimeSmoothProjectiveSpectrumAtDimension r m) :
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧
      FinalCoverAsymptotic := by
  apply finalResults_of_regularAffineLevelCounts
  intro r hr n hn
  apply eventual_primeRegularAffineLevelCountsAtDimension_of_projectiveCounts (by omega) hn
  · exact eventual_primeSmoothProjectiveCountAtDimension_of_spectrum (by omega)
      (hSpectrum r hr (n+1) (by omega))
  · by_cases h : n = 3
    · subst n
      exact eventual_primeSmoothProjectiveCountAtDimension_three_of_stepanov (by omega)
    · exact eventual_primeSmoothProjectiveCountAtDimension_of_spectrum (by omega)
        (hSpectrum r hr n (by omega))

end Birch
