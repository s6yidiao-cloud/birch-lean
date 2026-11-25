import Birch.NativeHypersurfaceSpectrum
import Birch.FinalRegularLevelCounts

namespace Birch

open Filter

/-- Smooth proper Weil spectra, weak Lefschetz and the Fermat rank comparison
supply the uniform projective spectrum used in the regular-level argument. -/
theorem native_eventualPrimeSmoothProjectiveSpectrumAtDimension {d m : ℕ}
    (hd : 2 ≤ d) (hm : 3 ≤ m) :
    EventualPrimeSmoothProjectiveSpectrumAtDimension d m := by
  refine ⟨(d-1)^m+1, Eventually.of_forall ?_⟩
  intro p _ _ hdp G hG hG₀ hjac
  exact nativeSmoothHypersurfaceSpectrum hd p hdp m hm G hG hG₀ hjac


/-- The smooth-projective Weil theorem and the regular-level argument
supply the four conclusions with no additional mathematical premise. -/
theorem nativeUnconditionalFinalResults :
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧
      FinalCoverAsymptotic :=
  finalResults_of_smoothProjectiveSpectrum fun _ hr _ hm =>
    native_eventualPrimeSmoothProjectiveSpectrumAtDimension (by omega) (by omega)

/-- The smooth Hasse principle at the stated dimension threshold. -/
theorem finalSmoothHassePrinciple : FinalSmoothHassePrinciple :=
  nativeUnconditionalFinalResults.1

/-- The weighted form asymptotic at the stated dimension threshold. -/
theorem finalFormAsymptotic : FinalFormAsymptotic :=
  nativeUnconditionalFinalResults.2.1

/-- The Serre bound for integral pairs on polynomial covers. -/
theorem finalCoverSerreBound : FinalCoverSerreBound :=
  nativeUnconditionalFinalResults.2.2.1

/-- The weighted asymptotic for polynomial covers. -/
theorem finalCoverAsymptotic : FinalCoverAsymptotic :=
  nativeUnconditionalFinalResults.2.2.2

end Birch
