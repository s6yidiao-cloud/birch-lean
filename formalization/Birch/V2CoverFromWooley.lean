import Birch.V2CoverVinogradovInterval
import GafniTao.WooleySourceCriticalBase
import GafniTao.WooleySourceToPadic
import GafniTao.WooleyPadicToCritical

/-! # The manuscript results with Deligne's finite-field estimate -/

namespace Birch

private theorem vinogradovCriticalIndex_eq_ford (e : ℕ) :
    vinogradovCriticalIndex e = GafniTao.fordVinogradovKappa e := by
  unfold GafniTao.fordVinogradovKappa
  have := vinogradovCriticalIndex_twice e
  omega

/-- The nested efficient congruencing proof gives the signed-interval
critical Vinogradov estimate. -/
theorem criticalVinogradovEstimate_of_wooley {e : ℕ} (he : 1 ≤ e) :
    CriticalVinogradovEstimate e := by
  have hcritical := GafniTao.vinogradovCriticalEndpoint_of_wooleyPadic
    (GafniTao.wooleyMonomialPadicConcentration_of_polynomialCorollary32
      GafniTao.wooleyPolynomialCorollary32_native)
  apply criticalVinogradovEstimate_of_initialInterval
  intro ε hε
  obtain ⟨C, hC, h⟩ := hcritical e ε he hε
  refine ⟨C, hC, fun Q hQ => ?_⟩
  have hbound := h Q hQ
  rw [GafniTao.fordLambda34_critical, ← vinogradovCriticalIndex_eq_ford] at hbound
  exact hbound

end Birch
