import Birch.CircleMethod
import Birch.CompleteSums
import Birch.MinorArcs

/-!
# Interfaces for the remaining analytic estimates

These propositions specify the input bounds used to combine the major and minor arcs.
The proof of a downstream theorem takes them as explicit hypotheses.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Birch

noncomputable section

/-- The weighted exponential sum divided by the scale to the number of variables. -/
def normalizedSum {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (P α : ℝ) : ℂ :=
  (P ^ (-(n : ℝ)) : ℝ) • exponentialSum F w P α

/-- The singular series, indexed by positive conductors. -/
def singularSeries {n : ℕ} (F : IntForm n) : ℂ :=
  ∑' q : ℕ, unitConductorSum F (q + 1)

/-- The real oscillatory integral at frequency `γ`. -/
def realOscillation {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) (γ : ℝ) : ℂ :=
  ∫ x, (w x : ℂ) * phase (γ * evalForm F x)

/-- The singular integral. -/
def singularIntegral {n : ℕ} (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : ℂ :=
  ∫ γ, realOscillation F w γ

/-- The exceptional-set estimate of Proposition prop:metric, with a uniform threshold
at each fixed degree and exponent, and a measure constant at each loss. -/
def MetricEstimate {n : ℕ} (d : ℕ) (F : IntForm n) (w : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (r : ℕ) (h : ℝ), 2 ≤ r → r < d → 0 < h → h ≤ 1/2 →
    ∃ C > 0, ∀ ε > 0, ∃ K > 0, ∀ᶠ P in atTop,
      circleMeasure {α | C * P ^ (-levelExponent d n r h) < ‖normalizedSum F w P α‖} ≤
        ENNReal.ofReal (K * P ^ (-(d : ℝ) + exceptionExponent d r h + ε))

/-- The major-arc evaluation with local-factor convergence and positivity. The default saving
is the unit saving in Section 5. -/
structure MajorArcEstimate {n : ℕ} (d : ℕ) (F : IntForm n)
    (w : (Fin n → ℝ) → ℝ) (saving : ℝ := 1) : Prop where
  series_converges : Summable (fun q : ℕ ↦ ‖unitConductorSum F (q + 1)‖)
  integral_converges : Integrable (realOscillation F w)
  positive_factor : 0 < (singularSeries F * singularIntegral F w).re
  asymptotic : ∃ C > 0, ∀ᶠ P in atTop,
    ‖(∫ α in majorArcs d P, normalizedSum F w P α ∂circleMeasure) -
      (P ^ (-(d : ℝ)) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
        C * P ^ (-(d : ℝ) - saving)

/-- A fixed initial power-saving bound on the minor arcs. -/
def InitialMinorEstimate {n : ℕ} (d : ℕ) (F : IntForm n)
    (w : (Fin n → ℝ) → ℝ) (σ : ℝ) : Prop :=
  ∃ C > 0, ∀ᶠ P in atTop, ∀ α ∈ (majorArcs d P)ᶜ,
    ‖normalizedSum F w P α‖ ≤ C * P ^ (-σ)

end
end Birch
