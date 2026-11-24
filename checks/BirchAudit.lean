import Birch

/-! Exact types, proof dependencies, and axioms for the results of the manuscript. -/

open Birch Filter MeasureTheory
open scoped Polynomial

#print FinalWeight
#print HasNonvanishingGradientOnSupport
#print RationalGradientDimension
#print PrimeDeligneEstimate
#print HasNonsingularZero
#print SmoothHassePrinciple
#print compactWeightedZeros
#print formConductorMass
#print coverIntegralPairs
#print coverWeightedZeros
#print coverConductorMass
#print coverSingularIntegral
#check quadraticPointwiseEstimate
#check quadraticMetricDistribution_uniform
#print axioms quadraticMetricDistribution_uniform

example (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) :
    ∀ (d n : ℕ) (F : IntForm n) (σ : ℕ), 2 ≤ d →
      F ≠ 0 → F.IsHomogeneous d → RationalGradientDimension F σ →
      2 ^ (d + 1) - 3 ≤ n - σ →
      (HasNonsingularZero F ℝ ∧ ∀ (p : ℕ) [Fact p.Prime], HasNonsingularZero F ℚ_[p]) →
      HasNonsingularZero F ℚ :=
  finalSmoothHassePrinciple hDeligne

example (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) :
    ∀ d n : ℕ, 2 ≤ d → ∃ η > 0, ∀ (F : IntForm n) (σ : ℕ) (w : (Fin n → ℝ) → ℝ),
      F ≠ 0 → F.IsHomogeneous d → RationalGradientDimension F σ → 2 ^ (d + 1) - 3 ≤ n - σ →
      FinalWeight w → HasNonvanishingGradientOnSupport F w →
      Summable (fun q : ℕ => formConductorMass F (q + 1)) ∧
      Integrable (realOscillation F w) ∧
      ∃ C > 0, ∀ᶠ B : ℝ in atTop,
        ‖(compactWeightedZeros F w B : ℂ) -
          (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
          C * B ^ ((n : ℝ) - d - η) :=
  finalFormAsymptotic hDeligne

example (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) :
    ∀ (d e n : ℕ) (F : IntForm n) (g : ℤ[X]) (σ : ℕ),
      2 ≤ d → 2 ≤ e → F ≠ 0 → F.IsHomogeneous d → g.natDegree = e →
      RationalGradientDimension F σ →
      ((2 ^ (d + 1) - 4 : ℕ) : ℝ) * (1 / (d : ℝ) + 1 / (2 * (e : ℝ))) ≤ (n - σ : ℕ) →
      ∀ ε > 0, ∃ C > 0, ∀ᶠ B : ℝ in atTop,
        (coverIntegralCount F g B : ℝ) ≤ C * B ^ ((n : ℝ) - 1 + ε) :=
  finalCoverSerreBound hDeligne

example (hDeligne : ∀ r, 3 ≤ r → PrimeDeligneEstimate r) :
    ∀ (d e n : ℕ) (F : IntForm n) (g : ℤ[X]) (σ : ℕ) (w : (Fin n → ℝ) → ℝ),
      2 ≤ d → 2 ≤ e → F ≠ 0 → F.IsHomogeneous d → g.natDegree = e →
      RationalGradientDimension F σ →
      ((2 ^ (d + 1) - 4 : ℕ) : ℝ) * (1 - 1 / ((min (2 ^ e) (e * (e + 1)) : ℕ) : ℝ)) <
        (n - σ : ℕ) →
      FinalWeight w → HasNonvanishingGradientOnSupport F w →
      Summable (fun q : ℕ => coverConductorMass F g (q + 1)) ∧
      Integrable (fun γ => realOscillation F w γ * coverRealOscillation g e γ) ∧
      ∃ η > 0, ∃ C > 0, ∀ᶠ B : ℝ in atTop,
        ‖(coverWeightedZeros d e F g w B : ℂ) -
          (B ^ ((n : ℝ) + (d : ℝ) / e - d) : ℝ) •
            (coverSingularSeries F g * coverSingularIntegral F g e w)‖ ≤
        C * B ^ ((n : ℝ) + (d : ℝ) / e - d - η) :=
  finalCoverAsymptotic hDeligne

#print axioms finalSmoothHassePrinciple
#print axioms finalFormAsymptotic
#print axioms finalCoverSerreBound
#print axioms finalCoverAsymptotic

open Lean Elab Command

private def isLocalModule (name : Name) : Bool :=
  (`Birch).isPrefixOf name || (`GafniTao).isPrefixOf name

private partial def collectLocalDependencies (env : Environment) (name : Name) :
    StateM NameSet Unit := do
  if (← get).contains name then return
  let some idx := env.getModuleIdxFor? name | return
  if !isLocalModule env.header.moduleNames[idx.toNat]! then return
  modify fun seen => seen.insert name
  if let some info := env.find? name then
    for dep in info.getUsedConstantsAsSet do
      collectLocalDependencies env dep

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let routes := [
    (``finalSmoothHassePrinciple,
      [``fixedPartialFormAsymptotic_of_deligne, ``singularSeries_positive_of_nonsingularZeros]),
    (``finalFormAsymptotic,
      [``formAsymptotic_of_gradientPartition, ``v2CubeFormAsymptotic_of_weilII,
        ``formConductorMass_tail_of_minorArcs_atExponent]),
    (``finalCoverSerreBound,
      [``coverIntegralCount_serre_of_weilII, ``coverYSum_fourthMoment]),
    (``finalCoverAsymptotic,
      [``v2CoverCubeAsymptoticAt_of_weilII_of_coverMoment, ``coverMeanValueBound_of_degree_le_four,
        ``criticalVinogradovEstimate_of_wooley, ``GafniTao.wooleyPolynomialCorollary32_native,
        ``coverConductorMass_tail_of_coverNormalizedMinor])]
  for (target, required) in routes do
    let deps := ((collectLocalDependencies env target).run {}).2
    for name in required ++ [``v2CompletionEstimate_of_weilII, ``v2MetricDistribution_of_completion,
        ``quadraticMetricDistribution_uniform] do
      unless deps.contains name do
        throwError "{target} is missing the expected dependency {name}"
    logInfo m!"Verified proof route for {target}."
  let superseded := [`Birch.v3MainTheorem_of_deligne, `Birch.hassePrinciple_four_mul_two_pow,
    `Birch.v2MainResults_of_deligne, `Birch.v2CoverAsymptotic_of_weilII,
    `Birch.v2FormAsymptotic_of_weilII, `Birch.v2CoverSerreBound_of_weilII,
    `Birch.coverRationalProjectionCount, `Birch.finalCoverIntegralProjectionBound_of_deligne]
  for name in superseded do
    if (env.find? name).isSome then
      throwError "The release imports superseded result {name}"
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let count ← env.constants.foldM (init := (0 : ℕ)) fun count name _ => do
    let some idx := env.getModuleIdxFor? name | return count
    if !isLocalModule env.header.moduleNames[idx.toNat]! then return count
    for axiomName in ← collectAxioms name do
      unless axiomName ∈ allowed do
        throwError "{name} depends on unexpected axiom {axiomName}"
    return count + 1
  logInfo m!"Checked axiom dependencies for {count} local declarations."
