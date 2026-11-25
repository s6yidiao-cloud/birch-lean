import Birch

/-! Exact types, proof dependencies, and axioms for the results of the manuscript. -/

open Birch Filter MeasureTheory
open scoped Polynomial

#print FinalWeight
#print HasNonvanishingGradientOnSupport
#print RationalGradientDimension
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

example :
    ∀ (d n : ℕ) (F : IntForm n) (σ : ℕ), 2 ≤ d →
      F ≠ 0 → F.IsHomogeneous d → RationalGradientDimension F σ →
      2 ^ (d + 1) - 3 ≤ n - σ →
      (HasNonsingularZero F ℝ ∧ ∀ (p : ℕ) [Fact p.Prime], HasNonsingularZero F ℚ_[p]) →
      HasNonsingularZero F ℚ :=
  finalSmoothHassePrinciple

example :
    ∀ d n : ℕ, 2 ≤ d → ∃ η > 0, ∀ (F : IntForm n) (σ : ℕ) (w : (Fin n → ℝ) → ℝ),
      F ≠ 0 → F.IsHomogeneous d → RationalGradientDimension F σ → 2 ^ (d + 1) - 3 ≤ n - σ →
      FinalWeight w → HasNonvanishingGradientOnSupport F w →
      Summable (fun q : ℕ => formConductorMass F (q + 1)) ∧
      Integrable (realOscillation F w) ∧
      ∃ C > 0, ∀ᶠ B : ℝ in atTop,
        ‖(compactWeightedZeros F w B : ℂ) -
          (B ^ ((n : ℝ) - d) : ℝ) • (singularSeries F * singularIntegral F w)‖ ≤
          C * B ^ ((n : ℝ) - d - η) :=
  finalFormAsymptotic

example :
    ∀ (d e n : ℕ) (F : IntForm n) (g : ℤ[X]) (σ : ℕ),
      2 ≤ d → 2 ≤ e → F ≠ 0 → F.IsHomogeneous d → g.natDegree = e →
      RationalGradientDimension F σ →
      ((2 ^ (d + 1) - 4 : ℕ) : ℝ) * (1 / (d : ℝ) + 1 / (2 * (e : ℝ))) ≤ (n - σ : ℕ) →
      ∀ ε > 0, ∃ C > 0, ∀ᶠ B : ℝ in atTop,
        (coverIntegralCount F g B : ℝ) ≤ C * B ^ ((n : ℝ) - 1 + ε) :=
  finalCoverSerreBound

example :
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
  finalCoverAsymptotic

#print axioms finalSmoothHassePrinciple
#print axioms finalFormAsymptotic
#print axioms finalCoverSerreBound
#print axioms finalCoverAsymptotic
#print axioms nativeSmoothHypersurfaceSpectrum
#print axioms nativeUnconditionalFinalResults

open Lean Elab Command

#check (finalResults_of_higherDimensionalPrimeBounds :
  (∀ r, 3 ≤ r → ∀ l, 2 ≤ l → UniformTwistedPrimeBound r l) →
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧ FinalCoverAsymptotic)
#print axioms finalResults_of_higherDimensionalPrimeBounds
#print axioms norm_univariate_characterSum_le_of_stepanov
#print axioms uniformTwistedPrimeBound_one_of_stepanov
#print axioms norm_separatedPrimeCharacterSum_le_of_stepanov

#check (finalResults_of_formCriticalMoments :
  (∀ d, FormCriticalMomentBounds d) →
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧ FinalCoverAsymptotic)
#print axioms criticalMoment_of_scaledMetric
#print axioms finalResults_of_formCriticalMoments

#check (finalResults_of_terminalPrimeBoundsWithLoss :
  (∀ d (δ : ℝ), 0 < δ → TerminalPrimeBoundsWithLoss d δ) →
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧ FinalCoverAsymptotic)
#check (finalResults_of_regularAffineLevelCounts :
  (∀ r, 3 ≤ r → ∀ n, 3 ≤ n → EventualPrimeRegularAffineLevelCountsAtDimension r n) →
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧ FinalCoverAsymptotic)
#check (finalResults_of_smoothProjectiveSpectrum :
  (∀ r, 3 ≤ r → ∀ m, 4 ≤ m → EventualPrimeSmoothProjectiveSpectrumAtDimension r m) →
    FinalSmoothHassePrinciple ∧ FinalFormAsymptotic ∧ FinalCoverSerreBound ∧ FinalCoverAsymptotic)
#print axioms finalResults_of_terminalPrimeBoundsWithLoss
#print axioms finalResults_of_regularAffineLevelCounts
#print axioms finalResults_of_smoothProjectiveSpectrum

private def isLocalModule (name : Name) : Bool :=
  (`Birch).isPrefixOf name || (`GafniTao).isPrefixOf name ||
    (`StacksFrontier).isPrefixOf name

private partial def collectLocalDependencies (env : Environment) (localModules : Array Bool) (name : Name) :
    StateM NameSet Unit := do
  if (← get).contains name then return
  let some idx := env.getModuleIdxFor? name | return
  if !localModules[idx.toNat]! then return
  modify fun seen => seen.insert name
  if let some info := env.find? name then
    for dep in info.getUsedConstantsAsSet do
      collectLocalDependencies env localModules dep

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := env.header.moduleNames.map isLocalModule
  let routes := [
    (``finalSmoothHassePrinciple,
      [``fixedPartialFormAsymptotic_of_formCriticalMoments, ``singularSeries_positive_of_nonsingularZeros]),
    (``finalFormAsymptotic,
      [``formAsymptotic_of_gradientPartition, ``v2CubeFormAsymptotic_of_formCriticalMoments,
        ``formConductorMass_tail_of_minorArcs_atExponent]),
    (``finalCoverSerreBound,
      [``coverIntegralCount_serre_of_formCriticalMoments, ``coverYSum_fourthMoment]),
    (``finalCoverAsymptotic,
      [``v2CoverCubeAsymptoticAt_of_formCriticalMoments_of_coverMoment, ``coverMeanValueBound_of_degree_le_four,
        ``criticalVinogradovEstimate_of_wooley, ``GafniTao.wooleyPolynomialCorollary32_native,
        ``coverConductorMass_tail_of_coverNormalizedMinor])]
  for (target, required) in routes do
    let deps := ((collectLocalDependencies env localModules target).run {}).2
    for name in required ++ [``nativeUnconditionalFinalResults, ``nativeSmoothHypersurfaceSpectrum,
        ``nativeWeilSpectrumWithRanks, ``nonempty_equiv_projectiveHypersurfaceConstantCohomology_of_lt,
        ``finrank_projectiveHypersurfaceConstantCohomology_eq_fermat, ``v2CompletionEstimateWithPrimeLoss,
        ``v2MetricDistribution_of_completion, ``criticalMoment_of_scaledMetric,
        ``quadraticMetricDistribution_uniform] do
      unless deps.contains name do
        throwError "{target} is missing the expected dependency {name}"
    if deps.contains ``PrimeDeligneEstimate then
      throwError "{target} depends on the prime-field estimate hypothesis."
    logInfo m!"Verified proof route for {target}."
  let target := ``finalResults_of_higherDimensionalPrimeBounds
  let deps := ((collectLocalDependencies env localModules target).run {}).2
  for name in [``uniformTwistedPrimeBound_one_of_stepanov,
      ``MvPolynomial.exists_card_zeroSet_ge_of_absolutelyIrreducible] do
    unless deps.contains name do
      throwError "{target} is missing the expected dependency {name}"
  logInfo m!"Verified proof route for {target}."
  let target := ``finalResults_of_formCriticalMoments
  let deps := ((collectLocalDependencies env localModules target).run {}).2
  for name in [``v2CubeFormAsymptotic_of_formCriticalMoments,
      ``coverIntegralCount_serre_of_formCriticalMoments,
      ``v2CoverCubeAsymptoticAt_of_formCriticalMoments_of_coverMoment,
      ``coverMinorArcBound_of_criticalMoment_atExponent] do
    unless deps.contains name do
      throwError "{target} is missing the expected dependency {name}"
  logInfo m!"Verified proof route for {target}."
  let target := ``finalResults_of_smoothProjectiveSpectrum
  let deps := ((collectLocalDependencies env localModules target).run {}).2
  for name in [``finalResults_of_regularAffineLevelCounts, ``finalResults_of_terminalPrimeBoundsWithLoss,
      ``eventual_primeRegularAffineLevelCountsAtDimension_of_projectiveCounts,
      ``eventual_primeSmoothProjectiveCountAtDimension_three_of_stepanov,
      ``uniformTwistedPrimeBoundWithLoss_of_higher_dimwise_regularLevels,
      ``eventual_regularPlaneLevelCounts_of_stepanov, ``uniformTwistedPrimeBound_one_of_stepanov,
      ``terminal_chain_bound_of_good_frames_of_residue_bound_with_multiplier,
      ``CompletionEstimateWithPrimeLoss.scaled, ``criticalMoment_of_scaledMetric,
      ``finalResults_of_formCriticalMoments] do
    unless deps.contains name do
      throwError "{target} is missing the expected dependency {name}"
  if deps.contains ``PrimeDeligneEstimate then
    throwError "{target} still depends on the Deligne estimate."
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
    if !localModules[idx.toNat]! then return count
    for axiomName in ← collectAxioms name do
      unless axiomName ∈ allowed do
        throwError "{name} depends on unexpected axiom {axiomName}"
    return count + 1
  logInfo m!"Checked axiom dependencies for {count} local declarations."
