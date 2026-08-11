import CommutingIntervalSimplified.DurandCommonDerived

/-!
# Primitive comparison for two exact-metric substitutions

This module is the acyclic bridge from the proved synchronized recurrent core
to the bounded return-system/Proposition-10 comparison.  During the staged
migration it adapts the synchronized core to the generic return-system records
still housed in `DurandMetric`; those records will move here unchanged once
their remaining proof leaves are closed.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

open Function Set

noncomputable section

universe u

/-- The honest common-metric replacement for the retired asserted M2 core
constructor. -/
theorem synchronizedReturnCoreData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord) :
    Nonempty (MetricCommonRecurrentCoreData Pleft Pright) := by
  obtain ⟨synchronized⟩ :=
    metricSynchronizedPrimitiveCoreData_exists Pleft Pright hsyndetic
  exact ⟨synchronized.toReturnCore⟩

/-- Aperiodic branch through the synchronized core and the generic bounded
return-system comparison. -/
theorem aperiodicSynchronizedMetricReturnComparison_has_powerEquality
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord)
    (hnotPeriodic : ¬ HasPeriodicRecurrentLanguage sourceWord) :
    ∃ leftPower rightPower : ℕ, 0 < leftPower ∧ 0 < rightPower ∧
      leftScale ^ leftPower = rightScale ^ rightPower := by
  obtain ⟨synchronized⟩ :=
    metricSynchronizedPrimitiveCoreData_exists Pleft Pright hsyndetic
  let core := synchronized.toReturnCore
  obtain ⟨linear⟩ :=
    metricSynchronizedCore_has_aperiodicLinearRecurrence
      synchronized hnotPeriodic
  obtain ⟨markers⟩ := cofinalMetricMarkerTower_exists core.coreWord
  obtain ⟨decompositions⟩ :=
    metricReturnDecompositionTower_exists linear markers
  obtain ⟨tower⟩ := boundedLocalReturnTower_exists core markers decompositions
  obtain ⟨bounds⟩ :=
    boundedLocalReturnTower_has_uniformBounds linear tower
  obtain ⟨coding⟩ :=
    boundedLocalReturnTowerBounds_have_finiteCoding bounds
  obtain ⟨repetition⟩ :=
    boundedLocalReturnTowerFiniteCoding_has_repetition coding
  obtain ⟨system⟩ :=
    DurandCommonDerived.repeatedBoundedLocalSystems_have_commonDerivedSystem
      synchronized repetition hnotPeriodic
  obtain ⟨equations⟩ :=
    metricDurandCommonSystem_has_twoPowerEquationFamilies system
  obtain ⟨comparison⟩ :=
    metricDurandMetricComparison_exists equations
  exact metricDurandMetricComparison_forces_basePowerEquality comparison

/-- Synchronized common-metric comparison: periodic recurrent language or
equal positive powers of the two exact scales. -/
theorem synchronizedMetricReturnComparison_periodic_or_dependent
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord) :
    HasPeriodicRecurrentLanguage sourceWord ∨
      ∃ leftPower rightPower : ℕ, 0 < leftPower ∧ 0 < rightPower ∧
        leftScale ^ leftPower = rightScale ^ rightPower := by
  by_cases hperiodic : HasPeriodicRecurrentLanguage sourceWord
  · exact Or.inl hperiodic
  · exact Or.inr
      (aperiodicSynchronizedMetricReturnComparison_has_powerEquality
        Pleft Pright hsyndetic hperiodic)

/-- Public exact-common-metric theorem routed through the proved synchronized
core.  This will replace the legacy in-file wrapper after the remaining
generic return/P10 leaves move into this module. -/
theorem metricTheorem9_synchronized
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength)
    (hindependent : MultiplicativelyIndependent leftScale rightScale) :
    IsUltimatelyPeriodic sourceWord := by
  have hsyndetic := recurrentFactorsSyndetic_of_independentMetricGrowth
    Pleft Pright hindependent
  rcases synchronizedMetricReturnComparison_periodic_or_dependent
      Pleft Pright hsyndetic with hperiodic | hdependent
  · exact periodicRecurrentLanguage_ultimatelyPeriodic hsyndetic hperiodic
  · obtain ⟨leftPower, rightPower, hleft, hright, heq⟩ := hdependent
    exact False.elim
      (hindependent leftPower rightPower hleft hright heq)

end
end Symbolic
end CommutingIntervalSimplified
