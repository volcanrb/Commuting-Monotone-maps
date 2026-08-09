import CommutingInterval.DynamicsDefs
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Scaled probabilities for interval maps

This module isolates the measure-theoretic predicate shared by the
Parry--Shultz construction and the finite-lap transfer operator.
-/

namespace CommutingInterval

open Function Set MeasureTheory

/-- A nonatomic full-support probability which scales injectivity sets of
`T` by `s`. -/
def IsScaledProbability (T : IntervalMap) (s : ℝ)
    (μ : Measure I) : Prop :=
  μ Set.univ = 1 ∧
    (∀ x : I, μ {x} = 0) ∧
    (∀ U : Set I, IsOpen U → U.Nonempty → μ U ≠ 0) ∧
    ∀ E : Set I, MeasurableSet E → Set.InjOn T E →
      μ (T '' E) = ENNReal.ofReal s * μ E

end CommutingInterval
