import CommutingInterval.DynamicsDefs

/-!
# Constant-slope finite-piece interval maps

This file isolates the small definition shared by the polygonal-model and
original-phase arguments.  Keeping it over `DynamicsDefs` prevents the
terminal original-phase calculation from importing the much broader
polygonal construction.
-/

namespace CommutingInterval

/-- A finite-piece PL map all of whose nonconstant branches have the same
absolute slope. -/
def HasConstantAbsoluteSlope (T : IntervalMap) (s : ℝ) : Prop :=
  Continuous T ∧
    ∃ p : RealPartition,
      ∀ ⦃a b : ℝ⦄, p.Adjacent a b →
        ∃ m c : ℝ, |m| = s ∧
          ∀ x ∈ intervalCell a b, (T x : ℝ) = m * (x : ℝ) + c

end CommutingInterval
