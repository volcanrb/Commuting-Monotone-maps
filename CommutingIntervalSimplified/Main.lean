import CommutingIntervalSimplified.Reduction
import CommutingIntervalSimplified.Extremal
import CommutingIntervalSimplified.Fold
import CommutingIntervalSimplified.Coding
import CommutingIntervalSimplified.PeriodicFold

/-!
# Common fixed points for commuting finite-piece monotone interval maps

This is the final standalone assembly module.  Its theorem follows the
dependency chain frozen in the simplified manuscript:

1. reduce a hypothetical counterexample to a normalized expanding
   constant-slope factor;
2. choose the extremal returned-power factor;
3. construct the orientation-normalized two-scale fold;
4. obtain eventual periodicity from its common Markov coding; and
5. apply periodic-fold rigidity to recover a common fixed point.

No declaration from the earlier `CommutingInterval` library is referenced.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set

/-! ## Common fixed points and midpoint reflection -/

/-- Simultaneous midpoint reflection preserves existence of a common fixed
point. -/
theorem hasCommonFixedPoint_reflected_iff (P Q : IntervalMap) :
    HasCommonFixedPoint (reflectedIntervalMap P) (reflectedIntervalMap Q) ↔
      HasCommonFixedPoint P Q := by
  constructor
  · rintro ⟨x, hxP, hxQ⟩
    refine ⟨reflectPoint x, ?_, ?_⟩
    · have h := congrArg reflectPoint hxP
      simpa [reflectedIntervalMap, Function.comp_apply] using h
    · have h := congrArg reflectPoint hxQ
      simpa [reflectedIntervalMap, Function.comp_apply] using h
  · rintro ⟨x, hxP, hxQ⟩
    refine ⟨reflectPoint x, ?_, ?_⟩
    · simpa [IsFixedPoint, reflectedIntervalMap, Function.comp_apply] using
        congrArg reflectPoint hxP
    · simpa [IsFixedPoint, reflectedIntervalMap, Function.comp_apply] using
        congrArg reflectPoint hxQ

/-- Transfer a common fixed point from an orientation-normalized system
back to the system before the optional simultaneous reflection. -/
theorem hasCommonFixedPoint_of_orientationVariant
    {C C' : NormalizedConstantSlopeCounterexample}
    (hvariant : IsOrientationVariant C C')
    (hfixed : HasCommonFixedPoint C'.P C'.Q) :
    HasCommonFixedPoint C.P C.Q := by
  rcases hvariant with hsame | hreflected
  · simpa [hsame] using hfixed
  · rcases hreflected with ⟨hP, hQ, _hscaleP, _hscaleQ⟩
    rw [hP, hQ] at hfixed
    exact (hasCommonFixedPoint_reflected_iff C.P C.Q).mp hfixed

/-! ## Final contradiction assembly -/

/-- Two commuting continuous interval maps which are weakly monotone on
finitely many closed cells have a common fixed point. -/
theorem finitePieceMonotone_common_fixed_point_simplified
    (P Q : IntervalMap)
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Function.Commute P Q) :
    HasCommonFixedPoint P Q := by
  by_contra hno
  let source : PiecewiseMonotoneCounterexample :=
    { P := P
      Q := Q
      finitePiece_P := hP
      finitePiece_Q := hQ
      commute := hcomm
      no_common_fixed_point := hno }
  obtain ⟨linearized⟩ := common_constantSlope_factor_exists source
  obtain ⟨C, _extremalFactor, bound, L,
      _hboundDefinition, hL, hfixedBound, hirreducible⟩ :=
    exists_extremal_normalized_counterexample linearized.target
  have hLpos : 0 < L := by
    rw [hL]
    exact Nat.factorial_pos _
  obtain ⟨C', hvariant, hirreducible', hfold⟩ :=
    twoScaleFoldData_exists_of_extremal
      C bound L hL hfixedBound hirreducible
  obtain ⟨fold⟩ := hfold
  have heventual : EventuallyPeriodicOnRay fold.ray :=
    twoScaleFold_eventuallyPeriodic fold
  have hfixedC' : HasCommonFixedPoint C'.P C'.Q :=
    common_fixed_point_of_eventually_periodic_twoScaleFold
      hLpos C'.commute rfl rfl
      C'.one_lt_scale_P C'.one_lt_scale_Q rfl rfl
      C'.constantSlope_P C'.constantSlope_Q
      hirreducible' fold heventual
  have hfixedC : HasCommonFixedPoint C.P C.Q :=
    hasCommonFixedPoint_of_orientationVariant hvariant hfixedC'
  exact C.no_common_fixed_point hfixedC

end CommutingIntervalSimplified
