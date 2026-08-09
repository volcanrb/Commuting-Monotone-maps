import CommutingInterval.OriginalPhase
import CommutingInterval.PiecewiseLinearB9Scratch

/-!
# Least-period return path and original phase

This module retains the least period of the decoded return path, identifies
its finite unit-speed predicate with the one used by `OriginalPhase`, applies
the affine-lift theorem, and pulls the resulting common fixed point back
through the common distribution coordinate.
-/

namespace CommutingInterval

open Function Set

noncomputable section

namespace PiecewiseLinearB10Scratch

open PiecewiseLinearB9Scratch

/-! ## Least-period return data -/

/-- Boundary 9 with its least-period information retained. -/
theorem markovSubstitutions_periodicReturnPathPackage
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E)
    (K : PiecewiseLinearCommonMarkovPackage M) :
    Nonempty (PeriodicReturnPathPackage M.A M.B
      (M.scaleP ^ G.L) (M.scaleQ ^ G.L)) := by
  obtain ⟨rayData, hseedData⟩ := exists_rebuiltRay_and_seed M K
  obtain ⟨seedData⟩ := hseedData
  obtain ⟨coding⟩ := exists_exactCommonRayCodingData K rayData seedData
  have hwordPeriodic := exactCoding_word_ultimatelyPeriodic coding
  have hcomm : Commute M.A M.B := by
    intro x
    simpa [PiecewiseLinearConstantSlopeSystem.A,
      PiecewiseLinearConstantSlopeSystem.B] using
      M.commute.iterate_iterate G.L G.L x
  have result := periodic_commonRay_produces_returnPathPackage
    coding.common hcomm (show M.R = M.A ∘ M.B from rfl) M.exact_R
      hwordPeriodic
  simpa [rayData.scaleA_eq, rayData.scaleB_eq] using result

/-- The Section 6 and original-phase finite unit-speed predicates differ
only in the name of their definitionally identical adjacency predicates. -/
theorem finiteUnitSpeedPiecesOn_iff_isFinitePieceUnitSpeedOn
    {ψ : ℝ → I} {a b : ℝ} :
    HasFiniteUnitSpeedPiecesOn ψ a b ↔ IsFinitePieceUnitSpeedOn ψ a b := by
  rfl

/-- A rich return-path package supplies exactly the least-period path and
the two dilation semiconjugacies consumed by `OriginalPhase`. -/
theorem periodicReturnPathPackage_originalPhase_specs
    {A B : IntervalMap} {a b : ℝ}
    (package : PeriodicReturnPathPackage A B a b) :
    IsUnitSpeedPeriodicSurjection package.path package.period ∧
      DilationSemiconjugates package.path a A ∧
      DilationSemiconjugates package.path b B := by
  rcases package.path_spec with ⟨hcont, honto, hleast, hpieces⟩
  rcases hleast with ⟨hperiodPos, hperiodic, hleast⟩
  refine ⟨⟨hcont, honto, hperiodPos, hperiodic, hleast, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    exact finiteUnitSpeedPiecesOn_iff_isFinitePieceUnitSpeedOn.mp
      (hpieces x y hxy)
  · exact package.returnA
  · exact package.returnB

/-- Apply the checked original-phase globalization theorem to the rich
least-period package.  Core's constant-slope predicate is definitionally
the predicate isolated in `ConstantSlopeDefs`. -/
theorem periodicReturnPathPackage_originalPhaseLifts
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E)
    (package : PeriodicReturnPathPackage M.A M.B
      (M.scaleP ^ G.L) (M.scaleQ ^ G.L)) :
    Nonempty (OriginalPhaseLiftPackage M.modelP M.modelQ) := by
  have hspecs := periodicReturnPathPackage_originalPhase_specs package
  have hSlopeP : HasConstantAbsoluteSlope M.modelP M.scaleP := by
    simpa [HasConstantAbsoluteSlope, HasConstantAbsoluteSlopePLCore] using
      M.slopeP
  have hSlopeQ : HasConstantAbsoluteSlope M.modelQ M.scaleQ := by
    simpa [HasConstantAbsoluteSlope, HasConstantAbsoluteSlopePLCore] using
      M.slopeQ
  exact original_phase_affine_lifts
    (L := G.L) (C := M.scaleP) (D := M.scaleQ)
    (a := M.scaleP ^ G.L) (b := M.scaleQ ^ G.L)
    (P₀ := package.period) (ψ := package.path)
    (piecewiseLinear_returnedLength_pos G) M.commute
    (show M.A = iterateMap M.modelP G.L from rfl)
    (show M.B = iterateMap M.modelQ G.L from rfl)
    M.one_lt_scaleP M.one_lt_scaleQ rfl rfl hSlopeP hSlopeQ
    hspecs.1 hspecs.2.1 hspecs.2.2

/-- The parity consumer turns the affine-lift package into a physical common
fixed point for the two constant-slope models. -/
theorem periodicReturnPathPackage_commonFixedPoint
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E)
    (package : PeriodicReturnPathPackage M.A M.B
      (M.scaleP ^ G.L) (M.scaleQ ^ G.L)) :
    HasCommonFixedPoint M.modelP M.modelQ := by
  obtain ⟨lifts⟩ := periodicReturnPathPackage_originalPhaseLifts M package
  exact common_fixed_point_of_original_phase_package lifts

/-- Corrected B9/B10 consumer: retain leastness through the original-phase
argument, then use the existing common coordinate to return to `G.P,G.Q`. -/
theorem markovSubstitutions_commonFixedPoint
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E)
    (K : PiecewiseLinearCommonMarkovPackage M) :
    HasCommonFixedPoint G.P G.Q := by
  obtain ⟨package⟩ := markovSubstitutions_periodicReturnPathPackage M K
  have hmodel := periodicReturnPathPackage_commonFixedPoint M package
  exact commonFixedPoint_of_conjugatesPLCore
    M.coordinate M.conjugatesP M.conjugatesQ hmodel

end PiecewiseLinearB10Scratch

end

end CommutingInterval
