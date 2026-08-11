import CommutingIntervalSimplified.Base
import CommutingIntervalSimplified.PiecewiseMonotoneBase
import CommutingIntervalSimplified.FactorBase
import CommutingIntervalSimplified.PolygonalBase

/-!
# Definitions for the simplified common-fixed-point proof

This module contains only the stable interfaces shared by the simplified
proof.  All underlying interval-map, piecewise-monotone, piecewise-linear,
constant-slope, intrinsic-turn, quotient, and unit-speed notions come from
the standalone local foundation.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set

/-! ## Minimal expanding constant-slope counterexamples -/

/--
An affinely normalized counterexample in the expanding constant-slope class.

The minimality field says that the only nonempty closed interval which is
forward invariant under both generators is the whole unit interval.  This is
the exact invariant-core condition used by the factor and irreducibility
arguments.
-/
structure NormalizedConstantSlopeCounterexample where
  P : IntervalMap
  Q : IntervalMap
  finitePiece_P : FinitePiecePL P
  finitePiece_Q : FinitePiecePL Q
  onto_P : IsOnto P
  onto_Q : IsOnto Q
  commute : Function.Commute P Q
  no_common_fixed_point : ¬HasCommonFixedPoint P Q
  core_minimal : ∀ J : ClosedSubinterval,
    IsCommonInvariantCore P Q J → J.carrier = Set.univ
  scale_P : ℝ
  scale_Q : ℝ
  one_lt_scale_P : 1 < scale_P
  one_lt_scale_Q : 1 < scale_Q
  constantSlope_P : HasConstantAbsoluteSlope P scale_P
  constantSlope_Q : HasConstantAbsoluteSlope Q scale_Q

namespace NormalizedConstantSlopeCounterexample

/-- The commuting product whose finite fixed set determines the return power. -/
def product (C : NormalizedConstantSlopeCounterexample) : IntervalMap :=
  C.P ∘ C.Q

end NormalizedConstantSlopeCounterexample

/-! ## Returned-power irreducibility -/

/-- A map carries a closed subinterval onto itself, not merely into itself. -/
def MapsOntoSubinterval (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  T '' J.carrier = J.carrier

/--
The extremal irreducibility property for the common return power `L`.
Every nondegenerate closed interval carried onto itself by both returned maps
is the whole unit interval.
-/
def ReturnedPowersIrreducible
    (P Q : IntervalMap) (L : ℕ) : Prop :=
  ∀ J : ClosedSubinterval,
    J.Nondegenerate →
      MapsOntoSubinterval (iterateMap P L) J →
      MapsOntoSubinterval (iterateMap Q L) J →
      J.carrier = Set.univ

/-! ## Genuine turns and joint postcritical sets -/

/-- The manuscript's set `E(T)` of endpoints and intrinsic genuine turns. -/
abbrev criticalDomain (T : IntervalMap) : Set I := vertexDomain T

/-- The manuscript's vertex-value set `ᵋ(T)=T(E(T))`. -/
abbrev criticalValues (T : IntervalMap) : Set I := vertexValues T

/--
The joint forward orbit of the endpoint-and-turn sets under two commuting
maps.  Commutation is deliberately not part of the definition; it is a
hypothesis of the finiteness theorem.
-/
def jointPostcriticalSet (A B : IntervalMap) : Set I :=
  ⋃ m : ℕ, ⋃ n : ℕ,
    positiveWordMap A B m n '' (criticalDomain A ∪ criticalDomain B)

/-! ## Nonnegative two-scale folds -/

/-- Eventual periodicity on the physical nonnegative parameter ray. -/
def EventuallyPeriodicOnRay (ψ : ℝ → I) : Prop :=
  ∃ start period : ℝ,
    0 ≤ start ∧ 0 < period ∧
      ∀ t : ℝ, start ≤ t → ψ (t + period) = ψ t

/--
The geometric data produced from a repelling germ before symbolic
periodicity is proved.  The path is represented on all of `ℝ`, but every
substantive field is restricted to the physical ray `t ≥ 0`; this avoids a
new parameter subtype and interfaces directly with the existing polygonal
path API.
-/
structure TwoScaleFoldData
    (A B : IntervalMap) (a b : ℝ) where
  commute : Function.Commute A B
  finitePiece_A : FinitePiecePL A
  finitePiece_B : FinitePiecePL B
  onto_A : IsOnto A
  onto_B : IsOnto B
  constantSlope_A : HasConstantAbsoluteSlope A a
  constantSlope_B : HasConstantAbsoluteSlope B b
  one_lt_a : 1 < a
  one_lt_b : 1 < b
  scales_independent : MultiplicativelyIndependent a b
  base : I
  ray : ℝ → I
  continuousOn_ray : ContinuousOn ray (Set.Ici 0)
  initial_radius : ℝ
  initial_radius_pos : 0 < initial_radius
  initial_unit_germ : ∀ t ∈ Set.Icc (0 : ℝ) initial_radius,
    (ray t : ℝ) = (base : ℝ) + t
  locally_unit_speed : ∀ u v : ℝ,
    0 ≤ u → u < v → IsFinitePieceUnitSpeedOn ray u v
  return_A : ∀ t : ℝ, 0 ≤ t → ray (a * t) = A (ray t)
  return_B : ∀ t : ℝ, 0 ≤ t → ray (b * t) = B (ray t)
  dense_nonnegative_range : Dense (ray '' Set.Ici (0 : ℝ))

namespace TwoScaleFoldData

/-- The product scale attached to a two-scale fold. -/
def productScale
    {A B : IntervalMap} {a b : ℝ} (_F : TwoScaleFoldData A B a b) : ℝ :=
  a * b

/-- The commuting product map attached to a two-scale fold. -/
def productMap
    {A B : IntervalMap} {a b : ℝ} (_F : TwoScaleFoldData A B a b) :
    IntervalMap :=
  A ∘ B

end TwoScaleFoldData

end CommutingIntervalSimplified
