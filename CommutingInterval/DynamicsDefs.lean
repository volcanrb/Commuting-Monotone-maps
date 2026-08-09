import CommutingInterval.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Dynamical definitions for commuting interval maps

This file introduces the dynamical vocabulary used in the manuscript without
postulating any dynamical theorem.  All intervals below are intervals in the
subtype `I = Set.Icc (0 : ℝ) 1`; consequently their endpoints automatically
belong to `[0,1]`.

There are two deliberate conventions.

* A `ClosedSubinterval` may be a singleton.  Nondegeneracy is always recorded
  separately by `ClosedSubinterval.Nondegenerate`.
* A one-sided germ includes its base point and contains a genuinely
  nondegenerate interval on the indicated side.  Thus a right germ at `1`, or
  a left germ at `0`, cannot be witnessed accidentally by a singleton.
-/

namespace CommutingInterval

open Set Function

/-! ## Endpoints, iterates, and closed subintervals -/

/-- The left endpoint of the unit interval, as an element of `I`. -/
def leftEndpoint : I :=
  ⟨0, le_rfl, zero_le_one⟩

/-- The right endpoint of the unit interval, as an element of `I`. -/
def rightEndpoint : I :=
  ⟨1, zero_le_one, le_rfl⟩

/-- The `n`-fold iterate of an interval self-map. -/
def iterateMap (T : IntervalMap) (n : ℕ) : IntervalMap :=
  T^[n]

/--
A closed subinterval of `I`, specified by ordered endpoints.  The carrier is
always nonempty; it is a singleton exactly when the endpoints agree.
-/
structure ClosedSubinterval where
  /-- The left endpoint. -/
  left : I
  /-- The right endpoint. -/
  right : I
  /-- The endpoints occur in their displayed order. -/
  left_le_right : left ≤ right

namespace ClosedSubinterval

/-- The set of points between the two endpoints, including both endpoints. -/
def carrier (J : ClosedSubinterval) : Set I :=
  Set.Icc J.left J.right

/-- A closed subinterval is nondegenerate when its endpoints are distinct. -/
def Nondegenerate (J : ClosedSubinterval) : Prop :=
  J.left < J.right

/-- The real length of a closed subinterval. -/
def length (J : ClosedSubinterval) : ℝ :=
  (J.right : ℝ) - (J.left : ℝ)

end ClosedSubinterval

/-- `J` is forward invariant under `T` when `T(J) ⊆ J`. -/
def IsForwardInvariant (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  Set.MapsTo T J.carrier J.carrier

/-- A closed subinterval forward invariant under both maps. -/
def IsCommonInvariantCore (P Q : IntervalMap) (J : ClosedSubinterval) : Prop :=
  IsForwardInvariant P J ∧ IsForwardInvariant Q J

/--
An inclusion-minimal common invariant core.  This is minimal, not necessarily
least: only common invariant subintervals already contained in `J` are
compared with `J`.  A singleton core is allowed and is precisely a common
fixed point.
-/
def IsMinimalCommonInvariantCore (P Q : IntervalMap)
    (J : ClosedSubinterval) : Prop :=
  IsCommonInvariantCore P Q J ∧
    ∀ K : ClosedSubinterval,
      IsCommonInvariantCore P Q K →
        K.carrier ⊆ J.carrier → J.carrier ⊆ K.carrier

/-- Surjectivity onto the whole closed unit interval. -/
def IsOnto (T : IntervalMap) : Prop :=
  Function.Surjective T

/-! ## Flat intervals and strict laps -/

/-- `T` is constant on the nondegenerate closed interval `J`. -/
def IsFlatInterval (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  J.Nondegenerate ∧
    ∀ ⦃x⦄, x ∈ J.carrier → ∀ ⦃y⦄, y ∈ J.carrier → T x = T y

/-- `T` has a flat interval somewhere in its domain. -/
def HasFlatInterval (T : IntervalMap) : Prop :=
  ∃ J : ClosedSubinterval, IsFlatInterval T J

/-- The portion of an ambient real interval lying in the subtype `I`. -/
def intervalCell (a b : ℝ) : Set I :=
  {x : I | (x : ℝ) ∈ Set.Icc a b}

/-- `T` is strictly increasing or strictly decreasing on `s`. -/
def IsStrictlyMonotoneOn (T : IntervalMap) (s : Set I) : Prop :=
  StrictMonoOn T s ∨ StrictAntiOn T s

/--
The map admits finitely many strict monotonicity laps.  Every adjacent closed
cell is required to be genuinely strictly increasing or decreasing; constant
cells are therefore excluded.
-/
def HasFiniteStrictMonotonicityLaps (T : IntervalMap) : Prop :=
  ∃ p : RealPartition,
    ∀ ⦃a b : ℝ⦄, p.Adjacent a b →
      IsStrictlyMonotoneOn T (intervalCell a b)

/-! ## Finite-piece polygonal maps and intrinsic vertices -/

/-- The real-valued graph of `T` is affine on `s`. -/
def IsAffineOn (T : IntervalMap) (s : Set I) : Prop :=
  ∃ m c : ℝ,
    ∀ x ∈ s, (T x : ℝ) = m * (x : ℝ) + c

/--
A continuous finite-piece piecewise-affine self-map of `[0,1]`.  Slopes may
vanish, so this definition includes constant branches.  Adjacent affine
formulas need not have matching derivatives at a partition vertex.
-/
def FinitePiecePL (T : IntervalMap) : Prop :=
  Continuous T ∧
    ∃ p : RealPartition,
      ∀ ⦃a b : ℝ⦄, p.Adjacent a b →
        IsAffineOn T (intervalCell a b)

/--
An intrinsic genuine turn: on some nondegenerate interval on each side of
`x`, the map is strict in opposite monotonicity directions.  In particular,
same-direction affine kinks and the two ambient endpoints are not turns.
-/
def IsGenuineTurn (T : IntervalMap) (x : I) : Prop :=
  ∃ a b : I, a < x ∧ x < b ∧
    ((StrictMonoOn T (Set.Icc a x) ∧
        StrictAntiOn T (Set.Icc x b)) ∨
      (StrictAntiOn T (Set.Icc a x) ∧
        StrictMonoOn T (Set.Icc x b)))

/-- The intrinsic set of genuine turns of `T`. -/
def genuineTurns (T : IntervalMap) : Set I :=
  {x | IsGenuineTurn T x}

/-- The domain endpoints and the genuine turns of `T`. -/
def vertexDomain (T : IntervalMap) : Set I :=
  {leftEndpoint, rightEndpoint} ∪ genuineTurns T

/--
The manuscript's vertex-value set `𝒱(T) = T(E(T))`, where `E(T)` consists of
the two domain endpoints and all genuine turns.
-/
def vertexValues (T : IntervalMap) : Set I :=
  T '' vertexDomain T

/-! ## Exactness and essential injectivity -/

/--
Topological exactness in the relative topology of the subtype `I`: every
nonempty relatively open set maps onto all of `I` under some iterate.  The
iterate exponent is allowed to be zero, as in the manuscript.
-/
def IsTopologicallyExact (T : IntervalMap) : Prop :=
  ∀ U : Set I, IsOpen U → U.Nonempty →
    ∃ n : ℕ, (iterateMap T n) '' U = Set.univ

/--
Shultz's essential injectivity condition: no two disjoint nondegenerate
closed intervals have the same image.  Requiring actual disjointness (rather
than merely disjoint interiors) follows the formulation quoted in the
manuscript.
-/
def IsEssentiallyInjective (T : IntervalMap) : Prop :=
  ∀ J K : ClosedSubinterval,
    J.Nondegenerate → K.Nondegenerate →
      Disjoint J.carrier K.carrier → T '' J.carrier ≠ T '' K.carrier

/-! ## Directed sides and one-sided germs -/

/-- A choice of the left or right side of a base point. -/
inductive Side where
  | left
  | right
  deriving DecidableEq

namespace Side

/-- The closed ray in `I` on the indicated side of `x`, including `x`. -/
def closedRay (side : Side) (x : I) : Set I :=
  match side with
  | left => Set.Iic x
  | right => Set.Ici x

/-- The punctured ray in `I` on the indicated side of `x`. -/
def puncturedRay (side : Side) (x : I) : Set I :=
  match side with
  | left => Set.Iio x
  | right => Set.Ioi x

/-- The indicated side contains points other than its base. -/
def Available (side : Side) (x : I) : Prop :=
  (puncturedRay side x).Nonempty

end Side

/-- A base point together with a genuinely available directed side. -/
structure DirectedSide where
  /-- The base of the directed side. -/
  base : I
  /-- Whether the side points left or right. -/
  direction : Side
  /-- There is at least one domain point strictly on that side. -/
  available : direction.Available base

/-- The canonical right-directed side at a point strictly below `1`. -/
def rightDirectedSide (x : I) (hx : x < rightEndpoint) : DirectedSide where
  base := x
  direction := .right
  available := ⟨rightEndpoint, hx⟩

/-- The canonical left-directed side at a point strictly above `0`. -/
def leftDirectedSide (x : I) (hx : leftEndpoint < x) : DirectedSide where
  base := x
  direction := .left
  available := ⟨leftEndpoint, hx⟩

/--
Two interval maps have the same germ on the indicated side of `x` when they
agree on some nondegenerate closed one-sided interval based at `x`.
-/
def SameOneSidedGermAt (side : Side) (x : I)
    (F G : IntervalMap) : Prop :=
  match side with
  | .left =>
      ∃ a : I, a < x ∧ Set.EqOn F G (Set.Icc a x)
  | .right =>
      ∃ b : I, x < b ∧ Set.EqOn F G (Set.Icc x b)

/-- Equality of germs on a packaged directed side. -/
def SameGermOnDirectedSide (σ : DirectedSide)
    (F G : IntervalMap) : Prop :=
  SameOneSidedGermAt σ.direction σ.base F G

/-! ## Right-hand `C¹` and `C^{1+BV}` local diffeomorphism germs -/

/--
Data exhibiting an orientation-preserving right-hand `C¹` local
diffeomorphism germ of `T` at `x`.

The interval endpoint `rightEnd` is strictly to the right of `x`, so the germ
is never vacuous.  `extension` is defined on all of `ℝ` only to fit mathlib's
calculus API; all its mathematical data are restricted to the open set
`neighborhood`.  Positivity of the derivative is the one-dimensional,
orientation-preserving local-diffeomorphism condition.
-/
structure RightGermC1Diffeomorphism (T : IntervalMap) (x : I) where
  /-- A nontrivial right endpoint for the representative. -/
  rightEnd : I
  /-- The representative interval is nondegenerate. -/
  base_lt_rightEnd : x < rightEnd
  /-- An ambient real representative of the interval-map germ. -/
  extension : ℝ → ℝ
  /-- An open ambient neighborhood on which the representative is `C¹`. -/
  neighborhood : Set ℝ
  /-- Openness of the ambient neighborhood. -/
  isOpen_neighborhood : IsOpen neighborhood
  /-- The entire closed representative interval lies in the neighborhood. -/
  segment_subset : Set.Icc (x : ℝ) (rightEnd : ℝ) ⊆ neighborhood
  /-- The representative agrees with `T` on the closed right interval. -/
  agrees :
    Set.EqOn (fun y : I => (T y : ℝ)) (fun y : I => extension y)
      (Set.Icc x rightEnd)
  /-- The ambient representative is continuously differentiable. -/
  contDiff_one : ContDiffOn ℝ 1 extension neighborhood
  /-- Its derivative is positive throughout the closed right interval. -/
  deriv_pos :
    ∀ y ∈ Set.Icc (x : ℝ) (rightEnd : ℝ), 0 < deriv extension y

/-- `T` has an orientation-preserving right-hand `C¹` local diffeomorphism germ at `x`. -/
def HasRightGermC1Diffeomorphism (T : IntervalMap) (x : I) : Prop :=
  Nonempty (RightGermC1Diffeomorphism T x)

namespace RightGermC1Diffeomorphism

/-- The logarithm of the positive derivative of a right-germ representative. -/
noncomputable def logDeriv {T : IntervalMap} {x : I}
    (g : RightGermC1Diffeomorphism T x) : ℝ → ℝ :=
  fun y => Real.log (deriv g.extension y)

/--
The manuscript's `C^{1+BV}` condition on a chosen right-germ
representative: the logarithm of its derivative has bounded variation on the
closed one-sided representative interval.
-/
def HasBoundedVariationLogDeriv {T : IntervalMap} {x : I}
    (g : RightGermC1Diffeomorphism T x) : Prop :=
  BoundedVariationOn g.logDeriv (Set.Icc (x : ℝ) (g.rightEnd : ℝ))

end RightGermC1Diffeomorphism

/--
`T` has a right-hand orientation-preserving `C^{1+BV}` local diffeomorphism
germ at `x` when it has a `C¹` representative whose log derivative has
bounded variation on some nondegenerate closed right interval.
-/
def HasRightGermC1BV (T : IntervalMap) (x : I) : Prop :=
  ∃ g : RightGermC1Diffeomorphism T x, g.HasBoundedVariationLogDeriv

/-! ## Multiplicative independence -/

/--
Two real scaling factors are multiplicatively independent when no positive
natural powers agree.  The manuscript applies this only under the separate
hypotheses `1 < a` and `1 < b`.
-/
def MultiplicativelyIndependent (a b : ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n

end CommutingInterval
