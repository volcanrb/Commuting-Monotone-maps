import Mathlib.Topology.UnitInterval

/-!
# Interval maps and finite real partitions

This file contains the basic objects used to study self-maps of the closed
unit interval: fixed points, commuting pairs, and finite partitions into
closed cells.
-/

namespace CommutingInterval

open Set

/-! ## The closed unit interval and its self-maps -/

/-- The closed unit interval, regarded as a subtype of `ℝ` when used as a type. -/
abbrev I : Set ℝ := Set.Icc (0 : ℝ) 1

/-- A self-map of the closed unit interval. -/
abbrev IntervalMap := I → I

/-- The proposition that `x` is fixed by the interval self-map `T`. -/
def IsFixedPoint (T : IntervalMap) (x : I) : Prop :=
  T x = x

/-- The set of fixed points of an interval self-map. -/
def fixedPoints (T : IntervalMap) : Set I :=
  {x | IsFixedPoint T x}

/-- The proposition that `x` is fixed by both `P` and `Q`. -/
def IsCommonFixedPoint (P Q : IntervalMap) (x : I) : Prop :=
  IsFixedPoint P x ∧ IsFixedPoint Q x

/-- The set of common fixed points of two interval self-maps. -/
def commonFixedPoints (P Q : IntervalMap) : Set I :=
  {x | IsCommonFixedPoint P Q x}

/-- Two interval self-maps commute when their two composites agree pointwise. -/
def Commute (P Q : IntervalMap) : Prop :=
  Function.Commute P Q

/-- The proposition that two interval self-maps have a common fixed point. -/
def HasCommonFixedPoint (P Q : IntervalMap) : Prop :=
  (commonFixedPoints P Q).Nonempty

/-! ## Finite partitions of the unit interval -/

/--
A finite real partition of `[0,1]` is represented by its finite set of
vertices.  Requiring both endpoints and requiring every vertex to lie in
`[0,1]` makes this representation canonical up to equality of `Finset`s.
-/
structure RealPartition where
  /-- The finite set of partition vertices. -/
  points : Finset ℝ
  /-- The left endpoint is a partition vertex. -/
  zero_mem : (0 : ℝ) ∈ points
  /-- The right endpoint is a partition vertex. -/
  one_mem : (1 : ℝ) ∈ points
  /-- Every partition vertex belongs to the unit interval. -/
  points_subset : (points : Set ℝ) ⊆ I

namespace RealPartition

/--
`p.Adjacent a b` means that `a < b` are consecutive vertices of `p`.
Adjacency is directed from left to right, matching the closed cell `[a,b]`.
-/
def Adjacent (p : RealPartition) (a b : ℝ) : Prop :=
  a ∈ p.points ∧ b ∈ p.points ∧ a < b ∧
    ∀ c ∈ p.points, ¬(a < c ∧ c < b)

/-- The closed interval determined by a directed adjacent pair. -/
def cell (_p : RealPartition) (a b : ℝ) : Set ℝ :=
  Set.Icc a b

end RealPartition

end CommutingInterval
