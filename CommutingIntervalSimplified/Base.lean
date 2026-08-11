import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UnitInterval

/-!
# Standalone foundations for commuting interval maps

This module is the Mathlib-only foundation of the simplified development.
It defines interval maps, finite real partitions, elementary invariant
intervals, finite-piece polygonal maps, intrinsic turns, one-sided germs,
and constant absolute slope.  No declaration from the earlier formalization
is imported or referenced.
-/

namespace CommutingIntervalSimplified

open Function Set

/-! ## The unit interval and fixed points -/

/-- The closed unit interval, used as a subtype of `ℝ`. -/
abbrev I : Set ℝ := Set.Icc (0 : ℝ) 1

/-- A self-map of the closed unit interval. -/
abbrev IntervalMap := I → I

/-- The point `x` is fixed by `T`. -/
def IsFixedPoint (T : IntervalMap) (x : I) : Prop :=
  T x = x

/-- The fixed-point set of `T`. -/
def fixedPoints (T : IntervalMap) : Set I :=
  {x | IsFixedPoint T x}

/-- The point `x` is fixed by both `P` and `Q`. -/
def IsCommonFixedPoint (P Q : IntervalMap) (x : I) : Prop :=
  IsFixedPoint P x ∧ IsFixedPoint Q x

/-- The common fixed-point set of `P` and `Q`. -/
def commonFixedPoints (P Q : IntervalMap) : Set I :=
  {x | IsCommonFixedPoint P Q x}

/-- The maps `P` and `Q` have a common fixed point. -/
def HasCommonFixedPoint (P Q : IntervalMap) : Prop :=
  (commonFixedPoints P Q).Nonempty

/-! ## Finite real partitions -/

/-- A finite partition of `[0,1]`, represented by its vertex set. -/
structure RealPartition where
  points : Finset ℝ
  zero_mem : (0 : ℝ) ∈ points
  one_mem : (1 : ℝ) ∈ points
  points_subset : (points : Set ℝ) ⊆ I

namespace RealPartition

/-- Directed adjacency of two consecutive partition vertices. -/
def Adjacent (p : RealPartition) (a b : ℝ) : Prop :=
  a ∈ p.points ∧ b ∈ p.points ∧ a < b ∧
    ∀ c ∈ p.points, ¬(a < c ∧ c < b)

/-- The ambient real closed cell determined by two vertices. -/
def cell (_p : RealPartition) (a b : ℝ) : Set ℝ :=
  Set.Icc a b

end RealPartition

/-! ## Endpoints, iterates, and closed subintervals -/

/-- The left endpoint of `I`. -/
def leftEndpoint : I :=
  ⟨0, le_rfl, zero_le_one⟩

/-- The right endpoint of `I`. -/
def rightEndpoint : I :=
  ⟨1, zero_le_one, le_rfl⟩

@[simp] theorem leftEndpoint_val : (leftEndpoint : ℝ) = 0 := rfl

@[simp] theorem rightEndpoint_val : (rightEndpoint : ℝ) = 1 := rfl

/-- The `n`-fold iterate of an interval map. -/
def iterateMap (T : IntervalMap) (n : ℕ) : IntervalMap :=
  T^[n]

/-- A closed subinterval of `I`, possibly a singleton. -/
structure ClosedSubinterval where
  left : I
  right : I
  left_le_right : left ≤ right

namespace ClosedSubinterval

/-- The carrier of a closed subinterval. -/
def carrier (J : ClosedSubinterval) : Set I :=
  Set.Icc J.left J.right

/-- A closed subinterval has distinct endpoints. -/
def Nondegenerate (J : ClosedSubinterval) : Prop :=
  J.left < J.right

/-- The real length of a closed subinterval. -/
def length (J : ClosedSubinterval) : ℝ :=
  (J.right : ℝ) - (J.left : ℝ)

@[simp] theorem left_mem_carrier (J : ClosedSubinterval) :
    J.left ∈ J.carrier :=
  ⟨le_rfl, J.left_le_right⟩

@[simp] theorem right_mem_carrier (J : ClosedSubinterval) :
    J.right ∈ J.carrier :=
  ⟨J.left_le_right, le_rfl⟩

theorem carrier_nonempty (J : ClosedSubinterval) : J.carrier.Nonempty :=
  ⟨J.left, J.left_mem_carrier⟩

end ClosedSubinterval

/-- `T` maps `J` into itself. -/
def IsForwardInvariant (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  Set.MapsTo T J.carrier J.carrier

/-- `J` is forward invariant under both maps. -/
def IsCommonInvariantCore
    (P Q : IntervalMap) (J : ClosedSubinterval) : Prop :=
  IsForwardInvariant P J ∧ IsForwardInvariant Q J

/-- Surjectivity onto the entire unit interval. -/
def IsOnto (T : IntervalMap) : Prop :=
  Function.Surjective T

/-! ## Elementary iterate facts -/

namespace IntervalMap

/-- Every continuous interval self-map has a fixed point. -/
theorem exists_fixedPoint {T : IntervalMap} (hT : Continuous T) :
    ∃ x : I, IsFixedPoint T x := by
  let a : I := ⟨0, by simp [I]⟩
  let b : I := ⟨1, by simp [I]⟩
  have hab : a ≤ b := by simp [a, b]
  have ha : a ≤ T a := (T a).property.1
  have hb : T b ≤ b := (T b).property.2
  obtain ⟨x, _hx, hfix⟩ :=
    exists_mem_Icc_isFixedPt hT.continuousOn hab ha hb
  exact ⟨x, hfix⟩

/-- Iterating the left member preserves commutation. -/
theorem commute_iterate_left {P Q : IntervalMap}
    (h : Function.Commute P Q) (n : ℕ) :
    Function.Commute (P^[n]) Q :=
  h.iterate_left n

/-- Iterating the right member preserves commutation. -/
theorem commute_iterate_right {P Q : IntervalMap}
    (h : Function.Commute P Q) (n : ℕ) :
    Function.Commute P (Q^[n]) :=
  h.iterate_right n

/-- Iterates of commuting maps commute. -/
theorem commute_iterates {P Q : IntervalMap}
    (h : Function.Commute P Q) (m n : ℕ) :
    Function.Commute (P^[m]) (Q^[n]) :=
  (h.iterate_left m).iterate_right n

/-- An iterate of a continuous map is continuous. -/
theorem continuous_iterate {T : IntervalMap}
    (hT : Continuous T) (n : ℕ) :
    Continuous (T^[n]) :=
  hT.iterate n

/-- An iterate of a surjective map is surjective. -/
theorem surjective_iterate {T : IntervalMap}
    (hT : Surjective T) (n : ℕ) :
    Surjective (T^[n]) :=
  hT.iterate n

end IntervalMap

/-! ## Flat intervals and finite-piece affine maps -/

/-- `T` is constant on a nondegenerate closed interval. -/
def IsFlatInterval (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  J.Nondegenerate ∧
    ∀ {x}, x ∈ J.carrier → ∀ {y}, y ∈ J.carrier → T x = T y

/-- `T` has a nondegenerate flat interval. -/
def HasFlatInterval (T : IntervalMap) : Prop :=
  ∃ J : ClosedSubinterval, IsFlatInterval T J

/-- The part of an ambient real interval lying in `I`. -/
def intervalCell (a b : ℝ) : Set I :=
  {x : I | (x : ℝ) ∈ Set.Icc a b}

/-- The graph of `T` is affine on `s`. -/
def IsAffineOn (T : IntervalMap) (s : Set I) : Prop :=
  ∃ m c : ℝ,
    ∀ x ∈ s, (T x : ℝ) = m * (x : ℝ) + c

/-- A continuous map with a finite closed-cell affine presentation. -/
def FinitePiecePL (T : IntervalMap) : Prop :=
  Continuous T ∧
    ∃ p : RealPartition,
      ∀ {a b : ℝ}, p.Adjacent a b → IsAffineOn T (intervalCell a b)

namespace FinitePiecePL

theorem continuous {T : IntervalMap} (hT : FinitePiecePL T) : Continuous T :=
  hT.1

end FinitePiecePL

/-! ## Intrinsic turns and vertex values -/

/-- A genuine interior reversal of strict monotonicity. -/
def IsGenuineTurn (T : IntervalMap) (x : I) : Prop :=
  ∃ a b : I, a < x ∧ x < b ∧
    ((StrictMonoOn T (Set.Icc a x) ∧
        StrictAntiOn T (Set.Icc x b)) ∨
      (StrictAntiOn T (Set.Icc a x) ∧
        StrictMonoOn T (Set.Icc x b)))

/-- The intrinsic genuine-turn set. -/
def genuineTurns (T : IntervalMap) : Set I :=
  {x | IsGenuineTurn T x}

/-- The two domain endpoints together with all intrinsic turns. -/
def vertexDomain (T : IntervalMap) : Set I :=
  {leftEndpoint, rightEndpoint} ∪ genuineTurns T

/-- Images of endpoints and intrinsic turns. -/
def vertexValues (T : IntervalMap) : Set I :=
  T '' vertexDomain T

/-! ## Directed sides and one-sided germs -/

/-- A choice of the left or right side of a base point. -/
inductive Side where
  | left
  | right
  deriving DecidableEq

namespace Side

/-- The closed one-sided ray based at `x`. -/
def closedRay (side : Side) (x : I) : Set I :=
  match side with
  | .left => Set.Iic x
  | .right => Set.Ici x

/-- The punctured one-sided ray based at `x`. -/
def puncturedRay (side : Side) (x : I) : Set I :=
  match side with
  | .left => Set.Iio x
  | .right => Set.Ioi x

/-- The selected side contains a point other than its base. -/
def Available (side : Side) (x : I) : Prop :=
  (side.puncturedRay x).Nonempty

end Side

/-- A point together with a genuinely available side. -/
structure DirectedSide where
  base : I
  direction : Side
  available : direction.Available base

/-- The canonical right side at a point below `1`. -/
def rightDirectedSide (x : I) (hx : x < rightEndpoint) : DirectedSide where
  base := x
  direction := .right
  available := ⟨rightEndpoint, hx⟩

/-- The canonical left side at a point above `0`. -/
def leftDirectedSide (x : I) (hx : leftEndpoint < x) : DirectedSide where
  base := x
  direction := .left
  available := ⟨leftEndpoint, hx⟩

/-- Equality of two germs on a specified one-sided neighbourhood. -/
def SameOneSidedGermAt (side : Side) (x : I)
    (F G : IntervalMap) : Prop :=
  match side with
  | .left => ∃ a : I, a < x ∧ Set.EqOn F G (Set.Icc a x)
  | .right => ∃ b : I, x < b ∧ Set.EqOn F G (Set.Icc x b)

/-- Equality of germs on a packaged directed side. -/
def SameGermOnDirectedSide (σ : DirectedSide)
    (F G : IntervalMap) : Prop :=
  SameOneSidedGermAt σ.direction σ.base F G

/-! ## Scales and constant absolute slope -/

/-- No two positive natural powers of `a` and `b` agree. -/
def MultiplicativelyIndependent (a b : ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → a ^ m ≠ b ^ n

/-- A finite-piece PL map with prescribed absolute branch slope. -/
def HasConstantAbsoluteSlope (T : IntervalMap) (s : ℝ) : Prop :=
  Continuous T ∧
    ∃ p : RealPartition,
      ∀ {a b : ℝ}, p.Adjacent a b →
        ∃ m c : ℝ, |m| = s ∧
          ∀ x ∈ intervalCell a b,
            (T x : ℝ) = m * (x : ℝ) + c

namespace HasConstantAbsoluteSlope

theorem continuous {T : IntervalMap} {s : ℝ}
    (hT : HasConstantAbsoluteSlope T s) : Continuous T :=
  hT.1

theorem finitePiecePL {T : IntervalMap} {s : ℝ}
    (hT : HasConstantAbsoluteSlope T s) : FinitePiecePL T := by
  refine ⟨hT.1, ?_⟩
  obtain ⟨p, hp⟩ := hT.2
  refine ⟨p, ?_⟩
  intro a b hab
  obtain ⟨m, c, _hm, hformula⟩ := hp hab
  exact ⟨m, c, hformula⟩

end HasConstantAbsoluteSlope

end CommutingIntervalSimplified
