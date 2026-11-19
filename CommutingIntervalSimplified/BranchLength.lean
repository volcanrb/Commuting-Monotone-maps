import CommutingIntervalSimplified.PiecewiseMonotoneBase
import CommutingIntervalSimplified.BrouwerCompactConvex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Branch length and a common eigen-coordinate

This file freezes the B1--B6 interface used in the simplified proof.  A
branch-length sum is first defined using a chosen monotonicity partition.
Partition independence then permits a canonical operator for every
finite-piece piecewise-monotone interval map.

The final section records the finite-dimensional Brouwer argument in the
form needed by the factor construction.  Substantive analytic and
finite-dimensional arguments are intentionally exposed as individual
statements, so their remaining proofs can be filled without changing the
dependency graph.
-/

namespace CommutingIntervalSimplified

open Function Set MeasureTheory
open scoped Topology

/-! ## Normalized continuous real coordinates -/

/-- Continuous real coordinates on `I` which vanish at the left endpoint.
This is the natural vector space on which branch length acts. -/
def normalizedContinuousCoordinates : Submodule ℝ C(I, ℝ) where
  carrier := {S | S leftEndpoint = 0}
  zero_mem' := by simp
  add_mem' := by
    intro S R hS hR
    simp only [Set.mem_setOf_eq, ContinuousMap.add_apply]
    rw [hS, hR, add_zero]
  smul_mem' := by
    intro c S hS
    simp only [Set.mem_setOf_eq, ContinuousMap.smul_apply]
    rw [hS, smul_zero]

/-- A normalized continuous real coordinate. -/
abbrev NormalizedContinuousCoordinate := normalizedContinuousCoordinates

/-- Coerce a normalized continuous coordinate to its underlying function. -/
instance : CoeFun NormalizedContinuousCoordinate (fun _ => I → ℝ) where
  coe S := S.1

namespace NormalizedContinuousCoordinate

@[simp] theorem leftEndpoint_eq_zero (S : NormalizedContinuousCoordinate) :
    S leftEndpoint = 0 :=
  S.property

theorem continuous (S : NormalizedContinuousCoordinate) :
    Continuous (fun x : I => S x) :=
  S.1.continuous

end NormalizedContinuousCoordinate

/-- The unoriented `S`-length of the interval with endpoints `u,v`.
For a nondecreasing coordinate this is nonnegative. -/
def coordinateLength (S : I → ℝ) (u v : I) : ℝ :=
  S (max u v) - S (min u v)

@[simp] theorem coordinateLength_self (S : I → ℝ) (u : I) :
    coordinateLength S u u = 0 := by
  simp [coordinateLength]

theorem coordinateLength_comm (S : I → ℝ) (u v : I) :
    coordinateLength S u v = coordinateLength S v u := by
  simp only [coordinateLength, max_comm u v, min_comm u v]

/-- For a nondecreasing coordinate, the ordered interval increment is the
absolute difference of the endpoint values. -/
theorem coordinateLength_eq_abs_sub_of_monotone
    (S : I → ℝ) (hS : Monotone S) (u v : I) :
    coordinateLength S u v = |S v - S u| := by
  rcases le_total u v with huv | hvu
  · rw [coordinateLength, max_eq_right huv, min_eq_left huv,
      abs_of_nonneg (sub_nonneg.mpr (hS huv))]
  · rw [coordinateLength, max_eq_left hvu, min_eq_right hvu,
      abs_of_nonpos (sub_nonpos.mpr (hS hvu))]
    ring

namespace RealPartition.LapIndex

variable {p : RealPartition}

/-- An indexed lap's left endpoint, regarded as a point of `I`. -/
def leftPoint (q : p.LapIndex) : I :=
  ⟨q.left, p.points_subset q.adjacent.1⟩

/-- An indexed lap's right endpoint, regarded as a point of `I`. -/
def rightPoint (q : p.LapIndex) : I :=
  ⟨q.right, p.points_subset q.adjacent.2.1⟩

/-- Clamp `x` to the right endpoint of the lap.  It is used only when
`x` lies strictly to the right of the lap's left endpoint. -/
def clippedPoint (q : p.LapIndex) (x : I) : I :=
  ⟨min (x : ℝ) q.right,
    le_min x.property.1 (p.points_subset q.adjacent.2.1).1,
    (min_le_left (x : ℝ) q.right).trans x.property.2⟩

@[simp] theorem leftPoint_val (q : p.LapIndex) :
    (q.leftPoint : ℝ) = q.left := rfl

@[simp] theorem rightPoint_val (q : p.LapIndex) :
    (q.rightPoint : ℝ) = q.right := rfl

@[simp] theorem clippedPoint_val (q : p.LapIndex) (x : I) :
    (q.clippedPoint x : ℝ) = min (x : ℝ) q.right := rfl

end RealPartition.LapIndex

/-! Elementary ordered-partition combinatorics used by the local increment
calculation. -/

private noncomputable def lapIndexOfAdjacent {p : RealPartition}
    {a b : ℝ} (hab : p.Adjacent a b) : p.LapIndex := by
  classical
  refine ⟨(a, b), ?_⟩
  rw [RealPartition.adjacentPairs]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩

@[simp] private theorem lapIndexOfAdjacent_left {p : RealPartition}
    {a b : ℝ} (hab : p.Adjacent a b) :
    (lapIndexOfAdjacent hab).left = a := rfl

@[simp] private theorem lapIndexOfAdjacent_right {p : RealPartition}
    {a b : ℝ} (hab : p.Adjacent a b) :
    (lapIndexOfAdjacent hab).right = b := rfl

/-- Two directed cells of one finite partition either coincide or one lies
entirely to one side of the other. -/
private theorem adjacent_eq_or_left_or_right {p : RealPartition}
    {a b c d : ℝ} (hab : p.Adjacent a b) (hcd : p.Adjacent c d) :
    (c = a ∧ d = b) ∨ d ≤ a ∨ b ≤ c := by
  rcases lt_trichotomy c a with hca | hca | hac
  · right; left
    by_contra hda
    exact hcd.2.2.2 a hab.1 ⟨hca, lt_of_not_ge hda⟩
  · left
    refine ⟨hca, le_antisymm ?_ ?_⟩
    · by_contra hdb
      exact hcd.2.2.2 b hab.2.1
        ⟨by simpa [hca] using hab.2.2.1, lt_of_not_ge hdb⟩
    · by_contra hbd
      exact hab.2.2.2 d hcd.2.1
        ⟨by simpa [hca] using hcd.2.2.1, lt_of_not_ge hbd⟩
  · right; right
    by_contra hbc
    exact hab.2.2.2 c hcd.1 ⟨hac, lt_of_not_ge hbc⟩

/-- Every non-left endpoint lies in a partition cell whose left endpoint is
strictly smaller. -/
private theorem exists_adjacent_left_of_pos (p : RealPartition) (x : I)
    (hxpos : (0 : ℝ) < x) :
    ∃ a b : ℝ, p.Adjacent a b ∧ a < (x : ℝ) ∧ (x : ℝ) ≤ b := by
  classical
  by_cases hxvertex : (x : ℝ) ∈ p.points
  · let lower := p.points.filter fun z => z < (x : ℝ)
    have hlower : lower.Nonempty := by
      refine ⟨0, ?_⟩
      simp [lower, p.zero_mem, hxpos]
    obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
    have ha' := Finset.mem_filter.mp ha
    refine ⟨a, (x : ℝ), ⟨ha'.1, hxvertex, ha'.2, ?_⟩,
      ha'.2, le_rfl⟩
    intro c hc hac
    have hclower : c ∈ lower := Finset.mem_filter.mpr ⟨hc, hac.2⟩
    have hca : c ≤ a := by simpa using hamax c hclower
    exact (not_lt_of_ge hca) hac.1
  · obtain ⟨a, b, hab, hax, hxb⟩ := p.exists_adjacent_containing x
    have hax' : a < (x : ℝ) := lt_of_le_of_ne hax fun hxa =>
      hxvertex (hxa ▸ hab.1)
    exact ⟨a, b, hab, hax', hxb⟩

/-- Number of partition vertices strictly to the left of a point. -/
private noncomputable def partitionLowerRank (p : RealPartition) (x : I) : ℕ :=
  (p.points.filter fun z => z < (x : ℝ)).card

private theorem partitionLowerRank_lt {p : RealPartition} {a : ℝ}
    (ha : a ∈ p.points) (haI : a ∈ I) {x : I} (hax : a < (x : ℝ)) :
    partitionLowerRank p ⟨a, haI⟩ < partitionLowerRank p x := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.trans hax⟩
  · intro heq
    have haright : a ∈ p.points.filter fun z => z < (x : ℝ) :=
      Finset.mem_filter.mpr ⟨ha, hax⟩
    rw [← heq] at haright
    exact (Finset.mem_filter.mp haright).2.false

/-- A finite ordered-cell induction principle: two functions with the same
initial value and the same increment on every partition cell agree
everywhere.  No continuity is needed. -/
theorem funext_of_partition_increments (p : RealPartition)
    (f g : I → ℝ) (hleft : f leftEndpoint = g leftEndpoint)
    (hinc : ∀ {a b : ℝ}, p.Adjacent a b → ∀ {x y : I},
      x ∈ intervalCell a b → y ∈ intervalCell a b → x ≤ y →
      f y - f x = g y - g x) :
    f = g := by
  funext x
  refine (measure (partitionLowerRank p)).wf.induction
    (C := fun z => f z = g z) x ?_
  intro x ih
  by_cases hxleft : x = leftEndpoint
  · simpa [hxleft] using hleft
  · have hxpos : (0 : ℝ) < x :=
      lt_of_le_of_ne x.property.1 (fun h => hxleft (Subtype.ext h.symm))
    obtain ⟨a, b, hab, hax, hxb⟩ :=
      exists_adjacent_left_of_pos p x hxpos
    let xa : I := ⟨a, p.points_subset hab.1⟩
    have hrank : partitionLowerRank p xa < partitionLowerRank p x :=
      partitionLowerRank_lt hab.1 (p.points_subset hab.1) hax
    have hxa_eq : f xa = g xa := ih xa hrank
    have hxa_cell : xa ∈ intervalCell a b :=
      ⟨le_rfl, hab.2.2.1.le⟩
    have hx_cell : x ∈ intervalCell a b := ⟨hax.le, hxb⟩
    have hdelta := hinc hab hxa_cell hx_cell hax.le
    linarith

/-! ## B1: a chosen-partition branch-length sum -/

/-- The contribution of one lap to branch length up to `x`.  Laps wholly
to the left contribute their full endpoint length; the lap containing `x`
contributes its partial length; laps to the right contribute zero. -/
noncomputable def branchContribution {T : IntervalMap}
    (P : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    (q : P.partition.LapIndex) (x : I) : ℝ :=
  if (x : ℝ) ≤ q.left then 0
  else coordinateLength (fun z : I => S z)
    (T q.leftPoint) (T (q.clippedPoint x))

/-- Branch length computed from a specified monotonicity partition. -/
noncomputable def branchLengthOnPartition {T : IntervalMap}
    (P : MonotonicityPartition T) (S : NormalizedContinuousCoordinate) :
    I → ℝ :=
  fun x => ∑ q : P.partition.LapIndex, branchContribution P S q x

/-- The chosen-partition sum vanishes at the left endpoint. -/
@[simp] theorem branchLengthOnPartition_leftEndpoint {T : IntervalMap}
    (P : MonotonicityPartition T) (S : NormalizedContinuousCoordinate) :
    branchLengthOnPartition P S leftEndpoint = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q _hq
  have hnonneg : (0 : ℝ) ≤ q.left :=
    (P.partition.points_subset q.adjacent.1).1
  simp [branchContribution, hnonneg]

/-- The chosen-partition branch-length sum is continuous. -/
private theorem branchContribution_continuous {T : IntervalMap}
    (P : MonotonicityPartition T) (hTcont : Continuous T)
    (S : NormalizedContinuousCoordinate)
    (q : P.partition.LapIndex) :
    Continuous (branchContribution P S q) := by
  have hclip : Continuous (q.clippedPoint : I → I) := by
    apply Continuous.subtype_mk
    fun_prop
  have hlength : Continuous (fun x : I =>
      coordinateLength (fun z : I => S z)
        (T q.leftPoint) (T (q.clippedPoint x))) := by
    unfold coordinateLength
    have hTclip : Continuous (fun x : I => T (q.clippedPoint x)) :=
      hTcont.comp hclip
    have hmax : Continuous (fun x : I =>
        max (T q.leftPoint) (T (q.clippedPoint x))) :=
      continuous_const.max hTclip
    have hmin : Continuous (fun x : I =>
        min (T q.leftPoint) (T (q.clippedPoint x))) :=
      continuous_const.min hTclip
    exact (NormalizedContinuousCoordinate.continuous S).comp hmax |>.sub
      ((NormalizedContinuousCoordinate.continuous S).comp hmin)
  unfold branchContribution
  apply Continuous.if_le continuous_const hlength
    continuous_subtype_val continuous_const
  intro x hx
  have hclip_eq : q.clippedPoint x = q.leftPoint := by
    apply Subtype.ext
    change min (x : ℝ) q.right = q.left
    rw [hx, min_eq_left q.adjacent.2.2.1.le]
  rw [hclip_eq, coordinateLength_self]

theorem branchLengthOnPartition_continuous {T : IntervalMap}
    (P : MonotonicityPartition T) (hTcont : Continuous T)
    (S : NormalizedContinuousCoordinate) :
    Continuous (branchLengthOnPartition P S) := by
  unfold branchLengthOnPartition
  exact continuous_finsetSum Finset.univ fun q _ =>
    branchContribution_continuous P hTcont S q

/-- On its own cell, the distinguished lap contribution is precisely the
unoriented coordinate length from the cell's left endpoint. -/
private theorem branchContribution_of_adjacent {T : IntervalMap}
    (P : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    {a b : ℝ} (hab : P.partition.Adjacent a b) {x : I}
    (hx : x ∈ intervalCell a b) :
    branchContribution P S (lapIndexOfAdjacent hab) x =
      coordinateLength (fun z : I => S z)
        (T (lapIndexOfAdjacent hab).leftPoint) (T x) := by
  let q := lapIndexOfAdjacent hab
  have hleftx : q.leftPoint ≤ x := by
    change a ≤ (x : ℝ)
    exact hx.1
  have hxright : x ≤ q.rightPoint := by
    change (x : ℝ) ≤ b
    exact hx.2
  by_cases hbefore : (x : ℝ) ≤ q.left
  · have hxeq : x = q.leftPoint := le_antisymm hbefore hleftx
    subst x
    simp [branchContribution, q]
  · have hclip : q.clippedPoint x = x := by
      apply Subtype.ext
      exact min_eq_left hxright
    have hbefore' : ¬(x : ℝ) ≤ (lapIndexOfAdjacent hab).left := by
      simpa [q] using hbefore
    simp only [branchContribution, if_neg hbefore']
    rw [show (lapIndexOfAdjacent hab).clippedPoint x = x by
      simpa [q] using hclip]

/-- The change of the distinguished lap contribution across its own cell
is the coordinate length of the image subinterval. -/
private theorem branchContribution_sub_of_adjacent {T : IntervalMap}
    (P : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    {a b : ℝ} (hab : P.partition.Adjacent a b) {x y : I}
    (hx : x ∈ intervalCell a b) (hy : y ∈ intervalCell a b)
    (hxy : x ≤ y) :
    branchContribution P S (lapIndexOfAdjacent hab) y -
        branchContribution P S (lapIndexOfAdjacent hab) x =
      coordinateLength (fun z : I => S z) (T x) (T y) := by
  rw [branchContribution_of_adjacent P S hab hy,
    branchContribution_of_adjacent P S hab hx]
  let q := lapIndexOfAdjacent hab
  have hleft : q.leftPoint ∈ intervalCell a b := by
    change a ≤ a ∧ a ≤ b
    exact ⟨le_rfl, hab.2.2.1.le⟩
  have hleftx : q.leftPoint ≤ x := by
    change a ≤ (x : ℝ)
    exact hx.1
  have hlefty : q.leftPoint ≤ y := by
    change a ≤ (y : ℝ)
    exact hy.1
  rcases P.weaklyMonotoneOn_cell hab with hmono | hanti
  · have hTax : T q.leftPoint ≤ T x := hmono hleft hx hleftx
    have hTay : T q.leftPoint ≤ T y := hmono hleft hy hlefty
    have hTxy : T x ≤ T y := hmono hx hy hxy
    have hTax' : T (lapIndexOfAdjacent hab).leftPoint ≤ T x := by
      simpa [q] using hTax
    have hTay' : T (lapIndexOfAdjacent hab).leftPoint ≤ T y := by
      simpa [q] using hTay
    simp only [coordinateLength, max_eq_right hTax', min_eq_left hTax',
      max_eq_right hTay', min_eq_left hTay',
      max_eq_right hTxy, min_eq_left hTxy]
    ring
  · have hTax : T x ≤ T q.leftPoint := hanti hleft hx hleftx
    have hTay : T y ≤ T q.leftPoint := hanti hleft hy hlefty
    have hTxy : T y ≤ T x := hanti hx hy hxy
    have hTax' : T x ≤ T (lapIndexOfAdjacent hab).leftPoint := by
      simpa [q] using hTax
    have hTay' : T y ≤ T (lapIndexOfAdjacent hab).leftPoint := by
      simpa [q] using hTay
    simp only [coordinateLength, max_eq_left hTax', min_eq_right hTax',
      max_eq_left hTay', min_eq_right hTay',
      max_eq_left hTxy, min_eq_right hTxy]
    ring

/-- Every other lap is already constant, or still zero, while two points
move inside a fixed partition cell. -/
private theorem branchContribution_sub_eq_zero_of_ne {T : IntervalMap}
    (P : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    {a b : ℝ} (hab : P.partition.Adjacent a b) {x y : I}
    (hx : x ∈ intervalCell a b) (hy : y ∈ intervalCell a b)
    (q : P.partition.LapIndex) (hne : q ≠ lapIndexOfAdjacent hab) :
    branchContribution P S q y - branchContribution P S q x = 0 := by
  rcases adjacent_eq_or_left_or_right hab q.adjacent with heq | hleft | hright
  · exfalso
    apply hne
    apply Subtype.ext
    exact Prod.ext heq.1 heq.2
  · have hqx : q.left < (x : ℝ) :=
      q.adjacent.2.2.1.trans_le (hleft.trans hx.1)
    have hqy : q.left < (y : ℝ) :=
      q.adjacent.2.2.1.trans_le (hleft.trans hy.1)
    have hclipx : q.clippedPoint x = q.rightPoint := by
      apply Subtype.ext
      exact min_eq_right (hleft.trans hx.1)
    have hclipy : q.clippedPoint y = q.rightPoint := by
      apply Subtype.ext
      exact min_eq_right (hleft.trans hy.1)
    simp only [branchContribution, if_neg (not_le.mpr hqx),
      if_neg (not_le.mpr hqy), hclipx, hclipy, sub_self]
  · have hxq : (x : ℝ) ≤ q.left := hx.2.trans hright
    have hyq : (y : ℝ) ≤ q.left := hy.2.trans hright
    simp [branchContribution, hxq, hyq]

/-- Partition-local increment formula, before passing to the canonical
partition-independent coordinate. -/
theorem branchLengthOnPartition_increment {T : IntervalMap}
    (P : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    {a b : ℝ} (hab : P.partition.Adjacent a b) {x y : I}
    (hx : x ∈ intervalCell a b) (hy : y ∈ intervalCell a b)
    (hxy : x ≤ y) :
    branchLengthOnPartition P S y - branchLengthOnPartition P S x =
      coordinateLength (fun z : I => S z) (T x) (T y) := by
  classical
  simp only [branchLengthOnPartition, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single (lapIndexOfAdjacent hab)]
  · exact branchContribution_sub_of_adjacent P S hab hx hy hxy
  · intro q _hq hne
    exact branchContribution_sub_eq_zero_of_ne P S hab hx hy q hne
  · simp

/-- Package a chosen-partition branch-length sum as a normalized continuous
coordinate. -/
noncomputable def branchLengthCoordinateOnPartition {T : IntervalMap}
    (P : MonotonicityPartition T) (hTcont : Continuous T)
    (S : NormalizedContinuousCoordinate) :
    NormalizedContinuousCoordinate :=
  ⟨⟨branchLengthOnPartition P S,
      branchLengthOnPartition_continuous P hTcont S⟩,
    branchLengthOnPartition_leftEndpoint P S⟩

/-- Refining, or otherwise changing, the monotonicity partition does not
change branch length. -/
theorem branchLengthOnPartition_independent {T : IntervalMap}
    (P R : MonotonicityPartition T)
    (S : NormalizedContinuousCoordinate) :
    branchLengthOnPartition P S = branchLengthOnPartition R S := by
  let C := P.partition.commonRefinement R.partition
  have hCP : C.Refines P.partition := by
    simpa [C] using
      RealPartition.commonRefinement_refines_left P.partition R.partition
  have hCR : C.Refines R.partition := by
    simpa [C] using
      RealPartition.commonRefinement_refines_right P.partition R.partition
  apply funext_of_partition_increments C
      (branchLengthOnPartition P S) (branchLengthOnPartition R S)
  · simp
  · intro a b hab x y hx hy hxy
    obtain ⟨c, d, hcd, hsub⟩ := hCP.adjacent_subset hab
    obtain ⟨e, f, hef, hsub'⟩ := hCR.adjacent_subset hab
    calc
      branchLengthOnPartition P S y - branchLengthOnPartition P S x =
          coordinateLength (fun z : I => S z) (T x) (T y) :=
        branchLengthOnPartition_increment P S hcd
          (hsub hx) (hsub hy) hxy
      _ = branchLengthOnPartition R S y - branchLengthOnPartition R S x :=
        (branchLengthOnPartition_increment R S hef
          (hsub' hx) (hsub' hy) hxy).symm

theorem branchLengthCoordinateOnPartition_independent {T : IntervalMap}
    (P R : MonotonicityPartition T)
    (hTcont : Continuous T)
    (S : NormalizedContinuousCoordinate) :
    branchLengthCoordinateOnPartition P hTcont S =
      branchLengthCoordinateOnPartition R hTcont S := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact congrFun (branchLengthOnPartition_independent P R S)

/-! ## B2: the canonical branch-length operation and its local formula -/

/-- A fixed witness used only to define the canonical branch-length
operation.  Partition independence makes the resulting operation intrinsic. -/
noncomputable def chosenMonotonicityPartition {T : IntervalMap}
    (hT : FinitePieceMonotone T) : MonotonicityPartition T :=
  Classical.choice hT.2

/-- The intrinsic branch-length coordinate associated to `T`. -/
noncomputable def branchLength {T : IntervalMap}
    (hT : FinitePieceMonotone T)
    (S : NormalizedContinuousCoordinate) :
    NormalizedContinuousCoordinate :=
  branchLengthCoordinateOnPartition (chosenMonotonicityPartition hT)
    hT.continuous S

/-- The canonical operation can be computed using any chosen monotonicity
partition. -/
theorem branchLength_eq_onPartition {T : IntervalMap}
    (hT : FinitePieceMonotone T) (P : MonotonicityPartition T)
    (S : NormalizedContinuousCoordinate) :
    branchLength hT S = branchLengthCoordinateOnPartition P hT.continuous S := by
  exact branchLengthCoordinateOnPartition_independent
    (chosenMonotonicityPartition hT) P hT.continuous S

theorem branchLength_continuous {T : IntervalMap}
    (hT : FinitePieceMonotone T) (S : NormalizedContinuousCoordinate) :
    Continuous (fun x : I => branchLength hT S x) :=
  NormalizedContinuousCoordinate.continuous (branchLength hT S)

@[simp] theorem branchLength_leftEndpoint {T : IntervalMap}
    (hT : FinitePieceMonotone T) (S : NormalizedContinuousCoordinate) :
    branchLength hT S leftEndpoint = 0 :=
  (branchLength hT S).property

/-- On one monotonicity cell, the increment of branch length is exactly the
unoriented coordinate length of the image endpoints. -/
theorem branchLength_increment {T : IntervalMap}
    (hT : FinitePieceMonotone T) (P : MonotonicityPartition T)
    (S : NormalizedContinuousCoordinate) {a b : ℝ}
    (hab : P.partition.Adjacent a b) {x y : I}
    (hx : x ∈ intervalCell a b) (hy : y ∈ intervalCell a b)
    (hxy : x ≤ y) :
    branchLength hT S y - branchLength hT S x =
      coordinateLength (fun z : I => S z) (T x) (T y) := by
  rw [branchLength_eq_onPartition hT P S]
  exact branchLengthOnPartition_increment P S hab hx hy hxy

/-! ## B3: linearity and preservation of nondecreasing coordinates -/

private theorem branchContribution_add {T : IntervalMap}
    (P : MonotonicityPartition T)
    (S R : NormalizedContinuousCoordinate)
    (q : P.partition.LapIndex) (x : I) :
    branchContribution P (S + R) q x =
      branchContribution P S q x + branchContribution P R q x := by
  unfold branchContribution
  split
  · simp
  · simp only [coordinateLength]
    have heval (z : I) : (S + R) z = S z + R z := rfl
    rw [heval, heval]
    ring

private theorem branchContribution_smul {T : IntervalMap}
    (P : MonotonicityPartition T) (c : ℝ)
    (S : NormalizedContinuousCoordinate)
    (q : P.partition.LapIndex) (x : I) :
    branchContribution P (c • S) q x =
      c * branchContribution P S q x := by
  unfold branchContribution
  split
  · simp
  · simp only [coordinateLength]
    have heval (z : I) : (c • S) z = c * S z := rfl
    rw [heval, heval]
    ring

theorem branchLength_add {T : IntervalMap}
    (hT : FinitePieceMonotone T)
    (S R : NormalizedContinuousCoordinate) :
    branchLength hT (S + R) = branchLength hT S + branchLength hT R := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change branchLengthOnPartition (chosenMonotonicityPartition hT) (S + R) x =
    branchLengthOnPartition (chosenMonotonicityPartition hT) S x +
      branchLengthOnPartition (chosenMonotonicityPartition hT) R x
  simp only [branchLengthOnPartition, branchContribution_add,
    Finset.sum_add_distrib]

theorem branchLength_smul {T : IntervalMap}
    (hT : FinitePieceMonotone T) (c : ℝ)
    (S : NormalizedContinuousCoordinate) :
    branchLength hT (c • S) = c • branchLength hT S := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change branchLengthOnPartition (chosenMonotonicityPartition hT) (c • S) x =
    c * branchLengthOnPartition (chosenMonotonicityPartition hT) S x
  simp only [branchLengthOnPartition, branchContribution_smul,
    Finset.mul_sum]

/-- The canonical branch-length operator as a real-linear endomorphism. -/
noncomputable def branchLengthOperator {T : IntervalMap}
    (hT : FinitePieceMonotone T) :
    NormalizedContinuousCoordinate →ₗ[ℝ]
      NormalizedContinuousCoordinate where
  toFun := branchLength hT
  map_add' := branchLength_add hT
  map_smul' := branchLength_smul hT

@[simp] theorem branchLengthOperator_apply {T : IntervalMap}
    (hT : FinitePieceMonotone T)
    (S : NormalizedContinuousCoordinate) :
    branchLengthOperator hT S = branchLength hT S := rfl

/-- The branch-length operator is bounded (hence continuous) in the uniform
norm.  The deliberately coarse bound is twice the number of laps. -/
theorem branchLengthOperator_continuous {T : IntervalMap}
    (hT : FinitePieceMonotone T) :
    Continuous (branchLengthOperator hT) := by
  let P := chosenMonotonicityPartition hT
  apply AddMonoidHomClass.continuous_of_bound (branchLengthOperator hT)
    (2 * Fintype.card P.partition.LapIndex)
  intro S
  change ‖branchLengthCoordinateOnPartition P hT.continuous S‖ ≤
    (2 * Fintype.card P.partition.LapIndex : ℝ) * ‖S‖
  refine (ContinuousMap.norm_le
    (branchLengthCoordinateOnPartition P hT.continuous S).1
    (mul_nonneg (by positivity) (norm_nonneg S))).2 ?_
  intro x
  change ‖∑ q : P.partition.LapIndex, branchContribution P S q x‖ ≤
    (2 * Fintype.card P.partition.LapIndex : ℝ) * ‖S‖
  calc
    ‖∑ q : P.partition.LapIndex, branchContribution P S q x‖
        ≤ ∑ q : P.partition.LapIndex, ‖branchContribution P S q x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _q : P.partition.LapIndex, (2 * ‖S‖) := by
      apply Finset.sum_le_sum
      intro q _hq
      unfold branchContribution
      split
      · simp
      · simp only [coordinateLength]
        calc
          ‖S (max (T q.leftPoint) (T (q.clippedPoint x))) -
              S (min (T q.leftPoint) (T (q.clippedPoint x)))‖
              ≤ ‖S (max (T q.leftPoint) (T (q.clippedPoint x)))‖ +
                  ‖S (min (T q.leftPoint) (T (q.clippedPoint x)))‖ :=
            norm_sub_le _ _
          _ ≤ ‖S‖ + ‖S‖ := add_le_add
            (ContinuousMap.norm_coe_le_norm S.1 _)
            (ContinuousMap.norm_coe_le_norm S.1 _)
          _ = 2 * ‖S‖ := by ring
    _ = (2 * Fintype.card P.partition.LapIndex : ℝ) * ‖S‖ := by
      simp [mul_assoc, mul_comm, mul_left_comm]

private theorem branchContribution_monotone {T : IntervalMap}
    (P : MonotonicityPartition T)
    (S : NormalizedContinuousCoordinate)
    (hS : Monotone (fun x : I => S x))
    (q : P.partition.LapIndex) :
    Monotone (branchContribution P S q) := by
  intro x y hxy
  by_cases hxleft : (x : ℝ) ≤ q.left
  · rw [branchContribution, if_pos hxleft]
    rw [branchContribution]
    split
    · exact le_rfl
    · exact sub_nonneg.mpr (hS (min_le_max :
        min (T q.leftPoint) (T (q.clippedPoint y)) ≤
          max (T q.leftPoint) (T (q.clippedPoint y))))
  · have hyleft : ¬(y : ℝ) ≤ q.left := by
      intro hy
      apply hxleft
      exact (show (x : ℝ) ≤ (y : ℝ) from hxy).trans hy
    rw [branchContribution, if_neg hxleft,
      branchContribution, if_neg hyleft]
    have hxright : q.left ≤ min (x : ℝ) q.right :=
      le_min (lt_of_not_ge hxleft).le q.adjacent.2.2.1.le
    have hyright : q.left ≤ min (y : ℝ) q.right :=
      le_min (lt_of_not_ge hyleft).le q.adjacent.2.2.1.le
    have hleftCell : q.leftPoint ∈ intervalCell q.left q.right :=
      ⟨le_rfl, q.adjacent.2.2.1.le⟩
    have hxCell : q.clippedPoint x ∈ intervalCell q.left q.right :=
      ⟨hxright, min_le_right (x : ℝ) q.right⟩
    have hyCell : q.clippedPoint y ∈ intervalCell q.left q.right :=
      ⟨hyright, min_le_right (y : ℝ) q.right⟩
    have hleftx : q.leftPoint ≤ q.clippedPoint x := hxright
    have hxyclip : q.clippedPoint x ≤ q.clippedPoint y := by
      change min (x : ℝ) q.right ≤ min (y : ℝ) q.right
      exact min_le_min (show (x : ℝ) ≤ (y : ℝ) from hxy) le_rfl
    rcases P.weaklyMonotoneOn_cell q.adjacent with hmono | hanti
    · have hTx : T q.leftPoint ≤ T (q.clippedPoint x) :=
        hmono hleftCell hxCell hleftx
      have hTxy : T (q.clippedPoint x) ≤ T (q.clippedPoint y) :=
        hmono hxCell hyCell hxyclip
      have hTy : T q.leftPoint ≤ T (q.clippedPoint y) := hTx.trans hTxy
      simp only [coordinateLength, max_eq_right hTx, min_eq_left hTx,
        max_eq_right hTy, min_eq_left hTy]
      exact sub_le_sub_right (hS hTxy) _
    · have hTx : T (q.clippedPoint x) ≤ T q.leftPoint :=
        hanti hleftCell hxCell hleftx
      have hTxy : T (q.clippedPoint y) ≤ T (q.clippedPoint x) :=
        hanti hxCell hyCell hxyclip
      have hTy : T (q.clippedPoint y) ≤ T q.leftPoint := hTxy.trans hTx
      simp only [coordinateLength, max_eq_left hTx, min_eq_right hTx,
        max_eq_left hTy, min_eq_right hTy]
      exact sub_le_sub_left (hS hTxy) _

/-- Branch length sends nondecreasing coordinates to nondecreasing
coordinates. -/
theorem branchLength_monotone {T : IntervalMap}
    (hT : FinitePieceMonotone T) (S : NormalizedContinuousCoordinate)
    (hS : Monotone (fun x : I => S x)) :
    Monotone (fun x : I => branchLengthOperator hT S x) := by
  intro x y hxy
  change branchLengthOnPartition (chosenMonotonicityPartition hT) S x ≤
    branchLengthOnPartition (chosenMonotonicityPartition hT) S y
  apply Finset.sum_le_sum
  intro q _hq
  exact branchContribution_monotone
    (chosenMonotonicityPartition hT) S hS q hxy

/-- A finite family of closed real intervals covering `[0,1]` has total
length at least one.  This is the finite interval-cover estimate used in the
onto branch-length bound. -/
theorem one_le_sum_intervalLengths_of_cover {ι : Type*} [Fintype ι]
    (lo hi : ι → ℝ) (hlohi : ∀ i, lo i ≤ hi i)
    (hcover : Set.Icc (0 : ℝ) 1 ⊆ ⋃ i, Set.Icc (lo i) (hi i)) :
    1 ≤ ∑ i, (hi i - lo i) := by
  have hmeasure : (1 : ENNReal) ≤
      ∑ i, ENNReal.ofReal (hi i - lo i) := by
    calc
      (1 : ENNReal) = volume (Set.Icc (0 : ℝ) 1) := by
        simp [Real.volume_Icc]
      _ ≤ volume (⋃ i, Set.Icc (lo i) (hi i)) := measure_mono hcover
      _ ≤ ∑ i, volume (Set.Icc (lo i) (hi i)) :=
        measure_iUnion_fintype_le volume _
      _ = ∑ i, ENNReal.ofReal (hi i - lo i) := by
        simp only [Real.volume_Icc]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    sub_nonneg.mpr (hlohi i))] at hmeasure
  exact ENNReal.one_le_ofReal.mp hmeasure

/-- At the right endpoint every lap contributes its full image length. -/
theorem branchLength_rightEndpoint_eq_sum_coordinateLengths
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (S : NormalizedContinuousCoordinate) :
    branchLengthOperator hT S rightEndpoint =
      ∑ q : (chosenMonotonicityPartition hT).partition.LapIndex,
        coordinateLength (fun z : I => S z)
          (T q.leftPoint) (T q.rightPoint) := by
  classical
  let P := chosenMonotonicityPartition hT
  change branchLengthOnPartition P S rightEndpoint =
    ∑ q : P.partition.LapIndex,
      coordinateLength (fun z : I => S z)
        (T q.leftPoint) (T q.rightPoint)
  apply Finset.sum_congr rfl
  intro q _hq
  have hright_le : q.right ≤ (1 : ℝ) :=
    (P.partition.points_subset q.adjacent.2.1).2
  have hleft_lt : q.left < (1 : ℝ) :=
    q.adjacent.2.2.1.trans_le hright_le
  have hclip : q.clippedPoint rightEndpoint = q.rightPoint := by
    apply Subtype.ext
    exact min_eq_right hright_le
  simp [branchContribution, not_le.mpr hleft_lt, hclip]

/-- For an onto piecewise-monotone map, the coordinate images of its laps
cover the whole normalized coordinate interval `[0,1]`. -/
theorem coordinateImageIntervals_cover_of_surjective {T : IntervalMap}
    (hT : FinitePieceMonotone T) (honto : Function.Surjective T)
    (S : NormalizedContinuousCoordinate)
    (hS : Monotone (fun x : I => S x))
    (hSone : S rightEndpoint = 1) :
    Set.Icc (0 : ℝ) 1 ⊆
      ⋃ q : (chosenMonotonicityPartition hT).partition.LapIndex,
        Set.Icc
          (S (min (T q.leftPoint) (T q.rightPoint)))
          (S (max (T q.leftPoint) (T q.rightPoint))) := by
  classical
  let P := chosenMonotonicityPartition hT
  intro r hr
  have hrange : r ∈ Set.range (fun y : I => S y) := by
    apply intermediate_value_univ leftEndpoint rightEndpoint
      (NormalizedContinuousCoordinate.continuous S)
    simpa [hSone] using hr
  obtain ⟨y, hy⟩ := hrange
  obtain ⟨x, hTx⟩ := honto y
  have hxunion : x ∈ ⋃ q : P.partition.LapIndex, q.assignedCell := by
    rw [P.partition.iUnion_assignedCells]
    trivial
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxunion
  apply Set.mem_iUnion.mpr
  refine ⟨q, ?_⟩
  have hxcell : x ∈ intervalCell q.left q.right :=
    q.assignedCell_subset_closedCell hxq
  have hleftcell : q.leftPoint ∈ intervalCell q.left q.right :=
    ⟨le_rfl, q.adjacent.2.2.1.le⟩
  have hrightcell : q.rightPoint ∈ intervalCell q.left q.right :=
    ⟨q.adjacent.2.2.1.le, le_rfl⟩
  have hleftx : q.leftPoint ≤ x := hxcell.1
  have hxright : x ≤ q.rightPoint := hxcell.2
  rw [← hy, ← hTx]
  rcases P.weaklyMonotoneOn_cell q.adjacent with hmono | hanti
  · have hTl : T q.leftPoint ≤ T x := hmono hleftcell hxcell hleftx
    have hTr : T x ≤ T q.rightPoint := hmono hxcell hrightcell hxright
    rw [min_eq_left (hTl.trans hTr), max_eq_right (hTl.trans hTr)]
    exact ⟨hS hTl, hS hTr⟩
  · have hTl : T x ≤ T q.leftPoint := hanti hleftcell hxcell hleftx
    have hTr : T q.rightPoint ≤ T x := hanti hxcell hrightcell hxright
    rw [min_eq_right (hTr.trans hTl), max_eq_left (hTr.trans hTl)]
    exact ⟨hS hTr, hS hTl⟩

/-- For an onto map, the total branch length of a normalized nondecreasing
coordinate is at least one. -/
theorem one_le_branchLength_rightEndpoint_of_surjective {T : IntervalMap}
    (hT : FinitePieceMonotone T) (honto : Function.Surjective T)
    (S : NormalizedContinuousCoordinate)
    (hS : Monotone (fun x : I => S x))
    (hSone : S rightEndpoint = 1) :
    1 ≤ branchLengthOperator hT S rightEndpoint := by
  let P := chosenMonotonicityPartition hT
  have hcover := coordinateImageIntervals_cover_of_surjective
    hT honto S hS hSone
  have hlength := one_le_sum_intervalLengths_of_cover
    (fun q : P.partition.LapIndex =>
      S (min (T q.leftPoint) (T q.rightPoint)))
    (fun q : P.partition.LapIndex =>
      S (max (T q.leftPoint) (T q.rightPoint)))
    (fun q => hS (min_le_max)) hcover
  rw [branchLength_rightEndpoint_eq_sum_coordinateLengths hT S]
  simpa only [coordinateLength] using hlength

/-! ## B4: composition, commutation, and iteration -/

/-- On one monotonicity cell of `U`, measuring an interval with the
`U`-branch-length coordinate is the same as measuring its image with the
original coordinate. -/
private theorem coordinateLength_branchLength_of_mem_cell {U : IntervalMap}
    (hU : FinitePieceMonotone U) (wU : MonotonicityPartition U)
    (S : NormalizedContinuousCoordinate) {c d : ℝ}
    (hcd : wU.partition.Adjacent c d) {u v : I}
    (hu : u ∈ intervalCell c d) (hv : v ∈ intervalCell c d) :
    coordinateLength (fun z : I => branchLengthOperator hU S z) u v =
      coordinateLength (fun z : I => S z) (U u) (U v) := by
  rcases le_total u v with huv | hvu
  · rw [coordinateLength, max_eq_right huv, min_eq_left huv]
    exact branchLength_increment hU wU S hcd hu hv huv
  · rw [coordinateLength, max_eq_left hvu, min_eq_right hvu]
    calc
      branchLengthOperator hU S u - branchLengthOperator hU S v =
          coordinateLength (fun z : I => S z) (U v) (U u) :=
        branchLength_increment hU wU S hcd hv hu hvu
      _ = coordinateLength (fun z : I => S z) (U u) (U v) :=
        coordinateLength_comm _ _ _

/-- Branch length reverses the order of composition:
`L_(U ∘ T) = L_T ∘ L_U`. -/
theorem branchLengthOperator_comp {T U : IntervalMap}
    (hT : FinitePieceMonotone T) (hU : FinitePieceMonotone U) :
    branchLengthOperator (hU.comp hT) =
      (branchLengthOperator hT).comp (branchLengthOperator hU) := by
  let wT := chosenMonotonicityPartition hT
  let wU := chosenMonotonicityPartition hU
  let C := wT.compositionRefinement wU
  have hCref : C.Refines wT.partition := by
    simpa [C] using wT.compositionRefinement_refines wU
  let wTref : MonotonicityPartition T := wT.refine C hCref
  let wComp : MonotonicityPartition (U ∘ T) :=
    { partition := C
      weaklyMonotoneOn_cell := by
        intro a b hab
        obtain ⟨hTcell, c, d, hcd, hmaps⟩ :=
          wT.composition_cell hT.continuous wU hab
        exact (wU.weaklyMonotoneOn_cell hcd).comp hTcell hmaps }
  apply LinearMap.ext
  intro S
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  have hfun :
      (fun x : I => branchLengthOperator (hU.comp hT) S x) =
      (fun x : I =>
        ((branchLengthOperator hT).comp (branchLengthOperator hU)) S x) := by
    apply funext_of_partition_increments C
    · simp
    · intro a b hab x y hx hy hxy
      obtain ⟨_hTcell, c, d, hcd, hmaps⟩ :=
        wT.composition_cell hT.continuous wU hab
      calc
        branchLengthOperator (hU.comp hT) S y -
            branchLengthOperator (hU.comp hT) S x =
            coordinateLength (fun z : I => S z) ((U ∘ T) x) ((U ∘ T) y) :=
          branchLength_increment (hU.comp hT) wComp S hab hx hy hxy
        _ = coordinateLength
            (fun z : I => branchLengthOperator hU S z) (T x) (T y) :=
          (coordinateLength_branchLength_of_mem_cell hU wU S hcd
            (hmaps hx) (hmaps hy)).symm
        _ = ((branchLengthOperator hT).comp (branchLengthOperator hU)) S y -
            ((branchLengthOperator hT).comp (branchLengthOperator hU)) S x :=
          (branchLength_increment hT wTref (branchLengthOperator hU S)
            hab hx hy hxy).symm
  exact congrFun hfun z

/-- The canonical operator is independent of the proof of finite-piece
monotonicity. -/
theorem branchLengthOperator_proof_irrel {T : IntervalMap}
    (hT hT' : FinitePieceMonotone T) :
    branchLengthOperator hT = branchLengthOperator hT' := by
  have hp : hT = hT' := Subsingleton.elim _ _
  subst hT'
  rfl

/-- Equal interval maps have equal branch-length operators. -/
theorem branchLengthOperator_congr {T U : IntervalMap}
    (hTU : T = U) (hT : FinitePieceMonotone T)
    (hU : FinitePieceMonotone U) :
    branchLengthOperator hT = branchLengthOperator hU := by
  subst U
  exact branchLengthOperator_proof_irrel hT hU

/-- Commuting maps have commuting branch-length operators. -/
theorem branchLengthOperator_commute {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Function.Commute P Q) :
    (branchLengthOperator hP).comp (branchLengthOperator hQ) =
      (branchLengthOperator hQ).comp (branchLengthOperator hP) := by
  have hpq : P ∘ Q = Q ∘ P := funext hcomm.eq
  calc
    (branchLengthOperator hP).comp (branchLengthOperator hQ) =
        branchLengthOperator (hQ.comp hP) :=
      (branchLengthOperator_comp hP hQ).symm
    _ = branchLengthOperator (hP.comp hQ) :=
      branchLengthOperator_congr hpq.symm (hQ.comp hP) (hP.comp hQ)
    _ = (branchLengthOperator hQ).comp (branchLengthOperator hP) :=
      branchLengthOperator_comp hQ hP

/-- The identity interval map is finite-piece monotone. -/
theorem finitePieceMonotone_id :
    FinitePieceMonotone (id : IntervalMap) :=
  FinitePieceMonotone.of_monotone continuous_id monotone_id

/-- Branch length for the identity is the identity operator. -/
theorem branchLengthOperator_id :
    branchLengthOperator finitePieceMonotone_id =
      (LinearMap.id : NormalizedContinuousCoordinate →ₗ[ℝ]
        NormalizedContinuousCoordinate) := by
  let wId : MonotonicityPartition (id : IntervalMap) :=
    { partition := RealPartition.trivial
      weaklyMonotoneOn_cell := by
        intro a b hab
        exact Or.inl (monotone_id.monotoneOn _) }
  have h01 : RealPartition.trivial.Adjacent 0 1 := by
    simp [RealPartition.trivial, RealPartition.Adjacent]
  apply LinearMap.ext
  intro S
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  have hleft : leftEndpoint ∈ intervalCell 0 1 := by
    exact ⟨le_rfl, zero_le_one⟩
  have hx : x ∈ intervalCell 0 1 := x.property
  have hle : leftEndpoint ≤ x := x.property.1
  have hinc := branchLength_increment finitePieceMonotone_id wId S h01
    hleft hx hle
  simpa [coordinateLength, max_eq_right hle, min_eq_left hle] using hinc

/-- Branch length of an iterate is the corresponding operator power. -/
theorem branchLengthOperator_iterate {T : IntervalMap}
    (hT : FinitePieceMonotone T) (n : ℕ) :
    branchLengthOperator (hT.iterateMap n) =
      (branchLengthOperator hT) ^ n := by
  induction n with
  | zero =>
      calc
        branchLengthOperator (hT.iterateMap 0) =
            branchLengthOperator finitePieceMonotone_id :=
          branchLengthOperator_congr (by
            simp [CommutingIntervalSimplified.iterateMap])
            (hT.iterateMap 0) finitePieceMonotone_id
        _ = (LinearMap.id : NormalizedContinuousCoordinate →ₗ[ℝ]
              NormalizedContinuousCoordinate) := branchLengthOperator_id
        _ = (branchLengthOperator hT) ^ 0 := by
          rw [pow_zero, Module.End.one_eq_id]
  | succ n ih =>
      let hTn := hT.iterateMap n
      let hcomp : FinitePieceMonotone
          (T ∘ CommutingIntervalSimplified.iterateMap T n) := hT.comp hTn
      calc
        branchLengthOperator (hT.iterateMap (Nat.succ n)) =
            branchLengthOperator hcomp :=
          branchLengthOperator_congr (by
            exact Function.iterate_succ' T n)
            (hT.iterateMap (Nat.succ n)) hcomp
        _ = (branchLengthOperator hTn).comp (branchLengthOperator hT) :=
          branchLengthOperator_comp hTn hT
        _ = ((branchLengthOperator hT) ^ n).comp
            (branchLengthOperator hT) := by rw [ih]
        _ = (branchLengthOperator hT) ^ (Nat.succ n) := by
          rw [pow_succ, Module.End.mul_eq_comp]

/-! ## B5: finite-dimensional evaluation of an expanding eigenspace -/

/-- The `rho`-eigenspace of branch length. -/
noncomputable def branchEigenspace {H : IntervalMap}
    (hH : FinitePieceMonotone H) (rho : ℝ) :
    Submodule ℝ NormalizedContinuousCoordinate :=
  LinearMap.ker
    (branchLengthOperator hH -
      rho • (LinearMap.id : NormalizedContinuousCoordinate →ₗ[ℝ]
        NormalizedContinuousCoordinate))

@[simp] theorem mem_branchEigenspace {H : IntervalMap}
    (hH : FinitePieceMonotone H) (rho : ℝ)
    (S : NormalizedContinuousCoordinate) :
    S ∈ branchEigenspace hH rho ↔
      branchLengthOperator hH S = rho • S := by
  simp [branchEigenspace, sub_eq_zero]

/-- The finite type of vertices of a real partition. -/
abbrev RealPartition.Vertex (p : RealPartition) := ↥p.points

namespace RealPartition.Vertex

variable {p : RealPartition}

/-- A partition vertex, regarded as a point of `I`. -/
def point (v : p.Vertex) : I :=
  ⟨v.1, p.points_subset v.2⟩

@[simp] theorem point_val (v : p.Vertex) : (v.point : ℝ) = v.1 := rfl

end RealPartition.Vertex

/-- Evaluation after `H^n` at every vertex of a monotonicity partition of
`H^n`.  Its coordinates are the manuscript's finite set `V_n`, with harmless
repetitions retained in the finite index type. -/
noncomputable def iterateVertexEvaluation (H : IntervalMap) (n : ℕ)
    (R : MonotonicityPartition (iterateMap H n)) :
    NormalizedContinuousCoordinate →ₗ[ℝ] (R.partition.Vertex → ℝ) where
  toFun S v := S (iterateMap H n v.point)
  map_add' := by
    intro S W
    funext v
    rfl
  map_smul' := by
    intro c S
    funext v
    rfl

/-- Restrict finite vertex evaluation to the branch eigenspace. -/
noncomputable def branchEigenspaceVertexEvaluation {H : IntervalMap}
    (hH : FinitePieceMonotone H) (rho : ℝ) (n : ℕ)
    (R : MonotonicityPartition (iterateMap H n)) :
    branchEigenspace hH rho →ₗ[ℝ] (R.partition.Vertex → ℝ) :=
  (iterateVertexEvaluation H n R).comp (branchEigenspace hH rho).subtype

/-- Iterating a branch-length eigen-equation raises its eigenvalue to the
corresponding power. -/
theorem branchLengthOperator_pow_apply_of_eigen {H : IntervalMap}
    (hH : FinitePieceMonotone H) {rho : ℝ}
    (S : NormalizedContinuousCoordinate)
    (hS : branchLengthOperator hH S = rho • S) (n : ℕ) :
    ((branchLengthOperator hH) ^ n) S = rho ^ n • S := by
  induction n with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hS, map_smul, ih,
        smul_smul, pow_succ]
      rw [mul_comm rho (rho ^ n)]

/-- The same eigen-equation for the branch operator of an iterate. -/
theorem branchLengthOperator_iterate_apply_of_eigen {H : IntervalMap}
    (hH : FinitePieceMonotone H) {rho : ℝ}
    (S : NormalizedContinuousCoordinate)
    (hS : branchLengthOperator hH S = rho • S) (n : ℕ) :
    branchLengthOperator (hH.iterateMap n) S = rho ^ n • S := by
  rw [branchLengthOperator_iterate hH n]
  exact branchLengthOperator_pow_apply_of_eigen hH S hS n

private theorem coordinateLength_eq_zero_of_endpoints
    (S : I → ℝ) {u v : I} (hu : S u = 0) (hv : S v = 0) :
    coordinateLength S u v = 0 := by
  rcases le_total u v with huv | hvu
  · simp [coordinateLength, max_eq_right huv, min_eq_left huv, hu, hv]
  · simp [coordinateLength, max_eq_left hvu, min_eq_right hvu, hu, hv]

/-- Uniform sup-norm bound for one unoriented coordinate interval. -/
theorem norm_coordinateLength_le_two_norm
    (S : NormalizedContinuousCoordinate) (u v : I) :
    ‖coordinateLength (fun z : I => S z) u v‖ ≤ 2 * ‖S‖ := by
  simp only [coordinateLength]
  calc
    ‖S (max u v) - S (min u v)‖ ≤
        ‖S (max u v)‖ + ‖S (min u v)‖ := norm_sub_le _ _
    _ ≤ ‖S‖ + ‖S‖ := add_le_add
      (ContinuousMap.norm_coe_le_norm S.1 _)
      (ContinuousMap.norm_coe_le_norm S.1 _)
    _ = 2 * ‖S‖ := by ring

/-- If the coordinate vanishes at the images of all partition vertices,
branch length also vanishes at every source vertex. -/
private theorem branchLengthOnPartition_vertex_eq_zero {T : IntervalMap}
    (R : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    (hzero : ∀ v : R.partition.Vertex, S (T v.point) = 0)
    (v : R.partition.Vertex) :
    branchLengthOnPartition R S v.point = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro q _hq
  have hqleft : S (T q.leftPoint) = 0 := by
    let u : R.partition.Vertex := ⟨q.left, q.adjacent.1⟩
    simpa [u, RealPartition.Vertex.point,
      RealPartition.LapIndex.leftPoint] using hzero u
  have hqright : S (T q.rightPoint) = 0 := by
    let u : R.partition.Vertex := ⟨q.right, q.adjacent.2.1⟩
    simpa [u, RealPartition.Vertex.point,
      RealPartition.LapIndex.rightPoint] using hzero u
  by_cases hvleft : (v.point : ℝ) ≤ q.left
  · unfold branchContribution
    rw [if_pos hvleft]
  · have hrightv : q.right ≤ (v.point : ℝ) := by
      apply le_of_not_gt
      intro hvright
      exact q.adjacent.2.2.2 v.1 v.2
        ⟨lt_of_not_ge hvleft, by simpa using hvright⟩
    have hclip : q.clippedPoint v.point = q.rightPoint := by
      apply Subtype.ext
      exact min_eq_right hrightv
    have hcoord : coordinateLength (fun z : I => S z)
        (T q.leftPoint) (T q.rightPoint) = 0 :=
      coordinateLength_eq_zero_of_endpoints _ hqleft hqright
    unfold branchContribution
    rw [if_neg hvleft, hclip, hcoord]

/-- Completed branches have zero increment. The one partial branch starts
at a vertex whose coordinate is zero, so its absolute increment is bounded
by the norm of the coordinate itself. -/
theorem norm_branchLengthOperator_le_norm_of_vertex_zero
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    (hzero : ∀ v : R.partition.Vertex, S (T v.point) = 0) :
    ‖branchLengthOperator hT S‖ ≤ ‖S‖ := by
  refine (ContinuousMap.norm_le (branchLengthOperator hT S).1 (norm_nonneg S)).2 ?_
  intro x
  obtain ⟨a, b, hab, hx⟩ := R.partition.exists_adjacent_containing x
  let va : R.partition.Vertex := ⟨a, hab.1⟩
  have hva_cell : va.point ∈ intervalCell a b := by
    change a ≤ a ∧ a ≤ b
    exact ⟨le_rfl, hab.2.2.1.le⟩
  have hva_le : va.point ≤ x := by
    change a ≤ (x : ℝ)
    exact hx.1
  have hvzero : branchLengthOperator hT S va.point = 0 := by
    change branchLength hT S va.point = 0
    rw [branchLength_eq_onPartition hT R S]
    exact branchLengthOnPartition_vertex_eq_zero R S hzero va
  have hinc := branchLength_increment hT R S hab hva_cell hx hva_le
  have heq : branchLengthOperator hT S x =
      coordinateLength (fun z : I => S z) (T va.point) (T x) := by
    have hvzero' : branchLength hT S va.point = 0 := hvzero
    rw [hvzero', sub_zero] at hinc
    exact hinc
  rw [heq]
  rcases le_total (T va.point) (T x) with ha | ha
  · simpa only [coordinateLength, max_eq_right ha, min_eq_left ha, hzero va, sub_zero] using
      (ContinuousMap.norm_coe_le_norm S.1 (T x))
  · simpa only [coordinateLength, max_eq_left ha, min_eq_right ha, hzero va, zero_sub, norm_neg]
      using (ContinuousMap.norm_coe_le_norm S.1 (T x))

/-- The factor-two bound used by the iterate-partition argument. -/
theorem norm_branchLengthOperator_le_two_norm_of_vertex_zero
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : MonotonicityPartition T) (S : NormalizedContinuousCoordinate)
    (hzero : ∀ v : R.partition.Vertex, S (T v.point) = 0) :
    ‖branchLengthOperator hT S‖ ≤ 2 * ‖S‖ :=
  (norm_branchLengthOperator_le_norm_of_vertex_zero hT R S hzero).trans (by linarith [norm_nonneg S])

/-- Lemma 5.1 of *Common periodic points of commuting interval maps*.
An expanding eigen-coordinate is determined by its values at the images
of the original partition vertices, without passing to any iterate. -/
theorem branchEigenspace_originalVertexEvaluation_injective
    {H : IntervalMap} (hH : FinitePieceMonotone H) {ρ : ℝ} (hρ : 1 < ρ)
    (R : MonotonicityPartition H) :
    Function.Injective (branchEigenspaceVertexEvaluation hH ρ 1 R) := by
  intro S W he
  let V := S.val - W.val
  have hV : V ∈ branchEigenspace hH ρ := (branchEigenspace hH ρ).sub_mem S.property W.property
  have hvertices (v : R.partition.Vertex) : V (H v.point) = 0 :=
    sub_eq_zero.mpr (congrFun he v)
  have hb := norm_branchLengthOperator_le_norm_of_vertex_zero hH R V hvertices
  rw [(mem_branchEigenspace hH ρ V).mp hV] at hb
  have hscalar : ‖ρ • V‖ = ρ * ‖V‖ := by
    change ‖ρ • (V.1 : C(I, ℝ))‖ = ρ * ‖(V.1 : C(I, ℝ))‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hρ)]
  rw [hscalar] at hb
  have hz : ‖V‖ = 0 := by nlinarith [norm_nonneg V]
  exact Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hz))

/-- In particular the dimension is bounded by the number of vertices of
any monotonicity partition of the original map. -/
theorem branchEigenspace_finrank_le_partition_card
    {H : IntervalMap} (hH : FinitePieceMonotone H) {ρ : ℝ} (hρ : 1 < ρ)
    (R : MonotonicityPartition H) :
    Module.finrank ℝ (branchEigenspace hH ρ) ≤ R.partition.points.card := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using
    LinearMap.finrank_le_finrank_of_injective (branchEigenspace_originalVertexEvaluation_injective hH hρ R)

/-- An expanding branch eigen-coordinate which vanishes at every image of an
iterate-partition vertex is identically zero. -/
theorem branchEigen_eq_zero_of_iterateVertexEvaluation_eq_zero
    {H : IntervalMap} (hH : FinitePieceMonotone H) {rho : ℝ} (n : ℕ)
    (hpow : 2 < rho ^ n)
    (R : MonotonicityPartition (iterateMap H n))
    (S : NormalizedContinuousCoordinate)
    (hSeig : S ∈ branchEigenspace hH rho)
    (hzero : iterateVertexEvaluation H n R S = 0) :
    S = 0 := by
  have hzero_point (v : R.partition.Vertex) :
      S (iterateMap H n v.point) = 0 := by
    have hv := congrFun hzero v
    exact hv
  have hbound : ‖branchLengthOperator (hH.iterateMap n) S‖ ≤ 2 * ‖S‖ :=
    norm_branchLengthOperator_le_two_norm_of_vertex_zero
      (hH.iterateMap n) R S hzero_point
  have heigen : branchLengthOperator (hH.iterateMap n) S = rho ^ n • S :=
    branchLengthOperator_iterate_apply_of_eigen hH S
      ((mem_branchEigenspace hH rho S).mp hSeig) n
  have hnorm_smul : ‖rho ^ n • S‖ = rho ^ n * ‖S‖ := by
    change ‖rho ^ n • (S.1 : C(I, ℝ))‖ = rho ^ n * ‖(S.1 : C(I, ℝ))‖
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (lt_trans (by norm_num) hpow)]
  rw [heigen, hnorm_smul] at hbound
  have hnorm : ‖S‖ = 0 := by
    nlinarith [norm_nonneg S]
  exact norm_eq_zero.mp hnorm

/-- If `rho^n > 2`, evaluation at the images of the vertices of any
monotonicity partition of `H^n` is injective on the `rho`-eigenspace. -/
theorem branchEigenspaceVertexEvaluation_injective {H : IntervalMap}
    (hH : FinitePieceMonotone H) {rho : ℝ} (n : ℕ)
    (hpow : 2 < rho ^ n)
    (R : MonotonicityPartition (iterateMap H n)) :
    Function.Injective (branchEigenspaceVertexEvaluation hH rho n R) := by
  intro S W hSW
  have hdiff_mem : S.1 - W.1 ∈ branchEigenspace hH rho :=
    (branchEigenspace hH rho).sub_mem S.2 W.2
  have hzero : iterateVertexEvaluation H n R (S.1 - W.1) = 0 := by
    funext v
    have hv := congrFun hSW v
    exact sub_eq_zero.mpr hv
  have hdiff_zero : S.1 - W.1 = 0 :=
    branchEigen_eq_zero_of_iterateVertexEvaluation_eq_zero
      hH n hpow R (S.1 - W.1) hdiff_mem hzero
  apply Subtype.ext
  exact sub_eq_zero.mp hdiff_zero

/-- The injective finite evaluation gives finite dimensionality. -/
theorem branchEigenspace_finiteDimensional_of_pow_gt_two
    {H : IntervalMap} (hH : FinitePieceMonotone H) {rho : ℝ} (n : ℕ)
    (hpow : 2 < rho ^ n)
    (R : MonotonicityPartition (iterateMap H n)) :
    FiniteDimensional ℝ (branchEigenspace hH rho) := by
  exact FiniteDimensional.of_injective
    (branchEigenspaceVertexEvaluation hH rho n R)
    (branchEigenspaceVertexEvaluation_injective hH n hpow R)

/-- Every expanding branch-length eigenspace is finite-dimensional. -/
theorem branchEigenspace_finiteDimensional {H : IntervalMap}
    (hH : FinitePieceMonotone H) {rho : ℝ} (hrho : 1 < rho) :
    FiniteDimensional ℝ (branchEigenspace hH rho) := by
  obtain ⟨n, hpow⟩ := pow_unbounded_of_one_lt (2 : ℝ) hrho
  let R : MonotonicityPartition (iterateMap H n) :=
    Classical.choice (hH.iterateMap n).2
  exact branchEigenspace_finiteDimensional_of_pow_gt_two hH n hpow R

/-! ## B6: the normalized eigencone and the Brouwer package -/

/-- The normalized nondecreasing part of a branch eigenspace. -/
def branchEigenSimplex {H : IntervalMap}
    (hH : FinitePieceMonotone H) (rho : ℝ) :
    Set NormalizedContinuousCoordinate :=
  {S | S ∈ branchEigenspace hH rho ∧
    Monotone (fun x : I => S x) ∧ S rightEndpoint = 1}

theorem mem_branchEigenSimplex {H : IntervalMap}
    (hH : FinitePieceMonotone H) (rho : ℝ)
    (S : NormalizedContinuousCoordinate) :
    S ∈ branchEigenSimplex hH rho ↔
      branchLengthOperator hH S = rho • S ∧
      Monotone (fun x : I => S x) ∧ S rightEndpoint = 1 := by
  simp [branchEigenSimplex]

theorem branchEigenSimplex_convex {H : IntervalMap}
    (hH : FinitePieceMonotone H) (rho : ℝ) :
    Convex ℝ (branchEigenSimplex hH rho) := by
  intro S hS R hR a b ha hb hab
  rcases hS with ⟨hSeig, hSmono, hSone⟩
  rcases hR with ⟨hReig, hRmono, hRone⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (branchEigenspace hH rho).add_mem
      ((branchEigenspace hH rho).smul_mem a hSeig)
      ((branchEigenspace hH rho).smul_mem b hReig)
  · intro x y hxy
    change a * S x + b * R x ≤ a * S y + b * R y
    exact add_le_add (mul_le_mul_of_nonneg_left (hSmono hxy) ha)
      (mul_le_mul_of_nonneg_left (hRmono hxy) hb)
  · change a * S rightEndpoint + b * R rightEndpoint = 1
    rw [hSone, hRone]
    simpa using hab

theorem branchEigenSimplex_isClosed {H : IntervalMap}
    (hH : FinitePieceMonotone H) (rho : ℝ) :
    IsClosed (branchEigenSimplex hH rho) := by
  have heval (x : I) :
      Continuous (fun S : NormalizedContinuousCoordinate => S x) :=
    (ContinuousMap.evalCLM ℝ x).continuous.comp continuous_subtype_val
  have hcoe : Continuous
      (fun S : NormalizedContinuousCoordinate => fun x : I => S x) :=
    continuous_pi heval
  have heig : IsClosed
      {S : NormalizedContinuousCoordinate |
        branchLengthOperator hH S = rho • S} :=
    isClosed_eq (branchLengthOperator_continuous hH) (by fun_prop)
  have hmono : IsClosed
      {S : NormalizedContinuousCoordinate | Monotone (fun x : I => S x)} :=
    isClosed_monotone.preimage hcoe
  have hone : IsClosed
      {S : NormalizedContinuousCoordinate | S rightEndpoint = 1} :=
    isClosed_eq (heval rightEndpoint) continuous_const
  simpa only [branchEigenSimplex, mem_branchEigenspace, Set.setOf_and] using
    heig.inter (hmono.inter hone)

/-- Finite-dimensionality plus normalization and monotonicity make the
eigen-simplex compact. -/
theorem branchEigenSimplex_isCompact {H : IntervalMap}
    (hH : FinitePieceMonotone H) {rho : ℝ} (hrho : 1 < rho) :
    IsCompact (branchEigenSimplex hH rho) := by
  let E := branchEigenspace hH rho
  let K : Set E := {S | (S.1 : NormalizedContinuousCoordinate) ∈
    branchEigenSimplex hH rho}
  letI : FiniteDimensional ℝ E :=
    branchEigenspace_finiteDimensional hH hrho
  letI : ProperSpace E := FiniteDimensional.proper ℝ E
  have hKclosed : IsClosed K := by
    exact (branchEigenSimplex_isClosed hH rho).preimage continuous_subtype_val
  have hKsubset : K ⊆ Metric.closedBall (0 : E) 1 := by
    intro S hS
    rw [Metric.mem_closedBall]
    change dist (S.1 : NormalizedContinuousCoordinate) 0 ≤ 1
    rw [dist_zero_right]
    change ‖(S.1 : NormalizedContinuousCoordinate)‖ ≤ 1
    change ‖((S.1 : NormalizedContinuousCoordinate).1 : C(I, ℝ))‖ ≤ 1
    apply (ContinuousMap.norm_le _ (by norm_num)).2
    intro x
    rcases hS with ⟨_heig, hmono, hone⟩
    have hnonneg : 0 ≤ (S.1 : NormalizedContinuousCoordinate) x := by
      have h := hmono (show leftEndpoint ≤ x from x.property.1)
      simpa using h
    have hle : (S.1 : NormalizedContinuousCoordinate) x ≤ 1 := by
      exact (hmono (show x ≤ rightEndpoint from x.property.2)).trans_eq hone
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : E) 1).of_isClosed_subset
      hKclosed hKsubset
  have himage : ((fun S : E =>
      (S.1 : NormalizedContinuousCoordinate)) '' K) =
      branchEigenSimplex hH rho := by
    ext S
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact hW
    · intro hS
      refine ⟨⟨S, hS.1⟩, ?_, rfl⟩
      exact hS
  rw [← himage]
  exact hKcompact.image continuous_subtype_val

/-- A branch operator preserves the product eigenspace when its map
commutes with the other factor. -/
theorem branchLength_P_preserves_productEigenspace {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Function.Commute P Q) (rho : ℝ)
    {S : NormalizedContinuousCoordinate}
    (hS : S ∈ branchEigenspace (hP.comp hQ) rho) :
    branchLengthOperator hP S ∈ branchEigenspace (hP.comp hQ) rho := by
  rw [mem_branchEigenspace] at hS ⊢
  let A := branchLengthOperator hP
  let B := branchLengthOperator hQ
  let L := branchLengthOperator (hP.comp hQ)
  have hL : L = B.comp A := branchLengthOperator_comp hQ hP
  have hAB : A.comp B = B.comp A :=
    branchLengthOperator_commute hP hQ hcomm
  calc
    L (A S) = B (A (A S)) := by rw [hL]; rfl
    _ = A (B (A S)) := by
      exact (LinearMap.congr_fun hAB (A S)).symm
    _ = A (L S) := by rw [hL]; rfl
    _ = A (rho • S) := by rw [hS]
    _ = rho • A S := by rw [map_smul]

/-- The second branch operator also preserves the product eigenspace. -/
theorem branchLength_Q_preserves_productEigenspace {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Function.Commute P Q) (rho : ℝ)
    {S : NormalizedContinuousCoordinate}
    (hS : S ∈ branchEigenspace (hP.comp hQ) rho) :
    branchLengthOperator hQ S ∈ branchEigenspace (hP.comp hQ) rho := by
  rw [mem_branchEigenspace] at hS ⊢
  let A := branchLengthOperator hP
  let B := branchLengthOperator hQ
  let L := branchLengthOperator (hP.comp hQ)
  have hL : L = B.comp A := branchLengthOperator_comp hQ hP
  have hAB : A.comp B = B.comp A :=
    branchLengthOperator_commute hP hQ hcomm
  calc
    L (B S) = B (A (B S)) := by rw [hL]; rfl
    _ = B (B (A S)) := by
      exact congrArg B (LinearMap.congr_fun hAB S)
    _ = B (L S) := by rw [hL]; rfl
    _ = B (rho • S) := by rw [hS]
    _ = rho • B S := by rw [map_smul]

/-- Normalize branch length by its value at the right endpoint. -/
noncomputable def normalizedBranchAction {T : IntervalMap}
    (hT : FinitePieceMonotone T)
    (S : NormalizedContinuousCoordinate) :
    NormalizedContinuousCoordinate :=
  (branchLengthOperator hT S rightEndpoint)⁻¹ •
    branchLengthOperator hT S

/-- On the product eigen-simplex, the normalized `P`-action is again in
the same simplex. -/
theorem normalizedBranchAction_mem_productSimplex {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Function.Commute P Q) (hPonto : Function.Surjective P)
    (rho : ℝ) {S : NormalizedContinuousCoordinate}
    (hS : S ∈ branchEigenSimplex (hP.comp hQ) rho) :
    normalizedBranchAction hP S ∈
      branchEigenSimplex (hP.comp hQ) rho := by
  rcases hS with ⟨hSeig, hSmono, hSone⟩
  let A := branchLengthOperator hP S
  let d := A rightEndpoint
  have hd : 1 ≤ d :=
    one_le_branchLength_rightEndpoint_of_surjective
      hP hPonto S hSmono hSone
  have hdpos : 0 < d := zero_lt_one.trans_le hd
  have hAmem : A ∈ branchEigenspace (hP.comp hQ) rho :=
    branchLength_P_preserves_productEigenspace
      hP hQ hcomm rho hSeig
  have hAmono : Monotone (fun x : I => A x) :=
    branchLength_monotone hP S hSmono
  refine ⟨?_, ?_, ?_⟩
  · exact (branchEigenspace (hP.comp hQ) rho).smul_mem d⁻¹ hAmem
  · intro x y hxy
    change d⁻¹ * A x ≤ d⁻¹ * A y
    exact mul_le_mul_of_nonneg_left (hAmono hxy) (inv_nonneg.mpr hdpos.le)
  · change d⁻¹ * d = 1
    exact inv_mul_cancel₀ hdpos.ne'

/-- The normalized action is continuous on the eigen-simplex; positivity
of its denominator follows from surjectivity. -/
theorem normalizedBranchAction_continuousOn_productSimplex
    {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hPonto : Function.Surjective P) (rho : ℝ) :
    ContinuousOn (normalizedBranchAction hP)
      (branchEigenSimplex (hP.comp hQ) rho) := by
  have heval : Continuous
      (fun S : NormalizedContinuousCoordinate => S rightEndpoint) :=
    (ContinuousMap.evalCLM ℝ rightEndpoint).continuous.comp
      continuous_subtype_val
  have hdenom : Continuous
      (fun S : NormalizedContinuousCoordinate =>
        branchLengthOperator hP S rightEndpoint) :=
    heval.comp (branchLengthOperator_continuous hP)
  have hne : ∀ S ∈ branchEigenSimplex (hP.comp hQ) rho,
      branchLengthOperator hP S rightEndpoint ≠ 0 := by
    intro S hS
    have hd := one_le_branchLength_rightEndpoint_of_surjective
      hP hPonto S hS.2.1 hS.2.2
    exact (zero_lt_one.trans_le hd).ne'
  simpa only [normalizedBranchAction] using
    ContinuousOn.smul (ContinuousOn.inv₀ hdenom.continuousOn hne)
      (branchLengthOperator_continuous hP).continuousOn

/-- Brouwer supplies a fixed point of the normalized `P`-action. -/
theorem normalizedBranchAction_exists_fixedPoint {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Function.Commute P Q)
    (hPonto : Function.Surjective P) {rho : ℝ} (hrho : 1 < rho)
    (ψ : NormalizedContinuousCoordinate)
    (hψ : ψ ∈ branchEigenSimplex (hP.comp hQ) rho) :
    ∃ θ : NormalizedContinuousCoordinate,
      θ ∈ branchEigenSimplex (hP.comp hQ) rho ∧
      normalizedBranchAction hP θ = θ := by
  exact BrouwerSupport.compactConvex_exists_fixedPoint_explicit
    (branchEigenSimplex (hP.comp hQ) rho)
    (normalizedBranchAction hP)
    (branchEigenSimplex_isCompact (hP.comp hQ) hrho)
    (branchEigenSimplex_convex (hP.comp hQ) rho)
    ⟨ψ, hψ⟩
    (normalizedBranchAction_continuousOn_productSimplex hP hQ hPonto rho)
    (fun _ hS =>
      normalizedBranchAction_mem_productSimplex hP hQ hcomm hPonto rho hS)

/-- Data delivered by the common Brouwer eigen-coordinate argument. -/
structure CommonBranchEigenCoordinate {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (rho : ℝ) where
  coordinate : NormalizedContinuousCoordinate
  monotone : Monotone (fun x : I => coordinate x)
  rightEndpoint_eq_one : coordinate rightEndpoint = 1
  coordinate_mem_I : ∀ x : I, coordinate x ∈ I
  surjective_interval : ∀ y : I, ∃ x : I, coordinate x = (y : ℝ)
  scaleP : ℝ
  scaleQ : ℝ
  scaleP_pos : 0 < scaleP
  scaleQ_pos : 0 < scaleQ
  eigen_P : branchLengthOperator hP coordinate = scaleP • coordinate
  eigen_Q : branchLengthOperator hQ coordinate = scaleQ • coordinate
  product_eigen :
    branchLengthOperator (hP.comp hQ) coordinate = rho • coordinate
  scale_product : scaleP * scaleQ = rho

namespace CommonBranchEigenCoordinate

variable {P Q : IntervalMap}
  {hP : FinitePieceMonotone P} {hQ : FinitePieceMonotone Q}
  {rho : ℝ}

/-- Package the normalized real eigen-coordinate as an interval map. -/
def intervalCoordinate
    (E : CommonBranchEigenCoordinate hP hQ rho) : IntervalMap :=
  fun x => ⟨E.coordinate x, E.coordinate_mem_I x⟩

/-- The packaged interval coordinate is continuous. -/
theorem continuous_intervalCoordinate
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    Continuous E.intervalCoordinate :=
  (NormalizedContinuousCoordinate.continuous E.coordinate).subtype_mk _

/-- The packaged interval coordinate is nondecreasing. -/
theorem monotone_intervalCoordinate
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    Monotone E.intervalCoordinate := by
  intro x y hxy
  exact E.monotone hxy

/-- The packaged interval coordinate is onto `I`. -/
theorem surjective_intervalCoordinate
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    Function.Surjective E.intervalCoordinate := by
  intro y
  obtain ⟨x, hx⟩ := E.surjective_interval y
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

@[simp] theorem intervalCoordinate_leftEndpoint
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    E.intervalCoordinate leftEndpoint = leftEndpoint := by
  apply Subtype.ext
  exact NormalizedContinuousCoordinate.leftEndpoint_eq_zero E.coordinate

@[simp] theorem intervalCoordinate_rightEndpoint
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    E.intervalCoordinate rightEndpoint = rightEndpoint := by
  apply Subtype.ext
  exact E.rightEndpoint_eq_one

end CommonBranchEigenCoordinate

/-- Commuting onto maps with a normalized nondecreasing expanding product
eigen-coordinate have one coordinate which is an eigen-coordinate for both
branch operators. -/
theorem commonBranchEigenCoordinate_exists {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Function.Commute P Q)
    (hPonto : Function.Surjective P) (hQonto : Function.Surjective Q)
    {rho : ℝ} (hrho : 1 < rho)
    (ψ : NormalizedContinuousCoordinate)
    (hψmono : Monotone (fun x : I => ψ x))
    (hψone : ψ rightEndpoint = 1)
    (hψeigen : branchLengthOperator (hP.comp hQ) ψ = rho • ψ) :
    Nonempty (CommonBranchEigenCoordinate hP hQ rho) := by
  have hψmem : ψ ∈ branchEigenSimplex (hP.comp hQ) rho := by
    exact (mem_branchEigenSimplex (hP.comp hQ) rho ψ).2
      ⟨hψeigen, hψmono, hψone⟩
  obtain ⟨θ, hθmem, hfixed⟩ :=
    normalizedBranchAction_exists_fixedPoint
      hP hQ hcomm hPonto hrho ψ hψmem
  obtain ⟨hθproduct, hθmono, hθone⟩ :=
    (mem_branchEigenSimplex (hP.comp hQ) rho θ).1 hθmem
  let a : ℝ := branchLengthOperator hP θ rightEndpoint
  have ha : 0 < a := by
    have haone : 1 ≤ a := by
      exact one_le_branchLength_rightEndpoint_of_surjective
        hP hPonto θ hθmono hθone
    exact zero_lt_one.trans_le haone
  have hfixed' : a⁻¹ • branchLengthOperator hP θ = θ := by
    simpa only [normalizedBranchAction, a] using hfixed
  have hPeig : branchLengthOperator hP θ = a • θ := by
    ext x
    have hx := congrArg (fun S : NormalizedContinuousCoordinate => S x) hfixed'
    change a⁻¹ * branchLengthOperator hP θ x = θ x at hx
    change branchLengthOperator hP θ x = a * θ x
    rw [← hx, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  have hBA :
      branchLengthOperator hQ (branchLengthOperator hP θ) = rho • θ := by
    change ((branchLengthOperator hQ).comp (branchLengthOperator hP)) θ =
      rho • θ
    rw [← branchLengthOperator_comp hQ hP]
    exact hθproduct
  have hscaledQ : a • branchLengthOperator hQ θ = rho • θ := by
    calc
      a • branchLengthOperator hQ θ =
          branchLengthOperator hQ (a • θ) := by rw [map_smul]
      _ = branchLengthOperator hQ (branchLengthOperator hP θ) :=
        congrArg (branchLengthOperator hQ) hPeig.symm
      _ = rho • θ := hBA
  let b : ℝ := a⁻¹ * rho
  have hb : 0 < b := mul_pos (inv_pos.mpr ha) (zero_lt_one.trans hrho)
  have hQeig : branchLengthOperator hQ θ = b • θ := by
    ext x
    have hx := congrArg (fun S : NormalizedContinuousCoordinate => S x) hscaledQ
    change a * branchLengthOperator hQ θ x = rho * θ x at hx
    change branchLengthOperator hQ θ x = b * θ x
    calc
      branchLengthOperator hQ θ x =
          a⁻¹ * (a * branchLengthOperator hQ θ x) := by
            rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      _ = a⁻¹ * (rho * θ x) := by rw [hx]
      _ = b * θ x := by simp only [b, mul_assoc]
  refine ⟨{
    coordinate := θ
    monotone := hθmono
    rightEndpoint_eq_one := hθone
    coordinate_mem_I := ?_
    surjective_interval := ?_
    scaleP := a
    scaleQ := b
    scaleP_pos := ha
    scaleQ_pos := hb
    eigen_P := hPeig
    eigen_Q := hQeig
    product_eigen := hθproduct
    scale_product := ?_
  }⟩
  · intro x
    constructor
    · have hx := hθmono (show leftEndpoint ≤ x from x.property.1)
      simpa using hx
    · have hx := hθmono (show x ≤ rightEndpoint from x.property.2)
      simpa [hθone] using hx
  · intro y
    have hy : (y : ℝ) ∈ Set.Icc (θ leftEndpoint) (θ rightEndpoint) := by
      simpa [hθone] using y.property
    obtain ⟨x, _hx, hxy⟩ :=
      (intermediate_value_Icc
        (show leftEndpoint ≤ rightEndpoint by exact zero_le_one)
        (NormalizedContinuousCoordinate.continuous θ).continuousOn) hy
    exact ⟨x, hxy⟩
  · dsimp [b]
    rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

end CommutingIntervalSimplified
