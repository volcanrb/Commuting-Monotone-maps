import CommutingIntervalSimplified.Base
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Order.IntermediateValue

/-!
# Standalone continuous finite-piece piecewise-monotone interval maps

This module extracts the finite-piece monotonicity, refinement, measurable
assigned-cell, composition, and iteration infrastructure needed by the
simplified argument.  It depends only on the local standalone base and
Mathlib.
-/

namespace CommutingIntervalSimplified

open Function Set
open scoped Topology

/-! ## The basic predicate and its witnesses -/

/-- A map is non-strictly monotone on `s`, with either orientation allowed. -/
def IsWeaklyMonotoneOn (T : IntervalMap) (s : Set I) : Prop :=
  MonotoneOn T s ∨ AntitoneOn T s

/-- A chosen finite closed-cell monotonicity partition for `T`. -/
structure MonotonicityPartition (T : IntervalMap) where
  /-- The vertices of the partition. -/
  partition : RealPartition
  /-- On every closed cell, `T` has one of the two weak orientations. -/
  weaklyMonotoneOn_cell :
    ∀ ⦃a b : ℝ⦄, partition.Adjacent a b →
      IsWeaklyMonotoneOn T (intervalCell a b)

/-- A finite-piece piecewise-monotone interval map, with constant pieces
and nontrivial plateau subintervals allowed. -/
def FinitePieceMonotone (T : IntervalMap) : Prop :=
  Continuous T ∧ Nonempty (MonotonicityPartition T)

namespace FinitePieceMonotone

variable {T U : IntervalMap}

/-- The continuity carried by a finite-piece piecewise-monotone map. -/
theorem continuous (hT : FinitePieceMonotone T) : Continuous T := hT.1

/-- Extract a closed-cell monotonicity witness. -/
theorem exists_partition (hT : FinitePieceMonotone T) :
    ∃ p : RealPartition, ∀ ⦃a b : ℝ⦄, p.Adjacent a b →
      IsWeaklyMonotoneOn T (intervalCell a b) := by
  rcases hT.2 with ⟨w⟩
  exact ⟨w.partition, w.weaklyMonotoneOn_cell⟩

/-- Package an explicit partition as a finite-piece monotonicity proof. -/
theorem of_partition (hcont : Continuous T) (p : RealPartition)
    (hp : ∀ ⦃a b : ℝ⦄, p.Adjacent a b →
      IsWeaklyMonotoneOn T (intervalCell a b)) :
    FinitePieceMonotone T := by
  exact ⟨hcont, ⟨⟨p, hp⟩⟩⟩

end FinitePieceMonotone

namespace IsWeaklyMonotoneOn

variable {T U : IntervalMap} {s t : Set I}

/-- Weak monotonicity survives restriction of the domain. -/
theorem mono (h : IsWeaklyMonotoneOn T t) (hst : s ⊆ t) :
    IsWeaklyMonotoneOn T s := by
  rcases h with h | h
  · exact Or.inl (h.mono hst)
  · exact Or.inr (h.mono hst)

/-- The composite of weakly monotone maps is weakly monotone, with the
orientation determined by the two branch orientations. -/
theorem comp (hU : IsWeaklyMonotoneOn U t)
    (hT : IsWeaklyMonotoneOn T s) (hmaps : MapsTo T s t) :
    IsWeaklyMonotoneOn (U ∘ T) s := by
  rcases hU with hU | hU <;> rcases hT with hT | hT
  · exact Or.inl (hU.comp hT hmaps)
  · exact Or.inr (hU.comp_AntitoneOn hT hmaps)
  · exact Or.inr (hU.comp_MonotoneOn hT hmaps)
  · exact Or.inl (hU.comp hT hmaps)

end IsWeaklyMonotoneOn

/-! ## Finite real partitions and refinement -/

namespace RealPartition

/-- The one-cell partition with vertices `0` and `1`. -/
noncomputable def trivial : RealPartition where
  points := {0, 1}
  zero_mem := by simp
  one_mem := by simp
  points_subset := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [I]

/-- `fine` refines `coarse` when it contains all vertices of `coarse`. -/
def Refines (fine coarse : RealPartition) : Prop :=
  coarse.points ⊆ fine.points

/-- The common refinement obtained by adjoining both finite vertex sets. -/
noncomputable def commonRefinement (p q : RealPartition) : RealPartition where
  points := p.points ∪ q.points
  zero_mem := by simp [p.zero_mem]
  one_mem := by simp [p.one_mem]
  points_subset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact p.points_subset hx
    · exact q.points_subset hx

theorem refines_refl (p : RealPartition) : p.Refines p := by
  exact fun _ hx => hx

theorem Refines.trans {p q r : RealPartition} (hpq : p.Refines q)
    (hqr : q.Refines r) : p.Refines r := by
  exact fun _ hx => hpq (hqr hx)

theorem commonRefinement_refines_left (p q : RealPartition) :
    (p.commonRefinement q).Refines p := by
  intro x hx
  exact Finset.mem_union_left q.points hx

theorem commonRefinement_refines_right (p q : RealPartition) :
    (p.commonRefinement q).Refines q := by
  intro x hx
  exact Finset.mem_union_right p.points hx

/-- A pair of consecutive coarse vertices encloses a smaller interval whose
interior contains no coarse vertex. -/
theorem exists_adjacent_superset (p : RealPartition) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a < b)
    (hnone : ∀ c ∈ p.points, ¬(a < c ∧ c < b)) :
    ∃ c d, p.Adjacent c d ∧ Set.Icc a b ⊆ Set.Icc c d := by
  classical
  let lower := p.points.filter fun x => x ≤ a
  let upper := p.points.filter fun x => b ≤ x
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, p.zero_mem, ha.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    simp [upper, p.one_mem, hb.2]
  obtain ⟨c, hc, hcmax⟩ := lower.exists_max_image id hlower
  obtain ⟨d, hd, hdmin⟩ := upper.exists_min_image id hupper
  have hc' := Finset.mem_filter.mp hc
  have hd' := Finset.mem_filter.mp hd
  have hca : c ≤ a := hc'.2
  have hbd : b ≤ d := hd'.2
  have hcd : c < d := hca.trans_lt (hab.trans_le hbd)
  refine ⟨c, d, ⟨hc'.1, hd'.1, hcd, ?_⟩, ?_⟩
  · intro e he hed
    by_cases hea : e ≤ a
    · have helower : e ∈ lower := Finset.mem_filter.mpr ⟨he, hea⟩
      have hec : e ≤ c := by simpa using hcmax e helower
      exact (not_lt_of_ge hec) hed.1
    · by_cases hbe : b ≤ e
      · have heupper : e ∈ upper := Finset.mem_filter.mpr ⟨he, hbe⟩
        have hde : d ≤ e := by simpa using hdmin e heupper
        exact (not_lt_of_ge hde) hed.2
      · exact hnone e he ⟨lt_of_not_ge hea, lt_of_not_ge hbe⟩
  · intro x hx
    exact ⟨hca.trans hx.1, hx.2.trans hbd⟩

/-- Every cell of a refinement is contained in a cell of the coarser
partition. -/
theorem Refines.adjacent_subset {fine coarse : RealPartition}
    (h : fine.Refines coarse) {a b : ℝ} (hab : fine.Adjacent a b) :
    ∃ c d, coarse.Adjacent c d ∧ Set.Icc a b ⊆ Set.Icc c d := by
  apply coarse.exists_adjacent_superset
  · exact fine.points_subset hab.1
  · exact fine.points_subset hab.2.1
  · exact hab.2.2.1
  · intro c hc
    exact hab.2.2.2 c (h hc)

/-- If `x < 1`, there is a unique-style right-assigned cell satisfying
`a ≤ x < b`.  Existence is all that subsequent constructions need. -/
theorem exists_adjacent_Ico (p : RealPartition) {x : I}
    (hx : x < rightEndpoint) :
    ∃ a b : ℝ, p.Adjacent a b ∧ a ≤ (x : ℝ) ∧ (x : ℝ) < b := by
  classical
  let lower := p.points.filter fun z => z ≤ (x : ℝ)
  let upper := p.points.filter fun z => (x : ℝ) < z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, p.zero_mem, x.property.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have hx1 : (x : ℝ) < 1 := hx
    simp [upper, p.one_mem, hx1]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨a, b, ⟨ha'.1, hb'.1, ha'.2.trans_lt hb'.2, ?_⟩,
    ha'.2, hb'.2⟩
  intro c hc hacb
  by_cases hcx : c ≤ (x : ℝ)
  · have hclower : c ∈ lower := Finset.mem_filter.mpr ⟨hc, hcx⟩
    have hca : c ≤ a := by simpa using hamax c hclower
    exact (not_lt_of_ge hca) hacb.1
  · have hxc : (x : ℝ) < c := lt_of_not_ge hcx
    have hcupper : c ∈ upper := Finset.mem_filter.mpr ⟨hc, hxc⟩
    have hbc : b ≤ c := by simpa using hbmin c hcupper
    exact (not_lt_of_ge hbc) hacb.2

/-- The endpoint `1` belongs to a final adjacent cell. -/
theorem exists_adjacent_one (p : RealPartition) :
    ∃ a : ℝ, p.Adjacent a 1 := by
  classical
  let lower := p.points.filter fun z => z < (1 : ℝ)
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, p.zero_mem]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  have ha' := Finset.mem_filter.mp ha
  refine ⟨a, ⟨ha'.1, p.one_mem, ha'.2, ?_⟩⟩
  intro c hc hac
  have hclower : c ∈ lower := Finset.mem_filter.mpr ⟨hc, hac.2⟩
  have hca : c ≤ a := by simpa using hamax c hclower
  exact (not_lt_of_ge hca) hac.1

/-- Every point of `I` is contained in some closed partition cell. -/
theorem exists_adjacent_containing (p : RealPartition) (x : I) :
    ∃ a b : ℝ, p.Adjacent a b ∧ x ∈ intervalCell a b := by
  by_cases hx : x < rightEndpoint
  · obtain ⟨a, b, hab, hax, hxb⟩ := p.exists_adjacent_Ico hx
    exact ⟨a, b, hab, hax, hxb.le⟩
  · have hxeq : x = rightEndpoint := le_antisymm x.property.2 (le_of_not_gt hx)
    obtain ⟨a, ha⟩ := p.exists_adjacent_one
    refine ⟨a, 1, ha, ?_⟩
    change (x : ℝ) ∈ Set.Icc a 1
    rw [hxeq]
    exact ⟨ha.2.2.1.le, le_rfl⟩

/-- The finite set of directed adjacent vertex pairs. -/
noncomputable def adjacentPairs (p : RealPartition) : Finset (ℝ × ℝ) := by
  classical
  exact (p.points.product p.points).filter fun q => p.Adjacent q.1 q.2

/-- An index for a monotonicity lap of a real partition. -/
noncomputable def LapIndex (p : RealPartition) :=
  {q : ℝ × ℝ // q ∈ p.adjacentPairs}

noncomputable instance (p : RealPartition) : Fintype p.LapIndex := by
  classical
  unfold LapIndex
  infer_instance

namespace LapIndex

variable {p : RealPartition}

/-- The left endpoint of an indexed lap. -/
def left (q : p.LapIndex) : ℝ := q.1.1

/-- The right endpoint of an indexed lap. -/
def right (q : p.LapIndex) : ℝ := q.1.2

/-- The endpoints of an indexed lap are adjacent. -/
theorem adjacent (q : p.LapIndex) : p.Adjacent q.left q.right := by
  classical
  have hq := q.property
  change q.val ∈ (p.points.product p.points).filter
    (fun z => p.Adjacent z.1 z.2) at hq
  exact (Finset.mem_filter.mp hq).2

/-- The closed cell underlying an indexed lap. -/
def closedCell (q : p.LapIndex) : Set I :=
  intervalCell q.left q.right

/-- The Borel lap obtained by assigning every internal vertex to the branch
on its right; the last branch also contains `1`. -/
def assignedCell (q : p.LapIndex) : Set I :=
  if q.right = 1 then
    {x : I | (x : ℝ) ∈ Set.Icc q.left q.right}
  else
    {x : I | (x : ℝ) ∈ Set.Ico q.left q.right}

theorem assignedCell_subset_closedCell (q : p.LapIndex) :
    q.assignedCell ⊆ q.closedCell := by
  intro x hx
  by_cases hright : q.right = 1
  · simpa [assignedCell, closedCell, hright] using hx
  · have hx' : (x : ℝ) ∈ Set.Ico q.left q.right := by
      simpa [assignedCell, hright] using hx
    exact ⟨hx'.1, hx'.2.le⟩

theorem measurableSet_assignedCell (q : p.LapIndex) :
    MeasurableSet q.assignedCell := by
  by_cases hright : q.right = 1
  · simp only [assignedCell, hright, ↓reduceIte]
    exact (measurableSet_Icc : MeasurableSet
      (Set.Icc q.left 1)).preimage measurable_subtype_coe
  · simp only [assignedCell, hright, ↓reduceIte]
    exact (measurableSet_Ico : MeasurableSet
      (Set.Ico q.left q.right)).preimage measurable_subtype_coe

end LapIndex

/-- The assigned lap cells cover `I`. -/
theorem iUnion_assignedCells (p : RealPartition) :
    (⋃ q : p.LapIndex, q.assignedCell) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x < rightEndpoint
  · obtain ⟨a, b, hab, hax, hxb⟩ := p.exists_adjacent_Ico hx
    have hpair : (a, b) ∈ p.adjacentPairs := by
      rw [adjacentPairs]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩
    let q : p.LapIndex := ⟨(a, b), hpair⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    dsimp [q, RealPartition.LapIndex.assignedCell,
      RealPartition.LapIndex.left, RealPartition.LapIndex.right]
    split
    · change (x : ℝ) ∈ Set.Icc a b
      exact ⟨hax, hxb.le⟩
    · change (x : ℝ) ∈ Set.Ico a b
      exact ⟨hax, hxb⟩
  · have hxeq : x = rightEndpoint := le_antisymm x.property.2 (le_of_not_gt hx)
    obtain ⟨a, ha⟩ := p.exists_adjacent_one
    have hpair : (a, (1 : ℝ)) ∈ p.adjacentPairs := by
      rw [adjacentPairs]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨ha.1, ha.2.1⟩, ha⟩
    let q : p.LapIndex := ⟨(a, 1), hpair⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    dsimp [q, RealPartition.LapIndex.assignedCell,
      RealPartition.LapIndex.left, RealPartition.LapIndex.right]
    simp [hxeq, rightEndpoint, ha.2.2.1.le]

private theorem adjacent_eq_of_common_Ico (p : RealPartition)
    {a b c d x : ℝ} (hab : p.Adjacent a b) (hcd : p.Adjacent c d)
    (hxab : a ≤ x ∧ x < b) (hxcd : c ≤ x ∧ x < d) :
    a = c ∧ b = d := by
  have hac : a = c := by
    apply le_antisymm
    · by_contra h
      have hca : c < a := lt_of_not_ge h
      exact hcd.2.2.2 a hab.1 ⟨hca, hxab.1.trans_lt hxcd.2⟩
    · by_contra h
      have hac : a < c := lt_of_not_ge h
      exact hab.2.2.2 c hcd.1 ⟨hac, hxcd.1.trans_lt hxab.2⟩
  have hbd : b = d := by
    apply le_antisymm
    · by_contra h
      have hdb : d < b := lt_of_not_ge h
      exact hab.2.2.2 d hcd.2.1
        ⟨by simpa [hac] using hxcd.1.trans_lt hxcd.2, hdb⟩
    · by_contra h
      have hbd : b < d := lt_of_not_ge h
      exact hcd.2.2.2 b hab.2.1
        ⟨by simpa [hac] using hxab.1.trans_lt hxab.2, hbd⟩
  exact ⟨hac, hbd⟩

private theorem adjacent_eq_of_right_eq_one (p : RealPartition)
    {a b c d : ℝ} (hab : p.Adjacent a b) (hcd : p.Adjacent c d)
    (hb : b = 1) (hd : d = 1) : a = c ∧ b = d := by
  have hac : a = c := by
    apply le_antisymm
    · by_contra h
      have hca : c < a := lt_of_not_ge h
      exact hcd.2.2.2 a hab.1
        ⟨hca, by simpa [hb, hd] using hab.2.2.1⟩
    · by_contra h
      have hac : a < c := lt_of_not_ge h
      exact hab.2.2.2 c hcd.1
        ⟨hac, by simpa [hb, hd] using hcd.2.2.1⟩
  exact ⟨hac, hb.trans hd.symm⟩

/-- Distinct assigned lap cells are disjoint. -/
theorem assignedCells_disjoint (p : RealPartition) {q r : p.LapIndex}
    (hqr : q ≠ r) : Disjoint q.assignedCell r.assignedCell := by
  rw [Set.disjoint_left]
  intro x hxq hxr
  apply hqr
  apply Subtype.ext
  apply Prod.ext
  · by_cases hxone : x = rightEndpoint
    · have hqone : q.right = 1 := by
        by_contra h
        have hxq' : (x : ℝ) ∈ Set.Ico q.left q.right := by
          simpa [RealPartition.LapIndex.assignedCell, h] using hxq
        have hright_le : q.right ≤ 1 :=
          (p.points_subset q.adjacent.2.1).2
        have hxreal : (x : ℝ) = 1 := congrArg Subtype.val hxone
        exact (not_lt_of_ge hright_le) (by simpa [hxreal] using hxq'.2)
      have hrone : r.right = 1 := by
        by_contra h
        have hxr' : (x : ℝ) ∈ Set.Ico r.left r.right := by
          simpa [RealPartition.LapIndex.assignedCell, h] using hxr
        have hright_le : r.right ≤ 1 :=
          (p.points_subset r.adjacent.2.1).2
        have hxreal : (x : ℝ) = 1 := congrArg Subtype.val hxone
        exact (not_lt_of_ge hright_le) (by simpa [hxreal] using hxr'.2)
      exact (adjacent_eq_of_right_eq_one p q.adjacent r.adjacent
        hqone hrone).1
    · have hxlt : (x : ℝ) < 1 :=
        lt_of_le_of_ne x.property.2 (fun h => hxone (Subtype.ext h))
      have hqx : q.left ≤ (x : ℝ) ∧ (x : ℝ) < q.right := by
        by_cases h : q.right = 1
        · have hxq' : (x : ℝ) ∈ Set.Icc q.left q.right := by
            simpa [RealPartition.LapIndex.assignedCell, h] using hxq
          exact ⟨hxq'.1, by simpa [h] using hxlt⟩
        · simpa [RealPartition.LapIndex.assignedCell, h] using hxq
      have hrx : r.left ≤ (x : ℝ) ∧ (x : ℝ) < r.right := by
        by_cases h : r.right = 1
        · have hxr' : (x : ℝ) ∈ Set.Icc r.left r.right := by
            simpa [RealPartition.LapIndex.assignedCell, h] using hxr
          exact ⟨hxr'.1, by simpa [h] using hxlt⟩
        · simpa [RealPartition.LapIndex.assignedCell, h] using hxr
      exact (adjacent_eq_of_common_Ico p q.adjacent r.adjacent hqx hrx).1
  · by_cases hxone : x = rightEndpoint
    · have hqone : q.right = 1 := by
        by_contra h
        have hxq' : (x : ℝ) ∈ Set.Ico q.left q.right := by
          simpa [RealPartition.LapIndex.assignedCell, h] using hxq
        have hright_le : q.right ≤ 1 :=
          (p.points_subset q.adjacent.2.1).2
        have hxreal : (x : ℝ) = 1 := congrArg Subtype.val hxone
        exact (not_lt_of_ge hright_le) (by simpa [hxreal] using hxq'.2)
      have hrone : r.right = 1 := by
        by_contra h
        have hxr' : (x : ℝ) ∈ Set.Ico r.left r.right := by
          simpa [RealPartition.LapIndex.assignedCell, h] using hxr
        have hright_le : r.right ≤ 1 :=
          (p.points_subset r.adjacent.2.1).2
        have hxreal : (x : ℝ) = 1 := congrArg Subtype.val hxone
        exact (not_lt_of_ge hright_le) (by simpa [hxreal] using hxr'.2)
      exact (adjacent_eq_of_right_eq_one p q.adjacent r.adjacent
        hqone hrone).2
    · have hxlt : (x : ℝ) < 1 :=
        lt_of_le_of_ne x.property.2 (fun h => hxone (Subtype.ext h))
      have hqx : q.left ≤ (x : ℝ) ∧ (x : ℝ) < q.right := by
        by_cases h : q.right = 1
        · have hxq' : (x : ℝ) ∈ Set.Icc q.left q.right := by
            simpa [RealPartition.LapIndex.assignedCell, h] using hxq
          exact ⟨hxq'.1, by simpa [h] using hxlt⟩
        · simpa [RealPartition.LapIndex.assignedCell, h] using hxq
      have hrx : r.left ≤ (x : ℝ) ∧ (x : ℝ) < r.right := by
        by_cases h : r.right = 1
        · have hxr' : (x : ℝ) ∈ Set.Icc r.left r.right := by
            simpa [RealPartition.LapIndex.assignedCell, h] using hxr
          exact ⟨hxr'.1, by simpa [h] using hxlt⟩
        · simpa [RealPartition.LapIndex.assignedCell, h] using hxr
      exact (adjacent_eq_of_common_Ico p q.adjacent r.adjacent hqx hrx).2

end RealPartition

namespace FinitePieceMonotone

variable {T : IntervalMap}

/-- A continuous globally nondecreasing interval map is finite-piece
piecewise monotone. -/
theorem of_monotone (hcont : Continuous T) (hmono : Monotone T) :
    FinitePieceMonotone T := by
  classical
  apply of_partition hcont RealPartition.trivial
  intro a b hab
  exact Or.inl (hmono.monotoneOn _)

/-- A continuous globally nonincreasing interval map is finite-piece
piecewise monotone. -/
theorem of_antitone (hcont : Continuous T) (hanti : Antitone T) :
    FinitePieceMonotone T := by
  classical
  apply of_partition hcont RealPartition.trivial
  intro a b hab
  exact Or.inr (hanti.antitoneOn _)

end FinitePieceMonotone

/-! ## Refining monotonicity witnesses -/

namespace MonotonicityPartition

variable {T : IntervalMap}

/-- Regard the same map on a finer real partition. -/
def refine (w : MonotonicityPartition T) (fine : RealPartition)
    (hfine : fine.Refines w.partition) : MonotonicityPartition T where
  partition := fine
  weaklyMonotoneOn_cell := by
    intro a b hab
    obtain ⟨c, d, hcd, hsub⟩ := hfine.adjacent_subset hab
    exact (w.weaklyMonotoneOn_cell hcd).mono (fun _ hx => hsub hx)

/-- The map is weakly monotone on each assigned (disjoint) lap. -/
theorem weaklyMonotoneOn_assignedCell (w : MonotonicityPartition T)
    (q : w.partition.LapIndex) :
    IsWeaklyMonotoneOn T q.assignedCell := by
  exact (w.weaklyMonotoneOn_cell q.adjacent).mono
    q.assignedCell_subset_closedCell

end MonotonicityPartition

/-! ## Fibre frontiers and the composition refinement -/

/-- The ambient real fibre of an interval map. -/
def ambientFibre (T : IntervalMap) (y : I) : Set ℝ :=
  {x | ∃ hx : x ∈ I, T ⟨x, hx⟩ = y}

private theorem frontier_finite_of_ordConnected_pm
    {s : Set ℝ} (hord : s.OrdConnected)
    (hbelow : BddBelow s) (habove : BddAbove s) :
    (frontier s).Finite := by
  by_cases hne : s.Nonempty
  · apply ((Set.finite_singleton (sSup s)).insert (sInf s)).subset
    intro x hx
    have hxclosure : x ∈ closure s := frontier_subset_closure hx
    have hxIcc : x ∈ Set.Icc (sInf s) (sSup s) :=
      closure_minimal (subset_Icc_csInf_csSup hbelow habove) isClosed_Icc hxclosure
    by_contra hxpair
    have hinf_ne : sInf s ≠ x := by
      intro h
      exact hxpair (by simp [h])
    have hsup_ne : x ≠ sSup s := by
      intro h
      exact hxpair (by simp [h])
    have hinf_lt : sInf s < x := lt_of_le_of_ne hxIcc.1 hinf_ne
    have hlt_sup : x < sSup s := lt_of_le_of_ne hxIcc.2 hsup_ne
    obtain ⟨u, hu, hux⟩ := (csInf_lt_iff hbelow hne).mp hinf_lt
    obtain ⟨v, hv, hxv⟩ := (lt_csSup_iff habove hne).mp hlt_sup
    have hIoo_subset : Set.Ioo u v ⊆ s := by
      intro z hz
      exact hord.out hu hv ⟨hz.1.le, hz.2.le⟩
    have hxmem : x ∈ s := hIoo_subset ⟨hux, hxv⟩
    have hxinterior : x ∈ interior s :=
      (isOpen_Ioo.subset_interior_iff.mpr hIoo_subset) ⟨hux, hxv⟩
    exact (mem_frontier_iff_notMem_interior hxmem).mp hx hxinterior
  · have hs : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [hs]

private theorem frontier_finite_iUnion_fintype_pm
    {ι : Type*} [Fintype ι] (pieces : ι → Set ℝ)
    (hpieces : ∀ i, (frontier (pieces i)).Finite) :
    (frontier (⋃ i, pieces i)).Finite := by
  classical
  have haux : ∀ q : Finset ι,
      (frontier (⋃ i ∈ q, pieces i)).Finite := by
    intro q
    induction q using Finset.induction_on with
    | empty => simp
    | @insert a q ha ih =>
        rw [Finset.set_biUnion_insert]
        apply ((hpieces a).union ih).subset
        intro x hx
        rcases frontier_union_subset (pieces a) (⋃ i ∈ q, pieces i) hx with hx | hx
        · exact Or.inl hx.1
        · exact Or.inr hx.2
  simpa using haux Finset.univ

/-- A fibre of a finite-piece weakly monotone map has finite frontier. -/
theorem MonotonicityPartition.finite_frontier_ambientFibre
    {T : IntervalMap} (w : MonotonicityPartition T) (y : I) :
    (frontier (ambientFibre T y)).Finite := by
  classical
  let piece : w.partition.LapIndex → Set ℝ := fun q =>
    {x | ∃ hxI : x ∈ I,
      x ∈ Set.Icc q.left q.right ∧ T ⟨x, hxI⟩ = y}
  have hunion : ambientFibre T y = ⋃ q, piece q := by
    ext x
    constructor
    · rintro ⟨hxI, hTx⟩
      obtain ⟨a, b, hab, hxcell⟩ :=
        w.partition.exists_adjacent_containing (⟨x, hxI⟩ : I)
      have hpair : (a, b) ∈ w.partition.adjacentPairs := by
        rw [RealPartition.adjacentPairs]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩
      let q : w.partition.LapIndex := ⟨(a, b), hpair⟩
      apply Set.mem_iUnion.mpr
      refine ⟨q, hxI, ?_, hTx⟩
      exact hxcell
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨q, hxI, _hxcell, hTx⟩
      exact ⟨hxI, hTx⟩
  rw [hunion]
  apply frontier_finite_iUnion_fintype_pm piece
  intro q
  apply frontier_finite_of_ordConnected_pm
  · refine ⟨?_⟩
    intro x hx z hz u huz
    rcases hx with ⟨hxI, hxcell, hTx⟩
    rcases hz with ⟨hzI, hzcell, hTz⟩
    have huI : u ∈ I :=
      ⟨hxI.1.trans huz.1, huz.2.trans hzI.2⟩
    let xI : I := ⟨x, hxI⟩
    let zI : I := ⟨z, hzI⟩
    let uI : I := ⟨u, huI⟩
    have hxcellI : xI ∈ intervalCell q.left q.right := hxcell
    have hzcellI : zI ∈ intervalCell q.left q.right := hzcell
    have hucell : u ∈ Set.Icc q.left q.right :=
      ⟨hxcell.1.trans huz.1, huz.2.trans hzcell.2⟩
    have hucellI : uI ∈ intervalCell q.left q.right := hucell
    have hxu : xI ≤ uI := huz.1
    have huz' : uI ≤ zI := huz.2
    have hTx' : T xI = y := by simpa [xI] using hTx
    have hTz' : T zI = y := by simpa [zI] using hTz
    refine ⟨huI, hucell, ?_⟩
    rcases w.weaklyMonotoneOn_cell q.adjacent with hmono | hanti
    · have hlo := hmono hxcellI hucellI hxu
      have hhi := hmono hucellI hzcellI huz'
      rw [hTx'] at hlo
      rw [hTz'] at hhi
      exact le_antisymm hhi hlo
    · have hhi := hanti hxcellI hucellI hxu
      have hlo := hanti hucellI hzcellI huz'
      rw [hTx'] at hhi
      rw [hTz'] at hlo
      exact le_antisymm hhi hlo
  · refine ⟨0, ?_⟩
    intro x hx
    exact hx.choose.1
  · refine ⟨1, ?_⟩
    intro x hx
    exact hx.choose.2

/-- All ambient fibre-frontier points still lie in `[0,1]`. -/
theorem frontier_ambientFibre_subset_I {T : IntervalMap} {y : I} :
    frontier (ambientFibre T y) ⊆ I := by
  apply frontier_subset_closure.trans
  apply closure_minimal
  · intro x hx
    exact hx.choose
  · exact isClosed_Icc

private theorem isClosed_ambientFibre_pm
    {T : IntervalMap} (y : I) (hT : Continuous T) :
    IsClosed (ambientFibre T y) := by
  have hclosed : IsClosed {x : I | T x = y} :=
    isClosed_eq hT continuous_const
  have himage : ambientFibre T y =
      ((↑) : I → ℝ) '' {x : I | T x = y} := by
    ext x
    constructor
    · rintro ⟨hx, hxy⟩
      exact ⟨⟨x, hx⟩, hxy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx⟩
  rw [himage]
  exact (hclosed.isCompact.image continuous_subtype_val).isClosed

private theorem Ioo_subset_of_mem_of_avoids_frontier_pm
    {s : Set ℝ} {a b x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo a b) (hx₀s : x₀ ∈ s)
    (havoid : ∀ x ∈ Set.Ioo a b, x ∉ frontier s) :
    Set.Ioo a b ⊆ s := by
  have hcover : Set.Ioo a b ⊆ interior s ∪ interior sᶜ := by
    intro x hx
    rw [← compl_frontier_eq_union_interior]
    exact havoid x hx
  have hdisjoint : Disjoint (interior s) (interior sᶜ) := by
    apply Set.disjoint_left.mpr
    intro x hxs hxsc
    exact (interior_subset hxsc) (interior_subset hxs)
  have hx₀interior : x₀ ∈ interior s :=
    (mem_interior_iff_notMem_frontier hx₀s).mpr (havoid x₀ hx₀)
  have hinter : (Set.Ioo a b ∩ interior s).Nonempty :=
    ⟨x₀, hx₀, hx₀interior⟩
  exact (ordConnected_Ioo.isPreconnected.subset_left_of_subset_union
    isOpen_interior isOpen_interior hdisjoint hcover hinter).trans interior_subset

/-- Refine the source partition at the finitely many frontier points of the
fibres above target vertices.  These are precisely the cuts needed for
composition in the presence of plateau intervals. -/
noncomputable def MonotonicityPartition.compositionRefinement
    {T U : IntervalMap} (wT : MonotonicityPartition T)
    (wU : MonotonicityPartition U) : RealPartition := by
  classical
  let fibreFrontier : {y : ℝ // y ∈ wU.partition.points} → Finset ℝ := fun y =>
    (wT.finite_frontier_ambientFibre
      (⟨y, wU.partition.points_subset y.property⟩ : I)).toFinset
  let boundaryPoints : Finset ℝ :=
    wU.partition.points.attach.biUnion fibreFrontier
  exact
    { points := wT.partition.points ∪ boundaryPoints
      zero_mem := by simp [wT.partition.zero_mem]
      one_mem := by simp [wT.partition.one_mem]
      points_subset := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact wT.partition.points_subset hx
        · rcases Finset.mem_biUnion.mp hx with ⟨y, _hy, hxy⟩
          apply frontier_ambientFibre_subset_I
          exact (wT.finite_frontier_ambientFibre
            (⟨y, wU.partition.points_subset y.property⟩ : I)).mem_toFinset.mp
              (by simpa [fibreFrontier] using hxy) }

theorem MonotonicityPartition.compositionRefinement_refines
    {T U : IntervalMap} (wT : MonotonicityPartition T)
    (wU : MonotonicityPartition U) :
    (wT.compositionRefinement wU).Refines wT.partition := by
  classical
  intro x hx
  simp only [MonotonicityPartition.compositionRefinement]
  exact Finset.mem_union_left _ hx

/-- On each cell of the composition refinement, `T` is weakly monotone and
its image is contained in one closed monotonicity cell of `U` (the constant
case at a target vertex is included). -/
theorem MonotonicityPartition.composition_cell
    {T U : IntervalMap} (hTcont : Continuous T)
    (wT : MonotonicityPartition T) (wU : MonotonicityPartition U)
    {a b : ℝ} (hab : (wT.compositionRefinement wU).Adjacent a b) :
    IsWeaklyMonotoneOn T (intervalCell a b) ∧
      ∃ c d : ℝ, wU.partition.Adjacent c d ∧
        MapsTo T (intervalCell a b) (intervalCell c d) := by
  classical
  have haI : a ∈ I :=
    (wT.compositionRefinement wU).points_subset hab.1
  have hbI : b ∈ I :=
    (wT.compositionRefinement wU).points_subset hab.2.1
  have hablt : a < b := hab.2.2.1
  have hsource : Set.Icc a b ⊆ I := by
    intro x hx
    exact ⟨haI.1.trans hx.1, hx.2.trans hbI.2⟩
  have hTweak : IsWeaklyMonotoneOn T (intervalCell a b) :=
    (wT.refine (wT.compositionRefinement wU)
      (wT.compositionRefinement_refines wU)).weaklyMonotoneOn_cell hab
  let m : ℝ := (a + b) / 2
  have hm : m ∈ Set.Ioo a b := by
    dsimp [m]
    constructor <;> linarith
  have hmI : m ∈ I := hsource ⟨hm.1.le, hm.2.le⟩
  let x₀ : I := ⟨m, hmI⟩
  have havoid (y : {z : ℝ // z ∈ wU.partition.points}) :
      ∀ x ∈ Set.Ioo a b,
        x ∉ frontier (ambientFibre T
          (⟨y, wU.partition.points_subset y.property⟩ : I)) := by
    intro x hx hxf
    apply hab.2.2.2 x
    · simp only [MonotonicityPartition.compositionRefinement]
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨y, by simp, ?_⟩
      exact (wT.finite_frontier_ambientFibre
        (⟨y, wU.partition.points_subset y.property⟩ : I)).mem_toFinset.mpr hxf
    · exact hx
  have hfibre_dichotomy
      (y : {z : ℝ // z ∈ wU.partition.points}) :
      (∀ x : I, (x : ℝ) ∈ Set.Icc a b →
        T x = (⟨y, wU.partition.points_subset y.property⟩ : I)) ∨
      (∀ x : I, (x : ℝ) ∈ Set.Ioo a b →
        T x ≠ (⟨y, wU.partition.points_subset y.property⟩ : I)) := by
    let yI : I := ⟨y, wU.partition.points_subset y.property⟩
    by_cases hmid : T x₀ = yI
    · left
      have hmFibre : m ∈ ambientFibre T yI := ⟨hmI, hmid⟩
      have hopen : Set.Ioo a b ⊆ ambientFibre T yI :=
        Ioo_subset_of_mem_of_avoids_frontier_pm hm hmFibre (havoid y)
      have hclosure : closure (Set.Ioo a b) ⊆ ambientFibre T yI :=
        closure_minimal hopen (isClosed_ambientFibre_pm yI hTcont)
      rw [closure_Ioo hablt.ne] at hclosure
      intro x hx
      rcases hclosure hx with ⟨hxI, hxy⟩
      have heq : (⟨(x : ℝ), hxI⟩ : I) = x := Subtype.ext rfl
      simpa [yI, heq] using hxy
    · right
      intro x hx hxy
      have hxFibre : (x : ℝ) ∈ ambientFibre T yI :=
        ⟨x.property, hxy⟩
      have hopen : Set.Ioo a b ⊆ ambientFibre T yI :=
        Ioo_subset_of_mem_of_avoids_frontier_pm hx hxFibre (havoid y)
      rcases hopen hm with ⟨hmI', hmy⟩
      have heq : (⟨m, hmI'⟩ : I) = x₀ := Subtype.ext rfl
      exact hmid (by simpa [yI, heq] using hmy)
  by_cases hyvertex : (T x₀ : ℝ) ∈ wU.partition.points
  · let y : {z : ℝ // z ∈ wU.partition.points} :=
      ⟨(T x₀ : ℝ), hyvertex⟩
    rcases hfibre_dichotomy y with hconst | havoidMid
    · obtain ⟨c, d, hcd, hycell⟩ :=
        wU.partition.exists_adjacent_containing (T x₀)
      refine ⟨hTweak, c, d, hcd, ?_⟩
      intro x hx
      have hxeq : T x = T x₀ := by
        simpa [y] using hconst x hx
      rw [hxeq]
      exact hycell
    · exfalso
      apply havoidMid x₀ hm
      apply Subtype.ext
      rfl
  · have hylt : T x₀ < rightEndpoint := by
      by_contra h
      have hyeq : T x₀ = rightEndpoint :=
        le_antisymm (T x₀).property.2 (le_of_not_gt h)
      apply hyvertex
      simpa [hyeq, rightEndpoint] using wU.partition.one_mem
    obtain ⟨c, d, hUadj, hc, hd⟩ :=
      wU.partition.exists_adjacent_Ico hylt
    have hcstrict : c < (T x₀ : ℝ) := by
      apply lt_of_le_of_ne hc
      intro h
      apply hyvertex
      rw [← h]
      exact hUadj.1
    let cI : I := ⟨c, wU.partition.points_subset hUadj.1⟩
    let dI : I := ⟨d, wU.partition.points_subset hUadj.2.1⟩
    let cy : {z : ℝ // z ∈ wU.partition.points} := ⟨c, hUadj.1⟩
    let dy : {z : ℝ // z ∈ wU.partition.points} := ⟨d, hUadj.2.1⟩
    have hcne : ∀ x : I, (x : ℝ) ∈ Set.Ioo a b → T x ≠ cI := by
      rcases hfibre_dichotomy cy with hall | hnone
      · have hbad := congrArg Subtype.val
          (hall x₀ ⟨hm.1.le, hm.2.le⟩)
        exact False.elim ((ne_of_gt hcstrict) (by simpa [cI, cy] using hbad))
      · simpa [cI, cy] using hnone
    have hdne : ∀ x : I, (x : ℝ) ∈ Set.Ioo a b → T x ≠ dI := by
      rcases hfibre_dichotomy dy with hall | hnone
      · have hbad := congrArg Subtype.val
          (hall x₀ ⟨hm.1.le, hm.2.le⟩)
        exact False.elim ((ne_of_lt hd) (by simpa [dI, dy] using hbad))
      · simpa [dI, dy] using hnone
    let aI : I := ⟨a, haI⟩
    let bI : I := ⟨b, hbI⟩
    have habI : aI < bI := hablt
    have hmx₀ : x₀ ∈ Set.Ioo aI bI := hm
    have hcne' : ∀ x ∈ Set.Ioo aI bI, T x ≠ cI := by
      intro x hx
      exact hcne x hx
    have hdne' : ∀ x ∈ Set.Ioo aI bI, T x ≠ dI := by
      intro x hx
      exact hdne x hx
    have hlower : MapsTo T (Set.Ioo aI bI) (Set.Ioi cI) :=
      (ordConnected_Ioo.isPreconnected.mapsTo_Ioi_or_Iio
        hTcont.continuousOn hcne').resolve_right (fun h =>
          (not_lt_of_ge hc) (h hmx₀))
    have hupper : MapsTo T (Set.Ioo aI bI) (Set.Iio dI) :=
      (ordConnected_Ioo.isPreconnected.mapsTo_Ioi_or_Iio
        hTcont.continuousOn hdne').resolve_left (fun h =>
          (not_lt_of_ge hd.le) (h hmx₀))
    have hopenMaps : MapsTo T (Set.Ioo aI bI) (Set.Icc cI dI) := by
      intro x hx
      exact ⟨(hlower hx).le, (hupper hx).le⟩
    have hclosedPreimage : IsClosed (T ⁻¹' Set.Icc cI dI) :=
      isClosed_Icc.preimage hTcont
    have hclosedMaps : closure (Set.Ioo aI bI) ⊆ T ⁻¹' Set.Icc cI dI :=
      closure_minimal hopenMaps hclosedPreimage
    rw [closure_Ioo habI.ne] at hclosedMaps
    refine ⟨hTweak, c, d, hUadj, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Icc aI bI := hx
    exact hclosedMaps hx'

/-! ## Closure under composition -/

namespace FinitePieceMonotone

variable {T U : IntervalMap}

/-- Continuous finite-piece piecewise-monotone interval maps are closed
under composition, including when either map has plateau intervals. -/
theorem comp (hU : FinitePieceMonotone U) (hT : FinitePieceMonotone T) :
    FinitePieceMonotone (U ∘ T) := by
  rcases hT.2 with ⟨wT⟩
  rcases hU.2 with ⟨wU⟩
  apply of_partition (hU.1.comp hT.1) (wT.compositionRefinement wU)
  intro a b hab
  rcases wT.composition_cell hT.1 wU hab with
    ⟨hTcell, c, d, hUadj, hmaps⟩
  exact (wU.weaklyMonotoneOn_cell hUadj).comp hTcell hmaps

end FinitePieceMonotone

/-! ## Closure under iteration -/

namespace FinitePieceMonotone

/-- Continuous finite-piece piecewise-monotonicity is stable under iteration. -/
theorem iterateMap {T : IntervalMap} (hT : FinitePieceMonotone T) (n : ℕ) :
    FinitePieceMonotone (CommutingIntervalSimplified.iterateMap T n) := by
  induction n with
  | zero =>
      simpa [CommutingIntervalSimplified.iterateMap] using
        (FinitePieceMonotone.of_monotone continuous_id monotone_id)
  | succ n ih =>
      rw [show CommutingIntervalSimplified.iterateMap T (Nat.succ n) =
          T ∘ CommutingIntervalSimplified.iterateMap T n by
        exact Function.iterate_succ' T n]
      exact hT.comp ih

end FinitePieceMonotone

end CommutingIntervalSimplified

