import CommutingInterval.Basic
import CommutingInterval.DynamicsDefs
import CommutingInterval.QuotientDefs

/-!
# Finite fixed-component quotients for the piecewise-linear core

This module extracts the cumulative-length quotient construction and the four
fixed-component facts needed by `PiecewiseLinearCore`.
-/

namespace CommutingInterval

open Function Set Topology

/-- A set in `I` is a finite union of closed subintervals, with singleton
subintervals allowed. -/
def IsFiniteUnionClosedSubintervals (s : Set I) : Prop :=
  ∃ n : ℕ, ∃ pieces : Fin n → ClosedSubinterval,
    s = ⋃ i, (pieces i).carrier

namespace PLQuotientSupport

def StrictlyOrderedIntervalFamily {n : ℕ}
    (classes : Fin n → ClosedSubinterval) : Prop :=
  ∀ ⦃i j : Fin n⦄, i < j → (classes i).right < (classes j).left

/-- Total length removed by a finite family of interval classes. -/
def totalCollapsedLength {n : ℕ}
    (classes : Fin n → ClosedSubinterval) : ℝ :=
  ∑ i, (classes i).length

/-- The portion of `J` lying weakly to the left of `x`, measured in `ℝ`. -/
def removedLengthAt (J : ClosedSubinterval) (x : I) : ℝ :=
  min (max ((x : ℝ) - (J.left : ℝ)) 0) J.length

/-- The cumulative removed length weakly before `x`. -/
def cumulativeRemovedLength {n : ℕ}
    (classes : Fin n → ClosedSubinterval) (x : I) : ℝ :=
  ∑ i, removedLengthAt (classes i) x

/-- The real-valued normalized coordinate underlying the canonical quotient. -/
noncomputable def collapseCoordinateReal {n : ℕ}
    (classes : Fin n → ClosedSubinterval) (x : I) : ℝ :=
  ((x : ℝ) - cumulativeRemovedLength classes x) /
    (1 - totalCollapsedLength classes)

/-- Geometric order implies pairwise disjointness, including endpoints. -/
theorem strictlyOrderedIntervalFamily_pairwise_disjoint
    {n : ℕ} {classes : Fin n → ClosedSubinterval}
    (hordered : StrictlyOrderedIntervalFamily classes) :
    ∀ i j, i ≠ j → Disjoint (classes i).carrier (classes j).carrier := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact (not_lt_of_ge (hxj.1.trans hxi.2)) (hordered hij')
  · exact (not_lt_of_ge (hxi.1.trans hxj.2)) (hordered hji')

/-- The lengths of an ordered family contained in `[a,b]` fit inside its span. -/
private theorem sum_length_le_span_of_ordered
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : ∀ ⦃i j : Fin n⦄, i < j → (classes i).right ≤ (classes j).left)
    (a b : ℝ) (hab : a ≤ b)
    (ha : ∀ i, a ≤ (classes i).left)
    (hb : ∀ i, (classes i).right ≤ b) :
    (∑ i, (classes i).length) ≤ b - a := by
  induction n generalizing a b with
  | zero => simp; linarith
  | succ n ih =>
      let tail : Fin n → ClosedSubinterval := fun i => classes i.succ
      have htailOrdered :
          ∀ ⦃i j : Fin n⦄, i < j → (tail i).right ≤ (tail j).left := by
        intro i j hij
        exact hordered (Fin.succ_lt_succ_iff.mpr hij)
      have htailLeft : ∀ i, (classes 0).right ≤ (tail i).left := by
        intro i
        exact hordered (by simp)
      have htailRight : ∀ i, (tail i).right ≤ b := by
        intro i
        exact hb i.succ
      have hright0 : (classes 0).right ≤ b := hb 0
      have htail := ih tail htailOrdered (classes 0).right b hright0
        htailLeft htailRight
      rw [Fin.sum_univ_succ]
      change (classes 0).length + (∑ i, (tail i).length) ≤ b - a
      dsimp [ClosedSubinterval.length] at htail ⊢
      have hleft0 := ha 0
      linarith

/-- A proper ordered collapsed locus leaves strictly positive total length. -/
theorem totalCollapsedLength_lt_one_of_proper
    {n : ℕ} {classes : Fin n → ClosedSubinterval}
    (hordered : StrictlyOrderedIntervalFamily classes)
    (hproper : collapsedLocus classes ≠ Set.univ) :
    totalCollapsedLength classes < 1 := by
  cases n with
  | zero => simp [totalCollapsedLength]
  | succ n =>
      cases n with
      | zero =>
          rw [show totalCollapsedLength classes = (classes 0).length by
            simp [totalCollapsedLength, Fin.sum_univ_succ]]
          by_contra hnot
          have hlen : 1 ≤ (classes 0).length := le_of_not_gt hnot
          have hleft0 : 0 ≤ ((classes 0).left : ℝ) := (classes 0).left.property.1
          have hright1 : ((classes 0).right : ℝ) ≤ 1 := (classes 0).right.property.2
          have hleft : ((classes 0).left : ℝ) = 0 := by
            dsimp [ClosedSubinterval.length] at hlen
            linarith
          have hright : ((classes 0).right : ℝ) = 1 := by
            dsimp [ClosedSubinterval.length] at hlen
            linarith
          have hleftI : (classes 0).left = leftEndpoint := by
            apply Subtype.ext
            simpa [leftEndpoint] using hleft
          have hrightI : (classes 0).right = rightEndpoint := by
            apply Subtype.ext
            simpa [rightEndpoint] using hright
          apply hproper
          ext x
          simp only [collapsedLocus, Set.mem_iUnion, Set.mem_univ, iff_true]
          refine ⟨0, ?_⟩
          change (classes 0).left ≤ x ∧ x ≤ (classes 0).right
          rw [hleftI, hrightI]
          exact x.property
      | succ n =>
          let tail : Fin (n + 1) → ClosedSubinterval := fun i => classes i.succ
          have htailOrdered : StrictlyOrderedIntervalFamily tail := by
            intro i j hij
            exact hordered (Fin.succ_lt_succ_iff.mpr hij)
          let one : Fin (n + 2) := Fin.succ (0 : Fin (n + 1))
          have htailLeft : ∀ i, (classes one).left ≤ (tail i).left := by
            intro i
            by_cases hi : i = 0
            · subst i
              rfl
            · have hone_le_idx : one ≤ i.succ := by
                change (1 : ℕ) ≤ i.val + 1
                omega
              have hone_ne_idx : one ≠ i.succ := by
                intro heq
                apply hi
                exact Fin.succ_injective _ heq.symm
              have hone_lt : one < i.succ := lt_of_le_of_ne hone_le_idx hone_ne_idx
              exact (classes one).left_le_right.trans (hordered hone_lt).le
          have htailRight : ∀ i, (tail i).right ≤ (1 : ℝ) := by
            intro i
            exact (tail i).right.property.2
          have hone_le : ((classes one).left : ℝ) ≤ 1 :=
            (classes one).left.property.2
          have htailBound := sum_length_le_span_of_ordered tail
            (fun i j hij => (htailOrdered hij).le)
            (classes one).left 1 hone_le htailLeft htailRight
          have hgap : (classes 0).right < (classes one).left := by
            apply hordered
            simp [one]
          change ((classes 0).right : ℝ) < ((classes one).left : ℝ) at hgap
          have hleft0 : 0 ≤ ((classes 0).left : ℝ) :=
            (classes 0).left.property.1
          rw [show totalCollapsedLength classes =
              (classes 0).length + ∑ i, (tail i).length by
            simp [totalCollapsedLength, tail, Fin.sum_univ_succ]]
          dsimp [ClosedSubinterval.length] at htailBound ⊢
          linarith

/-- The part of `J` lying weakly to the left of `x`, with empty parts replaced by `{x}`. -/
private def leftTruncateInterval (J : ClosedSubinterval) (x : I) :
    ClosedSubinterval where
  left := min J.left x
  right := min J.right x
  left_le_right := min_le_min J.left_le_right le_rfl

/-- The part of `J` lying weakly to the right of `x`, with empty parts replaced by `{x}`. -/
private def rightTruncateInterval (J : ClosedSubinterval) (x : I) :
    ClosedSubinterval where
  left := max J.left x
  right := max J.right x
  left_le_right := max_le_max J.left_le_right le_rfl

/-- The part of `J` inside `[x,y]`, with empty parts replaced by an endpoint singleton. -/
private def segmentTruncateInterval (J : ClosedSubinterval)
    (x y : I) : ClosedSubinterval where
  left := max x (min J.left y)
  right := max x (min J.right y)
  left_le_right := max_le_max le_rfl (min_le_min J.left_le_right le_rfl)

private theorem removedLengthAt_of_le_left
    (J : ClosedSubinterval) {x : I} (hx : x ≤ J.left) :
    removedLengthAt J x = 0 := by
  have hsub : (x : ℝ) - (J.left : ℝ) ≤ 0 := sub_nonpos.mpr hx
  have hlen : 0 ≤ J.length := sub_nonneg.mpr J.left_le_right
  simp [removedLengthAt, max_eq_right hsub, min_eq_left hlen]

private theorem removedLengthAt_of_mem
    (J : ClosedSubinterval) {x : I} (hx : x ∈ J.carrier) :
    removedLengthAt J x = (x : ℝ) - (J.left : ℝ) := by
  have hzero : 0 ≤ (x : ℝ) - (J.left : ℝ) := sub_nonneg.mpr hx.1
  have hlen : (x : ℝ) - (J.left : ℝ) ≤ J.length := by
    dsimp [ClosedSubinterval.length]
    linarith [show (x : ℝ) ≤ (J.right : ℝ) from hx.2]
  simp [removedLengthAt, max_eq_left hzero, min_eq_left hlen]

private theorem removedLengthAt_of_right_le
    (J : ClosedSubinterval) {x : I} (hx : J.right ≤ x) :
    removedLengthAt J x = J.length := by
  have hzero : 0 ≤ (x : ℝ) - (J.left : ℝ) :=
    sub_nonneg.mpr (J.left_le_right.trans hx)
  have hlen : J.length ≤ (x : ℝ) - (J.left : ℝ) := by
    dsimp [ClosedSubinterval.length]
    linarith [show (J.right : ℝ) ≤ (x : ℝ) from hx]
  simp [removedLengthAt, max_eq_left hzero, min_eq_right hlen]

private theorem leftTruncateInterval_length
    (J : ClosedSubinterval) (x : I) :
    (leftTruncateInterval J x).length = removedLengthAt J x := by
  by_cases hxleft : x ≤ J.left
  · have hxright : x ≤ J.right := hxleft.trans J.left_le_right
    rw [removedLengthAt_of_le_left J hxleft]
    simp [leftTruncateInterval, ClosedSubinterval.length,
      min_eq_right hxleft, min_eq_right hxright]
  · have hleftx : J.left ≤ x := (lt_of_not_ge hxleft).le
    by_cases hxright : x ≤ J.right
    · rw [removedLengthAt_of_mem J ⟨hleftx, hxright⟩]
      simp [leftTruncateInterval, ClosedSubinterval.length,
        min_eq_left hleftx, min_eq_right hxright]
    · have hrightx : J.right ≤ x := (le_of_not_ge hxright)
      rw [removedLengthAt_of_right_le J hrightx]
      simp [leftTruncateInterval, min_eq_left hleftx,
        min_eq_left hrightx]

private theorem rightTruncateInterval_length
    (J : ClosedSubinterval) (x : I) :
    (rightTruncateInterval J x).length = J.length - removedLengthAt J x := by
  by_cases hxleft : x ≤ J.left
  · rw [removedLengthAt_of_le_left J hxleft]
    have hxright : x ≤ J.right := hxleft.trans J.left_le_right
    simp [rightTruncateInterval, max_eq_left hxleft, max_eq_left hxright]
  · have hleftx : J.left ≤ x := (lt_of_not_ge hxleft).le
    by_cases hxright : x ≤ J.right
    · rw [removedLengthAt_of_mem J ⟨hleftx, hxright⟩]
      simp [rightTruncateInterval, ClosedSubinterval.length,
        max_eq_right hleftx, max_eq_left hxright]
    · have hrightx : J.right ≤ x := le_of_not_ge hxright
      rw [removedLengthAt_of_right_le J hrightx]
      simp [rightTruncateInterval, ClosedSubinterval.length,
        max_eq_right hleftx, max_eq_right hrightx]

private theorem segmentTruncateInterval_length
    (J : ClosedSubinterval) {x y : I} (hxy : x ≤ y) :
    (segmentTruncateInterval J x y).length =
      removedLengthAt J y - removedLengthAt J x := by
  by_cases hyleft : y ≤ J.left
  · have hxleft : x ≤ J.left := hxy.trans hyleft
    rw [removedLengthAt_of_le_left J hyleft,
      removedLengthAt_of_le_left J hxleft]
    have hyright : y ≤ J.right := hyleft.trans J.left_le_right
    simp [segmentTruncateInterval, ClosedSubinterval.length,
      min_eq_right hyleft, min_eq_right hyright, max_eq_right hxy]
  · have hlefty : J.left ≤ y := (lt_of_not_ge hyleft).le
    by_cases hxright : J.right ≤ x
    · have hrighty : J.right ≤ y := hxright.trans hxy
      rw [removedLengthAt_of_right_le J hxright,
        removedLengthAt_of_right_le J hrighty]
      have hleftx : J.left ≤ x := J.left_le_right.trans hxright
      simp [segmentTruncateInterval, ClosedSubinterval.length,
        min_eq_left hlefty, min_eq_left hrighty,
        max_eq_left hleftx, max_eq_left hxright]
    · have hxright' : x ≤ J.right := le_of_not_ge hxright
      by_cases hyleftRight : y ≤ J.right
      · rw [removedLengthAt_of_mem J ⟨hlefty, hyleftRight⟩]
        by_cases hxleft : x ≤ J.left
        · rw [removedLengthAt_of_le_left J hxleft]
          simp [segmentTruncateInterval, ClosedSubinterval.length,
            min_eq_left hlefty, min_eq_right hyleftRight,
            max_eq_right hxleft, max_eq_right hxy]
        · have hleftx : J.left ≤ x := (lt_of_not_ge hxleft).le
          rw [removedLengthAt_of_mem J ⟨hleftx, hxright'⟩]
          simp [segmentTruncateInterval, ClosedSubinterval.length,
            min_eq_left hlefty, min_eq_right hyleftRight,
            max_eq_left hleftx, max_eq_right hxy]
      · have hrighty : J.right ≤ y := le_of_not_ge hyleftRight
        rw [removedLengthAt_of_right_le J hrighty]
        by_cases hxleft : x ≤ J.left
        · rw [removedLengthAt_of_le_left J hxleft]
          simp [segmentTruncateInterval, ClosedSubinterval.length,
            min_eq_left hlefty, min_eq_left hrighty,
            max_eq_right hxleft, max_eq_right hxright']
        · have hleftx : J.left ≤ x := (lt_of_not_ge hxleft).le
          rw [removedLengthAt_of_mem J ⟨hleftx, hxright'⟩]
          simp [segmentTruncateInterval, ClosedSubinterval.length,
            min_eq_left hlefty, min_eq_left hrighty,
            max_eq_left hleftx, max_eq_right hxright']

private theorem cumulativeRemovedLength_le
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes) (x : I) :
    cumulativeRemovedLength classes x ≤ (x : ℝ) := by
  let truncated : Fin n → ClosedSubinterval := fun i => leftTruncateInterval (classes i) x
  have htruncatedOrdered :
      ∀ ⦃i j : Fin n⦄, i < j → (truncated i).right ≤ (truncated j).left := by
    intro i j hij
    exact min_le_min (hordered hij).le le_rfl
  have hleft : ∀ i, (0 : ℝ) ≤ (truncated i).left := by
    intro i
    exact (truncated i).left.property.1
  have hright : ∀ i, (truncated i).right ≤ x := by
    intro i
    exact min_le_right _ _
  have hbound := sum_length_le_span_of_ordered truncated htruncatedOrdered
    0 x x.property.1 hleft hright
  rw [show cumulativeRemovedLength classes x = ∑ i, (truncated i).length by
    simp only [cumulativeRemovedLength]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (leftTruncateInterval_length (classes i) x).symm]
  simpa using hbound

private theorem total_sub_cumulativeRemovedLength_le
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes) (x : I) :
    totalCollapsedLength classes - cumulativeRemovedLength classes x ≤
      1 - (x : ℝ) := by
  let truncated : Fin n → ClosedSubinterval := fun i => rightTruncateInterval (classes i) x
  have htruncatedOrdered :
      ∀ ⦃i j : Fin n⦄, i < j → (truncated i).right ≤ (truncated j).left := by
    intro i j hij
    exact max_le_max (hordered hij).le le_rfl
  have hleft : ∀ i, x ≤ (truncated i).left := by
    intro i
    exact le_max_right _ _
  have hright : ∀ i, (truncated i).right ≤ (1 : ℝ) := by
    intro i
    exact (truncated i).right.property.2
  have hbound := sum_length_le_span_of_ordered truncated htruncatedOrdered
    x 1 x.property.2 hleft hright
  rw [show totalCollapsedLength classes - cumulativeRemovedLength classes x =
      ∑ i, (truncated i).length by
    simp only [totalCollapsedLength, cumulativeRemovedLength,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (rightTruncateInterval_length (classes i) x).symm]
  simpa using hbound

private theorem cumulativeRemovedLength_sub_le
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    {x y : I} (hxy : x ≤ y) :
    cumulativeRemovedLength classes y - cumulativeRemovedLength classes x ≤
      (y : ℝ) - (x : ℝ) := by
  let truncated : Fin n → ClosedSubinterval :=
    fun i => segmentTruncateInterval (classes i) x y
  have htruncatedOrdered :
      ∀ ⦃i j : Fin n⦄, i < j → (truncated i).right ≤ (truncated j).left := by
    intro i j hij
    exact max_le_max le_rfl (min_le_min (hordered hij).le le_rfl)
  have hleft : ∀ i, x ≤ (truncated i).left := by
    intro i
    exact le_max_left _ _
  have hright : ∀ i, (truncated i).right ≤ y := by
    intro i
    exact max_le hxy (min_le_right _ _)
  have hbound := sum_length_le_span_of_ordered truncated htruncatedOrdered
    x y hxy hleft hright
  rw [show cumulativeRemovedLength classes y - cumulativeRemovedLength classes x =
      ∑ i, (truncated i).length by
    simp only [cumulativeRemovedLength, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (segmentTruncateInterval_length (classes i) hxy).symm]
  simpa using hbound

/-- Equality in the ordered length bound forces the interval interior to be covered. -/
private theorem Ioo_subset_iUnion_of_sum_length_eq
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : ∀ ⦃i j : Fin n⦄, i < j → (classes i).right ≤ (classes j).left)
    (a b : I) (hab : a ≤ b)
    (ha : ∀ i, a ≤ (classes i).left)
    (hb : ∀ i, (classes i).right ≤ b)
    (heq : (∑ i, (classes i).length) = (b : ℝ) - (a : ℝ)) :
    Set.Ioo a b ⊆ ⋃ i, (classes i).carrier := by
  induction n generalizing a b with
  | zero =>
      intro z hz
      have hab' : a < b := hz.1.trans hz.2
      have heq' : (0 : ℝ) = (b : ℝ) - (a : ℝ) := by simpa using heq
      have : (0 : ℝ) < (b : ℝ) - (a : ℝ) := sub_pos.mpr hab'
      linarith
  | succ n ih =>
      let tail : Fin n → ClosedSubinterval := fun i => classes i.succ
      have htailOrdered :
          ∀ ⦃i j : Fin n⦄, i < j → (tail i).right ≤ (tail j).left := by
        intro i j hij
        exact hordered (Fin.succ_lt_succ_iff.mpr hij)
      have htailLeft : ∀ i, (classes 0).right ≤ (tail i).left := by
        intro i
        exact hordered (by simp)
      have htailRight : ∀ i, (tail i).right ≤ b := fun i => hb i.succ
      have hright0 : (classes 0).right ≤ b := hb 0
      have htailBound := sum_length_le_span_of_ordered tail htailOrdered
        (classes 0).right b hright0 htailLeft htailRight
      rw [Fin.sum_univ_succ] at heq
      have hleft0 : a ≤ (classes 0).left := ha 0
      change (a : ℝ) ≤ ((classes 0).left : ℝ) at hleft0
      have htailEq : (∑ i, (tail i).length) =
          (b : ℝ) - ((classes 0).right : ℝ) := by
        change (classes 0).length + (∑ i, (tail i).length) =
          (b : ℝ) - (a : ℝ) at heq
        dsimp [ClosedSubinterval.length] at heq htailBound
        apply le_antisymm htailBound
        linarith
      have hleftEq : (classes 0).left = a := by
        apply Subtype.ext
        change ((classes 0).left : ℝ) = (a : ℝ)
        change (classes 0).length + (∑ i, (tail i).length) =
          (b : ℝ) - (a : ℝ) at heq
        dsimp [ClosedSubinterval.length] at heq htailBound
        linarith
      have htailCover := ih tail htailOrdered (classes 0).right b hright0
        htailLeft htailRight htailEq
      intro z hz
      by_cases hzright : z ≤ (classes 0).right
      · apply Set.mem_iUnion.mpr
        refine ⟨0, ?_⟩
        exact ⟨hleftEq.trans_le hz.1.le, hzright⟩
      · have hzTail : z ∈ Set.Ioo (classes 0).right b :=
          ⟨lt_of_not_ge hzright, hz.2⟩
        rcases Set.mem_iUnion.mp (htailCover hzTail) with ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i.succ, hi⟩

private theorem segmentTruncateInterval_mem_original_of_mem_Ioo
    (J : ClosedSubinterval) {x y z : I}
    (hzxy : z ∈ Set.Ioo x y)
    (hz : z ∈ (segmentTruncateInterval J x y).carrier) :
    z ∈ J.carrier := by
  have hleft : J.left ≤ z := by
    by_cases hlefty : J.left ≤ y
    · have hmin : min J.left y = J.left := min_eq_left hlefty
      have := hz.1
      simp only [segmentTruncateInterval, hmin] at this
      exact (le_max_right x J.left).trans this
    · have hyleft : y ≤ J.left := le_of_not_ge hlefty
      have hyz : y ≤ z := by
        have hzleft := hz.1
        simp only [segmentTruncateInterval, min_eq_right hyleft] at hzleft
        have hmax : max x y = y :=
          max_eq_right (hzxy.1.le.trans hzxy.2.le)
        rw [hmax] at hzleft
        exact hzleft
      exact False.elim ((not_le_of_gt hzxy.2) hyz)
  have hright : z ≤ J.right := by
    by_cases hrighty : J.right ≤ y
    · have hmin : min J.right y = J.right := min_eq_left hrighty
      have hzmax := hz.2
      simp only [segmentTruncateInterval, hmin] at hzmax
      rcases max_cases x J.right with hmax | hmax
      · rw [hmax.1] at hzmax
        exact False.elim ((not_le_of_gt hzxy.1) hzmax)
      · rwa [hmax.1] at hzmax
    · exact hzxy.2.le.trans (le_of_not_ge hrighty)
  exact ⟨hleft, hright⟩

private theorem isClosed_collapsedLocus
    {n : ℕ} (classes : Fin n → ClosedSubinterval) :
    IsClosed (collapsedLocus classes) := by
  exact isClosed_iUnion_of_finite (fun _ => isClosed_Icc)

private theorem same_class_of_Icc_subset_collapsedLocus
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    {x y : I} (hxy : x ≤ y)
    (hcover : Set.Icc x y ⊆ collapsedLocus classes) :
    ∃ i, x ∈ (classes i).carrier ∧ y ∈ (classes i).carrier := by
  let S : Set I := Set.Icc x y
  let K := {i : Fin n // (S ∩ (classes i).carrier).Nonempty}
  let pieces : K → Set S := fun k => {z | (z : I) ∈ (classes k.1).carrier}
  letI : PreconnectedSpace S := Subtype.preconnectedSpace isPreconnected_Icc
  have hpiecesNonempty : ∀ k, (pieces k).Nonempty := by
    intro k
    rcases k.property with ⟨z, hzS, hzk⟩
    exact ⟨⟨z, hzS⟩, hzk⟩
  have hpiecesDisjoint : Pairwise (Disjoint on pieces) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro z hzk hzl
    have hindex : k.1 ≠ l.1 := by
      intro h
      apply hkl
      exact Subtype.ext h
    exact (Set.disjoint_left.mp
      (strictlyOrderedIntervalFamily_pairwise_disjoint hordered k.1 l.1 hindex)) hzk hzl
  have hpiecesClosed : ∀ k, IsClosed (pieces k) := by
    intro k
    exact isClosed_Icc.preimage continuous_subtype_val
  have hpiecesUnion : ⋃ k, pieces k = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hz := hcover z.property
    rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
    let k : K := ⟨i, ⟨z, z.property, hi⟩⟩
    exact ⟨k, hi⟩
  have hKsubsingleton : Subsingleton K :=
    subsingleton_of_disjoint_isClosed_iUnion_eq_univ
      hpiecesNonempty hpiecesDisjoint hpiecesClosed hpiecesUnion
  have hxcover := hcover (Set.left_mem_Icc.mpr hxy)
  have hycover := hcover (Set.right_mem_Icc.mpr hxy)
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  rcases Set.mem_iUnion.mp hycover with ⟨j, hyj⟩
  let ki : K := ⟨i, ⟨x, Set.left_mem_Icc.mpr hxy, hxi⟩⟩
  let kj : K := ⟨j, ⟨y, Set.right_mem_Icc.mpr hxy, hyj⟩⟩
  have hij : i = j := congrArg Subtype.val (hKsubsingleton.elim ki kj)
  subst j
  exact ⟨i, hxi, hyj⟩

/-- The normalized cumulative-length coordinate takes values in `[0,1]`. -/
theorem collapseCoordinateReal_mem_unitInterval
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) (x : I) :
    collapseCoordinateReal classes x ∈ Set.Icc (0 : ℝ) 1 := by
  have hden : 0 < 1 - totalCollapsedLength classes := sub_pos.mpr htotal
  have hlower := cumulativeRemovedLength_le classes hordered x
  have hupper := total_sub_cumulativeRemovedLength_le classes hordered x
  constructor
  · apply div_nonneg
    · linarith
    · exact hden.le
  · apply (div_le_one hden).mpr
    linarith

/-- The canonical interval map obtained by deleting the displayed lengths. -/
noncomputable def canonicalCollapseMap
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) : IntervalMap :=
  fun x =>
    ⟨collapseCoordinateReal classes x,
      collapseCoordinateReal_mem_unitInterval classes hordered htotal x⟩

/-- The explicit collapse coordinate is continuous. -/
theorem canonicalCollapseMap_continuous
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) :
    Continuous (canonicalCollapseMap classes hordered htotal) := by
  have hremoved (i : Fin n) : Continuous (fun x : I => removedLengthAt (classes i) x) := by
    unfold removedLengthAt
    exact ((continuous_subtype_val.sub continuous_const).max continuous_const).min
      continuous_const
  have hsum : Continuous (fun x : I => cumulativeRemovedLength classes x) := by
    unfold cumulativeRemovedLength
    fun_prop
  apply Continuous.subtype_mk
  unfold collapseCoordinateReal
  fun_prop

/-- The explicit collapse coordinate is nondecreasing. -/
theorem canonicalCollapseMap_monotone
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) :
    Monotone (canonicalCollapseMap classes hordered htotal) := by
  intro x y hxy
  apply Subtype.coe_le_coe.mp
  change ((x : ℝ) - cumulativeRemovedLength classes x) /
      (1 - totalCollapsedLength classes) ≤
    ((y : ℝ) - cumulativeRemovedLength classes y) /
      (1 - totalCollapsedLength classes)
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr htotal.le)
  have hremoved := cumulativeRemovedLength_sub_le classes hordered hxy
  linarith

/-- The explicit collapse coordinate fixes the left ambient endpoint. -/
theorem canonicalCollapseMap_leftEndpoint
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) :
    canonicalCollapseMap classes hordered htotal leftEndpoint = leftEndpoint := by
  apply Subtype.ext
  change collapseCoordinateReal classes leftEndpoint = 0
  have hremoved : cumulativeRemovedLength classes leftEndpoint = 0 := by
    unfold cumulativeRemovedLength
    apply Finset.sum_eq_zero
    intro i _hi
    apply removedLengthAt_of_le_left
    exact (classes i).left.property.1
  rw [collapseCoordinateReal, hremoved]
  simp [leftEndpoint]

/-- The explicit collapse coordinate fixes the right ambient endpoint. -/
theorem canonicalCollapseMap_rightEndpoint
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) :
    canonicalCollapseMap classes hordered htotal rightEndpoint = rightEndpoint := by
  apply Subtype.ext
  change collapseCoordinateReal classes rightEndpoint = 1
  have hremoved :
      cumulativeRemovedLength classes rightEndpoint = totalCollapsedLength classes := by
    unfold cumulativeRemovedLength totalCollapsedLength
    apply Finset.sum_congr rfl
    intro i _hi
    apply removedLengthAt_of_right_le
    exact (classes i).right.property.2
  rw [collapseCoordinateReal, hremoved]
  change (1 - totalCollapsedLength classes) /
      (1 - totalCollapsedLength classes) = 1
  exact div_self (sub_ne_zero.mpr htotal.ne')

/-- The explicit collapse coordinate is onto the unit interval. -/
theorem canonicalCollapseMap_surjective
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) :
    Function.Surjective (canonicalCollapseMap classes hordered htotal) := by
  intro y
  apply intermediate_value_univ leftEndpoint rightEndpoint
    (canonicalCollapseMap_continuous classes hordered htotal)
  rw [canonicalCollapseMap_leftEndpoint classes hordered htotal,
    canonicalCollapseMap_rightEndpoint classes hordered htotal]
  exact y.property

/-- Exact fibres of the cumulative-length collapse coordinate. -/
theorem canonicalCollapseMap_fibre_iff
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (hnondegenerate : ∀ i, (classes i).Nondegenerate)
    (htotal : totalCollapsedLength classes < 1) (x y : I) :
    canonicalCollapseMap classes hordered htotal x =
        canonicalCollapseMap classes hordered htotal y ↔
      x = y ∨ ∃ i, x ∈ (classes i).carrier ∧ y ∈ (classes i).carrier := by
  have sameClass_of_lt {u v : I} (huv : u < v)
      (hq : canonicalCollapseMap classes hordered htotal u =
        canonicalCollapseMap classes hordered htotal v) :
      ∃ i, u ∈ (classes i).carrier ∧ v ∈ (classes i).carrier := by
    have hqreal := congrArg Subtype.val hq
    change collapseCoordinateReal classes u = collapseCoordinateReal classes v at hqreal
    unfold collapseCoordinateReal at hqreal
    have hden : 1 - totalCollapsedLength classes ≠ 0 :=
      sub_ne_zero.mpr htotal.ne'
    have hnum := (div_left_inj' hden).mp hqreal
    have hcum :
        cumulativeRemovedLength classes v - cumulativeRemovedLength classes u =
          (v : ℝ) - (u : ℝ) := by
      linarith
    let truncated : Fin n → ClosedSubinterval :=
      fun i => segmentTruncateInterval (classes i) u v
    have htruncatedOrdered :
        ∀ ⦃i j : Fin n⦄, i < j → (truncated i).right ≤ (truncated j).left := by
      intro i j hij
      exact max_le_max le_rfl (min_le_min (hordered hij).le le_rfl)
    have hleft : ∀ i, u ≤ (truncated i).left := by
      intro i
      exact le_max_left _ _
    have hright : ∀ i, (truncated i).right ≤ v := by
      intro i
      exact max_le huv.le (min_le_right _ _)
    have hsum : (∑ i, (truncated i).length) = (v : ℝ) - (u : ℝ) := by
      calc
        (∑ i, (truncated i).length) =
            ∑ i, (removedLengthAt (classes i) v - removedLengthAt (classes i) u) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact segmentTruncateInterval_length (classes i) huv.le
        _ = cumulativeRemovedLength classes v - cumulativeRemovedLength classes u := by
          simp [cumulativeRemovedLength, Finset.sum_sub_distrib]
        _ = (v : ℝ) - (u : ℝ) := hcum
    have hinteriorTruncated := Ioo_subset_iUnion_of_sum_length_eq
      truncated htruncatedOrdered u v huv.le hleft hright hsum
    have hinterior : Set.Ioo u v ⊆ collapsedLocus classes := by
      intro z hz
      rcases Set.mem_iUnion.mp (hinteriorTruncated hz) with ⟨i, hzi⟩
      exact Set.mem_iUnion.mpr
        ⟨i, segmentTruncateInterval_mem_original_of_mem_Ioo (classes i) hz hzi⟩
    have hclosure : closure (Set.Ioo u v) ⊆ collapsedLocus classes :=
      closure_minimal hinterior (isClosed_collapsedLocus classes)
    have hcover : Set.Icc u v ⊆ collapsedLocus classes := by
      rw [closure_Ioo huv.ne] at hclosure
      exact hclosure
    exact same_class_of_Icc_subset_collapsedLocus classes hordered huv.le hcover
  have map_eq_of_same_class_of_le (i : Fin n) {u v : I}
      (hu : u ∈ (classes i).carrier) (hv : v ∈ (classes i).carrier)
      (huv : u ≤ v) :
      canonicalCollapseMap classes hordered htotal u =
        canonicalCollapseMap classes hordered htotal v := by
    have hdiff :
        cumulativeRemovedLength classes v - cumulativeRemovedLength classes u =
          (v : ℝ) - (u : ℝ) := by
      rw [cumulativeRemovedLength, cumulativeRemovedLength,
        ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single i]
      · rw [removedLengthAt_of_mem (classes i) hv,
          removedLengthAt_of_mem (classes i) hu]
        ring
      · intro j _hj hji
        rcases lt_or_gt_of_ne hji with hji' | hij'
        · have hjrightu : (classes j).right ≤ u :=
            (hordered hji').le.trans hu.1
          rw [removedLengthAt_of_right_le (classes j) hjrightu,
            removedLengthAt_of_right_le (classes j) (hjrightu.trans huv)]
          ring
        · have hvleftj : v ≤ (classes j).left :=
            hv.2.trans (hordered hij').le
          rw [removedLengthAt_of_le_left (classes j) hvleftj,
            removedLengthAt_of_le_left (classes j) (huv.trans hvleftj)]
          ring
      · simp
    apply Subtype.ext
    change collapseCoordinateReal classes u = collapseCoordinateReal classes v
    unfold collapseCoordinateReal
    congr 1
    linarith
  have map_eq_of_same_class (i : Fin n) {u v : I}
      (hu : u ∈ (classes i).carrier) (hv : v ∈ (classes i).carrier) :
      canonicalCollapseMap classes hordered htotal u =
        canonicalCollapseMap classes hordered htotal v := by
    by_cases huv : u ≤ v
    · exact map_eq_of_same_class_of_le i hu hv huv
    · exact (map_eq_of_same_class_of_le i hv hu (le_of_not_ge huv)).symm
  constructor
  · intro hxy
    by_cases heq : x = y
    · exact Or.inl heq
    · right
      rcases lt_or_gt_of_ne heq with hlt | hgt
      · exact sameClass_of_lt hlt hxy
      · rcases sameClass_of_lt hgt hxy.symm with ⟨i, hyi, hxi⟩
        exact ⟨i, hxi, hyi⟩
  · rintro (rfl | ⟨i, hxi, hyi⟩)
    · rfl
    · exact map_eq_of_same_class i hxi hyi

/-- The cumulative-length collapse coordinate is finite-piece polygonal. -/
theorem canonicalCollapseMap_finitePiecePL
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1) :
    FinitePiecePL (canonicalCollapseMap classes hordered htotal) := by
  let endpoints : Finset ℝ :=
    (Finset.univ.image fun i => ((classes i).left : ℝ)) ∪
      (Finset.univ.image fun i => ((classes i).right : ℝ))
  let p : RealPartition :=
    { points := insert 0 (insert 1 endpoints)
      zero_mem := by simp
      one_mem := by simp
      points_subset := by
        intro z hz
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
          Finset.mem_insert, endpoints] at hz
        rcases hz with rfl | rfl | hz
        · exact ⟨le_rfl, zero_le_one⟩
        · exact ⟨zero_le_one, le_rfl⟩
        · rcases Finset.mem_union.mp hz with hz | hz
          · rcases Finset.mem_image.mp hz with ⟨i, _hi, rfl⟩
            exact (classes i).left.property
          · rcases Finset.mem_image.mp hz with ⟨i, _hi, rfl⟩
            exact (classes i).right.property }
  refine ⟨canonicalCollapseMap_continuous classes hordered htotal, p, ?_⟩
  intro a b hab
  have hremovedAffine (i : Fin n) :
      ∃ m c : ℝ, ∀ x ∈ intervalCell a b,
        removedLengthAt (classes i) x = m * (x : ℝ) + c := by
    have hleftMem : ((classes i).left : ℝ) ∈ p.points := by
      simp [p, endpoints]
    have hrightMem : ((classes i).right : ℝ) ∈ p.points := by
      simp [p, endpoints]
    by_cases hbleft : b ≤ (classes i).left
    · refine ⟨0, 0, ?_⟩
      intro x hx
      rw [removedLengthAt_of_le_left (classes i) (hx.2.trans hbleft)]
      ring
    · have hleftb : ((classes i).left : ℝ) < b := lt_of_not_ge hbleft
      have hlefta : ((classes i).left : ℝ) ≤ a := by
        by_contra hnot
        exact (hab.2.2.2 (classes i).left hleftMem)
          ⟨lt_of_not_ge hnot, hleftb⟩
      by_cases hrighta : ((classes i).right : ℝ) ≤ a
      · refine ⟨0, (classes i).length, ?_⟩
        intro x hx
        rw [removedLengthAt_of_right_le (classes i) (hrighta.trans hx.1)]
        ring
      · have haright : a < ((classes i).right : ℝ) := lt_of_not_ge hrighta
        have hbright : b ≤ ((classes i).right : ℝ) := by
          by_contra hnot
          exact (hab.2.2.2 (classes i).right hrightMem)
            ⟨haright, lt_of_not_ge hnot⟩
        refine ⟨1, -((classes i).left : ℝ), ?_⟩
        intro x hx
        rw [removedLengthAt_of_mem (classes i)
          ⟨hlefta.trans hx.1, hx.2.trans hbright⟩]
        ring
  choose m c hmc using hremovedAffine
  refine ⟨(1 - ∑ i, m i) / (1 - totalCollapsedLength classes),
    -(∑ i, c i) / (1 - totalCollapsedLength classes), ?_⟩
  intro x hx
  change collapseCoordinateReal classes x =
    ((1 - ∑ i, m i) / (1 - totalCollapsedLength classes)) * (x : ℝ) +
      -(∑ i, c i) / (1 - totalCollapsedLength classes)
  have hsum : cumulativeRemovedLength classes x =
      (∑ i, m i) * (x : ℝ) + ∑ i, c i := by
    calc
      cumulativeRemovedLength classes x =
          ∑ i, (m i * (x : ℝ) + c i) := by
        unfold cumulativeRemovedLength
        apply Finset.sum_congr rfl
        intro i _hi
        exact hmc i x hx
      _ = (∑ i, m i) * (x : ℝ) + ∑ i, c i := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
  rw [collapseCoordinateReal, hsum]
  ring

/-- On every complementary gap the collapse coordinate is positively affine. -/
theorem canonicalCollapseMap_positiveAffineOn_complementaryGap
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (htotal : totalCollapsedLength classes < 1)
    (J : ClosedSubinterval) (hJ : IsComplementaryGap classes J) :
    IsPositiveAffineOn (canonicalCollapseMap classes hordered htotal) J.carrier := by
  have hside (i : Fin n) :
      (classes i).right ≤ J.left ∨ J.right ≤ (classes i).left := by
    by_cases hleft : (classes i).right ≤ J.left
    · exact Or.inl hleft
    · right
      by_contra hright
      have hJleftRight : J.left < (classes i).right := lt_of_not_ge hleft
      have hclassLeftJright : (classes i).left < J.right := lt_of_not_ge hright
      by_cases hJleftClassLeft : J.left < (classes i).left
      · have hopen : (classes i).left ∈ J.openCarrier :=
          ⟨hJleftClassLeft, hclassLeftJright⟩
        have hclass : (classes i).left ∈ (classes i).carrier :=
          Set.left_mem_Icc.mpr (classes i).left_le_right
        exact (Set.disjoint_left.mp hJ.2.1) hopen
          (Set.mem_iUnion.mpr ⟨i, hclass⟩)
      · have hclassLeft : (classes i).left ≤ J.left := le_of_not_gt hJleftClassLeft
        have hmin : J.left < min J.right (classes i).right :=
          lt_min hJ.1 hJleftRight
        obtain ⟨z, hJz, hzmin⟩ := exists_between hmin
        have hopen : z ∈ J.openCarrier :=
          ⟨hJz, hzmin.trans_le (min_le_left _ _)⟩
        have hclass : z ∈ (classes i).carrier :=
          ⟨hclassLeft.trans hJz.le, hzmin.le.trans (min_le_right _ _)⟩
        exact (Set.disjoint_left.mp hJ.2.1) hopen
          (Set.mem_iUnion.mpr ⟨i, hclass⟩)
  have hconstant (x : I) (hx : x ∈ J.carrier) :
      cumulativeRemovedLength classes x =
        cumulativeRemovedLength classes J.left := by
    unfold cumulativeRemovedLength
    apply Finset.sum_congr rfl
    intro i _hi
    rcases hside i with hleft | hright
    · rw [removedLengthAt_of_right_le (classes i) (hleft.trans hx.1),
        removedLengthAt_of_right_le (classes i) hleft]
    · rw [removedLengthAt_of_le_left (classes i) (hx.2.trans hright),
        removedLengthAt_of_le_left (classes i) (J.left_le_right.trans hright)]
  let d : ℝ := 1 - totalCollapsedLength classes
  refine ⟨1 / d, -cumulativeRemovedLength classes J.left / d, ?_, ?_⟩
  · dsimp [d]
    exact one_div_pos.mpr (sub_pos.mpr htotal)
  · intro x hx
    change collapseCoordinateReal classes x =
      (1 / d) * (x : ℝ) + -cumulativeRemovedLength classes J.left / d
    rw [collapseCoordinateReal, hconstant x hx]
    dsimp [d]
    ring

/--
The canonical finite quotient associated to a proper ordered family of
nondegenerate interval classes.
-/
noncomputable def canonicalFiniteIntervalQuotientOfOrdered
    {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hordered : StrictlyOrderedIntervalFamily classes)
    (hnondegenerate : ∀ i, (classes i).Nondegenerate)
    (hproper : collapsedLocus classes ≠ Set.univ) :
    CanonicalFiniteIntervalQuotient := by
  let htotal := totalCollapsedLength_lt_one_of_proper hordered hproper
  exact
    { toFun := canonicalCollapseMap classes hordered htotal
      continuous_toFun := canonicalCollapseMap_continuous classes hordered htotal
      surjective_toFun := canonicalCollapseMap_surjective classes hordered htotal
      monotone_toFun := canonicalCollapseMap_monotone classes hordered htotal
      nonconstant_toFun :=
        ⟨leftEndpoint, rightEndpoint, by
          rw [canonicalCollapseMap_leftEndpoint classes hordered htotal,
            canonicalCollapseMap_rightEndpoint classes hordered htotal]
          intro h
          have := congrArg Subtype.val h
          norm_num [leftEndpoint, rightEndpoint] at this⟩
      collapsedCount := n
      collapsed := classes
      collapsed_nondegenerate := hnondegenerate
      collapsed_pairwise_disjoint :=
        strictlyOrderedIntervalFamily_pairwise_disjoint hordered
      fibre_iff :=
        canonicalCollapseMap_fibre_iff classes hordered hnondegenerate htotal
      finitePiecePL_toFun :=
        canonicalCollapseMap_finitePiecePL classes hordered htotal
      positiveAffineOn_complementaryGap :=
        canonicalCollapseMap_positiveAffineOn_complementaryGap
          classes hordered htotal }
def IsOrderedFiniteFixedComponentFamily
    (T : IntervalMap) {n : ℕ} (classes : Fin n → ClosedSubinterval) : Prop :=
  StrictlyOrderedIntervalFamily classes ∧
    (∀ i, IsNondegenerateFixedComponent T (classes i)) ∧
    ∀ J : ClosedSubinterval,
      IsNondegenerateFixedComponent T J →
        ∃ i, J.carrier = (classes i).carrier

/-- A nontrivial preconnected fixed subset lies in a maximal fixed interval. -/
private theorem fixedComponent_of_preconnected_fixed_subset_for_enumeration
    (T : IntervalMap) (hT : Continuous T) (S : Set I)
    (hSpre : IsPreconnected S) (hSfixed : S ⊆ fixedPoints T)
    {a b : I} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ J : ClosedSubinterval,
      IsNondegenerateFixedComponent T J ∧ S ⊆ J.carrier := by
  let F : Set I := fixedPoints T
  let C : Set I := connectedComponentIn F a
  have haF : a ∈ F := hSfixed ha
  have hFcompact : IsCompact F := (isClosed_eq hT continuous_id).isCompact
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hFcompact
  have hCcompact : IsCompact C := by
    rw [show C = ((↑) '' connectedComponent (⟨a, haF⟩ : F)) from
      connectedComponentIn_eq_image haF]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hCconnected : IsConnected C :=
    isConnected_connectedComponentIn_iff.mpr haF
  have hCeq : C = Set.Icc (sInf C) (sSup C) :=
    eq_Icc_of_connected_compact hCconnected hCcompact
  have hle : sInf C ≤ sSup C := by
    have hCnonempty := hCconnected.1
    rw [hCeq] at hCnonempty
    exact Set.nonempty_Icc.mp hCnonempty
  let J : ClosedSubinterval :=
    { left := sInf C, right := sSup C, left_le_right := hle }
  have hSC : S ⊆ C :=
    hSpre.subset_connectedComponentIn ha hSfixed
  have hSJ : S ⊆ J.carrier := by
    intro x hx
    change x ∈ Set.Icc (sInf C) (sSup C)
    rw [← hCeq]
    exact hSC hx
  refine ⟨J, ⟨?_, ?_, ?_⟩, hSJ⟩
  · apply lt_of_le_of_ne J.left_le_right
    intro hends
    have haJ := hSJ ha
    have hbJ := hSJ hb
    have hae : a = J.left :=
      le_antisymm (by simpa [hends] using haJ.2) haJ.1
    have hbe : b = J.left :=
      le_antisymm (by simpa [hends] using hbJ.2) hbJ.1
    exact hab (hae.trans hbe.symm)
  · intro x hx
    apply connectedComponentIn_subset F a
    have hxC : x ∈ C := by
      rw [hCeq]
      exact hx
    exact hxC
  · intro K hKfixed hJK
    have haK : a ∈ K.carrier := hJK (hSJ ha)
    have hKC : K.carrier ⊆ C :=
      isPreconnected_Icc.subset_connectedComponentIn haK hKfixed
    intro x hx
    change x ∈ Set.Icc (sInf C) (sSup C)
    rw [← hCeq]
    exact hKC hx

private theorem closedSubinterval_eq_of_carrier_eq
    {J K : ClosedSubinterval} (h : J.carrier = K.carrier) : J = K := by
  have hJleftK : J.left ∈ K.carrier := by
    rw [← h]
    exact Set.left_mem_Icc.mpr J.left_le_right
  have hKleftJ : K.left ∈ J.carrier := by
    rw [h]
    exact Set.left_mem_Icc.mpr K.left_le_right
  have hJrightK : J.right ∈ K.carrier := by
    rw [← h]
    exact Set.right_mem_Icc.mpr J.left_le_right
  have hKrightJ : K.right ∈ J.carrier := by
    rw [h]
    exact Set.right_mem_Icc.mpr K.left_le_right
  have hleft : J.left = K.left := by
    exact le_antisymm hKleftJ.1 hJleftK.1
  have hright : J.right = K.right := by
    exact le_antisymm hJrightK.2 hKrightJ.2
  cases J
  cases K
  simp_all

private theorem nondegenerateFixedComponents_eq_of_inter_nonempty
    {T : IntervalMap} (hT : Continuous T) {J K : ClosedSubinterval}
    (hJ : IsNondegenerateFixedComponent T J)
    (hK : IsNondegenerateFixedComponent T K)
    (hinter : (J.carrier ∩ K.carrier).Nonempty) : J = K := by
  let S : Set I := J.carrier ∪ K.carrier
  have hSpre : IsPreconnected S :=
    isPreconnected_Icc.union' hinter isPreconnected_Icc
  have hSfixed : S ⊆ fixedPoints T := by
    intro x hx
    rcases hx with hxJ | hxK
    · exact hJ.2.1 hxJ
    · exact hK.2.1 hxK
  obtain ⟨L, hL, hSL⟩ :=
    fixedComponent_of_preconnected_fixed_subset_for_enumeration
      T hT S hSpre hSfixed
      (Set.mem_union_left K.carrier (Set.left_mem_Icc.mpr J.left_le_right))
      (Set.mem_union_left K.carrier (Set.right_mem_Icc.mpr J.left_le_right))
      hJ.1.ne
  have hJL : J.carrier ⊆ L.carrier :=
    fun x hx => hSL (Set.mem_union_left K.carrier hx)
  have hKL : K.carrier ⊆ L.carrier :=
    fun x hx => hSL (Set.mem_union_right J.carrier hx)
  have hLJ : L.carrier ⊆ J.carrier := hJ.2.2 L hL.2.1 hJL
  have hLK : L.carrier ⊆ K.carrier := hK.2.2 L hL.2.1 hKL
  apply closedSubinterval_eq_of_carrier_eq
  exact Set.Subset.antisymm (hJL.trans hLK) (hKL.trans hLJ)

/-- A finite-union fixed set has finitely many ordered nondegenerate components. -/
theorem exists_orderedFiniteFixedComponentFamily
    (T : IntervalMap) (hT : Continuous T)
    (hfinite : IsFiniteUnionClosedSubintervals (fixedPoints T)) :
    ∃ n : ℕ, ∃ classes : Fin n → ClosedSubinterval,
      IsOrderedFiniteFixedComponentFamily T classes := by
  classical
  rcases hfinite with ⟨m, pieces, hpieces⟩
  have hpieceFixed (i : Fin m) : (pieces i).carrier ⊆ fixedPoints T := by
    intro x hx
    rw [hpieces]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hexistsPiece (J : ClosedSubinterval)
      (hJ : IsNondegenerateFixedComponent T J) :
      ∃ i : Fin m,
        (pieces i).Nondegenerate ∧
          ((pieces i).carrier ∩ J.carrier).Nonempty := by
    by_contra hnone
    push_neg at hnone
    have hsubset : J.carrier ⊆ Set.range (fun i : Fin m => (pieces i).left) := by
      intro x hxJ
      have hxfixed := hJ.2.1 hxJ
      rw [hpieces] at hxfixed
      rcases Set.mem_iUnion.mp hxfixed with ⟨i, hxi⟩
      have hdeg : ¬(pieces i).Nondegenerate := by
        intro hnondeg
        exact (show ((pieces i).carrier ∩ J.carrier).Nonempty from ⟨x, hxi, hxJ⟩).ne_empty
          (hnone i hnondeg)
      have heq : (pieces i).left = (pieces i).right :=
        le_antisymm (pieces i).left_le_right (le_of_not_gt hdeg)
      have hxleft : x = (pieces i).left :=
        le_antisymm (by simpa [heq] using hxi.2) hxi.1
      exact ⟨i, hxleft.symm⟩
    have hfiniteJ : J.carrier.Finite := (Set.finite_range _).subset hsubset
    exact (Set.Icc_infinite hJ.1).not_finite hfiniteJ
  let D := {i : Fin m // (pieces i).Nondegenerate}
  let Comp := {J : ClosedSubinterval // IsNondegenerateFixedComponent T J}
  have hexistsComponent (d : D) :
      ∃ J : ClosedSubinterval,
        IsNondegenerateFixedComponent T J ∧
          (pieces d.1).carrier ⊆ J.carrier := by
    exact fixedComponent_of_preconnected_fixed_subset_for_enumeration
      T hT (pieces d.1).carrier isPreconnected_Icc (hpieceFixed d.1)
      (Set.left_mem_Icc.mpr (pieces d.1).left_le_right)
      (Set.right_mem_Icc.mpr (pieces d.1).left_le_right) d.2.ne
  let candidate : D → Comp := fun d =>
    ⟨Classical.choose (hexistsComponent d),
      (Classical.choose_spec (hexistsComponent d)).1⟩
  have candidate_spec (d : D) :
      (pieces d.1).carrier ⊆ (candidate d).1.carrier :=
    (Classical.choose_spec (hexistsComponent d)).2
  have hcandidateSurjective : Function.Surjective candidate := by
    intro K
    obtain ⟨i, hiNondeg, hinter⟩ := hexistsPiece K.1 K.2
    let d : D := ⟨i, hiNondeg⟩
    rcases hinter with ⟨x, hxi, hxK⟩
    have hinterCandidate :
        ((candidate d).1.carrier ∩ K.1.carrier).Nonempty :=
      ⟨x, candidate_spec d hxi, hxK⟩
    have heq : (candidate d).1 = K.1 :=
      nondegenerateFixedComponents_eq_of_inter_nonempty hT
        (candidate d).2 K.2 hinterCandidate
    refine ⟨d, ?_⟩
    exact Subtype.ext heq
  letI : Finite Comp := Finite.of_surjective candidate hcandidateSurjective
  letI : Fintype Comp := Fintype.ofFinite Comp
  have hleftInjective : Function.Injective (fun C : Comp => C.1.left) := by
    intro J K hleft
    apply Subtype.ext
    apply nondegenerateFixedComponents_eq_of_inter_nonempty hT J.2 K.2
    refine ⟨J.1.left, Set.left_mem_Icc.mpr J.1.left_le_right, ?_⟩
    change K.1.left ≤ J.1.left ∧ J.1.left ≤ K.1.right
    exact ⟨hleft.ge, hleft.le.trans K.1.left_le_right⟩
  letI : LinearOrder Comp :=
    LinearOrder.lift' (fun C : Comp => C.1.left) hleftInjective
  let e : Fin (Fintype.card Comp) ≃o Comp :=
    Fintype.orderIsoFinOfCardEq Comp rfl
  let classes : Fin (Fintype.card Comp) → ClosedSubinterval := fun i => (e i).1
  refine ⟨Fintype.card Comp, classes, ?_, ?_, ?_⟩
  · intro i j hij
    have hcompLt : e i < e j := e.strictMono hij
    have hleftLt : (classes i).left < (classes j).left := by
      exact hcompLt
    by_contra hnot
    have hleftRight : (classes j).left ≤ (classes i).right := le_of_not_gt hnot
    have hinter : ((classes i).carrier ∩ (classes j).carrier).Nonempty := by
      refine ⟨(classes j).left, ?_, Set.left_mem_Icc.mpr (classes j).left_le_right⟩
      exact ⟨hleftLt.le, hleftRight⟩
    have heq : classes i = classes j :=
      nondegenerateFixedComponents_eq_of_inter_nonempty hT (e i).2 (e j).2 hinter
    have : e i = e j := Subtype.ext heq
    exact (ne_of_lt hcompLt) this
  · intro i
    exact (e i).2
  · intro J hJ
    let C : Comp := ⟨J, hJ⟩
    obtain ⟨i, hi⟩ := e.surjective C
    refine ⟨i, ?_⟩
    have hval := congrArg (fun K : Comp => K.1.carrier) hi
    simpa [classes, C] using hval.symm

/-- A proper fixed set makes its enumerated nondegenerate-component locus proper. -/
theorem fixedComponentFamily_collapsedLocus_ne_univ
    {T : IntervalMap} {n : ℕ} {classes : Fin n → ClosedSubinterval}
    (hfamily : IsOrderedFiniteFixedComponentFamily T classes)
    (hproper : fixedPoints T ≠ Set.univ) :
    collapsedLocus classes ≠ Set.univ := by
  intro hlocus
  apply hproper
  apply Set.eq_univ_of_univ_subset
  intro x _hx
  have hx : x ∈ collapsedLocus classes := by rw [hlocus]; trivial
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  exact (hfamily.2.1 i).2.1 hxi

/-- The quotient built from an exact component family collapses exactly those components. -/
theorem canonicalFiniteIntervalQuotientOfOrdered_collapsesExactlyFixedComponents
    {T : IntervalMap} {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (hfamily : IsOrderedFiniteFixedComponentFamily T classes)
    (hproper : fixedPoints T ≠ Set.univ) :
    CollapsesExactlyFixedComponents
      (canonicalFiniteIntervalQuotientOfOrdered classes hfamily.1
        (fun i => (hfamily.2.1 i).1)
        (fixedComponentFamily_collapsedLocus_ne_univ hfamily hproper)) T := by
  constructor
  · intro i
    simpa [canonicalFiniteIntervalQuotientOfOrdered] using hfamily.2.1 i
  · intro J hJ
    obtain ⟨i, hi⟩ := hfamily.2.2 J hJ
    refine ⟨i, ?_⟩
    simpa [canonicalFiniteIntervalQuotientOfOrdered] using hi

/-- Every continuous finite-union proper fixed set has its canonical quotient. -/
theorem exists_canonicalFixedComponentQuotient
    (T : IntervalMap) (hT : Continuous T)
    (hfinite : IsFiniteUnionClosedSubintervals (fixedPoints T))
    (hproper : fixedPoints T ≠ Set.univ) :
    ∃ π : CanonicalFiniteIntervalQuotient,
      CollapsesExactlyFixedComponents π T := by
  obtain ⟨n, classes, hfamily⟩ :=
    exists_orderedFiniteFixedComponentFamily T hT hfinite
  let hclassesProper :=
    fixedComponentFamily_collapsedLocus_ne_univ hfamily hproper
  refine
    ⟨canonicalFiniteIntervalQuotientOfOrdered classes hfamily.1
        (fun i => (hfamily.2.1 i).1) hclassesProper, ?_⟩
  exact canonicalFiniteIntervalQuotientOfOrdered_collapsesExactlyFixedComponents
    classes hfamily hproper

/-- Collapsing every nondegenerate fixed component leaves a finite fixed-set image. -/
theorem fixedPoints_image_finite_of_collapsesExactlyFixedComponents
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hT : Continuous T)
    (hfinite : IsFiniteUnionClosedSubintervals (fixedPoints T))
    (hcomponents : CollapsesExactlyFixedComponents π T) :
    (π.toFun '' fixedPoints T).Finite := by
  classical
  rcases hfinite with ⟨m, pieces, hpieces⟩
  apply (Set.finite_range (fun i : Fin m => π (pieces i).left)).subset
  rintro y ⟨x, hxfixed, rfl⟩
  rw [hpieces] at hxfixed
  rcases Set.mem_iUnion.mp hxfixed with ⟨i, hxi⟩
  refine ⟨i, ?_⟩
  by_cases hnondeg : (pieces i).Nondegenerate
  · have hpieceFixed : (pieces i).carrier ⊆ fixedPoints T := by
      intro z hz
      rw [hpieces]
      exact Set.mem_iUnion.mpr ⟨i, hz⟩
    obtain ⟨J, hJ, hpieceJ⟩ :=
      fixedComponent_of_preconnected_fixed_subset_for_enumeration
        T hT (pieces i).carrier isPreconnected_Icc hpieceFixed
        (Set.left_mem_Icc.mpr (pieces i).left_le_right)
        (Set.right_mem_Icc.mpr (pieces i).left_le_right) hnondeg.ne
    obtain ⟨j, hJeq⟩ := hcomponents.2 J hJ
    apply (π.fibre_iff (pieces i).left x).mpr
    right
    refine ⟨j, ?_, ?_⟩
    · rw [← hJeq]
      exact hpieceJ (Set.left_mem_Icc.mpr (pieces i).left_le_right)
    · rw [← hJeq]
      exact hpieceJ hxi
  · have heq : (pieces i).left = (pieces i).right :=
      le_antisymm (pieces i).left_le_right (le_of_not_gt hnondeg)
    have hx : x = (pieces i).left :=
      le_antisymm (by simpa [heq] using hxi.2) hxi.1
    exact congrArg π.toFun hx.symm
private theorem fixedComponent_of_preconnected_fixed_subset
    (T : IntervalMap) (hT : Continuous T) (S : Set I)
    (hSpre : IsPreconnected S) (hSfixed : S ⊆ fixedPoints T)
    {a b : I} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ J : ClosedSubinterval,
      IsNondegenerateFixedComponent T J ∧ S ⊆ J.carrier := by
  let F : Set I := fixedPoints T
  let C : Set I := connectedComponentIn F a
  have haF : a ∈ F := hSfixed ha
  have hFcompact : IsCompact F := (isClosed_eq hT continuous_id).isCompact
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hFcompact
  have hCcompact : IsCompact C := by
    rw [show C = ((↑) '' connectedComponent (⟨a, haF⟩ : F)) from
      connectedComponentIn_eq_image haF]
    exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
  have hCconnected : IsConnected C :=
    isConnected_connectedComponentIn_iff.mpr haF
  have hCeq : C = Set.Icc (sInf C) (sSup C) :=
    eq_Icc_of_connected_compact hCconnected hCcompact
  have hle : sInf C ≤ sSup C := by
    have hCnonempty := hCconnected.1
    rw [hCeq] at hCnonempty
    exact Set.nonempty_Icc.mp hCnonempty
  let J : ClosedSubinterval :=
    { left := sInf C, right := sSup C, left_le_right := hle }
  have hSC : S ⊆ C :=
    hSpre.subset_connectedComponentIn ha hSfixed
  have hSJ : S ⊆ J.carrier := by
    intro x hx
    change x ∈ Set.Icc (sInf C) (sSup C)
    rw [← hCeq]
    exact hSC hx
  refine ⟨J, ⟨?_, ?_, ?_⟩, hSJ⟩
  · apply lt_of_le_of_ne J.left_le_right
    intro hends
    have haJ := hSJ ha
    have hbJ := hSJ hb
    have hae : a = J.left :=
      le_antisymm (by simpa [hends] using haJ.2) haJ.1
    have hbe : b = J.left :=
      le_antisymm (by simpa [hends] using hbJ.2) hbJ.1
    exact hab (hae.trans hbe.symm)
  · intro x hx
    apply connectedComponentIn_subset F a
    have hxC : x ∈ C := by
      rw [hCeq]
      exact hx
    exact hxC
  · intro K hKfixed hJK
    have haK : a ∈ K.carrier := hJK (hSJ ha)
    have hKC : K.carrier ⊆ C :=
      isPreconnected_Icc.subset_connectedComponentIn haK hKfixed
    intro x hx
    change x ∈ Set.Icc (sInf C) (sSup C)
    rw [← hCeq]
    exact hKC hx

/-- The positive commuting word commutes with its left-hand generator. -/
private theorem positiveWord_commutes_left
    (P Q : IntervalMap) (r s : ℕ) (hcommute : Commute P Q) :
    Commute (positiveWordMap P Q r s) P := by
  exact (Function.Commute.iterate_self P r).comp_left
    (hcommute.iterate_right s).symm

/-- The positive commuting word commutes with its right-hand generator. -/
private theorem positiveWord_commutes_right
    (P Q : IntervalMap) (r s : ℕ) (hcommute : Commute P Q) :
    Commute (positiveWordMap P Q r s) Q := by
  exact (hcommute.iterate_left r).comp_left
    (Function.Commute.iterate_self Q s)

/-- A positive word in two continuous maps is continuous. -/
private theorem continuous_positiveWordMap
    (P Q : IntervalMap) (r s : ℕ) (hP : Continuous P) (hQ : Continuous Q) :
    Continuous (positiveWordMap P Q r s) := by
  exact (hP.iterate r).comp (hQ.iterate s)

/-- On an invariant interval where a genuinely positive commuting word is
the identity, the two generators have a common fixed point. -/
theorem commonFixedPoint_on_positiveWord_fixedInterval
    (P Q : IntervalMap) (r s : ℕ)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcommute : Commute P Q) (hr : 0 < r) (hs : 0 < s)
    (J : ClosedSubinterval)
    (hmapP : MapsTo P J.carrier J.carrier)
    (hmapQ : MapsTo Q J.carrier J.carrier)
    (hword : IsFixedInterval (positiveWordMap P Q r s) J) :
    ∃ x ∈ J.carrier, IsCommonFixedPoint P Q x := by
  cases r with
  | zero => simp at hr
  | succ r =>
    cases s with
    | zero => simp at hs
    | succ s =>
      letI : Fact (J.left ≤ J.right) := ⟨J.left_le_right⟩
      let p : J.carrier → J.carrier := fun x => ⟨P x, hmapP x.2⟩
      let q : J.carrier → J.carrier := fun x => ⟨Q x, hmapQ x.2⟩
      have hpContinuous : Continuous p :=
        (hP.comp continuous_subtype_val).subtype_mk _
      have hqContinuous : Continuous q :=
        (hQ.comp continuous_subtype_val).subtype_mk _
      have hpq : Function.Commute p q := by
        intro x
        apply Subtype.ext
        exact hcommute x
      have hpIter (n : ℕ) (x : J.carrier) :
          ((p^[n]) x : I) = (P^[n]) x := by
        induction n generalizing x with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          simpa [p] using ih (p x)
      have hqIter (n : ℕ) (x : J.carrier) :
          ((q^[n]) x : I) = (Q^[n]) x := by
        induction n generalizing x with
        | zero => rfl
        | succ n ih =>
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          simpa [q] using ih (q x)
      have hwordSub (x : J.carrier) :
          (p^[r.succ]) ((q^[s.succ]) x) = x := by
        apply Subtype.ext
        calc
          ((p^[r.succ]) ((q^[s.succ]) x) : I) =
              (P^[r.succ]) ((q^[s.succ]) x) :=
            hpIter r.succ ((q^[s.succ]) x)
          _ = (P^[r.succ]) ((Q^[s.succ]) x) :=
            congrArg (P^[r.succ]) (hqIter s.succ x)
          _ = x := hword x.2
      have hiterCommute : Function.Commute (p^[r.succ]) (q^[s.succ]) :=
        hpq.iterate_iterate r.succ s.succ
      have hpInjective : Function.Injective p := by
        intro x y hxy
        have hpr : (p^[r.succ]) x = (p^[r.succ]) y := by
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hxy]
        calc
          x = (p^[r.succ]) ((q^[s.succ]) x) := (hwordSub x).symm
          _ = (q^[s.succ]) ((p^[r.succ]) x) := hiterCommute x
          _ = (q^[s.succ]) ((p^[r.succ]) y) := congrArg (q^[s.succ]) hpr
          _ = (p^[r.succ]) ((q^[s.succ]) y) := (hiterCommute y).symm
          _ = y := hwordSub y
      have hqInjective : Function.Injective q := by
        intro x y hxy
        have hqs : (q^[s.succ]) x = (q^[s.succ]) y := by
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hxy]
        calc
          x = (p^[r.succ]) ((q^[s.succ]) x) := (hwordSub x).symm
          _ = (p^[r.succ]) ((q^[s.succ]) y) := congrArg (p^[r.succ]) hqs
          _ = y := hwordSub y
      have hpSurjective : Function.Surjective p := by
        intro y
        refine ⟨(p^[r]) ((q^[s.succ]) y), ?_⟩
        rw [← Function.iterate_succ_apply' p r]
        exact hwordSub y
      have hqSurjective : Function.Surjective q := by
        intro y
        refine ⟨(q^[s]) ((p^[r.succ]) y), ?_⟩
        rw [← Function.iterate_succ_apply' q s]
        exact (hiterCommute y).symm.trans (hwordSub y)
      have hPinjOn : Set.InjOn P J.carrier := by
        intro x hx y hy hxy
        have hpEq : p ⟨x, hx⟩ = p ⟨y, hy⟩ := by
          apply Subtype.ext
          exact hxy
        exact congrArg Subtype.val (hpInjective hpEq)
      have hQinjOn : Set.InjOn Q J.carrier := by
        intro x hx y hy hxy
        have hqEq : q ⟨x, hx⟩ = q ⟨y, hy⟩ := by
          apply Subtype.ext
          exact hxy
        exact congrArg Subtype.val (hqInjective hqEq)
      have hpOrientation : StrictMono p ∨ StrictAnti p := by
        rcases hP.continuousOn.strictMonoOn_of_injOn_Icc'
            J.left_le_right hPinjOn with hmono | hanti
        · left
          intro x y hxy
          exact hmono x.2 y.2 hxy
        · right
          intro x y hxy
          exact hanti x.2 y.2 hxy
      have hqOrientation : StrictMono q ∨ StrictAnti q := by
        rcases hQ.continuousOn.strictMonoOn_of_injOn_Icc'
            J.left_le_right hQinjOn with hmono | hanti
        · left
          intro x y hxy
          exact hmono x.2 y.2 hxy
        · right
          intro x y hxy
          exact hanti x.2 y.2 hxy
      rcases hqOrientation with hqMono | hqAnti
      · rcases hpOrientation with hpMono | hpAnti
        · let leftJ : J.carrier :=
              ⟨J.left, Set.left_mem_Icc.mpr J.left_le_right⟩
          have hleft_le (z : J.carrier) : leftJ ≤ z := z.2.1
          have hpLeft : p leftJ = leftJ := by
            obtain ⟨z, hz⟩ := hpSurjective leftJ
            apply le_antisymm
            · exact (hpMono.monotone (hleft_le z)).trans_eq hz
            · exact hleft_le (p leftJ)
          have hqLeft : q leftJ = leftJ := by
            obtain ⟨z, hz⟩ := hqSurjective leftJ
            apply le_antisymm
            · exact (hqMono.monotone (hleft_le z)).trans_eq hz
            · exact hleft_le (q leftJ)
          refine ⟨(leftJ : I), leftJ.2, ?_⟩
          constructor
          · exact congrArg Subtype.val hpLeft
          · exact congrArg Subtype.val hqLeft
        · obtain ⟨x, hxJ, hxP⟩ :=
              exists_mem_Icc_isFixedPt_of_mapsTo
                hP.continuousOn J.left_le_right hmapP
          let xJ : J.carrier := ⟨x, hxJ⟩
          have hpxJ : p xJ = xJ := by
            apply Subtype.ext
            exact hxP
          have hqpxJ : p (q xJ) = q xJ := by
            calc
              p (q xJ) = q (p xJ) := hpq xJ
              _ = q xJ := congrArg q hpxJ
          have hfixed_unique {u v : J.carrier}
              (hu : p u = u) (hv : p v = v) : u = v := by
            rcases lt_trichotomy u v with huv | huv | huv
            · have h := hpAnti huv
              rw [hu, hv] at h
              exact (not_lt_of_ge huv.le h).elim
            · exact huv
            · have h := hpAnti huv
              rw [hu, hv] at h
              exact (not_lt_of_ge huv.le h).elim
          have hqxJ : q xJ = xJ := hfixed_unique hqpxJ hpxJ
          refine ⟨x, hxJ, hxP, ?_⟩
          exact congrArg Subtype.val hqxJ
      · obtain ⟨x, hxJ, hxQ⟩ :=
            exists_mem_Icc_isFixedPt_of_mapsTo
              hQ.continuousOn J.left_le_right hmapQ
        let xJ : J.carrier := ⟨x, hxJ⟩
        have hqxJ : q xJ = xJ := by
          apply Subtype.ext
          exact hxQ
        have hqpxJ : q (p xJ) = p xJ := by
          calc
            q (p xJ) = p (q xJ) := (hpq xJ).symm
            _ = p xJ := congrArg p hqxJ
        have hfixed_unique {u v : J.carrier}
            (hu : q u = u) (hv : q v = v) : u = v := by
          rcases lt_trichotomy u v with huv | huv | huv
          · have h := hqAnti huv
            rw [hu, hv] at h
            exact (not_lt_of_ge huv.le h).elim
          · exact huv
          · have h := hqAnti huv
            rw [hu, hv] at h
            exact (not_lt_of_ge huv.le h).elim
        have hpxJ : p xJ = xJ := hfixed_unique hqpxJ hqxJ
        refine ⟨x, hxJ, ?_, hxQ⟩
        exact congrArg Subtype.val hpxJ

theorem positiveWord_fixedComponents_respect
    (π : CanonicalFiniteIntervalQuotient) (P Q : IntervalMap)
    (r s : ℕ)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcommute : Commute P Q)
    (hr : 0 < r) (hs : 0 < s)
    (hcomponents :
      CollapsesExactlyFixedComponents π (positiveWordMap P Q r s)) :
    RespectsFibres π.toFun P ∧ RespectsFibres π.toFun Q := by
  have hwordContinuous : Continuous (positiveWordMap P Q r s) :=
    continuous_positiveWordMap P Q r s hP hQ
  have respect_of_commuting (R : IntervalMap) (hR : Continuous R)
      (hwordR : Commute (positiveWordMap P Q r s) R) :
      RespectsFibres π.toFun R := by
    intro x y hxy
    rcases (π.fibre_iff x y).mp hxy with rfl | ⟨i, hxi, hyi⟩
    · rfl
    · by_cases hRxy : R x = R y
      · exact congrArg π.toFun hRxy
      · let S : Set I := R '' (π.collapsed i).carrier
        have hSpre : IsPreconnected S := by
          exact isPreconnected_Icc.image R hR.continuousOn
        have hSfixed : S ⊆ fixedPoints (positiveWordMap P Q r s) := by
          rintro z ⟨u, hu, rfl⟩
          have hufixed := (hcomponents.1 i).2.1 hu
          change positiveWordMap P Q r s (R u) = R u
          calc
            positiveWordMap P Q r s (R u) =
                R (positiveWordMap P Q r s u) := hwordR u
            _ = R u := congrArg R hufixed
        have hRxS : R x ∈ S := ⟨x, hxi, rfl⟩
        have hRyS : R y ∈ S := ⟨y, hyi, rfl⟩
        obtain ⟨J, hJcomponent, hSJ⟩ :=
          fixedComponent_of_preconnected_fixed_subset
            (positiveWordMap P Q r s) hwordContinuous S
            hSpre hSfixed hRxS hRyS hRxy
        obtain ⟨j, hJeq⟩ := hcomponents.2 J hJcomponent
        apply (π.fibre_iff (R x) (R y)).mpr
        right
        refine ⟨j, ?_, ?_⟩
        · rw [← hJeq]
          exact hSJ hRxS
        · rw [← hJeq]
          exact hSJ hRyS
  exact ⟨
    respect_of_commuting P hP (positiveWord_commutes_left P Q r s hcommute),
    respect_of_commuting Q hQ (positiveWord_commutes_right P Q r s hcommute)⟩

end PLQuotientSupport

end CommutingInterval
