import CommutingIntervalSimplified.FactorBase
import Mathlib.Algebra.BigOperators.Fin

/-!
# Canonical quotients by finite interval families

This standalone module constructs the cumulative-length quotient associated
with a finite pairwise-disjoint family of nondegenerate closed intervals. It
uses only the simplified local foundations and Mathlib; no declaration from
the earlier formalization is imported or referenced.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set Topology

namespace FiniteIntervalQuotientConstruction

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
            simp [totalCollapsedLength]]
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
          endpoints] at hz
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
        canonicalCollapseMap_fibre_iff classes hordered htotal
      finitePiecePL_toFun :=
        canonicalCollapseMap_finitePiecePL classes hordered htotal
      positiveAffineOn_complementaryGap :=
        canonicalCollapseMap_positiveAffineOn_complementaryGap
          classes hordered htotal }

/-- A finite pairwise-disjoint family containing two distinct nonempty
closed intervals cannot cover the connected ambient interval. -/
theorem pairwiseDisjointFiniteIntervalFamily_union_ne_univ
    {α : Type*} [Fintype α] (classes : α → ClosedSubinterval)
    (hpairwise : ∀ i j, i ≠ j →
      Disjoint (classes i).carrier (classes j).carrier)
    (htwo : ∃ i j : α, i ≠ j) :
    (⋃ i, (classes i).carrier) ≠ Set.univ := by
  classical
  obtain ⟨i₀, i₁, hi⟩ := htwo
  intro hcover
  let A : Set I := (classes i₀).carrier
  let B : Set I := ⋃ j : {j : α // j ≠ i₀}, (classes j.1).carrier
  have hAcompact : IsCompact A := isCompact_Icc
  have hBcompact : IsCompact B := by
    exact isCompact_iUnion fun j : {j : α // j ≠ i₀} =>
      (isCompact_Icc : IsCompact (classes j.1).carrier)
  have hABunion : A ∪ B = Set.univ := by
    rw [← hcover]
    ext x
    constructor
    · rintro (hxA | hxB)
      · exact Set.mem_iUnion.mpr ⟨i₀, hxA⟩
      · obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxB
        exact Set.mem_iUnion.mpr ⟨j.1, hxj⟩
    · intro hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      by_cases hj : j = i₀
      · left
        simpa [A, hj] using hxj
      · right
        exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩
  have hABdisjoint : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxB
    exact (Set.disjoint_left.mp (hpairwise i₀ j.1 j.2.symm)) hxA hxj
  have hB_eq_compl : B = Aᶜ := by
    ext x
    constructor
    · intro hxB hxA
      exact (Set.disjoint_left.mp hABdisjoint) hxA hxB
    · intro hxA
      have hx : x ∈ A ∪ B := by rw [hABunion]; exact Set.mem_univ x
      rcases hx with hxA' | hxB
      · exact (hxA hxA').elim
      · exact hxB
  have hA_eq_compl : A = Bᶜ := by rw [hB_eq_compl, compl_compl]
  have hAopen : IsOpen A := by
    rw [hA_eq_compl]
    exact hBcompact.isClosed.isOpen_compl
  have hBopen : IsOpen B := by
    rw [hB_eq_compl]
    exact hAcompact.isClosed.isOpen_compl
  have hAne : (Set.univ ∩ A).Nonempty := by
    exact ⟨(classes i₀).left, Set.mem_univ _,
      Set.left_mem_Icc.mpr (classes i₀).left_le_right⟩
  have hBne : (Set.univ ∩ B).Nonempty := by
    refine ⟨(classes i₁).left, Set.mem_univ _, ?_⟩
    exact Set.mem_iUnion.mpr
      ⟨⟨i₁, hi.symm⟩,
        Set.left_mem_Icc.mpr (classes i₁).left_le_right⟩
  have hinter := isConnected_univ.isPreconnected A B hAopen hBopen
    (by rw [hABunion]) hAne hBne
  obtain ⟨x, _hxuniv, hxA, hxB⟩ := hinter
  exact (Set.disjoint_left.mp hABdisjoint) hxA hxB

/-- A canonical quotient together with the exact correspondence between its
ordered internal labels and the caller's original finite label type. -/
structure FiniteIntervalQuotientPresentation
    {α : Type*} [Fintype α] (classes : α → ClosedSubinterval) where
  quotient : CanonicalFiniteIntervalQuotient
  indexEquiv : Fin quotient.collapsedCount ≃ α
  collapsed_carrier : ∀ i,
    (quotient.collapsed i).carrier = (classes (indexEquiv i)).carrier

/-- Order-free construction of the canonical quotient of a proper finite
pairwise-disjoint interval family. -/
theorem finiteIntervalQuotientPresentation_exists
    {α : Type*} [Fintype α] (classes : α → ClosedSubinterval)
    (hnondegenerate : ∀ i, (classes i).Nondegenerate)
    (hpairwise : ∀ i j, i ≠ j →
      Disjoint (classes i).carrier (classes j).carrier)
    (hproper : (⋃ i, (classes i).carrier) ≠ Set.univ) :
    Nonempty (FiniteIntervalQuotientPresentation classes) := by
  classical
  have hleftInjective : Function.Injective
      (fun i : α => (classes i).left) := by
    intro i j hleft
    by_contra hij
    have hdisj := hpairwise i j hij
    have hlefti : (classes i).left ∈ (classes i).carrier :=
      Set.left_mem_Icc.mpr (classes i).left_le_right
    have hleftj : (classes i).left ∈ (classes j).carrier :=
      ⟨hleft.ge, hleft.le.trans (classes j).left_le_right⟩
    exact (Set.disjoint_left.mp hdisj) hlefti hleftj
  letI : LinearOrder α :=
    LinearOrder.lift' (fun i : α => (classes i).left) hleftInjective
  let e : Fin (Fintype.card α) ≃o α :=
    Fintype.orderIsoFinOfCardEq α rfl
  let orderedClasses : Fin (Fintype.card α) → ClosedSubinterval :=
    fun i => classes (e i)
  have hordered : StrictlyOrderedIntervalFamily orderedClasses := by
    intro i j hij
    have hleft : (orderedClasses i).left < (orderedClasses j).left :=
      e.strictMono hij
    by_contra hnot
    have hcommon : (orderedClasses j).left ∈
        (orderedClasses i).carrier ∩ (orderedClasses j).carrier :=
      ⟨⟨hleft.le, le_of_not_gt hnot⟩,
        Set.left_mem_Icc.mpr (orderedClasses j).left_le_right⟩
    have heij : e i ≠ e j := e.injective.ne (ne_of_lt hij)
    exact (Set.disjoint_left.mp (hpairwise (e i) (e j) heij))
      hcommon.1 hcommon.2
  have horderedNondegenerate : ∀ i,
      (orderedClasses i).Nondegenerate :=
    fun i => hnondegenerate (e i)
  have hlocus : collapsedLocus orderedClasses =
      ⋃ i, (classes i).carrier := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨e i, hxi⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, rfl⟩ := e.surjective i
      exact Set.mem_iUnion.mpr ⟨j, hxi⟩
  have horderedProper : collapsedLocus orderedClasses ≠ Set.univ := by
    rwa [hlocus]
  let π := canonicalFiniteIntervalQuotientOfOrdered
    orderedClasses hordered horderedNondegenerate horderedProper
  refine ⟨{
    quotient := π
    indexEquiv := ?_
    collapsed_carrier := ?_
  }⟩
  · exact e.toEquiv
  · intro i
    rfl

end FiniteIntervalQuotientConstruction

end CommutingIntervalSimplified
