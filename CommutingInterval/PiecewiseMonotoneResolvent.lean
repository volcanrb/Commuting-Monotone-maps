import CommutingInterval.PiecewiseMonotoneHorseshoe
import CommutingInterval.PiecewiseMonotoneVariation
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# A weak-lap resolvent for piecewise-monotone interval maps

This file constructs the expanding atomless eigenprobability needed by the
piecewise-monotone reduction.  Unlike the older strict-lap Parry development,
the construction here permits constant pieces and arbitrary plateau
subintervals.

The combinatorial input is the *minimal* number of weakly monotone cells on a
localized interval.  This makes the count independent of redundant cuts.
Adjacent additivity and transport through a weakly monotone first branch have
an error of at most one; after division by the diverging total resolvent these
errors disappear.  The horseshoe lower bound is proved at a target outside the
countable union of plateau values of all iterates.  Thus no finite-fibre or
strict-lap hypothesis is used in the consumed interface.
-/

noncomputable section

namespace CommutingInterval

open Function Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

/-! ## Minimal localized weak laps -/

/-- A finite ordered subdivision of `[x,y]` on whose closed cells `F` is
weakly monotone. -/
structure WeakLapSubdivision (F : IntervalMap) (x y : I) where
  cellCount : ℕ
  breakpoint : Fin (cellCount + 1) → I
  breakpoint_zero : breakpoint 0 = x
  breakpoint_last : breakpoint (Fin.last cellCount) = y
  breakpoint_strictMono : StrictMono breakpoint
  weaklyMonotoneOn_cell : ∀ i : Fin cellCount,
    IsWeaklyMonotoneOn F
      (Set.Icc (breakpoint i.castSucc) (breakpoint i.succ))

/-- There is a weak-lap subdivision with exactly `k` cells. -/
def HasWeakLapSubdivision (F : IntervalMap) (x y : I) (k : ℕ) : Prop :=
  ∃ S : WeakLapSubdivision F x y, S.cellCount = k

/-- The minimum number of weakly monotone cells on a nondegenerate localized
interval.  Degenerate and backwards intervals have count zero. -/
noncomputable def weakLapCountOf (F : IntervalMap) (x y : I) : ℕ :=
  if x < y then sInf {k : ℕ | HasWeakLapSubdivision F x y k} else 0

/-- Local weak-lap count for an iterate. -/
noncomputable def weakLapCountOn
    (T : IntervalMap) (n : ℕ) (x y : I) : ℕ :=
  weakLapCountOf (iterateMap T n) x y

/-- Total weak-lap count for an iterate. -/
noncomputable def weakLapCount (T : IntervalMap) (n : ℕ) : ℕ :=
  weakLapCountOn T n leftEndpoint rightEndpoint

/-- Finite-piece weak monotonicity is preserved by every iterate. -/
theorem FinitePieceMonotone.iterate {T : IntervalMap}
    (hT : FinitePieceMonotone T) (n : ℕ) :
    FinitePieceMonotone (iterateMap T n) := by
  induction n with
  | zero =>
      simpa [iterateMap] using
        (FinitePieceMonotone.of_monotone (T := id) continuous_id monotone_id)
  | succ n ih =>
      rw [iterateMap, Function.iterate_succ']
      exact hT.comp ih

/-- The left endpoint of a chosen monotonicity lap, regarded as a point of
the unit interval. -/
private def monotonicityLapLeftPoint {F : IntervalMap}
    (P : MonotonicityPartition F) (q : P.partition.LapIndex) : I :=
  ⟨q.left, P.partition.points_subset q.adjacent.1⟩

/-- The partition vertices relevant to `[x,y]`, with the two localized
endpoints adjoined.  Left endpoints suffice: every partition vertex below
`1` is the left endpoint of its right-adjacent lap. -/
private noncomputable def localizedPartitionBreakpoints {F : IntervalMap}
    (P : MonotonicityPartition F) (x y : I) : Finset I := by
  classical
  exact insert x <| insert y <|
    (Finset.univ.image (monotonicityLapLeftPoint P)).filter
      fun z => x ≤ z ∧ z ≤ y

private theorem localizedPartitionBreakpoints_mem_left {F : IntervalMap}
    (P : MonotonicityPartition F) (x y : I) :
    x ∈ localizedPartitionBreakpoints P x y := by
  classical
  simp [localizedPartitionBreakpoints]

private theorem localizedPartitionBreakpoints_mem_right {F : IntervalMap}
    (P : MonotonicityPartition F) (x y : I) :
    y ∈ localizedPartitionBreakpoints P x y := by
  classical
  simp [localizedPartitionBreakpoints]

private theorem localizedPartitionBreakpoints_bounds {F : IntervalMap}
    (P : MonotonicityPartition F) (x y z : I)
    (hxy : x ≤ y)
    (hz : z ∈ localizedPartitionBreakpoints P x y) :
    x ≤ z ∧ z ≤ y := by
  classical
  simp only [localizedPartitionBreakpoints, Finset.mem_insert,
    Finset.mem_filter] at hz
  rcases hz with rfl | rfl | ⟨_hz, hzxy⟩
  · exact ⟨le_rfl, hxy⟩
  · exact ⟨hxy, le_rfl⟩
  · exact hzxy

private theorem partitionPoint_mem_localizedPartitionBreakpoints
    {F : IntervalMap} (P : MonotonicityPartition F) {x y : I}
    {c : ℝ} (hc : c ∈ P.partition.points)
    (hxc : (x : ℝ) < c) (hcy : c < (y : ℝ)) :
    (⟨c, P.partition.points_subset hc⟩ : I) ∈
      localizedPartitionBreakpoints P x y := by
  classical
  let z : I := ⟨c, P.partition.points_subset hc⟩
  have hzright : z < rightEndpoint := by
    change c < 1
    exact hcy.trans_le y.property.2
  obtain ⟨a, b, hab, hac, hcb⟩ :=
    P.partition.exists_adjacent_Ico hzright
  have hca : c ≤ a := by
    by_contra h
    exact hab.2.2.2 c hc ⟨lt_of_not_ge h, hcb⟩
  have hac_eq : a = c := le_antisymm hac hca
  subst a
  have hpair : (c, b) ∈ P.partition.adjacentPairs := by
    rw [RealPartition.adjacentPairs]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hc, hab.2.1⟩, hab⟩
  let q : P.partition.LapIndex := ⟨(c, b), hpair⟩
  have hq : monotonicityLapLeftPoint P q = z := by
    apply Subtype.ext
    rfl
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩, ?_⟩
  exact ⟨hxc.le, hcy.le⟩

private theorem localizedPartitionBreakpoints_card_le {F : IntervalMap}
    (P : MonotonicityPartition F) (x y : I) :
    (localizedPartitionBreakpoints P x y).card ≤
      Fintype.card P.partition.LapIndex + 2 := by
  classical
  let L : Finset I :=
    Finset.univ.image (monotonicityLapLeftPoint P)
  let M : Finset I := L.filter fun z => x ≤ z ∧ z ≤ y
  have hM : M.card ≤ L.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hL : L.card ≤ Fintype.card P.partition.LapIndex := by
    simpa [L] using
      (Finset.card_image_le (s := (Finset.univ :
        Finset P.partition.LapIndex))
        (f := monotonicityLapLeftPoint P))
  have hy := Finset.card_insert_le y M
  have hx := Finset.card_insert_le x (insert y M)
  change (insert x (insert y M)).card ≤
    Fintype.card P.partition.LapIndex + 2
  omega

/-- A chosen weak-monotonicity partition canonically supplies a localized
subdivision, with a bound depending only on the number of its laps. -/
private theorem weakLapSubdivision_of_partition {F : IntervalMap}
    (P : MonotonicityPartition F) {x y : I} (hxy : x < y) :
    ∃ S : WeakLapSubdivision F x y,
      S.cellCount ≤ Fintype.card P.partition.LapIndex + 2 := by
  classical
  let s : Finset I := localizedPartitionBreakpoints P x y
  have hxs : x ∈ s := localizedPartitionBreakpoints_mem_left P x y
  have hys : y ∈ s := localizedPartitionBreakpoints_mem_right P x y
  have hsBounds : ∀ z ∈ s, x ≤ z ∧ z ≤ y := fun z hz =>
    localizedPartitionBreakpoints_bounds P x y z hxy.le hz
  have htwo : 2 ≤ s.card := by
    have hsubset : ({x, y} : Finset I) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxs
      · exact hys
    have hcard : ({x, y} : Finset I).card = 2 := by
      simp [hxy.ne]
    rw [← hcard]
    exact Finset.card_le_card hsubset
  let k := s.card - 1
  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hsCard : s.card = k + 1 := by
    dsimp [k]
    omega
  let e : Fin (k + 1) ↪o I := s.orderEmbOfFin hsCard
  have hsne : s.Nonempty := ⟨x, hxs⟩
  have he_mem : ∀ i : Fin (k + 1), e i ∈ s := by
    intro i
    exact Finset.orderEmbOfFin_mem s hsCard i
  have he_zero : e 0 = x := by
    calc
      e 0 = s.min' hsne := by
        simpa [e] using Finset.orderEmbOfFin_zero hsCard (by omega)
      _ = x := (Finset.min'_eq_iff s hsne x).2
        ⟨hxs, fun z hz => (hsBounds z hz).1⟩
  have he_last : e (Fin.last k) = y := by
    have hlast := Finset.orderEmbOfFin_last hsCard (by omega)
    have hmax : s.max' hsne = y := by
      apply (Finset.max'_eq_iff s hsne y).2
      exact ⟨hys, fun z hz => (hsBounds z hz).2⟩
    simpa [e, hmax] using hlast
  have he_noBetween : ∀ i : Fin k, ∀ z ∈ s,
      ¬(e i.castSucc < z ∧ z < e i.succ) := by
    intro i z hzs hz
    let j : Fin (k + 1) :=
      (s.orderIsoOfFin hsCard).symm ⟨z, hzs⟩
    have hej : e j = z := by
      exact congrArg Subtype.val
        ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨z, hzs⟩)
    have hij : i.castSucc < j := by
      apply e.lt_iff_lt.mp
      simpa [hej] using hz.1
    have hji : j < i.succ := by
      apply e.lt_iff_lt.mp
      simpa [hej] using hz.2
    change (i : ℕ) < (j : ℕ) at hij
    change (j : ℕ) < (i : ℕ) + 1 at hji
    omega
  have hweak : ∀ i : Fin k,
      IsWeaklyMonotoneOn F (Set.Icc (e i.castSucc) (e i.succ)) := by
    intro i
    have huv : e i.castSucc < e i.succ := e.strictMono (by simp)
    have hnone : ∀ c ∈ P.partition.points,
        ¬((e i.castSucc : ℝ) < c ∧ c < (e i.succ : ℝ)) := by
      intro c hc hcuv
      let z : I := ⟨c, P.partition.points_subset hc⟩
      have hzs : z ∈ s := by
        apply partitionPoint_mem_localizedPartitionBreakpoints P hc
        · have hxu : (x : ℝ) ≤ (e i.castSucc : ℝ) :=
            (hsBounds _ (he_mem i.castSucc)).1
          exact hxu.trans_lt hcuv.1
        · have hvy : (e i.succ : ℝ) ≤ (y : ℝ) :=
            (hsBounds _ (he_mem i.succ)).2
          exact hcuv.2.trans_le hvy
      exact he_noBetween i z hzs hcuv
    obtain ⟨a, b, hab, hsub⟩ :=
      P.partition.exists_adjacent_superset
        (e i.castSucc).property (e i.succ).property huv hnone
    exact (P.weaklyMonotoneOn_cell hab).mono fun z hz => hsub hz
  let S : WeakLapSubdivision F x y :=
    { cellCount := k
      breakpoint := e
      breakpoint_zero := he_zero
      breakpoint_last := he_last
      breakpoint_strictMono := e.strictMono
      weaklyMonotoneOn_cell := hweak }
  refine ⟨S, ?_⟩
  change k ≤ Fintype.card P.partition.LapIndex + 2
  have hsBound := localizedPartitionBreakpoints_card_le P x y
  change s.card ≤ Fintype.card P.partition.LapIndex + 2 at hsBound
  change s.card - 1 ≤ Fintype.card P.partition.LapIndex + 2
  omega

/-- A finite-piece weakly monotone map has a localized subdivision. -/
theorem weakLapSubdivision_exists {F : IntervalMap}
    (hF : FinitePieceMonotone F) {x y : I} (hxy : x < y) :
    Nonempty (WeakLapSubdivision F x y) := by
  rcases hF.2 with ⟨P⟩
  rcases weakLapSubdivision_of_partition P hxy with ⟨S, _hS⟩
  exact ⟨S⟩

/-- A chosen global partition gives an explicit finite upper bound for every
localized subdivision. -/
theorem weakLapSubdivision_exists_bounded {F : IntervalMap}
    (hF : FinitePieceMonotone F) (P : MonotonicityPartition F)
    {x y : I} (hxy : x < y) :
    ∃ S : WeakLapSubdivision F x y,
      S.cellCount ≤ Fintype.card P.partition.LapIndex + 2 := by
  exact weakLapSubdivision_of_partition P hxy

/-- The infimum defining the localized weak-lap count is attained. -/
theorem weakLapCountOf_attained {F : IntervalMap}
    (hF : FinitePieceMonotone F) {x y : I} (hxy : x < y) :
    ∃ S : WeakLapSubdivision F x y,
      S.cellCount = weakLapCountOf F x y := by
  have hnonempty :
      {k : ℕ | HasWeakLapSubdivision F x y k}.Nonempty := by
    rcases weakLapSubdivision_exists hF hxy with ⟨S⟩
    exact ⟨S.cellCount, S, rfl⟩
  have hmem := Nat.sInf_mem hnonempty
  rw [weakLapCountOf, if_pos hxy]
  exact hmem

/-- The attained count is minimal among all weak-lap subdivisions. -/
theorem weakLapCountOf_minimal {F : IntervalMap}
    (hF : FinitePieceMonotone F) {x y : I} (hxy : x < y)
    (S : WeakLapSubdivision F x y) :
    weakLapCountOf F x y ≤ S.cellCount := by
  rw [weakLapCountOf, if_pos hxy]
  exact Nat.sInf_le ⟨S, rfl⟩

/-- Every nondegenerate localized weak-lap count is positive. -/
theorem weakLapCountOf_pos {F : IntervalMap}
    (hF : FinitePieceMonotone F) {x y : I} (hxy : x < y) :
    0 < weakLapCountOf F x y := by
  rcases weakLapCountOf_attained hF hxy with ⟨S, hS⟩
  rw [← hS]
  by_contra hpos
  have hzero : S.cellCount = 0 := Nat.eq_zero_of_not_pos hpos
  apply hxy.ne
  calc
    x = S.breakpoint 0 := S.breakpoint_zero.symm
    _ = S.breakpoint (Fin.last S.cellCount) := by
      congr 1
      apply Fin.ext
      simp [hzero]
    _ = y := S.breakpoint_last

/-- Restricting an ordered weak-lap subdivision to a nondegenerate closed
subinterval does not increase its number of cells. -/
private theorem WeakLapSubdivision.restrict {F : IntervalMap}
    {a b x y : I} (S : WeakLapSubdivision F a b)
    (hax : a ≤ x) (hxy : x < y) (hyb : y ≤ b) :
    ∃ R : WeakLapSubdivision F x y, R.cellCount ≤ S.cellCount := by
  classical
  have hab : a < b := hax.trans_lt (hxy.trans_le hyb)
  have hScount : 0 < S.cellCount := by
    by_contra hpos
    have hzero : S.cellCount = 0 := Nat.eq_zero_of_not_pos hpos
    apply hab.ne
    calc
      a = S.breakpoint 0 := S.breakpoint_zero.symm
      _ = S.breakpoint (Fin.last S.cellCount) := by
        congr 1
        apply Fin.ext
        simp [hzero]
      _ = b := S.breakpoint_last
  let A : Finset I := Finset.univ.image S.breakpoint
  let M : Finset I := A.filter fun z => x < z ∧ z < y
  have haA : a ∈ A := by
    apply Finset.mem_image.mpr
    exact ⟨0, Finset.mem_univ _, S.breakpoint_zero⟩
  have hbA : b ∈ A := by
    apply Finset.mem_image.mpr
    exact ⟨Fin.last S.cellCount, Finset.mem_univ _, S.breakpoint_last⟩
  have haM : a ∉ M := by
    intro ha
    have hxa : x < a := (Finset.mem_filter.mp ha).2.1
    exact (not_lt_of_ge hax) hxa
  have hbM : b ∉ M := by
    intro hb
    have hby : b < y := (Finset.mem_filter.mp hb).2.2
    exact (not_lt_of_ge hyb) hby
  have habne : a ≠ b := hab.ne
  have hsubA : insert a (insert b M) ⊆ A := by
    intro z hz
    simp only [Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hzM
    · exact haA
    · exact hbA
    · exact (Finset.mem_filter.mp hzM).1
  have hAcard : A.card = S.cellCount + 1 := by
    simp [A, Finset.card_image_of_injective _
      S.breakpoint_strictMono.injective]
  have hinsertCard : (insert a (insert b M)).card = M.card + 2 := by
    simp [haM, hbM, habne]
  have hMcard : M.card + 2 ≤ S.cellCount + 1 := by
    have hcard := Finset.card_le_card hsubA
    simpa [hinsertCard, hAcard] using hcard
  let s : Finset I := insert x (insert y M)
  have hxs : x ∈ s := by simp [s]
  have hys : y ∈ s := by simp [s]
  have hsBounds : ∀ z ∈ s, x ≤ z ∧ z ≤ y := by
    intro z hz
    simp only [s, Finset.mem_insert] at hz
    rcases hz with rfl | rfl | hzM
    · exact ⟨le_rfl, hxy.le⟩
    · exact ⟨hxy.le, le_rfl⟩
    · have hzxy := (Finset.mem_filter.mp hzM).2
      exact ⟨hzxy.1.le, hzxy.2.le⟩
  have hsCardBound : s.card ≤ S.cellCount + 1 := by
    have hy := Finset.card_insert_le y M
    have hx := Finset.card_insert_le x (insert y M)
    change (insert x (insert y M)).card ≤ S.cellCount + 1
    omega
  have htwo : 2 ≤ s.card := by
    have hsubset : ({x, y} : Finset I) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxs
      · exact hys
    have hcard : ({x, y} : Finset I).card = 2 := by
      simp [hxy.ne]
    rw [← hcard]
    exact Finset.card_le_card hsubset
  let k := s.card - 1
  have hkpos : 0 < k := by
    dsimp [k]
    omega
  have hsCard : s.card = k + 1 := by
    dsimp [k]
    omega
  let e : Fin (k + 1) ↪o I := s.orderEmbOfFin hsCard
  have hsne : s.Nonempty := ⟨x, hxs⟩
  have he_mem : ∀ i : Fin (k + 1), e i ∈ s := by
    intro i
    exact Finset.orderEmbOfFin_mem s hsCard i
  have he_zero : e 0 = x := by
    calc
      e 0 = s.min' hsne := by
        simpa [e] using Finset.orderEmbOfFin_zero hsCard (by omega)
      _ = x := (Finset.min'_eq_iff s hsne x).2
        ⟨hxs, fun z hz => (hsBounds z hz).1⟩
  have he_last : e (Fin.last k) = y := by
    have hlast := Finset.orderEmbOfFin_last hsCard (by omega)
    have hmax : s.max' hsne = y :=
      (Finset.max'_eq_iff s hsne y).2
        ⟨hys, fun z hz => (hsBounds z hz).2⟩
    simpa [e, hmax] using hlast
  have he_noBetween : ∀ i : Fin k, ∀ z ∈ s,
      ¬(e i.castSucc < z ∧ z < e i.succ) := by
    intro i z hzs hz
    let j : Fin (k + 1) :=
      (s.orderIsoOfFin hsCard).symm ⟨z, hzs⟩
    have hej : e j = z := by
      exact congrArg Subtype.val
        ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨z, hzs⟩)
    have hij : i.castSucc < j := by
      apply e.lt_iff_lt.mp
      simpa [hej] using hz.1
    have hji : j < i.succ := by
      apply e.lt_iff_lt.mp
      simpa [hej] using hz.2
    change (i : ℕ) < (j : ℕ) at hij
    change (j : ℕ) < (i : ℕ) + 1 at hji
    omega
  have hSbreak_noBetween : ∀ i : Fin k, ∀ j : Fin (S.cellCount + 1),
      ¬(e i.castSucc < S.breakpoint j ∧
        S.breakpoint j < e i.succ) := by
    intro i j hj
    have hjA : S.breakpoint j ∈ A := by
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    have hjM : S.breakpoint j ∈ M := by
      apply Finset.mem_filter.mpr
      refine ⟨hjA, ?_⟩
      exact ⟨(hsBounds _ (he_mem i.castSucc)).1.trans_lt hj.1,
        hj.2.trans_le (hsBounds _ (he_mem i.succ)).2⟩
    exact he_noBetween i (S.breakpoint j)
      (by simp [s, hjM]) hj
  have hweak : ∀ i : Fin k,
      IsWeaklyMonotoneOn F (Set.Icc (e i.castSucc) (e i.succ)) := by
    intro i
    have huv : e i.castSucc < e i.succ := e.strictMono (by simp)
    let p : Fin (S.cellCount + 1) → Prop := fun j =>
      e i.castSucc < S.breakpoint j
    have hp : ∃ j, p j := by
      refine ⟨Fin.last S.cellCount, ?_⟩
      change e i.castSucc < S.breakpoint (Fin.last S.cellCount)
      rw [S.breakpoint_last]
      exact huv.trans_le
        ((hsBounds _ (he_mem i.succ)).2.trans hyb)
    let j : Fin (S.cellCount + 1) := Fin.find p hp
    have hjne : j ≠ 0 := by
      intro hj
      have hjp : p j := Fin.find_spec hp
      have hau : a ≤ e i.castSucc :=
        hax.trans (hsBounds _ (he_mem i.castSucc)).1
      apply (not_lt_of_ge hau)
      simpa [j, p, hj, S.breakpoint_zero] using hjp
    obtain ⟨r, hr⟩ := Fin.exists_succ_eq_of_ne_zero hjne
    have hri : r.castSucc < j := by
      rw [← hr]
      simp
    have hnot : ¬p r.castSucc := Fin.find_min hp hri
    have hlower : S.breakpoint r.castSucc ≤ e i.castSucc := by
      exact le_of_not_gt hnot
    have hjp : e i.castSucc < S.breakpoint j := Fin.find_spec hp
    have hupper : e i.succ ≤ S.breakpoint j := by
      by_contra h
      have hjv : S.breakpoint j < e i.succ := lt_of_not_ge h
      exact hSbreak_noBetween i j ⟨hjp, hjv⟩
    have hupper' : e i.succ ≤ S.breakpoint r.succ := by
      simpa [hr] using hupper
    exact (S.weaklyMonotoneOn_cell r).mono fun z hz =>
      ⟨hlower.trans hz.1, hz.2.trans hupper'⟩
  let R : WeakLapSubdivision F x y :=
    { cellCount := k
      breakpoint := e
      breakpoint_zero := he_zero
      breakpoint_last := he_last
      breakpoint_strictMono := e.strictMono
      weaklyMonotoneOn_cell := hweak }
  refine ⟨R, ?_⟩
  change k ≤ S.cellCount
  change s.card - 1 ≤ S.cellCount
  omega

private theorem weakLapCountOn_mono_aux {T : IntervalMap}
    (hT : FinitePieceMonotone T) (n : ℕ)
    {a x y b : I} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    weakLapCountOn T n x y ≤ weakLapCountOn T n a b := by
  by_cases hxy' : x < y
  · have hab : a < b := hax.trans_lt (hxy'.trans_le hyb)
    rcases weakLapCountOf_attained (hT.iterate n) hab with ⟨S, hS⟩
    rcases S.restrict hax hxy' hyb with ⟨R, hR⟩
    calc
      weakLapCountOn T n x y =
          weakLapCountOf (iterateMap T n) x y := rfl
      _ ≤ R.cellCount :=
        weakLapCountOf_minimal (hT.iterate n) hxy' R
      _ ≤ S.cellCount := hR
      _ = weakLapCountOn T n a b := hS
  · have hxeq : x = y := le_antisymm hxy (le_of_not_gt hxy')
    subst y
    simp [weakLapCountOn, weakLapCountOf]

/-- A localized interval uses no more weak laps than the full interval. -/
theorem weakLapCountOn_le_total {T : IntervalMap}
    (hT : FinitePieceMonotone T) (n : ℕ) (x y : I) :
    weakLapCountOn T n x y ≤ weakLapCount T n := by
  by_cases hxy : x ≤ y
  · exact weakLapCountOn_mono_aux hT n x.property.1 hxy y.property.2
  · have hyx : y < x := lt_of_not_ge hxy
    have hnlt : ¬x < y := not_lt_of_ge hyx.le
    simp [weakLapCountOn, weakLapCountOf, hnlt]

/-- Enlarging a localized interval cannot decrease its minimal weak-lap
count. -/
theorem weakLapCountOn_mono {T : IntervalMap}
    (hT : FinitePieceMonotone T) (n : ℕ)
    {a x y b : I} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    weakLapCountOn T n x y ≤ weakLapCountOn T n a b := by
  exact weakLapCountOn_mono_aux hT n hax hxy hyb

/-- If an interval crosses no breakpoint of a subdivision, it lies in one
of its weakly monotone cells. -/
private theorem WeakLapSubdivision.weaklyMonotoneOn_of_noBreakpoint
    {F : IntervalMap} {a b u v : I} (S : WeakLapSubdivision F a b)
    (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hnone : ∀ j : Fin (S.cellCount + 1),
      ¬(u < S.breakpoint j ∧ S.breakpoint j < v)) :
    IsWeaklyMonotoneOn F (Set.Icc u v) := by
  let p : Fin (S.cellCount + 1) → Prop := fun j =>
    u < S.breakpoint j
  have hp : ∃ j, p j := by
    refine ⟨Fin.last S.cellCount, ?_⟩
    change u < S.breakpoint (Fin.last S.cellCount)
    rw [S.breakpoint_last]
    exact huv.trans_le hvb
  let j : Fin (S.cellCount + 1) := Fin.find p hp
  have hjne : j ≠ 0 := by
    intro hj
    have hjp : p j := Fin.find_spec hp
    apply (not_lt_of_ge hau)
    simpa [j, p, hj, S.breakpoint_zero] using hjp
  obtain ⟨r, hr⟩ := Fin.exists_succ_eq_of_ne_zero hjne
  have hri : r.castSucc < j := by
    rw [← hr]
    simp
  have hnot : ¬p r.castSucc := Fin.find_min hp hri
  have hlower : S.breakpoint r.castSucc ≤ u := le_of_not_gt hnot
  have hjp : u < S.breakpoint j := Fin.find_spec hp
  have hupper : v ≤ S.breakpoint j := by
    by_contra h
    exact hnone j ⟨hjp, lt_of_not_ge h⟩
  have hupper' : v ≤ S.breakpoint r.succ := by
    simpa [hr] using hupper
  exact (S.weaklyMonotoneOn_cell r).mono fun z hz =>
    ⟨hlower.trans hz.1, hz.2.trans hupper'⟩

/-- Sort a finite set of proposed breakpoints and package the consecutive
intervals as a weak-lap subdivision. -/
private theorem weakLapSubdivision_of_breakpointFinset
    {F : IntervalMap} {x y : I} (hxy : x < y) (s : Finset I)
    (hxs : x ∈ s) (hys : y ∈ s)
    (hsBounds : ∀ z ∈ s, x ≤ z ∧ z ≤ y)
    (hweak : ∀ u v : I, u ∈ s → v ∈ s → u < v →
      (∀ z ∈ s, ¬(u < z ∧ z < v)) →
        IsWeaklyMonotoneOn F (Set.Icc u v)) :
    ∃ R : WeakLapSubdivision F x y, R.cellCount + 1 = s.card := by
  classical
  have htwo : 2 ≤ s.card := by
    have hsubset : ({x, y} : Finset I) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxs
      · exact hys
    have hcard : ({x, y} : Finset I).card = 2 := by
      simp [hxy.ne]
    rw [← hcard]
    exact Finset.card_le_card hsubset
  let k := s.card - 1
  have hsCard : s.card = k + 1 := by
    dsimp [k]
    omega
  let e : Fin (k + 1) ↪o I := s.orderEmbOfFin hsCard
  have hsne : s.Nonempty := ⟨x, hxs⟩
  have he_mem : ∀ i : Fin (k + 1), e i ∈ s := by
    intro i
    exact Finset.orderEmbOfFin_mem s hsCard i
  have he_zero : e 0 = x := by
    calc
      e 0 = s.min' hsne := by
        simpa [e] using Finset.orderEmbOfFin_zero hsCard (by omega)
      _ = x := (Finset.min'_eq_iff s hsne x).2
        ⟨hxs, fun z hz => (hsBounds z hz).1⟩
  have he_last : e (Fin.last k) = y := by
    have hlast := Finset.orderEmbOfFin_last hsCard (by omega)
    have hmax : s.max' hsne = y :=
      (Finset.max'_eq_iff s hsne y).2
        ⟨hys, fun z hz => (hsBounds z hz).2⟩
    simpa [e, hmax] using hlast
  have he_noBetween : ∀ i : Fin k, ∀ z ∈ s,
      ¬(e i.castSucc < z ∧ z < e i.succ) := by
    intro i z hzs hz
    let j : Fin (k + 1) :=
      (s.orderIsoOfFin hsCard).symm ⟨z, hzs⟩
    have hej : e j = z := by
      exact congrArg Subtype.val
        ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨z, hzs⟩)
    have hij : i.castSucc < j := by
      apply e.lt_iff_lt.mp
      simpa [hej] using hz.1
    have hji : j < i.succ := by
      apply e.lt_iff_lt.mp
      simpa [hej] using hz.2
    change (i : ℕ) < (j : ℕ) at hij
    change (j : ℕ) < (i : ℕ) + 1 at hji
    omega
  let R : WeakLapSubdivision F x y :=
    { cellCount := k
      breakpoint := e
      breakpoint_zero := he_zero
      breakpoint_last := he_last
      breakpoint_strictMono := e.strictMono
      weaklyMonotoneOn_cell := fun i =>
        hweak (e i.castSucc) (e i.succ) (he_mem i.castSucc)
          (he_mem i.succ) (e.strictMono (by simp)) (he_noBetween i) }
  refine ⟨R, ?_⟩
  change k + 1 = s.card
  exact hsCard.symm

/-- Concatenate subdivisions meeting at one endpoint. -/
private theorem WeakLapSubdivision.concat {F : IntervalMap}
    {x y z : I} (S : WeakLapSubdivision F x y)
    (U : WeakLapSubdivision F y z) (hxy : x < y) (hyz : y < z) :
    ∃ R : WeakLapSubdivision F x z,
      R.cellCount ≤ S.cellCount + U.cellCount := by
  classical
  let A : Finset I := Finset.univ.image S.breakpoint
  let B : Finset I := Finset.univ.image U.breakpoint
  let s : Finset I := A ∪ B
  have hSA : ∀ i, S.breakpoint i ∈ A := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hUB : ∀ i, U.breakpoint i ∈ B := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hxA : x ∈ A := by
    simpa [S.breakpoint_zero] using hSA (0 : Fin (S.cellCount + 1))
  have hyA : y ∈ A := by
    simpa [S.breakpoint_last] using hSA (Fin.last S.cellCount)
  have hyB : y ∈ B := by
    simpa [U.breakpoint_zero] using hUB (0 : Fin (U.cellCount + 1))
  have hzB : z ∈ B := by
    simpa [U.breakpoint_last] using hUB (Fin.last U.cellCount)
  have hxs : x ∈ s := Finset.mem_union_left B hxA
  have hys : y ∈ s := Finset.mem_union_left B hyA
  have hzs : z ∈ s := Finset.mem_union_right A hzB
  have hSBounds : ∀ i, x ≤ S.breakpoint i ∧ S.breakpoint i ≤ y := by
    intro i
    constructor
    · calc
        x = S.breakpoint 0 := S.breakpoint_zero.symm
        _ ≤ S.breakpoint i :=
          S.breakpoint_strictMono.monotone (Fin.zero_le i)
    · calc
        S.breakpoint i ≤ S.breakpoint (Fin.last S.cellCount) :=
          S.breakpoint_strictMono.monotone (Fin.le_last i)
        _ = y := S.breakpoint_last
  have hUBounds : ∀ i, y ≤ U.breakpoint i ∧ U.breakpoint i ≤ z := by
    intro i
    constructor
    · calc
        y = U.breakpoint 0 := U.breakpoint_zero.symm
        _ ≤ U.breakpoint i :=
          U.breakpoint_strictMono.monotone (Fin.zero_le i)
    · calc
        U.breakpoint i ≤ U.breakpoint (Fin.last U.cellCount) :=
          U.breakpoint_strictMono.monotone (Fin.le_last i)
        _ = z := U.breakpoint_last
  have hsBounds : ∀ w ∈ s, x ≤ w ∧ w ≤ z := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwA | hwB
    · rcases Finset.mem_image.mp hwA with ⟨i, _hi, rfl⟩
      exact ⟨(hSBounds i).1, (hSBounds i).2.trans hyz.le⟩
    · rcases Finset.mem_image.mp hwB with ⟨i, _hi, rfl⟩
      exact ⟨hxy.le.trans (hUBounds i).1, (hUBounds i).2⟩
  have hweak : ∀ u v : I, u ∈ s → v ∈ s → u < v →
      (∀ w ∈ s, ¬(u < w ∧ w < v)) →
        IsWeaklyMonotoneOn F (Set.Icc u v) := by
    intro u v hu hv huv hnone
    by_cases hvy : v ≤ y
    · apply S.weaklyMonotoneOn_of_noBreakpoint
        (hsBounds u hu).1 huv hvy
      intro j hj
      exact hnone (S.breakpoint j)
        (Finset.mem_union_left B (hSA j)) hj
    · have hyv : y < v := lt_of_not_ge hvy
      have hyu : y ≤ u := by
        by_contra h
        exact hnone y hys ⟨lt_of_not_ge h, hyv⟩
      apply U.weaklyMonotoneOn_of_noBreakpoint hyu huv
        ((hsBounds v hv).2)
      intro j hj
      exact hnone (U.breakpoint j)
        (Finset.mem_union_right A (hUB j)) hj
  rcases weakLapSubdivision_of_breakpointFinset
      (hxy.trans hyz) s hxs hzs hsBounds hweak with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  have hAcard : A.card = S.cellCount + 1 := by
    simp [A, Finset.card_image_of_injective _
      S.breakpoint_strictMono.injective]
  have hBcard : B.card = U.cellCount + 1 := by
    simp [B, Finset.card_image_of_injective _
      U.breakpoint_strictMono.injective]
  have hyInter : y ∈ A ∩ B := Finset.mem_inter.mpr ⟨hyA, hyB⟩
  have hinter : 1 ≤ (A ∩ B).card := Finset.one_le_card.mpr ⟨y, hyInter⟩
  have hunion := Finset.card_union_add_card_inter A B
  change R.cellCount ≤ S.cellCount + U.cellCount
  change R.cellCount + 1 = s.card at hR
  change s.card + (A ∩ B).card = A.card + B.card at hunion
  omega

/-- Splitting a subdivision at one interior point counts at most one cell
twice. -/
private theorem WeakLapSubdivision.split {F : IntervalMap}
    {x y z : I} (S : WeakLapSubdivision F x z)
    (hxy : x < y) (hyz : y < z) :
    ∃ L : WeakLapSubdivision F x y,
      ∃ R : WeakLapSubdivision F y z,
        L.cellCount + R.cellCount ≤ S.cellCount + 1 := by
  classical
  let A : Finset I := Finset.univ.image S.breakpoint
  let ML : Finset I := A.filter fun w => w < y
  let MR : Finset I := A.filter fun w => y < w
  let sL : Finset I := insert y ML
  let sR : Finset I := insert y MR
  have hSA : ∀ i, S.breakpoint i ∈ A := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hSBounds : ∀ i, x ≤ S.breakpoint i ∧ S.breakpoint i ≤ z := by
    intro i
    constructor
    · calc
        x = S.breakpoint 0 := S.breakpoint_zero.symm
        _ ≤ S.breakpoint i :=
          S.breakpoint_strictMono.monotone (Fin.zero_le i)
    · calc
        S.breakpoint i ≤ S.breakpoint (Fin.last S.cellCount) :=
          S.breakpoint_strictMono.monotone (Fin.le_last i)
        _ = z := S.breakpoint_last
  have hxML : x ∈ ML := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hxy⟩
    simpa [S.breakpoint_zero] using hSA (0 : Fin (S.cellCount + 1))
  have hzMR : z ∈ MR := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hyz⟩
    simpa [S.breakpoint_last] using hSA (Fin.last S.cellCount)
  have hxsL : x ∈ sL := Finset.mem_insert_of_mem hxML
  have hysL : y ∈ sL := Finset.mem_insert_self y ML
  have hysR : y ∈ sR := Finset.mem_insert_self y MR
  have hzsR : z ∈ sR := Finset.mem_insert_of_mem hzMR
  have hsLBounds : ∀ w ∈ sL, x ≤ w ∧ w ≤ y := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwML
    · exact ⟨hxy.le, le_rfl⟩
    · rcases Finset.mem_filter.mp hwML with ⟨hwA, hwy⟩
      rcases Finset.mem_image.mp hwA with ⟨i, _hi, rfl⟩
      exact ⟨(hSBounds i).1, hwy.le⟩
  have hsRBounds : ∀ w ∈ sR, y ≤ w ∧ w ≤ z := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hwMR
    · exact ⟨le_rfl, hyz.le⟩
    · rcases Finset.mem_filter.mp hwMR with ⟨hwA, hyw⟩
      rcases Finset.mem_image.mp hwA with ⟨i, _hi, rfl⟩
      exact ⟨hyw.le, (hSBounds i).2⟩
  have hweakL : ∀ u v : I, u ∈ sL → v ∈ sL → u < v →
      (∀ w ∈ sL, ¬(u < w ∧ w < v)) →
        IsWeaklyMonotoneOn F (Set.Icc u v) := by
    intro u v hu hv huv hnone
    apply S.weaklyMonotoneOn_of_noBreakpoint
      (hsLBounds u hu).1 huv
      ((hsLBounds v hv).2.trans hyz.le)
    intro j hj
    have hjML : S.breakpoint j ∈ ML := by
      apply Finset.mem_filter.mpr
      exact ⟨hSA j, hj.2.trans_le (hsLBounds v hv).2⟩
    exact hnone (S.breakpoint j) (Finset.mem_insert_of_mem hjML) hj
  have hweakR : ∀ u v : I, u ∈ sR → v ∈ sR → u < v →
      (∀ w ∈ sR, ¬(u < w ∧ w < v)) →
        IsWeaklyMonotoneOn F (Set.Icc u v) := by
    intro u v hu hv huv hnone
    apply S.weaklyMonotoneOn_of_noBreakpoint
      (hxy.le.trans (hsRBounds u hu).1) huv (hsRBounds v hv).2
    intro j hj
    have hjMR : S.breakpoint j ∈ MR := by
      apply Finset.mem_filter.mpr
      exact ⟨hSA j, (hsRBounds u hu).1.trans_lt hj.1⟩
    exact hnone (S.breakpoint j) (Finset.mem_insert_of_mem hjMR) hj
  rcases weakLapSubdivision_of_breakpointFinset hxy sL hxsL hysL
      hsLBounds hweakL with ⟨L, hL⟩
  rcases weakLapSubdivision_of_breakpointFinset hyz sR hysR hzsR
      hsRBounds hweakR with ⟨R, hR⟩
  refine ⟨L, R, ?_⟩
  have hdisj : Disjoint ML MR := by
    rw [Finset.disjoint_left]
    intro w hwL hwR
    exact (not_lt_of_ge (Finset.mem_filter.mp hwR).2.le)
      (Finset.mem_filter.mp hwL).2
  have hunionSub : ML ∪ MR ⊆ A := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwL | hwR
    · exact (Finset.mem_filter.mp hwL).1
    · exact (Finset.mem_filter.mp hwR).1
  have hfilters : ML.card + MR.card ≤ A.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunionSub
  have hsLcard := Finset.card_insert_le y ML
  have hsRcard := Finset.card_insert_le y MR
  have hAcard : A.card = S.cellCount + 1 := by
    simp [A, Finset.card_image_of_injective _
      S.breakpoint_strictMono.injective]
  change sL.card ≤ ML.card + 1 at hsLcard
  change sR.card ≤ MR.card + 1 at hsRcard
  change L.cellCount + 1 = sL.card at hL
  change R.cellCount + 1 = sR.card at hR
  omega

/-- Splitting at one point changes the sum of the two minimal weak-lap counts
by at most one. -/
theorem weakLapCountOn_adjacent_error {T : IntervalMap}
    (hT : FinitePieceMonotone T) (n : ℕ)
    {x y z : I} (hxy : x < y) (hyz : y < z) :
    |(weakLapCountOn T n x z : ℤ) -
        weakLapCountOn T n x y - weakLapCountOn T n y z| ≤ 1 := by
  let F := iterateMap T n
  have hF : FinitePieceMonotone F := hT.iterate n
  rcases weakLapCountOf_attained hF hxy with ⟨Sxy, hSxy⟩
  rcases weakLapCountOf_attained hF hyz with ⟨Syz, hSyz⟩
  have hSxy' : Sxy.cellCount = weakLapCountOn T n x y := by
    simpa [F, weakLapCountOn] using hSxy
  have hSyz' : Syz.cellCount = weakLapCountOn T n y z := by
    simpa [F, weakLapCountOn] using hSyz
  rcases Sxy.concat Syz hxy hyz with ⟨Sxz', hconcat⟩
  have hupper : weakLapCountOn T n x z ≤
      weakLapCountOn T n x y + weakLapCountOn T n y z := by
    calc
      weakLapCountOn T n x z = weakLapCountOf F x z := rfl
      _ ≤ Sxz'.cellCount :=
        weakLapCountOf_minimal hF (hxy.trans hyz) Sxz'
      _ ≤ Sxy.cellCount + Syz.cellCount := hconcat
      _ = weakLapCountOn T n x y + weakLapCountOn T n y z := by
        rw [hSxy', hSyz']
  rcases weakLapCountOf_attained hF (hxy.trans hyz) with ⟨Sxz, hSxz⟩
  have hSxz' : Sxz.cellCount = weakLapCountOn T n x z := by
    simpa [F, weakLapCountOn] using hSxz
  rcases Sxz.split hxy hyz with ⟨Sxy', Syz', hsplit⟩
  have hlower : weakLapCountOn T n x y + weakLapCountOn T n y z ≤
      weakLapCountOn T n x z + 1 := by
    calc
      weakLapCountOn T n x y + weakLapCountOn T n y z ≤
          Sxy'.cellCount + Syz'.cellCount := Nat.add_le_add
        (weakLapCountOf_minimal hF hxy Sxy')
        (weakLapCountOf_minimal hF hyz Syz')
      _ ≤ Sxz.cellCount + 1 := hsplit
      _ = weakLapCountOn T n x z + 1 := by rw [hSxz']
  rw [abs_le]
  constructor <;> omega

/-- Cancel a continuous nondecreasing parametrization from a weakly
monotone composite. -/
private theorem weaklyMonotoneOn_factor_of_monotoneOn
    {G φ : IntervalMap} {p q : I} (hpq : p ≤ q)
    (hφcont : Continuous φ) (hφ : MonotoneOn φ (Set.Icc p q))
    (hcomp : IsWeaklyMonotoneOn (G ∘ φ) (Set.Icc p q)) :
    IsWeaklyMonotoneOn G (Set.Icc (φ p) (φ q)) := by
  have hlift : ∀ t ∈ Set.Icc (φ p) (φ q),
      ∃ r ∈ Set.Icc p q, φ r = t := by
    intro t ht
    simpa only [Set.mem_image] using
      (intermediate_value_Icc hpq hφcont.continuousOn ht)
  rcases hcomp with hcomp | hcomp
  · left
    intro s hs t ht hst
    rcases hlift s hs with ⟨r, hr, hrs⟩
    rcases hlift t ht with ⟨w, hw, hwt⟩
    by_cases hrw : r ≤ w
    · simpa [Function.comp_apply, hrs, hwt] using hcomp hr hw hrw
    · have hts : t ≤ s := by
        simpa [hrs, hwt] using hφ hw hr (le_of_not_ge hrw)
      have heq : s = t := le_antisymm hst hts
      exact le_of_eq (congrArg G heq)
  · right
    intro s hs t ht hst
    rcases hlift s hs with ⟨r, hr, hrs⟩
    rcases hlift t ht with ⟨w, hw, hwt⟩
    by_cases hrw : r ≤ w
    · simpa [Function.comp_apply, hrs, hwt] using hcomp hr hw hrw
    · have hts : t ≤ s := by
        simpa [hrs, hwt] using hφ hw hr (le_of_not_ge hrw)
      have heq : s = t := le_antisymm hst hts
      exact le_of_eq (congrArg G heq).symm

/-- Cancel a continuous nonincreasing parametrization from a weakly
monotone composite. -/
private theorem weaklyMonotoneOn_factor_of_antitoneOn
    {G φ : IntervalMap} {p q : I} (hpq : p ≤ q)
    (hφcont : Continuous φ) (hφ : AntitoneOn φ (Set.Icc p q))
    (hcomp : IsWeaklyMonotoneOn (G ∘ φ) (Set.Icc p q)) :
    IsWeaklyMonotoneOn G (Set.Icc (φ q) (φ p)) := by
  have hlift : ∀ t ∈ Set.Icc (φ q) (φ p),
      ∃ r ∈ Set.Icc p q, φ r = t := by
    intro t ht
    simpa only [Set.mem_image] using
      (intermediate_value_Icc' hpq hφcont.continuousOn ht)
  rcases hcomp with hcomp | hcomp
  · right
    intro s hs t ht hst
    rcases hlift s hs with ⟨r, hr, hrs⟩
    rcases hlift t ht with ⟨w, hw, hwt⟩
    by_cases hwr : w ≤ r
    · simpa [Function.comp_apply, hrs, hwt] using hcomp hw hr hwr
    · have hts : t ≤ s := by
        simpa [hrs, hwt] using hφ hr hw (le_of_not_ge hwr)
      have heq : s = t := le_antisymm hst hts
      exact le_of_eq (congrArg G heq).symm
  · left
    intro s hs t ht hst
    rcases hlift s hs with ⟨r, hr, hrs⟩
    rcases hlift t ht with ⟨w, hw, hwt⟩
    by_cases hwr : w ≤ r
    · simpa [Function.comp_apply, hrs, hwt] using hcomp hw hr hwr
    · have hts : t ≤ s := by
        simpa [hrs, hwt] using hφ hr hw (le_of_not_ge hwr)
      have heq : s = t := le_antisymm hst hts
      exact le_of_eq (congrArg G heq)

/-- Removing repetitions from a nondecreasing finite weak-lap sequence does
not increase its number of cells. -/
private theorem weakLapSubdivision_of_monotoneSequence
    {F : IntervalMap} {u v : I} {k : ℕ}
    (w : Fin (k + 1) → I) (hw : Monotone w)
    (hw0 : w 0 = u) (hwlast : w (Fin.last k) = v) (huv : u < v)
    (hcell : ∀ i : Fin k,
      IsWeaklyMonotoneOn F (Set.Icc (w i.castSucc) (w i.succ))) :
    ∃ R : WeakLapSubdivision F u v, R.cellCount ≤ k := by
  classical
  let s : Finset I := Finset.univ.image w
  have hwmem : ∀ i, w i ∈ s := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hus : u ∈ s := by
    simpa [hw0] using hwmem (0 : Fin (k + 1))
  have hvs : v ∈ s := by
    simpa [hwlast] using hwmem (Fin.last k)
  have hbounds : ∀ z ∈ s, u ≤ z ∧ z ≤ v := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, _hi, rfl⟩
    constructor
    · calc
        u = w 0 := hw0.symm
        _ ≤ w i := hw (Fin.zero_le i)
    · calc
        w i ≤ w (Fin.last k) := hw (Fin.le_last i)
        _ = v := hwlast
  have hweak : ∀ a b : I, a ∈ s → b ∈ s → a < b →
      (∀ z ∈ s, ¬(a < z ∧ z < b)) →
        IsWeaklyMonotoneOn F (Set.Icc a b) := by
    intro a b ha hb hab hnone
    let p : Fin (k + 1) → Prop := fun j => a < w j
    have hp : ∃ j, p j := by
      refine ⟨Fin.last k, ?_⟩
      simpa [p, hwlast] using hab.trans_le (hbounds b hb).2
    let j : Fin (k + 1) := Fin.find p hp
    have hjne : j ≠ 0 := by
      intro hj
      have hjp : p j := Fin.find_spec hp
      apply (not_lt_of_ge (hbounds a ha).1)
      simpa [j, p, hj, hw0] using hjp
    obtain ⟨r, hr⟩ := Fin.exists_succ_eq_of_ne_zero hjne
    have hrj : r.castSucc < j := by
      rw [← hr]
      simp
    have hlower : w r.castSucc ≤ a :=
      le_of_not_gt (Fin.find_min hp hrj)
    rcases Finset.mem_image.mp hb with ⟨q, _hq, hqb⟩
    have hpq : p q := by simpa [p, hqb] using hab
    have hjq : j ≤ q := Fin.find_le_of_pos hp hpq
    have hjb : w j ≤ b := by simpa [hqb] using hw hjq
    have hbj : b ≤ w j := by
      by_contra h
      exact hnone (w j) (hwmem j)
        ⟨Fin.find_spec hp, lt_of_not_ge h⟩
    have hjeq : w j = b := le_antisymm hjb hbj
    have hupper : b ≤ w r.succ := by simpa [hr, hjeq]
    exact (hcell r).mono fun z hz =>
      ⟨hlower.trans hz.1, hz.2.trans hupper⟩
  rcases weakLapSubdivision_of_breakpointFinset huv s hus hvs hbounds hweak with
    ⟨R, hR⟩
  refine ⟨R, ?_⟩
  have hscard : s.card ≤ k + 1 := by
    simpa [s] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin (k + 1))))
        (f := w))
  omega

/-- A nondegenerate interval on which a finite-piece map is weakly monotone
has minimal weak-lap count one. -/
private theorem weakLapCountOf_eq_one_of_weaklyMonotoneOn
    {F : IntervalMap} (hF : FinitePieceMonotone F)
    {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn F (Set.Icc x y)) :
    weakLapCountOf F x y = 1 := by
  let s : Finset I := {x, y}
  have hxs : x ∈ s := by simp [s]
  have hys : y ∈ s := by simp [s]
  have hbounds : ∀ z ∈ s, x ≤ z ∧ z ≤ y := by
    intro z hz
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨le_rfl, hxy.le⟩
    · exact ⟨hxy.le, le_rfl⟩
  have hweak : ∀ a b : I, a ∈ s → b ∈ s → a < b →
      (∀ z ∈ s, ¬(a < z ∧ z < b)) →
        IsWeaklyMonotoneOn F (Set.Icc a b) := by
    intro a b ha hb hab _hnone
    have haeq : a = x := by
      rcases (show a = x ∨ a = y by simpa [s] using ha) with rfl | rfl
      · rfl
      · exact False.elim ((not_lt_of_ge (hbounds b hb).2) hab)
    have hbeq : b = y := by
      rcases (show b = x ∨ b = y by simpa [s] using hb) with rfl | rfl
      · exact False.elim ((not_lt_of_ge (hbounds a ha).1) hab)
      · rfl
    simpa [haeq, hbeq] using hmono
  rcases weakLapSubdivision_of_breakpointFinset hxy s hxs hys hbounds hweak with
    ⟨R, hR⟩
  have hRone : R.cellCount = 1 := by
    have hcard : s.card = 2 := by simp [s, hxy.ne]
    omega
  apply Nat.le_antisymm
  · simpa [hRone] using weakLapCountOf_minimal hF hxy R
  · simpa using weakLapCountOf_pos hF hxy

private theorem WeakLapSubdivision.breakpoint_bounds {F : IntervalMap}
    {a b : I} (S : WeakLapSubdivision F a b)
    (i : Fin (S.cellCount + 1)) :
    a ≤ S.breakpoint i ∧ S.breakpoint i ≤ b := by
  constructor
  · calc
      a = S.breakpoint 0 := S.breakpoint_zero.symm
      _ ≤ S.breakpoint i :=
        S.breakpoint_strictMono.monotone (Fin.zero_le i)
  · calc
      S.breakpoint i ≤ S.breakpoint (Fin.last S.cellCount) :=
        S.breakpoint_strictMono.monotone (Fin.le_last i)
      _ = b := S.breakpoint_last

/-- Push a subdivision of a composite through a nondecreasing branch,
discarding repeated image breakpoints. -/
private theorem WeakLapSubdivision.push_monotoneOn
    {G φ : IntervalMap} {x y : I}
    (R : WeakLapSubdivision (G ∘ φ) x y)
    (hxy : x < y) (hφcont : Continuous φ)
    (hφ : MonotoneOn φ (Set.Icc x y)) (himage : φ x < φ y) :
    ∃ Q : WeakLapSubdivision G (φ x) (φ y),
      Q.cellCount ≤ R.cellCount := by
  let w : Fin (R.cellCount + 1) → I := fun i => φ (R.breakpoint i)
  have hw : Monotone w := by
    intro i j hij
    exact hφ (R.breakpoint_bounds i) (R.breakpoint_bounds j)
      (R.breakpoint_strictMono.monotone hij)
  have hw0 : w 0 = φ x := by simp [w, R.breakpoint_zero]
  have hwlast : w (Fin.last R.cellCount) = φ y := by
    simp [w, R.breakpoint_last]
  have hcell : ∀ i : Fin R.cellCount,
      IsWeaklyMonotoneOn G (Set.Icc (w i.castSucc) (w i.succ)) := by
    intro i
    apply weaklyMonotoneOn_factor_of_monotoneOn
      (R.breakpoint_strictMono.monotone i.castSucc_le_succ) hφcont
    · exact hφ.mono fun z hz =>
        ⟨(R.breakpoint_bounds i.castSucc).1.trans hz.1,
          hz.2.trans (R.breakpoint_bounds i.succ).2⟩
    · exact R.weaklyMonotoneOn_cell i
  exact weakLapSubdivision_of_monotoneSequence w hw hw0 hwlast himage hcell

/-- Push a subdivision of a composite through a nonincreasing branch,
reversing its image breakpoints and discarding repetitions. -/
private theorem WeakLapSubdivision.push_antitoneOn
    {G φ : IntervalMap} {x y : I}
    (R : WeakLapSubdivision (G ∘ φ) x y)
    (hxy : x < y) (hφcont : Continuous φ)
    (hφ : AntitoneOn φ (Set.Icc x y)) (himage : φ y < φ x) :
    ∃ Q : WeakLapSubdivision G (φ y) (φ x),
      Q.cellCount ≤ R.cellCount := by
  let w : Fin (R.cellCount + 1) → I := fun i =>
    φ (R.breakpoint i.rev)
  have hw : Monotone w := by
    intro i j hij
    have hrev : j.rev ≤ i.rev := by simpa using hij
    exact hφ (R.breakpoint_bounds j.rev) (R.breakpoint_bounds i.rev)
      (R.breakpoint_strictMono.monotone hrev)
  have hw0 : w 0 = φ y := by simp [w, R.breakpoint_last]
  have hwlast : w (Fin.last R.cellCount) = φ x := by
    simp [w, R.breakpoint_zero]
  have hcell : ∀ i : Fin R.cellCount,
      IsWeaklyMonotoneOn G (Set.Icc (w i.castSucc) (w i.succ)) := by
    intro i
    let r : Fin R.cellCount := i.rev
    have hfactor := weaklyMonotoneOn_factor_of_antitoneOn
      (G := G) (φ := φ)
      (R.breakpoint_strictMono.monotone r.castSucc_le_succ)
      hφcont
      (hφ.mono fun z hz =>
        ⟨(R.breakpoint_bounds r.castSucc).1.trans hz.1,
          hz.2.trans (R.breakpoint_bounds r.succ).2⟩)
      (R.weaklyMonotoneOn_cell r)
    simpa [w, r, Fin.rev_castSucc, Fin.rev_succ] using hfactor
  exact weakLapSubdivision_of_monotoneSequence w hw hw0 hwlast himage hcell

/-- Pull a target subdivision back through a continuous nondecreasing
branch with distinct endpoint images. -/
private theorem WeakLapSubdivision.pull_monotoneOn
    {G φ : IntervalMap} {x y : I}
    (S : WeakLapSubdivision G (φ x) (φ y))
    (hxy : x < y) (hφcont : Continuous φ)
    (hφ : MonotoneOn φ (Set.Icc x y)) (himage : φ x < φ y) :
    ∃ R : WeakLapSubdivision (G ∘ φ) x y,
      R.cellCount = S.cellCount := by
  classical
  have hpre : ∀ j : Fin (S.cellCount + 1),
      ∃ r ∈ Set.Icc x y, φ r = S.breakpoint j := by
    intro j
    simpa only [Set.mem_image] using
      (intermediate_value_Icc hxy.le hφcont.continuousOn
        (S.breakpoint_bounds j))
  choose c hcI hcφ using hpre
  have hkpos : 0 < S.cellCount := by
    by_contra h
    have hk : S.cellCount = 0 := Nat.eq_zero_of_not_pos h
    apply himage.ne
    calc
      φ x = S.breakpoint 0 := S.breakpoint_zero.symm
      _ = S.breakpoint (Fin.last S.cellCount) := by
        congr 1
        apply Fin.ext
        simp [hk]
      _ = φ y := S.breakpoint_last
  have hlastne : Fin.last S.cellCount ≠ (0 : Fin (S.cellCount + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hkne : S.cellCount ≠ 0 := Nat.ne_of_gt hkpos
  let w : Fin (S.cellCount + 1) → I := fun j =>
    if j = 0 then x else if j = Fin.last S.cellCount then y else c j
  have hwI : ∀ j, w j ∈ Set.Icc x y := by
    intro j
    by_cases hj0 : j = 0
    · simp [w, hj0, hxy.le]
    · by_cases hjlast : j = Fin.last S.cellCount
      · subst j
        simp [w, hkne, hxy.le]
      · simpa [w, hj0, hjlast] using hcI j
  have hwφ : ∀ j, φ (w j) = S.breakpoint j := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp [w, S.breakpoint_zero]
    · by_cases hjlast : j = Fin.last S.cellCount
      · subst j
        simp [w, hlastne, S.breakpoint_last]
      · simpa [w, hj0, hjlast] using hcφ j
  have hwzero : w 0 = x := by simp [w]
  have hwlast : w (Fin.last S.cellCount) = y := by
    simp [w, hlastne]
  have hwStrict : StrictMono w := by
    intro i j hij
    apply lt_of_not_ge
    intro hji
    have himage_le : φ (w j) ≤ φ (w i) := hφ (hwI j) (hwI i) hji
    rw [hwφ j, hwφ i] at himage_le
    exact (not_lt_of_ge himage_le) (S.breakpoint_strictMono hij)
  have hweak : ∀ i : Fin S.cellCount,
      IsWeaklyMonotoneOn (G ∘ φ) (Set.Icc (w i.castSucc) (w i.succ)) := by
    intro i
    apply (S.weaklyMonotoneOn_cell i).comp
    · exact Or.inl <| hφ.mono fun z hz =>
        ⟨(hwI i.castSucc).1.trans hz.1,
          hz.2.trans (hwI i.succ).2⟩
    · intro z hz
      constructor
      · calc
          S.breakpoint i.castSucc = φ (w i.castSucc) := (hwφ _).symm
          _ ≤ φ z := hφ (hwI i.castSucc)
            ⟨(hwI i.castSucc).1.trans hz.1,
              hz.2.trans (hwI i.succ).2⟩ hz.1
      · calc
          φ z ≤ φ (w i.succ) := hφ
            ⟨(hwI i.castSucc).1.trans hz.1,
              hz.2.trans (hwI i.succ).2⟩ (hwI i.succ) hz.2
          _ = S.breakpoint i.succ := hwφ _
  let R : WeakLapSubdivision (G ∘ φ) x y :=
    { cellCount := S.cellCount
      breakpoint := w
      breakpoint_zero := hwzero
      breakpoint_last := hwlast
      breakpoint_strictMono := hwStrict
      weaklyMonotoneOn_cell := hweak }
  exact ⟨R, rfl⟩

/-- Pull a target subdivision back through a continuous nonincreasing
branch with distinct endpoint images. -/
private theorem WeakLapSubdivision.pull_antitoneOn
    {G φ : IntervalMap} {x y : I}
    (S : WeakLapSubdivision G (φ y) (φ x))
    (hxy : x < y) (hφcont : Continuous φ)
    (hφ : AntitoneOn φ (Set.Icc x y)) (himage : φ y < φ x) :
    ∃ R : WeakLapSubdivision (G ∘ φ) x y,
      R.cellCount = S.cellCount := by
  classical
  have hpre : ∀ j : Fin (S.cellCount + 1),
      ∃ r ∈ Set.Icc x y, φ r = S.breakpoint j.rev := by
    intro j
    simpa only [Set.mem_image] using
      (intermediate_value_Icc' hxy.le hφcont.continuousOn
        (S.breakpoint_bounds j.rev))
  choose c hcI hcφ using hpre
  have hkpos : 0 < S.cellCount := by
    by_contra h
    have hk : S.cellCount = 0 := Nat.eq_zero_of_not_pos h
    apply himage.ne
    calc
      φ y = S.breakpoint 0 := S.breakpoint_zero.symm
      _ = S.breakpoint (Fin.last S.cellCount) := by
        congr 1
        apply Fin.ext
        simp [hk]
      _ = φ x := S.breakpoint_last
  have hlastne : Fin.last S.cellCount ≠ (0 : Fin (S.cellCount + 1)) := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hkne : S.cellCount ≠ 0 := Nat.ne_of_gt hkpos
  let w : Fin (S.cellCount + 1) → I := fun j =>
    if j = 0 then x else if j = Fin.last S.cellCount then y else c j
  have hwI : ∀ j, w j ∈ Set.Icc x y := by
    intro j
    by_cases hj0 : j = 0
    · simp [w, hj0, hxy.le]
    · by_cases hjlast : j = Fin.last S.cellCount
      · subst j
        simp [w, hkne, hxy.le]
      · simpa [w, hj0, hjlast] using hcI j
  have hwφ : ∀ j, φ (w j) = S.breakpoint j.rev := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp [w, S.breakpoint_last]
    · by_cases hjlast : j = Fin.last S.cellCount
      · subst j
        simp [w, hlastne, S.breakpoint_zero]
      · simpa [w, hj0, hjlast] using hcφ j
  have hwzero : w 0 = x := by simp [w]
  have hwlast : w (Fin.last S.cellCount) = y := by
    simp [w, hlastne]
  have hwStrict : StrictMono w := by
    intro i j hij
    have hrev : j.rev < i.rev := by simpa using hij
    apply lt_of_not_ge
    intro hji
    have himage_le : φ (w i) ≤ φ (w j) := hφ (hwI j) (hwI i) hji
    rw [hwφ i, hwφ j] at himage_le
    exact (not_lt_of_ge himage_le) (S.breakpoint_strictMono hrev)
  have hweak : ∀ i : Fin S.cellCount,
      IsWeaklyMonotoneOn (G ∘ φ) (Set.Icc (w i.castSucc) (w i.succ)) := by
    intro i
    let r : Fin S.cellCount := i.rev
    apply (S.weaklyMonotoneOn_cell r).comp
    · exact Or.inr <| hφ.mono fun z hz =>
        ⟨(hwI i.castSucc).1.trans hz.1,
          hz.2.trans (hwI i.succ).2⟩
    · intro z hz
      have hzI : z ∈ Set.Icc x y :=
        ⟨(hwI i.castSucc).1.trans hz.1,
          hz.2.trans (hwI i.succ).2⟩
      constructor
      · calc
          S.breakpoint r.castSucc = φ (w i.succ) := by
            simpa [r, Fin.rev_succ] using (hwφ i.succ).symm
          _ ≤ φ z := hφ hzI (hwI i.succ) hz.2
      · calc
          φ z ≤ φ (w i.castSucc) := hφ (hwI i.castSucc) hzI hz.1
          _ = S.breakpoint r.succ := by
            simpa [r, Fin.rev_castSucc] using hwφ i.castSucc
  let R : WeakLapSubdivision (G ∘ φ) x y :=
    { cellCount := S.cellCount
      breakpoint := w
      breakpoint_zero := hwzero
      breakpoint_last := hwlast
      breakpoint_strictMono := hwStrict
      weaklyMonotoneOn_cell := hweak }
  exact ⟨R, rfl⟩

/-- Transport through a weakly monotone first branch changes the next-level
minimal count by at most one.  The error includes the honest constant-image
case, where the target interval is degenerate. -/
theorem weakLapCountOn_succ_branch_error {T : IntervalMap}
    (hT : FinitePieceMonotone T) {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) (n : ℕ) :
    |(weakLapCountOn T (n + 1) x y : ℤ) -
        weakLapCountOn T n (min (T x) (T y)) (max (T x) (T y))| ≤ 1 := by
  let G : IntervalMap := iterateMap T n
  have hG : FinitePieceMonotone G := hT.iterate n
  have hcomp : FinitePieceMonotone (G ∘ T) := hG.comp hT
  have hiter : iterateMap T (n + 1) = G ∘ T := by
    funext z
    simp [G, iterateMap, Function.iterate_succ_apply]
  rcases hmono with hinc | hdec
  · have hends : T x ≤ T y :=
      hinc ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
    by_cases heq : T x = T y
    · have hconst : ∀ z ∈ Set.Icc x y, T z = T x := by
        intro z hz
        apply le_antisymm
        · simpa [heq] using hinc hz ⟨hxy.le, le_rfl⟩ hz.2
        · exact hinc ⟨le_rfl, hxy.le⟩ hz hz.1
      have hweakComp : IsWeaklyMonotoneOn (G ∘ T) (Set.Icc x y) := by
        left
        intro a ha b hb _hab
        simp only [Function.comp_apply]
        rw [hconst a ha, hconst b hb]
      have hsource : weakLapCountOn T (n + 1) x y = 1 := by
        change weakLapCountOf (iterateMap T (n + 1)) x y = 1
        rw [hiter]
        exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
          hcomp hxy hweakComp
      have htarget : weakLapCountOn T n
          (min (T x) (T y)) (max (T x) (T y)) = 0 := by
        simp [heq, weakLapCountOn, weakLapCountOf]
      rw [hsource, htarget]
      norm_num
    · have hstrict : T x < T y := lt_of_le_of_ne hends heq
      have hforward : weakLapCountOf (G ∘ T) x y ≤
          weakLapCountOf G (T x) (T y) := by
        rcases weakLapCountOf_attained hG hstrict with ⟨S, hS⟩
        rcases S.pull_monotoneOn hxy hT.continuous hinc hstrict with
          ⟨R, hR⟩
        calc
          weakLapCountOf (G ∘ T) x y ≤ R.cellCount :=
            weakLapCountOf_minimal hcomp hxy R
          _ = S.cellCount := hR
          _ = weakLapCountOf G (T x) (T y) := hS
      have hbackward : weakLapCountOf G (T x) (T y) ≤
          weakLapCountOf (G ∘ T) x y := by
        rcases weakLapCountOf_attained hcomp hxy with ⟨R, hR⟩
        rcases R.push_monotoneOn hxy hT.continuous hinc hstrict with
          ⟨Q, hQ⟩
        calc
          weakLapCountOf G (T x) (T y) ≤ Q.cellCount :=
            weakLapCountOf_minimal hG hstrict Q
          _ ≤ R.cellCount := hQ
          _ = weakLapCountOf (G ∘ T) x y := hR
      have hequal : weakLapCountOn T (n + 1) x y =
          weakLapCountOn T n (T x) (T y) := by
        change weakLapCountOf (iterateMap T (n + 1)) x y =
          weakLapCountOf G (T x) (T y)
        rw [hiter]
        exact le_antisymm hforward hbackward
      rw [min_eq_left hends, max_eq_right hends, hequal]
      norm_num
  · have hends : T y ≤ T x :=
      hdec ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
    by_cases heq : T x = T y
    · have hconst : ∀ z ∈ Set.Icc x y, T z = T x := by
        intro z hz
        apply le_antisymm
        · exact hdec ⟨le_rfl, hxy.le⟩ hz hz.1
        · simpa [heq] using hdec hz ⟨hxy.le, le_rfl⟩ hz.2
      have hweakComp : IsWeaklyMonotoneOn (G ∘ T) (Set.Icc x y) := by
        left
        intro a ha b hb _hab
        simp only [Function.comp_apply]
        rw [hconst a ha, hconst b hb]
      have hsource : weakLapCountOn T (n + 1) x y = 1 := by
        change weakLapCountOf (iterateMap T (n + 1)) x y = 1
        rw [hiter]
        exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
          hcomp hxy hweakComp
      have htarget : weakLapCountOn T n
          (min (T x) (T y)) (max (T x) (T y)) = 0 := by
        simp [heq, weakLapCountOn, weakLapCountOf]
      rw [hsource, htarget]
      norm_num
    · have hne : T y ≠ T x := fun h => heq h.symm
      have hstrict : T y < T x := lt_of_le_of_ne hends hne
      have hforward : weakLapCountOf (G ∘ T) x y ≤
          weakLapCountOf G (T y) (T x) := by
        rcases weakLapCountOf_attained hG hstrict with ⟨S, hS⟩
        rcases S.pull_antitoneOn hxy hT.continuous hdec hstrict with
          ⟨R, hR⟩
        calc
          weakLapCountOf (G ∘ T) x y ≤ R.cellCount :=
            weakLapCountOf_minimal hcomp hxy R
          _ = S.cellCount := hR
          _ = weakLapCountOf G (T y) (T x) := hS
      have hbackward : weakLapCountOf G (T y) (T x) ≤
          weakLapCountOf (G ∘ T) x y := by
        rcases weakLapCountOf_attained hcomp hxy with ⟨R, hR⟩
        rcases R.push_antitoneOn hxy hT.continuous hdec hstrict with
          ⟨Q, hQ⟩
        calc
          weakLapCountOf G (T y) (T x) ≤ Q.cellCount :=
            weakLapCountOf_minimal hG hstrict Q
          _ ≤ R.cellCount := hQ
          _ = weakLapCountOf (G ∘ T) x y := hR
      have hequal : weakLapCountOn T (n + 1) x y =
          weakLapCountOn T n (T y) (T x) := by
        change weakLapCountOf (iterateMap T (n + 1)) x y =
          weakLapCountOf G (T y) (T x)
        rw [hiter]
        exact le_antisymm hforward hbackward
      rw [min_eq_right hends, max_eq_left hends, hequal]
      norm_num

/-- Concatenate a nonempty chain of adjacent subdivisions, retaining a
uniform bound on the number of cells contributed by each link. -/
private theorem weakLapSubdivision_concatChain_bounded {F : IntervalMap} :
    ∀ k : ℕ, ∀ (p : Fin (k + 2) → I), StrictMono p →
      ∀ (Q : ∀ i : Fin (k + 1),
        WeakLapSubdivision F (p i.castSucc) (p i.succ)),
      ∀ L : ℕ, (∀ i, (Q i).cellCount ≤ L) →
        ∃ R : WeakLapSubdivision F (p 0) (p (Fin.last (k + 1))),
          R.cellCount ≤ (k + 1) * L := by
  intro k
  induction k with
  | zero =>
      intro p hp Q L hQ
      let R : WeakLapSubdivision F (p 0) (p (Fin.last 1)) := by
        simpa using Q 0
      refine ⟨R, ?_⟩
      simpa [R] using hQ 0
  | succ k ih =>
      intro p hp Q L hQ
      let p' : Fin (k + 2) → I := fun i => p i.succ
      have hp' : StrictMono p' := by
        intro i j hij
        exact hp (by simpa [p'] using hij)
      let Q' : ∀ i : Fin (k + 1),
          WeakLapSubdivision F (p' i.castSucc) (p' i.succ) := fun i => by
        simpa [p'] using Q i.succ
      have hQ' : ∀ i, (Q' i).cellCount ≤ L := by
        intro i
        simpa [Q'] using hQ i.succ
      rcases ih p' hp' Q' L hQ' with ⟨Rtail, hRtail⟩
      have hfirst : p 0 < p 1 := hp (by simp)
      have htail : p' 0 < p' (Fin.last (k + 1)) := by
        apply hp
        change (1 : ℕ) < k + 2
        omega
      rcases (Q 0).concat Rtail hfirst htail with ⟨R, hR⟩
      have hbound : R.cellCount ≤ (k + 2) * L := by
        calc
          R.cellCount ≤ (Q 0).cellCount + Rtail.cellCount := hR
          _ ≤ L + (k + 1) * L := Nat.add_le_add (hQ 0) hRtail
          _ = (k + 2) * L := by
            simp [Nat.add_mul]
            omega
      simpa [p'] using
        (show ∃ R : WeakLapSubdivision F (p 0) (p' (Fin.last (k + 1))),
            R.cellCount ≤ (k + 2) * L from ⟨R, hbound⟩)

private theorem weakLapSubdivision_concatChain_bounded_of_pos
    {F : IntervalMap} {k : ℕ} (hk : 0 < k)
    (p : Fin (k + 1) → I) (hp : StrictMono p)
    (Q : ∀ i : Fin k,
      WeakLapSubdivision F (p i.castSucc) (p i.succ))
    (L : ℕ) (hQ : ∀ i, (Q i).cellCount ≤ L) :
    ∃ R : WeakLapSubdivision F (p 0) (p (Fin.last k)),
      R.cellCount ≤ k * L := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt hk)
  simpa using weakLapSubdivision_concatChain_bounded j p hp Q L hQ

/-- Minimal total weak-lap counts are submultiplicative under iteration. -/
theorem weakLapCount_submultiplicative {T : IntervalMap}
    (hT : FinitePieceMonotone T) (m n : ℕ) :
    weakLapCount T (m + n) ≤ weakLapCount T m * weakLapCount T n := by
  let F : IntervalMap := iterateMap T m
  let φ : IntervalMap := iterateMap T n
  have hF : FinitePieceMonotone F := hT.iterate m
  have hφ : FinitePieceMonotone φ := hT.iterate n
  have hcomp : FinitePieceMonotone (F ∘ φ) := hF.comp hφ
  have hiter : iterateMap T (m + n) = F ∘ φ := by
    funext z
    simp [F, φ, iterateMap, Function.iterate_add_apply]
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  rcases weakLapCountOf_attained hF hends with ⟨Sm, hSm⟩
  rcases weakLapCountOf_attained hφ hends with ⟨Sn, hSn⟩
  have hSm' : Sm.cellCount = weakLapCount T m := by
    simpa [F, weakLapCount, weakLapCountOn] using hSm
  have hSn' : Sn.cellCount = weakLapCount T n := by
    simpa [φ, weakLapCount, weakLapCountOn] using hSn
  have hSmpos : 0 < Sm.cellCount := by
    rw [hSm]
    exact weakLapCountOf_pos hF hends
  have hrefine : ∀ i : Fin Sn.cellCount,
      ∃ Q : WeakLapSubdivision (F ∘ φ)
          (Sn.breakpoint i.castSucc) (Sn.breakpoint i.succ),
        Q.cellCount ≤ Sm.cellCount := by
    intro i
    let a := Sn.breakpoint i.castSucc
    let b := Sn.breakpoint i.succ
    have hab : a < b := Sn.breakpoint_strictMono (by simp [a, b])
    rcases Sn.weaklyMonotoneOn_cell i with hinc | hdec
    · have hφends : φ a ≤ φ b :=
        hinc ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
      by_cases heq : φ a = φ b
      · have hconst : ∀ z ∈ Set.Icc a b, φ z = φ a := by
          intro z hz
          apply le_antisymm
          · simpa [heq] using hinc hz ⟨hab.le, le_rfl⟩ hz.2
          · exact hinc ⟨le_rfl, hab.le⟩ hz hz.1
        have hweakComp :
            IsWeaklyMonotoneOn (F ∘ φ) (Set.Icc a b) := by
          left
          intro x hx y hy _hxy
          simp only [Function.comp_apply]
          rw [hconst x hx, hconst y hy]
        rcases weakLapCountOf_attained hcomp hab with ⟨Q, hQ⟩
        have hQone : Q.cellCount = 1 := by
          rw [hQ]
          exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
            hcomp hab hweakComp
        refine ⟨Q, ?_⟩
        rw [hQone]
        exact hSmpos
      · have hstrict : φ a < φ b := lt_of_le_of_ne hφends heq
        rcases weakLapCountOf_attained hF hstrict with ⟨A, hA⟩
        rcases A.pull_monotoneOn hab hφ.1 hinc hstrict with ⟨Q, hQ⟩
        refine ⟨Q, ?_⟩
        calc
          Q.cellCount = A.cellCount := hQ
          _ = weakLapCountOn T m (φ a) (φ b) := by
            simpa [F, weakLapCountOn] using hA
          _ ≤ weakLapCount T m := weakLapCountOn_le_total hT m _ _
          _ = Sm.cellCount := hSm'.symm
    · have hφends : φ b ≤ φ a :=
        hdec ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
      by_cases heq : φ a = φ b
      · have hconst : ∀ z ∈ Set.Icc a b, φ z = φ a := by
          intro z hz
          apply le_antisymm
          · exact hdec ⟨le_rfl, hab.le⟩ hz hz.1
          · simpa [heq] using hdec hz ⟨hab.le, le_rfl⟩ hz.2
        have hweakComp :
            IsWeaklyMonotoneOn (F ∘ φ) (Set.Icc a b) := by
          left
          intro x hx y hy _hxy
          simp only [Function.comp_apply]
          rw [hconst x hx, hconst y hy]
        rcases weakLapCountOf_attained hcomp hab with ⟨Q, hQ⟩
        have hQone : Q.cellCount = 1 := by
          rw [hQ]
          exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
            hcomp hab hweakComp
        refine ⟨Q, ?_⟩
        rw [hQone]
        exact hSmpos
      · have hne : φ b ≠ φ a := fun h => heq h.symm
        have hstrict : φ b < φ a := lt_of_le_of_ne hφends hne
        rcases weakLapCountOf_attained hF hstrict with ⟨A, hA⟩
        rcases A.pull_antitoneOn hab hφ.1 hdec hstrict with ⟨Q, hQ⟩
        refine ⟨Q, ?_⟩
        calc
          Q.cellCount = A.cellCount := hQ
          _ = weakLapCountOn T m (φ b) (φ a) := by
            simpa [F, weakLapCountOn] using hA
          _ ≤ weakLapCount T m := weakLapCountOn_le_total hT m _ _
          _ = Sm.cellCount := hSm'.symm
  choose Q hQ using hrefine
  have hSnpos : 0 < Sn.cellCount := by
    rw [hSn]
    exact weakLapCountOf_pos hφ hends
  rcases weakLapSubdivision_concatChain_bounded_of_pos hSnpos
      Sn.breakpoint Sn.breakpoint_strictMono Q Sm.cellCount hQ with
    ⟨R, hR⟩
  have hassembled :
      ∃ R' : WeakLapSubdivision (F ∘ φ) leftEndpoint rightEndpoint,
        R'.cellCount ≤ Sn.cellCount * Sm.cellCount := by
    let R' : WeakLapSubdivision (F ∘ φ) leftEndpoint rightEndpoint :=
      { cellCount := R.cellCount
        breakpoint := R.breakpoint
        breakpoint_zero := R.breakpoint_zero.trans Sn.breakpoint_zero
        breakpoint_last := R.breakpoint_last.trans Sn.breakpoint_last
        breakpoint_strictMono := R.breakpoint_strictMono
        weaklyMonotoneOn_cell := R.weaklyMonotoneOn_cell }
    exact ⟨R', by simpa [R'] using hR⟩
  rcases hassembled with ⟨R', hR'⟩
  change weakLapCountOf (iterateMap T (m + n))
      leftEndpoint rightEndpoint ≤
    weakLapCount T m * weakLapCount T n
  rw [hiter]
  calc
    weakLapCountOf (F ∘ φ) leftEndpoint rightEndpoint ≤ R'.cellCount :=
      weakLapCountOf_minimal hcomp hends R'
    _ ≤ Sn.cellCount * Sm.cellCount := hR'
    _ = Sm.cellCount * Sn.cellCount := Nat.mul_comm _ _
    _ = weakLapCount T m * weakLapCount T n := by rw [hSm', hSn']

/-- A fixed finite weak-monotonicity partition supplies an exponential upper
bound for the minimal iterate counts. -/
theorem weakLapCount_exponential_upper {T : IntervalMap}
    (hT : FinitePieceMonotone T) :
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℕ, weakLapCount T n ≤ q ^ n := by
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  let q := weakLapCount T 1
  have hq : 0 < q := by
    change 0 < weakLapCountOf (iterateMap T 1)
      leftEndpoint rightEndpoint
    exact weakLapCountOf_pos (hT.iterate 1) hends
  have hzero : weakLapCount T 0 = 1 := by
    change weakLapCountOf (iterateMap T 0)
      leftEndpoint rightEndpoint = 1
    apply weakLapCountOf_eq_one_of_weaklyMonotoneOn
      (hT.iterate 0) hends
    left
    intro x _hx y _hy hxy
    simpa [iterateMap] using hxy
  refine ⟨q, hq, ?_⟩
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      calc
        weakLapCount T (n + 1) ≤
            weakLapCount T n * weakLapCount T 1 := by
          simpa using weakLapCount_submultiplicative hT n 1
        _ ≤ q ^ n * q := Nat.mul_le_mul ih (le_refl q)
        _ = q ^ (n + 1) := by simp [pow_succ]

/-- An interval follows one weak branch for each of its first `m` images.
This prefix condition is strictly stronger than merely asking the final
iterate to be weakly monotone: a final iterate can be monotone even when an
earlier image crosses a fold. -/
def IsWeakItineraryCell (T : IntervalMap) (m : ℕ) (x y : I) : Prop :=
  ∀ k < m,
    IsWeaklyMonotoneOn T
      (Set.Icc
        (min (iterateMap T k x) (iterateMap T k y))
        (max (iterateMap T k x) (iterateMap T k y)))

/-- A recursive composition refinement whose every subinterval follows one
weak branch through the indicated finite itinerary. -/
private theorem weakItineraryPartition_exists
    {T : IntervalMap} (hT : FinitePieceMonotone T) :
    ∀ m : ℕ,
      ∃ w : MonotonicityPartition (iterateMap T m),
        ∀ {a b : ℝ}, w.partition.Adjacent a b →
          ∀ x ∈ intervalCell a b, ∀ y ∈ intervalCell a b,
            IsWeakItineraryCell T m x y := by
  let wT : MonotonicityPartition T := Classical.choice hT.2
  intro m
  induction m with
  | zero =>
      let w₀ : MonotonicityPartition (iterateMap T 0) :=
        Classical.choice (hT.iterate 0).2
      refine ⟨w₀, ?_⟩
      intro a b hab x hx y hy k hk
      omega
  | succ m ih =>
      rcases ih with ⟨w, hw⟩
      let p := wT.compositionRefinement w
      have hiter : iterateMap T (m + 1) = iterateMap T m ∘ T := by
        funext z
        simp [iterateMap, Function.iterate_succ_apply]
      let w' : MonotonicityPartition (iterateMap T (m + 1)) :=
        { partition := p
          weaklyMonotoneOn_cell := by
            intro a b hab
            change p.Adjacent a b at hab
            rcases wT.composition_cell hT.1 w hab with
              ⟨hsource, c, d, hcd, hmaps⟩
            rw [hiter]
            exact (w.weaklyMonotoneOn_cell hcd).comp hsource hmaps }
      refine ⟨w', ?_⟩
      intro a b hab x hx y hy k hk
      change p.Adjacent a b at hab
      rcases wT.composition_cell hT.1 w hab with
        ⟨hsource, c, d, hcd, hmaps⟩
      cases k with
      | zero =>
          have hsub : Set.Icc (min x y) (max x y) ⊆
              intervalCell a b := by
            intro z hz
            change a ≤ (z : ℝ) ∧ (z : ℝ) ≤ b
            constructor
            · calc
                a ≤ min (x : ℝ) (y : ℝ) := le_min hx.1 hy.1
                _ ≤ (z : ℝ) := by simpa using hz.1
            · calc
                (z : ℝ) ≤ max (x : ℝ) (y : ℝ) := by
                  simpa using hz.2
                _ ≤ b := max_le hx.2 hy.2
          simpa [iterateMap] using hsource.mono hsub
      | succ k =>
          have hk' : k < m := Nat.lt_of_succ_lt_succ hk
          have hprev := hw hcd (T x) (hmaps hx) (T y) (hmaps hy) k hk'
          simpa [iterateMap, Function.iterate_succ_apply] using hprev

/-- A finite subset of the interval has cut-free one-sided neighborhoods at
every point, with the expected endpoint conventions. -/
private theorem finiteSet_twoSided_free (S : Set I) (hS : S.Finite)
    (x : I) :
    ∃ a b : I,
      a ≤ x ∧ x ≤ b ∧
      (leftEndpoint < x → a < x) ∧
      (x < rightEndpoint → x < b) ∧
      S ∩ Set.Ioo a x = ∅ ∧
      S ∩ Set.Ioo x b = ∅ := by
  let S' : Set I := S \ ({x} : Set I)
  let U : Set I := S'ᶜ
  have hS'finite : S'.Finite := by
    dsimp [S']
    exact hS.diff
  have hUopen : IsOpen U := hS'finite.isClosed.isOpen_compl
  have hxU : x ∈ U := by simp [U, S']
  have hUmem : U ∈ nhds x := hUopen.mem_nhds hxU
  have free_of_subset {a b : I} (hsub : Set.Ioo a b ⊆ U)
      (hne : ∀ q ∈ Set.Ioo a b, q ≠ x) :
      S ∩ Set.Ioo a b = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqU := hsub hq.2
    exact hqU ⟨hq.1, by simpa using hne q hq.2⟩
  by_cases hxl : x = leftEndpoint
  · subst x
    obtain ⟨b, hlb, hsub⟩ := exists_Ico_subset_of_mem_nhds hUmem
      ⟨rightEndpoint, by norm_num [leftEndpoint, rightEndpoint]⟩
    refine ⟨leftEndpoint, b, le_rfl, hlb.le, ?_, ?_, ?_, ?_⟩
    · intro h
      exact (lt_irrefl leftEndpoint h).elim
    · intro _
      exact hlb
    · simp
    · apply free_of_subset
      · intro q hq
        exact hsub ⟨hq.1.le, hq.2⟩
      · intro q hq hqeq
        subst q
        exact (lt_irrefl leftEndpoint) hq.1
  · by_cases hxr : x = rightEndpoint
    · subst x
      obtain ⟨a, har, hsub⟩ := exists_Ioc_subset_of_mem_nhds hUmem
        ⟨leftEndpoint, by norm_num [leftEndpoint, rightEndpoint]⟩
      refine ⟨a, rightEndpoint, har.le, le_rfl, ?_, ?_, ?_, ?_⟩
      · intro _
        exact har
      · intro h
        exact (lt_irrefl rightEndpoint h).elim
      · apply free_of_subset
        · intro q hq
          exact hsub ⟨hq.1, hq.2.le⟩
        · intro q hq hqeq
          subst q
          exact (lt_irrefl rightEndpoint) hq.2
      · simp
    · have hlx : leftEndpoint < x :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxl)
      have hxr' : x < rightEndpoint :=
        lt_of_le_of_ne x.property.2 hxr
      obtain ⟨a, b, hxab, hsub⟩ :=
        (mem_nhds_iff_exists_Ioo_subset'
          ⟨leftEndpoint, hlx⟩ ⟨rightEndpoint, hxr'⟩).mp hUmem
      refine ⟨a, b, hxab.1.le, hxab.2.le, fun _ => hxab.1,
        fun _ => hxab.2, ?_, ?_⟩
      · apply free_of_subset
        · intro q hq
          exact hsub ⟨hq.1, hq.2.trans hxab.2⟩
        · intro q hq hqeq
          subst q
          exact (lt_irrefl x) hq.2
      · apply free_of_subset
        · intro q hq
          exact hsub ⟨hxab.1.trans hq.1, hq.2⟩
        · intro q hq hqeq
          subst q
          exact (lt_irrefl x) hq.1

/-- Finite itinerary refinements give genuine two-sided itinerary cells at
every point. -/
theorem exists_twoSided_weakItineraryCell
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (m : ℕ) (x : I) :
    ∃ a b : I, a ≤ x ∧ x ≤ b ∧
      (leftEndpoint < x → a < x) ∧
      (x < rightEndpoint → x < b) ∧
      IsWeakItineraryCell T m a x ∧
      IsWeakItineraryCell T m x b := by
  classical
  rcases weakItineraryPartition_exists hT m with ⟨w, hw⟩
  let P : Set I := {z | (z : ℝ) ∈ w.partition.points}
  have hPfinite : P.Finite := by
    have hreal : ({z : ℝ | z ∈ w.partition.points} : Set ℝ).Finite :=
      w.partition.points.finite_toSet
    change (((↑) : I → ℝ) ⁻¹' {z : ℝ | z ∈ w.partition.points}).Finite
    exact Set.Finite.preimage
      (Set.injOn_of_injective Subtype.val_injective) hreal
  rcases finiteSet_twoSided_free P hPfinite x with
    ⟨a, b, hax, hxb, haleft, haright, hfreeLeft, hfreeRight⟩
  have itinerary_of_free {u v : I} (huv : u ≤ v)
      (hfree : P ∩ Set.Ioo u v = ∅) :
      IsWeakItineraryCell T m u v := by
    by_cases heq : u = v
    · subst v
      rcases w.partition.exists_adjacent_containing u with
        ⟨c, d, hcd, hu⟩
      exact hw hcd u hu u hu
    · have huv' : u < v := lt_of_le_of_ne huv heq
      have hnone : ∀ r ∈ w.partition.points,
          ¬((u : ℝ) < r ∧ r < (v : ℝ)) := by
        intro r hr hbetween
        let z : I := ⟨r, w.partition.points_subset hr⟩
        have hz : z ∈ P ∩ Set.Ioo u v := by
          constructor
          · simpa [P, z] using hr
          · simpa [z] using hbetween
        rw [hfree] at hz
        exact hz
      rcases w.partition.exists_adjacent_superset
          u.property v.property huv' hnone with ⟨c, d, hcd, hsub⟩
      exact hw hcd u (hsub ⟨le_rfl, huv⟩)
        v (hsub ⟨huv, le_rfl⟩)
  exact ⟨a, b, hax, hxb, haleft, haright,
    itinerary_of_free hax hfreeLeft,
    itinerary_of_free hxb hfreeRight⟩

/-! ## Plateau-regular targets and horseshoe growth -/

/-- Values attained on a nondegenerate interval on which `F` is constant. -/
def intrinsicPlateauValues (F : IntervalMap) : Set I :=
  {v | ∃ x y : I, x < y ∧ ∀ z ∈ Set.Icc x y, F z = v}

/-- The plateau values of a finite-piece weakly monotone map are countable. -/
theorem intrinsicPlateauValues_countable {F : IntervalMap}
    (hF : FinitePieceMonotone F) :
    (intrinsicPlateauValues F).Countable := by
  classical
  let V := intrinsicPlateauValues F
  have hexists : ∀ v : V,
      ∃ x y : I, x < y ∧ ∀ z ∈ Set.Icc x y, F z = (v : I) := by
    intro v
    exact v.property
  choose a b hab hconst using hexists
  let U : V → Set I := fun v => Set.Ioo (a v) (b v)
  have hdisj : Pairwise (Disjoint on U) := by
    intro v w hvw
    change Disjoint (U v) (U w)
    rw [Set.disjoint_left]
    intro z hzv hzw
    apply hvw
    apply Subtype.ext
    calc
      (v : I) = F z := (hconst v z ⟨hzv.1.le, hzv.2.le⟩).symm
      _ = (w : I) := hconst w z ⟨hzw.1.le, hzw.2.le⟩
  have hopen : ∀ v, IsOpen (U v) := fun _ => isOpen_Ioo
  have hnonempty : ∀ v, (U v).Nonempty := fun v =>
    Set.nonempty_Ioo.mpr (hab v)
  have hcount : Countable V :=
    hdisj.countable_of_isOpen_disjoint hopen hnonempty
  exact Set.countable_coe_iff.mp hcount

/-- Plateau values of all iterates. -/
def iteratedPlateauValues (T : IntervalMap) : Set I :=
  ⋃ n : ℕ, intrinsicPlateauValues (iterateMap T n)

/-- The union of plateau values over all iterates is countable. -/
theorem iteratedPlateauValues_countable {T : IntervalMap}
    (hT : FinitePieceMonotone T) :
    (iteratedPlateauValues T).Countable := by
  unfold iteratedPlateauValues
  exact Set.countable_iUnion fun n =>
    intrinsicPlateauValues_countable (hT.iterate n)

/-- A nondegenerate horseshoe hull contains a target which is not a plateau
value of any iterate. -/
theorem exists_regular_target_in_horseshoe {T : IntervalMap}
    (hT : FinitePieceMonotone T) (H : TwoBranchHorseshoe T) :
    ∃ y : I, y ∈ Set.Ioo H.a H.d ∧ y ∉ iteratedPlateauValues T := by
  let C : Set ℝ := ((↑) : I → ℝ) '' iteratedPlateauValues T
  have hC : C.Countable :=
    (iteratedPlateauValues_countable hT).image ((↑) : I → ℝ)
  have had : H.a < H.d :=
    (H.a_lt_b.trans H.b_lt_c).trans H.c_lt_d
  have hIoo : ¬(Set.Ioo (H.a : ℝ) (H.d : ℝ)).Countable := by
    intro hcount
    have hcard := Cardinal.le_aleph0_iff_set_countable.mpr hcount
    rw [Cardinal.mk_Ioo_real had] at hcard
    exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hcard
  have hnsub : ¬Set.Ioo (H.a : ℝ) (H.d : ℝ) ⊆ C := by
    intro hsub
    exact hIoo (hC.mono hsub)
  rcases Set.not_subset.mp hnsub with ⟨r, hr, hrC⟩
  have hrI : r ∈ I :=
    ⟨H.a.property.1.trans hr.1.le, hr.2.le.trans H.d.property.2⟩
  let y : I := ⟨r, hrI⟩
  refine ⟨y, ?_, ?_⟩
  · simpa [y] using hr
  · intro hy
    apply hrC
    exact ⟨y, hy, rfl⟩

/-- The fibre of the `n`-th iterate above `y`. -/
def iterateFibre (T : IntervalMap) (y : I) (n : ℕ) : Set I :=
  (iterateMap T n) ⁻¹' {y}

private theorem WeakLapSubdivision.exists_mem_cell {F : IntervalMap}
    {a b : I} (S : WeakLapSubdivision F a b) (hpos : 0 < S.cellCount)
    {z : I} (hz : z ∈ Set.Icc a b) :
    ∃ i : Fin S.cellCount,
      z ∈ Set.Icc (S.breakpoint i.castSucc) (S.breakpoint i.succ) := by
  let p : Fin (S.cellCount + 1) → Prop := fun j =>
    z ≤ S.breakpoint j
  have hp : ∃ j, p j := by
    refine ⟨Fin.last S.cellCount, ?_⟩
    change z ≤ S.breakpoint (Fin.last S.cellCount)
    simpa [S.breakpoint_last] using hz.2
  let j : Fin (S.cellCount + 1) := Fin.find p hp
  have hjp : p j := Fin.find_spec hp
  by_cases hj0 : j = 0
  · let i : Fin S.cellCount := ⟨0, hpos⟩
    refine ⟨i, ?_⟩
    constructor
    · calc
        S.breakpoint i.castSucc = a := by simp [i, S.breakpoint_zero]
        _ ≤ z := hz.1
    · have hz0 : z ≤ S.breakpoint 0 := by
        change z ≤ S.breakpoint j at hjp
        simpa [hj0] using hjp
      exact hz0.trans
        (S.breakpoint_strictMono.monotone (by simp [i]))
  · obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero hj0
    have hilj : i.castSucc < j := by
      rw [← hi]
      simp
    have hnot : ¬p i.castSucc := Fin.find_min hp hilj
    have hlower : S.breakpoint i.castSucc ≤ z := by
      change ¬z ≤ S.breakpoint i.castSucc at hnot
      exact (lt_of_not_ge hnot).le
    have hupper : z ≤ S.breakpoint i.succ := by
      change z ≤ S.breakpoint j at hjp
      simpa [hi] using hjp
    exact ⟨i, hlower, hupper⟩

private theorem intrinsicPlateauValue_of_eq_on_weakLap
    {F : IntervalMap} {a b x z : I}
    (hweak : IsWeaklyMonotoneOn F (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hxz : x < z) (heq : F x = F z) :
    F x ∈ intrinsicPlateauValues F := by
  refine ⟨x, z, hxz, ?_⟩
  intro w hw
  have hwcell : w ∈ Set.Icc a b :=
    ⟨hx.1.trans hw.1, hw.2.trans hz.2⟩
  rcases hweak with hinc | hdec
  · apply le_antisymm
    · simpa [heq] using hinc hwcell hz hw.2
    · exact hinc hx hwcell hw.1
  · apply le_antisymm
    · exact hdec hx hwcell hw.1
    · simpa [heq] using hdec hwcell hz hw.2

/-- A target avoiding all iterate plateau values has finite iterate fibres.
This is a conclusion, not a hypothesis of the resolvent construction. -/
theorem iterateFibre_finite_of_regular {T : IntervalMap}
    (hT : FinitePieceMonotone T) {y : I}
    (hy : y ∉ iteratedPlateauValues T) (n : ℕ) :
    (iterateFibre T y n).Finite := by
  let F : IntervalMap := iterateMap T n
  have hF : FinitePieceMonotone F := hT.iterate n
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  rcases weakLapCountOf_attained hF hends with ⟨S, hS⟩
  have hSpos : 0 < S.cellCount := by
    rw [hS]
    exact weakLapCountOf_pos hF hends
  have hregular : y ∉ intrinsicPlateauValues F := by
    intro hplateau
    apply hy
    apply Set.mem_iUnion.mpr
    exact ⟨n, by simpa [F] using hplateau⟩
  let A : Fin S.cellCount → Set I := fun i =>
    iterateFibre T y n ∩
      Set.Icc (S.breakpoint i.castSucc) (S.breakpoint i.succ)
  have hA_subsingleton : ∀ i, (A i).Subsingleton := by
    intro i x hx z hz
    rcases hx with ⟨hxFibre, hxCell⟩
    rcases hz with ⟨hzFibre, hzCell⟩
    have hFx : F x = y := by
      simpa [iterateFibre, F] using hxFibre
    have hFz : F z = y := by
      simpa [iterateFibre, F] using hzFibre
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxz | hzx
    · have hplateau := intrinsicPlateauValue_of_eq_on_weakLap
          (S.weaklyMonotoneOn_cell i) hxCell hzCell hxz
          (hFx.trans hFz.symm)
      apply hregular
      simpa [hFx] using hplateau
    · have hplateau := intrinsicPlateauValue_of_eq_on_weakLap
          (S.weaklyMonotoneOn_cell i) hzCell hxCell hzx
          (hFz.trans hFx.symm)
      apply hregular
      simpa [hFz] using hplateau
  have hdecomp : iterateFibre T y n = ⋃ i, A i := by
    ext z
    constructor
    · intro hz
      rcases S.exists_mem_cell hSpos
          ⟨z.property.1, z.property.2⟩ with ⟨i, hzi⟩
      exact Set.mem_iUnion.mpr ⟨i, hz, hzi⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
      exact hzi.1
  rw [hdecomp]
  apply Set.finite_iUnion
  intro i
  exact (hA_subsingleton i).finite

/-- At a plateau-regular target, each minimal weak lap contains at most one
fibre point. -/
theorem iterateFibre_ncard_le_weakLapCount {T : IntervalMap}
    (hT : FinitePieceMonotone T) {y : I}
    (hy : y ∉ iteratedPlateauValues T) (n : ℕ) :
    (iterateFibre T y n).ncard ≤ weakLapCount T n := by
  let F : IntervalMap := iterateMap T n
  have hF : FinitePieceMonotone F := hT.iterate n
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  rcases weakLapCountOf_attained hF hends with ⟨S, hS⟩
  have hSpos : 0 < S.cellCount := by
    rw [hS]
    exact weakLapCountOf_pos hF hends
  have hregular : y ∉ intrinsicPlateauValues F := by
    intro hplateau
    apply hy
    apply Set.mem_iUnion.mpr
    exact ⟨n, by simpa [F] using hplateau⟩
  let A : Fin S.cellCount → Set I := fun i =>
    iterateFibre T y n ∩
      Set.Icc (S.breakpoint i.castSucc) (S.breakpoint i.succ)
  have hA_subsingleton : ∀ i, (A i).Subsingleton := by
    intro i x hx z hz
    rcases hx with ⟨hxFibre, hxCell⟩
    rcases hz with ⟨hzFibre, hzCell⟩
    have hFx : F x = y := by
      simpa [iterateFibre, F] using hxFibre
    have hFz : F z = y := by
      simpa [iterateFibre, F] using hzFibre
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxz | hzx
    · have hplateau := intrinsicPlateauValue_of_eq_on_weakLap
          (S.weaklyMonotoneOn_cell i) hxCell hzCell hxz
          (hFx.trans hFz.symm)
      apply hregular
      simpa [hFx] using hplateau
    · have hplateau := intrinsicPlateauValue_of_eq_on_weakLap
          (S.weaklyMonotoneOn_cell i) hzCell hxCell hzx
          (hFz.trans hFx.symm)
      apply hregular
      simpa [hFz] using hplateau
  have hdecomp : iterateFibre T y n = ⋃ i, A i := by
    ext z
    constructor
    · intro hz
      rcases S.exists_mem_cell hSpos
          ⟨z.property.1, z.property.2⟩ with ⟨i, hzi⟩
      exact Set.mem_iUnion.mpr ⟨i, hz, hzi⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
      exact hzi.1
  calc
    (iterateFibre T y n).ncard = (⋃ i, A i).ncard :=
      congrArg Set.ncard hdecomp
    _ ≤ ∑ i, (A i).ncard := Set.ncard_iUnion_le_of_fintype A
    _ ≤ ∑ _i : Fin S.cellCount, 1 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply (Set.ncard_le_one (hA_subsingleton i).finite).2
      intro x hx z hz
      exact hA_subsingleton i hx hz
    _ = S.cellCount := by simp
    _ = weakLapCount T n := by
      simpa [F, weakLapCount, weakLapCountOn] using hS

/-- A covered interior target has an interior preimage in the covering
branch. -/
theorem exists_preimage_in_open_horseshoe_branch
    {F : IntervalMap} (hF : Continuous F)
    {a d l r : I} (had : a < d) (hlr : l < r)
    (hcover : IntervalCovers F l r a d)
    {y : I} (hy : y ∈ Set.Ioo a d) :
    ∃ x ∈ Set.Ioo l r, F x = y := by
  rcases hcover ⟨le_rfl, had.le⟩ with ⟨xa, hxa, hFxa⟩
  rcases hcover ⟨had.le, le_rfl⟩ with ⟨xd, hxd, hFxd⟩
  have hxane : xa ≠ xd := by
    intro h
    apply had.ne
    calc
      a = F xa := hFxa.symm
      _ = F xd := congrArg F h
      _ = d := hFxd
  rcases lt_or_gt_of_ne hxane with hxad | hxdxa
  · have hyvalues : y ∈ Set.Icc (F xa) (F xd) := by
      simpa [hFxa, hFxd] using
        (⟨hy.1.le, hy.2.le⟩ : y ∈ Set.Icc a d)
    rcases (intermediate_value_Icc hxad.le hF.continuousOn) hyvalues with
      ⟨x, hx, hFx⟩
    have hxane' : xa ≠ x := by
      intro h
      apply (ne_of_lt hy.1)
      calc
        a = F xa := hFxa.symm
        _ = F x := congrArg F h
        _ = y := hFx
    have hxxdne : x ≠ xd := by
      intro h
      apply (ne_of_lt hy.2)
      calc
        y = F x := hFx.symm
        _ = F xd := congrArg F h
        _ = d := hFxd
    have hxalt : xa < x := lt_of_le_of_ne hx.1 hxane'
    have hxxdlt : x < xd := lt_of_le_of_ne hx.2 hxxdne
    exact ⟨x, ⟨hxa.1.trans_lt hxalt, hxxdlt.trans_le hxd.2⟩, hFx⟩
  · have hyvalues : y ∈ Set.Icc (F xa) (F xd) := by
      simpa [hFxa, hFxd] using
        (⟨hy.1.le, hy.2.le⟩ : y ∈ Set.Icc a d)
    rcases (intermediate_value_Icc' hxdxa.le hF.continuousOn) hyvalues with
      ⟨x, hx, hFx⟩
    have hxdxne : xd ≠ x := by
      intro h
      apply (ne_of_gt hy.2)
      calc
        d = F xd := hFxd.symm
        _ = F x := congrArg F h
        _ = y := hFx
    have hxxane : x ≠ xa := by
      intro h
      apply (ne_of_gt hy.1)
      calc
        y = F x := hFx.symm
        _ = F xa := congrArg F h
        _ = a := hFxa
    have hxdxlt : xd < x := lt_of_le_of_ne hx.1 hxdxne
    have hxxalt : x < xa := lt_of_le_of_ne hx.2 hxxane
    exact ⟨x, ⟨hxd.1.trans_lt hxdxlt, hxxalt.trans_le hxa.2⟩, hFx⟩

/-- The two separated horseshoe branches give `2^n` distinct symbolic
preimages of every interior target. -/
theorem TwoBranchHorseshoe.symbolic_preimages
    {F : IntervalMap} (hF : Continuous F) (H : TwoBranchHorseshoe F) :
    ∀ n : ℕ, ∀ y ∈ Set.Ioo H.a H.d,
      ∃ E : Finset I, E.card = 2 ^ n ∧
        ∀ x ∈ E, iterateMap F n x = y ∧ x ∈ Set.Ioo H.a H.d := by
  intro n
  induction n with
  | zero =>
      intro y hy
      refine ⟨{y}, by simp, ?_⟩
      intro x hx
      have hxy : x = y := Finset.mem_singleton.mp hx
      subst x
      exact ⟨by simp [iterateMap], hy⟩
  | succ n ih =>
      intro y hy
      rcases ih y hy with ⟨E, hEcard, hE⟩
      have hleftExists : ∀ z : {z // z ∈ E},
          ∃ x ∈ Set.Ioo H.a H.b, F x = z := by
        intro z
        exact exists_preimage_in_open_horseshoe_branch hF
          ((H.a_lt_b.trans H.b_lt_c).trans H.c_lt_d) H.a_lt_b
          H.left_covers (hE z z.property).2
      have hrightExists : ∀ z : {z // z ∈ E},
          ∃ x ∈ Set.Ioo H.c H.d, F x = z := by
        intro z
        exact exists_preimage_in_open_horseshoe_branch hF
          ((H.a_lt_b.trans H.b_lt_c).trans H.c_lt_d) H.c_lt_d
          H.right_covers (hE z z.property).2
      let left : {z // z ∈ E} → I := fun z =>
        Classical.choose (hleftExists z)
      let right : {z // z ∈ E} → I := fun z =>
        Classical.choose (hrightExists z)
      have hleftMem (z : {z // z ∈ E}) : left z ∈ Set.Ioo H.a H.b :=
        (Classical.choose_spec (hleftExists z)).1
      have hleftMap (z : {z // z ∈ E}) : F (left z) = z :=
        (Classical.choose_spec (hleftExists z)).2
      have hrightMem (z : {z // z ∈ E}) : right z ∈ Set.Ioo H.c H.d :=
        (Classical.choose_spec (hrightExists z)).1
      have hrightMap (z : {z // z ∈ E}) : F (right z) = z :=
        (Classical.choose_spec (hrightExists z)).2
      have hleftInj : Function.Injective left := by
        intro z w hzw
        apply Subtype.ext
        calc
          (z : I) = F (left z) := (hleftMap z).symm
          _ = F (left w) := congrArg F hzw
          _ = (w : I) := hleftMap w
      have hrightInj : Function.Injective right := by
        intro z w hzw
        apply Subtype.ext
        calc
          (z : I) = F (right z) := (hrightMap z).symm
          _ = F (right w) := congrArg F hzw
          _ = (w : I) := hrightMap w
      let EL : Finset I := E.attach.image left
      let ER : Finset I := E.attach.image right
      have hELcard : EL.card = E.card := by
        simpa [EL] using
          (Finset.card_image_of_injective E.attach hleftInj)
      have hERcard : ER.card = E.card := by
        simpa [ER] using
          (Finset.card_image_of_injective E.attach hrightInj)
      have hdisj : Disjoint EL ER := by
        rw [Finset.disjoint_left]
        intro x hxL hxR
        rcases Finset.mem_image.mp hxL with ⟨z, _hz, hzx⟩
        rcases Finset.mem_image.mp hxR with ⟨w, _hw, hwx⟩
        have hxb : x < H.b := by
          rw [← hzx]
          exact (hleftMem z).2
        have hcx : H.c < x := by
          rw [← hwx]
          exact (hrightMem w).1
        exact (lt_irrefl x) ((hxb.trans H.b_lt_c).trans hcx)
      let E' : Finset I := EL ∪ ER
      have hE'card : E'.card = 2 ^ (n + 1) := by
        calc
          E'.card = EL.card + ER.card := by
            simpa [E'] using Finset.card_union_of_disjoint hdisj
          _ = E.card + E.card := by rw [hELcard, hERcard]
          _ = 2 ^ n + 2 ^ n := by rw [hEcard]
          _ = 2 ^ (n + 1) := by rw [pow_succ]; omega
      refine ⟨E', by simpa [Nat.succ_eq_add_one] using hE'card, ?_⟩
      intro x hx
      have hxunion : x ∈ EL ∪ ER := by simpa [E'] using hx
      rcases Finset.mem_union.mp hxunion with hxL | hxR
      · rcases Finset.mem_image.mp hxL with ⟨z, _hz, hzx⟩
        have hz := hE z z.property
        have hxhull : x ∈ Set.Ioo H.a H.d := by
          rw [← hzx]
          exact ⟨(hleftMem z).1,
            ((hleftMem z).2.trans H.b_lt_c).trans H.c_lt_d⟩
        constructor
        · rw [← hzx, iterateMap, Function.iterate_succ_apply, hleftMap z]
          exact hz.1
        · exact hxhull
      · rcases Finset.mem_image.mp hxR with ⟨z, _hz, hzx⟩
        have hz := hE z z.property
        have hxhull : x ∈ Set.Ioo H.a H.d := by
          rw [← hzx]
          exact ⟨(H.a_lt_b.trans H.b_lt_c).trans (hrightMem z).1,
            (hrightMem z).2⟩
        constructor
        · rw [← hzx, iterateMap, Function.iterate_succ_apply, hrightMap z]
          exact hz.1
        · exact hxhull

/-- The horseshoe forces exponential growth of the minimal weak-lap count;
the proof uses a plateau-regular target rather than a false global
finite-fibre assertion. -/
theorem weakLapCount_horseshoe_lower {T : IntervalMap}
    (hT : FinitePieceMonotone T) (H : TwoBranchHorseshoe T) (n : ℕ) :
    2 ^ n ≤ weakLapCount T n := by
  rcases exists_regular_target_in_horseshoe hT H with
    ⟨y, hyHull, hyregular⟩
  rcases H.symbolic_preimages hT.continuous n y hyHull with
    ⟨E, hEcard, hE⟩
  have hsub : (↑E : Set I) ⊆ iterateFibre T y n := by
    intro x hx
    have hxmap := (hE x hx).1
    simpa [iterateFibre] using hxmap
  have hfibre : (iterateFibre T y n).Finite :=
    iterateFibre_finite_of_regular hT hyregular n
  calc
    2 ^ n = E.card := hEcard.symm
    _ = (↑E : Set I).ncard := by simp
    _ ≤ (iterateFibre T y n).ncard :=
      Set.ncard_le_ncard hsub hfibre
    _ ≤ weakLapCount T n :=
      iterateFibre_ncard_le_weakLapCount hT hyregular n

/-! ## Radius and normalized weak-lap resolvents -/

/-- Exactly the growth information consumed by the analytic radius
construction. -/
structure WeakLapGrowthData (T : IntervalMap) where
  submultiplicative : ∀ m n : ℕ,
    weakLapCount T (m + n) ≤ weakLapCount T m * weakLapCount T n
  upperBase : ℕ
  upperBase_pos : 0 < upperBase
  upper_bound : ∀ n : ℕ, weakLapCount T n ≤ upperBase ^ n
  horse_lower : ∀ n : ℕ, 2 ^ n ≤ weakLapCount T n

/-- Assemble the weak-lap growth package. -/
theorem weakLapGrowthData_exists {T : IntervalMap}
    (hT : FinitePieceMonotone T) (H : TwoBranchHorseshoe T) :
    Nonempty (WeakLapGrowthData T) := by
  obtain ⟨q, hq, hupper⟩ := weakLapCount_exponential_upper hT
  exact ⟨{
    submultiplicative := weakLapCount_submultiplicative hT
    upperBase := q
    upperBase_pos := hq
    upper_bound := hupper
    horse_lower := weakLapCount_horseshoe_lower hT H
  }⟩

/-- Local weak-lap power series. -/
noncomputable def weakLapResolvent
    (T : IntervalMap) (x y : I) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (weakLapCountOn T n x y : ℝ) * t ^ n

/-- Total weak-lap power series. -/
noncomputable def weakTotalLapResolvent
    (T : IntervalMap) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (weakLapCount T n : ℝ) * t ^ n

/-- An approach from inside the positive convergence radius along which the
total resolvent diverges. -/
structure WeakLapRadiusData (T : IntervalMap) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le_half : radius ≤ 1 / 2
  sample : ℕ → ℝ
  sample_pos : ∀ n, 0 < sample n
  sample_lt_radius : ∀ n, sample n < radius
  sample_strictMono : StrictMono sample
  sample_tendsto : Tendsto sample atTop (𝓝 radius)
  series_summable : ∀ n, Summable
    (fun k : ℕ => (weakLapCount T k : ℝ) * sample n ^ k)
  total_tendsto : Tendsto
    (fun n => weakTotalLapResolvent T (sample n)) atTop atTop

private noncomputable def weakLapFormalSeries (T : IntervalMap) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (weakLapCount T n : ℝ))

/-- A block ratio test for nonnegative submultiplicative coefficients. -/
private theorem weakSummable_of_submultiplicative_block
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t)
    (hcontract : a N * t ^ N < 1) :
    Summable (fun n : ℕ => a n * t ^ n) := by
  let q := a N * t ^ N
  have hq0 : 0 ≤ q := mul_nonneg (ha N) (pow_nonneg ht N)
  have hblock : ∀ m k : ℕ, a (N * m + k) ≤ a N ^ m * a k := by
    intro m k
    induction m with
    | zero => simp [ha k]
    | succ m ih =>
        calc
          a (N * (m + 1) + k) = a (N + (N * m + k)) := by
            congr 1
            ring
          _ ≤ a N * a (N * m + k) := hsub N (N * m + k)
          _ ≤ a N * (a N ^ m * a k) :=
            mul_le_mul_of_nonneg_left ih (ha N)
          _ = a N ^ (m + 1) * a k := by ring
  have hstride : ∀ k : ℕ,
      Summable (fun m : ℕ => a (N * m + k) * t ^ (N * m + k)) := by
    intro k
    apply Summable.of_nonneg_of_le
      (f := fun m : ℕ => (a k * t ^ k) * q ^ m)
    · intro m
      exact mul_nonneg (ha _) (pow_nonneg ht _)
    · intro m
      calc
        a (N * m + k) * t ^ (N * m + k) ≤
            (a N ^ m * a k) * t ^ (N * m + k) :=
          mul_le_mul_of_nonneg_right (hblock m k) (pow_nonneg ht _)
        _ = (a k * t ^ k) * q ^ m := by
          simp only [q, pow_add, pow_mul, mul_pow]
          ring
    · exact (summable_geometric_of_lt_one hq0 hcontract).mul_left _
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  rw [Finset.sum_indicator_mod N (fun n : ℕ => a n * t ^ n)]
  have hsind (k : ZMod N) : Summable
      ({n : ℕ | (n : ZMod N) = k}.indicator
        (fun n : ℕ => a n * t ^ n)) := by
    rw [← ZMod.natCast_zmod_val k,
      summable_indicator_mod_iff_summable N k.val]
    exact hstride k.val
  have hsum : Summable (fun n : ℕ =>
      ∑ k : ZMod N,
        {m : ℕ | (m : ZMod N) = k}.indicator
          (fun m : ℕ => a m * t ^ m) n) := by
    apply summable_sum (s := Finset.univ)
    intro k _hk
    exact hsind k
  apply hsum.congr
  intro n
  simp only [Finset.sum_apply]

/-- Positive submultiplicative growth, the exponential upper bound, and the
horseshoe lower bound produce the required radius data. -/
theorem weakLapRadiusData_exists {T : IntervalMap}
    (G : WeakLapGrowthData T) : Nonempty (WeakLapRadiusData T) := by
  let a : ℕ → ℝ := fun n => (weakLapCount T n : ℝ)
  let P : FormalMultilinearSeries ℝ ℝ ℝ := weakLapFormalSeries T
  have ha : ∀ n : ℕ, 0 ≤ a n := fun _ => Nat.cast_nonneg _
  have hsub : ∀ m n : ℕ, a (m + n) ≤ a m * a n := by
    intro m n
    have hcast : (weakLapCount T (m + n) : ℝ) ≤
        weakLapCount T m * weakLapCount T n := by
      exact_mod_cast G.submultiplicative m n
    simpa [a] using hcast
  let q : ℝ := G.upperBase
  have hqpos : 0 < q := by
    have hcast : (0 : ℝ) < G.upperBase := by
      exact_mod_cast G.upperBase_pos
    simpa [q] using hcast
  let qinv : ℝ≥0 := ⟨q⁻¹, (inv_pos.mpr hqpos).le⟩
  have hP_lower : (qinv : ℝ≥0∞) ≤ P.radius := by
    apply P.le_radius_of_bound 1
    intro n
    have hupper : a n ≤ q ^ n := by
      have hcast : (weakLapCount T n : ℝ) ≤
          (G.upperBase : ℝ) ^ n := by
        exact_mod_cast G.upper_bound n
      simpa [a, q] using hcast
    dsimp only [P]
    rw [weakLapFormalSeries,
      FormalMultilinearSeries.ofScalars_norm]
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    dsimp [a, qinv]
    dsimp [a] at hupper
    calc
      a n * (q⁻¹) ^ n ≤ q ^ n * (q⁻¹) ^ n :=
        mul_le_mul_of_nonneg_right hupper
          (pow_nonneg (inv_pos.mpr hqpos).le _)
      _ = 1 := by
        rw [← mul_pow]
        simp [hqpos.ne']
  have hqinvpos : 0 < qinv := inv_pos.mpr hqpos
  have hPpos : 0 < P.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr hqinvpos) hP_lower
  let halfNN : ℝ≥0 := ⟨1 / 2, by norm_num⟩
  have hhorseTerm : ∀ n : ℕ,
      1 ≤ ‖P n‖ * (1 / 2 : ℝ) ^ n := by
    intro n
    have hlower : (2 : ℝ) ^ n ≤ a n := by
      have hcast : ((2 ^ n : ℕ) : ℝ) ≤
          (weakLapCount T n : ℝ) := by
        exact_mod_cast G.horse_lower n
      simpa [a] using hcast
    dsimp only [P]
    rw [weakLapFormalSeries,
      FormalMultilinearSeries.ofScalars_norm]
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    dsimp [a] at hlower ⊢
    calc
      1 = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num
      _ ≤ a n * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hlower (pow_nonneg (by norm_num) _)
  have hP_upper : P.radius ≤ (halfNN : ℝ≥0∞) := by
    by_contra hnot
    have hinside : (halfNN : ℝ≥0∞) < P.radius :=
      lt_of_not_ge hnot
    have hs := P.summable_norm_mul_pow hinside
    have hz := hs.tendsto_atTop_zero
    rw [Metric.tendsto_atTop] at hz
    obtain ⟨M, hM⟩ := hz 1 zero_lt_one
    have hsmall := hM M le_rfl
    have hhalf : (halfNN : ℝ) = 1 / 2 := by rfl
    have hnonneg : 0 ≤ ‖P M‖ * (halfNN : ℝ) ^ M :=
      mul_nonneg (norm_nonneg _) (pow_nonneg halfNN.property _)
    have hsmall' : ‖P M‖ * (halfNN : ℝ) ^ M < 1 := by
      simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hsmall
    rw [hhalf] at hsmall'
    exact (not_lt_of_ge (hhorseTerm M)) hsmall'
  have hPneTop : P.radius ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hP_upper
  let radiusNN : ℝ≥0 := P.radius.toNNReal
  let radius : ℝ := radiusNN
  have hcoeRadius : (radiusNN : ℝ≥0∞) = P.radius :=
    ENNReal.coe_toNNReal hPneTop
  have hradiusPos : 0 < radius := by
    have hpos : 0 < radiusNN := by
      rw [← ENNReal.coe_pos, hcoeRadius]
      exact hPpos
    exact_mod_cast hpos
  have hradiusLeHalf : radius ≤ 1 / 2 := by
    have hle : radiusNN ≤ halfNN := by
      exact ENNReal.coe_le_coe.mp (hcoeRadius.trans_le hP_upper)
    exact_mod_cast hle
  have hboundary : ∀ n : ℕ, 1 ≤ a n * radius ^ n := by
    intro n
    cases n with
    | zero =>
        have hzero : (1 : ℝ) ≤ a 0 := by
          have hcast : ((2 ^ 0 : ℕ) : ℝ) ≤
              (weakLapCount T 0 : ℝ) := by
            exact_mod_cast G.horse_lower 0
          simpa [a] using hcast
        simpa using hzero
    | succ n =>
        by_contra hnot
        have hcontract : a (n + 1) * radius ^ (n + 1) < 1 :=
          lt_of_not_ge hnot
        let U : Set ℝ := {s | a (n + 1) * s ^ (n + 1) < 1}
        have hUopen : IsOpen U := by
          exact isOpen_lt
            (continuous_const.mul (continuous_id.pow (n + 1))) continuous_const
        have hrU : radius ∈ U := hcontract
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen radius hrU
        let s := radius + ε / 2
        have hrs : radius < s := by dsimp [s]; linarith
        have hs0 : 0 ≤ s := hradiusPos.le.trans hrs.le
        have hsball : s ∈ Metric.ball radius ε := by
          rw [Metric.mem_ball, Real.dist_eq]
          dsimp [s]
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hscontract : a (n + 1) * s ^ (n + 1) < 1 :=
          hball hsball
        have hsum : Summable (fun k : ℕ => a k * s ^ k) :=
          weakSummable_of_submultiplicative_block a ha hsub
            (Nat.succ_pos n) hs0 hscontract
        let sNN : ℝ≥0 := ⟨s, hs0⟩
        have hsLeRadius : (sNN : ℝ≥0∞) ≤ P.radius := by
          apply P.le_radius_of_summable_norm
          simpa [P, weakLapFormalSeries,
            FormalMultilinearSeries.ofScalars_norm, a] using hsum
        rw [← hcoeRadius] at hsLeRadius
        have hsle : s ≤ radius := by
          exact_mod_cast ENNReal.coe_le_coe.mp hsLeRadius
        exact (not_le_of_gt hrs) hsle
  let factor : ℕ → ℝ := fun n =>
    1 - 1 / ((n : ℝ) + 2) ^ 2
  let sample : ℕ → ℝ := fun n => radius * factor n
  have hfactorPos : ∀ n : ℕ, 0 < factor n := by
    intro n
    dsimp [factor]
    have hden : 1 < ((n : ℝ) + 2) ^ 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [sq_nonneg ((n : ℝ) + 2)]
    have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden
    norm_num at hinv
    rw [one_div]
    exact sub_pos.mpr hinv
  have hfactorLt : ∀ n : ℕ, factor n < 1 := by
    intro n
    dsimp [factor]
    have hinv : 0 < 1 / ((n : ℝ) + 2) ^ 2 := by positivity
    linarith
  have hfactorMono : StrictMono factor := by
    intro m n hmn
    dsimp [factor]
    have hmnCast : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    have hmn' : (m : ℝ) + 2 < (n : ℝ) + 2 := by linarith
    have hsquares : ((m : ℝ) + 2) ^ 2 < ((n : ℝ) + 2) ^ 2 := by
      nlinarith [sq_nonneg ((m : ℝ) + 2),
        sq_nonneg ((n : ℝ) + 2)]
    have hinv := one_div_lt_one_div_of_lt
      (show 0 < ((m : ℝ) + 2) ^ 2 by positivity) hsquares
    linarith
  have hfactorTendsto : Tendsto factor atTop (nhds 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2))
        atTop (nhds 0) := by
      have h := (tendsto_add_atTop_iff_nat 2).2
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0))
      simpa [Nat.cast_add] using h
    have hinvSq := hinv.pow 2
    have hone :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1)).sub hinvSq
    simpa [factor, one_div_pow] using hone
  have hsamplePos : ∀ n : ℕ, 0 < sample n := fun n =>
    mul_pos hradiusPos (hfactorPos n)
  have hsampleLt : ∀ n : ℕ, sample n < radius := fun n => by
    dsimp [sample]
    nlinarith [mul_lt_mul_of_pos_left (hfactorLt n) hradiusPos]
  have hsampleMono : StrictMono sample := by
    intro m n hmn
    dsimp [sample]
    exact mul_lt_mul_of_pos_left (hfactorMono hmn) hradiusPos
  have hsampleTendsto : Tendsto sample atTop (nhds radius) := by
    convert tendsto_const_nhds.mul hfactorTendsto using 1 <;> simp [sample]
  have hseries : ∀ n : ℕ, Summable
      (fun k : ℕ => (weakLapCount T k : ℝ) * sample n ^ k) := by
    intro n
    let sNN : ℝ≥0 := ⟨sample n, (hsamplePos n).le⟩
    have hsInside : (sNN : ℝ≥0∞) < P.radius := by
      rw [← hcoeRadius, ENNReal.coe_lt_coe]
      exact hsampleLt n
    have hs := P.summable_norm_mul_pow hsInside
    simpa [P, weakLapFormalSeries,
      FormalMultilinearSeries.ofScalars_norm, sNN] using hs
  have hfactorHalfPow : ∀ n : ℕ, (1 / 2 : ℝ) ≤ factor n ^ n := by
    intro n
    have hbern := one_add_mul_sub_le_pow
      (a := factor n) (by linarith [hfactorPos n]) n
    have hdenpos : 0 < ((n : ℝ) + 2) ^ 2 := by positivity
    have hfrac : (n : ℝ) / ((n : ℝ) + 2) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [sq_nonneg ((n : ℝ) + 2)]
    dsimp [factor] at hbern ⊢
    have heq :
        1 + (n : ℝ) * (1 - 1 / ((n : ℝ) + 2) ^ 2 - 1) =
          1 - (n : ℝ) / ((n : ℝ) + 2) ^ 2 := by ring
    rw [heq] at hbern
    nlinarith
  have htotalLower : ∀ n : ℕ,
      (n : ℝ) / 2 ≤ weakTotalLapResolvent T (sample n) := by
    intro n
    have hterm : ∀ k ∈ Finset.range n,
        (1 / 2 : ℝ) ≤ (weakLapCount T k : ℝ) * sample n ^ k := by
      intro k hk
      have hkn : k ≤ n := (Finset.mem_range.mp hk).le
      have hf0 : 0 ≤ factor n := (hfactorPos n).le
      have hf1 : factor n ≤ 1 := (hfactorLt n).le
      have hpow : factor n ^ n ≤ factor n ^ k :=
        pow_le_pow_of_le_one hf0 hf1 hkn
      have hb := hboundary k
      calc
        (1 / 2 : ℝ) ≤ factor n ^ n := hfactorHalfPow n
        _ ≤ factor n ^ k := hpow
        _ = 1 * factor n ^ k := by ring
        _ ≤ (a k * radius ^ k) * factor n ^ k :=
          mul_le_mul_of_nonneg_right hb (pow_nonneg hf0 _)
        _ = (weakLapCount T k : ℝ) * sample n ^ k := by
          simp only [a, sample, mul_pow]
          ring
    have hfinite : (n : ℝ) / 2 ≤
        ∑ k ∈ Finset.range n,
          (weakLapCount T k : ℝ) * sample n ^ k := by
      calc
        (n : ℝ) / 2 =
            ∑ _k ∈ Finset.range n, (1 / 2 : ℝ) := by
          simp [div_eq_mul_inv]
        _ ≤ _ := Finset.sum_le_sum hterm
    refine hfinite.trans ?_
    unfold weakTotalLapResolvent
    exact (hseries n).sum_le_tsum (Finset.range n)
      (fun k _hk => mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (hsamplePos n).le _))
  have htotalTendsto : Tendsto
      (fun n => weakTotalLapResolvent T (sample n)) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Eventually.of_forall htotalLower)
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop
        (by norm_num : (0 : ℝ) < 1 / 2))
  exact ⟨{
    radius := radius
    radius_pos := hradiusPos
    radius_le_half := hradiusLeHalf
    sample := sample
    sample_pos := hsamplePos
    sample_lt_radius := hsampleLt
    sample_strictMono := hsampleMono
    sample_tendsto := hsampleTendsto
    series_summable := hseries
    total_tendsto := htotalTendsto
  }⟩

/-- The normalized local resolvent. -/
noncomputable def weakNormalizedLapResolvent
    {T : IntervalMap} (R : WeakLapRadiusData T)
    (x y : I) (n : ℕ) : ℝ :=
  weakLapResolvent T x y (R.sample n) /
    weakTotalLapResolvent T (R.sample n)

private theorem weakTotalLapResolvent_pos {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T) (n : ℕ) :
    0 < weakTotalLapResolvent T (R.sample n) := by
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  have hzero : weakLapCount T 0 = 1 := by
    change weakLapCountOf (iterateMap T 0)
      leftEndpoint rightEndpoint = 1
    apply weakLapCountOf_eq_one_of_weaklyMonotoneOn
      (hT.iterate 0) hends
    left
    intro x _hx y _hy hxy
    simpa [iterateMap] using hxy
  unfold weakTotalLapResolvent
  exact (R.series_summable n).tsum_pos
    (fun k => mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (R.sample_pos n).le k)) 0 (by simp [hzero])

/-- Local resolvent series converge by domination by the total series. -/
theorem weakLapResolvent_summable {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T)
    (x y : I) (n : ℕ) :
    Summable (fun k : ℕ =>
      (weakLapCountOn T k x y : ℝ) * R.sample n ^ k) := by
  apply Summable.of_nonneg_of_le
    (f := fun k : ℕ => (weakLapCount T k : ℝ) * R.sample n ^ k)
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (R.sample_pos n).le k)
  · intro k
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast weakLapCountOn_le_total hT k x y)
      (pow_nonneg (R.sample_pos n).le k)
  · exact R.series_summable n

/-- Every normalized local resolvent lies in the unit interval. -/
theorem weakNormalizedLapResolvent_bounds {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T)
    {x y : I} (hxy : x ≤ y) (n : ℕ) :
    0 ≤ weakNormalizedLapResolvent R x y n ∧
      weakNormalizedLapResolvent R x y n ≤ 1 := by
  have hs := weakLapResolvent_summable hT R x y n
  have hnum0 : 0 ≤ weakLapResolvent T x y (R.sample n) := by
    unfold weakLapResolvent
    exact tsum_nonneg fun k =>
      mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (R.sample_pos n).le _)
  have hnumle : weakLapResolvent T x y (R.sample n) ≤
      weakTotalLapResolvent T (R.sample n) := by
    unfold weakLapResolvent weakTotalLapResolvent
    apply hs.tsum_le_tsum _ (R.series_summable n)
    intro k
    apply mul_le_mul_of_nonneg_right _
      (pow_nonneg (R.sample_pos n).le _)
    exact_mod_cast weakLapCountOn_le_total hT k x y
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  constructor
  · exact div_nonneg hnum0 hDpos.le
  · apply (div_le_iff₀ hDpos).2
    simpa using hnumle

private theorem weakNormalizedLapResolvent_adjacent_error
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y z : I}
    (hxy : x < y) (hyz : y < z) :
    ∀ n : ℕ,
      |weakNormalizedLapResolvent R x z n -
          weakNormalizedLapResolvent R x y n -
          weakNormalizedLapResolvent R y z n| ≤
        (1 / (1 - R.sample n)) /
          weakTotalLapResolvent T (R.sample n) := by
  intro n
  let t := R.sample n
  have ht0 : 0 ≤ t := (R.sample_pos n).le
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  have ht1 : t < 1 := (R.sample_lt_radius n).trans hrlt
  have hsxz := weakLapResolvent_summable hT R x z n
  have hsxy := weakLapResolvent_summable hT R x y n
  have hsyz := weakLapResolvent_summable hT R y z n
  have hsum : HasSum
      (fun k : ℕ =>
        (weakLapCountOn T k x z : ℝ) * t ^ k -
          (weakLapCountOn T k x y : ℝ) * t ^ k -
          (weakLapCountOn T k y z : ℝ) * t ^ k)
      (weakLapResolvent T x z t - weakLapResolvent T x y t -
        weakLapResolvent T y z t) := by
    simpa [weakLapResolvent, t] using
      ((hsxz.hasSum.sub hsxy.hasSum).sub hsyz.hasSum)
  have hraw :
      |weakLapResolvent T x z t - weakLapResolvent T x y t -
          weakLapResolvent T y z t| ≤ 1 / (1 - t) := by
    have hbound := hsum.norm_le_of_bounded
      (hasSum_geometric_of_lt_one ht0 ht1) (fun k => by
        have hcoeff :
            |(weakLapCountOn T k x z : ℝ) -
                weakLapCountOn T k x y -
                weakLapCountOn T k y z| ≤ 1 := by
          exact_mod_cast weakLapCountOn_adjacent_error hT k hxy hyz
        rw [Real.norm_eq_abs]
        have halg :
            (weakLapCountOn T k x z : ℝ) * t ^ k -
                (weakLapCountOn T k x y : ℝ) * t ^ k -
                (weakLapCountOn T k y z : ℝ) * t ^ k =
              ((weakLapCountOn T k x z : ℝ) -
                weakLapCountOn T k x y -
                weakLapCountOn T k y z) * t ^ k := by ring
        rw [halg, abs_mul, abs_of_nonneg (pow_nonneg ht0 k)]
        simpa using mul_le_mul_of_nonneg_right hcoeff (pow_nonneg ht0 k))
    simpa [Real.norm_eq_abs, one_div] using hbound
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  have halg :
      weakLapResolvent T x z (R.sample n) /
            weakTotalLapResolvent T (R.sample n) -
          weakLapResolvent T x y (R.sample n) /
            weakTotalLapResolvent T (R.sample n) -
          weakLapResolvent T y z (R.sample n) /
            weakTotalLapResolvent T (R.sample n) =
        (weakLapResolvent T x z (R.sample n) -
          weakLapResolvent T x y (R.sample n) -
          weakLapResolvent T y z (R.sample n)) /
            weakTotalLapResolvent T (R.sample n) := by ring
  rw [halg, abs_div, abs_of_pos hDpos]
  exact div_le_div_of_nonneg_right (by simpa [t] using hraw) hDpos.le

/-- The normalized adjacent-additivity defect tends to zero. -/
theorem weakNormalizedLapResolvent_adjacent_tendsto_zero
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y z : I}
    (hxy : x < y) (hyz : y < z) :
    Tendsto (fun n =>
      weakNormalizedLapResolvent R x z n -
        weakNormalizedLapResolvent R x y n -
        weakNormalizedLapResolvent R y z n)
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => 1 - R.sample n)
      atTop (nhds (1 - R.radius)) :=
    tendsto_const_nhds.sub R.sample_tendsto
  have hdenne : 1 - R.radius ≠ 0 := by
    linarith [R.radius_le_half]
  have hnumer : Tendsto (fun n : ℕ => 1 / (1 - R.sample n))
      atTop (nhds (1 / (1 - R.radius))) :=
    tendsto_const_nhds.div hden hdenne
  have herror : Tendsto
      (fun n : ℕ => (1 / (1 - R.sample n)) /
        weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
    hnumer.div_atTop R.total_tendsto
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ herror
  intro n
  simpa [Real.norm_eq_abs] using
    weakNormalizedLapResolvent_adjacent_error hT R hxy hyz n

/-- A uniform quantitative version of the normalized weak-branch defect.
The geometric factor is needed precisely for an honest constant branch. -/
private theorem weakNormalizedLapResolvent_branch_error
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    ∀ n : ℕ,
      |weakNormalizedLapResolvent R x y n -
          R.sample n * weakNormalizedLapResolvent R
            (min (T x) (T y)) (max (T x) (T y)) n| ≤
        (1 / (1 - R.sample n)) /
          weakTotalLapResolvent T (R.sample n) := by
  intro n
  let t := R.sample n
  let u := min (T x) (T y)
  let v := max (T x) (T y)
  have ht0 : 0 ≤ t := (R.sample_pos n).le
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  have ht1 : t < 1 := (R.sample_lt_radius n).trans hrlt
  have hsxy := weakLapResolvent_summable hT R x y n
  have hsuv := weakLapResolvent_summable hT R u v n
  have hzero : weakLapCountOn T 0 x y = 1 := by
    change weakLapCountOf (iterateMap T 0) x y = 1
    apply weakLapCountOf_eq_one_of_weaklyMonotoneOn
      (hT.iterate 0) hxy
    left
    intro a _ha b _hb hab
    simpa [iterateMap] using hab
  have htailxy : Summable (fun k : ℕ =>
      (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1)) := by
    simpa [t] using hsxy.comp_injective Nat.succ_injective
  have htailuv : Summable (fun k : ℕ =>
      (weakLapCountOn T k u v : ℝ) * t ^ (k + 1)) := by
    have hmul := hsuv.mul_left t
    apply hmul.congr
    intro k
    simp only [t, pow_succ]
    ring
  have htailxy_tsum :
      (∑' k : ℕ,
          (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1)) =
        weakLapResolvent T x y t - 1 := by
    have hst : Summable (fun k : ℕ =>
        (weakLapCountOn T k x y : ℝ) * t ^ k) := by
      simpa [t] using hsxy
    rw [weakLapResolvent]
    rw [hst.tsum_eq_zero_add]
    simp [hzero]
  have htailuv_tsum :
      (∑' k : ℕ,
          (weakLapCountOn T k u v : ℝ) * t ^ (k + 1)) =
        t * weakLapResolvent T u v t := by
    calc
      (∑' k : ℕ,
          (weakLapCountOn T k u v : ℝ) * t ^ (k + 1)) =
          ∑' k : ℕ,
            t * ((weakLapCountOn T k u v : ℝ) * t ^ k) := by
        apply tsum_congr
        intro k
        rw [pow_succ]
        ring
      _ = t * ∑' k : ℕ,
          (weakLapCountOn T k u v : ℝ) * t ^ k := tsum_mul_left
      _ = t * weakLapResolvent T u v t := by rfl
  have hsum : HasSum
      (fun k : ℕ =>
        (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1) -
          (weakLapCountOn T k u v : ℝ) * t ^ (k + 1))
      (weakLapResolvent T x y t - 1 -
        t * weakLapResolvent T u v t) := by
    simpa [htailxy_tsum, htailuv_tsum] using
      htailxy.hasSum.sub htailuv.hasSum
  have hgeom : HasSum (fun k : ℕ => t ^ (k + 1))
      (t / (1 - t)) := by
    simpa [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one ht0 ht1).mul_left t
  have htailBound :
      |weakLapResolvent T x y t - 1 -
          t * weakLapResolvent T u v t| ≤ t / (1 - t) := by
    have hbound := hsum.norm_le_of_bounded hgeom (fun k => by
      have hcoeff :
          |(weakLapCountOn T (k + 1) x y : ℝ) -
              weakLapCountOn T k u v| ≤ 1 := by
        exact_mod_cast
          weakLapCountOn_succ_branch_error hT hxy hmono k
      rw [Real.norm_eq_abs]
      have halg :
          (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1) -
              (weakLapCountOn T k u v : ℝ) * t ^ (k + 1) =
            ((weakLapCountOn T (k + 1) x y : ℝ) -
              weakLapCountOn T k u v) * t ^ (k + 1) := by ring
      rw [halg, abs_mul, abs_of_nonneg (pow_nonneg ht0 (k + 1))]
      simpa using mul_le_mul_of_nonneg_right hcoeff
        (pow_nonneg ht0 (k + 1)))
    simpa [Real.norm_eq_abs] using hbound
  have hraw :
      |weakLapResolvent T x y t - t * weakLapResolvent T u v t| ≤
        1 / (1 - t) := by
    calc
      |weakLapResolvent T x y t - t * weakLapResolvent T u v t| =
          |1 + (weakLapResolvent T x y t - 1 -
            t * weakLapResolvent T u v t)| := by congr 1 <;> ring
      _ ≤ |(1 : ℝ)| +
          |weakLapResolvent T x y t - 1 -
            t * weakLapResolvent T u v t| := abs_add_le _ _
      _ ≤ 1 + t / (1 - t) := by
        simpa using add_le_add_left htailBound 1
      _ = 1 / (1 - t) := by
        field_simp [ne_of_gt (sub_pos.mpr ht1)]
        ring
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  have halg :
      weakLapResolvent T x y (R.sample n) /
            weakTotalLapResolvent T (R.sample n) -
          R.sample n *
            (weakLapResolvent T (min (T x) (T y)) (max (T x) (T y))
              (R.sample n) / weakTotalLapResolvent T (R.sample n)) =
        (weakLapResolvent T x y (R.sample n) -
          R.sample n * weakLapResolvent T (min (T x) (T y))
            (max (T x) (T y)) (R.sample n)) /
              weakTotalLapResolvent T (R.sample n) := by ring
  rw [halg, abs_div, abs_of_pos hDpos]
  exact div_le_div_of_nonneg_right (by simpa [t, u, v] using hraw) hDpos.le

/-- The normalized weak-branch shift defect tends to zero, including when
the first branch is constant. -/
theorem weakNormalizedLapResolvent_branch_tendsto_zero
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    Tendsto (fun n =>
      weakNormalizedLapResolvent R x y n -
        R.sample n * weakNormalizedLapResolvent R
          (min (T x) (T y)) (max (T x) (T y)) n)
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => 1 - R.sample n)
      atTop (nhds (1 - R.radius)) :=
    tendsto_const_nhds.sub R.sample_tendsto
  have hdenne : 1 - R.radius ≠ 0 := by
    linarith [R.radius_le_half]
  have hnumer : Tendsto (fun n : ℕ => 1 / (1 - R.sample n))
      atTop (nhds (1 / (1 - R.radius))) :=
    tendsto_const_nhds.div hden hdenne
  have herror : Tendsto
      (fun n : ℕ => (1 / (1 - R.sample n)) /
        weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
    hnumer.div_atTop R.total_tendsto
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ herror
  intro n
  simpa [Real.norm_eq_abs] using
    weakNormalizedLapResolvent_branch_error hT R hxy hmono n

/-- Every prefix iterate of a weak itinerary cell is itself weakly
monotone on the original interval. -/
private theorem weakItineraryCell_iterate_weaklyMonotoneOn
    {T : IntervalMap} {m k : ℕ} {x y : I} (hxy : x ≤ y)
    (hcell : IsWeakItineraryCell T m x y) (hk : k ≤ m) :
    IsWeaklyMonotoneOn (iterateMap T k) (Set.Icc x y) := by
  induction k with
  | zero =>
      left
      intro a _ha b _hb hab
      simpa [iterateMap] using hab
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      have hprev := ih (Nat.le_of_lt hklt)
      have hstep := hcell k hklt
      have hmaps : Set.MapsTo (iterateMap T k) (Set.Icc x y)
          (Set.Icc
            (min (iterateMap T k x) (iterateMap T k y))
            (max (iterateMap T k x) (iterateMap T k y))) := by
        intro z hz
        rcases hprev with hinc | hdec
        · have hlower : iterateMap T k x ≤ iterateMap T k z :=
            hinc ⟨le_rfl, hxy⟩ hz hz.1
          have hupper : iterateMap T k z ≤ iterateMap T k y :=
            hinc hz ⟨hxy, le_rfl⟩ hz.2
          exact ⟨(min_le_left _ _).trans hlower,
            hupper.trans (le_max_right _ _)⟩
        · have hlower : iterateMap T k y ≤ iterateMap T k z :=
            hdec hz ⟨hxy, le_rfl⟩ hz.2
          have hupper : iterateMap T k z ≤ iterateMap T k x :=
            hdec ⟨le_rfl, hxy⟩ hz hz.1
          exact ⟨(min_le_right _ _).trans hlower,
            hupper.trans (le_max_left _ _)⟩
      have hcomp := hstep.comp hprev hmaps
      have hiter : T ∘ iterateMap T k = iterateMap T (k + 1) := by
        funext z
        change T ((T^[k]) z) = (T^[k + 1]) z
        rw [Function.iterate_succ_apply]
        exact (Function.Commute.self_iterate T k).eq z
      rw [hiter] at hcomp
      exact hcomp

/-- If an `m`-fold iterate follows one weak branch on an interval, the
remaining `j` iterates require no more laps there than the global `j`-lap
count.  In the constant-image case the source needs one lap, which is still
bounded by the positive global count. -/
private theorem weakLapCountOn_add_le_total_of_iterate_weaklyMonotone
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {m j : ℕ} {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn (iterateMap T m) (Set.Icc x y)) :
    weakLapCountOn T (m + j) x y ≤ weakLapCount T j := by
  let φ : IntervalMap := iterateMap T m
  let F : IntervalMap := iterateMap T j
  have hφ : FinitePieceMonotone φ := hT.iterate m
  have hF : FinitePieceMonotone F := hT.iterate j
  have hcomp : FinitePieceMonotone (F ∘ φ) := hF.comp hφ
  have hiter : iterateMap T (m + j) = F ∘ φ := by
    funext z
    simp only [F, φ, iterateMap, Function.comp_apply,
      Function.iterate_add_apply]
    exact ((Function.Commute.refl T).iterate_iterate m j).eq z
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  have htotalPos : 0 < weakLapCount T j := by
    change 0 < weakLapCountOf F leftEndpoint rightEndpoint
    exact weakLapCountOf_pos hF hends
  rcases hmono with hinc | hdec
  · have hφends : φ x ≤ φ y :=
      hinc ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
    by_cases heq : φ x = φ y
    · have hconst : ∀ z ∈ Set.Icc x y, φ z = φ x := by
        intro z hz
        apply le_antisymm
        · simpa [heq] using hinc hz ⟨hxy.le, le_rfl⟩ hz.2
        · exact hinc ⟨le_rfl, hxy.le⟩ hz hz.1
      have hweakComp :
          IsWeaklyMonotoneOn (F ∘ φ) (Set.Icc x y) := by
        left
        intro a ha b hb _hab
        simp only [Function.comp_apply]
        rw [hconst a ha, hconst b hb]
      have hsource : weakLapCountOn T (m + j) x y = 1 := by
        change weakLapCountOf (iterateMap T (m + j)) x y = 1
        rw [hiter]
        exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
          hcomp hxy hweakComp
      rw [hsource]
      exact htotalPos
    · have hstrict : φ x < φ y := lt_of_le_of_ne hφends heq
      rcases weakLapCountOf_attained hF hstrict with ⟨A, hA⟩
      rcases A.pull_monotoneOn hxy hφ.continuous hinc hstrict with
        ⟨Q, hQ⟩
      change weakLapCountOf (iterateMap T (m + j)) x y ≤
        weakLapCount T j
      rw [hiter]
      calc
        weakLapCountOf (F ∘ φ) x y ≤ Q.cellCount :=
          weakLapCountOf_minimal hcomp hxy Q
        _ = weakLapCountOn T j (φ x) (φ y) := by
          simpa [F, weakLapCountOn] using hQ.trans hA
        _ ≤ weakLapCount T j := weakLapCountOn_le_total hT j _ _
  · have hφends : φ y ≤ φ x :=
      hdec ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
    by_cases heq : φ x = φ y
    · have hconst : ∀ z ∈ Set.Icc x y, φ z = φ x := by
        intro z hz
        apply le_antisymm
        · exact hdec ⟨le_rfl, hxy.le⟩ hz hz.1
        · simpa [heq] using hdec hz ⟨hxy.le, le_rfl⟩ hz.2
      have hweakComp :
          IsWeaklyMonotoneOn (F ∘ φ) (Set.Icc x y) := by
        left
        intro a ha b hb _hab
        simp only [Function.comp_apply]
        rw [hconst a ha, hconst b hb]
      have hsource : weakLapCountOn T (m + j) x y = 1 := by
        change weakLapCountOf (iterateMap T (m + j)) x y = 1
        rw [hiter]
        exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
          hcomp hxy hweakComp
      rw [hsource]
      exact htotalPos
    · have hne : φ y ≠ φ x := fun h => heq h.symm
      have hstrict : φ y < φ x := lt_of_le_of_ne hφends hne
      rcases weakLapCountOf_attained hF hstrict with ⟨A, hA⟩
      rcases A.pull_antitoneOn hxy hφ.continuous hdec hstrict with
        ⟨Q, hQ⟩
      change weakLapCountOf (iterateMap T (m + j)) x y ≤
        weakLapCount T j
      rw [hiter]
      calc
        weakLapCountOf (F ∘ φ) x y ≤ Q.cellCount :=
          weakLapCountOf_minimal hcomp hxy Q
        _ = weakLapCountOn T j (φ y) (φ x) := by
          simpa [F, weakLapCountOn] using hQ.trans hA
        _ ≤ weakLapCount T j := weakLapCountOn_le_total hT j _ _

/-- Before taking a limit, a genuine `m`-step itinerary cell has normalized
mass bounded by the terminal radius power plus the accumulated `m` branch
errors. -/
theorem weakNormalizedLapResolvent_le_pow_of_weakItineraryCell
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {m : ℕ} {x y : I} (hxy : x < y)
    (hcell : IsWeakItineraryCell T m x y) (n : ℕ) :
    weakNormalizedLapResolvent R x y n ≤
      (m : ℝ) / weakTotalLapResolvent T (R.sample n) +
        R.sample n ^ m := by
  let t := R.sample n
  have ht0 : 0 ≤ t := (R.sample_pos n).le
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  have ht1 : t < 1 := (R.sample_lt_radius n).trans hrlt
  have hs := weakLapResolvent_summable hT R x y n
  have hs_t : Summable (fun k : ℕ =>
      (weakLapCountOn T k x y : ℝ) * t ^ k) := by
    simpa [t] using hs
  have htotal_t : Summable (fun k : ℕ =>
      (weakLapCount T k : ℝ) * t ^ k) := by
    simpa [t] using R.series_summable n
  have hprefixCount : ∀ {k : ℕ}, k < m →
      weakLapCountOn T k x y = 1 := by
    intro k hk
    change weakLapCountOf (iterateMap T k) x y = 1
    apply weakLapCountOf_eq_one_of_weaklyMonotoneOn
      (hT.iterate k) hxy
    exact weakItineraryCell_iterate_weaklyMonotoneOn
      hxy.le hcell (Nat.le_of_lt hk)
  have hmmono : IsWeaklyMonotoneOn (iterateMap T m)
      (Set.Icc x y) :=
    weakItineraryCell_iterate_weaklyMonotoneOn hxy.le hcell le_rfl
  have htailCount : ∀ j : ℕ,
      weakLapCountOn T (j + m) x y ≤ weakLapCount T j := by
    intro j
    simpa [Nat.add_comm] using
      weakLapCountOn_add_le_total_of_iterate_weaklyMonotone
        hT hxy hmmono (j := j)
  have htailSource : Summable (fun j : ℕ =>
      (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m)) := by
    apply hs_t.comp_injective
    intro a b hab
    exact Nat.add_right_cancel hab
  have htailCompare : Summable (fun j : ℕ =>
      t ^ m * ((weakLapCount T j : ℝ) * t ^ j)) :=
    htotal_t.mul_left (t ^ m)
  have htailLe :
      (∑' j : ℕ,
          (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m)) ≤
        t ^ m * weakTotalLapResolvent T t := by
    calc
      (∑' j : ℕ,
          (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m)) ≤
          ∑' j : ℕ,
            t ^ m * ((weakLapCount T j : ℝ) * t ^ j) := by
        apply htailSource.tsum_le_tsum _ htailCompare
        intro j
        have hcount :
            (weakLapCountOn T (j + m) x y : ℝ) ≤
              weakLapCount T j := by
          exact_mod_cast htailCount j
        calc
          (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m) ≤
              (weakLapCount T j : ℝ) * t ^ (j + m) :=
            mul_le_mul_of_nonneg_right hcount
              (pow_nonneg ht0 (j + m))
          _ = t ^ m * ((weakLapCount T j : ℝ) * t ^ j) := by
            rw [pow_add]
            ring
      _ = t ^ m * ∑' j : ℕ,
          ((weakLapCount T j : ℝ) * t ^ j) := tsum_mul_left
      _ = t ^ m * weakTotalLapResolvent T t := by rfl
  have hprefixLe :
      (∑ k ∈ Finset.range m,
          (weakLapCountOn T k x y : ℝ) * t ^ k) ≤ (m : ℝ) := by
    calc
      (∑ k ∈ Finset.range m,
          (weakLapCountOn T k x y : ℝ) * t ^ k) =
          ∑ k ∈ Finset.range m, t ^ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hprefixCount (Finset.mem_range.mp hk)]
        simp
      _ ≤ ∑ _k ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _hk
        exact pow_le_one₀ ht0 ht1.le
      _ = (m : ℝ) := by simp
  have hresLe : weakLapResolvent T x y t ≤
      (m : ℝ) + t ^ m * weakTotalLapResolvent T t := by
    unfold weakLapResolvent
    calc
      (∑' k : ℕ, (weakLapCountOn T k x y : ℝ) * t ^ k) =
          (∑ k ∈ Finset.range m,
              (weakLapCountOn T k x y : ℝ) * t ^ k) +
            ∑' j : ℕ,
              (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m) :=
        (hs_t.sum_add_tsum_nat_add m).symm
      _ ≤ (m : ℝ) + t ^ m * weakTotalLapResolvent T t :=
        add_le_add hprefixLe htailLe
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  apply (div_le_iff₀ hDpos).2
  calc
    weakLapResolvent T x y (R.sample n) ≤
        (m : ℝ) + (R.sample n) ^ m *
          weakTotalLapResolvent T (R.sample n) := by
      simpa [t] using hresLe
    _ = ((m : ℝ) / weakTotalLapResolvent T (R.sample n) +
          R.sample n ^ m) * weakTotalLapResolvent T (R.sample n) := by
      field_simp [hDpos.ne']

/-- The pre-limit cumulative functions have uniformly small genuine
itinerary neighborhoods on both sides of every point. -/
theorem weakNormalizedLapResolvent_twoSided_eventually_small
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) (x : I) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ a b : I,
      a ≤ x ∧ x ≤ b ∧
      (leftEndpoint < x → a < x) ∧
      (x < rightEndpoint → x < b) ∧
      IsWeakItineraryCell T m a x ∧
      IsWeakItineraryCell T m x b ∧
      ∀ᶠ n in atTop,
        (a = x ∨ weakNormalizedLapResolvent R a x n < ε) ∧
        (x = b ∨ weakNormalizedLapResolvent R x b n < ε) := by
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  obtain ⟨m, hmpow⟩ := exists_pow_lt_of_lt_one hε hrlt
  obtain ⟨a, b, hax, hxb, haleft, haright, hcellLeft,
      hcellRight⟩ := exists_twoSided_weakItineraryCell hT m x
  have hsmall : ∀ {u v : I}, u < v →
      IsWeakItineraryCell T m u v →
      ∀ᶠ n : ℕ in atTop,
        weakNormalizedLapResolvent R u v n < ε := by
    intro u v huv hcell
    have hzero : Tendsto
        (fun n : ℕ => (m : ℝ) /
          weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop R.total_tendsto
    have hlim : Tendsto
        (fun n : ℕ => (m : ℝ) /
            weakTotalLapResolvent T (R.sample n) + R.sample n ^ m)
        atTop (nhds (R.radius ^ m)) := by
      simpa using hzero.add (R.sample_tendsto.pow m)
    have hevent : ∀ᶠ n : ℕ in atTop,
        (m : ℝ) / weakTotalLapResolvent T (R.sample n) +
          R.sample n ^ m < ε :=
      (tendsto_order.1 hlim).2 ε hmpow
    filter_upwards [hevent] with n hn
    exact (weakNormalizedLapResolvent_le_pow_of_weakItineraryCell
      hT R huv hcell n).trans_lt hn
  have hleft : ∀ᶠ n : ℕ in atTop,
      a = x ∨ weakNormalizedLapResolvent R a x n < ε := by
    by_cases heq : a = x
    · exact Filter.Eventually.of_forall fun _ => Or.inl heq
    · have hlt : a < x := lt_of_le_of_ne hax heq
      filter_upwards [hsmall hlt hcellLeft] with n hn
      exact Or.inr hn
  have hright : ∀ᶠ n : ℕ in atTop,
      x = b ∨ weakNormalizedLapResolvent R x b n < ε := by
    by_cases heq : x = b
    · exact Filter.Eventually.of_forall fun _ => Or.inl heq
    · have hlt : x < b := lt_of_le_of_ne hxb heq
      filter_upwards [hsmall hlt hcellRight] with n hn
      exact Or.inr hn
  refine ⟨m, a, b, hax, hxb, haleft, haright, hcellLeft,
    hcellRight, ?_⟩
  filter_upwards [hleft, hright] with n hnleft hnright
  exact ⟨hnleft, hnright⟩

/-! ## Diagonal limit and the continuous coordinate -/

/-- Enlarging an interval can only increase its normalized weak-lap
resolvent. -/
private theorem weakNormalizedLapResolvent_mono
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T)
    {a x y b : I} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b)
    (n : ℕ) :
    weakNormalizedLapResolvent R x y n ≤
      weakNormalizedLapResolvent R a b n := by
  have hsxy := weakLapResolvent_summable hT R x y n
  have hsab := weakLapResolvent_summable hT R a b n
  have hnumle : weakLapResolvent T x y (R.sample n) ≤
      weakLapResolvent T a b (R.sample n) := by
    unfold weakLapResolvent
    apply hsxy.tsum_le_tsum _ hsab
    intro k
    apply mul_le_mul_of_nonneg_right _
      (pow_nonneg (R.sample_pos n).le k)
    exact_mod_cast weakLapCountOn_mono hT k hax hxy hyb
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  exact (div_le_div_iff_of_pos_right hDpos).2 hnumle

/-- A subsequence on which every cumulative normalized resolvent from the
left endpoint converges.  The dense diagonal is upgraded to all endpoints by
the uniform two-sided itinerary estimate above. -/
structure WeakLapCumulativeLimitData
    (T : IntervalMap) (R : WeakLapRadiusData T) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  cumulative : I → ℝ
  tendsto_cumulative : ∀ x : I,
    Tendsto
      (fun n => weakNormalizedLapResolvent R leftEndpoint x (subsequence n))
      atTop (𝓝 (cumulative x))

/-- Countable dense diagonalization plus itinerary equicontinuity produces a
single cumulative subsequential limit at every real endpoint. -/
theorem weakLapCumulativeLimitData_exists {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T) :
    Nonempty (WeakLapCumulativeLimitData T R) := by
  let d : ℕ → I := TopologicalSpace.denseSeq I
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq I
  let A : ℕ → (ℕ → Set.Icc (0 : ℝ) 1) := fun n j =>
    ⟨weakNormalizedLapResolvent R leftEndpoint (d j) n,
      weakNormalizedLapResolvent_bounds hT R
        (show leftEndpoint ≤ d j from (d j).property.1) n⟩
  obtain ⟨g, φ, hφ, hAg⟩ := CompactSpace.tendsto_subseq A
  have hdenseLimit : ∀ j : ℕ, Tendsto
      (fun n => weakNormalizedLapResolvent R leftEndpoint (d j) (φ n))
      atTop (nhds ((g j : Set.Icc (0 : ℝ) 1) : ℝ)) := by
    intro j
    have hj := tendsto_pi_nhds.1 hAg j
    have hj' := (continuous_subtype_val.tendsto (g j)).comp hj
    simpa [A, Function.comp_apply] using hj'
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hcauchy : ∀ x : I, CauchySeq
      (fun n => weakNormalizedLapResolvent R leftEndpoint x (φ n)) := by
    intro x
    by_cases hxl : x = leftEndpoint
    · subst x
      apply Metric.cauchySeq_iff.2
      intro ε hε
      refine ⟨0, ?_⟩
      intro p _hp q _hq
      simp [weakNormalizedLapResolvent, weakLapResolvent,
        weakLapCountOn, weakLapCountOf]
      exact hε
    · have hlx : leftEndpoint < x :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxl)
      apply Metric.cauchySeq_iff.2
      intro ε hε
      let δ : ℝ := ε / 6
      have hδ : 0 < δ := by dsimp [δ]; linarith
      obtain ⟨m, a, b, hax, _hxb, haleft, _haright,
          _hcellLeft, _hcellRight, hsmall⟩ :=
        weakNormalizedLapResolvent_twoSided_eventually_small hT R x hδ
      have hax' : a < x := haleft hlx
      obtain ⟨j, hj⟩ := hdense.exists_mem_open isOpen_Ioo
        (Set.nonempty_Ioo.mpr hax')
      have hleftdj : leftEndpoint < d j :=
        a.property.1.trans_lt hj.1
      have hmassAX : ∀ᶠ n : ℕ in atTop,
          weakNormalizedLapResolvent R a x n < δ := by
        filter_upwards [hsmall] with n hn
        exact hn.1.resolve_left hax'.ne
      have hmassφ : ∀ᶠ n : ℕ in atTop,
          weakNormalizedLapResolvent R (d j) x (φ n) < δ := by
        filter_upwards [hφtop.eventually hmassAX] with n hn
        exact (weakNormalizedLapResolvent_mono hT R
          (a := a) (x := d j) (y := x) (b := x)
          hj.1.le hj.2.le le_rfl (φ n)).trans_lt hn
      have herrBase :=
        weakNormalizedLapResolvent_adjacent_tendsto_zero
          hT R hleftdj hj.2
      have herrComp : Tendsto
          (fun n =>
            weakNormalizedLapResolvent R leftEndpoint x (φ n) -
              weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
              weakNormalizedLapResolvent R (d j) x (φ n))
          atTop (nhds 0) := by
        simpa [Function.comp_apply] using herrBase.comp hφtop
      have herrNorm : Tendsto
          (fun n =>
            |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
              weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
              weakNormalizedLapResolvent R (d j) x (φ n)|)
          atTop (nhds 0) := by
        simpa [Real.norm_eq_abs] using
          tendsto_zero_iff_norm_tendsto_zero.mp herrComp
      have herrφ : ∀ᶠ n : ℕ in atTop,
          |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
              weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
              weakNormalizedLapResolvent R (d j) x (φ n)| < δ :=
        (tendsto_order.1 herrNorm).2 δ hδ
      have hclose : ∀ᶠ n : ℕ in atTop,
          dist (weakNormalizedLapResolvent R leftEndpoint x (φ n))
            (weakNormalizedLapResolvent R leftEndpoint (d j) (φ n)) <
              ε / 3 := by
        filter_upwards [hmassφ, herrφ] with n hmassn herrn
        have hmassNonneg :=
          (weakNormalizedLapResolvent_bounds hT R hj.2.le (φ n)).1
        rw [Real.dist_eq]
        calc
          |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
              weakNormalizedLapResolvent R leftEndpoint (d j) (φ n)| =
              |(weakNormalizedLapResolvent R leftEndpoint x (φ n) -
                  weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
                  weakNormalizedLapResolvent R (d j) x (φ n)) +
                weakNormalizedLapResolvent R (d j) x (φ n)| := by
            congr 1
            ring
          _ ≤
              |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
                  weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
                  weakNormalizedLapResolvent R (d j) x (φ n)| +
                |weakNormalizedLapResolvent R (d j) x (φ n)| :=
            abs_add_le _ _
          _ < δ + δ := by
            rw [abs_of_nonneg hmassNonneg]
            exact add_lt_add herrn hmassn
          _ = ε / 3 := by dsimp [δ]; ring
      obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hclose
      obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1
        (hdenseLimit j).cauchySeq (ε / 3) (by linarith)
      refine ⟨max N₁ N₂, ?_⟩
      intro p hp q hq
      have hp₁ : N₁ ≤ p := (le_max_left _ _).trans hp
      have hq₁ : N₁ ≤ q := (le_max_left _ _).trans hq
      have hp₂ : N₂ ≤ p := (le_max_right _ _).trans hp
      have hq₂ : N₂ ≤ q := (le_max_right _ _).trans hq
      calc
        dist (weakNormalizedLapResolvent R leftEndpoint x (φ p))
            (weakNormalizedLapResolvent R leftEndpoint x (φ q)) ≤
            dist (weakNormalizedLapResolvent R leftEndpoint x (φ p))
                (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p)) +
              dist (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p))
                (weakNormalizedLapResolvent R leftEndpoint x (φ q)) :=
          dist_triangle _ _ _
        _ ≤ dist (weakNormalizedLapResolvent R leftEndpoint x (φ p))
                (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p)) +
              (dist (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p))
                  (weakNormalizedLapResolvent R leftEndpoint (d j) (φ q)) +
                dist (weakNormalizedLapResolvent R leftEndpoint (d j) (φ q))
                  (weakNormalizedLapResolvent R leftEndpoint x (φ q))) := by
          gcongr
          exact dist_triangle _ _ _
        _ < ε / 3 + (ε / 3 + ε / 3) := by
          gcongr
          · exact hN₁ p hp₁
          · exact hN₂ p hp₂ q hq₂
          · simpa [dist_comm] using hN₁ q hq₁
        _ = ε := by ring
  choose f hf using fun x : I => cauchySeq_tendsto_of_complete (hcauchy x)
  exact ⟨{
    subsequence := φ
    subsequence_strictMono := hφ
    cumulative := f
    tendsto_cumulative := hf }⟩

/-- A single diagonal subsequence and the limit of every localized
normalized resolvent. -/
structure WeakLapLimitData
    (T : IntervalMap) (R : WeakLapRadiusData T) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  value : I → I → ℝ
  value_diag : ∀ x : I, value x x = 0
  tendsto_value : ∀ {x y : I}, x < y →
    Tendsto
      (fun n => weakNormalizedLapResolvent R x y (subsequence n))
      atTop (𝓝 (value x y))

/-- Adjacent-error convergence converts the cumulative subsequence into a
limit for every localized interval. -/
theorem weakLapLimitData_exists {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (C : WeakLapCumulativeLimitData T R) :
    Nonempty (WeakLapLimitData T R) := by
  have hCleft : C.cumulative leftEndpoint = 0 := by
    apply tendsto_nhds_unique (C.tendsto_cumulative leftEndpoint)
    simpa [weakNormalizedLapResolvent, weakLapResolvent,
      weakLapCountOn, weakLapCountOf] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
        atTop (nhds 0))
  refine ⟨{
    subsequence := C.subsequence
    subsequence_strictMono := C.subsequence_strictMono
    value := fun x y => C.cumulative y - C.cumulative x
    value_diag := by intro x; simp
    tendsto_value := ?_ }⟩
  intro x y hxy
  by_cases hxl : x = leftEndpoint
  · subst x
    simpa [hCleft] using C.tendsto_cumulative y
  · have hlx : leftEndpoint < x :=
      lt_of_le_of_ne x.property.1 (Ne.symm hxl)
    have hdiff : Tendsto
        (fun n =>
          weakNormalizedLapResolvent R leftEndpoint y (C.subsequence n) -
            weakNormalizedLapResolvent R leftEndpoint x (C.subsequence n))
        atTop (nhds (C.cumulative y - C.cumulative x)) :=
      (C.tendsto_cumulative y).sub (C.tendsto_cumulative x)
    have herr : Tendsto
        (fun n =>
          weakNormalizedLapResolvent R leftEndpoint y (C.subsequence n) -
            weakNormalizedLapResolvent R leftEndpoint x (C.subsequence n) -
            weakNormalizedLapResolvent R x y (C.subsequence n))
        atTop (nhds 0) := by
      simpa [Function.comp_apply] using
        (weakNormalizedLapResolvent_adjacent_tendsto_zero
          hT R hlx hxy).comp C.subsequence_strictMono.tendsto_atTop
    have hlim := hdiff.sub herr
    convert hlim using 1 <;> ring

/-- The weak-lap limit is nonnegative, bounded by one, and normalized on the
whole interval. -/
theorem weakLapLimit_bounds {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) {x y : I} (hxy : x < y) :
    (0 ≤ L.value x y ∧ L.value x y ≤ 1) ∧
      L.value leftEndpoint rightEndpoint = 1 := by
  constructor
  · have htend := L.tendsto_value hxy
    constructor
    · apply ge_of_tendsto' htend
      intro n
      exact (weakNormalizedLapResolvent_bounds hT R hxy.le
        (L.subsequence n)).1
    · apply le_of_tendsto' htend
      intro n
      exact (weakNormalizedLapResolvent_bounds hT R hxy.le
        (L.subsequence n)).2
  · have hends : leftEndpoint < rightEndpoint := by
      norm_num [leftEndpoint, rightEndpoint]
    have hone : ∀ n : ℕ,
        weakNormalizedLapResolvent R leftEndpoint rightEndpoint n = 1 := by
      intro n
      have hnum : weakLapResolvent T leftEndpoint rightEndpoint
          (R.sample n) = weakTotalLapResolvent T (R.sample n) := by
        unfold weakLapResolvent weakTotalLapResolvent weakLapCount
        rfl
      simp only [weakNormalizedLapResolvent, hnum]
      exact div_self (weakTotalLapResolvent_pos hT R n).ne'
    have honeTend : Tendsto
        (fun n => weakNormalizedLapResolvent R leftEndpoint rightEndpoint
          (L.subsequence n)) atTop (nhds 1) := by
      simpa only [hone] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
          atTop (nhds 1))
    exact tendsto_nhds_unique (L.tendsto_value hends) honeTend

/-- Adjacent additivity becomes exact in the weak-lap limit. -/
theorem weakLapLimit_adjacent {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) {x y z : I}
    (hxy : x < y) (hyz : y < z) :
    L.value x z = L.value x y + L.value y z := by
  have hrawLimit : Tendsto
      (fun n => weakNormalizedLapResolvent R x z (L.subsequence n) -
        weakNormalizedLapResolvent R x y (L.subsequence n) -
        weakNormalizedLapResolvent R y z (L.subsequence n))
      atTop (nhds (L.value x z - L.value x y - L.value y z)) :=
    ((L.tendsto_value (hxy.trans hyz)).sub (L.tendsto_value hxy)).sub
      (L.tendsto_value hyz)
  have hrawZero : Tendsto
      (fun n => weakNormalizedLapResolvent R x z (L.subsequence n) -
        weakNormalizedLapResolvent R x y (L.subsequence n) -
        weakNormalizedLapResolvent R y z (L.subsequence n))
      atTop (nhds 0) := by
    simpa [Function.comp_apply] using
      (weakNormalizedLapResolvent_adjacent_tendsto_zero
        hT R hxy hyz).comp L.subsequence_strictMono.tendsto_atTop
  have heq : L.value x z - L.value x y - L.value y z = 0 :=
    tendsto_nhds_unique hrawLimit hrawZero
  linarith

/-- Weak-branch transport becomes exact in the limit. -/
theorem weakLapLimit_scaling {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    L.value x y = R.radius *
      L.value (min (T x) (T y)) (max (T x) (T y)) := by
  let u : I := min (T x) (T y)
  let v : I := max (T x) (T y)
  have huv : u ≤ v := min_le_max
  have hsubTop : Tendsto L.subsequence atTop atTop :=
    L.subsequence_strictMono.tendsto_atTop
  have hsampleSub : Tendsto
      (fun n : ℕ => R.sample (L.subsequence n))
      atTop (nhds R.radius) :=
    R.sample_tendsto.comp hsubTop
  have htarget : Tendsto
      (fun n => weakNormalizedLapResolvent R u v (L.subsequence n))
      atTop (nhds (L.value u v)) := by
    by_cases heq : u = v
    · rw [← heq]
      simpa [L.value_diag, weakNormalizedLapResolvent,
        weakLapResolvent, weakLapCountOn, weakLapCountOf] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
          atTop (nhds 0))
    · exact L.tendsto_value (lt_of_le_of_ne huv heq)
  have hrawLimit : Tendsto
      (fun n => weakNormalizedLapResolvent R x y (L.subsequence n) -
        R.sample (L.subsequence n) *
          weakNormalizedLapResolvent R u v (L.subsequence n))
      atTop (nhds (L.value x y - R.radius * L.value u v)) :=
    (L.tendsto_value hxy).sub (hsampleSub.mul htarget)
  have hrawZero : Tendsto
      (fun n => weakNormalizedLapResolvent R x y (L.subsequence n) -
        R.sample (L.subsequence n) *
          weakNormalizedLapResolvent R u v (L.subsequence n))
      atTop (nhds 0) := by
    simpa [u, v, Function.comp_apply] using
      (weakNormalizedLapResolvent_branch_tendsto_zero
        hT R hxy hmono).comp hsubTop
  have heq : L.value x y - R.radius * L.value u v = 0 :=
    tendsto_nhds_unique hrawLimit hrawZero
  simpa [u, v] using sub_eq_zero.mp heq

/-- On a genuine `m`-step itinerary cell, repeated one-branch scaling bounds
the limiting mass by the corresponding power of the radius. -/
theorem weakLapLimit_le_pow_of_weakItineraryCell
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R)
    {m : ℕ} {x y : I} (hxy : x < y)
    (hcell : IsWeakItineraryCell T m x y) :
    L.value x y ≤ R.radius ^ m := by
  have hsubTop : Tendsto L.subsequence atTop atTop :=
    L.subsequence_strictMono.tendsto_atTop
  have hzero : Tendsto
      (fun n : ℕ => (m : ℝ) /
        weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop R.total_tendsto
  have hzeroSub : Tendsto
      (fun n : ℕ => (m : ℝ) /
        weakTotalLapResolvent T (R.sample (L.subsequence n)))
      atTop (nhds 0) := by
    simpa [Function.comp_apply] using hzero.comp hsubTop
  have hsampleSub : Tendsto
      (fun n : ℕ => R.sample (L.subsequence n))
      atTop (nhds R.radius) := R.sample_tendsto.comp hsubTop
  have hboundLimit : Tendsto
      (fun n : ℕ => (m : ℝ) /
          weakTotalLapResolvent T (R.sample (L.subsequence n)) +
        R.sample (L.subsequence n) ^ m)
      atTop (nhds (R.radius ^ m)) := by
    simpa using hzeroSub.add (hsampleSub.pow m)
  exact le_of_tendsto_of_tendsto'
    (L.tendsto_value hxy) hboundLimit (fun n =>
      weakNormalizedLapResolvent_le_pow_of_weakItineraryCell
        hT R hxy hcell (L.subsequence n))

/-- Around every point there are two-sided intervals of arbitrarily small
limiting weak-lap mass. -/
theorem weakLapLimit_twoSided_smallness
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R)
    (x : I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : I, a ≤ x ∧ x ≤ b ∧
      (leftEndpoint < x → a < x) ∧
      (x < rightEndpoint → x < b) ∧
      (a = x ∨ L.value a x < ε) ∧
      (x = b ∨ L.value x b < ε) := by
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  obtain ⟨m, hmpow⟩ := exists_pow_lt_of_lt_one hε hrlt
  obtain ⟨a, b, hax, hxb, haleft, haright, hcellLeft,
      hcellRight⟩ := exists_twoSided_weakItineraryCell hT m x
  refine ⟨a, b, hax, hxb, haleft, haright, ?_, ?_⟩
  · by_cases heq : a = x
    · exact Or.inl heq
    · right
      exact (weakLapLimit_le_pow_of_weakItineraryCell hT L
        (lt_of_le_of_ne hax heq) hcellLeft).trans_lt hmpow
  · by_cases heq : x = b
    · exact Or.inl heq
    · right
      exact (weakLapLimit_le_pow_of_weakItineraryCell hT L
        (lt_of_le_of_ne hxb heq) hcellRight).trans_lt hmpow

/-- Coordinate data obtained by integrating the limiting interval
functional from the left endpoint. -/
structure WeakLapResolventCoordinateData
    (T : IntervalMap) (R : WeakLapRadiusData T)
    (L : WeakLapLimitData T R) where
  coordinate : I → I
  continuous_coordinate : Continuous coordinate
  monotone_coordinate : Monotone coordinate
  surjective_coordinate : Surjective coordinate
  endpoint_zero : coordinate leftEndpoint = leftEndpoint
  endpoint_one : coordinate rightEndpoint = rightEndpoint
  interval_length : ∀ {x y : I}, x ≤ y →
    (coordinate y : ℝ) - (coordinate x : ℝ) =
      if x = y then 0 else L.value x y

/-- Adjacent additivity, normalization, and two-sided smallness build a
continuous nondecreasing surjective coordinate. -/
theorem weakLapResolventCoordinateData_exists
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    Nonempty (WeakLapResolventCoordinateData T R L) := by
  let c : I → ℝ := fun x =>
    if x = leftEndpoint then 0 else L.value leftEndpoint x
  have hc0 : c leftEndpoint = 0 := by simp [c]
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  have hrightne : rightEndpoint ≠ leftEndpoint := hends.ne'
  have hc1 : c rightEndpoint = 1 := by
    simp [c, hrightne, (weakLapLimit_bounds hT L hends).2]
  have hcbounds : ∀ x : I, 0 ≤ c x ∧ c x ≤ 1 := by
    intro x
    by_cases hxl : x = leftEndpoint
    · subst x
      simp [hc0]
    · have hlx : leftEndpoint < x :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxl)
      simpa [c, hxl] using (weakLapLimit_bounds hT L hlx).1
  let coordinate : I → I := fun x => ⟨c x, hcbounds x⟩
  have hc_interval : ∀ {x y : I}, x ≤ y →
      c y - c x = if x = y then 0 else L.value x y := by
    intro x y hxy
    by_cases hxeq : x = y
    · subst y
      simp
    · have hxy' : x < y := lt_of_le_of_ne hxy hxeq
      by_cases hxl : x = leftEndpoint
      · subst x
        have hyl : y ≠ leftEndpoint := hxy'.ne'
        simp [c, hyl, hxeq]
      · have hlx : leftEndpoint < x :=
          lt_of_le_of_ne x.property.1 (Ne.symm hxl)
        have hyl : y ≠ leftEndpoint := (hlx.trans hxy').ne'
        have hadd := weakLapLimit_adjacent hT L hlx hxy'
        simp only [c, if_neg hxl, if_neg hyl, if_neg hxeq]
        linarith
  have hcmono : Monotone c := by
    intro x y hxy
    by_cases hxeq : x = y
    · subst y
      exact le_rfl
    · have hxy' : x < y := lt_of_le_of_ne hxy hxeq
      have hnonneg := (weakLapLimit_bounds hT L hxy').1.1
      have hinc := hc_interval hxy
      rw [if_neg hxeq] at hinc
      linarith
  have hcoordinateMono : Monotone coordinate := by
    intro x y hxy
    change c x ≤ c y
    exact hcmono hxy
  have hcoordInterval : ∀ {x y : I}, x ≤ y →
      (coordinate y : ℝ) - (coordinate x : ℝ) =
        if x = y then 0 else L.value x y := by
    intro x y hxy
    exact hc_interval hxy
  have hcoordinateCont : Continuous coordinate := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨a, b, hax, hxb, haleft, haright, hleftMass,
        hrightMass⟩ := weakLapLimit_twoSided_smallness hT L x hε
    have hleftSmall : c x - c a < ε := by
      by_cases haxeq : a = x
      · subst a
        simpa using hε
      · have hmass : L.value a x < ε :=
          hleftMass.resolve_left haxeq
        have hlength := hc_interval hax
        rw [if_neg haxeq] at hlength
        linarith
    have hrightSmall : c b - c x < ε := by
      by_cases hxbeq : x = b
      · subst b
        simpa using hε
      · have hmass : L.value x b < ε :=
          hrightMass.resolve_left hxbeq
        have hlength := hc_interval hxb
        rw [if_neg hxbeq] at hlength
        linarith
    have hnear : ∀ y : I, a ≤ y → y ≤ b →
        dist (coordinate y) (coordinate x) < ε := by
      intro y hay hyb
      change dist (c y) (c x) < ε
      rw [Real.dist_eq]
      rcases le_total y x with hyx | hxy
      · rw [abs_of_nonpos (sub_nonpos.mpr (hcmono hyx))]
        have hcay : c a ≤ c y := hcmono hay
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (hcmono hxy))]
        have hyb' : c y ≤ c b := hcmono hyb
        linarith
    by_cases hxl : x = leftEndpoint
    · subst x
      have hlb : leftEndpoint < b := haright (by
        norm_num [leftEndpoint, rightEndpoint])
      let δ : ℝ := (b : ℝ) - (leftEndpoint : ℝ)
      have hδ : 0 < δ := sub_pos.mpr hlb
      refine ⟨δ, hδ, ?_⟩
      intro y hy
      have hy' : |(y : ℝ) - (leftEndpoint : ℝ)| < δ := by
        simpa [Real.dist_eq] using hy
      have hyb : y ≤ b := by
        have hupp := (abs_lt.mp hy').2
        change (y : ℝ) ≤ (b : ℝ)
        dsimp [δ] at hupp
        linarith
      exact hnear y (hax.trans y.property.1) hyb
    · by_cases hxr : x = rightEndpoint
      · subst x
        have hal : a < rightEndpoint := haleft (by
          norm_num [leftEndpoint, rightEndpoint])
        let δ : ℝ := (rightEndpoint : ℝ) - (a : ℝ)
        have hδ : 0 < δ := sub_pos.mpr hal
        refine ⟨δ, hδ, ?_⟩
        intro y hy
        have hy' : |(y : ℝ) - (rightEndpoint : ℝ)| < δ := by
          simpa [Real.dist_eq] using hy
        have hay : a ≤ y := by
          have hlow := (abs_lt.mp hy').1
          change (a : ℝ) ≤ (y : ℝ)
          dsimp [δ] at hlow
          linarith
        exact hnear y hay (y.property.2.trans hxb)
      · have hlx : leftEndpoint < x :=
          lt_of_le_of_ne x.property.1 (Ne.symm hxl)
        have hxr' : x < rightEndpoint :=
          lt_of_le_of_ne x.property.2 hxr
        have hax' : a < x := haleft hlx
        have hxb' : x < b := haright hxr'
        let δ : ℝ := min ((x : ℝ) - (a : ℝ))
          ((b : ℝ) - (x : ℝ))
        have hδ : 0 < δ :=
          lt_min (sub_pos.mpr hax') (sub_pos.mpr hxb')
        refine ⟨δ, hδ, ?_⟩
        intro y hy
        have hy' : |(y : ℝ) - (x : ℝ)| < δ := by
          simpa [Real.dist_eq] using hy
        have hay : a ≤ y := by
          have hlow := (abs_lt.mp hy').1
          have hδle : δ ≤ (x : ℝ) - (a : ℝ) := min_le_left _ _
          change (a : ℝ) ≤ (y : ℝ)
          linarith
        have hyb : y ≤ b := by
          have hupp := (abs_lt.mp hy').2
          have hδle : δ ≤ (b : ℝ) - (x : ℝ) := min_le_right _ _
          change (y : ℝ) ≤ (b : ℝ)
          linarith
        exact hnear y hay hyb
  have hcoordinate0 : coordinate leftEndpoint = leftEndpoint := by
    apply Subtype.ext
    simpa [coordinate] using hc0
  have hcoordinate1 : coordinate rightEndpoint = rightEndpoint := by
    apply Subtype.ext
    simpa [coordinate] using hc1
  have hcoordinateSurj : Surjective coordinate := by
    intro y
    have hyvals : y ∈ Set.Icc (coordinate leftEndpoint)
        (coordinate rightEndpoint) := by
      rw [hcoordinate0, hcoordinate1]
      exact y.property
    rcases intermediate_value_Icc
        (show leftEndpoint ≤ rightEndpoint by
          norm_num [leftEndpoint, rightEndpoint])
        hcoordinateCont.continuousOn hyvals with ⟨x, _hx, hxy⟩
    exact ⟨x, hxy⟩
  exact ⟨{
    coordinate := coordinate
    continuous_coordinate := hcoordinateCont
    monotone_coordinate := hcoordinateMono
    surjective_coordinate := hcoordinateSurj
    endpoint_zero := hcoordinate0
    endpoint_one := hcoordinate1
    interval_length := hcoordInterval }⟩

/-- The limiting coordinate has constant absolute expansion on every weakly
monotone interval.  Plateau intervals are therefore collapsed. -/
theorem weakLapResolventCoordinate_branch_scaling
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} {L : WeakLapLimitData T R}
    (D : WeakLapResolventCoordinateData T R L)
    {x y : I} (hxy : x ≤ y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    |(D.coordinate (T y) : ℝ) - D.coordinate (T x)| =
      R.radius⁻¹ *
        |(D.coordinate y : ℝ) - D.coordinate x| := by
  by_cases heq : x = y
  · subst y
    simp
  · have hxy' : x < y := lt_of_le_of_ne hxy heq
    let u : I := min (T x) (T y)
    let v : I := max (T x) (T y)
    have huv : u ≤ v := min_le_max
    have hsourceLen :
        (D.coordinate y : ℝ) - D.coordinate x = L.value x y := by
      have hlen := D.interval_length hxy
      rw [if_neg heq] at hlen
      exact hlen
    have hsourceAbs :
        |(D.coordinate y : ℝ) - D.coordinate x| = L.value x y := by
      have hcoord : (D.coordinate x : ℝ) ≤ D.coordinate y :=
        D.monotone_coordinate hxy
      rw [abs_of_nonneg (sub_nonneg.mpr hcoord)]
      exact hsourceLen
    have himageLen :
        (D.coordinate v : ℝ) - D.coordinate u = L.value u v := by
      rw [D.interval_length huv]
      by_cases huvEq : u = v
      · rw [huvEq]
        simp [L.value_diag]
      · simp [huvEq]
    have himageAbs :
        |(D.coordinate (T y) : ℝ) - D.coordinate (T x)| =
          L.value u v := by
      rcases le_total (T x) (T y) with hTxy | hTyx
      · have hcoord : (D.coordinate (T x) : ℝ) ≤
            D.coordinate (T y) := D.monotone_coordinate hTxy
        rw [abs_of_nonneg (sub_nonneg.mpr hcoord)]
        simpa [u, v, min_eq_left hTxy, max_eq_right hTxy] using himageLen
      · have hcoord : (D.coordinate (T y) : ℝ) ≤
            D.coordinate (T x) := D.monotone_coordinate hTyx
        rw [abs_of_nonpos (sub_nonpos.mpr hcoord)]
        simpa [u, v, min_eq_right hTyx, max_eq_left hTyx] using himageLen
    have hscale : L.value x y = R.radius * L.value u v := by
      simpa [u, v] using weakLapLimit_scaling hT L hxy' hmono
    rw [himageAbs, hsourceAbs, hscale]
    field_simp [R.radius_pos.ne']

/-- The manuscript-facing compatible coordinate. -/
structure ExpandingCompatibleCoordinate (T : IntervalMap) where
  scale : ℝ
  scale_gt_one : 1 < scale
  coordinate : I → I
  continuous_coordinate : Continuous coordinate
  monotone_coordinate : Monotone coordinate
  surjective_coordinate : Surjective coordinate
  endpoint_zero : coordinate leftEndpoint = leftEndpoint
  endpoint_one : coordinate rightEndpoint = rightEndpoint
  weak_branch_scaling : ∀ {x y : I}, x ≤ y →
    IsWeaklyMonotoneOn T (Set.Icc x y) →
      |(coordinate (T y) : ℝ) - coordinate (T x)| =
        scale * |(coordinate y : ℝ) - coordinate x|

/-- The real-valued presentation used to construct the Stieltjes measure. -/
def ExpandingCompatibleCoordinate.realCoordinate
    {T : IntervalMap} (D : ExpandingCompatibleCoordinate T) : I → ℝ :=
  fun x => (D.coordinate x : ℝ)

theorem ExpandingCompatibleCoordinate.monotone_realCoordinate
    {T : IntervalMap} (D : ExpandingCompatibleCoordinate T) :
    Monotone D.realCoordinate := by
  exact D.monotone_coordinate

theorem ExpandingCompatibleCoordinate.continuous_realCoordinate
    {T : IntervalMap} (D : ExpandingCompatibleCoordinate T) :
    Continuous D.realCoordinate := by
  exact continuous_subtype_val.comp D.continuous_coordinate

/-- A two-branch horseshoe produces a continuous nondecreasing compatible
coordinate of scale greater than one. -/
theorem expandingCompatibleCoordinate_of_horseshoe
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (H : TwoBranchHorseshoe T) :
    Nonempty (ExpandingCompatibleCoordinate T) := by
  obtain ⟨G⟩ := weakLapGrowthData_exists hT H
  obtain ⟨R⟩ := weakLapRadiusData_exists G
  obtain ⟨C⟩ := weakLapCumulativeLimitData_exists hT R
  obtain ⟨L⟩ := weakLapLimitData_exists hT C
  obtain ⟨D⟩ := weakLapResolventCoordinateData_exists hT L
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  exact ⟨{
    scale := R.radius⁻¹
    scale_gt_one := (one_lt_inv₀ R.radius_pos).2 hrlt
    coordinate := D.coordinate
    continuous_coordinate := D.continuous_coordinate
    monotone_coordinate := D.monotone_coordinate
    surjective_coordinate := D.surjective_coordinate
    endpoint_zero := D.endpoint_zero
    endpoint_one := D.endpoint_one
    weak_branch_scaling := by
      intro x y hxy hmono
      exact weakLapResolventCoordinate_branch_scaling
        hT D hxy hmono }⟩

/-! ## Stieltjes measure and the transfer eigen-equation -/

/-- The Stieltjes measure of a normalized compatible coordinate is an
atomless probability measure. -/
theorem compatibleCoordinate_stieltjes_probability
    {T : IntervalMap} (D : ExpandingCompatibleCoordinate T) :
    IsProbabilityMeasure
        (semiconjugacyMeasure D.realCoordinate
          D.monotone_realCoordinate) ∧
      ∀ x : I,
        semiconjugacyMeasure D.realCoordinate
          D.monotone_realCoordinate {x} = 0 := by
  constructor
  · refine ⟨?_⟩
    rw [semiconjugacyMeasure_univ D.realCoordinate
      D.monotone_realCoordinate D.continuous_realCoordinate]
    change ENNReal.ofReal
      ((D.coordinate rightEndpoint : ℝ) -
        (D.coordinate leftEndpoint : ℝ)) = 1
    rw [D.endpoint_zero, D.endpoint_one]
    norm_num [leftEndpoint, rightEndpoint]
  · intro x
    exact semiconjugacyMeasure_noAtoms D.realCoordinate
      D.monotone_realCoordinate D.continuous_realCoordinate x

/-- A continuous weakly monotone branch maps a closed interval onto the
closed interval spanned by its endpoint images, including the constant
case. -/
private theorem image_Icc_eq_Icc_min_max_of_weaklyMonotoneOn
    {T : IntervalMap} (hcont : Continuous T) {a b : I} (hab : a ≤ b)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc a b)) :
    T '' Set.Icc a b =
      Set.Icc (min (T a) (T b)) (max (T a) (T b)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hmono with hinc | hdec
    · have hends : T a ≤ T b :=
        hinc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
      have hlower : T a ≤ T w :=
        hinc ⟨le_rfl, hab⟩ hw hw.1
      have hupper : T w ≤ T b :=
        hinc hw ⟨hab, le_rfl⟩ hw.2
      simpa [min_eq_left hends, max_eq_right hends] using
        (⟨hlower, hupper⟩ : T w ∈ Set.Icc (T a) (T b))
    · have hends : T b ≤ T a :=
        hdec ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
      have hlower : T b ≤ T w :=
        hdec hw ⟨hab, le_rfl⟩ hw.2
      have hupper : T w ≤ T a :=
        hdec ⟨le_rfl, hab⟩ hw hw.1
      simpa [min_eq_right hends, max_eq_left hends] using
        (⟨hlower, hupper⟩ : T w ∈ Set.Icc (T b) (T a))
  · intro hz
    rcases hmono with hinc | hdec
    · have hends : T a ≤ T b :=
        hinc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
      have hz' : z ∈ Set.Icc (T a) (T b) := by
        simpa [min_eq_left hends, max_eq_right hends] using hz
      rcases intermediate_value_Icc hab hcont.continuousOn hz' with
        ⟨w, hw, hTw⟩
      exact ⟨w, hw, hTw⟩
    · have hends : T b ≤ T a :=
        hdec ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
      have hz' : z ∈ Set.Icc (T b) (T a) := by
        simpa [min_eq_right hends, max_eq_left hends] using hz
      rcases intermediate_value_Icc' hab hcont.continuousOn hz' with
        ⟨w, hw, hTw⟩
      exact ⟨w, hw, hTw⟩

/-- Coordinate scaling gives the interval identity on each assigned weak
monotonicity cell, including its endpoint convention. -/
theorem compatibleCoordinate_assignedCell_Icc_scaling
    {T : IntervalMap} (hcont : Continuous T)
    (D : ExpandingCompatibleCoordinate T)
    (P : MonotonicityPartition T) (q : P.partition.LapIndex)
    (a b : I) (hab : a ≤ b) :
    semiconjugacyMeasure D.realCoordinate D.monotone_realCoordinate
        (T '' (Set.Icc a b ∩ q.assignedCell)) =
      ENNReal.ofReal D.scale *
        semiconjugacyMeasure D.realCoordinate D.monotone_realCoordinate
          (Set.Icc a b ∩ q.assignedCell) := by
  let μ : Measure I :=
    semiconjugacyMeasure D.realCoordinate D.monotone_realCoordinate
  change μ (T '' (Set.Icc a b ∩ q.assignedCell)) =
    ENNReal.ofReal D.scale * μ (Set.Icc a b ∩ q.assignedCell)
  have hμsingleton : ∀ z : I, μ {z} = 0 := by
    intro z
    exact (compatibleCoordinate_stieltjes_probability D).2 z
  let l : I := ⟨q.left,
    P.partition.points_subset q.adjacent.1⟩
  let r : I := ⟨q.right,
    P.partition.points_subset q.adjacent.2.1⟩
  have hclosedEq : q.closedCell = Set.Icc l r := by
    ext z
    rfl
  have hassignedSub : q.assignedCell ⊆ q.closedCell :=
    q.assignedCell_subset_closedCell
  have hclosedSub : q.closedCell ⊆ q.assignedCell ∪ {r} := by
    intro z hz
    by_cases hzr : z = r
    · exact Or.inr (by simpa [hzr])
    · left
      by_cases hright : q.right = 1
      · simpa [RealPartition.LapIndex.assignedCell,
          RealPartition.LapIndex.closedCell, intervalCell, hright] using hz
      · have hz' : (z : ℝ) ∈ Set.Icc q.left q.right := by
          simpa [RealPartition.LapIndex.closedCell, intervalCell] using hz
        have hzne : (z : ℝ) ≠ q.right := by
          intro heq
          apply hzr
          apply Subtype.ext
          simpa [r] using heq
        have hzlt : (z : ℝ) < q.right :=
          lt_of_le_of_ne hz'.2 hzne
        simpa [RealPartition.LapIndex.assignedCell, hright] using
          (⟨hz'.1, hzlt⟩ : (z : ℝ) ∈ Set.Ico q.left q.right)
  let Eclosed : Set I := Set.Icc a b ∩ q.closedCell
  let Eassigned : Set I := Set.Icc a b ∩ q.assignedCell
  have hEsub : Eassigned ⊆ Eclosed := by
    intro z hz
    exact ⟨hz.1, hassignedSub hz.2⟩
  have hEclosedSub : Eclosed ⊆ Eassigned ∪ {r} := by
    intro z hz
    rcases hclosedSub hz.2 with hzassigned | hzr
    · exact Or.inl ⟨hz.1, hzassigned⟩
    · exact Or.inr hzr
  have hsourceEq : μ Eassigned = μ Eclosed := by
    apply le_antisymm
    · exact measure_mono hEsub
    · calc
        μ Eclosed ≤ μ (Eassigned ∪ {r}) := measure_mono hEclosedSub
        _ ≤ μ Eassigned + μ {r} := measure_union_le _ _
        _ = μ Eassigned := by rw [hμsingleton r, add_zero]
  have himageSub : T '' Eassigned ⊆ T '' Eclosed :=
    Set.image_mono hEsub
  have himageClosedSub : T '' Eclosed ⊆ T '' Eassigned ∪ {T r} := by
    rintro z ⟨w, hw, rfl⟩
    rcases hEclosedSub hw with hwassigned | hwr
    · exact Or.inl ⟨w, hwassigned, rfl⟩
    · have hwr' : w = r := by simpa using hwr
      subst w
      exact Or.inr (by simp)
  have himageEq : μ (T '' Eassigned) = μ (T '' Eclosed) := by
    apply le_antisymm
    · exact measure_mono himageSub
    · calc
        μ (T '' Eclosed) ≤ μ ((T '' Eassigned) ∪ {T r}) :=
          measure_mono himageClosedSub
        _ ≤ μ (T '' Eassigned) + μ {T r} := measure_union_le _ _
        _ = μ (T '' Eassigned) := by rw [hμsingleton (T r), add_zero]
  let c : I := a ⊔ l
  let d : I := b ⊓ r
  have hEclosedIcc : Eclosed = Set.Icc c d := by
    dsimp [Eclosed]
    rw [hclosedEq, Set.Icc_inter_Icc]
  have hclosedScale :
      μ (T '' Eclosed) = ENNReal.ofReal D.scale * μ Eclosed := by
    rw [hEclosedIcc]
    by_cases hcd : c ≤ d
    · have hsub : Set.Icc c d ⊆ q.closedCell := by
        intro z hz
        have hzE : z ∈ Eclosed := by
          rw [hEclosedIcc]
          exact hz
        exact hzE.2
      have hmonoClosed :
          IsWeaklyMonotoneOn T (Set.Icc c d) :=
        (P.weaklyMonotoneOn_cell q.adjacent).mono hsub
      have himage := image_Icc_eq_Icc_min_max_of_weaklyMonotoneOn
        hcont hcd hmonoClosed
      have hsourceIncrement :
          D.realCoordinate d - D.realCoordinate c =
            |D.realCoordinate d - D.realCoordinate c| := by
        rw [abs_of_nonneg]
        exact sub_nonneg.mpr (D.monotone_realCoordinate hcd)
      have htargetIncrement :
          D.realCoordinate (max (T c) (T d)) -
              D.realCoordinate (min (T c) (T d)) =
            |D.realCoordinate (T d) - D.realCoordinate (T c)| := by
        rcases le_total (T c) (T d) with hTcd | hTdc
        · have hcoord : D.realCoordinate (T c) ≤
              D.realCoordinate (T d) := D.monotone_realCoordinate hTcd
          simp [min_eq_left hTcd, max_eq_right hTcd,
            abs_of_nonneg (sub_nonneg.mpr hcoord)]
        · have hcoord : D.realCoordinate (T d) ≤
              D.realCoordinate (T c) := D.monotone_realCoordinate hTdc
          rw [min_eq_right hTdc, max_eq_left hTdc,
            abs_of_nonpos (sub_nonpos.mpr hcoord)]
          ring
      calc
        μ (T '' Set.Icc c d) =
            μ (Set.Icc (min (T c) (T d)) (max (T c) (T d))) := by
          rw [himage]
        _ = ENNReal.ofReal
            (D.realCoordinate (max (T c) (T d)) -
              D.realCoordinate (min (T c) (T d))) := by
          exact semiconjugacyMeasure_Icc D.realCoordinate
            D.monotone_realCoordinate D.continuous_realCoordinate min_le_max
        _ = ENNReal.ofReal
            |D.realCoordinate (T d) - D.realCoordinate (T c)| := by
          rw [htargetIncrement]
        _ = ENNReal.ofReal
            (D.scale * |D.realCoordinate d - D.realCoordinate c|) := by
          have hbranch :
              |D.realCoordinate (T d) - D.realCoordinate (T c)| =
                D.scale * |D.realCoordinate d - D.realCoordinate c| := by
            simpa [ExpandingCompatibleCoordinate.realCoordinate] using
              D.weak_branch_scaling hcd hmonoClosed
          rw [hbranch]
        _ = ENNReal.ofReal D.scale *
            ENNReal.ofReal |D.realCoordinate d - D.realCoordinate c| := by
          rw [ENNReal.ofReal_mul
            (le_of_lt (lt_trans zero_lt_one D.scale_gt_one))]
        _ = ENNReal.ofReal D.scale * μ (Set.Icc c d) := by
          rw [semiconjugacyMeasure_Icc D.realCoordinate
            D.monotone_realCoordinate D.continuous_realCoordinate hcd,
            ← hsourceIncrement]
    · rw [Set.Icc_eq_empty hcd]
      simp
  change μ (T '' Eassigned) = ENNReal.ofReal D.scale * μ Eassigned
  rw [himageEq, hsourceEq]
  exact hclosedScale

/-- The interval identity extends to every Borel subset of an assigned
monotonicity cell. -/
theorem compatibleCoordinate_branch_borel_scaling
    {T : IntervalMap} (hcont : Continuous T)
    (D : ExpandingCompatibleCoordinate T)
    (P : MonotonicityPartition T) (q : P.partition.LapIndex)
    {E : Set I} (hE : MeasurableSet E) :
    semiconjugacyMeasure D.realCoordinate D.monotone_realCoordinate
        (T '' (E ∩ q.assignedCell)) =
      ENNReal.ofReal D.scale *
        semiconjugacyMeasure D.realCoordinate D.monotone_realCoordinate
          (E ∩ q.assignedCell) := by
  apply semiconjugacy_branch_borel_scaling T q.assignedCell
    q.measurableSet_assignedCell
    (P.weaklyMonotoneOn_assignedCell q)
    D.realCoordinate D.monotone_realCoordinate
    D.continuous_realCoordinate D.scale
      (lt_trans zero_lt_one D.scale_gt_one).le
  · intro a b hab
    exact compatibleCoordinate_assignedCell_Icc_scaling
      hcont D P q a b hab
  · exact hE

/-- Summing the branch identities yields the plateau-aware transfer
eigen-equation. -/
theorem compatibleCoordinate_transferMeasure_eigen
    {T : IntervalMap} (hcont : Continuous T)
    (D : ExpandingCompatibleCoordinate T)
    (P : MonotonicityPartition T) :
    let μ := semiconjugacyMeasure D.realCoordinate
      D.monotone_realCoordinate
    let hμ : ∀ x : I, μ {x} = 0 :=
      fun x => semiconjugacyMeasure_noAtoms D.realCoordinate
        D.monotone_realCoordinate D.continuous_realCoordinate x
    transferMeasure T P μ hμ = ENNReal.ofReal D.scale • μ := by
  classical
  dsimp only
  let μ : Measure I :=
    semiconjugacyMeasure D.realCoordinate D.monotone_realCoordinate
  let hμ : ∀ x : I, μ {x} = 0 := fun x =>
    semiconjugacyMeasure_noAtoms D.realCoordinate
      D.monotone_realCoordinate D.continuous_realCoordinate x
  ext E hE
  rw [show transferMeasure T P μ hμ =
      piecewiseMonotoneTransferMeasure T
        P.toFiniteMonotonePartition μ hμ from rfl,
    piecewiseMonotoneTransferMeasure_apply T
      P.toFiniteMonotonePartition μ hμ hE,
    Measure.smul_apply]
  change (∑ q : P.partition.LapIndex,
      μ (T '' (E ∩ q.assignedCell))) = ENNReal.ofReal D.scale * μ E
  have hpartsMeas : ∀ q : P.partition.LapIndex,
      MeasurableSet (E ∩ q.assignedCell) := fun q =>
    hE.inter q.measurableSet_assignedCell
  have hpartsDisj : Pairwise
      (Disjoint on fun q : P.partition.LapIndex => E ∩ q.assignedCell) := by
    intro q r hqr
    change Disjoint (E ∩ q.assignedCell) (E ∩ r.assignedCell)
    rw [Set.disjoint_left]
    intro x hxq hxr
    exact Set.disjoint_left.mp
      (P.partition.assignedCells_disjoint hqr) hxq.2 hxr.2
  have hpartsCover : E =
      ⋃ q : P.partition.LapIndex, E ∩ q.assignedCell := by
    ext x
    constructor
    · intro hxE
      have hx : x ∈ ⋃ q : P.partition.LapIndex, q.assignedCell := by
        rw [P.partition.iUnion_assignedCells]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
      exact Set.mem_iUnion.mpr ⟨q, hxE, hxq⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨q, hxE, _hxq⟩
      exact hxE
  have hmeasureSum : μ E =
      ∑ q : P.partition.LapIndex, μ (E ∩ q.assignedCell) := by
    calc
      μ E = μ (⋃ q : P.partition.LapIndex,
          E ∩ q.assignedCell) := congrArg μ hpartsCover
      _ = ∑' q : P.partition.LapIndex,
          μ (E ∩ q.assignedCell) :=
        measure_iUnion hpartsDisj hpartsMeas
      _ = ∑ q : P.partition.LapIndex,
          μ (E ∩ q.assignedCell) := tsum_fintype _
  calc
    (∑ q : P.partition.LapIndex, μ (T '' (E ∩ q.assignedCell))) =
        ∑ q : P.partition.LapIndex,
          ENNReal.ofReal D.scale * μ (E ∩ q.assignedCell) := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact compatibleCoordinate_branch_borel_scaling hcont D P q hE
    _ = ENNReal.ofReal D.scale *
        ∑ q : P.partition.LapIndex, μ (E ∩ q.assignedCell) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal D.scale * μ E := by rw [← hmeasureSum]

/-- Strong partition-independent form of the weak piecewise-monotone
resolvent theorem. -/
theorem transferMeasure_eigenprobability_exists_of_horseshoe
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (H : TwoBranchHorseshoe T) :
    ∃ (scale : ℝ) (μ : Measure I),
      1 < scale ∧ IsProbabilityMeasure μ ∧
        ∃ hμ : ∀ x : I, μ {x} = 0,
          ∀ P : MonotonicityPartition T,
            transferMeasure T P μ hμ = ENNReal.ofReal scale • μ := by
  rcases expandingCompatibleCoordinate_of_horseshoe hT H with ⟨D⟩
  let μ : Measure I :=
    semiconjugacyMeasure D.realCoordinate D.monotone_realCoordinate
  have hprob : IsProbabilityMeasure μ :=
    (compatibleCoordinate_stieltjes_probability D).1
  have hμ : ∀ x : I, μ {x} = 0 :=
    (compatibleCoordinate_stieltjes_probability D).2
  refine ⟨D.scale, μ, D.scale_gt_one, hprob, hμ, ?_⟩
  intro P
  exact compatibleCoordinate_transferMeasure_eigen hT.continuous D P

/-- Quantified-partition wrapper in the exact shape used by downstream
files. -/
theorem transferMeasure_eigenprobability_exists
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (H : TwoBranchHorseshoe T) (P : MonotonicityPartition T) :
    ∃ (scale : ℝ) (μ : Measure I),
      1 < scale ∧ IsProbabilityMeasure μ ∧
        ∃ hμ : ∀ x : I, μ {x} = 0,
          transferMeasure T P μ hμ = ENNReal.ofReal scale • μ := by
  rcases transferMeasure_eigenprobability_exists_of_horseshoe hT H with
    ⟨scale, μ, hscale, hprob, hμ, htransfer⟩
  exact ⟨scale, μ, hscale, hprob, hμ, htransfer P⟩

end CommutingInterval
