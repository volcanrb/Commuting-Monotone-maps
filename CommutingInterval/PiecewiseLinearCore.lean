import CommutingInterval.CommonIterate
import CommutingInterval.ParryDefs
import CommutingInterval.PiecewiseMonotoneEigen
import CommutingInterval.PiecewiseMonotoneQuotient
import CommutingInterval.PiecewiseMonotoneResolvent
import CommutingInterval.PiecewiseMonotoneVariation
import CommutingInterval.PiecewiseLinearEndpointBasinSupport
import CommutingInterval.PiecewiseLinearFiniteArrivalSupport
import CommutingInterval.PiecewiseLinearQuotientSupport
import CommutingInterval.QuotientDefs
import CommutingInterval.SymbolicDefs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Shared finite-piece piecewise-linear infrastructure

This file contains the dependency-ordered definitions and checked middle
layers used by the direct piecewise-monotone manuscript.  The unconditional
finite-piece PL theorem is exported downstream by
`PiecewiseLinearCorrectedAssembly`.

The proof deliberately remains in the arbitrary PL category through all
fixed-component and phase quotients.  Those quotients preserve finite-piece
piecewise linearity, but they do not preserve constant absolute slope.  A
common constant-slope coordinate is therefore restored only after the orbit
and ray arguments have produced exactness.

The restoration step does not use exact uniqueness of the Parry measure.
Instead it uses a finite-dimensional complex eigenspace for the transfer of
the exact product, a joint eigenvector for the two commuting transfers, and
exact naturality of total variation.  This removes the exact-BV uniqueness
chain while retaining the quotient arguments on which finite arrival and
dense tails depend.
-/

noncomputable section

namespace CommutingInterval

open Function Set MeasureTheory

/-! ## Counterexamples and the three fixed-set normalization -/

/-- A counterexample in exactly the class of the PL-core proposition. -/
structure PiecewiseLinearCounterexample where
  P : IntervalMap
  Q : IntervalMap
  finitePieceP : FinitePiecePL P
  finitePieceQ : FinitePiecePL Q
  commute : Commute P Q
  noCommonFixed : ¬HasCommonFixedPoint P Q

/-- A counterexample restricted and affinely rescaled to a minimal common
invariant interval. -/
structure MinimalPiecewiseLinearCounterexample where
  base : PiecewiseLinearCounterexample
  ontoP : IsOnto base.P
  ontoQ : IsOnto base.Q
  core_minimal : ∀ J : ClosedSubinterval,
    IsCommonInvariantCore base.P base.Q J → J.carrier = Set.univ

/-- The product word used throughout normalization. -/
def piecewiseLinearW (P Q : IntervalMap) : IntervalMap :=
  iterateMap (P ∘ Q) 2

/-- The even return exponent attached to a finite fixed set. -/
def piecewiseLinearNormalizationExponent (K : Finset I) : ℕ :=
  2 * Nat.factorial (2 * K.card)

/-- The returned `P` word. -/
def piecewiseLinearA (P : IntervalMap) (K : Finset I) : IntervalMap :=
  iterateMap P (piecewiseLinearNormalizationExponent K)

/-- The returned `Q` word. -/
def piecewiseLinearB (Q : IntervalMap) (K : Finset I) : IntervalMap :=
  iterateMap Q (piecewiseLinearNormalizationExponent K)

/-- The returned positive product. -/
def piecewiseLinearR (P Q : IntervalMap) (K : Finset I) : IntervalMap :=
  piecewiseLinearA P K ∘ piecewiseLinearB Q K

/-- The square of the returned product. -/
def piecewiseLinearS (P Q : IntervalMap) (K : Finset I) : IntervalMap :=
  iterateMap (piecewiseLinearR P Q K) 2

/-- A normalized counterexample has finite fixed sets for `W`, `R`, and
`S = R^2`, with the finsets recording those sets exactly. -/
structure NormalizedPiecewiseLinearCounterexample where
  base : MinimalPiecewiseLinearCounterexample
  fixedW : Finset I
  fixedW_spec : ∀ x : I,
    x ∈ fixedW ↔ IsFixedPoint (piecewiseLinearW base.base.P base.base.Q) x
  fixedR : Finset I
  fixedR_spec : ∀ x : I,
    x ∈ fixedR ↔
      IsFixedPoint (piecewiseLinearR base.base.P base.base.Q fixedW) x
  fixedS : Finset I
  fixedS_spec : ∀ x : I,
    x ∈ fixedS ↔
      IsFixedPoint (piecewiseLinearS base.base.P base.base.Q fixedW) x

/-- Lexicographic comparison of the three normalization counts. -/
def FixedCountLexLE
    (aW aR aS bW bR bS : ℕ) : Prop :=
  aW < bW ∨
    (aW = bW ∧ (aR < bR ∨ (aR = bR ∧ aS ≤ bS)))

/-- A normalized counterexample minimizing the manuscript's ordered triple
`(#Fix(W), #Fix(R), #Fix(S))`. -/
structure LeastNormalizedPiecewiseLinearCounterexample where
  base : NormalizedPiecewiseLinearCounterexample
  lex_minimal : ∀ D : NormalizedPiecewiseLinearCounterexample,
    FixedCountLexLE
      base.fixedW.card base.fixedR.card base.fixedS.card
      D.fixedW.card D.fixedR.card D.fixedS.card

namespace NormalizedPiecewiseLinearCounterexample

def P (C : NormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.base.P

def Q (C : NormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.base.Q

def W (C : NormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  piecewiseLinearW C.P C.Q

def L (C : NormalizedPiecewiseLinearCounterexample) : ℕ :=
  piecewiseLinearNormalizationExponent C.fixedW

def A (C : NormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  piecewiseLinearA C.P C.fixedW

def B (C : NormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  piecewiseLinearB C.Q C.fixedW

def R (C : NormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  piecewiseLinearR C.P C.Q C.fixedW

def S (C : NormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  piecewiseLinearS C.P C.Q C.fixedW

end NormalizedPiecewiseLinearCounterexample

namespace LeastNormalizedPiecewiseLinearCounterexample

def P (C : LeastNormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.P

def Q (C : LeastNormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.Q

def W (C : LeastNormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.W

def L (C : LeastNormalizedPiecewiseLinearCounterexample) : ℕ :=
  C.base.L

def A (C : LeastNormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.A

def B (C : LeastNormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.B

def R (C : LeastNormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.R

def S (C : LeastNormalizedPiecewiseLinearCounterexample) : IntervalMap :=
  C.base.S

theorem finitePieceP (C : LeastNormalizedPiecewiseLinearCounterexample) :
    FinitePiecePL C.P :=
  C.base.base.base.finitePieceP

theorem finitePieceQ (C : LeastNormalizedPiecewiseLinearCounterexample) :
    FinitePiecePL C.Q :=
  C.base.base.base.finitePieceQ

theorem continuousP (C : LeastNormalizedPiecewiseLinearCounterexample) :
    Continuous C.P :=
  C.finitePieceP.1

theorem continuousQ (C : LeastNormalizedPiecewiseLinearCounterexample) :
    Continuous C.Q :=
  C.finitePieceQ.1

theorem commute (C : LeastNormalizedPiecewiseLinearCounterexample) :
    Commute C.P C.Q :=
  C.base.base.base.commute

theorem noCommonFixed (C : LeastNormalizedPiecewiseLinearCounterexample) :
    ¬HasCommonFixedPoint C.P C.Q :=
  C.base.base.base.noCommonFixed

end LeastNormalizedPiecewiseLinearCounterexample

theorem piecewiseLinearNormalizationExponent_pos (K : Finset I) :
    0 < piecewiseLinearNormalizationExponent K := by
  exact Nat.mul_pos (by decide) (Nat.factorial_pos _)

/-! ## PL finiteness and safe finite quotients -/

/-- The elementary PL closure and quotient facts used by every restart. -/
structure PiecewiseLinearFinitenessPackage : Prop where
  comp : ∀ {T U : IntervalMap},
    FinitePiecePL T → FinitePiecePL U → FinitePiecePL (T ∘ U)
  iterate : ∀ {T : IntervalMap},
    FinitePiecePL T → ∀ n : ℕ, FinitePiecePL (iterateMap T n)
  fixedPoints_finiteUnion : ∀ {T : IntervalMap},
    FinitePiecePL T → IsFiniteUnionClosedSubintervals (fixedPoints T)
  noFlat_finiteLaps : ∀ {T : IntervalMap},
    FinitePiecePL T → ¬HasFlatInterval T →
      HasFiniteStrictMonotonicityLaps T
  quotient_descended_PL :
    ∀ (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
      (_hT : FinitePiecePL T) (hrespect : RespectsFibres π.toFun T),
      FinitePiecePL (descendedMap π T hrespect)
  quotient_descended_commute :
    ∀ (π : CanonicalFiniteIntervalQuotient) (P Q : IntervalMap)
      (hP : RespectsFibres π.toFun P) (hQ : RespectsFibres π.toFun Q),
      Commute P Q →
        Commute (descendedMap π P hP) (descendedMap π Q hQ)
  quotient_fixedPoints_exact :
    ∀ (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
      (hrespect : RespectsFibres π.toFun T),
      CollapsesExactlyFixedComponents π T →
        FixedPointsDescendExactly π.toFun T (descendedMap π T hrespect)
  quotient_fixedCount_drops :
    ∀ (π T Tbar : IntervalMap),
      FixedPointsDescendExactly π T Tbar →
      IdentifiesDistinctFixedPoints π T →
      (fixedPoints T).Finite → FixedPointCardinalityDrops T Tbar
  quotient_preserves_noCommon_on_minimalCore :
    ∀ (C : MinimalPiecewiseLinearCounterexample)
      (π : CanonicalFiniteIntervalQuotient)
      (hP : RespectsFibres π.toFun C.base.P)
      (hQ : RespectsFibres π.toFun C.base.Q),
      ¬HasCommonFixedPoint
        (descendedMap π C.base.P hP) (descendedMap π C.base.Q hQ)

/-- An affine branch has one of the two weak monotonicity orientations. -/
private theorem affineOn_weaklyMonotoneOn_plCore
    {T : IntervalMap} {s : Set I} (h : IsAffineOn T s) :
    IsWeaklyMonotoneOn T s := by
  rcases h with ⟨m, c, hformula⟩
  by_cases hm : 0 ≤ m
  · left
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left
      (Subtype.coe_le_coe.mpr hxy) hm) c
  · right
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonpos_left
      (Subtype.coe_le_coe.mpr hxy) (le_of_not_ge hm)) c

/-- Finite-piece PL maps are closed under composition. -/
theorem finitePiecePL_comp
    {T U : IntervalMap} (hT : FinitePiecePL T) (hU : FinitePiecePL U) :
    FinitePiecePL (T ∘ U) := by
  rcases hT with ⟨hTcont, pT, hpT⟩
  rcases hU with ⟨hUcont, pU, hpU⟩
  let wT : MonotonicityPartition T :=
    ⟨pT, fun _ _ hab => affineOn_weaklyMonotoneOn_plCore (hpT hab)⟩
  let wU : MonotonicityPartition U :=
    ⟨pU, fun _ _ hab => affineOn_weaklyMonotoneOn_plCore (hpU hab)⟩
  refine ⟨hTcont.comp hUcont, wU.compositionRefinement wT, ?_⟩
  intro a b hab
  obtain ⟨aU, bU, hUadj, hsource⟩ :=
    (wU.compositionRefinement_refines wT).adjacent_subset hab
  obtain ⟨mU, cU, hUformula⟩ := hpU hUadj
  obtain ⟨_hUweak, aT, bT, hTadj, hmaps⟩ :=
    wU.composition_cell hUcont wT hab
  obtain ⟨mT, cT, hTformula⟩ := hpT hTadj
  refine ⟨mT * mU, mT * cU + cT, ?_⟩
  intro x hx
  change (T (U x) : ℝ) = _
  rw [hTformula (U x) (hmaps hx), hUformula x (hsource hx)]
  ring

/-- Finite-piece PL maps are closed under every finite iterate. -/
theorem finitePiecePL_iterate
    {T : IntervalMap} (hT : FinitePiecePL T) (n : ℕ) :
    FinitePiecePL (iterateMap T n) := by
  induction n with
  | zero =>
      refine ⟨continuous_id, RealPartition.trivial, ?_⟩
      intro a b _hab
      refine ⟨1, 0, ?_⟩
      intro x _hx
      simp [iterateMap]
  | succ n ih =>
      have hcomp := finitePiecePL_comp hT ih
      have hmap : iterateMap T (n + 1) = T ∘ iterateMap T n := by
        funext x
        exact Function.iterate_succ_apply' T n x
      rw [hmap]
      exact hcomp

/-- The fixed set of a finite-piece PL map is a finite union of closed
subintervals, including singleton components. -/
theorem finitePiecePL_fixedPoints_finiteUnion
    {T : IntervalMap} (hT : FinitePiecePL T) :
    IsFiniteUnionClosedSubintervals (fixedPoints T) := by
  classical
  rcases hT with ⟨_hcontinuous, p, hp⟩
  let Good := {q : p.LapIndex //
    (fixedPoints T ∩ q.closedCell).Nonempty}
  let witness : Good → I := fun q => Classical.choose q.property
  have witness_spec (q : Good) :
      witness q ∈ fixedPoints T ∩ q.1.closedCell :=
    Classical.choose_spec q.property
  let cellInterval : p.LapIndex → ClosedSubinterval := fun q =>
    { left := ⟨q.left, p.points_subset q.adjacent.1⟩
      right := ⟨q.right, p.points_subset q.adjacent.2.1⟩
      left_le_right := q.adjacent.2.2.1.le }
  have cellInterval_carrier (q : p.LapIndex) :
      (cellInterval q).carrier = q.closedCell := by
    rfl
  let pointInterval : I → ClosedSubinterval := fun x =>
    { left := x, right := x, left_le_right := le_rfl }
  let component : Good → ClosedSubinterval := fun q =>
    if hall : q.1.closedCell ⊆ fixedPoints T then
      cellInterval q
    else
      pointInterval (witness q)
  have component_carrier (q : Good) :
      (component q).carrier = fixedPoints T ∩ q.1.closedCell := by
    by_cases hall : q.1.closedCell ⊆ fixedPoints T
    · rw [show component q = cellInterval q by simp [component, hall],
        cellInterval_carrier]
      ext x
      constructor
      · intro hx
        exact ⟨hall hx, hx⟩
      · exact fun hx => hx.2
    · have hmne : ∀ m c : ℝ,
          (∀ x ∈ q.1.closedCell,
            (T x : ℝ) = m * (x : ℝ) + c) → m ≠ 1 := by
        intro m c hformula hm
        apply hall
        intro x hx
        apply Subtype.ext
        have hwformula := hformula (witness q) (witness_spec q).2
        have hxformula := hformula x hx
        have hwfixed := congrArg Subtype.val (witness_spec q).1
        rw [hm] at hwformula hxformula
        rw [hwfixed] at hwformula
        linarith
      obtain ⟨m, c, hformula⟩ := hp q.1.adjacent
      have hunique : ∀ x ∈ q.1.closedCell,
          x ∈ fixedPoints T → x = witness q := by
        intro x hxcell hxfixed
        have hxm := hformula x hxcell
        have hwm := hformula (witness q) (witness_spec q).2
        have hxfixed' := congrArg Subtype.val hxfixed
        have hwfixed' := congrArg Subtype.val (witness_spec q).1
        rw [hxfixed'] at hxm
        rw [hwfixed'] at hwm
        have hprod : (m - 1) *
            ((x : ℝ) - (witness q : ℝ)) = 0 := by
          nlinarith
        have hmone : m - 1 ≠ 0 := sub_ne_zero.mpr (hmne m c hformula)
        have hxeq : (x : ℝ) - (witness q : ℝ) = 0 :=
          (mul_eq_zero.mp hprod).resolve_left hmone
        apply Subtype.ext
        linarith
      rw [show component q = pointInterval (witness q) by
        simp [component, hall]]
      ext x
      constructor
      · intro hx
        have hxw : x = witness q := le_antisymm hx.2 hx.1
        subst x
        exact witness_spec q
      · intro hx
        have hxw : x = witness q := hunique x hx.2 hx.1
        subst x
        exact ⟨le_rfl, le_rfl⟩
  let n := Fintype.card Good
  let e : Fin n ≃ Good := (Fintype.equivFin Good).symm
  refine ⟨n, fun i => component (e i), ?_⟩
  ext x
  constructor
  · intro hxfixed
    obtain ⟨a, b, hab, hxcell⟩ := p.exists_adjacent_containing x
    have hpair : (a, b) ∈ p.adjacentPairs := by
      rw [RealPartition.adjacentPairs]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩
    let q : p.LapIndex := ⟨(a, b), hpair⟩
    have hxcell' : x ∈ q.closedCell := by
      exact hxcell
    let qgood : Good := ⟨q, ⟨x, hxfixed, hxcell'⟩⟩
    let i : Fin n := (Fintype.equivFin Good) qgood
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [component_carrier]
    have hei : e i = qgood := by
      simp [e, i]
    rw [hei]
    exact ⟨hxfixed, hxcell'⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [component_carrier] at hi
    exact hi.1

/-- Removing flat intervals from a finite-piece PL presentation leaves
finitely many strict monotonicity laps. -/
theorem finitePiecePL_noFlat_finiteStrictLaps
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hflat : ¬HasFlatInterval T) :
    HasFiniteStrictMonotonicityLaps T := by
  rcases hT.2 with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro a b hab
  rcases hp hab with ⟨m, c, hformula⟩
  have hm : m ≠ 0 := by
    intro hm0
    apply hflat
    let aI : I := ⟨a, p.points_subset hab.1⟩
    let bI : I := ⟨b, p.points_subset hab.2.1⟩
    let J : ClosedSubinterval := ⟨aI, bI, hab.2.2.1.le⟩
    refine ⟨J, hab.2.2.1, ?_⟩
    intro x hx y hy
    apply Subtype.ext
    have hxcell : x ∈ intervalCell a b := hx
    have hycell : y ∈ intervalCell a b := hy
    simp [hformula x hxcell, hformula y hycell, hm0]
  rcases lt_or_gt_of_ne hm with hmneg | hmpos
  · right
    intro x hx y hy hxy
    apply Subtype.coe_lt_coe.mp
    rw [hformula x hx, hformula y hy]
    have hxy' : (x : ℝ) < (y : ℝ) := hxy
    nlinarith
  · left
    intro x hx y hy hxy
    apply Subtype.coe_lt_coe.mp
    rw [hformula x hx, hformula y hy]
    have hxy' : (x : ℝ) < (y : ℝ) := hxy
    nlinarith

/-- A fibre-respecting finite-piece PL map descends through a canonical
finite interval quotient as another finite-piece PL map. -/
private theorem continuous_descendedMap_plCore
    (π : CanonicalFiniteIntervalQuotient) {T : IntervalMap}
    (hT : Continuous T) (hrespect : RespectsFibres π.toFun T) :
    Continuous (descendedMap π T hrespect) := by
  have hquot : Topology.IsQuotientMap π.toFun :=
    IsQuotientMap.of_surjective_continuous
      π.surjective_toFun π.continuous_toFun
  apply hquot.continuous_iff.mpr
  have heq : descendedMap π T hrespect ∘ π.toFun = π.toFun ∘ T := by
    funext x
    exact (intertwines_descendedMap π T hrespect x).symm
  rw [heq]
  exact π.continuous_toFun.comp hT

/-- A point which is not a partition vertex lies strictly inside a cell. -/
private theorem RealPartition.exists_adjacent_around_plCore
    (p : RealPartition) {x : ℝ} (hxI : x ∈ I)
    (hx : x ∉ p.points) :
    ∃ c d, p.Adjacent c d ∧ c < x ∧ x < d := by
  classical
  let lower := p.points.filter fun z ↦ z ≤ x
  let upper := p.points.filter fun z ↦ x ≤ z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, p.zero_mem, hxI.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    simp [upper, p.one_mem, hxI.2]
  obtain ⟨c, hc, hcmax⟩ := lower.exists_max_image id hlower
  obtain ⟨d, hd, hdmin⟩ := upper.exists_min_image id hupper
  have hc' := Finset.mem_filter.mp hc
  have hd' := Finset.mem_filter.mp hd
  have hcx : c < x :=
    lt_of_le_of_ne hc'.2 (fun h ↦ hx (by simpa [h] using hc'.1))
  have hxd : x < d :=
    lt_of_le_of_ne hd'.2 (fun h ↦ hx (by simpa [h] using hd'.1))
  refine ⟨c, d, ⟨hc'.1, hd'.1, hcx.trans hxd, ?_⟩, hcx, hxd⟩
  intro e he hed
  by_cases hex : e ≤ x
  · have helower : e ∈ lower := Finset.mem_filter.mpr ⟨he, hex⟩
    have hec : e ≤ c := by simpa using hcmax e helower
    exact (not_lt_of_ge hec) hed.1
  · have hxe : x ≤ e := (lt_of_not_ge hex).le
    have heupper : e ∈ upper := Finset.mem_filter.mpr ⟨he, hxe⟩
    have hde : d ≤ e := by simpa using hdmin e heupper
    exact (not_lt_of_ge hde) hed.2

/-- A partition cell enclosing a nondegenerate interval which contains no
partition point in its interior. -/
private theorem RealPartition.exists_adjacent_superset_plCore
    (p : RealPartition) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hab : a < b)
    (hnone : ∀ c ∈ p.points, ¬(a < c ∧ c < b)) :
    ∃ c d, p.Adjacent c d ∧ Set.Icc a b ⊆ Set.Icc c d := by
  classical
  let lower := p.points.filter fun x ↦ x ≤ a
  let upper := p.points.filter fun x ↦ b ≤ x
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
  · intro z hz
    exact ⟨hca.trans hz.1, hz.2.trans hbd⟩

/-- The partition cell immediately to the right of a point. -/
private theorem RealPartition.exists_adjacent_right_plCore
    (p : RealPartition) {x : ℝ} (hxI : x ∈ I) (hxright : x < 1) :
    ∃ a b : ℝ, p.Adjacent a b ∧ a ≤ x ∧ x < b := by
  classical
  let lower := p.points.filter fun z ↦ z ≤ x
  let upper := p.points.filter fun z ↦ x < z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, p.zero_mem, hxI.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    simp [upper, p.one_mem, hxright]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨a, b, ⟨ha'.1, hb'.1, ha'.2.trans_lt hb'.2, ?_⟩,
    ha'.2, hb'.2⟩
  intro z hz hzb
  by_cases hzx : z ≤ x
  · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzx⟩
    have hza : z ≤ a := by simpa using hamax z hzlower
    exact (not_lt_of_ge hza) hzb.1
  · have hxz : x < z := lt_of_not_ge hzx
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hxz⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzb.2

theorem finitePiecePL_descendedMap
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hT : FinitePiecePL T) (hrespect : RespectsFibres π.toFun T) :
    FinitePiecePL (descendedMap π T hrespect) := by
  classical
  let H : IntervalMap := π.toFun ∘ T
  have hH : FinitePiecePL H := by
    dsimp [H]
    exact finitePiecePL_comp π.finitePiecePL_toFun hT
  rcases π.finitePiecePL_toFun.2 with ⟨pπ, hπcells⟩
  rcases hH.2 with ⟨pH, hHcells⟩
  let imageπ : {x : ℝ // x ∈ pπ.points} → ℝ := fun x ↦
    (π (⟨x, pπ.points_subset x.property⟩ : I) : ℝ)
  let imageH : {x : ℝ // x ∈ pH.points} → ℝ := fun x ↦
    (π (⟨x, pH.points_subset x.property⟩ : I) : ℝ)
  let targetPoints : Finset ℝ :=
    pπ.points.attach.image imageπ ∪ pH.points.attach.image imageH
  have hπleft : π leftEndpoint = leftEndpoint := by
    obtain ⟨x, hx⟩ := π.surjective_toFun leftEndpoint
    apply Subtype.ext
    change (π leftEndpoint : ℝ) = 0
    have hmono := π.monotone_toFun
      (show leftEndpoint ≤ x by exact x.property.1)
    have hxreal := congrArg Subtype.val hx
    have hlower := (π leftEndpoint).property.1
    change (π leftEndpoint : ℝ) ≤ (π x : ℝ) at hmono
    change (π x : ℝ) = 0 at hxreal
    linarith
  have hπright : π rightEndpoint = rightEndpoint := by
    obtain ⟨x, hx⟩ := π.surjective_toFun rightEndpoint
    apply Subtype.ext
    change (π rightEndpoint : ℝ) = 1
    have hmono := π.monotone_toFun
      (show x ≤ rightEndpoint by exact x.property.2)
    have hxreal := congrArg Subtype.val hx
    have hupper := (π rightEndpoint).property.2
    change (π x : ℝ) ≤ (π rightEndpoint : ℝ) at hmono
    change (π x : ℝ) = 1 at hxreal
    linarith
  let q : RealPartition :=
    { points := targetPoints
      zero_mem := by
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨⟨0, pπ.zero_mem⟩, Finset.mem_attach _ _, ?_⟩
        dsimp [imageπ]
        exact congrArg Subtype.val hπleft
      one_mem := by
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨⟨1, pπ.one_mem⟩, Finset.mem_attach _ _, ?_⟩
        dsimp [imageπ]
        exact congrArg Subtype.val hπright
      points_subset := by
        intro y hy
        rcases Finset.mem_union.mp hy with hy | hy
        · rcases Finset.mem_image.mp hy with ⟨x, _hx, rfl⟩
          exact (π (⟨x, pπ.points_subset x.property⟩ : I)).property
        · rcases Finset.mem_image.mp hy with ⟨x, _hx, rfl⟩
          exact (π (⟨x, pH.points_subset x.property⟩ : I)).property }
  refine ⟨continuous_descendedMap_plCore π hT.1 hrespect, q, ?_⟩
  intro u v huv
  have huvlt : u < v := huv.2.2.1
  let yreal : ℝ := (u + v) / 2
  have hyuv : yreal ∈ Set.Ioo u v := by
    dsimp [yreal]
    constructor <;> linarith
  have hyI : yreal ∈ I :=
    ⟨(q.points_subset huv.1).1.trans hyuv.1.le,
      hyuv.2.le.trans (q.points_subset huv.2.1).2⟩
  let y : I := ⟨yreal, hyI⟩
  obtain ⟨x, hx⟩ := π.surjective_toFun y
  have hπxreal : (π x : ℝ) = yreal := congrArg Subtype.val hx
  have hxnotπ : (x : ℝ) ∉ pπ.points := by
    intro hxp
    have himage : (π x : ℝ) ∈ q.points := by
      change (π x : ℝ) ∈ targetPoints
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨⟨(x : ℝ), hxp⟩, Finset.mem_attach _ _, rfl⟩
    exact huv.2.2.2 (π x : ℝ) himage
      (by simpa [hπxreal] using hyuv)
  have hxnotH : (x : ℝ) ∉ pH.points := by
    intro hxp
    have himage : (π x : ℝ) ∈ q.points := by
      change (π x : ℝ) ∈ targetPoints
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨⟨(x : ℝ), hxp⟩, Finset.mem_attach _ _, rfl⟩
    exact huv.2.2.2 (π x : ℝ) himage
      (by simpa [hπxreal] using hyuv)
  obtain ⟨a, b, hab, hax, hxb⟩ :=
    pπ.exists_adjacent_around_plCore x.property hxnotπ
  obtain ⟨m, c, hπformula⟩ := hπcells hab
  let aI : I := ⟨a, pπ.points_subset hab.1⟩
  let bI : I := ⟨b, pπ.points_subset hab.2.1⟩
  have haCell : aI ∈ intervalCell a b := ⟨le_rfl, hab.2.2.1.le⟩
  have hbCell : bI ∈ intervalCell a b := ⟨hab.2.2.1.le, le_rfl⟩
  have hxCell : x ∈ intervalCell a b := ⟨hax.le, hxb.le⟩
  have hπa := hπformula aI haCell
  have hπb := hπformula bI hbCell
  have hπxform := hπformula x hxCell
  have hπaTarget : (π aI : ℝ) ∈ q.points := by
    change (π aI : ℝ) ∈ targetPoints
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨⟨a, hab.1⟩, Finset.mem_attach _ _, rfl⟩
  have hπbTarget : (π bI : ℝ) ∈ q.points := by
    change (π bI : ℝ) ∈ targetPoints
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨⟨b, hab.2.1⟩, Finset.mem_attach _ _, rfl⟩
  have hmne : m ≠ 0 := by
    intro hmzero
    have hπax : (π aI : ℝ) = (π x : ℝ) := by
      rw [hπa, hπxform, hmzero]
      ring
    apply huv.2.2.2 (π aI : ℝ) hπaTarget
    rw [hπax, hπxreal]
    exact hyuv
  have hmnonneg : 0 ≤ m := by
    have hmono := π.monotone_toFun (show aI ≤ x from hax.le)
    change (π aI : ℝ) ≤ (π x : ℝ) at hmono
    rw [hπa, hπxform] at hmono
    nlinarith
  have hm : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmne)
  have hπale : (π aI : ℝ) ≤ u := by
    apply le_of_not_gt
    intro hua
    apply huv.2.2.2 (π aI : ℝ) hπaTarget
    refine ⟨hua, ?_⟩
    have hmono := π.monotone_toFun (show aI ≤ x from hax.le)
    change (π aI : ℝ) ≤ (π x : ℝ) at hmono
    rw [hπxreal] at hmono
    exact hmono.trans_lt hyuv.2
  have hvleπb : v ≤ (π bI : ℝ) := by
    apply le_of_not_gt
    intro hbv
    apply huv.2.2.2 (π bI : ℝ) hπbTarget
    refine ⟨?_, hbv⟩
    have hmono := π.monotone_toFun (show x ≤ bI from hxb.le)
    change (π x : ℝ) ≤ (π bI : ℝ) at hmono
    rw [hπxreal] at hmono
    exact hyuv.1.trans_le hmono
  let xu : ℝ := (u - c) / m
  let xv : ℝ := (v - c) / m
  have haxu : a ≤ xu := by
    dsimp [xu]
    apply (le_div_iff₀ hm).2
    rw [hπa] at hπale
    linarith
  have hxub : xu ≤ b := by
    dsimp [xu]
    apply (div_le_iff₀ hm).2
    rw [hπb] at hvleπb
    linarith
  have haxv : a ≤ xv := by
    dsimp [xv]
    apply (le_div_iff₀ hm).2
    rw [hπa] at hπale
    linarith
  have hxvb : xv ≤ b := by
    dsimp [xv]
    apply (div_le_iff₀ hm).2
    rw [hπb] at hvleπb
    linarith
  have hxult : xu < xv := by
    dsimp [xu, xv]
    exact div_lt_div_of_pos_right (sub_lt_sub_right huvlt c) hm
  have hxuI : xu ∈ I :=
    ⟨(pπ.points_subset hab.1).1.trans haxu,
      hxub.trans (pπ.points_subset hab.2.1).2⟩
  have hxvI : xv ∈ I :=
    ⟨(pπ.points_subset hab.1).1.trans haxv,
      hxvb.trans (pπ.points_subset hab.2.1).2⟩
  have hnoneH : ∀ z ∈ pH.points, ¬(xu < z ∧ z < xv) := by
    intro z hz hbetween
    let zI : I := ⟨z, pH.points_subset hz⟩
    have hzCell : zI ∈ intervalCell a b :=
      ⟨(haxu.trans_lt hbetween.1).le,
        (hbetween.2.trans_le hxvb).le⟩
    have hπz := hπformula zI hzCell
    have hπzTarget : (π zI : ℝ) ∈ q.points := by
      change (π zI : ℝ) ∈ targetPoints
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩
    apply huv.2.2.2 (π zI : ℝ) hπzTarget
    dsimp [xu, xv] at hbetween
    rw [hπz]
    change u < m * z + c ∧ m * z + c < v
    have hleft := (div_lt_iff₀ hm).1 hbetween.1
    have hright := (lt_div_iff₀ hm).1 hbetween.2
    constructor <;> nlinarith
  let xuI : I := ⟨xu, hxuI⟩
  let xvI : I := ⟨xv, hxvI⟩
  obtain ⟨d, e, hde, hsource⟩ :=
    pH.exists_adjacent_superset hxuI hxvI hxult hnoneH
  obtain ⟨r, s, hHformula⟩ := hHcells hde
  refine ⟨r / m, s - r * c / m, ?_⟩
  intro z hz
  have hzpreI : ((z : ℝ) - c) / m ∈ I := by
    have hzlower : xu ≤ ((z : ℝ) - c) / m := by
      dsimp [xu]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.1 c) hm.le
    have hzupper : ((z : ℝ) - c) / m ≤ xv := by
      dsimp [xv]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.2 c) hm.le
    exact ⟨hxuI.1.trans hzlower, hzupper.trans hxvI.2⟩
  let zpre : I := ⟨((z : ℝ) - c) / m, hzpreI⟩
  have hzpreBounds : (zpre : ℝ) ∈ Set.Icc xu xv := by
    constructor
    · dsimp [xu, zpre]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.1 c) hm.le
    · dsimp [xv, zpre]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.2 c) hm.le
  have hzpreCell : zpre ∈ intervalCell a b := by
    exact ⟨haxu.trans hzpreBounds.1, hzpreBounds.2.trans hxvb⟩
  have hπpre : π zpre = z := by
    apply Subtype.ext
    have hformula := hπformula zpre hzpreCell
    change (π zpre : ℝ) = (z : ℝ)
    rw [hformula]
    dsimp [zpre]
    field_simp [hm.ne']
    ring
  have hdesc : descendedMap π T hrespect z = H zpre := by
    calc
      descendedMap π T hrespect z =
          descendedMap π T hrespect (π zpre) := by rw [hπpre]
      _ = π (T zpre) := (intertwines_descendedMap π T hrespect zpre).symm
      _ = H zpre := rfl
  calc
    (descendedMap π T hrespect z : ℝ) = (H zpre : ℝ) :=
      congrArg Subtype.val hdesc
    _ = r * (zpre : ℝ) + s := hHformula zpre (hsource hzpreBounds)
    _ = r / m * (z : ℝ) + (s - r * c / m) := by
      dsimp [zpre]
      field_simp [hm.ne']
      ring

/-- Commutation descends through a common surjective quotient. -/
theorem commute_descendedMap
    (π : CanonicalFiniteIntervalQuotient) (P Q : IntervalMap)
    (hP : RespectsFibres π.toFun P) (hQ : RespectsFibres π.toFun Q)
    (hcomm : Commute P Q) :
    Commute (descendedMap π P hP) (descendedMap π Q hQ) := by
  intro y
  obtain ⟨x, rfl⟩ := π.surjective_toFun y
  let Pbar := descendedMap π P hP
  let Qbar := descendedMap π Q hQ
  have hPbar := intertwines_descendedMap π P hP
  have hQbar := intertwines_descendedMap π Q hQ
  change Pbar (Qbar (π x)) = Qbar (Pbar (π x))
  calc
    Pbar (Qbar (π x)) = Pbar (π (Q x)) :=
      congrArg Pbar (hQbar x).symm
    _ = π (P (Q x)) := (hPbar (Q x)).symm
    _ = π (Q (P x)) := congrArg π.toFun (hcomm x)
    _ = Qbar (π (P x)) := hQbar (P x)
    _ = Qbar (Pbar (π x)) := congrArg Qbar (hPbar x)

/-- Collapsing exactly the nondegenerate fixed components gives the exact
fixed-set image identity downstairs. -/
theorem fixedPoints_descendedMap_exact
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hrespect : RespectsFibres π.toFun T)
    (hcollapse : CollapsesExactlyFixedComponents π T) :
    FixedPointsDescendExactly π.toFun T (descendedMap π T hrespect) := by
  ext y
  constructor
  · intro hy
    change descendedMap π T hrespect y = y at hy
    obtain ⟨x, hx⟩ := π.surjective_toFun y
    have hπTx : π (T x) = π x := by
      calc
        π (T x) = descendedMap π T hrespect (π x) :=
          intertwines_descendedMap π T hrespect x
        _ = descendedMap π T hrespect y := congrArg _ hx
        _ = y := hy
        _ = π x := hx.symm
    by_cases hcollapsed : x ∈ π.collapsedSet
    · rcases Set.mem_iUnion.mp hcollapsed with ⟨i, hxi⟩
      have hxfixed : x ∈ fixedPoints T :=
        (hcollapse.1 i).2.1 hxi
      exact ⟨x, hxfixed, hx⟩
    · have hTxmem : T x ∈ π.fibre x := hπTx
      rw [π.fibre_eq_singleton_of_isUncollapsed hcollapsed,
        Set.mem_singleton_iff] at hTxmem
      exact ⟨x, hTxmem, hx⟩
  · rintro ⟨x, hxfixed, rfl⟩
    change descendedMap π T hrespect (π x) = π x
    rw [← intertwines_descendedMap π T hrespect x, hxfixed]

/-- Identifying two fixed points strictly lowers a finite fixed count once
the exact fixed-set image identity is known. -/
theorem fixedPointCardinalityDrops_of_exact_image
    (π T Tbar : IntervalMap)
    (hexact : FixedPointsDescendExactly π T Tbar)
    (hidentifies : IdentifiesDistinctFixedPoints π T)
    (hfinite : (fixedPoints T).Finite) :
    FixedPointCardinalityDrops T Tbar := by
  have hbarfinite : (fixedPoints Tbar).Finite := by
    rw [hexact]
    exact hfinite.image π
  refine ⟨hfinite, hbarfinite, ?_⟩
  have himage_lt : (π '' fixedPoints T).ncard <
      (fixedPoints T).ncard := by
    have hle := Set.ncard_image_le (f := π) hfinite
    apply lt_of_le_of_ne hle
    intro heq
    have hinjective : Set.InjOn π (fixedPoints T) :=
      Set.injOn_of_ncard_image_eq heq hfinite
    obtain ⟨x, y, hx, hy, hxy, hπxy⟩ := hidentifies
    exact hxy (hinjective hx hy hπxy)
  rw [hexact]
  exact himage_lt

/-- On a minimal common core, a nonconstant respected quotient cannot gain
a common fixed point: its fixed fibre would be the whole source interval. -/
theorem noCommonFixedPoint_descendedMap_of_minimalCore
    (C : MinimalPiecewiseLinearCounterexample)
    (π : CanonicalFiniteIntervalQuotient)
    (hP : RespectsFibres π.toFun C.base.P)
    (hQ : RespectsFibres π.toFun C.base.Q) :
    ¬HasCommonFixedPoint
      (descendedMap π C.base.P hP) (descendedMap π C.base.Q hQ) := by
  rintro ⟨y, hyP, hyQ⟩
  change descendedMap π C.base.P hP y = y at hyP
  change descendedMap π C.base.Q hQ y = y at hyQ
  obtain ⟨x, hx⟩ := π.surjective_toFun y
  by_cases hcollapsed : x ∈ π.collapsedSet
  · rcases Set.mem_iUnion.mp hcollapsed with ⟨i, hxi⟩
    let J : ClosedSubinterval := π.collapsed i
    have hleft : J.left ∈ J.carrier :=
      Set.left_mem_Icc.mpr J.left_le_right
    have hπleft : π J.left = y := by
      calc
        π J.left = π x := (π.fibre_iff J.left x).mpr
          (Or.inr ⟨i, hleft, hxi⟩)
        _ = y := hx
    have hpointImage (z : I) (hz : z ∈ J.carrier) : π z = y := by
      calc
        π z = π J.left := (π.fibre_iff z J.left).mpr
          (Or.inr ⟨i, hz, hleft⟩)
        _ = y := hπleft
    have hPinvariant : IsForwardInvariant C.base.P J := by
      intro z hz
      have hπPz : π (C.base.P z) = π J.left := by
        calc
          π (C.base.P z) =
              descendedMap π C.base.P hP (π z) :=
            intertwines_descendedMap π C.base.P hP z
          _ = descendedMap π C.base.P hP y :=
            congrArg _ (hpointImage z hz)
          _ = y := hyP
          _ = π J.left := hπleft.symm
      have hmem : C.base.P z ∈ π.fibre J.left := hπPz
      rw [π.fibre_eq_collapsed i] at hmem
      exact hmem
    have hQinvariant : IsForwardInvariant C.base.Q J := by
      intro z hz
      have hπQz : π (C.base.Q z) = π J.left := by
        calc
          π (C.base.Q z) =
              descendedMap π C.base.Q hQ (π z) :=
            intertwines_descendedMap π C.base.Q hQ z
          _ = descendedMap π C.base.Q hQ y :=
            congrArg _ (hpointImage z hz)
          _ = y := hyQ
          _ = π J.left := hπleft.symm
      have hmem : C.base.Q z ∈ π.fibre J.left := hπQz
      rw [π.fibre_eq_collapsed i] at hmem
      exact hmem
    have hJuniv : J.carrier = Set.univ :=
      C.core_minimal J ⟨hPinvariant, hQinvariant⟩
    obtain ⟨u, v, huv⟩ := π.nonconstant_toFun
    apply huv
    have hu : u ∈ J.carrier := by
      rw [hJuniv]
      exact Set.mem_univ u
    have hv : v ∈ J.carrier := by
      rw [hJuniv]
      exact Set.mem_univ v
    exact (hpointImage u hu).trans (hpointImage v hv).symm
  · have hPxmem : C.base.P x ∈ π.fibre x := by
      change π (C.base.P x) = π x
      calc
        π (C.base.P x) = descendedMap π C.base.P hP (π x) :=
          intertwines_descendedMap π C.base.P hP x
        _ = descendedMap π C.base.P hP y := congrArg _ hx
        _ = y := hyP
        _ = π x := hx.symm
    have hQxmem : C.base.Q x ∈ π.fibre x := by
      change π (C.base.Q x) = π x
      calc
        π (C.base.Q x) = descendedMap π C.base.Q hQ (π x) :=
          intertwines_descendedMap π C.base.Q hQ x
        _ = descendedMap π C.base.Q hQ y := congrArg _ hx
        _ = y := hyQ
        _ = π x := hx.symm
    rw [π.fibre_eq_singleton_of_isUncollapsed hcollapsed,
      Set.mem_singleton_iff] at hPxmem hQxmem
    exact C.base.noCommonFixed ⟨x, hPxmem, hQxmem⟩

/-- Boundary 1: composition, fixed-component finiteness, and every safe
canonical finite quotient used by normalization and later phase collapses. -/
theorem piecewiseLinear_finitenessPackage :
    PiecewiseLinearFinitenessPackage := by
  exact
    { comp := fun hT hU => finitePiecePL_comp hT hU
      iterate := fun hT n => finitePiecePL_iterate hT n
      fixedPoints_finiteUnion := fun hT =>
        finitePiecePL_fixedPoints_finiteUnion hT
      noFlat_finiteLaps := fun hT hflat =>
        finitePiecePL_noFlat_finiteStrictLaps hT hflat
      quotient_descended_PL := fun π T hT hrespect =>
        finitePiecePL_descendedMap π T hT hrespect
      quotient_descended_commute := fun π P Q hP hQ hcomm =>
        commute_descendedMap π P Q hP hQ hcomm
      quotient_fixedPoints_exact := fun π T hrespect hcollapse =>
        fixedPoints_descendedMap_exact π T hrespect hcollapse
      quotient_fixedCount_drops := fun π T Tbar hexact hidentifies hfinite =>
        fixedPointCardinalityDrops_of_exact_image
          π T Tbar hexact hidentifies hfinite
      quotient_preserves_noCommon_on_minimalCore := fun C π hP hQ =>
        noCommonFixedPoint_descendedMap_of_minimalCore C π hP hQ }

/-! ### Minimal-core and fixed-component descent infrastructure -/

/-- Every finite-piece PL presentation is also a finite-piece weakly
monotone presentation. -/
private theorem finitePieceMonotone_of_finitePiecePL_plCore
    {T : IntervalMap} (hT : FinitePiecePL T) :
    FinitePieceMonotone T := by
  rcases hT with ⟨hcont, p, hp⟩
  apply FinitePieceMonotone.of_partition hcont p
  intro a b hab
  exact affineOn_weaklyMonotoneOn_plCore (hp hab)

/-- The affine embedding of the unit interval into a nondegenerate core is
itself a one-piece PL map. -/
private theorem coreEmbeddingMap_finitePiecePL_plCore
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) :
    FinitePiecePL (coreEmbeddingMap J hJ) := by
  refine ⟨coreEmbeddingMap_continuous J hJ, RealPartition.trivial, ?_⟩
  intro a b _hab
  refine ⟨((J.right : ℝ) - (J.left : ℝ)), (J.left : ℝ), ?_⟩
  intro x _hx
  simp [coreEmbeddingMap, coreAffineHomeomorph,
    coreCarrierRealHomeomorph, iccHomeoI_symm_apply_coe]

/-- Restriction to a nondegenerate invariant core and affine rescaling
preserve the finite-piece PL class. -/
private theorem finitePiecePL_rescaledCoreMap_plCore
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hmap : MapsTo T J.carrier J.carrier) :
    FinitePiecePL (rescaledCoreMap J hJ T hmap) := by
  let E : IntervalMap := coreEmbeddingMap J hJ
  have hE : FinitePiecePL E := coreEmbeddingMap_finitePiecePL_plCore J hJ
  have hpre : FinitePiecePL (T ∘ E) := finitePiecePL_comp hT hE
  rcases hpre with ⟨_hprecont, p, hp⟩
  refine ⟨rescaledCoreMap_continuous J hJ hT.1 hmap, p, ?_⟩
  intro a b hab
  obtain ⟨m, c, hformula⟩ := hp hab
  let d : ℝ := (J.right : ℝ) - (J.left : ℝ)
  have hd : d ≠ 0 := sub_ne_zero.mpr (ne_of_gt hJ)
  refine ⟨m / d, (c - (J.left : ℝ)) / d, ?_⟩
  intro x hx
  have hTx : T (E x) ∈ J.carrier :=
    hmap ((coreAffineHomeomorph J hJ).symm x).2
  have hcoord := clippedAffineCoordinate_of_mem
    J.left J.right hJ (T (E x)) hTx
  have hrescale :
      (rescaledCoreMap J hJ T hmap x : ℝ) =
        (clippedAffineCoordinate J.left J.right hJ (T (E x)) : ℝ) := by
    change ((coreAffineHomeomorph J hJ
        ⟨T ((coreAffineHomeomorph J hJ).symm x).1,
          hmap ((coreAffineHomeomorph J hJ).symm x).2⟩ : I) : ℝ) = _
    simp only [coreAffineHomeomorph, Homeomorph.trans_apply,
      iccHomeoI_apply_coe]
    exact hcoord.symm
  have hformula' : (T (E x) : ℝ) = m * (x : ℝ) + c := by
    simpa [Function.comp_apply] using hformula x hx
  rw [hrescale, hcoord, hformula']
  dsimp [d]
  field_simp
  ring

/-- For a continuous fibre-respecting map, every fixed point downstairs
lifts to a fixed point in its interval fibre. -/
private theorem fixedPoints_descendedMap_exact_continuous_plCore
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hT : Continuous T) (hrespect : RespectsFibres π.toFun T) :
    FixedPointsDescendExactly π.toFun T (descendedMap π T hrespect) := by
  ext y
  constructor
  · intro hy
    change descendedMap π T hrespect y = y at hy
    obtain ⟨x, hx⟩ := π.surjective_toFun y
    have hπTx : π (T x) = y := by
      rw [intertwines_descendedMap π T hrespect x, hx, hy]
    by_cases hcollapsed : x ∈ π.collapsedSet
    · rcases Set.mem_iUnion.mp hcollapsed with ⟨i, hxi⟩
      let J := π.collapsed i
      have hπleft : π J.left = y := by
        rw [← hx]
        exact (π.fibre_iff J.left x).mpr
          (Or.inr ⟨i, Set.left_mem_Icc.mpr J.left_le_right, hxi⟩)
      have hmaps : MapsTo T J.carrier J.carrier := by
        intro z hz
        have hπz : π z = y := by
          rw [← hπleft]
          exact (π.fibre_iff z J.left).mpr
            (Or.inr ⟨i, hz, Set.left_mem_Icc.mpr J.left_le_right⟩)
        have hπTz : π (T z) = y := by
          rw [intertwines_descendedMap π T hrespect z, hπz, hy]
        have hmem : T z ∈ π.fibre J.left := by
          change π (T z) = π J.left
          exact hπTz.trans hπleft.symm
        simpa [J, π.fibre_eq_collapsed i] using hmem
      obtain ⟨z, hz, hzfix⟩ :=
        exists_mem_Icc_isFixedPt_of_mapsTo
          hT.continuousOn J.left_le_right hmaps
      refine ⟨z, hzfix, ?_⟩
      rw [← hπleft]
      exact (π.fibre_iff z J.left).mpr
        (Or.inr ⟨i, hz, Set.left_mem_Icc.mpr J.left_le_right⟩)
    · have hsingle := π.fibre_eq_singleton_of_isUncollapsed hcollapsed
      have hTxmem : T x ∈ π.fibre x := hπTx.trans hx.symm
      rw [hsingle, Set.mem_singleton_iff] at hTxmem
      exact ⟨x, hTxmem, hx⟩
  · rintro ⟨x, hxfix, rfl⟩
    change descendedMap π T hrespect (π x) = π x
    rw [← intertwines_descendedMap π T hrespect x, hxfix]

private theorem intertwines_iterateMap_plCore
    {π T Tbar : IntervalMap} (h : Intertwines π T Tbar) (n : ℕ) :
    Intertwines π (iterateMap T n) (iterateMap Tbar n) := by
  intro x
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      calc
        π (iterateMap T n.succ x) = π (T (iterateMap T n x)) := by
          simp only [iterateMap, Function.iterate_succ_apply']
        _ = Tbar (π (iterateMap T n x)) := h (iterateMap T n x)
        _ = Tbar (iterateMap Tbar n (π x)) := congrArg Tbar (ih x)
        _ = iterateMap Tbar n.succ (π x) := by
          simp only [iterateMap, Function.iterate_succ_apply']

private theorem intertwines_positiveWordMap_plCore
    {π P Q Pbar Qbar : IntervalMap}
    (hP : Intertwines π P Pbar) (hQ : Intertwines π Q Qbar)
    (r s : ℕ) :
    Intertwines π (positiveWordMap P Q r s)
      (positiveWordMap Pbar Qbar r s) := by
  have hPr := intertwines_iterateMap_plCore hP r
  have hQs := intertwines_iterateMap_plCore hQ s
  intro x
  calc
    π (positiveWordMap P Q r s x) =
        iterateMap Pbar r (π (iterateMap Q s x)) :=
      hPr (iterateMap Q s x)
    _ = iterateMap Pbar r (iterateMap Qbar s (π x)) :=
      congrArg (iterateMap Pbar r) (hQs x)
    _ = positiveWordMap Pbar Qbar r s (π x) := rfl

private theorem respectsFibres_of_intertwines_plCore
    {π T Tbar : IntervalMap} (h : Intertwines π T Tbar) :
    RespectsFibres π T := by
  intro x y hxy
  rw [h x, h y, hxy]

/-- Re-minimalization after a quotient records the affine embedding back
into the quotient system, so fixed-set finiteness can be transported. -/
private theorem exists_minimalPiecewiseLinearCounterexample_with_embedding_plCore
    (C : PiecewiseLinearCounterexample) :
    ∃ (D : MinimalPiecewiseLinearCounterexample) (e : IntervalMap),
      Function.Injective e ∧
      Intertwines e D.base.P C.P ∧ Intertwines e D.base.Q C.Q := by
  let Cpm : PiecewiseMonotoneCounterexample :=
    { P := C.P
      Q := C.Q
      finitePiece_P :=
        finitePieceMonotone_of_finitePiecePL_plCore C.finitePieceP
      finitePiece_Q :=
        finitePieceMonotone_of_finitePiecePL_plCore C.finitePieceQ
      commute := C.commute
      no_common_fixed_point := C.noCommonFixed }
  obtain ⟨J, hJ, hminimal⟩ := Cpm.exists_nondegenerate_minimalCore
  let e : IntervalMap := coreEmbeddingMap J hJ
  let P' : IntervalMap := rescaledCoreMap J hJ C.P hminimal.1.1
  let Q' : IntervalMap := rescaledCoreMap J hJ C.Q hminimal.1.2
  obtain ⟨hPontoCore, hQontoCore⟩ :=
    minimalCommonInvariantCore_mapsOnto
      C.finitePieceP.1 C.finitePieceQ.1 C.commute J hminimal
  let C' : PiecewiseLinearCounterexample :=
    { P := P'
      Q := Q'
      finitePieceP := finitePiecePL_rescaledCoreMap_plCore
        J hJ C.finitePieceP hminimal.1.1
      finitePieceQ := finitePiecePL_rescaledCoreMap_plCore
        J hJ C.finitePieceQ hminimal.1.2
      commute := rescaledCoreMap_commute J hJ
        hminimal.1.1 hminimal.1.2 C.commute
      noCommonFixed := noCommonFixedPoint_rescaledCoreMaps
        J hJ hminimal.1.1 hminimal.1.2 C.noCommonFixed }
  let D : MinimalPiecewiseLinearCounterexample :=
    { base := C'
      ontoP := rescaledCoreMap_surjective_of_surjOn
        J hJ hminimal.1.1 hPontoCore
      ontoQ := rescaledCoreMap_surjective_of_surjOn
        J hJ hminimal.1.2 hQontoCore
      core_minimal := rescaledCoreMaps_coreMinimal J hJ hminimal }
  have heinj : Function.Injective e := by
    intro x y hxy
    have hsub : (coreAffineHomeomorph J hJ).symm x =
        (coreAffineHomeomorph J hJ).symm y := by
      apply Subtype.ext
      simpa [e, coreEmbeddingMap] using hxy
    exact (coreAffineHomeomorph J hJ).symm.injective hsub
  have hPintertwines : Intertwines e D.base.P C.P := by
    intro x
    simp [e, D, C', P', coreEmbeddingMap, rescaledCoreMap]
  have hQintertwines : Intertwines e D.base.Q C.Q := by
    intro x
    simp [e, D, C', Q', coreEmbeddingMap, rescaledCoreMap]
  exact ⟨D, e, heinj, hPintertwines, hQintertwines⟩

/-- Collapse the nondegenerate fixed components of one positive word,
then return to a minimal affine core.  The chosen word becomes finite and
all previously finite positive-word fixed counts do not increase. -/
private theorem exists_positiveWordFixedSetFiniteDescent_plCore
    (_package : PiecewiseLinearFinitenessPackage)
    (C : MinimalPiecewiseLinearCounterexample)
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∃ D : MinimalPiecewiseLinearCounterexample,
      (fixedPoints (positiveWordMap D.base.P D.base.Q r s)).Finite ∧
      ∀ a b : ℕ,
        (fixedPoints (positiveWordMap C.base.P C.base.Q a b)).Finite →
          (fixedPoints (positiveWordMap D.base.P D.base.Q a b)).Finite ∧
          (fixedPoints (positiveWordMap D.base.P D.base.Q a b)).ncard ≤
            (fixedPoints (positiveWordMap C.base.P C.base.Q a b)).ncard := by
  classical
  let T : IntervalMap := positiveWordMap C.base.P C.base.Q r s
  have hTPL : FinitePiecePL T := by
    simpa [T, positiveWordMap, Function.comp_def] using
      _package.comp
        (_package.iterate C.base.finitePieceP r)
        (_package.iterate C.base.finitePieceQ s)
  have hTfinite : IsFiniteUnionClosedSubintervals (fixedPoints T) :=
    _package.fixedPoints_finiteUnion hTPL
  have hTproper : fixedPoints T ≠ Set.univ := by
    intro hTall
    have hmapP : MapsTo C.base.P wholeIntervalPM.carrier wholeIntervalPM.carrier := by
      intro x _hx
      rw [wholeIntervalPM_carrier]
      exact Set.mem_univ _
    have hmapQ : MapsTo C.base.Q wholeIntervalPM.carrier wholeIntervalPM.carrier := by
      intro x _hx
      rw [wholeIntervalPM_carrier]
      exact Set.mem_univ _
    have hword : IsFixedInterval T wholeIntervalPM := by
      intro x _hx
      rw [hTall]
      exact Set.mem_univ _
    obtain ⟨x, _hx, hcommon⟩ :=
      PLQuotientSupport.commonFixedPoint_on_positiveWord_fixedInterval
        C.base.P C.base.Q r s C.base.finitePieceP.1 C.base.finitePieceQ.1
        C.base.commute hr hs wholeIntervalPM hmapP hmapQ hword
    exact C.base.noCommonFixed ⟨x, hcommon⟩
  obtain ⟨π, hcomponents⟩ :=
    PLQuotientSupport.exists_canonicalFixedComponentQuotient
      T hTPL.1 hTfinite hTproper
  obtain ⟨hrespectP, hrespectQ⟩ :=
    PLQuotientSupport.positiveWord_fixedComponents_respect
      π C.base.P C.base.Q r s C.base.finitePieceP.1
      C.base.finitePieceQ.1 C.base.commute hr hs hcomponents
  let Pbar : IntervalMap := descendedMap π C.base.P hrespectP
  let Qbar : IntervalMap := descendedMap π C.base.Q hrespectQ
  let Cbar : PiecewiseLinearCounterexample :=
    { P := Pbar
      Q := Qbar
      finitePieceP := _package.quotient_descended_PL
        π C.base.P C.base.finitePieceP hrespectP
      finitePieceQ := _package.quotient_descended_PL
        π C.base.Q C.base.finitePieceQ hrespectQ
      commute := _package.quotient_descended_commute
        π C.base.P C.base.Q hrespectP hrespectQ C.base.commute
      noCommonFixed := _package.quotient_preserves_noCommon_on_minimalCore
        C π hrespectP hrespectQ }
  obtain ⟨D, e, heinj, heP, heQ⟩ :=
    exists_minimalPiecewiseLinearCounterexample_with_embedding_plCore Cbar
  have hdescP : Intertwines π.toFun C.base.P Pbar :=
    intertwines_descendedMap π C.base.P hrespectP
  have hdescQ : Intertwines π.toFun C.base.Q Qbar :=
    intertwines_descendedMap π C.base.Q hrespectQ
  have hbarFixed (a b : ℕ) :
      fixedPoints (positiveWordMap Pbar Qbar a b) =
        π.toFun '' fixedPoints (positiveWordMap C.base.P C.base.Q a b) := by
    have hdescWord :=
      intertwines_positiveWordMap_plCore hdescP hdescQ a b
    let hrespectWord : RespectsFibres π.toFun
        (positiveWordMap C.base.P C.base.Q a b) :=
      respectsFibres_of_intertwines_plCore hdescWord
    have hunique : positiveWordMap Pbar Qbar a b =
        descendedMap π (positiveWordMap C.base.P C.base.Q a b) hrespectWord :=
      descendedMap_unique π.surjective_toFun hdescWord
        (intertwines_descendedMap π
          (positiveWordMap C.base.P C.base.Q a b) hrespectWord)
    rw [hunique]
    exact fixedPoints_descendedMap_exact_continuous_plCore π
      (positiveWordMap C.base.P C.base.Q a b)
      ((C.base.finitePieceP.1.iterate a).comp
        (C.base.finitePieceQ.1.iterate b)) hrespectWord
  have hfinite_of_bar_finite (a b : ℕ)
      (hfinite : (fixedPoints (positiveWordMap Pbar Qbar a b)).Finite) :
      (fixedPoints (positiveWordMap D.base.P D.base.Q a b)).Finite ∧
      (fixedPoints (positiveWordMap D.base.P D.base.Q a b)).ncard ≤
        (fixedPoints (positiveWordMap Pbar Qbar a b)).ncard := by
    have heWord := intertwines_positiveWordMap_plCore heP heQ a b
    have himage : e '' fixedPoints (positiveWordMap D.base.P D.base.Q a b) ⊆
        fixedPoints (positiveWordMap Pbar Qbar a b) := by
      rintro _ ⟨x, hx, rfl⟩
      change positiveWordMap Pbar Qbar a b (e x) = e x
      rw [← heWord x, hx]
    have hDfinite := (hfinite.subset himage).of_finite_image heinj.injOn
    refine ⟨hDfinite, ?_⟩
    exact Set.ncard_le_ncard_of_injOn e
      (fun x hx => himage ⟨x, hx, rfl⟩) heinj.injOn hfinite
  refine ⟨D, ?_, ?_⟩
  · apply (hfinite_of_bar_finite r s ?_).1
    rw [hbarFixed r s]
    exact PLQuotientSupport.fixedPoints_image_finite_of_collapsesExactlyFixedComponents
      π T hTPL.1 hTfinite hcomponents
  · intro a b hfinite
    have hbarfinite :
        (fixedPoints (positiveWordMap Pbar Qbar a b)).Finite := by
      rw [hbarFixed a b]
      exact hfinite.image π.toFun
    obtain ⟨hDfinite, hDbar⟩ := hfinite_of_bar_finite a b hbarfinite
    refine ⟨hDfinite, hDbar.trans ?_⟩
    rw [hbarFixed a b]
    exact Set.ncard_image_le hfinite

private theorem piecewiseLinearW_eq_positiveWord_plCore
    (C : MinimalPiecewiseLinearCounterexample) :
    piecewiseLinearW C.base.P C.base.Q =
      positiveWordMap C.base.P C.base.Q 2 2 := by
  simpa [piecewiseLinearW, positiveWordMap, iterateMap] using
    C.base.commute.comp_iterate 2

private theorem piecewiseLinearR_eq_positiveWord_plCore
    (P Q : IntervalMap) (K : Finset I) :
    piecewiseLinearR P Q K =
      positiveWordMap P Q
        (piecewiseLinearNormalizationExponent K)
        (piecewiseLinearNormalizationExponent K) := by
  rfl

private theorem piecewiseLinearS_eq_positiveWord_plCore
    (C : MinimalPiecewiseLinearCounterexample) (K : Finset I) :
    piecewiseLinearS C.base.P C.base.Q K =
      positiveWordMap C.base.P C.base.Q
        (piecewiseLinearNormalizationExponent K * 2)
        (piecewiseLinearNormalizationExponent K * 2) := by
  let L := piecewiseLinearNormalizationExponent K
  unfold piecewiseLinearS piecewiseLinearR piecewiseLinearA piecewiseLinearB
    iterateMap positiveWordMap
  change ((C.base.P^[L]) ∘ (C.base.Q^[L]))^[2] =
    (C.base.P^[L * 2]) ∘ (C.base.Q^[L * 2])
  calc
    ((C.base.P^[L]) ∘ (C.base.Q^[L]))^[2] =
        (C.base.P^[L])^[2] ∘ (C.base.Q^[L])^[2] :=
      (C.base.commute.iterate_iterate L L).comp_iterate 2
    _ = (C.base.P^[L * 2]) ∘ (C.base.Q^[L * 2]) := by
      rw [Function.iterate_mul, Function.iterate_mul]

/-- The first normalization stage: only `Fix(W)` has been made finite. -/
structure WNormalizedPiecewiseLinearCounterexample where
  base : MinimalPiecewiseLinearCounterexample
  fixedW : Finset I
  fixedW_spec : ∀ x : I,
    x ∈ fixedW ↔ IsFixedPoint (piecewiseLinearW base.base.P base.base.Q) x

/-- The second normalization stage: `Fix(W)` and `Fix(R)` are finite. -/
structure WRNormalizedPiecewiseLinearCounterexample where
  base : WNormalizedPiecewiseLinearCounterexample
  fixedR : Finset I
  fixedR_spec : ∀ x : I,
    x ∈ fixedR ↔ IsFixedPoint
      (piecewiseLinearR base.base.base.P base.base.base.Q base.fixedW) x

/-- The third normalization stage: all three fixed sets are finite. -/
structure WRSNormalizedPiecewiseLinearCounterexample where
  base : WRNormalizedPiecewiseLinearCounterexample
  fixedS : Finset I
  fixedS_spec : ∀ x : I,
    x ∈ fixedS ↔ IsFixedPoint
      (piecewiseLinearS
        base.base.base.base.P base.base.base.base.Q base.base.fixedW) x

namespace WRSNormalizedPiecewiseLinearCounterexample

/-- Forget the staging annotations after all three fixed sets are finite. -/
def toNormalized (C : WRSNormalizedPiecewiseLinearCounterexample) :
    NormalizedPiecewiseLinearCounterexample :=
  { base := C.base.base.base
    fixedW := C.base.base.fixedW
    fixedW_spec := C.base.base.fixedW_spec
    fixedR := C.base.fixedR
    fixedR_spec := C.base.fixedR_spec
    fixedS := C.fixedS
    fixedS_spec := C.fixedS_spec }

end WRSNormalizedPiecewiseLinearCounterexample

/-- If the finite `W` count is globally minimal, normalizing `R` cannot
change that count, so the exponent used before and after the quotient agrees. -/
private theorem exists_WRNormalized_of_minimalW_plCore
    (_package : PiecewiseLinearFinitenessPackage)
    (CW : WNormalizedPiecewiseLinearCounterexample)
    (hCWminimal : ∀ D : WNormalizedPiecewiseLinearCounterexample,
      CW.fixedW.card ≤ D.fixedW.card) :
    ∃ CWR : WRNormalizedPiecewiseLinearCounterexample,
      CWR.base.fixedW.card = CW.fixedW.card := by
  classical
  let L : ℕ := piecewiseLinearNormalizationExponent CW.fixedW
  have hLpos : 0 < L := piecewiseLinearNormalizationExponent_pos CW.fixedW
  obtain ⟨D, hDRword, hpreserve⟩ :=
    exists_positiveWordFixedSetFiniteDescent_plCore
      _package CW.base L L hLpos hLpos
  have hCWset :
      fixedPoints (piecewiseLinearW CW.base.base.P CW.base.base.Q) =
        (CW.fixedW : Set I) := by
    ext x
    exact (CW.fixedW_spec x).symm
  have hCWfinite :
      (fixedPoints (piecewiseLinearW CW.base.base.P CW.base.base.Q)).Finite := by
    rw [hCWset]
    exact CW.fixedW.finite_toSet
  have hCWword :
      (fixedPoints
        (positiveWordMap CW.base.base.P CW.base.base.Q 2 2)).Finite := by
    rw [← piecewiseLinearW_eq_positiveWord_plCore CW.base]
    exact hCWfinite
  obtain ⟨hDWword, hDWle⟩ := hpreserve 2 2 hCWword
  have hDW :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).Finite := by
    rw [piecewiseLinearW_eq_positiveWord_plCore D]
    exact hDWword
  let fixedW : Finset I := hDW.toFinset
  have hfixedWcard : fixedW.card =
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard :=
    (Set.ncard_eq_toFinset_card _ hDW).symm
  let DW : WNormalizedPiecewiseLinearCounterexample :=
    { base := D
      fixedW := fixedW
      fixedW_spec := fun x => hDW.mem_toFinset }
  have hDWle' :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard ≤
        (fixedPoints
          (piecewiseLinearW CW.base.base.P CW.base.base.Q)).ncard := by
    rw [piecewiseLinearW_eq_positiveWord_plCore D,
      piecewiseLinearW_eq_positiveWord_plCore CW.base]
    exact hDWle
  have hfixedW_le : fixedW.card ≤ CW.fixedW.card := by
    calc
      fixedW.card =
          (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard :=
        hfixedWcard
      _ ≤ (fixedPoints
          (piecewiseLinearW CW.base.base.P CW.base.base.Q)).ncard := hDWle'
      _ = CW.fixedW.card := by rw [hCWset]; simp
  have hfixedW_eq : fixedW.card = CW.fixedW.card :=
    le_antisymm hfixedW_le (hCWminimal DW)
  have hLfixedW : piecewiseLinearNormalizationExponent fixedW = L := by
    simp only [piecewiseLinearNormalizationExponent, L]
    rw [hfixedW_eq]
  have hDR :
      (fixedPoints
        (piecewiseLinearR D.base.P D.base.Q fixedW)).Finite := by
    rw [piecewiseLinearR_eq_positiveWord_plCore, hLfixedW]
    exact hDRword
  let fixedR : Finset I := hDR.toFinset
  refine ⟨{
    base := DW
    fixedR := fixedR
    fixedR_spec := fun x => hDR.mem_toFinset }, hfixedW_eq⟩

/-- Restrict a PL counterexample to a minimal common invariant interval and
affinely rescale it back to `I`. -/
theorem exists_minimalPiecewiseLinearCounterexample
    (_package : PiecewiseLinearFinitenessPackage)
    (_C : PiecewiseLinearCounterexample) :
    Nonempty MinimalPiecewiseLinearCounterexample := by
  let Cpm : PiecewiseMonotoneCounterexample :=
    { P := _C.P
      Q := _C.Q
      finitePiece_P :=
        finitePieceMonotone_of_finitePiecePL_plCore _C.finitePieceP
      finitePiece_Q :=
        finitePieceMonotone_of_finitePiecePL_plCore _C.finitePieceQ
      commute := _C.commute
      no_common_fixed_point := _C.noCommonFixed }
  obtain ⟨J, hJ, hminimal⟩ := Cpm.exists_nondegenerate_minimalCore
  let P' : IntervalMap := rescaledCoreMap J hJ _C.P hminimal.1.1
  let Q' : IntervalMap := rescaledCoreMap J hJ _C.Q hminimal.1.2
  obtain ⟨hPontoCore, hQontoCore⟩ :=
    minimalCommonInvariantCore_mapsOnto
      _C.finitePieceP.1 _C.finitePieceQ.1 _C.commute J hminimal
  let C' : PiecewiseLinearCounterexample :=
    { P := P'
      Q := Q'
      finitePieceP := finitePiecePL_rescaledCoreMap_plCore
        J hJ _C.finitePieceP hminimal.1.1
      finitePieceQ := finitePiecePL_rescaledCoreMap_plCore
        J hJ _C.finitePieceQ hminimal.1.2
      commute := rescaledCoreMap_commute J hJ
        hminimal.1.1 hminimal.1.2 _C.commute
      noCommonFixed := noCommonFixedPoint_rescaledCoreMaps
        J hJ hminimal.1.1 hminimal.1.2 _C.noCommonFixed }
  exact ⟨{
    base := C'
    ontoP := rescaledCoreMap_surjective_of_surjOn
      J hJ hminimal.1.1 hPontoCore
    ontoQ := rescaledCoreMap_surjective_of_surjOn
      J hJ hminimal.1.2 hQontoCore
    core_minimal := rescaledCoreMaps_coreMinimal J hJ hminimal }⟩

/-- Collapse all nondegenerate components of `Fix(W)` and restart on a
minimal core, producing a finite exact fixed finset for `W`. -/
theorem exists_WNormalizedPiecewiseLinearCounterexample
    (_package : PiecewiseLinearFinitenessPackage)
    (_C : MinimalPiecewiseLinearCounterexample) :
    Nonempty WNormalizedPiecewiseLinearCounterexample := by
  classical
  obtain ⟨D, hDword, _hpreserve⟩ :=
    exists_positiveWordFixedSetFiniteDescent_plCore
      _package _C 2 2 (by norm_num) (by norm_num)
  have hDW :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).Finite := by
    rw [piecewiseLinearW_eq_positiveWord_plCore D]
    exact hDword
  let fixedW : Finset I := hDW.toFinset
  refine ⟨{
    base := D
    fixedW := fixedW
    fixedW_spec := ?_ }⟩
  intro x
  exact hDW.mem_toFinset

/-- Collapse the remaining nondegenerate components of `Fix(R)` without
increasing the already normalized `W` count. -/
theorem exists_WRNormalizedPiecewiseLinearCounterexample
    (_package : PiecewiseLinearFinitenessPackage)
    (_C : WNormalizedPiecewiseLinearCounterexample) :
    Nonempty WRNormalizedPiecewiseLinearCounterexample := by
  classical
  let firstCounts : Set ℕ :=
    {n | ∃ C : WNormalizedPiecewiseLinearCounterexample,
      C.fixedW.card = n}
  have hfirst_nonempty : firstCounts.Nonempty :=
    ⟨_C.fixedW.card, _C, rfl⟩
  let wmin : ℕ := sInf firstCounts
  have hwmin_mem : wmin ∈ firstCounts := Nat.sInf_mem hfirst_nonempty
  rcases hwmin_mem with ⟨CW, hCWcard⟩
  have hCWminimal (D : WNormalizedPiecewiseLinearCounterexample) :
      CW.fixedW.card ≤ D.fixedW.card := by
    rw [hCWcard]
    exact Nat.sInf_le (show D.fixedW.card ∈ firstCounts from ⟨D, rfl⟩)
  obtain ⟨CWR, _hcard⟩ :=
    exists_WRNormalized_of_minimalW_plCore _package CW hCWminimal
  exact ⟨CWR⟩

/-- Collapse the remaining nondegenerate components of `Fix(S)` without
increasing either earlier fixed count. -/
theorem exists_WRSNormalizedPiecewiseLinearCounterexample
    (_package : PiecewiseLinearFinitenessPackage)
    (_C : WRNormalizedPiecewiseLinearCounterexample) :
    Nonempty WRSNormalizedPiecewiseLinearCounterexample := by
  classical
  let firstCounts : Set ℕ :=
    {n | ∃ C : WNormalizedPiecewiseLinearCounterexample,
      C.fixedW.card = n}
  have hfirst_nonempty : firstCounts.Nonempty :=
    ⟨_C.base.fixedW.card, _C.base, rfl⟩
  let wmin : ℕ := sInf firstCounts
  have hwmin_mem : wmin ∈ firstCounts := Nat.sInf_mem hfirst_nonempty
  rcases hwmin_mem with ⟨CW, hCWcard⟩
  have hCWminimal (E : WNormalizedPiecewiseLinearCounterexample) :
      CW.fixedW.card ≤ E.fixedW.card := by
    rw [hCWcard]
    exact Nat.sInf_le (show E.fixedW.card ∈ firstCounts from ⟨E, rfl⟩)
  obtain ⟨CWR, hCWRcard⟩ :=
    exists_WRNormalized_of_minimalW_plCore _package CW hCWminimal
  let L : ℕ := piecewiseLinearNormalizationExponent CWR.base.fixedW
  have hLpos : 0 < L :=
    piecewiseLinearNormalizationExponent_pos CWR.base.fixedW
  have hLtwopos : 0 < L * 2 := Nat.mul_pos hLpos (by norm_num)
  obtain ⟨D, hDSword, hpreserve⟩ :=
    exists_positiveWordFixedSetFiniteDescent_plCore
      _package CWR.base.base (L * 2) (L * 2) hLtwopos hLtwopos
  have hCWR_W_set :
      fixedPoints
          (piecewiseLinearW CWR.base.base.base.P CWR.base.base.base.Q) =
        (CWR.base.fixedW : Set I) := by
    ext x
    exact (CWR.base.fixedW_spec x).symm
  have hCWR_W_finite :
      (fixedPoints
        (piecewiseLinearW CWR.base.base.base.P CWR.base.base.base.Q)).Finite := by
    rw [hCWR_W_set]
    exact CWR.base.fixedW.finite_toSet
  have hCWR_W_word :
      (fixedPoints
        (positiveWordMap CWR.base.base.base.P CWR.base.base.base.Q 2 2)).Finite := by
    rw [← piecewiseLinearW_eq_positiveWord_plCore CWR.base.base]
    exact hCWR_W_finite
  obtain ⟨hDWword, hDWle⟩ := hpreserve 2 2 hCWR_W_word
  have hDW :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).Finite := by
    rw [piecewiseLinearW_eq_positiveWord_plCore D]
    exact hDWword
  let fixedW : Finset I := hDW.toFinset
  have hfixedWcard : fixedW.card =
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard :=
    (Set.ncard_eq_toFinset_card _ hDW).symm
  let DW : WNormalizedPiecewiseLinearCounterexample :=
    { base := D
      fixedW := fixedW
      fixedW_spec := fun x => hDW.mem_toFinset }
  have hDWle' :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard ≤
        (fixedPoints
          (piecewiseLinearW CWR.base.base.base.P CWR.base.base.base.Q)).ncard := by
    rw [piecewiseLinearW_eq_positiveWord_plCore D,
      piecewiseLinearW_eq_positiveWord_plCore CWR.base.base]
    exact hDWle
  have hfixedW_le : fixedW.card ≤ CWR.base.fixedW.card := by
    calc
      fixedW.card =
          (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard :=
        hfixedWcard
      _ ≤ (fixedPoints
          (piecewiseLinearW CWR.base.base.base.P CWR.base.base.base.Q)).ncard :=
        hDWle'
      _ = CWR.base.fixedW.card := by rw [hCWR_W_set]; simp
  have hfixedW_ge : CWR.base.fixedW.card ≤ fixedW.card := by
    rw [hCWRcard]
    exact hCWminimal DW
  have hfixedW_eq : fixedW.card = CWR.base.fixedW.card :=
    le_antisymm hfixedW_le hfixedW_ge
  have hLfixedW : piecewiseLinearNormalizationExponent fixedW = L := by
    simp only [piecewiseLinearNormalizationExponent, L]
    rw [hfixedW_eq]
  have hCWR_R_set :
      fixedPoints
          (piecewiseLinearR CWR.base.base.base.P CWR.base.base.base.Q
            CWR.base.fixedW) =
        (CWR.fixedR : Set I) := by
    ext x
    exact (CWR.fixedR_spec x).symm
  have hCWR_R_finite :
      (fixedPoints
        (piecewiseLinearR CWR.base.base.base.P CWR.base.base.base.Q
          CWR.base.fixedW)).Finite := by
    rw [hCWR_R_set]
    exact CWR.fixedR.finite_toSet
  have hCWR_R_word :
      (fixedPoints
        (positiveWordMap CWR.base.base.base.P CWR.base.base.base.Q L L)).Finite := by
    rw [piecewiseLinearR_eq_positiveWord_plCore] at hCWR_R_finite
    simpa [L] using hCWR_R_finite
  obtain ⟨hDRword, _hDRle⟩ := hpreserve L L hCWR_R_word
  have hDR :
      (fixedPoints
        (piecewiseLinearR D.base.P D.base.Q fixedW)).Finite := by
    rw [piecewiseLinearR_eq_positiveWord_plCore, hLfixedW]
    exact hDRword
  let fixedR : Finset I := hDR.toFinset
  let DWR : WRNormalizedPiecewiseLinearCounterexample :=
    { base := DW
      fixedR := fixedR
      fixedR_spec := fun x => hDR.mem_toFinset }
  have hDS :
      (fixedPoints
        (piecewiseLinearS D.base.P D.base.Q fixedW)).Finite := by
    rw [piecewiseLinearS_eq_positiveWord_plCore D, hLfixedW]
    exact hDSword
  let fixedS : Finset I := hDS.toFinset
  refine ⟨{
    base := DWR
    fixedS := fixedS
    fixedS_spec := ?_ }⟩
  intro x
  exact hDS.mem_toFinset

/-- A nonempty family of normalized counterexamples contains one with a
lexicographically least triple of natural-number fixed counts. -/
theorem exists_lexLeastNormalizedPiecewiseLinearCounterexample
    (_h : Nonempty NormalizedPiecewiseLinearCounterexample) :
    Nonempty LeastNormalizedPiecewiseLinearCounterexample := by
  classical
  obtain ⟨N₀⟩ := _h
  let firstCounts : Set ℕ :=
    {a | ∃ N : NormalizedPiecewiseLinearCounterexample,
      N.fixedW.card = a}
  have hfirst_nonempty : firstCounts.Nonempty :=
    ⟨N₀.fixedW.card, N₀, rfl⟩
  let a : ℕ := sInf firstCounts
  have ha_mem : a ∈ firstCounts := Nat.sInf_mem hfirst_nonempty
  rcases ha_mem with ⟨Na, hNa⟩
  let secondCounts : Set ℕ :=
    {b | ∃ N : NormalizedPiecewiseLinearCounterexample,
      N.fixedW.card = a ∧ N.fixedR.card = b}
  have hsecond_nonempty : secondCounts.Nonempty :=
    ⟨Na.fixedR.card, Na, hNa, rfl⟩
  let b : ℕ := sInf secondCounts
  have hb_mem : b ∈ secondCounts := Nat.sInf_mem hsecond_nonempty
  rcases hb_mem with ⟨Nb, hNb_a, hNb_b⟩
  let thirdCounts : Set ℕ :=
    {c | ∃ N : NormalizedPiecewiseLinearCounterexample,
      N.fixedW.card = a ∧ N.fixedR.card = b ∧ N.fixedS.card = c}
  have hthird_nonempty : thirdCounts.Nonempty :=
    ⟨Nb.fixedS.card, Nb, hNb_a, hNb_b, rfl⟩
  let c : ℕ := sInf thirdCounts
  have hc_mem : c ∈ thirdCounts := Nat.sInf_mem hthird_nonempty
  rcases hc_mem with ⟨Nmin, hNmin_a, hNmin_b, hNmin_c⟩
  refine ⟨{
    base := Nmin
    lex_minimal := ?_ }⟩
  intro other
  unfold FixedCountLexLE
  rw [hNmin_a, hNmin_b, hNmin_c]
  have ha_le : a ≤ other.fixedW.card :=
    Nat.sInf_le
      (show other.fixedW.card ∈ firstCounts from ⟨other, rfl⟩)
  rcases lt_or_eq_of_le ha_le with ha_lt | ha_eq
  · exact Or.inl ha_lt
  · refine Or.inr ⟨ha_eq, ?_⟩
    have hb_le : b ≤ other.fixedR.card :=
      Nat.sInf_le
        (show other.fixedR.card ∈ secondCounts from
          ⟨other, ha_eq.symm, rfl⟩)
    rcases lt_or_eq_of_le hb_le with hb_lt | hb_eq
    · exact Or.inl hb_lt
    · refine Or.inr ⟨hb_eq, ?_⟩
      exact Nat.sInf_le
        (show other.fixedS.card ∈ thirdCounts from
          ⟨other, ha_eq.symm, hb_eq.symm, rfl⟩)

/-- Boundary 2: minimal-core restriction, removal of fixed intervals for
`W`, `R`, and `S`, and well-founded lexicographic descent. -/
theorem exists_leastNormalizedPiecewiseLinearCounterexample
    (_package : PiecewiseLinearFinitenessPackage)
    (_C : PiecewiseLinearCounterexample) :
    Nonempty LeastNormalizedPiecewiseLinearCounterexample := by
  obtain ⟨Cmin⟩ :=
    exists_minimalPiecewiseLinearCounterexample _package _C
  obtain ⟨CW⟩ :=
    exists_WNormalizedPiecewiseLinearCounterexample _package Cmin
  obtain ⟨CWR⟩ :=
    exists_WRNormalizedPiecewiseLinearCounterexample _package CW
  obtain ⟨CWRS⟩ :=
    exists_WRSNormalizedPiecewiseLinearCounterexample _package CWR
  exact exists_lexLeastNormalizedPiecewiseLinearCounterexample
    ⟨CWRS.toNormalized⟩

/-! ## Selected gap, returned germs, finite arrival, and LEO -/

/-- A simultaneous reflection may be used to orient a consecutive fixed gap
to the right.  The resulting least counterexample records how a common fixed
point would pull back to the source system. -/
structure PiecewiseLinearSelectedFixedGap
    (source : LeastNormalizedPiecewiseLinearCounterexample) where
  system : LeastNormalizedPiecewiseLinearCounterexample
  source_commonFixed_of_system :
    HasCommonFixedPoint system.P system.Q →
      HasCommonFixedPoint source.P source.Q
  p : I
  c : I
  p_lt_c : p < c
  fixed_p : IsFixedPoint system.W p
  fixed_c : IsFixedPoint system.W c
  consecutive : ∀ x ∈ Set.Ioo p c, ¬IsFixedPoint system.W x
  moves_right : ∀ x ∈ Set.Ioo p c, x < system.W x

namespace PiecewiseLinearSelectedFixedGap

variable {source : LeastNormalizedPiecewiseLinearCounterexample}

def P (G : PiecewiseLinearSelectedFixedGap source) : IntervalMap :=
  G.system.P

def Q (G : PiecewiseLinearSelectedFixedGap source) : IntervalMap :=
  G.system.Q

def W (G : PiecewiseLinearSelectedFixedGap source) : IntervalMap :=
  G.system.W

def L (G : PiecewiseLinearSelectedFixedGap source) : ℕ :=
  G.system.L

def A (G : PiecewiseLinearSelectedFixedGap source) : IntervalMap :=
  G.system.A

def B (G : PiecewiseLinearSelectedFixedGap source) : IntervalMap :=
  G.system.B

def R (G : PiecewiseLinearSelectedFixedGap source) : IntervalMap :=
  G.system.R

def S (G : PiecewiseLinearSelectedFixedGap source) : IntervalMap :=
  G.system.S

theorem noCommonFixed (G : PiecewiseLinearSelectedFixedGap source) :
    ¬HasCommonFixedPoint G.P G.Q :=
  G.system.noCommonFixed

end PiecewiseLinearSelectedFixedGap

/-- A consecutive fixed gap before choosing between its two orientations. -/
structure PiecewiseLinearUnorientedFixedGap
    (C : LeastNormalizedPiecewiseLinearCounterexample) where
  p : I
  c : I
  p_lt_c : p < c
  fixed_p : IsFixedPoint C.W p
  fixed_c : IsFixedPoint C.W c
  consecutive : ∀ x ∈ Set.Ioo p c, ¬IsFixedPoint C.W x
  constant_sign :
    (∀ x ∈ Set.Ioo p c, x < C.W x) ∨
      (∀ x ∈ Set.Ioo p c, C.W x < x)

/-- A finite nontrivial `Fix(W)` has a consecutive gap on which `W-id` has
one strict sign. -/
theorem exists_piecewiseLinearUnorientedFixedGap
    (C : LeastNormalizedPiecewiseLinearCounterexample) :
    Nonempty (PiecewiseLinearUnorientedFixedGap C) := by
  classical
  have hWcont : Continuous C.W :=
    IntervalMap.continuous_iterate
      (C.continuousP.comp C.continuousQ) 2
  have hP_PQ : Commute C.P (C.P ∘ C.Q) :=
    (Function.Commute.refl C.P).comp_right C.commute
  have hQ_PQ : Commute C.Q (C.P ∘ C.Q) :=
    C.commute.symm.comp_right (Function.Commute.refl C.Q)
  have hPW : Commute C.P C.W := hP_PQ.iterate_right 2
  have hQW : Commute C.Q C.W := hQ_PQ.iterate_right 2
  obtain ⟨r, hr⟩ := IntervalMap.exists_fixedPoint hWcont
  have hrmem : r ∈ C.base.fixedW := (C.base.fixedW_spec r).2 hr
  have htwo : ∃ x ∈ C.base.fixedW, ∃ y ∈ C.base.fixedW, x ≠ y := by
    by_cases hPr : C.P r = r
    · by_cases hQr : C.Q r = r
      · exact (C.noCommonFixed ⟨r, hPr, hQr⟩).elim
      · refine ⟨r, hrmem, C.Q r, ?_, ?_⟩
        · apply (C.base.fixedW_spec _).2
          change C.W (C.Q r) = C.Q r
          rw [← hQW r, hr]
        · exact fun h ↦ hQr h.symm
    · refine ⟨r, hrmem, C.P r, ?_, ?_⟩
      · apply (C.base.fixedW_spec _).2
        change C.W (C.P r) = C.P r
        rw [← hPW r, hr]
      · exact fun h ↦ hPr h.symm
  obtain ⟨x₁, hx₁, x₂, hx₂, hxne⟩ := htwo
  obtain ⟨p, hp, hpmin⟩ :=
    C.base.fixedW.exists_min_image id ⟨x₁, hx₁⟩
  have herase : (C.base.fixedW.erase p).Nonempty := by
    by_cases hxp : x₁ = p
    · refine ⟨x₂, Finset.mem_erase.mpr ⟨?_, hx₂⟩⟩
      intro h
      apply hxne
      exact hxp.trans h.symm
    · exact ⟨x₁, Finset.mem_erase.mpr ⟨hxp, hx₁⟩⟩
  obtain ⟨c, hcErase, hcmin⟩ :=
    (C.base.fixedW.erase p).exists_min_image id herase
  have hc : c ∈ C.base.fixedW := (Finset.mem_erase.mp hcErase).2
  have hpc_le : p ≤ c := by simpa using hpmin c hc
  have hpc_ne : p ≠ c := fun h ↦ (Finset.mem_erase.mp hcErase).1 h.symm
  have hpc : p < c := lt_of_le_of_ne hpc_le hpc_ne
  have hconsecutive : ∀ z ∈ Set.Ioo p c, ¬IsFixedPoint C.W z := by
    intro z hz hzfix
    have hzmem : z ∈ C.base.fixedW := (C.base.fixedW_spec z).2 hzfix
    have hzErase : z ∈ C.base.fixedW.erase p :=
      Finset.mem_erase.mpr ⟨ne_of_gt hz.1, hzmem⟩
    have hcz : c ≤ z := by simpa using hcmin z hzErase
    exact (not_lt_of_ge hcz) hz.2
  refine ⟨{
    p := p
    c := c
    p_lt_c := hpc
    fixed_p := (C.base.fixedW_spec p).1 hp
    fixed_c := (C.base.fixedW_spec c).1 hc
    consecutive := hconsecutive
    constant_sign := ?_ }⟩
  let d : I → ℝ := fun z ↦ (C.W z : ℝ) - (z : ℝ)
  have hdcont : Continuous d :=
    (continuous_subtype_val.comp hWcont).sub continuous_subtype_val
  have opposite_impossible (x y : I) (hx : x ∈ Set.Ioo p c)
      (hy : y ∈ Set.Ioo p c) (hneg : C.W x < x)
      (hpos : y < C.W y) : False := by
    have hdx : d x < 0 := sub_neg.mpr hneg
    have hdy : 0 < d y := sub_pos.mpr hpos
    have hzero : (0 : ℝ) ∈ Set.uIcc (d x) (d y) :=
      Set.mem_uIcc_of_le hdx.le hdy.le
    obtain ⟨z, hzxy, hdz⟩ :=
      intermediate_value_uIcc hdcont.continuousOn hzero
    have hz : z ∈ Set.Ioo p c := by
      rcases Set.mem_uIcc.mp hzxy with hxy | hyx
      · exact ⟨hx.1.trans_le hxy.1, hxy.2.trans_lt hy.2⟩
      · exact ⟨hy.1.trans_le hyx.1, hyx.2.trans_lt hx.2⟩
    apply hconsecutive z hz
    apply Subtype.ext
    exact sub_eq_zero.mp hdz
  obtain ⟨m, hpm, hmc⟩ := exists_between hpc
  have hmIoo : m ∈ Set.Ioo p c := ⟨hpm, hmc⟩
  have hmne : C.W m ≠ m := hconsecutive m hmIoo
  rcases lt_or_gt_of_ne hmne with hmneg | hmpos
  · right
    intro x hx
    have hxne : C.W x ≠ x := hconsecutive x hx
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · exact hxneg
    · exact (opposite_impossible m x hmIoo hx hmneg hxpos).elim
  · left
    intro x hx
    have hxne : C.W x ≠ x := hconsecutive x hx
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · exact (opposite_impossible x m hx hmIoo hxneg hmpos).elim
    · exact hxpos

/-! ### Reflection transport for the selected gap -/

private def centralReflection_plB3 : IntervalMap := unitInterval.symm

private def reflectedIntervalMap_plB3 (T : IntervalMap) : IntervalMap :=
  centralReflection_plB3 ∘ T ∘ centralReflection_plB3

@[simp] private theorem reflectedIntervalMap_plB3_apply
    (T : IntervalMap) (x : I) :
    reflectedIntervalMap_plB3 T x =
      unitInterval.symm (T (unitInterval.symm x)) := rfl

private theorem reflectedIntervalMap_plB3_comp (F G : IntervalMap) :
    reflectedIntervalMap_plB3 (F ∘ G) =
      reflectedIntervalMap_plB3 F ∘ reflectedIntervalMap_plB3 G := by
  funext x
  simp [reflectedIntervalMap_plB3, centralReflection_plB3]

private theorem reflectedIntervalMap_plB3_iterate
    (T : IntervalMap) (n : ℕ) :
    reflectedIntervalMap_plB3 (T^[n]) =
      (reflectedIntervalMap_plB3 T)^[n] := by
  induction n with
  | zero =>
      funext x
      simp [reflectedIntervalMap_plB3, centralReflection_plB3]
  | succ n ih =>
      rw [Function.iterate_succ', Function.iterate_succ',
        reflectedIntervalMap_plB3_comp, ih]

private theorem isFixedPoint_reflectedIntervalMap_plB3
    (T : IntervalMap) (x : I) :
    IsFixedPoint (reflectedIntervalMap_plB3 T) x ↔
      IsFixedPoint T (unitInterval.symm x) := by
  constructor
  · intro h
    have hh := congrArg unitInterval.symm h
    simpa [reflectedIntervalMap_plB3, centralReflection_plB3] using hh
  · intro h
    change unitInterval.symm (T (unitInterval.symm x)) = x
    rw [h]
    simp

private theorem finitePiecePL_centralReflection_plB3 :
    FinitePiecePL centralReflection_plB3 := by
  refine ⟨unitInterval.continuous_symm, RealPartition.trivial, ?_⟩
  intro a b _hab
  refine ⟨-1, 1, ?_⟩
  intro x _hx
  change (unitInterval.symm x : ℝ) = -1 * (x : ℝ) + 1
  rw [unitInterval.coe_symm_eq]
  ring

private theorem finitePiecePL_reflectedIntervalMap_plB3
    {T : IntervalMap} (hT : FinitePiecePL T) :
    FinitePiecePL (reflectedIntervalMap_plB3 T) := by
  exact finitePiecePL_comp finitePiecePL_centralReflection_plB3
    (finitePiecePL_comp hT finitePiecePL_centralReflection_plB3)

private def reflectedClosedSubinterval_plB3
    (J : ClosedSubinterval) : ClosedSubinterval where
  left := unitInterval.symm J.right
  right := unitInterval.symm J.left
  left_le_right := unitInterval.strictAnti_symm.antitone J.left_le_right

private theorem mem_reflectedClosedSubinterval_plB3
    (J : ClosedSubinterval) (x : I) :
    x ∈ (reflectedClosedSubinterval_plB3 J).carrier ↔
      unitInterval.symm x ∈ J.carrier := by
  constructor
  · intro hx
    constructor
    · have h := unitInterval.strictAnti_symm.antitone hx.2
      simpa [reflectedClosedSubinterval_plB3] using h
    · have h := unitInterval.strictAnti_symm.antitone hx.1
      simpa [reflectedClosedSubinterval_plB3] using h
  · intro hx
    constructor
    · have h := unitInterval.strictAnti_symm.antitone hx.2
      simpa [reflectedClosedSubinterval_plB3] using h
    · have h := unitInterval.strictAnti_symm.antitone hx.1
      simpa [reflectedClosedSubinterval_plB3] using h

private def reflectPiecewiseLinearCounterexample_plB3
    (C : PiecewiseLinearCounterexample) : PiecewiseLinearCounterexample where
  P := reflectedIntervalMap_plB3 C.P
  Q := reflectedIntervalMap_plB3 C.Q
  finitePieceP := finitePiecePL_reflectedIntervalMap_plB3 C.finitePieceP
  finitePieceQ := finitePiecePL_reflectedIntervalMap_plB3 C.finitePieceQ
  commute := by
    intro x
    simp only [reflectedIntervalMap_plB3, centralReflection_plB3,
      Function.comp_apply, unitInterval.symm_symm, unitInterval.symm_inj]
    exact C.commute _
  noCommonFixed := by
    rintro ⟨y, hyP, hyQ⟩
    apply C.noCommonFixed
    refine ⟨unitInterval.symm y, ?_, ?_⟩
    · have h := congrArg unitInterval.symm hyP
      simpa [reflectedIntervalMap_plB3, centralReflection_plB3] using h
    · have h := congrArg unitInterval.symm hyQ
      simpa [reflectedIntervalMap_plB3, centralReflection_plB3] using h

private def reflectMinimalPiecewiseLinearCounterexample_plB3
    (C : MinimalPiecewiseLinearCounterexample) :
    MinimalPiecewiseLinearCounterexample where
  base := reflectPiecewiseLinearCounterexample_plB3 C.base
  ontoP := by
    intro y
    obtain ⟨z, hz⟩ := C.ontoP (unitInterval.symm y)
    refine ⟨unitInterval.symm z, ?_⟩
    simp [reflectPiecewiseLinearCounterexample_plB3,
      reflectedIntervalMap_plB3, centralReflection_plB3, hz]
  ontoQ := by
    intro y
    obtain ⟨z, hz⟩ := C.ontoQ (unitInterval.symm y)
    refine ⟨unitInterval.symm z, ?_⟩
    simp [reflectPiecewiseLinearCounterexample_plB3,
      reflectedIntervalMap_plB3, centralReflection_plB3, hz]
  core_minimal := by
    intro J hJ
    let K := reflectedClosedSubinterval_plB3 J
    have hK : IsCommonInvariantCore C.base.P C.base.Q K := by
      constructor
      · intro x hx
        apply (mem_reflectedClosedSubinterval_plB3 J (C.base.P x)).mpr
        have hxJ := (mem_reflectedClosedSubinterval_plB3 J x).mp hx
        have himage := hJ.1 hxJ
        simpa [reflectPiecewiseLinearCounterexample_plB3,
          reflectedIntervalMap_plB3, centralReflection_plB3] using himage
      · intro x hx
        apply (mem_reflectedClosedSubinterval_plB3 J (C.base.Q x)).mpr
        have hxJ := (mem_reflectedClosedSubinterval_plB3 J x).mp hx
        have himage := hJ.2 hxJ
        simpa [reflectPiecewiseLinearCounterexample_plB3,
          reflectedIntervalMap_plB3, centralReflection_plB3] using himage
    have hKuniv : K.carrier = Set.univ := C.core_minimal K hK
    apply Set.eq_univ_of_forall
    intro y
    have hyK : unitInterval.symm y ∈ K.carrier := by
      rw [hKuniv]
      exact Set.mem_univ _
    have h :=
      (mem_reflectedClosedSubinterval_plB3 J
        (unitInterval.symm y)).mp hyK
    simpa using h

private noncomputable def reflectNormalizedPiecewiseLinearCounterexample_plB3
    (C : NormalizedPiecewiseLinearCounterexample) :
    NormalizedPiecewiseLinearCounterexample := by
  classical
  let M := reflectMinimalPiecewiseLinearCounterexample_plB3 C.base
  let fixedW := C.fixedW.image unitInterval.symm
  let fixedR := C.fixedR.image unitInterval.symm
  let fixedS := C.fixedS.image unitInterval.symm
  have hcard : fixedW.card = C.fixedW.card :=
    Finset.card_image_of_injective C.fixedW
      unitInterval.symm_bijective.injective
  have hL : piecewiseLinearNormalizationExponent fixedW =
      piecewiseLinearNormalizationExponent C.fixedW := by
    unfold piecewiseLinearNormalizationExponent
    rw [hcard]
  have hW : piecewiseLinearW M.base.P M.base.Q =
      reflectedIntervalMap_plB3 C.W := by
    change ((reflectedIntervalMap_plB3 C.P ∘
      reflectedIntervalMap_plB3 C.Q)^[2]) =
        reflectedIntervalMap_plB3 ((C.P ∘ C.Q)^[2])
    rw [← reflectedIntervalMap_plB3_comp,
      ← reflectedIntervalMap_plB3_iterate]
  have hR : piecewiseLinearR M.base.P M.base.Q fixedW =
      reflectedIntervalMap_plB3 C.R := by
    unfold piecewiseLinearR piecewiseLinearA piecewiseLinearB
    rw [hL]
    change
      ((reflectedIntervalMap_plB3 C.P)^[
          piecewiseLinearNormalizationExponent C.fixedW]) ∘
        ((reflectedIntervalMap_plB3 C.Q)^[
          piecewiseLinearNormalizationExponent C.fixedW]) = _
    rw [← reflectedIntervalMap_plB3_iterate,
      ← reflectedIntervalMap_plB3_iterate,
      ← reflectedIntervalMap_plB3_comp]
    rfl
  have hS : piecewiseLinearS M.base.P M.base.Q fixedW =
      reflectedIntervalMap_plB3 C.S := by
    change
      (piecewiseLinearR M.base.P M.base.Q fixedW)^[2] =
        reflectedIntervalMap_plB3 (C.R^[2])
    rw [hR]
    exact (reflectedIntervalMap_plB3_iterate C.R 2).symm
  exact
    { base := M
      fixedW := fixedW
      fixedW_spec := by
        intro x
        rw [hW, isFixedPoint_reflectedIntervalMap_plB3]
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
          simpa using (C.fixedW_spec y).1 hy
        · intro hx
          refine Finset.mem_image.mpr
            ⟨unitInterval.symm x, ?_, by simp⟩
          exact (C.fixedW_spec _).2 hx
      fixedR := fixedR
      fixedR_spec := by
        intro x
        rw [hR, isFixedPoint_reflectedIntervalMap_plB3]
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
          simpa using (C.fixedR_spec y).1 hy
        · intro hx
          refine Finset.mem_image.mpr
            ⟨unitInterval.symm x, ?_, by simp⟩
          exact (C.fixedR_spec _).2 hx
      fixedS := fixedS
      fixedS_spec := by
        intro x
        rw [hS, isFixedPoint_reflectedIntervalMap_plB3]
        constructor
        · intro hx
          rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
          simpa using (C.fixedS_spec y).1 hy
        · intro hx
          refine Finset.mem_image.mpr
            ⟨unitInterval.symm x, ?_, by simp⟩
          exact (C.fixedS_spec _).2 hx }

private theorem reflectNormalizedPiecewiseLinearCounterexample_plB3_W
    (C : NormalizedPiecewiseLinearCounterexample) :
    (reflectNormalizedPiecewiseLinearCounterexample_plB3 C).W =
      reflectedIntervalMap_plB3 C.W := by
  change ((reflectedIntervalMap_plB3 C.P ∘
    reflectedIntervalMap_plB3 C.Q)^[2]) =
      reflectedIntervalMap_plB3 ((C.P ∘ C.Q)^[2])
  rw [← reflectedIntervalMap_plB3_comp,
    ← reflectedIntervalMap_plB3_iterate]

private theorem reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedW_card
    (C : NormalizedPiecewiseLinearCounterexample) :
    (reflectNormalizedPiecewiseLinearCounterexample_plB3 C).fixedW.card =
      C.fixedW.card := by
  change (C.fixedW.image unitInterval.symm).card = C.fixedW.card
  exact Finset.card_image_of_injective C.fixedW
    unitInterval.symm_bijective.injective

private theorem reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedR_card
    (C : NormalizedPiecewiseLinearCounterexample) :
    (reflectNormalizedPiecewiseLinearCounterexample_plB3 C).fixedR.card =
      C.fixedR.card := by
  change (C.fixedR.image unitInterval.symm).card = C.fixedR.card
  exact Finset.card_image_of_injective C.fixedR
    unitInterval.symm_bijective.injective

private theorem reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedS_card
    (C : NormalizedPiecewiseLinearCounterexample) :
    (reflectNormalizedPiecewiseLinearCounterexample_plB3 C).fixedS.card =
      C.fixedS.card := by
  change (C.fixedS.image unitInterval.symm).card = C.fixedS.card
  exact Finset.card_image_of_injective C.fixedS
    unitInterval.symm_bijective.injective

private noncomputable def reflectLeastNormalizedPiecewiseLinearCounterexample_plB3
    (C : LeastNormalizedPiecewiseLinearCounterexample) :
    LeastNormalizedPiecewiseLinearCounterexample where
  base := reflectNormalizedPiecewiseLinearCounterexample_plB3 C.base
  lex_minimal := by
    intro D
    have h := C.lex_minimal
      (reflectNormalizedPiecewiseLinearCounterexample_plB3 D)
    rw [reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedW_card D,
      reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedR_card D,
      reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedS_card D] at h
    rw [reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedW_card C.base,
      reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedR_card C.base,
      reflectNormalizedPiecewiseLinearCounterexample_plB3_fixedS_card C.base]
    exact h

private theorem commonFixedPoint_of_reflected_plB3
    {P Q : IntervalMap}
    (h : HasCommonFixedPoint (reflectedIntervalMap_plB3 P)
      (reflectedIntervalMap_plB3 Q)) :
    HasCommonFixedPoint P Q := by
  rcases h with ⟨y, hyP, hyQ⟩
  refine ⟨unitInterval.symm y, ?_, ?_⟩
  · have h' := congrArg unitInterval.symm hyP
    simpa [reflectedIntervalMap_plB3, centralReflection_plB3] using h'
  · have h' := congrArg unitInterval.symm hyQ
    simpa [reflectedIntervalMap_plB3, centralReflection_plB3] using h'

/-- Reflect the interval simultaneously in the left-moving case.  Reflection
preserves all three fixed counts, minimality, and the counterexample, and it
turns the chosen gap into a right-moving one. -/
theorem piecewiseLinear_orientFixedGap
    (C : LeastNormalizedPiecewiseLinearCounterexample)
    (G : PiecewiseLinearUnorientedFixedGap C) :
    Nonempty (PiecewiseLinearSelectedFixedGap C) := by
  rcases G.constant_sign with hmoves | hmoves
  · exact ⟨{
      system := C
      source_commonFixed_of_system := fun h ↦ h
      p := G.p
      c := G.c
      p_lt_c := G.p_lt_c
      fixed_p := G.fixed_p
      fixed_c := G.fixed_c
      consecutive := G.consecutive
      moves_right := hmoves }⟩
  · let C' :=
      reflectLeastNormalizedPiecewiseLinearCounterexample_plB3 C
    let p' := unitInterval.symm G.c
    let c' := unitInterval.symm G.p
    have hp'c' : p' < c' :=
      unitInterval.strictAnti_symm G.p_lt_c
    have hW' : C'.W = reflectedIntervalMap_plB3 C.W := by
      simpa [C', reflectLeastNormalizedPiecewiseLinearCounterexample_plB3]
        using
          reflectNormalizedPiecewiseLinearCounterexample_plB3_W C.base
    refine ⟨{
      system := C'
      source_commonFixed_of_system := ?_
      p := p'
      c := c'
      p_lt_c := hp'c'
      fixed_p := ?_
      fixed_c := ?_
      consecutive := ?_
      moves_right := ?_ }⟩
    · intro hcommon
      apply commonFixedPoint_of_reflected_plB3
      simpa [C', reflectLeastNormalizedPiecewiseLinearCounterexample_plB3,
        reflectNormalizedPiecewiseLinearCounterexample_plB3,
        reflectMinimalPiecewiseLinearCounterexample_plB3,
        reflectPiecewiseLinearCounterexample_plB3] using hcommon
    · rw [hW', isFixedPoint_reflectedIntervalMap_plB3]
      simpa [p'] using G.fixed_c
    · rw [hW', isFixedPoint_reflectedIntervalMap_plB3]
      simpa [c'] using G.fixed_p
    · intro x hx hxfix
      have hy : unitInterval.symm x ∈ Set.Ioo G.p G.c := by
        constructor
        · have h := unitInterval.strictAnti_symm hx.2
          simpa [c'] using h
        · have h := unitInterval.strictAnti_symm hx.1
          simpa [p'] using h
      apply G.consecutive (unitInterval.symm x) hy
      rw [hW', isFixedPoint_reflectedIntervalMap_plB3] at hxfix
      exact hxfix
    · intro x hx
      have hy : unitInterval.symm x ∈ Set.Ioo G.p G.c := by
        constructor
        · have h := unitInterval.strictAnti_symm hx.2
          simpa [c'] using h
        · have h := unitInterval.strictAnti_symm hx.1
          simpa [p'] using h
      have hmove := hmoves (unitInterval.symm x) hy
      have hant := unitInterval.strictAnti_symm hmove
      rw [hW']
      simpa [reflectedIntervalMap_plB3, centralReflection_plB3] using hant

/-- Boundary 3: choose the consecutive repelling fixed gap and orient its
available side. -/
theorem exists_piecewiseLinearSelectedFixedGap
    (C : LeastNormalizedPiecewiseLinearCounterexample) :
    Nonempty (PiecewiseLinearSelectedFixedGap C) := by
  obtain ⟨G⟩ := exists_piecewiseLinearUnorientedFixedGap C
  exact piecewiseLinear_orientFixedGap C G

/-- The finite directed-state return fixes both ends for `A` and `B` and
places all relevant maps in affine one-sided `C1+BV` germs. -/
structure PiecewiseLinearDirectedReturnData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop where
  fixed_A_p : IsFixedPoint G.A G.p
  fixed_A_c : IsFixedPoint G.A G.c
  fixed_B_p : IsFixedPoint G.B G.p
  fixed_B_c : IsFixedPoint G.B G.c
  right_germ_W : HasRightGermC1BV G.W G.p
  right_germ_A : HasRightGermC1BV G.A G.p
  right_germ_B : HasRightGermC1BV G.B G.p

/-- Internal fixed-point permutation data used by the elementary PL return. -/
private def PermutesFixedPointsPLCore
    (F W : IntervalMap) : Prop :=
  ∃ e : fixedPoints W ≃ fixedPoints W,
    ∀ x, F x.1 = (e x).1

private theorem permutesFixedPointsPLCore_of_bijOn
    {F W : IntervalMap}
    (hbij : Set.BijOn F (fixedPoints W) (fixedPoints W)) :
    PermutesFixedPointsPLCore F W := by
  let f : fixedPoints W → fixedPoints W :=
    fun x => ⟨F x.1, hbij.mapsTo x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hbij.injOn x.2 y.2 (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hFxy⟩ := hbij.surjOn y.2
      refine ⟨⟨x, hx⟩, ?_⟩
      exact Subtype.ext hFxy
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  intro x
  rfl

private theorem permutesFixedPointsPLCore_left_iterates_comp
    {P Q : IntervalMap} (hcomm : Commute P Q)
    {m n : ℕ} (hm : 0 < m) :
    PermutesFixedPointsPLCore P ((P^[m]) ∘ (Q^[n])) := by
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hfactor : Commute P ((P^[k]) ∘ (Q^[n])) :=
    (Function.Commute.self_iterate P k).comp_right
      (hcomm.iterate_right n)
  rw [Function.iterate_succ' P k]
  simpa only [Function.comp_assoc] using
    permutesFixedPointsPLCore_of_bijOn
      hfactor.left_bijOn_fixedPoints_comp

private theorem permutesFixedPointsPLCore_right_iterates_comp
    {P Q : IntervalMap} (hcomm : Commute P Q)
    {m n : ℕ} (hn : 0 < n) :
    PermutesFixedPointsPLCore Q ((P^[m]) ∘ (Q^[n])) := by
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hfactor : Commute ((P^[m]) ∘ (Q^[k])) Q :=
    (hcomm.iterate_left m).comp_left
      (Function.Commute.iterate_self Q k)
  rw [Function.iterate_succ Q k]
  simpa only [Function.comp_assoc] using
    permutesFixedPointsPLCore_of_bijOn
      hfactor.right_bijOn_fixedPoints_comp

/-- A permutation of the fixed set returns every point after the canonical
normalization exponent. -/
private theorem canonicalFactorial_return_fixedPoint_plCore
    {F W : IntervalMap} (fixedW : Finset I)
    (hmem : ∀ x : I, x ∈ fixedW ↔ IsFixedPoint W x)
    (hperm : PermutesFixedPointsPLCore F W)
    {x : I} (hx : IsFixedPoint W x) :
    (F^[2 * Nat.factorial (2 * fixedW.card)]) x = x := by
  classical
  letI : Fintype (fixedPoints W) := Fintype.ofFinset fixedW hmem
  have hcard : Fintype.card (fixedPoints W) = fixedW.card :=
    Fintype.card_ofFinset fixedW hmem
  obtain ⟨e, he⟩ := hperm
  have heFactorial : e ^ Nat.factorial fixedW.card = 1 := by
    rw [← hcard, ← Fintype.card_perm]
    exact pow_card_eq_one
  have hfactorial_dvd : Nat.factorial fixedW.card ∣
      2 * Nat.factorial (2 * fixedW.card) := by
    apply dvd_mul_of_dvd_right
    exact Nat.factorial_dvd_factorial
      (Nat.le_mul_of_pos_left fixedW.card (by norm_num))
  obtain ⟨k, hk⟩ := hfactorial_dvd
  have heReturn : e ^ (2 * Nat.factorial (2 * fixedW.card)) = 1 := by
    rw [hk, pow_mul, heFactorial, one_pow]
  let xsub : fixedPoints W := ⟨x, hx⟩
  have hiter : ∀ n : ℕ, (F^[n]) x = ((e ^ n) xsub).1 := by
    intro n
    induction n with
    | zero => simp [xsub]
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        have hphysical := he ((e ^ n) xsub)
        rw [hphysical, pow_succ']
        rfl
  rw [hiter, heReturn]
  rfl

private theorem piecewiseLinear_return_fixes_fixedPoint_P
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    {x : I} (hx : IsFixedPoint G.W x) : IsFixedPoint G.A x := by
  have hWform : G.W = (G.P^[2]) ∘ (G.Q^[2]) := by
    simpa [PiecewiseLinearSelectedFixedGap.W,
      PiecewiseLinearSelectedFixedGap.P,
      PiecewiseLinearSelectedFixedGap.Q,
      LeastNormalizedPiecewiseLinearCounterexample.W,
      LeastNormalizedPiecewiseLinearCounterexample.P,
      LeastNormalizedPiecewiseLinearCounterexample.Q,
      NormalizedPiecewiseLinearCounterexample.W,
      piecewiseLinearW, iterateMap] using
        G.system.commute.comp_iterate 2
  have hperm : PermutesFixedPointsPLCore G.P G.W := by
    rw [hWform]
    exact permutesFixedPointsPLCore_left_iterates_comp
      G.system.commute (by norm_num)
  have hreturn := canonicalFactorial_return_fixedPoint_plCore
    G.system.base.fixedW (by
      intro y
      simpa [PiecewiseLinearSelectedFixedGap.W,
        LeastNormalizedPiecewiseLinearCounterexample.W] using
        G.system.base.fixedW_spec y) hperm hx
  simpa [PiecewiseLinearSelectedFixedGap.A,
    PiecewiseLinearSelectedFixedGap.P,
    LeastNormalizedPiecewiseLinearCounterexample.A,
    NormalizedPiecewiseLinearCounterexample.A,
    piecewiseLinearA, iterateMap] using hreturn

private theorem piecewiseLinear_return_fixes_fixedPoint_Q
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    {x : I} (hx : IsFixedPoint G.W x) : IsFixedPoint G.B x := by
  have hWform : G.W = (G.P^[2]) ∘ (G.Q^[2]) := by
    simpa [PiecewiseLinearSelectedFixedGap.W,
      PiecewiseLinearSelectedFixedGap.P,
      PiecewiseLinearSelectedFixedGap.Q,
      LeastNormalizedPiecewiseLinearCounterexample.W,
      LeastNormalizedPiecewiseLinearCounterexample.P,
      LeastNormalizedPiecewiseLinearCounterexample.Q,
      NormalizedPiecewiseLinearCounterexample.W,
      piecewiseLinearW, iterateMap] using
        G.system.commute.comp_iterate 2
  have hperm : PermutesFixedPointsPLCore G.Q G.W := by
    rw [hWform]
    exact permutesFixedPointsPLCore_right_iterates_comp
      G.system.commute (by norm_num)
  have hreturn := canonicalFactorial_return_fixedPoint_plCore
    G.system.base.fixedW (by
      intro y
      simpa [PiecewiseLinearSelectedFixedGap.W,
        LeastNormalizedPiecewiseLinearCounterexample.W] using
        G.system.base.fixedW_spec y) hperm hx
  simpa [PiecewiseLinearSelectedFixedGap.B,
    PiecewiseLinearSelectedFixedGap.Q,
    LeastNormalizedPiecewiseLinearCounterexample.B,
    NormalizedPiecewiseLinearCounterexample.B,
    piecewiseLinearB, iterateMap] using hreturn

/-- The even finite-state return makes `A` fix the selected base. -/
theorem piecewiseLinear_return_fixes_A_p
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    IsFixedPoint G.A G.p := by
  exact piecewiseLinear_return_fixes_fixedPoint_P G G.fixed_p

/-- The same return exponent makes `A` fix the other gap endpoint. -/
theorem piecewiseLinear_return_fixes_A_c
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    IsFixedPoint G.A G.c := by
  exact piecewiseLinear_return_fixes_fixedPoint_P G G.fixed_c

/-- The even finite-state return makes `B` fix the selected base. -/
theorem piecewiseLinear_return_fixes_B_p
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    IsFixedPoint G.B G.p := by
  exact piecewiseLinear_return_fixes_fixedPoint_Q G G.fixed_p

/-- The same return exponent makes `B` fix the other gap endpoint. -/
theorem piecewiseLinear_return_fixes_B_c
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    IsFixedPoint G.B G.c := by
  exact piecewiseLinear_return_fixes_fixedPoint_Q G G.fixed_c

/-! ### Elementary directed-side return for finite PL factors -/

private def MovesAwayAlongPLCore (σ : DirectedSide) (x y : I) : Prop :=
  match σ.direction with
  | .right => σ.base < x ∧ x < y
  | .left => x < σ.base ∧ y < x

private def IsRepellingDirectedStatePLCore
    (W : IntervalMap) (σ : DirectedSide) : Prop :=
  IsFixedPoint W σ.base ∧
    ∃ U : Set I, IsOpen U ∧ σ.base ∈ U ∧
      (U ∩ σ.direction.puncturedRay σ.base).Nonempty ∧
      ∀ x ∈ U ∩ σ.direction.puncturedRay σ.base,
        W x ∈ σ.direction.puncturedRay σ.base ∧
          MovesAwayAlongPLCore σ x (W x)

private def repellingDirectedStatesPLCore (W : IntervalMap) :
    Set DirectedSide :=
  {σ | IsRepellingDirectedStatePLCore W σ}

private def CarriesDirectedSidePLCore
    (F : IntervalMap) (σ τ : DirectedSide) : Prop :=
  F σ.base = τ.base ∧
    ∃ U : Set I, IsOpen U ∧ σ.base ∈ U ∧
      (U ∩ σ.direction.puncturedRay σ.base).Nonempty ∧
      MapsTo F (U ∩ σ.direction.puncturedRay σ.base)
        (τ.direction.puncturedRay τ.base)

private def PermutesRepellingDirectedStatesPLCore
    (F W : IntervalMap) : Prop :=
  ∃ e : {σ // IsRepellingDirectedStatePLCore W σ} ≃
      {σ // IsRepellingDirectedStatePLCore W σ},
    ∀ σ, CarriesDirectedSidePLCore F σ.1 (e σ).1

private theorem repellingDirectedStatesPLCore_finite
    {W : IntervalMap} (hfix : (fixedPoints W).Finite) :
    (repellingDirectedStatesPLCore W).Finite := by
  let sideCode : Side → Bool
    | .left => false
    | .right => true
  have hsideCode : Function.Injective sideCode := by
    intro a b
    cases a <;> cases b <;> simp [sideCode]
  let encode : DirectedSide → I × Bool :=
    fun σ => (σ.base, sideCode σ.direction)
  have hencode : Function.Injective encode := by
    intro σ τ h
    cases σ with
    | mk σbase σdirection σavailable =>
      cases τ with
      | mk τbase τdirection τavailable =>
        have hbase : σbase = τbase := congrArg Prod.fst h
        have hdirection : σdirection = τdirection :=
          hsideCode (congrArg Prod.snd h)
        subst τbase
        subst τdirection
        rfl
  apply Set.Finite.of_finite_image _ hencode.injOn
  apply (hfix.prod (Set.finite_univ : (Set.univ : Set Bool).Finite)).subset
  rintro z ⟨σ, hσ, rfl⟩
  constructor
  · change IsRepellingDirectedStatePLCore W σ at hσ
    exact hσ.1
  · exact Set.mem_univ _

private theorem piecewiseLinear_selectedGap_is_repelling
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    IsRepellingDirectedStatePLCore G.W
      (rightDirectedSide G.p
        (G.p_lt_c.trans_le G.c.property.2)) := by
  constructor
  · exact G.fixed_p
  · refine ⟨Set.Iio G.c, isOpen_Iio, G.p_lt_c, ?_, ?_⟩
    · obtain ⟨x, hpx, hxc⟩ := exists_between G.p_lt_c
      refine ⟨x, hxc, ?_⟩
      simpa [rightDirectedSide, Side.puncturedRay] using hpx
    · intro x hx
      have hxc : x < G.c := hx.1
      have hpx : G.p < x := by
        simpa [rightDirectedSide, Side.puncturedRay] using hx.2
      have hmove : x < G.W x := G.moves_right x ⟨hpx, hxc⟩
      constructor
      · simpa [rightDirectedSide, Side.puncturedRay] using hpx.trans hmove
      · simpa [rightDirectedSide, MovesAwayAlongPLCore] using
          And.intro hpx hmove

/-- On a finite affine presentation, a repelling right state has a smaller
closed representative on which the map is strictly increasing and moves
strictly away from its base. -/
private theorem repelling_right_local_strictMono_plCore
    {W : IntervalMap} {p : I} {hp : p < rightEndpoint}
    (hW : FinitePiecePL W)
    (hrep : IsRepellingDirectedStatePLCore W
      (rightDirectedSide p hp)) :
    ∃ q : I, p < q ∧ StrictMonoOn W (Set.Icc p q) ∧
      ∀ x ∈ Set.Ioc p q, x < W x := by
  rcases hrep with ⟨hWp, U, hUopen, hpU, _hside, haction⟩
  obtain ⟨u, hu, hpu⟩ :=
    exists_Ico_subset_of_mem_nhds' (hUopen.mem_nhds hpU) hp
  rcases hW.2 with ⟨partition, hpartition⟩
  obtain ⟨a, b, hab, hap, hpb⟩ :=
    partition.exists_adjacent_right_plCore p.property
      (lt_of_lt_of_le hp rightEndpoint.property.2)
  obtain ⟨m, c, hformula⟩ := hpartition hab
  obtain ⟨qReal, hpqReal, hqReal⟩ :=
    exists_between (lt_min hpb hu.1)
  have hqb : qReal < b := hqReal.trans_le (min_le_left _ _)
  have hqu : qReal < (u : ℝ) :=
    hqReal.trans_le (min_le_right _ _)
  let q : I := ⟨qReal, ⟨p.property.1.trans hpqReal.le,
    hqu.le.trans u.property.2⟩⟩
  have hpq : p < q := hpqReal
  have hpCell : p ∈ intervalCell a b := ⟨hap, hpb.le⟩
  have hqCell : q ∈ intervalCell a b :=
    ⟨hap.trans hpq.le, hqb.le⟩
  have hqU : q ∈ U := hpu ⟨hpq.le, hqu⟩
  have hqSide : q ∈
      (rightDirectedSide p hp).direction.puncturedRay p := by
    simpa [rightDirectedSide, Side.puncturedRay] using hpq
  have hqAway := (haction q ⟨hqU, hqSide⟩).2
  have hqmove : q < W q := by
    simpa [rightDirectedSide, MovesAwayAlongPLCore] using hqAway.2
  have hWpReal : (W p : ℝ) = (p : ℝ) := congrArg Subtype.val hWp
  have hpformula := hformula p hpCell
  have hqformula := hformula q hqCell
  have hmone : 1 < m := by
    rw [hWpReal] at hpformula
    have hmoveReal : (q : ℝ) < (W q : ℝ) := hqmove
    rw [hqformula] at hmoveReal
    nlinarith
  refine ⟨q, hpq, ?_, ?_⟩
  · intro x hx y hy hxy
    apply Subtype.coe_lt_coe.mp
    have hxCell : x ∈ intervalCell a b :=
      ⟨hap.trans hx.1,
        (show (x : ℝ) ≤ (q : ℝ) from hx.2).trans hqb.le⟩
    have hyCell : y ∈ intervalCell a b :=
      ⟨hap.trans hy.1,
        (show (y : ℝ) ≤ (q : ℝ) from hy.2).trans hqb.le⟩
    rw [hformula x hxCell, hformula y hyCell]
    have hxyReal : (x : ℝ) < (y : ℝ) := hxy
    nlinarith
  · intro x hx
    have hxU : x ∈ U := hpu ⟨hx.1.le, hx.2.trans_lt hqu⟩
    have hxSide : x ∈
        (rightDirectedSide p hp).direction.puncturedRay p := by
      simpa [rightDirectedSide, Side.puncturedRay] using hx.1
    have hmove := (haction x ⟨hxU, hxSide⟩).2
    simpa [rightDirectedSide, MovesAwayAlongPLCore] using hmove.2

/-- The factor-action construction on a right-directed repelling state. -/
private theorem factor_maps_repellingRightState_plCore
    {W F H : IntervalMap} {p : I}
    {hp : p < rightEndpoint}
    (hW : FinitePiecePL W) (hF : Continuous F)
    (hfactor : H ∘ F = W) (hcommute : Commute F W)
    (hrep : IsRepellingDirectedStatePLCore W (rightDirectedSide p hp)) :
    ∃ tau : DirectedSide,
      IsRepellingDirectedStatePLCore W tau ∧
      CarriesDirectedSidePLCore F (rightDirectedSide p hp) tau ∧
      CarriesDirectedSidePLCore H tau (rightDirectedSide p hp) := by
  obtain ⟨q, hpq, hWstrict, hWaway⟩ :=
    repelling_right_local_strictMono_plCore hW hrep
  have hWp : W p = p := hrep.1
  have hpPre : p ∈ W ⁻¹' Set.Iio q := by
    change W p < q
    simpa [hWp] using hpq
  have hpreOpen : IsOpen (W ⁻¹' Set.Iio q) :=
    isOpen_Iio.preimage hW.1
  obtain ⟨r, hr, hrsub⟩ :=
    exists_Ico_subset_of_mem_nhds' (hpreOpen.mem_nhds hpPre) hpq
  obtain ⟨s, hps, hsr⟩ := exists_between hr.1
  have hsq : s < q := hsr.trans_le hr.2
  have hsMemQ : s ∈ Set.Icc p q := ⟨hps.le, hsq.le⟩
  have hpMemQ : p ∈ Set.Icc p q := ⟨le_rfl, hpq.le⟩
  have hWmaps : MapsTo W (Set.Icc p s) (Set.Icc p q) := by
    intro x hx
    constructor
    · calc
        p = W p := hWp.symm
        _ ≤ W x := hWstrict.monotoneOn hpMemQ
          ⟨hx.1, hx.2.trans hsq.le⟩ hx.1
    · exact (hrsub ⟨hx.1, hx.2.trans_lt hsr⟩).le
  have hFinj : Set.InjOn F (Set.Icc p q) := by
    intro x hx y hy hxy
    apply hWstrict.injOn hx hy
    calc
      W x = H (F x) := (congrFun hfactor x).symm
      _ = H (F y) := congrArg H hxy
      _ = W y := congrFun hfactor y
  rcases hF.continuousOn.strictMonoOn_of_injOn_Icc' hpq.le hFinj with
      hFmono | hFanti
  · have hFps : F p < F s := hFmono hpMemQ hsMemQ hps
    let tau : DirectedSide :=
      rightDirectedSide (F p) (hFps.trans_le (F s).property.2)
    have hFcarry : CarriesDirectedSidePLCore F (rightDirectedSide p hp) tau := by
      constructor
      · rfl
      · refine ⟨Set.Iio s, isOpen_Iio, hps, ?_, ?_⟩
        · obtain ⟨m, hpm, hms⟩ := exists_between hps
          refine ⟨m, hms, ?_⟩
          simpa [rightDirectedSide, Side.puncturedRay] using hpm
        · intro x hx
          have hpx : p < x := by
            simpa [rightDirectedSide, Side.puncturedRay] using hx.2
          have hxq : x ∈ Set.Icc p q :=
            ⟨hpx.le, hx.1.le.trans hsq.le⟩
          have hFx : F p < F x := hFmono hpMemQ hxq hpx
          simpa [tau, rightDirectedSide, Side.puncturedRay] using hFx
    have htargetRep : IsRepellingDirectedStatePLCore W tau := by
      constructor
      · change W (F p) = F p
        rw [← hcommute p, hWp]
      · refine ⟨Set.Iio (F s), isOpen_Iio, hFps, ?_, ?_⟩
        · obtain ⟨m, hpm, hms⟩ := exists_between hps
          refine ⟨F m, hFmono ⟨hpm.le, hms.le.trans hsq.le⟩ hsMemQ hms, ?_⟩
          have hFpm : F p < F m :=
            hFmono hpMemQ ⟨hpm.le, hms.le.trans hsq.le⟩ hpm
          simpa [tau, rightDirectedSide, Side.puncturedRay] using hFpm
        · intro y hy
          have hFpy : F p < y := by
            simpa [tau, rightDirectedSide, Side.puncturedRay] using hy.2
          have hyFs : y < F s := hy.1
          obtain ⟨x, hx, hFxy⟩ := intermediate_value_Icc hpq.le
            hF.continuousOn
            (show y ∈ Set.Icc (F p) (F q) from
              ⟨hFpy.le, hyFs.le.trans (hFmono hsMemQ
                (Set.right_mem_Icc.mpr hpq.le) hsq).le⟩)
          have hpx : p < x := lt_of_le_of_ne hx.1 fun hxp ↦ by
            subst x
            exact (ne_of_gt hFpy) hFxy.symm
          have hxs : x < s := by
            by_contra hnot
            have hsx : s ≤ x := le_of_not_gt hnot
            have hFsx : F s ≤ F x :=
              hFmono.monotoneOn hsMemQ hx hsx
            rw [hFxy] at hFsx
            exact (not_le_of_gt hyFs) hFsx
          have hWxMem := hWmaps ⟨hpx.le, hxs.le⟩
          have hxAway : x < W x :=
            hWaway x ⟨hpx, hxs.le.trans hsq.le⟩
          have hFW : F x < F (W x) :=
            hFmono hx hWxMem hxAway
          have hWy : W y = F (W x) := by
            rw [← hFxy, ← hcommute x]
          have hyAway : y < W y := by
            rw [hWy, ← hFxy]
            exact hFW
          constructor
          · have : F p < W y := hFpy.trans hyAway
            simpa [tau, rightDirectedSide, Side.puncturedRay] using this
          · simpa [tau, rightDirectedSide, MovesAwayAlongPLCore] using
              And.intro hFpy hyAway
    have hHcarry : CarriesDirectedSidePLCore H tau (rightDirectedSide p hp) := by
      constructor
      · change H (F p) = p
        exact (by simpa [Function.comp_apply] using
          (congrFun hfactor p).trans hWp)
      · refine ⟨Set.Iio (F s), isOpen_Iio, hFps, ?_, ?_⟩
        · obtain ⟨m, hpm, hms⟩ := exists_between hps
          refine ⟨F m, hFmono ⟨hpm.le, hms.le.trans hsq.le⟩ hsMemQ hms, ?_⟩
          have := hFmono hpMemQ ⟨hpm.le, hms.le.trans hsq.le⟩ hpm
          simpa [tau, rightDirectedSide, Side.puncturedRay] using this
        · intro y hy
          have hFpy : F p < y := by
            simpa [tau, rightDirectedSide, Side.puncturedRay] using hy.2
          obtain ⟨x, hx, hFxy⟩ := intermediate_value_Icc hpq.le
            hF.continuousOn
            (show y ∈ Set.Icc (F p) (F q) from
              ⟨hFpy.le, hy.1.le.trans (hFmono hsMemQ
                (Set.right_mem_Icc.mpr hpq.le) hsq).le⟩)
          have hpx : p < x := lt_of_le_of_ne hx.1 fun hxp ↦ by
            subst x
            exact (ne_of_gt hFpy) hFxy.symm
          have hHx : H y = W x := by
            rw [← hFxy]
            simpa [Function.comp_apply] using congrFun hfactor x
          have hpWx : p < W x := by
            exact hpx.trans (hWaway x ⟨hpx, hx.2⟩)
          rw [hHx]
          simpa [rightDirectedSide, Side.puncturedRay] using hpWx
    exact ⟨tau, htargetRep, hFcarry, hHcarry⟩
  · have hFsp : F s < F p := hFanti hpMemQ hsMemQ hps
    have hleftAvail : leftEndpoint < F p :=
      (F s).property.1.trans_lt hFsp
    let tau : DirectedSide := leftDirectedSide (F p) hleftAvail
    have hFcarry : CarriesDirectedSidePLCore F (rightDirectedSide p hp) tau := by
      constructor
      · rfl
      · refine ⟨Set.Iio s, isOpen_Iio, hps, ?_, ?_⟩
        · obtain ⟨m, hpm, hms⟩ := exists_between hps
          refine ⟨m, hms, ?_⟩
          simpa [rightDirectedSide, Side.puncturedRay] using hpm
        · intro x hx
          have hpx : p < x := by
            simpa [rightDirectedSide, Side.puncturedRay] using hx.2
          have hxq : x ∈ Set.Icc p q :=
            ⟨hpx.le, hx.1.le.trans hsq.le⟩
          have hFx : F x < F p := hFanti hpMemQ hxq hpx
          simpa [tau, leftDirectedSide, Side.puncturedRay] using hFx
    have htargetRep : IsRepellingDirectedStatePLCore W tau := by
      constructor
      · change W (F p) = F p
        rw [← hcommute p, hWp]
      · refine ⟨Set.Ioi (F s), isOpen_Ioi, hFsp, ?_, ?_⟩
        · obtain ⟨m, hpm, hms⟩ := exists_between hps
          refine ⟨F m, hFanti ⟨hpm.le, hms.le.trans hsq.le⟩ hsMemQ hms, ?_⟩
          have hFmp : F m < F p :=
            hFanti hpMemQ ⟨hpm.le, hms.le.trans hsq.le⟩ hpm
          simpa [tau, leftDirectedSide, Side.puncturedRay] using hFmp
        · intro y hy
          have hyFp : y < F p := by
            simpa [tau, leftDirectedSide, Side.puncturedRay] using hy.2
          have hFsy : F s < y := hy.1
          obtain ⟨x, hx, hFxy⟩ := intermediate_value_Icc' hpq.le
            hF.continuousOn
            (show y ∈ Set.Icc (F q) (F p) from
              ⟨(hFanti hsMemQ (Set.right_mem_Icc.mpr hpq.le) hsq).le.trans
                  hFsy.le, hyFp.le⟩)
          have hpx : p < x := lt_of_le_of_ne hx.1 fun hxp ↦ by
            subst x
            exact (ne_of_lt hyFp) hFxy.symm
          have hxs : x < s := by
            by_contra hnot
            have hsx : s ≤ x := le_of_not_gt hnot
            have hFxs : F x ≤ F s :=
              hFanti.antitoneOn hsMemQ hx hsx
            rw [hFxy] at hFxs
            exact (not_le_of_gt hFsy) hFxs
          have hWxMem := hWmaps ⟨hpx.le, hxs.le⟩
          have hxAway : x < W x :=
            hWaway x ⟨hpx, hxs.le.trans hsq.le⟩
          have hFW : F (W x) < F x := hFanti hx hWxMem hxAway
          have hWy : W y = F (W x) := by
            rw [← hFxy, ← hcommute x]
          have hyAway : W y < y := by
            rw [hWy, ← hFxy]
            exact hFW
          constructor
          · have : W y < F p := hyAway.trans hyFp
            simpa [tau, leftDirectedSide, Side.puncturedRay] using this
          · simpa [tau, leftDirectedSide, MovesAwayAlongPLCore] using
              And.intro hyFp hyAway
    have hHcarry : CarriesDirectedSidePLCore H tau (rightDirectedSide p hp) := by
      constructor
      · change H (F p) = p
        exact (by simpa [Function.comp_apply] using
          (congrFun hfactor p).trans hWp)
      · refine ⟨Set.Ioi (F s), isOpen_Ioi, hFsp, ?_, ?_⟩
        · obtain ⟨m, hpm, hms⟩ := exists_between hps
          refine ⟨F m, hFanti ⟨hpm.le, hms.le.trans hsq.le⟩ hsMemQ hms, ?_⟩
          have := hFanti hpMemQ ⟨hpm.le, hms.le.trans hsq.le⟩ hpm
          simpa [tau, leftDirectedSide, Side.puncturedRay] using this
        · intro y hy
          have hyFp : y < F p := by
            simpa [tau, leftDirectedSide, Side.puncturedRay] using hy.2
          obtain ⟨x, hx, hFxy⟩ := intermediate_value_Icc' hpq.le
            hF.continuousOn
            (show y ∈ Set.Icc (F q) (F p) from
              ⟨(hFanti hsMemQ (Set.right_mem_Icc.mpr hpq.le) hsq).le.trans
                  hy.1.le, hyFp.le⟩)
          have hpx : p < x := lt_of_le_of_ne hx.1 fun hxp ↦ by
            subst x
            exact (ne_of_lt hyFp) hFxy.symm
          have hHx : H y = W x := by
            rw [← hFxy]
            simpa [Function.comp_apply] using congrFun hfactor x
          have hpWx : p < W x := hpx.trans (hWaway x ⟨hpx, hx.2⟩)
          rw [hHx]
          simpa [rightDirectedSide, Side.puncturedRay] using hpWx
    exact ⟨tau, htargetRep, hFcarry, hHcarry⟩

/-- Central reflection, used only to transport the left-directed PL factor
argument to the checked right-directed one. -/
private def centralReflection_plB4 : IntervalMap := unitInterval.symm

private def reflectedIntervalMap_plB4 (T : IntervalMap) : IntervalMap :=
  centralReflection_plB4 ∘ T ∘ centralReflection_plB4

@[simp] private theorem reflectedIntervalMap_plB4_apply
    (T : IntervalMap) (x : I) :
    reflectedIntervalMap_plB4 T x =
      unitInterval.symm (T (unitInterval.symm x)) := rfl

private theorem reflectedIntervalMap_plB4_comp (F G : IntervalMap) :
    reflectedIntervalMap_plB4 (F ∘ G) =
      reflectedIntervalMap_plB4 F ∘ reflectedIntervalMap_plB4 G := by
  funext x
  simp [reflectedIntervalMap_plB4, centralReflection_plB4]

private theorem reflectedIntervalMap_plB4_involutive (T : IntervalMap) :
    reflectedIntervalMap_plB4 (reflectedIntervalMap_plB4 T) = T := by
  funext x
  simp [reflectedIntervalMap_plB4, centralReflection_plB4]

private theorem isFixedPoint_reflectedIntervalMap_plB4
    (T : IntervalMap) (x : I) :
    IsFixedPoint (reflectedIntervalMap_plB4 T) x ↔
      IsFixedPoint T (unitInterval.symm x) := by
  constructor
  · intro h
    have hh := congrArg unitInterval.symm h
    simpa [reflectedIntervalMap_plB4, centralReflection_plB4] using hh
  · intro h
    change unitInterval.symm (T (unitInterval.symm x)) = x
    rw [h]
    simp

private theorem finitePiecePL_centralReflection_plB4 :
    FinitePiecePL centralReflection_plB4 := by
  refine ⟨unitInterval.continuous_symm, RealPartition.trivial, ?_⟩
  intro a b _hab
  refine ⟨-1, 1, ?_⟩
  intro x _hx
  change (unitInterval.symm x : ℝ) = -1 * (x : ℝ) + 1
  rw [unitInterval.coe_symm_eq]
  ring

private theorem finitePiecePL_reflectedIntervalMap_plB4
    {T : IntervalMap} (hT : FinitePiecePL T) :
    FinitePiecePL (reflectedIntervalMap_plB4 T) := by
  exact finitePiecePL_comp finitePiecePL_centralReflection_plB4
    (finitePiecePL_comp hT finitePiecePL_centralReflection_plB4)


private def reflectedDirectedSide_plB4 : DirectedSide → DirectedSide
  | ⟨base, .left, havail⟩ =>
      rightDirectedSide (unitInterval.symm base) (by
        rcases havail with ⟨x, hx⟩
        have h := unitInterval.strictAnti_symm hx
        exact h.trans_le (unitInterval.symm x).property.2)
  | ⟨base, .right, havail⟩ =>
      leftDirectedSide (unitInterval.symm base) (by
        rcases havail with ⟨x, hx⟩
        have h := unitInterval.strictAnti_symm hx
        exact (unitInterval.symm x).property.1.trans_lt h)

@[simp] private theorem reflectedDirectedSide_plB4_base (sigma : DirectedSide) :
    (reflectedDirectedSide_plB4 sigma).base = unitInterval.symm sigma.base := by
  cases sigma with
  | mk base direction available => cases direction <;> rfl

@[simp] private theorem reflectedDirectedSide_plB4_involutive
    (sigma : DirectedSide) :
    reflectedDirectedSide_plB4 (reflectedDirectedSide_plB4 sigma) = sigma := by
  cases sigma with
  | mk base direction available =>
      cases direction <;> simp [reflectedDirectedSide_plB4, rightDirectedSide,
        leftDirectedSide]

private theorem mem_reflectedDirectedSide_plB4_puncturedRay
    (sigma : DirectedSide) (x : I) :
    x ∈ (reflectedDirectedSide_plB4 sigma).direction.puncturedRay
        (reflectedDirectedSide_plB4 sigma).base ↔
      unitInterval.symm x ∈ sigma.direction.puncturedRay sigma.base := by
  cases sigma with
  | mk base direction available =>
      cases direction with
      | left =>
          change unitInterval.symm base < x ↔ unitInterval.symm x < base
          constructor
          · intro h
            have := unitInterval.strictAnti_symm h
            simpa using this
          · intro h
            have := unitInterval.strictAnti_symm h
            simpa using this
      | right =>
          change x < unitInterval.symm base ↔ base < unitInterval.symm x
          constructor
          · intro h
            have := unitInterval.strictAnti_symm h
            simpa using this
          · intro h
            have := unitInterval.strictAnti_symm h
            simpa using this

private theorem movesAway_reflectedDirectedSide_plB4
    (sigma : DirectedSide) (x y : I) :
    MovesAwayAlongPLCore (reflectedDirectedSide_plB4 sigma) x y ↔
      MovesAwayAlongPLCore sigma (unitInterval.symm x) (unitInterval.symm y) := by
  cases sigma with
  | mk base direction available =>
      cases direction with
      | left =>
          change (unitInterval.symm base < x ∧ x < y) ↔
            (unitInterval.symm x < base ∧
              unitInterval.symm y < unitInterval.symm x)
          constructor
          · rintro ⟨hbase, hxy⟩
            constructor
            · have := unitInterval.strictAnti_symm hbase
              simpa using this
            · exact unitInterval.strictAnti_symm hxy
          · rintro ⟨hbase, hxy⟩
            constructor
            · have := unitInterval.strictAnti_symm hbase
              simpa using this
            · have := unitInterval.strictAnti_symm hxy
              simpa using this
      | right =>
          change (x < unitInterval.symm base ∧ y < x) ↔
            (base < unitInterval.symm x ∧
              unitInterval.symm x < unitInterval.symm y)
          constructor
          · rintro ⟨hbase, hyx⟩
            constructor
            · have := unitInterval.strictAnti_symm hbase
              simpa using this
            · exact unitInterval.strictAnti_symm hyx
          · rintro ⟨hbase, hxy⟩
            constructor
            · have := unitInterval.strictAnti_symm hbase
              simpa using this
            · have := unitInterval.strictAnti_symm hxy
              simpa using this

private theorem repelling_reflectedDirectedSide_plB4
    {W : IntervalMap} {sigma : DirectedSide}
    (hrep : IsRepellingDirectedStatePLCore W sigma) :
    IsRepellingDirectedStatePLCore (reflectedIntervalMap_plB4 W)
      (reflectedDirectedSide_plB4 sigma) := by
  rcases hrep with ⟨hfixed, U, hUopen, hbaseU, hside, haction⟩
  constructor
  · rw [isFixedPoint_reflectedIntervalMap_plB4]
    simpa using hfixed
  · let U' : Set I := unitInterval.symm ⁻¹' U
    have hU'open : IsOpen U' :=
      hUopen.preimage unitInterval.continuous_symm
    have hbaseU' : (reflectedDirectedSide_plB4 sigma).base ∈ U' := by
      change unitInterval.symm (reflectedDirectedSide_plB4 sigma).base ∈ U
      simpa using hbaseU
    have hside' : (U' ∩
        (reflectedDirectedSide_plB4 sigma).direction.puncturedRay
          (reflectedDirectedSide_plB4 sigma).base).Nonempty := by
      rcases hside with ⟨x, hxU, hxside⟩
      refine ⟨unitInterval.symm x, ?_, ?_⟩
      · simpa [U'] using hxU
      · apply (mem_reflectedDirectedSide_plB4_puncturedRay sigma _).2
        simpa using hxside
    refine ⟨U', hU'open, hbaseU', hside', ?_⟩
    intro x hx
    have hxU : unitInterval.symm x ∈ U := hx.1
    have hxside :=
      (mem_reflectedDirectedSide_plB4_puncturedRay sigma x).1 hx.2
    have horiginal := haction (unitInterval.symm x) ⟨hxU, hxside⟩
    constructor
    · apply (mem_reflectedDirectedSide_plB4_puncturedRay sigma _).2
      simpa [reflectedIntervalMap_plB4, centralReflection_plB4] using horiginal.1
    · apply (movesAway_reflectedDirectedSide_plB4 sigma _ _).2
      simpa [reflectedIntervalMap_plB4, centralReflection_plB4] using horiginal.2

private theorem carries_reflectedDirectedSide_plB4
    {F : IntervalMap} {sigma tau : DirectedSide}
    (hcarry : CarriesDirectedSidePLCore F sigma tau) :
    CarriesDirectedSidePLCore (reflectedIntervalMap_plB4 F)
      (reflectedDirectedSide_plB4 sigma) (reflectedDirectedSide_plB4 tau) := by
  rcases hcarry with ⟨hbase, U, hUopen, hbaseU, hside, hmaps⟩
  constructor
  · change unitInterval.symm (F (unitInterval.symm
        (reflectedDirectedSide_plB4 sigma).base)) =
      (reflectedDirectedSide_plB4 tau).base
    simp only [reflectedDirectedSide_plB4_base, unitInterval.symm_symm]
    rw [hbase]
  · let U' : Set I := unitInterval.symm ⁻¹' U
    have hU'open : IsOpen U' :=
      hUopen.preimage unitInterval.continuous_symm
    have hbaseU' : (reflectedDirectedSide_plB4 sigma).base ∈ U' := by
      change unitInterval.symm (reflectedDirectedSide_plB4 sigma).base ∈ U
      simpa using hbaseU
    have hside' : (U' ∩
        (reflectedDirectedSide_plB4 sigma).direction.puncturedRay
          (reflectedDirectedSide_plB4 sigma).base).Nonempty := by
      rcases hside with ⟨x, hxU, hxside⟩
      refine ⟨unitInterval.symm x, ?_, ?_⟩
      · simpa [U'] using hxU
      · apply (mem_reflectedDirectedSide_plB4_puncturedRay sigma _).2
        simpa using hxside
    refine ⟨U', hU'open, hbaseU', hside', ?_⟩
    intro x hx
    apply (mem_reflectedDirectedSide_plB4_puncturedRay tau _).2
    have himage := hmaps ⟨hx.1,
      (mem_reflectedDirectedSide_plB4_puncturedRay sigma x).1 hx.2⟩
    simpa [reflectedIntervalMap_plB4, centralReflection_plB4] using himage

/-- A continuous factor of a finite-PL repelling germ selects a unique
target side, conjugates the repelling germ onto that side, and its
complementary factor carries that target side back. -/
private theorem factor_maps_repellingDirectedState_plCore
    {W F H : IntervalMap}
    (hW : FinitePiecePL W) (hF : Continuous F)
    (hfactor : H ∘ F = W) (hcommute : Commute F W)
    {sigma : DirectedSide} (hsigma : IsRepellingDirectedStatePLCore W sigma) :
    ∃ tau : DirectedSide,
      IsRepellingDirectedStatePLCore W tau ∧
      CarriesDirectedSidePLCore F sigma tau ∧
        CarriesDirectedSidePLCore H tau sigma := by
  cases sigma with
  | mk base direction available =>
      cases direction with
      | right =>
          have hp : base < rightEndpoint := by
            rcases available with ⟨x, hx⟩
            exact hx.trans_le x.property.2
          have hrep' :
              IsRepellingDirectedStatePLCore W
                (rightDirectedSide base hp) := by
            simpa [rightDirectedSide] using hsigma
          obtain ⟨tau, htau, hFcarry, hHcarry⟩ :=
            factor_maps_repellingRightState_plCore hW hF hfactor hcommute hrep'
          refine ⟨tau, htau, ?_, ?_⟩
          · simpa [rightDirectedSide] using hFcarry
          · simpa [rightDirectedSide] using hHcarry
      | left =>
          have hp : leftEndpoint < base := by
            rcases available with ⟨x, hx⟩
            exact x.property.1.trans_lt hx
          have hrepLeft :
              IsRepellingDirectedStatePLCore W
                (leftDirectedSide base hp) := by
            simpa [leftDirectedSide] using hsigma
          let W' : IntervalMap := reflectedIntervalMap_plB4 W
          let F' : IntervalMap := reflectedIntervalMap_plB4 F
          let H' : IntervalMap := reflectedIntervalMap_plB4 H
          have hW' : FinitePiecePL W' :=
            finitePiecePL_reflectedIntervalMap_plB4 hW
          have hF' : Continuous F' := by
            exact unitInterval.continuous_symm.comp
              (hF.comp unitInterval.continuous_symm)
          have hfactor' : H' ∘ F' = W' := by
            calc
              H' ∘ F' = reflectedIntervalMap_plB4 (H ∘ F) := by
                exact (reflectedIntervalMap_plB4_comp H F).symm
              _ = W' := congrArg reflectedIntervalMap_plB4 hfactor
          have hcommute' : Commute F' W' := by
            intro x
            dsimp [F', W']
            simp only [reflectedIntervalMap_plB4_apply,
              unitInterval.symm_symm]
            exact congrArg unitInterval.symm
              (hcommute (unitInterval.symm x))
          have hp' : unitInterval.symm base < rightEndpoint := by
            have h := unitInterval.strictAnti_symm hp
            simpa [leftEndpoint, rightEndpoint] using h
          have hrepRight' : IsRepellingDirectedStatePLCore W'
              (rightDirectedSide (unitInterval.symm base) hp') := by
            have hreflected :=
              repelling_reflectedDirectedSide_plB4 hrepLeft
            simpa [reflectedDirectedSide_plB4, leftDirectedSide,
              rightDirectedSide, W'] using hreflected
          obtain ⟨tau', htau', hFcarry', hHcarry'⟩ :=
            factor_maps_repellingRightState_plCore hW' hF' hfactor'
              hcommute' hrepRight'
          let tau := reflectedDirectedSide_plB4 tau'
          have htau : IsRepellingDirectedStatePLCore W tau := by
            have h := repelling_reflectedDirectedSide_plB4 htau'
            rw [show reflectedIntervalMap_plB4 W' = W by
              exact reflectedIntervalMap_plB4_involutive W] at h
            exact h
          have hFcarry : CarriesDirectedSidePLCore F
              (leftDirectedSide base hp) tau := by
            have h := carries_reflectedDirectedSide_plB4 hFcarry'
            rw [show reflectedIntervalMap_plB4 F' = F by
              exact reflectedIntervalMap_plB4_involutive F] at h
            simpa [tau, reflectedDirectedSide_plB4, leftDirectedSide,
              rightDirectedSide] using h
          have hHcarry : CarriesDirectedSidePLCore H tau
              (leftDirectedSide base hp) := by
            have h := carries_reflectedDirectedSide_plB4 hHcarry'
            rw [show reflectedIntervalMap_plB4 H' = H by
              exact reflectedIntervalMap_plB4_involutive H] at h
            simpa [tau, reflectedDirectedSide_plB4, leftDirectedSide,
              rightDirectedSide] using h
          refine ⟨tau, htau, ?_, ?_⟩
          · simpa [leftDirectedSide] using hFcarry
          · simpa [leftDirectedSide] using hHcarry

private theorem carriesDirectedSide_target_unique_plCore
    {F : IntervalMap} {sigma tau upsilon : DirectedSide}
    (htau : CarriesDirectedSidePLCore F sigma tau)
    (hupsilon : CarriesDirectedSidePLCore F sigma upsilon) :
    tau = upsilon := by
  rcases htau with ⟨hbaseTau, U, hUopen, hbaseU, _hsideU, hmapsU⟩
  rcases hupsilon with
    ⟨hbaseUpsilon, V, hVopen, hbaseV, _hsideV, hmapsV⟩
  have hbase : tau.base = upsilon.base :=
    hbaseTau.symm.trans hbaseUpsilon
  have hsource : ∃ x : I,
      x ∈ U ∩ V ∧ x ∈ sigma.direction.puncturedRay sigma.base := by
    have hbaseUV : sigma.base ∈ U ∩ V := ⟨hbaseU, hbaseV⟩
    rcases sigma.available with ⟨z, hz⟩
    cases hsigmaDirection : sigma.direction with
    | left =>
        have hz' : z < sigma.base := by
          simpa [hsigmaDirection, Side.puncturedRay] using hz
        obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds'
          ((hUopen.inter hVopen).mem_nhds hbaseUV) hz'
        obtain ⟨x, hlx, hxs⟩ := exists_between hl.2
        refine ⟨x, hsub ⟨hlx, hxs.le⟩, ?_⟩
        simpa [hsigmaDirection, Side.puncturedRay] using hxs
    | right =>
        have hz' : sigma.base < z := by
          simpa [hsigmaDirection, Side.puncturedRay] using hz
        obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds'
          ((hUopen.inter hVopen).mem_nhds hbaseUV) hz'
        obtain ⟨x, hsx, hxu⟩ := exists_between hu.1
        refine ⟨x, hsub ⟨hsx.le, hxu⟩, ?_⟩
        simpa [hsigmaDirection, Side.puncturedRay] using hsx
  obtain ⟨x, hxUV, hxside⟩ := hsource
  have hFxTau := hmapsU ⟨hxUV.1, hxside⟩
  have hFxUpsilon := hmapsV ⟨hxUV.2, hxside⟩
  have hdirection : tau.direction = upsilon.direction := by
    cases ht : tau.direction <;> cases hu : upsilon.direction
    · rfl
    · have hleft : F x < tau.base := by
        simpa [ht, Side.puncturedRay] using hFxTau
      have hright : upsilon.base < F x := by
        simpa [hu, Side.puncturedRay] using hFxUpsilon
      rw [← hbase] at hright
      exact (not_lt_of_ge hright.le hleft).elim
    · have hright : tau.base < F x := by
        simpa [ht, Side.puncturedRay] using hFxTau
      have hleft : F x < upsilon.base := by
        simpa [hu, Side.puncturedRay] using hFxUpsilon
      rw [← hbase] at hleft
      exact (not_lt_of_ge hright.le hleft).elim
    · rfl
  cases tau with
  | mk tauBase tauDirection tauAvailable =>
      cases upsilon with
      | mk upsilonBase upsilonDirection upsilonAvailable =>
          simp only [DirectedSide.mk.injEq] at hbase hdirection ⊢
          exact ⟨hbase, hdirection⟩

private theorem factor_permutes_repellingDirectedStates_plCore
    {W F H : IntervalMap}
    (hW : FinitePiecePL W) (hF : Continuous F)
    (hfactor : H ∘ F = W) (hcommute : Commute F W)
    (hfinite : (repellingDirectedStatesPLCore W).Finite) :
    PermutesRepellingDirectedStatesPLCore F W := by
  classical
  letI : Fintype {sigma // IsRepellingDirectedStatePLCore W sigma} :=
    hfinite.fintype
  let target (sigma : {sigma // IsRepellingDirectedStatePLCore W sigma}) :
      DirectedSide :=
    Classical.choose
      (factor_maps_repellingDirectedState_plCore hW hF hfactor hcommute sigma.2)
  have htarget (sigma : {sigma // IsRepellingDirectedStatePLCore W sigma}) :
      IsRepellingDirectedStatePLCore W (target sigma) ∧
      CarriesDirectedSidePLCore F sigma.1 (target sigma) ∧
      CarriesDirectedSidePLCore H (target sigma) sigma.1 :=
    Classical.choose_spec
      (factor_maps_repellingDirectedState_plCore hW hF hfactor hcommute sigma.2)
  let f : {sigma // IsRepellingDirectedStatePLCore W sigma} →
      {sigma // IsRepellingDirectedStatePLCore W sigma} :=
    fun sigma ↦ ⟨target sigma, (htarget sigma).1⟩
  have hFcarry (sigma : {sigma // IsRepellingDirectedStatePLCore W sigma}) :
      CarriesDirectedSidePLCore F sigma.1 (f sigma).1 :=
    (htarget sigma).2.1
  have hHcarry (sigma : {sigma // IsRepellingDirectedStatePLCore W sigma}) :
      CarriesDirectedSidePLCore H (f sigma).1 sigma.1 :=
    (htarget sigma).2.2
  have hfinjective : Function.Injective f := by
    intro sigma rho heq
    apply Subtype.ext
    have htargetEq : (f sigma).1 = (f rho).1 :=
      congrArg Subtype.val heq
    have hHcarryRho : CarriesDirectedSidePLCore H (f sigma).1 rho.1 := by
      rw [htargetEq]
      exact hHcarry rho
    exact carriesDirectedSide_target_unique_plCore
      (hHcarry sigma) hHcarryRho
  have hfbijective : Function.Bijective f :=
    ⟨hfinjective, Finite.surjective_of_injective hfinjective⟩
  let e := Equiv.ofBijective f hfbijective
  refine ⟨e, ?_⟩
  intro sigma
  exact hFcarry sigma

private theorem piecewiseLinear_generators_permute_repellingStates
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    PermutesRepellingDirectedStatesPLCore G.P G.W ∧
      PermutesRepellingDirectedStatesPLCore G.Q G.W := by
  have hWform : G.W = (G.P^[2]) ∘ (G.Q^[2]) := by
    simpa [PiecewiseLinearSelectedFixedGap.W,
      PiecewiseLinearSelectedFixedGap.P,
      PiecewiseLinearSelectedFixedGap.Q,
      LeastNormalizedPiecewiseLinearCounterexample.W,
      LeastNormalizedPiecewiseLinearCounterexample.P,
      LeastNormalizedPiecewiseLinearCounterexample.Q,
      NormalizedPiecewiseLinearCounterexample.W,
      piecewiseLinearW, iterateMap] using
        G.system.commute.comp_iterate 2
  have hWPL : FinitePiecePL G.W := by
    change FinitePiecePL (iterateMap (G.P ∘ G.Q) 2)
    exact finitePiecePL_iterate
      (finitePiecePL_comp G.system.finitePieceP G.system.finitePieceQ) 2
  have hfixedFinite : (fixedPoints G.W).Finite := by
    have hset : fixedPoints G.W =
        (G.system.base.fixedW : Set I) := by
      ext x
      simpa [PiecewiseLinearSelectedFixedGap.W,
        LeastNormalizedPiecewiseLinearCounterexample.W] using
        (G.system.base.fixedW_spec x).symm
    rw [hset]
    exact G.system.base.fixedW.finite_toSet
  have hstatesFinite : (repellingDirectedStatesPLCore G.W).Finite :=
    repellingDirectedStatesPLCore_finite hfixedFinite
  let HP : IntervalMap := (G.P^[1]) ∘ (G.Q^[2])
  have hfactorP : HP ∘ G.P = G.W := by
    funext x
    calc
      (HP ∘ G.P) x = G.P ((G.Q^[2]) (G.P x)) := by
        simp [HP]
      _ = G.P (G.P ((G.Q^[2]) x)) :=
        congrArg G.P ((G.system.commute.iterate_right 2 x).symm)
      _ = ((G.P^[2]) ∘ (G.Q^[2])) x := by
        simp [Function.iterate_succ_apply']
      _ = G.W x := congrFun hWform.symm x
  have hPcommutesW : Commute G.P G.W := by
    have hPcommutesPQ : Commute G.P (G.P ∘ G.Q) :=
      (Function.Commute.refl G.P).comp_right G.system.commute
    change Commute G.P (iterateMap (G.P ∘ G.Q) 2)
    exact hPcommutesPQ.iterate_right 2
  have hpermP : PermutesRepellingDirectedStatesPLCore G.P G.W :=
    factor_permutes_repellingDirectedStates_plCore hWPL
      G.system.continuousP hfactorP hPcommutesW hstatesFinite
  let HQ : IntervalMap := (G.P^[2]) ∘ (G.Q^[1])
  have hfactorQ : HQ ∘ G.Q = G.W := by
    funext x
    calc
      (HQ ∘ G.Q) x = (G.P^[2]) ((G.Q^[2]) x) := by
        simp [HQ, Function.iterate_succ_apply']
      _ = G.W x := congrFun hWform.symm x
  have hQcommutesW : Commute G.Q G.W := by
    have hQcommutesPQ : Commute G.Q (G.P ∘ G.Q) :=
      G.system.commute.symm.comp_right (Function.Commute.refl G.Q)
    change Commute G.Q (iterateMap (G.P ∘ G.Q) 2)
    exact hQcommutesPQ.iterate_right 2
  have hpermQ : PermutesRepellingDirectedStatesPLCore G.Q G.W :=
    factor_permutes_repellingDirectedStates_plCore hWPL
      G.system.continuousQ hfactorQ hQcommutesW hstatesFinite
  exact ⟨hpermP, hpermQ⟩

private theorem open_puncturedSide_nonempty_plCore
    (sigma : DirectedSide) {U : Set I}
    (hUopen : IsOpen U) (hbase : sigma.base ∈ U) :
    (U ∩ sigma.direction.puncturedRay sigma.base).Nonempty := by
  rcases sigma.available with ⟨z, hz⟩
  cases hdirection : sigma.direction with
  | left =>
      have hz' : z < sigma.base := by
        simpa [hdirection, Side.puncturedRay] using hz
      obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds'
        (hUopen.mem_nhds hbase) hz'
      obtain ⟨x, hlx, hxb⟩ := exists_between hl.2
      refine ⟨x, hsub ⟨hlx, hxb.le⟩, ?_⟩
      simpa [hdirection, Side.puncturedRay] using hxb
  | right =>
      have hz' : sigma.base < z := by
        simpa [hdirection, Side.puncturedRay] using hz
      obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds'
        (hUopen.mem_nhds hbase) hz'
      obtain ⟨x, hbx, hxu⟩ := exists_between hu.1
      refine ⟨x, hsub ⟨hbx.le, hxu⟩, ?_⟩
      simpa [hdirection, Side.puncturedRay] using hbx

private theorem carriesDirectedSide_id_plCore (sigma : DirectedSide) :
    CarriesDirectedSidePLCore id sigma sigma := by
  refine ⟨rfl, Set.univ, isOpen_univ, Set.mem_univ _, ?_, ?_⟩
  · simpa using sigma.available
  · intro x hx
    exact hx.2

private theorem carriesDirectedSide_comp_plCore
    {F G : IntervalMap} {sigma tau upsilon : DirectedSide}
    (hFcont : Continuous F)
    (hF : CarriesDirectedSidePLCore F sigma tau)
    (hG : CarriesDirectedSidePLCore G tau upsilon) :
    CarriesDirectedSidePLCore (G ∘ F) sigma upsilon := by
  rcases hF with ⟨hFbase, U, hUopen, hbaseU, _hsideU, hFmaps⟩
  rcases hG with ⟨hGbase, V, hVopen, hbaseV, _hsideV, hGmaps⟩
  constructor
  · change G (F sigma.base) = upsilon.base
    rw [hFbase, hGbase]
  · let S : Set I := U ∩ F ⁻¹' V
    have hSopen : IsOpen S := hUopen.inter (hVopen.preimage hFcont)
    have hbaseS : sigma.base ∈ S := ⟨hbaseU, by
      change F sigma.base ∈ V
      rw [hFbase]
      exact hbaseV⟩
    refine ⟨S, hSopen, hbaseS,
      open_puncturedSide_nonempty_plCore sigma hSopen hbaseS, ?_⟩
    intro x hx
    have hFxTau := hFmaps ⟨hx.1.1, hx.2⟩
    exact hGmaps ⟨hx.1.2, hFxTau⟩

private theorem permutesRepelling_carries_pow_plCore
    {F W : IntervalMap} (hFcont : Continuous F)
    (e : {sigma // IsRepellingDirectedStatePLCore W sigma} ≃
      {sigma // IsRepellingDirectedStatePLCore W sigma})
    (hphysical : ∀ sigma,
      CarriesDirectedSidePLCore F sigma.1 (e sigma).1)
    (n : ℕ) (sigma : {sigma // IsRepellingDirectedStatePLCore W sigma}) :
    CarriesDirectedSidePLCore (F^[n]) sigma.1 ((e ^ n) sigma).1 := by
  induction n with
  | zero => simpa using carriesDirectedSide_id_plCore sigma.1
  | succ n ih =>
      have hnext := carriesDirectedSide_comp_plCore (hFcont.iterate n) ih
        (hphysical ((e ^ n) sigma))
      rw [Function.iterate_succ']
      simpa [pow_succ'] using hnext

private theorem canonicalExponent_carries_repellingState_plCore
    {F W : IntervalMap} (fixedW : Finset I)
    (hmem : ∀ x : I, x ∈ fixedW ↔ IsFixedPoint W x)
    (hFcont : Continuous F)
    (hperm : PermutesRepellingDirectedStatesPLCore F W)
    {sigma : DirectedSide} (hsigma : IsRepellingDirectedStatePLCore W sigma) :
    CarriesDirectedSidePLCore
      (F^[2 * Nat.factorial (2 * fixedW.card)]) sigma sigma := by
  classical
  have hfixedSet : fixedPoints W = (fixedW : Set I) := by
    ext x
    exact (hmem x).symm
  have hfixedFinite : (fixedPoints W).Finite := by
    rw [hfixedSet]
    exact fixedW.finite_toSet
  have hstatesFinite : (repellingDirectedStatesPLCore W).Finite :=
    repellingDirectedStatesPLCore_finite hfixedFinite
  letI : Fintype {sigma // IsRepellingDirectedStatePLCore W sigma} :=
    hstatesFinite.fintype
  let sideCode : Side → Bool
    | .left => false
    | .right => true
  have hsideCode : Function.Injective sideCode := by
    intro a b
    cases a <;> cases b <;> simp [sideCode]
  let encode : {sigma // IsRepellingDirectedStatePLCore W sigma} →
      {x // x ∈ fixedW} × Bool := fun sigma ↦
    (⟨sigma.1.base, (hmem sigma.1.base).2 sigma.2.1⟩,
      sideCode sigma.1.direction)
  have hencode : Function.Injective encode := by
    intro sigma tau h
    have hbase : sigma.1.base = tau.1.base :=
      congrArg (fun z ↦ ((z.1 : {x // x ∈ fixedW}) : I)) h
    have hdirection : sigma.1.direction = tau.1.direction :=
      hsideCode (congrArg Prod.snd h)
    apply Subtype.ext
    cases sigma with
    | mk sigma hsigma =>
      cases tau with
      | mk tau htau =>
        cases sigma
        cases tau
        simp_all
  have hcardLe : Fintype.card
      {sigma // IsRepellingDirectedStatePLCore W sigma} ≤
      2 * fixedW.card := by
    have h := Fintype.card_le_of_injective encode hencode
    simpa [Nat.mul_comm] using h
  obtain ⟨e, hphysical⟩ := hperm
  have heFactorial :
      e ^ Nat.factorial
          (Fintype.card {sigma // IsRepellingDirectedStatePLCore W sigma}) =
        1 := by
    rw [← Fintype.card_perm]
    exact pow_card_eq_one
  have hfactorialDvd :
      Nat.factorial
          (Fintype.card {sigma // IsRepellingDirectedStatePLCore W sigma}) ∣
        2 * Nat.factorial (2 * fixedW.card) := by
    apply dvd_mul_of_dvd_right
    exact Nat.factorial_dvd_factorial hcardLe
  obtain ⟨k, hk⟩ := hfactorialDvd
  have heReturn : e ^ (2 * Nat.factorial (2 * fixedW.card)) = 1 := by
    rw [hk, pow_mul, heFactorial, one_pow]
  let sigmaSub : {sigma // IsRepellingDirectedStatePLCore W sigma} :=
    ⟨sigma, hsigma⟩
  have hcarry := permutesRepelling_carries_pow_plCore hFcont e hphysical
    (2 * Nat.factorial (2 * fixedW.card)) sigmaSub
  rw [heReturn] at hcarry
  simpa [sigmaSub] using hcarry

private theorem repelling_carries_self_plCore
    {W : IntervalMap} {sigma : DirectedSide}
    (hrep : IsRepellingDirectedStatePLCore W sigma) :
    CarriesDirectedSidePLCore W sigma sigma := by
  rcases hrep with ⟨hfixed, U, hUopen, hbaseU, hside, haction⟩
  refine ⟨hfixed, U, hUopen, hbaseU, hside, ?_⟩
  intro x hx
  exact (haction x hx).1

private theorem piecewiseLinear_A_carries_selectedRight
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    CarriesDirectedSidePLCore G.A
      (rightDirectedSide G.p (G.p_lt_c.trans_le G.c.property.2))
      (rightDirectedSide G.p (G.p_lt_c.trans_le G.c.property.2)) := by
  have hperm :=
    (piecewiseLinear_generators_permute_repellingStates G).1
  have hcarry := canonicalExponent_carries_repellingState_plCore
    G.system.base.fixedW (by
      intro y
      simpa [PiecewiseLinearSelectedFixedGap.W,
        LeastNormalizedPiecewiseLinearCounterexample.W] using
        G.system.base.fixedW_spec y) G.system.continuousP hperm
      (piecewiseLinear_selectedGap_is_repelling G)
  simpa [PiecewiseLinearSelectedFixedGap.A,
    PiecewiseLinearSelectedFixedGap.P,
    LeastNormalizedPiecewiseLinearCounterexample.A,
    NormalizedPiecewiseLinearCounterexample.A,
    piecewiseLinearA, iterateMap] using hcarry

private theorem piecewiseLinear_B_carries_selectedRight
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    CarriesDirectedSidePLCore G.B
      (rightDirectedSide G.p (G.p_lt_c.trans_le G.c.property.2))
      (rightDirectedSide G.p (G.p_lt_c.trans_le G.c.property.2)) := by
  have hperm :=
    (piecewiseLinear_generators_permute_repellingStates G).2
  have hcarry := canonicalExponent_carries_repellingState_plCore
    G.system.base.fixedW (by
      intro y
      simpa [PiecewiseLinearSelectedFixedGap.W,
        LeastNormalizedPiecewiseLinearCounterexample.W] using
        G.system.base.fixedW_spec y) G.system.continuousQ hperm
      (piecewiseLinear_selectedGap_is_repelling G)
  simpa [PiecewiseLinearSelectedFixedGap.B,
    PiecewiseLinearSelectedFixedGap.Q,
    LeastNormalizedPiecewiseLinearCounterexample.B,
    NormalizedPiecewiseLinearCounterexample.B,
    piecewiseLinearB, iterateMap] using hcarry

/-- A finite-PL map that returns the available right side to itself has a
positive affine representative there, hence a right `C1+BV` germ. -/
private theorem finitePiecePL_rightGermC1BV_of_carries_right
    {T : IntervalMap} {p : I} {hp : p < rightEndpoint}
    (hT : FinitePiecePL T)
    (hcarry : CarriesDirectedSidePLCore T
      (rightDirectedSide p hp) (rightDirectedSide p hp)) :
    HasRightGermC1BV T p := by
  rcases hT.2 with ⟨partition, hpartition⟩
  obtain ⟨a, b, hab, hap, hpb⟩ :=
    partition.exists_adjacent_right_plCore p.property
      (lt_of_lt_of_le hp rightEndpoint.property.2)
  obtain ⟨m, c, hformula⟩ := hpartition hab
  rcases hcarry with ⟨hTp, V, hVopen, hpV, _hsideV, hmaps⟩
  obtain ⟨u, hu, hpu⟩ :=
    exists_Ico_subset_of_mem_nhds' (hVopen.mem_nhds hpV) hp
  obtain ⟨qReal, hpqReal, hqReal⟩ :=
    exists_between (lt_min hpb hu.1)
  have hqb : qReal < b := hqReal.trans_le (min_le_left _ _)
  have hqu : qReal < (u : ℝ) :=
    hqReal.trans_le (min_le_right _ _)
  let q : I := ⟨qReal, ⟨p.property.1.trans hpqReal.le,
    hqu.le.trans u.property.2⟩⟩
  have hpq : p < q := hpqReal
  have hpCell : p ∈ intervalCell a b := ⟨hap, hpb.le⟩
  have hqCell : q ∈ intervalCell a b :=
    ⟨hap.trans hpq.le, hqb.le⟩
  have hqV : q ∈ V := hpu ⟨hpq.le, hqu⟩
  have hqSide : q ∈
      (rightDirectedSide p hp).direction.puncturedRay p := by
    simpa [rightDirectedSide, Side.puncturedRay] using hpq
  have hTqSide := hmaps ⟨hqV, hqSide⟩
  have hTq : p < T q := by
    simpa [rightDirectedSide, Side.puncturedRay] using hTqSide
  have hTpReal : (T p : ℝ) = (p : ℝ) := congrArg Subtype.val hTp
  have hpformula := hformula p hpCell
  have hqformula := hformula q hqCell
  have hm : 0 < m := by
    have hpq' : (p : ℝ) < (q : ℝ) := hpq
    have hTq' : (p : ℝ) < (T q : ℝ) := hTq
    rw [hpformula] at hTpReal
    rw [hqformula] at hTq'
    nlinarith
  let affine : ℝ → ℝ := fun x ↦ m * x + c
  let g : RightGermC1Diffeomorphism T p :=
    { rightEnd := q
      base_lt_rightEnd := hpq
      extension := affine
      neighborhood := Set.univ
      isOpen_neighborhood := isOpen_univ
      segment_subset := by
        intro x hx
        exact Set.mem_univ x
      agrees := by
        intro x hx
        exact hformula x ⟨
          hap.trans (show (p : ℝ) ≤ (x : ℝ) from hx.1),
          (show (x : ℝ) ≤ (q : ℝ) from hx.2).trans hqb.le⟩
      contDiff_one := by
        change ContDiffOn ℝ 1 (fun x : ℝ ↦ m * x + c) Set.univ
        have hmC : ContDiff ℝ 1 (fun _ : ℝ ↦ m) := contDiff_const
        have hxC : ContDiff ℝ 1 (fun x : ℝ ↦ x) := contDiff_id
        have hcC : ContDiff ℝ 1 (fun _ : ℝ ↦ c) := contDiff_const
        exact ((hmC.mul hxC).add hcC).contDiffOn
      deriv_pos := by
        intro x hx
        simpa [affine] using hm }
  refine ⟨g, ?_⟩
  have himage :
      (g.logDeriv '' Set.Icc (p : ℝ) (q : ℝ)).Subsingleton := by
    rintro _ ⟨x, _hx, rfl⟩ _ ⟨y, _hy, rfl⟩
    simp [RightGermC1Diffeomorphism.logDeriv, g, affine]
  have hzero := eVariationOn.constant_on himage
  change eVariationOn g.logDeriv
      (Set.Icc (p : ℝ) (q : ℝ)) ≠ ⊤
  rw [hzero]
  exact ENNReal.zero_ne_top


/-- The selected affine branch of `W` is a right `C1+BV` germ. -/
theorem piecewiseLinear_W_hasRightGermC1BV
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    HasRightGermC1BV G.W G.p := by
  have hWPL : FinitePiecePL G.W := by
    change FinitePiecePL (iterateMap (G.P ∘ G.Q) 2)
    exact finitePiecePL_iterate
      (finitePiecePL_comp G.system.finitePieceP G.system.finitePieceQ) 2
  exact finitePiecePL_rightGermC1BV_of_carries_right hWPL
    (repelling_carries_self_plCore
      (piecewiseLinear_selectedGap_is_repelling G))

/-- The returned selected branch of `A` is orientation-preserving and
affine, hence a right `C1+BV` germ. -/
theorem piecewiseLinear_A_hasRightGermC1BV
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    HasRightGermC1BV G.A G.p := by
  have hAPL : FinitePiecePL G.A := by
    simpa [PiecewiseLinearSelectedFixedGap.A,
      PiecewiseLinearSelectedFixedGap.P,
      LeastNormalizedPiecewiseLinearCounterexample.A,
      NormalizedPiecewiseLinearCounterexample.A,
      piecewiseLinearA] using
        finitePiecePL_iterate G.system.finitePieceP
          (piecewiseLinearNormalizationExponent G.system.base.fixedW)
  exact finitePiecePL_rightGermC1BV_of_carries_right hAPL
    (piecewiseLinear_A_carries_selectedRight G)

/-- The returned selected branch of `B` is orientation-preserving and
affine, hence a right `C1+BV` germ. -/
theorem piecewiseLinear_B_hasRightGermC1BV
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    HasRightGermC1BV G.B G.p := by
  have hBPL : FinitePiecePL G.B := by
    simpa [PiecewiseLinearSelectedFixedGap.B,
      PiecewiseLinearSelectedFixedGap.Q,
      LeastNormalizedPiecewiseLinearCounterexample.B,
      NormalizedPiecewiseLinearCounterexample.B,
      piecewiseLinearB] using
        finitePiecePL_iterate G.system.finitePieceQ
          (piecewiseLinearNormalizationExponent G.system.base.fixedW)
  exact finitePiecePL_rightGermC1BV_of_carries_right hBPL
    (piecewiseLinear_B_carries_selectedRight G)

/-- Boundary 4: the finite directed-state permutation and affine right-germ
calculation. -/
theorem piecewiseLinear_directedStateReturn
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    PiecewiseLinearDirectedReturnData G := by
  exact
    { fixed_A_p := piecewiseLinear_return_fixes_A_p G
      fixed_A_c := piecewiseLinear_return_fixes_A_c G
      fixed_B_p := piecewiseLinear_return_fixes_B_p G
      fixed_B_c := piecewiseLinear_return_fixes_B_c G
      right_germ_W := piecewiseLinear_W_hasRightGermC1BV G
      right_germ_A := piecewiseLinear_A_hasRightGermC1BV G
      right_germ_B := piecewiseLinear_B_hasRightGermC1BV G }

/-- Finite arrival of the selected returned gap. -/
def HasFiniteSelectedGapCover
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop :=
  ∃ N : ℕ, iterateMap G.R N '' Set.Icc G.p G.c = Set.univ

/-- Local eventual onto on every nondegenerate interval on the selected
side. -/
def HasLocalEventualOntoPL (W : IntervalMap) (p : I) : Prop :=
  ∀ q : I, p < q →
    ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ

/-- The exact finite-arrival output consumed by orbit globalization. -/
structure PreparedPiecewiseLinearCounterexample
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop where
  finite_arrival : HasFiniteSelectedGapCover G
  local_eventual_onto : HasLocalEventualOntoPL G.W G.p

/-- A phase image of a compact set under the original, unreturned maps. -/
def piecewiseLinearPhaseSet
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (C : Set I) (i j : ℕ) : Set I :=
  iterateMap G.P i '' (iterateMap G.Q j '' C)

/-- Translation of phase labels preserves the phase-intersection graph. -/
def HasVertexTransitivePhaseIntersections
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop :=
  ∀ (C : Set I), G.A '' C = C → G.B '' C = C →
    ∀ i j k l u v : ℕ,
      ((piecewiseLinearPhaseSet G C i j ∩
          piecewiseLinearPhaseSet G C k l).Nonempty ↔
        (piecewiseLinearPhaseSet G C
            ((i + u) % G.L) ((j + v) % G.L) ∩
          piecewiseLinearPhaseSet G C
            ((k + u) % G.L) ((l + v) % G.L)).Nonempty)

/-- The returned diagonal images of the selected gap have dense union. -/
def HasDenseDiagonalSelectedGapCover
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop :=
  Dense (⋃ n : ℕ, iterateMap G.R n '' Set.Icc G.p G.c)

/-- A specific ambient endpoint remains absent from every finite diagonal
image, while the return square fixes it with singleton fibre.  Retaining the
missing-endpoint provenance is essential: singleton fibre alone does not
imply that an endpoint is locally attracting. -/
structure PiecewiseLinearAsymptoticEndpointObstruction
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) where
  endpoint : I
  ambient_endpoint : PLFiniteArrivalSupport.IsAmbientEndpoint endpoint
  never_arrives : ∀ n : ℕ,
    endpoint ∉ iterateMap G.R n '' Set.Icc G.p G.c
  fixed : G.S endpoint = endpoint
  singleton_fibre : ∀ x : I, G.S x = endpoint → x = endpoint

/-- Both ambient endpoints occur, possibly at different finite diagonal
stages. -/
def HasFiniteAmbientEndpointArrival
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop :=
  ∃ n0 n1 : ℕ,
    leftEndpoint ∈ iterateMap G.R n0 '' Set.Icc G.p G.c ∧
      rightEndpoint ∈ iterateMap G.R n1 '' Set.Icc G.p G.c

/-- The selected terminal endpoint is genuinely internal. -/
def HasInternalSelectedTerminalGap
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop :=
  G.c < rightEndpoint

/-- Returned endpoint fixing makes the selected gap expand under both
returned factors. -/
theorem piecewiseLinear_selectedGap_expands_under_returns
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_D : PiecewiseLinearDirectedReturnData G) :
    Set.Icc G.p G.c ⊆ G.A '' Set.Icc G.p G.c ∧
      Set.Icc G.p G.c ⊆ G.B '' Set.Icc G.p G.c := by
  have hAcont : Continuous G.A := by
    exact G.system.continuousP.iterate G.L
  have hBcont : Continuous G.B := by
    exact G.system.continuousQ.iterate G.L
  exact ⟨
    PLFiniteArrivalSupport.gap_subset_image_of_fixed_endpoints
      G.p_lt_c.le hAcont _D.fixed_A_p _D.fixed_A_c,
    PLFiniteArrivalSupport.gap_subset_image_of_fixed_endpoints
      G.p_lt_c.le hBcont _D.fixed_B_p _D.fixed_B_c⟩

/-- Applying `P` or `Q` to an intersection and then returning with the
complementary `L-1` iterate proves vertex transitivity without injectivity. -/
theorem piecewiseLinear_phaseIntersections_vertexTransitive
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    HasVertexTransitivePhaseIntersections G := by
  intro C hAperiodic hBperiodic i j k l u v
  have hL : 0 < G.L := by
    exact piecewiseLinearNormalizationExponent_pos G.system.base.fixedW
  have hcomm : Commute G.P G.Q := G.system.commute
  let D : PLFiniteArrivalSupport.PhaseLabel G.L → Set I :=
    PLFiniteArrivalSupport.labelledPhaseInterval G.P G.Q G.L C
  have hphase (a b : ℕ) :
      piecewiseLinearPhaseSet G C a b =
        D ((a : ZMod G.L), (b : ZMod G.L)) := by
    exact PLFiniteArrivalSupport.naturalPhase_eq_labelledPhase
      hL C hcomm hAperiodic hBperiodic a b
  let α : PLFiniteArrivalSupport.PhaseLabel G.L :=
    ((i : ZMod G.L), (j : ZMod G.L))
  let β : PLFiniteArrivalSupport.PhaseLabel G.L :=
    ((k : ZMod G.L), (l : ZMod G.L))
  let τ := PLFiniteArrivalSupport.phaseTranslation G.L u v
  have hauto :
      PLFiniteArrivalSupport.IsIntervalIntersectionGraphAutomorphism D τ := by
    exact PLFiniteArrivalSupport.phaseTranslation_graphAutomorphism
      hL C hcomm hAperiodic hBperiodic u v
  have hgoal : (D α ∩ D β).Nonempty ↔
      (D (τ α) ∩ D (τ β)).Nonempty := by
    by_cases hαβ : α = β
    · have hiff := (PLFiniteArrivalSupport.labelledPhaseInterval_nonempty_iff
        G.P G.Q G.L C α).trans
          (PLFiniteArrivalSupport.labelledPhaseInterval_nonempty_iff
            G.P G.Q G.L C (τ α)).symm
      simpa only [hαβ, Set.inter_self] using hiff
    · have hadj := hauto α β
      rw [PLFiniteArrivalSupport.intervalIntersectionAdjacent,
        PLFiniteArrivalSupport.intervalIntersectionAdjacent] at hadj
      have hτne : τ α ≠ τ β := fun h => hαβ (τ.injective h)
      simpa [hαβ, hτne] using hadj.symm
  rw [hphase, hphase, hphase, hphase]
  simpa [α, β, τ, PLFiniteArrivalSupport.phaseTranslation] using hgoal

/-! ### B5 normalization callback: no respected fixed-point-identifying quotient -/

private theorem descendedMap_onto_b5Prototype
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hrespect : RespectsFibres π.toFun T)
    (honto : IsOnto T) :
    IsOnto (descendedMap π T hrespect) := by
  intro y
  obtain ⟨x, hx⟩ := π.surjective_toFun y
  obtain ⟨z, hz⟩ := honto x
  refine ⟨π z, ?_⟩
  rw [← intertwines_descendedMap π T hrespect z, hz, hx]

private theorem invariantInterval_preimage_b5Prototype
    {α : Type*}
    (π : CanonicalFiniteIntervalQuotient)
    (F Fbar : α → IntervalMap)
    (hdescend : ∀ a, Intertwines π.toFun (F a) (Fbar a))
    (Jbar : ClosedSubinterval)
    (hinvariant : ∀ a, IsForwardInvariant (Fbar a) Jbar) :
    ∃ J : ClosedSubinterval,
      J.carrier = π.toFun ⁻¹' Jbar.carrier ∧
        ∀ a, IsForwardInvariant (F a) J := by
  let S : Set I := π.toFun ⁻¹' Jbar.carrier
  have hSnonempty : S.Nonempty := by
    obtain ⟨x, hx⟩ := π.surjective_toFun Jbar.left
    refine ⟨x, ?_⟩
    change π x ∈ Set.Icc Jbar.left Jbar.right
    rw [hx]
    exact Set.left_mem_Icc.mpr Jbar.left_le_right
  have hSclosed : IsClosed S :=
    isClosed_Icc.preimage π.continuous_toFun
  have hScompact : IsCompact S :=
    isCompact_univ.of_isClosed_subset hSclosed (Set.subset_univ S)
  have hSord : Set.OrdConnected S :=
    Set.ordConnected_Icc.preimage_mono π.monotone_toFun
  have hSconnected : IsConnected S :=
    ⟨hSnonempty, hSord.isPreconnected⟩
  have hSeq : S = Set.Icc (sInf S) (sSup S) :=
    eq_Icc_of_connected_compact hSconnected hScompact
  have hle : sInf S ≤ sSup S := by
    rw [hSeq] at hSnonempty
    exact Set.nonempty_Icc.mp hSnonempty
  let J : ClosedSubinterval :=
    { left := sInf S, right := sSup S, left_le_right := hle }
  refine ⟨J, ?_, ?_⟩
  · exact hSeq.symm
  · intro a x hx
    have hxS : x ∈ S := by
      rw [hSeq]
      exact hx
    have hbar : Fbar a (π x) ∈ Jbar.carrier := hinvariant a hxS
    have hπ : π (F a x) = Fbar a (π x) := hdescend a x
    have hFaS : F a x ∈ S := by
      change π (F a x) ∈ Jbar.carrier
      rwa [hπ]
    rw [hSeq] at hFaS
    exact hFaS

private theorem fixedPoints_descendedMap_exact_continuous_b5Prototype
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hT : Continuous T) (hrespect : RespectsFibres π.toFun T) :
    FixedPointsDescendExactly π.toFun T (descendedMap π T hrespect) := by
  ext y
  constructor
  · intro hy
    change descendedMap π T hrespect y = y at hy
    obtain ⟨x, hx⟩ := π.surjective_toFun y
    have hπTx : π (T x) = y := by
      rw [intertwines_descendedMap π T hrespect x, hx, hy]
    by_cases hcollapsed : x ∈ π.collapsedSet
    · rcases Set.mem_iUnion.mp hcollapsed with ⟨i, hxi⟩
      let J := π.collapsed i
      have hπleft : π J.left = y := by
        rw [← hx]
        exact (π.fibre_iff J.left x).mpr
          (Or.inr ⟨i, Set.left_mem_Icc.mpr J.left_le_right, hxi⟩)
      have hmaps : MapsTo T J.carrier J.carrier := by
        intro z hz
        have hπz : π z = y := by
          rw [← hπleft]
          exact (π.fibre_iff z J.left).mpr
            (Or.inr ⟨i, hz, Set.left_mem_Icc.mpr J.left_le_right⟩)
        have hπTz : π (T z) = y := by
          rw [intertwines_descendedMap π T hrespect z, hπz, hy]
        have hmem : T z ∈ π.fibre J.left := by
          change π (T z) = π J.left
          exact hπTz.trans hπleft.symm
        simpa [J, π.fibre_eq_collapsed i] using hmem
      obtain ⟨z, hz, hzfix⟩ :=
        exists_mem_Icc_isFixedPt_of_mapsTo
          hT.continuousOn J.left_le_right hmaps
      refine ⟨z, hzfix, ?_⟩
      rw [← hπleft]
      exact (π.fibre_iff z J.left).mpr
        (Or.inr ⟨i, hz, Set.left_mem_Icc.mpr J.left_le_right⟩)
    · have hsingle := π.fibre_eq_singleton_of_isUncollapsed hcollapsed
      have hTxmem : T x ∈ π.fibre x := hπTx.trans hx.symm
      rw [hsingle, Set.mem_singleton_iff] at hTxmem
      exact ⟨x, hTxmem, hx⟩
  · rintro ⟨x, hxfix, rfl⟩
    change descendedMap π T hrespect (π x) = π x
    rw [← intertwines_descendedMap π T hrespect x, hxfix]

private theorem intertwines_comp_b5Prototype
    {π F G Fbar Gbar : IntervalMap}
    (hF : Intertwines π F Fbar) (hG : Intertwines π G Gbar) :
    Intertwines π (F ∘ G) (Fbar ∘ Gbar) := by
  intro x
  change π (F (G x)) = Fbar (Gbar (π x))
  rw [hF (G x), hG x]

private theorem intertwines_iterateMap_b5Prototype
    {π T Tbar : IntervalMap} (h : Intertwines π T Tbar) (n : ℕ) :
    Intertwines π (iterateMap T n) (iterateMap Tbar n) := by
  intro x
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      calc
        π (iterateMap T n.succ x) = π (T (iterateMap T n x)) := by
          simp only [iterateMap, Function.iterate_succ_apply']
        _ = Tbar (π (iterateMap T n x)) := h (iterateMap T n x)
        _ = Tbar (iterateMap Tbar n (π x)) := congrArg Tbar (ih x)
        _ = iterateMap Tbar n.succ (π x) := by
          simp only [iterateMap, Function.iterate_succ_apply']

private theorem intertwines_positiveWordMap_b5Prototype
    {π P Q Pbar Qbar : IntervalMap}
    (hP : Intertwines π P Pbar) (hQ : Intertwines π Q Qbar)
    (r s : ℕ) :
    Intertwines π (positiveWordMap P Q r s)
      (positiveWordMap Pbar Qbar r s) := by
  have hPr := intertwines_iterateMap_b5Prototype hP r
  have hQs := intertwines_iterateMap_b5Prototype hQ s
  intro x
  calc
    π (positiveWordMap P Q r s x) =
        iterateMap Pbar r (π (iterateMap Q s x)) := hPr (iterateMap Q s x)
    _ = iterateMap Pbar r (iterateMap Qbar s (π x)) :=
      congrArg (iterateMap Pbar r) (hQs x)
    _ = positiveWordMap Pbar Qbar r s (π x) := rfl

private theorem respectsFibres_of_intertwines_b5Prototype
    {π T Tbar : IntervalMap} (h : Intertwines π T Tbar) :
    RespectsFibres π T := by
  intro x y hxy
  rw [h x, h y, hxy]

private theorem exists_descendedMinimalPiecewiseLinearCounterexample_b5Prototype
    (C : MinimalPiecewiseLinearCounterexample)
    (π : CanonicalFiniteIntervalQuotient)
    (hrespectP : RespectsFibres π.toFun C.base.P)
    (hrespectQ : RespectsFibres π.toFun C.base.Q) :
    ∃ D : MinimalPiecewiseLinearCounterexample,
      Intertwines π.toFun C.base.P D.base.P ∧
        Intertwines π.toFun C.base.Q D.base.Q := by
  let Pbar := descendedMap π C.base.P hrespectP
  let Qbar := descendedMap π C.base.Q hrespectQ
  have hdescP : Intertwines π.toFun C.base.P Pbar :=
    intertwines_descendedMap π C.base.P hrespectP
  have hdescQ : Intertwines π.toFun C.base.Q Qbar :=
    intertwines_descendedMap π C.base.Q hrespectQ
  have hminimalBar : ∀ J : ClosedSubinterval,
      IsCommonInvariantCore Pbar Qbar J → J.carrier = Set.univ := by
    intro J hJ
    let F : Bool → IntervalMap := fun b => if b then C.base.P else C.base.Q
    let Fbar : Bool → IntervalMap := fun b => if b then Pbar else Qbar
    have hdesc : ∀ b, Intertwines π.toFun (F b) (Fbar b) := by
      intro b
      cases b
      · exact hdescQ
      · exact hdescP
    have hinv : ∀ b, IsForwardInvariant (Fbar b) J := by
      intro b
      cases b
      · exact hJ.2
      · exact hJ.1
    obtain ⟨K, hKpre, hKinv⟩ :=
      invariantInterval_preimage_b5Prototype π F Fbar hdesc J hinv
    have hKwhole : K.carrier = Set.univ := by
      apply C.core_minimal K
      exact ⟨hKinv true, hKinv false⟩
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := π.surjective_toFun y
    have hxK : x ∈ K.carrier := by rw [hKwhole]; trivial
    rw [hKpre] at hxK
    exact hxK
  let D : MinimalPiecewiseLinearCounterexample :=
    { base :=
        { P := Pbar
          Q := Qbar
          finitePieceP := finitePiecePL_descendedMap
            π C.base.P C.base.finitePieceP hrespectP
          finitePieceQ := finitePiecePL_descendedMap
            π C.base.Q C.base.finitePieceQ hrespectQ
          commute := commute_descendedMap
            π C.base.P C.base.Q hrespectP hrespectQ C.base.commute
          noCommonFixed :=
            noCommonFixedPoint_descendedMap_of_minimalCore C π hrespectP hrespectQ }
      ontoP := descendedMap_onto_b5Prototype π C.base.P hrespectP C.ontoP
      ontoQ := descendedMap_onto_b5Prototype π C.base.Q hrespectQ C.ontoQ
      core_minimal := hminimalBar }
  exact ⟨D, hdescP, hdescQ⟩

private theorem exists_positiveWordFixedSetFiniteDescent_b5Prototype
    (C : MinimalPiecewiseLinearCounterexample)
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ∃ D : MinimalPiecewiseLinearCounterexample,
      (fixedPoints (positiveWordMap D.base.P D.base.Q r s)).Finite ∧
      ∀ a b : ℕ,
        (fixedPoints (positiveWordMap C.base.P C.base.Q a b)).Finite →
          (fixedPoints (positiveWordMap D.base.P D.base.Q a b)).Finite ∧
          (fixedPoints (positiveWordMap D.base.P D.base.Q a b)).ncard ≤
            (fixedPoints (positiveWordMap C.base.P C.base.Q a b)).ncard := by
  classical
  let T : IntervalMap := positiveWordMap C.base.P C.base.Q r s
  have hTPL : FinitePiecePL T := by
    simpa [T, positiveWordMap, Function.comp_def] using
      finitePiecePL_comp
        (finitePiecePL_iterate C.base.finitePieceP r)
        (finitePiecePL_iterate C.base.finitePieceQ s)
  have hTfinite : IsFiniteUnionClosedSubintervals (fixedPoints T) :=
    finitePiecePL_fixedPoints_finiteUnion hTPL
  have hTproper : fixedPoints T ≠ Set.univ := by
    intro hTall
    have hmapP : MapsTo C.base.P wholeIntervalPM.carrier wholeIntervalPM.carrier := by
      intro x _hx
      rw [wholeIntervalPM_carrier]
      exact Set.mem_univ _
    have hmapQ : MapsTo C.base.Q wholeIntervalPM.carrier wholeIntervalPM.carrier := by
      intro x _hx
      rw [wholeIntervalPM_carrier]
      exact Set.mem_univ _
    have hword : IsFixedInterval T wholeIntervalPM := by
      intro x _hx
      rw [hTall]
      exact Set.mem_univ _
    obtain ⟨x, _hx, hcommon⟩ :=
      PLQuotientSupport.commonFixedPoint_on_positiveWord_fixedInterval
        C.base.P C.base.Q r s C.base.finitePieceP.1 C.base.finitePieceQ.1
        C.base.commute hr hs wholeIntervalPM hmapP hmapQ hword
    exact C.base.noCommonFixed ⟨x, hcommon⟩
  obtain ⟨π, hcomponents⟩ :=
    PLQuotientSupport.exists_canonicalFixedComponentQuotient
      T hTPL.1 hTfinite hTproper
  obtain ⟨hrespectP, hrespectQ⟩ :=
    PLQuotientSupport.positiveWord_fixedComponents_respect
      π C.base.P C.base.Q r s C.base.finitePieceP.1
      C.base.finitePieceQ.1 C.base.commute hr hs hcomponents
  obtain ⟨D, hdescP, hdescQ⟩ :=
    exists_descendedMinimalPiecewiseLinearCounterexample_b5Prototype
      C π hrespectP hrespectQ
  have hfixed_eq (a b : ℕ) :
      fixedPoints (positiveWordMap D.base.P D.base.Q a b) =
        π.toFun '' fixedPoints (positiveWordMap C.base.P C.base.Q a b) := by
    have hdescWord :=
      intertwines_positiveWordMap_b5Prototype hdescP hdescQ a b
    let hrespectWord : RespectsFibres π.toFun
        (positiveWordMap C.base.P C.base.Q a b) :=
      respectsFibres_of_intertwines_b5Prototype hdescWord
    have hunique : positiveWordMap D.base.P D.base.Q a b =
        descendedMap π (positiveWordMap C.base.P C.base.Q a b) hrespectWord :=
      descendedMap_unique π.surjective_toFun hdescWord
        (intertwines_descendedMap π
          (positiveWordMap C.base.P C.base.Q a b) hrespectWord)
    rw [hunique]
    exact fixedPoints_descendedMap_exact_continuous_b5Prototype π
      (positiveWordMap C.base.P C.base.Q a b)
      ((C.base.finitePieceP.1.iterate a).comp
        (C.base.finitePieceQ.1.iterate b)) hrespectWord
  refine ⟨D, ?_, ?_⟩
  · rw [hfixed_eq r s]
    exact PLQuotientSupport.fixedPoints_image_finite_of_collapsesExactlyFixedComponents
      π T hTPL.1 hTfinite hcomponents
  · intro a b hfinite
    rw [hfixed_eq a b]
    exact ⟨hfinite.image π.toFun, Set.ncard_image_le hfinite⟩

private theorem piecewiseLinearW_eq_positiveWord_b5Prototype
    (C : MinimalPiecewiseLinearCounterexample) :
    piecewiseLinearW C.base.P C.base.Q =
      positiveWordMap C.base.P C.base.Q 2 2 := by
  simpa [piecewiseLinearW, positiveWordMap, iterateMap] using
    C.base.commute.comp_iterate 2

private theorem exists_finiteCanonicalFixedSets_of_finiteW_b5Prototype
    (C : MinimalPiecewiseLinearCounterexample)
    (hCfinite :
      (fixedPoints (piecewiseLinearW C.base.P C.base.Q)).Finite) :
    ∃ D : MinimalPiecewiseLinearCounterexample,
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).Finite ∧
      let ν := (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard
      let L := 2 * Nat.factorial (2 * ν)
      (fixedPoints
        ((iterateMap D.base.P L) ∘ (iterateMap D.base.Q L))).Finite ∧
      (fixedPoints
        (iterateMap
          ((iterateMap D.base.P L) ∘ (iterateMap D.base.Q L)) 2)).Finite ∧
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard ≤
        (fixedPoints (piecewiseLinearW C.base.P C.base.Q)).ncard := by
  classical
  let firstCounts : Set ℕ :=
    {n | ∃ M : MinimalPiecewiseLinearCounterexample,
      (fixedPoints (piecewiseLinearW M.base.P M.base.Q)).Finite ∧
      (fixedPoints (piecewiseLinearW M.base.P M.base.Q)).ncard = n}
  have hfirst_nonempty : firstCounts.Nonempty :=
    ⟨(fixedPoints (piecewiseLinearW C.base.P C.base.Q)).ncard,
      C, hCfinite, rfl⟩
  let wmin : ℕ := sInf firstCounts
  have hwmin_mem : wmin ∈ firstCounts := Nat.sInf_mem hfirst_nonempty
  rcases hwmin_mem with ⟨CW, hCWfinite, hCWcard⟩
  let L : ℕ := 2 * Nat.factorial (2 * wmin)
  have hLpos : 0 < L := by
    simp only [L]
    positivity
  obtain ⟨CR, hCRRfinite, hpreserveR⟩ :=
    exists_positiveWordFixedSetFiniteDescent_b5Prototype
      CW L L hLpos hLpos
  have hCWword :
      (fixedPoints (positiveWordMap CW.base.P CW.base.Q 2 2)).Finite := by
    rw [← piecewiseLinearW_eq_positiveWord_b5Prototype CW]
    exact hCWfinite
  obtain ⟨hCRwordWfinite, hCRwordWle⟩ := hpreserveR 2 2 hCWword
  have hCRWfinite :
      (fixedPoints (piecewiseLinearW CR.base.P CR.base.Q)).Finite := by
    rw [piecewiseLinearW_eq_positiveWord_b5Prototype CR]
    exact hCRwordWfinite
  have hCRWle :
      (fixedPoints (piecewiseLinearW CR.base.P CR.base.Q)).ncard ≤ wmin := by
    calc
      (fixedPoints (piecewiseLinearW CR.base.P CR.base.Q)).ncard =
          (fixedPoints (positiveWordMap CR.base.P CR.base.Q 2 2)).ncard := by
            rw [piecewiseLinearW_eq_positiveWord_b5Prototype CR]
      _ ≤ (fixedPoints (positiveWordMap CW.base.P CW.base.Q 2 2)).ncard :=
        hCRwordWle
      _ = (fixedPoints (piecewiseLinearW CW.base.P CW.base.Q)).ncard := by
        rw [piecewiseLinearW_eq_positiveWord_b5Prototype CW]
      _ = wmin := hCWcard
  have hwmin_le_CR :
      wmin ≤ (fixedPoints (piecewiseLinearW CR.base.P CR.base.Q)).ncard :=
    Nat.sInf_le
      (show (fixedPoints (piecewiseLinearW CR.base.P CR.base.Q)).ncard ∈
        firstCounts from ⟨CR, hCRWfinite, rfl⟩)
  have hCRWcard :
      (fixedPoints (piecewiseLinearW CR.base.P CR.base.Q)).ncard = wmin :=
    le_antisymm hCRWle hwmin_le_CR
  have htwiceLpos : 0 < L * 2 := Nat.mul_pos hLpos (by norm_num)
  obtain ⟨D, hDSfinite, hpreserveS⟩ :=
    exists_positiveWordFixedSetFiniteDescent_b5Prototype
      CR (L * 2) (L * 2) htwiceLpos htwiceLpos
  have hCRwordW :
      (fixedPoints (positiveWordMap CR.base.P CR.base.Q 2 2)).Finite := by
    rw [← piecewiseLinearW_eq_positiveWord_b5Prototype CR]
    exact hCRWfinite
  obtain ⟨hDwordWfinite, hDwordWle⟩ := hpreserveS 2 2 hCRwordW
  have hDWfinite :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).Finite := by
    rw [piecewiseLinearW_eq_positiveWord_b5Prototype D]
    exact hDwordWfinite
  have hDWle :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard ≤ wmin := by
    calc
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard =
          (fixedPoints (positiveWordMap D.base.P D.base.Q 2 2)).ncard := by
            rw [piecewiseLinearW_eq_positiveWord_b5Prototype D]
      _ ≤ (fixedPoints (positiveWordMap CR.base.P CR.base.Q 2 2)).ncard :=
        hDwordWle
      _ = (fixedPoints (piecewiseLinearW CR.base.P CR.base.Q)).ncard := by
        rw [piecewiseLinearW_eq_positiveWord_b5Prototype CR]
      _ = wmin := hCRWcard
  have hwmin_le_D :
      wmin ≤ (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard :=
    Nat.sInf_le
      (show (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard ∈
        firstCounts from ⟨D, hDWfinite, rfl⟩)
  have hDWcard :
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard = wmin :=
    le_antisymm hDWle hwmin_le_D
  obtain ⟨hDRfinite, _hDRle⟩ := hpreserveS L L hCRRfinite
  have hSform :
      iterateMap
          ((iterateMap D.base.P L) ∘ (iterateMap D.base.Q L)) 2 =
        positiveWordMap D.base.P D.base.Q (L * 2) (L * 2) := by
    unfold iterateMap positiveWordMap
    calc
      ((D.base.P^[L]) ∘ (D.base.Q^[L]))^[2] =
          (D.base.P^[L])^[2] ∘ (D.base.Q^[L])^[2] :=
        (D.base.commute.iterate_iterate L L).comp_iterate 2
      _ = (D.base.P^[L * 2]) ∘ (D.base.Q^[L * 2]) := by
        congr 1
        · exact (Function.iterate_mul D.base.P L 2).symm
        · exact (Function.iterate_mul D.base.Q L 2).symm
  refine ⟨D, hDWfinite, ?_⟩
  dsimp only
  have hcanonicalL :
      2 * Nat.factorial
          (2 * (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard) = L := by
    rw [hDWcard]
  rw [hcanonicalL]
  refine ⟨?_, ?_, ?_⟩
  · simpa [positiveWordMap] using hDRfinite
  · rw [hSform]
    exact hDSfinite
  · rw [hDWcard]
    exact Nat.sInf_le
      (show (fixedPoints (piecewiseLinearW C.base.P C.base.Q)).ncard ∈
        firstCounts from ⟨C, hCfinite, rfl⟩)

private noncomputable def normalizedOfFiniteCanonicalFixedSets_b5Prototype
    (D : MinimalPiecewiseLinearCounterexample)
    (hW : (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).Finite)
    (hR :
      (fixedPoints
        ((iterateMap D.base.P
            (2 * Nat.factorial
              (2 * (fixedPoints
                (piecewiseLinearW D.base.P D.base.Q)).ncard))) ∘
          (iterateMap D.base.Q
            (2 * Nat.factorial
              (2 * (fixedPoints
                (piecewiseLinearW D.base.P D.base.Q)).ncard))))).Finite)
    (hS :
      (fixedPoints
        (iterateMap
          ((iterateMap D.base.P
              (2 * Nat.factorial
                (2 * (fixedPoints
                  (piecewiseLinearW D.base.P D.base.Q)).ncard))) ∘
            (iterateMap D.base.Q
              (2 * Nat.factorial
                (2 * (fixedPoints
                  (piecewiseLinearW D.base.P D.base.Q)).ncard)))) 2)).Finite) :
    NormalizedPiecewiseLinearCounterexample := by
  let fixedW : Finset I := hW.toFinset
  let fixedR : Finset I := hR.toFinset
  let fixedS : Finset I := hS.toFinset
  have hWcard : fixedW.card =
      (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard :=
    (Set.ncard_eq_toFinset_card _ hW).symm
  have hL : piecewiseLinearNormalizationExponent fixedW =
      2 * Nat.factorial
        (2 * (fixedPoints (piecewiseLinearW D.base.P D.base.Q)).ncard) := by
    simp only [piecewiseLinearNormalizationExponent]
    rw [hWcard]
  exact
    { base := D
      fixedW := fixedW
      fixedW_spec := fun x => hW.mem_toFinset
      fixedR := fixedR
      fixedR_spec := by
        intro x
        change x ∈ fixedR ↔
          IsFixedPoint
            ((iterateMap D.base.P
              (piecewiseLinearNormalizationExponent fixedW)) ∘
            (iterateMap D.base.Q
              (piecewiseLinearNormalizationExponent fixedW))) x
        rw [hL]
        exact hR.mem_toFinset
      fixedS := fixedS
      fixedS_spec := by
        intro x
        change x ∈ fixedS ↔
          IsFixedPoint
            (iterateMap
              ((iterateMap D.base.P
                (piecewiseLinearNormalizationExponent fixedW)) ∘
              (iterateMap D.base.Q
                (piecewiseLinearNormalizationExponent fixedW))) 2) x
        rw [hL]
        exact hS.mem_toFinset }

/-- Prototype for the B5 normalization callback.  Lexicographic minimality
forbids a common respected quotient that identifies two fixed points of the
canonical returned square `S`. -/
theorem leastNormalizedPiecewiseLinear_no_respectedQuotient_identifying_S_fixedPoints_b5Prototype
    (C : LeastNormalizedPiecewiseLinearCounterexample)
    (π : CanonicalFiniteIntervalQuotient)
    (hrespectP : RespectsFibres π.toFun C.P)
    (hrespectQ : RespectsFibres π.toFun C.Q)
    (hidentifiedS : IdentifiesDistinctFixedPoints π.toFun C.S) :
    False := by
  classical
  obtain ⟨D, hdescP, hdescQ⟩ :=
    exists_descendedMinimalPiecewiseLinearCounterexample_b5Prototype
      C.base.base π hrespectP hrespectQ
  have hfixedDescend {T Tbar : IntervalMap}
      (hT : Continuous T) (hdesc : Intertwines π.toFun T Tbar) :
      fixedPoints Tbar = π.toFun '' fixedPoints T := by
    let hrespect : RespectsFibres π.toFun T :=
      respectsFibres_of_intertwines_b5Prototype hdesc
    have hunique : Tbar = descendedMap π T hrespect :=
      descendedMap_unique π.surjective_toFun hdesc
        (intertwines_descendedMap π T hrespect)
    rw [hunique]
    exact fixedPoints_descendedMap_exact_continuous_b5Prototype
      π T hT hrespect
  let Wbar : IntervalMap := piecewiseLinearW D.base.P D.base.Q
  let L : ℕ := C.L
  let Rbar : IntervalMap :=
    (iterateMap D.base.P L) ∘ (iterateMap D.base.Q L)
  let Sbar : IntervalMap := iterateMap Rbar 2
  have hdescPQ :
      Intertwines π.toFun (C.P ∘ C.Q) (D.base.P ∘ D.base.Q) :=
    intertwines_comp_b5Prototype hdescP hdescQ
  have hdescW : Intertwines π.toFun C.W Wbar := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.W,
      NormalizedPiecewiseLinearCounterexample.W, piecewiseLinearW, Wbar] using
      (intertwines_iterateMap_b5Prototype hdescPQ 2)
  have hdescA :
      Intertwines π.toFun C.A (iterateMap D.base.P L) := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.A,
      NormalizedPiecewiseLinearCounterexample.A, piecewiseLinearA, L] using
      (intertwines_iterateMap_b5Prototype hdescP L)
  have hdescB :
      Intertwines π.toFun C.B (iterateMap D.base.Q L) := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.B,
      NormalizedPiecewiseLinearCounterexample.B, piecewiseLinearB, L] using
      (intertwines_iterateMap_b5Prototype hdescQ L)
  have hdescR : Intertwines π.toFun C.R Rbar := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.R,
      NormalizedPiecewiseLinearCounterexample.R, piecewiseLinearR, Rbar] using
      (intertwines_comp_b5Prototype hdescA hdescB)
  have hdescS : Intertwines π.toFun C.S Sbar := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.S,
      NormalizedPiecewiseLinearCounterexample.S, piecewiseLinearS, Sbar] using
      (intertwines_iterateMap_b5Prototype hdescR 2)
  have hPcont : Continuous C.P := C.continuousP
  have hQcont : Continuous C.Q := C.continuousQ
  have hWcont : Continuous C.W := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.W,
      NormalizedPiecewiseLinearCounterexample.W, piecewiseLinearW] using
      ((hPcont.comp hQcont).iterate 2)
  have hRcont : Continuous C.R := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.R,
      NormalizedPiecewiseLinearCounterexample.R, piecewiseLinearR,
      piecewiseLinearA, piecewiseLinearB, L] using
      ((hPcont.iterate L).comp (hQcont.iterate L))
  have hScont : Continuous C.S := by
    simpa [LeastNormalizedPiecewiseLinearCounterexample.S,
      NormalizedPiecewiseLinearCounterexample.S, piecewiseLinearS] using
      hRcont.iterate 2
  have hWbarEq : fixedPoints Wbar = π.toFun '' fixedPoints C.W :=
    hfixedDescend hWcont hdescW
  have hRbarEq : fixedPoints Rbar = π.toFun '' fixedPoints C.R :=
    hfixedDescend hRcont hdescR
  have hSbarEq : fixedPoints Sbar = π.toFun '' fixedPoints C.S :=
    hfixedDescend hScont hdescS
  have hWset : fixedPoints C.W = (C.base.fixedW : Set I) := by
    ext x
    exact (C.base.fixedW_spec x).symm
  have hRset : fixedPoints C.R = (C.base.fixedR : Set I) := by
    ext x
    exact (C.base.fixedR_spec x).symm
  have hSset : fixedPoints C.S = (C.base.fixedS : Set I) := by
    ext x
    exact (C.base.fixedS_spec x).symm
  have hWfinite : (fixedPoints C.W).Finite := by
    rw [hWset]
    exact C.base.fixedW.finite_toSet
  have hRfinite : (fixedPoints C.R).Finite := by
    rw [hRset]
    exact C.base.fixedR.finite_toSet
  have hSfinite : (fixedPoints C.S).Finite := by
    rw [hSset]
    exact C.base.fixedS.finite_toSet
  have hWncard : (fixedPoints C.W).ncard = C.base.fixedW.card := by
    rw [hWset]
    simp
  have hRncard : (fixedPoints C.R).ncard = C.base.fixedR.card := by
    rw [hRset]
    simp
  have hSncard : (fixedPoints C.S).ncard = C.base.fixedS.card := by
    rw [hSset]
    simp
  have hWbarFinite : (fixedPoints Wbar).Finite := by
    rw [hWbarEq]
    exact hWfinite.image π.toFun
  have hRbarFinite : (fixedPoints Rbar).Finite := by
    rw [hRbarEq]
    exact hRfinite.image π.toFun
  have hSbarFinite : (fixedPoints Sbar).Finite := by
    rw [hSbarEq]
    exact hSfinite.image π.toFun
  have hWbarLe : (fixedPoints Wbar).ncard ≤ C.base.fixedW.card := by
    rw [hWbarEq, ← hWncard]
    exact Set.ncard_image_le hWfinite
  have hRbarLe : (fixedPoints Rbar).ncard ≤ C.base.fixedR.card := by
    rw [hRbarEq, ← hRncard]
    exact Set.ncard_image_le hRfinite
  have hSbarLt : (fixedPoints Sbar).ncard < C.base.fixedS.card := by
    rw [hSbarEq, ← hSncard]
    have hle := Set.ncard_image_le (f := π.toFun) hSfinite
    apply lt_of_le_of_ne hle
    intro heq
    have hinj : Set.InjOn π.toFun (fixedPoints C.S) :=
      Set.injOn_of_ncard_image_eq heq hSfinite
    obtain ⟨x, y, hx, hy, hxy, hπxy⟩ := hidentifiedS
    exact hxy (hinj hx hy hπxy)
  rcases lt_or_eq_of_le hWbarLe with hWbarLt | hWbarCard
  · obtain ⟨E, hEW, hER, hES, hEnoninc⟩ :=
      exists_finiteCanonicalFixedSets_of_finiteW_b5Prototype D hWbarFinite
    let N : NormalizedPiecewiseLinearCounterexample :=
      normalizedOfFiniteCanonicalFixedSets_b5Prototype E hEW hER hES
    have hNcard : N.fixedW.card =
        (fixedPoints (piecewiseLinearW E.base.P E.base.Q)).ncard := by
      change hEW.toFinset.card = _
      exact (Set.ncard_eq_toFinset_card _ hEW).symm
    have hElt :
        (fixedPoints (piecewiseLinearW E.base.P E.base.Q)).ncard <
          C.base.fixedW.card :=
      lt_of_le_of_lt hEnoninc hWbarLt
    have hleast := C.lex_minimal N
    unfold FixedCountLexLE at hleast
    rw [hNcard] at hleast
    omega
  · have hcanonicalL :
        2 * Nat.factorial (2 * (fixedPoints Wbar).ncard) = L := by
      rw [hWbarCard]
      rfl
    have hRcanonical :
        (fixedPoints
          ((iterateMap D.base.P
              (2 * Nat.factorial (2 * (fixedPoints Wbar).ncard))) ∘
            (iterateMap D.base.Q
              (2 * Nat.factorial (2 * (fixedPoints Wbar).ncard))))).Finite := by
      rw [hcanonicalL]
      exact hRbarFinite
    have hScanonical :
        (fixedPoints
          (iterateMap
            ((iterateMap D.base.P
                (2 * Nat.factorial (2 * (fixedPoints Wbar).ncard))) ∘
              (iterateMap D.base.Q
                (2 * Nat.factorial (2 * (fixedPoints Wbar).ncard)))) 2)).Finite := by
      rw [hcanonicalL]
      exact hSbarFinite
    let N : NormalizedPiecewiseLinearCounterexample :=
      normalizedOfFiniteCanonicalFixedSets_b5Prototype
        D hWbarFinite hRcanonical hScanonical
    have hNWcard : N.fixedW.card = (fixedPoints Wbar).ncard := by
      change hWbarFinite.toFinset.card = _
      exact (Set.ncard_eq_toFinset_card _ hWbarFinite).symm
    have hNRcard : N.fixedR.card = (fixedPoints Rbar).ncard := by
      change hRcanonical.toFinset.card = (fixedPoints Rbar).ncard
      rw [← Set.ncard_eq_toFinset_card _ hRcanonical, hcanonicalL]
    have hNScard : N.fixedS.card = (fixedPoints Sbar).ncard := by
      change hScanonical.toFinset.card = (fixedPoints Sbar).ncard
      rw [← Set.ncard_eq_toFinset_card _ hScanonical, hcanonicalL]
    have hleast := C.lex_minimal N
    unfold FixedCountLexLE at hleast
    rw [hNWcard, hNRcard, hNScard] at hleast
    omega

/-- The disconnected phase-union alternative gives a respected quotient
strictly lowering `#Fix(W)`; the connected alternative and interval Helly
force the diagonal core to be dense in all of `I`. -/
theorem piecewiseLinear_diagonalSelectedGap_dense
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_hexpand : Set.Icc G.p G.c ⊆ G.A '' Set.Icc G.p G.c ∧
      Set.Icc G.p G.c ⊆ G.B '' Set.Icc G.p G.c)
    (_hphase : HasVertexTransitivePhaseIntersections G) :
    HasDenseDiagonalSelectedGapCover G := by
  let J : ClosedSubinterval :=
    PLFiniteArrivalSupport.gapInterval G.p G.c G.p_lt_c.le
  have hL : 0 < G.L :=
    piecewiseLinearNormalizationExponent_pos G.system.base.fixedW
  have hdense :=
    PLFiniteArrivalSupport.diagonalIterates_dense_of_phase_descent
      G.P G.Q hL J G.p_lt_c G.system.continuousP
        G.system.continuousQ G.system.commute _hexpand.1 _hexpand.2
        G.system.base.base.core_minimal (by
          intro π hrespectP hrespectQ hidentified
          exact
            leastNormalizedPiecewiseLinear_no_respectedQuotient_identifying_S_fixedPoints_b5Prototype
              G.system π hrespectP hrespectQ hidentified)
  have hcommAB : Commute G.A G.B :=
    G.system.commute.iterate_iterate G.L G.L
  have hdiag (n : ℕ) :
      PLFiniteArrivalSupport.diagonalImage G.A G.B J n =
        iterateMap G.R n '' Set.Icc G.p G.c := by
    rw [PLFiniteArrivalSupport.diagonalImage_eq_comp_iterate_image J hcommAB]
    rfl
  change Dense
    (⋃ n : ℕ, PLFiniteArrivalSupport.diagonalImage G.A G.B J n) at hdense
  change Dense (⋃ n : ℕ, iterateMap G.R n '' Set.Icc G.p G.c)
  simpa only [hdiag] using hdense

/-- If dense diagonal images never reach both ambient endpoints, `S=R^2`
fixes one missing endpoint and has it as a singleton fibre. -/
theorem piecewiseLinear_asymptoticEndpoint_singletonFibre
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_hdense : HasDenseDiagonalSelectedGapCover G)
    (_hnot : ¬HasFiniteAmbientEndpointArrival G) :
    Nonempty (PiecewiseLinearAsymptoticEndpointObstruction G) := by
  let J : ClosedSubinterval :=
    PLFiniteArrivalSupport.gapInterval G.p G.c G.p_lt_c.le
  have hcommAB : Commute G.A G.B :=
    G.system.commute.iterate_iterate G.L G.L
  have hdiag (n : ℕ) :
      PLFiniteArrivalSupport.diagonalImage G.A G.B J n =
        iterateMap G.R n '' Set.Icc G.p G.c := by
    rw [PLFiniteArrivalSupport.diagonalImage_eq_comp_iterate_image J hcommAB]
    rfl
  have hdenseDiag : Dense
      (⋃ n : ℕ, PLFiniteArrivalSupport.diagonalImage G.A G.B J n) := by
    simpa only [hdiag] using _hdense
  have hreturn := piecewiseLinear_directedStateReturn G
  have hexpand :=
    piecewiseLinear_selectedGap_expands_under_returns G hreturn
  have hRonto : IsOnto (G.A ∘ G.B) :=
    (IntervalMap.surjective_iterate G.system.base.base.ontoP G.L).comp
      (IntervalMap.surjective_iterate G.system.base.base.ontoQ G.L)
  have buildObstruction (e : I)
      (he : PLFiniteArrivalSupport.IsAmbientEndpoint e)
      (hnever : ∀ n : ℕ,
        e ∉ iterateMap G.R n '' Set.Icc G.p G.c) :
      PiecewiseLinearAsymptoticEndpointObstruction G := by
    have hneverDiag :
        PLFiniteArrivalSupport.EndpointNeverArrives G.A G.B J e := by
      intro n hn
      apply hnever n
      rw [← hdiag n]
      exact hn
    obtain ⟨hfixed, hfibre⟩ :=
      PLFiniteArrivalSupport.endpoint_singletonFibre_of_neverArrives
        J (G.system.continuousP.iterate G.L)
          (G.system.continuousQ.iterate G.L) hcommAB
          hexpand.1 hexpand.2 hRonto hdenseDiag he hneverDiag
    exact
      { endpoint := e
        ambient_endpoint := he
        never_arrives := hnever
        fixed := hfixed
        singleton_fibre := hfibre }
  by_cases hleft : ∃ n : ℕ,
      leftEndpoint ∈ iterateMap G.R n '' Set.Icc G.p G.c
  · have hrightNever : ∀ n : ℕ,
        rightEndpoint ∉ iterateMap G.R n '' Set.Icc G.p G.c := by
      intro n hn
      obtain ⟨m, hm⟩ := hleft
      exact _hnot ⟨m, n, hm, hn⟩
    exact ⟨buildObstruction rightEndpoint (Or.inr rfl) hrightNever⟩
  · have hleftNever : ∀ n : ℕ,
        leftEndpoint ∉ iterateMap G.R n '' Set.Icc G.p G.c := by
      intro n hn
      exact hleft ⟨n, hn⟩
    exact ⟨buildObstruction leftEndpoint (Or.inl rfl) hleftNever⟩

/-- The singleton-fibre endpoint has a proper immediate attracting basin.
Its phase graph either yields a proper common invariant interval or a safe
quotient lowering `#Fix(S)`, contradicting lexicographic minimality. -/
theorem piecewiseLinear_asymptoticEndpoint_basin_contradiction
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_hdense : HasDenseDiagonalSelectedGapCover G)
    (_hobstruction : PiecewiseLinearAsymptoticEndpointObstruction G) :
    False := by
  let J : ClosedSubinterval :=
    PLFiniteArrivalSupport.gapInterval G.p G.c G.p_lt_c.le
  have hcommAB : Commute G.A G.B :=
    G.system.commute.iterate_iterate G.L G.L
  have hdiag (n : ℕ) :
      PLFiniteArrivalSupport.diagonalImage G.A G.B J n =
        iterateMap G.R n '' Set.Icc G.p G.c := by
    rw [PLFiniteArrivalSupport.diagonalImage_eq_comp_iterate_image J hcommAB]
    rfl
  have hdenseDiag : Dense
      (⋃ n : ℕ, PLFiniteArrivalSupport.diagonalImage G.A G.B J n) := by
    simpa only [hdiag] using _hdense
  have hreturn := piecewiseLinear_directedStateReturn G
  have hexpand :=
    piecewiseLinear_selectedGap_expands_under_returns G hreturn
  have hRonto : IsOnto (G.A ∘ G.B) :=
    (IntervalMap.surjective_iterate G.system.base.base.ontoP G.L).comp
      (IntervalMap.surjective_iterate G.system.base.base.ontoQ G.L)
  have hSPL : FinitePiecePL G.S := by
    change FinitePiecePL (iterateMap (G.A ∘ G.B) 2)
    exact finitePiecePL_iterate
      (finitePiecePL_comp
        (finitePiecePL_iterate G.system.finitePieceP G.L)
        (finitePiecePL_iterate G.system.finitePieceQ G.L)) 2
  have hSfinite : (fixedPoints G.S).Finite := by
    apply G.system.base.fixedS.finite_toSet.subset
    intro x hx
    exact (G.system.base.fixedS_spec x).2 hx
  have hfibre : G.S ⁻¹' {_hobstruction.endpoint} =
      {_hobstruction.endpoint} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact _hobstruction.singleton_fibre x
    · rintro rfl
      exact _hobstruction.fixed
  have hneverDiag :
      PLFiniteArrivalSupport.EndpointNeverArrives
        G.A G.B J _hobstruction.endpoint := by
    intro n hn
    apply _hobstruction.never_arrives n
    rw [← hdiag n]
    exact hn
  have happroach :
      PLFiniteArrivalSupport.EndpointApproachSequence
        G.S _hobstruction.endpoint := by
    exact PLEndpointBasinSupport.endpointApproachSequence_of_neverArrives J
      (G.system.continuousP.iterate G.L)
      (G.system.continuousQ.iterate G.L) hcommAB
      hexpand.1 hexpand.2 hRonto hSfinite hdenseDiag
      _hobstruction.ambient_endpoint hneverDiag
  have hRp : IsFixedPoint G.R G.p := by
    change G.A (G.B G.p) = G.p
    rw [hreturn.fixed_B_p, hreturn.fixed_A_p]
  have hRc : IsFixedPoint G.R G.c := by
    change G.A (G.B G.c) = G.c
    rw [hreturn.fixed_B_c, hreturn.fixed_A_c]
  have hSp : IsFixedPoint G.S G.p := Function.iterate_fixed hRp 2
  have hSc : IsFixedPoint G.S G.c := Function.iterate_fixed hRc 2
  have hpMemZero : G.p ∈ iterateMap G.R 0 '' Set.Icc G.p G.c := by
    simp [iterateMap, G.p_lt_c.le]
  have hcMemZero : G.c ∈ iterateMap G.R 0 '' Set.Icc G.p G.c := by
    simp [iterateMap, G.p_lt_c.le]
  have hbarrier : ∃ q : I,
      ¬ PLFiniteArrivalSupport.IsAmbientEndpoint q ∧
        IsFixedPoint G.S q := by
    rcases _hobstruction.ambient_endpoint with heLeft | heRight
    · refine ⟨G.p, ?_, hSp⟩
      intro hpEndpoint
      rcases hpEndpoint with hpLeft | hpRight
      · apply _hobstruction.never_arrives 0
        simpa [heLeft, hpLeft] using hpMemZero
      · exact (G.p_lt_c.trans_le G.c.property.2).ne hpRight
    · refine ⟨G.c, ?_, hSc⟩
      intro hcEndpoint
      rcases hcEndpoint with hcLeft | hcRight
      · have hleftC : leftEndpoint < G.c :=
          G.p.property.1.trans_lt G.p_lt_c
        exact hleftC.ne' hcLeft
      · apply _hobstruction.never_arrives 0
        simpa [heRight, hcRight] using hcMemZero
  obtain ⟨_hlocallyAttracting, _hbasinOpen, ⟨E⟩⟩ :=
    PLEndpointBasinSupport.local_endpoint_monotonicity_and_basinClosure
      _hobstruction.ambient_endpoint hSPL hSPL.1 hSfinite
        _hobstruction.fixed hfibre happroach hbarrier
  let k : ℕ := Nat.factorial (2 * G.system.base.fixedW.card)
  have hk : 0 < k := Nat.factorial_pos _
  have hSform : G.S = iterateMap
      ((iterateMap G.P (2 * k)) ∘ (iterateMap G.Q (2 * k))) 2 := by
    rfl
  obtain ⟨hAe, hBe⟩ :=
    PLFiniteArrivalSupport.evenReturnPowers_fix_singletonFibre_endpoint
      k hk G.system.continuousP G.system.continuousQ
        G.system.base.base.ontoP G.system.base.base.ontoQ G.system.commute
        hSform _hobstruction.ambient_endpoint _hobstruction.fixed hfibre
  have hAe' : IsFixedPoint G.A _hobstruction.endpoint := hAe
  have hBe' : IsFixedPoint G.B _hobstruction.endpoint := hBe
  have hSformAB : G.S =
      iterateMap G.A 2 ∘ iterateMap G.B 2 :=
    hcommAB.comp_iterate 2
  obtain ⟨hAonto, hBonto⟩ :=
    PLEndpointBasinSupport.canonical_powers_map_endpointBasinClosure_onto
      (G.system.continuousP.iterate G.L)
      (G.system.continuousQ.iterate G.L) hcommAB hSformAB
      _hobstruction.fixed hAe' hBe' E
  apply PLFiniteArrivalSupport.proper_powerInvariant_interval_impossible_of_phase_descent
    (P := G.P) (Q := G.Q)
    (piecewiseLinearNormalizationExponent_pos G.system.base.fixedW)
    E.interval G.system.continuousP G.system.continuousQ
    G.system.commute hAonto hBonto E.nondegenerate E.proper
    G.system.base.base.core_minimal
  intro π hrespectP hrespectQ hidentified
  exact
    leastNormalizedPiecewiseLinear_no_respectedQuotient_identifying_S_fixedPoints_b5Prototype
      G.system π hrespectP hrespectQ hidentified

/-- Dense diagonal coverage must therefore reach both ambient endpoints in
finite time. -/
theorem piecewiseLinear_ambientEndpoints_arrive
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (hdense : HasDenseDiagonalSelectedGapCover G) :
    HasFiniteAmbientEndpointArrival G := by
  by_contra hnot
  obtain ⟨hobstruction⟩ :=
    piecewiseLinear_asymptoticEndpoint_singletonFibre G hdense hnot
  exact piecewiseLinear_asymptoticEndpoint_basin_contradiction
    G hdense hobstruction

/-- Monotonicity of the diagonal image sequence combines the two endpoint
arrival times into one stage covering all of `I`. -/
theorem piecewiseLinear_finiteSelectedGapCover_of_endpointArrival
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_hexpand : Set.Icc G.p G.c ⊆ G.A '' Set.Icc G.p G.c ∧
      Set.Icc G.p G.c ⊆ G.B '' Set.Icc G.p G.c)
    (_harrival : HasFiniteAmbientEndpointArrival G) :
    HasFiniteSelectedGapCover G := by
  let J : ClosedSubinterval :=
    PLFiniteArrivalSupport.gapInterval G.p G.c G.p_lt_c.le
  have hcommAB : Commute G.A G.B := by
    exact G.system.commute.iterate_iterate G.L G.L
  have hdiag (n : ℕ) :
      PLFiniteArrivalSupport.diagonalImage G.A G.B J n =
        iterateMap G.R n '' Set.Icc G.p G.c := by
    rw [PLFiniteArrivalSupport.diagonalImage_eq_comp_iterate_image J hcommAB]
    rfl
  obtain ⟨n0, n1, hn0, hn1⟩ := _harrival
  have harrival : ∃ n0 n1 : ℕ,
      leftEndpoint ∈ PLFiniteArrivalSupport.diagonalImage G.A G.B J n0 ∧
        rightEndpoint ∈
          PLFiniteArrivalSupport.diagonalImage G.A G.B J n1 := by
    exact ⟨n0, n1, by rw [hdiag]; exact hn0, by rw [hdiag]; exact hn1⟩
  obtain ⟨N, hN⟩ :=
    PLFiniteArrivalSupport.finiteDiagonalCover_of_endpointArrival
      J (G.system.continuousP.iterate G.L)
        (G.system.continuousQ.iterate G.L) hcommAB
        _hexpand.1 _hexpand.2 harrival
  refine ⟨N, ?_⟩
  rw [← hdiag]
  exact hN

/-- Finite arrival excludes an ambient right terminal endpoint.  If the base
is internal, rightward motion of `R = W^d` cannot pull the left endpoint back
from the selected gap; if the gap is all of `I`, the generator actions on
fixed and repelling directed states force a common fixed endpoint. -/
theorem piecewiseLinear_selectedTerminalGap_internal
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_D : PiecewiseLinearDirectedReturnData G)
    (_hcover : HasFiniteSelectedGapCover G) :
    HasInternalSelectedTerminalGap G := by
  have fullGapGeneratorCannotSwap
      (hp : G.p = leftEndpoint) (hc : G.c = rightEndpoint)
      (F : IntervalMap)
      (hperm : PermutesRepellingDirectedStatesPLCore F G.W)
      (hswap : F G.p = G.c) : False := by
    obtain ⟨eperm, hphysical⟩ := hperm
    let sigma : {tau // IsRepellingDirectedStatePLCore G.W tau} :=
      ⟨rightDirectedSide G.p (G.p_lt_c.trans_le G.c.property.2),
        piecewiseLinear_selectedGap_is_repelling G⟩
    let tau : {tau // IsRepellingDirectedStatePLCore G.W tau} :=
      eperm sigma
    have hcarry := hphysical sigma
    have hbase : tau.1.base = rightEndpoint := by
      change (eperm sigma).1.base = rightEndpoint
      rw [← hcarry.1, show sigma.1.base = G.p by rfl, hswap, hc]
    have hdirection : tau.1.direction = .left := by
      cases hdir : tau.1.direction with
      | left => rfl
      | right =>
          exfalso
          obtain ⟨x, hx⟩ := tau.1.available
          have hx' : tau.1.base < x := by
            simpa [Side.Available, Side.puncturedRay, hdir] using hx
          rw [hbase] at hx'
          exact (not_lt_of_ge x.property.2) hx'
    obtain ⟨_htauFixed, U, hUopen, htauU, _hne, hmove⟩ := tau.2
    have hUnhds : U ∈ nhds rightEndpoint := by
      rw [← hbase]
      exact hUopen.mem_nhds htauU
    obtain ⟨epsilon, hepsilonPos, hepsilonSub⟩ :=
      Metric.mem_nhds_iff.mp hUnhds
    let delta : ℝ := min (epsilon / 2) (1 / 2)
    have hdeltaPos : 0 < delta := by
      dsimp [delta]
      exact lt_min (half_pos hepsilonPos) (by norm_num)
    have hdeltaEpsilon : delta < epsilon :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self hepsilonPos)
    have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
    let y : I := ⟨1 - delta, by linarith, by linarith⟩
    have hydist : dist y rightEndpoint < epsilon := by
      rw [Subtype.dist_eq, Real.dist_eq]
      change |(1 - delta) - 1| < epsilon
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hyU : y ∈ U := hepsilonSub (Metric.mem_ball.mpr hydist)
    have hySide : y ∈ tau.1.direction.puncturedRay tau.1.base := by
      rw [hdirection]
      change y < tau.1.base
      rw [hbase]
      change 1 - delta < 1
      linarith
    have hyInterior : y ∈ Set.Ioo G.p G.c := by
      rw [hp, hc]
      constructor
      · change 0 < 1 - delta
        linarith
      · change 1 - delta < 1
        linarith
    have hleftMove : G.W y < y := by
      have haway := (hmove y ⟨hyU, hySide⟩).2
      rw [MovesAwayAlongPLCore, hdirection] at haway
      exact haway.2
    exact (not_lt_of_ge (G.moves_right y hyInterior).le) hleftMove
  have hWform : G.W = (G.P^[2]) ∘ (G.Q^[2]) :=
    G.system.commute.comp_iterate 2
  have hfixedPermP : PermutesFixedPointsPLCore G.P G.W := by
    rw [hWform]
    exact permutesFixedPointsPLCore_left_iterates_comp
      G.system.commute (by norm_num)
  have hfixedPermQ : PermutesFixedPointsPLCore G.Q G.W := by
    rw [hWform]
    exact permutesFixedPointsPLCore_right_iterates_comp
      G.system.commute (by norm_num)
  obtain ⟨hrepPermP, hrepPermQ⟩ :=
    piecewiseLinear_generators_permute_repellingStates G
  have hfullGapImpossible (hp : G.p = leftEndpoint)
      (hc : G.c = rightEndpoint) : False := by
    have generatorFixesBase (F : IntervalMap)
        (hfixedPerm : PermutesFixedPointsPLCore F G.W)
        (hrepPerm : PermutesRepellingDirectedStatesPLCore F G.W) :
        F G.p = G.p := by
      obtain ⟨eperm, hphysical⟩ := hfixedPerm
      let pFixed : fixedPoints G.W := ⟨G.p, G.fixed_p⟩
      have hFfixed : IsFixedPoint G.W (F G.p) := by
        have h := (eperm pFixed).2
        rw [← hphysical pFixed] at h
        exact h
      by_cases hFp : F G.p = G.p
      · exact hFp
      · have hFc : F G.p = G.c := by
          by_contra hFneC
          have hpF : G.p < F G.p := by
            have hle : G.p ≤ F G.p := by
              have hleftle : leftEndpoint ≤ F G.p := by
                change (0 : ℝ) ≤ (F G.p : ℝ)
                exact (F G.p).property.1
              simpa [hp] using hleftle
            exact lt_of_le_of_ne hle (Ne.symm hFp)
          have hFc' : F G.p < G.c := by
            have hle : F G.p ≤ G.c := by
              rw [hc]
              exact (F G.p).property.2
            exact lt_of_le_of_ne hle hFneC
          exact (G.consecutive (F G.p) ⟨hpF, hFc'⟩) hFfixed
        exact (fullGapGeneratorCannotSwap hp hc F hrepPerm hFc).elim
    have hPp : IsFixedPoint G.P G.p :=
      generatorFixesBase G.P hfixedPermP hrepPermP
    have hQp : IsFixedPoint G.Q G.p :=
      generatorFixesBase G.Q hfixedPermQ hrepPermQ
    exact G.noCommonFixed ⟨G.p, hPp, hQp⟩
  let d : ℕ := Nat.factorial (2 * G.system.base.fixedW.card)
  have hWiterate : G.W^[d] =
      ((G.P^[2])^[d]) ∘ ((G.Q^[2])^[d]) := by
    rw [hWform]
    exact (G.system.commute.iterate_iterate 2 2).comp_iterate d
  have hRW : G.R = iterateMap G.W d := by
    calc
      G.R = (G.P^[2 * d]) ∘ (G.Q^[2 * d]) := by rfl
      _ = ((G.P^[2])^[d]) ∘ ((G.Q^[2])^[d]) := by
        apply congrArg₂ (fun F H : IntervalMap => F ∘ H)
        · exact Function.iterate_mul G.P 2 d
        · exact Function.iterate_mul G.Q 2 d
      _ = G.W^[d] := hWiterate.symm
      _ = iterateMap G.W d := rfl
  exact PLFiniteArrivalSupport.terminalGap_internal_of_finiteReturnCover
    G.p_lt_c G.fixed_p G.fixed_c G.moves_right _hcover d hRW
      hfullGapImpossible

/-- Strict rightward motion, an internal terminal endpoint, and finite
arrival turn every selected-side interval into all of `I` under a power of
`W`. -/
theorem piecewiseLinear_localEventualOnto_of_finiteArrival
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_hcover : HasFiniteSelectedGapCover G)
    (_hinternal : HasInternalSelectedTerminalGap G) :
    HasLocalEventualOntoPL G.W G.p := by
  let d : ℕ := Nat.factorial (2 * G.system.base.fixedW.card)
  have hWform : G.W = (G.P^[2]) ∘ (G.Q^[2]) := by
    exact G.system.commute.comp_iterate 2
  have hWiterate : G.W^[d] =
      ((G.P^[2])^[d]) ∘ ((G.Q^[2])^[d]) := by
    rw [hWform]
    exact (G.system.commute.iterate_iterate 2 2).comp_iterate d
  have hRW : G.R = iterateMap G.W d := by
    calc
      G.R = (G.P^[2 * d]) ∘ (G.Q^[2 * d]) := by rfl
      _ = ((G.P^[2])^[d]) ∘ ((G.Q^[2])^[d]) := by
        apply congrArg₂ (fun F H : IntervalMap => F ∘ H)
        · exact Function.iterate_mul G.P 2 d
        · exact Function.iterate_mul G.Q 2 d
      _ = G.W^[d] := hWiterate.symm
      _ = iterateMap G.W d := rfl
  have hWcont : Continuous G.W :=
    (G.system.continuousP.comp G.system.continuousQ).iterate 2
  have hRcont : Continuous G.R :=
    (G.system.continuousP.iterate G.L).comp
      (G.system.continuousQ.iterate G.L)
  have hRc : IsFixedPoint G.R G.c := by
    rw [hRW]
    exact Function.iterate_fixed G.fixed_c d
  exact PLFiniteArrivalSupport.localEventualOnto_of_finiteReturnCover
    G.p_lt_c hWcont hRcont G.fixed_p hRc G.moves_right
      _hinternal _hcover d hRW

/-- Boundary 5: phase-intersection alternatives, safe component quotients,
finite arrival, and local eventual onto. -/
theorem piecewiseLinear_finiteArrivalAndLEO
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_D : PiecewiseLinearDirectedReturnData G) :
    PreparedPiecewiseLinearCounterexample G := by
  have hexpand := piecewiseLinear_selectedGap_expands_under_returns G _D
  have hphase := piecewiseLinear_phaseIntersections_vertexTransitive G
  have hdense := piecewiseLinear_diagonalSelectedGap_dense
    G hexpand hphase
  have harrival := piecewiseLinear_ambientEndpoints_arrive G hdense
  have hcover := piecewiseLinear_finiteSelectedGapCover_of_endpointArrival
    G hexpand harrival
  have hinternal := piecewiseLinear_selectedTerminalGap_internal G _D hcover
  exact
    { finite_arrival := hcover
      local_eventual_onto :=
        piecewiseLinear_localEventualOnto_of_finiteArrival
          G hcover hinternal }

/-! ## Orbit-circle consumer data and exactness utility -/

/-- The rational branch of the orbit-circle dichotomy. -/
def PLCommonPositiveIterateAlternative (P Q : IntervalMap) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
    iterateMap P m = iterateMap Q n


/-- The irrational branch after ray extension, tail-core analysis, and
globalization.  The local dilation scales belong to the selected germs;
global constant slopes are restored only in the next stage. -/
structure PiecewiseLinearIrrationalExactSystem
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) where
  ray : ℝ → I
  scaleA : ℝ
  scaleB : ℝ
  one_lt_scaleA : 1 < scaleA
  one_lt_scaleB : 1 < scaleB
  scales_independent : MultiplicativelyIndependent scaleA scaleB
  continuous_ray : Continuous ray
  ray_base : ray 0 = G.p
  ray_onto : Function.Surjective ray
  action_A : ∀ t : ℝ, 0 ≤ t → ray (scaleA * t) = G.A (ray t)
  action_B : ∀ t : ℝ, 0 ≤ t → ray (scaleB * t) = G.B (ray t)
  dense_tails : ∀ T : ℝ, Dense (ray '' Set.Ici T)
  exact_P : IsTopologicallyExact G.P
  exact_Q : IsTopologicallyExact G.Q
  exact_A : IsTopologicallyExact G.A
  exact_B : IsTopologicallyExact G.B
  exact_R : IsTopologicallyExact G.R
  noFlat_P : ¬HasFlatInterval G.P
  noFlat_Q : ¬HasFlatInterval G.Q
  noFlat_R : ¬HasFlatInterval G.R
  no_positive_iterate : ¬PLCommonPositiveIterateAlternative G.P G.Q


/-- An exact finite-piece PL interval map has no flat interval. -/
theorem piecewiseLinear_exact_noFlat
    {T : IntervalMap} (_hPL : FinitePiecePL T)
    (_hexact : IsTopologicallyExact T) : ¬HasFlatInterval T := by
  rintro ⟨J, hJnondegenerate, hJflat⟩
  let U : Set I := Set.Ioo J.left J.right
  have hUopen : IsOpen U := isOpen_Ioo
  have hUnonempty : U.Nonempty := Set.nonempty_Ioo.mpr hJnondegenerate
  obtain ⟨n, hn⟩ := _hexact U hUopen hUnonempty
  cases n with
  | zero =>
      have hUuniv : U = Set.univ := by
        simpa [iterateMap] using hn
      have hleftU : J.left ∈ U := by
        rw [hUuniv]
        exact Set.mem_univ J.left
      exact (lt_irrefl J.left hleftU.1)
  | succ n =>
      have hconstant : ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
          iterateMap T (n + 1) x = iterateMap T (n + 1) y := by
        intro x hx y hy
        have hTxy : T x = T y :=
          hJflat ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩
        simpa [iterateMap, Function.iterate_succ_apply] using
          congrArg (T^[n]) hTxy
      have hleftImage : leftEndpoint ∈ iterateMap T (n + 1) '' U := by
        rw [hn]
        exact Set.mem_univ leftEndpoint
      have hrightImage : rightEndpoint ∈ iterateMap T (n + 1) '' U := by
        rw [hn]
        exact Set.mem_univ rightEndpoint
      obtain ⟨x, hxU, hx⟩ := hleftImage
      obtain ⟨y, hyU, hy⟩ := hrightImage
      have hends : leftEndpoint = rightEndpoint := by
        rw [← hx, ← hy]
        exact hconstant hxU hyU
      simpa [leftEndpoint, rightEndpoint] using congrArg Subtype.val hends


/-! ## Joint spectral measure and the common constant-slope coordinate -/

/-- A finite-piece PL map whose nonzero affine slopes all have one positive
absolute value. -/
def HasConstantAbsoluteSlopePLCore (T : IntervalMap) (s : ℝ) : Prop :=
  Continuous T ∧
    ∃ p : RealPartition,
      ∀ ⦃a b : ℝ⦄, p.Adjacent a b →
        ∃ m c : ℝ, |m| = s ∧
          ∀ x ∈ intervalCell a b,
            (T x : ℝ) = m * (x : ℝ) + c

/-- Constant absolute slopes multiply under composition. -/
private theorem constantAbsoluteSlopePLCore_comp
    {U T : IntervalMap} {u t : ℝ} (_ht : 0 < t)
    (hU : HasConstantAbsoluteSlopePLCore U u)
    (hT : HasConstantAbsoluteSlopePLCore T t) :
    HasConstantAbsoluteSlopePLCore (U ∘ T) (u * t) := by
  rcases hU with ⟨hUcont, pU, hpU⟩
  rcases hT with ⟨hTcont, pT, hpT⟩
  let wU : MonotonicityPartition U :=
    ⟨pU, fun _ _ hab ↦ by
      obtain ⟨m, c, _hm, hformula⟩ := hpU hab
      exact affineOn_weaklyMonotoneOn_plCore ⟨m, c, hformula⟩⟩
  let wT : MonotonicityPartition T :=
    ⟨pT, fun _ _ hab ↦ by
      obtain ⟨m, c, _hm, hformula⟩ := hpT hab
      exact affineOn_weaklyMonotoneOn_plCore ⟨m, c, hformula⟩⟩
  refine ⟨hUcont.comp hTcont, wT.compositionRefinement wU, ?_⟩
  intro a b hab
  obtain ⟨aT, bT, hTadj, hsource⟩ :=
    (wT.compositionRefinement_refines wU).adjacent_subset hab
  obtain ⟨mT, cT, hmT, hTformula⟩ := hpT hTadj
  obtain ⟨_hTweak, aU, bU, hUadj, hmaps⟩ :=
    wT.composition_cell hTcont wU hab
  obtain ⟨mU, cU, hmU, hUformula⟩ := hpU hUadj
  refine ⟨mU * mT, mU * cT + cU, ?_, ?_⟩
  · rw [abs_mul, hmU, hmT]
  · intro x hx
    change (U (T x) : ℝ) = _
    rw [hUformula (T x) (hmaps hx), hTformula x (hsource hx)]
    ring

/-- The identity has constant absolute slope one. -/
private theorem constantAbsoluteSlopePLCore_id :
    HasConstantAbsoluteSlopePLCore (id : IntervalMap) 1 := by
  refine ⟨continuous_id, RealPartition.trivial, ?_⟩
  intro a b _hab
  refine ⟨1, 0, by simp, ?_⟩
  intro x _hx
  simp

/-- Constant absolute slope is preserved by finite iteration. -/
private theorem constantAbsoluteSlopePLCore_iterate
    {T : IntervalMap} {s : ℝ} (hs : 0 < s)
    (hT : HasConstantAbsoluteSlopePLCore T s) (n : ℕ) :
    HasConstantAbsoluteSlopePLCore (iterateMap T n) (s ^ n) := by
  induction n with
  | zero => simpa [iterateMap] using constantAbsoluteSlopePLCore_id
  | succ n ih =>
      have hpow : 0 < s ^ n := pow_pos hs n
      have hcomp := constantAbsoluteSlopePLCore_comp hpow hT ih
      have hfun : iterateMap T (n + 1) = T ∘ iterateMap T n := by
        funext x
        exact Function.iterate_succ_apply' T n x
      rw [hfun]
      simpa [pow_succ, mul_comm] using hcomp

/-- Conjugacy written in the direction used by the distribution coordinate. -/
def ConjugatesPLCore
    (θ : I ≃ₜ I) (T Tbar : IntervalMap) : Prop :=
  ∀ x : I, θ (T x) = Tbar (θ x)

/-- Conjugacy is preserved by finite iteration. -/
theorem conjugatesPLCore_iterate
    {T Tbar : IntervalMap} {θ : I ≃ₜ I}
    (h : ConjugatesPLCore θ T Tbar) (n : ℕ) :
    ConjugatesPLCore θ (iterateMap T n) (iterateMap Tbar n) := by
  intro x
  induction n generalizing x with
  | zero => simp [iterateMap]
  | succ n ih =>
      simp only [iterateMap, Function.iterate_succ_apply]
      calc
        θ ((T^[n]) (T x)) = (Tbar^[n]) (θ (T x)) := ih (T x)
        _ = (Tbar^[n]) (Tbar (θ x)) := congrArg (Tbar^[n]) (h x)

/-- Two maps conjugated by the same coordinate may be composed. -/
theorem conjugatesPLCore_comp
    {T U Tbar Ubar : IntervalMap} {θ : I ≃ₜ I}
    (hT : ConjugatesPLCore θ T Tbar)
    (hU : ConjugatesPLCore θ U Ubar) :
    ConjugatesPLCore θ (T ∘ U) (Tbar ∘ Ubar) := by
  intro x
  change θ (T (U x)) = Tbar (Ubar (θ x))
  calc
    θ (T (U x)) = Tbar (θ (U x)) := hT (U x)
    _ = Tbar (Ubar (θ x)) := congrArg Tbar (hU x)

/-- Topological exactness passes through a topological conjugacy. -/
theorem exact_of_conjugatesPLCore
    {T Tbar : IntervalMap} {θ : I ≃ₜ I}
    (h : ConjugatesPLCore θ T Tbar)
    (hexact : IsTopologicallyExact T) :
    IsTopologicallyExact Tbar := by
  intro V hVopen hVne
  let Vpre : Set I := θ.symm '' V
  have hVpreOpen : IsOpen Vpre := θ.symm.isOpenMap V hVopen
  have hVpreNe : Vpre.Nonempty := hVne.image θ.symm
  obtain ⟨n, hn⟩ := hexact Vpre hVpreOpen hVpreNe
  refine ⟨n, Set.eq_univ_of_forall ?_⟩
  intro y
  have hy : θ.symm y ∈ iterateMap T n '' Vpre := by
    rw [hn]
    exact Set.mem_univ _
  rcases hy with ⟨x, hxpre, hTx⟩
  rcases hxpre with ⟨v, hv, hvx⟩
  have hthetax : θ x = v := by
    rw [← hvx]
    simp
  refine ⟨v, hv, ?_⟩
  calc
    iterateMap Tbar n v = iterateMap Tbar n (θ x) :=
      congrArg (iterateMap Tbar n) hthetax.symm
    _ = θ (iterateMap T n x) :=
      (conjugatesPLCore_iterate h n x).symm
    _ = θ (θ.symm y) := congrArg θ hTx
    _ = y := by simp

/-- Commutation passes through a common topological conjugacy. -/
theorem commute_of_conjugatesPLCore
    {T U Tbar Ubar : IntervalMap} {θ : I ≃ₜ I}
    (hT : ConjugatesPLCore θ T Tbar)
    (hU : ConjugatesPLCore θ U Ubar)
    (hcomm : Commute T U) : Commute Tbar Ubar := by
  intro y
  let x : I := θ.symm y
  have hy : y = θ x := by simp [x]
  rw [hy]
  calc
    Tbar (Ubar (θ x)) = Tbar (θ (U x)) :=
      congrArg Tbar (hU x).symm
    _ = θ (T (U x)) := (hT (U x)).symm
    _ = θ (U (T x)) := congrArg θ (hcomm x)
    _ = Ubar (θ (T x)) := hU (T x)
    _ = Ubar (Tbar (θ x)) := congrArg Ubar (hT x)

/-- The common distribution coordinate and its two constant-slope models.
The transformed returned scales retain the selected positive germs and are
multiplicatively independent. -/
structure PiecewiseLinearConstantSlopeSystem
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (_E : PiecewiseLinearIrrationalExactSystem G) where
  coordinate : I ≃ₜ I
  coordinate_strictMono : StrictMono coordinate
  modelP : IntervalMap
  modelQ : IntervalMap
  conjugatesP : ConjugatesPLCore coordinate G.P modelP
  conjugatesQ : ConjugatesPLCore coordinate G.Q modelQ
  scaleP : ℝ
  scaleQ : ℝ
  one_lt_scaleP : 1 < scaleP
  one_lt_scaleQ : 1 < scaleQ
  slopeP : HasConstantAbsoluteSlopePLCore modelP scaleP
  slopeQ : HasConstantAbsoluteSlopePLCore modelQ scaleQ
  commute : Commute modelP modelQ
  exact_P : IsTopologicallyExact modelP
  exact_Q : IsTopologicallyExact modelQ
  exact_A : IsTopologicallyExact (iterateMap modelP G.L)
  exact_B : IsTopologicallyExact (iterateMap modelQ G.L)
  exact_R : IsTopologicallyExact
    (iterateMap modelP G.L ∘ iterateMap modelQ G.L)
  returned_scales_independent :
    MultiplicativelyIndependent (scaleP ^ G.L) (scaleQ ^ G.L)

namespace PiecewiseLinearConstantSlopeSystem

variable {source : LeastNormalizedPiecewiseLinearCounterexample}
  {G : PiecewiseLinearSelectedFixedGap source}
  {E : PiecewiseLinearIrrationalExactSystem G}

def A (M : PiecewiseLinearConstantSlopeSystem E) : IntervalMap :=
  iterateMap M.modelP G.L

def B (M : PiecewiseLinearConstantSlopeSystem E) : IntervalMap :=
  iterateMap M.modelQ G.L

def R (M : PiecewiseLinearConstantSlopeSystem E) : IntervalMap :=
  M.A ∘ M.B

end PiecewiseLinearConstantSlopeSystem

/-- A constant-absolute-slope presentation is finite-piece PL. -/
theorem constantAbsoluteSlopePLCore_finitePiecePL
    {T : IntervalMap} {s : ℝ}
    (hT : HasConstantAbsoluteSlopePLCore T s) : FinitePiecePL T := by
  rcases hT with ⟨hcont, p, hp⟩
  refine ⟨hcont, p, ?_⟩
  intro a b hab
  obtain ⟨m, c, _hm, hmc⟩ := hp hab
  exact ⟨m, c, hmc⟩

/-! ## PL-to-piecewise-monotone infrastructure -/

/-- Every finite-piece PL interval map is finite-piece weakly monotone. -/
theorem finitePiecePL_finitePieceMonotone
    {T : IntervalMap} (hT : FinitePiecePL T) :
    FinitePieceMonotone T := by
  rcases hT with ⟨hcont, p, hp⟩
  refine FinitePieceMonotone.of_partition hcont p ?_
  intro a b hab
  rcases hp hab with ⟨m, c, hformula⟩
  by_cases hm : 0 ≤ m
  · left
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hxy) hm) c
  · right
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonpos_left (Subtype.coe_le_coe.mpr hxy)
        (le_of_not_ge hm)) c

/-- The common returned-word length chosen in the PL normalization is
positive. -/
theorem piecewiseLinear_returnedLength_pos
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) :
    0 < G.L := by
  simpa [PiecewiseLinearSelectedFixedGap.L,
    LeastNormalizedPiecewiseLinearCounterexample.L,
    NormalizedPiecewiseLinearCounterexample.L] using
      piecewiseLinearNormalizationExponent_pos G.system.base.fixedW

/-! ## Exact returned product and the generic product eigeninput -/

/-- Since the returned factors commute, the `N`th iterate of their product
is the returned product with common exponent `G.L * N`. -/
theorem piecewiseLinear_returnedProduct_iterate_eq
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) (N : ℕ) :
    iterateMap G.R N = returnedProductMap G.P G.Q (G.L * N) := by
  have hcomm : Commute G.P G.Q := G.system.commute
  have hreturned : G.R = returnedProductMap G.P G.Q G.L := by
    rfl
  rw [hreturned]
  change (G.P^[G.L] ∘ G.Q^[G.L])^[N] =
    G.P^[G.L * N] ∘ G.Q^[G.L * N]
  rw [(hcomm.iterate_iterate G.L G.L).comp_iterate,
    Function.iterate_mul, Function.iterate_mul]

/-- Every returned product occurring after multiplication of the common
word length remains finite-piece weakly monotone. -/
theorem piecewiseLinear_returnedProduct_finitePieceMonotone
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) (N : ℕ) :
    FinitePieceMonotone (returnedProductMap G.P G.Q (G.L * N)) := by
  have hP : FinitePieceMonotone G.P :=
    finitePiecePL_finitePieceMonotone G.system.finitePieceP
  have hQ : FinitePieceMonotone G.Q :=
    finitePiecePL_finitePieceMonotone G.system.finitePieceQ
  exact (hP.iterateMap (G.L * N)).comp
    (hQ.iterateMap (G.L * N))

/-- Exactness of the selected returned product produces a positive iterate
carrying a two-branch horseshoe. -/
theorem piecewiseLinear_exactProduct_eventualHorseshoe
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : PiecewiseLinearIrrationalExactSystem G) :
    ∃ N : ℕ, 0 < N ∧
      Nonempty (TwoBranchHorseshoe (iterateMap G.R N)) := by
  have hR : G.R = returnedProductMap G.P G.Q G.L := by
    simpa [iterateMap] using
      (piecewiseLinear_returnedProduct_iterate_eq G 1)
  have hRcont : Continuous G.R := by
    rw [hR]
    simpa using
      (piecewiseLinear_returnedProduct_finitePieceMonotone G 1).continuous
  exact twoBranchHorseshoe_iterate_exists_of_topologicallyExact
    hRcont E.exact_R

/-- Transport the preceding horseshoe through the exact product-iterate
identity, putting it in the form consumed by the weak-lap resolvent. -/
theorem piecewiseLinear_returnedProduct_eventualHorseshoe
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : PiecewiseLinearIrrationalExactSystem G) :
    ∃ N : ℕ, 0 < N ∧
      Nonempty (TwoBranchHorseshoe
        (returnedProductMap G.P G.Q (G.L * N))) := by
  obtain ⟨N, hN, H⟩ :=
    piecewiseLinear_exactProduct_eventualHorseshoe E
  refine ⟨N, hN, ?_⟩
  rw [← piecewiseLinear_returnedProduct_iterate_eq G N]
  exact H

/-- The exact returned product, its transported horseshoe, and the generic
piecewise-monotone product eigeninput built from the weak-lap resolvent. -/
structure PiecewiseLinearProductEigenAdapterData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (_E : PiecewiseLinearIrrationalExactSystem G) where
  N : ℕ
  N_pos : 0 < N
  horseshoe : TwoBranchHorseshoe
    (returnedProductMap G.P G.Q (G.L * N))
  productEigen : PiecewiseMonotoneProductEigenData
    G.P G.Q (G.L * N)

/-- The weak-lap resolvent fills the generic product-eigenmeasure package at
the transported exponent. -/
theorem piecewiseLinear_productEigenAdapterData_exists
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : PiecewiseLinearIrrationalExactSystem G) :
    Nonempty (PiecewiseLinearProductEigenAdapterData E) := by
  obtain ⟨N, hN, ⟨H⟩⟩ :=
    piecewiseLinear_returnedProduct_eventualHorseshoe E
  have hP : FinitePieceMonotone G.P :=
    finitePiecePL_finitePieceMonotone G.system.finitePieceP
  have hQ : FinitePieceMonotone G.Q :=
    finitePiecePL_finitePieceMonotone G.system.finitePieceQ
  have hK : 0 < G.L * N :=
    Nat.mul_pos (piecewiseLinear_returnedLength_pos G) hN
  have hProduct : FinitePieceMonotone
      (returnedProductMap G.P G.Q (G.L * N)) :=
    piecewiseLinear_returnedProduct_finitePieceMonotone G N
  let partitionP : MonotonicityPartition G.P :=
    Classical.choice hP.2
  let partitionQ : MonotonicityPartition G.Q :=
    Classical.choice hQ.2
  let partitionProduct : MonotonicityPartition
      (returnedProductMap G.P G.Q (G.L * N)) :=
    Classical.choice hProduct.2
  obtain ⟨lambda, measure, hlambda, hprobability, hnoAtoms,
      heigen⟩ :=
    transferMeasure_eigenprobability_exists_of_horseshoe hProduct H
  exact ⟨{
    N := N
    N_pos := hN
    horseshoe := H
    productEigen := {
      finitePiece_P := hP
      finitePiece_Q := hQ
      commute := G.system.commute
      L_pos := hK
      partitionP := partitionP
      partitionQ := partitionQ
      partitionProduct := partitionProduct
      lambda := lambda
      one_lt_lambda := hlambda
      measure := measure
      probability := hprobability.measure_univ
      noAtoms := hnoAtoms
      product_eigen := heigen partitionProduct } }⟩

/-! ## Generic joint eigenmeasure and exact variation -/

/-- The generic simultaneous eigenmeasure construction, upgraded by
exactness of `G.P` to the two full-support injective-set scaling laws. -/
structure PiecewiseLinearSimultaneousVariationAdapterData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (D : PiecewiseLinearProductEigenAdapterData E) where
  construction : SimultaneousEigenmeasureConstruction D.productEigen
  scaled :
    IsScaledProbability G.P construction.variation.scaleP
        construction.variation.measure ∧
      IsScaledProbability G.Q construction.variation.scaleQ
        construction.variation.measure

/-- Apply the generic finite-dimensional joint-eigenvector theorem, exact
variation naturality, and the exactness-to-full-support theorem. -/
theorem piecewiseLinear_simultaneousVariationAdapterData_exists
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (D : PiecewiseLinearProductEigenAdapterData E) :
    Nonempty (PiecewiseLinearSimultaneousVariationAdapterData D) := by
  obtain ⟨construction⟩ :=
    simultaneousEigenmeasureConstruction_exists D.productEigen
  have hscaled :=
    construction.variation.isScaled_of_exactP E.exact_P
  exact ⟨⟨construction, hscaled⟩⟩

/-! ## Elementary common distribution coordinate -/

/-- The normalized cumulative distribution of an atomless full-support
probability, recorded as an increasing self-homeomorphism of the interval. -/
structure PiecewiseLinearFullSupportDistributionCoordinateData
    (measure : Measure I) where
  coordinate : I ≃ₜ I
  coordinate_strictMono : StrictMono coordinate
  coordinate_apply : ∀ x : I,
    (coordinate x : ℝ) =
      (measure (Set.Icc leftEndpoint x)).toReal

/-- Elementary CDF lemma used by Boundary 7.  This statement is kept local
to the replacement adapter so importing the much larger legacy Parry file
is unnecessary. -/
theorem piecewiseLinear_fullSupportDistributionCoordinate_exists
    (measure : Measure I)
    (hprobability : measure Set.univ = 1)
    (hnoAtoms : ∀ x : I, measure {x} = 0)
    (hfullSupport : ∀ U : Set I,
      IsOpen U → U.Nonempty → measure U ≠ 0) :
    Nonempty (PiecewiseLinearFullSupportDistributionCoordinateData measure) := by
  let coordinateMap : IntervalMap := cdfCoordinate measure
  have hcontinuous : Continuous coordinateMap :=
    cdfCoordinate_continuous measure hprobability hnoAtoms
  have hstrictMono : StrictMono coordinateMap := by
    intro x y hxy
    have hopen : measure (Set.Ioo x y) ≠ 0 :=
      hfullSupport (Set.Ioo x y) isOpen_Ioo
        (Set.nonempty_Ioo.mpr hxy)
    have hclosed : measure (Set.Icc x y) ≠ 0 := by
      intro hzero
      apply hopen
      exact measure_mono_null Set.Ioo_subset_Icc_self hzero
    have hcoordinate_ne : coordinateMap x ≠ coordinateMap y := by
      intro heq
      apply hclosed
      have heq' : cdfCoordinate measure x = cdfCoordinate measure y := by
        simpa [coordinateMap] using heq
      rw [cdfCoordinate_interval_mass measure hprobability hnoAtoms hxy.le,
        heq']
      simp
    exact lt_of_le_of_ne (cdfCoordinate_monotone measure hxy.le)
      hcoordinate_ne
  have hsurjective : Function.Surjective coordinateMap :=
    cdfCoordinate_surjective measure hprobability hnoAtoms
  let coordinateEquiv : I ≃ I :=
    Equiv.ofBijective coordinateMap
      ⟨hstrictMono.injective, hsurjective⟩
  let coordinate : I ≃ₜ I :=
    Continuous.homeoOfEquivCompactToT2 (f := coordinateEquiv) (by
      change Continuous coordinateMap
      exact hcontinuous)
  refine ⟨{
    coordinate := coordinate
    coordinate_strictMono := ?_
    coordinate_apply := ?_ }⟩
  · change StrictMono coordinateMap
    exact hstrictMono
  · intro x
    change (cdfCoordinate measure x : ℝ) =
      (measure (Set.Icc leftEndpoint x)).toReal
    letI : IsProbabilityMeasure measure := ⟨hprobability⟩
    change ProbabilityTheory.cdf (measure.map Subtype.val) (x : ℝ) =
      (measure (Set.Icc leftEndpoint x)).toReal
    rw [ProbabilityTheory.unitInterval.cdf_eq_real measure x]
    rfl

/-- The common CDF and the two maps obtained by conjugating `G.P` and `G.Q`.
The generic injective-set scaling laws become constant absolute slopes. -/
structure PiecewiseLinearDistributionModelAdapterData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {D : PiecewiseLinearProductEigenAdapterData E}
    (V : PiecewiseLinearSimultaneousVariationAdapterData D) where
  distribution : PiecewiseLinearFullSupportDistributionCoordinateData
    V.construction.variation.measure
  modelP : IntervalMap
  modelQ : IntervalMap
  conjugatesP : ConjugatesPLCore distribution.coordinate G.P modelP
  conjugatesQ : ConjugatesPLCore distribution.coordinate G.Q modelQ
  slopeP : HasConstantAbsoluteSlopePLCore modelP
    V.construction.variation.scaleP
  slopeQ : HasConstantAbsoluteSlopePLCore modelQ
    V.construction.variation.scaleQ

/-- Build both conjugate models in the one elementary distribution
coordinate. -/
theorem piecewiseLinear_variation_distributionModels_adapter
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {D : PiecewiseLinearProductEigenAdapterData E}
    (V : PiecewiseLinearSimultaneousVariationAdapterData D) :
    Nonempty (PiecewiseLinearDistributionModelAdapterData V) := by
  let W := V.construction.variation
  let S : SimultaneousTransferEigenProbability G.P G.Q := {
    finitePiece_P := D.productEigen.finitePiece_P
    finitePiece_Q := D.productEigen.finitePiece_Q
    commute := D.productEigen.commute
    partitionP := D.productEigen.partitionP
    partitionQ := D.productEigen.partitionQ
    measure := W.measure
    probability := W.probability
    noAtoms := W.noAtoms
    scaleP := W.scaleP
    scaleQ := W.scaleQ
    scaleP_pos := W.scaleP_pos
    scaleQ_pos := W.scaleQ_pos
    transferP_eigen := W.transferP_eigen
    transferQ_eigen := W.transferQ_eigen }
  obtain ⟨distribution⟩ :=
    piecewiseLinear_fullSupportDistributionCoordinate_exists
      W.measure W.probability W.noAtoms V.scaled.1.2.2.1
  let X : DistributionQuotientData S.measure :=
    canonicalDistributionQuotientData S.measure S.probability S.noAtoms
  letI : IsProbabilityMeasure W.measure := ⟨W.probability⟩
  have hcoordinate :
      (distribution.coordinate : I → I) = X.coordinate := by
    funext x
    apply Subtype.ext
    rw [distribution.coordinate_apply]
    change (W.measure (Set.Icc leftEndpoint x)).toReal =
      ProbabilityTheory.cdf (W.measure.map Subtype.val) (x : ℝ)
    rw [ProbabilityTheory.unitInterval.cdf_eq_real W.measure x]
    rfl
  let modelP : IntervalMap := S.factorP X
  let modelQ : IntervalMap := S.factorQ X
  have hconjugatesP :
      ConjugatesPLCore distribution.coordinate G.P modelP := by
    intro x
    change distribution.coordinate (G.P x) =
      S.factorP X (distribution.coordinate x)
    rw [congrFun hcoordinate (G.P x), congrFun hcoordinate x]
    exact S.intertwines_factorP X x
  have hconjugatesQ :
      ConjugatesPLCore distribution.coordinate G.Q modelQ := by
    intro x
    change distribution.coordinate (G.Q x) =
      S.factorQ X (distribution.coordinate x)
    rw [congrFun hcoordinate (G.Q x), congrFun hcoordinate x]
    exact S.intertwines_factorQ X x
  have hslopeP : HasConstantAbsoluteSlopePLCore modelP W.scaleP := by
    refine ⟨S.continuous_factorP X, S.factorPartitionP X, ?_⟩
    intro a b hab
    exact S.factorP_affineOn_cell X hab
  have hslopeQ : HasConstantAbsoluteSlopePLCore modelQ W.scaleQ := by
    refine ⟨S.continuous_factorQ X, S.factorPartitionQ X, ?_⟩
    intro a b hab
    exact S.factorQ_affineOn_cell X hab
  exact ⟨{
    distribution := distribution
    modelP := modelP
    modelQ := modelQ
    conjugatesP := hconjugatesP
    conjugatesQ := hconjugatesQ
    slopeP := hslopeP
    slopeQ := hslopeQ }⟩

/-! ## Selected-germ scale recovery and Boundary 7 assembly -/

/-- A positive `C¹` right germ is strictly increasing on a nondegenerate
closed right interval.  This is the precise remnant of the local translation
coordinate needed after the global ray package has forgotten that local
coordinate. -/
theorem piecewiseLinear_rightGermC1BV_strictMono
    {T : IntervalMap} {p : I}
    (h : HasRightGermC1BV T p) :
    ∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q) := by
  rcases h with ⟨g, _hgBV⟩
  refine ⟨g.rightEnd, g.base_lt_rightEnd, ?_⟩
  have hcont : ContinuousOn g.extension
      (Set.Icc (p : ℝ) (g.rightEnd : ℝ)) :=
    g.contDiff_one.continuousOn.mono g.segment_subset
  have hstrict : StrictMonoOn g.extension
      (Set.Icc (p : ℝ) (g.rightEnd : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont fun x hx ↦
      g.deriv_pos x (interior_subset hx)
  intro x hx y hy hxy
  calc
    (T x : ℝ) = g.extension (x : ℝ) := g.agrees hx
    _ < g.extension (y : ℝ) := hstrict hx hy hxy
    _ = (T y : ℝ) := (g.agrees hy).symm

/-- A common increasing conjugacy transports a positive right germ to the
corresponding transformed base. -/
theorem piecewiseLinear_strictMonoNearBase_of_increasingConjugacy
    {T U : IntervalMap} {coordinate : I ≃ₜ I} {p : I}
    (hcoordinate : StrictMono coordinate)
    (hconjugates : ConjugatesPLCore coordinate T U)
    (hstrict : ∃ q : I, p < q ∧
      StrictMonoOn T (Set.Icc p q)) :
    ∃ q : I, coordinate p < q ∧
      StrictMonoOn U (Set.Icc (coordinate p) q) := by
  rcases hstrict with ⟨q, hpq, hstrict⟩
  refine ⟨coordinate q, hcoordinate hpq, ?_⟩
  intro x hx y hy hxy
  let x₀ : I := coordinate.symm x
  let y₀ : I := coordinate.symm y
  have hx₀ : x₀ ∈ Set.Icc p q := by
    constructor
    · apply hcoordinate.le_iff_le.mp
      simpa [x₀] using hx.1
    · apply hcoordinate.le_iff_le.mp
      simpa [x₀] using hx.2
  have hy₀ : y₀ ∈ Set.Icc p q := by
    constructor
    · apply hcoordinate.le_iff_le.mp
      simpa [y₀] using hy.1
    · apply hcoordinate.le_iff_le.mp
      simpa [y₀] using hy.2
  have hxy₀ : x₀ < y₀ := by
    apply hcoordinate.lt_iff_lt.mp
    simpa [x₀, y₀] using hxy
  calc
    U x = coordinate (T x₀) := by
      rw [hconjugates x₀]
      simp [x₀]
    _ < coordinate (T y₀) := hcoordinate (hstrict hx₀ hy₀ hxy₀)
    _ = U y := by
      rw [hconjugates y₀]
      simp [y₀]

/-- Constant absolute slope is preserved by finite iteration. -/
theorem piecewiseLinear_constantAbsoluteSlope_iterate
    {T : IntervalMap} {s : ℝ} (hs : 0 < s)
    (hT : HasConstantAbsoluteSlopePLCore T s) (n : ℕ) :
    HasConstantAbsoluteSlopePLCore (iterateMap T n) (s ^ n) := by
  exact constantAbsoluteSlopePLCore_iterate hs hT n

/-- A presented absolute slope is nonnegative. -/
private theorem constantAbsoluteSlopePLCore_nonneg_b7
    {T : IntervalMap} {s : ℝ}
    (hslope : HasConstantAbsoluteSlopePLCore T s) : 0 ≤ s := by
  rcases hslope with ⟨_hcont, p, hp⟩
  have hleftRight : leftEndpoint < rightEndpoint := by
    simp [leftEndpoint, rightEndpoint]
  obtain ⟨a, b, hab, _ha, _hb⟩ :=
    p.exists_adjacent_Ico hleftRight
  obtain ⟨m, _c, hm, _hformula⟩ := hp hab
  exact hm ▸ abs_nonneg m

private noncomputable def intervalVertices_b7 (p : RealPartition) (x y : I) : Finset ℝ :=
  p.points.filter fun z ↦ (x : ℝ) < z ∧ z < (y : ℝ)

private theorem constantAbsoluteSlopePLCore_dist_le_b7
    {T : IntervalMap} {s : ℝ} (hslope : HasConstantAbsoluteSlopePLCore T s) :
    ∀ x y : I, dist (T x) (T y) ≤ s * dist x y := by
  classical
  rcases hslope with ⟨_hcont, p, hp⟩
  have ordered : ∀ n : ℕ, ∀ x y : I, x ≤ y →
      (intervalVertices_b7 p x y).card = n →
      dist (T x) (T y) ≤ s * dist x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hxy hcard
      rcases hxy.eq_or_lt with rfl | hxylt
      · simp
      by_cases hempty : intervalVertices_b7 p x y = ∅
      · have hnone : ∀ z ∈ p.points,
            ¬((x : ℝ) < z ∧ z < (y : ℝ)) := by
          intro z hz hbetween
          have : z ∈ intervalVertices_b7 p x y := by
            exact Finset.mem_filter.mpr ⟨hz, hbetween⟩
          rw [hempty] at this
          simp at this
        obtain ⟨c, d, hcd, hsub⟩ := p.exists_adjacent_superset_plCore
          x.property y.property hxylt hnone
        obtain ⟨m, k, hm, hformula⟩ := hp hcd
        have hxcell : x ∈ intervalCell c d := hsub ⟨le_rfl, hxy⟩
        have hycell : y ∈ intervalCell c d := hsub ⟨hxy, le_rfl⟩
        rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq,
          hformula x hxcell, hformula y hycell]
        calc
          |m * (x : ℝ) + k - (m * (y : ℝ) + k)| =
              |m| * |(x : ℝ) - (y : ℝ)| := by
                rw [← abs_mul]
                congr 1
                ring
          _ = s * |(x : ℝ) - (y : ℝ)| := by rw [hm]
          _ ≤ s * |(x : ℝ) - (y : ℝ)| := le_rfl
      · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hz' := Finset.mem_filter.mp hz
        let zI : I := ⟨z, p.points_subset hz'.1⟩
        have hxz : x < zI := hz'.2.1
        have hzy : zI < y := hz'.2.2
        have hleftSub : intervalVertices_b7 p x zI ⊆ intervalVertices_b7 p x y := by
          intro w hw
          have hw' := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨hw'.1, hw'.2.1, hw'.2.2.trans hzy⟩
        have hrightSub : intervalVertices_b7 p zI y ⊆ intervalVertices_b7 p x y := by
          intro w hw
          have hw' := Finset.mem_filter.mp hw
          have hxzr : (x : ℝ) < (zI : ℝ) := hxz
          exact Finset.mem_filter.mpr ⟨hw'.1, hxzr.trans hw'.2.1, hw'.2.2⟩
        have hzWhole : z ∈ intervalVertices_b7 p x y := hz
        have hzNotLeft : z ∉ intervalVertices_b7 p x zI := by
          simp [intervalVertices_b7, zI]
        have hzNotRight : z ∉ intervalVertices_b7 p zI y := by
          simp [intervalVertices_b7, zI]
        have hleftCard : (intervalVertices_b7 p x zI).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hleftSub, fun heq ↦
              hzNotLeft (heq ▸ hzWhole)⟩)
        have hrightCard : (intervalVertices_b7 p zI y).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hrightSub, fun heq ↦
              hzNotRight (heq ▸ hzWhole)⟩)
        have hleft := ih _ hleftCard x zI hxz.le rfl
        have hright := ih _ hrightCard zI y hzy.le rfl
        have hdistadd : dist x zI + dist zI y = dist x y := by
          rw [Subtype.dist_eq, Subtype.dist_eq, Subtype.dist_eq,
            Real.dist_eq, Real.dist_eq, Real.dist_eq]
          have hxzr : (x : ℝ) ≤ (zI : ℝ) := hxz.le
          have hzyr : (zI : ℝ) ≤ (y : ℝ) := hzy.le
          have hxyr : (x : ℝ) ≤ (y : ℝ) := hxy
          rw [abs_of_nonpos (sub_nonpos.mpr hxzr),
            abs_of_nonpos (sub_nonpos.mpr hzyr),
            abs_of_nonpos (sub_nonpos.mpr hxyr)]
          ring
        calc
          dist (T x) (T y) ≤ dist (T x) (T zI) + dist (T zI) (T y) :=
            dist_triangle _ _ _
          _ ≤ s * dist x zI + s * dist zI y := add_le_add hleft hright
          _ = s * dist x y := by rw [← mul_add, hdistadd]
  intro x y
  rcases le_total x y with hxy | hyx
  · exact ordered _ x y hxy rfl
  · rw [dist_comm (T x), dist_comm x]
    exact ordered _ y x hyx rfl

/-- An exact finite-piece constant-absolute-slope interval map has scale
strictly bigger than one. -/
theorem piecewiseLinear_exact_constantAbsoluteSlope_scale_gt_one
    {T : IntervalMap} {scale : ℝ}
    (hexact : IsTopologicallyExact T)
    (hslope : HasConstantAbsoluteSlopePLCore T scale) :
    1 < scale := by
  have hscale_nonneg : 0 ≤ scale :=
    constantAbsoluteSlopePLCore_nonneg_b7 hslope
  have hstep := constantAbsoluteSlopePLCore_dist_le_b7 hslope
  have hiter : ∀ n : ℕ, ∀ x y : I,
      dist (iterateMap T n x) (iterateMap T n y) ≤
        scale ^ n * dist x y := by
    intro n
    induction n with
    | zero => simp [iterateMap]
    | succ n ih =>
        intro x y
        rw [iterateMap, Function.iterate_succ_apply',
          Function.iterate_succ_apply']
        calc
          dist (T (T^[n] x)) (T (T^[n] y)) ≤
              scale * dist (T^[n] x) (T^[n] y) := hstep _ _
          _ ≤ scale * (scale ^ n * dist x y) :=
            mul_le_mul_of_nonneg_left (ih x y) hscale_nonneg
          _ = scale ^ (n + 1) * dist x y := by rw [pow_succ]; ring
  by_contra hnot
  have hscale_one : scale ≤ 1 := le_of_not_gt hnot
  let U : Set I := Set.Ioo leftEndpoint rightEndpoint
  have hUne : U.Nonempty :=
    Set.nonempty_Ioo.mpr (by simp [leftEndpoint, rightEndpoint])
  obtain ⟨n, hn⟩ := hexact U isOpen_Ioo hUne
  have hleftImage : leftEndpoint ∈ iterateMap T n '' U := by
    rw [hn]
    exact Set.mem_univ _
  have hrightImage : rightEndpoint ∈ iterateMap T n '' U := by
    rw [hn]
    exact Set.mem_univ _
  rcases hleftImage with ⟨x, hxU, hx⟩
  rcases hrightImage with ⟨y, hyU, hy⟩
  have hxylt : dist x y < 1 := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    have hx0 : 0 < (x : ℝ) := hxU.1
    have hx1 : (x : ℝ) < 1 := hxU.2
    have hy0 : 0 < (y : ℝ) := hyU.1
    have hy1 : (y : ℝ) < 1 := hyU.2
    constructor <;> linarith
  have hpow : scale ^ n ≤ 1 :=
    pow_le_one₀ hscale_nonneg hscale_one
  have hbound := hiter n x y
  rw [hx, hy] at hbound
  have hends : dist leftEndpoint rightEndpoint = 1 := by
    rw [Subtype.dist_eq, Real.dist_eq]
    norm_num [leftEndpoint, rightEndpoint]
  have hscaled : scale ^ n * dist x y ≤ dist x y := by
    simpa using mul_le_mul_of_nonneg_right hpow
      (dist_nonneg : 0 ≤ dist x y)
  rw [hends] at hbound
  linarith

/-- A positive affine germ based at a fixed point, in the form used by the
selected-side rational-germ argument. -/
private def HasPositiveAffineRightGermB7
    (T : IntervalMap) (p : I) (scale : ℝ) : Prop :=
  ∃ q : I, p < q ∧ ∀ x ∈ Set.Icc p q,
    (T x : ℝ) = (p : ℝ) + scale * ((x : ℝ) - (p : ℝ))

private theorem positiveAffineRightGermB7_of_constantSlope
    {T : IntervalMap} {p : I} {scale : ℝ}
    (hpRight : p < rightEndpoint) (hfixed : T p = p)
    (hslope : HasConstantAbsoluteSlopePLCore T scale)
    (hstrict : ∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q)) :
    HasPositiveAffineRightGermB7 T p scale := by
  rcases hslope with ⟨_hcont, partition, hpartition⟩
  obtain ⟨a, b, hab, hap, hpb⟩ :=
    partition.exists_adjacent_Ico hpRight
  rcases hstrict with ⟨q₀, hpq₀, hstrict⟩
  obtain ⟨qReal, hpqReal, hqReal⟩ :=
    exists_between (lt_min hpb hpq₀)
  have hqb : qReal < b := hqReal.trans_le (min_le_left _ _)
  have hqq₀Real : qReal < (q₀ : ℝ) :=
    hqReal.trans_le (min_le_right _ _)
  let q : I := ⟨qReal, ⟨p.property.1.trans hpqReal.le,
    hqq₀Real.le.trans q₀.property.2⟩⟩
  have hpq : p < q := hpqReal
  have hqq₀ : q < q₀ := hqq₀Real
  obtain ⟨m, c, hmabs, hformula⟩ := hpartition hab
  have hpCell : p ∈ intervalCell a b := ⟨hap, hpb.le⟩
  have hqCell : q ∈ intervalCell a b :=
    ⟨hap.trans hpq.le, hqb.le⟩
  have hpStrict : p ∈ Set.Icc p q₀ := ⟨le_rfl, hpq₀.le⟩
  have hqStrict : q ∈ Set.Icc p q₀ := ⟨hpq.le, hqq₀.le⟩
  have hTpTq : T p < T q := hstrict hpStrict hqStrict hpq
  have hformulaP := hformula p hpCell
  have hformulaQ := hformula q hqCell
  have hmpos : 0 < m := by
    have hreal : (T p : ℝ) < (T q : ℝ) := hTpTq
    rw [hformulaP, hformulaQ] at hreal
    nlinarith
  have hms : m = scale := by
    rw [abs_of_pos hmpos] at hmabs
    exact hmabs
  refine ⟨q, hpq, ?_⟩
  intro x hx
  have hxCell : x ∈ intervalCell a b := by
    exact ⟨hap.trans hx.1,
      (show (x : ℝ) ≤ (q : ℝ) from hx.2).trans hqb.le⟩
  have hxformula := hformula x hxCell
  have hfixedReal : (T p : ℝ) = (p : ℝ) :=
    congrArg Subtype.val hfixed
  rw [hms] at hformulaP hxformula
  rw [hfixedReal] at hformulaP
  nlinarith

private theorem HasPositiveAffineRightGermB7.comp
    {A B : IntervalMap} {p : I} {a b : ℝ} (hb : 1 < b)
    (hA : HasPositiveAffineRightGermB7 A p a)
    (hB : HasPositiveAffineRightGermB7 B p b) :
    HasPositiveAffineRightGermB7 (A ∘ B) p (a * b) := by
  rcases hA with ⟨qA, hpA, hA⟩
  rcases hB with ⟨qB, hpB, hB⟩
  have hbpos : 0 < b := lt_trans (by norm_num) hb
  let bound : ℝ := (p : ℝ) + ((qA : ℝ) - (p : ℝ)) / b
  have hpbound : (p : ℝ) < bound := by
    dsimp [bound]
    exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr hpA) hbpos)
  obtain ⟨qReal, hpqReal, hqReal⟩ :=
    exists_between (lt_min (show (p : ℝ) < (qB : ℝ) from hpB)
      hpbound)
  have hqBReal : qReal < (qB : ℝ) :=
    hqReal.trans_le (min_le_left _ _)
  have hqBound : qReal < bound :=
    hqReal.trans_le (min_le_right _ _)
  have hbound_le_one : bound ≤ 1 := by
    dsimp [bound]
    have hdiv_le : ((qA : ℝ) - (p : ℝ)) / b ≤
        (qA : ℝ) - (p : ℝ) :=
      div_le_self (sub_nonneg.mpr hpA.le) hb.le
    linarith [qA.property.2]
  let q : I := ⟨qReal, ⟨p.property.1.trans hpqReal.le,
    hqBound.le.trans hbound_le_one⟩⟩
  refine ⟨q, hpqReal, ?_⟩
  intro x hx
  have hxB : x ∈ Set.Icc p qB :=
    ⟨hx.1, hx.2.trans hqBReal.le⟩
  have hBx := hB x hxB
  have hBxA : B x ∈ Set.Icc p qA := by
    constructor
    · change (p : ℝ) ≤ (B x : ℝ)
      rw [hBx]
      exact le_add_of_nonneg_right
        (mul_nonneg hbpos.le (sub_nonneg.mpr hx.1))
    · change (B x : ℝ) ≤ (qA : ℝ)
      rw [hBx]
      have hxq : (x : ℝ) ≤ qReal := hx.2
      dsimp [bound] at hqBound
      have hcross : b * (qReal - (p : ℝ)) <
          (qA : ℝ) - (p : ℝ) := by
        have := (lt_div_iff₀ hbpos).1 (by linarith :
          qReal - (p : ℝ) < ((qA : ℝ) - (p : ℝ)) / b)
        nlinarith
      nlinarith
  change (A (B x) : ℝ) = _
  rw [hA (B x) hBxA, hBx]
  ring

private theorem HasPositiveAffineRightGermB7.iterate_of_pos
    {A : IntervalMap} {p : I} {a : ℝ} (ha : 1 < a)
    (hA : HasPositiveAffineRightGermB7 A p a)
    {n : ℕ} (hn : 0 < n) :
    HasPositiveAffineRightGermB7 (iterateMap A n) p (a ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  clear hn
  induction k with
  | zero => simpa [iterateMap] using hA
  | succ k ih =>
      have hcomp := HasPositiveAffineRightGermB7.comp ha ih hA
      have hfun : iterateMap A (k + 1 + 1) =
          iterateMap A (k + 1) ∘ A := by
        funext x
        exact Function.iterate_succ_apply A (k + 1) x
      rw [hfun]
      simpa [pow_succ] using hcomp

/-- If two maps commute with the locally eventually onto map `W`, agreement
on one nondegenerate selected-side closed interval determines them globally. -/
private theorem eq_of_local_eq_of_commute_of_localEventualOnto_b7
    {W F H : IntervalMap} {p q : I}
    (hcover : HasLocalEventualOntoPL W p)
    (hpq : p < q)
    (hFcomm : Commute F W) (hHcomm : Commute H W)
    (hlocal : ∀ x ∈ Set.Icc p q, F x = H x) :
    F = H := by
  obtain ⟨n, hn⟩ := hcover q hpq
  funext y
  have hy : y ∈ iterateMap W n '' Set.Icc p q := by
    rw [hn]
    exact Set.mem_univ y
  obtain ⟨x, hx, hxy⟩ := hy
  calc
    F y = F (iterateMap W n x) := congrArg F hxy.symm
    _ = iterateMap W n (F x) := (hFcomm.iterate_right n).eq x
    _ = iterateMap W n (H x) := congrArg (iterateMap W n) (hlocal x hx)
    _ = H (iterateMap W n x) := (hHcomm.iterate_right n).eq x |>.symm
    _ = H y := congrArg H hxy

/-- Equal positive powers of the two transformed returned slopes make the
two positive affine germs equal.  Pulling that equality back through the
common increasing coordinate gives the rational selected-germ relation;
finite arrival and LEO then globalize it to the alternative excluded by the
exact irrational system. -/
theorem piecewiseLinear_transformedScales_independent
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : PiecewiseLinearIrrationalExactSystem G)
    {coordinate : I ≃ₜ I} {Abar Bbar : IntervalMap} {a b : ℝ}
    (hcoordinate : StrictMono coordinate)
    (hconjugatesA : ConjugatesPLCore coordinate G.A Abar)
    (hconjugatesB : ConjugatesPLCore coordinate G.B Bbar)
    (hslopeA : HasConstantAbsoluteSlopePLCore Abar a)
    (hslopeB : HasConstantAbsoluteSlopePLCore Bbar b)
    (hAstrict : ∃ q : I, coordinate G.p < q ∧
      StrictMonoOn Abar (Set.Icc (coordinate G.p) q))
    (hBstrict : ∃ q : I, coordinate G.p < q ∧
      StrictMonoOn Bbar (Set.Icc (coordinate G.p) q))
    (ha : 1 < a) (hb : 1 < b)
    : MultiplicativelyIndependent a b := by
  intro m n hm hn hscale
  let pbar : I := coordinate G.p
  have hpbarRight : pbar < rightEndpoint := by
    exact (hcoordinate G.p_lt_c).trans_le (coordinate G.c).property.2
  have hAbarFixed : Abar pbar = pbar := by
    calc
      Abar pbar = coordinate (G.A G.p) :=
        (hconjugatesA G.p).symm
      _ = pbar := congrArg coordinate
        (piecewiseLinear_return_fixes_A_p G)
  have hBbarFixed : Bbar pbar = pbar := by
    calc
      Bbar pbar = coordinate (G.B G.p) :=
        (hconjugatesB G.p).symm
      _ = pbar := congrArg coordinate
        (piecewiseLinear_return_fixes_B_p G)
  have hAgerm : HasPositiveAffineRightGermB7 Abar pbar a :=
    positiveAffineRightGermB7_of_constantSlope hpbarRight
      hAbarFixed hslopeA hAstrict
  have hBgerm : HasPositiveAffineRightGermB7 Bbar pbar b :=
    positiveAffineRightGermB7_of_constantSlope hpbarRight
      hBbarFixed hslopeB hBstrict
  have hAmgerm := hAgerm.iterate_of_pos ha hm
  have hBngerm := hBgerm.iterate_of_pos hb hn
  obtain ⟨qA, hpqA, hAm⟩ := hAmgerm
  obtain ⟨qB, hpqB, hBn⟩ := hBngerm
  let qbar : I := min qA qB
  have hpqbar : pbar < qbar := lt_min hpqA hpqB
  have hmodelEqual : Set.EqOn (iterateMap Abar m)
      (iterateMap Bbar n) (Set.Icc pbar qbar) := by
    intro x hx
    apply Subtype.ext
    rw [hAm x ⟨hx.1, hx.2.trans (min_le_left _ _)⟩,
      hBn x ⟨hx.1, hx.2.trans (min_le_right _ _)⟩, hscale]
  let q : I := coordinate.symm qbar
  have hpq : G.p < q := by
    apply hcoordinate.lt_iff_lt.mp
    simpa [pbar, q] using hpqbar
  let leftExponent : ℕ := G.L * m
  let rightExponent : ℕ := G.L * n
  have hleftExponent : 0 < leftExponent :=
    Nat.mul_pos (piecewiseLinear_returnedLength_pos G) hm
  have hrightExponent : 0 < rightExponent :=
    Nat.mul_pos (piecewiseLinear_returnedLength_pos G) hn
  have hlocal : ∀ x ∈ Set.Icc G.p q,
      iterateMap G.P leftExponent x = iterateMap G.Q rightExponent x := by
    intro x hx
    change (G.P^[G.L * m]) x = (G.Q^[G.L * n]) x
    rw [Function.iterate_mul, Function.iterate_mul]
    change iterateMap G.A m x = iterateMap G.B n x
    apply coordinate.injective
    rw [conjugatesPLCore_iterate hconjugatesA m x,
      conjugatesPLCore_iterate hconjugatesB n x]
    apply hmodelEqual
    constructor
    · exact hcoordinate.monotone hx.1
    · have hupper := hcoordinate.monotone hx.2
      simpa [q] using hupper
  have hleftCommutes : Commute (iterateMap G.P leftExponent) G.W := by
    change Commute (G.P^[leftExponent]) ((G.P ∘ G.Q)^[2])
    exact ((Function.Commute.refl G.P).comp_right G.system.commute).iterate_iterate
      leftExponent 2
  have hrightCommutes : Commute (iterateMap G.Q rightExponent) G.W := by
    change Commute (G.Q^[rightExponent]) ((G.P ∘ G.Q)^[2])
    exact (G.system.commute.symm.comp_right
      (Function.Commute.refl G.Q)).iterate_iterate rightExponent 2
  let directed : PiecewiseLinearDirectedReturnData G :=
    piecewiseLinear_directedStateReturn G
  let prepared : PreparedPiecewiseLinearCounterexample G :=
    piecewiseLinear_finiteArrivalAndLEO G directed
  have hglobal : iterateMap G.P leftExponent =
      iterateMap G.Q rightExponent :=
    eq_of_local_eq_of_commute_of_localEventualOnto_b7
      prepared.local_eventual_onto hpq hleftCommutes hrightCommutes hlocal
  exact E.no_positive_iterate
    ⟨leftExponent, rightExponent, hleftExponent, hrightExponent, hglobal⟩

/-- Exactness makes the one-step model scales expanding.  The two returned
positive affine germs share the transformed selected base, so dependence of
their `G.L`th-power slopes would force a forbidden common positive iterate. -/
theorem piecewiseLinear_distributionModels_adapter_scales
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {D : PiecewiseLinearProductEigenAdapterData E}
    {V : PiecewiseLinearSimultaneousVariationAdapterData D}
    (C : PiecewiseLinearDistributionModelAdapterData V) :
    1 < V.construction.variation.scaleP ∧
      1 < V.construction.variation.scaleQ ∧
      MultiplicativelyIndependent
        (V.construction.variation.scaleP ^ G.L)
        (V.construction.variation.scaleQ ^ G.L) := by
  let W := V.construction.variation
  have hexactP : IsTopologicallyExact C.modelP :=
    exact_of_conjugatesPLCore C.conjugatesP E.exact_P
  have hexactQ : IsTopologicallyExact C.modelQ :=
    exact_of_conjugatesPLCore C.conjugatesQ E.exact_Q
  have hscaleP : 1 < W.scaleP :=
    piecewiseLinear_exact_constantAbsoluteSlope_scale_gt_one
      hexactP C.slopeP
  have hscaleQ : 1 < W.scaleQ :=
    piecewiseLinear_exact_constantAbsoluteSlope_scale_gt_one
      hexactQ C.slopeQ
  have hL : 0 < G.L := piecewiseLinear_returnedLength_pos G
  have hAslope : HasConstantAbsoluteSlopePLCore
      (iterateMap C.modelP G.L) (W.scaleP ^ G.L) :=
    piecewiseLinear_constantAbsoluteSlope_iterate
      W.scaleP_pos C.slopeP G.L
  have hBslope : HasConstantAbsoluteSlopePLCore
      (iterateMap C.modelQ G.L) (W.scaleQ ^ G.L) :=
    piecewiseLinear_constantAbsoluteSlope_iterate
      W.scaleQ_pos C.slopeQ G.L
  have hconjugatesA : ConjugatesPLCore C.distribution.coordinate G.A
      (iterateMap C.modelP G.L) := by
    simpa [PiecewiseLinearSelectedFixedGap.A,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.A,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.A,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearA] using
        conjugatesPLCore_iterate C.conjugatesP G.L
  have hconjugatesB : ConjugatesPLCore C.distribution.coordinate G.B
      (iterateMap C.modelQ G.L) := by
    simpa [PiecewiseLinearSelectedFixedGap.B,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.B,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.B,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearB] using
        conjugatesPLCore_iterate C.conjugatesQ G.L
  have hAstrictSource : ∃ q : I, G.p < q ∧
      StrictMonoOn G.A (Set.Icc G.p q) :=
    piecewiseLinear_rightGermC1BV_strictMono
      (piecewiseLinear_A_hasRightGermC1BV G)
  have hBstrictSource : ∃ q : I, G.p < q ∧
      StrictMonoOn G.B (Set.Icc G.p q) :=
    piecewiseLinear_rightGermC1BV_strictMono
      (piecewiseLinear_B_hasRightGermC1BV G)
  have hAstrict :=
    piecewiseLinear_strictMonoNearBase_of_increasingConjugacy
      C.distribution.coordinate_strictMono hconjugatesA hAstrictSource
  have hBstrict :=
    piecewiseLinear_strictMonoNearBase_of_increasingConjugacy
      C.distribution.coordinate_strictMono hconjugatesB hBstrictSource
  have hreturnedA : 1 < W.scaleP ^ G.L :=
    one_lt_pow₀ hscaleP hL.ne'
  have hreturnedB : 1 < W.scaleQ ^ G.L :=
    one_lt_pow₀ hscaleQ hL.ne'
  have hindependent : MultiplicativelyIndependent
      (W.scaleP ^ G.L) (W.scaleQ ^ G.L) :=
    piecewiseLinear_transformedScales_independent E
      C.distribution.coordinate_strictMono hconjugatesA hconjugatesB
      hAslope hBslope hAstrict hBstrict hreturnedA hreturnedB
  exact ⟨hscaleP, hscaleQ, hindependent⟩

/-- Boundary 7 rebuilt solely through the generic piecewise-monotone
spectral theorem and an elementary full-support distribution coordinate. -/
theorem piecewiseLinear_jointEigenmeasure_commonCoordinate
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : PiecewiseLinearIrrationalExactSystem G) :
    Nonempty (PiecewiseLinearConstantSlopeSystem E) := by
  obtain ⟨D⟩ := piecewiseLinear_productEigenAdapterData_exists E
  obtain ⟨V⟩ := piecewiseLinear_simultaneousVariationAdapterData_exists D
  obtain ⟨C⟩ := piecewiseLinear_variation_distributionModels_adapter V
  obtain ⟨hscaleP, hscaleQ, hindependent⟩ :=
    piecewiseLinear_distributionModels_adapter_scales C
  let scaleP : ℝ := V.construction.variation.scaleP
  let scaleQ : ℝ := V.construction.variation.scaleQ
  have hcomm : Commute C.modelP C.modelQ :=
    commute_of_conjugatesPLCore C.conjugatesP C.conjugatesQ
      G.system.commute
  have hexactP : IsTopologicallyExact C.modelP :=
    exact_of_conjugatesPLCore C.conjugatesP E.exact_P
  have hexactQ : IsTopologicallyExact C.modelQ :=
    exact_of_conjugatesPLCore C.conjugatesQ E.exact_Q
  have hexactA : IsTopologicallyExact (iterateMap C.modelP G.L) := by
    apply exact_of_conjugatesPLCore
      (conjugatesPLCore_iterate C.conjugatesP G.L)
    simpa [PiecewiseLinearSelectedFixedGap.A,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.A,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.A,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearA] using E.exact_A
  have hexactB : IsTopologicallyExact (iterateMap C.modelQ G.L) := by
    apply exact_of_conjugatesPLCore
      (conjugatesPLCore_iterate C.conjugatesQ G.L)
    simpa [PiecewiseLinearSelectedFixedGap.B,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.B,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.B,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearB] using E.exact_B
  have hexactR : IsTopologicallyExact
      (iterateMap C.modelP G.L ∘ iterateMap C.modelQ G.L) := by
    apply exact_of_conjugatesPLCore
      (conjugatesPLCore_comp
        (conjugatesPLCore_iterate C.conjugatesP G.L)
        (conjugatesPLCore_iterate C.conjugatesQ G.L))
    simpa [PiecewiseLinearSelectedFixedGap.R,
      PiecewiseLinearSelectedFixedGap.P,
      PiecewiseLinearSelectedFixedGap.Q,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.R,
      LeastNormalizedPiecewiseLinearCounterexample.P,
      LeastNormalizedPiecewiseLinearCounterexample.Q,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.R,
      NormalizedPiecewiseLinearCounterexample.P,
      NormalizedPiecewiseLinearCounterexample.Q,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearR, piecewiseLinearA, piecewiseLinearB] using E.exact_R
  exact ⟨{
    coordinate := C.distribution.coordinate
    coordinate_strictMono := C.distribution.coordinate_strictMono
    modelP := C.modelP
    modelQ := C.modelQ
    conjugatesP := C.conjugatesP
    conjugatesQ := C.conjugatesQ
    scaleP := scaleP
    scaleQ := scaleQ
    one_lt_scaleP := hscaleP
    one_lt_scaleQ := hscaleQ
    slopeP := C.slopeP
    slopeQ := C.slopeQ
    commute := hcomm
    exact_P := hexactP
    exact_Q := hexactQ
    exact_A := hexactA
    exact_B := hexactB
    exact_R := hexactR
    returned_scales_independent := hindependent }⟩
/-- Pull a common fixed point back through a common conjugacy. -/
theorem commonFixedPoint_of_conjugatesPLCore
    {P Q Pbar Qbar : IntervalMap} (θ : I ≃ₜ I)
    (hP : ConjugatesPLCore θ P Pbar)
    (hQ : ConjugatesPLCore θ Q Qbar)
    (hfixed : HasCommonFixedPoint Pbar Qbar) :
    HasCommonFixedPoint P Q := by
  rcases hfixed with ⟨y, hyP, hyQ⟩
  refine ⟨θ.symm y, ?_, ?_⟩
  · apply θ.injective
    calc
      θ (P (θ.symm y)) = Pbar (θ (θ.symm y)) := hP _
      _ = Pbar y := congrArg Pbar (θ.apply_symm_apply y)
      _ = y := hyP
      _ = θ (θ.symm y) := (θ.apply_symm_apply y).symm
  · apply θ.injective
    calc
      θ (Q (θ.symm y)) = Qbar (θ (θ.symm y)) := hQ _
      _ = Qbar y := congrArg Qbar (θ.apply_symm_apply y)
      _ = y := hyQ
      _ = θ (θ.symm y) := (θ.apply_symm_apply y).symm

/-! ## Common Markov set, substitutions, and original-phase lift -/

/-- Consecutive vertices in a finite subset of the interval. -/
def PiecewiseLinearFinsetAdjacent (K : Finset I) (x y : I) : Prop :=
  x ∈ K ∧ y ∈ K ∧ x < y ∧
    ∀ z ∈ K, ¬(x < z ∧ z < y)

/-- A common Markov vertex set for two returned maps. -/
def IsPiecewiseLinearCommonMarkovSet
    (A B : IntervalMap) (K : Finset I) : Prop :=
  leftEndpoint ∈ K ∧ rightEndpoint ∈ K ∧
    (∀ x ∈ K, A x ∈ K) ∧
    (∀ x ∈ K, B x ∈ K) ∧
    ∀ ⦃x y : I⦄, PiecewiseLinearFinsetAdjacent K x y →
      (IsAffineOn A (Set.Icc x y) ∧
        IsStrictlyMonotoneOn A (Set.Icc x y)) ∧
      (IsAffineOn B (Set.Icc x y) ∧
        IsStrictlyMonotoneOn B (Set.Icc x y))

/-- The finite common Markov package at the transformed selected base. -/
structure PiecewiseLinearCommonMarkovPackage
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) where
  K : Finset I
  base_mem : M.coordinate G.p ∈ K
  markov : IsPiecewiseLinearCommonMarkovSet M.A M.B K

/-- The full forward orbit of the intrinsic vertex-value set is finite. -/
def HasFinitePostvertexSet (T : IntervalMap) : Prop :=
  (⋃ n : ℕ, iterateMap T n '' vertexValues T).Finite

/-! The following private one-sided germ calculus is the intrinsic vertex
infrastructure needed for the forward composition inclusion.  It is stated in
terms of strict monotonicity. -/

private inductive PLCoreDirection where
  | inc
  | dec
  deriving DecidableEq

private def PLCoreDirection.Holds (d : PLCoreDirection) (T : IntervalMap)
    (s : Set I) : Prop :=
  match d with
  | .inc => StrictMonoOn T s
  | .dec => StrictAntiOn T s

private def PLCoreDirection.mul :
    PLCoreDirection → PLCoreDirection → PLCoreDirection
  | .inc, .inc => .inc
  | .inc, .dec => .dec
  | .dec, .inc => .dec
  | .dec, .dec => .inc

private def HasLeftPLCoreDirection (d : PLCoreDirection)
    (T : IntervalMap) (x : I) : Prop :=
  ∃ a : I, a < x ∧ d.Holds T (Set.Icc a x)

private def HasRightPLCoreDirection (d : PLCoreDirection)
    (T : IntervalMap) (x : I) : Prop :=
  ∃ b : I, x < b ∧ d.Holds T (Set.Icc x b)

/-- A finite partition has a cell containing a terminal interval on the left
of any non-left-endpoint. -/
private theorem RealPartition.exists_left_cell_plCore
    (p : RealPartition) {x : I} (hx : leftEndpoint < x) :
    ∃ a : I, ∃ c d : ℝ, a < x ∧ p.Adjacent c d ∧
      Set.Icc a x ⊆ intervalCell c d := by
  classical
  let lower := p.points.filter fun z ↦ z < (x : ℝ)
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    have hx0 : (0 : ℝ) < x := hx
    simp [lower, p.zero_mem, hx0]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  have ha' := Finset.mem_filter.mp ha
  let aI : I := ⟨a, p.points_subset ha'.1⟩
  have hax : aI < x := ha'.2
  have hnone : ∀ z ∈ p.points, ¬(a < z ∧ z < (x : ℝ)) := by
    intro z hz hbetween
    have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hbetween.2⟩
    have hza : z ≤ a := by simpa using hamax z hzlower
    exact (not_lt_of_ge hza) hbetween.1
  obtain ⟨c, d, hcd, hsub⟩ := p.exists_adjacent_superset
    aI.property x.property hax hnone
  exact ⟨aI, c, d, hax, hcd, fun _ hz ↦ hsub hz⟩

/-- Right-sided counterpart of `exists_left_cell_plCore`. -/
private theorem RealPartition.exists_right_cell_plCore
    (p : RealPartition) {x : I} (hx : x < rightEndpoint) :
    ∃ b : I, ∃ c d : ℝ, x < b ∧ p.Adjacent c d ∧
      Set.Icc x b ⊆ intervalCell c d := by
  classical
  let upper := p.points.filter fun z ↦ (x : ℝ) < z
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have hx1 : (x : ℝ) < 1 := hx
    simp [upper, p.one_mem, hx1]
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have hb' := Finset.mem_filter.mp hb
  let bI : I := ⟨b, p.points_subset hb'.1⟩
  have hxb : x < bI := hb'.2
  have hnone : ∀ z ∈ p.points, ¬((x : ℝ) < z ∧ z < b) := by
    intro z hz hbetween
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hbetween.1⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hbetween.2
  obtain ⟨c, d, hcd, hsub⟩ := p.exists_adjacent_superset
    x.property bI.property hxb hnone
  exact ⟨bI, c, d, hxb, hcd, fun _ hz ↦ hsub hz⟩

private theorem hasLeftPLCoreDirection_of_pl
    {T : IntervalMap} (hflat : ¬HasFlatInterval T)
    (hPL : FinitePiecePL T) {x : I} (hx : leftEndpoint < x) :
    ∃ d, HasLeftPLCoreDirection d T x := by
  obtain ⟨p, hp⟩ := finitePiecePL_noFlat_finiteStrictLaps hPL hflat
  obtain ⟨a, c, d, hax, hcd, hsub⟩ := p.exists_left_cell_plCore hx
  rcases hp hcd with hmono | hanti
  · exact ⟨.inc, a, hax, hmono.mono hsub⟩
  · exact ⟨.dec, a, hax, hanti.mono hsub⟩

private theorem hasRightPLCoreDirection_of_pl
    {T : IntervalMap} (hflat : ¬HasFlatInterval T)
    (hPL : FinitePiecePL T) {x : I} (hx : x < rightEndpoint) :
    ∃ d, HasRightPLCoreDirection d T x := by
  obtain ⟨p, hp⟩ := finitePiecePL_noFlat_finiteStrictLaps hPL hflat
  obtain ⟨b, c, d, hxb, hcd, hsub⟩ := p.exists_right_cell_plCore hx
  rcases hp hcd with hmono | hanti
  · exact ⟨.inc, b, hxb, hmono.mono hsub⟩
  · exact ⟨.dec, b, hxb, hanti.mono hsub⟩

private theorem exists_left_Icc_subset_of_mem_nhds_plCore
    {a x : I} (hax : a < x) {s : Set I} (hs : s ∈ nhds x) :
    ∃ a' : I, a < a' ∧ a' < x ∧ Set.Icc a' x ⊆ s := by
  obtain ⟨l, hl, hls⟩ := exists_Ioc_subset_of_mem_nhds' hs hax
  obtain ⟨a', hla', ha'x⟩ := exists_between hl.2
  refine ⟨a', hl.1.trans_lt hla', ha'x, ?_⟩
  intro z hz
  exact hls ⟨hla'.trans_le hz.1, hz.2⟩

private theorem exists_right_Icc_subset_of_mem_nhds_plCore
    {x b : I} (hxb : x < b) {s : Set I} (hs : s ∈ nhds x) :
    ∃ b' : I, x < b' ∧ b' < b ∧ Set.Icc x b' ⊆ s := by
  obtain ⟨r, hr, hrs⟩ := exists_Ico_subset_of_mem_nhds' hs hxb
  obtain ⟨b', hxb', hb'r⟩ := exists_between hr.1
  refine ⟨b', hxb', hb'r.trans_le hr.2, ?_⟩
  intro z hz
  exact hrs ⟨hz.1, hz.2.trans_lt hb'r⟩

private theorem leftPLCoreDirection_ne
    {T : IntervalMap} {x : I} :
    ¬(HasLeftPLCoreDirection .inc T x ∧
      HasLeftPLCoreDirection .dec T x) := by
  rintro ⟨⟨a, hax, hmono⟩, ⟨b, hbx, hanti⟩⟩
  obtain ⟨z, hz, hzx⟩ := exists_between (max_lt hax hbx)
  have hza : a ≤ z := (le_max_left a b).trans hz.le
  have hzb : b ≤ z := (le_max_right a b).trans hz.le
  have hzxmono : T z < T x :=
    hmono ⟨hza, hzx.le⟩ ⟨hax.le, le_rfl⟩ hzx
  have hzxanti : T x < T z :=
    hanti ⟨hzb, hzx.le⟩ ⟨hbx.le, le_rfl⟩ hzx
  exact lt_asymm hzxmono hzxanti

private theorem rightPLCoreDirection_ne
    {T : IntervalMap} {x : I} :
    ¬(HasRightPLCoreDirection .inc T x ∧
      HasRightPLCoreDirection .dec T x) := by
  rintro ⟨⟨a, hxa, hmono⟩, ⟨b, hxb, hanti⟩⟩
  obtain ⟨z, hxz, hz⟩ := exists_between (lt_min hxa hxb)
  have hza : z ≤ a := hz.le.trans (min_le_left a b)
  have hzb : z ≤ b := hz.le.trans (min_le_right a b)
  have hxzmono : T x < T z :=
    hmono ⟨le_rfl, hxa.le⟩ ⟨hxz.le, hza⟩ hxz
  have hxzanti : T z < T x :=
    hanti ⟨le_rfl, hxb.le⟩ ⟨hxz.le, hzb⟩ hxz
  exact lt_asymm hxzmono hxzanti

private theorem PLCoreDirection.Holds.comp
    {U T : IntervalMap} {s t : Set I} {dU dT : PLCoreDirection}
    (hU : dU.Holds U t) (hT : dT.Holds T s)
    (hmap : MapsTo T s t) :
    (dU.mul dT).Holds (U ∘ T) s := by
  cases dU <;> cases dT
  · exact StrictMonoOn.comp hU hT hmap
  · exact StrictMonoOn.comp_strictAntiOn hU hT hmap
  · exact StrictAntiOn.comp_strictMonoOn hU hT hmap
  · exact StrictAntiOn.comp hU hT hmap

private theorem leftPLCoreDirection_comp_of_inc
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : PLCoreDirection}
    (hT : HasLeftPLCoreDirection .inc T x)
    (hU : HasLeftPLCoreDirection d U (T x)) :
    HasLeftPLCoreDirection (d.mul .inc) (U ∘ T) x := by
  obtain ⟨a, hax, hmono⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Ioi c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hc)
  obtain ⟨a', haa', ha'x, hsub⟩ :=
    exists_left_Icc_subset_of_mem_nhds_plCore hax hnear
  have hdom : Set.Icc a' x ⊆ Set.Icc a x := by
    intro z hz
    exact ⟨haa'.le.trans hz.1, hz.2⟩
  have hTdir := hmono.mono hdom
  have hmap : MapsTo T (Set.Icc a' x) (Set.Icc c (T x)) := by
    intro z hz
    refine ⟨(hsub hz).le, ?_⟩
    exact hTdir.monotoneOn hz ⟨ha'x.le, le_rfl⟩ hz.2
  exact ⟨a', ha'x, hUdir.comp hTdir hmap⟩

private theorem leftPLCoreDirection_comp_of_dec
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : PLCoreDirection}
    (hT : HasLeftPLCoreDirection .dec T x)
    (hU : HasRightPLCoreDirection d U (T x)) :
    HasLeftPLCoreDirection (d.mul .dec) (U ∘ T) x := by
  obtain ⟨a, hax, hanti⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Iio c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hc)
  obtain ⟨a', haa', ha'x, hsub⟩ :=
    exists_left_Icc_subset_of_mem_nhds_plCore hax hnear
  have hdom : Set.Icc a' x ⊆ Set.Icc a x := by
    intro z hz
    exact ⟨haa'.le.trans hz.1, hz.2⟩
  have hTdir := hanti.mono hdom
  have hmap : MapsTo T (Set.Icc a' x) (Set.Icc (T x) c) := by
    intro z hz
    refine ⟨?_, (hsub hz).le⟩
    exact hTdir.antitoneOn hz ⟨ha'x.le, le_rfl⟩ hz.2
  exact ⟨a', ha'x, hUdir.comp hTdir hmap⟩

private theorem rightPLCoreDirection_comp_of_inc
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : PLCoreDirection}
    (hT : HasRightPLCoreDirection .inc T x)
    (hU : HasRightPLCoreDirection d U (T x)) :
    HasRightPLCoreDirection (d.mul .inc) (U ∘ T) x := by
  obtain ⟨b, hxb, hmono⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Iio c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hc)
  obtain ⟨b', hxb', hb'b, hsub⟩ :=
    exists_right_Icc_subset_of_mem_nhds_plCore hxb hnear
  have hdom : Set.Icc x b' ⊆ Set.Icc x b := by
    intro z hz
    exact ⟨hz.1, hz.2.trans hb'b.le⟩
  have hTdir := hmono.mono hdom
  have hmap : MapsTo T (Set.Icc x b') (Set.Icc (T x) c) := by
    intro z hz
    refine ⟨?_, (hsub hz).le⟩
    exact hTdir.monotoneOn ⟨le_rfl, hxb'.le⟩ hz hz.1
  exact ⟨b', hxb', hUdir.comp hTdir hmap⟩

private theorem rightPLCoreDirection_comp_of_dec
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : PLCoreDirection}
    (hT : HasRightPLCoreDirection .dec T x)
    (hU : HasLeftPLCoreDirection d U (T x)) :
    HasRightPLCoreDirection (d.mul .dec) (U ∘ T) x := by
  obtain ⟨b, hxb, hanti⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Ioi c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hc)
  obtain ⟨b', hxb', hb'b, hsub⟩ :=
    exists_right_Icc_subset_of_mem_nhds_plCore hxb hnear
  have hdom : Set.Icc x b' ⊆ Set.Icc x b := by
    intro z hz
    exact ⟨hz.1, hz.2.trans hb'b.le⟩
  have hTdir := hanti.mono hdom
  have hmap : MapsTo T (Set.Icc x b') (Set.Icc c (T x)) := by
    intro z hz
    refine ⟨(hsub hz).le, ?_⟩
    exact hTdir.antitoneOn ⟨le_rfl, hxb'.le⟩ hz hz.1
  exact ⟨b', hxb', hUdir.comp hTdir hmap⟩

private theorem leftPLCoreDirection_unique
    {T : IntervalMap} {x : I} {d e : PLCoreDirection}
    (hd : HasLeftPLCoreDirection d T x)
    (he : HasLeftPLCoreDirection e T x) : d = e := by
  cases d <;> cases e
  · rfl
  · exact False.elim (leftPLCoreDirection_ne ⟨hd, he⟩)
  · exact False.elim (leftPLCoreDirection_ne ⟨he, hd⟩)
  · rfl

private theorem rightPLCoreDirection_unique
    {T : IntervalMap} {x : I} {d e : PLCoreDirection}
    (hd : HasRightPLCoreDirection d T x)
    (he : HasRightPLCoreDirection e T x) : d = e := by
  cases d <;> cases e
  · rfl
  · exact False.elim (rightPLCoreDirection_ne ⟨hd, he⟩)
  · exact False.elim (rightPLCoreDirection_ne ⟨he, hd⟩)
  · rfl

private theorem genuineTurn_iff_exists_plCore_directions_ne
    {T : IntervalMap} {x : I} :
    IsGenuineTurn T x ↔
      ∃ dL dR : PLCoreDirection,
        HasLeftPLCoreDirection dL T x ∧
          HasRightPLCoreDirection dR T x ∧ dL ≠ dR := by
  constructor
  · rintro ⟨a, b, hax, hxb, hturn⟩
    rcases hturn with ⟨hmono, hanti⟩ | ⟨hanti, hmono⟩
    · exact ⟨.inc, .dec, ⟨a, hax, hmono⟩,
        ⟨b, hxb, hanti⟩, by decide⟩
    · exact ⟨.dec, .inc, ⟨a, hax, hanti⟩,
        ⟨b, hxb, hmono⟩, by decide⟩
  · rintro ⟨dL, dR, ⟨a, hax, hL⟩, ⟨b, hxb, hR⟩, hne⟩
    cases dL <;> cases dR
    · exact False.elim (hne rfl)
    · exact ⟨a, b, hax, hxb, Or.inl ⟨hL, hR⟩⟩
    · exact ⟨a, b, hax, hxb, Or.inr ⟨hL, hR⟩⟩
    · exact False.elim (hne rfl)

private theorem genuineTurn_iff_plCore_direction_ne
    {T : IntervalMap} {x : I} {dL dR : PLCoreDirection}
    (hL : HasLeftPLCoreDirection dL T x)
    (hR : HasRightPLCoreDirection dR T x) :
    IsGenuineTurn T x ↔ dL ≠ dR := by
  rw [genuineTurn_iff_exists_plCore_directions_ne]
  constructor
  · rintro ⟨eL, eR, heL, heR, hne⟩ heq
    have hLe : dL = eL := leftPLCoreDirection_unique hL heL
    have hRe : dR = eR := rightPLCoreDirection_unique hR heR
    exact hne (hLe ▸ hRe ▸ heq)
  · intro hne
    exact ⟨dL, dR, hL, hR, hne⟩

private theorem leftEndpoint_lt_image_of_leftPLCore_inc
    {T : IntervalMap} {x : I}
    (h : HasLeftPLCoreDirection .inc T x) : leftEndpoint < T x := by
  obtain ⟨a, hax, hmono⟩ := h
  have hlt : T a < T x :=
    hmono ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax
  exact lt_of_le_of_lt (T a).property.1 hlt

private theorem image_lt_rightEndpoint_of_leftPLCore_dec
    {T : IntervalMap} {x : I}
    (h : HasLeftPLCoreDirection .dec T x) : T x < rightEndpoint := by
  obtain ⟨a, hax, hanti⟩ := h
  have hlt : T x < T a :=
    hanti ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax
  exact lt_of_lt_of_le hlt (T a).property.2

private theorem image_lt_rightEndpoint_of_rightPLCore_inc
    {T : IntervalMap} {x : I}
    (h : HasRightPLCoreDirection .inc T x) : T x < rightEndpoint := by
  obtain ⟨b, hxb, hmono⟩ := h
  have hlt : T x < T b :=
    hmono ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb
  exact lt_of_lt_of_le hlt (T b).property.2

private theorem leftEndpoint_lt_image_of_rightPLCore_dec
    {T : IntervalMap} {x : I}
    (h : HasRightPLCoreDirection .dec T x) : leftEndpoint < T x := by
  obtain ⟨b, hxb, hanti⟩ := h
  have hlt : T b < T x :=
    hanti ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb
  exact lt_of_le_of_lt (T b).property.1 hlt

private def HasPLCoreGerms (T : IntervalMap) : Prop :=
  Continuous T ∧
    (∀ {x : I}, leftEndpoint < x →
      ∃ d, HasLeftPLCoreDirection d T x) ∧
    (∀ {x : I}, x < rightEndpoint →
      ∃ d, HasRightPLCoreDirection d T x)

private theorem hasPLCoreGerms_of_finitePiecePL
    {T : IntervalMap} (hflat : ¬HasFlatInterval T)
    (hPL : FinitePiecePL T) : HasPLCoreGerms T := by
  refine ⟨hPL.1, ?_, ?_⟩
  · intro x hx
    exact hasLeftPLCoreDirection_of_pl hflat hPL hx
  · intro x hx
    exact hasRightPLCoreDirection_of_pl hflat hPL hx

/-- At an interior point, a turn of a composite is exactly a turn of the
inner map or a turn of the outer map at the intermediate value. -/
private theorem genuineTurn_comp_iff_plCore
    {U T : IntervalMap} (hUG : HasPLCoreGerms U)
    (hTG : HasPLCoreGerms T) {x : I}
    (hxL : leftEndpoint < x) (hxR : x < rightEndpoint) :
    IsGenuineTurn (U ∘ T) x ↔
      IsGenuineTurn T x ∨ IsGenuineTurn U (T x) := by
  obtain ⟨dL, hTL⟩ := hTG.2.1 hxL
  obtain ⟨dR, hTR⟩ := hTG.2.2 hxR
  cases dL <;> cases dR
  · have hyL : leftEndpoint < T x :=
      leftEndpoint_lt_image_of_leftPLCore_inc hTL
    have hyR : T x < rightEndpoint :=
      image_lt_rightEndpoint_of_rightPLCore_inc hTR
    obtain ⟨eL, hUL⟩ := hUG.2.1 hyL
    obtain ⟨eR, hUR⟩ := hUG.2.2 hyR
    have hCL := leftPLCoreDirection_comp_of_inc hTG.1 hTL hUL
    have hCR := rightPLCoreDirection_comp_of_inc hTG.1 hTR hUR
    constructor
    · intro hturn
      right
      apply (genuineTurn_iff_plCore_direction_ne hUL hUR).mpr
      have hne := (genuineTurn_iff_plCore_direction_ne hCL hCR).mp hturn
      cases eL <;> cases eR <;> simp_all [PLCoreDirection.mul]
    · rintro (hTturn | hUturn)
      · exact False.elim
          ((genuineTurn_iff_plCore_direction_ne hTL hTR).mp hTturn rfl)
      · apply (genuineTurn_iff_plCore_direction_ne hCL hCR).mpr
        have hne := (genuineTurn_iff_plCore_direction_ne hUL hUR).mp hUturn
        cases eL <;> cases eR <;> simp_all [PLCoreDirection.mul]
  · have hyL : leftEndpoint < T x :=
      leftEndpoint_lt_image_of_leftPLCore_inc hTL
    obtain ⟨e, hUL⟩ := hUG.2.1 hyL
    have hCL := leftPLCoreDirection_comp_of_inc hTG.1 hTL hUL
    have hCR := rightPLCoreDirection_comp_of_dec hTG.1 hTR hUL
    have hTturn : IsGenuineTurn T x :=
      (genuineTurn_iff_plCore_direction_ne hTL hTR).mpr (by decide)
    have hCturn : IsGenuineTurn (U ∘ T) x := by
      apply (genuineTurn_iff_plCore_direction_ne hCL hCR).mpr
      cases e <;> decide
    exact ⟨fun _ ↦ Or.inl hTturn, fun _ ↦ hCturn⟩
  · have hyR : T x < rightEndpoint :=
      image_lt_rightEndpoint_of_leftPLCore_dec hTL
    obtain ⟨e, hUR⟩ := hUG.2.2 hyR
    have hCL := leftPLCoreDirection_comp_of_dec hTG.1 hTL hUR
    have hCR := rightPLCoreDirection_comp_of_inc hTG.1 hTR hUR
    have hTturn : IsGenuineTurn T x :=
      (genuineTurn_iff_plCore_direction_ne hTL hTR).mpr (by decide)
    have hCturn : IsGenuineTurn (U ∘ T) x := by
      apply (genuineTurn_iff_plCore_direction_ne hCL hCR).mpr
      cases e <;> decide
    exact ⟨fun _ ↦ Or.inl hTturn, fun _ ↦ hCturn⟩
  · have hyR : T x < rightEndpoint :=
      image_lt_rightEndpoint_of_leftPLCore_dec hTL
    have hyL : leftEndpoint < T x :=
      leftEndpoint_lt_image_of_rightPLCore_dec hTR
    obtain ⟨eL, hUL⟩ := hUG.2.1 hyL
    obtain ⟨eR, hUR⟩ := hUG.2.2 hyR
    have hCL := leftPLCoreDirection_comp_of_dec hTG.1 hTL hUR
    have hCR := rightPLCoreDirection_comp_of_dec hTG.1 hTR hUL
    constructor
    · intro hturn
      right
      apply (genuineTurn_iff_plCore_direction_ne hUL hUR).mpr
      have hne := (genuineTurn_iff_plCore_direction_ne hCL hCR).mp hturn
      intro heq
      apply hne
      cases eL <;> cases eR <;> simp_all [PLCoreDirection.mul]
    · rintro (hTturn | hUturn)
      · exact False.elim
          ((genuineTurn_iff_plCore_direction_ne hTL hTR).mp hTturn rfl)
      · apply (genuineTurn_iff_plCore_direction_ne hCL hCR).mpr
        have hne := (genuineTurn_iff_plCore_direction_ne hUL hUR).mp hUturn
        intro heq
        apply hne
        cases eL <;> cases eR <;> simp_all [PLCoreDirection.mul]

private theorem vertexDomain_comp_subset_plCore
    {U T : IntervalMap} (hUG : HasPLCoreGerms U)
    (hTG : HasPLCoreGerms T) :
    vertexDomain (U ∘ T) ⊆
      vertexDomain T ∪ T ⁻¹' vertexDomain U := by
  intro x hx
  by_cases hxL0 : x = leftEndpoint
  · left
    simp [vertexDomain, hxL0]
  by_cases hxR0 : x = rightEndpoint
  · left
    simp [vertexDomain, hxR0]
  have hxL : leftEndpoint < x := by
    exact lt_of_le_of_ne
      (show leftEndpoint ≤ x from x.property.1) (Ne.symm hxL0)
  have hxR : x < rightEndpoint := by
    exact lt_of_le_of_ne
      (show x ≤ rightEndpoint from x.property.2) hxR0
  have hxturn : IsGenuineTurn (U ∘ T) x := by
    simpa [vertexDomain, genuineTurns, hxL0, hxR0] using hx
  rcases (genuineTurn_comp_iff_plCore hUG hTG hxL hxR).mp hxturn with
    hTturn | hUturn
  · left
    exact Or.inr hTturn
  · right
    exact Or.inr hUturn

/-- Vertex values of a composition occur either at an outer vertex value or
as the outer image of an inner vertex value. -/
theorem piecewiseLinear_vertexValues_comp
    {T U : IntervalMap}
    (hT : FinitePiecePL T) (hU : FinitePiecePL U)
    (hTflat : ¬HasFlatInterval T) (hUflat : ¬HasFlatInterval U) :
    vertexValues (U ∘ T) ⊆ vertexValues U ∪ U '' vertexValues T := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hx' := vertexDomain_comp_subset_plCore
    (hasPLCoreGerms_of_finitePiecePL hUflat hU)
    (hasPLCoreGerms_of_finitePiecePL hTflat hT) hx
  rcases hx' with hxT | hxU
  · right
    exact ⟨T x, ⟨x, hxT, rfl⟩, rfl⟩
  · left
    exact ⟨T x, hxU, rfl⟩

/-- One-sided PL germs are stable under composition. -/
private theorem hasPLCoreGerms_comp
    {U T : IntervalMap} (hUG : HasPLCoreGerms U)
    (hTG : HasPLCoreGerms T) : HasPLCoreGerms (U ∘ T) := by
  refine ⟨hUG.1.comp hTG.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hT⟩ := hTG.2.1 hx
    cases d
    · have hy : leftEndpoint < T x :=
        leftEndpoint_lt_image_of_leftPLCore_inc hT
      obtain ⟨e, hU⟩ := hUG.2.1 hy
      exact ⟨e.mul .inc, leftPLCoreDirection_comp_of_inc hTG.1 hT hU⟩
    · have hy : T x < rightEndpoint :=
        image_lt_rightEndpoint_of_leftPLCore_dec hT
      obtain ⟨e, hU⟩ := hUG.2.2 hy
      exact ⟨e.mul .dec, leftPLCoreDirection_comp_of_dec hTG.1 hT hU⟩
  · intro x hx
    obtain ⟨d, hT⟩ := hTG.2.2 hx
    cases d
    · have hy : T x < rightEndpoint :=
        image_lt_rightEndpoint_of_rightPLCore_inc hT
      obtain ⟨e, hU⟩ := hUG.2.2 hy
      exact ⟨e.mul .inc, rightPLCoreDirection_comp_of_inc hTG.1 hT hU⟩
    · have hy : leftEndpoint < T x :=
        leftEndpoint_lt_image_of_rightPLCore_dec hT
      obtain ⟨e, hU⟩ := hUG.2.1 hy
      exact ⟨e.mul .dec, rightPLCoreDirection_comp_of_dec hTG.1 hT hU⟩

private theorem hasPLCoreGerms_id : HasPLCoreGerms (id : IntervalMap) := by
  refine ⟨continuous_id, ?_, ?_⟩
  · intro x hx
    exact ⟨.inc, leftEndpoint, hx, strictMonoOn_id⟩
  · intro x hx
    exact ⟨.inc, rightEndpoint, hx, strictMonoOn_id⟩

private theorem hasPLCoreGerms_iterate
    {T : IntervalMap} (hG : HasPLCoreGerms T) (n : ℕ) :
    HasPLCoreGerms (iterateMap T n) := by
  induction n with
  | zero => simpa [iterateMap] using hasPLCoreGerms_id
  | succ n ih =>
      simpa only [iterateMap, Function.iterate_succ] using
        (hasPLCoreGerms_comp ih hG)

private theorem genuineTurn_of_image_eq_leftEndpoint_plCore
    {T : IntervalMap} (hG : HasPLCoreGerms T) {x : I}
    (hxL : leftEndpoint < x) (hxR : x < rightEndpoint)
    (hTx : T x = leftEndpoint) : IsGenuineTurn T x := by
  obtain ⟨dL, hL⟩ := hG.2.1 hxL
  obtain ⟨dR, hR⟩ := hG.2.2 hxR
  cases dL
  · exact False.elim (by
      have hpos := leftEndpoint_lt_image_of_leftPLCore_inc hL
      rw [hTx] at hpos
      exact lt_irrefl _ hpos)
  · cases dR
    · exact (genuineTurn_iff_plCore_direction_ne hL hR).mpr (by decide)
    · exact False.elim (by
        have hpos := leftEndpoint_lt_image_of_rightPLCore_dec hR
        rw [hTx] at hpos
        exact lt_irrefl _ hpos)

private theorem genuineTurn_of_image_eq_rightEndpoint_plCore
    {T : IntervalMap} (hG : HasPLCoreGerms T) {x : I}
    (hxL : leftEndpoint < x) (hxR : x < rightEndpoint)
    (hTx : T x = rightEndpoint) : IsGenuineTurn T x := by
  obtain ⟨dL, hL⟩ := hG.2.1 hxL
  obtain ⟨dR, hR⟩ := hG.2.2 hxR
  cases dL
  · cases dR
    · exact False.elim (by
        have hlt := image_lt_rightEndpoint_of_rightPLCore_inc hR
        rw [hTx] at hlt
        exact lt_irrefl _ hlt)
    · exact (genuineTurn_iff_plCore_direction_ne hL hR).mpr (by decide)
  · exact False.elim (by
      have hlt := image_lt_rightEndpoint_of_leftPLCore_dec hL
      rw [hTx] at hlt
      exact lt_irrefl _ hlt)

/-- Exact intrinsic vertex-domain composition, including the endpoint cases
lost by the forward-only inclusion. -/
private theorem vertexDomain_comp_of_germs_plCore
    {U T : IntervalMap} (hUG : HasPLCoreGerms U)
    (hTG : HasPLCoreGerms T) :
    vertexDomain (U ∘ T) = vertexDomain T ∪ T ⁻¹' vertexDomain U := by
  ext x
  by_cases hxL0 : x = leftEndpoint
  · subst x
    simp [vertexDomain]
  by_cases hxR0 : x = rightEndpoint
  · subst x
    simp [vertexDomain]
  have hxL : leftEndpoint < x := by
    exact lt_of_le_of_ne x.property.1 (Ne.symm hxL0)
  have hxR : x < rightEndpoint := by
    exact lt_of_le_of_ne x.property.2 hxR0
  simp only [vertexDomain, genuineTurns, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Set.mem_preimage, hxL0, hxR0, false_or]
  rw [genuineTurn_comp_iff_plCore hUG hTG hxL hxR]
  constructor
  · rintro (hTturn | hUturn)
    · exact Or.inl hTturn
    · exact Or.inr (Or.inr hUturn)
  · rintro (hTturn | hTxEnds | hUturn)
    · exact Or.inl hTturn
    · rcases hTxEnds with hTxL | hTxR
      · exact Or.inl
          (genuineTurn_of_image_eq_leftEndpoint_plCore hTG hxL hxR hTxL)
      · exact Or.inl
          (genuineTurn_of_image_eq_rightEndpoint_plCore hTG hxL hxR hTxR)
    · exact Or.inr hUturn

private theorem vertexValues_comp_of_germs_plCore
    {U T : IntervalMap} (hTonto : IsOnto T)
    (hUG : HasPLCoreGerms U) (hTG : HasPLCoreGerms T) :
    vertexValues (U ∘ T) = vertexValues U ∪ U '' vertexValues T := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [vertexDomain_comp_of_germs_plCore hUG hTG] at hx
    rcases hx with hxT | hxU
    · exact Or.inr ⟨T x, ⟨x, hxT, rfl⟩, rfl⟩
    · exact Or.inl ⟨T x, hxU, rfl⟩
  · rintro (hzU | hzT)
    · obtain ⟨y, hy, rfl⟩ := hzU
      obtain ⟨x, rfl⟩ := hTonto y
      refine ⟨x, ?_, rfl⟩
      rw [vertexDomain_comp_of_germs_plCore hUG hTG]
      exact Or.inr hy
    · obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hzT
      refine ⟨x, ?_, rfl⟩
      rw [vertexDomain_comp_of_germs_plCore hUG hTG]
      exact Or.inl hx

private theorem iUnion_Iio_succ_plCore {alpha : Type*}
    (F : ℕ → Set alpha) (n : ℕ) :
    (⋃ i ∈ Set.Iio (n + 1), F i) =
      (⋃ i ∈ Set.Iio n, F i) ∪ F n := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_union]
  constructor
  · rintro ⟨i, hi, hxi⟩
    by_cases hin : i = n
    · exact Or.inr (hin ▸ hxi)
    · left
      refine ⟨i, ?_, hxi⟩
      omega
  · rintro (⟨i, hi, hxi⟩ | hxn)
    · exact ⟨i, by omega, hxi⟩
    · exact ⟨n, by omega, hxn⟩

private theorem vertexValues_iterate_plCore
    {T : IntervalMap} (honto : IsOnto T) (hG : HasPLCoreGerms T)
    {n : ℕ} (hn : 0 < n) :
    vertexValues (iterateMap T n) =
      ⋃ i ∈ Set.Iio n, iterateMap T i '' vertexValues T := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hk : k = 0
      · subst k
        simp [iterateMap]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hprev := ih hkpos
        have hcomp := vertexValues_comp_of_germs_plCore honto
          (hasPLCoreGerms_iterate hG k) hG
        have hfun : iterateMap T (k + 1) = iterateMap T k ∘ T :=
          Function.iterate_succ T k
        rw [← hfun, hprev] at hcomp
        exact hcomp.trans (iUnion_Iio_succ_plCore
          (fun i ↦ iterateMap T i '' vertexValues T) k).symm

/-- The rectangular intrinsic-vertex identity for two commuting onto PL maps. -/
private theorem rectangular_vertex_identity_plCore
    {A B : IntervalMap} (hcomm : Commute A B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAG : HasPLCoreGerms A) (hBG : HasPLCoreGerms B)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (⋃ i ∈ Set.Iio m, iterateMap A i '' vertexValues A) ∪
        iterateMap A m '' (⋃ j ∈ Set.Iio n,
          iterateMap B j '' vertexValues B) =
      (⋃ j ∈ Set.Iio n, iterateMap B j '' vertexValues B) ∪
        iterateMap B n '' (⋃ i ∈ Set.Iio m,
          iterateMap A i '' vertexValues A) := by
  have hVA := vertexValues_iterate_plCore hAonto hAG hm
  have hVB := vertexValues_iterate_plCore hBonto hBG hn
  rw [← hVA, ← hVB]
  have hAmonto : IsOnto (iterateMap A m) :=
    Function.Surjective.iterate hAonto m
  have hBnonto : IsOnto (iterateMap B n) :=
    Function.Surjective.iterate hBonto n
  have hleft := vertexValues_comp_of_germs_plCore hBnonto
    (hasPLCoreGerms_iterate hAG m) (hasPLCoreGerms_iterate hBG n)
  have hright := vertexValues_comp_of_germs_plCore hAmonto
    (hasPLCoreGerms_iterate hBG n) (hasPLCoreGerms_iterate hAG m)
  have hmaps : iterateMap A m ∘ iterateMap B n =
      iterateMap B n ∘ iterateMap A m := by
    funext x
    exact hcomm.iterate_iterate m n x
  calc
    vertexValues (iterateMap A m) ∪
        iterateMap A m '' vertexValues (iterateMap B n) =
      vertexValues (iterateMap A m ∘ iterateMap B n) := hleft.symm
    _ = vertexValues (iterateMap B n ∘ iterateMap A m) :=
      congrArg vertexValues hmaps
    _ = vertexValues (iterateMap B n) ∪
        iterateMap B n '' vertexValues (iterateMap A m) := hright

private def postvertexValuesPLCore (T : IntervalMap) : Set I :=
  ⋃ n : ℕ, iterateMap T n '' vertexValues T

private def forwardOrbitPLCore (T : IntervalMap) (x : I) : Set I :=
  Set.range fun n : ℕ ↦ iterateMap T n x

private theorem postvertex_eq_biUnion_forwardOrbit_plCore
    (T : IntervalMap) :
    postvertexValuesPLCore T =
      ⋃ x ∈ vertexValues T, forwardOrbitPLCore T x := by
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx, hxy⟩ := hn
    subst y
    exact Set.mem_iUnion.mpr ⟨x,
      Set.mem_iUnion.mpr ⟨hx, ⟨n, rfl⟩⟩⟩
  · intro hy
    obtain ⟨x, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hx, horbit⟩ := Set.mem_iUnion.mp hy
    obtain ⟨n, hny⟩ := horbit
    subst y
    exact Set.mem_iUnion.mpr ⟨n, ⟨x, hx, rfl⟩⟩

private theorem forwardOrbitPLCore_finite_of_periodic
    {T : IntervalMap} {x : I} {d : ℕ} (hd : 0 < d)
    (hperiodic : iterateMap T d x = x) :
    (forwardOrbitPLCore T x).Finite := by
  classical
  let K : Finset I := (Finset.range d).image fun n ↦ iterateMap T n x
  apply K.finite_toSet.subset
  rintro y ⟨n, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨n % d, Finset.mem_range.mpr (Nat.mod_lt n hd), ?_⟩
  exact (show Function.IsPeriodicPt T d x from hperiodic).iterate_mod_apply n

private theorem forwardOrbitPLCore_finite_of_tail
    {T : IntervalMap} {x : I} {k : ℕ}
    (htail : (forwardOrbitPLCore T (iterateMap T k x)).Finite) :
    (forwardOrbitPLCore T x).Finite := by
  classical
  let K : Finset I := (Finset.range k).image fun n ↦ iterateMap T n x
  apply (K.finite_toSet.union htail).subset
  rintro y ⟨n, rfl⟩
  by_cases hnk : n < k
  · exact Or.inl (Finset.mem_image.mpr
      ⟨n, Finset.mem_range.mpr hnk, rfl⟩)
  · right
    refine ⟨n - k, ?_⟩
    change (T^[n - k]) ((T^[k]) x) = (T^[n]) x
    rw [← Function.iterate_add_apply]
    congr 1
    omega

private theorem forwardOrbitPLCore_iterate_infinite
    {T : IntervalMap} {x : I}
    (hx : (forwardOrbitPLCore T x).Infinite) (k : ℕ) :
    (forwardOrbitPLCore T (iterateMap T k x)).Infinite := by
  intro htail
  exact hx (forwardOrbitPLCore_finite_of_tail htail)

private theorem forwardOrbitPLCore_iterate_subset
    {T : IntervalMap} (x : I) (k : ℕ) :
    forwardOrbitPLCore T (iterateMap T k x) ⊆
      forwardOrbitPLCore T x := by
  rintro y ⟨n, rfl⟩
  refine ⟨n + k, ?_⟩
  change (T^[n + k]) x = (T^[n]) ((T^[k]) x)
  exact Function.iterate_add_apply T n k x

private theorem forwardOrbitPLCore_finite_of_eventually_periodic
    {T : IntervalMap} {x : I} {k d : ℕ} (hd : 0 < d)
    (hperiodic :
      iterateMap T d (iterateMap T k x) = iterateMap T k x) :
    (forwardOrbitPLCore T x).Finite := by
  exact forwardOrbitPLCore_finite_of_tail
    (forwardOrbitPLCore_finite_of_periodic hd hperiodic)

private theorem forwardOrbitPLCore_image_of_commute
    {A B : IntervalMap} (hcomm : Commute A B) (x : I) :
    forwardOrbitPLCore A (B x) = B '' forwardOrbitPLCore A x := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨iterateMap A n x, ⟨n, rfl⟩,
      (hcomm.iterate_left n x).symm⟩
  · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, hcomm.iterate_left n x⟩

private theorem forwardOrbitPLCore_infinite_image_of_commute
    {A B : IntervalMap} (hcomm : Commute A B)
    (hBfibers : ∀ y : I, (B ⁻¹' {y}).Finite) {x : I}
    (hx : (forwardOrbitPLCore A x).Infinite) :
    (forwardOrbitPLCore A (B x)).Infinite := by
  rw [forwardOrbitPLCore_image_of_commute hcomm x]
  intro himage
  apply hx
  apply Set.Finite.of_finite_fibers B himage
  intro y _hy
  exact (hBfibers y).subset Set.inter_subset_right

private theorem image_postvertex_or_vertex_or_periodic_plCore
    {A B : IntervalMap} (hcomm : Commute A B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAG : HasPLCoreGerms A) (hBG : HasPLCoreGerms B)
    (hVBfinite : (vertexValues B).Finite) {x : I}
    (hx : x ∈ postvertexValuesPLCore A) :
    B x ∈ postvertexValuesPLCore A ∨ B x ∈ vertexValues B ∨
      ∃ d : ℕ, 0 < d ∧ iterateMap A d (B x) = B x := by
  classical
  by_cases hpost : B x ∈ postvertexValuesPLCore A
  · exact Or.inl hpost
  by_cases hvert : B x ∈ vertexValues B
  · exact Or.inr (Or.inl hvert)
  right
  right
  obtain ⟨m₀, hm₀⟩ := Set.mem_iUnion.mp hx
  obtain ⟨v₀, hv₀, hv₀x⟩ := hm₀
  let N : ℕ → ℕ := fun k ↦ m₀ + 1 + k
  have hpreimage (k : ℕ) :
      B x ∈ iterateMap A (N k) '' vertexValues B := by
    have hNpos : 0 < N k := by dsimp [N]; omega
    have hrect :
        (⋃ i ∈ Set.Iio (N k), iterateMap A i '' vertexValues A) ∪
            iterateMap A (N k) '' vertexValues B =
          vertexValues B ∪ B ''
            (⋃ i ∈ Set.Iio (N k),
              iterateMap A i '' vertexValues A) := by
      simpa [iterateMap] using
        (rectangular_vertex_identity_plCore hcomm hAonto hBonto hAG hBG
          hNpos (show 0 < (1 : ℕ) by omega))
    have hxpartial :
        x ∈ ⋃ i ∈ Set.Iio (N k),
          iterateMap A i '' vertexValues A := by
      apply Set.mem_iUnion.mpr
      refine ⟨m₀, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · change m₀ < N k
        dsimp [N]
        omega
      · exact ⟨v₀, hv₀, hv₀x⟩
    have hxright :
        B x ∈ vertexValues B ∪ B ''
          (⋃ i ∈ Set.Iio (N k),
            iterateMap A i '' vertexValues A) :=
      Or.inr ⟨x, hxpartial, rfl⟩
    have hxleft :
        B x ∈ (⋃ i ∈ Set.Iio (N k),
          iterateMap A i '' vertexValues A) ∪
            iterateMap A (N k) '' vertexValues B := by
      rw [hrect]
      exact hxright
    rcases hxleft with hxold | hxnew
    · exfalso
      apply hpost
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxold
      obtain ⟨_hiN, hiimage⟩ := Set.mem_iUnion.mp hi
      exact Set.mem_iUnion.mpr ⟨i, hiimage⟩
    · exact hxnew
  let pick : ℕ → {v // v ∈ vertexValues B} := fun k ↦
    ⟨Classical.choose (hpreimage k),
      (Classical.choose_spec (hpreimage k)).1⟩
  have hpick (k : ℕ) : iterateMap A (N k) (pick k) = B x :=
    (Classical.choose_spec (hpreimage k)).2
  letI : Finite {v // v ∈ vertexValues B} := hVBfinite.to_subtype
  obtain ⟨k, l, hklne, hpickeq⟩ :=
    Finite.exists_ne_map_eq_of_infinite pick
  have hordered {r s : ℕ} (hrs : r < s) (heq : pick r = pick s) :
      ∃ d : ℕ, 0 < d ∧ iterateMap A d (B x) = B x := by
    refine ⟨s - r, Nat.sub_pos_of_lt hrs, ?_⟩
    change (A^[s - r]) (B x) = B x
    calc
      (A^[s - r]) (B x) =
          (A^[s - r]) ((A^[N r]) (pick r)) :=
        congrArg (A^[s - r]) (hpick r).symm
      _ = (A^[s - r + N r]) (pick r) :=
        (Function.iterate_add_apply A (s - r) (N r) (pick r)).symm
      _ = (A^[N s]) (pick s) := by
        have hexp : s - r + N r = N s := by
          dsimp [N]
          omega
        rw [hexp, heq]
      _ = B x := hpick s
  rcases lt_or_gt_of_ne hklne with hkl | hlk
  · exact hordered hkl hpickeq
  · exact hordered hlk hpickeq.symm

private theorem postvertexPLCore_iterate_mem
    {T : IntervalMap} {x : I} (hx : x ∈ postvertexValuesPLCore T)
    (k : ℕ) : iterateMap T k x ∈ postvertexValuesPLCore T := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  obtain ⟨v, hv, hvx⟩ := hn
  apply Set.mem_iUnion.mpr
  refine ⟨k + n, ⟨v, hv, ?_⟩⟩
  change (T^[k + n]) v = iterateMap T k x
  rw [Function.iterate_add_apply]
  exact congrArg (T^[k]) hvx

private theorem vertexValues_subset_postvertexPLCore (T : IntervalMap) :
    vertexValues T ⊆ postvertexValuesPLCore T := by
  intro x hx
  apply Set.mem_iUnion.mpr
  exact ⟨0, ⟨x, hx, by simp [iterateMap]⟩⟩

private theorem eventually_image_mem_postvertex_of_infinite_orbit_plCore
    {A B : IntervalMap} (hcomm : Commute A B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAG : HasPLCoreGerms A) (hBG : HasPLCoreGerms B)
    (hVBfinite : (vertexValues B).Finite)
    (hBfibers : ∀ y : I, (B ⁻¹' {y}).Finite) {x : I}
    (hxpost : x ∈ postvertexValuesPLCore A)
    (hxinfinite : (forwardOrbitPLCore A x).Infinite) :
    ∃ k : ℕ,
      iterateMap A k (B x) ∈ postvertexValuesPLCore A := by
  have hBxinfinite : (forwardOrbitPLCore A (B x)).Infinite :=
    forwardOrbitPLCore_infinite_image_of_commute hcomm hBfibers hxinfinite
  by_contra hnone
  push_neg at hnone
  have hnsubset : ¬forwardOrbitPLCore A (B x) ⊆ vertexValues B := by
    intro hsub
    exact hBxinfinite (hVBfinite.subset hsub)
  obtain ⟨z, ⟨k, hkz⟩, hznot⟩ := Set.not_subset.mp hnsubset
  have hxkpost : iterateMap A k x ∈ postvertexValuesPLCore A :=
    postvertexPLCore_iterate_mem hxpost k
  have hcommk : B (iterateMap A k x) = iterateMap A k (B x) :=
    (hcomm.iterate_left k x).symm
  rcases image_postvertex_or_vertex_or_periodic_plCore hcomm hAonto hBonto
      hAG hBG hVBfinite hxkpost with hpost | hvert | hperiodic
  · exact hnone k (hcommk ▸ hpost)
  · apply hznot
    rw [← hkz]
    change iterateMap A k (B x) ∈ vertexValues B
    rw [← hcommk]
    exact hvert
  · obtain ⟨d, hd, hfix⟩ := hperiodic
    have hfix' :
        iterateMap A d (iterateMap A k (B x)) =
          iterateMap A k (B x) := by
      simpa [hcommk] using hfix
    exact hBxinfinite
      (forwardOrbitPLCore_finite_of_eventually_periodic hd hfix')

private theorem RealPartition.exists_adjacent_plCore
    (p : RealPartition) : ∃ a b : ℝ, p.Adjacent a b := by
  classical
  let positive := p.points.filter fun x ↦ 0 < x
  have hpositive : positive.Nonempty := by
    refine ⟨1, ?_⟩
    simp [positive, p.one_mem]
  obtain ⟨b, hb, hbmin⟩ := positive.exists_min_image id hpositive
  have hb' := Finset.mem_filter.mp hb
  refine ⟨0, b, p.zero_mem, hb'.1, hb'.2, ?_⟩
  intro c hc hcb
  have hcpos : c ∈ positive := Finset.mem_filter.mpr ⟨hc, hcb.1⟩
  have hbc : b ≤ c := by simpa using hbmin c hcpos
  exact (not_lt_of_ge hbc) hcb.2

private theorem RealPartition.exists_cell_containing_plCore
    (p : RealPartition) (x : I) :
    ∃ a b : ℝ, p.Adjacent a b ∧ x ∈ intervalCell a b := by
  by_cases hx : x < rightEndpoint
  · obtain ⟨z, a, b, hxz, hab, hsub⟩ := p.exists_right_cell_plCore hx
    exact ⟨a, b, hab, hsub ⟨le_rfl, hxz.le⟩⟩
  · have hxeq : x = rightEndpoint := by
      apply Subtype.ext
      exact le_antisymm x.property.2 (le_of_not_gt hx)
    subst x
    have hleft : leftEndpoint < rightEndpoint := by
      simp [leftEndpoint, rightEndpoint]
    obtain ⟨z, a, b, hz, hab, hsub⟩ :=
      p.exists_left_cell_plCore hleft
    exact ⟨a, b, hab, hsub ⟨hz.le, le_rfl⟩⟩

private theorem constantAbsoluteSlopePLCore_finite_fibers
    {T : IntervalMap} {s : ℝ} (hs : 0 < s)
    (hT : HasConstantAbsoluteSlopePLCore T s) :
    ∀ y : I, (T ⁻¹' {y}).Finite := by
  classical
  rcases hT with ⟨_hcont, p, hp⟩
  let branchSlope : ℝ → ℝ → ℝ := fun a b ↦
    if h : p.Adjacent a b then Classical.choose (hp h) else 0
  let branchIntercept : ℝ → ℝ → ℝ := fun a b ↦
    if h : p.Adjacent a b then
      Classical.choose (Classical.choose_spec (hp h)) else 0
  have branch_spec {a b : ℝ} (h : p.Adjacent a b) :
      |branchSlope a b| = s ∧
        ∀ x ∈ intervalCell a b,
          (T x : ℝ) = branchSlope a b * (x : ℝ) +
            branchIntercept a b := by
    dsimp [branchSlope, branchIntercept]
    simp only [dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec (hp h))
  intro y
  let root : ℝ → ℝ → ℝ := fun a b ↦
    ((y : ℝ) - branchIntercept a b) / branchSlope a b
  let roots : Finset ℝ := p.points.biUnion fun a ↦
    p.points.image fun b ↦ root a b
  have hroots : ((roots : Finset ℝ) : Set ℝ).Finite := roots.finite_toSet
  have hcandidates : {x : I | (x : ℝ) ∈ roots}.Finite := by
    change (Subtype.val ⁻¹' (roots : Set ℝ)).Finite
    exact hroots.preimage (Set.injOn_of_injective Subtype.val_injective)
  apply hcandidates.subset
  intro x hx
  obtain ⟨a, b, hab, hcell⟩ := p.exists_cell_containing_plCore x
  have hspec := branch_spec hab
  have hm : branchSlope a b ≠ 0 := by
    intro hm0
    have hz : |branchSlope a b| = 0 := by rw [hm0, abs_zero]
    linarith [hspec.1]
  have hTy : T x = y := by simpa using hx
  have hval := congrArg Subtype.val hTy
  have hxroot : (x : ℝ) = root a b := by
    dsimp [root]
    apply (eq_div_iff hm).2
    rw [hspec.2 x hcell] at hval
    linarith
  change (x : ℝ) ∈ roots
  apply Finset.mem_biUnion.mpr
  refine ⟨a, hab.1, ?_⟩
  exact Finset.mem_image.mpr ⟨b, hab.2.1, hxroot.symm⟩

private theorem vertexDomain_finite_of_constantSlopePLCore
    {T : IntervalMap} {s : ℝ} (hs : 0 < s)
    (hT : HasConstantAbsoluteSlopePLCore T s) :
    (vertexDomain T).Finite := by
  classical
  rcases hT with ⟨_hcont, p, hp⟩
  let partitionPoints : Set I := {x | (x : ℝ) ∈ p.points}
  have hpartitionPoints : partitionPoints.Finite := by
    change (Subtype.val ⁻¹' (p.points : Set ℝ)).Finite
    exact p.points.finite_toSet.preimage
      (Set.injOn_of_injective Subtype.val_injective)
  have hturns : genuineTurns T ⊆ partitionPoints := by
    intro x hxturn
    by_contra hx
    have hxnot : (x : ℝ) ∉ p.points := by
      simpa [partitionPoints] using hx
    obtain ⟨c, d, hcd, hcx, hxd⟩ :=
      p.exists_adjacent_around_plCore x.property hxnot
    obtain ⟨m, k, hm, hformula⟩ := hp hcd
    have hmne : m ≠ 0 := by
      intro hm0
      have hz : |m| = 0 := by rw [hm0, abs_zero]
      linarith
    let cI : I := ⟨c, p.points_subset hcd.1⟩
    let dI : I := ⟨d, p.points_subset hcd.2.1⟩
    have hcxI : cI < x := hcx
    have hxdI : x < dI := hxd
    have hcell : IsStrictlyMonotoneOn T (intervalCell c d) := by
      rcases lt_or_gt_of_ne hmne with hmneg | hmpos
      · right
        intro u hu v hv huv
        apply Subtype.coe_lt_coe.mp
        rw [hformula u hu, hformula v hv]
        have huv' : (u : ℝ) < (v : ℝ) := huv
        nlinarith
      · left
        intro u hu v hv huv
        apply Subtype.coe_lt_coe.mp
        rw [hformula u hu, hformula v hv]
        have huv' : (u : ℝ) < (v : ℝ) := huv
        nlinarith
    have hsubL : Set.Icc cI x ⊆ intervalCell c d := by
      intro z hz
      exact ⟨hz.1, hz.2.trans hxdI.le⟩
    have hsubR : Set.Icc x dI ⊆ intervalCell c d := by
      intro z hz
      exact ⟨hcxI.le.trans hz.1, hz.2⟩
    rcases hcell with hmono | hanti
    · have hL : HasLeftPLCoreDirection .inc T x :=
        ⟨cI, hcxI, hmono.mono hsubL⟩
      have hR : HasRightPLCoreDirection .inc T x :=
        ⟨dI, hxdI, hmono.mono hsubR⟩
      exact ((genuineTurn_iff_plCore_direction_ne hL hR).mp hxturn) rfl
    · have hL : HasLeftPLCoreDirection .dec T x :=
        ⟨cI, hcxI, hanti.mono hsubL⟩
      have hR : HasRightPLCoreDirection .dec T x :=
        ⟨dI, hxdI, hanti.mono hsubR⟩
      exact ((genuineTurn_iff_plCore_direction_ne hL hR).mp hxturn) rfl
  change ({leftEndpoint, rightEndpoint} ∪ genuineTurns T).Finite
  exact (Set.toFinite {leftEndpoint, rightEndpoint}).union
    (hpartitionPoints.subset hturns)

private theorem vertexValues_finite_of_constantSlopePLCore
    {T : IntervalMap} {s : ℝ} (hs : 0 < s)
    (hT : HasConstantAbsoluteSlopePLCore T s) :
    (vertexValues T).Finite :=
  (vertexDomain_finite_of_constantSlopePLCore hs hT).image T

private theorem constantAbsoluteSlopePLCore_scale_unique
    {T : IntervalMap} {s t : ℝ}
    (hs : HasConstantAbsoluteSlopePLCore T s)
    (ht : HasConstantAbsoluteSlopePLCore T t) : s = t := by
  classical
  rcases hs with ⟨_hscont, ps, hps⟩
  rcases ht with ⟨_htcont, pt, hpt⟩
  let p : RealPartition :=
    { points := ps.points ∪ pt.points
      zero_mem := Finset.mem_union_left _ ps.zero_mem
      one_mem := Finset.mem_union_left _ ps.one_mem
      points_subset := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact ps.points_subset hx
        · exact pt.points_subset hx }
  obtain ⟨x, y, hxy⟩ := p.exists_adjacent_plCore
  have hxI : x ∈ I := p.points_subset hxy.1
  have hyI : y ∈ I := p.points_subset hxy.2.1
  have hnoneS : ∀ z ∈ ps.points, ¬(x < z ∧ z < y) := by
    intro z hz hbetween
    exact hxy.2.2.2 z (Finset.mem_union_left _ hz) hbetween
  have hnoneT : ∀ z ∈ pt.points, ¬(x < z ∧ z < y) := by
    intro z hz hbetween
    exact hxy.2.2.2 z (Finset.mem_union_right _ hz) hbetween
  obtain ⟨as, bs, habs, hsubS⟩ := ps.exists_adjacent_superset_plCore
    hxI hyI hxy.2.2.1 hnoneS
  obtain ⟨at₀, bt, habt, hsubT⟩ := pt.exists_adjacent_superset_plCore
    hxI hyI hxy.2.2.1 hnoneT
  obtain ⟨ms, cs, hms, hformulaS⟩ := hps habs
  obtain ⟨mt, ct, hmt, hformulaT⟩ := hpt habt
  let xI : I := ⟨x, hxI⟩
  let yI : I := ⟨y, hyI⟩
  have hxS := hformulaS xI (hsubS ⟨le_rfl, hxy.2.2.1.le⟩)
  have hyS := hformulaS yI (hsubS ⟨hxy.2.2.1.le, le_rfl⟩)
  have hxT := hformulaT xI (hsubT ⟨le_rfl, hxy.2.2.1.le⟩)
  have hyT := hformulaT yI (hsubT ⟨hxy.2.2.1.le, le_rfl⟩)
  have hm : ms = mt := by
    have hxyne : y - x ≠ 0 := sub_ne_zero.mpr hxy.2.2.1.ne'
    apply mul_right_cancel₀ hxyne
    linarith
  rw [← hms, ← hmt, hm]

private theorem constantSlopePLCore_maps_eqOn_interval_of_infinite
    {F G : IntervalMap} {s t : ℝ}
    (hF : HasConstantAbsoluteSlopePLCore F s)
    (hG : HasConstantAbsoluteSlopePLCore G t)
    {S : Set I} (hS : S.Infinite) (heq : Set.EqOn F G S) :
    ∃ J : ClosedSubinterval,
      J.Nondegenerate ∧ Set.EqOn F G J.carrier := by
  classical
  rcases hF with ⟨_hFcont, pF, hpF⟩
  rcases hG with ⟨_hGcont, pG, hpG⟩
  let p : RealPartition :=
    { points := pF.points ∪ pG.points
      zero_mem := Finset.mem_union_left _ pF.zero_mem
      one_mem := Finset.mem_union_left _ pF.one_mem
      points_subset := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact pF.points_subset hx
        · exact pG.points_subset hx }
  choose left right hadj hmem using
    fun x : I ↦ p.exists_cell_containing_plCore x
  let cell : I → (↥p.points × ↥p.points) := fun x ↦
    (⟨left x, (hadj x).1⟩, ⟨right x, (hadj x).2.1⟩)
  letI : Infinite S := hS.to_subtype
  obtain ⟨x, y, hxyne, hcell⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun z : S ↦ cell z.1)
  have hxyne' : x.1 ≠ y.1 := by
    intro h
    apply hxyne
    exact Subtype.ext h
  have hleft : left x.1 = left y.1 :=
    congrArg (fun q ↦ (q.1 : ℝ)) hcell
  have hright : right x.1 = right y.1 :=
    congrArg (fun q ↦ (q.2 : ℝ)) hcell
  let x₀ : I := min x.1 y.1
  let y₀ : I := max x.1 y.1
  have hxylt : x₀ < y₀ := min_lt_max.mpr hxyne'
  have hxcell : x₀ ∈ intervalCell (left x.1) (right x.1) := by
    rcases min_choice x.1 y.1 with hmin | hmin
    · simpa [x₀, hmin] using hmem x.1
    · simpa [x₀, hmin, hleft, hright] using hmem y.1
  have hycell : y₀ ∈ intervalCell (left x.1) (right x.1) := by
    rcases max_choice x.1 y.1 with hmax | hmax
    · simpa [y₀, hmax] using hmem x.1
    · simpa [y₀, hmax, hleft, hright] using hmem y.1
  have hnoneF : ∀ z ∈ pF.points,
      ¬((left x.1) < z ∧ z < right x.1) := by
    intro z hz hbetween
    exact (hadj x.1).2.2.2 z (Finset.mem_union_left _ hz) hbetween
  have hnoneG : ∀ z ∈ pG.points,
      ¬((left x.1) < z ∧ z < right x.1) := by
    intro z hz hbetween
    exact (hadj x.1).2.2.2 z (Finset.mem_union_right _ hz) hbetween
  have hleftI : left x.1 ∈ I := p.points_subset (hadj x.1).1
  have hrightI : right x.1 ∈ I := p.points_subset (hadj x.1).2.1
  obtain ⟨aF, bF, habF, hsubF⟩ := pF.exists_adjacent_superset_plCore
    hleftI hrightI (hadj x.1).2.2.1 hnoneF
  obtain ⟨aG, bG, habG, hsubG⟩ := pG.exists_adjacent_superset_plCore
    hleftI hrightI (hadj x.1).2.2.1 hnoneG
  obtain ⟨mF, cF, _hmF, hformulaF⟩ := hpF habF
  obtain ⟨mG, cG, _hmG, hformulaG⟩ := hpG habG
  have hxF := hformulaF x₀ (hsubF hxcell)
  have hyF := hformulaF y₀ (hsubF hycell)
  have hxG := hformulaG x₀ (hsubG hxcell)
  have hyG := hformulaG y₀ (hsubG hycell)
  have heqx : F x₀ = G x₀ := by
    rcases min_choice x.1 y.1 with hmin | hmin
    · simpa [x₀, hmin] using heq x.2
    · simpa [x₀, hmin] using heq y.2
  have heqy : F y₀ = G y₀ := by
    rcases max_choice x.1 y.1 with hmax | hmax
    · simpa [y₀, hmax] using heq x.2
    · simpa [y₀, hmax] using heq y.2
  have hvalx := congrArg Subtype.val heqx
  have hvaly := congrArg Subtype.val heqy
  rw [hxF, hxG] at hvalx
  rw [hyF, hyG] at hvaly
  have hm : mF = mG := by
    have hne : (y₀ : ℝ) - (x₀ : ℝ) ≠ 0 :=
      sub_ne_zero.mpr
        (ne_of_gt (show (x₀ : ℝ) < (y₀ : ℝ) from hxylt))
    apply mul_right_cancel₀ hne
    linarith
  have hc : cF = cG := by
    rw [hm] at hvalx
    linarith
  let J : ClosedSubinterval := ⟨x₀, y₀, hxylt.le⟩
  refine ⟨J, hxylt, ?_⟩
  intro z hz
  apply Subtype.ext
  have hzcell : z ∈ intervalCell (left x.1) (right x.1) := by
    exact ⟨hxcell.1.trans (show (x₀ : ℝ) ≤ (z : ℝ) from hz.1),
      (show (z : ℝ) ≤ (y₀ : ℝ) from hz.2).trans hycell.2⟩
  rw [hformulaF z (hsubF hzcell), hformulaG z (hsubG hzcell), hm, hc]

private theorem local_equality_global_of_exact_centralizer_plCore
    {F G R : IntervalMap} (hFR : Commute F R) (hGR : Commute G R)
    (hexact : IsTopologicallyExact R)
    {J : ClosedSubinterval} (hJ : J.Nondegenerate)
    (heq : Set.EqOn F G J.carrier) : F = G := by
  apply funext
  intro y
  let U : Set I := Set.Ioo J.left J.right
  have hUopen : IsOpen U := isOpen_Ioo
  have hUne : U.Nonempty := Set.nonempty_Ioo.mpr hJ
  obtain ⟨n, hn⟩ := hexact U hUopen hUne
  have hy : y ∈ iterateMap R n '' U := by
    rw [hn]
    exact Set.mem_univ y
  rcases hy with ⟨z, hz, rfl⟩
  change F ((R^[n]) z) = G ((R^[n]) z)
  rw [hFR.iterate_right n z, hGR.iterate_right n z]
  exact congrArg (iterateMap R n)
    (heq ⟨le_of_lt hz.1, le_of_lt hz.2⟩)

/-- Topological exactness of an interval self-map forces surjectivity. -/
private theorem onto_of_topologicallyExact_plCore
    {T : IntervalMap} (hexact : IsTopologicallyExact T) : IsOnto T := by
  let U : Set I := Set.Iio rightEndpoint
  have hUopen : IsOpen U := isOpen_Iio
  have hUne : U.Nonempty := by
    exact ⟨leftEndpoint, by simp [U, leftEndpoint, rightEndpoint]⟩
  obtain ⟨n, hn⟩ := hexact U hUopen hUne
  have hnpos : 0 < n := by
    by_contra hnnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnnot
    subst n
    have hright : rightEndpoint ∈ iterateMap T 0 '' U := by
      rw [hn]
      exact Set.mem_univ rightEndpoint
    rcases hright with ⟨x, hx, hxeq⟩
    have : x = rightEndpoint := by simpa [iterateMap] using hxeq
    subst x
    exact (lt_irrefl rightEndpoint) hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  intro y
  have hy : y ∈ iterateMap T (k + 1) '' U := by
    rw [hn]
    exact Set.mem_univ y
  rcases hy with ⟨x, _hx, hxy⟩
  refine ⟨iterateMap T k x, ?_⟩
  simpa only [iterateMap, Function.iterate_succ_apply'] using hxy

private theorem postvertexPLCore_finite_left
    {A B R : IntervalMap} {a b : ℝ}
    (hcomm : Commute A B) (hR : R = A ∘ B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAG : HasPLCoreGerms A) (hBG : HasPLCoreGerms B)
    (hexact : IsTopologicallyExact R)
    (hslopeA : HasConstantAbsoluteSlopePLCore A a)
    (hslopeB : HasConstantAbsoluteSlopePLCore B b)
    (ha : 1 < a) (hb : 1 < b)
    (hind : MultiplicativelyIndependent a b) :
    (postvertexValuesPLCore A).Finite := by
  classical
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hVAfinite : (vertexValues A).Finite :=
    vertexValues_finite_of_constantSlopePLCore ha0 hslopeA
  have hVBfinite : (vertexValues B).Finite :=
    vertexValues_finite_of_constantSlopePLCore hb0 hslopeB
  have hBfibers : ∀ y : I, (B ⁻¹' {y}).Finite :=
    constantAbsoluteSlopePLCore_finite_fibers hb0 hslopeB
  by_contra hpostfinite
  have hseed : ∃ w : I, w ∈ vertexValues A ∧
      (forwardOrbitPLCore A w).Infinite := by
    by_contra hseed
    apply hpostfinite
    rw [postvertex_eq_biUnion_forwardOrbit_plCore]
    apply hVAfinite.biUnion
    intro w hw
    by_contra hwfinite
    exact hseed ⟨w, hw, hwfinite⟩
  obtain ⟨w, hwvertex, hworbit⟩ := hseed
  have hstates : ∀ n : ℕ, ∃ s q : ℕ, ∃ v : I,
      v ∈ vertexValues A ∧ (forwardOrbitPLCore A v).Infinite ∧
        iterateMap A s (iterateMap B n w) = iterateMap A q v := by
    intro n
    induction n with
    | zero =>
        exact ⟨0, 0, w, hwvertex, hworbit, by simp [iterateMap]⟩
    | succ n ih =>
        obtain ⟨s, q, v, hvvertex, hvorbit, hsq⟩ := ih
        have hvpost : v ∈ postvertexValuesPLCore A := by
          apply Set.mem_iUnion.mpr
          exact ⟨0, ⟨v, hvvertex, by simp [iterateMap]⟩⟩
        obtain ⟨k, hkpost⟩ :=
          eventually_image_mem_postvertex_of_infinite_orbit_plCore
            hcomm hAonto hBonto hAG hBG hVBfinite hBfibers
            hvpost hvorbit
        obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hkpost
        obtain ⟨v', hv'vertex, hv'l⟩ := hl
        have hBvorbit : (forwardOrbitPLCore A (B v)).Infinite :=
          forwardOrbitPLCore_infinite_image_of_commute
            hcomm hBfibers hvorbit
        have hkBvorbit :
            (forwardOrbitPLCore A (iterateMap A k (B v))).Infinite :=
          forwardOrbitPLCore_iterate_infinite hBvorbit k
        have hlv'orbit :
            (forwardOrbitPLCore A (iterateMap A l v')).Infinite := by
          rw [hv'l]
          exact hkBvorbit
        have hv'orbit : (forwardOrbitPLCore A v').Infinite := by
          intro hv'finite
          exact hlv'orbit
            (hv'finite.subset (forwardOrbitPLCore_iterate_subset v' l))
        refine ⟨k + s, q + l, v', hv'vertex, hv'orbit, ?_⟩
        change (A^[k + s]) ((B^[n + 1]) w) = (A^[q + l]) v'
        calc
          (A^[k + s]) ((B^[n + 1]) w) =
              (A^[k]) ((A^[s]) ((B^[n + 1]) w)) :=
            Function.iterate_add_apply A k s ((B^[n + 1]) w)
          _ = (A^[k]) ((A^[s]) (B ((B^[n]) w))) := by
            rw [Function.iterate_succ_apply']
          _ = (A^[k]) (B ((A^[s]) ((B^[n]) w))) := by
            rw [hcomm.iterate_left s]
          _ = (A^[k]) (B ((A^[q]) v)) :=
            congrArg (fun z ↦ (A^[k]) (B z)) hsq
          _ = (A^[k]) ((A^[q]) (B v)) := by
            rw [hcomm.iterate_left q]
          _ = (A^[k + q]) (B v) :=
            (Function.iterate_add_apply A k q (B v)).symm
          _ = (A^[q + k]) (B v) := by rw [Nat.add_comm k q]
          _ = (A^[q]) ((A^[k]) (B v)) :=
            Function.iterate_add_apply A q k (B v)
          _ = (A^[q]) ((A^[l]) v') := congrArg (A^[q]) hv'l.symm
          _ = (A^[q + l]) v' :=
            (Function.iterate_add_apply A q l v').symm
  choose s q v hstate using hstates
  let stateVertex : ℕ → {x // x ∈ vertexValues A} := fun n ↦
    ⟨v n, (hstate n).1⟩
  letI : Finite {x // x ∈ vertexValues A} := hVAfinite.to_subtype
  obtain ⟨i, j, hijne, hvij⟩ :=
    Finite.exists_ne_map_eq_of_infinite stateVertex
  have hordered {i j : ℕ} (hij : i < j)
      (hvij : stateVertex i = stateVertex j) : False := by
    have hv : v i = v j := congrArg Subtype.val hvij
    let d : ℕ := j - i
    have hd : 0 < d := Nat.sub_pos_of_lt hij
    have hi := (hstate i).2.2
    have hj := (hstate j).2.2
    have hcycle :
        iterateMap A (s j + q i) (iterateMap B d (v i)) =
          iterateMap A (s i + q j) (v i) := by
      change (A^[s j + q i]) ((B^[d]) (v i)) =
        (A^[s i + q j]) (v i)
      calc
        (A^[s j + q i]) ((B^[d]) (v i)) =
            (A^[s j]) ((A^[q i]) ((B^[d]) (v i))) :=
          Function.iterate_add_apply A (s j) (q i) ((B^[d]) (v i))
        _ = (A^[s j]) ((B^[d]) ((A^[q i]) (v i))) := by
          rw [hcomm.iterate_iterate (q i) d]
        _ = (A^[s j]) ((B^[d]) ((A^[s i]) ((B^[i]) w))) :=
          congrArg (fun z ↦ (A^[s j]) ((B^[d]) z)) hi.symm
        _ = (A^[s j]) ((A^[s i]) ((B^[d]) ((B^[i]) w))) := by
          rw [hcomm.iterate_iterate (s i) d]
        _ = (A^[s j + s i]) ((B^[d]) ((B^[i]) w)) :=
          (Function.iterate_add_apply A (s j) (s i)
            ((B^[d]) ((B^[i]) w))).symm
        _ = (A^[s j + s i]) ((B^[d + i]) w) :=
          congrArg (A^[s j + s i])
            (Function.iterate_add_apply B d i w).symm
        _ = (A^[s j + s i]) ((B^[j]) w) := by
          have hdadd : d + i = j := by
            dsimp [d]
            omega
          rw [hdadd]
        _ = (A^[s i + s j]) ((B^[j]) w) := by
          rw [Nat.add_comm (s j) (s i)]
        _ = (A^[s i]) ((A^[s j]) ((B^[j]) w)) :=
          Function.iterate_add_apply A (s i) (s j) ((B^[j]) w)
        _ = (A^[s i]) ((A^[q j]) (v j)) :=
          congrArg (A^[s i]) hj
        _ = (A^[s i + q j]) (v j) :=
          (Function.iterate_add_apply A (s i) (q j) (v j)).symm
        _ = (A^[s i + q j]) (v i) := by rw [hv]
    let α : ℕ := s j + q i
    let γ : ℕ := s i + q j
    let F : IntervalMap := iterateMap A α ∘ iterateMap B d
    let H : IntervalMap := iterateMap A γ
    have hFA : Commute F A := by
      dsimp [F]
      exact (Function.Commute.iterate_self A α).comp_left
        (hcomm.symm.iterate_left d)
    have hHA : Commute H A := by
      dsimp [H]
      exact Function.Commute.iterate_self A γ
    have hpoint : F (v i) = H (v i) := by
      simpa [F, H, α, γ, Function.comp_apply] using hcycle
    have heqOrbit : Set.EqOn F H (forwardOrbitPLCore A (v i)) := by
      rintro z ⟨k, rfl⟩
      change F ((A^[k]) (v i)) = H ((A^[k]) (v i))
      rw [(hFA.iterate_right k).eq, (hHA.iterate_right k).eq, hpoint]
    have hAαslope :
        HasConstantAbsoluteSlopePLCore (iterateMap A α) (a ^ α) :=
      constantAbsoluteSlopePLCore_iterate ha0 hslopeA α
    have hBdslope :
        HasConstantAbsoluteSlopePLCore (iterateMap B d) (b ^ d) :=
      constantAbsoluteSlopePLCore_iterate hb0 hslopeB d
    have hFslope :
        HasConstantAbsoluteSlopePLCore F (a ^ α * b ^ d) := by
      dsimp [F]
      exact constantAbsoluteSlopePLCore_comp
        (pow_pos hb0 d) hAαslope hBdslope
    have hHslope : HasConstantAbsoluteSlopePLCore H (a ^ γ) := by
      simpa [H] using constantAbsoluteSlopePLCore_iterate ha0 hslopeA γ
    obtain ⟨J, hJ, heqJ⟩ :=
      constantSlopePLCore_maps_eqOn_interval_of_infinite
        hFslope hHslope (hstate i).2.1 heqOrbit
    have hAR : Commute A R := by
      rw [hR]
      exact (Function.Commute.refl A).comp_right hcomm
    have hBR : Commute B R := by
      rw [hR]
      exact hcomm.symm.comp_right (Function.Commute.refl B)
    have hFR : Commute F R := by
      dsimp [F]
      exact (hAR.iterate_left α).comp_left (hBR.iterate_left d)
    have hHR : Commute H R := by
      dsimp [H]
      exact hAR.iterate_left γ
    have hFH : F = H :=
      local_equality_global_of_exact_centralizer_plCore
        hFR hHR hexact hJ heqJ
    have hHslopeF : HasConstantAbsoluteSlopePLCore F (a ^ γ) := by
      rw [hFH]
      exact hHslope
    have hscale : a ^ α * b ^ d = a ^ γ :=
      constantAbsoluteSlopePLCore_scale_unique hFslope hHslopeF
    have hαγ : α < γ := by
      by_contra hnot
      have hγα : γ ≤ α := Nat.le_of_not_gt hnot
      have hpows : a ^ γ ≤ a ^ α := pow_le_pow_right₀ ha.le hγα
      have hbd : 1 < b ^ d := one_lt_pow₀ hb hd.ne'
      have haαpos : 0 < a ^ α := pow_pos ha0 α
      have hlt : a ^ α < a ^ α * b ^ d := by
        simpa using mul_lt_mul_of_pos_left hbd haαpos
      rw [hscale] at hlt
      exact (not_lt_of_ge hpows) hlt
    have hdep : a ^ (γ - α) = b ^ d := by
      have hsplit : α + (γ - α) = γ := Nat.add_sub_of_le hαγ.le
      have hcancel : a ^ α * b ^ d = a ^ α * a ^ (γ - α) := by
        calc
          a ^ α * b ^ d = a ^ γ := hscale
          _ = a ^ (α + (γ - α)) := by rw [hsplit]
          _ = a ^ α * a ^ (γ - α) := pow_add a α (γ - α)
      exact (mul_left_cancel₀ (ne_of_gt (pow_pos ha0 α)) hcancel).symm
    exact hind (γ - α) d (Nat.sub_pos_of_lt hαγ) hd hdep
  rcases lt_or_gt_of_ne hijne with hij | hji
  · exact hordered hij hvij
  · exact hordered hji hvij.symm

private theorem finite_postvertex_sets_plCore
    {A B R : IntervalMap} {a b : ℝ}
    (hcomm : Commute A B) (hR : R = A ∘ B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAG : HasPLCoreGerms A) (hBG : HasPLCoreGerms B)
    (hexact : IsTopologicallyExact R)
    (hslopeA : HasConstantAbsoluteSlopePLCore A a)
    (hslopeB : HasConstantAbsoluteSlopePLCore B b)
    (ha : 1 < a) (hb : 1 < b)
    (hind : MultiplicativelyIndependent a b) :
    (postvertexValuesPLCore A).Finite ∧
      (postvertexValuesPLCore B).Finite := by
  have hleft := postvertexPLCore_finite_left hcomm hR hAonto hBonto
    hAG hBG hexact hslopeA hslopeB ha hb hind
  have hRswap : R = B ∘ A := by
    rw [hR]
    funext x
    exact hcomm x
  have hindswap : MultiplicativelyIndependent b a := by
    intro m n hm hn hpow
    exact hind n m hn hm hpow.symm
  have hright := postvertexPLCore_finite_left hcomm.symm hRswap
    hBonto hAonto hBG hAG hexact hslopeB hslopeA hb ha hindswap
  exact ⟨hleft, hright⟩

private theorem piecewiseLinear_finitePostvertexSets_core
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) :
    HasFinitePostvertexSet M.A ∧ HasFinitePostvertexSet M.B := by
  have hLpos : 0 < G.L := by
    simpa [PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.L] using
      piecewiseLinearNormalizationExponent_pos G.system.base.fixedW
  have hscaleP0 : 0 < M.scaleP := lt_trans (by norm_num) M.one_lt_scaleP
  have hscaleQ0 : 0 < M.scaleQ := lt_trans (by norm_num) M.one_lt_scaleQ
  have hAslope :
      HasConstantAbsoluteSlopePLCore M.A (M.scaleP ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.A] using
      constantAbsoluteSlopePLCore_iterate hscaleP0 M.slopeP G.L
  have hBslope :
      HasConstantAbsoluteSlopePLCore M.B (M.scaleQ ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.B] using
      constantAbsoluteSlopePLCore_iterate hscaleQ0 M.slopeQ G.L
  have hAonto : IsOnto M.A := onto_of_topologicallyExact_plCore M.exact_A
  have hBonto : IsOnto M.B := onto_of_topologicallyExact_plCore M.exact_B
  have hAPL : FinitePiecePL M.A :=
    constantAbsoluteSlopePLCore_finitePiecePL hAslope
  have hBPL : FinitePiecePL M.B :=
    constantAbsoluteSlopePLCore_finitePiecePL hBslope
  have hAflat : ¬HasFlatInterval M.A :=
    piecewiseLinear_exact_noFlat hAPL M.exact_A
  have hBflat : ¬HasFlatInterval M.B :=
    piecewiseLinear_exact_noFlat hBPL M.exact_B
  have hAG : HasPLCoreGerms M.A :=
    hasPLCoreGerms_of_finitePiecePL hAflat hAPL
  have hBG : HasPLCoreGerms M.B :=
    hasPLCoreGerms_of_finitePiecePL hBflat hBPL
  have hcomm : Commute M.A M.B := by
    intro x
    simpa [PiecewiseLinearConstantSlopeSystem.A,
      PiecewiseLinearConstantSlopeSystem.B] using
      M.commute.iterate_iterate G.L G.L x
  have hscaleA : 1 < M.scaleP ^ G.L :=
    one_lt_pow₀ M.one_lt_scaleP hLpos.ne'
  have hscaleB : 1 < M.scaleQ ^ G.L :=
    one_lt_pow₀ M.one_lt_scaleQ hLpos.ne'
  have hpost := finite_postvertex_sets_plCore hcomm
    (show M.R = M.A ∘ M.B from rfl) hAonto hBonto hAG hBG M.exact_R
    hAslope hBslope hscaleA hscaleB M.returned_scales_independent
  simpa [HasFinitePostvertexSet, postvertexValuesPLCore] using hpost

/-- Commutation, constant slopes, and multiplicative independence make the
postvertex set of the returned `A` finite. -/
theorem piecewiseLinear_A_hasFinitePostvertexSet
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) :
    HasFinitePostvertexSet M.A := by
  exact (piecewiseLinear_finitePostvertexSets_core M).1

/-- The symmetric postvertex argument makes the returned `B` postvertex set
finite. -/
theorem piecewiseLinear_B_hasFinitePostvertexSet
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) :
    HasFinitePostvertexSet M.B := by
  exact (piecewiseLinear_finitePostvertexSets_core M).2

private theorem fixedPoints_iterate_finite_of_exact_centralizer_plCore
    {A R : IntervalMap} {a : ℝ} (hAR : Commute A R)
    (hexact : IsTopologicallyExact R)
    (hslopeA : HasConstantAbsoluteSlopePLCore A a) (ha : 1 < a)
    {d : ℕ} (hd : 0 < d) :
    {x : I | iterateMap A d x = x}.Finite := by
  let F : IntervalMap := iterateMap A d
  let Id : IntervalMap := id
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hFslope : HasConstantAbsoluteSlopePLCore F (a ^ d) := by
    simpa [F] using constantAbsoluteSlopePLCore_iterate ha0 hslopeA d
  have hIdslope : HasConstantAbsoluteSlopePLCore Id 1 := by
    simpa [Id] using constantAbsoluteSlopePLCore_id
  by_contra hfinite
  have hinfinite : {x : I | iterateMap A d x = x}.Infinite := hfinite
  have heq : Set.EqOn F Id {x : I | iterateMap A d x = x} := by
    intro x hx
    simpa [F, Id] using hx
  obtain ⟨J, hJ, heqJ⟩ :=
    constantSlopePLCore_maps_eqOn_interval_of_infinite
      hFslope hIdslope hinfinite heq
  have hFR : Commute F R := by
    simpa [F] using hAR.iterate_left d
  have hIdR : Commute Id R := by
    intro x
    rfl
  have hglobal : F = Id :=
    local_equality_global_of_exact_centralizer_plCore
      hFR hIdR hexact hJ heqJ
  have hIdslopeF : HasConstantAbsoluteSlopePLCore F 1 := by
    rw [hglobal]
    exact hIdslope
  have hscale : a ^ d = 1 :=
    constantAbsoluteSlopePLCore_scale_unique hFslope hIdslopeF
  exact (one_lt_pow₀ ha hd.ne').ne' hscale

private theorem commuting_maps_send_cross_vertices_plCore
    {A B : IntervalMap} (hcomm : Commute A B)
    (hAG : HasPLCoreGerms A) (hBG : HasPLCoreGerms B) :
    (∀ x ∈ vertexDomain A,
        B x ∈ vertexDomain A ∪ vertexValues B) ∧
      (∀ x ∈ vertexDomain B,
        A x ∈ vertexDomain B ∪ vertexValues A) := by
  have hmaps : A ∘ B = B ∘ A := funext hcomm
  have hdomains :
      vertexDomain B ∪ B ⁻¹' vertexDomain A =
        vertexDomain A ∪ A ⁻¹' vertexDomain B := by
    rw [← vertexDomain_comp_of_germs_plCore hAG hBG,
      ← vertexDomain_comp_of_germs_plCore hBG hAG, hmaps]
  constructor
  · intro x hx
    have hxright : x ∈ vertexDomain A ∪ A ⁻¹' vertexDomain B :=
      Or.inl hx
    rw [← hdomains] at hxright
    rcases hxright with hxB | hBxA
    · exact Or.inr ⟨x, hxB, rfl⟩
    · exact Or.inl hBxA
  · intro x hx
    have hxleft : x ∈ vertexDomain B ∪ B ⁻¹' vertexDomain A :=
      Or.inl hx
    rw [hdomains] at hxleft
    rcases hxleft with hxA | hAxB
    · exact Or.inr ⟨x, hxA, rfl⟩
    · exact Or.inl hAxB

private theorem exists_finite_common_invariant_postvertex_hull_plCore
    {A B R : IntervalMap} {a b : ℝ}
    (hcomm : Commute A B) (hR : R = A ∘ B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAG : HasPLCoreGerms A) (hBG : HasPLCoreGerms B)
    (hexact : IsTopologicallyExact R)
    (hslopeA : HasConstantAbsoluteSlopePLCore A a)
    (hslopeB : HasConstantAbsoluteSlopePLCore B b)
    (ha : 1 < a) (hb : 1 < b)
    (hpostA : (postvertexValuesPLCore A).Finite)
    (hpostB : (postvertexValuesPLCore B).Finite) :
    ∃ S : Set I, S.Finite ∧ postvertexValuesPLCore A ⊆ S ∧
      postvertexValuesPLCore B ⊆ S ∧ MapsTo A S S ∧ MapsTo B S S := by
  classical
  let base : Set I := postvertexValuesPLCore A ∪ postvertexValuesPLCore B
  let ZA : Set I := B '' postvertexValuesPLCore A \ base
  let ZB : Set I := A '' postvertexValuesPLCore B \ base
  have hbasefinite : base.Finite := hpostA.union hpostB
  have hZAfinite : ZA.Finite := by
    dsimp [ZA]
    exact (hpostA.image B).diff
  have hZBfinite : ZB.Finite := by
    dsimp [ZB]
    exact (hpostB.image A).diff
  have hAR : Commute A R := by
    rw [hR]
    exact (Function.Commute.refl A).comp_right hcomm
  have hBR : Commute B R := by
    rw [hR]
    exact hcomm.symm.comp_right (Function.Commute.refl B)
  have hVBfinite : (vertexValues B).Finite :=
    vertexValues_finite_of_constantSlopePLCore
      (lt_trans (by norm_num) hb) hslopeB
  have hVAfinite : (vertexValues A).Finite :=
    vertexValues_finite_of_constantSlopePLCore
      (lt_trans (by norm_num) ha) hslopeA
  have hZAperiodic (y : ZA) :
      ∃ d : ℕ, 0 < d ∧ iterateMap A d y = y := by
    obtain ⟨x, hxpost, hxy⟩ := y.property.1
    have hynotA : (y : I) ∉ postvertexValuesPLCore A := by
      intro hy
      exact y.property.2 (Or.inl hy)
    have hynotB : (y : I) ∉ postvertexValuesPLCore B := by
      intro hy
      exact y.property.2 (Or.inr hy)
    rcases image_postvertex_or_vertex_or_periodic_plCore
        hcomm hAonto hBonto hAG hBG hVBfinite hxpost with
      hback | hvert | hperiodic
    · exact False.elim (hynotA (hxy ▸ hback))
    · exact False.elim (hynotB
        (hxy ▸ vertexValues_subset_postvertexPLCore B hvert))
    · simpa [hxy] using hperiodic
  have hZBperiodic (y : ZB) :
      ∃ d : ℕ, 0 < d ∧ iterateMap B d y = y := by
    obtain ⟨x, hxpost, hxy⟩ := y.property.1
    have hynotA : (y : I) ∉ postvertexValuesPLCore A := by
      intro hy
      exact y.property.2 (Or.inl hy)
    have hynotB : (y : I) ∉ postvertexValuesPLCore B := by
      intro hy
      exact y.property.2 (Or.inr hy)
    rcases image_postvertex_or_vertex_or_periodic_plCore
        hcomm.symm hBonto hAonto hBG hAG hVAfinite hxpost with
      hback | hvert | hperiodic
    · exact False.elim (hynotB (hxy ▸ hback))
    · exact False.elim (hynotA
        (hxy ▸ vertexValues_subset_postvertexPLCore A hvert))
    · simpa [hxy] using hperiodic
  choose dA hdApos hdAfix using hZAperiodic
  choose dB hdBpos hdBfix using hZBperiodic
  let PA : Set I := ⋃ y : ZA, {z : I | iterateMap A (dA y) z = z}
  let PB : Set I := ⋃ y : ZB, {z : I | iterateMap B (dB y) z = z}
  have hPAfinite : PA.Finite := by
    letI : Finite ZA := hZAfinite.to_subtype
    change (⋃ y : ZA, {z : I | iterateMap A (dA y) z = z}).Finite
    rw [show (⋃ y : ZA, {z : I | iterateMap A (dA y) z = z}) =
        ⋃ y ∈ (Set.univ : Set ZA),
          {z : I | iterateMap A (dA y) z = z} by simp]
    exact Set.finite_univ.biUnion fun y _ ↦
      fixedPoints_iterate_finite_of_exact_centralizer_plCore
        hAR hexact hslopeA ha (hdApos y)
  have hPBfinite : PB.Finite := by
    letI : Finite ZB := hZBfinite.to_subtype
    change (⋃ y : ZB, {z : I | iterateMap B (dB y) z = z}).Finite
    rw [show (⋃ y : ZB, {z : I | iterateMap B (dB y) z = z}) =
        ⋃ y ∈ (Set.univ : Set ZB),
          {z : I | iterateMap B (dB y) z = z} by simp]
    exact Set.finite_univ.biUnion fun y _ ↦
      fixedPoints_iterate_finite_of_exact_centralizer_plCore
        hBR hexact hslopeB hb (hdBpos y)
  have hZA_PA : ZA ⊆ PA := by
    intro y hy
    apply Set.mem_iUnion.mpr
    exact ⟨⟨y, hy⟩, hdAfix ⟨y, hy⟩⟩
  have hZB_PB : ZB ⊆ PB := by
    intro y hy
    apply Set.mem_iUnion.mpr
    exact ⟨⟨y, hy⟩, hdBfix ⟨y, hy⟩⟩
  have hA_PA : MapsTo A PA PA := by
    intro z hz
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨y, ?_⟩
    change (A^[dA y]) z = z at hy
    change (A^[dA y]) (A z) = A z
    rw [(Function.Commute.iterate_self A (dA y)).eq, hy]
  have hB_PA : MapsTo B PA PA := by
    intro z hz
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨y, ?_⟩
    change (A^[dA y]) z = z at hy
    change (A^[dA y]) (B z) = B z
    rw [(hcomm.iterate_left (dA y)).eq, hy]
  have hB_PB : MapsTo B PB PB := by
    intro z hz
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨y, ?_⟩
    change (B^[dB y]) z = z at hy
    change (B^[dB y]) (B z) = B z
    rw [(Function.Commute.iterate_self B (dB y)).eq, hy]
  have hA_PB : MapsTo A PB PB := by
    intro z hz
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hz
    apply Set.mem_iUnion.mpr
    refine ⟨y, ?_⟩
    change (B^[dB y]) z = z at hy
    change (B^[dB y]) (A z) = A z
    rw [(hcomm.symm.iterate_left (dB y)).eq, hy]
  let S : Set I := base ∪ PA ∪ PB
  refine ⟨S, (hbasefinite.union hPAfinite).union hPBfinite,
    ?_, ?_, ?_, ?_⟩
  · exact fun x hx ↦ Or.inl (Or.inl (Or.inl hx))
  · exact fun x hx ↦ Or.inl (Or.inl (Or.inr hx))
  · intro x hx
    rcases hx with (hxbase | hxPA) | hxPB
    · rcases hxbase with hxA | hxB
      · have hAxpost : A x ∈ postvertexValuesPLCore A := by
          simpa [iterateMap] using postvertexPLCore_iterate_mem hxA 1
        exact Or.inl (Or.inl (Or.inl hAxpost))
      · by_cases hAx : A x ∈ base
        · exact Or.inl (Or.inl hAx)
        · exact Or.inr (hZB_PB ⟨⟨x, hxB, rfl⟩, hAx⟩)
    · exact Or.inl (Or.inr (hA_PA hxPA))
    · exact Or.inr (hA_PB hxPB)
  · intro x hx
    rcases hx with (hxbase | hxPA) | hxPB
    · rcases hxbase with hxA | hxB
      · by_cases hBx : B x ∈ base
        · exact Or.inl (Or.inl hBx)
        · exact Or.inl (Or.inr (hZA_PA ⟨⟨x, hxA, rfl⟩, hBx⟩))
      · have hBxpost : B x ∈ postvertexValuesPLCore B := by
          simpa [iterateMap] using postvertexPLCore_iterate_mem hxB 1
        exact Or.inl (Or.inl (Or.inr hBxpost))
    · exact Or.inl (Or.inr (hB_PA hxPA))
    · exact Or.inr (hB_PB hxPB)

/-- The finite forward-invariant hull of both postvertex sets and the
transformed selected base. -/
structure PiecewiseLinearMarkovVertexHull
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) where
  K : Finset I
  base_mem : M.coordinate G.p ∈ K
  left_mem : leftEndpoint ∈ K
  right_mem : rightEndpoint ∈ K
  forward_A : ∀ x ∈ K, M.A x ∈ K
  forward_B : ∀ x ∈ K, M.B x ∈ K
  contains_vertices_A : vertexDomain M.A ⊆ (K : Set I)
  contains_vertices_B : vertexDomain M.B ⊆ (K : Set I)

/-- Unite the two finite postvertex sets with the endpoints and selected
base to obtain a common forward-invariant vertex hull. -/
theorem piecewiseLinear_exists_markovVertexHull
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E)
    (_hA : HasFinitePostvertexSet M.A)
    (_hB : HasFinitePostvertexSet M.B) :
    Nonempty (PiecewiseLinearMarkovVertexHull M) := by
  classical
  have hLpos : 0 < G.L := by
    simpa [PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.L] using
      piecewiseLinearNormalizationExponent_pos G.system.base.fixedW
  have hscaleP0 : 0 < M.scaleP := lt_trans (by norm_num) M.one_lt_scaleP
  have hscaleQ0 : 0 < M.scaleQ := lt_trans (by norm_num) M.one_lt_scaleQ
  have hAslope :
      HasConstantAbsoluteSlopePLCore M.A (M.scaleP ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.A] using
      constantAbsoluteSlopePLCore_iterate hscaleP0 M.slopeP G.L
  have hBslope :
      HasConstantAbsoluteSlopePLCore M.B (M.scaleQ ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.B] using
      constantAbsoluteSlopePLCore_iterate hscaleQ0 M.slopeQ G.L
  have hAonto : IsOnto M.A := onto_of_topologicallyExact_plCore M.exact_A
  have hBonto : IsOnto M.B := onto_of_topologicallyExact_plCore M.exact_B
  have hAPL : FinitePiecePL M.A :=
    constantAbsoluteSlopePLCore_finitePiecePL hAslope
  have hBPL : FinitePiecePL M.B :=
    constantAbsoluteSlopePLCore_finitePiecePL hBslope
  have hAflat : ¬HasFlatInterval M.A :=
    piecewiseLinear_exact_noFlat hAPL M.exact_A
  have hBflat : ¬HasFlatInterval M.B :=
    piecewiseLinear_exact_noFlat hBPL M.exact_B
  have hAG : HasPLCoreGerms M.A :=
    hasPLCoreGerms_of_finitePiecePL hAflat hAPL
  have hBG : HasPLCoreGerms M.B :=
    hasPLCoreGerms_of_finitePiecePL hBflat hBPL
  have hcomm : Commute M.A M.B := by
    intro x
    simpa [PiecewiseLinearConstantSlopeSystem.A,
      PiecewiseLinearConstantSlopeSystem.B] using
      M.commute.iterate_iterate G.L G.L x
  have hscaleA : 1 < M.scaleP ^ G.L :=
    one_lt_pow₀ M.one_lt_scaleP hLpos.ne'
  have hscaleB : 1 < M.scaleQ ^ G.L :=
    one_lt_pow₀ M.one_lt_scaleQ hLpos.ne'
  have hpostA : (postvertexValuesPLCore M.A).Finite := by
    simpa [HasFinitePostvertexSet, postvertexValuesPLCore] using _hA
  have hpostB : (postvertexValuesPLCore M.B).Finite := by
    simpa [HasFinitePostvertexSet, postvertexValuesPLCore] using _hB
  obtain ⟨S, hSfinite, hpostAS, hpostBS, hAS, hBS⟩ :=
    exists_finite_common_invariant_postvertex_hull_plCore hcomm
      (show M.R = M.A ∘ M.B from rfl) hAonto hBonto hAG hBG M.exact_R
      hAslope hBslope hscaleA hscaleB hpostA hpostB
  have hEAfinite : (vertexDomain M.A).Finite :=
    vertexDomain_finite_of_constantSlopePLCore
      (pow_pos hscaleP0 G.L) hAslope
  have hEBfinite : (vertexDomain M.B).Finite :=
    vertexDomain_finite_of_constantSlopePLCore
      (pow_pos hscaleQ0 G.L) hBslope
  obtain ⟨hB_EA, hA_EB⟩ :=
    commuting_maps_send_cross_vertices_plCore hcomm hAG hBG
  have hconjA : ConjugatesPLCore M.coordinate G.A M.A := by
    simpa [PiecewiseLinearSelectedFixedGap.A,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.A,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.A,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearA, PiecewiseLinearConstantSlopeSystem.A] using
      conjugatesPLCore_iterate M.conjugatesP G.L
  have hconjB : ConjugatesPLCore M.coordinate G.B M.B := by
    simpa [PiecewiseLinearSelectedFixedGap.B,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.B,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.B,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearB, PiecewiseLinearConstantSlopeSystem.B] using
      conjugatesPLCore_iterate M.conjugatesQ G.L
  have hAp : M.A (M.coordinate G.p) = M.coordinate G.p := by
    calc
      M.A (M.coordinate G.p) = M.coordinate (G.A G.p) :=
        (hconjA G.p).symm
      _ = M.coordinate G.p :=
        congrArg M.coordinate (piecewiseLinear_return_fixes_A_p G)
  have hBp : M.B (M.coordinate G.p) = M.coordinate G.p := by
    calc
      M.B (M.coordinate G.p) = M.coordinate (G.B G.p) :=
        (hconjB G.p).symm
      _ = M.coordinate G.p :=
        congrArg M.coordinate (piecewiseLinear_return_fixes_B_p G)
  let pbar : I := M.coordinate G.p
  let Kset : Set I :=
    ((S ∪ vertexDomain M.A) ∪ vertexDomain M.B) ∪ {pbar}
  have hKfinite : Kset.Finite :=
    ((hSfinite.union hEAfinite).union hEBfinite).union
      (Set.toFinite {pbar})
  have hA_Kset : MapsTo M.A Kset Kset := by
    intro z hz
    rcases hz with ((hzS | hzEA) | hzEB) | hzp
    · exact Or.inl (Or.inl (Or.inl (hAS hzS)))
    · have hAzpost : M.A z ∈ postvertexValuesPLCore M.A :=
        vertexValues_subset_postvertexPLCore M.A ⟨z, hzEA, rfl⟩
      exact Or.inl (Or.inl (Or.inl (hpostAS hAzpost)))
    · rcases hA_EB z hzEB with hAzEB | hAzVA
      · exact Or.inl (Or.inr hAzEB)
      · exact Or.inl (Or.inl (Or.inl
          (hpostAS (vertexValues_subset_postvertexPLCore M.A hAzVA))))
    · have hzp' : z = pbar := by simpa using hzp
      subst z
      exact Or.inr (by simpa [pbar, hAp])
  have hB_Kset : MapsTo M.B Kset Kset := by
    intro z hz
    rcases hz with ((hzS | hzEA) | hzEB) | hzp
    · exact Or.inl (Or.inl (Or.inl (hBS hzS)))
    · rcases hB_EA z hzEA with hBzEA | hBzVB
      · exact Or.inl (Or.inl (Or.inr hBzEA))
      · exact Or.inl (Or.inl (Or.inl
          (hpostBS (vertexValues_subset_postvertexPLCore M.B hBzVB))))
    · have hBzpost : M.B z ∈ postvertexValuesPLCore M.B :=
        vertexValues_subset_postvertexPLCore M.B ⟨z, hzEB, rfl⟩
      exact Or.inl (Or.inl (Or.inl (hpostBS hBzpost)))
    · have hzp' : z = pbar := by simpa using hzp
      subst z
      exact Or.inr (by simpa [pbar, hBp])
  let K : Finset I := hKfinite.toFinset
  have hmemK (z : I) : z ∈ K ↔ z ∈ Kset := by
    simp [K]
  refine ⟨{
    K := K
    base_mem := (hmemK pbar).2 (Or.inr (by simp))
    left_mem := ?_
    right_mem := ?_
    forward_A := ?_
    forward_B := ?_
    contains_vertices_A := ?_
    contains_vertices_B := ?_ }⟩
  · apply (hmemK leftEndpoint).2
    exact Or.inl (Or.inl (Or.inr (by simp [vertexDomain])))
  · apply (hmemK rightEndpoint).2
    exact Or.inl (Or.inl (Or.inr (by simp [vertexDomain])))
  · intro z hz
    exact (hmemK (M.A z)).2 (hA_Kset ((hmemK z).1 hz))
  · intro z hz
    exact (hmemK (M.B z)).2 (hB_Kset ((hmemK z).1 hz))
  · intro z hz
    exact (hmemK z).2 (Or.inl (Or.inl (Or.inr hz)))
  · intro z hz
    exact (hmemK z).2 (Or.inl (Or.inr hz))

/-- Constant absolute slope and absence of an intrinsic turn on an interval
force one affine, strictly monotone branch across the whole interval. -/
private theorem constantSlopePLCore_affine_strict_on_Icc_of_no_vertex
    {T : IntervalMap} {r : ℝ} (hr : 0 < r)
    (hT : HasConstantAbsoluteSlopePLCore T r) {x y : I} (hxy : x < y)
    (hnone : ∀ z ∈ vertexDomain T, ¬(x < z ∧ z < y)) :
    IsAffineOn T (Set.Icc x y) ∧
      IsStrictlyMonotoneOn T (Set.Icc x y) := by
  classical
  rcases hT with ⟨_hcont, p, hp⟩
  let q : RealPartition :=
    { points := p.points ∪ {(x : ℝ), (y : ℝ)}
      zero_mem := Finset.mem_union_left _ p.zero_mem
      one_mem := Finset.mem_union_left _ p.one_mem
      points_subset := by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact p.points_subset hz
        · have hzxy : z = (x : ℝ) ∨ z = (y : ℝ) := by simpa using hz
          rcases hzxy with rfl | rfl
          · exact x.property
          · exact y.property }
  have hxq : (x : ℝ) ∈ q.points := by
    exact Finset.mem_union_right _ (by simp)
  have hyq : (y : ℝ) ∈ q.points := by
    exact Finset.mem_union_right _ (by simp)
  have hqformula {a b : ℝ} (hab : q.Adjacent a b) :
      ∃ m c : ℝ, |m| = r ∧ ∀ z ∈ intervalCell a b,
        (T z : ℝ) = m * (z : ℝ) + c := by
    have haI : a ∈ I := q.points_subset hab.1
    have hbI : b ∈ I := q.points_subset hab.2.1
    have hnonep : ∀ z ∈ p.points, ¬(a < z ∧ z < b) := by
      intro z hz hbetween
      exact hab.2.2.2 z (Finset.mem_union_left _ hz) hbetween
    obtain ⟨c, d, hcd, hsub⟩ := p.exists_adjacent_superset_plCore
      haI hbI hab.2.2.1 hnonep
    obtain ⟨m, k, hm, hformula⟩ := hp hcd
    exact ⟨m, k, hm, fun z hz ↦ hformula z (hsub hz)⟩
  have hxone : (x : ℝ) < 1 :=
    (show (x : ℝ) < (y : ℝ) from hxy).trans_le y.property.2
  obtain ⟨a₀, b₀, hab₀, ha₀x, hxb₀⟩ :=
    q.exists_adjacent_right_plCore x.property hxone
  have hxa₀ : (x : ℝ) ≤ a₀ := by
    by_contra hnot
    have ha₀ltx : a₀ < (x : ℝ) := lt_of_not_ge hnot
    exact hab₀.2.2.2 (x : ℝ) hxq ⟨ha₀ltx, hxb₀⟩
  have ha₀eq : a₀ = (x : ℝ) := le_antisymm ha₀x hxa₀
  have hb₀y : b₀ ≤ (y : ℝ) := by
    by_contra hnot
    have hyb₀ : (y : ℝ) < b₀ := lt_of_not_ge hnot
    exact hab₀.2.2.2 (y : ℝ) hyq
      ⟨by simpa [ha₀eq] using hxy, hyb₀⟩
  obtain ⟨m, c, hmabs, hformula₀⟩ := hqformula hab₀
  have hmne : m ≠ 0 := by
    intro hm0
    have : |m| = 0 := by rw [hm0, abs_zero]
    linarith
  let good : Finset ℝ := q.points.filter fun z ↦
    (x : ℝ) ≤ z ∧ z ≤ (y : ℝ) ∧
      ∀ u : I, (x : ℝ) ≤ (u : ℝ) → (u : ℝ) ≤ z →
        (T u : ℝ) = m * (u : ℝ) + c
  have hb₀good : b₀ ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨hab₀.2.1, hxb₀.le, hb₀y, ?_⟩
    intro u hxu hub
    apply hformula₀
    exact ⟨by simpa [ha₀eq] using hxu, hub⟩
  obtain ⟨g, hg, hgmax⟩ := good.exists_max_image id ⟨b₀, hb₀good⟩
  have hgdata := Finset.mem_filter.mp hg
  have hgq : g ∈ q.points := hgdata.1
  have hxg : (x : ℝ) ≤ g := hgdata.2.1
  have hgy : g ≤ (y : ℝ) := hgdata.2.2.1
  have hglobalg := hgdata.2.2.2
  have hb₀g : b₀ ≤ g := by simpa using hgmax b₀ hb₀good
  have hxglt : (x : ℝ) < g := hxb₀.trans_le hb₀g
  have hg_eq_y : g = (y : ℝ) := by
    apply le_antisymm hgy
    by_contra hnot
    have hgylt : g < (y : ℝ) := lt_of_not_ge hnot
    have hgI : g ∈ I := q.points_subset hgq
    have hgltone : g < 1 := hgylt.trans_le y.property.2
    obtain ⟨a₁, d, had, ha₁g, hgd⟩ :=
      q.exists_adjacent_right_plCore hgI hgltone
    have hga₁ : g ≤ a₁ := by
      by_contra hga₁not
      have ha₁ltg : a₁ < g := lt_of_not_ge hga₁not
      exact had.2.2.2 g hgq ⟨ha₁ltg, hgd⟩
    have ha₁eq : a₁ = g := le_antisymm ha₁g hga₁
    have hdy : d ≤ (y : ℝ) := by
      by_contra hdynot
      have hyd : (y : ℝ) < d := lt_of_not_ge hdynot
      exact had.2.2.2 (y : ℝ) hyq
        ⟨by simpa [ha₁eq] using hgylt, hyd⟩
    obtain ⟨m₁, c₁, hm₁abs, hformula₁⟩ := hqformula had
    have hm₁ne : m₁ ≠ 0 := by
      intro hm₁0
      have : |m₁| = 0 := by rw [hm₁0, abs_zero]
      linarith
    let gI : I := ⟨g, hgI⟩
    let dI : I := ⟨d, q.points_subset had.2.1⟩
    have hxgI : x < gI := hxglt
    have hgdI : gI < dI := by simpa [gI, dI, ha₁eq] using hgd
    have hgyI : gI < y := hgylt
    have hleftMono (hmpos : 0 < m) : StrictMonoOn T (Set.Icc x gI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg u hu.1 (by simpa [gI] using hu.2),
        hglobalg v hv.1 (by simpa [gI] using hv.2)]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hleftAnti (hmneg : m < 0) : StrictAntiOn T (Set.Icc x gI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg u hu.1 (by simpa [gI] using hu.2),
        hglobalg v hv.1 (by simpa [gI] using hv.2)]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hrightMono (hm₁pos : 0 < m₁) : StrictMonoOn T (Set.Icc gI dI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ u ⟨by simpa [gI, ha₁eq] using hu.1,
            by simpa [dI] using hu.2⟩,
        hformula₁ v ⟨by simpa [gI, ha₁eq] using hv.1,
            by simpa [dI] using hv.2⟩]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hrightAnti (hm₁neg : m₁ < 0) : StrictAntiOn T (Set.Icc gI dI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ u ⟨by simpa [gI, ha₁eq] using hu.1,
            by simpa [dI] using hu.2⟩,
        hformula₁ v ⟨by simpa [gI, ha₁eq] using hv.1,
            by simpa [dI] using hv.2⟩]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hmEq : m₁ = m := by
      rcases lt_or_gt_of_ne hmne with hmneg | hmpos
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · rw [abs_of_neg hmneg] at hmabs
          rw [abs_of_neg hm₁neg] at hm₁abs
          linarith
        · exfalso
          have hturn : IsGenuineTurn T gI :=
            ⟨x, dI, hxgI, hgdI,
              Or.inr ⟨hleftAnti hmneg, hrightMono hm₁pos⟩⟩
          exact hnone gI (Or.inr hturn) ⟨hxgI, hgyI⟩
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · exfalso
          have hturn : IsGenuineTurn T gI :=
            ⟨x, dI, hxgI, hgdI,
              Or.inl ⟨hleftMono hmpos, hrightAnti hm₁neg⟩⟩
          exact hnone gI (Or.inr hturn) ⟨hxgI, hgyI⟩
        · rw [abs_of_pos hmpos] at hmabs
          rw [abs_of_pos hm₁pos] at hm₁abs
          linarith
    have hglobal_at_g : (T gI : ℝ) = m * g + c := by
      exact hglobalg gI hxg (by simp [gI])
    have hright_at_g : (T gI : ℝ) = m₁ * g + c₁ := by
      apply hformula₁
      constructor
      · simpa [gI, ha₁eq]
      · simpa [gI] using hgd.le
    have hcEq : c₁ = c := by
      rw [hmEq] at hright_at_g
      linarith
    have hdgood : d ∈ good := by
      apply Finset.mem_filter.mpr
      refine ⟨had.2.1, hxg.trans hgd.le, hdy, ?_⟩
      intro u hxu hud
      by_cases hug : (u : ℝ) ≤ g
      · exact hglobalg u hxu hug
      · have hgu : g ≤ (u : ℝ) := (lt_of_not_ge hug).le
        rw [hformula₁ u ⟨by simpa [ha₁eq] using hgu, hud⟩, hmEq, hcEq]
    have hdg : d ≤ g := by simpa using hgmax d hdgood
    exact (not_lt_of_ge hdg) hgd
  have hglobal : ∀ u ∈ Set.Icc x y,
      (T u : ℝ) = m * (u : ℝ) + c := by
    intro u hu
    exact hglobalg u hu.1 (by simpa [hg_eq_y] using hu.2)
  constructor
  · exact ⟨m, c, hglobal⟩
  · rcases lt_or_gt_of_ne hmne with hmneg | hmpos
    · right
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobal u hu, hglobal v hv]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    · left
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobal u hu, hglobal v hv]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith

/-- Between consecutive points of a hull containing every genuine turn,
each returned map is affine and strictly monotone. -/
theorem piecewiseLinear_markovHull_cells
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    (H : PiecewiseLinearMarkovVertexHull M) :
    ∀ ⦃x y : I⦄, PiecewiseLinearFinsetAdjacent H.K x y →
      (IsAffineOn M.A (Set.Icc x y) ∧
        IsStrictlyMonotoneOn M.A (Set.Icc x y)) ∧
      (IsAffineOn M.B (Set.Icc x y) ∧
        IsStrictlyMonotoneOn M.B (Set.Icc x y)) := by
  intro x y hxy
  have hnoneA : ∀ z ∈ vertexDomain M.A, ¬(x < z ∧ z < y) := by
    intro z hz hbetween
    exact hxy.2.2.2 z (H.contains_vertices_A hz) hbetween
  have hnoneB : ∀ z ∈ vertexDomain M.B, ¬(x < z ∧ z < y) := by
    intro z hz hbetween
    exact hxy.2.2.2 z (H.contains_vertices_B hz) hbetween
  have hLpos : 0 < G.L := by
    simpa [PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.L] using
      piecewiseLinearNormalizationExponent_pos G.system.base.fixedW
  have hscaleP0 : 0 < M.scaleP := lt_trans (by norm_num) M.one_lt_scaleP
  have hscaleQ0 : 0 < M.scaleQ := lt_trans (by norm_num) M.one_lt_scaleQ
  have hAslope : HasConstantAbsoluteSlopePLCore M.A (M.scaleP ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.A] using
      constantAbsoluteSlopePLCore_iterate hscaleP0 M.slopeP G.L
  have hBslope : HasConstantAbsoluteSlopePLCore M.B (M.scaleQ ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.B] using
      constantAbsoluteSlopePLCore_iterate hscaleQ0 M.slopeQ G.L
  have hApositive : 0 < M.scaleP ^ G.L := pow_pos hscaleP0 G.L
  have hBpositive : 0 < M.scaleQ ^ G.L := pow_pos hscaleQ0 G.L
  exact ⟨
    constantSlopePLCore_affine_strict_on_Icc_of_no_vertex
      hApositive hAslope hxy.2.2.1 hnoneA,
    constantSlopePLCore_affine_strict_on_Icc_of_no_vertex
      hBpositive hBslope hxy.2.2.1 hnoneB⟩

/-- Boundary 8: finite postvertex sets and the common finite Markov hull. -/
theorem piecewiseLinear_exists_commonMarkovPackage
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) :
    Nonempty (PiecewiseLinearCommonMarkovPackage M) := by
  have hA := piecewiseLinear_A_hasFinitePostvertexSet M
  have hB := piecewiseLinear_B_hasFinitePostvertexSet M
  obtain ⟨H⟩ := piecewiseLinear_exists_markovVertexHull M hA hB
  refine ⟨{
    K := H.K
    base_mem := H.base_mem
    markov := ?_ }⟩
  exact
    ⟨H.left_mem, H.right_mem, H.forward_A, H.forward_B,
      piecewiseLinear_markovHull_cells H⟩


end CommutingInterval
