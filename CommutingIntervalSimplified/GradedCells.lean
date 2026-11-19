import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.DeriveFintype

/-! # Cell labels for the graded interval construction

The two Chinese remainder coordinates have separate types. A projection reduces
each coordinate modulo its smaller prime power. Only the two distinguished
quarters carry cycles. -/

namespace CommutingIntervalSimplified.GradedCells

open Function

abbrev Grade := ℕ × ℕ

def step : Bool → Grade → Grade
  | false, v => (v.1 + 1, v.2)
  | true, v => (v.1, v.2 + 1)

def cycleLength : Bool → Grade → ℕ
  | false, v => 5 ^ v.1
  | true, v => 7 ^ v.2

/-- In geometric order these are quarters 0 through 3. -/
inductive Quarter
  | left | second | third | right
  deriving DecidableEq, Fintype

@[ext] structure Cell (v : Grade) where
  quarter : Quarter
  five : ZMod (5 ^ v.1)
  seven : ZMod (7 ^ v.2)
  deriving Fintype

def color {v : Grade} (J : Cell v) : Bool :=
  match J.quarter with
  | .left | .third => false
  | .second | .right => true

def fiveCell {v : Grade} (k : ZMod (5 ^ v.1)) : Cell v := ⟨.third, k, 0⟩
def sevenCell {v : Grade} (k : ZMod (7 ^ v.2)) : Cell v := ⟨.second, 0, k⟩

def next {v : Grade} (J : Cell v) : Cell v :=
  match J.quarter with
  | .left => fiveCell 0
  | .second => sevenCell (J.seven + 1)
  | .third => fiveCell (J.five + 1)
  | .right => sevenCell 0

@[simp] theorem color_next {v : Grade} (J : Cell v) : color (next J) = color J := by
  rcases J with ⟨q, a, b⟩
  cases q <;> rfl

@[simp] theorem iterate_fiveCell {v : Grade} (n : ℕ) (k : ZMod (5 ^ v.1)) :
    next^[n] (fiveCell (v := v) k) = fiveCell (k + (n : ZMod (5 ^ v.1))) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', ih]; simp [next, fiveCell, Nat.cast_succ, add_assoc]

@[simp] theorem iterate_sevenCell {v : Grade} (n : ℕ) (k : ZMod (7 ^ v.2)) :
    next^[n] (sevenCell (v := v) k) = sevenCell (k + (n : ZMod (7 ^ v.2))) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', ih]; simp [next, sevenCell, Nat.cast_succ, add_assoc]

theorem isPeriodicPt_fiveCell_iff {v : Grade} (n : ℕ) (k : ZMod (5 ^ v.1)) :
    IsPeriodicPt next n (fiveCell (v := v) k) ↔ 5 ^ v.1 ∣ n := by
  change next^[n] _ = _ ↔ _
  rw [iterate_fiveCell]
  constructor
  · intro h
    have hk : k + (n : ZMod (5 ^ v.1)) = k := congrArg Cell.five h
    exact (ZMod.natCast_eq_zero_iff _ _).mp ((add_eq_left).mp hk)
  · intro hd
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, add_zero]

theorem isPeriodicPt_sevenCell_iff {v : Grade} (n : ℕ) (k : ZMod (7 ^ v.2)) :
    IsPeriodicPt next n (sevenCell (v := v) k) ↔ 7 ^ v.2 ∣ n := by
  change next^[n] _ = _ ↔ _
  rw [iterate_sevenCell]
  constructor
  · intro h
    have hk : k + (n : ZMod (7 ^ v.2)) = k := congrArg Cell.seven h
    exact (ZMod.natCast_eq_zero_iff _ _).mp ((add_eq_left).mp hk)
  · intro hd
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, add_zero]

/-- Every positive return of a label is divisible by the active prime power. -/
theorem cycleLength_dvd_of_isPeriodicPt {v : Grade} {J : Cell v} {n : ℕ}
    (_hn : 0 < n) (h : IsPeriodicPt next n J) : cycleLength (color J) v ∣ n := by
  have hs := h.apply
  rcases J with ⟨q, a, b⟩
  cases q with
  | left => exact (isPeriodicPt_fiveCell_iff (v := v) n 0).mp hs
  | second => exact (isPeriodicPt_sevenCell_iff (v := v) n (b + 1)).mp hs
  | third => exact (isPeriodicPt_fiveCell_iff (v := v) n (a + 1)).mp hs
  | right => exact (isPeriodicPt_sevenCell_iff (v := v) n 0).mp hs

/-- Coordinate projection along a pair of grade inequalities. -/
def project {u v : Grade} (_ha : u.1 ≤ v.1) (_hb : u.2 ≤ v.2) (J : Cell v) : Cell u :=
  ⟨J.quarter, J.five.cast, J.seven.cast⟩

@[simp] theorem color_project {u v : Grade} (ha : u.1 ≤ v.1) (hb : u.2 ≤ v.2)
    (J : Cell v) : color (project ha hb J) = color J := rfl

theorem project_next {u v : Grade} (ha : u.1 ≤ v.1) (hb : u.2 ≤ v.2) (J : Cell v) :
    project ha hb (next J) = next (project ha hb J) := by
  rcases J with ⟨q, a, b⟩
  cases q <;> simp [project, next, fiveCell, sevenCell, ZMod.cast_add (pow_dvd_pow 5 ha),
    ZMod.cast_add (pow_dvd_pow 7 hb), ZMod.cast_one (pow_dvd_pow 5 ha),
    ZMod.cast_one (pow_dvd_pow 7 hb)]

/-- Lift an opposite-color successor in the coordinate that is inactive for it. -/
def liftNext {v : Grade} (i : Bool) (J : Cell v) : Cell (step i v) :=
  match i with
  | false => sevenCell (if J.quarter = .second then (J.seven + (1 : ZMod (7 ^ v.2))) else 0)
  | true => fiveCell (if J.quarter = .third then (J.five + (1 : ZMod (5 ^ v.1))) else 0)

theorem project_liftNext {v : Grade} (i : Bool) (J : Cell v) (h : color J ≠ i) :
    project (u := v) (v := step i v) (by cases i <;> simp [step])
      (by cases i <;> simp [step]) (liftNext i J) = next J := by
  rcases J with ⟨q, a, b⟩
  cases i <;> cases q <;> simp [color] at h <;>
    simp [liftNext, next, step, project, fiveCell, sevenCell, ZMod.cast_id] <;>
    first | exact ZMod.cast_zero | constructor <;> first | rfl | exact ZMod.cast_zero

/-- Reduction commutes with lifting successors on a parallel edge of the grade square. -/
theorem project_liftNext_natural {u v : Grade} (ha : u.1 ≤ v.1) (hb : u.2 ≤ v.2)
    (i : Bool) (J : Cell v) :
    project (u := step i u) (v := step i v) (by cases i <;> simp [step, ha])
      (by cases i <;> simp [step, hb]) (liftNext i J) = liftNext i (project ha hb J) := by
  rcases J with ⟨q, a, b⟩
  cases i <;> cases q <;> simp [project, liftNext, step, fiveCell, sevenCell] <;>
    constructor <;> first
    | exact ZMod.cast_zero
    | exact (map_add (ZMod.castHom (pow_dvd_pow 5 ha) (ZMod (5 ^ u.1))) _ 1).trans
        (congrArg (_ + ·) (map_one _))
    | exact (map_add (ZMod.castHom (pow_dvd_pow 7 hb) (ZMod (7 ^ u.2))) _ 1).trans
        (congrArg (_ + ·) (map_one _))

/-- Project one elementary edge of the gradation. -/
def parent (v : Grade) (i : Bool) : Cell (step i v) → Cell v :=
  project (by cases i <;> simp [step]) (by cases i <;> simp [step])

@[simp] theorem color_parent (v : Grade) (i : Bool) (J : Cell (step i v)) :
    color (parent v i J) = color J := rfl

theorem parent_liftNext {v : Grade} (i : Bool) (J : Cell v) (h : color J ≠ i) :
    parent v i (liftNext i J) = next J := project_liftNext i J h

end CommutingIntervalSimplified.GradedCells
