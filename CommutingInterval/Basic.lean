import CommutingInterval.Defs
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Elementary interval-map facts

This file contains the fixed-point and iteration facts used by the later
dynamical arguments.
-/

namespace CommutingInterval

open Function Set

namespace IntervalMap

/-- Every continuous self-map of the closed unit interval has a fixed point. -/
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

/-- A continuous identity map has a common fixed point with every continuous map. -/
theorem hasCommonFixedPoint_of_eq_id {P Q : IntervalMap}
    (hQ : Continuous Q) (hP : P = id) : HasCommonFixedPoint P Q := by
  obtain ⟨x, hx⟩ := exists_fixedPoint hQ
  refine ⟨x, ?_⟩
  exact ⟨by simp [IsFixedPoint, hP], hx⟩

/-- Commutation is inherited by positive or zero iterates of the left map. -/
theorem commute_iterate_left {P Q : IntervalMap} (h : Commute P Q) (n : ℕ) :
    Commute (P^[n]) Q :=
  h.iterate_left n

/-- Commutation is inherited by positive or zero iterates of the right map. -/
theorem commute_iterate_right {P Q : IntervalMap} (h : Commute P Q) (n : ℕ) :
    Commute P (Q^[n]) :=
  h.iterate_right n

/-- Two iterates of commuting maps commute. -/
theorem commute_iterates {P Q : IntervalMap} (h : Commute P Q) (m n : ℕ) :
    Commute (P^[m]) (Q^[n]) :=
  (h.iterate_left m).iterate_right n

/-- A continuous iterate of an interval map is continuous. -/
theorem continuous_iterate {T : IntervalMap} (hT : Continuous T) (n : ℕ) :
    Continuous (T^[n]) :=
  hT.iterate n

/-- An iterate of a surjective map is surjective. -/
theorem surjective_iterate {T : IntervalMap} (hT : Surjective T) (n : ℕ) :
    Surjective (T^[n]) :=
  hT.iterate n

/-- A factor of a surjective composite is surjective in the appropriate order. -/
theorem surjective_left_of_comp {P Q : IntervalMap}
    (h : Surjective (P ∘ Q)) : Surjective P := by
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨Q x, hx⟩

end IntervalMap

end CommutingInterval
