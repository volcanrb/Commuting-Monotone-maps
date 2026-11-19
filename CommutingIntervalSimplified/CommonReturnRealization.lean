import CommutingIntervalSimplified.FiniteReturnRealization
import CommutingIntervalSimplified.GradedProjectionRealization
import CommutingIntervalSimplified.GradedProjectionSquare

/-! # Prescribed common return exponents

Theorem 1.1 of *Common periodic points of commuting interval maps*. The
empty spectrum uses the graded interval construction. Each nonempty spectrum
uses the finite permutation construction.
-/

namespace CommutingIntervalSimplified

open Function Set GradedCells GradedGeometry GradedMarkedCells GradedRealization ConcreteProjection

/-- There are commuting continuous maps of the closed unit interval whose
periodic-point sets are disjoint. -/
theorem exists_commuting_maps_disjoint_periodicPts :
    ∃ f g : IntervalMap, Continuous f ∧ Continuous g ∧ Function.Commute f g ∧
      periodicPts f ∩ periodicPts g = ∅ := by
  let proj := compatibleOfChart projection projection_chart projection_admissible projection_square
  exact exists_commuting_disjoint_periodicPts pieces proj
    (fun hx => section_unique hx ⟨_, rfl⟩)

/-- Every finite set of positive integers, including the empty set,
prescribes a union of positive multiples as the exact common return
spectrum of a commuting pair of continuous interval maps. -/
theorem exists_commuting_maps_prescribed_returns
    (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) :
    ∃ f g : IntervalMap, Continuous f ∧ Continuous g ∧ Function.Commute f g ∧
      commonReturnExponents f g = {n | 0 < n ∧ ∃ d ∈ D, d ∣ n} := by
  rcases D.eq_empty_or_nonempty with h | h
  · subst D
    obtain ⟨f, g, hf, hg, hcomm, hdisj⟩ := exists_commuting_maps_disjoint_periodicPts
    refine ⟨f, g, hf, hg, hcomm, ?_⟩
    simpa using (commonReturnExponents_eq_empty_iff f g).mpr hdisj
  · exact exists_commuting_maps_prescribed_nonempty_returns D hpos h

end CommutingIntervalSimplified
