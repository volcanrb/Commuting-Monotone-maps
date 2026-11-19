import CommutingIntervalSimplified.FiniteReturnConstructionGeometry
import CommutingIntervalSimplified.ReturnSpectrum

/-!
# Prescribing a nonempty common return spectrum

This is the nonempty case of Theorem 1.1 in *Common periodic points of
commuting interval maps*. Each chosen positive integer contributes a cycle
of each color. The continuous generators realize the union of the sets of
positive multiples of those cycle lengths.
-/

namespace CommutingIntervalSimplified

open Function Set

/-- Every nonempty finite set of positive integers prescribes the common
return exponents of a commuting pair of continuous interval maps. -/
theorem exists_commuting_maps_prescribed_nonempty_returns
    (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hne : D.Nonempty) :
    ∃ f g : I → I, Continuous f ∧ Continuous g ∧ Function.Commute f g ∧
      commonReturnExponents f g = {n | 0 < n ∧ ∃ d ∈ D, d ∣ n} := by
  obtain ⟨m, hm, P, hcolor, hperiod⟩ := exists_alternatingSuccessor D hpos hne
  obtain ⟨S, hnext⟩ := exists_equalCellSystem hm P hcolor
  obtain ⟨F, z, hcont, hcomm, hmaps, hown, hopp⟩ := S.exists_commuting_generators
  let R : ReturnCells F (Fin (2 * m)) :=
    { color := S.color
      next := S.next
      cell := S.cell
      core := fun j => range (S.sectionMap j)
      cover := S.cover
      core_subset := fun j _ ⟨x, hx⟩ => hx ▸ S.section_mem j x
      cell_unique := fun hx hy => S.cell_unique hx hy
      color_next := S.color_next
      opposite_maps := hmaps }
  refine ⟨F false, F true, hcont false, hcont true, hcomm, ?_⟩
  ext n
  change n ∈ commonReturnExponents (F false) (F true) ↔ 0 < n ∧ _
  rw [R.mem_commonReturnExponents_iff z hown hopp]
  change (0 < n ∧ ∃ j, IsPeriodicPt S.next n j) ↔ _
  rw [hnext, hperiod]

end CommutingIntervalSimplified
