import CommutingIntervalSimplified.GradedProjectionRealization
import CommutingIntervalSimplified.GradedProjectionSquare

/-! # Intertwining in all three projection directions

The degree-35 projection is the composite of the horizontal and vertical
projections. Moving a chosen decoder across each elementary projection
therefore proves the diagonal case of Proposition 3.6 on the same family.
-/

namespace CommutingIntervalSimplified.ConcreteProjection

open GradedCells GradedGeometry GradedMarkedCells GradedRealization GradedReturn

noncomputable section

/-- All branch data for the chosen, continuous decoders and geometric projections. -/
def concreteDecoderBranches : Branches I :=
  branchesOfPieces pieces (compatibleOfChart projection projection_chart projection_admissible
    projection_square) (fun hx => section_unique hx ⟨_, rfl⟩)

private theorem intertwine_horizontal (v : Grade) (i : Bool) (x : I) :
    chosenDecoder pieces v i (projection (1,0) v x) =
      projection (1,0) (step i v) (chosenDecoder pieces (step false v) i x) :=
  concreteDecoderBranches.intertwine interval_dist_le_one v i false x

private theorem intertwine_vertical (v : Grade) (i : Bool) (x : I) :
    chosenDecoder pieces v i (projection (0,1) v x) =
      projection (0,1) (step i v) (chosenDecoder pieces (step true v) i x) :=
  concreteDecoderBranches.intertwine interval_dist_le_one v i true x

/-- The decoder and projection identities hold on the two elementary edges
and the diagonal of the grade square. -/
theorem graded_decoder_intertwine (v : Grade) (i : Bool) {w : Grade}
    (hw : w = (1,0) ∨ w = (0,1) ∨ w = (1,1)) (x : I) :
    chosenDecoder pieces v i (projection w v x) =
      projection w (step i v) (chosenDecoder pieces (up w v) i x) := by
  rcases hw with rfl | rfl | rfl
  · exact intertwine_horizontal v i x
  · exact intertwine_vertical v i x
  · rw [← projection_diagonal v, intertwine_horizontal, intertwine_vertical,
      ← projection_diagonal (step i v)]
    cases i <;> rfl

/-- The whole section lies in the relative topological interior of the
physical cell. This includes cells adjoining zero or one. -/
theorem section_range_subset_interior {v : Grade} (J : Cell v) :
    Set.range (sectionMap J) ⊆ interior (physicalCell J) := by
  let N : ℝ := (4*M v : ℕ)
  let k : ℝ := (indexEquiv v J).val
  let U : Set I := {x | k < N*(x : ℝ) ∧ N*(x:ℝ) < k+1}
  have hcont : Continuous (fun x : I => N*(x : ℝ)) := continuous_const.mul continuous_subtype_val
  have hopen : IsOpen U := (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hsub : U ⊆ physicalCell J := by
    rw [physicalCell_eq]
    exact fun _ h => ⟨h.1.le,h.2.le⟩
  rintro x ⟨u,rfl⟩
  apply interior_maximal hsub hopen
  have hN : N ≠ 0 := by
    dsimp [N]
    have := M_pos v
    positivity
  change k < N*(chart J (GradedShoulderDecoders.sectionCoord u) : ℝ) ∧
    N*(chart J (GradedShoulderDecoders.sectionCoord u) : ℝ) < k+1
  rw [chart_val]
  change k < N*((k+_)/N) ∧ N*((k+_)/N) < k+1
  rw [mul_div_cancel₀ _ hN]
  change k < k + (if forward J then (1+(u:ℝ))/3 else 1-(1+(u:ℝ))/3) ∧ _
  by_cases h : forward J <;> simp only [h, if_true, if_false] <;>
    constructor <;> dsimp [GradedShoulderDecoders.sectionCoord] <;>
    linarith [u.2.1, u.2.2]

/-- The opposite same-grade map sends a closed cell into the section of its
successor, hence into the successor's topological interior (Corollary 3.7). -/
theorem opposite_maps_successor_interior {v : Grade} (J : Cell v) :
    Set.MapsTo ((concreteDecoderBranches.squares interval_dist_le_one).map v (!color J))
      (physicalCell J) (interior (physicalCell (next J))) := by
  intro x hx
  apply section_range_subset_interior
  exact ((concreteDecoderBranches.atlas interval_dist_le_one).cells v).opposite_maps J hx

end
end CommutingIntervalSimplified.ConcreteProjection
