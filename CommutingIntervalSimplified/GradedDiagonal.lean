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

end
end CommutingIntervalSimplified.ConcreteProjection
