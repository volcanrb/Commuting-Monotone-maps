import CommutingIntervalSimplified.GradedMarkedCells
import CommutingIntervalSimplified.DecoderProjectionChart

/-! # Compatibility of the actual decoder shoulders

The CRT mark comparison gives the even shift. Since the coarse mark is a
vertex, translating it by an even integer preserves the vertex condition
on the unfolded mesh. The sign of the core endpoint depends only on the
side of the cell, so corresponding shoulders have the same core value.
-/

namespace CommutingIntervalSimplified.ConcreteProjection

open GradedCells GradedGeometry GradedMarkedCells GradedShoulderDecoders DecoderProjection

/-- The normalized shoulders of a fine cell match those of its coarse label,
including at same-colour junctions and global endpoints. -/
noncomputable def chartMatch (w v : Grade) (J : Cell (up w v)) :
    ChartMatch (density (step (color J) v)) (degree w) (beta J) (beta (down w v J)) where
  shift s := (beta_projection w v J s).choose
  matched s := by
    let n := (beta_projection w v J s).choose
    have h : (degree w : ℝ) * beta J s = beta (down w v J) s + 2 * n :=
      (beta_projection w v J s).choose_spec
    refine ⟨h, ?_, by simp only [normalized_coreValue]⟩
    obtain ⟨z, hz⟩ := markCoordinate_vertex (markCell (down w v J) s)
    change (density (step (color J) v) : ℝ) * beta (down w v J) s = z at hz
    refine ⟨z + 2 * density (step (color J) v) * n, ?_⟩
    change (density (step (color J) v) : ℝ) * ((degree w : ℝ) * beta J s) = _
    rw [h, mul_add, hz]
    push_cast
    ring

end CommutingIntervalSimplified.ConcreteProjection
