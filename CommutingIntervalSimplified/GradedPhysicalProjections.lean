import CommutingIntervalSimplified.GradedChartTransfer
import CommutingIntervalSimplified.GradedFoldProjection
import CommutingIntervalSimplified.GradedProjectionFamily

/-! # Compatible projections on the physical graded intervals

Each fine cell uses its normalized projection, transported to its projected
coarse chart. The formulas on both sides of a shared endpoint equal the
standard fold there. Their common contraction factor is independent of the
grade, so the whole infinite system can be solved simultaneously. -/

namespace CommutingIntervalSimplified.ConcreteProjection

open Function Set GradedCells GradedGeometry GradedMarkedCells GradedFoldProjection
  GradedProjection DecoderProjection
open scoped NNReal BoundedContinuousFunction

noncomputable section

private def updatedCoord (w v : Grade) (J : Cell (up w v)) (r : IntervalFunction) (u : I) : I :=
  projIcc 0 1 zero_le_one ((chartMatch w v J).map (extend r) u)

private theorem updatedCoord_val (w v : Grade) (J : Cell (up w v)) (r : IntervalFunction)
    (hr : GridAdmissible (density (step (color J) v)) (degree w) (extend r)) (u : I) :
    (updatedCoord w v J r u : ℝ) = (chartMatch w v J).map (extend r) u := by
  let h := (chartMatch w v J).mapsTo hr (density_pos _) (degree_pos _) (degree_odd _) u.property
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one h)

private def liftCell (w v : Grade) (J : Cell (up w v)) (r : IntervalFunction) (x : I) : I :=
  chart (down w v J) (updatedCoord w v J r (coord J x))

private theorem lift_endpoint (w v : Grade) (J : Cell (up w v)) (r : IntervalFunction)
    (hr : GridAdmissible (density (step (color J) v)) (degree w) (extend r)) {u : I}
    (hu : u = leftEndpoint ∨ u = rightEndpoint) :
    (liftCell w v J r (chart J u) : ℝ) = fold ((degree w : ℝ)*(chart J u : ℝ)) := by
  rw [standard_chart, liftCell, coord_chart]
  suffices updatedCoord w v J r u = u by rw [this]
  apply Subtype.ext
  rw [updatedCoord_val _ _ _ _ hr]
  rcases hu with rfl | rfl
  · exact (chartMatch w v J).map_zero hr (density_pos _) (degree_pos _) (degree_odd _)
  · exact (chartMatch w v J).map_one hr (density_pos _) (degree_pos _) (degree_odd _)

private theorem cell_contraction (w v : Grade) (J : Cell (up w v)) (r s : IntervalFunction)
    (hr : GridAdmissible (density (step (color J) v)) (degree w) (extend r))
    (hs : GridAdmissible (density (step (color J) v)) (degree w) (extend s)) (x : I) :
    dist (liftCell w v J r x) (liftCell w v J s x) ≤ (1 / 12 : ℝ) * dist r s := by
  let u := coord J x
  have hcoord : dist (updatedCoord w v J r u) (updatedCoord w v J s u) ≤ dist r s / 3 := by
    rw [Subtype.dist_eq, Real.dist_eq, updatedCoord_val w v J r hr, updatedCoord_val w v J s hs]
    apply (chartMatch w v J).map_dist_le hr hs
    intro t _
    change dist (r (projIcc 0 1 zero_le_one t)) (s (projIcc 0 1 zero_le_one t)) ≤ dist r s
    exact BoundedContinuousFunction.dist_coe_le_dist _
  rw [liftCell, liftCell, chart_dist]
  have hN : (1 : ℝ) ≤ M v := by exact_mod_cast M_pos v
  have hpos : (0 : ℝ) < ((4 * M v : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (by decide : 0 < 4) (M_pos v)
  apply (div_le_iff₀ hpos).mpr
  apply hcoord.trans
  push_cast
  nlinarith [mul_nonneg (dist_nonneg (x := r) (y := s)) (sub_nonneg.mpr hN)]

/-- The contraction rule for all cells at a fixed grade displacement. -/
def rule (w : Grade) : LocalRule density (degree w) where
  Piece v := Cell (up w v)
  finite v := inferInstance
  region _ := physicalCell
  closed_region _ := cell_closed
  covers v := GradedGeometry.cover (up w v)
  sourceGrade v J := step (color J) v
  lift := liftCell w
  continuousOn v J r hr := by
    apply Continuous.continuousOn
    apply (continuous_chart (down w v J)).comp
    exact continuous_projIcc.comp (((chartMatch w v J).continuous_map hr
      (density_pos _) (degree_pos _) (degree_odd _)).comp
      (continuous_subtype_val.comp (continuous_coord J)))
  agrees v J K r s hne hr hs x hx hy := by
    obtain ⟨u,hu⟩ := hx
    obtain ⟨t,ht⟩ := hy
    obtain ⟨ha,hb⟩ := chart_shared_endpoint hne (hu.trans ht.symm)
    apply Subtype.ext
    exact ((hu ▸ lift_endpoint w v J r hr ha) : _ = fold ((degree w : ℝ)*(x:ℝ))).trans
      ((ht ▸ lift_endpoint w v K s hs hb) : _ = fold ((degree w : ℝ)*(x:ℝ))).symm
  q := 1/12
  q_lt := by norm_num
  lip v J r s hr hs x _ := by simpa using cell_contraction w v J r s hr hs x
  vertex v J r hr t i hv x hx hcell := by
    apply chart_transfer_vertex w v J hr ((congrArg Subtype.val (chart_coord J hcell)).trans hx)
      (updatedCoord_val w v J r hr _) hv
  piece v J r hr t i ht x hx hcell := by
    apply chart_transfer_piece w v J hr ((congrArg Subtype.val (chart_coord J hcell)).trans hx)
      (updatedCoord_val w v J r hr _) ht

/-- The family of admissible projections from grade `up w v` to grade `v`. -/
def projection (w : Grade) : Family := ((rule w).existsUnique_solution density_pos).choose

theorem projection_admissible (w v : Grade) :
    GridAdmissible (density v) (degree w) (extend (projection w v)) :=
  (((rule w).existsUnique_solution density_pos).choose_spec.1.1 v)

/-- On each whole chart the projection obeys the simultaneous core and
shoulder update, with the unique higher-grade projection as its input. -/
theorem projection_chart (w v : Grade) (J : Cell (up w v)) (u : I) :
    ∃ a : I, projection w v (chart J u) = chart (down w v J) a ∧
      (a : ℝ) = (chartMatch w v J).map (extend (projection w (step (color J) v))) u := by
  let r := projection w (step (color J) v)
  refine ⟨updatedCoord w v J r u, ?_, updatedCoord_val _ _ _ _ (projection_admissible ..) _⟩
  have h := ((rule w).existsUnique_solution density_pos).choose_spec.1.2 v J
    (chart J u) (mem_range_self u)
  change projection w v (chart J u) = chart (down w v J) (updatedCoord w v J r (coord J (chart J u))) at h
  simpa only [coord_chart] using h

end
end CommutingIntervalSimplified.ConcreteProjection
