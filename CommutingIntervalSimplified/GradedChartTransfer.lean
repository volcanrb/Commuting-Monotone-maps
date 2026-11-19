import CommutingIntervalSimplified.GradedChartAdmissibility
import CommutingIntervalSimplified.GradedConcreteMatch
import CommutingIntervalSimplified.GradedFoldProjection

/-! # Grid admissibility of the actual normalized chart update -/

namespace CommutingIntervalSimplified.ConcreteProjection

open Set GradedCells GradedGeometry GradedFoldProjection DecoderProjection

private theorem chart_transfer_fix (w v : Grade) (J : Cell (up w v)) {r : ℝ → ℝ}
    (hr : GridAdmissible (density (step (color J) v)) (degree w) r) {u a : I}
    (ha : (a:ℝ) = (chartMatch w v J).map r u) (hv : ∃ k : ℤ, 3*(u:ℝ) = k) :
    a = u := by
  obtain ⟨k, hk⟩ := hv
  have hlo : (0:ℤ) ≤ k := by exact_mod_cast (show (0:ℝ) ≤ k by linarith [u.property.1])
  have hhi : k ≤ (3:ℤ) := by exact_mod_cast (show (k:ℝ) ≤ 3 by linarith [u.property.2])
  apply Subtype.ext
  rw [ha]
  let P := chartMatch w v J
  change P.map r (u:ℝ) = u
  have hm := density_pos (step (color J) v)
  have hd := degree_pos w
  have ho := degree_odd w
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · norm_num at hk
    simpa only [hk] using P.map_zero hr hm hd ho
  · norm_num at hk
    simpa only [show (u:ℝ) = 1/3 by linarith] using P.map_one_third hr hm hd ho
  · norm_num at hk
    simpa only [show (u:ℝ) = 2/3 by linarith] using P.map_two_thirds hr hm hd ho
  · norm_num at hk
    simpa only [hk] using P.map_one hr hm hd ho

/-- The concrete normalized update agrees with the standard fold on every
vertex of the unfolded mesh. -/
theorem chart_transfer_vertex (w v : Grade) (J : Cell (up w v)) {r : ℝ → ℝ}
    (hr : GridAdmissible (density (step (color J) v)) (degree w) r)
    {u a : I} {t : ℝ} {i : ℤ} (hx : (chart J u : ℝ) = fold t)
    (ha : (a:ℝ) = (chartMatch w v J).map r u)
    (hv : (density v : ℝ)*(degree w*t) = i) :
    (chart (down w v J) a : ℝ) = fold (degree w*t) := by
  have e := chart_mesh_vertex J (density_up w v).symm hx hv
  rw [chart_transfer_fix w v J hr ha e, ← standard_chart]
  exact fold_dilated_chart_eq J hx (degree w)

/-- The concrete normalized update preserves the folded mesh interval of
every lift, including either neighboring interval at a common endpoint. -/
theorem chart_transfer_piece (w v : Grade) (J : Cell (up w v)) {r : ℝ → ℝ}
    (hr : GridAdmissible (density (step (color J) v)) (degree w) r)
    {u a : I} {t : ℝ} {i : ℤ} (hx : (chart J u : ℝ) = fold t)
    (ha : (a:ℝ) = (chartMatch w v J).map r u)
    (ht : (degree w:ℝ)*t ∈ mesh (density v) i) :
    (chart (down w v J) a : ℝ) ∈ fold '' mesh (density v) i := by
  let P := chartMatch w v J
  obtain ⟨k, hu, hmap⟩ : ∃ k : ℤ, 3*(u:ℝ) ∈ Icc (k:ℝ) (k+1) ∧
      3*(a:ℝ) ∈ Icc (k:ℝ) (k+1) := by
    have hm := density_pos (step (color J) v)
    have hd := degree_pos w
    change (a:ℝ) = P.map r u at ha
    rw [ha]
    by_cases hl : (u:ℝ) ≤ 1/3
    · obtain ⟨h₁, h₂⟩ := P.left_third hr hm hd ⟨u.property.1, hl⟩
      exact ⟨0, ⟨by push_cast; linarith [u.property.1], by push_cast; linarith⟩,
        ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
    by_cases hh : 2/3 ≤ (u:ℝ)
    · obtain ⟨h₁, h₂⟩ := P.right_third hr hm hd ⟨hh, u.property.2⟩
      exact ⟨2, ⟨by push_cast; linarith, by push_cast; linarith [u.property.2]⟩,
        ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
    · obtain ⟨h₁, h₂⟩ := P.middle_third hr hm hd (degree_odd w) ⟨le_of_not_ge hl, le_of_not_ge hh⟩
      exact ⟨1, ⟨by push_cast; linarith, by push_cast; linarith⟩,
        ⟨by push_cast; linarith, by push_cast; linarith⟩⟩
  rw [← standard_chart]
  exact chart_mesh_piece J (density_up w v).symm hx ht k hu hmap (chart_transfer_fix w v J hr ha)

end CommutingIntervalSimplified.ConcreteProjection
