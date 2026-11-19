import CommutingIntervalSimplified.GradedCellGeometry

/-!
# Transfer of chart thirds to the unfolded mesh

The scaled affine coordinate of a folded chart has the form `a ± 3u`,
with integral `a`. This identifies the normalized thirds exactly with the
mesh intervals, on every sheet of the triangular fold. At a shared vertex,
both incident mesh intervals are respected by fixing the vertex itself.
-/

namespace CommutingIntervalSimplified.GradedGeometry

open Set GradedCells DecoderProjection

private theorem dilated_translate (d n : ℤ) (x : ℝ) :
    fold (d * (2*n + x)) = fold (d*x) := by
  have h : (d:ℝ) * (2*n + x) = 2*((d*n:ℤ):ℝ) + d*x := by push_cast; ring
  rw [h, fold_even_translate]

private theorem dilated_reflect (d n : ℤ) (x : ℝ) :
    fold (d * (2*n - x)) = fold (d*x) := by
  have h : (d:ℝ) * (2*n - x) = 2*((d*n:ℤ):ℝ) + -(d*x) := by push_cast; ring
  rw [h, fold_even_translate, fold_neg]

/-- Using the physical chart or any other lift of the same point gives the
same projected value after integral dilation. -/
theorem fold_dilated_chart_eq {v : Grade} (J : Cell v) {u : I} {t : ℝ}
    (hx : (chart J u : ℝ) = fold t) (d : ℤ) :
    fold (d * (chart J u : ℝ)) = fold (d*t) := by
  obtain ⟨n, ht | ht⟩ := exists_even_translate t
  · rw [← hx] at ht
    rw [ht, dilated_translate]
  · rw [← hx] at ht
    rw [ht, dilated_reflect]

private theorem chart_affine_scaled {v : Grade} (J : Cell v) {m d : ℤ}
    (hmd : m*d = 12*(M v : ℤ)) :
    ∃ a : ℤ, (∀ u : I, (m : ℝ)*(d*(chart J u : ℝ)) = a+3*(u:ℝ)) ∨
              (∀ u : I, (m : ℝ)*(d*(chart J u : ℝ)) = a-3*(u:ℝ)) := by
  have hm : (m:ℝ)*d = 3*((4*M v : ℕ):ℝ) := by
    have h : (m:ℝ)*d = 12*(M v:ℝ) := by exact_mod_cast hmd
    push_cast
    linarith
  have hM : (M v : ℝ) ≠ 0 := by exact_mod_cast (M_pos v).ne'
  by_cases h : forward J
  · refine ⟨3*(indexEquiv v J).val, Or.inl (fun u => ?_)⟩
    rw [← mul_assoc, hm, chart_val, if_pos h]
    push_cast
    field_simp [hM]
  · refine ⟨3*((indexEquiv v J).val+1), Or.inr (fun u => ?_)⟩
    rw [← mul_assoc, hm, chart_val, if_neg h]
    push_cast
    field_simp [hM]
    ring

/-- Lift the entire chart to the same sheet as a prescribed representative
of one of its points. -/
private theorem chart_mesh_lift {v : Grade} (J : Cell v) {m d : ℤ}
    (hmd : m*d = 12*(M v : ℤ)) {u : I} {t : ℝ} (hx : (chart J u : ℝ) = fold t) :
    ∃ (L : I → ℝ) (a : ℤ), L u = d*t ∧
      (∀ z, fold (L z) = fold (d*(chart J z : ℝ))) ∧
      ((∀ z : I, (m:ℝ)*L z = a + 3*(z:ℝ)) ∨ (∀ z : I, (m:ℝ)*L z = a - 3*(z:ℝ))) := by
  obtain ⟨a, hsign⟩ := chart_affine_scaled J hmd
  obtain ⟨n, ht | ht⟩ := exists_even_translate t
  · rw [← hx] at ht
    refine ⟨fun z => (d:ℝ)*(2*n+(chart J z : ℝ)), 2*m*d*n+a, by rw [ht],
      fun z => dilated_translate d n _, ?_⟩
    rcases hsign with h | h
    · left; intro z; dsimp only; push_cast; linarith only [h z]
    · right; intro z; dsimp only; push_cast; linarith only [h z]
  · rw [← hx] at ht
    refine ⟨fun z => (d:ℝ)*(2*n-(chart J z : ℝ)), 2*m*d*n-a, by rw [ht],
      fun z => dilated_reflect d n _, ?_⟩
    rcases hsign with h | h
    · right; intro z; dsimp only; push_cast; linarith only [h z]
    · left; intro z; dsimp only; push_cast; linarith only [h z]

/-- At any unfolded mesh vertex the local chart parameter is a third vertex. -/
theorem chart_mesh_vertex {v : Grade} (J : Cell v) {m d : ℤ}
    (hmd : m*d = 12*(M v : ℤ)) {u : I} {t : ℝ} {i : ℤ}
    (hx : (chart J u : ℝ) = fold t) (hv : (m:ℝ)*(d*t) = i) :
    ∃ k : ℤ, 3*(u:ℝ) = k := by
  obtain ⟨L, a, hL, _, hs | hs⟩ := chart_mesh_lift J hmd hx
  · refine ⟨i-a, ?_⟩; push_cast; rw [← hL, hs] at hv; linarith
  · refine ⟨a-i, ?_⟩; push_cast; rw [← hL, hs] at hv; linarith

/-- Updating a chart parameter within its third and fixing third vertices
preserves the folded mesh interval of every representative, including both
closed intervals meeting at a vertex. -/
theorem chart_mesh_piece {v : Grade} (J : Cell v) {m d : ℤ}
    (hmd : m*d = 12*(M v : ℤ)) {u u' : I} {t : ℝ} {i : ℤ}
    (hx : (chart J u : ℝ) = fold t) (ht : (d:ℝ)*t ∈ mesh m i) (k : ℤ)
    (hu : 3*(u:ℝ) ∈ Icc (k:ℝ) (k+1)) (hu' : 3*(u':ℝ) ∈ Icc (k:ℝ) (k+1))
    (hfix : (∃ l : ℤ, 3*(u:ℝ) = l) → u' = u) :
    fold (d*(chart J u' : ℝ)) ∈ fold '' mesh m i := by
  by_cases h : ∃ l : ℤ, 3*(u:ℝ) = l
  · rw [hfix h, fold_dilated_chart_eq J hx d]
    exact mem_image_of_mem _ ht
  have hlo : (k:ℝ) < 3*(u:ℝ) := lt_of_le_of_ne hu.1 (fun e => h ⟨k, e.symm⟩)
  have hhi : 3*(u:ℝ) < k+1 := lt_of_le_of_ne hu.2 (fun e => h ⟨k+1, by exact_mod_cast e⟩)
  obtain ⟨L, a, hL, hfold, hs⟩ := chart_mesh_lift J hmd hx
  refine ⟨L u', ?_, hfold u'⟩
  change (m:ℝ)*(d*t) ∈ Icc (i:ℝ) (i+1) at ht
  change (m:ℝ)*L u' ∈ Icc (i:ℝ) (i+1)
  rcases hs with hs | hs
  · rw [← hL, hs] at ht
    have h₁ : i < a+k+1 := by exact_mod_cast (show (i:ℝ) < (a:ℝ)+k+1 by linarith [ht.1])
    have h₂ : a+k < i+1 := by exact_mod_cast (show (a:ℝ)+k < (i:ℝ)+1 by linarith [ht.2])
    have hi : i = a+k := by omega
    rw [hs, hi]; push_cast; exact ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
  · rw [← hL, hs] at ht
    have h₁ : i < a-k := by exact_mod_cast (show (i:ℝ) < (a:ℝ)-k by linarith [ht.1])
    have h₂ : a-k-1 < i+1 := by exact_mod_cast (show (a:ℝ)-k-1 < (i:ℝ)+1 by linarith [ht.2])
    have hi : i = a-k-1 := by omega
    rw [hs, hi]; push_cast; exact ⟨by linarith [hu'.2], by linarith [hu'.1]⟩

end CommutingIntervalSimplified.GradedGeometry
