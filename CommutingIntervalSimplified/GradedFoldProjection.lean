import CommutingIntervalSimplified.GradedMarkProjection
import CommutingIntervalSimplified.GradedProjectionGrades

/-! # The ordinary fold preserves all chart parameters

Reducing the fine residue discards an integral number of complete turns.
Thus a fold of the specified degree takes each cell, core and shoulder onto
its projected counterpart, with the same coordinate throughout.
-/

namespace CommutingIntervalSimplified.GradedFoldProjection

open Function Set GradedCells GradedGeometry ConcreteProjection DecoderProjection

theorem standard_chart (w v : Grade) (J : Cell (up w v)) (u : I) :
    fold ((degree w : ℝ) * (chart J u : ℝ)) = chart (down w v J) u := by
  rw [chart_eq_fold, chart_eq_fold]
  let t : ℝ := (2*(residue J).val + ((quarterNumber J.quarter).val + (u:ℝ))/4) / M (up w v)
  change fold ((degree w : ℝ)*fold t) = _
  have h : fold ((degree w : ℝ)*fold t) = fold ((degree w : ℝ)*t) :=
    fold_mul_fold (degree w) t
  rw [h]
  obtain ⟨m,hm⟩ := residue_project_turns (u := v) (v := up w v)
    (Nat.le_add_right ..) (Nat.le_add_right ..) J
  change (residue J).val = (residue (down w v J)).val + M v*m at hm
  have he : (degree w : ℝ)*t = 2*(m:ℤ) +
      (2*(residue (down w v J)).val + ((quarterNumber (down w v J).quarter).val + (u:ℝ))/4) /
      M v := by
    have hv : (M v : ℝ) ≠ 0 := by exact_mod_cast (M_pos v).ne'
    have hw : (M w : ℝ) ≠ 0 := by exact_mod_cast (M_pos w).ne'
    have hreal : (M (up w v) : ℝ) = (M v : ℝ) * M w := by exact_mod_cast M_up w v
    have hres : ((residue J).val : ℝ) = (residue (down w v J)).val + (M v : ℝ)*m := by exact_mod_cast hm
    dsimp only [t]
    rw [degree, hreal, hres]
    change _ = _ + (2 * _ + ((quarterNumber J.quarter).val + (u:ℝ))/4) / M v
    push_cast
    field_simp
    ring
  rw [he, fold_even_translate]

/-- The projection carries any parametrized part of a cell onto the matching
part. In particular this applies to its full interval and to each third. -/
theorem standard_image (w v : Grade) (J : Cell (up w v)) (s : Set I) :
    (fun x : I => (⟨fold ((degree w : ℝ)*x), fold_mem _⟩ : I)) '' (chart J '' s) =
      chart (down w v J) '' s := by
  rw [image_image]
  refine Set.image_congr fun u _ => Subtype.ext (standard_chart w v J u)

end CommutingIntervalSimplified.GradedFoldProjection
