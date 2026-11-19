import CommutingIntervalSimplified.Base
import CommutingIntervalSimplified.DecoderProjection
import CommutingIntervalSimplified.GradedCells

/-!
# The explicit shoulder decoders

For a marked shoulder, the decoder follows a triangular fold from the mark
to one end of the core, traversing a complete last sheet. The two shoulders
paste to the inverse of the central section. We use normalized cell coordinates
so this construction also applies to orientation-reversing charts.
-/

namespace CommutingIntervalSimplified.GradedShoulderDecoders

open Set GradedCells DecoderProjection
noncomputable section

/-- The outer mark at a normalized endpoint. The distinguished residue-zero
mark covers both global endpoints and junctions of two equal-colour cells. -/
def markCell {v : Grade} (J : Cell v) (right : Bool) : Cell (step (color J) v) := by
  rcases J with ⟨q,a,b⟩
  cases q with
  | left => exact sevenCell (if right then b + (1 : ZMod (7 ^ v.2)) else 0)
  | second => exact fiveCell (if right then a + (1 : ZMod (5 ^ v.1)) else 0)
  | third => exact sevenCell (if right then 0 else b + (1 : ZMod (7 ^ v.2)))
  | right => exact fiveCell (if right then 0 else a + (1 : ZMod (5 ^ v.1)))

/-- Mixed normalized endpoints have the mark specified by the lifted
successor of the incident opposite-color cell. -/
theorem mixed_mark {v : Grade} (a : ZMod (5 ^ v.1)) (b : ZMod (7 ^ v.2)) :
    let J (q : Quarter) : Cell v := ⟨q,a,b⟩
    markCell (J .left) true = liftNext false (J .second) ∧
    markCell (J .second) false = liftNext true (J .left) ∧
    markCell (J .second) true = liftNext true (J .third) ∧
    markCell (J .third) false = liftNext false (J .second) ∧
    markCell (J .third) true = liftNext false (J .right) ∧
    markCell (J .right) false = liftNext true (J .third) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Projection of the marked target cell along any grade increase preserves
both endpoint marks, including those of same-colour junctions. -/
theorem project_mark {u v : Grade} (ha : u.1 ≤ v.1) (hb : u.2 ≤ v.2)
    (J : Cell v) (side : Bool) :
    project (u := step (color J) u) (v := step (color J) v)
      (by cases color J <;> simp [step, ha]) (by cases color J <;> simp [step, hb])
      (markCell J side) = markCell (project ha hb J) side := by
  rcases J with ⟨q, a, b⟩
  cases q <;> cases side <;> simp [markCell, project, step, color, fiveCell, sevenCell] <;>
    constructor <;> first
    | exact ZMod.cast_zero
    | exact (map_add (ZMod.castHom (pow_dvd_pow 5 ha) (ZMod (5 ^ u.1))) _ 1).trans
        (congrArg (_ + ·) (map_one _))
    | exact (map_add (ZMod.castHom (pow_dvd_pow 7 hb) (ZMod (7 ^ u.2))) _ 1).trans
        (congrArg (_ + ·) (map_one _))

/-- The integer in the final sheet is the least integer of the required parity
at least as large as the unfolded mark. The right shoulder uses even parity. -/
def threshold (right : Bool) (β : ℝ) : ℤ :=
  if right then 2 * ⌈β / 2⌉ else 2 * ⌈(β - 1) / 2⌉ + 1

theorem le_threshold (right : Bool) (β : ℝ) : β ≤ (threshold right β : ℝ) := by
  cases right
  · simp only [threshold, Bool.false_eq_true, ↓reduceIte, Int.cast_add, Int.cast_mul,
      Int.cast_ofNat, Int.cast_one]
    linarith [Int.le_ceil ((β-1)/2)]
  · simp only [threshold, ↓reduceIte, Int.cast_mul, Int.cast_ofNat]
    linarith [Int.le_ceil (β/2)]

theorem threshold_le_even {β : ℝ} {n : ℤ} (h : β ≤ 2*(n:ℝ)) :
    threshold true β ≤ 2*n := by
  change 2 * ⌈β/2⌉ ≤ 2*n
  have : ⌈β/2⌉ ≤ n := Int.ceil_le.mpr (by linarith)
  omega

theorem threshold_le_odd {β : ℝ} {n : ℤ} (h : β ≤ 2*(n:ℝ)+1) :
    threshold false β ≤ 2*n+1 := by
  change 2 * ⌈(β-1)/2⌉ + 1 ≤ 2*n+1
  have : ⌈(β-1)/2⌉ ≤ n := Int.ceil_le.mpr (by linarith)
  omega

/-- The affine shoulder parameter, increasing from the mark to the core. -/
def shoulder (right : Bool) (β r : ℝ) : ℝ :=
  fold ((1-r)*β + r*((threshold right β : ℝ)+1))

theorem continuous_shoulder (side : Bool) (β : ℝ) : Continuous (shoulder side β) := by
  unfold shoulder
  apply continuous_fold.comp
  fun_prop

@[simp] theorem shoulder_zero (side : Bool) (β : ℝ) : shoulder side β 0 = fold β := by
  simp [shoulder]

@[simp] theorem shoulder_one_left (β : ℝ) : shoulder false β 1 = 0 := by
  have he : (threshold false β : ℝ) + 1 = 2*((⌈(β-1)/2⌉+1 : ℤ) : ℝ) + 0 := by
    simp [threshold]; ring
  simp only [shoulder, sub_self, zero_mul, one_mul, zero_add, he, fold_even_translate]
  exact fold_eq_self ⟨le_rfl, zero_le_one⟩

@[simp] theorem shoulder_one_right (β : ℝ) : shoulder true β 1 = 1 := by
  simp only [shoulder, sub_self, zero_mul, one_mul, zero_add, threshold, ↓reduceIte,
    Int.cast_mul, Int.cast_ofNat, fold_even_translate]
  exact fold_eq_self ⟨zero_le_one, le_rfl⟩

/-- The full decoder extended to all real normalized coordinates. Only its
restriction to the cell is used. -/
def chartDecoder (β₀ β₁ u : ℝ) : ℝ :=
  if u ≤ 1/3 then shoulder false β₀ (3*u)
  else if 2/3 ≤ u then shoulder true β₁ (3*(1-u))
  else 3*u-1

theorem continuous_chartDecoder (β₀ β₁ : ℝ) : Continuous (chartDecoder β₀ β₁) := by
  unfold chartDecoder
  apply Continuous.if_le
  · exact (continuous_shoulder false _).comp (by fun_prop)
  · apply Continuous.if_le
    · exact (continuous_shoulder true _).comp (by fun_prop)
    · fun_prop
    · exact continuous_const
    · exact continuous_id
    · intro x hx
      change (2:ℝ)/3 = x at hx
      subst x
      norm_num
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    change x = (1:ℝ)/3 at hx
    subst x
    norm_num

theorem chartDecoder_mem (β₀ β₁ u : ℝ) : chartDecoder β₀ β₁ u ∈ Icc (0:ℝ) 1 := by
  unfold chartDecoder
  split
  · exact fold_mem _
  · split
    · exact fold_mem _
    · constructor <;> linarith

theorem chartDecoder_core (β₀ β₁ : ℝ) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    chartDecoder β₀ β₁ ((1+u)/3) = u := by
  have h₀ := hu.1
  have h₁ := hu.2
  by_cases hl : u = 0
  · subst u; norm_num [chartDecoder]
  by_cases hr : u = 1
  · subst u; norm_num [chartDecoder]
  have hu₀ : 0 < u := lt_of_le_of_ne h₀ (Ne.symm hl)
  have hu₁ : u < 1 := lt_of_le_of_ne h₁ hr
  have hl' : ¬(1+u)/3 ≤ 1/3 := by linarith
  have hr' : ¬2/3 ≤ (1+u)/3 := by linarith
  rw [chartDecoder, if_neg hl', if_neg hr']; ring

@[simp] theorem chartDecoder_zero (β₀ β₁ : ℝ) : chartDecoder β₀ β₁ 0 = fold β₀ := by
  norm_num [chartDecoder]

@[simp] theorem chartDecoder_one (β₀ β₁ : ℝ) : chartDecoder β₀ β₁ 1 = fold β₁ := by
  norm_num [chartDecoder]

/-- The first and last closed thirds have exactly the prescribed sheet
interpolations, including the two ends of the central third. -/
theorem chartDecoder_left {u : ℝ} (h : u ≤ 1/3) (β₀ β₁ : ℝ) :
    chartDecoder β₀ β₁ u = shoulder false β₀ (3*u) := if_pos h

theorem chartDecoder_right {u : ℝ} (h : 2/3 ≤ u) (β₀ β₁ : ℝ) :
    chartDecoder β₀ β₁ u = shoulder true β₁ (3*(1-u)) := by
  rw [chartDecoder, if_neg (by linarith), if_pos h]

/-- The normalized central section and decoder as maps of the unit interval. -/
def sectionCoord (x : I) : I :=
  ⟨(1+(x:ℝ))/3, by constructor <;> linarith [x.2.1, x.2.2]⟩

def decoder (β₀ β₁ : ℝ) (u : I) : I :=
  ⟨chartDecoder β₀ β₁ u, chartDecoder_mem ..⟩

theorem continuous_decoder (β₀ β₁ : ℝ) : Continuous (decoder β₀ β₁) :=
  ((continuous_chartDecoder _ _).comp continuous_subtype_val).subtype_mk _

theorem decoder_section (β₀ β₁ : ℝ) : Function.LeftInverse (decoder β₀ β₁) sectionCoord :=
  fun x => Subtype.ext (chartDecoder_core _ _ x.2)

end
end CommutingIntervalSimplified.GradedShoulderDecoders
