import CommutingIntervalSimplified.FiniteReturnConstruction
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Equal cells, inner sections, and continuous decoders

In the coordinate `t = N*x - j`, the closed cell is the unit interval and
the section occupies its middle third. The decoder interpolates the marks
at the two ends and inverts the section on that middle third.
-/

namespace CommutingIntervalSimplified

open Set
open scoped NNReal

namespace EqualCell

variable {N : ℕ}

def cell (j : Fin N) : Set I :=
  {x | (j.val : ℝ) ≤ N * (x : ℝ) ∧ (N : ℝ) * x ≤ j.val + 1}

private theorem npos (j : Fin N) : 0 < (N : ℝ) := by
  exact_mod_cast Nat.zero_lt_of_lt j.isLt

private noncomputable def sectionMap (j : Fin N) (x : I) : I :=
  ⟨(j.val + (1 + (x : ℝ)) / 3) / N, by
    have h := npos j
    have hj : (j.val : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
    constructor
    · apply div_nonneg _ h.le
      linarith [Nat.cast_nonneg (α := ℝ) j.val, x.property.1]
    · apply (div_le_iff₀ h).mpr
      linarith [x.property.2]⟩

private theorem scale_section (j : Fin N) (x : I) :
    (N : ℝ) * (sectionMap j x : ℝ) = j.val + (1 + (x : ℝ)) / 3 := by
  change _ * (_ / _) = _
  field_simp [ne_of_gt (npos j)]

private theorem section_strict (j : Fin N) (x : I) :
    (j.val : ℝ) < N * (sectionMap j x : ℝ) ∧
      (N : ℝ) * (sectionMap j x : ℝ) < j.val + 1 := by
  rw [scale_section]
  constructor <;> linarith [x.property.1, x.property.2]

theorem cover (hN : 0 < N) (x : I) : ∃ j : Fin N, x ∈ cell j := by
  let u := (N : ℝ) * (x : ℝ)
  have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg _) x.property.1
  have hu' : u ≤ N := by
    dsimp [u]
    simpa using mul_le_mul_of_nonneg_left x.property.2 (Nat.cast_nonneg N : 0 ≤ (N : ℝ))
  by_cases h : ⌊u⌋₊ < N
  · exact ⟨⟨_, h⟩, Nat.floor_le hu, (Nat.lt_floor_add_one u).le⟩
  · have hlu : N ≤ ⌊u⌋₊ := Nat.le_of_not_gt h
    have he : (N : ℝ) = u :=
      le_antisymm ((Nat.cast_le.mpr hlu).trans (Nat.floor_le hu)) hu'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    refine ⟨⟨k, Nat.lt_succ_self k⟩, ?_⟩
    change (k : ℝ) ≤ u ∧ u ≤ k + 1
    rw [← he, Nat.cast_succ]
    exact ⟨by linarith, le_rfl⟩

private noncomputable def mark (P : Fin N → Fin N) (n : ℕ) : I :=
  if h : n < N then sectionMap (P ⟨n, h⟩) leftEndpoint else leftEndpoint

/-- A real-valued interpolation formula, clipped only to extend the decoder
continuously to all of the ambient interval. -/
private noncomputable def decoderValue (a b : I) (t : ℝ) : I :=
  projIcc 0 1 zero_le_one
    ((a : ℝ) * max 0 (1 - 3*t) + min 1 (max 0 (3*t - 1)) + ((b : ℝ) - 1) * max 0 (3*t - 2))

private noncomputable def decoder (P : Fin N → Fin N) (j : Fin N) (x : I) : I :=
  decoderValue (mark P (j.val - 1)) (mark P (j.val + 1)) (N * (x : ℝ) - j.val)

private theorem decoder_cont (P : Fin N → Fin N) (j : Fin N) : Continuous (decoder P j) := by
  unfold decoder decoderValue
  exact continuous_projIcc.comp (by fun_prop)

private theorem at_zero (a b : I) : decoderValue a b 0 = a := by
  simp [decoderValue, projIcc_of_mem (h := zero_le_one) a.property]

private theorem at_one (a b : I) : decoderValue a b 1 = b := by
  unfold decoderValue
  convert projIcc_of_mem (h := zero_le_one) b.property using 2
  norm_num

private theorem at_core (a b x : I) : decoderValue a b ((1 + (x : ℝ)) / 3) = x := by
  unfold decoderValue
  have h₁ : 1 - 3 * ((1 + (x : ℝ)) / 3) ≤ 0 := by linarith [x.property.1]
  have h₂ : 3 * ((1 + (x : ℝ)) / 3) - 1 = x := by ring
  have h₃ : 3 * ((1 + (x : ℝ)) / 3) - 2 ≤ 0 := by linarith [x.property.2]
  rw [max_eq_left h₁, h₂, max_eq_right x.property.1, min_eq_right x.property.2, max_eq_left h₃]
  simp [projIcc_of_mem (h := zero_le_one) x.property]

private theorem section_lip (j : Fin N) : LipschitzWith (1/3 : ℝ≥0) (sectionMap j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Subtype.dist_eq, Real.dist_eq, sectionMap, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.zero_lt_of_lt j.isLt
  rw [show ((j.val : ℝ) + (1 + (x : ℝ)) / 3) / N - (j.val + (1 + (y : ℝ)) / 3) / N =
    ((x : ℝ) - y) / 3 / N by ring, abs_div, abs_div, abs_of_pos (npos j), abs_of_pos (by norm_num : (0:ℝ) < 3)]
  apply (div_le_iff₀ (npos j)).mpr
  nlinarith [abs_nonneg ((x : ℝ) - y), mul_nonneg (sub_nonneg.mpr hN) (abs_nonneg ((x : ℝ) - y))]

private theorem adjacent {j k : Fin N} {x : I} (hne : j ≠ k) (hj : x ∈ cell j)
    (hk : x ∈ cell k) :
    (j.val + 1 = k.val ∧ (N : ℝ) * x = k.val) ∨
    (k.val + 1 = j.val ∧ (N : ℝ) * x = j.val) := by
  have hne' : j.val ≠ k.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with h | h
  · have h' : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast h
    have he := le_antisymm (hk.1.trans hj.2) h'
    exact Or.inl ⟨by exact_mod_cast he.symm, le_antisymm (hj.2.trans h') hk.1⟩
  · have h' : (k.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    have he := le_antisymm (hj.1.trans hk.2) h'
    exact Or.inr ⟨by exact_mod_cast he.symm, le_antisymm (hk.2.trans h') hj.1⟩

private theorem unique_core {j k : Fin N} {x : I} (hj : x ∈ cell j)
    (hk : x ∈ range (sectionMap k)) : j = k := by
  obtain ⟨y, rfl⟩ := hk
  obtain ⟨hl, hr⟩ := section_strict k y
  by_contra h
  rcases adjacent h hj ⟨hl.le, hr.le⟩ with ⟨_, he⟩ | ⟨hv, he⟩
  · exact (ne_of_gt hl) he
  · have hv' : (k.val : ℝ) + 1 = j.val := by exact_mod_cast hv
    linarith

private theorem overlap {P : Fin N → Fin N} {j k : Fin N} {x : I}
    (hne : j ≠ k) (hj : x ∈ cell j) (hk : x ∈ cell k) :
    decide (j.val % 2 = 1) ≠ decide (k.val % 2 = 1) ∧
      decoder P j x = sectionMap (P k) leftEndpoint := by
  rcases adjacent hne hj hk with ⟨hs, hx⟩ | ⟨hs, hx⟩
  · constructor
    · simp only [ne_eq, decide_eq_decide]; omega
    · have hs' : (j.val : ℝ) + 1 = k.val := by exact_mod_cast hs
      rw [decoder, show (N : ℝ) * (x : ℝ) - j.val = 1 by linarith, at_one, hs]
      simp [mark, k.isLt]
  · constructor
    · simp only [ne_eq, decide_eq_decide]; omega
    · have hk' : j.val - 1 = k.val := by omega
      rw [decoder, hx, sub_self, at_zero, hk']
      simp [mark, k.isLt]

end EqualCell

/-- A parity-preserving permutation acts on a partition into equal closed cells
with all the sections, endpoint marks, and decoders required for gluing. -/
theorem exists_equalCellSystem {m : ℕ} (hm : 0 < m) (P : Equiv.Perm (Fin (2*m)))
    (hP : ∀ j, (P j).val % 2 = j.val % 2) :
    ∃ S : FiniteDecoderSystem (Fin (2*m)), S.next = ⇑P := by
  classical
  refine ⟨{
    color := fun j => decide (j.val % 2 = 1)
    next := P
    cell := EqualCell.cell
    cell_closed := fun j => by
      have hc : Continuous (fun x : I => ((2*m : ℕ) : ℝ) * (x : ℝ)) := by fun_prop
      exact (isClosed_le (show Continuous (fun _ : I => (j.val : ℝ)) from continuous_const) hc).inter
        (isClosed_le hc (show Continuous (fun _ : I => (j.val : ℝ) + 1) from continuous_const))
    cover := EqualCell.cover (by omega)
    color_next := fun j => by simp [hP j]
    sectionMap := EqualCell.sectionMap
    decoder := EqualCell.decoder P
    decoder_cont := EqualCell.decoder_cont P
    q := 1/3
    q_lt := by norm_num
    section_lip := EqualCell.section_lip
    section_mem := fun j x => ⟨(EqualCell.section_strict j x).1.le, (EqualCell.section_strict j x).2.le⟩
    decode_section := fun j x => by
      rw [EqualCell.decoder, EqualCell.scale_section, add_sub_cancel_left, EqualCell.at_core]
    overlap := EqualCell.overlap
    cell_unique := EqualCell.unique_core }, rfl⟩

end CommutingIntervalSimplified
