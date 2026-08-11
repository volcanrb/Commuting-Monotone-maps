import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The terminal affine-circle parity argument

The reflection quotient identifies `t` with `-t`.  Thus an affine circle map
fixes the reflection orbit of `t` exactly when its value is either `t` or
`-t`.
-/

namespace CommutingIntervalSimplified

noncomputable section

/-- The additive circle of period one. -/
abbrev UnitAddCircle := AddCircle (1 : ℝ)

/-- The affine circle map `t ↦ k t + α`, where `k` may be negative. -/
def affineCircleMap (k : ℤ) (α : UnitAddCircle) (t : UnitAddCircle) :
    UnitAddCircle :=
  k • t + α

/-- The reflection of the parameter circle used in the terminal quotient. -/
def circleReflection (t : UnitAddCircle) : UnitAddCircle :=
  -t

/--
`f` preserves the reflection orbit of `t`, equivalently it fixes the image
of `t` in the quotient by `t ∼ -t`.
-/
def PreservesReflectionOrbitAt (f : UnitAddCircle → UnitAddCircle)
    (t : UnitAddCircle) : Prop :=
  f t = t ∨ f t = circleReflection t

/-- The half-turn translation on the unit additive circle. -/
def circleHalf : UnitAddCircle :=
  ((1 / 2 : ℝ) : UnitAddCircle)

/-- The quarter-turn point used in the parity argument. -/
def circleQuarter : UnitAddCircle :=
  ((1 / 4 : ℝ) : UnitAddCircle)

private lemma unitAddCircle_coe_eq_of_sub_eq_int (x y : ℝ) (n : ℤ)
    (h : x - y = (n : ℝ)) :
    (x : UnitAddCircle) = (y : UnitAddCircle) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub]
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simpa [zsmul_eq_mul] using h.symm⟩

private lemma circleHalf_ne_zero : circleHalf ≠ (0 : UnitAddCircle) := by
  intro h
  change ((1 / 2 : ℝ) : UnitAddCircle) = 0 at h
  rw [AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have : (n : ℝ) = 1 / 2 := by simpa [zsmul_eq_mul] using hn
  have htwoReal : (2 : ℝ) * (n : ℝ) = 1 := by rw [this]; norm_num
  have htwoInt : (2 : ℤ) * n = 1 := by exact_mod_cast htwoReal
  have hone : Even (1 : ℤ) := ⟨n, by simpa [two_mul] using htwoInt.symm⟩
  simp at hone

private lemma evenForm_smul_circleHalf (m : ℤ) :
    (2 * m) • circleHalf = (0 : UnitAddCircle) := by
  change (((2 * m) • (1 / 2 : ℝ) : ℝ) : UnitAddCircle) = 0
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨m, ?_⟩
  ring

private lemma oddForm_smul_circleHalf (m : ℤ) :
    (2 * m + 1) • circleHalf = circleHalf := by
  change (((2 * m + 1) • (1 / 2 : ℝ) : ℝ) : UnitAddCircle) =
    ((1 / 2 : ℝ) : UnitAddCircle)
  apply unitAddCircle_coe_eq_of_sub_eq_int _ _ m
  ring

private lemma oddForm_smul_circleQuarter_orbit (m : ℤ) :
    (2 * m + 1) • circleQuarter = circleQuarter ∨
      (2 * m + 1) • circleQuarter = -circleQuarter := by
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' m
  · subst m
    left
    change ((((2 * (2 * n) + 1) • (1 / 4 : ℝ) : ℝ)) : UnitAddCircle) =
      ((1 / 4 : ℝ) : UnitAddCircle)
    apply unitAddCircle_coe_eq_of_sub_eq_int _ _ n
    ring
  · subst m
    right
    change ((((2 * (2 * n + 1) + 1) • (1 / 4 : ℝ) : ℝ)) : UnitAddCircle) =
      ((-(1 / 4 : ℝ)) : UnitAddCircle)
    apply unitAddCircle_coe_eq_of_sub_eq_int _ _ (n + 1)
    push_cast
    ring

private lemma smul_circleQuarter_orbit_of_smul_circleHalf (k : ℤ)
    (hk : k • circleHalf = circleHalf) :
    k • circleQuarter = circleQuarter ∨ k • circleQuarter = -circleQuarter := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · rw [hm, evenForm_smul_circleHalf] at hk
    exact (circleHalf_ne_zero hk.symm).elim
  · rw [hm]
    exact oddForm_smul_circleQuarter_orbit m

private lemma circleQuarter_add_circleHalf :
    circleQuarter + circleHalf = -circleQuarter := by
  change (((1 / 4 : ℝ) + 1 / 2 : ℝ) : UnitAddCircle) =
    ((-(1 / 4 : ℝ)) : UnitAddCircle)
  apply unitAddCircle_coe_eq_of_sub_eq_int _ _ 1
  norm_num

private lemma neg_circleQuarter_add_circleHalf :
    -circleQuarter + circleHalf = circleQuarter := by
  change ((-(1 / 4 : ℝ) + 1 / 2 : ℝ) : UnitAddCircle) =
    ((1 / 4 : ℝ) : UnitAddCircle)
  congr 1
  norm_num

private lemma zeroTranslation_preserves_quarter (k : ℤ)
    (hk : k • circleHalf = circleHalf) :
    PreservesReflectionOrbitAt (affineCircleMap k 0) circleQuarter := by
  simpa [PreservesReflectionOrbitAt, affineCircleMap, circleReflection] using
    smul_circleQuarter_orbit_of_smul_circleHalf k hk

private lemma halfTranslation_preserves_quarter (k : ℤ)
    (hk : k • circleHalf = circleHalf) :
    PreservesReflectionOrbitAt (affineCircleMap k circleHalf) circleQuarter := by
  rcases smul_circleQuarter_orbit_of_smul_circleHalf k hk with h | h
  · right
    simp only [affineCircleMap, h]
    exact circleQuarter_add_circleHalf
  · left
    simp only [affineCircleMap, h]
    exact neg_circleQuarter_add_circleHalf

private lemma translation_relation_of_commute (k ℓ : ℤ) (α β : UnitAddCircle)
    (hcomm : Function.Commute (affineCircleMap k α) (affineCircleMap ℓ β)) :
    k • β + α = ℓ • α + β := by
  simpa [affineCircleMap] using hcomm 0

/--
Two commuting affine maps of the unit circle whose translations commute with
the reflection `t ↦ -t` have a common fixed reflection orbit.

The hypotheses `hα` and `hβ` are the concrete form of commuting with that
reflection: each translation is either zero or the half-turn.  No sign
condition is imposed on the integer degrees.
-/
theorem exists_common_reflection_orbit_of_half_translations
    (k ℓ : ℤ) (α β : UnitAddCircle)
    (hα : α = 0 ∨ α = circleHalf)
    (hβ : β = 0 ∨ β = circleHalf)
    (hcomm : Function.Commute (affineCircleMap k α) (affineCircleMap ℓ β)) :
    ∃ t : UnitAddCircle,
      PreservesReflectionOrbitAt (affineCircleMap k α) t ∧
        PreservesReflectionOrbitAt (affineCircleMap ℓ β) t := by
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
  · exact ⟨0, by simp [PreservesReflectionOrbitAt, affineCircleMap, circleReflection]⟩
  · have hrel := translation_relation_of_commute k ℓ 0 circleHalf hcomm
    have hk : k • circleHalf = circleHalf := by simpa using hrel
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' ℓ
    · have hℓ : ℓ • circleHalf = 0 := by simpa [hm] using evenForm_smul_circleHalf m
      refine ⟨circleHalf, ?_, ?_⟩
      · left
        simpa [affineCircleMap] using hk
      · left
        simp [affineCircleMap, hℓ]
    · have hℓ : ℓ • circleHalf = circleHalf := by
        simpa [hm] using oddForm_smul_circleHalf m
      exact ⟨circleQuarter, zeroTranslation_preserves_quarter k hk,
        halfTranslation_preserves_quarter ℓ hℓ⟩
  · have hrel := translation_relation_of_commute k ℓ circleHalf 0 hcomm
    have hℓ : ℓ • circleHalf = circleHalf := by simpa using hrel.symm
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · have hk : k • circleHalf = 0 := by simpa [hm] using evenForm_smul_circleHalf m
      refine ⟨circleHalf, ?_, ?_⟩
      · left
        simp [affineCircleMap, hk]
      · left
        simpa [affineCircleMap] using hℓ
    · have hk : k • circleHalf = circleHalf := by
        simpa [hm] using oddForm_smul_circleHalf m
      exact ⟨circleQuarter, halfTranslation_preserves_quarter k hk,
        zeroTranslation_preserves_quarter ℓ hℓ⟩
  · have hrel := translation_relation_of_commute k ℓ circleHalf circleHalf hcomm
    have hsame : k • circleHalf = ℓ • circleHalf := by
      exact add_right_cancel hrel
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · have hk : k • circleHalf = 0 := by simpa [hm] using evenForm_smul_circleHalf m
      have hℓ : ℓ • circleHalf = 0 := hsame ▸ hk
      refine ⟨circleHalf, ?_, ?_⟩
      · left
        simp [affineCircleMap, hk]
      · left
        simp [affineCircleMap, hℓ]
    · have hk : k • circleHalf = circleHalf := by
        simpa [hm] using oddForm_smul_circleHalf m
      have hℓ : ℓ • circleHalf = circleHalf := hsame ▸ hk
      exact ⟨circleQuarter, halfTranslation_preserves_quarter k hk,
        halfTranslation_preserves_quarter ℓ hℓ⟩

end

end CommutingIntervalSimplified
