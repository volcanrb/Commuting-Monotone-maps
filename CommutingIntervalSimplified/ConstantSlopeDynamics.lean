import CommutingIntervalSimplified.Base
import CommutingIntervalSimplified.PiecewiseMonotoneBase
import Mathlib.Order.Interval.Set.Infinite

/-!
# Elementary dynamics of finite-piece constant-slope interval maps

This standalone module contains the generic constant-slope facts shared by
the extremal and postcritical arguments: composition and iteration of slope
magnitudes, finite fibres and absence of flat intervals for positive slope,
and finiteness of fixed points for expanding slope.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set

/-! ## Affine branches and composition -/

/-- An affine branch has one of the two weak monotonicity orientations. -/
theorem IsAffineOn.isWeaklyMonotoneOn
    {T : IntervalMap} {s : Set I} (h : IsAffineOn T s) :
    IsWeaklyMonotoneOn T s := by
  rcases h with ⟨m, c, hformula⟩
  by_cases hm : 0 ≤ m
  · left
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mpr hxy) hm) c
  · right
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonpos_left (Subtype.coe_le_coe.mpr hxy)
        (le_of_not_ge hm)) c

/-- Positive constant absolute slopes multiply under composition. -/
theorem HasConstantAbsoluteSlope.comp_of_pos
    {U T : IntervalMap} {u t : ℝ} (_ht : 0 < t)
    (hU : HasConstantAbsoluteSlope U u)
    (hT : HasConstantAbsoluteSlope T t) :
    HasConstantAbsoluteSlope (U ∘ T) (u * t) := by
  rcases hU with ⟨hUcont, pU, hpU⟩
  rcases hT with ⟨hTcont, pT, hpT⟩
  let wU : MonotonicityPartition U :=
    ⟨pU, fun _ _ hab => by
      obtain ⟨m, c, _hm, hformula⟩ := hpU hab
      exact IsAffineOn.isWeaklyMonotoneOn ⟨m, c, hformula⟩⟩
  let wT : MonotonicityPartition T :=
    ⟨pT, fun _ _ hab => by
      obtain ⟨m, c, _hm, hformula⟩ := hpT hab
      exact IsAffineOn.isWeaklyMonotoneOn ⟨m, c, hformula⟩⟩
  refine ⟨hUcont.comp hTcont, wT.compositionRefinement wU, ?_⟩
  intro a b hab
  obtain ⟨aT, bT, hTadj, hsource⟩ :=
    (wT.compositionRefinement_refines wU).adjacent_subset hab
  obtain ⟨mT, cT, hmT, hTformula⟩ := hpT hTadj
  obtain ⟨_hTweak, aU, bU, hUadj, hmaps⟩ :=
    wT.composition_cell hTcont wU hab
  obtain ⟨mU, cU, hmU, hUformula⟩ := hpU hUadj
  refine ⟨mU * mT, mU * cT + cU, ?_, ?_⟩
  · rw [abs_mul, hmU, hmT]
  · intro x hx
    change (U (T x) : ℝ) = _
    rw [hUformula (T x) (hmaps hx), hTformula x (hsource hx)]
    ring

/-- The identity map has constant absolute slope one. -/
theorem hasConstantAbsoluteSlope_id :
    HasConstantAbsoluteSlope (id : IntervalMap) 1 := by
  refine ⟨continuous_id, RealPartition.trivial, ?_⟩
  intro a b _hab
  refine ⟨1, 0, by simp, ?_⟩
  intro x _hx
  simp

/-- Positive constant absolute slope is preserved by finite iteration, and
the slope magnitude is the corresponding natural power. -/
theorem HasConstantAbsoluteSlope.iterateMap
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (hs : 0 < s) (n : ℕ) :
    HasConstantAbsoluteSlope
      (CommutingIntervalSimplified.iterateMap T n) (s ^ n) := by
  induction n with
  | zero =>
      simpa [CommutingIntervalSimplified.iterateMap] using
        hasConstantAbsoluteSlope_id
  | succ n ih =>
      have hpow : 0 < s ^ n := pow_pos hs n
      have hcomp := HasConstantAbsoluteSlope.comp_of_pos hpow hT ih
      have hfun : CommutingIntervalSimplified.iterateMap T (n + 1) =
          T ∘ CommutingIntervalSimplified.iterateMap T n := by
        funext x
        exact Function.iterate_succ_apply' T n x
      rw [hfun]
      simpa [pow_succ, mul_comm] using hcomp

/-! ## Finite fibres and no flat intervals -/

/-- On every lap of a positive constant-slope presentation, a fibre has at
most one point. -/
private theorem fibre_inter_lap_subsingleton
    {T : IntervalMap} {s : ℝ} (hs : 0 < s) (p : RealPartition)
    (hp : ∀ {a b : ℝ}, p.Adjacent a b →
      ∃ m c : ℝ, |m| = s ∧
        ∀ x ∈ intervalCell a b,
          (T x : ℝ) = m * (x : ℝ) + c)
    (q : p.LapIndex) (y : I) :
    ({x : I | T x = y} ∩ q.closedCell).Subsingleton := by
  intro x hx z hz
  obtain ⟨m, c, hm, hformula⟩ := hp q.adjacent
  have hmne : m ≠ 0 := by
    intro hmzero
    subst m
    simp at hm
    linarith
  have hxreal := congrArg Subtype.val hx.1
  have hzreal := congrArg Subtype.val hz.1
  rw [hformula x hx.2] at hxreal
  rw [hformula z hz.2] at hzreal
  apply Subtype.ext
  have hmul : m * ((x : ℝ) - (z : ℝ)) = 0 := by
    linarith
  rcases mul_eq_zero.mp hmul with hmzero | hxz
  · exact (hmne hmzero).elim
  · exact sub_eq_zero.mp hxz

/-- Every fibre of a positive finite-piece constant-slope map is finite. -/
theorem HasConstantAbsoluteSlope.finite_fibre
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (hs : 0 < s) (y : I) :
    {x : I | T x = y}.Finite := by
  classical
  rcases hT with ⟨hcont, p, hp⟩
  have hpiece (q : p.LapIndex) :
      ({x : I | T x = y} ∩ q.closedCell).Finite :=
    (fibre_inter_lap_subsingleton hs p hp q y).finite
  have hunion :
      (⋃ q : p.LapIndex, ({x : I | T x = y} ∩ q.closedCell)).Finite :=
    Set.finite_iUnion hpiece
  apply hunion.subset
  intro x hx
  obtain ⟨a, b, hab, hxab⟩ := p.exists_adjacent_containing x
  have hpair : (a, b) ∈ p.adjacentPairs := by
    rw [RealPartition.adjacentPairs]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩
  let q : p.LapIndex := ⟨(a, b), hpair⟩
  apply Set.mem_iUnion.mpr
  refine ⟨q, hx, ?_⟩
  simpa [q, RealPartition.LapIndex.closedCell,
    RealPartition.LapIndex.left, RealPartition.LapIndex.right] using hxab

/-- A positive constant absolute slope map has no nondegenerate flat
interval. -/
theorem HasConstantAbsoluteSlope.noFlatInterval
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (hs : 0 < s) :
    ¬HasFlatInterval T := by
  rintro ⟨J, hJ, hflat⟩
  have hsubset : J.carrier ⊆ {x : I | T x = T J.left} := by
    intro x hx
    exact hflat hx J.left_mem_carrier
  have hfinite : J.carrier.Finite :=
    (hT.finite_fibre hs (T J.left)).subset hsubset
  exact (Set.Icc_infinite hJ) hfinite

/-- Every iterate of a positive constant-slope map is flat-free. -/
theorem HasConstantAbsoluteSlope.iterateMap_noFlatInterval
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (hs : 0 < s) (n : ℕ) :
    ¬HasFlatInterval (CommutingIntervalSimplified.iterateMap T n) :=
  (hT.iterateMap hs n).noFlatInterval (pow_pos hs n)

/-! ## Finite fixed sets in the expanding case -/

/-- On one affine lap whose slope magnitude is greater than one, the fixed
set has at most one point. -/
private theorem fixedPoints_inter_lap_subsingleton
    {T : IntervalMap} {s : ℝ} (hs : 1 < s) (p : RealPartition)
    (hp : ∀ {a b : ℝ}, p.Adjacent a b →
      ∃ m c : ℝ, |m| = s ∧
        ∀ x ∈ intervalCell a b,
          (T x : ℝ) = m * (x : ℝ) + c)
    (q : p.LapIndex) :
    (fixedPoints T ∩ q.closedCell).Subsingleton := by
  intro x hx y hy
  obtain ⟨m, c, hm, hformula⟩ := hp q.adjacent
  have hmne : m ≠ 1 := by
    intro hmone
    subst m
    simp at hm
    linarith
  have hxreal := congrArg Subtype.val hx.1
  have hyreal := congrArg Subtype.val hy.1
  rw [hformula x hx.2] at hxreal
  rw [hformula y hy.2] at hyreal
  apply Subtype.ext
  have hmul : (m - 1) * ((x : ℝ) - (y : ℝ)) = 0 := by
    linarith
  rcases mul_eq_zero.mp hmul with hmzero | hxy
  · exact (hmne (sub_eq_zero.mp hmzero)).elim
  · exact sub_eq_zero.mp hxy

/-- An expanding finite-piece constant-slope interval map has finitely many
fixed points. -/
theorem HasConstantAbsoluteSlope.fixedPoints_finite
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (hs : 1 < s) :
    (fixedPoints T).Finite := by
  classical
  rcases hT with ⟨hcont, p, hp⟩
  have hpiece (q : p.LapIndex) :
      (fixedPoints T ∩ q.closedCell).Finite :=
    (fixedPoints_inter_lap_subsingleton hs p hp q).finite
  have hunion :
      (⋃ q : p.LapIndex, (fixedPoints T ∩ q.closedCell)).Finite :=
    Set.finite_iUnion hpiece
  apply hunion.subset
  intro x hx
  obtain ⟨a, b, hab, hxab⟩ := p.exists_adjacent_containing x
  have hpair : (a, b) ∈ p.adjacentPairs := by
    rw [RealPartition.adjacentPairs]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩
  let q : p.LapIndex := ⟨(a, b), hpair⟩
  apply Set.mem_iUnion.mpr
  refine ⟨q, hx, ?_⟩
  simpa [q, RealPartition.LapIndex.closedCell,
    RealPartition.LapIndex.left, RealPartition.LapIndex.right] using hxab

/-- Every positive iterate of an expanding constant-slope map has a finite
fixed set. -/
theorem HasConstantAbsoluteSlope.iterateMap_fixedPoints_finite
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (hs : 1 < s) (n : ℕ) (hn : 0 < n) :
    (fixedPoints (CommutingIntervalSimplified.iterateMap T n)).Finite := by
  have hspos : 0 < s := zero_lt_one.trans hs
  exact (hT.iterateMap hspos n).fixedPoints_finite
    (one_lt_pow₀ hs (Nat.ne_of_gt hn))

end CommutingIntervalSimplified
