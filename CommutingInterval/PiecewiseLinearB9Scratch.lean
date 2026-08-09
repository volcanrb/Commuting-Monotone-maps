import CommutingInterval.PiecewiseLinearCore
import CommutingInterval.PiecewiseLinearB9GeometrySupport

/-!
# Exact directed-edge coding and two-scale comparison

The construction has three stages.

1. Rebuild a locally unit-speed ray *after* passing to the common
   constant-slope coordinate.  Its two dilation scales are explicitly
   identified with `M.scaleP ^ G.L` and `M.scaleQ ^ G.L`; no equality with
   the unrelated parameter scales stored in `E` is assumed.
2. Construct `CommonRayFixedWord` together with a complete decoder: every
   directed crossing made by every map iterate is present in the matching
   substitution power.  Endpoint-only `ModelsDirectedEdgeSubstitution` is
   retained, but is not mistaken for this stronger completeness statement.
3. Use exactness to obtain a uniform directed-edge crossing depth and hence
   primitive substitutions.  Primitive fixed points have linear factor gaps,
   reducing the remaining symbolic step to a primitive two-scale return-word
   comparison.

The return-system tower records exact decoders, simultaneous repetition,
deep common-seed powers, maximal factorizations, bounded boundary errors, and
the Perron specialization needed to force equality of positive powers of the
two metric scales.
-/

namespace CommutingInterval

open Function Set

noncomputable section

namespace PiecewiseLinearB9Scratch

/-! ## Returned scales and the rebuilt ray -/

/-- The positive selected-side affine germs used to rebuild the metric ray.
The formulas are based at the transformed selected point, and the displayed
slopes are the returned constant slopes rather than the earlier ray
parameters in `E`. -/
structure PositiveReturnedGermData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) where
  rightEnd : I
  base_lt_rightEnd : M.coordinate G.p < rightEnd
  formula_A : ∀ x : I, x ∈ Set.Icc (M.coordinate G.p) rightEnd →
    (M.A x : Real) - (M.coordinate G.p : Real) =
      (M.scaleP ^ G.L) * ((x : Real) - (M.coordinate G.p : Real))
  formula_B : ∀ x : I, x ∈ Set.Icc (M.coordinate G.p) rightEnd →
    (M.B x : Real) - (M.coordinate G.p : Real) =
      (M.scaleQ ^ G.L) * ((x : Real) - (M.coordinate G.p : Real))
  formula_R : ∀ x : I, x ∈ Set.Icc (M.coordinate G.p) rightEnd →
    (M.R x : Real) - (M.coordinate G.p : Real) =
      ((M.scaleP ^ G.L) * (M.scaleQ ^ G.L)) *
        ((x : Real) - (M.coordinate G.p : Real))

/-- The metric ray rebuilt from the positive returned germ.  The explicit
scale equalities are the missing adapter between the geometric construction
and the Perron-growth statements. -/
structure RebuiltReturnedRayData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) where
  ray : Real → I
  scaleA : Real
  scaleB : Real
  scaleA_eq : scaleA = M.scaleP ^ G.L
  scaleB_eq : scaleB = M.scaleQ ^ G.L
  scaleA_gt_one : 1 < scaleA
  scaleB_gt_one : 1 < scaleB
  scales_independent : MultiplicativelyIndependent scaleA scaleB
  initialRadius : Real
  initialRadius_pos : 0 < initialRadius
  initial_segment : ∀ t : Real, 0 ≤ t → t ≤ initialRadius →
    (ray t : Real) = (M.coordinate G.p : Real) + t
  locally_unitSpeed : IsLocallyUnitSpeedRay ray
  onto_nonnegative : IsOntoNonnegativeRay ray
  return_A : DilationReturnsOnRay ray scaleA M.A
  return_B : DilationReturnsOnRay ray scaleB M.B

/-- The first positively oriented Markov edge traversed by the rebuilt ray.
Keeping this separate makes the finite-set selection independent of the
ray-globalization proof. -/
structure RebuiltRaySeedData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    (K : PiecewiseLinearCommonMarkovPackage M)
    (rayData : RebuiltReturnedRayData M) where
  edge : DirectedMarkovEdge K.K
  edge_forward : edge.forward = true
  edge_source : edge.source = M.coordinate G.p
  initial_traversal : TraversesDirectedEdge rayData.ray 0 edge

/-- Leaf G1: expose the common positive returned germ of `A`, `B`, and
`R = A o B`. -/
theorem exists_positiveReturnedGermData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E) :
    Nonempty (PositiveReturnedGermData M) := by
  let HasPositiveAffineRightFormula :=
    fun (T : IntervalMap) (p : I) (scale : ℝ) ↦
      ∃ q : I, p < q ∧ ∀ x ∈ Set.Icc p q,
        (T x : ℝ) = (p : ℝ) + scale * ((x : ℝ) - (p : ℝ))
  have positiveFormula_of_constantSlope :
      ∀ {T : IntervalMap} {p : I} {scale : ℝ},
        p < rightEndpoint → T p = p →
        HasConstantAbsoluteSlopePLCore T scale →
        (∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q)) →
        HasPositiveAffineRightFormula T p scale := by
    intro T p scale hpRight hfixed hslope hstrict
    rcases hslope with ⟨_hcont, partition, hpartition⟩
    obtain ⟨a, b, hab, hap, hpb⟩ :=
      partition.exists_adjacent_Ico hpRight
    rcases hstrict with ⟨q₀, hpq₀, hstrict⟩
    obtain ⟨qReal, hpqReal, hqReal⟩ :=
      exists_between (lt_min hpb hpq₀)
    have hqb : qReal < b := hqReal.trans_le (min_le_left _ _)
    have hqq₀Real : qReal < (q₀ : ℝ) :=
      hqReal.trans_le (min_le_right _ _)
    let q : I := ⟨qReal, ⟨p.property.1.trans hpqReal.le,
      hqq₀Real.le.trans q₀.property.2⟩⟩
    have hpq : p < q := hpqReal
    have hqq₀ : q < q₀ := hqq₀Real
    obtain ⟨m, c, hmabs, hformula⟩ := hpartition hab
    have hpCell : p ∈ intervalCell a b := ⟨hap, hpb.le⟩
    have hqCell : q ∈ intervalCell a b :=
      ⟨hap.trans hpq.le, hqb.le⟩
    have hpStrict : p ∈ Set.Icc p q₀ := ⟨le_rfl, hpq₀.le⟩
    have hqStrict : q ∈ Set.Icc p q₀ := ⟨hpq.le, hqq₀.le⟩
    have hTpTq : T p < T q := hstrict hpStrict hqStrict hpq
    have hformulaP := hformula p hpCell
    have hformulaQ := hformula q hqCell
    have hmpos : 0 < m := by
      have hreal : (T p : ℝ) < (T q : ℝ) := hTpTq
      rw [hformulaP, hformulaQ] at hreal
      nlinarith
    have hms : m = scale := by
      rw [abs_of_pos hmpos] at hmabs
      exact hmabs
    refine ⟨q, hpq, ?_⟩
    intro x hx
    have hxCell : x ∈ intervalCell a b := by
      exact ⟨hap.trans hx.1,
        (show (x : ℝ) ≤ (q : ℝ) from hx.2).trans hqb.le⟩
    have hxformula := hformula x hxCell
    have hfixedReal : (T p : ℝ) = (p : ℝ) :=
      congrArg Subtype.val hfixed
    rw [hms] at hformulaP hxformula
    rw [hfixedReal] at hformulaP
    nlinarith
  have positiveFormula_comp :
      ∀ {A B : IntervalMap} {p : I} {a b : ℝ},
        1 < b →
        HasPositiveAffineRightFormula A p a →
        HasPositiveAffineRightFormula B p b →
        HasPositiveAffineRightFormula (A ∘ B) p (a * b) := by
    intro A B p a b hb hA hB
    rcases hA with ⟨qA, hpA, hA⟩
    rcases hB with ⟨qB, hpB, hB⟩
    have hbpos : 0 < b := lt_trans (by norm_num) hb
    let bound : ℝ := (p : ℝ) + ((qA : ℝ) - (p : ℝ)) / b
    have hpbound : (p : ℝ) < bound := by
      dsimp [bound]
      exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr hpA) hbpos)
    obtain ⟨qReal, hpqReal, hqReal⟩ :=
      exists_between (lt_min (show (p : ℝ) < (qB : ℝ) from hpB)
        hpbound)
    have hqBReal : qReal < (qB : ℝ) :=
      hqReal.trans_le (min_le_left _ _)
    have hqBound : qReal < bound :=
      hqReal.trans_le (min_le_right _ _)
    have hbound_le_one : bound ≤ 1 := by
      dsimp [bound]
      have hdiv_le : ((qA : ℝ) - (p : ℝ)) / b ≤
          (qA : ℝ) - (p : ℝ) :=
        div_le_self (sub_nonneg.mpr hpA.le) hb.le
      linarith [qA.property.2]
    let q : I := ⟨qReal, ⟨p.property.1.trans hpqReal.le,
      hqBound.le.trans hbound_le_one⟩⟩
    refine ⟨q, hpqReal, ?_⟩
    intro x hx
    have hxB : x ∈ Set.Icc p qB :=
      ⟨hx.1, hx.2.trans hqBReal.le⟩
    have hBx := hB x hxB
    have hBxA : B x ∈ Set.Icc p qA := by
      constructor
      · change (p : ℝ) ≤ (B x : ℝ)
        rw [hBx]
        exact le_add_of_nonneg_right
          (mul_nonneg hbpos.le (sub_nonneg.mpr hx.1))
      · change (B x : ℝ) ≤ (qA : ℝ)
        rw [hBx]
        have hxq : (x : ℝ) ≤ qReal := hx.2
        dsimp [bound] at hqBound
        have hcross : b * (qReal - (p : ℝ)) <
            (qA : ℝ) - (p : ℝ) := by
          have := (lt_div_iff₀ hbpos).1 (by linarith :
            qReal - (p : ℝ) < ((qA : ℝ) - (p : ℝ)) / b)
          nlinarith
        nlinarith
    change (A (B x) : ℝ) = _
    rw [hA (B x) hBxA, hBx]
    ring
  have hLpos : 0 < G.L := piecewiseLinear_returnedLength_pos G
  have hscaleP0 : 0 < M.scaleP := lt_trans (by norm_num) M.one_lt_scaleP
  have hscaleQ0 : 0 < M.scaleQ := lt_trans (by norm_num) M.one_lt_scaleQ
  have hAslope :
      HasConstantAbsoluteSlopePLCore M.A (M.scaleP ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.A] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleP0 M.slopeP G.L
  have hBslope :
      HasConstantAbsoluteSlopePLCore M.B (M.scaleQ ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.B] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleQ0 M.slopeQ G.L
  have hconjA : ConjugatesPLCore M.coordinate G.A M.A := by
    simpa [PiecewiseLinearSelectedFixedGap.A,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.A,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.A,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearA, PiecewiseLinearConstantSlopeSystem.A] using
      conjugatesPLCore_iterate M.conjugatesP G.L
  have hconjB : ConjugatesPLCore M.coordinate G.B M.B := by
    simpa [PiecewiseLinearSelectedFixedGap.B,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.B,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.B,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearB, PiecewiseLinearConstantSlopeSystem.B] using
      conjugatesPLCore_iterate M.conjugatesQ G.L
  have hAp : M.A (M.coordinate G.p) = M.coordinate G.p := by
    calc
      M.A (M.coordinate G.p) = M.coordinate (G.A G.p) :=
        (hconjA G.p).symm
      _ = M.coordinate G.p :=
        congrArg M.coordinate (piecewiseLinear_return_fixes_A_p G)
  have hBp : M.B (M.coordinate G.p) = M.coordinate G.p := by
    calc
      M.B (M.coordinate G.p) = M.coordinate (G.B G.p) :=
        (hconjB G.p).symm
      _ = M.coordinate G.p :=
        congrArg M.coordinate (piecewiseLinear_return_fixes_B_p G)
  have hpRight : M.coordinate G.p < rightEndpoint :=
    (M.coordinate_strictMono G.p_lt_c).trans_le
      (M.coordinate G.c).property.2
  have hAstrictSource : ∃ q : I, G.p < q ∧
      StrictMonoOn G.A (Set.Icc G.p q) :=
    piecewiseLinear_rightGermC1BV_strictMono
      (piecewiseLinear_A_hasRightGermC1BV G)
  have hBstrictSource : ∃ q : I, G.p < q ∧
      StrictMonoOn G.B (Set.Icc G.p q) :=
    piecewiseLinear_rightGermC1BV_strictMono
      (piecewiseLinear_B_hasRightGermC1BV G)
  have hAstrict :=
    piecewiseLinear_strictMonoNearBase_of_increasingConjugacy
      M.coordinate_strictMono hconjA hAstrictSource
  have hBstrict :=
    piecewiseLinear_strictMonoNearBase_of_increasingConjugacy
      M.coordinate_strictMono hconjB hBstrictSource
  have hAgerm : HasPositiveAffineRightFormula M.A
      (M.coordinate G.p) (M.scaleP ^ G.L) :=
    positiveFormula_of_constantSlope hpRight hAp hAslope hAstrict
  have hBgerm : HasPositiveAffineRightFormula M.B
      (M.coordinate G.p) (M.scaleQ ^ G.L) :=
    positiveFormula_of_constantSlope hpRight hBp hBslope hBstrict
  have hscaleB : 1 < M.scaleQ ^ G.L :=
    one_lt_pow₀ M.one_lt_scaleQ hLpos.ne'
  have hRgerm : HasPositiveAffineRightFormula M.R
      (M.coordinate G.p)
      ((M.scaleP ^ G.L) * (M.scaleQ ^ G.L)) := by
    simpa [PiecewiseLinearConstantSlopeSystem.R] using
      positiveFormula_comp hscaleB hAgerm hBgerm
  rcases hAgerm with ⟨qA, hpA, hA⟩
  rcases hBgerm with ⟨qB, hpB, hB⟩
  rcases hRgerm with ⟨qR, hpR, hR⟩
  let rightEnd : I := min qA (min qB qR)
  have hpEnd : M.coordinate G.p < rightEnd :=
    lt_min hpA (lt_min hpB hpR)
  refine ⟨{
    rightEnd := rightEnd
    base_lt_rightEnd := hpEnd
    formula_A := ?_
    formula_B := ?_
    formula_R := ?_ }⟩
  · intro x hx
    have hformula := hA x ⟨hx.1, hx.2.trans (min_le_left _ _)⟩
    linarith
  · intro x hx
    have hformula := hB x ⟨hx.1,
      hx.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    linarith
  · intro x hx
    have hformula := hR x ⟨hx.1,
      hx.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    linarith

/-- Leaf G2: stabilize the selected-germ formula on compact parameter
intervals to obtain the onto locally unit-speed ray. -/
theorem rebuild_returned_unitSpeedRay
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E)
    (_germ : PositiveReturnedGermData M) :
    Nonempty (RebuiltReturnedRayData M) := by
  have hLpos : 0 < G.L := piecewiseLinear_returnedLength_pos G
  have hscaleP0 : 0 < M.scaleP := lt_trans (by norm_num) M.one_lt_scaleP
  have hscaleQ0 : 0 < M.scaleQ := lt_trans (by norm_num) M.one_lt_scaleQ
  have hAslopePL :
      HasConstantAbsoluteSlopePLCore M.A (M.scaleP ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.A] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleP0 M.slopeP G.L
  have hBslopePL :
      HasConstantAbsoluteSlopePLCore M.B (M.scaleQ ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.B] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleQ0 M.slopeQ G.L
  have hAslope : HasConstantAbsoluteSlope M.A (M.scaleP ^ G.L) := by
    simpa [HasConstantAbsoluteSlopePLCore, HasConstantAbsoluteSlope] using
      hAslopePL
  have hBslope : HasConstantAbsoluteSlope M.B (M.scaleQ ^ G.L) := by
    simpa [HasConstantAbsoluteSlopePLCore, HasConstantAbsoluteSlope] using
      hBslopePL
  have hconjA : ConjugatesPLCore M.coordinate G.A M.A := by
    simpa [PiecewiseLinearSelectedFixedGap.A,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.A,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.A,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearA, PiecewiseLinearConstantSlopeSystem.A] using
      conjugatesPLCore_iterate M.conjugatesP G.L
  have hconjB : ConjugatesPLCore M.coordinate G.B M.B := by
    simpa [PiecewiseLinearSelectedFixedGap.B,
      PiecewiseLinearSelectedFixedGap.L,
      LeastNormalizedPiecewiseLinearCounterexample.B,
      LeastNormalizedPiecewiseLinearCounterexample.L,
      NormalizedPiecewiseLinearCounterexample.B,
      NormalizedPiecewiseLinearCounterexample.L,
      piecewiseLinearB, PiecewiseLinearConstantSlopeSystem.B] using
      conjugatesPLCore_iterate M.conjugatesQ G.L
  have hAp : IsFixedPoint M.A (M.coordinate G.p) := by
    calc
      M.A (M.coordinate G.p) = M.coordinate (G.A G.p) :=
        (hconjA G.p).symm
      _ = M.coordinate G.p :=
        congrArg M.coordinate (piecewiseLinear_return_fixes_A_p G)
  have hBp : IsFixedPoint M.B (M.coordinate G.p) := by
    calc
      M.B (M.coordinate G.p) = M.coordinate (G.B G.p) :=
        (hconjB G.p).symm
      _ = M.coordinate G.p :=
        congrArg M.coordinate (piecewiseLinear_return_fixes_B_p G)
  have hpRight : M.coordinate G.p < rightEndpoint :=
    (M.coordinate_strictMono G.p_lt_c).trans_le
      (M.coordinate G.c).property.2
  have hAstrictSource : ∃ q : I, G.p < q ∧
      StrictMonoOn G.A (Set.Icc G.p q) :=
    piecewiseLinear_rightGermC1BV_strictMono
      (piecewiseLinear_A_hasRightGermC1BV G)
  have hBstrictSource : ∃ q : I, G.p < q ∧
      StrictMonoOn G.B (Set.Icc G.p q) :=
    piecewiseLinear_rightGermC1BV_strictMono
      (piecewiseLinear_B_hasRightGermC1BV G)
  have hAstrict :=
    piecewiseLinear_strictMonoNearBase_of_increasingConjugacy
      M.coordinate_strictMono hconjA hAstrictSource
  have hBstrict :=
    piecewiseLinear_strictMonoNearBase_of_increasingConjugacy
      M.coordinate_strictMono hconjB hBstrictSource
  have hcomm : Commute M.A M.B := by
    intro x
    simpa [PiecewiseLinearConstantSlopeSystem.A,
      PiecewiseLinearConstantSlopeSystem.B] using
      M.commute.iterate_iterate G.L G.L x
  have hscaleA : 1 < M.scaleP ^ G.L :=
    one_lt_pow₀ M.one_lt_scaleP hLpos.ne'
  have hscaleB : 1 < M.scaleQ ^ G.L :=
    one_lt_pow₀ M.one_lt_scaleQ hLpos.ne'
  obtain ⟨ray⟩ := rebuildPolygonal_unitSpeedRay hpRight hcomm
    (show M.R = M.A ∘ M.B from rfl) hAp hBp M.exact_R
    hAslope hBslope hAstrict hBstrict hscaleA hscaleB
  rcases ray.initial_linear with ⟨initialRadius, hinitialRadius,
    hinitial⟩
  exact ⟨{
    ray := ray.ray
    scaleA := M.scaleP ^ G.L
    scaleB := M.scaleQ ^ G.L
    scaleA_eq := rfl
    scaleB_eq := rfl
    scaleA_gt_one := hscaleA
    scaleB_gt_one := hscaleB
    scales_independent := M.returned_scales_independent
    initialRadius := initialRadius
    initialRadius_pos := hinitialRadius
    initial_segment := hinitial
    locally_unitSpeed := ray.ray_unitSpeed
    onto_nonnegative := ray.ray_onto
    return_A := ray.returnA
    return_B := ray.returnB }⟩

/-- Leaf G3: choose the least Markov vertex to the right of the transformed
base and identify the initial literal traversal. -/
theorem rebuiltRay_has_positiveMarkovSeed
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    (K : PiecewiseLinearCommonMarkovPackage M)
    (rayData : RebuiltReturnedRayData M) :
    Nonempty (RebuiltRaySeedData K rayData) := by
  have hpRight : M.coordinate G.p < rightEndpoint :=
    (M.coordinate_strictMono G.p_lt_c).trans_le
      (M.coordinate G.c).property.2
  have hmarkov : IsCommonMarkovSet M.A M.B K.K := by
    simpa [IsCommonMarkovSet, IsPiecewiseLinearCommonMarkovSet,
      FinsetAdjacent, PiecewiseLinearFinsetAdjacent] using K.markov
  let genericRay : PolygonalUnitSpeedRayData M.A M.B M.R
      (M.coordinate G.p) rayData.scaleA rayData.scaleB := {
    ray := rayData.ray
    ray_unitSpeed := rayData.locally_unitSpeed
    ray_onto := rayData.onto_nonnegative
    returnA := rayData.return_A
    returnB := rayData.return_B
    initial_linear := ⟨rayData.initialRadius, rayData.initialRadius_pos,
      rayData.initial_segment⟩ }
  obtain ⟨edge, hedgeForward, hedgeSource, htraversal⟩ :=
    bridge_initialMarkovEdge_traversed genericRay K.base_mem hpRight
      hmarkov rayData.scaleA_gt_one
  exact ⟨{
    edge := edge
    edge_forward := hedgeForward
    edge_source := hedgeSource
    initial_traversal := htraversal }⟩

/-- Proved aggregator for the three geometric construction stages. -/
theorem exists_rebuiltRay_and_seed
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    (M : PiecewiseLinearConstantSlopeSystem E)
    (K : PiecewiseLinearCommonMarkovPackage M) :
    ∃ rayData : RebuiltReturnedRayData M,
      Nonempty (RebuiltRaySeedData K rayData) := by
  obtain ⟨germ⟩ := exists_positiveReturnedGermData M
  obtain ⟨rayData⟩ := rebuild_returned_unitSpeedRay M germ
  exact ⟨rayData, rebuiltRay_has_positiveMarkovSeed K rayData⟩

/-! ## Complete directed-edge decoding -/

/-- Two points occur in the strict interior of a source edge in its
displayed orientation. -/
def InDirectedInteriorOrder {K : Finset I}
    (edge : DirectedMarkovEdge K) (x y : I) : Prop :=
  x ∈ Set.Ioo edge.lower edge.upper ∧
    y ∈ Set.Ioo edge.lower edge.upper ∧
      match edge.forward with
      | true => x < y
      | false => y < x

/-- An oriented target edge is crossed inside an oriented source edge.
Only endpoint values are needed for the exactness-to-primitivity argument. -/
def HasDirectedEdgeCrossing {K : Finset I}
    (T : IntervalMap) (sourceEdge targetEdge : DirectedMarkovEdge K) : Prop :=
  ∃ x y : I,
    InDirectedInteriorOrder sourceEdge x y ∧
      T x = targetEdge.source ∧ T y = targetEdge.target

/-- Completeness of the literal decoder at every substitution power.  This
is strictly stronger than `ModelsDirectedEdgeSubstitution`, whose current
definition records only a path and its two outer endpoints. -/
def RecordsAllIteratedDirectedCrossings {K : Finset I}
    (T : IntervalMap) (alphabet : OccurringDirectedAlphabet K)
    (sigma : Symbolic.Substitution alphabet) : Prop :=
  ∀ n : Nat, ∀ sourceEdge targetEdge : alphabet,
    HasDirectedEdgeCrossing (iterateMap T n) sourceEdge.1 targetEdge.1 →
      targetEdge ∈ sigma.iterateLetter n sourceEdge

/-- Completeness at the first literal edge image.  This is the local
geometric statement proved directly from the canonical monotonicity-cell
word before any substitution iteration or alphabet restriction. -/
def RecordsOneStepDirectedCrossings {K : Finset I}
    (T : IntervalMap) (alphabet : OccurringDirectedAlphabet K)
    (sigma : Symbolic.Substitution alphabet) : Prop :=
  ∀ sourceEdge targetEdge : alphabet,
    HasDirectedEdgeCrossing T sourceEdge.1 targetEdge.1 →
      targetEdge ∈ sigma sourceEdge

/-- The canonical construction before unused directed letters are removed.
Unlike `CommonRayFixedWord`, this full-alphabet package does not assert that
every ambient directed edge occurs. -/
structure FullAlphabetRayCodingData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    (K : PiecewiseLinearCommonMarkovPackage M)
    (rayData : RebuiltReturnedRayData M)
    (seedData : RebuiltRaySeedData K rayData) where
  alphabet : OccurringDirectedAlphabet K.K
  alphabet_full : alphabet = Finset.univ
  substitutionA : Symbolic.Substitution alphabet
  substitutionB : Symbolic.Substitution alphabet
  seed : alphabet
  seed_eq : seed.1 = seedData.edge
  word : Symbolic.InfiniteWord alphabet
  fixed_A : substitutionA.IsFixedPoint word
  fixed_B : substitutionB.IsFixedPoint word
  prolongable_A : substitutionA.ProlongableOn seed
  prolongable_B : substitutionB.ProlongableOn seed
  models_A : ModelsDirectedEdgeSubstitution M.A alphabet substitutionA
  models_B : ModelsDirectedEdgeSubstitution M.B alphabet substitutionB
  itinerary : HasLiteralUnitSpeedItinerary rayData.ray
    (occurringEdge alphabet) (fun edge => edge.1.length) word
  prefix_A : ∀ n : Nat,
    substitutionA.iterateLetter n seed =
      word.take (substitutionA.iterateLetter n seed).length
  prefix_B : ∀ n : Nat,
    substitutionB.iterateLetter n seed =
      word.take (substitutionB.iterateLetter n seed).length
  imageMetric_A : SubstitutionScalesLetterLengths substitutionA
    (fun edge => edge.1.length) rayData.scaleA
  imageMetric_B : SubstitutionScalesLetterLengths substitutionB
    (fun edge => edge.1.length) rayData.scaleB

private theorem substitution_iterateLetter_map_of_intertwining_b9
    {α β : Type*} (coding : α → β)
    (source : Symbolic.Substitution α) (target : Symbolic.Substitution β)
    (himage : ∀ a, (source a).map coding = target (coding a))
    (n : Nat) (a : α) :
    (source.iterateLetter n a).map coding =
      target.iterateLetter n (coding a) := by
  have hmapWord (w : Symbolic.Word α) :
      (source.mapWord w).map coding =
        target.mapWord (w.map coding) := by
    induction w with
    | nil => simp
    | cons z w ih =>
        calc
          (source.mapWord (z :: w)).map coding =
              ((source z) ++ source.mapWord w).map coding := rfl
          _ = target (coding z) ++ target.mapWord (w.map coding) := by
            rw [List.map_append, himage, ih]
          _ = target.mapWord (coding z :: w.map coding) :=
            (Symbolic.Substitution.mapWord_cons target (coding z)
              (w.map coding)).symm
          _ = target.mapWord ((z :: w).map coding) := rfl
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Symbolic.Substitution.iterateLetter_succ,
        Symbolic.Substitution.iterateLetter_succ, hmapWord, ih]

/-- Support gate for D0: embed the public occurring-alphabet common word in
the full directed alphabet, using full geometric substitutions only on the
letters absent from the word. -/
private theorem commonRayFixedWord_extendToFullAlphabet
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (common : CommonRayFixedWord M.A M.B K.K rayData.ray
      rayData.scaleA rayData.scaleB)
    (common_seed : common.seed.1 = seedData.edge)
    (fullA : FullDirectedMarkovSubstitution M.A K.K rayData.scaleA)
    (fullB : FullDirectedMarkovSubstitution M.B K.K rayData.scaleB) :
    Nonempty (FullAlphabetRayCodingData K rayData seedData) := by
  classical
  let alphabet : OccurringDirectedAlphabet K.K := Finset.univ
  let liftEdge : DirectedMarkovEdge K.K → alphabet :=
    fun edge => ⟨edge, Finset.mem_univ edge⟩
  let liftCommon : common.alphabet → alphabet :=
    fun edge => liftEdge edge.1
  let imageA : alphabet → Symbolic.Word alphabet := fun edge =>
    if hedge : edge.1 ∈ common.alphabet then
      (common.substitutionA ⟨edge.1, hedge⟩).map liftCommon
    else
      (fullA.substitution edge.1).map liftEdge
  let imageB : alphabet → Symbolic.Word alphabet := fun edge =>
    if hedge : edge.1 ∈ common.alphabet then
      (common.substitutionB ⟨edge.1, hedge⟩).map liftCommon
    else
      (fullB.substitution edge.1).map liftEdge
  let substitutionA : Symbolic.Substitution alphabet := {
    image := imageA
    image_ne_nil := by
      intro edge
      dsimp [imageA]
      split
      next hedge =>
        apply List.ne_nil_of_length_pos
        simpa using List.length_pos_of_ne_nil
          (common.substitutionA.image_ne_nil ⟨edge.1, hedge⟩)
      next hedge =>
        apply List.ne_nil_of_length_pos
        simpa using List.length_pos_of_ne_nil
          (fullA.substitution.image_ne_nil edge.1) }
  let substitutionB : Symbolic.Substitution alphabet := {
    image := imageB
    image_ne_nil := by
      intro edge
      dsimp [imageB]
      split
      next hedge =>
        apply List.ne_nil_of_length_pos
        simpa using List.length_pos_of_ne_nil
          (common.substitutionB.image_ne_nil ⟨edge.1, hedge⟩)
      next hedge =>
        apply List.ne_nil_of_length_pos
        simpa using List.length_pos_of_ne_nil
          (fullB.substitution.image_ne_nil edge.1) }
  let seed : alphabet := liftCommon common.seed
  let coding : Symbolic.LetterCoding common.alphabet alphabet :=
    ⟨liftCommon⟩
  let word : Symbolic.InfiniteWord alphabet :=
    coding.mapInfinite common.word
  have himageA (edge : common.alphabet) :
      substitutionA (liftCommon edge) =
        (common.substitutionA edge).map liftCommon := by
    simp only [substitutionA, imageA]
    split
    next hedge =>
      congr 1
    next hedge =>
      exact False.elim (hedge edge.2)
  have himageB (edge : common.alphabet) :
      substitutionB (liftCommon edge) =
        (common.substitutionB edge).map liftCommon := by
    simp only [substitutionB, imageB]
    split
    next hedge =>
      congr 1
    next hedge =>
      exact False.elim (hedge edge.2)
  have hfixedA : substitutionA.IsFixedPoint word := by
    have hnatural := Symbolic.LetterCoding.mapInfinite_substitution coding
      common.substitutionA substitutionA (fun edge => by
        simpa [coding, Symbolic.LetterCoding.mapWord] using
          (himageA edge).symm) common.word
    rw [common.fixedA] at hnatural
    exact hnatural.symm
  have hfixedB : substitutionB.IsFixedPoint word := by
    have hnatural := Symbolic.LetterCoding.mapInfinite_substitution coding
      common.substitutionB substitutionB (fun edge => by
        simpa [coding, Symbolic.LetterCoding.mapWord] using
          (himageB edge).symm) common.word
    rw [common.fixedB] at hnatural
    exact hnatural.symm
  have hprolongableA : substitutionA.ProlongableOn seed := by
    rcases common.prolongableA with ⟨tail, htail, hcommonImage⟩
    refine ⟨tail.map liftCommon, ?_, ?_⟩
    · apply List.ne_nil_of_length_pos
      simpa using List.length_pos_of_ne_nil htail
    · rw [show seed = liftCommon common.seed from rfl, himageA,
        hcommonImage]
      rfl
  have hprolongableB : substitutionB.ProlongableOn seed := by
    rcases common.prolongableB with ⟨tail, htail, hcommonImage⟩
    refine ⟨tail.map liftCommon, ?_, ?_⟩
    · apply List.ne_nil_of_length_pos
      simpa using List.length_pos_of_ne_nil htail
    · rw [show seed = liftCommon common.seed from rfl, himageB,
        hcommonImage]
      rfl
  have hmodelsA :
      ModelsDirectedEdgeSubstitution M.A alphabet substitutionA := by
    intro edge
    by_cases hedge : edge.1 ∈ common.alphabet
    · let commonEdge : common.alphabet := ⟨edge.1, hedge⟩
      have hvalues :
          geometricEdgeWord alphabet (substitutionA edge) =
            geometricEdgeWord common.alphabet
              (common.substitutionA commonEdge) := by
        simp [geometricEdgeWord, occurringEdge, substitutionA, imageA,
          hedge, commonEdge, liftCommon, liftEdge]
      rw [hvalues]
      simpa [commonEdge] using common.modelsA commonEdge
    · have hvalues :
          geometricEdgeWord alphabet (substitutionA edge) =
            fullA.substitution edge.1 := by
        simp only [geometricEdgeWord, substitutionA, imageA, dif_neg hedge,
          List.map_map]
        induction fullA.substitution edge.1 with
        | nil => rfl
        | cons first rest ih =>
            simp [occurringEdge, liftEdge, ih]
      rw [hvalues]
      exact ⟨fullA.path edge.1, fullA.starts edge.1, fullA.ends edge.1⟩
  have hmodelsB :
      ModelsDirectedEdgeSubstitution M.B alphabet substitutionB := by
    intro edge
    by_cases hedge : edge.1 ∈ common.alphabet
    · let commonEdge : common.alphabet := ⟨edge.1, hedge⟩
      have hvalues :
          geometricEdgeWord alphabet (substitutionB edge) =
            geometricEdgeWord common.alphabet
              (common.substitutionB commonEdge) := by
        simp [geometricEdgeWord, occurringEdge, substitutionB, imageB,
          hedge, commonEdge, liftCommon, liftEdge]
      rw [hvalues]
      simpa [commonEdge] using common.modelsB commonEdge
    · have hvalues :
          geometricEdgeWord alphabet (substitutionB edge) =
            fullB.substitution edge.1 := by
        simp only [geometricEdgeWord, substitutionB, imageB, dif_neg hedge,
          List.map_map]
        induction fullB.substitution edge.1 with
        | nil => rfl
        | cons first rest ih =>
            simp [occurringEdge, liftEdge, ih]
      rw [hvalues]
      exact ⟨fullB.path edge.1, fullB.starts edge.1, fullB.ends edge.1⟩
  have hmetricA : SubstitutionScalesLetterLengths substitutionA
      (fun edge : alphabet => edge.1.length) rayData.scaleA := by
    intro edge
    by_cases hedge : edge.1 ∈ common.alphabet
    · let commonEdge : common.alphabet := ⟨edge.1, hedge⟩
      rw [show substitutionA edge =
          (common.substitutionA commonEdge).map liftCommon by
        simp [substitutionA, imageA, hedge, commonEdge]]
      have hmetricMap :
          wordMetricLength (fun z : alphabet => z.1.length)
              ((common.substitutionA commonEdge).map liftCommon) =
            wordMetricLength (fun z : common.alphabet => z.1.length)
              (common.substitutionA commonEdge) := by
        simp [wordMetricLength, List.map_map, liftCommon, liftEdge,
          Function.comp_def]
      rw [hmetricMap]
      have hlengthFun :
          (fun z : common.alphabet => z.1.length) = common.letterLength := by
        funext z
        exact (common.letterLength_eq z).symm
      rw [hlengthFun]
      calc
        wordMetricLength common.letterLength
            (common.substitutionA commonEdge) =
            rayData.scaleA * common.letterLength commonEdge :=
          common.imageMetricA commonEdge
        _ = rayData.scaleA * edge.1.length := by
          rw [common.letterLength_eq]
    · rw [show substitutionA edge =
          (fullA.substitution edge.1).map liftEdge by
        simp [substitutionA, imageA, hedge]]
      have hmetricMap :
          wordMetricLength (fun z : alphabet => z.1.length)
              ((fullA.substitution edge.1).map liftEdge) =
            wordMetricLength DirectedMarkovEdge.length
              (fullA.substitution edge.1) := by
        simp [wordMetricLength, List.map_map, liftEdge, Function.comp_def]
      rw [hmetricMap]
      exact fullA.metric edge.1
  have hmetricB : SubstitutionScalesLetterLengths substitutionB
      (fun edge : alphabet => edge.1.length) rayData.scaleB := by
    intro edge
    by_cases hedge : edge.1 ∈ common.alphabet
    · let commonEdge : common.alphabet := ⟨edge.1, hedge⟩
      rw [show substitutionB edge =
          (common.substitutionB commonEdge).map liftCommon by
        simp [substitutionB, imageB, hedge, commonEdge]]
      have hmetricMap :
          wordMetricLength (fun z : alphabet => z.1.length)
              ((common.substitutionB commonEdge).map liftCommon) =
            wordMetricLength (fun z : common.alphabet => z.1.length)
              (common.substitutionB commonEdge) := by
        simp [wordMetricLength, List.map_map, liftCommon, liftEdge,
          Function.comp_def]
      rw [hmetricMap]
      have hlengthFun :
          (fun z : common.alphabet => z.1.length) = common.letterLength := by
        funext z
        exact (common.letterLength_eq z).symm
      rw [hlengthFun]
      calc
        wordMetricLength common.letterLength
            (common.substitutionB commonEdge) =
            rayData.scaleB * common.letterLength commonEdge :=
          common.imageMetricB commonEdge
        _ = rayData.scaleB * edge.1.length := by
          rw [common.letterLength_eq]
    · rw [show substitutionB edge =
          (fullB.substitution edge.1).map liftEdge by
        simp [substitutionB, imageB, hedge]]
      have hmetricMap :
          wordMetricLength (fun z : alphabet => z.1.length)
              ((fullB.substitution edge.1).map liftEdge) =
            wordMetricLength DirectedMarkovEdge.length
              (fullB.substitution edge.1) := by
        simp [wordMetricLength, List.map_map, liftEdge, Function.comp_def]
      rw [hmetricMap]
      exact fullB.metric edge.1
  have hitinerary : HasLiteralUnitSpeedItinerary rayData.ray
      (occurringEdge alphabet) (fun edge : alphabet => edge.1.length) word := by
    refine ⟨fun _ => rfl, ?_, ?_⟩
    · intro n
      change (common.word n).1.target = (common.word (n + 1)).1.source
      exact common.itinerary.2.1 n
    · intro n
      have hprefix :
          prefixMetricLength (fun edge : alphabet => edge.1.length) word n =
            prefixMetricLength common.letterLength common.word n := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (common.letterLength_eq (common.word i)).symm
      change TraversesDirectedEdge rayData.ray
        (prefixMetricLength (fun edge : alphabet => edge.1.length) word n)
        (word n).1
      rw [hprefix]
      exact common.itinerary.2.2 n
  have htake (n : Nat) :
      (common.word.take n).map liftCommon = word.take n := by
    change (common.word.take n).map liftCommon =
      (Stream'.map liftCommon common.word).take n
    exact Stream'.map_take (n := n) (a := common.word) liftCommon
  have hprefixA (n : Nat) :
      substitutionA.iterateLetter n seed =
        word.take (substitutionA.iterateLetter n seed).length := by
    have hiterate :=
      substitution_iterateLetter_map_of_intertwining_b9 liftCommon
        common.substitutionA substitutionA (fun edge => (himageA edge).symm)
        n common.seed
    have hlength := congrArg List.length hiterate
    simp only [List.length_map] at hlength
    calc
      substitutionA.iterateLetter n seed =
          (common.substitutionA.iterateLetter n common.seed).map liftCommon := by
        simpa [seed] using hiterate.symm
      _ = (common.word.take
          (common.substitutionA.iterateLetter n common.seed).length).map
            liftCommon := congrArg (List.map liftCommon) (common.prefixA n)
      _ = word.take
          (common.substitutionA.iterateLetter n common.seed).length := htake _
      _ = word.take (substitutionA.iterateLetter n seed).length := by
        rw [hlength]
  have hprefixB (n : Nat) :
      substitutionB.iterateLetter n seed =
        word.take (substitutionB.iterateLetter n seed).length := by
    have hiterate :=
      substitution_iterateLetter_map_of_intertwining_b9 liftCommon
        common.substitutionB substitutionB (fun edge => (himageB edge).symm)
        n common.seed
    have hlength := congrArg List.length hiterate
    simp only [List.length_map] at hlength
    calc
      substitutionB.iterateLetter n seed =
          (common.substitutionB.iterateLetter n common.seed).map liftCommon := by
        simpa [seed] using hiterate.symm
      _ = (common.word.take
          (common.substitutionB.iterateLetter n common.seed).length).map
            liftCommon := congrArg (List.map liftCommon) (common.prefixB n)
      _ = word.take
          (common.substitutionB.iterateLetter n common.seed).length := htake _
      _ = word.take (substitutionB.iterateLetter n seed).length := by
        rw [hlength]
  exact ⟨{
    alphabet := alphabet
    alphabet_full := rfl
    substitutionA := substitutionA
    substitutionB := substitutionB
    seed := seed
    seed_eq := by simpa [seed, liftCommon, liftEdge] using common_seed
    word := word
    fixed_A := hfixedA
    fixed_B := hfixedB
    prolongable_A := hprolongableA
    prolongable_B := hprolongableB
    models_A := hmodelsA
    models_B := hmodelsB
    itinerary := hitinerary
    prefix_A := hprefixA
    prefix_B := hprefixB
    imageMetric_A := hmetricA
    imageMetric_B := hmetricB }⟩

/-- Leaf D0: construct both canonical substitutions and their common full
directed-edge ray word.  This isolates the existing full Markov-word
construction from the new decoder and restriction obligations. -/
theorem exists_fullAlphabetRayCodingData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    (K : PiecewiseLinearCommonMarkovPackage M)
    (rayData : RebuiltReturnedRayData M)
    (seedData : RebuiltRaySeedData K rayData) :
    Nonempty (FullAlphabetRayCodingData K rayData seedData) := by
  have hscaleP0 : 0 < M.scaleP :=
    lt_trans (by norm_num) M.one_lt_scaleP
  have hscaleQ0 : 0 < M.scaleQ :=
    lt_trans (by norm_num) M.one_lt_scaleQ
  have hAslopePL :
      HasConstantAbsoluteSlopePLCore M.A (M.scaleP ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.A] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleP0 M.slopeP G.L
  have hBslopePL :
      HasConstantAbsoluteSlopePLCore M.B (M.scaleQ ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.B] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleQ0 M.slopeQ G.L
  have hAslope : HasConstantAbsoluteSlope M.A rayData.scaleA := by
    rw [rayData.scaleA_eq]
    simpa [HasConstantAbsoluteSlopePLCore, HasConstantAbsoluteSlope] using
      hAslopePL
  have hBslope : HasConstantAbsoluteSlope M.B rayData.scaleB := by
    rw [rayData.scaleB_eq]
    simpa [HasConstantAbsoluteSlopePLCore, HasConstantAbsoluteSlope] using
      hBslopePL
  have hmarkov : IsCommonMarkovSet M.A M.B K.K := by
    simpa [IsCommonMarkovSet, IsPiecewiseLinearCommonMarkovSet,
      FinsetAdjacent, PiecewiseLinearFinsetAdjacent] using K.markov
  have hcomm : Commute M.A M.B := by
    intro x
    simpa [PiecewiseLinearConstantSlopeSystem.A,
      PiecewiseLinearConstantSlopeSystem.B] using
      M.commute.iterate_iterate G.L G.L x
  rcases hmarkov with
    ⟨hzero, hone, hforwardA, hforwardB, hmarkovCells⟩
  have hmarkovA : ∀ ⦃x y : I⦄, FinsetAdjacent K.K x y →
      IsAffineOn M.A (Set.Icc x y) ∧
        IsStrictlyMonotoneOn M.A (Set.Icc x y) :=
    fun _ _ hxy => (hmarkovCells hxy).1
  have hmarkovB : ∀ ⦃x y : I⦄, FinsetAdjacent K.K x y →
      IsAffineOn M.B (Set.Icc x y) ∧
        IsStrictlyMonotoneOn M.B (Set.Icc x y) :=
    fun _ _ hxy => (hmarkovCells hxy).2
  obtain ⟨fullA⟩ := exists_fullDirectedMarkovSubstitution
    hzero hone hforwardA hmarkovA hAslope
  obtain ⟨fullB⟩ := exists_fullDirectedMarkovSubstitution
    hzero hone hforwardB hmarkovB hBslope
  have hmarkov' : IsCommonMarkovSet M.A M.B K.K :=
    ⟨hzero, hone, hforwardA, hforwardB, hmarkovCells⟩
  obtain ⟨common, hseed⟩ :=
    directed_edge_substitutions_and_common_ray_word seedData.edge
      hmarkov' hcomm K.base_mem rayData.scaleA_gt_one
      rayData.scaleB_gt_one hAslope hBslope seedData.edge_forward
      seedData.edge_source seedData.initial_traversal
      rayData.locally_unitSpeed rayData.onto_nonnegative
      rayData.return_A rayData.return_B
  exact commonRayFixedWord_extendToFullAlphabet
    common hseed fullA fullB

private theorem directedMarkovEdge_source_mem_d1
    {K : Finset I} (edge : DirectedMarkovEdge K) : edge.source ∈ K := by
  cases hdir : edge.forward <;>
    simp [DirectedMarkovEdge.source, hdir, DirectedMarkovEdge.lower,
      DirectedMarkovEdge.upper, edge.2.1, edge.2.2.1]

private theorem directedMarkovEdge_eq_of_forward_source_d1
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (hedge : edge.forward = true) (htarget : target.forward = true)
    (hsource : edge.source = target.source) : edge = target := by
  have hlower : edge.lower = target.lower := by
    simpa [DirectedMarkovEdge.source, hedge, htarget] using hsource
  have hupper : edge.upper = target.upper := by
    apply le_antisymm
    · by_contra hnot
      have hlt : target.upper < edge.upper := lt_of_not_ge hnot
      have hbetween : edge.lower < target.upper ∧ target.upper < edge.upper :=
        ⟨by rw [hlower]; exact target.2.2.2.1, hlt⟩
      exact edge.2.2.2.2 target.upper target.1.1.2.property hbetween
    · by_contra hnot
      have hlt : edge.upper < target.upper := lt_of_not_ge hnot
      have hbetween : target.lower < edge.upper ∧ edge.upper < target.upper :=
        ⟨by rw [← hlower]; exact edge.2.2.2.1, hlt⟩
      exact target.2.2.2.2 edge.upper edge.1.1.2.property hbetween
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext hlower
    · exact Subtype.ext hupper
  · exact hedge.trans htarget.symm

private theorem directedMarkovEdge_eq_of_backward_source_d1
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (hedge : edge.forward = false) (htarget : target.forward = false)
    (hsource : edge.source = target.source) : edge = target := by
  have hupper : edge.upper = target.upper := by
    simpa [DirectedMarkovEdge.source, hedge, htarget] using hsource
  have hlower : edge.lower = target.lower := by
    apply le_antisymm
    · by_contra hnot
      have hlt : target.lower < edge.lower := lt_of_not_ge hnot
      have hbetween : target.lower < edge.lower ∧ edge.lower < target.upper :=
        ⟨hlt, by rw [← hupper]; exact edge.2.2.2.1⟩
      exact target.2.2.2.2 edge.lower edge.1.1.1.property hbetween
    · by_contra hnot
      have hlt : edge.lower < target.lower := lt_of_not_ge hnot
      have hbetween : edge.lower < target.lower ∧ target.lower < edge.upper :=
        ⟨hlt, by rw [hupper]; exact target.2.2.2.1⟩
      exact edge.2.2.2.2 target.lower target.1.1.1.property hbetween
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext hlower
    · exact Subtype.ext hupper
  · exact hedge.trans htarget.symm

private theorem directedEdge_target_le_or_eq_forward_d1
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (htarget : target.forward = true)
    (hstart : edge.source ≤ target.source) :
    edge.target ≤ target.source ∨ edge = target := by
  cases hedge : edge.forward with
  | false =>
      left
      have hedgeOrder : edge.target < edge.source := by
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hedge]
          using edge.2.2.2.1
      exact hedgeOrder.le.trans hstart
  | true =>
      by_cases hlt : edge.source < target.source
      · left
        apply le_of_not_gt
        intro hcross
        apply edge.2.2.2.2 target.source
          (directedMarkovEdge_source_mem_d1 target)
        constructor
        · simpa [DirectedMarkovEdge.source, hedge] using hlt
        · simpa [DirectedMarkovEdge.target, hedge] using hcross
      · right
        apply directedMarkovEdge_eq_of_forward_source_d1 hedge htarget
        exact le_antisymm hstart (le_of_not_gt hlt)

private theorem directedEdge_target_ge_or_eq_backward_d1
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (htarget : target.forward = false)
    (hstart : target.source ≤ edge.source) :
    target.source ≤ edge.target ∨ edge = target := by
  cases hedge : edge.forward with
  | true =>
      left
      have hedgeOrder : edge.source < edge.target := by
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hedge]
          using edge.2.2.2.1
      exact hstart.trans hedgeOrder.le
  | false =>
      by_cases hlt : target.source < edge.source
      · left
        apply le_of_not_gt
        intro hcross
        apply edge.2.2.2.2 target.source
          (directedMarkovEdge_source_mem_d1 target)
        constructor
        · simpa [DirectedMarkovEdge.target, hedge] using hcross
        · simpa [DirectedMarkovEdge.source, hedge] using hlt
      · right
        apply directedMarkovEdge_eq_of_backward_source_d1 hedge htarget
        exact le_antisymm (le_of_not_gt hlt) hstart

private theorem directedEdgePathEndsAt_tail_d1
    {K : Finset I} {edge next : DirectedMarkovEdge K}
    {rest : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathEndsAt (edge :: next :: rest) x) :
    DirectedEdgePathEndsAt (next :: rest) x := by
  rcases h with ⟨init, last, heq, hlast⟩
  cases init with
  | nil => simp at heq
  | cons first init =>
      refine ⟨init, last, ?_, hlast⟩
      simpa using congrArg List.tail heq

private theorem literalDirectedEdgePath_contains_forward_d1
    {K : Finset I} {word : LiteralDirectedEdgeWord K} {x y : I}
    {target : DirectedMarkovEdge K}
    (htarget : target.forward = true)
    (hpath : IsLiteralDirectedEdgePath word)
    (hstart : DirectedEdgePathStartsAt word x)
    (hend : DirectedEdgePathEndsAt word y)
    (hx : x ≤ target.source) (hy : target.target ≤ y) :
    target ∈ word := by
  induction word generalizing x with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons edge rest ih =>
      rcases hstart with ⟨first, tail, heq, hfirst⟩
      simp only [List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have hedgeStart : edge.source ≤ target.source := by
        rw [hfirst]
        exact hx
      rcases directedEdge_target_le_or_eq_forward_d1
          htarget hedgeStart with hedgeNext | rfl
      · cases rest with
        | nil =>
            rcases hend with ⟨init, last, heq, hlast⟩
            cases init with
            | nil =>
                have hedgeLast : edge = last := by simpa using heq
                subst last
                exfalso
                have hbad : target.target ≤ target.source := by
                  calc
                    target.target ≤ y := hy
                    _ = edge.target := hlast.symm
                    _ ≤ target.source := hedgeNext
                have htargetOrder : target.source < target.target := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, htarget] using
                    target.2.2.2.1
                exact (not_le_of_gt htargetOrder) hbad
            | cons first init => simp at heq
        | cons next rest =>
            have hlink : edge.target = next.source := hpath.1
            have htailPath : IsLiteralDirectedEdgePath (next :: rest) :=
              hpath.2
            have htailStart :
                DirectedEdgePathStartsAt (next :: rest) edge.target :=
              ⟨next, rest, rfl, hlink.symm⟩
            have htailEnd : DirectedEdgePathEndsAt (next :: rest) y :=
              directedEdgePathEndsAt_tail_d1 hend
            exact List.mem_cons_of_mem edge
              (ih htailPath htailStart htailEnd hedgeNext)
      · exact List.mem_cons_self

private theorem literalDirectedEdgePath_contains_backward_d1
    {K : Finset I} {word : LiteralDirectedEdgeWord K} {x y : I}
    {target : DirectedMarkovEdge K}
    (htarget : target.forward = false)
    (hpath : IsLiteralDirectedEdgePath word)
    (hstart : DirectedEdgePathStartsAt word x)
    (hend : DirectedEdgePathEndsAt word y)
    (hx : target.source ≤ x) (hy : y ≤ target.target) :
    target ∈ word := by
  induction word generalizing x with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons edge rest ih =>
      rcases hstart with ⟨first, tail, heq, hfirst⟩
      simp only [List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have hedgeStart : target.source ≤ edge.source := by
        rw [hfirst]
        exact hx
      rcases directedEdge_target_ge_or_eq_backward_d1
          htarget hedgeStart with hedgeNext | rfl
      · cases rest with
        | nil =>
            rcases hend with ⟨init, last, heq, hlast⟩
            cases init with
            | nil =>
                have hedgeLast : edge = last := by simpa using heq
                subst last
                exfalso
                have hbad : target.source ≤ target.target := by
                  calc
                    target.source ≤ edge.target := hedgeNext
                    _ = y := hlast
                    _ ≤ target.target := hy
                have htargetOrder : target.target < target.source := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, htarget] using
                    target.2.2.2.1
                exact (not_le_of_gt htargetOrder) hbad
            | cons first init => simp at heq
        | cons next rest =>
            have hlink : edge.target = next.source := hpath.1
            have htailPath : IsLiteralDirectedEdgePath (next :: rest) :=
              hpath.2
            have htailStart :
                DirectedEdgePathStartsAt (next :: rest) edge.target :=
              ⟨next, rest, rfl, hlink.symm⟩
            have htailEnd : DirectedEdgePathEndsAt (next :: rest) y :=
              directedEdgePathEndsAt_tail_d1 hend
            exact List.mem_cons_of_mem edge
              (ih htailPath htailStart htailEnd hedgeNext)
      · exact List.mem_cons_self

private theorem directedMarkovEdge_forward_of_source_lt_target_d1
    {K : Finset I} (edge : DirectedMarkovEdge K)
    (h : edge.source < edge.target) : edge.forward = true := by
  cases hdir : edge.forward with
  | false =>
      exfalso
      have hback : edge.target < edge.source := by
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir]
          using edge.2.2.2.1
      exact (not_lt_of_ge h.le) hback
  | true => rfl

private theorem directedMarkovEdge_backward_of_target_lt_source_d1
    {K : Finset I} (edge : DirectedMarkovEdge K)
    (h : edge.target < edge.source) : edge.forward = false := by
  cases hdir : edge.forward with
  | false => rfl
  | true =>
      exfalso
      have hforward : edge.source < edge.target := by
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir]
          using edge.2.2.2.1
      exact (not_lt_of_ge h.le) hforward

private theorem modelsDirectedEdgeSubstitution_recordsOneStep_d1
    {T : IntervalMap} {K : Finset I}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet}
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet substitution)
    (hmono : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsStrictlyMonotoneOn T (Set.Icc x y)) :
    RecordsOneStepDirectedCrossings T alphabet substitution := by
  intro sourceEdge targetEdge hcross
  rcases hcross with ⟨x, y, ⟨hx, hy, hxy⟩, hTx, hTy⟩
  have hlowerMem : sourceEdge.1.lower ∈
      Set.Icc sourceEdge.1.lower sourceEdge.1.upper :=
    ⟨le_rfl, sourceEdge.1.2.2.2.1.le⟩
  have hupperMem : sourceEdge.1.upper ∈
      Set.Icc sourceEdge.1.lower sourceEdge.1.upper :=
    ⟨sourceEdge.1.2.2.2.1.le, le_rfl⟩
  have hxMem : x ∈ Set.Icc sourceEdge.1.lower sourceEdge.1.upper :=
    ⟨hx.1.le, hx.2.le⟩
  have hyMem : y ∈ Set.Icc sourceEdge.1.lower sourceEdge.1.upper :=
    ⟨hy.1.le, hy.2.le⟩
  rcases hmodels sourceEdge with ⟨hpath, hstart, hend⟩
  have hphysical : targetEdge.1 ∈
      geometricEdgeWord alphabet (substitution sourceEdge) := by
    rcases hmono sourceEdge.1.2 with hinc | hanti
    · cases hsourceDir : sourceEdge.1.forward with
      | false =>
          simp only [hsourceDir] at hxy
          have htargetOrder : targetEdge.1.target < targetEdge.1.source := by
            rw [← hTy, ← hTx]
            exact hinc hyMem hxMem hxy
          have htargetDir :=
            directedMarkovEdge_backward_of_target_lt_source_d1
              targetEdge.1 htargetOrder
          apply literalDirectedEdgePath_contains_backward_d1
            htargetDir hpath hstart hend
          · have hinside : T x < T sourceEdge.1.upper :=
              hinc hxMem hupperMem hx.2
            rw [← hTx]
            simpa [DirectedMarkovEdge.source, hsourceDir] using hinside.le
          · have hinside : T sourceEdge.1.lower < T y :=
              hinc hlowerMem hyMem hy.1
            rw [← hTy]
            simpa [DirectedMarkovEdge.target, hsourceDir] using hinside.le
      | true =>
          simp only [hsourceDir] at hxy
          have htargetOrder : targetEdge.1.source < targetEdge.1.target := by
            rw [← hTx, ← hTy]
            exact hinc hxMem hyMem hxy
          have htargetDir :=
            directedMarkovEdge_forward_of_source_lt_target_d1
              targetEdge.1 htargetOrder
          apply literalDirectedEdgePath_contains_forward_d1
            htargetDir hpath hstart hend
          · have hinside : T sourceEdge.1.lower < T x :=
              hinc hlowerMem hxMem hx.1
            rw [← hTx]
            simpa [DirectedMarkovEdge.source, hsourceDir] using hinside.le
          · have hinside : T y < T sourceEdge.1.upper :=
              hinc hyMem hupperMem hy.2
            rw [← hTy]
            simpa [DirectedMarkovEdge.target, hsourceDir] using hinside.le
    · cases hsourceDir : sourceEdge.1.forward with
      | false =>
          simp only [hsourceDir] at hxy
          have htargetOrder : targetEdge.1.source < targetEdge.1.target := by
            rw [← hTx, ← hTy]
            exact hanti hyMem hxMem hxy
          have htargetDir :=
            directedMarkovEdge_forward_of_source_lt_target_d1
              targetEdge.1 htargetOrder
          apply literalDirectedEdgePath_contains_forward_d1
            htargetDir hpath hstart hend
          · have hinside : T sourceEdge.1.upper < T x :=
              hanti hxMem hupperMem hx.2
            rw [← hTx]
            simpa [DirectedMarkovEdge.source, hsourceDir] using hinside.le
          · have hinside : T y < T sourceEdge.1.lower :=
              hanti hlowerMem hyMem hy.1
            rw [← hTy]
            simpa [DirectedMarkovEdge.target, hsourceDir] using hinside.le
      | true =>
          simp only [hsourceDir] at hxy
          have htargetOrder : targetEdge.1.target < targetEdge.1.source := by
            rw [← hTy, ← hTx]
            exact hanti hxMem hyMem hxy
          have htargetDir :=
            directedMarkovEdge_backward_of_target_lt_source_d1
              targetEdge.1 htargetOrder
          apply literalDirectedEdgePath_contains_backward_d1
            htargetDir hpath hstart hend
          · have hinside : T x < T sourceEdge.1.lower :=
              hanti hlowerMem hxMem hx.1
            rw [← hTx]
            simpa [DirectedMarkovEdge.source, hsourceDir] using hinside.le
          · have hinside : T sourceEdge.1.upper < T y :=
              hanti hyMem hupperMem hy.2
            rw [← hTy]
            simpa [DirectedMarkovEdge.target, hsourceDir] using hinside.le
  change targetEdge.1 ∈
    (substitution sourceEdge).map (occurringEdge alphabet) at hphysical
  rcases List.mem_map.mp hphysical with ⟨letter, hletter, hvalue⟩
  have hletterEq : letter = targetEdge := Subtype.ext hvalue
  simpa [hletterEq] using hletter

/-- Leaf D1: the canonical one-step words record every literal crossing of
the corresponding Markov map, not merely their two outside endpoints. -/
theorem fullCoding_oneStep_literalCrossingComplete
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (full : FullAlphabetRayCodingData K rayData seedData) :
    RecordsOneStepDirectedCrossings M.A full.alphabet full.substitutionA ∧
      RecordsOneStepDirectedCrossings M.B full.alphabet full.substitutionB := by
  have hmarkov : IsCommonMarkovSet M.A M.B K.K := by
    simpa [IsCommonMarkovSet, IsPiecewiseLinearCommonMarkovSet,
      FinsetAdjacent, PiecewiseLinearFinsetAdjacent] using K.markov
  constructor
  · exact modelsDirectedEdgeSubstitution_recordsOneStep_d1
      full.models_A (fun _ _ hadj => (hmarkov.2.2.2.2 hadj).1.2)
  · exact modelsDirectedEdgeSubstitution_recordsOneStep_d1
      full.models_B (fun _ _ hadj => (hmarkov.2.2.2.2 hadj).2.2)

private noncomputable def directedEdgeArc_d2 {K : Finset I}
    (edge : DirectedMarkovEdge K) (t : ℝ) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one
    (match edge.forward with
      | true => (edge.lower : ℝ) + t
      | false => (edge.upper : ℝ) - t)

private theorem directedEdgeArc_d2_coe_d2 {K : Finset I}
    (edge : DirectedMarkovEdge K) {t : ℝ}
    (ht0 : 0 ≤ t) (htle : t ≤ edge.length) :
    (directedEdgeArc_d2 edge t : ℝ) =
      match edge.forward with
      | true => (edge.lower : ℝ) + t
      | false => (edge.upper : ℝ) - t := by
  cases hdir : edge.forward with
  | false =>
      simp only [directedEdgeArc_d2, hdir]
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
        ⟨by
          change 0 ≤ (edge.upper : ℝ) - t
          dsimp [DirectedMarkovEdge.length] at htle
          linarith [edge.lower.property.1], by
          change (edge.upper : ℝ) - t ≤ 1
          linarith [edge.upper.property.2]⟩)
  | true =>
      simp only [directedEdgeArc_d2, hdir]
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
        ⟨by
          change 0 ≤ (edge.lower : ℝ) + t
          linarith [edge.lower.property.1], by
          change (edge.lower : ℝ) + t ≤ 1
          dsimp [DirectedMarkovEdge.length] at htle
          linarith [edge.upper.property.2]⟩)

/-- Recursive literal traversal beginning at an arbitrary real parameter. -/
private def TraversesLiteralWord_d2 {K : Finset I} (path : ℝ → I) :
    ℝ → LiteralDirectedEdgeWord K → Prop
  | _, [] => True
  | t, edge :: rest =>
      TraversesDirectedEdge path t edge ∧
        TraversesLiteralWord_d2 path (t + edge.length) rest

/-- The entire `n`th substituted edge word is the pointwise path obtained by
applying `T^[n]` to the source edge and rescaling its parameter by
`scale^n`.  This ordered realization is the induction invariant that the
per-letter crossing predicate alone does not retain. -/
private def RealizesIteratedLiteralWord_d2 {K : Finset I}
    (T : IntervalMap) (scale : ℝ)
    (alphabet : OccurringDirectedAlphabet K)
    (substitution : Symbolic.Substitution alphabet) (n : ℕ) : Prop :=
  ∀ sourceEdge : alphabet,
    TraversesLiteralWord_d2
      (fun t => iterateMap T n
        (directedEdgeArc_d2 sourceEdge.1 (t / scale ^ n))) 0
      (geometricEdgeWord alphabet
        (substitution.iterateLetter n sourceEdge))

/-- The identity iterate realizes the singleton source word. -/
private theorem realizesIteratedLiteralWord_zero_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet} :
    RealizesIteratedLiteralWord_d2 T scale alphabet substitution 0 := by
  intro sourceEdge
  simp only [RealizesIteratedLiteralWord_d2,
    Symbolic.Substitution.iterateLetter, geometricEdgeWord, occurringEdge,
    iterateMap, pow_zero, div_one, List.map_cons, List.map_nil,
    TraversesLiteralWord_d2]
  constructor
  · intro u hu0 hule
    simp only [Function.iterate_zero_apply, zero_add, occurringEdge]
    rw [directedEdgeArc_d2_coe_d2 sourceEdge.1 hu0 hule]
    rfl
  · trivial

/-! ### Local one-step metric/traversal support

These lemmas deliberately remain private to the D2 production proof.  The support
module currently exposes path/endpoints/metric data, but not the ordered
traversal consequence needed below. -/

private theorem realPartition_exists_adjacent_straddling_d2
    (partition : RealPartition) {x : ℝ} (hxI : x ∈ I)
    (hxnot : x ∉ partition.points) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ a < x ∧ x < b := by
  classical
  let lower := partition.points.filter fun z ↦ z < x
  let upper := partition.points.filter fun z ↦ x < z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    have hx0 : (0 : ℝ) < x := lt_of_le_of_ne hxI.1 fun h ↦ by
      apply hxnot
      simpa [h] using partition.zero_mem
    simp [lower, partition.zero_mem, hx0]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have hx1 : x < (1 : ℝ) := lt_of_le_of_ne hxI.2 fun h ↦ by
      apply hxnot
      simpa [h] using partition.one_mem
    simp [upper, partition.one_mem, hx1]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨a, b, ⟨ha'.1, hb'.1, ha'.2.trans hb'.2, ?_⟩,
    ha'.2, hb'.2⟩
  intro z hz hzb
  by_cases hzx : z < x
  · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzx⟩
    have hza : z ≤ a := by simpa using hamax z hzlower
    exact (not_lt_of_ge hza) hzb.1
  · have hxz : x < z := lt_of_le_of_ne (le_of_not_gt hzx) fun h ↦ by
      apply hxnot
      simpa [h] using hz
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hxz⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzb.2

private theorem markovEdge_image_distance_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (e : DirectedMarkovEdge K) :
    |(T e.target : ℝ) - (T e.source : ℝ)| = scale * e.length := by
  classical
  rcases (hmarkov e.2).1 with ⟨m, c, hmc⟩
  rcases hslope.2 with ⟨partition, hpartition⟩
  obtain ⟨r, hrEdge, hrnot⟩ :=
    (Set.Ioo_infinite
      (show (e.lower : ℝ) < (e.upper : ℝ) from e.2.2.2.1)).exists_notMem_finset
        partition.points
  have hrI : r ∈ I := ⟨e.lower.property.1.trans hrEdge.1.le,
    hrEdge.2.le.trans e.upper.property.2⟩
  obtain ⟨u, v, huv, hur, hrv⟩ :=
    realPartition_exists_adjacent_straddling_d2 partition hrI hrnot
  rcases hpartition huv with ⟨m', c', hm'abs, hm'c⟩
  have hrmin : r < min v (e.upper : ℝ) := lt_min hrv hrEdge.2
  obtain ⟨s, hrs, hsmin⟩ := exists_between hrmin
  have hsv : s < v := hsmin.trans_le (min_le_left _ _)
  have hsupper : s < (e.upper : ℝ) :=
    hsmin.trans_le (min_le_right _ _)
  let rI : I := ⟨r, hrI⟩
  let sI : I := ⟨s, ⟨e.lower.property.1.trans (hrEdge.1.le.trans hrs.le),
    hsupper.le.trans e.upper.property.2⟩⟩
  have hrMarkov : rI ∈ Set.Icc e.lower e.upper :=
    ⟨hrEdge.1.le, hrEdge.2.le⟩
  have hsMarkov : sI ∈ Set.Icc e.lower e.upper :=
    ⟨hrEdge.1.le.trans hrs.le, hsupper.le⟩
  have hrCell : rI ∈ intervalCell u v := ⟨hur.le, hrv.le⟩
  have hsCell : sI ∈ intervalCell u v :=
    ⟨hur.le.trans hrs.le, hsv.le⟩
  have heqR : m * r + c = m' * r + c' := by
    calc
      m * r + c = (T rI : ℝ) := (hmc rI hrMarkov).symm
      _ = m' * r + c' := hm'c rI hrCell
  have heqS : m * s + c = m' * s + c' := by
    calc
      m * s + c = (T sI : ℝ) := (hmc sI hsMarkov).symm
      _ = m' * s + c' := hm'c sI hsCell
  have hmm' : m = m' := by nlinarith
  have hmabs : |m| = scale := by simpa [hmm'] using hm'abs
  have hlowerMem : e.lower ∈ Set.Icc e.lower e.upper :=
    ⟨le_rfl, e.2.2.2.1.le⟩
  have hupperMem : e.upper ∈ Set.Icc e.lower e.upper :=
    ⟨e.2.2.2.1.le, le_rfl⟩
  have hdiff : (T e.upper : ℝ) - (T e.lower : ℝ) =
      m * ((e.upper : ℝ) - (e.lower : ℝ)) := by
    rw [hmc e.upper hupperMem, hmc e.lower hlowerMem]
    ring
  have hforwardDistance :
      |(T e.upper : ℝ) - (T e.lower : ℝ)| = scale * e.length := by
    have hlenpos : 0 < (e.upper : ℝ) - (e.lower : ℝ) :=
      sub_pos.mpr (show (e.lower : ℝ) < (e.upper : ℝ) from e.2.2.2.1)
    change |(T e.upper : ℝ) - (T e.lower : ℝ)| =
      scale * ((e.upper : ℝ) - (e.lower : ℝ))
    rw [hdiff, abs_mul, hmabs, abs_of_pos hlenpos]
  cases hdir : e.forward with
  | false =>
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir,
        abs_sub_comm] using hforwardDistance
  | true =>
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir]
        using hforwardDistance

private theorem wordMetricLength_append_d2 {α : Type*} (length : α → ℝ)
    (u v : Symbolic.Word α) :
    wordMetricLength length (u ++ v) =
      wordMetricLength length u + wordMetricLength length v := by
  simp [wordMetricLength]

private def directedEdgeDisplacement_d2 {K : Finset I}
    (e : DirectedMarkovEdge K) : ℝ :=
  (e.target : ℝ) - (e.source : ℝ)

private theorem directedEdgeDisplacement_abs_d2 {K : Finset I}
    (e : DirectedMarkovEdge K) :
    |directedEdgeDisplacement_d2 e| = e.length := by
  cases hdir : e.forward with
  | false =>
      have hlt : (e.lower : ℝ) < (e.upper : ℝ) := e.2.2.2.1
      simp [directedEdgeDisplacement_d2, DirectedMarkovEdge.source,
        DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.length,
        abs_of_neg (sub_neg.mpr hlt)]
  | true =>
      have hlt : (e.lower : ℝ) < (e.upper : ℝ) := e.2.2.2.1
      simp [directedEdgeDisplacement_d2, DirectedMarkovEdge.source,
        DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.length,
        abs_of_pos (sub_pos.mpr hlt)]

private theorem directedEdgeDisplacement_le_length_d2 {K : Finset I}
    (e : DirectedMarkovEdge K) :
    directedEdgeDisplacement_d2 e ≤ e.length := by
  rw [← directedEdgeDisplacement_abs_d2]
  exact le_abs_self _

private theorem directedEdgePathEndsAt_tail_d2
    {K : Finset I} {e f : DirectedMarkovEdge K}
    {rest : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathEndsAt (e :: f :: rest) x) :
    DirectedEdgePathEndsAt (f :: rest) x := by
  rcases h with ⟨init, last, heq, hlast⟩
  cases init with
  | nil => simp at heq
  | cons first init =>
      refine ⟨init, last, ?_, hlast⟩
      simpa using congrArg List.tail heq

private theorem directedEdgePathEndsAt_prepend_d2
    {K : Finset I} {e : DirectedMarkovEdge K}
    {rest : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathEndsAt rest x) :
    DirectedEdgePathEndsAt (e :: rest) x := by
  rcases h with ⟨init, last, heq, hlast⟩
  refine ⟨e :: init, last, ?_, hlast⟩
  simp [heq]

private theorem literalDirectedEdgePath_displacement_sum_d2
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y) :
    (w.map directedEdgeDisplacement_d2).sum =
      (y : ℝ) - (x : ℝ) := by
  induction w generalizing x with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons e rest ih =>
      cases rest with
      | nil =>

          rcases hstart with ⟨first, tail, heq, hfirst⟩
          simp at heq
          rcases heq with ⟨rfl, rfl⟩
          rcases hend with ⟨init, last, heq, hlast⟩
          cases init with
          | nil =>
              have helast : e = last := by simpa using heq
              subst last
              simp [directedEdgeDisplacement_d2, hfirst, hlast]
          | cons first init => simp at heq
      | cons f rest =>
          have hlink : e.target = f.source := hpath.1
          have htailPath : IsLiteralDirectedEdgePath (f :: rest) := hpath.2
          rcases hstart with ⟨first, tail, heq, hfirst⟩
          simp at heq
          rcases heq with ⟨rfl, rfl⟩
          have htailStart : DirectedEdgePathStartsAt (f :: rest) e.target :=
            ⟨f, rest, rfl, hlink.symm⟩
          have htailEnd := directedEdgePathEndsAt_tail_d2 hend
          have htailSum := ih htailPath htailStart htailEnd
          change directedEdgeDisplacement_d2 e +
            (List.map directedEdgeDisplacement_d2 (f :: rest)).sum = _
          rw [htailSum]
          simp [directedEdgeDisplacement_d2, hfirst, hlink]

private theorem literalDirectedEdgePath_source_coordinate_d2
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (i : ℕ) (hi : i < w.length) :
    ((w[i]).source : ℝ) = (x : ℝ) +
      ((w.take i).map directedEdgeDisplacement_d2).sum := by
  induction w generalizing x i with
  | nil => simp at hi
  | cons e rest ih =>
      rcases hstart with ⟨first, tail, heq, hsource⟩
      simp at heq
      rcases heq with ⟨rfl, rfl⟩
      cases i with
      | zero => simpa using congrArg Subtype.val hsource
      | succ i =>
          cases rest with
          | nil => simp at hi
          | cons f tail =>
              have hconnect : e.target = f.source := hpath.1
              have htailPath : IsLiteralDirectedEdgePath (f :: tail) := hpath.2
              have htailStart : DirectedEdgePathStartsAt (f :: tail) e.target :=
                ⟨f, tail, rfl, hconnect.symm⟩
              have hiTail : i < (f :: tail).length := by simpa using hi
              have hcoord := ih htailPath htailStart i hiTail
              simp only [List.getElem_cons_succ, List.take_succ_cons,
                List.map_cons, List.sum_cons]
              rw [hcoord]
              have hsourceR : (e.source : ℝ) = (x : ℝ) :=
                congrArg Subtype.val hsource
              rw [← hsourceR]
              simp [directedEdgeDisplacement_d2]
              ring

private theorem list_sum_le_sum_of_forall_mem_d2
    {α : Type*} {f g : α → ℝ} {w : List α}
    (h : ∀ z ∈ w, f z ≤ g z) :
    (w.map f).sum ≤ (w.map g).sum := by
  induction w with
  | nil => simp
  | cons z w ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h z (by simp))
        (ih fun q hq ↦ h q (by simp [hq]))

private theorem list_pointwise_eq_of_le_of_sum_eq_d2
    {α : Type*} {f g : α → ℝ} {w : List α}
    (hle : ∀ z ∈ w, f z ≤ g z)
    (hsum : (w.map f).sum = (w.map g).sum) :
    ∀ z ∈ w, f z = g z := by
  induction w with
  | nil => simp
  | cons q w ih =>
      have hqle : f q ≤ g q := hle q (by simp)
      have hrestle : (w.map f).sum ≤ (w.map g).sum :=
        list_sum_le_sum_of_forall_mem_d2
          (fun z hz ↦ hle z (by simp [hz]))
      have hqeq : f q = g q := by
        simp only [List.map_cons, List.sum_cons] at hsum
        linarith
      have hrestEq : (w.map f).sum = (w.map g).sum := by
        simp only [List.map_cons, List.sum_cons, hqeq] at hsum
        exact add_left_cancel hsum
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hqeq
      · exact ih (fun u hu ↦ hle u (by simp [hu])) hrestEq z hz

private theorem list_sum_map_neg_d2 {α : Type*} (f : α → ℝ) (w : List α) :
    (w.map (fun z ↦ -f z)).sum = -(w.map f).sum := by
  induction w with
  | nil => simp
  | cons z w ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

private theorem shortestLiteralPath_forward_d2
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hxy : x < y)
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|) :
    ∀ e ∈ w, directedEdgeDisplacement_d2 e = e.length := by
  have hdisp := literalDirectedEdgePath_displacement_sum_d2
    hpath hstart hend
  have hxyR : (x : ℝ) < (y : ℝ) := hxy
  have hsum : (w.map directedEdgeDisplacement_d2).sum =
      (w.map DirectedMarkovEdge.length).sum := by
    calc
      (w.map directedEdgeDisplacement_d2).sum =
          (y : ℝ) - (x : ℝ) := hdisp
      _ = |(y : ℝ) - (x : ℝ)| :=
        (abs_of_pos (sub_pos.mpr hxyR)).symm
      _ = wordMetricLength DirectedMarkovEdge.length w := hmetric.symm
      _ = (w.map DirectedMarkovEdge.length).sum := rfl
  exact list_pointwise_eq_of_le_of_sum_eq_d2
    (fun e _he ↦ directedEdgeDisplacement_le_length_d2 e) hsum

private theorem shortestLiteralPath_backward_d2
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hyx : y < x)
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|) :
    ∀ e ∈ w, directedEdgeDisplacement_d2 e = -e.length := by
  have hdisp := literalDirectedEdgePath_displacement_sum_d2
    hpath hstart hend
  have hyxR : (y : ℝ) < (x : ℝ) := hyx
  have hnegSum : (w.map (fun e ↦ -directedEdgeDisplacement_d2 e)).sum =
      -(w.map directedEdgeDisplacement_d2).sum :=
    list_sum_map_neg_d2 directedEdgeDisplacement_d2 w
  have hsum : (w.map (fun e ↦ -directedEdgeDisplacement_d2 e)).sum =
      (w.map DirectedMarkovEdge.length).sum := by
    calc
      (w.map (fun e ↦ -directedEdgeDisplacement_d2 e)).sum =
          -(w.map directedEdgeDisplacement_d2).sum := hnegSum
      _ = -((y : ℝ) - (x : ℝ)) := by rw [hdisp]
      _ = |(y : ℝ) - (x : ℝ)| := by
        rw [abs_of_neg (sub_neg.mpr hyxR)]
      _ = wordMetricLength DirectedMarkovEdge.length w := hmetric.symm
      _ = (w.map DirectedMarkovEdge.length).sum := rfl
  have heach := list_pointwise_eq_of_le_of_sum_eq_d2
    (f := fun e ↦ -directedEdgeDisplacement_d2 e)
    (g := DirectedMarkovEdge.length)
    (fun e _he ↦ by
      rw [← directedEdgeDisplacement_abs_d2]
      exact neg_le_abs _) hsum
  intro e he
  have := heach e he
  linarith

private theorem traversesLiteralWord_of_pointwise_d2
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (h : ∀ (i : ℕ) (hi : i < w.length),
      TraversesDirectedEdge ψ
        (t + wordMetricLength DirectedMarkovEdge.length (w.take i)) (w[i])) :
    TraversesLiteralWord_d2 ψ t w := by
  induction w generalizing t with
  | nil => trivial
  | cons e rest ih =>
      constructor
      · have hzero := h 0 (by simp)
        simpa [wordMetricLength] using hzero
      · apply ih
        intro i hi
        have hsucc := h (i + 1) (by simpa using hi)
        simpa [wordMetricLength, add_assoc] using hsucc

private theorem wordMetricLength_take_le_d2
    {α : Type*} {length : α → ℝ} (hlength : ∀ a, 0 ≤ length a)
    (w : List α) (n : ℕ) :
    wordMetricLength length (w.take n) ≤ wordMetricLength length w := by
  calc
    wordMetricLength length (w.take n) ≤
        wordMetricLength length (w.take n) +
          wordMetricLength length (w.drop n) :=
      le_add_of_nonneg_right
        (List.sum_nonneg fun z hz ↦ by
          obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hz
          exact hlength a)
    _ = wordMetricLength length (w.take n ++ w.drop n) :=
      (wordMetricLength_append_d2 length (w.take n) (w.drop n)).symm
    _ = wordMetricLength length w := by rw [List.take_append_drop]

private theorem directedEdge_forward_of_displacement_eq_length_d2
    {K : Finset I} (e : DirectedMarkovEdge K)
    (h : directedEdgeDisplacement_d2 e = e.length) : e.forward = true := by
  cases hdir : e.forward with
  | false =>
      have hd : directedEdgeDisplacement_d2 e = -e.length := by
        simp [directedEdgeDisplacement_d2, DirectedMarkovEdge.source,
          DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
      have hp := e.length_pos
      rw [hd] at h
      linarith
  | true => rfl

private theorem directedEdge_backward_of_displacement_eq_neg_length_d2
    {K : Finset I} (e : DirectedMarkovEdge K)
    (h : directedEdgeDisplacement_d2 e = -e.length) : e.forward = false := by
  cases hdir : e.forward with
  | false => rfl
  | true =>
      have hd : directedEdgeDisplacement_d2 e = e.length := by
        simp [directedEdgeDisplacement_d2, DirectedMarkovEdge.source,
          DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
      have hp := e.length_pos
      rw [hd] at h
      linarith

private theorem traversesLiteralWord_of_shortest_segment_d2
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K} {x y : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|)
    (hsegment : ∀ v : ℝ, 0 ≤ v → v ≤ |(y : ℝ) - (x : ℝ)| →
      (ψ (t + v) : ℝ) =
        if x < y then (x : ℝ) + v else (x : ℝ) - v) :
    TraversesLiteralWord_d2 ψ t w := by
  have hmetricPos : 0 < wordMetricLength DirectedMarkovEdge.length w := by
    rcases hstart with ⟨first, rest, rfl, _hfirst⟩
    simp only [wordMetricLength, List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg first.length_pos
      (List.sum_nonneg fun z hz ↦ by
        obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hz
        exact e.length_pos.le)
  have hxyne : x ≠ y := by
    intro hxy
    subst y
    rw [hmetric] at hmetricPos
    simp at hmetricPos
  apply traversesLiteralWord_of_pointwise_d2
  intro i hi
  have hiMem : w[i] ∈ w := List.getElem_mem _
  have hcoord := literalDirectedEdgePath_source_coordinate_d2

    hpath hstart i hi
  let pref := wordMetricLength DirectedMarkovEdge.length (w.take i)
  have hprefNonneg : 0 ≤ pref := by
    dsimp [pref, wordMetricLength]
    exact List.sum_nonneg fun z hz ↦ by
      obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hz
      exact e.length_pos.le
  have hstepBound : pref + (w[i]).length ≤ |(y : ℝ) - (x : ℝ)| := by
    have htake := wordMetricLength_take_le_d2
      (fun e : DirectedMarkovEdge K ↦ e.length_pos.le) w (i + 1)
    rw [List.take_succ_eq_append_getElem hi,
      wordMetricLength_append_d2] at htake
    rw [hmetric] at htake
    simpa [wordMetricLength, pref] using htake
  by_cases hxy : x < y
  · have halign := shortestLiteralPath_forward_d2 hxy hpath hstart hend hmetric
    have hprefixDisp : ((w.take i).map directedEdgeDisplacement_d2).sum = pref := by
      dsimp [pref, wordMetricLength]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      exact halign e (List.mem_of_mem_take he)
    rw [hprefixDisp] at hcoord
    have hdir := directedEdge_forward_of_displacement_eq_length_d2
      w[i] (halign w[i] hiMem)
    have hlower : ((w[i]).lower : ℝ) = (x : ℝ) + pref := by
      simpa [DirectedMarkovEdge.source, hdir] using hcoord
    intro u hu0 hule
    have hv0 : 0 ≤ pref + u := add_nonneg hprefNonneg hu0
    have hvle : pref + u ≤ |(y : ℝ) - (x : ℝ)| := by linarith
    have hs := hsegment (pref + u) hv0 hvle
    rw [hdir]
    change (ψ ((t + pref) + u) : ℝ) = (w[i].lower : ℝ) + u
    calc
      (ψ ((t + pref) + u) : ℝ) = (ψ (t + (pref + u)) : ℝ) := by ring_nf
      _ = (x : ℝ) + (pref + u) := by simpa [hxy] using hs
      _ = (w[i].lower : ℝ) + u := by rw [hlower]; ring
  · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) hxyne.symm
    have halign := shortestLiteralPath_backward_d2 hyx hpath hstart hend hmetric
    have hprefixDisp : ((w.take i).map directedEdgeDisplacement_d2).sum = -pref := by
      calc
        ((w.take i).map directedEdgeDisplacement_d2).sum =
            ((w.take i).map (fun e ↦ -e.length)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro e he
          exact halign e (List.mem_of_mem_take he)
        _ = -pref := by
          exact list_sum_map_neg_d2 DirectedMarkovEdge.length (w.take i)
    rw [hprefixDisp] at hcoord
    have hdir := directedEdge_backward_of_displacement_eq_neg_length_d2
      w[i] (halign w[i] hiMem)
    have hupper : ((w[i]).upper : ℝ) = (x : ℝ) - pref := by
      simpa [DirectedMarkovEdge.source, hdir] using hcoord
    intro u hu0 hule
    have hv0 : 0 ≤ pref + u := add_nonneg hprefNonneg hu0
    have hvle : pref + u ≤ |(y : ℝ) - (x : ℝ)| := by linarith
    have hs := hsegment (pref + u) hv0 hvle
    rw [hdir]
    change (ψ ((t + pref) + u) : ℝ) = (w[i].upper : ℝ) - u
    calc
      (ψ ((t + pref) + u) : ℝ) = (ψ (t + (pref + u)) : ℝ) := by ring_nf
      _ = (x : ℝ) - (pref + u) := by simpa [hxy] using hs
      _ = (w[i].upper : ℝ) - u := by rw [hupper]; ring

/-- The endpoint model and metric law, together with affine strict Markov
cells and the constant slope, give the ordered pointwise realization of every
one-step image.  `_oneStep` crossing completeness alone is not enough here. -/
private theorem realizesIteratedLiteralWord_one_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet}
    (hscale : 0 < scale)
    (hcell : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet substitution)
    (hmetric : SubstitutionScalesLetterLengths substitution
      (fun edge : alphabet => edge.1.length) scale) :
    RealizesIteratedLiteralWord_d2 T scale alphabet substitution 1 := by
  intro sourceEdge
  let e := sourceEdge.1
  let w := geometricEdgeWord alphabet (substitution sourceEdge)
  have hlen : 0 < e.length := e.length_pos
  have hlowerMem : e.lower ∈ Set.Icc e.lower e.upper :=
    ⟨le_rfl, e.2.2.2.1.le⟩
  have hupperMem : e.upper ∈ Set.Icc e.lower e.upper :=
    ⟨e.2.2.2.1.le, le_rfl⟩
  have hsourceMem : e.source ∈ Set.Icc e.lower e.upper := by
    cases hdir : e.forward <;>
      simp [DirectedMarkovEdge.source, hdir, hlowerMem, hupperMem]
  have htargetMem : e.target ∈ Set.Icc e.lower e.upper := by
    cases hdir : e.forward <;>
      simp [DirectedMarkovEdge.target, hdir, hlowerMem, hupperMem]
  rcases (hcell e.2).1 with ⟨m, c, haff⟩
  have hdistance := markovEdge_image_distance_d2 hcell hslope e
  have himageNe : T e.source ≠ T e.target := by
    intro heq
    have : (0 : ℝ) = scale * e.length := by
      simpa [heq] using hdistance
    nlinarith
  have hwordMetric : wordMetricLength DirectedMarkovEdge.length w =
      |(T e.target : ℝ) - (T e.source : ℝ)| := by
    calc
      wordMetricLength DirectedMarkovEdge.length w =
          wordMetricLength (fun edge : alphabet => edge.1.length)
            (substitution sourceEdge) := by
        simp [w, wordMetricLength, geometricEdgeWord, occurringEdge,
          List.map_map, Function.comp_def]
      _ = scale * e.length := hmetric sourceEdge
      _ = |(T e.target : ℝ) - (T e.source : ℝ)| := hdistance.symm
  have htrav : TraversesLiteralWord_d2
      (fun t => T (directedEdgeArc_d2 e (t / scale))) 0 w := by
    apply traversesLiteralWord_of_shortest_segment_d2
      (hmodels sourceEdge).1 (hmodels sourceEdge).2.1
        (hmodels sourceEdge).2.2 hwordMetric
    intro v hv0 hvle
    let u := v / scale
    have hu0 : 0 ≤ u := div_nonneg hv0 hscale.le
    have hule : u ≤ e.length := by
      apply (div_le_iff₀ hscale).2
      nlinarith [hvle, hdistance]
    have harcCoe := directedEdgeArc_d2_coe_d2 e hu0 hule
    have harcMem : directedEdgeArc_d2 e u ∈ Set.Icc e.lower e.upper := by
      cases hdir : e.forward with
      | false =>
          rw [hdir] at harcCoe
          constructor
          · change (e.lower : ℝ) ≤ (directedEdgeArc_d2 e u : ℝ)
            rw [harcCoe]
            dsimp [DirectedMarkovEdge.length] at hule
            linarith
          · change (directedEdgeArc_d2 e u : ℝ) ≤ (e.upper : ℝ)
            rw [harcCoe]
            linarith
      | true =>
          rw [hdir] at harcCoe
          constructor
          · change (e.lower : ℝ) ≤ (directedEdgeArc_d2 e u : ℝ)
            rw [harcCoe]
            linarith
          · change (directedEdgeArc_d2 e u : ℝ) ≤ (e.upper : ℝ)
            rw [harcCoe]
            dsimp [DirectedMarkovEdge.length] at hule
            linarith
    have hdispAffine :
        (T e.target : ℝ) - (T e.source : ℝ) =
          m * directedEdgeDisplacement_d2 e := by
      rw [haff e.target htargetMem, haff e.source hsourceMem]
      simp [directedEdgeDisplacement_d2]
      ring
    have harcParam : (directedEdgeArc_d2 e u : ℝ) = (e.source : ℝ) +
        directedEdgeDisplacement_d2 e / e.length * u := by
      cases hdir : e.forward with
      | false =>
          rw [hdir] at harcCoe
          rw [harcCoe]
          have hd : directedEdgeDisplacement_d2 e = -e.length := by
            simp [directedEdgeDisplacement_d2, DirectedMarkovEdge.source,
              DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
          rw [hd]
          simp only [DirectedMarkovEdge.source, hdir]
          field_simp [hlen.ne'] <;> ring
      | true =>
          rw [hdir] at harcCoe
          rw [harcCoe]
          have hd : directedEdgeDisplacement_d2 e = e.length := by
            simp [directedEdgeDisplacement_d2, DirectedMarkovEdge.source,
              DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
          rw [hd]
          simp only [DirectedMarkovEdge.source, hdir]
          field_simp [hlen.ne'] <;> ring
    have hinterp : (T (directedEdgeArc_d2 e u) : ℝ) = (T e.source : ℝ) +
        ((T e.target : ℝ) - (T e.source : ℝ)) / e.length * u := by
      rw [haff (directedEdgeArc_d2 e u) harcMem, harcParam, hdispAffine,
        haff e.source hsourceMem]
      field_simp [hlen.ne'] <;> ring
    by_cases hinc : T e.source < T e.target
    · have hincR : (T e.source : ℝ) < (T e.target : ℝ) := hinc
      have hinc' : T sourceEdge.1.source < T sourceEdge.1.target := by
        simpa [e] using hinc
      have hdelta : (T e.target : ℝ) - (T e.source : ℝ) =
          scale * e.length := by
        rw [← hdistance, abs_of_pos (sub_pos.mpr hincR)]
      simp only [if_pos hinc', zero_add]
      rw [hinterp, hdelta]
      dsimp [u]
      field_simp [hlen.ne', hscale.ne'] <;> ring
    · have hdec : T e.target < T e.source :=
        lt_of_le_of_ne (le_of_not_gt hinc) himageNe.symm
      have hinc' : ¬ T sourceEdge.1.source < T sourceEdge.1.target := by
        simpa [e] using hinc
      have hdecR : (T e.target : ℝ) < (T e.source : ℝ) := hdec
      have hdelta : (T e.target : ℝ) - (T e.source : ℝ) =
          -(scale * e.length) := by
        have hd := hdistance
        rw [abs_of_neg (sub_neg.mpr hdecR)] at hd
        linarith
      simp only [if_neg hinc', zero_add]
      rw [hinterp, hdelta]
      dsimp [u]
      field_simp [hlen.ne', hscale.ne'] <;> ring
  simpa [RealizesIteratedLiteralWord_d2, Symbolic.Substitution.iterateLetter,
    iterateMap, e, w] using htrav

private theorem traversesLiteralWord_append_d2
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {u v : LiteralDirectedEdgeWord K} :
    TraversesLiteralWord_d2 ψ t (u ++ v) ↔
      TraversesLiteralWord_d2 ψ t u ∧
        TraversesLiteralWord_d2 ψ
          (t + wordMetricLength DirectedMarkovEdge.length u) v := by
  induction u generalizing t with
  | nil => simp [TraversesLiteralWord_d2, wordMetricLength]
  | cons e u ih =>
      simp only [List.cons_append, TraversesLiteralWord_d2]
      rw [ih]
      simp [wordMetricLength, add_assoc]
      tauto

private theorem wordMetricLength_geometricEdgeWord_d2
    {K : Finset I} (alphabet : OccurringDirectedAlphabet K)
    (w : Symbolic.Word alphabet) :
    wordMetricLength DirectedMarkovEdge.length
        (geometricEdgeWord alphabet w) =
      wordMetricLength (fun edge : alphabet => edge.1.length) w := by
  simp [wordMetricLength, geometricEdgeWord, occurringEdge]

private theorem traversesLiteralWord_congr_d2
    {K : Finset I} {ψ χ : ℝ → I} {s t : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (htrav : TraversesLiteralWord_d2 ψ s w)
    (heq : ∀ u : ℝ, 0 ≤ u →
      u ≤ wordMetricLength DirectedMarkovEdge.length w →
        χ (t + u) = ψ (s + u)) :
    TraversesLiteralWord_d2 χ t w := by
  induction w generalizing s t with
  | nil => trivial
  | cons e rest ih =>
      have hrestNonneg :
          0 ≤ wordMetricLength DirectedMarkovEdge.length rest := by
        dsimp [wordMetricLength]
        exact List.sum_nonneg fun z hz ↦ by
          obtain ⟨q, _hq, rfl⟩ := List.mem_map.mp hz
          exact q.length_pos.le
      constructor
      · intro u hu0 hule
        have huTotal :
            u ≤ wordMetricLength DirectedMarkovEdge.length (e :: rest) := by

          calc
            u ≤ e.length := hule
            _ ≤ e.length + wordMetricLength DirectedMarkovEdge.length rest :=
              le_add_of_nonneg_right hrestNonneg
            _ = wordMetricLength DirectedMarkovEdge.length (e :: rest) := by
              simp [wordMetricLength]
        calc
          (χ (t + u) : ℝ) = (ψ (s + u) : ℝ) :=
            congrArg Subtype.val (heq u hu0 huTotal)
          _ = match e.forward with
              | true => (e.lower : ℝ) + u
              | false => (e.upper : ℝ) - u := htrav.1 u hu0 hule
      · apply ih htrav.2
        intro u hu0 hule
        have hbound : e.length + u ≤
            wordMetricLength DirectedMarkovEdge.length (e :: rest) := by
          calc
            e.length + u ≤ e.length +
                wordMetricLength DirectedMarkovEdge.length rest :=
              by linarith
            _ = wordMetricLength DirectedMarkovEdge.length (e :: rest) := by
              simp [wordMetricLength]
        simpa [add_assoc] using
          heq (e.length + u) (add_nonneg e.length_pos.le hu0) hbound

private theorem realizesOne_image_traversal_at_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet}
    (hscale : 0 < scale)
    (hmetric : SubstitutionScalesLetterLengths substitution
      (fun edge : alphabet => edge.1.length) scale)
    (hone : RealizesIteratedLiteralWord_d2 T scale alphabet substitution 1)
    {ψ χ : ℝ → I} {t : ℝ} (ht : 0 ≤ t) {e : alphabet}
    (htrav : TraversesDirectedEdge ψ t e.1)
    (hrel : ∀ r : ℝ, 0 ≤ r → χ (scale * r) = T (ψ r)) :
    TraversesLiteralWord_d2 χ (scale * t)
      (geometricEdgeWord alphabet (substitution e)) := by
  have honeE : TraversesLiteralWord_d2
      (fun v => T (directedEdgeArc_d2 e.1 (v / scale))) 0
      (geometricEdgeWord alphabet (substitution e)) := by
    simpa [RealizesIteratedLiteralWord_d2, Symbolic.Substitution.iterateLetter,
      iterateMap] using hone e
  have hgeoMetric : wordMetricLength DirectedMarkovEdge.length
      (geometricEdgeWord alphabet (substitution e)) =
        scale * e.1.length := by
    rw [wordMetricLength_geometricEdgeWord_d2]
    exact hmetric e
  apply traversesLiteralWord_congr_d2 honeE
  intro v hv0 hvle
  let u := v / scale
  have hu0 : 0 ≤ u := div_nonneg hv0 hscale.le
  have hule : u ≤ e.1.length := by
    rw [hgeoMetric] at hvle
    apply (div_le_iff₀ hscale).2
    simpa [mul_comm] using hvle
  have hψarc : ψ (t + u) = directedEdgeArc_d2 e.1 u := by
    apply Subtype.ext
    calc
      (ψ (t + u) : ℝ) =
          match e.1.forward with
          | true => (e.1.lower : ℝ) + u
          | false => (e.1.upper : ℝ) - u := htrav u hu0 hule
      _ = (directedEdgeArc_d2 e.1 u : ℝ) :=
        (directedEdgeArc_d2_coe_d2 e.1 hu0 hule).symm
  have htpu : 0 ≤ t + u := add_nonneg ht hu0
  have htime : scale * (t + u) = scale * t + v := by
    dsimp [u]
    field_simp [hscale.ne'] <;> ring
  calc
    χ (scale * t + v) = χ (scale * (t + u)) := by rw [htime]
    _ = T (ψ (t + u)) := hrel (t + u) htpu
    _ = T (directedEdgeArc_d2 e.1 u) := congrArg T hψarc
    _ = (fun q => T (directedEdgeArc_d2 e.1 (q / scale))) (0 + v) := by
      simp [u]

private theorem realizesOne_mapWord_traversal_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet}
    (hscale : 0 < scale)
    (hmetric : SubstitutionScalesLetterLengths substitution
      (fun edge : alphabet => edge.1.length) scale)
    (hone : RealizesIteratedLiteralWord_d2 T scale alphabet substitution 1)
    {ψ χ : ℝ → I} {t : ℝ} (ht : 0 ≤ t)
    (hrel : ∀ r : ℝ, 0 ≤ r → χ (scale * r) = T (ψ r))
    {w : Symbolic.Word alphabet}
    (htrav : TraversesLiteralWord_d2 ψ t (geometricEdgeWord alphabet w)) :
    TraversesLiteralWord_d2 χ (scale * t)
      (geometricEdgeWord alphabet (substitution.mapWord w)) := by
  induction w generalizing t with
  | nil => simp [Symbolic.Substitution.mapWord, geometricEdgeWord,
      TraversesLiteralWord_d2]
  | cons e rest ih =>
      change TraversesLiteralWord_d2 ψ t
        (e.1 :: geometricEdgeWord alphabet rest) at htrav
      rw [Symbolic.Substitution.mapWord_cons]
      simp only [geometricEdgeWord, List.map_append]
      rw [traversesLiteralWord_append_d2]
      constructor
      · exact realizesOne_image_traversal_at_d2 hscale hmetric hone ht
          htrav.1 hrel
      · have htail := ih (t := t + e.1.length)
          (add_nonneg ht e.1.length_pos.le) htrav.2
        have hblock : wordMetricLength DirectedMarkovEdge.length
            (geometricEdgeWord alphabet (substitution e)) =
              scale * e.1.length := by
          rw [wordMetricLength_geometricEdgeWord_d2]
          exact hmetric e
        change TraversesLiteralWord_d2 χ
          (scale * t + wordMetricLength DirectedMarkovEdge.length
            (geometricEdgeWord alphabet (substitution e)))
          (geometricEdgeWord alphabet (substitution.mapWord rest))
        rw [hblock]
        convert htail using 1 <;> ring

/-- Literal traversal distributes over substitution: applying the one-step
realization to every traversed letter yields the next iterated word. -/
private theorem realizesIteratedLiteralWord_succ_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet}
    (hscale : 0 < scale)
    (hmetric : SubstitutionScalesLetterLengths substitution
      (fun edge : alphabet => edge.1.length) scale)
    (hone : RealizesIteratedLiteralWord_d2 T scale alphabet substitution 1)
    {n : ℕ}
    (hn : RealizesIteratedLiteralWord_d2 T scale alphabet substitution n) :
    RealizesIteratedLiteralWord_d2 T scale alphabet substitution (n + 1) := by
  intro sourceEdge
  let ψ : ℝ → I := fun t => iterateMap T n
    (directedEdgeArc_d2 sourceEdge.1 (t / scale ^ n))
  let χ : ℝ → I := fun t => iterateMap T (n + 1)
    (directedEdgeArc_d2 sourceEdge.1 (t / scale ^ (n + 1)))
  have hrel : ∀ r : ℝ, 0 ≤ r → χ (scale * r) = T (ψ r) := by
    intro r _hr
    dsimp [χ, ψ]
    rw [iterateMap, Function.iterate_succ_apply']
    congr 2
    apply congrArg (directedEdgeArc_d2 sourceEdge.1)
    rw [pow_succ]
    field_simp [hscale.ne'] <;> ring
  have hnext := realizesOne_mapWord_traversal_d2 hscale hmetric hone
    (ψ := ψ) (χ := χ) (t := 0) (le_refl 0) hrel (hn sourceEdge)
  rw [Symbolic.Substitution.iterateLetter_succ]
  simpa [RealizesIteratedLiteralWord_d2, ψ, χ] using hnext

/-! ### Boundary-time decoding support -/

private theorem directedMarkovEdge_source_mem_d2
    {K : Finset I} (edge : DirectedMarkovEdge K) : edge.source ∈ K := by
  cases hdir : edge.forward <;>
    simp [DirectedMarkovEdge.source, hdir, DirectedMarkovEdge.lower,
      DirectedMarkovEdge.upper, edge.2.1, edge.2.2.1]

private theorem directedMarkovEdge_target_mem_d2
    {K : Finset I} (edge : DirectedMarkovEdge K) : edge.target ∈ K := by
  cases hdir : edge.forward <;>
    simp [DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.lower,
      DirectedMarkovEdge.upper, edge.2.1, edge.2.2.1]

private theorem directedMarkovEdge_eq_of_forward_source_d2
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (hedge : edge.forward = true) (htarget : target.forward = true)
    (hsource : edge.source = target.source) : edge = target := by
  have hlower : edge.lower = target.lower := by
    simpa [DirectedMarkovEdge.source, hedge, htarget] using hsource
  have hupper : edge.upper = target.upper := by
    apply le_antisymm
    · by_contra hnot
      have hlt : target.upper < edge.upper := lt_of_not_ge hnot
      have hbetween : edge.lower < target.upper ∧ target.upper < edge.upper :=
        ⟨by rw [hlower]; exact target.2.2.2.1, hlt⟩
      exact edge.2.2.2.2 target.upper target.1.1.2.property hbetween
    · by_contra hnot
      have hlt : edge.upper < target.upper := lt_of_not_ge hnot
      have hbetween : target.lower < edge.upper ∧ edge.upper < target.upper :=
        ⟨by rw [← hlower]; exact edge.2.2.2.1, hlt⟩
      exact target.2.2.2.2 edge.upper edge.1.1.2.property hbetween
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext hlower
    · exact Subtype.ext hupper
  · exact hedge.trans htarget.symm

private theorem directedMarkovEdge_eq_of_backward_source_d2
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (hedge : edge.forward = false) (htarget : target.forward = false)
    (hsource : edge.source = target.source) : edge = target := by
  have hupper : edge.upper = target.upper := by
    simpa [DirectedMarkovEdge.source, hedge, htarget] using hsource
  have hlower : edge.lower = target.lower := by
    apply le_antisymm
    · by_contra hnot
      have hlt : target.lower < edge.lower := lt_of_not_ge hnot
      have hbetween : target.lower < edge.lower ∧ edge.lower < target.upper :=
        ⟨hlt, by rw [← hupper]; exact edge.2.2.2.1⟩
      exact target.2.2.2.2 edge.lower edge.1.1.1.property hbetween
    · by_contra hnot
      have hlt : edge.lower < target.lower := lt_of_not_ge hnot
      have hbetween : edge.lower < target.lower ∧ target.lower < edge.upper :=
        ⟨hlt, by rw [hupper]; exact target.2.2.2.1⟩
      exact edge.2.2.2.2 target.lower target.1.1.1.property hbetween
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext hlower
    · exact Subtype.ext hupper
  · exact hedge.trans htarget.symm

private theorem directedEdge_target_le_or_eq_forward_d2
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (htarget : target.forward = true)
    (hstart : edge.source ≤ target.source) :
    edge.target ≤ target.source ∨ edge = target := by
  cases hedge : edge.forward with
  | false =>
      left
      have hedgeOrder : edge.target < edge.source := by
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hedge]
          using edge.2.2.2.1
      exact hedgeOrder.le.trans hstart
  | true =>
      by_cases hlt : edge.source < target.source
      · left
        apply le_of_not_gt
        intro hcross
        apply edge.2.2.2.2 target.source
          (directedMarkovEdge_source_mem_d2 target)
        constructor
        · simpa [DirectedMarkovEdge.source, hedge] using hlt
        · simpa [DirectedMarkovEdge.target, hedge] using hcross
      · right
        apply directedMarkovEdge_eq_of_forward_source_d2 hedge htarget
        exact le_antisymm hstart (le_of_not_gt hlt)

private theorem directedEdge_target_ge_or_eq_backward_d2
    {K : Finset I} {edge target : DirectedMarkovEdge K}
    (htarget : target.forward = false)
    (hstart : target.source ≤ edge.source) :
    target.source ≤ edge.target ∨ edge = target := by
  cases hedge : edge.forward with
  | true =>
      left
      have hedgeOrder : edge.source < edge.target := by
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hedge]
          using edge.2.2.2.1
      exact hstart.trans hedgeOrder.le
  | false =>

      by_cases hlt : target.source < edge.source
      · left
        apply le_of_not_gt
        intro hcross
        apply edge.2.2.2.2 target.source
          (directedMarkovEdge_source_mem_d2 target)
        constructor
        · simpa [DirectedMarkovEdge.target, hedge] using hcross
        · simpa [DirectedMarkovEdge.source, hedge] using hlt
      · right
        apply directedMarkovEdge_eq_of_backward_source_d2 hedge htarget
        exact le_antisymm (le_of_not_gt hlt) hstart

private theorem literalDirectedEdgePath_contains_forward_d2
    {K : Finset I} {word : LiteralDirectedEdgeWord K} {x y : I}
    {target : DirectedMarkovEdge K}
    (htarget : target.forward = true)
    (hpath : IsLiteralDirectedEdgePath word)
    (hstart : DirectedEdgePathStartsAt word x)
    (hend : DirectedEdgePathEndsAt word y)
    (hx : x ≤ target.source) (hy : target.target ≤ y) :
    target ∈ word := by
  induction word generalizing x with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons edge rest ih =>
      rcases hstart with ⟨first, tail, heq, hfirst⟩
      simp only [List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have hedgeStart : edge.source ≤ target.source := by
        rw [hfirst]
        exact hx
      rcases directedEdge_target_le_or_eq_forward_d2
          htarget hedgeStart with hedgeNext | rfl
      · cases rest with
        | nil =>
            rcases hend with ⟨init, last, heq, hlast⟩
            cases init with
            | nil =>
                have hedgeLast : edge = last := by simpa using heq
                subst last
                exfalso
                have hbad : target.target ≤ target.source := by
                  calc
                    target.target ≤ y := hy
                    _ = edge.target := hlast.symm
                    _ ≤ target.source := hedgeNext
                have htargetOrder : target.source < target.target := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, htarget] using
                    target.2.2.2.1
                exact (not_le_of_gt htargetOrder) hbad
            | cons first init => simp at heq
        | cons next rest =>
            have hlink : edge.target = next.source := hpath.1
            have htailPath : IsLiteralDirectedEdgePath (next :: rest) :=
              hpath.2
            have htailStart :
                DirectedEdgePathStartsAt (next :: rest) edge.target :=
              ⟨next, rest, rfl, hlink.symm⟩
            have htailEnd : DirectedEdgePathEndsAt (next :: rest) y :=
              directedEdgePathEndsAt_tail_d2 hend
            exact List.mem_cons_of_mem edge
              (ih htailPath htailStart htailEnd hedgeNext)
      · exact List.mem_cons_self

private theorem literalDirectedEdgePath_contains_backward_d2
    {K : Finset I} {word : LiteralDirectedEdgeWord K} {x y : I}
    {target : DirectedMarkovEdge K}
    (htarget : target.forward = false)
    (hpath : IsLiteralDirectedEdgePath word)
    (hstart : DirectedEdgePathStartsAt word x)
    (hend : DirectedEdgePathEndsAt word y)
    (hx : target.source ≤ x) (hy : y ≤ target.target) :
    target ∈ word := by
  induction word generalizing x with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons edge rest ih =>
      rcases hstart with ⟨first, tail, heq, hfirst⟩
      simp only [List.cons.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      have hedgeStart : target.source ≤ edge.source := by
        rw [hfirst]
        exact hx
      rcases directedEdge_target_ge_or_eq_backward_d2
          htarget hedgeStart with hedgeNext | rfl
      · cases rest with
        | nil =>
            rcases hend with ⟨init, last, heq, hlast⟩
            cases init with
            | nil =>
                have hedgeLast : edge = last := by simpa using heq
                subst last
                exfalso
                have hbad : target.source ≤ target.target := by
                  calc
                    target.source ≤ edge.target := hedgeNext
                    _ = y := hlast
                    _ ≤ target.target := hy
                have htargetOrder : target.target < target.source := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, htarget] using
                    target.2.2.2.1
                exact (not_le_of_gt htargetOrder) hbad
            | cons first init => simp at heq
        | cons next rest =>
            have hlink : edge.target = next.source := hpath.1
            have htailPath : IsLiteralDirectedEdgePath (next :: rest) :=
              hpath.2
            have htailStart :
                DirectedEdgePathStartsAt (next :: rest) edge.target :=
              ⟨next, rest, rfl, hlink.symm⟩
            have htailEnd : DirectedEdgePathEndsAt (next :: rest) y :=
              directedEdgePathEndsAt_tail_d2 hend
            exact List.mem_cons_of_mem edge
              (ih htailPath htailStart htailEnd hedgeNext)
      · exact List.mem_cons_self

private theorem traversesDirectedEdge_start_d2
    {K : Finset I} {ψ : ℝ → I} {t : ℝ} {e : DirectedMarkovEdge K}
    (h : TraversesDirectedEdge ψ t e) : ψ t = e.source := by
  have hzero := h 0 (le_refl 0) e.length_pos.le
  apply Subtype.ext
  cases hdir : e.forward <;>
    simp [hdir, DirectedMarkovEdge.source] at hzero ⊢ <;> exact hzero

private theorem traversesDirectedEdge_end_d2
    {K : Finset I} {ψ : ℝ → I} {t : ℝ} {e : DirectedMarkovEdge K}
    (h : TraversesDirectedEdge ψ t e) : ψ (t + e.length) = e.target := by
  have hend := h e.length e.length_pos.le le_rfl
  apply Subtype.ext
  cases hdir : e.forward with
  | false =>
      rw [hdir] at hend
      simpa [hdir, DirectedMarkovEdge.target, DirectedMarkovEdge.length]
        using hend
  | true =>
      rw [hdir] at hend
      simpa [hdir, DirectedMarkovEdge.target, DirectedMarkovEdge.length]
        using hend

private theorem traversesDirectedEdge_vertex_time_d2
    {K : Finset I} {ψ : ℝ → I} {t r : ℝ}
    {e : DirectedMarkovEdge K} {q : I}
    (htrav : TraversesDirectedEdge ψ t e) (hq : q ∈ K)
    (hr0 : 0 ≤ r) (hrle : r ≤ e.length)
    (hhit : ψ (t + r) = q) : r = 0 ∨ r = e.length := by
  by_cases hrz : r = 0
  · exact Or.inl hrz
  by_cases hre : r = e.length
  · exact Or.inr hre
  exfalso
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
  have hrlt : r < e.length := lt_of_le_of_ne hrle hre
  apply e.2.2.2.2 q hq
  have hqval : (q : ℝ) =
      match e.forward with
      | true => (e.lower : ℝ) + r
      | false => (e.upper : ℝ) - r := by
    calc
      (q : ℝ) = (ψ (t + r) : ℝ) := congrArg Subtype.val hhit.symm
      _ = _ := htrav r hr0 hrle
  cases hdir : e.forward with
  | false =>
      simp only [hdir] at hqval
      constructor
      · change (e.lower : ℝ) < (q : ℝ)
        dsimp [DirectedMarkovEdge.length] at hrlt
        linarith
      · change (q : ℝ) < (e.upper : ℝ)
        linarith
  | true =>
      simp only [hdir] at hqval
      constructor
      · change (e.lower : ℝ) < (q : ℝ)
        linarith
      · change (q : ℝ) < (e.upper : ℝ)
        dsimp [DirectedMarkovEdge.length] at hrlt
        linarith

private theorem traversesLiteralWord_vertex_time_split_d2
    {K : Finset I} {ψ : ℝ → I} {t r : ℝ}
    {w : LiteralDirectedEdgeWord K} {q : I}
    (htrav : TraversesLiteralWord_d2 ψ t w) (hq : q ∈ K)
    (hr0 : 0 ≤ r)
    (hrle : r ≤ wordMetricLength DirectedMarkovEdge.length w)
    (hhit : ψ (t + r) = q) :
    ∃ u v : LiteralDirectedEdgeWord K, w = u ++ v ∧
      wordMetricLength DirectedMarkovEdge.length u = r := by
  induction w generalizing t r with
  | nil =>
      have hr : r = 0 := by
        have : r ≤ 0 := by simpa [wordMetricLength] using hrle
        linarith
      subst r
      exact ⟨[], [], rfl, by simp [wordMetricLength]⟩
  | cons e rest ih =>
      by_cases hfirst : r ≤ e.length
      · rcases traversesDirectedEdge_vertex_time_d2 htrav.1 hq
          hr0 hfirst hhit with rfl | rfl
        · exact ⟨[], e :: rest, rfl, by simp [wordMetricLength]⟩
        · exact ⟨[e], rest, by simp, by simp [wordMetricLength]⟩
      · have her : e.length < r := lt_of_not_ge hfirst
        let r' := r - e.length
        have hr'0 : 0 ≤ r' := sub_nonneg.mpr her.le
        have hr'le : r' ≤
            wordMetricLength DirectedMarkovEdge.length rest := by
          have htotal : wordMetricLength DirectedMarkovEdge.length (e :: rest) =
              e.length + wordMetricLength DirectedMarkovEdge.length rest := by
            simp [wordMetricLength]
          rw [htotal] at hrle
          dsimp [r']
          linarith
        have hhit' : ψ ((t + e.length) + r') = q := by
          convert hhit using 1 <;> dsimp [r'] <;> ring
        obtain ⟨u, v, huv, huMetric⟩ :=
          ih htrav.2 hr'0 hr'le hhit'
        refine ⟨e :: u, v, ?_, ?_⟩
        · simp [huv]
        · change e.length + wordMetricLength DirectedMarkovEdge.length u = r
          rw [huMetric]
          dsimp [r']
          ring

private theorem traversesLiteralWord_geometry_d2
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (htrav : TraversesLiteralWord_d2 ψ t w) (hne : w ≠ []) :
    IsLiteralDirectedEdgePath w ∧
      DirectedEdgePathStartsAt w (ψ t) ∧
      DirectedEdgePathEndsAt w
        (ψ (t + wordMetricLength DirectedMarkovEdge.length w)) := by
  induction w generalizing t with
  | nil => exact (hne rfl).elim
  | cons e rest ih =>
      have hstartE := traversesDirectedEdge_start_d2 htrav.1
      cases rest with
      | nil =>
          have hendE := traversesDirectedEdge_end_d2 htrav.1
          refine ⟨by simp [IsLiteralDirectedEdgePath],
            ⟨e, [], rfl, hstartE.symm⟩, ?_⟩
          refine ⟨[], e, rfl, ?_⟩
          simpa [wordMetricLength] using hendE.symm
      | cons f tail =>
          have htail := ih htrav.2 (by simp)
          have hendE := traversesDirectedEdge_end_d2 htrav.1
          have hstartF := traversesDirectedEdge_start_d2 htrav.2.1
          have hlink : e.target = f.source := hendE.symm.trans hstartF
          refine ⟨⟨hlink, htail.1⟩,
            ⟨e, f :: tail, rfl, hstartE.symm⟩, ?_⟩
          have hendAll := directedEdgePathEndsAt_prepend_d2

            (e := e) htail.2.2
          simpa [wordMetricLength, add_assoc] using hendAll

private theorem traversesLiteralWord_contains_between_vertex_hits_d2
    {K : Finset I} {ψ : ℝ → I} {t r₁ r₂ : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (htrav : TraversesLiteralWord_d2 ψ t w)
    (target : DirectedMarkovEdge K)
    (hr₁0 : 0 ≤ r₁) (hrlt : r₁ < r₂)
    (hr₂le : r₂ ≤ wordMetricLength DirectedMarkovEdge.length w)
    (hhit₁ : ψ (t + r₁) = target.source)
    (hhit₂ : ψ (t + r₂) = target.target) :
    target ∈ w := by
  have hr₁le : r₁ ≤ wordMetricLength DirectedMarkovEdge.length w :=
    hrlt.le.trans hr₂le
  obtain ⟨a, b, hab, haMetric⟩ :=
    traversesLiteralWord_vertex_time_split_d2 htrav
      (directedMarkovEdge_source_mem_d2 target) hr₁0 hr₁le hhit₁
  have htravAB : TraversesLiteralWord_d2 ψ t (a ++ b) := by
    simpa [hab] using htrav
  have hsides := (traversesLiteralWord_append_d2).1 htravAB
  have htravB : TraversesLiteralWord_d2 ψ (t + r₁) b := by
    simpa [haMetric] using hsides.2
  have hwordMetric : wordMetricLength DirectedMarkovEdge.length w =
      wordMetricLength DirectedMarkovEdge.length a +
        wordMetricLength DirectedMarkovEdge.length b := by
    rw [hab, wordMetricLength_append_d2]
  have hdiff0 : 0 ≤ r₂ - r₁ := sub_nonneg.mpr hrlt.le
  have hdiffle : r₂ - r₁ ≤
      wordMetricLength DirectedMarkovEdge.length b := by
    rw [hwordMetric, haMetric] at hr₂le
    linarith
  have hhit₂' : ψ ((t + r₁) + (r₂ - r₁)) = target.target := by
    convert hhit₂ using 1 <;> ring
  obtain ⟨c, d, hcd, hcMetric⟩ :=
    traversesLiteralWord_vertex_time_split_d2 htravB
      (directedMarkovEdge_target_mem_d2 target)
      hdiff0 hdiffle hhit₂'
  have htravCD : TraversesLiteralWord_d2 ψ (t + r₁) (c ++ d) := by
    simpa [hcd] using htravB
  have htravC := (traversesLiteralWord_append_d2).1 htravCD |>.1
  have hcne : c ≠ [] := by
    intro hc
    subst c
    simp [wordMetricLength] at hcMetric
    linarith
  have hgeometry := traversesLiteralWord_geometry_d2 htravC hcne
  have hstart : DirectedEdgePathStartsAt c target.source := by
    rw [hhit₁] at hgeometry
    exact hgeometry.2.1
  have hendPoint :
      ψ ((t + r₁) + wordMetricLength DirectedMarkovEdge.length c) =
        target.target := by
    rw [hcMetric]
    exact hhit₂'
  have hend : DirectedEdgePathEndsAt c target.target := by
    rw [hendPoint] at hgeometry
    exact hgeometry.2.2
  cases htarget : target.forward with
  | false =>
      have hmem := literalDirectedEdgePath_contains_backward_d2
        (word := c) (x := target.source) (y := target.target)
        (target := target) htarget
        hgeometry.1 hstart hend le_rfl le_rfl
      rw [hab, hcd]
      simp [hmem]
  | true =>
      have hmem := literalDirectedEdgePath_contains_forward_d2
        (word := c) (x := target.source) (y := target.target)
        (target := target) htarget
        hgeometry.1 hstart hend le_rfl le_rfl
      rw [hab, hcd]
      simp [hmem]

private theorem wordMetricLength_mapWord_of_scales_d2
    {α : Type*} {substitution : Symbolic.Substitution α}
    {length : α → ℝ} {scale : ℝ}
    (hscale : SubstitutionScalesLetterLengths substitution length scale)
    (w : Symbolic.Word α) :
    wordMetricLength length (substitution.mapWord w) =
      scale * wordMetricLength length w := by
  induction w with
  | nil => simp [wordMetricLength]
  | cons a w ih =>
      rw [Symbolic.Substitution.mapWord_cons, wordMetricLength_append_d2,
        hscale a, ih]
      simp [wordMetricLength, mul_add]

private theorem wordMetricLength_iterateLetter_of_scales_d2
    {α : Type*} {substitution : Symbolic.Substitution α}
    {length : α → ℝ} {scale : ℝ}
    (hscale : SubstitutionScalesLetterLengths substitution length scale)
    (seed : α) (n : ℕ) :
    wordMetricLength length (substitution.iterateLetter n seed) =
      scale ^ n * length seed := by
  induction n with
  | zero => simp [Symbolic.Substitution.iterateLetter, wordMetricLength]
  | succ n ih =>
      rw [Symbolic.Substitution.iterateLetter_succ,
        wordMetricLength_mapWord_of_scales_d2 hscale, ih, pow_succ]
      ring

/-- A strict-interior target crossing in a pointwise realized word must occur
as the corresponding literal letter. -/
private theorem realizedIteratedLiteralWord_crossingComplete_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet}
    (hscale : 0 < scale)
    (hmetric : SubstitutionScalesLetterLengths substitution
      (fun edge : alphabet => edge.1.length) scale)
    {n : ℕ}
    (hrealizes : RealizesIteratedLiteralWord_d2 T scale alphabet substitution n) :
    ∀ sourceEdge targetEdge : alphabet,
      HasDirectedEdgeCrossing (iterateMap T n)
        sourceEdge.1 targetEdge.1 →
          targetEdge ∈ substitution.iterateLetter n sourceEdge := by
  intro sourceEdge targetEdge hcross
  rcases hcross with ⟨x, y, horder, hx, hy⟩
  let e := sourceEdge.1
  let p := scale ^ n
  let ux : ℝ :=
    match e.forward with
    | true => (x : ℝ) - (e.lower : ℝ)
    | false => (e.upper : ℝ) - (x : ℝ)
  let uy : ℝ :=
    match e.forward with
    | true => (y : ℝ) - (e.lower : ℝ)
    | false => (e.upper : ℝ) - (y : ℝ)
  have hp : 0 < p := pow_pos hscale n
  have hutimes : 0 < ux ∧ ux < uy ∧ uy < e.length := by
    cases hdir : e.forward with
    | false =>
        have hdir' : sourceEdge.1.forward = false := by
          simpa [e] using hdir
        simp only [InDirectedInteriorOrder, hdir'] at horder
        simp only [ux, uy, hdir]
        have hxup : (x : ℝ) < (e.upper : ℝ) := by
          simpa [e] using horder.1.2
        have hylow : (e.lower : ℝ) < (y : ℝ) := by
          simpa [e] using horder.2.1.1
        have hyx : (y : ℝ) < (x : ℝ) := by
          exact_mod_cast horder.2.2
        dsimp [DirectedMarkovEdge.length]
        constructor
        · exact sub_pos.mpr hxup
        constructor
        · exact sub_lt_sub_left hyx (e.upper : ℝ)
        · linarith
    | true =>
        have hdir' : sourceEdge.1.forward = true := by
          simpa [e] using hdir
        simp only [InDirectedInteriorOrder, hdir'] at horder
        simp only [ux, uy, hdir]
        have hxlow : (e.lower : ℝ) < (x : ℝ) := by
          simpa [e] using horder.1.1
        have hyup : (y : ℝ) < (e.upper : ℝ) := by
          simpa [e] using horder.2.1.2
        have hxy : (x : ℝ) < (y : ℝ) := by
          exact_mod_cast horder.2.2
        dsimp [DirectedMarkovEdge.length]
        constructor
        · exact sub_pos.mpr hxlow
        constructor
        · exact sub_lt_sub_right hxy (e.lower : ℝ)
        · linarith
  have huxle : ux ≤ e.length :=
    (hutimes.2.1.trans hutimes.2.2).le
  have huyle : uy ≤ e.length := hutimes.2.2.le
  have harcx : directedEdgeArc_d2 e ux = x := by
    apply Subtype.ext
    rw [directedEdgeArc_d2_coe_d2 e hutimes.1.le huxle]
    cases hdir : e.forward <;> simp [hdir, ux]
  have harcy : directedEdgeArc_d2 e uy = y := by
    apply Subtype.ext
    rw [directedEdgeArc_d2_coe_d2 e (hutimes.1.trans hutimes.2.1).le huyle]
    cases hdir : e.forward <;> simp [hdir, uy]
  let r₁ := p * ux
  let r₂ := p * uy
  have hr₁0 : 0 ≤ r₁ := mul_nonneg hp.le hutimes.1.le
  have hrlt : r₁ < r₂ := mul_lt_mul_of_pos_left hutimes.2.1 hp
  have hr₂lt : r₂ < p * e.length :=
    mul_lt_mul_of_pos_left hutimes.2.2 hp
  let w := geometricEdgeWord alphabet
    (substitution.iterateLetter n sourceEdge)
  let ψ : ℝ → I := fun t => iterateMap T n
    (directedEdgeArc_d2 e (t / p))
  have htrav : TraversesLiteralWord_d2 ψ 0 w := by
    simpa [ψ, w, e, p] using hrealizes sourceEdge
  have hwordMetric : wordMetricLength DirectedMarkovEdge.length w =
      p * e.length := by
    calc
      wordMetricLength DirectedMarkovEdge.length w =
          wordMetricLength (fun edge : alphabet => edge.1.length)
            (substitution.iterateLetter n sourceEdge) := by
        exact wordMetricLength_geometricEdgeWord_d2 alphabet _
      _ = scale ^ n * sourceEdge.1.length :=
        wordMetricLength_iterateLetter_of_scales_d2 hmetric sourceEdge n
      _ = p * e.length := by rfl
  have hr₂le : r₂ ≤ wordMetricLength DirectedMarkovEdge.length w := by
    rw [hwordMetric]
    exact hr₂lt.le
  have hdivx : r₁ / p = ux := by
    dsimp [r₁]
    field_simp [hp.ne'] <;> ring
  have hdivy : r₂ / p = uy := by
    dsimp [r₂]
    field_simp [hp.ne'] <;> ring
  have hhit₁ : ψ (0 + r₁) = targetEdge.1.source := by
    dsimp [ψ]
    simp only [zero_add]
    rw [hdivx, harcx]
    exact hx
  have hhit₂ : ψ (0 + r₂) = targetEdge.1.target := by
    dsimp [ψ]
    simp only [zero_add]
    rw [hdivy, harcy]
    exact hy
  have hphysical : targetEdge.1 ∈ w :=
    traversesLiteralWord_contains_between_vertex_hits_d2 htrav targetEdge.1
      hr₁0 hrlt hr₂le hhit₁ hhit₂
  change targetEdge.1 ∈
    (substitution.iterateLetter n sourceEdge).map
      (occurringEdge alphabet) at hphysical
  rcases List.mem_map.mp hphysical with ⟨letter, hletter, hvalue⟩
  have hletterEq : letter = targetEdge := Subtype.ext hvalue
  simpa [hletterEq] using hletter

/-- Generic Markov-map iteration driver used for each of `M.A` and `M.B`.
The retained one-step hypothesis is part of the frozen production interface;
the stronger ordered realization is derived from models and metric data. -/
private theorem recordsAllIteratedDirectedCrossings_of_oneStep_d2
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {substitution : Symbolic.Substitution alphabet}
    (hscale : 0 < scale)
    (hcell : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet substitution)
    (hmetric : SubstitutionScalesLetterLengths substitution
      (fun edge : alphabet => edge.1.length) scale)
    (_honeStep : RecordsOneStepDirectedCrossings T alphabet substitution) :
    RecordsAllIteratedDirectedCrossings T alphabet substitution := by
  have honeRealizes :
      RealizesIteratedLiteralWord_d2 T scale alphabet substitution 1 :=
    realizesIteratedLiteralWord_one_d2 hscale hcell hslope
      hmodels hmetric
  have hallRealizes : ∀ n : ℕ,
      RealizesIteratedLiteralWord_d2 T scale alphabet substitution n := by
    intro n
    induction n with
    | zero => exact realizesIteratedLiteralWord_zero_d2
    | succ n ih =>
        simpa [Nat.succ_eq_add_one] using
          realizesIteratedLiteralWord_succ_d2 hscale hmetric
            honeRealizes ih
  intro n sourceEdge targetEdge hcross
  exact realizedIteratedLiteralWord_crossingComplete_d2
    hscale hmetric (hallRealizes n) sourceEdge targetEdge hcross


/-- Leaf D2: literal path-word substitution and concatenation are compatible
with map iteration.  Induction on `n` upgrades the two one-step decoders to
complete decoders for the corresponding substitution powers. -/
theorem fullCoding_pathWord_iterationCompatible
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (full : FullAlphabetRayCodingData K rayData seedData)
    (_oneStep :
      RecordsOneStepDirectedCrossings M.A full.alphabet full.substitutionA ∧
        RecordsOneStepDirectedCrossings M.B full.alphabet full.substitutionB) :
    RecordsAllIteratedDirectedCrossings M.A
        full.alphabet full.substitutionA ∧
      RecordsAllIteratedDirectedCrossings M.B
        full.alphabet full.substitutionB := by
  have hscaleP0 : 0 < M.scaleP :=
    lt_trans (by norm_num) M.one_lt_scaleP
  have hscaleQ0 : 0 < M.scaleQ :=
    lt_trans (by norm_num) M.one_lt_scaleQ
  have hAslopePL :
      HasConstantAbsoluteSlopePLCore M.A (M.scaleP ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.A] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleP0 M.slopeP G.L
  have hBslopePL :
      HasConstantAbsoluteSlopePLCore M.B (M.scaleQ ^ G.L) := by
    simpa [PiecewiseLinearConstantSlopeSystem.B] using
      piecewiseLinear_constantAbsoluteSlope_iterate hscaleQ0 M.slopeQ G.L
  have hAslope : HasConstantAbsoluteSlope M.A rayData.scaleA := by
    rw [rayData.scaleA_eq]
    simpa [HasConstantAbsoluteSlopePLCore, HasConstantAbsoluteSlope] using
      hAslopePL
  have hBslope : HasConstantAbsoluteSlope M.B rayData.scaleB := by
    rw [rayData.scaleB_eq]
    simpa [HasConstantAbsoluteSlopePLCore, HasConstantAbsoluteSlope] using
      hBslopePL
  have hmarkov : IsCommonMarkovSet M.A M.B K.K := by
    simpa [IsCommonMarkovSet, IsPiecewiseLinearCommonMarkovSet,
      FinsetAdjacent, PiecewiseLinearFinsetAdjacent] using K.markov
  have hmarkovA : ∀ ⦃x y : I⦄, FinsetAdjacent K.K x y →
      IsAffineOn M.A (Set.Icc x y) ∧
        IsStrictlyMonotoneOn M.A (Set.Icc x y) :=
    fun _ _ hxy => (hmarkov.2.2.2.2 hxy).1
  have hmarkovB : ∀ ⦃x y : I⦄, FinsetAdjacent K.K x y →
      IsAffineOn M.B (Set.Icc x y) ∧
        IsStrictlyMonotoneOn M.B (Set.Icc x y) :=
    fun _ _ hxy => (hmarkov.2.2.2.2 hxy).2
  constructor
  · exact recordsAllIteratedDirectedCrossings_of_oneStep_d2
      (zero_lt_one.trans rayData.scaleA_gt_one) hmarkovA hAslope
      full.models_A full.imageMetric_A _oneStep.1
  · exact recordsAllIteratedDirectedCrossings_of_oneStep_d2
      (zero_lt_one.trans rayData.scaleB_gt_one) hmarkovB hBslope
      full.models_B full.imageMetric_B _oneStep.2

/-- Restriction data retaining the value-level intertwining with the full
alphabet.  The decoder fields state explicitly that powered completeness
survives restriction to exactly the letters occurring in the ray word. -/
structure OccurringAlphabetRestrictionData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (full : FullAlphabetRayCodingData K rayData seedData) where
  common : CommonRayFixedWord M.A M.B K.K rayData.ray
    rayData.scaleA rayData.scaleB
  seed_value : common.seed.1 = full.seed.1
  word_values : Stream'.map Subtype.val common.word =
    Stream'.map Subtype.val full.word
  image_values_A : ∀ edge : common.alphabet,
    ∃ fullEdge : full.alphabet, fullEdge.1 = edge.1 ∧
      (common.substitutionA edge).map Subtype.val =
        (full.substitutionA fullEdge).map Subtype.val
  image_values_B : ∀ edge : common.alphabet,
    ∃ fullEdge : full.alphabet, fullEdge.1 = edge.1 ∧
      (common.substitutionB edge).map Subtype.val =
        (full.substitutionB fullEdge).map Subtype.val
  decoder_A : RecordsAllIteratedDirectedCrossings M.A
    common.alphabet common.substitutionA
  decoder_B : RecordsAllIteratedDirectedCrossings M.B
    common.alphabet common.substitutionB

/-- The ordinary restriction data before powered decoder transport. -/
private structure OccurringRestrictionCoreB9
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (full : FullAlphabetRayCodingData K rayData seedData) where
  common : CommonRayFixedWord M.A M.B K.K rayData.ray
    rayData.scaleA rayData.scaleB
  seed_value : common.seed.1 = full.seed.1
  word_values : Stream'.map Subtype.val common.word =
    Stream'.map Subtype.val full.word
  image_values_A : ∀ edge : common.alphabet,
    ∃ fullEdge : full.alphabet, fullEdge.1 = edge.1 ∧
      (common.substitutionA edge).map Subtype.val =
        (full.substitutionA fullEdge).map Subtype.val
  image_values_B : ∀ edge : common.alphabet,
    ∃ fullEdge : full.alphabet, fullEdge.1 = edge.1 ∧
      (common.substitutionB edge).map Subtype.val =
        (full.substitutionB fullEdge).map Subtype.val

/-- Restrict a full fixed coding to exactly the underlying directed edges
which occur in its word, retaining all value-level comparison squares. -/
private theorem fullAlphabetRayCoding_restrict_core_b9
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (full : FullAlphabetRayCodingData K rayData seedData) :
    Nonempty (OccurringRestrictionCoreB9 full) := by
  classical
  let fullEquiv : full.alphabet ≃ DirectedMarkovEdge K.K :=
    { toFun := Subtype.val
      invFun := fun edge =>
        ⟨edge, by rw [full.alphabet_full]; exact Finset.mem_univ edge⟩
      left_inv := by
        intro edge
        apply Subtype.ext
        rfl
      right_inv := by
        intro edge
        rfl }
  let fullWord : Symbolic.InfiniteWord (DirectedMarkovEdge K.K) :=
    Symbolic.Substitution.relabelInfiniteWord fullEquiv full.word
  let ambientSubstitutionA :
      Symbolic.Substitution (DirectedMarkovEdge K.K) :=
    full.substitutionA.relabel fullEquiv
  let ambientSubstitutionB :
      Symbolic.Substitution (DirectedMarkovEdge K.K) :=
    full.substitutionB.relabel fullEquiv
  let ambientSeed : DirectedMarkovEdge K.K := fullEquiv full.seed
  have hfullFixedA : ambientSubstitutionA.IsFixedPoint fullWord := by
    simpa [ambientSubstitutionA, fullWord] using
      (Symbolic.Substitution.relabel_isFixedPoint_iff
        fullEquiv full.substitutionA full.word).2 full.fixed_A
  have hfullFixedB : ambientSubstitutionB.IsFixedPoint fullWord := by
    simpa [ambientSubstitutionB, fullWord] using
      (Symbolic.Substitution.relabel_isFixedPoint_iff
        fullEquiv full.substitutionB full.word).2 full.fixed_B
  have hfullProlongA : ambientSubstitutionA.ProlongableOn ambientSeed := by
    simpa [ambientSubstitutionA, ambientSeed] using
      (Symbolic.Substitution.relabel_prolongableOn_iff
        fullEquiv full.substitutionA full.seed).2 full.prolongable_A
  have hfullProlongB : ambientSubstitutionB.ProlongableOn ambientSeed := by
    simpa [ambientSubstitutionB, ambientSeed] using
      (Symbolic.Substitution.relabel_prolongableOn_iff
        fullEquiv full.substitutionB full.seed).2 full.prolongable_B
  have hseedAtZeroFull : full.word 0 = full.seed := by
    have hp := full.prefix_A 0
    have hleft : 0 <
        (full.substitutionA.iterateLetter 0 full.seed).length := by simp
    have hright : 0 < (full.word.take
        (full.substitutionA.iterateLetter 0 full.seed).length).length := by
      simp
    have hget :
        (full.substitutionA.iterateLetter 0 full.seed)[0]'hleft =
          (full.word.take
            (full.substitutionA.iterateLetter 0 full.seed).length)[0]'hright :=
      getElem_congr hp rfl hleft
    have htake := Stream'.take_get (m := 0)
      (n := (full.substitutionA.iterateLetter 0 full.seed).length)
      (a := full.word) hright
    exact (hget.trans htake).symm
  have hseedAtZero : fullWord 0 = ambientSeed := by
    simpa [fullWord, ambientSeed] using congrArg fullEquiv hseedAtZeroFull
  let occFinite :=
    Symbolic.Substitution.occurringAlphabet_finite fullWord
  let alphabet : OccurringDirectedAlphabet K.K := occFinite.toFinset
  let q : Symbolic.Substitution.OccurringAlphabet fullWord ≃ alphabet :=
    occFinite.subtypeEquivToFinset
  let seedOcc : Symbolic.Substitution.OccurringAlphabet fullWord :=
    ⟨ambientSeed, ⟨0, hseedAtZero⟩⟩
  let seed : alphabet := q seedOcc
  let wordOcc := Symbolic.Substitution.wordOnOccurringAlphabet fullWord
  let word : Symbolic.InfiniteWord alphabet := fun n => q (wordOcc n)
  let restrictedA :=
    ambientSubstitutionA.restrictToOccurringAlphabet fullWord hfullFixedA
  let restrictedB :=
    ambientSubstitutionB.restrictToOccurringAlphabet fullWord hfullFixedB
  let substitutionA : Symbolic.Substitution alphabet := restrictedA.relabel q
  let substitutionB : Symbolic.Substitution alphabet := restrictedB.relabel q
  have hseedValue : seed.1 = ambientSeed := rfl
  have hseedValueFull : seed.1 = full.seed.1 := rfl
  have hwordValue (n : Nat) : (word n).1 = fullWord n := rfl
  have hwordValueFull (n : Nat) : (word n).1 = (full.word n).1 := rfl
  have hwordValues : Stream'.map Subtype.val word = fullWord := by
    funext n
    exact hwordValue n
  have hwordValuesFull : Stream'.map Subtype.val word =
      Stream'.map Subtype.val full.word := by
    funext n
    exact hwordValueFull n
  have himageA (edge : alphabet) :
      (substitutionA edge).map Subtype.val =
        ambientSubstitutionA edge.1 := by
    have hrestricted :=
      ambientSubstitutionA.restrictToOccurringAlphabet_image_values
        fullWord hfullFixedA (q.symm edge)
    simpa [substitutionA, restrictedA,
      Symbolic.Substitution.relabel, List.map_map] using hrestricted
  have himageB (edge : alphabet) :
      (substitutionB edge).map Subtype.val =
        ambientSubstitutionB edge.1 := by
    have hrestricted :=
      ambientSubstitutionB.restrictToOccurringAlphabet_image_values
        fullWord hfullFixedB (q.symm edge)
    simpa [substitutionB, restrictedB,
      Symbolic.Substitution.relabel, List.map_map] using hrestricted
  have himageFullA (edge : alphabet) :
      ∃ fullEdge : full.alphabet, fullEdge.1 = edge.1 ∧
        (substitutionA edge).map Subtype.val =
          (full.substitutionA fullEdge).map Subtype.val := by
    let fullEdge : full.alphabet := fullEquiv.symm edge.1
    refine ⟨fullEdge, ?_, ?_⟩
    · rfl
    · calc
        (substitutionA edge).map Subtype.val =
            ambientSubstitutionA edge.1 := himageA edge
        _ = (full.substitutionA fullEdge).map fullEquiv := by
          change (full.substitutionA.relabel fullEquiv) edge.1 = _
          rw [show edge.1 = fullEquiv fullEdge by simp [fullEdge]]
          exact full.substitutionA.relabel_apply_equiv fullEquiv fullEdge
        _ = (full.substitutionA fullEdge).map Subtype.val := by
          rfl
  have himageFullB (edge : alphabet) :
      ∃ fullEdge : full.alphabet, fullEdge.1 = edge.1 ∧
        (substitutionB edge).map Subtype.val =
          (full.substitutionB fullEdge).map Subtype.val := by
    let fullEdge : full.alphabet := fullEquiv.symm edge.1
    refine ⟨fullEdge, ?_, ?_⟩
    · rfl
    · calc
        (substitutionB edge).map Subtype.val =
            ambientSubstitutionB edge.1 := himageB edge
        _ = (full.substitutionB fullEdge).map fullEquiv := by
          change (full.substitutionB.relabel fullEquiv) edge.1 = _
          rw [show edge.1 = fullEquiv fullEdge by simp [fullEdge]]
          exact full.substitutionB.relabel_apply_equiv fullEquiv fullEdge
        _ = (full.substitutionB fullEdge).map Subtype.val := by
          rfl
  let values : Symbolic.LetterCoding alphabet (DirectedMarkovEdge K.K) :=
    ⟨Subtype.val⟩
  have hfixedA : substitutionA.IsFixedPoint word := by
    have hnatural := Symbolic.LetterCoding.mapInfinite_substitution values
      substitutionA ambientSubstitutionA himageA word
    have hvalues : values.mapInfinite word = fullWord := hwordValues
    rw [hvalues, hfullFixedA] at hnatural
    apply funext
    intro n
    apply Subtype.ext
    simpa [values, hwordValue] using congrFun hnatural n
  have hfixedB : substitutionB.IsFixedPoint word := by
    have hnatural := Symbolic.LetterCoding.mapInfinite_substitution values
      substitutionB ambientSubstitutionB himageB word
    have hvalues : values.mapInfinite word = fullWord := hwordValues
    rw [hvalues, hfullFixedB] at hnatural
    apply funext
    intro n
    apply Subtype.ext
    simpa [values, hwordValue] using congrFun hnatural n
  have hprolongA : substitutionA.ProlongableOn seed := by
    rcases hfullProlongA with ⟨tail, htail, hfullImage⟩
    obtain ⟨first, rest, hrestrictedImage⟩ :=
      List.exists_cons_of_ne_nil (substitutionA.image_ne_nil seed)
    have hvalues := himageA seed
    rw [hrestrictedImage, hseedValue, hfullImage] at hvalues
    simp only [List.map_cons] at hvalues
    have hparts := List.cons.inj hvalues
    have hfirst : first = seed := by
      apply Subtype.ext
      exact hparts.1.trans hseedValue.symm
    subst first
    refine ⟨rest, ?_, hrestrictedImage⟩
    intro hrest
    subst rest
    simp at hparts
    exact htail hparts.2
  have hprolongB : substitutionB.ProlongableOn seed := by
    rcases hfullProlongB with ⟨tail, htail, hfullImage⟩
    obtain ⟨first, rest, hrestrictedImage⟩ :=
      List.exists_cons_of_ne_nil (substitutionB.image_ne_nil seed)
    have hvalues := himageB seed
    rw [hrestrictedImage, hseedValue, hfullImage] at hvalues
    simp only [List.map_cons] at hvalues
    have hparts := List.cons.inj hvalues
    have hfirst : first = seed := by
      apply Subtype.ext
      exact hparts.1.trans hseedValue.symm
    subst first
    refine ⟨rest, ?_, hrestrictedImage⟩
    intro hrest
    subst rest
    simp at hparts
    exact htail hparts.2
  have hwordHead : word.head = seed := by
    change q (wordOcc 0) = q seedOcc
    apply congrArg q
    apply Subtype.ext
    exact hseedAtZero
  have hprefixA (n : Nat) :
      substitutionA.iterateLetter n seed =
        word.take (substitutionA.iterateLetter n seed).length :=
    Symbolic.Substitution.iterateLetter_eq_take_of_fixedPoint
      hfixedA hwordHead n
  have hprefixB (n : Nat) :
      substitutionB.iterateLetter n seed =
        word.take (substitutionB.iterateLetter n seed).length :=
    Symbolic.Substitution.iterateLetter_eq_take_of_fixedPoint
      hfixedB hwordHead n
  have hevery (edge : alphabet) :
      Symbolic.Substitution.OccursInInfiniteWord edge word := by
    have hedgeOcc : edge.1 ∈
        Symbolic.Substitution.OccurringAlphabet fullWord :=
      occFinite.mem_toFinset.mp edge.2
    rcases hedgeOcc with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [hwordValue n]
    exact hn
  have hgeneratingA : substitutionA.IsGeneratingLetter seed := by
    intro edge
    exact substitutionA.isGeneratingLetter_of_iterateLetter_eq_take
      hprolongA hprefixA edge (hevery edge)
  have hgeneratingB : substitutionB.IsGeneratingLetter seed := by
    intro edge
    exact substitutionB.isGeneratingLetter_of_iterateLetter_eq_take
      hprolongB hprefixB edge (hevery edge)
  have hmodelsA : ModelsDirectedEdgeSubstitution M.A alphabet substitutionA := by
    intro edge
    obtain ⟨fullEdge, hvalue, himages⟩ := himageFullA edge
    have hgeom : geometricEdgeWord alphabet (substitutionA edge) =
        geometricEdgeWord full.alphabet (full.substitutionA fullEdge) := by
      simpa [geometricEdgeWord, occurringEdge] using himages
    rw [hgeom]
    have hmodels := full.models_A fullEdge
    simpa [hvalue] using hmodels
  have hmodelsB : ModelsDirectedEdgeSubstitution M.B alphabet substitutionB := by
    intro edge
    obtain ⟨fullEdge, hvalue, himages⟩ := himageFullB edge
    have hgeom : geometricEdgeWord alphabet (substitutionB edge) =
        geometricEdgeWord full.alphabet (full.substitutionB fullEdge) := by
      simpa [geometricEdgeWord, occurringEdge] using himages
    rw [hgeom]
    have hmodels := full.models_B fullEdge
    simpa [hvalue] using hmodels
  let letterLength : alphabet → ℝ := fun edge => edge.1.length
  have hletterLengthEq (edge : alphabet) :
      letterLength edge = edge.1.length := rfl
  have hletterLengthPos (edge : alphabet) : 0 < letterLength edge :=
    edge.1.length_pos
  have hmetricA : SubstitutionScalesLetterLengths substitutionA
      letterLength rayData.scaleA := by
    intro edge
    obtain ⟨fullEdge, hvalue, himages⟩ := himageFullA edge
    calc
      wordMetricLength letterLength (substitutionA edge) =
          wordMetricLength DirectedMarkovEdge.length
            ((substitutionA edge).map Subtype.val) := by
        simp [wordMetricLength, letterLength]
      _ = wordMetricLength DirectedMarkovEdge.length
            ((full.substitutionA fullEdge).map Subtype.val) := by rw [himages]
      _ = wordMetricLength (fun e : full.alphabet => e.1.length)
            (full.substitutionA fullEdge) := by
        simp [wordMetricLength]
      _ = rayData.scaleA * fullEdge.1.length := full.imageMetric_A fullEdge
      _ = rayData.scaleA * edge.1.length := by rw [hvalue]
      _ = rayData.scaleA * letterLength edge := rfl
  have hmetricB : SubstitutionScalesLetterLengths substitutionB
      letterLength rayData.scaleB := by
    intro edge
    obtain ⟨fullEdge, hvalue, himages⟩ := himageFullB edge
    calc
      wordMetricLength letterLength (substitutionB edge) =
          wordMetricLength DirectedMarkovEdge.length
            ((substitutionB edge).map Subtype.val) := by
        simp [wordMetricLength, letterLength]
      _ = wordMetricLength DirectedMarkovEdge.length
            ((full.substitutionB fullEdge).map Subtype.val) := by rw [himages]
      _ = wordMetricLength (fun e : full.alphabet => e.1.length)
            (full.substitutionB fullEdge) := by
        simp [wordMetricLength]
      _ = rayData.scaleB * fullEdge.1.length := full.imageMetric_B fullEdge
      _ = rayData.scaleB * edge.1.length := by rw [hvalue]
      _ = rayData.scaleB * letterLength edge := rfl
  have hitinerary : HasLiteralUnitSpeedItinerary rayData.ray
      (occurringEdge alphabet) letterLength word := by
    refine ⟨hletterLengthEq, ?_, ?_⟩
    · intro n
      change (word n).1.target = (word (n + 1)).1.source
      rw [hwordValueFull n, hwordValueFull (n + 1)]
      exact full.itinerary.2.1 n
    · intro n
      have htime : prefixMetricLength letterLength word n =
          prefixMetricLength (fun e : full.alphabet => e.1.length)
            full.word n := by
        apply Finset.sum_congr rfl
        intro i hi
        change (word i).1.length = (full.word i).1.length
        rw [hwordValueFull i]
      change TraversesDirectedEdge rayData.ray
        (prefixMetricLength letterLength word n) (word n).1
      rw [htime, hwordValueFull n]
      exact full.itinerary.2.2 n
  have hprefixMetricA (n : Nat) :
      wordMetricLength letterLength
          (substitutionA.iterateLetter n seed) =
        rayData.scaleA ^ n * letterLength seed := by
    simpa using
      (Symbolic.Substitution.scalesLetterLengths_power
        substitutionA hmetricA n seed)
  have hprefixMetricB (n : Nat) :
      wordMetricLength letterLength
          (substitutionB.iterateLetter n seed) =
        rayData.scaleB ^ n * letterLength seed := by
    simpa using
      (Symbolic.Substitution.scalesLetterLengths_power
        substitutionB hmetricB n seed)
  have heigenA : IsPositiveLengthEigenvector substitutionA
      letterLength rayData.scaleA :=
    substitution_metric_lengths_give_incidence_identity
      hletterLengthPos hmetricA
  have heigenB : IsPositiveLengthEigenvector substitutionB
      letterLength rayData.scaleB :=
    substitution_metric_lengths_give_incidence_identity
      hletterLengthPos hmetricB
  have hgrowthA : LetterImagesGrow substitutionA seed := by
    intro bound
    refine ⟨bound, ?_⟩
    exact (Nat.le_succ bound).trans
      (substitutionA.succ_le_iterateLetter_length hprolongA bound)
  have hgrowthB : LetterImagesGrow substitutionB seed := by
    intro bound
    refine ⟨bound, ?_⟩
    exact (Nat.le_succ bound).trans
      (substitutionB.succ_le_iterateLetter_length hprolongB bound)
  have halphabet : alphabet.Nonempty := ⟨seed.1, seed.2⟩
  let common : CommonRayFixedWord M.A M.B K.K rayData.ray
      rayData.scaleA rayData.scaleB :=
    { alphabet := alphabet
      alphabet_nonempty := halphabet
      substitutionA := substitutionA
      substitutionB := substitutionB
      seed := seed
      word := word
      every_letter_occurs := hevery
      fixedA := hfixedA
      fixedB := hfixedB
      prolongableA := hprolongA
      prolongableB := hprolongB
      generatingA := hgeneratingA
      generatingB := hgeneratingB
      modelsA := hmodelsA
      modelsB := hmodelsB
      letterLength := letterLength
      letterLength_eq := hletterLengthEq
      letterLength_pos := hletterLengthPos
      itinerary := hitinerary
      prefixA := hprefixA
      prefixB := hprefixB
      prefixMetricA := hprefixMetricA
      prefixMetricB := hprefixMetricB
      imageMetricA := hmetricA
      imageMetricB := hmetricB
      lengthEigenA := heigenA
      lengthEigenB := heigenB
      growthA := hgrowthA
      growthB := hgrowthB
      one_lt_a := rayData.scaleA_gt_one
      one_lt_b := rayData.scaleB_gt_one
      ray_unit_speed := rayData.locally_unitSpeed
      ray_onto := rayData.onto_nonnegative
      ray_returnA := rayData.return_A
      ray_returnB := rayData.return_B }
  exact ⟨{
    common := common
    seed_value := by simpa [common] using hseedValueFull
    word_values := by simpa [common] using hwordValuesFull
    image_values_A := by simpa [common] using himageFullA
    image_values_B := by simpa [common] using himageFullB }⟩

/-- Powered crossing completeness descends along the injective inclusion of
the restricted alphabet into a full ambient directed alphabet. -/
private theorem recordsAllIteratedDirectedCrossings_transport_b9
    {T : IntervalMap} {K : Finset I}
    {fullAlphabet restrictedAlphabet : OccurringDirectedAlphabet K}
    {fullSubstitution : Symbolic.Substitution fullAlphabet}
    {restrictedSubstitution : Symbolic.Substitution restrictedAlphabet}
    (hfull : fullAlphabet = Finset.univ)
    (himage : ∀ edge : restrictedAlphabet,
      ∃ fullEdge : fullAlphabet, fullEdge.1 = edge.1 ∧
        (restrictedSubstitution edge).map Subtype.val =
          (fullSubstitution fullEdge).map Subtype.val)
    (hpowered : RecordsAllIteratedDirectedCrossings T
      fullAlphabet fullSubstitution) :
    RecordsAllIteratedDirectedCrossings T
      restrictedAlphabet restrictedSubstitution := by
  classical
  let lift : restrictedAlphabet → fullAlphabet := fun edge =>
    ⟨edge.1, by rw [hfull]; exact Finset.mem_univ edge.1⟩
  have hlift_value (edge : restrictedAlphabet) :
      (lift edge).1 = edge.1 := rfl
  have hlift_injective : Function.Injective lift := by
    intro left right heq
    apply Subtype.ext
    exact congrArg (fun edge : fullAlphabet => edge.1) heq
  have himage_lift (edge : restrictedAlphabet) :
      (restrictedSubstitution edge).map lift =
        fullSubstitution (lift edge) := by
    obtain ⟨fullEdge, hvalue, hvalues⟩ := himage edge
    have hfullEdge : fullEdge = lift edge := by
      apply Subtype.ext
      exact hvalue
    subst fullEdge
    apply (List.map_injective_iff.mpr Subtype.val_injective)
    simpa [List.map_map, lift] using hvalues
  have hiterate (n : Nat) (edge : restrictedAlphabet) :
      (restrictedSubstitution.iterateLetter n edge).map lift =
        fullSubstitution.iterateLetter n (lift edge) :=
    substitution_iterateLetter_map_of_intertwining_b9
      lift restrictedSubstitution fullSubstitution himage_lift n edge
  intro n sourceEdge targetEdge hcross
  let fullSource : fullAlphabet := lift sourceEdge
  let fullTarget : fullAlphabet := lift targetEdge
  have hcrossFull : HasDirectedEdgeCrossing (iterateMap T n)
      fullSource.1 fullTarget.1 := by
    simpa [fullSource, fullTarget, lift] using hcross
  have hmemFull : fullTarget ∈
      fullSubstitution.iterateLetter n fullSource :=
    hpowered n fullSource fullTarget hcrossFull
  have hmemMapped : fullTarget ∈
      (restrictedSubstitution.iterateLetter n sourceEdge).map lift := by
    rw [hiterate n sourceEdge]
    exact hmemFull
  rcases List.mem_map.mp hmemMapped with ⟨letter, hletter, hletterValue⟩
  have hletterEq : letter = targetEdge := by
    apply hlift_injective
    simpa [fullTarget] using hletterValue
  simpa [hletterEq] using hletter

/-- Leaf D3: simultaneous restriction to the common occurring alphabet
preserves fixedness, generation, metric scaling, and the powered decoder. -/
theorem fullCoding_restrictToOccurringAlphabet
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (full : FullAlphabetRayCodingData K rayData seedData)
    (_powered :
      RecordsAllIteratedDirectedCrossings M.A
          full.alphabet full.substitutionA ∧
        RecordsAllIteratedDirectedCrossings M.B
          full.alphabet full.substitutionB) :
    Nonempty (OccurringAlphabetRestrictionData full) := by
  obtain ⟨core⟩ := fullAlphabetRayCoding_restrict_core_b9 full
  have decoderA :=
    recordsAllIteratedDirectedCrossings_transport_b9
      full.alphabet_full core.image_values_A _powered.1
  have decoderB :=
    recordsAllIteratedDirectedCrossings_transport_b9
      full.alphabet_full core.image_values_B _powered.2
  exact ⟨{
    common := core.common
    seed_value := core.seed_value
    word_values := core.word_values
    image_values_A := core.image_values_A
    image_values_B := core.image_values_B
    decoder_A := decoderA
    decoder_B := decoderB }⟩

/-- The exact coding package.  `CommonRayFixedWord` supplies occurrence,
generation, fixed-point, metric-growth, itinerary, and ray-return data; the
two added fields are precisely the missing complete powered decoders. -/
structure ExactCommonRayCodingData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    (K : PiecewiseLinearCommonMarkovPackage M)
    (rayData : RebuiltReturnedRayData M)
    (seedData : RebuiltRaySeedData K rayData) where
  common : CommonRayFixedWord M.A M.B K.K rayData.ray
    rayData.scaleA rayData.scaleB
  seed_eq : common.seed.1 = seedData.edge
  decoder_A : RecordsAllIteratedDirectedCrossings M.A
    common.alphabet common.substitutionA
  decoder_B : RecordsAllIteratedDirectedCrossings M.B
    common.alphabet common.substitutionB

/-- Proved D-stage packaging aggregator. -/
theorem exists_exactCommonRayCodingData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    (K : PiecewiseLinearCommonMarkovPackage M)
    (rayData : RebuiltReturnedRayData M)
    (seedData : RebuiltRaySeedData K rayData) :
    Nonempty (ExactCommonRayCodingData K rayData seedData) := by
  obtain ⟨full⟩ := exists_fullAlphabetRayCodingData K rayData seedData
  have oneStep := fullCoding_oneStep_literalCrossingComplete full
  have powered := fullCoding_pathWord_iterationCompatible full oneStep
  obtain ⟨restricted⟩ :=
    fullCoding_restrictToOccurringAlphabet full powered
  exact ⟨{
    common := restricted.common
    seed_eq := restricted.seed_value.trans full.seed_eq
    decoder_A := restricted.decoder_A
    decoder_B := restricted.decoder_B }⟩

/-- Decoder-under-powers adapter for the first map. -/
theorem decoder_A_under_substitution_powers
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (coding : ExactCommonRayCodingData K rayData seedData) :
    RecordsAllIteratedDirectedCrossings M.A
      coding.common.alphabet coding.common.substitutionA := by
  exact coding.decoder_A

/-- Decoder-under-powers adapter for the second map. -/
theorem decoder_B_under_substitution_powers
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (coding : ExactCommonRayCodingData K rayData seedData) :
    RecordsAllIteratedDirectedCrossings M.B
      coding.common.alphabet coding.common.substitutionB := by
  exact coding.decoder_B

/-! ## Exactness gives primitivity -/

/-- The concrete primitivity predicate consumed by the proved substitution
recurrence theorem. -/
def IsPrimitiveSubstitution {alpha : Type*}
    (sigma : Symbolic.Substitution alpha) : Prop :=
  ∃ depth : Nat, 0 < depth ∧
    ∀ sourceLetter targetLetter : alpha,
      targetLetter ∈ sigma.iterateLetter depth sourceLetter

/-- Leaf X1: split each source edge into two ordered open subintervals,
apply exactness to both, pad the hitting depths using onto-ness, and take a
finite maximum.  The two subintervals realize both target orientations. -/
theorem exact_crosses_all_directed_edges_uniformly
    {T : IntervalMap} {K : Finset I}
    {alphabet : OccurringDirectedAlphabet K}
    (_hexact : IsTopologicallyExact T) :
    ∃ depth : Nat, 0 < depth ∧
      ∀ sourceEdge targetEdge : alphabet,
        HasDirectedEdgeCrossing (iterateMap T depth)
          sourceEdge.1 targetEdge.1 := by
  classical
  have honto : Function.Surjective T := by
    let U : Set I := Set.Iio rightEndpoint
    have hUopen : IsOpen U := isOpen_Iio
    have hUne : U.Nonempty := by
      exact ⟨leftEndpoint, by simp [U, leftEndpoint, rightEndpoint]⟩
    obtain ⟨n, hn⟩ := _hexact U hUopen hUne
    have hnpos : 0 < n := by
      by_contra hnnot
      have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnnot
      subst n
      have hright : rightEndpoint ∈ iterateMap T 0 '' U := by
        rw [hn]
        exact Set.mem_univ rightEndpoint
      rcases hright with ⟨x, hx, hxeq⟩
      have : x = rightEndpoint := by simpa [iterateMap] using hxeq
      subst x
      exact (lt_irrefl rightEndpoint) hx
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
    intro y
    have hy : y ∈ iterateMap T (k + 1) '' U := by
      rw [hn]
      exact Set.mem_univ y
    rcases hy with ⟨x, _hx, hxy⟩
    refine ⟨iterateMap T k x, ?_⟩
    simpa only [iterateMap, Function.iterate_succ_apply'] using hxy
  let midpoint : alphabet → I := fun edge =>
    ⟨((edge.1.lower : Real) + (edge.1.upper : Real)) / 2, by
      constructor
      · linarith [edge.1.lower.property.1, edge.1.upper.property.1]
      · linarith [edge.1.lower.property.2, edge.1.upper.property.2]⟩
  have hlower_mid (edge : alphabet) : edge.1.lower < midpoint edge := by
    change (edge.1.lower : Real) <
      ((edge.1.lower : Real) + (edge.1.upper : Real)) / 2
    have hlen := edge.1.length_pos
    simp only [DirectedMarkovEdge.length] at hlen
    linarith
  have hmid_upper (edge : alphabet) : midpoint edge < edge.1.upper := by
    change ((edge.1.lower : Real) + (edge.1.upper : Real)) / 2 <
      (edge.1.upper : Real)
    have hlen := edge.1.length_pos
    simp only [DirectedMarkovEdge.length] at hlen
    linarith
  have local_cover : ∀ edge : alphabet, ∃ d : Nat,
      iterateMap T d '' Set.Ioo edge.1.lower (midpoint edge) = Set.univ ∧
        iterateMap T d '' Set.Ioo (midpoint edge) edge.1.upper = Set.univ := by
    intro edge
    obtain ⟨n, hn⟩ := _hexact
      (Set.Ioo edge.1.lower (midpoint edge)) isOpen_Ioo
      (Set.nonempty_Ioo.mpr (hlower_mid edge))
    obtain ⟨m, hm⟩ := _hexact
      (Set.Ioo (midpoint edge) edge.1.upper) isOpen_Ioo
      (Set.nonempty_Ioo.mpr (hmid_upper edge))
    refine ⟨n + m, ?_, ?_⟩
    · apply Set.eq_univ_of_forall
      intro y
      obtain ⟨z, hz⟩ := IntervalMap.surjective_iterate honto m y
      have hzImage : z ∈ iterateMap T n ''
          Set.Ioo edge.1.lower (midpoint edge) := by
        rw [hn]
        exact Set.mem_univ z
      rcases hzImage with ⟨x, hx, hxz⟩
      refine ⟨x, hx, ?_⟩
      change (T^[n]) x = z at hxz
      change (T^[n + m]) x = y
      rw [show n + m = m + n by omega,
        Function.iterate_add_apply, hxz, hz]
    · apply Set.eq_univ_of_forall
      intro y
      obtain ⟨z, hz⟩ := IntervalMap.surjective_iterate honto n y
      have hzImage : z ∈ iterateMap T m ''
          Set.Ioo (midpoint edge) edge.1.upper := by
        rw [hm]
        exact Set.mem_univ z
      rcases hzImage with ⟨x, hx, hxz⟩
      refine ⟨x, hx, ?_⟩
      change (T^[m]) x = z at hxz
      change (T^[n + m]) x = y
      rw [Function.iterate_add_apply, hxz, hz]
  let localDepth : alphabet → Nat := fun edge =>
    Classical.choose (local_cover edge)
  have localDepth_spec (edge : alphabet) :
      iterateMap T (localDepth edge) ''
          Set.Ioo edge.1.lower (midpoint edge) = Set.univ ∧
        iterateMap T (localDepth edge) ''
          Set.Ioo (midpoint edge) edge.1.upper = Set.univ :=
    Classical.choose_spec (local_cover edge)
  let depth : Nat := 1 + alphabet.attach.sum localDepth
  have hdepth : 0 < depth := by simp [depth]
  refine ⟨depth, hdepth, ?_⟩
  intro sourceEdge targetEdge
  have hlocal_le_sum : localDepth sourceEdge ≤
      alphabet.attach.sum localDepth := by
    exact Finset.single_le_sum (s := alphabet.attach) (f := localDepth)
      (fun _ _ => Nat.zero_le _) (Finset.mem_attach alphabet sourceEdge)
  have hlocal_le : localDepth sourceEdge ≤ depth := by
    dsimp [depth]
    omega
  have pad_cover (U : Set I)
      (hU : iterateMap T (localDepth sourceEdge) '' U = Set.univ) :
      iterateMap T depth '' U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨z, hz⟩ := IntervalMap.surjective_iterate honto
      (depth - localDepth sourceEdge) y
    have hzImage : z ∈ iterateMap T (localDepth sourceEdge) '' U := by
      rw [hU]
      exact Set.mem_univ z
    rcases hzImage with ⟨x, hx, hxz⟩
    refine ⟨x, hx, ?_⟩
    change (T^[localDepth sourceEdge]) x = z at hxz
    change (T^[depth]) x = y
    rw [show depth = (depth - localDepth sourceEdge) +
        localDepth sourceEdge by omega,
      Function.iterate_add_apply, hxz, hz]
  have hleft := pad_cover
    (Set.Ioo sourceEdge.1.lower (midpoint sourceEdge))
    (localDepth_spec sourceEdge).1
  have hright := pad_cover
    (Set.Ioo (midpoint sourceEdge) sourceEdge.1.upper)
    (localDepth_spec sourceEdge).2
  cases hforward : sourceEdge.1.forward with
  | false =>
      have hxImage : targetEdge.1.source ∈ iterateMap T depth ''
          Set.Ioo (midpoint sourceEdge) sourceEdge.1.upper := by
        rw [hright]
        exact Set.mem_univ _
      have hyImage : targetEdge.1.target ∈ iterateMap T depth ''
          Set.Ioo sourceEdge.1.lower (midpoint sourceEdge) := by
        rw [hleft]
        exact Set.mem_univ _
      rcases hxImage with ⟨x, hx, hxmap⟩
      rcases hyImage with ⟨y, hy, hymap⟩
      refine ⟨x, y, ?_, hxmap, hymap⟩
      refine ⟨⟨hlower_mid sourceEdge |>.trans hx.1, hx.2⟩,
        ⟨hy.1, hy.2.trans (hmid_upper sourceEdge)⟩, ?_⟩
      simpa [hforward] using hy.2.trans hx.1
  | true =>
      have hxImage : targetEdge.1.source ∈ iterateMap T depth ''
          Set.Ioo sourceEdge.1.lower (midpoint sourceEdge) := by
        rw [hleft]
        exact Set.mem_univ _
      have hyImage : targetEdge.1.target ∈ iterateMap T depth ''
          Set.Ioo (midpoint sourceEdge) sourceEdge.1.upper := by
        rw [hright]
        exact Set.mem_univ _
      rcases hxImage with ⟨x, hx, hxmap⟩
      rcases hyImage with ⟨y, hy, hymap⟩
      refine ⟨x, y, ?_, hxmap, hymap⟩
      refine ⟨⟨hx.1, hx.2.trans (hmid_upper sourceEdge)⟩,
        ⟨(hlower_mid sourceEdge).trans hy.1, hy.2⟩, ?_⟩
      simpa [hforward] using hx.2.trans hy.1

/-- Proved adapter: a uniform crossing depth plus a complete decoder is
exactly a primitive substitution certificate. -/
theorem primitive_of_uniformCrossing_and_decoder
    {T : IntervalMap} {K : Finset I}
    {alphabet : OccurringDirectedAlphabet K}
    {sigma : Symbolic.Substitution alphabet}
    (hcross : ∃ depth : Nat, 0 < depth ∧
      ∀ sourceEdge targetEdge : alphabet,
        HasDirectedEdgeCrossing (iterateMap T depth)
          sourceEdge.1 targetEdge.1)
    (hdecoder : RecordsAllIteratedDirectedCrossings T alphabet sigma) :
    IsPrimitiveSubstitution sigma := by
  obtain ⟨depth, hdepth, hall⟩ := hcross
  exact ⟨depth, hdepth, fun sourceLetter targetLetter =>
    hdecoder depth sourceLetter targetLetter
      (hall sourceLetter targetLetter)⟩

/-- Exactness and the first powered decoder make the first induced
substitution primitive on the occurring alphabet. -/
theorem exactCoding_substitutionA_primitive
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (coding : ExactCommonRayCodingData K rayData seedData) :
    IsPrimitiveSubstitution coding.common.substitutionA := by
  exact primitive_of_uniformCrossing_and_decoder
    (exact_crosses_all_directed_edges_uniformly M.exact_A)
    (decoder_A_under_substitution_powers coding)

/-- Symmetric primitivity of the second induced substitution. -/
theorem exactCoding_substitutionB_primitive
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (coding : ExactCommonRayCodingData K rayData seedData) :
    IsPrimitiveSubstitution coding.common.substitutionB := by
  exact primitive_of_uniformCrossing_and_decoder
    (exact_crosses_all_directed_edges_uniformly M.exact_B)
    (decoder_B_under_substitution_powers coding)

/-! ## Primitive recurrence and the remaining Cobham boundary -/

/-- Existing checked primitive-substitution theory gives an explicit linear
factor-gap bound, so no general nonprimitive Durand--Rigo syndetic theorem is
needed in this branch. -/
theorem exactCoding_word_hasLinearFactorGaps
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (coding : ExactCommonRayCodingData K rayData seedData) :
    ∃ constant : Nat,
      Symbolic.HasLinearFactorGaps coding.common.word constant := by
  letI : Nonempty coding.common.alphabet :=
    coding.common.alphabet_nonempty.to_subtype
  exact Symbolic.Substitution.primitive_fixedPoint_hasLinearFactorGaps
    coding.common.fixedA
    (exactCoding_substitutionA_primitive coding)
    coding.common.growthA

/-- Proved conversion from the linear-gap result to the exact syndetic
predicate used by the Durand return-word layer. -/
theorem exactCoding_word_recurrentFactorsSyndetic
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (coding : ExactCommonRayCodingData K rayData seedData) :
    Symbolic.RecurrentFactorsSyndetic coding.common.word := by
  obtain ⟨constant, hgap⟩ := exactCoding_word_hasLinearFactorGaps coding
  have hlinear := Symbolic.isLinearlyRecurrent_of_hasLinearFactorGaps hgap
  intro word hword
  apply hlinear.2.1 word
  obtain ⟨start, _hstart, hfactor⟩ := hword 0
  exact ⟨start, hfactor⟩

/-- Powered Perron data exposed before the remaining symbolic comparison.
This is the precise growth dependency needed by the return-word argument. -/
structure PoweredPerronData
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} (data : CommonRayFixedWord A B K ray a b) where
  powerA : Nat
  powerB : Nat
  powerA_pos : 0 < powerA
  powerB_pos : 0 < powerB
  perron_A : IsPerronNumber (a ^ powerA)
  perron_B : IsPerronNumber (b ^ powerB)
  base_independent : MultiplicativelyIndependent a b
  powered_independent :
    MultiplicativelyIndependent (a ^ powerA) (b ^ powerB)
  dominant_A : IsDominantEigenvalue
    (data.substitutionA.power powerA).incidenceMatrix (a ^ powerA)
  dominant_B : IsDominantEigenvalue
    (data.substitutionB.power powerB).incidenceMatrix (b ^ powerB)
  prolongable_A : (data.substitutionA.power powerA).ProlongableOn data.seed
  prolongable_B : (data.substitutionB.power powerB).ProlongableOn data.seed
  generating_A : (data.substitutionA.power powerA).IsGeneratingLetter data.seed
  generating_B : (data.substitutionB.power powerB).IsGeneratingLetter data.seed
  fixed_A : (data.substitutionA.power powerA).IsFixedPoint data.word
  fixed_B : (data.substitutionB.power powerB).IsFixedPoint data.word
  grows_A : LetterImagesGrow (data.substitutionA.power powerA) data.seed
  grows_B : LetterImagesGrow (data.substitutionB.power powerB) data.seed

/-- Proved Perron-power adapter from the positive geometric length vectors. -/
theorem commonRay_has_poweredPerronData
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} (data : CommonRayFixedWord A B K ray a b)
    (hind : MultiplicativelyIndependent a b) :
    Nonempty (PoweredPerronData data) := by
  rcases common_ray_has_perron_powered_presentations data hind with
    ⟨u, v, hu, hv, hperronA, hperronB, hindPower,
      hdominantA, hdominantB, hprolongA, hprolongB,
      hgenerateA, hgenerateB, hfixedA, hfixedB, hgrowA, hgrowB⟩
  exact ⟨{
    powerA := u
    powerB := v
    powerA_pos := hu
    powerB_pos := hv
    perron_A := hperronA
    perron_B := hperronB
    base_independent := hind
    powered_independent := hindPower
    dominant_A := hdominantA
    dominant_B := hdominantB
    prolongable_A := hprolongA
    prolongable_B := hprolongB
    generating_A := hgenerateA
    generating_B := hgenerateB
    fixed_A := hfixedA
    fixed_B := hfixedB
    grows_A := hgrowA
    grows_B := hgrowB }⟩

/-- The two primitive return presentations placed on one recurrent core. -/
structure PrimitiveReturnComparisonInput
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} (data : CommonRayFixedWord A B K ray a b) where
  core : Symbolic.RecurrentCore data.word
  core_word_eq : core.word = data.word
  linearConstant : Nat
  linearlyRecurrent :
    Symbolic.IsLinearlyRecurrent core.word linearConstant
  powered : PoweredPerronData data
  leftReturn : Symbolic.PoweredReturnPresentation a core.word
  rightReturn : Symbolic.PoweredReturnPresentation b core.word

/-- Positive exact letter-metric scaling by a factor bigger than one forces
every iterated letter image to grow. -/
private theorem letterImagesGrow_of_positive_metric_scaling
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    {sigma : Symbolic.Substitution alpha} {length : alpha → Real}
    {scale : Real}
    (hlength : ∀ letter, 0 < length letter)
    (hscale : SubstitutionScalesLetterLengths sigma length scale)
    (hone : 1 < scale) (seed : alpha) :
    LetterImagesGrow sigma seed := by
  classical
  let total : Real := ∑ letter : alpha, length letter
  let chosen : alpha := Classical.choice inferInstance
  have hchosen_le : length chosen ≤ total := by
    dsimp [total]
    exact Finset.single_le_sum (fun letter _ => (hlength letter).le)
      (Finset.mem_univ chosen)
  have htotal_pos : 0 < total := (hlength chosen).trans_le hchosen_le
  have hupper : ∀ word : Symbolic.Word alpha,
      wordMetricLength length word ≤ (word.length : Real) * total := by
    intro word
    induction word with
    | nil => simp [wordMetricLength]
    | cons letter word ih =>
        have hletter_le : length letter ≤ total := by
          dsimp [total]
          exact Finset.single_le_sum
            (fun other _ => (hlength other).le)
            (Finset.mem_univ letter)
        simp only [wordMetricLength, List.map_cons, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        have htotal_nonneg : 0 ≤ total := htotal_pos.le
        change (word.map length).sum ≤
          (word.length : Real) * total at ih
        nlinarith
  intro bound
  have hevent : ∀ᶠ n : Nat in Filter.atTop,
      ((bound : Real) * total) / length seed < scale ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop _
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.1 hevent
  have hlarge := hcutoff cutoff le_rfl
  have hlarge' : (bound : Real) * total <
      scale ^ cutoff * length seed := by
    exact (div_lt_iff₀ (hlength seed)).mp hlarge
  refine ⟨cutoff, le_of_not_gt fun hshort => ?_⟩
  have hshortReal :
      ((sigma.iterateLetter cutoff seed).length : Real) < bound := by
    exact_mod_cast hshort
  have hmetricIter :=
    sigma.scalesLetterLengths_power hscale cutoff seed
  simp only [Symbolic.Substitution.power_apply] at hmetricIter
  have hmetricUpper := hupper (sigma.iterateLetter cutoff seed)
  rw [hmetricIter] at hmetricUpper
  have hmul := mul_lt_mul_of_pos_right hshortReal htotal_pos
  nlinarith

/-- The checked powered-return construction does not use its historical
aperiodicity parameter.  This local adapter exposes exactly the stronger
statement proved by that construction, so the periodic branch is not forced
to manufacture a false hypothesis. -/
private theorem poweredReturnPresentation_of_primitiveCore
    {gamma : Type*}
    [Fintype gamma] [DecidableEq gamma]
    {growth : Real} {x : Symbolic.InfiniteWord gamma}
    (core : Symbolic.PrimitiveRecurrentCore growth x) :
    Nonempty (Symbolic.PoweredReturnPresentation
      growth core.core.word) := by
  classical
  letI : Nonempty (Fin core.rank) :=
    ⟨⟨0, core.rank_pos⟩⟩
  obtain ⟨sourceConstant, hsourceGaps⟩ :=
    Symbolic.Substitution.primitive_fixedPoint_hasLinearFactorGaps
      core.fixed core.primitive core.images_grow
  have hsourceLinear : Symbolic.IsLinearlyRecurrent core.fixedWord
      (sourceConstant + 1) :=
    Symbolic.isLinearlyRecurrent_of_hasLinearFactorGaps hsourceGaps
  have hmarker : Symbolic.InfiniteFactorAt core.fixedWord
      [core.fixedWord.head] 0 := by
    simp [Symbolic.InfiniteFactorAt, Stream'.take_succ]
  obtain ⟨returnRank, ⟨sourceDecomposition⟩⟩ :=
    linearlyRecurrent_returnDecomposition
      hsourceLinear hmarker (by simp)
  letI : Nonempty (Fin returnRank) :=
    ⟨⟨0, sourceDecomposition.rank_pos⟩⟩
  obtain ⟨factorization⟩ :=
    Symbolic.Substitution.exists_returnSubstitutionFactorization
      core.fixed sourceDecomposition
  let rho := factorization.substitution
  let returnMetric : Fin returnRank → ℝ := fun letter =>
    wordMetricLength core.metric (sourceDecomposition.blocks letter)
  let returnScale := growth ^ core.exponent
  have hreturnMetricPos : ∀ letter : Fin returnRank,
      0 < returnMetric letter := by
    exact factorization.returnMetric_pos core.metric core.metric_pos
  have hreturnScale : SubstitutionScalesLetterLengths rho
      returnMetric returnScale := by
    exact factorization.scalesReturnMetric core.metric_scales
  have hreturnScaleOne : 1 < returnScale := by
    exact one_lt_pow₀ core.growth_gt_one core.exponent_pos.ne'
  have hreturnGrow : ∀ letter : Fin returnRank,
      LetterImagesGrow rho letter := by
    intro letter
    exact letterImagesGrow_of_positive_metric_scaling
      hreturnMetricPos hreturnScale hreturnScaleOne letter
  have hsourceUniform : Symbolic.IsUniformlyRecurrent core.fixedWord :=
    hsourceLinear.2.1
  have hderivedUniform :
      Symbolic.IsUniformlyRecurrent sourceDecomposition.derived :=
    sourceDecomposition.uniformlyRecurrent_derived hsourceUniform
  have hreturnPrimitive : ∃ iterate : Nat, 0 < iterate ∧
      ∀ left right : Fin returnRank,
        right ∈ rho.iterateLetter iterate left :=
    Symbolic.Substitution.primitive_of_fixed_uniform_all_images_grow
      factorization.fixed hderivedUniform
      sourceDecomposition.every_letter_occurs hreturnGrow
  let seed := sourceDecomposition.derived.head
  have hseedGrow : LetterImagesGrow rho seed := hreturnGrow seed
  have hprolongable : rho.ProlongableOn seed :=
    Symbolic.Substitution.prolongableOn_head_of_primitive_fixedPoint
      factorization.fixed hreturnPrimitive hseedGrow
  have hgenerating : rho.IsGeneratingLetter seed := by
    obtain ⟨iterate, _hiterate, hcontains⟩ := hreturnPrimitive
    intro letter
    exact ⟨iterate, hcontains seed letter⟩
  have hlengthEigen := substitution_metric_lengths_give_incidence_identity
    hreturnMetricPos hreturnScale
  have heigenTranspose : NatMatrixEigenvectorEquation
      rho.incidenceMatrix.transpose returnMetric returnScale := by
    intro source
    simpa [NatMatrixEigenvectorEquation, incidenceTransposeMul] using
      hlengthEigen.2 source
  have hdominantTranspose : IsDominantEigenvalue
      rho.incidenceMatrix.transpose returnScale :=
    positive_eigenvector_isDominant rho.incidenceMatrix.transpose
      returnMetric returnScale hreturnMetricPos heigenTranspose
  have hdominant : IsDominantEigenvalue rho.incidenceMatrix returnScale :=
    (dominantEigenvalue_transpose_iff rho.incidenceMatrix returnScale).mp
      hdominantTranspose
  let sourceMapped := sourceDecomposition.map_injective
    core.coding core.coding_injective
  let targetDecomposition :=
    Symbolic.Substitution.castReturnDecompositionWord
      core.coding_eq sourceMapped
  have htargetDerived : targetDecomposition.derived =
      sourceDecomposition.derived := by
    calc
      targetDecomposition.derived = sourceMapped.derived := by
        simp [targetDecomposition]
      _ = sourceDecomposition.derived := rfl
  exact ⟨{
    exponent := core.exponent
    exponent_pos := core.exponent_pos
    marker := core.coding.mapWord [core.fixedWord.head]
    rank := returnRank
    decomposition := targetDecomposition
    substitution := rho
    seed := seed
    prolongable := hprolongable
    generating := hgenerating
    fixed := by rw [htargetDerived]; exact factorization.fixed
    primitive := hreturnPrimitive
    every_letter_occurs := by
      intro letter
      rw [htargetDerived]
      exact sourceDecomposition.every_letter_occurs letter
    images_grow := hseedGrow
    dominant := by simpa [returnScale] using hdominant }⟩

/-- Relabel one positive power of a primitive common-word substitution onto
`Fin rank`, retaining the common recurrent core and deriving dominance from
the transported positive edge-length eigenvector. -/
private theorem primitiveCore_of_commonWord_power
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b growth : Real}
    (data : CommonRayFixedWord A B K ray a b)
    (core : Symbolic.RecurrentCore data.word)
    (hcoreWord : core.word = data.word)
    (sigma : Symbolic.Substitution data.alphabet)
    (exponent : Nat) (hexponent : 0 < exponent)
    (hgrowth : 1 < growth)
    (hprimitive : IsPrimitiveSubstitution sigma)
    (hfixed : (sigma.power exponent).IsFixedPoint data.word)
    (hprolongable : (sigma.power exponent).ProlongableOn data.seed)
    (hgenerating : (sigma.power exponent).IsGeneratingLetter data.seed)
    (himagesGrow : LetterImagesGrow (sigma.power exponent) data.seed)
    (hmetric : SubstitutionScalesLetterLengths
      sigma data.letterLength growth) :
    ∃ built : Symbolic.PrimitiveRecurrentCore growth data.word,
      built.core = core := by
  classical
  letI : Nonempty data.alphabet := data.alphabet_nonempty.to_subtype
  let rank := Fintype.card data.alphabet
  have hrank : 0 < rank := by
    exact Fintype.card_pos
  let equiv : data.alphabet ≃ Fin rank :=
    Fintype.equivFin data.alphabet
  let tau := (sigma.power exponent).relabel equiv
  let fixedWord : Symbolic.InfiniteWord (Fin rank) :=
    Symbolic.Substitution.relabelInfiniteWordPublic equiv data.word
  let coding : Symbolic.LetterCoding (Fin rank) data.alphabet :=
    ⟨equiv.symm⟩
  let metric : Fin rank → Real := fun letter =>
    data.letterLength (equiv.symm letter)
  have hmetricPos : ∀ letter : Fin rank, 0 < metric letter := by
    intro letter
    exact data.letterLength_pos (equiv.symm letter)
  have hmetricPower : SubstitutionScalesLetterLengths
      (sigma.power exponent) data.letterLength (growth ^ exponent) :=
    sigma.scalesLetterLengths_power hmetric exponent
  have hmetricTau : SubstitutionScalesLetterLengths
      tau metric (growth ^ exponent) := by
    exact (sigma.power exponent).relabel_scalesLetterLengths
      equiv data.letterLength (growth ^ exponent) hmetricPower
  letI : Nonempty (Fin rank) := ⟨⟨0, hrank⟩⟩
  have hlengthEigen := substitution_metric_lengths_give_incidence_identity
    hmetricPos hmetricTau
  have heigenTranspose : NatMatrixEigenvectorEquation
      tau.incidenceMatrix.transpose metric (growth ^ exponent) := by
    intro source
    simpa [NatMatrixEigenvectorEquation, incidenceTransposeMul] using
      hlengthEigen.2 source
  have hdominantTranspose : IsDominantEigenvalue
      tau.incidenceMatrix.transpose (growth ^ exponent) :=
    positive_eigenvector_isDominant tau.incidenceMatrix.transpose
      metric (growth ^ exponent) hmetricPos heigenTranspose
  have hdominant : IsDominantEigenvalue tau.incidenceMatrix
      (growth ^ exponent) :=
    (dominantEigenvalue_transpose_iff tau.incidenceMatrix
      (growth ^ exponent)).mp hdominantTranspose
  have hprimitivePower := sigma.primitive_power hprimitive hexponent
  refine ⟨{
    core := core
    growth_gt_one := hgrowth
    rank := rank
    rank_pos := hrank
    substitution := tau
    seed := equiv data.seed
    fixedWord := fixedWord
    coding := coding
    coding_injective := equiv.symm.injective
    exponent := exponent
    exponent_pos := hexponent
    primitive := (sigma.power exponent).relabel_primitive
      equiv hprimitivePower
    prolongable :=
      ((sigma.power exponent).relabel_prolongableOn_iff
        equiv data.seed).2 hprolongable
    generating :=
      ((sigma.power exponent).relabel_isGeneratingLetter_iff
        equiv data.seed).2 hgenerating
    fixed :=
      (Symbolic.Substitution.relabel_isFixedPoint_public_iff
        equiv (sigma.power exponent) data.word).2 hfixed
    every_letter_occurs := by
      intro letter
      obtain ⟨position, hposition⟩ :=
        data.every_letter_occurs (equiv.symm letter)
      exact ⟨position, by
        change equiv (data.word position) = letter
        rw [hposition, equiv.apply_symm_apply]⟩
    metric := metric
    metric_pos := hmetricPos
    metric_scales := hmetricTau
    images_grow :=
      (sigma.power exponent).relabel_letterImagesGrow
        equiv himagesGrow
    dominant := hdominant
    coding_eq := by
      rw [hcoreWord]
      funext position
      simp [coding, fixedWord, Symbolic.LetterCoding.mapInfinite,
        Symbolic.Substitution.relabelInfiniteWordPublic] }, ?_⟩
  rfl

/-- Leaf C0: relabel the two primitive occurring alphabets onto finite
alphabets, form the common recurrent core, and invoke the already checked
return-decomposition/induced-substitution constructors. -/
theorem primitiveCommonRay_has_returnComparisonInput
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} (data : CommonRayFixedWord A B K ray a b)
    (_primitiveA : IsPrimitiveSubstitution data.substitutionA)
    (_primitiveB : IsPrimitiveSubstitution data.substitutionB)
    (_powered : PoweredPerronData data) :
    Nonempty (PrimitiveReturnComparisonInput data) := by
  classical
  letI : Nonempty data.alphabet := data.alphabet_nonempty.to_subtype
  obtain ⟨gapConstant, hfactorGaps⟩ :=
    Symbolic.Substitution.primitive_fixedPoint_hasLinearFactorGaps
      data.fixedA _primitiveA data.growthA
  have hlinear : Symbolic.IsLinearlyRecurrent data.word
      (gapConstant + 1) :=
    Symbolic.isLinearlyRecurrent_of_hasLinearFactorGaps hfactorGaps
  let core : Symbolic.RecurrentCore data.word := {
    word := data.word
    same_language := by
      intro word
      constructor
      · intro hfactor cutoff
        obtain ⟨gap, _hgapPos, hgap⟩ := hlinear.2.1 word hfactor
        obtain ⟨offset, _hoffset, hoccurs⟩ := hgap cutoff
        exact ⟨cutoff + offset, by omega, hoccurs⟩
      · intro hrecurrent
        obtain ⟨position, _hposition, hfactor⟩ := hrecurrent 0
        exact ⟨position, hfactor⟩ }
  obtain ⟨leftCore, hleftCore⟩ :=
    primitiveCore_of_commonWord_power data core rfl
      data.substitutionA _powered.powerA _powered.powerA_pos
      data.one_lt_a _primitiveA _powered.fixed_A
      _powered.prolongable_A _powered.generating_A _powered.grows_A
      data.imageMetricA
  obtain ⟨rightCore, hrightCore⟩ :=
    primitiveCore_of_commonWord_power data core rfl
      data.substitutionB _powered.powerB _powered.powerB_pos
      data.one_lt_b _primitiveB _powered.fixed_B
      _powered.prolongable_B _powered.generating_B _powered.grows_B
      data.imageMetricB
  obtain ⟨leftReturn⟩ :=
    poweredReturnPresentation_of_primitiveCore leftCore
  obtain ⟨rightReturn⟩ :=
    poweredReturnPresentation_of_primitiveCore rightCore
  rw [hleftCore] at leftReturn
  rw [hrightCore] at rightReturn
  exact ⟨{
    core := core
    core_word_eq := rfl
    linearConstant := gapConstant + 1
    linearlyRecurrent := hlinear
    powered := _powered
    leftReturn := leftReturn
    rightReturn := rightReturn }⟩

/-! ### Arbitrary-prefix induced return substitutions -/

/-- The exact parsing of the image of every return block for an arbitrary
nonempty prefix marker.  This generalizes the checked singleton-head
`ReturnSubstitutionFactorization` interface without suppressing its source
substitution, boundary alignment, derived tiling, uniqueness, or nonerasing
facts. -/
structure PrefixReturnSubstitutionFactorization
    {alpha : Type*} (source : Symbolic.Substitution alpha)
    {fixedWord : Symbolic.InfiniteWord alpha}
    {marker : Symbolic.Word alpha} {rank : Nat}
    (decomposition : Symbolic.ReturnDecomposition
      fixedWord marker rank) where
  factor : Fin rank → Symbolic.Word (Fin rank)
  factor_decodes : ∀ letter : Fin rank,
    (factor letter).flatMap decomposition.blocks =
      source.mapWord (decomposition.blocks letter)
  factor_ne_nil : ∀ letter : Fin rank, factor letter ≠ []
  factor_unique : ∀ letter : Fin rank,
    ∀ letters : Symbolic.Word (Fin rank),
      letters.flatMap decomposition.blocks =
        source.mapWord (decomposition.blocks letter) →
      letters = factor letter
  boundary : Nat → Nat
  boundary_zero : boundary 0 = 0
  boundary_cut : ∀ position : Nat,
    decomposition.cut (boundary position) =
      Symbolic.Substitution.substitutedReturnCut
        source decomposition position
  boundary_succ : ∀ position : Nat,
    boundary (position + 1) = boundary position +
      (factor (decomposition.derived position)).length
  derived_factor_at : ∀ position : Nat,
    Symbolic.InfiniteFactorAt decomposition.derived
      (factor (decomposition.derived position)) (boundary position)

/-- The induced nonerasing substitution named by an arbitrary-prefix
factorization. -/
def PrefixReturnSubstitutionFactorization.substitution
    {alpha : Type*} {source : Symbolic.Substitution alpha}
    {fixedWord : Symbolic.InfiniteWord alpha}
    {marker : Symbolic.Word alpha} {rank : Nat}
    {decomposition : Symbolic.ReturnDecomposition fixedWord marker rank}
    (factorization : PrefixReturnSubstitutionFactorization
      source decomposition) : Symbolic.Substitution (Fin rank) where
  image := factorization.factor
  image_ne_nil := factorization.factor_ne_nil

/-- Every substituted return cut for an arbitrary prefix marker is again a
marker occurrence. -/
private theorem marker_at_substitutedReturnCut_of_prefix
    {alpha : Type*} {source : Symbolic.Substitution alpha}
    {fixedWord : Symbolic.InfiniteWord alpha}
    (hfixed : source.IsFixedPoint fixedWord)
    {marker : Symbolic.Word alpha} {rank : Nat}
    (decomposition : Symbolic.ReturnDecomposition
      fixedWord marker rank) (position : Nat) :
    Symbolic.InfiniteFactorAt fixedWord marker
      (Symbolic.Substitution.substitutedReturnCut
        source decomposition position) := by
  have hmappedAtZero :=
    Symbolic.Substitution.iterateWord_drop_take_at_fixed_positive hfixed
      (level := 1) (by omega) 0 marker.length
  have hmarkerZero : fixedWord.take marker.length = marker := by
    simpa [Symbolic.InfiniteFactorAt] using decomposition.marker_at_zero
  simp only [Stream'.drop_zero] at hmappedAtZero
  rw [hmarkerZero] at hmappedAtZero
  have hmappedZero : Symbolic.InfiniteFactorAt fixedWord
      (source.mapWord marker) 0 := by
    simpa [Symbolic.InfiniteFactorAt] using hmappedAtZero
  have hmappedEq : fixedWord.take (source.mapWord marker).length =
      source.mapWord marker := by
    simpa [Symbolic.InfiniteFactorAt] using hmappedZero
  have hprefix : marker <+: source.mapWord marker := by
    have hlength := source.length_le_mapWord_for_return marker
    have hpref := Stream'.take_prefix_take_left
      (a := fixedWord) (m := marker.length)
      (n := (source.mapWord marker).length) hlength
    rw [hmarkerZero, hmappedEq] at hpref
    exact hpref
  have hwhole :=
    Symbolic.Substitution.iterateWord_drop_take_at_fixed_positive hfixed
      (level := 1) (by omega) (decomposition.cut position) marker.length
  have hsource :
      (fixedWord.drop (decomposition.cut position)).take marker.length =
        marker := decomposition.marker_at_cut position
  rw [hsource] at hwhole
  have hfinite : Symbolic.FiniteFactorAt
      (source.mapWord marker) marker 0 := by
    refine ⟨by simpa using hprefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hprefix).symm
  simpa [Symbolic.Substitution.substitutedReturnCut] using
    hwhole.of_finiteFactorAt hfinite

/-- Proved arbitrary-prefix factorization constructor.  The proof is the
checked cut-alignment argument with the singleton-head marker lemma replaced
by `marker_at_substitutedReturnCut_of_prefix`. -/
theorem exists_prefixReturnSubstitutionFactorization
    {alpha : Type*} {source : Symbolic.Substitution alpha}
    {fixedWord : Symbolic.InfiniteWord alpha}
    (hfixed : source.IsFixedPoint fixedWord)
    {marker : Symbolic.Word alpha} {rank : Nat}
    (decomposition : Symbolic.ReturnDecomposition
      fixedWord marker rank) :
    Nonempty (PrefixReturnSubstitutionFactorization
      source decomposition) := by
  classical
  let boundary : Nat → Nat := fun position =>
    Classical.choose (decomposition.marker_occurrence_eq_cut
      (marker_at_substitutedReturnCut_of_prefix
        hfixed decomposition position))
  have hboundaryCut : ∀ position : Nat,
      decomposition.cut (boundary position) =
        Symbolic.Substitution.substitutedReturnCut
          source decomposition position := by
    intro position
    exact Classical.choose_spec (decomposition.marker_occurrence_eq_cut
      (marker_at_substitutedReturnCut_of_prefix
        hfixed decomposition position))
  have hsubZero : Symbolic.Substitution.substitutedReturnCut
      source decomposition 0 = 0 := by
    simp [Symbolic.Substitution.substitutedReturnCut,
      decomposition.cut_zero]
  have hboundaryZero : boundary 0 = 0 := by
    apply decomposition.cut_injective
    rw [hboundaryCut, hsubZero, decomposition.cut_zero]
  have hsubStrict : StrictMono
      (Symbolic.Substitution.substitutedReturnCut source decomposition) := by
    apply strictMono_nat_of_lt_succ
    intro position
    rw [Symbolic.Substitution.substitutedReturnCut_succ]
    exact Nat.lt_add_of_pos_right
      (List.length_pos_of_ne_nil
        (source.mapWord_ne_nil
          (decomposition.blocks_are_returns
            (decomposition.derived position)).2.1))
  have hboundaryStrict : StrictMono boundary := by
    intro left right hlr
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hboundaryCut, hboundaryCut]
    exact hsubStrict hlr
  let factorAt : Nat → Symbolic.Word (Fin rank) := fun position =>
    (decomposition.derived.drop (boundary position)).take
      (boundary (position + 1) - boundary position)
  have hfactorAtDecodes : ∀ position : Nat,
      (factorAt position).flatMap decomposition.blocks =
        source.mapWord
          (decomposition.blocks (decomposition.derived position)) := by
    intro position
    have hboundaryLe : boundary position ≤ boundary (position + 1) :=
      (hboundaryStrict (Nat.lt_succ_self position)).le
    have hdecode := decomposition.flatMap_drop_take_derived
      (boundary position) (boundary (position + 1) - boundary position)
    change (factorAt position).flatMap decomposition.blocks =
      (fixedWord.drop (decomposition.cut (boundary position))).take
        ((factorAt position).flatMap decomposition.blocks).length at hdecode
    have hcutAdd := decomposition.cut_add (boundary position)
      (boundary (position + 1) - boundary position)
    have hboundaryAdd : boundary position +
        (boundary (position + 1) - boundary position) =
        boundary (position + 1) := Nat.add_sub_of_le hboundaryLe
    rw [hboundaryAdd] at hcutAdd
    change decomposition.cut (boundary (position + 1)) =
      decomposition.cut (boundary position) +
        ((factorAt position).flatMap decomposition.blocks).length at hcutAdd
    have hsubSucc :=
      Symbolic.Substitution.substitutedReturnCut_succ
        source decomposition position
    rw [hboundaryCut, hboundaryCut] at hcutAdd
    have hlength : ((factorAt position).flatMap
        decomposition.blocks).length =
        (source.mapWord
          (decomposition.blocks
            (decomposition.derived position))).length := by
      omega
    rw [hboundaryCut, hlength] at hdecode
    exact hdecode.trans
      (Symbolic.Substitution.map_block_at_substitutedReturnCut
        hfixed decomposition position)
  let occurrence : Fin rank → Nat := fun letter =>
    Classical.choose (decomposition.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin rank,
      decomposition.derived (occurrence letter) = letter := by
    intro letter
    exact Classical.choose_spec
      (decomposition.every_letter_occurs letter)
  let factor : Fin rank → Symbolic.Word (Fin rank) := fun letter =>
    factorAt (occurrence letter)
  have hfactorDecodes : ∀ letter : Fin rank,
      (factor letter).flatMap decomposition.blocks =
        source.mapWord (decomposition.blocks letter) := by
    intro letter
    change (factorAt (occurrence letter)).flatMap decomposition.blocks = _
    rw [hfactorAtDecodes, hoccurrence]
  have hfactorAt : ∀ position : Nat,
      factor (decomposition.derived position) = factorAt position := by
    intro position
    apply Symbolic.flatMap_returnWords_injective
      decomposition.blocks_injective decomposition.blocks_are_returns
    exact (hfactorDecodes (decomposition.derived position)).trans
      (hfactorAtDecodes position).symm
  have hfactorNonempty : ∀ letter : Fin rank,
      factor letter ≠ [] := by
    intro letter hempty
    have hdecode := hfactorDecodes letter
    rw [hempty] at hdecode
    simp only [List.flatMap_nil] at hdecode
    exact source.mapWord_ne_nil
      (decomposition.blocks_are_returns letter).2.1 hdecode.symm
  have hfactorUnique : ∀ letter : Fin rank,
      ∀ letters : Symbolic.Word (Fin rank),
        letters.flatMap decomposition.blocks =
          source.mapWord (decomposition.blocks letter) →
        letters = factor letter := by
    intro letter letters hdecode
    apply Symbolic.flatMap_returnWords_injective
      decomposition.blocks_injective decomposition.blocks_are_returns
    exact hdecode.trans (hfactorDecodes letter).symm
  have hboundarySucc : ∀ position : Nat,
      boundary (position + 1) = boundary position +
        (factor (decomposition.derived position)).length := by
    intro position
    have hboundaryLe : boundary position ≤ boundary (position + 1) :=
      (hboundaryStrict (Nat.lt_succ_self position)).le
    rw [hfactorAt]
    change boundary (position + 1) = boundary position +
      ((decomposition.derived.drop (boundary position)).take
        (boundary (position + 1) - boundary position)).length
    simp only [Stream'.length_take]
    exact (Nat.add_sub_of_le hboundaryLe).symm
  have hderivedFactorAt : ∀ position : Nat,
      Symbolic.InfiniteFactorAt decomposition.derived
        (factor (decomposition.derived position))
        (boundary position) := by
    intro position
    rw [hfactorAt]
    simp [Symbolic.InfiniteFactorAt, factorAt]
  exact ⟨{
    factor := factor
    factor_decodes := hfactorDecodes
    factor_ne_nil := hfactorNonempty
    factor_unique := hfactorUnique
    boundary := boundary
    boundary_zero := hboundaryZero
    boundary_cut := hboundaryCut
    boundary_succ := hboundarySucc
    derived_factor_at := hderivedFactorAt }⟩

/-- The induced arbitrary-prefix return substitution fixes the displayed
derived word. -/
theorem PrefixReturnSubstitutionFactorization.fixed
    {alpha : Type*} {source : Symbolic.Substitution alpha}
    {fixedWord : Symbolic.InfiniteWord alpha}
    {marker : Symbolic.Word alpha} {rank : Nat}
    {decomposition : Symbolic.ReturnDecomposition fixedWord marker rank}
    (factorization : PrefixReturnSubstitutionFactorization
      source decomposition) :
    factorization.substitution.IsFixedPoint decomposition.derived := by
  have hboundaryLower : ∀ position : Nat,
      position ≤ factorization.boundary position := by
    intro position
    induction position with
    | zero => simp [factorization.boundary_zero]
    | succ position ih =>
        rw [factorization.boundary_succ]
        have hpositive : 0 <
            (factorization.factor
              (decomposition.derived position)).length :=
          List.length_pos_of_ne_nil
            (factorization.factor_ne_nil
              (decomposition.derived position))
        omega
  have hfiniteTiling : ∀ count : Nat,
      factorization.substitution.mapWord
          (decomposition.derived.take count) =
        decomposition.derived.take (factorization.boundary count) := by
    intro count
    induction count with
    | zero => simp [factorization.boundary_zero]
    | succ count ih =>
        have hfactorAt := factorization.derived_factor_at count
        change
          (decomposition.derived.drop
            (factorization.boundary count)).take
              (factorization.factor
                (decomposition.derived count)).length =
            factorization.factor
              (decomposition.derived count) at hfactorAt
        rw [Stream'.take_succ', Symbolic.Substitution.mapWord_append,
          Symbolic.Substitution.mapWord_cons,
          Symbolic.Substitution.mapWord_nil, List.append_nil, ih,
          factorization.boundary_succ, Stream'.take_add]
        exact congrArg
          (fun tail => decomposition.derived.take
            (factorization.boundary count) ++ tail) hfactorAt.symm
  rw [Symbolic.Substitution.IsFixedPoint]
  funext position
  let count := position + 1
  have hposition : position < factorization.boundary count := by
    have hbound := hboundaryLower count
    omega
  have hwordLength :
      (factorization.substitution.mapWord
        (decomposition.derived.take count)).length =
      factorization.boundary count := by
    rw [hfiniteTiling]
    simp
  have hmapPrefix :
      (factorization.substitution.mapInfinite
        decomposition.derived).take (factorization.boundary count) =
      factorization.substitution.mapWord
        (decomposition.derived.take count) := by
    rw [← hwordLength]
    calc
      (factorization.substitution.mapInfinite
          decomposition.derived).take
            (factorization.substitution.mapWord
              (decomposition.derived.take count)).length =
          (factorization.substitution.mapInfinite
            (decomposition.derived.take count ++ₛ
              decomposition.derived.drop count)).take
                (factorization.substitution.mapWord
                  (decomposition.derived.take count)).length := by
            rw [Stream'.append_take_drop]
      _ = (factorization.substitution.mapWord
              (decomposition.derived.take count) ++ₛ
            factorization.substitution.mapInfinite
              (decomposition.derived.drop count)).take
                (factorization.substitution.mapWord
                  (decomposition.derived.take count)).length := by
            rw [factorization.substitution.mapInfinite_append_stream]
      _ = factorization.substitution.mapWord
              (decomposition.derived.take count) := by
            simpa using Stream'.take_append_of_le_length
              (x := factorization.substitution.mapWord
                (decomposition.derived.take count))
              (a := factorization.substitution.mapInfinite
                (decomposition.derived.drop count))
              (n := (factorization.substitution.mapWord
                (decomposition.derived.take count)).length) le_rfl
  have hprefix :
      (factorization.substitution.mapInfinite
        decomposition.derived).take (factorization.boundary count) =
      decomposition.derived.take (factorization.boundary count) :=
    hmapPrefix.trans (hfiniteTiling count)
  have hleftIndex : position <
      ((factorization.substitution.mapInfinite
        decomposition.derived).take
          (factorization.boundary count)).length := by
    simpa using hposition
  have hrightIndex : position <
      (decomposition.derived.take
        (factorization.boundary count)).length := by
    simpa using hposition
  have hleftGet := Stream'.take_get
    (a := factorization.substitution.mapInfinite decomposition.derived)
    (m := position) (n := factorization.boundary count) hleftIndex
  have hrightGet := Stream'.take_get
    (a := decomposition.derived)
    (m := position) (n := factorization.boundary count) hrightIndex
  change Stream'.get
      (factorization.substitution.mapInfinite decomposition.derived)
        position = Stream'.get decomposition.derived position
  rw [← hleftGet, ← hrightGet]
  rw [← Option.some_inj, ← List.getElem?_eq_getElem,
    ← List.getElem?_eq_getElem]
  exact congrArg (fun word => word[position]?) hprefix

/-- Positive source-letter lengths induce positive return-block lengths. -/
theorem PrefixReturnSubstitutionFactorization.returnMetric_pos
    {alpha : Type*} {source : Symbolic.Substitution alpha}
    {fixedWord : Symbolic.InfiniteWord alpha}
    {marker : Symbolic.Word alpha} {rank : Nat}
    {decomposition : Symbolic.ReturnDecomposition fixedWord marker rank}
    (_factorization : PrefixReturnSubstitutionFactorization
      source decomposition)
    (length : alpha → Real) (hlength : ∀ letter, 0 < length letter) :
    ∀ letter : Fin rank,
      0 < wordMetricLength length (decomposition.blocks letter) := by
  intro letter
  exact Symbolic.Substitution.wordMetricLength_pos_of_ne_nil length hlength
    (decomposition.blocks_are_returns letter).2.1

/-- Exact source metric scaling descends through the arbitrary-prefix
decoding square. -/
theorem PrefixReturnSubstitutionFactorization.scalesReturnMetric
    {alpha : Type*} {source : Symbolic.Substitution alpha}
    {fixedWord : Symbolic.InfiniteWord alpha}
    {marker : Symbolic.Word alpha} {rank : Nat}
    {decomposition : Symbolic.ReturnDecomposition fixedWord marker rank}
    (factorization : PrefixReturnSubstitutionFactorization
      source decomposition)
    {length : alpha → Real} {scale : Real}
    (hscale : SubstitutionScalesLetterLengths source length scale) :
    SubstitutionScalesLetterLengths factorization.substitution
      (fun letter => wordMetricLength length
        (decomposition.blocks letter)) scale := by
  intro letter
  change wordMetricLength
      (fun other => wordMetricLength length (decomposition.blocks other))
      (factorization.factor letter) =
    scale * wordMetricLength length (decomposition.blocks letter)
  rw [Symbolic.Substitution.wordMetricLength_flatMap,
    factorization.factor_decodes]
  have hmapWord : ∀ word : Symbolic.Word alpha,
      wordMetricLength length (source.mapWord word) =
        scale * wordMetricLength length word := by
    intro word
    induction word with
    | nil => simp [wordMetricLength]
    | cons head tail ih =>
        rw [Symbolic.Substitution.mapWord_cons]
        have hhead := hscale head
        change (List.map length (source head)).sum =
          scale * length head at hhead
        have htail : (List.map length (source.mapWord tail)).sum =
            scale * (List.map length tail).sum := by
          simpa only [wordMetricLength] using ih
        simp only [wordMetricLength, List.map_append, List.sum_append,
          List.map_cons, List.sum_cons]
        rw [hhead, htail]
        ring
  exact hmapWord (decomposition.blocks letter)

/-- C1a infrastructure: a cofinal tower of nonempty prefix markers.  The
strict growth and prefix fields prevent the former constant-family
degeneracy. -/
structure CofinalPrefixMarkerTower
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    (input : PrimitiveReturnComparisonInput data) where
  marker : Nat → Symbolic.Word data.alphabet
  marker_eq_take : ∀ level : Nat,
    marker level = input.core.word.take (level + 1)
  marker_ne_nil : ∀ level : Nat, marker level ≠ []
  marker_at_zero : ∀ level : Nat,
    Symbolic.InfiniteFactorAt input.core.word (marker level) 0
  length_strictMono : StrictMono (fun level => (marker level).length)
  marker_prefix : ∀ {short long : Nat}, short < long →
    marker short <+: marker long
  length_cofinal : ∀ bound : Nat, ∃ level : Nat,
    bound ≤ (marker level).length

/-- Proved C1a reduction: the prefixes of lengths `level + 1` form the
required cofinal tower for every infinite word. -/
theorem exists_cofinalPrefixMarkerTower
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    (input : PrimitiveReturnComparisonInput data) :
    Nonempty (CofinalPrefixMarkerTower input) := by
  refine ⟨{
    marker := fun level => input.core.word.take (level + 1)
    marker_eq_take := fun _ => rfl
    marker_ne_nil := by
      intro level
      apply List.ne_nil_of_length_pos
      simp
    marker_at_zero := by
      intro level
      simp [Symbolic.InfiniteFactorAt]
    length_strictMono := by
      intro left right hlr
      simpa using hlr
    marker_prefix := by
      intro short long hlt
      exact Stream'.take_prefix_take_left
        (a := input.core.word) (m := short + 1) (n := long + 1) (by omega)
    length_cofinal := by
      intro bound
      exact ⟨bound, by simp⟩ }⟩

/-- The canonical return decomposition at every marker of the cofinal
tower.  It is shared by the two scale presentations. -/
structure ReturnDecompositionTower
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    (markers : CofinalPrefixMarkerTower input) where
  rank : Nat → Nat
  decomposition : ∀ level : Nat,
    Symbolic.ReturnDecomposition input.core.word
      (markers.marker level) (rank level)

/-- Proved C1b-base reduction: linear recurrence gives a finite return
alphabet and complete decomposition at each nonempty prefix marker. -/
theorem cofinalMarkers_have_returnDecompositionTower
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    (markers : CofinalPrefixMarkerTower input) :
    Nonempty (ReturnDecompositionTower markers) := by
  classical
  have existsDecomposition (level : Nat) :
      ∃ rank : Nat, Nonempty
        (Symbolic.ReturnDecomposition input.core.word
          (markers.marker level) rank) :=
    linearlyRecurrent_returnDecomposition input.linearlyRecurrent
      (markers.marker_at_zero level) (markers.marker_ne_nil level)
  let rank : Nat → Nat := fun level =>
    Classical.choose (existsDecomposition level)
  let decomposition : ∀ level : Nat,
      Symbolic.ReturnDecomposition input.core.word
        (markers.marker level) (rank level) := fun level =>
    Classical.choice (Classical.choose_spec (existsDecomposition level))
  exact ⟨{ rank := rank, decomposition := decomposition }⟩

/-- Induced powered substitutions at one fixed geometric growth scale, on
the exact shared decomposition at every marker level. -/
structure PoweredReturnTowerAtScale
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b growth : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    (decompositions : ReturnDecompositionTower markers)
    (source : Symbolic.Substitution data.alphabet) where
  exponent : Nat
  exponent_pos : 0 < exponent
  factorization : ∀ level : Nat,
    PrefixReturnSubstitutionFactorization source
      (decompositions.decomposition level)
  seed : ∀ level : Nat, Fin (decompositions.rank level)
  seed_is_head : ∀ level : Nat, seed level =
    (decompositions.decomposition level).derived.head
  prolongable : ∀ level : Nat,
    (factorization level).substitution.ProlongableOn (seed level)
  generating : ∀ level : Nat,
    (factorization level).substitution.IsGeneratingLetter (seed level)
  fixed : ∀ level : Nat,
    (factorization level).substitution.IsFixedPoint
      (decompositions.decomposition level).derived
  primitive : ∀ level : Nat,
    IsPrimitiveSubstitution (factorization level).substitution
  every_letter_occurs : ∀ level : Nat,
    ∀ letter : Fin (decompositions.rank level),
      Symbolic.Substitution.OccursInInfiniteWord letter
        (decompositions.decomposition level).derived
  images_grow : ∀ level : Nat,
    LetterImagesGrow (factorization level).substitution (seed level)
  dominant : ∀ level : Nat,
    IsDominantEigenvalue
      (factorization level).substitution.incidenceMatrix
      (growth ^ exponent)

/-- The level substitution, definitionally tied to its exact powered-source
block-decoding factorization. -/
def PoweredReturnTowerAtScale.substitution
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b growth : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    {decompositions : ReturnDecompositionTower markers}
    {source : Symbolic.Substitution data.alphabet}
    (tower : PoweredReturnTowerAtScale
      (growth := growth) decompositions source)
    (level : Nat) : Symbolic.Substitution
      (Fin (decompositions.rank level)) :=
  (tower.factorization level).substitution

/-- Proved metric/primitivity/Perron upgrade from the arbitrary-prefix
powered-source decoding interface. -/
theorem exists_poweredReturnTowerAtScale
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b growth : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    (decompositions : ReturnDecompositionTower markers)
    (source : Symbolic.Substitution data.alphabet)
    (exponent : Nat) (hexponent : 0 < exponent)
    (hgrowth : 1 < growth)
    (hfixed : source.IsFixedPoint input.core.word)
    (hmetric : SubstitutionScalesLetterLengths
      source data.letterLength (growth ^ exponent)) :
    Nonempty (PoweredReturnTowerAtScale
      (growth := growth) decompositions source) := by
  classical
  let factorization : ∀ level : Nat,
      PrefixReturnSubstitutionFactorization source
        (decompositions.decomposition level) := fun level =>
    Classical.choice (exists_prefixReturnSubstitutionFactorization
      hfixed (decompositions.decomposition level))
  let seed : ∀ level : Nat, Fin (decompositions.rank level) :=
    fun level => (decompositions.decomposition level).derived.head
  let returnMetric : ∀ level : Nat,
      Fin (decompositions.rank level) → Real := fun level letter =>
    wordMetricLength data.letterLength
      ((decompositions.decomposition level).blocks letter)
  have hreturnMetricPos : ∀ level : Nat,
      ∀ letter : Fin (decompositions.rank level),
        0 < returnMetric level letter := by
    intro level
    exact (factorization level).returnMetric_pos
      data.letterLength data.letterLength_pos
  have hreturnScale : ∀ level : Nat,
      SubstitutionScalesLetterLengths
        (factorization level).substitution (returnMetric level)
        (growth ^ exponent) := by
    intro level
    exact (factorization level).scalesReturnMetric hmetric
  have hscaleOne : 1 < growth ^ exponent :=
    one_lt_pow₀ hgrowth hexponent.ne'
  have hreturnGrow : ∀ level : Nat,
      ∀ letter : Fin (decompositions.rank level),
        LetterImagesGrow (factorization level).substitution letter := by
    intro level
    letI : Nonempty (Fin (decompositions.rank level)) :=
      ⟨⟨0, (decompositions.decomposition level).rank_pos⟩⟩
    intro letter
    exact letterImagesGrow_of_positive_metric_scaling
      (hreturnMetricPos level) (hreturnScale level) hscaleOne letter
  have hderivedUniform : ∀ level : Nat,
      Symbolic.IsUniformlyRecurrent
        (decompositions.decomposition level).derived := by
    intro level
    exact (decompositions.decomposition level).uniformlyRecurrent_derived
      input.linearlyRecurrent.2.1
  have hprimitive : ∀ level : Nat,
      IsPrimitiveSubstitution (factorization level).substitution := by
    intro level
    letI : Nonempty (Fin (decompositions.rank level)) :=
      ⟨⟨0, (decompositions.decomposition level).rank_pos⟩⟩
    exact Symbolic.Substitution.primitive_of_fixed_uniform_all_images_grow
      (factorization level).fixed (hderivedUniform level)
      (decompositions.decomposition level).every_letter_occurs
      (hreturnGrow level)
  have hprolongable : ∀ level : Nat,
      (factorization level).substitution.ProlongableOn (seed level) := by
    intro level
    exact Symbolic.Substitution.prolongableOn_head_of_primitive_fixedPoint
      (factorization level).fixed (hprimitive level)
      (hreturnGrow level (seed level))
  have hgenerating : ∀ level : Nat,
      (factorization level).substitution.IsGeneratingLetter
        (seed level) := by
    intro level letter
    obtain ⟨iterate, _hiterate, hcontains⟩ := hprimitive level
    exact ⟨iterate, hcontains (seed level) letter⟩
  have hdominant : ∀ level : Nat,
      IsDominantEigenvalue
        (factorization level).substitution.incidenceMatrix
        (growth ^ exponent) := by
    intro level
    letI : Nonempty (Fin (decompositions.rank level)) :=
      ⟨⟨0, (decompositions.decomposition level).rank_pos⟩⟩
    have hlengthEigen := substitution_metric_lengths_give_incidence_identity
      (hreturnMetricPos level) (hreturnScale level)
    have heigenTranspose : NatMatrixEigenvectorEquation
        (factorization level).substitution.incidenceMatrix.transpose
        (returnMetric level) (growth ^ exponent) := by
      intro sourceLetter
      simpa [NatMatrixEigenvectorEquation, incidenceTransposeMul] using
        hlengthEigen.2 sourceLetter
    have hdominantTranspose : IsDominantEigenvalue
        (factorization level).substitution.incidenceMatrix.transpose
        (growth ^ exponent) :=
      positive_eigenvector_isDominant
        (factorization level).substitution.incidenceMatrix.transpose
        (returnMetric level) (growth ^ exponent)
        (hreturnMetricPos level) heigenTranspose
    exact (dominantEigenvalue_transpose_iff
      (factorization level).substitution.incidenceMatrix
      (growth ^ exponent)).mp hdominantTranspose
  exact ⟨{
    exponent := exponent
    exponent_pos := hexponent
    factorization := factorization
    seed := seed
    seed_is_head := by
      intro level
      rfl
    prolongable := hprolongable
    generating := hgenerating
    fixed := fun level => (factorization level).fixed
    primitive := hprimitive
    every_letter_occurs := fun level =>
      (decompositions.decomposition level).every_letter_occurs
    images_grow := fun level => hreturnGrow level (seed level)
    dominant := hdominant }⟩

/-- Proved C1b-L assembly from the generic arbitrary-prefix factorization
and its separate metric/primitivity/Perron upgrade. -/
theorem exists_leftPoweredReturnTower
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    (decompositions : ReturnDecompositionTower markers) :
    Nonempty (PoweredReturnTowerAtScale (growth := a) decompositions
      (data.substitutionA.power input.powered.powerA)) := by
  have hfixed : (data.substitutionA.power input.powered.powerA).IsFixedPoint
      input.core.word := by
    rw [input.core_word_eq]
    exact input.powered.fixed_A
  exact exists_poweredReturnTowerAtScale decompositions
    (data.substitutionA.power input.powered.powerA)
    input.powered.powerA input.powered.powerA_pos data.one_lt_a hfixed
    (data.substitutionA.scalesLetterLengths_power
      data.imageMetricA input.powered.powerA)

/-- Proved C1b-R assembly from the same generic arbitrary-prefix interface. -/
theorem exists_rightPoweredReturnTower
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    (decompositions : ReturnDecompositionTower markers) :
    Nonempty (PoweredReturnTowerAtScale (growth := b) decompositions
      (data.substitutionB.power input.powered.powerB)) := by
  have hfixed : (data.substitutionB.power input.powered.powerB).IsFixedPoint
      input.core.word := by
    rw [input.core_word_eq]
    exact input.powered.fixed_B
  exact exists_poweredReturnTowerAtScale decompositions
    (data.substitutionB.power input.powered.powerB)
    input.powered.powerB input.powered.powerB_pos data.one_lt_b hfixed
    (data.substitutionB.scalesLetterLengths_power
      data.imageMetricB input.powered.powerB)

/-- Every pair of strictly nested marker levels carries the complete unique
decoding of long return blocks into short return blocks. -/
structure NestedReturnTower
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    (decompositions : ReturnDecompositionTower markers) where
  factorization : ∀ {short long : Nat}, short < long →
    Symbolic.NestedReturnFactorization
      (decompositions.decomposition short)
      (decompositions.decomposition long)

/-- Proved C1c reduction to the checked marker-alignment and unique nested
return-factorization API. -/
theorem returnDecompositionTower_has_nestedFactorizations
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    (decompositions : ReturnDecompositionTower markers) :
    Nonempty (NestedReturnTower decompositions) := by
  classical
  exact ⟨{
    factorization := fun {short long} hlt =>
      Classical.choice (Symbolic.exists_nestedReturnFactorization
        (decompositions.decomposition short)
        (decompositions.decomposition long)
        (markers.marker_prefix hlt)) }⟩

/-- Exact same-source intertwining supplied by a nested return decoder.
This is the generic word equation that the four aligned refinement maps
actually satisfy; it does not assert a cross-source intertwining. -/
theorem prefixReturnSubstitutions_intertwine_nestedFactorization
    {alpha : Type*} {source : Symbolic.Substitution alpha}
    {fixedWord : Symbolic.InfiniteWord alpha}
    {shortMarker longMarker : Symbolic.Word alpha}
    {shortRank longRank : Nat}
    {short : Symbolic.ReturnDecomposition
      fixedWord shortMarker shortRank}
    {long : Symbolic.ReturnDecomposition
      fixedWord longMarker longRank}
    (shortFactorization : PrefixReturnSubstitutionFactorization
      source short)
    (longFactorization : PrefixReturnSubstitutionFactorization
      source long)
    (nested : Symbolic.NestedReturnFactorization short long)
    (letter : Fin longRank) :
    shortFactorization.substitution.mapWord (nested.factor letter) =
      (longFactorization.substitution letter).flatMap nested.factor := by
  have hshortDecode : ∀ letters : Symbolic.Word (Fin shortRank),
      (shortFactorization.substitution.mapWord letters).flatMap short.blocks =
        source.mapWord (letters.flatMap short.blocks) := by
    intro letters
    induction letters with
    | nil => simp
    | cons head tail ih =>
        rw [Symbolic.Substitution.mapWord_cons, List.flatMap_append]
        change
          (shortFactorization.factor head).flatMap short.blocks ++
              (shortFactorization.substitution.mapWord tail).flatMap
                short.blocks =
            source.mapWord
              (short.blocks head ++ tail.flatMap short.blocks)
        rw [shortFactorization.factor_decodes,
          Symbolic.Substitution.mapWord_append, ih]
  have hnestedDecode : ∀ letters : Symbolic.Word (Fin longRank),
      (letters.flatMap nested.factor).flatMap short.blocks =
        letters.flatMap long.blocks := by
    intro letters
    induction letters with
    | nil => simp
    | cons head tail ih =>
        simp only [List.flatMap_cons, List.flatMap_append]
        rw [nested.factor_decodes, ih]
  apply Symbolic.flatMap_returnWords_injective
    short.blocks_injective short.blocks_are_returns
  change
    (shortFactorization.substitution.mapWord
        (nested.factor letter)).flatMap short.blocks =
      ((longFactorization.factor letter).flatMap
        nested.factor).flatMap short.blocks
  rw [hshortDecode, nested.factor_decodes, hnestedDecode,
    longFactorization.factor_decodes]

/-- C1d's quantitative payload.  Aperiodicity and linear recurrence give a
uniform rank bound; the two induced scale towers also have uniformly bounded
letter-image lengths. -/
structure UniformReturnTowerBounds
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    {decompositions : ReturnDecompositionTower markers}
    (left : PoweredReturnTowerAtScale (growth := a) decompositions
      (data.substitutionA.power input.powered.powerA))
    (right : PoweredReturnTowerAtScale (growth := b) decompositions
      (data.substitutionB.power input.powered.powerB)) where
  core_aperiodic : ¬ Symbolic.IsPeriodic input.core.word
  rankBound : Nat
  rankBound_pos : 0 < rankBound
  rank_le : ∀ level : Nat, decompositions.rank level ≤ rankBound
  leftImageLengthBound : Nat
  leftImageLengthBound_pos : 0 < leftImageLengthBound
  left_image_length_le : ∀ level : Nat,
    ∀ letter : Fin (decompositions.rank level),
      (left.substitution level letter).length ≤ leftImageLengthBound
  rightImageLengthBound : Nat
  rightImageLengthBound_pos : 0 < rightImageLengthBound
  right_image_length_le : ∀ level : Nat,
    ∀ letter : Fin (decompositions.rank level),
      (right.substitution level letter).length ≤ rightImageLengthBound

/-- Summing the aperiodic lower bound for return blocks over a coded word.
This is the cancellation estimate used in both quantitative parts of C1d. -/
private theorem word_length_mul_marker_le_decoded_length_b9
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    {word : Symbolic.InfiniteWord alphabet} {constant : Nat}
    (hlinear : Symbolic.IsLinearlyRecurrent word constant)
    (haperiodic : ¬ Symbolic.IsPeriodic word)
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (letters : Symbolic.Word (Fin rank)) :
    letters.length * marker.length ≤
      constant * (letters.flatMap decomposition.blocks).length := by
  induction letters with
  | nil => simp
  | cons letter tail ih =>
      have hblock : marker.length ≤
          constant * (decomposition.blocks letter).length :=
        linearlyRecurrent_returnWord_lowerBound hlinear haperiodic
          (decomposition.blocks_are_returns letter)
      rw [List.length_cons, List.flatMap_cons, List.length_append,
        Nat.add_mul]
      calc
        tail.length * marker.length + 1 * marker.length ≤
            constant * (tail.flatMap decomposition.blocks).length +
              constant * (decomposition.blocks letter).length :=
          Nat.add_le_add ih (by simpa using hblock)
        _ = constant * ((decomposition.blocks letter).length +
              (tail.flatMap decomposition.blocks).length) := by
          simp only [Nat.mul_add]
          omega

/-- The image of an induced return substitution is uniformly bounded in
terms of the recurrence constant and the largest one-step source image. -/
private theorem prefixReturnFactorization_image_length_le_b9
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    {word : Symbolic.InfiniteWord alphabet} {constant : Nat}
    (hlinear : Symbolic.IsLinearlyRecurrent word constant)
    (haperiodic : ¬ Symbolic.IsPeriodic word)
    (source : Symbolic.Substitution alphabet)
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (factorization : PrefixReturnSubstitutionFactorization
      source decomposition) (letter : Fin rank) :
    (factorization.substitution letter).length ≤
      constant * (source.maxIterateLength 1 * constant) := by
  have hdecodedLower := word_length_mul_marker_le_decoded_length_b9
    hlinear haperiodic decomposition (factorization.factor letter)
  rw [factorization.factor_decodes] at hdecodedLower
  have hsourceUpper :
      (source.mapWord (decomposition.blocks letter)).length ≤
        source.maxIterateLength 1 *
          (decomposition.blocks letter).length := by
    simpa [Symbolic.Substitution.iterateWord] using
      source.iterateWord_length_le_maxIterateLength 1
        (decomposition.blocks letter)
  have hblockUpper : (decomposition.blocks letter).length ≤
      constant * marker.length :=
    hlinear.2.2 marker (decomposition.blocks letter)
      (decomposition.blocks_are_returns letter)
  have hproduct : (factorization.substitution letter).length *
        marker.length ≤
      (constant * (source.maxIterateLength 1 * constant)) *
        marker.length := by
    change (factorization.factor letter).length * marker.length ≤ _
    calc
      (factorization.factor letter).length * marker.length ≤
          constant *
            (source.mapWord (decomposition.blocks letter)).length :=
        hdecodedLower
      _ ≤ constant *
            (source.maxIterateLength 1 *
              (decomposition.blocks letter).length) :=
        Nat.mul_le_mul_left _ hsourceUpper
      _ ≤ constant *
            (source.maxIterateLength 1 *
              (constant * marker.length)) :=
        Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ hblockUpper)
      _ = (constant * (source.maxIterateLength 1 * constant)) *
            marker.length := by
        simp only [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right hproduct
    (List.length_pos_of_ne_nil decomposition.marker_ne_nil)

/-- Return types can be packed into a common late window.  The upper return
bound controls the physical window, while the lower return bound controls
how many distinct cuts it contains. -/
private theorem linearlyRecurrent_returnDecomposition_rank_le_b9
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    {word : Symbolic.InfiniteWord alphabet} {constant : Nat}
    (hlinear : Symbolic.IsLinearlyRecurrent word constant)
    (haperiodic : ¬ Symbolic.IsPeriodic word)
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (decomposition : Symbolic.ReturnDecomposition word marker rank) :
    rank ≤ constant * (constant * (constant + 1)) + 1 := by
  classical
  let occurrence : Fin rank → Nat := fun letter =>
    Classical.choose (decomposition.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin rank,
      decomposition.derived (occurrence letter) = letter := by
    intro letter
    exact Classical.choose_spec
      (decomposition.every_letter_occurs letter)
  let baseline : Nat := ∑ letter : Fin rank, occurrence letter
  have hoccurrenceLe : ∀ letter : Fin rank,
      occurrence letter ≤ baseline := by
    intro letter
    dsimp [baseline]
    exact Finset.single_le_sum (fun candidate _ => Nat.zero_le _)
      (Finset.mem_univ letter)
  let offsetBound := constant * (constant * (constant + 1))
  have hnear : ∀ letter : Fin rank,
      ∃ index : Nat, baseline ≤ index ∧
        index - baseline ≤ offsetBound ∧
        decomposition.derived index = letter := by
    intro letter
    have hpriorCut : decomposition.cut (occurrence letter) ≤
        decomposition.cut baseline :=
      decomposition.cut_strictMono.monotone (hoccurrenceLe letter)
    have hprior : Symbolic.InfiniteFactorAt word
        (decomposition.blocks letter ++ marker)
        (decomposition.cut (occurrence letter)) := by
      have hat := decomposition.block_marker_at_cut (occurrence letter)
      rw [hoccurrence letter] at hat
      exact hat
    have hfactorNonempty : decomposition.blocks letter ++ marker ≠ [] :=
      List.append_ne_nil_of_left_ne_nil
        (decomposition.blocks_are_returns letter).2.1 marker
    obtain ⟨physicalPosition, hphysicalLower, hphysicalUpper,
        hfactor⟩ :=
      hlinear.nextOccurrence hfactorNonempty hpriorCut hprior
    obtain ⟨index, hcutIndex, hderived⟩ :=
      decomposition.block_marker_occurrence_aligns letter hfactor
    have hbaselineIndex : baseline ≤ index := by
      apply decomposition.cut_strictMono.le_iff_le.mp
      rw [hcutIndex]
      exact hphysicalLower
    let offset := index - baseline
    have hindexEq : baseline + offset = index := by
      exact Nat.add_sub_of_le hbaselineIndex
    have hblockUpper : (decomposition.blocks letter).length ≤
        constant * marker.length :=
      hlinear.2.2 marker (decomposition.blocks letter)
        (decomposition.blocks_are_returns letter)
    have hfactorLength :
        (decomposition.blocks letter ++ marker).length ≤
          (constant + 1) * marker.length := by
      simp only [List.length_append, Nat.add_mul, one_mul]
      exact Nat.add_le_add_right hblockUpper marker.length
    have hcutUpper : decomposition.cut index ≤
        decomposition.cut baseline +
          constant * ((constant + 1) * marker.length) := by
      rw [hcutIndex]
      exact hphysicalUpper.trans
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left constant hfactorLength) _)
    let coded :=
      (decomposition.derived.drop baseline).take offset
    have hcodedLength : coded.length = offset := by
      simp [coded]
    have hdecodedLower := word_length_mul_marker_le_decoded_length_b9
      hlinear haperiodic decomposition coded
    rw [hcodedLength] at hdecodedLower
    have hcutAdd := decomposition.cut_add baseline offset
    rw [hindexEq] at hcutAdd
    have hdecodedUpper : (coded.flatMap decomposition.blocks).length ≤
        constant * ((constant + 1) * marker.length) := by
      change ((decomposition.derived.drop baseline).take offset |>.flatMap
        decomposition.blocks).length ≤ _
      rw [hcutAdd] at hcutUpper
      omega
    have hoffsetProduct : offset * marker.length ≤
        offsetBound * marker.length := by
      calc
        offset * marker.length ≤
            constant * (coded.flatMap decomposition.blocks).length :=
          hdecodedLower
        _ ≤ constant *
              (constant * ((constant + 1) * marker.length)) :=
          Nat.mul_le_mul_left constant hdecodedUpper
        _ = offsetBound * marker.length := by
          simp only [offsetBound, Nat.mul_assoc]
    have hoffset : offset ≤ offsetBound :=
      Nat.le_of_mul_le_mul_right hoffsetProduct
        (List.length_pos_of_ne_nil decomposition.marker_ne_nil)
    exact ⟨index, hbaselineIndex, by simpa [offset] using hoffset,
      hderived⟩
  let selectedIndex : Fin rank → Nat := fun letter =>
    Classical.choose (hnear letter)
  have hselectedLower : ∀ letter : Fin rank,
      baseline ≤ selectedIndex letter := by
    intro letter
    exact (Classical.choose_spec (hnear letter)).1
  have hselectedOffset : ∀ letter : Fin rank,
      selectedIndex letter - baseline ≤ offsetBound := by
    intro letter
    exact (Classical.choose_spec (hnear letter)).2.1
  have hselectedDerived : ∀ letter : Fin rank,
      decomposition.derived (selectedIndex letter) = letter := by
    intro letter
    exact (Classical.choose_spec (hnear letter)).2.2
  let encode : Fin rank → Fin (offsetBound + 1) := fun letter =>
    ⟨selectedIndex letter - baseline, by
      have := hselectedOffset letter
      omega⟩
  have hencode : Function.Injective encode := by
    intro leftLetter rightLetter heq
    have hoffsetEq := congrArg Fin.val heq
    have hindexEq : selectedIndex leftLetter =
        selectedIndex rightLetter := by
      have hleft := hselectedLower leftLetter
      have hright := hselectedLower rightLetter
      change selectedIndex leftLetter - baseline =
        selectedIndex rightLetter - baseline at hoffsetEq
      omega
    have hleftDerived := hselectedDerived leftLetter
    have hrightDerived := hselectedDerived rightLetter
    rw [hindexEq] at hleftDerived
    exact hleftDerived.symm.trans hrightDerived
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [offsetBound] using hcard

/-- Leaf C1d: the standard linearly-recurrent return-word estimates give
uniform rank and induced-image bounds on the aperiodic tower. -/
theorem returnTowers_have_uniformBounds
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    {decompositions : ReturnDecompositionTower markers}
    (left : PoweredReturnTowerAtScale (growth := a) decompositions
      (data.substitutionA.power input.powered.powerA))
    (right : PoweredReturnTowerAtScale (growth := b) decompositions
      (data.substitutionB.power input.powered.powerB))
    (_notPeriodicLanguage :
      ¬ Symbolic.HasPeriodicRecurrentLanguage data.word) :
    Nonempty (UniformReturnTowerBounds left right) := by
  classical
  have hcoreAperiodic : ¬ Symbolic.IsPeriodic input.core.word := by
    intro hperiodic
    exact _notPeriodicLanguage
      (input.core.hasPeriodicRecurrentLanguage hperiodic)
  let recurrenceConstant := input.linearConstant
  let rankBound := recurrenceConstant *
    (recurrenceConstant * (recurrenceConstant + 1)) + 1
  let leftImageLengthBound := recurrenceConstant *
    ((data.substitutionA.power input.powered.powerA).maxIterateLength 1 *
      recurrenceConstant) + 1
  let rightImageLengthBound := recurrenceConstant *
    ((data.substitutionB.power input.powered.powerB).maxIterateLength 1 *
      recurrenceConstant) + 1
  refine ⟨{
    core_aperiodic := hcoreAperiodic
    rankBound := rankBound
    rankBound_pos := by simp [rankBound]
    rank_le := ?_
    leftImageLengthBound := leftImageLengthBound
    leftImageLengthBound_pos := by simp [leftImageLengthBound]
    left_image_length_le := ?_
    rightImageLengthBound := rightImageLengthBound
    rightImageLengthBound_pos := by simp [rightImageLengthBound]
    right_image_length_le := ?_ }⟩
  · intro level
    simpa [rankBound, recurrenceConstant] using
      linearlyRecurrent_returnDecomposition_rank_le_b9
        input.linearlyRecurrent hcoreAperiodic
        (decompositions.decomposition level)
  · intro level letter
    have hbound := prefixReturnFactorization_image_length_le_b9
      input.linearlyRecurrent hcoreAperiodic
      (data.substitutionA.power input.powered.powerA)
      (decompositions.decomposition level) (left.factorization level) letter
    exact hbound.trans (Nat.le_add_right _ 1)
  · intro level letter
    have hbound := prefixReturnFactorization_image_length_le_b9
      input.linearlyRecurrent hcoreAperiodic
      (data.substitutionB.power input.powered.powerB)
      (decompositions.decomposition level) (right.factorization level) letter
    exact hbound.trans (Nat.le_add_right _ 1)

/-- The complete tower infrastructure consumed by the finite-coding and
alignment stages. -/
structure ReturnTowerInfrastructure
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    (input : PrimitiveReturnComparisonInput data) where
  markers : CofinalPrefixMarkerTower input
  decompositions : ReturnDecompositionTower markers
  left : PoweredReturnTowerAtScale (growth := a) decompositions
    (data.substitutionA.power input.powered.powerA)
  right : PoweredReturnTowerAtScale (growth := b) decompositions
    (data.substitutionB.power input.powered.powerB)
  nested : NestedReturnTower decompositions
  bounds : UniformReturnTowerBounds left right

/-- Equality of two levels after a bijective renaming.  The seed, complete
derived stream, and induced substitution are all part of the key. -/
def ReturnTowerLevelsEquivalent
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b growth : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    {decompositions : ReturnDecompositionTower markers}
    {source : Symbolic.Substitution data.alphabet}
    (tower : PoweredReturnTowerAtScale (growth := growth)
      decompositions source)
    (leftLevel rightLevel : Nat) : Prop :=
  ∃ relabel : Fin (decompositions.rank leftLevel) ≃
      Fin (decompositions.rank rightLevel),
    relabel (tower.seed leftLevel) = tower.seed rightLevel ∧
    (∀ position : Nat,
      relabel ((decompositions.decomposition leftLevel).derived position) =
        (decompositions.decomposition rightLevel).derived position) ∧
    ∀ letter : Fin (decompositions.rank leftLevel),
      (tower.substitution leftLevel letter).map relabel =
        tower.substitution rightLevel (relabel letter)

/-- A finite code for the two genuinely cofinal derived-system towers. -/
structure FiniteReturnSystemFamily
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    (input : PrimitiveReturnComparisonInput data) where
  infrastructure : ReturnTowerInfrastructure input
  leftClassCount : Nat
  rightClassCount : Nat
  leftClassCount_pos : 0 < leftClassCount
  rightClassCount_pos : 0 < rightClassCount
  leftCode : Nat → Fin leftClassCount
  rightCode : Nat → Fin rightClassCount
  left_same_code : ∀ i j : Nat, leftCode i = leftCode j →
    ReturnTowerLevelsEquivalent infrastructure.left i j
  right_same_code : ∀ i j : Nat, rightCode i = rightCode j →
    ReturnTowerLevelsEquivalent infrastructure.right i j

/-- Two fixed points of the same substitution agree when they have the same
head and that head has unbounded iterated images. -/
private theorem fixedPoints_eq_of_head_and_growth_b9
    {alphabet : Type*} {substitution : Symbolic.Substitution alphabet}
    {leftWord rightWord : Symbolic.InfiniteWord alphabet}
    (hleftFixed : substitution.IsFixedPoint leftWord)
    (hrightFixed : substitution.IsFixedPoint rightWord)
    (hhead : leftWord.head = rightWord.head)
    (hgrow : LetterImagesGrow substitution leftWord.head) :
    leftWord = rightWord := by
  apply Stream'.ext
  intro position
  obtain ⟨level, hlevel⟩ := hgrow (position + 1)
  have hposition : position <
      (substitution.iterateLetter level leftWord.head).length := by
    omega
  have hleftPrefix :=
    Symbolic.Substitution.iterateLetter_eq_take_of_fixedPoint
      hleftFixed rfl level
  have hrightPrefix :=
    Symbolic.Substitution.iterateLetter_eq_take_of_fixedPoint
      hrightFixed rfl level
  rw [← hhead] at hrightPrefix
  have hleftGet := Stream'.take_get
    (a := leftWord) (m := position)
    (n := (substitution.iterateLetter level leftWord.head).length)
    (by simpa [← hleftPrefix] using hposition)
  have hrightGet := Stream'.take_get
    (a := rightWord) (m := position)
    (n := (substitution.iterateLetter level leftWord.head).length)
    (by simpa [← hrightPrefix] using hposition)
  rw [← hleftGet, ← hrightGet, ← Option.some_inj,
    ← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem,
    ← hleftPrefix, ← hrightPrefix]

/-- A common finite table format for a varying-rank return system.  The
rank, distinguished seed, actual fixed-word head, and every bounded image
entry are retained. -/
private structure ReturnTowerFiniteCode (rankBound imageBound : Nat) where
  rankTag : Fin (rankBound + 1)
  seedTag : Fin rankBound
  headTag : Fin rankBound
  imageTable : Fin rankBound → Fin imageBound → Option (Fin rankBound)

private noncomputable instance (rankBound imageBound : Nat) :
    Fintype (ReturnTowerFiniteCode rankBound imageBound) := by
  classical
  let target := Fin (rankBound + 1) × Fin rankBound × Fin rankBound ×
    (Fin rankBound → Fin imageBound → Option (Fin rankBound))
  let encode : ReturnTowerFiniteCode rankBound imageBound → target :=
    fun value =>
      (value.rankTag, value.seedTag, value.headTag, value.imageTable)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftRank, leftSeed, leftHead, leftTable⟩
    rcases right with ⟨rightRank, rightSeed, rightHead, rightTable⟩
    have hrank : leftRank = rightRank :=
      congrArg (fun value : target => value.1) heq
    have hseed : leftSeed = rightSeed :=
      congrArg (fun value : target => value.2.1) heq
    have hhead : leftHead = rightHead :=
      congrArg (fun value : target => value.2.2.1) heq
    have htable : leftTable = rightTable :=
      congrArg (fun value : target => value.2.2.2) heq
    subst rightRank
    subst rightSeed
    subst rightHead
    subst rightTable
    rfl)

private theorem substitution_eq_of_images_c1e_b9
    {alphabet : Type*} (left right : Symbolic.Substitution alphabet)
    (himages : ∀ letter, left letter = right letter) : left = right := by
  cases left with
  | mk leftImage leftNonempty =>
      cases right with
      | mk rightImage rightNonempty =>
          have himage : leftImage = rightImage := by
            funext letter
            exact himages letter
          subst rightImage
          rfl

/-- Bounded ranks and bounded images give a finite code for one powered
return tower.  Equal codes recover literal equality after the rank equality
has identified the two `Fin` alphabets. -/
private theorem poweredReturnTower_has_finiteCoding_b9
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b growth : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {markers : CofinalPrefixMarkerTower input}
    {decompositions : ReturnDecompositionTower markers}
    {source : Symbolic.Substitution data.alphabet}
    (tower : PoweredReturnTowerAtScale (growth := growth)
      decompositions source)
    (rankBound imageBound : Nat)
    (hrank : ∀ level, decompositions.rank level ≤ rankBound)
    (himage : ∀ level letter,
      (tower.substitution level letter).length ≤ imageBound) :
    ∃ codeCount : Nat, ∃ code : Nat → Fin codeCount,
      0 < codeCount ∧
      ∀ leftLevel rightLevel,
        code leftLevel = code rightLevel →
          ReturnTowerLevelsEquivalent tower leftLevel rightLevel := by
  classical
  let embed (level : Nat) :
      Fin (decompositions.rank level) → Fin rankBound := fun letter =>
    ⟨letter.1, letter.2.trans_le (hrank level)⟩
  let rankTag (level : Nat) : Fin (rankBound + 1) :=
    ⟨decompositions.rank level, by
      have := hrank level
      omega⟩
  let imageTable (level : Nat) :
      Fin rankBound → Fin imageBound → Option (Fin rankBound) :=
    fun sourceSlot position =>
      if hsource : sourceSlot.1 < decompositions.rank level then
        ((tower.substitution level ⟨sourceSlot.1, hsource⟩)[position.1]?).map
          (embed level)
      else none
  let encode : Nat → ReturnTowerFiniteCode rankBound imageBound :=
    fun level => {
      rankTag := rankTag level
      seedTag := embed level (tower.seed level)
      headTag := embed level
        (decompositions.decomposition level).derived.head
      imageTable := imageTable level }
  let codeEquiv := Fintype.equivFin
    (ReturnTowerFiniteCode rankBound imageBound)
  let code : Nat →
      Fin (Fintype.card (ReturnTowerFiniteCode rankBound imageBound)) :=
    fun level => codeEquiv (encode level)
  have hcard : 0 <
      Fintype.card (ReturnTowerFiniteCode rankBound imageBound) := by
    letI : Nonempty (ReturnTowerFiniteCode rankBound imageBound) :=
      ⟨encode 0⟩
    exact Fintype.card_pos
  refine ⟨Fintype.card (ReturnTowerFiniteCode rankBound imageBound),
    code, hcard, ?_⟩
  intro leftLevel rightLevel hcode
  have hencoded : encode leftLevel = encode rightLevel := by
    apply codeEquiv.injective
    exact hcode
  have hrankEq : decompositions.rank leftLevel =
      decompositions.rank rightLevel := by
    have htag := congrArg
      (fun value : ReturnTowerFiniteCode rankBound imageBound =>
        value.rankTag.1) hencoded
    exact htag
  let relabel : Fin (decompositions.rank leftLevel) ≃
      Fin (decompositions.rank rightLevel) := finCongr hrankEq
  have hseedEncoded := congrArg
    (fun value : ReturnTowerFiniteCode rankBound imageBound => value.seedTag)
    hencoded
  have hseed : relabel (tower.seed leftLevel) = tower.seed rightLevel := by
    apply Fin.ext
    simpa [relabel, embed] using congrArg Fin.val hseedEncoded
  have hheadEncoded := congrArg
    (fun value : ReturnTowerFiniteCode rankBound imageBound => value.headTag)
    hencoded
  have hhead : relabel
        (decompositions.decomposition leftLevel).derived.head =
      (decompositions.decomposition rightLevel).derived.head := by
    apply Fin.ext
    simpa [relabel, embed] using congrArg Fin.val hheadEncoded
  have htable : imageTable leftLevel = imageTable rightLevel := by
    exact congrArg
      (fun value : ReturnTowerFiniteCode rankBound imageBound =>
        value.imageTable) hencoded
  have himages : ∀ letter : Fin (decompositions.rank leftLevel),
      (tower.substitution leftLevel letter).map relabel =
        tower.substitution rightLevel (relabel letter) := by
    intro letter
    apply List.ext_getElem?
    intro position
    simp only [List.getElem?_map]
    by_cases hposition : position < imageBound
    · let boundedPosition : Fin imageBound := ⟨position, hposition⟩
      let sourceSlot : Fin rankBound := embed leftLevel letter
      have hsourceLeft : sourceSlot.1 <
          decompositions.rank leftLevel := by
        simpa [sourceSlot, embed] using letter.2
      have hsourceRight : sourceSlot.1 <
          decompositions.rank rightLevel := by
        rw [← hrankEq]
        exact hsourceLeft
      have hvalue := congrFun (congrFun htable sourceSlot) boundedPosition
      rw [show imageTable leftLevel sourceSlot boundedPosition =
          ((tower.substitution leftLevel
            ⟨sourceSlot.1, hsourceLeft⟩)[position]?).map
              (embed leftLevel) by
            simp [imageTable, boundedPosition, hsourceLeft],
        show imageTable rightLevel sourceSlot boundedPosition =
          ((tower.substitution rightLevel
            ⟨sourceSlot.1, hsourceRight⟩)[position]?).map
              (embed rightLevel) by
            simp [imageTable, boundedPosition, hsourceRight]] at hvalue
      have hleftLetter : (⟨sourceSlot.1, hsourceLeft⟩ :
          Fin (decompositions.rank leftLevel)) = letter := by
        apply Fin.ext
        rfl
      have hrightLetter : (⟨sourceSlot.1, hsourceRight⟩ :
          Fin (decompositions.rank rightLevel)) = relabel letter := by
        apply Fin.ext
        rfl
      rw [hleftLetter, hrightLetter] at hvalue
      generalize hleftOption :
          (tower.substitution leftLevel letter)[position]? = leftOption
      generalize hrightOption :
          (tower.substitution rightLevel (relabel letter))[position]? =
            rightOption
      rw [hleftOption, hrightOption] at hvalue
      cases leftOption with
      | none =>
          cases rightOption with
          | none => simp
          | some rightLetter => simp at hvalue
      | some leftLetter =>
          cases rightOption with
          | none => simp at hvalue
          | some rightLetter =>
              have hembedded : embed leftLevel leftLetter =
                  embed rightLevel rightLetter := by
                simpa using hvalue
              have hrelabelLetters : relabel leftLetter = rightLetter := by
                apply Fin.ext
                simpa [relabel, embed] using congrArg Fin.val hembedded
              simp [hrelabelLetters]
    · have hleftLength := himage leftLevel letter
      have hrightLength := himage rightLevel (relabel letter)
      rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by omega)]
      simp
  have hsubstitution :
      (tower.substitution leftLevel).relabel relabel =
        tower.substitution rightLevel := by
    apply substitution_eq_of_images_c1e_b9
    intro rightLetter
    let leftLetter := relabel.symm rightLetter
    calc
      ((tower.substitution leftLevel).relabel relabel) rightLetter =
          (tower.substitution leftLevel leftLetter).map relabel := by
        simp [leftLetter]
      _ = tower.substitution rightLevel (relabel leftLetter) :=
        himages leftLetter
      _ = tower.substitution rightLevel rightLetter := by
        simp [leftLetter]
  have hleftHeadGrow : LetterImagesGrow
      (tower.substitution leftLevel)
      (decompositions.decomposition leftLevel).derived.head := by
    obtain ⟨depth, _hdepth, hcontains⟩ := tower.primitive leftLevel
    exact (tower.substitution leftLevel).letterImagesGrow_of_mem_iterate
      (hcontains (decompositions.decomposition leftLevel).derived.head
        (tower.seed leftLevel))
      (tower.images_grow leftLevel)
  let relabeledDerived :=
    Symbolic.Substitution.relabelInfiniteWordPublic relabel
      (decompositions.decomposition leftLevel).derived
  have hrelabeledFixed : (tower.substitution rightLevel).IsFixedPoint
      relabeledDerived := by
    rw [← hsubstitution]
    exact (Symbolic.Substitution.relabel_isFixedPoint_public_iff
      relabel (tower.substitution leftLevel)
        (decompositions.decomposition leftLevel).derived).2
      (tower.fixed leftLevel)
  have hrelabeledGrow : LetterImagesGrow
      (tower.substitution rightLevel) relabeledDerived.head := by
    have hgrow := (tower.substitution leftLevel).relabel_letterImagesGrow
      relabel hleftHeadGrow
    rw [hsubstitution] at hgrow
    simpa [relabeledDerived,
      Symbolic.Substitution.relabelInfiniteWordPublic] using hgrow
  have hrelabeledHead : relabeledDerived.head =
      (decompositions.decomposition rightLevel).derived.head := by
    simpa [relabeledDerived,
      Symbolic.Substitution.relabelInfiniteWordPublic] using hhead
  have hderived : relabeledDerived =
      (decompositions.decomposition rightLevel).derived :=
    fixedPoints_eq_of_head_and_growth_b9 hrelabeledFixed
      (tower.fixed rightLevel) hrelabeledHead hrelabeledGrow
  refine ⟨relabel, hseed, ?_, himages⟩
  · intro position
    simpa [relabeledDerived,
      Symbolic.Substitution.relabelInfiniteWordPublic] using
        congrFun hderived position

/-- Leaf C1e: bounded ranks and bounded induced images leave only finitely
many seed/substitution/derived systems up to bijective relabeling. -/
theorem finiteCode_of_returnTowerInfrastructure
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    (infrastructure : ReturnTowerInfrastructure input) :
    Nonempty (FiniteReturnSystemFamily input) := by
  obtain ⟨leftClassCount, leftCode, hleftCountPos, hleftSame⟩ :=
    poweredReturnTower_has_finiteCoding_b9 infrastructure.left
      infrastructure.bounds.rankBound
      infrastructure.bounds.leftImageLengthBound
      infrastructure.bounds.rank_le
      infrastructure.bounds.left_image_length_le
  obtain ⟨rightClassCount, rightCode, hrightCountPos, hrightSame⟩ :=
    poweredReturnTower_has_finiteCoding_b9 infrastructure.right
      infrastructure.bounds.rankBound
      infrastructure.bounds.rightImageLengthBound
      infrastructure.bounds.rank_le
      infrastructure.bounds.right_image_length_le
  exact ⟨{
    infrastructure := infrastructure
    leftClassCount := leftClassCount
    rightClassCount := rightClassCount
    leftClassCount_pos := hleftCountPos
    rightClassCount_pos := hrightCountPos
    leftCode := leftCode
    rightCode := rightCode
    left_same_code := hleftSame
    right_same_code := hrightSame }⟩

/-- Proved C1 aggregator.  Each construction stage remains separately
visible, and the resulting family cannot be the former constant tower. -/
theorem exists_finiteReturnSystemFamily
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    (input : PrimitiveReturnComparisonInput data)
    (notPeriodicLanguage :
      ¬ Symbolic.HasPeriodicRecurrentLanguage data.word) :
    Nonempty (FiniteReturnSystemFamily input) := by
  obtain ⟨markers⟩ := exists_cofinalPrefixMarkerTower input
  obtain ⟨decompositions⟩ :=
    cofinalMarkers_have_returnDecompositionTower markers
  obtain ⟨left⟩ := exists_leftPoweredReturnTower decompositions
  obtain ⟨right⟩ := exists_rightPoweredReturnTower decompositions
  obtain ⟨nested⟩ :=
    returnDecompositionTower_has_nestedFactorizations decompositions
  obtain ⟨bounds⟩ :=
    returnTowers_have_uniformBounds left right notPeriodicLanguage
  let infrastructure : ReturnTowerInfrastructure input := {
    markers := markers
    decompositions := decompositions
    left := left
    right := right
    nested := nested
    bounds := bounds }
  exact finiteCode_of_returnTowerInfrastructure infrastructure

/-- Pigeonhole output: each finite return-system family repeats at two
strictly ordered tower levels. -/
structure RepeatedReturnSystems
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    (family : FiniteReturnSystemFamily input) where
  leftEarlier : Nat
  leftLater : Nat
  left_lt : leftEarlier < leftLater
  left_code_eq : family.leftCode leftEarlier = family.leftCode leftLater
  rightEarlier : Nat
  rightLater : Nat
  right_lt : rightEarlier < rightLater
  right_code_eq : family.rightCode rightEarlier = family.rightCode rightLater

/-- Proved C-stage pigeonhole selection; no Durand-specific leaf is hidden
in this finite argument. -/
theorem finiteReturnSystemFamily_has_repetitions
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    (family : FiniteReturnSystemFamily input) :
    Nonempty (RepeatedReturnSystems family) := by
  obtain ⟨leftI, leftJ, hleftNe, hleftCode⟩ :=
    Finite.exists_ne_map_eq_of_infinite family.leftCode
  obtain ⟨rightI, rightJ, hrightNe, hrightCode⟩ :=
    Finite.exists_ne_map_eq_of_infinite family.rightCode
  rcases lt_or_gt_of_ne hleftNe with hleft | hleft
  · rcases lt_or_gt_of_ne hrightNe with hright | hright
    · exact ⟨{
        leftEarlier := leftI
        leftLater := leftJ
        left_lt := hleft
        left_code_eq := hleftCode
        rightEarlier := rightI
        rightLater := rightJ
        right_lt := hright
        right_code_eq := hrightCode }⟩
    · exact ⟨{
        leftEarlier := leftI
        leftLater := leftJ
        left_lt := hleft
        left_code_eq := hleftCode
        rightEarlier := rightJ
        rightLater := rightI
        right_lt := hright
        right_code_eq := hrightCode.symm }⟩
  · rcases lt_or_gt_of_ne hrightNe with hright | hright
    · exact ⟨{
        leftEarlier := leftJ
        leftLater := leftI
        left_lt := hleft
        left_code_eq := hleftCode.symm
        rightEarlier := rightI
        rightLater := rightJ
        right_lt := hright
        right_code_eq := hrightCode }⟩
    · exact ⟨{
        leftEarlier := leftJ
        leftLater := leftI
        left_lt := hleft
        left_code_eq := hleftCode.symm
        rightEarlier := rightJ
        rightLater := rightI
        right_lt := hright
        right_code_eq := hrightCode.symm }⟩

/-- C2 alignment data: both within-scale repetitions are exposed together
with one strictly deeper common marker and all four nested decoding maps.
Thus normalization cannot hide marker alignment or return refinement. -/
structure AlignedRepeatedReturnSystems
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    (repeated : RepeatedReturnSystems family) where
  commonLevel : Nat
  leftEarlier_lt_common : repeated.leftEarlier < commonLevel
  leftLater_lt_common : repeated.leftLater < commonLevel
  rightEarlier_lt_common : repeated.rightEarlier < commonLevel
  rightLater_lt_common : repeated.rightLater < commonLevel
  leftRepeated : ReturnTowerLevelsEquivalent
    family.infrastructure.left repeated.leftEarlier repeated.leftLater
  rightRepeated : ReturnTowerLevelsEquivalent
    family.infrastructure.right repeated.rightEarlier repeated.rightLater
  leftEarlierToCommon : Symbolic.NestedReturnFactorization
    (family.infrastructure.decompositions.decomposition repeated.leftEarlier)
    (family.infrastructure.decompositions.decomposition commonLevel)
  leftLaterToCommon : Symbolic.NestedReturnFactorization
    (family.infrastructure.decompositions.decomposition repeated.leftLater)
    (family.infrastructure.decompositions.decomposition commonLevel)
  rightEarlierToCommon : Symbolic.NestedReturnFactorization
    (family.infrastructure.decompositions.decomposition repeated.rightEarlier)
    (family.infrastructure.decompositions.decomposition commonLevel)
  rightLaterToCommon : Symbolic.NestedReturnFactorization
    (family.infrastructure.decompositions.decomposition repeated.rightLater)
    (family.infrastructure.decompositions.decomposition commonLevel)

/-- Proved C2 alignment aggregator: choose a level beyond both later
collisions and obtain all refinement maps from the C1c tower. -/
theorem repeatedReturnSystems_have_commonAlignment
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    (repeated : RepeatedReturnSystems family) :
    Nonempty (AlignedRepeatedReturnSystems repeated) := by
  let commonLevel := max repeated.leftLater repeated.rightLater + 1
  have hleftOrder := repeated.left_lt
  have hrightOrder := repeated.right_lt
  have hleftEarlier : repeated.leftEarlier < commonLevel := by
    dsimp [commonLevel]
    omega
  have hleftLater : repeated.leftLater < commonLevel := by
    dsimp [commonLevel]
    omega
  have hrightEarlier : repeated.rightEarlier < commonLevel := by
    dsimp [commonLevel]
    omega
  have hrightLater : repeated.rightLater < commonLevel := by
    dsimp [commonLevel]
    omega
  exact ⟨{
    commonLevel := commonLevel
    leftEarlier_lt_common := hleftEarlier
    leftLater_lt_common := hleftLater
    rightEarlier_lt_common := hrightEarlier
    rightLater_lt_common := hrightLater
    leftRepeated := family.left_same_code _ _ repeated.left_code_eq
    rightRepeated := family.right_same_code _ _ repeated.right_code_eq
    leftEarlierToCommon :=
      family.infrastructure.nested.factorization hleftEarlier
    leftLaterToCommon :=
      family.infrastructure.nested.factorization hleftLater
    rightEarlierToCommon :=
      family.infrastructure.nested.factorization hrightEarlier
    rightLaterToCommon :=
      family.infrastructure.nested.factorization hrightLater }⟩

/-- The four named nested decoders carry exact same-source word equations at
the common level.  Keeping these equations separate prevents them from being
mistaken for unsupported cross-source intertwining squares. -/
structure AlignedNestedIntertwiningData
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    (aligned : AlignedRepeatedReturnSystems repeated) where
  leftEarlier_nonempty : ∀ letter,
    aligned.leftEarlierToCommon.factor letter ≠ []
  leftLater_nonempty : ∀ letter,
    aligned.leftLaterToCommon.factor letter ≠ []
  rightEarlier_nonempty : ∀ letter,
    aligned.rightEarlierToCommon.factor letter ≠ []
  rightLater_nonempty : ∀ letter,
    aligned.rightLaterToCommon.factor letter ≠ []
  leftEarlier_intertwines : ∀ letter,
    (family.infrastructure.left.substitution repeated.leftEarlier).mapWord
        (aligned.leftEarlierToCommon.factor letter) =
      (family.infrastructure.left.substitution aligned.commonLevel letter).flatMap
        aligned.leftEarlierToCommon.factor
  leftLater_intertwines : ∀ letter,
    (family.infrastructure.left.substitution repeated.leftLater).mapWord
        (aligned.leftLaterToCommon.factor letter) =
      (family.infrastructure.left.substitution aligned.commonLevel letter).flatMap
        aligned.leftLaterToCommon.factor
  rightEarlier_intertwines : ∀ letter,
    (family.infrastructure.right.substitution repeated.rightEarlier).mapWord
        (aligned.rightEarlierToCommon.factor letter) =
      (family.infrastructure.right.substitution aligned.commonLevel letter).flatMap
        aligned.rightEarlierToCommon.factor
  rightLater_intertwines : ∀ letter,
    (family.infrastructure.right.substitution repeated.rightLater).mapWord
        (aligned.rightLaterToCommon.factor letter) =
      (family.infrastructure.right.substitution aligned.commonLevel letter).flatMap
        aligned.rightLaterToCommon.factor

/-- Proved packaging of the four exact nested-decoder equations. -/
theorem alignedReturnSystems_have_exactNestedIntertwinings
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    (aligned : AlignedRepeatedReturnSystems repeated) :
    Nonempty (AlignedNestedIntertwiningData aligned) := by
  exact ⟨{
    leftEarlier_nonempty :=
      aligned.leftEarlierToCommon.factor_ne_nil
    leftLater_nonempty :=
      aligned.leftLaterToCommon.factor_ne_nil
    rightEarlier_nonempty :=
      aligned.rightEarlierToCommon.factor_ne_nil
    rightLater_nonempty :=
      aligned.rightLaterToCommon.factor_ne_nil
    leftEarlier_intertwines := fun letter =>
      prefixReturnSubstitutions_intertwine_nestedFactorization
        (family.infrastructure.left.factorization repeated.leftEarlier)
        (family.infrastructure.left.factorization aligned.commonLevel)
        aligned.leftEarlierToCommon letter
    leftLater_intertwines := fun letter =>
      prefixReturnSubstitutions_intertwine_nestedFactorization
        (family.infrastructure.left.factorization repeated.leftLater)
        (family.infrastructure.left.factorization aligned.commonLevel)
        aligned.leftLaterToCommon letter
    rightEarlier_intertwines := fun letter =>
      prefixReturnSubstitutions_intertwine_nestedFactorization
        (family.infrastructure.right.factorization repeated.rightEarlier)
        (family.infrastructure.right.factorization aligned.commonLevel)
        aligned.rightEarlierToCommon letter
    rightLater_intertwines := fun letter =>
      prefixReturnSubstitutions_intertwine_nestedFactorization
        (family.infrastructure.right.factorization repeated.rightLater)
        (family.infrastructure.right.factorization aligned.commonLevel)
        aligned.rightLaterToCommon letter }⟩

/-- A return-block decoder viewed as a nonerasing substitution when the
return alphabet has been identified with the ambient alphabet. -/
def returnDecoderSubstitution
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank) :
    Symbolic.Substitution (Fin rank) where
  image := decomposition.blocks
  image_ne_nil := fun letter =>
    (decomposition.blocks_are_returns letter).2.1

/-- Infinite concatenation of the return blocks in a complete return
decomposition recovers the original word. -/
private theorem returnDecoderSubstitution_mapInfinite_derived
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank) :
    (returnDecoderSubstitution decomposition).mapInfinite
        decomposition.derived = word := by
  let decoder := returnDecoderSubstitution decomposition
  let R : Symbolic.InfiniteWord (Fin rank) →
      Symbolic.InfiniteWord (Fin rank) → Prop := fun left right =>
    ∃ (pref : Symbolic.Word (Fin rank)) (stage : Nat),
      left = pref ++ₛ decoder.mapInfinite (decomposition.derived.drop stage) ∧
      right = pref ++ₛ word.drop (decomposition.cut stage)
  apply Stream'.eq_of_bisim R
  · intro left right hrelated
    rcases hrelated with ⟨pref, stage, rfl, rfl⟩
    cases pref with
    | cons head tail =>
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨tail, stage, rfl, rfl⟩⟩
    | nil =>
        simp only [Stream'.nil_append_stream]
        let block := decomposition.blocks (decomposition.derived stage)
        have hleft :
            decoder.mapInfinite (decomposition.derived.drop stage) =
              block ++ₛ decoder.mapInfinite
                (decomposition.derived.drop (stage + 1)) := by
          rw [decoder.mapInfinite_eq_append_first_image]
          simp [decoder, returnDecoderSubstitution, block,
            Stream'.get]
        have hright :
            word.drop (decomposition.cut stage) =
              block ++ₛ word.drop (decomposition.cut (stage + 1)) := by
          calc
            word.drop (decomposition.cut stage) =
                (word.drop (decomposition.cut stage)).take block.length ++ₛ
                  (word.drop (decomposition.cut stage)).drop block.length :=
              (Stream'.append_take_drop _ _).symm
            _ = block ++ₛ word.drop (decomposition.cut (stage + 1)) := by
              rw [show (word.drop (decomposition.cut stage)).take block.length =
                  block by
                exact decomposition.block_at_cut stage]
              simp [block, decomposition.cut_succ, Stream'.drop_drop]
        rw [hleft, hright]
        obtain ⟨head, tail, hblock⟩ := List.exists_cons_of_ne_nil
          (decomposition.blocks_are_returns
            (decomposition.derived stage)).2.1
        change block = head :: tail at hblock
        rw [hblock]
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨tail, stage + 1, rfl, rfl⟩⟩
  · exact ⟨[], 0, by simp [decoder], by simp [decomposition.cut_zero]⟩

/-- A nonerasing substitution sends a purely periodic word to a purely
periodic word, although the output period is measured in decoded letters. -/
private theorem substitution_mapInfinite_isPeriodic
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet)
    {word : Symbolic.InfiniteWord alphabet}
    (hperiodic : Symbolic.IsPeriodic word) :
    Symbolic.IsPeriodic (substitution.mapInfinite word) := by
  rcases hperiodic with ⟨period, hperiodPos, hperiod⟩
  let periodWord := word.take period
  let decodedPeriod := substitution.mapWord periodWord
  have hperiodWordNonempty : periodWord ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [periodWord, hperiodPos]
  have hdecodedPeriodNonempty : decodedPeriod ≠ [] :=
    substitution.mapWord_ne_nil hperiodWordNonempty
  have hdrop : word.drop period = word := by
    funext position
    calc
      (word.drop period) position = word (period + position) :=
        Stream'.get_drop position period word
      _ = word position := by
        simpa [Nat.add_comm] using hperiod position
  have hself : substitution.mapInfinite word =
      decodedPeriod ++ₛ substitution.mapInfinite word := by
    calc
      substitution.mapInfinite word =
          substitution.mapInfinite (word.take period ++ₛ word.drop period) := by
            rw [Stream'.append_take_drop]
      _ = substitution.mapWord (word.take period) ++ₛ
            substitution.mapInfinite (word.drop period) :=
          substitution.mapInfinite_append_stream _ _
      _ = decodedPeriod ++ₛ substitution.mapInfinite word := by
          rw [hdrop]
  refine ⟨decodedPeriod.length,
    List.length_pos_of_ne_nil hdecodedPeriodNonempty, ?_⟩
  intro position
  have hpoint := congrFun hself (decodedPeriod.length + position)
  calc
    substitution.mapInfinite word (position + decodedPeriod.length) =
        substitution.mapInfinite word (decodedPeriod.length + position) := by
      rw [Nat.add_comm]
    _ = (decodedPeriod ++ₛ substitution.mapInfinite word).get
          (decodedPeriod.length + position) := hpoint
    _ = substitution.mapInfinite word position :=
      Stream'.get_append_right position decodedPeriod
        (substitution.mapInfinite word)

/-- Periodicity of a complete derived return word forces periodicity of the
word decoded by its return blocks. -/
private theorem returnDecomposition_word_periodic_of_derived_periodic
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (hperiodic : Symbolic.IsPeriodic decomposition.derived) :
    Symbolic.IsPeriodic word := by
  rw [← returnDecoderSubstitution_mapInfinite_derived decomposition]
  exact substitution_mapInfinite_isPeriodic
    (returnDecoderSubstitution decomposition) hperiodic

/-- If the return-derived word of a recurrent core is periodic, decoding its
arbitrarily high powers gives a periodic recurrent language for the original
word. -/
private theorem returnDecomposition_derivedPeriodic_hasPeriodicRecurrentLanguage
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    (core : Symbolic.RecurrentCore word)
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (decomposition :
      Symbolic.ReturnDecomposition core.word marker rank)
    (hperiodic : Symbolic.IsPeriodic decomposition.derived) :
    Symbolic.HasPeriodicRecurrentLanguage word := by
  obtain ⟨derivedRoot, hderivedRootPrimitive, hpowers⟩ :=
    hperiodic.hasPrimitivePowerFactors
  let decodedRoot := derivedRoot.flatMap decomposition.blocks
  have hdecodedRootNonempty : decodedRoot ≠ [] := by
    obtain ⟨head, tail, hroot⟩ :=
      List.exists_cons_of_ne_nil hderivedRootPrimitive.1
    change derivedRoot.flatMap decomposition.blocks ≠ []
    rw [hroot]
    exact List.append_ne_nil_of_left_ne_nil
      (decomposition.blocks_are_returns head).2.1 _
  have hdecodePower : ∀ exponent : Nat,
      (Symbolic.wordPower derivedRoot exponent).flatMap decomposition.blocks =
        Symbolic.wordPower decodedRoot exponent := by
    intro exponent
    induction exponent with
    | zero => simp [Symbolic.wordPower]
    | succ exponent ih =>
        calc
          (Symbolic.wordPower derivedRoot (exponent + 1)).flatMap
                decomposition.blocks =
              (Symbolic.wordPower derivedRoot exponent).flatMap
                  decomposition.blocks ++
                (Symbolic.wordPower derivedRoot 1).flatMap
                  decomposition.blocks := by
            rw [Symbolic.wordPower_add, List.flatMap_append]
          _ = Symbolic.wordPower decodedRoot exponent ++ decodedRoot := by
            rw [ih]
            simp [decodedRoot, Symbolic.wordPower]
          _ = Symbolic.wordPower decodedRoot (exponent + 1) := by
            rw [Symbolic.wordPower_add]
            simp [Symbolic.wordPower]
  have hdecodedPowerFactor : ∀ exponent : Nat, 0 < exponent →
      Symbolic.IsInfiniteFactor core.word
        (Symbolic.wordPower decodedRoot exponent) := by
    intro exponent hexponent
    rcases hpowers exponent hexponent with ⟨start, hfactor⟩
    have hdecode := decomposition.flatMap_drop_take_derived start
      (Symbolic.wordPower derivedRoot exponent).length
    rw [hfactor, hdecodePower exponent] at hdecode
    refine ⟨decomposition.cut start, ?_⟩
    exact hdecode.symm
  obtain ⟨primitiveRoot, primitiveExponent, hprimitiveRoot,
      hprimitiveExponent, hprimitivePower⟩ :=
    Symbolic.exists_primitiveRoot decodedRoot hdecodedRootNonempty
  refine ⟨primitiveRoot, hprimitiveRoot, ?_⟩
  intro exponent hexponent
  apply (core.same_language (Symbolic.wordPower primitiveRoot exponent)).mp
  have hlarge := hdecodedPowerFactor exponent hexponent
  have hprefix :
      Symbolic.wordPower primitiveRoot exponent <+:
        Symbolic.wordPower decodedRoot exponent := by
    have hle : exponent ≤ exponent * primitiveExponent :=
      Nat.le_mul_of_pos_right exponent hprimitiveExponent
    rw [← hprimitivePower, Symbolic.wordPower_wordPower]
    exact Symbolic.wordPower_prefix_of_le hle
  exact hlarge.of_infix hprefix.isInfix

/-- The four explicit hypotheses of Durand's Proposition 10, with fixedness,
primitivity, and prolongability retained because they are consumed by the
power-equation and spectral steps. -/
structure DurandProposition10Input
    {rank : Nat} (word : Symbolic.InfiniteWord (Fin rank))
    (source : Symbolic.Substitution (Fin rank)) where
  rank_pos : 0 < rank
  seed : Fin rank
  seed_is_head : seed = word.head
  source_fixed : source.IsFixedPoint word
  source_primitive : IsPrimitiveSubstitution source
  source_prolongable : source.ProlongableOn seed
  word_aperiodic : ¬ Symbolic.IsPeriodic word
  images_begin_seed : ∀ letter : Fin rank, [seed] <+: source letter
  marker : Symbolic.Word (Fin rank)
  decomposition : Symbolic.ReturnDecomposition word marker rank
  derived_eq : decomposition.derived = word
  induced : PrefixReturnSubstitutionFactorization source decomposition
  induced_eq : induced.substitution = source
  decoder_fixed :
    (returnDecoderSubstitution decomposition).IsFixedPoint word
  decoder_prolongable :
    (returnDecoderSubstitution decomposition).ProlongableOn seed
  decoder_generating :
    (returnDecoderSubstitution decomposition).IsGeneratingLetter seed
  decoder_primitive :
    IsPrimitiveSubstitution (returnDecoderSubstitution decomposition)
  decoder_contains_all : ∀ sourceLetter targetLetter : Fin rank,
    targetLetter ∈ decomposition.blocks sourceLetter

/-- Durand Lemma 12 output specialized to the two exact powered return
towers.  The selected system lies strictly beyond the displayed common
alignment, and every substitution mentioned below is definitionally induced
from its original powered source. -/
structure DurandCommonDerivedSystem
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    (_refinements : AlignedNestedIntertwiningData aligned) where
  selectedLevel : Nat
  common_lt_selected : aligned.commonLevel < selectedLevel
  commonToSelected : Symbolic.NestedReturnFactorization
    (family.infrastructure.decompositions.decomposition aligned.commonLevel)
    (family.infrastructure.decompositions.decomposition selectedLevel)
  commonPower : Nat
  commonPower_pos : 0 < commonPower
  seed : Fin (family.infrastructure.decompositions.rank selectedLevel)
  seed_is_head : seed =
    (family.infrastructure.decompositions.decomposition selectedLevel).derived.head
  left_seed_eq : family.infrastructure.left.seed selectedLevel = seed
  right_seed_eq : family.infrastructure.right.seed selectedLevel = seed
  marker : Symbolic.Word
    (Fin (family.infrastructure.decompositions.rank selectedLevel))
  decomposition : Symbolic.ReturnDecomposition
    (family.infrastructure.decompositions.decomposition selectedLevel).derived
    marker (family.infrastructure.decompositions.rank selectedLevel)
  derived_eq : decomposition.derived =
    (family.infrastructure.decompositions.decomposition selectedLevel).derived
  leftInduced : PrefixReturnSubstitutionFactorization
    ((family.infrastructure.left.substitution selectedLevel).power commonPower)
      decomposition
  rightInduced : PrefixReturnSubstitutionFactorization
    ((family.infrastructure.right.substitution selectedLevel).power commonPower)
      decomposition
  left_induced_eq : leftInduced.substitution =
    (family.infrastructure.left.substitution selectedLevel).power commonPower
  right_induced_eq : rightInduced.substitution =
    (family.infrastructure.right.substitution selectedLevel).power commonPower
  left_power_fixed :
    ((family.infrastructure.left.substitution selectedLevel).power
      commonPower).IsFixedPoint
        (family.infrastructure.decompositions.decomposition selectedLevel).derived
  right_power_fixed :
    ((family.infrastructure.right.substitution selectedLevel).power
      commonPower).IsFixedPoint
        (family.infrastructure.decompositions.decomposition selectedLevel).derived
  left_power_primitive : IsPrimitiveSubstitution
    ((family.infrastructure.left.substitution selectedLevel).power commonPower)
  right_power_primitive : IsPrimitiveSubstitution
    ((family.infrastructure.right.substitution selectedLevel).power commonPower)
  left_power_prolongable :
    ((family.infrastructure.left.substitution selectedLevel).power
      commonPower).ProlongableOn seed
  right_power_prolongable :
    ((family.infrastructure.right.substitution selectedLevel).power
      commonPower).ProlongableOn seed
  left_power_dominant : IsDominantEigenvalue
    ((family.infrastructure.left.substitution selectedLevel).power
      commonPower).incidenceMatrix
      ((a ^ family.infrastructure.left.exponent) ^ commonPower)
  right_power_dominant : IsDominantEigenvalue
    ((family.infrastructure.right.substitution selectedLevel).power
      commonPower).incidenceMatrix
      ((b ^ family.infrastructure.right.exponent) ^ commonPower)
  left_images_begin_seed : ∀ letter,
    [seed] <+:
      (family.infrastructure.left.substitution selectedLevel).power
        commonPower letter
  right_images_begin_seed : ∀ letter,
    [seed] <+:
      (family.infrastructure.right.substitution selectedLevel).power
        commonPower letter
  word_aperiodic : ¬ Symbolic.IsPeriodic
    (family.infrastructure.decompositions.decomposition selectedLevel).derived
  decoder_fixed : (returnDecoderSubstitution decomposition).IsFixedPoint
    (family.infrastructure.decompositions.decomposition selectedLevel).derived
  decoder_prolongable :
    (returnDecoderSubstitution decomposition).ProlongableOn seed
  decoder_generating :
    (returnDecoderSubstitution decomposition).IsGeneratingLetter seed
  decoder_primitive :
    IsPrimitiveSubstitution (returnDecoderSubstitution decomposition)
  decoder_contains_all : ∀ sourceLetter targetLetter,
    targetLetter ∈ decomposition.blocks sourceLetter

/-- The final common-to-selected decoder is nonerasing. -/
theorem DurandCommonDerivedSystem.commonToSelected_nonempty
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (system : DurandCommonDerivedSystem refinements) (letter : Fin
      (family.infrastructure.decompositions.rank system.selectedLevel)) :
    system.commonToSelected.factor letter ≠ [] :=
  system.commonToSelected.factor_ne_nil letter

/-- Exact left-source word equation for the final common-to-selected
refinement used by Lemma 12. -/
theorem DurandCommonDerivedSystem.left_commonToSelected_intertwines
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (system : DurandCommonDerivedSystem refinements) (letter : Fin
      (family.infrastructure.decompositions.rank system.selectedLevel)) :
    (family.infrastructure.left.substitution aligned.commonLevel).mapWord
        (system.commonToSelected.factor letter) =
      (family.infrastructure.left.substitution system.selectedLevel letter).flatMap
        system.commonToSelected.factor :=
  prefixReturnSubstitutions_intertwine_nestedFactorization
    (family.infrastructure.left.factorization aligned.commonLevel)
    (family.infrastructure.left.factorization system.selectedLevel)
    system.commonToSelected letter

/-- Exact right-source word equation for the same final refinement. -/
theorem DurandCommonDerivedSystem.right_commonToSelected_intertwines
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (system : DurandCommonDerivedSystem refinements) (letter : Fin
      (family.infrastructure.decompositions.rank system.selectedLevel)) :
    (family.infrastructure.right.substitution aligned.commonLevel).mapWord
        (system.commonToSelected.factor letter) =
      (family.infrastructure.right.substitution system.selectedLevel letter).flatMap
        system.commonToSelected.factor :=
  prefixReturnSubstitutions_intertwine_nestedFactorization
    (family.infrastructure.right.factorization aligned.commonLevel)
    (family.infrastructure.right.factorization system.selectedLevel)
    system.commonToSelected letter

/-- The left exact powered return system satisfies the generic Proposition
10 interface. -/
def DurandCommonDerivedSystem.leftInput
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (system : DurandCommonDerivedSystem refinements) :
    DurandProposition10Input
      (family.infrastructure.decompositions.decomposition
        system.selectedLevel).derived
      ((family.infrastructure.left.substitution system.selectedLevel).power
        system.commonPower) where
  rank_pos :=
    (family.infrastructure.decompositions.decomposition
      system.selectedLevel).rank_pos
  seed := system.seed
  seed_is_head := system.seed_is_head
  source_fixed := system.left_power_fixed
  source_primitive := system.left_power_primitive
  source_prolongable := system.left_power_prolongable
  word_aperiodic := system.word_aperiodic
  images_begin_seed := system.left_images_begin_seed
  marker := system.marker
  decomposition := system.decomposition
  derived_eq := system.derived_eq
  induced := system.leftInduced
  induced_eq := system.left_induced_eq
  decoder_fixed := system.decoder_fixed
  decoder_prolongable := system.decoder_prolongable
  decoder_generating := system.decoder_generating
  decoder_primitive := system.decoder_primitive
  decoder_contains_all := system.decoder_contains_all

/-- The right exact powered return system satisfies the same generic
Proposition 10 interface on the identical word, seed, marker, and decoder. -/
def DurandCommonDerivedSystem.rightInput
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (system : DurandCommonDerivedSystem refinements) :
    DurandProposition10Input
      (family.infrastructure.decompositions.decomposition
        system.selectedLevel).derived
      ((family.infrastructure.right.substitution system.selectedLevel).power
        system.commonPower) where
  rank_pos :=
    (family.infrastructure.decompositions.decomposition
      system.selectedLevel).rank_pos
  seed := system.seed
  seed_is_head := system.seed_is_head
  source_fixed := system.right_power_fixed
  source_primitive := system.right_power_primitive
  source_prolongable := system.right_power_prolongable
  word_aperiodic := system.word_aperiodic
  images_begin_seed := system.right_images_begin_seed
  marker := system.marker
  decomposition := system.decomposition
  derived_eq := system.derived_eq
  induced := system.rightInduced
  induced_eq := system.right_induced_eq
  decoder_fixed := system.decoder_fixed
  decoder_prolongable := system.decoder_prolongable
  decoder_generating := system.decoder_generating
  decoder_primitive := system.decoder_primitive
  decoder_contains_all := system.decoder_contains_all

/-- C2.1: iterated derivation at the current first letter.  Each successor
word is the displayed return-derived word; the heterogeneous block decoders
are composed all the way back to stage zero.  Both exact source substitutions
are induced through every step. -/
structure IteratedFirstLetterDerivedSystems
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    (_refinements : AlignedNestedIntertwiningData aligned) where
  rank : Nat → Nat
  rank_pos : ∀ stage, 0 < rank stage
  word : ∀ stage, Symbolic.InfiniteWord (Fin (rank stage))
  baseRelabel : Fin (rank 0) ≃ Fin
    (family.infrastructure.decompositions.rank aligned.commonLevel)
  base_word_eq : ∀ position,
    baseRelabel (word 0 position) =
      (family.infrastructure.decompositions.decomposition
        aligned.commonLevel).derived position
  stepDecomposition : ∀ stage,
    Symbolic.ReturnDecomposition (word stage) [(word stage).head]
      (rank (stage + 1))
  step_word_eq : ∀ stage,
    (stepDecomposition stage).derived = word (stage + 1)
  compositeDecoder : ∀ stage,
    Fin (rank stage) → Symbolic.Word (Fin (rank 0))
  compositeDecoder_zero : ∀ letter,
    compositeDecoder 0 letter = [letter]
  compositeDecoder_succ : ∀ stage letter,
    compositeDecoder (stage + 1) letter =
      ((stepDecomposition stage).blocks letter).flatMap
        (compositeDecoder stage)
  compositeDecoder_nonempty : ∀ stage letter,
    compositeDecoder stage letter ≠ []
  leftSubstitution : ∀ stage, Symbolic.Substitution (Fin (rank stage))
  rightSubstitution : ∀ stage, Symbolic.Substitution (Fin (rank stage))
  leftFixed : ∀ stage,
    (leftSubstitution stage).IsFixedPoint (word stage)
  rightFixed : ∀ stage,
    (rightSubstitution stage).IsFixedPoint (word stage)
  leftStepFactorization : ∀ stage,
    PrefixReturnSubstitutionFactorization (leftSubstitution stage)
      (stepDecomposition stage)
  rightStepFactorization : ∀ stage,
    PrefixReturnSubstitutionFactorization (rightSubstitution stage)
      (stepDecomposition stage)
  left_succ_eq : ∀ stage,
    leftSubstitution (stage + 1) =
      (leftStepFactorization stage).substitution
  right_succ_eq : ∀ stage,
    rightSubstitution (stage + 1) =
      (rightStepFactorization stage).substitution
  left_base_eq : ∀ letter,
    (leftSubstitution 0 letter).map baseRelabel =
      family.infrastructure.left.substitution aligned.commonLevel
        (baseRelabel letter)
  right_base_eq : ∀ letter,
    (rightSubstitution 0 letter).map baseRelabel =
      family.infrastructure.right.substitution aligned.commonLevel
        (baseRelabel letter)

/-- The recursively composed first-letter decoder always spells an actual
prefix of the original common-level derived word.  This is the explicit
bridge between the iterated first-letter systems and the cofinal marker
system from which they were built. -/
private theorem IteratedFirstLetterDerivedSystems.compositeDecoder_is_commonPrefix
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage count : Nat) :
    Symbolic.InfiniteFactorAt
      (family.infrastructure.decompositions.decomposition
        aligned.commonLevel).derived
      ((((tower.word stage).take count).flatMap
        (tower.compositeDecoder stage)).map tower.baseRelabel) 0 := by
  have hbase : ∀ (stage count : Nat),
      Symbolic.InfiniteFactorAt (tower.word 0)
        (((tower.word stage).take count).flatMap
          (tower.compositeDecoder stage)) 0 := by
    intro currentStage
    induction currentStage with
    | zero =>
        intro currentCount
        have hdecoder : tower.compositeDecoder 0 =
            fun letter => [letter] := by
          funext letter
          exact tower.compositeDecoder_zero letter
        simp [Symbolic.InfiniteFactorAt, hdecoder]
    | succ currentStage ih =>
        intro currentCount
        have hdecoded :
            ((tower.word (currentStage + 1)).take currentCount).flatMap
                (tower.compositeDecoder (currentStage + 1)) =
              ((tower.word currentStage).take
                  ((tower.stepDecomposition currentStage).cut currentCount)).flatMap
                (tower.compositeDecoder currentStage) := by
          have hdecoderSucc :
              tower.compositeDecoder (currentStage + 1) = fun letter =>
                ((tower.stepDecomposition currentStage).blocks letter).flatMap
                  (tower.compositeDecoder currentStage) := by
            funext letter
            exact tower.compositeDecoder_succ currentStage letter
          rw [hdecoderSucc]
          rw [← List.flatMap_assoc]
          have hstep :=
            (tower.stepDecomposition currentStage).flatMap_take_derived
              currentCount
          rw [tower.step_word_eq currentStage] at hstep
          rw [hstep]
        rw [hdecoded]
        exact ih ((tower.stepDecomposition currentStage).cut currentCount)
  let coding : Symbolic.LetterCoding (Fin (tower.rank 0))
      (Fin (family.infrastructure.decompositions.rank aligned.commonLevel)) :=
    ⟨tower.baseRelabel⟩
  have hmapped := coding.infiniteFactorAt_mapInfinite (hbase stage count)
  have hword : coding.mapInfinite (tower.word 0) =
      (family.infrastructure.decompositions.decomposition
        aligned.commonLevel).derived := by
    funext position
    exact tower.base_word_eq position
  rw [hword] at hmapped
  simpa [coding, Symbolic.LetterCoding.mapWord] using hmapped

/-- Positive exact metric scaling by a factor greater than one forces every
letter image to grow.  This production-local copy keeps the C2 construction independent of
the private helper used by the earlier return-tower construction. -/
private theorem letterImagesGrow_of_positive_metricScaling_c2
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    [Nonempty alphabet]
    {substitution : Symbolic.Substitution alphabet}
    {length : alphabet → Real} {scale : Real}
    (hlength : ∀ letter, 0 < length letter)
    (hscale : SubstitutionScalesLetterLengths substitution length scale)
    (hone : 1 < scale) (seed : alphabet) :
    LetterImagesGrow substitution seed := by
  classical
  let total : Real := ∑ letter : alphabet, length letter
  let chosen : alphabet := Classical.choice inferInstance
  have hchosen_le : length chosen ≤ total := by
    dsimp [total]
    exact Finset.single_le_sum (fun letter _ ↦ (hlength letter).le)
      (Finset.mem_univ chosen)
  have htotal_pos : 0 < total := (hlength chosen).trans_le hchosen_le
  have hupper : ∀ word : Symbolic.Word alphabet,
      wordMetricLength length word ≤ (word.length : Real) * total := by
    intro word
    induction word with
    | nil => simp [wordMetricLength]
    | cons letter word ih =>
        have hletter_le : length letter ≤ total := by
          dsimp [total]
          exact Finset.single_le_sum
            (fun other _ ↦ (hlength other).le)
            (Finset.mem_univ letter)
        simp only [wordMetricLength, List.map_cons, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        have htotal_nonneg : 0 ≤ total := htotal_pos.le
        change (word.map length).sum ≤
          (word.length : Real) * total at ih
        nlinarith
  intro bound
  have hevent : ∀ᶠ n : Nat in Filter.atTop,
      ((bound : Real) * total) / length seed < scale ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop _
  obtain ⟨cutoff, hcutoff⟩ := Filter.eventually_atTop.1 hevent
  have hlarge := hcutoff cutoff le_rfl
  have hlarge' : (bound : Real) * total <
      scale ^ cutoff * length seed := by
    exact (div_lt_iff₀ (hlength seed)).mp hlarge
  refine ⟨cutoff, le_of_not_gt fun hshort ↦ ?_⟩
  have hshortReal :
      ((substitution.iterateLetter cutoff seed).length : Real) < bound := by
    exact_mod_cast hshort
  have hmetricIter :=
    substitution.scalesLetterLengths_power hscale cutoff seed
  simp only [Symbolic.Substitution.power_apply] at hmetricIter
  have hmetricUpper := hupper (substitution.iterateLetter cutoff seed)
  rw [hmetricIter] at hmetricUpper
  have hmul := mul_lt_mul_of_pos_right hshortReal htotal_pos
  nlinarith

/-- The strengthened induction invariant used to build C2.1.  In addition
to the data retained by the published interface, it carries a positive left
metric at one fixed expanding scale, hence enough quantitative information
to construct the next finite return alphabet. -/
private structure FirstLetterStageC2Local
    (baseRank : Nat) (scale : Real) where
  rank : Nat
  rank_pos : 0 < rank
  word : Symbolic.InfiniteWord (Fin rank)
  compositeDecoder : Fin rank → Symbolic.Word (Fin baseRank)
  compositeDecoder_nonempty : ∀ letter, compositeDecoder letter ≠ []
  leftSubstitution : Symbolic.Substitution (Fin rank)
  rightSubstitution : Symbolic.Substitution (Fin rank)
  leftFixed : leftSubstitution.IsFixedPoint word
  rightFixed : rightSubstitution.IsFixedPoint word
  leftMetric : Fin rank → Real
  leftMetric_pos : ∀ letter, 0 < leftMetric letter
  leftMetric_scales :
    SubstitutionScalesLetterLengths leftSubstitution leftMetric scale
  leftPrimitive : IsPrimitiveSubstitution leftSubstitution

/-- One exact first-letter return step together with the next strengthened
stage.  These equalities are deliberately stored, rather than reconstructed
after dependent choice, so the final published tower has literal successor
fields. -/
private structure FirstLetterStepC2Local
    {baseRank : Nat} {scale : Real}
    (current : FirstLetterStageC2Local baseRank scale) where
  next : FirstLetterStageC2Local baseRank scale
  decomposition : Symbolic.ReturnDecomposition current.word
    [current.word.head] next.rank
  word_eq : decomposition.derived = next.word
  leftFactorization : PrefixReturnSubstitutionFactorization
    current.leftSubstitution decomposition
  rightFactorization : PrefixReturnSubstitutionFactorization
    current.rightSubstitution decomposition
  left_eq : next.leftSubstitution = leftFactorization.substitution
  right_eq : next.rightSubstitution = rightFactorization.substitution
  decoder_eq : ∀ letter,
    next.compositeDecoder letter =
      (decomposition.blocks letter).flatMap current.compositeDecoder

/-- Every strengthened stage admits another exact first-letter return step. -/
private theorem exists_firstLetterStep_c2
    {baseRank : Nat} {scale : Real} (hone : 1 < scale)
    (current : FirstLetterStageC2Local baseRank scale) :
    Nonempty (FirstLetterStepC2Local current) := by
  classical
  letI : Nonempty (Fin current.rank) :=
    ⟨⟨0, current.rank_pos⟩⟩
  have hleftGrow : ∀ letter : Fin current.rank,
      LetterImagesGrow current.leftSubstitution letter := by
    intro letter
    exact letterImagesGrow_of_positive_metricScaling_c2
      current.leftMetric_pos current.leftMetric_scales hone letter
  obtain ⟨linearConstant, hfactorGaps⟩ :=
    Symbolic.Substitution.primitive_fixedPoint_hasLinearFactorGaps
      current.leftFixed current.leftPrimitive
      (hleftGrow current.word.head)
  have hlinear : Symbolic.IsLinearlyRecurrent current.word
      (linearConstant + 1) :=
    Symbolic.isLinearlyRecurrent_of_hasLinearFactorGaps hfactorGaps
  have hmarker : Symbolic.InfiniteFactorAt current.word
      [current.word.head] 0 := by
    simp [Symbolic.InfiniteFactorAt, Stream'.take_succ]
  obtain ⟨nextRank, ⟨decomposition⟩⟩ :=
    linearlyRecurrent_returnDecomposition hlinear hmarker (by simp)
  letI : Nonempty (Fin nextRank) :=
    ⟨⟨0, decomposition.rank_pos⟩⟩
  obtain ⟨leftFactorization⟩ :=
    exists_prefixReturnSubstitutionFactorization
      current.leftFixed decomposition
  obtain ⟨rightFactorization⟩ :=
    exists_prefixReturnSubstitutionFactorization
      current.rightFixed decomposition
  let nextMetric : Fin nextRank → Real := fun letter ↦
    wordMetricLength current.leftMetric (decomposition.blocks letter)
  have hnextMetricPos : ∀ letter : Fin nextRank,
      0 < nextMetric letter := by
    exact leftFactorization.returnMetric_pos
      current.leftMetric current.leftMetric_pos
  have hnextScale : SubstitutionScalesLetterLengths
      leftFactorization.substitution nextMetric scale := by
    exact leftFactorization.scalesReturnMetric current.leftMetric_scales
  have hnextGrow : ∀ letter : Fin nextRank,
      LetterImagesGrow leftFactorization.substitution letter := by
    intro letter
    exact letterImagesGrow_of_positive_metricScaling_c2
      hnextMetricPos hnextScale hone letter
  have hderivedUniform : Symbolic.IsUniformlyRecurrent
      decomposition.derived :=
    decomposition.uniformlyRecurrent_derived hlinear.2.1
  have hnextPrimitive :
      IsPrimitiveSubstitution leftFactorization.substitution :=
    Symbolic.Substitution.primitive_of_fixed_uniform_all_images_grow
      leftFactorization.fixed hderivedUniform
      decomposition.every_letter_occurs hnextGrow
  let nextDecoder : Fin nextRank → Symbolic.Word (Fin baseRank) :=
    fun letter ↦
      (decomposition.blocks letter).flatMap current.compositeDecoder
  have hnextDecoderNonempty : ∀ letter : Fin nextRank,
      nextDecoder letter ≠ [] := by
    intro letter hempty
    obtain ⟨head, tail, hblock⟩ := List.exists_cons_of_ne_nil
      (decomposition.blocks_are_returns letter).2.1
    have hdecodedHead : current.compositeDecoder head = [] := by
      change (decomposition.blocks letter).flatMap
        current.compositeDecoder = [] at hempty
      rw [hblock, List.flatMap_cons] at hempty
      exact (List.append_eq_nil_iff.mp hempty).1
    exact current.compositeDecoder_nonempty head hdecodedHead
  let next : FirstLetterStageC2Local baseRank scale := {
    rank := nextRank
    rank_pos := decomposition.rank_pos
    word := decomposition.derived
    compositeDecoder := nextDecoder
    compositeDecoder_nonempty := hnextDecoderNonempty
    leftSubstitution := leftFactorization.substitution
    rightSubstitution := rightFactorization.substitution
    leftFixed := leftFactorization.fixed
    rightFixed := rightFactorization.fixed
    leftMetric := nextMetric
    leftMetric_pos := hnextMetricPos
    leftMetric_scales := hnextScale
    leftPrimitive := hnextPrimitive }
  exact ⟨{
    next := next
    decomposition := decomposition
    word_eq := rfl
    leftFactorization := leftFactorization
    rightFactorization := rightFactorization
    left_eq := rfl
    right_eq := rfl
    decoder_eq := fun _ ↦ rfl }⟩

/-- Leaf C2.1: build the infinite first-letter derivation and all composite
decoders from the exact common-level systems. -/
theorem alignedSystems_have_iteratedFirstLetterDerivedSystems
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    (refinements : AlignedNestedIntertwiningData aligned)
    (_notPeriodicLanguage :
      ¬ Symbolic.HasPeriodicRecurrentLanguage data.word) :
    Nonempty (IteratedFirstLetterDerivedSystems refinements) := by
  classical
  let baseRank :=
    family.infrastructure.decompositions.rank aligned.commonLevel
  let baseDecomposition :=
    family.infrastructure.decompositions.decomposition aligned.commonLevel
  let scale : Real := a ^ input.powered.powerA
  have hscale : 1 < scale := by
    dsimp [scale]
    exact one_lt_pow₀ data.one_lt_a input.powered.powerA_pos.ne'
  let baseLeftFactorization :=
    family.infrastructure.left.factorization aligned.commonLevel
  let baseRightFactorization :=
    family.infrastructure.right.factorization aligned.commonLevel
  let baseMetric : Fin baseRank → Real := fun letter ↦
    wordMetricLength data.letterLength (baseDecomposition.blocks letter)
  have hbaseMetricPos : ∀ letter : Fin baseRank,
      0 < baseMetric letter := by
    exact baseLeftFactorization.returnMetric_pos
      data.letterLength data.letterLength_pos
  have hsourceScale : SubstitutionScalesLetterLengths
      (data.substitutionA.power input.powered.powerA)
      data.letterLength scale := by
    dsimp [scale]
    exact data.substitutionA.scalesLetterLengths_power
      data.imageMetricA input.powered.powerA
  have hbaseScale : SubstitutionScalesLetterLengths
      baseLeftFactorization.substitution baseMetric scale := by
    exact baseLeftFactorization.scalesReturnMetric hsourceScale
  have hbasePrimitive :
      IsPrimitiveSubstitution baseLeftFactorization.substitution := by
    exact family.infrastructure.left.primitive aligned.commonLevel
  let base : FirstLetterStageC2Local baseRank scale := {
    rank := baseRank
    rank_pos := baseDecomposition.rank_pos
    word := baseDecomposition.derived
    compositeDecoder := fun letter ↦ [letter]
    compositeDecoder_nonempty := by simp
    leftSubstitution := baseLeftFactorization.substitution
    rightSubstitution := baseRightFactorization.substitution
    leftFixed := baseLeftFactorization.fixed
    rightFixed := baseRightFactorization.fixed
    leftMetric := baseMetric
    leftMetric_pos := hbaseMetricPos
    leftMetric_scales := hbaseScale
    leftPrimitive := hbasePrimitive }
  let successor : ∀ current : FirstLetterStageC2Local baseRank scale,
      FirstLetterStepC2Local current := fun current ↦
    Classical.choice (exists_firstLetterStep_c2 hscale current)
  let stages : Nat → FirstLetterStageC2Local baseRank scale :=
    fun stage ↦ Nat.rec base
      (fun _ current ↦ (successor current).next) stage
  let rank : Nat → Nat := fun stage ↦ (stages stage).rank
  let word : ∀ stage, Symbolic.InfiniteWord (Fin (rank stage)) :=
    fun stage ↦ (stages stage).word
  let baseRelabel : Equiv (Fin (rank 0)) (Fin baseRank) := Equiv.refl _
  let stepDecomposition : ∀ stage,
      Symbolic.ReturnDecomposition (word stage) [(word stage).head]
        (rank (stage + 1)) := fun stage ↦
    (successor (stages stage)).decomposition
  let compositeDecoder : ∀ stage,
      Fin (rank stage) → Symbolic.Word (Fin (rank 0)) := fun stage ↦
    (stages stage).compositeDecoder
  let leftSubstitution : ∀ stage,
      Symbolic.Substitution (Fin (rank stage)) := fun stage ↦
    (stages stage).leftSubstitution
  let rightSubstitution : ∀ stage,
      Symbolic.Substitution (Fin (rank stage)) := fun stage ↦
    (stages stage).rightSubstitution
  let leftStepFactorization : ∀ stage,
      PrefixReturnSubstitutionFactorization (leftSubstitution stage)
        (stepDecomposition stage) := fun stage ↦
    (successor (stages stage)).leftFactorization
  let rightStepFactorization : ∀ stage,
      PrefixReturnSubstitutionFactorization (rightSubstitution stage)
        (stepDecomposition stage) := fun stage ↦
    (successor (stages stage)).rightFactorization
  exact ⟨{
    rank := rank
    rank_pos := fun stage ↦ (stages stage).rank_pos
    word := word
    baseRelabel := baseRelabel
    base_word_eq := by
      intro position
      rfl
    stepDecomposition := stepDecomposition
    step_word_eq := by
      intro stage
      exact (successor (stages stage)).word_eq
    compositeDecoder := compositeDecoder
    compositeDecoder_zero := by
      intro letter
      rfl
    compositeDecoder_succ := by
      intro stage letter
      exact (successor (stages stage)).decoder_eq letter
    compositeDecoder_nonempty := fun stage ↦
      (stages stage).compositeDecoder_nonempty
    leftSubstitution := leftSubstitution
    rightSubstitution := rightSubstitution
    leftFixed := fun stage ↦ (stages stage).leftFixed
    rightFixed := fun stage ↦ (stages stage).rightFixed
    leftStepFactorization := leftStepFactorization
    rightStepFactorization := rightStepFactorization
    left_succ_eq := by
      intro stage
      exact (successor (stages stage)).left_eq
    right_succ_eq := by
      intro stage
      exact (successor (stages stage)).right_eq
    left_base_eq := by
      intro letter
      simp [leftSubstitution, stages, base, baseRelabel,
        baseLeftFactorization, PoweredReturnTowerAtScale.substitution]
    right_base_eq := by
      intro letter
      simp [rightSubstitution, stages, base, baseRelabel,
        baseRightFactorization, PoweredReturnTowerAtScale.substitution] }⟩

/-! ### Physical realization of the iterated first-letter tower -/

/-- Decoding a return word of a derived sequence gives a return word at the
composed physical marker.  This is the return-word core of the realization
bridge used by both C2.2 and C2.3. -/
private theorem decodedReturnWord_of_derivedReturnWord_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {outerRank : Nat}
    (outer : Symbolic.ReturnDecomposition word marker outerRank)
    {innerMarker innerBlock : Symbolic.Word (Fin outerRank)}
    (hreturn : Symbolic.IsReturnWord outer.derived innerMarker innerBlock) :
    Symbolic.IsReturnWord word
      (innerMarker.flatMap outer.blocks ++ marker)
      (innerBlock.flatMap outer.blocks) := by
  classical
  let decodedMarker := innerMarker.flatMap outer.blocks
  let decodedBlock := innerBlock.flatMap outer.blocks
  let composedMarker := decodedMarker ++ marker
  have hdecodedBlockNonempty : decodedBlock ≠ [] := by
    intro hempty
    have hinjective := Symbolic.flatMap_returnWords_injective
      outer.blocks_injective outer.blocks_are_returns
    apply hreturn.2.1
    apply hinjective
    simpa [decodedBlock] using hempty
  have hcomposedMarkerNonempty : composedMarker ≠ [] :=
    List.append_ne_nil_of_right_ne_nil decodedMarker outer.marker_ne_nil
  obtain ⟨origin, horigin⟩ := hreturn.2.2.1
  have hfullAt : Symbolic.InfiniteFactorAt word
      (decodedBlock ++ composedMarker) (outer.cut origin) := by
    have hdecoded := outer.decoded_marker_at_cut origin
      (innerBlock ++ innerMarker).length
    rw [horigin] at hdecoded
    simpa [decodedBlock, decodedMarker, composedMarker,
      List.flatMap_append, List.append_assoc] using hdecoded
  have hcomposedPrefix : composedMarker <+:
      decodedBlock ++ composedMarker := by
    obtain ⟨tail, htail⟩ := hreturn.2.2.2.1
    have hmarkerTail : marker <+: tail.flatMap outer.blocks ++ marker :=
      Symbolic.marker_prefix_flatMap_returnWords outer.blocks
        outer.blocks_are_returns tail
    have hlift : decodedMarker ++ marker <+:
        decodedMarker ++ (tail.flatMap outer.blocks ++ marker) :=
      (List.prefix_append_right_inj decodedMarker).mpr hmarkerTail
    have hdecodedEq := congrArg (fun letters ↦
      letters.flatMap outer.blocks) htail
    have hdecodedEq' :
        decodedMarker ++ tail.flatMap outer.blocks =
          decodedBlock ++ decodedMarker := by
      simpa [decodedBlock, decodedMarker, List.flatMap_append] using hdecodedEq
    have hrightEq :
        decodedMarker ++ (tail.flatMap outer.blocks ++ marker) =
          decodedBlock ++ (decodedMarker ++ marker) := by
      rw [← List.append_assoc, hdecodedEq', List.append_assoc]
    rw [hrightEq] at hlift
    change composedMarker <+: decodedBlock ++ composedMarker at hlift
    exact hlift
  refine ⟨hcomposedMarkerNonempty, hdecodedBlockNonempty,
    ⟨outer.cut origin, hfullAt⟩, hcomposedPrefix, ?_⟩
  intro physicalOffset
  constructor
  · intro hfinite
    have hcomposedAt : Symbolic.InfiniteFactorAt word composedMarker
        (outer.cut origin + physicalOffset) :=
      hfullAt.of_finiteFactorAt hfinite
    have hmarkerPrefix : marker <+: composedMarker := by
      exact Symbolic.marker_prefix_flatMap_returnWords outer.blocks
        outer.blocks_are_returns innerMarker
    have hmarkerFinite : Symbolic.FiniteFactorAt composedMarker marker 0 := by
      refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
    have hmarkerAt : Symbolic.InfiniteFactorAt word marker
        (outer.cut origin + physicalOffset) := by
      simpa using hcomposedAt.of_finiteFactorAt hmarkerFinite
    obtain ⟨index, hcutIndex⟩ :=
      outer.marker_occurrence_eq_cut hmarkerAt
    have hphysicalOffsetLe : physicalOffset ≤ decodedBlock.length := by
      have hlength := hfinite.1
      change physicalOffset + composedMarker.length ≤
        (decodedBlock ++ composedMarker).length at hlength
      simp only [List.length_append] at hlength
      omega
    have hinnerBlockAt : Symbolic.InfiniteFactorAt outer.derived
        innerBlock origin := by
      have hprefix : innerBlock <+: innerBlock ++ innerMarker :=
        List.prefix_append _ _
      have hfinitePrefix : Symbolic.FiniteFactorAt
          (innerBlock ++ innerMarker) innerBlock 0 := by
        refine ⟨by simpa using hprefix.length_le, ?_⟩
        simpa using (List.prefix_iff_eq_take.mp hprefix).symm
      exact horigin.of_finiteFactorAt hfinitePrefix
    have hcutEnd : outer.cut (origin + innerBlock.length) =
        outer.cut origin + decodedBlock.length := by
      have hcut := outer.cut_add origin innerBlock.length
      rw [hinnerBlockAt] at hcut
      simpa [decodedBlock] using hcut
    have horiginLe : origin ≤ index := by
      by_contra hnot
      have hstrict := outer.cut_strictMono
        (by omega : index < origin)
      rw [hcutIndex] at hstrict
      omega
    have hindexLe : index ≤ origin + innerBlock.length := by
      by_contra hnot
      have hstrict := outer.cut_strictMono
        (by omega : origin + innerBlock.length < index)
      rw [hcutIndex, hcutEnd] at hstrict
      omega
    let derivedOffset := index - origin
    have hindexEq : origin + derivedOffset = index := by
      simp [derivedOffset, Nat.add_sub_of_le horiginLe]
    have hderivedOffsetLe : derivedOffset ≤ innerBlock.length := by
      omega
    have hcomposedAtCut : Symbolic.InfiniteFactorAt word
        (innerMarker.flatMap outer.blocks ++ marker) (outer.cut index) := by
      rw [hcutIndex]
      simpa [decodedMarker, composedMarker] using hcomposedAt
    have hinnerMarkerAt : Symbolic.InfiniteFactorAt outer.derived
        innerMarker index :=
      outer.derived_factor_of_decoded_marker_at_cut
        innerMarker index hcomposedAtCut
    have hinnerMarkerAtOffset : Symbolic.InfiniteFactorAt outer.derived
        innerMarker (origin + derivedOffset) := by
      rw [hindexEq]
      exact hinnerMarkerAt
    have hwithin : derivedOffset + innerMarker.length ≤
        (innerBlock ++ innerMarker).length := by
      simp only [List.length_append]
      omega
    have hinnerFinite : Symbolic.FiniteFactorAt
        (innerBlock ++ innerMarker) innerMarker derivedOffset :=
      Symbolic.finiteFactorAt_of_nested_infiniteFactorAt horigin
        hinnerMarkerAtOffset hwithin
    rcases (hreturn.2.2.2.2 derivedOffset).mp hinnerFinite with
      hzero | hend
    · left
      have hcutIndex' := hcutIndex
      rw [← hindexEq, hzero, Nat.add_zero] at hcutIndex'
      omega
    · right
      have hcutIndex' := hcutIndex
      rw [← hindexEq, hend] at hcutIndex'
      rw [hcutEnd] at hcutIndex'
      change physicalOffset = decodedBlock.length
      omega
  · rintro (rfl | rfl)
    · change Symbolic.FiniteFactorAt
        (decodedBlock ++ composedMarker) composedMarker 0
      refine ⟨by simpa using hcomposedPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hcomposedPrefix).symm
    · change Symbolic.FiniteFactorAt
        (decodedBlock ++ composedMarker) composedMarker decodedBlock.length
      simp [Symbolic.FiniteFactorAt]

/-- Compose a physical return decomposition with a return decomposition of
its derived word. -/
private def composeReturnDecompositions_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {outerMarker : Symbolic.Word alphabet} {outerRank : Nat}
    (outer : Symbolic.ReturnDecomposition word outerMarker outerRank)
    {innerMarker : Symbolic.Word (Fin outerRank)} {innerRank : Nat}
    (inner : Symbolic.ReturnDecomposition outer.derived
      innerMarker innerRank) :
    Symbolic.ReturnDecomposition word
      (innerMarker.flatMap outer.blocks ++ outerMarker) innerRank where
  rank_pos := inner.rank_pos
  marker_ne_nil :=
    List.append_ne_nil_of_right_ne_nil _ outer.marker_ne_nil
  marker_at_zero := by
    have hdecoded := outer.decoded_marker_at_cut 0 innerMarker.length
    have hinnerZero : outer.derived.take innerMarker.length = innerMarker := by
      simpa [Symbolic.InfiniteFactorAt] using inner.marker_at_zero
    rw [outer.cut_zero, Stream'.drop_zero, hinnerZero] at hdecoded
    exact hdecoded
  blocks := fun letter ↦ (inner.blocks letter).flatMap outer.blocks
  blocks_injective := by
    intro left right heq
    apply inner.blocks_injective
    exact (Symbolic.flatMap_returnWords_injective
      outer.blocks_injective outer.blocks_are_returns) heq
  blocks_are_returns := fun letter ↦
    decodedReturnWord_of_derivedReturnWord_c2 outer
      (inner.blocks_are_returns letter)
  derived := inner.derived
  cut := fun position ↦ outer.cut (inner.cut position)
  cut_zero := by rw [inner.cut_zero, outer.cut_zero]
  cut_succ := by
    intro position
    have hinnerBlock := inner.block_at_cut position
    have hcut := outer.cut_add (inner.cut position)
      (inner.blocks (inner.derived position)).length
    rw [hinnerBlock] at hcut
    rw [inner.cut_succ]
    exact hcut
  block_at_cut := by
    intro position
    have hinnerBlock := inner.block_at_cut position
    have hdecode := outer.flatMap_drop_take_derived
      (inner.cut position) (inner.blocks (inner.derived position)).length
    rw [hinnerBlock] at hdecode
    exact hdecode.symm

/-- Transport an arbitrary-prefix factorization when only the ambient fixed
word of its return decomposition has been rewritten. -/
private def castPrefixReturnFactorizationWord_c2
    {alphabet : Type*} {source : Symbolic.Substitution alphabet}
    {left right : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (hword : left = right)
    (decomposition : Symbolic.ReturnDecomposition left marker rank)
    (factorization : PrefixReturnSubstitutionFactorization
      source decomposition) :
    PrefixReturnSubstitutionFactorization source
      (Symbolic.Substitution.castReturnDecompositionWord
        hword decomposition) := by
  subst right
  exact factorization

@[simp] private theorem castPrefixReturnFactorizationWord_substitution_c2
    {alphabet : Type*} {source : Symbolic.Substitution alphabet}
    {left right : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (hword : left = right)
    (decomposition : Symbolic.ReturnDecomposition left marker rank)
    (factorization : PrefixReturnSubstitutionFactorization
      source decomposition) :
    (castPrefixReturnFactorizationWord_c2 hword decomposition
      factorization).substitution = factorization.substitution := by
  subst right
  rfl

/-- A blockwise decoding equation automatically extends from letters to
finite words. -/
private theorem mapWord_flatMap_blocks_c2
    {sourceAlphabet returnAlphabet : Type*}
    (source : Symbolic.Substitution sourceAlphabet)
    (induced : Symbolic.Substitution returnAlphabet)
    (blocks : returnAlphabet → Symbolic.Word sourceAlphabet)
    (hletter : ∀ letter,
      (induced letter).flatMap blocks = source.mapWord (blocks letter)) :
    ∀ letters : Symbolic.Word returnAlphabet,
      (induced.mapWord letters).flatMap blocks =
        source.mapWord (letters.flatMap blocks) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      rw [Symbolic.Substitution.mapWord_cons, List.flatMap_append,
        hletter, List.flatMap_cons,
        Symbolic.Substitution.mapWord_append, ih]

/-- If an outer induced substitution decodes through an outer return
decomposition, then the next induced substitution decodes through the
composite return decomposition. -/
private theorem composedFactor_decodes_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {outerMarker : Symbolic.Word alphabet} {outerRank : Nat}
    (outer : Symbolic.ReturnDecomposition word outerMarker outerRank)
    {source : Symbolic.Substitution alphabet}
    {outerSubstitution : Symbolic.Substitution (Fin outerRank)}
    (houter : ∀ letter,
      (outerSubstitution letter).flatMap outer.blocks =
        source.mapWord (outer.blocks letter))
    {innerMarker : Symbolic.Word (Fin outerRank)} {innerRank : Nat}
    (inner : Symbolic.ReturnDecomposition outer.derived
      innerMarker innerRank)
    (factorization : PrefixReturnSubstitutionFactorization
      outerSubstitution inner) (letter : Fin innerRank) :
    (factorization.substitution letter).flatMap
        (composeReturnDecompositions_c2 outer inner).blocks =
      source.mapWord
        ((composeReturnDecompositions_c2 outer inner).blocks
          letter) := by
  change (factorization.factor letter).flatMap
      (fun innerLetter => (inner.blocks innerLetter).flatMap outer.blocks) =
    source.mapWord ((inner.blocks letter).flatMap outer.blocks)
  rw [← List.flatMap_assoc, factorization.factor_decodes]
  exact mapWord_flatMap_blocks_c2 source outerSubstitution
    outer.blocks houter (inner.blocks letter)

/-- A realization of one first-letter stage as a literal prefix-return
decomposition of the original recurrent core.  The two decoding equations
are the only induction data needed by C2.2. -/
private structure FirstLetterPhysicalStageC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) where
  marker : Symbolic.Word data.alphabet
  decomposition : Symbolic.ReturnDecomposition input.core.word marker
    (tower.rank stage)
  derived_eq : decomposition.derived = tower.word stage
  left_decodes : ∀ letter,
    (tower.leftSubstitution stage letter).flatMap decomposition.blocks =
      (data.substitutionA.power input.powered.powerA).mapWord

        (decomposition.blocks letter)
  right_decodes : ∀ letter,
    (tower.rightSubstitution stage letter).flatMap decomposition.blocks =
      (data.substitutionB.power input.powered.powerB).mapWord
        (decomposition.blocks letter)

/-- Stage zero is the common canonical level, with its return alphabet
renamed by the tower's base equivalence. -/
private def firstLetterPhysicalBase_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements) :
    FirstLetterPhysicalStageC2Local tower 0 := by
  classical
  let canonical :=
    family.infrastructure.decompositions.decomposition aligned.commonLevel
  let relabeled : Symbolic.ReturnDecomposition input.core.word
      (family.infrastructure.markers.marker aligned.commonLevel)
      (tower.rank 0) := {
    rank_pos := tower.rank_pos 0
    marker_ne_nil := canonical.marker_ne_nil
    marker_at_zero := canonical.marker_at_zero
    blocks := fun letter => canonical.blocks (tower.baseRelabel letter)
    blocks_injective := canonical.blocks_injective.comp
      tower.baseRelabel.injective
    blocks_are_returns := fun letter =>
      canonical.blocks_are_returns (tower.baseRelabel letter)
    derived := tower.word 0
    cut := canonical.cut
    cut_zero := canonical.cut_zero
    cut_succ := by
      intro position
      rw [canonical.cut_succ, ← tower.base_word_eq position]
    block_at_cut := by
      intro position
      simpa [tower.base_word_eq position] using
        canonical.block_at_cut position }
  refine {
    marker := family.infrastructure.markers.marker aligned.commonLevel
    decomposition := relabeled
    derived_eq := rfl
    left_decodes := ?_
    right_decodes := ?_ }
  · intro letter
    change (tower.leftSubstitution 0 letter).flatMap
        (fun current => canonical.blocks (tower.baseRelabel current)) =
      (data.substitutionA.power input.powered.powerA).mapWord
        (canonical.blocks (tower.baseRelabel letter))
    rw [← List.flatMap_map, tower.left_base_eq]
    exact (family.infrastructure.left.factorization
      aligned.commonLevel).factor_decodes (tower.baseRelabel letter)
  · intro letter
    change (tower.rightSubstitution 0 letter).flatMap
        (fun current => canonical.blocks (tower.baseRelabel current)) =
      (data.substitutionB.power input.powered.powerB).mapWord
        (canonical.blocks (tower.baseRelabel letter))
    rw [← List.flatMap_map, tower.right_base_eq]
    exact (family.infrastructure.right.factorization
      aligned.commonLevel).factor_decodes (tower.baseRelabel letter)

/-- Compose one physical stage with the displayed first-letter return step. -/
private def firstLetterPhysicalSucc_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) (current : FirstLetterPhysicalStageC2Local tower stage) :
    FirstLetterPhysicalStageC2Local tower (stage + 1) := by
  classical
  let inner := Symbolic.Substitution.castReturnDecompositionWord
    current.derived_eq.symm (tower.stepDecomposition stage)
  let leftFactorization := castPrefixReturnFactorizationWord_c2
    current.derived_eq.symm (tower.stepDecomposition stage)
      (tower.leftStepFactorization stage)
  let rightFactorization := castPrefixReturnFactorizationWord_c2
    current.derived_eq.symm (tower.stepDecomposition stage)
      (tower.rightStepFactorization stage)
  let composed := composeReturnDecompositions_c2
    current.decomposition inner
  refine {
    marker := [(tower.word stage).head].flatMap
      current.decomposition.blocks ++ current.marker
    decomposition := composed
    derived_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }
  · change inner.derived = tower.word (stage + 1)
    rw [Symbolic.Substitution.castReturnDecompositionWord_derived]
    exact tower.step_word_eq stage
  · intro letter
    rw [tower.left_succ_eq stage]
    have hfactorization : leftFactorization.substitution =
        (tower.leftStepFactorization stage).substitution := by
      simp [leftFactorization]
    rw [← hfactorization]
    change (leftFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_c2 current.decomposition
      current.left_decodes inner leftFactorization letter
  · intro letter
    rw [tower.right_succ_eq stage]
    have hfactorization : rightFactorization.substitution =
        (tower.rightStepFactorization stage).substitution := by
      simp [rightFactorization]
    rw [← hfactorization]
    change (rightFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_c2 current.decomposition
      current.right_decodes inner rightFactorization letter

/-- The physical realization at every finite first-letter stage. -/
private def firstLetterPhysicalStages_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements) :
    ∀ stage, FirstLetterPhysicalStageC2Local tower stage
  | 0 => firstLetterPhysicalBase_c2 tower
  | stage + 1 => firstLetterPhysicalSucc_c2 tower stage
      (firstLetterPhysicalStages_c2 tower stage)

/-- An arbitrary return word occurring at a cut of a complete return
decomposition is exactly the block named at that cut. -/
private theorem returnWord_eq_block_at_cut_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker block : Symbolic.Word alphabet} {rank : Nat}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (hreturn : Symbolic.IsReturnWord word marker block)
    (index : Nat)
    (hat : Symbolic.InfiniteFactorAt word (block ++ marker)
      (decomposition.cut index)) :
    block = decomposition.blocks (decomposition.derived index) := by
  have hmarkerAtEnd : Symbolic.InfiniteFactorAt word marker
      (decomposition.cut index + block.length) := by
    have hfinite : Symbolic.FiniteFactorAt
        (block ++ marker) marker block.length := by
      simp [Symbolic.FiniteFactorAt]
    exact hat.of_finiteFactorAt hfinite
  obtain ⟨endpoint, hendpoint⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAtEnd
  have hblockPositive : 0 < block.length :=
    List.length_pos_of_ne_nil hreturn.2.1
  have hendpointGt : index < endpoint := by
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hendpoint]
    omega
  have hnextLe : index + 1 ≤ endpoint := by omega
  have hlengthLe :
      (decomposition.blocks (decomposition.derived index)).length ≤
        block.length := by
    have hcuts := decomposition.cut_strictMono.monotone hnextLe
    rw [decomposition.cut_succ, hendpoint] at hcuts
    omega
  have hreverseLength : block.length ≤
      (decomposition.blocks (decomposition.derived index)).length := by
    by_contra hnot
    have hstrict :
        (decomposition.blocks (decomposition.derived index)).length <
          block.length := by omega
    have hnextMarker := decomposition.marker_at_cut (index + 1)
    have hnextPosition : decomposition.cut (index + 1) =
        decomposition.cut index +
          (decomposition.blocks (decomposition.derived index)).length :=
      decomposition.cut_succ index
    have hfinite : Symbolic.FiniteFactorAt
        (block ++ marker) marker
          (decomposition.blocks (decomposition.derived index)).length := by
      apply Symbolic.finiteFactorAt_of_nested_infiniteFactorAt hat
      · rw [hnextPosition] at hnextMarker
        exact hnextMarker
      · simp only [List.length_append]
        omega
    rcases (hreturn.2.2.2.2
        (decomposition.blocks (decomposition.derived index)).length).mp
          hfinite with hzero | hend
    · exact (decomposition.block_length_pos
        (decomposition.derived index)).ne' hzero
    · omega
  have hlength : block.length =
      (decomposition.blocks (decomposition.derived index)).length := by
    omega
  have hblockAt : Symbolic.InfiniteFactorAt word block
      (decomposition.cut index) := by
    have hfinite : Symbolic.FiniteFactorAt (block ++ marker) block 0 := by
      simp [Symbolic.FiniteFactorAt]
    simpa using hat.of_finiteFactorAt hfinite
  have hactual := decomposition.block_at_cut index
  rw [Symbolic.InfiniteFactorAt] at hblockAt hactual
  rw [← hlength] at hactual
  exact hblockAt.symm.trans hactual

/-- Two complete return decompositions of the same word at the same marker
differ only by a unique relabeling of their return alphabets. -/
private structure SameMarkerReturnRelabelingC2Local
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {leftRank rightRank : Nat}
    (left : Symbolic.ReturnDecomposition word marker leftRank)
    (right : Symbolic.ReturnDecomposition word marker rightRank) where
  relabel : Fin leftRank ≃ Fin rightRank
  blocks_eq : ∀ letter,
    right.blocks (relabel letter) = left.blocks letter
  word_eq : ∀ position,
    relabel (left.derived position) = right.derived position

private theorem returnDecompositions_sameMarker_relabel_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {leftRank rightRank : Nat}
    (left : Symbolic.ReturnDecomposition word marker leftRank)
    (right : Symbolic.ReturnDecomposition word marker rightRank) :
    Nonempty (SameMarkerReturnRelabelingC2Local left right) := by
  classical
  have hexistsRight : ∀ letter : Fin leftRank,
      ∃ target : Fin rightRank,
        right.blocks target = left.blocks letter := by
    intro letter
    obtain ⟨position, hat⟩ :=
      (left.blocks_are_returns letter).2.2.1
    have hmarkerPrefix := (left.blocks_are_returns letter).2.2.2.1
    have hfinite : Symbolic.FiniteFactorAt
        (left.blocks letter ++ marker) marker 0 := by
      refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
    have hmarkerAt : Symbolic.InfiniteFactorAt word marker position := by
      simpa using hat.of_finiteFactorAt hfinite
    obtain ⟨index, hcut⟩ :=
      right.marker_occurrence_eq_cut hmarkerAt
    have hatCut : Symbolic.InfiniteFactorAt word
        (left.blocks letter ++ marker) (right.cut index) := by
      rw [hcut]
      exact hat
    exact ⟨right.derived index,
      (returnWord_eq_block_at_cut_c2 right
        (left.blocks_are_returns letter) index hatCut).symm⟩
  let toFun : Fin leftRank → Fin rightRank := fun letter =>
    Classical.choose (hexistsRight letter)
  have hblocks : ∀ letter,
      right.blocks (toFun letter) = left.blocks letter := by
    intro letter
    exact Classical.choose_spec (hexistsRight letter)
  have htoFunInjective : Function.Injective toFun := by
    intro leftLetter rightLetter heq
    apply left.blocks_injective
    rw [← hblocks leftLetter, ← hblocks rightLetter, heq]
  have htoFunSurjective : Function.Surjective toFun := by
    intro target
    obtain ⟨position, hat⟩ :=
      (right.blocks_are_returns target).2.2.1
    have hmarkerPrefix := (right.blocks_are_returns target).2.2.2.1
    have hfinite : Symbolic.FiniteFactorAt
        (right.blocks target ++ marker) marker 0 := by
      refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
    have hmarkerAt : Symbolic.InfiniteFactorAt word marker position := by
      simpa using hat.of_finiteFactorAt hfinite
    obtain ⟨index, hcut⟩ := left.marker_occurrence_eq_cut hmarkerAt
    have hatCut : Symbolic.InfiniteFactorAt word
        (right.blocks target ++ marker) (left.cut index) := by
      rw [hcut]
      exact hat
    let source := left.derived index
    have hsource : left.blocks source = right.blocks target :=
      (returnWord_eq_block_at_cut_c2 left
        (right.blocks_are_returns target) index hatCut).symm
    refine ⟨source, ?_⟩
    apply right.blocks_injective
    rw [hblocks source, hsource]
  let relabel : Fin leftRank ≃ Fin rightRank :=
    Equiv.ofBijective toFun ⟨htoFunInjective, htoFunSurjective⟩
  have hblocksRelabel : ∀ letter,
      right.blocks (relabel letter) = left.blocks letter := hblocks
  have hcuts : ∀ position, left.cut position = right.cut position := by
    intro position
    induction position with
    | zero => rw [left.cut_zero, right.cut_zero]
    | succ position ih =>
        have hleftAt := left.block_marker_at_cut position
        have hleftAtRight : Symbolic.InfiniteFactorAt word
            (left.blocks (left.derived position) ++ marker)
            (right.cut position) := by
          rw [← ih]
          exact hleftAt
        have hblock := returnWord_eq_block_at_cut_c2 right
          (left.blocks_are_returns (left.derived position)) position
            hleftAtRight
        have hletter : relabel (left.derived position) =
            right.derived position := by
          apply right.blocks_injective
          rw [hblocksRelabel]
          exact hblock

        rw [left.cut_succ, right.cut_succ, ih, ← hletter,
          hblocksRelabel]
  have hword : ∀ position,
      relabel (left.derived position) = right.derived position := by
    intro position
    have hleftAt := left.block_marker_at_cut position
    have hleftAtRight : Symbolic.InfiniteFactorAt word
        (left.blocks (left.derived position) ++ marker)
        (right.cut position) := by
      rw [← hcuts position]
      exact hleftAt
    have hblock := returnWord_eq_block_at_cut_c2 right
      (left.blocks_are_returns (left.derived position)) position
        hleftAtRight
    apply right.blocks_injective
    rw [hblocksRelabel]
    exact hblock
  exact ⟨{
    relabel := relabel
    blocks_eq := hblocksRelabel
    word_eq := hword }⟩

/-- One first-letter stage, identified with the canonical cofinal-prefix
return system at the length of its physical marker. -/
private structure FirstLetterCanonicalStageC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) where
  level : Nat
  level_length : level + 1 =
    (firstLetterPhysicalStages_c2 tower stage).marker.length
  relabel : Fin (tower.rank stage) ≃ Fin
    (family.infrastructure.decompositions.rank level)
  word_relabels : ∀ position,
    relabel (tower.word stage position) =
      (family.infrastructure.decompositions.decomposition level).derived
        position
  left_relabels : ∀ letter,
    (tower.leftSubstitution stage letter).map relabel =
      family.infrastructure.left.substitution level (relabel letter)
  right_relabels : ∀ letter,
    (tower.rightSubstitution stage letter).map relabel =
      family.infrastructure.right.substitution level (relabel letter)

/-- Transport only the marker parameter of a return decomposition. -/
private def castReturnDecompositionMarker_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {left right : Symbolic.Word alphabet} {rank : Nat}
    (hmarker : left = right)
    (decomposition : Symbolic.ReturnDecomposition word left rank) :
    Symbolic.ReturnDecomposition word right rank := by
  subst right
  exact decomposition

@[simp] private theorem castReturnDecompositionMarker_blocks_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {left right : Symbolic.Word alphabet} {rank : Nat}
    (hmarker : left = right)
    (decomposition : Symbolic.ReturnDecomposition word left rank) :
    (castReturnDecompositionMarker_c2 hmarker decomposition).blocks =
      decomposition.blocks := by
  subst right
  rfl

@[simp] private theorem castReturnDecompositionMarker_derived_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {left right : Symbolic.Word alphabet} {rank : Nat}
    (hmarker : left = right)
    (decomposition : Symbolic.ReturnDecomposition word left rank) :
    (castReturnDecompositionMarker_c2 hmarker decomposition).derived =
      decomposition.derived := by
  subst right
  rfl

/-- Rename the finite return alphabet of a complete return decomposition. -/
private def reindexReturnDecomposition_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {leftRank rightRank : Nat}
    (relabel : Fin leftRank ≃ Fin rightRank)
    (decomposition : Symbolic.ReturnDecomposition word marker leftRank) :
    Symbolic.ReturnDecomposition word marker rightRank where
  rank_pos := by
    have hwitness := relabel ⟨0, decomposition.rank_pos⟩
    exact Nat.zero_lt_of_lt hwitness.isLt
  marker_ne_nil := decomposition.marker_ne_nil
  marker_at_zero := decomposition.marker_at_zero
  blocks := fun letter => decomposition.blocks (relabel.symm letter)
  blocks_injective := by
    intro left right heq
    apply relabel.symm.injective
    exact decomposition.blocks_injective heq
  blocks_are_returns := fun letter =>
    decomposition.blocks_are_returns (relabel.symm letter)
  derived := fun position => relabel (decomposition.derived position)
  cut := decomposition.cut
  cut_zero := decomposition.cut_zero
  cut_succ := by
    intro position
    simpa using decomposition.cut_succ position
  block_at_cut := by
    intro position
    simpa using decomposition.block_at_cut position

@[simp] private theorem reindexReturnDecomposition_blocks_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {leftRank rightRank : Nat}
    (relabel : Fin leftRank ≃ Fin rightRank)
    (decomposition : Symbolic.ReturnDecomposition word marker leftRank)
    (letter : Fin rightRank) :
    (reindexReturnDecomposition_c2 relabel decomposition).blocks
        letter = decomposition.blocks (relabel.symm letter) := rfl

@[simp] private theorem reindexReturnDecomposition_derived_c2
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {leftRank rightRank : Nat}
    (relabel : Fin leftRank ≃ Fin rightRank)
    (decomposition : Symbolic.ReturnDecomposition word marker leftRank)
    (position : Nat) :
    (reindexReturnDecomposition_c2 relabel decomposition).derived
        position = relabel (decomposition.derived position) := rfl

@[simp] private theorem castReturnDecompositionWord_blocks_c2
    {alphabet : Type*}
    {left right : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (hword : left = right)
    (decomposition : Symbolic.ReturnDecomposition left marker rank)
    (letter : Fin rank) :
    (Symbolic.Substitution.castReturnDecompositionWord
      hword decomposition).blocks letter = decomposition.blocks letter := by
  subst right
  rfl

/-- Every physical stage is one of the canonical cofinal-prefix systems,
up to the unique return-alphabet relabeling. -/
private theorem firstLetterPhysical_has_canonicalStage_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat)
    (physical : FirstLetterPhysicalStageC2Local tower stage)
    (hphysical : physical =
      firstLetterPhysicalStages_c2 tower stage) :
    Nonempty (FirstLetterCanonicalStageC2Local tower stage) := by
  classical
  let level := physical.marker.length - 1
  have hmarkerLengthPositive : 0 < physical.marker.length :=
    List.length_pos_of_ne_nil physical.decomposition.marker_ne_nil
  have hlevelLength : level + 1 = physical.marker.length := by
    dsimp [level]
    omega
  have hphysicalMarker : input.core.word.take physical.marker.length =
      physical.marker := by
    simpa [Symbolic.InfiniteFactorAt] using
      physical.decomposition.marker_at_zero
  have hmarker : family.infrastructure.markers.marker level =
      physical.marker := by
    rw [family.infrastructure.markers.marker_eq_take, hlevelLength]
    exact hphysicalMarker
  let canonical : Symbolic.ReturnDecomposition input.core.word
      physical.marker
      (family.infrastructure.decompositions.rank level) :=
    castReturnDecompositionMarker_c2 hmarker
      (family.infrastructure.decompositions.decomposition level)
  let comparison := Classical.choice
    (returnDecompositions_sameMarker_relabel_c2
      physical.decomposition canonical)
  let relabel := comparison.relabel
  have hword : ∀ position,
      relabel (tower.word stage position) =
        (family.infrastructure.decompositions.decomposition level).derived
          position := by
    intro position
    rw [← physical.derived_eq]
    have hcomparison := comparison.word_eq position
    change relabel (physical.decomposition.derived position) =
      canonical.derived position at hcomparison
    simpa [canonical] using hcomparison
  have hleft : ∀ letter,
      (tower.leftSubstitution stage letter).map relabel =
        family.infrastructure.left.substitution level (relabel letter) := by
    intro letter
    apply Symbolic.flatMap_returnWords_injective
      (family.infrastructure.decompositions.decomposition level).blocks_injective
      (family.infrastructure.decompositions.decomposition level).blocks_are_returns
    change ((tower.leftSubstitution stage letter).map relabel).flatMap
        (family.infrastructure.decompositions.decomposition level).blocks =
      ((family.infrastructure.left.factorization level).factor
        (relabel letter)).flatMap
          (family.infrastructure.decompositions.decomposition level).blocks
    rw [List.flatMap_map]
    have hcomparison : ∀ current,
        (family.infrastructure.decompositions.decomposition level).blocks
            (relabel current) = physical.decomposition.blocks current := by
      intro current
      have hblocks := comparison.blocks_eq current
      change canonical.blocks (relabel current) =
        physical.decomposition.blocks current at hblocks
      simpa [canonical] using hblocks
    simp_rw [hcomparison]
    rw [physical.left_decodes letter,
      ← hcomparison letter,
      (family.infrastructure.left.factorization level).factor_decodes]
  have hright : ∀ letter,
      (tower.rightSubstitution stage letter).map relabel =
        family.infrastructure.right.substitution level (relabel letter) := by
    intro letter
    apply Symbolic.flatMap_returnWords_injective
      (family.infrastructure.decompositions.decomposition level).blocks_injective
      (family.infrastructure.decompositions.decomposition level).blocks_are_returns
    change ((tower.rightSubstitution stage letter).map relabel).flatMap
        (family.infrastructure.decompositions.decomposition level).blocks =
      ((family.infrastructure.right.factorization level).factor
        (relabel letter)).flatMap
          (family.infrastructure.decompositions.decomposition level).blocks
    rw [List.flatMap_map]
    have hcomparison : ∀ current,
        (family.infrastructure.decompositions.decomposition level).blocks
            (relabel current) = physical.decomposition.blocks current := by
      intro current
      have hblocks := comparison.blocks_eq current
      change canonical.blocks (relabel current) =
        physical.decomposition.blocks current at hblocks
      simpa [canonical] using hblocks
    simp_rw [hcomparison]
    rw [physical.right_decodes letter,
      ← hcomparison letter,
      (family.infrastructure.right.factorization level).factor_decodes]
  exact ⟨{
    level := level
    level_length := by simpa [hphysical] using hlevelLength
    relabel := relabel
    word_relabels := hword
    left_relabels := hleft
    right_relabels := hright }⟩

/-- Deterministic canonical realization of every first-letter stage. -/
private def firstLetterCanonicalStages_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) : FirstLetterCanonicalStageC2Local tower stage :=
  Classical.choice (firstLetterPhysical_has_canonicalStage_c2
    tower stage (firstLetterPhysicalStages_c2 tower stage) rfl)

private theorem firstLetterPhysical_marker_length_strict_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) :
    (firstLetterPhysicalStages_c2 tower stage).marker.length <
      (firstLetterPhysicalStages_c2 tower (stage + 1)).marker.length := by
  let current := firstLetterPhysicalStages_c2 tower stage
  change current.marker.length <
    (firstLetterPhysicalSucc_c2 tower stage current).marker.length
  simp only [firstLetterPhysicalSucc_c2]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change current.marker.length <
    ((current.decomposition.blocks (tower.word stage).head) ++
      current.marker).length
  have hblock : 0 <
      (current.decomposition.blocks (tower.word stage).head).length :=
    current.decomposition.block_length_pos _
  simp only [List.length_append]
  omega

private theorem firstLetterPhysical_base_marker_length_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements) :
    (firstLetterPhysicalStages_c2 tower 0).marker.length =
      aligned.commonLevel + 1 := by
  change (family.infrastructure.markers.marker aligned.commonLevel).length = _
  rw [family.infrastructure.markers.marker_eq_take]

  simp

private theorem firstLetterPhysical_marker_length_lower_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements) : ∀ stage,
    (firstLetterPhysicalStages_c2 tower 0).marker.length + stage ≤
      (firstLetterPhysicalStages_c2 tower stage).marker.length
  | 0 => by simp
  | stage + 1 => by
      have hprevious :=
        firstLetterPhysical_marker_length_lower_c2 tower stage
      have hstrict :=
        firstLetterPhysical_marker_length_strict_c2 tower stage
      omega

private theorem firstLetterCanonicalStage_common_lt_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) (hstage : 0 < stage) :
    aligned.commonLevel <
      (firstLetterCanonicalStages_c2 tower stage).level := by
  have hbase := firstLetterPhysical_base_marker_length_c2 tower
  have hlower := firstLetterPhysical_marker_length_lower_c2 tower stage
  have hlevel :=
    (firstLetterCanonicalStages_c2 tower stage).level_length
  omega

/-- Relabeling fixed words composes. -/
private theorem wordRelabeling_trans_c2
    {alpha beta gamma : Type*}
    {left : Nat → alpha} {middle : Nat → beta} {right : Nat → gamma}
    (first : alpha ≃ beta) (second : beta ≃ gamma)
    (hfirst : ∀ position, first (left position) = middle position)
    (hsecond : ∀ position, second (middle position) = right position) :
    ∀ position, (first.trans second) (left position) = right position := by
  intro position
  rw [Equiv.trans_apply, hfirst, hsecond]

/-- A word relabeling can be read in the reverse direction. -/
private theorem wordRelabeling_symm_c2
    {alpha beta : Type*} {left : Nat → alpha} {right : Nat → beta}
    (relabel : alpha ≃ beta)
    (h : ∀ position, relabel (left position) = right position) :
    ∀ position, relabel.symm (right position) = left position := by
  intro position
  rw [← h position]
  simp

/-- Relabeling substitutions composes, with `List.map_map` supplying the
finite-word coherence. -/
private theorem substitutionRelabeling_trans_c2
    {alpha beta gamma : Type*}
    {left : Symbolic.Substitution alpha}
    {middle : Symbolic.Substitution beta}
    {right : Symbolic.Substitution gamma}
    (first : alpha ≃ beta) (second : beta ≃ gamma)
    (hfirst : ∀ letter, (left letter).map first = middle (first letter))
    (hsecond : ∀ letter, (middle letter).map second = right (second letter)) :
    ∀ letter, (left letter).map (first.trans second) =
      right ((first.trans second) letter) := by
  intro letter
  rw [show (left letter).map (first.trans second) =
      ((left letter).map first).map second by
        simp [List.map_map]]
  rw [hfirst, hsecond]
  rfl

/-- A substitution relabeling can be inverted. -/
private theorem substitutionRelabeling_symm_c2
    {alpha beta : Type*}
    {left : Symbolic.Substitution alpha}
    {right : Symbolic.Substitution beta}
    (relabel : alpha ≃ beta)
    (h : ∀ letter, (left letter).map relabel = right (relabel letter)) :
    ∀ letter, (right letter).map relabel.symm = left (relabel.symm letter) := by
  intro letter
  have hmapped := congrArg (List.map relabel.symm)
    (h (relabel.symm letter))
  simpa [List.map_map] using hmapped.symm

/-- C2.2: two stages at which the derived word and both induced return
substitutions repeat under one literal alphabet relabeling. -/
structure SimultaneousFirstLetterDerivedRepetition
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements) where
  earlier : Nat
  later : Nat
  earlier_lt_later : earlier < later
  relabel : Fin (tower.rank earlier) ≃ Fin (tower.rank later)
  word_relabels : ∀ position,
    relabel (tower.word earlier position) = tower.word later position
  left_relabels : ∀ letter,
    (tower.leftSubstitution earlier letter).map relabel =
      tower.leftSubstitution later (relabel letter)
  right_relabels : ∀ letter,
    (tower.rightSubstitution earlier letter).map relabel =
      tower.rightSubstitution later (relabel letter)

/-- Leaf C2.2: bounded simultaneous left/right return systems and infinite
pigeonhole give one common repeated pair. -/
theorem iteratedFirstLetterSystems_have_simultaneousRepetition
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements) :
    Nonempty (SimultaneousFirstLetterDerivedRepetition tower) := by
  classical
  let canonical := firstLetterCanonicalStages_c2 tower
  let encode : Nat →
      Fin family.leftClassCount × Fin family.rightClassCount := fun stage =>
    (family.leftCode (canonical stage).level,
      family.rightCode (canonical stage).level)
  obtain ⟨first, second, hne, hcode⟩ :=
    Finite.exists_ne_map_eq_of_infinite encode
  have construct : ∀ earlier later : Nat, earlier < later →
      encode earlier = encode later →
      Nonempty (SimultaneousFirstLetterDerivedRepetition tower) := by
    intro earlier later hearlierLater hsameCode
    let earlierSystem := canonical earlier
    let laterSystem := canonical later
    have hleftCode : family.leftCode earlierSystem.level =
        family.leftCode laterSystem.level := by
      have hfirst := congrArg Prod.fst hsameCode
      simpa [encode, earlierSystem, laterSystem] using hfirst
    have hrightCode : family.rightCode earlierSystem.level =
        family.rightCode laterSystem.level := by
      have hsecond := congrArg Prod.snd hsameCode
      simpa [encode, earlierSystem, laterSystem] using hsecond
    obtain ⟨leftRelabel, _leftSeed, leftWord, leftSubstitution⟩ :=
      family.left_same_code earlierSystem.level laterSystem.level hleftCode
    obtain ⟨rightRelabel, _rightSeed, rightWord, rightSubstitution⟩ :=
      family.right_same_code earlierSystem.level laterSystem.level hrightCode
    have hrelabels : leftRelabel = rightRelabel := by
      apply Equiv.ext
      intro letter
      obtain ⟨position, hposition⟩ :=
        (family.infrastructure.decompositions.decomposition
          earlierSystem.level).every_letter_occurs letter
      rw [← hposition]
      exact (leftWord position).trans (rightWord position).symm
    have rightSubstitution' : ∀ letter,
        (family.infrastructure.right.substitution earlierSystem.level
          letter).map leftRelabel =
        family.infrastructure.right.substitution laterSystem.level
          (leftRelabel letter) := by
      intro letter
      simpa [hrelabels] using rightSubstitution letter
    let relabel : Fin (tower.rank earlier) ≃ Fin (tower.rank later) :=
      (earlierSystem.relabel.trans leftRelabel).trans
        laterSystem.relabel.symm
    have hwordCanonical : ∀ position,
        leftRelabel
            ((family.infrastructure.decompositions.decomposition
              earlierSystem.level).derived position) =
          (family.infrastructure.decompositions.decomposition
            laterSystem.level).derived position := leftWord
    have hwordToLater : ∀ position,
        laterSystem.relabel.symm
            ((family.infrastructure.decompositions.decomposition
              laterSystem.level).derived position) =
          tower.word later position :=
      wordRelabeling_symm_c2 laterSystem.relabel
        laterSystem.word_relabels
    have hwordFirst : ∀ position,
        (earlierSystem.relabel.trans leftRelabel)
            (tower.word earlier position) =
          (family.infrastructure.decompositions.decomposition
            laterSystem.level).derived position :=
      wordRelabeling_trans_c2 earlierSystem.relabel leftRelabel
        earlierSystem.word_relabels hwordCanonical
    have hword : ∀ position,
        relabel (tower.word earlier position) = tower.word later position := by
      exact wordRelabeling_trans_c2
        (earlierSystem.relabel.trans leftRelabel)
        laterSystem.relabel.symm hwordFirst hwordToLater
    have hleftToLater : ∀ letter,
        (family.infrastructure.left.substitution laterSystem.level
          letter).map laterSystem.relabel.symm =
        tower.leftSubstitution later (laterSystem.relabel.symm letter) :=
      substitutionRelabeling_symm_c2 laterSystem.relabel
        laterSystem.left_relabels
    have hleftFirst : ∀ letter,
        (tower.leftSubstitution earlier letter).map
            (earlierSystem.relabel.trans leftRelabel) =
          family.infrastructure.left.substitution laterSystem.level
            ((earlierSystem.relabel.trans leftRelabel) letter) :=
      substitutionRelabeling_trans_c2 earlierSystem.relabel
        leftRelabel earlierSystem.left_relabels leftSubstitution
    have hleft : ∀ letter,
        (tower.leftSubstitution earlier letter).map relabel =
          tower.leftSubstitution later (relabel letter) := by
      exact substitutionRelabeling_trans_c2
        (earlierSystem.relabel.trans leftRelabel)
        laterSystem.relabel.symm hleftFirst hleftToLater
    have hrightToLater : ∀ letter,
        (family.infrastructure.right.substitution laterSystem.level
          letter).map laterSystem.relabel.symm =
        tower.rightSubstitution later (laterSystem.relabel.symm letter) :=
      substitutionRelabeling_symm_c2 laterSystem.relabel
        laterSystem.right_relabels
    have hrightFirst : ∀ letter,
        (tower.rightSubstitution earlier letter).map
            (earlierSystem.relabel.trans leftRelabel) =
          family.infrastructure.right.substitution laterSystem.level
            ((earlierSystem.relabel.trans leftRelabel) letter) :=
      substitutionRelabeling_trans_c2 earlierSystem.relabel
        leftRelabel earlierSystem.right_relabels rightSubstitution'
    have hright : ∀ letter,
        (tower.rightSubstitution earlier letter).map relabel =
          tower.rightSubstitution later (relabel letter) := by
      exact substitutionRelabeling_trans_c2
        (earlierSystem.relabel.trans leftRelabel)
        laterSystem.relabel.symm hrightFirst hrightToLater
    exact ⟨{
      earlier := earlier
      later := later
      earlier_lt_later := hearlierLater
      relabel := relabel
      word_relabels := hword
      left_relabels := hleft
      right_relabels := hright }⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact construct first second hlt hcode
  · exact construct second first hgt hcode.symm

/-! ### Shifted repetition and the deep self-return decoder -/

/-- The order-free part of a simultaneous stage repetition. -/
private structure FirstLetterStageEquivalenceC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (leftStage rightStage : Nat) where
  relabel : Fin (tower.rank leftStage) ≃ Fin (tower.rank rightStage)
  word_relabels : ∀ position,
    relabel (tower.word leftStage position) =
      tower.word rightStage position
  left_relabels : ∀ letter,
    (tower.leftSubstitution leftStage letter).map relabel =
      tower.leftSubstitution rightStage (relabel letter)
  right_relabels : ∀ letter,
    (tower.rightSubstitution leftStage letter).map relabel =
      tower.rightSubstitution rightStage (relabel letter)

/-- A letterwise substitution relabeling extends to arbitrary source words. -/
private theorem mapWord_relabels_c2
    {alpha beta : Type*}
    {left : Symbolic.Substitution alpha}
    {right : Symbolic.Substitution beta}
    (relabel : alpha ≃ beta)
    (hletter : ∀ letter, (left letter).map relabel =
      right (relabel letter)) :
    ∀ letters : Symbolic.Word alpha,
      (left.mapWord letters).map relabel =
        right.mapWord (letters.map relabel) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.map_cons]
      rw [Symbolic.Substitution.mapWord_cons,
        Symbolic.Substitution.mapWord_cons, List.map_append,
        hletter, ih]

/-- Relabeled block tables transport a whole decoded word. -/
private theorem flatMap_relabels_blocks_c2
    {alpha beta gamma delta : Type*}
    (sourceRelabel : alpha → beta) (returnRelabel : gamma → delta)
    (leftBlocks : gamma → Symbolic.Word alpha)
    (rightBlocks : delta → Symbolic.Word beta)
    (hblocks : ∀ letter,
      rightBlocks (returnRelabel letter) =
        (leftBlocks letter).map sourceRelabel) :
    ∀ letters : Symbolic.Word gamma,
      (letters.map returnRelabel).flatMap rightBlocks =
        (letters.flatMap leftBlocks).map sourceRelabel := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [hblocks, ih]

/-- Simultaneous equivalence propagates through one exact first-letter
derivation.  Completeness of return decompositions supplies the successor
alphabet bijection; uniqueness of the two induced factorizations supplies
both successor substitution equations. -/
private theorem firstLetterStageEquivalence_succ_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    {leftStage rightStage : Nat}
    (equivalence : FirstLetterStageEquivalenceC2Local tower
      leftStage rightStage) :
    Nonempty (FirstLetterStageEquivalenceC2Local tower
      (leftStage + 1) (rightStage + 1)) := by
  classical
  let coding : Symbolic.LetterCoding (Fin (tower.rank leftStage))
      (Fin (tower.rank rightStage)) := ⟨equivalence.relabel⟩
  have hword : coding.mapInfinite (tower.word leftStage) =
      tower.word rightStage := by
    funext position
    exact equivalence.word_relabels position
  have hmarker : coding.mapWord [(tower.word leftStage).head] =
      [(tower.word rightStage).head] := by
    simp only [coding, Symbolic.LetterCoding.mapWord, List.map_singleton,
      List.cons.injEq, and_true]
    change equivalence.relabel (tower.word leftStage 0) =
      tower.word rightStage 0
    exact equivalence.word_relabels 0
  let mapped := (tower.stepDecomposition leftStage).map_injective
    coding equivalence.relabel.injective
  let sameWord := Symbolic.Substitution.castReturnDecompositionWord
    hword mapped
  let transported : Symbolic.ReturnDecomposition
      (tower.word rightStage) [(tower.word rightStage).head]
      (tower.rank (leftStage + 1)) :=
    castReturnDecompositionMarker_c2 hmarker sameWord
  let comparison := Classical.choice
    (returnDecompositions_sameMarker_relabel_c2 transported
      (tower.stepDecomposition rightStage))
  let nextRelabel := comparison.relabel
  have hblocks : ∀ letter,
      (tower.stepDecomposition rightStage).blocks (nextRelabel letter) =
        ((tower.stepDecomposition leftStage).blocks letter).map
          equivalence.relabel := by
    intro letter
    have hraw := comparison.blocks_eq letter
    change (tower.stepDecomposition rightStage).blocks
        (nextRelabel letter) = transported.blocks letter at hraw
    calc
      (tower.stepDecomposition rightStage).blocks
          (nextRelabel letter) = transported.blocks letter := hraw
      _ = sameWord.blocks letter := by
        exact congrFun
          (castReturnDecompositionMarker_blocks_c2
            hmarker sameWord) letter
      _ = mapped.blocks letter :=
        castReturnDecompositionWord_blocks_c2 hword mapped letter
      _ = ((tower.stepDecomposition leftStage).blocks letter).map
          equivalence.relabel := rfl
  have hnextWord : ∀ position,
      nextRelabel (tower.word (leftStage + 1) position) =
        tower.word (rightStage + 1) position := by
    intro position
    rw [← tower.step_word_eq leftStage,
      ← tower.step_word_eq rightStage]
    have hraw := comparison.word_eq position
    change nextRelabel (transported.derived position) =
      (tower.stepDecomposition rightStage).derived position at hraw
    simpa [transported, sameWord, mapped] using hraw
  have hleft : ∀ letter,
      (tower.leftSubstitution (leftStage + 1) letter).map nextRelabel =
        tower.leftSubstitution (rightStage + 1)
          (nextRelabel letter) := by
    intro letter
    rw [tower.left_succ_eq leftStage, tower.left_succ_eq rightStage]
    change ((tower.leftStepFactorization leftStage).factor letter).map
        nextRelabel =
      (tower.leftStepFactorization rightStage).factor
        (nextRelabel letter)
    apply (tower.leftStepFactorization rightStage).factor_unique
    calc
      (((tower.leftStepFactorization leftStage).factor letter).map
          nextRelabel).flatMap
            (tower.stepDecomposition rightStage).blocks =
          (((tower.leftStepFactorization leftStage).factor letter).flatMap
            (tower.stepDecomposition leftStage).blocks).map
              equivalence.relabel :=
        flatMap_relabels_blocks_c2 equivalence.relabel
          nextRelabel (tower.stepDecomposition leftStage).blocks
          (tower.stepDecomposition rightStage).blocks hblocks _
      _ = ((tower.leftSubstitution leftStage).mapWord
            ((tower.stepDecomposition leftStage).blocks letter)).map
              equivalence.relabel := by
        rw [(tower.leftStepFactorization leftStage).factor_decodes]
      _ = (tower.leftSubstitution rightStage).mapWord
            (((tower.stepDecomposition leftStage).blocks letter).map
              equivalence.relabel) :=
        mapWord_relabels_c2 equivalence.relabel
          equivalence.left_relabels _
      _ = (tower.leftSubstitution rightStage).mapWord
            ((tower.stepDecomposition rightStage).blocks
              (nextRelabel letter)) := by rw [hblocks]
  have hright : ∀ letter,
      (tower.rightSubstitution (leftStage + 1) letter).map nextRelabel =
        tower.rightSubstitution (rightStage + 1)
          (nextRelabel letter) := by
    intro letter
    rw [tower.right_succ_eq leftStage, tower.right_succ_eq rightStage]
    change ((tower.rightStepFactorization leftStage).factor letter).map
        nextRelabel =
      (tower.rightStepFactorization rightStage).factor
        (nextRelabel letter)
    apply (tower.rightStepFactorization rightStage).factor_unique
    calc
      (((tower.rightStepFactorization leftStage).factor letter).map
          nextRelabel).flatMap
            (tower.stepDecomposition rightStage).blocks =
          (((tower.rightStepFactorization leftStage).factor letter).flatMap
            (tower.stepDecomposition leftStage).blocks).map
              equivalence.relabel :=
        flatMap_relabels_blocks_c2 equivalence.relabel
          nextRelabel (tower.stepDecomposition leftStage).blocks
          (tower.stepDecomposition rightStage).blocks hblocks _
      _ = ((tower.rightSubstitution leftStage).mapWord
            ((tower.stepDecomposition leftStage).blocks letter)).map
              equivalence.relabel := by
        rw [(tower.rightStepFactorization leftStage).factor_decodes]
      _ = (tower.rightSubstitution rightStage).mapWord
            (((tower.stepDecomposition leftStage).blocks letter).map
              equivalence.relabel) :=
        mapWord_relabels_c2 equivalence.relabel
          equivalence.right_relabels _
      _ = (tower.rightSubstitution rightStage).mapWord
            ((tower.stepDecomposition rightStage).blocks
              (nextRelabel letter)) := by rw [hblocks]
  exact ⟨{
    relabel := nextRelabel
    word_relabels := hnextWord
    left_relabels := hleft
    right_relabels := hright }⟩

/-- The literal composite return decomposition along a nonempty interval of
the first-letter tower. -/
private structure FirstLetterIntervalDecompositionC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (startStage endStage : Nat) where
  marker : Symbolic.Word (Fin (tower.rank startStage))
  decomposition : Symbolic.ReturnDecomposition (tower.word startStage)
    marker (tower.rank endStage)
  derived_eq : decomposition.derived = tower.word endStage
  left_decodes : ∀ letter,
    (tower.leftSubstitution endStage letter).flatMap decomposition.blocks =
      (tower.leftSubstitution startStage).mapWord
        (decomposition.blocks letter)
  right_decodes : ∀ letter,
    (tower.rightSubstitution endStage letter).flatMap decomposition.blocks =
      (tower.rightSubstitution startStage).mapWord
        (decomposition.blocks letter)

private def firstLetterInterval_one_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (startStage : Nat) :
    FirstLetterIntervalDecompositionC2Local tower startStage
      (startStage + 1) where
  marker := [(tower.word startStage).head]
  decomposition := tower.stepDecomposition startStage
  derived_eq := tower.step_word_eq startStage
  left_decodes := by
    intro letter
    rw [tower.left_succ_eq startStage]
    exact (tower.leftStepFactorization startStage).factor_decodes letter
  right_decodes := by
    intro letter
    rw [tower.right_succ_eq startStage]
    exact (tower.rightStepFactorization startStage).factor_decodes letter

private def firstLetterInterval_succ_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    {startStage endStage : Nat}
    (current : FirstLetterIntervalDecompositionC2Local tower
      startStage endStage) :
    FirstLetterIntervalDecompositionC2Local tower startStage
      (endStage + 1) := by
  let inner := Symbolic.Substitution.castReturnDecompositionWord
    current.derived_eq.symm (tower.stepDecomposition endStage)
  let leftFactorization := castPrefixReturnFactorizationWord_c2
    current.derived_eq.symm (tower.stepDecomposition endStage)
      (tower.leftStepFactorization endStage)
  let rightFactorization := castPrefixReturnFactorizationWord_c2
    current.derived_eq.symm (tower.stepDecomposition endStage)
      (tower.rightStepFactorization endStage)
  let composed := composeReturnDecompositions_c2
    current.decomposition inner
  refine {
    marker := [(tower.word endStage).head].flatMap
      current.decomposition.blocks ++ current.marker
    decomposition := composed
    derived_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }
  · change inner.derived = tower.word (endStage + 1)
    rw [Symbolic.Substitution.castReturnDecompositionWord_derived]
    exact tower.step_word_eq endStage
  · intro letter
    rw [tower.left_succ_eq endStage]
    have hfactorization : leftFactorization.substitution =
        (tower.leftStepFactorization endStage).substitution := by
      simp [leftFactorization]
    rw [← hfactorization]
    change (leftFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_c2 current.decomposition
      current.left_decodes inner leftFactorization letter

  · intro letter
    rw [tower.right_succ_eq endStage]
    have hfactorization : rightFactorization.substitution =
        (tower.rightStepFactorization endStage).substitution := by
      simp [rightFactorization]
    rw [← hfactorization]
    change (rightFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_c2 current.decomposition
      current.right_decodes inner rightFactorization letter

private def firstLetterInterval_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (startStage : Nat) : ∀ extraSteps : Nat,
    FirstLetterIntervalDecompositionC2Local tower startStage
      (startStage + (extraSteps + 1))
  | 0 => firstLetterInterval_one_c2 tower startStage
  | extraSteps + 1 => by
      simpa [Nat.add_assoc] using
        firstLetterInterval_succ_c2 tower
          (firstLetterInterval_c2 tower startStage extraSteps)

private def castFirstLetterIntervalEnd_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {startStage leftEnd rightEnd : Nat} (hend : leftEnd = rightEnd)
    (interval : FirstLetterIntervalDecompositionC2Local tower
      startStage leftEnd) :
    FirstLetterIntervalDecompositionC2Local tower startStage rightEnd := by
  subst rightEnd
  exact interval

/-- A self-return decomposition at the successor of the repeated later
stage. -/
private structure FirstLetterSelfReturnC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) where
  marker : Symbolic.Word (Fin (tower.rank stage))
  decomposition : Symbolic.ReturnDecomposition (tower.word stage)
    marker (tower.rank stage)
  derived_eq : decomposition.derived = tower.word stage
  left_decodes : ∀ letter,
    (tower.leftSubstitution stage letter).flatMap decomposition.blocks =
      (tower.leftSubstitution stage).mapWord (decomposition.blocks letter)
  right_decodes : ∀ letter,
    (tower.rightSubstitution stage letter).flatMap decomposition.blocks =
      (tower.rightSubstitution stage).mapWord (decomposition.blocks letter)

private theorem simultaneousRepetition_has_successorSelfReturn_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    (repetition : SimultaneousFirstLetterDerivedRepetition tower) :
    Nonempty (FirstLetterSelfReturnC2Local tower
      (repetition.later + 1)) := by
  classical
  let initial : FirstLetterStageEquivalenceC2Local tower
      repetition.earlier repetition.later := {
    relabel := repetition.relabel
    word_relabels := repetition.word_relabels
    left_relabels := repetition.left_relabels
    right_relabels := repetition.right_relabels }
  let shifted := Classical.choice
    (firstLetterStageEquivalence_succ_c2 tower initial)
  let gap := repetition.later - repetition.earlier
  have hgap : 0 < gap := Nat.sub_pos_of_lt repetition.earlier_lt_later
  let extraSteps := gap - 1
  have hcount : extraSteps + 1 = gap := by
    dsimp [extraSteps]
    omega
  have hend : (repetition.earlier + 1) + (extraSteps + 1) =
      repetition.later + 1 := by
    dsimp [gap] at hcount
    omega
  let rawInterval := firstLetterInterval_c2 tower
    (repetition.earlier + 1) extraSteps
  let interval := castFirstLetterIntervalEnd_c2 hend rawInterval
  let coding : Symbolic.LetterCoding
      (Fin (tower.rank (repetition.earlier + 1)))
      (Fin (tower.rank (repetition.later + 1))) := ⟨shifted.relabel⟩
  have hword : coding.mapInfinite
      (tower.word (repetition.earlier + 1)) =
        tower.word (repetition.later + 1) := by
    funext position
    exact shifted.word_relabels position
  let mapped := interval.decomposition.map_injective coding
    shifted.relabel.injective
  let self := Symbolic.Substitution.castReturnDecompositionWord hword mapped
  have hselfBlocks : ∀ letter, self.blocks letter =
      (interval.decomposition.blocks letter).map shifted.relabel := by
    intro letter
    calc
      self.blocks letter = mapped.blocks letter :=
        castReturnDecompositionWord_blocks_c2 hword mapped letter
      _ = (interval.decomposition.blocks letter).map shifted.relabel := rfl
  refine ⟨{
    marker := coding.mapWord interval.marker
    decomposition := self
    derived_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }⟩
  · change self.derived = tower.word (repetition.later + 1)
    rw [Symbolic.Substitution.castReturnDecompositionWord_derived]
    change interval.decomposition.derived = _
    exact interval.derived_eq
  · intro letter
    calc
      (tower.leftSubstitution (repetition.later + 1) letter).flatMap
          self.blocks =
        ((tower.leftSubstitution (repetition.later + 1) letter).flatMap
          interval.decomposition.blocks).map shifted.relabel := by
            simpa [hselfBlocks] using
              flatMap_relabels_blocks_c2 shifted.relabel id
                interval.decomposition.blocks self.blocks
                (fun current => by simpa using hselfBlocks current)
                (tower.leftSubstitution (repetition.later + 1) letter)
      _ = ((tower.leftSubstitution (repetition.earlier + 1)).mapWord
          (interval.decomposition.blocks letter)).map shifted.relabel := by
            rw [interval.left_decodes]
      _ = (tower.leftSubstitution (repetition.later + 1)).mapWord
          ((interval.decomposition.blocks letter).map shifted.relabel) :=
            mapWord_relabels_c2 shifted.relabel
              shifted.left_relabels _
      _ = (tower.leftSubstitution (repetition.later + 1)).mapWord
          (self.blocks letter) := by rw [hselfBlocks]
  · intro letter
    calc
      (tower.rightSubstitution (repetition.later + 1) letter).flatMap
          self.blocks =
        ((tower.rightSubstitution (repetition.later + 1) letter).flatMap
          interval.decomposition.blocks).map shifted.relabel := by
            simpa [hselfBlocks] using
              flatMap_relabels_blocks_c2 shifted.relabel id
                interval.decomposition.blocks self.blocks
                (fun current => by simpa using hselfBlocks current)
                (tower.rightSubstitution (repetition.later + 1) letter)
      _ = ((tower.rightSubstitution (repetition.earlier + 1)).mapWord
          (interval.decomposition.blocks letter)).map shifted.relabel := by
            rw [interval.right_decodes]
      _ = (tower.rightSubstitution (repetition.later + 1)).mapWord
          ((interval.decomposition.blocks letter).map shifted.relabel) :=
            mapWord_relabels_c2 shifted.relabel
              shifted.right_relabels _
      _ = (tower.rightSubstitution (repetition.later + 1)).mapWord
          (self.blocks letter) := by rw [hselfBlocks]

/-- Infinite concatenation of a complete return decomposition recovers its
ambient word.  This local public-facing copy avoids the private production
helper while C2.3 remains isolated. -/
private theorem returnDecoder_mapInfinite_derived_c2
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank) :
    (returnDecoderSubstitution decomposition).mapInfinite
        decomposition.derived = word := by
  let decoder := returnDecoderSubstitution decomposition
  let R : Symbolic.InfiniteWord (Fin rank) →
      Symbolic.InfiniteWord (Fin rank) → Prop := fun left right =>
    ∃ (pref : Symbolic.Word (Fin rank)) (stage : Nat),
      left = pref ++ₛ decoder.mapInfinite (decomposition.derived.drop stage) ∧
      right = pref ++ₛ word.drop (decomposition.cut stage)
  apply Stream'.eq_of_bisim R
  · intro left right hrelated
    rcases hrelated with ⟨pref, stage, rfl, rfl⟩
    cases pref with
    | cons head tail =>
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨tail, stage, rfl, rfl⟩⟩
    | nil =>
        simp only [Stream'.nil_append_stream]
        let block := decomposition.blocks (decomposition.derived stage)
        have hleft :
            decoder.mapInfinite (decomposition.derived.drop stage) =
              block ++ₛ decoder.mapInfinite
                (decomposition.derived.drop (stage + 1)) := by
          rw [decoder.mapInfinite_eq_append_first_image]
          simp [decoder, returnDecoderSubstitution, block, Stream'.get]
        have hright : word.drop (decomposition.cut stage) =
            block ++ₛ word.drop (decomposition.cut (stage + 1)) := by
          calc
            word.drop (decomposition.cut stage) =
                (word.drop (decomposition.cut stage)).take block.length ++ₛ
                  (word.drop (decomposition.cut stage)).drop block.length :=
              (Stream'.append_take_drop _ _).symm
            _ = block ++ₛ word.drop (decomposition.cut (stage + 1)) := by
              rw [show (word.drop (decomposition.cut stage)).take block.length =
                  block by exact decomposition.block_at_cut stage]
              simp [block, decomposition.cut_succ, Stream'.drop_drop]
        rw [hleft, hright]
        obtain ⟨head, tail, hblock⟩ := List.exists_cons_of_ne_nil
          (decomposition.blocks_are_returns
            (decomposition.derived stage)).2.1
        change block = head :: tail at hblock
        rw [hblock]
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨tail, stage + 1, rfl, rfl⟩⟩
  · exact ⟨[], 0, by simp [decoder], by simp [decomposition.cut_zero]⟩

/-- A nonerasing substitution preserves pure periodicity under infinite
concatenation. -/
private theorem mapInfinite_periodic_c2
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet)
    {word : Symbolic.InfiniteWord alphabet}
    (hperiodic : Symbolic.IsPeriodic word) :
    Symbolic.IsPeriodic (substitution.mapInfinite word) := by
  rcases hperiodic with ⟨period, hperiodPos, hperiod⟩
  let periodWord := word.take period
  let decodedPeriod := substitution.mapWord periodWord
  have hperiodWordNonempty : periodWord ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [periodWord, hperiodPos]
  have hdecodedPeriodNonempty : decodedPeriod ≠ [] :=
    substitution.mapWord_ne_nil hperiodWordNonempty
  have hdrop : word.drop period = word := by
    funext position
    calc
      (word.drop period) position = word (period + position) :=
        Stream'.get_drop position period word
      _ = word position := by
        simpa [Nat.add_comm] using hperiod position
  have hself : substitution.mapInfinite word =
      decodedPeriod ++ₛ substitution.mapInfinite word := by
    calc
      substitution.mapInfinite word =
          substitution.mapInfinite (word.take period ++ₛ word.drop period) := by
            rw [Stream'.append_take_drop]
      _ = substitution.mapWord (word.take period) ++ₛ
            substitution.mapInfinite (word.drop period) :=
          substitution.mapInfinite_append_stream _ _
      _ = decodedPeriod ++ₛ substitution.mapInfinite word := by rw [hdrop]
  refine ⟨decodedPeriod.length,
    List.length_pos_of_ne_nil hdecodedPeriodNonempty, ?_⟩
  intro position
  have hpoint := congrFun hself (decodedPeriod.length + position)
  calc
    substitution.mapInfinite word (position + decodedPeriod.length) =
        substitution.mapInfinite word (decodedPeriod.length + position) := by
      rw [Nat.add_comm]
    _ = (decodedPeriod ++ₛ substitution.mapInfinite word).get
          (decodedPeriod.length + position) := hpoint
    _ = substitution.mapInfinite word position :=
      Stream'.get_append_right position decodedPeriod
        (substitution.mapInfinite word)

private theorem returnDecomposition_word_aperiodic_of_ambient_c2
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (hword : ¬ Symbolic.IsPeriodic word) :
    ¬ Symbolic.IsPeriodic decomposition.derived := by
  intro hperiodic
  apply hword
  rw [← returnDecoder_mapInfinite_derived_c2 decomposition]
  exact mapInfinite_periodic_c2
    (returnDecoderSubstitution decomposition) hperiodic

/-- Every block of a return decomposition at a nonempty prefix begins with
the first letter of the ambient word. -/
private theorem returnBlocks_begin_head_c2
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank) :
    ∀ letter, [word.head] <+: decomposition.blocks letter := by
  intro letter
  obtain ⟨markerHead, markerTail, hmarker⟩ :=
    List.exists_cons_of_ne_nil decomposition.marker_ne_nil
  obtain ⟨blockHead, blockTail, hblock⟩ :=
    List.exists_cons_of_ne_nil
      (decomposition.blocks_are_returns letter).2.1
  have hmarkerHead : markerHead = word.head := by
    have hzero := decomposition.marker_at_zero
    rw [Symbolic.InfiniteFactorAt, Stream'.drop_zero, hmarker,
      List.length_cons, Stream'.take_succ] at hzero
    exact (List.cons.inj hzero).1.symm

  have hblockHead : blockHead = markerHead := by
    obtain ⟨tail, hprefix⟩ :=
      (decomposition.blocks_are_returns letter).2.2.2.1
    have hheads := congrArg List.head? hprefix
    simpa [hmarker, hblock] using hheads.symm
  rw [hblock, hblockHead, hmarkerHead]
  exact List.prefix_append _ _

/-- In a nonconstant fixed word, a nonerasing substitution all of whose
images begin at the fixed-word head has unbounded images from every letter. -/
private theorem allLetterGrowth_of_fixed_nonconstant_beginHead_c2
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    {substitution : Symbolic.Substitution alphabet}
    {word : Symbolic.InfiniteWord alphabet}
    (hfixed : substitution.IsFixedPoint word)
    (hnonconstant : ∃ position, word position ≠ word.head)
    (hbegin : ∀ letter, [word.head] <+: substitution letter) :
    ∀ letter, LetterImagesGrow substitution letter := by
  classical
  have hheadLength : 1 < (substitution word.head).length := by
    by_contra hnot
    have hpositive : 0 < (substitution word.head).length :=
      List.length_pos_of_ne_nil (substitution.image_ne_nil word.head)
    have hone : (substitution word.head).length = 1 := by omega
    have hheadImage : substitution word.head = [word.head] := by
      obtain ⟨tail, htail⟩ := hbegin word.head
      have htailLength := congrArg List.length htail
      simp only [List.length_singleton, List.length_append] at htailLength
      have : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [this] using htail.symm
    let firstDifferent := Nat.find hnonconstant
    have hfirstDifferent := Nat.find_spec hnonconstant
    have hbefore : ∀ position < firstDifferent,
        word position = word.head := by
      intro position hposition
      by_contra hne
      exact (Nat.find_min hnonconstant hposition) hne
    have hprefix : word.take firstDifferent =
        List.replicate firstDifferent word.head := by
      apply List.ext_getElem
      · simp
      · intro position hleft hright
        rw [Stream'.take_get (a := word) (m := position)
          (n := firstDifferent) (by simpa using hleft)]
        simp only [List.getElem_replicate]
        exact hbefore position (by simpa using hleft)
    have hmappedPrefix : substitution.mapWord
        (word.take firstDifferent) = word.take firstDifferent := by
      rw [hprefix]
      induction firstDifferent with
      | zero => simp
      | succ position ih =>
          simp [List.replicate_succ, hheadImage, ih]
    have hat := Symbolic.Substitution.iterateWord_drop_take_at_fixed
      hfixed 1 firstDifferent 1
    have htake : (word.drop firstDifferent).take 1 =
        [word firstDifferent] := by
      rw [Stream'.take_succ]
      simp [Stream'.get]
    rw [htake] at hat
    have hstart :
        (substitution.iterateWord 1 (word.take firstDifferent)).length =
          firstDifferent := by
      change (substitution.mapWord (word.take firstDifferent)).length = _
      rw [hmappedPrefix]
      simp
    have himageAt : Symbolic.InfiniteFactorAt word
        (substitution (word firstDifferent)) firstDifferent := by
      rw [hstart] at hat
      simpa [Symbolic.Substitution.iterateWord] using hat
    have hheadAt : word firstDifferent = word.head := by
      have hprefixImage := hbegin (word firstDifferent)
      have hfinite : Symbolic.FiniteFactorAt
          (substitution (word firstDifferent)) [word.head] 0 := by
        refine ⟨by simpa using hprefixImage.length_le, ?_⟩
        simpa using (List.prefix_iff_eq_take.mp hprefixImage).symm
      have := himageAt.of_finiteFactorAt hfinite
      simpa [Symbolic.InfiniteFactorAt, Stream'.take_succ] using this
    exact hfirstDifferent hheadAt
  have hprolong : substitution.ProlongableOn word.head :=
    Symbolic.Substitution.prolongableOn_head_of_fixedPoint hfixed hheadLength
  have hheadGrow : LetterImagesGrow substitution word.head := by
    intro bound
    exact ⟨bound,
      (Nat.le_succ bound).trans
        (substitution.succ_le_iterateLetter_length hprolong bound)⟩
  intro letter bound
  obtain ⟨depth, hdepth⟩ := hheadGrow bound
  refine ⟨depth + 1, hdepth.trans ?_⟩
  have hinfix := Symbolic.Substitution.iterateWord_infix_public
    substitution depth (hbegin letter).isInfix
  have hlength := hinfix.length_le
  have hcommute : substitution.iterateWord depth (substitution letter) =
      substitution.mapWord (substitution.iterateWord depth [letter]) := by
    calc
      substitution.iterateWord depth (substitution letter) =
          substitution.iterateWord depth
            (substitution.iterateWord 1 [letter]) := by
        simp [Symbolic.Substitution.iterateWord]
      _ = substitution.iterateWord (depth + 1) [letter] :=
        (Symbolic.Substitution.iterateWord_add_public
          substitution depth 1 [letter]).symm
      _ = substitution.iterateWord (1 + depth) [letter] := by
        rw [Nat.add_comm]
      _ = substitution.iterateWord 1
          (substitution.iterateWord depth [letter]) :=
        Symbolic.Substitution.iterateWord_add_public
          substitution 1 depth [letter]
      _ = substitution.mapWord
          (substitution.iterateWord depth [letter]) := by rfl
  rw [hcommute] at hlength
  simpa [Symbolic.Substitution.iterateLetter] using hlength

private theorem firstLetterTower_word_uniform_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) : Symbolic.IsUniformlyRecurrent (tower.word stage) := by
  let physical := firstLetterPhysicalStages_c2 tower stage
  have huniform := physical.decomposition.uniformlyRecurrent_derived
    input.linearlyRecurrent.2.1
  rw [physical.derived_eq] at huniform
  exact huniform

/-- The self-return decoder obtained from the shifted loop is primitive. -/
private theorem firstLetterSelfReturn_decoder_primitive_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {stage : Nat} (self : FirstLetterSelfReturnC2Local tower stage)
    (hrank : 1 < tower.rank stage) :
    IsPrimitiveSubstitution (returnDecoderSubstitution self.decomposition) := by
  classical
  letI : Nonempty (Fin (tower.rank stage)) :=
    ⟨⟨0, tower.rank_pos stage⟩⟩
  let decoder := returnDecoderSubstitution self.decomposition
  have hfixed : decoder.IsFixedPoint (tower.word stage) := by
    have hdecode := returnDecoder_mapInfinite_derived_c2
      self.decomposition
    rw [self.derived_eq] at hdecode
    exact hdecode
  have hbegin : ∀ letter,
      [(tower.word stage).head] <+: decoder letter := by
    intro letter
    exact returnBlocks_begin_head_c2 self.decomposition letter
  obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card
    (by simpa using hrank) (tower.word stage).head
  obtain ⟨position, hposition⟩ :=
    self.decomposition.every_letter_occurs other
  have hwordPosition : tower.word stage position = other := by
    rw [← self.derived_eq]
    exact hposition
  have hnonconstant : ∃ position,
      tower.word stage position ≠ (tower.word stage).head :=
    ⟨position, by rw [hwordPosition]; exact hother⟩
  have hgrow : ∀ letter, LetterImagesGrow decoder letter :=
    allLetterGrowth_of_fixed_nonconstant_beginHead_c2 hfixed
      hnonconstant hbegin
  exact Symbolic.Substitution.primitive_of_fixed_uniform_all_images_grow
    hfixed (firstLetterTower_word_uniform_c2 tower stage)
    (by
      intro letter
      rw [← self.derived_eq]
      exact self.decomposition.every_letter_occurs letter)
    hgrow

/-- Iterating a self-return decomposition retains its derived word and the
two commuting substitution equations, while its blocks become exact powers
of the return decoder. -/
private structure IteratedFirstLetterSelfReturnC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {stage : Nat} (self : FirstLetterSelfReturnC2Local tower stage)
    (level : Nat) where
  marker : Symbolic.Word (Fin (tower.rank stage))
  decomposition : Symbolic.ReturnDecomposition (tower.word stage)
    marker (tower.rank stage)
  derived_eq : decomposition.derived = tower.word stage
  blocks_eq : ∀ letter,
    decomposition.blocks letter =
      ((returnDecoderSubstitution self.decomposition).power (level + 1))
        letter
  left_decodes : ∀ letter,
    (tower.leftSubstitution stage letter).flatMap decomposition.blocks =
      (tower.leftSubstitution stage).mapWord (decomposition.blocks letter)
  right_decodes : ∀ letter,
    (tower.rightSubstitution stage letter).flatMap decomposition.blocks =
      (tower.rightSubstitution stage).mapWord (decomposition.blocks letter)

private def iteratedFirstLetterSelfReturn_zero_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {stage : Nat} (self : FirstLetterSelfReturnC2Local tower stage) :
    IteratedFirstLetterSelfReturnC2Local self 0 where
  marker := self.marker
  decomposition := self.decomposition
  derived_eq := self.derived_eq
  blocks_eq := by
    intro letter
    simp [returnDecoderSubstitution, Symbolic.Substitution.power_apply,
      Symbolic.Substitution.iterateLetter,
      Symbolic.Substitution.iterateWord]
  left_decodes := self.left_decodes
  right_decodes := self.right_decodes

private def iteratedFirstLetterSelfReturn_succ_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {stage : Nat} (self : FirstLetterSelfReturnC2Local tower stage)
    (level : Nat)
    (current : IteratedFirstLetterSelfReturnC2Local self level) :
    IteratedFirstLetterSelfReturnC2Local self (level + 1) := by
  rcases current with
    ⟨currentMarker, currentDecomposition, currentDerivedEq, currentBlocksEq,
      currentLeftDecodes, currentRightDecodes⟩
  let inner := Symbolic.Substitution.castReturnDecompositionWord
    self.derived_eq.symm currentDecomposition
  let composed := composeReturnDecompositions_c2
    self.decomposition inner
  refine {
    marker := currentMarker.flatMap self.decomposition.blocks ++ self.marker
    decomposition := composed
    derived_eq := ?_
    blocks_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }
  · change inner.derived = tower.word stage
    rw [Symbolic.Substitution.castReturnDecompositionWord_derived]
    exact currentDerivedEq
  · intro letter
    change (inner.blocks letter).flatMap self.decomposition.blocks = _
    rw [castReturnDecompositionWord_blocks_c2,
      currentBlocksEq]
    change (returnDecoderSubstitution self.decomposition).mapWord
        (((returnDecoderSubstitution self.decomposition).power
          (level + 1)) letter) = _
    simp only [Symbolic.Substitution.power_apply,
      Symbolic.Substitution.iterateLetter_succ]
  · intro letter
    change (tower.leftSubstitution stage letter).flatMap
        (fun currentLetter =>
          (inner.blocks currentLetter).flatMap self.decomposition.blocks) = _
    rw [← List.flatMap_assoc]
    have hinnerBlocks : ∀ currentLetter,
        inner.blocks currentLetter = currentDecomposition.blocks currentLetter :=
      castReturnDecompositionWord_blocks_c2 self.derived_eq.symm
        currentDecomposition
    have hinnerBlocksFun : inner.blocks = currentDecomposition.blocks :=
      funext hinnerBlocks
    rw [hinnerBlocksFun]
    rw [currentLeftDecodes]
    change _ = (tower.leftSubstitution stage).mapWord
      ((inner.blocks letter).flatMap self.decomposition.blocks)
    rw [hinnerBlocks]
    exact mapWord_flatMap_blocks_c2
      (tower.leftSubstitution stage) (tower.leftSubstitution stage)
      self.decomposition.blocks self.left_decodes
      (currentDecomposition.blocks letter)
  · intro letter
    change (tower.rightSubstitution stage letter).flatMap
        (fun currentLetter =>
          (inner.blocks currentLetter).flatMap self.decomposition.blocks) = _
    rw [← List.flatMap_assoc]
    have hinnerBlocks : ∀ currentLetter,
        inner.blocks currentLetter = currentDecomposition.blocks currentLetter :=
      castReturnDecompositionWord_blocks_c2 self.derived_eq.symm
        currentDecomposition
    have hinnerBlocksFun : inner.blocks = currentDecomposition.blocks :=
      funext hinnerBlocks
    rw [hinnerBlocksFun]
    rw [currentRightDecodes]
    change _ = (tower.rightSubstitution stage).mapWord

      ((inner.blocks letter).flatMap self.decomposition.blocks)
    rw [hinnerBlocks]
    exact mapWord_flatMap_blocks_c2
      (tower.rightSubstitution stage) (tower.rightSubstitution stage)
      self.decomposition.blocks self.right_decodes
      (currentDecomposition.blocks letter)

private def iteratedFirstLetterSelfReturn_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {stage : Nat} (self : FirstLetterSelfReturnC2Local tower stage) :
    ∀ level, IteratedFirstLetterSelfReturnC2Local self level
  | 0 => iteratedFirstLetterSelfReturn_zero_c2 self
  | level + 1 => iteratedFirstLetterSelfReturn_succ_c2 self level
      (iteratedFirstLetterSelfReturn_c2 self level)

/-- A self-return decomposition at a first-letter stage whose every block
contains every letter of that stage alphabet. -/
private structure AllLetterFirstLetterSelfReturnC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) where
  marker : Symbolic.Word (Fin (tower.rank stage))
  decomposition : Symbolic.ReturnDecomposition (tower.word stage)
    marker (tower.rank stage)
  derived_eq : decomposition.derived = tower.word stage
  left_decodes : ∀ letter,
    (tower.leftSubstitution stage letter).flatMap decomposition.blocks =
      (tower.leftSubstitution stage).mapWord (decomposition.blocks letter)
  right_decodes : ∀ letter,
    (tower.rightSubstitution stage letter).flatMap decomposition.blocks =
      (tower.rightSubstitution stage).mapWord (decomposition.blocks letter)
  contains_all : ∀ sourceLetter targetLetter,
    targetLetter ∈ decomposition.blocks sourceLetter

/-- A shifted simultaneous loop can be iterated until every decoder block
contains every stage letter.  Rank one is handled directly; at larger rank,
primitivity of the self-return decoder supplies one common iterate. -/
private theorem firstLetterSelfReturn_has_allLetterIterate_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {stage : Nat} (self : FirstLetterSelfReturnC2Local tower stage) :
    Nonempty (AllLetterFirstLetterSelfReturnC2Local tower stage) := by
  classical
  by_cases hrank : tower.rank stage = 1
  · refine ⟨{
      marker := self.marker
      decomposition := self.decomposition
      derived_eq := self.derived_eq
      left_decodes := self.left_decodes
      right_decodes := self.right_decodes
      contains_all := ?_ }⟩
    intro sourceLetter targetLetter
    obtain ⟨blockHead, blockTail, hblock⟩ :=
      List.exists_cons_of_ne_nil
        (self.decomposition.blocks_are_returns sourceLetter).2.1
    have htarget : targetLetter = blockHead := by
      apply Fin.eq_of_val_eq
      have htargetLt := targetLetter.isLt
      have hheadLt := blockHead.isLt
      omega
    rw [htarget, hblock]
    simp
  · have hrankLarge : 1 < tower.rank stage := by
      have := tower.rank_pos stage
      omega
    obtain ⟨power, hpowerPos, hcontains⟩ :=
      firstLetterSelfReturn_decoder_primitive_c2 self hrankLarge
    let level := power - 1
    have hlevel : level + 1 = power := by
      dsimp [level]
      omega
    let iterated := iteratedFirstLetterSelfReturn_c2 self level
    rcases iterated with
      ⟨marker, decomposition, derivedEq, blocksEq, leftDecodes,
        rightDecodes⟩
    refine ⟨{
      marker := marker
      decomposition := decomposition
      derived_eq := derivedEq
      left_decodes := leftDecodes
      right_decodes := rightDecodes
      contains_all := ?_ }⟩
    intro sourceLetter targetLetter
    rw [blocksEq, hlevel]
    simpa [Symbolic.Substitution.power_apply] using
      hcontains sourceLetter targetLetter

/-- The all-letter self-return, transported to the literal canonical return
alphabet at the same physical marker level. -/
private structure CanonicalAllLetterSelfReturnC2Local
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (tower : IteratedFirstLetterDerivedSystems refinements)
    (stage : Nat) where
  level : Nat
  level_length : level + 1 =
    (firstLetterPhysicalStages_c2 tower stage).marker.length
  relabel : Fin (tower.rank stage) ≃ Fin
    (family.infrastructure.decompositions.rank level)
  word_relabels : ∀ position,
    relabel (tower.word stage position) =
      (family.infrastructure.decompositions.decomposition level).derived
        position
  left_relabels : ∀ letter,
    (tower.leftSubstitution stage letter).map relabel =
      family.infrastructure.left.substitution level (relabel letter)
  right_relabels : ∀ letter,
    (tower.rightSubstitution stage letter).map relabel =
      family.infrastructure.right.substitution level (relabel letter)
  marker : Symbolic.Word
    (Fin (family.infrastructure.decompositions.rank level))
  decomposition : Symbolic.ReturnDecomposition
    (family.infrastructure.decompositions.decomposition level).derived
    marker (family.infrastructure.decompositions.rank level)
  derived_eq : decomposition.derived =
    (family.infrastructure.decompositions.decomposition level).derived
  left_decodes : ∀ letter,
    (family.infrastructure.left.substitution level letter).flatMap
        decomposition.blocks =
      (family.infrastructure.left.substitution level).mapWord
        (decomposition.blocks letter)
  right_decodes : ∀ letter,
    (family.infrastructure.right.substitution level letter).flatMap
        decomposition.blocks =
      (family.infrastructure.right.substitution level).mapWord
        (decomposition.blocks letter)
  contains_all : ∀ sourceLetter targetLetter,
    targetLetter ∈ decomposition.blocks sourceLetter

private theorem allLetterFirstLetterStage_has_canonicalSelfReturn_c2
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {stage : Nat}
    (canonical : FirstLetterCanonicalStageC2Local tower stage)
    (all : AllLetterFirstLetterSelfReturnC2Local tower stage) :
    Nonempty (CanonicalAllLetterSelfReturnC2Local tower stage) := by
  classical
  let coding : Symbolic.LetterCoding
      (Fin (tower.rank stage))
      (Fin (family.infrastructure.decompositions.rank canonical.level)) :=
    ⟨canonical.relabel⟩
  have hword : coding.mapInfinite (tower.word stage) =
      (family.infrastructure.decompositions.decomposition
        canonical.level).derived := by
    funext position
    exact canonical.word_relabels position
  let mapped := all.decomposition.map_injective coding
    canonical.relabel.injective
  have hmappedBlocks : ∀ letter,
      mapped.blocks letter =
        (all.decomposition.blocks letter).map canonical.relabel := by
    intro letter
    rfl
  have hmappedDerived : ∀ position,
      mapped.derived position = all.decomposition.derived position := by
    intro position
    rfl
  let casted := Symbolic.Substitution.castReturnDecompositionWord hword mapped
  let decomposition := reindexReturnDecomposition_c2
    canonical.relabel casted
  have hblocks : ∀ letter,
      decomposition.blocks (canonical.relabel letter) =
        (all.decomposition.blocks letter).map canonical.relabel := by
    intro letter
    simp [decomposition, casted, mapped, coding,
      Symbolic.LetterCoding.mapWord, hmappedBlocks]
  have hderived : decomposition.derived =
      (family.infrastructure.decompositions.decomposition
        canonical.level).derived := by
    funext position
    rw [reindexReturnDecomposition_derived_c2,
      Symbolic.Substitution.castReturnDecompositionWord_derived,
      hmappedDerived, all.derived_eq, canonical.word_relabels]
  refine ⟨{
    level := canonical.level
    level_length := canonical.level_length
    relabel := canonical.relabel
    word_relabels := canonical.word_relabels
    left_relabels := canonical.left_relabels
    right_relabels := canonical.right_relabels
    marker := coding.mapWord all.marker
    decomposition := decomposition
    derived_eq := hderived
    left_decodes := ?_
    right_decodes := ?_
    contains_all := ?_ }⟩
  · intro letter
    let oldLetter := canonical.relabel.symm letter
    have hletter : canonical.relabel oldLetter = letter :=
      canonical.relabel.apply_symm_apply letter
    rw [← hletter]
    calc
      (family.infrastructure.left.substitution canonical.level
          (canonical.relabel oldLetter)).flatMap decomposition.blocks =
          ((tower.leftSubstitution stage oldLetter).map
            canonical.relabel).flatMap decomposition.blocks := by
            rw [canonical.left_relabels]
      _ = ((tower.leftSubstitution stage oldLetter).flatMap
            all.decomposition.blocks).map canonical.relabel :=
          flatMap_relabels_blocks_c2 canonical.relabel
            canonical.relabel all.decomposition.blocks decomposition.blocks
            hblocks _
      _ = ((tower.leftSubstitution stage).mapWord
            (all.decomposition.blocks oldLetter)).map canonical.relabel := by
          rw [all.left_decodes]
      _ = (family.infrastructure.left.substitution canonical.level).mapWord
            ((all.decomposition.blocks oldLetter).map canonical.relabel) :=
          mapWord_relabels_c2 canonical.relabel
            canonical.left_relabels _
      _ = (family.infrastructure.left.substitution canonical.level).mapWord
            (decomposition.blocks (canonical.relabel oldLetter)) := by
          rw [hblocks]
  · intro letter
    let oldLetter := canonical.relabel.symm letter
    have hletter : canonical.relabel oldLetter = letter :=
      canonical.relabel.apply_symm_apply letter
    rw [← hletter]
    calc
      (family.infrastructure.right.substitution canonical.level
          (canonical.relabel oldLetter)).flatMap decomposition.blocks =
          ((tower.rightSubstitution stage oldLetter).map
            canonical.relabel).flatMap decomposition.blocks := by
            rw [canonical.right_relabels]
      _ = ((tower.rightSubstitution stage oldLetter).flatMap
            all.decomposition.blocks).map canonical.relabel :=
          flatMap_relabels_blocks_c2 canonical.relabel
            canonical.relabel all.decomposition.blocks decomposition.blocks
            hblocks _
      _ = ((tower.rightSubstitution stage).mapWord
            (all.decomposition.blocks oldLetter)).map canonical.relabel := by
          rw [all.right_decodes]
      _ = (family.infrastructure.right.substitution canonical.level).mapWord
            ((all.decomposition.blocks oldLetter).map canonical.relabel) :=
          mapWord_relabels_c2 canonical.relabel
            canonical.right_relabels _
      _ = (family.infrastructure.right.substitution canonical.level).mapWord
            (decomposition.blocks (canonical.relabel oldLetter)) := by
          rw [hblocks]
  · intro sourceLetter targetLetter
    rw [← canonical.relabel.apply_symm_apply sourceLetter, hblocks]
    exact List.mem_map.mpr
      ⟨canonical.relabel.symm targetLetter,
        all.contains_all _ _, canonical.relabel.apply_symm_apply _⟩

private theorem iterateLetter_prefix_of_le_c2
    {alphabet : Type*} {substitution : Symbolic.Substitution alphabet}
    {seed : alphabet} (hprolongable : substitution.ProlongableOn seed)
    {earlier later : Nat} (hle : earlier ≤ later) :
    substitution.iterateLetter earlier seed <+:
      substitution.iterateLetter later seed := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simp
  | succ extra ih =>
      simpa [Nat.add_assoc] using ih.trans
        (substitution.iterateLetter_prefix_succ hprolongable
          (earlier + extra))

private theorem mapWord_id_c2
    {alphabet : Type*} (letters : Symbolic.Word alphabet) :
    Symbolic.Substitution.id.mapWord letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih => simp [ih]

private theorem mapWord_comp_c2
    {alphabet : Type*} (left right : Symbolic.Substitution alphabet)
    (letters : Symbolic.Word alphabet) :
    (left.comp right).mapWord letters =

      left.mapWord (right.mapWord letters) := by
  induction letters with
  | nil => rfl
  | cons letter rest ih => simp [ih]

private theorem power_mapWord_c2
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet) :
    ∀ power letters,
      (substitution.power power).mapWord letters =
        substitution.iterateWord power letters
  | 0, letters => mapWord_id_c2 letters
  | power + 1, letters => by
      rw [Symbolic.Substitution.power_succ,
        mapWord_comp_c2, power_mapWord_c2]
      rfl

private theorem substitution_ext_c2
    {alphabet : Type*} (left right : Symbolic.Substitution alphabet)
    (himages : ∀ letter, left letter = right letter) : left = right := by
  cases left with
  | mk leftImage leftNonempty =>
      cases right with
      | mk rightImage rightNonempty =>
          have himage : leftImage = rightImage := funext himages
          subst rightImage
          rfl

/-- A blockwise commuting equation remains valid for every substitution
power. -/
private theorem decodingEquation_power_c2
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet)
    (blocks : alphabet → Symbolic.Word alphabet)
    (hdecode : ∀ letter,
      (substitution letter).flatMap blocks =
        substitution.mapWord (blocks letter)) :
    ∀ power letter,
      ((substitution.power power) letter).flatMap blocks =
        (substitution.power power).mapWord (blocks letter) := by
  intro power letter
  rw [Symbolic.Substitution.power_apply,
    power_mapWord_c2]
  induction power with
  | zero =>
      simp [Symbolic.Substitution.iterateLetter,
        Symbolic.Substitution.iterateWord]
  | succ power ih =>
      change (substitution.mapWord
          (substitution.iterateLetter power letter)).flatMap blocks =
        substitution.mapWord
          (substitution.iterateWord power (blocks letter))
      rw [mapWord_flatMap_blocks_c2 substitution substitution
        blocks hdecode, ih]

/-- A letterwise relabeling of substitutions also relabels every power. -/
private theorem substitutionPower_relabels_c2
    {alpha beta : Type*}
    (source : Symbolic.Substitution alpha)
    (target : Symbolic.Substitution beta)
    (relabel : alpha ≃ beta)
    (hletter : ∀ letter,
      (source letter).map relabel = target (relabel letter)) :
    ∀ power letter,
      ((source.power power) letter).map relabel =
        (target.power power) (relabel letter) := by
  intro power
  induction power with
  | zero => intro letter; simp [Symbolic.Substitution.power_apply]
  | succ power ih =>
      intro letter
      change (source.mapWord ((source.power power) letter)).map relabel =
        target.mapWord ((target.power power) (relabel letter))
      rw [mapWord_relabels_c2 relabel hletter, ih]

private structure SelfReturnSourcePowerC2Local
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (source : Symbolic.Substitution (Fin rank)) (power : Nat) where
  induced : PrefixReturnSubstitutionFactorization
    (source.power power) decomposition
  induced_eq : induced.substitution = source.power power
  images_begin_head : ∀ letter, [word.head] <+:
    (source.power power) letter

/-- Once the seed iterate covers the first return block and the following
marker, a commuting source power has a unique return parsing and every image
starts at the derived-word head. -/
private theorem selfReturn_has_sourcePower_c2
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (hderived : decomposition.derived = word)
    (source : Symbolic.Substitution (Fin rank))
    (hfixed : source.IsFixedPoint word)
    (hdecode : ∀ letter,
      (source letter).flatMap decomposition.blocks =
        source.mapWord (decomposition.blocks letter))
    {power : Nat} (hpower : 0 < power)
    (hlong : (decomposition.blocks word.head ++ marker).length ≤
      (source.iterateLetter power word.head).length) :
    Nonempty (SelfReturnSourcePowerC2Local
      decomposition source power) := by
  classical
  have hdecodePower := decodingEquation_power_c2 source
    decomposition.blocks hdecode
  have hpowerFixed : (source.power power).IsFixedPoint word :=
    Symbolic.Substitution.isFixedPoint_power hfixed hpower
  obtain ⟨factorization⟩ :=
    exists_prefixReturnSubstitutionFactorization hpowerFixed decomposition
  have hinduced : factorization.substitution = source.power power := by
    apply substitution_ext_c2
    intro letter
    exact (factorization.factor_unique letter _
      (hdecodePower power letter)).symm
  have hblockMarkerAtZero := decomposition.block_marker_at_cut 0
  rw [decomposition.cut_zero, hderived] at hblockMarkerAtZero
  change Symbolic.InfiniteFactorAt word
      (decomposition.blocks word.head ++ marker) 0 at hblockMarkerAtZero
  have hblockMarkerTake :
      word.take (decomposition.blocks word.head ++ marker).length =
        decomposition.blocks word.head ++ marker := by
    simpa [Symbolic.InfiniteFactorAt] using hblockMarkerAtZero
  have hseedIterateTake :=
    Symbolic.Substitution.iterateLetter_eq_take_of_fixedPoint
      hfixed rfl power
  have hblockMarkerSeedPrefix :
      decomposition.blocks word.head ++ marker <+:
        source.iterateLetter power word.head := by
    have htakes := Stream'.take_prefix_take_left
      (a := word)
      (m := (decomposition.blocks word.head ++ marker).length)
      (n := (source.iterateLetter power word.head).length) hlong
    rw [hblockMarkerTake, ← hseedIterateTake] at htakes
    exact htakes
  have hblockMarkerImagePrefix : ∀ letter,
      decomposition.blocks word.head ++ marker <+:
        (source.power power).mapWord
          (decomposition.blocks letter) := by
    intro letter
    have hblockBegins : [word.head] <+:
        decomposition.blocks letter :=
      returnBlocks_begin_head_c2 decomposition letter
    have himage :=
      Symbolic.Substitution.mapWord_prefix
        (σ := source.power power) hblockBegins
    have hseedPrefix : source.iterateLetter power word.head <+:
        (source.power power).mapWord
          (decomposition.blocks letter) := by
      simpa [Symbolic.Substitution.power_apply] using himage
    exact hblockMarkerSeedPrefix.trans hseedPrefix
  refine ⟨{
    induced := factorization
    induced_eq := hinduced
    images_begin_head := ?_ }⟩
  intro letter
  obtain ⟨position, hposition⟩ :=
    decomposition.every_letter_occurs letter
  have hfactorAt := factorization.derived_factor_at position
  change Symbolic.InfiniteFactorAt decomposition.derived
      (factorization.substitution (decomposition.derived position))
      (factorization.boundary position) at hfactorAt
  rw [hposition, hinduced] at hfactorAt
  have htaken :
      (decomposition.derived.drop (factorization.boundary position)).take
          ((source.power power) letter).length =
        (source.power power) letter := by
    simpa [Symbolic.InfiniteFactorAt] using hfactorAt
  have hdecoded := decomposition.decoded_marker_at_cut
    (factorization.boundary position) ((source.power power) letter).length
  rw [htaken] at hdecoded
  have hdecodedPrefix : decomposition.blocks word.head ++ marker <+:
      ((source.power power) letter).flatMap decomposition.blocks := by
    rw [hdecodePower power letter]
    exact hblockMarkerImagePrefix letter
  have hfullPrefix : decomposition.blocks word.head ++ marker <+:
      ((source.power power) letter).flatMap decomposition.blocks ++ marker :=
    hdecodedPrefix.trans (List.prefix_append _ _)
  have hfinite : Symbolic.FiniteFactorAt
      (((source.power power) letter).flatMap decomposition.blocks ++ marker)
      (decomposition.blocks word.head ++ marker) 0 := by
    refine ⟨by simpa using hfullPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hfullPrefix).symm
  have hblockAt := hdecoded.of_finiteFactorAt hfinite
  have hblockEq := decomposition.block_eq_of_block_marker_at_cut
    word.head (factorization.boundary position) hblockAt
  have hseedAtBoundary : word.head =
      decomposition.derived (factorization.boundary position) :=
    decomposition.blocks_injective hblockEq
  obtain ⟨imageHead, imageTail, himage⟩ :=
    List.exists_cons_of_ne_nil
      ((source.power power).image_ne_nil letter)
  have hfactorHead :
      decomposition.derived (factorization.boundary position) =
        imageHead := by
    rw [Symbolic.InfiniteFactorAt, himage, List.length_cons,
      Stream'.take_succ] at hfactorAt
    simpa [Stream'.head_drop, Stream'.get] using
      (List.cons.inj hfactorAt).1
  have hseedHead : word.head = imageHead :=
    hseedAtBoundary.trans hfactorHead
  rw [himage, hseedHead]
  simp

/-- C2.3: choose a still deeper realization in the original cofinal marker
tower.  The common return decoder sees every letter, and one shared positive
power makes every left/right image begin at the common seed. -/
structure DeepAllLetterSeedPoweringData
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    (repetition : SimultaneousFirstLetterDerivedRepetition tower) where
  selectedStage : Nat
  repetition_lt_selected : repetition.later < selectedStage
  selectedLevel : Nat
  common_lt_selected : aligned.commonLevel < selectedLevel
  stageRelabel : Fin (tower.rank selectedStage) ≃ Fin
    (family.infrastructure.decompositions.rank selectedLevel)
  stage_word_eq : ∀ position,
    stageRelabel (tower.word selectedStage position) =
      (family.infrastructure.decompositions.decomposition
        selectedLevel).derived position
  commonToSelected : Symbolic.NestedReturnFactorization
    (family.infrastructure.decompositions.decomposition aligned.commonLevel)
    (family.infrastructure.decompositions.decomposition selectedLevel)
  commonPower : Nat
  commonPower_pos : 0 < commonPower
  left_stage_power_eq : ∀ letter,
    ((tower.leftSubstitution selectedStage).power commonPower letter).map
        stageRelabel =
      (family.infrastructure.left.substitution selectedLevel).power
        commonPower (stageRelabel letter)
  right_stage_power_eq : ∀ letter,
    ((tower.rightSubstitution selectedStage).power commonPower letter).map
        stageRelabel =
      (family.infrastructure.right.substitution selectedLevel).power
        commonPower (stageRelabel letter)
  seed : Fin (family.infrastructure.decompositions.rank selectedLevel)
  seed_is_head : seed =
    (family.infrastructure.decompositions.decomposition selectedLevel).derived.head
  left_seed_eq : family.infrastructure.left.seed selectedLevel = seed
  right_seed_eq : family.infrastructure.right.seed selectedLevel = seed
  marker : Symbolic.Word
    (Fin (family.infrastructure.decompositions.rank selectedLevel))
  decomposition : Symbolic.ReturnDecomposition
    (family.infrastructure.decompositions.decomposition selectedLevel).derived
    marker (family.infrastructure.decompositions.rank selectedLevel)
  derived_eq : decomposition.derived =
    (family.infrastructure.decompositions.decomposition selectedLevel).derived
  leftInduced : PrefixReturnSubstitutionFactorization
    ((family.infrastructure.left.substitution selectedLevel).power commonPower)
      decomposition
  rightInduced : PrefixReturnSubstitutionFactorization
    ((family.infrastructure.right.substitution selectedLevel).power commonPower)
      decomposition
  left_induced_eq : leftInduced.substitution =
    (family.infrastructure.left.substitution selectedLevel).power commonPower
  right_induced_eq : rightInduced.substitution =
    (family.infrastructure.right.substitution selectedLevel).power commonPower
  left_images_begin_seed : ∀ letter,
    [seed] <+:
      (family.infrastructure.left.substitution selectedLevel).power
        commonPower letter
  right_images_begin_seed : ∀ letter,
    [seed] <+:
      (family.infrastructure.right.substitution selectedLevel).power
        commonPower letter
  decoder_contains_all : ∀ sourceLetter targetLetter,
    targetLetter ∈ decomposition.blocks sourceLetter

/-- Leaf C2.3: simultaneous recurrence supplies a deep all-letter return
decoder and a common seed-stabilizing source power. -/
theorem simultaneousRepetition_has_deepAllLetterSeedPowering
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    (repetition : SimultaneousFirstLetterDerivedRepetition tower) :
    Nonempty (DeepAllLetterSeedPoweringData repetition) := by
  classical
  let selectedStage := repetition.later + 1
  obtain ⟨self⟩ :=
    simultaneousRepetition_has_successorSelfReturn_c2 repetition
  obtain ⟨allStage⟩ :=
    firstLetterSelfReturn_has_allLetterIterate_c2 self
  let canonical := firstLetterCanonicalStages_c2 tower selectedStage
  obtain ⟨canonicalAll⟩ :=
    allLetterFirstLetterStage_has_canonicalSelfReturn_c2
      canonical allStage
  have hselectedPositive : 0 < selectedStage := by
    dsimp [selectedStage]
    omega
  have hcommonLt : aligned.commonLevel < canonicalAll.level := by
    have hbase := firstLetterPhysical_base_marker_length_c2 tower
    have hlower := firstLetterPhysical_marker_length_lower_c2
      tower selectedStage
    have hlevel := canonicalAll.level_length
    omega
  let selectedWord :=
    (family.infrastructure.decompositions.decomposition
      canonicalAll.level).derived
  let seed := selectedWord.head
  let leftSource := family.infrastructure.left.substitution
    canonicalAll.level
  let rightSource := family.infrastructure.right.substitution
    canonicalAll.level
  have hleftFixed : leftSource.IsFixedPoint selectedWord := by
    exact family.infrastructure.left.fixed canonicalAll.level
  have hrightFixed : rightSource.IsFixedPoint selectedWord := by
    exact family.infrastructure.right.fixed canonicalAll.level
  have hleftGrow : LetterImagesGrow leftSource seed := by
    have hgrow := family.infrastructure.left.images_grow canonicalAll.level
    rw [family.infrastructure.left.seed_is_head canonicalAll.level] at hgrow
    exact hgrow
  have hrightGrow : LetterImagesGrow rightSource seed := by
    have hgrow := family.infrastructure.right.images_grow canonicalAll.level
    rw [family.infrastructure.right.seed_is_head canonicalAll.level] at hgrow
    exact hgrow
  have hleftProlongable : leftSource.ProlongableOn seed := by
    have hprolongable :=
      family.infrastructure.left.prolongable canonicalAll.level
    rw [family.infrastructure.left.seed_is_head canonicalAll.level]
      at hprolongable
    exact hprolongable
  have hrightProlongable : rightSource.ProlongableOn seed := by
    have hprolongable :=
      family.infrastructure.right.prolongable canonicalAll.level
    rw [family.infrastructure.right.seed_is_head canonicalAll.level]
      at hprolongable
    exact hprolongable
  let coverLength :=
    (canonicalAll.decomposition.blocks seed ++ canonicalAll.marker).length
  have hcoverLarge : 1 < coverLength := by
    have hblock := canonicalAll.decomposition.block_length_pos seed
    have hmarker := List.length_pos_of_ne_nil
      canonicalAll.decomposition.marker_ne_nil
    dsimp [coverLength]
    simp only [List.length_append]
    omega
  obtain ⟨leftDepth, hleftDepth⟩ := hleftGrow coverLength
  obtain ⟨rightDepth, hrightDepth⟩ := hrightGrow coverLength
  have hleftDepthPos : 0 < leftDepth := by
    by_contra hnot
    have hzero : leftDepth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hleftDepth
    simp [Symbolic.Substitution.iterateLetter] at hleftDepth
    omega
  have hrightDepthPos : 0 < rightDepth := by
    by_contra hnot
    have hzero : rightDepth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hrightDepth
    simp [Symbolic.Substitution.iterateLetter] at hrightDepth
    omega
  let commonPower := max leftDepth rightDepth
  have hcommonPowerPos : 0 < commonPower := by
    dsimp [commonPower]
    omega
  have hleftLong : coverLength ≤
      (leftSource.iterateLetter commonPower seed).length := by
    exact hleftDepth.trans
      (iterateLetter_prefix_of_le_c2 hleftProlongable
        (Nat.le_max_left leftDepth rightDepth)).length_le
  have hrightLong : coverLength ≤
      (rightSource.iterateLetter commonPower seed).length := by
    exact hrightDepth.trans
      (iterateLetter_prefix_of_le_c2 hrightProlongable
        (Nat.le_max_right leftDepth rightDepth)).length_le
  obtain ⟨leftPowered⟩ := selfReturn_has_sourcePower_c2
    canonicalAll.decomposition canonicalAll.derived_eq leftSource hleftFixed
      canonicalAll.left_decodes hcommonPowerPos hleftLong
  obtain ⟨rightPowered⟩ := selfReturn_has_sourcePower_c2
    canonicalAll.decomposition canonicalAll.derived_eq rightSource hrightFixed
      canonicalAll.right_decodes hcommonPowerPos hrightLong
  refine ⟨{
    selectedStage := selectedStage
    repetition_lt_selected := by dsimp [selectedStage]; omega
    selectedLevel := canonicalAll.level
    common_lt_selected := hcommonLt
    stageRelabel := canonicalAll.relabel
    stage_word_eq := canonicalAll.word_relabels
    commonToSelected :=
      family.infrastructure.nested.factorization hcommonLt
    commonPower := commonPower
    commonPower_pos := hcommonPowerPos
    left_stage_power_eq := ?_
    right_stage_power_eq := ?_
    seed := seed
    seed_is_head := rfl
    left_seed_eq := family.infrastructure.left.seed_is_head canonicalAll.level
    right_seed_eq := family.infrastructure.right.seed_is_head canonicalAll.level
    marker := canonicalAll.marker
    decomposition := canonicalAll.decomposition
    derived_eq := canonicalAll.derived_eq
    leftInduced := leftPowered.induced
    rightInduced := rightPowered.induced
    left_induced_eq := leftPowered.induced_eq
    right_induced_eq := rightPowered.induced_eq
    left_images_begin_seed := leftPowered.images_begin_head
    right_images_begin_seed := rightPowered.images_begin_head
    decoder_contains_all := canonicalAll.contains_all }⟩
  · intro letter
    exact substitutionPower_relabels_c2
      (tower.leftSubstitution selectedStage) leftSource canonicalAll.relabel
      canonicalAll.left_relabels commonPower letter
  · intro letter
    exact substitutionPower_relabels_c2
      (tower.rightSubstitution selectedStage) rightSource canonicalAll.relabel
      canonicalAll.right_relabels commonPower letter

/-- C2.4: the proof-only part of the simultaneous Proposition-10 package.
All substitutions and growths refer to the shared positive power selected in
the preceding combinatorial stage. -/
structure DurandCommonProposition10Package
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {repetition : SimultaneousFirstLetterDerivedRepetition tower}
    (deep : DeepAllLetterSeedPoweringData repetition) where
  word_aperiodic : ¬ Symbolic.IsPeriodic
    (family.infrastructure.decompositions.decomposition deep.selectedLevel).derived
  left_power_fixed :
    ((family.infrastructure.left.substitution deep.selectedLevel).power
      deep.commonPower).IsFixedPoint
        (family.infrastructure.decompositions.decomposition
          deep.selectedLevel).derived
  right_power_fixed :
    ((family.infrastructure.right.substitution deep.selectedLevel).power
      deep.commonPower).IsFixedPoint
        (family.infrastructure.decompositions.decomposition
          deep.selectedLevel).derived
  left_power_primitive : IsPrimitiveSubstitution
    ((family.infrastructure.left.substitution deep.selectedLevel).power
      deep.commonPower)
  right_power_primitive : IsPrimitiveSubstitution
    ((family.infrastructure.right.substitution deep.selectedLevel).power
      deep.commonPower)
  left_power_prolongable :
    ((family.infrastructure.left.substitution deep.selectedLevel).power
      deep.commonPower).ProlongableOn deep.seed
  right_power_prolongable :
    ((family.infrastructure.right.substitution deep.selectedLevel).power
      deep.commonPower).ProlongableOn deep.seed
  left_power_dominant : IsDominantEigenvalue
    ((family.infrastructure.left.substitution deep.selectedLevel).power
      deep.commonPower).incidenceMatrix
      ((a ^ family.infrastructure.left.exponent) ^ deep.commonPower)
  right_power_dominant : IsDominantEigenvalue
    ((family.infrastructure.right.substitution deep.selectedLevel).power
      deep.commonPower).incidenceMatrix
      ((b ^ family.infrastructure.right.exponent) ^ deep.commonPower)
  decoder_fixed :
    (returnDecoderSubstitution deep.decomposition).IsFixedPoint
      (family.infrastructure.decompositions.decomposition
        deep.selectedLevel).derived
  decoder_prolongable :
    (returnDecoderSubstitution deep.decomposition).ProlongableOn deep.seed
  decoder_generating :
    (returnDecoderSubstitution deep.decomposition).IsGeneratingLetter deep.seed
  decoder_primitive :
    IsPrimitiveSubstitution (returnDecoderSubstitution deep.decomposition)

/-- Leaf C2.4: verify aperiodicity and package fixedness, primitivity,
prolongability, all-letter occurrence, and powered Perron data. -/
theorem deepAllLetterSeedPowering_has_proposition10Package
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {repetition : SimultaneousFirstLetterDerivedRepetition tower}
    (deep : DeepAllLetterSeedPoweringData repetition)
    (_notPeriodicLanguage :
      ¬ Symbolic.HasPeriodicRecurrentLanguage data.word) :
    Nonempty (DurandCommonProposition10Package deep) := by
  classical
  have hwordAperiodic : ¬ Symbolic.IsPeriodic
      (family.infrastructure.decompositions.decomposition
        deep.selectedLevel).derived := by
    intro hperiodic
    apply _notPeriodicLanguage
    exact returnDecomposition_derivedPeriodic_hasPeriodicRecurrentLanguage
      input.core
      (family.infrastructure.decompositions.decomposition deep.selectedLevel)
      hperiodic
  have hleftFixed :
      ((family.infrastructure.left.substitution deep.selectedLevel).power
        deep.commonPower).IsFixedPoint
          (family.infrastructure.decompositions.decomposition
            deep.selectedLevel).derived :=
    Symbolic.Substitution.isFixedPoint_power
      (family.infrastructure.left.fixed deep.selectedLevel)
      deep.commonPower_pos
  have hrightFixed :
      ((family.infrastructure.right.substitution deep.selectedLevel).power
        deep.commonPower).IsFixedPoint
          (family.infrastructure.decompositions.decomposition
            deep.selectedLevel).derived :=
    Symbolic.Substitution.isFixedPoint_power
      (family.infrastructure.right.fixed deep.selectedLevel)
      deep.commonPower_pos
  have hleftPrimitive : IsPrimitiveSubstitution
      ((family.infrastructure.left.substitution deep.selectedLevel).power
        deep.commonPower) :=
    Symbolic.Substitution.primitive_power
      (family.infrastructure.left.substitution deep.selectedLevel)
      (family.infrastructure.left.primitive deep.selectedLevel)
      deep.commonPower_pos
  have hrightPrimitive : IsPrimitiveSubstitution
      ((family.infrastructure.right.substitution deep.selectedLevel).power
        deep.commonPower) :=
    Symbolic.Substitution.primitive_power
      (family.infrastructure.right.substitution deep.selectedLevel)
      (family.infrastructure.right.primitive deep.selectedLevel)
      deep.commonPower_pos
  have hleftProlongable :
      ((family.infrastructure.left.substitution deep.selectedLevel).power
        deep.commonPower).ProlongableOn deep.seed := by
    rw [← deep.left_seed_eq]
    exact Symbolic.Substitution.prolongableOn_power
      (family.infrastructure.left.prolongable deep.selectedLevel)
      deep.commonPower_pos
  have hrightProlongable :
      ((family.infrastructure.right.substitution deep.selectedLevel).power
        deep.commonPower).ProlongableOn deep.seed := by
    rw [← deep.right_seed_eq]
    exact Symbolic.Substitution.prolongableOn_power
      (family.infrastructure.right.prolongable deep.selectedLevel)
      deep.commonPower_pos
  have hleftDominant : IsDominantEigenvalue
      ((family.infrastructure.left.substitution deep.selectedLevel).power
        deep.commonPower).incidenceMatrix
      ((a ^ family.infrastructure.left.exponent) ^ deep.commonPower) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    exact dominantEigenvalue_pow
      (family.infrastructure.left.substitution deep.selectedLevel).incidenceMatrix
      (a ^ family.infrastructure.left.exponent)
      (family.infrastructure.left.dominant deep.selectedLevel)
      deep.commonPower_pos
  have hrightDominant : IsDominantEigenvalue
      ((family.infrastructure.right.substitution deep.selectedLevel).power
        deep.commonPower).incidenceMatrix
      ((b ^ family.infrastructure.right.exponent) ^ deep.commonPower) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    exact dominantEigenvalue_pow
      (family.infrastructure.right.substitution deep.selectedLevel).incidenceMatrix
      (b ^ family.infrastructure.right.exponent)
      (family.infrastructure.right.dominant deep.selectedLevel)
      deep.commonPower_pos
  have hdecoderFixed :
      (returnDecoderSubstitution deep.decomposition).IsFixedPoint
        (family.infrastructure.decompositions.decomposition
          deep.selectedLevel).derived := by
    have hdecode :=
      returnDecoderSubstitution_mapInfinite_derived deep.decomposition
    rw [deep.derived_eq] at hdecode
    exact hdecode
  have hdecoderPrimitive :
      IsPrimitiveSubstitution
        (returnDecoderSubstitution deep.decomposition) := by
    refine ⟨1, by omega, ?_⟩
    intro sourceLetter targetLetter
    simpa [Symbolic.Substitution.iterateLetter,
      Symbolic.Substitution.iterateWord,
      Symbolic.Substitution.mapWord, returnDecoderSubstitution] using
      deep.decoder_contains_all sourceLetter targetLetter
  have hdecoderGenerating :
      (returnDecoderSubstitution deep.decomposition).IsGeneratingLetter
        deep.seed := by
    intro targetLetter
    refine ⟨1, ?_⟩
    simpa [Symbolic.Substitution.iterateLetter,
      Symbolic.Substitution.iterateWord,
      Symbolic.Substitution.mapWord, returnDecoderSubstitution,
      Symbolic.Substitution.OccursInWord] using
      deep.decoder_contains_all deep.seed targetLetter
  let selectedRank :=
    family.infrastructure.decompositions.rank deep.selectedLevel
  have hselectedRank : 1 < selectedRank := by
    by_contra hnot
    have hle : selectedRank ≤ 1 := Nat.le_of_not_gt hnot
    apply hwordAperiodic
    refine ⟨1, by omega, ?_⟩
    intro position
    apply Fin.ext
    have hl := ((family.infrastructure.decompositions.decomposition
      deep.selectedLevel).derived (position + 1)).isLt
    have hr := ((family.infrastructure.decompositions.decomposition
      deep.selectedLevel).derived position).isLt
    change family.infrastructure.decompositions.rank deep.selectedLevel ≤ 1 at hle
    omega
  obtain ⟨otherLetter, hotherLetter⟩ :=
    Fintype.exists_ne_of_one_lt_card
      (by simpa [selectedRank] using hselectedRank) deep.seed
  have mem_eq_of_length_le_one
      (letters : List (Fin selectedRank)) (hlength : letters.length ≤ 1) :
      ∀ {left right : Fin selectedRank},
        left ∈ letters → right ∈ letters → left = right := by
    cases letters with
    | nil => simp
    | cons head tail =>
        cases tail with
        | nil => simp
        | cons next rest => simp at hlength
  have hdecoderSeedLength :
      1 < (returnDecoderSubstitution deep.decomposition deep.seed).length := by
    by_contra hnot
    have hle := Nat.le_of_not_gt hnot
    have hequal := mem_eq_of_length_le_one
      (returnDecoderSubstitution deep.decomposition deep.seed) hle
      (deep.decoder_contains_all deep.seed deep.seed)
      (deep.decoder_contains_all deep.seed otherLetter)
    exact hotherLetter hequal.symm
  have hdecoderProlongable :
      (returnDecoderSubstitution deep.decomposition).ProlongableOn
        deep.seed := by
    have hdecoderHeadLength := hdecoderSeedLength
    rw [deep.seed_is_head] at hdecoderHeadLength
    rw [deep.seed_is_head]
    exact Symbolic.Substitution.prolongableOn_head_of_fixedPoint
      hdecoderFixed hdecoderHeadLength
  exact ⟨{
    word_aperiodic := hwordAperiodic
    left_power_fixed := hleftFixed
    right_power_fixed := hrightFixed
    left_power_primitive := hleftPrimitive
    right_power_primitive := hrightPrimitive
    left_power_prolongable := hleftProlongable
    right_power_prolongable := hrightProlongable
    left_power_dominant := hleftDominant
    right_power_dominant := hrightDominant
    decoder_fixed := hdecoderFixed
    decoder_prolongable := hdecoderProlongable
    decoder_generating := hdecoderGenerating
    decoder_primitive := hdecoderPrimitive }⟩

/-- Proved C2.5 packaging of the combinatorial and proof-only halves. -/
theorem durandProposition10Package_to_commonDerivedSystem
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {tower : IteratedFirstLetterDerivedSystems refinements}
    {repetition : SimultaneousFirstLetterDerivedRepetition tower}
    {deep : DeepAllLetterSeedPoweringData repetition}
    (package : DurandCommonProposition10Package deep) :
    Nonempty (DurandCommonDerivedSystem refinements) := by
  exact ⟨{
    selectedLevel := deep.selectedLevel
    common_lt_selected := deep.common_lt_selected
    commonToSelected := deep.commonToSelected
    commonPower := deep.commonPower
    commonPower_pos := deep.commonPower_pos
    seed := deep.seed
    seed_is_head := deep.seed_is_head
    left_seed_eq := deep.left_seed_eq
    right_seed_eq := deep.right_seed_eq
    marker := deep.marker
    decomposition := deep.decomposition
    derived_eq := deep.derived_eq
    leftInduced := deep.leftInduced
    rightInduced := deep.rightInduced
    left_induced_eq := deep.left_induced_eq
    right_induced_eq := deep.right_induced_eq
    left_power_fixed := package.left_power_fixed
    right_power_fixed := package.right_power_fixed
    left_power_primitive := package.left_power_primitive
    right_power_primitive := package.right_power_primitive
    left_power_prolongable := package.left_power_prolongable
    right_power_prolongable := package.right_power_prolongable
    left_power_dominant := package.left_power_dominant
    right_power_dominant := package.right_power_dominant
    left_images_begin_seed := deep.left_images_begin_seed
    right_images_begin_seed := deep.right_images_begin_seed
    word_aperiodic := package.word_aperiodic
    decoder_fixed := package.decoder_fixed
    decoder_prolongable := package.decoder_prolongable
    decoder_generating := package.decoder_generating
    decoder_primitive := package.decoder_primitive
    decoder_contains_all := deep.decoder_contains_all }⟩

/-- Proved C2 / Durand Lemma 12 aggregator: refine beyond the aligned
repetitions until both exact powered return substitutions, on the same
derived system, satisfy all four Proposition 10 hypotheses. -/
theorem construct_durandCommonDerivedSystem
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    (refinements : AlignedNestedIntertwiningData aligned)
    (_notPeriodicLanguage :
      ¬ Symbolic.HasPeriodicRecurrentLanguage data.word) :
    Nonempty (DurandCommonDerivedSystem refinements) := by
  obtain ⟨tower⟩ := alignedSystems_have_iteratedFirstLetterDerivedSystems
    refinements _notPeriodicLanguage
  obtain ⟨repetition⟩ :=
    iteratedFirstLetterSystems_have_simultaneousRepetition tower
  obtain ⟨deep⟩ :=
    simultaneousRepetition_has_deepAllLetterSeedPowering repetition
  obtain ⟨package⟩ := deepAllLetterSeedPowering_has_proposition10Package
    deep _notPeriodicLanguage
  exact durandProposition10Package_to_commonDerivedSystem package

/-- Exact `Theta^l ∘ gamma = gamma ∘ Theta^l = source^p` data from
Durand's Proposition 10.  Both exponent sequences are genuinely cofinal and
every image of the auxiliary morphism is nonempty. -/
structure DurandPowerEquationFamily
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source) where
  sourcePower : Nat → Nat
  sourcePower_strictMono : StrictMono sourcePower
  sourcePower_zero_pos : 0 < sourcePower 0
  refinementPower : Nat → Nat
  refinementPower_strictMono : StrictMono refinementPower
  refinementPower_zero_pos : 0 < refinementPower 0
  gamma : Symbolic.Substitution (Fin rank)
  gamma_nonempty : ∀ letter, gamma letter ≠ []
  theta_comp_gamma : ∀ index,
    ((returnDecoderSubstitution input.decomposition).power
          (refinementPower index)).comp gamma =
      source.power (sourcePower index)
  gamma_comp_theta : ∀ index,
    gamma.comp ((returnDecoderSubstitution input.decomposition).power
      (refinementPower index)) = source.power (sourcePower index)

/-- A two-sided factorization of one source power through one power of the
return decoder.  Naming this predicate makes the maximality condition in the
preliminary `gamma_k` construction explicit. -/
def HasTwoSidedDecoderFactorization
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source)
    (sourceExponent refinementExponent : Nat) : Prop :=
  ∃ gamma : Symbolic.Substitution (Fin rank),
    ((returnDecoderSubstitution input.decomposition).power
        refinementExponent).comp gamma = source.power sourceExponent ∧
      gamma.comp
        ((returnDecoderSubstitution input.decomposition).power
          refinementExponent) = source.power sourceExponent

/-- The exact iterated-return tower used in Durand's Proposition 10.  Level
`n` is the return decomposition at
`Theta^n(u) Theta^(n-1)(u) ... Theta(u) u`; its decoder is literally
`Theta^(n+1)`, and its derived word is again the original fixed word. -/
structure DurandIteratedDecoderTower
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source) where
  marker : Nat → Symbolic.Word (Fin rank)
  decomposition : ∀ level : Nat,
    Symbolic.ReturnDecomposition word (marker level) rank
  marker_zero : marker 0 = input.marker
  marker_succ : ∀ level : Nat,
    marker (level + 1) =
      (returnDecoderSubstitution input.decomposition).mapWord
          (marker level) ++ input.marker
  derived_eq : ∀ level : Nat, (decomposition level).derived = word
  blocks_eq : ∀ level (letter : Fin rank),
    (decomposition level).blocks letter =
      ((returnDecoderSubstitution input.decomposition).power
        (level + 1)) letter

/-- Decoding a return word of the derived sequence gives a return word of
the original sequence at the composed marker.  This is the finite-word core
of the return-decomposition composition used in Proposition 10. -/
private theorem decodedReturnWord_of_derivedReturnWord_b9
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {outerRank : Nat}
    (outer : Symbolic.ReturnDecomposition word marker outerRank)
    {innerMarker innerBlock : Symbolic.Word (Fin outerRank)}
    (hreturn : Symbolic.IsReturnWord outer.derived innerMarker innerBlock) :
    Symbolic.IsReturnWord word
      (innerMarker.flatMap outer.blocks ++ marker)
      (innerBlock.flatMap outer.blocks) := by
  classical
  let decodedMarker := innerMarker.flatMap outer.blocks
  let decodedBlock := innerBlock.flatMap outer.blocks
  let composedMarker := decodedMarker ++ marker
  have hdecodedBlockNonempty : decodedBlock ≠ [] := by
    intro hempty
    have hinjective := Symbolic.flatMap_returnWords_injective
      outer.blocks_injective outer.blocks_are_returns
    apply hreturn.2.1
    apply hinjective
    simpa [decodedBlock] using hempty
  have hcomposedMarkerNonempty : composedMarker ≠ [] :=
    List.append_ne_nil_of_right_ne_nil decodedMarker outer.marker_ne_nil
  obtain ⟨origin, horigin⟩ := hreturn.2.2.1
  have hfullAt : Symbolic.InfiniteFactorAt word
      (decodedBlock ++ composedMarker) (outer.cut origin) := by
    have hdecoded := outer.decoded_marker_at_cut origin
      (innerBlock ++ innerMarker).length
    rw [horigin] at hdecoded
    simpa [decodedBlock, decodedMarker, composedMarker,
      List.flatMap_append, List.append_assoc] using hdecoded
  have hcomposedPrefix : composedMarker <+:
      decodedBlock ++ composedMarker := by
    obtain ⟨tail, htail⟩ := hreturn.2.2.2.1
    have hmarkerTail : marker <+: tail.flatMap outer.blocks ++ marker :=
      Symbolic.marker_prefix_flatMap_returnWords outer.blocks
        outer.blocks_are_returns tail
    have hlift : decodedMarker ++ marker <+:
        decodedMarker ++ (tail.flatMap outer.blocks ++ marker) :=
      (List.prefix_append_right_inj decodedMarker).mpr hmarkerTail
    have hdecodedEq := congrArg (fun letters =>
      letters.flatMap outer.blocks) htail
    have hdecodedEq' :
        decodedMarker ++ tail.flatMap outer.blocks =
          decodedBlock ++ decodedMarker := by
      simpa [decodedBlock, decodedMarker, List.flatMap_append] using hdecodedEq
    have hrightEq :
        decodedMarker ++ (tail.flatMap outer.blocks ++ marker) =
          decodedBlock ++ (decodedMarker ++ marker) := by
      rw [← List.append_assoc, hdecodedEq', List.append_assoc]
    rw [hrightEq] at hlift
    change composedMarker <+: decodedBlock ++ composedMarker at hlift
    exact hlift
  refine ⟨hcomposedMarkerNonempty, hdecodedBlockNonempty,
    ⟨outer.cut origin, hfullAt⟩, hcomposedPrefix, ?_⟩
  intro physicalOffset
  constructor
  · intro hfinite
    have hcomposedAt : Symbolic.InfiniteFactorAt word composedMarker
        (outer.cut origin + physicalOffset) :=
      hfullAt.of_finiteFactorAt hfinite
    have hmarkerPrefix : marker <+: composedMarker := by
      exact Symbolic.marker_prefix_flatMap_returnWords outer.blocks
        outer.blocks_are_returns innerMarker
    have hmarkerFinite : Symbolic.FiniteFactorAt composedMarker marker 0 := by
      refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
    have hmarkerAt : Symbolic.InfiniteFactorAt word marker
        (outer.cut origin + physicalOffset) := by
      simpa using hcomposedAt.of_finiteFactorAt hmarkerFinite
    obtain ⟨index, hcutIndex⟩ :=
      outer.marker_occurrence_eq_cut hmarkerAt
    have hphysicalOffsetLe : physicalOffset ≤ decodedBlock.length := by
      have hlength := hfinite.1
      change physicalOffset + composedMarker.length ≤
        (decodedBlock ++ composedMarker).length at hlength
      simp only [List.length_append] at hlength
      omega
    have hinnerBlockAt : Symbolic.InfiniteFactorAt outer.derived
        innerBlock origin := by
      have hprefix : innerBlock <+: innerBlock ++ innerMarker :=
        List.prefix_append _ _
      have hfinitePrefix : Symbolic.FiniteFactorAt
          (innerBlock ++ innerMarker) innerBlock 0 := by
        refine ⟨by simpa using hprefix.length_le, ?_⟩
        simpa using (List.prefix_iff_eq_take.mp hprefix).symm
      exact horigin.of_finiteFactorAt hfinitePrefix
    have hcutEnd : outer.cut (origin + innerBlock.length) =
        outer.cut origin + decodedBlock.length := by
      have hcut := outer.cut_add origin innerBlock.length
      rw [hinnerBlockAt] at hcut
      simpa [decodedBlock] using hcut
    have horiginLe : origin ≤ index := by
      by_contra hnot
      have hstrict := outer.cut_strictMono
        (by omega : index < origin)
      rw [hcutIndex] at hstrict
      omega
    have hindexLe : index ≤ origin + innerBlock.length := by
      by_contra hnot
      have hstrict := outer.cut_strictMono
        (by omega : origin + innerBlock.length < index)
      rw [hcutIndex, hcutEnd] at hstrict
      omega
    let derivedOffset := index - origin
    have hindexEq : origin + derivedOffset = index := by
      simp [derivedOffset, Nat.add_sub_of_le horiginLe]
    have hderivedOffsetLe : derivedOffset ≤ innerBlock.length := by
      omega
    have hcomposedAtCut : Symbolic.InfiniteFactorAt word
        (innerMarker.flatMap outer.blocks ++ marker) (outer.cut index) := by
      rw [hcutIndex]
      simpa [decodedMarker, composedMarker] using hcomposedAt
    have hinnerMarkerAt : Symbolic.InfiniteFactorAt outer.derived
        innerMarker index :=
      outer.derived_factor_of_decoded_marker_at_cut
        innerMarker index hcomposedAtCut
    have hinnerMarkerAtOffset : Symbolic.InfiniteFactorAt outer.derived
        innerMarker (origin + derivedOffset) := by
      rw [hindexEq]
      exact hinnerMarkerAt
    have hwithin : derivedOffset + innerMarker.length ≤
        (innerBlock ++ innerMarker).length := by
      simp only [List.length_append]
      omega
    have hinnerFinite : Symbolic.FiniteFactorAt
        (innerBlock ++ innerMarker) innerMarker derivedOffset :=
      Symbolic.finiteFactorAt_of_nested_infiniteFactorAt horigin
        hinnerMarkerAtOffset hwithin
    rcases (hreturn.2.2.2.2 derivedOffset).mp hinnerFinite with
      hzero | hend
    · left
      have hcutIndex' := hcutIndex
      rw [← hindexEq, hzero, Nat.add_zero] at hcutIndex'
      omega
    · right
      have hcutIndex' := hcutIndex
      rw [← hindexEq, hend] at hcutIndex'
      rw [hcutEnd] at hcutIndex'
      change physicalOffset = decodedBlock.length
      omega
  · rintro (rfl | rfl)
    · change Symbolic.FiniteFactorAt
        (decodedBlock ++ composedMarker) composedMarker 0
      refine ⟨by simpa using hcomposedPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hcomposedPrefix).symm
    · change Symbolic.FiniteFactorAt
        (decodedBlock ++ composedMarker) composedMarker decodedBlock.length
      simp [Symbolic.FiniteFactorAt]

/-- Compose a return decomposition of a word with a return decomposition of
its derived word.  The composed cuts are the outer cuts at the inner cuts,
and every composed block is obtained by the outer return-word decoder. -/
private def composeReturnDecompositions_b9
    {alphabet : Type*} {word : Symbolic.InfiniteWord alphabet}
    {outerMarker : Symbolic.Word alphabet} {outerRank : Nat}
    (outer : Symbolic.ReturnDecomposition word outerMarker outerRank)
    {innerMarker : Symbolic.Word (Fin outerRank)} {innerRank : Nat}
    (inner : Symbolic.ReturnDecomposition outer.derived
      innerMarker innerRank) :
    Symbolic.ReturnDecomposition word
      (innerMarker.flatMap outer.blocks ++ outerMarker) innerRank where
  rank_pos := inner.rank_pos
  marker_ne_nil :=
    List.append_ne_nil_of_right_ne_nil _ outer.marker_ne_nil
  marker_at_zero := by
    have hdecoded := outer.decoded_marker_at_cut 0 innerMarker.length
    have hinnerZero : outer.derived.take innerMarker.length = innerMarker := by
      simpa [Symbolic.InfiniteFactorAt] using inner.marker_at_zero
    rw [outer.cut_zero, Stream'.drop_zero, hinnerZero] at hdecoded
    exact hdecoded
  blocks := fun letter => (inner.blocks letter).flatMap outer.blocks
  blocks_injective := by
    intro left right heq
    apply inner.blocks_injective
    exact (Symbolic.flatMap_returnWords_injective
      outer.blocks_injective outer.blocks_are_returns) heq
  blocks_are_returns := fun letter =>
    decodedReturnWord_of_derivedReturnWord_b9 outer
      (inner.blocks_are_returns letter)
  derived := inner.derived
  cut := fun position => outer.cut (inner.cut position)
  cut_zero := by rw [inner.cut_zero, outer.cut_zero]
  cut_succ := by
    intro position
    have hinnerBlock := inner.block_at_cut position
    have hcut := outer.cut_add (inner.cut position)
      (inner.blocks (inner.derived position)).length
    rw [hinnerBlock] at hcut
    rw [inner.cut_succ]
    exact hcut
  block_at_cut := by
    intro position
    have hinnerBlock := inner.block_at_cut position
    have hdecode := outer.flatMap_drop_take_derived
      (inner.cut position) (inner.blocks (inner.derived position)).length
    rw [hinnerBlock] at hdecode
    exact hdecode.symm

/-- Transporting only the ambient infinite word leaves the return-block
enumeration unchanged.  The public transport API already exposes the
corresponding `derived` simp theorem; this is the projection needed by the
iterated decoder calculation. -/
private theorem castReturnDecompositionWord_blocks_b9
    {alphabet : Type*}
    {left right : Symbolic.InfiniteWord alphabet}
    {marker : Symbolic.Word alphabet} {rank : Nat}
    (hword : left = right)
    (decomposition : Symbolic.ReturnDecomposition left marker rank)
    (letter : Fin rank) :
    (Symbolic.Substitution.castReturnDecompositionWord
      hword decomposition).blocks letter = decomposition.blocks letter := by
  subst right
  rfl

/-- C3.1a: iterating a self-derived return decomposition gives the exact
`w_n` return tower and the decoder powers asserted in the paper. -/
theorem durand_proposition10_has_iteratedDecoderTower
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source) :
    Nonempty (DurandIteratedDecoderTower input) := by
  let marker : Nat → Symbolic.Word (Fin rank) := fun level =>
    Nat.rec input.marker (fun _ previous =>
      previous.flatMap input.decomposition.blocks ++ input.marker) level
  let decomposition : ∀ level : Nat,
      Symbolic.ReturnDecomposition word (marker level) rank := fun level =>
    Nat.rec (motive := fun level =>
        Symbolic.ReturnDecomposition word (marker level) rank)
      input.decomposition
      (fun _ previous =>
        composeReturnDecompositions_b9 input.decomposition
          (Symbolic.Substitution.castReturnDecompositionWord
            input.derived_eq.symm previous)) level
  refine ⟨{
    marker := marker
    decomposition := decomposition
    marker_zero := rfl
    marker_succ := ?_
    derived_eq := ?_
    blocks_eq := ?_ }⟩
  · intro level
    rfl
  · intro level
    induction level with
    | zero => exact input.derived_eq
    | succ level ih =>
        change
          (Symbolic.Substitution.castReturnDecompositionWord
            input.derived_eq.symm (decomposition level)).derived = word
        simpa using ih
  · intro level letter
    induction level with
    | zero =>
        simp [decomposition, returnDecoderSubstitution]
    | succ level ih =>
        have hstep : (decomposition (level + 1)).blocks letter =
            ((decomposition level).blocks letter).flatMap
              input.decomposition.blocks := by
          simp [decomposition, composeReturnDecompositions_b9,
            castReturnDecompositionWord_blocks_b9]
        rw [hstep]
        calc
          ((decomposition level).blocks letter).flatMap
                  input.decomposition.blocks =
              (returnDecoderSubstitution input.decomposition).mapWord
                ((decomposition level).blocks letter) := rfl
          _ = (returnDecoderSubstitution input.decomposition).mapWord
                (((returnDecoderSubstitution input.decomposition).power
                  (level + 1)) letter) := by rw [ih]
          _ = ((returnDecoderSubstitution input.decomposition).power
                ((level + 1) + 1)) letter := by
            simp only [Symbolic.Substitution.power_apply,
              Symbolic.Substitution.iterateLetter_succ]

/-- A source power factored at the greatest available positive decoder
power.  Maximality is deliberately part of the data: without it, the image
lengths of the auxiliary morphisms need not be uniformly bounded. -/
structure DurandMaximalFactorization
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source)
    (sourceExponent : Nat) where
  refinementExponent : Nat
  refinementExponent_pos : 0 < refinementExponent
  gamma : Symbolic.Substitution (Fin rank)
  theta_comp_gamma :
    ((returnDecoderSubstitution input.decomposition).power
        refinementExponent).comp gamma = source.power sourceExponent
  gamma_comp_theta :
    gamma.comp
        ((returnDecoderSubstitution input.decomposition).power
          refinementExponent) = source.power sourceExponent
  maximal : ¬ HasTwoSidedDecoderFactorization input sourceExponent
    (refinementExponent + 1)

/-- Extensionality for the nonerasing substitution structure. -/
private theorem substitution_ext_b9
    {alphabet : Type*} (left right : Symbolic.Substitution alphabet)
    (himages : ∀ letter, left letter = right letter) : left = right := by
  cases left with
  | mk leftImage leftNonempty =>
      cases right with
      | mk rightImage rightNonempty =>
          have himage : leftImage = rightImage := by
            funext letter
            exact himages letter
          subst rightImage
          rfl

/-- Finite-word substitution respects concatenating composition. -/
private theorem substitution_mapWord_comp_b9
    {alphabet : Type*} (outer inner : Symbolic.Substitution alphabet)
    (letters : Symbolic.Word alphabet) :
    (outer.comp inner).mapWord letters =
      outer.mapWord (inner.mapWord letters) := by
  induction letters with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-- Concatenating composition of substitutions is associative. -/
private theorem substitution_comp_assoc_b9
    {alphabet : Type*} (first second third : Symbolic.Substitution alphabet) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply substitution_ext_b9
  intro letter
  change (first.comp second).mapWord (third letter) =
    first.mapWord ((second.comp third) letter)
  rw [substitution_mapWord_comp_b9]
  rfl

private theorem substitution_comp_id_b9
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet) :
    substitution.comp Symbolic.Substitution.id = substitution := by
  apply substitution_ext_b9
  intro letter
  simp [Symbolic.Substitution.mapWord]

private theorem substitution_id_comp_b9
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet) :
    Symbolic.Substitution.id.comp substitution = substitution := by
  apply substitution_ext_b9
  intro letter
  change Symbolic.Substitution.id.mapWord (substitution letter) =
    substitution letter
  have hid : ∀ letters : Symbolic.Word alphabet,
      Symbolic.Substitution.id.mapWord letters = letters := by
    intro letters
    induction letters with
    | nil => rfl
    | cons head tail ih => simp [ih]
  exact hid (substitution letter)

/-- An injective finite-word decoder cancels from the left in the
substitution monoid. -/
private theorem substitution_comp_left_cancel_b9
    {alphabet : Type*} (decoder : Symbolic.Substitution alphabet)
    (hinjective : Function.Injective decoder.mapWord)
    {left right : Symbolic.Substitution alphabet}
    (heq : decoder.comp left = decoder.comp right) : left = right := by
  apply substitution_ext_b9
  intro letter
  apply hinjective
  have hletter := congrArg (fun substitution :
    Symbolic.Substitution alphabet => substitution letter) heq
  exact hletter

/-- Commuting substitutions have commuting arbitrary powers. -/
private theorem substitution_powers_commute_b9
    {alphabet : Type*} {left right : Symbolic.Substitution alphabet}
    (hcommute : left.comp right = right.comp left) :
    ∀ leftPower rightPower : Nat,
      (left.power leftPower).comp (right.power rightPower) =
        (right.power rightPower).comp (left.power leftPower) := by
  have hright : ∀ rightPower : Nat,
      left.comp (right.power rightPower) =
        (right.power rightPower).comp left := by
    intro rightPower
    induction rightPower with
    | zero =>
        rw [Symbolic.Substitution.power_zero,
          substitution_comp_id_b9, substitution_id_comp_b9]
    | succ rightPower ih =>
        rw [Symbolic.Substitution.power_succ]
        calc
          left.comp (right.comp (right.power rightPower)) =
              (left.comp right).comp (right.power rightPower) :=
            (substitution_comp_assoc_b9 _ _ _).symm
          _ = (right.comp left).comp (right.power rightPower) := by
            rw [hcommute]
          _ = right.comp (left.comp (right.power rightPower)) :=
            substitution_comp_assoc_b9 _ _ _
          _ = right.comp ((right.power rightPower).comp left) := by
            rw [ih]
          _ = (right.comp (right.power rightPower)).comp left :=
            (substitution_comp_assoc_b9 _ _ _).symm
  intro leftPower rightPower
  induction leftPower with
  | zero =>
      rw [Symbolic.Substitution.power_zero,
        substitution_id_comp_b9, substitution_comp_id_b9]
  | succ leftPower ih =>
      rw [Symbolic.Substitution.power_succ]
      calc
        (left.comp (left.power leftPower)).comp
              (right.power rightPower) =
            left.comp ((left.power leftPower).comp
              (right.power rightPower)) :=
          substitution_comp_assoc_b9 _ _ _
        _ = left.comp ((right.power rightPower).comp
              (left.power leftPower)) := by rw [ih]
        _ = (left.comp (right.power rightPower)).comp
              (left.power leftPower) :=
          (substitution_comp_assoc_b9 _ _ _).symm
        _ = ((right.power rightPower).comp left).comp
              (left.power leftPower) := by rw [hright]
        _ = (right.power rightPower).comp
              (left.comp (left.power leftPower)) :=
          substitution_comp_assoc_b9 _ _ _

/-- The source substitution commutes with its identified return decoder. -/
private theorem durand_source_commutes_decoder_b9
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source) :
    (returnDecoderSubstitution input.decomposition).comp source =
      source.comp (returnDecoderSubstitution input.decomposition) := by
  apply substitution_ext_b9
  intro letter
  have hdecode := input.induced.factor_decodes letter
  have himage := congrArg (fun substitution :
    Symbolic.Substitution (Fin rank) => substitution letter)
      input.induced_eq
  change input.induced.factor letter = source letter at himage
  rw [himage] at hdecode
  exact hdecode

/-- Iterating a substitution preserves finite-word prefixes. -/
private theorem substitution_iterateWord_prefix_b9
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet)
    {small large : Symbolic.Word alphabet} (hprefix : small <+: large) :
    ∀ level : Nat,
      substitution.iterateWord level small <+:
        substitution.iterateWord level large := by
  intro level
  induction level with
  | zero => exact hprefix
  | succ level ih =>
      exact Symbolic.Substitution.mapWord_prefix ih

/-- If every source-letter image begins at a return marker, the images have
a unique nonempty parsing by the corresponding return blocks. -/
private theorem exists_decoderFactorization_of_images_begin_marker_b9
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {marker : Symbolic.Word (Fin rank)}
    (decomposition : Symbolic.ReturnDecomposition word marker rank)
    (hderived : decomposition.derived = word)
    (source : Symbolic.Substitution (Fin rank))
    (hfixed : source.IsFixedPoint word)
    (hbegins : ∀ letter : Fin rank, marker <+: source letter) :
    ∃ gamma : Symbolic.Substitution (Fin rank),
      (returnDecoderSubstitution decomposition).comp gamma = source := by
  classical
  let sourceCut : Nat → Nat := fun position =>
    (source.mapWord (word.take position)).length
  have himageAt : ∀ position : Nat,
      Symbolic.InfiniteFactorAt word (source (word position))
        (sourceCut position) := by
    intro position
    have hraw :=
      Symbolic.Substitution.iterateWord_drop_take_at_fixed_positive hfixed
        (level := 1) (by omega) position 1
    simpa [sourceCut, Symbolic.Substitution.iterateWord,
      Stream'.take_succ, Stream'.get] using hraw
  have hmarkerAt : ∀ position : Nat,
      Symbolic.InfiniteFactorAt word marker (sourceCut position) := by
    intro position
    have hprefix := hbegins (word position)
    have hfinite : Symbolic.FiniteFactorAt
        (source (word position)) marker 0 := by
      refine ⟨by simpa using hprefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hprefix).symm
    exact (himageAt position).of_finiteFactorAt hfinite
  let boundary : Nat → Nat := fun position =>
    Classical.choose
      (decomposition.marker_occurrence_eq_cut (hmarkerAt position))
  have hboundaryCut : ∀ position : Nat,
      decomposition.cut (boundary position) = sourceCut position := by
    intro position
    exact Classical.choose_spec
      (decomposition.marker_occurrence_eq_cut (hmarkerAt position))
  have hsourceCutSucc : ∀ position : Nat,
      sourceCut (position + 1) = sourceCut position +
        (source (word position)).length := by
    intro position
    change (source.mapWord (word.take (position + 1))).length =
      (source.mapWord (word.take position)).length +
        (source (word position)).length
    rw [Stream'.take_succ', Symbolic.Substitution.mapWord_append,
      List.length_append]
    simp [Stream'.get]
  have hsourceCutStrict : StrictMono sourceCut := by
    apply strictMono_nat_of_lt_succ
    intro position
    rw [hsourceCutSucc]
    exact Nat.lt_add_of_pos_right
      (List.length_pos_of_ne_nil (source.image_ne_nil (word position)))
  have hboundaryStrict : StrictMono boundary := by
    intro left right hlr
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hboundaryCut, hboundaryCut]
    exact hsourceCutStrict hlr
  let factorAt : Nat → Symbolic.Word (Fin rank) := fun position =>
    (decomposition.derived.drop (boundary position)).take
      (boundary (position + 1) - boundary position)
  have hfactorAtDecodes : ∀ position : Nat,
      (factorAt position).flatMap decomposition.blocks =
        source (word position) := by
    intro position
    have hboundaryLe : boundary position ≤ boundary (position + 1) :=
      (hboundaryStrict (Nat.lt_succ_self position)).le
    have hdecode := decomposition.flatMap_drop_take_derived
      (boundary position) (boundary (position + 1) - boundary position)
    change (factorAt position).flatMap decomposition.blocks =
      (word.drop (decomposition.cut (boundary position))).take
        ((factorAt position).flatMap decomposition.blocks).length at hdecode
    have hcutAdd := decomposition.cut_add (boundary position)
      (boundary (position + 1) - boundary position)
    have hboundaryAdd : boundary position +
        (boundary (position + 1) - boundary position) =
          boundary (position + 1) := Nat.add_sub_of_le hboundaryLe
    rw [hboundaryAdd] at hcutAdd
    change decomposition.cut (boundary (position + 1)) =
      decomposition.cut (boundary position) +
        ((factorAt position).flatMap decomposition.blocks).length at hcutAdd
    have hlength : ((factorAt position).flatMap
        decomposition.blocks).length = (source (word position)).length := by
      rw [hboundaryCut, hboundaryCut, hsourceCutSucc] at hcutAdd
      omega
    rw [hboundaryCut, hlength] at hdecode
    exact hdecode.trans (himageAt position)
  let occurrence : Fin rank → Nat := fun letter =>
    Classical.choose (decomposition.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin rank,
      word (occurrence letter) = letter := by
    intro letter
    have hletter := Classical.choose_spec
      (decomposition.every_letter_occurs letter)
    change decomposition.derived (occurrence letter) = letter at hletter
    exact (congrFun hderived (occurrence letter)).symm.trans hletter
  let factor : Fin rank → Symbolic.Word (Fin rank) := fun letter =>
    factorAt (occurrence letter)
  have hfactorDecodes : ∀ letter : Fin rank,
      (factor letter).flatMap decomposition.blocks = source letter := by
    intro letter
    change (factorAt (occurrence letter)).flatMap decomposition.blocks = _
    rw [hfactorAtDecodes, hoccurrence]
  have hfactorNonempty : ∀ letter : Fin rank, factor letter ≠ [] := by
    intro letter hempty
    have hdecode := hfactorDecodes letter
    rw [hempty] at hdecode
    simp only [List.flatMap_nil] at hdecode
    exact source.image_ne_nil letter hdecode.symm
  let gamma : Symbolic.Substitution (Fin rank) := {
    image := factor
    image_ne_nil := hfactorNonempty }
  refine ⟨gamma, ?_⟩
  apply substitution_ext_b9
  intro letter
  exact hfactorDecodes letter

/-- Every admissible decoder exponent is bounded by one fixed source-image
length.  Decoder positivity and the all-letter condition force a level-`n`
seed image inside every level-`n+1` decoder letter image. -/
private theorem durand_factorization_refinement_le_sourceLength_b9
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source)
    (sourceExponent refinementExponent : Nat)
    (hfactor : HasTwoSidedDecoderFactorization input
      sourceExponent refinementExponent) :
    refinementExponent ≤
      ((source.power sourceExponent) input.seed).length := by
  rcases hfactor with ⟨gamma, hleft, _hright⟩
  cases refinementExponent with
  | zero => omega
  | succ level =>
      let theta := returnDecoderSubstitution input.decomposition
      obtain ⟨firstLetter, tail, hgamma⟩ :=
        List.exists_cons_of_ne_nil (gamma.image_ne_nil input.seed)
      have hseedMem : input.seed ∈ theta.iterateLetter 1 firstLetter := by
        simpa [theta, Symbolic.Substitution.iterateLetter,
          Symbolic.Substitution.iterateWord, returnDecoderSubstitution] using
            input.decoder_contains_all firstLetter input.seed
      have hinfix := theta.iterateLetter_infix_of_mem_iterate
        (later := level) hseedMem
      have hseedLength : level + 1 ≤
          (theta.iterateLetter level input.seed).length :=
        theta.succ_le_iterateLetter_length input.decoder_prolongable level
      have hletterLength : level + 1 ≤
          (theta.iterateLetter (level + 1) firstLetter).length :=
        hseedLength.trans hinfix.length_le
      have himageLength :
          (theta.iterateLetter (level + 1) firstLetter).length ≤
            ((theta.power (level + 1)).mapWord
              (gamma input.seed)).length := by
        rw [hgamma, Symbolic.Substitution.mapWord_cons,
          List.length_append, Symbolic.Substitution.power_apply]
        omega
      have hleftSeed := congrArg (fun substitution :
        Symbolic.Substitution (Fin rank) => substitution input.seed) hleft
      change (theta.power (level + 1)).mapWord (gamma input.seed) =
        (source.power sourceExponent) input.seed at hleftSeed
      rw [← hleftSeed]
      exact hletterLength.trans himageLength

/-- C3.1b: arbitrarily far out in both exponent variables there is a source
power with a maximal positive two-sided decoder factorization.  This is the
cofinal maximal-prefix selection in Proposition 10. -/
theorem durand_proposition10_has_cofinalMaximalFactorizations
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source)
    (tower : DurandIteratedDecoderTower input)
    (sourceFloor refinementFloor : Nat) :
    ∃ sourceExponent : Nat, sourceFloor < sourceExponent ∧
      ∃ factorization : DurandMaximalFactorization input sourceExponent,
        refinementFloor < factorization.refinementExponent := by
  classical
  let level := refinementFloor
  let decomposition := tower.decomposition level
  let theta := returnDecoderSubstitution input.decomposition
  let refinementExponent := level + 1
  let sourceDepth := sourceFloor + (tower.marker level).length
  let sourceExponent := sourceDepth + 1
  let poweredSource := source.power sourceExponent
  have hsourceExponent : sourceFloor < sourceExponent := by
    simp [sourceExponent, sourceDepth]
  have hmarkerAtZero : word.take (tower.marker level).length =
      tower.marker level := by
    simpa [Symbolic.InfiniteFactorAt, decomposition] using
      (tower.decomposition level).marker_at_zero
  have hseedPrefix : tower.marker level <+:
      source.iterateLetter sourceDepth input.seed := by
    have hsourcePrefix :=
      Symbolic.Substitution.iterateLetter_eq_take_of_fixedPoint
        input.source_fixed input.seed_is_head.symm sourceDepth
    have hlength : (tower.marker level).length ≤
        (source.iterateLetter sourceDepth input.seed).length := by
      have hgrowth := source.succ_le_iterateLetter_length
        input.source_prolongable sourceDepth
      simp [sourceDepth] at hgrowth ⊢
      omega
    have htakes := Stream'.take_prefix_take_left
      (a := word) (m := (tower.marker level).length)
      (n := (source.iterateLetter sourceDepth input.seed).length) hlength
    rw [hmarkerAtZero, ← hsourcePrefix] at htakes
    exact htakes
  have hbegins : ∀ letter : Fin rank,
      tower.marker level <+: poweredSource letter := by
    intro letter
    have himagePrefix := substitution_iterateWord_prefix_b9 source
      (input.images_begin_seed letter) sourceDepth
    change source.iterateLetter sourceDepth input.seed <+:
      source.iterateWord sourceDepth (source letter) at himagePrefix
    have hright : source.iterateWord sourceDepth (source letter) =
        poweredSource letter := by
      calc
        source.iterateWord sourceDepth (source letter) =
            source.iterateWord sourceDepth
              (source.iterateWord 1 [letter]) := by
          simp [Symbolic.Substitution.iterateWord]
        _ = source.iterateWord (sourceDepth + 1) [letter] :=
          (source.iterateWord_add_public sourceDepth 1 [letter]).symm
        _ = poweredSource letter := by
          simp [poweredSource, sourceExponent,
            Symbolic.Substitution.power_apply,
            Symbolic.Substitution.iterateLetter]
    rw [hright] at himagePrefix
    exact hseedPrefix.trans himagePrefix
  have hsourceExponentPos : 0 < sourceExponent := by
    omega
  have hpoweredFixed : poweredSource.IsFixedPoint word :=
    Symbolic.Substitution.isFixedPoint_power input.source_fixed
      hsourceExponentPos
  obtain ⟨gamma, hdecoderGamma⟩ :=
    exists_decoderFactorization_of_images_begin_marker_b9 decomposition
      (tower.derived_eq level) poweredSource hpoweredFixed hbegins
  have hdecoderEq : returnDecoderSubstitution decomposition =
      theta.power refinementExponent := by
    apply substitution_ext_b9
    intro letter
    change (tower.decomposition level).blocks letter =
      ((returnDecoderSubstitution input.decomposition).power
        (level + 1)) letter
    exact tower.blocks_eq level letter
  have hthetaGamma : (theta.power refinementExponent).comp gamma =
      poweredSource := by
    rw [← hdecoderEq]
    exact hdecoderGamma
  have hthetaInjective : Function.Injective
      (theta.power refinementExponent).mapWord := by
    rw [← hdecoderEq]
    exact Symbolic.flatMap_returnWords_injective
      decomposition.blocks_injective decomposition.blocks_are_returns
  have hpowerCommute : (theta.power refinementExponent).comp poweredSource =
      poweredSource.comp (theta.power refinementExponent) := by
    exact substitution_powers_commute_b9
      (durand_source_commutes_decoder_b9 input)
      refinementExponent sourceExponent
  have hgammaTheta : gamma.comp (theta.power refinementExponent) =
      poweredSource := by
    apply substitution_comp_left_cancel_b9
      (theta.power refinementExponent) hthetaInjective
    calc
      (theta.power refinementExponent).comp
            (gamma.comp (theta.power refinementExponent)) =
          ((theta.power refinementExponent).comp gamma).comp
            (theta.power refinementExponent) :=
        (substitution_comp_assoc_b9 _ _ _).symm
      _ = poweredSource.comp (theta.power refinementExponent) := by
        rw [hthetaGamma]
      _ = (theta.power refinementExponent).comp poweredSource :=
        hpowerCommute.symm
  have hinitial : HasTwoSidedDecoderFactorization input sourceExponent
      refinementExponent := by
    refine ⟨gamma, ?_, ?_⟩
    · simpa [theta, poweredSource] using hthetaGamma
    · simpa [theta, poweredSource] using hgammaTheta
  let bound := (poweredSource input.seed).length
  have hinitialBound : refinementExponent ≤ bound := by
    exact durand_factorization_refinement_le_sourceLength_b9 input
      sourceExponent refinementExponent hinitial
  let admissible : Nat → Prop := fun exponent =>
    HasTwoSidedDecoderFactorization input sourceExponent exponent
  let maximalExponent := Nat.findGreatest admissible bound
  have hmaximalAdmissible : admissible maximalExponent := by
    exact Nat.findGreatest_spec hinitialBound hinitial
  have hinitialLeMaximal : refinementExponent ≤ maximalExponent := by
    exact Nat.le_findGreatest hinitialBound hinitial
  have hfloorMaximal : refinementFloor < maximalExponent := by
    simp [refinementExponent, level] at hinitialLeMaximal
    omega
  have hmaximal : ¬ HasTwoSidedDecoderFactorization input sourceExponent
      (maximalExponent + 1) := by
    intro hsuccessor
    have hsuccessorBound : maximalExponent + 1 ≤ bound :=
      durand_factorization_refinement_le_sourceLength_b9 input
        sourceExponent (maximalExponent + 1) hsuccessor
    have hsuccessorLe := Nat.le_findGreatest
      (P := admissible) hsuccessorBound hsuccessor
    omega
  rcases hmaximalAdmissible with ⟨maximalGamma,
    hmaximalLeft, hmaximalRight⟩
  refine ⟨sourceExponent, hsourceExponent, ?_⟩
  refine ⟨{
    refinementExponent := maximalExponent
    refinementExponent_pos := Nat.zero_lt_of_lt hfloorMaximal
    gamma := maximalGamma
    theta_comp_gamma := hmaximalLeft
    gamma_comp_theta := hmaximalRight
    maximal := hmaximal }, hfloorMaximal⟩

/-- C3.1: the preliminary Proposition-10 construction before the auxiliary
morphisms `gamma_k` have been made constant.  The two exact same-source word
equations are recorded at every index. -/
structure DurandGammaSequence
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source) where
  sourcePower : Nat → Nat
  sourcePower_strictMono : StrictMono sourcePower
  sourcePower_zero_pos : 0 < sourcePower 0
  refinementPower : Nat → Nat
  refinementPower_strictMono : StrictMono refinementPower
  refinementPower_zero_pos : 0 < refinementPower 0
  gammaAt : Nat → Symbolic.Substitution (Fin rank)
  gammaAt_nonempty : ∀ index letter, gammaAt index letter ≠ []
  theta_comp_gammaAt : ∀ index,
    ((returnDecoderSubstitution input.decomposition).power
          (refinementPower index)).comp (gammaAt index) =
      source.power (sourcePower index)
  gammaAt_comp_theta : ∀ index,
    (gammaAt index).comp
        ((returnDecoderSubstitution input.decomposition).power
          (refinementPower index)) =
      source.power (sourcePower index)
  refinementPower_maximal : ∀ index,
    ¬ HasTwoSidedDecoderFactorization input (sourcePower index)
      (refinementPower index + 1)

/-- Leaf C3.1: construct `gamma_k` by cutting a sufficiently long source
iterate at the maximal complete `Theta`-decoder prefix. -/
theorem durand_proposition10_constructGammaSequence
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source) :
    Nonempty (DurandGammaSequence input) := by
  classical
  obtain ⟨tower⟩ := durand_proposition10_has_iteratedDecoderTower input
  have hexists (sourceFloor refinementFloor : Nat) :
      ∃ sourceExponent : Nat, sourceFloor < sourceExponent ∧
        ∃ factorization : DurandMaximalFactorization input sourceExponent,
          refinementFloor < factorization.refinementExponent :=
    durand_proposition10_has_cofinalMaximalFactorizations input tower
      sourceFloor refinementFloor
  let selectedSource (sourceFloor refinementFloor : Nat) : Nat :=
    Classical.choose (hexists sourceFloor refinementFloor)
  let selectedFactor (sourceFloor refinementFloor : Nat) :
      DurandMaximalFactorization input
        (selectedSource sourceFloor refinementFloor) :=
    Classical.choose
      (Classical.choose_spec (hexists sourceFloor refinementFloor)).2
  have hselectedSource : ∀ sourceFloor refinementFloor : Nat,
      sourceFloor < selectedSource sourceFloor refinementFloor := by
    intro sourceFloor refinementFloor
    exact (Classical.choose_spec (hexists sourceFloor refinementFloor)).1
  have hselectedFactor : ∀ sourceFloor refinementFloor : Nat,
      refinementFloor <
        (selectedFactor sourceFloor refinementFloor).refinementExponent := by
    intro sourceFloor refinementFloor
    exact Classical.choose_spec
      (Classical.choose_spec (hexists sourceFloor refinementFloor)).2
  let Stage := Σ sourceExponent : Nat,
    DurandMaximalFactorization input sourceExponent
  let first : Stage :=
    ⟨selectedSource 0 0, selectedFactor 0 0⟩
  let next : Stage → Stage := fun previous =>
    ⟨selectedSource previous.1 previous.2.refinementExponent,
      selectedFactor previous.1 previous.2.refinementExponent⟩
  let stage : Nat → Stage := fun index =>
    Nat.rec first (fun _ previous => next previous) index
  have hsourceStep : ∀ index : Nat,
      (stage index).1 < (stage (index + 1)).1 := by
    intro index
    change (stage index).1 <
      selectedSource (stage index).1
        (stage index).2.refinementExponent
    exact hselectedSource _ _
  have hrefinementStep : ∀ index : Nat,
      (stage index).2.refinementExponent <
        (stage (index + 1)).2.refinementExponent := by
    intro index
    change (stage index).2.refinementExponent <
      (selectedFactor (stage index).1
        (stage index).2.refinementExponent).refinementExponent
    exact hselectedFactor _ _
  refine ⟨{
    sourcePower := fun index => (stage index).1
    sourcePower_strictMono := strictMono_nat_of_lt_succ hsourceStep
    sourcePower_zero_pos := by
      change 0 < selectedSource 0 0
      exact hselectedSource 0 0
    refinementPower := fun index =>
      (stage index).2.refinementExponent
    refinementPower_strictMono :=
      strictMono_nat_of_lt_succ hrefinementStep
    refinementPower_zero_pos := by
      change 0 < (selectedFactor 0 0).refinementExponent
      exact hselectedFactor 0 0
    gammaAt := fun index => (stage index).2.gamma
    gammaAt_nonempty := fun index letter =>
      (stage index).2.gamma.image_ne_nil letter
    theta_comp_gammaAt := fun index =>
      (stage index).2.theta_comp_gamma
    gammaAt_comp_theta := fun index =>
      (stage index).2.gamma_comp_theta
    refinementPower_maximal := fun index =>
      (stage index).2.maximal }⟩

/-!
Formalization note.  The maximality field above is essential and was absent
from the first skeleton.  For example, in the standard Fibonacci return-word
configuration one has, up to the chosen return-letter labels, `Theta = tau^2`.
The algebraic choices `p_i = 3(i+1)`, `l_i = i+1`, and
`gamma_i = tau^(i+1)` satisfy both old word equations and both strict-growth
conditions, while the `gamma_i` image lengths are unbounded.  Durand instead
chooses `l_i` maximally; the manuscript should state that provenance before
invoking the uniform-bound estimate.
-/

/-- The paper-level length comparison extracted from maximality.  A chosen
letter realizes the shortest decoder image at each stage, and every source
image is at most a fixed multiple of that shortest image.  This is the exact
ratio estimate needed to bound the number of decoder blocks in `gamma_k`. -/
structure DurandGammaLengthRatioControl
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    (sequence : DurandGammaSequence input) where
  ratioBound : Nat
  ratioBound_pos : 0 < ratioBound
  minimumLetter : Nat → Fin rank
  minimumLetter_is_minimum : ∀ index letter,
    (((returnDecoderSubstitution input.decomposition).power
        (sequence.refinementPower index)) (minimumLetter index)).length ≤
      (((returnDecoderSubstitution input.decomposition).power
        (sequence.refinementPower index)) letter).length
  source_image_length_le : ∀ index letter,
    ((source.power (sequence.sourcePower index)) letter).length ≤
      ratioBound *
        (((returnDecoderSubstitution input.decomposition).power
          (sequence.refinementPower index))
            (minimumLetter index)).length

/-- If all images of a powered source begin with one marker in the exact
return tower, that source power factors on both sides through the
corresponding decoder power.  This is the local implication contradicted by
the maximality field of `DurandGammaSequence`. -/
private theorem durand_has_factorization_of_towerMarker_begins_b9
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source)
    (tower : DurandIteratedDecoderTower input)
    (sourceExponent level : Nat)
    (hsourceExponentPos : 0 < sourceExponent)
    (hbegins : ∀ letter : Fin rank,
      tower.marker level <+: (source.power sourceExponent) letter) :
    HasTwoSidedDecoderFactorization input sourceExponent (level + 1) := by
  classical
  let decomposition := tower.decomposition level
  let theta := returnDecoderSubstitution input.decomposition
  let poweredSource := source.power sourceExponent
  have hpoweredFixed : poweredSource.IsFixedPoint word :=
    Symbolic.Substitution.isFixedPoint_power input.source_fixed
      hsourceExponentPos
  obtain ⟨gamma, hdecoderGamma⟩ :=
    exists_decoderFactorization_of_images_begin_marker_b9 decomposition
      (tower.derived_eq level) poweredSource hpoweredFixed hbegins
  have hdecoderEq : returnDecoderSubstitution decomposition =
      theta.power (level + 1) := by
    apply substitution_ext_b9
    intro letter
    change (tower.decomposition level).blocks letter =
      ((returnDecoderSubstitution input.decomposition).power
        (level + 1)) letter
    exact tower.blocks_eq level letter
  have hthetaGamma : (theta.power (level + 1)).comp gamma =
      poweredSource := by
    rw [← hdecoderEq]
    exact hdecoderGamma
  have hthetaInjective : Function.Injective
      (theta.power (level + 1)).mapWord := by
    rw [← hdecoderEq]
    exact Symbolic.flatMap_returnWords_injective
      decomposition.blocks_injective decomposition.blocks_are_returns
  have hpowerCommute : (theta.power (level + 1)).comp poweredSource =
      poweredSource.comp (theta.power (level + 1)) := by
    exact substitution_powers_commute_b9
      (durand_source_commutes_decoder_b9 input)
      (level + 1) sourceExponent
  have hgammaTheta : gamma.comp (theta.power (level + 1)) =
      poweredSource := by
    apply substitution_comp_left_cancel_b9
      (theta.power (level + 1)) hthetaInjective
    calc
      (theta.power (level + 1)).comp
            (gamma.comp (theta.power (level + 1))) =
          ((theta.power (level + 1)).comp gamma).comp
            (theta.power (level + 1)) :=
        (substitution_comp_assoc_b9 _ _ _).symm
      _ = poweredSource.comp (theta.power (level + 1)) := by
        rw [hthetaGamma]
      _ = (theta.power (level + 1)).comp poweredSource :=
        hpowerCommute.symm
  refine ⟨gamma, ?_, ?_⟩
  · simpa [theta, poweredSource] using hthetaGamma
  · simpa [theta, poweredSource] using hgammaTheta

/-- The preceding seed iterate is a prefix of every image of a positive
source power, because every one-step source image begins in the seed. -/
private theorem durand_previousSeed_prefix_sourcePower_b9
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source)
    (sourceExponent : Nat) (hsourceExponentPos : 0 < sourceExponent)
    (letter : Fin rank) :
    source.iterateLetter (sourceExponent - 1) input.seed <+:
      (source.power sourceExponent) letter := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hsourceExponentPos)
  have himagePrefix := substitution_iterateWord_prefix_b9 source
    (input.images_begin_seed letter) depth
  change source.iterateLetter depth input.seed <+:
    source.iterateWord depth (source letter) at himagePrefix
  have hright : source.iterateWord depth (source letter) =
      (source.power (depth + 1)) letter := by
    calc
      source.iterateWord depth (source letter) =
          source.iterateWord depth
            (source.iterateWord 1 [letter]) := by
        simp [Symbolic.Substitution.iterateWord]
      _ = source.iterateWord (depth + 1) [letter] :=
        (source.iterateWord_add_public depth 1 [letter]).symm
      _ = (source.power (depth + 1)) letter := by
        simp [Symbolic.Substitution.power_apply,
          Symbolic.Substitution.iterateLetter]
  simpa [hright] using himagePrefix

/-- If every letter image has length at least two, substitution doubles the
length of every finite word. -/
private theorem substitution_two_mul_length_le_mapWord_b9
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet)
    (himage : ∀ letter, 2 ≤ (substitution letter).length)
    (finiteWord : Symbolic.Word alphabet) :
    2 * finiteWord.length ≤ (substitution.mapWord finiteWord).length := by
  induction finiteWord with
  | nil => simp
  | cons letter tail ih =>
      rw [Symbolic.Substitution.mapWord_cons, List.length_append,
        List.length_cons]
      have hletter := himage letter
      omega

/-- The explicit word `Theta^n(u) ... Theta(u)u` occurring as the level-`n`
marker in the iterated decoder tower. -/
private def expandedTowerMarker_b9
    {alphabet : Type*} (theta : Symbolic.Substitution alphabet)
    (marker : Symbolic.Word alphabet) : Nat → Symbolic.Word alphabet
  | 0 => marker
  | level + 1 =>
      theta.iterateWord (level + 1) marker ++
        expandedTowerMarker_b9 theta marker level

private theorem mapWord_expandedTowerMarker_append_b9
    {alphabet : Type*} (theta : Symbolic.Substitution alphabet)
    (marker : Symbolic.Word alphabet) (level : Nat) :
    theta.mapWord (expandedTowerMarker_b9 theta marker level) ++ marker =
      expandedTowerMarker_b9 theta marker (level + 1) := by
  induction level with
  | zero => simp [expandedTowerMarker_b9]
  | succ level ih =>
      simp only [expandedTowerMarker_b9,
        Symbolic.Substitution.mapWord_append, List.append_assoc]
      rw [ih]
      rfl

private theorem tower_marker_eq_expanded_b9
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source)
    (tower : DurandIteratedDecoderTower input) (level : Nat) :
    tower.marker level = expandedTowerMarker_b9
      (returnDecoderSubstitution input.decomposition) input.marker level := by
  induction level with
  | zero => simpa [expandedTowerMarker_b9] using tower.marker_zero
  | succ level ih =>
      rw [tower.marker_succ level, ih,
        mapWord_expandedTowerMarker_append_b9]

private theorem expandedTowerMarker_length_le_b9
    {alphabet : Type*} (theta : Symbolic.Substitution alphabet)
    (marker : Symbolic.Word alphabet)
    (himage : ∀ letter, 2 ≤ (theta letter).length)
    (level : Nat) :
    (expandedTowerMarker_b9 theta marker level).length ≤
      2 * (theta.iterateWord level marker).length := by
  induction level with
  | zero =>
      simp only [expandedTowerMarker_b9,
        Symbolic.Substitution.iterateWord_zero]
      exact Nat.le_mul_of_pos_left marker.length (by omega)
  | succ level ih =>
      rw [expandedTowerMarker_b9, List.length_append]
      have hdouble := substitution_two_mul_length_le_mapWord_b9 theta
        himage (theta.iterateWord level marker)
      have hstep : 2 * (theta.iterateWord level marker).length ≤
          (theta.iterateWord (level + 1) marker).length := by
        simpa only [Symbolic.Substitution.iterateWord_succ] using hdouble
      calc
        (theta.iterateWord (level + 1) marker).length +
              (expandedTowerMarker_b9 theta marker level).length ≤
            (theta.iterateWord (level + 1) marker).length +
              2 * (theta.iterateWord level marker).length :=
          Nat.add_le_add_left ih _
        _ ≤ (theta.iterateWord (level + 1) marker).length +
              (theta.iterateWord (level + 1) marker).length :=
          Nat.add_le_add_left hstep _
        _ = 2 * (theta.iterateWord (level + 1) marker).length := by
          omega

/-- C3.2a: maximal decoder exponents give the uniform source/decoder length
ratio used in Durand's return-word estimate. -/
theorem durand_maximalGammaSequence_has_lengthRatioControl
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    (sequence : DurandGammaSequence input) :
    Nonempty (DurandGammaLengthRatioControl sequence) := by
  classical
  letI : Nonempty (Fin rank) := ⟨⟨0, input.rank_pos⟩⟩
  let theta := returnDecoderSubstitution input.decomposition
  obtain ⟨tower⟩ := durand_proposition10_has_iteratedDecoderTower input
  obtain ⟨primitiveDepth, _hprimitiveDepth, hsourceContains⟩ :=
    input.source_primitive
  have hrankTwo : 2 ≤ rank := by
    by_contra hnot
    have hrankLe : rank ≤ 1 := by omega
    apply input.word_aperiodic
    refine ⟨1, by omega, ?_⟩
    intro position
    apply Fin.ext
    have hleft := (word (position + 1)).isLt
    have hright := (word position).isLt
    omega
  have hthetaImageTwo : ∀ letter : Fin rank,
      2 ≤ (theta letter).length := by
    intro letter
    let zeroLetter : Fin rank := ⟨0, input.rank_pos⟩
    let oneLetter : Fin rank := ⟨1, hrankTwo⟩
    have hzeroMem : zeroLetter ∈ theta letter := by
      simpa [theta, returnDecoderSubstitution] using
        input.decoder_contains_all letter zeroLetter
    have honeMem : oneLetter ∈ theta letter := by
      simpa [theta, returnDecoderSubstitution] using
        input.decoder_contains_all letter oneLetter
    have hne : zeroLetter ≠ oneLetter := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [zeroLetter, oneLetter] at hval
    have hsubset : ({zeroLetter, oneLetter} : Finset (Fin rank)) ⊆
        (theta letter).toFinset := by
      intro candidate hcandidate
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcandidate
      simp only [List.mem_toFinset]
      rcases hcandidate with rfl | rfl
      · exact hzeroMem
      · exact honeMem
    have hcard := Finset.card_le_card hsubset
    have hfinsetLength := List.toFinset_card_le (theta letter)
    have hpairCard : ({zeroLetter, oneLetter} : Finset (Fin rank)).card = 2 := by
      simp [hne]
    omega
  let minimumLetter : Nat → Fin rank := fun index =>
    Classical.choose (Finset.exists_min_image Finset.univ
      (fun letter : Fin rank =>
        ((theta.power (sequence.refinementPower index)) letter).length)
      Finset.univ_nonempty)
  have hminimum : ∀ index letter,
      ((theta.power (sequence.refinementPower index))
          (minimumLetter index)).length ≤
        ((theta.power (sequence.refinementPower index)) letter).length := by
    intro index letter
    exact (Classical.choose_spec
      (Finset.exists_min_image Finset.univ
        (fun candidate : Fin rank =>
          ((theta.power (sequence.refinementPower index)) candidate).length)
        Finset.univ_nonempty)).2 letter (Finset.mem_univ letter)
  let sourceConstant :=
    source.maxIterateLength primitiveDepth * source.maxIterateLength 1
  let markerConstant :=
    2 * theta.maxIterateLength 1 * input.marker.length
  let ratioBound := sourceConstant * markerConstant
  have hsourceMaxPos : ∀ level : Nat,
      0 < source.maxIterateLength level := by
    intro level
    exact (List.length_pos_of_ne_nil
      (source.iterateLetter_ne_nil level input.seed)).trans_le
        (source.iterateLetter_length_le_maxIterateLength level input.seed)
  have hthetaMaxPos : ∀ level : Nat,
      0 < theta.maxIterateLength level := by
    intro level
    exact (List.length_pos_of_ne_nil
      (theta.iterateLetter_ne_nil level input.seed)).trans_le
        (theta.iterateLetter_length_le_maxIterateLength level input.seed)
  have hmarkerPos : 0 < input.marker.length :=
    List.length_pos_of_ne_nil input.decomposition.marker_ne_nil
  have hratioBoundPos : 0 < ratioBound := by
    dsimp [ratioBound, sourceConstant, markerConstant]
    exact Nat.mul_pos
      (Nat.mul_pos (hsourceMaxPos primitiveDepth) (hsourceMaxPos 1))
      (Nat.mul_pos (Nat.mul_pos (by omega) (hthetaMaxPos 1)) hmarkerPos)
  refine ⟨{
    ratioBound := ratioBound
    ratioBound_pos := hratioBoundPos
    minimumLetter := minimumLetter
    minimumLetter_is_minimum := ?_
    source_image_length_le := ?_ }⟩
  · intro index letter
    simpa [theta] using hminimum index letter
  · intro index letter
    let sourceExponent := sequence.sourcePower index
    let refinementExponent := sequence.refinementPower index
    have hsourceExponentPos : 0 < sourceExponent := by
      have hmono := sequence.sourcePower_strictMono.monotone
        (Nat.zero_le index)
      exact lt_of_lt_of_le sequence.sourcePower_zero_pos hmono
    have hrefinementExponentPos : 0 < refinementExponent := by
      have hmono := sequence.refinementPower_strictMono.monotone
        (Nat.zero_le index)
      dsimp [refinementExponent]
      exact lt_of_lt_of_le sequence.refinementPower_zero_pos hmono
    have hpreviousSeedLtMarker :
        (source.iterateLetter (sourceExponent - 1) input.seed).length <
          (tower.marker refinementExponent).length := by
      by_contra hnot
      have hmarkerLe : (tower.marker refinementExponent).length ≤
          (source.iterateLetter (sourceExponent - 1) input.seed).length := by
        omega
      have hmarkerAtZero :
          word.take (tower.marker refinementExponent).length =
            tower.marker refinementExponent := by
        simpa [Symbolic.InfiniteFactorAt] using
          (tower.decomposition refinementExponent).marker_at_zero
      have hsourcePrefix :=
        Symbolic.Substitution.iterateLetter_eq_take_of_fixedPoint
          input.source_fixed input.seed_is_head.symm
          (sourceExponent - 1)
      have htakes := Stream'.take_prefix_take_left
        (a := word) (m := (tower.marker refinementExponent).length)
        (n := (source.iterateLetter
          (sourceExponent - 1) input.seed).length) hmarkerLe
      rw [hmarkerAtZero, ← hsourcePrefix] at htakes
      have hbegins : ∀ candidate : Fin rank,
          tower.marker refinementExponent <+:
            (source.power sourceExponent) candidate := by
        intro candidate
        exact htakes.trans
          (durand_previousSeed_prefix_sourcePower_b9 input
            sourceExponent hsourceExponentPos candidate)
      exact sequence.refinementPower_maximal index
        (durand_has_factorization_of_towerMarker_begins_b9 input tower
          sourceExponent refinementExponent hsourceExponentPos hbegins)
    obtain ⟨sourceDepth, hsourceExponentEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsourceExponentPos)
    obtain ⟨maxSourceLetter, hmaxSourceLetter⟩ :=
      source.exists_length_eq_maxIterateLength sourceDepth
    have hmaxSourceInfix := source.iterateLetter_infix_of_mem_iterate
      (later := sourceDepth)
      (hsourceContains input.seed maxSourceLetter)
    have hdeeperSourceLength :
        (source.iterateLetter (sourceDepth + primitiveDepth)
          input.seed).length ≤
          source.maxIterateLength primitiveDepth *
            (source.iterateLetter sourceDepth input.seed).length := by
      have hbound := source.iterateWord_length_le_maxIterateLength
        primitiveDepth (source.iterateLetter sourceDepth input.seed)
      calc
        (source.iterateLetter (sourceDepth + primitiveDepth)
              input.seed).length =
            (source.iterateWord primitiveDepth
              (source.iterateLetter sourceDepth input.seed)).length := by
          change (source.iterateWord (sourceDepth + primitiveDepth)
              [input.seed]).length = _
          rw [Nat.add_comm, source.iterateWord_add_public]
          rfl
        _ ≤ source.maxIterateLength primitiveDepth *
              (source.iterateLetter sourceDepth input.seed).length := hbound
    have hmaxSourceDepth : source.maxIterateLength sourceDepth ≤
        source.maxIterateLength primitiveDepth *
          (source.iterateLetter sourceDepth input.seed).length := by
      calc
        source.maxIterateLength sourceDepth =
            (source.iterateLetter sourceDepth maxSourceLetter).length :=
          hmaxSourceLetter.symm
        _ ≤ (source.iterateLetter
              (sourceDepth + primitiveDepth) input.seed).length :=
          hmaxSourceInfix.length_le
        _ ≤ source.maxIterateLength primitiveDepth *
              (source.iterateLetter sourceDepth input.seed).length :=
          hdeeperSourceLength
    have hsourceImageRewrite :
        (source.power sourceExponent) letter =
          source.iterateWord sourceDepth (source letter) := by
      rw [hsourceExponentEq, Symbolic.Substitution.power_apply]
      change source.iterateWord (sourceDepth + 1) [letter] = _
      rw [source.iterateWord_add_public]
      simp [Symbolic.Substitution.iterateWord]
    have hsourceOne : (source letter).length ≤
        source.maxIterateLength 1 := by
      simpa [Symbolic.Substitution.iterateLetter,
        Symbolic.Substitution.iterateWord] using
        source.iterateLetter_length_le_maxIterateLength 1 letter
    have hsourceImagePrevious :
        ((source.power sourceExponent) letter).length ≤
          sourceConstant *
            (source.iterateLetter sourceDepth input.seed).length := by
      rw [hsourceImageRewrite]
      calc
        (source.iterateWord sourceDepth (source letter)).length ≤
            source.maxIterateLength sourceDepth *
              (source letter).length :=
          source.iterateWord_length_le_maxIterateLength
            sourceDepth (source letter)
        _ ≤ (source.maxIterateLength primitiveDepth *
              (source.iterateLetter sourceDepth input.seed).length) *
                source.maxIterateLength 1 :=
          Nat.mul_le_mul hmaxSourceDepth hsourceOne
        _ = sourceConstant *
              (source.iterateLetter sourceDepth input.seed).length := by
          simp only [sourceConstant, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
    have hpreviousSeedLtMarker' :
        (source.iterateLetter sourceDepth input.seed).length <
          (tower.marker refinementExponent).length := by
      simpa [hsourceExponentEq] using hpreviousSeedLtMarker
    have hmarkerExpanded : (tower.marker refinementExponent).length ≤
        2 * (theta.iterateWord refinementExponent input.marker).length := by
      rw [tower_marker_eq_expanded_b9 input tower refinementExponent]
      exact expandedTowerMarker_length_le_b9 theta input.marker
        hthetaImageTwo refinementExponent
    obtain ⟨previousRefinement, hrefinementExponentEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hrefinementExponentPos)
    obtain ⟨maxThetaLetter, hmaxThetaLetter⟩ :=
      theta.exists_length_eq_maxIterateLength previousRefinement
    have hmaxThetaMem : maxThetaLetter ∈
        theta.iterateLetter 1 (minimumLetter index) := by
      simpa [theta, Symbolic.Substitution.iterateLetter,
        Symbolic.Substitution.iterateWord, returnDecoderSubstitution] using
        input.decoder_contains_all (minimumLetter index) maxThetaLetter
    have hmaxThetaInfix := theta.iterateLetter_infix_of_mem_iterate
      (later := previousRefinement) hmaxThetaMem
    have hmaxPreviousLeMinimum :
        theta.maxIterateLength previousRefinement ≤
          ((theta.power refinementExponent) (minimumLetter index)).length := by
      calc
        theta.maxIterateLength previousRefinement =
            (theta.iterateLetter previousRefinement maxThetaLetter).length :=
          hmaxThetaLetter.symm
        _ ≤ (theta.iterateLetter
              (previousRefinement + 1) (minimumLetter index)).length :=
          hmaxThetaInfix.length_le
        _ = ((theta.power refinementExponent)
              (minimumLetter index)).length := by
          rw [hrefinementExponentEq]
          simp [Symbolic.Substitution.power_apply]
    have hmaxCurrentLeMinimum :
        theta.maxIterateLength refinementExponent ≤
          theta.maxIterateLength 1 *
            ((theta.power refinementExponent)
              (minimumLetter index)).length := by
      rw [hrefinementExponentEq] at hmaxPreviousLeMinimum ⊢
      exact (theta.maxIterateLength_add_le previousRefinement 1).trans
        (Nat.mul_le_mul_left _ hmaxPreviousLeMinimum)
    have hmarkerMinimum : (tower.marker refinementExponent).length ≤
        markerConstant *
          ((theta.power refinementExponent) (minimumLetter index)).length := by
      have hterm := theta.iterateWord_length_le_maxIterateLength
        refinementExponent input.marker
      calc
        (tower.marker refinementExponent).length ≤
            2 * (theta.iterateWord refinementExponent input.marker).length :=
          hmarkerExpanded
        _ ≤ 2 * (theta.maxIterateLength refinementExponent *
              input.marker.length) := Nat.mul_le_mul_left 2 hterm
        _ ≤ 2 * ((theta.maxIterateLength 1 *
              ((theta.power refinementExponent)
                (minimumLetter index)).length) * input.marker.length) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_right input.marker.length hmaxCurrentLeMinimum)
        _ = markerConstant *
              ((theta.power refinementExponent)
                (minimumLetter index)).length := by
          simp only [markerConstant, Nat.mul_assoc, Nat.mul_comm,
            Nat.mul_left_comm]
    change ((source.power sourceExponent) letter).length ≤
      ratioBound *
        ((theta.power refinementExponent) (minimumLetter index)).length
    calc
      ((source.power sourceExponent) letter).length ≤
          sourceConstant *
            (source.iterateLetter sourceDepth input.seed).length :=
        hsourceImagePrevious
      _ ≤ sourceConstant *
            (tower.marker refinementExponent).length :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hpreviousSeedLtMarker')
      _ ≤ sourceConstant *
            (markerConstant *
              ((theta.power refinementExponent)
                (minimumLetter index)).length) :=
        Nat.mul_le_mul_left _ hmarkerMinimum
      _ = ratioBound *
            ((theta.power refinementExponent)
              (minimumLetter index)).length := by
        simp [ratioBound, Nat.mul_assoc]

/-- C3.2: uniform finite-word bounds for every auxiliary `gamma_k` image. -/
structure DurandGammaUniformBounds
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    (sequence : DurandGammaSequence input) where
  imageLengthBound : Nat
  imageLengthBound_pos : 0 < imageLengthBound
  image_length_le : ∀ index letter,
    (sequence.gammaAt index letter).length ≤ imageLengthBound

/-- A finite word decoded into blocks is at least its number of letters
times the length of a shortest block. -/
private theorem minimumImage_mul_length_le_mapWord_b9
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet)
    (minimumLetter : alphabet)
    (hminimum : ∀ letter,
      (substitution minimumLetter).length ≤
        (substitution letter).length)
    (finiteWord : Symbolic.Word alphabet) :
    (substitution minimumLetter).length * finiteWord.length ≤
      (substitution.mapWord finiteWord).length := by
  induction finiteWord with
  | nil => simp
  | cons letter tail ih =>
      rw [Symbolic.Substitution.mapWord_cons, List.length_append,
        List.length_cons]
      calc
        (substitution minimumLetter).length * (tail.length + 1) =
            (substitution minimumLetter).length +
              (substitution minimumLetter).length * tail.length := by
          rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ (substitution letter).length +
              (substitution.mapWord tail).length :=
          Nat.add_le_add (hminimum letter) ih

/-- Leaf C3.2: linear-recurrence return bounds make the `gamma_k` images
uniformly short. -/
theorem durand_gammaSequence_has_uniformBounds
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    (sequence : DurandGammaSequence input) :
    Nonempty (DurandGammaUniformBounds sequence) := by
  classical
  obtain ⟨ratio⟩ :=
    durand_maximalGammaSequence_has_lengthRatioControl sequence
  refine ⟨{
    imageLengthBound := ratio.ratioBound
    imageLengthBound_pos := ratio.ratioBound_pos
    image_length_le := ?_ }⟩
  intro index letter
  let decoder :=
    (returnDecoderSubstitution input.decomposition).power
      (sequence.refinementPower index)
  let shortest := ratio.minimumLetter index
  let shortestLength := (decoder shortest).length
  have hshortest : ∀ candidate : Fin rank,
      shortestLength ≤ (decoder candidate).length := by
    intro candidate
    exact ratio.minimumLetter_is_minimum index candidate
  have hshortestPos : 0 < shortestLength := by
    exact List.length_pos_of_ne_nil (decoder.image_ne_nil shortest)
  have hdecodedLower :
      shortestLength * (sequence.gammaAt index letter).length ≤
        (decoder.mapWord (sequence.gammaAt index letter)).length :=
    minimumImage_mul_length_le_mapWord_b9 decoder shortest hshortest
      (sequence.gammaAt index letter)
  have hdecodedEq :
      decoder.mapWord (sequence.gammaAt index letter) =
        (source.power (sequence.sourcePower index)) letter := by
    have heq := congrArg
      (fun substitution : Symbolic.Substitution (Fin rank) =>
        substitution letter)
      (sequence.theta_comp_gammaAt index)
    exact heq
  have hcancel : shortestLength *
        (sequence.gammaAt index letter).length ≤
      shortestLength * ratio.ratioBound := by
    calc
      shortestLength * (sequence.gammaAt index letter).length ≤
          (decoder.mapWord (sequence.gammaAt index letter)).length :=
        hdecodedLower
      _ = ((source.power (sequence.sourcePower index)) letter).length := by
        rw [hdecodedEq]
      _ ≤ ratio.ratioBound * shortestLength :=
        ratio.source_image_length_le index letter
      _ = shortestLength * ratio.ratioBound := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hcancel hshortestPos

/-- C3.3: a finite code for all substitutions satisfying the uniform image
bound.  Equal codes identify the full letter-to-word function, not only its
incidence matrix. -/
structure DurandFiniteGammaCoding
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {sequence : DurandGammaSequence input}
    (_bounds : DurandGammaUniformBounds sequence) where
  codeCount : Nat
  codeCount_pos : 0 < codeCount
  code : Nat → Fin codeCount
  same_code : ∀ left right, code left = code right →
    sequence.gammaAt left = sequence.gammaAt right

/-- Leaf C3.3: bounded words over the finite return alphabet give a finite
code for the auxiliary substitutions. -/
theorem durand_uniformGammaBounds_have_finiteCoding
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {sequence : DurandGammaSequence input}
    (bounds : DurandGammaUniformBounds sequence) :
    Nonempty (DurandFiniteGammaCoding bounds) := by
  classical
  let codeType := Fin rank → Fin bounds.imageLengthBound → Option (Fin rank)
  let encode : Nat → codeType := fun index letter position =>
    (sequence.gammaAt index letter)[position.1]?
  let codeEquiv := Fintype.equivFin codeType
  let code : Nat → Fin (Fintype.card codeType) := fun index =>
    codeEquiv (encode index)
  have hcard : 0 < Fintype.card codeType := by
    letI : Nonempty codeType := ⟨fun _ _ => none⟩
    exact Fintype.card_pos
  refine ⟨{
    codeCount := Fintype.card codeType
    codeCount_pos := hcard
    code := code
    same_code := ?_ }⟩
  intro left right hcode
  have hencoded : encode left = encode right := by
    apply codeEquiv.injective
    exact hcode
  have substitution_ext (σ τ : Symbolic.Substitution (Fin rank))
      (himages : ∀ letter, σ letter = τ letter) : σ = τ := by
    cases σ with
    | mk σimage σnonempty =>
        cases τ with
        | mk τimage τnonempty =>
            have himage : σimage = τimage := by
              funext letter
              exact himages letter
            subst τimage
            rfl
  apply substitution_ext
  intro letter
  apply List.ext_getElem?
  intro position
  by_cases hposition : position < bounds.imageLengthBound
  · let boundedPosition : Fin bounds.imageLengthBound :=
      ⟨position, hposition⟩
    have hvalue := congrFun (congrFun hencoded letter) boundedPosition
    exact hvalue
  · have hleftLength := bounds.image_length_le left letter
    have hrightLength := bounds.image_length_le right letter
    have hleftOut : (sequence.gammaAt left letter)[position]? = none := by
      exact List.getElem?_eq_none (by omega)
    have hrightOut : (sequence.gammaAt right letter)[position]? = none := by
      exact List.getElem?_eq_none (by omega)
    rw [hleftOut, hrightOut]

/-- C3.4: an infinite increasing subsequence on which `gamma_k` is literally
constant. -/
structure DurandConstantGammaSubsequence
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    (sequence : DurandGammaSequence input) where
  embedding : Nat → Nat
  embedding_strictMono : StrictMono embedding
  gamma : Symbolic.Substitution (Fin rank)
  gamma_eq : ∀ index, sequence.gammaAt (embedding index) = gamma

/-- Leaf C3.4: infinite pigeonhole on the finite gamma code supplies a
strictly increasing constant-gamma subsequence. -/
theorem durand_finiteGammaCoding_has_constantSubsequence
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {sequence : DurandGammaSequence input}
    {bounds : DurandGammaUniformBounds sequence}
    (coding : DurandFiniteGammaCoding bounds) :
    Nonempty (DurandConstantGammaSubsequence sequence) := by
  classical
  let fiber : Fin coding.codeCount → Set Nat := fun value =>
    {index | coding.code index = value}
  have hcover : (⋃ value, fiber value) = Set.univ := by
    ext index
    simp [fiber]
  have hinfiniteFiber : ∃ value, (fiber value).Infinite := by
    by_contra hnone
    push_neg at hnone
    have hfiniteUnion : (⋃ value, fiber value).Finite :=
      Set.finite_iUnion fun value => hnone value
    rw [hcover] at hfiniteUnion
    exact Set.infinite_univ hfiniteUnion
  obtain ⟨value, hvalueInfinite⟩ := hinfiniteFiber
  let start : Nat := Classical.choose hvalueInfinite.nonempty
  let next : Nat → Nat := fun previous =>
    Classical.choose (hvalueInfinite.exists_gt previous)
  have hstartMem : start ∈ fiber value :=
    Classical.choose_spec hvalueInfinite.nonempty
  have hnextMem : ∀ previous, next previous ∈ fiber value := fun previous =>
    (Classical.choose_spec (hvalueInfinite.exists_gt previous)).1
  have hnextGt : ∀ previous, previous < next previous := fun previous =>
    (Classical.choose_spec (hvalueInfinite.exists_gt previous)).2
  let embedding : Nat → Nat := fun index =>
    Nat.rec start (fun _ previous => next previous) index
  have hembeddingMem : ∀ index, embedding index ∈ fiber value := by
    intro index
    induction index with
    | zero => exact hstartMem
    | succ index ih =>
        change next (embedding index) ∈ fiber value
        exact hnextMem (embedding index)
  have hembeddingStrict : StrictMono embedding := by
    apply strictMono_nat_of_lt_succ
    intro index
    change embedding index < next (embedding index)
    exact hnextGt (embedding index)
  let gamma := sequence.gammaAt (embedding 0)
  have hgamma : ∀ index, sequence.gammaAt (embedding index) = gamma := by
    intro index
    apply coding.same_code
    exact (hembeddingMem index).trans (hembeddingMem 0).symm
  exact ⟨{
    embedding := embedding
    embedding_strictMono := hembeddingStrict
    gamma := gamma
    gamma_eq := hgamma }⟩

/-- Proved C3.5 packaging: restrict both cofinal exponent sequences and the
two exact word equations to the constant-gamma subsequence. -/
theorem durand_constantGammaSubsequence_packages_powerEquationFamily
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {sequence : DurandGammaSequence input}
    (subsequence : DurandConstantGammaSubsequence sequence) :
    Nonempty (DurandPowerEquationFamily input) := by
  let sourcePower : Nat → Nat := fun index =>
    sequence.sourcePower (subsequence.embedding index)
  let refinementPower : Nat → Nat := fun index =>
    sequence.refinementPower (subsequence.embedding index)
  have hsourceStrict : StrictMono sourcePower := by
    intro left right hlt
    exact sequence.sourcePower_strictMono
      (subsequence.embedding_strictMono hlt)
  have hrefinementStrict : StrictMono refinementPower := by
    intro left right hlt
    exact sequence.refinementPower_strictMono
      (subsequence.embedding_strictMono hlt)
  have hsourceZero : 0 < sourcePower 0 :=
    lt_of_lt_of_le sequence.sourcePower_zero_pos
      (sequence.sourcePower_strictMono.monotone
        (Nat.zero_le (subsequence.embedding 0)))
  have hrefinementZero : 0 < refinementPower 0 :=
    lt_of_lt_of_le sequence.refinementPower_zero_pos
      (sequence.refinementPower_strictMono.monotone
        (Nat.zero_le (subsequence.embedding 0)))
  exact ⟨{
    sourcePower := sourcePower
    sourcePower_strictMono := hsourceStrict
    sourcePower_zero_pos := hsourceZero
    refinementPower := refinementPower
    refinementPower_strictMono := hrefinementStrict
    refinementPower_zero_pos := hrefinementZero
    gamma := subsequence.gamma
    gamma_nonempty := subsequence.gamma.image_ne_nil
    theta_comp_gamma := by
      intro index
      have h := sequence.theta_comp_gammaAt (subsequence.embedding index)
      rw [subsequence.gamma_eq index] at h
      exact h
    gamma_comp_theta := by
      intro index
      have h := sequence.gammaAt_comp_theta (subsequence.embedding index)
      rw [subsequence.gamma_eq index] at h
      exact h }⟩

/-- Proved C3 / Durand Proposition 10 aggregator.  The generic statement is
kept separate from the left/right packaging. -/
theorem durand_proposition10_powerEquationFamily
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    (input : DurandProposition10Input word source) :
    Nonempty (DurandPowerEquationFamily input) := by
  obtain ⟨sequence⟩ := durand_proposition10_constructGammaSequence input
  obtain ⟨bounds⟩ := durand_gammaSequence_has_uniformBounds sequence
  obtain ⟨coding⟩ := durand_uniformGammaBounds_have_finiteCoding bounds
  obtain ⟨subsequence⟩ :=
    durand_finiteGammaCoding_has_constantSubsequence coding
  exact durand_constantGammaSubsequence_packages_powerEquationFamily
    subsequence

/-- Both exact powered sources carry Proposition 10 equation families for
the same return decoder `Theta`. -/
structure DurandTwoSourcePowerEquationData
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (system : DurandCommonDerivedSystem refinements) where
  left : DurandPowerEquationFamily system.leftInput
  right : DurandPowerEquationFamily system.rightInput

/-- Proved C3 packaging aggregator. -/
theorem durandCommonSystem_has_twoPowerEquationFamilies
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    (system : DurandCommonDerivedSystem refinements) :
    Nonempty (DurandTwoSourcePowerEquationData system) := by
  obtain ⟨left⟩ :=
    durand_proposition10_powerEquationFamily system.leftInput
  obtain ⟨right⟩ :=
    durand_proposition10_powerEquationFamily system.rightInput
  exact ⟨{ left := left, right := right }⟩

/-- The dominant-eigenvalue consequence of Durand's Proposition 11 for the
two sources sharing `Theta`.  The four positive differences are retained so
the final exponent arithmetic is definitionally visible. -/
structure DurandProposition11Comparison
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {system : DurandCommonDerivedSystem refinements}
    (equations : DurandTwoSourcePowerEquationData system) where
  leftEarlierIndex : Nat
  leftLaterIndex : Nat
  leftIndex_lt : leftEarlierIndex < leftLaterIndex
  leftSourceDifference : Nat
  leftSourceDifference_pos : 0 < leftSourceDifference
  leftSourceDifference_eq : leftSourceDifference =
    equations.left.sourcePower leftLaterIndex -
      equations.left.sourcePower leftEarlierIndex
  leftRefinementDifference : Nat
  leftRefinementDifference_pos : 0 < leftRefinementDifference
  leftRefinementDifference_eq : leftRefinementDifference =
    equations.left.refinementPower leftLaterIndex -
      equations.left.refinementPower leftEarlierIndex
  rightEarlierIndex : Nat
  rightLaterIndex : Nat
  rightIndex_lt : rightEarlierIndex < rightLaterIndex
  rightSourceDifference : Nat
  rightSourceDifference_pos : 0 < rightSourceDifference
  rightSourceDifference_eq : rightSourceDifference =
    equations.right.sourcePower rightLaterIndex -
      equations.right.sourcePower rightEarlierIndex
  rightRefinementDifference : Nat
  rightRefinementDifference_pos : 0 < rightRefinementDifference
  rightRefinementDifference_eq : rightRefinementDifference =
    equations.right.refinementPower rightLaterIndex -
      equations.right.refinementPower rightEarlierIndex
  thetaGrowth : Real
  thetaGrowth_gt_one : 1 < thetaGrowth
  thetaDominant : IsDominantEigenvalue
    (returnDecoderSubstitution system.decomposition).incidenceMatrix thetaGrowth
  left_growth_eq :
    ((a ^ family.infrastructure.left.exponent) ^ system.commonPower) ^
        leftSourceDifference =
      thetaGrowth ^ leftRefinementDifference
  right_growth_eq :
    ((b ^ family.infrastructure.right.exponent) ^ system.commonPower) ^
        rightSourceDifference =
      thetaGrowth ^ rightRefinementDifference

/-- A positive pair of exponent differences selected from one exact
Proposition-10 equation family. -/
structure DurandPowerEquationDifference
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    (equations : DurandPowerEquationFamily input) where
  earlierIndex : Nat
  laterIndex : Nat
  index_lt : earlierIndex < laterIndex
  sourceDifference : Nat
  sourceDifference_pos : 0 < sourceDifference
  sourceDifference_eq : sourceDifference =
    equations.sourcePower laterIndex - equations.sourcePower earlierIndex
  refinementDifference : Nat
  refinementDifference_pos : 0 < refinementDifference
  refinementDifference_eq : refinementDifference =
    equations.refinementPower laterIndex -
      equations.refinementPower earlierIndex

/-- Proved selection of the first two indices; strict monotonicity makes both
differences positive. -/
theorem durandPowerEquationFamily_has_positiveDifference
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    (equations : DurandPowerEquationFamily input) :
    Nonempty (DurandPowerEquationDifference equations) := by
  have hsource := equations.sourcePower_strictMono (Nat.zero_lt_succ 0)
  have hrefinement :=
    equations.refinementPower_strictMono (Nat.zero_lt_succ 0)
  exact ⟨{
    earlierIndex := 0
    laterIndex := 1
    index_lt := by omega
    sourceDifference := equations.sourcePower 1 - equations.sourcePower 0
    sourceDifference_pos := Nat.sub_pos_of_lt hsource
    sourceDifference_eq := rfl
    refinementDifference :=
      equations.refinementPower 1 - equations.refinementPower 0
    refinementDifference_pos := Nat.sub_pos_of_lt hrefinement
    refinementDifference_eq := rfl }⟩

/-- C4.1 / first half of Durand Proposition 11: every nonzero eigenvalue of
the selected source-power difference occurs in the matching `Theta` power. -/
structure DurandForwardEigenvalueInclusion
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    (difference : DurandPowerEquationDifference equations) where
  includes : ∀ eigenvalue : ℂ, eigenvalue ≠ 0 →
    IsComplexEigenvalue
        (source.power difference.sourceDifference).incidenceMatrix eigenvalue →
      IsComplexEigenvalue
        ((returnDecoderSubstitution input.decomposition).power
          difference.refinementDifference).incidenceMatrix eigenvalue

/-- Word counting makes incidence matrices contravariantly multiplicative
under substitution composition. -/
private theorem incidenceMatrix_comp_b9
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    (outer inner : Symbolic.Substitution alphabet) :
    (outer.comp inner).incidenceMatrix =
      outer.incidenceMatrix * inner.incidenceMatrix := by
  have count_mapWord (word : Symbolic.Word alphabet) (letter : alphabet) :
      (outer.mapWord word).count letter =
        ∑ sourceLetter : alphabet,
          (outer sourceLetter).count letter * word.count sourceLetter := by
    induction word with
    | nil => simp
    | cons head tail ih =>
        rw [Symbolic.Substitution.mapWord_cons, List.count_append, ih]
        calc
          (outer head).count letter +
                ∑ sourceLetter : alphabet,
                  (outer sourceLetter).count letter * tail.count sourceLetter =
              (∑ sourceLetter : alphabet,
                  if sourceLetter = head then
                    (outer sourceLetter).count letter else 0) +
                ∑ sourceLetter : alphabet,
                  (outer sourceLetter).count letter * tail.count sourceLetter := by
            simp
          _ = ∑ sourceLetter : alphabet,
                ((if sourceLetter = head then
                    (outer sourceLetter).count letter else 0) +
                  (outer sourceLetter).count letter *
                    tail.count sourceLetter) :=
            Finset.sum_add_distrib.symm
          _ = ∑ sourceLetter : alphabet,
                (outer sourceLetter).count letter *
                  (head :: tail).count sourceLetter := by
            apply Finset.sum_congr rfl
            intro sourceLetter _
            by_cases heq : sourceLetter = head
            · subst sourceLetter
              simp [Nat.mul_add, Nat.add_comm]
            · simp [heq, Ne.symm heq]
  ext output sourceLetter
  simp [Symbolic.Substitution.incidenceMatrix, Matrix.mul_apply,
    count_mapWord]

/-- Entrywise coercion of a natural matrix to a complex matrix. -/
private def complexNatMatrix {alphabet : Type*}
    (matrix : Matrix alphabet alphabet Nat) :
    Matrix alphabet alphabet ℂ := fun row column => matrix row column

private theorem complexNatMatrix_mul
    {alphabet : Type*} [Fintype alphabet]
    (left right : Matrix alphabet alphabet Nat) :
    complexNatMatrix (left * right) =
      complexNatMatrix left * complexNatMatrix right := by
  ext row column
  simp [complexNatMatrix, Matrix.mul_apply]

private theorem complexNatMatrix_add
    {alphabet : Type*}
    (left right : Matrix alphabet alphabet Nat) :
    complexNatMatrix (left + right) =
      complexNatMatrix left + complexNatMatrix right := by
  ext row column
  simp [complexNatMatrix]

private theorem complexNatMatrix_transpose
    {alphabet : Type*} (matrix : Matrix alphabet alphabet Nat) :
    complexNatMatrix matrix.transpose =
      (complexNatMatrix matrix).transpose := by
  rfl

private theorem complexNatMatrix_pow
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    (matrix : Matrix alphabet alphabet Nat) (powerIndex : Nat) :
    complexNatMatrix (matrix ^ powerIndex) =
      complexNatMatrix matrix ^ powerIndex := by
  induction powerIndex with
  | zero =>
      ext row column
      by_cases heq : row = column
      · subst column
        simp [complexNatMatrix]
      · simp [complexNatMatrix, heq]
  | succ powerIndex ih =>
      rw [pow_succ, pow_succ, complexNatMatrix_mul, ih]

/-- The explicit natural-matrix eigenvalue predicate is the standard
finite-dimensional eigenvalue predicate after complexification. -/
private theorem isComplexEigenvalue_iff_hasEigenvalue_b9
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    (matrix : Matrix alphabet alphabet Nat) (eigenvalue : ℂ) :
    IsComplexEigenvalue matrix eigenvalue ↔
      Module.End.HasEigenvalue
        (Matrix.toLin' (complexNatMatrix matrix)) eigenvalue := by
  constructor
  · rintro ⟨vector, hvector, heigen⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hvector⟩
    ext row
    simp only [Matrix.toLin'_apply, Matrix.mulVec, complexNatMatrix,
      Pi.smul_apply, smul_eq_mul]
    exact heigen row
  · intro hvalue
    obtain ⟨vector, hvector⟩ := hvalue.exists_hasEigenvector
    refine ⟨vector, hvector.2, ?_⟩
    have heigen := Module.End.mem_eigenspace_iff.mp hvector.1
    intro row
    have hrow := congrFun heigen row
    simpa only [Matrix.toLin'_apply, Matrix.mulVec, complexNatMatrix,
      Pi.smul_apply, smul_eq_mul] using hrow

/-- Transposition preserves the explicit complex eigenvalue predicate. -/
private theorem isComplexEigenvalue_transpose_iff_b9
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    (matrix : Matrix alphabet alphabet Nat) (eigenvalue : ℂ) :
    IsComplexEigenvalue matrix.transpose eigenvalue ↔
      IsComplexEigenvalue matrix eigenvalue := by
  rw [isComplexEigenvalue_iff_hasEigenvalue_b9,
    isComplexEigenvalue_iff_hasEigenvalue_b9,
    Module.End.hasEigenvalue_iff_mem_spectrum,
    Module.End.hasEigenvalue_iff_mem_spectrum,
    Matrix.spectrum_toLin', Matrix.spectrum_toLin',
    Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (complexNatMatrix matrix).transpose.charpoly.IsRoot eigenvalue ↔
    (complexNatMatrix matrix).charpoly.IsRoot eigenvalue
  rw [Matrix.charpoly_transpose]

/-- A matrix eigenvector equation persists through matrix powers. -/
private theorem complexMatrix_eigenvector_power
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    (matrix : Matrix alphabet alphabet ℂ)
    (vector : alphabet → ℂ) (eigenvalue : ℂ)
    (heigen : matrix.mulVec vector = eigenvalue • vector) :
    ∀ powerIndex : Nat,
      (matrix ^ powerIndex).mulVec vector =
        (eigenvalue ^ powerIndex) • vector := by
  intro powerIndex
  induction powerIndex with
  | zero =>
      simp
  | succ powerIndex ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih,
        Matrix.mulVec_smul, heigen]
      rw [smul_smul, pow_succ]

/-- A vector killed by a matrix is killed by every positive matrix power. -/
private theorem complexMatrix_power_mulVec_eq_zero
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    (matrix : Matrix alphabet alphabet ℂ) (vector : alphabet → ℂ)
    (hzero : matrix.mulVec vector = 0) {powerIndex : Nat}
    (hpower : 0 < powerIndex) :
    (matrix ^ powerIndex).mulVec vector = 0 := by
  obtain ⟨later, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpower.ne'
  rw [pow_succ, ← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero]

/-- A nonzero eigenvalue crosses a powered intertwiner even when the
intertwiner itself may be singular. -/
private theorem nonzeroEigenvalue_transfer_of_powerIntertwining
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    (source target : Matrix alphabet alphabet Nat)
    (sourcePrefix sourceDifference targetDifference : Nat)
    (hsourceDifference : 0 < sourceDifference)
    (hintertwines :
      target ^ targetDifference * source ^ sourcePrefix =
        source ^ sourcePrefix * source ^ sourceDifference)
    {eigenvalue : ℂ} (heigenvalue : eigenvalue ≠ 0)
    (heigen : IsComplexEigenvalue (source ^ sourceDifference) eigenvalue) :
    IsComplexEigenvalue (target ^ targetDifference) eigenvalue := by
  rcases heigen with ⟨vector, hvector, heigen⟩
  let sourceComplex := complexNatMatrix source
  let targetComplex := complexNatMatrix target
  have heigenFunction :
      (sourceComplex ^ sourceDifference).mulVec vector =
        eigenvalue • vector := by
    have hraw :
        (complexNatMatrix (source ^ sourceDifference)).mulVec vector =
          eigenvalue • vector := by
      funext row
      simpa [complexNatMatrix, Matrix.mulVec, Pi.smul_apply] using heigen row
    rw [complexNatMatrix_pow] at hraw
    simpa [sourceComplex] using hraw
  let transported := (sourceComplex ^ sourcePrefix).mulVec vector
  have htransported : transported ≠ 0 := by
    intro hzero
    by_cases hprefixZero : sourcePrefix = 0
    · subst sourcePrefix
      apply hvector
      simpa [transported] using hzero
    · have hprefixPos : 0 < sourcePrefix := Nat.pos_of_ne_zero hprefixZero
      have hkill :
          ((sourceComplex ^ sourcePrefix) ^ sourceDifference).mulVec vector =
            0 :=
        complexMatrix_power_mulVec_eq_zero
          (sourceComplex ^ sourcePrefix) vector hzero hsourceDifference
      have heigenPower := complexMatrix_eigenvector_power
        (sourceComplex ^ sourceDifference) vector eigenvalue
        heigenFunction sourcePrefix
      have hpowers :
          (sourceComplex ^ sourcePrefix) ^ sourceDifference =
            (sourceComplex ^ sourceDifference) ^ sourcePrefix := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [hpowers, heigenPower] at hkill
      exact (smul_ne_zero (pow_ne_zero _ heigenvalue) hvector) hkill
  refine ⟨transported, htransported, ?_⟩
  intro row
  have hintertwinesComplex := congrArg complexNatMatrix hintertwines
  simp only [complexNatMatrix_mul, complexNatMatrix_pow] at hintertwinesComplex
  have htransportedEigen :
      (targetComplex ^ targetDifference).mulVec transported =
        eigenvalue • transported := by
    calc
      (targetComplex ^ targetDifference).mulVec transported =
          ((targetComplex ^ targetDifference) *
            (sourceComplex ^ sourcePrefix)).mulVec vector := by
            rw [← Matrix.mulVec_mulVec]
      _ = ((sourceComplex ^ sourcePrefix) *
            (sourceComplex ^ sourceDifference)).mulVec vector := by
            rw [hintertwinesComplex]
      _ = (sourceComplex ^ sourcePrefix).mulVec
            ((sourceComplex ^ sourceDifference).mulVec vector) := by
            rw [Matrix.mulVec_mulVec]
      _ = (sourceComplex ^ sourcePrefix).mulVec
            (eigenvalue • vector) := by rw [heigenFunction]
      _ = eigenvalue • transported := by
            rw [Matrix.mulVec_smul]
  have hraw :
      (complexNatMatrix (target ^ targetDifference)).mulVec transported =
        eigenvalue • transported := by
    rw [complexNatMatrix_pow]
    simpa [targetComplex] using htransportedEigen
  have hrow := congrFun hraw row
  simpa [complexNatMatrix, Matrix.mulVec, Pi.smul_apply] using hrow

/-- The two selected Proposition-10 equations give the powered incidence
intertwining used in both directions of Proposition 11. -/
private theorem durand_powerDifference_incidence_intertwining
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    (difference : DurandPowerEquationDifference equations) :
    ((returnDecoderSubstitution input.decomposition).power
          difference.refinementDifference).incidenceMatrix *
        (source.power
          (equations.sourcePower difference.earlierIndex)).incidenceMatrix =
      (source.power
          (equations.sourcePower difference.earlierIndex)).incidenceMatrix *
        (source.power difference.sourceDifference).incidenceMatrix := by
  classical
  let theta := returnDecoderSubstitution input.decomposition
  let sourceMatrix := source.incidenceMatrix
  let thetaMatrix := theta.incidenceMatrix
  let sourcePrefix := equations.sourcePower difference.earlierIndex
  let refinementPrefix := equations.refinementPower difference.earlierIndex
  have hsourceAdd :
      sourcePrefix + difference.sourceDifference =
        equations.sourcePower difference.laterIndex := by
    dsimp [sourcePrefix]
    rw [difference.sourceDifference_eq]
    have hlt := equations.sourcePower_strictMono difference.index_lt
    omega
  have hrefinementAdd :
      difference.refinementDifference + refinementPrefix =
        equations.refinementPower difference.laterIndex := by
    dsimp [refinementPrefix]
    rw [difference.refinementDifference_eq]
    have hlt := equations.refinementPower_strictMono difference.index_lt
    omega
  have hearlierRaw := congrArg
    (fun substitution : Symbolic.Substitution (Fin rank) =>
      substitution.incidenceMatrix)
    (equations.theta_comp_gamma difference.earlierIndex)
  have hlaterRaw := congrArg
    (fun substitution : Symbolic.Substitution (Fin rank) =>
      substitution.incidenceMatrix)
    (equations.theta_comp_gamma difference.laterIndex)
  change
    ((((returnDecoderSubstitution input.decomposition).power
          (equations.refinementPower difference.earlierIndex)).comp
        equations.gamma).incidenceMatrix =
      (source.power
        (equations.sourcePower difference.earlierIndex)).incidenceMatrix)
    at hearlierRaw
  change
    ((((returnDecoderSubstitution input.decomposition).power
          (equations.refinementPower difference.laterIndex)).comp
        equations.gamma).incidenceMatrix =
      (source.power
        (equations.sourcePower difference.laterIndex)).incidenceMatrix)
    at hlaterRaw
  rw [incidenceMatrix_comp_b9,
    Symbolic.Substitution.incidenceMatrix_power,
    Symbolic.Substitution.incidenceMatrix_power] at hearlierRaw hlaterRaw
  have hearlier :
      thetaMatrix ^ refinementPrefix * equations.gamma.incidenceMatrix =
        sourceMatrix ^ sourcePrefix := by
    simpa [thetaMatrix, theta, refinementPrefix, sourceMatrix, sourcePrefix]
      using hearlierRaw
  have hlater :
      thetaMatrix ^ equations.refinementPower difference.laterIndex *
          equations.gamma.incidenceMatrix =
        sourceMatrix ^ equations.sourcePower difference.laterIndex := by
    simpa [thetaMatrix, theta, sourceMatrix] using hlaterRaw
  rw [Symbolic.Substitution.incidenceMatrix_power,
    Symbolic.Substitution.incidenceMatrix_power,
    Symbolic.Substitution.incidenceMatrix_power]
  calc
    thetaMatrix ^ difference.refinementDifference *
          sourceMatrix ^ sourcePrefix =
        thetaMatrix ^ difference.refinementDifference *
          (thetaMatrix ^ refinementPrefix *
            equations.gamma.incidenceMatrix) := by rw [hearlier]
    _ = (thetaMatrix ^ difference.refinementDifference *
            thetaMatrix ^ refinementPrefix) *
          equations.gamma.incidenceMatrix := by
            rw [Matrix.mul_assoc]
    _ = thetaMatrix ^
            (difference.refinementDifference + refinementPrefix) *
          equations.gamma.incidenceMatrix := by rw [pow_add]
    _ = thetaMatrix ^ equations.refinementPower difference.laterIndex *
          equations.gamma.incidenceMatrix := by rw [hrefinementAdd]
    _ = sourceMatrix ^ equations.sourcePower difference.laterIndex := hlater
    _ = sourceMatrix ^
          (sourcePrefix + difference.sourceDifference) := by rw [hsourceAdd]
    _ = sourceMatrix ^ sourcePrefix *
          sourceMatrix ^ difference.sourceDifference := by rw [pow_add]

/-- Leaf C4.1: cancel the nonzero action of the earlier source power in the
two exact `Theta/gamma/source` equations. -/
theorem durand_first_nonzeroEigenvalue_inclusion
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    (difference : DurandPowerEquationDifference equations) :
    Nonempty (DurandForwardEigenvalueInclusion difference) := by
  classical
  let theta := returnDecoderSubstitution input.decomposition
  let sourceMatrix := source.incidenceMatrix
  let thetaMatrix := theta.incidenceMatrix
  let sourcePrefix := equations.sourcePower difference.earlierIndex
  let refinementPrefix := equations.refinementPower difference.earlierIndex
  have hsourceAdd :
      sourcePrefix + difference.sourceDifference =
        equations.sourcePower difference.laterIndex := by
    dsimp [sourcePrefix]
    rw [difference.sourceDifference_eq]
    have hlt := equations.sourcePower_strictMono difference.index_lt
    omega
  have hrefinementAdd :
      difference.refinementDifference + refinementPrefix =
        equations.refinementPower difference.laterIndex := by
    dsimp [refinementPrefix]
    rw [difference.refinementDifference_eq]
    have hlt := equations.refinementPower_strictMono difference.index_lt
    omega
  have hearlierRaw := congrArg
    (fun substitution : Symbolic.Substitution (Fin rank) =>
      substitution.incidenceMatrix)
    (equations.theta_comp_gamma difference.earlierIndex)
  have hlaterRaw := congrArg
    (fun substitution : Symbolic.Substitution (Fin rank) =>
      substitution.incidenceMatrix)
    (equations.theta_comp_gamma difference.laterIndex)
  change
    ((((returnDecoderSubstitution input.decomposition).power
          (equations.refinementPower difference.earlierIndex)).comp
        equations.gamma).incidenceMatrix =
      (source.power
        (equations.sourcePower difference.earlierIndex)).incidenceMatrix)
    at hearlierRaw
  change
    ((((returnDecoderSubstitution input.decomposition).power
          (equations.refinementPower difference.laterIndex)).comp
        equations.gamma).incidenceMatrix =
      (source.power
        (equations.sourcePower difference.laterIndex)).incidenceMatrix)
    at hlaterRaw
  rw [incidenceMatrix_comp_b9,
    Symbolic.Substitution.incidenceMatrix_power,
    Symbolic.Substitution.incidenceMatrix_power] at hearlierRaw hlaterRaw
  have hearlier :
      thetaMatrix ^ refinementPrefix * equations.gamma.incidenceMatrix =
        sourceMatrix ^ sourcePrefix := by
    simpa [thetaMatrix, theta, refinementPrefix, sourceMatrix, sourcePrefix]
      using hearlierRaw
  have hlater :
      thetaMatrix ^ equations.refinementPower difference.laterIndex *
          equations.gamma.incidenceMatrix =
        sourceMatrix ^ equations.sourcePower difference.laterIndex := by
    simpa [thetaMatrix, theta, sourceMatrix] using hlaterRaw
  have hintertwines :
      thetaMatrix ^ difference.refinementDifference *
          sourceMatrix ^ sourcePrefix =
        sourceMatrix ^ sourcePrefix *
          sourceMatrix ^ difference.sourceDifference := by
    calc
      thetaMatrix ^ difference.refinementDifference *
            sourceMatrix ^ sourcePrefix =
          thetaMatrix ^ difference.refinementDifference *
            (thetaMatrix ^ refinementPrefix *
              equations.gamma.incidenceMatrix) := by rw [hearlier]
      _ = (thetaMatrix ^ difference.refinementDifference *
              thetaMatrix ^ refinementPrefix) *
            equations.gamma.incidenceMatrix := by
              rw [Matrix.mul_assoc]
      _ = thetaMatrix ^
              (difference.refinementDifference + refinementPrefix) *
            equations.gamma.incidenceMatrix := by
              rw [pow_add]
      _ = thetaMatrix ^ equations.refinementPower difference.laterIndex *
            equations.gamma.incidenceMatrix := by rw [hrefinementAdd]
      _ = sourceMatrix ^ equations.sourcePower difference.laterIndex := hlater
      _ = sourceMatrix ^
            (sourcePrefix + difference.sourceDifference) := by rw [hsourceAdd]
      _ = sourceMatrix ^ sourcePrefix *
            sourceMatrix ^ difference.sourceDifference := by rw [pow_add]
  refine ⟨{ includes := ?_ }⟩
  intro eigenvalue heigenvalue heigen
  rw [Symbolic.Substitution.incidenceMatrix_power] at heigen ⊢
  exact nonzeroEigenvalue_transfer_of_powerIntertwining
    sourceMatrix thetaMatrix sourcePrefix difference.sourceDifference
      difference.refinementDifference difference.sourceDifference_pos
      hintertwines heigenvalue heigen

/-! The next finite-word lemma is the precise combinatorial input used in
the boundary-error argument.  A factor of a substitution-fixed word contains
all the substitution tiles lying strictly between its two boundary tiles.
Only those two tiles can be lost. -/

private def fixedPointImageCut_b9 {alphabet : Type*}
    (substitution : Symbolic.Substitution alphabet)
    (fixedWord : Symbolic.InfiniteWord alphabet) (index : Nat) : Nat :=
  (substitution.mapWord (fixedWord.take index)).length

@[simp] private theorem fixedPointImageCut_zero_b9 {alphabet : Type*}
    (substitution : Symbolic.Substitution alphabet)
    (fixedWord : Symbolic.InfiniteWord alphabet) :
    fixedPointImageCut_b9 substitution fixedWord 0 = 0 := by
  simp [fixedPointImageCut_b9]

private theorem fixedPointImageCut_succ_b9 {alphabet : Type*}
    (substitution : Symbolic.Substitution alphabet)
    (fixedWord : Symbolic.InfiniteWord alphabet) (index : Nat) :
    fixedPointImageCut_b9 substitution fixedWord (index + 1) =
      fixedPointImageCut_b9 substitution fixedWord index +
        (substitution (fixedWord index)).length := by
  change (substitution.mapWord (fixedWord.take (index + 1))).length =
    (substitution.mapWord (fixedWord.take index)).length + _
  rw [Stream'.take_succ', Symbolic.Substitution.mapWord_append,
    List.length_append]
  simp only [Symbolic.Substitution.mapWord_cons,
    Symbolic.Substitution.mapWord_nil, List.append_nil]
  simp [Stream'.get]

private theorem fixedPointImageCut_add_b9 {alphabet : Type*}
    (substitution : Symbolic.Substitution alphabet)
    (fixedWord : Symbolic.InfiniteWord alphabet) (start count : Nat) :
    fixedPointImageCut_b9 substitution fixedWord (start + count) =
      fixedPointImageCut_b9 substitution fixedWord start +
        (substitution.mapWord
          ((fixedWord.drop start).take count)).length := by
  simp [fixedPointImageCut_b9, Stream'.take_add,
    Symbolic.Substitution.mapWord_append]

private theorem index_le_fixedPointImageCut_b9 {alphabet : Type*}
    (substitution : Symbolic.Substitution alphabet)
    (fixedWord : Symbolic.InfiniteWord alphabet) (index : Nat) :
    index ≤ fixedPointImageCut_b9 substitution fixedWord index := by
  simpa [fixedPointImageCut_b9] using
    substitution.length_le_mapWord_for_return (fixedWord.take index)

private theorem fixedPointImageCut_strictMono_b9 {alphabet : Type*}
    (substitution : Symbolic.Substitution alphabet)
    (fixedWord : Symbolic.InfiniteWord alphabet) :
    StrictMono (fixedPointImageCut_b9 substitution fixedWord) := by
  apply strictMono_nat_of_lt_succ
  intro index
  rw [fixedPointImageCut_succ_b9]
  exact Nat.lt_add_of_pos_right
    (List.length_pos_of_ne_nil (substitution.image_ne_nil _))

private def maximumImageLength_b9 {alphabet : Type*}
    [Fintype alphabet] [DecidableEq alphabet]
    (substitution : Symbolic.Substitution alphabet) : Nat :=
  Finset.univ.sup fun letter => (substitution letter).length

private theorem imageLength_le_maximumImageLength_b9 {alphabet : Type*}
    [Fintype alphabet] [DecidableEq alphabet]
    (substitution : Symbolic.Substitution alphabet) (letter : alphabet) :
    (substitution letter).length ≤ maximumImageLength_b9 substitution := by
  exact Finset.le_sup (f := fun sourceLetter =>
    (substitution sourceLetter).length) (Finset.mem_univ letter)

private structure FixedPointFactorCore_b9 {alphabet : Type*}
    [Fintype alphabet] [DecidableEq alphabet]
    (substitution : Symbolic.Substitution alphabet)
    (factor : Symbolic.Word alphabet) where
  middle : Symbolic.Word alphabet
  core_isInfix : substitution.mapWord middle <:+: factor
  residual_length_le :
    factor.length - (substitution.mapWord middle).length ≤
      2 * maximumImageLength_b9 substitution

/-- Keep all complete substitution images strictly between the two cuts that
surround a nonempty factor. -/
private theorem fixedPointFactor_has_boundedCore_b9 {alphabet : Type*}
    [Fintype alphabet] [DecidableEq alphabet]
    {substitution : Symbolic.Substitution alphabet}
    {fixedWord : Symbolic.InfiniteWord alphabet}
    (hfixed : substitution.IsFixedPoint fixedWord)
    {factor : Symbolic.Word alphabet} {start : Nat}
    (hfactor : Symbolic.InfiniteFactorAt fixedWord factor start)
    (hfactorNonempty : factor ≠ []) :
    Nonempty (FixedPointFactorCore_b9 substitution factor) := by
  let cut : Nat → Nat := fixedPointImageCut_b9 substitution fixedWord
  let endPosition : Nat := start + factor.length
  have hcutLower : ∀ index : Nat, index ≤ cut index := by
    intro index
    exact index_le_fixedPointImageCut_b9 substitution fixedWord index
  let startWitness : ∃ index : Nat, start ≤ cut index :=
    ⟨start, hcutLower start⟩
  let endWitness : ∃ index : Nat, endPosition ≤ cut index :=
    ⟨endPosition, hcutLower endPosition⟩
  let firstCut : Nat := Nat.find startWitness
  let lastCut : Nat := Nat.find endWitness
  have hfirst : start ≤ cut firstCut := by
    exact Nat.find_spec startWitness
  have hlast : endPosition ≤ cut lastCut := by
    exact Nat.find_spec endWitness
  have hstartEnd : start ≤ endPosition := by
    simp [endPosition]
  have hfirstLast : firstCut ≤ lastCut := by
    by_contra hnot
    have hlastFirst : lastCut < firstCut := Nat.lt_of_not_ge hnot
    have hminimal := Nat.find_min startWitness hlastFirst
    exact hminimal (hstartEnd.trans hlast)
  have hendPositive : 0 < endPosition := by
    have hlengthPositive := List.length_pos_of_ne_nil hfactorNonempty
    simp only [endPosition]
    omega
  have hlastPositive : 0 < lastCut := by
    by_contra hnot
    have hzero : lastCut = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hlast
    change endPosition ≤ fixedPointImageCut_b9 substitution fixedWord 0 at hlast
    rw [fixedPointImageCut_zero_b9] at hlast
    omega
  by_cases hsame : firstCut = lastCut
  · refine ⟨{
      middle := []
      core_isInfix := by simp
      residual_length_le := ?_ }⟩
    obtain ⟨previous, hfirstSucc⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt (hsame ▸ hlastPositive))
    have hpreviousNot : ¬ start ≤ cut previous := by
      intro hle
      exact (Nat.find_min startWitness (by omega)) hle
    have hpreviousLt : cut previous < start := Nat.lt_of_not_ge hpreviousNot
    have hlastAtFirst : endPosition ≤ cut firstCut := by
      simpa [hsame] using hlast
    have hcutStep : cut firstCut = cut previous +
        (substitution (fixedWord previous)).length := by
      change fixedPointImageCut_b9 substitution fixedWord firstCut = _
      rw [hfirstSucc]
      simpa [Nat.succ_eq_add_one] using
        fixedPointImageCut_succ_b9 substitution fixedWord previous
    have hfactorLength : factor.length ≤
        (substitution (fixedWord previous)).length := by
      simp only [endPosition] at hlastAtFirst
      omega
    have himageBound :
        (substitution (fixedWord previous)).length ≤
          maximumImageLength_b9 substitution :=
      imageLength_le_maximumImageLength_b9 substitution _
    simp only [Symbolic.Substitution.mapWord_nil, List.length_nil,
      Nat.sub_zero]
    omega
  · have hfirstLtLast : firstCut < lastCut :=
      lt_of_le_of_ne hfirstLast hsame
    let innerLast : Nat := lastCut - 1
    have hinnerLast : innerLast + 1 = lastCut := by
      simp only [innerLast]
      omega
    have hfirstLeInner : firstCut ≤ innerLast := by
      simp only [innerLast]
      omega
    let middle : Symbolic.Word alphabet :=
      (fixedWord.drop firstCut).take (innerLast - firstCut)
    let core : Symbolic.Word alphabet := substitution.mapWord middle
    have hcutAdd := fixedPointImageCut_add_b9 substitution fixedWord
      firstCut (innerLast - firstCut)
    have hindexAdd : firstCut + (innerLast - firstCut) = innerLast :=
      Nat.add_sub_of_le hfirstLeInner
    have hcoreLength : core.length = cut innerLast - cut firstCut := by
      change (substitution.mapWord
        ((fixedWord.drop firstCut).take
          (innerLast - firstCut))).length = _
      change fixedPointImageCut_b9 substitution fixedWord
          (firstCut + (innerLast - firstCut)) =
        fixedPointImageCut_b9 substitution fixedWord firstCut +
          (substitution.mapWord
            ((fixedWord.drop firstCut).take
              (innerLast - firstCut))).length at hcutAdd
      rw [hindexAdd] at hcutAdd
      change cut innerLast = cut firstCut + _ at hcutAdd
      have hcutLe : cut firstCut ≤ cut innerLast :=
        (fixedPointImageCut_strictMono_b9 substitution fixedWord).monotone
          hfirstLeInner
      omega
    have hinnerNot : ¬ endPosition ≤ cut innerLast := by
      intro hle
      exact (Nat.find_min endWitness (by omega)) hle
    have hinnerLt : cut innerLast < endPosition := Nat.lt_of_not_ge hinnerNot
    have hcoreAtRaw :=
      Symbolic.Substitution.iterateWord_drop_take_at_fixed
        hfixed 1 firstCut (innerLast - firstCut)
    have hcoreAt : Symbolic.InfiniteFactorAt fixedWord core (cut firstCut) := by
      simpa [core, middle, cut, fixedPointImageCut_b9,
        Symbolic.Substitution.iterateWord] using hcoreAtRaw
    let offset : Nat := cut firstCut - start
    have hposition : cut firstCut = start + offset := by
      simp only [offset]
      omega
    have hwithin : offset + core.length ≤ factor.length := by
      simp only [offset]
      rw [hcoreLength]
      simp only [endPosition] at hinnerLt
      have hcutOrder : cut firstCut ≤ cut innerLast :=
        (fixedPointImageCut_strictMono_b9 substitution fixedWord).monotone
          hfirstLeInner
      omega
    have hcoreAtTranslated : Symbolic.InfiniteFactorAt fixedWord core
        (start + offset) := by
      simpa [hposition] using hcoreAt
    have hfinite : Symbolic.FiniteFactorAt factor core offset :=
      Symbolic.finiteFactorAt_of_nested_infiniteFactorAt
        hfactor hcoreAtTranslated hwithin
    have hleftBound : cut firstCut - start ≤
        maximumImageLength_b9 substitution := by
      by_cases hfirstZero : firstCut = 0
      · rw [hfirstZero]
        change fixedPointImageCut_b9 substitution fixedWord 0 - start ≤ _
        rw [fixedPointImageCut_zero_b9]
        simp
      · obtain ⟨previous, hfirstSucc⟩ :=
          Nat.exists_eq_succ_of_ne_zero hfirstZero
        have hpreviousNot : ¬ start ≤ cut previous := by
          intro hle
          exact (Nat.find_min startWitness (by omega)) hle
        have hpreviousLt : cut previous < start := Nat.lt_of_not_ge hpreviousNot
        have hcutStep : cut firstCut = cut previous +
            (substitution (fixedWord previous)).length := by
          change fixedPointImageCut_b9 substitution fixedWord firstCut = _
          rw [hfirstSucc]
          simpa [Nat.succ_eq_add_one] using
            fixedPointImageCut_succ_b9 substitution fixedWord previous
        exact (by omega : cut firstCut - start ≤
          (substitution (fixedWord previous)).length) |>.trans
            (imageLength_le_maximumImageLength_b9 substitution _)
    have hrightBound : endPosition - cut innerLast ≤
        maximumImageLength_b9 substitution := by
      have hcutStep : cut lastCut = cut innerLast +
          (substitution (fixedWord innerLast)).length := by
        change fixedPointImageCut_b9 substitution fixedWord lastCut = _
        rw [← hinnerLast]
        simpa [Nat.succ_eq_add_one] using
          fixedPointImageCut_succ_b9 substitution fixedWord innerLast
      exact (by omega : endPosition - cut innerLast ≤
        (substitution (fixedWord innerLast)).length) |>.trans
          (imageLength_le_maximumImageLength_b9 substitution _)
    have hresidual : factor.length - core.length =
        (cut firstCut - start) + (endPosition - cut innerLast) := by
      simp only [endPosition]
      rw [hcoreLength]
      have hcutOrder : cut firstCut ≤ cut innerLast :=
        (fixedPointImageCut_strictMono_b9 substitution fixedWord).monotone
          hfirstLeInner
      omega
    refine ⟨{
      middle := middle
      core_isInfix := by simpa [core] using hfinite.isInfix
      residual_length_le := ?_ }⟩
    change factor.length - core.length ≤
      2 * maximumImageLength_b9 substitution
    rw [hresidual]
    omega

private theorem count_sub_count_le_length_sub_length_of_infix_b9
    {alphabet : Type*} [DecidableEq alphabet]
    {core whole : Symbolic.Word alphabet} (letter : alphabet)
    (hinfix : core <:+: whole) :
    whole.count letter - core.count letter ≤
      whole.length - core.length := by
  rcases hinfix with ⟨left, right, rfl⟩
  simp only [List.count_append, List.length_append]
  have hleft : left.count letter ≤ left.length := List.count_le_length
  have hright : right.count letter ≤ right.length := List.count_le_length
  omega

private theorem count_le_of_infix_b9
    {alphabet : Type*} [DecidableEq alphabet]
    {core whole : Symbolic.Word alphabet} (letter : alphabet)
    (hinfix : core <:+: whole) :
    core.count letter ≤ whole.count letter := by
  rcases hinfix with ⟨left, right, rfl⟩
  simp only [List.count_append]
  omega

private theorem count_mapWord_b9 {alphabet : Type*}
    [Fintype alphabet] [DecidableEq alphabet]
    (substitution : Symbolic.Substitution alphabet)
    (word : Symbolic.Word alphabet) (letter : alphabet) :
    (substitution.mapWord word).count letter =
      ∑ sourceLetter : alphabet,
        (substitution sourceLetter).count letter * word.count sourceLetter := by
  induction word with
  | nil => simp
  | cons head tail ih =>
      rw [Symbolic.Substitution.mapWord_cons, List.count_append, ih]
      calc
        (substitution head).count letter +
              ∑ sourceLetter : alphabet,
                (substitution sourceLetter).count letter *
                  tail.count sourceLetter =
            (∑ sourceLetter : alphabet,
                if sourceLetter = head then
                  (substitution sourceLetter).count letter else 0) +
              ∑ sourceLetter : alphabet,
                (substitution sourceLetter).count letter *
                  tail.count sourceLetter := by simp
        _ = ∑ sourceLetter : alphabet,
              ((if sourceLetter = head then
                  (substitution sourceLetter).count letter else 0) +
                (substitution sourceLetter).count letter *
                  tail.count sourceLetter) := Finset.sum_add_distrib.symm
        _ = ∑ sourceLetter : alphabet,
              (substitution sourceLetter).count letter *
                (head :: tail).count sourceLetter := by
          apply Finset.sum_congr rfl
          intro sourceLetter _
          by_cases heq : sourceLetter = head
          · subst sourceLetter
            simp [Nat.mul_add, Nat.add_comm]
          · simp [heq, Ne.symm heq]

/-- C4.2: the long `Theta` image is a complete earlier-source image plus a
uniformly bounded prefix/suffix error matrix. -/
structure DurandBoundaryErrorMatrixDecomposition
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    (difference : DurandPowerEquationDifference equations) where
  threshold : Nat
  threshold_pos : 0 < threshold
  quotientMatrix : Nat → Matrix (Fin rank) (Fin rank) Nat
  errorMatrix : Nat → Matrix (Fin rank) (Fin rank) Nat
  decomposition : ∀ multiplier, threshold ≤ multiplier →
    ((returnDecoderSubstitution input.decomposition).power
        (multiplier * difference.refinementDifference)).incidenceMatrix =
      (source.power
          (equations.sourcePower difference.earlierIndex)).incidenceMatrix *
        quotientMatrix multiplier + errorMatrix multiplier
  errorEntryBound : Nat
  errorEntryBound_pos : 0 < errorEntryBound
  error_entry_le : ∀ multiplier row column,
    errorMatrix multiplier row column ≤ errorEntryBound

/-- Leaf C4.2: recognizability and the long-return lower bound give the
complete-image plus bounded-boundary-error matrix decomposition. -/
theorem durand_has_boundedBoundaryErrorDecomposition
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    (difference : DurandPowerEquationDifference equations) :
    Nonempty (DurandBoundaryErrorMatrixDecomposition difference) := by
  classical
  let theta := returnDecoderSubstitution input.decomposition
  let sourceExponent := equations.sourcePower difference.earlierIndex
  let tau := source.power sourceExponent
  have hsourceExponent : 0 < sourceExponent := by
    have hmono : equations.sourcePower 0 ≤
        equations.sourcePower difference.earlierIndex :=
      equations.sourcePower_strictMono.monotone (Nat.zero_le _)
    exact equations.sourcePower_zero_pos.trans_le hmono
  have htauFixed : tau.IsFixedPoint word := by
    exact Symbolic.Substitution.isFixedPoint_power
      input.source_fixed hsourceExponent
  let occurrence : Fin rank → Nat := fun letter =>
    Classical.choose (input.decomposition.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin rank,
      word (occurrence letter) = letter := by
    intro letter
    rw [← input.derived_eq]
    exact Classical.choose_spec
      (input.decomposition.every_letter_occurs letter)
  let targetWord : Nat → Fin rank → Symbolic.Word (Fin rank) :=
    fun multiplier letter =>
      theta.power (multiplier * difference.refinementDifference) letter
  let targetStart : Nat → Fin rank → Nat := fun multiplier letter =>
    (theta.iterateWord (multiplier * difference.refinementDifference)
      (word.take (occurrence letter))).length
  have htargetAt : ∀ multiplier letter,
      Symbolic.InfiniteFactorAt word (targetWord multiplier letter)
        (targetStart multiplier letter) := by
    intro multiplier letter
    have htake : (word.drop (occurrence letter)).take 1 = [letter] := by
      rw [Stream'.take_succ]
      simp [Stream'.get, hoccurrence]
    have hraw := Symbolic.Substitution.iterateWord_drop_take_at_fixed
      input.decoder_fixed
      (multiplier * difference.refinementDifference)
      (occurrence letter) 1
    rw [htake] at hraw
    change Symbolic.InfiniteFactorAt word
      (theta.iterateLetter
        (multiplier * difference.refinementDifference) letter)
      (targetStart multiplier letter) at hraw
    simpa [targetWord, Symbolic.Substitution.power_apply] using hraw
  have htargetNonempty : ∀ multiplier letter,
      targetWord multiplier letter ≠ [] := by
    intro multiplier letter
    exact (theta.power
      (multiplier * difference.refinementDifference)).image_ne_nil letter
  let core : ∀ multiplier letter,
      FixedPointFactorCore_b9 tau (targetWord multiplier letter) :=
    fun multiplier letter => Classical.choice
      (fixedPointFactor_has_boundedCore_b9 htauFixed
        (htargetAt multiplier letter)
        (htargetNonempty multiplier letter))
  let quotientMatrix : Nat → Matrix (Fin rank) (Fin rank) Nat :=
    fun multiplier row column =>
      (core multiplier column).middle.count row
  let errorMatrix : Nat → Matrix (Fin rank) (Fin rank) Nat :=
    fun multiplier row column =>
      (targetWord multiplier column).count row -
        (tau.mapWord (core multiplier column).middle).count row
  let errorEntryBound : Nat :=
    2 * maximumImageLength_b9 tau + 1
  refine ⟨{
    threshold := 1
    threshold_pos := by omega
    quotientMatrix := quotientMatrix
    errorMatrix := errorMatrix
    decomposition := ?_
    errorEntryBound := errorEntryBound
    errorEntryBound_pos := by simp [errorEntryBound]
    error_entry_le := ?_ }⟩
  · intro multiplier _hthreshold
    ext row column
    change (targetWord multiplier column).count row =
      (∑ middleLetter : Fin rank,
        (tau middleLetter).count row *
          (core multiplier column).middle.count middleLetter) +
        ((targetWord multiplier column).count row -
          (tau.mapWord (core multiplier column).middle).count row)
    rw [← count_mapWord_b9]
    exact (Nat.add_sub_of_le
      (count_le_of_infix_b9 row
        (core multiplier column).core_isInfix)).symm
  · intro multiplier row column
    change (targetWord multiplier column).count row -
        (tau.mapWord (core multiplier column).middle).count row ≤
      errorEntryBound
    have hcountResidual :=
      count_sub_count_le_length_sub_length_of_infix_b9 row
        (core multiplier column).core_isInfix
    exact hcountResidual.trans
      ((core multiplier column).residual_length_le.trans (by
        simp only [errorEntryBound]
        omega))

/-- C4.3: two distinct large multipliers have exactly the same finite error
matrix. -/
structure DurandRepeatedBoundaryErrors
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    {difference : DurandPowerEquationDifference equations}
    (boundary : DurandBoundaryErrorMatrixDecomposition difference) where
  earlierMultiplier : Nat
  laterMultiplier : Nat
  threshold_le_earlier : boundary.threshold ≤ earlierMultiplier
  multiplier_lt : earlierMultiplier < laterMultiplier
  error_eq : boundary.errorMatrix earlierMultiplier =
    boundary.errorMatrix laterMultiplier

/-- Leaf C4.3: finite pigeonhole for uniformly bounded finite matrices. -/
theorem durand_boundedBoundaryErrors_have_repetition
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    {difference : DurandPowerEquationDifference equations}
    (boundary : DurandBoundaryErrorMatrixDecomposition difference) :
    Nonempty (DurandRepeatedBoundaryErrors boundary) := by
  classical
  let multiplier : Nat → Nat := fun index => boundary.threshold + index
  let encode : Nat → Fin rank → Fin rank →
      Fin (boundary.errorEntryBound + 1) := fun index row column =>
    ⟨boundary.errorMatrix (multiplier index) row column,
      by
        exact Nat.lt_succ_of_le
          (boundary.error_entry_le (multiplier index) row column)⟩
  obtain ⟨left, right, hne, hcode⟩ :=
    Finite.exists_ne_map_eq_of_infinite encode
  have herror : boundary.errorMatrix (multiplier left) =
      boundary.errorMatrix (multiplier right) := by
    ext row column
    have hentry := congrFun (congrFun hcode row) column
    exact congrArg Fin.val hentry
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨{
      earlierMultiplier := multiplier left
      laterMultiplier := multiplier right
      threshold_le_earlier := by simp [multiplier]
      multiplier_lt := by simp [multiplier, hlt]
      error_eq := herror }⟩
  · exact ⟨{
      earlierMultiplier := multiplier right
      laterMultiplier := multiplier left
      threshold_le_earlier := by simp [multiplier]
      multiplier_lt := by simp [multiplier, hgt]
      error_eq := herror.symm }⟩

/-- A complex number is a root of unity when one positive power is one. -/
def IsComplexRootOfUnity (value : ℂ) : Prop :=
  ∃ order : Nat, 0 < order ∧ value ^ order = 1

/-- C4.4 / reverse half of Durand Proposition 11: bounded equal boundary
errors return every nonzero non-root-of-unity `Theta` eigenvalue to the
source-power difference. -/
structure DurandReverseEigenvalueInclusion
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    {difference : DurandPowerEquationDifference equations}
    {boundary : DurandBoundaryErrorMatrixDecomposition difference}
    (_repeatedErrors : DurandRepeatedBoundaryErrors boundary) where
  includes : ∀ eigenvalue : ℂ, eigenvalue ≠ 0 →
    ¬ IsComplexRootOfUnity eigenvalue →
    IsComplexEigenvalue
        ((returnDecoderSubstitution input.decomposition).power
          difference.refinementDifference).incidenceMatrix eigenvalue →
      IsComplexEigenvalue
        (source.power difference.sourceDifference).incidenceMatrix eigenvalue

/-- Leaf C4.4: subtract the two equal-error decompositions and apply a left
eigenvector; roots of unity are exactly the exceptional cancellation case. -/
theorem durand_boundaryErrorRepetition_gives_reverseInclusion
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    {difference : DurandPowerEquationDifference equations}
    {boundary : DurandBoundaryErrorMatrixDecomposition difference}
    (repeatedErrors : DurandRepeatedBoundaryErrors boundary) :
    Nonempty (DurandReverseEigenvalueInclusion repeatedErrors) := by
  classical
  let thetaMatrix :=
    (returnDecoderSubstitution input.decomposition).incidenceMatrix
  let sourceMatrix := source.incidenceMatrix
  let action := thetaMatrix ^ difference.refinementDifference
  let prefixMatrix := sourceMatrix ^
    (equations.sourcePower difference.earlierIndex)
  let sourceAction := sourceMatrix ^ difference.sourceDifference
  have hintertwinesNat : action * prefixMatrix = prefixMatrix * sourceAction := by
    have hraw := durand_powerDifference_incidence_intertwining difference
    rw [Symbolic.Substitution.incidenceMatrix_power,
      Symbolic.Substitution.incidenceMatrix_power,
      Symbolic.Substitution.incidenceMatrix_power] at hraw
    simpa [action, prefixMatrix, sourceAction, thetaMatrix, sourceMatrix] using hraw
  have hintertwinesComplex := congrArg complexNatMatrix hintertwinesNat
  simp only [complexNatMatrix_mul] at hintertwinesComplex
  have hintertwinesTranspose :
      (complexNatMatrix sourceAction).transpose *
          (complexNatMatrix prefixMatrix).transpose =
        (complexNatMatrix prefixMatrix).transpose *
          (complexNatMatrix action).transpose := by
    have htranspose := congrArg Matrix.transpose hintertwinesComplex
    simpa only [Matrix.transpose_mul] using htranspose.symm
  have boundaryComplex (multiplier : Nat)
      (hthreshold : boundary.threshold ≤ multiplier) :
      (complexNatMatrix action) ^ multiplier =
        complexNatMatrix prefixMatrix *
            complexNatMatrix (boundary.quotientMatrix multiplier) +
          complexNatMatrix (boundary.errorMatrix multiplier) := by
    have hnat := boundary.decomposition multiplier hthreshold
    rw [Symbolic.Substitution.incidenceMatrix_power,
      Symbolic.Substitution.incidenceMatrix_power] at hnat
    have hcomplex := congrArg complexNatMatrix hnat
    simp only [complexNatMatrix_mul, complexNatMatrix_add,
      complexNatMatrix_pow] at hcomplex
    change
      (complexNatMatrix
          (thetaMatrix ^ difference.refinementDifference)) ^ multiplier =
        complexNatMatrix
              (sourceMatrix ^
                equations.sourcePower difference.earlierIndex) *
            complexNatMatrix (boundary.quotientMatrix multiplier) +
          complexNatMatrix (boundary.errorMatrix multiplier)
    rw [complexNatMatrix_pow, complexNatMatrix_pow, ← pow_mul,
      Nat.mul_comm difference.refinementDifference multiplier]
    exact hcomplex
  refine ⟨{ includes := ?_ }⟩
  intro eigenvalue heigenvalue hnotRoot heigen
  rw [Symbolic.Substitution.incidenceMatrix_power] at heigen ⊢
  have heigenAction : IsComplexEigenvalue action eigenvalue := by
    simpa [action, thetaMatrix] using heigen
  have heigenTranspose :
      IsComplexEigenvalue action.transpose eigenvalue :=
    (isComplexEigenvalue_transpose_iff_b9 action eigenvalue).2 heigenAction
  rcases heigenTranspose with ⟨leftVector, hleftVector, heigenLeft⟩
  have heigenLeftFunction :
      (complexNatMatrix action).transpose.mulVec leftVector =
        eigenvalue • leftVector := by
    funext row
    have hrow := heigenLeft row
    simpa [complexNatMatrix, Matrix.mulVec, Pi.smul_apply] using hrow
  let transported :=
    (complexNatMatrix prefixMatrix).transpose.mulVec leftVector
  have htransported : transported ≠ 0 := by
    intro hzero
    have action_on_error (multiplier : Nat)
        (hthreshold : boundary.threshold ≤ multiplier) :
        (eigenvalue ^ multiplier) • leftVector =
          (complexNatMatrix (boundary.errorMatrix multiplier)).transpose.mulVec
            leftVector := by
      have hboundaryTranspose :=
        congrArg Matrix.transpose (boundaryComplex multiplier hthreshold)
      simp only [Matrix.transpose_add, Matrix.transpose_mul] at hboundaryTranspose
      have hpower := complexMatrix_eigenvector_power
        (complexNatMatrix action).transpose leftVector eigenvalue
        heigenLeftFunction multiplier
      calc
        (eigenvalue ^ multiplier) • leftVector =
            (((complexNatMatrix action).transpose) ^ multiplier).mulVec
              leftVector := hpower.symm
        _ = ((complexNatMatrix action) ^ multiplier).transpose.mulVec
              leftVector := by rw [Matrix.transpose_pow]
        _ = (((complexNatMatrix
                (boundary.quotientMatrix multiplier)).transpose *
                (complexNatMatrix prefixMatrix).transpose) +
              (complexNatMatrix
                (boundary.errorMatrix multiplier)).transpose).mulVec
                leftVector := by rw [hboundaryTranspose]
        _ = (complexNatMatrix
                (boundary.errorMatrix multiplier)).transpose.mulVec
              leftVector := by
            rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
            change (complexNatMatrix
                (boundary.quotientMatrix multiplier)).transpose.mulVec
                  transported +
                (complexNatMatrix
                  (boundary.errorMatrix multiplier)).transpose.mulVec
                    leftVector = _
            rw [hzero, Matrix.mulVec_zero, zero_add]
    have hearlierAction := action_on_error
      repeatedErrors.earlierMultiplier
      repeatedErrors.threshold_le_earlier
    have hthresholdLater :
        boundary.threshold ≤ repeatedErrors.laterMultiplier :=
      le_trans repeatedErrors.threshold_le_earlier
        (Nat.le_of_lt repeatedErrors.multiplier_lt)
    have hlaterAction := action_on_error
      repeatedErrors.laterMultiplier hthresholdLater
    have herrorTranspose :
        (complexNatMatrix
            (boundary.errorMatrix repeatedErrors.earlierMultiplier)).transpose =
          (complexNatMatrix
            (boundary.errorMatrix repeatedErrors.laterMultiplier)).transpose := by
      rw [repeatedErrors.error_eq]
    have hsmul :
        (eigenvalue ^ repeatedErrors.earlierMultiplier) • leftVector =
          (eigenvalue ^ repeatedErrors.laterMultiplier) • leftVector := by
      calc
        (eigenvalue ^ repeatedErrors.earlierMultiplier) • leftVector =
            (complexNatMatrix
              (boundary.errorMatrix
                repeatedErrors.earlierMultiplier)).transpose.mulVec
                  leftVector := hearlierAction
        _ = (complexNatMatrix
              (boundary.errorMatrix
                repeatedErrors.laterMultiplier)).transpose.mulVec
                  leftVector := by rw [herrorTranspose]
        _ = (eigenvalue ^ repeatedErrors.laterMultiplier) • leftVector :=
          hlaterAction.symm
    have hexistsCoordinate : ∃ row, leftVector row ≠ 0 := by
      by_contra hnone
      apply hleftVector
      funext row
      by_contra hrow
      exact hnone ⟨row, hrow⟩
    obtain ⟨coordinate, hcoordinate⟩ := hexistsCoordinate
    have hscalar :
        eigenvalue ^ repeatedErrors.earlierMultiplier =
          eigenvalue ^ repeatedErrors.laterMultiplier := by
      apply mul_right_cancel₀ hcoordinate
      simpa [Pi.smul_apply, smul_eq_mul] using congrFun hsmul coordinate
    have hadd :
        repeatedErrors.earlierMultiplier +
            (repeatedErrors.laterMultiplier -
              repeatedErrors.earlierMultiplier) =
          repeatedErrors.laterMultiplier :=
      Nat.add_sub_of_le (Nat.le_of_lt repeatedErrors.multiplier_lt)
    have hrootPower :
        eigenvalue ^ (repeatedErrors.laterMultiplier -
          repeatedErrors.earlierMultiplier) = 1 := by
      apply mul_left_cancel₀
        (pow_ne_zero repeatedErrors.earlierMultiplier heigenvalue)
      calc
        eigenvalue ^ repeatedErrors.earlierMultiplier *
              eigenvalue ^ (repeatedErrors.laterMultiplier -
                repeatedErrors.earlierMultiplier) =
            eigenvalue ^ repeatedErrors.laterMultiplier := by
              rw [← pow_add, hadd]
        _ = eigenvalue ^ repeatedErrors.earlierMultiplier := hscalar.symm
        _ = eigenvalue ^ repeatedErrors.earlierMultiplier * 1 := by simp
    apply hnotRoot
    exact ⟨repeatedErrors.laterMultiplier -
        repeatedErrors.earlierMultiplier,
      Nat.sub_pos_of_lt repeatedErrors.multiplier_lt, hrootPower⟩
  have htransportedEigen :
      (complexNatMatrix sourceAction).transpose.mulVec transported =
        eigenvalue • transported := by
    calc
      (complexNatMatrix sourceAction).transpose.mulVec transported =
          ((complexNatMatrix sourceAction).transpose *
            (complexNatMatrix prefixMatrix).transpose).mulVec leftVector := by
              rw [← Matrix.mulVec_mulVec]
      _ = ((complexNatMatrix prefixMatrix).transpose *
            (complexNatMatrix action).transpose).mulVec leftVector := by
              rw [hintertwinesTranspose]
      _ = (complexNatMatrix prefixMatrix).transpose.mulVec
            ((complexNatMatrix action).transpose.mulVec leftVector) := by
              rw [Matrix.mulVec_mulVec]
      _ = (complexNatMatrix prefixMatrix).transpose.mulVec
            (eigenvalue • leftVector) := by rw [heigenLeftFunction]
      _ = eigenvalue • transported := by rw [Matrix.mulVec_smul]
  have heigenSourceTranspose :
      IsComplexEigenvalue sourceAction.transpose eigenvalue := by
    refine ⟨transported, htransported, ?_⟩
    intro row
    have hrow := congrFun htransportedEigen row
    simpa [complexNatMatrix, Matrix.mulVec, Pi.smul_apply] using hrow
  exact (isComplexEigenvalue_transpose_iff_b9
    sourceAction eigenvalue).1 heigenSourceTranspose

/-- Complete one-source Proposition-11 eigenvalue data. -/
structure DurandOneSourceProposition11Data
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    (difference : DurandPowerEquationDifference equations) where
  forward : DurandForwardEigenvalueInclusion difference
  boundary : DurandBoundaryErrorMatrixDecomposition difference
  repeatedErrors : DurandRepeatedBoundaryErrors boundary
  reverse : DurandReverseEigenvalueInclusion repeatedErrors

/-- Proved C4.5 assembly of both eigenvalue inclusions. -/
theorem durandPowerDifference_has_proposition11EigenvalueData
    {rank : Nat} {word : Symbolic.InfiniteWord (Fin rank)}
    {source : Symbolic.Substitution (Fin rank)}
    {input : DurandProposition10Input word source}
    {equations : DurandPowerEquationFamily input}
    (difference : DurandPowerEquationDifference equations) :
    Nonempty (DurandOneSourceProposition11Data difference) := by
  obtain ⟨forward⟩ := durand_first_nonzeroEigenvalue_inclusion difference
  obtain ⟨boundary⟩ :=
    durand_has_boundedBoundaryErrorDecomposition difference
  obtain ⟨repeatedErrors⟩ :=
    durand_boundedBoundaryErrors_have_repetition boundary
  obtain ⟨reverse⟩ :=
    durand_boundaryErrorRepetition_gives_reverseInclusion repeatedErrors
  exact ⟨{
    forward := forward
    boundary := boundary
    repeatedErrors := repeatedErrors
    reverse := reverse }⟩

private theorem wordMetricLength_smul_b9 {alphabet : Type*}
    (scalar : Real) (length : alphabet → Real)
    (word : Symbolic.Word alphabet) :
    wordMetricLength (fun letter => scalar * length letter) word =
      scalar * wordMetricLength length word := by
  induction word with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      change scalar * length head +
          wordMetricLength (fun letter => scalar * length letter) tail =
        scalar * (length head + wordMetricLength length tail)
      rw [ih]
      ring

private theorem wordMetricLength_append_b9 {alphabet : Type*}
    (length : alphabet → Real) (left right : Symbolic.Word alphabet) :
    wordMetricLength length (left ++ right) =
      wordMetricLength length left + wordMetricLength length right := by
  simp [wordMetricLength]

private theorem wordMetricLength_mapWord_of_scales_b9
    {alphabet : Type*} {substitution : Symbolic.Substitution alphabet}
    {length : alphabet → Real} {scale : Real}
    (hscales : SubstitutionScalesLetterLengths substitution length scale)
    (word : Symbolic.Word alphabet) :
    wordMetricLength length (substitution.mapWord word) =
      scale * wordMetricLength length word := by
  induction word with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      rw [Symbolic.Substitution.mapWord_cons]
      rw [wordMetricLength_append_b9, hscales head, ih]
      change scale * length head + scale * wordMetricLength length tail =
        scale * (length head + wordMetricLength length tail)
      ring

private theorem wordMetricLength_substitutionImageMetric_b9
    {alphabet : Type*} (substitution : Symbolic.Substitution alphabet)
    (length : alphabet → Real) (word : Symbolic.Word alphabet) :
    wordMetricLength
        (fun letter => wordMetricLength length (substitution letter)) word =
      wordMetricLength length (substitution.mapWord word) := by
  induction word with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      rw [Symbolic.Substitution.mapWord_cons,
        wordMetricLength_append_b9]
      change wordMetricLength length (substitution head) +
          wordMetricLength
            (fun letter => wordMetricLength length (substitution letter)) tail =
        wordMetricLength length (substitution head) +
          wordMetricLength length (substitution.mapWord tail)
      rw [ih]

private theorem wordMetricLength_mono_b9
    {alphabet : Type*} {left right : alphabet → Real}
    (hle : ∀ letter, left letter ≤ right letter)
    (word : Symbolic.Word alphabet) :
    wordMetricLength left word ≤ wordMetricLength right word := by
  induction word with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      change left head + wordMetricLength left tail ≤
        right head + wordMetricLength right tail
      exact add_le_add (hle head) ih

private theorem wordMetricLength_lt_of_pointwise_le_of_mem_lt_b9
    {alphabet : Type*} {left right : alphabet → Real}
    (hle : ∀ letter, left letter ≤ right letter)
    {strictLetter : alphabet} {word : Symbolic.Word alphabet}
    (hmem : strictLetter ∈ word)
    (hstrict : left strictLetter < right strictLetter) :
    wordMetricLength left word < wordMetricLength right word := by
  induction word with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      change left head + wordMetricLength left tail <
        right head + wordMetricLength right tail
      rcases hmem with rfl | htail
      · linarith [wordMetricLength_mono_b9 hle tail]
      · have htailLt := ih htail
        linarith [hle head]

/-- A primitive substitution has only one strictly positive length vector at
a fixed scale, up to a positive scalar.  The proof uses a maximal coordinate
ratio and one all-positive substitution power. -/
private theorem primitive_scalingMetrics_proportional_b9
    {alphabet : Type*} [Fintype alphabet] [DecidableEq alphabet]
    [Nonempty alphabet]
    (substitution : Symbolic.Substitution alphabet)
    (hprimitive : IsPrimitiveSubstitution substitution)
    (left right : alphabet → Real) (scale : Real)
    (hleftPositive : ∀ letter, 0 < left letter)
    (hrightPositive : ∀ letter, 0 < right letter)
    (hleftScales :
      SubstitutionScalesLetterLengths substitution left scale)
    (hrightScales :
      SubstitutionScalesLetterLengths substitution right scale) :
    ∃ scalar : Real, 0 < scalar ∧
      ∀ letter, right letter = scalar * left letter := by
  classical
  obtain ⟨depth, hdepthPositive, hcontains⟩ := hprimitive
  obtain ⟨pivot, _hpivotMem, hpivotMax⟩ :=
    Finset.univ.exists_max_image
      (fun letter => right letter / left letter) Finset.univ_nonempty
  let scalar : Real := right pivot / left pivot
  have hscalarPositive : 0 < scalar := by
    exact div_pos (hrightPositive pivot) (hleftPositive pivot)
  have hpointwise : ∀ letter, right letter ≤ scalar * left letter := by
    intro letter
    exact (div_le_iff₀ (hleftPositive letter)).mp
      (hpivotMax letter (Finset.mem_univ letter))
  have hpivot : right pivot = scalar * left pivot := by
    simp only [scalar]
    field_simp [(ne_of_gt (hleftPositive pivot))]
  have hleftPower := substitution.scalesLetterLengths_power
    hleftScales depth pivot
  have hrightPower := substitution.scalesLetterLengths_power
    hrightScales depth pivot
  simp only [Symbolic.Substitution.power_apply] at hleftPower hrightPower
  refine ⟨scalar, hscalarPositive, ?_⟩
  intro letter
  apply le_antisymm (hpointwise letter)
  by_contra hnot
  have hstrict : right letter < scalar * left letter := by
    exact lt_of_not_ge hnot
  have hwordStrict :
      wordMetricLength right
          (substitution.iterateLetter depth pivot) <
        wordMetricLength (fun other => scalar * left other)
          (substitution.iterateLetter depth pivot) :=
    wordMetricLength_lt_of_pointwise_le_of_mem_lt_b9
      hpointwise (hcontains pivot letter) hstrict
  have hwordEqual :
      wordMetricLength right
          (substitution.iterateLetter depth pivot) =
        wordMetricLength (fun other => scalar * left other)
          (substitution.iterateLetter depth pivot) := by
    rw [hrightPower, wordMetricLength_smul_b9, hleftPower, hpivot]
    ring
  exact (ne_of_lt hwordStrict) hwordEqual

private theorem real_gt_one_not_complexRootOfUnity_b9
    {value : Real} (hvalue : 1 < value) :
    ¬ IsComplexRootOfUnity (value : ℂ) := by
  rintro ⟨order, horder, hpower⟩
  have hrealPower : value ^ order = 1 := by
    apply Complex.ofReal_injective
    simpa using hpower
  have honeLt : 1 < value ^ order :=
    one_lt_pow₀ hvalue horder.ne'
  linarith

/-- C4.6: Perron specialization of the two one-source eigenvalue comparisons
against their common primitive `Theta`. -/
structure DurandTwoSourcePerronSpecialization
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {system : DurandCommonDerivedSystem refinements}
    {equations : DurandTwoSourcePowerEquationData system}
    {leftDifference : DurandPowerEquationDifference equations.left}
    {rightDifference : DurandPowerEquationDifference equations.right}
    (_leftData : DurandOneSourceProposition11Data leftDifference)
    (_rightData : DurandOneSourceProposition11Data rightDifference) where
  thetaGrowth : Real
  thetaGrowth_gt_one : 1 < thetaGrowth
  thetaDominant : IsDominantEigenvalue
    (returnDecoderSubstitution system.decomposition).incidenceMatrix thetaGrowth
  left_growth_eq :
    ((a ^ family.infrastructure.left.exponent) ^ system.commonPower) ^
        leftDifference.sourceDifference =
      thetaGrowth ^ leftDifference.refinementDifference
  right_growth_eq :
    ((b ^ family.infrastructure.right.exponent) ^ system.commonPower) ^
        rightDifference.sourceDifference =
      thetaGrowth ^ rightDifference.refinementDifference

/-- Leaf C4.6: primitive Perron dominance removes the zero/root-of-unity
exceptions and identifies the positive powered growths on both sides. -/
theorem durand_twoSourceEigenvalueData_perronSpecialization
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {system : DurandCommonDerivedSystem refinements}
    {equations : DurandTwoSourcePowerEquationData system}
    {leftDifference : DurandPowerEquationDifference equations.left}
    {rightDifference : DurandPowerEquationDifference equations.right}
    (leftData : DurandOneSourceProposition11Data leftDifference)
    (rightData : DurandOneSourceProposition11Data rightDifference) :
    Nonempty (DurandTwoSourcePerronSpecialization leftData rightData) := by
  classical
  let selectedDecomposition :=
    family.infrastructure.decompositions.decomposition system.selectedLevel
  let theta := returnDecoderSubstitution system.decomposition
  let leftSource :=
    (family.infrastructure.left.substitution system.selectedLevel).power
      system.commonPower
  let metric : Fin
      (family.infrastructure.decompositions.rank system.selectedLevel) → Real :=
    fun letter => wordMetricLength data.letterLength
      (selectedDecomposition.blocks letter)
  letI : Nonempty (Fin
      (family.infrastructure.decompositions.rank system.selectedLevel)) :=
    ⟨⟨0, selectedDecomposition.rank_pos⟩⟩
  have hmetricPositive : ∀ letter, 0 < metric letter := by
    exact (family.infrastructure.left.factorization
      system.selectedLevel).returnMetric_pos
        data.letterLength data.letterLength_pos
  have horiginalScales : SubstitutionScalesLetterLengths
      (data.substitutionA.power input.powered.powerA)
      data.letterLength (a ^ input.powered.powerA) :=
    data.substitutionA.scalesLetterLengths_power
      data.imageMetricA input.powered.powerA
  have hbaseScales : SubstitutionScalesLetterLengths
      (family.infrastructure.left.substitution system.selectedLevel)
      metric (a ^ input.powered.powerA) := by
    exact (family.infrastructure.left.factorization
      system.selectedLevel).scalesReturnMetric horiginalScales
  have hsourceScales : SubstitutionScalesLetterLengths leftSource metric
      ((a ^ input.powered.powerA) ^ system.commonPower) := by
    exact (family.infrastructure.left.substitution
      system.selectedLevel).scalesLetterLengths_power
        hbaseScales system.commonPower
  have hwordCommutes : ∀ letter,
      theta.mapWord (leftSource letter) =
        leftSource.mapWord (theta letter) := by
    intro letter
    have hfactorImage : system.leftInduced.factor letter =
        leftSource letter := by
      change system.leftInduced.substitution letter = leftSource letter
      rw [system.left_induced_eq]
    change (leftSource letter).flatMap system.decomposition.blocks =
      leftSource.mapWord (system.decomposition.blocks letter)
    rw [← hfactorImage]
    exact system.leftInduced.factor_decodes letter
  let thetaMetric : Fin
      (family.infrastructure.decompositions.rank system.selectedLevel) → Real :=
    fun letter => wordMetricLength metric (theta letter)
  have hthetaMetricPositive : ∀ letter, 0 < thetaMetric letter := by
    intro letter
    exact Symbolic.Substitution.wordMetricLength_pos_of_ne_nil
      metric hmetricPositive (theta.image_ne_nil letter)
  have hthetaMetricScalesSource : SubstitutionScalesLetterLengths
      leftSource thetaMetric
      ((a ^ input.powered.powerA) ^ system.commonPower) := by
    intro letter
    change wordMetricLength thetaMetric (leftSource letter) =
      ((a ^ input.powered.powerA) ^ system.commonPower) *
        thetaMetric letter
    rw [show wordMetricLength thetaMetric (leftSource letter) =
        wordMetricLength metric (theta.mapWord (leftSource letter)) by
      exact wordMetricLength_substitutionImageMetric_b9
        theta metric (leftSource letter)]
    rw [hwordCommutes]
    exact wordMetricLength_mapWord_of_scales_b9
      hsourceScales (theta letter)
  obtain ⟨thetaGrowth, hthetaGrowthPositive, hthetaScales⟩ :=
    primitive_scalingMetrics_proportional_b9 leftSource
      system.left_power_primitive metric thetaMetric
      ((a ^ input.powered.powerA) ^ system.commonPower)
      hmetricPositive hthetaMetricPositive hsourceScales
      hthetaMetricScalesSource
  have hthetaScale : SubstitutionScalesLetterLengths
      theta metric thetaGrowth := by
    intro letter
    simpa [thetaMetric] using hthetaScales letter
  have hthetaGrowth_gt_one : 1 < thetaGrowth := by
    obtain ⟨tail, htailNonempty, hseedImage⟩ :=
      system.decoder_prolongable
    have htailPositive : 0 < wordMetricLength metric tail :=
      Symbolic.Substitution.wordMetricLength_pos_of_ne_nil
        metric hmetricPositive htailNonempty
    have hseedScale := hthetaScale system.seed
    rw [hseedImage] at hseedScale
    change metric system.seed + wordMetricLength metric tail =
      thetaGrowth * metric system.seed at hseedScale
    nlinarith [hmetricPositive system.seed]
  have hthetaLengthEigen :=
    substitution_metric_lengths_give_incidence_identity
      hmetricPositive hthetaScale
  have hthetaEigenTranspose : NatMatrixEigenvectorEquation
      theta.incidenceMatrix.transpose metric thetaGrowth := by
    intro sourceLetter
    simpa [NatMatrixEigenvectorEquation, incidenceTransposeMul] using
      hthetaLengthEigen.2 sourceLetter
  have hthetaDominantTranspose : IsDominantEigenvalue
      theta.incidenceMatrix.transpose thetaGrowth :=
    positive_eigenvector_isDominant theta.incidenceMatrix.transpose
      metric thetaGrowth hmetricPositive hthetaEigenTranspose
  have hthetaDominant : IsDominantEigenvalue
      theta.incidenceMatrix thetaGrowth :=
    (dominantEigenvalue_transpose_iff
      theta.incidenceMatrix thetaGrowth).mp hthetaDominantTranspose
  let leftGrowth : Real :=
    (a ^ family.infrastructure.left.exponent) ^ system.commonPower
  let rightGrowth : Real :=
    (b ^ family.infrastructure.right.exponent) ^ system.commonPower
  have hleftGrowth_gt_one : 1 < leftGrowth := by
    exact one_lt_pow₀
      (one_lt_pow₀ data.one_lt_a
        family.infrastructure.left.exponent_pos.ne')
      system.commonPower_pos.ne'
  have hrightGrowth_gt_one : 1 < rightGrowth := by
    exact one_lt_pow₀
      (one_lt_pow₀ data.one_lt_b
        family.infrastructure.right.exponent_pos.ne')
      system.commonPower_pos.ne'
  have hleftSourcePowerDominant : IsDominantEigenvalue
      ((leftSource.power leftDifference.sourceDifference).incidenceMatrix)
      (leftGrowth ^ leftDifference.sourceDifference) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    exact dominantEigenvalue_pow leftSource.incidenceMatrix leftGrowth
      (by simpa [leftSource, leftGrowth] using system.left_power_dominant)
      leftDifference.sourceDifference_pos
  have hrightSourcePowerDominant : IsDominantEigenvalue
      ((((family.infrastructure.right.substitution
        system.selectedLevel).power system.commonPower).power
          rightDifference.sourceDifference).incidenceMatrix)
      (rightGrowth ^ rightDifference.sourceDifference) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    exact dominantEigenvalue_pow
      ((family.infrastructure.right.substitution
        system.selectedLevel).power system.commonPower).incidenceMatrix
      rightGrowth
      (by simpa [rightGrowth] using system.right_power_dominant)
      rightDifference.sourceDifference_pos
  have hleftThetaPowerDominant : IsDominantEigenvalue
      ((theta.power leftDifference.refinementDifference).incidenceMatrix)
      (thetaGrowth ^ leftDifference.refinementDifference) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    exact dominantEigenvalue_pow theta.incidenceMatrix thetaGrowth
      hthetaDominant leftDifference.refinementDifference_pos
  have hrightThetaPowerDominant : IsDominantEigenvalue
      ((theta.power rightDifference.refinementDifference).incidenceMatrix)
      (thetaGrowth ^ rightDifference.refinementDifference) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    exact dominantEigenvalue_pow theta.incidenceMatrix thetaGrowth
      hthetaDominant rightDifference.refinementDifference_pos
  have hleftSourcePowerPositive :
      0 < leftGrowth ^ leftDifference.sourceDifference :=
    pow_pos (lt_trans (by norm_num) hleftGrowth_gt_one) _
  have hrightSourcePowerPositive :
      0 < rightGrowth ^ rightDifference.sourceDifference :=
    pow_pos (lt_trans (by norm_num) hrightGrowth_gt_one) _
  have hleftThetaPower_gt_one :
      1 < thetaGrowth ^ leftDifference.refinementDifference :=
    one_lt_pow₀ hthetaGrowth_gt_one
      leftDifference.refinementDifference_pos.ne'
  have hrightThetaPower_gt_one :
      1 < thetaGrowth ^ rightDifference.refinementDifference :=
    one_lt_pow₀ hthetaGrowth_gt_one
      rightDifference.refinementDifference_pos.ne'
  have hleftForwardEigen : IsComplexEigenvalue
      ((theta.power leftDifference.refinementDifference).incidenceMatrix)
      ((leftGrowth ^ leftDifference.sourceDifference : Real) : ℂ) := by
    exact leftData.forward.includes _
      (by exact_mod_cast (ne_of_gt hleftSourcePowerPositive))
      (by simpa [leftSource, theta] using hleftSourcePowerDominant.1)
  have hrightForwardEigen : IsComplexEigenvalue
      ((theta.power rightDifference.refinementDifference).incidenceMatrix)
      ((rightGrowth ^ rightDifference.sourceDifference : Real) : ℂ) := by
    exact rightData.forward.includes _
      (by exact_mod_cast (ne_of_gt hrightSourcePowerPositive))
      (by simpa [theta] using hrightSourcePowerDominant.1)
  have hleftForwardLe :
      leftGrowth ^ leftDifference.sourceDifference ≤
        thetaGrowth ^ leftDifference.refinementDifference := by
    have hbound := hleftThetaPowerDominant.2 _ hleftForwardEigen
    simpa [abs_of_pos (lt_trans (by norm_num) hleftGrowth_gt_one)]
      using hbound
  have hrightForwardLe :
      rightGrowth ^ rightDifference.sourceDifference ≤
        thetaGrowth ^ rightDifference.refinementDifference := by
    have hbound := hrightThetaPowerDominant.2 _ hrightForwardEigen
    simpa [abs_of_pos (lt_trans (by norm_num) hrightGrowth_gt_one)]
      using hbound
  have hleftReverseEigen : IsComplexEigenvalue
      (leftSource.power leftDifference.sourceDifference).incidenceMatrix
      ((thetaGrowth ^ leftDifference.refinementDifference : Real) : ℂ) := by
    exact leftData.reverse.includes _
      (by exact_mod_cast
        (ne_of_gt (lt_trans (by norm_num) hleftThetaPower_gt_one)))
      (real_gt_one_not_complexRootOfUnity_b9 hleftThetaPower_gt_one)
      (by simpa [theta] using hleftThetaPowerDominant.1)
  have hrightReverseEigen : IsComplexEigenvalue
      (((family.infrastructure.right.substitution
        system.selectedLevel).power system.commonPower).power
          rightDifference.sourceDifference).incidenceMatrix
      ((thetaGrowth ^ rightDifference.refinementDifference : Real) : ℂ) := by
    exact rightData.reverse.includes _
      (by exact_mod_cast
        (ne_of_gt (lt_trans (by norm_num) hrightThetaPower_gt_one)))
      (real_gt_one_not_complexRootOfUnity_b9 hrightThetaPower_gt_one)
      (by simpa [theta] using hrightThetaPowerDominant.1)
  have hleftReverseLe :
      thetaGrowth ^ leftDifference.refinementDifference ≤
        leftGrowth ^ leftDifference.sourceDifference := by
    have hbound := hleftSourcePowerDominant.2 _ hleftReverseEigen
    simpa [abs_of_pos hthetaGrowthPositive] using hbound
  have hrightReverseLe :
      thetaGrowth ^ rightDifference.refinementDifference ≤
        rightGrowth ^ rightDifference.sourceDifference := by
    have hbound := hrightSourcePowerDominant.2 _ hrightReverseEigen
    simpa [abs_of_pos hthetaGrowthPositive] using hbound
  exact ⟨{
    thetaGrowth := thetaGrowth
    thetaGrowth_gt_one := hthetaGrowth_gt_one
    thetaDominant := by simpa [theta] using hthetaDominant
    left_growth_eq := by
      simpa [leftGrowth] using le_antisymm hleftForwardLe hleftReverseLe
    right_growth_eq := by
      simpa [rightGrowth] using
        le_antisymm hrightForwardLe hrightReverseLe }⟩

/-- Proved C4.7 packaging into the public comparison record. -/
theorem durandPerronSpecialization_to_proposition11Comparison
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {system : DurandCommonDerivedSystem refinements}
    {equations : DurandTwoSourcePowerEquationData system}
    {leftDifference : DurandPowerEquationDifference equations.left}
    {rightDifference : DurandPowerEquationDifference equations.right}
    {leftData : DurandOneSourceProposition11Data leftDifference}
    {rightData : DurandOneSourceProposition11Data rightDifference}
    (specialization :
      DurandTwoSourcePerronSpecialization leftData rightData) :
    Nonempty (DurandProposition11Comparison equations) := by
  exact ⟨{
    leftEarlierIndex := leftDifference.earlierIndex
    leftLaterIndex := leftDifference.laterIndex
    leftIndex_lt := leftDifference.index_lt
    leftSourceDifference := leftDifference.sourceDifference
    leftSourceDifference_pos := leftDifference.sourceDifference_pos
    leftSourceDifference_eq := leftDifference.sourceDifference_eq
    leftRefinementDifference := leftDifference.refinementDifference
    leftRefinementDifference_pos := leftDifference.refinementDifference_pos
    leftRefinementDifference_eq := leftDifference.refinementDifference_eq
    rightEarlierIndex := rightDifference.earlierIndex
    rightLaterIndex := rightDifference.laterIndex
    rightIndex_lt := rightDifference.index_lt
    rightSourceDifference := rightDifference.sourceDifference
    rightSourceDifference_pos := rightDifference.sourceDifference_pos
    rightSourceDifference_eq := rightDifference.sourceDifference_eq
    rightRefinementDifference := rightDifference.refinementDifference
    rightRefinementDifference_pos := rightDifference.refinementDifference_pos
    rightRefinementDifference_eq := rightDifference.refinementDifference_eq
    thetaGrowth := specialization.thetaGrowth
    thetaGrowth_gt_one := specialization.thetaGrowth_gt_one
    thetaDominant := specialization.thetaDominant
    left_growth_eq := specialization.left_growth_eq
    right_growth_eq := specialization.right_growth_eq }⟩

/-- Proved C4 / Durand Proposition 11 aggregator: the two exact Proposition
10 equation families transfer nonzero spectra in both directions and hence
identify positive powers of the common Perron growth. -/
theorem durand_proposition11_spectralComparison
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {system : DurandCommonDerivedSystem refinements}
    (equations : DurandTwoSourcePowerEquationData system) :
    Nonempty (DurandProposition11Comparison equations) := by
  obtain ⟨leftDifference⟩ :=
    durandPowerEquationFamily_has_positiveDifference equations.left
  obtain ⟨rightDifference⟩ :=
    durandPowerEquationFamily_has_positiveDifference equations.right
  obtain ⟨leftData⟩ :=
    durandPowerDifference_has_proposition11EigenvalueData leftDifference
  obtain ⟨rightData⟩ :=
    durandPowerDifference_has_proposition11EigenvalueData rightDifference
  obtain ⟨specialization⟩ :=
    durand_twoSourceEigenvalueData_perronSpecialization leftData rightData
  exact durandPerronSpecialization_to_proposition11Comparison specialization

/-- Proved former-C5 arithmetic: eliminate the common `Theta` growth by
cross-multiplying the two positive refinement exponents. -/
theorem durandProposition11_forces_basePowerEquality
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} {data : CommonRayFixedWord A B K ray a b}
    {input : PrimitiveReturnComparisonInput data}
    {family : FiniteReturnSystemFamily input}
    {repeated : RepeatedReturnSystems family}
    {aligned : AlignedRepeatedReturnSystems repeated}
    {refinements : AlignedNestedIntertwiningData aligned}
    {system : DurandCommonDerivedSystem refinements}
    {equations : DurandTwoSourcePowerEquationData system}
    (comparison : DurandProposition11Comparison equations) :
    ∃ leftPower rightPower : Nat,
      0 < leftPower ∧ 0 < rightPower ∧ a ^ leftPower = b ^ rightPower := by
  let leftPower := family.infrastructure.left.exponent *
    system.commonPower * comparison.leftSourceDifference *
      comparison.rightRefinementDifference
  let rightPower := family.infrastructure.right.exponent *
    system.commonPower * comparison.rightSourceDifference *
      comparison.leftRefinementDifference
  have hleftPower : 0 < leftPower := by
    dsimp [leftPower]
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos family.infrastructure.left.exponent_pos
          system.commonPower_pos)
        comparison.leftSourceDifference_pos)
      comparison.rightRefinementDifference_pos
  have hrightPower : 0 < rightPower := by
    dsimp [rightPower]
    exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos family.infrastructure.right.exponent_pos
          system.commonPower_pos)
        comparison.rightSourceDifference_pos)
      comparison.leftRefinementDifference_pos
  have hleft := congrArg
    (fun value : Real => value ^ comparison.rightRefinementDifference)
    comparison.left_growth_eq
  have hright := congrArg
    (fun value : Real => value ^ comparison.leftRefinementDifference)
    comparison.right_growth_eq
  have htheta :
      (comparison.thetaGrowth ^ comparison.leftRefinementDifference) ^
          comparison.rightRefinementDifference =
        (comparison.thetaGrowth ^ comparison.rightRefinementDifference) ^
          comparison.leftRefinementDifference := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  refine ⟨leftPower, rightPower, hleftPower, hrightPower, ?_⟩
  have hcombined := hleft.trans (htheta.trans hright.symm)
  simpa only [← pow_mul, Nat.mul_assoc, leftPower, rightPower] using hcombined

/-- Proved C-stage aggregator.  If the recurrent language were not periodic,
the finite-return, simultaneous Durand-Lemma-12 system, Proposition-10
equation families, and Proposition-11 spectral comparison would produce
equal positive powers of `a` and `b`, contrary to base independence. -/
theorem primitive_twoScale_periodicRecurrentLanguage
    {A B : IntervalMap} {K : Finset I} {ray : Real → I}
    {a b : Real} (data : CommonRayFixedWord A B K ray a b)
    (primitiveA : IsPrimitiveSubstitution data.substitutionA)
    (primitiveB : IsPrimitiveSubstitution data.substitutionB)
    (powered : PoweredPerronData data) :
    Symbolic.HasPeriodicRecurrentLanguage data.word := by
  by_contra hnotPeriodicLanguage
  obtain ⟨input⟩ := primitiveCommonRay_has_returnComparisonInput
    data primitiveA primitiveB powered
  obtain ⟨family⟩ :=
    exists_finiteReturnSystemFamily input hnotPeriodicLanguage
  obtain ⟨repeated⟩ := finiteReturnSystemFamily_has_repetitions family
  obtain ⟨aligned⟩ := repeatedReturnSystems_have_commonAlignment repeated
  obtain ⟨refinements⟩ :=
    alignedReturnSystems_have_exactNestedIntertwinings aligned
  obtain ⟨system⟩ := construct_durandCommonDerivedSystem
    refinements hnotPeriodicLanguage
  obtain ⟨equations⟩ :=
    durandCommonSystem_has_twoPowerEquationFamilies system
  obtain ⟨comparison⟩ :=
    durand_proposition11_spectralComparison equations
  obtain ⟨leftPower, rightPower, hleftPower, hrightPower, hgrowth⟩ :=
    durandProposition11_forces_basePowerEquality comparison
  exact powered.base_independent leftPower rightPower
    hleftPower hrightPower hgrowth

/-- Proved primitive-Cobham aggregator: the checked linear-gap theorem
supplies syndeticity and the C0--C5 chain supplies the periodic recurrent
language. -/
theorem exactCoding_word_ultimatelyPeriodic
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    {E : PiecewiseLinearIrrationalExactSystem G}
    {M : PiecewiseLinearConstantSlopeSystem E}
    {K : PiecewiseLinearCommonMarkovPackage M}
    {rayData : RebuiltReturnedRayData M}
    {seedData : RebuiltRaySeedData K rayData}
    (coding : ExactCommonRayCodingData K rayData seedData) :
    Symbolic.IsUltimatelyPeriodic coding.common.word := by
  have hsyndetic := exactCoding_word_recurrentFactorsSyndetic coding
  obtain ⟨powered⟩ := commonRay_has_poweredPerronData
    coding.common rayData.scales_independent
  apply periodicRecurrentLanguage_ultimatelyPeriodic hsyndetic
  exact primitive_twoScale_periodicRecurrentLanguage coding.common
    (exactCoding_substitutionA_primitive coding)
    (exactCoding_substitutionB_primitive coding) powered

/-! ## Decode the periodic word back to geometry -/

/-- Once word periodicity is available, all remaining symbolic-to-metric,
tail-extension, exact-range, least-period, and scale-integrality steps are
already proved.  This theorem is a dependency-clean version of
`common_substitutions_produce_periodic_return_path` with periodicity supplied
as an argument instead of recomputed through the general Cobham boundary. -/
theorem periodic_commonRay_produces_returnPathPackage
    {A B R : IntervalMap} {K : Finset I} {ray : Real → I} {a b : Real}
    (data : CommonRayFixedWord A B K ray a b)
    (_hcomm : Commute A B)
    (hR : R = A ∘ B)
    (hexact : IsTopologicallyExact R)
    (hwordPeriodic : Symbolic.IsUltimatelyPeriodic data.word) :
    Nonempty (PeriodicReturnPathPackage A B a b) := by
  obtain ⟨P, hmetricPeriod⟩ :=
    ultimate_word_period_gives_eventual_metric_period
      data.letterLength_pos data.itinerary hwordPeriodic
  obtain ⟨path, hext⟩ :=
    exists_periodic_tail_extension data.ray_unit_speed.1 hmetricPeriod
  have hproductScale : 1 < a * b := by
    nlinarith [data.one_lt_a, data.one_lt_b]
  have hproductReturn : DilationReturnsOnRay ray (a * b) R :=
    product_dilation_returns_on_ray (lt_trans zero_lt_one data.one_lt_b)
      data.ray_returnA data.ray_returnB hR
  have hrange : Set.range path = Set.univ :=
    periodic_tail_range_eq_univ_of_exact data.ray_unit_speed hproductScale
      hext hproductReturn hexact
  have hsurjective : Function.Surjective path := by
    intro y
    have hy : y ∈ Set.range path := by rw [hrange]; exact Set.mem_univ y
    exact hy
  have hnonconstant : ¬(∀ x y : Real, path x = path y) := by
    intro hconstant
    obtain ⟨x, hx⟩ := hsurjective leftEndpoint
    obtain ⟨y, hy⟩ := hsurjective rightEndpoint
    have hends : leftEndpoint = rightEndpoint := by
      rw [← hx, ← hy]
      exact hconstant x y
    exact (by simp [leftEndpoint, rightEndpoint] :
      leftEndpoint ≠ rightEndpoint) hends
  obtain ⟨P0, hleast⟩ := periodic_nonconstant_path_has_least_period
    hext.2.1 hnonconstant hext.1 hext.2.2.1
  have hAeventual : EventuallyDilationReturns path a A :=
    periodic_extension_eventually_returns
      (lt_trans zero_lt_one data.one_lt_a) hext data.ray_returnA
  have hBeventual : EventuallyDilationReturns path b B :=
    periodic_extension_eventually_returns
      (lt_trans zero_lt_one data.one_lt_b) hext data.ray_returnB
  obtain ⟨m, hm, haNatural⟩ :=
    expanding_return_scale_is_natural hleast data.one_lt_a hAeventual
  obtain ⟨n, hn, hbNatural⟩ :=
    expanding_return_scale_is_natural hleast data.one_lt_b hBeventual
  have hAglobal : DilationReturns path a A :=
    eventual_return_global_of_natural_scale hleast
      ⟨m, by omega, haNatural⟩ hAeventual
  have hBglobal : DilationReturns path b B :=
    eventual_return_global_of_natural_scale hleast
      ⟨n, by omega, hbNatural⟩ hBeventual
  exact ⟨{
    path := path
    period := P0
    path_spec := ⟨hext.2.1, hsurjective, hleast,
      periodic_tail_extension_unit_speed data.ray_unit_speed hext⟩
    scaleA_natural := ⟨m, hm, haNatural⟩
    scaleB_natural := ⟨n, hn, hbNatural⟩
    returnA := hAglobal
    returnB := hBglobal }⟩

end PiecewiseLinearB9Scratch

end

end CommutingInterval
