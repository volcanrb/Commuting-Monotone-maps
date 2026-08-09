import CommutingInterval.PiecewiseMonotoneEigen
import CommutingInterval.PiecewiseMonotoneReduction
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.Separation.Hausdorff

/-!
# The common distribution quotient and piecewise-linear descent

This file isolates the quotient stage of the direct piecewise-monotone proof.
Its input is a common atomless transfer-eigenprobability for two commuting
finite-piece maps.  The cumulative-distribution coordinate is allowed to have
nontrivial interval fibres.  Both maps descend through those fibres, and the
descents are finite-piece piecewise linear with slopes of absolute value equal
to the two transfer scales.
-/

noncomputable section

namespace CommutingInterval

open Function Set MeasureTheory Topology
open scoped ENNReal Topology

/-! ## 1. Probability-CDF coordinate data -/

/-- The exact positive input needed by the common quotient construction. -/
structure SimultaneousTransferEigenProbability
    (P Q : IntervalMap) where
  finitePiece_P : FinitePieceMonotone P
  finitePiece_Q : FinitePieceMonotone Q
  commute : Commute P Q
  partitionP : MonotonicityPartition P
  partitionQ : MonotonicityPartition Q
  measure : Measure I
  probability : measure Set.univ = 1
  noAtoms : ∀ x : I, measure {x} = 0
  scaleP : ℝ
  scaleQ : ℝ
  scaleP_pos : 0 < scaleP
  scaleQ_pos : 0 < scaleQ
  transferP_eigen :
    transferMeasure P partitionP measure noAtoms =
      ENNReal.ofReal scaleP • measure
  transferQ_eigen :
    transferMeasure Q partitionQ measure noAtoms =
      ENNReal.ofReal scaleQ • measure

/-- Forget the complex spectral construction while retaining exactly the
positive data used by the quotient. -/
theorem simultaneousTransferEigenProbability_of_variation
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    {Z : JointTransferEigenvectorData D}
    (V : SimultaneousVariationData Z) :
    Nonempty (SimultaneousTransferEigenProbability P Q) := by
  exact ⟨{
    finitePiece_P := D.finitePiece_P
    finitePiece_Q := D.finitePiece_Q
    commute := D.commute
    partitionP := D.partitionP
    partitionQ := D.partitionQ
    measure := V.measure
    probability := V.probability
    noAtoms := V.noAtoms
    scaleP := V.scaleP
    scaleQ := V.scaleQ
    scaleP_pos := V.scaleP_pos
    scaleQ_pos := V.scaleQ_pos
    transferP_eigen := V.transferP_eigen
    transferQ_eigen := V.transferQ_eigen }⟩

/-- The cumulative distribution coordinate of a measure on the unit
interval, formed by taking the real CDF of its pushforward to `ℝ`. -/
noncomputable def cdfCoordinate (μ : Measure I) : IntervalMap :=
  fun x =>
    ⟨ProbabilityTheory.cdf (μ.map Subtype.val) (x : ℝ),
      ⟨ProbabilityTheory.cdf_nonneg (μ.map Subtype.val) (x : ℝ),
        ProbabilityTheory.cdf_le_one (μ.map Subtype.val) (x : ℝ)⟩⟩

theorem cdfCoordinate_interval_mass
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0)
    {x y : I} (hxy : x ≤ y) :
    μ (Set.Icc x y) = ENNReal.ofReal
      ((cdfCoordinate μ y : ℝ) - (cdfCoordinate μ x : ℝ)) := by
  classical
  letI : IsProbabilityMeasure μ := ⟨hprob⟩
  let ν : Measure ℝ := μ.map Subtype.val
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : NoAtoms ν := by
    refine ⟨fun r => ?_⟩
    change (μ.map Subtype.val) {r} = 0
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton r)]
    by_cases hne : ((Subtype.val : I → ℝ) ⁻¹' {r}).Nonempty
    · obtain ⟨u, hu⟩ := hne
      have heq : (Subtype.val : I → ℝ) ⁻¹' {r} = {u} := by
        ext v
        constructor
        · intro hv
          have hvr : (v : ℝ) = r := hv
          have hur : (u : ℝ) = r := hu
          exact Subtype.ext (hvr.trans hur.symm)
        · rintro rfl
          exact hu
      rw [heq]
      exact hμ u
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
  let F : ℝ → ℝ := ProbabilityTheory.cdf ν
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro r
    apply (ProbabilityTheory.monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim.mpr
    rw [show Function.rightLim F r = F r by
      exact StieltjesFunction.rightLim_eq (ProbabilityTheory.cdf ν) r]
    have hmeasure : (ProbabilityTheory.cdf ν).measure {r} = 0 := by
      rw [ProbabilityTheory.measure_cdf]
      exact measure_singleton r
    rw [StieltjesFunction.measure_singleton] at hmeasure
    have hle : F r - Function.leftLim F r ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hmeasure
    have hge : 0 ≤ F r - Function.leftLim F r :=
      sub_nonneg.mpr ((ProbabilityTheory.monotone_cdf ν).leftLim_le le_rfl)
    linarith
  calc
    μ (Set.Icc x y) = ν (Set.Icc (x : ℝ) (y : ℝ)) := by
      change μ (Set.Icc x y) =
        (μ.map Subtype.val) (Set.Icc (x : ℝ) (y : ℝ))
      rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
      congr 1
    _ = (ProbabilityTheory.cdf ν).measure
        (Set.Icc (x : ℝ) (y : ℝ)) := by
      rw [ProbabilityTheory.measure_cdf]
    _ = ENNReal.ofReal
        (F y - Function.leftLim F (x : ℝ)) := by
      exact StieltjesFunction.measure_Icc _ _ _
    _ = ENNReal.ofReal (F y - F x) := by
      rw [hFcont.continuousAt.continuousWithinAt.leftLim_eq]
    _ = ENNReal.ofReal
        ((cdfCoordinate μ y : ℝ) - (cdfCoordinate μ x : ℝ)) := by
      rfl

theorem cdfCoordinate_continuous
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0) :
    Continuous (cdfCoordinate μ) := by
  classical
  letI : IsProbabilityMeasure μ := ⟨hprob⟩
  let ν : Measure ℝ := μ.map Subtype.val
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : NoAtoms ν := by
    refine ⟨fun r => ?_⟩
    change (μ.map Subtype.val) {r} = 0
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton r)]
    by_cases hne : ((Subtype.val : I → ℝ) ⁻¹' {r}).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have heq : (Subtype.val : I → ℝ) ⁻¹' {r} = {x} := by
        ext y
        constructor
        · intro hy
          have hyr : (y : ℝ) = r := hy
          have hxr : (x : ℝ) = r := hx
          exact Subtype.ext (hyr.trans hxr.symm)
        · rintro rfl
          exact hx
      rw [heq]
      exact hμ x
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
  let F : ℝ → ℝ := ProbabilityTheory.cdf ν
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro r
    apply (ProbabilityTheory.monotone_cdf ν).continuousAt_iff_leftLim_eq_rightLim.mpr
    rw [show Function.rightLim F r = F r by
      exact StieltjesFunction.rightLim_eq (ProbabilityTheory.cdf ν) r]
    have hmeasure : (ProbabilityTheory.cdf ν).measure {r} = 0 := by
      rw [ProbabilityTheory.measure_cdf]
      exact measure_singleton r
    rw [StieltjesFunction.measure_singleton] at hmeasure
    have hle : F r - Function.leftLim F r ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hmeasure
    have hge : 0 ≤ F r - Function.leftLim F r :=
      sub_nonneg.mpr ((ProbabilityTheory.monotone_cdf ν).leftLim_le le_rfl)
    linarith
  unfold cdfCoordinate
  exact (hFcont.comp continuous_subtype_val).subtype_mk _

theorem cdfCoordinate_monotone (μ : Measure I) :
    Monotone (cdfCoordinate μ) := by
  intro x y hxy
  exact ProbabilityTheory.monotone_cdf (μ.map Subtype.val) hxy

theorem cdfCoordinate_leftEndpoint
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0) :
    cdfCoordinate μ leftEndpoint = leftEndpoint := by
  letI : IsProbabilityMeasure μ := ⟨hprob⟩
  apply Subtype.ext
  change ProbabilityTheory.cdf (μ.map Subtype.val)
    (leftEndpoint : ℝ) = 0
  rw [ProbabilityTheory.unitInterval.cdf_eq_real μ leftEndpoint]
  have hsingle : Set.Icc (0 : I) leftEndpoint = {leftEndpoint} := by
    ext z
    constructor
    · intro hz
      exact Set.mem_singleton_iff.mpr
        (le_antisymm hz.2 z.property.1)
    · intro hz
      rw [Set.mem_singleton_iff.mp hz]
      exact ⟨le_rfl, le_rfl⟩
  rw [hsingle, measureReal_def, hμ]
  simp

theorem cdfCoordinate_rightEndpoint
    (μ : Measure I) (hprob : μ Set.univ = 1) :
    cdfCoordinate μ rightEndpoint = rightEndpoint := by
  letI : IsProbabilityMeasure μ := ⟨hprob⟩
  apply Subtype.ext
  change ProbabilityTheory.cdf (μ.map Subtype.val)
    (rightEndpoint : ℝ) = 1
  rw [ProbabilityTheory.unitInterval.cdf_eq_real μ rightEndpoint]
  have hunit : Set.Icc (0 : I) rightEndpoint = Set.univ := by
    ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      exact ⟨z.property.1, z.property.2⟩
  rw [hunit, measureReal_def, hprob]
  simp

theorem cdfCoordinate_surjective
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0) :
    Function.Surjective (cdfCoordinate μ) := by
  intro y
  have hy : y ∈ Set.Icc (cdfCoordinate μ leftEndpoint)
      (cdfCoordinate μ rightEndpoint) := by
    rw [cdfCoordinate_leftEndpoint μ hprob hμ,
      cdfCoordinate_rightEndpoint μ hprob]
    exact y.property
  rcases intermediate_value_Icc
      (show leftEndpoint ≤ rightEndpoint by
        simp [leftEndpoint, rightEndpoint])
      (cdfCoordinate_continuous μ hprob hμ).continuousOn hy with
    ⟨x, _hx, hxy⟩
  exact ⟨x, hxy⟩

/-- A packaged continuous monotone onto distribution coordinate. -/
structure DistributionQuotientData (μ : Measure I) where
  coordinate : IntervalMap
  interval_mass : ∀ {x y : I}, x ≤ y →
    μ (Set.Icc x y) = ENNReal.ofReal
      ((coordinate y : ℝ) - (coordinate x : ℝ))
  continuous_coordinate : Continuous coordinate
  monotone_coordinate : Monotone coordinate
  left_endpoint : coordinate leftEndpoint = leftEndpoint
  right_endpoint : coordinate rightEndpoint = rightEndpoint
  surjective_coordinate : Function.Surjective coordinate

/-- Package the canonical CDF coordinate and its elementary properties. -/
noncomputable def canonicalDistributionQuotientData
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0) : DistributionQuotientData μ where
  coordinate := cdfCoordinate μ
  interval_mass := cdfCoordinate_interval_mass μ hprob hμ
  continuous_coordinate := cdfCoordinate_continuous μ hprob hμ
  monotone_coordinate := cdfCoordinate_monotone μ
  left_endpoint := cdfCoordinate_leftEndpoint μ hprob hμ
  right_endpoint := cdfCoordinate_rightEndpoint μ hprob
  surjective_coordinate := cdfCoordinate_surjective μ hprob hμ

/-! ## 2. Assigned-cell and closed-cell scaling -/

/-- The assigned-cell scaling theorem remains valid on the underlying closed
cell: the only possible discrepancy is one endpoint, whose source and image
are null for an atomless measure. -/
theorem measure_image_eq_of_transferEigen_on_closedCell
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    (q : PT.partition.LapIndex) {E : Set I}
    (hE : MeasurableSet E) (hEq : E ⊆ q.closedCell) :
    μ (T '' E) = ENNReal.ofReal C * μ E := by
  classical
  let r : I := ⟨q.right, PT.partition.points_subset q.adjacent.2.1⟩
  let E' : Set I := E \ {r}
  have hE'meas : MeasurableSet E' := hE.diff (measurableSet_singleton r)
  have hE'sub : E' ⊆ q.assignedCell := by
    intro z hz
    have hzclosed := hEq hz.1
    by_cases hright : q.right = 1
    · simpa [RealPartition.LapIndex.assignedCell,
        RealPartition.LapIndex.closedCell, intervalCell, hright] using hzclosed
    · have hzIcc : (z : ℝ) ∈ Set.Icc q.left q.right := by
        simpa [RealPartition.LapIndex.closedCell, intervalCell] using hzclosed
      have hzne : (z : ℝ) ≠ q.right := by
        intro hzr
        apply hz.2
        exact Set.mem_singleton_iff.mpr (Subtype.ext hzr)
      have hzIco : (z : ℝ) ∈ Set.Ico q.left q.right :=
        ⟨hzIcc.1, lt_of_le_of_ne hzIcc.2 hzne⟩
      simpa [RealPartition.LapIndex.assignedCell, hright] using hzIco
  have hsource : μ E' = μ E := by
    exact measure_diff_null (hμ r)
  have himage_sub : T '' E' ⊆ T '' E :=
    Set.image_mono Set.diff_subset
  have himage_rest : (T '' E) \ {T r} ⊆ T '' E' := by
    rintro z ⟨⟨u, huE, huz⟩, hznot⟩
    refine ⟨u, ⟨huE, ?_⟩, huz⟩
    intro hur
    apply hznot
    rw [Set.mem_singleton_iff]
    have hur' : u = r := Set.mem_singleton_iff.mp hur
    simpa [hur'] using huz.symm
  have himage : μ (T '' E') = μ (T '' E) := by
    apply le_antisymm
    · exact measure_mono himage_sub
    · rw [← measure_diff_null (hμ (T r))]
      exact measure_mono himage_rest
  calc
    μ (T '' E) = μ (T '' E') := himage.symm
    _ = ENNReal.ofReal C * μ E' :=
      measure_image_eq_of_transferEigen_on_assignedCell
        PT μ hμ C heigen q hE'meas hE'sub
    _ = ENNReal.ofReal C * μ E := by rw [hsource]

/-! ## 3. Zero-coordinate intervals, fibre respect, and raw descent -/

/-- On one monotonicity cell, a zero-coordinate source interval has
zero-measure image. -/
theorem image_Icc_measure_zero_of_coordinate_eq_on_cell
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    (X : DistributionQuotientData μ)
    (q : PT.partition.LapIndex) {x y : I}
    (hxy : x ≤ y) (hx : x ∈ q.closedCell) (hy : y ∈ q.closedCell)
    (hcoord : X.coordinate x = X.coordinate y) :
    μ (T '' Set.Icc x y) = 0 := by
  have hsub : Set.Icc x y ⊆ q.closedCell := by
    intro z hz
    have hx' : (x : ℝ) ∈ Set.Icc q.left q.right := by
      simpa [RealPartition.LapIndex.closedCell, intervalCell] using hx
    have hy' : (y : ℝ) ∈ Set.Icc q.left q.right := by
      simpa [RealPartition.LapIndex.closedCell, intervalCell] using hy
    have hxz : (x : ℝ) ≤ (z : ℝ) := hz.1
    have hzy : (z : ℝ) ≤ (y : ℝ) := hz.2
    have hz' : (z : ℝ) ∈ Set.Icc q.left q.right :=
      ⟨hx'.1.trans hxz, hzy.trans hy'.2⟩
    simpa [RealPartition.LapIndex.closedCell, intervalCell] using hz'
  have hsource : μ (Set.Icc x y) = 0 := by
    rw [X.interval_mass hxy, hcoord]
    simp
  rw [measure_image_eq_of_transferEigen_on_closedCell
    PT μ hμ C heigen q measurableSet_Icc hsub, hsource, mul_zero]

/-- Consequently, the two endpoint images of such a subcell have equal
distribution coordinate. -/
theorem coordinate_image_eq_of_coordinate_eq_on_cell
    {T : IntervalMap} (hT : Continuous T)
    (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    (X : DistributionQuotientData μ)
    (q : PT.partition.LapIndex) {x y : I}
    (hxy : x ≤ y) (hx : x ∈ q.closedCell) (hy : y ∈ q.closedCell)
    (hcoord : X.coordinate x = X.coordinate y) :
    X.coordinate (T x) = X.coordinate (T y) := by
  have himagezero : μ (T '' Set.Icc x y) = 0 :=
    image_Icc_measure_zero_of_coordinate_eq_on_cell
      PT μ hμ C heigen X q hxy hx hy hcoord
  have htarget_coordinate {u v : I} (huv : u ≤ v)
      (hsub : Set.Icc u v ⊆ T '' Set.Icc x y) :
      X.coordinate u = X.coordinate v := by
    have htargetzero : μ (Set.Icc u v) = 0 :=
      measure_mono_null hsub himagezero
    have hmass := X.interval_mass huv
    rw [htargetzero] at hmass
    have hreverseReal : (X.coordinate v : ℝ) ≤ (X.coordinate u : ℝ) :=
      sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hmass.symm)
    apply le_antisymm
    · exact X.monotone_coordinate huv
    · exact hreverseReal
  by_cases hTxy : T x ≤ T y
  · apply htarget_coordinate hTxy
    intro z hz
    obtain ⟨u, hu, huz⟩ := intermediate_value_Icc hxy hT.continuousOn hz
    exact ⟨u, hu, huz⟩
  · have hTyx : T y ≤ T x := le_of_not_ge hTxy
    symm
    apply htarget_coordinate hTyx
    intro z hz
    obtain ⟨u, hu, huz⟩ := intermediate_value_Icc' hxy hT.continuousOn hz
    exact ⟨u, hu, huz⟩

/-- The closed-cell scaling laws on a finite lap cover upgrade the local
fibre-respect statement to arbitrary ordered source pairs. -/
private theorem coordinate_image_eq_of_coordinate_eq_global
    {T : IntervalMap} (hT : Continuous T)
    (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    (X : DistributionQuotientData μ) {x y : I}
    (hxy : x ≤ y) (hcoord : X.coordinate x = X.coordinate y) :
    X.coordinate (T x) = X.coordinate (T y) := by
  have hsource : μ (Set.Icc x y) = 0 := by
    rw [X.interval_mass hxy, hcoord]
    simp
  have hpiecezero (q : PT.partition.LapIndex) :
      μ (T '' (Set.Icc x y ∩ q.closedCell)) = 0 := by
    have hclosedmeas : MeasurableSet q.closedCell := by
      exact measurableSet_Icc.preimage measurable_subtype_coe
    rw [measure_image_eq_of_transferEigen_on_closedCell
      PT μ hμ C heigen q (measurableSet_Icc.inter hclosedmeas)
        inter_subset_right]
    have hinterzero : μ (Set.Icc x y ∩ q.closedCell) = 0 :=
      measure_mono_null inter_subset_left hsource
    rw [hinterzero, mul_zero]
  have hunionzero : μ (⋃ q : PT.partition.LapIndex,
      T '' (Set.Icc x y ∩ q.closedCell)) = 0 :=
    measure_iUnion_null hpiecezero
  have himagesub : T '' Set.Icc x y ⊆
      ⋃ q : PT.partition.LapIndex, T '' (Set.Icc x y ∩ q.closedCell) := by
    rintro z ⟨u, hu, rfl⟩
    have hucover : u ∈ ⋃ q : PT.partition.LapIndex, q.assignedCell := by
      rw [RealPartition.iUnion_assignedCells]
      exact Set.mem_univ u
    rcases Set.mem_iUnion.mp hucover with ⟨q, huq⟩
    apply Set.mem_iUnion.mpr
    exact ⟨q, u, ⟨hu, q.assignedCell_subset_closedCell huq⟩, rfl⟩
  have himagezero : μ (T '' Set.Icc x y) = 0 :=
    measure_mono_null himagesub hunionzero
  have htarget_coordinate {u v : I} (huv : u ≤ v)
      (hsub : Set.Icc u v ⊆ T '' Set.Icc x y) :
      X.coordinate u = X.coordinate v := by
    have htargetzero : μ (Set.Icc u v) = 0 :=
      measure_mono_null hsub himagezero
    have hmass := X.interval_mass huv
    rw [htargetzero] at hmass
    have hreverseReal : (X.coordinate v : ℝ) ≤ (X.coordinate u : ℝ) :=
      sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hmass.symm)
    apply le_antisymm
    · exact X.monotone_coordinate huv
    · exact hreverseReal
  by_cases hTxy : T x ≤ T y
  · apply htarget_coordinate hTxy
    exact intermediate_value_Icc hxy hT.continuousOn
  · have hTyx : T y ≤ T x := le_of_not_ge hTxy
    symm
    apply htarget_coordinate hTyx
    exact intermediate_value_Icc' hxy hT.continuousOn

/-- A map respects the fibres of a common coordinate. -/
def RespectsCoordinateFibres (θ T : IntervalMap) : Prop :=
  ∀ ⦃x y : I⦄, θ x = θ y → θ (T x) = θ (T y)

theorem SimultaneousTransferEigenProbability.respectsFibres_P
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    RespectsCoordinateFibres X.coordinate P := by
  intro x y hcoord
  rcases le_total x y with hxy | hyx
  · exact coordinate_image_eq_of_coordinate_eq_global
      E.finitePiece_P.continuous E.partitionP E.measure E.noAtoms
      E.scaleP E.transferP_eigen X hxy hcoord
  · exact (coordinate_image_eq_of_coordinate_eq_global
      E.finitePiece_P.continuous E.partitionP E.measure E.noAtoms
      E.scaleP E.transferP_eigen X hyx hcoord.symm).symm

theorem SimultaneousTransferEigenProbability.respectsFibres_Q
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    RespectsCoordinateFibres X.coordinate Q := by
  intro x y hcoord
  rcases le_total x y with hxy | hyx
  · exact coordinate_image_eq_of_coordinate_eq_global
      E.finitePiece_Q.continuous E.partitionQ E.measure E.noAtoms
      E.scaleQ E.transferQ_eigen X hxy hcoord
  · exact (coordinate_image_eq_of_coordinate_eq_global
      E.finitePiece_Q.continuous E.partitionQ E.measure E.noAtoms
      E.scaleQ E.transferQ_eigen X hyx hcoord.symm).symm

/-- The choice-defined descent through an arbitrary surjective coordinate. -/
noncomputable def coordinateDescent
    (θ : IntervalMap) (hθ : Function.Surjective θ)
    (T : IntervalMap) (_hrespect : RespectsCoordinateFibres θ T) :
    IntervalMap :=
  fun y => θ (T (Classical.choose (hθ y)))

/-- The pointwise factor identity `θ ∘ T = Tbar ∘ θ`. -/
def CoordinateIntertwines (θ T Tbar : IntervalMap) : Prop :=
  ∀ x : I, θ (T x) = Tbar (θ x)

/-! ## 4. Continuous descents, uniqueness, and commutation -/

theorem coordinateDescent_intertwines
    (θ : IntervalMap) (hθ : Function.Surjective θ)
    (T : IntervalMap) (hrespect : RespectsCoordinateFibres θ T) :
    CoordinateIntertwines θ T (coordinateDescent θ hθ T hrespect) := by
  intro x
  apply hrespect
  exact (Classical.choose_spec (hθ (θ x))).symm

theorem coordinateDescent_continuous
    (θ : IntervalMap) (hθsurj : Function.Surjective θ)
    (hθcont : Continuous θ) (T : IntervalMap) (hTcont : Continuous T)
    (hrespect : RespectsCoordinateFibres θ T) :
    Continuous (coordinateDescent θ hθsurj T hrespect) := by
  have hquot : IsQuotientMap θ :=
    IsQuotientMap.of_surjective_continuous hθsurj hθcont
  have hintertwines := coordinateDescent_intertwines θ hθsurj T hrespect
  have hcomp : coordinateDescent θ hθsurj T hrespect ∘ θ = θ ∘ T := by
    funext x
    exact (hintertwines x).symm
  apply hquot.continuous_iff.mpr
  rw [hcomp]
  exact hθcont.comp hTcont

theorem coordinateDescent_unique
    {θ T F G : IntervalMap} (hθ : Function.Surjective θ)
    (hF : CoordinateIntertwines θ T F)
    (hG : CoordinateIntertwines θ T G) :
    F = G := by
  funext y
  obtain ⟨x, rfl⟩ := hθ y
  exact (hF x).symm.trans (hG x)

theorem coordinateDescents_commute
    (θ : IntervalMap) (hθ : Function.Surjective θ)
    {P Q : IntervalMap}
    (hrespectP : RespectsCoordinateFibres θ P)
    (hrespectQ : RespectsCoordinateFibres θ Q)
    (hcommute : Commute P Q) :
    Commute (coordinateDescent θ hθ P hrespectP)
      (coordinateDescent θ hθ Q hrespectQ) := by
  intro y
  obtain ⟨x, rfl⟩ := hθ y
  let Pbar := coordinateDescent θ hθ P hrespectP
  let Qbar := coordinateDescent θ hθ Q hrespectQ
  have hP := coordinateDescent_intertwines θ hθ P hrespectP
  have hQ := coordinateDescent_intertwines θ hθ Q hrespectQ
  change Pbar (Qbar (θ x)) = Qbar (Pbar (θ x))
  calc
    Pbar (Qbar (θ x)) = Pbar (θ (Q x)) :=
      congrArg Pbar (hQ x).symm
    _ = θ (P (Q x)) := (hP (Q x)).symm
    _ = θ (Q (P x)) := congrArg θ (hcommute x)
    _ = Qbar (θ (P x)) := hQ (P x)
    _ = Qbar (Pbar (θ x)) := congrArg Qbar (hP x)

noncomputable def SimultaneousTransferEigenProbability.factorP
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) : IntervalMap :=
  coordinateDescent X.coordinate X.surjective_coordinate P
    (E.respectsFibres_P X)

noncomputable def SimultaneousTransferEigenProbability.factorQ
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) : IntervalMap :=
  coordinateDescent X.coordinate X.surjective_coordinate Q
    (E.respectsFibres_Q X)

theorem SimultaneousTransferEigenProbability.intertwines_factorP
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    CoordinateIntertwines X.coordinate P (E.factorP X) := by
  exact coordinateDescent_intertwines X.coordinate X.surjective_coordinate P
    (E.respectsFibres_P X)

theorem SimultaneousTransferEigenProbability.intertwines_factorQ
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    CoordinateIntertwines X.coordinate Q (E.factorQ X) := by
  exact coordinateDescent_intertwines X.coordinate X.surjective_coordinate Q
    (E.respectsFibres_Q X)

theorem SimultaneousTransferEigenProbability.continuous_factorP
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    Continuous (E.factorP X) := by
  exact coordinateDescent_continuous X.coordinate X.surjective_coordinate
    X.continuous_coordinate P E.finitePiece_P.continuous
    (E.respectsFibres_P X)

theorem SimultaneousTransferEigenProbability.continuous_factorQ
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    Continuous (E.factorQ X) := by
  exact coordinateDescent_continuous X.coordinate X.surjective_coordinate
    X.continuous_coordinate Q E.finitePiece_Q.continuous
    (E.respectsFibres_Q X)

theorem SimultaneousTransferEigenProbability.factors_commute
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    Commute (E.factorP X) (E.factorQ X) := by
  exact coordinateDescents_commute X.coordinate X.surjective_coordinate
    (E.respectsFibres_P X) (E.respectsFibres_Q X) E.commute

/-! ## 5. Image partitions and exact signed slopes -/

/-- The finite partition obtained by applying an endpoint-preserving
coordinate to all source vertices and removing duplicate images. -/
noncomputable def RealPartition.coordinateImage
    (p : RealPartition) (θ : IntervalMap)
    (hleft : θ leftEndpoint = leftEndpoint)
    (hright : θ rightEndpoint = rightEndpoint) : RealPartition := by
  exact
    { points := p.points.attach.image fun x =>
        (θ ⟨x.1, p.points_subset x.2⟩ : ℝ)
      zero_mem := by
        apply Finset.mem_image.mpr
        refine ⟨⟨0, p.zero_mem⟩, by simp, ?_⟩
        have h := congrArg Subtype.val hleft
        simpa [leftEndpoint] using h
      one_mem := by
        apply Finset.mem_image.mpr
        refine ⟨⟨1, p.one_mem⟩, by simp, ?_⟩
        have h := congrArg Subtype.val hright
        simpa [rightEndpoint] using h
      points_subset := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, _hx, rfl⟩
        exact (θ ⟨x.1, p.points_subset x.2⟩).property }

noncomputable def SimultaneousTransferEigenProbability.factorPartitionP
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) : RealPartition :=
  E.partitionP.partition.coordinateImage X.coordinate
    X.left_endpoint X.right_endpoint

noncomputable def SimultaneousTransferEigenProbability.factorPartitionQ
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) : RealPartition :=
  E.partitionQ.partition.coordinateImage X.coordinate
    X.left_endpoint X.right_endpoint

/-- An affine formula on `s` whose slope has prescribed absolute value. -/
def IsAffineWithAbsoluteSlopeOn
    (T : IntervalMap) (s : Set I) (scale : ℝ) : Prop :=
  ∃ m c : ℝ, |m| = scale ∧
    ∀ x ∈ s, (T x : ℝ) = m * (x : ℝ) + c

/-- Consecutive distinct coordinate-images of source vertices are the images
of the endpoints of an actual source cell. -/
private theorem exists_source_adjacent_of_coordinateImage_adjacent
    {μ : Measure I} (X : DistributionQuotientData μ) (p : RealPartition)
    {a b : ℝ}
    (hab : (p.coordinateImage X.coordinate
      X.left_endpoint X.right_endpoint).Adjacent a b) :
    ∃ c d : ℝ, ∃ hcd : p.Adjacent c d,
      (X.coordinate ⟨c, p.points_subset hcd.1⟩ : ℝ) = a ∧
      (X.coordinate ⟨d, p.points_subset hcd.2.1⟩ : ℝ) = b := by
  classical
  let pX := p.coordinateImage X.coordinate
    X.left_endpoint X.right_endpoint
  have haI : a ∈ I := pX.points_subset hab.1
  have hbI : b ∈ I := pX.points_subset hab.2.1
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith [hab.2.2.1]
  have hmb : m < b := by dsimp [m]; linarith [hab.2.2.1]
  have hmI : m ∈ I :=
    ⟨haI.1.trans ham.le, hmb.le.trans hbI.2⟩
  let mI : I := ⟨m, hmI⟩
  obtain ⟨x, hxcoord⟩ := X.surjective_coordinate mI
  have hxright : x < rightEndpoint := by
    by_contra h
    have hxEq : x = rightEndpoint :=
      le_antisymm x.property.2 (le_of_not_gt h)
    have hθrightm : X.coordinate rightEndpoint = mI := by
      simpa [hxEq] using hxcoord
    have hmright : mI = rightEndpoint :=
      hθrightm.symm.trans X.right_endpoint
    have hmreal : m = 1 := congrArg Subtype.val hmright
    linarith [hmb, hbI.2]
  obtain ⟨c, d, hcd, hcx, hxd⟩ := p.exists_adjacent_Ico hxright
  let cI : I := ⟨c, p.points_subset hcd.1⟩
  let dI : I := ⟨d, p.points_subset hcd.2.1⟩
  have hcIx : cI ≤ x := hcx
  have hxdI : x < dI := hxd
  have ha_mem : a ∈ p.points.attach.image (fun z =>
      (X.coordinate ⟨z.1, p.points_subset z.2⟩ : ℝ)) := by
    simpa [pX, RealPartition.coordinateImage] using hab.1
  have hb_mem : b ∈ p.points.attach.image (fun z =>
      (X.coordinate ⟨z.1, p.points_subset z.2⟩ : ℝ)) := by
    simpa [pX, RealPartition.coordinateImage] using hab.2.1
  rcases Finset.mem_image.mp ha_mem with ⟨av, _havmem, hθav⟩
  rcases Finset.mem_image.mp hb_mem with ⟨bv, _hbvmem, hθbv⟩
  let aI : I := ⟨av.1, p.points_subset av.2⟩
  let bI : I := ⟨bv.1, p.points_subset bv.2⟩
  have hθa : (X.coordinate aI : ℝ) = a := by
    simpa [aI] using hθav
  have hθb : (X.coordinate bI : ℝ) = b := by
    simpa [bI] using hθbv
  have haIx : aI < x := by
    apply lt_of_not_ge
    intro hxa
    have hmono := X.monotone_coordinate hxa
    change (X.coordinate x : ℝ) ≤ (X.coordinate aI : ℝ) at hmono
    have hma : m ≤ a := by
      simpa [mI, hxcoord, hθa] using hmono
    exact (not_le_of_gt ham) hma
  have hxbI : x < bI := by
    apply lt_of_not_ge
    intro hbx
    have hmono := X.monotone_coordinate hbx
    change (X.coordinate bI : ℝ) ≤ (X.coordinate x : ℝ) at hmono
    have hbm : b ≤ m := by
      simpa [mI, hxcoord, hθb] using hmono
    exact (not_le_of_gt hmb) hbm
  have haIc : aI ≤ cI := by
    apply le_of_not_gt
    intro hca
    exact hcd.2.2.2 (aI : ℝ) av.2
      ⟨hca, haIx.trans hxdI⟩
  have hdIb : dI ≤ bI := by
    apply le_of_not_gt
    intro hbd
    exact hcd.2.2.2 (bI : ℝ) bv.2
      ⟨hcIx.trans_lt hxbI, hbd⟩
  have hθc_mem : (X.coordinate cI : ℝ) ∈ pX.points := by
    apply Finset.mem_image.mpr
    refine ⟨⟨c, hcd.1⟩, by simp, ?_⟩
    rfl
  have hθd_mem : (X.coordinate dI : ℝ) ∈ pX.points := by
    apply Finset.mem_image.mpr
    refine ⟨⟨d, hcd.2.1⟩, by simp, ?_⟩
    rfl
  have ha_le_θc : a ≤ (X.coordinate cI : ℝ) := by
    have hmono := X.monotone_coordinate haIc
    change (X.coordinate aI : ℝ) ≤ (X.coordinate cI : ℝ) at hmono
    simpa [hθa] using hmono
  have hθc_le_a : (X.coordinate cI : ℝ) ≤ a := by
    apply le_of_not_gt
    intro haθc
    have hmono := X.monotone_coordinate hcIx
    have hθc_le_m : (X.coordinate cI : ℝ) ≤ m := by
      simpa [mI, hxcoord] using hmono
    exact hab.2.2.2 (X.coordinate cI : ℝ) hθc_mem
      ⟨haθc, hθc_le_m.trans_lt hmb⟩
  have hθd_le_b : (X.coordinate dI : ℝ) ≤ b := by
    have hmono := X.monotone_coordinate hdIb
    change (X.coordinate dI : ℝ) ≤ (X.coordinate bI : ℝ) at hmono
    simpa [hθb] using hmono
  have hb_le_θd : b ≤ (X.coordinate dI : ℝ) := by
    apply le_of_not_gt
    intro hθdb
    have hmono := X.monotone_coordinate hxdI.le
    have hm_le_θd : m ≤ (X.coordinate dI : ℝ) := by
      simpa [mI, hxcoord] using hmono
    exact hab.2.2.2 (X.coordinate dI : ℝ) hθd_mem
      ⟨ham.trans_le hm_le_θd, hθdb⟩
  exact ⟨c, d, hcd, le_antisymm hθc_le_a ha_le_θc,
    le_antisymm hθd_le_b hb_le_θd⟩

/-- Transfer scaling on a source cell becomes a signed affine formula on the
corresponding coordinate-image cell. -/
private theorem factor_affineOn_coordinateImage_cell
    {T Tbar : IntervalMap} (hT : Continuous T)
    (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ) (hC : 0 < C)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    (X : DistributionQuotientData μ)
    (hintertwines : CoordinateIntertwines X.coordinate T Tbar)
    {a b : ℝ}
    (hab : (PT.partition.coordinateImage X.coordinate
      X.left_endpoint X.right_endpoint).Adjacent a b) :
    IsAffineWithAbsoluteSlopeOn Tbar (intervalCell a b) C := by
  classical
  obtain ⟨c, d, hcd, hθc, hθd⟩ :=
    exists_source_adjacent_of_coordinateImage_adjacent X PT.partition hab
  have hpair : (c, d) ∈ PT.partition.adjacentPairs := by
    rw [RealPartition.adjacentPairs]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hcd.1, hcd.2.1⟩, hcd⟩
  let q : PT.partition.LapIndex := ⟨(c, d), hpair⟩
  let cI : I := ⟨c, PT.partition.points_subset hcd.1⟩
  let dI : I := ⟨d, PT.partition.points_subset hcd.2.1⟩
  have hcdI : cI ≤ dI := hcd.2.2.1.le
  have hweak := PT.weaklyMonotoneOn_cell hcd
  change MonotoneOn T (Set.Icc cI dI) ∨
    AntitoneOn T (Set.Icc cI dI) at hweak
  rcases hweak with hmono | hanti
  · refine ⟨C, (X.coordinate (T cI) : ℝ) - C * a,
      abs_of_pos hC, ?_⟩
    intro z hz
    have hzcoord : z ∈ Set.Icc (X.coordinate cI) (X.coordinate dI) := by
      constructor
      · change (X.coordinate cI : ℝ) ≤ (z : ℝ)
        simpa [cI] using hθc.trans_le hz.1
      · change (z : ℝ) ≤ (X.coordinate dI : ℝ)
        simpa [dI] using hz.2.trans hθd.symm.le
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc hcdI
      X.continuous_coordinate.continuousOn hzcoord
    have hcu : cI ≤ u := hu.1
    have hud : u ≤ dI := hu.2
    have hc_mem : cI ∈ Set.Icc cI dI := ⟨le_rfl, hcdI⟩
    have hTcu : T cI ≤ T u := hmono hc_mem hu hcu
    have hsmall : Set.Icc cI u ⊆ Set.Icc cI dI := by
      intro w hw
      exact ⟨hw.1, hw.2.trans hud⟩
    have himage : T '' Set.Icc cI u = Set.Icc (T cI) (T u) :=
      hT.continuousOn.image_Icc_of_monotoneOn hcu (hmono.mono hsmall)
    have hqsub : Set.Icc cI u ⊆ q.closedCell := by
      intro w hw
      change q.left ≤ (w : ℝ) ∧ (w : ℝ) ≤ q.right
      change c ≤ (w : ℝ) ∧ (w : ℝ) ≤ d
      exact ⟨hw.1, hw.2.trans hud⟩
    have hscale := measure_image_eq_of_transferEigen_on_closedCell
      PT μ hμ C heigen q measurableSet_Icc hqsub
    rw [himage, X.interval_mass hTcu, X.interval_mass hcu] at hscale
    have hsource_nonneg :
        0 ≤ (X.coordinate u : ℝ) - (X.coordinate cI : ℝ) := by
      apply sub_nonneg.mpr
      exact X.monotone_coordinate hcu
    have htarget_nonneg :
        0 ≤ (X.coordinate (T u) : ℝ) -
          (X.coordinate (T cI) : ℝ) := by
      apply sub_nonneg.mpr
      exact X.monotone_coordinate hTcu
    have hreal :
        (X.coordinate (T u) : ℝ) - (X.coordinate (T cI) : ℝ) =
          C * ((X.coordinate u : ℝ) - (X.coordinate cI : ℝ)) := by
      apply (ENNReal.ofReal_eq_ofReal_iff htarget_nonneg
        (mul_nonneg hC.le hsource_nonneg)).mp
      rw [ENNReal.ofReal_mul hC.le]
      exact hscale
    have hfactor : Tbar z = X.coordinate (T u) := by
      calc
        Tbar z = Tbar (X.coordinate u) := congrArg Tbar hθu.symm
        _ = X.coordinate (T u) := (hintertwines u).symm
    have hfactor_real := congrArg Subtype.val hfactor
    have hθu_real := congrArg Subtype.val hθu
    calc
      (Tbar z : ℝ) = (X.coordinate (T u) : ℝ) := hfactor_real
      _ = C * (X.coordinate u : ℝ) +
          ((X.coordinate (T cI) : ℝ) - C * a) := by
        have hθc' : (X.coordinate cI : ℝ) = a := by simpa [cI] using hθc
        nlinarith
      _ = C * (z : ℝ) +
          ((X.coordinate (T cI) : ℝ) - C * a) := by rw [hθu_real]
  · refine ⟨-C, (X.coordinate (T cI) : ℝ) + C * a,
      by rw [abs_neg, abs_of_pos hC], ?_⟩
    intro z hz
    have hzcoord : z ∈ Set.Icc (X.coordinate cI) (X.coordinate dI) := by
      constructor
      · change (X.coordinate cI : ℝ) ≤ (z : ℝ)
        simpa [cI] using hθc.trans_le hz.1
      · change (z : ℝ) ≤ (X.coordinate dI : ℝ)
        simpa [dI] using hz.2.trans hθd.symm.le
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc hcdI
      X.continuous_coordinate.continuousOn hzcoord
    have hcu : cI ≤ u := hu.1
    have hud : u ≤ dI := hu.2
    have hc_mem : cI ∈ Set.Icc cI dI := ⟨le_rfl, hcdI⟩
    have hTuc : T u ≤ T cI := hanti hc_mem hu hcu
    have hsmall : Set.Icc cI u ⊆ Set.Icc cI dI := by
      intro w hw
      exact ⟨hw.1, hw.2.trans hud⟩
    have himage : T '' Set.Icc cI u = Set.Icc (T u) (T cI) :=
      hT.continuousOn.image_Icc_of_antitoneOn hcu (hanti.mono hsmall)
    have hqsub : Set.Icc cI u ⊆ q.closedCell := by
      intro w hw
      change q.left ≤ (w : ℝ) ∧ (w : ℝ) ≤ q.right
      change c ≤ (w : ℝ) ∧ (w : ℝ) ≤ d
      exact ⟨hw.1, hw.2.trans hud⟩
    have hscale := measure_image_eq_of_transferEigen_on_closedCell
      PT μ hμ C heigen q measurableSet_Icc hqsub
    rw [himage, X.interval_mass hTuc, X.interval_mass hcu] at hscale
    have hsource_nonneg :
        0 ≤ (X.coordinate u : ℝ) - (X.coordinate cI : ℝ) := by
      apply sub_nonneg.mpr
      exact X.monotone_coordinate hcu
    have htarget_nonneg :
        0 ≤ (X.coordinate (T cI) : ℝ) -
          (X.coordinate (T u) : ℝ) := by
      apply sub_nonneg.mpr
      exact X.monotone_coordinate hTuc
    have hreal :
        (X.coordinate (T cI) : ℝ) - (X.coordinate (T u) : ℝ) =
          C * ((X.coordinate u : ℝ) - (X.coordinate cI : ℝ)) := by
      apply (ENNReal.ofReal_eq_ofReal_iff htarget_nonneg
        (mul_nonneg hC.le hsource_nonneg)).mp
      rw [ENNReal.ofReal_mul hC.le]
      exact hscale
    have hfactor : Tbar z = X.coordinate (T u) := by
      calc
        Tbar z = Tbar (X.coordinate u) := congrArg Tbar hθu.symm
        _ = X.coordinate (T u) := (hintertwines u).symm
    have hfactor_real := congrArg Subtype.val hfactor
    have hθu_real := congrArg Subtype.val hθu
    calc
      (Tbar z : ℝ) = (X.coordinate (T u) : ℝ) := hfactor_real
      _ = -C * (X.coordinate u : ℝ) +
          ((X.coordinate (T cI) : ℝ) + C * a) := by
        have hθc' : (X.coordinate cI : ℝ) = a := by simpa [cI] using hθc
        nlinarith
      _ = -C * (z : ℝ) +
          ((X.coordinate (T cI) : ℝ) + C * a) := by rw [hθu_real]

theorem SimultaneousTransferEigenProbability.factorP_affineOn_cell
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure)
    {a b : ℝ} (hab : (E.factorPartitionP X).Adjacent a b) :
    IsAffineWithAbsoluteSlopeOn (E.factorP X)
      (intervalCell a b) E.scaleP := by
  exact factor_affineOn_coordinateImage_cell
    E.finitePiece_P.continuous E.partitionP E.measure E.noAtoms
    E.scaleP E.scaleP_pos E.transferP_eigen X
    (E.intertwines_factorP X) hab

theorem SimultaneousTransferEigenProbability.factorQ_affineOn_cell
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure)
    {a b : ℝ} (hab : (E.factorPartitionQ X).Adjacent a b) :
    IsAffineWithAbsoluteSlopeOn (E.factorQ X)
      (intervalCell a b) E.scaleQ := by
  exact factor_affineOn_coordinateImage_cell
    E.finitePiece_Q.continuous E.partitionQ E.measure E.noAtoms
    E.scaleQ E.scaleQ_pos E.transferQ_eigen X
    (E.intertwines_factorQ X) hab

/-! ## 6. PL factors, plateau collapse, and fixed fibres -/

theorem SimultaneousTransferEigenProbability.finitePiecePL_factorP
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    FinitePiecePL (E.factorP X) := by
  refine ⟨E.continuous_factorP X, E.factorPartitionP X, ?_⟩
  intro a b hab
  rcases E.factorP_affineOn_cell X hab with ⟨m, c, _hm, hformula⟩
  exact ⟨m, c, hformula⟩

theorem SimultaneousTransferEigenProbability.finitePiecePL_factorQ
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) :
    FinitePiecePL (E.factorQ X) := by
  refine ⟨E.continuous_factorQ X, E.factorPartitionQ X, ?_⟩
  intro a b hab
  rcases E.factorQ_affineOn_cell X hab with ⟨m, c, _hm, hformula⟩
  exact ⟨m, c, hformula⟩

/-- Positive transfer scaling forces every constant source interval to have
zero measure, hence the distribution coordinate collapses it. -/
private theorem coordinate_collapses_plateau
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ) (hC : 0 < C)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    (X : DistributionQuotientData μ)
    {x y : I} (hxy : x ≤ y)
    (hflat : Set.EqOn T (fun _ => T x) (Set.Icc x y)) :
    Set.EqOn X.coordinate (fun _ => X.coordinate x) (Set.Icc x y) := by
  classical
  let F := PT.toFiniteMonotonePartition
  letI := F.fintype_idx
  have heval := congrArg (fun ν : Measure I => ν (Set.Icc x y)) heigen
  change piecewiseMonotoneTransferMeasure T F μ hμ (Set.Icc x y) =
    (ENNReal.ofReal C • μ) (Set.Icc x y) at heval
  rw [piecewiseMonotoneTransferMeasure_apply T F μ hμ measurableSet_Icc,
    Measure.smul_apply, smul_eq_mul] at heval
  have hterm (i : F.idx) :
      μ (T '' (Set.Icc x y ∩ F.piece i)) = 0 := by
    apply measure_mono_null _ (hμ (T x))
    rintro z ⟨u, hu, rfl⟩
    rw [Set.mem_singleton_iff]
    exact hflat hu.1
  have hsum : (∑ i : F.idx,
      μ (T '' (Set.Icc x y ∩ F.piece i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    exact hterm i
  rw [hsum] at heval
  have hsource : μ (Set.Icc x y) = 0 := by
    have hprod : ENNReal.ofReal C * μ (Set.Icc x y) = 0 := heval.symm
    rcases mul_eq_zero.mp hprod with hCzero | hzero
    · exact (ENNReal.ofReal_ne_zero_iff.mpr hC hCzero).elim
    · exact hzero
  have hends : X.coordinate x = X.coordinate y := by
    have hmass := X.interval_mass hxy
    rw [hsource] at hmass
    have hreverseReal : (X.coordinate y : ℝ) ≤ (X.coordinate x : ℝ) :=
      sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hmass.symm)
    apply le_antisymm
    · exact X.monotone_coordinate hxy
    · exact hreverseReal
  intro z hz
  have hxz := X.monotone_coordinate hz.1
  have hzy := X.monotone_coordinate hz.2
  rw [← hends] at hzy
  exact le_antisymm hzy hxz

/-- Every interval on which `P` is constant is collapsed by the common
distribution coordinate. -/
theorem SimultaneousTransferEigenProbability.coordinate_collapses_plateau_P
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure)
    {x y : I} (hxy : x ≤ y)
    (hflat : Set.EqOn P (fun _ => P x) (Set.Icc x y)) :
    Set.EqOn X.coordinate (fun _ => X.coordinate x) (Set.Icc x y) := by
  exact coordinate_collapses_plateau E.partitionP E.measure E.noAtoms
    E.scaleP E.scaleP_pos E.transferP_eigen X hxy hflat

/-- Every interval on which `Q` is constant is collapsed by the common
distribution coordinate. -/
theorem SimultaneousTransferEigenProbability.coordinate_collapses_plateau_Q
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure)
    {x y : I} (hxy : x ≤ y)
    (hflat : Set.EqOn Q (fun _ => Q x) (Set.Icc x y)) :
    Set.EqOn X.coordinate (fun _ => X.coordinate x) (Set.Icc x y) := by
  exact coordinate_collapses_plateau E.partitionQ E.measure E.noAtoms
    E.scaleQ E.scaleQ_pos E.transferQ_eigen X hxy hflat

/-- A common fixed point downstairs determines a nonempty compact interval
fibre upstairs, forward invariant under both original maps. -/
structure CommonFixedFibreData
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) (y : I) where
  interval : ClosedSubinterval
  carrier_eq : interval.carrier = {x : I | X.coordinate x = y}
  common_invariant : IsCommonInvariantCore P Q interval

theorem SimultaneousTransferEigenProbability.commonFixedFibre_exists
    {P Q : IntervalMap} (E : SimultaneousTransferEigenProbability P Q)
    (X : DistributionQuotientData E.measure) {y : I}
    (hyP : IsFixedPoint (E.factorP X) y)
    (hyQ : IsFixedPoint (E.factorQ X) y) :
    Nonempty (CommonFixedFibreData E X y) := by
  let fibre : Set I := {x : I | X.coordinate x = y}
  have hfibre_nonempty : fibre.Nonempty := X.surjective_coordinate y
  have hfibre_closed : IsClosed fibre := by
    exact isClosed_eq X.continuous_coordinate continuous_const
  have hfibre_compact : IsCompact fibre := hfibre_closed.isCompact
  obtain ⟨l, hl, hlmin⟩ := hfibre_compact.exists_isMinOn
    hfibre_nonempty continuous_id.continuousOn
  obtain ⟨r, hr, hrmax⟩ := hfibre_compact.exists_isMaxOn
    hfibre_nonempty continuous_id.continuousOn
  have hlr : l ≤ r := hlmin hr
  let J : ClosedSubinterval :=
    { left := l
      right := r
      left_le_right := hlr }
  have hcarrier : J.carrier = fibre := by
    change Set.Icc l r = fibre
    apply Set.Subset.antisymm
    · intro z hz
      have hlθz := X.monotone_coordinate hz.1
      have hzθr := X.monotone_coordinate hz.2
      have hlcoord : X.coordinate l = y := hl
      have hrcoord : X.coordinate r = y := hr
      change X.coordinate z = y
      apply le_antisymm
      · rw [hrcoord] at hzθr
        exact hzθr
      · rw [hlcoord] at hlθz
        exact hlθz
    · intro z hz
      exact ⟨hlmin hz, hrmax hz⟩
  refine ⟨{
    interval := J
    carrier_eq := hcarrier
    common_invariant := ?_ }⟩
  constructor
  · intro z hz
    have hzcoord : X.coordinate z = y := by
      have hz' : z ∈ fibre := by
        rw [← hcarrier]
        exact hz
      exact hz'
    rw [hcarrier]
    calc
      X.coordinate (P z) = E.factorP X (X.coordinate z) :=
        E.intertwines_factorP X z
      _ = E.factorP X y := congrArg (E.factorP X) hzcoord
      _ = y := hyP
  · intro z hz
    have hzcoord : X.coordinate z = y := by
      have hz' : z ∈ fibre := by
        rw [← hcarrier]
        exact hz
      exact hz'
    rw [hcarrier]
    calc
      X.coordinate (Q z) = E.factorQ X (X.coordinate z) :=
        E.intertwines_factorQ X z
      _ = E.factorQ X y := congrArg (E.factorQ X) hzcoord
      _ = y := hyQ

end CommutingInterval
