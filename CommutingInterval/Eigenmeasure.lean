import CommutingInterval.PiecewiseMonotoneEigen
import CommutingIntervalSimplified.BranchLength
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Signed eigenmeasures and continuous branch coordinates

The cumulative function `x ↦ σ([0,x])` embeds finite nonatomic signed
interval measures into normalized continuous real coordinates. This identifies
the signed branch-transfer eigenspace with its image in the coordinate
eigenspace and identifies their positive probability simplices. -/

namespace CommutingInterval.Eigenmeasure

open Set Function MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

private theorem jordan_apply (σ : SignedMeasure I) {E : Set I} (hE : MeasurableSet E) :
    σ E = (σ.toJordanDecomposition.posPart E).toReal - (σ.toJordanDecomposition.negPart E).toReal := by
  conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition σ,
    JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hE]
  rfl

private theorem jordan_noAtoms (σ : NonatomicSignedMeasure) :
    NoAtoms σ.1.toJordanDecomposition.posPart ∧ NoAtoms σ.1.toJordanDecomposition.negPart := by
  let p := σ.1.toJordanDecomposition.posPart
  let n := σ.1.toJordanDecomposition.negPart
  obtain ⟨A, _, hA, hAc⟩ := σ.1.toJordanDecomposition.mutuallySingular
  have h (x : I) : p {x} = 0 ∧ n {x} = 0 := by
    have he : p {x} = n {x} := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top p {x}) (measure_ne_top n {x})).mp
      apply sub_eq_zero.mp
      exact (jordan_apply σ.1 (measurableSet_singleton x)).symm.trans (σ.2 x)
    by_cases hx : x ∈ A
    · have hp : p {x} = 0 := measure_mono_null (singleton_subset_iff.mpr hx) hA
      exact ⟨hp, he.symm.trans hp⟩
    · have hn : n {x} = 0 := measure_mono_null (singleton_subset_iff.mpr hx) hAc
      exact ⟨he.trans hn, hn⟩
  exact ⟨⟨fun x => (h x).1⟩, ⟨fun x => (h x).2⟩⟩

private theorem continuous_measure_Iic (μ : Measure I) [IsFiniteMeasure μ] [NoAtoms μ] :
    Continuous (fun x : I => (μ (Iic x)).toReal) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (ENNReal.continuousAt_toReal (measure_ne_top μ (Iic x))).tendsto.comp
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 x) measurableSet_Iic
    (fun _ => measurableSet_Iic)
  filter_upwards [μ.ae_ne x] with y hy
  rcases lt_or_gt_of_ne hy with hl | hh
  · filter_upwards [Ioi_mem_nhds hl] with z hz
    change y < z at hz
    change y ≤ z ↔ y ≤ x
    exact iff_of_true hz.le hl.le
  · filter_upwards [Iio_mem_nhds hh] with z hz
    change z < y at hz
    change y ≤ z ↔ y ≤ x
    exact iff_of_false (not_le_of_gt hz) (not_le_of_gt hh)

theorem continuous_cumulative (σ : NonatomicSignedMeasure) : Continuous (fun x : I => σ.1 (Iic x)) := by
  obtain ⟨hp, hn⟩ := jordan_noAtoms σ
  exact ((continuous_measure_Iic σ.1.toJordanDecomposition.posPart).sub
    (continuous_measure_Iic σ.1.toJordanDecomposition.negPart)).congr fun _ => (jordan_apply _ measurableSet_Iic).symm

/-- The continuous distribution function, linear in the signed measure. -/
def cumulative : NonatomicSignedMeasure →ₗ[ℝ] CommutingIntervalSimplified.NormalizedContinuousCoordinate where
  toFun σ := ⟨⟨fun x => σ.1 (Iic x), continuous_cumulative σ⟩, by
    change σ.1 (Iic leftEndpoint) = 0
    rw [show Iic leftEndpoint = {leftEndpoint} by exact Iic_bot]
    exact σ.2 _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cumulative_injective : Injective cumulative := by
  intro σ τ he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply signedMeasure_eq_zero_of_Iic_eq_zero
  intro x
  exact sub_eq_zero.mpr (congrArg (fun F : CommutingIntervalSimplified.NormalizedContinuousCoordinate => F x) he)

theorem cumulative_increment (σ : NonatomicSignedMeasure) {x y : I} (hxy : x ≤ y) :
    cumulative σ y - cumulative σ x = σ.1 (Icc x y) := by
  change σ.1 (Iic y) - σ.1 (Iic x) = _
  rw [← VectorMeasure.of_diff (v := σ.1) measurableSet_Iic measurableSet_Iic (Iic_subset_Iic.mpr hxy), Iic_diff_Iic]
  have he : Icc x y \ {x} = Ioc x y := by
    ext z
    simp only [mem_diff, mem_Icc, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨hx,hy⟩,hne⟩; exact ⟨lt_of_le_of_ne hx (Ne.symm hne),hy⟩
    · rintro ⟨hx,hy⟩; exact ⟨⟨hx.le,hy⟩,hx.ne'⟩
  rw [← he]
  exact SignedNoAtoms.diff_countable σ.2 measurableSet_Icc (countable_singleton _)

theorem cumulative_stieltjes (F : CommutingIntervalSimplified.NormalizedContinuousCoordinate) (hF : Monotone (fun x : I => F x)) :
    cumulative (semiconjugacySignedMeasure _ hF F.1.continuous) = F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  have h := semiconjugacySignedMeasure_Icc _ hF F.1.continuous (a := leftEndpoint) (b := x) x.2.1
  have h₀ : F leftEndpoint = 0 := F.2
  change (semiconjugacySignedMeasure _ hF F.1.continuous).1 (Iic x) = F x
  simpa only [show Icc leftEndpoint x = Iic x by exact Icc_bot, h₀, sub_zero] using h

/-- The same partition, expressed in the signed-transfer API. -/
def measurePartition {T : IntervalMap} (P : CommutingIntervalSimplified.MonotonicityPartition T) :
    MonotonicityPartition T where
  partition := ⟨P.partition.points, P.partition.zero_mem, P.partition.one_mem, P.partition.points_subset⟩
  weaklyMonotoneOn_cell := fun {_ _} h => P.weaklyMonotoneOn_cell h

/-- The manuscript's branchwise pullback acting on actual signed measures. -/
def transfer {T : IntervalMap} (P : CommutingIntervalSimplified.MonotonicityPartition T) :
    Module.End ℝ NonatomicSignedMeasure :=
  piecewiseMonotoneTransfer T (measurePartition P).toFiniteMonotonePartition

private theorem insert_null (σ : NonatomicSignedMeasure) {E : Set I} (hE : MeasurableSet E) (x : I) :
    σ.1 (insert x E) = σ.1 E := by
  by_cases hx : x ∈ E
  · rw [insert_eq_of_mem hx]
  · rw [← singleton_union, VectorMeasure.of_union (by simpa) (measurableSet_singleton _) hE,
      σ.2 x, zero_add]

private theorem transfer_interval {T : IntervalMap} (P : CommutingIntervalSimplified.MonotonicityPartition T)
    (σ : NonatomicSignedMeasure) {a b : ℝ} (hab : P.partition.Adjacent a b)
    {x y : I} (hx : x ∈ CommutingIntervalSimplified.intervalCell a b)
    (hy : y ∈ CommutingIntervalSimplified.intervalCell a b) (hxy : x ≤ y) :
    (transfer P σ).1 (Icc x y) = σ.1 (T '' Icc x y) := by
  classical
  let Q := measurePartition P
  let q : Q.partition.LapIndex := ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩⟩
  have hsub : Ico x y ⊆ q.assignedCell := by
    intro z hz
    have ha : a ≤ (z:ℝ) := hx.1.trans hz.1
    have hb : (z:ℝ) < b := (show (z:ℝ) < y from hz.2).trans_le hy.2
    change z ∈ (if b = 1 then {w : I | (w:ℝ) ∈ Icc a b} else {w : I | (w:ℝ) ∈ Ico a b})
    split
    · exact ⟨ha, hb.le⟩
    · exact ⟨ha, hb⟩
  have hmeas := measurableSet_image_of_monotoneBranchOn measurableSet_Ico hsub (Q.weaklyMonotoneOn_assignedCell q)
  rw [← Ico_insert_right hxy, image_insert_eq, insert_null (transfer P σ) measurableSet_Ico,
    insert_null σ hmeas]
  exact piecewiseMonotoneTransfer_apply_of_subset_piece T Q.toFiniteMonotonePartition σ
    measurableSet_Ico (i := q) hsub

/-- Taking the cumulative function intertwines the signed-measure transfer
with the continuous branch-length operator, including on constant laps. -/
theorem cumulative_transfer {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) (σ : NonatomicSignedMeasure) :
    cumulative (transfer P σ) = CommutingIntervalSimplified.branchLengthOperator hT (cumulative σ) := by
  suffices h : (fun x : I => cumulative (transfer P σ) x) =
      (fun x : I => (CommutingIntervalSimplified.branchLengthOperator hT (cumulative σ)) x) by
    exact Subtype.ext (ContinuousMap.ext (congrFun h))
  apply CommutingIntervalSimplified.funext_of_partition_increments P.partition
  · change cumulative (transfer P σ) leftEndpoint = (CommutingIntervalSimplified.branchLengthOperator hT (cumulative σ)) leftEndpoint
    exact (cumulative (transfer P σ)).2.trans (CommutingIntervalSimplified.branchLengthOperator hT (cumulative σ)).2.symm
  · intro a b hab x y hx hy hxy
    change cumulative (transfer P σ) y - cumulative (transfer P σ) x =
      CommutingIntervalSimplified.branchLength hT (cumulative σ) y - CommutingIntervalSimplified.branchLength hT (cumulative σ) x
    rw [cumulative_increment _ hxy, transfer_interval P σ hab hx hy hxy,
      CommutingIntervalSimplified.branchLength_increment hT P _ hab hx hy hxy]
    have hsub : Icc x y ⊆ CommutingIntervalSimplified.intervalCell a b :=
      fun z hz => ⟨hx.1.trans hz.1, (show (z:ℝ) ≤ y from hz.2).trans hy.2⟩
    rcases P.weaklyMonotoneOn_cell hab with hp | hn
    · have he := hp hx hy hxy
      rw [hT.continuous.continuousOn.image_Icc_of_monotoneOn hxy (hp.mono hsub),
        CommutingIntervalSimplified.coordinateLength, max_eq_right he, min_eq_left he]
      exact (cumulative_increment σ he).symm
    · have he := hn hx hy hxy
      rw [hT.continuous.continuousOn.image_Icc_of_antitoneOn hxy (hn.mono hsub),
        CommutingIntervalSimplified.coordinateLength, max_eq_left he, min_eq_right he]
      exact (cumulative_increment σ he).symm

/-- Finite signed nonatomic measures satisfying the branch-transfer eigen-equation. -/
def space {T : IntervalMap} (P : CommutingIntervalSimplified.MonotonicityPartition T) (ρ : ℝ) :
    Submodule ℝ NonatomicSignedMeasure := Module.End.eigenspace (transfer P) ρ

theorem mem_space_iff {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) (ρ : ℝ) (σ : NonatomicSignedMeasure) :
    σ ∈ space P ρ ↔ cumulative σ ∈ CommutingIntervalSimplified.branchEigenspace hT ρ := by
  rw [space, Module.End.mem_eigenspace_iff, CommutingIntervalSimplified.mem_branchEigenspace,
    ← cumulative_transfer hT P, ← map_smul]
  exact ⟨congrArg cumulative, fun h => cumulative_injective h⟩

def spaceEmbedding {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) (ρ : ℝ) :
    space P ρ →ₗ[ℝ] CommutingIntervalSimplified.branchEigenspace hT ρ :=
  (cumulative.comp (space P ρ).subtype).codRestrict _ (fun σ => (mem_space_iff hT P ρ σ.1).mp σ.2)

theorem spaceEmbedding_injective {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) (ρ : ℝ) : Injective (spaceEmbedding hT P ρ) :=
  fun _ _ h => Subtype.ext (cumulative_injective (congrArg Subtype.val h))

theorem finiteDimensional {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) {ρ : ℝ} (hρ : 1 < ρ) :
    FiniteDimensional ℝ (space P ρ) := by
  letI := CommutingIntervalSimplified.branchEigenspace_finiteDimensional hT hρ
  exact FiniteDimensional.of_injective (V₂ := ↥(CommutingIntervalSimplified.branchEigenspace hT ρ)) (spaceEmbedding hT P ρ) (spaceEmbedding_injective hT P ρ)

theorem finrank_le_partition_card {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) {ρ : ℝ} (hρ : 1 < ρ) :
    Module.finrank ℝ (space P ρ) ≤ P.partition.points.card := by
  letI := CommutingIntervalSimplified.branchEigenspace_finiteDimensional hT hρ
  exact (LinearMap.finrank_le_finrank_of_injective (spaceEmbedding_injective hT P ρ)).trans
    (CommutingIntervalSimplified.branchEigenspace_finrank_le_partition_card hT hρ P)

/-- A positive signed interval measure of mass one in the given eigenspace. -/
def probabilities {T : IntervalMap} (P : CommutingIntervalSimplified.MonotonicityPartition T) (ρ : ℝ) :
    Set NonatomicSignedMeasure := {σ | σ ∈ space P ρ ∧ (∀ E, MeasurableSet E → 0 ≤ σ.1 E) ∧ σ.1 univ = 1}

private theorem nonnegative_stieltjes {F : CommutingIntervalSimplified.NormalizedContinuousCoordinate}
    (hF : Monotone (fun x : I => F x)) {E : Set I} (hE : MeasurableSet E) :
    0 ≤ (semiconjugacySignedMeasure _ hF F.1.continuous).1 E := by
  letI := semiconjugacyMeasure_finite _ hF
  change 0 ≤ (semiconjugacyMeasure _ hF).toSignedMeasure E
  rw [Measure.toSignedMeasure_apply_measurable hE]; exact ENNReal.toReal_nonneg

theorem probabilities_image {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) (ρ : ℝ) :
    cumulative '' probabilities P ρ = CommutingIntervalSimplified.branchEigenSimplex hT ρ := by
  have hright (σ : NonatomicSignedMeasure) : cumulative σ rightEndpoint = σ.1 univ := by
    change σ.1 (Iic rightEndpoint) = _; rw [show Iic rightEndpoint = univ by exact Iic_top]
  ext F
  constructor
  · rintro ⟨σ, ⟨hσ, hpos, hone⟩, rfl⟩
    refine ⟨(mem_space_iff hT P ρ σ).mp hσ, fun x y hxy => ?_, (hright σ).trans hone⟩
    exact sub_nonneg.mp ((cumulative_increment σ hxy).symm ▸ hpos _ measurableSet_Icc)
  · rintro ⟨hF, hmon, hone⟩
    let σ := semiconjugacySignedMeasure _ hmon F.1.continuous
    have he : cumulative σ = F := cumulative_stieltjes F hmon
    exact ⟨σ, ⟨(mem_space_iff hT P ρ σ).mpr (he ▸ hF), fun _ hE => nonnegative_stieltjes hmon hE,
      (hright σ).symm.trans (he ▸ hone)⟩, he⟩

/-- Nonemptiness follows from a normalized positive eigen-coordinate, as
supplied by the semiconjugacy in the preceding paragraph of the manuscript. -/
theorem probabilities_nonempty {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) {ρ : ℝ}
    (hseed : (CommutingIntervalSimplified.branchEigenSimplex hT ρ).Nonempty) :
    (probabilities P ρ).Nonempty := by
  rw [← probabilities_image hT P] at hseed
  exact hseed.of_image

/-- With the topology induced by the cumulative uniform norm, the signed
eigenprobabilities form a compact set. -/
theorem probabilities_compact {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) {ρ : ℝ} (hρ : 1 < ρ) :
    @IsCompact _ (TopologicalSpace.induced cumulative inferInstance) (probabilities P ρ) := by
  letI : TopologicalSpace NonatomicSignedMeasure := TopologicalSpace.induced cumulative inferInstance
  exact (Topology.IsInducing.isCompact_iff (f := cumulative) ⟨rfl⟩).mpr
    (by rw [probabilities_image hT]; exact CommutingIntervalSimplified.branchEigenSimplex_isCompact hT hρ)

theorem probabilities_convex {T : IntervalMap} (P : CommutingIntervalSimplified.MonotonicityPartition T) (ρ : ℝ) :
    Convex ℝ (probabilities P ρ) := by
  intro σ hσ τ hτ a b ha hb hab
  rcases hσ with ⟨hs,hpos,hm⟩; rcases hτ with ⟨ht,hpos',hm'⟩
  refine ⟨(space P ρ).add_mem ((space P ρ).smul_mem a hs) ((space P ρ).smul_mem b ht), ?_, ?_⟩
  · intro E hE
    change 0 ≤ a*σ.1 E+b*τ.1 E
    exact add_nonneg (mul_nonneg ha (hpos _ hE)) (mul_nonneg hb (hpos' _ hE))
  · change a*σ.1 univ+b*τ.1 univ = 1
    simpa [hm, hm'] using hab

/-- The finite-dimensional eigenmeasure lemma of §5.1. The input eigen-coordinate
gives the initial probability measure, and compactness uses the uniform norm
of the cumulative distribution function. -/
theorem finite_eigenmeasure_space {T : IntervalMap} (hT : CommutingIntervalSimplified.FinitePieceMonotone T)
    (P : CommutingIntervalSimplified.MonotonicityPartition T) {ρ : ℝ} (hρ : 1 < ρ)
    (hseed : (CommutingIntervalSimplified.branchEigenSimplex hT ρ).Nonempty) :
    FiniteDimensional ℝ (space P ρ) ∧ Module.finrank ℝ (space P ρ) ≤ P.partition.points.card ∧
      (probabilities P ρ).Nonempty ∧ Convex ℝ (probabilities P ρ) ∧
      @IsCompact _ (TopologicalSpace.induced cumulative inferInstance) (probabilities P ρ) :=
  ⟨finiteDimensional hT P hρ, finrank_le_partition_card hT P hρ,
    probabilities_nonempty hT P hseed, probabilities_convex P ρ, probabilities_compact hT P hρ⟩

end
end CommutingInterval.Eigenmeasure
