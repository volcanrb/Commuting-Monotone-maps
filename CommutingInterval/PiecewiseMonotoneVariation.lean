import CommutingInterval.PiecewiseMonotoneDefs
import CommutingInterval.PiecewiseMonotoneTransfer
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Vector and positive transfer for piecewise-monotone interval maps

This file supplies the exact total-variation argument used by the direct
piecewise-monotone proof.  The declarations are deliberately ordered by
dependency.  In particular, exactness for a finite partition is separated
into the one-branch change-of-partition argument and an exact finite-sum
lemma with the strong measurable-subset support hypothesis.
-/

noncomputable section

namespace CommutingInterval

open Function Set MeasureTheory
open scoped BigOperators ENNReal

/-! ## Bridge from manuscript partitions to transfer partitions -/

/-- The assigned Borel cells of a manuscript monotonicity partition form
the abstract finite monotonicity partition used by transfer operators. -/
noncomputable def MonotonicityPartition.toFiniteMonotonePartition
    {T : IntervalMap} (P : MonotonicityPartition T) :
    FiniteMonotonePartition T := by
  classical
  exact
    { idx := P.partition.LapIndex
      fintype_idx := inferInstance
      piece := fun q => q.assignedCell
      measurable_piece := fun q => q.measurableSet_assignedCell
      pairwise_disjoint := by
        intro q r hqr
        exact P.partition.assignedCells_disjoint hqr
      cover := P.partition.iUnion_assignedCells
      monotone_piece := fun q => P.weaklyMonotoneOn_assignedCell q }

/-- A map with a finite closed-interval monotonicity partition is Borel
measurable.  Continuity is not needed for this conclusion. -/
theorem MonotonicityPartition.measurable
    {T : IntervalMap} (P : MonotonicityPartition T) : Measurable T := by
  classical
  intro E hE
  have hpiece : ∀ q : P.partition.LapIndex,
      MeasurableSet (T ⁻¹' E ∩ q.assignedCell) := by
    intro q
    have hrestr : Measurable (fun x : q.assignedCell => T x) := by
      rcases P.weaklyMonotoneOn_assignedCell q with hmono | hanti
      · apply Monotone.measurable
        intro x y hxy
        exact hmono x.property y.property hxy
      · apply Antitone.measurable
        intro x y hxy
        exact hanti x.property y.property hxy
    have himage := q.measurableSet_assignedCell.subtype_image (hrestr hE)
    convert himage using 1
    ext x
    simp [and_comm]
  have hunion : T ⁻¹' E =
      ⋃ q : P.partition.LapIndex, (T ⁻¹' E ∩ q.assignedCell) := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⋃ q : P.partition.LapIndex, q.assignedCell := by
        rw [P.partition.iUnion_assignedCells]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.1 hxcover with ⟨q, hxq⟩
      exact Set.mem_iUnion.2 ⟨q, hx, hxq⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨q, hxE, _hxq⟩
      exact hxE
  rw [hunion]
  exact MeasurableSet.iUnion hpiece

/-- A finite-piece monotone map supplies an abstract transfer partition. -/
noncomputable def FinitePieceMonotone.someFiniteMonotonePartition
    {T : IntervalMap} (hT : FinitePieceMonotone T) :
    FiniteMonotonePartition T := by
  exact (Classical.choice hT.2).toFiniteMonotonePartition

/-! ## Nonatomic vector measures -/

/-- A vector measure is nonatomic when it vanishes on every singleton. -/
def VectorNoAtoms {K : Type*} [RCLike K]
    (z : VectorMeasure I K) : Prop :=
  ∀ x : I, z {x} = 0

/-- The `K`-subspace of nonatomic `K`-valued vector measures. -/
def nonatomicVectorMeasureSubmodule (K : Type*) [RCLike K] :
    Submodule K (VectorMeasure I K) where
  carrier := {z | VectorNoAtoms z}
  zero_mem' := by
    intro x
    exact VectorMeasure.zero_apply _
  add_mem' := by
    intro z w hz hw x
    rw [VectorMeasure.add_apply, hz x, hw x, add_zero]
  smul_mem' := by
    intro c z hz x
    rw [VectorMeasure.smul_apply, hz x, smul_zero]

/-- Nonatomic scalar-valued vector measures. -/
abbrev NonatomicVectorMeasure (K : Type*) [RCLike K] :=
  nonatomicVectorMeasureSubmodule K

theorem VectorNoAtoms.countable_null {K : Type*} [RCLike K]
    {z : VectorMeasure I K} (hz : VectorNoAtoms z)
    {s : Set I} (hs : s.Countable) : z s = 0 := by
  classical
  letI : Countable s := hs.to_subtype
  have hs_union : s = ⋃ x : s, ({x.1} : Set I) := by
    ext y
    simp
  have hs_meas : ∀ x : s, MeasurableSet ({x.1} : Set I) := fun x =>
    MeasurableSet.singleton x.1
  have hs_disj : Pairwise (Disjoint on fun x : s => ({x.1} : Set I)) := by
    intro x y hxy
    simp only [onFun, disjoint_singleton]
    exact Subtype.coe_ne_coe.mpr hxy
  rw [hs_union, VectorMeasure.of_disjoint_iUnion hs_meas hs_disj]
  have hzero : (fun x : s => z ({x.1} : Set I)) = 0 := by
    funext x
    exact hz x.1
  rw [hzero]
  exact tsum_zero

theorem VectorNoAtoms.diff_countable {K : Type*} [RCLike K]
    {z : VectorMeasure I K} (hz : VectorNoAtoms z)
    {A s : Set I} (hA : MeasurableSet A) (hs : s.Countable) :
    z (A \ s) = z A := by
  have hinter : A \ s = A \ (A ∩ s) := by
    ext x
    simp only [mem_diff, mem_inter_iff]
    tauto
  rw [hinter, VectorMeasure.of_diff (hA.inter hs.measurableSet) hA
    inter_subset_left, hz.countable_null (hs.mono inter_subset_right), sub_zero]

/-! ## One branch: vector and positive image measures -/

/-- The literal vector-valued branch image `E ↦ z (u '' (E ∩ D))`. -/
noncomputable def monotoneBranchImageVector {K : Type*} [RCLike K]
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) : VectorMeasure I K := by
  classical
  refine
    { measureOf' := fun E => if MeasurableSet E then z (u '' (E ∩ D)) else 0
      empty' := ?_
      not_measurable' := ?_
      m_iUnion' := ?_ }
  · simp
  · intro E hE
    simp [hE]
  · intro E hE hdisj
    simp only [hE, MeasurableSet.iUnion hE, if_true]
    let P := branchPlateauValues u D
    let A : ℕ → Set I := fun n => u '' (E n ∩ D)
    let F : ℕ → Set I := fun n => A n \ P
    have hsub : ∀ n, E n ∩ D ⊆ D := fun _ => inter_subset_right
    have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
      measurableSet_image_of_monotoneBranchOn
        ((hE n).inter hD) (hsub n) hu
    have hPcount : P.Countable := branchPlateauValues_countable hu
    have hFmeas : ∀ n, MeasurableSet (F n) := fun n =>
      (hAmeas n).diff hPcount.measurableSet
    have hinterDisj : Pairwise (Disjoint on fun n => E n ∩ D) := by
      intro n m hnm
      change Disjoint (E n ∩ D) (E m ∩ D)
      rw [Set.disjoint_left]
      intro x hxn hxm
      exact Set.disjoint_left.1 (hdisj hnm) hxn.1 hxm.1
    have hFdisj : Pairwise (Disjoint on F) :=
      pairwise_disjoint_image_diff_plateau hsub hinterDisj
    have hsum : HasSum (fun n => z (F n)) (z (⋃ n, F n)) :=
      z.m_iUnion hFmeas hFdisj
    have hterm : ∀ n, z (A n) = z (F n) := by
      intro n
      exact (hz.diff_countable (hAmeas n) hPcount).symm
    have hunionDomain : (⋃ n, E n) ∩ D = ⋃ n, E n ∩ D := by
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      tauto
    have hunionImage : u '' ((⋃ n, E n) ∩ D) = ⋃ n, A n := by
      rw [hunionDomain]
      ext y
      constructor
      · rintro ⟨x, hx, hux⟩
        rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
        exact Set.mem_iUnion.2 ⟨n, ⟨x, hxn, hux⟩⟩
      · intro hy
        rcases Set.mem_iUnion.1 hy with ⟨n, x, hxn, hux⟩
        exact ⟨x, Set.mem_iUnion.2 ⟨n, hxn⟩, hux⟩
    have hunionDiff : (⋃ n, A n) \ P = ⋃ n, F n := by
      rw [← Set.image_iUnion]
      simpa [A, F, P] using
        (image_iUnion_diff_plateau (u := u) (D := D)
          (E := fun n => E n ∩ D))
    have htotal : z (u '' ((⋃ n, E n) ∩ D)) = z (⋃ n, F n) := by
      rw [hunionImage, ← hunionDiff]
      exact (hz.diff_countable (MeasurableSet.iUnion hAmeas) hPcount).symm
    rw [htotal]
    exact hsum.congr_fun hterm

@[simp]
theorem monotoneBranchImageVector_apply {K : Type*} [RCLike K]
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) {E : Set I} (hE : MeasurableSet E) :
    monotoneBranchImageVector u D hD hu z hz E =
      z (u '' (E ∩ D)) := by
  simp [monotoneBranchImageVector, hE]

theorem monotoneBranchImageVector_noAtoms {K : Type*} [RCLike K]
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) :
    VectorNoAtoms (monotoneBranchImageVector u D hD hu z hz) := by
  intro x
  rw [monotoneBranchImageVector_apply u D hD hu z hz
    (MeasurableSet.singleton x)]
  apply hz.countable_null
  exact (countable_singleton x).image u |>.mono
    (image_mono inter_subset_left)

theorem monotoneBranchImageVector_add {K : Type*} [RCLike K]
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D)
    (z w : VectorMeasure I K) (hz : VectorNoAtoms z)
    (hw : VectorNoAtoms w) :
    monotoneBranchImageVector u D hD hu (z + w)
        (by
          intro x
          rw [VectorMeasure.add_apply, hz x, hw x, add_zero]) =
      monotoneBranchImageVector u D hD hu z hz +
        monotoneBranchImageVector u D hD hu w hw := by
  ext E hE
  simp only [monotoneBranchImageVector_apply _ _ _ _ _ _ hE,
    VectorMeasure.add_apply]

theorem monotoneBranchImageVector_smul {K : Type*} [RCLike K]
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (c : K)
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    monotoneBranchImageVector u D hD hu (c • z)
        (by
          intro x
          rw [VectorMeasure.smul_apply, hz x, smul_zero]) =
      c • monotoneBranchImageVector u D hD hu z hz := by
  ext E hE
  simp only [monotoneBranchImageVector_apply _ _ _ _ _ _ hE,
    VectorMeasure.smul_apply]

/-- A monotone branch acts linearly on nonatomic vector measures. -/
noncomputable def monotoneBranchTransferVector
    {K : Type*} [RCLike K] (u : I → I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D) :
    NonatomicVectorMeasure K →ₗ[K] NonatomicVectorMeasure K := by
  refine
    { toFun := fun z =>
        ⟨monotoneBranchImageVector u D hD hu z.1 z.2,
          monotoneBranchImageVector_noAtoms u D hD hu z.1 z.2⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro z w
    apply Subtype.ext
    exact monotoneBranchImageVector_add u D hD hu z.1 w.1 z.2 w.2
  · intro c z
    apply Subtype.ext
    exact monotoneBranchImageVector_smul u D hD hu c z.1 z.2

theorem monotoneBranchTransferVector_congr
    {K : Type*} [RCLike K] (u : I → I) (D D' : Set I)
    (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hu : MonotoneBranchOn u D) (hu' : MonotoneBranchOn u D')
    (h : D = D') :
    monotoneBranchTransferVector (K := K) u D hD hu =
      monotoneBranchTransferVector u D' hD' hu' := by
  subst D'
  rfl

/-- The literal positive branch image `E ↦ μ (u '' (E ∩ D))`. -/
noncomputable def monotoneBranchImageMeasure
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (μ : Measure I)
    (hμ : ∀ x : I, μ {x} = 0) : Measure I := by
  classical
  letI : NoAtoms μ := ⟨hμ⟩
  refine Measure.ofMeasurable
    (fun E _hE => μ (u '' (E ∩ D))) ?_ ?_
  · simp
  · intro E hE hdisj
    let P := branchPlateauValues u D
    let A : ℕ → Set I := fun n => u '' (E n ∩ D)
    let F : ℕ → Set I := fun n => A n \ P
    have hsub : ∀ n, E n ∩ D ⊆ D := fun _ => inter_subset_right
    have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
      measurableSet_image_of_monotoneBranchOn
        ((hE n).inter hD) (hsub n) hu
    have hPcount : P.Countable := branchPlateauValues_countable hu
    have hPnull : μ P = 0 := hPcount.measure_zero μ
    have hFmeas : ∀ n, MeasurableSet (F n) := fun n =>
      (hAmeas n).diff hPcount.measurableSet
    have hinterDisj : Pairwise (Disjoint on fun n => E n ∩ D) := by
      intro n m hnm
      change Disjoint (E n ∩ D) (E m ∩ D)
      rw [Set.disjoint_left]
      intro x hxn hxm
      exact Set.disjoint_left.1 (hdisj hnm) hxn.1 hxm.1
    have hFdisj : Pairwise (Disjoint on F) :=
      pairwise_disjoint_image_diff_plateau hsub hinterDisj
    have hterm : ∀ n, μ (A n) = μ (F n) := by
      intro n
      exact (measure_diff_null hPnull).symm
    have hunionDomain : (⋃ n, E n) ∩ D = ⋃ n, E n ∩ D := by
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      tauto
    have hunionImage : u '' ((⋃ n, E n) ∩ D) = ⋃ n, A n := by
      rw [hunionDomain]
      ext y
      constructor
      · rintro ⟨x, hx, hux⟩
        rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
        exact Set.mem_iUnion.2 ⟨n, ⟨x, hxn, hux⟩⟩
      · intro hy
        rcases Set.mem_iUnion.1 hy with ⟨n, x, hxn, hux⟩
        exact ⟨x, Set.mem_iUnion.2 ⟨n, hxn⟩, hux⟩
    have hunionDiff : (⋃ n, A n) \ P = ⋃ n, F n := by
      rw [← Set.image_iUnion]
      simpa [A, F, P] using
        (image_iUnion_diff_plateau (u := u) (D := D)
          (E := fun n => E n ∩ D))
    have htotal : μ (u '' ((⋃ n, E n) ∩ D)) = μ (⋃ n, F n) := by
      rw [hunionImage, ← hunionDiff]
      exact (measure_diff_null hPnull).symm
    change μ (u '' ((⋃ n, E n) ∩ D)) =
      ∑' n, μ (u '' (E n ∩ D))
    rw [htotal, measure_iUnion hFdisj hFmeas]
    congr 1
    funext n
    exact (hterm n).symm

@[simp]
theorem monotoneBranchImageMeasure_apply
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (μ : Measure I)
    (hμ : ∀ x : I, μ {x} = 0) {E : Set I} (hE : MeasurableSet E) :
    monotoneBranchImageMeasure u D hD hu μ hμ E =
      μ (u '' (E ∩ D)) := by
  exact Measure.ofMeasurable_apply E hE

theorem monotoneBranchImageMeasure_noAtoms
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (μ : Measure I)
    (hμ : ∀ x : I, μ {x} = 0) :
    ∀ x : I, monotoneBranchImageMeasure u D hD hu μ hμ {x} = 0 := by
  intro x
  rw [monotoneBranchImageMeasure_apply u D hD hu μ hμ
    (MeasurableSet.singleton x)]
  letI : NoAtoms μ := ⟨hμ⟩
  apply (countable_singleton x).image u |>.mono
    (image_mono inter_subset_left) |>.measure_zero μ

theorem monotoneBranchImageMeasure_isFinite
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (μ : Measure I)
    (hμ : ∀ x : I, μ {x} = 0) [IsFiniteMeasure μ] :
    IsFiniteMeasure (monotoneBranchImageMeasure u D hD hu μ hμ) := by
  constructor
  rw [monotoneBranchImageMeasure_apply u D hD hu μ hμ
    MeasurableSet.univ]
  exact lt_of_le_of_lt (measure_mono (subset_univ _))
    IsFiniteMeasure.measure_univ_lt_top

/-! ## Finite-partition vector and positive transfer -/

noncomputable def piecewiseMonotoneTransferVector
    {K : Type*} [RCLike K] (T : I → I)
    (P : FiniteMonotonePartition T) :
    NonatomicVectorMeasure K →ₗ[K] NonatomicVectorMeasure K := by
  letI := P.fintype_idx
  exact Finset.univ.sum fun i =>
    monotoneBranchTransferVector T (P.piece i) (P.measurable_piece i)
      (P.monotone_piece i)

theorem piecewiseMonotoneTransferVector_apply
    {K : Type*} [RCLike K] (T : I → I)
    (P : FiniteMonotonePartition T) (z : NonatomicVectorMeasure K)
    {E : Set I} (hE : MeasurableSet E) :
    (piecewiseMonotoneTransferVector T P z).1 E =
      (@Finset.univ P.idx P.fintype_idx).sum
        (fun i => z.1 (T '' (E ∩ P.piece i))) := by
  classical
  letI := P.fintype_idx
  simp only [piecewiseMonotoneTransferVector, LinearMap.sum_apply,
    Submodule.coe_sum]
  rw [VectorMeasure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  exact monotoneBranchImageVector_apply T (P.piece i)
    (P.measurable_piece i) (P.monotone_piece i) z.1 z.2 hE

theorem monotoneBranchTransferVector_split
    {K : Type*} [RCLike K] (T : I → I)
    (D : Set I) (hD : MeasurableSet D)
    (hmono : MonotoneBranchOn T D) {j : Type*} [Fintype j]
    (Q : j → Set I) (hQmeas : ∀ k, MeasurableSet (Q k))
    (hQdisj : Pairwise (Disjoint on Q))
    (hQcover : iUnion Q = Set.univ) :
    monotoneBranchTransferVector (K := K) T D hD hmono =
      Finset.univ.sum fun k =>
        monotoneBranchTransferVector T (D ∩ Q k)
          (hD.inter (hQmeas k))
          (by
            rcases hmono with hmono | hanti
            · exact Or.inl (hmono.mono inter_subset_left)
            · exact Or.inr (hanti.mono inter_subset_left)) := by
  classical
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  ext E hE
  let v : VectorMeasure I K :=
    monotoneBranchImageVector T D hD hmono z.1 z.2
  have hpartsMeas : ∀ k, MeasurableSet (E ∩ Q k) := fun k =>
    hE.inter (hQmeas k)
  have hpartsDisj : Pairwise (Disjoint on fun k => E ∩ Q k) := by
    intro k l hkl
    change Disjoint (E ∩ Q k) (E ∩ Q l)
    rw [Set.disjoint_left]
    intro x hxk hxl
    exact Set.disjoint_left.1 (hQdisj hkl) hxk.2 hxl.2
  have hpartsCover : E = ⋃ k, E ∩ Q k := by
    ext x
    constructor
    · intro hxE
      have hxQ : x ∈ ⋃ k, Q k := by
        rw [hQcover]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.1 hxQ with ⟨k, hxk⟩
      exact Set.mem_iUnion.2 ⟨k, hxE, hxk⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨k, hxE, _hxk⟩
      exact hxE
  have hv : v E = ∑ k, v (E ∩ Q k) := by
    calc
      v E = v (⋃ k, E ∩ Q k) := congrArg v hpartsCover
      _ = ∑' k, v (E ∩ Q k) :=
        VectorMeasure.of_disjoint_iUnion hpartsMeas hpartsDisj
      _ = ∑ k, v (E ∩ Q k) := tsum_fintype _
  have hv' :
      monotoneBranchImageVector T D hD hmono z.1 z.2 E =
        ∑ k, monotoneBranchImageVector T D hD hmono z.1 z.2
          (E ∩ Q k) := hv
  change monotoneBranchImageVector T D hD hmono z.1 z.2 E = _
  simp only [LinearMap.sum_apply]
  rw [Submodule.coe_sum, VectorMeasure.coe_finsetSum, Finset.sum_apply, hv']
  apply Finset.sum_congr rfl
  intro k _hk
  have hmonoK : MonotoneBranchOn T (D ∩ Q k) := by
    rcases hmono with hmono | hanti
    · exact Or.inl (hmono.mono inter_subset_left)
    · exact Or.inr (hanti.mono inter_subset_left)
  rw [monotoneBranchImageVector_apply T D hD hmono z.1 z.2
      (hE.inter (hQmeas k))]
  change z.1 (T '' ((E ∩ Q k) ∩ D)) =
    monotoneBranchImageVector T (D ∩ Q k) (hD.inter (hQmeas k))
      hmonoK z.1 z.2 E
  rw [monotoneBranchImageVector_apply T (D ∩ Q k)
      (hD.inter (hQmeas k)) hmonoK z.1 z.2 hE]
  congr 2
  ext x
  simp only [mem_inter_iff]
  tauto

theorem piecewiseMonotoneTransferVector_independent
    {K : Type*} [RCLike K] (T : I → I)
    (P Q : FiniteMonotonePartition T) :
    piecewiseMonotoneTransferVector (K := K) T P =
      piecewiseMonotoneTransferVector T Q := by
  classical
  letI := P.fintype_idx
  letI := Q.fintype_idx
  calc
    piecewiseMonotoneTransferVector (K := K) T P =
        ∑ i, monotoneBranchTransferVector T (P.piece i)
          (P.measurable_piece i) (P.monotone_piece i) := rfl
    _ = ∑ i, ∑ j, monotoneBranchTransferVector T
          (P.piece i ∩ Q.piece j)
          ((P.measurable_piece i).inter (Q.measurable_piece j))
          (by
            rcases P.monotone_piece i with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact monotoneBranchTransferVector_split T (P.piece i)
        (P.measurable_piece i) (P.monotone_piece i) (Q := Q.piece)
        Q.measurable_piece Q.pairwise_disjoint Q.cover
    _ = ∑ j, ∑ i, monotoneBranchTransferVector T
          (P.piece i ∩ Q.piece j)
          ((P.measurable_piece i).inter (Q.measurable_piece j))
          (by
            rcases P.monotone_piece i with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, monotoneBranchTransferVector T
          (Q.piece j ∩ P.piece i)
          ((Q.measurable_piece j).inter (P.measurable_piece i))
          (by
            rcases Q.monotone_piece j with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      apply monotoneBranchTransferVector_congr
      exact inter_comm (P.piece i) (Q.piece j)
    _ = ∑ j, monotoneBranchTransferVector T (Q.piece j)
          (Q.measurable_piece j) (Q.monotone_piece j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      symm
      exact monotoneBranchTransferVector_split T (Q.piece j)
        (Q.measurable_piece j) (Q.monotone_piece j) (Q := P.piece)
        P.measurable_piece P.pairwise_disjoint P.cover
    _ = piecewiseMonotoneTransferVector T Q := rfl

theorem piecewiseMonotoneTransferVector_comp
    {K : Type*} [RCLike K] {T U : I → I}
    (hTmeas : Measurable T) (P : FiniteMonotonePartition T)
    (Q : FiniteMonotonePartition U)
    (R : FiniteMonotonePartition (U ∘ T)) :
    piecewiseMonotoneTransferVector (K := K) (U ∘ T) R =
      (piecewiseMonotoneTransferVector T P).comp
        (piecewiseMonotoneTransferVector U Q) := by
  classical
  rw [piecewiseMonotoneTransferVector_independent (K := K)
    (U ∘ T) R (P.comp hTmeas Q)]
  letI := P.fintype_idx
  letI := Q.fintype_idx
  apply LinearMap.ext
  intro z
  change piecewiseMonotoneTransferVector (U ∘ T) (P.comp hTmeas Q) z =
    piecewiseMonotoneTransferVector T P
      (piecewiseMonotoneTransferVector U Q z)
  apply Subtype.ext
  ext E hE
  rw [piecewiseMonotoneTransferVector_apply (U ∘ T)
      (P.comp hTmeas Q) z hE,
    piecewiseMonotoneTransferVector_apply T P
      (piecewiseMonotoneTransferVector U Q z) hE]
  change (∑ q : P.idx × Q.idx,
      z.1 ((U ∘ T) ''
        (E ∩ (P.piece q.1 ∩ T ⁻¹' Q.piece q.2)))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  have hImageMeas : MeasurableSet (T '' (E ∩ P.piece i)) :=
    measurableSet_image_of_monotoneBranchOn
      (hE.inter (P.measurable_piece i)) inter_subset_right
        (P.monotone_piece i)
  rw [piecewiseMonotoneTransferVector_apply U Q z hImageMeas]
  apply Finset.sum_congr rfl
  intro j _hj
  apply congrArg z.1
  ext y
  constructor
  · rintro ⟨x, ⟨hxE, hxi, hTxj⟩, rfl⟩
    exact ⟨T x, ⟨⟨x, ⟨hxE, hxi⟩, rfl⟩, hTxj⟩, rfl⟩
  · rintro ⟨w, ⟨⟨x, ⟨hxE, hxi⟩, rfl⟩, hTxj⟩, rfl⟩
    exact ⟨x, ⟨hxE, hxi, hTxj⟩, rfl⟩

noncomputable def piecewiseMonotoneTransferMeasure
    (T : I → I) (P : FiniteMonotonePartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) : Measure I := by
  letI := P.fintype_idx
  exact ∑ i, monotoneBranchImageMeasure T (P.piece i)
    (P.measurable_piece i) (P.monotone_piece i) μ hμ

theorem piecewiseMonotoneTransferMeasure_apply
    (T : I → I) (P : FiniteMonotonePartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    {E : Set I} (hE : MeasurableSet E) :
    piecewiseMonotoneTransferMeasure T P μ hμ E =
      (@Finset.univ P.idx P.fintype_idx).sum
        (fun i => μ (T '' (E ∩ P.piece i))) := by
  classical
  letI := P.fintype_idx
  rw [piecewiseMonotoneTransferMeasure, MeasureTheory.Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  exact monotoneBranchImageMeasure_apply T (P.piece i)
    (P.measurable_piece i) (P.monotone_piece i) μ hμ hE

theorem piecewiseMonotoneTransferMeasure_noAtoms
    (T : I → I) (P : FiniteMonotonePartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) :
    ∀ x : I, piecewiseMonotoneTransferMeasure T P μ hμ {x} = 0 := by
  intro x
  rw [piecewiseMonotoneTransferMeasure_apply T P μ hμ
    (MeasurableSet.singleton x)]
  apply Finset.sum_eq_zero
  intro i _hi
  letI : NoAtoms μ := ⟨hμ⟩
  apply ((countable_singleton x).image T).mono
    (image_mono inter_subset_left) |>.measure_zero μ

theorem piecewiseMonotoneTransferMeasure_isFinite
    (T : I → I) (P : FiniteMonotonePartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    [IsFiniteMeasure μ] :
    IsFiniteMeasure (piecewiseMonotoneTransferMeasure T P μ hμ) := by
  constructor
  rw [piecewiseMonotoneTransferMeasure_apply T P μ hμ
    MeasurableSet.univ]
  rw [ENNReal.sum_lt_top]
  intro i _hi
  exact lt_of_le_of_lt (measure_mono (subset_univ _))
    IsFiniteMeasure.measure_univ_lt_top

theorem piecewiseMonotoneTransferMeasure_independent
    (T : I → I) (P Q : FiniteMonotonePartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) :
    piecewiseMonotoneTransferMeasure T P μ hμ =
      piecewiseMonotoneTransferMeasure T Q μ hμ := by
  classical
  letI := P.fintype_idx
  letI := Q.fintype_idx
  have hsplit (D : Set I) (hDm : MeasurableSet D)
      (hmono : MonotoneBranchOn T D) {j : Type} [Fintype j]
      (S : j → Set I) (hSmeas : ∀ k, MeasurableSet (S k))
      (hSdisj : Pairwise (Disjoint on S))
      (hScover : iUnion S = Set.univ) :
      monotoneBranchImageMeasure T D hDm hmono μ hμ =
        ∑ k, monotoneBranchImageMeasure T (D ∩ S k)
          (hDm.inter (hSmeas k))
          (by
            rcases hmono with hmono | hanti
            · exact Or.inl (hmono.mono inter_subset_left)
            · exact Or.inr (hanti.mono inter_subset_left)) μ hμ := by
    ext E hE
    rw [MeasureTheory.Measure.finsetSum_apply]
    let v : Measure I := monotoneBranchImageMeasure T D hDm hmono μ hμ
    have hpartsMeas : ∀ k, MeasurableSet (E ∩ S k) := fun k =>
      hE.inter (hSmeas k)
    have hpartsDisj : Pairwise (Disjoint on fun k => E ∩ S k) := by
      intro k l hkl
      change Disjoint (E ∩ S k) (E ∩ S l)
      rw [Set.disjoint_left]
      intro x hxk hxl
      exact Set.disjoint_left.1 (hSdisj hkl) hxk.2 hxl.2
    have hpartsCover : E = ⋃ k, E ∩ S k := by
      ext x
      constructor
      · intro hxE
        have hxS : x ∈ ⋃ k, S k := by
          rw [hScover]
          exact Set.mem_univ x
        rcases Set.mem_iUnion.1 hxS with ⟨k, hxk⟩
        exact Set.mem_iUnion.2 ⟨k, hxE, hxk⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨k, hxE, _⟩
        exact hxE
    have hv : v E = ∑ k, v (E ∩ S k) := by
      calc
        v E = v (⋃ k, E ∩ S k) := congrArg v hpartsCover
        _ = ∑' k, v (E ∩ S k) := measure_iUnion hpartsDisj hpartsMeas
        _ = ∑ k, v (E ∩ S k) := tsum_fintype _
    rw [show monotoneBranchImageMeasure T D hDm hmono μ hμ E = v E from rfl,
      hv]
    apply Finset.sum_congr rfl
    intro k _hk
    have hmonoK : MonotoneBranchOn T (D ∩ S k) := by
      rcases hmono with hmono | hanti
      · exact Or.inl (hmono.mono inter_subset_left)
      · exact Or.inr (hanti.mono inter_subset_left)
    rw [monotoneBranchImageMeasure_apply T D hDm hmono μ hμ
        (hE.inter (hSmeas k)),
      monotoneBranchImageMeasure_apply T (D ∩ S k)
        (hDm.inter (hSmeas k)) hmonoK μ hμ hE]
    congr 2
    ext x
    simp only [mem_inter_iff]
    tauto
  have hcongr (D D' : Set I) (hDm : MeasurableSet D)
      (hDm' : MeasurableSet D') (hmono : MonotoneBranchOn T D)
      (hmono' : MonotoneBranchOn T D') (h : D = D') :
      monotoneBranchImageMeasure T D hDm hmono μ hμ =
        monotoneBranchImageMeasure T D' hDm' hmono' μ hμ := by
    subst D'
    rfl
  calc
    piecewiseMonotoneTransferMeasure T P μ hμ =
        ∑ i, monotoneBranchImageMeasure T (P.piece i)
          (P.measurable_piece i) (P.monotone_piece i) μ hμ := rfl
    _ = ∑ i, ∑ j, monotoneBranchImageMeasure T
          (P.piece i ∩ Q.piece j)
          ((P.measurable_piece i).inter (Q.measurable_piece j))
          (by
            rcases P.monotone_piece i with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) μ hμ := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hsplit (P.piece i) (P.measurable_piece i)
        (P.monotone_piece i) Q.piece Q.measurable_piece
        Q.pairwise_disjoint Q.cover
    _ = ∑ j, ∑ i, monotoneBranchImageMeasure T
          (P.piece i ∩ Q.piece j)
          ((P.measurable_piece i).inter (Q.measurable_piece j))
          (by
            rcases P.monotone_piece i with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) μ hμ := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, monotoneBranchImageMeasure T
          (Q.piece j ∩ P.piece i)
          ((Q.measurable_piece j).inter (P.measurable_piece i))
          (by
            rcases Q.monotone_piece j with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) μ hμ := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      apply hcongr
      exact inter_comm (P.piece i) (Q.piece j)
    _ = ∑ j, monotoneBranchImageMeasure T (Q.piece j)
          (Q.measurable_piece j) (Q.monotone_piece j) μ hμ := by
      apply Finset.sum_congr rfl
      intro j _hj
      symm
      exact hsplit (Q.piece j) (Q.measurable_piece j)
        (Q.monotone_piece j) P.piece P.measurable_piece
        P.pairwise_disjoint P.cover
    _ = piecewiseMonotoneTransferMeasure T Q μ hμ := rfl

theorem piecewiseMonotoneTransferMeasure_comp
    {T U : I → I} (hTmeas : Measurable T)
    (P : FiniteMonotonePartition T) (Q : FiniteMonotonePartition U)
    (R : FiniteMonotonePartition (U ∘ T))
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) :
    piecewiseMonotoneTransferMeasure (U ∘ T) R μ hμ =
      piecewiseMonotoneTransferMeasure T P
        (piecewiseMonotoneTransferMeasure U Q μ hμ)
        (piecewiseMonotoneTransferMeasure_noAtoms U Q μ hμ) := by
  classical
  rw [piecewiseMonotoneTransferMeasure_independent (U ∘ T) R
    (P.comp hTmeas Q) μ hμ]
  letI := P.fintype_idx
  letI := Q.fintype_idx
  ext E hE
  rw [piecewiseMonotoneTransferMeasure_apply (U ∘ T)
      (P.comp hTmeas Q) μ hμ hE,
    piecewiseMonotoneTransferMeasure_apply T P
      (piecewiseMonotoneTransferMeasure U Q μ hμ)
      (piecewiseMonotoneTransferMeasure_noAtoms U Q μ hμ) hE]
  change (∑ q : P.idx × Q.idx,
      μ ((U ∘ T) ''
        (E ∩ (P.piece q.1 ∩ T ⁻¹' Q.piece q.2)))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  have hImageMeas : MeasurableSet (T '' (E ∩ P.piece i)) :=
    measurableSet_image_of_monotoneBranchOn
      (hE.inter (P.measurable_piece i)) inter_subset_right
        (P.monotone_piece i)
  rw [piecewiseMonotoneTransferMeasure_apply U Q μ hμ hImageMeas]
  apply Finset.sum_congr rfl
  intro j _hj
  apply congrArg μ
  ext y
  constructor
  · rintro ⟨x, ⟨hxE, hxi, hTxj⟩, rfl⟩
    exact ⟨T x, ⟨⟨x, ⟨hxE, hxi⟩, rfl⟩, hTxj⟩, rfl⟩
  · rintro ⟨w, ⟨⟨x, ⟨hxE, hxi⟩, rfl⟩, hTxj⟩, rfl⟩
    exact ⟨x, ⟨hxE, hxi, hTxj⟩, rfl⟩

/-! ## Manuscript-facing wrappers and compatibility -/

noncomputable def transferVector {K : Type*} [RCLike K]
    (T : IntervalMap) (P : MonotonicityPartition T)
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) : VectorMeasure I K :=
  (piecewiseMonotoneTransferVector T P.toFiniteMonotonePartition
    ⟨z, by change VectorNoAtoms z; exact hz⟩).1

noncomputable def transferMeasure
    (T : IntervalMap) (P : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) : Measure I :=
  piecewiseMonotoneTransferMeasure T P.toFiniteMonotonePartition μ hμ

theorem transferVector_noAtoms {K : Type*} [RCLike K]
    (T : IntervalMap) (P : MonotonicityPartition T)
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    VectorNoAtoms (transferVector T P z hz) := by
  exact (piecewiseMonotoneTransferVector T P.toFiniteMonotonePartition
    ⟨z, by change VectorNoAtoms z; exact hz⟩).2

theorem transferMeasure_noAtoms
    (T : IntervalMap) (P : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) :
    ∀ x : I, transferMeasure T P μ hμ {x} = 0 := by
  exact piecewiseMonotoneTransferMeasure_noAtoms T
    P.toFiniteMonotonePartition μ hμ

theorem transferVector_add {K : Type*} [RCLike K]
    (T : IntervalMap) (P : MonotonicityPartition T)
    (z w : VectorMeasure I K) (hz : VectorNoAtoms z)
    (hw : VectorNoAtoms w) :
    transferVector T P (z + w)
        (by
          intro x
          rw [VectorMeasure.add_apply, hz x, hw x, add_zero]) =
      transferVector T P z hz + transferVector T P w hw := by
  let L := piecewiseMonotoneTransferVector (K := K) T
    P.toFiniteMonotonePartition
  let z' : NonatomicVectorMeasure K :=
    ⟨z, by change VectorNoAtoms z; exact hz⟩
  let w' : NonatomicVectorMeasure K :=
    ⟨w, by change VectorNoAtoms w; exact hw⟩
  have h := congrArg Subtype.val (L.map_add z' w')
  simpa [transferVector, L, z', w'] using h

theorem transferVector_smul {K : Type*} [RCLike K]
    (T : IntervalMap) (P : MonotonicityPartition T)
    (c : K) (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    transferVector T P (c • z)
        (by
          intro x
          rw [VectorMeasure.smul_apply, hz x, smul_zero]) =
      c • transferVector T P z hz := by
  let L := piecewiseMonotoneTransferVector (K := K) T
    P.toFiniteMonotonePartition
  let z' : NonatomicVectorMeasure K :=
    ⟨z, by change VectorNoAtoms z; exact hz⟩
  have h := congrArg Subtype.val (L.map_smul c z')
  simpa [transferVector, L, z'] using h

theorem transferVector_independent {K : Type*} [RCLike K]
    (T : IntervalMap) (P Q : MonotonicityPartition T)
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    transferVector T P z hz = transferVector T Q z hz := by
  unfold transferVector
  rw [piecewiseMonotoneTransferVector_independent (K := K) T
    P.toFiniteMonotonePartition Q.toFiniteMonotonePartition]

theorem transferMeasure_independent
    (T : IntervalMap) (P Q : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) :
    transferMeasure T P μ hμ = transferMeasure T Q μ hμ := by
  exact piecewiseMonotoneTransferMeasure_independent T
    P.toFiniteMonotonePartition Q.toFiniteMonotonePartition μ hμ

theorem transferVector_comp {K : Type*} [RCLike K]
    {T U : IntervalMap} (hTmeas : Measurable T)
    (P : MonotonicityPartition T) (Q : MonotonicityPartition U)
    (R : MonotonicityPartition (U ∘ T))
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    transferVector (U ∘ T) R z hz =
      transferVector T P (transferVector U Q z hz)
        (transferVector_noAtoms U Q z hz) := by
  let z' : NonatomicVectorMeasure K :=
    ⟨z, by change VectorNoAtoms z; exact hz⟩
  have h := LinearMap.congr_fun
    (piecewiseMonotoneTransferVector_comp (K := K) hTmeas
      P.toFiniteMonotonePartition Q.toFiniteMonotonePartition
      R.toFiniteMonotonePartition) z'
  exact congrArg Subtype.val h

theorem transferMeasure_comp
    {T U : IntervalMap} (hTmeas : Measurable T)
    (P : MonotonicityPartition T) (Q : MonotonicityPartition U)
    (R : MonotonicityPartition (U ∘ T))
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) :
    transferMeasure (U ∘ T) R μ hμ =
      transferMeasure T P (transferMeasure U Q μ hμ)
        (transferMeasure_noAtoms U Q μ hμ) := by
  exact piecewiseMonotoneTransferMeasure_comp hTmeas
    P.toFiniteMonotonePartition Q.toFiniteMonotonePartition
    R.toFiniteMonotonePartition μ hμ

theorem transferVector_real_eq_signed
    (T : IntervalMap) (P : MonotonicityPartition T)
    (z : VectorMeasure I ℝ) (hz : VectorNoAtoms z) :
    transferVector T P z hz =
      (piecewiseMonotoneTransfer T P.toFiniteMonotonePartition
        ⟨z, hz⟩).1 := by
  ext E hE
  change (piecewiseMonotoneTransferVector T
      P.toFiniteMonotonePartition
      ⟨z, by change VectorNoAtoms z; exact hz⟩).1 E = _
  rw [piecewiseMonotoneTransferVector_apply T
      P.toFiniteMonotonePartition _ hE,
    piecewiseMonotoneTransfer_apply T P.toFiniteMonotonePartition _ hE]

/-! ## Exact variation: singleton, restriction, branch, and finite sum -/

theorem variation_singleton {K : Type*} [RCLike K]
    (z : VectorMeasure I K) (x : I) :
    z.variation {x} = ‖z {x}‖ₑ := by
  let hs : MeasurableSet ({x} : Set I) := MeasurableSet.singleton x
  rw [VectorMeasure.variation_apply, preVariation_apply,
    VectorMeasure.ennrealToMeasure_apply hs, ennrealPreVariation_apply]
  simp only [preVariationFun, hs, dite_true]
  let a : Subtype MeasurableSet := ⟨{x}, hs⟩
  have ha : IsAtom a := by
    constructor
    · intro h
      have hc : ({x} : Set I) = ∅ := congrArg Subtype.val h
      simp at hc
    · intro b hb
      apply Subtype.ext
      exact (Set.isAtom_singleton x).2 b.1 hb
  letI : Unique (Finpartition a) :=
    ha.uniqueFinpartition (P := Finpartition.indiscrete ha.ne_bot)
  rw [iSup_unique]
  have hdef : (default : Finpartition a) =
      Finpartition.indiscrete ha.ne_bot := Subsingleton.elim _ _
  rw [hdef, Finpartition.indiscrete_parts]
  simp

theorem variation_noAtoms {K : Type*} [RCLike K]
    {z : VectorMeasure I K} (hz : VectorNoAtoms z) :
    NoAtoms z.variation := by
  constructor
  intro x
  rw [variation_singleton z x, hz x, enorm_zero]

theorem variation_restrict {K : Type*} [RCLike K]
    (z : VectorMeasure I K) {D : Set I} (hD : MeasurableSet D) :
    (z.restrict D).variation = z.variation.restrict D := by
  have hle (A : Set I) (hA : MeasurableSet A) :
      (z.restrict A).variation ≤ z.variation.restrict A := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    rw [VectorMeasure.restrict_apply z hA hE,
      Measure.restrict_apply hE]
    exact VectorMeasure.enorm_measure_le_variation z (E ∩ A)
  apply le_antisymm (hle D hD)
  have hcomp : (z.restrict D).variation.restrict Dᶜ = 0 := by
    apply le_antisymm
    · calc
        (z.restrict D).variation.restrict Dᶜ ≤
            (z.variation.restrict D).restrict Dᶜ :=
          Measure.restrict_mono_measure (hle D hD) Dᶜ
        _ = 0 := by
          rw [Measure.restrict_restrict hD.compl, compl_inter_self,
            Measure.restrict_empty]
    · exact Measure.zero_le _
  have hself : (z.restrict D).variation.restrict D =
      (z.restrict D).variation := by
    have hsplit := Measure.restrict_add_restrict_compl
      (μ := (z.restrict D).variation) hD
    rw [hcomp, add_zero] at hsplit
    exact hsplit
  have hcomp' : (z.restrict Dᶜ).variation.restrict D = 0 := by
    apply le_antisymm
    · calc
        (z.restrict Dᶜ).variation.restrict D ≤
            (z.variation.restrict Dᶜ).restrict D :=
          Measure.restrict_mono_measure (hle Dᶜ hD.compl) D
        _ = 0 := by
          rw [Measure.restrict_restrict hD, inter_compl_self,
            Measure.restrict_empty]
    · exact Measure.zero_le _
  have hzsum : z.restrict D + z.restrict Dᶜ = z :=
    VectorMeasure.restrict_add_restrict_compl z hD
  have hvar : z.variation ≤
      (z.restrict D).variation + (z.restrict Dᶜ).variation := by
    calc
      z.variation = (z.restrict D + z.restrict Dᶜ).variation :=
        congrArg VectorMeasure.variation hzsum.symm
      _ ≤ (z.restrict D).variation + (z.restrict Dᶜ).variation :=
        VectorMeasure.variation_add_le
  have hres := Measure.restrict_mono_measure hvar D
  rw [Measure.restrict_add, hself, hcomp', add_zero] at hres
  exact hres

theorem variation_monotoneBranchImage_le
    {K : Type*} [RCLike K]
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) :
    (monotoneBranchImageVector u D hD hu z hz).variation ≤
      monotoneBranchImageMeasure u D hD hu z.variation
        (fun x => by
          letI : NoAtoms z.variation := variation_noAtoms hz
          exact measure_singleton x) := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  rw [monotoneBranchImageVector_apply u D hD hu z hz hE,
    monotoneBranchImageMeasure_apply u D hD hu z.variation _ hE]
  exact VectorMeasure.enorm_measure_le_variation z (u '' (E ∩ D))

/-- Reverse branch variation needs measurable preimages; continuity of an
interval map is the manuscript source of this hypothesis. -/
theorem monotoneBranchImageMeasure_le_variation
    {K : Type*} [RCLike K]
    (u : I → I) (huMeas : Measurable u)
    (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) :
    monotoneBranchImageMeasure u D hD hu z.variation
        (fun x => by
          letI : NoAtoms z.variation := variation_noAtoms hz
          exact measure_singleton x) ≤
      (monotoneBranchImageVector u D hD hu z hz).variation := by
  classical
  let b := monotoneBranchImageVector u D hD hu z hz
  refine Measure.le_intro fun E hE _ => ?_
  have hAmeas : MeasurableSet (u '' (E ∩ D)) :=
    measurableSet_image_of_monotoneBranchOn (hE.inter hD)
      inter_subset_right hu
  rw [monotoneBranchImageMeasure_apply u D hD hu z.variation _ hE]
  simp only [VectorMeasure.variation_apply, preVariation,
    VectorMeasure.ennrealToMeasure_apply hAmeas,
    ennrealPreVariation_apply, preVariationFun, hAmeas, dite_true,
    iSup_le_iff]
  intro Q
  let B : Subtype MeasurableSet → Set I := fun p =>
    (E ∩ D) ∩ u ⁻¹' p.1
  have hBmeas (p : Subtype MeasurableSet) : MeasurableSet (B p) :=
    (hE.inter hD).inter (p.property.preimage huMeas)
  have hBsub (p : Subtype MeasurableSet) : B p ⊆ E := by
    intro x hx
    exact hx.1.1
  have hImage (p : Subtype MeasurableSet) (hp : p ∈ Q.parts) :
      u '' (B p) = p.1 := by
    have hpA : (p.1 : Set I) ⊆ u '' (E ∩ D) :=
      Q.le hp
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      rcases hpA hy with ⟨x, hx, hux⟩
      exact ⟨x, ⟨hx, by simpa [hux] using hy⟩, hux⟩
  have hBinj : Set.InjOn B (↑Q.parts : Set (Subtype MeasurableSet)) := by
    intro p hp q hq hpq
    apply Subtype.ext
    calc
      p.1 = u '' (B p) := (hImage p hp).symm
      _ = u '' (B q) := congrArg (fun C : Set I => u '' C) hpq
      _ = q.1 := hImage q hq
  let S : Finset (Set I) := Q.parts.image B
  have hSmeas : ∀ C ∈ S, MeasurableSet C := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
    exact hBmeas p
  have hSsub : ∀ C ∈ S, C ⊆ E := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
    exact hBsub p
  have hSdisj : (S : Set (Set I)).PairwiseDisjoint id := by
    intro C hC F hF hCF
    rcases Finset.mem_image.mp hC with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hF with ⟨q, hq, rfl⟩
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact hCF rfl
    have hpqDisj := Q.disjoint hp hq hpq
    change Disjoint (B p) (B q)
    rw [Set.disjoint_left]
    intro x hxp hxq
    have hup : u x ∈ p.1 := hxp.2
    have huq : u x ∈ q.1 := hxq.2
    change Disjoint p q at hpqDisj
    have hmeet : p ⊓ q = (⊥ : Subtype MeasurableSet) :=
      disjoint_iff.mp hpqDisj
    have hmeetSet : p.1 ∩ q.1 = (∅ : Set I) :=
      congrArg Subtype.val hmeet
    have hmem : u x ∈ p.1 ∩ q.1 := ⟨hup, huq⟩
    rw [hmeetSet] at hmem
    exact hmem
  have hterm (p : Subtype MeasurableSet) (hp : p ∈ Q.parts) :
      ‖z p.1‖ₑ = ‖b (B p)‖ₑ := by
    have hBD : B p ∩ D = B p := by
      apply inter_eq_left.2
      intro x hx
      exact hx.1.2
    change ‖z p.1‖ₑ =
      ‖monotoneBranchImageVector u D hD hu z hz (B p)‖ₑ
    rw [monotoneBranchImageVector_apply u D hD hu z hz (hBmeas p),
      hBD, hImage p hp]
  calc
    ∑ p ∈ Q.parts, ‖z p.1‖ₑ =
        ∑ p ∈ Q.parts, ‖b (B p)‖ₑ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hterm p hp
    _ = ∑ C ∈ S, ‖b C‖ₑ := by
      change (∑ p ∈ Q.parts, ‖b (B p)‖ₑ) =
        ∑ C ∈ Q.parts.image B, ‖b C‖ₑ
      exact (Finset.sum_image
        (f := fun C : Set I => ‖b C‖ₑ) hBinj).symm
    _ ≤ b.variation E :=
      VectorMeasure.le_variation b hE hSsub hSdisj

theorem variation_monotoneBranchImage
    {K : Type*} [RCLike K]
    (u : I → I) (huMeas : Measurable u)
    (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) :
    (monotoneBranchImageVector u D hD hu z hz).variation =
      monotoneBranchImageMeasure u D hD hu z.variation
        (fun x => by
          letI : NoAtoms z.variation := variation_noAtoms hz
          exact measure_singleton x) := by
  apply le_antisymm
  · exact variation_monotoneBranchImage_le u D hD hu z hz
  · exact monotoneBranchImageMeasure_le_variation u huMeas D hD hu z hz

/-- Strong support: every measurable subset disjoint from `D` has zero
vector mass.  The whole complement alone would permit cancellation. -/
def HasStrongMeasurableSupport {K : Type*} [RCLike K]
    (z : VectorMeasure I K) (D : Set I) : Prop :=
  ∀ E : Set I, MeasurableSet E → Disjoint E D → z E = 0

theorem monotoneBranchImageVector_hasStrongSupport
    {K : Type*} [RCLike K]
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) :
    HasStrongMeasurableSupport
      (monotoneBranchImageVector u D hD hu z hz) D := by
  intro E hE hdisj
  rw [monotoneBranchImageVector_apply u D hD hu z hz hE]
  have hinter : E ∩ D = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  rw [hinter, image_empty, z.empty]

theorem eq_restrict_of_hasStrongMeasurableSupport
    {K : Type*} [RCLike K]
    (z : VectorMeasure I K) {D : Set I} (hD : MeasurableSet D)
    (hz : HasStrongMeasurableSupport z D) : z.restrict D = z := by
  ext E hE
  rw [VectorMeasure.restrict_apply z hD hE]
  have hzero : z (E \ D) = 0 :=
    hz (E \ D) (hE.diff hD) Set.disjoint_sdiff_left
  have hdisj : Disjoint (E ∩ D) (E \ D) := by
    rw [Set.disjoint_left]
    intro x hx hxd
    exact hxd.2 hx.2
  have hunion : (E ∩ D) ∪ (E \ D) = E := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_diff]
    tauto
  have hadd := z.of_union hdisj (hE.inter hD) (hE.diff hD)
  rw [hunion, hzero, add_zero] at hadd
  exact hadd.symm

theorem variation_finsetSum_eq_of_disjoint_support
    {K : Type*} [RCLike K] {ι : Type*}
    (s : Finset ι) (z : ι → VectorMeasure I K)
    (D : ι → Set I)
    (hDmeas : ∀ i ∈ s, MeasurableSet (D i))
    (hD : Set.PairwiseDisjoint (↑s : Set ι) D)
    (hsupp : ∀ i ∈ s, HasStrongMeasurableSupport (z i) (D i)) :
    (∑ i ∈ s, z i).variation =
      ∑ i ∈ s, (z i).variation := by
  classical
  let v : VectorMeasure I K := ∑ i ∈ s, z i
  have hrestrict (i : ι) (hi : i ∈ s) : v.restrict (D i) = z i := by
    change (VectorMeasure.restrictGm (D i)) (∑ j ∈ s, z j) = z i
    rw [map_sum]
    calc
      (∑ j ∈ s, (VectorMeasure.restrictGm (D i)) (z j)) =
          (z i).restrict (D i) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          ext E hE
          change (z j).restrict (D i) E = 0
          rw [VectorMeasure.restrict_apply _ (hDmeas i hi) hE]
          apply hsupp j hj (E ∩ D i) (hE.inter (hDmeas i hi))
          exact (hD hi hj hji.symm).mono inter_subset_right Subset.rfl
        · exact fun hni => (hni hi).elim
      _ = z i := eq_restrict_of_hasStrongMeasurableSupport
        (z i) (hDmeas i hi) (hsupp i hi)
  have hvarRestrict (i : ι) (hi : i ∈ s) :
      v.variation.restrict (D i) = (z i).variation := by
    rw [← hrestrict i hi, variation_restrict v (hDmeas i hi)]
  apply le_antisymm
  · simpa [v] using VectorMeasure.variation_finsetSum_le s z
  · refine Measure.le_intro fun E hE _ => ?_
    rw [Measure.finsetSum_apply]
    calc
      (∑ i ∈ s, (z i).variation E) =
          ∑ i ∈ s, v.variation (E ∩ D i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hvarRestrict i hi, Measure.restrict_apply hE]
      _ = ∑ i ∈ s, (v.variation.restrict E) (D i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Measure.restrict_apply (hDmeas i hi), inter_comm]
      _ ≤ (v.variation.restrict E) Set.univ :=
        MeasureTheory.sum_measure_le_measure_univ
          (fun i hi => (hDmeas i hi).nullMeasurableSet)
          (fun i hi j hj hij => (hD hi hj hij).aedisjoint)
      _ = v.variation E := Measure.restrict_apply_univ E

theorem variation_piecewiseMonotoneTransferVector
    {K : Type*} [RCLike K]
    (T : I → I) (hTmeas : Measurable T)
    (P : FiniteMonotonePartition T)
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    (piecewiseMonotoneTransferVector T P
      ⟨z, by change VectorNoAtoms z; exact hz⟩).1.variation =
      piecewiseMonotoneTransferMeasure T P z.variation
        (fun x => by
          letI : NoAtoms z.variation := variation_noAtoms hz
          exact measure_singleton x) := by
  classical
  letI := P.fintype_idx
  let hvarNoAtoms : ∀ x : I, z.variation {x} = 0 := fun x => by
    letI : NoAtoms z.variation := variation_noAtoms hz
    exact measure_singleton x
  let b : P.idx → VectorMeasure I K := fun i =>
    monotoneBranchImageVector T (P.piece i)
      (P.measurable_piece i) (P.monotone_piece i) z hz
  have hvec :
      (piecewiseMonotoneTransferVector T P
        ⟨z, by change VectorNoAtoms z; exact hz⟩).1 = ∑ i, b i := by
    simp only [piecewiseMonotoneTransferVector, LinearMap.sum_apply,
      Submodule.coe_sum, b]
    apply Finset.sum_congr rfl
    intro i _hi
    rfl
  have hmeasure :
      piecewiseMonotoneTransferMeasure T P z.variation
        (fun x => by
          letI : NoAtoms z.variation := variation_noAtoms hz
          exact measure_singleton x) =
      ∑ i, monotoneBranchImageMeasure T (P.piece i)
        (P.measurable_piece i) (P.monotone_piece i) z.variation
          hvarNoAtoms := by
    rfl
  rw [hvec, hmeasure]
  change
    (∑ i, b i).variation =
    ∑ i, monotoneBranchImageMeasure T (P.piece i)
      (P.measurable_piece i) (P.monotone_piece i) z.variation hvarNoAtoms
  rw [variation_finsetSum_eq_of_disjoint_support
    (Finset.univ : Finset P.idx) b P.piece
    (fun i _ => P.measurable_piece i)
    (fun i _ j _ hij => P.pairwise_disjoint hij)
    (fun i _ => monotoneBranchImageVector_hasStrongSupport T
      (P.piece i) (P.measurable_piece i) (P.monotone_piece i) z hz)]
  apply Finset.sum_congr rfl
  intro i _hi
  change (b i).variation = _
  exact variation_monotoneBranchImage T hTmeas (P.piece i)
    (P.measurable_piece i) (P.monotone_piece i) z hz

/-- Exact naturality of total variation under piecewise-monotone transfer. -/
theorem variation_transfer_eq_transfer_variation
    {K : Type*} [RCLike K]
    (T : IntervalMap) (PT : MonotonicityPartition T)
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    (transferVector T PT z hz).variation =
      transferMeasure T PT z.variation
        (fun x => by
          letI : NoAtoms z.variation := variation_noAtoms hz
          exact measure_singleton x) := by
  exact variation_piecewiseMonotoneTransferVector T PT.measurable
    PT.toFiniteMonotonePartition z hz

/-! ## Complex-measure finiteness and exact scalar variation -/

theorem signed_enorm_le_totalVariation
    (s : SignedMeasure I) {E : Set I} (hE : MeasurableSet E) :
    ‖s E‖ₑ ≤ s.totalVariation E := by
  let p := s.toJordanDecomposition.posPart
  let n := s.toJordanDecomposition.negPart
  have hsE : s E = (p E).toReal - (n E).toReal := by
    rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s,
      JordanDecomposition.toSignedMeasure,
      Measure.toSignedMeasure_sub_apply hE]
    rfl
  rw [hsE, ← ofReal_norm]
  calc
    ENNReal.ofReal ‖(p E).toReal - (n E).toReal‖ ≤
        ENNReal.ofReal ((p E).toReal + (n E).toReal) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs]
      calc
        |(p E).toReal - (n E).toReal| ≤
            |(p E).toReal| + |(n E).toReal| := abs_sub _ _
        _ = (p E).toReal + (n E).toReal := by
          rw [abs_of_nonneg ENNReal.toReal_nonneg,
            abs_of_nonneg ENNReal.toReal_nonneg]
    _ = p E + n E := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top p E),
        ENNReal.ofReal_toReal (measure_ne_top n E)]
    _ = s.totalVariation E := by
      rw [SignedMeasure.totalVariation, Measure.add_apply]

theorem complex_variation_le_re_im_totalVariation
    (z : ComplexMeasure I) :
    z.variation ≤ z.re.totalVariation + z.im.totalVariation := by
  apply VectorMeasure.variation_le_of_forall_enorm_le
  intro E hE
  calc
    ‖z E‖ₑ ≤ ‖z.re E‖ₑ + ‖z.im E‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
      rw [← ENNReal.ofReal_add (norm_nonneg (z.re E))
        (norm_nonneg (z.im E))]
      exact ENNReal.ofReal_le_ofReal
        (Complex.norm_le_abs_re_add_abs_im (z E))
    _ ≤ z.re.totalVariation E + z.im.totalVariation E := by
      gcongr
      · exact signed_enorm_le_totalVariation z.re hE
      · exact signed_enorm_le_totalVariation z.im hE
    _ = (z.re.totalVariation + z.im.totalVariation) E := by
      rw [Measure.add_apply]

theorem complex_variation_ne_zero_iff (z : ComplexMeasure I) :
    z.variation ≠ 0 ↔ z ≠ 0 := by
  constructor
  · intro hv hz
    subst z
    exact hv VectorMeasure.variation_zero
  · intro hz hv
    apply hz
    ext E hE
    have h := VectorMeasure.enorm_measure_le_variation z E
    rw [hv] at h
    simp only [Measure.coe_zero, Pi.zero_apply] at h
    exact enorm_eq_zero.mp (nonpos_iff_eq_zero.mp h)

theorem complex_variation_isFinite (z : ComplexMeasure I) :
    IsFiniteMeasure z.variation := by
  constructor
  calc
    z.variation Set.univ ≤
        (z.re.totalVariation + z.im.totalVariation) Set.univ :=
      complex_variation_le_re_im_totalVariation z Set.univ
    _ < ∞ := by
      simp [SignedMeasure.totalVariation, measure_lt_top]

theorem variation_smul_isROrC {K : Type*} [RCLike K]
    (c : K) (z : VectorMeasure I K) :
    (c • z).variation = ENNReal.ofReal ‖c‖ • z.variation := by
  have hle (a : K) (w : VectorMeasure I K) :
      (a • w).variation ≤ ENNReal.ofReal ‖a‖ • w.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    rw [VectorMeasure.smul_apply, enorm_smul, ← ofReal_norm,
      Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right
      (VectorMeasure.enorm_measure_le_variation w E) _
  apply le_antisymm (hle c z)
  by_cases hc : c = 0
  · subst c
    have hleft : ENNReal.ofReal ‖(0 : K)‖ • z.variation = 0 := by simp
    have hright : ((0 : K) • z).variation = 0 := by
      have hz : (0 : K) • z = (0 : VectorMeasure I K) := zero_smul K z
      rw [hz, VectorMeasure.variation_zero]
    rw [hleft, hright]
  have hinv := hle c⁻¹ (c • z)
  have hscalar : ENNReal.ofReal ‖c‖ * ENNReal.ofReal ‖c⁻¹‖ = 1 := by
    rw [← ENNReal.ofReal_mul (norm_nonneg c)]
    simp [hc]
  refine Measure.le_intro fun E hE _ => ?_
  have hinvE := hinv E
  rw [inv_smul_smul₀ hc] at hinvE
  rw [Measure.smul_apply, smul_eq_mul] at hinvE ⊢
  calc
    ENNReal.ofReal ‖c‖ * z.variation E ≤
        ENNReal.ofReal ‖c‖ *
          (ENNReal.ofReal ‖c⁻¹‖ * (c • z).variation E) :=
      mul_le_mul_right hinvE _
    _ = (c • z).variation E := by
      rw [← mul_assoc, hscalar, one_mul]

theorem variation_complex_smul (c : ℂ) (z : ComplexMeasure I) :
    (c • z).variation = ENNReal.ofReal ‖c‖ • z.variation := by
  exact variation_smul_isROrC c z

end CommutingInterval
