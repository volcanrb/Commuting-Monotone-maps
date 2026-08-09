import CommutingInterval.DynamicsDefs
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Transfer operators for monotone branches with plateaus

Branches need not be injective.  The source measure is therefore required to
be nonatomic: different pieces of a fibre can only create overlaps at the
countable set of plateau values.
-/

noncomputable section

namespace CommutingInterval

open Function Set MeasureTheory
open scoped BigOperators ENNReal

/-! ## Nonatomic finite signed Borel measures -/

/-- A signed measure is nonatomic when every singleton has signed mass zero. -/
def SignedNoAtoms (sigma : SignedMeasure I) : Prop :=
  forall x : I, sigma {x} = 0

/-- The vector subspace of finite signed nonatomic Borel measures on `I`. -/
def nonatomicSignedMeasureSubmodule : Submodule Real (SignedMeasure I) where
  carrier := {sigma | SignedNoAtoms sigma}
  zero_mem' := by
    intro x
    exact VectorMeasure.zero_apply _
  add_mem' := by
    intro sigma tau hsigma htau x
    simp only [SignedNoAtoms] at hsigma htau
    rw [VectorMeasure.add_apply, hsigma x, htau x, add_zero]
  smul_mem' := by
    intro c sigma hsigma x
    simp only [SignedNoAtoms] at hsigma
    rw [VectorMeasure.smul_apply, hsigma x, smul_zero]

/-- The real vector space denoted by `M(I)` in the manuscript. -/
abbrev NonatomicSignedMeasure := nonatomicSignedMeasureSubmodule

theorem SignedNoAtoms.countable_null {sigma : SignedMeasure I}
    (hsigma : SignedNoAtoms sigma) {s : Set I} (hs : s.Countable) :
    sigma s = 0 := by
  classical
  letI : Countable s := hs.to_subtype
  have hs_union : s = ⋃ x : s, ({x.1} : Set I) := by
    ext y
    simp
  have hmeas : ∀ x : s, MeasurableSet ({x.1} : Set I) := fun x =>
    MeasurableSet.singleton x.1
  have hdisj : Pairwise (Disjoint on fun x : s => ({x.1} : Set I)) := by
    intro x y hxy
    simp only [onFun, disjoint_singleton]
    exact Subtype.coe_ne_coe.mpr hxy
  rw [hs_union, VectorMeasure.of_disjoint_iUnion hmeas hdisj]
  have hzero : (fun x : s => sigma ({x.1} : Set I)) = 0 := by
    funext x
    exact hsigma x.1
  rw [hzero]
  exact tsum_zero

/-- Removing a countable set does not change a nonatomic signed measure. -/
theorem SignedNoAtoms.diff_countable {sigma : SignedMeasure I}
    (hsigma : SignedNoAtoms sigma) {A s : Set I} (hA : MeasurableSet A)
    (hs : s.Countable) :
    sigma (A \ s) = sigma A := by
  have hinter : A \ s = A \ (A ∩ s) := by
    ext x
    simp only [mem_diff, mem_inter_iff]
    tauto
  rw [hinter, VectorMeasure.of_diff (hA.inter hs.measurableSet) hA inter_subset_left,
    hsigma.countable_null (hs.mono inter_subset_right), sub_zero]

/-! ## A single monotone branch -/

/-- A branch is allowed to be either nondecreasing or nonincreasing. -/
def MonotoneBranchOn (u : I -> I) (D : Set I) : Prop :=
  MonotoneOn u D \/ AntitoneOn u D

/-- Values whose fiber in `D` contains two ordered distinct points. -/
def branchPlateauValues (u : I -> I) (D : Set I) : Set I :=
  {z | exists x y, x ∈ D ∧ y ∈ D ∧ x < y ∧ u x = z ∧ u y = z}

theorem branchPlateauValues_countable {u : I -> I} {D : Set I}
    (hu : MonotoneBranchOn u D) :
    (branchPlateauValues u D).Countable := by
  rcases hu with hu | hu
  · exact hu.countable_setOf_two_preimages
  · exact hu.countable_setOf_two_preimages

theorem measurableSet_image_of_monotoneBranchOn {u : I -> I}
    {D E : Set I} (hE : MeasurableSet E) (hED : E ⊆ D)
    (hu : MonotoneBranchOn u D) :
    MeasurableSet (u '' E) := by
  rcases hu with hu | hu
  · exact hE.image_of_monotoneOn (hu.mono hED)
  · exact hE.image_of_antitoneOn (hu.mono hED)

theorem image_inter_image_subset_plateau {u : I -> I} {D A B : Set I}
    (hA : A ⊆ D) (hB : B ⊆ D) (hAB : Disjoint A B) :
    u '' A ∩ u '' B ⊆ branchPlateauValues u D := by
  rintro z ⟨⟨x, hxA, hxz⟩, ⟨y, hyB, hyz⟩⟩
  have hxy : x ≠ y := by
    intro h
    subst y
    exact Set.disjoint_left.1 hAB hxA hyB
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · exact ⟨x, y, hA hxA, hB hyB, hxy, hxz, hyz⟩
  · exact ⟨y, x, hB hyB, hA hxA, hyx, hyz, hxz⟩

theorem pairwise_disjoint_image_diff_plateau {u : I -> I} {D : Set I}
    {E : Nat -> Set I} (hED : forall n, E n ⊆ D)
    (hdisj : Pairwise (Disjoint on E)) :
    Pairwise (Disjoint on
      fun n => u '' E n \ branchPlateauValues u D) := by
  intro n m hnm
  change Disjoint (u '' E n \ branchPlateauValues u D)
    (u '' E m \ branchPlateauValues u D)
  rw [Set.disjoint_left]
  intro z hzn hzm
  have hzP : z ∈ branchPlateauValues u D :=
    image_inter_image_subset_plateau (hED n) (hED m) (hdisj hnm)
      ⟨hzn.1, hzm.1⟩
  exact hzn.2 hzP

theorem image_iUnion_diff_plateau {u : I -> I} {D : Set I}
    {E : Nat -> Set I} :
    u '' (iUnion E) \ branchPlateauValues u D =
      iUnion fun n => u '' E n \ branchPlateauValues u D := by
  ext z
  simp only [mem_diff, mem_image, mem_iUnion]
  constructor
  · rintro ⟨⟨x, ⟨n, hxn⟩, hux⟩, hzP⟩
    exact ⟨n, ⟨⟨x, hxn, hux⟩, hzP⟩⟩
  · rintro ⟨n, ⟨⟨x, hxn, hux⟩, hzP⟩⟩
    exact ⟨⟨x, ⟨n, hxn⟩, hux⟩, hzP⟩

/-- The signed image measure `E |-> sigma (u(E inter D))` of a monotone
branch.  The proof arguments certify exactly why this set function is a
signed measure in the presence of plateaus. -/
noncomputable def monotoneBranchImageSigned (u : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D)
    (sigma : SignedMeasure I) (hsigma : SignedNoAtoms sigma) :
    SignedMeasure I := by
  classical
  refine
    { measureOf' := fun E => if MeasurableSet E then sigma (u '' (E ∩ D)) else 0
      empty' := ?_
      not_measurable' := ?_
      m_iUnion' := ?_ }
  · simp
  · intro E hE
    simp [hE]
  · intro E hE hdisj
    simp only [hE, MeasurableSet.iUnion hE, if_true]
    let P := branchPlateauValues u D
    let A : Nat → Set I := fun n => u '' (E n ∩ D)
    let F : Nat → Set I := fun n => A n \ P
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
    have hsum : HasSum (fun n => sigma (F n)) (sigma (⋃ n, F n)) :=
      sigma.m_iUnion hFmeas hFdisj
    have hterm : ∀ n, sigma (A n) = sigma (F n) := by
      intro n
      exact (hsigma.diff_countable (hAmeas n) hPcount).symm
    have hunionDomain : (⋃ n, E n) ∩ D = ⋃ n, E n ∩ D := by
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      tauto
    have hunionImage : u '' ((⋃ n, E n) ∩ D) = ⋃ n, A n := by
      rw [hunionDomain]
      ext z
      constructor
      · rintro ⟨x, hx, hux⟩
        rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
        exact Set.mem_iUnion.2 ⟨n, ⟨x, hxn, hux⟩⟩
      · intro hz
        rcases Set.mem_iUnion.1 hz with ⟨n, x, hxn, hux⟩
        exact ⟨x, Set.mem_iUnion.2 ⟨n, hxn⟩, hux⟩
    have hunionDiff : (⋃ n, A n) \ P = ⋃ n, F n := by
      rw [← Set.image_iUnion]
      simpa [A, F, P] using
        (image_iUnion_diff_plateau (u := u) (D := D)
          (E := fun n => E n ∩ D))
    have htotal : sigma (u '' ((⋃ n, E n) ∩ D)) = sigma (⋃ n, F n) := by
      rw [hunionImage, ← hunionDiff]
      exact (hsigma.diff_countable
        (MeasurableSet.iUnion hAmeas) hPcount).symm
    rw [htotal]
    exact hsum.congr_fun hterm

@[simp]
theorem monotoneBranchImageSigned_apply (u : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D)
    (sigma : SignedMeasure I) (hsigma : SignedNoAtoms sigma)
    {E : Set I} (hE : MeasurableSet E) :
    monotoneBranchImageSigned u D hD hu sigma hsigma E =
      sigma (u '' (E ∩ D)) := by
  simp [monotoneBranchImageSigned, hE]

theorem monotoneBranchImageSigned_noAtoms (u : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D)
    (sigma : SignedMeasure I) (hsigma : SignedNoAtoms sigma) :
    SignedNoAtoms (monotoneBranchImageSigned u D hD hu sigma hsigma) := by
  intro x
  rw [monotoneBranchImageSigned_apply u D hD hu sigma hsigma
    (MeasurableSet.singleton x)]
  apply hsigma.countable_null
  exact (countable_singleton x).image u |>.mono (image_mono inter_subset_left)

theorem monotoneBranchImageSigned_add (u : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D)
    (sigma tau : SignedMeasure I) (hsigma : SignedNoAtoms sigma)
    (htau : SignedNoAtoms tau) :
    monotoneBranchImageSigned u D hD hu (sigma + tau)
        (nonatomicSignedMeasureSubmodule.add_mem hsigma htau) =
      monotoneBranchImageSigned u D hD hu sigma hsigma +
        monotoneBranchImageSigned u D hD hu tau htau := by
  ext E hE
  simp only [monotoneBranchImageSigned_apply _ _ _ _ _ _ hE,
    VectorMeasure.add_apply]

theorem monotoneBranchImageSigned_smul (u : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D)
    (c : Real) (sigma : SignedMeasure I) (hsigma : SignedNoAtoms sigma) :
    monotoneBranchImageSigned u D hD hu (c • sigma)
        (nonatomicSignedMeasureSubmodule.smul_mem c hsigma) =
      c • monotoneBranchImageSigned u D hD hu sigma hsigma := by
  ext E hE
  simp only [monotoneBranchImageSigned_apply _ _ _ _ _ _ hE,
    VectorMeasure.smul_apply]

/-- A single branch acts linearly on finite signed nonatomic measures. -/
noncomputable def monotoneBranchTransfer (u : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D) :
    NonatomicSignedMeasure →ₗ[Real] NonatomicSignedMeasure := by
  refine
    { toFun := fun sigma =>
        ⟨monotoneBranchImageSigned u D hD hu sigma.1 sigma.2,
          monotoneBranchImageSigned_noAtoms u D hD hu sigma.1 sigma.2⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro sigma tau
    apply Subtype.ext
    exact monotoneBranchImageSigned_add u D hD hu sigma.1 tau.1 sigma.2 tau.2
  · intro c sigma
    apply Subtype.ext
    exact monotoneBranchImageSigned_smul u D hD hu c sigma.1 sigma.2

/-- Branch transfer depends on the branch set, not its proof presentation. -/
theorem monotoneBranchTransfer_congr (u : I -> I) (D D' : Set I)
    (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hu : MonotoneBranchOn u D) (hu' : MonotoneBranchOn u D')
    (h : D = D') :
    monotoneBranchTransfer u D hD hu =
      monotoneBranchTransfer u D' hD' hu' := by
  subst D'
  rfl

/-! ## Finite monotonicity partitions and the transfer operator -/

/-- A disjoint finite Borel partition into (not necessarily strict)
monotonicity pieces.  Endpoint assignment is represented by disjointness. -/
structure FiniteMonotonePartition (T : I -> I) where
  idx : Type
  fintype_idx : Fintype idx
  piece : idx -> Set I
  measurable_piece : forall i, MeasurableSet (piece i)
  pairwise_disjoint : Pairwise (Disjoint on piece)
  cover : iUnion piece = Set.univ
  monotone_piece : forall i, MonotoneBranchOn T (piece i)

/-- The finite branch-transfer operator associated to a chosen partition. -/
noncomputable def piecewiseMonotoneTransfer (T : I -> I)
    (P : FiniteMonotonePartition T) :
    NonatomicSignedMeasure →ₗ[Real] NonatomicSignedMeasure := by
  letI := P.fintype_idx
  exact Finset.univ.sum fun i =>
    monotoneBranchTransfer T (P.piece i) (P.measurable_piece i)
      (P.monotone_piece i)

theorem piecewiseMonotoneTransfer_apply (T : I -> I)
    (P : FiniteMonotonePartition T) (sigma : NonatomicSignedMeasure)
    {E : Set I} (hE : MeasurableSet E) :
    (piecewiseMonotoneTransfer T P sigma).1 E =
      (@Finset.univ P.idx P.fintype_idx).sum
        (fun i => sigma.1 (T '' (E ∩ P.piece i))) := by
  classical
  letI := P.fintype_idx
  simp only [piecewiseMonotoneTransfer, LinearMap.sum_apply,
    Submodule.coe_sum]
  rw [VectorMeasure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  exact monotoneBranchImageSigned_apply T (P.piece i)
    (P.measurable_piece i) (P.monotone_piece i) sigma.1 sigma.2 hE

theorem monotoneBranchTransfer_nonnegative (u : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hu : MonotoneBranchOn u D)
    (sigma : NonatomicSignedMeasure) (hsigma : 0 <= sigma.1) :
    0 <= (monotoneBranchTransfer u D hD hu sigma).1 := by
  change 0 ≤ monotoneBranchImageSigned u D hD hu sigma.1 sigma.2
  intro E hE
  rw [VectorMeasure.zero_apply,
    monotoneBranchImageSigned_apply u D hD hu sigma.1 sigma.2 hE]
  apply hsigma
  exact measurableSet_image_of_monotoneBranchOn
    (hE.inter hD) inter_subset_right hu

theorem piecewiseMonotoneTransfer_nonnegative (T : I -> I)
    (P : FiniteMonotonePartition T) (sigma : NonatomicSignedMeasure)
    (hsigma : 0 <= sigma.1) :
    0 <= (piecewiseMonotoneTransfer T P sigma).1 := by
  intro E hE
  rw [VectorMeasure.zero_apply,
    piecewiseMonotoneTransfer_apply T P sigma hE]
  apply Finset.sum_nonneg
  intro i _hi
  apply hsigma
  exact measurableSet_image_of_monotoneBranchOn
    (hE.inter (P.measurable_piece i)) inter_subset_right
      (P.monotone_piece i)

/-- Splitting one branch by a finite measurable partition does not change its
transfer measure. -/
theorem monotoneBranchTransfer_split (T : I -> I)
    (D : Set I) (hD : MeasurableSet D) (hmono : MonotoneBranchOn T D)
    {j : Type} [Fintype j] (Q : j -> Set I)
    (hQmeas : forall k, MeasurableSet (Q k))
    (hQdisj : Pairwise (Disjoint on Q)) (hQcover : iUnion Q = Set.univ) :
    monotoneBranchTransfer T D hD hmono =
      Finset.univ.sum fun k =>
        monotoneBranchTransfer T (D ∩ Q k) (hD.inter (hQmeas k))
          (by
            rcases hmono with hmono | hanti
            · exact Or.inl (hmono.mono inter_subset_left)
            · exact Or.inr (hanti.mono inter_subset_left)) := by
  classical
  apply LinearMap.ext
  intro sigma
  apply Subtype.ext
  ext E hE
  let v : SignedMeasure I :=
    monotoneBranchImageSigned T D hD hmono sigma.1 sigma.2
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
      monotoneBranchImageSigned T D hD hmono sigma.1 sigma.2 E =
        ∑ k, monotoneBranchImageSigned T D hD hmono sigma.1 sigma.2
          (E ∩ Q k) := hv
  change monotoneBranchImageSigned T D hD hmono sigma.1 sigma.2 E = _
  simp only [LinearMap.sum_apply]
  rw [Submodule.coe_sum, VectorMeasure.coe_finsetSum, Finset.sum_apply, hv']
  apply Finset.sum_congr rfl
  intro k _hk
  have hmonoK : MonotoneBranchOn T (D ∩ Q k) := by
    rcases hmono with hmono | hanti
    · exact Or.inl (hmono.mono inter_subset_left)
    · exact Or.inr (hanti.mono inter_subset_left)
  rw [monotoneBranchImageSigned_apply T D hD hmono sigma.1 sigma.2
      (hE.inter (hQmeas k))]
  change sigma.1 (T '' ((E ∩ Q k) ∩ D)) =
    monotoneBranchImageSigned T (D ∩ Q k) (hD.inter (hQmeas k))
      hmonoK sigma.1 sigma.2 E
  rw [monotoneBranchImageSigned_apply T (D ∩ Q k) (hD.inter (hQmeas k))
      hmonoK sigma.1 sigma.2 hE]
  congr 2
  ext x
  simp only [mem_inter_iff]
  tauto

/-- Refining or changing the finite monotonicity partition leaves the
operator unchanged. -/
theorem piecewiseMonotoneTransfer_independent (T : I -> I)
    (P Q : FiniteMonotonePartition T) :
    piecewiseMonotoneTransfer T P = piecewiseMonotoneTransfer T Q := by
  classical
  letI := P.fintype_idx
  letI := Q.fintype_idx
  calc
    piecewiseMonotoneTransfer T P =
        ∑ i, monotoneBranchTransfer T (P.piece i)
          (P.measurable_piece i) (P.monotone_piece i) := rfl
    _ = ∑ i, ∑ j, monotoneBranchTransfer T (P.piece i ∩ Q.piece j)
          ((P.measurable_piece i).inter (Q.measurable_piece j))
          (by
            rcases P.monotone_piece i with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact monotoneBranchTransfer_split T (P.piece i)
        (P.measurable_piece i) (P.monotone_piece i) (Q := Q.piece)
        Q.measurable_piece Q.pairwise_disjoint Q.cover
    _ = ∑ j, ∑ i, monotoneBranchTransfer T (P.piece i ∩ Q.piece j)
          ((P.measurable_piece i).inter (Q.measurable_piece j))
          (by
            rcases P.monotone_piece i with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) := by
      rw [Finset.sum_comm]
    _ = ∑ j, ∑ i, monotoneBranchTransfer T (Q.piece j ∩ P.piece i)
          ((Q.measurable_piece j).inter (P.measurable_piece i))
          (by
            rcases Q.monotone_piece j with h | h
            · exact Or.inl (h.mono inter_subset_left)
            · exact Or.inr (h.mono inter_subset_left)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      apply monotoneBranchTransfer_congr
      exact inter_comm (P.piece i) (Q.piece j)
    _ = ∑ j, monotoneBranchTransfer T (Q.piece j)
          (Q.measurable_piece j) (Q.monotone_piece j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      symm
      exact monotoneBranchTransfer_split T (Q.piece j)
        (Q.measurable_piece j) (Q.monotone_piece j) (Q := P.piece)
        P.measurable_piece P.pairwise_disjoint P.cover
    _ = piecewiseMonotoneTransfer T Q := rfl

/-- Transfer operators are compatible with replacing the underlying map by
an equal function and transporting its partitions. -/
theorem piecewiseMonotoneTransfer_congr {T U : I -> I} (hTU : T = U)
    (P : FiniteMonotonePartition T) (Q : FiniteMonotonePartition U) :
    piecewiseMonotoneTransfer T P = piecewiseMonotoneTransfer U Q := by
  subst U
  exact piecewiseMonotoneTransfer_independent T P Q

/-- On a measurable set contained in one partition piece, only that branch
contributes. -/
theorem piecewiseMonotoneTransfer_apply_of_subset_piece (T : I -> I)
    (P : FiniteMonotonePartition T) (sigma : NonatomicSignedMeasure)
    {E : Set I} (hE : MeasurableSet E) {i : P.idx}
    (hEi : E ⊆ P.piece i) :
    (piecewiseMonotoneTransfer T P sigma).1 E = sigma.1 (T '' E) := by
  classical
  letI := P.fintype_idx
  rw [piecewiseMonotoneTransfer_apply T P sigma hE,
    Finset.sum_eq_single i]
  · rw [inter_eq_left.2 hEi]
  · intro j _hj hji
    have hEmpty : E ∩ P.piece j = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      exact Set.disjoint_left.1 (P.pairwise_disjoint hji)
        hx.2 (hEi hx.1)
    rw [hEmpty, image_empty, VectorMeasure.empty]
  · simp

/-! ## Composition -/

theorem monotoneBranchOn_comp {T U : I -> I} {A B : Set I}
    (hT : MonotoneBranchOn T A) (hU : MonotoneBranchOn U B)
    (hmap : MapsTo T A B) :
    MonotoneBranchOn (U ∘ T) A := by
  rcases hT with hT | hT <;> rcases hU with hU | hU
  · exact Or.inl (hU.comp hT hmap)
  · exact Or.inr (hU.comp_MonotoneOn hT hmap)
  · exact Or.inr (hU.comp_AntitoneOn hT hmap)
  · exact Or.inl (hU.comp hT hmap)

/-- The common refinement by `P_i inter T^{-1}(Q_j)` is a monotonicity
partition for `U ∘ T`. -/
noncomputable def FiniteMonotonePartition.comp {T U : I -> I}
    (hTmeas : Measurable T) (P : FiniteMonotonePartition T)
    (Q : FiniteMonotonePartition U) :
    FiniteMonotonePartition (U ∘ T) := by
  letI := P.fintype_idx
  letI := Q.fintype_idx
  refine
    { idx := P.idx × Q.idx
      fintype_idx := inferInstance
      piece := fun ij => P.piece ij.1 ∩ T ⁻¹' Q.piece ij.2
      measurable_piece := ?_
      pairwise_disjoint := ?_
      cover := ?_
      monotone_piece := ?_ }
  · intro ij
    exact (P.measurable_piece ij.1).inter
      ((Q.measurable_piece ij.2).preimage hTmeas)
  · rintro ⟨i, j⟩ ⟨k, l⟩ hne
    change Disjoint (P.piece i ∩ T ⁻¹' Q.piece j)
      (P.piece k ∩ T ⁻¹' Q.piece l)
    rw [Set.disjoint_left]
    intro x hx hy
    by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := by
        intro hjl
        subst l
        exact hne rfl
      exact Set.disjoint_left.1 (Q.pairwise_disjoint hjl) hx.2 hy.2
    · exact Set.disjoint_left.1 (P.pairwise_disjoint hik) hx.1 hy.1
  · ext x
    constructor
    · intro _hx
      exact Set.mem_univ x
    · intro _hx
      have hxP : x ∈ ⋃ i, P.piece i := by
        rw [P.cover]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.1 hxP with ⟨i, hxi⟩
      have hTxQ : T x ∈ ⋃ j, Q.piece j := by
        rw [Q.cover]
        exact Set.mem_univ (T x)
      rcases Set.mem_iUnion.1 hTxQ with ⟨j, hTxj⟩
      exact Set.mem_iUnion.2 ⟨(i, j), hxi, hTxj⟩
  · intro ij
    apply monotoneBranchOn_comp
    · rcases P.monotone_piece ij.1 with h | h
      · exact Or.inl (h.mono inter_subset_left)
      · exact Or.inr (h.mono inter_subset_left)
    · exact Q.monotone_piece ij.2
    · intro x hx
      exact hx.2

theorem piecewiseMonotoneTransfer_comp_refinement {T U : I -> I}
    (hTmeas : Measurable T) (P : FiniteMonotonePartition T)
    (Q : FiniteMonotonePartition U) :
    piecewiseMonotoneTransfer (U ∘ T) (P.comp hTmeas Q) =
      (piecewiseMonotoneTransfer T P).comp
        (piecewiseMonotoneTransfer U Q) := by
  classical
  letI := P.fintype_idx
  letI := Q.fintype_idx
  apply LinearMap.ext
  intro sigma
  change piecewiseMonotoneTransfer (U ∘ T) (P.comp hTmeas Q) sigma =
    piecewiseMonotoneTransfer T P (piecewiseMonotoneTransfer U Q sigma)
  apply Subtype.ext
  ext E hE
  rw [piecewiseMonotoneTransfer_apply (U ∘ T) (P.comp hTmeas Q) sigma hE,
    piecewiseMonotoneTransfer_apply T P
      (piecewiseMonotoneTransfer U Q sigma) hE]
  change (∑ z : P.idx × Q.idx,
      sigma.1 ((U ∘ T) ''
        (E ∩ (P.piece z.1 ∩ T ⁻¹' Q.piece z.2)))) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  have hImageMeas : MeasurableSet (T '' (E ∩ P.piece i)) :=
    measurableSet_image_of_monotoneBranchOn
      (hE.inter (P.measurable_piece i)) inter_subset_right
        (P.monotone_piece i)
  rw [piecewiseMonotoneTransfer_apply U Q sigma hImageMeas]
  apply Finset.sum_congr rfl
  intro j _hj
  apply congrArg sigma.1
  ext z
  constructor
  · rintro ⟨x, ⟨hxE, hxi, hTxj⟩, rfl⟩
    exact ⟨T x, ⟨⟨x, ⟨hxE, hxi⟩, rfl⟩, hTxj⟩, rfl⟩
  · rintro ⟨y, ⟨⟨x, ⟨hxE, hxi⟩, rfl⟩, hTxj⟩, rfl⟩
    exact ⟨x, ⟨hxE, hxi, hTxj⟩, rfl⟩

/-- Partition-independent composition law, in the manuscript's contravariant
operator order: `T_(U o T) = T_T T_U`. -/
theorem piecewiseMonotoneTransfer_comp {T U : I -> I}
    (hTmeas : Measurable T) (P : FiniteMonotonePartition T)
    (Q : FiniteMonotonePartition U)
    (R : FiniteMonotonePartition (U ∘ T)) :
    piecewiseMonotoneTransfer (U ∘ T) R =
      (piecewiseMonotoneTransfer T P).comp
        (piecewiseMonotoneTransfer U Q) := by
  rw [piecewiseMonotoneTransfer_independent (U ∘ T) R (P.comp hTmeas Q)]
  exact piecewiseMonotoneTransfer_comp_refinement hTmeas P Q

theorem piecewiseMonotoneTransfer_commute {T U : I -> I}
    (hTmeas : Measurable T) (hUmeas : Measurable U)
    (P : FiniteMonotonePartition T) (Q : FiniteMonotonePartition U)
    (RTU : FiniteMonotonePartition (U ∘ T))
    (RUT : FiniteMonotonePartition (T ∘ U)) (hcomm : Commute T U) :
    (piecewiseMonotoneTransfer T P).comp
        (piecewiseMonotoneTransfer U Q) =
      (piecewiseMonotoneTransfer U Q).comp
        (piecewiseMonotoneTransfer T P) := by
  have hEq : T ∘ U = U ∘ T := by
    funext x
    exact hcomm x
  have hmiddle :
      piecewiseMonotoneTransfer (U ∘ T) RTU =
        piecewiseMonotoneTransfer (T ∘ U) RUT := by
    exact piecewiseMonotoneTransfer_congr hEq.symm RTU RUT
  calc
    (piecewiseMonotoneTransfer T P).comp
        (piecewiseMonotoneTransfer U Q) =
      piecewiseMonotoneTransfer (U ∘ T) RTU :=
        (piecewiseMonotoneTransfer_comp hTmeas P Q RTU).symm
    _ = piecewiseMonotoneTransfer (T ∘ U) RUT := hmiddle
    _ = (piecewiseMonotoneTransfer U Q).comp
        (piecewiseMonotoneTransfer T P) :=
      piecewiseMonotoneTransfer_comp hUmeas Q P RUT

/-! ## The Stieltjes measure of a semiconjugacy -/

/-- The Lebesgue--Stieltjes measure whose interval increments are those of a
monotone coordinate `psi`. -/
noncomputable def semiconjugacyMeasure (psi : I -> Real) (hpsi : Monotone psi) :
    Measure I :=
  hpsi.stieltjesFunction.measure

theorem semiconjugacyMeasure_finite (psi : I -> Real) (hpsi : Monotone psi) :
    IsFiniteMeasure (semiconjugacyMeasure psi hpsi) := by
  let f : StieltjesFunction I := hpsi.stieltjesFunction
  change IsFiniteMeasure f.measure
  apply f.isFiniteMeasure_of_forall_abs_le
    (C := max |f leftEndpoint| |f rightEndpoint|)
  intro x
  apply abs_le_max_abs_abs
  · exact f.mono x.property.1
  · exact f.mono x.property.2

theorem semiconjugacyMeasure_Icc (psi : I -> Real) (hpsi : Monotone psi)
    (hcont : Continuous psi) {a b : I} (_hab : a <= b) :
    semiconjugacyMeasure psi hpsi (Set.Icc a b) =
      ENNReal.ofReal (psi b - psi a) := by
  let f : StieltjesFunction I := hpsi.stieltjesFunction
  have hf : ∀ x, f x = psi x := by
    intro x
    rw [show f x = Function.rightLim psi x from
      Monotone.stieltjesFunction_eq hpsi x]
    exact hcont.continuousAt.continuousWithinAt.rightLim_eq
  have hleft : Function.leftLim (fun x => f x) a = psi a := by
    rw [show (fun x => f x) = psi from funext hf]
    exact hcont.continuousAt.continuousWithinAt.leftLim_eq
  rw [semiconjugacyMeasure, StieltjesFunction.measure_Icc, hf b, hleft]

theorem semiconjugacyMeasure_noAtoms (psi : I -> Real) (hpsi : Monotone psi)
    (hcont : Continuous psi) (x : I) :
    semiconjugacyMeasure psi hpsi {x} = 0 := by
  let f : StieltjesFunction I := hpsi.stieltjesFunction
  have hf : ∀ y, f y = psi y := by
    intro y
    rw [show f y = Function.rightLim psi y from
      Monotone.stieltjesFunction_eq hpsi y]
    exact hcont.continuousAt.continuousWithinAt.rightLim_eq
  have hleft : Function.leftLim (fun y => f y) x = psi x := by
    rw [show (fun y => f y) = psi from funext hf]
    exact hcont.continuousAt.continuousWithinAt.leftLim_eq
  rw [semiconjugacyMeasure, StieltjesFunction.measure_singleton, hf x, hleft,
    sub_self, ENNReal.ofReal_zero]

theorem semiconjugacyMeasure_univ (psi : I -> Real) (hpsi : Monotone psi)
    (hcont : Continuous psi) :
    semiconjugacyMeasure psi hpsi Set.univ =
      ENNReal.ofReal (psi rightEndpoint - psi leftEndpoint) := by
  have hUniv : (Set.univ : Set I) = Set.Icc leftEndpoint rightEndpoint := by
    ext x
    constructor
    · intro _hx
      exact ⟨x.property.1, x.property.2⟩
    · intro _hx
      exact Set.mem_univ x
  rw [hUniv]
  exact semiconjugacyMeasure_Icc psi hpsi hcont (by
    exact Subtype.mk_le_mk.2 zero_le_one)

/-- The Stieltjes measure, viewed as an element of `M(I)`. -/
noncomputable def semiconjugacySignedMeasure (psi : I -> Real)
    (hpsi : Monotone psi) (hcont : Continuous psi) :
    NonatomicSignedMeasure := by
  letI : IsFiniteMeasure (semiconjugacyMeasure psi hpsi) :=
    semiconjugacyMeasure_finite psi hpsi
  exact
    ⟨(semiconjugacyMeasure psi hpsi).toSignedMeasure,
      fun x => by
        rw [Measure.toSignedMeasure_apply_measurable (MeasurableSet.singleton x),
          measureReal_def, semiconjugacyMeasure_noAtoms psi hpsi hcont x]
        simp⟩

theorem semiconjugacySignedMeasure_Icc (psi : I -> Real)
    (hpsi : Monotone psi) (hcont : Continuous psi) {a b : I} (hab : a <= b) :
    (semiconjugacySignedMeasure psi hpsi hcont).1 (Set.Icc a b) =
      psi b - psi a := by
  letI : IsFiniteMeasure (semiconjugacyMeasure psi hpsi) :=
    semiconjugacyMeasure_finite psi hpsi
  change (semiconjugacyMeasure psi hpsi).toSignedMeasure (Set.Icc a b) = _
  rw [Measure.toSignedMeasure_apply_measurable measurableSet_Icc,
    measureReal_def, semiconjugacyMeasure_Icc psi hpsi hcont hab,
    ENNReal.toReal_ofReal (sub_nonneg.2 (hpsi hab))]

/-- Equality on interval intersections with a branch upgrades to equality on
all Borel sets by finite-measure uniqueness. -/
theorem branch_borel_scaling_of_Icc_scaling (T : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hmono : MonotoneBranchOn T D)
    (mu : Measure I) [IsFiniteMeasure mu] [NoAtoms mu]
    (lambda : Real) (_hlambda : 0 <= lambda)
    (hIcc : forall a b : I, a <= b ->
      mu (T '' (Set.Icc a b ∩ D)) =
        ENNReal.ofReal lambda * mu (Set.Icc a b ∩ D))
    {E : Set I} (hE : MeasurableSet E) :
    mu (T '' (E ∩ D)) = ENNReal.ofReal lambda * mu (E ∩ D) := by
  let sigma : NonatomicSignedMeasure :=
    ⟨mu.toSignedMeasure, fun x => by
      rw [Measure.toSignedMeasure_apply_measurable (MeasurableSet.singleton x),
        measureReal_def]
      simp⟩
  let v : SignedMeasure I :=
    (monotoneBranchTransfer T D hD hmono sigma).1
  have hsigma : 0 ≤ sigma.1 := Measure.zero_le_toSignedMeasure mu
  have hv : 0 ≤ v :=
    monotoneBranchTransfer_nonnegative T D hD hmono sigma hsigma
  have hv_univ : 0 ≤[Set.univ] v := by
    simpa only [VectorMeasure.restrict_univ] using hv
  let nu : Measure I :=
    v.toMeasureOfZeroLE Set.univ MeasurableSet.univ hv_univ
  have hv_apply {A : Set I} (hA : MeasurableSet A) :
      v A = mu.real (T '' (A ∩ D)) := by
    change monotoneBranchImageSigned T D hD hmono sigma.1 sigma.2 A = _
    rw [monotoneBranchImageSigned_apply T D hD hmono sigma.1 sigma.2 hA]
    exact Measure.toSignedMeasure_apply_measurable
      (measurableSet_image_of_monotoneBranchOn
        (hA.inter hD) inter_subset_right hmono)
  have hnu_real {A : Set I} (hA : MeasurableSet A) :
      nu.real A = mu.real (T '' (A ∩ D)) := by
    rw [SignedMeasure.toMeasureOfZeroLE_real_apply v hv_univ
      MeasurableSet.univ hA, univ_inter, hv_apply hA]
  have hnu_apply {A : Set I} (hA : MeasurableSet A) :
      nu A = mu (T '' (A ∩ D)) := by
    apply (measureReal_eq_measureReal_iff).mp
    exact hnu_real hA
  have hnu : nu = ENNReal.ofReal lambda • mu.restrict D := by
    apply Measure.ext_of_Icc
    intro a b hab
    rw [hnu_apply measurableSet_Icc, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Icc]
    exact hIcc a b hab
  have hvalue := congrArg (fun m : Measure I => m E) hnu
  change nu E = (ENNReal.ofReal lambda • mu.restrict D) E at hvalue
  rw [hnu_apply hE, Measure.smul_apply, Measure.restrict_apply hE] at hvalue
  exact hvalue

/-- The constant-slope interval identity supplied by a semiconjugacy yields
the branchwise Borel scaling needed by the transfer operator. -/
theorem semiconjugacy_branch_borel_scaling (T : I -> I) (D : Set I)
    (hD : MeasurableSet D) (hmono : MonotoneBranchOn T D)
    (psi : I -> Real) (hpsi : Monotone psi) (hcont : Continuous psi)
    (lambda : Real) (hlambda : 0 <= lambda)
    (hIcc : forall a b : I, a <= b ->
      semiconjugacyMeasure psi hpsi (T '' (Set.Icc a b ∩ D)) =
        ENNReal.ofReal lambda *
          semiconjugacyMeasure psi hpsi (Set.Icc a b ∩ D))
    {E : Set I} (hE : MeasurableSet E) :
    semiconjugacyMeasure psi hpsi (T '' (E ∩ D)) =
      ENNReal.ofReal lambda *
        semiconjugacyMeasure psi hpsi (E ∩ D) := by
  letI : IsFiniteMeasure (semiconjugacyMeasure psi hpsi) :=
    semiconjugacyMeasure_finite psi hpsi
  letI : NoAtoms (semiconjugacyMeasure psi hpsi) := by
    refine ⟨?_⟩
    intro x
    exact semiconjugacyMeasure_noAtoms psi hpsi hcont x
  exact branch_borel_scaling_of_Icc_scaling T D hD hmono
    (semiconjugacyMeasure psi hpsi) lambda hlambda hIcc hE

/-- Summing the branchwise constant-slope identities gives the expanding
eigenmeasure of the finite-lap transfer operator. -/
theorem semiconjugacySignedMeasure_eigen (T : I -> I)
    (P : FiniteMonotonePartition T) (psi : I -> Real)
    (hpsi : Monotone psi) (hcont : Continuous psi)
    (lambda : Real) (hlambda : 0 <= lambda)
    (hscale : forall i (E : Set I), MeasurableSet E ->
      semiconjugacyMeasure psi hpsi (T '' (E ∩ P.piece i)) =
        ENNReal.ofReal lambda *
          semiconjugacyMeasure psi hpsi (E ∩ P.piece i)) :
    piecewiseMonotoneTransfer T P
        (semiconjugacySignedMeasure psi hpsi hcont) =
      lambda • semiconjugacySignedMeasure psi hpsi hcont := by
  classical
  letI := P.fintype_idx
  let mu : Measure I := semiconjugacyMeasure psi hpsi
  letI : IsFiniteMeasure mu := semiconjugacyMeasure_finite psi hpsi
  apply Subtype.ext
  ext E hE
  have hBranchImageMeas : ∀ i,
      MeasurableSet (T '' (E ∩ P.piece i)) := fun i =>
    measurableSet_image_of_monotoneBranchOn
      (hE.inter (P.measurable_piece i)) inter_subset_right
        (P.monotone_piece i)
  have hscaleReal : ∀ i,
      mu.real (T '' (E ∩ P.piece i)) =
        lambda * mu.real (E ∩ P.piece i) := by
    intro i
    simp only [mu, measureReal_def]
    rw [hscale i E hE, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hlambda]
  have hpartsMeas : ∀ i, MeasurableSet (E ∩ P.piece i) := fun i =>
    hE.inter (P.measurable_piece i)
  have hpartsDisj : Pairwise (Disjoint on fun i => E ∩ P.piece i) := by
    intro i j hij
    change Disjoint (E ∩ P.piece i) (E ∩ P.piece j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.1 (P.pairwise_disjoint hij) hxi.2 hxj.2
  have hpartsCover : E = ⋃ i, E ∩ P.piece i := by
    ext x
    constructor
    · intro hxE
      have hxP : x ∈ ⋃ i, P.piece i := by
        rw [P.cover]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.1 hxP with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, hxE, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hxE, _hxi⟩
      exact hxE
  have hsignedSum : mu.toSignedMeasure E =
      ∑ i, mu.toSignedMeasure (E ∩ P.piece i) := by
    calc
      mu.toSignedMeasure E =
          mu.toSignedMeasure (⋃ i, E ∩ P.piece i) :=
        congrArg mu.toSignedMeasure hpartsCover
      _ = ∑' i, mu.toSignedMeasure (E ∩ P.piece i) :=
        VectorMeasure.of_disjoint_iUnion hpartsMeas hpartsDisj
      _ = ∑ i, mu.toSignedMeasure (E ∩ P.piece i) := tsum_fintype _
  have hrealSum : mu.real E = ∑ i, mu.real (E ∩ P.piece i) := by
    rw [Measure.toSignedMeasure_apply_measurable hE] at hsignedSum
    simpa only [Measure.toSignedMeasure_apply_measurable (hpartsMeas _)]
      using hsignedSum
  rw [piecewiseMonotoneTransfer_apply T P
    (semiconjugacySignedMeasure psi hpsi hcont) hE]
  change (∑ i, mu.toSignedMeasure (T '' (E ∩ P.piece i))) =
    (lambda • mu.toSignedMeasure) E
  rw [VectorMeasure.smul_apply]
  calc
    (∑ i, mu.toSignedMeasure (T '' (E ∩ P.piece i))) =
        ∑ i, mu.real (T '' (E ∩ P.piece i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact Measure.toSignedMeasure_apply_measurable (hBranchImageMeas i)
    _ = ∑ i, lambda * mu.real (E ∩ P.piece i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hscaleReal i
    _ = lambda * ∑ i, mu.real (E ∩ P.piece i) := by
      rw [Finset.mul_sum]
    _ = lambda * mu.real E := by rw [hrealSum]
    _ = lambda * mu.toSignedMeasure E := by
      rw [Measure.toSignedMeasure_apply_measurable hE]

end CommutingInterval
