import CommutingInterval.PiecewiseMonotoneVariation
import CommutingInterval.ParryDefs
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Simultaneous eigenmeasures for commuting piecewise-monotone maps

This file isolates the finite-dimensional argument in the direct
piecewise-monotone proof.  Its input is an expanding atomless probability
eigenmeasure for a returned product; no resolvent or existence theorem is
imported here.  The declarations are ordered by dependency and the complete
proof skeleton is kept visible from the outset.
-/

noncomputable section

namespace CommutingInterval

open Function Set MeasureTheory
open scoped BigOperators ENNReal

/-! ## Transfer algebra and iterates -/

/-- The complex transfer endomorphism on nonatomic complex measures. -/
noncomputable def complexTransfer
    (T : IntervalMap) (P : MonotonicityPartition T) :
    Module.End ℂ (NonatomicVectorMeasure ℂ) :=
  piecewiseMonotoneTransferVector T P.toFiniteMonotonePartition

/-- Transfer reverses composition, independently of the chosen partitions. -/
theorem complexTransfer_comp
    {T U : IntervalMap}
    (PT : MonotonicityPartition T) (PU : MonotonicityPartition U)
    (PC : MonotonicityPartition (U ∘ T)) :
    complexTransfer (U ∘ T) PC =
      (complexTransfer T PT).comp (complexTransfer U PU) := by
  exact piecewiseMonotoneTransferVector_comp PT.measurable
    PT.toFiniteMonotonePartition PU.toFiniteMonotonePartition
    PC.toFiniteMonotonePartition

/-- Replacing the underlying map by an equal function does not change
complex transfer. -/
theorem complexTransfer_congr
    {T U : IntervalMap} (hTU : T = U)
    (PT : MonotonicityPartition T) (PU : MonotonicityPartition U) :
    complexTransfer T PT = complexTransfer U PU := by
  subst U
  exact piecewiseMonotoneTransferVector_independent (K := ℂ) T
    PT.toFiniteMonotonePartition PU.toFiniteMonotonePartition

/-- Continuous finite-piece piecewise-monotonicity is stable under iteration. -/
theorem FinitePieceMonotone.iterateMap
    {T : IntervalMap} (hT : FinitePieceMonotone T) (n : ℕ) :
    FinitePieceMonotone (iterateMap T n) := by
  induction n with
  | zero =>
      simpa [CommutingInterval.iterateMap] using
        (FinitePieceMonotone.of_monotone continuous_id monotone_id)
  | succ n ih =>
      rw [show CommutingInterval.iterateMap T (Nat.succ n) =
          T ∘ CommutingInterval.iterateMap T n by
        exact Function.iterate_succ' T n]
      exact hT.comp ih

/-- The transfer of the identity map is the identity endomorphism. -/
theorem complexTransfer_id (P : MonotonicityPartition (id : IntervalMap)) :
    complexTransfer (id : IntervalMap) P = 1 := by
  classical
  let Q : FiniteMonotonePartition (id : IntervalMap) :=
    { idx := PUnit
      fintype_idx := inferInstance
      piece := fun _ => Set.univ
      measurable_piece := fun _ => MeasurableSet.univ
      pairwise_disjoint := by
        intro i j hij
        exact (hij (Subsingleton.elim i j)).elim
      cover := by
        apply Set.eq_univ_of_forall
        intro x
        exact Set.mem_iUnion.2 ⟨PUnit.unit, Set.mem_univ x⟩
      monotone_piece := fun _ => Or.inl fun _ _ _ _ hxy => hxy }
  unfold complexTransfer
  rw [piecewiseMonotoneTransferVector_independent (K := ℂ)
    (id : IntervalMap) P.toFiniteMonotonePartition Q]
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  ext E hE
  rw [piecewiseMonotoneTransferVector_apply (id : IntervalMap) Q z hE]
  simp [Q]

/-- The transfer of an iterate is the corresponding power of transfer. -/
theorem complexTransfer_iterate
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (PT : MonotonicityPartition T) (n : ℕ)
    (Pn : MonotonicityPartition (iterateMap T n)) :
    complexTransfer (iterateMap T n) Pn = (complexTransfer T PT) ^ n := by
  classical
  induction n with
  | zero =>
      change MonotonicityPartition (id : IntervalMap) at Pn
      change complexTransfer (id : IntervalMap) Pn = 1
      exact complexTransfer_id Pn
  | succ n ih =>
      let Pprev : MonotonicityPartition
          (CommutingInterval.iterateMap T n) :=
        Classical.choice (hT.iterateMap n).2
      have heq : CommutingInterval.iterateMap T (Nat.succ n) =
          T ∘ CommutingInterval.iterateMap T n :=
        Function.iterate_succ' T n
      let Pcomp : MonotonicityPartition
          (T ∘ CommutingInterval.iterateMap T n) := heq ▸ Pn
      have htransport :
          complexTransfer (CommutingInterval.iterateMap T (Nat.succ n)) Pn =
            complexTransfer (T ∘ CommutingInterval.iterateMap T n) Pcomp := by
        exact complexTransfer_congr heq Pn Pcomp
      calc
        complexTransfer (CommutingInterval.iterateMap T (Nat.succ n)) Pn =
            complexTransfer (T ∘ CommutingInterval.iterateMap T n) Pcomp :=
          htransport
        _ = (complexTransfer (CommutingInterval.iterateMap T n) Pprev).comp
              (complexTransfer T PT) :=
          complexTransfer_comp Pprev PT Pcomp
        _ = ((complexTransfer T PT) ^ n).comp (complexTransfer T PT) := by
          rw [ih Pprev]
        _ = (complexTransfer T PT) ^ (Nat.succ n) := by
          rw [pow_succ]
          rfl

/-- Commuting finite-piece maps have commuting complex transfers. -/
theorem complexTransfer_commute
    {T U : IntervalMap} (hT : FinitePieceMonotone T)
    (hU : FinitePieceMonotone U) (hcomm : Commute T U)
    (PT : MonotonicityPartition T) (PU : MonotonicityPartition U) :
    Function.Commute (complexTransfer T PT) (complexTransfer U PU) := by
  let PTU : MonotonicityPartition (U ∘ T) :=
    Classical.choice (hU.comp hT).2
  let PUT : MonotonicityPartition (T ∘ U) :=
    Classical.choice (hT.comp hU).2
  have hmaps : U ∘ T = T ∘ U := by
    funext x
    exact (hcomm x).symm
  have hlinear :
      (complexTransfer T PT).comp (complexTransfer U PU) =
        (complexTransfer U PU).comp (complexTransfer T PT) := by
    calc
      (complexTransfer T PT).comp (complexTransfer U PU) =
          complexTransfer (U ∘ T) PTU :=
        (complexTransfer_comp PT PU PTU).symm
      _ = complexTransfer (T ∘ U) PUT :=
        complexTransfer_congr hmaps PTU PUT
      _ = (complexTransfer U PU).comp (complexTransfer T PT) :=
        complexTransfer_comp PU PT PUT
  intro z
  exact LinearMap.congr_fun hlinear z

/-! ## Expanding product eigenmeasure input -/

/-- The product of the two returned words of common positive length `L`. -/
def returnedProductMap (P Q : IntervalMap) (L : ℕ) : IntervalMap :=
  iterateMap P L ∘ iterateMap Q L

/-- All data consumed from an external expanding-eigenprobability theorem. -/
structure PiecewiseMonotoneProductEigenData
    (P Q : IntervalMap) (L : ℕ) where
  finitePiece_P : FinitePieceMonotone P
  finitePiece_Q : FinitePieceMonotone Q
  commute : Commute P Q
  L_pos : 0 < L
  partitionP : MonotonicityPartition P
  partitionQ : MonotonicityPartition Q
  partitionProduct : MonotonicityPartition (returnedProductMap P Q L)
  lambda : ℝ
  one_lt_lambda : 1 < lambda
  measure : Measure I
  probability : measure Set.univ = 1
  noAtoms : ∀ x : I, measure {x} = 0
  product_eigen :
    transferMeasure (returnedProductMap P Q L) partitionProduct measure noAtoms =
      ENNReal.ofReal lambda • measure

namespace PiecewiseMonotoneProductEigenData

variable {P Q : IntervalMap} {L : ℕ}

/-- The returned product remains continuous finite-piece piecewise monotone. -/
theorem finitePiece_product (D : PiecewiseMonotoneProductEigenData P Q L) :
    FinitePieceMonotone (returnedProductMap P Q L) := by
  exact (D.finitePiece_P.iterateMap L).comp
    (D.finitePiece_Q.iterateMap L)

/-- The product transfer is the `L`th power of the two commuting transfers. -/
theorem complexTransfer_product_eq
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    complexTransfer (returnedProductMap P Q L) D.partitionProduct =
      (complexTransfer Q D.partitionQ) ^ L *
        (complexTransfer P D.partitionP) ^ L := by
  let PPL : MonotonicityPartition (CommutingInterval.iterateMap P L) :=
    Classical.choice (D.finitePiece_P.iterateMap L).2
  let PQL : MonotonicityPartition (CommutingInterval.iterateMap Q L) :=
    Classical.choice (D.finitePiece_Q.iterateMap L).2
  calc
    complexTransfer (returnedProductMap P Q L) D.partitionProduct =
        (complexTransfer (CommutingInterval.iterateMap Q L) PQL).comp
          (complexTransfer (CommutingInterval.iterateMap P L) PPL) :=
      complexTransfer_comp PQL PPL D.partitionProduct
    _ = ((complexTransfer Q D.partitionQ) ^ L).comp
          ((complexTransfer P D.partitionP) ^ L) := by
      rw [complexTransfer_iterate D.finitePiece_Q D.partitionQ L PQL,
        complexTransfer_iterate D.finitePiece_P D.partitionP L PPL]
    _ = (complexTransfer Q D.partitionQ) ^ L *
          (complexTransfer P D.partitionP) ^ L := rfl

end PiecewiseMonotoneProductEigenData

/-! ## Complexification and the product eigenspace -/

/-- A finite positive measure regarded as a complex measure. -/
noncomputable def measureComplexification
    (μ : Measure I) [IsFiniteMeasure μ] : ComplexMeasure I :=
  μ.toSignedMeasure.toComplexMeasure 0

theorem measureComplexification_apply
    (μ : Measure I) [IsFiniteMeasure μ]
    {E : Set I} (hE : MeasurableSet E) :
    measureComplexification μ E = (μ.real E : ℂ) := by
  change μ.toSignedMeasure.toComplexMeasure 0 E = (μ.real E : ℂ)
  rw [SignedMeasure.toComplexMeasure_apply,
    Measure.toSignedMeasure_apply_measurable hE,
    VectorMeasure.zero_apply]
  rfl

theorem variation_measureComplexification
    (μ : Measure I) [IsFiniteMeasure μ] :
    (measureComplexification μ).variation = μ := by
  apply le_antisymm
  · apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    rw [measureComplexification_apply μ hE, ← ofReal_norm]
    simp [measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ E)]
  · refine Measure.le_intro fun E hE _ => ?_
    calc
      μ E = ‖measureComplexification μ E‖ₑ := by
        rw [measureComplexification_apply μ hE, ← ofReal_norm]
        simp [measureReal_def,
          ENNReal.ofReal_toReal (measure_ne_top μ E)]
      _ ≤ (measureComplexification μ).variation E :=
        VectorMeasure.enorm_measure_le_variation
          (measureComplexification μ) E

theorem measureComplexification_noAtoms
    (μ : Measure I) [IsFiniteMeasure μ]
    (hμ : ∀ x : I, μ {x} = 0) :
    VectorNoAtoms (measureComplexification μ) := by
  intro x
  rw [measureComplexification_apply μ (MeasurableSet.singleton x),
    measureReal_def, hμ x]
  simp

/-- The complex `lambda`-eigenspace of the returned product transfer. -/
def productEigenspace
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    Submodule ℂ (NonatomicVectorMeasure ℂ) where
  carrier := {z |
    complexTransfer (returnedProductMap P Q L) D.partitionProduct z =
      (D.lambda : ℂ) • z}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add, hx, hy, smul_add]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smul, hx]
    exact smul_comm c (D.lambda : ℂ) x

noncomputable instance productEigenspace.instAddCommGroup
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    AddCommGroup (productEigenspace D) :=
  @Submodule.addCommGroup ℂ (NonatomicVectorMeasure ℂ)
    inferInstance inferInstance inferInstance (productEigenspace D)

/-- The positive product eigenmeasure embedded in the complex eigenspace. -/
structure ComplexProductEigenData
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) where
  vector : productEigenspace D
  vector_ne_zero : vector ≠ 0
  variation_eq_measure : vector.1.1.variation = D.measure

theorem complexifyProductEigenmeasure
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    Nonempty (ComplexProductEigenData D) := by
  letI : IsFiniteMeasure D.measure :=
    ⟨by rw [D.probability]; exact ENNReal.one_lt_top⟩
  let z0 : ComplexMeasure I := measureComplexification D.measure
  have hz0 := measureComplexification_noAtoms D.measure D.noAtoms
  let z : NonatomicVectorMeasure ℂ := ⟨z0, hz0⟩
  have heigen :
      complexTransfer (returnedProductMap P Q L) D.partitionProduct z =
        (D.lambda : ℂ) • z := by
    apply Subtype.ext
    ext E hE
    change
      (piecewiseMonotoneTransferVector
        (returnedProductMap P Q L)
        D.partitionProduct.toFiniteMonotonePartition z).1 E =
          (D.lambda : ℂ) * z.1 E
    rw [piecewiseMonotoneTransferVector_apply
      (returnedProductMap P Q L)
      D.partitionProduct.toFiniteMonotonePartition z hE]
    let F := D.partitionProduct.toFiniteMonotonePartition
    letI := F.fintype_idx
    have hterm (i : F.idx) :
        MeasurableSet
          (returnedProductMap P Q L '' (E ∩ F.piece i)) :=
      measurableSet_image_of_monotoneBranchOn
        (hE.inter (F.measurable_piece i)) inter_subset_right
        (F.monotone_piece i)
    have hpositive := congrArg (fun m : Measure I => m E) D.product_eigen
    change
      piecewiseMonotoneTransferMeasure
        (returnedProductMap P Q L) F D.measure D.noAtoms E =
          (ENNReal.ofReal D.lambda • D.measure) E at hpositive
    rw [piecewiseMonotoneTransferMeasure_apply
      (returnedProductMap P Q L) F D.measure D.noAtoms hE,
      Measure.smul_apply, smul_eq_mul] at hpositive
    have hreal := congrArg ENNReal.toReal hpositive
    rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top D.measure _),
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (zero_le_one.trans D.one_lt_lambda.le),
      ← measureReal_def] at hreal
    calc
      ∑ i : F.idx,
          z.1 (returnedProductMap P Q L '' (E ∩ F.piece i)) =
          ∑ i : F.idx,
            (D.measure.real
              (returnedProductMap P Q L '' (E ∩ F.piece i)) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        change z0 (returnedProductMap P Q L '' (E ∩ F.piece i)) = _
        exact measureComplexification_apply D.measure (hterm i)
      _ = (D.lambda : ℂ) * (D.measure.real E : ℂ) := by
        exact_mod_cast hreal
      _ = (D.lambda : ℂ) * z.1 E := by
        congr 1
        change (D.measure.real E : ℂ) = z0 E
        exact (measureComplexification_apply D.measure hE).symm
  let ze : productEigenspace D := ⟨z, heigen⟩
  have hzne : ze ≠ 0 := by
    intro hz
    have hz0eq : z0 = 0 :=
      congrArg (fun w : productEigenspace D => w.1.1) hz
    have hvar := congrArg VectorMeasure.variation hz0eq
    rw [variation_measureComplexification,
      VectorMeasure.variation_zero] at hvar
    have huniv := congrArg (fun m : Measure I => m Set.univ) hvar
    simpa [D.probability] using huniv
  exact
    ⟨⟨ze, hzne, variation_measureComplexification D.measure⟩⟩

/-! ## Endpoint coordinates and finite-dimensionality -/

/-- A power with expansion factor greater than two, together with an
explicit monotonicity partition for that iterate. -/
structure ExpandingIterateData
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) where
  N : ℕ
  N_pos : 0 < N
  lambda_pow_gt_two : 2 < D.lambda ^ N
  partition : MonotonicityPartition
    (iterateMap (returnedProductMap P Q L) N)

theorem expandingIterateData_exists
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    Nonempty (ExpandingIterateData D) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 : ℝ) D.one_lt_lambda
  have hNpos : 0 < N := by
    apply Nat.pos_of_ne_zero
    intro hNzero
    subst N
    norm_num at hN
  let PN : MonotonicityPartition
      (iterateMap (returnedProductMap P Q L) N) :=
    Classical.choice (D.finitePiece_product.iterateMap N).2
  exact ⟨⟨N, hNpos, hN, PN⟩⟩

/-- The finite set of real endpoints in the selected iterate partition. -/
abbrev ExpandingEndpoint
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    (X : ExpandingIterateData D) :=
  {x : ℝ // x ∈ X.partition.partition.points}

def ExpandingEndpoint.toI
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    {X : ExpandingIterateData D} (x : ExpandingEndpoint X) : I :=
  ⟨x.1, X.partition.partition.points_subset x.2⟩

/-- The cumulative value `z([0,x])`. -/
def complexCumulative (z : ComplexMeasure I) (x : I) : ℂ :=
  z (Set.Icc leftEndpoint x)

/-- Evaluation of cumulative values at every selected partition endpoint. -/
noncomputable def cumulativeEndpointCoordinate
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    (X : ExpandingIterateData D) :
    productEigenspace D →ₗ[ℂ] (ExpandingEndpoint X → ℂ) where
  toFun z x := complexCumulative z.1 x.toI
  map_add' z w := by
    funext x
    simp [complexCumulative, VectorMeasure.add_apply]
  map_smul' c z := by
    funext x
    simp [complexCumulative, VectorMeasure.smul_apply]

/-- The least uniform real bound on the cumulative values. -/
noncomputable def cumulativeNormSup (z : ComplexMeasure I) : ℝ :=
  sSup (Set.range fun x : I => ‖complexCumulative z x‖)

theorem cumulativeNormSup_nonneg (z : ComplexMeasure I) :
    0 ≤ cumulativeNormSup z := by
  letI : IsFiniteMeasure z.variation := complex_variation_isFinite z
  have hbdd : BddAbove
      (Set.range fun x : I => ‖complexCumulative z x‖) := by
    refine ⟨z.variation.real Set.univ, ?_⟩
    rintro y ⟨x, rfl⟩
    exact (VectorMeasure.norm_measure_le_variation).trans
      (measureReal_mono (Set.subset_univ _))
  have hmem : ‖complexCumulative z (0 : I)‖ ∈
      Set.range (fun x : I => ‖complexCumulative z x‖) :=
    ⟨0, rfl⟩
  exact (norm_nonneg _).trans (le_csSup hbdd hmem)

theorem complexCumulative_norm_le_sup (z : ComplexMeasure I) (x : I) :
    ‖complexCumulative z x‖ ≤ cumulativeNormSup z := by
  letI : IsFiniteMeasure z.variation := complex_variation_isFinite z
  apply le_csSup
  · refine ⟨z.variation.real Set.univ, ?_⟩
    rintro y ⟨u, rfl⟩
    exact (VectorMeasure.norm_measure_le_variation).trans
      (measureReal_mono (Set.subset_univ _))
  · exact ⟨x, rfl⟩

/-- On a measurable subset of one assigned lap, complex transfer is the
literal image vector measure. -/
private theorem complexTransfer_apply_of_subset_assignedCell
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (z : NonatomicVectorMeasure ℂ)
    (q : PT.partition.LapIndex) {E : Set I}
    (hE : MeasurableSet E) (hEq : E ⊆ q.assignedCell) :
    (complexTransfer T PT z).1 E = z.1 (T '' E) := by
  classical
  let F := PT.toFiniteMonotonePartition
  letI := F.fintype_idx
  change E ⊆ F.piece q at hEq
  change (piecewiseMonotoneTransferVector T F z).1 E = _
  rw [piecewiseMonotoneTransferVector_apply T F z hE]
  calc
    ∑ i, z.1 (T '' (E ∩ F.piece i)) =
        z.1 (T '' (E ∩ F.piece q)) := by
      apply Finset.sum_eq_single q
      · intro r _hr hrq
        have hEmpty : E ∩ F.piece r = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro x hx
          exact Set.disjoint_left.1 (F.pairwise_disjoint hrq)
            hx.2 (hEq hx.1)
        rw [hEmpty, image_empty, VectorMeasure.empty]
      · intro hq
        exact (hq (Finset.mem_univ q)).elim
    _ = z.1 (T '' E) := by rw [inter_eq_left.2 hEq]

/-- For a nonatomic complex measure, the mass of a closed interval is the
difference of its two left cumulative values. -/
private theorem complexMeasure_Icc_eq_cumulative_sub
    (z : ComplexMeasure I) (hz : VectorNoAtoms z)
    {a b : I} (hab : a ≤ b) :
    z (Set.Icc a b) = complexCumulative z b - complexCumulative z a := by
  have hleft : leftEndpoint ≤ a := a.property.1
  have hwhole :
      z (Set.Icc leftEndpoint b) =
        z (Set.Icc leftEndpoint a) + z (Set.Ioc a b) := by
    rw [← Set.Icc_union_Ioc_eq_Icc hleft hab,
      VectorMeasure.of_union (by
        rw [Set.disjoint_left]
        intro x hx hxa
        exact (not_lt_of_ge hx.2) hxa.1)
        measurableSet_Icc measurableSet_Ioc]
  have hpart : z (Set.Icc a b) = z (Set.Ioc a b) := by
    rw [← Set.Icc_union_Ioc_eq_Icc le_rfl hab,
      VectorMeasure.of_union (by simp) measurableSet_Icc measurableSet_Ioc,
      Set.Icc_self, hz a, zero_add]
  rw [hpart, complexCumulative, complexCumulative, hwhole]
  abel

/-- The image of a weakly monotone closed interval has complex mass bounded
by twice the cumulative supremum. -/
private theorem complexMeasure_image_Icc_norm_le_two_sup
    (T : IntervalMap) (hT : Continuous T)
    (z : NonatomicVectorMeasure ℂ) {a b : I} (hab : a ≤ b)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc a b)) :
    ‖z.1 (T '' Set.Icc a b)‖ ≤ 2 * cumulativeNormSup z.1 := by
  rcases hmono with hmono | hanti
  · have hends : T a ≤ T b :=
      hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    rw [hT.continuousOn.image_Icc_of_monotoneOn hab hmono,
      complexMeasure_Icc_eq_cumulative_sub z.1 z.2 hends]
    calc
      ‖complexCumulative z.1 (T b) - complexCumulative z.1 (T a)‖ ≤
          ‖complexCumulative z.1 (T b)‖ +
            ‖complexCumulative z.1 (T a)‖ := norm_sub_le _ _
      _ ≤ cumulativeNormSup z.1 + cumulativeNormSup z.1 :=
        add_le_add (complexCumulative_norm_le_sup z.1 (T b))
          (complexCumulative_norm_le_sup z.1 (T a))
      _ = 2 * cumulativeNormSup z.1 := by ring
  · have hends : T b ≤ T a :=
      hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
    rw [hT.continuousOn.image_Icc_of_antitoneOn hab hanti,
      complexMeasure_Icc_eq_cumulative_sub z.1 z.2 hends]
    calc
      ‖complexCumulative z.1 (T a) - complexCumulative z.1 (T b)‖ ≤
          ‖complexCumulative z.1 (T a)‖ +
            ‖complexCumulative z.1 (T b)‖ := norm_sub_le _ _
      _ ≤ cumulativeNormSup z.1 + cumulativeNormSup z.1 :=
        add_le_add (complexCumulative_norm_le_sup z.1 (T a))
          (complexCumulative_norm_le_sup z.1 (T b))
      _ = 2 * cumulativeNormSup z.1 := by ring

/-- Vanishing endpoint coordinates force the manuscript's strict
`2 / lambda^N` contraction for the cumulative supremum. -/
theorem cumulativeNormSup_contraction
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    (X : ExpandingIterateData D) (z : productEigenspace D)
    (hz : cumulativeEndpointCoordinate X z = 0) :
    cumulativeNormSup z.1 ≤
      (2 / D.lambda ^ X.N) * cumulativeNormSup z.1 := by
  classical
  let H : IntervalMap := returnedProductMap P Q L
  let A : Module.End ℂ (NonatomicVectorMeasure ℂ) :=
    complexTransfer H D.partitionProduct
  have hpow (n : ℕ) :
      (A ^ n) z.1 = ((D.lambda : ℂ) ^ n) • z.1 := by
    induction n with
    | zero => simp
    | succ n ihn =>
        rw [pow_succ']
        change A ((A ^ n) z.1) = _
        rw [ihn, map_smul, z.2, smul_smul]
        congr 1
  have hiterate :
      complexTransfer (iterateMap H X.N) X.partition z.1 =
        ((D.lambda : ℂ) ^ X.N) • z.1 := by
    rw [complexTransfer_iterate D.finitePiece_product
      D.partitionProduct X.N X.partition]
    exact hpow X.N
  have hvertex (c : ℝ) (hc : c ∈ X.partition.partition.points) :
      complexCumulative z.1
        (⟨c, X.partition.partition.points_subset hc⟩ : I) = 0 := by
    have hc0 := congrFun hz (⟨c, hc⟩ : ExpandingEndpoint X)
    simpa [cumulativeEndpointCoordinate, ExpandingEndpoint.toI] using hc0
  have hpoint (x : I) :
      ‖complexCumulative z.1 x‖ ≤
        (2 / D.lambda ^ X.N) * cumulativeNormSup z.1 := by
    by_cases hxright : x = rightEndpoint
    · have hxzero : complexCumulative z.1 x = 0 := by
        rw [hxright]
        exact hvertex 1 X.partition.partition.one_mem
      rw [hxzero, norm_zero]
      exact mul_nonneg
        (div_nonneg (by norm_num)
          (pow_nonneg (le_of_lt (lt_trans zero_lt_one D.one_lt_lambda)) _))
        (cumulativeNormSup_nonneg z.1)
    · have hxlt : x < rightEndpoint :=
        lt_of_le_of_ne x.property.2 hxright
      obtain ⟨a, b, hab, hax, hxb⟩ :=
        X.partition.partition.exists_adjacent_Ico hxlt
      have hpair : (a, b) ∈ X.partition.partition.adjacentPairs := by
        rw [RealPartition.adjacentPairs]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hab.1, hab.2.1⟩, hab⟩
      let q : X.partition.partition.LapIndex := ⟨(a, b), hpair⟩
      let aI : I := ⟨a, X.partition.partition.points_subset hab.1⟩
      have haIx : aI ≤ x := hax
      have hsubset : Set.Icc aI x ⊆ q.assignedCell := by
        intro y hy
        by_cases hb : b = 1
        · simpa [q, RealPartition.LapIndex.assignedCell,
            RealPartition.LapIndex.left, RealPartition.LapIndex.right, hb]
            using (⟨(show a ≤ (y : ℝ) from hy.1),
              (show (y : ℝ) ≤ (x : ℝ) from hy.2).trans hxb.le⟩ :
              (y : ℝ) ∈ Set.Icc a b)
        · simpa [q, RealPartition.LapIndex.assignedCell,
            RealPartition.LapIndex.left, RealPartition.LapIndex.right, hb]
            using (⟨(show a ≤ (y : ℝ) from hy.1),
              (show (y : ℝ) ≤ (x : ℝ) from hy.2).trans_lt hxb⟩ :
              (y : ℝ) ∈ Set.Ico a b)
      have hscale :
          ((D.lambda : ℂ) ^ X.N) * z.1.1 (Set.Icc aI x) =
            z.1.1 (iterateMap H X.N '' Set.Icc aI x) := by
        calc
          ((D.lambda : ℂ) ^ X.N) * z.1.1 (Set.Icc aI x) =
              ((((D.lambda : ℂ) ^ X.N) • z.1 :
                NonatomicVectorMeasure ℂ).1) (Set.Icc aI x) := by
            rw [Submodule.coe_smul, VectorMeasure.smul_apply, smul_eq_mul]
          _ = (complexTransfer (iterateMap H X.N) X.partition z.1).1
                (Set.Icc aI x) := by
            exact congrArg
              (fun w : NonatomicVectorMeasure ℂ => w.1 (Set.Icc aI x))
              hiterate.symm
          _ = z.1.1 (iterateMap H X.N '' Set.Icc aI x) := by
            exact complexTransfer_apply_of_subset_assignedCell
              X.partition z.1 q measurableSet_Icc hsubset
      have hlocal : z.1.1 (Set.Icc aI x) = complexCumulative z.1 x := by
        rw [complexMeasure_Icc_eq_cumulative_sub z.1 z.1.2 haIx,
          hvertex a hab.1, sub_zero]
      have hscale' :
          ((D.lambda : ℂ) ^ X.N) * complexCumulative z.1 x =
            z.1.1 (iterateMap H X.N '' Set.Icc aI x) := by
        rw [← hlocal]
        exact hscale
      have hnorm := congrArg norm hscale'
      have hlambda_pos : 0 < D.lambda ^ X.N :=
        pow_pos (lt_trans zero_lt_one D.one_lt_lambda) _
      have hnorm' :
          D.lambda ^ X.N * ‖complexCumulative z.1 x‖ =
            ‖z.1.1 (iterateMap H X.N '' Set.Icc aI x)‖ := by
        simpa [norm_mul, norm_pow, Real.norm_eq_abs,
          abs_of_pos (lt_trans zero_lt_one D.one_lt_lambda)] using hnorm
      have hcell : Set.Icc aI x ⊆ intervalCell a b := by
        intro y hy
        exact ⟨(show a ≤ (y : ℝ) from hy.1),
          (show (y : ℝ) ≤ (x : ℝ) from hy.2).trans hxb.le⟩
      have hmono : IsWeaklyMonotoneOn (iterateMap H X.N)
          (Set.Icc aI x) :=
        (X.partition.weaklyMonotoneOn_cell hab).mono hcell
      have himageBound :
          ‖z.1.1 (iterateMap H X.N '' Set.Icc aI x)‖ ≤
            2 * cumulativeNormSup z.1 :=
        complexMeasure_image_Icc_norm_le_two_sup
          (iterateMap H X.N)
          (D.finitePiece_product.iterateMap X.N).continuous
          z.1 haIx hmono
      have hmul :
          D.lambda ^ X.N * ‖complexCumulative z.1 x‖ ≤
            2 * cumulativeNormSup z.1 := by
        rw [hnorm']
        exact himageBound
      calc
        ‖complexCumulative z.1 x‖ ≤
            (2 * cumulativeNormSup z.1) / D.lambda ^ X.N :=
          (le_div_iff₀ hlambda_pos).2 (by simpa [mul_comm] using hmul)
        _ = (2 / D.lambda ^ X.N) * cumulativeNormSup z.1 := by ring
  rw [cumulativeNormSup]
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro _ ⟨x, rfl⟩
    exact hpoint x

/-- A nonatomic complex measure is determined by all left cumulative
interval values. -/
private theorem signedMeasure_eq_zero_of_Iic_eq_zero
    (s : SignedMeasure I)
    (hs : ∀ a : I, s (Set.Iic a) = 0) :
    s = 0 := by
  let p : Measure I := s.toJordanDecomposition.posPart
  let n : Measure I := s.toJordanDecomposition.negPart
  have hpn : p = n := by
    apply Measure.ext_of_Iic p n
    intro a
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top p (Set.Iic a))
      (measure_ne_top n (Set.Iic a))).mp
    have hsE :
        s (Set.Iic a) =
          (p (Set.Iic a)).toReal - (n (Set.Iic a)).toReal := by
      rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s,
        JordanDecomposition.toSignedMeasure,
        Measure.toSignedMeasure_sub_apply measurableSet_Iic]
      rfl
    rw [hs a] at hsE
    exact sub_eq_zero.mp hsE.symm
  rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s]
  ext E hE
  rw [JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply hE]
  change (p E).toReal - (n E).toReal = 0
  rw [hpn, sub_self]

theorem complexMeasure_eq_zero_of_cumulative_eq_zero
    (z : ComplexMeasure I)
    (hz : ∀ x : I, complexCumulative z x = 0) : z = 0 := by
  have hleft (x : I) : Set.Icc leftEndpoint x = Set.Iic x := by
    apply Set.Subset.antisymm
    · intro y hy
      exact hy.2
    · intro y hy
      exact ⟨y.property.1, hy⟩
  have hIic (x : I) : z (Set.Iic x) = 0 := by
    rw [← hleft x]
    exact hz x
  have hre : ComplexMeasure.re z = 0 := by
    apply signedMeasure_eq_zero_of_Iic_eq_zero
    intro a
    have h := congrArg Complex.re (hIic a)
    simpa using h
  have him : ComplexMeasure.im z = 0 := by
    apply signedMeasure_eq_zero_of_Iic_eq_zero
    intro a
    have h := congrArg Complex.im (hIic a)
    simpa using h
  rw [← ComplexMeasure.toComplexMeasure_to_signedMeasure z, hre, him]
  rfl

/-- The cumulative contraction makes the endpoint coordinate injective. -/
theorem cumulativeEndpointCoordinate_injective
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    (X : ExpandingIterateData D) :
    Function.Injective (cumulativeEndpointCoordinate X) := by
  intro z w hzw
  let v : productEigenspace D := z - w
  have hvcoord : cumulativeEndpointCoordinate X v = 0 := by
    dsimp [v]
    rw [map_sub, hzw, sub_self]
  have hcontract := cumulativeNormSup_contraction X v hvcoord
  have hlambda_pos : 0 < D.lambda ^ X.N :=
    pow_pos (lt_trans zero_lt_one D.one_lt_lambda) _
  have hfactor : 2 / D.lambda ^ X.N < (1 : ℝ) :=
    (div_lt_one hlambda_pos).2 X.lambda_pow_gt_two
  have hsupzero : cumulativeNormSup v.1 = 0 := by
    have hnonneg := cumulativeNormSup_nonneg v.1
    nlinarith
  have hcumulative : ∀ x : I, complexCumulative v.1 x = 0 := by
    intro x
    apply norm_eq_zero.mp
    apply le_antisymm
    · simpa [hsupzero] using complexCumulative_norm_le_sup v.1 x
    · exact norm_nonneg _
  have hvmeasure : v.1.1 = 0 :=
    complexMeasure_eq_zero_of_cumulative_eq_zero v.1 hcumulative
  have hvzero : v = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hvmeasure
  apply sub_eq_zero.mp
  simpa [v] using hvzero

/-- The expanding product eigenspace embeds into a finite coordinate space. -/
theorem productEigenspace_finiteDimensional
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    FiniteDimensional ℂ (productEigenspace D) := by
  classical
  let X : ExpandingIterateData D :=
    Classical.choice (expandingIterateData_exists D)
  letI : Fintype (ExpandingEndpoint X) := by infer_instance
  exact FiniteDimensional.of_injective
    (cumulativeEndpointCoordinate X)
    (cumulativeEndpointCoordinate_injective X)

/-! ## Restricted commuting transfers and a joint eigenvector -/

theorem transferP_preserves_productEigenspace
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L)
    (z : productEigenspace D) :
    complexTransfer P D.partitionP z.1 ∈ productEigenspace D := by
  have hPH : Commute P (returnedProductMap P Q L) := by
    change Commute P (iterateMap P L ∘ iterateMap Q L)
    exact (Function.Commute.self_iterate P L).comp_right
      (D.commute.iterate_right L)
  have hcomm := complexTransfer_commute D.finitePiece_product
    D.finitePiece_P hPH.symm D.partitionProduct D.partitionP
  change complexTransfer (returnedProductMap P Q L) D.partitionProduct
      (complexTransfer P D.partitionP z.1) =
        (D.lambda : ℂ) • complexTransfer P D.partitionP z.1
  calc
    complexTransfer (returnedProductMap P Q L) D.partitionProduct
        (complexTransfer P D.partitionP z.1) =
      complexTransfer P D.partitionP
        (complexTransfer (returnedProductMap P Q L)
          D.partitionProduct z.1) := hcomm z.1
    _ = complexTransfer P D.partitionP ((D.lambda : ℂ) • z.1) := by
      rw [z.2]
    _ = (D.lambda : ℂ) • complexTransfer P D.partitionP z.1 :=
      map_smul _ _ _

theorem transferQ_preserves_productEigenspace
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L)
    (z : productEigenspace D) :
    complexTransfer Q D.partitionQ z.1 ∈ productEigenspace D := by
  have hQH : Commute Q (returnedProductMap P Q L) := by
    change Commute Q (iterateMap P L ∘ iterateMap Q L)
    exact (D.commute.symm.iterate_right L).comp_right
      (Function.Commute.self_iterate Q L)
  have hcomm := complexTransfer_commute D.finitePiece_product
    D.finitePiece_Q hQH.symm D.partitionProduct D.partitionQ
  change complexTransfer (returnedProductMap P Q L) D.partitionProduct
      (complexTransfer Q D.partitionQ z.1) =
        (D.lambda : ℂ) • complexTransfer Q D.partitionQ z.1
  calc
    complexTransfer (returnedProductMap P Q L) D.partitionProduct
        (complexTransfer Q D.partitionQ z.1) =
      complexTransfer Q D.partitionQ
        (complexTransfer (returnedProductMap P Q L)
          D.partitionProduct z.1) := hcomm z.1
    _ = complexTransfer Q D.partitionQ ((D.lambda : ℂ) • z.1) := by
      rw [z.2]
    _ = (D.lambda : ℂ) • complexTransfer Q D.partitionQ z.1 :=
      map_smul _ _ _

noncomputable def restrictedTransferP
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    Module.End ℂ (productEigenspace D) where
  toFun z := ⟨complexTransfer P D.partitionP z.1,
    transferP_preserves_productEigenspace D z⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul _ _ _

noncomputable def restrictedTransferQ
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    Module.End ℂ (productEigenspace D) where
  toFun z := ⟨complexTransfer Q D.partitionQ z.1,
    transferQ_preserves_productEigenspace D z⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul _ _ _

theorem restrictedTransfers_commute
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    Function.Commute (restrictedTransferP D) (restrictedTransferQ D) := by
  intro z
  apply Subtype.ext
  exact complexTransfer_commute D.finitePiece_P D.finitePiece_Q
    D.commute D.partitionP D.partitionQ z.1

/-- A common complex eigenvector, with the exact returned-word relation. -/
structure JointTransferEigenvectorData
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) where
  vector : productEigenspace D
  vector_ne_zero : vector ≠ 0
  eigenP : ℂ
  eigenQ : ℂ
  transferP_eigen :
    complexTransfer P D.partitionP vector.1 = eigenP • vector.1
  transferQ_eigen :
    complexTransfer Q D.partitionQ vector.1 = eigenQ • vector.1
  eigenP_ne_zero : eigenP ≠ 0
  eigenQ_ne_zero : eigenQ ≠ 0
  product_relation : (eigenP * eigenQ) ^ L = (D.lambda : ℂ)

theorem restrictedTransfers_jointEigenvector
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L)
    (_seed : ComplexProductEigenData D)
    (_hfinite : FiniteDimensional ℂ (productEigenspace D))
    (_hcomm : Function.Commute (restrictedTransferP D)
      (restrictedTransferQ D)) :
    Nonempty (JointTransferEigenvectorData D) := by
  letI : FiniteDimensional ℂ (productEigenspace D) := _hfinite
  letI : Nontrivial (productEigenspace D) :=
    ⟨⟨_seed.vector, 0, _seed.vector_ne_zero⟩⟩
  let A : Module.End ℂ (productEigenspace D) := restrictedTransferP D
  let B : Module.End ℂ (productEigenspace D) := restrictedTransferQ D
  obtain ⟨α, hα⟩ := A.exists_eigenvalue
  let E : Submodule ℂ (productEigenspace D) := A.eigenspace α
  have hBmaps : ∀ x ∈ E, B x ∈ E := by
    intro x hx
    have hAx : A x = α • x := Module.End.mem_eigenspace_iff.mp hx
    apply Module.End.mem_eigenspace_iff.mpr
    calc
      A (B x) = B (A x) := _hcomm x
      _ = B (α • x) := by rw [hAx]
      _ = α • B x := map_smul B α x
  let BR : Module.End ℂ E := B.restrict hBmaps
  letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hα
  obtain ⟨β, hβ⟩ := BR.exists_eigenvalue
  obtain ⟨e, he⟩ := hβ.exists_hasEigenvector
  let u : productEigenspace D := e.1
  have hu_ne : u ≠ 0 := by
    intro hu
    apply he.2
    apply Subtype.ext
    exact hu
  have hA : A u = α • u :=
    Module.End.mem_eigenspace_iff.mp e.2
  have hB : B u = β • u := by
    have h := he.apply_eq_smul
    exact congrArg Subtype.val h
  have hu_under : u.1 ≠ 0 := by
    intro hu
    apply hu_ne
    apply Subtype.ext
    exact hu
  have hPmeasure :
      complexTransfer P D.partitionP u.1 = α • u.1 := by
    have h := congrArg (fun v : productEigenspace D => v.1) hA
    simpa [A, restrictedTransferP] using h
  have hQmeasure :
      complexTransfer Q D.partitionQ u.1 = β • u.1 := by
    have h := congrArg (fun v : productEigenspace D => v.1) hB
    simpa [B, restrictedTransferQ] using h
  have hPvec :
      (complexTransfer P D.partitionP).HasEigenvector α u.1 :=
    ⟨Module.End.mem_eigenspace_iff.mpr hPmeasure, hu_under⟩
  have hQvec :
      (complexTransfer Q D.partitionQ).HasEigenvector β u.1 :=
    ⟨Module.End.mem_eigenspace_iff.mpr hQmeasure, hu_under⟩
  have hproduct_action :
      complexTransfer (returnedProductMap P Q L) D.partitionProduct u.1 =
        ((α * β) ^ L) • u.1 := by
    rw [D.complexTransfer_product_eq]
    change ((complexTransfer Q D.partitionQ) ^ L)
      (((complexTransfer P D.partitionP) ^ L) u.1) = _
    rw [hPvec.pow_apply, map_smul, hQvec.pow_apply, smul_smul]
    congr 1
    ring
  have hscalar_smul :
      ((α * β) ^ L) • u.1 = (D.lambda : ℂ) • u.1 :=
    hproduct_action.symm.trans u.2
  have hrelation : (α * β) ^ L = (D.lambda : ℂ) :=
    smul_left_injective ℂ (m := u.1) hu_under hscalar_smul
  have hlambda_ne : (D.lambda : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_trans zero_lt_one D.one_lt_lambda)
  have hmul_ne : α * β ≠ 0 := by
    intro hzero
    apply hlambda_ne
    rw [← hrelation, hzero, zero_pow (Nat.ne_of_gt D.L_pos)]
  have hα_ne : α ≠ 0 := by
    intro hzero
    exact hmul_ne (by simp [hzero])
  have hβ_ne : β ≠ 0 := by
    intro hzero
    exact hmul_ne (by simp [hzero])
  exact ⟨⟨u, hu_ne, α, β, hPmeasure, hQmeasure,
    hα_ne, hβ_ne, hrelation⟩⟩

/-! ## Exact variation and normalization -/

/-- Normalize total variation by its mass on the whole interval. -/
noncomputable def normalizedVariation (z : ComplexMeasure I) : Measure I :=
  (z.variation Set.univ)⁻¹ • z.variation

structure SimultaneousVariationData
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    (Z : JointTransferEigenvectorData D) where
  measure : Measure I
  measure_eq_normalizedVariation : measure = normalizedVariation Z.vector.1
  scaleP : ℝ
  scaleQ : ℝ
  scaleP_pos : 0 < scaleP
  scaleQ_pos : 0 < scaleQ
  probability : measure Set.univ = 1
  noAtoms : ∀ x : I, measure {x} = 0
  transferP_eigen :
    transferMeasure P D.partitionP measure noAtoms =
      ENNReal.ofReal scaleP • measure
  transferQ_eigen :
    transferMeasure Q D.partitionQ measure noAtoms =
      ENNReal.ofReal scaleQ • measure
  product_relation : (scaleP * scaleQ) ^ L = D.lambda

/-- Positive transfer commutes with an `ENNReal` scalar. -/
private theorem transferMeasure_smul_ennreal
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0) (c : ℝ≥0∞) :
    transferMeasure T PT (c • μ)
        (fun x => by rw [Measure.smul_apply, hμ x, smul_eq_mul, mul_zero]) =
      c • transferMeasure T PT μ hμ := by
  classical
  let F := PT.toFiniteMonotonePartition
  letI := F.fintype_idx
  ext E hE
  change piecewiseMonotoneTransferMeasure T F (c • μ) _ E =
    (c • piecewiseMonotoneTransferMeasure T F μ hμ) E
  calc
    piecewiseMonotoneTransferMeasure T F (c • μ) _ E =
        ∑ i, (c • μ) (T '' (E ∩ F.piece i)) :=
      piecewiseMonotoneTransferMeasure_apply T F (c • μ) _ hE
    _ = ∑ i, c * μ (T '' (E ∩ F.piece i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Measure.smul_apply, smul_eq_mul]
    _ = c * ∑ i, μ (T '' (E ∩ F.piece i)) :=
      (Finset.mul_sum _ _ _).symm
    _ = c * piecewiseMonotoneTransferMeasure T F μ hμ E := by
      rw [piecewiseMonotoneTransferMeasure_apply T F μ hμ hE]
    _ = (c • piecewiseMonotoneTransferMeasure T F μ hμ) E := by
      rw [Measure.smul_apply, smul_eq_mul]

theorem jointEigenvector_variation
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    (Z : JointTransferEigenvectorData D) :
    Nonempty (SimultaneousVariationData Z) := by
  let z : ComplexMeasure I := Z.vector.1.1
  letI : IsFiniteMeasure z.variation := complex_variation_isFinite z
  have hz_noAtoms : VectorNoAtoms z := Z.vector.1.2
  have hz_ne : z ≠ 0 := by
    intro hz
    apply Z.vector_ne_zero
    apply Subtype.ext
    apply Subtype.ext
    exact hz
  have hvar_ne : z.variation ≠ 0 :=
    (complex_variation_ne_zero_iff z).2 hz_ne
  have hmass_ne : z.variation Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.2 hvar_ne
  have hmass_top : z.variation Set.univ ≠ ∞ :=
    measure_ne_top z.variation Set.univ
  have hvar_noAtoms : ∀ x : I, z.variation {x} = 0 := by
    letI : NoAtoms z.variation := variation_noAtoms hz_noAtoms
    exact fun x => measure_singleton x
  have hnormalized_noAtoms :
      ∀ x : I, normalizedVariation z {x} = 0 := by
    intro x
    rw [normalizedVariation, Measure.smul_apply,
      hvar_noAtoms x, smul_eq_mul, mul_zero]
  have hprob : normalizedVariation z Set.univ = 1 := by
    rw [normalizedVariation, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hmass_ne hmass_top]
  have hnatP :
      (complexTransfer P D.partitionP Z.vector.1).1.variation =
        transferMeasure P D.partitionP z.variation hvar_noAtoms := by
    simpa [complexTransfer, transferVector, transferMeasure, z] using
      variation_transfer_eq_transfer_variation P D.partitionP z hz_noAtoms
  have hnatQ :
      (complexTransfer Q D.partitionQ Z.vector.1).1.variation =
        transferMeasure Q D.partitionQ z.variation hvar_noAtoms := by
    simpa [complexTransfer, transferVector, transferMeasure, z] using
      variation_transfer_eq_transfer_variation Q D.partitionQ z hz_noAtoms
  have hvarP :
      transferMeasure P D.partitionP z.variation hvar_noAtoms =
        ENNReal.ofReal ‖Z.eigenP‖ • z.variation := by
    calc
      transferMeasure P D.partitionP z.variation hvar_noAtoms =
          (complexTransfer P D.partitionP Z.vector.1).1.variation :=
        hnatP.symm
      _ = (Z.eigenP • z).variation := by
        have h := congrArg
          (fun w : NonatomicVectorMeasure ℂ => w.1.variation)
          Z.transferP_eigen
        simpa [Submodule.coe_smul, z] using h
      _ = ENNReal.ofReal ‖Z.eigenP‖ • z.variation :=
        variation_complex_smul Z.eigenP z
  have hvarQ :
      transferMeasure Q D.partitionQ z.variation hvar_noAtoms =
        ENNReal.ofReal ‖Z.eigenQ‖ • z.variation := by
    calc
      transferMeasure Q D.partitionQ z.variation hvar_noAtoms =
          (complexTransfer Q D.partitionQ Z.vector.1).1.variation :=
        hnatQ.symm
      _ = (Z.eigenQ • z).variation := by
        have h := congrArg
          (fun w : NonatomicVectorMeasure ℂ => w.1.variation)
          Z.transferQ_eigen
        simpa [Submodule.coe_smul, z] using h
      _ = ENNReal.ofReal ‖Z.eigenQ‖ • z.variation :=
        variation_complex_smul Z.eigenQ z
  have hnormalizedP :
      transferMeasure P D.partitionP (normalizedVariation z)
          hnormalized_noAtoms =
        ENNReal.ofReal ‖Z.eigenP‖ • normalizedVariation z := by
    have hscaled :
        transferMeasure P D.partitionP
            ((z.variation Set.univ)⁻¹ • z.variation)
            (fun x => by rw [Measure.smul_apply, hvar_noAtoms x,
              smul_eq_mul, mul_zero]) =
          ENNReal.ofReal ‖Z.eigenP‖ •
            ((z.variation Set.univ)⁻¹ • z.variation) := by
      rw [transferMeasure_smul_ennreal D.partitionP z.variation
        hvar_noAtoms (z.variation Set.univ)⁻¹]
      rw [hvarP]
      simp only [smul_smul]
      congr 1
      exact mul_comm _ _
    simpa [normalizedVariation] using hscaled
  have hnormalizedQ :
      transferMeasure Q D.partitionQ (normalizedVariation z)
          hnormalized_noAtoms =
        ENNReal.ofReal ‖Z.eigenQ‖ • normalizedVariation z := by
    have hscaled :
        transferMeasure Q D.partitionQ
            ((z.variation Set.univ)⁻¹ • z.variation)
            (fun x => by rw [Measure.smul_apply, hvar_noAtoms x,
              smul_eq_mul, mul_zero]) =
          ENNReal.ofReal ‖Z.eigenQ‖ •
            ((z.variation Set.univ)⁻¹ • z.variation) := by
      rw [transferMeasure_smul_ennreal D.partitionQ z.variation
        hvar_noAtoms (z.variation Set.univ)⁻¹]
      rw [hvarQ]
      simp only [smul_smul]
      congr 1
      exact mul_comm _ _
    simpa [normalizedVariation] using hscaled
  have hscaleP_pos : 0 < ‖Z.eigenP‖ := norm_pos_iff.mpr Z.eigenP_ne_zero
  have hscaleQ_pos : 0 < ‖Z.eigenQ‖ := norm_pos_iff.mpr Z.eigenQ_ne_zero
  have hrelation : (‖Z.eigenP‖ * ‖Z.eigenQ‖) ^ L = D.lambda := by
    have h := congrArg norm Z.product_relation
    simpa [norm_pow, norm_mul, Real.norm_eq_abs,
      abs_of_pos (lt_trans zero_lt_one D.one_lt_lambda)] using h
  exact ⟨⟨normalizedVariation z, rfl, ‖Z.eigenP‖, ‖Z.eigenQ‖,
    hscaleP_pos, hscaleQ_pos, hprob, hnormalized_noAtoms,
    hnormalizedP, hnormalizedQ, hrelation⟩⟩

structure SimultaneousEigenmeasureConstruction
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) where
  joint : JointTransferEigenvectorData D
  variation : SimultaneousVariationData joint

/-- General returned-word theorem, retaining `(C*D)^L = lambda`. -/
theorem simultaneousEigenmeasureConstruction_exists
    {P Q : IntervalMap} {L : ℕ}
    (D : PiecewiseMonotoneProductEigenData P Q L) :
    Nonempty (SimultaneousEigenmeasureConstruction D) := by
  obtain ⟨seed⟩ := complexifyProductEigenmeasure D
  have hfinite : FiniteDimensional ℂ (productEigenspace D) :=
    productEigenspace_finiteDimensional D
  have hcomm : Function.Commute (restrictedTransferP D)
      (restrictedTransferQ D) := restrictedTransfers_commute D
  obtain ⟨joint⟩ :=
    restrictedTransfers_jointEigenvector D seed hfinite hcomm
  obtain ⟨variation⟩ := jointEigenvector_variation joint
  exact ⟨⟨joint, variation⟩⟩

/-- The `L = 1` form used by the direct piecewise-monotone theorem. -/
theorem simultaneousEigenprobability_of_productEigenprobability
    {P Q : IntervalMap}
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Commute P Q)
    (PP : MonotonicityPartition P) (PQ : MonotonicityPartition Q)
    (PPQ : MonotonicityPartition (P ∘ Q))
    (lambda : ℝ) (hlambda : 1 < lambda)
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0)
    (heigen : transferMeasure (P ∘ Q) PPQ μ hμ =
      ENNReal.ofReal lambda • μ) :
    ∃ ν : Measure I, ∃ C D : ℝ,
      ∃ hν : ∀ x : I, ν {x} = 0,
      0 < C ∧ 0 < D ∧ ν Set.univ = 1 ∧
      transferMeasure P PP ν hν =
        ENNReal.ofReal C • ν ∧
      transferMeasure Q PQ ν hν =
        ENNReal.ofReal D • ν ∧
      C * D = lambda := by
  let data : PiecewiseMonotoneProductEigenData P Q 1 :=
    { finitePiece_P := hP
      finitePiece_Q := hQ
      commute := hcomm
      L_pos := by norm_num
      partitionP := PP
      partitionQ := PQ
      partitionProduct := by
        simpa [returnedProductMap, CommutingInterval.iterateMap] using PPQ
      lambda := lambda
      one_lt_lambda := hlambda
      measure := μ
      probability := hprob
      noAtoms := hμ
      product_eigen := by
        simpa [returnedProductMap, CommutingInterval.iterateMap] using heigen }
  obtain ⟨S⟩ := simultaneousEigenmeasureConstruction_exists data
  let V := S.variation
  refine ⟨V.measure, V.scaleP, V.scaleQ, V.noAtoms,
    V.scaleP_pos, V.scaleQ_pos, V.probability, V.transferP_eigen,
    V.transferQ_eigen, ?_⟩
  simpa using V.product_relation

/-! ## Exactness, full support, and scaled probabilities -/

/-- On a measurable subset of one assigned lap, the positive transfer is
the literal image measure.  This statement remains valid on a plateau. -/
theorem transferMeasure_apply_of_subset_assignedCell
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (q : PT.partition.LapIndex) {E : Set I}
    (hE : MeasurableSet E) (hEq : E ⊆ q.assignedCell) :
    transferMeasure T PT μ hμ E = μ (T '' E) := by
  classical
  let F := PT.toFiniteMonotonePartition
  letI := F.fintype_idx
  change E ⊆ F.piece q at hEq
  change piecewiseMonotoneTransferMeasure T F μ hμ E = _
  rw [piecewiseMonotoneTransferMeasure_apply T F μ hμ hE]
  calc
    ∑ i, μ (T '' (E ∩ F.piece i)) =
        μ (T '' (E ∩ F.piece q)) := by
      apply Finset.sum_eq_single q
      · intro r _hr hrq
        have hEmpty : E ∩ F.piece r = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro x hx
          exact Set.disjoint_left.1 (F.pairwise_disjoint hrq)
            hx.2 (hEq hx.1)
        rw [hEmpty, image_empty, measure_empty]
      · intro hq
        exact (hq (Finset.mem_univ q)).elim
    _ = μ (T '' E) := by rw [inter_eq_left.2 hEq]

/-- A transfer eigenidentity gives image scaling on every measurable
subset of an assigned lap, without exactness or full support. -/
theorem measure_image_eq_of_transferEigen_on_assignedCell
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    (q : PT.partition.LapIndex) {E : Set I}
    (hE : MeasurableSet E) (hEq : E ⊆ q.assignedCell) :
    μ (T '' E) = ENNReal.ofReal C * μ E := by
  calc
    μ (T '' E) = transferMeasure T PT μ hμ E :=
      (transferMeasure_apply_of_subset_assignedCell
        PT μ hμ q hE hEq).symm
    _ = (ENNReal.ofReal C • μ) E :=
      congrArg (fun ν : Measure I => ν E) heigen
    _ = ENNReal.ofReal C * μ E := by
      rw [Measure.smul_apply, smul_eq_mul]

/-- On any measurable set where the map is injective, positive transfer
is the literal image measure. -/
theorem transferMeasure_apply_of_injOn
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    {E : Set I} (hE : MeasurableSet E) (hinj : Set.InjOn T E) :
    transferMeasure T PT μ hμ E = μ (T '' E) := by
  classical
  let F := PT.toFiniteMonotonePartition
  letI := F.fintype_idx
  change piecewiseMonotoneTransferMeasure T F μ hμ E = _
  rw [piecewiseMonotoneTransferMeasure_apply T F μ hμ hE]
  have hdecomp : T '' E = ⋃ i, T '' (E ∩ F.piece i) := by
    ext y
    constructor
    · rintro ⟨x, hxE, rfl⟩
      have hxU : x ∈ ⋃ i, F.piece i := by
        rw [F.cover]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.1 hxU with ⟨i, hxi⟩
      exact Set.mem_iUnion.2 ⟨i, x, ⟨hxE, hxi⟩, rfl⟩
    · intro hy
      rcases Set.mem_iUnion.1 hy with ⟨i, x, hx, rfl⟩
      exact ⟨x, hx.1, rfl⟩
  have hdisj : Pairwise (Disjoint on
      fun i => T '' (E ∩ F.piece i)) := by
    intro i j hij
    change Disjoint (T '' (E ∩ F.piece i))
      (T '' (E ∩ F.piece j))
    rw [Set.disjoint_left]
    intro y hyi hyj
    rcases hyi with ⟨x, ⟨hxE, hxi⟩, hxy⟩
    rcases hyj with ⟨z, ⟨hzE, hzj⟩, hzy⟩
    have hxz : x = z := hinj hxE hzE (hxy.trans hzy.symm)
    subst z
    exact Set.disjoint_left.1 (F.pairwise_disjoint hij) hxi hzj
  have hmeas : ∀ i, MeasurableSet (T '' (E ∩ F.piece i)) := by
    intro i
    exact measurableSet_image_of_monotoneBranchOn
      (hE.inter (F.measurable_piece i)) inter_subset_right
      (F.monotone_piece i)
  calc
    ∑ i, μ (T '' (E ∩ F.piece i)) =
        ∑' i, μ (T '' (E ∩ F.piece i)) :=
      (tsum_fintype _).symm
    _ = μ (⋃ i, T '' (E ∩ F.piece i)) :=
      (measure_iUnion hdisj hmeas).symm
    _ = μ (T '' E) := by rw [hdecomp]

/-- A transfer eigenidentity gives the manuscript's scaling law on every
measurable injectivity set, without exactness or full support. -/
theorem measure_image_eq_of_transferEigen_of_injOn
    {T : IntervalMap} (PT : MonotonicityPartition T)
    (μ : Measure I) (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ)
    {E : Set I} (hE : MeasurableSet E) (hinj : Set.InjOn T E) :
    μ (T '' E) = ENNReal.ofReal C * μ E := by
  calc
    μ (T '' E) = transferMeasure T PT μ hμ E :=
      (transferMeasure_apply_of_injOn PT μ hμ hE hinj).symm
    _ = (ENNReal.ofReal C • μ) E :=
      congrArg (fun ν : Measure I => ν E) heigen
    _ = ENNReal.ofReal C * μ E := by
      rw [Measure.smul_apply, smul_eq_mul]

/-- Exactness upgrades a nonzero positive transfer eigenmeasure to full
topological support. -/
theorem isOpenPosMeasure_of_exact_transferEigen
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (PT : MonotonicityPartition T) (hExact : IsTopologicallyExact T)
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0)
    (C : ℝ) (hC : 0 < C)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ) :
    μ.IsOpenPosMeasure := by
  classical
  let F := PT.toFiniteMonotonePartition
  letI := F.fintype_idx
  have himage_data {E : Set I} (hE : MeasurableSet E) (hzero : μ E = 0) :
      MeasurableSet (T '' E) ∧ μ (T '' E) = 0 := by
    have hunion : T '' E = ⋃ i : F.idx, T '' (E ∩ F.piece i) := by
      ext y
      constructor
      · rintro ⟨x, hxE, rfl⟩
        have hxcover : x ∈ ⋃ i : F.idx, F.piece i := by
          rw [F.cover]
          exact Set.mem_univ x
        rcases Set.mem_iUnion.1 hxcover with ⟨i, hxi⟩
        exact Set.mem_iUnion.2 ⟨i, x, ⟨hxE, hxi⟩, rfl⟩
      · intro hy
        rcases Set.mem_iUnion.1 hy with ⟨i, x, hx, rfl⟩
        exact ⟨x, hx.1, rfl⟩
    have htermMeas (i : F.idx) :
        MeasurableSet (T '' (E ∩ F.piece i)) :=
      measurableSet_image_of_monotoneBranchOn
        (hE.inter (F.measurable_piece i)) inter_subset_right
        (F.monotone_piece i)
    have heval := congrArg (fun ν : Measure I => ν E) heigen
    change piecewiseMonotoneTransferMeasure T F μ hμ E =
      (ENNReal.ofReal C • μ) E at heval
    rw [piecewiseMonotoneTransferMeasure_apply T F μ hμ hE,
      Measure.smul_apply, smul_eq_mul, hzero, mul_zero] at heval
    have htermZero (i : F.idx) : μ (T '' (E ∩ F.piece i)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => (bot_le : (0 : ℝ≥0∞) ≤ _))).mp heval
        i (Finset.mem_univ i)
    constructor
    · rw [hunion]
      exact MeasurableSet.iUnion htermMeas
    · rw [hunion]
      exact measure_iUnion_null htermZero
  refine ⟨?_⟩
  intro U hU hUne hUzero
  obtain ⟨n, hn⟩ := hExact U hU hUne
  have hiterate : ∀ m : ℕ,
      MeasurableSet (iterateMap T m '' U) ∧
        μ (iterateMap T m '' U) = 0 := by
    intro m
    induction m with
    | zero =>
        simpa [CommutingInterval.iterateMap] using
          (⟨hU.measurableSet, hUzero⟩ : MeasurableSet U ∧ μ U = 0)
    | succ m ihm =>
        have hnext := himage_data ihm.1 ihm.2
        have heq : iterateMap T (Nat.succ m) '' U =
            T '' (iterateMap T m '' U) := by
          rw [show iterateMap T (Nat.succ m) =
              T ∘ iterateMap T m by exact Function.iterate_succ' T m,
            Set.image_comp]
        rw [heq]
        exact hnext
  have hnzero := (hiterate n).2
  rw [hn, hprob] at hnzero
  exact one_ne_zero hnzero

/-- A positive transfer eigenidentity is exactly injective-set scaling;
with probability, nonatomicity, and full support it is a scaled probability. -/
theorem isScaledProbability_of_transferEigen
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (PT : MonotonicityPartition T)
    (μ : Measure I) (hprob : μ Set.univ = 1)
    (hμ : ∀ x : I, μ {x} = 0)
    (hfull : μ.IsOpenPosMeasure)
    (C : ℝ) (hC : 0 < C)
    (heigen : transferMeasure T PT μ hμ = ENNReal.ofReal C • μ) :
    IsScaledProbability T C μ := by
  refine ⟨hprob, hμ, hfull.open_pos, ?_⟩
  intro E hE hinj
  exact measure_image_eq_of_transferEigen_of_injOn
    PT μ hμ C heigen hE hinj

/-- Either exact generator supplies full support for the common measure;
both transfer eigenidentities then become scaled-probability identities. -/
theorem SimultaneousVariationData.isScaled_of_exactP
    {P Q : IntervalMap} {L : ℕ}
    {D : PiecewiseMonotoneProductEigenData P Q L}
    {Z : JointTransferEigenvectorData D}
    (V : SimultaneousVariationData Z)
    (hExactP : IsTopologicallyExact P) :
    IsScaledProbability P V.scaleP V.measure ∧
      IsScaledProbability Q V.scaleQ V.measure := by
  have hfull : V.measure.IsOpenPosMeasure :=
    isOpenPosMeasure_of_exact_transferEigen D.finitePiece_P
      D.partitionP hExactP V.measure V.probability V.noAtoms
      V.scaleP V.scaleP_pos V.transferP_eigen
  constructor
  · exact isScaledProbability_of_transferEigen D.finitePiece_P
      D.partitionP V.measure V.probability V.noAtoms hfull
      V.scaleP V.scaleP_pos V.transferP_eigen
  · exact isScaledProbability_of_transferEigen D.finitePiece_Q
      D.partitionQ V.measure V.probability V.noAtoms hfull
      V.scaleQ V.scaleQ_pos V.transferQ_eigen

end CommutingInterval
