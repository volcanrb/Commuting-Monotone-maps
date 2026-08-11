import CommutingIntervalSimplified.Defs
import CommutingIntervalSimplified.BranchLength
import CommutingIntervalSimplified.FactorBase
import CommutingIntervalSimplified.MinimalCore
import CommutingIntervalSimplified.PiecewiseMonotoneBase
import CommutingIntervalSimplified.ProductBranchEigen

/-!
# Reduction to a minimal expanding constant-slope counterexample

This module follows the branch-length proof of manuscript Lemma
`lem:linearize`.  The only input not yet supplied by the branch-length
operator itself is isolated as `initialProductBranchEigenData_exists`: it is
the internal, axiom-free theorem which replaces the cited BF+AM product
eigen-coordinate step.  No simultaneous eigenmeasure or distribution-function
shortcut is used here.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set

/-! ## Counterexamples and minimal-core normalization -/

/-- A counterexample in the continuous finite-piece piecewise-monotone class. -/
structure PiecewiseMonotoneCounterexample where
  P : IntervalMap
  Q : IntervalMap
  finitePiece_P : FinitePieceMonotone P
  finitePiece_Q : FinitePieceMonotone Q
  commute : Function.Commute P Q
  no_common_fixed_point : ¬HasCommonFixedPoint P Q

/-- An affinely normalized minimal-core counterexample. -/
structure MinimalPiecewiseMonotoneCounterexample where
  P : IntervalMap
  Q : IntervalMap
  finitePiece_P : FinitePieceMonotone P
  finitePiece_Q : FinitePieceMonotone Q
  onto_P : IsOnto P
  onto_Q : IsOnto Q
  commute : Function.Commute P Q
  no_common_fixed_point : ¬HasCommonFixedPoint P Q
  core_minimal : ∀ J : ClosedSubinterval,
    IsCommonInvariantCore P Q J → J.carrier = Set.univ

namespace MinimalPiecewiseMonotoneCounterexample

/-- The commuting product used in the product eigen-coordinate step. -/
def product (C : MinimalPiecewiseMonotoneCounterexample) : IntervalMap :=
  C.P ∘ C.Q

/-- The product is finite-piece piecewise monotone. -/
theorem finitePiece_product (C : MinimalPiecewiseMonotoneCounterexample) :
    FinitePieceMonotone C.product :=
  C.finitePiece_P.comp C.finitePiece_Q

end MinimalPiecewiseMonotoneCounterexample

/--
Exact data relating the normalized minimal dynamics to the original source:
the affine embedding identifies `I` with the selected invariant core and
intertwines both generators.
-/
structure MinimalCoreNormalization
    (source : PiecewiseMonotoneCounterexample) where
  core : ClosedSubinterval
  core_nondegenerate : core.Nondegenerate
  minimal : MinimalPiecewiseMonotoneCounterexample
  embedding : IntervalMap
  continuous_embedding : Continuous embedding
  strictMono_embedding : StrictMono embedding
  range_embedding : Set.range embedding = core.carrier
  affine_embedding : ∃ m c : ℝ, 0 < m ∧
    ∀ x : I, (embedding x : ℝ) = m * (x : ℝ) + c
  intertwines_P : Intertwines embedding minimal.P source.P
  intertwines_Q : Intertwines embedding minimal.Q source.Q

/-- Every counterexample has a nondegenerate affinely normalized minimal
common invariant core, and the returned maps are onto that core. -/
theorem minimalCoreNormalization_exists
    (C : PiecewiseMonotoneCounterexample) :
    Nonempty (MinimalCoreNormalization C) := by
  obtain ⟨J, hminimal⟩ := exists_minimalCommonInvariantCore C.P C.Q
    C.finitePiece_P.continuous C.finitePiece_Q.continuous
  have hJ : J.Nondegenerate :=
    invariantCore_nondegenerate_of_noCommonFixedPoint
      C.no_common_fixed_point hminimal.1
  obtain ⟨hPontoCore, hQontoCore⟩ :=
    minimalCommonInvariantCore_mapsOnto
      C.finitePiece_P.continuous C.finitePiece_Q.continuous
      C.commute J hminimal
  let P' : IntervalMap := rescaledCoreMap J hJ C.P hminimal.1.1
  let Q' : IntervalMap := rescaledCoreMap J hJ C.Q hminimal.1.2
  let M : MinimalPiecewiseMonotoneCounterexample :=
    { P := P'
      Q := Q'
      finitePiece_P := C.finitePiece_P.rescaledCoreMap
        J hJ hminimal.1.1
      finitePiece_Q := C.finitePiece_Q.rescaledCoreMap
        J hJ hminimal.1.2
      onto_P := rescaledCoreMap_surjective_of_surjOn
        J hJ hminimal.1.1 hPontoCore
      onto_Q := rescaledCoreMap_surjective_of_surjOn
        J hJ hminimal.1.2 hQontoCore
      commute := rescaledCoreMap_commute J hJ
        hminimal.1.1 hminimal.1.2 C.commute
      no_common_fixed_point := noCommonFixedPoint_rescaledCoreMaps
        J hJ hminimal.1.1 hminimal.1.2 C.no_common_fixed_point
      core_minimal := rescaledCoreMaps_coreMinimal J hJ hminimal }
  refine ⟨{
    core := J
    core_nondegenerate := hJ
    minimal := M
    embedding := coreEmbeddingMap J hJ
    continuous_embedding := coreEmbeddingMap_continuous J hJ
    strictMono_embedding := coreEmbeddingMap_strictMono J hJ
    range_embedding := range_coreEmbeddingMap J hJ
    affine_embedding := coreEmbeddingMap_affine J hJ
    intertwines_P := ?_
    intertwines_Q := ?_
  }⟩
  · simpa [M, P'] using
      (coreEmbeddingMap_intertwines_rescaledCoreMap
        J hJ C.P hminimal.1.1)
  · simpa [M, Q'] using
      (coreEmbeddingMap_intertwines_rescaledCoreMap
        J hJ C.Q hminimal.1.2)

/-! ## The isolated BF+AM replacement and the common branch eigen-coordinate -/

/--
The expanding normalized product eigen-coordinate supplied internally by the
horseshoe/finite-dimensional branch-length argument.  This theorem is the
single replacement for the external BF+AM input in the manuscript route; it
must ultimately be proved, not postulated as an axiom.
-/
structure InitialProductBranchEigenData
    (C : MinimalPiecewiseMonotoneCounterexample) where
  rho : ℝ
  one_lt_rho : 1 < rho
  coordinate : NormalizedContinuousCoordinate
  coordinate_monotone : Monotone (fun x : I => coordinate x)
  coordinate_rightEndpoint : coordinate rightEndpoint = 1
  product_eigen :
    branchLengthOperator C.finitePiece_product coordinate = rho • coordinate

/-- Internal no-axiom construction of the expanding product
eigen-coordinate corresponding to the manuscript's BF+AM step. -/
theorem initialProductBranchEigenData_exists
    (C : MinimalPiecewiseMonotoneCounterexample) :
    Nonempty (InitialProductBranchEigenData C) := by
  obtain ⟨H⟩ := commuting_noCommonFixedPoint_product_horseshoe
    C.finitePiece_P.continuous C.finitePiece_Q.continuous
      C.commute C.no_common_fixed_point
  obtain ⟨D⟩ := productBranchEigenData_exists_of_horseshoe
    C.finitePiece_product H
  exact ⟨{
    rho := D.rho
    one_lt_rho := D.one_lt_rho
    coordinate := D.coordinate
    coordinate_monotone := D.coordinate_monotone
    coordinate_rightEndpoint := D.coordinate_rightEndpoint
    product_eigen := D.product_eigen }⟩

/-- Apply the branch-length Brouwer theorem to turn a product eigen-coordinate
into one common eigen-coordinate for the two commuting branch operators. -/
theorem commonBranchEigenCoordinate_of_initialProduct
    (C : MinimalPiecewiseMonotoneCounterexample)
    (D : InitialProductBranchEigenData C) :
    Nonempty
      (CommonBranchEigenCoordinate C.finitePiece_P C.finitePiece_Q D.rho) := by
  exact commonBranchEigenCoordinate_exists
    C.finitePiece_P C.finitePiece_Q C.commute C.onto_P C.onto_Q
    D.one_lt_rho D.coordinate D.coordinate_monotone
    D.coordinate_rightEndpoint D.product_eigen

/-! ## Descent through a general surjective coordinate -/

/-- The choice-defined descent through an arbitrary surjective coordinate. -/
noncomputable def coordinateDescent
    (θ : IntervalMap) (hθ : Surjective θ) (T : IntervalMap)
    (_hrespect : RespectsFibres θ T) : IntervalMap :=
  fun y => θ (T (Classical.choose (hθ y)))

/-- The choice-defined coordinate descent satisfies the semiconjugacy square. -/
theorem coordinateDescent_intertwines
    (θ : IntervalMap) (hθ : Surjective θ) (T : IntervalMap)
    (hrespect : RespectsFibres θ T) :
    Intertwines θ T (coordinateDescent θ hθ T hrespect) := by
  intro x
  apply hrespect
  exact (Classical.choose_spec (hθ (θ x))).symm

/-- Descent through a continuous quotient coordinate is continuous. -/
theorem coordinateDescent_continuous
    (θ : IntervalMap) (hθsurj : Surjective θ) (hθcont : Continuous θ)
    (T : IntervalMap) (hTcont : Continuous T)
    (hrespect : RespectsFibres θ T) :
    Continuous (coordinateDescent θ hθsurj T hrespect) := by
  have hquot : Topology.IsQuotientMap θ :=
    IsQuotientMap.of_surjective_continuous hθsurj hθcont
  apply hquot.continuous_iff.mpr
  have heq : coordinateDescent θ hθsurj T hrespect ∘ θ = θ ∘ T := by
    funext x
    exact (coordinateDescent_intertwines θ hθsurj T hrespect x).symm
  rw [heq]
  exact hθcont.comp hTcont

/-- An onto source map descends to an onto target map. -/
theorem coordinateDescent_surjective
    (θ : IntervalMap) (hθsurj : Surjective θ) (T : IntervalMap)
    (hrespect : RespectsFibres θ T) (hTsurj : Surjective T) :
    Surjective (coordinateDescent θ hθsurj T hrespect) := by
  intro y
  obtain ⟨x, hx⟩ := hθsurj y
  obtain ⟨z, hz⟩ := hTsurj x
  refine ⟨θ z, ?_⟩
  calc
    coordinateDescent θ hθsurj T hrespect (θ z) = θ (T z) :=
      (coordinateDescent_intertwines θ hθsurj T hrespect z).symm
    _ = θ x := by rw [hz]
    _ = y := hx

/-- Commutation descends through a common surjective coordinate. -/
theorem coordinateDescents_commute
    (θ : IntervalMap) (hθsurj : Surjective θ) (P Q : IntervalMap)
    (hP : RespectsFibres θ P) (hQ : RespectsFibres θ Q)
    (hcomm : Function.Commute P Q) :
    Function.Commute (coordinateDescent θ hθsurj P hP)
      (coordinateDescent θ hθsurj Q hQ) := by
  intro y
  obtain ⟨x, rfl⟩ := hθsurj y
  let Pbar := coordinateDescent θ hθsurj P hP
  let Qbar := coordinateDescent θ hθsurj Q hQ
  have hinterP := coordinateDescent_intertwines θ hθsurj P hP
  have hinterQ := coordinateDescent_intertwines θ hθsurj Q hQ
  change Pbar (Qbar (θ x)) = Qbar (Pbar (θ x))
  calc
    Pbar (Qbar (θ x)) = Pbar (θ (Q x)) :=
      congrArg Pbar (hinterQ x).symm
    _ = θ (P (Q x)) := (hinterP (Q x)).symm
    _ = θ (Q (P x)) := congrArg θ (hcomm x)
    _ = Qbar (θ (P x)) := hinterQ (P x)
    _ = Qbar (Pbar (θ x)) := congrArg Qbar (hinterP x)

/-! ### Finite-cell propagation for zero coordinate length -/

/-- Adjoin one interval point to a real partition. -/
noncomputable def RealPartition.adjoinPointR5
    (p : RealPartition) (x : I) : RealPartition where
  points := insert (x : ℝ) p.points
  zero_mem := Finset.mem_insert_of_mem p.zero_mem
  one_mem := Finset.mem_insert_of_mem p.one_mem
  points_subset := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact x.property
    · exact p.points_subset hz

theorem RealPartition.adjoinPointR5_refines
    (p : RealPartition) (x : I) :
    (p.adjoinPointR5 x).Refines p := by
  intro z hz
  exact Finset.mem_insert_of_mem hz

@[simp] theorem RealPartition.mem_adjoinPointR5
    (p : RealPartition) (x : I) :
    (x : ℝ) ∈ (p.adjoinPointR5 x).points := by
  simp [RealPartition.adjoinPointR5]

/-- Number of vertices of `p` strictly to the left of `x`. -/
private noncomputable def partitionLowerRankR5
    (p : RealPartition) (x : I) : ℕ :=
  (p.points.filter fun z => z < (x : ℝ)).card

private theorem partitionLowerRankR5_lt {p : RealPartition} {a : ℝ}
    (ha : a ∈ p.points) (haI : a ∈ I) {x : I} (hax : a < (x : ℝ)) :
    partitionLowerRankR5 p ⟨a, haI⟩ < partitionLowerRankR5 p x := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.trans hax⟩
  · intro heq
    have haright : a ∈ p.points.filter fun z => z < (x : ℝ) :=
      Finset.mem_filter.mpr ⟨ha, hax⟩
    rw [← heq] at haright
    exact (Finset.mem_filter.mp haright).2.false

/-- Every non-left endpoint lies in a cell with a strictly smaller left
endpoint. -/
private theorem exists_adjacent_left_of_posR5
    (p : RealPartition) (x : I) (hxpos : (0 : ℝ) < x) :
    ∃ a b : ℝ, p.Adjacent a b ∧ a < (x : ℝ) ∧ (x : ℝ) ≤ b := by
  classical
  by_cases hxvertex : (x : ℝ) ∈ p.points
  · let lower := p.points.filter fun z => z < (x : ℝ)
    have hlower : lower.Nonempty := by
      refine ⟨0, ?_⟩
      simp [lower, p.zero_mem, hxpos]
    obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
    have ha' := Finset.mem_filter.mp ha
    refine ⟨a, (x : ℝ), ⟨ha'.1, hxvertex, ha'.2, ?_⟩,
      ha'.2, le_rfl⟩
    intro c hc hac
    have hclower : c ∈ lower := Finset.mem_filter.mpr ⟨hc, hac.2⟩
    have hca : c ≤ a := by simpa using hamax c hclower
    exact (not_lt_of_ge hca) hac.1
  · obtain ⟨a, b, hab, hax, hxb⟩ := p.exists_adjacent_containing x
    have hax' : a < (x : ℝ) := lt_of_le_of_ne hax fun hxa =>
      hxvertex (hxa ▸ hab.1)
    exact ⟨a, b, hab, hax', hxb⟩

/-- Cellwise constancy propagates across a closed interval whose left
endpoint is a partition vertex. -/
private theorem eq_of_cellwise_on_IccR5
    (p : RealPartition) (F : I → I) {x y : I}
    (hxy : x ≤ y) (hxvertex : (x : ℝ) ∈ p.points)
    (hcell : ∀ {a b : ℝ}, p.Adjacent a b → ∀ {u v : I},
      u ∈ intervalCell a b → v ∈ intervalCell a b →
      x ≤ u → v ≤ y → u ≤ v → F u = F v) :
    F x = F y := by
  have hprop : ∀ z : I, z ∈ Set.Icc x y → F x = F z := by
    intro z
    refine (measure (partitionLowerRankR5 p)).wf.induction
      (C := fun z => z ∈ Set.Icc x y → F x = F z) z ?_
    intro z ih hz
    by_cases hzx : z = x
    · subst z
      rfl
    · have hxz : x < z := lt_of_le_of_ne hz.1 (Ne.symm hzx)
      have hzpos : (0 : ℝ) < z := x.property.1.trans_lt hxz
      obtain ⟨a, b, hab, haz, hzb⟩ :=
        exists_adjacent_left_of_posR5 p z hzpos
      let za : I := ⟨a, p.points_subset hab.1⟩
      have hxza : x ≤ za := by
        apply le_of_not_gt
        intro hax
        have haxreal : a < (x : ℝ) := hax
        have hxzreal : (x : ℝ) < (z : ℝ) := hxz
        exact hab.2.2.2 (x : ℝ) hxvertex
          ⟨haxreal, hxzreal.trans_le hzb⟩
      have hzay : za ≤ y := haz.le.trans hz.2
      have hrank : partitionLowerRankR5 p za < partitionLowerRankR5 p z :=
        partitionLowerRankR5_lt hab.1 (p.points_subset hab.1) haz
      have hza : F x = F za := ih za hrank ⟨hxza, hzay⟩
      have hzaCell : za ∈ intervalCell a b :=
        ⟨le_rfl, hab.2.2.1.le⟩
      have hzCell : z ∈ intervalCell a b := ⟨haz.le, hzb⟩
      exact hza.trans
        (hcell hab hzaCell hzCell hxza hz.2 haz.le)
  exact hprop y ⟨hxy, le_rfl⟩

/-- A nondecreasing branch eigen-coordinate sends every coordinate fibre to
a coordinate fibre under the source map. -/
theorem branchEigenCoordinate_respectsFibres
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (S : NormalizedContinuousCoordinate)
    (hSmono : Monotone (fun x : I => S x))
    (hSmem : ∀ x : I, S x ∈ I)
    (scale : ℝ)
    (heigen : branchLengthOperator hT S = scale • S) :
    RespectsFibres (fun x => ⟨S x, hSmem x⟩) T := by
  let θ : IntervalMap := fun x => ⟨S x, hSmem x⟩
  change RespectsFibres θ T
  have hordered {x y : I} (hxy : x ≤ y) (hcoord : θ x = θ y) :
      θ (T x) = θ (T y) := by
    have hSxy : S x = S y := congrArg Subtype.val hcoord
    let w := chosenMonotonicityPartition hT
    let r := w.partition.adjoinPointR5 x
    let wr : MonotonicityPartition T :=
      w.refine r (RealPartition.adjoinPointR5_refines w.partition x)
    apply eq_of_cellwise_on_IccR5 r (fun z => θ (T z)) hxy
      (RealPartition.mem_adjoinPointR5 w.partition x)
    intro a b hab u v hu hv hxu hvy huv
    apply Subtype.ext
    have hSu : S u = S x := by
      apply le_antisymm
      · rw [hSxy]
        exact hSmono (huv.trans hvy)
      · exact hSmono hxu
    have hSv : S v = S x := by
      apply le_antisymm
      · rw [hSxy]
        exact hSmono hvy
      · exact hSmono (hxu.trans huv)
    have hinc := branchLength_increment hT wr S hab hu hv huv
    have heu := congrArg (fun R : NormalizedContinuousCoordinate => R u) heigen
    have hev := congrArg (fun R : NormalizedContinuousCoordinate => R v) heigen
    change branchLength hT S u = scale * S u at heu
    change branchLength hT S v = scale * S v at hev
    have hlen : coordinateLength (fun z : I => S z) (T u) (T v) = 0 := by
      rw [← hinc, heu, hev, hSu, hSv]
      ring
    rw [coordinateLength_eq_abs_sub_of_monotone
      (fun z : I => S z) hSmono] at hlen
    exact (sub_eq_zero.mp (abs_eq_zero.mp hlen)).symm
  intro x y hcoord
  rcases le_total x y with hxy | hyx
  · exact hordered hxy hcoord
  · exact (hordered hyx hcoord.symm).symm

/-! ### Coordinate-image partitions -/

/-- Apply an endpoint-preserving interval coordinate to all source vertices
and remove duplicate images. -/
noncomputable def RealPartition.coordinateImageR5
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

/-- Consecutive distinct coordinate-images of source vertices come from the
endpoints of an actual source cell.  Flat coordinate intervals merely cause
duplicate image vertices, which the target `Finset` removes. -/
private theorem exists_source_adjacent_of_coordinateImageR5_adjacent
    (θ : IntervalMap) (hθsurj : Surjective θ) (hθmono : Monotone θ)
    (hleft : θ leftEndpoint = leftEndpoint)
    (hright : θ rightEndpoint = rightEndpoint)
    (p : RealPartition) {a b : ℝ}
    (hab : (p.coordinateImageR5 θ hleft hright).Adjacent a b) :
    ∃ c d : ℝ, ∃ hcd : p.Adjacent c d,
      (θ ⟨c, p.points_subset hcd.1⟩ : ℝ) = a ∧
      (θ ⟨d, p.points_subset hcd.2.1⟩ : ℝ) = b := by
  classical
  let pθ := p.coordinateImageR5 θ hleft hright
  have haI : a ∈ I := pθ.points_subset hab.1
  have hbI : b ∈ I := pθ.points_subset hab.2.1
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith [hab.2.2.1]
  have hmb : m < b := by dsimp [m]; linarith [hab.2.2.1]
  have hmI : m ∈ I := ⟨haI.1.trans ham.le, hmb.le.trans hbI.2⟩
  let mI : I := ⟨m, hmI⟩
  obtain ⟨x, hxcoord⟩ := hθsurj mI
  have hxright : x < rightEndpoint := by
    by_contra h
    have hxEq : x = rightEndpoint :=
      le_antisymm x.property.2 (le_of_not_gt h)
    have hθrightm : θ rightEndpoint = mI := by
      simpa [hxEq] using hxcoord
    have hmright : mI = rightEndpoint :=
      hθrightm.symm.trans hright
    have hmreal : m = 1 := congrArg Subtype.val hmright
    linarith [hmb, hbI.2]
  obtain ⟨c, d, hcd, hcx, hxd⟩ := p.exists_adjacent_Ico hxright
  let cI : I := ⟨c, p.points_subset hcd.1⟩
  let dI : I := ⟨d, p.points_subset hcd.2.1⟩
  have hcIx : cI ≤ x := hcx
  have hxdI : x < dI := hxd
  have ha_mem : a ∈ p.points.attach.image (fun z =>
      (θ ⟨z.1, p.points_subset z.2⟩ : ℝ)) := by
    simpa [pθ, RealPartition.coordinateImageR5] using hab.1
  have hb_mem : b ∈ p.points.attach.image (fun z =>
      (θ ⟨z.1, p.points_subset z.2⟩ : ℝ)) := by
    simpa [pθ, RealPartition.coordinateImageR5] using hab.2.1
  rcases Finset.mem_image.mp ha_mem with ⟨av, _havmem, hθav⟩
  rcases Finset.mem_image.mp hb_mem with ⟨bv, _hbvmem, hθbv⟩
  let aI : I := ⟨av.1, p.points_subset av.2⟩
  let bI : I := ⟨bv.1, p.points_subset bv.2⟩
  have hθa : (θ aI : ℝ) = a := by simpa [aI] using hθav
  have hθb : (θ bI : ℝ) = b := by simpa [bI] using hθbv
  have haIx : aI < x := by
    apply lt_of_not_ge
    intro hxa
    have hmono := hθmono hxa
    change (θ x : ℝ) ≤ (θ aI : ℝ) at hmono
    have hma : m ≤ a := by simpa [mI, hxcoord, hθa] using hmono
    exact (not_le_of_gt ham) hma
  have hxbI : x < bI := by
    apply lt_of_not_ge
    intro hbx
    have hmono := hθmono hbx
    change (θ bI : ℝ) ≤ (θ x : ℝ) at hmono
    have hbm : b ≤ m := by simpa [mI, hxcoord, hθb] using hmono
    exact (not_le_of_gt hmb) hbm
  have haIc : aI ≤ cI := by
    apply le_of_not_gt
    intro hca
    exact hcd.2.2.2 (aI : ℝ) av.2 ⟨hca, haIx.trans hxdI⟩
  have hdIb : dI ≤ bI := by
    apply le_of_not_gt
    intro hbd
    exact hcd.2.2.2 (bI : ℝ) bv.2
      ⟨hcIx.trans_lt hxbI, hbd⟩
  have hθc_mem : (θ cI : ℝ) ∈ pθ.points := by
    apply Finset.mem_image.mpr
    refine ⟨⟨c, hcd.1⟩, by simp, rfl⟩
  have hθd_mem : (θ dI : ℝ) ∈ pθ.points := by
    apply Finset.mem_image.mpr
    refine ⟨⟨d, hcd.2.1⟩, by simp, rfl⟩
  have ha_le_θc : a ≤ (θ cI : ℝ) := by
    have hmono := hθmono haIc
    change (θ aI : ℝ) ≤ (θ cI : ℝ) at hmono
    simpa [hθa] using hmono
  have hθc_le_a : (θ cI : ℝ) ≤ a := by
    apply le_of_not_gt
    intro haθc
    have hmono := hθmono hcIx
    have hθc_le_m : (θ cI : ℝ) ≤ m := by
      simpa [mI, hxcoord] using hmono
    exact hab.2.2.2 (θ cI : ℝ) hθc_mem
      ⟨haθc, hθc_le_m.trans_lt hmb⟩
  have hθd_le_b : (θ dI : ℝ) ≤ b := by
    have hmono := hθmono hdIb
    change (θ dI : ℝ) ≤ (θ bI : ℝ) at hmono
    simpa [hθb] using hmono
  have hb_le_θd : b ≤ (θ dI : ℝ) := by
    apply le_of_not_gt
    intro hθdb
    have hmono := hθmono hxdI.le
    have hm_le_θd : m ≤ (θ dI : ℝ) := by
      simpa [mI, hxcoord] using hmono
    exact hab.2.2.2 (θ dI : ℝ) hθd_mem
      ⟨ham.trans_le hm_le_θd, hθdb⟩
  exact ⟨c, d, hcd, le_antisymm hθc_le_a ha_le_θc,
    le_antisymm hθd_le_b hb_le_θd⟩

/-! ## The quotient attached to a common branch eigen-coordinate -/

namespace CommonBranchEigenCoordinate

variable {P Q : IntervalMap}
  {hP : FinitePieceMonotone P} {hQ : FinitePieceMonotone Q}
  {rho : ℝ}

/-- The common eigen-coordinate respects the fibres of both generators. -/
theorem respectsFibres_generators
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    RespectsFibres E.intervalCoordinate P ∧
      RespectsFibres E.intervalCoordinate Q := by
  constructor
  · simpa [intervalCoordinate] using
      (branchEigenCoordinate_respectsFibres hP E.coordinate E.monotone
        E.coordinate_mem_I E.scaleP E.eigen_P)
  · simpa [intervalCoordinate] using
      (branchEigenCoordinate_respectsFibres hQ E.coordinate E.monotone
        E.coordinate_mem_I E.scaleQ E.eigen_Q)

/-- The first descended generator. -/
noncomputable def factorP
    (E : CommonBranchEigenCoordinate hP hQ rho) : IntervalMap :=
  coordinateDescent E.intervalCoordinate E.surjective_intervalCoordinate P
    E.respectsFibres_generators.1

/-- The second descended generator. -/
noncomputable def factorQ
    (E : CommonBranchEigenCoordinate hP hQ rho) : IntervalMap :=
  coordinateDescent E.intervalCoordinate E.surjective_intervalCoordinate Q
    E.respectsFibres_generators.2

theorem intertwines_factorP
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    Intertwines E.intervalCoordinate P E.factorP :=
  coordinateDescent_intertwines E.intervalCoordinate
    E.surjective_intervalCoordinate P E.respectsFibres_generators.1

theorem intertwines_factorQ
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    Intertwines E.intervalCoordinate Q E.factorQ :=
  coordinateDescent_intertwines E.intervalCoordinate
    E.surjective_intervalCoordinate Q E.respectsFibres_generators.2

theorem continuous_factorP
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    Continuous E.factorP :=
  coordinateDescent_continuous E.intervalCoordinate
    E.surjective_intervalCoordinate E.continuous_intervalCoordinate P
    hP.continuous E.respectsFibres_generators.1

theorem continuous_factorQ
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    Continuous E.factorQ :=
  coordinateDescent_continuous E.intervalCoordinate
    E.surjective_intervalCoordinate E.continuous_intervalCoordinate Q
    hQ.continuous E.respectsFibres_generators.2

theorem surjective_factorP
    (E : CommonBranchEigenCoordinate hP hQ rho) (hPonto : Surjective P) :
    Surjective E.factorP :=
  coordinateDescent_surjective E.intervalCoordinate
    E.surjective_intervalCoordinate P E.respectsFibres_generators.1 hPonto

theorem surjective_factorQ
    (E : CommonBranchEigenCoordinate hP hQ rho) (hQonto : Surjective Q) :
    Surjective E.factorQ :=
  coordinateDescent_surjective E.intervalCoordinate
    E.surjective_intervalCoordinate Q E.respectsFibres_generators.2 hQonto

theorem factors_commute
    (E : CommonBranchEigenCoordinate hP hQ rho)
    (hcomm : Function.Commute P Q) :
    Function.Commute E.factorP E.factorQ :=
  coordinateDescents_commute E.intervalCoordinate
    E.surjective_intervalCoordinate P Q E.respectsFibres_generators.1
      E.respectsFibres_generators.2 hcomm

/-- Target partition induced from the chosen source partition of `P`. -/
noncomputable def factorPartitionP
    (E : CommonBranchEigenCoordinate hP hQ rho) : RealPartition :=
  (chosenMonotonicityPartition hP).partition.coordinateImageR5
    E.intervalCoordinate E.intervalCoordinate_leftEndpoint
      E.intervalCoordinate_rightEndpoint

/-- Target partition induced from the chosen source partition of `Q`. -/
noncomputable def factorPartitionQ
    (E : CommonBranchEigenCoordinate hP hQ rho) : RealPartition :=
  (chosenMonotonicityPartition hQ).partition.coordinateImageR5
    E.intervalCoordinate E.intervalCoordinate_leftEndpoint
      E.intervalCoordinate_rightEndpoint

/-- On every cell of the deduplicated coordinate-image partition, the
descended map has signed slope `±scale`. -/
private theorem factor_affineOn_coordinateImageR5_cell
    {T Tbar θ : IntervalMap} (hT : FinitePieceMonotone T)
    (PT : MonotonicityPartition T)
    (S : NormalizedContinuousCoordinate)
    (hSmono : Monotone (fun x : I => S x))
    (hθval : ∀ x : I, (θ x : ℝ) = S x)
    (hθcont : Continuous θ) (hθmono : Monotone θ)
    (hθsurj : Surjective θ)
    (hleft : θ leftEndpoint = leftEndpoint)
    (hright : θ rightEndpoint = rightEndpoint)
    (scale : ℝ) (hscale : 0 < scale)
    (heigen : branchLengthOperator hT S = scale • S)
    (hintertwines : Intertwines θ T Tbar)
    {a b : ℝ}
    (hab : (PT.partition.coordinateImageR5 θ hleft hright).Adjacent a b) :
    ∃ m c : ℝ, |m| = scale ∧
      ∀ z ∈ intervalCell a b,
        (Tbar z : ℝ) = m * (z : ℝ) + c := by
  classical
  obtain ⟨c, d, hcd, hθc, hθd⟩ :=
    exists_source_adjacent_of_coordinateImageR5_adjacent
      θ hθsurj hθmono hleft hright PT.partition hab
  let cI : I := ⟨c, PT.partition.points_subset hcd.1⟩
  let dI : I := ⟨d, PT.partition.points_subset hcd.2.1⟩
  have hcdI : cI ≤ dI := hcd.2.2.1.le
  have hweak := PT.weaklyMonotoneOn_cell hcd
  change MonotoneOn T (Set.Icc cI dI) ∨
    AntitoneOn T (Set.Icc cI dI) at hweak
  rcases hweak with hmono | hanti
  · refine ⟨scale, (θ (T cI) : ℝ) - scale * a,
      abs_of_pos hscale, ?_⟩
    intro z hz
    have hzcoord : z ∈ Set.Icc (θ cI) (θ dI) := by
      constructor
      · change (θ cI : ℝ) ≤ (z : ℝ)
        simpa [cI] using hθc.trans_le hz.1
      · change (z : ℝ) ≤ (θ dI : ℝ)
        simpa [dI] using hz.2.trans hθd.symm.le
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc hcdI
      hθcont.continuousOn hzcoord
    have hcu : cI ≤ u := hu.1
    have hud : u ≤ dI := hu.2
    have hc_mem : cI ∈ Set.Icc cI dI := ⟨le_rfl, hcdI⟩
    have hTcu : T cI ≤ T u := hmono hc_mem hu hcu
    have hinc := branchLength_increment hT PT S hcd hc_mem hu hcu
    have hec := congrArg
      (fun R : NormalizedContinuousCoordinate => R cI) heigen
    have heu := congrArg
      (fun R : NormalizedContinuousCoordinate => R u) heigen
    change branchLength hT S cI = scale * S cI at hec
    change branchLength hT S u = scale * S u at heu
    have htarget :
        coordinateLength (fun x : I => S x) (T cI) (T u) =
          S (T u) - S (T cI) := by
      rw [coordinateLength_eq_abs_sub_of_monotone
        (fun x : I => S x) hSmono,
        abs_of_nonneg (sub_nonneg.mpr (hSmono hTcu))]
    have hrealS : S (T u) - S (T cI) =
        scale * (S u - S cI) := by
      rw [htarget] at hinc
      linarith
    have hreal : (θ (T u) : ℝ) - (θ (T cI) : ℝ) =
        scale * ((θ u : ℝ) - (θ cI : ℝ)) := by
      simpa only [hθval] using hrealS
    have hfactor : Tbar z = θ (T u) := by
      calc
        Tbar z = Tbar (θ u) := congrArg Tbar hθu.symm
        _ = θ (T u) := (hintertwines u).symm
    have hfactor_real := congrArg Subtype.val hfactor
    have hθu_real := congrArg Subtype.val hθu
    calc
      (Tbar z : ℝ) = (θ (T u) : ℝ) := hfactor_real
      _ = scale * (θ u : ℝ) +
          ((θ (T cI) : ℝ) - scale * a) := by
        have hθc' : (θ cI : ℝ) = a := by simpa [cI] using hθc
        nlinarith
      _ = scale * (z : ℝ) +
          ((θ (T cI) : ℝ) - scale * a) := by rw [hθu_real]
  · refine ⟨-scale, (θ (T cI) : ℝ) + scale * a,
      by rw [abs_neg, abs_of_pos hscale], ?_⟩
    intro z hz
    have hzcoord : z ∈ Set.Icc (θ cI) (θ dI) := by
      constructor
      · change (θ cI : ℝ) ≤ (z : ℝ)
        simpa [cI] using hθc.trans_le hz.1
      · change (z : ℝ) ≤ (θ dI : ℝ)
        simpa [dI] using hz.2.trans hθd.symm.le
    obtain ⟨u, hu, hθu⟩ := intermediate_value_Icc hcdI
      hθcont.continuousOn hzcoord
    have hcu : cI ≤ u := hu.1
    have hc_mem : cI ∈ Set.Icc cI dI := ⟨le_rfl, hcdI⟩
    have hTuc : T u ≤ T cI := hanti hc_mem hu hcu
    have hinc := branchLength_increment hT PT S hcd hc_mem hu hcu
    have hec := congrArg
      (fun R : NormalizedContinuousCoordinate => R cI) heigen
    have heu := congrArg
      (fun R : NormalizedContinuousCoordinate => R u) heigen
    change branchLength hT S cI = scale * S cI at hec
    change branchLength hT S u = scale * S u at heu
    have htarget :
        coordinateLength (fun x : I => S x) (T cI) (T u) =
          S (T cI) - S (T u) := by
      rw [coordinateLength_eq_abs_sub_of_monotone
        (fun x : I => S x) hSmono,
        abs_of_nonpos (sub_nonpos.mpr (hSmono hTuc))]
      ring
    have hrealS : S (T cI) - S (T u) =
        scale * (S u - S cI) := by
      rw [htarget] at hinc
      linarith
    have hreal : (θ (T cI) : ℝ) - (θ (T u) : ℝ) =
        scale * ((θ u : ℝ) - (θ cI : ℝ)) := by
      simpa only [hθval] using hrealS
    have hfactor : Tbar z = θ (T u) := by
      calc
        Tbar z = Tbar (θ u) := congrArg Tbar hθu.symm
        _ = θ (T u) := (hintertwines u).symm
    have hfactor_real := congrArg Subtype.val hfactor
    have hθu_real := congrArg Subtype.val hθu
    calc
      (Tbar z : ℝ) = (θ (T u) : ℝ) := hfactor_real
      _ = -scale * (θ u : ℝ) +
          ((θ (T cI) : ℝ) + scale * a) := by
        have hθc' : (θ cI : ℝ) = a := by simpa [cI] using hθc
        nlinarith
      _ = -scale * (z : ℝ) +
          ((θ (T cI) : ℝ) + scale * a) := by rw [hθu_real]

/-- The branch-increment identity makes both descendants finite-piece PL
with the two eigenvalues as their exact absolute branch slopes. -/
theorem factors_haveConstantAbsoluteSlope
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    HasConstantAbsoluteSlope E.factorP E.scaleP ∧
      HasConstantAbsoluteSlope E.factorQ E.scaleQ := by
  constructor
  · refine ⟨E.continuous_factorP, E.factorPartitionP, ?_⟩
    intro a b hab
    apply factor_affineOn_coordinateImageR5_cell
      hP (chosenMonotonicityPartition hP) E.coordinate E.monotone
      (θ := E.intervalCoordinate)
      (fun _ => rfl) E.continuous_intervalCoordinate
      E.monotone_intervalCoordinate E.surjective_intervalCoordinate
      E.intervalCoordinate_leftEndpoint E.intervalCoordinate_rightEndpoint
      E.scaleP E.scaleP_pos E.eigen_P E.intertwines_factorP
    simpa [factorPartitionP] using hab
  · refine ⟨E.continuous_factorQ, E.factorPartitionQ, ?_⟩
    intro a b hab
    apply factor_affineOn_coordinateImageR5_cell
      hQ (chosenMonotonicityPartition hQ) E.coordinate E.monotone
      (θ := E.intervalCoordinate)
      (fun _ => rfl) E.continuous_intervalCoordinate
      E.monotone_intervalCoordinate E.surjective_intervalCoordinate
      E.intervalCoordinate_leftEndpoint E.intervalCoordinate_rightEndpoint
      E.scaleQ E.scaleQ_pos E.eigen_Q E.intertwines_factorQ
    simpa [factorPartitionQ] using hab

/-- The coordinate and its two descents form a common monotone factor. -/
def monotonePairFactor
    (E : CommonBranchEigenCoordinate hP hQ rho) :
    MonotonePairFactor P Q E.factorP E.factorQ where
  coordinate := E.intervalCoordinate
  continuous_coordinate := E.continuous_intervalCoordinate
  monotone_coordinate := E.monotone_intervalCoordinate
  surjective_coordinate := E.surjective_intervalCoordinate
  intertwines_P := E.intertwines_factorP
  intertwines_Q := E.intertwines_factorQ

end CommonBranchEigenCoordinate

/-- All quotient data delivered by the common branch eigen-coordinate. -/
structure ConstantSlopeQuotientData
    (C : MinimalPiecewiseMonotoneCounterexample) where
  rho : ℝ
  one_lt_rho : 1 < rho
  eigen : CommonBranchEigenCoordinate C.finitePiece_P C.finitePiece_Q rho
  product_scale_gt_one : 1 < eigen.scaleP * eigen.scaleQ
  finitePiece_factorP : FinitePiecePL eigen.factorP
  finitePiece_factorQ : FinitePiecePL eigen.factorQ
  onto_factorP : IsOnto eigen.factorP
  onto_factorQ : IsOnto eigen.factorQ
  factors_commute : Function.Commute eigen.factorP eigen.factorQ
  constantSlope_factorP :
    HasConstantAbsoluteSlope eigen.factorP eigen.scaleP
  constantSlope_factorQ :
    HasConstantAbsoluteSlope eigen.factorQ eigen.scaleQ
  common_factor : MonotonePairFactor C.P C.Q eigen.factorP eigen.factorQ

/-- Construct the common onto constant-slope PL quotient from the product
eigen-coordinate and the common branch eigen-coordinate theorem. -/
theorem constantSlope_quotient_exists
    (C : MinimalPiecewiseMonotoneCounterexample) :
    Nonempty (ConstantSlopeQuotientData C) := by
  obtain ⟨D⟩ := initialProductBranchEigenData_exists C
  obtain ⟨E⟩ := commonBranchEigenCoordinate_of_initialProduct C D
  have hslopes := E.factors_haveConstantAbsoluteSlope
  refine ⟨{
    rho := D.rho
    one_lt_rho := D.one_lt_rho
    eigen := E
    product_scale_gt_one := ?_
    finitePiece_factorP := hslopes.1.finitePiecePL
    finitePiece_factorQ := hslopes.2.finitePiecePL
    onto_factorP := E.surjective_factorP C.onto_P
    onto_factorQ := E.surjective_factorQ C.onto_Q
    factors_commute := E.factors_commute C.commute
    constantSlope_factorP := hslopes.1
    constantSlope_factorQ := hslopes.2
    common_factor := E.monotonePairFactor }⟩
  rw [E.scale_product]
  exact D.one_lt_rho

/-! ## Fixed descent and minimality through a monotone factor -/

/-- FactorBase gives exact fixed descent for every word `P^m Q^n`. -/
theorem MonotonePairFactor.fixedPoints_word_descendExactly
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar)
    (hPcont : Continuous P) (hQcont : Continuous Q) (m n : ℕ) :
    FixedPointsDescendExactly F.coordinate
      (positiveWordMap P Q m n) (positiveWordMap Pbar Qbar m n) :=
  F.fixedPoints_positiveWord_descendExactly hPcont hQcont m n

/-- A common fixed point downstairs would give a common invariant interval
fibre upstairs, contradicting minimality. -/
theorem MonotonePairFactor.target_noCommonFixedPoint_of_coreMinimal
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar)
    (hminimal : ∀ J : ClosedSubinterval,
      IsCommonInvariantCore P Q J → J.carrier = Set.univ) :
    ¬HasCommonFixedPoint Pbar Qbar := by
  rintro ⟨y, hyP, hyQ⟩
  change Pbar y = y at hyP
  change Qbar y = y at hyQ
  obtain ⟨D⟩ := monotoneFibreInterval_exists F.coordinate
    F.continuous_coordinate F.monotone_coordinate
    F.surjective_coordinate y
  have hcore : IsCommonInvariantCore P Q D.interval := by
    constructor
    · intro z hz
      rw [D.carrier_eq] at hz ⊢
      calc
        F.coordinate (P z) = Pbar (F.coordinate z) := F.intertwines_P z
        _ = Pbar y := congrArg Pbar hz
        _ = y := hyP
    · intro z hz
      rw [D.carrier_eq] at hz ⊢
      calc
        F.coordinate (Q z) = Qbar (F.coordinate z) := F.intertwines_Q z
        _ = Qbar y := congrArg Qbar hz
        _ = y := hyQ
  have hall := hminimal D.interval hcore
  have hconst (x : I) : F.coordinate x = y := by
    have hx : x ∈ D.interval.carrier := by
      rw [hall]
      exact Set.mem_univ x
    rw [D.carrier_eq] at hx
    exact hx
  obtain ⟨x₀, hx₀⟩ := F.surjective_coordinate leftEndpoint
  obtain ⟨x₁, hx₁⟩ := F.surjective_coordinate rightEndpoint
  have hy₀ : y = leftEndpoint := (hconst x₀).symm.trans hx₀
  have hy₁ : y = rightEndpoint := (hconst x₁).symm.trans hx₁
  have hends : leftEndpoint = rightEndpoint := hy₀.symm.trans hy₁
  have hvals := congrArg Subtype.val hends
  norm_num at hvals

/-- A continuous monotone surjection pulls a nonempty target interval back
to a nonempty source interval. -/
structure MonotonePreimageIntervalData
    (π : IntervalMap) (J : ClosedSubinterval) where
  interval : ClosedSubinterval
  carrier_eq : interval.carrier = π ⁻¹' J.carrier

theorem monotonePreimageInterval_exists
    (π : IntervalMap) (hπcont : Continuous π) (hπmono : Monotone π)
    (hπsurj : Surjective π) (J : ClosedSubinterval) :
    Nonempty (MonotonePreimageIntervalData π J) := by
  let pre : Set I := π ⁻¹' J.carrier
  have hpre_nonempty : pre.Nonempty := by
    obtain ⟨x, hx⟩ := hπsurj J.left
    refine ⟨x, ?_⟩
    change π x ∈ J.carrier
    rw [hx]
    exact J.left_mem_carrier
  have hpre_closed : IsClosed pre := isClosed_Icc.preimage hπcont
  have hpre_compact : IsCompact pre := hpre_closed.isCompact
  obtain ⟨l, hl, hlmin⟩ := hpre_compact.exists_isMinOn
    hpre_nonempty continuous_id.continuousOn
  obtain ⟨r, hr, hrmax⟩ := hpre_compact.exists_isMaxOn
    hpre_nonempty continuous_id.continuousOn
  have hlr : l ≤ r := hlmin hr
  let K : ClosedSubinterval := ⟨l, r, hlr⟩
  have hcarrier : K.carrier = pre := by
    change Set.Icc l r = pre
    apply Set.Subset.antisymm
    · intro z hz
      have hlπz := hπmono hz.1
      have hzπr := hπmono hz.2
      exact ⟨hl.1.trans hlπz, hzπr.trans hr.2⟩
    · intro z hz
      exact ⟨hlmin hz, hrmax hz⟩
  exact ⟨⟨K, hcarrier⟩⟩

/-- The inverse image of a common invariant target interval is a common
invariant source interval, so minimality descends. -/
theorem MonotonePairFactor.target_coreMinimal
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar)
    (hminimal : ∀ J : ClosedSubinterval,
      IsCommonInvariantCore P Q J → J.carrier = Set.univ) :
    ∀ J : ClosedSubinterval,
      IsCommonInvariantCore Pbar Qbar J → J.carrier = Set.univ := by
  intro J hJ
  obtain ⟨D⟩ := monotonePreimageInterval_exists F.coordinate
    F.continuous_coordinate F.monotone_coordinate
      F.surjective_coordinate J
  have hcore : IsCommonInvariantCore P Q D.interval := by
    constructor
    · intro z hz
      rw [D.carrier_eq] at hz ⊢
      have hPmem := hJ.1 hz
      simpa [F.intertwines_P z] using hPmem
    · intro z hz
      rw [D.carrier_eq] at hz ⊢
      have hQmem := hJ.2 hz
      simpa [F.intertwines_Q z] using hQmem
  have hall := hminimal D.interval hcore
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨x, hx⟩ := F.surjective_coordinate y
  have hxpre : x ∈ F.coordinate ⁻¹' J.carrier := by
    rw [← D.carrier_eq, hall]
    exact Set.mem_univ x
  simpa [hx] using hxpre

/-! ## Individual expansion and final linearization data -/

/-- The absolute slope exhibited by a nondegenerate real partition is
nonnegative. -/
private theorem constantAbsoluteSlope_nonneg
    {T : IntervalMap} {s : ℝ}
    (hslope : HasConstantAbsoluteSlope T s) : 0 ≤ s := by
  rcases hslope with ⟨_hcont, p, hp⟩
  have hleftRight : leftEndpoint < rightEndpoint := by
    simp [leftEndpoint, rightEndpoint]
  obtain ⟨a, b, hab, _ha, _hb⟩ := p.exists_adjacent_Ico hleftRight
  obtain ⟨m, _c, hm, _hformula⟩ := hp hab
  exact hm ▸ abs_nonneg m

/-- Partition vertices strictly between two interval points. -/
private noncomputable def constantSlopeIntervalVertices
    (p : RealPartition) (x y : I) : Finset ℝ :=
  p.points.filter fun z ↦ (x : ℝ) < z ∧ z < (y : ℝ)

/-- A finite-piece map of constant absolute slope `s` is globally
`s`-Lipschitz.  The proof splits at all intervening partition vertices and
telescopes the affine estimates. -/
private theorem constantAbsoluteSlope_dist_le
    {T : IntervalMap} {s : ℝ} (hslope : HasConstantAbsoluteSlope T s) :
    ∀ x y : I, dist (T x) (T y) ≤ s * dist x y := by
  classical
  rcases hslope with ⟨_hcont, p, hp⟩
  have ordered : ∀ n : ℕ, ∀ x y : I, x ≤ y →
      (constantSlopeIntervalVertices p x y).card = n →
      dist (T x) (T y) ≤ s * dist x y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x y hxy hcard
      rcases hxy.eq_or_lt with rfl | hxylt
      · simp
      by_cases hempty : constantSlopeIntervalVertices p x y = ∅
      · have hnone : ∀ z ∈ p.points,
            ¬((x : ℝ) < z ∧ z < (y : ℝ)) := by
          intro z hz hbetween
          have hzmem : z ∈ constantSlopeIntervalVertices p x y :=
            Finset.mem_filter.mpr ⟨hz, hbetween⟩
          rw [hempty] at hzmem
          simp at hzmem
        obtain ⟨c, d, hcd, hsub⟩ := p.exists_adjacent_superset
          x.property y.property hxylt hnone
        obtain ⟨m, k, hm, hformula⟩ := hp hcd
        have hxcell : x ∈ intervalCell c d := hsub ⟨le_rfl, hxy⟩
        have hycell : y ∈ intervalCell c d := hsub ⟨hxy, le_rfl⟩
        rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq,
          hformula x hxcell, hformula y hycell]
        calc
          |m * (x : ℝ) + k - (m * (y : ℝ) + k)| =
              |m| * |(x : ℝ) - (y : ℝ)| := by
                rw [← abs_mul]
                congr 1
                ring
          _ = s * |(x : ℝ) - (y : ℝ)| := by rw [hm]
          _ ≤ s * |(x : ℝ) - (y : ℝ)| := le_rfl
      · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hz' := Finset.mem_filter.mp hz
        let zI : I := ⟨z, p.points_subset hz'.1⟩
        have hxz : x < zI := hz'.2.1
        have hzy : zI < y := hz'.2.2
        have hleftSub : constantSlopeIntervalVertices p x zI ⊆
            constantSlopeIntervalVertices p x y := by
          intro w hw
          have hw' := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨hw'.1, hw'.2.1, hw'.2.2.trans hzy⟩
        have hrightSub : constantSlopeIntervalVertices p zI y ⊆
            constantSlopeIntervalVertices p x y := by
          intro w hw
          have hw' := Finset.mem_filter.mp hw
          have hxzr : (x : ℝ) < (zI : ℝ) := hxz
          exact Finset.mem_filter.mpr ⟨hw'.1, hxzr.trans hw'.2.1, hw'.2.2⟩
        have hzWhole : z ∈ constantSlopeIntervalVertices p x y := hz
        have hzNotLeft : z ∉ constantSlopeIntervalVertices p x zI := by
          simp [constantSlopeIntervalVertices, zI]
        have hzNotRight : z ∉ constantSlopeIntervalVertices p zI y := by
          simp [constantSlopeIntervalVertices, zI]
        have hleftCard : (constantSlopeIntervalVertices p x zI).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hleftSub, fun heq ↦
              hzNotLeft (heq ▸ hzWhole)⟩)
        have hrightCard : (constantSlopeIntervalVertices p zI y).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hrightSub, fun heq ↦
              hzNotRight (heq ▸ hzWhole)⟩)
        have hleft := ih _ hleftCard x zI hxz.le rfl
        have hright := ih _ hrightCard zI y hzy.le rfl
        have hdistadd : dist x zI + dist zI y = dist x y := by
          rw [Subtype.dist_eq, Subtype.dist_eq, Subtype.dist_eq,
            Real.dist_eq, Real.dist_eq, Real.dist_eq]
          have hxzr : (x : ℝ) ≤ (zI : ℝ) := hxz.le
          have hzyr : (zI : ℝ) ≤ (y : ℝ) := hzy.le
          have hxyr : (x : ℝ) ≤ (y : ℝ) := hxy
          rw [abs_of_nonpos (sub_nonpos.mpr hxzr),
            abs_of_nonpos (sub_nonpos.mpr hzyr),
            abs_of_nonpos (sub_nonpos.mpr hxyr)]
          ring
        calc
          dist (T x) (T y) ≤ dist (T x) (T zI) + dist (T zI) (T y) :=
            dist_triangle _ _ _
          _ ≤ s * dist x zI + s * dist zI y := add_le_add hleft hright
          _ = s * dist x y := by rw [← mul_add, hdistadd]
  intro x y
  rcases le_total x y with hxy | hyx
  · exact ordered _ x y hxy rfl
  · rw [dist_comm (T x), dist_comm x]
    exact ordered _ y x hyx rfl

/-- Surjectivity forces the absolute slope of a constant-slope interval map
to be at least one. -/
private theorem one_le_constantAbsoluteSlope_of_onto
    {T : IntervalMap} {s : ℝ}
    (honto : IsOnto T) (hslope : HasConstantAbsoluteSlope T s) :
    1 ≤ s := by
  obtain ⟨x₀, hx₀⟩ := honto leftEndpoint
  obtain ⟨x₁, hx₁⟩ := honto rightEndpoint
  have hstep := constantAbsoluteSlope_dist_le hslope x₀ x₁
  rw [hx₀, hx₁] at hstep
  have hdiam : dist x₀ x₁ ≤ 1 := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_le]
    constructor <;> linarith [x₀.property.1, x₀.property.2,
      x₁.property.1, x₁.property.2]
  have hsnonneg : 0 ≤ s := constantAbsoluteSlope_nonneg hslope
  calc
    (1 : ℝ) = dist leftEndpoint rightEndpoint := by
      simp [leftEndpoint, rightEndpoint, Subtype.dist_eq, Real.dist_eq]
    _ ≤ s * dist x₀ x₁ := hstep
    _ ≤ s * 1 := mul_le_mul_of_nonneg_left hdiam hsnonneg
    _ = s := mul_one s

/-- Reflection in the midpoint of the normalized interval. -/
private def midpointReflectionR9 : IntervalMap := fun x ↦
  ⟨1 - (x : ℝ), by
    constructor <;> linarith [x.property.1, x.property.2]⟩

@[simp] private theorem midpointReflectionR9_val (x : I) :
    (midpointReflectionR9 x : ℝ) = 1 - (x : ℝ) := rfl

/-- A surjective one-Lipschitz self-map of the unit interval is either the
identity or reflection in the midpoint. -/
private theorem eq_id_or_midpointReflection_of_onto_oneLipschitz
    {T : IntervalMap} (honto : IsOnto T)
    (hlip : ∀ x y : I, dist (T x) (T y) ≤ dist x y) :
    T = id ∨ T = midpointReflectionR9 := by
  obtain ⟨u, hu⟩ := honto leftEndpoint
  obtain ⟨v, hv⟩ := honto rightEndpoint
  have hlower : 1 ≤ dist u v := by
    have h := hlip u v
    rw [hu, hv] at h
    simpa [leftEndpoint, rightEndpoint, Subtype.dist_eq, Real.dist_eq] using h
  have hupper : dist u v ≤ 1 := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_le]
    constructor <;> linarith [u.property.1, u.property.2,
      v.property.1, v.property.2]
  have huvDist : dist u v = 1 := le_antisymm hupper hlower
  rcases le_total u v with huv | hvu
  · have huvr : (u : ℝ) ≤ (v : ℝ) := huv
    have huvDist' := huvDist
    rw [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr huvr)] at huvDist'
    have huval : (u : ℝ) = 0 := by
      linarith [u.property.1, v.property.2]
    have hvval : (v : ℝ) = 1 := by
      linarith [u.property.1, v.property.2]
    have hueq : u = leftEndpoint := by
      apply Subtype.ext
      simpa [leftEndpoint] using huval
    have hveq : v = rightEndpoint := by
      apply Subtype.ext
      simpa [rightEndpoint] using hvval
    have hTleft : T leftEndpoint = leftEndpoint := by
      simpa [hueq] using hu
    have hTright : T rightEndpoint = rightEndpoint := by
      simpa [hveq] using hv
    left
    funext z
    apply Subtype.ext
    have hleft := hlip z leftEndpoint
    have hright := hlip z rightEndpoint
    rw [hTleft, Subtype.dist_eq, Subtype.dist_eq,
      Real.dist_eq, Real.dist_eq] at hleft
    rw [hTright, Subtype.dist_eq, Subtype.dist_eq,
      Real.dist_eq, Real.dist_eq] at hright
    simp only [leftEndpoint_val, rightEndpoint_val, sub_zero,
      abs_of_nonneg (T z).property.1, abs_of_nonneg z.property.1,
      abs_of_nonpos (sub_nonpos.mpr (T z).property.2),
      abs_of_nonpos (sub_nonpos.mpr z.property.2)] at hleft hright
    change (T z : ℝ) = (z : ℝ)
    linarith
  · have hvur : (v : ℝ) ≤ (u : ℝ) := hvu
    have huvDist' := huvDist
    rw [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hvur)] at huvDist'
    have huval : (u : ℝ) = 1 := by
      linarith [v.property.1, u.property.2]
    have hvval : (v : ℝ) = 0 := by
      linarith [v.property.1, u.property.2]
    have hueq : u = rightEndpoint := by
      apply Subtype.ext
      simpa [rightEndpoint] using huval
    have hveq : v = leftEndpoint := by
      apply Subtype.ext
      simpa [leftEndpoint] using hvval
    have hTleft : T leftEndpoint = rightEndpoint := by
      simpa [hveq] using hv
    have hTright : T rightEndpoint = leftEndpoint := by
      simpa [hueq] using hu
    right
    funext z
    apply Subtype.ext
    have hleft := hlip z leftEndpoint
    have hright := hlip z rightEndpoint
    rw [hTleft, Subtype.dist_eq, Subtype.dist_eq,
      Real.dist_eq, Real.dist_eq] at hleft
    rw [hTright, Subtype.dist_eq, Subtype.dist_eq,
      Real.dist_eq, Real.dist_eq] at hright
    simp only [leftEndpoint_val, rightEndpoint_val, sub_zero,
      abs_of_nonneg (T z).property.1, abs_of_nonneg z.property.1,
      abs_of_nonpos (sub_nonpos.mpr (T z).property.2),
      abs_of_nonpos (sub_nonpos.mpr z.property.2)] at hleft hright
    change (T z : ℝ) = (midpointReflectionR9 z : ℝ)
    simp only [midpointReflectionR9_val]
    linarith

/-- Hence an onto constant-absolute-slope map of unit slope has the exact
identity/reflection classification. -/
private theorem eq_id_or_midpointReflection_of_onto_unitSlope
    {T : IntervalMap} (honto : IsOnto T)
    (hslope : HasConstantAbsoluteSlope T 1) :
    T = id ∨ T = midpointReflectionR9 := by
  apply eq_id_or_midpointReflection_of_onto_oneLipschitz honto
  intro x y
  simpa using constantAbsoluteSlope_dist_le hslope x y

/-- If the first of two commuting continuous interval maps is an onto
unit-slope map, then the pair has a common fixed point.  In the identity
case take any fixed point of the second map; in the reflection case
commutation fixes the unique midpoint fixed by the reflection. -/
private theorem hasCommonFixedPoint_of_onto_unitSlope_left
    {P Q : IntervalMap}
    (hPonto : IsOnto P) (hcomm : Function.Commute P Q)
    (hQcont : Continuous Q)
    (hPslope : HasConstantAbsoluteSlope P 1) :
    HasCommonFixedPoint P Q := by
  rcases eq_id_or_midpointReflection_of_onto_unitSlope hPonto hPslope with
    hPid | hPref
  · obtain ⟨x, hx⟩ := IntervalMap.exists_fixedPoint hQcont
    refine ⟨x, ?_, hx⟩
    change P x = x
    rw [hPid]
    rfl
  · let m : I := ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩
    have hPm : P m = m := by
      rw [hPref]
      apply Subtype.ext
      change 1 - (m : ℝ) = (m : ℝ)
      norm_num [m]
    have hcommAt := hcomm m
    rw [hPm] at hcommAt
    have hQmval : (Q m : ℝ) = (1 : ℝ) / 2 := by
      have hval := congrArg Subtype.val hcommAt
      rw [hPref] at hval
      simp only [midpointReflectionR9_val] at hval
      linarith
    have hQm : Q m = m := by
      apply Subtype.ext
      simpa [m] using hQmval
    exact ⟨m, hPm, hQm⟩

/-- Onto positive constant-slope factors of a commuting counterexample both
have slope strictly greater than one. -/
theorem constantSlope_counterexample_scales_gt_one
    {P Q : IntervalMap} {C D : ℝ}
    (hPonto : IsOnto P) (hQonto : IsOnto Q)
    (hcomm : Function.Commute P Q)
    (hno : ¬HasCommonFixedPoint P Q)
    (hCpos : 0 < C) (hDpos : 0 < D)
    (hPslope : HasConstantAbsoluteSlope P C)
    (hQslope : HasConstantAbsoluteSlope Q D) :
    1 < C ∧ 1 < D := by
  have hCone : 1 ≤ C :=
    one_le_constantAbsoluteSlope_of_onto hPonto hPslope
  have hDone : 1 ≤ D :=
    one_le_constantAbsoluteSlope_of_onto hQonto hQslope
  constructor
  · by_contra hCnot
    have hCle : C ≤ 1 := le_of_not_gt hCnot
    have hCeq : C = 1 := le_antisymm hCle hCone
    have hPslopeOne : HasConstantAbsoluteSlope P 1 := by
      simpa [hCeq] using hPslope
    exact hno (hasCommonFixedPoint_of_onto_unitSlope_left
      hPonto hcomm hQslope.continuous hPslopeOne)
  · by_contra hDnot
    have hDle : D ≤ 1 := le_of_not_gt hDnot
    have hDeq : D = 1 := le_antisymm hDle hDone
    have hQslopeOne : HasConstantAbsoluteSlope Q 1 := by
      simpa [hDeq] using hQslope
    obtain ⟨x, hxQ, hxP⟩ :=
      hasCommonFixedPoint_of_onto_unitSlope_left
        hQonto hcomm.symm hPslope.continuous hQslopeOne
    exact hno ⟨x, hxP, hxQ⟩

/--
The complete output of manuscript Lemma `lem:linearize`: a normalized
minimal core of the source has a common monotone factor which is an expanding
normalized constant-slope counterexample.
-/
structure CommonConstantSlopeFactorData
    (source : PiecewiseMonotoneCounterexample) where
  normalization : MinimalCoreNormalization source
  target : NormalizedConstantSlopeCounterexample
  factor : MonotonePairFactor normalization.minimal.P
    normalization.minimal.Q target.P target.Q

/-- Every finite-piece piecewise-monotone counterexample has the stated
normalized expanding constant-slope factor. -/
theorem common_constantSlope_factor_exists
    (C₀ : PiecewiseMonotoneCounterexample) :
    Nonempty (CommonConstantSlopeFactorData C₀) := by
  obtain ⟨N⟩ := minimalCoreNormalization_exists C₀
  let C := N.minimal
  obtain ⟨D⟩ := constantSlope_quotient_exists C
  let Pbar : IntervalMap := D.eigen.factorP
  let Qbar : IntervalMap := D.eigen.factorQ
  have hno : ¬HasCommonFixedPoint Pbar Qbar :=
    D.common_factor.target_noCommonFixedPoint_of_coreMinimal C.core_minimal
  have hminimal : ∀ J : ClosedSubinterval,
      IsCommonInvariantCore Pbar Qbar J → J.carrier = Set.univ :=
    D.common_factor.target_coreMinimal C.core_minimal
  have hscales : 1 < D.eigen.scaleP ∧ 1 < D.eigen.scaleQ :=
    constantSlope_counterexample_scales_gt_one
      D.onto_factorP D.onto_factorQ D.factors_commute hno
      D.eigen.scaleP_pos D.eigen.scaleQ_pos
      D.constantSlope_factorP D.constantSlope_factorQ
  let target : NormalizedConstantSlopeCounterexample :=
    { P := Pbar
      Q := Qbar
      finitePiece_P := D.finitePiece_factorP
      finitePiece_Q := D.finitePiece_factorQ
      onto_P := D.onto_factorP
      onto_Q := D.onto_factorQ
      commute := D.factors_commute
      no_common_fixed_point := hno
      core_minimal := hminimal
      scale_P := D.eigen.scaleP
      scale_Q := D.eigen.scaleQ
      one_lt_scale_P := hscales.1
      one_lt_scale_Q := hscales.2
      constantSlope_P := D.constantSlope_factorP
      constantSlope_Q := D.constantSlope_factorQ }
  exact ⟨⟨N, target, D.common_factor⟩⟩

end CommutingIntervalSimplified
