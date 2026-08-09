import CommutingInterval.ConstantSlopeDefs
import CommutingInterval.PiecewiseLinearOrbitRaySupport
import CommutingInterval.PiecewiseLinearB9SymbolicSupport

/-!
# Geometric support for exact directed-edge coding

The principal constructions are
`PolygonalUnitSpeedRayData`, `rebuildPolygonal_unitSpeedRay`, and
`bridge_initialMarkovEdge_traversed`.

Their dependency order is:

1. finite-partition adjacency and positive affine right germs;
2. the clipped identity local chart and its scale action;
3. exact local covering and extension to a full product ray;
4. positive constant-slope composition and iteration;
5. conversion of the full ray to a real-parameter unit-speed ray; and
6. selection and traversal of the first positive Markov edge.

The ray extension comes from `PiecewiseLinearOrbitRaySupport`; the metric
itinerary vocabulary comes from `PiecewiseLinearB9SymbolicSupport`.
-/

namespace CommutingInterval

open Function Set Filter Topology

noncomputable section

/-! ## Finite partitions and positive affine germs -/

private theorem RealPartition.exists_adjacent_right_for_b9Geometry
    (partition : RealPartition) {x : ℝ}
    (hxI : x ∈ I) (hxright : x < 1) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ a ≤ x ∧ x < b := by
  classical
  let lower := partition.points.filter fun z ↦ z ≤ x
  let upper := partition.points.filter fun z ↦ x < z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, partition.zero_mem, hxI.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    simp [upper, partition.one_mem, hxright]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨a, b, ⟨ha'.1, hb'.1, ha'.2.trans_lt hb'.2, ?_⟩,
    ha'.2, hb'.2⟩
  intro z hz hzb
  by_cases hzx : z ≤ x
  · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzx⟩
    have hza : z ≤ a := by simpa using hamax z hzlower
    exact (not_lt_of_ge hza) hzb.1
  · have hxz : x < z := lt_of_not_ge hzx
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hxz⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzb.2

private theorem RealPartition.exists_adjacent_superset_for_b9Geometry
    (partition : RealPartition) {x y : ℝ}
    (hx : x ∈ I) (hy : y ∈ I) (hxy : x < y)
    (hnone : ∀ z ∈ partition.points, ¬(x < z ∧ z < y)) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ Set.Icc x y ⊆ Set.Icc a b := by
  classical
  let lower := partition.points.filter fun z ↦ z ≤ x
  let upper := partition.points.filter fun z ↦ y ≤ z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, partition.zero_mem, hx.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    simp [upper, partition.one_mem, hy.2]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hax : a ≤ x := ha'.2
  have hyb : y ≤ b := hb'.2
  have hab : a < b := hax.trans_lt (hxy.trans_le hyb)
  refine ⟨a, b, ⟨ha'.1, hb'.1, hab, ?_⟩, ?_⟩
  · intro z hz hzb
    by_cases hzx : z ≤ x
    · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzx⟩
      have hza : z ≤ a := by simpa using hamax z hzlower
      exact (not_lt_of_ge hza) hzb.1
    · by_cases hyz : y ≤ z
      · have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hyz⟩
        have hbz : b ≤ z := by simpa using hbmin z hzupper
        exact (not_lt_of_ge hbz) hzb.2
      · exact hnone z hz ⟨lt_of_not_ge hzx, lt_of_not_ge hyz⟩
  · intro z hz
    exact ⟨hax.trans hz.1, hz.2.trans hyb⟩

private def HasPositiveAffineRightGerm
    (T : IntervalMap) (p : I) (scale : ℝ) : Prop :=
  ∃ q : I, p < q ∧ ∀ x ∈ Set.Icc p q,
    (T x : ℝ) = (p : ℝ) + scale * ((x : ℝ) - (p : ℝ))

private theorem positiveAffineRightGerm_of_constantSlope
    {T : IntervalMap} {p : I} {scale : ℝ}
    (hpRight : p < rightEndpoint)
    (hfixed : IsFixedPoint T p)
    (hslope : HasConstantAbsoluteSlope T scale)
    (hstrict : ∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q)) :
    HasPositiveAffineRightGerm T p scale := by
  rcases hslope with ⟨_hcont, partition, hpartition⟩
  obtain ⟨a, b, hab, hap, hpb⟩ :=
    partition.exists_adjacent_right_for_b9Geometry p.property hpRight
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

private theorem HasPositiveAffineRightGerm.comp
    {A B : IntervalMap} {p : I} {a b : ℝ}
    (hb : 1 < b)
    (hA : HasPositiveAffineRightGerm A p a)
    (hB : HasPositiveAffineRightGerm B p b) :
    HasPositiveAffineRightGerm (A ∘ B) p (a * b) := by
  rcases hA with ⟨qA, hpA, hA⟩
  rcases hB with ⟨qB, hpB, hB⟩
  have hbpos : 0 < b := zero_lt_one.trans hb
  let bound : ℝ := (p : ℝ) + ((qA : ℝ) - (p : ℝ)) / b
  have hpbound : (p : ℝ) < bound := by
    dsimp [bound]
    exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr hpA) hbpos)
  have hpBReal : (p : ℝ) < (qB : ℝ) := hpB
  obtain ⟨qReal, hpqReal, hqReal⟩ :=
    exists_between (lt_min hpBReal hpbound)
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

/-! ## The identity local ray -/

private noncomputable def clippedIdentityRay (p : I)
    (t : RayParameter) : I :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ((p : ℝ) + (t : ℝ))

private theorem clippedIdentityRay_eq {p : I} {t : RayParameter}
    (h : (p : ℝ) + (t : ℝ) ≤ 1) :
    (clippedIdentityRay p t : ℝ) = (p : ℝ) + (t : ℝ) := by
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
    ⟨add_nonneg p.property.1 t.property, h⟩)

private noncomputable def identityLocalRayChart
    (p q : I) (hpq : p < q) : LocalRayChart p := by
  exact {
    base_lt_rightEndpoint := hpq.trans_le q.property.2
    radius := (q : ℝ) - (p : ℝ)
    radius_pos := sub_pos.mpr hpq
    toFun := clippedIdentityRay p
    continuousOn_toFun := by
      exact continuous_projIcc.comp
        (continuous_const.add continuous_subtype_val) |>.continuousOn
    map_origin := by
      apply Subtype.ext
      rw [clippedIdentityRay_eq (p := p)
        (t := rayOrigin) (by
          change (p : ℝ) + 0 ≤ 1
          simpa using p.property.2)]
      change (p : ℝ) + 0 = (p : ℝ)
      ring
    strictMonoOn_toFun := by
      intro x hx y hy hxy
      have hxone : (p : ℝ) + (x : ℝ) ≤ 1 := by
        have : (x : ℝ) < (q : ℝ) - (p : ℝ) := hx
        linarith [q.property.2]
      have hyone : (p : ℝ) + (y : ℝ) ≤ 1 := by
        have : (y : ℝ) < (q : ℝ) - (p : ℝ) := hy
        linarith [q.property.2]
      change clippedIdentityRay p x < clippedIdentityRay p y
      change (clippedIdentityRay p x : ℝ) <
        (clippedIdentityRay p y : ℝ)
      rw [clippedIdentityRay_eq hxone, clippedIdentityRay_eq hyone]
      have hxyReal : (x : ℝ) < (y : ℝ) := hxy
      linarith
    mapsTo_rightSide := by
      intro t ht
      have htone : (p : ℝ) + (t : ℝ) ≤ 1 := by
        have : (t : ℝ) < (q : ℝ) - (p : ℝ) := ht
        linarith [q.property.2]
      change (p : ℝ) ≤ (clippedIdentityRay p t : ℝ)
      rw [clippedIdentityRay_eq htone]
      exact le_add_of_nonneg_right t.property }

private theorem identityLocalRayChart_scaleAction
    {T : IntervalMap} {p q : I} {scale : ℝ}
    (hpq : p < q) (hscale : 0 < scale)
    (hgerm : ∀ x ∈ Set.Icc p q,
      (T x : ℝ) = (p : ℝ) + scale * ((x : ℝ) - (p : ℝ))) :
    LocalRayScaleAction (identityLocalRayChart p q hpq) T scale := by
  refine ⟨hscale, ?_⟩
  intro t ht hst
  have htq : (p : ℝ) + (t : ℝ) < (q : ℝ) := by
    change (t : ℝ) < (q : ℝ) - (p : ℝ) at ht
    linarith
  have hstq : (p : ℝ) + scale * (t : ℝ) < (q : ℝ) := by
    change scale * (t : ℝ) < (q : ℝ) - (p : ℝ) at hst
    linarith
  have htone : (p : ℝ) + (t : ℝ) ≤ 1 :=
    htq.le.trans q.property.2
  have hstone : (p : ℝ) + scale * (t : ℝ) ≤ 1 :=
    hstq.le.trans q.property.2
  have hchartMem : identityLocalRayChart p q hpq t ∈ Set.Icc p q := by
    constructor
    · change (p : ℝ) ≤ (clippedIdentityRay p t : ℝ)
      rw [clippedIdentityRay_eq htone]
      exact le_add_of_nonneg_right t.property
    · change (clippedIdentityRay p t : ℝ) ≤ (q : ℝ)
      rw [clippedIdentityRay_eq htone]
      exact htq.le
  apply Subtype.ext
  rw [hgerm _ hchartMem]
  change (p : ℝ) + scale *
      ((clippedIdentityRay p t : ℝ) - (p : ℝ)) =
    (clippedIdentityRay p
      (scaleRayParameter scale hscale.le t) : ℝ)
  rw [clippedIdentityRay_eq htone, clippedIdentityRay_eq hstone]
  change (p : ℝ) + scale * ((p : ℝ) + (t : ℝ) - (p : ℝ)) =
    (p : ℝ) + scale * (t : ℝ)
  ring

private theorem exact_closedIntervalCover {T : IntervalMap} {p : I}
    (hexact : IsTopologicallyExact T) :
    ∀ q : I, p < q →
      ∃ n : ℕ, iterateMap T n '' Set.Icc p q = Set.univ := by
  intro q hpq
  obtain ⟨n, hn⟩ := hexact (Set.Ioo p q) isOpen_Ioo
    (Set.nonempty_Ioo.mpr hpq)
  refine ⟨n, Set.eq_univ_of_forall ?_⟩
  intro y
  have hy : y ∈ iterateMap T n '' Set.Ioo p q := by
    rw [hn]
    exact Set.mem_univ y
  rcases hy with ⟨x, hx, hxy⟩
  exact ⟨x, ⟨hx.1.le, hx.2.le⟩, hxy⟩

/-! ## Clean constant-slope composition and iteration -/

private theorem constantAbsoluteSlope_comp_of_pos_b9Geometry
    {U T : IntervalMap} {u t : ℝ}
    (ht : 0 < t)
    (hU : HasConstantAbsoluteSlope U u)
    (hT : HasConstantAbsoluteSlope T t) :
    HasConstantAbsoluteSlope (U ∘ T) (u * t) := by
  classical
  rcases hU with ⟨hUcont, pU, hpU⟩
  rcases hT with ⟨hTcont, pT, hpT⟩
  let branchSlope : ℝ → ℝ → ℝ := fun a b ↦
    if h : pT.Adjacent a b then Classical.choose (hpT h) else 0
  let branchIntercept : ℝ → ℝ → ℝ := fun a b ↦
    if h : pT.Adjacent a b then
      Classical.choose (Classical.choose_spec (hpT h)) else 0
  have branch_spec {a b : ℝ} (h : pT.Adjacent a b) :
      |branchSlope a b| = t ∧
        ∀ x ∈ intervalCell a b,
          (T x : ℝ) = branchSlope a b * (x : ℝ) +
            branchIntercept a b := by
    dsimp [branchSlope, branchIntercept]
    simp only [dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec (hpT h))
  let root : ℝ → ℝ → ℝ → ℝ := fun a b z ↦
    (z - branchIntercept a b) / branchSlope a b
  let roots : Finset ℝ := pT.points.biUnion fun a ↦
    pT.points.biUnion fun b ↦ pU.points.image (root a b)
  let newPoints : Finset ℝ :=
    pT.points ∪ roots.filter fun x ↦ x ∈ I
  let p : RealPartition :=
    { points := newPoints
      zero_mem := by
        exact Finset.mem_union_left _ pT.zero_mem
      one_mem := by
        exact Finset.mem_union_left _ pT.one_mem
      points_subset := by
        intro x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact pT.points_subset hx
        · exact (Finset.mem_filter.mp hx).2 }
  refine ⟨hUcont.comp hTcont, p, ?_⟩
  intro x y hxy
  have hxI : x ∈ I := p.points_subset hxy.1
  have hyI : y ∈ I := p.points_subset hxy.2.1
  have hxylt : x < y := hxy.2.2.1
  let xI : I := ⟨x, hxI⟩
  let yI : I := ⟨y, hyI⟩
  have hnoInner : ∀ z ∈ pT.points, ¬(x < z ∧ z < y) := by
    intro z hz hbetween
    exact hxy.2.2.2 z (Finset.mem_union_left _ hz) hbetween
  obtain ⟨a, b, hab, hsource⟩ :=
    pT.exists_adjacent_superset_for_b9Geometry hxI hyI hxylt hnoInner
  have hbranch := branch_spec hab
  have hmne : branchSlope a b ≠ 0 := by
    intro hm
    have : |branchSlope a b| = 0 := by rw [hm, abs_zero]
    linarith [hbranch.1]
  have hxsource : xI ∈ intervalCell a b :=
    hsource ⟨le_rfl, hxylt.le⟩
  have hysource : yI ∈ intervalCell a b :=
    hsource ⟨hxylt.le, le_rfl⟩
  have hxformula := hbranch.2 xI hxsource
  have hyformula := hbranch.2 yI hysource
  have hTxy : T xI ≠ T yI := by
    intro heq
    have hval := congrArg Subtype.val heq
    rw [hxformula, hyformula] at hval
    have hmprod : branchSlope a b * (y - x) ≠ 0 :=
      mul_ne_zero hmne (sub_ne_zero.mpr hxylt.ne')
    apply hmprod
    linarith
  let lo : I := min (T xI) (T yI)
  let hi : I := max (T xI) (T yI)
  have hlohi : lo < hi := min_lt_max.mpr hTxy
  have hnoOuter : ∀ z ∈ pU.points,
      ¬((lo : ℝ) < z ∧ z < (hi : ℝ)) := by
    intro z hz hbetween
    let zI : I := ⟨z, pU.points_subset hz⟩
    have hzui : zI ∈ Set.uIcc (T xI) (T yI) := by
      change min (T xI) (T yI) ≤ zI ∧ zI ≤ max (T xI) (T yI)
      exact ⟨(show lo < zI from hbetween.1).le,
        (show zI < hi from hbetween.2).le⟩
    have hcontOn : ContinuousOn T (Set.uIcc xI yI) :=
      hTcont.continuousOn
    rcases intermediate_value_uIcc hcontOn hzui with ⟨w, hwui, hTw⟩
    have hwIcc : w ∈ Set.Icc xI yI := by
      have hxyI : xI ≤ yI := hxylt.le
      simpa only [Set.uIcc_of_le hxyI] using hwui
    have hwneX : w ≠ xI := by
      intro hw
      subst w
      have hzTx : zI = T xI := hTw.symm
      have hzExtreme : zI = lo ∨ zI = hi := by
        by_cases hle : T xI ≤ T yI
        · left
          exact hzTx.trans (min_eq_left hle).symm
        · right
          exact hzTx.trans (max_eq_left (le_of_not_ge hle)).symm
      rcases hzExtreme with hzlo | hzhi
      · exact (show lo < zI from hbetween.1).ne hzlo.symm
      · exact (show zI < hi from hbetween.2).ne hzhi
    have hwneY : w ≠ yI := by
      intro hw
      subst w
      have hzTy : zI = T yI := hTw.symm
      have hzExtreme : zI = lo ∨ zI = hi := by
        by_cases hle : T xI ≤ T yI
        · right
          exact hzTy.trans (max_eq_right hle).symm
        · left
          exact hzTy.trans (min_eq_right (le_of_not_ge hle)).symm
      rcases hzExtreme with hzlo | hzhi
      · exact (show lo < zI from hbetween.1).ne hzlo.symm
      · exact (show zI < hi from hbetween.2).ne hzhi
    have hwxy : w ∈ Set.Ioo xI yI :=
      ⟨lt_of_le_of_ne hwIcc.1 (Ne.symm hwneX),
        lt_of_le_of_ne hwIcc.2 hwneY⟩
    have hwsource : w ∈ intervalCell a b :=
      hsource ⟨hwxy.1.le, hwxy.2.le⟩
    have hwformula := hbranch.2 w hwsource
    have hwroot : (w : ℝ) = root a b z := by
      dsimp [root]
      apply (eq_div_iff hmne).2
      have hval := congrArg Subtype.val hTw
      change (T w : ℝ) = z at hval
      rw [hwformula] at hval
      linarith
    have hrootMem : root a b z ∈ roots := by
      apply Finset.mem_biUnion.mpr
      refine ⟨a, hab.1, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨b, hab.2.1, ?_⟩
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hwNew : (w : ℝ) ∈ p.points := by
      change (w : ℝ) ∈ newPoints
      apply Finset.mem_union_right
      exact Finset.mem_filter.mpr
        ⟨by simpa [hwroot] using hrootMem, w.property⟩
    exact hxy.2.2.2 (w : ℝ) hwNew ⟨hwxy.1, hwxy.2⟩
  obtain ⟨c, d, hcd, hrange⟩ :=
    pU.exists_adjacent_superset_for_b9Geometry
      lo.property hi.property hlohi hnoOuter
  obtain ⟨mU, kU, hmU, hUformula⟩ := hpU hcd
  refine ⟨mU * branchSlope a b,
    mU * branchIntercept a b + kU, ?_, ?_⟩
  · rw [abs_mul, hmU, hbranch.1]
  · intro w hw
    let wI : I := ⟨w, ⟨hxI.1.trans hw.1, hw.2.trans hyI.2⟩⟩
    have hwxy : wI ∈ Set.Icc xI yI := hw
    have hwsource : wI ∈ intervalCell a b := hsource hwxy
    have hwformula := hbranch.2 wI hwsource
    have hTbetween : T wI ∈ Set.Icc lo hi := by
      by_cases hmpos : 0 < branchSlope a b
      · have hxle : T xI ≤ T wI := by
          have hxwR : (xI : ℝ) ≤ (wI : ℝ) := hwxy.1
          change (T xI : ℝ) ≤ (T wI : ℝ)
          calc
            (T xI : ℝ) = branchSlope a b * (xI : ℝ) +
                branchIntercept a b := hxformula
            _ ≤ branchSlope a b * (wI : ℝ) + branchIntercept a b := by
              have := mul_le_mul_of_nonneg_left hxwR hmpos.le
              linarith
            _ = (T wI : ℝ) := hwformula.symm
        have hwle : T wI ≤ T yI := by
          have hwyR : (wI : ℝ) ≤ (yI : ℝ) := hwxy.2
          change (T wI : ℝ) ≤ (T yI : ℝ)
          calc
            (T wI : ℝ) = branchSlope a b * (wI : ℝ) +
                branchIntercept a b := hwformula
            _ ≤ branchSlope a b * (yI : ℝ) + branchIntercept a b := by
              have := mul_le_mul_of_nonneg_left hwyR hmpos.le
              linarith
            _ = (T yI : ℝ) := hyformula.symm
        have hxyImage : T xI ≤ T yI := hxle.trans hwle
        simpa [lo, hi, min_eq_left hxyImage,
          max_eq_right hxyImage] using ⟨hxle, hwle⟩
      · have hmneg : branchSlope a b < 0 :=
          lt_of_le_of_ne (le_of_not_gt hmpos) hmne
        have hyle : T yI ≤ T wI := by
          have hwyR : (wI : ℝ) ≤ (yI : ℝ) := hwxy.2
          change (T yI : ℝ) ≤ (T wI : ℝ)
          calc
            (T yI : ℝ) = branchSlope a b * (yI : ℝ) +
                branchIntercept a b := hyformula
            _ ≤ branchSlope a b * (wI : ℝ) + branchIntercept a b := by
              have := mul_le_mul_of_nonpos_left hwyR hmneg.le
              linarith
            _ = (T wI : ℝ) := hwformula.symm
        have hwle : T wI ≤ T xI := by
          have hxwR : (xI : ℝ) ≤ (wI : ℝ) := hwxy.1
          change (T wI : ℝ) ≤ (T xI : ℝ)
          calc
            (T wI : ℝ) = branchSlope a b * (wI : ℝ) +
                branchIntercept a b := hwformula
            _ ≤ branchSlope a b * (xI : ℝ) + branchIntercept a b := by
              have := mul_le_mul_of_nonpos_left hxwR hmneg.le
              linarith
            _ = (T xI : ℝ) := hxformula.symm
        have hyxImage : T yI ≤ T xI := hyle.trans hwle
        simpa [lo, hi, min_eq_right hyxImage,
          max_eq_left hyxImage] using ⟨hyle, hwle⟩
    have hTrange : T wI ∈ intervalCell c d := hrange hTbetween
    change (U (T wI) : ℝ) =
      (mU * branchSlope a b) * (wI : ℝ) +
        (mU * branchIntercept a b + kU)
    rw [hUformula (T wI) hTrange, hwformula]
    ring

private theorem constantAbsoluteSlope_positiveIterate_b9Geometry
    {T : IntervalMap} {scale : ℝ} {n : ℕ}
    (hscale : 0 < scale) (hn : 0 < n)
    (hslope : HasConstantAbsoluteSlope T scale) :
    HasConstantAbsoluteSlope (iterateMap T n) (scale ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction k with
  | zero => simpa [iterateMap] using hslope
  | succ k ih =>
      have ih' : HasConstantAbsoluteSlope (iterateMap T (Nat.succ k))
          (scale ^ Nat.succ k) := ih (Nat.succ_pos k)
      have hinnerPos : 0 < scale ^ (k + 1) := pow_pos hscale _
      have hcomp := constantAbsoluteSlope_comp_of_pos_b9Geometry
        hinnerPos hslope ih'
      have hmap : iterateMap T (Nat.succ (Nat.succ k)) =
          T ∘ iterateMap T (Nat.succ k) := by
        funext x
        exact Function.iterate_succ_apply' T (Nat.succ k) x
      rw [hmap]
      simpa [pow_succ, mul_comm] using hcomp

/-! ## Full-ray extension and real-parameter unit speed -/

private theorem build_exactProduct_rayChart
    {A B R : IntervalMap} {p : I} {a b : ℝ}
    (hR : R = A ∘ B)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (ha : 1 < a) (hb : 1 < b)
    (hAgerm : HasPositiveAffineRightGerm A p a)
    (hBgerm : HasPositiveAffineRightGerm B p b)
    (hexact : IsTopologicallyExact R) :
    ∃ ray : RayChart p, ∃ q : I, ∃ hpq : p < q,
      ray.ExtendsLocal (identityLocalRayChart p q hpq) ∧
        RayScaleAction ray R (a * b) := by
  have hs : 1 < a * b := one_lt_mul ha.le hb
  have hRcont : Continuous R := by
    rw [hR]
    exact hAslope.1.comp hBslope.1
  have hRfixed : IsFixedPoint R p := by
    rcases hAgerm with ⟨qA, hpA, hA⟩
    rcases hBgerm with ⟨qB, hpB, hB⟩
    have hAp : A p = p := by
      apply Subtype.ext
      rw [hA p ⟨le_rfl, hpA.le⟩]
      ring
    have hBp : B p = p := by
      apply Subtype.ext
      rw [hB p ⟨le_rfl, hpB.le⟩]
      ring
    rw [hR]
    change A (B p) = p
    rw [hBp, hAp]
  have hRgermR : HasPositiveAffineRightGerm R p (a * b) := by
    rw [hR]
    exact HasPositiveAffineRightGerm.comp hb hAgerm hBgerm
  rcases hRgermR with ⟨q, hpq, hRgerm⟩
  let iota : LocalRayChart p := identityLocalRayChart p q hpq
  have hlocal : LocalRayScaleAction iota R (a * b) := by
    rw [show iota = identityLocalRayChart p q hpq by rfl]
    exact identityLocalRayChart_scaleAction hpq (zero_lt_one.trans hs) hRgerm
  have hRstrict : ∃ r : I, p < r ∧ StrictMonoOn R (Set.Icc p r) := by
    refine ⟨q, hpq, ?_⟩
    intro x hx y hy hxy
    have hxyReal : (x : ℝ) < (y : ℝ) := hxy
    have hRx := hRgerm x hx
    have hRy := hRgerm y hy
    change (R x : ℝ) < (R y : ℝ)
    rw [hRx, hRy]
    nlinarith [mul_pos (sub_pos.mpr hs) (sub_pos.mpr hxyReal)]
  obtain ⟨ray, hExtends, hAction⟩ :=
    extend_local_germ_to_fullRay iota (a * b) hRcont hRfixed hRstrict hs
      hlocal (exact_closedIntervalCover hexact)
  exact ⟨ray, q, hpq, hExtends, hAction⟩

private theorem positiveGerm_to_fullRayGerm
    {ray : RayChart p} {q : I} {hpq : p < q}
    {T : IntervalMap} {scale : ℝ}
    (hExtends : ray.ExtendsLocal (identityLocalRayChart p q hpq))
    (hscale : 0 < scale)
    (hTgerm : HasPositiveAffineRightGerm T p scale) :
    HasLocalScaleGerm ray T scale := by
  rcases hExtends with ⟨radius, hradius, hradius_le, hagree⟩
  rcases hTgerm with ⟨qT, hpqT, hT⟩
  let radius' : ℝ := min radius ((qT : ℝ) - (p : ℝ)) / 2
  have hradius' : 0 < radius' := by
    dsimp [radius']
    exact half_pos (lt_min hradius (sub_pos.mpr hpqT))
  have hradius'_radius : radius' < radius := by
    have hmin := min_le_left radius ((qT : ℝ) - (p : ℝ))
    dsimp [radius'] at hradius' ⊢
    linarith
  have hradius'_qT : radius' < (qT : ℝ) - (p : ℝ) := by
    have hmin := min_le_right radius ((qT : ℝ) - (p : ℝ))
    dsimp [radius'] at hradius' ⊢
    linarith
  refine ⟨hscale, radius', hradius', ?_⟩
  intro t ht hst
  have htExt : t ∈ rayInitialSegment radius :=
    ht.trans hradius'_radius
  have hstExt : scaleRayParameter scale hscale.le t ∈ rayInitialSegment radius :=
    hst.trans hradius'_radius
  have htIota : t ∈ rayInitialSegment
      (identityLocalRayChart p q hpq).radius :=
    htExt.trans_le hradius_le
  have hstIota : scaleRayParameter scale hscale.le t ∈ rayInitialSegment
      (identityLocalRayChart p q hpq).radius :=
    hstExt.trans_le hradius_le
  have htqT : (p : ℝ) + (t : ℝ) < (qT : ℝ) := by
    linarith [ht.trans hradius'_qT]
  have hstqT : (p : ℝ) + scale * (t : ℝ) < (qT : ℝ) := by
    change scale * (t : ℝ) < radius' at hst
    linarith [hst.trans hradius'_qT]
  have htone : (p : ℝ) + (t : ℝ) ≤ 1 :=
    htqT.le.trans qT.property.2
  have hstone : (p : ℝ) + scale * (t : ℝ) ≤ 1 :=
    hstqT.le.trans qT.property.2
  have hrayT : ray t = identityLocalRayChart p q hpq t := hagree htExt
  have hrayST : ray (scaleRayParameter scale hscale.le t) =
      identityLocalRayChart p q hpq (scaleRayParameter scale hscale.le t) :=
    hagree hstExt
  have hrayTReal : (ray t : ℝ) = (p : ℝ) + (t : ℝ) := by
    rw [hrayT]
    exact clippedIdentityRay_eq htone
  have hraySTReal : (ray (scaleRayParameter scale hscale.le t) : ℝ) =
      (p : ℝ) + scale * (t : ℝ) := by
    rw [hrayST]
    exact clippedIdentityRay_eq hstone
  have hrayTmem : ray t ∈ Set.Icc p qT := by
    constructor
    · change (p : ℝ) ≤ (ray t : ℝ)
      rw [hrayTReal]
      exact le_add_of_nonneg_right t.property
    · change (ray t : ℝ) ≤ (qT : ℝ)
      rw [hrayTReal]
      exact htqT.le
  apply Subtype.ext
  rw [hT _ hrayTmem]
  rw [hrayTReal, hraySTReal]
  ring

private noncomputable def fullRayToReal {p : I}
    (ray : RayChart p) (t : ℝ) : I :=
  ray ⟨max 0 t, le_max_left 0 t⟩

private theorem fullRayToReal_eq {p : I} (ray : RayChart p)
    {t : ℝ} (ht : 0 ≤ t) :
    fullRayToReal ray t = ray ⟨t, ht⟩ := by
  apply congrArg ray
  apply Subtype.ext
  exact max_eq_right ht

private theorem build_exactProduct_fullActions
    {A B R : IntervalMap} {p : I} {a b : ℝ}
    (hR : R = A ∘ B) (hcomm : Commute A B)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (ha : 1 < a) (hb : 1 < b)
    (hAgerm : HasPositiveAffineRightGerm A p a)
    (hBgerm : HasPositiveAffineRightGerm B p b)
    (hexact : IsTopologicallyExact R) :
    ∃ ray : RayChart p, ∃ q : I, ∃ hpq : p < q,
      ray.ExtendsLocal (identityLocalRayChart p q hpq) ∧
      RayScaleAction ray R (a * b) ∧
      RayScaleAction ray A a ∧ RayScaleAction ray B b := by
  obtain ⟨ray, q, hpq, hExtends, hRaction⟩ :=
    build_exactProduct_rayChart hR hAslope hBslope ha hb hAgerm hBgerm hexact
  have hs : 1 < a * b := one_lt_mul ha.le hb
  have hRcont : Continuous R := by
    rw [hR]
    exact hAslope.1.comp hBslope.1
  have hAR : Commute A R := by
    intro x
    rw [hR]
    change A (A (B x)) = A (B (A x))
    exact congrArg A (hcomm x)
  have hBR : Commute B R := by
    intro x
    rw [hR]
    change B (A (B x)) = A (B (B x))
    exact (hcomm (B x)).symm
  have hAgermRay : HasLocalScaleGerm ray A a :=
    positiveGerm_to_fullRayGerm hExtends (zero_lt_one.trans ha) hAgerm
  have hBgermRay : HasLocalScaleGerm ray B b :=
    positiveGerm_to_fullRayGerm hExtends (zero_lt_one.trans hb) hBgerm
  have hAaction := localScaleGerm_extends_to_fullRay ray hRcont hAslope.1
    hAR hs hRaction hAgermRay
  have hBaction := localScaleGerm_extends_to_fullRay ray hRcont hBslope.1
    hBR hs hRaction hBgermRay
  exact ⟨ray, q, hpq, hExtends, hRaction, hAaction, hBaction⟩

private theorem rescaled_constantSlope_unitSpeed
    {T : IntervalMap} {path : ℝ → I} {scale base left right : ℝ}
    (hscale : 0 < scale) (hlr : left < right)
    (hslope : HasConstantAbsoluteSlope T scale)
    (hinput : ∀ t ∈ Set.Icc left right,
      base + t / scale ∈ I)
    (hpath : ∀ t ∈ Set.Icc left right,
      ∀ htI : base + t / scale ∈ I,
      (path t : ℝ) =
        (T ⟨base + t / scale, htI⟩ : ℝ)) :
    HasFiniteUnitSpeedPiecesOn path left right := by
  classical
  rcases hslope with ⟨_hcont, partition, hpartition⟩
  let parameterVertex : ℝ → ℝ := fun z ↦ scale * (z - base)
  let scaledVertices : Finset ℝ := partition.points.image parameterVertex
  let K : Finset ℝ :=
    insert left (insert right
      (scaledVertices.filter fun z ↦ z ∈ Set.Icc left right))
  have hleftK : left ∈ K := by simp [K]
  have hrightK : right ∈ K := by simp [K]
  have hKsubset : ∀ x ∈ K, x ∈ Set.Icc left right := by
    intro x hx
    simp only [K, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_rfl, hlr.le⟩
    · exact ⟨hlr.le, le_rfl⟩
    · exact (Finset.mem_filter.mp hx).2
  refine ⟨K, hleftK, hrightK, hKsubset, ?_⟩
  intro x y hxy
  have hxRange := hKsubset x hxy.1
  have hyRange := hKsubset y hxy.2.1
  have hinputx := hinput x hxRange
  have hinputy := hinput y hyRange
  let xI : I := ⟨base + x / scale, hinputx⟩
  let yI : I := ⟨base + y / scale, hinputy⟩
  have hxyI : xI < yI := by
    change base + x / scale < base + y / scale
    have := div_lt_div_of_pos_right hxy.2.2.1 hscale
    linarith
  obtain ⟨c, d, hcd, hcx, hxd⟩ :=
    partition.exists_adjacent_right_for_b9Geometry xI.property
      ((show (xI : ℝ) < (yI : ℝ) from hxyI).trans_le yI.property.2)
  have hyd : (yI : ℝ) ≤ d := by
    apply le_of_not_gt
    intro hdy
    let z : ℝ := parameterVertex d
    have hxz : x < z := by
      dsimp [z, parameterVertex]
      have hxdiv : x / scale < d - base := by linarith [hxd]
      have hxmul := (div_lt_iff₀ hscale).1 hxdiv
      nlinarith
    have hzy : z < y := by
      dsimp [z, parameterVertex]
      change d < base + y / scale at hdy
      have := (lt_div_iff₀ hscale).1
        (by linarith : d - base < y / scale)
      nlinarith
    have hzScaled : z ∈ scaledVertices := by
      exact Finset.mem_image.mpr ⟨d, hcd.2.1, rfl⟩
    have hzRange : z ∈ Set.Icc left right :=
      ⟨hxRange.1.trans hxz.le, hzy.le.trans hyRange.2⟩
    have hzK : z ∈ K := by
      simp only [K, Finset.mem_insert]
      exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hzScaled, hzRange⟩))
    exact hxy.2.2.2 z hzK ⟨hxz, hzy⟩
  obtain ⟨m, k, hm, hformula⟩ := hpartition hcd
  refine ⟨m / scale, m * base + k, ?_, ?_⟩
  · rw [abs_div, hm, abs_of_pos hscale, div_self hscale.ne']
  · intro t ht
    have htRange : t ∈ Set.Icc left right :=
      ⟨hxRange.1.trans ht.1, ht.2.trans hyRange.2⟩
    have htInput := hinput t htRange
    let tI : I := ⟨base + t / scale, htInput⟩
    have hxtI : xI ≤ tI := by
      change base + x / scale ≤ base + t / scale
      have := div_le_div_of_nonneg_right ht.1 hscale.le
      linarith
    have htIy : tI ≤ yI := by
      change base + t / scale ≤ base + y / scale
      have := div_le_div_of_nonneg_right ht.2 hscale.le
      linarith
    have htCell : tI ∈ intervalCell c d := by
      constructor
      · exact hcx.trans (show (xI : ℝ) ≤ (tI : ℝ) from hxtI)
      · exact (show (tI : ℝ) ≤ (yI : ℝ) from htIy).trans hyd
    rw [hpath t htRange htInput, hformula tI htCell]
    change m * (base + t / scale) + k =
      (m / scale) * t + (m * base + k)
    field_simp [hscale.ne']
    ring

private theorem rayScaleAction_iterate_for_b9Geometry
    {p : I} (ray : RayChart p) {T : IntervalMap} {scale : ℝ}
    (hT : RayScaleAction ray T scale) (n : ℕ) (t : RayParameter) :
    iterateMap T n (ray t) =
      ray (scaleRayParameter (scale ^ n)
        (pow_nonneg hT.scale_pos.le n) t) := by
  induction n with
  | zero =>
      change ray t = ray (scaleRayParameter 1 (by positivity) t)
      have ht : scaleRayParameter 1 (by positivity) t = t := by
        apply Subtype.ext
        change 1 * (t : ℝ) = (t : ℝ)
        ring
      rw [ht]
  | succ n ih =>
      rw [iterateMap, Function.iterate_succ_apply']
      change T^[n] (ray t) = _ at ih
      rw [ih, hT.equivariant]
      apply congrArg ray
      apply Subtype.ext
      change scale * (scale ^ n * (t : ℝ)) =
        scale ^ (n + 1) * (t : ℝ)
      rw [pow_succ]
      ring

private theorem fullRay_locallyUnitSpeed
    {T : IntervalMap} {p q : I} {hpq : p < q} {scale : ℝ}
    (ray : RayChart p)
    (hExtends : ray.ExtendsLocal (identityLocalRayChart p q hpq))
    (hscale : 1 < scale)
    (hTaction : RayScaleAction ray T scale)
    (hTslope : HasConstantAbsoluteSlope T scale) :
    IsLocallyUnitSpeedRay (fullRayToReal ray) := by
  have hcontinuousLift : Continuous
      (fun t : ℝ ↦ (⟨max 0 t, le_max_left 0 t⟩ : RayParameter)) :=
    (continuous_const.max continuous_id).subtype_mk _
  constructor
  · exact ray.continuous_toFun.comp hcontinuousLift
  · intro left right hleft hlr
    rcases hExtends with ⟨radius, hradius, hradius_le, hagree⟩
    let M : ℝ := right / radius
    obtain ⟨k, hk⟩ :=
      (tendsto_pow_atTop_atTop_of_one_lt hscale).eventually_gt_atTop M |>.exists
    let n : ℕ := k + 1
    have hn : 0 < n := Nat.succ_pos k
    have hscalePos : 0 < scale := zero_lt_one.trans hscale
    have hpowpos : 0 < scale ^ n := pow_pos hscalePos n
    have hkcover : right < radius * scale ^ k := by
      have hcross := (div_lt_iff₀ hradius).1 hk
      simpa [M, mul_comm] using hcross
    have hncover : right < radius * scale ^ n := by
      have hpowle : scale ^ k ≤ scale ^ n := by
        exact pow_le_pow_right₀ hscale.le (Nat.le_succ k)
      exact hkcover.trans_le
        (mul_le_mul_of_nonneg_left hpowle hradius.le)
    have hiterSlope :
        HasConstantAbsoluteSlope (iterateMap T n) (scale ^ n) :=
      constantAbsoluteSlope_positiveIterate_b9Geometry hscalePos hn hTslope
    have hinput : ∀ t ∈ Set.Icc left right,
        (p : ℝ) + t / scale ^ n ∈ I := by
      intro t ht
      constructor
      · exact add_nonneg p.property.1
          (div_nonneg (hleft.trans ht.1) hpowpos.le)
      · have htRadius : t / scale ^ n < radius := by
          apply (div_lt_iff₀ hpowpos).2
          exact ht.2.trans_lt hncover
        have htIota : t / scale ^ n < (q : ℝ) - (p : ℝ) :=
          htRadius.trans_le hradius_le
        linarith [q.property.2]
    have hpath : ∀ t ∈ Set.Icc left right,
        ∀ htI : (p : ℝ) + t / scale ^ n ∈ I,
        (fullRayToReal ray t : ℝ) =
          (iterateMap T n
            ⟨(p : ℝ) + t / scale ^ n, htI⟩ : ℝ) := by
      intro t ht htI
      have ht0 : 0 ≤ t := hleft.trans ht.1
      let tRay : RayParameter := ⟨t, ht0⟩
      let uRay : RayParameter :=
        ⟨t / scale ^ n, div_nonneg ht0 hpowpos.le⟩
      have huRadius : (uRay : ℝ) < radius := by
        change t / scale ^ n < radius
        apply (div_lt_iff₀ hpowpos).2
        exact ht.2.trans_lt hncover
      have huIota : (uRay : ℝ) <
          (identityLocalRayChart p q hpq).radius :=
        huRadius.trans_le hradius_le
      have huOne : (p : ℝ) + (uRay : ℝ) ≤ 1 := by
        change (p : ℝ) + t / scale ^ n ≤ 1
        exact htI.2
      have hrayU : ray uRay =
          ⟨(p : ℝ) + t / scale ^ n, htI⟩ := by
        apply Subtype.ext
        rw [hagree huRadius]
        change (clippedIdentityRay p uRay : ℝ) = _
        rw [clippedIdentityRay_eq huOne]
      have hscaled : scaleRayParameter (scale ^ n)
          (pow_nonneg hTaction.scale_pos.le n) uRay = tRay := by
        apply Subtype.ext
        change scale ^ n * (t / scale ^ n) = t
        calc
          scale ^ n * (t / scale ^ n) =
              scale ^ n * t / scale ^ n := by ring
          _ = t := mul_div_cancel_left₀ t hpowpos.ne'
      have hiterate :=
        rayScaleAction_iterate_for_b9Geometry ray hTaction n uRay
      rw [hscaled] at hiterate
      calc
        (fullRayToReal ray t : ℝ) = (ray tRay : ℝ) := by
          exact congrArg Subtype.val (fullRayToReal_eq ray ht0)
        _ = (iterateMap T n (ray uRay) : ℝ) :=
          congrArg Subtype.val hiterate.symm
        _ = (iterateMap T n
            ⟨(p : ℝ) + t / scale ^ n, htI⟩ : ℝ) := by
          rw [hrayU]
    exact rescaled_constantSlope_unitSpeed hpowpos hlr hiterSlope
      hinput hpath

/-! ## Frozen public G2/G3 support boundary -/

/-- The common rebuilt ray together with the exact properties consumed by
the directed-edge substitution construction. -/
structure PolygonalUnitSpeedRayData
    (A B R : IntervalMap) (p : I) (a b : ℝ) where
  ray : ℝ → I
  ray_unitSpeed : IsLocallyUnitSpeedRay ray
  ray_onto : IsOntoNonnegativeRay ray
  returnA : DilationReturnsOnRay ray a A
  returnB : DilationReturnsOnRay ray b B
  initial_linear : ∃ radius : ℝ, 0 < radius ∧
    ∀ t : ℝ, 0 ≤ t → t ≤ radius →
      (ray t : ℝ) = (p : ℝ) + t

theorem rebuildPolygonal_unitSpeedRay
    {A B R : IntervalMap} {p : I} {a b : ℝ}
    (hp : p < rightEndpoint)
    (hcomm : Commute A B) (hR : R = A ∘ B)
    (hAp : IsFixedPoint A p) (hBp : IsFixedPoint B p)
    (hRexact : IsTopologicallyExact R)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (hAstrict : ∃ q : I, p < q ∧ StrictMonoOn A (Set.Icc p q))
    (hBstrict : ∃ q : I, p < q ∧ StrictMonoOn B (Set.Icc p q))
    (ha : 1 < a) (hb : 1 < b) :
    Nonempty (PolygonalUnitSpeedRayData A B R p a b) := by
  have hAgerm : HasPositiveAffineRightGerm A p a :=
    positiveAffineRightGerm_of_constantSlope hp hAp hAslope hAstrict
  have hBgerm : HasPositiveAffineRightGerm B p b :=
    positiveAffineRightGerm_of_constantSlope hp hBp hBslope hBstrict
  obtain ⟨rayChart, q, hpq, hExtends, hRaction, hAaction, hBaction⟩ :=
    build_exactProduct_fullActions hR hcomm hAslope hBslope ha hb
      hAgerm hBgerm hRexact
  have hRslope : HasConstantAbsoluteSlope R (a * b) := by
    rw [hR]
    exact constantAbsoluteSlope_comp_of_pos_b9Geometry
      (zero_lt_one.trans hb) hAslope hBslope
  have hs : 1 < a * b := one_lt_mul ha.le hb
  let ray : ℝ → I := fullRayToReal rayChart
  have hrayUnit : IsLocallyUnitSpeedRay ray :=
    fullRay_locallyUnitSpeed rayChart hExtends hs hRaction hRslope
  have hrayOnto : IsOntoNonnegativeRay ray := by
    intro y
    obtain ⟨t, ht⟩ := rayChart.surjective_toFun y
    refine ⟨(t : ℝ), t.property, ?_⟩
    change fullRayToReal rayChart (t : ℝ) = y
    rw [fullRayToReal_eq rayChart t.property, ht]
  have hreturnA : DilationReturnsOnRay ray a A := by
    intro t ht
    have hat : 0 ≤ a * t :=
      mul_nonneg (zero_lt_one.trans ha).le ht
    let tRay : RayParameter := ⟨t, ht⟩
    have hscaled : scaleRayParameter a hAaction.scale_pos.le tRay =
        ⟨a * t, hat⟩ := by
      apply Subtype.ext
      rfl
    change fullRayToReal rayChart (a * t) =
      A (fullRayToReal rayChart t)
    rw [fullRayToReal_eq rayChart hat, fullRayToReal_eq rayChart ht]
    change rayChart ⟨a * t, hat⟩ = A (rayChart tRay)
    rw [← hscaled]
    exact (hAaction.equivariant tRay).symm
  have hreturnB : DilationReturnsOnRay ray b B := by
    intro t ht
    have hbt : 0 ≤ b * t :=
      mul_nonneg (zero_lt_one.trans hb).le ht
    let tRay : RayParameter := ⟨t, ht⟩
    have hscaled : scaleRayParameter b hBaction.scale_pos.le tRay =
        ⟨b * t, hbt⟩ := by
      apply Subtype.ext
      rfl
    change fullRayToReal rayChart (b * t) =
      B (fullRayToReal rayChart t)
    rw [fullRayToReal_eq rayChart hbt, fullRayToReal_eq rayChart ht]
    change rayChart ⟨b * t, hbt⟩ = B (rayChart tRay)
    rw [← hscaled]
    exact (hBaction.equivariant tRay).symm
  rcases hExtends with ⟨radius, hradius, hradius_le, hagree⟩
  let initialRadius : ℝ := radius / 2
  have hinitialRadius : 0 < initialRadius := half_pos hradius
  have hinitial_lt : initialRadius < radius := by
    dsimp [initialRadius]
    linarith
  have hinitial : ∀ t : ℝ, 0 ≤ t → t ≤ initialRadius →
      (ray t : ℝ) = (p : ℝ) + t := by
    intro t ht htRadius
    let tRay : RayParameter := ⟨t, ht⟩
    have htExt : (tRay : ℝ) < radius := htRadius.trans_lt hinitial_lt
    have htIota : (tRay : ℝ) <
        (identityLocalRayChart p q hpq).radius :=
      htExt.trans_le hradius_le
    have htOne : (p : ℝ) + (tRay : ℝ) ≤ 1 := by
      change t < (q : ℝ) - (p : ℝ) at htIota
      linarith [q.property.2]
    change (fullRayToReal rayChart t : ℝ) = (p : ℝ) + t
    rw [fullRayToReal_eq rayChart ht, hagree htExt]
    exact clippedIdentityRay_eq htOne
  exact ⟨{
    ray := ray
    ray_unitSpeed := hrayUnit
    ray_onto := hrayOnto
    returnA := hreturnA
    returnB := hreturnB
    initial_linear := ⟨initialRadius, hinitialRadius, hinitial⟩ }⟩

theorem bridge_initialMarkovEdge_traversed
    {A B R : IntervalMap} {p : I} {a b : ℝ} {K : Finset I}
    (data : PolygonalUnitSpeedRayData A B R p a b)
    (hp : p ∈ K) (hpRight : p < rightEndpoint)
    (hK : IsCommonMarkovSet A B K)
    (ha : 1 < a) :
    ∃ edge : DirectedMarkovEdge K,
      edge.forward = true ∧ edge.source = p ∧
        TraversesDirectedEdge data.ray 0 edge := by
  classical
  let upper : Finset I := K.filter fun z ↦ p < z
  have hupper : upper.Nonempty := by
    refine ⟨rightEndpoint, ?_⟩
    exact Finset.mem_filter.mpr ⟨hK.2.1, hpRight⟩
  obtain ⟨q, hq, hqmin⟩ := upper.exists_min_image id hupper
  have hq' := Finset.mem_filter.mp hq
  have hadj : FinsetAdjacent K p q := by
    refine ⟨hp, hq'.1, hq'.2, ?_⟩
    intro z hz hzbetween
    have hzupper : z ∈ upper :=
      Finset.mem_filter.mpr ⟨hz, hzbetween.1⟩
    have hqz : q ≤ z := by simpa using hqmin z hzupper
    exact (not_lt_of_ge hqz) hzbetween.2
  let edge : DirectedMarkovEdge K :=
    ⟨((⟨p, hp⟩, ⟨q, hq'.1⟩), true), hadj⟩
  refine ⟨edge, rfl, rfl, ?_⟩
  rcases data.initial_linear with ⟨radius, hradius, hinitial⟩
  have hapos : 0 < a := zero_lt_one.trans ha
  let delta : ℝ := min (radius / a)
      (((q : ℝ) - (p : ℝ)) / a) / 2
  have hpq : p < q := hadj.2.2.1
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact half_pos (lt_min (div_pos hradius hapos)
      (div_pos (sub_pos.mpr hpq) hapos))
  have hdelta_radius : delta ≤ radius := by
    have hmin := min_le_left (radius / a)
      (((q : ℝ) - (p : ℝ)) / a)
    dsimp [delta] at hdelta ⊢
    have hra : 0 < radius / a := div_pos hradius hapos
    nlinarith [hmin, div_lt_self hradius ha]
  have ha_delta_radius : a * delta ≤ radius := by
    have hmin := min_le_left (radius / a)
      (((q : ℝ) - (p : ℝ)) / a)
    dsimp [delta]
    have hra : 0 < radius / a := div_pos hradius hapos
    nlinarith [hmin, (div_mul_cancel₀ radius hapos.ne')]
  have ha_delta_edge : a * delta ≤ (q : ℝ) - (p : ℝ) := by
    have hmin := min_le_right (radius / a)
      (((q : ℝ) - (p : ℝ)) / a)
    dsimp [delta]
    have hqa : 0 < ((q : ℝ) - (p : ℝ)) / a :=
      div_pos (sub_pos.mpr hpq) hapos
    nlinarith [hmin,
      (div_mul_cancel₀ ((q : ℝ) - (p : ℝ)) hapos.ne')]
  have hdelta_edge : delta ≤ (q : ℝ) - (p : ℝ) := by
    nlinarith [ha_delta_edge, mul_lt_mul_of_pos_right ha hdelta]
  have hray_zero : (data.ray 0 : ℝ) = (p : ℝ) := by
    simpa using hinitial 0 le_rfl hradius.le
  have hray_delta : (data.ray delta : ℝ) = (p : ℝ) + delta :=
    hinitial delta hdelta.le hdelta_radius
  have hray_adelta : (data.ray (a * delta) : ℝ) =
      (p : ℝ) + a * delta :=
    hinitial (a * delta) (mul_nonneg hapos.le hdelta.le) ha_delta_radius
  have hAfix : A p = p := by
    have hreturn := data.returnA 0 le_rfl
    have hrayZero : data.ray 0 = p := Subtype.ext hray_zero
    simpa [hrayZero] using hreturn.symm
  have hdelta_mem : data.ray delta ∈ Set.Icc p q := by
    constructor
    · change (p : ℝ) ≤ (data.ray delta : ℝ)
      rw [hray_delta]
      linarith
    · change (data.ray delta : ℝ) ≤ (q : ℝ)
      rw [hray_delta]
      linarith
  have hAaff : IsAffineOn A (Set.Icc p q) :=
    (hK.2.2.2.2 hadj).1.1
  rcases hAaff with ⟨m, c, hformula⟩
  have hformula_p := hformula p ⟨le_rfl, hpq.le⟩
  have hformula_delta := hformula (data.ray delta) hdelta_mem
  have hA_delta : (A (data.ray delta) : ℝ) =
      (p : ℝ) + a * delta := by
    rw [← data.returnA delta hdelta.le]
    exact hray_adelta
  have hAfixReal : (A p : ℝ) = (p : ℝ) :=
    congrArg Subtype.val hAfix
  have hm : m = a := by
    rw [hAfixReal] at hformula_p
    rw [hA_delta, hray_delta] at hformula_delta
    nlinarith
  have hA_on_edge : ∀ x ∈ Set.Icc p q,
      (A x : ℝ) = (p : ℝ) + a * ((x : ℝ) - (p : ℝ)) := by
    intro x hx
    have hxformula := hformula x hx
    rw [hm] at hxformula
    rw [hAfixReal] at hformula_p
    rw [hm] at hformula_p
    nlinarith
  intro u hu0 huLength
  have huEdge : u ≤ (q : ℝ) - (p : ℝ) := by
    simpa [edge, DirectedMarkovEdge.length, DirectedMarkovEdge.upper,
      DirectedMarkovEdge.lower] using huLength
  obtain ⟨n, hn⟩ :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).eventually_gt_atTop
      (u / delta) |>.exists
  have hpowpos : 0 < a ^ n := pow_pos hapos n
  let t : ℝ := u / a ^ n
  have ht0 : 0 ≤ t := div_nonneg hu0 hpowpos.le
  have ht_delta : t < delta := by
    dsimp [t]
    apply (div_lt_iff₀ hpowpos).2
    have hcross := (div_lt_iff₀ hdelta).1 hn
    nlinarith
  have hscaled : a ^ n * t = u := by
    dsimp [t]
    calc
      a ^ n * (u / a ^ n) = a ^ n * u / a ^ n := by ring
      _ = u := mul_div_cancel_left₀ u hpowpos.ne'
  have hray_scaled : ∀ k : ℕ, k ≤ n →
      (data.ray (a ^ k * t) : ℝ) = (p : ℝ) + a ^ k * t := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using hinitial t ht0 (ht_delta.trans_le hdelta_radius).le
    | succ k ih =>
        intro hk
        have hkn : k ≤ n := (Nat.le_succ k).trans hk
        have hpowle : a ^ k ≤ a ^ n :=
          pow_le_pow_right₀ ha.le hkn
        have hparam0 : 0 ≤ a ^ k * t :=
          mul_nonneg (pow_nonneg hapos.le k) ht0
        have hparam_le : a ^ k * t ≤ u := by
          calc
            a ^ k * t ≤ a ^ n * t :=
              mul_le_mul_of_nonneg_right hpowle ht0
            _ = u := hscaled
        have hrayk := ih hkn
        have hrayk_mem : data.ray (a ^ k * t) ∈ Set.Icc p q := by
          constructor
          · change (p : ℝ) ≤ (data.ray (a ^ k * t) : ℝ)
            rw [hrayk]
            linarith
          · change (data.ray (a ^ k * t) : ℝ) ≤ (q : ℝ)
            rw [hrayk]
            linarith
        calc
          (data.ray (a ^ (k + 1) * t) : ℝ) =
              (data.ray (a * (a ^ k * t)) : ℝ) := by
                congr 2
                rw [pow_succ]
                ring
          _ = (A (data.ray (a ^ k * t)) : ℝ) :=
            congrArg Subtype.val (data.returnA (a ^ k * t) hparam0)
          _ = (p : ℝ) + a *
              ((data.ray (a ^ k * t) : ℝ) - (p : ℝ)) :=
            hA_on_edge _ hrayk_mem
          _ = (p : ℝ) + a ^ (k + 1) * t := by
            rw [hrayk, pow_succ]
            ring
  have hfinal := hray_scaled n le_rfl
  change (data.ray (0 + u) : ℝ) = (edge.lower : ℝ) + u
  simp only [zero_add]
  simpa [edge, DirectedMarkovEdge.lower, hscaled] using hfinal

end


end CommutingInterval
