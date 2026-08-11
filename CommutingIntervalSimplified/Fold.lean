import CommutingIntervalSimplified.Extremal
import CommutingIntervalSimplified.CommonIterate

/-!
# Repelling return states and the stabilized two-scale fold

This file freezes the geometric half (F1--F8) of the manuscript's
two-scale lemma.  It is standalone: the only project import is the
simplified extremal layer, which in turn imports the simplified definitions.

The common-positive-iterate theorem is supplied by the standalone local
inverse-limit development in `CommonIterate`.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set
open scoped Topology

/-! ## Orientation normalization -/

/-- Reflection in the midpoint of the unit interval. -/
def reflectPoint (x : I) : I :=
  ⟨1 - (x : ℝ), sub_nonneg.mpr x.property.2,
    sub_le_self 1 x.property.1⟩

@[simp] theorem reflectPoint_val (x : I) :
    (reflectPoint x : ℝ) = 1 - (x : ℝ) := rfl

@[simp] theorem reflectPoint_involutive (x : I) :
    reflectPoint (reflectPoint x) = x := by
  apply Subtype.ext
  simp [reflectPoint]

/-- Conjugation of an interval map by midpoint reflection. -/
def reflectedIntervalMap (T : IntervalMap) : IntervalMap :=
  reflectPoint ∘ T ∘ reflectPoint

/-- `C'` is either `C` itself or its simultaneous reflection conjugate.
The scale magnitudes are unchanged. -/
def IsOrientationVariant
    (C C' : NormalizedConstantSlopeCounterexample) : Prop :=
  C' = C ∨
    (C'.P = reflectedIntervalMap C.P ∧
      C'.Q = reflectedIntervalMap C.Q ∧
      C'.scale_P = C.scale_P ∧ C'.scale_Q = C.scale_Q)

theorem IsOrientationVariant.refl
    (C : NormalizedConstantSlopeCounterexample) :
    IsOrientationVariant C C :=
  Or.inl rfl

private theorem reflectPoint_injective : Function.Injective reflectPoint := by
  intro x y hxy
  have h := congrArg reflectPoint hxy
  simpa using h

private theorem reflectPoint_strictAnti : StrictAnti reflectPoint := by
  intro x y hxy
  apply Subtype.coe_lt_coe.mp
  have hxy' : (x : ℝ) < (y : ℝ) := hxy
  simp only [reflectPoint_val]
  linarith

@[simp] private theorem reflectedIntervalMap_apply
    (T : IntervalMap) (x : I) :
    reflectedIntervalMap T x = reflectPoint (T (reflectPoint x)) := rfl

private theorem reflectedIntervalMap_comp (F G : IntervalMap) :
    reflectedIntervalMap (F ∘ G) =
      reflectedIntervalMap F ∘ reflectedIntervalMap G := by
  funext x
  simp [reflectedIntervalMap, Function.comp_apply]

private theorem reflectedIntervalMap_iterate
    (T : IntervalMap) (n : ℕ) :
    reflectedIntervalMap (T^[n]) = (reflectedIntervalMap T)^[n] := by
  induction n with
  | zero =>
      funext x
      simp [reflectedIntervalMap, Function.comp_apply]
  | succ n ih =>
      rw [Function.iterate_succ', Function.iterate_succ',
        reflectedIntervalMap_comp, ih]

private theorem isFixedPoint_reflectedIntervalMap
    (T : IntervalMap) (x : I) :
    IsFixedPoint (reflectedIntervalMap T) x ↔
      IsFixedPoint T (reflectPoint x) := by
  constructor
  · intro h
    have hh := congrArg reflectPoint h
    simpa [IsFixedPoint, reflectedIntervalMap, Function.comp_apply] using hh
  · intro h
    change reflectPoint (T (reflectPoint x)) = x
    rw [h]
    simp

private def reflectedClosedSubinterval
    (J : ClosedSubinterval) : ClosedSubinterval where
  left := reflectPoint J.right
  right := reflectPoint J.left
  left_le_right := reflectPoint_strictAnti.antitone J.left_le_right

private theorem mem_reflectedClosedSubinterval
    (J : ClosedSubinterval) (x : I) :
    x ∈ (reflectedClosedSubinterval J).carrier ↔
      reflectPoint x ∈ J.carrier := by
  constructor
  · intro hx
    constructor
    · have h := reflectPoint_strictAnti.antitone hx.2
      simpa [reflectedClosedSubinterval] using h
    · have h := reflectPoint_strictAnti.antitone hx.1
      simpa [reflectedClosedSubinterval] using h
  · intro hx
    constructor
    · have h := reflectPoint_strictAnti.antitone hx.2
      simpa [reflectedClosedSubinterval] using h
    · have h := reflectPoint_strictAnti.antitone hx.1
      simpa [reflectedClosedSubinterval] using h

private theorem hasConstantAbsoluteSlope_reflectPoint :
    HasConstantAbsoluteSlope reflectPoint 1 := by
  refine ⟨?_, RealPartition.trivial, ?_⟩
  · exact Continuous.subtype_mk
      (continuous_const.sub continuous_subtype_val) _
  · intro a b _hab
    refine ⟨-1, 1, by simp, ?_⟩
    intro x _hx
    change 1 - (x : ℝ) = -1 * (x : ℝ) + 1
    ring

private theorem HasConstantAbsoluteSlope.reflected
    {T : IntervalMap} {s : ℝ}
    (hT : HasConstantAbsoluteSlope T s) (hs : 0 < s) :
    HasConstantAbsoluteSlope (reflectedIntervalMap T) s := by
  have hleft : HasConstantAbsoluteSlope (reflectPoint ∘ T) (1 * s) :=
    hasConstantAbsoluteSlope_reflectPoint.comp_of_pos hs hT
  have hboth : HasConstantAbsoluteSlope
      ((reflectPoint ∘ T) ∘ reflectPoint) ((1 * s) * 1) :=
    hleft.comp_of_pos zero_lt_one hasConstantAbsoluteSlope_reflectPoint
  simpa [reflectedIntervalMap, Function.comp_assoc] using hboth

private noncomputable def reflectedCounterexample
    (C : NormalizedConstantSlopeCounterexample) :
    NormalizedConstantSlopeCounterexample where
  P := reflectedIntervalMap C.P
  Q := reflectedIntervalMap C.Q
  finitePiece_P :=
    (C.constantSlope_P.reflected
      (zero_lt_one.trans C.one_lt_scale_P)).finitePiecePL
  finitePiece_Q :=
    (C.constantSlope_Q.reflected
      (zero_lt_one.trans C.one_lt_scale_Q)).finitePiecePL
  onto_P := by
    intro y
    obtain ⟨z, hz⟩ := C.onto_P (reflectPoint y)
    refine ⟨reflectPoint z, ?_⟩
    simp [reflectedIntervalMap, Function.comp_apply, hz]
  onto_Q := by
    intro y
    obtain ⟨z, hz⟩ := C.onto_Q (reflectPoint y)
    refine ⟨reflectPoint z, ?_⟩
    simp [reflectedIntervalMap, Function.comp_apply, hz]
  commute := by
    intro x
    simpa [reflectedIntervalMap, Function.comp_apply] using
      congrArg reflectPoint (C.commute (reflectPoint x))
  no_common_fixed_point := by
    rintro ⟨y, hyP, hyQ⟩
    apply C.no_common_fixed_point
    refine ⟨reflectPoint y, ?_, ?_⟩
    · have h := congrArg reflectPoint hyP
      simpa [IsFixedPoint, reflectedIntervalMap, Function.comp_apply] using h
    · have h := congrArg reflectPoint hyQ
      simpa [IsFixedPoint, reflectedIntervalMap, Function.comp_apply] using h
  core_minimal := by
    intro J hJ
    let K := reflectedClosedSubinterval J
    have hK : IsCommonInvariantCore C.P C.Q K := by
      constructor
      · intro x hx
        apply (mem_reflectedClosedSubinterval J (C.P x)).mpr
        have hxJ := (mem_reflectedClosedSubinterval J x).mp hx
        have himage := hJ.1 hxJ
        simpa [reflectedIntervalMap, Function.comp_apply] using himage
      · intro x hx
        apply (mem_reflectedClosedSubinterval J (C.Q x)).mpr
        have hxJ := (mem_reflectedClosedSubinterval J x).mp hx
        have himage := hJ.2 hxJ
        simpa [reflectedIntervalMap, Function.comp_apply] using himage
    have hKuniv : K.carrier = Set.univ := C.core_minimal K hK
    apply Set.eq_univ_of_forall
    intro y
    have hyK : reflectPoint y ∈ K.carrier := by
      rw [hKuniv]
      exact Set.mem_univ _
    have h := (mem_reflectedClosedSubinterval J (reflectPoint y)).mp hyK
    simpa using h
  scale_P := C.scale_P
  scale_Q := C.scale_Q
  one_lt_scale_P := C.one_lt_scale_P
  one_lt_scale_Q := C.one_lt_scale_Q
  constantSlope_P := C.constantSlope_P.reflected
    (zero_lt_one.trans C.one_lt_scale_P)
  constantSlope_Q := C.constantSlope_Q.reflected
    (zero_lt_one.trans C.one_lt_scale_Q)

private theorem reflectedCounterexample_product
    (C : NormalizedConstantSlopeCounterexample) :
    (reflectedCounterexample C).product = reflectedIntervalMap C.product := by
  change reflectedIntervalMap C.P ∘ reflectedIntervalMap C.Q =
    reflectedIntervalMap (C.P ∘ C.Q)
  exact (reflectedIntervalMap_comp C.P C.Q).symm

private def fixedPointReflectionEquiv (T : IntervalMap) :
    fixedPoints (reflectedIntervalMap T) ≃ fixedPoints T where
  toFun x := ⟨reflectPoint x.1,
    (isFixedPoint_reflectedIntervalMap T x.1).mp x.2⟩
  invFun x := ⟨reflectPoint x.1,
    (isFixedPoint_reflectedIntervalMap T (reflectPoint x.1)).mpr (by
      rw [reflectPoint_involutive]
      exact x.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

private theorem fixedPoints_reflected_ncard (T : IntervalMap) :
    (fixedPoints (reflectedIntervalMap T)).ncard =
      (fixedPoints T).ncard :=
  Set.ncard_congr' (fixedPointReflectionEquiv T)

private theorem mapsOntoSubinterval_reflected_to_original
    (T : IntervalMap) (n : ℕ) (J : ClosedSubinterval)
    (honto : MapsOntoSubinterval
      (iterateMap (reflectedIntervalMap T) n) J) :
    MapsOntoSubinterval (iterateMap T n)
      (reflectedClosedSubinterval J) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply (mem_reflectedClosedSubinterval J _).mpr
    have hxJ := (mem_reflectedClosedSubinterval J x).mp hx
    have himage : iterateMap (reflectedIntervalMap T) n (reflectPoint x) ∈
        J.carrier := by
      rw [← honto]
      exact ⟨reflectPoint x, hxJ, rfl⟩
    change (reflectedIntervalMap T)^[n] (reflectPoint x) ∈ J.carrier at himage
    rw [← reflectedIntervalMap_iterate T n] at himage
    simpa [reflectedIntervalMap, Function.comp_apply] using himage
  · intro y hy
    have hryJ := (mem_reflectedClosedSubinterval J y).mp hy
    have hryImage : reflectPoint y ∈
        iterateMap (reflectedIntervalMap T) n '' J.carrier := by
      rw [honto]
      exact hryJ
    rcases hryImage with ⟨z, hz, hzy⟩
    refine ⟨reflectPoint z, ?_, ?_⟩
    · apply (mem_reflectedClosedSubinterval J _).mpr
      simpa using hz
    · change (reflectedIntervalMap T)^[n] z = reflectPoint y at hzy
      rw [← reflectedIntervalMap_iterate T n] at hzy
      have h := congrArg reflectPoint hzy
      simpa [reflectedIntervalMap, Function.comp_apply] using h

private theorem returnedPowersIrreducible_reflected
    {P Q : IntervalMap} {L : ℕ}
    (h : ReturnedPowersIrreducible P Q L) :
    ReturnedPowersIrreducible
      (reflectedIntervalMap P) (reflectedIntervalMap Q) L := by
  intro J hJ hPonto hQonto
  let K := reflectedClosedSubinterval J
  have hK : K.Nondegenerate := by
    exact reflectPoint_strictAnti hJ
  have hPK : MapsOntoSubinterval (iterateMap P L) K :=
    mapsOntoSubinterval_reflected_to_original P L J hPonto
  have hQK : MapsOntoSubinterval (iterateMap Q L) K :=
    mapsOntoSubinterval_reflected_to_original Q L J hQonto
  have hKuniv : K.carrier = Set.univ := h K hK hPK hQK
  apply Set.eq_univ_of_forall
  intro y
  have hyK : reflectPoint y ∈ K.carrier := by
    rw [hKuniv]
    exact Set.mem_univ _
  have hy := (mem_reflectedClosedSubinterval J (reflectPoint y)).mp hyK
  simpa using hy

/-! ## F1: the finite product fixed set -/

/-- A fully finite presentation of `Fix(PQ)`, together with the inverse
actions induced by `P` and `Q`. -/
structure ProductFixedSetPackage
    (C : NormalizedConstantSlopeCounterexample) (bound : ℕ) where
  points : Finset I
  mem_points : ∀ x : I, x ∈ points ↔ IsFixedPoint C.product x
  two_le_card : 2 ≤ points.card
  card_le_bound : points.card ≤ bound
  actionP : Equiv.Perm {x : I // x ∈ points}
  actionQ : Equiv.Perm {x : I // x ∈ points}
  actionP_base : ∀ x, (actionP x).1 = C.P x.1
  actionQ_base : ∀ x, (actionQ x).1 = C.Q x.1
  actionQ_actionP : ∀ x, actionQ (actionP x) = x
  actionP_actionQ : ∀ x, actionP (actionQ x) = x

/-- The product fixed set is finite, has at least two points, is bounded by
the extremal fixed count, and carries mutually inverse generator actions. -/
theorem productFixedSetPackage_exists
    (C : NormalizedConstantSlopeCounterexample) (bound : ℕ)
    (hbound : (fixedPoints C.product).ncard ≤ bound) :
    Nonempty (ProductFixedSetPackage C bound) := by
  let points : Finset I := productFixedFinset C
  have hP_maps : ∀ x : I, x ∈ points → C.P x ∈ points := by
    intro x hx
    rw [show points = productFixedFinset C from rfl,
      mem_productFixedFinset]
    have hxfix : C.P (C.Q x) = x := by
      have := (mem_productFixedFinset C x).mp
        (show x ∈ productFixedFinset C from hx)
      simpa [NormalizedConstantSlopeCounterexample.product] using this
    change C.P (C.Q (C.P x)) = C.P x
    calc
      C.P (C.Q (C.P x)) = C.P (C.P (C.Q x)) :=
        congrArg C.P (C.commute x).symm
      _ = C.P x := congrArg C.P hxfix
  have hQ_maps : ∀ x : I, x ∈ points → C.Q x ∈ points := by
    intro x hx
    rw [show points = productFixedFinset C from rfl,
      mem_productFixedFinset]
    have hxfix : C.P (C.Q x) = x := by
      have := (mem_productFixedFinset C x).mp
        (show x ∈ productFixedFinset C from hx)
      simpa [NormalizedConstantSlopeCounterexample.product] using this
    change C.P (C.Q (C.Q x)) = C.Q x
    calc
      C.P (C.Q (C.Q x)) = C.Q (C.P (C.Q x)) := C.commute (C.Q x)
      _ = C.Q x := congrArg C.Q hxfix
  let pMap : {x : I // x ∈ points} → {x : I // x ∈ points} :=
    fun x => ⟨C.P x.1, hP_maps x.1 x.2⟩
  let qMap : {x : I // x ∈ points} → {x : I // x ∈ points} :=
    fun x => ⟨C.Q x.1, hQ_maps x.1 x.2⟩
  have hq_p : ∀ x, qMap (pMap x) = x := by
    intro x
    apply Subtype.ext
    change C.Q (C.P x.1) = x.1
    calc
      C.Q (C.P x.1) = C.P (C.Q x.1) := (C.commute x.1).symm
      _ = x.1 := by
        have hxfix := (mem_productFixedFinset C x.1).mp
          (show x.1 ∈ productFixedFinset C from x.2)
        simpa [NormalizedConstantSlopeCounterexample.product] using hxfix
  have hp_q : ∀ x, pMap (qMap x) = x := by
    intro x
    apply Subtype.ext
    change C.P (C.Q x.1) = x.1
    have hxfix := (mem_productFixedFinset C x.1).mp
      (show x.1 ∈ productFixedFinset C from x.2)
    simpa [NormalizedConstantSlopeCounterexample.product] using hxfix
  let actionP : Equiv.Perm {x : I // x ∈ points} :=
    { toFun := pMap
      invFun := qMap
      left_inv := hq_p
      right_inv := hp_q }
  let actionQ : Equiv.Perm {x : I // x ∈ points} := actionP.symm
  have hpoints_pos : 0 < points.card := by
    simpa [points, productFixedCount] using productFixedCount_pos C
  have htwo : 2 ≤ points.card := by
    by_contra hnot
    have hcard : points.card = 1 := by omega
    obtain ⟨x, hpoints⟩ := Finset.card_eq_one.mp hcard
    have hx : x ∈ points := by simp [hpoints]
    have hPx_mem : C.P x ∈ points := hP_maps x hx
    have hQx_mem : C.Q x ∈ points := hQ_maps x hx
    have hPx : IsFixedPoint C.P x := by
      change C.P x = x
      simpa [hpoints] using hPx_mem
    have hQx : IsFixedPoint C.Q x := by
      change C.Q x = x
      simpa [hpoints] using hQx_mem
    apply C.no_common_fixed_point
    exact ⟨x, hPx, hQx⟩
  have hcard_bound : points.card ≤ bound := by
    calc
      points.card = (fixedPoints C.product).ncard := by
        simpa [points, productFixedFinset] using
          (Set.ncard_eq_toFinset_card (fixedPoints C.product)
            (product_fixedPoints_finite C)).symm
      _ ≤ bound := hbound
  refine ⟨{
    points := points
    mem_points := ?_
    two_le_card := htwo
    card_le_bound := hcard_bound
    actionP := actionP
    actionQ := actionQ
    actionP_base := ?_
    actionQ_base := ?_
    actionQ_actionP := ?_
    actionP_actionQ := ?_ }⟩
  · intro x
    simpa [points] using mem_productFixedFinset C x
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    exact actionP.symm_apply_apply x
  · intro x
    exact actionP.apply_symm_apply x

/-! ## F2: a consecutive fixed gap and its repelling directed side -/

/-- Consecutive elements of a finite ordered subset of `I`. -/
def ConsecutiveInFinset (X : Finset I) (p c : I) : Prop :=
  p ∈ X ∧ c ∈ X ∧ p < c ∧
    ∀ x ∈ X, ¬(p < x ∧ x < c)

/-- A map fixes the base of a directed side and acts there by a positive
dilation of the indicated magnitude. -/
def HasPositiveDilationGerm
    (T : IntervalMap) (sigma : DirectedSide) (scale : ℝ) : Prop :=
  IsFixedPoint T sigma.base ∧ 0 < scale ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ x : I,
        x ∈ sigma.direction.closedRay sigma.base →
        |(x : ℝ) - (sigma.base : ℝ)| < epsilon →
          T x ∈ sigma.direction.closedRay sigma.base ∧
            (T x : ℝ) - (sigma.base : ℝ) =
              scale * ((x : ℝ) - (sigma.base : ℝ))

/-- A map carries the germ of one directed side into another. -/
def CarriesDirectedSide
    (T : IntervalMap) (sigma tau : DirectedSide) : Prop :=
  T sigma.base = tau.base ∧
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ x : I,
        x ∈ sigma.direction.closedRay sigma.base →
        |(x : ℝ) - (sigma.base : ℝ)| < epsilon →
          T x ∈ tau.direction.closedRay tau.base

/-- The orientation-normalized consecutive gap used to launch the ray. -/
structure RepellingGapData
    (C : NormalizedConstantSlopeCounterexample) (bound : ℕ)
    (X : ProductFixedSetPackage C bound) where
  p : I
  c : I
  consecutive : ConsecutiveInFinset X.points p c
  product_moves_right :
    ∀ x : I, p < x → x < c → x < C.product x
  side : DirectedSide
  side_base : side.base = p
  side_direction : side.direction = Side.right
  product_repelling :
    HasPositiveDilationGerm C.product side (C.scale_P * C.scale_Q)

private theorem consecutiveInProductFixedFinset_exists
    {C : NormalizedConstantSlopeCounterexample} {bound : ℕ}
    (X : ProductFixedSetPackage C bound) :
    ∃ p c : I, ConsecutiveInFinset X.points p c := by
  classical
  have htwo : 2 ≤ X.points.card := X.two_le_card
  have hnonempty : X.points.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp, hpmin⟩ := X.points.exists_min_image id hnonempty
  have herase_card : 0 < (X.points.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  have herase : (X.points.erase p).Nonempty :=
    Finset.card_pos.mp herase_card
  obtain ⟨c, hcErase, hcmin⟩ :=
    (X.points.erase p).exists_min_image id herase
  have hc : c ∈ X.points := (Finset.mem_erase.mp hcErase).2
  have hpc_le : p ≤ c := by simpa using hpmin c hc
  have hcp_ne : c ≠ p := (Finset.mem_erase.mp hcErase).1
  have hpc : p < c := lt_of_le_of_ne hpc_le hcp_ne.symm
  refine ⟨p, c, hp, hc, hpc, ?_⟩
  intro x hx hbetween
  have hxErase : x ∈ X.points.erase p :=
    Finset.mem_erase.mpr ⟨ne_of_gt hbetween.1, hx⟩
  have hcx : c ≤ x := by simpa using hcmin x hxErase
  exact (not_lt_of_ge hcx) hbetween.2

private theorem consecutiveProductGap_constantSign
    {C : NormalizedConstantSlopeCounterexample} {bound : ℕ}
    {X : ProductFixedSetPackage C bound} {p c : I}
    (hgap : ConsecutiveInFinset X.points p c) :
    (∀ x : I, p < x → x < c → x < C.product x) ∨
      (∀ x : I, p < x → x < c → C.product x < x) := by
  rcases hgap with ⟨hp, hc, hpc, hconsecutive⟩
  have hcont : Continuous C.product :=
    C.finitePiece_P.continuous.comp C.finitePiece_Q.continuous
  have hnotfix (x : I) (hpx : p < x) (hxc : x < c) :
      ¬IsFixedPoint C.product x := by
    intro hxfix
    exact hconsecutive x ((X.mem_points x).mpr hxfix) ⟨hpx, hxc⟩
  let d : I → ℝ := fun z => (C.product z : ℝ) - (z : ℝ)
  have hdcont : Continuous d :=
    (continuous_subtype_val.comp hcont).sub continuous_subtype_val
  have opposite_impossible (x y : I) (hpx : p < x) (hxc : x < c)
      (hpy : p < y) (hyc : y < c) (hneg : C.product x < x)
      (hpos : y < C.product y) : False := by
    have hdx : d x < 0 := sub_neg.mpr hneg
    have hdy : 0 < d y := sub_pos.mpr hpos
    have hzero : (0 : ℝ) ∈ Set.uIcc (d x) (d y) :=
      Set.mem_uIcc_of_le hdx.le hdy.le
    obtain ⟨z, hzxy, hdz⟩ :=
      intermediate_value_uIcc hdcont.continuousOn hzero
    have hz : z ∈ Set.Ioo p c := by
      rcases Set.mem_uIcc.mp hzxy with hxy | hyx
      · exact ⟨hpx.trans_le hxy.1, hxy.2.trans_lt hyc⟩
      · exact ⟨hpy.trans_le hyx.1, hyx.2.trans_lt hxc⟩
    apply hnotfix z hz.1 hz.2
    apply Subtype.ext
    exact sub_eq_zero.mp hdz
  obtain ⟨m, hpm, hmc⟩ := exists_between hpc
  have hmne : C.product m ≠ m := hnotfix m hpm hmc
  rcases lt_or_gt_of_ne hmne with hmneg | hmpos
  · right
    intro x hpx hxc
    have hxne : C.product x ≠ x := hnotfix x hpx hxc
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · exact hxneg
    · exact (opposite_impossible m x hpm hmc hpx hxc hmneg hxpos).elim
  · left
    intro x hpx hxc
    have hxne : C.product x ≠ x := hnotfix x hpx hxc
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · exact (opposite_impossible x m hpx hxc hpm hmc hxneg hmpos).elim
    · exact hxpos

private theorem repellingGapData_of_movesRight
    {C : NormalizedConstantSlopeCounterexample} {bound : ℕ}
    {X : ProductFixedSetPackage C bound} {p c : I}
    (hgap : ConsecutiveInFinset X.points p c)
    (hmoves : ∀ x : I, p < x → x < c → x < C.product x) :
    Nonempty (RepellingGapData C bound X) := by
  have hscale_pos : 0 < C.scale_P * C.scale_Q :=
    mul_pos (zero_lt_one.trans C.one_lt_scale_P)
      (zero_lt_one.trans C.one_lt_scale_Q)
  have hproductSlope : HasConstantAbsoluteSlope C.product
      (C.scale_P * C.scale_Q) := by
    simpa [NormalizedConstantSlopeCounterexample.product] using
      C.constantSlope_P.comp_of_pos
        (zero_lt_one.trans C.one_lt_scale_Q) C.constantSlope_Q
  obtain ⟨partition, hpartition⟩ := hproductSlope.2
  have hpfix : IsFixedPoint C.product p :=
    (X.mem_points p).mp hgap.1
  have hpc : p < c := hgap.2.2.1
  have hpRight : p < rightEndpoint := hpc.trans_le c.property.2
  obtain ⟨a, b, hab, hap, hpb⟩ :=
    partition.exists_adjacent_Ico hpRight
  obtain ⟨m, d, hmabs, hformula⟩ := hpartition hab
  have hpCell : p ∈ intervalCell a b := ⟨hap, hpb.le⟩
  obtain ⟨qReal, hpqReal, hqReal⟩ :=
    exists_between (lt_min hpb hpc)
  let q : I := ⟨qReal,
    p.property.1.trans hpqReal.le,
    (hqReal.trans_le (min_le_right b (c : ℝ))).le.trans c.property.2⟩
  have hpq : p < q := hpqReal
  have hqb : (q : ℝ) < b :=
    hqReal.trans_le (min_le_left b (c : ℝ))
  have hqc : q < c :=
    hqReal.trans_le (min_le_right b (c : ℝ))
  have hqCell : q ∈ intervalCell a b :=
    ⟨hap.trans hpq.le, hqb.le⟩
  have hqmove : q < C.product q := hmoves q hpq hqc
  have hpformula := hformula p hpCell
  have hqformula := hformula q hqCell
  have hpval : (C.product p : ℝ) = (p : ℝ) := congrArg Subtype.val hpfix
  have hmone : 1 < m := by
    rw [hpval] at hpformula
    have hqmoveReal : (q : ℝ) < (C.product q : ℝ) := hqmove
    rw [hqformula] at hqmoveReal
    nlinarith
  have hm : m = C.scale_P * C.scale_Q := by
    simpa [abs_of_pos (zero_lt_one.trans hmone)] using hmabs
  let epsilon : ℝ := min (b - (p : ℝ)) ((c : ℝ) - (p : ℝ))
  have hepsilon : 0 < epsilon := by
    exact lt_min (sub_pos.mpr hpb) (sub_pos.mpr hpc)
  let side : DirectedSide := rightDirectedSide p hpRight
  refine ⟨{
    p := p
    c := c
    consecutive := hgap
    product_moves_right := hmoves
    side := side
    side_base := rfl
    side_direction := rfl
    product_repelling := ?_ }⟩
  refine ⟨hpfix, hscale_pos, epsilon, hepsilon, ?_⟩
  intro x hxray hxnear
  have hpx : p ≤ x := by
    simpa [side, rightDirectedSide, Side.closedRay] using hxray
  have hdiff_nonneg : 0 ≤ (x : ℝ) - (p : ℝ) := sub_nonneg.mpr hpx
  have habs : |(x : ℝ) - (p : ℝ)| = (x : ℝ) - (p : ℝ) :=
    abs_of_nonneg hdiff_nonneg
  have hdiff_b : |(x : ℝ) - (p : ℝ)| < b - (p : ℝ) :=
    hxnear.trans_le (min_le_left _ _)
  have hdiff_c : |(x : ℝ) - (p : ℝ)| < (c : ℝ) - (p : ℝ) :=
    hxnear.trans_le (min_le_right _ _)
  rw [habs] at hdiff_b hdiff_c
  have hxb : (x : ℝ) < b := by linarith
  have hxc : (x : ℝ) < (c : ℝ) := by linarith
  have hxCell : x ∈ intervalCell a b :=
    ⟨hap.trans hpx, hxb.le⟩
  have hxformula := hformula x hxCell
  have heq :
      (C.product x : ℝ) - (p : ℝ) =
        (C.scale_P * C.scale_Q) * ((x : ℝ) - (p : ℝ)) := by
    rw [hxformula, hm]
    rw [hpval] at hpformula
    rw [hm] at hpformula
    linarith
  have himage : p ≤ C.product x := by
    apply Subtype.coe_le_coe.mp
    have hnonneg : 0 ≤
        (C.scale_P * C.scale_Q) * ((x : ℝ) - (p : ℝ)) :=
      mul_nonneg hscale_pos.le hdiff_nonneg
    linarith
  constructor
  · simpa [side, rightDirectedSide, Side.closedRay] using himage
  · simpa [side, rightDirectedSide] using heq

/-- Simultaneous reflection, if necessary, supplies a right-directed
repelling gap while preserving the extremal returned-power property. -/
theorem orientedRepellingGap_exists
    (C : NormalizedConstantSlopeCounterexample) (bound L : ℕ)
    (hbound : (fixedPoints C.product).ncard ≤ bound)
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L) :
    ∃ C' : NormalizedConstantSlopeCounterexample,
      IsOrientationVariant C C' ∧
      ReturnedPowersIrreducible C'.P C'.Q L ∧
      ∃ X : ProductFixedSetPackage C' bound,
        Nonempty (RepellingGapData C' bound X) := by
  obtain ⟨X⟩ := productFixedSetPackage_exists C bound hbound
  obtain ⟨p, c, hgap⟩ := consecutiveInProductFixedFinset_exists X
  rcases consecutiveProductGap_constantSign hgap with hmoves | hmoves
  · exact ⟨C, IsOrientationVariant.refl C, hirreducible, X,
      repellingGapData_of_movesRight hgap hmoves⟩
  · let C' := reflectedCounterexample C
    have hvariant : IsOrientationVariant C C' := by
      right
      exact ⟨rfl, rfl, rfl, rfl⟩
    have hirreducible' : ReturnedPowersIrreducible C'.P C'.Q L := by
      simpa [C', reflectedCounterexample] using
        (returnedPowersIrreducible_reflected hirreducible)
    have hbound' : (fixedPoints C'.product).ncard ≤ bound := by
      calc
        (fixedPoints C'.product).ncard =
            (fixedPoints (reflectedIntervalMap C.product)).ncard := by
          rw [show C'.product = reflectedIntervalMap C.product from
            reflectedCounterexample_product C]
        _ = (fixedPoints C.product).ncard := fixedPoints_reflected_ncard _
        _ ≤ bound := hbound
    obtain ⟨X'⟩ := productFixedSetPackage_exists C' bound hbound'
    let p' : I := reflectPoint c
    let c' : I := reflectPoint p
    have hp'c' : p' < c' := reflectPoint_strictAnti hgap.2.2.1
    have hgap' : ConsecutiveInFinset X'.points p' c' := by
      refine ⟨?_, ?_, hp'c', ?_⟩
      · apply (X'.mem_points p').mpr
        rw [show C'.product = reflectedIntervalMap C.product from
          reflectedCounterexample_product C]
        apply (isFixedPoint_reflectedIntervalMap C.product p').mpr
        simpa [p'] using (X.mem_points c).mp hgap.2.1
      · apply (X'.mem_points c').mpr
        rw [show C'.product = reflectedIntervalMap C.product from
          reflectedCounterexample_product C]
        apply (isFixedPoint_reflectedIntervalMap C.product c').mpr
        simpa [c'] using (X.mem_points p).mp hgap.1
      · intro x hx hbetween
        have hpx : p < reflectPoint x := by
          have h := reflectPoint_strictAnti hbetween.2
          simpa [c'] using h
        have hxc : reflectPoint x < c := by
          have h := reflectPoint_strictAnti hbetween.1
          simpa [p'] using h
        apply hgap.2.2.2 (reflectPoint x)
        · apply (X.mem_points (reflectPoint x)).mpr
          have hxfix : IsFixedPoint C'.product x :=
            (X'.mem_points x).mp hx
          rw [show C'.product = reflectedIntervalMap C.product from
            reflectedCounterexample_product C] at hxfix
          exact (isFixedPoint_reflectedIntervalMap C.product x).mp hxfix
        · exact ⟨hpx, hxc⟩
    have hmoves' :
        ∀ x : I, p' < x → x < c' → x < C'.product x := by
      intro x hpx hxc
      have hpOrig : p < reflectPoint x := by
        have h := reflectPoint_strictAnti hxc
        simpa [c'] using h
      have hcOrig : reflectPoint x < c := by
        have h := reflectPoint_strictAnti hpx
        simpa [p'] using h
      have hmove := hmoves (reflectPoint x) hpOrig hcOrig
      have hant := reflectPoint_strictAnti hmove
      rw [show C'.product = reflectedIntervalMap C.product from
        reflectedCounterexample_product C]
      simpa [reflectedIntervalMap, Function.comp_apply] using hant
    exact ⟨C', hvariant, hirreducible', X',
      repellingGapData_of_movesRight hgap' hmoves'⟩

/-! ## F3: the finite side action and factorial return germs -/

private def DeltaAlongSide (side : Side) (delta : ℝ) : Prop :=
  match side with
  | .left => delta ≤ 0
  | .right => 0 ≤ delta

private theorem mem_closedRay_iff_deltaAlong
    (side : Side) (base x : I) :
    x ∈ side.closedRay base ↔
      DeltaAlongSide side ((x : ℝ) - (base : ℝ)) := by
  cases side <;> simp [Side.closedRay, DeltaAlongSide, sub_nonpos, sub_nonneg]

private theorem mem_puncturedRay_iff_deltaAlong_strict
    (side : Side) (base x : I) :
    x ∈ side.puncturedRay base ↔
      match side with
      | .left => (x : ℝ) - (base : ℝ) < 0
      | .right => 0 < (x : ℝ) - (base : ℝ) := by
  cases side <;> simp [Side.puncturedRay, sub_neg, sub_pos]

/-- Every available directed side contains punctured points arbitrarily close
to its base. -/
private theorem DirectedSide.exists_punctured_point_below
    (sigma : DirectedSide) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ q : I, q ∈ sigma.direction.puncturedRay sigma.base ∧
      |(q : ℝ) - (sigma.base : ℝ)| < epsilon := by
  cases hdirection : sigma.direction with
  | right =>
      rcases sigma.available with ⟨z, hz⟩
      have hbz : sigma.base < z := by
        simpa [hdirection, Side.puncturedRay] using hz
      have hbzReal : (sigma.base : ℝ) < (z : ℝ) := hbz
      obtain ⟨delta, hdelta, hdeltalt⟩ :=
        exists_between (lt_min (sub_pos.mpr hbzReal) hepsilon)
      let q : I := ⟨(sigma.base : ℝ) + delta,
        sigma.base.property.1.trans (le_add_of_nonneg_right hdelta.le), by
          have hz1 : (z : ℝ) ≤ 1 := z.property.2
          have hdeltaBound : delta < (z : ℝ) - (sigma.base : ℝ) :=
            hdeltalt.trans_le (min_le_left _ _)
          exact (by linarith : (sigma.base : ℝ) + delta ≤ 1)⟩
      refine ⟨q, ?_, ?_⟩
      · change (sigma.base : ℝ) < (q : ℝ)
        dsimp [q]
        linarith
      · simp only [q, add_sub_cancel_left, abs_of_pos hdelta]
        exact hdeltalt.trans_le (min_le_right _ _)
  | left =>
      rcases sigma.available with ⟨z, hz⟩
      have hzb : z < sigma.base := by
        simpa [hdirection, Side.puncturedRay] using hz
      have hzbReal : (z : ℝ) < (sigma.base : ℝ) := hzb
      obtain ⟨delta, hdelta, hdeltalt⟩ :=
        exists_between (lt_min (sub_pos.mpr hzbReal) hepsilon)
      let q : I := ⟨(sigma.base : ℝ) - delta, by
          have hz0 : 0 ≤ (z : ℝ) := z.property.1
          have hdeltaBound : delta < (sigma.base : ℝ) - (z : ℝ) :=
            hdeltalt.trans_le (min_le_left _ _)
          exact (by linarith : 0 ≤ (sigma.base : ℝ) - delta),
        sub_le_self _ hdelta.le |>.trans sigma.base.property.2⟩
      refine ⟨q, ?_, ?_⟩
      · change (q : ℝ) < (sigma.base : ℝ)
        dsimp [q]
        linarith
      · simp only [q, sub_sub_cancel_left, abs_neg, abs_of_pos hdelta]
        exact hdeltalt.trans_le (min_le_right _ _)

private theorem mem_closedRay_of_mem_puncturedRay
    {side : Side} {x y : I} (h : y ∈ side.puncturedRay x) :
    y ∈ side.closedRay x := by
  cases side <;> simpa [Side.puncturedRay, Side.closedRay] using h.le

private theorem directedSide_eq_of_base_direction
    {sigma tau : DirectedSide}
    (hbase : sigma.base = tau.base)
    (hdirection : sigma.direction = tau.direction) : sigma = tau := by
  cases sigma with
  | mk sigmaBase sigmaDirection sigmaAvailable =>
      cases tau with
      | mk tauBase tauDirection tauAvailable =>
          simp only at hbase hdirection ⊢
          subst tauBase
          subst tauDirection
          rfl

private theorem exists_adjacent_left_of_pos_fold
    (partition : RealPartition) (x : I) (hxpos : (0 : ℝ) < x) :
    ∃ a b : ℝ, partition.Adjacent a b ∧
      a < (x : ℝ) ∧ (x : ℝ) ≤ b := by
  classical
  by_cases hxvertex : (x : ℝ) ∈ partition.points
  · let lower := partition.points.filter fun z => z < (x : ℝ)
    have hlower : lower.Nonempty := by
      refine ⟨0, ?_⟩
      simp [lower, partition.zero_mem, hxpos]
    obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
    have ha' := Finset.mem_filter.mp ha
    refine ⟨a, (x : ℝ), ⟨ha'.1, hxvertex, ha'.2, ?_⟩,
      ha'.2, le_rfl⟩
    intro c hc hac
    have hclower : c ∈ lower := Finset.mem_filter.mpr ⟨hc, hac.2⟩
    have hca : c ≤ a := by simpa using hamax c hclower
    exact (not_lt_of_ge hca) hac.1
  · obtain ⟨a, b, hab, hax, hxb⟩ :=
      partition.exists_adjacent_containing x
    have hax' : a < (x : ℝ) := lt_of_le_of_ne hax fun hxa =>
      hxvertex (hxa ▸ hab.1)
    exact ⟨a, b, hab, hax', hxb⟩

private structure OneSidedAffineGerm
    (T : IntervalMap) (sigma : DirectedSide) (s : ℝ) where
  slope : ℝ
  offset : ℝ
  abs_slope : |slope| = s
  radius : ℝ
  radius_pos : 0 < radius
  formula : ∀ x : I,
    x ∈ sigma.direction.closedRay sigma.base →
    |(x : ℝ) - (sigma.base : ℝ)| < radius →
      (T x : ℝ) = slope * (x : ℝ) + offset
  point_of_delta : ∀ delta : ℝ,
    DeltaAlongSide sigma.direction delta → |delta| < radius →
      ∃ x : I, (x : ℝ) = (sigma.base : ℝ) + delta

private theorem oneSidedAffineGerm_exists
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (sigma : DirectedSide) :
    Nonempty (OneSidedAffineGerm T sigma s) := by
  obtain ⟨partition, hpartition⟩ := hT.2
  cases hdirection : sigma.direction with
  | right =>
      have hbaseRight : sigma.base < rightEndpoint := by
        rcases sigma.available with ⟨z, hz⟩
        have hbz : sigma.base < z := by
          simpa [hdirection, Side.puncturedRay] using hz
        exact hbz.trans_le z.property.2
      obtain ⟨a, b, hab, habase, hbaseb⟩ :=
        partition.exists_adjacent_Ico hbaseRight
      obtain ⟨m, d, hm, hformula⟩ := hpartition hab
      refine ⟨{
        slope := m
        offset := d
        abs_slope := hm
        radius := b - (sigma.base : ℝ)
        radius_pos := sub_pos.mpr hbaseb
        formula := ?_
        point_of_delta := ?_ }⟩
      · intro x hxray hxnear
        have hbasex : sigma.base ≤ x := by
          simpa [hdirection, Side.closedRay] using hxray
        have hbasexReal : (sigma.base : ℝ) ≤ (x : ℝ) := hbasex
        have hdiff : (x : ℝ) - (sigma.base : ℝ) <
            b - (sigma.base : ℝ) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hbasexReal)] at hxnear
          exact hxnear
        apply hformula x
        exact ⟨habase.trans hbasexReal,
          (by linarith : (x : ℝ) ≤ b)⟩
      · intro delta hdelta hnear
        have hdelta0 : 0 ≤ delta := by
          simpa [hdirection, DeltaAlongSide] using hdelta
        have hdeltab : delta < b - (sigma.base : ℝ) := by
          simpa [abs_of_nonneg hdelta0] using hnear
        refine ⟨⟨(sigma.base : ℝ) + delta, ?_, ?_⟩, rfl⟩
        · exact sigma.base.property.1.trans (le_add_of_nonneg_right hdelta0)
        · have hb1 : b ≤ 1 := (partition.points_subset hab.2.1).2
          linarith
  | left =>
      have hbasePos : (0 : ℝ) < sigma.base := by
        rcases sigma.available with ⟨z, hz⟩
        have hzb : z < sigma.base := by
          simpa [hdirection, Side.puncturedRay] using hz
        exact z.property.1.trans_lt hzb
      obtain ⟨a, b, hab, habase, hbaseb⟩ :=
        exists_adjacent_left_of_pos_fold partition sigma.base hbasePos
      obtain ⟨m, d, hm, hformula⟩ := hpartition hab
      refine ⟨{
        slope := m
        offset := d
        abs_slope := hm
        radius := (sigma.base : ℝ) - a
        radius_pos := sub_pos.mpr habase
        formula := ?_
        point_of_delta := ?_ }⟩
      · intro x hxray hxnear
        have hxbase : x ≤ sigma.base := by
          simpa [hdirection, Side.closedRay] using hxray
        have hxbaseReal : (x : ℝ) ≤ (sigma.base : ℝ) := hxbase
        have hdiff : (sigma.base : ℝ) - (x : ℝ) <
            (sigma.base : ℝ) - a := by
          have habs : |(x : ℝ) - (sigma.base : ℝ)| =
              (sigma.base : ℝ) - (x : ℝ) := by
            rw [abs_of_nonpos (sub_nonpos.mpr hxbaseReal)]
            ring
          simpa [habs] using hxnear
        apply hformula x
        exact ⟨(by linarith : a ≤ (x : ℝ)), hxbaseReal.trans hbaseb⟩
      · intro delta hdelta hnear
        have hdelta0 : delta ≤ 0 := by
          simpa [hdirection, DeltaAlongSide] using hdelta
        have hdeltaa : -delta < (sigma.base : ℝ) - a := by
          have habs : |delta| = -delta := abs_of_nonpos hdelta0
          simpa [habs] using hnear
        refine ⟨⟨(sigma.base : ℝ) + delta, ?_, ?_⟩, rfl⟩
        · have ha0 : 0 ≤ a := (partition.points_subset hab.1).1
          linarith
        · exact (add_le_of_nonpos_right hdelta0).trans sigma.base.property.2

private theorem OneSidedAffineGerm.exists_punctured_point
    {T : IntervalMap} {sigma : DirectedSide} {s : ℝ}
    (g : OneSidedAffineGerm T sigma s) :
    ∃ q : I, q ∈ sigma.direction.puncturedRay sigma.base ∧
      |(q : ℝ) - (sigma.base : ℝ)| < g.radius := by
  cases hdirection : sigma.direction with
  | right =>
      rcases sigma.available with ⟨z, hz⟩
      have hbz : sigma.base < z := by
        simpa [hdirection, Side.puncturedRay] using hz
      have hbzReal : (sigma.base : ℝ) < (z : ℝ) := hbz
      obtain ⟨delta, hdelta, hdeltalt⟩ :=
        exists_between (lt_min (sub_pos.mpr hbzReal) g.radius_pos)
      obtain ⟨q, hq⟩ := g.point_of_delta delta (by
        simpa [hdirection, DeltaAlongSide] using hdelta.le) (by
        rw [abs_of_pos hdelta]
        exact hdeltalt.trans_le (min_le_right _ _))
      refine ⟨q, ?_, ?_⟩
      · simp only [hdirection, Side.puncturedRay, Set.mem_Ioi]
        apply Subtype.coe_lt_coe.mp
        rw [hq]
        linarith
      · rw [hq, add_sub_cancel_left, abs_of_pos hdelta]
        exact hdeltalt.trans_le (min_le_right _ _)
  | left =>
      rcases sigma.available with ⟨z, hz⟩
      have hzb : z < sigma.base := by
        simpa [hdirection, Side.puncturedRay] using hz
      have hzbReal : (z : ℝ) < (sigma.base : ℝ) := hzb
      obtain ⟨delta, hdelta, hdeltalt⟩ :=
        exists_between (lt_min (sub_pos.mpr hzbReal) g.radius_pos)
      obtain ⟨q, hq⟩ := g.point_of_delta (-delta) (by
        simp [hdirection, DeltaAlongSide, hdelta.le]) (by
        rw [abs_neg, abs_of_pos hdelta]
        exact hdeltalt.trans_le (min_le_right _ _))
      refine ⟨q, ?_, ?_⟩
      · simp only [hdirection, Side.puncturedRay, Set.mem_Iio]
        apply Subtype.coe_lt_coe.mp
        rw [hq]
        linarith
      · rw [hq, add_sub_cancel_left, abs_neg, abs_of_pos hdelta]
        exact hdeltalt.trans_le (min_le_right _ _)

private structure ConstantSlopeSideImage
    (T : IntervalMap) (sigma : DirectedSide) (s : ℝ) where
  germ : OneSidedAffineGerm T sigma s
  target : DirectedSide
  carries : CarriesDirectedSide T sigma target
  locally_onto : ∀ y : I,
    y ∈ target.direction.closedRay target.base →
    |(y : ℝ) - (target.base : ℝ)| < s * germ.radius →
      ∃ x : I,
        x ∈ sigma.direction.closedRay sigma.base ∧
        |(x : ℝ) - (sigma.base : ℝ)| < germ.radius ∧ T x = y

private theorem constantSlopeSideImage_exists
    {T : IntervalMap} {s : ℝ} (hT : HasConstantAbsoluteSlope T s)
    (hs : 0 < s) (sigma : DirectedSide) :
    Nonempty (ConstantSlopeSideImage T sigma s) := by
  obtain ⟨g⟩ := oneSidedAffineGerm_exists hT sigma
  obtain ⟨q, hqside, hqnear⟩ := g.exists_punctured_point
  have hbaseRay : sigma.base ∈
      sigma.direction.closedRay sigma.base := by
    rw [mem_closedRay_iff_deltaAlong]
    cases sigma.direction <;> simp [DeltaAlongSide]
  have hbaseFormula := g.formula sigma.base hbaseRay (by
    simpa using g.radius_pos)
  have hqRay : q ∈ sigma.direction.closedRay sigma.base := by
    cases hd : sigma.direction with
    | left =>
        have : q < sigma.base := by
          simpa [hd, Side.puncturedRay] using hqside
        simpa [hd, Side.closedRay] using this.le
    | right =>
        have : sigma.base < q := by
          simpa [hd, Side.puncturedRay] using hqside
        simpa [hd, Side.closedRay] using this.le
  have hqFormula := g.formula q hqRay hqnear
  have hmne : g.slope ≠ 0 := by
    intro hm
    have habs := g.abs_slope
    rw [hm, abs_zero] at habs
    linarith
  have hqne : (q : ℝ) - (sigma.base : ℝ) ≠ 0 := by
    intro hzero
    have heq : q = sigma.base := Subtype.ext (sub_eq_zero.mp hzero)
    cases hdirection : sigma.direction with
    | left =>
        have hlt : q < sigma.base := by
          simpa [hdirection, Side.puncturedRay] using hqside
        exact (ne_of_lt hlt) heq
    | right =>
        have hlt : sigma.base < q := by
          simpa [hdirection, Side.puncturedRay] using hqside
        exact (ne_of_gt hlt) heq
  have hqdiff :
      (T q : ℝ) - (T sigma.base : ℝ) =
        g.slope * ((q : ℝ) - (sigma.base : ℝ)) := by
    linarith
  have hTne : T q ≠ T sigma.base := by
    intro heq
    have heqReal := congrArg Subtype.val heq
    have hzero : g.slope * ((q : ℝ) - (sigma.base : ℝ)) = 0 := by
      linarith
    exact (mul_ne_zero hmne hqne) hzero
  rcases lt_or_gt_of_ne hTne with hleft | hright
  · have htargetAvailable : leftEndpoint < T sigma.base :=
      (T q).property.1.trans_lt hleft
    let tau : DirectedSide := leftDirectedSide (T sigma.base) htargetAvailable
    have hcarry : CarriesDirectedSide T sigma tau := by
      refine ⟨rfl, g.radius, g.radius_pos, ?_⟩
      intro x hxray hxnear
      have hxFormula := g.formula x hxray hxnear
      have hxdiff :
          (T x : ℝ) - (T sigma.base : ℝ) =
            g.slope * ((x : ℝ) - (sigma.base : ℝ)) := by
        linarith
      have hTx : (T x : ℝ) ≤ (T sigma.base : ℝ) := by
        cases hdirection : sigma.direction with
        | left =>
            have hqdelta : (q : ℝ) - (sigma.base : ℝ) < 0 := by
              simpa [hdirection] using
                (mem_puncturedRay_iff_deltaAlong_strict
                  Side.left sigma.base q).mp (by simpa [hdirection] using hqside)
            have hxdelta : (x : ℝ) - (sigma.base : ℝ) ≤ 0 := by
              simpa [DeltaAlongSide] using
                (mem_closedRay_iff_deltaAlong Side.left sigma.base x).mp
                  (by simpa [hdirection] using hxray)
            have hTd : (T q : ℝ) - (T sigma.base : ℝ) < 0 := sub_neg.mpr hleft
            nlinarith [hqdiff, hxdiff]
        | right =>
            have hqdelta : 0 < (q : ℝ) - (sigma.base : ℝ) := by
              simpa [hdirection] using
                (mem_puncturedRay_iff_deltaAlong_strict
                  Side.right sigma.base q).mp (by simpa [hdirection] using hqside)
            have hxdelta : 0 ≤ (x : ℝ) - (sigma.base : ℝ) := by
              simpa [DeltaAlongSide] using
                (mem_closedRay_iff_deltaAlong Side.right sigma.base x).mp
                  (by simpa [hdirection] using hxray)
            have hTd : (T q : ℝ) - (T sigma.base : ℝ) < 0 := sub_neg.mpr hleft
            nlinarith [hqdiff, hxdiff]
      simpa [tau, leftDirectedSide, Side.closedRay] using hTx
    refine ⟨{
      germ := g
      target := tau
      carries := hcarry
      locally_onto := ?_ }⟩
    intro y hyray hynear
    have hyDelta : (y : ℝ) - (T sigma.base : ℝ) ≤ 0 := by
      simpa [tau, leftDirectedSide, Side.closedRay, sub_nonpos] using hyray
    let delta : ℝ :=
      ((y : ℝ) - (T sigma.base : ℝ)) / g.slope
    have habsDelta : |delta| < g.radius := by
      have hnear : |(y : ℝ) - (T sigma.base : ℝ)| <
          s * g.radius := by
        simpa [tau, leftDirectedSide] using hynear
      rw [show |delta| =
          |(y : ℝ) - (T sigma.base : ℝ)| / s by
        dsimp [delta]
        rw [abs_div, g.abs_slope]]
      exact (div_lt_iff₀ hs).2 (by simpa [mul_comm] using hnear)
    have hdeltaSide : DeltaAlongSide sigma.direction delta := by
      cases hdirection : sigma.direction with
      | left =>
          have hqdelta : (q : ℝ) - (sigma.base : ℝ) < 0 := by
            simpa [hdirection] using
              (mem_puncturedRay_iff_deltaAlong_strict
                Side.left sigma.base q).mp (by simpa [hdirection] using hqside)
          have hmpos : 0 < g.slope := by
            have hTd : (T q : ℝ) - (T sigma.base : ℝ) < 0 := sub_neg.mpr hleft
            nlinarith [hqdiff]
          simp only [hdirection, DeltaAlongSide]
          exact (div_nonpos_iff).2 (Or.inr ⟨hyDelta, hmpos.le⟩)
      | right =>
          have hqdelta : 0 < (q : ℝ) - (sigma.base : ℝ) := by
            simpa [hdirection] using
              (mem_puncturedRay_iff_deltaAlong_strict
                Side.right sigma.base q).mp (by simpa [hdirection] using hqside)
          have hmneg : g.slope < 0 := by
            have hTd : (T q : ℝ) - (T sigma.base : ℝ) < 0 := sub_neg.mpr hleft
            nlinarith [hqdiff]
          simp only [hdirection, DeltaAlongSide]
          exact (div_nonneg_iff).2 (Or.inr ⟨hyDelta, hmneg.le⟩)
    obtain ⟨x, hx⟩ := g.point_of_delta delta hdeltaSide habsDelta
    have hxray : x ∈ sigma.direction.closedRay sigma.base := by
      rw [mem_closedRay_iff_deltaAlong, hx]
      simpa [DeltaAlongSide] using hdeltaSide
    have hxFormula := g.formula x hxray (by simpa [hx] using habsDelta)
    have hmul : g.slope * delta =
        (y : ℝ) - (T sigma.base : ℝ) := by
      dsimp [delta]
      field_simp
    refine ⟨x, hxray, by simpa [hx] using habsDelta, ?_⟩
    apply Subtype.ext
    dsimp
    rw [hx] at hxFormula
    ring_nf at hxFormula
    linarith

  · have htargetAvailable : T sigma.base < rightEndpoint :=
      hright.trans_le (T q).property.2
    let tau : DirectedSide := rightDirectedSide (T sigma.base) htargetAvailable
    have hcarry : CarriesDirectedSide T sigma tau := by
      refine ⟨rfl, g.radius, g.radius_pos, ?_⟩
      intro x hxray hxnear
      have hxFormula := g.formula x hxray hxnear
      have hxdiff :
          (T x : ℝ) - (T sigma.base : ℝ) =
            g.slope * ((x : ℝ) - (sigma.base : ℝ)) := by
        linarith
      have hTx : (T sigma.base : ℝ) ≤ (T x : ℝ) := by
        cases hdirection : sigma.direction with
        | left =>
            have hqdelta : (q : ℝ) - (sigma.base : ℝ) < 0 := by
              simpa [hdirection] using
                (mem_puncturedRay_iff_deltaAlong_strict
                  Side.left sigma.base q).mp (by simpa [hdirection] using hqside)
            have hxdelta : (x : ℝ) - (sigma.base : ℝ) ≤ 0 := by
              simpa [DeltaAlongSide] using
                (mem_closedRay_iff_deltaAlong Side.left sigma.base x).mp
                  (by simpa [hdirection] using hxray)
            have hTd : 0 < (T q : ℝ) - (T sigma.base : ℝ) := sub_pos.mpr hright
            nlinarith [hqdiff, hxdiff]
        | right =>
            have hqdelta : 0 < (q : ℝ) - (sigma.base : ℝ) := by
              simpa [hdirection] using
                (mem_puncturedRay_iff_deltaAlong_strict
                  Side.right sigma.base q).mp (by simpa [hdirection] using hqside)
            have hxdelta : 0 ≤ (x : ℝ) - (sigma.base : ℝ) := by
              simpa [DeltaAlongSide] using
                (mem_closedRay_iff_deltaAlong Side.right sigma.base x).mp
                  (by simpa [hdirection] using hxray)
            have hTd : 0 < (T q : ℝ) - (T sigma.base : ℝ) := sub_pos.mpr hright
            nlinarith [hqdiff, hxdiff]
      simpa [tau, rightDirectedSide, Side.closedRay] using hTx
    refine ⟨{
      germ := g
      target := tau
      carries := hcarry
      locally_onto := ?_ }⟩
    intro y hyray hynear
    have hyDelta : 0 ≤ (y : ℝ) - (T sigma.base : ℝ) := by
      simpa [tau, rightDirectedSide, Side.closedRay, sub_nonneg] using hyray
    let delta : ℝ :=
      ((y : ℝ) - (T sigma.base : ℝ)) / g.slope
    have habsDelta : |delta| < g.radius := by
      have hnear : |(y : ℝ) - (T sigma.base : ℝ)| <
          s * g.radius := by
        simpa [tau, rightDirectedSide] using hynear
      rw [show |delta| =
          |(y : ℝ) - (T sigma.base : ℝ)| / s by
        dsimp [delta]
        rw [abs_div, g.abs_slope]]
      exact (div_lt_iff₀ hs).2 (by simpa [mul_comm] using hnear)
    have hdeltaSide : DeltaAlongSide sigma.direction delta := by
      cases hdirection : sigma.direction with
      | left =>
          have hqdelta : (q : ℝ) - (sigma.base : ℝ) < 0 := by
            simpa [hdirection] using
              (mem_puncturedRay_iff_deltaAlong_strict
                Side.left sigma.base q).mp (by simpa [hdirection] using hqside)
          have hmneg : g.slope < 0 := by
            have hTd : 0 < (T q : ℝ) - (T sigma.base : ℝ) := sub_pos.mpr hright
            nlinarith [hqdiff]
          simp only [hdirection, DeltaAlongSide]
          exact (div_nonpos_iff).2 (Or.inl ⟨hyDelta, hmneg.le⟩)
      | right =>
          have hqdelta : 0 < (q : ℝ) - (sigma.base : ℝ) := by
            simpa [hdirection] using
              (mem_puncturedRay_iff_deltaAlong_strict
                Side.right sigma.base q).mp (by simpa [hdirection] using hqside)
          have hmpos : 0 < g.slope := by
            have hTd : 0 < (T q : ℝ) - (T sigma.base : ℝ) := sub_pos.mpr hright
            nlinarith [hqdiff]
          simp only [hdirection, DeltaAlongSide]
          exact (div_nonneg_iff).2 (Or.inl ⟨hyDelta, hmpos.le⟩)
    obtain ⟨x, hx⟩ := g.point_of_delta delta hdeltaSide habsDelta
    have hxray : x ∈ sigma.direction.closedRay sigma.base := by
      rw [mem_closedRay_iff_deltaAlong, hx]
      simpa [DeltaAlongSide] using hdeltaSide
    have hxFormula := g.formula x hxray (by simpa [hx] using habsDelta)
    have hmul : g.slope * delta =
        (y : ℝ) - (T sigma.base : ℝ) := by
      dsimp [delta]
      field_simp
    refine ⟨x, hxray, by simpa [hx] using habsDelta, ?_⟩
    apply Subtype.ext
    dsimp
    rw [hx] at hxFormula
    ring_nf at hxFormula
    linarith

private theorem constantSlope_maps_repellingSide
    {H T U : IntervalMap} {s r : ℝ} {sigma : DirectedSide}
    (hT : HasConstantAbsoluteSlope T s) (hs : 0 < s)
    (hrep : HasPositiveDilationGerm H sigma r)
    (hcommute : Function.Commute T H) (hfactor : U ∘ T = H) :
    ∃ image : ConstantSlopeSideImage T sigma s,
      HasPositiveDilationGerm H image.target r ∧
        CarriesDirectedSide U image.target sigma := by
  obtain ⟨image⟩ := constantSlopeSideImage_exists hT hs sigma
  rcases hrep with ⟨hHbase, hr, epsilonH, hepsilonH, hHgerm⟩
  have hTbase : T sigma.base = image.target.base := image.carries.1
  have hbaseFormula := image.germ.formula sigma.base (by
    rw [mem_closedRay_iff_deltaAlong]
    cases sigma.direction <;> simp [DeltaAlongSide]) (by
      simpa using image.germ.radius_pos)
  let sourceRadius : ℝ :=
    min image.germ.radius (min epsilonH (image.germ.radius / r))
  have hsourceRadius : 0 < sourceRadius := by
    exact lt_min image.germ.radius_pos
      (lt_min hepsilonH (div_pos image.germ.radius_pos hr))
  have htargetRepelling :
      HasPositiveDilationGerm H image.target r := by
    have hfixedTarget : IsFixedPoint H image.target.base := by
      rw [← hTbase]
      change H (T sigma.base) = T sigma.base
      rw [← hcommute sigma.base, hHbase]
    refine ⟨hfixedTarget, hr, s * sourceRadius,
      mul_pos hs hsourceRadius, ?_⟩
    intro y hyray hynear
    have hynearLarge :
        |(y : ℝ) - (image.target.base : ℝ)| <
          s * image.germ.radius :=
      hynear.trans_le (mul_le_mul_of_nonneg_left
        (min_le_left _ _) hs.le)
    obtain ⟨x, hxray, hxnear, hTx⟩ :=
      image.locally_onto y hyray hynearLarge
    have hxFormula := image.germ.formula x hxray hxnear
    have hTxReal : (T x : ℝ) = (y : ℝ) := congrArg Subtype.val hTx
    have hTbaseReal : (T sigma.base : ℝ) =
        (image.target.base : ℝ) := congrArg Subtype.val hTbase
    have hsideRelation :
        (y : ℝ) - (image.target.base : ℝ) =
          image.germ.slope * ((x : ℝ) - (sigma.base : ℝ)) := by
      linarith
    have habsRelation :
        |(y : ℝ) - (image.target.base : ℝ)| =
          s * |(x : ℝ) - (sigma.base : ℝ)| := by
      rw [hsideRelation, abs_mul, image.germ.abs_slope]
    have hxsource : |(x : ℝ) - (sigma.base : ℝ)| < sourceRadius := by
      have hsx :
          s * |(x : ℝ) - (sigma.base : ℝ)| < s * sourceRadius := by
        rw [← habsRelation]
        exact hynear
      nlinarith
    have hxepsilon : |(x : ℝ) - (sigma.base : ℝ)| < epsilonH :=
      hxsource.trans_le (min_le_right _ _ |>.trans (min_le_left _ _))
    obtain ⟨hHxray, hHeq⟩ := hHgerm x hxray hxepsilon
    have habsHx :
        |(H x : ℝ) - (sigma.base : ℝ)| =
          r * |(x : ℝ) - (sigma.base : ℝ)| := by
      rw [hHeq, abs_mul, abs_of_pos hr]
    have hxdiv : |(x : ℝ) - (sigma.base : ℝ)| <
        image.germ.radius / r :=
      hxsource.trans_le (min_le_right _ _ |>.trans (min_le_right _ _))
    have hHxnear : |(H x : ℝ) - (sigma.base : ℝ)| <
        image.germ.radius := by
      rw [habsHx]
      simpa [mul_comm] using (lt_div_iff₀ hr).mp hxdiv
    have hHxFormula := image.germ.formula (H x) hHxray hHxnear
    have hHy : H y = T (H x) := by
      rw [← hTx, ← hcommute x]
    have hHyReal : (H y : ℝ) = (T (H x) : ℝ) :=
      congrArg Subtype.val hHy
    have heq :
        (H y : ℝ) - (image.target.base : ℝ) =
          r * ((y : ℝ) - (image.target.base : ℝ)) := by
      calc
        (H y : ℝ) - (image.target.base : ℝ) =
            (T (H x) : ℝ) - (T sigma.base : ℝ) := by
              rw [hHyReal, hTbaseReal]
        _ = image.germ.slope *
              ((H x : ℝ) - (sigma.base : ℝ)) := by
              linarith
        _ = image.germ.slope *
              (r * ((x : ℝ) - (sigma.base : ℝ))) := by rw [hHeq]
        _ = r *
              (image.germ.slope * ((x : ℝ) - (sigma.base : ℝ))) := by ring
        _ = r * ((y : ℝ) - (image.target.base : ℝ)) := by
              rw [← hsideRelation]
    have himageRay : H y ∈
        image.target.direction.closedRay image.target.base := by
      rw [mem_closedRay_iff_deltaAlong]
      have hyDelta :=
        (mem_closedRay_iff_deltaAlong image.target.direction
          image.target.base y).mp hyray
      cases hdirection : image.target.direction <;>
        simp only [hdirection, DeltaAlongSide] at hyDelta ⊢ <;> nlinarith
    exact ⟨himageRay, heq⟩
  have hcomplementCarries : CarriesDirectedSide U image.target sigma := by
    have hbase : U image.target.base = sigma.base := by
      rw [← hTbase]
      have h := congrFun hfactor sigma.base
      change U (T sigma.base) = H sigma.base at h
      rw [h, hHbase]
    let sourceRadius' : ℝ := min image.germ.radius epsilonH
    have hsourceRadius' : 0 < sourceRadius' :=
      lt_min image.germ.radius_pos hepsilonH
    refine ⟨hbase, s * sourceRadius', mul_pos hs hsourceRadius', ?_⟩
    intro y hyray hynear
    have hynearLarge :
        |(y : ℝ) - (image.target.base : ℝ)| <
          s * image.germ.radius :=
      hynear.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) hs.le)
    obtain ⟨x, hxray, hxnear, hTx⟩ :=
      image.locally_onto y hyray hynearLarge
    have hxFormula := image.germ.formula x hxray hxnear
    have hTxReal : (T x : ℝ) = (y : ℝ) := congrArg Subtype.val hTx
    have hTbaseReal : (T sigma.base : ℝ) =
        (image.target.base : ℝ) := congrArg Subtype.val hTbase
    have hsideRelation :
        (y : ℝ) - (image.target.base : ℝ) =
          image.germ.slope * ((x : ℝ) - (sigma.base : ℝ)) := by
      linarith
    have habsRelation :
        |(y : ℝ) - (image.target.base : ℝ)| =
          s * |(x : ℝ) - (sigma.base : ℝ)| := by
      rw [hsideRelation, abs_mul, image.germ.abs_slope]
    have hxsource : |(x : ℝ) - (sigma.base : ℝ)| < sourceRadius' := by
      have hsx :
          s * |(x : ℝ) - (sigma.base : ℝ)| < s * sourceRadius' := by
        rw [← habsRelation]
        exact hynear
      nlinarith
    have hxepsilon : |(x : ℝ) - (sigma.base : ℝ)| < epsilonH :=
      hxsource.trans_le (min_le_right _ _)
    have hHxray := (hHgerm x hxray hxepsilon).1
    have hUy : U y = H x := by
      rw [← hTx]
      exact congrFun hfactor x
    rw [hUy]
    exact hHxray
  exact ⟨image, htargetRepelling, hcomplementCarries⟩

/-- A locally onto one-sided affine chart determines the carried target side
uniquely. This is the endpoint-safe uniqueness input used to turn the two
generator images into inverse permutations. -/
private theorem ConstantSlopeSideImage.target_eq_of_carries
    {T : IntervalMap} {sigma tau : DirectedSide} {s : ℝ}
    (hs : 0 < s) (image : ConstantSlopeSideImage T sigma s)
    (hcarry : CarriesDirectedSide T sigma tau) :
    tau = image.target := by
  rcases image.carries with ⟨himageBase, epsilonImage,
    hepsilonImage, himageLocal⟩
  rcases hcarry with ⟨htauBase, epsilonTau, hepsilonTau, htauLocal⟩
  let epsilon : ℝ :=
    min image.germ.radius (min epsilonImage epsilonTau)
  have hepsilon : 0 < epsilon := by
    exact lt_min image.germ.radius_pos
      (lt_min hepsilonImage hepsilonTau)
  obtain ⟨q, hqpunctured, hqnear⟩ :=
    sigma.exists_punctured_point_below hepsilon
  have hqray : q ∈ sigma.direction.closedRay sigma.base :=
    mem_closedRay_of_mem_puncturedRay hqpunctured
  have hqGerm : |(q : ℝ) - (sigma.base : ℝ)| < image.germ.radius :=
    hqnear.trans_le (min_le_left _ _)
  have hqImage : |(q : ℝ) - (sigma.base : ℝ)| < epsilonImage :=
    hqnear.trans_le (min_le_right _ _ |>.trans (min_le_left _ _))
  have hqTau : |(q : ℝ) - (sigma.base : ℝ)| < epsilonTau :=
    hqnear.trans_le (min_le_right _ _ |>.trans (min_le_right _ _))
  have hTqImage : T q ∈
      image.target.direction.closedRay image.target.base :=
    himageLocal q hqray hqImage
  have hTqTau : T q ∈ tau.direction.closedRay tau.base :=
    htauLocal q hqray hqTau
  have hbaseEq : tau.base = image.target.base := by
    rw [← htauBase, ← himageBase]
  have hbaseRay : sigma.base ∈
      sigma.direction.closedRay sigma.base := by
    rw [mem_closedRay_iff_deltaAlong]
    cases sigma.direction <;> simp [DeltaAlongSide]
  have hbaseFormula := image.germ.formula sigma.base hbaseRay (by
    simpa using image.germ.radius_pos)
  have hqFormula := image.germ.formula q hqray hqGerm
  have hslope : image.germ.slope ≠ 0 := by
    intro hslope
    have habs := image.germ.abs_slope
    rw [hslope, abs_zero] at habs
    linarith
  have hqne : q ≠ sigma.base := by
    cases hdirection : sigma.direction with
    | left =>
        have hlt : q < sigma.base := by
          simpa [hdirection, Side.puncturedRay] using hqpunctured
        exact ne_of_lt hlt
    | right =>
        have hlt : sigma.base < q := by
          simpa [hdirection, Side.puncturedRay] using hqpunctured
        exact ne_of_gt hlt
  have hqdiff : (q : ℝ) - (sigma.base : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (Subtype.val_injective.ne hqne)
  have hTqne : T q ≠ image.target.base := by
    intro hTq
    have hTqReal := congrArg Subtype.val hTq
    have himageBaseReal := congrArg Subtype.val himageBase
    have hzero : image.germ.slope *
        ((q : ℝ) - (sigma.base : ℝ)) = 0 := by
      linarith
    exact (mul_ne_zero hslope hqdiff) hzero
  have hdirection : tau.direction = image.target.direction := by
    cases htau : tau.direction <;> cases himage : image.target.direction
    · rfl
    · exfalso
      apply hTqne
      have hle : T q ≤ tau.base := by
        simpa [htau, Side.closedRay] using hTqTau
      have hge : image.target.base ≤ T q := by
        simpa [himage, Side.closedRay] using hTqImage
      rw [hbaseEq] at hle
      exact le_antisymm hle hge
    · exfalso
      apply hTqne
      have hge : tau.base ≤ T q := by
        simpa [htau, Side.closedRay] using hTqTau
      have hle : T q ≤ image.target.base := by
        simpa [himage, Side.closedRay] using hTqImage
      rw [hbaseEq] at hge
      exact le_antisymm hle hge
    · rfl
  exact directedSide_eq_of_base_direction hbaseEq hdirection

/-- The finite action of the two generators on all repelling directed
states over the product fixed set. -/
structure RepellingSideActionData
    (C : NormalizedConstantSlopeCounterexample) (bound : ℕ)
    (X : ProductFixedSetPackage C bound)
    (G : RepellingGapData C bound X) where
  states : Set DirectedSide
  states_finite : states.Finite
  chosen_mem : G.side ∈ states
  base_mem : ∀ sigma ∈ states, sigma.base ∈ X.points
  repelling : ∀ sigma ∈ states,
    HasPositiveDilationGerm C.product sigma
      (C.scale_P * C.scale_Q)
  card_le : states.ncard ≤ 2 * X.points.card
  actionP : Equiv.Perm {sigma : DirectedSide // sigma ∈ states}
  actionQ : Equiv.Perm {sigma : DirectedSide // sigma ∈ states}
  actionP_carries : ∀ sigma,
    CarriesDirectedSide C.P sigma.1 (actionP sigma).1
  actionQ_carries : ∀ sigma,
    CarriesDirectedSide C.Q sigma.1 (actionQ sigma).1
  actionQ_actionP : ∀ sigma, actionQ (actionP sigma) = sigma
  actionP_actionQ : ∀ sigma, actionP (actionQ sigma) = sigma

/-- Construction of the finite mutually inverse generator permutations on
product-repelling directed sides. -/
private theorem finiteRepellingSidePermutation_exists
    {C : NormalizedConstantSlopeCounterexample} {bound : ℕ}
    {X : ProductFixedSetPackage C bound}
    (G : RepellingGapData C bound X) :
    Nonempty (RepellingSideActionData C bound X G) := by
  classical
  let states : Set DirectedSide :=
    {sigma | HasPositiveDilationGerm C.product sigma
      (C.scale_P * C.scale_Q)}
  let sideCode : Side → Bool
    | .left => false
    | .right => true
  let encode : DirectedSide → I × Bool :=
    fun sigma => (sigma.base, sideCode sigma.direction)
  let targets : Set (I × Bool) :=
    (↑X.points : Set I) ×ˢ (Set.univ : Set Bool)
  have hmaps : ∀ sigma ∈ states, encode sigma ∈ targets := by
    intro sigma hsigma
    have hbase : sigma.base ∈ X.points :=
      (X.mem_points sigma.base).mpr hsigma.1
    simp [encode, targets, hbase]
  have hencode : Set.InjOn encode states := by
    intro sigma _ tau _ heq
    apply directedSide_eq_of_base_direction
    · exact congrArg Prod.fst heq
    · have hcode := congrArg Prod.snd heq
      cases hsigma : sigma.direction <;>
        cases htau : tau.direction <;>
          simp [encode, sideCode, hsigma, htau] at hcode ⊢
  have htargetsFinite : targets.Finite := by
    dsimp [targets]
    exact X.points.finite_toSet.prod Set.finite_univ
  have hstatesFinite : states.Finite :=
    Set.Finite.of_injOn hmaps hencode htargetsFinite
  have hcard : states.ncard ≤ 2 * X.points.card := by
    have hle := Set.ncard_le_ncard_of_injOn encode hmaps hencode htargetsFinite
    simpa [targets, Set.ncard_prod, Nat.mul_comm] using hle
  have hPproduct : Function.Commute C.P C.product := by
    intro x
    change C.P (C.P (C.Q x)) = C.P (C.Q (C.P x))
    exact congrArg C.P (C.commute x)
  have hQproduct : Function.Commute C.Q C.product := by
    intro x
    change C.Q (C.P (C.Q x)) = C.P (C.Q (C.Q x))
    exact (C.commute (C.Q x)).symm
  have hQP : C.Q ∘ C.P = C.product := by
    funext x
    exact (C.commute x).symm
  have hPQ : C.P ∘ C.Q = C.product := rfl
  let State := {sigma : DirectedSide // sigma ∈ states}
  let pImage (sigma : State) :
      ConstantSlopeSideImage C.P sigma.1 C.scale_P :=
    Classical.choose (constantSlope_maps_repellingSide
      C.constantSlope_P (lt_trans zero_lt_one C.one_lt_scale_P)
      sigma.2 hPproduct hQP)
  have pImage_spec (sigma : State) :
      HasPositiveDilationGerm C.product (pImage sigma).target
          (C.scale_P * C.scale_Q) ∧
        CarriesDirectedSide C.Q (pImage sigma).target sigma.1 :=
    Classical.choose_spec (constantSlope_maps_repellingSide
      C.constantSlope_P (lt_trans zero_lt_one C.one_lt_scale_P)
      sigma.2 hPproduct hQP)
  let qImage (sigma : State) :
      ConstantSlopeSideImage C.Q sigma.1 C.scale_Q :=
    Classical.choose (constantSlope_maps_repellingSide
      C.constantSlope_Q (lt_trans zero_lt_one C.one_lt_scale_Q)
      sigma.2 hQproduct hPQ)
  have qImage_spec (sigma : State) :
      HasPositiveDilationGerm C.product (qImage sigma).target
          (C.scale_P * C.scale_Q) ∧
        CarriesDirectedSide C.P (qImage sigma).target sigma.1 :=
    Classical.choose_spec (constantSlope_maps_repellingSide
      C.constantSlope_Q (lt_trans zero_lt_one C.one_lt_scale_Q)
      sigma.2 hQproduct hPQ)
  let pMap : State → State := fun sigma =>
    ⟨(pImage sigma).target, (pImage_spec sigma).1⟩
  let qMap : State → State := fun sigma =>
    ⟨(qImage sigma).target, (qImage_spec sigma).1⟩
  have hq_p : ∀ sigma : State, qMap (pMap sigma) = sigma := by
    intro sigma
    apply Subtype.ext
    have hunique := (qImage (pMap sigma)).target_eq_of_carries
      (lt_trans zero_lt_one C.one_lt_scale_Q) (pImage_spec sigma).2
    exact hunique.symm
  have hp_q : ∀ sigma : State, pMap (qMap sigma) = sigma := by
    intro sigma
    apply Subtype.ext
    have hunique := (pImage (qMap sigma)).target_eq_of_carries
      (lt_trans zero_lt_one C.one_lt_scale_P) (qImage_spec sigma).2
    exact hunique.symm
  let actionP : Equiv.Perm State :=
    { toFun := pMap
      invFun := qMap
      left_inv := hq_p
      right_inv := hp_q }
  let actionQ : Equiv.Perm State := actionP.symm
  refine ⟨{
    states := states
    states_finite := hstatesFinite
    chosen_mem := G.product_repelling
    base_mem := ?_
    repelling := ?_
    card_le := hcard
    actionP := actionP
    actionQ := actionQ
    actionP_carries := ?_
    actionQ_carries := ?_
    actionQ_actionP := ?_
    actionP_actionQ := ?_ }⟩
  · intro sigma hsigma
    exact (X.mem_points sigma.base).mpr hsigma.1
  · intro sigma hsigma
    exact hsigma
  · intro sigma
    exact (pImage sigma).carries
  · intro sigma
    exact (qImage sigma).carries
  · intro sigma
    exact hq_p sigma
  · intro sigma
    exact hp_q sigma

/-- The generator actions on repelling sides are finite mutually inverse
permutations, with at most two states over each fixed point. -/
theorem repellingSideActionData_exists
    {C : NormalizedConstantSlopeCounterexample} {bound : ℕ}
    {X : ProductFixedSetPackage C bound}
    (G : RepellingGapData C bound X) :
    Nonempty (RepellingSideActionData C bound X G) := by
  exact finiteRepellingSidePermutation_exists G

/-- The returned first generator. -/
def returnedP (C : NormalizedConstantSlopeCounterexample) (L : ℕ) :
    IntervalMap :=
  iterateMap C.P L

/-- The returned second generator. -/
def returnedQ (C : NormalizedConstantSlopeCounterexample) (L : ℕ) :
    IntervalMap :=
  iterateMap C.Q L

/-- The product of the returned generators. -/
def returnedProduct (C : NormalizedConstantSlopeCounterexample) (L : ℕ) :
    IntervalMap :=
  returnedP C L ∘ returnedQ C L

/-- The returned slope magnitude of the first generator. -/
def returnedScaleP (C : NormalizedConstantSlopeCounterexample) (L : ℕ) : ℝ :=
  C.scale_P ^ L

/-- The returned slope magnitude of the second generator. -/
def returnedScaleQ (C : NormalizedConstantSlopeCounterexample) (L : ℕ) : ℝ :=
  C.scale_Q ^ L

/-- The returned product slope. -/
def returnedProductScale
    (C : NormalizedConstantSlopeCounterexample) (L : ℕ) : ℝ :=
  returnedScaleP C L * returnedScaleQ C L

/-- The cardinal bound forces the factorial return exponent to kill both
finite side permutations. -/
private theorem repellingSideActions_factorial_eq_one
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (A : RepellingSideActionData C bound X G)
    (hL : L = Nat.factorial (2 * bound)) :
    A.actionP ^ L = 1 ∧ A.actionQ ^ L = 1 := by
  letI : Finite {sigma : DirectedSide // sigma ∈ A.states} :=
    Set.finite_coe_iff.mpr A.states_finite
  have hstateCard :
      Nat.card {sigma : DirectedSide // sigma ∈ A.states} ≤ 2 * bound := by
    rw [Nat.card_coe_set_eq]
    exact A.card_le.trans (Nat.mul_le_mul_left 2 X.card_le_bound)
  have hfactorialDvd :
      Nat.factorial (Nat.card {sigma : DirectedSide // sigma ∈ A.states}) ∣
        Nat.factorial (2 * bound) :=
    Nat.factorial_dvd_factorial hstateCard
  have hkill (e : Equiv.Perm
      {sigma : DirectedSide // sigma ∈ A.states}) :
      e ^ Nat.factorial (2 * bound) = 1 := by
    have hsmall :
        e ^ Nat.factorial
            (Nat.card {sigma : DirectedSide // sigma ∈ A.states}) = 1 := by
      simpa [Nat.card_perm] using (pow_card_eq_one' (x := e))
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_pow_eq_one hsmall).trans hfactorialDvd)
  rw [hL]
  exact ⟨hkill A.actionP, hkill A.actionQ⟩

/-- A positive constant-slope map that returns a directed side to itself has
the positive (rather than reflected) one-sided affine germ there. -/
private theorem positiveDilationGerm_of_constantSlope_selfCarry
    {T : IntervalMap} {sigma : DirectedSide} {s : ℝ}
    (hT : HasConstantAbsoluteSlope T s) (hs : 0 < s)
    (hcarry : CarriesDirectedSide T sigma sigma) :
    HasPositiveDilationGerm T sigma s := by
  obtain ⟨g⟩ := oneSidedAffineGerm_exists hT sigma
  rcases hcarry with ⟨hfixed, epsilonCarry, hepsilonCarry, hlocal⟩
  let epsilon : ℝ := min g.radius epsilonCarry
  have hepsilon : 0 < epsilon := lt_min g.radius_pos hepsilonCarry
  obtain ⟨q, hqpunctured, hqnear⟩ :=
    sigma.exists_punctured_point_below hepsilon
  have hqray : q ∈ sigma.direction.closedRay sigma.base :=
    mem_closedRay_of_mem_puncturedRay hqpunctured
  have hqGerm : |(q : ℝ) - (sigma.base : ℝ)| < g.radius :=
    hqnear.trans_le (min_le_left _ _)
  have hqCarry : |(q : ℝ) - (sigma.base : ℝ)| < epsilonCarry :=
    hqnear.trans_le (min_le_right _ _)
  have hTqray : T q ∈ sigma.direction.closedRay sigma.base :=
    hlocal q hqray hqCarry
  have hbaseRay : sigma.base ∈
      sigma.direction.closedRay sigma.base := by
    rw [mem_closedRay_iff_deltaAlong]
    cases sigma.direction <;> simp [DeltaAlongSide]
  have hqFormula := g.formula q hqray hqGerm
  have hbaseFormula := g.formula sigma.base hbaseRay (by
    simpa using g.radius_pos)
  have hfixedReal : (T sigma.base : ℝ) = (sigma.base : ℝ) :=
    congrArg Subtype.val hfixed
  have hrelation :
      (T q : ℝ) - (sigma.base : ℝ) =
        g.slope * ((q : ℝ) - (sigma.base : ℝ)) := by
    linarith
  have hslope_ne : g.slope ≠ 0 := by
    intro hslope
    have habs := g.abs_slope
    rw [hslope, abs_zero] at habs
    linarith
  have hslope_pos : 0 < g.slope := by
    cases hdirection : sigma.direction with
    | left =>
        have hsource : (q : ℝ) - (sigma.base : ℝ) < 0 := by
          exact (mem_puncturedRay_iff_deltaAlong_strict
            Side.left sigma.base q).mp (by
              simpa [hdirection] using hqpunctured)
        have himage : (T q : ℝ) - (sigma.base : ℝ) ≤ 0 := by
          simpa [hdirection, Side.closedRay, sub_nonpos] using hTqray
        by_contra hnot
        have hslope_nonpos : g.slope ≤ 0 := le_of_not_gt hnot
        have hslope_neg : g.slope < 0 :=
          lt_of_le_of_ne hslope_nonpos hslope_ne
        have hproduct : 0 <
            g.slope * ((q : ℝ) - (sigma.base : ℝ)) :=
          mul_pos_of_neg_of_neg hslope_neg hsource
        nlinarith
    | right =>
        have hsource : 0 < (q : ℝ) - (sigma.base : ℝ) := by
          exact (mem_puncturedRay_iff_deltaAlong_strict
            Side.right sigma.base q).mp (by
              simpa [hdirection] using hqpunctured)
        have himage : 0 ≤ (T q : ℝ) - (sigma.base : ℝ) := by
          simpa [hdirection, Side.closedRay, sub_nonneg] using hTqray
        by_contra hnot
        have hslope_nonpos : g.slope ≤ 0 := le_of_not_gt hnot
        have hslope_neg : g.slope < 0 :=
          lt_of_le_of_ne hslope_nonpos hslope_ne
        have hproduct :
            g.slope * ((q : ℝ) - (sigma.base : ℝ)) < 0 :=
          mul_neg_of_neg_of_pos hslope_neg hsource
        nlinarith
  have hslope_eq : g.slope = s := by
    simpa [abs_of_pos hslope_pos] using g.abs_slope
  refine ⟨hfixed, hs, epsilon, hepsilon, ?_⟩
  intro x hxray hxnear
  have hxGerm : |(x : ℝ) - (sigma.base : ℝ)| < g.radius :=
    hxnear.trans_le (min_le_left _ _)
  have hxCarry : |(x : ℝ) - (sigma.base : ℝ)| < epsilonCarry :=
    hxnear.trans_le (min_le_right _ _)
  have hxFormula := g.formula x hxray hxGerm
  refine ⟨hlocal x hxray hxCarry, ?_⟩
  rw [hslope_eq] at hxFormula
  rw [hslope_eq] at hbaseFormula
  linarith

private theorem CarriesDirectedSide.comp
    {T U : IntervalMap} {sigma tau upsilon : DirectedSide}
    (hTcontinuous : Continuous T)
    (hT : CarriesDirectedSide T sigma tau)
    (hU : CarriesDirectedSide U tau upsilon) :
    CarriesDirectedSide (U ∘ T) sigma upsilon := by
  rcases hT with ⟨hTbase, epsilonT, hepsilonT, hTlocal⟩
  rcases hU with ⟨hUbase, epsilonU, hepsilonU, hUlocal⟩
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    Metric.continuousAt_iff.mp hTcontinuous.continuousAt epsilonU hepsilonU
  let epsilon : ℝ := min epsilonT delta
  have hepsilon : 0 < epsilon := lt_min hepsilonT hdelta
  refine ⟨?_, epsilon, hepsilon, ?_⟩
  · change U (T sigma.base) = upsilon.base
    rw [hTbase, hUbase]
  · intro x hxray hxnear
    have hxT : |(x : ℝ) - (sigma.base : ℝ)| < epsilonT :=
      hxnear.trans_le (min_le_left _ _)
    have hxDelta : dist x sigma.base < delta := by
      simpa [Real.dist_eq] using hxnear.trans_le (min_le_right _ _)
    have hTxNearDist : dist (T x) (T sigma.base) < epsilonU :=
      hcontrol hxDelta
    have hTxNear : |(T x : ℝ) - (tau.base : ℝ)| < epsilonU := by
      rw [← hTbase]
      simpa [Real.dist_eq] using hTxNearDist
    exact hUlocal (T x) (hTlocal x hxray hxT) hTxNear

private theorem carriesDirectedSide_iterate_action
    {T : IntervalMap} {states : Set DirectedSide}
    (hTcontinuous : Continuous T)
    (action : Equiv.Perm {sigma : DirectedSide // sigma ∈ states})
    (hcarries : ∀ sigma,
      CarriesDirectedSide T sigma.1 (action sigma).1)
    (n : ℕ) (sigma : {sigma : DirectedSide // sigma ∈ states}) :
    CarriesDirectedSide (iterateMap T n) sigma.1 ((action ^ n) sigma).1 := by
  induction n with
  | zero =>
      refine ⟨rfl, 1, zero_lt_one, ?_⟩
      intro x hxray _hxnear
      simpa [iterateMap] using hxray
  | succ n ih =>
      have hcomp := CarriesDirectedSide.comp
        (IntervalMap.continuous_iterate hTcontinuous n) ih
        (hcarries ((action ^ n) sigma))
      have hmap : iterateMap T (n + 1) = T ∘ iterateMap T n := by
        funext x
        exact Function.iterate_succ_apply' T n x
      have htarget :
          ((action ^ (n + 1)) sigma).1 =
            (action ((action ^ n) sigma)).1 := by
        rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
        exact congrArg Subtype.val (Function.iterate_succ_apply' action n sigma)
      rw [hmap, htarget]
      exact hcomp

/-- Algebraic and PL properties of the two returned generators. -/
structure ReturnedSystemProperties
    (C : NormalizedConstantSlopeCounterexample) (L : ℕ) where
  L_pos : 0 < L
  commute : Function.Commute (returnedP C L) (returnedQ C L)
  finitePiece_A : FinitePiecePL (returnedP C L)
  finitePiece_B : FinitePiecePL (returnedQ C L)
  onto_A : IsOnto (returnedP C L)
  onto_B : IsOnto (returnedQ C L)
  constantSlope_A :
    HasConstantAbsoluteSlope (returnedP C L) (returnedScaleP C L)
  constantSlope_B :
    HasConstantAbsoluteSlope (returnedQ C L) (returnedScaleQ C L)
  one_lt_a : 1 < returnedScaleP C L
  one_lt_b : 1 < returnedScaleQ C L

/-- The factorial returns fix the selected right-directed state and have
simultaneous positive affine germs on a common neighborhood. -/
structure FactorialReturnGermData
    (C : NormalizedConstantSlopeCounterexample) (bound L : ℕ)
    (X : ProductFixedSetPackage C bound)
    (G : RepellingGapData C bound X) where
  properties : ReturnedSystemProperties C L
  sideAction : RepellingSideActionData C bound X G
  fixed_side_A : CarriesDirectedSide (returnedP C L) G.side G.side
  fixed_side_B : CarriesDirectedSide (returnedQ C L) G.side G.side
  positive_germ_A : HasPositiveDilationGerm
    (returnedP C L) G.side (returnedScaleP C L)
  positive_germ_B : HasPositiveDilationGerm
    (returnedQ C L) G.side (returnedScaleQ C L)
  germ_radius : ℝ
  germ_radius_pos : 0 < germ_radius
  germ_fits :
    (G.p : ℝ) + returnedProductScale C L * germ_radius ≤ 1
  germ_A : ∀ t : ℝ,
    0 ≤ t → t ≤ returnedProductScale C L * germ_radius →
      ∀ x : I, (x : ℝ) = (G.p : ℝ) + t →
        (returnedP C L x : ℝ) =
          (G.p : ℝ) + returnedScaleP C L * t
  germ_B : ∀ t : ℝ,
    0 ≤ t → t ≤ returnedProductScale C L * germ_radius →
      ∀ x : I, (x : ℝ) = (G.p : ℝ) + t →
        (returnedQ C L x : ℝ) =
          (G.p : ℝ) + returnedScaleQ C L * t
  germ_product : ∀ t : ℝ,
    0 ≤ t → t ≤ germ_radius →
      ∀ x : I, (x : ℝ) = (G.p : ℝ) + t →
        (returnedProduct C L x : ℝ) =
          (G.p : ℝ) + returnedProductScale C L * t

/-- The factorial bound fixes every repelling state and yields the common
positive return germs. -/
theorem factorialReturnGermData_exists
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    (G : RepellingGapData C bound X)
    (hL : L = Nat.factorial (2 * bound)) :
    Nonempty (FactorialReturnGermData C bound L X G) := by
  obtain ⟨sideAction⟩ := finiteRepellingSidePermutation_exists G
  have hfactorial := repellingSideActions_factorial_eq_one sideAction hL
  have hLpos : 0 < L := by
    rw [hL]
    exact Nat.factorial_pos _
  have hscalePpos : 0 < C.scale_P :=
    lt_trans zero_lt_one C.one_lt_scale_P
  have hscaleQpos : 0 < C.scale_Q :=
    lt_trans zero_lt_one C.one_lt_scale_Q
  have hconstantA :
      HasConstantAbsoluteSlope (returnedP C L) (returnedScaleP C L) := by
    simpa [returnedP, returnedScaleP] using
      C.constantSlope_P.iterateMap hscalePpos L
  have hconstantB :
      HasConstantAbsoluteSlope (returnedQ C L) (returnedScaleQ C L) := by
    simpa [returnedQ, returnedScaleQ] using
      C.constantSlope_Q.iterateMap hscaleQpos L
  have honeA : 1 < returnedScaleP C L := by
    exact one_lt_pow₀ C.one_lt_scale_P (Nat.ne_of_gt hLpos)
  have honeB : 1 < returnedScaleQ C L := by
    exact one_lt_pow₀ C.one_lt_scale_Q (Nat.ne_of_gt hLpos)
  let properties : ReturnedSystemProperties C L :=
    { L_pos := hLpos
      commute := by
        simpa [returnedP, returnedQ, iterateMap] using
          IntervalMap.commute_iterates C.commute L L
      finitePiece_A := hconstantA.finitePiecePL
      finitePiece_B := hconstantB.finitePiecePL
      onto_A := by
        simpa [returnedP, iterateMap] using
          IntervalMap.surjective_iterate C.onto_P L
      onto_B := by
        simpa [returnedQ, iterateMap] using
          IntervalMap.surjective_iterate C.onto_Q L
      constantSlope_A := hconstantA
      constantSlope_B := hconstantB
      one_lt_a := honeA
      one_lt_b := honeB }
  let chosen : {sigma : DirectedSide // sigma ∈ sideAction.states} :=
    ⟨G.side, sideAction.chosen_mem⟩
  have hcarryA0 := carriesDirectedSide_iterate_action
    C.constantSlope_P.continuous sideAction.actionP
    sideAction.actionP_carries L chosen
  have hcarryB0 := carriesDirectedSide_iterate_action
    C.constantSlope_Q.continuous sideAction.actionQ
    sideAction.actionQ_carries L chosen
  have hactionA : (sideAction.actionP ^ L) chosen = chosen := by
    rw [hfactorial.1]
    rfl
  have hactionB : (sideAction.actionQ ^ L) chosen = chosen := by
    rw [hfactorial.2]
    rfl
  have hfixedSideA :
      CarriesDirectedSide (returnedP C L) G.side G.side := by
    rw [hactionA] at hcarryA0
    simpa [returnedP, chosen] using hcarryA0
  have hfixedSideB :
      CarriesDirectedSide (returnedQ C L) G.side G.side := by
    rw [hactionB] at hcarryB0
    simpa [returnedQ, chosen] using hcarryB0
  have hreturnedScalePpos : 0 < returnedScaleP C L :=
    pow_pos hscalePpos L
  have hreturnedScaleQpos : 0 < returnedScaleQ C L :=
    pow_pos hscaleQpos L
  have hpositiveA : HasPositiveDilationGerm
      (returnedP C L) G.side (returnedScaleP C L) :=
    positiveDilationGerm_of_constantSlope_selfCarry
      hconstantA hreturnedScalePpos hfixedSideA
  have hpositiveB : HasPositiveDilationGerm
      (returnedQ C L) G.side (returnedScaleQ C L) :=
    positiveDilationGerm_of_constantSlope_selfCarry
      hconstantB hreturnedScaleQpos hfixedSideB
  have hpositiveA_spec := hpositiveA
  have hpositiveB_spec := hpositiveB
  rcases hpositiveA_spec with
    ⟨_hfixA, _hscaleA, epsilonA, hepsilonA, hlocalA⟩
  rcases hpositiveB_spec with
    ⟨_hfixB, _hscaleB, epsilonB, hepsilonB, hlocalB⟩
  have hp_lt_one : (G.p : ℝ) < 1 :=
    (show (G.p : ℝ) < (G.c : ℝ) from G.consecutive.2.2.1).trans_le
      G.c.property.2
  let productScale : ℝ := returnedProductScale C L
  have hproductScalePos : 0 < productScale := by
    exact mul_pos hreturnedScalePpos hreturnedScaleQpos
  let margin : ℝ := min epsilonA (min epsilonB (1 - (G.p : ℝ)))
  have hmarginPos : 0 < margin := by
    exact lt_min hepsilonA (lt_min hepsilonB (sub_pos.mpr hp_lt_one))
  let radius : ℝ := margin / (2 * productScale)
  have hradiusPos : 0 < radius := by
    exact div_pos hmarginPos (mul_pos (by norm_num) hproductScalePos)
  have hproductRadius : productScale * radius = margin / 2 := by
    dsimp [radius]
    field_simp [ne_of_gt hproductScalePos]
  have hproductRadius_lt_margin : productScale * radius < margin := by
    rw [hproductRadius]
    linarith
  have hproductRadius_lt_A : productScale * radius < epsilonA :=
    hproductRadius_lt_margin.trans_le (min_le_left _ _)
  have hproductRadius_lt_B : productScale * radius < epsilonB :=
    hproductRadius_lt_margin.trans_le
      (min_le_right _ _ |>.trans (min_le_left _ _))
  have hproductRadius_le_boundary :
      productScale * radius ≤ 1 - (G.p : ℝ) :=
    hproductRadius_lt_margin.le.trans
      (min_le_right _ _ |>.trans (min_le_right _ _))
  have hgermFits :
      (G.p : ℝ) + returnedProductScale C L * radius ≤ 1 := by
    change (G.p : ℝ) + productScale * radius ≤ 1
    linarith
  have hgermA : ∀ t : ℝ,
      0 ≤ t → t ≤ returnedProductScale C L * radius →
        ∀ x : I, (x : ℝ) = (G.p : ℝ) + t →
          (returnedP C L x : ℝ) =
            (G.p : ℝ) + returnedScaleP C L * t := by
    intro t ht htbound x hx
    have htbound' : t ≤ productScale * radius := by
      simpa [productScale] using htbound
    have htEpsilon : t < epsilonA :=
      htbound'.trans_lt hproductRadius_lt_A
    have hxray : x ∈ G.side.direction.closedRay G.side.base := by
      rw [G.side_direction, G.side_base, Side.closedRay]
      change (G.p : ℝ) ≤ (x : ℝ)
      rw [hx]
      linarith
    have hxnear : |(x : ℝ) - (G.side.base : ℝ)| < epsilonA := by
      rw [G.side_base, hx, add_sub_cancel_left, abs_of_nonneg ht]
      exact htEpsilon
    obtain ⟨_himage, heq⟩ := hlocalA x hxray hxnear
    rw [G.side_base, hx] at heq
    linarith
  have hgermB : ∀ t : ℝ,
      0 ≤ t → t ≤ returnedProductScale C L * radius →
        ∀ x : I, (x : ℝ) = (G.p : ℝ) + t →
          (returnedQ C L x : ℝ) =
            (G.p : ℝ) + returnedScaleQ C L * t := by
    intro t ht htbound x hx
    have htbound' : t ≤ productScale * radius := by
      simpa [productScale] using htbound
    have htEpsilon : t < epsilonB :=
      htbound'.trans_lt hproductRadius_lt_B
    have hxray : x ∈ G.side.direction.closedRay G.side.base := by
      rw [G.side_direction, G.side_base, Side.closedRay]
      change (G.p : ℝ) ≤ (x : ℝ)
      rw [hx]
      linarith
    have hxnear : |(x : ℝ) - (G.side.base : ℝ)| < epsilonB := by
      rw [G.side_base, hx, add_sub_cancel_left, abs_of_nonneg ht]
      exact htEpsilon
    obtain ⟨_himage, heq⟩ := hlocalB x hxray hxnear
    rw [G.side_base, hx] at heq
    linarith
  have hproductScaleOne : 1 < productScale := by
    dsimp [productScale, returnedProductScale]
    calc
      1 < returnedScaleP C L := honeA
      _ ≤ returnedScaleP C L * returnedScaleQ C L := by
        nlinarith [hreturnedScalePpos, hreturnedScaleQpos, honeB]
  have hgermProduct : ∀ t : ℝ,
      0 ≤ t → t ≤ radius →
        ∀ x : I, (x : ℝ) = (G.p : ℝ) + t →
          (returnedProduct C L x : ℝ) =
            (G.p : ℝ) + returnedProductScale C L * t := by
    intro t ht htradius x hx
    have htProduct : t ≤ returnedProductScale C L * radius := by
      change t ≤ productScale * radius
      have hradiusGrowth : radius ≤ productScale * radius := by
        simpa using
          (mul_le_mul_of_nonneg_right hproductScaleOne.le hradiusPos.le)
      exact htradius.trans hradiusGrowth
    have hBx := hgermB t ht htProduct x hx
    have hbt : 0 ≤ returnedScaleQ C L * t :=
      mul_nonneg hreturnedScaleQpos.le ht
    have hb_le_ab : returnedScaleQ C L ≤ productScale := by
      dsimp [productScale, returnedProductScale]
      nlinarith [hreturnedScalePpos, hreturnedScaleQpos, honeA]
    have hbtProduct :
        returnedScaleQ C L * t ≤ returnedProductScale C L * radius := by
      change returnedScaleQ C L * t ≤ productScale * radius
      calc
        returnedScaleQ C L * t ≤ returnedScaleQ C L * radius :=
          mul_le_mul_of_nonneg_left htradius hreturnedScaleQpos.le
        _ ≤ productScale * radius :=
          mul_le_mul_of_nonneg_right hb_le_ab hradiusPos.le
    have hAB := hgermA (returnedScaleQ C L * t) hbt hbtProduct
      (returnedQ C L x) hBx
    simpa [returnedProduct, returnedProductScale, Function.comp_apply,
      mul_assoc] using hAB
  refine ⟨{
    properties := properties
    sideAction := sideAction
    fixed_side_A := hfixedSideA
    fixed_side_B := hfixedSideB
    positive_germ_A := hpositiveA
    positive_germ_B := hpositiveB
    germ_radius := radius
    germ_radius_pos := hradiusPos
    germ_fits := hgermFits
    germ_A := hgermA
    germ_B := hgermB
    germ_product := hgermProduct }⟩

/-! ## F4: nested returned intervals and the stabilized ray -/

/-- The small right-hand seed interval based at the repelling fixed point. -/
def initialRaySegment
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) : Set I :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) F.germ_radius,
    (x : ℝ) = (G.p : ℝ) + t}

/-- The `n`th image of the seed interval under the returned product. -/
def returnedInterval
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) (n : ℕ) : Set I :=
  iterateMap (returnedProduct C L) n '' initialRaySegment F

/-- The purely dynamical part of the expanding returned-interval family,
before taking its closed interval hull. -/
private structure ReturnedIntervalDynamicsData
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) where
  nested : ∀ n : ℕ, returnedInterval F n ⊆ returnedInterval F (n + 1)
  product_image : ∀ n : ℕ,
    returnedProduct C L '' returnedInterval F n = returnedInterval F (n + 1)
  A_forward : ∀ n : ℕ,
    returnedP C L '' returnedInterval F n ⊆ returnedInterval F (n + 1)
  B_forward : ∀ n : ℕ,
    returnedQ C L '' returnedInterval F n ⊆ returnedInterval F (n + 1)

/-- The local three dilation germs imply nesting and the three one-step
image relations for every returned interval. -/
private theorem returnedIntervalDynamicsData_exists
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) :
    Nonempty (ReturnedIntervalDynamicsData F) := by
  let R : IntervalMap := returnedProduct C L
  let A : IntervalMap := returnedP C L
  let B : IntervalMap := returnedQ C L
  let s : ℝ := returnedProductScale C L
  let a : ℝ := returnedScaleP C L
  let b : ℝ := returnedScaleQ C L
  have ha : 1 < a := F.properties.one_lt_a
  have hb : 1 < b := F.properties.one_lt_b
  have haPos : 0 < a := zero_lt_one.trans ha
  have hbPos : 0 < b := zero_lt_one.trans hb
  have hs : 1 < s := by
    dsimp [s, returnedProductScale]
    nlinarith [haPos, hbPos, ha, hb]
  have hsPos : 0 < s := zero_lt_one.trans hs
  let expanded : Set I :=
    {x | ∃ t ∈ Set.Icc (0 : ℝ) (s * F.germ_radius),
      (x : ℝ) = (G.p : ℝ) + t}
  have hseed_product : R '' initialRaySegment F = expanded := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, ⟨t, ht, hxt⟩, rfl⟩
      refine ⟨s * t, ⟨mul_nonneg hsPos.le ht.1,
        mul_le_mul_of_nonneg_left ht.2 hsPos.le⟩, ?_⟩
      exact F.germ_product t ht.1 ht.2 x hxt
    · rintro y ⟨u, hu, hyu⟩
      let t : ℝ := u / s
      have ht0 : 0 ≤ t := div_nonneg hu.1 hsPos.le
      have htepsilon : t ≤ F.germ_radius := by
        exact (div_le_iff₀ hsPos).2 (by simpa [mul_comm] using hu.2)
      have htx0 : 0 ≤ (G.p : ℝ) + t :=
        add_nonneg G.p.property.1 ht0
      have ht_le_scaled : t ≤ s * F.germ_radius := by
        have hgrowth : F.germ_radius ≤ s * F.germ_radius := by
          simpa using
            (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
        exact htepsilon.trans hgrowth
      have htx1 : (G.p : ℝ) + t ≤ 1 := by
        calc
          (G.p : ℝ) + t ≤ (G.p : ℝ) + s * F.germ_radius :=
            by simpa [add_comm] using
              (add_le_add_left ht_le_scaled (G.p : ℝ))
          _ ≤ 1 := by simpa [s] using F.germ_fits
      let x : I := ⟨(G.p : ℝ) + t, htx0, htx1⟩
      refine ⟨x, ⟨t, ⟨ht0, htepsilon⟩, rfl⟩, ?_⟩
      apply Subtype.ext
      have hR := F.germ_product t ht0 htepsilon x rfl
      change (R x : ℝ) = (G.p : ℝ) + s * t at hR
      rw [hR, hyu]
      dsimp [t]
      field_simp [hsPos.ne']
  have hseed_nested : initialRaySegment F ⊆ R '' initialRaySegment F := by
    rw [hseed_product]
    rintro x ⟨t, ht, hxt⟩
    refine ⟨t, ⟨ht.1, ?_⟩, hxt⟩
    have hgrowth : F.germ_radius ≤ s * F.germ_radius := by
      simpa using
        (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
    exact ht.2.trans hgrowth
  have ha_le_s : a ≤ s := by
    dsimp [a, s, returnedProductScale]
    nlinarith [haPos, hbPos, hb]
  have hb_le_s : b ≤ s := by
    dsimp [b, s, returnedProductScale]
    nlinarith [haPos, hbPos, ha]
  have hseed_A : A '' initialRaySegment F ⊆ R '' initialRaySegment F := by
    rw [hseed_product]
    rintro y ⟨x, ⟨t, ht, hxt⟩, rfl⟩
    have htScaled : t ≤ returnedProductScale C L * F.germ_radius := by
      change t ≤ s * F.germ_radius
      have hgrowth : F.germ_radius ≤ s * F.germ_radius := by
        simpa using
          (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
      exact ht.2.trans hgrowth
    refine ⟨a * t, ⟨mul_nonneg haPos.le ht.1, ?_⟩, ?_⟩
    · exact (mul_le_mul_of_nonneg_left ht.2 haPos.le).trans
        (mul_le_mul_of_nonneg_right ha_le_s F.germ_radius_pos.le)
    · exact F.germ_A t ht.1 htScaled x hxt
  have hseed_B : B '' initialRaySegment F ⊆ R '' initialRaySegment F := by
    rw [hseed_product]
    rintro y ⟨x, ⟨t, ht, hxt⟩, rfl⟩
    have htScaled : t ≤ returnedProductScale C L * F.germ_radius := by
      change t ≤ s * F.germ_radius
      have hgrowth : F.germ_radius ≤ s * F.germ_radius := by
        simpa using
          (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
      exact ht.2.trans hgrowth
    refine ⟨b * t, ⟨mul_nonneg hbPos.le ht.1, ?_⟩, ?_⟩
    · exact (mul_le_mul_of_nonneg_left ht.2 hbPos.le).trans
        (mul_le_mul_of_nonneg_right hb_le_s F.germ_radius_pos.le)
    · exact F.germ_B t ht.1 htScaled x hxt
  have hAR : Function.Commute A R := by
    intro x
    dsimp [A, R, returnedProduct]
    change returnedP C L (returnedP C L (returnedQ C L x)) =
      returnedP C L (returnedQ C L (returnedP C L x))
    exact congrArg (returnedP C L) (F.properties.commute x)
  have hBR : Function.Commute B R := by
    intro x
    dsimp [B, R, returnedProduct]
    change returnedQ C L (returnedP C L (returnedQ C L x)) =
      returnedP C L (returnedQ C L (returnedQ C L x))
    exact (F.properties.commute (returnedQ C L x)).symm
  have hproductImage (n : ℕ) :
      R '' returnedInterval F n = returnedInterval F (n + 1) := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, hx, hzx⟩, hyz⟩
      refine ⟨x, hx, ?_⟩
      subst z
      subst y
      exact Function.iterate_succ_apply' R n x
    · rintro ⟨x, hx, hyx⟩
      refine ⟨iterateMap R n x, ⟨x, hx, rfl⟩, ?_⟩
      rw [← hyx]
      exact (Function.iterate_succ_apply' R n x).symm
  have hnested (n : ℕ) :
      returnedInterval F n ⊆ returnedInterval F (n + 1) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := hseed_nested hx
    refine ⟨z, hz, ?_⟩
    rw [← hxz]
    calc
      iterateMap R n (R z) = R (iterateMap R n z) :=
        (Function.Commute.self_iterate R n z).symm
      _ = iterateMap R (n + 1) z :=
        (Function.iterate_succ_apply' R n z).symm
  have hAForward (n : ℕ) :
      A '' returnedInterval F n ⊆ returnedInterval F (n + 1) := by
    rintro y ⟨x, ⟨z, hz, hxz⟩, hyx⟩
    obtain ⟨w, hw, hAw⟩ := hseed_A ⟨z, hz, rfl⟩
    refine ⟨w, hw, ?_⟩
    subst x
    subst y
    change iterateMap R (n + 1) w = A (iterateMap R n z)
    calc
      iterateMap R (n + 1) w = R (iterateMap R n w) :=
        Function.iterate_succ_apply' R n w
      _ = iterateMap R n (R w) := Function.Commute.self_iterate R n w
      _ = iterateMap R n (A z) := congrArg (iterateMap R n) hAw
      _ = A (iterateMap R n z) := (hAR.iterate_right n z).symm
  have hBForward (n : ℕ) :
      B '' returnedInterval F n ⊆ returnedInterval F (n + 1) := by
    rintro y ⟨x, ⟨z, hz, hxz⟩, hyx⟩
    obtain ⟨w, hw, hBw⟩ := hseed_B ⟨z, hz, rfl⟩
    refine ⟨w, hw, ?_⟩
    subst x
    subst y
    change iterateMap R (n + 1) w = B (iterateMap R n z)
    calc
      iterateMap R (n + 1) w = R (iterateMap R n w) :=
        Function.iterate_succ_apply' R n w
      _ = iterateMap R n (R w) := Function.Commute.self_iterate R n w
      _ = iterateMap R n (B z) := congrArg (iterateMap R n) hBw
      _ = B (iterateMap R n z) := (hBR.iterate_right n z).symm
  exact ⟨{
    nested := hnested
    product_image := hproductImage
    A_forward := hAForward
    B_forward := hBForward }⟩

/-- The closure of the increasing returned-interval union is a
nondegenerate closed subinterval carried onto itself by both returns. -/
private theorem returnedIntervalHull_exists
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    (D : ReturnedIntervalDynamicsData F) :
    ∃ hull : ClosedSubinterval,
      hull.carrier = closure (⋃ n : ℕ, returnedInterval F n) ∧
      hull.Nondegenerate ∧
      MapsOntoSubinterval (returnedP C L) hull ∧
      MapsOntoSubinterval (returnedQ C L) hull := by
  let A : IntervalMap := returnedP C L
  let B : IntervalMap := returnedQ C L
  let R : IntervalMap := returnedProduct C L
  let U : Set I := ⋃ n : ℕ, returnedInterval F n
  let K : Set I := closure U
  let s : ℝ := returnedProductScale C L
  have ha : 1 < returnedScaleP C L := F.properties.one_lt_a
  have hb : 1 < returnedScaleQ C L := F.properties.one_lt_b
  have haPos : 0 < returnedScaleP C L := zero_lt_one.trans ha
  have hbPos : 0 < returnedScaleQ C L := zero_lt_one.trans hb
  have hs : 1 < s := by
    dsimp [s, returnedProductScale]
    nlinarith
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hRcontinuous : Continuous R := by
    exact F.properties.constantSlope_A.continuous.comp
      F.properties.constantSlope_B.continuous
  have hAcontinuous : Continuous A := F.properties.constantSlope_A.continuous
  have hBcontinuous : Continuous B := F.properties.constantSlope_B.continuous
  have hseedNonempty : (initialRaySegment F).Nonempty := by
    refine ⟨G.p, 0, ⟨le_rfl, F.germ_radius_pos.le⟩, ?_⟩
    simp
  have hintervalNonempty (n : ℕ) : (returnedInterval F n).Nonempty :=
    hseedNonempty.image _
  have hintervalConnected (n : ℕ) : IsConnected (returnedInterval F n) := by
    let q : I :=
      ⟨(G.p : ℝ) + F.germ_radius,
        add_nonneg G.p.property.1 F.germ_radius_pos.le,
        (by
          have hle : F.germ_radius ≤ s * F.germ_radius := by
            simpa using
              (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
          have hfit : (G.p : ℝ) + s * F.germ_radius ≤ 1 := by
            simpa [s] using F.germ_fits
          linarith)⟩
    have hseed : initialRaySegment F = Set.Icc G.p q := by
      ext x
      constructor
      · rintro ⟨t, ht, hxt⟩
        constructor
        · change (G.p : ℝ) ≤ (x : ℝ)
          rw [hxt]
          linarith [ht.1]
        · change (x : ℝ) ≤ (q : I)
          rw [hxt]
          change (G.p : ℝ) + t ≤ (G.p : ℝ) + F.germ_radius
          linarith [ht.2]
      · rintro hx
        refine ⟨(x : ℝ) - (G.p : ℝ), ?_, by linarith⟩
        constructor
        · have hxp : (G.p : ℝ) ≤ (x : ℝ) := hx.1
          linarith
        · have hxq : (x : ℝ) ≤ (q : I) := hx.2
          change (x : ℝ) ≤ (G.p : ℝ) + F.germ_radius at hxq
          linarith
    rw [returnedInterval, hseed]
    exact (isConnected_Icc (show G.p ≤ q by
      change (G.p : ℝ) ≤ (G.p : ℝ) + F.germ_radius
      linarith [F.germ_radius_pos])).image _
      (IntervalMap.continuous_iterate hRcontinuous n).continuousOn
  have hUConnected : IsConnected U := by
    dsimp [U]
    apply IsConnected.iUnion_of_chain hintervalConnected
    intro n
    obtain ⟨x, hx⟩ := hintervalNonempty n
    exact ⟨x, hx, D.nested n hx⟩
  have hUNonempty : U.Nonempty := by
    obtain ⟨x, hx⟩ := hintervalNonempty 0
    exact ⟨x, Set.mem_iUnion.2 ⟨0, hx⟩⟩
  have hKConnected : IsConnected K := by
    exact hUConnected.closure
  have hKClosed : IsClosed K := isClosed_closure
  have hKNonempty : K.Nonempty := hUNonempty.mono subset_closure
  have hKBelow : BddBelow K := by
    refine ⟨leftEndpoint, ?_⟩
    intro x _
    exact x.property.1
  have hKAbove : BddAbove K := by
    refine ⟨rightEndpoint, ?_⟩
    intro x _
    exact x.property.2
  have hKInterval : K = Set.Icc (sInf K) (sSup K) :=
    eq_Icc_csInf_csSup_of_connected_bdd_closed
      hKConnected hKBelow hKAbove hKClosed
  let hull : ClosedSubinterval :=
    { left := sInf K
      right := sSup K
      left_le_right := csInf_le_csSup hKNonempty hKBelow hKAbove }
  have hhull : hull.carrier = K := by
    dsimp [hull, ClosedSubinterval.carrier]
    exact hKInterval.symm
  have hpSeed : G.p ∈ initialRaySegment F := by
    exact ⟨0, ⟨le_rfl, F.germ_radius_pos.le⟩, by simp⟩
  have hpK : G.p ∈ K := by
    apply subset_closure
    exact Set.mem_iUnion.2 ⟨0, ⟨G.p, hpSeed, rfl⟩⟩
  let q : I :=
    ⟨(G.p : ℝ) + F.germ_radius,
      add_nonneg G.p.property.1 F.germ_radius_pos.le,
      (by
        have hle : F.germ_radius ≤ s * F.germ_radius := by
          simpa using
            (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
        have hfit : (G.p : ℝ) + s * F.germ_radius ≤ 1 := by
          simpa [s] using F.germ_fits
        linarith)⟩
  have hqSeed : q ∈ initialRaySegment F := by
    exact ⟨F.germ_radius, ⟨F.germ_radius_pos.le, le_rfl⟩, rfl⟩
  have hqK : q ∈ K := by
    apply subset_closure
    exact Set.mem_iUnion.2 ⟨0, ⟨q, hqSeed, rfl⟩⟩
  have hnondegenerate : hull.Nondegenerate := by
    have hpBounds : sInf K ≤ G.p ∧ G.p ≤ sSup K := by
      rw [← Set.mem_Icc, ← hKInterval]
      exact hpK
    have hqBounds : sInf K ≤ q ∧ q ≤ sSup K := by
      rw [← Set.mem_Icc, ← hKInterval]
      exact hqK
    dsimp [ClosedSubinterval.Nondegenerate, hull]
    exact lt_of_le_of_lt hpBounds.1
      (lt_of_lt_of_le (by
        change (G.p : ℝ) < (G.p : ℝ) + F.germ_radius
        linarith [F.germ_radius_pos]) hqBounds.2)
  have hA_U : A '' U ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    have hAx : A x ∈ returnedInterval F (n + 1) :=
      D.A_forward n ⟨x, hn, rfl⟩
    exact Set.mem_iUnion.2 ⟨n + 1, hAx⟩
  have hB_U : B '' U ⊆ U := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    have hBx : B x ∈ returnedInterval F (n + 1) :=
      D.B_forward n ⟨x, hn, rfl⟩
    exact Set.mem_iUnion.2 ⟨n + 1, hBx⟩
  have hR_U : R '' U = U := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
      have hRx : R x ∈ returnedInterval F (n + 1) := by
        rw [← D.product_image n]
        exact ⟨x, hn, rfl⟩
      exact Set.mem_iUnion.2 ⟨n + 1, hRx⟩
    · intro y hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
      cases n with
      | zero =>
          have hy1 : y ∈ returnedInterval F 1 := D.nested 0 hn
          rw [← D.product_image 0] at hy1
          obtain ⟨x, hx, rfl⟩ := hy1
          exact ⟨x, Set.mem_iUnion.2 ⟨0, hx⟩, rfl⟩
      | succ n =>
          have hyImage : y ∈ R '' returnedInterval F n := by
            rw [D.product_image n]
            simpa [Nat.succ_eq_add_one] using hn
          obtain ⟨x, hx, rfl⟩ := hyImage
          exact ⟨x, Set.mem_iUnion.2 ⟨n, hx⟩, rfl⟩
  have hA_K : A '' K ⊆ K := by
    change A '' closure U ⊆ closure U
    exact (image_closure_subset_closure_image hAcontinuous).trans
      (closure_mono hA_U)
  have hB_K : B '' K ⊆ K := by
    change B '' closure U ⊆ closure U
    exact (image_closure_subset_closure_image hBcontinuous).trans
      (closure_mono hB_U)
  have hR_K_subset : R '' K ⊆ K := by
    change R '' closure U ⊆ closure U
    exact (image_closure_subset_closure_image hRcontinuous).trans
      (closure_mono hR_U.le)
  have hKCompact : IsCompact K :=
    isCompact_univ.of_isClosed_subset hKClosed (Set.subset_univ K)
  have hRKClosed : IsClosed (R '' K) :=
    (hKCompact.image hRcontinuous).isClosed
  have hK_RK : K ⊆ R '' K := by
    change closure U ⊆ R '' K
    apply closure_minimal _ hRKClosed
    intro y hy
    have hyImage : y ∈ R '' U := by simpa [hR_U] using hy
    obtain ⟨x, hx, rfl⟩ := hyImage
    exact ⟨x, subset_closure hx, rfl⟩
  have hR_K : R '' K = K := Set.Subset.antisymm hR_K_subset hK_RK
  have hA_K_eq : A '' K = K := by
    apply Set.Subset.antisymm hA_K
    intro y hy
    have hyR : y ∈ R '' K := by simpa [hR_K] using hy
    obtain ⟨x, hx, rfl⟩ := hyR
    refine ⟨B x, hB_K ⟨x, hx, rfl⟩, ?_⟩
    rfl
  have hB_K_eq : B '' K = K := by
    apply Set.Subset.antisymm hB_K
    intro y hy
    have hyR : y ∈ R '' K := by simpa [hR_K] using hy
    obtain ⟨x, hx, rfl⟩ := hyR
    refine ⟨A x, hA_K ⟨x, hx, rfl⟩, ?_⟩
    dsimp [A, B, R, returnedProduct]
    exact (F.properties.commute x).symm
  refine ⟨hull, ?_, hnondegenerate, ?_, ?_⟩
  · exact hhull
  · dsimp [MapsOntoSubinterval]
    rw [hhull]
    exact hA_K_eq
  · dsimp [MapsOntoSubinterval]
    rw [hhull]
    exact hB_K_eq

/-- The nested image family and its compact invariant interval hull. -/
structure NestedReturnedIntervalsData
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) where
  nested : ∀ n : ℕ, returnedInterval F n ⊆ returnedInterval F (n + 1)
  product_image : ∀ n : ℕ,
    returnedProduct C L '' returnedInterval F n = returnedInterval F (n + 1)
  A_forward : ∀ n : ℕ,
    returnedP C L '' returnedInterval F n ⊆ returnedInterval F (n + 1)
  B_forward : ∀ n : ℕ,
    returnedQ C L '' returnedInterval F n ⊆ returnedInterval F (n + 1)
  hull : ClosedSubinterval
  hull_carrier :
    hull.carrier = closure (⋃ n : ℕ, returnedInterval F n)
  hull_nondegenerate : hull.Nondegenerate
  mapsOnto_A : MapsOntoSubinterval (returnedP C L) hull
  mapsOnto_B : MapsOntoSubinterval (returnedQ C L) hull

/-- The local product dilation produces nested returned intervals whose
closure is carried onto itself by both returned maps. -/
theorem nestedReturnedIntervalsData_exists
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) :
    Nonempty (NestedReturnedIntervalsData F) := by
  obtain ⟨D⟩ := returnedIntervalDynamicsData_exists F
  obtain ⟨hull, hhull, hnondegenerate, hAonto, hBonto⟩ :=
    returnedIntervalHull_exists D
  exact ⟨{
    nested := D.nested
    product_image := D.product_image
    A_forward := D.A_forward
    B_forward := D.B_forward
    hull := hull
    hull_carrier := hhull
    hull_nondegenerate := hnondegenerate
    mapsOnto_A := hAonto
    mapsOnto_B := hBonto }⟩

/-- The canonical stabilized ray before the generator identities and local
unit-speed regularity are attached. -/
private structure StabilizedRayCoreData
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) where
  ray : ℝ → I
  stabilizes : ∀ t : ℝ, 0 ≤ t →
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∃ x ∈ initialRaySegment F,
        (x : ℝ) = (G.p : ℝ) +
          t / (returnedProductScale C L) ^ n ∧
        ray t = iterateMap (returnedProduct C L) n x
  continuousOn_ray : ContinuousOn ray (Set.Ici 0)
  initial_unit_germ : ∀ t ∈ Set.Icc (0 : ℝ) F.germ_radius,
    (ray t : ℝ) = (G.p : ℝ) + t
  return_product : ∀ t : ℝ, 0 ≤ t →
    ray (returnedProductScale C L * t) = returnedProduct C L (ray t)
  range_interval : ∀ n : ℕ,
    ray '' Set.Icc (0 : ℝ)
      ((returnedProductScale C L) ^ n * F.germ_radius) =
        returnedInterval F n

/-- Nonnegative parameters used internally by the stabilized-ray
construction. -/
private abbrev FoldRayParameter := {t : ℝ // 0 ≤ t}

/-- Division by the positive returned-product scale on the parameter ray. -/
private noncomputable def foldDescale
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (n : ℕ) (t : FoldRayParameter) : FoldRayParameter :=
  ⟨(t : ℝ) / (returnedProductScale C L) ^ n,
    div_nonneg t.property (pow_nonneg
      (by
        have ha := F.properties.one_lt_a
        have hb := F.properties.one_lt_b
        dsimp [returnedProductScale]
        nlinarith) n)⟩

/-- A total clipped representative of the affine seed chart.  On every
parameter below `s * ε` it is exactly `p+t`; clipping merely supplies a
continuous total function outside the germ where it is never used. -/
private def foldSeedPoint
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (t : FoldRayParameter) : I :=
  let cap := returnedProductScale C L * F.germ_radius
  ⟨(G.p : ℝ) + min (t : ℝ) cap,
    add_nonneg G.p.property.1
      (le_min t.property (mul_nonneg
        (by
          have ha := F.properties.one_lt_a
          have hb := F.properties.one_lt_b
          dsimp [returnedProductScale]
          nlinarith) F.germ_radius_pos.le)),
    (by
      have hmin : min (t : ℝ) cap ≤ cap := min_le_right _ _
      dsimp [cap] at hmin ⊢
      linarith [F.germ_fits])⟩

private theorem foldSeedPoint_val_of_le
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (t : FoldRayParameter)
    (ht : (t : ℝ) ≤ returnedProductScale C L * F.germ_radius) :
    (foldSeedPoint F t : ℝ) = (G.p : ℝ) + (t : ℝ) := by
  change (G.p : ℝ) + min (t : ℝ)
      (returnedProductScale C L * F.germ_radius) =
    (G.p : ℝ) + (t : ℝ)
  rw [min_eq_left ht]

private theorem foldSeedPoint_continuous
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) :
    Continuous (foldSeedPoint F) := by
  unfold foldSeedPoint
  fun_prop

/-- The level-`n` normalized product representative of the ray. -/
private noncomputable def foldRayCandidate
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (n : ℕ) (t : FoldRayParameter) : I :=
  iterateMap (returnedProduct C L) n (foldSeedPoint F (foldDescale F n t))

/-- Consecutive normalized representatives agree whenever the lower level
lies in the enlarged local germ. -/
private theorem foldRayCandidate_succ_eq
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (n : ℕ) (t : FoldRayParameter)
    (ht : (t : ℝ) <
      (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ n) :
    foldRayCandidate F (n + 1) t = foldRayCandidate F n t := by
  let s : ℝ := returnedProductScale C L
  have hs : 1 < s := by
    have ha := F.properties.one_lt_a
    have hb := F.properties.one_lt_b
    dsimp [s, returnedProductScale]
    nlinarith
  have hsPos : 0 < s := zero_lt_one.trans hs
  let u : FoldRayParameter := foldDescale F (n + 1) t
  let v : FoldRayParameter := foldDescale F n t
  have hvCap : (v : ℝ) < s * F.germ_radius := by
    change (t : ℝ) / s ^ n < s * F.germ_radius
    exact (div_lt_iff₀ (pow_pos hsPos n)).2 (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using ht)
  have hsu_v : s * (u : ℝ) = (v : ℝ) := by
    change s * ((t : ℝ) / s ^ (n + 1)) = (t : ℝ) / s ^ n
    rw [pow_succ]
    field_simp [hsPos.ne']
  have huRadius : (u : ℝ) ≤ F.germ_radius := by
    have hmul : s * (u : ℝ) < s * F.germ_radius := by
      calc
        s * (u : ℝ) = (v : ℝ) := hsu_v
        _ < s * F.germ_radius := hvCap
    nlinarith
  have huCap : (u : ℝ) ≤ s * F.germ_radius := by
    have hgrowth : F.germ_radius ≤ s * F.germ_radius := by
      simpa using
        (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
    exact huRadius.trans hgrowth
  have hvCapLe : (v : ℝ) ≤ s * F.germ_radius := hvCap.le
  have hu0 : 0 ≤ (u : ℝ) := u.property
  have hseedU := foldSeedPoint_val_of_le F u huCap
  have hseedV := foldSeedPoint_val_of_le F v hvCapLe
  have hlocal := F.germ_product (u : ℝ) hu0 huRadius
    (foldSeedPoint F u) hseedU
  have hseedImage : returnedProduct C L (foldSeedPoint F u) =
      foldSeedPoint F v := by
    apply Subtype.ext
    rw [hseedV]
    exact hlocal.trans (by rw [← hsu_v])
  unfold foldRayCandidate
  rw [iterateMap, Function.iterate_succ_apply']
  change returnedProduct C L
      (((returnedProduct C L)^[n]) (foldSeedPoint F u)) =
    ((returnedProduct C L)^[n]) (foldSeedPoint F v)
  calc
    returnedProduct C L (((returnedProduct C L)^[n]) (foldSeedPoint F u)) =
        ((returnedProduct C L)^[n])
          (returnedProduct C L (foldSeedPoint F u)) :=
      Function.Commute.self_iterate (returnedProduct C L) n (foldSeedPoint F u)
    _ = ((returnedProduct C L)^[n]) (foldSeedPoint F v) :=
      congrArg ((returnedProduct C L)^[n]) hseedImage

private theorem foldRayCandidate_eq_of_le
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    {n m : ℕ} (hnm : n ≤ m) (t : FoldRayParameter)
    (ht : (t : ℝ) <
      (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ n) :
    foldRayCandidate F m t = foldRayCandidate F n t := by
  have hs : 1 < returnedProductScale C L := by
    have ha := F.properties.one_lt_a
    have hb := F.properties.one_lt_b
    dsimp [returnedProductScale]
    nlinarith
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => rfl
  | succ d ih =>
      have hpow : (returnedProductScale C L) ^ n ≤
          (returnedProductScale C L) ^ (n + d) :=
        pow_le_pow_right₀ hs.le (Nat.le_add_right n d)
      have ht' : (t : ℝ) <
          (returnedProductScale C L * F.germ_radius) *
            (returnedProductScale C L) ^ (n + d) :=
        ht.trans_le (mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (zero_lt_one.trans hs).le F.germ_radius_pos.le))
      rw [Nat.add_succ]
      exact (foldRayCandidate_succ_eq F (n + d) t ht').trans
        (ih (Nat.le_add_right n d))

private theorem foldRayCandidate_eq_of_admissible
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (n m : ℕ) (t : FoldRayParameter)
    (hn : (t : ℝ) <
      (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ n)
    (hm : (t : ℝ) <
      (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ m) :
    foldRayCandidate F n t = foldRayCandidate F m t := by
  rcases le_total n m with hnm | hmn
  · exact (foldRayCandidate_eq_of_le F hnm t hn).symm
  · exact foldRayCandidate_eq_of_le F hmn t hm

private theorem exists_foldRayCandidate_index
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (t : FoldRayParameter) :
    ∃ n : ℕ, (t : ℝ) <
      (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ n := by
  have hs : 1 < returnedProductScale C L := by
    have ha := F.properties.one_lt_a
    have hb := F.properties.one_lt_b
    dsimp [returnedProductScale]
    nlinarith
  have hcap : 0 < returnedProductScale C L * F.germ_radius :=
    mul_pos (zero_lt_one.trans hs) F.germ_radius_pos
  let M : ℝ := (t : ℝ) /
    (returnedProductScale C L * F.germ_radius)
  obtain ⟨n, hn⟩ :=
    (tendsto_pow_atTop_atTop_of_one_lt hs).eventually_gt_atTop M |>.exists
  refine ⟨n, ?_⟩
  have := (div_lt_iff₀ hcap).mp hn
  simpa [M, mul_comm, mul_left_comm, mul_assoc] using this

private noncomputable def foldRayExtensionIndex
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (t : FoldRayParameter) : ℕ :=
  Classical.choose (exists_foldRayCandidate_index F t)

private theorem foldRayExtensionIndex_spec
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (t : FoldRayParameter) :
    (t : ℝ) < (returnedProductScale C L * F.germ_radius) *
      (returnedProductScale C L) ^ foldRayExtensionIndex F t :=
  Classical.choose_spec (exists_foldRayCandidate_index F t)

private noncomputable def foldExtendedRay
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (t : FoldRayParameter) : I :=
  foldRayCandidate F (foldRayExtensionIndex F t) t

private theorem foldExtendedRay_eq_candidate
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (n : ℕ) (t : FoldRayParameter)
    (hn : (t : ℝ) <
      (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ n) :
    foldExtendedRay F t = foldRayCandidate F n t := by
  unfold foldExtendedRay
  exact foldRayCandidate_eq_of_admissible F
    (foldRayExtensionIndex F t) n t (foldRayExtensionIndex_spec F t) hn

private theorem foldExtendedRay_continuous
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) :
    Continuous (foldExtendedRay F) := by
  rw [continuous_iff_continuousAt]
  intro t
  let n := foldRayExtensionIndex F t
  have ht : (t : ℝ) <
      (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ n :=
    foldRayExtensionIndex_spec F t
  have hdescale : Continuous (foldDescale F n) :=
    (continuous_subtype_val.div_const _).subtype_mk _
  have hcand : Continuous (foldRayCandidate F n) := by
    exact (IntervalMap.continuous_iterate
      (F.properties.constantSlope_A.continuous.comp
        F.properties.constantSlope_B.continuous) n).comp
      ((foldSeedPoint_continuous F).comp hdescale)
  have hnear : {u : FoldRayParameter |
      (u : ℝ) < (returnedProductScale C L * F.germ_radius) *
        (returnedProductScale C L) ^ n} ∈ nhds t :=
    (isOpen_lt continuous_subtype_val continuous_const).mem_nhds ht
  have heq : foldExtendedRay F =ᶠ[nhds t] foldRayCandidate F n := by
    filter_upwards [hnear] with u hu
    exact foldExtendedRay_eq_candidate F n u hu
  exact hcand.continuousAt.congr heq.symm

/-- The stabilized ray as a total real function, constant on the unused
negative half-line. -/
private noncomputable def foldStabilizedRay
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) (t : ℝ) : I :=
  foldExtendedRay F ⟨max 0 t, le_max_left 0 t⟩

private theorem foldExtendedRay_product
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (t : FoldRayParameter) :
    foldExtendedRay F
        ⟨returnedProductScale C L * (t : ℝ),
          mul_nonneg
            (by
              have ha := F.properties.one_lt_a
              have hb := F.properties.one_lt_b
              dsimp [returnedProductScale]
              nlinarith) t.property⟩ =
      returnedProduct C L (foldExtendedRay F t) := by
  let s : ℝ := returnedProductScale C L
  have hs : 1 < s := by
    have ha := F.properties.one_lt_a
    have hb := F.properties.one_lt_b
    dsimp [s, returnedProductScale]
    nlinarith
  have hsPos : 0 < s := zero_lt_one.trans hs
  let n := foldRayExtensionIndex F t
  have ht : (t : ℝ) < (s * F.germ_radius) * s ^ n := by
    simpa [s] using foldRayExtensionIndex_spec F t
  let scaled : FoldRayParameter :=
    ⟨s * (t : ℝ), mul_nonneg hsPos.le t.property⟩
  have hscaled : (scaled : ℝ) <
      (s * F.germ_radius) * s ^ (n + 1) := by
    have hmul := mul_lt_mul_of_pos_left ht hsPos
    simpa [scaled, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hdescale : foldDescale F (n + 1) scaled = foldDescale F n t := by
    apply Subtype.ext
    change (s * (t : ℝ)) / s ^ (n + 1) = (t : ℝ) / s ^ n
    rw [pow_succ]
    field_simp [hsPos.ne']
  change foldExtendedRay F scaled =
    returnedProduct C L (foldExtendedRay F t)
  rw [foldExtendedRay_eq_candidate F (n + 1) scaled hscaled,
    foldExtendedRay_eq_candidate F n t ht]
  unfold foldRayCandidate
  rw [hdescale]
  simp only [iterateMap, Function.iterate_succ_apply']

/-- Stabilization of the normalized product iterates gives the continuous
core ray and its exact product-scale and range identities. -/
private theorem stabilizedRayCoreData_exists
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G) :
    Nonempty (StabilizedRayCoreData F) := by
  let s : ℝ := returnedProductScale C L
  have hs : 1 < s := by
    have ha := F.properties.one_lt_a
    have hb := F.properties.one_lt_b
    dsimp [s, returnedProductScale]
    nlinarith
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hcapPos : 0 < s * F.germ_radius :=
    mul_pos hsPos F.germ_radius_pos
  have hepsilon_cap : F.germ_radius < s * F.germ_radius := by
    nlinarith [F.germ_radius_pos]
  have hliftContinuous : Continuous
      (fun t : ℝ => (⟨max 0 t, le_max_left 0 t⟩ : FoldRayParameter)) :=
    (continuous_const.max continuous_id).subtype_mk _
  have hrayContinuous : Continuous (foldStabilizedRay F) := by
    exact (foldExtendedRay_continuous F).comp hliftContinuous
  have hstabilizes : ∀ t : ℝ, 0 ≤ t →
      ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
        ∃ x ∈ initialRaySegment F,
          (x : ℝ) = (G.p : ℝ) + t / s ^ n ∧
          foldStabilizedRay F t =
            iterateMap (returnedProduct C L) n x := by
    intro t ht
    let M : ℝ := t / F.germ_radius
    obtain ⟨N0, hN0⟩ :=
      (tendsto_pow_atTop_atTop_of_one_lt hs).eventually_gt_atTop M |>.exists
    have htN0 : t < F.germ_radius * s ^ N0 := by
      have := (div_lt_iff₀ F.germ_radius_pos).mp hN0
      simpa [M, mul_comm] using this
    refine ⟨N0, ?_⟩
    intro n hn
    have hpow : s ^ N0 ≤ s ^ n := pow_le_pow_right₀ hs.le hn
    have htn : t < F.germ_radius * s ^ n :=
      htN0.trans_le
        (mul_le_mul_of_nonneg_left hpow F.germ_radius_pos.le)
    let tp : FoldRayParameter := ⟨t, ht⟩
    let u : FoldRayParameter := foldDescale F n tp
    have huEpsilon : (u : ℝ) ≤ F.germ_radius := by
      change t / s ^ n ≤ F.germ_radius
      exact ((div_le_iff₀ (pow_pos hsPos n)).2 (by
        simpa [mul_comm] using htn.le))
    have huCap : (u : ℝ) ≤ s * F.germ_radius :=
      huEpsilon.trans hepsilon_cap.le
    have hseedVal : (foldSeedPoint F u : ℝ) =
        (G.p : ℝ) + t / s ^ n := by
      rw [foldSeedPoint_val_of_le F u huCap]
      rfl
    have htAdmissible : t < (s * F.germ_radius) * s ^ n := by
      exact htn.trans_le (mul_le_mul_of_nonneg_right
        hepsilon_cap.le (pow_nonneg hsPos.le n))
    have hrayCandidate : foldStabilizedRay F t =
        foldRayCandidate F n tp := by
      have hlift : (⟨max 0 t, le_max_left 0 t⟩ : FoldRayParameter) = tp := by
        apply Subtype.ext
        exact max_eq_right ht
      unfold foldStabilizedRay
      rw [hlift]
      exact foldExtendedRay_eq_candidate F n tp (by simpa [s] using htAdmissible)
    refine ⟨foldSeedPoint F u, ?_, hseedVal, ?_⟩
    · exact ⟨(u : ℝ), ⟨u.property, huEpsilon⟩,
        foldSeedPoint_val_of_le F u huCap⟩
    · exact hrayCandidate
  have hinitial : ∀ t ∈ Set.Icc (0 : ℝ) F.germ_radius,
      (foldStabilizedRay F t : ℝ) = (G.p : ℝ) + t := by
    intro t ht
    let tp : FoldRayParameter := ⟨t, ht.1⟩
    have htAdmissible : t < (s * F.germ_radius) * s ^ 0 := by
      simp only [pow_zero, mul_one]
      exact ht.2.trans_lt hepsilon_cap
    have hlift : (⟨max 0 t, le_max_left 0 t⟩ : FoldRayParameter) = tp := by
      apply Subtype.ext
      exact max_eq_right ht.1
    have hray : foldStabilizedRay F t = foldRayCandidate F 0 tp := by
      unfold foldStabilizedRay
      rw [hlift]
      exact foldExtendedRay_eq_candidate F 0 tp (by simpa [s] using htAdmissible)
    rw [hray]
    change (foldSeedPoint F (foldDescale F 0 tp) : ℝ) = _
    have hdescale : foldDescale F 0 tp = tp := by
      exact Subtype.ext (by
        change (t / (returnedProductScale C L) ^ 0) = t
        simp)
    rw [hdescale, foldSeedPoint_val_of_le F tp]
    exact ht.2.trans hepsilon_cap.le
  have hreturnProduct : ∀ t : ℝ, 0 ≤ t →
      foldStabilizedRay F (s * t) =
        returnedProduct C L (foldStabilizedRay F t) := by
    intro t ht
    let tp : FoldRayParameter := ⟨t, ht⟩
    have hst0 : 0 ≤ s * t := mul_nonneg hsPos.le ht
    have hliftT : (⟨max 0 t, le_max_left 0 t⟩ : FoldRayParameter) = tp := by
      apply Subtype.ext
      exact max_eq_right ht
    have hliftST :
        (⟨max 0 (s * t), le_max_left 0 (s * t)⟩ : FoldRayParameter) =
          ⟨s * t, hst0⟩ := by
      apply Subtype.ext
      exact max_eq_right hst0
    unfold foldStabilizedRay
    rw [hliftT, hliftST]
    simpa [s] using foldExtendedRay_product F tp
  have hrange : ∀ n : ℕ,
      foldStabilizedRay F '' Set.Icc (0 : ℝ) (s ^ n * F.germ_radius) =
        returnedInterval F n := by
    intro n
    apply Set.Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      let tp : FoldRayParameter := ⟨t, ht.1⟩
      let u : FoldRayParameter := foldDescale F n tp
      have huEpsilon : (u : ℝ) ≤ F.germ_radius := by
        change t / s ^ n ≤ F.germ_radius
        exact (div_le_iff₀ (pow_pos hsPos n)).2 (by
          simpa [mul_comm] using ht.2)
      have huCap : (u : ℝ) ≤ s * F.germ_radius :=
        huEpsilon.trans hepsilon_cap.le
      have htAdmissible : t < (s * F.germ_radius) * s ^ n := by
        have hstrict : s ^ n * F.germ_radius <
            (s * F.germ_radius) * s ^ n := by
          calc
            s ^ n * F.germ_radius = F.germ_radius * s ^ n := by ring
            _ < (s * F.germ_radius) * s ^ n :=
              mul_lt_mul_of_pos_right hepsilon_cap (pow_pos hsPos n)
        exact ht.2.trans_lt hstrict
      have hlift : (⟨max 0 t, le_max_left 0 t⟩ : FoldRayParameter) = tp := by
        apply Subtype.ext
        exact max_eq_right ht.1
      have hray : foldStabilizedRay F t = foldRayCandidate F n tp := by
        unfold foldStabilizedRay
        rw [hlift]
        exact foldExtendedRay_eq_candidate F n tp (by simpa [s] using htAdmissible)
      rw [returnedInterval]
      refine ⟨foldSeedPoint F u, ?_, ?_⟩
      · exact ⟨(u : ℝ), ⟨u.property, huEpsilon⟩,
          foldSeedPoint_val_of_le F u huCap⟩
      · exact hray.symm
    · rintro y ⟨x, hx, hxy⟩
      obtain ⟨u, hu, hxu⟩ := hx
      let t : ℝ := s ^ n * u
      have ht0 : 0 ≤ t := mul_nonneg (pow_nonneg hsPos.le n) hu.1
      have htupper : t ≤ s ^ n * F.germ_radius :=
        mul_le_mul_of_nonneg_left hu.2 (pow_nonneg hsPos.le n)
      let tp : FoldRayParameter := ⟨t, ht0⟩
      let up : FoldRayParameter := ⟨u, hu.1⟩
      have hdescale : foldDescale F n tp = up := by
        apply Subtype.ext
        change (s ^ n * u) / s ^ n = u
        field_simp [(pow_pos hsPos n).ne']
      have hupCap : (up : ℝ) ≤ s * F.germ_radius :=
        hu.2.trans hepsilon_cap.le
      have hseedX : foldSeedPoint F up = x := by
        apply Subtype.ext
        rw [foldSeedPoint_val_of_le F up hupCap]
        exact hxu.symm
      have htAdmissible : t < (s * F.germ_radius) * s ^ n := by
        calc
          t ≤ s ^ n * F.germ_radius := htupper
          _ < (s * F.germ_radius) * s ^ n := by
            calc
              s ^ n * F.germ_radius = F.germ_radius * s ^ n := by ring
              _ < (s * F.germ_radius) * s ^ n :=
                mul_lt_mul_of_pos_right hepsilon_cap (pow_pos hsPos n)
      have hlift : (⟨max 0 t, le_max_left 0 t⟩ : FoldRayParameter) = tp := by
        apply Subtype.ext
        exact max_eq_right ht0
      have hray : foldStabilizedRay F t = foldRayCandidate F n tp := by
        unfold foldStabilizedRay
        rw [hlift]
        exact foldExtendedRay_eq_candidate F n tp (by simpa [s] using htAdmissible)
      refine ⟨t, ⟨ht0, htupper⟩, ?_⟩
      rw [hray]
      unfold foldRayCandidate
      rw [hdescale, hseedX, hxy]
  refine ⟨{
    ray := foldStabilizedRay F
    stabilizes := by simpa [s] using hstabilizes
    continuousOn_ray := hrayContinuous.continuousOn
    initial_unit_germ := hinitial
    return_product := by simpa [s] using hreturnProduct
    range_interval := by simpa [s] using hrange }⟩

/-- Commutation and the two local return germs globalize the generator
scale identities along the stabilized product ray. -/
private theorem StabilizedRayCoreData.generator_returns
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    (S : StabilizedRayCoreData F) :
    (∀ t : ℝ, 0 ≤ t →
      S.ray (returnedScaleP C L * t) = returnedP C L (S.ray t)) ∧
    (∀ t : ℝ, 0 ≤ t →
      S.ray (returnedScaleQ C L * t) = returnedQ C L (S.ray t)) := by
  let A : IntervalMap := returnedP C L
  let B : IntervalMap := returnedQ C L
  let R : IntervalMap := returnedProduct C L
  let a : ℝ := returnedScaleP C L
  let b : ℝ := returnedScaleQ C L
  let s : ℝ := returnedProductScale C L
  have ha : 1 < a := F.properties.one_lt_a
  have hb : 1 < b := F.properties.one_lt_b
  have haPos : 0 < a := zero_lt_one.trans ha
  have hbPos : 0 < b := zero_lt_one.trans hb
  have hs : 1 < s := by
    dsimp [s, returnedProductScale]
    nlinarith
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hepsilonScale : F.germ_radius ≤ s * F.germ_radius := by
    simpa using
      (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
  have hAR : Function.Commute A R := by
    intro x
    dsimp [A, R, returnedProduct]
    exact congrArg (returnedP C L) (F.properties.commute x)
  have hBR : Function.Commute B R := by
    intro x
    dsimp [B, R, returnedProduct]
    exact (F.properties.commute (returnedQ C L x)).symm
  constructor
  · intro t ht
    have hat : 0 ≤ a * t := mul_nonneg haPos.le ht
    obtain ⟨Nt, hNt⟩ := S.stabilizes t ht
    obtain ⟨Nat, hNat⟩ := S.stabilizes (a * t) hat
    let n := max Nt Nat
    obtain ⟨x, hxSeed, hxCoord, hxRay⟩ := hNt n (le_max_left _ _)
    obtain ⟨y, hySeed, hyCoord, hyRay⟩ := hNat n (le_max_right _ _)
    obtain ⟨ux, hux, hxSeedCoord⟩ := hxSeed
    have hu0 : 0 ≤ t / s ^ n :=
      div_nonneg ht (pow_nonneg hsPos.le n)
    have huRadius : t / s ^ n ≤ F.germ_radius := by
      have huEq : t / s ^ n = ux := by linarith [hxCoord, hxSeedCoord]
      rw [huEq]
      exact hux.2
    have huScale : t / s ^ n ≤ returnedProductScale C L * F.germ_radius := by
      change t / s ^ n ≤ s * F.germ_radius
      exact huRadius.trans hepsilonScale
    have hAx := F.germ_A (t / s ^ n) hu0 huScale x hxCoord
    have hAy : A x = y := by
      apply Subtype.ext
      have hscaled : a * t / s ^ n = a * (t / s ^ n) := by ring
      change (returnedP C L x : ℝ) = (y : ℝ)
      rw [hAx, hyCoord, hscaled]
    rw [hyRay, hxRay]
    change iterateMap R n y = A (iterateMap R n x)
    rw [← hAy]
    exact (hAR.iterate_right n x).symm
  · intro t ht
    have hbt : 0 ≤ b * t := mul_nonneg hbPos.le ht
    obtain ⟨Nt, hNt⟩ := S.stabilizes t ht
    obtain ⟨Nbt, hNbt⟩ := S.stabilizes (b * t) hbt
    let n := max Nt Nbt
    obtain ⟨x, hxSeed, hxCoord, hxRay⟩ := hNt n (le_max_left _ _)
    obtain ⟨y, hySeed, hyCoord, hyRay⟩ := hNbt n (le_max_right _ _)
    obtain ⟨ux, hux, hxSeedCoord⟩ := hxSeed
    have hu0 : 0 ≤ t / s ^ n :=
      div_nonneg ht (pow_nonneg hsPos.le n)
    have huRadius : t / s ^ n ≤ F.germ_radius := by
      have huEq : t / s ^ n = ux := by linarith [hxCoord, hxSeedCoord]
      rw [huEq]
      exact hux.2
    have huScale : t / s ^ n ≤ returnedProductScale C L * F.germ_radius := by
      change t / s ^ n ≤ s * F.germ_radius
      exact huRadius.trans hepsilonScale
    have hBx := F.germ_B (t / s ^ n) hu0 huScale x hxCoord
    have hBy : B x = y := by
      apply Subtype.ext
      have hscaled : b * t / s ^ n = b * (t / s ^ n) := by ring
      change (returnedQ C L x : ℝ) = (y : ℝ)
      rw [hBx, hyCoord, hscaled]
    rw [hyRay, hxRay]
    change iterateMap R n y = B (iterateMap R n x)
    rw [← hBy]
    exact (hBR.iterate_right n x).symm

private theorem RealPartition.exists_adjacent_right_for_foldRay
    (partition : RealPartition) {x : ℝ}
    (hxI : x ∈ I) (hxright : x < 1) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ a ≤ x ∧ x < b := by
  classical
  let lower := partition.points.filter fun z => z ≤ x
  let upper := partition.points.filter fun z => x < z
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

/-- Pulling a positive constant-slope map back by its slope magnitude gives
a finite-piece unit-speed path on any compact parameter interval. -/
private theorem rescaledConstantSlope_unitSpeed
    {T : IntervalMap} {path : ℝ → I} {scale base left right : ℝ}
    (hscale : 0 < scale) (hlr : left < right)
    (hslope : HasConstantAbsoluteSlope T scale)
    (hinput : ∀ t ∈ Set.Icc left right,
      base + t / scale ∈ I)
    (hpath : ∀ t ∈ Set.Icc left right,
      ∀ htI : base + t / scale ∈ I,
      (path t : ℝ) =
        (T ⟨base + t / scale, htI⟩ : ℝ)) :
    IsFinitePieceUnitSpeedOn path left right := by
  classical
  rcases hslope with ⟨_hcont, partition, hpartition⟩
  let parameterVertex : ℝ → ℝ := fun z => scale * (z - base)
  let scaledVertices : Finset ℝ := partition.points.image parameterVertex
  let K : Finset ℝ :=
    insert left (insert right
      (scaledVertices.filter fun z => z ∈ Set.Icc left right))
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
    partition.exists_adjacent_right_for_foldRay xI.property
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

private theorem StabilizedRayCoreData.return_product_iterate
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    (S : StabilizedRayCoreData F) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    S.ray ((returnedProductScale C L) ^ n * t) =
      iterateMap (returnedProduct C L) n (S.ray t) := by
  induction n with
  | zero => simp [iterateMap]
  | succ n ih =>
      have hs0 : 0 ≤ returnedProductScale C L := by
        have ha := F.properties.one_lt_a
        have hb := F.properties.one_lt_b
        dsimp [returnedProductScale]
        nlinarith
      have hpowt : 0 ≤ (returnedProductScale C L) ^ n * t :=
        mul_nonneg (pow_nonneg hs0 n) ht
      calc
        S.ray ((returnedProductScale C L) ^ (n + 1) * t) =
            S.ray (returnedProductScale C L *
              ((returnedProductScale C L) ^ n * t)) := by
          rw [pow_succ]
          congr 1
          ring
        _ =
            returnedProduct C L
              (S.ray ((returnedProductScale C L) ^ n * t)) :=
          S.return_product _ hpowt
        _ = returnedProduct C L
              (iterateMap (returnedProduct C L) n (S.ray t)) :=
          congrArg (returnedProduct C L) ih
        _ = iterateMap (returnedProduct C L) (n + 1) (S.ray t) := by
          exact (Function.iterate_succ_apply' (returnedProduct C L) n (S.ray t)).symm

/-- Rescaling a constant-slope product iterate by its slope magnitude makes
the stabilized ray finite-piece unit speed on every compact positive
parameter interval. -/
private theorem StabilizedRayCoreData.locally_unit_speed
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    (S : StabilizedRayCoreData F) :
    ∀ u v : ℝ, 0 ≤ u → u < v → IsFinitePieceUnitSpeedOn S.ray u v := by
  intro u v hu huv
  let s : ℝ := returnedProductScale C L
  have ha : 1 < returnedScaleP C L := F.properties.one_lt_a
  have hb : 1 < returnedScaleQ C L := F.properties.one_lt_b
  have haPos : 0 < returnedScaleP C L := zero_lt_one.trans ha
  have hbPos : 0 < returnedScaleQ C L := zero_lt_one.trans hb
  have hs : 1 < s := by
    dsimp [s, returnedProductScale]
    nlinarith
  have hsPos : 0 < s := zero_lt_one.trans hs
  let M : ℝ := v / F.germ_radius
  obtain ⟨n, hn⟩ :=
    (tendsto_pow_atTop_atTop_of_one_lt hs).eventually_gt_atTop M |>.exists
  have hvBound : v < F.germ_radius * s ^ n := by
    have := (div_lt_iff₀ F.germ_radius_pos).mp hn
    simpa [M, mul_comm] using this
  let R : IntervalMap := returnedProduct C L
  let T : IntervalMap := iterateMap R n
  let scale : ℝ := s ^ n
  have hscale : 0 < scale := pow_pos hsPos n
  have hRconstant : HasConstantAbsoluteSlope R s := by
    have hcomp := HasConstantAbsoluteSlope.comp_of_pos hbPos
      F.properties.constantSlope_A F.properties.constantSlope_B
    simpa [R, s, returnedProduct, returnedProductScale] using hcomp
  have hTconstant : HasConstantAbsoluteSlope T scale := by
    simpa [T, scale] using hRconstant.iterateMap hsPos n
  have hepsilonScale : F.germ_radius ≤ s * F.germ_radius := by
    simpa using
      (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
  have hsmallFit : (G.p : ℝ) + F.germ_radius ≤ 1 := by
    have hfit : (G.p : ℝ) + s * F.germ_radius ≤ 1 := by
      simpa [s] using F.germ_fits
    linarith
  have hinput : ∀ t ∈ Set.Icc u v,
      (G.p : ℝ) + t / scale ∈ I := by
    intro t ht
    have ht0 : 0 ≤ t := hu.trans ht.1
    have htDiv0 : 0 ≤ t / scale := div_nonneg ht0 hscale.le
    have htDivEpsilon : t / scale < F.germ_radius := by
      apply (div_lt_iff₀ hscale).2
      exact ht.2.trans_lt (by simpa [scale, mul_comm] using hvBound)
    exact ⟨add_nonneg G.p.property.1 htDiv0,
      (by linarith [hsmallFit])⟩
  have hpath : ∀ t ∈ Set.Icc u v,
      ∀ htI : (G.p : ℝ) + t / scale ∈ I,
      (S.ray t : ℝ) =
        (T ⟨(G.p : ℝ) + t / scale, htI⟩ : ℝ) := by
    intro t ht htI
    have ht0 : 0 ≤ t := hu.trans ht.1
    have hz0 : 0 ≤ t / scale := div_nonneg ht0 hscale.le
    have hzEpsilon : t / scale ≤ F.germ_radius := by
      apply (div_le_iff₀ hscale).2
      exact ht.2.trans (by simpa [scale, mul_comm] using hvBound.le)
    have hlocal := S.initial_unit_germ (t / scale) ⟨hz0, hzEpsilon⟩
    have hlocalPoint : S.ray (t / scale) =
        (⟨(G.p : ℝ) + t / scale, htI⟩ : I) := by
      exact Subtype.ext hlocal
    have hreturn := S.return_product_iterate n (t / scale) hz0
    have hmul : s ^ n * (t / scale) = t := by
      change scale * (t / scale) = t
      field_simp [hscale.ne']
    change S.ray (s ^ n * (t / scale)) =
      T (S.ray (t / scale)) at hreturn
    rw [hmul, hlocalPoint] at hreturn
    exact congrArg Subtype.val hreturn
  exact rescaledConstantSlope_unitSpeed hscale huv hTconstant hinput hpath

/-- Stabilization of `R^n(p+t/s^n)` gives the global nonnegative ray. -/
structure StabilizedRayData
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (N : NestedReturnedIntervalsData F) where
  ray : ℝ → I
  stabilizes : ∀ t : ℝ, 0 ≤ t →
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∃ x ∈ initialRaySegment F,
        (x : ℝ) = (G.p : ℝ) +
          t / (returnedProductScale C L) ^ n ∧
        ray t = iterateMap (returnedProduct C L) n x
  continuousOn_ray : ContinuousOn ray (Set.Ici 0)
  initial_unit_germ : ∀ t ∈ Set.Icc (0 : ℝ) F.germ_radius,
    (ray t : ℝ) = (G.p : ℝ) + t
  locally_unit_speed : ∀ u v : ℝ,
    0 ≤ u → u < v → IsFinitePieceUnitSpeedOn ray u v
  return_A : ∀ t : ℝ, 0 ≤ t →
    ray (returnedScaleP C L * t) = returnedP C L (ray t)
  return_B : ∀ t : ℝ, 0 ≤ t →
    ray (returnedScaleQ C L * t) = returnedQ C L (ray t)
  return_product : ∀ t : ℝ, 0 ≤ t →
    ray (returnedProductScale C L * t) = returnedProduct C L (ray t)
  range_interval : ∀ n : ℕ,
    ray '' Set.Icc (0 : ℝ)
      ((returnedProductScale C L) ^ n * F.germ_radius) =
        returnedInterval F n

/-- The compatible local formulas stabilize to a continuous locally
unit-speed ray satisfying all three return identities. -/
theorem stabilizedRayData_exists
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (N : NestedReturnedIntervalsData F) :
    Nonempty (StabilizedRayData F N) := by
  obtain ⟨S⟩ := stabilizedRayCoreData_exists F
  obtain ⟨hreturnA, hreturnB⟩ := S.generator_returns
  exact ⟨{
    ray := S.ray
    stabilizes := S.stabilizes
    continuousOn_ray := S.continuousOn_ray
    initial_unit_germ := S.initial_unit_germ
    locally_unit_speed := S.locally_unit_speed
    return_A := hreturnA
    return_B := hreturnB
    return_product := S.return_product
    range_interval := S.range_interval }⟩

/-! ## F5: irreducibility makes the ray dense -/

theorem nestedReturnedHull_eq_univ
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    (N : NestedReturnedIntervalsData F)
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L) :
    N.hull.carrier = Set.univ := by
  exact hirreducible N.hull N.hull_nondegenerate N.mapsOnto_A N.mapsOnto_B

/-- The nonnegative ray is exactly the increasing union of its bounded
returned-interval ranges. -/
private theorem stabilizedRay_nonnegativeRange_eq_iUnion
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    {N : NestedReturnedIntervalsData F}
    (S : StabilizedRayData F N) :
    S.ray '' Set.Ici (0 : ℝ) = ⋃ n : ℕ, returnedInterval F n := by
  let s : ℝ := returnedProductScale C L
  have hs : 1 < s := by
    have ha := F.properties.one_lt_a
    have hb := F.properties.one_lt_b
    dsimp [s, returnedProductScale]
    nlinarith
  apply Set.Subset.antisymm
  · rintro y ⟨t, ht, rfl⟩
    let M : ℝ := t / F.germ_radius
    obtain ⟨n, hn⟩ :=
      (tendsto_pow_atTop_atTop_of_one_lt hs).eventually_gt_atTop M |>.exists
    have htupper : t ≤ s ^ n * F.germ_radius := by
      have hstrict := (div_lt_iff₀ F.germ_radius_pos).mp hn
      simpa [M, mul_comm] using hstrict.le
    apply Set.mem_iUnion.2
    refine ⟨n, ?_⟩
    rw [← S.range_interval n]
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    simpa [s] using htupper
  · intro y hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hy
    rw [← S.range_interval n] at hn
    obtain ⟨t, ht, rfl⟩ := hn
    exact ⟨t, ht.1, rfl⟩

/-- The nonnegative range of the stabilized ray is dense in `I`. -/
theorem stabilizedRay_dense
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    {N : NestedReturnedIntervalsData F}
    (S : StabilizedRayData F N)
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L) :
    Dense (S.ray '' Set.Ici (0 : ℝ)) := by
  apply dense_iff_closure_eq.mpr
  rw [stabilizedRay_nonnegativeRange_eq_iUnion S]
  rw [← N.hull_carrier]
  exact nestedReturnedHull_eq_univ N hirreducible

/-! ## F6: centralizer germ globalization -/

/-- Commuting maps which agree on the seed interval agree on all returned
images and hence, by irreducibility, everywhere. -/
theorem centralizer_eq_of_eqOn_initialRaySegment
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    {F : FactorialReturnGermData C bound L X G}
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L)
    {U V : IntervalMap}
    (hU : Continuous U) (hV : Continuous V)
    (hUcomm : Function.Commute U (returnedProduct C L))
    (hVcomm : Function.Commute V (returnedProduct C L))
    (hlocal : Set.EqOn U V (initialRaySegment F)) :
    U = V := by
  obtain ⟨N⟩ := nestedReturnedIntervalsData_exists F
  have heqInterval (n : ℕ) :
      Set.EqOn U V (returnedInterval F n) := by
    rintro y ⟨x, hx, rfl⟩
    calc
      U (iterateMap (returnedProduct C L) n x) =
          iterateMap (returnedProduct C L) n (U x) :=
        hUcomm.iterate_right n x
      _ = iterateMap (returnedProduct C L) n (V x) :=
        congrArg (iterateMap (returnedProduct C L) n) (hlocal hx)
      _ = V (iterateMap (returnedProduct C L) n x) :=
        (hVcomm.iterate_right n x).symm
  have heqUnion : Set.EqOn U V (⋃ n : ℕ, returnedInterval F n) := by
    intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
    exact heqInterval n hn
  have hequalizerClosed : IsClosed {x : I | U x = V x} :=
    isClosed_eq hU hV
  apply funext
  intro x
  apply closure_minimal heqUnion hequalizerClosed
  rw [← N.hull_carrier, nestedReturnedHull_eq_univ N hirreducible]
  exact Set.mem_univ x

/-- All returned-germ data remain valid after replacing the common radius
by a smaller positive radius. -/
private def FactorialReturnGermData.restrictRadius
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (radius : ℝ) (hradius : 0 < radius)
    (hle : radius ≤ F.germ_radius) :
    FactorialReturnGermData C bound L X G := by
  have hs0 : 0 ≤ returnedProductScale C L := by
    have ha := F.properties.one_lt_a
    have hb := F.properties.one_lt_b
    dsimp [returnedProductScale]
    nlinarith
  refine {
    properties := F.properties
    sideAction := F.sideAction
    fixed_side_A := F.fixed_side_A
    fixed_side_B := F.fixed_side_B
    positive_germ_A := F.positive_germ_A
    positive_germ_B := F.positive_germ_B
    germ_radius := radius
    germ_radius_pos := hradius
    germ_fits := ?_
    germ_A := ?_
    germ_B := ?_
    germ_product := ?_ }
  · have hscaled : returnedProductScale C L * radius ≤
        returnedProductScale C L * F.germ_radius :=
      mul_le_mul_of_nonneg_left hle hs0
    linarith [F.germ_fits]
  · intro t ht htbound x hx
    apply F.germ_A t ht _ x hx
    exact htbound.trans (mul_le_mul_of_nonneg_left hle hs0)
  · intro t ht htbound x hx
    apply F.germ_B t ht _ x hx
    exact htbound.trans (mul_le_mul_of_nonneg_left hle hs0)
  · intro t ht htbound x hx
    exact F.germ_product t ht (htbound.trans hle) x hx

/-- The seed may be shrunk: equality on the selected repelling germ already
globalizes throughout the centralizer of the returned product. -/
theorem centralizer_germ_globalization
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L)
    {U V : IntervalMap}
    (hU : Continuous U) (hV : Continuous V)
    (hUcomm : Function.Commute U (returnedProduct C L))
    (hVcomm : Function.Commute V (returnedProduct C L))
    (hgerm : SameGermOnDirectedSide G.side U V) :
    U = V := by
  have hgermRight := hgerm
  simp only [SameGermOnDirectedSide, G.side_direction, G.side_base,
    SameOneSidedGermAt] at hgermRight
  obtain ⟨b, hpb, heqGerm⟩ := hgermRight
  let gap : ℝ := (b : ℝ) - (G.p : ℝ)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hpb
  let radius : ℝ := min F.germ_radius gap / 2
  have hminPos : 0 < min F.germ_radius gap :=
    lt_min F.germ_radius_pos hgap
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hradius_le : radius ≤ F.germ_radius := by
    have hmin := min_le_left F.germ_radius gap
    dsimp [radius]
    linarith
  have hradius_gap : radius < gap := by
    have hmin := min_le_right F.germ_radius gap
    dsimp [radius]
    linarith
  let Fsmall : FactorialReturnGermData C bound L X G :=
    F.restrictRadius radius hradius hradius_le
  have hlocalSmall : Set.EqOn U V (initialRaySegment Fsmall) := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := hx
    apply heqGerm
    constructor
    · change (G.p : ℝ) ≤ (x : ℝ)
      rw [hxt]
      linarith [ht.1]
    · change (x : ℝ) ≤ (b : ℝ)
      rw [hxt]
      have htRadius : t ≤ radius := by
        simpa [Fsmall, FactorialReturnGermData.restrictRadius] using ht.2
      dsimp [gap] at hradius_gap
      linarith
  exact centralizer_eq_of_eqOn_initialRaySegment
    (F := Fsmall) hirreducible hU hV hUcomm hVcomm hlocalSmall

/-! ## F7: equality of scale powers globalizes to equality of iterates -/

/-- Iterating a positive affine germ raises its dilation factor to the
corresponding power, provided the initial displacement is divided by that
power. -/
private theorem iterateMap_affineGerm_formula
    {T : IntervalMap} {p : I} {scale cap radius : ℝ}
    (hscale : 1 < scale) (hcap : 1 ≤ cap) (hradius : 0 < radius)
    (hgerm : ∀ t : ℝ, 0 ≤ t → t ≤ cap * radius →
      ∀ x : I, (x : ℝ) = (p : ℝ) + t →
        (T x : ℝ) = (p : ℝ) + scale * t) :
    ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ radius / scale ^ m →
      ∀ x : I, (x : ℝ) = (p : ℝ) + t →
        (iterateMap T m x : ℝ) = (p : ℝ) + scale ^ m * t := by
  intro m
  induction m with
  | zero =>
      intro t _ht _htbound x hx
      simpa [iterateMap] using hx
  | succ m ih =>
      intro t ht htbound x hx
      have hpowPos : 0 < scale ^ m := pow_pos (zero_lt_one.trans hscale) m
      have hpowSuccPos : 0 < scale ^ (m + 1) :=
        pow_pos (zero_lt_one.trans hscale) (m + 1)
      have htMulSucc : t * scale ^ (m + 1) ≤ radius :=
        (le_div_iff₀ hpowSuccPos).mp htbound
      have hpowLe : scale ^ m ≤ scale ^ (m + 1) :=
        pow_le_pow_right₀ hscale.le (Nat.le_succ m)
      have htMul : t * scale ^ m ≤ radius :=
        (mul_le_mul_of_nonneg_left hpowLe ht).trans htMulSucc
      have htbound' : t ≤ radius / scale ^ m :=
        (le_div_iff₀ hpowPos).2 htMul
      have hiterate := ih t ht htbound' x hx
      have hu0 : 0 ≤ scale ^ m * t :=
        mul_nonneg hpowPos.le ht
      have huRadius : scale ^ m * t ≤ radius := by
        simpa [mul_comm] using htMul
      have hradiusCap : radius ≤ cap * radius := by
        simpa using mul_le_mul_of_nonneg_right hcap hradius.le
      have hnext := hgerm (scale ^ m * t) hu0
        (huRadius.trans hradiusCap) (iterateMap T m x) hiterate
      have hsucc : iterateMap T (m + 1) x = T (iterateMap T m x) := by
        exact Function.iterate_succ_apply' T m x
      rw [hsucc, hnext, pow_succ]
      ring

/-- Equal positive powers of the two local dilation factors give the same
one-sided germ for the corresponding returned iterates. -/
theorem returnedIterates_sameGerm_of_scalePowers_eq
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hscale : (returnedScaleP C L) ^ m =
      (returnedScaleQ C L) ^ n) :
    SameGermOnDirectedSide G.side
      (iterateMap (returnedP C L) m)
      (iterateMap (returnedQ C L) n) := by
  let a : ℝ := returnedScaleP C L
  let b : ℝ := returnedScaleQ C L
  let s : ℝ := returnedProductScale C L
  have ha : 1 < a := F.properties.one_lt_a
  have hb : 1 < b := F.properties.one_lt_b
  have hs : 1 < s := by
    dsimp [s, returnedProductScale]
    nlinarith [zero_lt_one.trans ha, zero_lt_one.trans hb]
  have ham : 1 < a ^ m := one_lt_pow₀ ha (Nat.ne_of_gt hm)
  let radius : ℝ := F.germ_radius / a ^ m
  have hradius : 0 < radius :=
    div_pos F.germ_radius_pos (zero_lt_one.trans ham)
  have hradius_le : radius ≤ F.germ_radius := by
    exact div_le_self F.germ_radius_pos.le ham.le
  have hsmallFit : (G.p : ℝ) + F.germ_radius ≤ 1 := by
    have hepsilonScale : F.germ_radius ≤ s * F.germ_radius := by
      simpa using
        (mul_le_mul_of_nonneg_right hs.le F.germ_radius_pos.le)
    have hfit : (G.p : ℝ) + s * F.germ_radius ≤ 1 := by
      simpa [s] using F.germ_fits
    linarith
  let q : I :=
    ⟨(G.p : ℝ) + radius,
      add_nonneg G.p.property.1 hradius.le,
      (by linarith [hsmallFit, hradius_le])⟩
  have hpq : G.p < q := by
    change (G.p : ℝ) < (G.p : ℝ) + radius
    linarith
  have hPformula := iterateMap_affineGerm_formula
    (T := returnedP C L) (p := G.p)
    (scale := a) (cap := s) (radius := F.germ_radius)
    ha hs.le F.germ_radius_pos (by
      intro t ht htbound x hx
      exact F.germ_A t ht (by simpa [s] using htbound) x hx) m
  have hQformula := iterateMap_affineGerm_formula
    (T := returnedQ C L) (p := G.p)
    (scale := b) (cap := s) (radius := F.germ_radius)
    hb hs.le F.germ_radius_pos (by
      intro t ht htbound x hx
      exact F.germ_B t ht (by simpa [s] using htbound) x hx) n
  simp only [SameGermOnDirectedSide, G.side_direction, G.side_base,
    SameOneSidedGermAt]
  refine ⟨q, hpq, ?_⟩
  intro x hx
  let t : ℝ := (x : ℝ) - (G.p : ℝ)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact sub_nonneg.mpr hx.1
  have htRadius : t ≤ radius := by
    have hxq : (x : ℝ) ≤ (q : I) := hx.2
    change (x : ℝ) ≤ (G.p : ℝ) + radius at hxq
    dsimp [t]
    linarith
  have hxCoord : (x : ℝ) = (G.p : ℝ) + t := by
    dsimp [t]
    ring
  have hPm := hPformula t ht0 (by simpa [radius]) x hxCoord
  have htRadiusQ : t ≤ F.germ_radius / b ^ n := by
    rw [← hscale]
    exact htRadius
  have hQn := hQformula t ht0 htRadiusQ x hxCoord
  apply Subtype.ext
  rw [hPm, hQn, hscale]

/-- The germ equality globalizes, so equal powers of returned scales force
equal returned maps. -/
theorem returnedIterates_eq_of_scalePowers_eq
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hscale : (returnedScaleP C L) ^ m =
      (returnedScaleQ C L) ^ n) :
    iterateMap (returnedP C L) m =
      iterateMap (returnedQ C L) n := by
  have hsame := returnedIterates_sameGerm_of_scalePowers_eq F hm hn hscale
  have hAR : Function.Commute (returnedP C L) (returnedProduct C L) := by
    intro x
    dsimp [returnedProduct]
    exact congrArg (returnedP C L) (F.properties.commute x)
  have hBR : Function.Commute (returnedQ C L) (returnedProduct C L) := by
    intro x
    dsimp [returnedProduct]
    exact (F.properties.commute (returnedQ C L x)).symm
  apply centralizer_germ_globalization F hirreducible
  · exact IntervalMap.continuous_iterate
      F.properties.constantSlope_A.continuous m
  · exact IntervalMap.continuous_iterate
      F.properties.constantSlope_B.continuous n
  · simpa [iterateMap] using hAR.iterate_left m
  · simpa [iterateMap] using hBR.iterate_left n
  · exact hsame

/-- Iterating an iterate multiplies its exponents. -/
theorem iterateMap_iterateMap (T : IntervalMap) (m n : ℕ) :
    iterateMap (iterateMap T m) n = iterateMap T (m * n) := by
  exact (Function.iterate_mul T m n).symm

/-! ## F8: common-positive-iterate contradiction and final fold data -/

/-- Local spelling of the standalone inverse-limit theorem used below. -/
theorem commonPositiveIterate_standalone_dependency
    {F G : IntervalMap}
    (hF : Continuous F) (hG : Continuous G)
    (hcomm : Function.Commute F G)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hpowers : iterateMap F m = iterateMap G n) :
    HasCommonFixedPoint F G := by
  exact common_positive_iterate hF hG hcomm hm hn hpowers

/-- Equality of positive returned scale powers would give equal positive
original iterates and hence a forbidden common fixed point. -/
theorem returnedScales_multiplicativelyIndependent
    {C : NormalizedConstantSlopeCounterexample} {bound L : ℕ}
    {X : ProductFixedSetPackage C bound}
    {G : RepellingGapData C bound X}
    (F : FactorialReturnGermData C bound L X G)
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L) :
    MultiplicativelyIndependent
      (returnedScaleP C L) (returnedScaleQ C L) := by
  intro m n hm hn hscale
  have hreturned := returnedIterates_eq_of_scalePowers_eq
    F hirreducible hm hn hscale
  have horiginal :
      iterateMap C.P (L * m) = iterateMap C.Q (L * n) := by
    rw [← iterateMap_iterateMap C.P L m,
      ← iterateMap_iterateMap C.Q L n]
    exact hreturned
  have hLm : 0 < L * m := Nat.mul_pos F.properties.L_pos hm
  have hLn : 0 < L * n := Nat.mul_pos F.properties.L_pos hn
  exact C.no_common_fixed_point
    (commonPositiveIterate_standalone_dependency
      C.finitePiece_P.continuous C.finitePiece_Q.continuous C.commute
      hLm hLn horiginal)

/-- F1--F8 assembled.  Reflection is exposed explicitly because the
manuscript normalizes the chosen gap by `x ↦ 1-x` before launching the
right-directed ray. -/
theorem twoScaleFoldData_exists_of_extremal
    (C : NormalizedConstantSlopeCounterexample) (bound L : ℕ)
    (hL : L = Nat.factorial (2 * bound))
    (hbound : (fixedPoints C.product).ncard ≤ bound)
    (hirreducible : ReturnedPowersIrreducible C.P C.Q L) :
    ∃ C' : NormalizedConstantSlopeCounterexample,
      IsOrientationVariant C C' ∧
      ReturnedPowersIrreducible C'.P C'.Q L ∧
      Nonempty
        (TwoScaleFoldData
          (returnedP C' L) (returnedQ C' L)
          (returnedScaleP C' L) (returnedScaleQ C' L)) := by
  obtain ⟨C', hvariant, hirreducible', X, hG⟩ :=
    orientedRepellingGap_exists C bound L hbound hirreducible
  obtain ⟨G⟩ := hG
  obtain ⟨F⟩ := factorialReturnGermData_exists G hL
  obtain ⟨N⟩ := nestedReturnedIntervalsData_exists F
  obtain ⟨S⟩ := stabilizedRayData_exists F N
  have hindependent :=
    returnedScales_multiplicativelyIndependent F hirreducible'
  refine ⟨C', hvariant, hirreducible', ⟨{
    commute := F.properties.commute
    finitePiece_A := F.properties.finitePiece_A
    finitePiece_B := F.properties.finitePiece_B
    onto_A := F.properties.onto_A
    onto_B := F.properties.onto_B
    constantSlope_A := F.properties.constantSlope_A
    constantSlope_B := F.properties.constantSlope_B
    one_lt_a := F.properties.one_lt_a
    one_lt_b := F.properties.one_lt_b
    scales_independent := hindependent
    base := G.p
    ray := S.ray
    continuousOn_ray := S.continuousOn_ray
    initial_radius := F.germ_radius
    initial_radius_pos := F.germ_radius_pos
    initial_unit_germ := S.initial_unit_germ
    locally_unit_speed := S.locally_unit_speed
    return_A := S.return_A
    return_B := S.return_B
    dense_nonnegative_range := stabilizedRay_dense S hirreducible' }⟩⟩

end CommutingIntervalSimplified
