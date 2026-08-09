import CommutingInterval.DynamicsDefs
import CommutingInterval.ExpandingFixedPoints
import CommutingInterval.Kopell
import CommutingInterval.Denjoy
import CommutingInterval.DenjoyKoksma
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The one-sided orbit line and orbit-circle dichotomy

This module records the complete interface for the manuscript's local
`C^{1+BV}` branch.  Proofs are intentionally left as tracked proof states;
the definitions keep the physical one-sided germ, its direct-limit orbit
line, the selected degree-one lifts, and all regularity assumptions separate.

The existing mathlib type `CircleDeg1Lift` is used for monotone maps of `ℝ`
which commute with unit translation.  Its units are precisely the bundled
invertible lifts needed here, and mathlib's translation number therefore has
the correct normalization `τ(t ↦ t + 1) = 1`.
-/

namespace CommutingInterval

open Function Set Filter MeasureTheory intervalIntegral
open scoped BigOperators Topology

/-! ## Germ relations and signed germ powers -/

/-- The identity interval map. -/
def identityIntervalMap : IntervalMap := fun x => x

/-- Two maps commute as right germs at `p`. -/
def RightGermCommute (p : I) (F G : IntervalMap) : Prop :=
  SameOneSidedGermAt .right p (F ∘ G) (G ∘ F)

/-- `F` has no fixed point on some punctured right neighborhood of `p`. -/
def HasNoRightFixedPointNear (F : IntervalMap) (p : I) : Prop :=
  ∃ q : I, p < q ∧ ∀ x ∈ Set.Ioc p q, F x ≠ x

/-- `F` moves every point strictly right on some punctured right
neighborhood of `p`. -/
def MovesStrictlyRightNear (F : IntervalMap) (p : I) : Prop :=
  ∃ q : I, p < q ∧ ∀ x ∈ Set.Ioc p q, x < F x

/-- `F` and `G` are mutually inverse as right germs at `p`. -/
def AreInverseRightGermsAt (p : I) (F G : IntervalMap) : Prop :=
  SameOneSidedGermAt .right p (F ∘ G) identityIntervalMap ∧
    SameOneSidedGermAt .right p (G ∘ F) identityIntervalMap

/--
`H` agrees with the signed `z`-th iterate of `F` as a right germ.

For negative `z`, the predicate explicitly quantifies a representative of
the inverse germ.  This is necessary because an interval self-map need not
have a global inverse even though its selected local germ is a diffeomorphism.
-/
def SameAsSignedRightGermIterateAt (p : I) (H F : IntervalMap) (z : ℤ) : Prop :=
  if 0 ≤ z then
    SameOneSidedGermAt .right p H (iterateMap F z.toNat)
  else
    ∃ FInv : IntervalMap,
      AreInverseRightGermsAt p F FInv ∧
        SameOneSidedGermAt .right p H (iterateMap FInv z.natAbs)

/-! ## The ordered physical end and selected line lifts -/

/--
An ordered coordinate identifying a punctured right neighborhood of `p`
with a negative half-line.  `coord` and `point` are total functions only to
avoid pervasive subtype coercions; all inverse and order assertions are
restricted to the displayed physical domain and to `(-∞, top)`.
-/
structure RightOrbitLineEmbedding (p : I) where
  /-- Right endpoint of the physical germ representative. -/
  rightEnd : I
  /-- The physical representative is nondegenerate. -/
  base_lt_rightEnd : p < rightEnd
  /-- Upper endpoint of the corresponding negative half-line. -/
  top : ℝ
  /-- Coordinate on physical interval points. -/
  coord : I → ℝ
  /-- Inverse coordinate, used only below `top`. -/
  point : ℝ → I
  /-- The coordinate preserves the physical order. -/
  coord_strictMono : StrictMonoOn coord (Set.Ioo p rightEnd)
  /-- Physical points have coordinate below `top`. -/
  coord_lt_top : MapsTo coord (Set.Ioo p rightEnd) (Set.Iio top)
  /-- Every parameter below `top` represents a physical punctured-side point. -/
  point_mem : ∀ s < top, point s ∈ Set.Ioo p rightEnd
  /-- `point` is a left inverse on the physical representative. -/
  point_coord : ∀ x ∈ Set.Ioo p rightEnd, point (coord x) = x
  /-- `coord` is a left inverse on the negative half-line. -/
  coord_point : ∀ s < top, coord (point s) = s

/-- An invertible monotone degree-one lift of a circle homeomorphism. -/
abbrev CircleHomeomorphismLift := Units CircleDeg1Lift

/-- The underlying real function of an invertible degree-one lift. -/
def circleLiftFun (F : CircleHomeomorphismLift) : ℝ → ℝ :=
  (F : CircleDeg1Lift)

/-- The normalized translation number of an invertible degree-one lift. -/
noncomputable def selectedTranslationNumber (F : CircleHomeomorphismLift) : ℝ :=
  (F : CircleDeg1Lift).translationNumber

/-- `C^{1+BV}` regularity on one period of a selected lift. -/
def IsC1BVUnitLift (F : CircleHomeomorphismLift) : Prop :=
  ContDiff ℝ 1 (circleLiftFun F) ∧
    (∀ x : ℝ, 0 < deriv (circleLiftFun F) x) ∧
    BoundedVariationOn
      (fun x : ℝ => Real.log (deriv (circleLiftFun F) x))
      (Set.Icc (0 : ℝ) 1)

/-- A selected degree-one line lift which agrees with a physical right germ
on a sufficiently far-left tail. -/
structure RightGermLineLift {p : I} (E : RightOrbitLineEmbedding p)
    (F : IntervalMap) where
  /-- The selected invertible degree-one lift. -/
  lift : CircleHomeomorphismLift
  /-- The physical intertwining identity is valid below this parameter. -/
  tailBound : ℝ
  /-- The tail lies in the coordinate half-line. -/
  tailBound_lt_top : tailBound < E.top
  /-- The physical map stays in the displayed representative on that tail. -/
  image_mem : ∀ s < tailBound, F (E.point s) ∈ Set.Ioo p E.rightEnd
  /-- Exact agreement of the physical germ with the selected lift. -/
  intertwines : ∀ s < tailBound,
    E.coord (F (E.point s)) = circleLiftFun lift s

/--
The direct-limit orbit line simultaneously carrying `f`, `A`, and `B`.
The chosen coordinate normalizes `f` to unit translation.  The product
identity is exact on the selected lifts, not merely modulo an integer.
-/
structure OneSidedOrbitLineModel
    (f A B : IntervalMap) (p : I) (d : ℕ) where
  /-- Ordered identification of the physical punctured side with a negative end. -/
  embedding : RightOrbitLineEmbedding p
  /-- Selected lift of the repelling germ `f`. -/
  fAction : RightGermLineLift embedding f
  /-- Selected lift of `A`. -/
  AAction : RightGermLineLift embedding A
  /-- Selected lift of `B`. -/
  BAction : RightGermLineLift embedding B
  /-- The deck map is unit translation in the chosen coordinate. -/
  f_is_unit_translation : ∀ s : ℝ, circleLiftFun fAction.lift s = s + 1
  /-- The selected `A` and `B` lifts commute exactly. -/
  A_B_commute : Function.Commute
    (circleLiftFun AAction.lift) (circleLiftFun BAction.lift)
  /-- Their exact selected product is translation by `d`. -/
  A_B_product : ∀ s : ℝ,
    circleLiftFun AAction.lift (circleLiftFun BAction.lift s) = s + d
  /-- The induced `A` circle diffeomorphism has the Denjoy regularity. -/
  regular_A : IsC1BVUnitLift AAction.lift
  /-- The induced `B` circle diffeomorphism has the same regularity. -/
  regular_B : IsC1BVUnitLift BAction.lift

/-- A line lift intertwines every finite physical iterate as long as the
whole lifted orbit segment remains in its displayed tail. -/
private theorem RightGermLineLift.iterate_intertwines
    {p : I} {E : RightOrbitLineEmbedding p} {F : IntervalMap}
    (L : RightGermLineLift E F) {s : ℝ} {n : ℕ}
    (horbit : ∀ i : ℕ, i ≤ n →
      (((L.lift : CircleDeg1Lift) ^ i) s) < L.tailBound) :
    iterateMap F n (E.point s) ∈ Set.Ioo p E.rightEnd ∧
      E.coord (iterateMap F n (E.point s)) =
        ((L.lift : CircleDeg1Lift) ^ n) s := by
  induction n with
  | zero =>
      have hsTail := horbit 0 (by omega)
      have hsTop : s < E.top := hsTail.trans L.tailBound_lt_top
      constructor
      · simpa [iterateMap] using E.point_mem s hsTop
      · simpa [iterateMap] using E.coord_point s hsTop
  | succ n ih =>
      have hprevious := ih (fun i hi ↦ horbit i (by omega))
      let t : ℝ := ((L.lift : CircleDeg1Lift) ^ n) s
      have htTail : t < L.tailBound := horbit n (by omega)
      have hpoint : E.point t = iterateMap F n (E.point s) := by
        dsimp [t]
        rw [← hprevious.2]
        exact E.point_coord _ hprevious.1
      have hpoint' : E.point t = F^[n] (E.point s) := by
        simpa [iterateMap] using hpoint
      have himage := L.image_mem t htTail
      have hintertwines := L.intertwines t htTail
      constructor
      · rw [iterateMap, Function.iterate_succ_apply']
        rw [← hpoint']
        exact himage
      · rw [iterateMap, Function.iterate_succ_apply']
        rw [← hpoint', hintertwines]
        simp [t, circleLiftFun, pow_succ']

/-- Two successive physical germ actions intertwine with the product of
their selected line lifts whenever both steps remain in their tails. -/
private theorem RightGermLineLift.comp_intertwines
    {p : I} {E : RightOrbitLineEmbedding p}
    {F G : IntervalMap}
    (LF : RightGermLineLift E F) (LG : RightGermLineLift E G)
    {s : ℝ} (hsG : s < LG.tailBound)
    (hGsF : circleLiftFun LG.lift s < LF.tailBound) :
    (F ∘ G) (E.point s) ∈ Set.Ioo p E.rightEnd ∧
      E.coord ((F ∘ G) (E.point s)) =
        circleLiftFun LF.lift (circleLiftFun LG.lift s) := by
  have hGmem := LG.image_mem s hsG
  have hGcoord := LG.intertwines s hsG
  have hpointG :
      E.point (circleLiftFun LG.lift s) = G (E.point s) := by
    rw [← hGcoord]
    exact E.point_coord _ hGmem
  have hFmem := LF.image_mem (circleLiftFun LG.lift s) hGsF
  have hFcoord := LF.intertwines (circleLiftFun LG.lift s) hGsF
  constructor
  · simpa [Function.comp_apply, hpointG] using hFmem
  · simpa [Function.comp_apply, hpointG] using hFcoord

/-- Powers of the normalized deck lift are the corresponding integral
translations. -/
private theorem circleLift_pow_apply_of_unitTranslation
    (F : CircleHomeomorphismLift)
    (hF : ∀ s : ℝ, circleLiftFun F s = s + 1) :
    ∀ (n : ℕ) (s : ℝ),
      ((F : CircleDeg1Lift) ^ n) s = s + n := by
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
      intro s
      rw [pow_succ']
      change circleLiftFun F (((F : CircleDeg1Lift) ^ n) s) =
        s + (n + 1 : ℕ)
      rw [hF, ih]
      push_cast
      ring

/-- Degree-one lifts agreeing on a far-left tail agree everywhere. -/
private theorem circleDeg1Lift_ext_of_eqOn_Iio
    (F G : CircleDeg1Lift) {t : ℝ}
    (h : ∀ s < t, F s = G s) :
    F = G := by
  apply CircleDeg1Lift.ext
  intro x
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (x - t)
  have hxn : x - n < t := by
    have hnR : x - t < (n : ℝ) := by exact_mod_cast hn
    linarith
  have heq := h (x - n) hxn
  calc
    F x = F ((x - (n : ℝ)) + (n : ℝ)) := by
      congr 1
      ring
    _ = F (x - n) + n := by
      simpa using F.map_add_nat (x - n) n
    _ = G (x - n) + n := by rw [heq]
    _ = G ((x - (n : ℝ)) + (n : ℝ)) := by
      symm
      simpa using G.map_add_nat (x - n) n
    _ = G x := by
      congr 1
      ring

/-! ## Analytic lemmas -/

/-- Package a `C¹` ambient extension with positive derivative at the base
into the closed one-sided representative used throughout the formalization.
All shrinking needed to make `C¹` regularity and derivative positivity
uniform is performed here, so later germ-composition and inverse lemmas can
work with point-local calculus data. -/
private theorem hasRightGermC1Diffeomorphism_of_local_extension
    {T : IntervalMap} {p q : I} {extension : ℝ → ℝ}
    (hpq : p < q)
    (hC1 : ContDiffAt ℝ 1 extension (p : ℝ))
    (hderiv : 0 < deriv extension (p : ℝ))
    (hagrees : Set.EqOn (fun y : I => (T y : ℝ))
      (fun y : I => extension y) (Set.Icc p q)) :
    HasRightGermC1Diffeomorphism T p := by
  obtain ⟨u, hu, hC1u⟩ :=
    hC1.contDiffOn (m := (1 : ℕ∞)) le_rfl (by simp)
  obtain ⟨v, hvu, hvOpen, hpv⟩ := mem_nhds_iff.mp hu
  have hC1v : ContDiffOn ℝ 1 extension v := hC1u.mono hvu
  have hderivContinuous : ContinuousOn (deriv extension) v :=
    hC1v.continuousOn_deriv_of_isOpen hvOpen (by norm_num)
  let good : Set ℝ := v ∩ deriv extension ⁻¹' Set.Ioi 0
  have hgoodOpen : IsOpen good := by
    dsimp [good]
    exact hderivContinuous.isOpen_inter_preimage hvOpen isOpen_Ioi
  have hpgood : (p : ℝ) ∈ good := ⟨hpv, hderiv⟩
  have hgoodNhds : good ∈ 𝓝 (p : ℝ) := hgoodOpen.mem_nhds hpgood
  obtain ⟨s, hps, hIccGood⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (mem_nhdsWithin_of_mem_nhds hgoodNhds)
  have hpmin : (p : ℝ) < min s (q : ℝ) := by
    exact lt_min hps hpq
  obtain ⟨r, hpr, hrmin⟩ := exists_between hpmin
  have hrs : r < s := hrmin.trans_le (min_le_left _ _)
  have hrq : r < (q : ℝ) := hrmin.trans_le (min_le_right _ _)
  let rI : I := ⟨r, ⟨p.property.1.trans hpr.le,
    hrq.le.trans q.property.2⟩⟩
  refine ⟨{
    rightEnd := rI
    base_lt_rightEnd := hpr
    extension := extension
    neighborhood := good
    isOpen_neighborhood := hgoodOpen
    segment_subset := ?_
    agrees := ?_
    contDiff_one := ?_
    deriv_pos := ?_ }⟩
  · intro y hy
    exact hIccGood ⟨hy.1, hy.2.trans hrs.le⟩
  · intro y hy
    apply hagrees
    exact ⟨hy.1, hy.2.trans hrq.le⟩
  · exact hC1v.mono (inter_subset_left)
  · intro y hy
    exact (hIccGood ⟨hy.1, hy.2.trans hrs.le⟩).2

/-- Orientation-preserving right `C¹` germs are closed under composition
when both factors fix the base. -/
private theorem hasRightGermC1Diffeomorphism_comp
    {F G : IntervalMap} {p : I}
    (hFfixed : IsFixedPoint F p) (hGfixed : IsFixedPoint G p)
    (gF : RightGermC1Diffeomorphism F p)
    (gG : RightGermC1Diffeomorphism G p) :
    HasRightGermC1Diffeomorphism (F ∘ G) p := by
  have hpF : (p : ℝ) ∈ Set.Icc (p : ℝ) (gF.rightEnd : ℝ) :=
    ⟨le_rfl, gF.base_lt_rightEnd.le⟩
  have hpG : (p : ℝ) ∈ Set.Icc (p : ℝ) (gG.rightEnd : ℝ) :=
    ⟨le_rfl, gG.base_lt_rightEnd.le⟩
  have hFextp : gF.extension (p : ℝ) = (p : ℝ) := by
    calc
      gF.extension (p : ℝ) = (F p : ℝ) := (gF.agrees ⟨le_rfl,
        gF.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hFfixed
  have hGextp : gG.extension (p : ℝ) = (p : ℝ) := by
    calc
      gG.extension (p : ℝ) = (G p : ℝ) := (gG.agrees ⟨le_rfl,
        gG.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hGfixed
  have hFC1 : ContDiffAt ℝ 1 gF.extension (p : ℝ) :=
    gF.contDiff_one.contDiffAt
      (gF.isOpen_neighborhood.mem_nhds (gF.segment_subset hpF))
  have hGC1 : ContDiffAt ℝ 1 gG.extension (p : ℝ) :=
    gG.contDiff_one.contDiffAt
      (gG.isOpen_neighborhood.mem_nhds (gG.segment_subset hpG))
  have hFC1image : ContDiffAt ℝ 1 gF.extension
      (gG.extension (p : ℝ)) := by simpa [hGextp] using hFC1
  have hcompC1 : ContDiffAt ℝ 1 (gF.extension ∘ gG.extension)
      (p : ℝ) := hFC1image.comp (p : ℝ) hGC1
  have hFderiv : HasDerivAt gF.extension (deriv gF.extension (p : ℝ))
      (p : ℝ) := hFC1.differentiableAt_one.hasDerivAt
  have hGderiv : HasDerivAt gG.extension (deriv gG.extension (p : ℝ))
      (p : ℝ) := hGC1.differentiableAt_one.hasDerivAt
  have hFderivImage : HasDerivAt gF.extension
      (deriv gF.extension (p : ℝ)) (gG.extension (p : ℝ)) := by
    simpa [hGextp] using hFderiv
  have hcompDeriv := hFderivImage.comp (p : ℝ) hGderiv
  have hcompDerivPos :
      0 < deriv (gF.extension ∘ gG.extension) (p : ℝ) := by
    rw [hcompDeriv.deriv]
    exact mul_pos (gF.deriv_pos _ hpF) (gG.deriv_pos _ hpG)
  have hGnearF : gG.extension ⁻¹' Set.Iio (gF.rightEnd : ℝ) ∈
      𝓝 (p : ℝ) := by
    apply hGC1.continuousAt
    rw [hGextp]
    exact Iio_mem_nhds gF.base_lt_rightEnd
  obtain ⟨s, hps, hIccS⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (mem_nhdsWithin_of_mem_nhds hGnearF)
  have hpmin : (p : ℝ) < min s (gG.rightEnd : ℝ) :=
    lt_min hps gG.base_lt_rightEnd
  obtain ⟨r, hpr, hrmin⟩ := exists_between hpmin
  have hrs : r < s := hrmin.trans_le (min_le_left _ _)
  have hrG : r < (gG.rightEnd : ℝ) :=
    hrmin.trans_le (min_le_right _ _)
  let q : I := ⟨r, ⟨p.property.1.trans hpr.le,
    hrG.le.trans gG.rightEnd.property.2⟩⟩
  have hGcontinuous : ContinuousOn gG.extension
      (Set.Icc (p : ℝ) (gG.rightEnd : ℝ)) :=
    gG.contDiff_one.continuousOn.mono gG.segment_subset
  have hGstrict : StrictMonoOn gG.extension
      (Set.Icc (p : ℝ) (gG.rightEnd : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hGcontinuous
    intro y hy
    exact gG.deriv_pos y (interior_subset hy)
  have hpq : p < q := hpr
  apply hasRightGermC1Diffeomorphism_of_local_extension
      (p := p) (q := q) (extension := gF.extension ∘ gG.extension)
      hpq hcompC1 hcompDerivPos
  intro y hy
  have hyG : (y : ℝ) ∈ Set.Icc (p : ℝ) (gG.rightEnd : ℝ) :=
    ⟨hy.1, hy.2.trans hrG.le⟩
  have hGagree : (G y : ℝ) = gG.extension y :=
    gG.agrees ⟨hy.1, hy.2.trans hrG.le⟩
  have hGlow : (p : ℝ) ≤ gG.extension y := by
    rw [← hGextp]
    exact hGstrict.monotoneOn hpG hyG hy.1
  have hGhigh : gG.extension y ≤ (gF.rightEnd : ℝ) := by
    have hyr : (y : ℝ) ≤ r := hy.2
    exact (hIccS ⟨hy.1, hyr.trans hrs.le⟩).le
  have hGyF : G y ∈ Set.Icc p gF.rightEnd := by
    constructor
    · exact hGlow.trans_eq hGagree.symm
    · exact hGagree.trans_le hGhigh
  change (F (G y) : ℝ) = gF.extension (gG.extension y)
  calc
    (F (G y) : ℝ) = gF.extension (G y : ℝ) := gF.agrees hGyF
    _ = gF.extension (gG.extension y) := congrArg gF.extension hGagree

/-- Every positive iterate of an orientation-preserving right `C¹` germ is
again such a germ.  The zero iterate is represented by the identity. -/
private theorem hasRightGermC1Diffeomorphism_iterate
    {F : IntervalMap} {p : I} (hFfixed : IsFixedPoint F p)
    (gF : RightGermC1Diffeomorphism F p) :
    ∀ n : ℕ, HasRightGermC1Diffeomorphism (iterateMap F n) p := by
  have hIterFixed : ∀ k : ℕ, IsFixedPoint (iterateMap F k) p := by
    intro k
    induction k with
    | zero => simp [IsFixedPoint, iterateMap]
    | succ k hk =>
        simp only [IsFixedPoint, iterateMap,
          Function.iterate_succ_apply'] at hk ⊢
        rw [hk, hFfixed]
  intro n
  induction n with
  | zero =>
      refine ⟨{
        rightEnd := gF.rightEnd
        base_lt_rightEnd := gF.base_lt_rightEnd
        extension := id
        neighborhood := Set.univ
        isOpen_neighborhood := isOpen_univ
        segment_subset := fun _ _ => Set.mem_univ _
        agrees := ?_
        contDiff_one := contDiff_id.contDiffOn
        deriv_pos := ?_ }⟩
      · intro y _hy
        simp [iterateMap, identityIntervalMap]
      · intro y _hy
        simp
  | succ n ih =>
      rcases ih with ⟨gIter⟩
      simpa [iterateMap, Function.iterate_succ_apply'] using
        hasRightGermC1Diffeomorphism_comp
          (hIterFixed n) hFfixed gIter gF

/-- A right orientation-preserving `C¹` germ fixing its base has a local
inverse which can be represented by an interval self-map; the representative
inverse is again an orientation-preserving right `C¹` germ. -/
private theorem exists_c1_rightGerm_inverse
    {F : IntervalMap} {p : I} (hFfixed : IsFixedPoint F p)
    (gF : RightGermC1Diffeomorphism F p) :
    ∃ FInv : IntervalMap,
      IsFixedPoint FInv p ∧
      AreInverseRightGermsAt p F FInv ∧
      HasRightGermC1Diffeomorphism FInv p := by
  have hpF : (p : ℝ) ∈ Set.Icc (p : ℝ) (gF.rightEnd : ℝ) :=
    ⟨le_rfl, gF.base_lt_rightEnd.le⟩
  have hFextp : gF.extension (p : ℝ) = (p : ℝ) := by
    calc
      gF.extension (p : ℝ) = (F p : ℝ) :=
        (gF.agrees ⟨le_rfl, gF.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hFfixed
  have hFC1 : ContDiffAt ℝ 1 gF.extension (p : ℝ) :=
    gF.contDiff_one.contDiffAt
      (gF.isOpen_neighborhood.mem_nhds (gF.segment_subset hpF))
  have hFderiv : HasDerivAt gF.extension (deriv gF.extension (p : ℝ))
      (p : ℝ) := hFC1.differentiableAt_one.hasDerivAt
  have hderivPos : 0 < deriv gF.extension (p : ℝ) :=
    gF.deriv_pos _ hpF
  have hderivNe : deriv gF.extension (p : ℝ) ≠ 0 := hderivPos.ne'
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 (deriv gF.extension (p : ℝ)) hderivNe)
  have hFderivEquiv : HasFDerivAt gF.extension
      (e : ℝ →L[ℝ] ℝ) (p : ℝ) := by
    dsimp [e]
    exact hFderiv.hasFDerivAt_equiv hderivNe
  have hOne : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  let hStrict : HasStrictFDerivAt gF.extension
      (e : ℝ →L[ℝ] ℝ) (p : ℝ) :=
    hFC1.hasStrictFDerivAt' hFderivEquiv hOne
  let invExt : ℝ → ℝ := hFC1.localInverse hFderivEquiv hOne
  have hinvC1raw := hFC1.to_localInverse hFderivEquiv hOne
  have hinvC1 : ContDiffAt ℝ 1 invExt (p : ℝ) := by
    simpa [invExt, hFextp] using hinvC1raw
  have hinvExtp : invExt (p : ℝ) = (p : ℝ) := by
    simpa [invExt, hFextp] using
      hFC1.localInverse_apply_image hFderivEquiv hOne
  have hleftInv : ∀ᶠ x in 𝓝 (p : ℝ),
      invExt (gF.extension x) = x := by
    simpa [invExt, hStrict] using hStrict.eventually_left_inverse
  have hrightInv : ∀ᶠ x in 𝓝 (p : ℝ),
      gF.extension (invExt x) = x := by
    simpa [invExt, hStrict, hFextp] using
      hStrict.eventually_right_inverse
  have hinvStrictF : HasStrictFDerivAt invExt
      (e.symm : ℝ →L[ℝ] ℝ) (p : ℝ) := by
    simpa [invExt, hStrict, hFextp] using hStrict.to_localInverse
  have hinvDeriv : HasStrictDerivAt invExt
      (deriv gF.extension (p : ℝ))⁻¹ (p : ℝ) := by
    convert hinvStrictF.hasStrictDerivAt using 1 <;> simp [e]
  have hinvDerivPos : 0 < deriv invExt (p : ℝ) := by
    rw [hinvDeriv.hasDerivAt.deriv]
    exact inv_pos.mpr hderivPos
  let FInv : IntervalMap := fun x =>
    Set.projIcc (0 : ℝ) 1 zero_le_one (invExt (x : ℝ))
  have hFInvFixed : IsFixedPoint FInv p := by
    apply Subtype.ext
    simp [FInv, hinvExtp, Set.projIcc_of_mem, p.property]
  obtain ⟨u, hu, hinvC1u⟩ :=
    hinvC1.contDiffOn (m := (1 : ℕ∞)) le_rfl (by simp)
  obtain ⟨v, hvu, hvOpen, hpv⟩ := mem_nhds_iff.mp hu
  have hinvC1v : ContDiffOn ℝ 1 invExt v := hinvC1u.mono hvu
  have hinvDerivContinuous : ContinuousOn (deriv invExt) v :=
    hinvC1v.continuousOn_deriv_of_isOpen hvOpen (by norm_num)
  let good : Set ℝ := v ∩ deriv invExt ⁻¹' Set.Ioi 0
  have hgoodOpen : IsOpen good := by
    dsimp [good]
    exact hinvDerivContinuous.isOpen_inter_preimage hvOpen isOpen_Ioi
  have hpgood : (p : ℝ) ∈ good := ⟨hpv, hinvDerivPos⟩
  have hgoodNhds : good ∈ 𝓝 (p : ℝ) := hgoodOpen.mem_nhds hpgood
  have hinvUpper : invExt ⁻¹' Set.Iio (gF.rightEnd : ℝ) ∈
      𝓝 (p : ℝ) := by
    apply hinvC1.continuousAt
    rw [hinvExtp]
    exact Iio_mem_nhds gF.base_lt_rightEnd
  let localSet : Set ℝ := {x |
    x ∈ good ∧
    invExt x < (gF.rightEnd : ℝ) ∧
    invExt (gF.extension x) = x ∧
    gF.extension (invExt x) = x}
  have hlocalNhds : localSet ∈ 𝓝 (p : ℝ) := by
    dsimp [localSet]
    filter_upwards [hgoodNhds, hinvUpper, hleftInv, hrightInv] with
      x hxgood hxupper hxleft hxright
    exact ⟨hxgood, hxupper, hxleft, hxright⟩
  obtain ⟨s, hps, hIccLocal⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (mem_nhdsWithin_of_mem_nhds hlocalNhds)
  have hpmin : (p : ℝ) < min s (gF.rightEnd : ℝ) :=
    lt_min hps gF.base_lt_rightEnd
  obtain ⟨r, hpr, hrmin⟩ := exists_between hpmin
  have hrs : r < s := hrmin.trans_le (min_le_left _ _)
  have hrF : r < (gF.rightEnd : ℝ) :=
    hrmin.trans_le (min_le_right _ _)
  let q : I := ⟨r, ⟨p.property.1.trans hpr.le,
    hrF.le.trans gF.rightEnd.property.2⟩⟩
  have hpq : p < q := hpr
  have hIccGood : Set.Icc (p : ℝ) r ⊆ good := by
    intro x hx
    exact (hIccLocal ⟨hx.1, hx.2.trans hrs.le⟩).1
  have hinvContinuous : ContinuousOn invExt (Set.Icc (p : ℝ) r) :=
    hinvC1v.continuousOn.mono (hIccGood.trans inter_subset_left)
  have hinvStrict : StrictMonoOn invExt (Set.Icc (p : ℝ) r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hinvContinuous
    intro x hx
    exact (hIccGood (interior_subset hx)).2
  have hpReal : (p : ℝ) ∈ Set.Icc (p : ℝ) r := ⟨le_rfl, hpr.le⟩
  have hinv_mem (x : ℝ) (hx : x ∈ Set.Icc (p : ℝ) r) :
      invExt x ∈ Set.Icc (0 : ℝ) 1 := by
    have hlower : (p : ℝ) ≤ invExt x := by
      rw [← hinvExtp]
      exact hinvStrict.monotoneOn hpReal hx hx.1
    have hupper : invExt x < (gF.rightEnd : ℝ) :=
      (hIccLocal ⟨hx.1, hx.2.trans hrs.le⟩).2.1
    exact ⟨p.property.1.trans hlower, hupper.le.trans gF.rightEnd.property.2⟩
  have hFInvAgree : Set.EqOn (fun y : I => (FInv y : ℝ))
      (fun y : I => invExt y) (Set.Icc p q) := by
    intro y hy
    have hyr : (y : ℝ) ≤ r := hy.2
    change ((Set.projIcc (0 : ℝ) 1 zero_le_one (invExt (y : ℝ)) : I) : ℝ) =
      invExt (y : ℝ)
    rw [Set.projIcc_of_mem zero_le_one
      (hinv_mem (y : ℝ) ⟨hy.1, hyr⟩)]
  have hFInvC1 : HasRightGermC1Diffeomorphism FInv p :=
    hasRightGermC1Diffeomorphism_of_local_extension
      (p := p) (q := q) (extension := invExt)
      hpq hinvC1 hinvDerivPos hFInvAgree
  have hleftGerm : SameOneSidedGermAt .right p
      (F ∘ FInv) identityIntervalMap := by
    refine ⟨q, hpq, ?_⟩
    intro x hx
    have hxr : (x : ℝ) ∈ Set.Icc (p : ℝ) r := ⟨hx.1, hx.2⟩
    have hlocal := hIccLocal ⟨hxr.1, hxr.2.trans hrs.le⟩
    have hInvRange : FInv x ∈ Set.Icc p gF.rightEnd := by
      have hlow : (p : ℝ) ≤ invExt x := by
        rw [← hinvExtp]
        exact hinvStrict.monotoneOn hpReal hxr hxr.1
      have hInvEq : (FInv x : ℝ) = invExt x := hFInvAgree hx
      constructor
      · exact hlow.trans_eq hInvEq.symm
      · exact hInvEq.trans_le hlocal.2.1.le
    apply Subtype.ext
    change (F (FInv x) : ℝ) = (x : ℝ)
    calc
      (F (FInv x) : ℝ) = gF.extension (FInv x : ℝ) :=
        gF.agrees hInvRange
      _ = gF.extension (invExt x) := congrArg gF.extension (hFInvAgree hx)
      _ = (x : ℝ) := hlocal.2.2.2
  have hrightGerm : SameOneSidedGermAt .right p
      (FInv ∘ F) identityIntervalMap := by
    refine ⟨q, hpq, ?_⟩
    intro x hx
    have hFagree : (F x : ℝ) = gF.extension x :=
      gF.agrees ⟨hx.1, hx.2.trans hrF.le⟩
    have hxr : (x : ℝ) ≤ r := hx.2
    have hlocal := hIccLocal ⟨hx.1, hxr.trans hrs.le⟩
    apply Subtype.ext
    change (FInv (F x) : ℝ) = (x : ℝ)
    have harg : invExt (F x : ℝ) = (x : ℝ) := by
      rw [hFagree]
      exact hlocal.2.2.1
    change ((Set.projIcc (0 : ℝ) 1 zero_le_one
      (invExt (F x : ℝ)) : I) : ℝ) = (x : ℝ)
    rw [harg, Set.projIcc_of_mem zero_le_one x.property]
  exact ⟨FInv, hFInvFixed, ⟨hleftGerm, hrightGerm⟩, hFInvC1⟩

/-- Equality on an explicit right-germ representative is equivalent to
eventual equality for the right-neighborhood filter, provided the right side
is nontrivial. -/
private theorem sameRightGerm_iff_eventuallyEq
    {F G : IntervalMap} {p : I} (havailable : ∃ q : I, p < q) :
    SameOneSidedGermAt .right p F G ↔
      F =ᶠ[𝓝[≥] p] G := by
  let B := nhdsGE_basis_of_exists_gt havailable
  constructor
  · rintro ⟨q, hpq, hagree⟩
    apply B.mem_iff.mpr
    refine ⟨q, hpq, ?_⟩
    intro x hx
    exact hagree ⟨hx.1, hx.2.le⟩
  · intro heq
    obtain ⟨q, hpq, hagree⟩ := B.mem_iff.mp heq
    obtain ⟨r, hpr, hrq⟩ := exists_between hpq
    refine ⟨r, hpr, ?_⟩
    intro x hx
    exact hagree ⟨hx.1, hx.2.trans_lt hrq⟩

/-- A positive right `C¹` germ fixing its base preserves the right
neighborhood filter. -/
private theorem RightGermC1Diffeomorphism.tendsto_nhdsGE
    {F : IntervalMap} {p : I} (gF : RightGermC1Diffeomorphism F p)
    (hFfixed : IsFixedPoint F p) :
    Tendsto F (𝓝[≥] p) (𝓝[≥] p) := by
  have hpF : (p : ℝ) ∈ Set.Icc (p : ℝ) (gF.rightEnd : ℝ) :=
    ⟨le_rfl, gF.base_lt_rightEnd.le⟩
  have hFextp : gF.extension (p : ℝ) = (p : ℝ) := by
    calc
      gF.extension (p : ℝ) = (F p : ℝ) :=
        (gF.agrees ⟨le_rfl, gF.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hFfixed
  have hFC1 : ContDiffAt ℝ 1 gF.extension (p : ℝ) :=
    gF.contDiff_one.contDiffAt
      (gF.isOpen_neighborhood.mem_nhds (gF.segment_subset hpF))
  have hFcontinuous : ContinuousOn gF.extension
      (Set.Icc (p : ℝ) (gF.rightEnd : ℝ)) :=
    gF.contDiff_one.continuousOn.mono gF.segment_subset
  have hFstrict : StrictMonoOn gF.extension
      (Set.Icc (p : ℝ) (gF.rightEnd : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hFcontinuous
    intro x hx
    exact gF.deriv_pos x (interior_subset hx)
  let B := nhdsGE_basis_of_exists_gt
    (α := I) ⟨gF.rightEnd, gF.base_lt_rightEnd⟩
  apply B.tendsto_right_iff.mpr
  intro q hpq
  have hnear : gF.extension ⁻¹' Set.Iio (q : ℝ) ∈ 𝓝 (p : ℝ) := by
    apply hFC1.continuousAt
    rw [hFextp]
    exact Iio_mem_nhds hpq
  obtain ⟨s, hps, hIccNear⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (mem_nhdsWithin_of_mem_nhds hnear)
  have hpmin : (p : ℝ) < min s (gF.rightEnd : ℝ) :=
    lt_min hps gF.base_lt_rightEnd
  obtain ⟨r, hpr, hrmin⟩ := exists_between hpmin
  have hrs : r < s := hrmin.trans_le (min_le_left _ _)
  have hrF : r < (gF.rightEnd : ℝ) :=
    hrmin.trans_le (min_le_right _ _)
  let rI : I := ⟨r, ⟨p.property.1.trans hpr.le,
    hrF.le.trans gF.rightEnd.property.2⟩⟩
  apply B.mem_iff.mpr
  refine ⟨rI, hpr, ?_⟩
  intro x hx
  have hxr : (x : ℝ) < r := hx.2
  have hxF : (x : ℝ) ∈ Set.Icc (p : ℝ) (gF.rightEnd : ℝ) :=
    ⟨hx.1, hxr.le.trans hrF.le⟩
  have hFagree : (F x : ℝ) = gF.extension x :=
    gF.agrees ⟨hx.1, hxr.le.trans hrF.le⟩
  have hlower : (p : ℝ) ≤ gF.extension x := by
    rw [← hFextp]
    exact hFstrict.monotoneOn hpF hxF hx.1
  have hupper : gF.extension x < (q : ℝ) :=
    hIccNear ⟨hx.1, hxr.le.trans hrs.le⟩
  constructor
  · exact hlower.trans_eq hFagree.symm
  · exact hFagree.trans_lt hupper

/-- Composition respects equality of right germs when the inner germ is a
positive `C¹` germ fixing the base. -/
private theorem sameRightGerm_comp
    {F F' G G' : IntervalMap} {p : I}
    (hFF' : SameOneSidedGermAt .right p F F')
    (hGG' : SameOneSidedGermAt .right p G G')
    (hGfixed : IsFixedPoint G p)
    (gG : RightGermC1Diffeomorphism G p) :
    SameOneSidedGermAt .right p (F ∘ G) (F' ∘ G') := by
  have havailable : ∃ q : I, p < q :=
    ⟨gG.rightEnd, gG.base_lt_rightEnd⟩
  apply (sameRightGerm_iff_eventuallyEq havailable).2
  have hOuter := (sameRightGerm_iff_eventuallyEq havailable).1 hFF'
  have hInner := (sameRightGerm_iff_eventuallyEq havailable).1 hGG'
  exact (hOuter.comp_tendsto (gG.tendsto_nhdsGE hGfixed)).trans
    (hInner.fun_comp F')

/-- Eventual commutation is inherited by every positive iterate of the
second map. -/
private theorem rightEventuallyEq_commute_iterate
    {F G : IntervalMap} {p : I}
    (hcomm : (F ∘ G) =ᶠ[𝓝[≥] p] (G ∘ F))
    (hGtend : Tendsto G (𝓝[≥] p) (𝓝[≥] p)) :
    ∀ n : ℕ,
      (F ∘ iterateMap G n) =ᶠ[𝓝[≥] p]
        (iterateMap G n ∘ F) := by
  intro n
  induction n with
  | zero =>
      filter_upwards [] with x
      simp [iterateMap]
  | succ n ih =>
      have h₁ := ih.comp_tendsto hGtend
      have h₂ := hcomm.fun_comp (iterateMap G n)
      filter_upwards [h₁, h₂] with x hx₁ hx₂
      simpa [iterateMap, Function.iterate_succ_apply,
        Function.iterate_succ_apply', Function.comp_apply] using
        hx₁.trans hx₂

/-- Iterating two mutually inverse right germs gives mutually inverse
iterated germs.  This orientation cancels `FInv^n` after `F^n`. -/
private theorem rightEventuallyEq_inverse_iterates
    {F FInv : IntervalMap} {p : I}
    (hInvF : (FInv ∘ F) =ᶠ[𝓝[≥] p] identityIntervalMap)
    (hFtend : Tendsto F (𝓝[≥] p) (𝓝[≥] p)) :
    ∀ n : ℕ,
      (iterateMap FInv n ∘ iterateMap F n) =ᶠ[𝓝[≥] p]
        identityIntervalMap := by
  intro n
  induction n with
  | zero =>
      filter_upwards [] with x
      simp [iterateMap, identityIntervalMap]
  | succ n ih =>
      have hmiddle :=
        (hInvF.fun_comp (iterateMap FInv n)).comp_tendsto
          (hFtend.iterate n)
      filter_upwards [hmiddle, ih] with x hxmiddle hxih
      simp only [Function.comp_apply, iterateMap, identityIntervalMap] at hxmiddle hxih ⊢
      rw [(Function.Commute.self_iterate F n).eq x] at hxmiddle
      simpa only [Function.iterate_succ_apply] using hxmiddle.trans hxih

/-- If `A` commutes eventually with `B` and with `C`, then it commutes
eventually with their composite. -/
private theorem rightEventuallyEq_commute_comp
    {A B C : IntervalMap} {p : I}
    (hAB : (A ∘ B) =ᶠ[𝓝[≥] p] (B ∘ A))
    (hAC : (A ∘ C) =ᶠ[𝓝[≥] p] (C ∘ A))
    (hCtend : Tendsto C (𝓝[≥] p) (𝓝[≥] p)) :
    (A ∘ (B ∘ C)) =ᶠ[𝓝[≥] p] ((B ∘ C) ∘ A) := by
  have h₁ := hAB.comp_tendsto hCtend
  have h₂ := hAC.fun_comp B
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact hx₁.trans hx₂

/--
The local bounded-variation Kopell lemma used in the proof.

The endpoint `q` is required to lie in both displayed `C¹` representatives,
so the fixed point and the commuting identities cannot accidentally be
witnessed outside the germ domains.  Only the first germ needs BV regularity,
matching the quoted theorem.
-/
private theorem contraction_iterates_tendsto
    {f : ℝ → ℝ} {p b : ℝ}
    (hfcont : ∀ x ∈ Set.Icc p b, ContinuousAt f x)
    (hfmap : Set.MapsTo f (Set.Icc p b) (Set.Icc p b))
    (hfp : f p = p)
    (hcontract : ∀ x ∈ Set.Ioc p b, f x < x) :
    ∀ x ∈ Set.Icc p b,
      Tendsto (fun n => (f^[n]) x) atTop (𝓝 p) := by
  intro x hx
  let z : ℕ → ℝ := fun n => (f^[n]) x
  have hzmem : ∀ n, z n ∈ Set.Icc p b :=
    fun n => hfmap.iterate n hx
  have hzanti : Antitone z := by
    apply antitone_nat_of_succ_le
    intro n
    rw [show z (n + 1) = f (z n) by
      simp [z, Function.iterate_succ_apply']]
    rcases eq_or_lt_of_le (hzmem n).1 with heq | hlt
    · rw [← heq, hfp]
    · exact (hcontract (z n) ⟨hlt, (hzmem n).2⟩).le
  have hzbdd : BddBelow (Set.range z) := by
    exact ⟨p, by rintro _ ⟨n, rfl⟩; exact (hzmem n).1⟩
  let L : ℝ := sInf (Set.range z)
  have hzlim : Tendsto z atTop (𝓝 L) :=
    tendsto_atTop_ciInf hzanti hzbdd
  have hLmem : L ∈ Set.Icc p b :=
    isClosed_Icc.mem_of_tendsto hzlim (Eventually.of_forall hzmem)
  have hshift : Tendsto (fun n => z (n + 1)) atTop (𝓝 L) :=
    hzlim.comp (tendsto_add_atTop_nat 1)
  have hfzlim : Tendsto (fun n => f (z n)) atTop (𝓝 L) := by
    simpa [z, Function.iterate_succ_apply'] using hshift
  have hf_tend : Tendsto f (𝓝 L) (𝓝 (f L)) := hfcont L hLmem
  have hfix : f L = L :=
    tendsto_nhds_unique (hf_tend.comp hzlim) hfzlim
  have hLp : L = p := by
    apply le_antisymm
    · by_contra hnot
      have hpL : p < L := lt_of_not_ge hnot
      exact (not_lt_of_ge hfix.ge)
        (hcontract L ⟨hpL, hLmem.2⟩)
    · exact hLmem.1
  simpa [hLp] using hzlim

/-- The nonfixed component containing a moved point has fixed endpoints and
the restriction of the increasing map is an order automorphism. -/
private theorem exists_nonfixed_component_orderIso
    {g : ℝ → ℝ} {p y x : ℝ}
    (hcont : ContinuousOn g (Set.Icc p y))
    (hstrict : StrictMonoOn g (Set.Icc p y))
    (hgp : g p = p) (hgy : g y = y)
    (hx : x ∈ Set.Ioo p y) (hxmove : g x ≠ x) :
    ∃ c d : ℝ,
      c < d ∧
      Set.Icc c d ⊆ Set.Icc p y ∧
      Set.Ioo c d ⊆ Set.Ioo p y ∧
      g c = c ∧ g d = d ∧
      (∀ z ∈ Set.Ioo c d, g z ≠ z) ∧
      (∃ z ∈ Set.Ioo c d, g z ≠ z) ∧
      ∃ e : Set.Icc c d ≃o Set.Icc c d,
        ∀ z : Set.Icc c d, (e z : ℝ) = g z := by
  let KL : Set ℝ := {z ∈ Set.Icc p x | g z = z}
  let KR : Set ℝ := {z ∈ Set.Icc x y | g z = z}
  have hpx : p ≤ x := hx.1.le
  have hxy : x ≤ y := hx.2.le
  have hKLclosed : IsClosed KL := by
    dsimp [KL]
    exact isClosed_Icc.isClosed_eq
      (hcont.mono <| Set.Icc_subset_Icc le_rfl hxy) continuousOn_id
  have hKRclosed : IsClosed KR := by
    dsimp [KR]
    exact isClosed_Icc.isClosed_eq
      (hcont.mono <| Set.Icc_subset_Icc hpx le_rfl) continuousOn_id
  have hpKL : p ∈ KL := ⟨⟨le_rfl, hpx⟩, hgp⟩
  have hyKR : y ∈ KR := ⟨⟨hxy, le_rfl⟩, hgy⟩
  have hKLne : KL.Nonempty := ⟨p, hpKL⟩
  have hKRne : KR.Nonempty := ⟨y, hyKR⟩
  have hKLbdd : BddAbove KL := ⟨x, fun z hz => hz.1.2⟩
  have hKRbdd : BddBelow KR := ⟨x, fun z hz => hz.1.1⟩
  let c := sSup KL
  let d := sInf KR
  have hcKL : c ∈ KL := hKLclosed.csSup_mem hKLne hKLbdd
  have hdKR : d ∈ KR := hKRclosed.csInf_mem hKRne hKRbdd
  have hpc : p ≤ c := le_csSup hKLbdd hpKL
  have hcx : c ≤ x := csSup_le hKLne (fun z hz => hz.1.2)
  have hxd : x ≤ d := le_csInf hKRne (fun z hz => hz.1.1)
  have hdy : d ≤ y := csInf_le hKRbdd hyKR
  have hcx_strict : c < x := by
    refine hcx.lt_of_ne ?_
    intro h
    apply hxmove
    rw [← h]
    exact hcKL.2
  have hxd_strict : x < d := by
    refine hxd.lt_of_ne ?_
    intro h
    apply hxmove
    rw [h]
    exact hdKR.2
  have hcd : c < d := hcx_strict.trans hxd_strict
  have hcomponent_mem : Set.Icc c d ⊆ Set.Icc p y := by
    intro z hz
    exact ⟨hpc.trans hz.1, hz.2.trans hdy⟩
  have hinterior_mem : Set.Ioo c d ⊆ Set.Ioo p y := by
    intro z hz
    exact ⟨hpc.trans_lt hz.1, hz.2.trans_le hdy⟩
  have hnofix : ∀ z ∈ Set.Ioo c d, g z ≠ z := by
    intro z hz hzfix
    rcases le_total z x with hzx | hxz
    · have hzKL : z ∈ KL :=
        ⟨⟨hpc.trans hz.1.le, hzx⟩, hzfix⟩
      exact (not_lt_of_ge (le_csSup hKLbdd hzKL)) hz.1
    · have hzKR : z ∈ KR :=
        ⟨⟨hxz, hz.2.le.trans hdy⟩, hzfix⟩
      exact (not_lt_of_ge (csInf_le hKRbdd hzKR)) hz.2
  have hgcont : ContinuousOn g (Set.Icc c d) :=
    hcont.mono hcomponent_mem
  have hgstrict : StrictMonoOn g (Set.Icc c d) :=
    hstrict.mono hcomponent_mem
  have hgmap : Set.MapsTo g (Set.Icc c d) (Set.Icc c d) := by
    intro z hz
    constructor
    · calc
        c = g c := hcKL.2.symm
        _ ≤ g z := hgstrict.monotoneOn ⟨le_rfl, hcd.le⟩ hz hz.1
    · calc
        g z ≤ g d := hgstrict.monotoneOn hz ⟨hcd.le, le_rfl⟩ hz.2
        _ = d := hdKR.2
  have hgsurj : Set.SurjOn g (Set.Icc c d) (Set.Icc c d) := by
    simpa [hcKL.2, hdKR.2] using
      hgcont.surjOn_Icc
        (show c ∈ Set.Icc c d from ⟨le_rfl, hcd.le⟩)
        (show d ∈ Set.Icc c d from ⟨hcd.le, le_rfl⟩)
  let gI : Set.Icc c d → Set.Icc c d :=
    fun z => ⟨g z, hgmap z.property⟩
  have hgIstrict : StrictMono gI := by
    intro z w hzw
    exact hgstrict z.property w.property hzw
  have hgIsurj : Function.Surjective gI := by
    intro z
    obtain ⟨w, hw, hwz⟩ := hgsurj z.property
    exact ⟨⟨w, hw⟩, Subtype.ext hwz⟩
  let e : Set.Icc c d ≃o Set.Icc c d :=
    StrictMono.orderIsoOfSurjective gI hgIstrict hgIsurj
  refine ⟨c, d, hcd, hcomponent_mem, hinterior_mem,
    hcKL.2, hdKR.2, hnofix,
    ⟨x, ⟨hcx_strict, hxd_strict⟩, hxmove⟩, e, ?_⟩
  intro z
  rfl

private structure LocalKopellContractingComponentData
    {u v : IntervalMap} {p q : I}
    (gu : RightGermC1Diffeomorphism u p)
    (gv : RightGermC1Diffeomorphism v p) where
  /-- A single closed representative on which both extensions and the
  interval-map commutation identity are valid. -/
  commonEnd : I
  base_lt_commonEnd : p < commonEnd
  commonEnd_le_u : commonEnd ≤ gu.rightEnd
  commonEnd_le_v : commonEnd ≤ gv.rightEnd
  commonEnd_le_q : commonEnd ≤ q
  u_maps_common : Set.MapsTo gu.extension
    (Set.Icc (p : ℝ) commonEnd) (Set.Icc (p : ℝ) commonEnd)
  v_maps_common : Set.MapsTo gv.extension
    (Set.Icc (p : ℝ) commonEnd) (Set.Icc (p : ℝ) commonEnd)
  extensions_commute : Set.EqOn
    (gu.extension ∘ gv.extension) (gv.extension ∘ gu.extension)
    (Set.Icc (p : ℝ) commonEnd)
  /-- The selected nonfixed component of the second extension. -/
  componentLeft : ℝ
  componentRight : ℝ
  component_nondegenerate : componentLeft < componentRight
  component_mem_common : Set.Icc componentLeft componentRight ⊆
    Set.Icc (p : ℝ) commonEnd
  component_interior_common : Set.Ioo componentLeft componentRight ⊆
    Set.Ioo (p : ℝ) commonEnd
  left_fixed : gv.extension componentLeft = componentLeft
  right_fixed : gv.extension componentRight = componentRight
  component_no_fixed : ∀ x ∈ Set.Ioo componentLeft componentRight,
    gv.extension x ≠ x
  component_moved : ∃ x ∈ Set.Ioo componentLeft componentRight,
    gv.extension x ≠ x
  componentOrderIso : Set.Icc componentLeft componentRight ≃o
    Set.Icc componentLeft componentRight
  componentOrderIso_agrees : ∀ x : Set.Icc componentLeft componentRight,
    (componentOrderIso x : ℝ) = gv.extension x
  /-- Endpoint accumulation and contraction data. -/
  fixedSequence : ℕ → ℝ
  fixedSequence_tendsto : Tendsto fixedSequence atTop (𝓝 (p : ℝ))
  fixedSequence_ne : ∀ i, fixedSequence i ≠ (p : ℝ)
  fixedSequence_fixed : ∀ i,
    gv.extension (fixedSequence i) = fixedSequence i
  orbit_contracts : ∀ x ∈ Set.Ioo componentLeft componentRight,
    Tendsto (fun n ↦ (gu.extension^[n]) x) atTop (𝓝 (p : ℝ))
  /-- The contracting movement and component-image separation used to build
  the antitone fundamental-interval interleaving. -/
  u_contracts : ∀ x ∈ Set.Ioc (p : ℝ) commonEnd,
    gu.extension x < x
  forward_right_fixed : ∀ i,
    gv.extension ((gu.extension^[i]) componentRight) =
      (gu.extension^[i]) componentRight
  forward_components_no_fixed : ∀ i x,
    x ∈ Set.Ioo ((gu.extension^[i]) componentLeft)
      ((gu.extension^[i]) componentRight) → gv.extension x ≠ x
  /-- Every local analytic hypothesis passed to the real contracting core. -/
  g_iter_cont : ∀ n, ContinuousOn (gv.extension^[n])
    (Set.Icc componentLeft componentRight)
  g_iter_diff : ∀ n, DifferentiableOn ℝ (gv.extension^[n])
    (Set.Ioo componentLeft componentRight)
  logDeriv_bv : BoundedVariationOn gu.logDeriv
    (Set.Icc (p : ℝ) commonEnd)
  f_step_diff : ∀ x ∈ Set.Ioo componentLeft componentRight, ∀ k i,
    DifferentiableAt ℝ gu.extension ((gu.extension^[i]) x) ∧
      DifferentiableAt ℝ gu.extension
        ((gu.extension^[i]) ((gv.extension^[k]) x))
  f_step_pos : ∀ x ∈ Set.Ioo componentLeft componentRight, ∀ k i,
    0 < deriv gu.extension ((gu.extension^[i]) x) ∧
      0 < deriv gu.extension ((gu.extension^[i]) ((gv.extension^[k]) x))
  g_iter_pos : ∀ x ∈ Set.Ioo componentLeft componentRight, ∀ k n,
    0 < deriv (gv.extension^[k]) ((gu.extension^[n]) x)
  ordered_interleaving : ∀ x ∈ Set.Ioo componentLeft componentRight, ∀ k,
    ∃ z : ℕ → ℕ → ℝ,
      (∀ n, Monotone (z n) ∨ Antitone (z n)) ∧
      (∀ n j, j ≤ 2 * n → z n j ∈ Set.Icc (p : ℝ) commonEnd) ∧
      (∀ n i, i < n →
        (z n (2 * i) = (gu.extension^[i]) x ∧
          z n (2 * i + 1) =
            (gu.extension^[i]) ((gv.extension^[k]) x)) ∨
        (z n (2 * i) =
            (gu.extension^[i]) ((gv.extension^[k]) x) ∧
          z n (2 * i + 1) = (gu.extension^[i]) x))
  derivative_chain : ∀ x ∈ Set.Ioo componentLeft componentRight, ∀ k n,
    deriv (gv.extension^[k]) ((gu.extension^[n]) x) *
        deriv (gu.extension^[n]) x =
      deriv (gu.extension^[n]) ((gv.extension^[k]) x) *
        deriv (gv.extension^[k]) x

/-- Fixed-point-free positive `C¹` dynamics on a connected right interval
has one constant movement direction. -/
private theorem rightGerm_fixedPointFree_direction
    {u : IntervalMap} {p q : I}
    (gu : RightGermC1Diffeomorphism u p)
    (hpq : p < q)
    (hq_u : q ≤ gu.rightEnd)
    (hu_fixed : IsFixedPoint u p)
    (hu_no_fixed : ∀ x ∈ Set.Ioc p q, u x ≠ x) :
    (∀ x ∈ Set.Ioc p q, (u x : ℝ) < x) ∨
      (∀ x ∈ Set.Ioc p q, (x : ℝ) < u x) := by
  have hsegment : Set.Icc (p : ℝ) (q : ℝ) ⊆ gu.neighborhood := by
    intro x hx
    exact gu.segment_subset ⟨hx.1, hx.2.trans hq_u⟩
  have hcont : ContinuousOn gu.extension (Set.Icc (p : ℝ) (q : ℝ)) :=
    gu.contDiff_one.continuousOn.mono hsegment
  have hdiff : ContinuousOn (fun x : ℝ => gu.extension x - x)
      (Set.Icc (p : ℝ) (q : ℝ)) := hcont.sub continuousOn_id
  have hq_mem : q ∈ Set.Icc p gu.rightEnd := ⟨hpq.le, hq_u⟩
  have hq_agree : gu.extension (q : ℝ) = (u q : ℝ) :=
    (gu.agrees hq_mem).symm
  have hq_ne_real : (u q : ℝ) ≠ (q : ℝ) := by
    intro h
    exact hu_no_fixed q ⟨hpq, le_rfl⟩ (Subtype.ext h)
  rcases lt_or_gt_of_ne hq_ne_real with hq_contracts | hq_expands
  · left
    intro x hx
    have hx_mem : x ∈ Set.Icc p gu.rightEnd :=
      ⟨hx.1.le, hx.2.trans hq_u⟩
    have hx_agree : gu.extension (x : ℝ) = (u x : ℝ) :=
      (gu.agrees hx_mem).symm
    have hx_ne_real : (u x : ℝ) ≠ (x : ℝ) := by
      intro h
      exact hu_no_fixed x hx (Subtype.ext h)
    rcases lt_or_gt_of_ne hx_ne_real with hx_contracts | hx_expands
    · exact hx_contracts
    · exfalso
      have hxq : (x : ℝ) ≤ (q : ℝ) := hx.2
      have hzero_mem : (0 : ℝ) ∈ Set.Icc
          (gu.extension (q : ℝ) - q) (gu.extension (x : ℝ) - x) := by
        constructor
        · rw [hq_agree]
          exact sub_nonpos.mpr hq_contracts.le
        · rw [hx_agree]
          exact sub_nonneg.mpr hx_expands.le
      obtain ⟨c, hc, hczero⟩ := Set.mem_image _ _ _ |>.mp
        (intermediate_value_Icc' (f := fun t : ℝ => gu.extension t - t)
          hxq (hdiff.mono <| Set.Icc_subset_Icc hx.1.le le_rfl) hzero_mem)
      have hc_eq : gu.extension c = c := sub_eq_zero.mp hczero
      let cI : I :=
        ⟨c, ⟨x.property.1.trans hc.1, hc.2.trans q.property.2⟩⟩
      have hcI_mem : cI ∈ Set.Ioc p q := by
        exact ⟨hx.1.trans_le hc.1, hc.2⟩
      apply hu_no_fixed cI hcI_mem
      apply Subtype.ext
      change (u cI : ℝ) = c
      calc
        (u cI : ℝ) = gu.extension c := gu.agrees ⟨hcI_mem.1.le,
          hcI_mem.2.trans hq_u⟩
        _ = c := hc_eq
  · right
    intro x hx
    have hx_mem : x ∈ Set.Icc p gu.rightEnd :=
      ⟨hx.1.le, hx.2.trans hq_u⟩
    have hx_agree : gu.extension (x : ℝ) = (u x : ℝ) :=
      (gu.agrees hx_mem).symm
    have hx_ne_real : (u x : ℝ) ≠ (x : ℝ) := by
      intro h
      exact hu_no_fixed x hx (Subtype.ext h)
    rcases lt_or_gt_of_ne hx_ne_real with hx_contracts | hx_expands
    · exfalso
      have hxq : (x : ℝ) ≤ (q : ℝ) := hx.2
      have hzero_mem : (0 : ℝ) ∈ Set.Icc
          (gu.extension (x : ℝ) - x) (gu.extension (q : ℝ) - q) := by
        constructor
        · rw [hx_agree]
          exact sub_nonpos.mpr hx_contracts.le
        · rw [hq_agree]
          exact sub_nonneg.mpr hq_expands.le
      obtain ⟨c, hc, hczero⟩ := Set.mem_image _ _ _ |>.mp
        (intermediate_value_Icc (f := fun t : ℝ => gu.extension t - t)
          hxq (hdiff.mono <| Set.Icc_subset_Icc hx.1.le le_rfl) hzero_mem)
      have hc_eq : gu.extension c = c := sub_eq_zero.mp hczero
      let cI : I :=
        ⟨c, ⟨x.property.1.trans hc.1, hc.2.trans q.property.2⟩⟩
      have hcI_mem : cI ∈ Set.Ioc p q := by
        exact ⟨hx.1.trans_le hc.1, hc.2⟩
      apply hu_no_fixed cI hcI_mem
      apply Subtype.ext
      change (u cI : ℝ) = c
      calc
        (u cI : ℝ) = gu.extension c := gu.agrees ⟨hcI_mem.1.le,
          hcI_mem.2.trans hq_u⟩
        _ = c := hc_eq
    · exact hx_expands

/-- Under the contracting orientation, failure of identity supplies one
fully explicit nonfixed component and all data required by the real core. -/
private theorem exists_localKopellContractingComponentData
    {u v : IntervalMap} {p q : I}
    (gu : RightGermC1Diffeomorphism u p)
    (gv : RightGermC1Diffeomorphism v p)
    (hu_bv : gu.HasBoundedVariationLogDeriv)
    (hpq : p < q)
    (hq_u : q ≤ gu.rightEnd)
    (hq_v : q ≤ gv.rightEnd)
    (hu_fixed : IsFixedPoint u p)
    (hv_fixed : IsFixedPoint v p)
    (hcomm : Set.EqOn (u ∘ v) (v ∘ u) (Set.Icc p q))
    (hu_no_fixed : ∀ x ∈ Set.Ioc p q, u x ≠ x)
    (hv_has_fixed : ∃ y ∈ Set.Ioc p q, v y = y)
    (hu_contracts : ∀ x ∈ Set.Ioc p q, (u x : ℝ) < x)
    (hv_not_identity : ¬SameOneSidedGermAt .right p v identityIntervalMap) :
    Nonempty (LocalKopellContractingComponentData (q := q) gu gv) := by
  rcases hv_has_fixed with ⟨y, hy, hy_fixed⟩
  have hpy : (p : ℝ) < (y : ℝ) := hy.1
  have hyq : y ≤ q := hy.2
  have hypU : y ≤ gu.rightEnd := hyq.trans hq_u
  have hypV : y ≤ gv.rightEnd := hyq.trans hq_v
  have hUp : gu.extension (p : ℝ) = (p : ℝ) := by
    calc
      gu.extension (p : ℝ) = (u p : ℝ) :=
        (gu.agrees ⟨le_rfl, gu.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hu_fixed
  have hVp : gv.extension (p : ℝ) = (p : ℝ) := by
    calc
      gv.extension (p : ℝ) = (v p : ℝ) :=
        (gv.agrees ⟨le_rfl, gv.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hv_fixed
  have hVy : gv.extension (y : ℝ) = (y : ℝ) := by
    calc
      gv.extension (y : ℝ) = (v y : ℝ) :=
        (gv.agrees ⟨hy.1.le, hypV⟩).symm
      _ = (y : ℝ) := congrArg Subtype.val hy_fixed
  have hUcont : ContinuousOn gu.extension
      (Set.Icc (p : ℝ) (y : ℝ)) :=
    gu.contDiff_one.continuousOn.mono fun _ hx =>
      gu.segment_subset ⟨hx.1, hx.2.trans hypU⟩
  have hVcont : ContinuousOn gv.extension
      (Set.Icc (p : ℝ) (y : ℝ)) :=
    gv.contDiff_one.continuousOn.mono fun _ hx =>
      gv.segment_subset ⟨hx.1, hx.2.trans hypV⟩
  have hUstrict : StrictMonoOn gu.extension
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hUcont
    intro z hz
    exact gu.deriv_pos z
      ⟨(interior_subset hz).1, (interior_subset hz).2.trans hypU⟩
  have hVstrict : StrictMonoOn gv.extension
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hVcont
    intro z hz
    exact gv.deriv_pos z
      ⟨(interior_subset hz).1, (interior_subset hz).2.trans hypV⟩
  have hUcontracts : ∀ z ∈ Set.Ioc (p : ℝ) (y : ℝ),
      gu.extension z < z := by
    intro z hz
    let zI : I := ⟨z, ⟨p.property.1.trans hz.1.le,
      hz.2.trans y.property.2⟩⟩
    have hzIq : zI ∈ Set.Ioc p q :=
      ⟨hz.1, hz.2.trans hyq⟩
    have hzIU : zI ∈ Set.Icc p gu.rightEnd :=
      ⟨hz.1.le, hz.2.trans hypU⟩
    have hagree : gu.extension z = (u zI : ℝ) :=
      (gu.agrees hzIU).symm
    simpa [zI, hagree] using hu_contracts zI hzIq
  have hUmap : Set.MapsTo gu.extension
      (Set.Icc (p : ℝ) (y : ℝ))
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro z hz
    constructor
    · rw [← hUp]
      exact hUstrict.monotoneOn ⟨le_rfl, hpy.le⟩ hz hz.1
    · exact (hUcontracts (y : ℝ) ⟨hpy, le_rfl⟩).le.trans'
        (hUstrict.monotoneOn hz ⟨hpy.le, le_rfl⟩ hz.2)
  have hVmap : Set.MapsTo gv.extension
      (Set.Icc (p : ℝ) (y : ℝ))
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro z hz
    constructor
    · rw [← hVp]
      exact hVstrict.monotoneOn ⟨le_rfl, hpy.le⟩ hz hz.1
    · rw [← hVy]
      exact hVstrict.monotoneOn hz ⟨hpy.le, le_rfl⟩ hz.2
  have hExtComm : Set.EqOn
      (gu.extension ∘ gv.extension) (gv.extension ∘ gu.extension)
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro z hz
    let zI : I := ⟨z, ⟨p.property.1.trans hz.1,
      hz.2.trans y.property.2⟩⟩
    have hzIU : zI ∈ Set.Icc p gu.rightEnd :=
      ⟨hz.1, hz.2.trans hypU⟩
    have hzIV : zI ∈ Set.Icc p gv.rightEnd :=
      ⟨hz.1, hz.2.trans hypV⟩
    have hUagree : (u zI : ℝ) = gu.extension z := gu.agrees hzIU
    have hVagree : (v zI : ℝ) = gv.extension z := gv.agrees hzIV
    have hvRangeReal := hVmap hz
    have huRangeReal := hUmap hz
    have hvRangeU : v zI ∈ Set.Icc p gu.rightEnd := by
      constructor
      · exact hvRangeReal.1.trans_eq hVagree.symm
      · exact hVagree.trans_le (hvRangeReal.2.trans hypU)
    have huRangeV : u zI ∈ Set.Icc p gv.rightEnd := by
      constructor
      · exact huRangeReal.1.trans_eq hUagree.symm
      · exact hUagree.trans_le (huRangeReal.2.trans hypV)
    have hzIq : zI ∈ Set.Icc p q := ⟨hz.1, hz.2.trans hyq⟩
    have hmapComm := congrArg Subtype.val (hcomm hzIq)
    change gu.extension (gv.extension z) = gv.extension (gu.extension z)
    calc
      gu.extension (gv.extension z) = gu.extension (v zI : ℝ) :=
        congrArg gu.extension hVagree.symm
      _ = (u (v zI) : ℝ) := (gu.agrees hvRangeU).symm
      _ = (v (u zI) : ℝ) := hmapComm
      _ = gv.extension (u zI : ℝ) := gv.agrees huRangeV
      _ = gv.extension (gu.extension z) :=
        congrArg gv.extension hUagree
  have hUcontAt : ∀ z ∈ Set.Icc (p : ℝ) (y : ℝ),
      ContinuousAt gu.extension z := by
    intro z hz
    exact (gu.contDiff_one.contDiffAt
      (gu.isOpen_neighborhood.mem_nhds <|
        gu.segment_subset ⟨hz.1, hz.2.trans hypU⟩)).continuousAt
  have hVcontAt : ∀ z ∈ Set.Icc (p : ℝ) (y : ℝ),
      ContinuousAt gv.extension z := by
    intro z hz
    exact (gv.contDiff_one.contDiffAt
      (gv.isOpen_neighborhood.mem_nhds <|
        gv.segment_subset ⟨hz.1, hz.2.trans hypV⟩)).continuousAt
  have hUorbit := contraction_iterates_tendsto
    hUcontAt hUmap hUp hUcontracts
  have hUiterStrict : ∀ n : ℕ, StrictMonoOn (gu.extension^[n])
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro n
    induction n with
    | zero => exact strictMonoOn_id
    | succ n ih =>
        intro a ha b hb hab
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact hUstrict (hUmap.iterate n ha) (hUmap.iterate n hb)
          (ih ha hb hab)
  have hViterStrict : ∀ n : ℕ, StrictMonoOn (gv.extension^[n])
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro n
    induction n with
    | zero => exact strictMonoOn_id
    | succ n ih =>
        intro a ha b hb hab
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact hVstrict (hVmap.iterate n ha) (hVmap.iterate n hb)
          (ih ha hb hab)
  have hUiterIoo : ∀ n z, z ∈ Set.Ioo (p : ℝ) (y : ℝ) →
      (gu.extension^[n]) z ∈ Set.Ioo (p : ℝ) (y : ℝ) := by
    intro n z hz
    have hpiter : (gu.extension^[n]) (p : ℝ) = (p : ℝ) :=
      Function.IsFixedPt.iterate hUp n
    constructor
    · rw [← hpiter]
      exact hUiterStrict n ⟨le_rfl, hpy.le⟩
        ⟨hz.1.le, hz.2.le⟩ hz.1
    · exact (hUiterStrict n ⟨hz.1.le, hz.2.le⟩
          ⟨hpy.le, le_rfl⟩ hz.2).trans_le
        (hUmap.iterate n ⟨hpy.le, le_rfl⟩).2
  have hViterIoo : ∀ n z, z ∈ Set.Ioo (p : ℝ) (y : ℝ) →
      (gv.extension^[n]) z ∈ Set.Ioo (p : ℝ) (y : ℝ) := by
    intro n z hz
    have hpiter : (gv.extension^[n]) (p : ℝ) = (p : ℝ) :=
      Function.IsFixedPt.iterate hVp n
    have hyiter : (gv.extension^[n]) (y : ℝ) = (y : ℝ) :=
      Function.IsFixedPt.iterate hVy n
    constructor
    · rw [← hpiter]
      exact hViterStrict n ⟨le_rfl, hpy.le⟩
        ⟨hz.1.le, hz.2.le⟩ hz.1
    · rw [← hyiter]
      exact hViterStrict n ⟨hz.1.le, hz.2.le⟩
        ⟨hpy.le, le_rfl⟩ hz.2
  have hnotEqOn : ¬Set.EqOn v identityIntervalMap (Set.Icc p y) := by
    intro heq
    exact hv_not_identity ⟨y, hy.1, heq⟩
  have hexMoved : ∃ x ∈ Set.Icc p y, v x ≠ identityIntervalMap x := by
    by_contra hnone
    push_neg at hnone
    exact hnotEqOn hnone
  obtain ⟨xI, hxI, hxmoveMap⟩ := hexMoved
  have hxIp : xI ≠ p := by
    intro h
    subst xI
    apply hxmoveMap
    simpa [identityIntervalMap] using hv_fixed
  have hxIy : xI ≠ y := by
    intro h
    subst xI
    apply hxmoveMap
    simpa [identityIntervalMap] using hy_fixed
  have hxIoo : (xI : ℝ) ∈ Set.Ioo (p : ℝ) (y : ℝ) :=
    ⟨lt_of_le_of_ne hxI.1 (fun h => hxIp (Subtype.ext h.symm)),
      lt_of_le_of_ne hxI.2 (fun h => hxIy (Subtype.ext h))⟩
  have hxmoveExt : gv.extension (xI : ℝ) ≠ (xI : ℝ) := by
    intro h
    apply hxmoveMap
    apply Subtype.ext
    have hagree := gv.agrees ⟨hxI.1, hxI.2.trans hypV⟩
    simpa [identityIntervalMap, h] using hagree
  obtain ⟨c, d, hcd, hcomponentMem, hinteriorMem,
      hcFixed, hdFixed, hcomponentNoFix, hcomponentMoved,
      e, he⟩ := exists_nonfixed_component_orderIso
        hVcont hVstrict hVp hVy hxIoo hxmoveExt
  have hcMem : c ∈ Set.Icc (p : ℝ) (y : ℝ) :=
    hcomponentMem ⟨le_rfl, hcd.le⟩
  have hdMem : d ∈ Set.Icc (p : ℝ) (y : ℝ) :=
    hcomponentMem ⟨hcd.le, le_rfl⟩
  have hVmapComponent : Set.MapsTo gv.extension
      (Set.Icc c d) (Set.Icc c d) := by
    intro z hz
    constructor
    · calc
        c = gv.extension c := hcFixed.symm
        _ ≤ gv.extension z :=
          hVstrict.monotoneOn (hcomponentMem ⟨le_rfl, hcd.le⟩)
            (hcomponentMem hz) hz.1
    · calc
        gv.extension z ≤ gv.extension d :=
          hVstrict.monotoneOn (hcomponentMem hz)
            (hcomponentMem ⟨hcd.le, le_rfl⟩) hz.2
        _ = d := hdFixed
  have hUiterComm (n k : ℕ) :=
    eqOn_iterates_of_commuteOn_mapsTo (n := n) (k := k)
      hExtComm hUmap hVmap
  have hfixedSequenceFixed : ∀ n,
      gv.extension ((gu.extension^[n]) (y : ℝ)) =
        (gu.extension^[n]) (y : ℝ) := by
    intro n
    have h := hUiterComm n 1 ⟨hpy.le, le_rfl⟩
    simpa [Function.comp_apply, hVy] using h.symm
  have hfixedSequenceNe : ∀ n,
      (gu.extension^[n]) (y : ℝ) ≠ (p : ℝ) := by
    intro n hEq
    have hpiter : (gu.extension^[n]) (p : ℝ) = (p : ℝ) :=
      Function.IsFixedPt.iterate hUp n
    have hlt := hUiterStrict n ⟨le_rfl, hpy.le⟩
      ⟨hpy.le, le_rfl⟩ hpy
    rw [hpiter, hEq] at hlt
    exact lt_irrefl _ hlt
  have hforwardRightFixed : ∀ i,
      gv.extension ((gu.extension^[i]) d) = (gu.extension^[i]) d := by
    intro i
    have h := hUiterComm i 1 hdMem
    simpa [Function.comp_apply, hdFixed] using h.symm
  have hforwardMove : ∀ i,
      gu.extension ((gu.extension^[i]) d) < (gu.extension^[i]) d := by
    intro i
    have hdIoo : d ∈ Set.Ioc (p : ℝ) (y : ℝ) :=
      ⟨hcMem.1.trans_lt hcd, hdMem.2⟩
    have hpiter : (gu.extension^[i]) (p : ℝ) = (p : ℝ) :=
      Function.IsFixedPt.iterate hUp i
    have hlower : (p : ℝ) < (gu.extension^[i]) d := by
      rw [← hpiter]
      exact hUiterStrict i ⟨le_rfl, hpy.le⟩ hdMem hdIoo.1
    exact hUcontracts _
      ⟨hlower, (hUmap.iterate i hdMem).2⟩
  have hforwardNoFix : ∀ i z,
      z ∈ Set.Ioo ((gu.extension^[i]) c) ((gu.extension^[i]) d) →
        gv.extension z ≠ z := by
    intro i z hz hzfix
    have hiterCont := (hUcont.iterate hUmap i).mono hcomponentMem
    have hsurj := hiterCont.surjOn_Icc
      (show c ∈ Set.Icc c d from ⟨le_rfl, hcd.le⟩)
      (show d ∈ Set.Icc c d from ⟨hcd.le, le_rfl⟩)
    obtain ⟨t, ht, htz⟩ := hsurj ⟨hz.1.le, hz.2.le⟩
    have htIoo : t ∈ Set.Ioo c d := by
      constructor
      · apply lt_of_le_of_ne ht.1
        intro htc
        subst t
        exact (ne_of_lt hz.1) htz
      · apply lt_of_le_of_ne ht.2
        intro htd
        subst t
        exact (ne_of_lt hz.2) htz.symm
    have hgtIoo : gv.extension t ∈ Set.Ioo c d := by
      simpa using orderIso_iterate_ambient_mem_Ioo
        hcd e he htIoo 1
    have hcommAt := hUiterComm i 1
      (hcomponentMem ⟨htIoo.1.le, htIoo.2.le⟩)
    have hiterEq : (gu.extension^[i]) (gv.extension t) =
        (gu.extension^[i]) t := by
      calc
        (gu.extension^[i]) (gv.extension t) =
            gv.extension ((gu.extension^[i]) t) := by
          simpa [Function.comp_apply] using hcommAt
        _ = gv.extension z := congrArg gv.extension htz
        _ = z := hzfix
        _ = (gu.extension^[i]) t := htz.symm
    have hinj := (hUiterStrict i).injOn
    have hgt : gv.extension t = t := hinj
      (hcomponentMem ⟨hgtIoo.1.le, hgtIoo.2.le⟩)
      (hcomponentMem ⟨htIoo.1.le, htIoo.2.le⟩) hiterEq
    exact hcomponentNoFix t htIoo hgt
  have hcomponents : ∀ i,
      (gu.extension^[i + 1]) d ≤ (gu.extension^[i]) c :=
    successive_component_images_ordered hforwardMove
      hforwardRightFixed hforwardNoFix
  have hUdiffOn : DifferentiableOn ℝ gu.extension
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro z hz
    exact (gu.contDiff_one.contDiffAt
      (gu.isOpen_neighborhood.mem_nhds <|
        gu.segment_subset ⟨hz.1, hz.2.trans hypU⟩)).differentiableAt_one
      |>.differentiableWithinAt
  have hVdiffOn : DifferentiableOn ℝ gv.extension
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro z hz
    exact (gv.contDiff_one.contDiffAt
      (gv.isOpen_neighborhood.mem_nhds <|
        gv.segment_subset ⟨hz.1, hz.2.trans hypV⟩)).differentiableAt_one
      |>.differentiableWithinAt
  have hUdiffAt : ∀ n z, z ∈ Set.Ioo (p : ℝ) (y : ℝ) →
      DifferentiableAt ℝ (gu.extension^[n]) z := by
    intro n z hz
    exact (hUdiffOn.iterate hUmap n z ⟨hz.1.le, hz.2.le⟩).differentiableAt
      (Icc_mem_nhds hz.1 hz.2)
  have hVdiffAt : ∀ n z, z ∈ Set.Ioo (p : ℝ) (y : ℝ) →
      DifferentiableAt ℝ (gv.extension^[n]) z := by
    intro n z hz
    exact (hVdiffOn.iterate hVmap n z ⟨hz.1.le, hz.2.le⟩).differentiableAt
      (Icc_mem_nhds hz.1 hz.2)
  have hUderivPos : ∀ z ∈ Set.Icc (p : ℝ) (y : ℝ),
      0 < deriv gu.extension z := by
    intro z hz
    exact gu.deriv_pos z ⟨hz.1, hz.2.trans hypU⟩
  have hVderivPos : ∀ z ∈ Set.Icc (p : ℝ) (y : ℝ),
      0 < deriv gv.extension z := by
    intro z hz
    exact gv.deriv_pos z ⟨hz.1, hz.2.trans hypV⟩
  have hViterPos : ∀ n z, z ∈ Set.Ioo (p : ℝ) (y : ℝ) →
      0 < deriv (gv.extension^[n]) z := by
    intro n z hz
    rw [deriv_iterate_eq_prod]
    · exact Finset.prod_pos fun i hi =>
        hVderivPos _ (hVmap.iterate i ⟨hz.1.le, hz.2.le⟩)
    · intro i hi
      exact (hVdiffOn _
        (hVmap.iterate i ⟨hz.1.le, hz.2.le⟩)).differentiableAt
        (Icc_mem_nhds (hViterIoo i z hz).1 (hViterIoo i z hz).2)
  have hOrdered : ∀ z ∈ Set.Ioo c d, ∀ k,
      ∃ w : ℕ → ℕ → ℝ,
        (∀ n, Monotone (w n) ∨ Antitone (w n)) ∧
        (∀ n j, j ≤ 2 * n → w n j ∈ Set.Icc (p : ℝ) (y : ℝ)) ∧
        (∀ n i, i < n →
          (w n (2 * i) = (gu.extension^[i]) z ∧
            w n (2 * i + 1) =
              (gu.extension^[i]) ((gv.extension^[k]) z)) ∨
          (w n (2 * i) =
              (gu.extension^[i]) ((gv.extension^[k]) z) ∧
            w n (2 * i + 1) = (gu.extension^[i]) z)) := by
    intro z hz k
    have hgz : (gv.extension^[k]) z ∈ Set.Ioo c d :=
      orderIso_iterate_ambient_mem_Ioo hcd e he hz k
    have hXmem : ∀ i, (gu.extension^[i]) z ∈
        Set.Icc (p : ℝ) (y : ℝ) :=
      fun i => hUmap.iterate i
        (hcomponentMem ⟨hz.1.le, hz.2.le⟩)
    have hYmem : ∀ i, (gu.extension^[i]) ((gv.extension^[k]) z) ∈
        Set.Icc (p : ℝ) (y : ℝ) :=
      fun i => hUmap.iterate i
        (hcomponentMem ⟨hgz.1.le, hgz.2.le⟩)
    have hsep : ∀ i,
        max ((gu.extension^[i + 1]) z)
            ((gu.extension^[i + 1]) ((gv.extension^[k]) z)) ≤
          min ((gu.extension^[i]) z)
            ((gu.extension^[i]) ((gv.extension^[k]) z)) := by
      intro i
      have hnext : max ((gu.extension^[i + 1]) z)
          ((gu.extension^[i + 1]) ((gv.extension^[k]) z)) <
          (gu.extension^[i + 1]) d := by
        rw [max_lt_iff]
        exact ⟨hUiterStrict (i + 1)
            (hcomponentMem ⟨hz.1.le, hz.2.le⟩) hdMem hz.2,
          hUiterStrict (i + 1)
            (hcomponentMem ⟨hgz.1.le, hgz.2.le⟩) hdMem hgz.2⟩
      have hprev : (gu.extension^[i]) c <
          min ((gu.extension^[i]) z)
            ((gu.extension^[i]) ((gv.extension^[k]) z)) := by
        rw [lt_min_iff]
        exact ⟨hUiterStrict i hcMem
            (hcomponentMem ⟨hz.1.le, hz.2.le⟩) hz.1,
          hUiterStrict i hcMem
            (hcomponentMem ⟨hgz.1.le, hgz.2.le⟩) hgz.1⟩
      exact hnext.le.trans ((hcomponents i).trans hprev.le)
    obtain ⟨w, hwanti, hwmem, hwpair⟩ :=
      exists_antitoneInterleaving_of_orderedPairs hsep hXmem hYmem
    refine ⟨fun _ => w, ?_, ?_, ?_⟩
    · intro n
      exact Or.inr hwanti
    · intro n j hj
      exact hwmem j
    · intro n i hi
      exact hwpair i
  have hDerivativeChain : ∀ z ∈ Set.Ioo c d, ∀ k n,
      deriv (gv.extension^[k]) ((gu.extension^[n]) z) *
          deriv (gu.extension^[n]) z =
        deriv (gu.extension^[n]) ((gv.extension^[k]) z) *
          deriv (gv.extension^[k]) z := by
    intro z hz k n
    have hzCommon := hinteriorMem hz
    have hgzCommon : (gv.extension^[k]) z ∈
        Set.Ioo (p : ℝ) (y : ℝ) :=
      hinteriorMem (orderIso_iterate_ambient_mem_Ioo hcd e he hz k)
    have hfzCommon := hUiterIoo n z hzCommon
    exact deriv_commuting_iterates_identity_of_eqOn_nhds
      hExtComm hUmap hVmap (Icc_mem_nhds hzCommon.1 hzCommon.2)
      (hUdiffAt n z hzCommon) (hUdiffAt n _ hgzCommon)
      (hVdiffAt k z hzCommon) (hVdiffAt k _ hfzCommon)
  refine ⟨{
    commonEnd := y
    base_lt_commonEnd := hy.1
    commonEnd_le_u := hypU
    commonEnd_le_v := hypV
    commonEnd_le_q := hyq
    u_maps_common := hUmap
    v_maps_common := hVmap
    extensions_commute := hExtComm
    componentLeft := c
    componentRight := d
    component_nondegenerate := hcd
    component_mem_common := hcomponentMem
    component_interior_common := hinteriorMem
    left_fixed := hcFixed
    right_fixed := hdFixed
    component_no_fixed := hcomponentNoFix
    component_moved := hcomponentMoved
    componentOrderIso := e
    componentOrderIso_agrees := he
    fixedSequence := fun n => (gu.extension^[n]) (y : ℝ)
    fixedSequence_tendsto := hUorbit (y : ℝ) ⟨hpy.le, le_rfl⟩
    fixedSequence_ne := hfixedSequenceNe
    fixedSequence_fixed := hfixedSequenceFixed
    orbit_contracts := fun z hz =>
      hUorbit z (hcomponentMem ⟨hz.1.le, hz.2.le⟩)
    u_contracts := hUcontracts
    forward_right_fixed := hforwardRightFixed
    forward_components_no_fixed := hforwardNoFix
    g_iter_cont := fun n =>
      (hVcont.mono hcomponentMem).iterate hVmapComponent n
    g_iter_diff := fun n =>
      ((hVdiffOn.mono hcomponentMem).iterate hVmapComponent n).mono
        Set.Ioo_subset_Icc_self
    logDeriv_bv := hu_bv.mono
      (Set.Icc_subset_Icc le_rfl hypU)
    f_step_diff := by
      intro z hz k i
      have hzCommon := hinteriorMem hz
      have hgzCommon : (gv.extension^[k]) z ∈
          Set.Ioo (p : ℝ) (y : ℝ) :=
        hinteriorMem (orderIso_iterate_ambient_mem_Ioo hcd e he hz k)
      exact ⟨(hUdiffOn _
          (hUmap.iterate i ⟨hzCommon.1.le, hzCommon.2.le⟩)).differentiableAt
          (Icc_mem_nhds (hUiterIoo i z hzCommon).1
            (hUiterIoo i z hzCommon).2),
        (hUdiffOn _
          (hUmap.iterate i ⟨hgzCommon.1.le, hgzCommon.2.le⟩)).differentiableAt
          (Icc_mem_nhds (hUiterIoo i _ hgzCommon).1
            (hUiterIoo i _ hgzCommon).2)⟩
    f_step_pos := by
      intro z hz k i
      have hzCommon := hinteriorMem hz
      have hgzCommon : (gv.extension^[k]) z ∈
          Set.Ioo (p : ℝ) (y : ℝ) :=
        hinteriorMem (orderIso_iterate_ambient_mem_Ioo hcd e he hz k)
      exact ⟨hUderivPos _
          (hUmap.iterate i ⟨hzCommon.1.le, hzCommon.2.le⟩),
        hUderivPos _
          (hUmap.iterate i ⟨hgzCommon.1.le, hgzCommon.2.le⟩)⟩
    g_iter_pos := by
      intro z hz k n
      exact hViterPos k _ (hUiterIoo n z (hinteriorMem hz))
    ordered_interleaving := hOrdered
    derivative_chain := hDerivativeChain }⟩

/-- The contracting component data contradict Polterovich--Sodin through the
local bounded-distortion core. -/
private theorem local_c1BV_Kopell_of_contracting
    {u v : IntervalMap} {p q : I}
    (gu : RightGermC1Diffeomorphism u p)
    (gv : RightGermC1Diffeomorphism v p)
    (hu_bv : gu.HasBoundedVariationLogDeriv)
    (hpq : p < q)
    (hq_u : q ≤ gu.rightEnd)
    (hq_v : q ≤ gv.rightEnd)
    (hu_fixed : IsFixedPoint u p)
    (hv_fixed : IsFixedPoint v p)
    (hcomm : Set.EqOn (u ∘ v) (v ∘ u) (Set.Icc p q))
    (hu_no_fixed : ∀ x ∈ Set.Ioc p q, u x ≠ x)
    (hv_has_fixed : ∃ y ∈ Set.Ioc p q, v y = y)
    (hu_contracts : ∀ x ∈ Set.Ioc p q, (u x : ℝ) < x) :
    SameOneSidedGermAt .right p v identityIntervalMap := by
  by_contra hv_not_identity
  let D := (exists_localKopellContractingComponentData gu gv hu_bv hpq
    hq_u hq_v hu_fixed hv_fixed hcomm hu_no_fixed hv_has_fixed
    hu_contracts hv_not_identity).some
  have hidentity := contracting_kopell_core_localData
    D.component_nondegenerate D.componentOrderIso
    D.componentOrderIso_agrees D.g_iter_cont D.g_iter_diff
    (gv.contDiff_one.contDiffAt <| gv.isOpen_neighborhood.mem_nhds <|
      gv.segment_subset ⟨le_rfl, gv.base_lt_rightEnd.le⟩)
    D.fixedSequence D.fixedSequence_tendsto D.fixedSequence_ne
    D.fixedSequence_fixed D.orbit_contracts D.logDeriv_bv
    D.f_step_diff D.f_step_pos D.g_iter_pos D.ordered_interleaving
    D.derivative_chain
  obtain ⟨x, hx, hmove⟩ := D.component_moved
  exact hmove (hidentity x hx)

/-- Inversion preserves the selected right `C^{1+BV}` germ class, including
an explicit inverse representative and the two inverse-germ identities. -/
private theorem exists_c1BV_rightGerm_inverse
    {F : IntervalMap} {p : I}
    (hFfixed : IsFixedPoint F p)
    (gF : RightGermC1Diffeomorphism F p)
    (hBV : gF.HasBoundedVariationLogDeriv) :
    ∃ FInv : IntervalMap, ∃ gInv : RightGermC1Diffeomorphism FInv p,
      IsFixedPoint FInv p ∧
      AreInverseRightGermsAt p F FInv ∧
      gInv.HasBoundedVariationLogDeriv := by
  rcases exists_c1_rightGerm_inverse hFfixed gF with
    ⟨FInv, hFInvfixed, hInverseGerms, ⟨gInv₀⟩⟩
  rcases hInverseGerms.1 with ⟨a, hpa, hleftInverse⟩
  have hpInv : (p : ℝ) ∈
      Set.Icc (p : ℝ) (gInv₀.rightEnd : ℝ) :=
    ⟨le_rfl, gInv₀.base_lt_rightEnd.le⟩
  have hInvExtp : gInv₀.extension (p : ℝ) = (p : ℝ) := by
    calc
      gInv₀.extension (p : ℝ) = (FInv p : ℝ) :=
        (gInv₀.agrees ⟨le_rfl, gInv₀.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hFInvfixed
  have hInvContinuous : ContinuousOn gInv₀.extension
      (Set.Icc (p : ℝ) (gInv₀.rightEnd : ℝ)) :=
    gInv₀.contDiff_one.continuousOn.mono gInv₀.segment_subset
  have hInvStrict : StrictMonoOn gInv₀.extension
      (Set.Icc (p : ℝ) (gInv₀.rightEnd : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hInvContinuous
    intro x hx
    exact gInv₀.deriv_pos x (interior_subset hx)
  have hInvC1p : ContDiffAt ℝ 1 gInv₀.extension (p : ℝ) :=
    gInv₀.contDiff_one.contDiffAt
      (gInv₀.isOpen_neighborhood.mem_nhds
        (gInv₀.segment_subset hpInv))
  have hnearF : gInv₀.extension ⁻¹' Set.Iio (gF.rightEnd : ℝ) ∈
      𝓝 (p : ℝ) := by
    apply hInvC1p.continuousAt
    rw [hInvExtp]
    exact Iio_mem_nhds gF.base_lt_rightEnd
  obtain ⟨s, hps, hIccNear⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (mem_nhdsWithin_of_mem_nhds hnearF)
  have hpmin : (p : ℝ) <
      min s (min (a : ℝ) (gInv₀.rightEnd : ℝ)) := by
    exact lt_min hps (lt_min hpa gInv₀.base_lt_rightEnd)
  obtain ⟨r, hpr, hrmin⟩ := exists_between hpmin
  have hrs : r < s := hrmin.trans_le (min_le_left _ _)
  have hra : r < (a : ℝ) :=
    hrmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrInv : r < (gInv₀.rightEnd : ℝ) :=
    hrmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let q : I := ⟨r, ⟨p.property.1.trans hpr.le,
    hrInv.le.trans gInv₀.rightEnd.property.2⟩⟩
  have hpq : p < q := hpr
  have hInvMapsF : Set.MapsTo gInv₀.extension
      (Set.Icc (p : ℝ) r)
      (Set.Icc (p : ℝ) (gF.rightEnd : ℝ)) := by
    intro x hx
    have hxInv : x ∈ Set.Icc (p : ℝ) (gInv₀.rightEnd : ℝ) :=
      ⟨hx.1, hx.2.trans hrInv.le⟩
    constructor
    · rw [← hInvExtp]
      exact hInvStrict.monotoneOn hpInv hxInv hx.1
    · exact (hIccNear ⟨hx.1, hx.2.trans hrs.le⟩).le
  have hExtLeftInverse : Set.EqOn
      (gF.extension ∘ gInv₀.extension) id
      (Set.Icc (p : ℝ) r) := by
    intro x hx
    let xI : I := ⟨x, ⟨p.property.1.trans hx.1,
      hx.2.trans (hrInv.le.trans gInv₀.rightEnd.property.2)⟩⟩
    have hxIInv : xI ∈ Set.Icc p gInv₀.rightEnd :=
      ⟨hx.1, hx.2.trans hrInv.le⟩
    have hxIa : xI ∈ Set.Icc p a :=
      ⟨hx.1, hx.2.trans hra.le⟩
    have hInvAgree : (FInv xI : ℝ) = gInv₀.extension x :=
      gInv₀.agrees hxIInv
    have hInvRangeReal := hInvMapsF hx
    have hInvRange : FInv xI ∈ Set.Icc p gF.rightEnd := by
      constructor
      · exact hInvRangeReal.1.trans_eq hInvAgree.symm
      · exact hInvAgree.trans_le hInvRangeReal.2
    have hleft := congrArg Subtype.val (hleftInverse hxIa)
    simp only [Function.comp_apply, identityIntervalMap] at hleft
    change gF.extension (gInv₀.extension x) = x
    calc
      gF.extension (gInv₀.extension x) =
          gF.extension (FInv xI : ℝ) :=
        congrArg gF.extension hInvAgree.symm
      _ = (F (FInv xI) : ℝ) := (gF.agrees hInvRange).symm
      _ = x := hleft
  let gInv : RightGermC1Diffeomorphism FInv p := {
    rightEnd := q
    base_lt_rightEnd := hpq
    extension := gInv₀.extension
    neighborhood := gInv₀.neighborhood
    isOpen_neighborhood := gInv₀.isOpen_neighborhood
    segment_subset := by
      intro x hx
      exact gInv₀.segment_subset ⟨hx.1, hx.2.trans hrInv.le⟩
    agrees := by
      intro x hx
      exact gInv₀.agrees ⟨hx.1, hx.2.trans hrInv.le⟩
    contDiff_one := gInv₀.contDiff_one
    deriv_pos := by
      intro x hx
      exact gInv₀.deriv_pos x ⟨hx.1, hx.2.trans hrInv.le⟩ }
  have hInvMonotone : MonotoneOn gInv₀.extension
      (Set.Icc (p : ℝ) r) :=
    hInvStrict.monotoneOn.mono (Set.Icc_subset_Icc le_rfl hrInv.le)
  have hCompBV : BoundedVariationOn
      (gF.logDeriv ∘ gInv₀.extension) (Set.Icc (p : ℝ) r) := by
    apply ne_top_of_le_ne_top hBV
    exact eVariationOn.comp_le_of_monotoneOn gF.logDeriv
      gInv₀.extension hInvMonotone hInvMapsF
  have hNegCompBV : BoundedVariationOn
      (fun x : ℝ => -gF.logDeriv (gInv₀.extension x))
      (Set.Icc (p : ℝ) r) := by
    have hneg : BoundedVariationOn
        ((fun y : ℝ => -y) ∘ (gF.logDeriv ∘ gInv₀.extension))
        (Set.Icc (p : ℝ) r) :=
      (LipschitzWith.id.neg :
        LipschitzWith 1 (fun y : ℝ => -y)).comp_boundedVariationOn hCompBV
    simpa [Function.comp_def] using hneg
  have hLogFormula : Set.EqOn gInv.logDeriv
      (fun x : ℝ => -gF.logDeriv (gInv₀.extension x))
      (Set.Icc (p : ℝ) r) := by
    intro x hx
    have hxInv : x ∈ Set.Icc (p : ℝ) (gInv₀.rightEnd : ℝ) :=
      ⟨hx.1, hx.2.trans hrInv.le⟩
    have hInvDiff : DifferentiableAt ℝ gInv₀.extension x :=
      (gInv₀.contDiff_one.contDiffAt
        (gInv₀.isOpen_neighborhood.mem_nhds
          (gInv₀.segment_subset hxInv))).differentiableAt_one
    have hxImage := hInvMapsF hx
    have hFDiff : DifferentiableAt ℝ gF.extension
        (gInv₀.extension x) :=
      (gF.contDiff_one.contDiffAt
        (gF.isOpen_neighborhood.mem_nhds
          (gF.segment_subset hxImage))).differentiableAt_one
    have hunique := (uniqueDiffOn_Icc hpr).uniqueDiffWithinAt hx
    have hchain : HasDerivAt (gF.extension ∘ gInv₀.extension)
        (deriv gF.extension (gInv₀.extension x) *
          deriv gInv₀.extension x) x :=
      hFDiff.hasDerivAt.comp x hInvDiff.hasDerivAt
    have hchainWithin : HasDerivWithinAt
        (gF.extension ∘ gInv₀.extension)
        (deriv gF.extension (gInv₀.extension x) *
          deriv gInv₀.extension x) (Set.Icc (p : ℝ) r) x :=
      hchain.hasDerivWithinAt
    have hidWithin : HasDerivWithinAt id 1
        (Set.Icc (p : ℝ) r) x :=
      (hasDerivAt_id x).hasDerivWithinAt
    have hprod : deriv gF.extension (gInv₀.extension x) *
        deriv gInv₀.extension x = 1 := by
      calc
        deriv gF.extension (gInv₀.extension x) *
              deriv gInv₀.extension x =
            derivWithin (gF.extension ∘ gInv₀.extension)
              (Set.Icc (p : ℝ) r) x :=
          (hchainWithin.derivWithin hunique).symm
        _ = derivWithin id (Set.Icc (p : ℝ) r) x :=
          derivWithin_congr hExtLeftInverse (hExtLeftInverse hx)
        _ = 1 := hidWithin.derivWithin hunique
    have hInvDeriv : deriv gInv₀.extension x =
        (deriv gF.extension (gInv₀.extension x))⁻¹ :=
      eq_inv_of_mul_eq_one_right hprod
    change Real.log (deriv gInv₀.extension x) =
      -Real.log (deriv gF.extension (gInv₀.extension x))
    rw [hInvDeriv, Real.log_inv]
  have hInvBV : gInv.HasBoundedVariationLogDeriv := by
    change BoundedVariationOn gInv.logDeriv
      (Set.Icc (p : ℝ) (gInv.rightEnd : ℝ))
    simpa [gInv, q] using
      (show BoundedVariationOn gInv.logDeriv
          (Set.Icc (p : ℝ) r) from by
        rw [BoundedVariationOn, eVariationOn.eq_of_eqOn hLogFormula]
        exact hNegCompBV)
  exact ⟨FInv, gInv, hFInvfixed, hInverseGerms, hInvBV⟩

/-- The expanding orientation reduces to the contracting one by the explicit
`C^{1+BV}` inverse germ, after shrinking all representatives together. -/
private theorem local_c1BV_Kopell_of_expanding
    {u v : IntervalMap} {p q : I}
    (gu : RightGermC1Diffeomorphism u p)
    (gv : RightGermC1Diffeomorphism v p)
    (hu_bv : gu.HasBoundedVariationLogDeriv)
    (hpq : p < q)
    (hq_u : q ≤ gu.rightEnd)
    (hq_v : q ≤ gv.rightEnd)
    (hu_fixed : IsFixedPoint u p)
    (hv_fixed : IsFixedPoint v p)
    (hcomm : Set.EqOn (u ∘ v) (v ∘ u) (Set.Icc p q))
    (hu_no_fixed : ∀ x ∈ Set.Ioc p q, u x ≠ x)
    (hv_has_fixed : ∃ y ∈ Set.Ioc p q, v y = y)
    (hu_expands : ∀ x ∈ Set.Ioc p q, (x : ℝ) < u x) :
    SameOneSidedGermAt .right p v identityIntervalMap := by
  rcases exists_c1BV_rightGerm_inverse hu_fixed gu hu_bv with
    ⟨uInv, gInv, huInv_fixed, hInverseGerms, huInv_bv⟩
  obtain ⟨fixedSeq, hfixedSeq_tendsto, hfixedSeq_gt,
      hfixedSeq_fixed⟩ := expanding_fixed_sequence gu gv hpq hq_u hq_v
        hu_fixed hv_fixed hcomm hv_has_fixed hu_expands
  have havailable : ∃ r : I, p < r := ⟨q, hpq⟩
  have hcommEv : (u ∘ v) =ᶠ[𝓝[≥] p] (v ∘ u) :=
    (sameRightGerm_iff_eventuallyEq havailable).1 ⟨q, hpq, hcomm⟩
  have hUInvEv : (u ∘ uInv) =ᶠ[𝓝[≥] p] identityIntervalMap :=
    (sameRightGerm_iff_eventuallyEq havailable).1 hInverseGerms.1
  have hInvUEv : (uInv ∘ u) =ᶠ[𝓝[≥] p] identityIntervalMap :=
    (sameRightGerm_iff_eventuallyEq havailable).1 hInverseGerms.2
  have hUTend : Tendsto u (𝓝[≥] p) (𝓝[≥] p) :=
    gu.tendsto_nhdsGE hu_fixed
  have hVTend : Tendsto v (𝓝[≥] p) (𝓝[≥] p) :=
    gv.tendsto_nhdsGE hv_fixed
  have hInvTend : Tendsto uInv (𝓝[≥] p) (𝓝[≥] p) :=
    gInv.tendsto_nhdsGE huInv_fixed
  have hInvCommEv : (uInv ∘ v) =ᶠ[𝓝[≥] p] (v ∘ uInv) := by
    have hcommAtInv := hcommEv.comp_tendsto hInvTend
    have hUInvThenV := hUInvEv.fun_comp v
    have hInvUAtVInv := hInvUEv.comp_tendsto (hVTend.comp hInvTend)
    filter_upwards [hcommAtInv, hUInvThenV, hInvUAtVInv] with
      x hxcomm hxUInv hxInvU
    calc
      uInv (v x) = uInv (v (u (uInv x))) :=
        congrArg uInv hxUInv.symm
      _ = uInv (u (v (uInv x))) :=
        congrArg uInv hxcomm.symm
      _ = v (uInv x) := hxInvU
  have htargetRange : Set.Iio q ∈ 𝓝[≥] p :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hpq)
  have hInvRangeEv : ∀ᶠ x in 𝓝[≥] p, uInv x < q :=
    hInvTend htargetRange
  have hInvEndEv : ∀ᶠ x in 𝓝[≥] p, x < gInv.rightEnd :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds gInv.base_lt_rightEnd)
  have hVEndEv : ∀ᶠ x in 𝓝[≥] p, x < gv.rightEnd :=
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds gv.base_lt_rightEnd)
  have hAllEv : ∀ᶠ x in 𝓝[≥] p,
      (uInv (v x) = v (uInv x)) ∧
      (u (uInv x) = x) ∧
      uInv x < q ∧ x < gInv.rightEnd ∧ x < gv.rightEnd := by
    filter_upwards [hInvCommEv, hUInvEv, hInvRangeEv,
      hInvEndEv, hVEndEv] with x hxcomm hxinv hxrange hxInvEnd hxVEnd
    simpa [Function.comp_apply, identityIntervalMap] using
      ⟨hxcomm, hxinv, hxrange, hxInvEnd, hxVEnd⟩
  let B := nhdsGE_basis_of_exists_gt havailable
  obtain ⟨r, hpr, hprops⟩ := B.mem_iff.mp hAllEv
  have hfixedSeq_small : ∀ᶠ n in atTop, (fixedSeq n : ℝ) < (r : ℝ) :=
    hfixedSeq_tendsto (Iio_mem_nhds hpr)
  obtain ⟨n, hn⟩ := hfixedSeq_small.exists
  let q' : I := fixedSeq n
  have hpq' : p < q' := hfixedSeq_gt n
  have hq'r : q' < r := hn
  have hq'props := hprops ⟨hpq'.le, hq'r⟩
  have hq'_inv : q' ≤ gInv.rightEnd := hq'props.2.2.2.1.le
  have hq'_v : q' ≤ gv.rightEnd := hq'props.2.2.2.2.le
  have hInvExtp : gInv.extension (p : ℝ) = (p : ℝ) := by
    calc
      gInv.extension (p : ℝ) = (uInv p : ℝ) :=
        (gInv.agrees ⟨le_rfl, gInv.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val huInv_fixed
  have hInvCont : ContinuousOn gInv.extension
      (Set.Icc (p : ℝ) (gInv.rightEnd : ℝ)) :=
    gInv.contDiff_one.continuousOn.mono gInv.segment_subset
  have hInvStrict : StrictMonoOn gInv.extension
      (Set.Icc (p : ℝ) (gInv.rightEnd : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hInvCont
    intro x hx
    exact gInv.deriv_pos x (interior_subset hx)
  have hcommInv : Set.EqOn (uInv ∘ v) (v ∘ uInv)
      (Set.Icc p q') := by
    intro x hx
    exact (hprops ⟨hx.1, hx.2.trans_lt hq'r⟩).1
  have hInvContracts : ∀ x ∈ Set.Ioc p q', (uInv x : ℝ) < x := by
    intro x hx
    have hxProps := hprops ⟨hx.1.le, hx.2.trans_lt hq'r⟩
    have hxInvSeg : x ∈ Set.Icc p gInv.rightEnd :=
      ⟨hx.1.le, hx.2.trans hq'_inv⟩
    have hInvAgree : (uInv x : ℝ) = gInv.extension x :=
      gInv.agrees hxInvSeg
    have hpInv : (p : ℝ) < (uInv x : ℝ) := by
      calc
        (p : ℝ) = gInv.extension (p : ℝ) := hInvExtp.symm
        _ < gInv.extension (x : ℝ) :=
          hInvStrict ⟨le_rfl, gInv.base_lt_rightEnd.le⟩
            ⟨hx.1.le, hx.2.trans hq'_inv⟩ hx.1
        _ = (uInv x : ℝ) := hInvAgree.symm
    have hInvMem : uInv x ∈ Set.Ioc p q :=
      ⟨hpInv, hxProps.2.2.1.le⟩
    calc
      (uInv x : ℝ) < (u (uInv x) : ℝ) :=
        hu_expands (uInv x) hInvMem
      _ = (x : ℝ) := congrArg Subtype.val hxProps.2.1
  have hInvNoFixed : ∀ x ∈ Set.Ioc p q', uInv x ≠ x := by
    intro x hx heq
    exact (ne_of_lt (hInvContracts x hx)) (congrArg Subtype.val heq)
  exact local_c1BV_Kopell_of_contracting gInv gv huInv_bv hpq'
    hq'_inv hq'_v huInv_fixed hv_fixed hcommInv hInvNoFixed
    ⟨q', ⟨hpq', le_rfl⟩, hfixedSeq_fixed n⟩ hInvContracts

theorem local_c1BV_Kopell
    {u v : IntervalMap} {p q : I}
    (gu : RightGermC1Diffeomorphism u p)
    (gv : RightGermC1Diffeomorphism v p)
    (hu_bv : gu.HasBoundedVariationLogDeriv)
    (hpq : p < q)
    (hq_u : q ≤ gu.rightEnd)
    (hq_v : q ≤ gv.rightEnd)
    (hu_fixed : IsFixedPoint u p)
    (hv_fixed : IsFixedPoint v p)
    (hcomm : Set.EqOn (u ∘ v) (v ∘ u) (Set.Icc p q))
    (hu_no_fixed : ∀ x ∈ Set.Ioc p q, u x ≠ x)
    (hv_has_fixed : ∃ y ∈ Set.Ioc p q, v y = y) :
    SameOneSidedGermAt .right p v identityIntervalMap := by
  rcases rightGerm_fixedPointFree_direction gu hpq hq_u hu_fixed
      hu_no_fixed with hu_contracts | hu_expands
  · exact local_c1BV_Kopell_of_contracting gu gv hu_bv hpq hq_u hq_v
      hu_fixed hv_fixed hcomm hu_no_fixed hv_has_fixed hu_contracts
  · exact local_c1BV_Kopell_of_expanding gu gv hu_bv hpq hq_u hq_v
      hu_fixed hv_fixed hcomm hu_no_fixed hv_has_fixed hu_expands

/-- Accumulating fixed points are the germ-level form in which the local
Kopell lemma is used below.  This wrapper performs all common-representative
shrinking explicitly. -/
private theorem local_c1BV_Kopell_identity_of_accumulating_fixedPoints
    {u v : IntervalMap} {p : I}
    (gu : RightGermC1Diffeomorphism u p)
    (gv : RightGermC1Diffeomorphism v p)
    (hu_bv : gu.HasBoundedVariationLogDeriv)
    (hu_fixed : IsFixedPoint u p)
    (hv_fixed : IsFixedPoint v p)
    (hu_moves : MovesStrictlyRightNear u p)
    (hcomm : RightGermCommute p u v)
    (hv_accumulates : ∀ q : I, p < q →
      ∃ y ∈ Set.Ioc p q, v y = y) :
    SameOneSidedGermAt .right p v identityIntervalMap := by
  rcases hu_moves with ⟨qmove, hpqmove, hmove⟩
  rcases hcomm with ⟨qcomm, hpqcomm, hcommOn⟩
  let r : I := min gu.rightEnd (min gv.rightEnd (min qmove qcomm))
  have hpr : p < r := by
    simp only [r, lt_min_iff]
    exact ⟨gu.base_lt_rightEnd, gv.base_lt_rightEnd,
      hpqmove, hpqcomm⟩
  obtain ⟨q, hpq, hqr⟩ := exists_between hpr
  have hq_u : q ≤ gu.rightEnd := hqr.le.trans (by simp [r])
  have hq_v : q ≤ gv.rightEnd := hqr.le.trans (by simp [r])
  have hq_move : q ≤ qmove := hqr.le.trans (by simp [r])
  have hq_comm : q ≤ qcomm := hqr.le.trans (by simp [r])
  apply local_c1BV_Kopell gu gv hu_bv hpq hq_u hq_v
      hu_fixed hv_fixed
  · exact hcommOn.mono (Set.Icc_subset_Icc le_rfl hq_comm)
  · intro x hx
    exact ne_of_gt (hmove x ⟨hx.1, hx.2.trans hq_move⟩)
  · exact hv_accumulates q hpq

/-- Translation number is additive on a commuting pair of selected lifts. -/
theorem translationNumber_add_of_commuting_lifts
    (F G : CircleHomeomorphismLift)
    (hcomm : Function.Commute (circleLiftFun F) (circleLiftFun G)) :
    selectedTranslationNumber (F * G) =
      selectedTranslationNumber F + selectedTranslationNumber G := by
  have hcomm' : _root_.Commute
      (F : CircleDeg1Lift) (G : CircleDeg1Lift) := by
    apply CircleDeg1Lift.ext
    intro x
    exact hcomm x
  simpa [selectedTranslationNumber] using
    CircleDeg1Lift.translationNumber_mul_of_commute hcomm'

/-- The kernel of translation number consists of lifts having a fixed point. -/
theorem translationNumber_zero_has_fixed_point
    (F : CircleHomeomorphismLift)
    (hzero : selectedTranslationNumber F = 0) :
    ∃ s : ℝ, circleLiftFun F s = s := by
  have hcont : Continuous (F : CircleDeg1Lift) := by
    simpa using (CircleDeg1Lift.toOrderIso F).continuous
  obtain ⟨s, hs⟩ :=
    (F : CircleDeg1Lift).exists_eq_add_translationNumber hcont
  change (F : CircleDeg1Lift).translationNumber = 0 at hzero
  rw [hzero, add_zero] at hs
  refine ⟨s, ?_⟩
  exact hs

/--
Kernel alternative on the physical germ: a zero-translation lift commuting
with the fixed-point-free `C^{1+BV}` deck germ is the identity germ.
-/
theorem translationNumber_kernel_forces_identity_germ
    {u v : IntervalMap} {p : I}
    (hu_fixed : IsFixedPoint u p)
    (hv_fixed : IsFixedPoint v p)
    (hu_bv : HasRightGermC1BV u p)
    (hv_c1 : HasRightGermC1Diffeomorphism v p)
    (hu_no_fixed : HasNoRightFixedPointNear u p)
    (hcomm : RightGermCommute p u v)
    (E : RightOrbitLineEmbedding p)
    (vLift : RightGermLineLift E v)
    (hv_zero : selectedTranslationNumber vLift.lift = 0) :
    SameOneSidedGermAt .right p v identityIntervalMap := by
  rcases hu_bv with ⟨gu, hgu_bv⟩
  rcases hv_c1 with ⟨gv⟩
  rcases hu_no_fixed with ⟨qnf, hpqnf, hnofix⟩
  rcases hcomm with ⟨qcomm, hpqcomm, hcommOn⟩
  let r : I := min gu.rightEnd
    (min gv.rightEnd (min qnf (min qcomm E.rightEnd)))
  have hpr : p < r := by
    simp only [r, lt_min_iff]
    exact ⟨gu.base_lt_rightEnd, gv.base_lt_rightEnd, hpqnf,
      hpqcomm, E.base_lt_rightEnd⟩
  obtain ⟨q, hpq, hqr⟩ := exists_between hpr
  have hq_gu : q ≤ gu.rightEnd :=
    hqr.le.trans (by simp [r])
  have hq_gv : q ≤ gv.rightEnd :=
    hqr.le.trans (by simp [r])
  have hq_nf : q ≤ qnf :=
    hqr.le.trans (by simp [r])
  have hq_comm : q ≤ qcomm :=
    hqr.le.trans (by simp [r])
  have hq_E : q < E.rightEnd :=
    hqr.trans_le (by simp [r])
  have hq_mem : q ∈ Set.Ioo p E.rightEnd := ⟨hpq, hq_E⟩
  obtain ⟨s, hs⟩ := translationNumber_zero_has_fixed_point vLift.lift hv_zero
  let bound : ℝ := min vLift.tailBound (E.coord q)
  obtain ⟨k : ℤ, hk⟩ := exists_int_lt (bound - s)
  let t : ℝ := s + (k : ℝ)
  have ht_bound : t < bound := by
    dsimp [t]
    linarith
  have ht_tail : t < vLift.tailBound :=
    ht_bound.trans_le (min_le_left _ _)
  have ht_coord : t < E.coord q :=
    ht_bound.trans_le (min_le_right _ _)
  have ht_top : t < E.top := ht_tail.trans vLift.tailBound_lt_top
  have ht_fixed : circleLiftFun vLift.lift t = t := by
    calc
      circleLiftFun vLift.lift t =
          circleLiftFun vLift.lift s + (k : ℝ) := by
        simpa [t, circleLiftFun] using
          (vLift.lift : CircleDeg1Lift).map_add_int s k
      _ = t := by rw [hs]
  let y : I := E.point t
  have hy_mem : y ∈ Set.Ioo p E.rightEnd := E.point_mem t ht_top
  have hvy_mem : v y ∈ Set.Ioo p E.rightEnd :=
    vLift.image_mem t ht_tail
  have hcoord_y : E.coord y = t := E.coord_point t ht_top
  have hcoord_vy : E.coord (v y) = t :=
    (vLift.intertwines t ht_tail).trans ht_fixed
  have hvy : v y = y :=
    E.coord_strictMono.injOn hvy_mem hy_mem
      (hcoord_vy.trans hcoord_y.symm)
  have hy_lt_q : y < q := by
    apply (E.coord_strictMono.lt_iff_lt hy_mem hq_mem).mp
    rw [hcoord_y]
    exact ht_coord
  apply local_c1BV_Kopell gu gv hgu_bv hpq hq_gu hq_gv
      hu_fixed hv_fixed
  · exact hcommOn.mono (Set.Icc_subset_Icc le_rfl hq_comm)
  · intro x hx
    exact hnofix x ⟨hx.1, hx.2.trans hq_nf⟩
  · exact ⟨y, ⟨hy_mem.1, hy_lt_q.le⟩, hvy⟩

/-- Pairwise disjoint forward images modulo deck translations have lengths
tending to zero.  This is the packing half of the Denjoy argument. -/
private theorem forwardWanderingLiftInterval_length_tendsto_zero
    (F : CircleHomeomorphismLift) {a b : ℝ}
    (hwandering : IsForwardWanderingLiftInterval F a b) :
    Tendsto
      (fun n : ℕ =>
        ((circleLiftFun F)^[n]) b - ((circleLiftFun F)^[n]) a)
      atTop (𝓝 0) := by
  apply interval_lengths_tendsto_zero_of_disjoint_mod_int
  · intro n
    simpa [circleLiftFun] using
      ((CircleDeg1Lift.toOrderIso F).strictMono.iterate n hwandering.1)
  · intro m n hmn k
    simpa [circleLiftFun, CircleDeg1Lift.coe_pow] using
      hwandering.2 m n hmn k

/-- Denjoy's inequality in its standard closest-return form: along an
unbounded sequence of return denominators, the logarithmic derivative of the
whole iterate is uniformly bounded on the line.  This is the remaining
continued-fraction/ordered-variation step of the Denjoy proof. -/
private theorem denjoy_logDeriv_bound_at_returnTimes
    (F : CircleHomeomorphismLift)
    (hregular : IsC1BVUnitLift F)
    (hirr : Irrational (selectedTranslationNumber F)) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      ∃ V : ℝ, ∀ n : ℕ, ∀ x : ℝ,
        |Real.log (deriv ((circleLiftFun F)^[q n]) x)| ≤ V := by
  simpa [circleLiftFun, selectedTranslationNumber] using
    exists_logDeriv_bound_at_returnTimes
      F hregular.1 hregular.2.1 hregular.2.2 hirr

/-- A direct consequence of Denjoy's logarithmic inequality: the same
return iterates have derivative uniformly bounded away from zero. -/
private theorem denjoy_returnTimes_uniform_deriv_lowerBound
    (F : CircleHomeomorphismLift)
    (hregular : IsC1BVUnitLift F)
    (hirr : Irrational (selectedTranslationNumber F)) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ x : ℝ,
        C ≤ deriv ((circleLiftFun F)^[q n]) x := by
  obtain ⟨q, hq, V, hbound⟩ :=
    denjoy_logDeriv_bound_at_returnTimes F hregular hirr
  refine ⟨q, hq, Real.exp (-V), Real.exp_pos _, ?_⟩
  intro n x
  have hiterpos : 0 < deriv ((circleLiftFun F)^[q n]) x := by
    rw [deriv_iterate_eq_prod]
    · exact Finset.prod_pos fun i _hi => hregular.2.1 _
    · intro i _hi
      exact hregular.1.differentiable_one.differentiableAt
  calc
    Real.exp (-V) ≤
        Real.exp (Real.log (deriv ((circleLiftFun F)^[q n]) x)) :=
      Real.exp_le_exp.mpr (neg_le_of_abs_le (hbound n x))
    _ = deriv ((circleLiftFun F)^[q n]) x := Real.exp_log hiterpos

/-- The analytic core of Denjoy's theorem needed below: an irrational
positive `C¹` degree-one lift whose log derivative has bounded variation
cannot have a nondegenerate interval with pairwise-disjoint forward images
modulo deck translations. -/
private theorem c1BV_no_forwardWanderingLiftInterval
    (F : CircleHomeomorphismLift)
    (hregular : IsC1BVUnitLift F)
    (hirr : Irrational (selectedTranslationNumber F))
    {a b : ℝ}
    (hwandering : IsForwardWanderingLiftInterval F a b) :
    False := by
  obtain ⟨q, hq, C, hC, hderiv⟩ :=
    denjoy_returnTimes_uniform_deriv_lowerBound F hregular hirr
  have hlength :=
    forwardWanderingLiftInterval_length_tendsto_zero F hwandering
  have hsubseq :
      Tendsto
        (fun n : ℕ =>
          ((circleLiftFun F)^[q n]) b -
            ((circleLiftFun F)^[q n]) a)
        atTop (𝓝 0) := hlength.comp hq
  have hab : a < b := hwandering.1
  have hlower : ∀ n : ℕ,
      C * (b - a) ≤
        ((circleLiftFun F)^[q n]) b -
          ((circleLiftFun F)^[q n]) a := by
    intro n
    have hcontinuous :
        ContinuousOn ((circleLiftFun F)^[q n]) (Set.Icc a b) :=
      (hregular.1.continuous.iterate (q n)).continuousOn
    have hdifferentiable :
        DifferentiableOn ℝ ((circleLiftFun F)^[q n]) (Set.Ioo a b) :=
      (hregular.1.differentiable_one.iterate (q n)).differentiableOn
    obtain ⟨x, _hx, hxderiv⟩ :=
      exists_deriv_eq_slope ((circleLiftFun F)^[q n]) hab
        hcontinuous hdifferentiable
    have hxlower := hderiv n x
    rw [hxderiv] at hxlower
    exact (le_div_iff₀ (sub_pos.mpr hab)).mp hxlower
  have hnonpos : C * (b - a) ≤ 0 :=
    ge_of_tendsto' hsubseq hlower
  exact (not_le_of_gt (mul_pos hC (sub_pos.mpr hab))) hnonpos

/-- The no-wandering-interval core of Denjoy's theorem.  Mathlib already
constructs a monotone degree-one semiconjugacy to the rotation with matching
translation number; bounded variation and irrationality force that
semiconjugacy itself to be a circle homeomorphism. -/
private theorem denjoy_semiconjugacy_isUnit
    (F : CircleHomeomorphismLift)
    (hregular : IsC1BVUnitLift F)
    (hirr : Irrational (selectedTranslationNumber F))
    (H : CircleDeg1Lift)
    (hsemiconj : Function.Semiconj H (F : CircleDeg1Lift)
      (CircleDeg1Lift.translate
        (Multiplicative.ofAdd (selectedTranslationNumber F)))) :
    IsUnit H := by
  have hdense : DenseRange H :=
    irrationalTranslation_semiconj_denseRange F H
      (selectedTranslationNumber F) hirr hsemiconj
  have hcontinuous : Continuous H :=
    H.monotone.continuous_of_denseRange hdense
  have hsurjective : Function.Surjective H :=
    (CircleDeg1Lift.continuous_iff_surjective H).mp hcontinuous
  have hinjective : Function.Injective H := by
    intro a b hab
    rcases lt_trichotomy a b with hab_lt | hab_eq | hba_lt
    · exact False.elim <|
        c1BV_no_forwardWanderingLiftInterval F hregular
          hirr
          (flatFiber_isForwardWanderingLiftInterval F H
            (selectedTranslationNumber F) hirr hsemiconj hab_lt hab)
    · exact hab_eq
    · exact False.elim <|
        c1BV_no_forwardWanderingLiftInterval F hregular
          hirr
          (flatFiber_isForwardWanderingLiftInterval F H
            (selectedTranslationNumber F) hirr hsemiconj hba_lt hab.symm)
  exact CircleDeg1Lift.isUnit_iff_bijective.mpr ⟨hinjective, hsurjective⟩

/-- Denjoy's theorem in the exact lift form needed on the irrational branch. -/
theorem denjoy_conjugacy_of_irrational_translationNumber
    (F : CircleHomeomorphismLift)
    (hregular : IsC1BVUnitLift F)
    (hirr : Irrational (selectedTranslationNumber F)) :
    ∃ H : CircleHomeomorphismLift, ∀ s : ℝ,
      circleLiftFun H (circleLiftFun F s) =
        circleLiftFun H s + selectedTranslationNumber F := by
  let R : CircleHomeomorphismLift :=
    CircleDeg1Lift.translate
      (Multiplicative.ofAdd (selectedTranslationNumber F))
  have htranslation :
      (F : CircleDeg1Lift).translationNumber =
        (R : CircleDeg1Lift).translationNumber := by
    change selectedTranslationNumber F =
      (R : CircleDeg1Lift).translationNumber
    simpa [R] using
      (CircleDeg1Lift.translationNumber_translate
        (selectedTranslationNumber F)).symm
  obtain ⟨H, hH⟩ :=
    CircleDeg1Lift.units_semiconj_of_translationNumber_eq htranslation
  have hHunit : IsUnit H :=
    denjoy_semiconjugacy_isUnit F hregular hirr H (by simpa [R] using hH)
  obtain ⟨Hunit, rfl⟩ := hHunit
  refine ⟨Hunit, ?_⟩
  intro s
  have hs := hH s
  simpa [R, circleLiftFun, CircleDeg1Lift.translate_apply,
    add_comm] using hs

/-- Germ equality between two compositions upgrades to exact equality of
the corresponding selected degree-one line lifts. -/
private theorem lineLift_mul_eq_mul_of_sameRightGerm_comp
    {p : I} {E : RightOrbitLineEmbedding p}
    {F G H K : IntervalMap}
    (LF : RightGermLineLift E F) (LG : RightGermLineLift E G)
    (LH : RightGermLineLift E H) (LK : RightGermLineLift E K)
    (hrel : SameOneSidedGermAt .right p (F ∘ G) (H ∘ K)) :
    LF.lift * LG.lift = LH.lift * LK.lift := by
  rcases hrel with ⟨q, hpq, hrelOn⟩
  let r : I := min q E.rightEnd
  have hpr : p < r := by
    simp only [r, lt_min_iff]
    exact ⟨hpq, E.base_lt_rightEnd⟩
  obtain ⟨q', hpq', hq'r⟩ := exists_between hpr
  have hq'q : q' < q := hq'r.trans_le (min_le_left _ _)
  have hq'E : q' < E.rightEnd := hq'r.trans_le (min_le_right _ _)
  have hq'mem : q' ∈ Set.Ioo p E.rightEnd := ⟨hpq', hq'E⟩
  have hLGto : Tendsto (circleLiftFun LG.lift) atBot atBot :=
    (LG.lift : CircleDeg1Lift).tendsto_atBot
  have hLKto : Tendsto (circleLiftFun LK.lift) atBot atBot :=
    (LK.lift : CircleDeg1Lift).tendsto_atBot
  have hevent : ∀ᶠ s : ℝ in atBot,
      s < LG.tailBound ∧
      circleLiftFun LG.lift s < LF.tailBound ∧
      s < LK.tailBound ∧
      circleLiftFun LK.lift s < LH.tailBound ∧
      s < E.coord q' := by
    filter_upwards [eventually_lt_atBot LG.tailBound,
      hLGto (eventually_lt_atBot LF.tailBound),
      eventually_lt_atBot LK.tailBound,
      hLKto (eventually_lt_atBot LH.tailBound),
      eventually_lt_atBot (E.coord q')] with s hsG hGsF hsK hKsH hscoord
    exact ⟨hsG, hGsF, hsK, hKsH, hscoord⟩
  obtain ⟨t, ht⟩ := eventually_atBot.mp hevent
  apply Units.ext
  apply circleDeg1Lift_ext_of_eqOn_Iio (t := t)
  intro s hst
  rcases ht s hst.le with ⟨hsG, hGsF, hsK, hKsH, hscoord⟩
  have hsTop : s < E.top := hscoord.trans (E.coord_lt_top hq'mem)
  have hsmem := E.point_mem s hsTop
  have hscoordPoint : E.coord (E.point s) = s := E.coord_point s hsTop
  have hpointlt : E.point s < q' :=
    (E.coord_strictMono.lt_iff_lt hsmem hq'mem).mp (by
      simpa [hscoordPoint] using hscoord)
  have hxrel : E.point s ∈ Set.Icc p q :=
    ⟨hsmem.1.le, hpointlt.le.trans hq'q.le⟩
  have hphysical : (F ∘ G) (E.point s) = (H ∘ K) (E.point s) :=
    hrelOn hxrel
  have hleft := LF.comp_intertwines LG hsG hGsF
  have hright := LH.comp_intertwines LK hsK hKsH
  change circleLiftFun LF.lift (circleLiftFun LG.lift s) =
    circleLiftFun LH.lift (circleLiftFun LK.lift s)
  calc
    circleLiftFun LF.lift (circleLiftFun LG.lift s) =
        E.coord ((F ∘ G) (E.point s)) := hleft.2.symm
    _ = E.coord ((H ∘ K) (E.point s)) := congrArg E.coord hphysical
    _ = circleLiftFun LH.lift (circleLiftFun LK.lift s) := hright.2

/-- A physical product-germ identity upgrades to the exact corresponding
power identity between selected line lifts. -/
private theorem lineLift_mul_eq_pow_of_sameRightGerm_comp
    {p : I} {E : RightOrbitLineEmbedding p}
    {F G H : IntervalMap}
    (LF : RightGermLineLift E F) (LG : RightGermLineLift E G)
    (LH : RightGermLineLift E H) (d : ℕ)
    (hrel : SameOneSidedGermAt .right p (F ∘ G) (iterateMap H d)) :
    LF.lift * LG.lift = LH.lift ^ d := by
  rcases hrel with ⟨q, hpq, hrelOn⟩
  let r : I := min q E.rightEnd
  have hpr : p < r := by
    simp only [r, lt_min_iff]
    exact ⟨hpq, E.base_lt_rightEnd⟩
  obtain ⟨q', hpq', hq'r⟩ := exists_between hpr
  have hq'q : q' < q := hq'r.trans_le (min_le_left _ _)
  have hq'E : q' < E.rightEnd := hq'r.trans_le (min_le_right _ _)
  have hq'mem : q' ∈ Set.Ioo p E.rightEnd := ⟨hpq', hq'E⟩
  have hLGto : Tendsto (circleLiftFun LG.lift) atBot atBot :=
    (LG.lift : CircleDeg1Lift).tendsto_atBot
  have horbitEvent : ∀ᶠ s : ℝ in atBot,
      ∀ i ∈ Finset.range (d + 1),
        (((LH.lift : CircleDeg1Lift) ^ i) s) < LH.tailBound :=
    (Filter.eventually_all_finset (Finset.range (d + 1))).2
      (fun i _hi =>
        ((LH.lift : CircleDeg1Lift) ^ i).tendsto_atBot
          (eventually_lt_atBot LH.tailBound))
  have hevent : ∀ᶠ s : ℝ in atBot,
      s < LG.tailBound ∧
      circleLiftFun LG.lift s < LF.tailBound ∧
      (∀ i ∈ Finset.range (d + 1),
        (((LH.lift : CircleDeg1Lift) ^ i) s) < LH.tailBound) ∧
      s < E.coord q' := by
    filter_upwards [eventually_lt_atBot LG.tailBound,
      hLGto (eventually_lt_atBot LF.tailBound), horbitEvent,
      eventually_lt_atBot (E.coord q')] with s hsG hGsF horbit hscoord
    exact ⟨hsG, hGsF, horbit, hscoord⟩
  obtain ⟨t, ht⟩ := eventually_atBot.mp hevent
  apply Units.ext
  apply circleDeg1Lift_ext_of_eqOn_Iio (t := t)
  intro s hst
  rcases ht s hst.le with ⟨hsG, hGsF, horbit, hscoord⟩
  have hsTop : s < E.top := hscoord.trans (E.coord_lt_top hq'mem)
  have hsmem := E.point_mem s hsTop
  have hscoordPoint : E.coord (E.point s) = s := E.coord_point s hsTop
  have hpointlt : E.point s < q' :=
    (E.coord_strictMono.lt_iff_lt hsmem hq'mem).mp (by
      simpa [hscoordPoint] using hscoord)
  have hxrel : E.point s ∈ Set.Icc p q :=
    ⟨hsmem.1.le, hpointlt.le.trans hq'q.le⟩
  have hphysical :
      (F ∘ G) (E.point s) = iterateMap H d (E.point s) :=
    hrelOn hxrel
  have hleft := LF.comp_intertwines LG hsG hGsF
  have hright := LH.iterate_intertwines (s := s) (n := d) (by
    intro i hi
    exact horbit i (Finset.mem_range.mpr (by omega)))
  change circleLiftFun LF.lift (circleLiftFun LG.lift s) =
    ((LH.lift : CircleDeg1Lift) ^ d) s
  calc
    circleLiftFun LF.lift (circleLiftFun LG.lift s) =
        E.coord ((F ∘ G) (E.point s)) := hleft.2.symm
    _ = E.coord (iterateMap H d (E.point s)) := congrArg E.coord hphysical
    _ = ((LH.lift : CircleDeg1Lift) ^ d) s := hright.2

/-- The sum of two real-valued functions of bounded variation again has
bounded variation.  This elementary closure lemma is not currently exposed
by mathlib's general emetric-space API. -/
private theorem boundedVariationOn_add
    {α : Type*} [LinearOrder α] {f g : α → ℝ} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x + g x) s := by
  unfold BoundedVariationOn at hf hg ⊢
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩)
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  calc
    (∑ i ∈ Finset.range n,
        edist (f (u (i + 1)) + g (u (i + 1)))
          (f (u i) + g (u i))) ≤
        ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) +
            edist (g (u (i + 1))) (g (u i))) := by
      exact Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n,
          edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n,
          edist (g (u (i + 1))) (g (u i)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ eVariationOn f s + eVariationOn g s :=
      add_le_add (eVariationOn.sum_le hu hus) (eVariationOn.sum_le hu hus)

/-!
This scratch module develops the reusable analytic half of the normalized
orbit-line construction.  A local lift on one fundamental interval is
periodized through its positive derivative.  Periodizing the derivative,
rather than the map itself, makes the seam regularity explicit: equality of
the endpoint derivatives is exactly the condition needed for a global `C¹`
lift.
-/

/-- A `C¹+BV` map on one fundamental interval, with the value and derivative
seams matched, extends to a regular invertible degree-one lift. -/
private theorem exists_regularCircleLift_of_fundamentalInterval
    {U : Set ℝ} (g : ℝ → ℝ)
    (hgC1 : ContDiffOn ℝ 1 g U)
    (hUopen : IsOpen U)
    (hIccU : Set.Icc (0 : ℝ) 1 ⊆ U)
    (hgpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < deriv g x)
    (hgvalue : g 1 = g 0 + 1)
    (hgseam : deriv g 1 = deriv g 0)
    (hgBV : BoundedVariationOn
      (fun x : ℝ => Real.log (deriv g x)) (Set.Icc (0 : ℝ) 1)) :
    ∃ F : CircleHomeomorphismLift,
      IsC1BVUnitLift F ∧
        Set.EqOn (circleLiftFun F) g (Set.Icc (0 : ℝ) 1) := by
  let w : ℝ → ℝ := fun x => deriv g (Int.fract x)
  have hgDerivCont : ContinuousOn (deriv g) (Set.Icc (0 : ℝ) 1) :=
    (hgC1.continuousOn_deriv_of_isOpen hUopen (by norm_num)).mono hIccU
  have hgDiffAt : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ g x := by
    intro x hx
    exact (hgC1.contDiffAt
      (hUopen.mem_nhds (hIccU hx))).differentiableAt_one
  have hwEq : Set.EqOn w (deriv g) (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    rcases hx.2.eq_or_lt with h | h
    · subst x
      simp [w, hgseam]
    · simp [w, Int.fract_eq_self.2 ⟨hx.1, h⟩]
  have hwcont : Continuous w := by
    dsimp only [w]
    apply ContinuousOn.comp_fract'' hgDerivCont
    simpa using hgseam.symm
  have hwpos : ∀ x : ℝ, 0 < w x := by
    intro x
    apply hgpos
    exact ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hwperiodic : Function.Periodic w 1 := by
    intro x
    simp [w]
  let liftFun : ℝ → ℝ := fun x =>
    g 0 + ∫ t in (0 : ℝ)..x, w t
  have hliftDeriv : ∀ x : ℝ, HasDerivAt liftFun (w x) x := by
    intro x
    have h := intervalIntegral.integral_hasDerivAt_right
      (hwcont.intervalIntegrable (0 : ℝ) x)
      hwcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hwcont.continuousAt
    simpa only [liftFun] using h.const_add (g 0)
  have hliftC1 : ContDiff ℝ 1 liftFun := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hliftDeriv x).differentiableAt, ?_⟩
    have hderiv : deriv liftFun = w := by
      funext x
      exact (hliftDeriv x).deriv
    rw [hderiv]
    exact hwcont
  have hintegralEq : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (∫ t in (0 : ℝ)..x, w t) = g x - g 0 := by
    intro x hx
    calc
      (∫ t in (0 : ℝ)..x, w t) =
          ∫ t in (0 : ℝ)..x, deriv g t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        apply hwEq
        rw [Set.uIoc_of_le hx.1] at ht
        exact ⟨ht.1.le, ht.2.trans hx.2⟩
      _ = g x - g 0 := by
        apply intervalIntegral.integral_deriv_eq_sub
        · intro t _ht
          exact hgDiffAt t (by
            rw [Set.uIcc_of_le hx.1] at _ht
            exact ⟨_ht.1, _ht.2.trans hx.2⟩)
        · exact
            (hgDerivCont.mono (Set.Icc_subset_Icc le_rfl hx.2)).intervalIntegrable_of_Icc hx.1
  have hliftEq : Set.EqOn liftFun g (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    dsimp only [liftFun]
    rw [hintegralEq x hx]
    ring
  have hintegralOne : (∫ t in (0 : ℝ)..1, w t) = 1 := by
    rw [hintegralEq 1 (by simp), hgvalue]
    ring
  have hliftAddOne : ∀ x : ℝ, liftFun (x + 1) = liftFun x + 1 := by
    intro x
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hwcont.intervalIntegrable (μ := (volume : Measure ℝ)) (0 : ℝ) x)
      (hwcont.intervalIntegrable (μ := (volume : Measure ℝ)) x (x + 1))
    have hperiod := hwperiodic.intervalIntegral_add_eq x 0
    dsimp only [liftFun]
    rw [← hsplit, hperiod]
    simp only [zero_add, hintegralOne]
    ring
  have hliftStrict : StrictMono liftFun := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(hliftDeriv x).deriv]
    exact hwpos x
  let lift : CircleDeg1Lift :=
    { toOrderHom := ⟨liftFun, hliftStrict.monotone⟩
      map_add_one' := hliftAddOne }
  have hliftContinuous : Continuous (lift : ℝ → ℝ) := by
    simpa [lift] using hliftC1.continuous
  have hliftSurjective : Function.Surjective lift :=
    (CircleDeg1Lift.continuous_iff_surjective lift).mp hliftContinuous
  have hliftInjective : Function.Injective lift := by
    simpa [lift] using hliftStrict.injective
  have hliftUnit : IsUnit lift :=
    CircleDeg1Lift.isUnit_iff_bijective.mpr
      ⟨hliftInjective, hliftSurjective⟩
  obtain ⟨F, hF⟩ := hliftUnit
  have hFfun : circleLiftFun F = liftFun := by
    funext x
    have hx := congrArg (fun L : CircleDeg1Lift => L x) hF
    simpa [circleLiftFun, lift] using hx
  refine ⟨F, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [hFfun] using hliftC1
    · intro x
      rw [hFfun, (hliftDeriv x).deriv]
      exact hwpos x
    · unfold BoundedVariationOn at hgBV ⊢
      rw [eVariationOn.eq_of_eqOn (s := Set.Icc (0 : ℝ) 1) (f :=
        fun x : ℝ => Real.log (deriv (circleLiftFun F) x)) (f' :=
        fun x : ℝ => Real.log (deriv g x))]
      · exact hgBV
      · intro x hx
        change Real.log (deriv (circleLiftFun F) x) =
          Real.log (deriv g x)
        rw [hFfun, (hliftDeriv x).deriv, hwEq hx]
  · intro x hx
    rw [hFfun]
    exact hliftEq hx

/-! ## Fixed skeleton for the physical Abel coordinate

The remaining construction is deliberately split at its mathematical seam.
The first theorem constructs a smooth Abel coordinate for the repelling
germ alone.  The second theorem descends one commuting regular germ through
that coordinate.  The final pair theorem is then only assembly, so progress
on the construction and on the descent can be checked independently.
-/

/-- A normalized Abel coordinate with the precise local regularity needed to
transport bounded logarithmic variation through commuting germs. -/
private structure NormalizedC1BVAbelCoordinate
    (f : IntervalMap) (p : I) where
  embedding : RightOrbitLineEmbedding p
  fAction : RightGermLineLift embedding f
  f_translation : ∀ s : ℝ,
    circleLiftFun fAction.lift s = s + 1
  coordExtension : ℝ → ℝ
  pointExtension : ℝ → ℝ
  coord_agrees : ∀ x ∈ Set.Ioo p embedding.rightEnd,
    coordExtension (x : ℝ) = embedding.coord x
  point_agrees : ∀ s < embedding.top,
    pointExtension s = (embedding.point s : ℝ)
  coord_contDiff : ContDiffOn ℝ 1 coordExtension
    (Set.Ioo (p : ℝ) (embedding.rightEnd : ℝ))
  point_contDiff : ContDiffOn ℝ 1 pointExtension
    (Set.Iio embedding.top)
  coord_deriv_pos : ∀ x ∈
      Set.Ioo (p : ℝ) (embedding.rightEnd : ℝ),
    0 < deriv coordExtension x
  point_deriv_pos : ∀ s < embedding.top,
    0 < deriv pointExtension s
  coord_logDeriv_bv : ∀ a b : ℝ,
    (p : ℝ) < a → b < (embedding.rightEnd : ℝ) → a ≤ b →
      BoundedVariationOn
        (fun x : ℝ => Real.log (deriv coordExtension x))
        (Set.Icc a b)
  point_logDeriv_bv : ∀ a b : ℝ, b < embedding.top → a ≤ b →
    BoundedVariationOn
      (fun s : ℝ => Real.log (deriv pointExtension s))
      (Set.Icc a b)

/-- A positive right-germ representative fixing its base maps a sufficiently
small punctured interval into any prescribed larger right neighborhood. -/
private theorem exists_rightInterval_mapsInto
    {G : IntervalMap} {p r : I}
    (gG : RightGermC1Diffeomorphism G p)
    (hGfixed : IsFixedPoint G p) (hpr : p < r) :
    ∃ q : I, p < q ∧ q < gG.rightEnd ∧
      ∀ x ∈ Set.Ioc p q, G x ∈ Set.Ioo p r := by
  have hpMem : (p : ℝ) ∈
      Set.Icc (p : ℝ) (gG.rightEnd : ℝ) :=
    ⟨le_rfl, gG.base_lt_rightEnd.le⟩
  have hExtP : gG.extension (p : ℝ) = (p : ℝ) := by
    calc
      gG.extension (p : ℝ) = (G p : ℝ) := (gG.agrees hpMem).symm
      _ = (p : ℝ) := congrArg Subtype.val hGfixed
  have hC1At : ContDiffAt ℝ 1 gG.extension (p : ℝ) :=
    gG.contDiff_one.contDiffAt
      (gG.isOpen_neighborhood.mem_nhds (gG.segment_subset hpMem))
  have hNear : gG.extension ⁻¹' Set.Iio (r : ℝ) ∈ nhds (p : ℝ) := by
    apply hC1At.continuousAt
    rw [hExtP]
    exact Iio_mem_nhds hpr
  obtain ⟨s, hps, hIccS⟩ :=
    mem_nhdsGE_iff_exists_Icc_subset.mp
      (mem_nhdsWithin_of_mem_nhds hNear)
  have hpMin : (p : ℝ) < min s (gG.rightEnd : ℝ) :=
    lt_min hps gG.base_lt_rightEnd
  obtain ⟨qReal, hpq, hqMin⟩ := exists_between hpMin
  have hqs : qReal < s := hqMin.trans_le (min_le_left _ _)
  have hqG : qReal < (gG.rightEnd : ℝ) :=
    hqMin.trans_le (min_le_right _ _)
  let q : I := ⟨qReal, ⟨p.property.1.trans hpq.le,
    hqG.le.trans gG.rightEnd.property.2⟩⟩
  have hExtCont : ContinuousOn gG.extension
      (Set.Icc (p : ℝ) (gG.rightEnd : ℝ)) :=
    gG.contDiff_one.continuousOn.mono gG.segment_subset
  have hExtStrict : StrictMonoOn gG.extension
      (Set.Icc (p : ℝ) (gG.rightEnd : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hExtCont
    intro x hx
    exact gG.deriv_pos x (interior_subset hx)
  refine ⟨q, hpq, hqG, ?_⟩
  intro x hx
  have hxG : (x : ℝ) ∈
      Set.Icc (p : ℝ) (gG.rightEnd : ℝ) :=
    ⟨hx.1.le, hx.2.trans hqG.le⟩
  have hAgree : (G x : ℝ) = gG.extension (x : ℝ) :=
    gG.agrees ⟨hx.1.le, hx.2.trans hqG.le⟩
  constructor
  · change (p : ℝ) < (G x : ℝ)
    rw [hAgree, ← hExtP]
    exact hExtStrict hpMem hxG hx.1
  · change (G x : ℝ) < (r : ℝ)
    rw [hAgree]
    have hxq : (x : ℝ) ≤ qReal := hx.2
    exact hIccS ⟨hx.1.le, hxq.trans hqs.le⟩

/-- Equality with a degree-one lift on one half-open fundamental interval
propagates through every earlier translate, provided the physical expression
satisfies the same add-one identity on that tail. -/
private theorem circleDeg1Lift_eqOn_Iio_of_fundamentalInterval
    (F : CircleDeg1Lift) (raw : ℝ → ℝ) (a : ℝ)
    (hraw : ∀ s < a + 1, raw (s + 1) = raw s + 1)
    (hbase : Set.EqOn F raw (Set.Ico a (a + 1))) :
    ∀ s < a + 1, F s = raw s := by
  intro s hs
  obtain ⟨n : ℤ, hn, _hnUnique⟩ :=
    existsUnique_add_zsmul_mem_Ico (by positivity : (0 : ℝ) < 1) s a
  have hn' : s + (n : ℝ) ∈ Set.Ico a (a + 1) := by
    simpa using hn
  have hnNonneg : 0 ≤ n := by
    by_contra hnNot
    have hnNeg : n < 0 := lt_of_not_ge hnNot
    have hnLe : n ≤ -1 := by omega
    have hnLeReal : (n : ℝ) ≤ -1 := by exact_mod_cast hnLe
    have hyLt : s + (n : ℝ) < a := by linarith
    exact (not_lt_of_ge hn'.1) hyLt
  let k : ℕ := n.toNat
  have hkCast : (k : ℝ) = (n : ℝ) := by
    dsimp only [k]
    exact_mod_cast Int.toNat_of_nonneg hnNonneg
  have hyMem : s + (k : ℝ) ∈ Set.Ico a (a + 1) := by
    simpa [hkCast] using hn'
  have hrawIter : ∀ j : ℕ, s + (j : ℝ) < a + 1 →
      raw (s + (j : ℝ)) = raw s + (j : ℝ) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        have hjPrev : s + (j : ℝ) < a + 1 := by
          have : (j : ℝ) ≤ (j + 1 : ℕ) := by norm_num
          linarith
        calc
          raw (s + (j + 1 : ℕ)) =
              raw ((s + (j : ℝ)) + 1) := by congr 1 <;> push_cast <;> ring
          _ = raw (s + (j : ℝ)) + 1 := hraw _ hjPrev
          _ = (raw s + (j : ℝ)) + 1 := by rw [ih hjPrev]
          _ = raw s + (j + 1 : ℕ) := by push_cast; ring
  have hrawK := hrawIter k hyMem.2
  have hFK : F (s + (k : ℝ)) = F s + (k : ℝ) := by
    simpa using F.map_add_nat s k
  have hbaseK := hbase hyMem
  linarith

/-- Parameters below the coordinate of a physical point represent strictly
earlier physical points. -/
private theorem RightOrbitLineEmbedding.point_lt_of_lt_coord
    {p : I} (E : RightOrbitLineEmbedding p)
    {s : ℝ} {q : I} (hq : q ∈ Set.Ioo p E.rightEnd)
    (hs : s < E.coord q) : E.point s < q := by
  have hsTop : s < E.top := hs.trans (E.coord_lt_top hq)
  have hsMem := E.point_mem s hsTop
  apply (E.coord_strictMono.lt_iff_lt hsMem hq).mp
  rw [E.coord_point s hsTop]
  exact hs

/-- Closure of real-valued bounded variation under pointwise negation. -/
private theorem boundedVariationOn_neg
    {α : Type*} [LinearOrder α] {f : α → ℝ} {s : Set α}
    (hf : BoundedVariationOn f s) :
    BoundedVariationOn (fun x ↦ -f x) s := by
  have hneg : LipschitzOnWith 1 (fun x : ℝ ↦ -x) Set.univ :=
    isometry_neg.lipschitz.lipschitzOnWith
  simpa [Function.comp_def] using
    hneg.comp_boundedVariationOn (fun _ _ ↦ Set.mem_univ _) hf

/-- All domain choices for one fundamental interval of the repelling germ. -/
private structure AbelFundamentalData
    (f : IntervalMap) (p : I) where
  fixed : IsFixedPoint f p
  germ : RightGermC1Diffeomorphism f p
  germ_logDeriv_bv : germ.HasBoundedVariationLogDeriv
  moveEnd : I
  base_lt_moveEnd : p < moveEnd
  moves : ∀ x ∈ Set.Ioc p moveEnd, x < f x
  a : I
  b : I
  base_lt_a : p < a
  a_lt_b : a < b
  b_lt_moveEnd : b < moveEnd
  b_lt_germEnd : b < germ.rightEnd
  b_eq : b = f a

/-- Select a complete fundamental interval strictly inside every local
representative. -/
private theorem exists_abelFundamentalData
    {f : IntervalMap} {p : I}
    (hf_fixed : IsFixedPoint f p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p) :
    Nonempty (AbelFundamentalData f p) := by
  rcases hf_regular with ⟨gf, hgfBV⟩
  rcases hf_repelling with ⟨qMove, hpMove, hmove⟩
  let r : I := min qMove gf.rightEnd
  have hpr : p < r := by
    exact (lt_min_iff.mpr ⟨hpMove, gf.base_lt_rightEnd⟩)
  obtain ⟨qMap, hpMap, hqMapG, hmaps⟩ :=
    exists_rightInterval_mapsInto gf hf_fixed hpr
  have hpSmall : p < min qMap r := lt_min hpMap hpr
  obtain ⟨a, hpa, haSmall⟩ := exists_between hpSmall
  have haq : a < qMap := haSmall.trans_le (min_le_left _ _)
  have har : a < r := haSmall.trans_le (min_le_right _ _)
  have haIoc : a ∈ Set.Ioc p qMap := ⟨hpa, haq.le⟩
  have hfa := hmaps a haIoc
  let b : I := f a
  have hab : a < b := by
    apply hmove a
    refine ⟨hpa, ?_⟩
    exact har.le.trans (min_le_left _ _)
  have hbMove : b < qMove := by
    exact hfa.2.trans_le (min_le_left _ _)
  have hbG : b < gf.rightEnd := by
    exact hfa.2.trans_le (min_le_right _ _)
  exact ⟨{
    fixed := hf_fixed
    germ := gf
    germ_logDeriv_bv := hgfBV
    moveEnd := qMove
    base_lt_moveEnd := hpMove
    moves := hmove
    a := a
    b := b
    base_lt_a := hpa
    a_lt_b := hab
    b_lt_moveEnd := hbMove
    b_lt_germEnd := hbG
    b_eq := rfl }⟩

namespace AbelFundamentalData

private theorem extension_base
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) :
    D.germ.extension (p : ℝ) = (p : ℝ) := by
  calc
    D.germ.extension (p : ℝ) = (f p : ℝ) :=
      (D.germ.agrees ⟨le_rfl, D.germ.base_lt_rightEnd.le⟩).symm
    _ = (p : ℝ) := congrArg Subtype.val D.fixed

private theorem extension_a
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) :
    D.germ.extension (D.a : ℝ) = (D.b : ℝ) := by
  have haMem : D.a ∈ Set.Icc p D.germ.rightEnd :=
    ⟨D.base_lt_a.le, D.a_lt_b.le.trans D.b_lt_germEnd.le⟩
  calc
    D.germ.extension (D.a : ℝ) = (f D.a : ℝ) :=
      (D.germ.agrees haMem).symm
    _ = (D.b : ℝ) := congrArg Subtype.val D.b_eq.symm

private theorem extension_continuousOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) :
    ContinuousOn D.germ.extension
      (Set.Icc (p : ℝ) (D.b : ℝ)) :=
  D.germ.contDiff_one.continuousOn.mono fun _ hx ↦
    D.germ.segment_subset ⟨hx.1, hx.2.trans D.b_lt_germEnd.le⟩

private theorem extension_strictMonoOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) :
    StrictMonoOn D.germ.extension
      (Set.Icc (p : ℝ) (D.b : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    D.extension_continuousOn
  intro x hx
  have hx' : x ∈ Set.Icc (p : ℝ) (D.b : ℝ) := interior_subset hx
  exact D.germ.deriv_pos x
    ⟨hx'.1, hx'.2.trans D.b_lt_germEnd.le⟩

/-- The selected representative maps its first closed fundamental segment
order-isomorphically onto the next one. -/
private theorem exists_segmentOrderIso
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) :
    ∃ e : Set.Icc (p : ℝ) (D.a : ℝ) ≃o
        Set.Icc (p : ℝ) (D.b : ℝ),
      ∀ x, (e x : ℝ) = D.germ.extension x := by
  have hpa : (p : ℝ) ≤ (D.a : ℝ) := D.base_lt_a.le
  have hcont : ContinuousOn D.germ.extension
      (Set.Icc (p : ℝ) (D.a : ℝ)) :=
    D.extension_continuousOn.mono
      (Set.Icc_subset_Icc le_rfl D.a_lt_b.le)
  have hstrict : StrictMonoOn D.germ.extension
      (Set.Icc (p : ℝ) (D.a : ℝ)) :=
    D.extension_strictMonoOn.mono
      (Set.Icc_subset_Icc le_rfl D.a_lt_b.le)
  have himage : D.germ.extension ''
      Set.Icc (p : ℝ) (D.a : ℝ) =
      Set.Icc (p : ℝ) (D.b : ℝ) := by
    rw [hcont.image_Icc_of_monotoneOn hpa hstrict.monotoneOn,
      D.extension_base, D.extension_a]
  let F : Set.Icc (p : ℝ) (D.a : ℝ) →
      Set.Icc (p : ℝ) (D.b : ℝ) := fun x ↦
    ⟨D.germ.extension x, by
      rw [← himage]
      exact ⟨x, x.property, rfl⟩⟩
  have hFstrict : StrictMono F := by
    intro x y hxy
    exact hstrict x.property y.property hxy
  have hFsurj : Surjective F := by
    intro y
    have hy : (y : ℝ) ∈ D.germ.extension ''
        Set.Icc (p : ℝ) (D.a : ℝ) := by
      rw [himage]
      exact y.property
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let e := StrictMono.orderIsoOfSurjective F hFstrict hFsurj
  refine ⟨e, ?_⟩
  intro x
  rfl

/-- A smooth normalized coordinate on one fundamental interval, with the
exact derivative seam required for `C¹` gluing. -/
private structure AbelSeed (D : AbelFundamentalData f p) where
  psi : ℝ → ℝ
  contDiff : ContDiff ℝ 1 psi
  value_a : psi D.a = 0
  value_b : psi D.b = 1
  deriv_pos : ∀ x ∈ Set.Icc (D.a : ℝ) (D.b : ℝ),
    0 < deriv psi x
  deriv_seam : deriv psi D.b * deriv D.germ.extension D.a =
    deriv psi D.a
  logDeriv_bv : BoundedVariationOn
    (fun x : ℝ ↦ Real.log (deriv psi x))
    (Set.Icc (D.a : ℝ) (D.b : ℝ))

/-- The quadratic seed obtained by linearly interpolating a positive
derivative from `f'(a)` to `1`. -/
private theorem exists_abelSeed
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) :
    Nonempty (AbelSeed D) := by
  let L : ℝ := (D.b : ℝ) - (D.a : ℝ)
  have hL : 0 < L := sub_pos.mpr D.a_lt_b
  let r : ℝ := deriv D.germ.extension (D.a : ℝ)
  have hr : 0 < r := D.germ.deriv_pos _
    ⟨D.base_lt_a.le, D.a_lt_b.le.trans D.b_lt_germEnd.le⟩
  let c : ℝ := (1 - r) / (2 * L)
  let N : ℝ := L * (r + 1) / 2
  have hN : 0 < N := by
    dsimp [N]
    positivity
  let w : ℝ → ℝ := fun x ↦ r + 2 * c * (x - (D.a : ℝ))
  let psi : ℝ → ℝ := fun x ↦
    (r * (x - (D.a : ℝ)) +
      c * (x - (D.a : ℝ)) ^ 2) / N
  have hpsiDerivAt : ∀ x : ℝ, HasDerivAt psi (w x / N) x := by
    intro x
    have hu : HasDerivAt (fun y : ℝ ↦ y - (D.a : ℝ)) 1 x :=
      (hasDerivAt_id x).sub_const _
    have hraw := (hu.const_mul r).add ((hu.pow 2).const_mul c) |>.div_const N
    convert hraw using 1 <;> dsimp [psi, w] <;> ring
  have hpsiDeriv : ∀ x : ℝ, deriv psi x = w x / N :=
    fun x ↦ (hpsiDerivAt x).deriv
  have hw_formula : ∀ x : ℝ,
      w x = r + (1 - r) * (x - (D.a : ℝ)) / L := by
    intro x
    dsimp [w, c]
    field_simp
    <;> ring
  have hw_pos : ∀ x ∈ Set.Icc (D.a : ℝ) (D.b : ℝ),
      0 < w x := by
    intro x hx
    have ht0 : 0 ≤ (x - (D.a : ℝ)) / L :=
      div_nonneg (sub_nonneg.mpr hx.1) hL.le
    have ht1 : (x - (D.a : ℝ)) / L ≤ 1 := by
      apply (div_le_one hL).2
      dsimp [L]
      linarith [hx.2]
    rw [hw_formula]
    let t : ℝ := (x - (D.a : ℝ)) / L
    have ht0' : 0 ≤ t := ht0
    have ht1' : t ≤ 1 := ht1
    have hid : r + (1 - r) * t = (1 - t) * r + t := by ring
    have heq : r + (1 - r) * (x - (D.a : ℝ)) / L =
        r + (1 - r) * t := by
      dsimp [t]
      ring
    rw [heq, hid]
    by_cases ht : t = 1
    · rw [ht]
      simp
    · have htlt : t < 1 := lt_of_le_of_ne ht1' ht
      have hfirst : 0 < (1 - t) * r := mul_pos (sub_pos.mpr htlt) hr
      linarith
  have hpsiPos : ∀ x ∈ Set.Icc (D.a : ℝ) (D.b : ℝ),
      0 < deriv psi x := by
    intro x hx
    rw [hpsiDeriv]
    exact div_pos (hw_pos x hx) hN
  have hpsiA : psi (D.a : ℝ) = 0 := by
    simp [psi]
  have hpsiB : psi (D.b : ℝ) = 1 := by
    change (r * L + c * L ^ 2) / N = 1
    dsimp [c, N]
    field_simp [hL.ne']
    <;> ring
  have hwA : w (D.a : ℝ) = r := by simp [w]
  have hwB : w (D.b : ℝ) = 1 := by
    rw [hw_formula]
    change r + (1 - r) * L / L = 1
    field_simp [hL.ne']
    ring
  have hseam : deriv psi (D.b : ℝ) *
      deriv D.germ.extension (D.a : ℝ) = deriv psi (D.a : ℝ) := by
    rw [hpsiDeriv, hpsiDeriv, hwA, hwB]
    change 1 / N * r = r / N
    field_simp
  have hlogBV : BoundedVariationOn
      (fun x : ℝ ↦ Real.log (deriv psi x))
      (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
    have hEq : Set.EqOn
        (fun x : ℝ ↦ Real.log (deriv psi x))
        (fun x : ℝ ↦ Real.log (w x / N))
        (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
      intro x hx
      change Real.log (deriv psi x) = Real.log (w x / N)
      rw [hpsiDeriv]
    rw [BoundedVariationOn, eVariationOn.eq_of_eqOn hEq]
    by_cases hcr : 0 ≤ c
    · have hwmono : Monotone w := by
        intro x y hxy
        dsimp [w]
        nlinarith
      have hlogmono : MonotoneOn (fun x : ℝ ↦ Real.log (w x / N))
          (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
        intro x hx y hy hxy
        apply Real.log_le_log (div_pos (hw_pos x hx) hN)
        exact div_le_div_of_nonneg_right (hwmono hxy) hN.le
      have hlocal := hlogmono.locallyBoundedVariationOn
        (D.a : ℝ) (D.b : ℝ)
        (show (D.a : ℝ) ∈ Set.Icc (D.a : ℝ) (D.b : ℝ) by
          exact ⟨le_rfl, D.a_lt_b.le⟩)
        (show (D.b : ℝ) ∈ Set.Icc (D.a : ℝ) (D.b : ℝ) by
          exact ⟨D.a_lt_b.le, le_rfl⟩)
      simpa only [Set.inter_self] using hlocal
    · have hc : c ≤ 0 := le_of_not_ge hcr
      have hwanti : Antitone w := by
        intro x y hxy
        dsimp [w]
        nlinarith
      have hloganti : AntitoneOn (fun x : ℝ ↦ Real.log (w x / N))
          (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
        intro x hx y hy hxy
        apply Real.log_le_log (div_pos (hw_pos y hy) hN)
        exact div_le_div_of_nonneg_right (hwanti hxy) hN.le
      have hnegmono : MonotoneOn
          (fun x : ℝ ↦ -Real.log (w x / N))
          (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
        intro x hx y hy hxy
        exact neg_le_neg (hloganti hx hy hxy)
      have hnegLocal := hnegmono.locallyBoundedVariationOn
        (D.a : ℝ) (D.b : ℝ)
        (show (D.a : ℝ) ∈ Set.Icc (D.a : ℝ) (D.b : ℝ) by
          exact ⟨le_rfl, D.a_lt_b.le⟩)
        (show (D.b : ℝ) ∈ Set.Icc (D.a : ℝ) (D.b : ℝ) by
          exact ⟨D.a_lt_b.le, le_rfl⟩)
      have hnegBV : BoundedVariationOn
          (fun x : ℝ ↦ -Real.log (w x / N))
          (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
        simpa only [Set.inter_self] using hnegLocal
      have hback := (LipschitzWith.id.neg :
        LipschitzWith 1 (fun y : ℝ ↦ -y)).comp_boundedVariationOn hnegBV
      simpa [Function.comp_def] using hback
  refine ⟨{
    psi := psi
    contDiff := ?_
    value_a := hpsiA
    value_b := hpsiB
    deriv_pos := hpsiPos
    deriv_seam := hseam
    logDeriv_bv := hlogBV }⟩
  dsimp [psi]
  fun_prop

private theorem extension_moves
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hx : x ∈ Set.Ioc (p : ℝ) (D.b : ℝ)) :
    x < D.germ.extension x := by
  let xI : I := ⟨x, ⟨p.property.1.trans hx.1.le,
    hx.2.trans D.b_lt_moveEnd.le |>.trans D.moveEnd.property.2⟩⟩
  have hxMove : xI ∈ Set.Ioc p D.moveEnd :=
    ⟨hx.1, hx.2.trans D.b_lt_moveEnd.le⟩
  have hxGerm : xI ∈ Set.Icc p D.germ.rightEnd :=
    ⟨hx.1.le, hx.2.trans D.b_lt_germEnd.le⟩
  have hmove := D.moves xI hxMove
  have hagree := D.germ.agrees hxGerm
  have hmoveReal : x < (f xI : ℝ) := by
    simpa [xI] using hmove
  have hagreeReal : (f xI : ℝ) = D.germ.extension x := by
    simpa [xI] using hagree
  change x < D.germ.extension x
  exact hmoveReal.trans_eq hagreeReal

private theorem extension_lt_b_of_lt_a
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) ≤ x) (hxa : x < (D.a : ℝ)) :
    D.germ.extension x < (D.b : ℝ) := by
  rw [← D.extension_a]
  apply D.extension_strictMonoOn
  · exact ⟨hpx, hxa.le.trans D.a_lt_b.le⟩
  · exact ⟨D.base_lt_a.le, D.a_lt_b.le⟩
  · exact hxa

/-- Every point strictly to the right of the fixed base reaches the selected
fundamental interval after finitely many forward germ iterates. -/
private theorem extension_iterate_reaches_a
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    ∃ n : ℕ, (D.a : ℝ) ≤ (D.germ.extension^[n]) x := by
  by_cases hax : (D.a : ℝ) ≤ x
  · exact ⟨0, by simpa⟩
  have hxa : x < (D.a : ℝ) := lt_of_not_ge hax
  by_contra hnot
  push_neg at hnot
  let u : ℕ → ℝ := fun n ↦ (D.germ.extension^[n]) x
  have hua : ∀ n, u n < (D.a : ℝ) := by
    intro n
    simpa [u] using hnot n
  have hpu : ∀ n, (p : ℝ) < u n := by
    intro n
    induction n with
    | zero => simpa [u] using hpx
    | succ n ih =>
        have hstep := D.extension_moves
          (show u n ∈ Set.Ioc (p : ℝ) (D.b : ℝ) from
            ⟨ih, ((hua n).trans D.a_lt_b).le⟩)
        change (p : ℝ) < D.germ.extension^[Nat.succ n] x
        rw [Function.iterate_succ_apply']
        exact ih.trans hstep
  have hstepEq : ∀ n, D.germ.extension (u n) = u (n + 1) := by
    intro n
    simp only [u, Function.iterate_succ_apply', Nat.succ_eq_add_one]
  have hstep : ∀ n, u n < u (n + 1) := by
    intro n
    rw [← hstepEq n]
    exact D.extension_moves
      ⟨hpu n, ((hua n).trans D.a_lt_b).le⟩
  have hmono : Monotone u :=
    monotone_nat_of_le_succ fun n ↦ (hstep n).le
  let l : ℝ := ⨆ n, u n
  have hbdd : BddAbove (Set.range u) := by
    refine ⟨(D.a : ℝ), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hua n).le
  have htend : Tendsto u atTop (nhds l) :=
    tendsto_atTop_ciSup hmono hbdd
  have htendShift : Tendsto (fun n ↦ u (n + 1)) atTop (nhds l) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have hpl : (p : ℝ) < l := hpx.trans_le (le_ciSup hbdd 0)
  have hla : l ≤ (D.a : ℝ) := ciSup_le fun n ↦ (hua n).le
  have hlGerm : l ∈ Set.Icc (p : ℝ) (D.germ.rightEnd : ℝ) :=
    ⟨hpl.le, hla.trans (D.a_lt_b.le.trans D.b_lt_germEnd.le)⟩
  have hcontAt : ContinuousAt D.germ.extension l :=
    (D.germ.contDiff_one.contDiffAt
      (D.germ.isOpen_neighborhood.mem_nhds
        (D.germ.segment_subset hlGerm))).continuousAt
  have htendF : Tendsto (fun n ↦ D.germ.extension (u n)) atTop
      (nhds (D.germ.extension l)) := hcontAt.tendsto.comp htend
  have hfixed : D.germ.extension l = l := by
    apply tendsto_nhds_unique htendF
    simpa only [hstepEq] using htendShift
  have hlaStrict : l < (D.a : ℝ) := by
    by_contra hnotla
    have hal : (D.a : ℝ) ≤ l := le_of_not_gt hnotla
    have heq : l = (D.a : ℝ) := le_antisymm hla hal
    have hFa : D.germ.extension l = (D.b : ℝ) := by
      rw [heq, D.extension_a]
    rw [hfixed] at hFa
    exact (show (D.a : ℝ) < (D.b : ℝ) from D.a_lt_b).ne
      (heq.symm.trans hFa)
  exact (ne_of_lt (D.extension_moves
    ⟨hpl, (hlaStrict.trans D.a_lt_b).le⟩)) hfixed.symm

/-- Least forward iterate entering the selected fundamental interval.  It is
used only on `(p,b)`; the total default keeps later ambient functions simple. -/
private noncomputable def arrivalIndex
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) (x : ℝ) : ℕ :=
  if hx : (p : ℝ) < x ∧ x < (D.b : ℝ) then
    Nat.find (D.extension_iterate_reaches_a hx.1 hx.2)
  else 0

private theorem arrivalIndex_spec
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    (D.a : ℝ) ≤
      (D.germ.extension^[D.arrivalIndex x]) x := by
  rw [arrivalIndex, dif_pos ⟨hpx, hxb⟩]
  exact Nat.find_spec (D.extension_iterate_reaches_a hpx hxb)

private theorem arrivalIndex_min
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    {m : ℕ} (hm : m < D.arrivalIndex x) :
    (D.germ.extension^[m]) x < (D.a : ℝ) := by
  rw [arrivalIndex, dif_pos ⟨hpx, hxb⟩] at hm
  exact lt_of_not_ge
    (Nat.find_min (D.extension_iterate_reaches_a hpx hxb) hm)

private theorem arrivalIndex_eq_iff
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    {n : ℕ} :
    D.arrivalIndex x = n ↔
      (D.a : ℝ) ≤ (D.germ.extension^[n]) x ∧
        ∀ m < n, (D.germ.extension^[m]) x < (D.a : ℝ) := by
  constructor
  · intro hn
    subst n
    exact ⟨D.arrivalIndex_spec hpx hxb,
      fun _ hm ↦ D.arrivalIndex_min hpx hxb hm⟩
  · rintro ⟨hn, hmin⟩
    apply le_antisymm
    · by_contra hnot
      have hlt : n < D.arrivalIndex x := lt_of_not_ge hnot
      exact (not_le_of_gt (D.arrivalIndex_min hpx hxb hlt)) hn
    · by_contra hnot
      have hlt : D.arrivalIndex x < n := lt_of_not_ge hnot
      exact (not_le_of_gt (hmin _ hlt)) (D.arrivalIndex_spec hpx hxb)

private theorem iterate_pos_before_arrival
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    ∀ m ≤ D.arrivalIndex x,
      (p : ℝ) < (D.germ.extension^[m]) x := by
  intro m hm
  induction m with
  | zero => simpa using hpx
  | succ m ih =>
      have hmLt : m < D.arrivalIndex x := by omega
      have hma := D.arrivalIndex_min hpx hxb hmLt
      have hpm := ih (by omega)
      rw [Function.iterate_succ_apply']
      exact hpm.trans (D.extension_moves
        ⟨hpm, (hma.trans D.a_lt_b).le⟩)

private theorem arrival_terminal_lt_b
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    (D.germ.extension^[D.arrivalIndex x]) x < (D.b : ℝ) := by
  by_cases hn : D.arrivalIndex x = 0
  · simpa [hn] using hxb
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [hm, Function.iterate_succ_apply']
  have hmLt : m < D.arrivalIndex x := by omega
  have hma := D.arrivalIndex_min hpx hxb hmLt
  have hpm := D.iterate_pos_before_arrival hpx hxb m (by omega) |>.le
  exact D.extension_lt_b_of_lt_a hpm hma

private theorem arrivalIndex_eq_zero_iff
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    D.arrivalIndex x = 0 ↔ (D.a : ℝ) ≤ x := by
  rw [D.arrivalIndex_eq_iff hpx hxb]
  simp

private theorem iterate_apply_next (F : ℝ → ℝ) (m : ℕ) (x : ℝ) :
    (F^[m]) (F x) = (F^[m + 1]) x := by
  simpa [Nat.succ_eq_add_one] using
    (Function.iterate_succ_apply F m x).symm

private theorem arrivalIndex_image_add_one
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxa : x < (D.a : ℝ)) :
    D.arrivalIndex x = D.arrivalIndex (D.germ.extension x) + 1 := by
  have hxb : x < (D.b : ℝ) := hxa.trans D.a_lt_b
  have hFxPos : (p : ℝ) < D.germ.extension x :=
    hpx.trans (D.extension_moves ⟨hpx, hxb.le⟩)
  have hFxB : D.germ.extension x < (D.b : ℝ) :=
    D.extension_lt_b_of_lt_a hpx.le hxa
  apply (D.arrivalIndex_eq_iff hpx hxb).2
  constructor
  · rw [← iterate_apply_next D.germ.extension]
    exact D.arrivalIndex_spec hFxPos hFxB
  · intro m hm
    by_cases hm0 : m = 0
    · simpa [hm0] using hxa
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    rw [Nat.succ_eq_add_one, ← iterate_apply_next D.germ.extension]
    apply D.arrivalIndex_min hFxPos hFxB
    omega

namespace AbelSeed

private theorem strictMonoOn
    {f : IntervalMap} {p : I} {D : AbelFundamentalData f p}
    (S : AbelSeed D) :
    StrictMonoOn S.psi (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact S.contDiff.continuous.continuousOn
  · intro x hx
    exact S.deriv_pos x (interior_subset hx)

private theorem value_nonneg
    {f : IntervalMap} {p : I} {D : AbelFundamentalData f p}
    (S : AbelSeed D) {x : ℝ}
    (hx : x ∈ Set.Icc (D.a : ℝ) (D.b : ℝ)) :
    0 ≤ S.psi x := by
  rw [← S.value_a]
  exact S.strictMonoOn.monotoneOn
    ⟨le_rfl, D.a_lt_b.le⟩ hx hx.1

private theorem value_lt_one
    {f : IntervalMap} {p : I} {D : AbelFundamentalData f p}
    (S : AbelSeed D) {x : ℝ}
    (hx : x ∈ Set.Ico (D.a : ℝ) (D.b : ℝ)) :
    S.psi x < 1 := by
  rw [← S.value_b]
  exact S.strictMonoOn
    ⟨hx.1, hx.2.le⟩ ⟨D.a_lt_b.le, le_rfl⟩ hx.2

end AbelSeed

/-- The dynamically glued Abel coordinate. -/
private noncomputable def gluedCoord
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) (x : ℝ) : ℝ :=
  S.psi ((D.germ.extension^[D.arrivalIndex x]) x) -
    (D.arrivalIndex x : ℝ)

private theorem gluedCoord_action
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxa : x < (D.a : ℝ)) :
    D.gluedCoord S (D.germ.extension x) = D.gluedCoord S x + 1 := by
  have hn := D.arrivalIndex_image_add_one hpx hxa
  dsimp [gluedCoord]
  rw [hn, iterate_apply_next D.germ.extension]
  push_cast
  ring

private theorem gluedCoord_bounds
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    -(D.arrivalIndex x : ℝ) ≤ D.gluedCoord S x ∧
      D.gluedCoord S x < 1 - (D.arrivalIndex x : ℝ) := by
  have hterm : (D.germ.extension^[D.arrivalIndex x]) x ∈
      Set.Ico (D.a : ℝ) (D.b : ℝ) :=
    ⟨D.arrivalIndex_spec hpx hxb, D.arrival_terminal_lt_b hpx hxb⟩
  constructor
  · dsimp [gluedCoord]
    linarith [S.value_nonneg ⟨hterm.1, hterm.2.le⟩]
  · dsimp [gluedCoord]
    linarith [S.value_lt_one hterm]

private theorem iterate_strictMono_before_arrivals
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x y : ℝ}
    (hpx : (p : ℝ) < x) (hxy : x < y) (hyb : y < (D.b : ℝ)) :
    ∀ m, m ≤ D.arrivalIndex x → m ≤ D.arrivalIndex y →
      (D.germ.extension^[m]) x < (D.germ.extension^[m]) y := by
  intro m hmx hmy
  induction m with
  | zero => simpa using hxy
  | succ m ih =>
      have hmxLt : m < D.arrivalIndex x := by omega
      have hmyLt : m < D.arrivalIndex y := by omega
      have hxp := D.iterate_pos_before_arrival hpx (hxy.trans hyb)
        m (by omega)
      have hyp := D.iterate_pos_before_arrival (hpx.trans hxy) hyb
        m (by omega)
      have hxa := D.arrivalIndex_min hpx (hxy.trans hyb) hmxLt
      have hya := D.arrivalIndex_min (hpx.trans hxy) hyb hmyLt
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact D.extension_strictMonoOn
        ⟨hxp.le, hxa.le.trans D.a_lt_b.le⟩
        ⟨hyp.le, hya.le.trans D.a_lt_b.le⟩
        (ih (by omega) (by omega))

private theorem arrivalIndex_antitoneOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p) :
    AntitoneOn D.arrivalIndex
      (Set.Ioo (p : ℝ) (D.b : ℝ)) := by
  intro x hx y hy hxy
  by_contra hnot
  have hlt : D.arrivalIndex x < D.arrivalIndex y := lt_of_not_ge hnot
  have hiter := D.iterate_strictMono_before_arrivals hx.1
    (lt_of_le_of_ne hxy fun heq ↦ by
      subst y
      exact (not_lt_of_ge le_rfl) hlt)
    hy.2 (D.arrivalIndex x) le_rfl hlt.le
  exact (not_lt_of_ge (D.arrivalIndex_spec hx.1 hx.2))
    (hiter.trans (D.arrivalIndex_min hy.1 hy.2 hlt))

private theorem gluedCoord_strictMonoOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    StrictMonoOn (D.gluedCoord S)
      (Set.Ioo (p : ℝ) (D.b : ℝ)) := by
  intro x hx y hy hxy
  have hnyx : D.arrivalIndex y ≤ D.arrivalIndex x :=
    D.arrivalIndex_antitoneOn hx hy hxy.le
  rcases hnyx.eq_or_lt with hnEq | hnLt
  · have hn : D.arrivalIndex x = D.arrivalIndex y := hnEq.symm
    have hiter := D.iterate_strictMono_before_arrivals hx.1 hxy hy.2
      (D.arrivalIndex x) le_rfl (by simpa [hn])
    have hxTerm : (D.germ.extension^[D.arrivalIndex x]) x ∈
        Set.Icc (D.a : ℝ) (D.b : ℝ) :=
      ⟨D.arrivalIndex_spec hx.1 hx.2,
        (D.arrival_terminal_lt_b hx.1 hx.2).le⟩
    have hyTerm : (D.germ.extension^[D.arrivalIndex x]) y ∈
        Set.Icc (D.a : ℝ) (D.b : ℝ) := by
      rw [hn]
      exact ⟨D.arrivalIndex_spec hy.1 hy.2,
        (D.arrival_terminal_lt_b hy.1 hy.2).le⟩
    have hpsi := S.strictMonoOn hxTerm hyTerm hiter
    dsimp [gluedCoord]
    simpa [hn] using (sub_lt_sub_right hpsi (D.arrivalIndex x : ℝ))
  · have hxB := D.gluedCoord_bounds S hx.1 hx.2
    have hyB := D.gluedCoord_bounds S hy.1 hy.2
    have hcast : (D.arrivalIndex y : ℝ) + 1 ≤
        (D.arrivalIndex x : ℝ) := by exact_mod_cast hnLt
    linarith

/-- The smooth formula used on the `n`-th fundamental interval. -/
private noncomputable def localPiece
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) (n : ℕ) (x : ℝ) : ℝ :=
  S.psi ((D.germ.extension^[n]) x) - (n : ℝ)

private theorem gluedCoord_eq_localPiece
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) (x : ℝ) :
    D.gluedCoord S x = D.localPiece S (D.arrivalIndex x) x := rfl

private theorem iterate_mem_le_arrival
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    {m : ℕ} (hm : m ≤ D.arrivalIndex x) :
    (D.germ.extension^[m]) x ∈
      Set.Ioo (p : ℝ) (D.b : ℝ) := by
  refine ⟨D.iterate_pos_before_arrival hpx hxb m hm, ?_⟩
  rcases hm.eq_or_lt with rfl | hlt
  · exact D.arrival_terminal_lt_b hpx hxb
  · exact (D.arrivalIndex_min hpx hxb hlt).trans D.a_lt_b

private theorem iterate_contDiffAt_through_arrival
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    ∀ m ≤ D.arrivalIndex x + 1,
      ContDiffAt ℝ 1 (D.germ.extension^[m]) x := by
  intro m hm
  induction m with
  | zero => simpa using (contDiffAt_id : ContDiffAt ℝ 1 id x)
  | succ m ih =>
      have hmPrev : m ≤ D.arrivalIndex x := by omega
      have hmem := D.iterate_mem_le_arrival hpx hxb hmPrev
      have hmemG : (D.germ.extension^[m]) x ∈
          Set.Icc (p : ℝ) (D.germ.rightEnd : ℝ) :=
        ⟨hmem.1.le, hmem.2.le.trans D.b_lt_germEnd.le⟩
      have houter : ContDiffAt ℝ 1 D.germ.extension
          ((D.germ.extension^[m]) x) :=
        D.germ.contDiff_one.contDiffAt
          (D.germ.isOpen_neighborhood.mem_nhds
            (D.germ.segment_subset hmemG))
      rw [Function.iterate_succ']
      exact houter.comp x (ih (by omega))

private theorem iterate_hasDerivAt_pos_through_arrival
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ)) :
    ∀ m ≤ D.arrivalIndex x + 1,
      ∃ d : ℝ, 0 < d ∧ HasDerivAt (D.germ.extension^[m]) d x := by
  intro m hm
  induction m with
  | zero => exact ⟨1, zero_lt_one, by simpa using hasDerivAt_id x⟩
  | succ m ih =>
      have hmPrev : m ≤ D.arrivalIndex x := by omega
      have hmem := D.iterate_mem_le_arrival hpx hxb hmPrev
      have hmemG : (D.germ.extension^[m]) x ∈
          Set.Icc (p : ℝ) (D.germ.rightEnd : ℝ) :=
        ⟨hmem.1.le, hmem.2.le.trans D.b_lt_germEnd.le⟩
      have houterC1 : ContDiffAt ℝ 1 D.germ.extension
          ((D.germ.extension^[m]) x) :=
        D.germ.contDiff_one.contDiffAt
          (D.germ.isOpen_neighborhood.mem_nhds
            (D.germ.segment_subset hmemG))
      have houter : HasDerivAt D.germ.extension
          (deriv D.germ.extension ((D.germ.extension^[m]) x))
          ((D.germ.extension^[m]) x) :=
        houterC1.differentiableAt_one.hasDerivAt
      obtain ⟨d, hd, hderiv⟩ := ih (by omega)
      refine ⟨deriv D.germ.extension ((D.germ.extension^[m]) x) * d,
        mul_pos (D.germ.deriv_pos _ hmemG) hd, ?_⟩
      rw [Function.iterate_succ']
      exact houter.comp x hderiv

private theorem localPiece_contDiffAt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    {n : ℕ} (hn : n ≤ D.arrivalIndex x + 1) :
    ContDiffAt ℝ 1 (D.localPiece S n) x := by
  change ContDiffAt ℝ 1
    (fun y ↦ S.psi ((D.germ.extension^[n]) y) - (n : ℝ)) x
  exact ((S.contDiff.contDiffAt.comp x
    (D.iterate_contDiffAt_through_arrival hpx hxb n hn)).sub
      contDiffAt_const)

private theorem localPiece_hasDerivAt_pos_of_terminal
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ} {n : ℕ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hn : n ≤ D.arrivalIndex x + 1)
    (hterm : (D.germ.extension^[n]) x ∈
      Set.Icc (D.a : ℝ) (D.b : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (D.localPiece S n) d x := by
  obtain ⟨e, he, hiter⟩ :=
    D.iterate_hasDerivAt_pos_through_arrival hpx hxb n hn
  have hseed : HasDerivAt S.psi
      (deriv S.psi ((D.germ.extension^[n]) x))
      ((D.germ.extension^[n]) x) :=
    (S.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  refine ⟨deriv S.psi ((D.germ.extension^[n]) x) * e,
    mul_pos (S.deriv_pos _ hterm) he, ?_⟩
  change HasDerivAt
    (fun y ↦ S.psi ((D.germ.extension^[n]) y) - (n : ℝ))
    (deriv S.psi ((D.germ.extension^[n]) x) * e) x
  exact (hseed.comp x hiter).sub_const (n : ℝ)

private theorem eventually_arrivalIndex_eq_of_terminal_gt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.a : ℝ) <
      (D.germ.extension^[D.arrivalIndex x]) x) :
    ∀ᶠ z in nhds x, D.arrivalIndex z = D.arrivalIndex x := by
  let n := D.arrivalIndex x
  have hdom : ∀ᶠ z in nhds x,
      (p : ℝ) < z ∧ z < (D.b : ℝ) :=
    Ioo_mem_nhds hpx hxb
  have hterminal : ∀ᶠ z in nhds x,
      (D.a : ℝ) < (D.germ.extension^[n]) z := by
    apply (D.iterate_contDiffAt_through_arrival hpx hxb n (by
      dsimp [n]
      omega)).continuousAt
    exact Ioi_mem_nhds hterm
  have hpre : ∀ᶠ z in nhds x, ∀ m ∈ Finset.range n,
      (D.germ.extension^[m]) z < (D.a : ℝ) :=
    (Filter.eventually_all_finset (Finset.range n)).2 fun m hm ↦ by
      have hmLt : m < D.arrivalIndex x := by
        simpa [n] using Finset.mem_range.mp hm
      exact (D.iterate_contDiffAt_through_arrival hpx hxb m (by omega)).continuousAt
        |>.eventually_lt_const (D.arrivalIndex_min hpx hxb hmLt)
  filter_upwards [hdom, hterminal, hpre] with z hz hzterm hzpre
  apply (D.arrivalIndex_eq_iff hz.1 hz.2).2
  refine ⟨hzterm.le, ?_⟩
  intro m hm
  exact hzpre m (Finset.mem_range.mpr (by simpa [n] using hm))

private theorem eventually_arrivalIndex_cases_of_terminal_eq
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.germ.extension^[D.arrivalIndex x]) x = (D.a : ℝ)) :
    ∀ᶠ z in nhds x,
      D.arrivalIndex z = D.arrivalIndex x ∨
        D.arrivalIndex z = D.arrivalIndex x + 1 := by
  let n := D.arrivalIndex x
  have hdom : ∀ᶠ z in nhds x,
      (p : ℝ) < z ∧ z < (D.b : ℝ) :=
    Ioo_mem_nhds hpx hxb
  have hnextAt : (D.germ.extension^[n + 1]) x = (D.b : ℝ) := by
    rw [show n + 1 = Nat.succ n by omega,
      Function.iterate_succ_apply', show n = D.arrivalIndex x from rfl,
      hterm, D.extension_a]
  have hnext : ∀ᶠ z in nhds x,
      (D.a : ℝ) < (D.germ.extension^[n + 1]) z := by
    apply (D.iterate_contDiffAt_through_arrival hpx hxb (n + 1) (by
      dsimp [n]
      omega)).continuousAt
    rw [hnextAt]
    exact Ioi_mem_nhds D.a_lt_b
  have hpre : ∀ᶠ z in nhds x, ∀ m ∈ Finset.range n,
      (D.germ.extension^[m]) z < (D.a : ℝ) :=
    (Filter.eventually_all_finset (Finset.range n)).2 fun m hm ↦ by
      have hmLt : m < D.arrivalIndex x := by
        simpa [n] using Finset.mem_range.mp hm
      exact (D.iterate_contDiffAt_through_arrival hpx hxb m (by omega)).continuousAt
        |>.eventually_lt_const (D.arrivalIndex_min hpx hxb hmLt)
  filter_upwards [hdom, hnext, hpre] with z hz hznext hzpre
  by_cases hzterm : (D.a : ℝ) ≤ (D.germ.extension^[n]) z
  · left
    apply (D.arrivalIndex_eq_iff hz.1 hz.2).2
    refine ⟨hzterm, ?_⟩
    intro m hm
    exact hzpre m (Finset.mem_range.mpr hm)
  · right
    apply (D.arrivalIndex_eq_iff hz.1 hz.2).2
    refine ⟨hznext.le, ?_⟩
    intro m hm
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hmn | rfl
    · exact hzpre m (Finset.mem_range.mpr hmn)
    · exact lt_of_not_ge hzterm

private theorem localPiece_succ_eq_at_seam
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ} {n : ℕ}
    (hterm : (D.germ.extension^[n]) x = (D.a : ℝ)) :
    D.localPiece S (n + 1) x = D.localPiece S n x := by
  have hnext : (D.germ.extension^[n + 1]) x = (D.b : ℝ) := by
    rw [show n + 1 = Nat.succ n by omega,
      Function.iterate_succ_apply', hterm, D.extension_a]
  have hnext' : (D.germ.extension^[n]) (D.germ.extension x) =
      (D.b : ℝ) := by
    rw [iterate_apply_next D.germ.extension]
    exact hnext
  dsimp [localPiece]
  rw [hterm, hnext', S.value_a, S.value_b]
  push_cast
  ring

private theorem eventually_gluedCoord_eq_localPiece_of_terminal_gt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.a : ℝ) <
      (D.germ.extension^[D.arrivalIndex x]) x) :
    D.gluedCoord S =ᶠ[nhds x]
      D.localPiece S (D.arrivalIndex x) :=
  (D.eventually_arrivalIndex_eq_of_terminal_gt hpx hxb hterm).mono
    fun z hz ↦ by simp only [gluedCoord_eq_localPiece, hz]

private theorem gluedCoord_hasDerivAt_pos_of_terminal_gt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.a : ℝ) <
      (D.germ.extension^[D.arrivalIndex x]) x) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (D.gluedCoord S) d x := by
  have htermMem : (D.germ.extension^[D.arrivalIndex x]) x ∈
      Set.Icc (D.a : ℝ) (D.b : ℝ) :=
    ⟨hterm.le, (D.arrival_terminal_lt_b hpx hxb).le⟩
  obtain ⟨d, hd, hlocal⟩ := D.localPiece_hasDerivAt_pos_of_terminal
    S hpx hxb (by omega) htermMem
  refine ⟨d, hd, ?_⟩
  exact hlocal.congr_of_eventuallyEq
    (D.eventually_gluedCoord_eq_localPiece_of_terminal_gt S hpx hxb hterm)

private theorem eventually_gluedCoord_eq_localPiece_right_of_seam
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.germ.extension^[D.arrivalIndex x]) x = (D.a : ℝ)) :
    D.gluedCoord S =ᶠ[nhdsWithin x (Set.Ici x)]
      D.localPiece S (D.arrivalIndex x) := by
  have hcases : ∀ᶠ z in nhdsWithin x (Set.Ici x),
      D.arrivalIndex z = D.arrivalIndex x ∨
        D.arrivalIndex z = D.arrivalIndex x + 1 :=
    (D.eventually_arrivalIndex_cases_of_terminal_eq hpx hxb hterm).filter_mono
      nhdsWithin_le_nhds
  have hdom : ∀ᶠ z in nhdsWithin x (Set.Ici x),
      z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ z in nhds x, z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) from
        Ioo_mem_nhds hpx hxb)
  filter_upwards [hcases, hdom, self_mem_nhdsWithin] with z hz hzdom hxz
  have hle : D.arrivalIndex z ≤ D.arrivalIndex x :=
    D.arrivalIndex_antitoneOn ⟨hpx, hxb⟩ hzdom hxz
  have heq : D.arrivalIndex z = D.arrivalIndex x := by
    rcases hz with hz | hz
    · exact hz
    · omega
  simp only [gluedCoord_eq_localPiece, heq]

private theorem eventually_gluedCoord_eq_localPiece_left_of_seam
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.germ.extension^[D.arrivalIndex x]) x = (D.a : ℝ)) :
    D.gluedCoord S =ᶠ[nhdsWithin x (Set.Iic x)]
      D.localPiece S (D.arrivalIndex x + 1) := by
  have hcases : ∀ᶠ z in nhdsWithin x (Set.Iic x),
      D.arrivalIndex z = D.arrivalIndex x ∨
        D.arrivalIndex z = D.arrivalIndex x + 1 :=
    (D.eventually_arrivalIndex_cases_of_terminal_eq hpx hxb hterm).filter_mono
      nhdsWithin_le_nhds
  have hdom : ∀ᶠ z in nhdsWithin x (Set.Iic x),
      z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ z in nhds x, z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) from
        Ioo_mem_nhds hpx hxb)
  filter_upwards [hcases, hdom, self_mem_nhdsWithin] with z hz hzdom hzx
  rcases hz with hz | hz
  · have hzxEq : z = x := by
      have hzx' : z ≤ x := hzx
      rcases hzx'.eq_or_lt with heq | hlt
      · exact heq
      · have hiter := D.iterate_strictMono_before_arrivals hzdom.1 hlt hxb
            (D.arrivalIndex x) (by simpa [hz]) le_rfl
        have hzSpec := D.arrivalIndex_spec hzdom.1 hzdom.2
        rw [hz] at hzSpec
        exact False.elim ((not_lt_of_ge hzSpec) (hiter.trans_eq hterm))
    subst z
    change D.gluedCoord S x = D.localPiece S (D.arrivalIndex x + 1) x
    rw [D.gluedCoord_eq_localPiece]
    exact (D.localPiece_succ_eq_at_seam S hterm).symm
  · simp only [gluedCoord_eq_localPiece, hz]

private theorem gluedCoord_hasDerivAt_pos_of_terminal_eq
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.germ.extension^[D.arrivalIndex x]) x = (D.a : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (D.gluedCoord S) d x := by
  let n := D.arrivalIndex x
  obtain ⟨e, he, hiter⟩ :=
    D.iterate_hasDerivAt_pos_through_arrival hpx hxb n (by
      dsimp [n]
      omega)
  have haMem : (D.a : ℝ) ∈ Set.Icc (D.a : ℝ) (D.b : ℝ) :=
    ⟨le_rfl, D.a_lt_b.le⟩
  have hbMem : (D.b : ℝ) ∈ Set.Icc (D.a : ℝ) (D.b : ℝ) :=
    ⟨D.a_lt_b.le, le_rfl⟩
  let d : ℝ := deriv S.psi (D.a : ℝ) * e
  have hd : 0 < d := mul_pos (S.deriv_pos _ haMem) he
  have hseedA : HasDerivAt S.psi (deriv S.psi (D.a : ℝ)) (D.a : ℝ) :=
    (S.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hseedTerm : HasDerivAt S.psi (deriv S.psi (D.a : ℝ))
      ((D.germ.extension^[n]) x) := by
    rw [show n = D.arrivalIndex x from rfl, hterm]
    exact hseedA
  have hrightRaw : HasDerivAt
      (fun y ↦ S.psi ((D.germ.extension^[n]) y) - (n : ℝ)) d x := by
    dsimp [d]
    exact (hseedTerm.comp x hiter).sub_const (n : ℝ)
  have hright : HasDerivAt (D.localPiece S n) d x := by
    exact hrightRaw
  have hFAt : HasDerivAt D.germ.extension
      (deriv D.germ.extension (D.a : ℝ)) (D.a : ℝ) :=
    (D.germ.contDiff_one.contDiffAt
      (D.germ.isOpen_neighborhood.mem_nhds
        (D.germ.segment_subset
          ⟨D.base_lt_a.le,
            D.a_lt_b.le.trans D.b_lt_germEnd.le⟩))).differentiableAt_one.hasDerivAt
  have hFAtTerm : HasDerivAt D.germ.extension
      (deriv D.germ.extension (D.a : ℝ))
      ((D.germ.extension^[n]) x) := by
    rw [show n = D.arrivalIndex x from rfl, hterm]
    exact hFAt
  have hiterNextRaw := hFAtTerm.comp x hiter
  have hiterNext : HasDerivAt (D.germ.extension^[n + 1])
      (deriv D.germ.extension (D.a : ℝ) * e) x := by
    rw [show n + 1 = Nat.succ n by omega, Function.iterate_succ']
    exact hiterNextRaw
  have hnext : (D.germ.extension^[n + 1]) x = (D.b : ℝ) := by
    rw [show n + 1 = Nat.succ n by omega,
      Function.iterate_succ_apply', show n = D.arrivalIndex x from rfl,
      hterm, D.extension_a]
  have hseedB : HasDerivAt S.psi (deriv S.psi (D.b : ℝ)) (D.b : ℝ) :=
    (S.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hseedNext : HasDerivAt S.psi (deriv S.psi (D.b : ℝ))
      ((D.germ.extension^[n + 1]) x) := by
    rw [hnext]
    exact hseedB
  have hleftRaw := (hseedNext.comp x hiterNext).sub_const ((n + 1 : ℕ) : ℝ)
  have hcoef : deriv S.psi (D.b : ℝ) *
        (deriv D.germ.extension (D.a : ℝ) * e) = d := by
    dsimp [d]
    rw [← mul_assoc, S.deriv_seam]
  have hleft : HasDerivAt (D.localPiece S (n + 1)) d x := by
    change HasDerivAt
      (fun y ↦ S.psi ((D.germ.extension^[n + 1]) y) - (n + 1 : ℕ)) d x
    exact hleftRaw.congr_deriv hcoef
  have hrightWithin : HasDerivWithinAt (D.gluedCoord S) d (Set.Ici x) x :=
    hright.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
      (D.eventually_gluedCoord_eq_localPiece_right_of_seam S hpx hxb hterm)
      (Set.mem_Ici.mpr le_rfl)
  have hleftWithin : HasDerivWithinAt (D.gluedCoord S) d (Set.Iic x) x :=
    hleft.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
      (D.eventually_gluedCoord_eq_localPiece_left_of_seam S hpx hxb hterm)
      (Set.mem_Iic.mpr le_rfl)
  have hfull := hleftWithin.union hrightWithin
  rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at hfull
  exact ⟨d, hd, hfull⟩

private theorem gluedCoord_hasDerivAt_pos
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hx : x ∈ Set.Ioo (p : ℝ) (D.b : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (D.gluedCoord S) d x := by
  rcases lt_or_eq_of_le (D.arrivalIndex_spec hx.1 hx.2) with hterm | hterm
  · exact D.gluedCoord_hasDerivAt_pos_of_terminal_gt S hx.1 hx.2 hterm
  · exact D.gluedCoord_hasDerivAt_pos_of_terminal_eq S hx.1 hx.2 hterm.symm

private theorem gluedCoord_deriv_pos
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hx : x ∈ Set.Ioo (p : ℝ) (D.b : ℝ)) :
    0 < deriv (D.gluedCoord S) x := by
  obtain ⟨d, hd, hderiv⟩ := D.gluedCoord_hasDerivAt_pos S hx
  simpa [hderiv.deriv] using hd

private theorem gluedCoord_contDiffAt_of_terminal_gt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.a : ℝ) <
      (D.germ.extension^[D.arrivalIndex x]) x) :
    ContDiffAt ℝ 1 (D.gluedCoord S) x := by
  exact (D.localPiece_contDiffAt S hpx hxb (by omega)).congr_of_eventuallyEq
    (D.eventually_gluedCoord_eq_localPiece_of_terminal_gt S hpx hxb hterm)

private theorem eventually_arrivalIndex_eq_right_of_seam
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    {x : ℝ} (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.germ.extension^[D.arrivalIndex x]) x = (D.a : ℝ)) :
    ∀ᶠ z in nhdsWithin x (Set.Ici x),
      D.arrivalIndex z = D.arrivalIndex x := by
  have hcases : ∀ᶠ z in nhdsWithin x (Set.Ici x),
      D.arrivalIndex z = D.arrivalIndex x ∨
        D.arrivalIndex z = D.arrivalIndex x + 1 :=
    (D.eventually_arrivalIndex_cases_of_terminal_eq hpx hxb hterm).filter_mono
      nhdsWithin_le_nhds
  have hdom : ∀ᶠ z in nhdsWithin x (Set.Ici x),
      z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ z in nhds x, z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) from
        Ioo_mem_nhds hpx hxb)
  filter_upwards [hcases, hdom, self_mem_nhdsWithin] with z hz hzdom hxz
  have hle := D.arrivalIndex_antitoneOn ⟨hpx, hxb⟩ hzdom hxz
  rcases hz with hz | hz
  · exact hz
  · omega

private theorem gluedCoord_deriv_continuousAt_of_terminal_eq
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x < (D.b : ℝ))
    (hterm : (D.germ.extension^[D.arrivalIndex x]) x = (D.a : ℝ)) :
    ContinuousAt (deriv (D.gluedCoord S)) x := by
  let n := D.arrivalIndex x
  have hfunRight :=
    D.eventually_gluedCoord_eq_localPiece_right_of_seam S hpx hxb hterm
  have hfunLeft :=
    D.eventually_gluedCoord_eq_localPiece_left_of_seam S hpx hxb hterm
  have harrRight := D.eventually_arrivalIndex_eq_right_of_seam hpx hxb hterm
  have harrCases : ∀ᶠ z in nhdsWithin x (Set.Iic x),
      D.arrivalIndex z = n ∨ D.arrivalIndex z = n + 1 := by
    exact (D.eventually_arrivalIndex_cases_of_terminal_eq hpx hxb hterm).filter_mono
      nhdsWithin_le_nhds
  have hdomRight : ∀ᶠ z in nhdsWithin x (Set.Ici x),
      z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ z in nhds x, z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) from
        Ioo_mem_nhds hpx hxb)
  have hdomLeft : ∀ᶠ z in nhdsWithin x (Set.Iic x),
      z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (show ∀ᶠ z in nhds x, z ∈ Set.Ioo (p : ℝ) (D.b : ℝ) from
        Ioo_mem_nhds hpx hxb)
  have hwithinRight := hfunRight.derivWithin
  have hderivRight : deriv (D.gluedCoord S) =ᶠ[nhdsWithin x (Set.Ici x)]
      deriv (D.localPiece S n) := by
    filter_upwards [hwithinRight, hdomRight, harrRight,
      self_mem_nhdsWithin] with z hz hzdom hzarr hzx
    have hgd : DifferentiableAt ℝ (D.gluedCoord S) z :=
      (D.gluedCoord_hasDerivAt_pos S hzdom).choose_spec.2.differentiableAt
    have hld : DifferentiableAt ℝ (D.localPiece S n) z :=
      (D.localPiece_contDiffAt S hzdom.1 hzdom.2 (by
        dsimp [n]
        omega)).differentiableAt_one
    have hu := (uniqueDiffOn_Ici x).uniqueDiffWithinAt hzx
    rw [hgd.derivWithin hu, hld.derivWithin hu] at hz
    exact hz
  have hwithinLeft := hfunLeft.derivWithin
  have hderivLeft : deriv (D.gluedCoord S) =ᶠ[nhdsWithin x (Set.Iic x)]
      deriv (D.localPiece S (n + 1)) := by
    filter_upwards [hwithinLeft, hdomLeft, harrCases,
      self_mem_nhdsWithin] with z hz hzdom hzarr hzx
    have hgd : DifferentiableAt ℝ (D.gluedCoord S) z :=
      (D.gluedCoord_hasDerivAt_pos S hzdom).choose_spec.2.differentiableAt
    have hbound : n + 1 ≤ D.arrivalIndex z + 1 := by
      rcases hzarr with hzarr | hzarr <;> omega
    have hld : DifferentiableAt ℝ (D.localPiece S (n + 1)) z :=
      (D.localPiece_contDiffAt S hzdom.1 hzdom.2 hbound).differentiableAt_one
    have hu := (uniqueDiffOn_Iic x).uniqueDiffWithinAt hzx
    rw [hgd.derivWithin hu, hld.derivWithin hu] at hz
    exact hz
  have hlocalRightC1 : ContDiffAt ℝ 1 (D.localPiece S n) x :=
    D.localPiece_contDiffAt S hpx hxb (by
      dsimp [n]
      omega)
  have hlocalLeftC1 : ContDiffAt ℝ 1 (D.localPiece S (n + 1)) x :=
    D.localPiece_contDiffAt S hpx hxb (by
      dsimp [n]
      omega)
  have hcontRightLocal : ContinuousAt (deriv (D.localPiece S n)) x :=
    (hlocalRightC1.derivWithin (m := 0) (by norm_num)).continuousAt
  have hcontLeftLocal : ContinuousAt (deriv (D.localPiece S (n + 1))) x :=
    (hlocalLeftC1.derivWithin (m := 0) (by norm_num)).continuousAt
  have hcontRight : ContinuousWithinAt (deriv (D.gluedCoord S)) (Set.Ici x) x :=
    hcontRightLocal.continuousWithinAt.congr_of_eventuallyEq_of_mem
      hderivRight (Set.mem_Ici.mpr le_rfl)
  have hcontLeft : ContinuousWithinAt (deriv (D.gluedCoord S)) (Set.Iic x) x :=
    hcontLeftLocal.continuousWithinAt.congr_of_eventuallyEq_of_mem
      hderivLeft (Set.mem_Iic.mpr le_rfl)
  have hfull := hcontLeft.union hcontRight
  rw [Set.Iic_union_Ici, continuousWithinAt_univ] at hfull
  exact hfull

private theorem gluedCoord_deriv_continuousOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    ContinuousOn (deriv (D.gluedCoord S))
      (Set.Ioo (p : ℝ) (D.b : ℝ)) := by
  intro x hx
  rcases lt_or_eq_of_le (D.arrivalIndex_spec hx.1 hx.2) with hterm | hterm
  · have hC1 := D.gluedCoord_contDiffAt_of_terminal_gt S hx.1 hx.2 hterm
    exact ((hC1.derivWithin (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  · exact (D.gluedCoord_deriv_continuousAt_of_terminal_eq
      S hx.1 hx.2 hterm.symm).continuousWithinAt

private theorem gluedCoord_contDiffOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    ContDiffOn ℝ 1 (D.gluedCoord S)
      (Set.Ioo (p : ℝ) (D.b : ℝ)) := by
  apply (contDiffOn_one_iff_derivWithin
    (uniqueDiffOn_Ioo (p : ℝ) (D.b : ℝ))).2
  constructor
  · intro x hx
    exact (D.gluedCoord_hasDerivAt_pos S hx).choose_spec.2.differentiableAt
      |>.differentiableWithinAt
  · exact (D.gluedCoord_deriv_continuousOn S).congr fun x hx ↦ by
      rw [derivWithin_of_isOpen isOpen_Ioo hx]

private theorem gluedCoord_eventuallyEq_seed_of_a_lt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ} (hax : (D.a : ℝ) < x) :
    D.gluedCoord S =ᶠ[nhds x] S.psi := by
  filter_upwards [Ioi_mem_nhds hax] with z haz
  have hn : D.arrivalIndex z = 0 := by
    by_cases hz : (p : ℝ) < z ∧ z < (D.b : ℝ)
    · exact (D.arrivalIndex_eq_zero_iff hz.1 hz.2).2 haz.le
    · simp [arrivalIndex, hz]
  dsimp [gluedCoord]
  simp [hn]

private theorem gluedCoord_deriv_eq_seed_on_Icc
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    Set.EqOn (deriv (D.gluedCoord S)) (deriv S.psi)
      (Set.Icc (D.a : ℝ) (D.b : ℝ)) := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hax
  · have hpx : (p : ℝ) < (D.a : ℝ) := D.base_lt_a
    have hxb : (D.a : ℝ) < (D.b : ℝ) := D.a_lt_b
    have hn : D.arrivalIndex (D.a : ℝ) = 0 :=
      (D.arrivalIndex_eq_zero_iff hpx hxb).2 le_rfl
    have hterm : (D.germ.extension^[D.arrivalIndex (D.a : ℝ)])
        (D.a : ℝ) = (D.a : ℝ) := by simp [hn]
    have hEq := D.eventually_gluedCoord_eq_localPiece_right_of_seam
      S hpx hxb hterm
    have hseed : HasDerivWithinAt S.psi (deriv S.psi (D.a : ℝ))
        (Set.Ici (D.a : ℝ)) (D.a : ℝ) :=
      ((S.contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt).hasDerivWithinAt
    have hlocal : D.localPiece S 0 = S.psi := by
      funext y
      simp [localPiece]
    rw [hn, hlocal] at hEq
    have hglued := hseed.congr_of_eventuallyEq_of_mem hEq
      (Set.mem_Ici.mpr le_rfl)
    have hdiff : DifferentiableAt ℝ (D.gluedCoord S) (D.a : ℝ) :=
      (D.gluedCoord_hasDerivAt_pos S ⟨D.base_lt_a, D.a_lt_b⟩).choose_spec.2.differentiableAt
    have hu := uniqueDiffWithinAt_Ici (D.a : ℝ)
    have heq := hglued.derivWithin hu
    simpa [hdiff.derivWithin hu] using heq
  · exact (D.gluedCoord_eventuallyEq_seed_of_a_lt S hax).deriv_eq

private theorem gluedCoord_logDeriv_bv_seedInterval
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {u v : ℝ}
    (hau : (D.a : ℝ) ≤ u) (huv : u ≤ v)
    (hvb : v ≤ (D.b : ℝ)) :
    BoundedVariationOn
      (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
      (Set.Icc u v) := by
  have hsub : Set.Icc u v ⊆ Set.Icc (D.a : ℝ) (D.b : ℝ) :=
    Set.Icc_subset_Icc hau hvb
  have hEq : Set.EqOn
      (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
      (fun x ↦ Real.log (deriv S.psi x)) (Set.Icc u v) :=
    fun x hx ↦ congrArg Real.log (D.gluedCoord_deriv_eq_seed_on_Icc S (hsub hx))
  rw [BoundedVariationOn, eVariationOn.eq_of_eqOn hEq]
  exact S.logDeriv_bv.mono hsub

private theorem gluedCoord_deriv_pos_to_b
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxb : x ≤ (D.b : ℝ)) :
    0 < deriv (D.gluedCoord S) x := by
  rcases hxb.eq_or_lt with rfl | hlt
  · rw [D.gluedCoord_deriv_eq_seed_on_Icc S
      ⟨D.a_lt_b.le, le_rfl⟩]
    exact S.deriv_pos _ ⟨D.a_lt_b.le, le_rfl⟩
  · exact D.gluedCoord_deriv_pos S ⟨hpx, hlt⟩

private theorem gluedCoord_deriv_cocycle
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxa : x ≤ (D.a : ℝ)) :
    deriv (D.gluedCoord S) x =
      deriv (D.gluedCoord S) (D.germ.extension x) *
        deriv D.germ.extension x := by
  rcases hxa.eq_or_lt with rfl | hlt
  · have hcoordA := D.gluedCoord_deriv_eq_seed_on_Icc S
      ⟨le_rfl, D.a_lt_b.le⟩
    have hcoordB := D.gluedCoord_deriv_eq_seed_on_Icc S
      ⟨D.a_lt_b.le, le_rfl⟩
    rw [D.extension_a, hcoordA, hcoordB]
    exact S.deriv_seam.symm
  · have hxb : x < (D.b : ℝ) := hlt.trans D.a_lt_b
    have hFxP : (p : ℝ) < D.germ.extension x :=
      hpx.trans (D.extension_moves ⟨hpx, hxb.le⟩)
    have hFxB : D.germ.extension x < (D.b : ℝ) :=
      D.extension_lt_b_of_lt_a hpx.le hlt
    have hEq : (fun z ↦ D.gluedCoord S (D.germ.extension z)) =ᶠ[nhds x]
        (fun z ↦ D.gluedCoord S z + 1) := by
      filter_upwards [Ioo_mem_nhds hpx hlt] with z hz
      exact D.gluedCoord_action S hz.1 hz.2
    have hcoordX : DifferentiableAt ℝ (D.gluedCoord S) x :=
      (D.gluedCoord_hasDerivAt_pos S ⟨hpx, hxb⟩).choose_spec.2.differentiableAt
    have hcoordFx : DifferentiableAt ℝ (D.gluedCoord S)
        (D.germ.extension x) :=
      (D.gluedCoord_hasDerivAt_pos S ⟨hFxP, hFxB⟩).choose_spec.2.differentiableAt
    have hxG : x ∈ Set.Icc (p : ℝ) (D.germ.rightEnd : ℝ) :=
      ⟨hpx.le, hlt.le.trans (D.a_lt_b.le.trans D.b_lt_germEnd.le)⟩
    have hF : DifferentiableAt ℝ D.germ.extension x :=
      (D.germ.contDiff_one.contDiffAt
        (D.germ.isOpen_neighborhood.mem_nhds
          (D.germ.segment_subset hxG))).differentiableAt_one
    have hleft := (hcoordFx.hasDerivAt.comp x hF.hasDerivAt).deriv
    have hright := (hcoordX.hasDerivAt.add_const 1).deriv
    have heq := hEq.deriv_eq
    change deriv (D.gluedCoord S ∘ D.germ.extension) x =
      deriv (fun z ↦ D.gluedCoord S z + 1) x at heq
    rw [hleft, hright] at heq
    exact heq.symm

private theorem gluedCoord_logDeriv_cocycle
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hpx : (p : ℝ) < x) (hxa : x ≤ (D.a : ℝ)) :
    Real.log (deriv (D.gluedCoord S) x) =
      Real.log (deriv (D.gluedCoord S) (D.germ.extension x)) +
        Real.log (deriv D.germ.extension x) := by
  rw [D.gluedCoord_deriv_cocycle S hpx hxa]
  apply Real.log_mul
  · have hxb : x ≤ (D.b : ℝ) := hxa.trans D.a_lt_b.le
    have hFxP : (p : ℝ) < D.germ.extension x :=
      hpx.trans (D.extension_moves ⟨hpx, hxb⟩)
    have hFxB : D.germ.extension x ≤ (D.b : ℝ) := by
      rcases hxa.eq_or_lt with rfl | hlt
      · rw [D.extension_a]
      · exact (D.extension_lt_b_of_lt_a hpx.le hlt).le
    exact (D.gluedCoord_deriv_pos_to_b S hFxP hFxB).ne'
  · exact (D.germ.deriv_pos x
      ⟨hpx.le, hxa.trans (D.a_lt_b.le.trans D.b_lt_germEnd.le)⟩).ne'

private theorem gluedCoord_logDeriv_bv_pullback
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {u v : ℝ}
    (hpu : (p : ℝ) < u) (huv : u ≤ v) (hva : v ≤ (D.a : ℝ))
    (himage : BoundedVariationOn
      (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
      (Set.Icc (D.germ.extension u) (D.germ.extension v))) :
    BoundedVariationOn
      (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
      (Set.Icc u v) := by
  let ell : ℝ → ℝ :=
    fun x ↦ Real.log (deriv (D.gluedCoord S) x)
  have hvb : v ≤ (D.b : ℝ) := hva.trans D.a_lt_b.le
  have hFmono : MonotoneOn D.germ.extension (Set.Icc u v) := by
    apply D.extension_strictMonoOn.monotoneOn.mono
    exact Set.Icc_subset_Icc hpu.le hvb
  have hFmaps : Set.MapsTo D.germ.extension (Set.Icc u v)
      (Set.Icc (D.germ.extension u) (D.germ.extension v)) := by
    intro x hx
    exact ⟨hFmono ⟨le_rfl, huv⟩ hx hx.1,
      hFmono hx ⟨huv, le_rfl⟩ hx.2⟩
  have hcomp : BoundedVariationOn (ell ∘ D.germ.extension)
      (Set.Icc u v) := by
    apply ne_top_of_le_ne_top himage
    exact eVariationOn.comp_le_of_monotoneOn ell D.germ.extension
      hFmono hFmaps
  have hgerm : BoundedVariationOn
      (fun x ↦ Real.log (deriv D.germ.extension x)) (Set.Icc u v) := by
    change BoundedVariationOn D.germ.logDeriv (Set.Icc u v)
    exact D.germ_logDeriv_bv.mono
      (Set.Icc_subset_Icc hpu.le
        (hvb.trans D.b_lt_germEnd.le))
  have hadd : BoundedVariationOn
      (fun x ↦ ell (D.germ.extension x) +
        Real.log (deriv D.germ.extension x)) (Set.Icc u v) := by
    simpa [ell, Function.comp_def] using boundedVariationOn_add hcomp hgerm
  have hEq : Set.EqOn ell
      (fun x ↦ ell (D.germ.extension x) +
        Real.log (deriv D.germ.extension x)) (Set.Icc u v) := by
    intro x hx
    exact D.gluedCoord_logDeriv_cocycle S
      (hpu.trans_le hx.1) (hx.2.trans hva)
  rw [BoundedVariationOn, eVariationOn.eq_of_eqOn hEq]
  exact hadd

private theorem gluedCoord_logDeriv_bv_aux
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    ∀ N u v,
      (p : ℝ) < u → u ≤ v → v ≤ (D.b : ℝ) →
      D.arrivalIndex u ≤ N →
      BoundedVariationOn
        (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
        (Set.Icc u v) := by
  intro N
  induction N with
  | zero =>
      intro u v hpu huv hvb harr
      have hu0 : D.arrivalIndex u = 0 := Nat.eq_zero_of_le_zero harr
      have hau : (D.a : ℝ) ≤ u := by
        by_cases hub : u < (D.b : ℝ)
        · exact (D.arrivalIndex_eq_zero_iff hpu hub).1 hu0
        · exact (show (D.a : ℝ) ≤ (D.b : ℝ) from D.a_lt_b.le).trans
            (le_of_not_gt hub)
      exact D.gluedCoord_logDeriv_bv_seedInterval S hau huv hvb
  | succ N ih =>
      intro u v hpu huv hvb harr
      by_cases hau : (D.a : ℝ) ≤ u
      · exact D.gluedCoord_logDeriv_bv_seedInterval S hau huv hvb
      · have hua : u < (D.a : ℝ) := lt_of_not_ge hau
        have hshift := D.arrivalIndex_image_add_one hpu hua
        have hFuArr : D.arrivalIndex (D.germ.extension u) ≤ N := by omega
        by_cases hva : v ≤ (D.a : ℝ)
        · have hFuP : (p : ℝ) < D.germ.extension u :=
            hpu.trans (D.extension_moves ⟨hpu, hua.le.trans D.a_lt_b.le⟩)
          have hFmono : MonotoneOn D.germ.extension (Set.Icc u v) := by
            apply D.extension_strictMonoOn.monotoneOn.mono
            exact Set.Icc_subset_Icc hpu.le
              (hva.trans (show (D.a : ℝ) ≤ (D.b : ℝ) from D.a_lt_b.le))
          have hFuFv : D.germ.extension u ≤ D.germ.extension v :=
            hFmono ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv
          have hFvB : D.germ.extension v ≤ (D.b : ℝ) := by
            rcases hva.eq_or_lt with rfl | hlt
            · rw [D.extension_a]
            · exact (D.extension_lt_b_of_lt_a
                (hpu.le.trans huv) hlt).le
          have himage := ih (D.germ.extension u) (D.germ.extension v)
            hFuP hFuFv hFvB hFuArr
          exact D.gluedCoord_logDeriv_bv_pullback S hpu huv hva himage
        · have hav : (D.a : ℝ) < v := lt_of_not_ge hva
          have hFuP : (p : ℝ) < D.germ.extension u :=
            hpu.trans (D.extension_moves ⟨hpu, hua.le.trans D.a_lt_b.le⟩)
          have hFuB : D.germ.extension u ≤ (D.b : ℝ) :=
            (D.extension_lt_b_of_lt_a hpu.le hua).le
          have himage := ih (D.germ.extension u) (D.b : ℝ)
            hFuP hFuB le_rfl hFuArr
          have hleft : BoundedVariationOn
              (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
              (Set.Icc u (D.a : ℝ)) := by
            have h := D.gluedCoord_logDeriv_bv_pullback S hpu hua.le le_rfl
              (by simpa [D.extension_a] using himage)
            exact h
          have hright : BoundedVariationOn
              (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
              (Set.Icc (D.a : ℝ) v) :=
            D.gluedCoord_logDeriv_bv_seedInterval S le_rfl hav.le hvb
          let ell : ℝ → ℝ :=
            fun x ↦ Real.log (deriv (D.gluedCoord S) x)
          have hsum := eVariationOn.Icc_add_Icc ell
            (s := Set.univ) hua.le hav.le (by simp)
          simp only [Set.univ_inter] at hsum
          rw [BoundedVariationOn, ← hsum]
          exact ENNReal.add_ne_top.mpr ⟨hleft, hright⟩

private theorem gluedCoord_logDeriv_bv
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {u v : ℝ}
    (hpu : (p : ℝ) < u) (huv : u ≤ v) (hvb : v < (D.b : ℝ)) :
    BoundedVariationOn
      (fun x ↦ Real.log (deriv (D.gluedCoord S) x))
      (Set.Icc u v) := by
  exact D.gluedCoord_logDeriv_bv_aux S (D.arrivalIndex u)
    u v hpu huv hvb.le le_rfl

private theorem gluedCoord_surjective_Iio
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 1) :
    ∃ x : ℝ, x ∈ Set.Ioo (p : ℝ) (D.b : ℝ) ∧
      D.gluedCoord S x = s := by
  obtain ⟨e, he⟩ := D.exists_segmentOrderIso
  let pB : Set.Icc (p : ℝ) (D.b : ℝ) :=
    ⟨p, le_rfl, D.base_lt_a.le.trans D.a_lt_b.le⟩
  let aB : Set.Icc (p : ℝ) (D.b : ℝ) :=
    ⟨D.a, D.base_lt_a.le, D.a_lt_b.le⟩
  let bB : Set.Icc (p : ℝ) (D.b : ℝ) :=
    ⟨D.b, D.base_lt_a.le.trans D.a_lt_b.le, le_rfl⟩
  let pA : Set.Icc (p : ℝ) (D.a : ℝ) :=
    ⟨p, le_rfl, D.base_lt_a.le⟩
  let aA : Set.Icc (p : ℝ) (D.a : ℝ) :=
    ⟨D.a, D.base_lt_a.le, le_rfl⟩
  let back : Set.Icc (p : ℝ) (D.b : ℝ) →
      Set.Icc (p : ℝ) (D.b : ℝ) := fun y ↦
    ⟨e.symm y, (e.symm y).property.1,
      (e.symm y).property.2.trans D.a_lt_b.le⟩
  have heP : e pA = pB := by
    apply Subtype.ext
    change (e pA : ℝ) = (p : ℝ)
    rw [he]
    exact D.extension_base
  have heA : e aA = bB := by
    apply Subtype.ext
    change (e aA : ℝ) = (D.b : ℝ)
    rw [he]
    exact D.extension_a
  have hbackP : back pB = pB := by
    apply Subtype.ext
    change (e.symm pB : ℝ) = (p : ℝ)
    have h := e.symm_apply_eq.mpr heP.symm
    exact congrArg Subtype.val h
  have hback_strict : StrictMono back := by
    intro x y hxy
    exact e.symm.strictMono hxy
  have hFback (y : Set.Icc (p : ℝ) (D.b : ℝ)) :
      D.germ.extension (back y : ℝ) = (y : ℝ) := by
    calc
      D.germ.extension (back y : ℝ) = (e (e.symm y) : ℝ) := by
        symm
        exact he (e.symm y)
      _ = (y : ℝ) := congrArg Subtype.val (e.apply_symm_apply y)
  have hback_lt_a (y : Set.Icc (p : ℝ) (D.b : ℝ))
      (hya : (y : ℝ) ≤ (D.a : ℝ)) :
      (back y : ℝ) < (D.a : ℝ) := by
    have hyb : y < bB := hya.trans_lt D.a_lt_b
    have hinv := e.symm.strictMono hyb
    have hinvB : e.symm bB = aA := e.symm_apply_eq.mpr heA.symm
    rw [hinvB] at hinv
    exact hinv
  let xSeq : ℕ → Set.Icc (p : ℝ) (D.b : ℝ) :=
    fun n ↦ (back^[n]) aB
  have hxSeq_pos (n : ℕ) : (p : ℝ) < (xSeq n : ℝ) := by
    have hmono : StrictMono (back^[n]) := hback_strict.iterate n
    have hpaB : pB < aB := D.base_lt_a
    have h := hmono hpaB
    rw [Function.IsFixedPt.iterate hbackP n] at h
    exact h
  have hxSeq_le_a : ∀ n : ℕ, (xSeq n : ℝ) ≤ (D.a : ℝ) := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
        rw [show xSeq (n + 1) = back (xSeq n) by
          simp only [xSeq, Function.iterate_succ_apply']]
        exact (hback_lt_a (xSeq n) ih).le
  have hcoordA : D.gluedCoord S (D.a : ℝ) = 0 := by
    have hn : D.arrivalIndex (D.a : ℝ) = 0 :=
      (D.arrivalIndex_eq_zero_iff D.base_lt_a D.a_lt_b).2 le_rfl
    simp [gluedCoord, hn, S.value_a]
  have hcoordSeq : ∀ n : ℕ,
      D.gluedCoord S (xSeq n : ℝ) = -(n : ℝ) := by
    intro n
    induction n with
    | zero => simpa [xSeq] using hcoordA
    | succ n ih =>
        have hxNext : xSeq (n + 1) = back (xSeq n) := by
          simp only [xSeq, Function.iterate_succ_apply']
        have hnextPos : (p : ℝ) < (xSeq (n + 1) : ℝ) :=
          hxSeq_pos (n + 1)
        have hnextA : (xSeq (n + 1) : ℝ) < (D.a : ℝ) := by
          rw [hxNext]
          exact hback_lt_a (xSeq n) (hxSeq_le_a n)
        have hact := D.gluedCoord_action S hnextPos hnextA
        have hnextImage : D.germ.extension (xSeq (n + 1) : ℝ) =
            (xSeq n : ℝ) := by
          rw [hxNext]
          exact hFback (xSeq n)
        rw [hnextImage, ih] at hact
        push_cast
        linarith
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (-s)
  have hxBelow : D.gluedCoord S (xSeq N : ℝ) < s := by
    rw [hcoordSeq N]
    exact neg_lt.mp hN
  let t : ℝ := (max s 0 + 1) / 2
  have hmaxLt : max s 0 < 1 := (max_lt_iff.mpr ⟨hs, by norm_num⟩)
  have htPos : 0 < t := by
    dsimp [t]
    have : 0 ≤ max s 0 := le_max_right _ _
    linarith
  have htLt : t < 1 := by
    dsimp [t]
    linarith
  have hst : s < t := by
    dsimp [t]
    have hsmax : s ≤ max s 0 := le_max_left _ _
    linarith
  have hseedImage : S.psi '' Set.Icc (D.a : ℝ) (D.b : ℝ) =
      Set.Icc (0 : ℝ) 1 := by
    have himage := S.contDiff.continuous.continuousOn.image_Icc_of_monotoneOn
      (a := (D.a : ℝ)) (b := (D.b : ℝ))
      (show (D.a : ℝ) ≤ (D.b : ℝ) from D.a_lt_b.le)
      S.strictMonoOn.monotoneOn
    simpa [S.value_a, S.value_b] using himage
  have htMem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htPos.le, htLt.le⟩
  rw [← hseedImage] at htMem
  rcases htMem with ⟨y, hy, hpsiY⟩
  have hay : (D.a : ℝ) < y := by
    apply lt_of_le_of_ne hy.1
    intro hayEq
    subst y
    rw [S.value_a] at hpsiY
    linarith
  have hyb : y < (D.b : ℝ) := by
    apply lt_of_le_of_ne hy.2
    intro hybEq
    subst y
    rw [S.value_b] at hpsiY
    linarith
  have hcoordY : D.gluedCoord S y = t := by
    have hn : D.arrivalIndex y = 0 :=
      (D.arrivalIndex_eq_zero_iff
        ((show (p : ℝ) < (D.a : ℝ) from D.base_lt_a).trans hay) hyb).2 hay.le
    simp [gluedCoord, hn, hpsiY]
  have hxy : (xSeq N : ℝ) ≤ y :=
    (hxSeq_le_a N).trans hay.le
  have hsub : Set.Icc (xSeq N : ℝ) y ⊆
      Set.Ioo (p : ℝ) (D.b : ℝ) := by
    intro z hz
    exact ⟨(hxSeq_pos N).trans_le hz.1, hz.2.trans_lt hyb⟩
  have hcont : ContinuousOn (D.gluedCoord S)
      (Set.Icc (xSeq N : ℝ) y) :=
    D.gluedCoord_contDiffOn S |>.continuousOn.mono hsub
  have hmono : MonotoneOn (D.gluedCoord S)
      (Set.Icc (xSeq N : ℝ) y) :=
    D.gluedCoord_strictMonoOn S |>.monotoneOn.mono hsub
  have himage := hcont.image_Icc_of_monotoneOn hxy hmono
  have hsMem : s ∈ Set.Icc
      (D.gluedCoord S (xSeq N : ℝ)) (D.gluedCoord S y) := by
    rw [hcoordY]
    exact ⟨hxBelow.le, hst.le⟩
  rw [← himage] at hsMem
  rcases hsMem with ⟨x, hx, hcoord⟩
  exact ⟨x, hsub hx, hcoord⟩

private theorem gluedCoord_image_Ioo
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    D.gluedCoord S '' Set.Ioo (p : ℝ) (D.b : ℝ) =
      Set.Iio (1 : ℝ) := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hb := D.gluedCoord_bounds S hx.1 hx.2
    have hn : (0 : ℝ) ≤ (D.arrivalIndex x : ℝ) := by positivity
    exact hb.2.trans_le (by linarith)
  · intro hs
    obtain ⟨x, hx, hcoord⟩ := D.gluedCoord_surjective_Iio S hs
    exact ⟨x, hx, hcoord⟩

private noncomputable def gluedCoordOrderIso
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    Set.Ioo (p : ℝ) (D.b : ℝ) ≃o Set.Iio (1 : ℝ) :=
  (D.gluedCoord_strictMonoOn S).orderIso (D.gluedCoord S)
      (Set.Ioo (p : ℝ) (D.b : ℝ)) |>.trans
    (OrderIso.setCongr _ _ (D.gluedCoord_image_Ioo S))

@[simp] private theorem gluedCoordOrderIso_apply
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) (x : Set.Ioo (p : ℝ) (D.b : ℝ)) :
    ((D.gluedCoordOrderIso S x : Set.Iio (1 : ℝ)) : ℝ) =
      D.gluedCoord S (x : ℝ) := rfl

private noncomputable def gluedPointI
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) (s : ℝ) : I :=
  if hs : s < 1 then
    let x := (D.gluedCoordOrderIso S).symm
      (⟨s, hs⟩ : Set.Iio (1 : ℝ))
    ⟨(x : ℝ),
      ⟨p.property.1.trans x.property.1.le,
        x.property.2.le.trans D.b.property.2⟩⟩
  else D.a

private noncomputable def gluedPoint
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) (s : ℝ) : ℝ :=
  (D.gluedPointI S s : ℝ)

private theorem gluedPoint_mem
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 1) :
    D.gluedPoint S s ∈ Set.Ioo (p : ℝ) (D.b : ℝ) := by
  simp only [gluedPoint, gluedPointI, dif_pos hs]
  exact ((D.gluedCoordOrderIso S).symm
    (⟨s, hs⟩ : Set.Iio (1 : ℝ))).property

private theorem gluedCoord_gluedPoint
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 1) :
    D.gluedCoord S (D.gluedPoint S s) = s := by
  have h := (D.gluedCoordOrderIso S).apply_symm_apply
    (⟨s, hs⟩ : Set.Iio (1 : ℝ))
  have hval := congrArg Subtype.val h
  change D.gluedCoord S
      (((D.gluedCoordOrderIso S).symm
        (⟨s, hs⟩ : Set.Iio (1 : ℝ)) :
          Set.Ioo (p : ℝ) (D.b : ℝ)) : ℝ) = s at hval
  rw [gluedPoint, gluedPointI, dif_pos hs]
  exact hval

private theorem gluedPoint_gluedCoord
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {x : ℝ}
    (hx : x ∈ Set.Ioo (p : ℝ) (D.b : ℝ)) :
    D.gluedPoint S (D.gluedCoord S x) = x := by
  have htop : D.gluedCoord S x < 1 := by
    have hb := D.gluedCoord_bounds S hx.1 hx.2
    have hn : (0 : ℝ) ≤ (D.arrivalIndex x : ℝ) := by positivity
    linarith
  let xI : Set.Ioo (p : ℝ) (D.b : ℝ) := ⟨x, hx⟩
  have h := (D.gluedCoordOrderIso S).symm_apply_apply xI
  have hval := congrArg Subtype.val h
  have harg :
      (⟨D.gluedCoord S x, htop⟩ : Set.Iio (1 : ℝ)) =
        D.gluedCoordOrderIso S xI := by
    apply Subtype.ext
    rfl
  rw [gluedPoint, gluedPointI, dif_pos htop]
  change (((D.gluedCoordOrderIso S).symm
    (⟨D.gluedCoord S x, htop⟩ : Set.Iio (1 : ℝ)) :
      Set.Ioo (p : ℝ) (D.b : ℝ)) : ℝ) = x
  rw [harg]
  exact hval

private theorem gluedPoint_continuousOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    ContinuousOn (D.gluedPoint S) (Set.Iio (1 : ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hcont : Continuous
      (fun s : Set.Iio (1 : ℝ) ↦
        (((D.gluedCoordOrderIso S).symm s :
          Set.Ioo (p : ℝ) (D.b : ℝ)) : ℝ)) :=
    continuous_subtype_val.comp (D.gluedCoordOrderIso S).symm.continuous
  convert hcont using 1
  funext s
  have hs : (s : ℝ) < 1 := s.property
  simp only [Set.restrict, gluedPoint, gluedPointI, dif_pos hs]

private theorem gluedPoint_hasDerivAt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 1) :
    HasDerivAt (D.gluedPoint S)
      (deriv (D.gluedCoord S) (D.gluedPoint S s))⁻¹ s := by
  have hx := D.gluedPoint_mem S hs
  have hcoord : HasDerivAt (D.gluedCoord S)
      (deriv (D.gluedCoord S) (D.gluedPoint S s))
      (D.gluedPoint S s) :=
    (D.gluedCoord_hasDerivAt_pos S hx).choose_spec.2.differentiableAt.hasDerivAt
  have hcoordPos := D.gluedCoord_deriv_pos S hx
  have hpointCont : ContinuousAt (D.gluedPoint S) s :=
    (D.gluedPoint_continuousOn S s hs).continuousAt
      (isOpen_Iio.mem_nhds hs)
  apply hcoord.of_local_left_inverse hpointCont hcoordPos.ne'
  filter_upwards [Iio_mem_nhds hs] with t ht
  exact D.gluedCoord_gluedPoint S ht

private theorem gluedPoint_deriv_eq
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 1) :
    deriv (D.gluedPoint S) s =
      (deriv (D.gluedCoord S) (D.gluedPoint S s))⁻¹ :=
  (D.gluedPoint_hasDerivAt S hs).deriv

private theorem gluedPoint_deriv_pos
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 1) :
    0 < deriv (D.gluedPoint S) s := by
  rw [D.gluedPoint_deriv_eq S hs]
  exact inv_pos.mpr (D.gluedCoord_deriv_pos S (D.gluedPoint_mem S hs))

private theorem gluedPoint_contDiffAt
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 1) :
    ContDiffAt ℝ 1 (D.gluedPoint S) s := by
  let x : ℝ := D.gluedPoint S s
  have hx : x ∈ Set.Ioo (p : ℝ) (D.b : ℝ) := D.gluedPoint_mem S hs
  have hcoordAt : ContDiffAt ℝ 1 (D.gluedCoord S) x :=
    (D.gluedCoord_contDiffOn S x hx).contDiffAt
      (isOpen_Ioo.mem_nhds hx)
  let d : ℝ := deriv (D.gluedCoord S) x
  have hdpos : 0 < d := D.gluedCoord_deriv_pos S hx
  have hcoordDeriv : HasDerivAt (D.gluedCoord S) d x := by
    exact (D.gluedCoord_hasDerivAt_pos S hx).choose_spec.2.differentiableAt.hasDerivAt
  let dEquiv : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hdpos.ne')
  have hF : HasFDerivAt (D.gluedCoord S)
      (dEquiv : ℝ →L[ℝ] ℝ) x := by
    simpa [dEquiv] using hcoordDeriv.hasFDerivAt_equiv hdpos.ne'
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hlocal : ContDiffAt ℝ 1
      (hcoordAt.localInverse hF hn) (D.gluedCoord S x) :=
    hcoordAt.to_localInverse hF hn
  have hstrict : HasStrictFDerivAt (D.gluedCoord S)
      (dEquiv : ℝ →L[ℝ] ℝ) x :=
    hcoordAt.hasStrictFDerivAt' hF hn
  have hleft : ∀ᶠ z in nhds x,
      D.gluedPoint S (D.gluedCoord S z) = z := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
    exact D.gluedPoint_gluedCoord S hz
  have heq := hstrict.localInverse_unique hleft
  have heq' : D.gluedPoint S =ᶠ[nhds (D.gluedCoord S x)]
      hcoordAt.localInverse hF hn := by
    exact heq
  have hout := hlocal.congr_of_eventuallyEq heq'
  simpa [x, D.gluedCoord_gluedPoint S hs] using hout

private theorem gluedPoint_contDiffOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    ContDiffOn ℝ 1 (D.gluedPoint S) (Set.Iio (1 : ℝ)) := by
  intro s hs
  exact (D.gluedPoint_contDiffAt S hs).contDiffWithinAt

private theorem gluedPoint_strictMonoOn
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    StrictMonoOn (D.gluedPoint S) (Set.Iio (1 : ℝ)) := by
  intro s hs t ht hst
  have hs' : s < 1 := hs
  have ht' : t < 1 := ht
  simp only [gluedPoint, gluedPointI, dif_pos hs', dif_pos ht']
  exact (D.gluedCoordOrderIso S).symm.strictMono hst

private theorem gluedPoint_logDeriv_bv
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {a b : ℝ}
    (hb : b < 1) (hab : a ≤ b) :
    BoundedVariationOn
      (fun s ↦ Real.log (deriv (D.gluedPoint S) s))
      (Set.Icc a b) := by
  let ell : ℝ → ℝ :=
    fun x ↦ Real.log (deriv (D.gluedCoord S) x)
  have ha : a < 1 := hab.trans_lt hb
  have hsub : Set.Icc a b ⊆ Set.Iio (1 : ℝ) := by
    intro s hs
    exact hs.2.trans_lt hb
  have hpointMono : MonotoneOn (D.gluedPoint S) (Set.Icc a b) :=
    D.gluedPoint_strictMonoOn S |>.monotoneOn.mono hsub
  have hpointA := D.gluedPoint_mem S ha
  have hpointB := D.gluedPoint_mem S hb
  have hpointAB : D.gluedPoint S a ≤ D.gluedPoint S b :=
    hpointMono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hphysical : BoundedVariationOn ell
      (Set.Icc (D.gluedPoint S a) (D.gluedPoint S b)) :=
    D.gluedCoord_logDeriv_bv S hpointA.1 hpointAB hpointB.2
  have hmaps : Set.MapsTo (D.gluedPoint S) (Set.Icc a b)
      (Set.Icc (D.gluedPoint S a) (D.gluedPoint S b)) := by
    intro s hs
    exact ⟨hpointMono ⟨le_rfl, hab⟩ hs hs.1,
      hpointMono hs ⟨hab, le_rfl⟩ hs.2⟩
  have hcomp : BoundedVariationOn (ell ∘ D.gluedPoint S)
      (Set.Icc a b) := by
    apply ne_top_of_le_ne_top hphysical
    exact eVariationOn.comp_le_of_monotoneOn ell (D.gluedPoint S)
      hpointMono hmaps
  have hneg : BoundedVariationOn
      (fun s ↦ -ell (D.gluedPoint S s)) (Set.Icc a b) := by
    simpa [Function.comp_def] using boundedVariationOn_neg hcomp
  have hEq : Set.EqOn
      (fun s ↦ Real.log (deriv (D.gluedPoint S) s))
      (fun s ↦ -ell (D.gluedPoint S s)) (Set.Icc a b) := by
    intro s hs
    change Real.log (deriv (D.gluedPoint S) s) =
      -Real.log (deriv (D.gluedCoord S) (D.gluedPoint S s))
    rw [D.gluedPoint_deriv_eq S (hs.2.trans_lt hb), Real.log_inv]
  rw [BoundedVariationOn, eVariationOn.eq_of_eqOn hEq]
  exact hneg

private noncomputable def gluedEmbedding
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) : RightOrbitLineEmbedding p where
  rightEnd := D.b
  base_lt_rightEnd := D.base_lt_a.trans D.a_lt_b
  top := 1
  coord := fun x ↦ D.gluedCoord S (x : ℝ)
  point := D.gluedPointI S
  coord_strictMono := by
    intro x hx y hy hxy
    exact D.gluedCoord_strictMonoOn S
      ⟨show (p : ℝ) < (x : ℝ) from hx.1,
        show (x : ℝ) < (D.b : ℝ) from hx.2⟩
      ⟨show (p : ℝ) < (y : ℝ) from hy.1,
        show (y : ℝ) < (D.b : ℝ) from hy.2⟩ hxy
  coord_lt_top := by
    intro x hx
    have hb := D.gluedCoord_bounds S
      (show (p : ℝ) < (x : ℝ) from hx.1)
      (show (x : ℝ) < (D.b : ℝ) from hx.2)
    have hn : (0 : ℝ) ≤ (D.arrivalIndex (x : ℝ) : ℝ) := by positivity
    exact hb.2.trans_le (sub_le_self 1 hn)
  point_mem := by
    intro s hs
    exact D.gluedPoint_mem S hs
  point_coord := by
    intro x hx
    apply Subtype.ext
    exact D.gluedPoint_gluedCoord S hx
  coord_point := by
    intro s hs
    exact D.gluedCoord_gluedPoint S hs

private theorem gluedPoint_zero
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) :
    D.gluedPoint S 0 = (D.a : ℝ) := by
  have haMem : (D.a : ℝ) ∈
      Set.Ioo (p : ℝ) (D.b : ℝ) :=
    ⟨D.base_lt_a, D.a_lt_b⟩
  have hcoordA : D.gluedCoord S (D.a : ℝ) = 0 := by
    have hn : D.arrivalIndex (D.a : ℝ) = 0 :=
      (D.arrivalIndex_eq_zero_iff D.base_lt_a D.a_lt_b).2 le_rfl
    simp [gluedCoord, hn, S.value_a]
  have h := D.gluedPoint_gluedCoord S haMem
  rwa [hcoordA] at h

private theorem gluedPoint_lt_a_of_neg
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) {s : ℝ} (hs : s < 0) :
    D.gluedPoint S s < (D.a : ℝ) := by
  have hsTop : s < 1 := hs.trans (by norm_num)
  have hzeroTop : (0 : ℝ) < 1 := by norm_num
  have h := D.gluedPoint_strictMonoOn S hsTop hzeroTop hs
  rwa [D.gluedPoint_zero S] at h

private noncomputable def gluedFAction
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) : RightGermLineLift (D.gluedEmbedding S) f where
  lift := CircleDeg1Lift.translate (Multiplicative.ofAdd (1 : ℝ))
  tailBound := 0
  tailBound_lt_top := by
    change (0 : ℝ) < 1
    norm_num
  image_mem := by
    intro s hs
    have hsTop : s < 1 := hs.trans (by norm_num)
    have hxMem := D.gluedPoint_mem S hsTop
    have hxa := D.gluedPoint_lt_a_of_neg S hs
    let x : I := D.gluedPointI S s
    have hxG : (x : ℝ) ∈
        Set.Icc (p : ℝ) (D.germ.rightEnd : ℝ) := by
      exact ⟨hxMem.1.le,
        hxa.le.trans (D.a_lt_b.le.trans D.b_lt_germEnd.le)⟩
    have hagree : (f x : ℝ) = D.germ.extension (x : ℝ) :=
      D.germ.agrees hxG
    change f x ∈ Set.Ioo p D.b
    constructor
    · change (p : ℝ) < (f x : ℝ)
      rw [hagree]
      exact hxMem.1.trans (D.extension_moves
        ⟨hxMem.1, hxa.le.trans D.a_lt_b.le⟩)
    · change (f x : ℝ) < (D.b : ℝ)
      rw [hagree]
      exact D.extension_lt_b_of_lt_a hxMem.1.le hxa
  intertwines := by
    intro s hs
    have hsTop : s < 1 := hs.trans (by norm_num)
    have hxMem := D.gluedPoint_mem S hsTop
    have hxa := D.gluedPoint_lt_a_of_neg S hs
    let x : I := D.gluedPointI S s
    have hxG : (x : ℝ) ∈
        Set.Icc (p : ℝ) (D.germ.rightEnd : ℝ) := by
      exact ⟨hxMem.1.le,
        hxa.le.trans (D.a_lt_b.le.trans D.b_lt_germEnd.le)⟩
    have hagree : (f x : ℝ) = D.germ.extension (x : ℝ) :=
      D.germ.agrees hxG
    change D.gluedCoord S (f x : ℝ) =
      circleLiftFun (CircleDeg1Lift.translate
        (Multiplicative.ofAdd (1 : ℝ))) s
    rw [hagree]
    change D.gluedCoord S
      (D.germ.extension (D.gluedPoint S s)) =
        circleLiftFun (CircleDeg1Lift.translate
          (Multiplicative.ofAdd (1 : ℝ))) s
    rw [D.gluedCoord_action S hxMem.1 hxa,
      D.gluedCoord_gluedPoint S hsTop]
    simp [circleLiftFun, CircleDeg1Lift.translate_apply, add_comm]

private theorem gluedFAction_translation
    {f : IntervalMap} {p : I} (D : AbelFundamentalData f p)
    (S : AbelSeed D) (s : ℝ) :
    circleLiftFun (D.gluedFAction S).lift s = s + 1 := by
  simp [gluedFAction, circleLiftFun, CircleDeg1Lift.translate_apply,
    add_comm]

end AbelFundamentalData

/-- Smooth direct-limit construction for one repelling `C¹+BV` germ,
checked against the scratch copy of the production interface. -/
private theorem exists_normalizedC1BVAbelCoordinate
    {f : IntervalMap} {p : I}
    (hf_fixed : IsFixedPoint f p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p) :
    Nonempty (NormalizedC1BVAbelCoordinate f p) := by
  obtain ⟨D⟩ := exists_abelFundamentalData hf_fixed hf_repelling hf_regular
  obtain ⟨S⟩ := D.exists_abelSeed
  exact ⟨{
    embedding := D.gluedEmbedding S
    fAction := D.gluedFAction S
    f_translation := D.gluedFAction_translation S
    coordExtension := D.gluedCoord S
    pointExtension := D.gluedPoint S
    coord_agrees := by
      intro x hx
      rfl
    point_agrees := by
      intro s hs
      rfl
    coord_contDiff := by
      simpa [AbelFundamentalData.gluedEmbedding] using
        D.gluedCoord_contDiffOn S
    point_contDiff := by
      simpa [AbelFundamentalData.gluedEmbedding] using
        D.gluedPoint_contDiffOn S
    coord_deriv_pos := by
      intro x hx
      exact D.gluedCoord_deriv_pos S hx
    point_deriv_pos := by
      intro s hs
      exact D.gluedPoint_deriv_pos S hs
    coord_logDeriv_bv := by
      intro a b ha hb hab
      exact D.gluedCoord_logDeriv_bv S ha hab hb
    point_logDeriv_bv := by
      intro a b hb hab
      exact D.gluedPoint_logDeriv_bv S hb hab
  }⟩

/-- A fixed regular germ commuting with the deck germ descends to a regular
degree-one lift in the already chosen Abel coordinate. -/
private theorem regularLineLift_of_normalizedC1BVAbelCoordinate
    {f G : IntervalMap} {p : I}
    (C : NormalizedC1BVAbelCoordinate f p)
    (hG_fixed : IsFixedPoint G p)
    (hG_regular : HasRightGermC1BV G p)
    (hfG_commute : RightGermCommute p f G) :
    ∃ GAction : RightGermLineLift C.embedding G,
      IsC1BVUnitLift GAction.lift := by
  rcases hG_regular with ⟨gG, hgGBV⟩
  rcases hfG_commute with ⟨qComm, hpComm, hcomm⟩
  let rF : I := C.embedding.point C.fAction.tailBound
  have hrFMem : rF ∈ Set.Ioo p C.embedding.rightEnd :=
    C.embedding.point_mem C.fAction.tailBound
      C.fAction.tailBound_lt_top
  obtain ⟨qMap, hpMap, hqMapG, hGmaps⟩ :=
    exists_rightInterval_mapsInto gG hG_fixed hrFMem.1
  have hpCut : p < min qMap (min qComm C.embedding.rightEnd) := by
    simp only [lt_min_iff]
    exact ⟨hpMap, hpComm, C.embedding.base_lt_rightEnd⟩
  obtain ⟨qReal, hpq, hqCut⟩ := exists_between hpCut
  have hqMap : qReal < (qMap : ℝ) :=
    hqCut.trans_le (min_le_left _ _)
  have hqComm : qReal < (qComm : ℝ) :=
    hqCut.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hqEnd : qReal < (C.embedding.rightEnd : ℝ) :=
    hqCut.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let q : I := ⟨qReal, ⟨p.property.1.trans hpq.le,
    hqEnd.le.trans C.embedding.rightEnd.property.2⟩⟩
  have hqMem : q ∈ Set.Ioo p C.embedding.rightEnd := ⟨hpq, hqEnd⟩
  let bound : ℝ := min C.fAction.tailBound (C.embedding.coord q) - 3
  obtain ⟨a : ℤ, ha⟩ := exists_int_lt bound
  have haTail : (a : ℝ) + 3 < C.fAction.tailBound := by
    have h := min_le_left C.fAction.tailBound (C.embedding.coord q)
    dsimp only [bound] at ha
    linarith
  have haCoord : (a : ℝ) + 3 < C.embedding.coord q := by
    have h := min_le_right C.fAction.tailBound (C.embedding.coord q)
    dsimp only [bound] at ha
    linarith
  let raw : ℝ → ℝ := fun s =>
    C.coordExtension (gG.extension (C.pointExtension s))
  have hphysical : ∀ s < (a : ℝ) + 2,
      G (C.embedding.point s) ∈ Set.Ioo p rF ∧
        raw s = C.embedding.coord (G (C.embedding.point s)) := by
    intro s hs
    have hsCoord : s < C.embedding.coord q := by linarith
    have hsTop : s < C.embedding.top :=
      hsCoord.trans (C.embedding.coord_lt_top hqMem)
    have hsMem := C.embedding.point_mem s hsTop
    have hsLtQ : C.embedding.point s < q :=
      C.embedding.point_lt_of_lt_coord hqMem hsCoord
    have hsMap : C.embedding.point s ∈ Set.Ioc p qMap := by
      constructor
      · exact hsMem.1
      · change (C.embedding.point s : ℝ) ≤ (qMap : ℝ)
        exact hsLtQ.le.trans hqMap.le
    have hGMemRF := hGmaps _ hsMap
    have hGMem : G (C.embedding.point s) ∈
        Set.Ioo p C.embedding.rightEnd :=
      ⟨hGMemRF.1, hGMemRF.2.trans hrFMem.2⟩
    refine ⟨hGMemRF, ?_⟩
    have hsGDomain : C.embedding.point s ∈ Set.Icc p gG.rightEnd := by
      constructor
      · exact hsMem.1.le
      · change (C.embedding.point s : ℝ) ≤ (gG.rightEnd : ℝ)
        have hsLtQReal : (C.embedding.point s : ℝ) < qReal := hsLtQ
        exact (hsLtQReal.le.trans hqMap.le).trans hqMapG.le
    calc
      raw s = C.coordExtension
          (gG.extension (C.embedding.point s : ℝ)) := by
        dsimp only [raw]
        rw [C.point_agrees s hsTop]
      _ = C.coordExtension (G (C.embedding.point s) : ℝ) := by
        exact congrArg C.coordExtension (gG.agrees hsGDomain).symm
      _ = C.embedding.coord (G (C.embedding.point s)) :=
        C.coord_agrees _ hGMem
  have hrawAdd : ∀ s < (a : ℝ) + 1,
      raw (s + 1) = raw s + 1 := by
    intro s hs
    have hs1 : s + 1 < (a : ℝ) + 2 := by linarith
    have hs0 : s < (a : ℝ) + 2 := hs.trans (by linarith)
    obtain ⟨hGsRF, hraws⟩ := hphysical s hs0
    obtain ⟨hGs1RF, hraws1⟩ := hphysical (s + 1) hs1
    have hGsMem : G (C.embedding.point s) ∈
        Set.Ioo p C.embedding.rightEnd :=
      ⟨hGsRF.1, hGsRF.2.trans hrFMem.2⟩
    have hGs1Mem : G (C.embedding.point (s + 1)) ∈
        Set.Ioo p C.embedding.rightEnd :=
      ⟨hGs1RF.1, hGs1RF.2.trans hrFMem.2⟩
    have hsTail : s < C.fAction.tailBound := by linarith
    have hsTop : s < C.embedding.top :=
      hsTail.trans C.fAction.tailBound_lt_top
    have hfStepMem := C.fAction.image_mem s hsTail
    have hfStepCoord := C.fAction.intertwines s hsTail
    rw [C.f_translation s] at hfStepCoord
    have hpointStep : C.embedding.point (s + 1) =
        f (C.embedding.point s) := by
      rw [← hfStepCoord]
      exact C.embedding.point_coord _ hfStepMem
    have hsLtQ : C.embedding.point s < q := by
      apply C.embedding.point_lt_of_lt_coord hqMem
      linarith
    have hsComm : C.embedding.point s ∈ Set.Icc p qComm := by
      constructor
      · exact (C.embedding.point_mem s hsTop).1.le
      · change (C.embedding.point s : ℝ) ≤ (qComm : ℝ)
        exact hsLtQ.le.trans hqComm.le
    have hcommAt := hcomm hsComm
    have hrawTail : raw s < C.fAction.tailBound := by
      rw [hraws]
      have hrFCoord : C.embedding.coord rF = C.fAction.tailBound :=
        C.embedding.coord_point _ C.fAction.tailBound_lt_top
      rw [← hrFCoord]
      exact C.embedding.coord_strictMono hGsMem hrFMem hGsRF.2
    have hfGRaw := C.fAction.intertwines (raw s) hrawTail
    rw [C.f_translation (raw s)] at hfGRaw
    calc
      raw (s + 1) =
          C.embedding.coord (G (C.embedding.point (s + 1))) := hraws1
      _ = C.embedding.coord (G (f (C.embedding.point s))) := by
        rw [hpointStep]
      _ = C.embedding.coord (f (G (C.embedding.point s))) := by
        exact congrArg C.embedding.coord hcommAt.symm
      _ = raw s + 1 := by
        have hpointG : C.embedding.point (raw s) =
            G (C.embedding.point s) := by
          rw [hraws]
          exact C.embedding.point_coord _ hGsMem
        simpa [hpointG] using hfGRaw
  let S : Set ℝ := Set.Iio ((a : ℝ) + 2)
  have hS_pointDomain : S ⊆ Set.Iio C.embedding.top := by
    intro s hs
    change s < (a : ℝ) + 2 at hs
    change s < C.embedding.top
    exact hs.trans ((show (a : ℝ) + 2 < C.fAction.tailBound by
      linarith).trans C.fAction.tailBound_lt_top)
  have hpointMaps : Set.MapsTo C.pointExtension S gG.neighborhood := by
    intro s hs
    have hsTop : s < C.embedding.top := hS_pointDomain hs
    have hsCoord : s < C.embedding.coord q := by
      change s < (a : ℝ) + 2 at hs
      linarith
    have hsMem := C.embedding.point_mem s hsTop
    have hsLtQ := C.embedding.point_lt_of_lt_coord hqMem hsCoord
    rw [C.point_agrees s hsTop]
    apply gG.segment_subset
    constructor
    · exact hsMem.1.le
    · change (C.embedding.point s : ℝ) ≤ (gG.rightEnd : ℝ)
      have hsLtQReal : (C.embedding.point s : ℝ) < qReal := hsLtQ
      exact (hsLtQReal.le.trans hqMap.le).trans hqMapG.le
  have hcompMaps : Set.MapsTo
      (gG.extension ∘ C.pointExtension) S
      (Set.Ioo (p : ℝ) (C.embedding.rightEnd : ℝ)) := by
    intro s hs
    have hsTop : s < C.embedding.top := hS_pointDomain hs
    have hsCoord : s < C.embedding.coord q := by
      change s < (a : ℝ) + 2 at hs
      linarith
    have hsMem := C.embedding.point_mem s hsTop
    have hsLtQ := C.embedding.point_lt_of_lt_coord hqMem hsCoord
    have hsGDomain : C.embedding.point s ∈ Set.Icc p gG.rightEnd := by
      constructor
      · exact hsMem.1.le
      · change (C.embedding.point s : ℝ) ≤ (gG.rightEnd : ℝ)
        have hsLtQReal : (C.embedding.point s : ℝ) < qReal := hsLtQ
        exact (hsLtQReal.le.trans hqMap.le).trans hqMapG.le
    have hphys := hphysical s hs
    change gG.extension (C.pointExtension s) ∈
      Set.Ioo (p : ℝ) (C.embedding.rightEnd : ℝ)
    have hExtEq : gG.extension (C.pointExtension s) =
        (G (C.embedding.point s) : ℝ) := by
      rw [C.point_agrees s hsTop]
      exact (gG.agrees hsGDomain).symm
    rw [hExtEq]
    exact ⟨hphys.1.1, hphys.1.2.trans hrFMem.2⟩
  have hrawC1 : ContDiffOn ℝ 1 raw S := by
    have hpointC1 : ContDiffOn ℝ 1 C.pointExtension S :=
      C.point_contDiff.mono hS_pointDomain
    have hgPointC1 : ContDiffOn ℝ 1
        (gG.extension ∘ C.pointExtension) S :=
      gG.contDiff_one.comp hpointC1 hpointMaps
    have hcomp := C.coord_contDiff.comp hgPointC1 hcompMaps
    simpa only [raw, Function.comp_apply, Function.comp_def] using hcomp
  have hrawDeriv : ∀ s ∈ S,
      deriv raw s =
        deriv C.coordExtension (gG.extension (C.pointExtension s)) *
          (deriv gG.extension (C.pointExtension s) *
            deriv C.pointExtension s) := by
    intro s hs
    have hsTop : s < C.embedding.top := hS_pointDomain hs
    have hpointAt : ContDiffAt ℝ 1 C.pointExtension s :=
      C.point_contDiff.contDiffAt (isOpen_Iio.mem_nhds hsTop)
    have hgAt : ContDiffAt ℝ 1 gG.extension (C.pointExtension s) :=
      gG.contDiff_one.contDiffAt
        (gG.isOpen_neighborhood.mem_nhds (hpointMaps hs))
    have hcoordAt : ContDiffAt ℝ 1 C.coordExtension
        (gG.extension (C.pointExtension s)) :=
      C.coord_contDiff.contDiffAt
        (isOpen_Ioo.mem_nhds (hcompMaps hs))
    have hchain := hcoordAt.differentiableAt_one.hasDerivAt.comp s
      (hgAt.differentiableAt_one.hasDerivAt.comp s
        hpointAt.differentiableAt_one.hasDerivAt)
    simpa only [raw, Function.comp_apply, Function.comp_def] using hchain.deriv
  have hrawPos : ∀ s ∈ S, 0 < deriv raw s := by
    intro s hs
    rw [hrawDeriv s hs]
    have hsTop : s < C.embedding.top := hS_pointDomain hs
    have hsPoint : C.pointExtension s =
        (C.embedding.point s : ℝ) := C.point_agrees s hsTop
    have hsCoord : s < C.embedding.coord q := by
      change s < (a : ℝ) + 2 at hs
      linarith
    have hsMem := C.embedding.point_mem s hsTop
    have hsLtQ := C.embedding.point_lt_of_lt_coord hqMem hsCoord
    have hsGDomain : C.pointExtension s ∈
        Set.Icc (p : ℝ) (gG.rightEnd : ℝ) := by
      rw [hsPoint]
      constructor
      · exact hsMem.1.le
      · change (C.embedding.point s : ℝ) ≤ (gG.rightEnd : ℝ)
        have hsLtQReal : (C.embedding.point s : ℝ) < qReal := hsLtQ
        exact (hsLtQReal.le.trans hqMap.le).trans hqMapG.le
    exact mul_pos (C.coord_deriv_pos _ (hcompMaps hs))
      (mul_pos (gG.deriv_pos _ hsGDomain) (C.point_deriv_pos s hsTop))
  have hrawSeam : deriv raw ((a : ℝ) + 1) = deriv raw (a : ℝ) := by
    have haS : (a : ℝ) ∈ S := by
      change (a : ℝ) < (a : ℝ) + 2
      linarith
    have ha1S : (a : ℝ) + 1 ∈ S := by
      change (a : ℝ) + 1 < (a : ℝ) + 2
      linarith
    have hrawDiffA : DifferentiableAt ℝ raw (a : ℝ) :=
      (hrawC1.contDiffAt (isOpen_Iio.mem_nhds haS)).differentiableAt_one
    have hrawDiffA1 : DifferentiableAt ℝ raw ((a : ℝ) + 1) :=
      (hrawC1.contDiffAt (isOpen_Iio.mem_nhds ha1S)).differentiableAt_one
    have hevent : (fun s : ℝ => raw (s + 1)) =ᶠ[nhds (a : ℝ)]
        (fun s : ℝ => raw s + 1) := by
      filter_upwards [Iio_mem_nhds (show (a : ℝ) < (a : ℝ) + 1 by linarith)]
        with s hs
      exact hrawAdd s hs
    have hleft : deriv (fun s : ℝ => raw (s + 1)) (a : ℝ) =
        deriv raw ((a : ℝ) + 1) := by
      simpa using (hrawDiffA1.hasDerivAt.comp (a : ℝ)
        ((hasDerivAt_id (a : ℝ)).add_const 1)).deriv
    have hright : deriv (fun s : ℝ => raw s + 1) (a : ℝ) =
        deriv raw (a : ℝ) := by
      simpa using (hrawDiffA.hasDerivAt.add_const 1).deriv
    rw [← hleft, hevent.deriv_eq, hright]
  let J : Set ℝ := Set.Icc (a : ℝ) ((a : ℝ) + 1)
  have hJ_S : J ⊆ S := by
    intro s hs
    change s < (a : ℝ) + 2
    exact hs.2.trans_lt (by linarith)
  have hpointSegment : Set.MapsTo C.pointExtension J
      (Set.Icc (p : ℝ) (gG.rightEnd : ℝ)) := by
    intro s hs
    have hsS := hJ_S hs
    have hsTop := hS_pointDomain hsS
    have hsCoord : s < C.embedding.coord q := by
      have hsUpper : s ≤ (a : ℝ) + 1 := hs.2
      linarith
    have hsMem := C.embedding.point_mem s hsTop
    have hsLtQ := C.embedding.point_lt_of_lt_coord hqMem hsCoord
    rw [C.point_agrees s hsTop]
    constructor
    · exact hsMem.1.le
    · change (C.embedding.point s : ℝ) ≤ (gG.rightEnd : ℝ)
      have hsLtQReal : (C.embedding.point s : ℝ) < qReal := hsLtQ
      exact (hsLtQReal.le.trans hqMap.le).trans hqMapG.le
  have hpointMonotone : MonotoneOn C.pointExtension J := by
    have hcont : ContinuousOn C.pointExtension J :=
      C.point_contDiff.continuousOn.mono
        (fun s hs => hS_pointDomain (hJ_S hs))
    have hstrict : StrictMonoOn C.pointExtension J := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
      intro s hs
      exact C.point_deriv_pos s
        (hS_pointDomain (hJ_S (interior_subset hs)))
    exact hstrict.monotoneOn
  have hgSegmentStrict : StrictMonoOn gG.extension
      (Set.Icc (p : ℝ) (gG.rightEnd : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (gG.contDiff_one.continuousOn.mono gG.segment_subset)
    intro x hx
    exact gG.deriv_pos x (interior_subset hx)
  have hcompMonotone : MonotoneOn
      (gG.extension ∘ C.pointExtension) J := by
    intro x hx y hy hxy
    exact hgSegmentStrict.monotoneOn
      (hpointSegment hx) (hpointSegment hy)
      (hpointMonotone hx hy hxy)
  have hcompEndpointMaps : Set.MapsTo
      (gG.extension ∘ C.pointExtension) J
      (Set.Icc
        (gG.extension (C.pointExtension (a : ℝ)))
        (gG.extension (C.pointExtension ((a : ℝ) + 1)))) := by
    intro s hs
    constructor
    · exact hcompMonotone (by
        change (a : ℝ) ∈ J
        exact ⟨le_rfl, by linarith⟩) hs hs.1
    · exact hcompMonotone hs (by
        change (a : ℝ) + 1 ∈ J
        exact ⟨by linarith, le_rfl⟩) hs.2
  have hcoordCompBV : BoundedVariationOn
      ((fun x : ℝ => Real.log (deriv C.coordExtension x)) ∘
        (gG.extension ∘ C.pointExtension)) J := by
    have hleftMem := hcompMaps (hJ_S (show (a : ℝ) ∈ J by
      exact ⟨le_rfl, by linarith⟩))
    have hrightMem := hcompMaps (hJ_S (show (a : ℝ) + 1 ∈ J by
      exact ⟨by linarith, le_rfl⟩))
    have hsource := C.coord_logDeriv_bv
      (gG.extension (C.pointExtension (a : ℝ)))
      (gG.extension (C.pointExtension ((a : ℝ) + 1)))
      hleftMem.1 hrightMem.2
      (hcompMonotone (show (a : ℝ) ∈ J by
        exact ⟨le_rfl, by linarith⟩)
        (show (a : ℝ) + 1 ∈ J by exact ⟨by linarith, le_rfl⟩)
        (by linarith))
    apply ne_top_of_le_ne_top hsource
    exact eVariationOn.comp_le_of_monotoneOn
      (fun x : ℝ => Real.log (deriv C.coordExtension x))
      (gG.extension ∘ C.pointExtension) hcompMonotone hcompEndpointMaps
  have hgCompBV : BoundedVariationOn
      ((fun x : ℝ => Real.log (deriv gG.extension x)) ∘
        C.pointExtension) J := by
    change BoundedVariationOn
      (fun x : ℝ => Real.log (deriv gG.extension x))
      (Set.Icc (p : ℝ) (gG.rightEnd : ℝ)) at hgGBV
    apply ne_top_of_le_ne_top hgGBV
    exact eVariationOn.comp_le_of_monotoneOn
      (fun x : ℝ => Real.log (deriv gG.extension x))
      C.pointExtension hpointMonotone hpointSegment
  have hpointBV : BoundedVariationOn
      (fun s : ℝ => Real.log (deriv C.pointExtension s)) J := by
    apply C.point_logDeriv_bv (a : ℝ) ((a : ℝ) + 1)
    · exact (show (a : ℝ) + 1 < C.fAction.tailBound by
        linarith).trans C.fAction.tailBound_lt_top
    · linarith
  have hrawLogFormula : Set.EqOn
      (fun s : ℝ => Real.log (deriv raw s))
      (fun s : ℝ =>
        Real.log (deriv C.coordExtension
          (gG.extension (C.pointExtension s))) +
        Real.log (deriv gG.extension (C.pointExtension s)) +
        Real.log (deriv C.pointExtension s)) J := by
    intro s hs
    change Real.log (deriv raw s) =
      Real.log (deriv C.coordExtension
        (gG.extension (C.pointExtension s))) +
      Real.log (deriv gG.extension (C.pointExtension s)) +
      Real.log (deriv C.pointExtension s)
    rw [hrawDeriv s (hJ_S hs)]
    have hcoordPos := C.coord_deriv_pos _ (hcompMaps (hJ_S hs))
    have hcoordPos' : 0 < deriv C.coordExtension
        (gG.extension (C.pointExtension s)) := by
      simpa only [Function.comp_apply] using hcoordPos
    have hgPos := gG.deriv_pos _ (hpointSegment hs)
    have hpointPos := C.point_deriv_pos s
      (hS_pointDomain (hJ_S hs))
    rw [Real.log_mul hcoordPos'.ne' (mul_pos hgPos hpointPos).ne',
      Real.log_mul hgPos.ne' hpointPos.ne']
    ring
  have hrawLogBV : BoundedVariationOn
      (fun s : ℝ => Real.log (deriv raw s)) J := by
    have hsum := boundedVariationOn_add
      (boundedVariationOn_add hcoordCompBV hgCompBV) hpointBV
    unfold BoundedVariationOn at hsum ⊢
    rw [eVariationOn.eq_of_eqOn hrawLogFormula]
    simpa only [Function.comp_apply, Function.comp_def, add_assoc] using hsum
  let shift : ℝ → ℝ := fun t => (a : ℝ) + t
  let g0 : ℝ → ℝ := fun t => raw (shift t) - (a : ℝ)
  let U0 : Set ℝ := Set.Iio 2
  have hshiftMapsS : Set.MapsTo shift U0 S := by
    intro t ht
    change t < (2 : ℝ) at ht
    change (a : ℝ) + t < (a : ℝ) + 2
    linarith
  have hg0C1 : ContDiffOn ℝ 1 g0 U0 := by
    have hshiftC1 : ContDiff ℝ 1 shift := by
      simpa only [shift] using (contDiff_const.add contDiff_id)
    have hcomp : ContDiffOn ℝ 1 (raw ∘ shift) U0 :=
      hrawC1.comp hshiftC1.contDiffOn hshiftMapsS
    have hsub := hcomp.sub (contDiff_const.contDiffOn :
      ContDiffOn ℝ 1 (fun _ : ℝ => (a : ℝ)) U0)
    simpa only [g0, Function.comp_apply, Function.comp_def] using hsub
  have hg0Deriv : ∀ t ∈ U0,
      deriv g0 t = deriv raw ((a : ℝ) + t) := by
    intro t ht
    have hrawAt : DifferentiableAt ℝ raw (shift t) :=
      (hrawC1.contDiffAt
        (isOpen_Iio.mem_nhds (hshiftMapsS ht))).differentiableAt_one
    have hshiftDeriv : HasDerivAt shift 1 t := by
      simpa only [shift, zero_add] using
        ((hasDerivAt_const t (a : ℝ)).add (hasDerivAt_id t))
    have h := (hrawAt.hasDerivAt.comp t hshiftDeriv).sub_const (a : ℝ)
    simpa only [g0, shift, Function.comp_apply, Function.comp_def,
      one_mul, mul_one] using h.deriv
  have hIccU0 : Set.Icc (0 : ℝ) 1 ⊆ U0 := by
    intro t ht
    change t < (2 : ℝ)
    linarith [ht.2]
  have hg0Pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < deriv g0 t := by
    intro t ht
    rw [hg0Deriv t (hIccU0 ht)]
    exact hrawPos _ (hshiftMapsS (hIccU0 ht))
  have hg0Value : g0 1 = g0 0 + 1 := by
    have hstep := hrawAdd (a : ℝ) (by linarith)
    dsimp only [g0, shift]
    norm_num at hstep ⊢
    linarith
  have hg0Seam : deriv g0 1 = deriv g0 0 := by
    rw [hg0Deriv 1 (hIccU0 (by norm_num)),
      hg0Deriv 0 (hIccU0 (by norm_num))]
    norm_num
    exact hrawSeam
  have hshiftMonotone : MonotoneOn shift (Set.Icc (0 : ℝ) 1) := by
    intro x _hx y _hy hxy
    dsimp only [shift]
    linarith
  have hshiftMapsJ : Set.MapsTo shift (Set.Icc (0 : ℝ) 1) J := by
    intro t ht
    change (a : ℝ) ≤ (a : ℝ) + t ∧
      (a : ℝ) + t ≤ (a : ℝ) + 1
    constructor <;> linarith [ht.1, ht.2]
  have hg0LogFormula : Set.EqOn
      (fun t : ℝ => Real.log (deriv g0 t))
      ((fun s : ℝ => Real.log (deriv raw s)) ∘ shift)
      (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    change Real.log (deriv g0 t) =
      Real.log (deriv raw (shift t))
    rw [hg0Deriv t (hIccU0 ht)]
  have hg0BV : BoundedVariationOn
      (fun t : ℝ => Real.log (deriv g0 t))
      (Set.Icc (0 : ℝ) 1) := by
    have hcompBV : BoundedVariationOn
        ((fun s : ℝ => Real.log (deriv raw s)) ∘ shift)
        (Set.Icc (0 : ℝ) 1) := by
      apply ne_top_of_le_ne_top hrawLogBV
      exact eVariationOn.comp_le_of_monotoneOn
        (fun s : ℝ => Real.log (deriv raw s)) shift
        hshiftMonotone hshiftMapsJ
    unfold BoundedVariationOn at hcompBV ⊢
    rw [eVariationOn.eq_of_eqOn hg0LogFormula]
    exact hcompBV
  obtain ⟨lift, hliftRegular, hliftEq⟩ :=
    exists_regularCircleLift_of_fundamentalInterval g0 hg0C1
      isOpen_Iio hIccU0 hg0Pos hg0Value hg0Seam hg0BV
  have hbase : Set.EqOn (circleLiftFun lift) raw
      (Set.Ico (a : ℝ) ((a : ℝ) + 1)) := by
    intro s hs
    let t : ℝ := s - (a : ℝ)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp only [t]
      constructor <;> linarith [hs.1, hs.2.le]
    have heqt := hliftEq ht
    have heqt' : circleLiftFun lift t = raw s - (a : ℝ) := by
      calc
        circleLiftFun lift t = g0 t := heqt
        _ = raw s - (a : ℝ) := by
          dsimp only [g0, shift, t]
          congr 2
          ring
    have hmap := (lift : CircleDeg1Lift).map_add_int t a
    have hsDecomp : t + (a : ℝ) = s := by
      dsimp only [t]
      ring
    calc
      circleLiftFun lift s = circleLiftFun lift (t + (a : ℝ)) :=
        congrArg (circleLiftFun lift) hsDecomp.symm
      _ = circleLiftFun lift t + (a : ℝ) := by
        simpa only [circleLiftFun] using hmap
      _ = raw s := by rw [heqt']; ring
  have htailEq : ∀ s < (a : ℝ) + 1,
      circleLiftFun lift s = raw s :=
    circleDeg1Lift_eqOn_Iio_of_fundamentalInterval
      (lift : CircleDeg1Lift) raw (a : ℝ) hrawAdd hbase
  let GAction : RightGermLineLift C.embedding G :=
    { lift := lift
      tailBound := (a : ℝ) + 1
      tailBound_lt_top :=
        (show (a : ℝ) + 1 < C.fAction.tailBound by linarith).trans
          C.fAction.tailBound_lt_top
      image_mem := by
        intro s hs
        have hphys := hphysical s (by linarith)
        exact ⟨hphys.1.1, hphys.1.2.trans hrFMem.2⟩
      intertwines := by
        intro s hs
        have hphys := hphysical s (by linarith)
        calc
          C.embedding.coord (G (C.embedding.point s)) = raw s := hphys.2.symm
          _ = circleLiftFun lift s := (htailEq s hs).symm }
  exact ⟨GAction, hliftRegular⟩

/-! ## Construction of the orbit line -/

/-- The actual direct-limit construction, separated from all relation
bookkeeping.  A repelling `C^{1+BV}` germ supplies a normalized line
coordinate; any two fixed `C^{1+BV}` germs commuting with it extend to
regular selected degree-one lifts in that same coordinate. -/
private theorem exists_normalizedOrbitLine_regular_pair
    {f A B : IntervalMap} {p : I}
    (hf_fixed : IsFixedPoint f p)
    (hA_fixed : IsFixedPoint A p)
    (hB_fixed : IsFixedPoint B p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p)
    (hA_regular : HasRightGermC1BV A p)
    (hB_regular : HasRightGermC1BV B p)
    (hfA_commute : RightGermCommute p f A)
    (hfB_commute : RightGermCommute p f B) :
    ∃ E : RightOrbitLineEmbedding p,
      ∃ fAction : RightGermLineLift E f,
      ∃ AAction : RightGermLineLift E A,
      ∃ BAction : RightGermLineLift E B,
        (∀ s : ℝ, circleLiftFun fAction.lift s = s + 1) ∧
        IsC1BVUnitLift AAction.lift ∧
        IsC1BVUnitLift BAction.lift := by
  obtain ⟨C⟩ := exists_normalizedC1BVAbelCoordinate
    hf_fixed hf_repelling hf_regular
  obtain ⟨AAction, hA⟩ :=
    regularLineLift_of_normalizedC1BVAbelCoordinate
      C hA_fixed hA_regular hfA_commute
  obtain ⟨BAction, hB⟩ :=
    regularLineLift_of_normalizedC1BVAbelCoordinate
      C hB_fixed hB_regular hfB_commute
  exact ⟨C.embedding, C.fAction, AAction, BAction,
    C.f_translation, hA, hB⟩

/--
The direct-limit orbit-line claim from the manuscript, with every physical
germ hypothesis exposed.  Pairwise commutation is required only as germ
equality, and the product relation is likewise a germ relation.
-/
theorem exists_oneSidedOrbitLineModel
    {f A B : IntervalMap} {p : I} {d : ℕ}
    (hd : 0 < d)
    (hf_fixed : IsFixedPoint f p)
    (hA_fixed : IsFixedPoint A p)
    (hB_fixed : IsFixedPoint B p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p)
    (hA_regular : HasRightGermC1BV A p)
    (hB_regular : HasRightGermC1BV B p)
    (hfA_commute : RightGermCommute p f A)
    (hfB_commute : RightGermCommute p f B)
    (hAB_commute : RightGermCommute p A B)
    (hproduct : SameOneSidedGermAt .right p (A ∘ B) (iterateMap f d)) :
    Nonempty (OneSidedOrbitLineModel f A B p d) := by
  obtain ⟨E, fAction, AAction, BAction, hfdeck, hAreg, hBreg⟩ :=
    exists_normalizedOrbitLine_regular_pair hf_fixed hA_fixed hB_fixed
      hf_repelling hf_regular hA_regular hB_regular hfA_commute hfB_commute
  have hABlifts : AAction.lift * BAction.lift =
      BAction.lift * AAction.lift :=
    lineLift_mul_eq_mul_of_sameRightGerm_comp
      AAction BAction BAction AAction hAB_commute
  have hproductLifts : AAction.lift * BAction.lift = fAction.lift ^ d :=
    lineLift_mul_eq_pow_of_sameRightGerm_comp
      AAction BAction fAction d hproduct
  refine ⟨{
    embedding := E
    fAction := fAction
    AAction := AAction
    BAction := BAction
    f_is_unit_translation := hfdeck
    A_B_commute := ?_
    A_B_product := ?_
    regular_A := hAreg
    regular_B := hBreg }⟩
  · intro s
    have hs := congrArg
      (fun U : CircleHomeomorphismLift => circleLiftFun U s) hABlifts
    simpa [circleLiftFun, CircleDeg1Lift.mul_apply] using hs
  · intro s
    have hs := congrArg
      (fun U : CircleHomeomorphismLift => circleLiftFun U s) hproductLifts
    have hpow := circleLift_pow_apply_of_unitTranslation
      fAction.lift hfdeck d s
    simpa [circleLiftFun, CircleDeg1Lift.mul_apply, hpow] using hs

/-! ## Rational and irrational conclusions -/

/-- The exact rational-power conclusion, including possibly negative powers
of the repelling germ through `SameAsSignedRightGermIterateAt`. -/
def RationalOrbitAlternative
    (f A B : IntervalMap) (p : I) (d : ℕ) (α : ℝ) : Prop :=
  ∃ m : ℤ, ∃ n : ℕ, 0 < n ∧
    α = (m : ℝ) / (n : ℝ) ∧
    SameAsSignedRightGermIterateAt p (iterateMap A n) f m ∧
    SameAsSignedRightGermIterateAt p (iterateMap B n) f
      (((d * n : ℕ) : ℤ) - m)

/--
The simultaneous far-left translation chart supplied by the irrational
branch.  All three identities use the same physical coordinate and the exact
selected phases `α` and `d - α`.
-/
structure RightTranslationChart
    (f A B : IntervalMap) (p : I) (d : ℕ) (α : ℝ) where
  /-- Ordered orbit-line coordinate. -/
  embedding : RightOrbitLineEmbedding p
  /-- All three identities hold below this common cutoff. -/
  tailBound : ℝ
  /-- The cutoff lies in the negative half-line. -/
  tailBound_lt_top : tailBound < embedding.top
  /-- The `f`-image stays inside the physical representative. -/
  f_image_mem : ∀ s < tailBound,
    f (embedding.point s) ∈ Set.Ioo p embedding.rightEnd
  /-- The `A`-image stays inside the same physical representative. -/
  A_image_mem : ∀ s < tailBound,
    A (embedding.point s) ∈ Set.Ioo p embedding.rightEnd
  /-- The `B`-image stays inside the same physical representative. -/
  B_image_mem : ∀ s < tailBound,
    B (embedding.point s) ∈ Set.Ioo p embedding.rightEnd
  /-- The repelling germ becomes translation by one. -/
  f_translation : ∀ s < tailBound,
    embedding.coord (f (embedding.point s)) = s + 1
  /-- `A` becomes translation by its selected translation number. -/
  A_translation : ∀ s < tailBound,
    embedding.coord (A (embedding.point s)) = s + α
  /-- `B` becomes the complementary translation. -/
  B_translation : ∀ s < tailBound,
    embedding.coord (B (embedding.point s)) = s + (d - α)

/-- The irrational conclusion, including irrationality itself rather than
only the negation of one chosen rational representation. -/
def IrrationalOrbitAlternative
    (f A B : IntervalMap) (p : I) (d : ℕ) (α : ℝ) : Prop :=
  Irrational α ∧ Nonempty (RightTranslationChart f A B p d α)

/-- A non-irrational real number in the integer-over-positive-natural form
used by the signed germ-power alternative. -/
theorem rational_representation_of_not_irrational
    {alpha : ℝ} (h : ¬ Irrational alpha) :
    ∃ m : ℤ, ∃ n : ℕ, 0 < n ∧ alpha = (m : ℝ) / (n : ℝ) := by
  obtain ⟨q, rfl⟩ := exists_rat_of_not_irrational h
  refine ⟨q.num, q.den, q.den_pos, ?_⟩
  exact Rat.cast_def q

/-- A rational-translation lift intersection can be shifted, by an integer,
so that the entire finite orbit segment lies below any prescribed physical
tail cutoff. -/
private theorem rationalLift_intersection_farLeft
    (F : CircleHomeomorphismLift) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (htranslation : selectedTranslationNumber F =
      (m : ℝ) / (n : ℝ)) (bound : ℝ) :
    ∃ t : ℝ,
      (∀ i : ℕ, i ≤ n → ((F : CircleDeg1Lift) ^ i) t < bound) ∧
      ((F : CircleDeg1Lift) ^ n) t = t + (m : ℝ) := by
  have hcont : Continuous (F : CircleDeg1Lift) := by
    simpa using (CircleDeg1Lift.toOrderIso F).continuous
  have htranslation' : (F : CircleDeg1Lift).translationNumber =
      (m : ℝ) / (n : ℝ) := htranslation
  obtain ⟨s, hs⟩ :=
    ((F : CircleDeg1Lift).translationNumber_eq_rat_iff hcont hn).mp
      htranslation'
  let orbitBound : ℝ :=
    ∑ i ∈ Finset.range (n + 1), |((F : CircleDeg1Lift) ^ i) s|
  obtain ⟨k : ℤ, hk⟩ := exists_int_lt (bound - orbitBound)
  let t : ℝ := s + (k : ℝ)
  refine ⟨t, ?_, ?_⟩
  · intro i hi
    have hirange : i ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (by omega)
    have habs : |((F : CircleDeg1Lift) ^ i) s| ≤ orbitBound := by
      dsimp [orbitBound]
      exact Finset.single_le_sum
        (fun j _hj ↦ abs_nonneg (((F : CircleDeg1Lift) ^ j) s)) hirange
    have hvalue : ((F : CircleDeg1Lift) ^ i) t =
        ((F : CircleDeg1Lift) ^ i) s + (k : ℝ) := by
      simpa [t] using
        (((F : CircleDeg1Lift) ^ i).map_add_int s k)
    rw [hvalue]
    have hleabs : ((F : CircleDeg1Lift) ^ i) s ≤
        |((F : CircleDeg1Lift) ^ i) s| := le_abs_self _
    linarith
  · have hshift : ((F : CircleDeg1Lift) ^ n) t =
        ((F : CircleDeg1Lift) ^ n) s + (k : ℝ) := by
      simpa [t] using
        (((F : CircleDeg1Lift) ^ n).map_add_int s k)
    rw [hshift, hs]
    simp [t, add_assoc, add_left_comm, add_comm]

/-- The rational lift intersection transported to the physical tail.  For a
nonnegative numerator the two positive iterates meet; for a negative
numerator, applying the corresponding positive deck iterate to the `G`-image
returns to the starting point. -/
private theorem rationalTranslation_physical_power_relation
    {f G : IntervalMap} {p : I} (E : RightOrbitLineEmbedding p)
    (fAction : RightGermLineLift E f)
    (GAction : RightGermLineLift E G)
    (hf_deck : ∀ s : ℝ, circleLiftFun fAction.lift s = s + 1)
    {m : ℤ} {n : ℕ} (hn : 0 < n)
    (htranslation : selectedTranslationNumber GAction.lift =
      (m : ℝ) / (n : ℝ)) (cutoff : ℝ) :
    ∃ t : ℝ,
      let x := E.point t
      x ∈ Set.Ioo p E.rightEnd ∧
      iterateMap G n x ∈ Set.Ioo p E.rightEnd ∧
      E.coord x < cutoff ∧
      E.coord (iterateMap G n x) < cutoff ∧
      if 0 ≤ m then
        iterateMap G n x = iterateMap f m.toNat x
      else
        iterateMap f m.natAbs (iterateMap G n x) = x := by
  let bound : ℝ :=
    min (min fAction.tailBound GAction.tailBound) cutoff
  obtain ⟨t, hGorbit, hGendpoint⟩ :=
    rationalLift_intersection_farLeft GAction.lift hn htranslation bound
  have htG : t < GAction.tailBound :=
    (hGorbit 0 (by omega)).trans_le
      ((min_le_left _ _).trans (min_le_right _ _))
  have htF : t < fAction.tailBound :=
    (hGorbit 0 (by omega)).trans_le
      ((min_le_left _ _).trans (min_le_left _ _))
  have htTop : t < E.top := htG.trans GAction.tailBound_lt_top
  have hxmem : E.point t ∈ Set.Ioo p E.rightEnd := E.point_mem t htTop
  have hGorbitTail : ∀ i : ℕ, i ≤ n →
      (((GAction.lift : CircleDeg1Lift) ^ i) t) <
        GAction.tailBound := by
    intro i hi
    exact (hGorbit i hi).trans_le
      ((min_le_left _ _).trans (min_le_right _ _))
  have hGphysical := GAction.iterate_intertwines hGorbitTail
  have htCutoff : t < cutoff :=
    (hGorbit 0 (by omega)).trans_le (min_le_right _ _)
  have hxCutoff : E.coord (E.point t) < cutoff := by
    rw [E.coord_point t htTop]
    exact htCutoff
  have hGcutoff : E.coord (iterateMap G n (E.point t)) < cutoff := by
    rw [hGphysical.2]
    exact (hGorbit n le_rfl).trans_le (min_le_right _ _)
  refine ⟨t, hxmem, hGphysical.1, hxCutoff, hGcutoff, ?_⟩
  by_cases hm : 0 ≤ m
  · simp only [if_pos hm]
    have hmcast : (m.toNat : ℝ) = (m : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hm
    have hGendF : t + (m : ℝ) < fAction.tailBound := by
      rw [← hGendpoint]
      exact (hGorbit n le_rfl).trans_le
        ((min_le_left _ _).trans (min_le_left _ _))
    have hfOrbit : ∀ i : ℕ, i ≤ m.toNat →
        (((fAction.lift : CircleDeg1Lift) ^ i) t) <
          fAction.tailBound := by
      intro i hi
      rw [circleLift_pow_apply_of_unitTranslation fAction.lift hf_deck]
      have hicast : (i : ℝ) ≤ (m.toNat : ℝ) := by exact_mod_cast hi
      rw [hmcast] at hicast
      linarith
    have hfPhysical := fAction.iterate_intertwines hfOrbit
    apply E.coord_strictMono.injOn hGphysical.1 hfPhysical.1
    calc
      E.coord (iterateMap G n (E.point t)) =
          ((GAction.lift : CircleDeg1Lift) ^ n) t := hGphysical.2
      _ = t + (m : ℝ) := hGendpoint
      _ = t + (m.toNat : ℝ) := by rw [hmcast]
      _ = ((fAction.lift : CircleDeg1Lift) ^ m.toNat) t :=
        (circleLift_pow_apply_of_unitTranslation
          fAction.lift hf_deck m.toNat t).symm
      _ = E.coord (iterateMap f m.toNat (E.point t)) := hfPhysical.2.symm
  · simp only [if_neg hm]
    have hmneg : m < 0 := lt_of_not_ge hm
    have hmcast : (m : ℝ) = -(m.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_neg (by exact_mod_cast hmneg)]
      simp
    have hcoordG : E.coord (iterateMap G n (E.point t)) =
        t + (m : ℝ) := hGphysical.2.trans hGendpoint
    have hpointG : E.point (t + (m : ℝ)) =
        iterateMap G n (E.point t) := by
      rw [← hcoordG]
      exact E.point_coord _ hGphysical.1
    have hfOrbit : ∀ i : ℕ, i ≤ m.natAbs →
        (((fAction.lift : CircleDeg1Lift) ^ i) (t + (m : ℝ))) <
          fAction.tailBound := by
      intro i hi
      rw [circleLift_pow_apply_of_unitTranslation fAction.lift hf_deck]
      have hicast : (i : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast hi
      rw [hmcast]
      linarith
    have hfPhysical := fAction.iterate_intertwines hfOrbit
    rw [← hpointG]
    apply E.coord_strictMono.injOn hfPhysical.1 hxmem
    calc
      E.coord (iterateMap f m.natAbs (E.point (t + (m : ℝ)))) =
          ((fAction.lift : CircleDeg1Lift) ^ m.natAbs)
            (t + (m : ℝ)) := hfPhysical.2
      _ = (t + (m : ℝ)) + (m.natAbs : ℝ) :=
        circleLift_pow_apply_of_unitTranslation
          fAction.lift hf_deck m.natAbs _
      _ = t := by rw [hmcast]; ring
      _ = E.coord (E.point t) := (E.coord_point t htTop).symm

/-- Local signed-power rigidity in the form needed after the lift
intersection has been moved back to the interval.  The two points in each
intersection are required arbitrarily close to the base; this is the exact
localization needed to place the relative germ and all inverse-germ
bookkeeping inside common `C¹` representatives before invoking Kopell. -/
private theorem local_c1BV_signed_power_rigidity_of_intersections
    {f G : IntervalMap} {p : I}
    (hf_fixed : IsFixedPoint f p)
    (hG_fixed : IsFixedPoint G p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p)
    (hG_regular : HasRightGermC1BV G p)
    (hfG_commute : RightGermCommute p f G)
    {m : ℤ} {n : ℕ}
    (hintersections : ∀ q : I, p < q → ∃ x : I,
      x ∈ Set.Ioc p q ∧
      iterateMap G n x ∈ Set.Ioc p q ∧
      if 0 ≤ m then
        iterateMap G n x = iterateMap f m.toNat x
      else
        iterateMap f m.natAbs (iterateMap G n x) = x) :
    SameAsSignedRightGermIterateAt p (iterateMap G n) f m := by
  rcases hf_regular with ⟨gf, hgfBV⟩
  rcases hG_regular with ⟨gG, _hGgBV⟩
  obtain ⟨fInv, hfInv_fixed, hInverse, ⟨gInv⟩⟩ :=
    exists_c1_rightGerm_inverse hf_fixed gf
  have iterateFixed (T : IntervalMap) (hT : IsFixedPoint T p) :
      ∀ k : ℕ, IsFixedPoint (iterateMap T k) p := by
    intro k
    induction k with
    | zero => simp [IsFixedPoint, iterateMap]
    | succ k hk =>
        simp only [IsFixedPoint, iterateMap,
          Function.iterate_succ_apply'] at hk ⊢
        rw [hk, hT]
  have hHfixed : IsFixedPoint (iterateMap G n) p :=
    iterateFixed G hG_fixed n
  rcases hasRightGermC1Diffeomorphism_iterate hG_fixed gG n with ⟨gH⟩
  have havailable : ∃ q : I, p < q :=
    ⟨gf.rightEnd, gf.base_lt_rightEnd⟩
  have hftend : Tendsto f (𝓝[≥] p) (𝓝[≥] p) :=
    gf.tendsto_nhdsGE hf_fixed
  have hGtend : Tendsto G (𝓝[≥] p) (𝓝[≥] p) :=
    gG.tendsto_nhdsGE hG_fixed
  have hHtend : Tendsto (iterateMap G n) (𝓝[≥] p) (𝓝[≥] p) := by
    simpa [iterateMap] using hGtend.iterate n
  have hInvtend : Tendsto fInv (𝓝[≥] p) (𝓝[≥] p) :=
    gInv.tendsto_nhdsGE hfInv_fixed
  have hfGevent : (f ∘ G) =ᶠ[𝓝[≥] p] (G ∘ f) :=
    (sameRightGerm_iff_eventuallyEq havailable).1 hfG_commute
  have hHcommEvent :=
    rightEventuallyEq_commute_iterate hfGevent hGtend n
  have hInvLeftEvent :
      (f ∘ fInv) =ᶠ[𝓝[≥] p] identityIntervalMap :=
    (sameRightGerm_iff_eventuallyEq havailable).1 hInverse.1
  have hInvRightEvent :
      (fInv ∘ f) =ᶠ[𝓝[≥] p] identityIntervalMap :=
    (sameRightGerm_iff_eventuallyEq havailable).1 hInverse.2
  have hInvCommEvent :
      (f ∘ fInv) =ᶠ[𝓝[≥] p] (fInv ∘ f) :=
    hInvLeftEvent.trans hInvRightEvent.symm
  by_cases hm : 0 ≤ m
  · rw [SameAsSignedRightGermIterateAt, if_pos hm]
    let k : ℕ := m.toNat
    have hFPowFixed : IsFixedPoint (iterateMap f k) p :=
      iterateFixed f hf_fixed k
    have hInvPowFixed : IsFixedPoint (iterateMap fInv k) p :=
      iterateFixed fInv hfInv_fixed k
    rcases hasRightGermC1Diffeomorphism_iterate hf_fixed gf k with ⟨gFPow⟩
    rcases hasRightGermC1Diffeomorphism_iterate hfInv_fixed gInv k with
      ⟨gInvPow⟩
    let V : IntervalMap := iterateMap fInv k ∘ iterateMap G n
    have hVfixed : IsFixedPoint V p := by
      change iterateMap fInv k (iterateMap G n p) = p
      rw [hHfixed, hInvPowFixed]
    rcases hasRightGermC1Diffeomorphism_comp
        hInvPowFixed hHfixed gInvPow gH with ⟨gV⟩
    have hInvPowComm :=
      rightEventuallyEq_commute_iterate hInvCommEvent hInvtend k
    have hVcommEvent :
        (f ∘ V) =ᶠ[𝓝[≥] p] (V ∘ f) := by
      simpa [V] using
        rightEventuallyEq_commute_comp
          hInvPowComm hHcommEvent hHtend
    have hVcomm : RightGermCommute p f V :=
      (sameRightGerm_iff_eventuallyEq havailable).2 hVcommEvent
    have hInvAfterF :=
      rightEventuallyEq_inverse_iterates hInvRightEvent hftend k
    have hFAfterInv :=
      rightEventuallyEq_inverse_iterates hInvLeftEvent hInvtend k
    have hVfixedNear : ∀ q : I, p < q →
        ∃ x ∈ Set.Ioc p q, V x = x := by
      intro q hpq
      have hCancelSame : SameOneSidedGermAt .right p
          (iterateMap fInv k ∘ iterateMap f k) identityIntervalMap :=
        (sameRightGerm_iff_eventuallyEq havailable).2 hInvAfterF
      rcases hCancelSame with ⟨qcancel, hpqcancel, hcancelOn⟩
      let r : I := min q qcancel
      have hpr : p < r := by
        simp only [r, lt_min_iff]
        exact ⟨hpq, hpqcancel⟩
      obtain ⟨q', hpq', hq'r⟩ := exists_between hpr
      have hq'q : q' < q := hq'r.trans_le (min_le_left _ _)
      have hq'cancel : q' < qcancel :=
        hq'r.trans_le (min_le_right _ _)
      obtain ⟨x, hx, _hHx, hrelation⟩ :=
        hintersections q' hpq'
      simp only [if_pos hm] at hrelation
      refine ⟨x, ⟨hx.1, hx.2.trans hq'q.le⟩, ?_⟩
      change iterateMap fInv k (iterateMap G n x) = x
      rw [hrelation]
      simpa [identityIntervalMap, Function.comp_apply] using
        hcancelOn ⟨hx.1.le, hx.2.trans hq'cancel.le⟩
    have hVidentity :=
      local_c1BV_Kopell_identity_of_accumulating_fixedPoints
        gf gV hgfBV hf_fixed hVfixed hf_repelling hVcomm hVfixedNear
    have hVidentityEvent : V =ᶠ[𝓝[≥] p] identityIntervalMap :=
      (sameRightGerm_iff_eventuallyEq havailable).1 hVidentity
    have hCancelApplied := hFAfterInv.comp_tendsto hHtend
    have hIdentityApplied := hVidentityEvent.fun_comp (iterateMap f k)
    have hFinal : iterateMap G n =ᶠ[𝓝[≥] p] iterateMap f k := by
      filter_upwards [hCancelApplied, hIdentityApplied] with x hxCancel hxIdentity
      simp only [V, Function.comp_apply, identityIntervalMap] at hxCancel hxIdentity
      exact hxCancel.symm.trans hxIdentity
    simpa [k] using (sameRightGerm_iff_eventuallyEq havailable).2 hFinal
  · simp only [SameAsSignedRightGermIterateAt, if_neg hm]
    refine ⟨fInv, hInverse, ?_⟩
    let k : ℕ := m.natAbs
    have hFPowFixed : IsFixedPoint (iterateMap f k) p :=
      iterateFixed f hf_fixed k
    have hInvPowFixed : IsFixedPoint (iterateMap fInv k) p :=
      iterateFixed fInv hfInv_fixed k
    rcases hasRightGermC1Diffeomorphism_iterate hf_fixed gf k with ⟨gFPow⟩
    rcases hasRightGermC1Diffeomorphism_iterate hfInv_fixed gInv k with
      ⟨gInvPow⟩
    let V : IntervalMap := iterateMap f k ∘ iterateMap G n
    have hVfixed : IsFixedPoint V p := by
      change iterateMap f k (iterateMap G n p) = p
      rw [hHfixed, hFPowFixed]
    rcases hasRightGermC1Diffeomorphism_comp
        hFPowFixed hHfixed gFPow gH with ⟨gV⟩
    have hfPowComm :
        (f ∘ iterateMap f k) =ᶠ[𝓝[≥] p]
          (iterateMap f k ∘ f) := by
      filter_upwards [] with x
      simpa [iterateMap, Function.comp_apply] using
        (Function.Commute.self_iterate f k).eq x
    have hVcommEvent :
        (f ∘ V) =ᶠ[𝓝[≥] p] (V ∘ f) := by
      simpa [V] using
        rightEventuallyEq_commute_comp hfPowComm hHcommEvent hHtend
    have hVcomm : RightGermCommute p f V :=
      (sameRightGerm_iff_eventuallyEq havailable).2 hVcommEvent
    have hVfixedNear : ∀ q : I, p < q →
        ∃ x ∈ Set.Ioc p q, V x = x := by
      intro q hpq
      obtain ⟨x, hx, _hHx, hrelation⟩ := hintersections q hpq
      simp only [if_neg hm] at hrelation
      exact ⟨x, hx, hrelation⟩
    have hVidentity :=
      local_c1BV_Kopell_identity_of_accumulating_fixedPoints
        gf gV hgfBV hf_fixed hVfixed hf_repelling hVcomm hVfixedNear
    have hVidentityEvent : V =ᶠ[𝓝[≥] p] identityIntervalMap :=
      (sameRightGerm_iff_eventuallyEq havailable).1 hVidentity
    have hInvAfterF :=
      rightEventuallyEq_inverse_iterates hInvRightEvent hftend k
    have hCancelApplied := hInvAfterF.comp_tendsto hHtend
    have hIdentityApplied := hVidentityEvent.fun_comp (iterateMap fInv k)
    have hFinal : iterateMap G n =ᶠ[𝓝[≥] p] iterateMap fInv k := by
      filter_upwards [hCancelApplied, hIdentityApplied] with x hxCancel hxIdentity
      simp only [V, Function.comp_apply, identityIntervalMap] at hxCancel hxIdentity
      exact hxCancel.symm.trans hxIdentity
    simpa [k] using (sameRightGerm_iff_eventuallyEq havailable).2 hFinal

/-- The analytic core of the rational branch.  A rational selected
translation number produces a point where the indicated lift power meets a
deck translate.  Moving that point into the physical tail and applying the
local BV Kopell lemma to the relative germ forces equality with the signed
deck power. -/
private theorem rationalTranslationNumber_forces_signed_germ_power
    {f G : IntervalMap} {p : I}
    (hf_fixed : IsFixedPoint f p)
    (hG_fixed : IsFixedPoint G p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p)
    (hG_regular : HasRightGermC1BV G p)
    (hfG_commute : RightGermCommute p f G)
    (E : RightOrbitLineEmbedding p)
    (fAction : RightGermLineLift E f)
    (GAction : RightGermLineLift E G)
    (hf_deck : ∀ s : ℝ, circleLiftFun fAction.lift s = s + 1)
    {m : ℤ} {n : ℕ} (hn : 0 < n)
    (htranslation : selectedTranslationNumber GAction.lift =
      (m : ℝ) / (n : ℝ)) :
    SameAsSignedRightGermIterateAt p (iterateMap G n) f m := by
  apply local_c1BV_signed_power_rigidity_of_intersections
      hf_fixed hG_fixed hf_repelling hf_regular hG_regular hfG_commute
  intro q hpq
  let r : I := min q E.rightEnd
  have hpr : p < r := by
    simp only [r, lt_min_iff]
    exact ⟨hpq, E.base_lt_rightEnd⟩
  obtain ⟨q', hpq', hq'r⟩ := exists_between hpr
  have hq'q : q' < q := hq'r.trans_le (min_le_left _ _)
  have hq'E : q' < E.rightEnd := hq'r.trans_le (min_le_right _ _)
  obtain ⟨t, hxmem, hGmem, hxcoord, hGcoord, hrelation⟩ :=
    rationalTranslation_physical_power_relation E fAction GAction
      hf_deck hn htranslation (E.coord q')
  have hq'mem : q' ∈ Set.Ioo p E.rightEnd := ⟨hpq', hq'E⟩
  have hxlt : E.point t < q' :=
    (E.coord_strictMono.lt_iff_lt hxmem hq'mem).mp hxcoord
  have hGlt : iterateMap G n (E.point t) < q' :=
    (E.coord_strictMono.lt_iff_lt hGmem hq'mem).mp hGcoord
  refine ⟨E.point t, ⟨hxmem.1, hxlt.le.trans hq'q.le⟩,
    ⟨hGmem.1, hGlt.le.trans hq'q.le⟩, hrelation⟩

/-- Rational translation number gives the two complementary signed germ
powers.  This is the rational half of the orbit-circle proof, isolated so
that its inverse-germ and local Kopell bookkeeping is independently visible. -/
private theorem rationalOrbitAlternative_of_model
    {f A B : IntervalMap} {p : I} {d : ℕ}
    (hf_fixed : IsFixedPoint f p)
    (hA_fixed : IsFixedPoint A p)
    (hB_fixed : IsFixedPoint B p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p)
    (hA_regular : HasRightGermC1BV A p)
    (hB_regular : HasRightGermC1BV B p)
    (hfA_commute : RightGermCommute p f A)
    (hfB_commute : RightGermCommute p f B)
    (M : OneSidedOrbitLineModel f A B p d)
    {m : ℤ} {n : ℕ} (hn : 0 < n)
    (halpha : selectedTranslationNumber M.AAction.lift =
      (m : ℝ) / (n : ℝ)) :
    RationalOrbitAlternative f A B p d
      (selectedTranslationNumber M.AAction.lift) := by
  have hApower := rationalTranslationNumber_forces_signed_germ_power
    hf_fixed hA_fixed hf_repelling hf_regular hA_regular hfA_commute
    M.embedding M.fAction M.AAction M.f_is_unit_translation hn halpha
  have hproductTranslation :
      selectedTranslationNumber (M.AAction.lift * M.BAction.lift) = d := by
    change ((M.AAction.lift * M.BAction.lift : CircleHomeomorphismLift) :
      CircleDeg1Lift).translationNumber = (d : ℝ)
    have hvalue :
        ((M.AAction.lift * M.BAction.lift : CircleHomeomorphismLift) :
          CircleDeg1Lift) 0 = 0 + (d : ℤ) := by
      simpa [circleLiftFun, CircleDeg1Lift.mul_apply] using M.A_B_product 0
    simpa using
      (((M.AAction.lift * M.BAction.lift : CircleHomeomorphismLift) :
        CircleDeg1Lift).translationNumber_of_eq_add_int hvalue)
  have hadd := translationNumber_add_of_commuting_lifts
    M.AAction.lift M.BAction.lift M.A_B_commute
  have hnreal : (n : ℝ) ≠ 0 := by positivity
  let z : ℤ := (((d * n : ℕ) : ℤ) - m)
  have hBtranslation : selectedTranslationNumber M.BAction.lift =
      (z : ℝ) / (n : ℝ) := by
    rw [hproductTranslation] at hadd
    rw [halpha] at hadd
    dsimp [z]
    rw [eq_div_iff hnreal]
    push_cast
    field_simp at hadd ⊢
    linarith
  have hBpower := rationalTranslationNumber_forces_signed_germ_power
    hf_fixed hB_fixed hf_repelling hf_regular hB_regular hfB_commute
    M.embedding M.fAction M.BAction M.f_is_unit_translation hn hBtranslation
  exact ⟨m, n, hn, halpha, hApower, hBpower⟩

/-- Denjoy conjugacy, transported back through the common physical tail,
gives the simultaneous translation chart.  The `B` phase is forced by the
exact product relation rather than chosen modulo an integer. -/
private theorem irrationalOrbitAlternative_of_model
    {f A B : IntervalMap} {p : I} {d : ℕ}
    (M : OneSidedOrbitLineModel f A B p d)
    (hirr : Irrational (selectedTranslationNumber M.AAction.lift)) :
    IrrationalOrbitAlternative f A B p d
      (selectedTranslationNumber M.AAction.lift) := by
  obtain ⟨H, hHconj⟩ :=
    denjoy_conjugacy_of_irrational_translationNumber
      M.AAction.lift M.regular_A hirr
  let Hiso : ℝ ≃o ℝ := CircleDeg1Lift.toOrderIso H
  let oldBound : ℝ := min M.fAction.tailBound
    (min M.AAction.tailBound M.BAction.tailBound)
  let E' : RightOrbitLineEmbedding p :=
    { rightEnd := M.embedding.rightEnd
      base_lt_rightEnd := M.embedding.base_lt_rightEnd
      top := circleLiftFun H M.embedding.top
      coord := fun x => circleLiftFun H (M.embedding.coord x)
      point := fun s => M.embedding.point (circleLiftFun H⁻¹ s)
      coord_strictMono := by
        intro x hx y hy hxy
        exact Hiso.strictMono (M.embedding.coord_strictMono hx hy hxy)
      coord_lt_top := by
        intro x hx
        exact Hiso.strictMono (M.embedding.coord_lt_top hx)
      point_mem := by
        intro s hs
        apply M.embedding.point_mem
        apply Hiso.lt_iff_lt.mp
        simpa [Hiso, circleLiftFun] using hs
      point_coord := by
        intro x hx
        simpa [circleLiftFun] using M.embedding.point_coord x hx
      coord_point := by
        intro s hs
        have hsold : circleLiftFun H⁻¹ s < M.embedding.top := by
          apply Hiso.lt_iff_lt.mp
          simpa [Hiso, circleLiftFun] using hs
        rw [M.embedding.coord_point _ hsold]
        simp [circleLiftFun] }
  have hold_top : oldBound < M.embedding.top := by
    dsimp [oldBound]
    exact lt_of_le_of_lt (min_le_left _ _)
      M.fAction.tailBound_lt_top
  let newBound : ℝ := circleLiftFun H oldBound
  have hnew_top : newBound < E'.top := Hiso.strictMono hold_top
  have old_of_new : ∀ s < newBound, circleLiftFun H⁻¹ s < oldBound := by
    intro s hs
    apply Hiso.lt_iff_lt.mp
    simpa [newBound, Hiso, circleLiftFun] using hs
  have old_f : ∀ s < newBound,
      circleLiftFun H⁻¹ s < M.fAction.tailBound := by
    intro s hs
    exact (old_of_new s hs).trans_le (min_le_left _ _)
  have old_A : ∀ s < newBound,
      circleLiftFun H⁻¹ s < M.AAction.tailBound := by
    intro s hs
    exact (old_of_new s hs).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have old_B : ∀ s < newBound,
      circleLiftFun H⁻¹ s < M.BAction.tailBound := by
    intro s hs
    exact (old_of_new s hs).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hirr, ⟨{
    embedding := E'
    tailBound := newBound
    tailBound_lt_top := hnew_top
    f_image_mem := ?_
    A_image_mem := ?_
    B_image_mem := ?_
    f_translation := ?_
    A_translation := ?_
    B_translation := ?_ }⟩⟩
  · intro s hs
    exact M.fAction.image_mem _ (old_f s hs)
  · intro s hs
    exact M.AAction.image_mem _ (old_A s hs)
  · intro s hs
    exact M.BAction.image_mem _ (old_B s hs)
  · intro s hs
    change circleLiftFun H
      (M.embedding.coord (f (M.embedding.point (circleLiftFun H⁻¹ s)))) = s + 1
    rw [M.fAction.intertwines _ (old_f s hs), M.f_is_unit_translation]
    calc
      circleLiftFun H (circleLiftFun H⁻¹ s + 1) =
          circleLiftFun H (circleLiftFun H⁻¹ s) + 1 := by
        simpa [circleLiftFun] using
          (H : CircleDeg1Lift).map_add_one (circleLiftFun H⁻¹ s)
      _ = s + 1 := by simp [circleLiftFun]
  · intro s hs
    change circleLiftFun H
      (M.embedding.coord (A (M.embedding.point (circleLiftFun H⁻¹ s)))) =
        s + selectedTranslationNumber M.AAction.lift
    rw [M.AAction.intertwines _ (old_A s hs)]
    rw [hHconj]
    simp [circleLiftFun]
  · intro s hs
    change circleLiftFun H
      (M.embedding.coord (B (M.embedding.point (circleLiftFun H⁻¹ s)))) =
        s + (d - selectedTranslationNumber M.AAction.lift)
    rw [M.BAction.intertwines _ (old_B s hs)]
    have hprod := M.A_B_product (circleLiftFun H⁻¹ s)
    have hconj := hHconj
      (circleLiftFun M.BAction.lift (circleLiftFun H⁻¹ s))
    have hdeck : circleLiftFun H (circleLiftFun H⁻¹ s + d) = s + d := by
      calc
        circleLiftFun H (circleLiftFun H⁻¹ s + d) =
            circleLiftFun H (circleLiftFun H⁻¹ s) + d := by
          simpa [circleLiftFun] using
            (H : CircleDeg1Lift).map_add_nat (circleLiftFun H⁻¹ s) d
        _ = s + d := by simp [circleLiftFun]
    rw [hprod] at hconj
    rw [hdeck] at hconj
    linarith

/--
Orbit-circle dichotomy (manuscript Lemma 5).  The physical germ selects the
lift and hence the real number `α`; exactly one of the rational signed-power
alternative and the irrational simultaneous-translation alternative holds.
-/
theorem orbit_circle_dichotomy
    {f A B : IntervalMap} {p : I} {d : ℕ}
    (hd : 0 < d)
    (hf_fixed : IsFixedPoint f p)
    (hA_fixed : IsFixedPoint A p)
    (hB_fixed : IsFixedPoint B p)
    (hf_repelling : MovesStrictlyRightNear f p)
    (hf_regular : HasRightGermC1BV f p)
    (hA_regular : HasRightGermC1BV A p)
    (hB_regular : HasRightGermC1BV B p)
    (hfA_commute : RightGermCommute p f A)
    (hfB_commute : RightGermCommute p f B)
    (hAB_commute : RightGermCommute p A B)
    (hproduct : SameOneSidedGermAt .right p (A ∘ B) (iterateMap f d)) :
    ∃ M : OneSidedOrbitLineModel f A B p d,
      let α := selectedTranslationNumber M.AAction.lift
      Xor (RationalOrbitAlternative f A B p d α)
        (IrrationalOrbitAlternative f A B p d α) := by
  let M := Classical.choice
    (exists_oneSidedOrbitLineModel hd hf_fixed hA_fixed hB_fixed
      hf_repelling hf_regular hA_regular hB_regular hfA_commute
      hfB_commute hAB_commute hproduct)
  refine ⟨M, ?_⟩
  let alpha := selectedTranslationNumber M.AAction.lift
  by_cases hirr : Irrational alpha
  · right
    refine ⟨irrationalOrbitAlternative_of_model M hirr, ?_⟩
    rintro ⟨m, n, hn, halpha, _⟩
    exact hirr.ne_rational m (n : ℤ) (by simpa using halpha)
  · obtain ⟨m, n, hn, halpha⟩ :=
      rational_representation_of_not_irrational hirr
    left
    refine ⟨rationalOrbitAlternative_of_model hf_fixed hA_fixed hB_fixed
      hf_repelling hf_regular hA_regular hB_regular hfA_commute hfB_commute
      M hn halpha, ?_⟩
    rintro ⟨hirr', _⟩
    exact hirr'.ne_rational m (n : ℤ) (by simpa using halpha)

end CommutingInterval
