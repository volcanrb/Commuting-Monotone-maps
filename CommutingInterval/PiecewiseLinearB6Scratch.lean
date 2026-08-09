import CommutingInterval.PiecewiseLinearCore
import CommutingInterval.PiecewiseLinearOrbitRaySupport
import CommutingInterval.OrbitDichotomy

/-!
# Orbit circle, global ray, and exactness

This module specializes the orbit-circle dichotomy to a normalized
piecewise-linear counterexample.  It retains the physical local chart, deck
action, local-cover data, and positive boundary lift needed to extend a local
dilation germ to a global ray.  The rational alternative is stated with
signed deck powers; the irrational alternative yields the tail-core and
covering-exactness conclusions.
-/

noncomputable section

namespace CommutingInterval
namespace PiecewiseLinearB6

open Function Set

/-- The exact irrational orbit-circle output, before exponentiating the
translation coordinate.  In particular the full common physical chart is
retained. -/
structure TranslationChartData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) where
  d : ℕ
  d_pos : 0 < d
  returnedProduct : G.R = iterateMap G.W d
  alpha : ℝ
  irrational : Irrational alpha
  chart : RightTranslationChart G.W G.A G.B G.p d alpha

/-- The honest exponential image of a translation chart.  Actor scales are
only positive and nonunit here; they are not asserted expanding until after
the global ray and local-cover argument. -/
structure LocalDilationData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) where
  orbit : TranslationChartData G
  chart : LocalRayChart G.p
  lambdaScale : ℝ
  scaleA : ℝ
  scaleB : ℝ
  lambda_gt_one : 1 < lambdaScale
  scaleA_pos : 0 < scaleA
  scaleB_pos : 0 < scaleB
  scaleA_ne_one : scaleA ≠ 1
  scaleB_ne_one : scaleB ≠ 1
  product_eq_power : scaleA * scaleB = lambdaScale ^ orbit.d
  actionW : LocalRayScaleAction chart G.W lambdaScale
  actionA : LocalRayScaleAction chart G.A scaleA
  actionB : LocalRayScaleAction chart G.B scaleB

/-- The full global ray package consumed by tail-core and exactness.  This is
the minimal corrected replacement for `PiecewiseLinearRaySystem`: it retains
the locally strict chart, its extension, the expanding deck action, and the
local covering witness. -/
structure RayCoveringData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) where
  localData : LocalDilationData G
  ray : RayChart G.p
  extendsLocal : ray.ExtendsLocal localData.chart
  actionW : RayScaleAction ray G.W localData.lambdaScale
  actionA : RayScaleAction ray G.A localData.scaleA
  actionB : RayScaleAction ray G.B localData.scaleB
  actionR : RayScaleAction ray G.R (localData.scaleA * localData.scaleB)
  one_lt_scaleA : 1 < localData.scaleA
  one_lt_scaleB : 1 < localData.scaleB
  scales_independent :
    MultiplicativelyIndependent localData.scaleA localData.scaleB
  continuous_P : Continuous G.P
  continuous_Q : Continuous G.Q
  continuous_A : Continuous G.A
  continuous_B : Continuous G.B
  continuous_R : Continuous G.R
  continuous_W : Continuous G.W
  onto_P : IsOnto G.P
  onto_Q : IsOnto G.Q
  onto_A : IsOnto G.A
  onto_B : IsOnto G.B
  onto_R : IsOnto G.R
  onto_W : IsOnto G.W
  L_pos : 0 < G.L
  A_iterate : G.A = iterateMap G.P G.L
  B_iterate : G.B = iterateMap G.Q G.L
  R_comp : G.R = G.A ∘ G.B
  fixed_A_p : IsFixedPoint G.A G.p
  fixed_B_p : IsFixedPoint G.B G.p
  strict_A_near_p :
    ∃ q : I, G.p < q ∧ StrictMonoOn G.A (Set.Icc G.p q)
  strict_B_near_p :
    ∃ q : I, G.p < q ∧ StrictMonoOn G.B (Set.Icc G.p q)
  localCover :
    ∀ q : I, G.p < q →
      ∃ n : ℕ, iterateMap G.W n '' Set.Icc G.p q = Set.univ

/-- Exact orbit-circle dichotomy.  The rational side retains its signed
deck-germ powers; the irrational side retains the full translation chart. -/
def OrbitCircleAlternative
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop :=
  (∃ d : ℕ, ∃ alpha : ℝ,
      0 < d ∧ G.R = iterateMap G.W d ∧
        RationalOrbitAlternative G.W G.A G.B G.p d alpha) ∨
    Nonempty (TranslationChartData G)

/-- Specialize the checked orbit-circle theorem to the PL directed-return
data without projecting away either branch's actual output. -/
theorem piecewiseLinear_orbitCircle_localDichotomy
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_D : PiecewiseLinearDirectedReturnData G) :
    OrbitCircleAlternative G := by
  let d : ℕ := Nat.factorial (2 * G.system.base.fixedW.card)
  have hd : 0 < d := Nat.factorial_pos _
  have hWform : G.W = (G.P^[2]) ∘ (G.Q^[2]) := by
    exact G.system.commute.comp_iterate 2
  have hWiterate : G.W^[d] =
      ((G.P^[2])^[d]) ∘ ((G.Q^[2])^[d]) := by
    rw [hWform]
    exact (G.system.commute.iterate_iterate 2 2).comp_iterate d
  have hRword : G.R = iterateMap G.W d := by
    calc
      G.R = (G.P^[2 * d]) ∘ (G.Q^[2 * d]) := by rfl
      _ = ((G.P^[2])^[d]) ∘ ((G.Q^[2])^[d]) := by
        apply congrArg₂ (fun F H : IntervalMap => F ∘ H)
        · exact Function.iterate_mul G.P 2 d
        · exact Function.iterate_mul G.Q 2 d
      _ = G.W^[d] := hWiterate.symm
      _ = iterateMap G.W d := rfl
  have hMoves : MovesStrictlyRightNear G.W G.p := by
    obtain ⟨q, hpq, hqc⟩ := exists_between G.p_lt_c
    refine ⟨q, hpq, ?_⟩
    intro x hx
    exact G.moves_right x ⟨hx.1, hx.2.trans_lt hqc⟩
  have hAW : Commute G.A G.W := by
    change Commute (G.P^[G.L]) ((G.P ∘ G.Q)^[2])
    exact ((Function.Commute.refl G.P).comp_right G.system.commute).iterate_iterate
      G.L 2
  have hBW : Commute G.B G.W := by
    change Commute (G.Q^[G.L]) ((G.P ∘ G.Q)^[2])
    exact (G.system.commute.symm.comp_right
      (Function.Commute.refl G.Q)).iterate_iterate G.L 2
  have hAB : Commute G.A G.B := by
    change Commute (G.P^[G.L]) (G.Q^[G.L])
    exact G.system.commute.iterate_iterate G.L G.L
  have germCommute {F H : IntervalMap} (h : Commute F H) :
      RightGermCommute G.p F H := by
    refine ⟨G.c, G.p_lt_c, ?_⟩
    intro x _hx
    simpa [Function.comp_apply] using h x
  have hproduct : SameOneSidedGermAt .right G.p
      (G.A ∘ G.B) (iterateMap G.W d) := by
    refine ⟨G.c, G.p_lt_c, ?_⟩
    intro x _hx
    have hRcomp : G.R = G.A ∘ G.B := rfl
    exact congrFun (hRcomp.symm.trans hRword) x
  obtain ⟨M, horbit⟩ :=
    orbit_circle_dichotomy hd G.fixed_p _D.fixed_A_p _D.fixed_B_p
      hMoves _D.right_germ_W _D.right_germ_A _D.right_germ_B
      (germCommute hAW.symm) (germCommute hBW.symm)
      (germCommute hAB) hproduct
  let alpha : ℝ := selectedTranslationNumber M.AAction.lift
  dsimp only at horbit
  rcases horbit.or with hrational | hirrational
  · exact Or.inl ⟨d, alpha, hd, hRword, hrational⟩
  · rcases hirrational with ⟨halpha, ⟨chart⟩⟩
    exact Or.inr ⟨{
      d := d
      d_pos := hd
      returnedProduct := hRword
      alpha := alpha
      irrational := halpha
      chart := chart }⟩

/-- Closed-interval local covering determines every commuting map from one
right germ. -/
private theorem germDetermination_of_closedCover_plB6
    {W F H : IntervalMap} {p : I}
    (hcover : ∀ q : I, p < q →
      ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ)
    (hFcomm : Commute F W) (hHcomm : Commute H W)
    (hgerm : SameOneSidedGermAt .right p F H) : F = H := by
  obtain ⟨q, hpq, hagree⟩ := hgerm
  obtain ⟨n, hn⟩ := hcover q hpq
  funext y
  have hy : y ∈ iterateMap W n '' Set.Icc p q := by
    rw [hn]
    exact Set.mem_univ y
  obtain ⟨x, hx, hxy⟩ := hy
  calc
    F y = F (iterateMap W n x) := congrArg F hxy.symm
    _ = iterateMap W n (F x) := (hFcomm.iterate_right n).eq x
    _ = iterateMap W n (H x) := congrArg (iterateMap W n) (hagree hx)
    _ = H (iterateMap W n x) := (hHcomm.iterate_right n).eq x |>.symm
    _ = H y := congrArg H hxy

/-- The positive derivative in a `C¹+BV` right representative makes the
physical germ strictly increasing. -/
private theorem rightC1BVGerm_strictMono_rational_plB6
    {T : IntervalMap} {p : I}
    (h : HasRightGermC1BV T p) :
    ∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q) := by
  rcases h with ⟨g, _hgBV⟩
  refine ⟨g.rightEnd, g.base_lt_rightEnd, ?_⟩
  have hcont : ContinuousOn g.extension
      (Set.Icc (p : ℝ) (g.rightEnd : ℝ)) :=
    g.contDiff_one.continuousOn.mono g.segment_subset
  have hstrict : StrictMonoOn g.extension
      (Set.Icc (p : ℝ) (g.rightEnd : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont fun x hx =>
      g.deriv_pos x (interior_subset hx)
  intro x hx y hy hxy
  calc
    (T x : ℝ) = g.extension (x : ℝ) := g.agrees hx
    _ < g.extension (y : ℝ) := hstrict hx hy hxy
    _ = (T y : ℝ) := (g.agrees hy).symm

/-- A negative signed deck exponent is incompatible with onto-ness,
commutation, repulsion, and local eventual covering. -/
private theorem negative_signed_germ_power_impossible_plB6
    {W T : IntervalMap} {p : I} {n : ℕ} {m : ℤ}
    (hWcont : Continuous W)
    (hWfixed : IsFixedPoint W p)
    (hWregular : HasRightGermC1BV W p)
    (hWmoves : MovesStrictlyRightNear W p)
    (hcomm : Commute T W)
    (hLEO : HasLocalEventualOntoPL W p)
    (hm : m < 0)
    (hgerm : SameAsSignedRightGermIterateAt p (iterateMap T n) W m) :
    False := by
  have hmnot : ¬(0 : ℤ) ≤ m := not_le.mpr hm
  rcases (by
      simpa [SameAsSignedRightGermIterateAt, hmnot] using hgerm) with
    ⟨Winv, hWinv, hTgerm⟩
  rcases hWinv.2 with ⟨qInv, hpInv, hInv⟩
  rcases hTgerm with ⟨qT, hpT, hTlocal⟩
  obtain ⟨qStrict, hpStrict, hWstrict⟩ :=
    rightC1BVGerm_strictMono_rational_plB6 hWregular
  have hWp : W p = p := hWfixed

  -- Shrink a right interval so that one application of `W` lands in a
  -- prescribed right interval while remaining inside the inverse germ.
  have shrink : ∀ q : I, p < q →
      ∃ r : I, p < r ∧ r ≤ qInv ∧
        Set.MapsTo W (Set.Icc p r) (Set.Icc p q) := by
    intro q hpq
    have hpre : W ⁻¹' Set.Iio q ∈ nhds p := by
      exact hWcont.continuousAt
        (Iio_mem_nhds (by simpa only [hWp] using hpq))
    obtain ⟨u, hpu, hpu_sub⟩ :=
      exists_Ico_subset_of_mem_nhds hpre ⟨q, hpq⟩
    have hpmin : p < min u (min qInv qStrict) :=
      lt_min hpu (lt_min hpInv hpStrict)
    obtain ⟨r, hpr, hrmin⟩ := exists_between hpmin
    have hru : r < u := hrmin.trans_le (min_le_left _ _)
    have hrinner : r < min qInv qStrict :=
      hrmin.trans_le (min_le_right _ _)
    have hrInv : r ≤ qInv :=
      (hrinner.trans_le (min_le_left _ _)).le
    have hrStrict : r < qStrict :=
      hrinner.trans_le (min_le_right _ _)
    refine ⟨r, hpr, hrInv, ?_⟩
    intro x hx
    constructor
    · have hpx : p ∈ Set.Icc p qStrict := ⟨le_rfl, hpStrict.le⟩
      have hxx : x ∈ Set.Icc p qStrict :=
        ⟨hx.1, hx.2.trans (hrStrict.le)⟩
      have hmono := hWstrict.monotoneOn hpx hxx hx.1
      simpa only [hWp] using hmono
    · have hxu : x ∈ Set.Ico p u := ⟨hx.1, hx.2.trans_lt hru⟩
      exact (hpu_sub hxu).le

  -- On a sufficiently small interval, `Winv^k` cancels `W^k`, and the
  -- whole finite orbit remains in any prescribed right neighborhood.
  have cancel : ∀ k : ℕ, ∀ q : I, p < q →
      ∃ r : I, p < r ∧ r ≤ qInv ∧
        ∀ y ∈ Set.Icc p r,
          iterateMap W k y ∈ Set.Icc p q ∧
            iterateMap Winv k (iterateMap W k y) = y := by
    intro k
    induction k with
    | zero =>
        intro q hpq
        obtain ⟨r, hpr, hr⟩ := exists_between (lt_min hpq hpInv)
        have hrq : r < q := hr.trans_le (min_le_left _ _)
        have hrInv : r ≤ qInv :=
          (hr.trans_le (min_le_right _ _)).le
        refine ⟨r, hpr, hrInv, ?_⟩
        intro y hy
        constructor
        · simpa [iterateMap] using
            (show y ∈ Set.Icc p q from ⟨hy.1, hy.2.trans hrq.le⟩)
        · simp [iterateMap]
    | succ k ih =>
        intro q hpq
        obtain ⟨r₀, hpr₀, hr₀Inv, hcancel₀⟩ := ih q hpq
        obtain ⟨r, hpr, hrInv, hWmaps⟩ := shrink r₀ hpr₀
        refine ⟨r, hpr, hrInv, ?_⟩
        intro y hy
        have hWy : W y ∈ Set.Icc p r₀ := hWmaps hy
        have hc := hcancel₀ (W y) hWy
        constructor
        · simpa [iterateMap, Function.iterate_succ_apply] using hc.1
        · have hyInv : y ∈ Set.Icc p qInv :=
            ⟨hy.1, hy.2.trans hrInv⟩
          have hinvy : Winv (W y) = y := by
            simpa [Function.comp_apply, identityIntervalMap] using hInv hyInv
          change (Winv^[k + 1]) ((W^[k + 1]) y) = y
          calc
            (Winv^[k + 1]) ((W^[k + 1]) y) =
                Winv ((Winv^[k]) ((W^[k]) (W y))) := by
              rw [Function.iterate_succ_apply W k y]
              rw [Function.iterate_succ_apply' Winv k]
            _ = Winv (W y) := congrArg Winv hc.2
            _ = y := hinvy

  have hk : 0 < m.natAbs := Int.natAbs_pos.mpr hm.ne
  obtain ⟨r, hpr, _hrInv, hcancel⟩ := cancel m.natAbs qT hpT
  have hlocal : SameOneSidedGermAt .right p
      (iterateMap T n ∘ iterateMap W m.natAbs) identityIntervalMap := by
    refine ⟨r, hpr, ?_⟩
    intro y hy
    have hc := hcancel y hy
    change iterateMap T n (iterateMap W m.natAbs y) = y
    calc
      iterateMap T n (iterateMap W m.natAbs y) =
          iterateMap Winv m.natAbs (iterateMap W m.natAbs y) :=
        hTlocal hc.1
      _ = y := hc.2
  have hTnW : Commute (iterateMap T n) W := by
    simpa [iterateMap] using hcomm.iterate_left n
  have hWkW : Commute (iterateMap W m.natAbs) W := by
    simpa [iterateMap] using Function.Commute.iterate_self W m.natAbs
  have hcompW : Commute
      (iterateMap T n ∘ iterateMap W m.natAbs) W :=
    hTnW.comp_left hWkW
  have hidW : Commute identityIntervalMap W := by
    intro x
    rfl
  have hglobal : iterateMap T n ∘ iterateMap W m.natAbs =
      identityIntervalMap :=
    germDetermination_of_closedCover_plB6 hLEO hcompW hidW hlocal
  have hWkInj : Function.Injective (iterateMap W m.natAbs) := by
    intro x y hxy
    have hxy' := congrArg (iterateMap T n) hxy
    have hxglobal : iterateMap T n (iterateMap W m.natAbs x) = x := by
      simpa [Function.comp_apply, identityIntervalMap] using congrFun hglobal x
    have hyglobal : iterateMap T n (iterateMap W m.natAbs y) = y := by
      simpa [Function.comp_apply, identityIntervalMap] using congrFun hglobal y
    exact hxglobal.symm.trans (hxy'.trans hyglobal)
  have hWinj : Function.Injective W := by
    obtain ⟨k, hkform⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    intro x y hxy
    apply hWkInj
    rw [hkform]
    simp only [iterateMap, Function.iterate_succ_apply]
    rw [hxy]
  obtain ⟨qMove, hpMove, _hmove⟩ := hWmoves
  obtain ⟨b, hpb, hbMove⟩ := exists_between hpMove
  have hbRight : b < rightEndpoint := by
    have hqRight : qMove ≤ rightEndpoint := by
      simpa [rightEndpoint] using qMove.property.2
    exact hbMove.trans_le hqRight
  obtain ⟨N, hN⟩ := hLEO b hpb
  have htarget : iterateMap W N rightEndpoint ∈
      iterateMap W N '' Set.Icc p b := by
    rw [hN]
    exact Set.mem_univ _
  rcases htarget with ⟨x, hx, hximage⟩
  have hWNinj : Function.Injective (iterateMap W N) := by
    simpa [iterateMap] using hWinj.iterate N
  have hxRight : x = rightEndpoint := hWNinj hximage
  rw [hxRight] at hx
  exact (not_le_of_gt hbRight) hx.2

/-- A zero signed exponent globalizes to a finite-order factor; a commuting
continuous interval map then shares a fixed point with that factor. -/
private theorem zero_signed_germ_power_forces_commonFixed_plB6
    {F G W T : IntervalMap} {p : I} {L n : ℕ}
    (hFcont : Continuous F) (hGcont : Continuous G)
    (hFG : Commute F G) (hTW : Commute T W)
    (hLEO : HasLocalEventualOntoPL W p)
    (hL : 0 < L) (hn : 0 < n)
    (hT : T = iterateMap F L)
    (hgerm : SameAsSignedRightGermIterateAt p (iterateMap T n) W 0) :
    HasCommonFixedPoint F G := by
  have hgerm0 : SameOneSidedGermAt .right p
      (iterateMap T n) (iterateMap W 0) := by
    simpa [SameAsSignedRightGermIterateAt] using hgerm
  have hTncomm : Commute (iterateMap T n) W := by
    simpa [iterateMap] using hTW.iterate_left n
  have hIdcomm : Commute (iterateMap W 0) W := by
    simpa [iterateMap] using Function.Commute.iterate_self W 0
  have hTnid' : iterateMap T n = iterateMap W 0 :=
    germDetermination_of_closedCover_plB6 hLEO hTncomm hIdcomm hgerm0
  have hTnid : iterateMap T n = id := by
    simpa [iterateMap] using hTnid'
  have hFpow : iterateMap F (L * n) = id := by
    simpa [hT, iterateMap, Function.iterate_mul] using hTnid
  have hk : 0 < L * n := Nat.mul_pos hL hn
  have hiter_inj : Function.Injective (iterateMap F (L * n)) := by
    rw [hFpow]
    exact Function.injective_id
  have hF_inj : Function.Injective F := by
    obtain ⟨k, hkform⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    intro x y hxy
    apply hiter_inj
    rw [hkform]
    simp only [iterateMap, Function.iterate_succ_apply]
    rw [hxy]
  rcases hFcont.strictMono_of_inj hF_inj with hmono | hanti
  · have hFid : F = id := by
      funext x
      change F x = x
      have hkx : (F^[L * n]) x = x := by
        change iterateMap F (L * n) x = x
        rw [hFpow]
        rfl
      rcases lt_trichotomy (F x) x with hlt | heq | hgt
      · have hbad : (F^[L * n]) x < (F^[0]) x :=
          hmono.strictAnti_iterate_of_map_lt hlt hk
        exfalso
        simpa [hkx] using hbad
      · exact heq
      · have hbad : (F^[0]) x < (F^[L * n]) x :=
          hmono.strictMono_iterate_of_lt_map hgt hk
        exfalso
        simpa [hkx] using hbad
    exact IntervalMap.hasCommonFixedPoint_of_eq_id hGcont hFid
  · obtain ⟨x, hx⟩ := IntervalMap.exists_fixedPoint hFcont
    have hunique : ∀ y : I, IsFixedPoint F y → y = x := by
      intro y hy
      by_contra hyx
      rcases lt_or_gt_of_ne hyx with hyxlt | hxylt
      · have hcontra := hanti hyxlt
        rw [hx, hy] at hcontra
        exact (not_lt_of_ge hyxlt.le) hcontra
      · have hcontra := hanti hxylt
        rw [hx, hy] at hcontra
        exact (not_lt_of_ge hxylt.le) hcontra
    refine ⟨x, hx, ?_⟩
    apply hunique
    calc
      F (G x) = G (F x) := hFG x
      _ = G x := congrArg G hx

/-- Positive signed powers on both actors globalize by LEO and yield equal
positive iterates of the original maps. -/
private theorem positive_rational_germs_give_commonIterate_plB6
    {P Q W A B : IntervalMap} {p : I} {L n : ℕ} {m z : ℤ}
    (hAW : Commute A W) (hBW : Commute B W)
    (hLEO : HasLocalEventualOntoPL W p)
    (hL : 0 < L) (hn : 0 < n) (hm : 0 < m) (hz : 0 < z)
    (hA : A = iterateMap P L) (hB : B = iterateMap Q L)
    (hAgerm : SameAsSignedRightGermIterateAt p (iterateMap A n) W m)
    (hBgerm : SameAsSignedRightGermIterateAt p (iterateMap B n) W z) :
    ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ iterateMap P r = iterateMap Q s := by
  have hm0 : (0 : ℤ) ≤ m := hm.le
  have hz0 : (0 : ℤ) ≤ z := hz.le
  have hAgerm' : SameOneSidedGermAt .right p
      (iterateMap A n) (iterateMap W m.toNat) := by
    simpa [SameAsSignedRightGermIterateAt, hm0] using hAgerm
  have hBgerm' : SameOneSidedGermAt .right p
      (iterateMap B n) (iterateMap W z.toNat) := by
    simpa [SameAsSignedRightGermIterateAt, hz0] using hBgerm
  have hAncomm : Commute (iterateMap A n) W := by
    simpa [iterateMap] using hAW.iterate_left n
  have hBncomm : Commute (iterateMap B n) W := by
    simpa [iterateMap] using hBW.iterate_left n
  have hWmcomm : Commute (iterateMap W m.toNat) W := by
    simpa [iterateMap] using Function.Commute.iterate_self W m.toNat
  have hWzcomm : Commute (iterateMap W z.toNat) W := by
    simpa [iterateMap] using Function.Commute.iterate_self W z.toNat
  have hAglobal : iterateMap A n = iterateMap W m.toNat :=
    germDetermination_of_closedCover_plB6 hLEO hAncomm hWmcomm hAgerm'
  have hBglobal : iterateMap B n = iterateMap W z.toNat :=
    germDetermination_of_closedCover_plB6 hLEO hBncomm hWzcomm hBgerm'
  have hmNat : 0 < m.toNat := by omega
  have hzNat : 0 < z.toNat := by omega
  have hAz : iterateMap A (n * z.toNat) =
      iterateMap W (m.toNat * z.toNat) := by
    have h := congrArg (fun T : IntervalMap => iterateMap T z.toNat) hAglobal
    simpa [iterateMap, Function.iterate_mul] using h
  have hBm : iterateMap B (n * m.toNat) =
      iterateMap W (z.toNat * m.toNat) := by
    have h := congrArg (fun T : IntervalMap => iterateMap T m.toNat) hBglobal
    simpa [iterateMap, Function.iterate_mul] using h
  refine ⟨L * (n * z.toNat), L * (n * m.toNat),
    Nat.mul_pos hL (Nat.mul_pos hn hzNat),
    Nat.mul_pos hL (Nat.mul_pos hn hmNat), ?_⟩
  calc
    iterateMap P (L * (n * z.toNat)) =
        iterateMap A (n * z.toNat) := by
      simp [hA, iterateMap, Function.iterate_mul]
    _ = iterateMap W (m.toNat * z.toNat) := hAz
    _ = iterateMap W (z.toNat * m.toNat) := by rw [Nat.mul_comm]
    _ = iterateMap B (n * m.toNat) := hBm.symm
    _ = iterateMap Q (L * (n * m.toNat)) := by
      simp [hB, iterateMap, Function.iterate_mul]

/-- Symmetry of the physical common-fixed-point predicate. -/
private theorem hasCommonFixedPoint_comm_plB6 {F G : IntervalMap} :
    HasCommonFixedPoint F G → HasCommonFixedPoint G F := by
  rintro ⟨x, hxF, hxG⟩
  exact ⟨x, hxG, hxF⟩
/-! ### Exact signed-power resolution of the rational branch -/

/-- LEO resolves every sign case in the exact rational alternative: negative
deck powers are incompatible with the repelling germ, a zero deck power gives
a common fixed point, and two positive powers globalize to a common iterate. -/
theorem piecewiseLinear_rationalOrbitAlternative_impossible
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_D : PiecewiseLinearDirectedReturnData G)
    (_H : PreparedPiecewiseLinearCounterexample G)
    {d : ℕ} {alpha : ℝ}
    (_hd : 0 < d)
    (_hR : G.R = iterateMap G.W d)
    (_rat : RationalOrbitAlternative G.W G.A G.B G.p d alpha) : False := by
  have hPcont : Continuous G.P := G.system.continuousP
  have hQcont : Continuous G.Q := G.system.continuousQ
  have hWcont : Continuous G.W :=
    (hPcont.comp hQcont).iterate 2
  have hMoves : MovesStrictlyRightNear G.W G.p := by
    obtain ⟨q, hpq, hqc⟩ := exists_between G.p_lt_c
    refine ⟨q, hpq, ?_⟩
    intro x hx
    exact G.moves_right x ⟨hx.1, hx.2.trans_lt hqc⟩
  have hAW : Commute G.A G.W := by
    change Commute (G.P^[G.L]) ((G.P ∘ G.Q)^[2])
    exact ((Function.Commute.refl G.P).comp_right G.system.commute).iterate_iterate
      G.L 2
  have hBW : Commute G.B G.W := by
    change Commute (G.Q^[G.L]) ((G.P ∘ G.Q)^[2])
    exact (G.system.commute.symm.comp_right
      (Function.Commute.refl G.Q)).iterate_iterate G.L 2
  have hL : 0 < G.L :=
    piecewiseLinearNormalizationExponent_pos G.system.base.fixedW
  rcases _rat with ⟨m, n, hn, _halpha, hAgerm, hBgerm⟩
  let z : ℤ := (((d * n : ℕ) : ℤ) - m)
  have hBgermZ :
      SameAsSignedRightGermIterateAt G.p (iterateMap G.B n) G.W z := by
    simpa [z] using hBgerm
  by_cases hmneg : m < 0
  · exact negative_signed_germ_power_impossible_plB6
      hWcont G.fixed_p _D.right_germ_W hMoves hAW
      _H.local_eventual_onto hmneg hAgerm
  · by_cases hmzero : m = 0
    · subst m
      have hcommon := zero_signed_germ_power_forces_commonFixed_plB6
        hPcont hQcont G.system.commute hAW _H.local_eventual_onto
        hL hn (by rfl) hAgerm
      exact G.system.noCommonFixed hcommon
    · have hmpos : 0 < m := by omega
      by_cases hzneg : z < 0
      · exact negative_signed_germ_power_impossible_plB6
          hWcont G.fixed_p _D.right_germ_W hMoves hBW
          _H.local_eventual_onto hzneg hBgermZ
      · by_cases hzzero : z = 0
        · have hBgermZero : SameAsSignedRightGermIterateAt G.p
              (iterateMap G.B n) G.W 0 := by
            simpa [hzzero] using hBgermZ
          have hcommonQP := zero_signed_germ_power_forces_commonFixed_plB6
            hQcont hPcont G.system.commute.symm hBW
            _H.local_eventual_onto hL hn (by rfl) hBgermZero
          exact G.system.noCommonFixed
            (hasCommonFixedPoint_comm_plB6 hcommonQP)
        · have hzpos : 0 < z := by omega
          obtain ⟨r, s, hr, hs, hpowers⟩ :=
            positive_rational_germs_give_commonIterate_plB6
              hAW hBW _H.local_eventual_onto hL hn hmpos hzpos
              (by rfl) (by rfl) hAgerm hBgermZ
          have hcommon := common_positive_iterate
            hPcont hQcont G.system.commute hr hs hpowers
          exact G.system.noCommonFixed hcommon

/-- The ordered physical orbit line is an order isomorphism between its
coordinate half-line and the displayed punctured interval. -/
private noncomputable def rightOrbitLineOpenOrderIso {p : I}
    (E : RightOrbitLineEmbedding p) :
    Set.Iio E.top ≃o Set.Ioo p E.rightEnd where
  toFun s := ⟨E.point s, E.point_mem s s.property⟩
  invFun x := ⟨E.coord x, E.coord_lt_top x.property⟩
  left_inv s := Subtype.ext (E.coord_point s s.property)
  right_inv x := Subtype.ext (E.point_coord x x.property)
  map_rel_iff' {s t} := by
    change E.point s ≤ E.point t ↔ s ≤ t
    have hpoint : ∀ {u v : ℝ}, u < E.top → v < E.top → u < v →
        E.point u < E.point v := by
      intro u v hu hv huv
      apply lt_of_not_ge
      intro hge
      rcases hge.eq_or_lt with heq | hgt
      · apply huv.ne
        simpa [E.coord_point u hu, E.coord_point v hv] using
          congrArg E.coord heq.symm
      · have hc := E.coord_strictMono (E.point_mem v hv) (E.point_mem u hu) hgt
        have : v < u := by
          simpa [E.coord_point u hu, E.coord_point v hv] using hc
        exact (not_lt_of_ge huv.le) this
    constructor
    · intro hst
      apply le_of_not_gt
      intro hts
      exact (not_lt_of_ge hst) (hpoint t.property s.property hts)
    · intro hst
      apply le_of_not_gt
      intro hts
      have hc := E.coord_strictMono
        (E.point_mem t t.property) (E.point_mem s s.property) hts
      have : t < s := by
        simpa [E.coord_point s s.property, E.coord_point t t.property] using hc
      exact (not_lt_of_ge hst) this

private theorem rightOrbitLine_point_strictMono {p : I}
    (E : RightOrbitLineEmbedding p) {u v : ℝ}
    (hu : u < E.top) (hv : v < E.top) (huv : u < v) :
    E.point u < E.point v := by
  have hsub : (⟨u, hu⟩ : Set.Iio E.top) < ⟨v, hv⟩ := huv
  exact ((rightOrbitLineOpenOrderIso E).lt_iff_lt).2 hsub

/-- Extend `s ↦ E.point s` across the negative end by the exponential
parameter `t = exp s`, sending `t = 0` to the physical base point. -/
private noncomputable def exponentialRealRay {p : I}
    (E : RightOrbitLineEmbedding p) (t : ℝ) : I :=
  if t = 0 then p else E.point (Real.log t)

private noncomputable def exponentialRay {p : I}
    (E : RightOrbitLineEmbedding p) (t : RayParameter) : I :=
  exponentialRealRay E (t : ℝ)

private noncomputable def exponentialRealRayInv {p : I}
    (E : RightOrbitLineEmbedding p) (x : I) : ℝ :=
  if x = p then 0 else Real.exp (E.coord x)

private theorem exponentialRay_strictMonoOn {p : I}
    (E : RightOrbitLineEmbedding p) (c : ℝ) (hc : c < E.top) :
    StrictMonoOn (exponentialRay E) (rayInitialSegment (Real.exp c)) := by
  intro u hu v hv huv
  by_cases hu0 : (u : ℝ) = 0
  · have hv0 : (v : ℝ) ≠ 0 := by
      intro hvzero
      have : u = v := Subtype.ext (hu0.trans hvzero.symm)
      exact (ne_of_lt huv) this
    have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne v.property (Ne.symm hv0)
    have hlogv : Real.log (v : ℝ) < c :=
      (Real.log_lt_iff_lt_exp hvpos).2 hv
    have hlogtop : Real.log (v : ℝ) < E.top := hlogv.trans hc
    rw [exponentialRay, exponentialRealRay, if_pos hu0,
      exponentialRay, exponentialRealRay, if_neg hv0]
    exact (E.point_mem _ hlogtop).1
  · have hv0 : (v : ℝ) ≠ 0 := ne_of_gt (lt_of_le_of_lt u.property huv)
    have hupos : 0 < (u : ℝ) := lt_of_le_of_ne u.property (Ne.symm hu0)
    have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne v.property (Ne.symm hv0)
    have hlogu : Real.log (u : ℝ) < c :=
      (Real.log_lt_iff_lt_exp hupos).2 hu
    have hlogv : Real.log (v : ℝ) < c :=
      (Real.log_lt_iff_lt_exp hvpos).2 hv
    rw [exponentialRay, exponentialRealRay, if_neg hu0,
      exponentialRay, exponentialRealRay, if_neg hv0]
    apply rightOrbitLine_point_strictMono E (hlogu.trans hc) (hlogv.trans hc)
    exact Real.log_lt_log hupos huv

/-- On a finite initial segment, the exponential ray is an order
isomorphism onto the corresponding physical half-open interval. -/
private noncomputable def exponentialRealRayOrderIso {p : I}
    (E : RightOrbitLineEmbedding p) (c : ℝ) (hc : c < E.top) :
    Set.Ico (0 : ℝ) (Real.exp c) ≃o Set.Ico p (E.point c) where
  toFun t := by
    refine ⟨exponentialRealRay E (t : ℝ), ?_⟩
    by_cases ht : (t : ℝ) = 0
    · rw [exponentialRealRay, if_pos ht]
      exact ⟨le_rfl, (E.point_mem c hc).1⟩
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have hlogc : Real.log (t : ℝ) < c :=
        (Real.log_lt_iff_lt_exp htpos).2 t.property.2
      have hlogtop : Real.log (t : ℝ) < E.top := hlogc.trans hc
      rw [exponentialRealRay, if_neg ht]
      exact ⟨(E.point_mem _ hlogtop).1.le,
        rightOrbitLine_point_strictMono E hlogtop hc hlogc⟩
  invFun x := by
    refine ⟨exponentialRealRayInv E (x : I), ?_⟩
    by_cases hx : (x : I) = p
    · rw [exponentialRealRayInv, if_pos hx]
      exact ⟨le_rfl, Real.exp_pos c⟩
    · have hpx : p < (x : I) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
      have hqc : E.point c < E.rightEnd := (E.point_mem c hc).2
      have hxmem : (x : I) ∈ Set.Ioo p E.rightEnd :=
        ⟨hpx, x.property.2.trans hqc⟩
      have hcoord : E.coord x < c := by
        have hmono := E.coord_strictMono hxmem (E.point_mem c hc) x.property.2
        simpa [E.coord_point c hc] using hmono
      rw [exponentialRealRayInv, if_neg hx]
      exact ⟨(Real.exp_pos _).le, Real.exp_lt_exp.mpr hcoord⟩
  left_inv t := by
    apply Subtype.ext
    change exponentialRealRayInv E (exponentialRealRay E (t : ℝ)) = (t : ℝ)
    by_cases ht0 : (t : ℝ) = 0
    · rw [ht0]
      simp [exponentialRealRayInv, exponentialRealRay]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
      have hlogc : Real.log (t : ℝ) < c :=
        (Real.log_lt_iff_lt_exp htpos).2 t.property.2
      have hlogtop : Real.log (t : ℝ) < E.top := hlogc.trans hc
      have hpoint_ne : E.point (Real.log (t : ℝ)) ≠ p :=
        ne_of_gt (E.point_mem _ hlogtop).1
      rw [exponentialRealRay, if_neg ht0,
        exponentialRealRayInv, if_neg hpoint_ne]
      rw [E.coord_point _ hlogtop, Real.exp_log htpos]
  right_inv x := by
    apply Subtype.ext
    change exponentialRealRay E (exponentialRealRayInv E (x : I)) = (x : I)
    by_cases hx : (x : I) = p
    · rw [exponentialRealRayInv, if_pos hx]
      simp [exponentialRealRay, hx]
    · have hpx : p < (x : I) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
      have hqc : E.point c < E.rightEnd := (E.point_mem c hc).2
      have hxmem : (x : I) ∈ Set.Ioo p E.rightEnd :=
        ⟨hpx, x.property.2.trans hqc⟩
      rw [exponentialRealRayInv, if_neg hx,
        exponentialRealRay, if_neg (Real.exp_ne_zero _)]
      rw [Real.log_exp, E.point_coord x hxmem]
  map_rel_iff' {s t} := by
    change exponentialRealRay E (s : ℝ) ≤ exponentialRealRay E (t : ℝ) ↔
      (s : ℝ) ≤ (t : ℝ)
    let sr : RayParameter := ⟨s, s.property.1⟩
    let tr : RayParameter := ⟨t, t.property.1⟩
    have hs : sr ∈ rayInitialSegment (Real.exp c) := s.property.2
    have ht : tr ∈ rayInitialSegment (Real.exp c) := t.property.2
    have hsfun : exponentialRay E sr = exponentialRealRay E s := rfl
    have htfun : exponentialRay E tr = exponentialRealRay E t := rfl
    constructor
    · intro h
      apply le_of_not_gt
      intro hts
      have hstrict := exponentialRay_strictMonoOn E c hc ht hs hts
      rw [hsfun, htfun] at hstrict
      exact (not_lt_of_ge h) hstrict
    · intro h
      rcases h.eq_or_lt with heq | hlt
      · exact le_of_eq (congrArg (exponentialRealRay E) heq)
      · have hstrict := exponentialRay_strictMonoOn E c hc hs ht hlt
        rw [hsfun, htfun] at hstrict
        exact hstrict.le

private theorem exponentialRealRay_continuousOn {p : I}
    (E : RightOrbitLineEmbedding p) (c : ℝ) (hc : c < E.top) :
    ContinuousOn (exponentialRealRay E) (Set.Ico (0 : ℝ) (Real.exp c)) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_subtype_val.comp (exponentialRealRayOrderIso E c hc).continuous

private theorem exponentialRay_continuousOn {p : I}
    (E : RightOrbitLineEmbedding p) (c : ℝ) (hc : c < E.top) :
    ContinuousOn (exponentialRay E) (rayInitialSegment (Real.exp c)) := by
  have hreal := exponentialRealRay_continuousOn E c hc
  exact hreal.comp continuous_subtype_val.continuousOn fun t ht => ⟨t.property, ht⟩

/-- The local chart obtained by exponentiating a negative-end orbit-line
coordinate. -/
private noncomputable def exponentialLocalRayChart {p : I}
    (hp : p < rightEndpoint) (E : RightOrbitLineEmbedding p)
    (c : ℝ) (hc : c < E.top) : LocalRayChart p where
  base_lt_rightEndpoint := hp
  radius := Real.exp c
  radius_pos := Real.exp_pos c
  toFun := exponentialRay E
  continuousOn_toFun := exponentialRay_continuousOn E c hc
  map_origin := by
    change exponentialRealRay E 0 = p
    rw [exponentialRealRay, if_pos rfl]
  strictMonoOn_toFun := exponentialRay_strictMonoOn E c hc
  mapsTo_rightSide := by
    intro t ht
    by_cases ht0 : (t : ℝ) = 0
    · rw [exponentialRay, exponentialRealRay, if_pos ht0]
      show p ≤ p
      exact le_rfl
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property (Ne.symm ht0)
      have hlogc : Real.log (t : ℝ) < c :=
        (Real.log_lt_iff_lt_exp htpos).2 ht
      rw [exponentialRay, exponentialRealRay, if_neg ht0]
      exact (E.point_mem _ (hlogc.trans hc)).1.le

/-- Translation by `beta` in an orbit-line coordinate becomes multiplication
by `exp beta` in its exponential local ray chart. -/
private theorem localRayScaleAction_of_translation {p : I} {T : IntervalMap}
    (hp : p < rightEndpoint) (E : RightOrbitLineEmbedding p)
    (c : ℝ) (hc : c < E.top) (beta : ℝ)
    (hfixed : IsFixedPoint T p)
    (himage : ∀ s < c, T (E.point s) ∈ Set.Ioo p E.rightEnd)
    (htranslation : ∀ s < c, E.coord (T (E.point s)) = s + beta) :
    LocalRayScaleAction
      (exponentialLocalRayChart hp E c hc) T (Real.exp beta) := by
  refine ⟨Real.exp_pos beta, ?_⟩
  intro t ht hscaled
  by_cases ht0 : (t : ℝ) = 0
  · have hscaled0 :
        scaleRayParameter (Real.exp beta) (Real.exp_pos beta).le t = rayOrigin := by
      apply Subtype.ext
      change Real.exp beta * (t : ℝ) = 0
      rw [ht0, mul_zero]
    change T (exponentialRay E t) =
      exponentialRay E
        (scaleRayParameter (Real.exp beta) (Real.exp_pos beta).le t)
    rw [show exponentialRay E t = p by
      change exponentialRealRay E (t : ℝ) = p
      rw [exponentialRealRay, if_pos ht0]]
    rw [hfixed, hscaled0]
    change p = exponentialRealRay E 0
    rw [exponentialRealRay, if_pos rfl]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property (Ne.symm ht0)
    have hlogc : Real.log (t : ℝ) < c :=
      (Real.log_lt_iff_lt_exp htpos).2 ht
    have himage' := himage (Real.log (t : ℝ)) hlogc
    have hscaledpos :
        0 < (scaleRayParameter (Real.exp beta) (Real.exp_pos beta).le t : ℝ) := by
      exact mul_pos (Real.exp_pos beta) htpos
    change T (exponentialRay E t) =
      exponentialRay E
        (scaleRayParameter (Real.exp beta) (Real.exp_pos beta).le t)
    rw [exponentialRay, exponentialRealRay, if_neg ht0]
    rw [exponentialRay, exponentialRealRay, if_neg (ne_of_gt hscaledpos)]
    calc
      T (E.point (Real.log (t : ℝ))) =
          E.point (E.coord (T (E.point (Real.log (t : ℝ))))) :=
        (E.point_coord _ himage').symm
      _ = E.point (Real.log (t : ℝ) + beta) := by
        rw [htranslation _ hlogc]
      _ = E.point (Real.log
          (scaleRayParameter (Real.exp beta) (Real.exp_pos beta).le t : ℝ)) := by
        congr 1
        change Real.log (t : ℝ) + beta = Real.log (Real.exp beta * (t : ℝ))
        rw [Real.log_mul (Real.exp_ne_zero beta) ht0, Real.log_exp]
        ring
/-! ### Exponentiating the retained translation chart -/

/-- Exponentiate the full common translation chart.  This is the adapter
which cannot be defined from the legacy projected translation germ. -/
theorem piecewiseLinear_translationChart_to_localDilation
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_D : PiecewiseLinearDirectedReturnData G)
    (_T : TranslationChartData G) :
    Nonempty (LocalDilationData G) := by
  let chart : LocalRayChart G.p :=
    exponentialLocalRayChart
      (G.p_lt_c.trans_le G.c.property.2) _T.chart.embedding
      _T.chart.tailBound _T.chart.tailBound_lt_top
  let lambdaScale : ℝ := Real.exp 1
  let scaleA : ℝ := Real.exp _T.alpha
  let scaleB : ℝ := Real.exp ((_T.d : ℝ) - _T.alpha)
  have hlambda : 1 < lambdaScale := by
    dsimp [lambdaScale]
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr zero_lt_one)
  have haPos : 0 < scaleA := Real.exp_pos _T.alpha
  have hbPos : 0 < scaleB := Real.exp_pos ((_T.d : ℝ) - _T.alpha)
  have haNe : scaleA ≠ 1 := by
    intro h
    apply _T.irrational.ne_zero
    apply Real.exp_injective
    simpa [scaleA] using h
  have hbetaNe : (_T.d : ℝ) - _T.alpha ≠ 0 := by
    intro h
    apply _T.irrational.ne_nat _T.d
    linarith
  have hbNe : scaleB ≠ 1 := by
    intro h
    apply hbetaNe
    apply Real.exp_injective
    simpa [scaleB] using h
  have hproduct : scaleA * scaleB = lambdaScale ^ _T.d := by
    dsimp [scaleA, scaleB, lambdaScale]
    calc
      Real.exp _T.alpha * Real.exp ((_T.d : ℝ) - _T.alpha) =
          Real.exp (_T.alpha + ((_T.d : ℝ) - _T.alpha)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp ((_T.d : ℝ) * 1) := by congr 1 <;> ring
      _ = Real.exp 1 ^ _T.d := Real.exp_nat_mul 1 _T.d
  have hWaction : LocalRayScaleAction chart G.W lambdaScale := by
    exact localRayScaleAction_of_translation
      (G.p_lt_c.trans_le G.c.property.2) _T.chart.embedding
      _T.chart.tailBound _T.chart.tailBound_lt_top 1 G.fixed_p
      _T.chart.f_image_mem _T.chart.f_translation
  have hAaction : LocalRayScaleAction chart G.A scaleA := by
    exact localRayScaleAction_of_translation
      (G.p_lt_c.trans_le G.c.property.2) _T.chart.embedding
      _T.chart.tailBound _T.chart.tailBound_lt_top _T.alpha _D.fixed_A_p
      _T.chart.A_image_mem _T.chart.A_translation
  have hBaction : LocalRayScaleAction chart G.B scaleB := by
    exact localRayScaleAction_of_translation
      (G.p_lt_c.trans_le G.c.property.2) _T.chart.embedding
      _T.chart.tailBound _T.chart.tailBound_lt_top
      ((_T.d : ℝ) - _T.alpha) _D.fixed_B_p
      _T.chart.B_image_mem (by
        intro s hs
        simpa using _T.chart.B_translation s hs)
  exact ⟨{
    orbit := _T
    chart := chart
    lambdaScale := lambdaScale
    scaleA := scaleA
    scaleB := scaleB
    lambda_gt_one := hlambda
    scaleA_pos := haPos
    scaleB_pos := hbPos
    scaleA_ne_one := haNe
    scaleB_ne_one := hbNe
    product_eq_power := hproduct
    actionW := hWaction
    actionA := hAaction
    actionB := hBaction }⟩

/-- A positive `C¹` right germ is strictly increasing on its displayed
closed representative interval. -/
private theorem rightC1BVGerm_strictMono_plB6
    {T : IntervalMap} {p : I}
    (h : HasRightGermC1BV T p) :
    ∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q) := by
  rcases h with ⟨g, _hgBV⟩
  refine ⟨g.rightEnd, g.base_lt_rightEnd, ?_⟩
  have hcont : ContinuousOn g.extension
      (Set.Icc (p : ℝ) (g.rightEnd : ℝ)) :=
    g.contDiff_one.continuousOn.mono g.segment_subset
  have hstrict : StrictMonoOn g.extension
      (Set.Icc (p : ℝ) (g.rightEnd : ℝ)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont fun x hx =>
      g.deriv_pos x (interior_subset hx)
  intro x hx y hy hxy
  calc
    (T x : ℝ) = g.extension (x : ℝ) := g.agrees hx
    _ < g.extension (y : ℝ) := hstrict hx hy hxy
    _ = (T y : ℝ) := (g.agrees hy).symm

/-- Extend the locally strict deck dilation to a global ray, propagate both
commuting actor germs, and only then prove the actor scales expanding and
independent.  The returned package retains the B5 local-cover witness. -/
theorem piecewiseLinear_localDilation_to_rayCovering
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (_D : PiecewiseLinearDirectedReturnData G)
    (_H : PreparedPiecewiseLinearCounterexample G)
    (_T : LocalDilationData G) :
    Nonempty (RayCoveringData G) := by
  have hPcont : Continuous G.P := G.system.continuousP
  have hQcont : Continuous G.Q := G.system.continuousQ
  have hAcont : Continuous G.A := hPcont.iterate G.L
  have hBcont : Continuous G.B := hQcont.iterate G.L
  have hRcont : Continuous G.R := hAcont.comp hBcont
  have hWcont : Continuous G.W := (hPcont.comp hQcont).iterate 2
  have hPonto : IsOnto G.P := G.system.base.base.ontoP
  have hQonto : IsOnto G.Q := G.system.base.base.ontoQ
  have hAonto : IsOnto G.A :=
    IntervalMap.surjective_iterate hPonto G.L
  have hBonto : IsOnto G.B :=
    IntervalMap.surjective_iterate hQonto G.L
  have hRonto : IsOnto G.R := hAonto.comp hBonto
  have hWonto : IsOnto G.W :=
    IntervalMap.surjective_iterate (hPonto.comp hQonto) 2
  have hL : 0 < G.L :=
    piecewiseLinearNormalizationExponent_pos G.system.base.fixedW
  have hAW : Commute G.A G.W := by
    change Commute (G.P^[G.L]) ((G.P ∘ G.Q)^[2])
    exact ((Function.Commute.refl G.P).comp_right G.system.commute).iterate_iterate
      G.L 2
  have hBW : Commute G.B G.W := by
    change Commute (G.Q^[G.L]) ((G.P ∘ G.Q)^[2])
    exact (G.system.commute.symm.comp_right
      (Function.Commute.refl G.Q)).iterate_iterate G.L 2
  have hWstrict := rightC1BVGerm_strictMono_plB6 _D.right_germ_W
  obtain ⟨ray, hextends, hWaction⟩ :=
    extend_local_germ_to_fullRay _T.chart _T.lambdaScale hWcont
      G.fixed_p hWstrict _T.lambda_gt_one _T.actionW
      _H.local_eventual_onto
  have hAgerm : HasLocalScaleGerm ray G.A _T.scaleA :=
    localRayScaleAction_to_hasLocalScaleGerm hextends _T.actionA
  have hBgerm : HasLocalScaleGerm ray G.B _T.scaleB :=
    localRayScaleAction_to_hasLocalScaleGerm hextends _T.actionB
  have hAaction : RayScaleAction ray G.A _T.scaleA :=
    localScaleGerm_extends_to_fullRay ray hWcont hAcont hAW
      _T.lambda_gt_one hWaction hAgerm
  have hBaction : RayScaleAction ray G.B _T.scaleB :=
    localScaleGerm_extends_to_fullRay ray hWcont hBcont hBW
      _T.lambda_gt_one hWaction hBgerm
  obtain ⟨ha_ne, hb_ne, hindependent⟩ :=
    scaleFactors_nontrivial_and_multiplicativelyIndependent
      ray G.P G.Q G.A G.B _T.scaleA _T.scaleB G.L
      hPcont hQcont G.system.commute G.system.noCommonFixed hL
      (by rfl) (by rfl) hAaction hBaction
  have ha : 1 < _T.scaleA :=
    globalScale_gt_one_of_onto_commuting_actor ray hWcont hAcont
      hAonto hAW _T.lambda_gt_one hWaction hAaction ha_ne
      _H.local_eventual_onto
  have hb : 1 < _T.scaleB :=
    globalScale_gt_one_of_onto_commuting_actor ray hWcont hBcont
      hBonto hBW _T.lambda_gt_one hWaction hBaction hb_ne
      _H.local_eventual_onto
  have hRdef : G.R = G.A ∘ G.B := rfl
  have hRaction : RayScaleAction ray G.R (_T.scaleA * _T.scaleB) :=
    rayScaleAction_comp ray hRdef hAaction hBaction
  have hAstrict := rightC1BVGerm_strictMono_plB6 _D.right_germ_A
  have hBstrict := rightC1BVGerm_strictMono_plB6 _D.right_germ_B
  exact ⟨{
    localData := _T
    ray := ray
    extendsLocal := hextends
    actionW := hWaction
    actionA := hAaction
    actionB := hBaction
    actionR := hRaction
    one_lt_scaleA := ha
    one_lt_scaleB := hb
    scales_independent := hindependent
    continuous_P := hPcont
    continuous_Q := hQcont
    continuous_A := hAcont
    continuous_B := hBcont
    continuous_R := hRcont
    continuous_W := hWcont
    onto_P := hPonto
    onto_Q := hQonto
    onto_A := hAonto
    onto_B := hBonto
    onto_R := hRonto
    onto_W := hWonto
    L_pos := hL
    A_iterate := rfl
    B_iterate := rfl
    R_comp := hRdef
    fixed_A_p := _D.fixed_A_p
    fixed_B_p := _D.fixed_B_p
    strict_A_near_p := hAstrict
    strict_B_near_p := hBstrict
    localCover := _H.local_eventual_onto }⟩

/-- The three exhaustive possibilities for the compact interval tail core. -/
def HasTailCoreTrichotomy
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) : Prop :=
  (∃ x : I, T.ray.tailCore = {x}) ∨
    (∃ J : ClosedSubinterval, J.Nondegenerate ∧
      T.ray.tailCore = J.carrier ∧ J.carrier ≠ Set.univ) ∨
    T.ray.tailCore = Set.univ

/-- Generic compact connected tail extraction supplies the trichotomy; no
piecewise-linear or minimality input is used at this step. -/
theorem piecewiseLinear_rayTailCore_trichotomy
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) :
    HasTailCoreTrichotomy T := by
  obtain ⟨Omega, _htails, hcore, _hAeq, _hBeq, _hinvariant⟩ :=
    commonInvariant_rayTail_extraction T.ray G.A G.B
      T.localData.scaleA T.localData.scaleB T.continuous_A T.continuous_B
      T.actionA T.actionB
  by_cases hnondegenerate : Omega.Nondegenerate
  · by_cases hproper : Omega.carrier ≠ Set.univ
    · exact Or.inr (Or.inl
        ⟨Omega, hnondegenerate, hcore.symm, hproper⟩)
    · exact Or.inr (Or.inr (hcore.symm.trans (not_ne_iff.mp hproper)))
  · left
    have hends : Omega.left = Omega.right :=
      le_antisymm Omega.left_le_right (le_of_not_gt hnondegenerate)
    refine ⟨Omega.left, hcore.symm.trans ?_⟩
    ext x
    simp [ClosedSubinterval.carrier, hends]

/-- If the only `W`-fixed points allowed by the ray tail are the selected
gap endpoints, an onto finite-piece PL map commuting with `W` cannot carry
the ray base to the other endpoint.  The affine branch at the base has three
possibilities: a flat branch globalizes to a constant map by local covering,
a decreasing branch reverses the selected rightward motion, and an increasing
branch produces a third fixed point by the intermediate value theorem. -/
private theorem onto_finitePiecePL_commuter_ne_gapEndpoint_plB6
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) (F : IntervalMap)
    (hFPL : FinitePiecePL F) (hFonto : IsOnto F)
    (hFW : Commute F G.W)
    (hfixedPosition : ∀ {z : I}, IsFixedPoint G.W z →
      z = G.p ∨ z = G.c) :
    F G.p ≠ G.c := by
  intro hFp
  obtain ⟨partition, hpartition⟩ := hFPL.2
  obtain ⟨a, b, hab, hap, hpb⟩ :=
    PLFiniteArrivalSupport.RealPartition.exists_adjacent_right_b5 partition
      G.p.property
      (show (G.p : ℝ) < 1 from
        (show (G.p : ℝ) < (G.c : ℝ) from G.p_lt_c).trans_le
          G.c.property.2)
  have hbI : b ∈ I := partition.points_subset hab.2.1
  let q : I := ⟨b, hbI⟩
  have hpq : G.p < q := by
    change (G.p : ℝ) < b
    exact hpb
  obtain ⟨m, d, hformula⟩ := hpartition hab
  have hcell : Set.Icc G.p q ⊆ intervalCell a b := by
    intro z hz
    change a ≤ (z : ℝ) ∧ (z : ℝ) ≤ b
    constructor
    · exact hap.trans hz.1
    · simpa [q] using hz.2
  have hpCell : G.p ∈ Set.Icc G.p q := ⟨le_rfl, hpq.le⟩

  have hWp : G.W G.p = G.p := G.fixed_p
  have hWpre : G.W ⁻¹' Set.Iio q ∈ nhds G.p := by
    exact T.continuous_W.continuousAt
      (Iio_mem_nhds (by rw [hWp]; exact hpq))
  have hFpre : F ⁻¹' Set.Ioi G.p ∈ nhds G.p := by
    exact hFPL.1.continuousAt
      (Ioi_mem_nhds (by simpa only [hFp] using G.p_lt_c))
  have hpre : (G.W ⁻¹' Set.Iio q) ∩ (F ⁻¹' Set.Ioi G.p) ∈
      nhds G.p := Filter.inter_mem hWpre hFpre
  obtain ⟨u, hpu, hpu_sub⟩ :=
    exists_Ico_subset_of_mem_nhds hpre ⟨q, hpq⟩
  have hpmin : G.p < min u (min q G.c) :=
    lt_min hpu (lt_min hpq G.p_lt_c)
  obtain ⟨x, hpx, hxmin⟩ := exists_between hpmin
  have hxu : x < u := hxmin.trans_le (min_le_left _ _)
  have hxq : x < q :=
    hxmin.trans_le (min_le_right _ _) |>.trans_le (min_le_left _ _)
  have hxc : x < G.c :=
    hxmin.trans_le (min_le_right _ _) |>.trans_le (min_le_right _ _)
  have hxpre := hpu_sub ⟨hpx.le, hxu⟩
  have hWxq : G.W x < q := hxpre.1
  have hpFx : G.p < F x := hxpre.2
  have hxmove : x < G.W x := G.moves_right x ⟨hpx, hxc⟩
  have hxCell : x ∈ Set.Icc G.p q := ⟨hpx.le, hxq.le⟩
  have hWxCell : G.W x ∈ Set.Icc G.p q :=
    ⟨hpx.le.trans hxmove.le, hWxq.le⟩

  rcases lt_trichotomy m 0 with hmneg | hmzero | hmpos
  · have hanti : StrictAntiOn F (Set.Icc G.p q) := by
      intro y hy z hz hyz
      change (F z : ℝ) < (F y : ℝ)
      rw [hformula z (hcell hz), hformula y (hcell hy)]
      have hyzReal : (y : ℝ) < (z : ℝ) := hyz
      nlinarith
    have hFxc : F x < G.c := by
      have h := hanti hpCell hxCell hpx
      simpa only [hFp] using h
    have hWFl : G.W (F x) < F x := by
      calc
        G.W (F x) = F (G.W x) := (hFW x).symm
        _ < F x := hanti hxCell hWxCell hxmove
    have hFright : F x < G.W (F x) :=
      G.moves_right (F x) ⟨hpFx, hFxc⟩
    exact (lt_asymm hFright hWFl).elim
  · let K : IntervalMap := fun _ ↦ G.c
    have hKW : Commute K G.W := by
      intro z
      change G.c = G.W G.c
      exact G.fixed_c.symm
    have hgerm : SameOneSidedGermAt .right G.p F K := by
      refine ⟨q, hpq, ?_⟩
      intro z hz
      change F z = G.c
      calc
        F z = F G.p := by
          apply Subtype.ext
          change (F z : ℝ) = (F G.p : ℝ)
          rw [hformula z (hcell hz), hformula G.p (hcell hpCell)]
          simp [hmzero]
        _ = G.c := hFp
    have hFK : F = K :=
      germDetermination_of_closedCover_plB6 T.localCover hFW hKW hgerm
    obtain ⟨z, hz⟩ := hFonto G.p
    have hcp : G.c = G.p := by
      calc
        G.c = K z := rfl
        _ = F z := (congrFun hFK z).symm
        _ = G.p := hz
    exact G.p_lt_c.ne hcp.symm
  · have hmono : StrictMonoOn F (Set.Icc G.p q) := by
      intro y hy z hz hyz
      change (F y : ℝ) < (F z : ℝ)
      rw [hformula y (hcell hy), hformula z (hcell hz)]
      have hyzReal : (y : ℝ) < (z : ℝ) := hyz
      nlinarith
    have hcFx : G.c < F x := by
      have h := hmono hpCell hxCell hpx
      simpa only [hFp] using h
    have hFright : F x < G.W (F x) := by
      calc
        F x < F (G.W x) := hmono hxCell hWxCell hxmove
        _ = G.W (F x) := hFW x
    obtain ⟨z, hz, hzfix⟩ :=
      exists_mem_Icc_isFixedPt T.continuous_W.continuousOn
        (F x).property.2 hFright.le (G.W rightEndpoint).property.2
    have hcz : G.c < z := hcFx.trans_le hz.1
    rcases hfixedPosition hzfix with hzp | hzc
    · rw [hzp] at hcz
      exact (not_lt_of_ge G.p_lt_c.le hcz).elim
    · rw [hzc] at hcz
      exact (lt_irrefl G.c hcz).elim

/-- A singleton tail core forces a common fixed point at the selected gap,
contradicting the least PL counterexample. -/
theorem piecewiseLinear_rayTailCore_not_singleton
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) :
    ¬∃ x : I, T.ray.tailCore = {x} := by
  rintro ⟨x, hcore⟩
  have hcTail : G.c ∈ T.ray.tailCore :=
    (fixedPoint_eq_base_or_mem_tailCore T.ray T.actionW
      T.localData.lambda_gt_one G.fixed_c).resolve_left G.p_lt_c.ne'
  have hcx : G.c = x := by
    rw [hcore] at hcTail
    simpa using hcTail
  have hfixedPosition : ∀ {z : I}, IsFixedPoint G.W z →
      z = G.p ∨ z = G.c := by
    intro z hz
    rcases fixedPoint_eq_base_or_mem_tailCore T.ray T.actionW
        T.localData.lambda_gt_one hz with hzp | hzTail
    · exact Or.inl hzp
    · right
      have hzx : z = x := by
        rw [hcore] at hzTail
        simpa using hzTail
      exact hzx.trans hcx.symm
  have hPW : Commute G.P G.W := by
    have hP_PQ : Commute G.P (G.P ∘ G.Q) :=
      (Function.Commute.refl G.P).comp_right G.system.commute
    change Commute G.P (iterateMap (G.P ∘ G.Q) 2)
    exact hP_PQ.iterate_right 2
  have hQW : Commute G.Q G.W := by
    have hQ_PQ : Commute G.Q (G.P ∘ G.Q) :=
      G.system.commute.symm.comp_right (Function.Commute.refl G.Q)
    change Commute G.Q (iterateMap (G.P ∘ G.Q) 2)
    exact hQ_PQ.iterate_right 2
  have hPpfixed : IsFixedPoint G.W (G.P G.p) := by
    calc
      G.W (G.P G.p) = G.P (G.W G.p) := (hPW G.p).symm
      _ = G.P G.p := congrArg G.P G.fixed_p
  have hQpfixed : IsFixedPoint G.W (G.Q G.p) := by
    calc
      G.W (G.Q G.p) = G.Q (G.W G.p) := (hQW G.p).symm
      _ = G.Q G.p := congrArg G.Q G.fixed_p
  have hPp : IsFixedPoint G.P G.p := by
    rcases hfixedPosition hPpfixed with hPp | hPc
    · exact hPp
    · exact False.elim
        (onto_finitePiecePL_commuter_ne_gapEndpoint_plB6 T G.P
          G.system.finitePieceP T.onto_P hPW hfixedPosition hPc)
  have hQp : IsFixedPoint G.Q G.p := by
    rcases hfixedPosition hQpfixed with hQp | hQc
    · exact hQp
    · exact False.elim
        (onto_finitePiecePL_commuter_ne_gapEndpoint_plB6 T G.Q
          G.system.finitePieceQ T.onto_Q hQW hfixedPosition hQc)
  exact G.noCommonFixed ⟨G.p, hPp, hQp⟩

/-- A proper nondegenerate tail interval contradicts either minimal common
core or the B2 fixed-component quotient lexicographic minimality. -/
theorem piecewiseLinear_rayTailCore_not_properNondegenerate
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) :
    ¬∃ J : ClosedSubinterval, J.Nondegenerate ∧
      T.ray.tailCore = J.carrier ∧ J.carrier ≠ Set.univ := by
  rintro ⟨J, hJnondegenerate, htailJ, hJproper⟩
  obtain ⟨Omega, _htails, hOmegaTail, hAonto, hBonto,
      _hcommonCore⟩ :=
    commonInvariant_rayTail_extraction T.ray G.A G.B
      T.localData.scaleA T.localData.scaleB T.continuous_A T.continuous_B
      T.actionA T.actionB
  have hOmegaJ : Omega.carrier = J.carrier := hOmegaTail.trans htailJ
  have hAontoJ : G.A '' J.carrier = J.carrier := by
    rw [← hOmegaJ]
    exact hAonto
  have hBontoJ : G.B '' J.carrier = J.carrier := by
    rw [← hOmegaJ]
    exact hBonto
  apply
    PLFiniteArrivalSupport.proper_powerInvariant_interval_impossible_of_phase_descent
      (P := G.P) (Q := G.Q) T.L_pos J T.continuous_P T.continuous_Q
      G.system.commute
  · rw [← T.A_iterate]
    exact hAontoJ
  · rw [← T.B_iterate]
    exact hBontoJ
  · exact hJnondegenerate
  · exact hJproper
  · exact G.system.base.base.core_minimal
  · intro π hrespectP hrespectQ hidentified
    exact
      leastNormalizedPiecewiseLinear_no_respectedQuotient_identifying_S_fixedPoints_b5Prototype
        G.system π hrespectP hrespectQ hidentified

/-- Eliminating the two proper alternatives identifies the full tail core. -/
theorem piecewiseLinear_rayTailCore_eq_univ
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) :
    T.ray.tailCore = Set.univ := by
  rcases piecewiseLinear_rayTailCore_trichotomy T with
    hsingleton | hproper | hfull
  · exact False.elim
      (piecewiseLinear_rayTailCore_not_singleton T hsingleton)
  · exact False.elim
      (piecewiseLinear_rayTailCore_not_properNondegenerate T hproper)
  · exact hfull

/-- Full tail core is exactly the dense-tail property used by exactness. -/
theorem piecewiseLinear_ray_hasDenseTails
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) : T.ray.HasDenseTails := by
  exact denseTails_of_tailCore_eq_univ T.ray
    (piecewiseLinear_rayTailCore_eq_univ T)

/-- The positive lift of the selected boundary required by the covering
argument. -/
structure BoundaryLiftData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G) where
  tstar : RayParameter
  positiveBoundary : T.ray.IsPositiveBoundaryLift tstar

/-- Dense tails and the expanding returned product supply the boundary lift. -/
theorem piecewiseLinear_exists_positiveBoundaryLift
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G)
    (hdense : T.ray.HasDenseTails) :
    Nonempty (BoundaryLiftData T) := by
  have hRfixed : IsFixedPoint G.R G.p := by
    rw [T.R_comp]
    change G.A (G.B G.p) = G.p
    rw [T.fixed_B_p, T.fixed_A_p]
  have hRstrict := strictMonoOn_comp_near_fixed T.R_comp T.fixed_B_p
    T.continuous_B T.strict_A_near_p T.strict_B_near_p
  have hproduct : 1 < T.localData.scaleA * T.localData.scaleB := by
    nlinarith [T.one_lt_scaleA, T.one_lt_scaleB]
  obtain ⟨tstar, htstar⟩ :=
    exists_positiveBoundaryLift T.ray G.R
      (T.localData.scaleA * T.localData.scaleB) T.continuous_R T.onto_R
      hRfixed hRstrict hproduct T.actionR hdense
  exact ⟨⟨tstar, htstar⟩⟩

/-- The single covering package whose projections are the five B6 exactness
leaves and their nonflatness consequences. -/
structure ExactnessData
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source) : Prop where
  exact_R : IsTopologicallyExact G.R
  exact_A : IsTopologicallyExact G.A
  exact_B : IsTopologicallyExact G.B
  exact_P : IsTopologicallyExact G.P
  exact_Q : IsTopologicallyExact G.Q
  noFlat_R : ¬HasFlatInterval G.R
  noFlat_A : ¬HasFlatInterval G.A
  noFlat_B : ¬HasFlatInterval G.B
  noFlat_P : ¬HasFlatInterval G.P
  noFlat_Q : ¬HasFlatInterval G.Q

/-- Apply the checked generic ray-covering theorem once, retaining its entire
conclusion for projection by the five public exactness lemmas. -/
theorem piecewiseLinear_denseRay_exactnessPackage
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G)
    (hdense : T.ray.HasDenseTails)
    (E : BoundaryLiftData T) : ExactnessData G := by
  rcases ray_exactness_covering_package T.ray
      G.P G.Q G.A G.B G.R G.W
      T.localData.scaleA T.localData.scaleB
      (T.localData.scaleA * T.localData.scaleB) G.L T.localData.orbit.d
      T.continuous_P T.continuous_Q T.continuous_A T.continuous_B
      T.continuous_R T.continuous_W T.onto_P T.onto_Q T.onto_A
      T.onto_B T.onto_R T.onto_W T.L_pos T.localData.orbit.d_pos
      T.A_iterate T.B_iterate T.localData.orbit.returnedProduct
      T.fixed_A_p T.fixed_B_p T.strict_A_near_p T.strict_B_near_p
      T.actionA T.actionB T.actionR T.one_lt_scaleA T.one_lt_scaleB
      rfl T.scales_independent hdense E.tstar E.positiveBoundary
      T.localCover with
    ⟨hR, hA, hB, hP, hQ, hfR, hfA, hfB, hfP, hfQ⟩
  exact ⟨hR, hA, hB, hP, hQ, hfR, hfA, hfB, hfP, hfQ⟩

theorem piecewiseLinear_denseRay_exact_P
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : ExactnessData G) : IsTopologicallyExact G.P := E.exact_P

theorem piecewiseLinear_denseRay_exact_Q
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : ExactnessData G) : IsTopologicallyExact G.Q := E.exact_Q

theorem piecewiseLinear_denseRay_exact_A
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : ExactnessData G) : IsTopologicallyExact G.A := E.exact_A

theorem piecewiseLinear_denseRay_exact_B
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : ExactnessData G) : IsTopologicallyExact G.B := E.exact_B

theorem piecewiseLinear_denseRay_exact_R
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : ExactnessData G) : IsTopologicallyExact G.R := E.exact_R

end PiecewiseLinearB6
end CommutingInterval
