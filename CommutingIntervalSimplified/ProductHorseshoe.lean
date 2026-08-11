import CommutingIntervalSimplified.PiecewiseMonotoneBase

/-!
# The direct product horseshoe

This file isolates the geometric input to the weak-lap construction.  It is
standalone: the only dynamical ingredients are continuity, commutation, and
the absence of a common fixed point.  The named De Marr configuration and
the two trimming lemmas expose the complete substantive proof DAG rather
than hiding the product horseshoe behind one opaque assertion.
-/

namespace CommutingIntervalSimplified

open Function Set

/-- The image of `[a,b]` under `F` covers `[c,d]`. -/
def IntervalCovers (F : IntervalMap) (a b c d : I) : Prop :=
  Set.Icc c d ⊆ F '' Set.Icc a b

/-- Two separated closed branches whose images cover their common hull. -/
structure TwoBranchHorseshoe (F : IntervalMap) where
  a : I
  b : I
  c : I
  d : I
  a_lt_b : a < b
  b_lt_c : b < c
  c_lt_d : c < d
  left_covers : IntervalCovers F a b a d
  right_covers : IntervalCovers F c d a d

theorem intervalCovers_of_endpoints_mono
    {F : IntervalMap} (hF : Continuous F)
    {a b c d : I} (hab : a ≤ b) (_hcd : c ≤ d)
    (hleft : F a ≤ c) (hright : d ≤ F b) :
    IntervalCovers F a b c d := by
  intro y hy
  apply intermediate_value_Icc hab hF.continuousOn
  exact ⟨hleft.trans hy.1, hy.2.trans hright⟩

theorem intervalCovers_of_endpoints_anti
    {F : IntervalMap} (hF : Continuous F)
    {a b c d : I} (hab : a ≤ b) (_hcd : c ≤ d)
    (hleft : F b ≤ c) (hright : d ≤ F a) :
    IntervalCovers F a b c d := by
  intro y hy
  apply intermediate_value_Icc' hab hF.continuousOn
  exact ⟨hleft.trans hy.1, hy.2.trans hright⟩

theorem IntervalCovers.mono_domain
    {F : IntervalMap} {a b a' b' c d : I}
    (h : IntervalCovers F a b c d)
    (hsub : Set.Icc a b ⊆ Set.Icc a' b') :
    IntervalCovers F a' b' c d := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := h hy
  exact ⟨x, hsub hx, hxy⟩

theorem IntervalCovers.comp
    {P Q : IntervalMap} {a b c d e f : I}
    (hQ : IntervalCovers Q a b c d)
    (hP : IntervalCovers P c d e f) :
    IntervalCovers (P ∘ Q) a b e f := by
  intro y hy
  obtain ⟨z, hz, hPzy⟩ := hP hy
  obtain ⟨x, hx, hQxz⟩ := hQ hz
  exact ⟨x, hx, by change P (Q x) = y; rw [hQxz, hPzy]⟩

/-! ## Fixed sets and the closest crossing pair -/

theorem fixedPoints_isClosed {T : IntervalMap} (hT : Continuous T) :
    IsClosed (fixedPoints T) := by
  simpa [fixedPoints, IsFixedPoint] using isClosed_eq hT continuous_id

theorem fixedPoints_isCompact {T : IntervalMap} (hT : Continuous T) :
    IsCompact (fixedPoints T) := by
  exact (fixedPoints_isClosed hT).isCompact

theorem fixedPoints_nonempty {T : IntervalMap} (hT : Continuous T) :
    (fixedPoints T).Nonempty := by
  obtain ⟨x, hx⟩ := IntervalMap.exists_fixedPoint hT
  exact ⟨x, hx⟩

/-- A commuting map preserves the fixed set of the other map. -/
theorem commute_mapsTo_fixedPoints {P Q : IntervalMap}
    (hcomm : Function.Commute P Q) :
    MapsTo Q (fixedPoints P) (fixedPoints P) := by
  intro x hx
  change P x = x at hx
  change P (Q x) = Q x
  rw [hcomm x, hx]

/-- A closest ordered pair in `Fix(P)` where `Q` moves the left point right
and the right point left.  The minimal-gap field is the exact compactness
output used to exclude further `P`-fixed points between the pair. -/
structure MinimalFixedCrossingPair (P Q : IntervalMap) where
  x0 : I
  x1 : I
  x0_lt_x1 : x0 < x1
  fixed_P_x0 : P x0 = x0
  fixed_P_x1 : P x1 = x1
  Q_moves_x0_right : x0 < Q x0
  Q_moves_x1_left : Q x1 < x1
  minimal_gap :
    ∀ y0 y1 : I,
      P y0 = y0 → y0 < Q y0 →
      P y1 = y1 → Q y1 < y1 → y0 < y1 →
      (x1 : ℝ) - (x0 : ℝ) ≤ (y1 : ℝ) - (y0 : ℝ)

/-- Compactness of the two closed sign sets supplies a closest crossing
pair.  Weak inequalities become strict because equality would be a common
fixed point. -/
theorem exists_minimalFixedCrossingPair
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Function.Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Nonempty (MinimalFixedCrossingPair P Q) := by
  let rising : Set I := fixedPoints P ∩ {x | x ≤ Q x}
  let falling : Set I := fixedPoints P ∩ {x | Q x ≤ x}
  let pairs : Set (I × I) :=
    (rising ×ˢ falling) ∩ {z | z.1 ≤ z.2}
  have hrisingClosed : IsClosed rising := by
    exact (fixedPoints_isClosed hP).inter (isClosed_le continuous_id hQ)
  have hfallingClosed : IsClosed falling := by
    exact (fixedPoints_isClosed hP).inter (isClosed_le hQ continuous_id)
  have hpairsClosed : IsClosed pairs := by
    exact (hrisingClosed.prod hfallingClosed).inter
      (isClosed_le continuous_fst continuous_snd)
  have hfixedNonempty : (fixedPoints P).Nonempty := fixedPoints_nonempty hP
  obtain ⟨xmin, hxmin, hxmin_le⟩ :=
    (fixedPoints_isCompact hP).exists_isMinOn
      hfixedNonempty continuous_id.continuousOn
  obtain ⟨xmax, hxmax, hxmax_ge⟩ :=
    (fixedPoints_isCompact hP).exists_isMaxOn
      hfixedNonempty continuous_id.continuousOn
  have hQxmin : Q xmin ∈ fixedPoints P :=
    commute_mapsTo_fixedPoints hcomm hxmin
  have hQxmax : Q xmax ∈ fixedPoints P :=
    commute_mapsTo_fixedPoints hcomm hxmax
  have hxmin_rising : xmin ∈ rising :=
    ⟨hxmin, hxmin_le hQxmin⟩
  have hxmax_falling : xmax ∈ falling :=
    ⟨hxmax, hxmax_ge hQxmax⟩
  have hxmin_le_xmax : xmin ≤ xmax := hxmin_le hxmax
  have hpairsNonempty : pairs.Nonempty :=
    ⟨(xmin, xmax), ⟨⟨hxmin_rising, hxmax_falling⟩,
      hxmin_le_xmax⟩⟩
  let gap : I × I → ℝ := fun z ↦ (z.2 : ℝ) - (z.1 : ℝ)
  have hgapContinuous : Continuous gap := by
    exact (continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)
  obtain ⟨z, hz, hzmin⟩ :=
    hpairsClosed.isCompact.exists_isMinOn
      hpairsNonempty hgapContinuous.continuousOn
  rcases z with ⟨x0, x1⟩
  have hx0rising : x0 ∈ rising := hz.1.1
  have hx1falling : x1 ∈ falling := hz.1.2
  have hx0le_x1 : x0 ≤ x1 := hz.2
  have hPx0 : P x0 = x0 := hx0rising.1
  have hPx1 : P x1 = x1 := hx1falling.1
  have hx0leQx0 : x0 ≤ Q x0 := hx0rising.2
  have hQx1lex1 : Q x1 ≤ x1 := hx1falling.2
  have hQx0ne : Q x0 ≠ x0 := by
    intro heq
    apply hno
    exact ⟨x0, hPx0, heq⟩
  have hQx1ne : Q x1 ≠ x1 := by
    intro heq
    apply hno
    exact ⟨x1, hPx1, heq⟩
  have hx0ltQx0 : x0 < Q x0 :=
    lt_of_le_of_ne hx0leQx0 hQx0ne.symm
  have hQx1ltx1 : Q x1 < x1 :=
    lt_of_le_of_ne hQx1lex1 hQx1ne
  have hx0ltx1 : x0 < x1 := by
    apply lt_of_le_of_ne hx0le_x1
    intro heq
    subst x1
    exact (not_lt_of_ge hQx1lex1) hx0ltQx0
  refine ⟨{
    x0 := x0
    x1 := x1
    x0_lt_x1 := hx0ltx1
    fixed_P_x0 := hPx0
    fixed_P_x1 := hPx1
    Q_moves_x0_right := hx0ltQx0
    Q_moves_x1_left := hQx1ltx1
    minimal_gap := ?_ }⟩
  intro y0 y1 hPy0 hy0right hPy1 hy1left hy01
  have hyPair : (y0, y1) ∈ pairs :=
    ⟨⟨⟨hPy0, hy0right.le⟩, ⟨hPy1, hy1left.le⟩⟩, hy01.le⟩
  exact hzmin hyPair

namespace MinimalFixedCrossingPair

/-- Minimality leaves no further `P`-fixed point in the open gap. -/
theorem no_fixed_P_between
    {P Q : IntervalMap} (X : MinimalFixedCrossingPair P Q)
    (hno : ¬HasCommonFixedPoint P Q) :
    ∀ z ∈ Set.Ioo X.x0 X.x1, P z ≠ z := by
  intro z hz hPz
  have hQz_ne : Q z ≠ z := by
    intro hQz
    apply hno
    exact ⟨z, hPz, hQz⟩
  rcases lt_or_gt_of_ne hQz_ne with hQzleft | hzright
  · have hmin := X.minimal_gap X.x0 z
      X.fixed_P_x0 X.Q_moves_x0_right hPz hQzleft hz.1
    have hstrict :
        (z : ℝ) - (X.x0 : ℝ) <
          (X.x1 : ℝ) - (X.x0 : ℝ) :=
      sub_lt_sub_right (show (z : ℝ) < (X.x1 : ℝ) from hz.2)
        (X.x0 : ℝ)
    exact (not_le_of_gt hstrict) hmin
  · have hmin := X.minimal_gap z X.x1
      hPz hzright X.fixed_P_x1 X.Q_moves_x1_left hz.2
    have hstrict :
        (X.x1 : ℝ) - (z : ℝ) <
          (X.x1 : ℝ) - (X.x0 : ℝ) :=
      sub_lt_sub_left (show (X.x0 : ℝ) < (z : ℝ) from hz.1)
        (X.x1 : ℝ)
    exact (not_le_of_gt hstrict) hmin

/-- Commutation pushes the left endpoint across the entire fixed-point-free
gap. -/
theorem Q_x0_ge_x1
    {P Q : IntervalMap} (X : MinimalFixedCrossingPair P Q)
    (hcomm : Function.Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    X.x1 ≤ Q X.x0 := by
  have hfixed : P (Q X.x0) = Q X.x0 := by
    have hx0mem : X.x0 ∈ fixedPoints P := X.fixed_P_x0
    exact commute_mapsTo_fixedPoints hcomm hx0mem
  by_contra hge
  have hinside : Q X.x0 ∈ Set.Ioo X.x0 X.x1 :=
    ⟨X.Q_moves_x0_right, lt_of_not_ge hge⟩
  exact X.no_fixed_P_between hno (Q X.x0) hinside hfixed

/-- Commutation pushes the right endpoint across the entire
fixed-point-free gap. -/
theorem Q_x1_le_x0
    {P Q : IntervalMap} (X : MinimalFixedCrossingPair P Q)
    (hcomm : Function.Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Q X.x1 ≤ X.x0 := by
  have hfixed : P (Q X.x1) = Q X.x1 := by
    have hx1mem : X.x1 ∈ fixedPoints P := X.fixed_P_x1
    exact commute_mapsTo_fixedPoints hcomm hx1mem
  by_contra hle
  have hinside : Q X.x1 ∈ Set.Ioo X.x0 X.x1 :=
    ⟨lt_of_not_ge hle, X.Q_moves_x1_left⟩
  exact X.no_fixed_P_between hno (Q X.x1) hinside hfixed

end MinimalFixedCrossingPair

/-! ## The fixed-point-free gap -/

/-- On an interval containing no fixed point, one strict right displacement
fixes the displacement direction throughout the interval. -/
theorem gap_moves_right
    {T : IntervalMap} (hT : Continuous T) {a b r : I}
    (hr : r ∈ Set.Ioo a b)
    (hfree : ∀ z ∈ Set.Ioo a b, T z ≠ z)
    (hrright : r < T r) :
    ∀ z ∈ Set.Ioo a b, z < T z := by
  intro z hz
  rcases lt_or_gt_of_ne (hfree z hz) with hTzleft | hzright
  · obtain ⟨w, hw, hTw⟩ := exists_mem_uIcc_isFixedPt
      hT.continuousOn hrright.le hTzleft.le
    have hwgap : w ∈ Set.Ioo a b := by
      rcases Set.mem_uIcc.mp hw with hrwz | hzwr
      · exact ⟨hr.1.trans_le hrwz.1, hrwz.2.trans_lt hz.2⟩
      · exact ⟨hz.1.trans_le hzwr.1, hzwr.2.trans_lt hr.2⟩
    exact ((hfree w hwgap) hTw).elim
  · exact hzright

/-- The analogous left-displacement statement. -/
theorem gap_moves_left
    {T : IntervalMap} (hT : Continuous T) {a b r : I}
    (hr : r ∈ Set.Ioo a b)
    (hfree : ∀ z ∈ Set.Ioo a b, T z ≠ z)
    (hrleft : T r < r) :
    ∀ z ∈ Set.Ioo a b, T z < z := by
  intro z hz
  rcases lt_or_gt_of_ne (hfree z hz) with hTzleft | hzright
  · exact hTzleft
  · obtain ⟨w, hw, hTw⟩ := exists_mem_uIcc_isFixedPt
      hT.continuousOn hzright.le hrleft.le
    have hwgap : w ∈ Set.Ioo a b := by
      rcases Set.mem_uIcc.mp hw with hzw | hrw
      · exact ⟨hz.1.trans_le hzw.1, hzw.2.trans_lt hr.2⟩
      · exact ⟨hr.1.trans_le hrw.1, hrw.2.trans_lt hz.2⟩
    exact ((hfree w hwgap) hTw).elim

/-- Fixed points of `T` in a closed gap. -/
def gapFixedPoints (T : IntervalMap) (a b : I) : Set I :=
  fixedPoints T ∩ Set.Icc a b

theorem gapFixedPoints_isCompact
    {T : IntervalMap} (hT : Continuous T) (a b : I) :
    IsCompact (gapFixedPoints T a b) := by
  exact ((fixedPoints_isClosed hT).inter isClosed_Icc).isCompact

theorem gapFixedPoints_nonempty
    {T : IntervalMap} (hT : Continuous T) {a b : I}
    (hab : a ≤ b) (ha : a ≤ T a) (hb : T b ≤ b) :
    (gapFixedPoints T a b).Nonempty := by
  obtain ⟨s, hs, hTs⟩ :=
    exists_mem_Icc_isFixedPt hT.continuousOn hab ha hb
  exact ⟨s, hTs, hs⟩

theorem gapFixedPoints_has_least
    {T : IntervalMap} (hT : Continuous T) {a b : I}
    (hne : (gapFixedPoints T a b).Nonempty) :
    ∃ s ∈ gapFixedPoints T a b,
      ∀ y ∈ gapFixedPoints T a b, s ≤ y := by
  obtain ⟨s, hs, hmin⟩ :=
    (gapFixedPoints_isCompact hT a b).exists_isMinOn
      hne continuous_id.continuousOn
  exact ⟨s, hs, fun _ hy ↦ hmin hy⟩

theorem gapFixedPoints_has_greatest
    {T : IntervalMap} (hT : Continuous T) {a b : I}
    (hne : (gapFixedPoints T a b).Nonempty) :
    ∃ s ∈ gapFixedPoints T a b,
      ∀ y ∈ gapFixedPoints T a b, y ≤ s := by
  obtain ⟨s, hs, hmax⟩ :=
    (gapFixedPoints_isCompact hT a b).exists_isMaxOn
      hne continuous_id.continuousOn
  exact ⟨s, hs, fun _ hy ↦ hmax hy⟩

/-! ## The two genuine trimming steps -/

/-- Adjacent forward branches can be trimmed to separated closed branches. -/
theorem strict_horseshoe_of_forward_adjacent_branches
    {F : IntervalMap} (hF : Continuous F)
    {l p m r : I}
    (hlp : l < p) (hpm : p < m) (hmr : m < r)
    (hFp : F p = r) (hFm : F m ≤ l)
    (hright : IntervalCovers F m r l r)
    (hFr : F r ≠ r) :
    Nonempty (TwoBranchHorseshoe F) := by
  have hlr : l < r := hlp.trans (hpm.trans hmr)
  have hrTarget : r ∈ Set.Icc l r := ⟨hlr.le, le_rfl⟩
  obtain ⟨d, hdDom, hFd⟩ := hright hrTarget
  have hd_ne_m : d ≠ m := by
    intro hdm
    subst d
    have hrle : r ≤ l := by simpa [hFd] using hFm
    exact (not_le_of_gt hlr) hrle
  have hd_ne_r : d ≠ r := by
    intro hdr
    apply hFr
    subst d
    exact hFd
  have hmd : m < d := lt_of_le_of_ne hdDom.1 hd_ne_m.symm
  have hdr : d < r := lt_of_le_of_ne hdDom.2 hd_ne_r
  obtain ⟨e, hde, her⟩ := exists_between hdr
  have hle : l < e := hlp.trans (hpm.trans (hmd.trans hde))
  have heValues : e ∈ Set.Icc (F m) (F p) := by
    constructor
    · exact hFm.trans hle.le
    · simpa [hFp] using her.le
  obtain ⟨a, haDom, hFa⟩ :=
    intermediate_value_Icc' hpm.le hF.continuousOn heValues
  have ha_ne_p : a ≠ p := by
    intro hap
    subst a
    have : e = r := by rw [← hFa, hFp]
    exact her.ne this
  have ha_ne_m : a ≠ m := by
    intro ham
    subst a
    have hele : e ≤ l := by simpa [hFa] using hFm
    exact (not_le_of_gt hle) hele
  have hpa : p < a := lt_of_le_of_ne haDom.1 ha_ne_p.symm
  have ham : a < m := lt_of_le_of_ne haDom.2 ha_ne_m
  have hla : l < a := hlp.trans hpa
  obtain ⟨u, hlu, hua⟩ := exists_between hla
  have hue : u < e := hua.trans (ham.trans (hmd.trans hde))
  have huLeftValues : u ∈ Set.Icc (F m) (F a) := by
    constructor
    · exact hFm.trans hlu.le
    · simpa [hFa] using hue.le
  obtain ⟨b, hbDom, hFb⟩ :=
    intermediate_value_Icc' ham.le hF.continuousOn huLeftValues
  have hb_ne_a : b ≠ a := by
    intro hba
    subst b
    have : u = e := by rw [← hFb, hFa]
    exact hue.ne this
  have hb_ne_m : b ≠ m := by
    intro hbm
    subst b
    have hule : u ≤ l := by simpa [hFb] using hFm
    exact (not_le_of_gt hlu) hule
  have hab : a < b := lt_of_le_of_ne hbDom.1 hb_ne_a.symm
  have hbm : b < m := lt_of_le_of_ne hbDom.2 hb_ne_m
  have huRightValues : u ∈ Set.Icc (F m) (F d) := by
    constructor
    · exact hFm.trans hlu.le
    · simpa [hFd] using (hue.trans her).le
  obtain ⟨c, hcDom, hFc⟩ :=
    intermediate_value_Icc hmd.le hF.continuousOn huRightValues
  have hc_ne_m : c ≠ m := by
    intro hcm
    subst c
    have hule : u ≤ l := by simpa [hFc] using hFm
    exact (not_le_of_gt hlu) hule
  have hc_ne_d : c ≠ d := by
    intro hcd
    subst c
    have : u = r := by rw [← hFc, hFd]
    exact (hue.trans her).ne this
  have hmc : m < c := lt_of_le_of_ne hcDom.1 hc_ne_m.symm
  have hcd : c < d := lt_of_le_of_ne hcDom.2 hc_ne_d
  refine ⟨{
    a := a
    b := b
    c := c
    d := d
    a_lt_b := hab
    b_lt_c := hbm.trans hmc
    c_lt_d := hcd
    left_covers := intervalCovers_of_endpoints_anti hF hab.le
      (hab.trans (hbm.trans (hmc.trans hcd))).le
      (by simpa [hFb] using hua.le)
      (by simpa [hFa] using hde.le)
    right_covers := intervalCovers_of_endpoints_mono hF hcd.le
      (hab.trans (hbm.trans (hmc.trans hcd))).le
      (by simpa [hFc] using hua.le)
      (by simpa [hFd] using hdr.le) }⟩

/-- The reflected adjacent-branch configuration admits the same trimming. -/
theorem strict_horseshoe_of_backward_adjacent_branches
    {F : IntervalMap} (hF : Continuous F)
    {l p m r : I}
    (hlp : l < p) (hpm : p < m) (hmr : m < r)
    (hFl : F l ≠ l) (hFp : r ≤ F p) (hFm : F m = l)
    (hleft : IntervalCovers F l p l r) :
    Nonempty (TwoBranchHorseshoe F) := by
  have hlr : l < r := hlp.trans (hpm.trans hmr)
  have hlTarget : l ∈ Set.Icc l r := ⟨le_rfl, hlr.le⟩
  obtain ⟨a, haDom, hFa⟩ := hleft hlTarget
  have ha_ne_l : a ≠ l := by
    intro hal
    apply hFl
    subst a
    exact hFa
  have ha_ne_p : a ≠ p := by
    intro hap
    subst a
    have hrle : r ≤ l := by simpa [hFa] using hFp
    exact (not_le_of_gt hlr) hrle
  have hla : l < a := lt_of_le_of_ne haDom.1 ha_ne_l.symm
  have hap : a < p := lt_of_le_of_ne haDom.2 ha_ne_p
  obtain ⟨u, hlu, hua⟩ := exists_between hla
  have hur : u < r := hua.trans (hap.trans (hpm.trans hmr))
  have huValues : u ∈ Set.Icc (F m) (F p) := by
    constructor
    · simpa [hFm] using hlu.le
    · exact hur.le.trans hFp
  obtain ⟨d, hdDom, hFd⟩ :=
    intermediate_value_Icc' hpm.le hF.continuousOn huValues
  have hd_ne_p : d ≠ p := by
    intro hdp
    subst d
    have hrle : r ≤ u := by simpa [hFd] using hFp
    exact (not_le_of_gt hur) hrle
  have hd_ne_m : d ≠ m := by
    intro hdm
    subst d
    have : u = l := by rw [← hFd, hFm]
    exact hlu.ne this.symm
  have hpd : p < d := lt_of_le_of_ne hdDom.1 hd_ne_p.symm
  have hdm : d < m := lt_of_le_of_ne hdDom.2 hd_ne_m
  have hdr : d < r := hdm.trans hmr
  obtain ⟨e, hde, her⟩ := exists_between hdr
  have hle : l < e := hla.trans (hap.trans (hpd.trans hde))
  have heLeftValues : e ∈ Set.Icc (F a) (F p) := by
    constructor
    · simpa [hFa] using hle.le
    · exact her.le.trans hFp
  obtain ⟨b, hbDom, hFb⟩ :=
    intermediate_value_Icc hap.le hF.continuousOn heLeftValues
  have hb_ne_a : b ≠ a := by
    intro hba
    subst b
    have : e = l := by rw [← hFb, hFa]
    exact hle.ne this.symm
  have hb_ne_p : b ≠ p := by
    intro hbp
    subst b
    have hrle : r ≤ e := by simpa [hFb] using hFp
    exact (not_le_of_gt her) hrle
  have hab : a < b := lt_of_le_of_ne hbDom.1 hb_ne_a.symm
  have hbp : b < p := lt_of_le_of_ne hbDom.2 hb_ne_p
  have hue : u < e := hua.trans (hap.trans (hpd.trans hde))
  have heRightValues : e ∈ Set.Icc (F d) (F p) := by
    constructor
    · simpa [hFd] using hue.le
    · exact her.le.trans hFp
  obtain ⟨c, hcDom, hFc⟩ :=
    intermediate_value_Icc' hpd.le hF.continuousOn heRightValues
  have hc_ne_p : c ≠ p := by
    intro hcp
    subst c
    have hrle : r ≤ e := by simpa [hFc] using hFp
    exact (not_le_of_gt her) hrle
  have hc_ne_d : c ≠ d := by
    intro hcd
    subst c
    have : e = u := by rw [← hFc, hFd]
    exact hue.ne this.symm
  have hpc : p < c := lt_of_le_of_ne hcDom.1 hc_ne_p.symm
  have hcd : c < d := lt_of_le_of_ne hcDom.2 hc_ne_d
  refine ⟨{
    a := a
    b := b
    c := c
    d := d
    a_lt_b := hab
    b_lt_c := hbp.trans hpc
    c_lt_d := hcd
    left_covers := intervalCovers_of_endpoints_mono hF hab.le
      (hab.trans (hbp.trans (hpc.trans hcd))).le
      (by simpa [hFa] using hla.le)
      (by simpa [hFb] using hde.le)
    right_covers := intervalCovers_of_endpoints_anti hF hcd.le
      (hab.trans (hbp.trans (hpc.trans hcd))).le
      (by simpa [hFd] using hua.le)
      (by simpa [hFc] using hde.le) }⟩

/-! ## The De Marr alternating configuration -/

structure MarrForwardConfiguration (P Q : IntervalMap) where
  x0 : I
  s : I
  x1 : I
  t : I
  x0_lt_s : x0 < s
  s_lt_x1 : s < x1
  x1_lt_t : x1 < t
  fixed_P_x0 : P x0 = x0
  image_P_s : P s = t
  fixed_P_x1 : P x1 = x1
  Q_x0_ge_x1 : x1 ≤ Q x0
  fixed_Q_s : Q s = s
  Q_x1_le_x0 : Q x1 ≤ x0
  fixed_Q_t : Q t = t

structure MarrBackwardConfiguration (P Q : IntervalMap) where
  t : I
  x0 : I
  s : I
  x1 : I
  t_lt_x0 : t < x0
  x0_lt_s : x0 < s
  s_lt_x1 : s < x1
  fixed_P_x0 : P x0 = x0
  image_P_s : P s = t
  fixed_P_x1 : P x1 = x1
  Q_x0_ge_x1 : x1 ≤ Q x0
  fixed_Q_s : Q s = s
  Q_x1_le_x0 : Q x1 ≤ x0
  fixed_Q_t : Q t = t

inductive MarrAlternatingConfiguration (P Q : IntervalMap)
  | forward (X : MarrForwardConfiguration P Q)
  | backward (X : MarrBackwardConfiguration P Q)

/-- Compact fixed sets and the intermediate value theorem produce one of
the two alternating De Marr configurations. -/
theorem marr_configuration_of_commuting_noCommonFixedPoint
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Function.Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Nonempty (MarrAlternatingConfiguration P Q) := by
  obtain ⟨X⟩ := exists_minimalFixedCrossingPair hP hQ hcomm hno
  have hfree : ∀ z ∈ Set.Ioo X.x0 X.x1, P z ≠ z :=
    X.no_fixed_P_between hno
  have hgapNonempty :
      (gapFixedPoints Q X.x0 X.x1).Nonempty :=
    gapFixedPoints_nonempty hQ X.x0_lt_x1.le
      X.Q_moves_x0_right.le X.Q_moves_x1_left.le
  obtain ⟨r, hrfixed, hrIcc⟩ := hgapNonempty
  have hr_ne_x0 : r ≠ X.x0 := by
    intro heq
    apply hno
    subst r
    exact ⟨X.x0, X.fixed_P_x0, hrfixed⟩
  have hr_ne_x1 : r ≠ X.x1 := by
    intro heq
    apply hno
    subst r
    exact ⟨X.x1, X.fixed_P_x1, hrfixed⟩
  have hrIoo : r ∈ Set.Ioo X.x0 X.x1 :=
    ⟨lt_of_le_of_ne hrIcc.1 hr_ne_x0.symm,
      lt_of_le_of_ne hrIcc.2 hr_ne_x1⟩
  rcases lt_or_gt_of_ne (hfree r hrIoo) with hrleft | hrright
  · obtain ⟨s, hsmem, hsmin⟩ :=
      gapFixedPoints_has_least hQ ⟨r, hrfixed, hrIcc⟩
    rcases hsmem with ⟨hsfixed, hsIcc⟩
    have hs_ne_x0 : s ≠ X.x0 := by
      intro heq
      apply hno
      subst s
      exact ⟨X.x0, X.fixed_P_x0, hsfixed⟩
    have hs_ne_x1 : s ≠ X.x1 := by
      intro heq
      apply hno
      subst s
      exact ⟨X.x1, X.fixed_P_x1, hsfixed⟩
    have hsIoo : s ∈ Set.Ioo X.x0 X.x1 :=
      ⟨lt_of_le_of_ne hsIcc.1 hs_ne_x0.symm,
        lt_of_le_of_ne hsIcc.2 hs_ne_x1⟩
    have hPs_left : P s < s :=
      gap_moves_left hP hrIoo hfree hrleft s hsIoo
    have hQPs : Q (P s) = P s := by
      calc
        Q (P s) = P (Q s) := (hcomm s).symm
        _ = P s := by rw [hsfixed]
    have hPs_lt_x0 : P s < X.x0 := by
      by_contra hnot
      have hx0lePs : X.x0 ≤ P s := le_of_not_gt hnot
      have hPsMem : P s ∈ gapFixedPoints Q X.x0 X.x1 :=
        ⟨hQPs, hx0lePs, hPs_left.le.trans hsIcc.2⟩
      exact (not_le_of_gt hPs_left) (hsmin (P s) hPsMem)
    exact ⟨MarrAlternatingConfiguration.backward {
      t := P s
      x0 := X.x0
      s := s
      x1 := X.x1
      t_lt_x0 := hPs_lt_x0
      x0_lt_s := hsIoo.1
      s_lt_x1 := hsIoo.2
      fixed_P_x0 := X.fixed_P_x0
      image_P_s := rfl
      fixed_P_x1 := X.fixed_P_x1
      Q_x0_ge_x1 := X.Q_x0_ge_x1 hcomm hno
      fixed_Q_s := hsfixed
      Q_x1_le_x0 := X.Q_x1_le_x0 hcomm hno
      fixed_Q_t := hQPs }⟩
  · obtain ⟨s, hsmem, hsmax⟩ :=
      gapFixedPoints_has_greatest hQ ⟨r, hrfixed, hrIcc⟩
    rcases hsmem with ⟨hsfixed, hsIcc⟩
    have hs_ne_x0 : s ≠ X.x0 := by
      intro heq
      apply hno
      subst s
      exact ⟨X.x0, X.fixed_P_x0, hsfixed⟩
    have hs_ne_x1 : s ≠ X.x1 := by
      intro heq
      apply hno
      subst s
      exact ⟨X.x1, X.fixed_P_x1, hsfixed⟩
    have hsIoo : s ∈ Set.Ioo X.x0 X.x1 :=
      ⟨lt_of_le_of_ne hsIcc.1 hs_ne_x0.symm,
        lt_of_le_of_ne hsIcc.2 hs_ne_x1⟩
    have hs_lt_Ps : s < P s :=
      gap_moves_right hP hrIoo hfree hrright s hsIoo
    have hQPs : Q (P s) = P s := by
      calc
        Q (P s) = P (Q s) := (hcomm s).symm
        _ = P s := by rw [hsfixed]
    have hx1_lt_Ps : X.x1 < P s := by
      by_contra hnot
      have hPsleX1 : P s ≤ X.x1 := le_of_not_gt hnot
      have hPsMem : P s ∈ gapFixedPoints Q X.x0 X.x1 :=
        ⟨hQPs, hsIcc.1.trans hs_lt_Ps.le, hPsleX1⟩
      exact (not_le_of_gt hs_lt_Ps) (hsmax (P s) hPsMem)
    exact ⟨MarrAlternatingConfiguration.forward {
      x0 := X.x0
      s := s
      x1 := X.x1
      t := P s
      x0_lt_s := hsIoo.1
      s_lt_x1 := hsIoo.2
      x1_lt_t := hx1_lt_Ps
      fixed_P_x0 := X.fixed_P_x0
      image_P_s := rfl
      fixed_P_x1 := X.fixed_P_x1
      Q_x0_ge_x1 := X.Q_x0_ge_x1 hcomm hno
      fixed_Q_s := hsfixed
      Q_x1_le_x0 := X.Q_x1_le_x0 hcomm hno
      fixed_Q_t := hQPs }⟩

namespace MarrForwardConfiguration

theorem middle_covers_hull
    {P Q : IntervalMap} (X : MarrForwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Function.Commute P Q) :
    IntervalCovers (P ∘ Q) X.s X.x1 X.x0 X.t := by
  have hHcont : Continuous (P ∘ Q) := hP.comp hQ
  have hHs : (P ∘ Q) X.s = X.t := by
    simp only [Function.comp_apply, X.fixed_Q_s, X.image_P_s]
  have hHx1 : (P ∘ Q) X.x1 = Q X.x1 := by
    change P (Q X.x1) = Q X.x1
    rw [hcomm X.x1, X.fixed_P_x1]
  apply intervalCovers_of_endpoints_anti hHcont X.s_lt_x1.le
    (X.x0_lt_s.trans (X.s_lt_x1.trans X.x1_lt_t)).le
  · rw [hHx1]
    exact X.Q_x1_le_x0
  · rw [hHs]

theorem right_covers_hull
    {P Q : IntervalMap} (X : MarrForwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (_hcomm : Function.Commute P Q) :
    IntervalCovers (P ∘ Q) X.x1 X.t X.x0 X.t := by
  have hQcover : IntervalCovers Q X.x1 X.t X.x0 X.t := by
    apply intervalCovers_of_endpoints_mono hQ X.x1_lt_t.le
      (X.x0_lt_s.trans (X.s_lt_x1.trans X.x1_lt_t)).le
    · exact X.Q_x1_le_x0
    · simp [X.fixed_Q_t]
  have hPsmall : IntervalCovers P X.x0 X.s X.x0 X.t := by
    apply intervalCovers_of_endpoints_mono hP X.x0_lt_s.le
      (X.x0_lt_s.trans (X.s_lt_x1.trans X.x1_lt_t)).le
    · simp [X.fixed_P_x0]
    · simp [X.image_P_s]
  have hPwide : IntervalCovers P X.x0 X.t X.x0 X.t := by
    apply hPsmall.mono_domain
    intro z hz
    exact ⟨hz.1, hz.2.trans (X.s_lt_x1.trans X.x1_lt_t).le⟩
  exact hQcover.comp hPwide

theorem composite_horseshoe
    {P Q : IntervalMap} (X : MarrForwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Function.Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Nonempty (TwoBranchHorseshoe (P ∘ Q)) := by
  have hHcont : Continuous (P ∘ Q) := hP.comp hQ
  have hHs : (P ∘ Q) X.s = X.t := by
    simp only [Function.comp_apply, X.fixed_Q_s, X.image_P_s]
  have hHx1 : (P ∘ Q) X.x1 ≤ X.x0 := by
    change P (Q X.x1) ≤ X.x0
    rw [hcomm X.x1, X.fixed_P_x1]
    exact X.Q_x1_le_x0
  have hHt_ne : (P ∘ Q) X.t ≠ X.t := by
    intro hHt
    apply hno
    refine ⟨X.t, ?_, X.fixed_Q_t⟩
    change P X.t = X.t
    simpa only [Function.comp_apply, X.fixed_Q_t] using hHt
  exact strict_horseshoe_of_forward_adjacent_branches hHcont
    X.x0_lt_s X.s_lt_x1 X.x1_lt_t hHs hHx1
    (X.right_covers_hull hP hQ hcomm) hHt_ne

end MarrForwardConfiguration

namespace MarrBackwardConfiguration

theorem left_covers_hull
    {P Q : IntervalMap} (X : MarrBackwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (_hcomm : Function.Commute P Q) :
    IntervalCovers (P ∘ Q) X.t X.x0 X.t X.x1 := by
  have hQcover : IntervalCovers Q X.t X.x0 X.t X.x1 := by
    apply intervalCovers_of_endpoints_mono hQ X.t_lt_x0.le
      (X.t_lt_x0.trans (X.x0_lt_s.trans X.s_lt_x1)).le
    · simp [X.fixed_Q_t]
    · exact X.Q_x0_ge_x1
  have hPsmall : IntervalCovers P X.s X.x1 X.t X.x1 := by
    apply intervalCovers_of_endpoints_mono hP X.s_lt_x1.le
      (X.t_lt_x0.trans (X.x0_lt_s.trans X.s_lt_x1)).le
    · simp [X.image_P_s]
    · simp [X.fixed_P_x1]
  have hPwide : IntervalCovers P X.t X.x1 X.t X.x1 := by
    apply hPsmall.mono_domain
    intro z hz
    exact ⟨(X.t_lt_x0.trans X.x0_lt_s).le.trans hz.1, hz.2⟩
  exact hQcover.comp hPwide

theorem middle_covers_hull
    {P Q : IntervalMap} (X : MarrBackwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Function.Commute P Q) :
    IntervalCovers (P ∘ Q) X.x0 X.s X.t X.x1 := by
  have hHcont : Continuous (P ∘ Q) := hP.comp hQ
  have hHs : (P ∘ Q) X.s = X.t := by
    simp only [Function.comp_apply, X.fixed_Q_s, X.image_P_s]
  have hHx0 : (P ∘ Q) X.x0 = Q X.x0 := by
    change P (Q X.x0) = Q X.x0
    rw [hcomm X.x0, X.fixed_P_x0]
  apply intervalCovers_of_endpoints_anti hHcont X.x0_lt_s.le
    (X.t_lt_x0.trans (X.x0_lt_s.trans X.s_lt_x1)).le
  · rw [hHs]
  · rw [hHx0]
    exact X.Q_x0_ge_x1

theorem composite_horseshoe
    {P Q : IntervalMap} (X : MarrBackwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Function.Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Nonempty (TwoBranchHorseshoe (P ∘ Q)) := by
  have hHcont : Continuous (P ∘ Q) := hP.comp hQ
  have hHt_ne : (P ∘ Q) X.t ≠ X.t := by
    intro hHt
    apply hno
    refine ⟨X.t, ?_, X.fixed_Q_t⟩
    change P X.t = X.t
    simpa only [Function.comp_apply, X.fixed_Q_t] using hHt
  have hHx0 : X.x1 ≤ (P ∘ Q) X.x0 := by
    change X.x1 ≤ P (Q X.x0)
    rw [hcomm X.x0, X.fixed_P_x0]
    exact X.Q_x0_ge_x1
  have hHs : (P ∘ Q) X.s = X.t := by
    simp only [Function.comp_apply, X.fixed_Q_s, X.image_P_s]
  exact strict_horseshoe_of_backward_adjacent_branches hHcont
    X.t_lt_x0 X.x0_lt_s X.s_lt_x1 hHt_ne hHx0 hHs
    (X.left_covers_hull hP hQ hcomm)

end MarrBackwardConfiguration

/-- The first commuting product itself has a separated two-branch
horseshoe; no iterate and no exactness assumption are required. -/
theorem commuting_noCommonFixedPoint_product_horseshoe
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Function.Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Nonempty (TwoBranchHorseshoe (P ∘ Q)) := by
  obtain ⟨X⟩ :=
    marr_configuration_of_commuting_noCommonFixedPoint hP hQ hcomm hno
  cases X with
  | forward X => exact X.composite_horseshoe hP hQ hcomm hno
  | backward X => exact X.composite_horseshoe hP hQ hcomm hno

end CommutingIntervalSimplified
