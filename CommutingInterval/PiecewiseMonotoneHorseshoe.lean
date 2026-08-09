import CommutingInterval.PiecewiseMonotoneReduction
import CommutingInterval.Basic

/-!
# A direct Marr horseshoe for commuting interval maps

This file proves the exact geometric input consumed by the
piecewise-monotone argument.  No entropy theory is used.  The proof has four
layers:

1. choose a closest ordered pair of fixed points of one map on which the
   other map crosses in opposite directions;
2. use the fixed-point-free gap to obtain the (forward or backward) De Marr
   alternating configuration;
3. turn the configuration into two adjacent full branches for the commuting
   composite by intermediate-value arguments; and
4. trim those branches, with explicit strict margins, to a genuinely
   separated two-branch horseshoe.

The published Bogatyi--Frolkina incidence graph is therefore unnecessary for
the consumed conclusion: the first composite itself has the horseshoe, so the
eventual statement below uses the iterate `N = 1`.
-/

namespace CommutingInterval

open Function Set

/-! ## Interval covering and horseshoes -/

/-- The image of `[a,b]` under `F` covers `[c,d]`. -/
def IntervalCovers (F : IntervalMap) (a b c d : I) : Prop :=
  Set.Icc c d ⊆ F '' Set.Icc a b

/-- Two strictly separated closed branches whose images cover their common
hull. -/
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

/-- Endpoint order and the intermediate value theorem give a covering
relation. -/
theorem intervalCovers_of_endpoints_mono
    {F : IntervalMap} (hF : Continuous F)
    {a b c d : I} (hab : a ≤ b) (_hcd : c ≤ d)
    (hleft : F a ≤ c) (hright : d ≤ F b) :
    IntervalCovers F a b c d := by
  intro y hy
  apply intermediate_value_Icc hab hF.continuousOn
  exact ⟨hleft.trans hy.1, hy.2.trans hright⟩

/-- The reversed endpoint order gives the same covering relation. -/
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

theorem IntervalCovers.mono_target
    {F : IntervalMap} {a b c d c' d' : I}
    (h : IntervalCovers F a b c d)
    (hsub : Set.Icc c' d' ⊆ Set.Icc c d) :
    IntervalCovers F a b c' d' := by
  exact fun _ hy ↦ h (hsub hy)

/-- Covering relations compose in the same order as maps. -/
theorem IntervalCovers.comp
    {P Q : IntervalMap} {a b c d e f : I}
    (hQ : IntervalCovers Q a b c d)
    (hP : IntervalCovers P c d e f) :
    IntervalCovers (P ∘ Q) a b e f := by
  intro y hy
  obtain ⟨z, hz, hPzy⟩ := hP hy
  obtain ⟨x, hx, hQxz⟩ := hQ hz
  refine ⟨x, hx, ?_⟩
  change P (Q x) = y
  rw [hQxz, hPzy]

/-- The elementary iterate-transport step for a finite covering path. -/
theorem IntervalCovers.iterate_succ
    {F : IntervalMap} {n : ℕ} {a b c d e f : I}
    (hpath : IntervalCovers (iterateMap F n) a b c d)
    (hstep : IntervalCovers F c d e f) :
    IntervalCovers (iterateMap F (n + 1)) a b e f := by
  simpa only [iterateMap, Function.iterate_succ'] using hpath.comp hstep

/-! ## Exactness produces an iterate horseshoe -/

/-- Two separated open intervals which both map onto the whole unit interval
contain two separated closed full branches. -/
theorem twoBranchHorseshoe_of_two_full_open_intervals
    {F : IntervalMap} (hF : Continuous F)
    {u₀ u₁ v₀ v₁ : I} (hu : u₀ < u₁) (hsep : u₁ < v₀)
    (hv : v₀ < v₁)
    (hleft : F '' Set.Ioo u₀ u₁ = Set.univ)
    (hright : F '' Set.Ioo v₀ v₁ = Set.univ) :
    Nonempty (TwoBranchHorseshoe F) := by
  have hleft0 : leftEndpoint ∈ F '' Set.Ioo u₀ u₁ := by
    rw [hleft]
    exact Set.mem_univ leftEndpoint
  have hleft1 : rightEndpoint ∈ F '' Set.Ioo u₀ u₁ := by
    rw [hleft]
    exact Set.mem_univ rightEndpoint
  rcases hleft0 with ⟨a₀, ha₀, hFa₀⟩
  rcases hleft1 with ⟨a₁, ha₁, hFa₁⟩
  have ha_ne : a₀ ≠ a₁ := by
    intro h
    have hend : leftEndpoint = rightEndpoint := by
      calc
        leftEndpoint = F a₀ := hFa₀.symm
        _ = F a₁ := congrArg F h
        _ = rightEndpoint := hFa₁
    exact (by norm_num [leftEndpoint, rightEndpoint] at hend)
  have hright0 : leftEndpoint ∈ F '' Set.Ioo v₀ v₁ := by
    rw [hright]
    exact Set.mem_univ leftEndpoint
  have hright1 : rightEndpoint ∈ F '' Set.Ioo v₀ v₁ := by
    rw [hright]
    exact Set.mem_univ rightEndpoint
  rcases hright0 with ⟨b₀, hb₀, hFb₀⟩
  rcases hright1 with ⟨b₁, hb₁, hFb₁⟩
  have hb_ne : b₀ ≠ b₁ := by
    intro h
    have hend : leftEndpoint = rightEndpoint := by
      calc
        leftEndpoint = F b₀ := hFb₀.symm
        _ = F b₁ := congrArg F h
        _ = rightEndpoint := hFb₁
    exact (by norm_num [leftEndpoint, rightEndpoint] at hend)
  let a := min a₀ a₁
  let b := max a₀ a₁
  let c := min b₀ b₁
  let d := max b₀ b₁
  have hab : a < b := by
    exact min_lt_max.mpr ha_ne
  have hbc : b < c := by
    exact (max_lt ha₀.2 ha₁.2).trans
      (hsep.trans (lt_min hb₀.1 hb₁.1))
  have hcd : c < d := by
    exact min_lt_max.mpr hb_ne
  have hfullLeft : IntervalCovers F a b leftEndpoint rightEndpoint := by
    rcases lt_or_gt_of_ne ha_ne with ha | ha
    · apply intervalCovers_of_endpoints_mono hF hab.le
        (by norm_num [leftEndpoint, rightEndpoint])
      · simpa [a, min_eq_left ha.le, hFa₀]
      · simpa [b, max_eq_right ha.le, hFa₁]
    · apply intervalCovers_of_endpoints_anti hF hab.le
        (by norm_num [leftEndpoint, rightEndpoint])
      · simpa [b, max_eq_left ha.le, hFa₀]
      · simpa [a, min_eq_right ha.le, hFa₁]
  have hfullRight : IntervalCovers F c d leftEndpoint rightEndpoint := by
    rcases lt_or_gt_of_ne hb_ne with hb | hb
    · apply intervalCovers_of_endpoints_mono hF hcd.le
        (by norm_num [leftEndpoint, rightEndpoint])
      · simpa [c, min_eq_left hb.le, hFb₀]
      · simpa [d, max_eq_right hb.le, hFb₁]
    · apply intervalCovers_of_endpoints_anti hF hcd.le
        (by norm_num [leftEndpoint, rightEndpoint])
      · simpa [d, max_eq_left hb.le, hFb₀]
      · simpa [c, min_eq_right hb.le, hFb₁]
  have htarget : Set.Icc a d ⊆ Set.Icc leftEndpoint rightEndpoint := by
    intro z _hz
    exact ⟨z.property.1, z.property.2⟩
  exact ⟨
    { a := a
      b := b
      c := c
      d := d
      a_lt_b := hab
      b_lt_c := hbc
      c_lt_d := hcd
      left_covers := hfullLeft.mono_target htarget
      right_covers := hfullRight.mono_target htarget }⟩

/-- A topologically exact interval map is onto. -/
theorem onto_of_topologicallyExact {T : IntervalMap}
    (hExact : IsTopologicallyExact T) : IsOnto T := by
  let U : Set I := Set.Iio rightEndpoint
  have hUopen : IsOpen U := isOpen_Iio
  have hUne : U.Nonempty := by
    exact ⟨leftEndpoint, by simp [U, leftEndpoint, rightEndpoint]⟩
  obtain ⟨n, hn⟩ := hExact U hUopen hUne
  have hnpos : 0 < n := by
    by_contra hnnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnnot
    subst n
    have hright : rightEndpoint ∈ iterateMap T 0 '' U := by
      rw [hn]
      exact Set.mem_univ rightEndpoint
    rcases hright with ⟨x, hx, hxeq⟩
    have : x = rightEndpoint := by simpa [iterateMap] using hxeq
    subst x
    exact (lt_irrefl rightEndpoint) hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnpos.ne'
  intro y
  have hy : y ∈ iterateMap T (k + 1) '' U := by
    rw [hn]
    exact Set.mem_univ y
  rcases hy with ⟨x, _hx, hxy⟩
  refine ⟨iterateMap T k x, ?_⟩
  simpa only [iterateMap, Function.iterate_succ_apply'] using hxy

/-- Every continuous topologically exact interval map has a positive iterate
with a two-branch horseshoe. -/
theorem twoBranchHorseshoe_iterate_exists_of_topologicallyExact
    {T : IntervalMap} (hT : Continuous T)
    (hExact : IsTopologicallyExact T) :
    ∃ N : ℕ, 0 < N ∧
      Nonempty (TwoBranchHorseshoe (iterateMap T N)) := by
  let u₀ : I := ⟨(1 : ℝ) / 5, by norm_num, by norm_num⟩
  let u₁ : I := ⟨(2 : ℝ) / 5, by norm_num, by norm_num⟩
  let v₀ : I := ⟨(3 : ℝ) / 5, by norm_num, by norm_num⟩
  let v₁ : I := ⟨(4 : ℝ) / 5, by norm_num, by norm_num⟩
  have hu : u₀ < u₁ := by norm_num [u₀, u₁]
  have hsep : u₁ < v₀ := by norm_num [u₁, v₀]
  have hv : v₀ < v₁ := by norm_num [v₀, v₁]
  let U : Set I := Set.Ioo u₀ u₁
  let V : Set I := Set.Ioo v₀ v₁
  obtain ⟨n, hn⟩ := hExact U isOpen_Ioo (Set.nonempty_Ioo.mpr hu)
  obtain ⟨m, hm⟩ := hExact V isOpen_Ioo (Set.nonempty_Ioo.mpr hv)
  have hnpos : 0 < n := by
    by_contra hnnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnnot
    subst n
    have hleft : leftEndpoint ∈ iterateMap T 0 '' U := by
      rw [hn]
      exact Set.mem_univ leftEndpoint
    rcases hleft with ⟨x, hxU, hxeq⟩
    have hx : x = leftEndpoint := by simpa [iterateMap] using hxeq
    subst x
    exact (not_lt_of_ge (show leftEndpoint ≤ u₀ by
      exact u₀.property.1)) hxU.1
  have hmpos : 0 < m := by
    by_contra hmnot
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hmnot
    subst m
    have hleft : leftEndpoint ∈ iterateMap T 0 '' V := by
      rw [hm]
      exact Set.mem_univ leftEndpoint
    rcases hleft with ⟨x, hxV, hxeq⟩
    have hx : x = leftEndpoint := by simpa [iterateMap] using hxeq
    subst x
    exact (not_lt_of_ge (show leftEndpoint ≤ v₀ by
      exact v₀.property.1)) hxV.1
  have honto : Function.Surjective T := onto_of_topologicallyExact hExact
  let N := n + m
  have hUN : iterateMap T N '' U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨z, hz⟩ := IntervalMap.surjective_iterate honto m y
    have hzU : z ∈ iterateMap T n '' U := by
      rw [hn]
      exact Set.mem_univ z
    rcases hzU with ⟨x, hxU, hxz⟩
    change (T^[n]) x = z at hxz
    refine ⟨x, hxU, ?_⟩
    change (T^[N]) x = y
    rw [show N = m + n by simp [N, Nat.add_comm],
      Function.iterate_add_apply, hxz, hz]
  have hVN : iterateMap T N '' V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨z, hz⟩ := IntervalMap.surjective_iterate honto n y
    have hzV : z ∈ iterateMap T m '' V := by
      rw [hm]
      exact Set.mem_univ z
    rcases hzV with ⟨x, hxV, hxz⟩
    change (T^[m]) x = z at hxz
    refine ⟨x, hxV, ?_⟩
    change (T^[N]) x = y
    rw [show N = n + m by rfl, Function.iterate_add_apply, hxz, hz]
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  exact twoBranchHorseshoe_of_two_full_open_intervals
    (IntervalMap.continuous_iterate hT N) hu hsep hv hUN hVN

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
    (hcomm : Commute P Q) : MapsTo Q (fixedPoints P) (fixedPoints P) := by
  intro x hx
  change P x = x at hx
  change P (Q x) = Q x
  rw [hcomm x, hx]

/-- A closest ordered pair in `Fix(P)` where `Q` moves the left point right
and the right point left. -/
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

/-- Compactness of the two closed sign sets supplies the closest crossing
pair.  Weak sign inequalities are used for compactness and become strict
because a common equality would be a common fixed point. -/
theorem exists_minimalFixedCrossingPair
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
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
  have hxmin_rising : xmin ∈ rising := by
    exact ⟨hxmin, hxmin_le hQxmin⟩
  have hxmax_falling : xmax ∈ falling := by
    exact ⟨hxmax, hxmax_ge hQxmax⟩
  have hxmin_le_xmax : xmin ≤ xmax := hxmin_le hxmax
  have hpairsNonempty : pairs.Nonempty := by
    exact ⟨(xmin, xmax), ⟨⟨hxmin_rising, hxmax_falling⟩,
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

theorem Q_x0_ge_x1
    {P Q : IntervalMap} (X : MinimalFixedCrossingPair P Q)
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    X.x1 ≤ Q X.x0 := by
  have hfixed : P (Q X.x0) = Q X.x0 := by
    have hx0mem : X.x0 ∈ fixedPoints P := X.fixed_P_x0
    exact commute_mapsTo_fixedPoints hcomm hx0mem
  by_contra hge
  have hinside : Q X.x0 ∈ Set.Ioo X.x0 X.x1 :=
    ⟨X.Q_moves_x0_right, lt_of_not_ge hge⟩
  exact X.no_fixed_P_between hno (Q X.x0) hinside hfixed

theorem Q_x1_le_x0
    {P Q : IntervalMap} (X : MinimalFixedCrossingPair P Q)
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Q X.x1 ≤ X.x0 := by
  have hfixed : P (Q X.x1) = Q X.x1 := by
    have hx1mem : X.x1 ∈ fixedPoints P := X.fixed_P_x1
    exact commute_mapsTo_fixedPoints hcomm hx1mem
  by_contra hle
  have hinside : Q X.x1 ∈ Set.Ioo X.x0 X.x1 :=
    ⟨lt_of_not_ge hle, X.Q_moves_x1_left⟩
  exact X.no_fixed_P_between hno (Q X.x1) hinside hfixed

end MinimalFixedCrossingPair

/-! ## The fixed-point-free gap and Marr configurations -/

/-- On an interval containing no fixed point, one strict displacement fixes
the displacement direction everywhere. -/
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

/-- Fixed points of `T` in the closed gap. -/
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

/-- The orientation used on the printed page of Bogatyi--Frolkina. -/
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

/-- The reflected orientation; retaining it avoids hiding a conjugacy step. -/
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

/-- The exact order-theoretic output of the De Marr argument. -/
inductive MarrAlternatingConfiguration (P Q : IntervalMap)
  | forward (X : MarrForwardConfiguration P Q)
  | backward (X : MarrBackwardConfiguration P Q)

/-- The substantive interval-order lemma, proved from compact fixed sets,
commutation, and the intermediate value theorem. -/
theorem marr_configuration_of_commuting_noCommonFixedPoint
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
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
  have hrIoo : r ∈ Set.Ioo X.x0 X.x1 := by
    exact ⟨lt_of_le_of_ne hrIcc.1 hr_ne_x0.symm,
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
      have hPsMem : P s ∈ gapFixedPoints Q X.x0 X.x1 := by
        exact ⟨hQPs, hx0lePs, hPs_left.le.trans hsIcc.2⟩
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
      have hPsMem : P s ∈ gapFixedPoints Q X.x0 X.x1 := by
        exact ⟨hQPs, hsIcc.1.trans (hs_lt_Ps.le), hPsleX1⟩
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

/-! ## Strict-margin trimming -/

/-- Forward strict-margin lemma.  It explicitly handles the possible
equality `F m = l`: a preimage of `r` on the right full branch is first moved
strictly away from both `m` and `r`, and three further IVT levels provide the
strict gaps. -/
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

/-- Reflected strict-margin lemma. -/
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

/-! ## From Marr to the first-composite horseshoe -/

namespace MarrForwardConfiguration

theorem middle_covers_hull
    {P Q : IntervalMap} (X : MarrForwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q) :
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
    (_hcomm : Commute P Q) :
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
    exact ⟨hz.1, hz.2.trans
      (X.s_lt_x1.trans X.x1_lt_t).le⟩
  exact hQcover.comp hPwide

theorem composite_horseshoe
    {P Q : IntervalMap} (X : MarrForwardConfiguration P Q)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
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
    (_hcomm : Commute P Q) :
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
    (hcomm : Commute P Q) :
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
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
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

/-- Direct no-common-fixed-point horseshoe theorem. -/
theorem commuting_noCommonFixedPoint_horseshoe
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    Nonempty (TwoBranchHorseshoe (P ∘ Q)) := by
  obtain ⟨X⟩ :=
    marr_configuration_of_commuting_noCommonFixedPoint hP hQ hcomm hno
  cases X with
  | forward X => exact X.composite_horseshoe hP hQ hcomm hno
  | backward X => exact X.composite_horseshoe hP hQ hcomm hno

/-- Compatibility interface requested by the manuscript: the direct theorem
already supplies `N = 1`. -/
theorem commuting_noCommonFixedPoint_eventual_horseshoe
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q) (hno : ¬HasCommonFixedPoint P Q) :
    ∃ N : ℕ, 0 < N ∧
      Nonempty (TwoBranchHorseshoe (iterateMap (P ∘ Q) N)) := by
  refine ⟨1, by simp, ?_⟩
  simpa [iterateMap] using
    commuting_noCommonFixedPoint_horseshoe hP hQ hcomm hno

namespace MinimalPiecewiseMonotoneCounterexample

theorem eventual_horseshoe (C : MinimalPiecewiseMonotoneCounterexample) :
    ∃ N : ℕ, 0 < N ∧
      Nonempty (TwoBranchHorseshoe (iterateMap C.H N)) := by
  simpa [H] using commuting_noCommonFixedPoint_eventual_horseshoe
    C.finitePiece_P.continuous C.finitePiece_Q.continuous
      C.commute C.no_common_fixed_point

end MinimalPiecewiseMonotoneCounterexample

end CommutingInterval
