import CommutingIntervalSimplified.PiecewiseMonotoneBase

/-!
# Intrinsic turns of flat-free polygonal interval maps

This file develops the one-sided strict-direction calculus needed to work
with genuine turns rather than arbitrary vertices of a chosen polygonal
presentation.  In particular, it proves exact composition formulae for the
intrinsic endpoint-and-turn domain and its image.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set Filter
open scoped Topology

/-! ## Strict directions on one-sided germs -/

private inductive TurnDirection where
  | inc
  | dec
  deriving DecidableEq

private def TurnDirection.Holds (d : TurnDirection) (T : IntervalMap)
    (s : Set I) : Prop :=
  match d with
  | .inc => StrictMonoOn T s
  | .dec => StrictAntiOn T s

private def TurnDirection.mul :
    TurnDirection → TurnDirection → TurnDirection
  | .inc, .inc => .inc
  | .inc, .dec => .dec
  | .dec, .inc => .dec
  | .dec, .dec => .inc

private def HasLeftTurnDirection (d : TurnDirection)
    (T : IntervalMap) (x : I) : Prop :=
  ∃ a : I, a < x ∧ d.Holds T (Set.Icc a x)

private def HasRightTurnDirection (d : TurnDirection)
    (T : IntervalMap) (x : I) : Prop :=
  ∃ b : I, x < b ∧ d.Holds T (Set.Icc x b)

/-- On every cell of a flat-free finite-piece affine map, the affine slope
is nonzero, and hence the map is strictly monotone in one direction. -/
private theorem finitePiecePL_noFlat_strictLaps
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hflat : ¬HasFlatInterval T) :
    ∃ p : RealPartition, ∀ {a b : ℝ}, p.Adjacent a b →
      StrictMonoOn T (intervalCell a b) ∨
        StrictAntiOn T (intervalCell a b) := by
  rcases hT.2 with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  intro a b hab
  rcases hp hab with ⟨m, c, hformula⟩
  have hm : m ≠ 0 := by
    intro hm0
    apply hflat
    let aI : I := ⟨a, p.points_subset hab.1⟩
    let bI : I := ⟨b, p.points_subset hab.2.1⟩
    let J : ClosedSubinterval := ⟨aI, bI, hab.2.2.1.le⟩
    refine ⟨J, hab.2.2.1, ?_⟩
    intro x hx y hy
    apply Subtype.ext
    have hxcell : x ∈ intervalCell a b := hx
    have hycell : y ∈ intervalCell a b := hy
    simp [hformula x hxcell, hformula y hycell, hm0]
  rcases lt_or_gt_of_ne hm with hmneg | hmpos
  · right
    intro x hx y hy hxy
    apply Subtype.coe_lt_coe.mp
    rw [hformula x hx, hformula y hy]
    have hxy' : (x : ℝ) < (y : ℝ) := hxy
    nlinarith
  · left
    intro x hx y hy hxy
    apply Subtype.coe_lt_coe.mp
    rw [hformula x hx, hformula y hy]
    have hxy' : (x : ℝ) < (y : ℝ) := hxy
    nlinarith

/-- A point which is not a partition vertex lies strictly inside a cell. -/
private theorem RealPartition.exists_adjacent_around_turn
    (p : RealPartition) {x : ℝ} (hxI : x ∈ I)
    (hx : x ∉ p.points) :
    ∃ c d, p.Adjacent c d ∧ c < x ∧ x < d := by
  classical
  let lower := p.points.filter fun z ↦ z ≤ x
  let upper := p.points.filter fun z ↦ x ≤ z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, p.zero_mem, hxI.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    simp [upper, p.one_mem, hxI.2]
  obtain ⟨c, hc, hcmax⟩ := lower.exists_max_image id hlower
  obtain ⟨d, hd, hdmin⟩ := upper.exists_min_image id hupper
  have hc' := Finset.mem_filter.mp hc
  have hd' := Finset.mem_filter.mp hd
  have hcx : c < x :=
    lt_of_le_of_ne hc'.2 (fun h ↦ hx (by simpa [h] using hc'.1))
  have hxd : x < d :=
    lt_of_le_of_ne hd'.2 (fun h ↦ hx (by simpa [h] using hd'.1))
  refine ⟨c, d, ⟨hc'.1, hd'.1, hcx.trans hxd, ?_⟩, hcx, hxd⟩
  intro e he hed
  by_cases hex : e ≤ x
  · have helower : e ∈ lower := Finset.mem_filter.mpr ⟨he, hex⟩
    have hec : e ≤ c := by simpa using hcmax e helower
    exact (not_lt_of_ge hec) hed.1
  · have hxe : x ≤ e := (lt_of_not_ge hex).le
    have heupper : e ∈ upper := Finset.mem_filter.mpr ⟨he, hxe⟩
    have hde : d ≤ e := by simpa using hdmin e heupper
    exact (not_lt_of_ge hde) hed.2

/-- A finite partition has a cell containing a terminal interval on the
left of any non-left-endpoint. -/
private theorem RealPartition.exists_left_cell_turn
    (p : RealPartition) {x : I} (hx : leftEndpoint < x) :
    ∃ a : I, ∃ c d : ℝ, a < x ∧ p.Adjacent c d ∧
      Set.Icc a x ⊆ intervalCell c d := by
  classical
  let lower := p.points.filter fun z ↦ z < (x : ℝ)
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    have hx0 : (0 : ℝ) < x := hx
    simp [lower, p.zero_mem, hx0]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  have ha' := Finset.mem_filter.mp ha
  let aI : I := ⟨a, p.points_subset ha'.1⟩
  have hax : aI < x := ha'.2
  have hnone : ∀ z ∈ p.points, ¬(a < z ∧ z < (x : ℝ)) := by
    intro z hz hbetween
    have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hbetween.2⟩
    have hza : z ≤ a := by simpa using hamax z hzlower
    exact (not_lt_of_ge hza) hbetween.1
  obtain ⟨c, d, hcd, hsub⟩ := p.exists_adjacent_superset
    aI.property x.property hax hnone
  exact ⟨aI, c, d, hax, hcd, fun _ hz ↦ hsub hz⟩

/-- Right-sided counterpart of `RealPartition.exists_left_cell_turn`. -/
private theorem RealPartition.exists_right_cell_turn
    (p : RealPartition) {x : I} (hx : x < rightEndpoint) :
    ∃ b : I, ∃ c d : ℝ, x < b ∧ p.Adjacent c d ∧
      Set.Icc x b ⊆ intervalCell c d := by
  classical
  let upper := p.points.filter fun z ↦ (x : ℝ) < z
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have hx1 : (x : ℝ) < 1 := hx
    simp [upper, p.one_mem, hx1]
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have hb' := Finset.mem_filter.mp hb
  let bI : I := ⟨b, p.points_subset hb'.1⟩
  have hxb : x < bI := hb'.2
  have hnone : ∀ z ∈ p.points, ¬((x : ℝ) < z ∧ z < b) := by
    intro z hz hbetween
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hbetween.1⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hbetween.2
  obtain ⟨c, d, hcd, hsub⟩ := p.exists_adjacent_superset
    x.property bI.property hxb hnone
  exact ⟨bI, c, d, hxb, hcd, fun _ hz ↦ hsub hz⟩

private theorem hasLeftTurnDirection_of_pl
    {T : IntervalMap} (hflat : ¬HasFlatInterval T)
    (hPL : FinitePiecePL T) {x : I} (hx : leftEndpoint < x) :
    ∃ d, HasLeftTurnDirection d T x := by
  obtain ⟨p, hp⟩ := finitePiecePL_noFlat_strictLaps hPL hflat
  obtain ⟨a, c, d, hax, hcd, hsub⟩ := p.exists_left_cell_turn hx
  rcases hp hcd with hmono | hanti
  · exact ⟨.inc, a, hax, hmono.mono hsub⟩
  · exact ⟨.dec, a, hax, hanti.mono hsub⟩

private theorem hasRightTurnDirection_of_pl
    {T : IntervalMap} (hflat : ¬HasFlatInterval T)
    (hPL : FinitePiecePL T) {x : I} (hx : x < rightEndpoint) :
    ∃ d, HasRightTurnDirection d T x := by
  obtain ⟨p, hp⟩ := finitePiecePL_noFlat_strictLaps hPL hflat
  obtain ⟨b, c, d, hxb, hcd, hsub⟩ := p.exists_right_cell_turn hx
  rcases hp hcd with hmono | hanti
  · exact ⟨.inc, b, hxb, hmono.mono hsub⟩
  · exact ⟨.dec, b, hxb, hanti.mono hsub⟩

private theorem exists_left_Icc_subset_of_mem_nhds_turn
    {a x : I} (hax : a < x) {s : Set I} (hs : s ∈ nhds x) :
    ∃ a' : I, a < a' ∧ a' < x ∧ Set.Icc a' x ⊆ s := by
  obtain ⟨l, hl, hls⟩ := exists_Ioc_subset_of_mem_nhds' hs hax
  obtain ⟨a', hla', ha'x⟩ := exists_between hl.2
  refine ⟨a', hl.1.trans_lt hla', ha'x, ?_⟩
  intro z hz
  exact hls ⟨hla'.trans_le hz.1, hz.2⟩

private theorem exists_right_Icc_subset_of_mem_nhds_turn
    {x b : I} (hxb : x < b) {s : Set I} (hs : s ∈ nhds x) :
    ∃ b' : I, x < b' ∧ b' < b ∧ Set.Icc x b' ⊆ s := by
  obtain ⟨r, hr, hrs⟩ := exists_Ico_subset_of_mem_nhds' hs hxb
  obtain ⟨b', hxb', hb'r⟩ := exists_between hr.1
  refine ⟨b', hxb', hb'r.trans_le hr.2, ?_⟩
  intro z hz
  exact hrs ⟨hz.1, hz.2.trans_lt hb'r⟩

private theorem leftTurnDirection_ne
    {T : IntervalMap} {x : I} :
    ¬(HasLeftTurnDirection .inc T x ∧
      HasLeftTurnDirection .dec T x) := by
  rintro ⟨⟨a, hax, hmono⟩, ⟨b, hbx, hanti⟩⟩
  obtain ⟨z, hz, hzx⟩ := exists_between (max_lt hax hbx)
  have hza : a ≤ z := (le_max_left a b).trans hz.le
  have hzb : b ≤ z := (le_max_right a b).trans hz.le
  have hzxmono : T z < T x :=
    hmono ⟨hza, hzx.le⟩ ⟨hax.le, le_rfl⟩ hzx
  have hzxanti : T x < T z :=
    hanti ⟨hzb, hzx.le⟩ ⟨hbx.le, le_rfl⟩ hzx
  exact lt_asymm hzxmono hzxanti

private theorem rightTurnDirection_ne
    {T : IntervalMap} {x : I} :
    ¬(HasRightTurnDirection .inc T x ∧
      HasRightTurnDirection .dec T x) := by
  rintro ⟨⟨a, hxa, hmono⟩, ⟨b, hxb, hanti⟩⟩
  obtain ⟨z, hxz, hz⟩ := exists_between (lt_min hxa hxb)
  have hza : z ≤ a := hz.le.trans (min_le_left a b)
  have hzb : z ≤ b := hz.le.trans (min_le_right a b)
  have hxzmono : T x < T z :=
    hmono ⟨le_rfl, hxa.le⟩ ⟨hxz.le, hza⟩ hxz
  have hxzanti : T z < T x :=
    hanti ⟨le_rfl, hxb.le⟩ ⟨hxz.le, hzb⟩ hxz
  exact lt_asymm hxzmono hxzanti

private theorem TurnDirection.Holds.comp
    {U T : IntervalMap} {s t : Set I} {dU dT : TurnDirection}
    (hU : dU.Holds U t) (hT : dT.Holds T s)
    (hmap : MapsTo T s t) :
    (dU.mul dT).Holds (U ∘ T) s := by
  cases dU <;> cases dT
  · exact StrictMonoOn.comp hU hT hmap
  · exact StrictMonoOn.comp_strictAntiOn hU hT hmap
  · exact StrictAntiOn.comp_strictMonoOn hU hT hmap
  · exact StrictAntiOn.comp hU hT hmap

private theorem leftTurnDirection_comp_of_inc
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : TurnDirection}
    (hT : HasLeftTurnDirection .inc T x)
    (hU : HasLeftTurnDirection d U (T x)) :
    HasLeftTurnDirection (d.mul .inc) (U ∘ T) x := by
  obtain ⟨a, hax, hmono⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Ioi c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hc)
  obtain ⟨a', haa', ha'x, hsub⟩ :=
    exists_left_Icc_subset_of_mem_nhds_turn hax hnear
  have hdom : Set.Icc a' x ⊆ Set.Icc a x := by
    intro z hz
    exact ⟨haa'.le.trans hz.1, hz.2⟩
  have hTdir := hmono.mono hdom
  have hmap : MapsTo T (Set.Icc a' x) (Set.Icc c (T x)) := by
    intro z hz
    refine ⟨(hsub hz).le, ?_⟩
    exact hTdir.monotoneOn hz ⟨ha'x.le, le_rfl⟩ hz.2
  exact ⟨a', ha'x, hUdir.comp hTdir hmap⟩

private theorem leftTurnDirection_comp_of_dec
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : TurnDirection}
    (hT : HasLeftTurnDirection .dec T x)
    (hU : HasRightTurnDirection d U (T x)) :
    HasLeftTurnDirection (d.mul .dec) (U ∘ T) x := by
  obtain ⟨a, hax, hanti⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Iio c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hc)
  obtain ⟨a', haa', ha'x, hsub⟩ :=
    exists_left_Icc_subset_of_mem_nhds_turn hax hnear
  have hdom : Set.Icc a' x ⊆ Set.Icc a x := by
    intro z hz
    exact ⟨haa'.le.trans hz.1, hz.2⟩
  have hTdir := hanti.mono hdom
  have hmap : MapsTo T (Set.Icc a' x) (Set.Icc (T x) c) := by
    intro z hz
    refine ⟨?_, (hsub hz).le⟩
    exact hTdir.antitoneOn hz ⟨ha'x.le, le_rfl⟩ hz.2
  exact ⟨a', ha'x, hUdir.comp hTdir hmap⟩

private theorem rightTurnDirection_comp_of_inc
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : TurnDirection}
    (hT : HasRightTurnDirection .inc T x)
    (hU : HasRightTurnDirection d U (T x)) :
    HasRightTurnDirection (d.mul .inc) (U ∘ T) x := by
  obtain ⟨b, hxb, hmono⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Iio c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Iio_mem_nhds hc)
  obtain ⟨b', hxb', hb'b, hsub⟩ :=
    exists_right_Icc_subset_of_mem_nhds_turn hxb hnear
  have hdom : Set.Icc x b' ⊆ Set.Icc x b := by
    intro z hz
    exact ⟨hz.1, hz.2.trans hb'b.le⟩
  have hTdir := hmono.mono hdom
  have hmap : MapsTo T (Set.Icc x b') (Set.Icc (T x) c) := by
    intro z hz
    refine ⟨?_, (hsub hz).le⟩
    exact hTdir.monotoneOn ⟨le_rfl, hxb'.le⟩ hz hz.1
  exact ⟨b', hxb', hUdir.comp hTdir hmap⟩

private theorem rightTurnDirection_comp_of_dec
    {U T : IntervalMap} (hcont : Continuous T) {x : I}
    {d : TurnDirection}
    (hT : HasRightTurnDirection .dec T x)
    (hU : HasLeftTurnDirection d U (T x)) :
    HasRightTurnDirection (d.mul .dec) (U ∘ T) x := by
  obtain ⟨b, hxb, hanti⟩ := hT
  obtain ⟨c, hc, hUdir⟩ := hU
  have hnear : T ⁻¹' Set.Ioi c ∈ nhds x :=
    hcont.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hc)
  obtain ⟨b', hxb', hb'b, hsub⟩ :=
    exists_right_Icc_subset_of_mem_nhds_turn hxb hnear
  have hdom : Set.Icc x b' ⊆ Set.Icc x b := by
    intro z hz
    exact ⟨hz.1, hz.2.trans hb'b.le⟩
  have hTdir := hanti.mono hdom
  have hmap : MapsTo T (Set.Icc x b') (Set.Icc c (T x)) := by
    intro z hz
    refine ⟨(hsub hz).le, ?_⟩
    exact hTdir.antitoneOn ⟨le_rfl, hxb'.le⟩ hz hz.1
  exact ⟨b', hxb', hUdir.comp hTdir hmap⟩

private theorem leftTurnDirection_unique
    {T : IntervalMap} {x : I} {d e : TurnDirection}
    (hd : HasLeftTurnDirection d T x)
    (he : HasLeftTurnDirection e T x) : d = e := by
  cases d <;> cases e
  · rfl
  · exact False.elim (leftTurnDirection_ne ⟨hd, he⟩)
  · exact False.elim (leftTurnDirection_ne ⟨he, hd⟩)
  · rfl

private theorem rightTurnDirection_unique
    {T : IntervalMap} {x : I} {d e : TurnDirection}
    (hd : HasRightTurnDirection d T x)
    (he : HasRightTurnDirection e T x) : d = e := by
  cases d <;> cases e
  · rfl
  · exact False.elim (rightTurnDirection_ne ⟨hd, he⟩)
  · exact False.elim (rightTurnDirection_ne ⟨he, hd⟩)
  · rfl

private theorem genuineTurn_iff_exists_directions_ne
    {T : IntervalMap} {x : I} :
    IsGenuineTurn T x ↔
      ∃ dL dR : TurnDirection,
        HasLeftTurnDirection dL T x ∧
          HasRightTurnDirection dR T x ∧ dL ≠ dR := by
  constructor
  · rintro ⟨a, b, hax, hxb, hturn⟩
    rcases hturn with ⟨hmono, hanti⟩ | ⟨hanti, hmono⟩
    · exact ⟨.inc, .dec, ⟨a, hax, hmono⟩,
        ⟨b, hxb, hanti⟩, by decide⟩
    · exact ⟨.dec, .inc, ⟨a, hax, hanti⟩,
        ⟨b, hxb, hmono⟩, by decide⟩
  · rintro ⟨dL, dR, ⟨a, hax, hL⟩, ⟨b, hxb, hR⟩, hne⟩
    cases dL <;> cases dR
    · exact False.elim (hne rfl)
    · exact ⟨a, b, hax, hxb, Or.inl ⟨hL, hR⟩⟩
    · exact ⟨a, b, hax, hxb, Or.inr ⟨hL, hR⟩⟩
    · exact False.elim (hne rfl)

private theorem genuineTurn_iff_direction_ne
    {T : IntervalMap} {x : I} {dL dR : TurnDirection}
    (hL : HasLeftTurnDirection dL T x)
    (hR : HasRightTurnDirection dR T x) :
    IsGenuineTurn T x ↔ dL ≠ dR := by
  rw [genuineTurn_iff_exists_directions_ne]
  constructor
  · rintro ⟨eL, eR, heL, heR, hne⟩ heq
    have hLe : dL = eL := leftTurnDirection_unique hL heL
    have hRe : dR = eR := rightTurnDirection_unique hR heR
    exact hne (hLe ▸ hRe ▸ heq)
  · intro hne
    exact ⟨dL, dR, hL, hR, hne⟩

private theorem leftEndpoint_lt_image_of_left_inc
    {T : IntervalMap} {x : I}
    (h : HasLeftTurnDirection .inc T x) : leftEndpoint < T x := by
  obtain ⟨a, hax, hmono⟩ := h
  have hlt : T a < T x :=
    hmono ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax
  exact lt_of_le_of_lt (T a).property.1 hlt

private theorem image_lt_rightEndpoint_of_left_dec
    {T : IntervalMap} {x : I}
    (h : HasLeftTurnDirection .dec T x) : T x < rightEndpoint := by
  obtain ⟨a, hax, hanti⟩ := h
  have hlt : T x < T a :=
    hanti ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax
  exact lt_of_lt_of_le hlt (T a).property.2

private theorem image_lt_rightEndpoint_of_right_inc
    {T : IntervalMap} {x : I}
    (h : HasRightTurnDirection .inc T x) : T x < rightEndpoint := by
  obtain ⟨b, hxb, hmono⟩ := h
  have hlt : T x < T b :=
    hmono ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb
  exact lt_of_lt_of_le hlt (T b).property.2

private theorem leftEndpoint_lt_image_of_right_dec
    {T : IntervalMap} {x : I}
    (h : HasRightTurnDirection .dec T x) : leftEndpoint < T x := by
  obtain ⟨b, hxb, hanti⟩ := h
  have hlt : T b < T x :=
    hanti ⟨le_rfl, hxb.le⟩ ⟨hxb.le, le_rfl⟩ hxb
  exact lt_of_le_of_lt (T b).property.1 hlt

private def HasStrictTurnGerms (T : IntervalMap) : Prop :=
  Continuous T ∧
    (∀ {x : I}, leftEndpoint < x →
      ∃ d, HasLeftTurnDirection d T x) ∧
    (∀ {x : I}, x < rightEndpoint →
      ∃ d, HasRightTurnDirection d T x)

private theorem hasStrictTurnGerms_of_finitePiecePL
    {T : IntervalMap} (hflat : ¬HasFlatInterval T)
    (hPL : FinitePiecePL T) : HasStrictTurnGerms T := by
  refine ⟨hPL.1, ?_, ?_⟩
  · intro x hx
    exact hasLeftTurnDirection_of_pl hflat hPL hx
  · intro x hx
    exact hasRightTurnDirection_of_pl hflat hPL hx

/-! ## Exact intrinsic composition -/

/-- At an interior point, a turn of a composite is exactly a turn of the
inner map or a turn of the outer map at the intermediate value. -/
private theorem genuineTurn_comp_iff
    {U T : IntervalMap} (hUG : HasStrictTurnGerms U)
    (hTG : HasStrictTurnGerms T) {x : I}
    (hxL : leftEndpoint < x) (hxR : x < rightEndpoint) :
    IsGenuineTurn (U ∘ T) x ↔
      IsGenuineTurn T x ∨ IsGenuineTurn U (T x) := by
  obtain ⟨dL, hTL⟩ := hTG.2.1 hxL
  obtain ⟨dR, hTR⟩ := hTG.2.2 hxR
  cases dL <;> cases dR
  · have hyL : leftEndpoint < T x :=
      leftEndpoint_lt_image_of_left_inc hTL
    have hyR : T x < rightEndpoint :=
      image_lt_rightEndpoint_of_right_inc hTR
    obtain ⟨eL, hUL⟩ := hUG.2.1 hyL
    obtain ⟨eR, hUR⟩ := hUG.2.2 hyR
    have hCL := leftTurnDirection_comp_of_inc hTG.1 hTL hUL
    have hCR := rightTurnDirection_comp_of_inc hTG.1 hTR hUR
    constructor
    · intro hturn
      right
      apply (genuineTurn_iff_direction_ne hUL hUR).mpr
      have hne := (genuineTurn_iff_direction_ne hCL hCR).mp hturn
      cases eL <;> cases eR <;> simp_all [TurnDirection.mul]
    · rintro (hTturn | hUturn)
      · exact False.elim
          ((genuineTurn_iff_direction_ne hTL hTR).mp hTturn rfl)
      · apply (genuineTurn_iff_direction_ne hCL hCR).mpr
        have hne := (genuineTurn_iff_direction_ne hUL hUR).mp hUturn
        cases eL <;> cases eR <;> simp_all [TurnDirection.mul]
  · have hyL : leftEndpoint < T x :=
      leftEndpoint_lt_image_of_left_inc hTL
    obtain ⟨e, hUL⟩ := hUG.2.1 hyL
    have hCL := leftTurnDirection_comp_of_inc hTG.1 hTL hUL
    have hCR := rightTurnDirection_comp_of_dec hTG.1 hTR hUL
    have hTturn : IsGenuineTurn T x :=
      (genuineTurn_iff_direction_ne hTL hTR).mpr (by decide)
    have hCturn : IsGenuineTurn (U ∘ T) x := by
      apply (genuineTurn_iff_direction_ne hCL hCR).mpr
      cases e <;> decide
    exact ⟨fun _ ↦ Or.inl hTturn, fun _ ↦ hCturn⟩
  · have hyR : T x < rightEndpoint :=
      image_lt_rightEndpoint_of_left_dec hTL
    obtain ⟨e, hUR⟩ := hUG.2.2 hyR
    have hCL := leftTurnDirection_comp_of_dec hTG.1 hTL hUR
    have hCR := rightTurnDirection_comp_of_inc hTG.1 hTR hUR
    have hTturn : IsGenuineTurn T x :=
      (genuineTurn_iff_direction_ne hTL hTR).mpr (by decide)
    have hCturn : IsGenuineTurn (U ∘ T) x := by
      apply (genuineTurn_iff_direction_ne hCL hCR).mpr
      cases e <;> decide
    exact ⟨fun _ ↦ Or.inl hTturn, fun _ ↦ hCturn⟩
  · have hyR : T x < rightEndpoint :=
      image_lt_rightEndpoint_of_left_dec hTL
    have hyL : leftEndpoint < T x :=
      leftEndpoint_lt_image_of_right_dec hTR
    obtain ⟨eL, hUL⟩ := hUG.2.1 hyL
    obtain ⟨eR, hUR⟩ := hUG.2.2 hyR
    have hCL := leftTurnDirection_comp_of_dec hTG.1 hTL hUR
    have hCR := rightTurnDirection_comp_of_dec hTG.1 hTR hUL
    constructor
    · intro hturn
      right
      apply (genuineTurn_iff_direction_ne hUL hUR).mpr
      have hne := (genuineTurn_iff_direction_ne hCL hCR).mp hturn
      intro heq
      apply hne
      cases eL <;> cases eR <;> simp_all [TurnDirection.mul]
    · rintro (hTturn | hUturn)
      · exact False.elim
          ((genuineTurn_iff_direction_ne hTL hTR).mp hTturn rfl)
      · apply (genuineTurn_iff_direction_ne hCL hCR).mpr
        have hne := (genuineTurn_iff_direction_ne hUL hUR).mp hUturn
        intro heq
        apply hne
        cases eL <;> cases eR <;> simp_all [TurnDirection.mul]

private theorem genuineTurn_of_image_eq_leftEndpoint
    {T : IntervalMap} (hG : HasStrictTurnGerms T) {x : I}
    (hxL : leftEndpoint < x) (hxR : x < rightEndpoint)
    (hTx : T x = leftEndpoint) : IsGenuineTurn T x := by
  obtain ⟨dL, hL⟩ := hG.2.1 hxL
  obtain ⟨dR, hR⟩ := hG.2.2 hxR
  cases dL
  · exact False.elim (by
      have hpos := leftEndpoint_lt_image_of_left_inc hL
      rw [hTx] at hpos
      exact lt_irrefl _ hpos)
  · cases dR
    · exact (genuineTurn_iff_direction_ne hL hR).mpr (by decide)
    · exact False.elim (by
        have hpos := leftEndpoint_lt_image_of_right_dec hR
        rw [hTx] at hpos
        exact lt_irrefl _ hpos)

private theorem genuineTurn_of_image_eq_rightEndpoint
    {T : IntervalMap} (hG : HasStrictTurnGerms T) {x : I}
    (hxL : leftEndpoint < x) (hxR : x < rightEndpoint)
    (hTx : T x = rightEndpoint) : IsGenuineTurn T x := by
  obtain ⟨dL, hL⟩ := hG.2.1 hxL
  obtain ⟨dR, hR⟩ := hG.2.2 hxR
  cases dL
  · cases dR
    · exact False.elim (by
        have hlt := image_lt_rightEndpoint_of_right_inc hR
        rw [hTx] at hlt
        exact lt_irrefl _ hlt)
    · exact (genuineTurn_iff_direction_ne hL hR).mpr (by decide)
  · exact False.elim (by
      have hlt := image_lt_rightEndpoint_of_left_dec hL
      rw [hTx] at hlt
      exact lt_irrefl _ hlt)

/-- Exact intrinsic endpoint-and-turn composition for maps admitting strict
one-sided germs everywhere.  Interior preimages of an endpoint of the outer
map are turns of the inner map, which is the endpoint case missing from the
naive local turn formula. -/
private theorem vertexDomain_comp_of_strictTurnGerms
    {U T : IntervalMap} (hUG : HasStrictTurnGerms U)
    (hTG : HasStrictTurnGerms T) :
    vertexDomain (U ∘ T) = vertexDomain T ∪ T ⁻¹' vertexDomain U := by
  ext x
  by_cases hxL0 : x = leftEndpoint
  · subst x
    simp [vertexDomain]
  by_cases hxR0 : x = rightEndpoint
  · subst x
    simp [vertexDomain]
  have hxL : leftEndpoint < x := by
    exact lt_of_le_of_ne x.property.1 (Ne.symm hxL0)
  have hxR : x < rightEndpoint := by
    exact lt_of_le_of_ne x.property.2 hxR0
  simp only [vertexDomain, genuineTurns, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    Set.mem_preimage, hxL0, hxR0, false_or]
  rw [genuineTurn_comp_iff hUG hTG hxL hxR]
  constructor
  · rintro (hTturn | hUturn)
    · exact Or.inl hTturn
    · exact Or.inr (Or.inr hUturn)
  · rintro (hTturn | hTxEnds | hUturn)
    · exact Or.inl hTturn
    · rcases hTxEnds with hTxL | hTxR
      · exact Or.inl
          (genuineTurn_of_image_eq_leftEndpoint hTG hxL hxR hTxL)
      · exact Or.inl
          (genuineTurn_of_image_eq_rightEndpoint hTG hxL hxR hTxR)
    · exact Or.inr hUturn

/-! ## Public finite-piece PL consequences -/

/-- A flat-free finite-piece PL map has only finitely many intrinsic turns,
so its endpoint-and-turn domain is finite. -/
theorem vertexDomain_finite_of_finitePiecePL_noFlat
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hflat : ¬HasFlatInterval T) : (vertexDomain T).Finite := by
  classical
  obtain ⟨p, hp⟩ := finitePiecePL_noFlat_strictLaps hT hflat
  let partitionPoints : Set I := {x | (x : ℝ) ∈ p.points}
  have hpartitionPoints : partitionPoints.Finite := by
    change (Subtype.val ⁻¹' (p.points : Set ℝ)).Finite
    exact p.points.finite_toSet.preimage
      (Set.injOn_of_injective Subtype.val_injective)
  have hturns : genuineTurns T ⊆ partitionPoints := by
    intro x hxturn
    by_contra hx
    have hxnot : (x : ℝ) ∉ p.points := by
      simpa [partitionPoints] using hx
    obtain ⟨c, d, hcd, hcx, hxd⟩ :=
      p.exists_adjacent_around_turn x.property hxnot
    let cI : I := ⟨c, p.points_subset hcd.1⟩
    let dI : I := ⟨d, p.points_subset hcd.2.1⟩
    have hcxI : cI < x := hcx
    have hxdI : x < dI := hxd
    have hsubL : Set.Icc cI x ⊆ intervalCell c d := by
      intro z hz
      exact ⟨hz.1, hz.2.trans hxdI.le⟩
    have hsubR : Set.Icc x dI ⊆ intervalCell c d := by
      intro z hz
      exact ⟨hcxI.le.trans hz.1, hz.2⟩
    rcases hp hcd with hmono | hanti
    · have hL : HasLeftTurnDirection .inc T x :=
        ⟨cI, hcxI, hmono.mono hsubL⟩
      have hR : HasRightTurnDirection .inc T x :=
        ⟨dI, hxdI, hmono.mono hsubR⟩
      exact ((genuineTurn_iff_direction_ne hL hR).mp hxturn) rfl
    · have hL : HasLeftTurnDirection .dec T x :=
        ⟨cI, hcxI, hanti.mono hsubL⟩
      have hR : HasRightTurnDirection .dec T x :=
        ⟨dI, hxdI, hanti.mono hsubR⟩
      exact ((genuineTurn_iff_direction_ne hL hR).mp hxturn) rfl
  change ({leftEndpoint, rightEndpoint} ∪ genuineTurns T).Finite
  exact (Set.toFinite {leftEndpoint, rightEndpoint}).union
    (hpartitionPoints.subset hturns)

/-- Exact intrinsic endpoint-and-turn composition for flat-free finite-piece
PL interval maps. -/
theorem vertexDomain_comp_exact_of_finitePiecePL_noFlat
    {U T : IntervalMap}
    (hU : FinitePiecePL U) (hT : FinitePiecePL T)
    (hUflat : ¬HasFlatInterval U) (hTflat : ¬HasFlatInterval T) :
    vertexDomain (U ∘ T) = vertexDomain T ∪ T ⁻¹' vertexDomain U := by
  exact vertexDomain_comp_of_strictTurnGerms
    (hasStrictTurnGerms_of_finitePiecePL hUflat hU)
    (hasStrictTurnGerms_of_finitePiecePL hTflat hT)

/-- For an onto inner map, exact endpoint-and-turn composition descends to
the exact intrinsic vertex-value formula. -/
theorem vertexValues_comp_exact_of_finitePiecePL_noFlat
    {U T : IntervalMap}
    (hU : FinitePiecePL U) (hT : FinitePiecePL T)
    (hUflat : ¬HasFlatInterval U) (hTflat : ¬HasFlatInterval T)
    (hTonto : IsOnto T) :
    vertexValues (U ∘ T) = vertexValues U ∪ U '' vertexValues T := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [vertexDomain_comp_exact_of_finitePiecePL_noFlat
      hU hT hUflat hTflat] at hx
    rcases hx with hxT | hxU
    · exact Or.inr ⟨T x, ⟨x, hxT, rfl⟩, rfl⟩
    · exact Or.inl ⟨T x, hxU, rfl⟩
  · rintro (hzU | hzT)
    · obtain ⟨y, hy, rfl⟩ := hzU
      obtain ⟨x, rfl⟩ := hTonto y
      refine ⟨x, ?_, rfl⟩
      rw [vertexDomain_comp_exact_of_finitePiecePL_noFlat
        hU hT hUflat hTflat]
      exact Or.inr hy
    · obtain ⟨y, ⟨x, hx, rfl⟩, rfl⟩ := hzT
      refine ⟨x, ?_, rfl⟩
      rw [vertexDomain_comp_exact_of_finitePiecePL_noFlat
        hU hT hUflat hTflat]
      exact Or.inl hx

end CommutingIntervalSimplified

