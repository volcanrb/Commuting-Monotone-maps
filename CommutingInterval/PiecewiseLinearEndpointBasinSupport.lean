import CommutingInterval.PiecewiseLinearFiniteArrivalSupport

/-!
# Endpoint-basin support for piecewise-linear finite arrival

This module isolates the one-dimensional endpoint dynamics used after a
diagonal orbit has produced a strict approach sequence.  It depends only on
the finite-arrival support, and its local monotonicity input is
`FinitePiecePL`.
-/

noncomputable section

namespace CommutingInterval

open Filter Function Set Topology
open PLFiniteArrivalSupport

namespace PLEndpointBasinSupport

/-- The basin of a fixed point under iteration. -/
def attractionBasin (T : IntervalMap) (e : I) : Set I :=
  {x | Tendsto (fun n : ℕ => iterateMap T n x) atTop (nhds e)}

/-- Local strict monotonicity together with strict attraction toward the
ambient endpoint. -/
def IsLocallyAttractingEndpoint (T : IntervalMap) (e : I) : Prop :=
  ∃ U : Set I,
    IsOpen U ∧ e ∈ U ∧ (U \ {e}).Nonempty ∧
      StrictMonoOn T U ∧
      ∀ x ∈ U, x ≠ e →
        0 < dist (T x) e ∧ dist (T x) e < dist x e

/-- The closure of the immediate endpoint basin, including its fixed-free
boundary and the onto relation used by the phase argument. -/
structure EndpointBasinClosure (T : IntervalMap) (e : I) where
  interval : ClosedSubinterval
  freeEndpoint : I
  endpoints :
    (e = interval.left ∧ freeEndpoint = interval.right) ∨
      (e = interval.right ∧ freeEndpoint = interval.left)
  nondegenerate : interval.Nondegenerate
  proper : interval.carrier ≠ Set.univ
  carrier_eq :
    interval.carrier = closure (connectedComponentIn (attractionBasin T e) e)
  freeEndpoint_fixed : IsFixedPoint T freeEndpoint
  maps_onto : T '' interval.carrier = interval.carrier

private theorem exists_fixed_free_right_neighborhood
    {S : IntervalMap} (hfinite : (fixedPoints S).Finite) :
    ∃ q : I, leftEndpoint < q ∧
      ∀ x ∈ Set.Ioo leftEndpoint q, S x ≠ x := by
  let bad : Set I := fixedPoints S \ {leftEndpoint}
  have hbadFinite : bad.Finite := hfinite.diff
  have hleftBad : leftEndpoint ∉ bad := by simp [bad]
  have hnhds : badᶜ ∈ 𝓝 leftEndpoint :=
    hbadFinite.isClosed.isOpen_compl.mem_nhds hleftBad
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hεsub⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδone : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let q : I := ⟨δ, hδpos.le, hδone⟩
  refine ⟨q, hδpos, ?_⟩
  intro x hx hfix
  have hdist : dist x leftEndpoint < ε := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(x : ℝ) - 0| < ε
    rw [sub_zero, abs_of_nonneg x.property.1]
    exact (show (x : ℝ) < δ from hx.2).trans hδε
  have hxgood : x ∈ badᶜ := hεsub (Metric.mem_ball.mpr hdist)
  exact hxgood ⟨hfix, by simpa using hx.1.ne'⟩

private theorem exists_fixed_free_left_neighborhood
    {S : IntervalMap} (hfinite : (fixedPoints S).Finite) :
    ∃ q : I, q < rightEndpoint ∧
      ∀ x ∈ Set.Ioo q rightEndpoint, S x ≠ x := by
  let bad : Set I := fixedPoints S \ {rightEndpoint}
  have hbadFinite : bad.Finite := hfinite.diff
  have hrightBad : rightEndpoint ∉ bad := by simp [bad]
  have hnhds : badᶜ ∈ 𝓝 rightEndpoint :=
    hbadFinite.isClosed.isOpen_compl.mem_nhds hrightBad
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hε, hεsub⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδpos : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδε : δ < ε :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hδone : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  let q : I := ⟨1 - δ, by linarith, by linarith⟩
  refine ⟨q, by change 1 - δ < 1; linarith, ?_⟩
  intro x hx hfix
  have hdist : dist x rightEndpoint < ε := by
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(x : ℝ) - 1| < ε
    rw [abs_of_nonpos (by linarith [x.property.2])]
    have hδx : 1 - δ < (x : ℝ) := hx.1
    linarith
  have hxgood : x ∈ badᶜ := hεsub (Metric.mem_ball.mpr hdist)
  exact hxgood ⟨hfix, by simpa using hx.2.ne⟩

private theorem fixed_free_sign_dichotomy
    {S : IntervalMap} (hcont : Continuous S) {a b : I}
    (hnofix : ∀ x ∈ Set.Ioo a b, S x ≠ x) :
    (∀ x ∈ Set.Ioo a b, S x < x) ∨
      (∀ x ∈ Set.Ioo a b, x < S x) := by
  let f : I → ℝ := fun x => (S x : ℝ) - (x : ℝ)
  have hfcont : Continuous f :=
    (continuous_subtype_val.comp hcont).sub continuous_subtype_val
  have hfne : ∀ x ∈ Set.Ioo a b, f x ≠ 0 := by
    intro x hx hzero
    apply hnofix x hx
    apply Subtype.ext
    dsimp [f] at hzero
    linarith
  rcases Set.ordConnected_Ioo.isPreconnected.mapsTo_Ioi_or_Iio
      hfcont.continuousOn hfne with hpos | hneg
  · right
    intro x hx
    change (x : ℝ) < (S x : ℝ)
    have hxpos := hpos hx
    change 0 < (S x : ℝ) - (x : ℝ) at hxpos
    linarith
  · left
    intro x hx
    change (S x : ℝ) < (x : ℝ)
    have hxneg := hneg hx
    change (S x : ℝ) - (x : ℝ) < 0 at hxneg
    linarith

private theorem singleton_right_fibre_preimages_near
    {S : IntervalMap} (hcont : Continuous S)
    (hfibre : S ⁻¹' {rightEndpoint} = {rightEndpoint})
    {q : I} (hq : q < rightEndpoint) :
    ∃ r : I, r < rightEndpoint ∧
      ∀ x : I, r < S x → q < x := by
  let K : Set I := Set.Iic q
  have hKcompact : IsCompact K := isClosed_Iic.isCompact
  have hKne : K.Nonempty := ⟨leftEndpoint, q.property.1⟩
  have himageCompact : IsCompact (S '' K) := hKcompact.image hcont
  have himageNe : (S '' K).Nonempty := hKne.image S
  obtain ⟨m, hm_mem, hm_ge⟩ := himageCompact.exists_isGreatest himageNe
  have hm_lt_right : m < rightEndpoint := by
    apply lt_of_le_of_ne m.property.2
    intro hm
    have hme : m = rightEndpoint := by
      apply Subtype.ext
      change (m : ℝ) = 1
      exact hm
    subst m
    rcases hm_mem with ⟨x, hxq, hxS⟩
    have hxpre : x ∈ S ⁻¹' {rightEndpoint} := by simpa using hxS
    rw [hfibre] at hxpre
    have hxe : x = rightEndpoint := by simpa using hxpre
    subst x
    exact (not_le_of_gt hq) hxq
  obtain ⟨r, hmr, hrright⟩ := exists_between hm_lt_right
  refine ⟨r, hrright, ?_⟩
  intro x hrSx
  by_contra hqx
  have hxK : x ∈ K := le_of_not_gt hqx
  have hSxm : S x ≤ m := hm_ge ⟨x, hxK, rfl⟩
  exact (not_lt_of_ge hSxm) (hmr.trans hrSx)

/-- Right-endpoint exhaustion counterpart to the left-endpoint construction
in `PLFiniteArrivalSupport`. -/
theorem endpointApproachSequence_right_of_exhaustion
    {S : IntervalMap} (hcont : Continuous S)
    (hfinite : (fixedPoints S).Finite)
    (hfibre : S ⁻¹' {rightEndpoint} = {rightEndpoint})
    (D : ℕ → Set I)
    (hcompact : ∀ n, IsCompact (D n))
    (hne : ∀ n, (D n).Nonempty)
    (hmono : Monotone D)
    (hmap : ∀ n, S '' D n = D (n + 2))
    (hnever : ∀ n, rightEndpoint ∉ D n)
    (hdense : Dense (⋃ n, D n)) :
    EndpointApproachSequence S rightEndpoint := by
  obtain ⟨q, hqright, hnofix⟩ :=
    exists_fixed_free_left_neighborhood hfinite
  have hsign := fixed_free_sign_dichotomy hcont hnofix
  have hmove : ∀ x ∈ Set.Ioo q rightEndpoint, x < S x := by
    rcases hsign with haway | htoward
    · exfalso
      obtain ⟨r, hrright, hpre⟩ :=
        singleton_right_fibre_preimages_near hcont hfibre hqright
      obtain ⟨y, hyUnion, hyr⟩ := hdense.exists_mem_open isOpen_Ioo
        (Set.nonempty_Ioo.mpr hrright)
      rcases Set.mem_iUnion.mp hyUnion with ⟨n, hyn⟩
      have hyn2 : y ∈ D (n + 2) := hmono (by omega) hyn
      obtain ⟨z, hzmem, hzgreatest⟩ :=
        (hcompact (n + 2)).exists_isGreatest (hne (n + 2))
      have hrz : r < z := hyr.1.trans_le (hzgreatest hyn2)
      have hzimage : z ∈ S '' D n := by
        rw [hmap n]
        exact hzmem
      rcases hzimage with ⟨x, hxn, hSxz⟩
      have hqx : q < x := hpre x (hrz.trans_eq hSxz.symm)
      have hxright : x < rightEndpoint := by
        exact lt_of_le_of_ne x.property.2 (fun h => hnever n (h ▸ hxn))
      have hxlocal : x ∈ Set.Ioo q rightEndpoint := ⟨hqx, hxright⟩
      have hxn2 : x ∈ D (n + 2) := hmono (by omega) hxn
      have hxz : x ≤ z := hzgreatest hxn2
      exact (not_lt_of_ge hxz) (hSxz ▸ haway x hxlocal)
    · exact htoward
  obtain ⟨u0, hu0q, hu0right⟩ := exists_between hqright
  let u : ℕ → I := fun n => iterateMap S n u0
  have hstepEq : ∀ n, S (u n) = u (n + 1) := by
    intro n
    simp only [u, iterateMap, Function.iterate_succ_apply']
  have huLocal : ∀ n, u n ∈ Set.Ioo q rightEndpoint := by
    intro n
    induction n with
    | zero => exact ⟨hu0q, hu0right⟩
    | succ n ih =>
        have hlt := hmove (u n) ih
        have hSne : S (u n) ≠ rightEndpoint := by
          intro heq
          have hpre : u n ∈ S ⁻¹' {rightEndpoint} := by simpa using heq
          rw [hfibre] at hpre
          have hueq : u n = rightEndpoint := by simpa using hpre
          exact ih.2.ne hueq
        rw [← hstepEq n]
        exact ⟨ih.1.trans hlt,
          lt_of_le_of_ne (S (u n)).property.2 hSne⟩
  have hstep : ∀ n, u n < u (n + 1) := by
    intro n
    rw [← hstepEq n]
    exact hmove (u n) (huLocal n)
  have hmonoU : Monotone u := monotone_nat_of_le_succ fun n => (hstep n).le
  let l : I := ⨆ n, u n
  have htend : Tendsto u atTop (𝓝 l) := tendsto_atTop_iSup hmonoU
  have htendShift : Tendsto (fun n => u (n + 1)) atTop (𝓝 l) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have htendS : Tendsto (fun n => S (u n)) atTop (𝓝 (S l)) :=
    hcont.continuousAt.tendsto.comp htend
  have hfixedl : S l = l := by
    apply tendsto_nhds_unique htendS
    simpa only [hstepEq] using htendShift
  have hql : q < l := (huLocal 0).1.trans_le (le_iSup u 0)
  have hlright : l ≤ rightEndpoint := l.property.2
  have hleq : l = rightEndpoint := by
    apply le_antisymm
    · exact hlright
    · by_contra hnot
      have hlright' : l < rightEndpoint := lt_of_not_ge hnot
      have := hmove l ⟨hql, hlright'⟩
      exact (ne_of_lt this) hfixedl.symm
  refine ⟨u, ?_, ?_, hstepEq, ?_⟩
  · intro n hnep
    exact (huLocal n).2.ne hnep
  · simpa [hleq] using htend
  · intro n
    rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
    change |(u (n + 1) : ℝ) - 1| < |(u n : ℝ) - 1|
    rw [abs_of_nonpos (by linarith [(u (n + 1)).property.2]),
      abs_of_nonpos (by linarith [(u n).property.2])]
    have hs : (u n : ℝ) < (u (n + 1) : ℝ) := hstep n
    linarith

/-- A missing endpoint in a dense expanding diagonal sequence supplies the
strict approach sequence for the product square. -/
theorem endpointApproachSequence_of_neverArrives
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hA : Continuous A) (hB : Continuous B)
    (hcomm : Commute A B)
    (hexpandA : J.carrier ⊆ imageInterval A J)
    (hexpandB : J.carrier ⊆ imageInterval B J)
    (hRonto : IsOnto (A ∘ B))
    (hfinite : (fixedPoints (iterateMap (A ∘ B) 2)).Finite)
    (hdense : Dense (⋃ n : ℕ, diagonalImage A B J n))
    {e : I} (he : IsAmbientEndpoint e)
    (hnever : EndpointNeverArrives A B J e) :
    EndpointApproachSequence (iterateMap (A ∘ B) 2) e := by
  let S : IntervalMap := iterateMap (A ∘ B) 2
  have hsingleton := endpoint_singletonFibre_of_neverArrives J
    hA hB hcomm hexpandA hexpandB hRonto hdense he hnever
  have hfibre : S ⁻¹' {e} = {e} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · exact hsingleton.2 x
    · intro hxe
      subst x
      exact hsingleton.1
  have hScont : Continuous S :=
    IntervalMap.continuous_iterate (hA.comp hB) 2
  have hcompact : ∀ n, IsCompact (diagonalImage A B J n) := by
    intro n
    rw [diagonalImage_eq_comp_iterate_image J hcomm n]
    exact isCompact_Icc.image
      (IntervalMap.continuous_iterate (hA.comp hB) n)
  have hne : ∀ n, (diagonalImage A B J n).Nonempty := by
    intro n
    rw [diagonalImage_eq_comp_iterate_image J hcomm n]
    exact (Set.nonempty_Icc.mpr J.left_le_right).image _
  have hmono : Monotone (fun n => diagonalImage A B J n) :=
    diagonalImage_monotone J hcomm hexpandA hexpandB
  have hmap : ∀ n,
      S '' diagonalImage A B J n = diagonalImage A B J (n + 2) := by
    intro n
    simpa [S, Nat.add_comm] using
      (iterate_product_image_diagonalImage J hcomm 2 n)
  rcases he with rfl | rfl
  · exact PLFiniteArrivalSupport.endpointApproachSequence_left_of_exhaustion
      hScont hfinite hfibre (fun n => diagonalImage A B J n)
      hcompact hne hmono hmap hnever hdense
  · exact endpointApproachSequence_right_of_exhaustion
      hScont hfinite hfibre (fun n => diagonalImage A B J n)
      hcompact hne hmono hmap hnever hdense

private theorem mem_attractionBasin_iterate_iff
    {S : IntervalMap} {e x : I} (k : ℕ) :
    iterateMap S k x ∈ attractionBasin S e ↔
      x ∈ attractionBasin S e := by
  unfold attractionBasin
  change Tendsto (fun n : ℕ => iterateMap S n (iterateMap S k x))
      atTop (nhds e) ↔
    Tendsto (fun n : ℕ => iterateMap S n x) atTop (nhds e)
  have hseq : (fun n : ℕ => iterateMap S n (iterateMap S k x)) =
      fun n : ℕ => iterateMap S (n + k) x := by
    funext n
    exact (Function.iterate_add_apply S n k x).symm
  rw [hseq]
  exact Filter.tendsto_add_atTop_iff_nat
    (f := fun n : ℕ => iterateMap S n x) k

private theorem left_local_subset_attractionBasin
    {S : IntervalMap} (hcont : Continuous S)
    (hfixed : IsFixedPoint S leftEndpoint)
    (hfibre : S ⁻¹' {leftEndpoint} = {leftEndpoint})
    {q : I}
    (hmove : ∀ x ∈ Set.Ioo leftEndpoint q, S x < x) :
    Set.Iio q ⊆ attractionBasin S leftEndpoint := by
  intro x hxq
  by_cases hxleft : x = leftEndpoint
  · subst x
    change Tendsto (fun n : ℕ => iterateMap S n leftEndpoint)
      atTop (nhds leftEndpoint)
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => leftEndpoint) atTop (nhds leftEndpoint)) using 1
    funext n
    exact Function.iterate_fixed hfixed n
  · have hxleft' : leftEndpoint < x :=
      lt_of_le_of_ne x.property.1 (Ne.symm hxleft)
    let u : ℕ → I := fun n => iterateMap S n x
    have hstepEq : ∀ n, S (u n) = u (n + 1) := by
      intro n
      simp only [u, iterateMap, Function.iterate_succ_apply']
    have huLocal : ∀ n, u n ∈ Set.Ioo leftEndpoint q := by
      intro n
      induction n with
      | zero => exact ⟨hxleft', hxq⟩
      | succ n ih =>
          have hlt := hmove (u n) ih
          have hSne : S (u n) ≠ leftEndpoint := by
            intro heq
            have hpre : u n ∈ S ⁻¹' {leftEndpoint} := by simpa using heq
            rw [hfibre] at hpre
            have hueq : u n = leftEndpoint := by simpa using hpre
            exact ih.1.ne' hueq
          rw [← hstepEq n]
          exact ⟨lt_of_le_of_ne (S (u n)).property.1 (Ne.symm hSne),
            hlt.trans ih.2⟩
    have hstep : ∀ n, u (n + 1) < u n := by
      intro n
      rw [← hstepEq n]
      exact hmove (u n) (huLocal n)
    have hanti : Antitone u :=
      antitone_nat_of_succ_le fun n => (hstep n).le
    let l : I := ⨅ n, u n
    have htend : Tendsto u atTop (nhds l) := tendsto_atTop_iInf hanti
    have htendShift : Tendsto (fun n => u (n + 1)) atTop (nhds l) :=
      htend.comp (tendsto_add_atTop_nat 1)
    have htendS : Tendsto (fun n => S (u n)) atTop (nhds (S l)) :=
      hcont.continuousAt.tendsto.comp htend
    have hfixedl : S l = l := by
      apply tendsto_nhds_unique htendS
      simpa only [hstepEq] using htendShift
    have hlq : l < q := (iInf_le u 0).trans_lt (huLocal 0).2
    have hleq : l = leftEndpoint := by
      apply le_antisymm
      · by_contra hnot
        have hleftl : leftEndpoint < l := lt_of_not_ge hnot
        have := hmove l ⟨hleftl, hlq⟩
        exact (ne_of_lt this) hfixedl
      · exact l.property.1
    change Tendsto u atTop (nhds leftEndpoint)
    simpa [hleq] using htend

private theorem right_local_subset_attractionBasin
    {S : IntervalMap} (hcont : Continuous S)
    (hfixed : IsFixedPoint S rightEndpoint)
    (hfibre : S ⁻¹' {rightEndpoint} = {rightEndpoint})
    {q : I}
    (hmove : ∀ x ∈ Set.Ioo q rightEndpoint, x < S x) :
    Set.Ioi q ⊆ attractionBasin S rightEndpoint := by
  intro x hqx
  by_cases hxright : x = rightEndpoint
  · subst x
    change Tendsto (fun n : ℕ => iterateMap S n rightEndpoint)
      atTop (nhds rightEndpoint)
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => rightEndpoint) atTop (nhds rightEndpoint)) using 1
    funext n
    exact Function.iterate_fixed hfixed n
  · have hxright' : x < rightEndpoint :=
      lt_of_le_of_ne x.property.2 hxright
    let u : ℕ → I := fun n => iterateMap S n x
    have hstepEq : ∀ n, S (u n) = u (n + 1) := by
      intro n
      simp only [u, iterateMap, Function.iterate_succ_apply']
    have huLocal : ∀ n, u n ∈ Set.Ioo q rightEndpoint := by
      intro n
      induction n with
      | zero => exact ⟨hqx, hxright'⟩
      | succ n ih =>
          have hlt := hmove (u n) ih
          have hSne : S (u n) ≠ rightEndpoint := by
            intro heq
            have hpre : u n ∈ S ⁻¹' {rightEndpoint} := by simpa using heq
            rw [hfibre] at hpre
            have hueq : u n = rightEndpoint := by simpa using hpre
            exact ih.2.ne hueq
          rw [← hstepEq n]
          exact ⟨ih.1.trans hlt,
            lt_of_le_of_ne (S (u n)).property.2 hSne⟩
    have hstep : ∀ n, u n < u (n + 1) := by
      intro n
      rw [← hstepEq n]
      exact hmove (u n) (huLocal n)
    have hmono : Monotone u :=
      monotone_nat_of_le_succ fun n => (hstep n).le
    let l : I := ⨆ n, u n
    have htend : Tendsto u atTop (nhds l) := tendsto_atTop_iSup hmono
    have htendShift : Tendsto (fun n => u (n + 1)) atTop (nhds l) :=
      htend.comp (tendsto_add_atTop_nat 1)
    have htendS : Tendsto (fun n => S (u n)) atTop (nhds (S l)) :=
      hcont.continuousAt.tendsto.comp htend
    have hfixedl : S l = l := by
      apply tendsto_nhds_unique htendS
      simpa only [hstepEq] using htendShift
    have hql : q < l := (huLocal 0).1.trans_le (le_iSup u 0)
    have hleq : l = rightEndpoint := by
      apply le_antisymm
      · exact l.property.2
      · by_contra hnot
        have hlright : l < rightEndpoint := lt_of_not_ge hnot
        have := hmove l ⟨hql, hlright⟩
        exact (ne_of_lt this) hfixedl.symm
    change Tendsto u atTop (nhds rightEndpoint)
    simpa [hleq] using htend

private theorem attractionBasin_isOpen_of_local
    {S : IntervalMap} {e : I} (hcont : Continuous S)
    {U : Set I} (hUopen : IsOpen U) (heU : e ∈ U)
    (hUbasin : U ⊆ attractionBasin S e) :
    IsOpen (attractionBasin S e) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hevent : ∀ᶠ n : ℕ in atTop, iterateMap S n x ∈ U :=
    hx.eventually (hUopen.mem_nhds heU)
  obtain ⟨n, hn⟩ := hevent.exists
  let V : Set I := iterateMap S n ⁻¹' U
  have hVopen : IsOpen V :=
    hUopen.preimage (IntervalMap.continuous_iterate hcont n)
  have hxV : x ∈ V := hn
  have hVsub : V ⊆ attractionBasin S e := by
    intro y hy
    exact (mem_attractionBasin_iterate_iff n).mp (hUbasin hy)
  exact mem_of_superset (hVopen.mem_nhds hxV) hVsub

private theorem left_move_of_endpointApproach
    {S : IntervalMap} (hcont : Continuous S)
    (hfinite : (fixedPoints S).Finite)
    (happroach : EndpointApproachSequence S leftEndpoint) :
    ∃ q : I, leftEndpoint < q ∧
      ∀ x ∈ Set.Ioo leftEndpoint q, S x < x := by
  obtain ⟨q, hq, hnofix⟩ :=
    exists_fixed_free_right_neighborhood hfinite
  have hsign := fixed_free_sign_dichotomy hcont hnofix
  refine ⟨q, hq, ?_⟩
  rcases hsign with htoward | haway
  · exact htoward
  · exfalso
    rcases happroach with ⟨u, hune, htend, hstep, hdist⟩
    have hevent : ∀ᶠ n : ℕ in atTop, u n ∈ Set.Iio q :=
      htend.eventually (isOpen_Iio.mem_nhds hq)
    obtain ⟨n, hnq⟩ := hevent.exists
    have hnleft : leftEndpoint < u n :=
      lt_of_le_of_ne (u n).property.1 (Ne.symm (hune n))
    have hawayn := haway (u n) ⟨hnleft, hnq⟩
    have hnextLt : u (n + 1) < u n := by
      have hd := hdist n
      rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq] at hd
      change |(u (n + 1) : ℝ) - 0| < |(u n : ℝ) - 0| at hd
      simpa only [sub_zero, abs_of_nonneg (u (n + 1)).property.1,
        abs_of_nonneg (u n).property.1] using hd
    rw [hstep n] at hawayn
    exact (not_lt_of_ge hawayn.le) hnextLt

private theorem right_move_of_endpointApproach
    {S : IntervalMap} (hcont : Continuous S)
    (hfinite : (fixedPoints S).Finite)
    (happroach : EndpointApproachSequence S rightEndpoint) :
    ∃ q : I, q < rightEndpoint ∧
      ∀ x ∈ Set.Ioo q rightEndpoint, x < S x := by
  obtain ⟨q, hq, hnofix⟩ :=
    exists_fixed_free_left_neighborhood hfinite
  have hsign := fixed_free_sign_dichotomy hcont hnofix
  refine ⟨q, hq, ?_⟩
  rcases hsign with haway | htoward
  · exfalso
    rcases happroach with ⟨u, hune, htend, hstep, hdist⟩
    have hevent : ∀ᶠ n : ℕ in atTop, u n ∈ Set.Ioi q :=
      htend.eventually (isOpen_Ioi.mem_nhds hq)
    obtain ⟨n, hnq⟩ := hevent.exists
    have hnright : u n < rightEndpoint :=
      lt_of_le_of_ne (u n).property.2 (hune n)
    have hawayn := haway (u n) ⟨hnq, hnright⟩
    have hnLtNext : u n < u (n + 1) := by
      have hd := hdist n
      rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq] at hd
      change |(u (n + 1) : ℝ) - 1| < |(u n : ℝ) - 1| at hd
      rw [abs_of_nonpos (by linarith [(u (n + 1)).property.2]),
        abs_of_nonpos (by linarith [(u n).property.2])] at hd
      change (u n : ℝ) < (u (n + 1) : ℝ)
      linarith
    rw [hstep n] at hawayn
    exact (not_lt_of_ge hawayn.le) hnLtNext
  · exact htoward

private theorem left_endpointBasinClosure
    {S : IntervalMap} (hcont : Continuous S)
    (hfixed : IsFixedPoint S leftEndpoint)
    (hfibre : S ⁻¹' {leftEndpoint} = {leftEndpoint})
    {q : I} (hq : leftEndpoint < q)
    (hUbasin : Set.Iio q ⊆ attractionBasin S leftEndpoint)
    (hbasinOpen : IsOpen (attractionBasin S leftEndpoint))
    (hbarrier : ∃ r : I,
      ¬ IsAmbientEndpoint r ∧ IsFixedPoint S r) :
    Nonempty (EndpointBasinClosure S leftEndpoint) := by
  let basin : Set I := attractionBasin S leftEndpoint
  let component : Set I := connectedComponentIn basin leftEndpoint
  let A : Set I := closure component
  have heBasin : leftEndpoint ∈ basin := by
    change Tendsto (fun n : ℕ => iterateMap S n leftEndpoint)
      atTop (nhds leftEndpoint)
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => leftEndpoint) atTop (nhds leftEndpoint)) using 1
    funext n
    exact Function.iterate_fixed hfixed n
  have heComponent : leftEndpoint ∈ component :=
    mem_connectedComponentIn heBasin
  have heA : leftEndpoint ∈ A := subset_closure heComponent
  have hcomponentPre : IsPreconnected component :=
    isPreconnected_connectedComponentIn
  have hAord : Set.OrdConnected A :=
    hcomponentPre.closure.ordConnected
  have hAcompact : IsCompact A := isClosed_closure.isCompact
  obtain ⟨b, hbA, hbGreatest⟩ :=
    hAcompact.exists_isGreatest ⟨leftEndpoint, heA⟩
  have hAeq : A = Set.Icc leftEndpoint b := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨x.property.1, hbGreatest hx⟩
    · exact hAord.out heA hbA
  obtain ⟨r, hrInterior, hrFixed⟩ := hbarrier
  have hrLeft : leftEndpoint < r := by
    have hne : leftEndpoint ≠ r := by
      intro hre
      apply hrInterior
      exact Or.inl hre.symm
    exact lt_of_le_of_ne r.property.1 hne
  have hrRight : r < rightEndpoint := by
    have hne : r ≠ rightEndpoint := by
      intro hre
      apply hrInterior
      exact Or.inr hre
    exact lt_of_le_of_ne r.property.2 hne
  have hrNotBasin : r ∉ basin := by
    intro hrBasin
    have hrConst : Tendsto (fun n : ℕ => iterateMap S n r)
        atTop (nhds r) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => r) atTop (nhds r)) using 1
      funext n
      exact Function.iterate_fixed hrFixed n
    have hre : leftEndpoint = r := tendsto_nhds_unique hrBasin hrConst
    exact hrLeft.ne hre
  have hrNotComponent : r ∉ component := fun hrC =>
    hrNotBasin (connectedComponentIn_subset basin leftEndpoint hrC)
  have hcomponentLeBarrier : component ⊆ Set.Iic r := by
    intro x hx
    by_contra hrx
    have hrx' : r < x := lt_of_not_ge hrx
    have hrMem : r ∈ component :=
      hcomponentPre.ordConnected.out heComponent hx ⟨hrLeft.le, hrx'.le⟩
    exact hrNotComponent hrMem
  have hALeBarrier : A ⊆ Set.Iic r :=
    closure_minimal hcomponentLeBarrier isClosed_Iic
  have hbLeR : b ≤ r := hALeBarrier hbA
  have hbRight : b < rightEndpoint := hbLeR.trans_lt hrRight
  have hUComponent : Set.Iio q ⊆ component := by
    apply Set.ordConnected_Iio.isPreconnected.subset_connectedComponentIn
    · exact hq
    · exact hUbasin
  obtain ⟨z, hzLeft, hzq⟩ := exists_between hq
  have hzComponent : z ∈ component := hUComponent hzq
  have hzA : z ∈ A := subset_closure hzComponent
  have hLeftB : leftEndpoint < b := hzLeft.trans_le (hbGreatest hzA)
  have hbNotComponent : b ∉ component := by
    intro hbComponent
    have hcomponentOpen : IsOpen component := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨a, c, hxac, hIccNhds, hIccBasin⟩ :=
        exists_Icc_mem_subset_of_mem_nhds
          (hbasinOpen.mem_nhds
            (connectedComponentIn_subset basin leftEndpoint hx))
      apply mem_of_superset hIccNhds
      have hsub := isPreconnected_Icc.subset_connectedComponentIn
        hxac hIccBasin
      change Set.Icc a c ⊆ connectedComponentIn basin x at hsub
      rw [← connectedComponentIn_eq hx] at hsub
      exact hsub
    obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds'
      (hcomponentOpen.mem_nhds hbComponent) hbRight
    obtain ⟨y, hby, hyu⟩ := exists_between hu.1
    have hyComponent : y ∈ component := hsub ⟨hby.le, hyu⟩
    have hyA : y ∈ A := subset_closure hyComponent
    exact (not_lt_of_ge (hbGreatest hyA)) hby
  have hinteriorA_mem_component :
      ∀ {x : I}, x ∈ A → x < b → x ∈ component := by
    intro x hxA hxb
    by_cases hxe : x = leftEndpoint
    · simpa [hxe] using heComponent
    · have hexists : ∃ y ∈ component, x < y := by
        by_contra hnot
        have hcomponentLe : component ⊆ Set.Iic x := by
          intro y hy
          exact le_of_not_gt fun hxy => hnot ⟨y, hy, hxy⟩
        have hALe : A ⊆ Set.Iic x :=
          closure_minimal hcomponentLe isClosed_Iic
        exact (not_le_of_gt hxb) (hALe hbA)
      obtain ⟨y, hyComponent, hxy⟩ := hexists
      exact hcomponentPre.ordConnected.out heComponent hyComponent
        ⟨x.property.1, hxy.le⟩
  have hmapBasin : MapsTo S basin basin := by
    intro x hx
    have hx' : iterateMap S 1 x ∈ attractionBasin S leftEndpoint :=
      (mem_attractionBasin_iterate_iff 1).mpr hx
    simpa [basin, iterateMap] using hx'
  have hmapComponent : MapsTo S component component := by
    apply mapsTo_iff_image_subset.mpr
    apply IsPreconnected.subset_connectedComponentIn
      (hcomponentPre.image S hcont.continuousOn)
    · exact ⟨leftEndpoint, heComponent, hfixed⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hmapBasin (connectedComponentIn_subset basin leftEndpoint hx)
  have hmapA : MapsTo S A A := hmapComponent.closure hcont
  have hSbA : S b ∈ A := hmapA hbA
  have hSbLe : S b ≤ b := hbGreatest hSbA
  have hSbNeLeft : S b ≠ leftEndpoint := by
    intro hSb
    have hbPre : b ∈ S ⁻¹' {leftEndpoint} := by simpa using hSb
    rw [hfibre] at hbPre
    have hbe : b = leftEndpoint := by simpa using hbPre
    exact hLeftB.ne' hbe
  have hbFixed : IsFixedPoint S b := by
    change S b = b
    apply le_antisymm hSbLe
    by_contra hnot
    have hSbLt : S b < b := lt_of_not_ge hnot
    have hSbComponent : S b ∈ component :=
      hinteriorA_mem_component hSbA hSbLt
    have hSbBasin : S b ∈ basin :=
      connectedComponentIn_subset basin leftEndpoint hSbComponent
    have hbBasin : b ∈ basin := by
      have : iterateMap S 1 b ∈ attractionBasin S leftEndpoint := by
        simpa [basin, iterateMap] using hSbBasin
      exact (mem_attractionBasin_iterate_iff 1).mp this
    have hIccBasin : Set.Icc leftEndpoint b ⊆ basin := by
      intro x hx
      by_cases hxbEq : x = b
      · simpa [hxbEq] using hbBasin
      · have hxb' : x < b := lt_of_le_of_ne hx.2 hxbEq
        have hxA : x ∈ A := by
          rw [hAeq]
          exact hx
        exact connectedComponentIn_subset basin leftEndpoint
          (hinteriorA_mem_component hxA hxb')
    have hIccComponent : Set.Icc leftEndpoint b ⊆ component :=
      isPreconnected_Icc.subset_connectedComponentIn
        (Set.left_mem_Icc.mpr hLeftB.le) hIccBasin
    exact hbNotComponent (hIccComponent (Set.right_mem_Icc.mpr hLeftB.le))
  have hmapOnto : S '' A = A := by
    apply Set.Subset.antisymm hmapA.image_subset
    intro x hx
    have hx' : x ∈ Set.Icc (S leftEndpoint) (S b) := by
      have hSe : S leftEndpoint = leftEndpoint := hfixed
      have hSb : S b = b := hbFixed
      simpa [hSe, hSb, hAeq] using hx
    rw [hAeq]
    exact intermediate_value_Icc hLeftB.le hcont.continuousOn hx'
  let J : ClosedSubinterval :=
    { left := leftEndpoint
      right := b
      left_le_right := hLeftB.le }
  refine ⟨{
    interval := J
    freeEndpoint := b
    endpoints := Or.inl ⟨rfl, rfl⟩
    nondegenerate := hLeftB
    proper := ?_
    carrier_eq := ?_
    freeEndpoint_fixed := hbFixed
    maps_onto := ?_ }⟩
  · intro hJuniv
    have hrightMem : rightEndpoint ∈ J.carrier := by
      rw [hJuniv]
      trivial
    exact (not_le_of_gt hbRight) hrightMem.2
  · change Set.Icc leftEndpoint b = A
    exact hAeq.symm
  · simpa [J, hAeq] using hmapOnto

private theorem right_endpointBasinClosure
    {S : IntervalMap} (hcont : Continuous S)
    (hfixed : IsFixedPoint S rightEndpoint)
    (hfibre : S ⁻¹' {rightEndpoint} = {rightEndpoint})
    {q : I} (hq : q < rightEndpoint)
    (hUbasin : Set.Ioi q ⊆ attractionBasin S rightEndpoint)
    (hbasinOpen : IsOpen (attractionBasin S rightEndpoint))
    (hbarrier : ∃ r : I,
      ¬ IsAmbientEndpoint r ∧ IsFixedPoint S r) :
    Nonempty (EndpointBasinClosure S rightEndpoint) := by
  let basin : Set I := attractionBasin S rightEndpoint
  let component : Set I := connectedComponentIn basin rightEndpoint
  let A : Set I := closure component
  have heBasin : rightEndpoint ∈ basin := by
    change Tendsto (fun n : ℕ => iterateMap S n rightEndpoint)
      atTop (nhds rightEndpoint)
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => rightEndpoint) atTop (nhds rightEndpoint)) using 1
    funext n
    exact Function.iterate_fixed hfixed n
  have heComponent : rightEndpoint ∈ component :=
    mem_connectedComponentIn heBasin
  have heA : rightEndpoint ∈ A := subset_closure heComponent
  have hcomponentPre : IsPreconnected component :=
    isPreconnected_connectedComponentIn
  have hAord : Set.OrdConnected A :=
    hcomponentPre.closure.ordConnected
  have hAcompact : IsCompact A := isClosed_closure.isCompact
  obtain ⟨a, haA, haLeast⟩ :=
    hAcompact.exists_isLeast ⟨rightEndpoint, heA⟩
  have hAeq : A = Set.Icc a rightEndpoint := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨haLeast hx, x.property.2⟩
    · exact hAord.out haA heA
  obtain ⟨r, hrInterior, hrFixed⟩ := hbarrier
  have hrLeft : leftEndpoint < r := by
    have hne : leftEndpoint ≠ r := by
      intro hre
      apply hrInterior
      exact Or.inl hre.symm
    exact lt_of_le_of_ne r.property.1 hne
  have hrRight : r < rightEndpoint := by
    have hne : r ≠ rightEndpoint := by
      intro hre
      apply hrInterior
      exact Or.inr hre
    exact lt_of_le_of_ne r.property.2 hne
  have hrNotBasin : r ∉ basin := by
    intro hrBasin
    have hrConst : Tendsto (fun n : ℕ => iterateMap S n r)
        atTop (nhds r) := by
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => r) atTop (nhds r)) using 1
      funext n
      exact Function.iterate_fixed hrFixed n
    have hre : rightEndpoint = r := tendsto_nhds_unique hrBasin hrConst
    exact hrRight.ne' hre
  have hrNotComponent : r ∉ component := fun hrC =>
    hrNotBasin (connectedComponentIn_subset basin rightEndpoint hrC)
  have hbarrierLeComponent : component ⊆ Set.Ici r := by
    intro x hx
    by_contra hxr
    have hxr' : x < r := lt_of_not_ge hxr
    have hrMem : r ∈ component :=
      hcomponentPre.ordConnected.out hx heComponent ⟨hxr'.le, hrRight.le⟩
    exact hrNotComponent hrMem
  have hbarrierLeA : A ⊆ Set.Ici r :=
    closure_minimal hbarrierLeComponent isClosed_Ici
  have hrLeA : r ≤ a := hbarrierLeA haA
  have hLeftA : leftEndpoint < a := hrLeft.trans_le hrLeA
  have hUComponent : Set.Ioi q ⊆ component := by
    apply Set.ordConnected_Ioi.isPreconnected.subset_connectedComponentIn
    · exact hq
    · exact hUbasin
  obtain ⟨z, hqz, hzRight⟩ := exists_between hq
  have hzComponent : z ∈ component := hUComponent hqz
  have hzA : z ∈ A := subset_closure hzComponent
  have hARight : a < rightEndpoint := (haLeast hzA).trans_lt hzRight
  have haNotComponent : a ∉ component := by
    intro haComponent
    have hcomponentOpen : IsOpen component := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨b, c, hxbc, hIccNhds, hIccBasin⟩ :=
        exists_Icc_mem_subset_of_mem_nhds
          (hbasinOpen.mem_nhds
            (connectedComponentIn_subset basin rightEndpoint hx))
      apply mem_of_superset hIccNhds
      have hsub := isPreconnected_Icc.subset_connectedComponentIn
        hxbc hIccBasin
      change Set.Icc b c ⊆ connectedComponentIn basin x at hsub
      rw [← connectedComponentIn_eq hx] at hsub
      exact hsub
    obtain ⟨u, hu, hsub⟩ := exists_Ioc_subset_of_mem_nhds'
      (hcomponentOpen.mem_nhds haComponent) hLeftA
    obtain ⟨y, huy, hya⟩ := exists_between hu.2
    have hyComponent : y ∈ component := hsub ⟨huy, hya.le⟩
    have hyA : y ∈ A := subset_closure hyComponent
    exact (not_lt_of_ge (haLeast hyA)) hya
  have hinteriorA_mem_component :
      ∀ {x : I}, x ∈ A → a < x → x ∈ component := by
    intro x hxA hax
    by_cases hxe : x = rightEndpoint
    · simpa [hxe] using heComponent
    · have hexists : ∃ y ∈ component, y < x := by
        by_contra hnot
        have hcomponentGe : component ⊆ Set.Ici x := by
          intro y hy
          exact le_of_not_gt fun hyx => hnot ⟨y, hy, hyx⟩
        have hAGe : A ⊆ Set.Ici x :=
          closure_minimal hcomponentGe isClosed_Ici
        exact (not_le_of_gt hax) (hAGe haA)
      obtain ⟨y, hyComponent, hyx⟩ := hexists
      exact hcomponentPre.ordConnected.out hyComponent heComponent
        ⟨hyx.le, x.property.2⟩
  have hmapBasin : MapsTo S basin basin := by
    intro x hx
    have hx' : iterateMap S 1 x ∈ attractionBasin S rightEndpoint :=
      (mem_attractionBasin_iterate_iff 1).mpr hx
    simpa [basin, iterateMap] using hx'
  have hmapComponent : MapsTo S component component := by
    apply mapsTo_iff_image_subset.mpr
    apply IsPreconnected.subset_connectedComponentIn
      (hcomponentPre.image S hcont.continuousOn)
    · exact ⟨rightEndpoint, heComponent, hfixed⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hmapBasin (connectedComponentIn_subset basin rightEndpoint hx)
  have hmapA : MapsTo S A A := hmapComponent.closure hcont
  have hSaA : S a ∈ A := hmapA haA
  have haLeSa : a ≤ S a := haLeast hSaA
  have hSaNeRight : S a ≠ rightEndpoint := by
    intro hSa
    have haPre : a ∈ S ⁻¹' {rightEndpoint} := by simpa using hSa
    rw [hfibre] at haPre
    have hae : a = rightEndpoint := by simpa using haPre
    exact hARight.ne hae
  have haFixed : IsFixedPoint S a := by
    change S a = a
    apply le_antisymm
    · by_contra hnot
      have haLtSa : a < S a := lt_of_not_ge hnot
      have hSaComponent : S a ∈ component :=
        hinteriorA_mem_component hSaA haLtSa
      have hSaBasin : S a ∈ basin :=
        connectedComponentIn_subset basin rightEndpoint hSaComponent
      have haBasin : a ∈ basin := by
        have : iterateMap S 1 a ∈ attractionBasin S rightEndpoint := by
          simpa [basin, iterateMap] using hSaBasin
        exact (mem_attractionBasin_iterate_iff 1).mp this
      have hIccBasin : Set.Icc a rightEndpoint ⊆ basin := by
        intro x hx
        by_cases hxaEq : x = a
        · simpa [hxaEq] using haBasin
        · have hax' : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxaEq)
          have hxA : x ∈ A := by
            rw [hAeq]
            exact hx
          exact connectedComponentIn_subset basin rightEndpoint
            (hinteriorA_mem_component hxA hax')
      have hIccComponent : Set.Icc a rightEndpoint ⊆ component :=
        isPreconnected_Icc.subset_connectedComponentIn
          (Set.right_mem_Icc.mpr hARight.le) hIccBasin
      exact haNotComponent
        (hIccComponent (Set.left_mem_Icc.mpr hARight.le))
    · exact haLeSa
  have hmapOnto : S '' A = A := by
    apply Set.Subset.antisymm hmapA.image_subset
    intro x hx
    have hx' : x ∈ Set.Icc (S a) (S rightEndpoint) := by
      have hSa : S a = a := haFixed
      have hSe : S rightEndpoint = rightEndpoint := hfixed
      simpa [hSa, hSe, hAeq] using hx
    rw [hAeq]
    exact intermediate_value_Icc hARight.le hcont.continuousOn hx'
  let J : ClosedSubinterval :=
    { left := a
      right := rightEndpoint
      left_le_right := hARight.le }
  refine ⟨{
    interval := J
    freeEndpoint := a
    endpoints := Or.inr ⟨rfl, rfl⟩
    nondegenerate := hARight
    proper := ?_
    carrier_eq := ?_
    freeEndpoint_fixed := haFixed
    maps_onto := ?_ }⟩
  · intro hJuniv
    have hleftMem : leftEndpoint ∈ J.carrier := by
      rw [hJuniv]
      trivial
    exact (not_le_of_gt hLeftA) hleftMem.1
  · change Set.Icc a rightEndpoint = A
    exact hAeq.symm
  · simpa [J, hAeq] using hmapOnto

/-- A finite PL decomposition, the singleton endpoint fibre, and a strictly
approaching orbit give local endpoint monotonicity, an open attraction basin,
and a proper closed interval on which the map is onto. -/
theorem local_endpoint_monotonicity_and_basinClosure
    {S : IntervalMap} {e : I}
    (he : IsAmbientEndpoint e)
    (hPL : FinitePiecePL S)
    (hcont : Continuous S)
    (hfinite : (fixedPoints S).Finite)
    (hfixed : IsFixedPoint S e)
    (hfibre : S ⁻¹' {e} = {e})
    (happroach : EndpointApproachSequence S e)
    (hbarrier : ∃ q : I,
      ¬ IsAmbientEndpoint q ∧ IsFixedPoint S q) :
    IsLocallyAttractingEndpoint S e ∧
      IsOpen (attractionBasin S e) ∧
      Nonempty (EndpointBasinClosure S e) := by
  rcases he with rfl | rfl
  · obtain ⟨qMove, hqMove, hmove⟩ :=
      left_move_of_endpointApproach hcont hfinite happroach
    obtain ⟨qStrict, hqStrict, hstrict⟩ :=
      finitePiecePL_singleton_leftEndpointFibre_local_strictMono
        hPL hfixed hfibre
    let q : I := min qStrict qMove
    have hq : leftEndpoint < q := lt_min hqStrict hqMove
    have hstrictQ : StrictMonoOn S (Set.Iio q) := by
      apply hstrict.mono
      intro x hx
      have hxq : x < q := hx
      exact hxq.trans_le (min_le_left _ _)
    have hmoveQ : ∀ x ∈ Set.Ioo leftEndpoint q, S x < x := by
      intro x hx
      exact hmove x ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩
    have hlocal : IsLocallyAttractingEndpoint S leftEndpoint := by
      refine ⟨Set.Iio q, isOpen_Iio, hq, ?_, hstrictQ, ?_⟩
      · obtain ⟨x, hxLeft, hxq⟩ := exists_between hq
        refine ⟨x, hxq, ?_⟩
        simp only [Set.mem_singleton_iff]
        exact hxLeft.ne'
      · intro x hx hxne
        have hxLeft : leftEndpoint < x :=
          lt_of_le_of_ne x.property.1 (Ne.symm hxne)
        have hxMove : S x < x := hmoveQ x ⟨hxLeft, hx⟩
        have hSxne : S x ≠ leftEndpoint := by
          intro hSx
          have hxpre : x ∈ S ⁻¹' {leftEndpoint} := by simpa using hSx
          rw [hfibre] at hxpre
          have hxe : x = leftEndpoint := by simpa using hxpre
          exact hxne hxe
        constructor
        · exact dist_pos.mpr hSxne
        · rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
          change |(S x : ℝ) - 0| < |(x : ℝ) - 0|
          simpa only [sub_zero, abs_of_nonneg (S x).property.1,
            abs_of_nonneg x.property.1] using hxMove
    have hUbasin : Set.Iio q ⊆ attractionBasin S leftEndpoint :=
      left_local_subset_attractionBasin hcont hfixed hfibre hmoveQ
    have hbasinOpen : IsOpen (attractionBasin S leftEndpoint) :=
      attractionBasin_isOpen_of_local hcont isOpen_Iio hq hUbasin
    exact ⟨hlocal, hbasinOpen,
      left_endpointBasinClosure hcont hfixed hfibre hq hUbasin
        hbasinOpen hbarrier⟩
  · obtain ⟨qMove, hqMove, hmove⟩ :=
      right_move_of_endpointApproach hcont hfinite happroach
    obtain ⟨qStrict, hqStrict, hstrict⟩ :=
      finitePiecePL_singleton_rightEndpointFibre_local_strictMono
        hPL hfixed hfibre
    let q : I := max qStrict qMove
    have hq : q < rightEndpoint := max_lt hqStrict hqMove
    have hstrictQ : StrictMonoOn S (Set.Ioi q) := by
      apply hstrict.mono
      intro x hx
      have hqx : q < x := hx
      exact (le_max_left _ _).trans_lt hqx
    have hmoveQ : ∀ x ∈ Set.Ioo q rightEndpoint, x < S x := by
      intro x hx
      exact hmove x ⟨(le_max_right _ _).trans_lt hx.1, hx.2⟩
    have hlocal : IsLocallyAttractingEndpoint S rightEndpoint := by
      refine ⟨Set.Ioi q, isOpen_Ioi, hq, ?_, hstrictQ, ?_⟩
      · obtain ⟨x, hqx, hxRight⟩ := exists_between hq
        refine ⟨x, hqx, ?_⟩
        simp only [Set.mem_singleton_iff]
        exact hxRight.ne
      · intro x hx hxne
        have hxRight : x < rightEndpoint :=
          lt_of_le_of_ne x.property.2 hxne
        have hxMove : x < S x := hmoveQ x ⟨hx, hxRight⟩
        have hSxne : S x ≠ rightEndpoint := by
          intro hSx
          have hxpre : x ∈ S ⁻¹' {rightEndpoint} := by simpa using hSx
          rw [hfibre] at hxpre
          have hxe : x = rightEndpoint := by simpa using hxpre
          exact hxne hxe
        constructor
        · exact dist_pos.mpr hSxne
        · rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
          change |(S x : ℝ) - 1| < |(x : ℝ) - 1|
          rw [abs_of_nonpos (by linarith [(S x).property.2]),
            abs_of_nonpos (by linarith [x.property.2])]
          have hxMoveReal : (x : ℝ) < (S x : ℝ) := hxMove
          linarith
    have hUbasin : Set.Ioi q ⊆ attractionBasin S rightEndpoint :=
      right_local_subset_attractionBasin hcont hfixed hfibre hmoveQ
    have hbasinOpen : IsOpen (attractionBasin S rightEndpoint) :=
      attractionBasin_isOpen_of_local hcont isOpen_Ioi hq hUbasin
    exact ⟨hlocal, hbasinOpen,
      right_endpointBasinClosure hcont hfixed hfibre hq hUbasin
        hbasinOpen hbarrier⟩

/-- Commutation carries the immediate endpoint basin into itself.  If the
two factor maps fix the attracting endpoint, the onto relation for
`S = A² ∘ B²` sandwiches both factor images to equality. -/
theorem canonical_powers_map_endpointBasinClosure_onto
    {A B S : IntervalMap} {e : I}
    (hAcont : Continuous A) (hBcont : Continuous B)
    (hcommAB : Commute A B)
    (hSform : S = iterateMap A 2 ∘ iterateMap B 2)
    (hfixed : IsFixedPoint S e)
    (hAe : IsFixedPoint A e) (hBe : IsFixedPoint B e)
    (E : EndpointBasinClosure S e) :
    A '' E.interval.carrier = E.interval.carrier ∧
      B '' E.interval.carrier = E.interval.carrier := by
  let basin : Set I := attractionBasin S e
  let component : Set I := connectedComponentIn basin e
  have heBasin : e ∈ basin := by
    change Tendsto (fun n : ℕ => iterateMap S n e) atTop (nhds e)
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => e) atTop (nhds e)) using 1
    funext n
    exact Function.iterate_fixed hfixed n
  have heComponent : e ∈ component :=
    mem_connectedComponentIn heBasin
  have hcommAS : Commute A S := by
    rw [hSform]
    exact (Function.Commute.self_iterate A 2).comp_right
      (hcommAB.iterate_right 2)
  have hcommBS : Commute B S := by
    rw [hSform]
    exact (hcommAB.symm.iterate_right 2).comp_right
      (Function.Commute.self_iterate B 2)
  have preserveBasin (F : IntervalMap) (hFcont : Continuous F)
      (hcommFS : Commute F S) (hFe : IsFixedPoint F e) :
      MapsTo F basin basin := by
    intro x hx
    change Tendsto (fun n : ℕ => iterateMap S n x) atTop (nhds e) at hx
    change Tendsto (fun n : ℕ => iterateMap S n (F x)) atTop (nhds e)
    have hlim : Tendsto (fun n : ℕ => F (iterateMap S n x))
        atTop (nhds (F e)) := hFcont.continuousAt.tendsto.comp hx
    have hseq : (fun n : ℕ => iterateMap S n (F x)) =
        fun n : ℕ => F (iterateMap S n x) := by
      funext n
      exact ((hcommFS.iterate_right n).eq x).symm
    rw [hseq]
    change F e = e at hFe
    rw [hFe] at hlim
    exact hlim
  have preserveComponent (F : IntervalMap) (hFcont : Continuous F)
      (hcommFS : Commute F S) (hFe : IsFixedPoint F e) :
      MapsTo F component component := by
    have hbasin := preserveBasin F hFcont hcommFS hFe
    apply mapsTo_iff_image_subset.mpr
    apply IsPreconnected.subset_connectedComponentIn
      (isPreconnected_connectedComponentIn.image F hFcont.continuousOn)
    · exact ⟨e, heComponent, hFe⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hbasin (connectedComponentIn_subset basin e hx)
  have preserveClosure (F : IntervalMap) (hFcont : Continuous F)
      (hcommFS : Commute F S) (hFe : IsFixedPoint F e) :
      MapsTo F (closure component) (closure component) :=
    (preserveComponent F hFcont hcommFS hFe).closure hFcont
  have hAmap : MapsTo A E.interval.carrier E.interval.carrier := by
    intro x hx
    rw [E.carrier_eq] at hx ⊢
    exact preserveClosure A hAcont hcommAS hAe hx
  have hBmap : MapsTo B E.interval.carrier E.interval.carrier := by
    intro x hx
    rw [E.carrier_eq] at hx ⊢
    exact preserveClosure B hBcont hcommBS hBe hx
  constructor
  · apply Set.Subset.antisymm hAmap.image_subset
    intro x hx
    have hxS : x ∈ S '' E.interval.carrier := by
      rw [E.maps_onto]
      exact hx
    obtain ⟨y, hy, rfl⟩ := hxS
    refine ⟨A (B (B y)), ?_, ?_⟩
    · exact hAmap (hBmap (hBmap hy))
    · exact (congrFun hSform y).symm
  · apply Set.Subset.antisymm hBmap.image_subset
    intro x hx
    have hxS : x ∈ S '' E.interval.carrier := by
      rw [E.maps_onto]
      exact hx
    obtain ⟨y, hy, rfl⟩ := hxS
    refine ⟨B (A (A y)), ?_, ?_⟩
    · exact hBmap (hAmap (hAmap hy))
    · exact ((congrFun hSform y).trans
        ((hcommAB.iterate_iterate 2 2).eq y)).symm

end PLEndpointBasinSupport

end CommutingInterval
