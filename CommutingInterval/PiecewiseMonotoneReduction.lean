import CommutingInterval.PiecewiseMonotoneDefs

/-!
# Minimal-core reduction for finite-piece piecewise-monotone maps

This module contains the elementary compact-interval reduction used by the
piecewise-monotone proof.
-/

namespace CommutingInterval

open Function Set

/-! ## Explicit proof states -/

/-- A hypothetical counterexample in the continuous finite-piece
piecewise-monotone class. -/
structure PiecewiseMonotoneCounterexample where
  P : IntervalMap
  Q : IntervalMap
  finitePiece_P : FinitePieceMonotone P
  finitePiece_Q : FinitePieceMonotone Q
  commute : Commute P Q
  no_common_fixed_point : ¬HasCommonFixedPoint P Q

/-- A counterexample affinely normalized from a minimal common invariant
closed interval. -/
structure MinimalPiecewiseMonotoneCounterexample
    extends PiecewiseMonotoneCounterexample where
  onto_P : IsOnto P
  onto_Q : IsOnto Q
  core_minimal :
    ∀ J : ClosedSubinterval,
      IsCommonInvariantCore P Q J → J.carrier = Set.univ

/-! ## Common-invariant closed intervals and chain intersections -/

/-- The whole unit interval as a packaged closed subinterval. -/
def wholeIntervalPM : ClosedSubinterval where
  left := leftEndpoint
  right := rightEndpoint
  left_le_right := by simp [leftEndpoint, rightEndpoint]

/-- The carriers of all nonempty closed intervals forward invariant under
both `P` and `Q`. -/
def commonInvariantCarriers (P Q : IntervalMap) : Set (Set I) :=
  {s | ∃ J : ClosedSubinterval,
    J.carrier = s ∧ IsCommonInvariantCore P Q J}

theorem wholeIntervalPM_carrier :
    wholeIntervalPM.carrier = (Set.univ : Set I) := by
  apply Set.eq_univ_of_forall
  intro x
  change leftEndpoint ≤ x ∧ x ≤ rightEndpoint
  exact ⟨x.property.1, x.property.2⟩

theorem univ_mem_commonInvariantCarriers (P Q : IntervalMap) :
    (Set.univ : Set I) ∈ commonInvariantCarriers P Q := by
  refine ⟨wholeIntervalPM, wholeIntervalPM_carrier, ?_⟩
  constructor <;> intro x hx <;>
    rw [wholeIntervalPM_carrier] <;> exact Set.mem_univ _

/-- A nonempty inclusion-chain of common invariant closed intervals has a
common invariant closed-interval lower bound, namely its compact
intersection. -/
theorem commonInvariantCarriers_chain_lowerBound
    {P Q : IntervalMap} {c : Set (Set I)}
    (hc : c ⊆ commonInvariantCarriers P Q)
    (hchain : IsChain (· ⊆ ·) c) (hcne : c.Nonempty) :
    ∃ lb ∈ commonInvariantCarriers P Q,
      ∀ s ∈ c, lb ⊆ s := by
  let m : Set I := ⋂₀ c
  letI : Nonempty c := hcne.to_subtype
  have hmember_nonempty : ∀ s ∈ c, s.Nonempty := by
    intro s hs
    obtain ⟨J, rfl, _⟩ := hc hs
    exact Set.nonempty_Icc.mpr J.left_le_right
  have hmember_compact : ∀ s ∈ c, IsCompact s := by
    intro s hs
    obtain ⟨J, rfl, _⟩ := hc hs
    exact isCompact_Icc
  have hmember_closed : ∀ s ∈ c, IsClosed s := by
    intro s hs
    obtain ⟨J, rfl, _⟩ := hc hs
    exact isClosed_Icc
  have hmnonempty : m.Nonempty := by
    apply IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    · intro a ha b hb
      rcases hchain.total ha hb with hab | hba
      · exact ⟨a, ha, Set.Subset.rfl, hab⟩
      · exact ⟨b, hb, hba, Set.Subset.rfl⟩
    · exact hmember_nonempty
    · exact hmember_compact
    · exact hmember_closed
  have hmclosed : IsClosed m := isClosed_sInter hmember_closed
  have hmcompact : IsCompact m := hmclosed.isCompact
  have hmord : Set.OrdConnected m := by
    apply Set.ordConnected_sInter
    intro s hs
    obtain ⟨J, rfl, _⟩ := hc hs
    exact Set.ordConnected_Icc
  have hmconnected : IsConnected m := ⟨hmnonempty, hmord.isPreconnected⟩
  have hmeq : m = Set.Icc (sInf m) (sSup m) :=
    eq_Icc_of_connected_compact hmconnected hmcompact
  have hmle : sInf m ≤ sSup m := by
    rw [hmeq] at hmnonempty
    exact Set.nonempty_Icc.mp hmnonempty
  let Jm : ClosedSubinterval :=
    { left := sInf m
      right := sSup m
      left_le_right := hmle }
  have hmP : MapsTo P m m := by
    intro x hx
    rw [Set.mem_sInter] at hx ⊢
    intro s hs
    obtain ⟨J, hJs, hJinv⟩ := hc hs
    rw [← hJs]
    apply hJinv.1
    rw [hJs]
    exact hx s hs
  have hmQ : MapsTo Q m m := by
    intro x hx
    rw [Set.mem_sInter] at hx ⊢
    intro s hs
    obtain ⟨J, hJs, hJinv⟩ := hc hs
    rw [← hJs]
    apply hJinv.2
    rw [hJs]
    exact hx s hs
  refine ⟨m, ?_, ?_⟩
  · refine ⟨Jm, hmeq.symm, ?_⟩
    constructor
    · intro x hx
      have hxm : x ∈ m := by rw [hmeq]; exact hx
      have hPx := hmP hxm
      change P x ∈ Set.Icc (sInf m) (sSup m)
      rw [← hmeq]
      exact hPx
    · intro x hx
      have hxm : x ∈ m := by rw [hmeq]; exact hx
      have hQx := hmQ hxm
      change Q x ∈ Set.Icc (sInf m) (sSup m)
      rw [← hmeq]
      exact hQx
  · intro s hs
    exact Set.sInter_subset_of_mem hs

/-! ## Zorn minimality and the singleton alternative -/

/-- Every pair of interval self-maps admits an inclusion-minimal common
forward-invariant closed subinterval. -/
theorem exists_minimalCommonInvariantCore (P Q : IntervalMap) :
    ∃ J : ClosedSubinterval, IsMinimalCommonInvariantCore P Q J := by
  let cores := commonInvariantCarriers P Q
  have hwhole : (Set.univ : Set I) ∈ cores :=
    univ_mem_commonInvariantCarriers P Q
  have hchainLower : ∀ c ⊆ cores, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ cores, ∀ s ∈ c, lb ⊆ s := by
    intro c hc hchain hcne
    exact commonInvariantCarriers_chain_lowerBound hc hchain hcne
  obtain ⟨m, _hmwhole, hmminimal⟩ :=
    zorn_superset_nonempty cores hchainLower Set.univ hwhole
  obtain ⟨J, hJm, hJinv⟩ := hmminimal.prop
  refine ⟨J, hJinv, ?_⟩
  intro K hKinv hKJ
  have hKcore : K.carrier ∈ cores := ⟨K, rfl, hKinv⟩
  have hKm : K.carrier ⊆ m := by simpa [← hJm] using hKJ
  have hmK : m ⊆ K.carrier := hmminimal.le_of_le hKcore hKm
  simpa [hJm] using hmK

/-- A degenerate common invariant core is a common fixed point. -/
theorem hasCommonFixedPoint_of_invariantCore_not_nondegenerate
    {P Q : IntervalMap} {J : ClosedSubinterval}
    (hJ : IsCommonInvariantCore P Q J) (hdeg : ¬J.Nondegenerate) :
    HasCommonFixedPoint P Q := by
  have heq : J.left = J.right :=
    le_antisymm J.left_le_right (le_of_not_gt hdeg)
  have hPmem := hJ.1 (Set.left_mem_Icc.mpr J.left_le_right)
  have hQmem := hJ.2 (Set.left_mem_Icc.mpr J.left_le_right)
  have hPfix : P J.left = J.left := by
    exact le_antisymm (by simpa [heq] using hPmem.2) hPmem.1
  have hQfix : Q J.left = J.left := by
    exact le_antisymm (by simpa [heq] using hQmem.2) hQmem.1
  exact ⟨J.left, hPfix, hQfix⟩

/-- In the absence of a common fixed point, every common invariant core is
nondegenerate. -/
theorem invariantCore_nondegenerate_of_noCommonFixedPoint
    {P Q : IntervalMap} (hno : ¬HasCommonFixedPoint P Q)
    {J : ClosedSubinterval} (hJ : IsCommonInvariantCore P Q J) :
    J.Nondegenerate := by
  by_contra hdeg
  exact hno (hasCommonFixedPoint_of_invariantCore_not_nondegenerate hJ hdeg)

/-- A counterexample therefore has a nondegenerate inclusion-minimal common
invariant core. -/
theorem PiecewiseMonotoneCounterexample.exists_nondegenerate_minimalCore
    (C : PiecewiseMonotoneCounterexample) :
    ∃ J : ClosedSubinterval,
      J.Nondegenerate ∧ IsMinimalCommonInvariantCore C.P C.Q J := by
  obtain ⟨J, hminimal⟩ := exists_minimalCommonInvariantCore C.P C.Q
  exact ⟨J,
    invariantCore_nondegenerate_of_noCommonFixedPoint
      C.no_common_fixed_point hminimal.1,
    hminimal⟩

/-! ## Transport through the affine core coordinate -/

theorem rescaledCoreMap_continuous
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    {T : IntervalMap} (hT : Continuous T)
    (hmap : MapsTo T J.carrier J.carrier) :
    Continuous (rescaledCoreMap J hJ T hmap) := by
  let e := coreAffineHomeomorph J hJ
  let coreT : J.carrier → J.carrier := fun x => ⟨T x.1, hmap x.2⟩
  have hcoreT : Continuous coreT :=
    (hT.comp continuous_subtype_val).subtype_mk _
  have hcomp : Continuous (e ∘ coreT ∘ e.symm) :=
    e.continuous.comp (hcoreT.comp e.symm.continuous)
  simpa [e, coreT, rescaledCoreMap, Function.comp_def] using hcomp

theorem rescaledCoreMap_surjective_of_surjOn
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    {T : IntervalMap} (hmap : MapsTo T J.carrier J.carrier)
    (honto : Set.SurjOn T J.carrier J.carrier) :
    IsOnto (rescaledCoreMap J hJ T hmap) := by
  intro y
  let e := coreAffineHomeomorph J hJ
  let z : J.carrier := e.symm y
  obtain ⟨x, hxJ, hTx⟩ := honto z.2
  refine ⟨e ⟨x, hxJ⟩, ?_⟩
  rw [rescaledCoreMap_conjugacy]
  have hxeq : (⟨T x, hmap hxJ⟩ : J.carrier) = z := by
    apply Subtype.ext
    exact hTx
  simpa [z, e] using congrArg e hxeq

theorem noCommonFixedPoint_rescaledCoreMaps
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    {P Q : IntervalMap}
    (hPmap : MapsTo P J.carrier J.carrier)
    (hQmap : MapsTo Q J.carrier J.carrier)
    (hno : ¬HasCommonFixedPoint P Q) :
    ¬HasCommonFixedPoint (rescaledCoreMap J hJ P hPmap)
      (rescaledCoreMap J hJ Q hQmap) := by
  rintro ⟨y, hyP, hyQ⟩
  let e := coreAffineHomeomorph J hJ
  let x : J.carrier := e.symm y
  have hey : e x = y := by simp [x, e]
  have hPx : P x.1 = x.1 := by
    have hxsub : (⟨P x.1, hPmap x.2⟩ : J.carrier) = x := by
      apply e.injective
      rw [← rescaledCoreMap_conjugacy J hJ P hPmap x,
        hey, hyP, ← hey]
    exact congrArg Subtype.val hxsub
  have hQx : Q x.1 = x.1 := by
    have hxsub : (⟨Q x.1, hQmap x.2⟩ : J.carrier) = x := by
      apply e.injective
      rw [← rescaledCoreMap_conjugacy J hJ Q hQmap x,
        hey, hyQ, ← hey]
    exact congrArg Subtype.val hxsub
  exact hno ⟨x.1, hPx, hQx⟩

/-- Minimality of a core is transported to the statement that the rescaled
unit interval has no proper common invariant closed subinterval. -/
theorem rescaledCoreMaps_coreMinimal
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    {P Q : IntervalMap}
    (hminimal : IsMinimalCommonInvariantCore P Q J) :
    ∀ K : ClosedSubinterval,
      IsCommonInvariantCore
        (rescaledCoreMap J hJ P hminimal.1.1)
        (rescaledCoreMap J hJ Q hminimal.1.2) K →
      K.carrier = Set.univ := by
  intro K hK
  let e := coreAffineHomeomorph J hJ
  let P' := rescaledCoreMap J hJ P hminimal.1.1
  let Q' := rescaledCoreMap J hJ Q hminimal.1.2
  change IsCommonInvariantCore P' Q' K at hK
  have hconjP (x : J.carrier) :
      P' (e x) = e ⟨P x.1, hminimal.1.1 x.2⟩ := by
    exact rescaledCoreMap_conjugacy J hJ P hminimal.1.1 x
  have hconjQ (x : J.carrier) :
      Q' (e x) = e ⟨Q x.1, hminimal.1.2 x.2⟩ := by
    exact rescaledCoreMap_conjugacy J hJ Q hminimal.1.2 x
  have heMono : Monotone e :=
    (coreAffineHomeomorph_strictMono J hJ).monotone
  have heInvMono : Monotone e.symm := by
    intro a b hab
    by_contra hba
    have hba' : e.symm b < e.symm a := lt_of_not_ge hba
    have himage := coreAffineHomeomorph_strictMono J hJ hba'
    have hbad : b < a := by simpa [e] using himage
    exact (not_lt_of_ge hab) hbad
  have hab : e.symm K.left ≤ e.symm K.right :=
    heInvMono K.left_le_right
  let Kcore : ClosedSubinterval :=
    { left := (e.symm K.left).1
      right := (e.symm K.right).1
      left_le_right := hab }
  have hmem (z : J.carrier) : z.1 ∈ Kcore.carrier ↔ e z ∈ K.carrier := by
    constructor
    · intro hz
      constructor
      · have h := heMono hz.1
        simpa [Kcore, e] using h
      · have h := heMono hz.2
        simpa [Kcore, e] using h
    · intro hz
      constructor
      · have h := heInvMono hz.1
        simpa [Kcore, e] using h
      · have h := heInvMono hz.2
        simpa [Kcore, e] using h
  have hKcoreSubset : Kcore.carrier ⊆ J.carrier := by
    intro z hz
    exact ⟨(e.symm K.left).2.1.trans hz.1,
      hz.2.trans (e.symm K.right).2.2⟩
  have hKcoreInv : IsCommonInvariantCore P Q Kcore := by
    constructor
    · intro z hz
      have hzJ := hKcoreSubset hz
      let zJ : J.carrier := ⟨z, hzJ⟩
      have hzK : e zJ ∈ K.carrier := (hmem zJ).mp hz
      have hPzK := hK.1 hzK
      have hcoord : e ⟨P z, hminimal.1.1 hzJ⟩ ∈ K.carrier := by
        rw [← hconjP zJ]
        exact hPzK
      exact (hmem ⟨P z, hminimal.1.1 hzJ⟩).mpr hcoord
    · intro z hz
      have hzJ := hKcoreSubset hz
      let zJ : J.carrier := ⟨z, hzJ⟩
      have hzK : e zJ ∈ K.carrier := (hmem zJ).mp hz
      have hQzK := hK.2 hzK
      have hcoord : e ⟨Q z, hminimal.1.2 hzJ⟩ ∈ K.carrier := by
        rw [← hconjQ zJ]
        exact hQzK
      exact (hmem ⟨Q z, hminimal.1.2 hzJ⟩).mpr hcoord
  have hJKcore : J.carrier ⊆ Kcore.carrier :=
    hminimal.2 Kcore hKcoreInv hKcoreSubset
  apply Set.eq_univ_of_forall
  intro y
  let z : J.carrier := e.symm y
  have hzcore : z.1 ∈ Kcore.carrier := hJKcore z.2
  have hzK := (hmem z).mp hzcore
  simpa [z, e] using hzK

/-! ## Minimality forces both generators onto -/

/-- Each generator maps an inclusion-minimal common invariant core onto
itself. -/
theorem minimalCommonInvariantCore_mapsOnto
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcommute : Commute P Q) (J : ClosedSubinterval)
    (hminimal : IsMinimalCommonInvariantCore P Q J) :
    Set.SurjOn P J.carrier J.carrier ∧
      Set.SurjOn Q J.carrier J.carrier := by
  have generator_onto (F G : IntervalMap)
      (hF : Continuous F) (hcommFG : Commute F G)
      (hmapF : MapsTo F J.carrier J.carrier)
      (hmapG : MapsTo G J.carrier J.carrier)
      (hpair : ∀ K : ClosedSubinterval,
        IsForwardInvariant F K → IsForwardInvariant G K →
          IsCommonInvariantCore P Q K) :
      Set.SurjOn F J.carrier J.carrier := by
    let S : Set I := F '' J.carrier
    have hSconnected : IsConnected S :=
      (isConnected_Icc J.left_le_right).image F hF.continuousOn
    have hScompact : IsCompact S := isCompact_Icc.image hF
    have hSeq : S = Set.Icc (sInf S) (sSup S) :=
      eq_Icc_of_connected_compact hSconnected hScompact
    have hSle : sInf S ≤ sSup S := by
      have hSne := hSconnected.1
      rw [hSeq] at hSne
      exact Set.nonempty_Icc.mp hSne
    let K : ClosedSubinterval :=
      { left := sInf S
        right := sSup S
        left_le_right := hSle }
    have hKcarrier : K.carrier = S := hSeq.symm
    have hKF : IsForwardInvariant F K := by
      intro z hz
      rw [hKcarrier] at hz ⊢
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨F x, hmapF hx, rfl⟩
    have hKG : IsForwardInvariant G K := by
      intro z hz
      rw [hKcarrier] at hz ⊢
      obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨G x, hmapG hx, ?_⟩
      exact hcommFG x
    have hKJ : K.carrier ⊆ J.carrier := by
      rw [hKcarrier]
      exact Set.image_subset_iff.mpr hmapF
    have hJK : J.carrier ⊆ K.carrier :=
      hminimal.2 K (hpair K hKF hKG) hKJ
    intro y hy
    have hyK := hJK hy
    rw [hKcarrier] at hyK
    exact hyK
  exact ⟨
    generator_onto P Q hP hcommute hminimal.1.1 hminimal.1.2
      (fun _ hFP hGQ => ⟨hFP, hGQ⟩),
    generator_onto Q P hQ hcommute.symm hminimal.1.2 hminimal.1.1
      (fun _ hFQ hGP => ⟨hGP, hFQ⟩)⟩

/-! ## The normalized minimal counterexample -/

/-- Restrict a counterexample to a chosen nondegenerate minimal core and
rescale that core affinely to the unit interval. -/
noncomputable def PiecewiseMonotoneCounterexample.rescaledMinimalCore
    (C : PiecewiseMonotoneCounterexample)
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    (hminimal : IsMinimalCommonInvariantCore C.P C.Q J) :
    MinimalPiecewiseMonotoneCounterexample := by
  classical
  let P' := rescaledCoreMap J hJ C.P hminimal.1.1
  let Q' := rescaledCoreMap J hJ C.Q hminimal.1.2
  obtain ⟨hPontoCore, hQontoCore⟩ :=
    minimalCommonInvariantCore_mapsOnto
      C.finitePiece_P.1 C.finitePiece_Q.1 C.commute J hminimal
  exact
    { P := P'
      Q := Q'
      finitePiece_P := C.finitePiece_P.rescaledCoreMap
        J hJ hminimal.1.1
      finitePiece_Q := C.finitePiece_Q.rescaledCoreMap
        J hJ hminimal.1.2
      commute := rescaledCoreMap_commute J hJ
        hminimal.1.1 hminimal.1.2 C.commute
      no_common_fixed_point := noCommonFixedPoint_rescaledCoreMaps
        J hJ hminimal.1.1 hminimal.1.2 C.no_common_fixed_point
      onto_P := rescaledCoreMap_surjective_of_surjOn
        J hJ hminimal.1.1 hPontoCore
      onto_Q := rescaledCoreMap_surjective_of_surjOn
        J hJ hminimal.1.2 hQontoCore
      core_minimal := rescaledCoreMaps_coreMinimal J hJ hminimal }

/-- Every hypothetical counterexample has a normalized minimal-core
counterexample. -/
theorem PiecewiseMonotoneCounterexample.exists_minimalCounterexample
    (C : PiecewiseMonotoneCounterexample) :
    Nonempty MinimalPiecewiseMonotoneCounterexample := by
  obtain ⟨J, hJ, hminimal⟩ := C.exists_nondegenerate_minimalCore
  exact ⟨C.rescaledMinimalCore J hJ hminimal⟩

/-! ## The commuting composite -/

namespace MinimalPiecewiseMonotoneCounterexample

/-- The central composite `H = P ∘ Q`. -/
def H (C : MinimalPiecewiseMonotoneCounterexample) : IntervalMap :=
  C.P ∘ C.Q

theorem H_eq_reverse (C : MinimalPiecewiseMonotoneCounterexample) :
    C.H = C.Q ∘ C.P := by
  funext x
  exact C.commute x

theorem finitePiece_H (C : MinimalPiecewiseMonotoneCounterexample) :
    FinitePieceMonotone C.H := by
  exact C.finitePiece_P.comp C.finitePiece_Q

theorem onto_H (C : MinimalPiecewiseMonotoneCounterexample) :
    IsOnto C.H := by
  exact C.onto_P.comp C.onto_Q

end MinimalPiecewiseMonotoneCounterexample

end CommutingInterval
