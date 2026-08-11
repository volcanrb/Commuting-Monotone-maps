import CommutingIntervalSimplified.PiecewiseMonotoneBase
import CommutingIntervalSimplified.FactorBase
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Sequences

/-!
# Minimal common invariant cores

This file contains the compact-interval and affine-conjugacy infrastructure
used by the first reduction step.  It is standalone: all dynamics are
restricted to the selected core and then transported to the unit interval by
an explicit increasing affine homeomorphism.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set Filter Topology

/-- Inclusion-minimality among common invariant closed subintervals already
contained in `J`. -/
def IsMinimalCommonInvariantCore (P Q : IntervalMap)
    (J : ClosedSubinterval) : Prop :=
  IsCommonInvariantCore P Q J ∧
    ∀ K : ClosedSubinterval,
      IsCommonInvariantCore P Q K →
        K.carrier ⊆ J.carrier → J.carrier ⊆ K.carrier

/-! ## Existence and nondegeneracy of a minimal core -/

/-- Endpoint pairs of common forward-invariant closed intervals. -/
def commonInvariantEndpointPairs (P Q : IntervalMap) : Set (I × I) :=
  {ab | ab.1 ≤ ab.2 ∧
    MapsTo P (Set.Icc ab.1 ab.2) (Set.Icc ab.1 ab.2) ∧
    MapsTo Q (Set.Icc ab.1 ab.2) (Set.Icc ab.1 ab.2)}

/-- Continuity makes the endpoint-pair condition closed.  For a convergent
sequence of invariant intervals, a point of the limiting interval is
approximated by its clamp to each interval in the sequence. -/
theorem isClosed_commonInvariantEndpointPairs
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q) :
    IsClosed (commonInvariantEndpointPairs P Q) := by
  apply IsSeqClosed.isClosed
  intro sequence limit hsequence hlimit
  have hleft : Tendsto (fun n => (sequence n).1) atTop (𝓝 limit.1) :=
    (continuous_fst.tendsto limit).comp hlimit
  have hright : Tendsto (fun n => (sequence n).2) atTop (𝓝 limit.2) :=
    (continuous_snd.tendsto limit).comp hlimit
  have hlimit_le : limit.1 ≤ limit.2 :=
    le_of_tendsto_of_tendsto' hleft hright fun n => (hsequence n).1
  refine ⟨hlimit_le, ?_, ?_⟩
  · intro x hx
    let clamped : ℕ → I := fun n =>
      max (sequence n).1 (min (sequence n).2 x)
    have hclamped_mem (n : ℕ) :
        clamped n ∈ Set.Icc (sequence n).1 (sequence n).2 := by
      refine ⟨le_max_left _ _, max_le (hsequence n).1 (min_le_left _ _)⟩
    have hclamped : Tendsto clamped atTop (𝓝 x) := by
      have hcontinuous : Continuous (fun ab : I × I =>
          max ab.1 (min ab.2 x)) :=
        continuous_fst.max (continuous_snd.min continuous_const)
      have ht := (hcontinuous.tendsto limit).comp hlimit
      simpa [clamped, min_eq_right hx.2, max_eq_right hx.1] using ht
    have hPclamped : Tendsto (fun n => P (clamped n)) atTop (𝓝 (P x)) :=
      (hP.tendsto x).comp hclamped
    have hPmem (n : ℕ) :
        P (clamped n) ∈ Set.Icc (sequence n).1 (sequence n).2 :=
      (hsequence n).2.1 (hclamped_mem n)
    exact ⟨
      le_of_tendsto_of_tendsto' hleft hPclamped fun n => (hPmem n).1,
      le_of_tendsto_of_tendsto' hPclamped hright fun n => (hPmem n).2⟩
  · intro x hx
    let clamped : ℕ → I := fun n =>
      max (sequence n).1 (min (sequence n).2 x)
    have hclamped_mem (n : ℕ) :
        clamped n ∈ Set.Icc (sequence n).1 (sequence n).2 := by
      refine ⟨le_max_left _ _, max_le (hsequence n).1 (min_le_left _ _)⟩
    have hclamped : Tendsto clamped atTop (𝓝 x) := by
      have hcontinuous : Continuous (fun ab : I × I =>
          max ab.1 (min ab.2 x)) :=
        continuous_fst.max (continuous_snd.min continuous_const)
      have ht := (hcontinuous.tendsto limit).comp hlimit
      simpa [clamped, min_eq_right hx.2, max_eq_right hx.1] using ht
    have hQclamped : Tendsto (fun n => Q (clamped n)) atTop (𝓝 (Q x)) :=
      (hQ.tendsto x).comp hclamped
    have hQmem (n : ℕ) :
        Q (clamped n) ∈ Set.Icc (sequence n).1 (sequence n).2 :=
      (hsequence n).2.2 (hclamped_mem n)
    exact ⟨
      le_of_tendsto_of_tendsto' hleft hQclamped fun n => (hQmem n).1,
      le_of_tendsto_of_tendsto' hQclamped hright fun n => (hQmem n).2⟩

theorem commonInvariantEndpointPairs_nonempty (P Q : IntervalMap) :
    (commonInvariantEndpointPairs P Q).Nonempty := by
  refine ⟨(leftEndpoint, rightEndpoint), ?_⟩
  refine ⟨by simp [leftEndpoint, rightEndpoint], ?_, ?_⟩
  · intro x _hx
    constructor
    · change (0 : ℝ) ≤ (P x : ℝ)
      exact (P x).property.1
    · change (P x : ℝ) ≤ 1
      exact (P x).property.2
  · intro x _hx
    constructor
    · change (0 : ℝ) ≤ (Q x : ℝ)
      exact (Q x).property.1
    · change (Q x : ℝ) ≤ 1
      exact (Q x).property.2

/-- The real length represented by an ordered endpoint pair. -/
def endpointPairLength (ab : I × I) : ℝ :=
  (ab.2 : ℝ) - (ab.1 : ℝ)

theorem endpointPairLength_continuous : Continuous endpointPairLength := by
  exact (continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)

/-- Continuous interval maps admit a common invariant interval of least
length; least length implies inclusion-minimality. -/
theorem exists_minimalCommonInvariantCore (P Q : IntervalMap)
    (hP : Continuous P) (hQ : Continuous Q) :
    ∃ J : ClosedSubinterval, IsMinimalCommonInvariantCore P Q J := by
  have hcompact : IsCompact (commonInvariantEndpointPairs P Q) :=
    (isClosed_commonInvariantEndpointPairs hP hQ).isCompact
  obtain ⟨ab, hab, habmin⟩ := hcompact.exists_isMinOn
    (commonInvariantEndpointPairs_nonempty P Q)
    endpointPairLength_continuous.continuousOn
  let J : ClosedSubinterval :=
    { left := ab.1
      right := ab.2
      left_le_right := hab.1 }
  have hJinv : IsCommonInvariantCore P Q J := ⟨hab.2.1, hab.2.2⟩
  refine ⟨J, hJinv, ?_⟩
  intro K hKinv hKJ
  have hKpair : (K.left, K.right) ∈ commonInvariantEndpointPairs P Q :=
    ⟨K.left_le_right, hKinv.1, hKinv.2⟩
  have hmin := habmin hKpair
  have hJKleft : (J.left : ℝ) ≤ (K.left : ℝ) := by
    exact_mod_cast (hKJ K.left_mem_carrier).1
  have hKJright : (K.right : ℝ) ≤ (J.right : ℝ) := by
    exact_mod_cast (hKJ K.right_mem_carrier).2
  have hKJleft : (K.left : ℝ) ≤ (J.left : ℝ) := by
    change endpointPairLength ab ≤ endpointPairLength (K.left, K.right) at hmin
    dsimp [endpointPairLength, J] at hmin ⊢
    linarith
  have hJKright : (J.right : ℝ) ≤ (K.right : ℝ) := by
    change endpointPairLength ab ≤ endpointPairLength (K.left, K.right) at hmin
    dsimp [endpointPairLength, J] at hmin ⊢
    linarith
  have hKJleft' : K.left ≤ J.left := by exact_mod_cast hKJleft
  have hJKright' : J.right ≤ K.right := by exact_mod_cast hJKright
  intro x hx
  exact ⟨hKJleft'.trans hx.1, hx.2.trans hJKright'⟩

/-- A degenerate invariant core supplies a common fixed point. -/
theorem hasCommonFixedPoint_of_invariantCore_not_nondegenerate
    {P Q : IntervalMap} {J : ClosedSubinterval}
    (hJ : IsCommonInvariantCore P Q J) (hdeg : ¬J.Nondegenerate) :
    HasCommonFixedPoint P Q := by
  have heq : J.left = J.right :=
    le_antisymm J.left_le_right (le_of_not_gt hdeg)
  have hPmem := hJ.1 J.left_mem_carrier
  have hQmem := hJ.2 J.left_mem_carrier
  have hPfix : P J.left = J.left := by
    exact le_antisymm (by simpa [heq] using hPmem.2) hPmem.1
  have hQfix : Q J.left = J.left := by
    exact le_antisymm (by simpa [heq] using hQmem.2) hQmem.1
  exact ⟨J.left, hPfix, hQfix⟩

theorem invariantCore_nondegenerate_of_noCommonFixedPoint
    {P Q : IntervalMap} (hno : ¬HasCommonFixedPoint P Q)
    {J : ClosedSubinterval} (hJ : IsCommonInvariantCore P Q J) :
    J.Nondegenerate := by
  by_contra hdeg
  exact hno (hasCommonFixedPoint_of_invariantCore_not_nondegenerate hJ hdeg)

/-! ## The affine core coordinate -/

/-- Identify an interval carrier with the corresponding real `Icc` subtype. -/
def coreCarrierRealHomeomorph (J : ClosedSubinterval) :
    J.carrier ≃ₜ Set.Icc (J.left : ℝ) (J.right : ℝ) where
  toFun x := ⟨(x.1 : ℝ), x.2⟩
  invFun x :=
    ⟨⟨x.1, J.left.property.1.trans x.2.1,
        x.2.2.trans J.right.property.2⟩, x.2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The increasing affine coordinate from a nondegenerate core to `I`. -/
noncomputable def coreAffineHomeomorph
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) :
    J.carrier ≃ₜ I :=
  (coreCarrierRealHomeomorph J).trans
    (iccHomeoI (J.left : ℝ) (J.right : ℝ)
      (show (J.left : ℝ) < J.right from hJ))

theorem coreAffineHomeomorph_strictMono
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) :
    StrictMono (coreAffineHomeomorph J hJ) := by
  intro x y hxy
  change (((coreAffineHomeomorph J hJ) x : I) : ℝ) <
    (((coreAffineHomeomorph J hJ) y : I) : ℝ)
  simp only [coreAffineHomeomorph, Homeomorph.trans_apply,
    iccHomeoI_apply_coe]
  have hJreal : (J.left : ℝ) < (J.right : ℝ) := hJ
  rw [div_lt_div_iff_of_pos_right (sub_pos.mpr hJreal)]
  have hxyreal : (x.1 : ℝ) < (y.1 : ℝ) := hxy
  exact sub_lt_sub_right hxyreal _

/-- The inverse affine coordinate, viewed as an embedding `I → I`. -/
noncomputable def coreEmbeddingMap
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) : IntervalMap :=
  fun x => ((coreAffineHomeomorph J hJ).symm x).1

theorem coreEmbeddingMap_continuous
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) :
    Continuous (coreEmbeddingMap J hJ) :=
  (coreAffineHomeomorph J hJ).symm.continuous.subtype_val

theorem coreEmbeddingMap_strictMono
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) :
    StrictMono (coreEmbeddingMap J hJ) := by
  have hmono : Monotone (coreEmbeddingMap J hJ) := by
    intro x y hxy
    apply le_of_not_gt
    intro hyx
    have hbad := coreAffineHomeomorph_strictMono J hJ hyx
    have hbad' : y < x := by simpa [coreEmbeddingMap] using hbad
    exact (not_lt_of_ge hxy) hbad'
  apply hmono.strictMono_of_injective
  intro x y hxy
  apply (coreAffineHomeomorph J hJ).symm.injective
  apply Subtype.ext
  exact hxy

theorem range_coreEmbeddingMap
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) :
    Set.range (coreEmbeddingMap J hJ) = J.carrier := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((coreAffineHomeomorph J hJ).symm y).2
  · intro hx
    let z : J.carrier := ⟨x, hx⟩
    refine ⟨coreAffineHomeomorph J hJ z, ?_⟩
    change ((coreAffineHomeomorph J hJ).symm
      (coreAffineHomeomorph J hJ z)).1 = x
    simp [z]

/-- Explicit affine formula for the embedding into a core. -/
theorem coreEmbeddingMap_affine
    (J : ClosedSubinterval) (hJ : J.Nondegenerate) :
    ∃ m c : ℝ, 0 < m ∧
      ∀ x : I, (coreEmbeddingMap J hJ x : ℝ) = m * (x : ℝ) + c := by
  refine ⟨(J.right : ℝ) - J.left, (J.left : ℝ), sub_pos.mpr hJ, ?_⟩
  intro x
  simp [coreEmbeddingMap, coreAffineHomeomorph,
    coreCarrierRealHomeomorph, iccHomeoI_symm_apply_coe]

/-- Conjugate a core-preserving map into the affine unit coordinate. -/
noncomputable def rescaledCoreMap
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    (T : IntervalMap) (hmap : MapsTo T J.carrier J.carrier) : IntervalMap :=
  fun x => coreAffineHomeomorph J hJ
    ⟨T ((coreAffineHomeomorph J hJ).symm x).1,
      hmap ((coreAffineHomeomorph J hJ).symm x).2⟩

theorem rescaledCoreMap_conjugacy
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    (T : IntervalMap) (hmap : MapsTo T J.carrier J.carrier)
    (x : J.carrier) :
    rescaledCoreMap J hJ T hmap (coreAffineHomeomorph J hJ x) =
      coreAffineHomeomorph J hJ ⟨T x.1, hmap x.2⟩ := by
  simp [rescaledCoreMap]

theorem coreEmbeddingMap_intertwines_rescaledCoreMap
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    (T : IntervalMap) (hmap : MapsTo T J.carrier J.carrier) :
    Intertwines (coreEmbeddingMap J hJ)
      (rescaledCoreMap J hJ T hmap) T := by
  intro x
  simp [coreEmbeddingMap, rescaledCoreMap]

/-! ## Finite-piece and dynamical transport -/

/-- The inverse affine coordinate, clipped to `I` outside the core. -/
noncomputable def clippedAffineCoordinate
    (a b : I) (_hab : a < b) : IntervalMap :=
  fun x => Set.projIcc (0 : ℝ) 1 zero_le_one
    (((x : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)))

theorem clippedAffineCoordinate_continuous
    (a b : I) (hab : a < b) :
    Continuous (clippedAffineCoordinate a b hab) := by
  apply continuous_projIcc.comp
  fun_prop

theorem clippedAffineCoordinate_monotone
    (a b : I) (hab : a < b) :
    Monotone (clippedAffineCoordinate a b hab) := by
  intro x y hxy
  apply Set.monotone_projIcc zero_le_one
  have hden : (0 : ℝ) < (b : ℝ) - (a : ℝ) := sub_pos.mpr hab
  rw [div_le_div_iff_of_pos_right hden]
  have hxyreal : (x : ℝ) ≤ (y : ℝ) := hxy
  exact sub_le_sub_right hxyreal _

theorem clippedAffineCoordinate_of_mem
    (a b : I) (hab : a < b) (x : I) (hx : x ∈ Set.Icc a b) :
    (clippedAffineCoordinate a b hab x : ℝ) =
      ((x : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) := by
  have hd : (0 : ℝ) < (b : ℝ) - (a : ℝ) := sub_pos.mpr hab
  have hq0 : (0 : ℝ) ≤
      ((x : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) :=
    div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hq1 : ((x : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) ≤ 1 := by
    rw [div_le_one hd]
    have hxb : (x : ℝ) ≤ (b : ℝ) := hx.2
    exact sub_le_sub_right hxb _
  exact congrArg Subtype.val
    (Set.projIcc_of_mem zero_le_one ⟨hq0, hq1⟩)

/-- Affine restriction and rescaling preserve finite-piece weak
monotonicity. -/
theorem FinitePieceMonotone.rescaledCoreMap
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (hmap : MapsTo T J.carrier J.carrier) :
    FinitePieceMonotone
      (CommutingIntervalSimplified.rescaledCoreMap J hJ T hmap) := by
  have hfactor : CommutingIntervalSimplified.rescaledCoreMap J hJ T hmap =
      clippedAffineCoordinate J.left J.right hJ ∘ T ∘
        coreEmbeddingMap J hJ := by
    funext x
    apply Subtype.ext
    have hTx : T (coreEmbeddingMap J hJ x) ∈ Set.Icc J.left J.right :=
      hmap ((coreAffineHomeomorph J hJ).symm x).2
    have hclip := clippedAffineCoordinate_of_mem J.left J.right hJ
      (T (coreEmbeddingMap J hJ x)) hTx
    change ((coreAffineHomeomorph J hJ
        ⟨T ((coreAffineHomeomorph J hJ).symm x).1,
          hmap ((coreAffineHomeomorph J hJ).symm x).2⟩ : I) : ℝ) =
      (clippedAffineCoordinate J.left J.right hJ
        (T (coreEmbeddingMap J hJ x)) : ℝ)
    simp only [coreAffineHomeomorph, Homeomorph.trans_apply,
      iccHomeoI_apply_coe]
    exact hclip.symm
  rw [hfactor]
  exact (FinitePieceMonotone.of_monotone
      (clippedAffineCoordinate_continuous J.left J.right hJ)
      (clippedAffineCoordinate_monotone J.left J.right hJ)).comp
    (hT.comp (FinitePieceMonotone.of_monotone
      (coreEmbeddingMap_continuous J hJ)
      (coreEmbeddingMap_strictMono J hJ).monotone))

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

theorem rescaledCoreMap_commute
    (J : ClosedSubinterval) (hJ : J.Nondegenerate)
    {P Q : IntervalMap} (hPmap : MapsTo P J.carrier J.carrier)
    (hQmap : MapsTo Q J.carrier J.carrier)
    (hcomm : Function.Commute P Q) :
    Function.Commute (rescaledCoreMap J hJ P hPmap)
      (rescaledCoreMap J hJ Q hQmap) := by
  intro x
  simp only [rescaledCoreMap, Homeomorph.symm_apply_apply]
  apply congrArg (coreAffineHomeomorph J hJ)
  apply Subtype.ext
  exact hcomm ((coreAffineHomeomorph J hJ).symm x).1

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

/-! ## Minimality and surjectivity transport -/

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
      P' (e x) = e ⟨P x.1, hminimal.1.1 x.2⟩ :=
    rescaledCoreMap_conjugacy J hJ P hminimal.1.1 x
  have hconjQ (x : J.carrier) :
      Q' (e x) = e ⟨Q x.1, hminimal.1.2 x.2⟩ :=
    rescaledCoreMap_conjugacy J hJ Q hminimal.1.2 x
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
      · simpa [Kcore, e] using heMono hz.1
      · simpa [Kcore, e] using heMono hz.2
    · intro hz
      constructor
      · simpa [Kcore, e] using heInvMono hz.1
      · simpa [Kcore, e] using heInvMono hz.2
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

/-- Each generator maps a minimal common invariant core onto itself. -/
theorem minimalCommonInvariantCore_mapsOnto
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (hcommute : Function.Commute P Q) (J : ClosedSubinterval)
    (hminimal : IsMinimalCommonInvariantCore P Q J) :
    Set.SurjOn P J.carrier J.carrier ∧
      Set.SurjOn Q J.carrier J.carrier := by
  have generator_onto (F G : IntervalMap)
      (hF : Continuous F) (hcommFG : Function.Commute F G)
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
      exact ⟨G x, hmapG hx, hcommFG x⟩
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

end CommutingIntervalSimplified
