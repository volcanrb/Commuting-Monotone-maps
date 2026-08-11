import CommutingIntervalSimplified.Base
import CommutingIntervalSimplified.ArcLikeBase
import CommutingIntervalSimplified.ArcLikeFixedSet
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Regular

/-!
# A common positive iterate

This file records the complete inverse-limit skeleton for the manuscript's
`Common positive iterate` lemma.  The quoted Fugate--McLean input is isolated
as a separate declaration with exactly the arc-like special case needed here.
-/

namespace CommutingIntervalSimplified

open Function Set

/-- The eventual range `⋂ n, Tⁿ(I)` of an interval map. -/
def eventualRange (T : IntervalMap) : Set I :=
  ⋂ n : ℕ, iterateMap T n '' Set.univ

/-- The one-sided natural extension (inverse limit) of an interval map. -/
def NaturalExtension (T : IntervalMap) :=
  {x : ℕ → I // ∀ i : ℕ, T (x (i + 1)) = x i}

instance (T : IntervalMap) : TopologicalSpace (NaturalExtension T) :=
  inferInstanceAs (TopologicalSpace {x : ℕ → I // ∀ i : ℕ, T (x (i + 1)) = x i})

/-- Coordinate projection from a natural extension. -/
def NaturalExtension.proj (T : IntervalMap) (n : ℕ) : NaturalExtension T → I :=
  fun x => x.1 n

/-- A map commuting with the bonding map acts coordinatewise on its natural
extension. -/
def NaturalExtension.coordinateMap (T F : IntervalMap)
    (hcomm : Function.Commute F T) : NaturalExtension T → NaturalExtension T :=
  fun x =>
    ⟨fun i => F (x.1 i), fun i => by
      calc
        T (F (x.1 (i + 1))) = F (T (x.1 (i + 1))) :=
          (hcomm (x.1 (i + 1))).symm
        _ = F (x.1 i) := congrArg F (x.2 i)⟩

/-- Coordinatewise action is continuous. -/
theorem NaturalExtension.continuous_coordinateMap
    (T F : IntervalMap) (hcomm : Function.Commute F T) (hF : Continuous F) :
    Continuous (NaturalExtension.coordinateMap T F hcomm) := by
  apply continuous_induced_rng.mpr
  exact continuous_pi fun i =>
    hF.comp ((continuous_apply i).comp continuous_subtype_val)

/-- The inverse coordinate formula for a positive iterative root of the
bonding map. -/
def NaturalExtension.rootInverse (T F : IntervalMap) (k : ℕ)
    (hroot : iterateMap F (k + 1) = T) :
    NaturalExtension T → NaturalExtension T :=
  fun x => by
    have hFT : Function.Commute F T := by
      rw [← hroot]
      exact Function.Commute.self_iterate F (k + 1)
    refine ⟨fun i => iterateMap F k (x.1 (i + 1)), ?_⟩
    intro i
    calc
      T (iterateMap F k (x.1 (i + 2))) =
          iterateMap F k (T (x.1 (i + 2))) :=
        (hFT.iterate_left k (x.1 (i + 2))).symm
      _ = iterateMap F k (x.1 (i + 1)) := by
        congr 1
        simpa [Nat.add_assoc] using x.2 (i + 1)

/-- A positive iterative root of the bonding map induces a homeomorphism of
the natural extension. -/
noncomputable def NaturalExtension.rootHomeomorph
    (T F : IntervalMap) (k : ℕ) (hF : Continuous F)
    (hroot : iterateMap F (k + 1) = T) :
    NaturalExtension T ≃ₜ NaturalExtension T := by
  have hFT : Function.Commute F T := by
    rw [← hroot]
    exact Function.Commute.self_iterate F (k + 1)
  let forward := NaturalExtension.coordinateMap T F hFT
  let inverse := NaturalExtension.rootInverse T F k hroot
  refine
    { toFun := forward
      invFun := inverse
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := NaturalExtension.continuous_coordinateMap T F hFT hF
      continuous_invFun := ?_ }
  · intro x
    apply Subtype.ext
    funext i
    change iterateMap F k (F (x.1 (i + 1))) = x.1 i
    calc
      iterateMap F k (F (x.1 (i + 1))) =
          iterateMap F (k + 1) (x.1 (i + 1)) :=
        (Function.iterate_succ_apply F k (x.1 (i + 1))).symm
      _ = T (x.1 (i + 1)) := congrFun hroot (x.1 (i + 1))
      _ = x.1 i := x.2 i
  · intro x
    apply Subtype.ext
    funext i
    change F (iterateMap F k (x.1 (i + 1))) = x.1 i
    calc
      F (iterateMap F k (x.1 (i + 1))) =
          iterateMap F (k + 1) (x.1 (i + 1)) :=
        (Function.iterate_succ_apply' (f := F) k (x.1 (i + 1))).symm
      _ = T (x.1 (i + 1)) := congrFun hroot (x.1 (i + 1))
      _ = x.1 i := x.2 i
  · apply continuous_induced_rng.mpr
    exact continuous_pi fun i =>
      (IntervalMap.continuous_iterate hF k).comp
        ((continuous_apply (i + 1)).comp continuous_subtype_val)

@[simp] theorem NaturalExtension.rootHomeomorph_apply_coord
    (T F : IntervalMap) (k : ℕ) (hF : Continuous F)
    (hroot : iterateMap F (k + 1) = T)
    (x : NaturalExtension T) (i : ℕ) :
    ((NaturalExtension.rootHomeomorph T F k hF hroot x).1 i) = F (x.1 i) := by
  rfl

/-- Coordinates of an iterate of a root homeomorphism are the corresponding
iterates of the root map. -/
theorem NaturalExtension.rootHomeomorph_iterate_coord
    (T F : IntervalMap) (k : ℕ) (hF : Continuous F)
    (hroot : iterateMap F (k + 1) = T)
    (r : ℕ) (x : NaturalExtension T) (i : ℕ) :
    (((NaturalExtension.rootHomeomorph T F k hF hroot :
        NaturalExtension T → NaturalExtension T)^[r] x).1 i) =
      iterateMap F r (x.1 i) := by
  induction r generalizing x with
  | zero => simp [iterateMap]
  | succ r ih =>
      rw [Function.iterate_succ_apply]
      rw [ih]
      simp only [NaturalExtension.rootHomeomorph_apply_coord]
      simp [iterateMap, Function.iterate_succ_apply]

/-- The eventual range is a nonempty compact interval and `T` maps it onto
itself. -/
theorem eventualRange_package {T : IntervalMap} (hT : Continuous T) :
    (eventualRange T).Nonempty ∧ IsCompact (eventualRange T) ∧
      IsPreconnected (eventualRange T) ∧
      T '' eventualRange T = eventualRange T := by
  let K : ℕ → Set I := fun n => iterateMap T n '' Set.univ
  have hKnonempty : ∀ n, (K n).Nonempty := by
    intro n
    exact ⟨iterateMap T n leftEndpoint, ⟨leftEndpoint, Set.mem_univ _, rfl⟩⟩
  have hKcompact : ∀ n, IsCompact (K n) := by
    intro n
    exact isCompact_univ.image (IntervalMap.continuous_iterate hT n)
  have hKclosed : ∀ n, IsClosed (K n) := fun n => (hKcompact n).isClosed
  have hKdecreasing : ∀ n, K (n + 1) ⊆ K n := by
    intro n z hz
    rcases hz with ⟨x, -, rfl⟩
    refine ⟨T x, Set.mem_univ _, ?_⟩
    simp [iterateMap, Function.iterate_succ_apply]
  have hKpreconnected : ∀ n, IsPreconnected (K n) := by
    intro n
    exact isPreconnected_univ.image _
      (IntervalMap.continuous_iterate hT n).continuousOn
  have hnonempty : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hKdecreasing hKnonempty (hKcompact 0) hKclosed
  have hcompact : IsCompact (⋂ n, K n) :=
    isCompact_univ.of_isClosed_subset (isClosed_iInter hKclosed)
      (Set.subset_univ (⋂ n, K n))
  have hpreconnected : IsPreconnected (⋂ n, K n) :=
    (ordConnected_iInter fun n => (hKpreconnected n).ordConnected).isPreconnected
  have himage : T '' (⋂ n, K n) = ⋂ n, K n := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      rw [Set.mem_iInter] at hx ⊢
      intro n
      cases n with
      | zero =>
          change T x ∈ iterateMap T 0 '' Set.univ
          simp [iterateMap]
      | succ n =>
          rcases hx n with ⟨y, -, hy⟩
          refine ⟨y, Set.mem_univ _, ?_⟩
          rw [← hy]
          simp [iterateMap, Function.iterate_succ_apply']
    · intro x hx
      have hx' : ∀ n, x ∈ K n := Set.mem_iInter.mp hx
      let L : ℕ → Set I := fun n => K n ∩ T ⁻¹' {x}
      have hLnonempty : ∀ n, (L n).Nonempty := by
        intro n
        rcases hx' (n + 1) with ⟨y, -, hy⟩
        refine ⟨iterateMap T n y, ⟨⟨y, Set.mem_univ _, rfl⟩, ?_⟩⟩
        change T (iterateMap T n y) = x
        simpa [iterateMap, Function.iterate_succ_apply'] using hy
      have hLdecreasing : ∀ n, L (n + 1) ⊆ L n := by
        intro n z hz
        exact ⟨hKdecreasing n hz.1, hz.2⟩
      have hLclosed : ∀ n, IsClosed (L n) := by
        intro n
        exact (hKclosed n).inter (isClosed_singleton.preimage hT)
      have hLcompact0 : IsCompact (L 0) :=
        (hKcompact 0).of_isClosed_subset (hLclosed 0) Set.inter_subset_left
      have hLint : (⋂ n, L n).Nonempty :=
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
          L hLdecreasing hLnonempty hLcompact0 hLclosed
      obtain ⟨z, hz⟩ := hLint
      have hzall : ∀ n, z ∈ L n := Set.mem_iInter.mp hz
      refine ⟨z, Set.mem_iInter.mpr (fun n => (hzall n).1), ?_⟩
      simpa using (hzall 0).2
  simpa [eventualRange, K] using
    And.intro hnonempty (And.intro hcompact (And.intro hpreconnected himage))

/-- A map commuting with `T` preserves the eventual range. -/
theorem mapsTo_eventualRange_of_commute {F T : IntervalMap}
    (hcomm : Function.Commute F T) :
    MapsTo F (eventualRange T) (eventualRange T) := by
  intro x hx
  rw [eventualRange] at hx ⊢
  simp only [Set.mem_iInter] at hx ⊢
  intro n
  rcases hx n with ⟨y, -, rfl⟩
  refine ⟨F y, Set.mem_univ _, ?_⟩
  exact (hcomm.iterate_right n y).symm

/-- For a continuous interval map, its natural extension is a nonempty compact
connected arc-like metric space. -/
theorem naturalExtension_isArcLike {T : IntervalMap} (hT : Continuous T) :
    Nonempty (NaturalExtension T) ∧
      IsCompact (Set.univ : Set (NaturalExtension T)) ∧
      IsConnected (Set.univ : Set (NaturalExtension T)) ∧
      IsArcLike (NaturalExtension T) := by
  classical
  let A : ℕ → Set (ℕ → I) := fun n x =>
    ∀ i, i < n → T (x (i + 1)) = x i
  have hAclosed : ∀ n, IsClosed (A n) := by
    intro n
    change IsClosed {x : ℕ → I | ∀ i, i < n → T (x (i + 1)) = x i}
    rw [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    rw [show {x : ℕ → I | i < n → T (x (i + 1)) = x i} =
        Set.iInter (fun (_h : i < n) =>
          {x : ℕ → I | T (x (i + 1)) = x i}) by
      exact Set.setOf_forall
        (fun (_h : i < n) (x : ℕ → I) => T (x (i + 1)) = x i)]
    apply isClosed_iInter
    intro _hi
    exact isClosed_eq (hT.comp (continuous_apply (i + 1)))
      (continuous_apply i)
  have hAdec : ∀ n x, A (n + 1) x → A n x := by
    intro n x hx i hi
    exact hx i (by omega)
  have hAne : ∀ n, (A n).Nonempty := by
    intro n
    let x : ℕ → I := fun i =>
      if hi : i ≤ n then iterateMap T (n - i) leftEndpoint else leftEndpoint
    apply Exists.intro x
    intro i hi
    have hi0 : i ≤ n := by omega
    have hi1 : i + 1 ≤ n := by omega
    simp only [x, dif_pos hi0, dif_pos hi1]
    rw [show n - i = (n - (i + 1)) + 1 by omega]
    exact (Function.iterate_succ_apply' T (n - (i + 1)) leftEndpoint).symm
  have hstage_back : ∀ i n, i ≤ n → ∀ x, A n x →
      iterateMap T (n - i) (x n) = x i := by
    intro i n hi
    induction n, hi using Nat.le_induction with
    | base =>
        intro x _hx
        simp [iterateMap]
    | @succ n _hin ih =>
        intro x hx
        rw [show n + 1 - i = (n - i) + 1 by omega]
        rw [iterateMap, Function.iterate_succ_apply]
        rw [hx n (by omega)]
        exact ih x (fun j hj => hx j (by omega))
  have hAcompact : ∀ n, IsCompact (A n) := by
    intro n
    exact isCompact_univ.of_isClosed_subset (hAclosed n) (Set.subset_univ _)
  have hAconn : ∀ n, IsConnected (A n) := by
    intro n
    let p : (ℕ → I) → (ℕ → I) := fun y i =>
      if hi : i ≤ n then iterateMap T (n - i) (y n) else y i
    have hpcont : Continuous p := by
      apply continuous_pi
      intro i
      by_cases hi : i ≤ n
      case pos =>
        simp only [p, dif_pos hi]
        exact (IntervalMap.continuous_iterate hT (n - i)).comp
          (continuous_apply n)
      case neg =>
        simp only [p, dif_neg hi]
        exact continuous_apply i
    have hpA1 : ∀ z, z ∈ p '' Set.univ → A n z := by
      intro z hz
      rcases hz with ⟨y, _hy, rfl⟩
      intro i hi
      have hi0 : i ≤ n := by omega
      have hi1 : i + 1 ≤ n := by omega
      simp only [p, dif_pos hi0, dif_pos hi1]
      rw [show n - i = (n - (i + 1)) + 1 by omega]
      exact (Function.iterate_succ_apply' T (n - (i + 1)) (y n)).symm
    have hpA2 : ∀ x, A n x → x ∈ p '' Set.univ := by
      intro x hx
      refine ⟨x, Set.mem_univ _, ?_⟩
      funext i
      by_cases hi : i ≤ n
      case pos =>
        simp only [p, dif_pos hi]
        exact hstage_back i n hi x hx
      case neg => simp only [p, dif_neg hi]
    have hpA : p '' Set.univ = A n := Set.Subset.antisymm hpA1 hpA2
    rw [← hpA]
    exact isConnected_univ.image p hpcont.continuousOn

  let K : Set (ℕ → I) := Set.iInter A
  have hKne : K.Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      A hAdec hAne (hAcompact 0) hAclosed
  have hKclosed : IsClosed K := isClosed_iInter hAclosed
  have hKcompact : IsCompact K :=
    isCompact_univ.of_isClosed_subset hKclosed (Set.subset_univ _)
  have hKpre : IsPreconnected K := by
    intro u v hu hv hKuv hKu hKv
    by_contra hnone
    let S : Set (ℕ → I) := Set.inter K u
    let R : Set (ℕ → I) := Set.inter K v
    have hSeq : S = Set.inter K v.compl := by
      ext x
      change (K x ∧ u x) ↔ (K x ∧ ¬v x)
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        intro hxv
        exact hnone ⟨x, hx.1, hx.2, hxv⟩
      · intro hx
        exact ⟨hx.1, (hKuv hx.1).resolve_right hx.2⟩
    have hReq : R = Set.inter K u.compl := by
      ext x
      change (K x ∧ v x) ↔ (K x ∧ ¬u x)
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        intro hxu
        exact hnone ⟨x, hx.1, hxu, hx.2⟩
      · intro hx
        exact ⟨hx.1, (hKuv hx.1).resolve_left hx.2⟩
    have hSclosed : IsClosed S := by
      rw [hSeq]
      exact hKclosed.inter hv.isClosed_compl
    have hRclosed : IsClosed R := by
      rw [hReq]
      exact hKclosed.inter hu.isClosed_compl
    have hSRdisj : Disjoint S R := by
      rw [Set.disjoint_left]
      intro x hxS hxR
      exact hnone ⟨x, hxS.1, hxS.2, hxR.2⟩
    obtain ⟨U, V, hUopen, hVopen, hSU, hRV, hUV⟩ :=
      normal_separation hSclosed hRclosed hSRdisj
    have hKcover : ∀ x, K x → Set.union U V x := by
      intro x hx
      rcases hKuv hx with hxu | hxv
      · exact Or.inl (hSU ⟨hx, hxu⟩)
      · exact Or.inr (hRV ⟨hx, hxv⟩)
    have hstageCover : ∃ N, ∀ x, A N x → Set.union U V x := by
      by_contra hnot
      let L : ℕ → Set (ℕ → I) := fun n =>
        Set.inter (A n) (Set.union U V).compl
      have hLne : ∀ n, (L n).Nonempty := by
        intro n
        have hn : ¬(∀ x, A n x → Set.union U V x) := by
          intro hnall
          exact hnot ⟨n, hnall⟩
        simp only [Classical.not_forall, Classical.not_imp] at hn
        rcases hn with ⟨x, hxA, hxout⟩
        exact ⟨x, hxA, hxout⟩
      have hLclosed : ∀ n, IsClosed (L n) := by
        intro n
        exact (hAclosed n).inter (hUopen.union hVopen).isClosed_compl
      have hLdec : ∀ n x, L (n + 1) x → L n x := by
        intro n x hx
        exact ⟨hAdec n x hx.1, hx.2⟩
      have hLcompact0 : IsCompact (L 0) :=
        isCompact_univ.of_isClosed_subset (hLclosed 0) (Set.subset_univ _)
      have hLint :=
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
          L hLdec hLne hLcompact0 hLclosed
      rcases hLint with ⟨x, hxall⟩
      have hxK : K x := by
        apply Set.mem_iInter.mpr
        intro n
        exact (Set.mem_iInter.mp hxall n).1
      exact (Set.mem_iInter.mp hxall 0).2 (hKcover x hxK)
    obtain ⟨N, hANsub⟩ := hstageCover
    have hANU : (Set.inter (A N) U).Nonempty := by
      rcases hKu with ⟨x, hxK, hxu⟩
      exact ⟨x, Set.mem_iInter.mp hxK N, hSU ⟨hxK, hxu⟩⟩
    have hANV : (Set.inter (A N) V).Nonempty := by
      rcases hKv with ⟨x, hxK, hxv⟩
      exact ⟨x, Set.mem_iInter.mp hxK N, hRV ⟨hxK, hxv⟩⟩
    have hoverlap :=
      (hAconn N).isPreconnected U V hUopen hVopen hANsub hANU hANV
    rcases hoverlap with ⟨x, _hxA, hxU, hxV⟩
    exact Set.disjoint_left.mp hUV hxU hxV
  have hKconn : IsConnected K := ⟨hKne, hKpre⟩
  have hKcarrier : K = {x : ℕ → I | ∀ i, T (x (i + 1)) = x i} := by
    ext x
    constructor
    · intro hx i
      exact (Set.mem_iInter.mp hx (i + 1)) i (by omega)
    · intro hx
      apply Set.mem_iInter.mpr
      intro n i _hi
      exact hx i
  let carrier : Set (ℕ → I) := {x | ∀ i, T (x (i + 1)) = x i}
  have hKcarrier' : K = carrier := by
    simpa [carrier] using hKcarrier
  have hnonempty : Nonempty (NaturalExtension T) := by
    rcases hKne with ⟨x, hx⟩
    apply Nonempty.intro
    refine { val := x, property := ?_ }
    change carrier x
    rw [← hKcarrier']
    exact hx
  letI : Nonempty (NaturalExtension T) := hnonempty
  have hcarriercompact : IsCompact carrier := by
    rw [← hKcarrier']
    exact hKcompact
  have hcarrierconn : IsConnected carrier := by
    rw [← hKcarrier']
    exact hKconn
  have hvalsub1 : ∀ x,
      x ∈ (fun z : NaturalExtension T => z.1) '' Set.univ → carrier x := by
    rintro x ⟨z, _hzuniv, rfl⟩
    exact z.2
  have hvalsub2 : ∀ x, carrier x →
      x ∈ (fun z : NaturalExtension T => z.1) '' Set.univ := by
    intro x hx
    exact ⟨({ val := x, property := hx } : NaturalExtension T), Set.mem_univ _, rfl⟩
  have hvalimage :
      (fun z : NaturalExtension T => z.1) '' Set.univ = carrier :=
    Set.Subset.antisymm hvalsub1 hvalsub2
  have hNEcompact : IsCompact (Set.univ : Set (NaturalExtension T)) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    change IsCompact ((fun z : NaturalExtension T => z.1) '' Set.univ)
    rw [hvalimage]
    exact hcarriercompact
  have hNEconn : IsConnected (Set.univ : Set (NaturalExtension T)) := by
    constructor
    · exact Set.univ_nonempty
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      change IsPreconnected ((fun z : NaturalExtension T => z.1) '' Set.univ)
      rw [hvalimage]
      exact hcarrierconn.isPreconnected

  have harclike : IsArcLike (NaturalExtension T) := by
    letI : TopologicalSpace.MetrizableSpace (NaturalExtension T) := by
      exact Topology.IsEmbedding.subtypeVal.metrizableSpace
    let _ : MetricSpace (NaturalExtension T) :=
      TopologicalSpace.metrizableSpaceMetric _
    have hcoord {x y : NaturalExtension T} {i N : ℕ}
        (hi : i ≤ N) (hN : x.1 N = y.1 N) : x.1 i = y.1 i := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
      subst N
      induction k generalizing i with
      | zero => simpa using hN
      | succ k ih =>
          have hind : i + 1 + k = i + (k + 1) := by omega
          have htop : x.1 (i + 1 + k) = y.1 (i + 1 + k) := by
            rw [hind]
            exact hN
          have hnext : x.1 (i + 1) = y.1 (i + 1) :=
            ih (i := i + 1) (by omega) htop
          calc
            x.1 i = T (x.1 (i + 1)) := (x.2 i).symm
            _ = T (y.1 (i + 1)) := congrArg T hnext
            _ = y.1 i := y.2 i
    intro cover hopen hcover
    have hcoverne : cover.Nonempty := by
      let x0 : NaturalExtension T := Classical.choice inferInstance
      have hxcover := hcover (Set.mem_univ x0)
      rcases Set.mem_sUnion.mp hxcover with ⟨W, hW, _hxW⟩
      exact ⟨W, hW⟩
    obtain ⟨δ, hδ, hLeb⟩ :=
      lebesgue_number_lemma_of_metric_sUnion hNEcompact hopen hcover
    have hcyl : ∀ x : NaturalExtension T,
        ∃ J : Finset ℕ, ∃ w : ℕ → Set I,
          (∀ i, i ∈ J → IsOpen (w i) ∧ x.1 i ∈ w i) ∧
            ∀ z : NaturalExtension T,
              z.1 ∈ (J : Set ℕ).pi w → z ∈ Metric.ball x (δ / 2) := by
      intro x
      have hballopen : IsOpen (Metric.ball x (δ / 2)) := Metric.isOpen_ball
      obtain ⟨O, hOopen, hOeq⟩ :=
        Topology.IsInducing.subtypeVal.isOpen_iff.mp hballopen
      have hxball : x ∈ Metric.ball x (δ / 2) :=
        Metric.mem_ball_self (half_pos hδ)
      have hxO : x.1 ∈ O := by
        rw [← hOeq] at hxball
        exact hxball
      obtain ⟨J, w, hJpkg⟩ := isOpen_pi_iff.mp hOopen x.1 hxO
      refine ⟨J, w, hJpkg.1, ?_⟩
      intro z hz
      have hzO : z.1 ∈ O := hJpkg.2 hz
      exact (Set.ext_iff.mp hOeq z).mp hzO
    choose J w hJopenmem hJball using hcyl
    let D : NaturalExtension T → Set (NaturalExtension T) := fun x z =>
      z.1 ∈ (J x : Set ℕ).pi (w x)
    have hDopen : ∀ x, IsOpen (D x) := by
      intro x
      have hopenpi : IsOpen ((J x : Set ℕ).pi (w x)) := by
        apply isOpen_set_pi (J x).finite_toSet
        intro i hi
        exact (hJopenmem x i hi).1
      exact hopenpi.preimage continuous_subtype_val
    have hxD : ∀ x, x ∈ D x := by
      intro x i hi
      exact (hJopenmem x i hi).2
    have hDcover : Set.univ ⊆ Set.iUnion D := by
      intro x _hx
      exact Set.mem_iUnion_of_mem x (hxD x)
    obtain ⟨centers, hcenters⟩ :=
      hNEcompact.elim_finite_subcover D hDopen hDcover
    let N : ℕ := centers.sup (fun x => (J x).sup id)
    have hbound : ∀ c, c ∈ centers → ∀ i, i ∈ J c → i ≤ N := by
      intro c hc i hi
      calc
        i ≤ (J c).sup id := Finset.le_sup (f := id) hi
        _ ≤ N := Finset.le_sup (f := fun x => (J x).sup id) hc
    have hfiberSmall : ∀ y z : NaturalExtension T,
        y.1 N = z.1 N → dist y z < δ := by
      intro y z hyzN
      have hycover := hcenters (Set.mem_univ y)
      rcases Set.mem_iUnion.mp hycover with ⟨c, hcPkg⟩
      rcases Set.mem_iUnion.mp hcPkg with ⟨hc, hyD⟩
      have hzD : z ∈ D c := by
        intro i hi
        have hyi : y.1 i ∈ w c i := hyD i hi
        have hiyz : y.1 i = z.1 i :=
          hcoord (hbound c hc i hi) hyzN
        rw [← hiyz]
        exact hyi
      have hyball := hJball c y hyD
      have hzball := hJball c z hzD
      calc
        dist y z ≤ dist y c + dist c z := dist_triangle _ _ _
        _ = dist y c + dist z c := by rw [dist_comm c z]
        _ < δ / 2 + δ / 2 :=
          add_lt_add (Metric.mem_ball.mp hyball) (Metric.mem_ball.mp hzball)
        _ = δ := add_halves δ
    let φ : NaturalExtension T → I := NaturalExtension.proj T N
    have hφcont : Continuous φ :=
      (continuous_apply N).comp continuous_subtype_val
    refine ⟨φ, hφcont, ?_⟩
    intro q
    by_cases hfne : ({z | φ z = q} : Set (NaturalExtension T)).Nonempty
    · rcases hfne with ⟨x, hx⟩
      have hxp : φ x = q := hx
      obtain ⟨W, hW, hballW⟩ := hLeb x (Set.mem_univ x)
      refine ⟨W, hW, ?_⟩
      intro z hz
      apply hballW
      apply Metric.mem_ball.mpr
      rw [dist_comm]
      apply hfiberSmall x z
      have hzp : φ z = q := hz
      exact hxp.trans hzp.symm
    · rcases hcoverne with ⟨W, hW⟩
      refine ⟨W, hW, ?_⟩
      intro z hz
      exact False.elim (hfne ⟨z, hz⟩)
  exact ⟨hnonempty, hNEcompact, hNEconn, harclike⟩

/-- Arc-like compact metric spaces are hereditarily unicoherent: the
intersection of any two subcontinua is connected (or empty).  This is the
cover-theoretic form needed in the periodic fixed-set argument below. -/
theorem arcLike_inter_preconnected
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (harc : IsArcLike X)
    {A B : Set X} (hAcompact : IsCompact A) (hBcompact : IsCompact B)
    (hApre : IsPreconnected A) (hBpre : IsPreconnected B) :
    IsPreconnected (A ∩ B) := by
  classical
  let C : Set X := A ∩ B
  have hCclosed : IsClosed C := hAcompact.isClosed.inter hBcompact.isClosed
  by_contra hCnot
  change ¬ IsPreconnected C at hCnot
  rw [isPreconnected_iff_subset_of_disjoint] at hCnot
  push Not at hCnot
  rcases hCnot with
    ⟨u, v, hu, hv, hCcover, hCdis, hCnotu, hCnotv⟩
  let P : Set X := C \ v
  let Q : Set X := C \ u
  have hPclosed : IsClosed P := hCclosed.sdiff hv
  have hQclosed : IsClosed Q := hCclosed.sdiff hu
  have hPQ : Disjoint P Q := by
    rw [Set.disjoint_left]
    intro y hyP hyQ
    rcases hCcover hyP.1 with hyu | hyv
    · exact hyQ.2 hyu
    · exact hyP.2 hyv
  have hCPQ : C ⊆ P ∪ Q := by
    intro y hyC
    rcases hCcover hyC with hyu | hyv
    · left
      refine ⟨hyC, ?_⟩
      intro hyv
      have : y ∈ C ∩ (u ∩ v) := ⟨hyC, hyu, hyv⟩
      rw [hCdis] at this
      exact this
    · right
      refine ⟨hyC, ?_⟩
      intro hyu
      have : y ∈ C ∩ (u ∩ v) := ⟨hyC, hyu, hyv⟩
      rw [hCdis] at this
      exact this
  obtain ⟨p, hpC, hpnv⟩ := Set.not_subset.mp hCnotv
  obtain ⟨q, hqC, hqnu⟩ := Set.not_subset.mp hCnotu
  have hpP : p ∈ P := ⟨hpC, hpnv⟩
  have hqQ : q ∈ Q := ⟨hqC, hqnu⟩
  rcases normal_separation hPclosed hQclosed hPQ with
    ⟨UP, VQ, hUPopen, hVQopen, hPUP, hQVQ, hUPVQ⟩
  have hCUV : C ⊆ UP ∪ VQ := by
    intro y hyC
    rcases hCPQ hyC with hyP | hyQ
    · exact Or.inl (hPUP hyP)
    · exact Or.inr (hQVQ hyQ)
  have hpUP : p ∈ UP := hPUP hpP
  have hqVQ : q ∈ VQ := hQVQ hqQ
  let cover : Set (Set X) := {UP, VQ, Aᶜ, Bᶜ}
  have hopen : ∀ W ∈ cover, IsOpen W := by
    intro W hW
    simp only [cover, Set.mem_insert_iff, Set.mem_singleton_iff] at hW
    rcases hW with rfl | rfl | rfl | rfl
    · exact hUPopen
    · exact hVQopen
    · exact hAcompact.isClosed.isOpen_compl
    · exact hBcompact.isClosed.isOpen_compl
  have hcover : Set.univ ⊆ Set.sUnion cover := by
    intro y _hy
    by_cases hyA : y ∈ A
    · by_cases hyB : y ∈ B
      · rcases hCUV ⟨hyA, hyB⟩ with hyUP | hyVQ
        · apply Set.mem_sUnion_of_mem hyUP
          simp [cover]
        · apply Set.mem_sUnion_of_mem hyVQ
          simp [cover]
      · apply Set.mem_sUnion_of_mem (show y ∈ Bᶜ from hyB)
        simp [cover]
    · apply Set.mem_sUnion_of_mem (show y ∈ Aᶜ from hyA)
      simp [cover]
  obtain ⟨φ, hφ, hfib⟩ := harc cover hopen hcover
  let J : Set I := Set.uIcc (φ p) (φ q)
  let O₀ : Set I := (φ '' UPᶜ)ᶜ
  let O₁ : Set I := (φ '' VQᶜ)ᶜ
  have hO₀open : IsOpen O₀ := by
    dsimp [O₀]
    exact ((isClosed_compl_iff.mpr hUPopen).isCompact.image hφ).isClosed.isOpen_compl
  have hO₁open : IsOpen O₁ := by
    dsimp [O₁]
    exact ((isClosed_compl_iff.mpr hVQopen).isCompact.image hφ).isClosed.isOpen_compl
  have hpA : p ∈ A := hpC.1
  have hpB : p ∈ B := hpC.2
  have hqA : q ∈ A := hqC.1
  have hqB : q ∈ B := hqC.2
  have hJimageA : J ⊆ φ '' A := by
    intro y hyJ
    rcases Set.mem_uIcc.mp hyJ with hy | hy
    · exact hApre.intermediate_value hpA hqA hφ.continuousOn hy
    · exact hApre.intermediate_value hqA hpA hφ.continuousOn hy
  have hJimageB : J ⊆ φ '' B := by
    intro y hyJ
    rcases Set.mem_uIcc.mp hyJ with hy | hy
    · exact hBpre.intermediate_value hpB hqB hφ.continuousOn hy
    · exact hBpre.intermediate_value hqB hpB hφ.continuousOn hy
  have hfiberSide : ∀ y ∈ J,
      φ ⁻¹' {y} ⊆ UP ∨ φ ⁻¹' {y} ⊆ VQ := by
    intro y hyJ
    rcases hJimageA hyJ with ⟨a, haA, haφ⟩
    rcases hJimageB hyJ with ⟨b, hbB, hbφ⟩
    obtain ⟨W, hW, hWfiber⟩ := hfib y
    simp only [cover, Set.mem_insert_iff, Set.mem_singleton_iff] at hW
    rcases hW with rfl | rfl | rfl | rfl
    · exact Or.inl hWfiber
    · exact Or.inr hWfiber
    · exfalso
      have haFiber : a ∈ φ ⁻¹' {y} := by simpa using haφ
      exact (hWfiber haFiber) haA
    · exfalso
      have hbFiber : b ∈ φ ⁻¹' {y} := by simpa using hbφ
      exact (hWfiber hbFiber) hbB
  have hJcover : J ⊆ O₀ ∪ O₁ := by
    intro y hyJ
    rcases hfiberSide y hyJ with hyUP | hyVQ
    · left
      change y ∉ φ '' UPᶜ
      rintro ⟨z, hzUP, hzφ⟩
      apply hzUP
      apply hyUP
      simpa using hzφ
    · right
      change y ∉ φ '' VQᶜ
      rintro ⟨z, hzVQ, hzφ⟩
      apply hzVQ
      apply hyVQ
      simpa using hzφ
  have hJdis : J ∩ (O₀ ∩ O₁) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hy⟩
    rcases hJimageA hy.1 with ⟨a, _haA, haφ⟩
    have haUP : a ∈ UP := by
      by_contra ha
      apply hy.2.1
      exact ⟨a, ha, haφ⟩
    have haVQ : a ∈ VQ := by
      by_contra ha
      apply hy.2.2
      exact ⟨a, ha, haφ⟩
    exact (Set.disjoint_left.mp hUPVQ) haUP haVQ
  have hside :=
    (isPreconnected_iff_subset_of_disjoint.mp
      (isPreconnected_uIcc : IsPreconnected J))
      O₀ O₁ hO₀open hO₁open hJcover hJdis
  rcases hside with hJO₀ | hJO₁
  · have hφqO₀ : φ q ∈ O₀ := hJO₀ Set.right_mem_uIcc
    change φ q ∉ φ '' UPᶜ at hφqO₀
    apply hφqO₀
    refine ⟨q, ?_, rfl⟩
    intro hqUP
    exact (Set.disjoint_left.mp hUPVQ) hqUP hqVQ
  · have hφpO₁ : φ p ∈ O₁ := hJO₁ Set.left_mem_uIcc
    change φ p ∉ φ '' VQᶜ at hφpO₁
    apply hφpO₁
    refine ⟨p, ?_, rfl⟩
    intro hpVQ
    exact (Set.disjoint_left.mp hUPVQ) hpUP hpVQ

/-- A continuum disjoint from the fixed set of a finite-order homeomorphism
cannot contain both a point and its image.  The interval-valued approximation
turns displacement by the homeomorphism into a continuous function of
constant strict sign; summing around a finite orbit then gives the
contradiction. -/
private theorem periodicHomeomorph_no_moved_pair_in_continuum
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (harc : IsArcLike X) (V : X ≃ₜ X) {d : ℕ} (hd : 0 < d)
    (hperiodic : (V : X → X)^[d] = Homeomorph.refl X)
    {K : Set X} (hKcompact : IsCompact K) (hKpre : IsPreconnected K)
    {x : X} (hx : x ∈ K) (hVx : V x ∈ K)
    (hKavoid : ∀ y ∈ K, V y ≠ y) : False := by
  let sat : ℕ → Set X := fun n =>
    Nat.rec K (fun k S => S ∪ ((V : X → X)^[k + 1] '' K)) n
  have himageSat : ∀ n : ℕ, (V : X → X)^[n] '' K ⊆ sat n := by
    intro n
    cases n with
    | zero => simpa [sat]
    | succ n =>
        intro z hz
        exact Set.mem_union_right _ hz
  have hsatStep : ∀ n : ℕ, sat n ⊆ sat (n + 1) := by
    intro n z hz
    exact Set.mem_union_left _ hz
  have hsatMono : ∀ {m n : ℕ}, m ≤ n → sat m ⊆ sat n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact Set.Subset.rfl
    | succ n _ ih => exact ih.trans (hsatStep n)
  have hsatCompact : ∀ n : ℕ, IsCompact (sat n) := by
    intro n
    induction n with
    | zero => simpa [sat] using hKcompact
    | succ n ih =>
        simp only [sat, Nat.rec]
        exact ih.union (hKcompact.image (V.continuous.iterate (n + 1)))
  have hsatPre : ∀ n : ℕ, IsPreconnected (sat n) := by
    intro n
    induction n with
    | zero => simpa [sat] using hKpre
    | succ n ih =>
        simp only [sat, Nat.rec]
        apply ih.union ((V : X → X)^[n + 1] x)
        · apply himageSat n
          refine ⟨V x, hVx, ?_⟩
          exact (Function.iterate_succ_apply V n x).symm
        · exact ⟨x, hx, rfl⟩
        · exact hKpre.image _ (V.continuous.iterate (n + 1)).continuousOn
  have hiterateAvoid : ∀ n : ℕ, ∀ y ∈ K,
      V ((V : X → X)^[n] y) ≠ (V : X → X)^[n] y := by
    intro n y hy hfixed
    apply hKavoid y hy
    apply (V.injective.iterate n)
    calc
      (V : X → X)^[n] (V y) = (V : X → X)^[n + 1] y :=
        (Function.iterate_succ_apply V n y).symm
      _ = V ((V : X → X)^[n] y) :=
        Function.iterate_succ_apply' V n y
      _ = (V : X → X)^[n] y := hfixed
  have hsatAvoid : ∀ n : ℕ, ∀ y ∈ sat n, V y ≠ y := by
    intro n
    induction n with
    | zero => simpa [sat] using hKavoid
    | succ n ih =>
        intro y hy
        simp only [sat, Nat.rec] at hy
        rcases hy with hy | hy
        · exact ih y hy
        · rcases hy with ⟨z, hz, rfl⟩
          exact hiterateAvoid (n + 1) z hz
  let L : Set X := sat d
  have hLcompact : IsCompact L := hsatCompact d
  have hLpre : IsPreconnected L := hsatPre d
  have hxL : x ∈ L := by
    apply hsatMono (Nat.zero_le d)
    simpa [sat] using hx
  have hLavoid : ∀ y ∈ L, V y ≠ y := hsatAvoid d
  let disp : X → ℝ := fun y => dist (V y) y
  have hdispcont : Continuous disp := V.continuous.dist continuous_id
  obtain ⟨z, hzL, hzmin⟩ :=
    hLcompact.exists_isMinOn ⟨x, hxL⟩ hdispcont.continuousOn
  have hdispPos : 0 < disp z := by
    exact dist_pos.mpr (hLavoid z hzL)
  let cover : Set (Set X) :=
    Set.range (fun a : X => Metric.ball a (disp z / 2))
  have hopen : ∀ W, W ∈ cover → IsOpen W := by
    intro W hW
    rcases hW with ⟨a, rfl⟩
    exact Metric.isOpen_ball
  have hcover : Set.univ ⊆ Set.sUnion cover := by
    intro y _hy
    apply Set.mem_sUnion_of_mem (Metric.mem_ball_self (half_pos hdispPos))
    exact ⟨y, rfl⟩
  obtain ⟨φ, hφ, hfib⟩ := harc cover hopen hcover
  let q : X → ℝ := fun y => (φ (V y)).1 - (φ y).1
  have hqcont : Continuous q :=
    (continuous_subtype_val.comp (hφ.comp V.continuous)).sub
      (continuous_subtype_val.comp hφ)
  have hqne : ∀ y ∈ L, q y ≠ 0 := by
    intro y hyL hqy
    have hφeq : φ (V y) = φ y := by
      apply Subtype.ext
      exact sub_eq_zero.mp hqy
    obtain ⟨W, hW, hWfiber⟩ := hfib (φ y)
    rcases hW with ⟨a, rfl⟩
    have hyball : y ∈ Metric.ball a (disp z / 2) :=
      hWfiber (by simp)
    have hVyball : V y ∈ Metric.ball a (disp z / 2) :=
      hWfiber (by simp [hφeq])
    have hylt : disp y < disp z := by
      dsimp [disp]
      calc
        dist (V y) y ≤ dist (V y) a + dist a y := dist_triangle _ _ _
        _ = dist (V y) a + dist y a := by rw [dist_comm a y]
        _ < disp z / 2 + disp z / 2 :=
          add_lt_add (Metric.mem_ball.mp hVyball) (Metric.mem_ball.mp hyball)
        _ = disp z := add_halves (disp z)
    exact (not_lt_of_ge (hzmin hyL)) hylt
  have hsign :
      (∀ y ∈ L, q y < 0) ∨ (∀ y ∈ L, 0 < q y) := by
    rcases lt_or_gt_of_ne (hqne x hxL) with hxneg | hxpos
    · left
      intro y hyL
      rcases lt_trichotomy (q y) 0 with hyneg | hyeq | hypos
      · exact hyneg
      · exact False.elim ((hqne y hyL) hyeq)
      · have hzero : (0 : ℝ) ∈ q '' L :=
          (hLpre.intermediate_value hxL hyL hqcont.continuousOn)
            ⟨le_of_lt hxneg, le_of_lt hypos⟩
        rcases hzero with ⟨w, hwL, hqw⟩
        exact False.elim ((hqne w hwL) hqw)
    · right
      intro y hyL
      rcases lt_trichotomy (q y) 0 with hyneg | hyeq | hypos
      · have hzero : (0 : ℝ) ∈ q '' L :=
          (hLpre.intermediate_value hyL hxL hqcont.continuousOn)
            ⟨le_of_lt hyneg, le_of_lt hxpos⟩
        rcases hzero with ⟨w, hwL, hqw⟩
        exact False.elim ((hqne w hwL) hqw)
      · exact False.elim ((hqne y hyL) hyeq)
      · exact hypos
  have horbitMem : ∀ k < d, (V : X → X)^[k] x ∈ L := by
    intro k hk
    apply hsatMono (Nat.le_of_lt hk)
    apply himageSat k
    exact ⟨x, hx, rfl⟩
  have htel : ∀ n : ℕ,
      ∑ k ∈ Finset.range n, q ((V : X → X)^[k] x) =
        (φ ((V : X → X)^[n] x)).1 - (φ x).1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [q, Function.iterate_succ_apply']
        ring
  have horbit : (V : X → X)^[d] x = x := by
    simpa using congrFun hperiodic x
  have hsumzero :
      ∑ k ∈ Finset.range d, q ((V : X → X)^[k] x) = 0 := by
    rw [htel d, horbit, sub_self]
  rcases hsign with hneg | hpos
  · have hsumneg :
        ∑ k ∈ Finset.range d, q ((V : X → X)^[k] x) < 0 := by
      apply Finset.sum_neg
      · intro k hk
        exact hneg _ (horbitMem k (Finset.mem_range.mp hk))
      · exact ⟨0, Finset.mem_range.mpr hd⟩
    exact (ne_of_lt hsumneg) hsumzero
  · have hsumpos :
        0 < ∑ k ∈ Finset.range d, q ((V : X → X)^[k] x) := by
      apply Finset.sum_pos
      · intro k hk
        exact hpos _ (horbitMem k (Finset.mem_range.mp hk))
      · exact ⟨0, Finset.mem_range.mpr hd⟩
    exact (ne_of_gt hsumpos) hsumzero

/- Fugate--McLean's periodic fixed-set theorem, specialized to arc-like
continua.  The proof is internal to this development: it is split out here so
the downstream Bézout argument can be checked independently while the
equivariant arc-like approximation argument is developed. -/

/- The fixed-point set of a periodic homeomorphism of a nonempty compact
connected arc-like metric space is a nonempty continuum.  Fugate--McLean
prove the more general tree-like statement in Theorems 1.3--1.4, using an
invariant one-dimensional cover, its nerve graph, and a lift to the universal
covering tree.  Arc-like continua are tree-like, so this is the exact special
case used below. -/

/-- Every homeomorphism of a nonempty compact connected arc-like metric
space has a fixed point.  Arc-like coordinates give arbitrarily small
displacement; compactness turns these approximate fixed points into an exact
one. -/
theorem homeomorph_fixedSet_nonempty_of_arcLike
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) :
    {x : X | V x = x}.Nonempty := by
  letI : ConnectedSpace X := hconnected
  have happ : ∀ ε : ℝ, 0 < ε → ∃ z, dist (V z) z < ε := by
    intro ε hε
    let cover : Set (Set X) :=
      Set.range (fun a : X ↦ Metric.ball a (ε / 2))
    have hopen : ∀ W, W ∈ cover → IsOpen W := by
      intro W hW
      rcases hW with ⟨a, rfl⟩
      exact Metric.isOpen_ball
    have hcover : Set.univ ⊆ Set.sUnion cover := by
      intro x _hx
      apply Set.mem_sUnion_of_mem (Metric.mem_ball_self (half_pos hε))
      exact ⟨x, rfl⟩
    obtain ⟨φ, hφ, hfib⟩ := harc cover hopen hcover
    have himgcompact : IsCompact (φ '' (Set.univ : Set X)) :=
      isCompact_univ.image hφ
    have himgne : (φ '' (Set.univ : Set X)).Nonempty :=
      Set.univ_nonempty.image φ
    obtain ⟨ymin, hymin⟩ := himgcompact.exists_isLeast himgne
    obtain ⟨ymax, hymax⟩ := himgcompact.exists_isGreatest himgne
    rcases hymin.1 with ⟨xmin, hxminU, hxminφ⟩
    rcases hymax.1 with ⟨xmax, hxmaxU, hxmaxφ⟩
    let ψ : X → ℝ := fun x ↦ (φ (V x)).1 - (φ x).1
    have hψcont : Continuous ψ :=
      (continuous_subtype_val.comp (hφ.comp V.continuous)).sub
        (continuous_subtype_val.comp hφ)
    have hminsign : 0 ≤ ψ xmin := by
      apply sub_nonneg.mpr
      rw [hxminφ]
      exact Subtype.coe_le_coe.mpr
        (hymin.2 ⟨V xmin, Set.mem_univ _, rfl⟩)
    have hmaxsign : ψ xmax ≤ 0 := by
      apply sub_nonpos.mpr
      rw [hxmaxφ]
      exact Subtype.coe_le_coe.mpr
        (hymax.2 ⟨V xmax, Set.mem_univ _, rfl⟩)
    have hiv :=
      isConnected_univ.isPreconnected.intermediate_value
        hxmaxU hxminU hψcont.continuousOn
    have hzeroimg : (0 : ℝ) ∈ ψ '' (Set.univ : Set X) :=
      hiv ⟨hmaxsign, hminsign⟩
    rcases hzeroimg with ⟨z, _hzU, hψz⟩
    have hφeq : φ (V z) = φ z := by
      apply Subtype.ext
      exact sub_eq_zero.mp hψz
    obtain ⟨W, hW, hWfiber⟩ := hfib (φ z)
    rcases hW with ⟨a, rfl⟩
    have hzball : z ∈ Metric.ball a (ε / 2) := hWfiber (by simp)
    have hVzball : V z ∈ Metric.ball a (ε / 2) :=
      hWfiber (by simp [hφeq])
    refine ⟨z, ?_⟩
    calc
      dist (V z) z ≤ dist (V z) a + dist a z := dist_triangle _ _ _
      _ = dist (V z) a + dist z a := by rw [dist_comm a z]
      _ < ε / 2 + ε / 2 :=
        add_lt_add (Metric.mem_ball.mp hVzball) (Metric.mem_ball.mp hzball)
      _ = ε := add_halves ε
  let disp : X → ℝ := fun x ↦ dist (V x) x
  have hdispcont : Continuous disp := V.continuous.dist continuous_id
  obtain ⟨z, _hzU, hzmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hdispcont.continuousOn
  have hdispzero : disp z = 0 := by
    have hnonpos : disp z ≤ 0 := by
      by_contra hnot
      have hpos : 0 < disp z := lt_of_not_ge hnot
      obtain ⟨w, hwlt⟩ := happ (disp z) hpos
      exact (not_lt_of_ge (hzmin (Set.mem_univ w))) hwlt
    exact le_antisymm hnonpos dist_nonneg
  refine ⟨z, ?_⟩
  change dist (V z) z = 0 at hdispzero
  exact dist_eq_zero.mp hdispzero

/-- Arc-likeness passes to nonempty compact subcontinua.  Only compactness
and nonemptiness are needed for the cover-extension argument; preconnectedness
is recorded at call sites when the subtype is used as a continuum. -/
private theorem isArcLike_compact_subtype
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (harc : IsArcLike X) {K : Set X} (hKcompact : IsCompact K)
    (hKne : K.Nonempty) : IsArcLike K := by
  classical
  intro 𝒰 hopen hcover
  have hcoverne : 𝒰.Nonempty := by
    obtain ⟨x, hxK⟩ := hKne
    have hxU : (⟨x, hxK⟩ : K) ∈ ⋃₀ 𝒰 := hcover (Set.mem_univ _)
    rw [Set.mem_sUnion] at hxU
    rcases hxU with ⟨U, hU, _hxU⟩
    exact ⟨U, hU⟩
  choose ambient hambientOpen hambientEq using fun U : 𝒰 ↦
    IsOpen.image_val (hopen U.1 U.2)
  let coverX : Set (Set X) :=
    Set.range (fun U : 𝒰 ↦ ambient U) ∪ {Kᶜ}
  have hcoverXopen : ∀ W ∈ coverX, IsOpen W := by
    intro W hW
    change W ∈ Set.range (fun U : 𝒰 ↦ ambient U) ∨ W ∈ {Kᶜ} at hW
    rcases hW with ⟨U, rfl⟩ | hW
    · exact hambientOpen U
    · simp only [Set.mem_singleton_iff] at hW
      subst W
      exact hKcompact.isClosed.isOpen_compl
  have hcoverX : Set.univ ⊆ ⋃₀ coverX := by
    intro x _hx
    by_cases hxK : x ∈ K
    · have hxU : (⟨x, hxK⟩ : K) ∈ ⋃₀ 𝒰 :=
        hcover (Set.mem_univ _)
      rw [Set.mem_sUnion] at hxU
      obtain ⟨U, hUcover, hxU⟩ := hxU
      let Us : 𝒰 := ⟨U, hUcover⟩
      have hximage : x ∈ Subtype.val '' U := ⟨⟨x, hxK⟩, hxU, rfl⟩
      have hxambient : x ∈ ambient Us := by
        rw [hambientEq Us] at hximage
        exact hximage.1
      exact Set.mem_sUnion_of_mem hxambient
        (Or.inl ⟨Us, rfl⟩)
    · exact Set.mem_sUnion_of_mem hxK
        (Or.inr (Set.mem_singleton Kᶜ))
  obtain ⟨f, hfcont, hfiber⟩ :=
    harc coverX hcoverXopen hcoverX
  refine ⟨fun x : K ↦ f x.1, hfcont.comp continuous_subtype_val, ?_⟩
  intro y
  obtain ⟨W, hWcover, hWfiber⟩ := hfiber y
  change W ∈ Set.range (fun U : 𝒰 ↦ ambient U) ∨ W ∈ {Kᶜ} at hWcover
  rcases hWcover with ⟨U, rfl⟩ | hWcompl
  · refine ⟨U.1, U.2, ?_⟩
    intro x hx
    have hxambient : x.1 ∈ ambient U := hWfiber hx
    have hximage : x.1 ∈ Subtype.val '' U.1 := by
      rw [hambientEq U]
      exact ⟨hxambient, x.2⟩
    rcases hximage with ⟨z, hzU, hzx⟩
    have hzx' : z = x := Subtype.ext hzx
    simpa only [hzx'] using hzU
  · obtain ⟨U, hU⟩ := hcoverne
    simp only [Set.mem_singleton_iff] at hWcompl
    subst W
    refine ⟨U, hU, ?_⟩
    intro x hx
    have hxcompl : x.1 ∈ Kᶜ := hWfiber hx
    exact False.elim (hxcompl x.2)

/-- Reduction of the finite-order fixed-continuum theorem to its prime-order
case.  At a prime divisor `p` of the period, first take the fixed continuum
of `V^(d/p)`, then restrict `V` to it and recurse on the smaller period. -/
private theorem finitePeriodicHomeomorph_fixedSet_preconnected
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) {d : ℕ} (hd : 0 < d)
    (hperiodic : V ^ d = 1) :
    IsPreconnected {x : X | V x = x} := by
  by_cases hd1 : d = 1
  · subst d
    have hV : V = 1 := by simpa using hperiodic
    simpa [hV] using (isPreconnected_univ : IsPreconnected (Set.univ : Set X))
  · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    let q := d / p
    have hqp : q * p = d := Nat.div_mul_cancel hpd
    have hqpos : 0 < q := Nat.div_pos (Nat.le_of_dvd hd hpd) hp.pos
    have hqlt : q < d := Nat.div_lt_self hd hp.one_lt
    let W : X ≃ₜ X := V ^ q
    have hWperiodic : W ^ p = 1 := by
      dsimp [W]
      rw [← pow_mul, hqp, hperiodic]
    let F : Set X := {x | W x = x}
    have hFpre : IsPreconnected F := by
      simpa [F] using
        primePeriodicHomeomorph_fixedSet_preconnected_of_arcLike
          hconnected harc W hp hWperiodic
    have hFne : F.Nonempty := by
      simpa [F] using homeomorph_fixedSet_nonempty_of_arcLike hconnected harc W
    have hFclosed : IsClosed F := by
      dsimp [F]
      exact isClosed_eq W.continuous continuous_id
    have hFcompact : IsCompact F := hFclosed.isCompact
    have hWV : _root_.Commute W V := by
      dsimp [W]
      exact (_root_.Commute.refl V).pow_left q
    have hWVfun : Function.Commute W V := by
      intro x
      simpa only [Homeomorph.mul_apply] using
        congrArg (fun H : X ≃ₜ X ↦ H x) hWV.eq
    have hVpreserves : ∀ x : X, x ∈ F ↔ V x ∈ F := by
      intro x
      change W x = x ↔ W (V x) = V x
      constructor
      · intro hx
        rw [hWVfun x, hx]
      · intro hx
        apply V.injective
        calc
          V (W x) = W (V x) := (hWVfun x).symm
          _ = V x := hx
    let VF : F ≃ₜ F := V.subtype hVpreserves
    have hVFperiodic : VF ^ q = 1 := by
      have hval : ∀ n : ℕ, ∀ x : F,
          ((VF ^ n) x).1 = (V ^ n) x.1 := by
        intro n
        induction n with
        | zero => intro x; simp
        | succ n ih =>
            intro x
            rw [pow_succ, Homeomorph.mul_apply]
            rw [ih]
            change (V ^ n) (V x.1) = (V ^ (n + 1)) x.1
            rw [pow_succ, Homeomorph.mul_apply]
      apply Homeomorph.ext
      intro x
      apply Subtype.ext
      rw [hval]
      exact x.2
    letI : CompactSpace F := isCompact_iff_compactSpace.mp hFcompact
    letI : ConnectedSpace F := Subtype.connectedSpace ⟨hFne, hFpre⟩
    have hFarc : IsArcLike F :=
      isArcLike_compact_subtype harc hFcompact hFne
    have hrec : IsPreconnected {x : F | VF x = x} :=
      finitePeriodicHomeomorph_fixedSet_preconnected
        (X := F) (by infer_instance) hFarc VF hqpos hVFperiodic
    have himage : IsPreconnected
        (Subtype.val '' {x : F | VF x = x} : Set X) :=
      hrec.image _ continuous_subtype_val.continuousOn
    have heq : (Subtype.val '' {x : F | VF x = x} : Set X) =
        {x : X | V x = x} := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact congrArg Subtype.val hz
      · intro hx
        have hxF : x ∈ F := by
          change W x = x
          dsimp [W]
          induction q with
          | zero => simp
          | succ n ih =>
              rw [pow_succ, Homeomorph.mul_apply, hx, ih]
        let z : F := ⟨x, hxF⟩
        refine ⟨z, ?_, rfl⟩
        apply Subtype.ext
        exact hx
    rwa [heq] at himage
  termination_by d
  decreasing_by exact hqlt

/-- The exact connectedness boundary in Fugate--McLean's theorem. -/
theorem fugateMcLean_periodicHomeomorph_fixedSet_preconnected_of_arcLike
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) {d : ℕ} (hd : 0 < d)
    (hperiodic : V^[d] = Homeomorph.refl X) :
    IsPreconnected {x : X | V x = x} := by
  have hiterate : ∀ n : ℕ, ∀ x : X,
      (V : X → X)^[n] x = (V ^ n) x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [Function.iterate_succ_apply, pow_succ, Homeomorph.mul_apply]
        exact ih (V x)
  have hpow : V ^ d = 1 := by
    apply Homeomorph.ext
    intro x
    rw [← hiterate d x]
    simpa using congrFun hperiodic x
  exact finitePeriodicHomeomorph_fixedSet_preconnected
    hconnected harc V hd hpow

theorem fugateMcLean_periodicHomeomorph_fixedSet_nonempty_connected_of_arcLike
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) {d : ℕ} (hd : 0 < d)
    (hperiodic : V^[d] = Homeomorph.refl X) :
    {x : X | V x = x}.Nonempty ∧
      IsConnected {x : X | V x = x} := by
  have hne := homeomorph_fixedSet_nonempty_of_arcLike hconnected harc V
  have hpre :=
    fugateMcLean_periodicHomeomorph_fixedSet_preconnected_of_arcLike
      hconnected harc V hd hperiodic
  exact ⟨hne, hne, hpre⟩

/--
Fugate--McLean, specialized to the only form used in the manuscript: the
fixed set of a periodic homeomorphism of a nonempty compact connected
arc-like metric space is a nonempty connected compactum.
-/
theorem periodicHomeomorph_fixedSet_preconnected_of_arcLike
    {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) {d : ℕ} (hd : 0 < d)
    (hperiodic : V^[d] = Homeomorph.refl X) :
    IsPreconnected {x : X | V x = x} := by
  exact
    (fugateMcLean_periodicHomeomorph_fixedSet_nonempty_connected_of_arcLike
      hconnected harc V hd hperiodic).2.isPreconnected

theorem periodicHomeomorph_fixedSet_nonempty_connected_of_arcLike
    {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) {d : ℕ} (hd : 0 < d)
    (hperiodic : V^[d] = Homeomorph.refl X) :
    {x : X | V x = x}.Nonempty ∧
      IsConnected {x : X | V x = x} := by
  letI : ConnectedSpace X := hconnected
  have happ : ∀ ε : ℝ, 0 < ε → ∃ z, dist (V z) z < ε := by
    intro ε hε
    let cover : Set (Set X) :=
      Set.range (fun a : X => Metric.ball a (ε / 2))
    have hopen : ∀ W, W ∈ cover → IsOpen W := by
      intro W hW
      rcases hW with ⟨a, rfl⟩
      exact Metric.isOpen_ball
    have hcover : Set.univ ⊆ Set.sUnion cover := by
      intro x _hx
      apply Set.mem_sUnion_of_mem (Metric.mem_ball_self (half_pos hε))
      exact ⟨x, rfl⟩
    obtain ⟨φ, hφ, hfib⟩ := harc cover hopen hcover
    have himgcompact : IsCompact (φ '' (Set.univ : Set X)) :=
      isCompact_univ.image hφ
    have himgne : (φ '' (Set.univ : Set X)).Nonempty :=
      Set.univ_nonempty.image φ
    obtain ⟨ymin, hymin⟩ := himgcompact.exists_isLeast himgne
    obtain ⟨ymax, hymax⟩ := himgcompact.exists_isGreatest himgne
    rcases hymin.1 with ⟨xmin, hxminU, hxminφ⟩
    rcases hymax.1 with ⟨xmax, hxmaxU, hxmaxφ⟩
    let ψ : X → ℝ := fun x => (φ (V x)).1 - (φ x).1
    have hψcont : Continuous ψ :=
      (continuous_subtype_val.comp (hφ.comp V.continuous)).sub
        (continuous_subtype_val.comp hφ)
    have hminsign : 0 ≤ ψ xmin := by
      apply sub_nonneg.mpr
      rw [hxminφ]
      exact Subtype.coe_le_coe.mpr
        (hymin.2 ⟨V xmin, Set.mem_univ _, rfl⟩)
    have hmaxsign : ψ xmax ≤ 0 := by
      apply sub_nonpos.mpr
      rw [hxmaxφ]
      exact Subtype.coe_le_coe.mpr
        (hymax.2 ⟨V xmax, Set.mem_univ _, rfl⟩)
    have hiv :=
      isConnected_univ.isPreconnected.intermediate_value
        hxmaxU hxminU hψcont.continuousOn
    have hzeroimg : (0 : ℝ) ∈ ψ '' (Set.univ : Set X) :=
      hiv ⟨hmaxsign, hminsign⟩
    rcases hzeroimg with ⟨z, _hzU, hψz⟩
    have hφeq : φ (V z) = φ z := by
      apply Subtype.ext
      exact sub_eq_zero.mp hψz
    obtain ⟨W, hW, hWfiber⟩ := hfib (φ z)
    rcases hW with ⟨a, rfl⟩
    have hzball : z ∈ Metric.ball a (ε / 2) := hWfiber (by simp)
    have hVzball : V z ∈ Metric.ball a (ε / 2) :=
      hWfiber (by simp [hφeq])
    refine ⟨z, ?_⟩
    calc
      dist (V z) z ≤ dist (V z) a + dist a z := dist_triangle _ _ _
      _ = dist (V z) a + dist z a := by rw [dist_comm a z]
      _ < ε / 2 + ε / 2 :=
        add_lt_add (Metric.mem_ball.mp hVzball) (Metric.mem_ball.mp hzball)
      _ = ε := add_halves ε
  let disp : X → ℝ := fun x => dist (V x) x
  have hdispcont : Continuous disp := V.continuous.dist continuous_id
  obtain ⟨z, _hzU, hzmin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hdispcont.continuousOn
  have hdispzero : disp z = 0 := by
    have hnonpos : disp z ≤ 0 := by
      by_contra hnot
      have hpos : 0 < disp z := lt_of_not_ge hnot
      obtain ⟨w, hwlt⟩ := happ (disp z) hpos
      exact (not_lt_of_ge (hzmin (Set.mem_univ w))) hwlt
    exact le_antisymm hnonpos dist_nonneg
  have hfixne : {x : X | V x = x}.Nonempty := by
    refine ⟨z, ?_⟩
    change dist (V z) z = 0 at hdispzero
    exact dist_eq_zero.mp hdispzero
  have hfixpre : IsPreconnected {x : X | V x = x} :=
    periodicHomeomorph_fixedSet_preconnected_of_arcLike
      hconnected harc V hd hperiodic
  exact ⟨hfixne, hfixne, hfixpre⟩

/-- The Bézout/Fugate--McLean consequence used after passing to a natural
extension: commuting homeomorphisms with equal positive powers have a common
fixed point on a compact connected arc-like space. -/
theorem commutingHomeomorphisms_commonFixed_of_equalPositivePowers
    {X : Type*} [MetricSpace X]
    (hnonempty : Nonempty X)
    (hcompact : IsCompact (Set.univ : Set X))
    (hconnected : IsConnected (Set.univ : Set X))
    (harc : IsArcLike X)
    (F G : X ≃ₜ X) (hcomm : Function.Commute F G)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hpowers : F^[m] = G^[n]) :
    ∃ x : X, F x = x ∧ G x = x := by
  letI : Nonempty X := hnonempty
  letI : CompactSpace X := { isCompact_univ := hcompact }
  have hconnSpace : ConnectedSpace X :=
    connectedSpace_iff_univ.mpr hconnected
  have hFG : _root_.Commute F G := by
    apply Homeomorph.ext
    intro x
    exact hcomm x
  have hiterate (H : X ≃ₜ X) :
      ∀ k x, (H : X → X)^[k] x = (H ^ k) x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply, pow_succ, Homeomorph.mul_apply]
        exact ih (H x)
  have hpowers' : F ^ m = G ^ n := by
    apply Homeomorph.ext
    intro x
    rw [← hiterate F m x, ← hiterate G n x]
    exact congrFun hpowers x

  let d := Nat.gcd m n
  let m0 := m / d
  let n0 := n / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left n hm
  have hdm : m0 * d = m :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left m n)
  have hdn : n0 * d = n :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right m n)
  have hcop : Nat.Coprime m0 n0 :=
    Nat.coprime_div_gcd_div_gcd hd
  let r : ℤ := Nat.gcdB m0 n0
  let s : ℤ := Nat.gcdA m0 n0
  have hrs : r * (n0 : ℤ) + s * (m0 : ℤ) = 1 := by
    have hb := Nat.gcd_eq_gcd_ab m0 n0
    rw [hcop.gcd_eq_one] at hb
    dsimp [r, s]
    calc
      Nat.gcdB m0 n0 * (n0 : ℤ) + Nat.gcdA m0 n0 * (m0 : ℤ) =
          (m0 : ℤ) * Nat.gcdA m0 n0 +
            (n0 : ℤ) * Nat.gcdB m0 n0 := by ring
      _ = 1 := by simpa using hb.symm

  let U : X ≃ₜ X := F ^ r * G ^ s
  let V : X ≃ₜ X := F ^ (m0 : ℤ) * G ^ (-(n0 : ℤ))
  have hVpow : V ^ d = 1 := by
    dsimp [V]
    rw [(hFG.zpow_zpow (m0 : ℤ) (-(n0 : ℤ))).mul_pow]
    rw [← zpow_natCast (F ^ (m0 : ℤ)) d,
      ← zpow_mul F (m0 : ℤ) d]
    rw [← zpow_natCast (G ^ (-(n0 : ℤ))) d,
      ← zpow_mul G (-(n0 : ℤ)) d]
    have hdmi : (m0 : ℤ) * (d : ℤ) = m := by exact_mod_cast hdm
    have hdni : (n0 : ℤ) * (d : ℤ) = n := by exact_mod_cast hdn
    rw [hdmi]
    rw [neg_mul, hdni]
    simpa [hpowers']
  have hVperiodic : (V : X → X)^[d] = Homeomorph.refl X := by
    funext x
    rw [hiterate V d x, hVpow]
    simp

  let C : Set X := {x | V x = x}
  have hCpkg :=
    periodicHomeomorph_fixedSet_nonempty_connected_of_arcLike
      hconnSpace harc V hd hVperiodic
  have hCne : C.Nonempty := by
    simpa [C] using hCpkg.1
  have hCconn : IsConnected C := by
    simpa [C] using hCpkg.2
  have hCclosed : IsClosed C := by
    dsimp [C]
    exact isClosed_eq V.continuous continuous_id
  have hCcompact : IsCompact C := hCclosed.isCompact

  have hUV : _root_.Commute U V := by
    dsimp [U, V]
    exact
      (((_root_.Commute.refl F).zpow_zpow r (m0 : ℤ)).mul_right
        (hFG.zpow_zpow r (-(n0 : ℤ)))).mul_left
      ((hFG.symm.zpow_zpow s (m0 : ℤ)).mul_right
        ((_root_.Commute.refl G).zpow_zpow s (-(n0 : ℤ))))
  have hUVfun : Function.Commute U V := by
    intro x
    simpa only [Homeomorph.mul_apply] using
      congrArg (fun W : X ≃ₜ X => W x) hUV.eq
  have hUmaps : MapsTo U C C := by
    intro x hx
    change V (U x) = U x
    rw [← hUVfun x, hx]

  have happ : ∀ ε : ℝ, 0 < ε →
      ∃ z, C z ∧ dist (U z) z < ε := by
    intro ε hε
    let cover : Set (Set X) :=
      Set.range (fun a : X => Metric.ball a (ε / 2))
    have hopen : ∀ W, cover W → IsOpen W := by
      intro W hW
      rcases hW with ⟨a, rfl⟩
      exact Metric.isOpen_ball
    have hcover : Set.univ ⊆ Set.sUnion cover := by
      intro x _
      apply Set.mem_sUnion_of_mem (Metric.mem_ball_self (half_pos hε))
      exact ⟨x, rfl⟩
    obtain ⟨φ, hφ, hfib⟩ := harc cover hopen hcover
    have himgcompact : IsCompact (φ '' C) := hCcompact.image hφ
    have himgne : (φ '' C).Nonempty := hCne.image φ
    obtain ⟨ymin, hymin⟩ := himgcompact.exists_isLeast himgne
    obtain ⟨ymax, hymax⟩ := himgcompact.exists_isGreatest himgne
    rcases hymin.1 with ⟨xmin, hxminC, hxminφ⟩
    rcases hymax.1 with ⟨xmax, hxmaxC, hxmaxφ⟩
    let ψ : X → ℝ := fun x => (φ (U x)).1 - (φ x).1
    have hψcont : Continuous ψ :=
      (continuous_subtype_val.comp (hφ.comp U.continuous)).sub
        (continuous_subtype_val.comp hφ)
    have hminsign : 0 ≤ ψ xmin := by
      apply sub_nonneg.mpr
      rw [hxminφ]
      exact Subtype.coe_le_coe.mpr
        (hymin.2 ⟨U xmin, hUmaps hxminC, rfl⟩)
    have hmaxsign : ψ xmax ≤ 0 := by
      apply sub_nonpos.mpr
      rw [hxmaxφ]
      exact Subtype.coe_le_coe.mpr
        (hymax.2 ⟨U xmax, hUmaps hxmaxC, rfl⟩)
    have hiv :=
      hCconn.isPreconnected.intermediate_value
        hxmaxC hxminC hψcont.continuousOn
    have hzeroimg : (0 : ℝ) ∈ ψ '' C :=
      hiv ⟨hmaxsign, hminsign⟩
    rcases hzeroimg with ⟨z, hzC, hψz⟩
    have hφeq : φ (U z) = φ z := by
      apply Subtype.ext
      exact sub_eq_zero.mp hψz
    obtain ⟨W, hW, hWfiber⟩ := hfib (φ z)
    rcases hW with ⟨a, rfl⟩
    have hzball : z ∈ Metric.ball a (ε / 2) := hWfiber (by simp)
    have hUzball : U z ∈ Metric.ball a (ε / 2) :=
      hWfiber (by simp [hφeq])
    refine ⟨z, hzC, ?_⟩
    calc
      dist (U z) z ≤ dist (U z) a + dist a z := dist_triangle _ _ _
      _ = dist (U z) a + dist z a := by rw [dist_comm a z]
      _ < ε / 2 + ε / 2 :=
        add_lt_add (Metric.mem_ball.mp hUzball) (Metric.mem_ball.mp hzball)
      _ = ε := add_halves ε

  let disp : X → ℝ := fun x => dist (U x) x
  have hdispcont : Continuous disp := U.continuous.dist continuous_id
  obtain ⟨z, hzC, hzmin⟩ :=
    hCcompact.exists_isMinOn hCne hdispcont.continuousOn
  have hdispzero : disp z = 0 := by
    have hnonpos : disp z ≤ 0 := by
      by_contra hnot
      have hpos : 0 < disp z := lt_of_not_ge hnot
      obtain ⟨w, hwC, hwlt⟩ := happ (disp z) hpos
      exact (not_lt_of_ge (hzmin hwC)) hwlt
    exact le_antisymm hnonpos dist_nonneg
  have hzU : U z = z := by
    change dist (U z) z = 0 at hdispzero
    exact dist_eq_zero.mp hdispzero
  have hzV : V z = z := hzC

  have hFsplit : F = U ^ n0 * V ^ s := by
    dsimp [U, V]
    rw [(hFG.zpow_zpow r s).mul_pow]
    rw [(hFG.zpow_zpow (m0 : ℤ) (-(n0 : ℤ))).mul_zpow]
    rw [← zpow_natCast (F ^ r) n0, ← zpow_mul F r n0]
    rw [← zpow_natCast (G ^ s) n0, ← zpow_mul G s n0]
    rw [← zpow_mul F (m0 : ℤ) s]
    rw [← zpow_mul G (-(n0 : ℤ)) s]
    rw [((hFG.zpow_zpow ((m0 : ℤ) * s) (s * n0)).symm).mul_mul_mul_comm]
    rw [← zpow_add F (r * n0) (m0 * s)]
    rw [← zpow_add G (s * n0) (-(n0 : ℤ) * s)]
    rw [mul_comm (m0 : ℤ) s, hrs]
    simp only [neg_mul, mul_comm (n0 : ℤ) s, add_neg_cancel,
      zpow_zero, zpow_one, mul_one]
  have hGsplit : G = U ^ m0 * V ^ (-r) := by
    dsimp [U, V]
    rw [(hFG.zpow_zpow r s).mul_pow]
    rw [(hFG.zpow_zpow (m0 : ℤ) (-(n0 : ℤ))).mul_zpow]
    rw [← zpow_natCast (F ^ r) m0, ← zpow_mul F r m0]
    rw [← zpow_natCast (G ^ s) m0, ← zpow_mul G s m0]
    rw [← zpow_mul F (m0 : ℤ) (-r)]
    rw [← zpow_mul G (-(n0 : ℤ)) (-r)]
    rw [((hFG.zpow_zpow ((m0 : ℤ) * (-r)) (s * m0)).symm).mul_mul_mul_comm]
    rw [← zpow_add F (r * m0) (m0 * (-r))]
    rw [← zpow_add G (s * m0) (-(n0 : ℤ) * (-r))]
    have hrs' : s * (m0 : ℤ) + (n0 : ℤ) * r = 1 := by
      calc
        s * (m0 : ℤ) + (n0 : ℤ) * r =
            r * (n0 : ℤ) + s * (m0 : ℤ) := by ring
        _ = 1 := hrs
    simp only [neg_mul, mul_neg, neg_neg]
    rw [hrs']
    simp only [mul_comm r (m0 : ℤ), add_neg_cancel, zpow_zero,
      zpow_one, one_mul]

  have hfixedNat (H : X ≃ₜ X) (hz : H z = z) :
      ∀ q : ℕ, (H ^ q) z = z := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [pow_succ, Homeomorph.mul_apply, hz, ih]
  have hfixedInt (H : X ≃ₜ X) (hz : H z = z) :
      ∀ q : ℤ, (H ^ q) z = z := by
    intro q
    cases q with
    | ofNat k => exact hfixedNat H hz k
    | negSucc k =>
        have hsymm : H.symm z = z := by
          calc
            H.symm z = H.symm (H z) := congrArg H.symm hz.symm
            _ = z := H.left_inv z
        rw [zpow_negSucc, ← inv_pow]
        exact hfixedNat H.symm hsymm (k + 1)
  refine ⟨z, ?_, ?_⟩
  · calc
      F z = (U ^ n0 * V ^ s) z :=
        congrArg (fun W : X ≃ₜ X => W z) hFsplit
      _ = (U ^ n0) ((V ^ s) z) := Homeomorph.mul_apply _ _ _
      _ = z := by rw [hfixedInt V hzV, hfixedNat U hzU]
  · calc
      G z = (U ^ m0 * V ^ (-r)) z :=
        congrArg (fun W : X ≃ₜ X => W z) hGsplit
      _ = (U ^ m0) ((V ^ (-r)) z) := Homeomorph.mul_apply _ _ _
      _ = z := by rw [hfixedInt V hzV, hfixedNat U hzU]

/-- If commuting maps have the same positive iterate, their coordinatewise
lifts to the natural extension of that iterate are commuting homeomorphisms
whose corresponding powers equal the shift. -/
theorem naturalExtension_lift_package
    {F G : IntervalMap} (hF : Continuous F) (hG : Continuous G)
    (hcomm : Function.Commute F G) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hpowers : iterateMap F m = iterateMap G n) :
    ∃ Fhat Ghat Sigma : NaturalExtension (iterateMap F m) ≃ₜ
        NaturalExtension (iterateMap F m),
      Function.Commute Fhat Ghat ∧
        Fhat^[m] = Sigma ∧ Ghat^[n] = Sigma ∧
        (∀ x i, (Fhat x).1 i = F (x.1 i)) ∧
        (∀ x i, (Ghat x).1 i = G (x.1 i)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  subst m
  subst n
  let H : IntervalMap := iterateMap F (k + 1)
  have hrootF : iterateMap F (k + 1) = H := rfl
  have hrootG : iterateMap G (l + 1) = H := hpowers.symm
  have hH : Continuous H := IntervalMap.continuous_iterate hF (k + 1)
  have hrootH : iterateMap H (0 + 1) = H := by
    simp [iterateMap]
  let Fhat : NaturalExtension H ≃ₜ NaturalExtension H :=
    NaturalExtension.rootHomeomorph H F k hF hrootF
  let Ghat : NaturalExtension H ≃ₜ NaturalExtension H :=
    NaturalExtension.rootHomeomorph H G l hG hrootG
  let Sigma : NaturalExtension H ≃ₜ NaturalExtension H :=
    NaturalExtension.rootHomeomorph H H 0 hH hrootH
  have hFG : Function.Commute Fhat Ghat := by
    intro x
    apply Subtype.ext
    funext i
    change F (G (x.1 i)) = G (F (x.1 i))
    exact hcomm (x.1 i)
  have hFpower : (Fhat : NaturalExtension H → NaturalExtension H)^[k + 1] = Sigma := by
    funext x
    apply Subtype.ext
    funext i
    rw [NaturalExtension.rootHomeomorph_iterate_coord H F k hF hrootF]
    change iterateMap F (k + 1) (x.1 i) = H (x.1 i)
    exact congrFun hrootF (x.1 i)
  have hGpower : (Ghat : NaturalExtension H → NaturalExtension H)^[l + 1] = Sigma := by
    funext x
    apply Subtype.ext
    funext i
    rw [NaturalExtension.rootHomeomorph_iterate_coord H G l hG hrootG]
    change iterateMap G (l + 1) (x.1 i) = H (x.1 i)
    exact congrFun hrootG (x.1 i)
  exact ⟨Fhat, Ghat, Sigma, hFG, hFpower, hGpower,
    fun _ _ => rfl, fun _ _ => rfl⟩

/--
Commuting continuous interval maps with a common positive iterate have a
common fixed point.
-/
theorem common_positive_iterate
    {F G : IntervalMap} (hF : Continuous F) (hG : Continuous G)
    (hcomm : Function.Commute F G) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hpowers : iterateMap F m = iterateMap G n) :
    HasCommonFixedPoint F G := by
  let T := iterateMap F m
  letI : TopologicalSpace.MetrizableSpace (NaturalExtension T) := by
    exact Topology.IsEmbedding.subtypeVal.metrizableSpace
  let _ : MetricSpace (NaturalExtension T) :=
    TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨Fhat, Ghat, Sigma, hhatcomm, hFpower, hGpower,
      hFcoord, hGcoord⟩ :=
    naturalExtension_lift_package hF hG hcomm hm hn hpowers
  have hX := naturalExtension_isArcLike
    (T := T) (IntervalMap.continuous_iterate hF m)
  have hhatpowers : Fhat^[m] = Ghat^[n] := hFpower.trans hGpower.symm
  obtain ⟨z, hzF, hzG⟩ :=
    commutingHomeomorphisms_commonFixed_of_equalPositivePowers
      hX.1 hX.2.1 hX.2.2.1 hX.2.2.2 Fhat Ghat hhatcomm hm hn hhatpowers
  refine ⟨z.1 0, ?_, ?_⟩
  · change F (z.1 0) = z.1 0
    rw [← hFcoord z 0]
    exact congrArg (fun w : NaturalExtension T => w.1 0) hzF
  · change G (z.1 0) = z.1 0
    rw [← hGcoord z 0]
    exact congrArg (fun w : NaturalExtension T => w.1 0) hzG

end CommutingIntervalSimplified
