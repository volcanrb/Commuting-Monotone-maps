import CommutingInterval.Basic
import CommutingInterval.DynamicsDefs
import CommutingInterval.QuotientDefs
import CommutingInterval.PiecewiseLinearQuotientSupport
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Finite-arrival support for the piecewise-linear core

This file contains only the topological, finite-graph, and elementary
piecewise-affine ingredients of the finite-arrival argument.  The
least-counterexample layer supplies the two contradiction
interfaces (minimal invariant cores and strict fixed-count descent) when this
module is instantiated in `PiecewiseLinearCore`.
-/

noncomputable section

namespace CommutingInterval

open Filter Function Set Topology

namespace PLFiniteArrivalSupport

/-! ## Closed interval images and diagonal iterates -/

/-- A closed interval with named endpoints. -/
def gapInterval (p c : I) (hpc : p ≤ c) : ClosedSubinterval where
  left := p
  right := c
  left_le_right := hpc

/-- The image of a closed subinterval under an interval map. -/
def imageInterval (T : IntervalMap) (J : ClosedSubinterval) : Set I :=
  T '' J.carrier

/-- The two-parameter image `A^i B^j(J)`. -/
def biIterateImage (A B : IntervalMap) (J : ClosedSubinterval)
    (i j : ℕ) : Set I :=
  iterateMap A i '' (iterateMap B j '' J.carrier)

/-- The diagonal image `A^n B^n(J)`. -/
def diagonalImage (A B : IntervalMap) (J : ClosedSubinterval)
    (n : ℕ) : Set I :=
  biIterateImage A B J n n

/-- The closure of the increasing diagonal range. -/
def diagonalRange (A B : IntervalMap) (J : ClosedSubinterval) : Set I :=
  closure (⋃ n : ℕ, diagonalImage A B J n)

/-- Continuity and fixed endpoints force a closed interval into its image. -/
theorem gap_subset_image_of_fixed_endpoints
    {T : IntervalMap} {p c : I} (hpc : p ≤ c)
    (hT : Continuous T) (hp : T p = p) (hc : T c = c) :
    Set.Icc p c ⊆ T '' Set.Icc p c := by
  intro x hx
  have hx' : x ∈ Set.Icc (T p) (T c) := by
    simpa [hp, hc] using hx
  exact intermediate_value_Icc hpc hT.continuousOn hx'

private theorem diagonalImage_eq_comp_iterate_image_aux
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hcomm : Commute A B) (n : ℕ) :
    diagonalImage A B J n = imageInterval (iterateMap (A ∘ B) n) J := by
  simp only [diagonalImage, biIterateImage, imageInterval, iterateMap]
  rw [Set.image_image, hcomm.comp_iterate n]
  rfl

/-- For commuting maps, a diagonal image is an iterate of the product. -/
theorem diagonalImage_eq_comp_iterate_image
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hcomm : Commute A B) (n : ℕ) :
    diagonalImage A B J n = imageInterval (iterateMap (A ∘ B) n) J :=
  diagonalImage_eq_comp_iterate_image_aux J hcomm n

/-- If the base interval expands under each factor, its diagonal images form
an increasing sequence. -/
theorem diagonalImage_monotone
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hcomm : Commute A B)
    (hA : J.carrier ⊆ imageInterval A J)
    (hB : J.carrier ⊆ imageInterval B J) :
    Monotone (fun n => diagonalImage A B J n) := by
  have hcomp : J.carrier ⊆ imageInterval (A ∘ B) J := by
    intro x hx
    obtain ⟨y, hy, hBy⟩ := hB hx
    obtain ⟨z, hz, hAz⟩ := hA hy
    refine ⟨z, hz, ?_⟩
    change A (B z) = x
    rw [hcomm.eq z, hAz, hBy]
  apply monotone_nat_of_le_succ
  intro n
  rw [diagonalImage_eq_comp_iterate_image_aux J hcomm n,
    diagonalImage_eq_comp_iterate_image_aux J hcomm (n + 1)]
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hcomp hy
  exact ⟨z, hz, rfl⟩

/-- Cofinality of the two indices makes the closed diagonal range invariant
under each generator. -/
theorem diagonalRange_invariant
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hAcont : Continuous A) (hBcont : Continuous B)
    (hcomm : Commute A B)
    (hA : J.carrier ⊆ imageInterval A J)
    (hB : J.carrier ⊆ imageInterval B J) :
    A '' diagonalRange A B J = diagonalRange A B J ∧
      B '' diagonalRange A B J = diagonalRange A B J := by
  let R : IntervalMap := A ∘ B
  let U : Set I := ⋃ n : ℕ, diagonalImage A B J n
  have hAR : Commute A R :=
    (Function.Commute.refl A).comp_right hcomm
  have hBR : Commute B R :=
    hcomm.symm.comp_right (Function.Commute.refl B)
  have hforwardA : A '' U ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨n, hyn⟩ := Set.mem_iUnion.mp hy
    rw [diagonalImage_eq_comp_iterate_image_aux J hcomm n] at hyn
    obtain ⟨z, hz, rfl⟩ := hyn
    obtain ⟨w, hw, hBw⟩ := hB hz
    apply Set.mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    rw [diagonalImage_eq_comp_iterate_image_aux J hcomm (n + 1)]
    refine ⟨w, hw, ?_⟩
    change R^[n + 1] w = A (R^[n] z)
    symm
    rw [(hAR.iterate_right n).eq, ← hBw]
    rfl
  have hbackwardA : U ⊆ A '' U := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    rw [diagonalImage_eq_comp_iterate_image_aux J hcomm n] at hxn
    obtain ⟨z, hz, rfl⟩ := hxn
    obtain ⟨w, hw, hAw⟩ := hA hz
    refine ⟨R^[n] w, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨n, by
        rw [diagonalImage_eq_comp_iterate_image_aux J hcomm n]
        exact ⟨w, hw, rfl⟩⟩
    · change A (R^[n] w) = R^[n] z
      rw [(hAR.iterate_right n).eq, hAw]
  have hforwardB : B '' U ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨n, hyn⟩ := Set.mem_iUnion.mp hy
    rw [diagonalImage_eq_comp_iterate_image_aux J hcomm n] at hyn
    obtain ⟨z, hz, rfl⟩ := hyn
    obtain ⟨w, hw, hAw⟩ := hA hz
    apply Set.mem_iUnion.mpr
    refine ⟨n + 1, ?_⟩
    rw [diagonalImage_eq_comp_iterate_image_aux J hcomm (n + 1)]
    refine ⟨w, hw, ?_⟩
    change R^[n + 1] w = B (R^[n] z)
    symm
    rw [(hBR.iterate_right n).eq, ← hAw]
    change R^[n] (B (A w)) = R^[n] (A (B w))
    rw [hcomm.eq]
  have hbackwardB : U ⊆ B '' U := by
    intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    rw [diagonalImage_eq_comp_iterate_image_aux J hcomm n] at hxn
    obtain ⟨z, hz, rfl⟩ := hxn
    obtain ⟨w, hw, hBw⟩ := hB hz
    refine ⟨R^[n] w, ?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨n, by
        rw [diagonalImage_eq_comp_iterate_image_aux J hcomm n]
        exact ⟨w, hw, rfl⟩⟩
    · change B (R^[n] w) = R^[n] z
      rw [(hBR.iterate_right n).eq, hBw]
  have hKcompact : IsCompact (closure U) := isClosed_closure.isCompact
  have hAimageClosed : IsClosed (A '' closure U) :=
    (hKcompact.image hAcont).isClosed
  have hBimageClosed : IsClosed (B '' closure U) :=
    (hKcompact.image hBcont).isClosed
  have hAeq : A '' closure U = closure U := by
    apply Set.Subset.antisymm
    · exact (image_closure_subset_closure_image hAcont).trans
        (closure_mono hforwardA)
    · apply closure_minimal
      exact hbackwardA.trans (Set.image_mono subset_closure)
      exact hAimageClosed
  have hBeq : B '' closure U = closure U := by
    apply Set.Subset.antisymm
    · exact (image_closure_subset_closure_image hBcont).trans
        (closure_mono hforwardB)
    · apply closure_minimal
      exact hbackwardB.trans (Set.image_mono subset_closure)
      exact hBimageClosed
  simpa only [diagonalRange, U] using ⟨hAeq, hBeq⟩

/-- Every diagonal image of a closed interval under continuous factors is
order-connected. -/
theorem diagonalImage_ordConnected
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hA : Continuous A) (hB : Continuous B)
    (hcomm : Commute A B) (n : ℕ) :
    Set.OrdConnected (diagonalImage A B J n) := by
  rw [diagonalImage_eq_comp_iterate_image J hcomm n]
  exact (Set.ordConnected_Icc.isPreconnected.image _
    (IntervalMap.continuous_iterate (hA.comp hB) n).continuousOn).ordConnected

/-- The closed diagonal range is a nonempty compact interval. -/
theorem diagonalRange_interval_package
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hA : Continuous A) (hB : Continuous B)
    (hcomm : Commute A B)
    (hexpandA : J.carrier ⊆ imageInterval A J)
    (hexpandB : J.carrier ⊆ imageInterval B J) :
    IsCompact (diagonalRange A B J) ∧
      Set.OrdConnected (diagonalRange A B J) ∧
      (diagonalRange A B J).Nonempty := by
  have hmono : Monotone (fun n => diagonalImage A B J n) :=
    diagonalImage_monotone J hcomm hexpandA hexpandB
  have hdiagConnected (n : ℕ) : IsConnected (diagonalImage A B J n) := by
    have hbase : IsConnected J.carrier := by
      simpa [ClosedSubinterval.carrier] using isConnected_Icc J.left_le_right
    have himage := hbase.image (iterateMap (A ∘ B) n)
      (IntervalMap.continuous_iterate (hA.comp hB) n).continuousOn
    rw [diagonalImage_eq_comp_iterate_image J hcomm n]
    simpa [imageInterval] using himage
  have hchain (n : ℕ) :
      (diagonalImage A B J n ∩ diagonalImage A B J (Order.succ n)).Nonempty := by
    obtain ⟨x, hx⟩ := (hdiagConnected n).1
    exact ⟨x, hx, hmono (Nat.le_succ n) hx⟩
  have hunionPre : IsPreconnected (⋃ n : ℕ, diagonalImage A B J n) :=
    IsPreconnected.iUnion_of_chain
      (fun n => (hdiagConnected n).2) hchain
  have hunionNonempty : (⋃ n : ℕ, diagonalImage A B J n).Nonempty := by
    obtain ⟨x, hx⟩ := (hdiagConnected 0).1
    exact ⟨x, Set.mem_iUnion.mpr ⟨0, hx⟩⟩
  have hcompact : IsCompact (diagonalRange A B J) := by
    simpa [diagonalRange] using
      (isClosed_closure.isCompact :
        IsCompact (closure (⋃ n : ℕ, diagonalImage A B J n)))
  have hpre : IsPreconnected (diagonalRange A B J) := by
    simpa [diagonalRange] using hunionPre.closure
  have hnonempty : (diagonalRange A B J).Nonempty := by
    simpa [diagonalRange] using hunionNonempty.mono subset_closure
  exact ⟨hcompact, isPreconnected_iff_ordConnected.mp hpre, hnonempty⟩

/-- Applying a further product iterate shifts the diagonal index. -/
theorem iterate_product_image_diagonalImage
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hcomm : Commute A B) (k n : ℕ) :
    iterateMap (A ∘ B) k '' diagonalImage A B J n =
      diagonalImage A B J (k + n) := by
  rw [diagonalImage_eq_comp_iterate_image J hcomm n,
    diagonalImage_eq_comp_iterate_image J hcomm (k + n)]
  simp only [imageInterval, iterateMap]
  rw [Set.image_image, Function.iterate_add]
  rfl

/-! ## Finite phase labels and their intersection graph -/

/-- A phase label is retained as a label even if two geometric images
coincide. -/
abbrev PhaseLabel (L : ℕ) := ZMod L × ZMod L

/-- The phase interval indexed by least nonnegative representatives. -/
def labelledPhaseInterval (P Q : IntervalMap) (L : ℕ) (C : Set I)
    (α : PhaseLabel L) : Set I :=
  iterateMap P α.1.val '' (iterateMap Q α.2.val '' C)

/-- Every labelled phase is nonempty exactly when its seed is nonempty. -/
theorem labelledPhaseInterval_nonempty_iff
    (P Q : IntervalMap) (L : ℕ) (C : Set I) (α : PhaseLabel L) :
    (labelledPhaseInterval P Q L C α).Nonempty ↔ C.Nonempty := by
  constructor
  · rintro ⟨_, _, ⟨x, hx, _⟩, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨iterateMap P α.1.val (iterateMap Q α.2.val x),
      iterateMap Q α.2.val x, ⟨x, hx, rfl⟩, rfl⟩

/-- The common intersection of all labelled phase intervals. -/
def labelledPhaseCore (P Q : IntervalMap) (L : ℕ) (C : Set I) : Set I :=
  ⋂ α : PhaseLabel L, labelledPhaseInterval P Q L C α

/-- Translation in the first phase coordinate. -/
def phaseShiftP (L : ℕ) : PhaseLabel L ≃ PhaseLabel L where
  toFun α := (α.1 + 1, α.2)
  invFun α := (α.1 - 1, α.2)
  left_inv α := by rcases α with ⟨i, j⟩; simp
  right_inv α := by rcases α with ⟨i, j⟩; simp

/-- Translation in the second phase coordinate. -/
def phaseShiftQ (L : ℕ) : PhaseLabel L ≃ PhaseLabel L where
  toFun α := (α.1, α.2 + 1)
  invFun α := (α.1, α.2 - 1)
  left_inv α := by rcases α with ⟨i, j⟩; simp
  right_inv α := by rcases α with ⟨i, j⟩; simp

/-- Adjacency in the labelled intersection graph. -/
def intervalIntersectionAdjacent {V : Type*} (D : V → Set I)
    (u v : V) : Prop :=
  u ≠ v ∧ (D u ∩ D v).Nonempty

/-- Connectedness of the labelled intersection graph. -/
def IntervalIntersectionGraphConnected {V : Type*} (D : V → Set I) : Prop :=
  ∀ u v, Relation.ReflTransGen (intervalIntersectionAdjacent D) u v

/-- An equivalence preserving and reflecting adjacency. -/
def IsIntervalIntersectionGraphAutomorphism {V : Type*} (D : V → Set I)
    (e : V ≃ V) : Prop :=
  ∀ u v, intervalIntersectionAdjacent D (e u) (e v) ↔
    intervalIntersectionAdjacent D u v

/-- Vertex transitivity of a labelled interval-intersection graph. -/
def IntervalIntersectionGraphVertexTransitive {V : Type*}
    (D : V → Set I) : Prop :=
  ∀ u v, ∃ e : V ≃ V,
    IsIntervalIntersectionGraphAutomorphism D e ∧ e u = v

/-- Completeness of the labelled intersection graph. -/
def IntervalIntersectionGraphComplete {V : Type*} (D : V → Set I) : Prop :=
  ∀ u v, u ≠ v → intervalIntersectionAdjacent D u v

/-- The simple graph underlying a labelled interval-intersection family. -/
def intervalIntersectionSimpleGraph {V : Type*}
    (D : V → Set I) : SimpleGraph V where
  Adj := intervalIntersectionAdjacent D
  symm := by
    rintro u v ⟨huv, x, hxu, hxv⟩
    exact ⟨huv.symm, x, hxv, hxu⟩
  loopless := ⟨fun v h => h.1 rfl⟩

/-- The geometric union belonging to one graph component. -/
def intervalGraphComponentUnion {V : Type*} (D : V → Set I)
    (c : (intervalIntersectionSimpleGraph D).ConnectedComponent) : Set I :=
  ⋃ v : c.supp, D v.1

/-- Components of a finite compact connected interval family are represented
by pairwise-disjoint nondegenerate closed intervals. -/
theorem intervalGraph_componentInterval_package
    {V : Type*} [Fintype V] (D : V → Set I)
    (hcompact : ∀ v, IsCompact (D v))
    (hconnected : ∀ v, IsConnected (D v))
    (hnontrivial : ∀ v, ∃ x ∈ D v, ∃ y ∈ D v, x ≠ y) :
    ∃ classes : (intervalIntersectionSimpleGraph D).ConnectedComponent →
        ClosedSubinterval,
      (∀ c, (classes c).carrier = intervalGraphComponentUnion D c) ∧
      (∀ c, (classes c).Nondegenerate) ∧
      (∀ c d, c ≠ d → Disjoint (classes c).carrier (classes d).carrier) ∧
      (⋃ c, (classes c).carrier) = ⋃ v, D v := by
  classical
  let G := intervalIntersectionSimpleGraph D
  have hcomponentConnected (c : G.ConnectedComponent) :
      IsConnected (intervalGraphComponentUnion D c) := by
    letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
    apply IsConnected.iUnion_of_reflTransGen
    · intro v
      exact hconnected v.1
    · intro v w
      have hreach : Relation.ReflTransGen c.toSimpleGraph.Adj v w :=
        (c.toSimpleGraph.reachable_iff_reflTransGen v w).mp
          (c.reachable_toSimpleGraph v.2 w.2)
      exact hreach.mono fun a b hadj =>
        ((c.toSimpleGraph_adj a.2 b.2).mp hadj).2
  have hcomponentCompact (c : G.ConnectedComponent) :
      IsCompact (intervalGraphComponentUnion D c) := by
    exact isCompact_iUnion fun v : c.supp => hcompact v.1
  have hcomponentEq (c : G.ConnectedComponent) :
      intervalGraphComponentUnion D c =
        Set.Icc (sInf (intervalGraphComponentUnion D c))
          (sSup (intervalGraphComponentUnion D c)) :=
    eq_Icc_of_connected_compact (hcomponentConnected c) (hcomponentCompact c)
  have hcomponentLe (c : G.ConnectedComponent) :
      sInf (intervalGraphComponentUnion D c) ≤
        sSup (intervalGraphComponentUnion D c) := by
    have hne := (hcomponentConnected c).1
    rw [hcomponentEq c] at hne
    exact Set.nonempty_Icc.mp hne
  let classes : G.ConnectedComponent → ClosedSubinterval := fun c =>
    { left := sInf (intervalGraphComponentUnion D c)
      right := sSup (intervalGraphComponentUnion D c)
      left_le_right := hcomponentLe c }
  have hcarrier (c : G.ConnectedComponent) :
      (classes c).carrier = intervalGraphComponentUnion D c := by
    change Set.Icc (sInf (intervalGraphComponentUnion D c))
        (sSup (intervalGraphComponentUnion D c)) =
      intervalGraphComponentUnion D c
    exact (hcomponentEq c).symm
  have hnondegenerate (c : G.ConnectedComponent) :
      (classes c).Nondegenerate := by
    obtain ⟨v, hvc⟩ := c.nonempty_supp
    obtain ⟨x, hx, y, hy, hxy⟩ := hnontrivial v
    have hxcomponent : x ∈ intervalGraphComponentUnion D c :=
      Set.mem_iUnion.mpr ⟨⟨v, hvc⟩, hx⟩
    have hycomponent : y ∈ intervalGraphComponentUnion D c :=
      Set.mem_iUnion.mpr ⟨⟨v, hvc⟩, hy⟩
    rw [← hcarrier c] at hxcomponent hycomponent
    apply lt_of_le_of_ne (classes c).left_le_right
    intro hends
    have hxleft : x = (classes c).left :=
      le_antisymm (by simpa [hends] using hxcomponent.2) hxcomponent.1
    have hyleft : y = (classes c).left :=
      le_antisymm (by simpa [hends] using hycomponent.2) hycomponent.1
    exact hxy (hxleft.trans hyleft.symm)
  have hpairwise : ∀ c d : G.ConnectedComponent, c ≠ d →
      Disjoint (classes c).carrier (classes d).carrier := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    intro x hxc hxd
    rw [hcarrier c] at hxc
    rw [hcarrier d] at hxd
    obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hxc
    obtain ⟨w, hxw⟩ := Set.mem_iUnion.mp hxd
    have hmkV : G.connectedComponentMk v.1 = c :=
      (c.mem_supp_iff v.1).mp v.2
    have hmkW : G.connectedComponentMk w.1 = d :=
      (d.mem_supp_iff w.1).mp w.2
    have hmkEq : G.connectedComponentMk v.1 = G.connectedComponentMk w.1 := by
      by_cases hvw : v.1 = w.1
      · exact congrArg G.connectedComponentMk hvw
      · apply SimpleGraph.ConnectedComponent.sound
        have hadj : G.Adj v.1 w.1 := ⟨hvw, ⟨x, hxv, hxw⟩⟩
        exact hadj.reachable
    exact hcd (hmkV.symm.trans (hmkEq.trans hmkW))
  refine ⟨classes, hcarrier, hnondegenerate, hpairwise, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp hx
    rw [hcarrier c] at hxc
    obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hxc
    exact Set.mem_iUnion.mpr ⟨v.1, hxv⟩
  · intro hx
    obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hx
    let c : G.ConnectedComponent := G.connectedComponentMk v
    let vc : c.supp :=
      ⟨v, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
    apply Set.mem_iUnion.mpr
    refine ⟨c, ?_⟩
    rw [hcarrier c]
    exact Set.mem_iUnion.mpr ⟨vc, hxv⟩

/-- A geometric realization of a graph automorphism maps a component union
into a component union. -/
theorem intervalGraph_componentUnion_mapsTo_of_automorphism
    {V : Type*} (D : V → Set I) (F : IntervalMap) (e : V ≃ V)
    (hauto : IsIntervalIntersectionGraphAutomorphism D e)
    (himage : ∀ v, D (e v) = F '' D v) :
    ∀ c : (intervalIntersectionSimpleGraph D).ConnectedComponent,
      ∃ d : (intervalIntersectionSimpleGraph D).ConnectedComponent,
        MapsTo F (intervalGraphComponentUnion D c)
          (intervalGraphComponentUnion D d) := by
  classical
  let G := intervalIntersectionSimpleGraph D
  intro c
  obtain ⟨v, hvc⟩ := c.nonempty_supp
  let d : G.ConnectedComponent := G.connectedComponentMk (e v)
  refine ⟨d, ?_⟩
  intro x hx
  obtain ⟨u, hxu⟩ := Set.mem_iUnion.mp hx
  have hucomponent : G.connectedComponentMk u.1 = c :=
    (c.mem_supp_iff u.1).mp u.2
  have hvcomponent : G.connectedComponentMk v = c :=
    (c.mem_supp_iff v).mp hvc
  have huvReachable : G.Reachable u.1 v :=
    SimpleGraph.ConnectedComponent.exact
      (hucomponent.trans hvcomponent.symm)
  have huvPath : Relation.ReflTransGen G.Adj u.1 v :=
    (G.reachable_iff_reflTransGen u.1 v).mp huvReachable
  have hePath : Relation.ReflTransGen G.Adj (e u.1) (e v) := by
    exact huvPath.lift e fun a b hab => (hauto a b).mpr hab
  have heComponent : G.connectedComponentMk (e u.1) =
      G.connectedComponentMk (e v) := by
    apply SimpleGraph.ConnectedComponent.sound
    exact (G.reachable_iff_reflTransGen (e u.1) (e v)).mpr hePath
  have heMem : e u.1 ∈ d.supp := by
    apply (d.mem_supp_iff (e u.1)).mpr
    exact heComponent
  apply Set.mem_iUnion.mpr
  refine ⟨⟨e u.1, heMem⟩, ?_⟩
  rw [himage u.1]
  exact ⟨x, hxu, rfl⟩

/-- A disconnected finite family of nontrivial compact intervals cannot
cover the connected ambient interval. -/
theorem intervalGraph_union_ne_univ_of_not_connected
    {V : Type*} [Fintype V] (D : V → Set I)
    (hcompact : ∀ v, IsCompact (D v))
    (hconnected : ∀ v, IsConnected (D v))
    (hnontrivial : ∀ v, ∃ x ∈ D v, ∃ y ∈ D v, x ≠ y)
    (hgraph : ¬IntervalIntersectionGraphConnected D) :
    (⋃ v, D v) ≠ Set.univ := by
  classical
  let G := intervalIntersectionSimpleGraph D
  obtain ⟨classes, hcarrier, _hnondegenerate, hpairwise, hunion⟩ :=
    intervalGraph_componentInterval_package D hcompact hconnected hnontrivial
  unfold IntervalIntersectionGraphConnected at hgraph
  push Not at hgraph
  obtain ⟨u, v, huv⟩ := hgraph
  let cu : G.ConnectedComponent := G.connectedComponentMk u
  let cv : G.ConnectedComponent := G.connectedComponentMk v
  have hcune : cu ≠ cv := by
    intro hcomp
    apply huv
    have hreach : G.Reachable u v :=
      SimpleGraph.ConnectedComponent.exact hcomp
    exact (G.reachable_iff_reflTransGen u v).mp hreach
  intro hcover
  let A : Set I := (classes cu).carrier
  let B : Set I := ⋃ d : {d : G.ConnectedComponent // d ≠ cu},
    (classes d.1).carrier
  have hAcompact : IsCompact A := isCompact_Icc
  have hBcompact : IsCompact B := by
    exact isCompact_iUnion fun d : {d : G.ConnectedComponent // d ≠ cu} =>
      (isCompact_Icc : IsCompact (classes d.1).carrier)
  have hABunion : A ∪ B = Set.univ := by
    rw [← hcover, ← hunion]
    ext x
    constructor
    · rintro (hxA | hxB)
      · exact Set.mem_iUnion.mpr ⟨cu, hxA⟩
      · obtain ⟨d, hxd⟩ := Set.mem_iUnion.mp hxB
        exact Set.mem_iUnion.mpr ⟨d.1, hxd⟩
    · intro hx
      obtain ⟨d, hxd⟩ := Set.mem_iUnion.mp hx
      by_cases hdc : d = cu
      · left
        simpa [A, hdc] using hxd
      · right
        exact Set.mem_iUnion.mpr ⟨⟨d, hdc⟩, hxd⟩
  have hABdisjoint : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨d, hxd⟩ := Set.mem_iUnion.mp hxB
    exact (Set.disjoint_left.mp (hpairwise cu d.1 d.2.symm)) hxA hxd
  have hB_eq_compl : B = Aᶜ := by
    ext x
    constructor
    · intro hxB hxA
      exact (Set.disjoint_left.mp hABdisjoint) hxA hxB
    · intro hxA
      have hx : x ∈ A ∪ B := by rw [hABunion]; exact Set.mem_univ x
      rcases hx with hxA' | hxB
      · exact (hxA hxA').elim
      · exact hxB
  have hA_eq_compl : A = Bᶜ := by rw [hB_eq_compl, compl_compl]
  have hAopen : IsOpen A := by rw [hA_eq_compl]; exact hBcompact.isClosed.isOpen_compl
  have hBopen : IsOpen B := by rw [hB_eq_compl]; exact hAcompact.isClosed.isOpen_compl
  have hAne : (Set.univ ∩ A).Nonempty := by
    exact ⟨(classes cu).left, Set.mem_univ _,
      Set.left_mem_Icc.mpr (classes cu).left_le_right⟩
  have hBne : (Set.univ ∩ B).Nonempty := by
    refine ⟨(classes cv).left, Set.mem_univ _, ?_⟩
    exact Set.mem_iUnion.mpr
      ⟨⟨cv, hcune.symm⟩,
        Set.left_mem_Icc.mpr (classes cv).left_le_right⟩
  have hinter := isConnected_univ.isPreconnected A B hAopen hBopen
    (by rw [hABunion]) hAne hBne
  obtain ⟨x, _hxuniv, hxA, hxB⟩ := hinter
  exact (Set.disjoint_left.mp hABdisjoint) hxA hxB

/-- Index-order-free wrapper around the dependency-clean cumulative-length
quotient.  The exact fibre formula is retained in the caller's index type. -/
theorem exists_canonicalFiniteIntervalQuotient_of_finiteFamily
    {α : Type*} [Fintype α] (classes : α → ClosedSubinterval)
    (hnondegenerate : ∀ i, (classes i).Nondegenerate)
    (hpairwise : ∀ i j, i ≠ j →
      Disjoint (classes i).carrier (classes j).carrier)
    (hproper : (⋃ i, (classes i).carrier) ≠ Set.univ) :
    ∃ π : CanonicalFiniteIntervalQuotient,
      (∀ x y : I, π x = π y ↔
        x = y ∨ ∃ i : α,
          x ∈ (classes i).carrier ∧ y ∈ (classes i).carrier) ∧
      π.collapsedSet = ⋃ i, (classes i).carrier := by
  classical
  have hleftInjective : Function.Injective (fun i : α => (classes i).left) := by
    intro i j hleft
    by_contra hij
    have hdisj := hpairwise i j hij
    have hlefti : (classes i).left ∈ (classes i).carrier :=
      Set.left_mem_Icc.mpr (classes i).left_le_right
    have hleftj : (classes i).left ∈ (classes j).carrier := by
      exact ⟨hleft.ge, hleft.le.trans (classes j).left_le_right⟩
    exact (Set.disjoint_left.mp hdisj) hlefti hleftj
  letI : LinearOrder α :=
    LinearOrder.lift' (fun i : α => (classes i).left) hleftInjective
  let e : Fin (Fintype.card α) ≃o α :=
    Fintype.orderIsoFinOfCardEq α rfl
  let orderedClasses : Fin (Fintype.card α) → ClosedSubinterval :=
    fun i => classes (e i)
  have hordered : PLQuotientSupport.StrictlyOrderedIntervalFamily
      orderedClasses := by
    intro i j hij
    have hleft : (orderedClasses i).left < (orderedClasses j).left :=
      e.strictMono hij
    by_contra hnot
    have hcommon : (orderedClasses j).left ∈
        (orderedClasses i).carrier ∩ (orderedClasses j).carrier :=
      ⟨⟨hleft.le, le_of_not_gt hnot⟩,
        Set.left_mem_Icc.mpr (orderedClasses j).left_le_right⟩
    have heij : e i ≠ e j := e.injective.ne (ne_of_lt hij)
    exact (Set.disjoint_left.mp (hpairwise (e i) (e j) heij))
      hcommon.1 hcommon.2
  have horderedNondegenerate : ∀ i, (orderedClasses i).Nondegenerate :=
    fun i => hnondegenerate (e i)
  have hlocus : collapsedLocus orderedClasses = ⋃ i, (classes i).carrier := by
    ext x
    constructor
    · rintro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      exact Set.mem_iUnion.mpr ⟨e i, hxi⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      obtain ⟨j, rfl⟩ := e.surjective i
      exact Set.mem_iUnion.mpr ⟨j, hxi⟩
  have horderedProper : collapsedLocus orderedClasses ≠ Set.univ := by
    rwa [hlocus]
  let π := PLQuotientSupport.canonicalFiniteIntervalQuotientOfOrdered
    orderedClasses hordered horderedNondegenerate horderedProper
  refine ⟨π, ?_, ?_⟩
  · intro x y
    rw [show π x = π y ↔
        x = y ∨ ∃ i, x ∈ (orderedClasses i).carrier ∧
          y ∈ (orderedClasses i).carrier from π.fibre_iff x y]
    constructor
    · rintro (rfl | ⟨i, hxi, hyi⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨e i, hxi, hyi⟩
    · rintro (rfl | ⟨i, hxi, hyi⟩)
      · exact Or.inl rfl
      · obtain ⟨j, rfl⟩ := e.surjective i
        exact Or.inr ⟨j, hxi, hyi⟩
  · change collapsedLocus orderedClasses = ⋃ i, (classes i).carrier
    exact hlocus

/-- A continuous self-map carrying a nondegenerate interval onto itself has
two distinct fixed points of its square. -/
theorem intervalSurjection_square_has_two_fixedPoints
    (T : IntervalMap) (J : ClosedSubinterval)
    (hT : Continuous T)
    (honto : T '' J.carrier = J.carrier)
    (hJnondegenerate : J.Nondegenerate) :
    ∃ x ∈ J.carrier, ∃ y ∈ J.carrier,
      x ≠ y ∧ IsFixedPoint (iterateMap T 2) x ∧
        IsFixedPoint (iterateMap T 2) y := by
  have hmaps : MapsTo T J.carrier J.carrier := by
    intro x hx
    rw [← honto]
    exact ⟨x, hx, rfl⟩
  obtain ⟨z, hzJ, hzfix⟩ :=
    exists_mem_Icc_isFixedPt_of_mapsTo hT.continuousOn
      J.left_le_right hmaps
  have hzg : IsFixedPoint (iterateMap T 2) z :=
    Function.iterate_fixed hzfix 2
  suffices hsecond : ∃ y ∈ J.carrier,
      y ≠ z ∧ IsFixedPoint (iterateMap T 2) y by
    obtain ⟨y, hyJ, hyz, hyfix⟩ := hsecond
    exact ⟨z, hzJ, y, hyJ, hyz.symm, hzg, hyfix⟩
  by_contra hnoSecond
  push Not at hnoSecond
  have hgUnique : ∀ x ∈ J.carrier,
      IsFixedPoint (iterateMap T 2) x → x = z := by
    intro x hxJ hxg
    by_contra hxz
    exact hnoSecond x hxJ hxz hxg
  have hTUnique : ∀ x ∈ J.carrier, IsFixedPoint T x → x = z := by
    intro x hxJ hxT
    exact hgUnique x hxJ (Function.iterate_fixed hxT 2)
  have hgContinuous : Continuous (iterateMap T 2) := hT.iterate 2
  have hgMaps : MapsTo (iterateMap T 2) J.carrier J.carrier := by
    intro x hx
    exact hmaps (hmaps hx)
  have hTleft : J.left ≤ T J.left :=
    (hmaps (Set.left_mem_Icc.mpr J.left_le_right)).1
  have hTright : T J.right ≤ J.right :=
    (hmaps (Set.right_mem_Icc.mpr J.left_le_right)).2
  have hgleft : J.left ≤ iterateMap T 2 J.left :=
    (hgMaps (Set.left_mem_Icc.mpr J.left_le_right)).1
  have hgright : iterateMap T 2 J.right ≤ J.right :=
    (hgMaps (Set.right_mem_Icc.mpr J.left_le_right)).2
  have hTmovesLeft : ∀ x ∈ J.carrier, x < z → x < T x := by
    intro x hxJ hxz
    by_contra hnot
    have hTxle : T x ≤ x := le_of_not_gt hnot
    obtain ⟨w, hw, hwfix⟩ :=
      exists_mem_Icc_isFixedPt hT.continuousOn hxJ.1 hTleft hTxle
    have hwJ : w ∈ J.carrier := ⟨hw.1, hw.2.trans hxJ.2⟩
    have hwz : w = z := hTUnique w hwJ hwfix
    exact (not_le_of_gt hxz) (hwz ▸ hw.2)
  have hTmovesRight : ∀ x ∈ J.carrier, z < x → T x < x := by
    intro x hxJ hzx
    by_contra hnot
    have hxle : x ≤ T x := le_of_not_gt hnot
    obtain ⟨w, hw, hwfix⟩ :=
      exists_mem_Icc_isFixedPt hT.continuousOn hxJ.2 hxle hTright
    have hwJ : w ∈ J.carrier := ⟨hxJ.1.trans hw.1, hw.2⟩
    have hwz : w = z := hTUnique w hwJ hwfix
    exact (not_le_of_gt hzx) (hwz ▸ hw.1)
  have hgmovesLeft : ∀ x ∈ J.carrier, x < z →
      x < iterateMap T 2 x := by
    intro x hxJ hxz
    by_contra hnot
    have hgxle : iterateMap T 2 x ≤ x := le_of_not_gt hnot
    obtain ⟨w, hw, hwfix⟩ :=
      exists_mem_Icc_isFixedPt hgContinuous.continuousOn
        hxJ.1 hgleft hgxle
    have hwJ : w ∈ J.carrier := ⟨hw.1, hw.2.trans hxJ.2⟩
    have hwz : w = z := hgUnique w hwJ hwfix
    exact (not_le_of_gt hxz) (hwz ▸ hw.2)
  have hzltRight : z < J.right := by
    by_contra hnot
    have hrightle : J.right ≤ z := le_of_not_gt hnot
    have hzright : z = J.right := le_antisymm hzJ.2 hrightle
    subst z
    have hleftImage : J.left ∈ T '' J.carrier := by
      rw [honto]
      exact Set.left_mem_Icc.mpr J.left_le_right
    obtain ⟨v, hvJ, hv⟩ := hleftImage
    have hvne : v ≠ J.right := by
      intro hvright
      subst v
      exact hJnondegenerate.ne' (hzfix.symm.trans hv)
    have hvlt : v < J.right := lt_of_le_of_ne hvJ.2 hvne
    have hmove := hTmovesLeft v hvJ hvlt
    rw [hv] at hmove
    exact (not_lt_of_ge hvJ.1) hmove
  have hleftltz : J.left < z := by
    by_contra hnot
    have hzle : z ≤ J.left := le_of_not_gt hnot
    have hzleft : z = J.left := le_antisymm hzle hzJ.1
    subst z
    have hrightImage : J.right ∈ T '' J.carrier := by
      rw [honto]
      exact Set.right_mem_Icc.mpr J.left_le_right
    obtain ⟨u, huJ, hu⟩ := hrightImage
    have hune : u ≠ J.left := by
      intro huleft
      subst u
      exact hJnondegenerate.ne (hzfix.symm.trans hu)
    have hult : J.left < u := lt_of_le_of_ne huJ.1 hune.symm
    have hmove := hTmovesRight u huJ hult
    rw [hu] at hmove
    exact (not_lt_of_ge huJ.2) hmove
  have hrightImage : J.right ∈ T '' J.carrier := by
    rw [honto]
    exact Set.right_mem_Icc.mpr J.left_le_right
  obtain ⟨u, huJ, hu⟩ := hrightImage
  have hultZ : u < z := by
    rcases lt_trichotomy u z with huz | huz | hzu
    · exact huz
    · subst u
      exact (hzltRight.ne (hzfix.symm.trans hu)).elim
    · have hTu : T u < u := hTmovesRight u huJ hzu
      exact ((hu ▸ hTu).trans_le huJ.2).false.elim
  have hleftImage : J.left ∈ T '' J.carrier := by
    rw [honto]
    exact Set.left_mem_Icc.mpr J.left_le_right
  obtain ⟨v, hvJ, hv⟩ := hleftImage
  have hzltV : z < v := by
    rcases lt_trichotomy z v with hzv | hzv | hvz
    · exact hzv
    · subst v
      exact (hleftltz.ne' (hzfix.symm.trans hv)).elim
    · have hvT : v < T v := hTmovesLeft v hvJ hvz
      exact (hvJ.1.trans_lt (hv ▸ hvT)).false.elim
  have hvBetween : v ∈ Set.Icc (T z) (T u) := by
    rw [hzfix, hu]
    exact ⟨hzltV.le, hvJ.2⟩
  obtain ⟨w, hw, hTw⟩ :=
    intermediate_value_Icc' hultZ.le hT.continuousOn hvBetween
  have hwJ : w ∈ J.carrier :=
    ⟨huJ.1.trans hw.1, hw.2.trans hzJ.2⟩
  have hwltZ : w < z :=
    lt_of_le_of_ne hw.2 fun hwz => by
      subst w
      exact hzltV.ne (hzfix.symm.trans hTw)
  have hgw : iterateMap T 2 w = J.left := by
    change T (T w) = J.left
    rw [hTw, hv]
  have hwltg := hgmovesLeft w hwJ hwltZ
  rw [hgw] at hwltg
  exact (not_lt_of_ge (huJ.1.trans hw.1)) hwltg

private theorem iterate_image_iterate_image (T : IntervalMap)
    (m n : ℕ) (C : Set I) :
    T^[m] '' (T^[n] '' C) = T^[m + n] '' C := by
  rw [Set.image_image, Function.iterate_add]
  rfl

private theorem image_image_commute {F G : IntervalMap}
    (hcomm : Commute F G) (C : Set I) :
    F '' (G '' C) = G '' (F '' C) := by
  rw [Set.image_image, Set.image_image]
  exact congrArg (fun H : IntervalMap => H '' C) hcomm.comp_eq

private theorem zmod_shift_image_eq {T : IntervalMap} {L : ℕ}
    (hL : 0 < L) (C : Set I)
    (hperiodic : T^[L] '' C = C) (i : ZMod L) :
    T^[(i + 1).val] '' C = T '' (T^[i.val] '' C) := by
  by_cases hLone : L = 1
  · subst L
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    have hval : (1 : ZMod 1).val = 0 := by decide
    change T^[(1 : ZMod 1).val] '' C =
      T '' (T^[(0 : ZMod 1).val] '' C)
    rw [hval, ZMod.val_zero, Function.iterate_zero, Set.image_id]
    simpa using hperiodic.symm
  · have hLtwo : 1 < L := by omega
    letI : Fact (1 < L) := ⟨hLtwo⟩
    letI : NeZero L := ⟨by omega⟩
    by_cases hi : i.val + 1 < L
    · have hval : (i + 1).val = i.val + 1 := by
        have hone : (1 : ZMod L).val = 1 := ZMod.val_one L
        have hadd := ZMod.val_add_of_lt
          (a := i) (b := (1 : ZMod L)) (by simpa [hone] using hi)
        simpa [hone] using hadd
      rw [hval, Function.iterate_succ' T i.val]
      exact (Set.image_image T (T^[i.val]) C).symm
    · have hieq : i.val + 1 = L := by
        have := i.val_lt
        omega
      have hval : (i + 1).val = 0 := by
        rw [ZMod.val_add]
        simpa [ZMod.val_one, hieq]
      rw [hval, Function.iterate_zero, Set.image_id]
      calc
        C = T^[L] '' C := hperiodic.symm
        _ = T^[i.val + 1] '' C := by rw [hieq]
        _ = T '' (T^[i.val] '' C) := by
          rw [Function.iterate_succ' T i.val]
          exact (Set.image_image T (T^[i.val]) C).symm

private theorem zmod_shift_back_image_eq {T : IntervalMap} {L : ℕ}
    (hL : 0 < L) (C : Set I)
    (hperiodic : T^[L] '' C = C) (i : ZMod L) :
    T^[L - 1] '' (T^[(i + 1).val] '' C) = T^[i.val] '' C := by
  rw [zmod_shift_image_eq hL C hperiodic i]
  change T^[L - 1] '' (T^[1] '' (T^[i.val] '' C)) = T^[i.val] '' C
  rw [iterate_image_iterate_image T (L - 1) 1]
  have hpred : L - 1 + 1 = L := by omega
  rw [hpred]
  rw [image_image_commute ((Function.Commute.refl T).iterate_iterate L i.val)]
  rw [hperiodic]

/-- `P` translates the first phase coordinate. -/
theorem labelledPhaseInterval_shiftP
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (α : PhaseLabel L) :
    labelledPhaseInterval P Q L C (phaseShiftP L α) =
      P '' labelledPhaseInterval P Q L C α := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rcases α with ⟨i, j⟩
  change P^[(i + 1).val] '' (Q^[j.val] '' C) =
    P '' (P^[i.val] '' (Q^[j.val] '' C))
  exact zmod_shift_image_eq hL (Q^[j.val] '' C) (by
    calc
      P^[L] '' (Q^[j.val] '' C) = Q^[j.val] '' (P^[L] '' C) :=
        image_image_commute (hcomm.iterate_iterate L j.val) _
      _ = Q^[j.val] '' C := by simpa [iterateMap] using congrArg (Q^[j.val] '' ·) hPperiodic) i

/-- A complementary `P` return translates a shifted phase back. -/
theorem labelledPhaseInterval_shiftP_back
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (α : PhaseLabel L) :
    P^[L - 1] '' labelledPhaseInterval P Q L C (phaseShiftP L α) =
      labelledPhaseInterval P Q L C α := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rcases α with ⟨i, j⟩
  change P^[L - 1] '' (P^[(i + 1).val] '' (Q^[j.val] '' C)) =
    P^[i.val] '' (Q^[j.val] '' C)
  exact zmod_shift_back_image_eq hL (Q^[j.val] '' C) (by
    calc
      P^[L] '' (Q^[j.val] '' C) = Q^[j.val] '' (P^[L] '' C) :=
        image_image_commute (hcomm.iterate_iterate L j.val) _
      _ = Q^[j.val] '' C := by simpa [iterateMap] using congrArg (Q^[j.val] '' ·) hPperiodic) i

/-- `Q` translates the second phase coordinate. -/
theorem labelledPhaseInterval_shiftQ
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hQperiodic : iterateMap Q L '' C = C)
    (α : PhaseLabel L) :
    labelledPhaseInterval P Q L C (phaseShiftQ L α) =
      Q '' labelledPhaseInterval P Q L C α := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rcases α with ⟨i, j⟩
  change P^[i.val] '' (Q^[(j + 1).val] '' C) =
    Q '' (P^[i.val] '' (Q^[j.val] '' C))
  rw [image_image_commute (hcomm.iterate_left i.val).symm]
  exact congrArg (P^[i.val] '' ·)
    (zmod_shift_image_eq hL C (by simpa [iterateMap] using hQperiodic) j)

/-- A complementary `Q` return translates a shifted phase back. -/
theorem labelledPhaseInterval_shiftQ_back
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hQperiodic : iterateMap Q L '' C = C)
    (α : PhaseLabel L) :
    Q^[L - 1] '' labelledPhaseInterval P Q L C (phaseShiftQ L α) =
      labelledPhaseInterval P Q L C α := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rcases α with ⟨i, j⟩
  change Q^[L - 1] '' (P^[i.val] '' (Q^[(j + 1).val] '' C)) =
    P^[i.val] '' (Q^[j.val] '' C)
  rw [image_image_commute (hcomm.iterate_iterate i.val (L - 1)).symm]
  exact congrArg (P^[i.val] '' ·)
    (zmod_shift_back_image_eq hL C (by simpa [iterateMap] using hQperiodic) j)

/-- Complementary powers return every phase interval onto its periodic base. -/
theorem labelledPhaseInterval_return_image
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C)
    (α : PhaseLabel L) :
    iterateMap P (L - α.1.val) ''
        (iterateMap Q (L - α.2.val) ''
          labelledPhaseInterval P Q L C α) = C := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rcases α with ⟨i, j⟩
  have hi : i.val ≤ L := Nat.le_of_lt i.val_lt
  have hj : j.val ≤ L := Nat.le_of_lt j.val_lt
  have hPperiodic' : P^[L] '' C = C := by simpa [iterateMap] using hPperiodic
  have hQperiodic' : Q^[L] '' C = C := by simpa [iterateMap] using hQperiodic
  change P^[L - i.val] ''
      (Q^[L - j.val] '' (P^[i.val] '' (Q^[j.val] '' C))) = C
  calc
    _ = P^[L - i.val] ''
        (P^[i.val] '' (Q^[L - j.val] '' (Q^[j.val] '' C))) := by
          exact congrArg (P^[L - i.val] '' ·)
            (image_image_commute
              (hcomm.iterate_iterate i.val (L - j.val)).symm
              (Q^[j.val] '' C))
    _ = P^[L - i.val] ''
        (P^[i.val] '' (Q^[(L - j.val) + j.val] '' C)) := by
          exact congrArg (fun S => P^[L - i.val] '' (P^[i.val] '' S))
            (iterate_image_iterate_image Q (L - j.val) j.val C)
    _ = P^[L - i.val] '' (P^[i.val] '' (Q^[L] '' C)) := by
          rw [Nat.sub_add_cancel hj]
    _ = P^[L - i.val] '' (P^[i.val] '' C) := by rw [hQperiodic']
    _ = P^[(L - i.val) + i.val] '' C := by
          exact iterate_image_iterate_image P (L - i.val) i.val C
    _ = P^[L] '' C := by rw [Nat.sub_add_cancel hi]
    _ = C := hPperiodic'

/-- A periodic nontrivial base cannot have a singleton phase image. -/
theorem labelledPhaseIntervals_nontrivial
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C)
    (hCnontrivial : ∃ x ∈ C, ∃ y ∈ C, x ≠ y) :
    ∀ α : PhaseLabel L,
      ∃ x ∈ labelledPhaseInterval P Q L C α,
        ∃ y ∈ labelledPhaseInterval P Q L C α, x ≠ y := by
  intro α
  obtain ⟨x, hx, y, hy, hxy⟩ := hCnontrivial
  have hreturn := labelledPhaseInterval_return_image
    hL C hcomm hPperiodic hQperiodic α
  have hxreturn : x ∈ iterateMap P (L - α.1.val) ''
      (iterateMap Q (L - α.2.val) ''
        labelledPhaseInterval P Q L C α) := by rw [hreturn]; exact hx
  have hyreturn : y ∈ iterateMap P (L - α.1.val) ''
      (iterateMap Q (L - α.2.val) ''
        labelledPhaseInterval P Q L C α) := by rw [hreturn]; exact hy
  obtain ⟨x₁, ⟨x₀, hx₀, hx₁⟩, hx'⟩ := hxreturn
  obtain ⟨y₁, ⟨y₀, hy₀, hy₁⟩, hy'⟩ := hyreturn
  refine ⟨x₀, hx₀, y₀, hy₀, ?_⟩
  intro hxy₀
  apply hxy
  rw [← hx', ← hy', ← hx₁, ← hy₁, hxy₀]

/-- Both full return powers preserve every phase interval. -/
theorem labelledPhaseInterval_periodic_images
    {P Q : IntervalMap} {L : ℕ} (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C)
    (α : PhaseLabel L) :
    iterateMap P L '' labelledPhaseInterval P Q L C α =
        labelledPhaseInterval P Q L C α ∧
      iterateMap Q L '' labelledPhaseInterval P Q L C α =
        labelledPhaseInterval P Q L C α := by
  rcases α with ⟨i, j⟩
  have hPperiodic' : P^[L] '' C = C := by simpa [iterateMap] using hPperiodic
  have hQperiodic' : Q^[L] '' C = C := by simpa [iterateMap] using hQperiodic
  constructor
  · change P^[L] '' (P^[i.val] '' (Q^[j.val] '' C)) =
      P^[i.val] '' (Q^[j.val] '' C)
    calc
      _ = P^[i.val] '' (P^[L] '' (Q^[j.val] '' C)) :=
        image_image_commute
          ((Function.Commute.refl P).iterate_iterate L i.val) _
      _ = P^[i.val] '' (Q^[j.val] '' (P^[L] '' C)) := by
        exact congrArg (P^[i.val] '' ·)
          (image_image_commute (hcomm.iterate_iterate L j.val) C)
      _ = P^[i.val] '' (Q^[j.val] '' C) := by rw [hPperiodic']
  · change Q^[L] '' (P^[i.val] '' (Q^[j.val] '' C)) =
      P^[i.val] '' (Q^[j.val] '' C)
    calc
      _ = P^[i.val] '' (Q^[L] '' (Q^[j.val] '' C)) :=
        image_image_commute (hcomm.iterate_iterate i.val L).symm _
      _ = P^[i.val] '' (Q^[j.val] '' (Q^[L] '' C)) := by
        exact congrArg (P^[i.val] '' ·)
          (image_image_commute
            ((Function.Commute.refl Q).iterate_iterate L j.val) C)
      _ = P^[i.val] '' (Q^[j.val] '' C) := by rw [hQperiodic']

/-- The positive return word preserves every graph-component union. -/
theorem labelledPhaseComponent_returnWord_image
    {P Q : IntervalMap} {L : ℕ} (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C)
    (c : (intervalIntersectionSimpleGraph
      (labelledPhaseInterval P Q L C)).ConnectedComponent) :
    ((iterateMap P L) ∘ (iterateMap Q L)) ''
        intervalGraphComponentUnion (labelledPhaseInterval P Q L C) c =
      intervalGraphComponentUnion (labelledPhaseInterval P Q L C) c := by
  let D := labelledPhaseInterval P Q L C
  have hpiece : ∀ α, ((iterateMap P L) ∘ (iterateMap Q L)) '' D α = D α := by
    intro α
    obtain ⟨hPα, hQα⟩ :=
      labelledPhaseInterval_periodic_images C hcomm hPperiodic hQperiodic α
    calc
      ((iterateMap P L) ∘ (iterateMap Q L)) '' D α =
          iterateMap P L '' (iterateMap Q L '' D α) :=
        (Set.image_image (iterateMap P L) (iterateMap Q L) (D α)).symm
      _ = iterateMap P L '' D α := by rw [hQα]
      _ = D α := hPα
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨α, hyα⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨α, ?_⟩
    have hmem : ((iterateMap P L) ∘ (iterateMap Q L)) y ∈
        ((iterateMap P L) ∘ (iterateMap Q L)) '' D α.1 := ⟨y, hyα, rfl⟩
    rw [hpiece α.1] at hmem
    exact hmem
  · intro hx
    obtain ⟨α, hxα⟩ := Set.mem_iUnion.mp hx
    have hximage : x ∈ ((iterateMap P L) ∘ (iterateMap Q L)) '' D α.1 := by
      rw [hpiece α.1]
      exact hxα
    obtain ⟨y, hyα, hyx⟩ := hximage
    exact ⟨y, Set.mem_iUnion.mpr ⟨α, hyα⟩, hyx⟩

/-- Both coordinate translations are graph automorphisms; injectivity of the
interval maps is not required. -/
theorem phaseLabel_graph_automorphisms
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C) :
    IsIntervalIntersectionGraphAutomorphism
        (labelledPhaseInterval P Q L C) (phaseShiftP L) ∧
      IsIntervalIntersectionGraphAutomorphism
        (labelledPhaseInterval P Q L C) (phaseShiftQ L) := by
  let D := labelledPhaseInterval P Q L C
  have hPforward := labelledPhaseInterval_shiftP hL C hcomm hPperiodic
  have hPback := labelledPhaseInterval_shiftP_back hL C hcomm hPperiodic
  have hQforward := labelledPhaseInterval_shiftQ hL C hcomm hQperiodic
  have hQback := labelledPhaseInterval_shiftQ_back hL C hcomm hQperiodic
  constructor
  · intro u v
    constructor
    · rintro ⟨huv, ⟨x, hxu, hxv⟩⟩
      refine ⟨fun h => huv (congrArg (phaseShiftP L) h), ?_⟩
      exact ⟨P^[L - 1] x,
        by rw [← hPback u]; exact ⟨x, hxu, rfl⟩,
        by rw [← hPback v]; exact ⟨x, hxv, rfl⟩⟩
    · rintro ⟨huv, ⟨x, hxu, hxv⟩⟩
      refine ⟨fun h => huv ((phaseShiftP L).injective h), ?_⟩
      exact ⟨P x,
        by rw [hPforward u]; exact ⟨x, hxu, rfl⟩,
        by rw [hPforward v]; exact ⟨x, hxv, rfl⟩⟩
  · intro u v
    constructor
    · rintro ⟨huv, ⟨x, hxu, hxv⟩⟩
      refine ⟨fun h => huv (congrArg (phaseShiftQ L) h), ?_⟩
      exact ⟨Q^[L - 1] x,
        by rw [← hQback u]; exact ⟨x, hxu, rfl⟩,
        by rw [← hQback v]; exact ⟨x, hxv, rfl⟩⟩
    · rintro ⟨huv, ⟨x, hxu, hxv⟩⟩
      refine ⟨fun h => huv ((phaseShiftQ L).injective h), ?_⟩
      exact ⟨Q x,
        by rw [hQforward u]; exact ⟨x, hxu, rfl⟩,
        by rw [hQforward v]; exact ⟨x, hxv, rfl⟩⟩

private def equivIterate {V : Type*} (e : V ≃ V) : ℕ → V ≃ V
  | 0 => Equiv.refl V
  | n + 1 => (equivIterate e n).trans e

@[simp] private theorem equivIterate_succ_apply {V : Type*}
    (e : V ≃ V) (n : ℕ) (v : V) :
    equivIterate e (n + 1) v = e (equivIterate e n v) := rfl

private theorem graphAutomorphism_trans {V : Type*} (D : V → Set I)
    (e f : V ≃ V)
    (he : IsIntervalIntersectionGraphAutomorphism D e)
    (hf : IsIntervalIntersectionGraphAutomorphism D f) :
    IsIntervalIntersectionGraphAutomorphism D (e.trans f) := by
  intro u v
  exact (hf (e u) (e v)).trans (he u v)

private theorem graphAutomorphism_equivIterate {V : Type*}
    (D : V → Set I) (e : V ≃ V)
    (he : IsIntervalIntersectionGraphAutomorphism D e) :
    ∀ n : ℕ, IsIntervalIntersectionGraphAutomorphism D (equivIterate e n)
  | 0 => by intro u v; rfl
  | n + 1 => graphAutomorphism_trans D (equivIterate e n) e
      (graphAutomorphism_equivIterate D e he n) he

private theorem phaseShiftP_equivIterate_apply (L n : ℕ)
    (α : PhaseLabel L) :
    equivIterate (phaseShiftP L) n α = (α.1 + (n : ZMod L), α.2) := by
  induction n with
  | zero => simp [equivIterate]
  | succ n ih =>
      rw [equivIterate_succ_apply, ih]
      simp [phaseShiftP, Nat.cast_succ, add_assoc]

private theorem phaseShiftQ_equivIterate_apply (L n : ℕ)
    (α : PhaseLabel L) :
    equivIterate (phaseShiftQ L) n α = (α.1, α.2 + (n : ZMod L)) := by
  induction n with
  | zero => simp [equivIterate]
  | succ n ih =>
      rw [equivIterate_succ_apply, ih]
      simp [phaseShiftQ, Nat.cast_succ, add_assoc]

/-- Translation by arbitrary natural offsets in the two cyclic phase
coordinates. -/
def phaseTranslation (L u v : ℕ) : PhaseLabel L ≃ PhaseLabel L where
  toFun α := (α.1 + (u : ZMod L), α.2 + (v : ZMod L))
  invFun α := (α.1 - (u : ZMod L), α.2 - (v : ZMod L))
  left_inv α := by
    apply Prod.ext <;> simp
  right_inv α := by
    apply Prod.ext <;> simp

/-- Every natural coordinate translation preserves phase intersections. -/
theorem phaseTranslation_graphAutomorphism
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C) (u v : ℕ) :
    IsIntervalIntersectionGraphAutomorphism
      (labelledPhaseInterval P Q L C) (phaseTranslation L u v) := by
  obtain ⟨hPauto, hQauto⟩ :=
    phaseLabel_graph_automorphisms hL C hcomm hPperiodic hQperiodic
  let eP := equivIterate (phaseShiftP L) u
  let eQ := equivIterate (phaseShiftQ L) v
  have he := graphAutomorphism_trans _ eP eQ
    (graphAutomorphism_equivIterate _ _ hPauto u)
    (graphAutomorphism_equivIterate _ _ hQauto v)
  have htranslation : eP.trans eQ = phaseTranslation L u v := by
    ext α <;> simp [eP, eQ, phaseTranslation,
      phaseShiftP_equivIterate_apply, phaseShiftQ_equivIterate_apply]
  rw [← htranslation]
  exact he

/-- If the `L`-th image of a set returns to itself, every image exponent may
be reduced modulo `L`. -/
theorem iterate_image_mod_eq
    {T : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hperiodic : iterateMap T L '' C = C) (n : ℕ) :
    iterateMap T (n % L) '' C = iterateMap T n '' C := by
  let F : Set I → Set I := fun D => T '' D
  have hiter : ∀ k : ℕ, F^[k] C = iterateMap T k '' C := by
    intro k
    induction k with
    | zero => simp [F, iterateMap]
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih]
        simpa [F, iterateMap, Nat.add_comm] using
          (iterate_image_iterate_image T 1 k C)
  have hperiodicF : Function.IsPeriodicPt F L C := by
    change F^[L] C = C
    rw [hiter]
    exact hperiodic
  rw [← hiter, ← hiter]
  exact hperiodicF.iterate_mod_apply n

/-- A phase written with arbitrary natural exponents agrees with the phase
indexed by their classes in `ZMod L`. -/
theorem naturalPhase_eq_labelledPhase
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C) (i j : ℕ) :
    iterateMap P i '' (iterateMap Q j '' C) =
      labelledPhaseInterval P Q L C ((i : ZMod L), (j : ZMod L)) := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hQreduce := iterate_image_mod_eq hL C hQperiodic j
  have hPperiodicQ :
      iterateMap P L '' (iterateMap Q (j % L) '' C) =
        iterateMap Q (j % L) '' C := by
    calc
      iterateMap P L '' (iterateMap Q (j % L) '' C) =
          iterateMap Q (j % L) '' (iterateMap P L '' C) :=
        image_image_commute (hcomm.iterate_iterate L (j % L)) _
      _ = iterateMap Q (j % L) '' C := by rw [hPperiodic]
  have hPreduce := iterate_image_mod_eq hL
    (iterateMap Q (j % L) '' C) hPperiodicQ i
  rw [← hQreduce, ← hPreduce]
  simp only [labelledPhaseInterval, ZMod.val_natCast]

/-- Coordinate translations act transitively on phase labels. -/
theorem phaseLabel_graph_vertexTransitive
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C) :
    IntervalIntersectionGraphVertexTransitive
      (labelledPhaseInterval P Q L C) := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  obtain ⟨hPauto, hQauto⟩ :=
    phaseLabel_graph_automorphisms hL C hcomm hPperiodic hQperiodic
  intro u v
  let δP : ZMod L := v.1 - u.1
  let δQ : ZMod L := v.2 - u.2
  let eP := equivIterate (phaseShiftP L) δP.val
  let eQ := equivIterate (phaseShiftQ L) δQ.val
  refine ⟨eP.trans eQ, ?_, ?_⟩
  · exact graphAutomorphism_trans _ eP eQ
      (graphAutomorphism_equivIterate _ _ hPauto δP.val)
      (graphAutomorphism_equivIterate _ _ hQauto δQ.val)
  · rcases u with ⟨uP, uQ⟩
    rcases v with ⟨vP, vQ⟩
    apply Prod.ext
    · simp only [Equiv.trans_apply, eP, eQ,
        phaseShiftP_equivIterate_apply, phaseShiftQ_equivIterate_apply,
        Prod.fst]
      rw [ZMod.natCast_zmod_val]
      simp [δP]
    · simp only [Equiv.trans_apply, eP, eQ,
        phaseShiftP_equivIterate_apply, phaseShiftQ_equivIterate_apply,
        Prod.snd]
      rw [ZMod.natCast_zmod_val]
      simp [δQ]

/-- Continuous images of a nonempty compact interval are nonempty compact
intervals. -/
theorem labelledPhaseIntervals_are_intervals
    {P Q : IntervalMap} {L : ℕ} (C : Set I)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcompact : IsCompact C) (hinterval : Set.OrdConnected C)
    (hnonempty : C.Nonempty) :
    ∀ α : PhaseLabel L,
      IsCompact (labelledPhaseInterval P Q L C α) ∧
        Set.OrdConnected (labelledPhaseInterval P Q L C α) ∧
        (labelledPhaseInterval P Q L C α).Nonempty := by
  intro α
  have hPi : Continuous (iterateMap P α.1.val) :=
    IntervalMap.continuous_iterate hP α.1.val
  have hQj : Continuous (iterateMap Q α.2.val) :=
    IntervalMap.continuous_iterate hQ α.2.val
  have hcompactQ : IsCompact (iterateMap Q α.2.val '' C) :=
    hcompact.image hQj
  have hcompactPQ :
      IsCompact (iterateMap P α.1.val '' (iterateMap Q α.2.val '' C)) :=
    hcompactQ.image hPi
  have hpreconnected : IsPreconnected C :=
    isPreconnected_iff_ordConnected.mpr hinterval
  have hpreconnectedQ : IsPreconnected (iterateMap Q α.2.val '' C) :=
    hpreconnected.image _ hQj.continuousOn
  have hpreconnectedPQ :
      IsPreconnected (iterateMap P α.1.val '' (iterateMap Q α.2.val '' C)) :=
    hpreconnectedQ.image _ hPi.continuousOn
  have hnonemptyQ : (iterateMap Q α.2.val '' C).Nonempty :=
    hnonempty.image _
  have hnonemptyPQ :
      (iterateMap P α.1.val '' (iterateMap Q α.2.val '' C)).Nonempty :=
    hnonemptyQ.image _
  simpa only [labelledPhaseInterval] using
    ⟨hcompactPQ, isPreconnected_iff_ordConnected.mp hpreconnectedPQ,
      hnonemptyPQ⟩

/-- A finite connected vertex-transitive intersection graph of compact
intervals is complete, and the family has a common point. -/
theorem connected_vertexTransitive_intervalGraph_complete_and_Helly
    {V : Type*} [Fintype V] [Nonempty V] (D : V → Set I)
    (hcompact : ∀ v, IsCompact (D v))
    (hinterval : ∀ v, Set.OrdConnected (D v))
    (hnonempty : ∀ v, (D v).Nonempty)
    (hconnected : IntervalIntersectionGraphConnected D)
    (htransitive : IntervalIntersectionGraphVertexTransitive D) :
    IntervalIntersectionGraphComplete D ∧ (⋂ v, D v).Nonempty := by
  classical
  let rightEnd : V → I := fun v => sSup (D v)
  obtain ⟨v₀, _hv₀, hmin⟩ := Finset.exists_min_image Finset.univ rightEnd
    (show (Finset.univ : Finset V).Nonempty from Finset.univ_nonempty)
  have hright_mem (v : V) : rightEnd v ∈ D v := by
    dsimp [rightEnd]
    exact (hcompact v).sSup_mem (hnonempty v)
  have hle_right (v : V) {x : I} (hx : x ∈ D v) : x ≤ rightEnd v :=
    ((hcompact v).isGreatest_sSup (hnonempty v)).2 hx
  have hadj_symm {u v : V}
      (h : intervalIntersectionAdjacent D u v) :
      intervalIntersectionAdjacent D v u := by
    refine ⟨h.1.symm, ?_⟩
    simpa [Set.inter_comm] using h.2
  have hneighbor_mem (u : V)
      (hu : u = v₀ ∨ intervalIntersectionAdjacent D v₀ u) :
      rightEnd v₀ ∈ D u := by
    rcases hu with rfl | hu
    · exact hright_mem u
    · obtain ⟨x, hxv₀, hxu⟩ := hu.2
      have hx_le : x ≤ rightEnd v₀ := hle_right v₀ hxv₀
      have hright_le : rightEnd v₀ ≤ rightEnd u :=
        hmin u (Finset.mem_univ u)
      exact (Set.ordConnected_iff.mp (hinterval u)
        x hxu (rightEnd u) (hright_mem u) (hx_le.trans hright_le))
        ⟨hx_le, hright_le⟩
  have hlocal₀ (u w : V)
      (hu : u = v₀ ∨ intervalIntersectionAdjacent D v₀ u)
      (hw : w = v₀ ∨ intervalIntersectionAdjacent D v₀ w)
      (huw : u ≠ w) : intervalIntersectionAdjacent D u w := by
    exact ⟨huw, ⟨rightEnd v₀, hneighbor_mem u hu, hneighbor_mem w hw⟩⟩
  have hlocal (v u w : V)
      (hu : u = v ∨ intervalIntersectionAdjacent D v u)
      (hw : w = v ∨ intervalIntersectionAdjacent D v w)
      (huw : u ≠ w) : intervalIntersectionAdjacent D u w := by
    obtain ⟨e, he, hev⟩ := htransitive v₀ v
    let u' : V := e.symm u
    let w' : V := e.symm w
    have hu' : u' = v₀ ∨ intervalIntersectionAdjacent D v₀ u' := by
      rcases hu with rfl | hu
      · left
        dsimp [u']
        rw [← hev, e.symm_apply_apply]
      · right
        apply (he v₀ u').mp
        simpa [u', hev] using hu
    have hw' : w' = v₀ ∨ intervalIntersectionAdjacent D v₀ w' := by
      rcases hw with rfl | hw
      · left
        dsimp [w']
        rw [← hev, e.symm_apply_apply]
      · right
        apply (he v₀ w').mp
        simpa [w', hev] using hw
    have huw' : u' ≠ w' := by
      intro h
      apply huw
      have := congrArg e h
      simpa [u', w'] using this
    have h' := hlocal₀ u' w' hu' hw' huw'
    have := (he u' w').mpr h'
    simpa [u', w'] using this
  have hcollapse : ∀ u v : V,
      Relation.ReflTransGen (intervalIntersectionAdjacent D) u v →
        u = v ∨ intervalIntersectionAdjacent D u v := by
    intro u v hpath
    induction hpath with
    | refl => exact Or.inl rfl
    | @tail b c hab hbc ih =>
        rcases ih with hab_eq | hab_adj
        · subst b
          exact Or.inr hbc
        · by_cases hac : u = c
          · exact Or.inl hac
          · exact Or.inr (hlocal b u c
              (Or.inr (hadj_symm hab_adj)) (Or.inr hbc) hac)
  have hcomplete : IntervalIntersectionGraphComplete D := by
    intro u v huv
    rcases hcollapse u v (hconnected u v) with huv' | huv'
    · exact False.elim (huv huv')
    · exact huv'
  refine ⟨hcomplete, ⟨rightEnd v₀, ?_⟩⟩
  rw [Set.mem_iInter]
  intro v
  by_cases hv : v = v₀
  · simpa [hv] using hright_mem v₀
  · exact hneighbor_mem v (Or.inr (hcomplete v₀ v (fun h => hv h.symm)))

/-- In a minimal interval system, a periodic compact interval with connected
phase graph is already the whole ambient interval. -/
theorem periodicInterval_eq_univ_of_connectedPhaseGraph_and_minimalCore
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q)
    (hcompact : IsCompact C) (hord : Set.OrdConnected C)
    (hnonempty : C.Nonempty)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C)
    (hconnected : IntervalIntersectionGraphConnected
      (labelledPhaseInterval P Q L C))
    (hminimal : ∀ J : ClosedSubinterval,
      IsCommonInvariantCore P Q J → J.carrier = Set.univ) :
    C = Set.univ := by
  let D := labelledPhaseInterval P Q L C
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hD : ∀ α : PhaseLabel L,
      IsCompact (D α) ∧ Set.OrdConnected (D α) ∧ (D α).Nonempty :=
    labelledPhaseIntervals_are_intervals C hP hQ hcompact hord hnonempty
  have htransitive : IntervalIntersectionGraphVertexTransitive D :=
    phaseLabel_graph_vertexTransitive hL C hcomm hPperiodic hQperiodic
  have hHelly := connected_vertexTransitive_intervalGraph_complete_and_Helly
    D (fun α => (hD α).1) (fun α => (hD α).2.1)
      (fun α => (hD α).2.2) hconnected htransitive
  let core : Set I := labelledPhaseCore P Q L C
  have hcoreNonempty : core.Nonempty := by
    change (⋂ α : PhaseLabel L, D α).Nonempty
    exact hHelly.2
  have hcoreCompact : IsCompact core := by
    have hclosed : IsClosed core := by
      dsimp [core, labelledPhaseCore]
      exact isClosed_iInter (fun α => (hD α).1.isClosed)
    exact hclosed.isCompact
  have hcoreOrd : Set.OrdConnected core := by
    dsimp [core, labelledPhaseCore]
    exact Set.ordConnected_iInter (fun α => (hD α).2.1)
  have hcoreConnected : IsConnected core :=
    ⟨hcoreNonempty, hcoreOrd.isPreconnected⟩
  have hcoreEq : core = Set.Icc (sInf core) (sSup core) :=
    eq_Icc_of_connected_compact hcoreConnected hcoreCompact
  have hle : sInf core ≤ sSup core := by
    rw [hcoreEq] at hcoreNonempty
    exact Set.nonempty_Icc.mp hcoreNonempty
  let J : ClosedSubinterval :=
    { left := sInf core, right := sSup core, left_le_right := hle }
  have hJcarrier : J.carrier = core := by
    change Set.Icc (sInf core) (sSup core) = core
    exact hcoreEq.symm
  have hPshift := labelledPhaseInterval_shiftP hL C hcomm hPperiodic
  have hQshift := labelledPhaseInterval_shiftQ hL C hcomm hQperiodic
  have hPcore : Set.MapsTo P core core := by
    intro x hx
    rw [show core = ⋂ α, D α by rfl, Set.mem_iInter] at hx ⊢
    intro β
    let α := (phaseShiftP L).symm β
    have himage : P x ∈ P '' D α := ⟨x, hx α, rfl⟩
    have hshift : P '' D α = D (phaseShiftP L α) := by
      simpa [D] using (hPshift α).symm
    rw [hshift] at himage
    simpa [α] using himage
  have hQcore : Set.MapsTo Q core core := by
    intro x hx
    rw [show core = ⋂ α, D α by rfl, Set.mem_iInter] at hx ⊢
    intro β
    let α := (phaseShiftQ L).symm β
    have himage : Q x ∈ Q '' D α := ⟨x, hx α, rfl⟩
    have hshift : Q '' D α = D (phaseShiftQ L α) := by
      simpa [D] using (hQshift α).symm
    rw [hshift] at himage
    simpa [α] using himage
  have hJuniv : J.carrier = Set.univ := by
    apply hminimal J
    constructor
    · intro x hx
      rw [hJcarrier] at hx ⊢
      exact hPcore hx
    · intro x hx
      rw [hJcarrier] at hx ⊢
      exact hQcore hx
  let zeroPhase : PhaseLabel L := (0, 0)
  have hcoreSubset : core ⊆ D zeroPhase := iInter_subset _ zeroPhase
  have hzeroPhase : D zeroPhase = C := by
    simp [D, zeroPhase, labelledPhaseInterval, iterateMap]
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x _hx
  rw [← hzeroPhase]
  apply hcoreSubset
  rw [← hJcarrier, hJuniv]
  exact Set.mem_univ x

/-- A disconnected periodic phase graph gives exactly the finite quotient
used in lexicographic descent: both generators respect it and the square of
the return word has two distinct fixed points in one quotient fibre. -/
theorem disconnectedPhaseGraph_gives_respectedQuotient
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L) (C : Set I)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q)
    (hcompact : IsCompact C) (hord : Set.OrdConnected C)
    (hnonempty : C.Nonempty)
    (hnontrivial : ∃ x ∈ C, ∃ y ∈ C, x ≠ y)
    (hPperiodic : iterateMap P L '' C = C)
    (hQperiodic : iterateMap Q L '' C = C)
    (hgraph : ¬IntervalIntersectionGraphConnected
      (labelledPhaseInterval P Q L C)) :
    ∃ π : CanonicalFiniteIntervalQuotient,
      RespectsFibres π.toFun P ∧
      RespectsFibres π.toFun Q ∧
      IdentifiesDistinctFixedPoints π.toFun
        (iterateMap ((iterateMap P L) ∘ (iterateMap Q L)) 2) := by
  classical
  let D : PhaseLabel L → Set I := labelledPhaseInterval P Q L C
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  have hD : ∀ α : PhaseLabel L,
      IsCompact (D α) ∧ Set.OrdConnected (D α) ∧ (D α).Nonempty :=
    labelledPhaseIntervals_are_intervals C hP hQ hcompact hord hnonempty
  have hDnontrivial : ∀ α : PhaseLabel L,
      ∃ x ∈ D α, ∃ y ∈ D α, x ≠ y :=
    labelledPhaseIntervals_nontrivial hL C hcomm
      hPperiodic hQperiodic hnontrivial
  obtain ⟨classes, hcarrier, hclassesNondegenerate,
      hclassesPairwise, hclassesUnion⟩ :=
    intervalGraph_componentInterval_package D
      (fun α => (hD α).1)
      (fun α => ⟨(hD α).2.2, (hD α).2.1.isPreconnected⟩)
      hDnontrivial
  have hclassesProper : (⋃ c, (classes c).carrier) ≠ Set.univ := by
    rw [hclassesUnion]
    exact intervalGraph_union_ne_univ_of_not_connected D
      (fun α => (hD α).1)
      (fun α => ⟨(hD α).2.2, (hD α).2.1.isPreconnected⟩)
      hDnontrivial hgraph
  obtain ⟨π, hπfibre, _hπcollapsed⟩ :=
    exists_canonicalFiniteIntervalQuotient_of_finiteFamily classes
      hclassesNondegenerate hclassesPairwise hclassesProper
  obtain ⟨hPauto, hQauto⟩ :=
    phaseLabel_graph_automorphisms hL C hcomm hPperiodic hQperiodic
  have hPcomponent : ∀ c, ∃ d,
      MapsTo P (intervalGraphComponentUnion D c)
        (intervalGraphComponentUnion D d) := by
    apply intervalGraph_componentUnion_mapsTo_of_automorphism
      D P (phaseShiftP L) hPauto
    intro α
    exact labelledPhaseInterval_shiftP hL C hcomm hPperiodic α
  have hQcomponent : ∀ c, ∃ d,
      MapsTo Q (intervalGraphComponentUnion D c)
        (intervalGraphComponentUnion D d) := by
    apply intervalGraph_componentUnion_mapsTo_of_automorphism
      D Q (phaseShiftQ L) hQauto
    intro α
    exact labelledPhaseInterval_shiftQ hL C hcomm hQperiodic α
  have hrespectP : RespectsFibres π.toFun P := by
    intro x y hxy
    rcases (hπfibre x y).mp hxy with hxy | ⟨c, hxc, hyc⟩
    · subst y
      rfl
    · obtain ⟨d, hmaps⟩ := hPcomponent c
      apply (hπfibre (P x) (P y)).mpr
      right
      refine ⟨d, ?_, ?_⟩
      · rw [hcarrier d]
        apply hmaps
        rw [← hcarrier c]
        exact hxc
      · rw [hcarrier d]
        apply hmaps
        rw [← hcarrier c]
        exact hyc
  have hrespectQ : RespectsFibres π.toFun Q := by
    intro x y hxy
    rcases (hπfibre x y).mp hxy with hxy | ⟨c, hxc, hyc⟩
    · subst y
      rfl
    · obtain ⟨d, hmaps⟩ := hQcomponent c
      apply (hπfibre (Q x) (Q y)).mpr
      right
      refine ⟨d, ?_, ?_⟩
      · rw [hcarrier d]
        apply hmaps
        rw [← hcarrier c]
        exact hxc
      · rw [hcarrier d]
        apply hmaps
        rw [← hcarrier c]
        exact hyc
  let R : IntervalMap := (iterateMap P L) ∘ (iterateMap Q L)
  have hRcontinuous : Continuous R :=
    (IntervalMap.continuous_iterate hP L).comp
      (IntervalMap.continuous_iterate hQ L)
  have hRclass : ∀ c, R '' (classes c).carrier = (classes c).carrier := by
    intro c
    rw [hcarrier c]
    exact labelledPhaseComponent_returnWord_image C hcomm
      hPperiodic hQperiodic c
  let c₀ : (intervalIntersectionSimpleGraph D).ConnectedComponent :=
    (intervalIntersectionSimpleGraph D).connectedComponentMk (0, 0)
  obtain ⟨x, hxc, y, hyc, hxy, hxS, hyS⟩ :=
    intervalSurjection_square_has_two_fixedPoints R (classes c₀)
      hRcontinuous (hRclass c₀) (hclassesNondegenerate c₀)
  refine ⟨π, hrespectP, hrespectQ, ?_⟩
  exact ⟨x, y, hxS, hyS, hxy,
    (hπfibre x y).mpr (Or.inr ⟨c₀, hxc, hyc⟩)⟩

/-- A proper nondegenerate interval cannot be returned by equal positive
powers when connected phase cores are minimal and disconnected phase
quotients are excluded.  This is the callback-factored form used by the
piecewise-linear least-counterexample layer. -/
theorem proper_powerInvariant_interval_impossible_of_phase_descent
    {P Q : IntervalMap} {L : ℕ} (hL : 0 < L)
    (Omega : ClosedSubinterval)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q)
    (hPperiodic : iterateMap P L '' Omega.carrier = Omega.carrier)
    (hQperiodic : iterateMap Q L '' Omega.carrier = Omega.carrier)
    (hOmegaNondegenerate : Omega.Nondegenerate)
    (hOmegaProper : Omega.carrier ≠ Set.univ)
    (hminimal : ∀ K : ClosedSubinterval,
      IsCommonInvariantCore P Q K → K.carrier = Set.univ)
    (hnoQuotient : ∀ π : CanonicalFiniteIntervalQuotient,
      RespectsFibres π.toFun P → RespectsFibres π.toFun Q →
      IdentifiesDistinctFixedPoints π.toFun
        (iterateMap ((iterateMap P L) ∘ (iterateMap Q L)) 2) → False) :
    False := by
  classical
  let D : PhaseLabel L → Set I :=
    labelledPhaseInterval P Q L Omega.carrier
  by_cases hgraph : IntervalIntersectionGraphConnected D
  · have hOmegaUniv : Omega.carrier = Set.univ :=
      periodicInterval_eq_univ_of_connectedPhaseGraph_and_minimalCore
        hL Omega.carrier hP hQ hcomm isCompact_Icc Set.ordConnected_Icc
          (Set.nonempty_Icc.mpr Omega.left_le_right)
          hPperiodic hQperiodic hgraph hminimal
    exact hOmegaProper hOmegaUniv
  · obtain ⟨π, hrespectP, hrespectQ, hidentified⟩ :=
      disconnectedPhaseGraph_gives_respectedQuotient
        hL Omega.carrier hP hQ hcomm isCompact_Icc Set.ordConnected_Icc
          (Set.nonempty_Icc.mpr Omega.left_le_right)
          ⟨Omega.left, Set.left_mem_Icc.mpr Omega.left_le_right,
            Omega.right, Set.right_mem_Icc.mpr Omega.left_le_right,
            hOmegaNondegenerate.ne⟩
          hPperiodic hQperiodic hgraph
    exact hnoQuotient π hrespectP hrespectQ hidentified

/-- The selected diagonal range fills the interval once the two abstract
least-counterexample consequences are supplied: minimality of invariant
intervals and exclusion of a phase quotient identifying two return-square
fixed points. -/
theorem diagonalRange_iterates_eq_univ_of_phase_descent
    (P Q : IntervalMap) {L : ℕ} (hL : 0 < L)
    (J : ClosedSubinterval) (hJnondegenerate : J.Nondegenerate)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q)
    (hexpandP : J.carrier ⊆ imageInterval (iterateMap P L) J)
    (hexpandQ : J.carrier ⊆ imageInterval (iterateMap Q L) J)
    (hminimal : ∀ K : ClosedSubinterval,
      IsCommonInvariantCore P Q K → K.carrier = Set.univ)
    (hnoQuotient : ∀ π : CanonicalFiniteIntervalQuotient,
      RespectsFibres π.toFun P → RespectsFibres π.toFun Q →
      IdentifiesDistinctFixedPoints π.toFun
        (iterateMap
          ((iterateMap P L) ∘ (iterateMap Q L)) 2) → False) :
    diagonalRange (iterateMap P L) (iterateMap Q L) J = Set.univ := by
  let A : IntervalMap := iterateMap P L
  let B : IntervalMap := iterateMap Q L
  let K : Set I := diagonalRange A B J
  have hA : Continuous A := IntervalMap.continuous_iterate hP L
  have hB : Continuous B := IntervalMap.continuous_iterate hQ L
  have hAB : Commute A B := hcomm.iterate_iterate L L
  have hKpackage : IsCompact K ∧ Set.OrdConnected K ∧ K.Nonempty := by
    exact diagonalRange_interval_package J hA hB hAB hexpandP hexpandQ
  have hinvariant : A '' K = K ∧ B '' K = K := by
    exact diagonalRange_invariant J hA hB hAB hexpandP hexpandQ
  have hJK : J.carrier ⊆ K := by
    intro x hx
    apply subset_closure
    apply Set.mem_iUnion.mpr
    refine ⟨0, ?_⟩
    simpa [K, A, B, diagonalRange, diagonalImage, biIterateImage,
      iterateMap] using hx
  have hKnontrivial : ∃ x ∈ K, ∃ y ∈ K, x ≠ y :=
    ⟨J.left, hJK (Set.left_mem_Icc.mpr J.left_le_right),
      J.right, hJK (Set.right_mem_Icc.mpr J.left_le_right),
      hJnondegenerate.ne⟩
  have hgraph : IntervalIntersectionGraphConnected
      (labelledPhaseInterval P Q L K) := by
    by_contra hdisconnected
    obtain ⟨π, hrespectP, hrespectQ, hidentified⟩ :=
      disconnectedPhaseGraph_gives_respectedQuotient
        hL K hP hQ hcomm hKpackage.1 hKpackage.2.1
          hKpackage.2.2 hKnontrivial (by simpa [A] using hinvariant.1)
          (by simpa [B] using hinvariant.2) hdisconnected
    exact hnoQuotient π hrespectP hrespectQ hidentified
  exact periodicInterval_eq_univ_of_connectedPhaseGraph_and_minimalCore
    hL K hP hQ hcomm hKpackage.1 hKpackage.2.1 hKpackage.2.2
      (by simpa [A] using hinvariant.1)
      (by simpa [B] using hinvariant.2) hgraph hminimal

/-- Dense-union form of the preceding diagonal-range theorem. -/
theorem diagonalIterates_dense_of_phase_descent
    (P Q : IntervalMap) {L : ℕ} (hL : 0 < L)
    (J : ClosedSubinterval) (hJnondegenerate : J.Nondegenerate)
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q)
    (hexpandP : J.carrier ⊆ imageInterval (iterateMap P L) J)
    (hexpandQ : J.carrier ⊆ imageInterval (iterateMap Q L) J)
    (hminimal : ∀ K : ClosedSubinterval,
      IsCommonInvariantCore P Q K → K.carrier = Set.univ)
    (hnoQuotient : ∀ π : CanonicalFiniteIntervalQuotient,
      RespectsFibres π.toFun P → RespectsFibres π.toFun Q →
      IdentifiesDistinctFixedPoints π.toFun
        (iterateMap
          ((iterateMap P L) ∘ (iterateMap Q L)) 2) → False) :
    Dense (⋃ n : ℕ,
      diagonalImage (iterateMap P L) (iterateMap Q L) J n) := by
  apply dense_iff_closure_eq.mpr
  simpa [diagonalRange] using
    diagonalRange_iterates_eq_univ_of_phase_descent
      P Q hL J hJnondegenerate hP hQ hcomm hexpandP hexpandQ
        hminimal hnoQuotient

/-! ## Missing endpoints and singleton fibres -/

/-- A point is one of the two ambient endpoints. -/
def IsAmbientEndpoint (e : I) : Prop :=
  e = leftEndpoint ∨ e = rightEndpoint

/-- An endpoint never occurs in the diagonal image sequence. -/
def EndpointNeverArrives (A B : IntervalMap) (J : ClosedSubinterval)
    (e : I) : Prop :=
  ∀ n : ℕ, e ∉ diagonalImage A B J n

private theorem dense_iUnion_monotone_ordConnected_contains_interior
    (D : ℕ → Set I)
    (hdense : Dense (⋃ n : ℕ, D n))
    (hmono : Monotone D)
    (hinterval : ∀ n, Set.OrdConnected (D n))
    {x : I} (hxleft : x ≠ leftEndpoint)
    (hxright : x ≠ rightEndpoint) :
    ∃ n : ℕ, x ∈ D n := by
  have hleftx : leftEndpoint < x := by
    exact lt_of_le_of_ne
      (show leftEndpoint ≤ x by exact x.property.1) (Ne.symm hxleft)
  have hxright' : x < rightEndpoint := by
    exact lt_of_le_of_ne
      (show x ≤ rightEndpoint by exact x.property.2) hxright
  obtain ⟨y, hyUnion, hyx⟩ :=
    hdense.exists_mem_open isOpen_Iio
      (show (Set.Iio x).Nonempty from ⟨leftEndpoint, hleftx⟩)
  obtain ⟨z, hzUnion, hxz⟩ :=
    hdense.exists_mem_open isOpen_Ioi
      (show (Set.Ioi x).Nonempty from ⟨rightEndpoint, hxright'⟩)
  rcases Set.mem_iUnion.mp hyUnion with ⟨n, hyn⟩
  rcases Set.mem_iUnion.mp hzUnion with ⟨m, hzm⟩
  let N := max n m
  have hyN : y ∈ D N := hmono (Nat.le_max_left n m) hyn
  have hzN : z ∈ D N := hmono (Nat.le_max_right n m) hzm
  exact ⟨N, (hinterval N).out hyN hzN ⟨hyx.le, hxz.le⟩⟩

private theorem diagonalDenseUnion_contains_interior
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hA : Continuous A) (hB : Continuous B)
    (hcomm : Commute A B)
    (hexpandA : J.carrier ⊆ imageInterval A J)
    (hexpandB : J.carrier ⊆ imageInterval B J)
    (hdense : Dense (⋃ n : ℕ, diagonalImage A B J n))
    {x : I} (hxleft : x ≠ leftEndpoint)
    (hxright : x ≠ rightEndpoint) :
    ∃ n : ℕ, x ∈ diagonalImage A B J n :=
  dense_iUnion_monotone_ordConnected_contains_interior
    (fun n => diagonalImage A B J n) hdense
    (diagonalImage_monotone J hcomm hexpandA hexpandB)
    (diagonalImage_ordConnected J hA hB hcomm) hxleft hxright

private theorem diagonalImage_map_product
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hcomm : Commute A B) (n : ℕ) :
    (A ∘ B) '' diagonalImage A B J n =
      diagonalImage A B J (n + 1) := by
  simpa [iterateMap, Nat.add_comm] using
    iterate_product_image_diagonalImage J hcomm 1 n

private theorem diagonalImage_map_productSquare
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hcomm : Commute A B) (n : ℕ) :
    iterateMap (A ∘ B) 2 '' diagonalImage A B J n =
      diagonalImage A B J (n + 2) := by
  simpa [Nat.add_comm] using
    iterate_product_image_diagonalImage J hcomm 2 n

/-- A missing ambient endpoint in a dense expanding diagonal sequence is a
fixed singleton fibre of the product square. -/
theorem endpoint_singletonFibre_of_neverArrives
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hA : Continuous A) (hB : Continuous B)
    (hcomm : Commute A B)
    (hexpandA : J.carrier ⊆ imageInterval A J)
    (hexpandB : J.carrier ⊆ imageInterval B J)
    (hRonto : IsOnto (A ∘ B))
    (hdense : Dense (⋃ n : ℕ, diagonalImage A B J n))
    {e : I} (he : IsAmbientEndpoint e)
    (hnever : EndpointNeverArrives A B J e) :
    IsFixedPoint (iterateMap (A ∘ B) 2) e ∧
      ∀ x : I, iterateMap (A ∘ B) 2 x = e → x = e := by
  let R : IntervalMap := A ∘ B
  let S : IntervalMap := iterateMap R 2
  have hends : leftEndpoint ≠ rightEndpoint := by
    simp [leftEndpoint, rightEndpoint]
  have hInteriorAvoids (t : I) (htnever : EndpointNeverArrives A B J t)
      (x : I) (hxleft : x ≠ leftEndpoint) (hxright : x ≠ rightEndpoint) :
      S x ≠ t := by
    intro hSxt
    obtain ⟨n, hxn⟩ := diagonalDenseUnion_contains_interior J
      hA hB hcomm hexpandA hexpandB hdense hxleft hxright
    have hximage : S x ∈ S '' diagonalImage A B J n := ⟨x, hxn, rfl⟩
    rw [show S '' diagonalImage A B J n =
        diagonalImage A B J (n + 2) by
          exact diagonalImage_map_productSquare J hcomm n,
      hSxt] at hximage
    exact htnever (n + 2) hximage
  have hBothNever
      (hleftNever : EndpointNeverArrives A B J leftEndpoint)
      (hrightNever : EndpointNeverArrives A B J rightEndpoint) :
      (IsFixedPoint S leftEndpoint ∧
          ∀ x : I, S x = leftEndpoint → x = leftEndpoint) ∧
        (IsFixedPoint S rightEndpoint ∧
          ∀ x : I, S x = rightEndpoint → x = rightEndpoint) := by
    have hRavoids (t : I) (htnever : EndpointNeverArrives A B J t)
        (x : I) (hxleft : x ≠ leftEndpoint) (hxright : x ≠ rightEndpoint) :
        R x ≠ t := by
      intro hRxt
      obtain ⟨n, hxn⟩ := diagonalDenseUnion_contains_interior J
        hA hB hcomm hexpandA hexpandB hdense hxleft hxright
      have hximage : R x ∈ R '' diagonalImage A B J n := ⟨x, hxn, rfl⟩
      rw [show R '' diagonalImage A B J n =
          diagonalImage A B J (n + 1) by
            exact diagonalImage_map_product J hcomm n,
        hRxt] at hximage
      exact htnever (n + 1) hximage
    obtain ⟨a, ha⟩ := hRonto leftEndpoint
    obtain ⟨b, hb⟩ := hRonto rightEndpoint
    have haEndpoint : IsAmbientEndpoint a := by
      by_contra haNot
      exact (hRavoids leftEndpoint hleftNever a
        (fun h => haNot (Or.inl h)) (fun h => haNot (Or.inr h))) ha
    have hbEndpoint : IsAmbientEndpoint b := by
      by_contra hbNot
      exact (hRavoids rightEndpoint hrightNever b
        (fun h => hbNot (Or.inl h)) (fun h => hbNot (Or.inr h))) hb
    have hRcases :
        (R leftEndpoint = leftEndpoint ∧ R rightEndpoint = rightEndpoint) ∨
          (R leftEndpoint = rightEndpoint ∧ R rightEndpoint = leftEndpoint) := by
      rcases haEndpoint with haLeft | haRight
      · subst a
        rcases hbEndpoint with hbLeft | hbRight
        · subst b
          exact False.elim (hends (ha.symm.trans hb))
        · subst b
          exact Or.inl ⟨ha, hb⟩
      · subst a
        rcases hbEndpoint with hbLeft | hbRight
        · subst b
          exact Or.inr ⟨hb, ha⟩
        · subst b
          exact False.elim (hends (ha.symm.trans hb))
    have hSleft : S leftEndpoint = leftEndpoint := by
      change R (R leftEndpoint) = leftEndpoint
      rcases hRcases with hRfix | hRswap
      · rw [hRfix.1, hRfix.1]
      · rw [hRswap.1, hRswap.2]
    have hSright : S rightEndpoint = rightEndpoint := by
      change R (R rightEndpoint) = rightEndpoint
      rcases hRcases with hRfix | hRswap
      · rw [hRfix.2, hRfix.2]
      · rw [hRswap.2, hRswap.1]
    have hpreLeft : ∀ x : I, S x = leftEndpoint → x = leftEndpoint := by
      intro x hx
      by_cases hxleft : x = leftEndpoint
      · exact hxleft
      by_cases hxright : x = rightEndpoint
      · subst x
        exact False.elim (hends (hx.symm.trans hSright))
      · exact False.elim (hInteriorAvoids leftEndpoint hleftNever x
          hxleft hxright hx)
    have hpreRight : ∀ x : I, S x = rightEndpoint → x = rightEndpoint := by
      intro x hx
      by_cases hxright : x = rightEndpoint
      · exact hxright
      by_cases hxleft : x = leftEndpoint
      · subst x
        exact False.elim (hends (hSleft.symm.trans hx))
      · exact False.elim (hInteriorAvoids rightEndpoint hrightNever x
          hxleft hxright hx)
    exact ⟨⟨hSleft, hpreLeft⟩, ⟨hSright, hpreRight⟩⟩
  rcases he with rfl | rfl
  · by_cases hrightArrives :
        ∃ n : ℕ, rightEndpoint ∈ diagonalImage A B J n
    · obtain ⟨n, hn⟩ := hrightArrives
      have hrightNotPre : S rightEndpoint ≠ leftEndpoint := by
        intro hS
        have himage : S rightEndpoint ∈ S '' diagonalImage A B J n :=
          ⟨rightEndpoint, hn, rfl⟩
        rw [show S '' diagonalImage A B J n =
            diagonalImage A B J (n + 2) by
              exact diagonalImage_map_productSquare J hcomm n,
          hS] at himage
        exact hnever (n + 2) himage
      have hpre : ∀ x : I, S x = leftEndpoint → x = leftEndpoint := by
        intro x hx
        by_cases hxleft : x = leftEndpoint
        · exact hxleft
        by_cases hxright : x = rightEndpoint
        · subst x
          exact False.elim (hrightNotPre hx)
        · exact False.elim (hInteriorAvoids leftEndpoint hnever x
            hxleft hxright hx)
      have hSonto : IsOnto S := IntervalMap.surjective_iterate hRonto 2
      obtain ⟨x, hx⟩ := hSonto leftEndpoint
      have hxe : x = leftEndpoint := hpre x hx
      subst x
      exact ⟨hx, hpre⟩
    · have hrightNever : EndpointNeverArrives A B J rightEndpoint := by
        intro n hn
        exact hrightArrives ⟨n, hn⟩
      exact (hBothNever hnever hrightNever).1
  · by_cases hleftArrives :
        ∃ n : ℕ, leftEndpoint ∈ diagonalImage A B J n
    · obtain ⟨n, hn⟩ := hleftArrives
      have hleftNotPre : S leftEndpoint ≠ rightEndpoint := by
        intro hS
        have himage : S leftEndpoint ∈ S '' diagonalImage A B J n :=
          ⟨leftEndpoint, hn, rfl⟩
        rw [show S '' diagonalImage A B J n =
            diagonalImage A B J (n + 2) by
              exact diagonalImage_map_productSquare J hcomm n,
          hS] at himage
        exact hnever (n + 2) himage
      have hpre : ∀ x : I, S x = rightEndpoint → x = rightEndpoint := by
        intro x hx
        by_cases hxright : x = rightEndpoint
        · exact hxright
        by_cases hxleft : x = leftEndpoint
        · subst x
          exact False.elim (hleftNotPre hx)
        · exact False.elim (hInteriorAvoids rightEndpoint hnever x
            hxleft hxright hx)
      have hSonto : IsOnto S := IntervalMap.surjective_iterate hRonto 2
      obtain ⟨x, hx⟩ := hSonto rightEndpoint
      have hxe : x = rightEndpoint := hpre x hx
      subst x
      exact ⟨hx, hpre⟩
    · have hleftNever : EndpointNeverArrives A B J leftEndpoint := by
        intro n hn
        exact hleftArrives ⟨n, hn⟩
      exact (hBothNever hleftNever hnever).2

/-- If both endpoints do not arrive in finite time, one missing endpoint is
a fixed singleton fibre of the return square. -/
theorem asymptoticEndpoint_singletonFibre
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hA : Continuous A) (hB : Continuous B)
    (hcomm : Commute A B)
    (hexpandA : J.carrier ⊆ imageInterval A J)
    (hexpandB : J.carrier ⊆ imageInterval B J)
    (hRonto : IsOnto (A ∘ B))
    (hdense : Dense (⋃ n : ℕ, diagonalImage A B J n))
    (hnot : ¬∃ n0 n1 : ℕ,
      leftEndpoint ∈ diagonalImage A B J n0 ∧
        rightEndpoint ∈ diagonalImage A B J n1) :
    (IsFixedPoint (iterateMap (A ∘ B) 2) leftEndpoint ∧
        ∀ x : I, iterateMap (A ∘ B) 2 x = leftEndpoint →
          x = leftEndpoint) ∨
      (IsFixedPoint (iterateMap (A ∘ B) 2) rightEndpoint ∧
        ∀ x : I, iterateMap (A ∘ B) 2 x = rightEndpoint →
          x = rightEndpoint) := by
  by_cases hleft : ∃ n, leftEndpoint ∈ diagonalImage A B J n
  · right
    have hrightNever : EndpointNeverArrives A B J rightEndpoint := by
      intro n hn
      obtain ⟨m, hm⟩ := hleft
      exact hnot ⟨m, n, hm, hn⟩
    exact endpoint_singletonFibre_of_neverArrives J hA hB hcomm
      hexpandA hexpandB hRonto hdense (Or.inr rfl) hrightNever
  · left
    have hleftNever : EndpointNeverArrives A B J leftEndpoint := by
      intro n hn
      exact hleft ⟨n, hn⟩
    exact endpoint_singletonFibre_of_neverArrives J hA hB hcomm
      hexpandA hexpandB hRonto hdense (Or.inl rfl) hleftNever

/-- A non-endpoint orbit follows `S`, approaches an endpoint, and moves
strictly closer at every step. -/
def EndpointApproachSequence (S : IntervalMap) (e : I) : Prop :=
  ∃ u : ℕ → I,
    (∀ n, u n ≠ e) ∧
      Tendsto u atTop (nhds e) ∧
      (∀ n, S (u n) = u (n + 1)) ∧
      ∀ n, dist (u (n + 1)) e < dist (u n) e

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

private theorem singleton_left_fibre_preimages_near
    {S : IntervalMap} (hcont : Continuous S)
    (hfibre : S ⁻¹' {leftEndpoint} = {leftEndpoint})
    {q : I} (hq : leftEndpoint < q) :
    ∃ r : I, leftEndpoint < r ∧
      ∀ x : I, S x < r → x < q := by
  let K : Set I := Set.Ici q
  have hKcompact : IsCompact K := isClosed_Ici.isCompact
  have hKne : K.Nonempty := ⟨rightEndpoint, q.property.2⟩
  have himageCompact : IsCompact (S '' K) := hKcompact.image hcont
  have himageNe : (S '' K).Nonempty := hKne.image S
  obtain ⟨m, hm_mem, hm_le⟩ := himageCompact.exists_isLeast himageNe
  have hleft_lt_m : leftEndpoint < m := by
    apply lt_of_le_of_ne m.property.1
    intro hm
    have hme : m = leftEndpoint := by
      apply Subtype.ext
      change (m : ℝ) = 0
      exact hm.symm
    subst m
    rcases hm_mem with ⟨x, hxq, hxS⟩
    have hxpre : x ∈ S ⁻¹' {leftEndpoint} := by simpa using hxS
    rw [hfibre] at hxpre
    have hxe : x = leftEndpoint := by simpa using hxpre
    subst x
    exact (not_le_of_gt hq) hxq
  obtain ⟨r, hlr, hrm⟩ := exists_between hleft_lt_m
  refine ⟨r, hlr, ?_⟩
  intro x hSxr
  by_contra hxq
  have hxK : x ∈ K := le_of_not_gt hxq
  have hmSx : m ≤ S x := hm_le ⟨x, hxK, rfl⟩
  exact (not_lt_of_ge hmSx) (hSxr.trans hrm)

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

/-- A compact increasing family exhausting a dense set and avoiding the left
endpoint supplies a strictly approaching orbit for a singleton-fibre map. -/
theorem endpointApproachSequence_left_of_exhaustion
    {S : IntervalMap} (hcont : Continuous S)
    (hfinite : (fixedPoints S).Finite)
    (hfibre : S ⁻¹' {leftEndpoint} = {leftEndpoint})
    (D : ℕ → Set I)
    (hcompact : ∀ n, IsCompact (D n))
    (hne : ∀ n, (D n).Nonempty)
    (hmono : Monotone D)
    (hmap : ∀ n, S '' D n = D (n + 2))
    (hnever : ∀ n, leftEndpoint ∉ D n)
    (hdense : Dense (⋃ n, D n)) :
    EndpointApproachSequence S leftEndpoint := by
  obtain ⟨q, hleftq, hnofix⟩ :=
    exists_fixed_free_right_neighborhood hfinite
  have hsign := fixed_free_sign_dichotomy hcont hnofix
  have hmove : ∀ x ∈ Set.Ioo leftEndpoint q, S x < x := by
    rcases hsign with htoward | haway
    · exact htoward
    · exfalso
      obtain ⟨r, hleftr, hpre⟩ :=
        singleton_left_fibre_preimages_near hcont hfibre hleftq
      obtain ⟨y, hyUnion, hyr⟩ := hdense.exists_mem_open isOpen_Ioo
        (Set.nonempty_Ioo.mpr hleftr)
      rcases Set.mem_iUnion.mp hyUnion with ⟨n, hyn⟩
      have hyn2 : y ∈ D (n + 2) := hmono (by omega) hyn
      obtain ⟨z, hzmem, hzleast⟩ :=
        (hcompact (n + 2)).exists_isLeast (hne (n + 2))
      have hzlt : z < r := (hzleast hyn2).trans_lt hyr.2
      have hzimage : z ∈ S '' D n := by rw [hmap n]; exact hzmem
      rcases hzimage with ⟨x, hxn, hSxz⟩
      have hxq : x < q := hpre x (hSxz.trans_lt hzlt)
      have hxleft : leftEndpoint < x :=
        lt_of_le_of_ne x.property.1 (fun h => hnever n (h ▸ hxn))
      have hxlocal : x ∈ Set.Ioo leftEndpoint q := ⟨hxleft, hxq⟩
      have hxn2 : x ∈ D (n + 2) := hmono (by omega) hxn
      have hzx : z ≤ x := hzleast hxn2
      exact (not_lt_of_ge hzx) (hSxz ▸ haway x hxlocal)
  obtain ⟨u0, hu0left, hu0q⟩ := exists_between hleftq
  let u : ℕ → I := fun n => iterateMap S n u0
  have hstepEq : ∀ n, S (u n) = u (n + 1) := by
    intro n
    simp only [u, iterateMap, Function.iterate_succ_apply']
  have huLocal : ∀ n, u n ∈ Set.Ioo leftEndpoint q := by
    intro n
    induction n with
    | zero => exact ⟨hu0left, hu0q⟩
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
  have hanti : Antitone u := antitone_nat_of_succ_le fun n => (hstep n).le
  let l : I := ⨅ n, u n
  have htend : Tendsto u atTop (𝓝 l) := tendsto_atTop_iInf hanti
  have htendShift : Tendsto (fun n => u (n + 1)) atTop (𝓝 l) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have htendS : Tendsto (fun n => S (u n)) atTop (𝓝 (S l)) :=
    hcont.continuousAt.tendsto.comp htend
  have hfixedl : S l = l := by
    apply tendsto_nhds_unique htendS
    simpa only [hstepEq] using htendShift
  have hlq : l < q := (iInf_le u 0).trans_lt (huLocal 0).2
  have hleq : l = leftEndpoint := by
    apply le_antisymm
    · by_contra hnot
      have hleftl : leftEndpoint < l := lt_of_not_ge hnot
      exact (ne_of_lt (hmove l ⟨hleftl, hlq⟩)) hfixedl
    · exact l.property.1
  refine ⟨u, ?_, ?_, hstepEq, ?_⟩
  · intro n hnep
    exact (huLocal n).1.ne' hnep
  · simpa [hleq] using htend
  · intro n
    rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
    change |(u (n + 1) : ℝ) - 0| < |(u n : ℝ) - 0|
    simpa only [sub_zero, abs_of_nonneg (u (n + 1)).property.1,
      abs_of_nonneg (u n).property.1] using hstep n

/-! ## Singleton-fibre factorization at an ambient endpoint -/

/-- A fixed singleton fibre of a commuting product factors into singleton
fibres for both factors. -/
theorem singleton_fibre_factorization {U V : IntervalMap} {e : I}
    (hUonto : IsOnto U) (hVonto : IsOnto V)
    (hcomm : Commute U V)
    (hfixed : IsFixedPoint (U ∘ V) e)
    (hfibre : (U ∘ V) ⁻¹' {e} = {e}) :
    U ⁻¹' {e} = {V e} ∧
      V ⁻¹' {e} = {U e} ∧
      U ⁻¹' {U e} = {e} ∧
      V ⁻¹' {V e} = {e} := by
  have hUV : U (V e) = e := by
    simpa [IsFixedPoint, Function.comp_apply] using hfixed
  have hVU : V (U e) = e := by
    rw [← hcomm.eq e, hUV]
  have hUe : U ⁻¹' {e} = {V e} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hVonto x
      have hy : y ∈ (U ∘ V) ⁻¹' {e} := by
        simpa [Function.comp_apply] using hx
      have : y = e := by
        simpa [hfibre] using hy
      simpa [this]
    · rintro rfl
      exact hUV
  have hVe : V ⁻¹' {e} = {U e} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hUonto x
      have hy : y ∈ (U ∘ V) ⁻¹' {e} := by
        change U (V y) = e
        rw [hcomm.eq y, hx]
      have : y = e := by
        simpa [hfibre] using hy
      simpa [this]
    · rintro rfl
      exact hVU
  refine ⟨hUe, hVe, ?_, ?_⟩
  · ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hVx : V (U x) = V (U e) := congrArg V hx
      rw [← hcomm.eq x, hVU] at hVx
      have hx' : x ∈ (U ∘ V) ⁻¹' {e} := by
        simpa [Function.comp_apply] using hVx
      simpa [hfibre] using hx'
    · rintro rfl
      rfl
  · ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hUx : U (V x) = U (V e) := congrArg U hx
      rw [hUV] at hUx
      have hx' : x ∈ (U ∘ V) ⁻¹' {e} := by
        simpa [Function.comp_apply] using hUx
      simpa [hfibre] using hx'
    · rintro rfl
      rfl

/-- For a continuous onto interval map, if a value has an ambient endpoint
as its unique preimage, then that value is itself an ambient endpoint. -/
theorem unique_endpoint_preimage_forces_endpoint_value
    {T : IntervalMap} {e : I}
    (hcont : Continuous T) (honto : IsOnto T)
    (he : IsAmbientEndpoint e)
    (hunique : T ⁻¹' {T e} = {e}) :
    IsAmbientEndpoint (T e) := by
  by_contra hnotEndpoint
  have hnotLeft : T e ≠ leftEndpoint := by
    intro h
    exact hnotEndpoint (Or.inl h)
  have hnotRight : T e ≠ rightEndpoint := by
    intro h
    exact hnotEndpoint (Or.inr h)
  obtain ⟨a, ha⟩ := honto leftEndpoint
  obtain ⟨b, hb⟩ := honto rightEndpoint
  have hae : a ≠ e := by
    intro hae
    apply hnotLeft
    simpa [hae] using ha
  have hbe : b ≠ e := by
    intro hbe
    apply hnotRight
    simpa [hbe] using hb
  have hTe_mem : T e ∈ Set.uIcc (T a) (T b) := by
    rw [ha, hb]
    have hends : leftEndpoint ≤ rightEndpoint := by
      simp [leftEndpoint, rightEndpoint]
    rw [Set.uIcc_of_le hends]
    exact ⟨(T e).property.1, (T e).property.2⟩
  obtain ⟨x, hxab, hx⟩ :=
    intermediate_value_uIcc hcont.continuousOn hTe_mem
  have hxe : x = e := by
    have hxpre : x ∈ T ⁻¹' {T e} := by
      simpa using hx
    rw [hunique] at hxpre
    simpa using hxpre
  subst x
  rcases he with rfl | rfl
  · have hleft_a : leftEndpoint < a := by
      apply lt_of_le_of_ne
      · exact a.property.1
      · exact Ne.symm hae
    have hleft_b : leftEndpoint < b := by
      apply lt_of_le_of_ne
      · exact b.property.1
      · exact Ne.symm hbe
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hxab
      exact (not_le_of_gt hleft_a) hxab.1
    · rw [Set.uIcc_of_ge hba] at hxab
      exact (not_le_of_gt hleft_b) hxab.1
  · have ha_right : a < rightEndpoint := by
      apply lt_of_le_of_ne
      · exact a.property.2
      · exact hae
    have hb_right : b < rightEndpoint := by
      apply lt_of_le_of_ne
      · exact b.property.2
      · exact hbe
    rcases le_total a b with hab | hba
    · rw [Set.uIcc_of_le hab] at hxab
      exact (not_le_of_gt hb_right) hxab.2
    · rw [Set.uIcc_of_ge hba] at hxab
      exact (not_le_of_gt ha_right) hxab.2

/-- The factorization data force both factors to send the exceptional
endpoint to an ambient endpoint. -/
theorem singleton_fibre_factorization_endpoint_actions
    {U V : IntervalMap} {e : I}
    (hUcont : Continuous U) (hVcont : Continuous V)
    (hUonto : IsOnto U) (hVonto : IsOnto V)
    (hcomm : Commute U V) (he : IsAmbientEndpoint e)
    (hfixed : IsFixedPoint (U ∘ V) e)
    (hfibre : (U ∘ V) ⁻¹' {e} = {e}) :
    IsAmbientEndpoint (U e) ∧ IsAmbientEndpoint (V e) := by
  obtain ⟨_, _, hUfibre, hVfibre⟩ :=
    singleton_fibre_factorization hUonto hVonto hcomm hfixed hfibre
  exact ⟨
    unique_endpoint_preimage_forces_endpoint_value hUcont hUonto he hUfibre,
    unique_endpoint_preimage_forces_endpoint_value hVcont hVonto he hVfibre⟩

private theorem ambientEndpoint_eq_of_ne
    {e x y : I} (he : IsAmbientEndpoint e)
    (hx : IsAmbientEndpoint x) (hy : IsAmbientEndpoint y)
    (hxe : x ≠ e) (hye : y ≠ e) :
    x = y := by
  rcases he with rfl | rfl
  · rcases hx with rfl | rfl
    · exact (hxe rfl).elim
    · rcases hy with rfl | rfl
      · exact (hye rfl).elim
      · rfl
  · rcases hx with rfl | rfl
    · rcases hy with rfl | rfl
      · rfl
      · exact (hye rfl).elim
    · exact (hxe rfl).elim

/-- If a commuting factorization has a fixed singleton fibre at an ambient
endpoint, then every even iterate of either factor returns that endpoint. -/
theorem even_iterate_fixes_singleton_fibre_endpoint_factor
    {U V S : IntervalMap} {e : I}
    (he : IsAmbientEndpoint e)
    (hUcont : Continuous U) (hVcont : Continuous V)
    (hUonto : IsOnto U) (hVonto : IsOnto V)
    (hcomm : Commute U V) (hfactor : U ∘ V = S)
    (hfixed : IsFixedPoint S e)
    (hfibre : S ⁻¹' {e} = {e}) (k : ℕ) :
    IsFixedPoint (iterateMap U (2 * k)) e := by
  have hfixedUV : IsFixedPoint (U ∘ V) e := by
    rw [hfactor]
    exact hfixed
  have hfibreUV : (U ∘ V) ⁻¹' {e} = {e} := by
    rw [hfactor]
    exact hfibre
  obtain ⟨_, _, _hUself, _⟩ :=
    singleton_fibre_factorization hUonto hVonto hcomm hfixedUV hfibreUV
  obtain ⟨hUendpoint, hVendpoint⟩ :=
    singleton_fibre_factorization_endpoint_actions
      hUcont hVcont hUonto hVonto hcomm he hfixedUV hfibreUV
  have hUV : U (V e) = e := by
    simpa [IsFixedPoint, Function.comp_apply] using hfixedUV
  have hUtwo : U (U e) = e := by
    by_cases hUe : U e = e
    · rw [hUe, hUe]
    · have hVe : V e ≠ e := by
        intro h
        rw [h] at hUV
        exact hUe hUV
      have hsame : U e = V e :=
        ambientEndpoint_eq_of_ne he hUendpoint hVendpoint hUe hVe
      rw [hsame]
      exact hUV
  have htwoFixed : IsFixedPoint (iterateMap U 2) e := by
    exact hUtwo
  simpa only [iterateMap, Function.iterate_mul] using
    (Function.iterate_fixed htwoFixed k)

/-- If `S` is the square of the commuting return word with even exponent
`2k`, then its fixed singleton endpoint is fixed by each returned factor.
This packages the factorization argument used by normalized powers. -/
theorem evenReturnPowers_fix_singletonFibre_endpoint
    {P Q S : IntervalMap} {e : I} (k : ℕ) (hk : 0 < k)
    (hPcont : Continuous P) (hQcont : Continuous Q)
    (hPonto : IsOnto P) (hQonto : IsOnto Q)
    (hcomm : Commute P Q)
    (hSform : S = iterateMap
      ((iterateMap P (2 * k)) ∘ (iterateMap Q (2 * k))) 2)
    (he : IsAmbientEndpoint e)
    (hfixed : IsFixedPoint S e)
    (hfibre : S ⁻¹' {e} = {e}) :
    IsFixedPoint (iterateMap P (2 * k)) e ∧
      IsFixedPoint (iterateMap Q (2 * k)) e := by
  let L : ℕ := 2 * k
  let m : ℕ := L * 2
  have hm : 0 < m := Nat.mul_pos (Nat.mul_pos (by norm_num) hk) (by norm_num)
  have hpred : m - 1 + 1 = m := by omega
  have hSexpanded : S = (P^[m]) ∘ (Q^[m]) := by
    rw [hSform]
    change ((P^[L]) ∘ (Q^[L]))^[2] = (P^[m]) ∘ (Q^[m])
    calc
      ((P^[L]) ∘ (Q^[L]))^[2] =
          (P^[L])^[2] ∘ (Q^[L])^[2] :=
        (hcomm.iterate_iterate L L).comp_iterate 2
      _ = (P^[m]) ∘ (Q^[m]) := by
        apply congrArg₂ (fun F H : IntervalMap => F ∘ H)
        · exact (Function.iterate_mul P L 2).symm
        · exact (Function.iterate_mul Q L 2).symm
  let VP : IntervalMap := (P^[m - 1]) ∘ (Q^[m])
  have hPfactor : P ∘ VP = S := by
    rw [hSexpanded]
    funext x
    change P ((P^[m - 1]) ((Q^[m]) x)) = (P^[m]) ((Q^[m]) x)
    simpa [hpred] using
      (Function.iterate_succ_apply' P (m - 1) ((Q^[m]) x)).symm
  have hPcomm : Commute P VP :=
    (Function.Commute.self_iterate P (m - 1)).comp_right
      (hcomm.iterate_right m)
  have hVPcont : Continuous VP :=
    (hPcont.iterate (m - 1)).comp (hQcont.iterate m)
  have hVPonto : IsOnto VP :=
    (IntervalMap.surjective_iterate hPonto (m - 1)).comp
      (IntervalMap.surjective_iterate hQonto m)
  let VQ : IntervalMap := (Q^[m - 1]) ∘ (P^[m])
  have hQfactor : Q ∘ VQ = S := by
    rw [hSexpanded]
    funext x
    change Q ((Q^[m - 1]) ((P^[m]) x)) = (P^[m]) ((Q^[m]) x)
    calc
      _ = (Q^[m]) ((P^[m]) x) := by
        simpa [hpred] using
          (Function.iterate_succ_apply' Q (m - 1) ((P^[m]) x)).symm
      _ = (P^[m]) ((Q^[m]) x) :=
        ((hcomm.iterate_iterate m m).eq x).symm
  have hQcomm : Commute Q VQ :=
    (Function.Commute.self_iterate Q (m - 1)).comp_right
      (hcomm.symm.iterate_right m)
  have hVQcont : Continuous VQ :=
    (hQcont.iterate (m - 1)).comp (hPcont.iterate m)
  have hVQonto : IsOnto VQ :=
    (IntervalMap.surjective_iterate hQonto (m - 1)).comp
      (IntervalMap.surjective_iterate hPonto m)
  constructor
  · simpa [L] using even_iterate_fixes_singleton_fibre_endpoint_factor
      he hPcont hVPcont hPonto hVPonto hPcomm hPfactor
        hfixed hfibre k
  · simpa [L] using even_iterate_fixes_singleton_fibre_endpoint_factor
      he hQcont hVQcont hQonto hVQonto hQcomm hQfactor
        hfixed hfibre k

/-- Monotonicity combines separate endpoint arrival times into one diagonal
stage covering the whole interval. -/
theorem finiteDiagonalCover_of_endpointArrival
    {A B : IntervalMap} (J : ClosedSubinterval)
    (hA : Continuous A) (hB : Continuous B)
    (hcomm : Commute A B)
    (hexpandA : J.carrier ⊆ imageInterval A J)
    (hexpandB : J.carrier ⊆ imageInterval B J)
    (harrival : ∃ n0 n1 : ℕ,
      leftEndpoint ∈ diagonalImage A B J n0 ∧
        rightEndpoint ∈ diagonalImage A B J n1) :
    ∃ N : ℕ, diagonalImage A B J N = Set.univ := by
  obtain ⟨nLeft, nRight, hnLeft, hnRight⟩ := harrival
  let N := max nLeft nRight
  have hmono : Monotone (fun n => diagonalImage A B J n) :=
    diagonalImage_monotone J hcomm hexpandA hexpandB
  have hleftN : leftEndpoint ∈ diagonalImage A B J N :=
    hmono (Nat.le_max_left _ _) hnLeft
  have hrightN : rightEndpoint ∈ diagonalImage A B J N :=
    hmono (Nat.le_max_right _ _) hnRight
  refine ⟨N, Set.eq_univ_of_forall fun x => ?_⟩
  exact (diagonalImage_ordConnected J hA hB hcomm N).out
    hleftN hrightN ⟨x.property.1, x.property.2⟩

/-! ## Finite cover to local eventual onto -/

/-- A returned cover rules out an ambient right terminal endpoint unless the
selected gap is the whole interval.  The whole-gap case is deliberately
factored as a callback because it is excluded by the directed-state
permutation layer rather than by finite arrival itself. -/
theorem terminalGap_internal_of_finiteReturnCover
    {W R : IntervalMap} {p c : I} (hpc : p < c)
    (hWp : IsFixedPoint W p) (hWc : IsFixedPoint W c)
    (hmove : ∀ x ∈ Set.Ioo p c, x < W x)
    (hcover : ∃ N : ℕ, iterateMap R N '' Set.Icc p c = Set.univ)
    (d : ℕ) (hRW : R = iterateMap W d)
    (hfullGapImpossible : p = leftEndpoint →
      c = rightEndpoint → False) :
    c < rightEndpoint := by
  by_contra hnot
  have hc : c = rightEndpoint :=
    le_antisymm c.property.2 (le_of_not_gt hnot)
  by_cases hp : p = leftEndpoint
  · exact (hfullGapImpossible hp hc).elim
  · have hleftp : leftEndpoint < p :=
      lt_of_le_of_ne p.property.1 (Ne.symm hp)
    have hWge : ∀ x : I, p ≤ x → x ≤ W x := by
      intro x hpx
      by_cases hxp : x = p
      · rw [hxp, hWp]
      by_cases hxc : x = c
      · rw [hxc, hWc]
      have hxc_le : x ≤ c := by
        rw [hc]
        exact x.property.2
      exact (hmove x
        ⟨lt_of_le_of_ne hpx (Ne.symm hxp),
          lt_of_le_of_ne hxc_le hxc⟩).le
    have hWiterateGe : ∀ n : ℕ, ∀ x : I, p ≤ x →
        x ≤ iterateMap W n x := by
      intro n
      induction n with
      | zero =>
          intro x _
          exact le_rfl
      | succ n ih =>
          intro x hx
          have hxn := ih x hx
          have hstep := hWge (iterateMap W n x) (hx.trans hxn)
          exact hxn.trans (by
            simpa only [iterateMap, Function.iterate_succ_apply'] using hstep)
    have hRge : ∀ x : I, p ≤ x → x ≤ R x := by
      intro x hx
      rw [hRW]
      exact hWiterateGe d x hx
    have hRiterateGe : ∀ n : ℕ, ∀ x : I, p ≤ x →
        x ≤ iterateMap R n x := by
      intro n
      induction n with
      | zero =>
          intro x _
          exact le_rfl
      | succ n ih =>
          intro x hx
          have hxn := ih x hx
          have hstep := hRge (iterateMap R n x) (hx.trans hxn)
          exact hxn.trans (by
            simpa only [iterateMap, Function.iterate_succ_apply'] using hstep)
    obtain ⟨N, hN⟩ := hcover
    have hleftImage : leftEndpoint ∈
        iterateMap R N '' Set.Icc p c := by
      rw [hN]
      exact Set.mem_univ _
    obtain ⟨z, hz, hRz⟩ := hleftImage
    have hzle : z ≤ leftEndpoint :=
      (hRiterateGe N z hz.1).trans_eq hRz
    exact (not_le_of_gt hleftp) (hz.1.trans hzle)

private theorem iterate_reaches_threshold_in_repelling_gap
    {W : IntervalMap} {p c q r : I}
    (hcont : Continuous W) (hpq : p < q) (hrc : r < c)
    (hmove : ∀ x ∈ Set.Ioo p c, x < W x) :
    ∃ j : ℕ, r ≤ iterateMap W j q := by
  by_contra hnot
  push_neg at hnot
  let u : ℕ → I := fun n => iterateMap W n q
  have hur : ∀ n, u n < r := by intro n; simpa [u] using hnot n
  have hpu : ∀ n, p < u n := by
    intro n
    induction n with
    | zero => simpa [u, iterateMap] using hpq
    | succ n ih =>
        have hunC : u n < c := (hur n).trans hrc
        have hstep := hmove (u n) ⟨ih, hunC⟩
        change p < W^[Nat.succ n] q
        rw [Function.iterate_succ_apply']
        exact ih.trans hstep
  have hstepEq : ∀ n, W (u n) = u (n + 1) := by
    intro n
    simp only [u, iterateMap, Function.iterate_succ_apply',
      Nat.succ_eq_add_one]
  have hstep : ∀ n, u n < u (n + 1) := by
    intro n
    rw [← hstepEq n]
    exact hmove (u n) ⟨hpu n, (hur n).trans hrc⟩
  have hmono : Monotone u := monotone_nat_of_le_succ fun n => (hstep n).le
  let l : I := ⨆ n, u n
  have htend : Tendsto u atTop (nhds l) := tendsto_atTop_iSup hmono
  have htendShift : Tendsto (fun n => u (n + 1)) atTop (nhds l) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have htendW : Tendsto (fun n => W (u n)) atTop (nhds (W l)) :=
    hcont.continuousAt.tendsto.comp htend
  have hfixed : W l = l := by
    apply tendsto_nhds_unique htendW
    simpa only [hstepEq] using htendShift
  have hql : q ≤ l := le_iSup u 0
  have hpl : p < l := hpq.trans_le hql
  have hlr : l ≤ r := iSup_le fun n => (hur n).le
  have hlc : l < c := hlr.trans_lt hrc
  exact (ne_of_lt (hmove l ⟨hpl, hlc⟩)) hfixed.symm

/-- A finite cover by a returned word which is a power of a repelling word
gives local eventual onto on every selected-side closed interval. -/
theorem localEventualOnto_of_finiteReturnCover
    {W R : IntervalMap} {p c : I} (hpc : p < c)
    (hW : Continuous W) (hR : Continuous R)
    (hWp : IsFixedPoint W p)
    (hRc : IsFixedPoint R c)
    (hmove : ∀ x ∈ Set.Ioo p c, x < W x)
    (hc : c < rightEndpoint)
    (hcover : ∃ N : ℕ, iterateMap R N '' Set.Icc p c = Set.univ)
    (d : ℕ) (hRW : R = iterateMap W d) :
    ∀ q : I, p < q →
      ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ := by
  intro q hpq
  obtain ⟨N, hN⟩ := hcover
  have hleftMem : leftEndpoint ∈ iterateMap R N '' Set.Icc p c := by
    rw [hN]
    exact Set.mem_univ _
  have hrightMem : rightEndpoint ∈ iterateMap R N '' Set.Icc p c := by
    rw [hN]
    exact Set.mem_univ _
  rcases hleftMem with ⟨xL, hxLgap, hxL⟩
  rcases hrightMem with ⟨xR, hxRgap, hxR⟩
  have hRNc : iterateMap R N c = c := Function.IsFixedPt.iterate hRc N
  have hxLc : xL < c := by
    exact lt_of_le_of_ne hxLgap.2 fun heq => by
      subst xL
      rw [hRNc] at hxL
      have hcpos : leftEndpoint < c :=
        lt_of_le_of_lt p.property.1 hpc
      exact hcpos.ne hxL.symm
  have hxRc : xR < c := by
    exact lt_of_le_of_ne hxRgap.2 fun heq => by
      subst xR
      rw [hRNc] at hxR
      exact hc.ne hxR
  let r : I := max xL xR
  have hrc : r < c := max_lt hxLc hxRc
  obtain ⟨j, hj⟩ :=
    iterate_reaches_threshold_in_repelling_gap hW hpq hrc hmove
  have hWjp : iterateMap W j p = p := Function.IsFixedPt.iterate hWp j
  have hsmall : Set.Icc p r ⊆ iterateMap W j '' Set.Icc p q := by
    intro x hx
    have hxbetween : x ∈ Set.Icc (iterateMap W j p) (iterateMap W j q) := by
      rw [hWjp]
      exact ⟨hx.1, hx.2.trans hj⟩
    exact intermediate_value_Icc hpq.le
      (IntervalMap.continuous_iterate hW j).continuousOn hxbetween
  have hxLr : xL ∈ Set.Icc p r := ⟨hxLgap.1, le_max_left _ _⟩
  have hxRr : xR ∈ Set.Icc p r := ⟨hxRgap.1, le_max_right _ _⟩
  have hpow : iterateMap W (d * N) = iterateMap R N := by
    rw [hRW]
    change W^[d * N] = (W^[d])^[N]
    exact Function.iterate_mul W d N
  refine ⟨d * N + j, Set.eq_univ_of_forall fun y => ?_⟩
  have hybetween : y ∈
      Set.uIcc (iterateMap R N xL) (iterateMap R N xR) := by
    rw [hxL, hxR]
    exact Set.mem_uIcc_of_le y.property.1 y.property.2
  obtain ⟨x, hxbetween, hRx⟩ := intermediate_value_uIcc
    (IntervalMap.continuous_iterate hR N).continuousOn hybetween
  have hxr : x ∈ Set.Icc p r := by
    rcases le_total xL xR with hLR | hRL
    · exact Set.ordConnected_Icc.out hxLr hxRr
        (by simpa only [Set.uIcc_of_le hLR] using hxbetween)
    · exact Set.ordConnected_Icc.out hxRr hxLr
        (by simpa only [Set.uIcc_of_ge hRL] using hxbetween)
  obtain ⟨z, hzsmall, hWz⟩ := hsmall hxr
  refine ⟨z, hzsmall, ?_⟩
  change W^[d * N + j] z = y
  rw [Function.iterate_add_apply]
  calc
    W^[d * N] (W^[j] z) = W^[d * N] x := congrArg _ hWz
    _ = R^[N] x := congrFun hpow x
    _ = y := hRx

/-! ## Endpoint partition lemma -/

theorem RealPartition.exists_adjacent_right_b5
    (partition : RealPartition) {x : ℝ}
    (hxI : x ∈ I) (hxright : x < 1) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ a ≤ x ∧ x < b := by
  classical
  let lower := partition.points.filter fun z => z ≤ x
  let upper := partition.points.filter fun z => x < z
  have hlower : lower.Nonempty := by
    exact ⟨0, by simp [lower, partition.zero_mem, hxI.1]⟩
  have hupper : upper.Nonempty := by
    exact ⟨1, by simp [upper, partition.one_mem, hxright]⟩
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

theorem RealPartition.exists_adjacent_left_b5
    (partition : RealPartition) {x : ℝ}
    (hxI : x ∈ I) (hxleft : 0 < x) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ a < x ∧ x ≤ b := by
  classical
  let lower := partition.points.filter fun z => z < x
  let upper := partition.points.filter fun z => x ≤ z
  have hlower : lower.Nonempty := by
    exact ⟨0, by simp [lower, partition.zero_mem, hxleft]⟩
  have hupper : upper.Nonempty := by
    exact ⟨1, by simp [upper, partition.one_mem, hxI.2]⟩
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨a, b, ⟨ha'.1, hb'.1, ha'.2.trans_le hb'.2, ?_⟩,
    ha'.2, hb'.2⟩
  intro z hz hzb
  by_cases hzx : z < x
  · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzx⟩
    have hza : z ≤ a := by simpa using hamax z hzlower
    exact (not_lt_of_ge hza) hzb.1
  · have hxz : x ≤ z := le_of_not_gt hzx
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hxz⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzb.2

/-- A finite-piece PL map with a singleton left-endpoint fibre is strictly
increasing on its first partition cell. -/
theorem finitePiecePL_singleton_leftEndpointFibre_local_strictMono
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hfixed : IsFixedPoint T leftEndpoint)
    (hfibre : T ⁻¹' {leftEndpoint} = {leftEndpoint}) :
    ∃ q : I, leftEndpoint < q ∧ StrictMonoOn T (Set.Iio q) := by
  rcases hT.2 with ⟨partition, hpartition⟩
  obtain ⟨a, b, hab, ha0, h0b⟩ :=
    PLFiniteArrivalSupport.RealPartition.exists_adjacent_right_b5 partition
      (show (0 : ℝ) ∈ I by constructor <;> norm_num) (by norm_num)
  have haI : a ∈ I := partition.points_subset hab.1
  have hbI : b ∈ I := partition.points_subset hab.2.1
  have ha : a = 0 := le_antisymm ha0 haI.1
  subst a
  let q : I := ⟨b, hbI⟩
  have hleftq : leftEndpoint < q := by
    change (0 : ℝ) < b
    exact h0b
  obtain ⟨m, d, hformula⟩ := hpartition hab
  have hleftCell : leftEndpoint ∈ intervalCell 0 b := by
    exact ⟨le_rfl, h0b.le⟩
  have hqCell : q ∈ intervalCell 0 b := by
    exact ⟨h0b.le, le_rfl⟩
  have hformulaLeft := hformula leftEndpoint hleftCell
  have hformulaQ := hformula q hqCell
  have hfixed' : T leftEndpoint = leftEndpoint := hfixed
  have hd : d = 0 := by
    have hfixedVal := congrArg Subtype.val hfixed'
    change (T leftEndpoint : ℝ) = 0 at hfixedVal
    change (T leftEndpoint : ℝ) = m * 0 + d at hformulaLeft
    linarith
  have hTqne : T q ≠ leftEndpoint := by
    intro hTq
    have hqpre : q ∈ T ⁻¹' {leftEndpoint} := by simpa using hTq
    rw [hfibre] at hqpre
    have hqeq : q = leftEndpoint := by simpa using hqpre
    exact hleftq.ne hqeq.symm
  have hmpos : 0 < m := by
    have hTqnonneg : 0 ≤ (T q : ℝ) := (T q).property.1
    have hmnonneg : 0 ≤ m := by
      rw [hd] at hformulaQ
      change (T q : ℝ) = m * b + 0 at hformulaQ
      nlinarith
    have hmne : m ≠ 0 := by
      intro hm
      apply hTqne
      apply Subtype.ext
      rw [hd, hm] at hformulaQ
      simpa [leftEndpoint] using hformulaQ
    exact lt_of_le_of_ne hmnonneg (Ne.symm hmne)
  refine ⟨q, hleftq, ?_⟩
  intro x hx y hy hxy
  have hxCell : x ∈ intervalCell 0 b :=
    ⟨x.property.1, (show (x : ℝ) < b by simpa [q] using hx).le⟩
  have hyCell : y ∈ intervalCell 0 b :=
    ⟨y.property.1, (show (y : ℝ) < b by simpa [q] using hy).le⟩
  have hxFormula := hformula x hxCell
  have hyFormula := hformula y hyCell
  have hxyReal : (x : ℝ) < (y : ℝ) := hxy
  change (T x : ℝ) < (T y : ℝ)
  rw [hxFormula, hyFormula]
  nlinarith

/-- Right-endpoint form of the finite-PL singleton-fibre lemma. -/
theorem finitePiecePL_singleton_rightEndpointFibre_local_strictMono
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hfixed : IsFixedPoint T rightEndpoint)
    (hfibre : T ⁻¹' {rightEndpoint} = {rightEndpoint}) :
    ∃ q : I, q < rightEndpoint ∧ StrictMonoOn T (Set.Ioi q) := by
  rcases hT.2 with ⟨partition, hpartition⟩
  obtain ⟨a, b, hab, ha1, h1b⟩ :=
    PLFiniteArrivalSupport.RealPartition.exists_adjacent_left_b5 partition
      (show (1 : ℝ) ∈ I by constructor <;> norm_num) (by norm_num)
  have haI : a ∈ I := partition.points_subset hab.1
  have hbI : b ∈ I := partition.points_subset hab.2.1
  have hb : b = 1 := le_antisymm hbI.2 h1b
  subst b
  let q : I := ⟨a, haI⟩
  have hqright : q < rightEndpoint := by
    change a < (1 : ℝ)
    exact ha1
  obtain ⟨m, d, hformula⟩ := hpartition hab
  have hqCell : q ∈ intervalCell a 1 := ⟨le_rfl, ha1.le⟩
  have hrightCell : rightEndpoint ∈ intervalCell a 1 :=
    ⟨ha1.le, le_rfl⟩
  have hformulaQ := hformula q hqCell
  have hformulaRight := hformula rightEndpoint hrightCell
  have hfixed' : T rightEndpoint = rightEndpoint := hfixed
  have hrightVal := congrArg Subtype.val hfixed'
  have hTqne : T q ≠ rightEndpoint := by
    intro hTq
    have hqpre : q ∈ T ⁻¹' {rightEndpoint} := by simpa using hTq
    rw [hfibre] at hqpre
    have hqeq : q = rightEndpoint := by simpa using hqpre
    exact hqright.ne hqeq
  have hmpos : 0 < m := by
    have hTqle : (T q : ℝ) ≤ 1 := (T q).property.2
    have hmnonneg : 0 ≤ m := by
      change (T rightEndpoint : ℝ) = m * 1 + d at hformulaRight
      change (T rightEndpoint : ℝ) = 1 at hrightVal
      change (T q : ℝ) = m * a + d at hformulaQ
      nlinarith
    have hmne : m ≠ 0 := by
      intro hm
      change (T rightEndpoint : ℝ) = m * 1 + d at hformulaRight
      change (T q : ℝ) = m * a + d at hformulaQ
      change (T rightEndpoint : ℝ) = 1 at hrightVal
      rw [hm] at hformulaQ hformulaRight
      have hTqVal : (T q : ℝ) = 1 := by linarith
      apply hTqne
      apply Subtype.ext
      simpa [rightEndpoint] using hTqVal
    exact lt_of_le_of_ne hmnonneg (Ne.symm hmne)
  refine ⟨q, hqright, ?_⟩
  intro x hx y hy hxy
  have hxCell : x ∈ intervalCell a 1 :=
    ⟨(show a < (x : ℝ) by simpa [q] using hx).le, x.property.2⟩
  have hyCell : y ∈ intervalCell a 1 :=
    ⟨(show a < (y : ℝ) by simpa [q] using hy).le, y.property.2⟩
  have hxFormula := hformula x hxCell
  have hyFormula := hformula y hyCell
  have hxyReal : (x : ℝ) < (y : ℝ) := hxy
  change (T x : ℝ) < (T y : ℝ)
  rw [hxFormula, hyFormula]
  nlinarith

end PLFiniteArrivalSupport

end CommutingInterval
