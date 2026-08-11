import CommutingIntervalSimplified.Defs
import CommutingIntervalSimplified.FactorBase
import CommutingIntervalSimplified.FiniteIntervalQuotientConstruction
import CommutingIntervalSimplified.DescendedPL
import CommutingIntervalSimplified.ConstantSlopeDynamics
import CommutingIntervalSimplified.Reduction
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Extremal constant-slope counterexamples

This file is the standalone dependency-ordered skeleton for the manuscript's
extremal irreducibility lemma.  It records the interval-intersection graph,
finite fixed counts, component collapse, restoration of constant slopes,
natural-number minimization, and the factorial-return conclusion without
using any declaration from the earlier formalization.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set

/-! ## The finite interval-intersection graph -/

/-- Two distinct labelled intervals are adjacent when they meet. -/
def intervalIntersectionAdjacent {V : Type*} (D : V → Set I)
    (u v : V) : Prop :=
  u ≠ v ∧ (D u ∩ D v).Nonempty

/-- Connectedness of the labelled interval-intersection graph. -/
def IntervalIntersectionGraphConnected {V : Type*} (D : V → Set I) : Prop :=
  ∀ u v, Relation.ReflTransGen (intervalIntersectionAdjacent D) u v

/-- An equivalence preserving and reflecting interval adjacency. -/
def IsIntervalIntersectionGraphAutomorphism {V : Type*} (D : V → Set I)
    (e : V ≃ V) : Prop :=
  ∀ u v, intervalIntersectionAdjacent D (e u) (e v) ↔
    intervalIntersectionAdjacent D u v

/-- Vertex transitivity of a labelled interval-intersection graph. -/
def IntervalIntersectionGraphVertexTransitive {V : Type*}
    (D : V → Set I) : Prop :=
  ∀ u v, ∃ e : V ≃ V,
    IsIntervalIntersectionGraphAutomorphism D e ∧ e u = v

/-- Completeness of a labelled interval-intersection graph. -/
def IntervalIntersectionGraphComplete {V : Type*} (D : V → Set I) : Prop :=
  ∀ u v, u ≠ v → intervalIntersectionAdjacent D u v

/--
A connected vertex-transitive intersection graph of finitely many nonempty
compact intervals is complete, and all intervals have a common point.
-/
theorem connected_vertexTransitive_intervalFamily_complete_and_Helly
    {V : Type*} [Fintype V] [Nonempty V] (D : V → Set I)
    (hcompact : ∀ v, IsCompact (D v))
    (hinterval : ∀ v, Set.OrdConnected (D v))
    (hnonempty : ∀ v, (D v).Nonempty)
    (hconnected : IntervalIntersectionGraphConnected D)
    (htransitive : IntervalIntersectionGraphVertexTransitive D) :
    IntervalIntersectionGraphComplete D ∧
      (⋂ v, D v).Nonempty := by
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

/-! ## Finite fixed sets and the canonical return exponent -/

/-- The expanding constant-slope product has a finite fixed set. -/
theorem product_fixedPoints_finite
    (C : NormalizedConstantSlopeCounterexample) :
    (fixedPoints C.product).Finite := by
  have hproduct :
      HasConstantAbsoluteSlope C.product (C.scale_P * C.scale_Q) := by
    simpa [NormalizedConstantSlopeCounterexample.product] using
      C.constantSlope_P.comp_of_pos
        (zero_lt_one.trans C.one_lt_scale_Q) C.constantSlope_Q
  have hscale : 1 < C.scale_P * C.scale_Q := by
    nlinarith [C.one_lt_scale_P, C.one_lt_scale_Q]
  exact hproduct.fixedPoints_finite hscale

/-- The product fixed points as a genuine finite set. -/
noncomputable def productFixedFinset
    (C : NormalizedConstantSlopeCounterexample) : Finset I :=
  (product_fixedPoints_finite C).toFinset

@[simp] theorem mem_productFixedFinset
    (C : NormalizedConstantSlopeCounterexample) (x : I) :
    x ∈ productFixedFinset C ↔ IsFixedPoint C.product x := by
  exact (product_fixedPoints_finite C).mem_toFinset

/-- The manuscript's number `ν = # Fix(PQ)`. -/
def productFixedCount (C : NormalizedConstantSlopeCounterexample) : ℕ :=
  (productFixedFinset C).card

/-- The product fixed count is positive. -/
theorem productFixedCount_pos
    (C : NormalizedConstantSlopeCounterexample) :
    0 < productFixedCount C := by
  have hcont : Continuous C.product :=
    C.finitePiece_P.continuous.comp C.finitePiece_Q.continuous
  obtain ⟨x, hx⟩ := IntervalMap.exists_fixedPoint hcont
  exact Finset.card_pos.mpr
    ⟨x, (mem_productFixedFinset C x).mpr hx⟩

/-- The common return exponent `L = (2ν)!`. -/
def extremalReturnExponent
    (C : NormalizedConstantSlopeCounterexample) : ℕ :=
  Nat.factorial (2 * productFixedCount C)

theorem extremalReturnExponent_pos
    (C : NormalizedConstantSlopeCounterexample) :
    0 < extremalReturnExponent C := by
  exact Nat.factorial_pos _

/-- Every positive returned square of an expanding constant-slope generator
has finitely many fixed points. -/
theorem returnedSquare_fixedPoints_finite
    (C : NormalizedConstantSlopeCounterexample) (L : ℕ) (hL : 0 < L) :
    (fixedPoints (iterateMap C.P (2 * L))).Finite := by
  exact C.constantSlope_P.iterateMap_fixedPoints_finite
    C.one_lt_scale_P (2 * L) (by omega)

/-! ## Exact fixed-count descent -/

/-- Exact descent strictly lowers a finite fixed count whenever the factor
identifies two distinct fixed points. -/
theorem fixed_cardinality_strict_of_exact_descent
    (π T Tbar : IntervalMap)
    (hexact : FixedPointsDescendExactly π T Tbar)
    (hidentifies : IdentifiesDistinctFixedPoints π T)
    (hfinite : (fixedPoints T).Finite) :
    (fixedPoints Tbar).Finite ∧
      (fixedPoints Tbar).ncard < (fixedPoints T).ncard := by
  have hdrop := fixedPointCardinalityDrops_of_exact_image
    π T Tbar hexact hidentifies hfinite
  exact ⟨hdrop.2.1, hdrop.2.2⟩

/-! ## The disconnected-component quotient -/

/-- The minimal PL counterexample produced immediately after collapsing the
disconnected phase components. -/
structure MinimalPiecewiseLinearCounterexampleData where
  P : IntervalMap
  Q : IntervalMap
  finitePiece_P : FinitePiecePL P
  finitePiece_Q : FinitePiecePL Q
  onto_P : IsOnto P
  onto_Q : IsOnto Q
  commute : Function.Commute P Q
  no_common_fixed_point : ¬HasCommonFixedPoint P Q
  core_minimal : ∀ J : ClosedSubinterval,
    IsCommonInvariantCore P Q J → J.carrier = Set.univ

/--
The quotient attached to a proper interval invariant under both returned
powers.  Its coordinate collapses two distinct fixed points of `P^(2L)`.
-/
structure PhaseComponentQuotientData
    (C : NormalizedConstantSlopeCounterexample) (L : ℕ) where
  target : MinimalPiecewiseLinearCounterexampleData
  factor : MonotonePairFactor C.P C.Q target.P target.Q
  identifies_returnedSquare :
    IdentifiesDistinctFixedPoints factor.coordinate
      (iterateMap C.P (2 * L))

/-! ### E3a: the finite phase family -/

/-- The manuscript index set `(ℤ/Lℤ)²` for the returned interval family. -/
abbrev PhaseIndex (L : ℕ) := ZMod L × ZMod L

/--
The exact finite phase family generated from a returned interval.  The two
permutations are the cyclic translations induced by `P` and `Q`.
-/
structure PhaseIntervalFamilyData
    (C : NormalizedConstantSlopeCounterexample) (L : ℕ)
    (J : ClosedSubinterval) where
  interval : PhaseIndex L → ClosedSubinterval
  base_carrier : (interval (0, 0)).carrier = J.carrier
  nondegenerate : ∀ i, (interval i).Nondegenerate
  shiftP : Equiv.Perm (PhaseIndex L)
  shiftQ : Equiv.Perm (PhaseIndex L)
  image_P : ∀ i, C.P '' (interval i).carrier = (interval (shiftP i)).carrier
  image_Q : ∀ i, C.Q '' (interval i).carrier = (interval (shiftQ i)).carrier
  graph_vertexTransitive :
    IntervalIntersectionGraphVertexTransitive (fun i => (interval i).carrier)
  intersection_interval :
    (⋂ i, (interval i).carrier).Nonempty →
      ∃ K : ClosedSubinterval,
        K.carrier = ⋂ i, (interval i).carrier

/-- A nonempty compact order-connected subset of `I` is exactly a closed
subinterval. -/
structure CompactIntervalRepresentation (S : Set I) where
  interval : ClosedSubinterval
  carrier_eq : interval.carrier = S

theorem compactIntervalRepresentation_exists
    (S : Set I) (hcompact : IsCompact S)
    (hord : Set.OrdConnected S) (hnonempty : S.Nonempty) :
    Nonempty (CompactIntervalRepresentation S) := by
  have hleft : sInf S ∈ S := hcompact.sInf_mem hnonempty
  have hright : sSup S ∈ S := hcompact.sSup_mem hnonempty
  have hlr : sInf S ≤ sSup S :=
    (hcompact.isLeast_sInf hnonempty).2 hright
  let K : ClosedSubinterval := ⟨sInf S, sSup S, hlr⟩
  have hcarrier : K.carrier = S := by
    apply Set.Subset.antisymm
    · intro x hx
      exact (Set.ordConnected_iff.mp hord
        (sInf S) hleft (sSup S) hright hlr) hx
    · intro x hx
      exact ⟨(hcompact.isLeast_sInf hnonempty).2 hx,
        (hcompact.isGreatest_sSup hnonempty).2 hx⟩
  exact ⟨⟨K, hcarrier⟩⟩

/-- The continuous image of a closed subinterval, represented as a closed
subinterval with the exact image carrier. -/
theorem continuousImageInterval_exists
    (T : IntervalMap) (hT : Continuous T) (J : ClosedSubinterval) :
    ∃ K : ClosedSubinterval, K.carrier = T '' J.carrier := by
  let S : Set I := T '' J.carrier
  have hcompact : IsCompact S := isCompact_Icc.image hT
  have hord : Set.OrdConnected S :=
    (Set.ordConnected_Icc.isPreconnected.image T hT.continuousOn).ordConnected
  have hnonempty : S.Nonempty := J.carrier_nonempty.image T
  obtain ⟨D⟩ := compactIntervalRepresentation_exists S hcompact hord hnonempty
  exact ⟨D.interval, D.carrier_eq⟩

/-- The phase word represented by `(i,j) ∈ (ℤ/Lℤ)²`. -/
def phaseWordMap
    (C : NormalizedConstantSlopeCounterexample) {L : ℕ}
    (i : PhaseIndex L) : IntervalMap :=
  positiveWordMap C.P C.Q i.1.val i.2.val

/-- A one-step translation on the first cyclic phase coordinate. -/
def phaseShiftP (L : ℕ) : Equiv.Perm (PhaseIndex L) :=
  Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl (ZMod L))

/-- A one-step translation on the second cyclic phase coordinate. -/
def phaseShiftQ (L : ℕ) : Equiv.Perm (PhaseIndex L) :=
  Equiv.prodCongr (Equiv.refl (ZMod L)) (Equiv.addRight 1)

/-- Constant-slope control for every phase word, including zero exponents. -/
theorem phaseWordMap_constantSlope
    (C : NormalizedConstantSlopeCounterexample) {L : ℕ}
    (i : PhaseIndex L) :
    HasConstantAbsoluteSlope (phaseWordMap C i)
      (C.scale_P ^ i.1.val * C.scale_Q ^ i.2.val) := by
  have hP := C.constantSlope_P.iterateMap
    (zero_lt_one.trans C.one_lt_scale_P) i.1.val
  have hQ := C.constantSlope_Q.iterateMap
    (zero_lt_one.trans C.one_lt_scale_Q) i.2.val
  have hcomp := hP.comp_of_pos
    (pow_pos (zero_lt_one.trans C.one_lt_scale_Q) i.2.val) hQ
  simpa [phaseWordMap, positiveWordMap, Function.comp_def] using hcomp

/-- Pulling one more copy of a map across the image of an iterate increments
the iterate exponent. -/
theorem image_iterateMap_succ
    (T : IntervalMap) (n : ℕ) (S : Set I) :
    T '' (iterateMap T n '' S) = iterateMap T (n + 1) '' S := by
  rw [Set.image_image]
  apply congrArg (fun f : IntervalMap => f '' S)
  funext x
  exact (Function.iterate_succ_apply' T n x).symm

/-- The cyclic successor image identity for representatives in `ZMod L`.
The wraparound case uses only the returned-set identity `T^L(S)=S`. -/
theorem image_iterateMap_zmod_succ
    (T : IntervalMap) (L : ℕ) (hL : 0 < L) (S : Set I)
    (hreturn : iterateMap T L '' S = S) (k : ZMod L) :
    T '' (iterateMap T k.val '' S) =
      iterateMap T (k + 1).val '' S := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  by_cases hLone : L = 1
  · subst L
    have hkzero : k = 0 := Subsingleton.elim _ _
    subst k
    have hval : ((0 : ZMod 1) + 1).val = 0 := by
      have hzero : (0 : ZMod 1) + 1 = 0 := Subsingleton.elim _ _
      exact congrArg ZMod.val hzero
    rw [hval]
    simpa [iterateMap] using hreturn
  letI : Fact (1 < L) := ⟨by omega⟩
  by_cases hk : k.val + 1 < L
  · have hval : (k + 1).val = k.val + 1 := by
      simpa [ZMod.val_one L] using
        (ZMod.val_add_of_lt (a := k) (b := (1 : ZMod L))
          (by simpa [ZMod.val_one L] using hk))
    rw [hval]
    exact image_iterateMap_succ T k.val S
  · have hkEq : k.val + 1 = L := by
      have hklt := ZMod.val_lt k
      omega
    have hval : (k + 1).val = 0 := by
      rw [ZMod.val_add_of_le]
      · simp [ZMod.val_one L, hkEq]
      · simpa [ZMod.val_one L, hkEq]
    rw [hval]
    simpa [iterateMap] using
      (calc
        T '' (iterateMap T k.val '' S) =
            iterateMap T (k.val + 1) '' S :=
          image_iterateMap_succ T k.val S
        _ = iterateMap T L '' S := by rw [hkEq]
        _ = S := hreturn)

/-- Images under a commuting map can be moved through every iterate. -/
theorem image_iterateMap_commute
    {P Q : IntervalMap} (hcomm : Function.Commute P Q)
    (n : ℕ) (S : Set I) :
    Q '' (iterateMap P n '' S) = iterateMap P n '' (Q '' S) := by
  rw [Set.image_image, Set.image_image]
  apply congrArg (fun f : IntervalMap => f '' S)
  funext x
  exact (hcomm.iterate_left n x).symm

/-- Commuting maps may be interchanged in a nested set image. -/
theorem image_image_commute
    {P Q : IntervalMap} (hcomm : Function.Commute P Q) (S : Set I) :
    P '' (Q '' S) = Q '' (P '' S) := by
  ext y
  constructor
  · rintro ⟨_z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨P x, ⟨x, hx, rfl⟩, (hcomm x).symm⟩
  · rintro ⟨_z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨Q x, ⟨x, hx, rfl⟩, hcomm x⟩

@[simp] theorem phaseShiftP_apply (L : ℕ) (i : PhaseIndex L) :
    phaseShiftP L i = (i.1 + 1, i.2) := rfl

@[simp] theorem phaseShiftQ_apply (L : ℕ) (i : PhaseIndex L) :
    phaseShiftQ L i = (i.1, i.2 + 1) := rfl

theorem phaseShiftP_iterate_apply (L n : ℕ) (i : PhaseIndex L) :
    (phaseShiftP L)^[n] i = (i.1 + n, i.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Prod.ext
      · change i.1 + (n : ZMod L) + 1 = i.1 + ((n + 1 : ℕ) : ZMod L)
        rw [Nat.cast_add, Nat.cast_one]
        abel
      · rfl

theorem phaseShiftQ_iterate_apply (L n : ℕ) (i : PhaseIndex L) :
    (phaseShiftQ L)^[n] i = (i.1, i.2 + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Prod.ext
      · rfl
      · change i.2 + (n : ZMod L) + 1 = i.2 + ((n + 1 : ℕ) : ZMod L)
        rw [Nat.cast_add, Nat.cast_one]
        abel

theorem phaseShiftP_periodic (L : ℕ) (i : PhaseIndex L) :
    (phaseShiftP L)^[L] i = i := by
  simpa using phaseShiftP_iterate_apply L L i

theorem phaseShiftQ_periodic (L : ℕ) (i : PhaseIndex L) :
    (phaseShiftQ L)^[L] i = i := by
  simpa using phaseShiftQ_iterate_apply L L i

theorem phaseShiftP_pow_apply (L n : ℕ) (i : PhaseIndex L) :
    (phaseShiftP L ^ n) i = (i.1 + n, i.2) := by
  rw [Equiv.Perm.coe_pow]
  exact phaseShiftP_iterate_apply L n i

theorem phaseShiftQ_pow_apply (L n : ℕ) (i : PhaseIndex L) :
    (phaseShiftQ L ^ n) i = (i.1, i.2 + n) := by
  rw [Equiv.Perm.coe_pow]
  exact phaseShiftQ_iterate_apply L n i

/-- The set underlying the phase indexed by `(i,j)`. -/
def phaseIntervalSet
    (C : NormalizedConstantSlopeCounterexample) {L : ℕ}
    (J : ClosedSubinterval) (i : PhaseIndex L) : Set I :=
  iterateMap C.P i.1.val '' (iterateMap C.Q i.2.val '' J.carrier)

/-- The nested-image presentation is the image of the corresponding phase
word. -/
theorem phaseIntervalSet_eq_phaseWord_image
    (C : NormalizedConstantSlopeCounterexample) {L : ℕ}
    (J : ClosedSubinterval) (i : PhaseIndex L) :
    phaseIntervalSet C J i = phaseWordMap C i '' J.carrier := by
  change iterateMap C.P i.1.val ''
      (iterateMap C.Q i.2.val '' J.carrier) =
    (fun x => iterateMap C.P i.1.val (iterateMap C.Q i.2.val x)) ''
      J.carrier
  rw [Set.image_image]

/-- `P` translates the first phase coordinate, including at the cyclic
wraparound. -/
theorem phaseIntervalSet_shiftP
    (C : NormalizedConstantSlopeCounterexample)
    (L : ℕ) (hL : 0 < L) (J : ClosedSubinterval)
    (hPonto : MapsOntoSubinterval (iterateMap C.P L) J)
    (i : PhaseIndex L) :
    C.P '' phaseIntervalSet C J i =
      phaseIntervalSet C J (phaseShiftP L i) := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rcases i with ⟨a, b⟩
  simp only [phaseIntervalSet, phaseShiftP_apply]
  apply image_iterateMap_zmod_succ C.P L hL
  calc
    iterateMap C.P L '' (iterateMap C.Q b.val '' J.carrier) =
        iterateMap C.Q b.val '' (iterateMap C.P L '' J.carrier) :=
      image_image_commute (C.commute.iterate_iterate L b.val)
        J.carrier
    _ = iterateMap C.Q b.val '' J.carrier := by rw [hPonto]

/-- `Q` translates the second phase coordinate, including at the cyclic
wraparound. -/
theorem phaseIntervalSet_shiftQ
    (C : NormalizedConstantSlopeCounterexample)
    (L : ℕ) (hL : 0 < L) (J : ClosedSubinterval)
    (hQonto : MapsOntoSubinterval (iterateMap C.Q L) J)
    (i : PhaseIndex L) :
    C.Q '' phaseIntervalSet C J i =
      phaseIntervalSet C J (phaseShiftQ L i) := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  rcases i with ⟨a, b⟩
  simp only [phaseIntervalSet, phaseShiftQ_apply]
  rw [image_iterateMap_commute C.commute a.val
    (iterateMap C.Q b.val '' J.carrier)]
  exact congrArg (iterateMap C.P a.val '' ·)
    (image_iterateMap_zmod_succ C.Q L hL J.carrier hQonto b)

/-- A cyclic permutation of a finite interval family induced by a map is an
automorphism of its intersection graph.  The reverse implication applies the
remaining `N-1` iterates. -/
theorem intervalIntersectionGraphAutomorphism_of_cyclicImage
    {V : Type*} (D : V → Set I) (e : Equiv.Perm V)
    (T : IntervalMap) (N : ℕ) (hN : 0 < N)
    (himage : ∀ i, T '' D i = D (e i))
    (hperiodic : ∀ i, e^[N] i = i) :
    IsIntervalIntersectionGraphAutomorphism D e := by
  have himage_iterate : ∀ n i,
      iterateMap T n '' D i = D (e^[n] i) := by
    intro n
    induction n with
    | zero =>
        intro i
        simp [iterateMap]
    | succ n ih =>
        intro i
        calc
          iterateMap T (n + 1) '' D i =
              T '' (iterateMap T n '' D i) :=
            (image_iterateMap_succ T n (D i)).symm
          _ = T '' D (e^[n] i) := by rw [ih i]
          _ = D (e (e^[n] i)) := himage (e^[n] i)
          _ = D (e^[n + 1] i) := by
            rw [Function.iterate_succ_apply']
  have hback (i : V) : e^[N - 1] (e i) = i := by
    calc
      e^[N - 1] (e i) = e^[(N - 1) + 1] i :=
        (Function.iterate_succ_apply e (N - 1) i).symm
      _ = e^[N] i := by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN.ne')]
      _ = i := hperiodic i
  intro u v
  constructor
  · rintro ⟨huv, ⟨x, hxu, hxv⟩⟩
    have huv' : u ≠ v := by
      intro huv'
      exact huv (congrArg e huv')
    refine ⟨huv', ⟨iterateMap T (N - 1) x, ?_, ?_⟩⟩
    · have hximage : iterateMap T (N - 1) x ∈
          iterateMap T (N - 1) '' D (e u) := ⟨x, hxu, rfl⟩
      rw [himage_iterate (N - 1) (e u), hback u] at hximage
      exact hximage
    · have hximage : iterateMap T (N - 1) x ∈
          iterateMap T (N - 1) '' D (e v) := ⟨x, hxv, rfl⟩
      rw [himage_iterate (N - 1) (e v), hback v] at hximage
      exact hximage
  · rintro ⟨huv, ⟨x, hxu, hxv⟩⟩
    refine ⟨e.injective.ne huv, ?_⟩
    exact ⟨T x,
      by rw [← himage u]; exact ⟨x, hxu, rfl⟩,
      by rw [← himage v]; exact ⟨x, hxv, rfl⟩⟩

private theorem intervalIntersectionGraphAutomorphism_refl
    {V : Type*} (D : V → Set I) :
    IsIntervalIntersectionGraphAutomorphism D (Equiv.refl V) := by
  intro u v
  rfl

private theorem intervalIntersectionGraphAutomorphism_mul
    {V : Type*} (D : V → Set I) {e f : Equiv.Perm V}
    (he : IsIntervalIntersectionGraphAutomorphism D e)
    (hf : IsIntervalIntersectionGraphAutomorphism D f) :
    IsIntervalIntersectionGraphAutomorphism D (e * f) := by
  intro u v
  exact (he (f u) (f v)).trans (hf u v)

private theorem intervalIntersectionGraphAutomorphism_pow
    {V : Type*} (D : V → Set I) {e : Equiv.Perm V}
    (he : IsIntervalIntersectionGraphAutomorphism D e) (n : ℕ) :
    IsIntervalIntersectionGraphAutomorphism D (e ^ n) := by
  induction n with
  | zero => simpa using intervalIntersectionGraphAutomorphism_refl D
  | succ n ih =>
      rw [pow_succ]
      exact intervalIntersectionGraphAutomorphism_mul D ih he

/-- Construction of the full `ZMod L × ZMod L` returned interval family,
including its two translation actions. -/
theorem phaseIntervalFamily_exists
    (C : NormalizedConstantSlopeCounterexample)
    (L : ℕ) (hL : 0 < L) (J : ClosedSubinterval)
    (hJ : J.Nondegenerate)
    (hPonto : MapsOntoSubinterval (iterateMap C.P L) J)
    (hQonto : MapsOntoSubinterval (iterateMap C.Q L) J) :
    Nonempty (PhaseIntervalFamilyData C L J) := by
  classical
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let raw : PhaseIndex L → Set I := fun i => phaseIntervalSet C J i
  have hraw_exists (i : PhaseIndex L) :
      ∃ K : ClosedSubinterval, K.carrier = raw i := by
    change ∃ K : ClosedSubinterval,
      K.carrier = phaseIntervalSet C J i
    rw [phaseIntervalSet_eq_phaseWord_image]
    exact continuousImageInterval_exists
      (phaseWordMap C i) (phaseWordMap_constantSlope C i).continuous J
  let D : PhaseIndex L → ClosedSubinterval := fun i =>
    Classical.choose (hraw_exists i)
  have hDcarrier (i : PhaseIndex L) : (D i).carrier = raw i := by
    exact Classical.choose_spec (hraw_exists i)
  have hDnondegenerate (i : PhaseIndex L) : (D i).Nondegenerate := by
    by_contra hdegenerate
    have hend : (D i).left = (D i).right :=
      le_antisymm (D i).left_le_right (not_lt.mp hdegenerate)
    have hflat : IsFlatInterval (phaseWordMap C i) J := by
      refine ⟨hJ, ?_⟩
      intro x hx y hy
      have hxD : phaseWordMap C i x ∈ (D i).carrier := by
        rw [hDcarrier i]
        change phaseWordMap C i x ∈ phaseIntervalSet C J i
        rw [phaseIntervalSet_eq_phaseWord_image]
        exact ⟨x, hx, rfl⟩
      have hyD : phaseWordMap C i y ∈ (D i).carrier := by
        rw [hDcarrier i]
        change phaseWordMap C i y ∈ phaseIntervalSet C J i
        rw [phaseIntervalSet_eq_phaseWord_image]
        exact ⟨y, hy, rfl⟩
      change (D i).left ≤ phaseWordMap C i x ∧
          phaseWordMap C i x ≤ (D i).right at hxD
      change (D i).left ≤ phaseWordMap C i y ∧
          phaseWordMap C i y ≤ (D i).right at hyD
      rw [hend] at hxD hyD
      have hxright : phaseWordMap C i x = (D i).right :=
        le_antisymm hxD.2 hxD.1
      have hyright : phaseWordMap C i y = (D i).right :=
        le_antisymm hyD.2 hyD.1
      exact hxright.trans hyright.symm
    have hslope_pos :
        0 < C.scale_P ^ i.1.val * C.scale_Q ^ i.2.val :=
      mul_pos (pow_pos (zero_lt_one.trans C.one_lt_scale_P) _)
        (pow_pos (zero_lt_one.trans C.one_lt_scale_Q) _)
    exact (phaseWordMap_constantSlope C i).noFlatInterval hslope_pos
      ⟨J, hflat⟩
  have hbase : (D (0, 0)).carrier = J.carrier := by
    rw [hDcarrier (0, 0)]
    change phaseIntervalSet C J (0, 0) = J.carrier
    rw [phaseIntervalSet]
    simp [iterateMap]
  have himageP (i : PhaseIndex L) :
      C.P '' (D i).carrier = (D (phaseShiftP L i)).carrier := by
    rw [hDcarrier i, hDcarrier (phaseShiftP L i)]
    exact phaseIntervalSet_shiftP C L hL J hPonto i
  have himageQ (i : PhaseIndex L) :
      C.Q '' (D i).carrier = (D (phaseShiftQ L i)).carrier := by
    rw [hDcarrier i, hDcarrier (phaseShiftQ L i)]
    exact phaseIntervalSet_shiftQ C L hL J hQonto i
  have hPauto : IsIntervalIntersectionGraphAutomorphism
      (fun i => (D i).carrier) (phaseShiftP L) :=
    intervalIntersectionGraphAutomorphism_of_cyclicImage
      (fun i => (D i).carrier) (phaseShiftP L) C.P L hL
        himageP (phaseShiftP_periodic L)
  have hQauto : IsIntervalIntersectionGraphAutomorphism
      (fun i => (D i).carrier) (phaseShiftQ L) :=
    intervalIntersectionGraphAutomorphism_of_cyclicImage
      (fun i => (D i).carrier) (phaseShiftQ L) C.Q L hL
        himageQ (phaseShiftQ_periodic L)
  have htransitive : IntervalIntersectionGraphVertexTransitive
      (fun i => (D i).carrier) := by
    intro u v
    let δP : ZMod L := v.1 - u.1
    let δQ : ZMod L := v.2 - u.2
    let eP : Equiv.Perm (PhaseIndex L) := phaseShiftP L ^ δP.val
    let eQ : Equiv.Perm (PhaseIndex L) := phaseShiftQ L ^ δQ.val
    refine ⟨eP * eQ, ?_, ?_⟩
    · exact intervalIntersectionGraphAutomorphism_mul
        (fun i => (D i).carrier)
        (intervalIntersectionGraphAutomorphism_pow
          (fun i => (D i).carrier) hPauto δP.val)
        (intervalIntersectionGraphAutomorphism_pow
          (fun i => (D i).carrier) hQauto δQ.val)
    · change (phaseShiftP L ^ δP.val)
        ((phaseShiftQ L ^ δQ.val) u) = v
      rw [phaseShiftQ_pow_apply, phaseShiftP_pow_apply]
      apply Prod.ext
      · change u.1 + (δP.val : ZMod L) = v.1
        rw [ZMod.natCast_zmod_val]
        simp [δP]
      · change u.2 + (δQ.val : ZMod L) = v.2
        rw [ZMod.natCast_zmod_val]
        simp [δQ]
  have hintersection :
      (⋂ i, (D i).carrier).Nonempty →
        ∃ K : ClosedSubinterval, K.carrier = ⋂ i, (D i).carrier := by
    intro hnonempty
    let S : Set I := ⋂ i, (D i).carrier
    have hclosed : IsClosed S := by
      dsimp [S]
      exact isClosed_iInter (fun _ => isClosed_Icc)
    have hcompact : IsCompact S := hclosed.isCompact
    have hord : Set.OrdConnected S := by
      dsimp [S]
      exact Set.ordConnected_iInter (fun _ => Set.ordConnected_Icc)
    obtain ⟨R⟩ := compactIntervalRepresentation_exists
      S hcompact hord (by simpa [S] using hnonempty)
    exact ⟨R.interval, by simpa [S] using R.carrier_eq⟩
  exact ⟨{
    interval := D
    base_carrier := hbase
    nondegenerate := hDnondegenerate
    shiftP := phaseShiftP L
    shiftQ := phaseShiftQ L
    image_P := himageP
    image_Q := himageQ
    graph_vertexTransitive := htransitive
    intersection_interval := hintersection
  }⟩

/-- The connected phase-graph alternative gives a common invariant
intersection, contradicting core minimality and properness of `J`. -/
theorem phaseIntersectionGraph_disconnected
    (C : NormalizedConstantSlopeCounterexample)
    (L : ℕ) (hL : 0 < L) (J : ClosedSubinterval)
    (hproper : J.carrier ≠ Set.univ)
    (F : PhaseIntervalFamilyData C L J) :
    ¬IntervalIntersectionGraphConnected (fun i => (F.interval i).carrier) := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  intro hconnected
  have hhelly :=
    connected_vertexTransitive_intervalFamily_complete_and_Helly
      (fun i => (F.interval i).carrier)
      (fun _ => isCompact_Icc)
      (fun _ => Set.ordConnected_Icc)
      (fun i => (F.interval i).carrier_nonempty)
      hconnected F.graph_vertexTransitive
  obtain ⟨K, hKcarrier⟩ := F.intersection_interval hhelly.2
  have hcore : IsCommonInvariantCore C.P C.Q K := by
    constructor
    · intro x hx
      rw [hKcarrier] at hx ⊢
      rw [Set.mem_iInter] at hx ⊢
      intro i
      let j := F.shiftP.symm i
      have hxj : x ∈ (F.interval j).carrier := hx j
      have himage : C.P x ∈ C.P '' (F.interval j).carrier := ⟨x, hxj, rfl⟩
      rw [F.image_P j] at himage
      simpa [j] using himage
    · intro x hx
      rw [hKcarrier] at hx ⊢
      rw [Set.mem_iInter] at hx ⊢
      intro i
      let j := F.shiftQ.symm i
      have hxj : x ∈ (F.interval j).carrier := hx j
      have himage : C.Q x ∈ C.Q '' (F.interval j).carrier := ⟨x, hxj, rfl⟩
      rw [F.image_Q j] at himage
      simpa [j] using himage
  have hKuniv : K.carrier = Set.univ := C.core_minimal K hcore
  apply hproper
  calc
    J.carrier = (F.interval (0, 0)).carrier := F.base_carrier.symm
    _ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hxK : x ∈ K.carrier := by rw [hKuniv]; exact Set.mem_univ x
      rw [hKcarrier, Set.mem_iInter] at hxK
      exact hxK (0, 0)

/-! ### E3b: connected components and their interval unions -/

/-- The simple graph underlying an interval-intersection family. -/
def intervalIntersectionSimpleGraph {V : Type*}
    (D : V → Set I) : SimpleGraph V where
  Adj := intervalIntersectionAdjacent D
  symm := by
    rintro u v ⟨huv, x, hxu, hxv⟩
    exact ⟨huv.symm, x, hxv, hxu⟩
  loopless := ⟨fun v h => h.1 rfl⟩

/-- The geometric union of all intervals whose labels lie in one graph
component. -/
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
      (∀ c d, c ≠ d →
        Disjoint (classes c).carrier (classes d).carrier) := by
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
    eq_Icc_of_connected_compact (hcomponentConnected c)
      (hcomponentCompact c)
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
    have hmkEq : G.connectedComponentMk v.1 =
        G.connectedComponentMk w.1 := by
      by_cases hvw : v.1 = w.1
      · exact congrArg G.connectedComponentMk hvw
      · apply SimpleGraph.ConnectedComponent.sound
        have hadj : G.Adj v.1 w.1 := ⟨hvw, ⟨x, hxv, hxw⟩⟩
        exact hadj.reachable
    exact hcd (hmkV.symm.trans (hmkEq.trans hmkW))
  exact ⟨classes, hcarrier, hnondegenerate, hpairwise⟩

/--
The unions of the connected components of the phase intersection graph.
The labelling records the actual graph components, while `permP` and `permQ`
record the permutations induced on component-unions by the generators.
-/
structure PhaseComponentUnionData
    {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
    {J : ClosedSubinterval} (F : PhaseIntervalFamilyData C L J) where
  componentCount : ℕ
  componentCount_nontrivial : 1 < componentCount
  componentOf : PhaseIndex L → Fin componentCount
  componentOf_surjective : Function.Surjective componentOf
  sameComponent_iff : ∀ i j,
    componentOf i = componentOf j ↔
      Relation.ReflTransGen
        (intervalIntersectionAdjacent (fun k => (F.interval k).carrier)) i j
  componentUnion : Fin componentCount → ClosedSubinterval
  componentUnion_carrier : ∀ k,
    (componentUnion k).carrier =
      ⋃ i, ⋃ (_hi : componentOf i = k), (F.interval i).carrier
  componentUnion_nondegenerate : ∀ k, (componentUnion k).Nondegenerate
  componentUnion_pairwise_disjoint : ∀ k l, k ≠ l →
    Disjoint (componentUnion k).carrier (componentUnion l).carrier
  permP : Equiv.Perm (Fin componentCount)
  permQ : Equiv.Perm (Fin componentCount)
  componentOf_shiftP : ∀ i, componentOf (F.shiftP i) = permP (componentOf i)
  componentOf_shiftQ : ∀ i, componentOf (F.shiftQ i) = permQ (componentOf i)
  image_P_componentUnion : ∀ k,
    C.P '' (componentUnion k).carrier = (componentUnion (permP k)).carrier
  image_Q_componentUnion : ∀ k,
    C.Q '' (componentUnion k).carrier = (componentUnion (permQ k)).carrier
  interval_subset_component : ∀ i,
    (F.interval i).carrier ⊆ (componentUnion (componentOf i)).carrier

/-- A disconnected finite interval-intersection graph yields finitely many
pairwise-disjoint nondegenerate interval component-unions, permuted by both
generators. -/
theorem phaseComponentUnions_exists
    {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
    {J : ClosedSubinterval} (F : PhaseIntervalFamilyData C L J)
    (hL : 0 < L)
    (hdisconnected :
      ¬IntervalIntersectionGraphConnected (fun i => (F.interval i).carrier)) :
    Nonempty (PhaseComponentUnionData F) := by
  classical
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let D : PhaseIndex L → Set I := fun i => (F.interval i).carrier
  let G := intervalIntersectionSimpleGraph D
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨classes, hclasses_carrier, hclasses_nondegenerate,
      hclasses_pairwise⟩ :=
    intervalGraph_componentInterval_package D
      (fun _ => isCompact_Icc)
      (fun i => ⟨(F.interval i).carrier_nonempty,
        Set.ordConnected_Icc.isPreconnected⟩)
      (fun i => ⟨(F.interval i).left,
        (F.interval i).left_mem_carrier,
        (F.interval i).right,
        (F.interval i).right_mem_carrier,
        ne_of_lt (F.nondegenerate i)⟩)
  let componentCount : ℕ := Fintype.card G.ConnectedComponent
  let componentEquiv : G.ConnectedComponent ≃ Fin componentCount :=
    Fintype.equivFin G.ConnectedComponent
  let componentOf : PhaseIndex L → Fin componentCount := fun i =>
    componentEquiv (G.connectedComponentMk i)
  let componentUnion : Fin componentCount → ClosedSubinterval := fun k =>
    classes (componentEquiv.symm k)
  have hcomponentCount : 1 < componentCount := by
    change 1 < Fintype.card G.ConnectedComponent
    rw [Fintype.one_lt_card_iff]
    change ¬∀ u v, Relation.ReflTransGen
      (intervalIntersectionAdjacent D) u v at hdisconnected
    push Not at hdisconnected
    obtain ⟨u, v, huv⟩ := hdisconnected
    refine ⟨G.connectedComponentMk u, G.connectedComponentMk v, ?_⟩
    intro hmk
    apply huv
    have hreach : G.Reachable u v :=
      SimpleGraph.ConnectedComponent.exact hmk
    simpa [G, intervalIntersectionSimpleGraph] using
      (G.reachable_iff_reflTransGen u v).mp hreach
  have hcomponentOf_surjective : Function.Surjective componentOf := by
    intro k
    let c : G.ConnectedComponent := componentEquiv.symm k
    obtain ⟨i, hi⟩ := c.nonempty_supp
    refine ⟨i, ?_⟩
    have hmk : G.connectedComponentMk i = c :=
      (c.mem_supp_iff i).mp hi
    simp [componentOf, hmk, c]
  have hsameComponent (i j : PhaseIndex L) :
      componentOf i = componentOf j ↔
        Relation.ReflTransGen
          (intervalIntersectionAdjacent D) i j := by
    constructor
    · intro hij
      have hmk : G.connectedComponentMk i = G.connectedComponentMk j := by
        apply componentEquiv.injective
        simpa [componentOf] using hij
      have hreach : G.Reachable i j :=
        SimpleGraph.ConnectedComponent.exact hmk
      simpa [G, intervalIntersectionSimpleGraph] using
        (G.reachable_iff_reflTransGen i j).mp hreach
    · intro hij
      have hpath : Relation.ReflTransGen G.Adj i j := by
        simpa [G, intervalIntersectionSimpleGraph] using hij
      have hreach : G.Reachable i j :=
        (G.reachable_iff_reflTransGen i j).mpr hpath
      have hmk : G.connectedComponentMk i = G.connectedComponentMk j :=
        SimpleGraph.ConnectedComponent.sound hreach
      exact congrArg componentEquiv hmk
  have hcomponentUnion_carrier (k : Fin componentCount) :
      (componentUnion k).carrier =
        ⋃ i, ⋃ (_hi : componentOf i = k), (F.interval i).carrier := by
    rw [show (componentUnion k).carrier =
        intervalGraphComponentUnion D (componentEquiv.symm k) by
      exact hclasses_carrier (componentEquiv.symm k)]
    ext x
    constructor
    · intro hx
      obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hx
      apply Set.mem_iUnion.mpr
      refine ⟨v.1, ?_⟩
      apply Set.mem_iUnion.mpr
      have hmk : G.connectedComponentMk v.1 = componentEquiv.symm k :=
        ((componentEquiv.symm k).mem_supp_iff v.1).mp v.2
      have hlabel : componentOf v.1 = k := by
        simp [componentOf, hmk]
      exact ⟨hlabel, by simpa [D] using hxv⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxi
      have hmk : G.connectedComponentMk i = componentEquiv.symm k := by
        apply componentEquiv.injective
        simpa [componentOf] using hi
      let v : (componentEquiv.symm k).supp :=
        ⟨i, ((componentEquiv.symm k).mem_supp_iff i).mpr hmk⟩
      exact Set.mem_iUnion.mpr ⟨v, by simpa [D, v] using hxi⟩
  have hadjP {i j : PhaseIndex L} (hij : G.Adj i j) :
      G.Adj (F.shiftP i) (F.shiftP j) := by
    rcases hij with ⟨hij, x, hxi, hxj⟩
    refine ⟨F.shiftP.injective.ne hij, C.P x, ?_, ?_⟩
    · change x ∈ (F.interval i).carrier at hxi
      change C.P x ∈ (F.interval (F.shiftP i)).carrier
      rw [← F.image_P i]
      exact ⟨x, hxi, rfl⟩
    · change x ∈ (F.interval j).carrier at hxj
      change C.P x ∈ (F.interval (F.shiftP j)).carrier
      rw [← F.image_P j]
      exact ⟨x, hxj, rfl⟩
  have hadjQ {i j : PhaseIndex L} (hij : G.Adj i j) :
      G.Adj (F.shiftQ i) (F.shiftQ j) := by
    rcases hij with ⟨hij, x, hxi, hxj⟩
    refine ⟨F.shiftQ.injective.ne hij, C.Q x, ?_, ?_⟩
    · change x ∈ (F.interval i).carrier at hxi
      change C.Q x ∈ (F.interval (F.shiftQ i)).carrier
      rw [← F.image_Q i]
      exact ⟨x, hxi, rfl⟩
    · change x ∈ (F.interval j).carrier at hxj
      change C.Q x ∈ (F.interval (F.shiftQ j)).carrier
      rw [← F.image_Q j]
      exact ⟨x, hxj, rfl⟩
  let homP : G →g G :=
    { toFun := F.shiftP
      map_rel' := fun h => hadjP h }
  let homQ : G →g G :=
    { toFun := F.shiftQ
      map_rel' := fun h => hadjQ h }
  let componentMapP : G.ConnectedComponent → G.ConnectedComponent :=
    fun c => c.map homP
  let componentMapQ : G.ConnectedComponent → G.ConnectedComponent :=
    fun c => c.map homQ
  have hcomponentMapP_surjective : Function.Surjective componentMapP := by
    intro d
    obtain ⟨v, hv⟩ := d.nonempty_supp
    let u : PhaseIndex L := F.shiftP.symm v
    refine ⟨G.connectedComponentMk u, ?_⟩
    change (G.connectedComponentMk u).map homP = d
    rw [SimpleGraph.ConnectedComponent.map_mk]
    change G.connectedComponentMk (F.shiftP u) = d
    have hshift : F.shiftP u = v := by simp [u]
    rw [hshift]
    exact (d.mem_supp_iff v).mp hv
  have hcomponentMapQ_surjective : Function.Surjective componentMapQ := by
    intro d
    obtain ⟨v, hv⟩ := d.nonempty_supp
    let u : PhaseIndex L := F.shiftQ.symm v
    refine ⟨G.connectedComponentMk u, ?_⟩
    change (G.connectedComponentMk u).map homQ = d
    rw [SimpleGraph.ConnectedComponent.map_mk]
    change G.connectedComponentMk (F.shiftQ u) = d
    have hshift : F.shiftQ u = v := by simp [u]
    rw [hshift]
    exact (d.mem_supp_iff v).mp hv
  let componentPermP : Equiv.Perm G.ConnectedComponent :=
    Equiv.ofBijective componentMapP
      hcomponentMapP_surjective.bijective_of_finite
  let componentPermQ : Equiv.Perm G.ConnectedComponent :=
    Equiv.ofBijective componentMapQ
      hcomponentMapQ_surjective.bijective_of_finite
  let permP : Equiv.Perm (Fin componentCount) :=
    componentEquiv.symm.trans (componentPermP.trans componentEquiv)
  let permQ : Equiv.Perm (Fin componentCount) :=
    componentEquiv.symm.trans (componentPermQ.trans componentEquiv)
  have hcomponentOf_shiftP (i : PhaseIndex L) :
      componentOf (F.shiftP i) = permP (componentOf i) := by
    simp [componentOf, permP, componentPermP, componentMapP, homP]
  have hcomponentOf_shiftQ (i : PhaseIndex L) :
      componentOf (F.shiftQ i) = permQ (componentOf i) := by
    simp [componentOf, permQ, componentPermQ, componentMapQ, homQ]
  have himageP_componentUnion (k : Fin componentCount) :
      C.P '' (componentUnion k).carrier =
        (componentUnion (permP k)).carrier := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hcomponentUnion_carrier] at hy ⊢
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hi, hyi⟩ := Set.mem_iUnion.mp hyi
      apply Set.mem_iUnion.mpr
      refine ⟨F.shiftP i, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨by simpa [hi] using hcomponentOf_shiftP i, ?_⟩
      rw [← F.image_P i]
      exact ⟨y, hyi, rfl⟩
    · intro hx
      rw [hcomponentUnion_carrier] at hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hj, hxj⟩ := Set.mem_iUnion.mp hxj
      let i : PhaseIndex L := F.shiftP.symm j
      have hshift : F.shiftP i = j := by simp [i]
      have hi : componentOf i = k := by
        apply permP.injective
        rw [← hcomponentOf_shiftP i, hshift, hj]
      have hximage : x ∈ C.P '' (F.interval i).carrier := by
        rw [F.image_P i, hshift]
        exact hxj
      obtain ⟨y, hyi, rfl⟩ := hximage
      refine ⟨y, ?_, rfl⟩
      rw [hcomponentUnion_carrier]
      exact Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨hi, hyi⟩⟩
  have himageQ_componentUnion (k : Fin componentCount) :
      C.Q '' (componentUnion k).carrier =
        (componentUnion (permQ k)).carrier := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hcomponentUnion_carrier] at hy ⊢
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨hi, hyi⟩ := Set.mem_iUnion.mp hyi
      apply Set.mem_iUnion.mpr
      refine ⟨F.shiftQ i, ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨by simpa [hi] using hcomponentOf_shiftQ i, ?_⟩
      rw [← F.image_Q i]
      exact ⟨y, hyi, rfl⟩
    · intro hx
      rw [hcomponentUnion_carrier] at hx
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hj, hxj⟩ := Set.mem_iUnion.mp hxj
      let i : PhaseIndex L := F.shiftQ.symm j
      have hshift : F.shiftQ i = j := by simp [i]
      have hi : componentOf i = k := by
        apply permQ.injective
        rw [← hcomponentOf_shiftQ i, hshift, hj]
      have hximage : x ∈ C.Q '' (F.interval i).carrier := by
        rw [F.image_Q i, hshift]
        exact hxj
      obtain ⟨y, hyi, rfl⟩ := hximage
      refine ⟨y, ?_, rfl⟩
      rw [hcomponentUnion_carrier]
      exact Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨hi, hyi⟩⟩
  have hinterval_subset (i : PhaseIndex L) :
      (F.interval i).carrier ⊆
        (componentUnion (componentOf i)).carrier := by
    intro x hx
    rw [hcomponentUnion_carrier]
    exact Set.mem_iUnion.mpr ⟨i,
      Set.mem_iUnion.mpr ⟨rfl, hx⟩⟩
  exact ⟨{
    componentCount := componentCount
    componentCount_nontrivial := hcomponentCount
    componentOf := componentOf
    componentOf_surjective := hcomponentOf_surjective
    sameComponent_iff := by
      intro i j
      simpa [D] using hsameComponent i j
    componentUnion := componentUnion
    componentUnion_carrier := hcomponentUnion_carrier
    componentUnion_nondegenerate := fun k =>
      hclasses_nondegenerate (componentEquiv.symm k)
    componentUnion_pairwise_disjoint := by
      intro k l hkl
      exact hclasses_pairwise _ _ (componentEquiv.symm.injective.ne hkl)
    permP := permP
    permQ := permQ
    componentOf_shiftP := hcomponentOf_shiftP
    componentOf_shiftQ := hcomponentOf_shiftQ
    image_P_componentUnion := himageP_componentUnion
    image_Q_componentUnion := himageQ_componentUnion
    interval_subset_component := hinterval_subset
  }⟩

/-! ### E3c: the canonical quotient and fibre respect -/

/-- A canonical finite interval quotient whose displayed nontrivial fibres
are exactly the phase component-unions. -/
structure PhaseCanonicalQuotientData
    {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
    {J : ClosedSubinterval} {F : PhaseIntervalFamilyData C L J}
    (U : PhaseComponentUnionData F) where
  quotient : CanonicalFiniteIntervalQuotient
  componentEquiv : Fin quotient.collapsedCount ≃ Fin U.componentCount
  collapsed_carrier : ∀ i,
    (quotient.collapsed i).carrier =
      (U.componentUnion (componentEquiv i)).carrier

/-- Pairwise-disjoint component-unions admit the manuscript's nonconstant
piecewise-linear monotone collapse, affine on every complementary gap. -/
theorem phaseCanonicalQuotient_exists
    {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
    {J : ClosedSubinterval} {F : PhaseIntervalFamilyData C L J}
    (U : PhaseComponentUnionData F) :
    Nonempty (PhaseCanonicalQuotientData U) := by
  classical
  have htwo : ∃ i j : Fin U.componentCount, i ≠ j := by
    let i : Fin U.componentCount :=
      ⟨0, Nat.zero_lt_of_lt U.componentCount_nontrivial⟩
    let j : Fin U.componentCount :=
      ⟨1, U.componentCount_nontrivial⟩
    refine ⟨i, j, ?_⟩
    intro hij
    have hval := congrArg Fin.val hij
    simp [i, j] at hval
  have hproper :
      (⋃ i, (U.componentUnion i).carrier) ≠ Set.univ :=
    FiniteIntervalQuotientConstruction.pairwiseDisjointFiniteIntervalFamily_union_ne_univ
        U.componentUnion U.componentUnion_pairwise_disjoint htwo
  obtain ⟨P⟩ := FiniteIntervalQuotientConstruction.finiteIntervalQuotientPresentation_exists
      U.componentUnion U.componentUnion_nondegenerate
        U.componentUnion_pairwise_disjoint hproper
  exact ⟨{
    quotient := P.quotient
    componentEquiv := P.indexEquiv
    collapsed_carrier := P.collapsed_carrier
  }⟩

/-- Permutation of the displayed quotient fibres is exactly what is needed
for both generators to respect the quotient relation. -/
theorem phaseCanonicalQuotient_respects_generators
    {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
    {J : ClosedSubinterval} {F : PhaseIntervalFamilyData C L J}
    {U : PhaseComponentUnionData F}
    (Q : PhaseCanonicalQuotientData U) :
    RespectsFibres Q.quotient.toFun C.P ∧
      RespectsFibres Q.quotient.toFun C.Q := by
  constructor
  · intro x y hxy
    rcases (Q.quotient.fibre_iff x y).mp hxy with hxy | ⟨i, hxi, hyi⟩
    · subst y
      rfl
    · let k := Q.componentEquiv i
      have hxk : x ∈ (U.componentUnion k).carrier := by
        rw [← Q.collapsed_carrier i]
        exact hxi
      have hyk : y ∈ (U.componentUnion k).carrier := by
        rw [← Q.collapsed_carrier i]
        exact hyi
      have hxP : C.P x ∈ (U.componentUnion (U.permP k)).carrier := by
        rw [← U.image_P_componentUnion k]
        exact ⟨x, hxk, rfl⟩
      have hyP : C.P y ∈ (U.componentUnion (U.permP k)).carrier := by
        rw [← U.image_P_componentUnion k]
        exact ⟨y, hyk, rfl⟩
      let j : Fin Q.quotient.collapsedCount :=
        Q.componentEquiv.symm (U.permP k)
      apply (Q.quotient.fibre_iff (C.P x) (C.P y)).mpr
      right
      refine ⟨j, ?_, ?_⟩
      · rw [Q.collapsed_carrier j]
        simpa [j, k] using hxP
      · rw [Q.collapsed_carrier j]
        simpa [j, k] using hyP
  · intro x y hxy
    rcases (Q.quotient.fibre_iff x y).mp hxy with hxy | ⟨i, hxi, hyi⟩
    · subst y
      rfl
    · let k := Q.componentEquiv i
      have hxk : x ∈ (U.componentUnion k).carrier := by
        rw [← Q.collapsed_carrier i]
        exact hxi
      have hyk : y ∈ (U.componentUnion k).carrier := by
        rw [← Q.collapsed_carrier i]
        exact hyi
      have hxQ : C.Q x ∈ (U.componentUnion (U.permQ k)).carrier := by
        rw [← U.image_Q_componentUnion k]
        exact ⟨x, hxk, rfl⟩
      have hyQ : C.Q y ∈ (U.componentUnion (U.permQ k)).carrier := by
        rw [← U.image_Q_componentUnion k]
        exact ⟨y, hyk, rfl⟩
      let j : Fin Q.quotient.collapsedCount :=
        Q.componentEquiv.symm (U.permQ k)
      apply (Q.quotient.fibre_iff (C.Q x) (C.Q y)).mpr
      right
      refine ⟨j, ?_, ?_⟩
      · rw [Q.collapsed_carrier j]
        simpa [j, k] using hxQ
      · rw [Q.collapsed_carrier j]
        simpa [j, k] using hyQ

/-! ### E3d: descended PL maps and the minimal counterexample package -/

/-- The only additional regularity needed after fibre respect: both
choice-defined descents are again finite-piece PL. -/
structure PhaseDescendedPLData
    {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
    {J : ClosedSubinterval} {F : PhaseIntervalFamilyData C L J}
    {U : PhaseComponentUnionData F}
    (Q : PhaseCanonicalQuotientData U)
    (hP : RespectsFibres Q.quotient.toFun C.P)
    (hQ : RespectsFibres Q.quotient.toFun C.Q) where
  finitePiece_P : FinitePiecePL (descendedMap Q.quotient C.P hP)
  finitePiece_Q : FinitePiecePL (descendedMap Q.quotient C.Q hQ)

/-- Refinement at the finitely many collapsed endpoints and original PL
vertices gives finite-piece PL presentations of both descended maps. -/
theorem phaseDescendedPL_exists
    {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
    {J : ClosedSubinterval} {F : PhaseIntervalFamilyData C L J}
    {U : PhaseComponentUnionData F}
    (Q : PhaseCanonicalQuotientData U)
    (hP : RespectsFibres Q.quotient.toFun C.P)
    (hQ : RespectsFibres Q.quotient.toFun C.Q) :
    Nonempty (PhaseDescendedPLData Q hP hQ) := by
  exact ⟨{
    finitePiece_P := finitePiecePL_descendedMap
      Q.quotient C.P C.finitePiece_P hP
    finitePiece_Q := finitePiecePL_descendedMap
      Q.quotient C.Q C.finitePiece_Q hQ
  }⟩

namespace PhaseDescendedPLData

variable {C : NormalizedConstantSlopeCounterexample} {L : ℕ}
  {J : ClosedSubinterval} {F : PhaseIntervalFamilyData C L J}
  {U : PhaseComponentUnionData F}
  {Q : PhaseCanonicalQuotientData U}
  {hP : RespectsFibres Q.quotient.toFun C.P}
  {hQ : RespectsFibres Q.quotient.toFun C.Q}

/-- The quotient and its two descents as a common monotone factor. -/
noncomputable def factor (D : PhaseDescendedPLData Q hP hQ) :
    MonotonePairFactor C.P C.Q
      (descendedMap Q.quotient C.P hP)
      (descendedMap Q.quotient C.Q hQ) :=
  descendedMonotonePairFactor Q.quotient C.P C.Q hP hQ

/-- The descended pair, with onto, commutation, absence of common fixed
points, and core minimality obtained from the common monotone factor. -/
noncomputable def target (D : PhaseDescendedPLData Q hP hQ) :
    MinimalPiecewiseLinearCounterexampleData where
  P := descendedMap Q.quotient C.P hP
  Q := descendedMap Q.quotient C.Q hQ
  finitePiece_P := D.finitePiece_P
  finitePiece_Q := D.finitePiece_Q
  onto_P := surjective_descendedMap Q.quotient C.P hP C.onto_P
  onto_Q := surjective_descendedMap Q.quotient C.Q hQ C.onto_Q
  commute := commute_descendedMap Q.quotient C.P C.Q hP hQ C.commute
  no_common_fixed_point :=
    D.factor.target_noCommonFixedPoint_of_coreMinimal C.core_minimal
  core_minimal := D.factor.target_coreMinimal C.core_minimal

/-- The same factor, with the derived target package exposed in its type. -/
noncomputable def factorToTarget (D : PhaseDescendedPLData Q hP hQ) :
    MonotonePairFactor C.P C.Q D.target.P D.target.Q :=
  D.factor

end PhaseDescendedPLData

/-- A continuous surjection of a nondegenerate interval onto itself has two
distinct fixed points for its square. -/
theorem mapsOntoSubinterval_exists_two_fixedPoints_square
    (T : IntervalMap) (J : ClosedSubinterval)
    (hT : Continuous T) (honto : MapsOntoSubinterval T J)
    (hJ : J.Nondegenerate) :
    ∃ x ∈ J.carrier, ∃ y ∈ J.carrier,
      x ≠ y ∧ IsFixedPoint (iterateMap T 2) x ∧
        IsFixedPoint (iterateMap T 2) y := by
  change T '' J.carrier = J.carrier at honto
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
      exact hJ.ne' (hzfix.symm.trans hv)
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
      exact hJ.ne (hzfix.symm.trans hu)
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

/-! ### E3e: the strict identification in the collapsed fibre -/

/-- The square of the returned map is the `2L`-th iterate, with the two
equivalent multiplication orders made explicit. -/
private theorem iterateMap_returned_square
    (T : IntervalMap) (L : ℕ) :
    iterateMap (iterateMap T L) 2 = iterateMap T (2 * L) := by
  calc
    iterateMap (iterateMap T L) 2 = iterateMap T (L * 2) :=
      (Function.iterate_mul T L 2).symm
    _ = iterateMap T (2 * L) := by rw [Nat.mul_comm]

/-- The two fixed points supplied inside the base returned interval lie in
one displayed component-union and hence in one nontrivial quotient fibre. -/
theorem phaseCanonicalQuotient_identifies_returnedSquare
    (C : NormalizedConstantSlopeCounterexample)
    (L : ℕ) (J : ClosedSubinterval)
    (hJ : J.Nondegenerate)
    (hPonto : MapsOntoSubinterval (iterateMap C.P L) J)
    (F : PhaseIntervalFamilyData C L J)
    (U : PhaseComponentUnionData F)
    (Q : PhaseCanonicalQuotientData U) :
    IdentifiesDistinctFixedPoints Q.quotient.toFun
      (iterateMap C.P (2 * L)) := by
  obtain ⟨x, hxJ, y, hyJ, hxy, hxfix, hyfix⟩ :=
    mapsOntoSubinterval_exists_two_fixedPoints_square
      (iterateMap C.P L) J
      (IntervalMap.continuous_iterate C.finitePiece_P.continuous L)
      hPonto hJ
  have hxreturned : x ∈ fixedPoints (iterateMap C.P (2 * L)) := by
    rw [← iterateMap_returned_square C.P L]
    exact hxfix
  have hyreturned : y ∈ fixedPoints (iterateMap C.P (2 * L)) := by
    rw [← iterateMap_returned_square C.P L]
    exact hyfix
  have hxbase : x ∈ (F.interval (0, 0)).carrier := by
    rw [F.base_carrier]
    exact hxJ
  have hybase : y ∈ (F.interval (0, 0)).carrier := by
    rw [F.base_carrier]
    exact hyJ
  let k : Fin U.componentCount := U.componentOf (0, 0)
  have hxcomponent : x ∈ (U.componentUnion k).carrier := by
    simpa [k] using U.interval_subset_component (0, 0) hxbase
  have hycomponent : y ∈ (U.componentUnion k).carrier := by
    simpa [k] using U.interval_subset_component (0, 0) hybase
  let i : Fin Q.quotient.collapsedCount := Q.componentEquiv.symm k
  have hxcollapsed : x ∈ (Q.quotient.collapsed i).carrier := by
    rw [Q.collapsed_carrier i]
    simpa [i, k] using hxcomponent
  have hycollapsed : y ∈ (Q.quotient.collapsed i).carrier := by
    rw [Q.collapsed_carrier i]
    simpa [i, k] using hycomponent
  refine ⟨x, y, hxreturned, hyreturned, hxy, ?_⟩
  exact (Q.quotient.fibre_iff x y).mpr
    (Or.inr ⟨i, hxcollapsed, hycollapsed⟩)

/--
The connected phase-graph alternative contradicts minimality.  In the
disconnected alternative, collapsing component unions gives the displayed
nonconstant common quotient and identifies two returned-square fixed points.
-/
theorem phaseComponentQuotient_exists
    (C : NormalizedConstantSlopeCounterexample)
    (L : ℕ) (hL : 0 < L) (J : ClosedSubinterval)
    (hJ : J.Nondegenerate)
    (hPonto : MapsOntoSubinterval (iterateMap C.P L) J)
    (hQonto : MapsOntoSubinterval (iterateMap C.Q L) J)
    (hproper : J.carrier ≠ Set.univ) :
    Nonempty (PhaseComponentQuotientData C L) := by
  obtain ⟨F⟩ := phaseIntervalFamily_exists C L hL J hJ hPonto hQonto
  have hdisconnected :=
    phaseIntersectionGraph_disconnected C L hL J hproper F
  obtain ⟨U⟩ := phaseComponentUnions_exists F hL hdisconnected
  obtain ⟨Q⟩ := phaseCanonicalQuotient_exists U
  have hrespect := phaseCanonicalQuotient_respects_generators Q
  obtain ⟨D⟩ := phaseDescendedPL_exists Q hrespect.1 hrespect.2
  refine ⟨{
    target := D.target
    factor := D.factorToTarget
    identifies_returnedSquare := ?_ }⟩
  change IdentifiesDistinctFixedPoints Q.quotient.toFun
    (iterateMap C.P (2 * L))
  exact phaseCanonicalQuotient_identifies_returnedSquare C L J hJ hPonto F U Q

/-- The component quotient strictly lowers the returned-square fixed count. -/
theorem phaseComponentQuotient_strict_descent
    (C : NormalizedConstantSlopeCounterexample)
    (L : ℕ) (hL : 0 < L)
    (D : PhaseComponentQuotientData C L) :
    (fixedPoints (iterateMap D.target.P (2 * L))).Finite ∧
      (fixedPoints (iterateMap D.target.P (2 * L))).ncard <
        (fixedPoints (iterateMap C.P (2 * L))).ncard := by
  have hexact := fixedPoints_descendExactly_of_monotone_semiconjugacy
    D.factor.continuous_coordinate D.factor.monotone_coordinate
    D.factor.surjective_coordinate
    (IntervalMap.continuous_iterate C.finitePiece_P.continuous (2 * L))
    (D.factor.intertwines_iterate_P (2 * L))
  exact fixed_cardinality_strict_of_exact_descent
    D.factor.coordinate (iterateMap C.P (2 * L))
      (iterateMap D.target.P (2 * L)) hexact
      D.identifies_returnedSquare
      (returnedSquare_fixedPoints_finite C L hL)

/-! ## Restoration of constant slopes -/

/-- A second common monotone factor restores a normalized expanding
constant-slope pair after the component collapse. -/
structure ConstantSlopeRelinearization
    (D : MinimalPiecewiseLinearCounterexampleData) where
  target : NormalizedConstantSlopeCounterexample
  factor : MonotonePairFactor D.P D.Q target.P target.Q

/-- Every finite-piece PL presentation supplies a finite-piece weak-
monotonicity presentation on the same cells. -/
private theorem FinitePiecePL.finitePieceMonotone_extremal
    {T : IntervalMap} (hT : FinitePiecePL T) :
    FinitePieceMonotone T := by
  rcases hT with ⟨hcont, p, hp⟩
  exact FinitePieceMonotone.of_partition hcont p fun _ _ hab =>
    (hp hab).isWeaklyMonotoneOn

/-- Every minimal PL counterexample admits the common constant-slope
relinearization used in the manuscript. -/
theorem constantSlopeRelinearization_exists
    (D : MinimalPiecewiseLinearCounterexampleData) :
    Nonempty (ConstantSlopeRelinearization D) := by
  let M : MinimalPiecewiseMonotoneCounterexample :=
    { P := D.P
      Q := D.Q
      finitePiece_P := D.finitePiece_P.finitePieceMonotone_extremal
      finitePiece_Q := D.finitePiece_Q.finitePieceMonotone_extremal
      onto_P := D.onto_P
      onto_Q := D.onto_Q
      commute := D.commute
      no_common_fixed_point := D.no_common_fixed_point
      core_minimal := D.core_minimal }
  obtain ⟨E⟩ := constantSlope_quotient_exists M
  have hno : ¬HasCommonFixedPoint E.eigen.factorP E.eigen.factorQ :=
    E.common_factor.target_noCommonFixedPoint_of_coreMinimal M.core_minimal
  have hminimal : ∀ J : ClosedSubinterval,
      IsCommonInvariantCore E.eigen.factorP E.eigen.factorQ J →
        J.carrier = Set.univ :=
    E.common_factor.target_coreMinimal M.core_minimal
  have hscales : 1 < E.eigen.scaleP ∧ 1 < E.eigen.scaleQ :=
    constantSlope_counterexample_scales_gt_one
      E.onto_factorP E.onto_factorQ E.factors_commute hno
      E.eigen.scaleP_pos E.eigen.scaleQ_pos
      E.constantSlope_factorP E.constantSlope_factorQ
  let target : NormalizedConstantSlopeCounterexample :=
    { P := E.eigen.factorP
      Q := E.eigen.factorQ
      finitePiece_P := E.finitePiece_factorP
      finitePiece_Q := E.finitePiece_factorQ
      onto_P := E.onto_factorP
      onto_Q := E.onto_factorQ
      commute := E.factors_commute
      no_common_fixed_point := hno
      core_minimal := hminimal
      scale_P := E.eigen.scaleP
      scale_Q := E.eigen.scaleQ
      one_lt_scale_P := hscales.1
      one_lt_scale_Q := hscales.2
      constantSlope_P := E.constantSlope_factorP
      constantSlope_Q := E.constantSlope_factorQ }
  refine ⟨⟨target, ?_⟩⟩
  simpa [M, target] using E.common_factor

/-- Relinearization cannot increase a finite returned-square fixed count. -/
theorem relinearization_returnedSquare_count_nonincreasing
    {D : MinimalPiecewiseLinearCounterexampleData}
    (R : ConstantSlopeRelinearization D)
    (L : ℕ)
    (hfinite : (fixedPoints (iterateMap D.P (2 * L))).Finite) :
    (fixedPoints (iterateMap R.target.P (2 * L))).ncard ≤
      (fixedPoints (iterateMap D.P (2 * L))).ncard := by
  have hexact := fixedPoints_descendExactly_of_monotone_semiconjugacy
    R.factor.continuous_coordinate R.factor.monotone_coordinate
    R.factor.surjective_coordinate
    (IntervalMap.continuous_iterate D.finitePiece_P.continuous (2 * L))
    (R.factor.intertwines_iterate_P (2 * L))
  rw [hexact]
  exact Set.ncard_image_le hfinite

/-! ## Extremal choice and irreducibility -/

/-- A normalized expanding constant-slope factor of the initial system. -/
structure ConstantSlopeFactorOf
    (C₀ : NormalizedConstantSlopeCounterexample) where
  system : NormalizedConstantSlopeCounterexample
  factor : MonotonePairFactor C₀.P C₀.Q system.P system.Q

/-- The initial system belongs to its factor family. -/
def ConstantSlopeFactorOf.refl
    (C₀ : NormalizedConstantSlopeCounterexample) :
    ConstantSlopeFactorOf C₀ where
  system := C₀
  factor := MonotonePairFactor.refl C₀.P C₀.Q

/-- The returned-square fixed-count objective. -/
def returnedSquareFixedCount
    {C₀ : NormalizedConstantSlopeCounterexample}
    (L : ℕ) (F : ConstantSlopeFactorOf C₀) : ℕ :=
  (fixedPoints (iterateMap F.system.P (2 * L))).ncard

/-- A factor attaining the least returned-square fixed count. -/
structure ExtremalFactorChoice
    (C₀ : NormalizedConstantSlopeCounterexample) (L : ℕ) where
  chosen : ConstantSlopeFactorOf C₀
  minimal : ∀ F : ConstantSlopeFactorOf C₀,
    returnedSquareFixedCount L chosen ≤ returnedSquareFixedCount L F

/-- The nonempty natural-number family of fixed counts has a least member. -/
theorem extremalFactorChoice_exists
    (C₀ : NormalizedConstantSlopeCounterexample) (L : ℕ) :
    Nonempty (ExtremalFactorChoice C₀ L) := by
  let counts : Set ℕ :=
    Set.range (returnedSquareFixedCount (C₀ := C₀) L)
  have hcounts : counts.Nonempty := by
    exact ⟨returnedSquareFixedCount L (ConstantSlopeFactorOf.refl C₀),
      ⟨ConstantSlopeFactorOf.refl C₀, rfl⟩⟩
  have hminimum_mem : sInf counts ∈ counts := Nat.sInf_mem hcounts
  obtain ⟨chosen, hchosen⟩ := hminimum_mem
  refine ⟨⟨chosen, ?_⟩⟩
  intro F
  rw [hchosen]
  exact Nat.sInf_le ⟨F, rfl⟩

/-- Product fixed-point count cannot increase through a common factor. -/
theorem product_fixedCount_nonincreasing
    {C₀ : NormalizedConstantSlopeCounterexample}
    (F : ConstantSlopeFactorOf C₀) :
    (fixedPoints F.system.product).ncard ≤ productFixedCount C₀ := by
  have hexact := fixedPoints_descendExactly_of_monotone_semiconjugacy
    F.factor.continuous_coordinate F.factor.monotone_coordinate
    F.factor.surjective_coordinate
    (C₀.finitePiece_P.continuous.comp C₀.finitePiece_Q.continuous)
    F.factor.intertwines_product
  change (fixedPoints (F.system.P ∘ F.system.Q)).ncard ≤
    productFixedCount C₀
  rw [hexact]
  calc
    (F.factor.coordinate '' fixedPoints (C₀.P ∘ C₀.Q)).ncard ≤
        (fixedPoints (C₀.P ∘ C₀.Q)).ncard :=
      Set.ncard_image_le (product_fixedPoints_finite C₀)
    _ = productFixedCount C₀ := by
      simpa [productFixedCount, productFixedFinset,
        NormalizedConstantSlopeCounterexample.product] using
        Set.ncard_eq_toFinset_card _ (product_fixedPoints_finite C₀)

/-- Minimality of the returned-square count rules out every proper
nondegenerate interval carried onto itself by both returned powers. -/
theorem ExtremalFactorChoice.returnedPowersIrreducible
    {C₀ : NormalizedConstantSlopeCounterexample} {L : ℕ}
    (E : ExtremalFactorChoice C₀ L) (hL : 0 < L) :
    ReturnedPowersIrreducible E.chosen.system.P E.chosen.system.Q L := by
  intro J hJ hPonto hQonto
  by_contra hproper
  obtain ⟨D⟩ := phaseComponentQuotient_exists
    E.chosen.system L hL J hJ hPonto hQonto hproper
  have hdrop := phaseComponentQuotient_strict_descent
    E.chosen.system L hL D
  obtain ⟨R⟩ := constantSlopeRelinearization_exists D.target
  have hnonincrease :=
    relinearization_returnedSquare_count_nonincreasing R L hdrop.1
  let F : ConstantSlopeFactorOf C₀ :=
    { system := R.target
      factor := (E.chosen.factor.comp D.factor).comp R.factor }
  have hminimal := E.minimal F
  have hstrict : returnedSquareFixedCount L F <
      returnedSquareFixedCount L E.chosen := by
    change (fixedPoints (iterateMap R.target.P (2 * L))).ncard <
      (fixedPoints (iterateMap E.chosen.system.P (2 * L))).ncard
    exact hnonincrease.trans_lt hdrop.2
  exact (not_lt_of_ge hminimal) hstrict

/--
Extremal irreducibility with the manuscript's exact normalization:
`ν₀ = # Fix(P₀Q₀)` and `L = (2ν₀)!`.  The selected pair is a common
monotone factor, its product fixed count is at most `ν₀`, and its returned
powers admit no proper common invariant nondegenerate interval.
-/
theorem exists_extremal_normalized_counterexample
    (C₀ : NormalizedConstantSlopeCounterexample) :
    ∃ (C : NormalizedConstantSlopeCounterexample)
      (F : MonotonePairFactor C₀.P C₀.Q C.P C.Q)
      (ν₀ L : ℕ),
      ν₀ = productFixedCount C₀ ∧
      L = Nat.factorial (2 * ν₀) ∧
      (fixedPoints C.product).ncard ≤ ν₀ ∧
      ReturnedPowersIrreducible C.P C.Q L := by
  let L := extremalReturnExponent C₀
  obtain ⟨E⟩ := extremalFactorChoice_exists C₀ L
  refine ⟨E.chosen.system, E.chosen.factor, productFixedCount C₀, L,
    rfl, rfl, product_fixedCount_nonincreasing E.chosen, ?_⟩
  exact E.returnedPowersIrreducible (extremalReturnExponent_pos C₀)

end CommutingIntervalSimplified
