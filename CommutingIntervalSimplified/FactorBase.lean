import CommutingIntervalSimplified.Base

/-!
# Standalone monotone factor and finite interval quotient infrastructure

This module contains the topological quotient vocabulary used by the
simplified proof.  In particular, exact fixed-point descent is proved for an
arbitrary continuous monotone surjective semiconjugacy; it is not an axiom and
does not depend on the earlier formalization.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set

/-! ## Canonical finite interval quotients -/

/-- The union of a finite indexed family of collapsed closed intervals. -/
def collapsedLocus {n : ℕ} (classes : Fin n → ClosedSubinterval) : Set I :=
  ⋃ i, (classes i).carrier

/-- A point lies outside every displayed collapsed interval. -/
def OutsideCollapsedLocus {n : ℕ}
    (classes : Fin n → ClosedSubinterval) (x : I) : Prop :=
  x ∉ collapsedLocus classes

namespace ClosedSubinterval

/-- The open interior of a closed subinterval, relative to `I`. -/
def openCarrier (J : ClosedSubinterval) : Set I :=
  Set.Ioo J.left J.right

end ClosedSubinterval

/-- A maximal nondegenerate complementary gap of a collapsed locus. -/
def IsComplementaryGap {n : ℕ}
    (classes : Fin n → ClosedSubinterval) (J : ClosedSubinterval) : Prop :=
  J.Nondegenerate ∧
    Disjoint J.openCarrier (collapsedLocus classes) ∧
    ∀ K : ClosedSubinterval,
      K.Nondegenerate →
        Disjoint K.openCarrier (collapsedLocus classes) →
        J.carrier ⊆ K.carrier → K.carrier ⊆ J.carrier

/-- An interval map is affine with strictly positive slope on `s`. -/
def IsPositiveAffineOn (π : IntervalMap) (s : Set I) : Prop :=
  ∃ m c : ℝ, 0 < m ∧
    ∀ x ∈ s, (π x : ℝ) = m * (x : ℝ) + c

/--
A nonconstant quotient of `I` by finitely many pairwise-disjoint,
nondegenerate compact interval classes.  `fibre_iff` states that the displayed
classes are exactly all non-singleton fibres.
-/
structure CanonicalFiniteIntervalQuotient where
  toFun : IntervalMap
  continuous_toFun : Continuous toFun
  surjective_toFun : Surjective toFun
  monotone_toFun : Monotone toFun
  nonconstant_toFun : ∃ x y : I, toFun x ≠ toFun y
  collapsedCount : ℕ
  collapsed : Fin collapsedCount → ClosedSubinterval
  collapsed_nondegenerate : ∀ i, (collapsed i).Nondegenerate
  collapsed_pairwise_disjoint :
    ∀ i j, i ≠ j → Disjoint (collapsed i).carrier (collapsed j).carrier
  fibre_iff :
    ∀ x y : I, toFun x = toFun y ↔
      x = y ∨ ∃ i, x ∈ (collapsed i).carrier ∧ y ∈ (collapsed i).carrier
  finitePiecePL_toFun : FinitePiecePL toFun
  positiveAffineOn_complementaryGap :
    ∀ J : ClosedSubinterval,
      IsComplementaryGap collapsed J → IsPositiveAffineOn toFun J.carrier

instance : CoeFun CanonicalFiniteIntervalQuotient (fun _ => IntervalMap) :=
  ⟨CanonicalFiniteIntervalQuotient.toFun⟩

namespace CanonicalFiniteIntervalQuotient

/-- The union of all nontrivial fibres. -/
def collapsedSet (π : CanonicalFiniteIntervalQuotient) : Set I :=
  collapsedLocus π.collapsed

/-- A source point outside every nontrivial fibre. -/
def IsUncollapsed (π : CanonicalFiniteIntervalQuotient) (x : I) : Prop :=
  x ∉ π.collapsedSet

/-- The fibre through `x`. -/
def fibre (π : CanonicalFiniteIntervalQuotient) (x : I) : Set I :=
  {y | π y = π x}

/-- Every point outside the collapsed locus has a singleton fibre. -/
theorem fibre_eq_singleton_of_isUncollapsed
    (π : CanonicalFiniteIntervalQuotient) {x : I}
    (hx : π.IsUncollapsed x) : π.fibre x = {x} := by
  ext y
  constructor
  · intro hy
    rcases (π.fibre_iff y x).mp hy with hxy | ⟨i, hyi, hxi⟩
    · simp [hxy]
    · exact False.elim (hx (Set.mem_iUnion.mpr ⟨i, hxi⟩))
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    rfl

/-- Each displayed collapsed interval is exactly one fibre. -/
theorem fibre_eq_collapsed
    (π : CanonicalFiniteIntervalQuotient) (i : Fin π.collapsedCount) :
    π.fibre (π.collapsed i).left = (π.collapsed i).carrier := by
  ext x
  have hleft : (π.collapsed i).left ∈ (π.collapsed i).carrier :=
    (π.collapsed i).left_mem_carrier
  constructor
  · intro hx
    rcases (π.fibre_iff x (π.collapsed i).left).mp hx with
      hxi | ⟨j, hxj, hleftj⟩
    · subst x
      exact hleft
    · by_cases hji : j = i
      · simpa [hji] using hxj
      · exact False.elim
          ((Set.disjoint_left.mp
            (π.collapsed_pairwise_disjoint j i hji)) hleftj hleft)
  · intro hx
    exact (π.fibre_iff x (π.collapsed i).left).mpr
      (Or.inr ⟨i, hx, hleft⟩)

end CanonicalFiniteIntervalQuotient

/-! ## Fibre-respecting maps and descents -/

/-- Identified source points remain identified after applying `T`. -/
def RespectsFibres (π T : IntervalMap) : Prop :=
  ∀ ⦃x y : I⦄, π x = π y → π (T x) = π (T y)

/-- The semiconjugacy identity `π ∘ T = Tbar ∘ π`. -/
def Intertwines (π T Tbar : IntervalMap) : Prop :=
  ∀ x : I, π (T x) = Tbar (π x)

/-- `Tbar` is a descended map for `T` along `π`. -/
def IsDescendedMap (π T Tbar : IntervalMap) : Prop :=
  Intertwines π T Tbar

/-- A continuous descended map. -/
def IsContinuousDescendedMap (π T Tbar : IntervalMap) : Prop :=
  Continuous Tbar ∧ IsDescendedMap π T Tbar

/-- Any semiconjugacy makes the source map fibre-respecting. -/
theorem respectsFibres_of_intertwines
    {π T Tbar : IntervalMap} (h : Intertwines π T Tbar) :
    RespectsFibres π T := by
  intro x y hxy
  rw [h x, h y, hxy]

/-- The choice-defined descent of a fibre-respecting map. -/
noncomputable def descendedMap (π : CanonicalFiniteIntervalQuotient)
    (T : IntervalMap) (_hT : RespectsFibres π.toFun T) : IntervalMap :=
  fun y => π (T (Classical.choose (π.surjective_toFun y)))

/-- The choice-defined descent satisfies the semiconjugacy identity. -/
theorem intertwines_descendedMap (π : CanonicalFiniteIntervalQuotient)
    (T : IntervalMap) (hT : RespectsFibres π.toFun T) :
    Intertwines π.toFun T (descendedMap π T hT) := by
  intro x
  apply hT
  exact (Classical.choose_spec (π.surjective_toFun (π x))).symm

/-- A descended map through a surjection is unique. -/
theorem descendedMap_unique {π T F G : IntervalMap}
    (hπ : Surjective π)
    (hF : Intertwines π T F) (hG : Intertwines π T G) : F = G := by
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF x).symm.trans (hG x)

/-- A continuous fibre-respecting map has a continuous descent. -/
theorem continuous_descendedMap
    (π : CanonicalFiniteIntervalQuotient) {T : IntervalMap}
    (hT : Continuous T) (hrespect : RespectsFibres π.toFun T) :
    Continuous (descendedMap π T hrespect) := by
  have hquot : Topology.IsQuotientMap π.toFun :=
    IsQuotientMap.of_surjective_continuous
      π.surjective_toFun π.continuous_toFun
  apply hquot.continuous_iff.mpr
  have heq : descendedMap π T hrespect ∘ π.toFun = π.toFun ∘ T := by
    funext x
    exact (intertwines_descendedMap π T hrespect x).symm
  rw [heq]
  exact π.continuous_toFun.comp hT

/-- Surjectivity descends through a common surjective coordinate. -/
theorem surjective_descendedMap
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hrespect : RespectsFibres π.toFun T) (hT : Surjective T) :
    Surjective (descendedMap π T hrespect) := by
  intro y
  obtain ⟨x, hx⟩ := π.surjective_toFun y
  obtain ⟨z, hz⟩ := hT x
  refine ⟨π z, ?_⟩
  calc
    descendedMap π T hrespect (π z) = π (T z) :=
      (intertwines_descendedMap π T hrespect z).symm
    _ = π x := by rw [hz]
    _ = y := hx

/-- Commutation descends through a common surjective quotient. -/
theorem commute_descendedMap
    (π : CanonicalFiniteIntervalQuotient) (P Q : IntervalMap)
    (hP : RespectsFibres π.toFun P) (hQ : RespectsFibres π.toFun Q)
    (hcomm : Function.Commute P Q) :
    Function.Commute (descendedMap π P hP) (descendedMap π Q hQ) := by
  intro y
  obtain ⟨x, rfl⟩ := π.surjective_toFun y
  let Pbar := descendedMap π P hP
  let Qbar := descendedMap π Q hQ
  have hPbar := intertwines_descendedMap π P hP
  have hQbar := intertwines_descendedMap π Q hQ
  change Pbar (Qbar (π x)) = Qbar (Pbar (π x))
  calc
    Pbar (Qbar (π x)) = Pbar (π (Q x)) :=
      congrArg Pbar (hQbar x).symm
    _ = π (P (Q x)) := (hPbar (Q x)).symm
    _ = π (Q (P x)) := congrArg π.toFun (hcomm x)
    _ = Qbar (π (P x)) := hQbar (P x)
    _ = Qbar (Pbar (π x)) := congrArg Qbar (hPbar x)

/-! ## Fixed components and positive words -/

/-- Every point of `J` is fixed by `T`. -/
def IsFixedInterval (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  J.carrier ⊆ fixedPoints T

/-- A maximal closed interval contained in the fixed-point set. -/
def IsFixedComponent (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  IsFixedInterval T J ∧
    ∀ K : ClosedSubinterval,
      IsFixedInterval T K → J.carrier ⊆ K.carrier → K.carrier ⊆ J.carrier

/-- A nondegenerate interval component of the fixed-point set. -/
def IsNondegenerateFixedComponent
    (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  J.Nondegenerate ∧ IsFixedComponent T J

/-- The displayed classes are exactly the nondegenerate fixed components. -/
def CollapsesExactlyFixedComponents
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap) : Prop :=
  (∀ i, IsNondegenerateFixedComponent T (π.collapsed i)) ∧
    ∀ J : ClosedSubinterval,
      IsNondegenerateFixedComponent T J →
        ∃ i, J.carrier = (π.collapsed i).carrier

/-- The word `P^r Q^s`, in manuscript composition order. -/
def positiveWordMap (P Q : IntervalMap) (r s : ℕ) : IntervalMap :=
  fun x => iterateMap P r (iterateMap Q s x)

/-- A quotient collapsing the fixed components of a genuinely positive word. -/
def IsPositiveWordFixedComponentCollapse
    (π : CanonicalFiniteIntervalQuotient) (P Q : IntervalMap)
    (r s : ℕ) : Prop :=
  0 < r ∧ 0 < s ∧
    CollapsesExactlyFixedComponents π (positiveWordMap P Q r s)

/-- The exact fixed-set image identity under a factor. -/
def FixedPointsDescendExactly (π T Tbar : IntervalMap) : Prop :=
  fixedPoints Tbar = π '' fixedPoints T

/-- A fibre identifies two distinct fixed points of `T`. -/
def IdentifiesDistinctFixedPoints (π T : IntervalMap) : Prop :=
  ∃ x y : I,
    x ∈ fixedPoints T ∧ y ∈ fixedPoints T ∧ x ≠ y ∧ π x = π y

/-- Both fixed sets are finite and the descended count does not increase. -/
def FixedPointCardinalityNonincreasing (T Tbar : IntervalMap) : Prop :=
  (fixedPoints T).Finite ∧
    (fixedPoints Tbar).Finite ∧
    (fixedPoints Tbar).ncard ≤ (fixedPoints T).ncard

/-- Both fixed sets are finite and the descended count strictly decreases. -/
def FixedPointCardinalityDrops (T Tbar : IntervalMap) : Prop :=
  (fixedPoints T).Finite ∧
    (fixedPoints Tbar).Finite ∧
    (fixedPoints Tbar).ncard < (fixedPoints T).ncard

/-- Intertwining is preserved by iteration. -/
theorem intertwines_iterateMap
    {π T Tbar : IntervalMap} (h : Intertwines π T Tbar) (n : ℕ) :
    Intertwines π (iterateMap T n) (iterateMap Tbar n) := by
  intro x
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      calc
        π (iterateMap T n.succ x) = π (T (iterateMap T n x)) := by
          simp only [iterateMap, Function.iterate_succ_apply']
        _ = Tbar (π (iterateMap T n x)) := h (iterateMap T n x)
        _ = Tbar (iterateMap Tbar n (π x)) := congrArg Tbar (ih x)
        _ = iterateMap Tbar n.succ (π x) := by
          simp only [iterateMap, Function.iterate_succ_apply']

/-- Intertwining each generator intertwines every positive word. -/
theorem intertwines_positiveWordMap
    {π P Q Pbar Qbar : IntervalMap}
    (hP : Intertwines π P Pbar) (hQ : Intertwines π Q Qbar)
    (r s : ℕ) :
    Intertwines π (positiveWordMap P Q r s)
      (positiveWordMap Pbar Qbar r s) := by
  have hPr := intertwines_iterateMap hP r
  have hQs := intertwines_iterateMap hQ s
  intro x
  calc
    π (positiveWordMap P Q r s x) =
        iterateMap Pbar r (π (iterateMap Q s x)) :=
      hPr (iterateMap Q s x)
    _ = iterateMap Pbar r (iterateMap Qbar s (π x)) :=
      congrArg (iterateMap Pbar r) (hQs x)
    _ = positiveWordMap Pbar Qbar r s (π x) := rfl

/-- A positive word in continuous maps is continuous. -/
theorem continuous_positiveWordMap
    {P Q : IntervalMap} (hP : Continuous P) (hQ : Continuous Q)
    (r s : ℕ) : Continuous (positiveWordMap P Q r s) := by
  exact (IntervalMap.continuous_iterate hP r).comp
    (IntervalMap.continuous_iterate hQ s)

/-! ## Compact interval fibres and exact fixed-point descent -/

/-- A monotone surjective coordinate has a closed-interval fibre at `y`. -/
structure MonotoneFibreIntervalData
    (π : IntervalMap) (y : I) where
  interval : ClosedSubinterval
  carrier_eq : interval.carrier = {x : I | π x = y}

/-- Every fibre of a continuous monotone surjective interval map is a
nonempty compact interval. -/
theorem monotoneFibreInterval_exists
    (π : IntervalMap) (hπcont : Continuous π) (hπmono : Monotone π)
    (hπsurj : Surjective π) (y : I) :
    Nonempty (MonotoneFibreIntervalData π y) := by
  let fibre : Set I := {x : I | π x = y}
  have hfibre_nonempty : fibre.Nonempty := hπsurj y
  have hfibre_closed : IsClosed fibre := by
    exact isClosed_eq hπcont continuous_const
  have hfibre_compact : IsCompact fibre := hfibre_closed.isCompact
  obtain ⟨l, hl, hlmin⟩ := hfibre_compact.exists_isMinOn
    hfibre_nonempty continuous_id.continuousOn
  obtain ⟨r, hr, hrmax⟩ := hfibre_compact.exists_isMaxOn
    hfibre_nonempty continuous_id.continuousOn
  have hlr : l ≤ r := hlmin hr
  let J : ClosedSubinterval :=
    { left := l
      right := r
      left_le_right := hlr }
  have hcarrier : J.carrier = fibre := by
    change Set.Icc l r = fibre
    apply Set.Subset.antisymm
    · intro z hz
      have hlπz := hπmono hz.1
      have hzπr := hπmono hz.2
      have hlcoord : π l = y := hl
      have hrcoord : π r = y := hr
      change π z = y
      apply le_antisymm
      · rw [hrcoord] at hzπr
        exact hzπr
      · rw [hlcoord] at hlπz
        exact hlπz
    · intro z hz
      exact ⟨hlmin hz, hrmax hz⟩
  exact ⟨⟨J, hcarrier⟩⟩

/--
Every fixed point downstairs lifts to a fixed point in its compact interval
fibre.  Thus fixed sets descend exactly through any continuous monotone
surjective semiconjugacy.
-/
theorem fixedPoints_descendExactly_of_monotone_semiconjugacy
    {π T Tbar : IntervalMap}
    (hπcont : Continuous π) (hπmono : Monotone π)
    (hπsurj : Surjective π) (hTcont : Continuous T)
    (hintertwines : Intertwines π T Tbar) :
    FixedPointsDescendExactly π T Tbar := by
  ext y
  constructor
  · intro hy
    change Tbar y = y at hy
    obtain ⟨D⟩ := monotoneFibreInterval_exists π hπcont hπmono hπsurj y
    have hmaps : MapsTo T D.interval.carrier D.interval.carrier := by
      intro z hz
      rw [D.carrier_eq] at hz ⊢
      calc
        π (T z) = Tbar (π z) := hintertwines z
        _ = Tbar y := congrArg Tbar hz
        _ = y := hy
    obtain ⟨z, hz, hzfix⟩ :=
      exists_mem_Icc_isFixedPt_of_mapsTo
        hTcont.continuousOn D.interval.left_le_right hmaps
    refine ⟨z, ?_, ?_⟩
    · exact hzfix
    · have hz' : z ∈ D.interval.carrier := hz
      rw [D.carrier_eq] at hz'
      exact hz'
  · rintro ⟨x, hxfix, rfl⟩
    change Tbar (π x) = π x
    rw [← hintertwines x, hxfix]

/-- A continuous map has exact fixed descent through a canonical quotient. -/
theorem fixedPoints_descendedMap_exact
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hT : Continuous T) (hrespect : RespectsFibres π.toFun T) :
    FixedPointsDescendExactly π.toFun T (descendedMap π T hrespect) := by
  exact fixedPoints_descendExactly_of_monotone_semiconjugacy
    π.continuous_toFun π.monotone_toFun π.surjective_toFun hT
    (intertwines_descendedMap π T hrespect)

/-- Exact descent of a finite fixed set cannot increase its cardinality. -/
theorem fixedPointCardinalityNonincreasing_of_exact_image
    (π T Tbar : IntervalMap)
    (hexact : FixedPointsDescendExactly π T Tbar)
    (hfinite : (fixedPoints T).Finite) :
    FixedPointCardinalityNonincreasing T Tbar := by
  have hbarfinite : (fixedPoints Tbar).Finite := by
    rw [hexact]
    exact hfinite.image π
  refine ⟨hfinite, hbarfinite, ?_⟩
  rw [hexact]
  exact Set.ncard_image_le hfinite

/-- Identifying two fixed points makes the finite fixed count drop strictly. -/
theorem fixedPointCardinalityDrops_of_exact_image
    (π T Tbar : IntervalMap)
    (hexact : FixedPointsDescendExactly π T Tbar)
    (hidentifies : IdentifiesDistinctFixedPoints π T)
    (hfinite : (fixedPoints T).Finite) :
    FixedPointCardinalityDrops T Tbar := by
  have hbarfinite : (fixedPoints Tbar).Finite := by
    rw [hexact]
    exact hfinite.image π
  refine ⟨hfinite, hbarfinite, ?_⟩
  have himage_lt : (π '' fixedPoints T).ncard <
      (fixedPoints T).ncard := by
    have hle := Set.ncard_image_le (f := π) hfinite
    apply lt_of_le_of_ne hle
    intro heq
    have hinjective : Set.InjOn π (fixedPoints T) :=
      Set.injOn_of_ncard_image_eq heq hfinite
    obtain ⟨x, y, hx, hy, hxy, hπxy⟩ := hidentifies
    exact hxy (hinjective hx hy hπxy)
  rw [hexact]
  exact himage_lt

/-! ## Common monotone factors -/

/-- A common monotone factor from `(P,Q)` to `(Pbar,Qbar)`. -/
structure MonotonePairFactor
    (P Q Pbar Qbar : IntervalMap) where
  coordinate : IntervalMap
  continuous_coordinate : Continuous coordinate
  monotone_coordinate : Monotone coordinate
  surjective_coordinate : Surjective coordinate
  intertwines_P : Intertwines coordinate P Pbar
  intertwines_Q : Intertwines coordinate Q Qbar

namespace MonotonePairFactor

/-- The identity common factor. -/
def refl (P Q : IntervalMap) : MonotonePairFactor P Q P Q where
  coordinate := id
  continuous_coordinate := continuous_id
  monotone_coordinate := monotone_id
  surjective_coordinate := surjective_id
  intertwines_P := by intro x; rfl
  intertwines_Q := by intro x; rfl

/-- Common monotone factors compose. -/
def comp
    {P Q P₁ Q₁ P₂ Q₂ : IntervalMap}
    (F₁ : MonotonePairFactor P Q P₁ Q₁)
    (F₂ : MonotonePairFactor P₁ Q₁ P₂ Q₂) :
    MonotonePairFactor P Q P₂ Q₂ where
  coordinate := F₂.coordinate ∘ F₁.coordinate
  continuous_coordinate :=
    F₂.continuous_coordinate.comp F₁.continuous_coordinate
  monotone_coordinate :=
    F₂.monotone_coordinate.comp F₁.monotone_coordinate
  surjective_coordinate :=
    F₂.surjective_coordinate.comp F₁.surjective_coordinate
  intertwines_P := by
    intro x
    change F₂.coordinate (F₁.coordinate (P x)) =
      P₂ (F₂.coordinate (F₁.coordinate x))
    rw [F₁.intertwines_P, F₂.intertwines_P]
  intertwines_Q := by
    intro x
    change F₂.coordinate (F₁.coordinate (Q x)) =
      Q₂ (F₂.coordinate (F₁.coordinate x))
    rw [F₁.intertwines_Q, F₂.intertwines_Q]

/-- A common pair factor intertwines the two products. -/
theorem intertwines_product
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar) :
    Intertwines F.coordinate (P ∘ Q) (Pbar ∘ Qbar) := by
  intro x
  change F.coordinate (P (Q x)) = Pbar (Qbar (F.coordinate x))
  rw [F.intertwines_P, F.intertwines_Q]

/-- A common factor intertwines iterates of its first generator. -/
theorem intertwines_iterate_P
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar) (n : ℕ) :
    Intertwines F.coordinate (iterateMap P n) (iterateMap Pbar n) :=
  intertwines_iterateMap F.intertwines_P n

/-- A common factor intertwines iterates of its second generator. -/
theorem intertwines_iterate_Q
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar) (n : ℕ) :
    Intertwines F.coordinate (iterateMap Q n) (iterateMap Qbar n) :=
  intertwines_iterateMap F.intertwines_Q n

/-- A common factor intertwines every positive word. -/
theorem intertwines_positiveWord
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar) (r s : ℕ) :
    Intertwines F.coordinate (positiveWordMap P Q r s)
      (positiveWordMap Pbar Qbar r s) :=
  intertwines_positiveWordMap F.intertwines_P F.intertwines_Q r s

/-- Every positive word has exact fixed descent through a common factor. -/
theorem fixedPoints_positiveWord_descendExactly
    {P Q Pbar Qbar : IntervalMap}
    (F : MonotonePairFactor P Q Pbar Qbar)
    (hPcont : Continuous P) (hQcont : Continuous Q) (r s : ℕ) :
    FixedPointsDescendExactly F.coordinate
      (positiveWordMap P Q r s) (positiveWordMap Pbar Qbar r s) := by
  exact fixedPoints_descendExactly_of_monotone_semiconjugacy
    F.continuous_coordinate F.monotone_coordinate
    F.surjective_coordinate (continuous_positiveWordMap hPcont hQcont r s)
    (F.intertwines_positiveWord r s)

end MonotonePairFactor

/-- A canonical quotient and the two choice-defined descents form a common
monotone factor. -/
def descendedMonotonePairFactor
    (π : CanonicalFiniteIntervalQuotient) (P Q : IntervalMap)
    (hP : RespectsFibres π.toFun P) (hQ : RespectsFibres π.toFun Q) :
    MonotonePairFactor P Q (descendedMap π P hP) (descendedMap π Q hQ) where
  coordinate := π.toFun
  continuous_coordinate := π.continuous_toFun
  monotone_coordinate := π.monotone_toFun
  surjective_coordinate := π.surjective_toFun
  intertwines_P := intertwines_descendedMap π P hP
  intertwines_Q := intertwines_descendedMap π Q hQ

end CommutingIntervalSimplified
