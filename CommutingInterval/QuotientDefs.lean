import CommutingInterval.DynamicsDefs

/-!
# Finite interval quotients

This file packages the canonical finite quotients used in the manuscript.
The quotient map has type `I → I`, so its target is the nondegenerate unit
interval.  Consequently `CanonicalFiniteIntervalQuotient` deliberately
excludes the exceptional quotient which collapses all of `I` to one point.
That case is represented separately at the end of the file by a map to
`OnePointInterval`.

The collapsed intervals are part of the data, and `fibre_iff` is an exact
description of every fibre: two points have the same image precisely when
they agree or lie in one displayed collapsed interval.  Thus there are no
hidden nontrivial fibres.
-/

namespace CommutingInterval

open Set Function

/-! ## Collapsed classes and complementary gaps -/

/-- The union of a finite indexed family of collapsed closed intervals. -/
def collapsedLocus {n : ℕ} (classes : Fin n → ClosedSubinterval) : Set I :=
  ⋃ i, (classes i).carrier

/-- A point lies outside every displayed collapsed interval. -/
def OutsideCollapsedLocus {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (x : I) : Prop :=
  x ∉ collapsedLocus classes

/-- The open interior of a closed subinterval, relative to the order on `I`. -/
def ClosedSubinterval.openCarrier (J : ClosedSubinterval) : Set I :=
  Set.Ioo J.left J.right

/--
`J` is the closure of a complementary gap of the collapsed locus.  Its open
interior misses every collapsed class, and it is maximal among
nondegenerate closed intervals with that property.  Its endpoints may be
ambient endpoints or endpoints of collapsed classes.
-/
def IsComplementaryGap {n : ℕ} (classes : Fin n → ClosedSubinterval)
    (J : ClosedSubinterval) : Prop :=
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

/-! ## Canonical finite interval quotients -/

/--
A nonconstant canonical quotient of `I` by finitely many pairwise-disjoint,
nondegenerate compact interval classes.

The quotient is continuous, onto, and nondecreasing.  Its complete fibre
relation is recorded by `fibre_iff`.  It is finite-piece PL, and on the
closure of every complementary gap its affine slope is positive.  No order
is imposed on the finite index type `Fin collapsedCount`; geometric order is
carried by the interval endpoints themselves.
-/
structure CanonicalFiniteIntervalQuotient where
  /-- The underlying quotient map. -/
  toFun : IntervalMap
  /-- The quotient map is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The quotient map is onto the nondegenerate target `I`. -/
  surjective_toFun : Function.Surjective toFun
  /-- The quotient map is nondecreasing. -/
  monotone_toFun : Monotone toFun
  /-- Explicit nonconstancy; this also records exclusion of the one-point quotient. -/
  nonconstant_toFun : ∃ x y : I, toFun x ≠ toFun y
  /-- The number of nontrivial collapsed classes. -/
  collapsedCount : ℕ
  /-- The finite family of collapsed closed intervals. -/
  collapsed : Fin collapsedCount → ClosedSubinterval
  /-- Every displayed collapsed class is nondegenerate. -/
  collapsed_nondegenerate : ∀ i, (collapsed i).Nondegenerate
  /-- Distinct displayed classes are disjoint, including their endpoints. -/
  collapsed_pairwise_disjoint :
    ∀ i j, i ≠ j → Disjoint (collapsed i).carrier (collapsed j).carrier
  /--
  Exact fibre characterization: the displayed intervals are all and only the
  non-singleton fibres.
  -/
  fibre_iff :
    ∀ x y : I, toFun x = toFun y ↔
      x = y ∨ ∃ i, x ∈ (collapsed i).carrier ∧ y ∈ (collapsed i).carrier
  /-- A finite polygonal presentation of the quotient map. -/
  finitePiecePL_toFun : FinitePiecePL toFun
  /-- Every complementary gap is affine with positive slope. -/
  positiveAffineOn_complementaryGap :
    ∀ J : ClosedSubinterval,
      IsComplementaryGap collapsed J → IsPositiveAffineOn toFun J.carrier

instance : CoeFun CanonicalFiniteIntervalQuotient (fun _ => IntervalMap) :=
  ⟨CanonicalFiniteIntervalQuotient.toFun⟩

namespace CanonicalFiniteIntervalQuotient

/-- The union of all nontrivial fibres of a canonical quotient. -/
def collapsedSet (π : CanonicalFiniteIntervalQuotient) : Set I :=
  collapsedLocus π.collapsed

/-- A point of the source lies outside every nontrivial fibre. -/
def IsUncollapsed (π : CanonicalFiniteIntervalQuotient) (x : I) : Prop :=
  x ∉ π.collapsedSet

/-- The fibre of `π` over the image of `x`. -/
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
  have hleft : (π.collapsed i).left ∈ (π.collapsed i).carrier := by
    exact ⟨le_rfl, (π.collapsed i).left_le_right⟩
  constructor
  · intro hx
    rcases (π.fibre_iff x (π.collapsed i).left).mp hx with hxi | ⟨j, hxj, hleftj⟩
    · simpa [hxi] using hleft
    · by_cases hji : j = i
      · simpa [hji] using hxj
      · exact False.elim
          ((Set.disjoint_left.mp (π.collapsed_pairwise_disjoint j i hji)) hleftj hleft)
  · intro hx
    exact (π.fibre_iff x (π.collapsed i).left).mpr
      (Or.inr ⟨i, hx, hleft⟩)

end CanonicalFiniteIntervalQuotient

/-! ## Fibre-respecting maps and descents -/

/--
`T` respects the fibres of `π`: points identified by the quotient remain
identified after applying `T`.
-/
def RespectsFibres (π T : IntervalMap) : Prop :=
  ∀ ⦃x y : I⦄, π x = π y → π (T x) = π (T y)

/-- The intertwining identity `π ∘ T = Tbar ∘ π`. -/
def Intertwines (π T Tbar : IntervalMap) : Prop :=
  ∀ x : I, π (T x) = Tbar (π x)

/-- `Tbar` is a descended map for `T` along `π`. -/
def IsDescendedMap (π T Tbar : IntervalMap) : Prop :=
  Intertwines π T Tbar

/-- `Tbar` is a continuous descended map for `T` along `π`. -/
def IsContinuousDescendedMap (π T Tbar : IntervalMap) : Prop :=
  Continuous Tbar ∧ IsDescendedMap π T Tbar

/--
The choice-defined descent of a fibre-respecting map through a canonical
finite quotient.  Later results prove its continuity and regularity; those
properties are intentionally not built into this definition.
-/
noncomputable def descendedMap (π : CanonicalFiniteIntervalQuotient)
    (T : IntervalMap) (_hT : RespectsFibres π.toFun T) : IntervalMap :=
  fun y => π (T (Classical.choose (π.surjective_toFun y)))

/-- The choice-defined descended map satisfies the intertwining identity. -/
theorem intertwines_descendedMap (π : CanonicalFiniteIntervalQuotient)
    (T : IntervalMap) (hT : RespectsFibres π.toFun T) :
    Intertwines π.toFun T (descendedMap π T hT) := by
  intro x
  apply hT
  exact (Classical.choose_spec (π.surjective_toFun (π x))).symm

/-- A descended map through a surjection is unique. -/
theorem descendedMap_unique {π T F G : IntervalMap}
    (hπ : Function.Surjective π)
    (hF : Intertwines π T F) (hG : Intertwines π T G) : F = G := by
  funext y
  obtain ⟨x, rfl⟩ := hπ y
  exact (hF x).symm.trans (hG x)

/-! ## Fixed-component quotients and fixed-set descent vocabulary -/

/-- Every point of `J` is fixed by `T`. -/
def IsFixedInterval (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  J.carrier ⊆ fixedPoints T

/--
`J` is a maximal closed interval contained in `Fix(T)`.  Singleton
components are allowed here; use `IsNondegenerateFixedComponent` for the
classes collapsed in the manuscript.
-/
def IsFixedComponent (T : IntervalMap) (J : ClosedSubinterval) : Prop :=
  IsFixedInterval T J ∧
    ∀ K : ClosedSubinterval,
      IsFixedInterval T K →
        J.carrier ⊆ K.carrier → K.carrier ⊆ J.carrier

/-- A nondegenerate interval component of `Fix(T)`. -/
def IsNondegenerateFixedComponent (T : IntervalMap)
    (J : ClosedSubinterval) : Prop :=
  J.Nondegenerate ∧ IsFixedComponent T J

/--
The displayed collapsed classes are exactly the nondegenerate interval
components of `Fix(T)`.
-/
def CollapsesExactlyFixedComponents
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap) : Prop :=
  (∀ i, IsNondegenerateFixedComponent T (π.collapsed i)) ∧
    ∀ J : ClosedSubinterval,
      IsNondegenerateFixedComponent T J →
        ∃ i, J.carrier = (π.collapsed i).carrier

/-- The positive commuting word `P^r Q^s`, using the manuscript's composition order. -/
def positiveWordMap (P Q : IntervalMap) (r s : ℕ) : IntervalMap :=
  fun x => iterateMap P r (iterateMap Q s x)

/-- A fixed-component quotient for a word with two genuinely positive exponents. -/
def IsPositiveWordFixedComponentCollapse
    (π : CanonicalFiniteIntervalQuotient) (P Q : IntervalMap)
    (r s : ℕ) : Prop :=
  0 < r ∧ 0 < s ∧
    CollapsesExactlyFixedComponents π (positiveWordMap P Q r s)

/-- The exact fixed-set identity required by the quotient package. -/
def FixedPointsDescendExactly (π T Tbar : IntervalMap) : Prop :=
  fixedPoints Tbar = π '' fixedPoints T

/-- A quotient fibre identifies two distinct fixed points of `T`. -/
def IdentifiesDistinctFixedPoints (π T : IntervalMap) : Prop :=
  ∃ x y : I,
    x ∈ fixedPoints T ∧ y ∈ fixedPoints T ∧ x ≠ y ∧ π x = π y

/-- Both fixed sets are finite and the descended fixed count does not increase. -/
def FixedPointCardinalityNonincreasing (T Tbar : IntervalMap) : Prop :=
  (fixedPoints T).Finite ∧
    (fixedPoints Tbar).Finite ∧
    (fixedPoints Tbar).ncard ≤ (fixedPoints T).ncard

/-- Both fixed sets are finite and the descended fixed count strictly decreases. -/
def FixedPointCardinalityDrops (T Tbar : IntervalMap) : Prop :=
  (fixedPoints T).Finite ∧
    (fixedPoints Tbar).Finite ∧
    (fixedPoints Tbar).ncard < (fixedPoints T).ncard

/-! ## The excluded one-point target -/

/-- A genuine one-point interval target for the quotient collapsing all of `I`. -/
abbrev OnePointInterval := PUnit

/-- The unique map which collapses the whole unit interval to one point. -/
def wholeIntervalPointQuotient : I → OnePointInterval :=
  fun _ => PUnit.unit

/--
A predicate for a quotient to the genuine one-point target.  It is kept
separate because no constant map `I → I` is surjective, whereas the canonical
finite quotients above are required to be onto `I`.
-/
def IsDegeneratePointQuotient (π : I → OnePointInterval) : Prop :=
  Continuous π ∧ Function.Surjective π ∧ ∀ x y : I, π x = π y

end CommutingInterval
