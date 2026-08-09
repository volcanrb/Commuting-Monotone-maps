# Audit of `common_fixed_points_piecewise_monotone_direct.tex`

Audit snapshot: 2026-08-08, mathlib/Lean `v4.30.0`.

> **Archival snapshot.** This document records the state before the direct
> proof was completed and the source tree was pruned on 2026-08-09. Its
> references to a “current project,” active skeletons, private legacy modules,
> and missing proof boundaries are historical, not descriptions of the
> present 40-file zero-hole tree. See `FORMALIZATION_PLAN.md` and
> `AXIOM_AUDIT.md` for the current status.

This audit is deliberately about what can be checked by Lean's kernel.  A
published theorem may guide a proof, but it cannot be introduced as an
`axiom` under the project's acceptance criterion.  Every item below therefore
distinguishes a mathematically correct citation from a theorem which is
already formalized.

## Executive conclusion

The new reduction is mathematically plausible and substantially cleaner than
trying to extend every part of the old tame proof directly to arbitrary
piecewise-monotone maps.  Its terminal fiber argument is sound.  It is not,
however, a short wrapper around the current Lean tree.  There are four new or
newly exposed critical paths.

1. **Bogatyi--Frolkina is absent.**  Mathlib has general topological-entropy
   definitions, but no theorem relating commuting interval maps, common fixed
   points, interval horseshoes, or lap growth.  The current project has no BF
   theorem either.
2. **Alsedà--Misiurewicz is absent.**  Neither mathlib nor the project has the
   positive-entropy semiconjugacy theorem for a non-strict finite-piece
   piecewise-monotone map.  The existing `ParryExistence` development is close
   in spirit, but assumes finitely many *strict* laps and transitivity.
3. **The manuscript's simultaneous-eigenmeasure proof invokes an unavailable
   fixed-point theorem, but it can be deleted.**  The local mathlib checkout
   has no Brouwer or Schauder theorem.  Complexifying the finite-dimensional
   expanding eigenspace, taking an ordinary complex eigenvector of
   `transfer P`, and then taking its total variation produces the required
   positive simultaneous eigenmeasure.  Exact naturality of variation under
   the plateau-aware transfer is the key new lemma.  It follows because
   plateau values are countable and the assigned branch cells are disjoint.
4. **The old piecewise-linear core is not exposed as an unconditional Lean
   theorem.**  `Main.tame_C1_common_fixed_point` requires a value of the
   abstract structure `OMinimalExpansion`.  The project constructs no concrete
   such value.  Although `finitePieceC1_of_finitePiecePL` exists, it is private
   and still needs an expansion value.  Thus the descended PL pair cannot yet
   be handed to the old final theorem.

The recommended kernel route is therefore:

* formalize a direct BF **horseshoe** consequence, not topological entropy;
* extract/generalize the existing lap-resolvent construction to produce one
  expanding compatible monotone coordinate from that horseshoe, avoiding the
  equality `lambda = exp(h_top)` entirely;
* prove exact total-variation naturality for the complexified transfer and use
  algebraic closure of `Complex` on the finite-dimensional eigenspace;
* refactor the earlier proof to expose an unconditional
  `FinitePiecePL` common-fixed-point theorem;
* then carry out the common distribution quotient and minimal-fiber descent.

This route proves exactly what the new manuscript uses.  It avoids formalizing
the full theory of topological entropy and avoids constructing a concrete
o-minimal expansion of the real field.

## What is and is not present

### Mathlib

Mathlib `v4.30.0` contains general cover/net topological entropy in
`Mathlib.Dynamics.TopologicalEntropy`, with values in `EReal`.  It does **not**
contain any of the following:

* the Bogatyi--Frolkina theorem;
* an interval-map entropy/lap-number equivalence;
* a positive-entropy interval horseshoe theorem specialized enough for this
  proof;
* the Alsedà--Misiurewicz or Milnor--Thurston constant-slope semiconjugacy;
* a general Brouwer or Schauder fixed-point theorem.

It does contain useful infrastructure which should be reused:

* Lusin--Souslin (`MeasurableSet.image_of_measurable_injOn` and related
  declarations in `MeasureTheory.Constructions.Polish.Basic`);
* finite signed measures as `MeasureTheory.SignedMeasure`;
* Jordan decomposition and total variation;
* Stieltjes measures;
* finite-dimensional linear algebra and Euclidean compactness;
* Arzelà--Ascoli and compact subsequence extraction, if the fallback AM route
  becomes necessary.

### Current project

The closest existing modules are:

* `CommutingInterval/ParryTransfer.lean`: a cover-independent transfer
  operator for finite **injective** covers and its composition law;
* `CommutingInterval/ParryExistence.lean`: horseshoe-to-lap-growth,
  convergence-radius, normalized lap-resolvent, monotone coordinate, and
  scaled probability machinery for continuous maps with finitely many strict
  laps; the key reusable declarations are currently private;
* `CommutingInterval/ConstantSlope.lean` and
  `CommutingInterval/Polygonal.lean`: downstream constant-slope facts once a
  strict/full-support coordinate exists;
* `CommutingInterval/QuotientDefs.lean` and
  `CommutingInterval/QuotientLemmas.lean`: finite canonical interval
  quotients.  These do not directly represent the possibly infinite family of
  fibers of a distribution function, but the quotient-map/descent arguments
  can be adapted;
* `CommutingInterval/Normalization.lean`: a correct Zorn/minimal-core proof,
  but packaged for `TameCounterexample` and with its core lemmas private;
* `CommutingInterval/Main.lean`: the old final theorem, conditional on an
  explicitly supplied `OMinimalExpansion`.

At this snapshot, `PiecewiseMonotoneDefs.lean` and
`PiecewiseMonotoneTransfer.lean` are new skeletons under active development.
Their overall interfaces match the recommended lower layers.  They must not
be counted as completed merely because all declarations have been named.

## Audit of the two published inputs

### Bogatyi--Frolkina

The manuscript states:

> If commuting continuous interval maps have no common fixed point, their
> composition has positive topological entropy.

This is supported by the cited paper.  In fact its Theorem 1 gives a uniform
lower bound (using the paper's entropy normalization) and obtains a finite
covering graph with Perron value `4`; positivity is a safe weakening.  The
theorem applies to arbitrary continuous interval self-maps and does not need
piecewise monotonicity or surjectivity.

The citation is mathematically adequate, but it contributes no kernel proof.
Formalizing the exact entropy statement would additionally require relating
the paper's entropy convention to mathlib's `Dynamics.coverEntropy : EReal`,
proving finiteness for finite-piece maps, and formalizing the graph/lap lower
bound.  None of that is needed later.

The exact replacement has now been proved in
`CommutingInterval/PiecewiseMonotoneHorseshoe.lean`; its public geometric
statement is the following strengthening.

```lean
/-- Two separated closed branches whose images cover their common hull. -/
structure TwoBranchHorseshoe (F : IntervalMap) where
  a b c d : I
  a_lt_b : a < b
  b_lt_c : b < c
  c_lt_d : c < d
  left_covers  : Set.Icc a d ⊆ F '' Set.Icc a b
  right_covers : Set.Icc a d ⊆ F '' Set.Icc c d

theorem commuting_noCommonFixedPoint_horseshoe
    {P Q : IntervalMap}
    (hP : Continuous P) (hQ : Continuous Q)
    (hcomm : Commute P Q)
    (hno : ¬ HasCommonFixedPoint P Q) :
    Nonempty (TwoBranchHorseshoe (P ∘ Q))
```

The decisive source inequality is `Q x0 ≥ x1` (not `Q x0 ≤ x1`). Up to
reflection, De Marr gives `x0 < s < x1 < t`, with `P x0=x0`, `P s=t`,
`P x1=x1`, `Q s=s`, `Q t=t`, and `Q x1≤x0`. These relations make both
`[s,x1]` and `[x1,t]` cover `[x0,t]` under `H=P∘Q`; the second covering uses
`Q([x1,t]) ⊇ [x0,t]` and `P([x0,t]) ⊇ [x0,t]`. After trimming the common
endpoint using continuity and absence of a common fixed point, this is a
two-branch horseshoe for `H` itself. No generic covering-graph or return-path
lemma is needed. The article's proof gives the following useful internal
skeleton.

```lean
structure MarrAlternatingConfiguration (P Q : IntervalMap) where
  x0 s x1 t : I
  x0_lt_s : x0 < s
  s_lt_x1 : s < x1
  x1_lt_t : x1 < t
  -- alternating fixed-point and crossing data, with orientation reflected
  -- once if necessary
  ...

theorem marr_configuration_of_commuting_noCommonFixedPoint ... :
  Nonempty (MarrAlternatingConfiguration P Q)

theorem commuting_noCommonFixedPoint_horseshoe ... :
  Nonempty (TwoBranchHorseshoe (P ∘ Q))
```

The first of these is the substantive BF interval-order lemma.  It should be
proved directly with fixed sets, extrema, commutation, and the intermediate
value theorem. The second is interval order, IVT, and the strict-separation
trimming argument. Stating only `0 < coverEntropy` would hide these actual
dependencies and would still leave the semiconjugacy proof needing lap
growth. The direct module is kernel-checked with zero placeholders/project
axioms; its axiom report is exactly `propext`, `Classical.choice`, and
`Quot.sound`.

### Alsedà--Misiurewicz

The cited Theorem A says that a finite-piece piecewise continuous,
piecewise-monotone map of positive entropy is semiconjugate by an increasing
continuous surjection to a map of constant slope, and the semiconjugacy is
`f`-compatible.  Their class `PM` explicitly distinguishes monotone from
strictly monotone maps.  Their preliminary reduction collapses non-strict
pieces.  Formula (2) in the paper is exactly the interval scaling used in the
manuscript:

```text
|psi (H y) - psi (H x)| = lambda * |psi y - psi x|
```

whenever `H` is continuous and monotone on `[x,y]`.  For a plateau this forces
`psi` to be constant on the plateau.  For continuous `H`, the descended
constant-slope model is continuous across adjacent lap images.  Thus the
manuscript's formulation is substantively correct.  Saying “nonzero slopes
have absolute value `lambda`” is slightly weaker than the paper's
constant-slope conclusion and is harmless.

Again, no Lean proof exists.  The full entropy-indexed statement would be:

```lean
structure CompatibleConstantSlopeModel (H : IntervalMap) (lambda : ℝ) where
  coordinate : IntervalMap
  model : IntervalMap
  coordinate_continuous : Continuous coordinate
  coordinate_monotone : Monotone coordinate
  coordinate_surjective : Function.Surjective coordinate
  model_piecewiseLinear : FinitePiecePL model
  intertwines : coordinate ∘ H = model ∘ coordinate
  branch_scaling :
    ∀ (w : MonotonicityPartition H) {a b : ℝ},
      w.partition.Adjacent a b → ∀ x y : I,
      x ∈ intervalCell a b → y ∈ intervalCell a b → x ≤ y →
      |(coordinate (H y) : ℝ) - coordinate (H x)| =
        lambda * |(coordinate y : ℝ) - coordinate x|

theorem alsedaMisiurewicz_constantSlope
    {H : IntervalMap} (hH : FinitePieceMonotone H)
    (hent : 0 < Dynamics.coverEntropy H Set.univ) :
    ∃ lambda : ℝ, 1 < lambda ∧
      Nonempty (CompatibleConstantSlopeModel H lambda)
```

That is not the recommended formal target.  The proof only consumes some
`lambda > 1` and the branch-scaling coordinate; it never consumes the equality
with `exp(h_top)`.  The shorter target is:

```lean
theorem expandingCompatibleCoordinate_of_horseshoe
    {H : IntervalMap} (hH : FinitePieceMonotone H)
    {N : ℕ} (hN : 0 < N)
    (horse : TwoBranchHorseshoe (iterateMap H N)) :
    ∃ lambda : ℝ, 1 < lambda ∧
      Nonempty (CompatibleConstantSlopeModel H lambda)
```

This theorem is the correct bridge between BF and the transfer argument.  It
can be proved by a generalized Parry lap-resolvent.  It is strictly less work
than formalizing the full AM theorem because it avoids:

* a definition-level comparison of entropy conventions;
* the Misiurewicz--Szlenk entropy/lap formula;
* entropy lower semicontinuity under Markov approximation;
* proving the final slope is exactly `exp(h_top)`.

## Concrete Parry extraction/generalization plan

The following declarations in `ParryExistence.lean` are currently private and
encode the reusable analytic pattern:

* `ParryTwoBranchHorseshoe` and `.fibre_lower`;
* `ParryLapGrowthData`;
* `ParryRadiusData` and `parryRadiusData_exists_of_growth`;
* `ParryLapLimitData` and `parryLapLimitData_exists`;
* `ParryResolventCoordinateData` and
  `parryResolventCoordinateData_exists`;
* `parryNormalizedLapResolvent_bounds` and
  `parryNormalizedLapResolvent_mono`;
* `parryNormalized_adjacent_error` and the cut-free small-interval estimates;
* `parryNormalized_cumulative_subsequence_exists`;
* `parryLapLimit_strictMonotone_scaling`;
* `parryResolventCoordinate_map_eq_on_cell` and
  `parryResolventCoordinate_map_eq_of_eq`.

They should not simply all be made public with their present statements.  The
present cut set and lap count rely on strict laps and finite iterate fibers.
For weak monotonicity a fiber can be an interval and can be infinite.  The
generalization boundary should be an abstract/local lap-count interface:

```lean
structure WeakLapResolventInput (H : IntervalMap) where
  countOn : I → I → ℕ → ℕ
  totalCount : ℕ → ℕ
  countOn_le_total : ...
  interval_monotone : ...
  adjacent_add_error : ...
  branch_shift_error : ...
  submultiplicative : ∀ m n,
    totalCount (m + n) ≤ totalCount m * totalCount n
  exponential_upper : ∃ q > 0, ∀ n, totalCount n ≤ q ^ n
  horseshoe_lower : ∃ N > 0, ∀ k, 2 ^ k ≤ totalCount (N * k)
```

There are two viable implementations of this interface.

1. Define the weak lap number as the minimum size of a finite closed-cell
   weak-monotonicity partition, and define its localized version on a closed
   interval.  Composition gives submultiplicativity; a chosen original
   partition gives an exponential upper bound; the horseshoe gives the lower
   bound.  The main cost is proving adjacent and branch-shift estimates for
   the minimal localized number.
2. Use a canonical itinerary refinement of one chosen finite partition.
   An `n`-word indexes the intersection of successive inverse images of the
   assigned cells.  On every nonempty itinerary cell, `H^n` is weakly
   monotone.  There are at most `m^n` cells.  Count nonempty itinerary cells
   meeting `[x,y]`, quotienting duplicate cells created by plateau fibers if
   needed.  This avoids a minimization API but requires careful duplicate and
   endpoint bookkeeping.

The analytic radius construction
`parryRadiusData_exists_of_growth` is almost reusable verbatim once supplied
with the abstract counts.  The diagonal compactness and monotone-coordinate
construction are also reusable.  The strict branch scaling lemma must become
a weak branch lemma:

```lean
theorem weakLapLimit_scaling
    (hmono : IsWeaklyMonotoneOn H (Set.Icc x y)) :
    L.value x y = R.radius * L.value (min (H x) (H y)) (max (H x) (H y))
```

In the constant case the target interval is a singleton and both sides must
be shown zero.  The resulting coordinate is only nondecreasing, not strict;
that is exactly what the new reduction requires.  Define its Stieltjes
measure directly rather than pulling Lebesgue measure back through a
homeomorphism.  The current private theorem
`parryScaledProbability_exists_of_resolventCoordinate` is therefore the wrong
last step and should be split into:

* construction and endpoint normalization of a continuous monotone
  coordinate;
* Stieltjes interval-increment formula;
* branchwise scaling and transfer-eigenmeasure;
* construction of the descended finite-piece PL model.

Estimated proof cost: a few thousand lines of interval/counting work, while
retaining the existing analytic convergence proof.  By comparison, a faithful
formalization of the published AM proof also needs finite Markov
approximations, Perron--Frobenius matrices, entropy comparison, equicontinuity,
and Arzelà--Ascoli.  Almost none of its entropy interface exists locally.
Unless the weak-lap adjacent estimate proves unexpectedly false, the Parry
generalization is the lower-risk route.

## Honest statements for the new measure layer

The following is a suitable exact type for the manuscript's vector space.

```lean
def SignedNoAtoms (sigma : MeasureTheory.SignedMeasure I) : Prop :=
  ∀ x : I, sigma {x} = 0

def NonatomicSignedMeasure : Submodule ℝ (MeasureTheory.SignedMeasure I) := ...
```

### Image measures on a monotone branch

```lean
theorem monotoneBranchImageSigned_exists
    {u : IntervalMap} {D : Set I}
    (hD : MeasurableSet D)
    (hu : IsWeaklyMonotoneOn u D)
    (sigma : NonatomicSignedMeasure) :
    ∃ tau : NonatomicSignedMeasure,
      ∀ E, MeasurableSet E → tau.1 E = sigma.1 (u '' (E ∩ D))
```

Dependencies/blockers:

* countability of nondegenerate fiber values (choose a rational in each
  disjoint fiber interior);
* Lusin--Souslin on the complement of those fibers;
* a signed nonatomic measure vanishes on countable sets;
* countable additivity after removing the countable overlap set.

The manuscript omits one technical sentence: `J₀` is Borel because the
plateau-value set is countable and, for continuous `u`, every fiber is closed.
After that addition its proof is sound.  In the more abstract Lean branch
lemma, it is also possible to prove relative Borel measurability directly for
a monotone function on a Borel subset of the real line.

### Composition law

```lean
theorem piecewiseMonotoneTransfer_comp
    {T U : IntervalMap}
    (PT : FiniteMonotonePartition T)
    (PU : FiniteMonotonePartition U)
    (PC : FiniteMonotonePartition (U ∘ T)) :
    transfer (U ∘ T) PC = (transfer T PT).comp (transfer U PU)
```

Dependencies/blockers:

* transfer independence under finite measurable refinement;
* the product refinement `P_i ∩ T ⁻¹' Q_j`;
* the single-branch image-measure theorem.

With disjoint assigned endpoint cells the composition identity is exact; the
phrase “up to endpoint assignments” should not be left inside the formal
statement.

### Expanding eigenspace and finite-dimensionality

For chosen partitions `PH`, define:

```lean
def ExpandingEigenspace (H : IntervalMap)
    (PH : FiniteMonotonePartition H) (lambda : ℝ) :
    Submodule ℝ NonatomicSignedMeasure :=
  LinearMap.ker (transfer H PH - lambda • LinearMap.id)
```

The finite-dimensional theorem can honestly be stated as:

```lean
theorem expandingEigenspace_finrank_le
    (hlambda : 1 < lambda)
    (PN : FiniteMonotonePartition (iterateMap H N))
    (hpow : lambda ^ N > 2) :
    Module.finrank ℝ (ExpandingEigenspace H PH lambda) ≤
      Fintype.card PN.idx
```

Use evaluations of cumulative mass at the ordered closed-cell endpoints.
One extra endpoint lemma is required: the transfer of `[cᵢ,x]` agrees with
the image measure even if `cᵢ` was assigned to the neighboring Borel cell.
Atomlessness removes that endpoint contribution.  The current convenient
lemma “subset of one assigned piece” is not by itself enough for the closed
interval used in the manuscript.

The manuscript's contraction proof is otherwise correct.  In particular,
for a finite signed measure, its cumulative function is bounded by total
variation, and an interval has signed mass equal to a difference of two
cumulative values because the measure is nonatomic.

### Compact probability slice

The statement as written has a real presentational gap: no topology has been
specified on the vector space of signed measures, and mathlib's
`SignedMeasure` does not come with the total-variation norm/topology needed by
the prose.  “Finite-dimensional” does not by itself create a Lean topology.

This is repairable without changing the mathematics.  Work in the Euclidean
range of the injective endpoint map:

```lean
def endpointCoordinates :
    ExpandingEigenspace H PH lambda →ₗ[ℝ] (Fin (r + 1) → ℝ) := ...

def EndpointRange := LinearMap.range endpointCoordinates
```

Transport the probability slice to `EndpointRange`, which inherits the
Euclidean topology.  Every set evaluation is an algebraic linear functional
on the finite-dimensional eigenspace.  After transport it is continuous by
finite-dimensional linear algebra.  Hence positivity is an intersection of
closed halfspaces and total mass `= 1` is closed.  Endpoint coordinates lie
in `[0,1]`, so the slice is bounded and therefore compact.

An honest statement should mention the coordinate image, for example:

```lean
theorem probabilityEndpointSlice_isCompact :
    IsCompact (endpointCoordinates ''
      {sigma : ExpandingEigenspace H PH lambda |
        0 ≤ sigma.1.1 ∧ sigma.1.1 Set.univ = 1})
```

This also makes continuity of the normalized transfer map precise.

## Simultaneous eigenmeasure by complex variation

The compact cone slice and Brouwer argument should not be formalized.  Let
`E` be the real nonatomic `lambda`-eigenspace of `transfer H`, and let `Eℂ`
be the corresponding subspace of complex measures: a complex measure belongs
to `Eℂ` when its real and imaginary parts are nonatomic and it is a
`lambda`-eigenmeasure for the complex-linear transfer of `H`.  The existing
linear equivalence
`ComplexMeasure.equivSignedMeasureₗ` identifies the underlying real space
with a subspace of `E × E`.  Thus the already proved finite-dimensionality
of `E` implies finite-dimensionality of `Eℂ` over `Real`, hence over
`Complex`.  It is nonzero because the positive `H`-eigenmeasure embeds in it.

Write `A = transfer P` and `B = transfer Q` on `Eℂ`.  Composition gives

```text
A B = B A = lambda * id.
```

`Module.End.exists_eigenvalue` over the algebraically closed field `Complex`
and `HasEigenvalue.exists_hasEigenvector` therefore give `z ≠ 0` and
`c : Complex` with `A z = c • z`.  The displayed identity makes `c ≠ 0`;
moreover

```text
c • B z = B (A z) = lambda • z,
```

so `B z = (lambda / c) • z`.  This is purely finite-dimensional linear
algebra and needs no topology or fixed-point theorem.

The decisive measure lemma is exact, not merely an inequality:

```lean
theorem variation_transfer_eq_transfer_variation
    {K : Type*} [IsROrC K]
    (T : IntervalMap) (PT : MonotonicityPartition T)
    (z : VectorMeasure I K) (hz : VectorNoAtoms z) :
    (transferVector T PT z hz).variation =
      transferMeasure T PT z.variation (variation_noAtoms hz)
```

It should be proved from the following declaration-level skeleton.

```lean
theorem variation_singleton (z : VectorMeasure I K) (x : I) :
    z.variation {x} = ‖z {x}‖ₑ

theorem variation_noAtoms {z : VectorMeasure I K}
    (hz : VectorNoAtoms z) : NoAtoms z.variation

theorem variation_monotoneBranchImage
    (u : I → I) (D : Set I) (hD : MeasurableSet D)
    (hu : MonotoneBranchOn u D) (z : VectorMeasure I K)
    (hz : VectorNoAtoms z) :
    (monotoneBranchImageVector u D hD hu z hz).variation =
      monotoneBranchImageMeasure u D hD hu z.variation

theorem variation_finsetSum_eq_of_disjoint_support
    (s : Finset ι) (z : ι → VectorMeasure I K)
    (D : ι → Set I) (hD : Set.PairwiseDisjoint s D)
    (hsupp : ∀ i ∈ s, ∀ E, MeasurableSet E →
      Disjoint E (D i) → z i E = 0) :
    (∑ i ∈ s, z i).variation = ∑ i ∈ s, (z i).variation
```

For one weakly monotone branch, images of disjoint measurable sets can
overlap only in the countable set of plateau values.  Remove that null set;
on what remains the image construction preserves partitions in both
directions, which proves the branch equality.  Assigned branch cells are
measurable and pairwise disjoint, and each branch image is supported on its
own source cell, so the finite-sum equality applies.  Global continuity of
the interval map supplies every preimage measurability fact needed in the
reverse partition argument.  This proof also explains why nonatomicity is an
essential hypothesis rather than convenient decoration.

The support hypothesis above must quantify over every measurable subset of
the complement.  The superficially shorter condition `z i (D i)ᶜ = 0` is
not sufficient for a signed or complex measure because cancellation can make
the mass of the whole complement zero while a subset has nonzero mass.

Mathlib's generic `VectorMeasure.variation` need not be finite for an
arbitrary Banach-valued vector measure.  For a complex measure it is finite,
but this fact is not packaged as an instance in the local checkout.  Prove it
explicitly by writing `z` as its real and imaginary signed measures and using

```lean
z.variation ≤ z.re.totalVariation + z.im.totalVariation.
```

The two Jordan total-variation measures are finite.  The remaining required
elementary facts are:

```lean
theorem complex_variation_ne_zero_iff (z : ComplexMeasure I) :
    z.variation ≠ 0 ↔ z ≠ 0

theorem complex_variation_isFinite (z : ComplexMeasure I) :
    IsFiniteMeasure z.variation

theorem variation_complex_smul (c : Complex) (z : ComplexMeasure I) :
    (c • z).variation = ENNReal.ofReal ‖c‖ • z.variation
```

Apply exact naturality to `z`.  The finite nonzero nonatomic positive measure
`|z| := z.variation` satisfies

```text
transfer H |z| = lambda |z|,
transfer P |z| = |c| |z|,
transfer Q |z| = (lambda / |c|) |z|.
```

Normalize by `|z| univ`, which is finite and strictly positive.  This yields
the exact central statement:

```lean
theorem simultaneous_conformal_probability
    ... :
    ∃ nu : Measure I, ∃ C D : ℝ,
      (∀ x, nu {x} = 0) ∧ nu Set.univ = 1 ∧
      0 < C ∧ 0 < D ∧ C * D = lambda ∧
      transfer P PP nu.toSignedMeasure = C • nu.toSignedMeasure ∧
      transfer Q PQ nu.toSignedMeasure = D • nu.toSignedMeasure
```

No conversion through a nonnegative signed measure is needed: variation is
already a `Measure`.  This route also repairs the manuscript.  Its compact
slice paragraph is missing a specified topology, and its Brouwer invocation
has no available kernel theorem; both paragraphs can be replaced by the
complex-eigenvector/variation argument above.  The endpoint-coordinate
compactness lemma remains mathematically repairable as described in the
preceding subsection, but is unused and should be omitted from the Lean DAG.

## Quotient and fiber-descent audit

### Respect of fibers

The production quotient skeleton uses mathlib's real CDF of the pushforward
under `Subtype.val`.  Its cumulative-mass formula, including the left endpoint,
must be proved under the probability hypothesis: the raw `cdf` definition is
available for arbitrary measures, but `cdf_eq_real` is not.

An honest statement is:

```lean
theorem conformalDistribution_respectsFibres
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {nu : Measure I} [IsProbabilityMeasure nu] [NoAtoms nu]
    {c : ℝ} (hc : 0 < c)
    (heigen : transfer T PT nu.toSignedMeasure =
      c • nu.toSignedMeasure) :
    RespectsFibres (distributionCoordinate nu) T
```

The manuscript proof is sound.  Positivity lets zero mass pass to each piece,
and the branch identity sends each such piece to a null interval.  Endpoint
assignment again requires a closed-cell version of the branch formula.

### Piecewise-linear quotient

```lean
theorem descendedMap_finitePiecePL_of_conformal
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {theta Tbar : IntervalMap}
    (htheta_cont : Continuous theta) (htheta_mono : Monotone theta)
    (htheta_onto : Function.Surjective theta)
    (hdesc : Intertwines theta T Tbar)
    {c : ℝ} (hc : 0 < c)
    (hscale : branchwise theta-increment scaling by c) :
    FinitePiecePL Tbar ∧ HasConstantAbsoluteSlope Tbar c
```

The proof in the manuscript is correct after one small addition.  A plateau
interval need not be contained in one originally chosen cell; split it at the
finitely many partition vertices, collapse each subinterval, and join them
through the common endpoints.  The current prose proves only the contained-in
one-cell case before saying all plateaus are collapsed.

### Final fiber descent

If `q` is fixed by both descended maps, then
`K = theta ⁻¹' {q}` is a nonempty compact interval and is forward invariant
under both original maps.  Minimality forces `K = I`, contradicting
surjectivity of nonconstant `theta`.  This argument is sound and requires no
new deep theorem.  It should be expressed as a reusable lemma:

```lean
theorem commonFixedPoint_descended_contradicts_minimalCore
    (hminimal : ∀ K : ClosedSubinterval,
      IsCommonInvariantCore P Q K → K.carrier = Set.univ)
    (htheta_cont : Continuous theta) (htheta_mono : Monotone theta)
    (htheta_onto : Function.Surjective theta)
    (hP : Intertwines theta P Pbar)
    (hQ : Intertwines theta Q Qbar)
    (hfixed : HasCommonFixedPoint Pbar Qbar) : False
```

## Piecewise-linear core: required refactor boundary

The desired callable theorem is:

```lean
theorem finitePiecePL_common_fixed_point
    {P Q : IntervalMap}
    (hP : FinitePiecePL P) (hQ : FinitePiecePL Q)
    (hcomm : Commute P Q) :
    HasCommonFixedPoint P Q
```

It does not currently exist.  The tempting derivation

```lean
exact tame_C1_common_fixed_point ?R P Q
  (finitePieceC1_of_finitePiecePL hP)
  (finitePieceC1_of_finitePiecePL hQ) hcomm
```

cannot be completed because the project has no term `?R : OMinimalExpansion`.
Constructing the semialgebraic real-field expansion would require
Tarski--Seidenberg/quantifier elimination, which is not in mathlib and is far
outside the efficient path.

The preferred refactor is to isolate the actual regularity consequences used
by the old proof into a structure, for example:

```lean
structure IntervalTamenessPackage (T : IntervalMap) where
  continuous : Continuous T
  fixedSet_finiteUnion : ...
  flatFree_finiteStrictLaps : ¬ HasFlatInterval T →
    HasFiniteStrictMonotonicityLaps T
  localC1BV_on_nonflatCell : ...
  stable_under_comp : ...
  stable_under_affine_conjugacy : ...
  stable_under_finite_respected_quotient : ...
```

Provide one constructor from `FinitePieceC1 R T` (reusing current proofs) and
one direct constructor from `FinitePiecePL T`.  Then parameterize the
normalization/least-counterexample front end by these packages.  Once the
proof reaches the already-PL `Polygonal` layer, all remaining declarations
are independent of `R` except for their packaging through
`LeastNormalizedCounterexample R`.

At minimum the following current private results must be exposed or split
from their `R` packaging:

* existence of a nondegenerate minimal invariant core;
* affine rescaling and surjectivity on a minimal core;
* finite fixed-component quotient/descent;
* PL fixed-set finiteness and flat-free strict-lap finiteness;
* the local right `C¹+BV` germ package for a PL branch (affine derivative,
  hence zero variation);
* preservation of `FinitePiecePL` under composition, affine conjugacy, and the
  finite canonical quotients used by the old normalization.

This is a critical-path task, not cleanup.  The new final theorem depends on
it even if every new measure lemma is completed.

## Manuscript revision checklist

The following points should be recorded in the eventual revised draft so its
proof order matches the formal development.

1. Replace the bare BF citation by the precise direct consequence actually
   used: absence of a common fixed point produces an eventual two-branch
   interval horseshoe.  State whether the proof follows Marr's alternating
   configuration and finite covering graph, and give the iterate convention.
2. Replace the full AM citation by the weaker project theorem: an eventual
   horseshoe plus finite weak monotonicity pieces produces a compatible
   expanding coordinate.  Do not claim an entropy equality that the proof
   never uses.
3. Make the monotonicity partition half-open/assigned at interior endpoints.
   State explicitly that plateau values are countable and are null for every
   total variation arising from a nonatomic complex measure.  This is what
   makes branch transfer independent of the partition and compositional.
4. In the finite-dimensionality proof, include the assigned-endpoint lemma
   needed for `[c_i,x]`; merely saying the interval lies in one closed lap
   loses track of which adjacent cell owns `c_i`.
5. Delete the compact probability slice and Brouwer paragraphs.  Besides the
   missing topology on signed measures, Brouwer is unnecessary.  Replace
   them with: complexify the finite-dimensional eigenspace, choose a complex
   eigenvector, prove exact transfer/variation naturality, take variation,
   and normalize.
6. State separately why complex total variation is finite.  Generic
   Banach-valued vector measures can have infinite variation; finiteness here
   follows from the Jordan total variations of the real and imaginary parts.
7. Expose the piecewise-linear common-fixed-point theorem without an
   `OMinimalExpansion` parameter.  Until that refactor is proved, the phrase
   “apply the earlier theorem” hides a genuine missing hypothesis.
8. Give the final minimal-core/fiber argument after quotient descent, with
   onto-ness and commutation transported explicitly.  This keeps the exact
   strength of the final theorem visible: continuous interval self-maps,
   finitely many weak monotonicity pieces, and no differentiability,
   transitivity, entropy, or o-minimal assumption.

## Dependency map and recommended order

```text
FinitePieceMonotone definitions and composition
        |
        +--> minimal common invariant core; P,Q onto
        |          |
        |          +--> H = P o Q is finite-piece monotone
        |                     |
        |                     +--> BF/De Marr alternating configuration
        |                              |
        |                              +--> direct two-branch horseshoe for H
        |                                       |
        |                                       +--> weak-lap resolvent
        |                                               |
        |                                               +--> expanding compatible
        |                                                    coordinate for H
        |
plateau-aware signed transfer + composition -----------------+
        |                                                     |
        +--> scalar-generic branch transfer <-----------+
                    |
                    +--> exact variation naturality
                    |          |
                    |          +--> finite/nonzero/nonatomic complex variation
                    |
        +--> finite-dimensional real H-eigenspace
                    |
                    +--> finite-dimensional complex H-eigenspace
                               |
                               +--> complex eigenvector for T_P
                                            |
                                            +--> take variation and normalize
                                                       |
                                            simultaneous conformal measure
                                                       |
                                            common distribution coordinate
                                                       |
                                            P,Q respect fibers and descend
                                                       |
                                            descended P,Q are finite-piece PL
                                                       |
direct unconditional PL-core refactor -----------------+
                                                       |
                                            fixed quotient fiber + minimality
                                                       |
                                            final common fixed point theorem
```

Declaration-level DAG (names may be adjusted once the current skeletons
settle, but dependencies should not be weakened or hidden):

| Layer | Required declarations | Immediate dependencies |
|---|---|---|
| Definitions | `MonotonicityPartition.assignedCells`, `assignedCells_pairwiseDisjoint`, `assignedCells_iUnion`, `FinitePieceMonotone.comp` | interval/Borel basics |
| Generic transfer | `VectorNoAtoms`, `monotoneBranchImageVector`, `piecewiseMonotoneTransferVector`, `piecewiseMonotoneTransferVector_comp` | assigned cells, countable plateau values, Lusin--Souslin/monotone image measurability |
| BF replacement | `MarrAlternatingConfiguration`, `marr_configuration_of_commuting_noCommonFixedPoint`, `MarrAlternatingConfiguration.twoBranchHorseshoe` | compact fixed-set order, commutation, IVT, branch trimming |
| Weak Parry bridge | `WeakLapResolventInput`, `weakLapLimit_scaling`, `expandingCompatibleCoordinate_of_horseshoe` | horseshoe, weak laps, generalized resolvent |
| Real eigenspace | `ExpandingEigenspace`, `expandingEigenspace_finrank_le` | transfer composition, assigned-endpoint contraction |
| Variation | `variation_singleton`, `variation_noAtoms`, `variation_monotoneBranchImage`, `variation_finsetSum_eq_of_disjoint_support`, `variation_transfer_eq_transfer_variation`, `complex_variation_isFinite`, `variation_complex_smul` | scalar-generic transfer, Jordan decomposition |
| Complex spectral step | `ComplexExpandingEigenspace`, `complexExpandingEigenspace_finiteDimensional`, `transferP_complexEnd`, `exists_common_eigen_complex` | real finrank, transfer composition, `Module.End.exists_eigenvalue` |
| Positive spectral step | `simultaneous_conformal_probability` | complex eigenvector, exact variation naturality, finite/nonzero variation |
| Quotient | `conformalDistribution_respectsFibres`, `descendedMap_finitePiecePL_of_conformal` | simultaneous probability, single-lap scaling |
| PL core | `finitePiecePL_common_fixed_point` | refactored old PL proof, no `OMinimalExpansion` argument |
| Finish | `commonFixedPoint_descended_contradicts_minimalCore`, `finitePieceMonotone_common_fixed_point` | quotient, PL core, minimality |

Post-audit PL spectral refinement: after the arbitrary-PL ray block proves the
returned product `R = P^[L] ∘ Q^[L]` topologically exact, use exactness to
construct a `TwoBranchHorseshoe` for some `R^[N]`.  Commutation rewrites this
as `P^[L*N] ∘ Q^[L*N]`; the generic positive-exponent complex/variation layer
then restores the common constant-slope coordinate.  This bridge now checks:
two fixed separated rational open intervals become full at positive exactness
times, surjectivity equalizes the times, and endpoint preimages give the strict
branches by IVT.  Thus the stronger dependency graph needs neither Parry
existence nor Parry uniqueness.  The still-sorried B7 skeleton is to be revised
to the checked generic interfaces rather than preserving its older Parry-shaped
interfaces.

Efficient scheduling:

1. Finish the definitions/assigned-cell/composition skeleton and the
   plateau-aware signed transfer in parallel.
2. Start the unconditional PL-core refactor immediately; it is independent
   of the new spectral layer and otherwise becomes a late surprise.
3. In parallel, prove the BF/Marr horseshoe theorem and extract the generic
   weak-lap-resolvent interface.
4. Once transfer composition is stable, formalize finite-dimensionality and,
   in parallel, scalar-generic branch transfer plus exact variation
   naturality.  Do not spend time on compactness or cone topology.
5. Complexify the eigenspace, use `Module.End.exists_eigenvalue`, take
   variation, and normalize.  The branch-variation equality is the principal
   new uncertainty and should be completed before downstream quotient proofs.
6. Only then fill fiber respect, PL descent, and the final minimality
   contradiction.  Their skeletons can be present from the beginning, but
   their proofs are low risk.

### Rational PL branch audit update

The sole use of `common_positive_iterate` in the rational PL branch cannot be
removed by component bookkeeping alone.  Two proposed replacements were
tested against frozen skeletons/interfaces:

1. A selected-gap specialization fails because finite arrival forces any
   common-return-invariant interval containing the selected orbit segment to
   be the whole interval, while the hypotheses do not produce another
   nondegenerate fixed component invariant under both factors.
2. The canonical fixed-component quotient is valid and already supported by
   the project: nondegenerate components can be collapsed, both maps descend,
   and only finitely many singleton fixed components remain.  But the last
   statement needed downstairs—global equal positive powers plus a finite
   positive-word fixed set implies a common fixed point—is equivalent to the
   original theorem.  Commuting finite permutations with equal squares and no
   common fixed component show why no component-only lemma can supply it.

Consequently the honest remaining route is the periodic-homeomorphism fixed-
set theorem on the arc-like natural extension.  Its nonemptiness part is
already formalized; its connectedness part is being expanded from the single
topological construction hole in `SmithH0Scratch.lean` into a complete
coherent invariant-cover/nerve/Smith skeleton before integration into
`CommonIterate.lean`.

### Assembly status update

The exact public theorem displayed below and its complete minimal-core
assembly now compile with zero local holes.  This does not yet constitute a
no-axiom proof: its upstream resolvent, joint-eigenspace, quotient-geometry,
PL-core, Fugate--McLean, and substitution obligations remain visible and are
counted in `FORMALIZATION_PLAN.md`.

### PL substitution-interface correction

The initial six-leaf Markov/substitution boundary is not sufficiently
hypothesized. Its edge-data structure merely stores two substitutions fixing a
common word, while the growth structure stores unrelated real numbers. Hence
identity substitutions and an arbitrary nonsyndetic fixed word give a direct
counterexample to the stated syndeticity leaf, and no stored field connects
ultimate periodicity of that word to a geometric return path. Boundary 9 must
therefore be refrozen around an occurring directed-edge alphabet, positive
edge-length scaling, complete occurrence/generation and Perron data, and
explicit word-to-path decoding. The raw source hole count remains a snapshot,
not an assertion that this invalid interface is final.

## Main theorem statement

The final result should be exposed without any o-minimal, differentiability,
entropy, or external-theorem hypothesis:

```lean
theorem finitePieceMonotone_common_fixed_point
    (P Q : IntervalMap)
    (hP : FinitePieceMonotone P)
    (hQ : FinitePieceMonotone Q)
    (hcomm : Commute P Q) :
    HasCommonFixedPoint P Q
```

Its proof may use classical choice and existing mathlib theorems; these do not
become project axioms.  Acceptance still requires:

```text
rg -n "\bsorry\b|^\s*axiom\b|\badmit\b" -g "*.lean" .
lake build
#print axioms CommutingInterval.finitePieceMonotone_common_fixed_point
```

The final `#print axioms` may report Lean/mathlib foundations such as
propositional/classical choice, but it must not report a project-specific
axiom or a declaration introduced to stand for BF, AM, Brouwer, Durand, or the
PL core.
