 # Simplified formalization plan and progress tracker

## Completion tracker

**Estimated work completion: 100%**  
**Estimated work remaining: 0%**  
**Open mathematical high-level ledger items: 0 of 53**  
**Executable Lean holes (`sorry` / `admit`) at the certified checkpoint: 0**  
**High-level skeleton slots not yet written: 0**  
**Deep internal sublemma DAGs still to freeze or repair: 0**  
**Project `axiom` declarations introduced by this development: 0**  
**Forbidden direct imports from `CommutingInterval` still to eliminate: 0**  
**Forbidden imports in the current public transitive closure: 0**  
**Confirmed manuscript corrections incorporated: 2 of 2**  
**Other tracked manuscript clarifications incorporated: 11 of 11**

**Final pinned manuscript snapshot:** 989 lines, SHA-256
`574FCF260AF68466A26F534BC4566F2803ED9D13931D99F3225E153BFEF38B03`
(filesystem modification time 2026-08-11 19:21:51 local).  The dependency
graph and skeleton order below match this simplified manuscript.  The final
post-edit theorem-alignment and journal-rigor audit is complete; any future
TeX hash change must trigger a fresh alignment check.

**Version-question resolution.**  The pinned manuscript already contains the
correct ordered branch increment
`S(max(u,v)) - S(min(u,v))`.  The earlier complaint concerned two transient
Lean skeleton interfaces, not an older or uncorrected TeX file: a real-valued
coordinate had incorrectly been required to be onto all of `R`, and a local
continuity lemma omitted `Continuous T`.  Both Lean interfaces are repaired;
`BranchLength.lean` and `Reduction.lean` rebuild with no proof holes.  The
manuscript formula must not be changed in response to that withdrawn warning.

The percentage is weighted by estimated mathematical and formalization work,
not by the number of holes.  The numerical obligation rows distinguish written
Lean holes, manuscript-facing skeleton slots, and deep internal DAGs still to
expand, so an incomplete skeleton cannot misleadingly look complete.

**Certified synchronized-core checkpoint.**  The route audit correctly rejected
the old assertion that equality of two decoded recurrent languages by itself
produces one literal common fixed word.  The completed proof obtains the extra
structure from the geometric specialization instead: both substitutions fix
the same ambient word and scale the same strictly positive metric.  Their
restrictions to the intrinsic recurrent-letter alphabet commute; after choosing
a primitive prolongable power on one side, the finite orbit under the other
side supplies positive powers fixing one literal recurrent word.  Relabelling
this finite alphabet gives `MetricSynchronizedPrimitiveCoreData`, with an
injective decoder, exact source-power intertwining, two primitive substitutions,
one common fixed word, and one pulled-back exact metric.  Thus the final route
does not infer a common word from language equality alone.

`DurandPrimitiveCore.lean`, `DurandSynchronization.lean`, and
`DurandLinearRecurrence.lean` prove this synchronized core and its aperiodic
linear recurrence.  The new production module `DurandCommonDerived.lean`
contains the complete 1a--1m common-derived-system construction, including the
faithful finite return-system code, literal self-return decoder, common source
powers, and the actual shared return metric.  `DurandPrimitiveComparison.lean`
then applies the two Proposition-10 power families and the exact-metric decoder
comparison to obtain equality of positive powers of the two source scales.
The old asserted M2 constructor and old M4.1 hole were deleted; the generic
return-tower and Proposition-10 records that remain are now reached only through
the proved synchronized adapter.

All manuscript-facing DAGs are statement-complete.  The axiom-free BF/AM
replacement, standalone Brouwer support, E3 quotient construction, geometric
fold, and terminal periodic-fold route are proved.  The common Markov hull C1,
the full directed-substitution construction C2, and the complete ray-itinerary
construction C3 are now certified zero-hole.  C2 includes the all-directed-edge
alphabet, exact literal image paths for both returned maps, nonerasing
substitutions, and the two exact metric-scaling laws.  C3 includes the locally
finite and unbounded Markov-hit sequence, its successive directed traversals,
and the full lifted itinerary.

The current dependency route is therefore
`Coding C1--C5 -> DurandMetric M0--M1 -> DurandPrimitiveCore ->
DurandSynchronization -> DurandLinearRecurrence -> DurandCommonDerived ->
DurandPrimitiveComparison -> Coding C7/C8 -> PeriodicFold -> Main`.
Every module in this route is build-green and contains zero executable proof
holes.  All ten C5 occurrence-restriction leaves, the exact-metric M1
target-parent contradiction, the synchronized primitive-core construction,
the complete common-derived-system DAG, and the final scale-power comparison
are proved.  No hidden Coding or Durand DAG remains.

The work percentage is weighted by proof difficulty, not hole count.  All
mathematical proof packages and certification tasks are complete.  Scratch-only
modules and unused dependencies were pruned, both `Main` and the public
`CommutingIntervalSimplified` target rebuild with Lake, and the production
M4.1 theorem, the synchronized comparison theorem, and the public final theorem
audit only to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
The coordinated journal-manuscript revision is incorporated in the final
pinned snapshot.  Both confirmed corrections and all eleven tracked
clarifications are present, and `MANUSCRIPT_REVISION_NOTES.md` now preserves
their mathematical rationale and replacement text as applied revision history.

The user requires this library to be completely standalone.  The certified
production route satisfies that rule: every retained theorem is proved locally
over Mathlib and local modules, the main argument does not invoke the old final
theorem or an old high-level route package, and temporary scratch modules have
been removed.

| Work package | Earned / weight | Status |
|---|---:|---|
| standalone base definitions and typed factor infrastructure | 8 / 8 | complete: all shared definitions and immediate APIs import only Mathlib/local modules |
| common constant-slope reduction | 18 / 18 | complete: product horseshoe, weak-lap growth/radius/limits, expanding compatible coordinate, branch-length eigen-equation, common Brouwer coordinate, minimal-core quotient, constant slopes, and expansion `>1` are all proved |
| common-positive-iterate lemma | 7 / 7 | complete standalone inverse-limit proof and internal fixed-set support; zero holes |
| extremal minimization and component collapse | 13 / 13 | complete: phase family, finite component permutations, cumulative-length quotient, descended PL regularity, strict descent, relinearization, minimization, and returned-power irreducibility |
| generic finite joint postcritical theorem | 10 / 10 | complete: intrinsic turns, exact composition, rectangle/difference identities, finite-tail recurrence, affine scale collision, cross-periodicity, turn transport, and the finite common hull are proved |
| repelling state and dense stabilized fold | 12 / 12 | complete: repelling states, factorial return, stabilized dense ray, germ globalization, scale-power iterate equality, common-positive-iterate contradiction, and final `TwoScaleFoldData` packaging are proved |
| Markov coding and no-axiom Durand adapter | 25 / 25 | complete: C1--C8, exact-metric M0--M1, recurrent-core extraction, synchronized common fixed word, aperiodic linear recurrence, bounded return systems, common-derived Proposition-10 package, and exact-metric scale-power comparison are proved in the standalone route |
| periodic rigidity, affine lifts, and parity | 5 / 5 | complete standalone path rigidity, tail extension/globalization, affine lifts, reflection, parity, and periodic-fold theorem |
| assembly, audits, cleanup, and correspondence | 2 / 2 | complete: dependency/import pruning and scratch removal, static hole/axiom/old-reference scans, clean `Main` and public-root builds, and transitive public-theorem axiom audit |
| **Total** | **100 / 100** | **formal proof and final certification complete** |

## Frozen proof architecture

The formal proof follows the simplified manuscript's seven main lemmas.  A
paper citation is never represented by a Lean axiom.  The final transitive
import closure may contain Mathlib and `CommutingIntervalSimplified` modules
only.  Existing repository code may be consulted and copied in dependency-
minimal form, but the resulting declaration and proof must live in the new
namespace and must not reference an old theorem.

1. `Base.lean` and small standalone support modules define interval maps,
   weak finite-piece monotonicity, PL maps, constant slope, quotients, genuine
   turns, symbolic words, and periodic paths directly over Mathlib.
2. `Defs.lean` fixes the shared counterexample, factor, return-power,
   postcritical, periodicity, and two-scale-fold interfaces.
3. `Reduction.lean` produces a normalized expanding common constant-slope
   counterexample from a weak finite-piece monotone counterexample.
4. `CommonIterate.lean` proves the manuscript's inverse-limit lemma inside the
   standalone library.  Generic continuum results not in Mathlib must also be
   proved here or in a standalone support module; they cannot be cited as Lean
   assumptions.
5. `Extremal.lean` chooses the fixed-count-minimal factor and proves returned
   power irreducibility.
6. `Postcritical.lean` proves finiteness of the joint postcritical set from
   multiplicative independence.
7. `Fold.lean` constructs the dense two-scale unit-speed ray from a repelling
   directed germ and proves scale independence.
8. `Coding.lean` builds the common Markov substitutions.
   `DurandMetric.lean`, `DurandPrimitiveCore.lean`,
   `DurandSynchronization.lean`, `DurandLinearRecurrence.lean`,
   `DurandCommonDerived.lean`, and `DurandPrimitiveComparison.lean` prove the
   exact-common-metric Durand specialization used by C7.
9. `PeriodicRigidity.lean` proves the local-to-global periodic-path facts;
   `PeriodicFold.lean` converts the periodic fold into a common fixed point.
10. `Main.lean` assembles the contradiction, and
   `CommutingIntervalSimplified.lean` is the public entrypoint.

The final import closure must contain no module beginning `CommutingInterval.`
and no reference to a declaration in the `CommutingInterval` namespace.  In
particular, importing a generic old support theorem is not acceptable: the
minimal proof and its dependencies must be moved into this library.

### Current-manuscript alignment audit

Rechecked against the final pinned 989-line snapshot after the coordinated
manuscript revision and post-edit audit:

- [x] `thm:main` maps to `Main.lean`.
- [x] `lem:linearize` maps to `BranchLength.lean` + `Reduction.lean`.
- [x] `lem:common-iterate` maps to standalone `CommonIterate.lean`.
- [x] `lem:irreducible` maps to `Extremal.lean`.
- [x] `lem:finite-postcritical` maps to `Postcritical.lean`.
- [x] `lem:two-scale` maps to `Fold.lean` + `Coding.lean`.
- [x] `lem:path-rigidity` maps to `PeriodicPathRigidity.lean`.
- [x] `lem:periodic-fold` maps to `PeriodicFold.lean` and the standalone
  affine-lift/parity modules.
- [x] The manuscript and Lean both use the ordered branch increment
  `S(max(u,v)) - S(min(u,v))`; no correction is pending there.

No obsolete o-minimal, Denjoy, Kopell, orbit-circle, selected-gap, or old
primitive/Perron proof stage occurs in this dependency order.

### Logged skeleton repairs

The frozen skeleton has been edited only for the following discovered type or
mathematical issues:

1. `CommonBranchEigenCoordinate` initially asked a real-valued coordinate
   `[0,1] -> R` to be surjective onto all of `R`.  It now stores bounds in
   `[0,1]`, interval-valued surjectivity, and exposes a proved packaged
   `IntervalMap`.
2. `branchLengthOnPartition_continuous` initially omitted continuity of the
   underlying map.  Weak monotonicity alone permits discontinuous step maps,
   so the statement now takes `Continuous T`; canonical branch length obtains
   this from `FinitePieceMonotone T`.
3. The geometric fold conclusion explicitly returns either the extremal
   system or its simultaneous midpoint-reflection conjugate.  This formalizes
   the manuscript's “conjugate by `x -> 1-x` if needed” step instead of
   silently assuming the repelling side points right.
4. The generic metric-scaling-to-dominant-eigenvalue lemma now requires a
   nonempty alphabet.  Without that hypothesis all scaling assumptions are
   vacuous on the empty alphabet, while an eigenvalue still requires a
   nonzero vector.  The occurring-alphabet application supplies nonemptiness
   from its distinguished seed letter.
5. `phaseComponentUnions_exists` now takes the already available hypothesis
   `0 < L`.  This is required because `PhaseIndex L = ZMod L x ZMod L` is
   finite only for positive `L`; at `L = 0`, `ZMod 0` is infinite.  The sole
   caller already has factorial positivity, so this adds no mathematical
   assumption to the manuscript theorem.
6. An abandoned `PoweredGrowthAsymptotics` route exposed a nonnegative
   nonzero left Perron weight and an exact eigenvector equation.  That entire
   finite-matrix route was later removed when the common exact metric supplied
   the needed growth and comparison data directly; it is not a current
   dependency or remaining obligation.
7. The same abandoned D1 draft incorrectly claimed that one power makes every
   recurrent SCC block positive; a two-cycle substitution disproves this for
   imprimitive SCCs.  A bounded-residue repair was designed, but both the
   faulty interface and its repair were physically removed with the D1/Perron
   route.  This item is retained only as a record of why that route must not be
   revived.
8. The first return-tower draft simultaneously required strictly increasing
   local source exponents and a uniform bound on all induced image lengths.
   This is false for the one-letter substitution `a -> aa`: the induced image
   length at local exponent `e` is `2^e`.  The replacement follows Durand's
   actual Lemma 12/Propositions 10--11 separation.  Per-level induced powers
   stay bounded, while distinct cumulative source and refinement exponents
   are tracked only in the Proposition 10 power equations.  The replacement
   also retains the common positive edge metric supplied by Coding, so the
   general SCC/Perron-asymptotics layer is unnecessary for the formal
   specialization used here.
9. The first M1.2 interface allowed the two substitutions to carry unrelated
   positive metrics.  Full Durand--Rigo theory proves that stronger statement,
   but its proof needs ordinary-length asymptotics and hence the Perron layer
   deliberately removed above.  The actual Markov coding supplies one common
   positive edge-length vector scaled exactly by both substitutions, exactly
   as written in the manuscript.  M1.2 and `metricTheorem9` therefore use that
   common metric.  This narrows only the internal formal specialization; it
   adds no hypothesis to the main theorem, and the paper continues to invoke
   Durand's stronger published theorem.
10. An early C2 tracker shorthand said that the two directed-edge
    substitutions commute.  Neither the manuscript nor the symbolic argument
    asserts or needs substitution commutation; what is needed is nonerasing,
    exact path realization, exact metric scaling, and later the two common
    fixed-word equations.  C2 now records exactly those properties.
11. The first M1.2f comparison interface was mathematically false: its coarse
    total metric-gap bound directly contradicted the strict-gap side it was
    meant to produce.  A later arbitrary-window formulation was also false for
    constant-length examples.  Both were removed.  The proved replacement is
    the recurrent-parent cell argument in `DurandMetric.lean`: a persistent
    safe tower cell is compared with the unique powered tiling cell containing
    a recurrent target occurrence; unbounded target-parent coordinates give a
    genuine positive scale window, cofinal density supplies a ratio in that
    window, and exact metric coordinates turn it into a forbidden literal
    embedding.  The public common-metric theorem is unchanged.
12. `MinimalCore.lean` originally retained an older Zorn/chain-intersection
    construction although the simplified manuscript uses a least-length
    interval.  The Zorn support has been physically removed.  The replacement
    forms the closed compact set of invariant endpoint pairs, proves closedness
    by clamping approximating points and using continuity of both maps,
    minimizes endpoint length, and derives inclusion-minimality from equality
    of lengths.  The needed continuity hypotheses are now explicit and are
    supplied by the sole caller in `Reduction.lean`; the public reduction
    conclusion is unchanged.
13. M3.7's first finite-coding record was formally satisfiable by a constant
    dummy code: it never stated that a recorded signature described the actual
    return system.  That record has been removed.  The repaired interface makes
    code equality produce `PairedReturnTowerLevelsEquivalent`, containing the
    current and next finite-alphabet relabelings, both complete derived-word
    equalities, both induced-substitution image equalities, and the adjacent
    connector equality.  M3.8 now stores this semantic witness, so M4 cannot
    consume a dummy table tag.
14. M2.1 initially demanded a common recurrent-core presentation without
    proving how the common literal word arose.  Equality of decoded languages
    is insufficient, and the source-specific core extraction was therefore
    formalized first in `DurandPrimitiveCore.lean`.  The decisive extra input
    is the one common exact metric: it makes the recurrent restrictions
    commute, and a finite orbit of one primitive fixed word under the other
    restriction yields positive powers fixing one literal word.  The final
    `MetricSynchronizedPrimitiveCoreData` records that word, both positive
    source powers, injective decoding, exact metric scaling, primitivity, and
    the decoded recurrent language.  This proves rather than assumes the
    common-point interface used downstream.
15. The five M5 matrix-spectrum leaves copied general Proposition-11 machinery
    even though the geometric input has an exact positive metric.  They were
    replaced by the proved exact-metric comparison in `DurandMetric.lean`:
    both source power-equation families scale one common return decoder, a
    positive metric identifies its scale on the two sides, and subtraction of
    two equations eliminates the auxiliary substitution.  Cross-multiplying
    the two positive exponent differences gives equality of positive powers
    of the original scales without a Perron/frequency layer.
16. `CofinalMetricMarkerTower` initially guaranteed only cofinal nested
    prefixes.  The physical realization step in M4.1 needs the selected marker
    of every numerical level to be the canonical prefix `word.take (level+1)`;
    arbitrary cofinal towers do not provide that identification.  The record
    and its constructor now expose `marker_eq_take`, and the canonical stage
    realization uses it explicitly.
17. An intermediate M4.1 signature quantified over an arbitrary generic
    `MetricCommonRecurrentCoreData`, allowing unrelated left and right return
    metrics.  The production theorem in `DurandCommonDerived.lean` instead
    takes `MetricSynchronizedPrimitiveCoreData`; its compatibility adapter
    defines both displayed return metrics from the same ambient metric.  This
    is exactly the strength supplied by the C2 coding and needed by the final
    metric comparison.
18. The original self-return assembly shifted a repeated pair of first-letter
    stages before composing decoders.  The final proof composes the complete
    return decompositions directly across the two repeated stages and then
    transports the ambient alphabet through the certified repetition
    relabelling.  This removes an unnecessary successor-shift dependency while
    preserving both source-decoding identities.

The current manuscript already has the correct ordered branch increment; the
withdrawn absolute-value warning was not a skeleton repair.

### Concurrent-proof checkpoint rule

Two downstream builds were temporarily blocked by half-elaborated edits in an
imported module.  From this checkpoint onward, an agent owning a dependency
module must leave that module compile-green before beginning the next proof
cluster.  Longer experiments should be made in a local scratch theorem or in
small independently checked helper blocks, then moved into the dependency
module atomically.  Public signature changes are announced before they are
made.  This keeps parallel work on downstream modules productive.

### Standalone foundation status

- [x] `Base.lean`: Mathlib-only unit interval, fixed points, partitions,
  iterates, invariant intervals, affine/finite-piece PL maps, intrinsic turns,
  directed germs, multiplicative independence, and constant absolute slope.
- [x] `PiecewiseMonotoneBase.lean`: weak monotonicity, refinement,
  composition/iteration, and the assigned-cell layer needed by the internal
  BF/AM replacement.
- [x] `FactorBase.lean`: fibres, exact fixed descent, finite interval
  quotients, descended maps, and common factor composition.
- [x] `PolygonalBase.lean`: finite-piece unit-speed paths, periodic
  surjections, and dilation semiconjugacy.
- [x] replace provisional `Defs.lean` so it imports only these local layers.

## Obligation countdown

These 53 identifiers are the fixed work ledger.  Statement wording may be
repaired when typechecking exposes a genuine issue, but completed statements
will not be replaced merely to make a proof easier.
Here a checked high-level item means its own Lean body is complete; any open
dependency it invokes remains counted by the executable-hole and internal-DAG
rows above.  Thus backward proofs can be tracked without concealing upstream
work.

### B. Branch-length infrastructure (6)

- [x] B1 define the branch-length operator and prove independence of the
      chosen weak-monotonicity partition
- [x] B2 prove continuity, endpoint normalization, and the one-lap increment
      identity
- [x] B3 prove linearity and preservation of nondecreasing coordinates
- [x] B4 prove the composition identity
      `L_(U o T) = L_T o L_U`
- [x] B5 prove finite dimensionality of the product eigenspace by evaluation
      on the image values of an iterate partition
- [x] B6 normalize the commuting branch-length actions and apply Brouwer to
      obtain a common nondecreasing eigen-coordinate

These obligations were added after the standalone clarification.  The old
development bypassed this step through a simultaneous eigenmeasure.  That
would not mirror the simplified proof, so it is not an acceptable replacement
for B1--B6.  Standalone internal proofs may still supply the two published
BF/AM input statements, but the new branch-length/Brouwer argument itself must
be formalized.

### R. Common constant-slope reduction (9)

- [x] R1 minimal common invariant core and affine normalization
- [x] R2 the product horseshoe and weak-lap compatible-coordinate chain
      assemble the initial expanding product branch eigen-coordinate
- [x] R3 the normalized Brouwer theorem converts the product coordinate into
      a common branch eigen-coordinate
- [x] R4 coordinate descent gives commuting onto factor maps
- [x] R5 descended maps are finite-piece PL with constant absolute slopes
- [x] R6 fixed points of every word descend exactly
- [x] R7 absence of a common fixed point descends
- [x] R8 minimal common-core property descends
- [x] R9 both slopes exceed one and the normalized factor exists

The manuscript and Lean both pass through B1--B6.  For the published BF/AM
input only, Lean contains a proved specialized internal replacement rather
than an axiom; after that input the formal route is the manuscript's
branch-length/Brouwer route.

### R2 standalone BF/AM-replacement dependency countdown (13)

These declarations prove, rather than assume, the specialized product input
used by the manuscript's branch-length argument.  R2 is checked above because
its aggregator is proved; the completed boxes retain the dependency breakdown
used while the proof was developed.

- [x] RH1 trim a forward adjacent-branch configuration to a strict horseshoe
- [x] RH2 trim a backward adjacent-branch configuration to a strict horseshoe
- [x] RH3 obtain the Marr crossing configuration from commuting maps with no
      common fixed point
- [x] RL1 weak-lap counts are submultiplicative
- [x] RL2 a finite monotonicity partition gives an exponential upper bound
- [x] RL3 a two-branch horseshoe gives the `2^n` lower bound
- [x] RL4 construct the positive weak-lap convergence radius and divergent
      normalizing sequence
  - [x] RL4a prove summability below a block-controlled radius from
        submultiplicativity
  - [x] RL4b construct the positive finite formal radius, including the
        boundary coefficient lower bound
  - [x] RL4c choose increasing interior samples whose total resolvent diverges
- [x] RL5 diagonalize the cumulative normalized resolvents
  - [x] RL5a prove positivity of the total normalizing resolvent
  - [x] RL5b prove summability of every localized resolvent
  - [x] RL5c bound every normalized localized resolvent in `[0,1]`
  - [x] RL5d bound the adjacent-additivity error quantitatively
  - [x] RL5e prove that adjacent-additivity error tends to zero
  - [x] RL5f prefixes of a weak itinerary cell remain weakly monotone
  - [x] RL5g dominate tail lap counts by the global tail count
  - [x] RL5h bound itinerary-cell mass by radius power plus prefix error
  - [x] RL5i obtain two-sided eventual smallness around every point
  - [x] RL5j prove monotonicity under interval enlargement
  - [x] RL5k diagonalize on a fixed countable dense subset
  - [x] RL5l upgrade dense convergence to a Cauchy sequence at every point
  - [x] RL5m assemble the cumulative limiting coordinate data
- [x] RL6 recover all localized interval limits from the cumulative limit
  - [x] RL6a prove normalization at the left endpoint
  - [x] RL6b pass adjacent additivity to the localized subsequential limit
  - [x] RL6c assemble the localized interval functional
- [x] RL7 construct the continuous monotone surjective limit coordinate
  - [x] RL7a bound the localized limiting functional in `[0,1]`
  - [x] RL7b prove exact adjacent additivity of the limit
  - [x] RL7c retain the itinerary-cell radius-power estimate in the limit
  - [x] RL7d obtain two-sided local smallness of the limit
  - [x] RL7e prove the real coordinate is zero at the left endpoint
  - [x] RL7f prove the real coordinate is one at the right endpoint
  - [x] RL7g prove the real coordinate takes values in `[0,1]`
  - [x] RL7h identify all coordinate increments with localized limits
  - [x] RL7i prove monotonicity of the real coordinate
  - [x] RL7j prove continuity of the real coordinate
  - [x] RL7k package the interval-valued coordinate and its continuity
  - [x] RL7l prove monotonicity of the interval-valued coordinate
  - [x] RL7m prove its left-endpoint value
  - [x] RL7n prove its right-endpoint value
  - [x] RL7o prove surjectivity by continuity and endpoint values
  - [x] RL7p assemble `WeakLapResolventCoordinateData`
- [x] RL8 prove exact branch scaling for that coordinate
  - [x] RL8a bound the quantitative normalized one-branch transport error
  - [x] RL8b prove that transport defect tends to zero
  - [x] RL8c identify exact limiting mass scaling, including degenerate images
  - [x] RL8d deduce the coordinate absolute-scaling identity
- [x] RL9 telescope the source-coordinate lap contributions
  - [x] RL9a pass the cellwise source increment identity to the global
        partition sum
- [x] RL10 identify each target contribution with scale times its source
      contribution
  - [x] RL10a prove each lap's left endpoint precedes its clipped point
  - [x] RL10b restrict lap weak monotonicity to the clipped interval
  - [x] RL10c apply coordinate branch scaling to the lap contribution

### E. Extremal irreducibility (7)

- [x] E1 finiteness and positivity of the relevant fixed sets
- [x] E2 connected vertex-transitive interval intersection graph is complete
- [x] E3 disconnected component unions admit a respected monotone collapse
- [x] E4 an onto interval map has at least two fixed points of its square
- [x] E5 exact fixed-point descent through the component collapse
- [x] E6 identifying two fixed points strictly lowers the finite fixed count,
      and relinearization does not increase it
- [x] E7 existence of the factorial-return extremal irreducible factor

### P. Finite joint postcritical set (9)

- [x] P1 exact intrinsic vertex-value formula for a composition
- [x] P2 rectangle identity for commuting powers
- [x] P3 one-step difference inclusion
- [x] P4 finite tail-equivalence action on an assumed infinite orbit
- [x] P5 affine-cell collision forces a forbidden equality of scales
- [x] P6 each one-generator postvertex set is finite
- [x] P7 fixed sets of positive iterates of an expanding constant-slope map
      are finite
- [x] P8 exceptional points give a finite common forward-invariant hull and
      turns transport into that hull
- [x] P9 the full joint postcritical set is finite

### F. Repelling state and stabilized fold (8)

- [x] F1 the product has a finite fixed set with at least two points
- [x] F2 a consecutive fixed-point gap supplies a repelling directed side
- [x] F3 the factorial return powers fix that side with positive germs
  - [x] F3a a carried repelling side has a unique target side
  - [x] F3b the two generators induce finite permutations of repelling sides
  - [x] F3c the factorial return exponent annihilates both permutations
  - [x] F3d positive constant slope plus self-carry gives a positive dilation
        germ
  - [x] F3e assemble the two returned maps and one common germ radius
- [x] F4 nested product images produce the stabilized unit-speed ray
  - [x] F4a prove product nesting and the two generator forward-image laws
  - [x] F4b identify the returned interval hull and prove both returns are
        onto it
  - [x] F4c construct the stabilized ray core with continuity, initial germ,
        product return, and range identities
  - [x] F4d derive both generator dilation-return laws
  - [x] F4e prove local finite-piece unit speed on the nonnegative ray
- [x] F5 returned-power irreducibility makes its nonnegative range dense
- [x] F6 commuting maps agreeing near the germ agree globally
- [x] F7 a positive equality of scale powers gives equal returned iterates
- [x] F8 common-positive-iterate contradiction gives independent scales and
      the complete `TwoScaleFoldData`

### G. Standalone common-positive-iterate theorem (1)

- [x] G1 prove the inverse-limit/common-positive-iterate lemma entirely in
      the new import closure, including the specialized periodic fixed-set
      input needed by the manuscript argument

### C. Markov coding and eventual periodicity (8)

- [x] C1 finite postcritical hull gives a common Markov edge partition
  - [x] C1a constant slope with no intrinsic vertex is affine and strict on
        the corresponding cell
  - [x] C1b the fold base is fixed by both returned generators
  - [x] C1c adjoining the base to the postcritical hull preserves finiteness
        and forward invariance
  - [x] C1d package the resulting finite invariant set as the common Markov
        hull
- [x] C2 directed-edge substitutions are nonerasing and satisfy the exact
      path and edge-length scaling laws
  - [x] C2a characterize literal directed paths as chained directed edges
  - [x] C2b prove literal-path closure under append
  - [x] C2c propagate the starting vertex through append
  - [x] C2d propagate the ending vertex through append
  - [x] C2e prove additivity of word metric length under append
  - [x] C2f construct the exact ordered-vertex path between two Markov points
  - [x] C2g find a source partition cell straddling each Markov edge
  - [x] C2h identify the image-path metric length with endpoint distance
  - [x] C2i construct the full directed-edge substitution for one map
  - [x] C2j prove the all-directed-edge alphabet is nonempty
  - [x] C2k lift the one-map substitution to the occurring all-edge subtype
  - [x] C2l package the two returned-map substitutions
- [x] C3 every fold of the stabilized ray lies in the Markov hull, and
      successive Markov hits give its literal directed-edge itinerary
  - [x] C3a prove local finiteness of fold times for a locally finite-piece
        unit-speed path
  - [x] C3b specialize fold-time local finiteness to the stabilized ray
  - [x] C3c identify the ray value at parameter zero with the fold base
  - [x] C3d prove the returned-iterate scale-down identity for the ray
  - [x] C3e choose a positive returned power which scales a positive fold
        parameter into the initial germ
  - [x] C3f prove that positive parameter rescaling preserves and reflects
        the path-fold predicate
  - [x] C3g transport a positive fold to a genuine turn of a returned iterate
  - [x] C3h place critical values of every positive returned iterate in the
        joint postcritical set
  - [x] C3i conclude that every positive fold value lies in the common Markov
        hull
  - [x] C3j prove finiteness of Markov-hit times on compact parameter
        intervals
  - [x] C3k prove that Markov-hit times are unbounded along the ray
  - [x] C3l construct the next Markov hit after any current hit
  - [x] C3m package one successive-hit interval as a directed Markov-edge
        traversal with exact unit-speed length
  - [x] C3n concatenate the successive steps into the full directed Markov
        itinerary
  - [x] C3o lift that itinerary to the certified C2 alphabet
  - [x] C3p assemble `foldItinerary_exists` from the named C3 leaves
- [x] C4 the literal itinerary is a common prolongable fixed word
  - [x] C4a bound endpoint displacement by the metric length of a literal
        directed-edge path
  - [x] C4b prove uniqueness of a metric-minimal literal path with fixed
        endpoints
  - [x] C4c prove each modeled substitution image is metric-minimal
  - [x] C4d identify finite prefixes of `mapInfinite` at substitution cuts
  - [x] C4e identify prefix metric coordinates at substitution cuts
  - [x] C4f transport one itinerary edge through the return equivariance
  - [x] C4g lift the whole literal unit-speed itinerary through `mapInfinite`
  - [x] C4h prove uniqueness of literal unit-speed itineraries with the same
        path and initial edge
  - [x] C4i deduce substitution fixedness from return equivariance
  - [x] C4j specialize fixedness to the first returned generator
  - [x] C4k specialize fixedness to the second returned generator
  - [x] C4l deduce prolongability at the head from fixedness and metric
        expansion
  - [x] C4m prove every iterated seed image is the corresponding word prefix
  - [x] C4n assemble `commonFixedCoding_exists` from the 13 named leaves
- [x] C5 restriction to occurring letters preserves both fixed equations and
      makes both substitutions growing
  - [x] C5a occurrence is closed under every image of a substitution fixing
        the word
  - [x] C5b construct the finite retained geometric alphabet with exact range
  - [x] C5c lift the common word and preserve occurrence of every retained
        letter
  - [x] C5d lift each ambient image block to a nonempty retained image
  - [x] C5e prove infinite-substitution naturality under an injective embedding
  - [x] C5f descend ambient fixedness through that embedding
  - [x] C5g package the two restricted substitutions and fixed equations
  - [x] C5h lift the common seed and both prolongation tails
  - [x] C5i transport the positive metric and both exact scaling laws
  - [x] C5j transport the literal unit-speed itinerary
  - [x] C5k assemble `occurringAlphabetCoding_exists` from the ten leaves
- [x] C6 the positive metric vector identifies the two dominating eigenvalues
- [x] C7 adapter to the standalone Durand periodicity aggregator
- [x] C8 word periodicity implies `EventuallyPeriodicOnRay`

### C7 metric-Durand internal route: certified closure

These declarations are internal to the checked C7 aggregator and are not
additional entries in the 53-item manuscript-facing ledger.  At the current
certified checkpoint every item below is proved, the production dependency
route builds, and the entire new library contains zero executable proof holes.

- [x] M0 exact positive metric scaling gives uniform exponential growth bounds
      for every substituted letter
- [x] M1 higher-block presentations reduce recurrent-factor syndeticity to
      recurrent-letter syndeticity
- [x] M1 recurrent-parent cell argument: stable avoiding tower cell, powered
      tiling parent of a recurrent target, unbounded metric coordinate, genuine
      scale window, cofinal power-ratio hit, exact containment, and forbidden
      literal embedding
- [x] P1 construct the intrinsic recurrent-letter restriction for each source
      and prove image closure
- [x] P2 prove each recurrent restriction primitive and growing, and choose a
      positive prolongable power with its exact fixed data
- [x] P3 prove the two recurrent restrictions commute from the common fixed
      word and common exact positive metric
- [x] P4 use the finite orbit of a primitive fixed word to choose positive
      powers fixing one literal recurrent word
- [x] P5 relabel the recurrent alphabet to one finite `Fin rank` and package
      `MetricSynchronizedPrimitiveCoreData` with injective decoding, exact
      source-power intertwining, primitivity, and decoded-language equality
- [x] LR prove aperiodic linear recurrence of the synchronized word, including
      primitive fixed-point factor gaps, periodicity transport, and the lower
      return-word bound
- [x] M3 construct canonical cofinal prefix markers, complete return
      decompositions, bounded local return systems, faithful finite coding, and
      an actual repeated pair of levels
- [x] M4.1a prove the complete-return decoder reconstructs and fixes its
      displayed derived word
- [x] M4.1b transport periodicity of a derived word to a periodic recurrent
      language of the ambient word
- [x] M4.1c construct all paired first-letter derived stages
- [x] M4.1d realize every abstract stage at an actual canonical prefix level,
      using `marker_eq_take`
- [x] M4.1e extract a simultaneous repetition from the faithful finite code
- [x] M4.1f compose the interval of return decompositions and relabel it into a
      literal self-return for both local sources
- [x] M4.1g prove the self-return decoder primitive, apart from the explicit
      rank-one branch
- [x] M4.1h iterate the decoder to a depth at which every block contains every
      letter
- [x] M4.1i transport that all-letter self-return to a canonical base level
- [x] M4.1j choose one common depth realizing positive powers of both selected
      local sources
- [x] M4.1k identify the left and right transported metrics with the same
      actual return-block metric
- [x] M4.1l package both complete Proposition-10 inputs
- [x] M4.1m assemble the production common-derived system in
      `DurandCommonDerived.lean`
- [x] M4.2--M4.8 construct the two Proposition-10 power-equation families,
      including maximal factorizations, bounded gamma data, and constant finite
      coding subsequences
- [x] M5 use the common positive decoder metric to obtain its unique scale,
      subtract two power equations on each side, and eliminate that scale to
      obtain equality of positive powers of the original source scales
- [x] assemble `metricTheorem9_synchronized`: multiplicative independence
      excludes the power equality, so the common coding word is ultimately
      periodic

### T. Periodic path, periodic fold, and main assembly (5)

- [x] T1 local periodic-path equality globalizes after dilation
- [x] T2 onto periodic unit-speed paths have a global translation/reflection
      relation and the same full period group
- [x] T3 an eventually periodic ray supplies the periodic surjective return
      package consumed by `common_fixed_point_of_periodic_fold`
- [x] T4 prove the affine-circle lift, common reflection symmetry, and parity
      conclusion of `common_fixed_point_of_periodic_fold` inside the standalone
      library
- [x] M1 assemble reduction, extremal factor, fold, coding, and periodic-fold
      contradiction into the public theorem

`CommonIterate.lean` and `PeriodicFold.lean` are now standalone closed
obligations, including their formerly external support.  They contain no
wrapper import from the older library.

## Final certification record

The forward Coding, synchronized metric-Durand, geometric, backward assembly,
and terminal periodic-fold tracks are closed.  Final certification was then
performed in dependency order:

- [x] remove scratch-only modules and declarations outside the production
      dependency closure, and prune unused imports;
- [x] rescan the retained source for `sorry`, `admit`, project `axiom`
      declarations, and forbidden old-namespace references;
- [x] rebuild both `CommutingIntervalSimplified.Main` and the public
      `CommutingIntervalSimplified` target with Lake; and
- [x] run `#print axioms` on the production common-derived theorem, the
      synchronized comparison theorem, and
      `finitePieceMonotone_common_fixed_point_simplified`.  Each reports only
      `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or
      project-defined axiom.

## Completion gates

All formal-proof completion gates are satisfied:

- [x] every item R1--M1 is checked;
- [x] no retained source imports a module beginning `CommutingInterval.` or
      references that namespace;
- [x] static scans find no executable `sorry`, `admit`, or project `axiom`;
- [x] `lake build CommutingIntervalSimplified.Main` and
      `lake build CommutingIntervalSimplified` succeed;
- [x] the final theorem contains no `sorryAx` or project-defined axiom;
- [x] the import closure and scratch artifacts are pruned; and
- [x] this correspondence maps every manuscript interface to Lean or records
      the exact published substitution and internal Lean route.

The final pinned TeX contains both confirmed corrections and all eleven
tracked clarifications.  Its 989-line snapshot and SHA-256 are recorded at the
top of this file and in `MANUSCRIPT_CORRESPONDENCE.md`; the latter has been
rechecked against every manuscript theorem interface.  The revision-notes file
is retained as an applied historical record rather than a pending work list.
