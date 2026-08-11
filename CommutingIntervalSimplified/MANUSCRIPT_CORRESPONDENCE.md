# Simplified manuscript--Lean correspondence

## Scope and trust rule

This is the live correspondence for `common_fixed_points_simplified.tex` and
the new Lean library rooted at `CommutingIntervalSimplified.lean`.  The map is
updated whenever a statement is frozen or closed.

The final audited TeX snapshot has 989 lines and SHA-256
`574FCF260AF68466A26F534BC4566F2803ED9D13931D99F3225E153BFEF38B03`.
The manuscript uses the ordered branch increment at TeX line 87;
any earlier audit note claiming it used an absolute-value bracket is
superseded.  The version discrepancy was confined to transient Lean APIs: an
impossible surjectivity field with codomain all of `Real` was replaced by
bounded interval-valued surjectivity, and the continuity/normalization
hypotheses needed by the branch-length operator were made explicit.  Neither
repair changes the manuscript's ordered `max`/`min` increment.

The manuscript may invoke a stronger published theorem in its natural form.
Lean never assumes such a theorem as an axiom: it either uses a theorem from
mathlib or a proved internal replacement.  When the mathematical routes
differ, the row below names the exact interface where they rejoin.

Current new-library status: every mathematical dependency of the public
theorem is present and the production route is build-green with zero
executable `sorry` or `admit` holes.  The library is standalone: its source
contains no import of, or declaration reference to, the older
`CommutingInterval` library, and no project `axiom` declaration has been
introduced.  The final dependency-pruning pass, clean public-root rebuild, and
public-theorem axiom audit are complete: scratch-only modules were removed,
static scans are clean, both `CommutingIntervalSimplified.Main` and the public
`CommutingIntervalSimplified` target build with Lake, and the production M4.1,
synchronized comparison, and final theorem report only `propext`,
`Classical.choice`, and `Quot.sound`.

The current production route is
`Coding C1--C5 -> DurandMetric M0--M1 -> DurandPrimitiveCore ->
DurandSynchronization -> DurandLinearRecurrence -> DurandCommonDerived ->
DurandPrimitiveComparison -> Coding C7/C8 -> PeriodicFold -> Main`.
The synchronized-core repair is now proved, not merely designed.  The two
source-specific recurrent restrictions first retain exact source-power and
decoded-language data.  Because the geometric application supplies one
common fixed word and one common positive metric, the restrictions commute;
a finite fixed-word orbit then yields positive powers fixing one literal
recurrent word.  After finite relabelling, both primitive substitutions act on
one `Fin` alphabet, fix that word, and scale the same pulled-back metric.
`DurandCommonDerived.lean` builds the complete common return system, while
`DurandPrimitiveComparison.lean` eliminates its common decoder scale to obtain
equality of positive powers of the source scales.  Multiplicative independence
therefore forces ultimate periodicity.  Language equality alone is never used
to assert a common literal word.

No old theorem import or namespace reference is permitted in the final
closure.

## Live map

| Manuscript interface | Lean interface | Correspondence and route | Status |
|---|---|---|---|
| Weak finite-piece monotonicity | `CommutingIntervalSimplified.FinitePieceMonotone` in `PiecewiseMonotoneBase.lean` | Standalone definition, including continuity and a finite weak-monotonicity partition. | closed |
| Finite-piece PL and constant absolute slope | `FinitePiecePL`, `HasConstantAbsoluteSlope` in `Base.lean` | Standalone predicates matching the manuscript definitions. | closed |
| Genuine turn sets `E(T)` and vertex values `V(T)` | `criticalDomain`, `criticalValues` in `Defs.lean` | Definitional aliases of the intrinsic `vertexDomain` and `vertexValues`; not arbitrary chosen partition vertices. | closed |
| Common monotone factor | `MonotonePairFactor` | Structure stores continuous monotone surjective coordinate and both semiconjugacies. Identity and composition are proved. | closed |
| Minimal expanding constant-slope counterexample | `NormalizedConstantSlopeCounterexample` | Stores exactly the finite-piece PL, onto, commuting, no-common-fixed-point, minimal-core, slope, and `>1` conclusions needed downstream. | closed interface |
| Least-length common invariant core in `lem:linearize` | `commonInvariantEndpointPairs`, `isClosed_commonInvariantEndpointPairs`, `endpointPairLength`, and `exists_minimalCommonInvariantCore` in `MinimalCore.lean` | This now follows the simplified manuscript literally.  Invariant endpoint pairs form a nonempty closed subset of the compact endpoint square; sequential closedness is proved by clamping an arbitrary limiting interval point into the approximating intervals and using continuity of both generators.  A minimum of `b-a` is then inclusion-minimal because a proper contained invariant interval would have strictly smaller length.  The previous Zorn/chain-intersection route was physically removed, and `Reduction.lean` supplies continuity from its finite-piece-monotone hypotheses. | Lean closed; route aligned |
| Branch-length identities `eq:length-increment` and `eq:length-composition` | B1--B4 declarations in standalone `BranchLength.lean` | Exact current definition in both sources: the linear ordered increment `S(max(u,v))-S(min(u,v))`, agreeing with absolute distance on nondecreasing coordinates. Partition independence, continuity, linearity, one-lap increment, composition, commutation, identity, iteration, and the onto endpoint estimate are proved. | closed |
| Finite-dimensional eigenspace and common Brouwer eigen-coordinate | B5--B6 in `BranchLength.lean` | Exact manuscript route. Evaluation on iterate-vertex images, finite dimensionality, simplex compactness, generator preservation, normalized-action continuity, the standalone standard-simplex/compact-convex Brouwer theorem, and final common-coordinate packaging are proved. | closed |
| Lemma `lem:linearize` (common constant-slope factor) | `common_constantSlope_factor_exists` with B1--B6/R1--R9 support | Complete standalone proof: the common invariant core is chosen by the compact least-endpoint-length construction above, its normalization is first embedded into the source, and only then is a monotone factor taken. The branch-length/Brouwer route proves product expansion, a compatible coordinate, exact branch scaling, finite dimensionality, a common normalized eigen-coordinate, constant-slope PL descent, exact fixed-point descent, and both slopes `>1`. The final TeX explicitly distinguishes affine normalization of the restricted subsystem from the subsequent monotone factor and states the factor's full minimal-counterexample conclusion. | closed and aligned |
| Lemma `lem:common-iterate` | `CommutingIntervalSimplified.common_positive_iterate` in local `CommonIterate.lean` | Exact standalone theorem. It follows the eventual-range/natural-extension/Bezout route; the specialized periodic fixed-set input is proved internally in local `ArcLikeFixedSet.lean`, so no publication is a Lean axiom. The earlier manuscript's invalid Bogatyi--Frolkina Theorem 3 appeal has been replaced in the final TeX by Fugate--McLean Theorem 1.5, an explicit arc-like inverse-limit verification, and the full projected-displacement argument. | closed and aligned |
| Returned-power irreducibility (equation `eq:irreducible`) | `ReturnedPowersIrreducible` | Exact predicate: any nondegenerate closed interval mapped onto itself by both return powers is the whole interval. | closed interface |
| Lemma `lem:irreducible` | `exists_extremal_normalized_counterexample` and E1--E7 in `Extremal.lean` | Complete standalone fixed-count minimization and component-collapse proof: exact phase family, component intervals and generator permutations, cumulative-length canonical collapse, descended PL regularity, strict descent, relinearization, minimization, and backward contradiction. The final TeX contains the endpoint-complete square-fixed-point argument and the full quotient-coordinate, fibre-respect, descended-PL, and relinearization construction. | closed and aligned |
| Lemma `lem:finite-postcritical` | `finite_jointPostcriticalSet` and P1--P9 in `Postcritical.lean` | New generic theorem under commuting, onto, flat-free finite-piece constant-slope, and multiplicatively independent hypotheses. Intrinsic turns and exact composition, rectangle/difference identities, finite-tail recurrence, common affine-cell collision, cross-periodicity, exact turn transport, construction of the finite common invariant hull, and the final joint-set assembly are proved. | closed |
| Nonnegative two-scale ray | `TwoScaleFoldData` | Structure records the initial unit germ, local unit speed, both dilation equations, scale independence, and dense nonnegative image. | closed interface |
| Common Markov hull and directed substitutions | `commonMarkovHull_exists` (C1) and `directedSubstitutionPair_exists` (C2) in `Coding.lean` | C1 constructs the finite common invariant vertex hull. C2 is now certified zero-hole: it constructs the nonempty all-directed-edge alphabet, realizes each returned-map edge image as a nonempty literal directed path, packages both nonerasing substitutions, and proves the exact metric laws with scale factors `a` and `b`. It does not assert substitution commutation. | closed |
| Published Durand eventual-periodicity input | `metricTheorem9_synchronized` in `DurandPrimitiveComparison.lean`, with `DurandMetric`, `DurandPrimitiveCore`, `DurandSynchronization`, `DurandLinearRecurrence`, and `DurandCommonDerived` support | The final paper invokes Durand's published theorem directly. Lean proves the exact-common-metric specialization supplied by the Markov coding: recurrent-parent syndeticity, primitive recurrent restriction, synchronized common powered fixed word, aperiodic linear recurrence, faithful bounded return systems, the common Proposition-10 package, and elimination of the common decoder scale. This intentional published/internal substitution is expanded below. | Lean closed; paper uses published theorem |
| Lemma `lem:two-scale` | F1--F8 in `Fold.lean` and C1--C8 in `Coding.lean` | The geometric half F1--F8 is complete: orientation-normalized repelling side, factorial return, stabilized locally unit-speed ray, exact generator returns, dense range, germ globalization, scale-power iterate equality, common-positive-iterate contradiction, and independent scales. The final TeX now includes the intrinsic definitions and the full simultaneous-reflection, unique side-action, compact returned-hull, radius-preserving scale comparison, and compact-uniform unit-speed arguments. The symbolic C1--C8 source, including C4's fixed-word construction, C5's occurring-alphabet restriction, and the proved synchronized metric-Durand dependency, is zero-hole. | closed and aligned |
| Lemma `lem:path-rigidity` | `periodic_local_match_globalizes`, `cross_period_globalization`, and `full_period_group_of_least_period` in `PeriodicPathRigidity.lean` | Exact standalone local-to-global and onto corollaries. The formal packaged path designates its least positive period; the eventual-tail bridge must construct this datum. | closed |
| Affine lifts, reflection, and four-torsion part of `lem:periodic-fold` | `original_phase_affine_lifts`, `common_fixed_point_of_original_phase_package`, and `exists_common_reflection_orbit_of_half_translations` | Entire terminal argument now lives in standalone `PeriodicAffineLifts.lean` and `AffineCircle.lean`; no old import. | closed |
| Eventual-ray-to-periodic-path part of `lem:periodic-fold` | T3 in standalone `PeriodicFold.lean` | Extends the tail, constructs its least positive period, globalizes both returns, and uses returned-power irreducibility for surjectivity. The final TeX explicitly proves local regularity and nonconstancy of the two-sided extension and local unit speed, onto-ness, and periodicity of the rescaled original-generator paths. | closed and aligned |
| Theorem `thm:main` | `finitePieceMonotone_common_fixed_point_simplified` in `Main.lean` | Complete zero-hole contradiction assembly R9 -> E7 -> F8 -> C8 -> T3 -> periodic fold. Every mathematical dependency is proved, both public builds succeed, and the transitive axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. | certified closed |

## Geometric F1--F8 closure audit

The completed geometric proof exposed four details that had to be explicit in
the journal argument.  They are mathematical steps, not Lean-only typing
devices.

- Before treating the directed-side actions as permutations, uniqueness of a
  carried target side is proved from the locally affine, locally onto image of
  a punctured source side.  This is the content represented formally by
  `ConstantSlopeSideImage.target_eq_of_carries` and the construction of
  `finiteRepellingSidePermutation_exists`.
- The stabilized returned interval is a genuine nondegenerate closed interval.
  The reverse inclusion in its return invariance uses compactness and closedness
  of the image, while nondegeneracy comes from the positive-length initial
  interval.  These points correspond to `returnedIntervalHull_exists` and
  `stabilizedRayCoreData_exists`.
- In the scale-power comparison, the initial germ radius is shrunk explicitly
  so that the original three return germs and both iterated germs remain valid.
  The formal bookkeeping is isolated in
  `FactorialReturnGermData.restrictRadius` and the iterated-affine-germ formula,
  after which `centralizer_germ_globalization` supplies the global equality.
- Local unit speed of the stabilized ray is proved uniformly on each compact
  parameter interval: one sufficiently deep representative works on the whole
  compact interval, and a finite affine partition is pulled back through that
  representative.  This is the mathematical content of the
  `StabilizedRayCoreData.locally_unit_speed` field.

These arguments now appear in the final manuscript in ordinary mathematical
language, without citing formal declaration names.  Their original audit
rationale remains recorded as items 8--11 in
`MANUSCRIPT_REVISION_NOTES.md`.

## Final-TeX journal-rigor audit

The completed audit was performed against the final 989-line snapshot with
SHA-256
`574FCF260AF68466A26F534BC4566F2803ED9D13931D99F3225E153BFEF38B03`.
Its scope was the complete mathematical chain: common linearization, common
positive iterates, extremal irreducibility, finite postcriticality, geometric
F1--F8, Markov coding and the published Durand input, periodic-path rigidity,
and the periodic-fold conclusion.

The two defects found in the earlier snapshot are corrected in the final TeX:

1. The common-positive-iterate proof now uses Fugate--McLean Theorem 1.5 for
   the connected fixed set of the periodic homeomorphism, after verifying that
   the natural extension is arc-like and hence tree-like, and then gives the
   full coordinate-projection displacement argument.
2. The proof that an onto interval map has two fixed points of its square now
   includes the endpoint cases through an endpoint-complete intermediate-value
   argument.

The two formerly compressed arguments are likewise expanded to journal-proof
level:

- The component collapse in `lem:irreducible` now gives the cumulative-gap
  quotient, proves that the generators respect its fibres, verifies finite-piece
  PL regularity of both descendants, and states the relinearization direction.
- The periodic-fold proof now verifies local regularity and nonconstancy of the
  two-sided extension and the locally finite-piece unit-speed regularity of the
  rescaled paths $P\psi(\cdot/C)$ and $Q\psi(\cdot/D)$.

The normalization, intrinsic-turn, orientation, side-uniqueness,
returned-hull, germ-radius, and uniform-ray clarifications are also incorporated.
The final orientation alternative is stated in `lem:two-scale` and explicitly
transported back in the proof of the main theorem.  No additional gap was found
in the branch-length finite-dimensionality/Brouwer argument, the tail-class
proof of finite postcriticality, the expanding-local-match proof of
periodic-path rigidity, or the affine-circle/four-torsion calculation.

The following formal details are intentionally absent from the paper because
they carry no mathematical content beyond the ordinary statements already
written there:

- subtype coercions for points of $[0,1]$ and separate endpoint membership
  witnesses;
- record constructors, `Nonempty` wrappers, and choices of witnesses from
  already proved existence statements;
- a particular finite index type for partition cells, endpoint-assignment
  conventions that change no interval image, and finite-cardinality API
  bookkeeping;
- proof-assistant-specific names for quotient representatives and descended
  maps once the mathematical fibre-respecting quotient and its regularity
  have been proved;
- syntactic associativity rewrites for iterates, composition, and commuting
  squares.

By contrast, the explicit quotient construction, uniqueness of directed-side
transport, compact closed-image argument, uniform germ radius, and finite
pullback refinements are genuine mathematics and therefore appear in the final
paper even though some of them look like implementation details at first.

## Published substitutions versus internal Lean proofs

The following differences are intentional and must remain visible:

1. The paper's BF/AM route supplies the initial product eigen-coordinate used
   in `lem:linearize`.  Lean proves only that published input internally, using
   a standalone weak-lap construction.  It then follows the manuscript's new
   branch-length finite-dimensionality and Brouwer argument; it does not use
   the old simultaneous-eigenmeasure shortcut for the common coordinate.
2. The corrected paper proof of `lem:common-iterate` uses Fugate--McLean,
   Theorem 1.5, followed by a direct projected-displacement/compactness proof
   of the remaining fixed point.  Hamilton is not needed.  Lean contains a
   standalone proof of the needed specialized fixed-set result in
   `ArcLikeFixedSet.lean`; the new import closure contains no
   reference to the old library.
3. The paper applies Durand's published general growing, nonerasing
   two-substitution theorem after restricting to the occurring alphabet; that
   is the clean journal proof and remains there.  The formal application
   has extra geometric information: one strictly positive edge-length vector
   is scaled exactly by each substitution.  These identities imply the
   manuscript's growing and dominant-eigenvalue hypotheses.  Lean formalizes
   that exact-common-metric specialization internally.

   Its syndeticity proof uses the recurrent-parent cell argument.  If a
   recurrent target had unbounded gaps, a positive power of one substitution
   would have a persistent target-free letter image.  A powered tiling for the
   other substitution assigns every recurrent target occurrence a unique
   parent cell.  Exact metric coordinates, arbitrarily late target parents,
   and cofinal density of the two scale powers produce a target-containing
   parent cell strictly inside a target-free cell, a contradiction.  This
   replaces both the false coarse-gap estimate and a later false universal
   arbitrary-window interface.

   The proof then restricts both substitutions to the same intrinsic alphabet
   of recurrent letters.  Syndeticity makes both restrictions primitive, and
   ordinary growth supplies a positive prolongable power.  The common fixed
   word and common exact metric identify corresponding substituted prefix
   cuts, which proves that the two recurrent restrictions commute.  The orbit
   of one primitive fixed word under the other restriction is finite; hence
   positive powers of both restrictions fix one literal recurrent word.
   Relabelling that alphabet to `Fin rank` gives an injectively decoded
   synchronized primitive core with one pulled-back metric.  This is the
   additional specialization that was missing from the abandoned asserted
   common-core interface; language equality alone is never used to construct
   the common word.

   On the aperiodic branch, primitive fixed-point gap bounds give linear
   recurrence.  Canonical prefix return decompositions then have uniformly
   bounded local data, so faithful finite coding supplies two genuinely
   equivalent levels.  The common-derived construction composes their return
   decoders into one primitive all-letter self-return and positive powers of
   both selected local sources.  Finally, the actual metric length of each
   return block makes the common decoder scale both source metrics by the same
   factor.  The two Proposition-10 power-equation families eliminate that
   decoder scale and yield equality of positive powers of the original scales.
   Multiplicative independence leaves only the periodic branch.

   This internal route proves only the exact-common-metric specialization
   required by the formal application; it does not replace the stronger
   published theorem in the paper.  The correspondence is recorded precisely
   here so the journal manuscript can use Durand directly without reproducing
   the formal specialization.
4. The paper's periodic-path proof is presented as ordinary mathematics.
   Lean proves the typed local-to-global, affine-lift, reflection, and
   four-torsion results in standalone local modules.  Lean-only packaging does
   not belong in the paper.

## Hygiene rule

The body of the aligned paper must not mention Lean, theorem declaration
names, proof-assistant typing devices, or this correspondence.  This document
alone explains differences between the journal proof and its formal
realization.
