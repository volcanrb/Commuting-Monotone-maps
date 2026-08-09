# Late-manuscript audit: directed-edge coding through the common fixed point

## Scope and bottom line

This audit compares the late part of
`common_fixed_points_piecewise_monotone_formalized.tex` (approximately lines
901--1340) with the retained Lean proof, and uses
`common_fixed_points_piecewise_monotone_direct.tex` as a candidate source for
repairs.

The main conclusion is important: **the criticism of the manuscript does not
show that the Lean theorem is unproved.**  The Lean development contains the
missing arguments.  The criticism is possible because the shorter manuscript
does not reproduce several of them, and sometimes substitutes an informal
sentence whose stated implication is not valid without additional lemmas.
Thus there are two distinct notions of “alignment”:

1. the manuscript and Lean reach the same mathematical conclusion through
   corresponding constructions; and
2. the manuscript actually supplies a journal-checkable proof of each
   construction.

The first is largely true in the late sections.  The second is not yet true of
the short formalized draft.  The newer direct draft already repairs the
Durand invocation and most of the cross-period/reflection argument, but it
still needs one explicit rescaled-path lemma and a more careful periodic-tail
package.

The late audit found no evidence that the final Lean theorem relies on a
project-specific axiom standing in for any of these claims.  In particular,
the long C0--C5 development proves the substitution comparison internally;
the paper is nevertheless free to cite Durand's published theorem instead of
reprinting that internal proof.

## Weighted repair ledger

The “weight” column measures the share of the mathematical checking and
writing needed to make this late portion independently journal-ready.  The
weights sum to 100; they are not counts of Lean declarations or manuscript
paragraphs.  “Direct source” records whether the newer direct draft already
contains a usable repair.

| No. | Item | Severity in short draft | Weight | Direct source |
|---:|---|---|---:|---|
| 1 | Rebuilt returned ray | major proof/method mismatch | 8 | substantially repaired |
| 2 | Full-alphabet common coding | major compression | 7 | cleaner outline available |
| 3 | One-step literal crossing | minor case compression | 2 | unnecessary on recommended route |
| 4 | Ordered powered decoding | major omitted invariant | 6 | unnecessary on recommended route |
| 5 | Occurrence restriction and generated presentation | moderate missing checks | 5 | substantially repaired |
| 6 | Exactness-to-primitivity and linear recurrence | critical logical omission if retained | 7 | unnecessary on recommended route |
| 7 | Six-step Cobham--Durand comparison | critical incomplete proof | 24 | repaired by direct Durand citation |
| 8 | Periodic return package | critical false/unsupported transitions | 16 | partly repaired; needs strengthening |
| 9 | Full period group | sound, small proof | 2 | reusable as written |
| 10 | Cross-period globalization | critical omission | 9 | substantially repaired |
| 11 | Rescaled original-map path and integral affine lift | major omission in both drafts | 7 | only outlined |
| 12 | Reflection, half translations, exact lift commutation | major omission | 5 | substantially repaired |
| 13 | Terminal parity and physical descent | sound | 2 | repaired/correct |
|  | **Total** |  | **100** |  |

If the recommended direct-Durand route is adopted, items 3, 4, and 6 can be
removed from the paper rather than expanded.  They remain genuine
mathematics in Lean because the axiom-free formalization proves the relevant
Durand comparison internally.  They are not dependencies of a journal proof
that cites Durand's theorem.  On that route, approximately 35 of the 100 raw
repair-weight points remain, concentrated in items 1, 2, 5, 8, and 11.

## Numbered findings

### 1. The rebuilt ray is proved in Lean, but not by the method stated in the short draft

**Manuscript.**  Proposition `prop:rebuilt-ray`, especially
`common_fixed_points_piecewise_monotone_formalized.tex:930-939`, says to
extend the initial edge by the two return equations and says that
“commutation and multiplicative independence make the extensions agree on
overlaps.”

**Lean.**  The construction is:

- `PolygonalUnitSpeedRayData` and `rebuildPolygonal_unitSpeedRay`,
  `CommutingInterval/PiecewiseLinearB9GeometrySupport.lean:921` and `:932`;
- `rebuild_returned_unitSpeedRay`,
  `CommutingInterval/PiecewiseLinearB9Scratch.lean:309`;
- `rebuiltRay_has_positiveMarkovSeed` and `exists_rebuiltRay_and_seed`,
  the same file at `:413` and `:446`.

The Lean construction first obtains positive affine right germs for both
maps, constructs a full nonnegative ray from the exact product map
`R = A \circ B`, installs the separate `A` and `B` actions using commutation,
and proves local finite unit speed by stabilizing the product-germ formula on
each compact parameter interval.  Exactness gives surjectivity of that full
ray.  **Multiplicative independence is not a hypothesis of
`rebuildPolygonal_unitSpeedRay` and is not what establishes overlap
compatibility.**

**Assessment.**  This is a method mismatch, not an unproved Lean theorem.
The sentence in the short draft should not remain.  The explicit stabilized
formula in `common_fixed_points_piecewise_monotone_direct.tex:1592-1622` is a
much better paper proof:

\[
  \Psi(t)=R^n\!\left(p_\theta+t/\widehat s^{,n}\right)
\]

for sufficiently large `n`.  The paper should verify independence of `n`,
compact-uniform choice of `n`, local unit speed, exactness-to-onto, and the
two separate equivariance identities.  That proof aligns with the actual
Lean geometry and removes the irrelevant appeal to independence.

### 2. D0 compresses four separate coding obligations into three sentences

**Manuscript.**  Proposition `prop:D0` and its proof are at lines 956--989.
It asserts the full substitutions, common fixed word, every seed-prefix
identity, geometric modeling, and both exact metric laws.

**Lean.**  These data are stored in `FullAlphabetRayCodingData`
(`PiecewiseLinearB9Scratch.lean:501`) and constructed by
`exists_fullAlphabetRayCodingData` (`:889`).  The underlying reusable
construction is `directed_edge_substitutions_and_common_ray_word`
(`PiecewiseLinearB9SymbolicSupport.lean:2389`).

The paper's proof needs to distinguish the following claims.

1. Every full-alphabet letter has a nonempty endpoint-compatible literal
   image, including letters never seen by the selected ray.
2. The two prolongable limit words have literal unit-speed itineraries for
   the same ray and therefore coincide.
3. The return equations imply fixedness and the all-depth seed-prefix laws,
   not merely a one-step itinerary relation.
4. Literal image length gives the metric law, and iteration gives unbounded
   seed-prefix length.

The current sentence “the seed-prefix statements follow from the initial
literal traversal” does not establish items 2 or 3.  A short induction plus
uniqueness of the literal itinerary is enough for a paper, but it must be
written.

**Recommended repair.**  Reuse the directed-edge construction in
`common_fixed_points_piecewise_monotone_direct.tex:1839-1905`, but add an
explicit lemma saying that the itinerary on
`[0,a^n|e_+|]` is `sigma_A^n(e_+)`, and similarly for `B`; the lengths tend
to infinity, so their limits are the same whole-ray word.  State explicitly
that the first letter of each seed image is the seed and that the remaining
tail is nonempty.

### 3. D1 is correct, but its proof suppresses the orientation cases

**Manuscript.**  Lemma `lem:D1`, lines 994--1010.

**Lean.**  `fullCoding_oneStep_literalCrossingComplete`,
`PiecewiseLinearB9Scratch.lean:1306`, is proved from a four-case analysis of
source orientation and monotonicity.  It uses literal containment between
the ordered endpoint states, not just abstract continuity.

**Assessment.**  The manuscript statement is correct.  Its proof is
acceptable only if “canonical subdivision” has already been defined as the
complete literal directed path and strict monotonicity on the source edge is
available.  One sentence should record the four possibilities (forward or
backward source, increasing or decreasing branch).  D1 can be deleted
entirely on the recommended direct-Durand route because it is used only to
reach the internal primitivity/Cobham implementation.

### 4. D2 states the right stronger invariant, but the successor proof needs one more displayed formula

**Manuscript.**  Lemma `lem:D2`, lines 1018--1049, correctly recognizes that
one-step membership is not an inductive invariant and instead states ordered
pointwise realization.

**Lean.**  The internal invariant is
`RealizesIteratedLiteralWord_d2` at
`PiecewiseLinearB9Scratch.lean:1372`; its zero, one-step, successor, and
crossing consequences run through `:1384`, `:1896`, `:2197`, `:2685`, with
the public aggregator
`fullCoding_pathWord_iterationCompatible` at `:2847`.

The manuscript gives the block endpoint
`s(|f_1|+...+|f_j|)`, but does not write the pointwise identity inside a
substituted block.  It should state that if `t=s d_{j-1}+u`, then

\[
  T^{n+1}\bigl(e(t/s^{n+1})\bigr)
  =T\!\left(T^n\bigl(e((d_{j-1}+u/s)/s^n)\bigr)\right),
\]

and use the one-step realization of `f_j` for `0 <= u <= s|f_j|`.
That identity and the metric duration law are what align adjacent blocks.
The final crossing consequence also needs the elementary fact that a literal
path in the line graph joining the two endpoints of a target edge in the
displayed order must traverse that edge.

**Assessment.**  The statement is mathematically appropriate; the proof is
still compressed.  As with D1, it can be omitted from the paper if Durand is
cited directly.

### 5. D3 needs to expose prolongability and generation, because Durand consumes them

**Manuscript.**  Proposition `prop:D3`, lines 1058--1080.

**Lean.**  The restriction is built in
`fullCoding_restrictToOccurringAlphabet`
(`PiecewiseLinearB9Scratch.lean:3399`) and packaged in
`ExactCommonRayCodingData` / `exists_exactCommonRayCodingData` (`:3433` and
`:3450`).  The older common-word package also explicitly stores fixedness,
prolongability, generation, every-letter occurrence, metric growth, and
prefix laws.

The invariant-occurrence argument in the manuscript is correct.  What is
missing from the statement is the exact boundary needed later:

- the retained seed is the head of the retained word;
- both restrictions are nonerasing and prolongable at that seed;
- every retained letter occurs in some iterated seed image, so the seed is
  generating for both substitutions;
- the powered substitutions retain these properties and have growing seed
  images.

The generation conclusion follows because the iterated seed images are
prefixes whose metric lengths tend to infinity.  It should be said rather
than left inside the later Cobham paragraph.

### 6. The short primitivity proof contains a real common-depth gap

**Manuscript.**  Proposition `prop:primitive`, lines 1082--1099, says that
exactness supplies a crossing depth for every ordered pair and that
finiteness of the alphabet gives one uniform depth.

**Lean.**  The relevant declarations are:

- `exact_crosses_all_directed_edges_uniformly`, beginning near
  `PiecewiseLinearB9Scratch.lean:3511`;
- `primitive_of_uniformCrossing_and_decoder` and the two primitive
  aggregators at `:3674`, `:3691`, and `:3706`;
- the linear-gap and syndeticity consequences at `:3725` and `:3745`.

Two details are essential.

1. Exactness of the whole source-edge interior does not control the order of
   preimages of the two target endpoints.  Lean splits each source edge into
   two ordered nonempty open halves, applies exactness to each half, and puts
   the two endpoint preimages in the required halves according to the source
   and target orientations.
2. Pairwise crossing depths cannot simply be replaced by their maximum.
   A target letter present at depth `d` need not remain present at every
   larger substitution depth.  Lean first derives surjectivity from
   exactness, pads each of the two exact hitting depths to a common depth,
   and only then takes a finite common bound.

Thus the manuscript's displayed implication is not valid as written.  The
linear-gap conclusion is also stronger than the last sentence proves: that
sentence gives a factor-dependent syndetic bound, while a uniform *linear*
bound requires the standard primitive-substitution recurrence estimate and
metric/image-growth comparison.

**Recommended repair.**  If primitivity is retained, reproduce the ordered
two-half/padding argument and cite or prove the standard linear-recurrence
theorem.  Preferably, delete D1, D2, and primitivity from the paper after
adopting the direct Durand invocation below.

### 7. The six-step return-word proof is not a proof; Durand is an exact replacement

**Manuscript.**  Lemma `lem:return-comparison`, lines 1107--1191.  The six
paragraphs name the stages of Durand's proof but omit the constructions and
estimates that make the result true.

**Lean.**  These omitted arguments are not absent from the formalization.
They occupy the C0--C5 chain in
`PiecewiseLinearB9Scratch.lean:4109-13466`, followed by
`primitive_twoScale_periodicRecurrentLanguage` (`:13472`) and
`exactCoding_word_ultimatelyPeriodic` (`:13502`).  In particular, the Lean
proof explicitly constructs the return towers, canonical seed/head data,
bounded comparison morphisms, boundary-error matrices, forward and reverse
eigenvalue inclusions, and the Perron specialization.

**Exact known-theorem substitution.**  Durand's published
[Definition 2 and Theorem 1](https://ems.press/content/serial-article-files/31803)
give precisely the needed implication: a one-sided sequence which is both
alpha- and beta-substitutive for multiplicatively independent Perron numbers
is ultimately periodic.  The relevant source is F. Durand, *Cobham's theorem
for substitutions*, JEMS 13 (2011), Definition 2 on p. 1803 and Theorem 1 on
pp. 1800--1801.

The paper should verify the hypotheses in one proposition:

1. take positive powers `u,v` so that `a^u,b^v` are Perron numbers;
2. the powered incidence matrices have those values as dominant
   eigenvalues;
3. the powered substitutions are nonerasing, prolongable on the actual head
   seed, and their seed images grow;
4. their generated fixed points are the same retained word `x`;
5. every retained letter occurs, and the letter coding is the identity;
6. `a^u,b^v` remain multiplicatively independent.

The first two points follow from the strictly positive length eigenvector.
The exact Lean interface is `PoweredPerronData` and
`commonRay_has_poweredPerronData` at
`PiecewiseLinearB9Scratch.lean:3764` and `:3790`, backed by
`common_ray_has_perron_powered_presentations` at
`PiecewiseLinearB9SymbolicSupport.lean:3303`.

`common_fixed_points_piecewise_monotone_direct.tex:1907-1994` already gives
a suitable Perron-power lemma and the correct direct Durand application.
That text should replace the six-step pseudo-proof.  This is not “using an
axiom” in the manuscript; it is an ordinary citation of a published theorem.
The axiom-free Lean proof remains stronger evidence because it formalizes the
cited comparison internally.

### 8. The return-package proof in the short draft does not match the formal argument

**Manuscript.**  Proposition `prop:return-package`, lines 1215--1245.  The
two problematic sentences are that dilation “moves periodicity backward
through the finite preperiod” and that periodic repetition “retains”
onto-ness.

**Lean.**  The actual chain is:

- symbolic period to eventual metric period:
  `ultimate_word_period_gives_eventual_metric_period`,
  `PiecewiseLinearB9SymbolicSupport.lean:8572`;
- periodic tail extension and inherited local unit speed:
  `exists_periodic_tail_extension` (`:8720`) and
  `periodic_tail_extension_unit_speed` (`:8863`);
- least period and full period group:
  `periodic_nonconstant_path_has_least_period` (`:8920`) and the following
  integer-multiple theorem;
- eventual return, naturality of the scales, and globalization:
  `periodic_extension_eventually_returns` (`:9007`),
  `expanding_return_scale_is_natural` (`:9073`), and
  `eventual_return_global_of_natural_scale` (`:9102`);
- onto-ness from exactness of the product return:
  `periodic_tail_core_package` (`:9214`) and
  `periodic_tail_range_eq_univ_of_exact` (`:9270`);
- final package:
  `PeriodicReturnPathPackage` (`:9291`) and
  `periodic_commonRay_produces_returnPathPackage`,
  `PiecewiseLinearB9Scratch.lean:13527`.

The short proof has two genuine problems.

1. An ultimately periodic word need not be periodic from position zero, so
   the ray's periodicity is not literally propagated backward by dilation in
   the way asserted.
2. The periodic tail need not a priori contain every point met during the
   finite preperiod.  Onto-ness of the original ray is therefore not simply
   “retained.”  Lean proves the tail image has nonempty interior, is forward
   invariant under the exact product map, and hence equals the whole
   interval.

The formal solution is clean.  Extend only the eventual tail periodically.
The two dilation identities are initially only eventual.  Obtain a least
positive period `T0`; show `a T0` and `b T0` are periods; the full period
group then gives `a,b` as natural numbers.  Those integral scales allow one
to shift any parameter by `N T0` and globalize the eventual return equations.
Exactness of `R=A\circ B` proves that the range of the periodic tail is all
of `I`.

`common_fixed_points_piecewise_monotone_direct.tex:1996-2060` follows this
route and is the right replacement, but it should add four explicit checks:
continuity of the shifted tail extension, nonconstancy from local unit speed,
the cancellation proving `a,b` integral, and the final shift-by-`N T0`
calculation that globalizes each return.

The alternative suggested in the external critique--primitive fixed point
plus ultimate periodicity implies pure periodicity--is also valid after a
uniform-recurrence lemma.  It is less closely aligned with the retained Lean
chain, so the periodic-tail package above is preferable.

### 9. The full-period-group lemma is sound

**Manuscript.**  Lemma `lem:period-group`, lines 1247--1255.

**Lean.**  `full_period_group_of_least_period`,
`CommutingInterval/OriginalPhase.lean:46`, and the analogous earlier
`path_periodGroup_eq_integer_multiples` in the symbolic-support file.

The floor-remainder proof is correct once `T0>0`, global periodicity, and
leastness have been established.  No expansion is needed here.  This lemma
can remain essentially unchanged.

### 10. Cross-period globalization is a major theorem, not a one-sentence expansion argument

**Manuscript.**  The first paragraph of Proposition `prop:phase-lifts`,
lines 1277--1283, says that a local germ match expands beyond one least
period and is therefore global.

That inference is insufficient for two different periodic paths: reducing
the left parameter modulo a period changes the right parameter by a shift
which is not yet known to be a period of the other path.  Equality of their
period groups is the conclusion, so it cannot be used at this point.

**Lean.**  `cross_period_globalization`,
`CommutingInterval/OriginalPhase.lean:253`, first obtains a local match,
expands it to intervals whose lengths tend to infinity, reduces the two
midpoint phases independently modulo positive periods, takes a convergent
subsequence in the product of two compact fundamental intervals, and then
passes to the limit.  Only after obtaining a global signed translate does it
deduce equality of the two period groups and least periods.

`common_fixed_points_piecewise_monotone_direct.tex:2064-2130` gives this
compactness/subsequence proof and should replace the short paragraph.  Its
statement should say “locally finite-piece with every affine slope of
absolute value one,” matching Lean's `IsUnitSpeedPeriodicSurjection`; the
current phrase “all nonzero slopes have absolute value one” unnecessarily
allows constant pieces.  Its local-match paragraph can be simplified further
by following Lean: take preimages of the right endpoint, whose right-hand
germs are forced to be unit-speed descents.

### 11. Both drafts still need an explicit rescaled-path lemma

**Manuscript.**  The short draft simply asserts that

\[
  t\longmapsto P(\Psi(t/C))
\]

is an onto periodic locally unit-speed polygonal path.  The direct draft at
approximately lines 2135--2150 makes the same assertion without proof.

**Lean.**  This is a substantial part of
`original_map_has_integral_affine_parameter_lift`,
`CommutingInterval/OriginalPhase.lean:1094`.  Its hypotheses include:

- `L>0`, `A=P^L`, `C>1`, and `a=C^L`;
- constant absolute slope `C` for `P`;
- an onto least-period unit-speed path for `Psi`;
- the `a`-dilation return for `A`.

Lean first proves `A` is onto from the path return, then proves `P` is onto
because a positive iterate of `P` is onto.  For finite-piece unit speed it
refines each compact parameter partition simultaneously by the vertices of
`P`: on a refined cell, `Psi(t/C)` has slope `+/-1/C` and `P` has slope
`+/-C`, so the composite has slope `+/-1`.  Its displayed period is
`C T0`, and commutation with `A` gives the common `A`-self-similarity.

After cross-period globalization, `C T0` is a period of `Psi`.  The full
period group gives `C T0=kT0`; since `T0>0`, `C=k` is a positive integer.
Substitution of `t=Cx` then gives the nonzero integral affine lift.  The same
argument applies to `Q`.

**Required repair.**  Add this as a named lemma before applying the
cross-period theorem.  This is genuine mathematics, not Lean-only partition
bookkeeping; the paper may present the partition refinement in one concise
paragraph.

### 12. The direct draft repairs the reflection and lift-commutation gaps

**Manuscript.**  The second paragraph of the short phase-lifts proof,
lines 1285--1294, asserts reflection existence/uniqueness, half-turn
translations, and exact lift commutation in a few sentences.

**Lean.**  The relevant chain is:

- `unique_reflection_of_expanding_dilation`,
  `OriginalPhase.lean:495`;
- `NormalizedRealAffineLiftData` and
  `normalized_real_affine_lifts_of_cross_period`, `:635` and `:1234`;
- `OriginalPhaseLiftPackage` and `original_phase_affine_lifts`, `:596` and
  `:1328`.

The missing arguments are:

1. a preimage of the interval maximum has forced unit-slope ascent/descent
   germs, yielding a local reflection;
2. expanding self-similarity makes its domain longer than one period and
   globalizes it;
3. two global reflections differ by a translation period, giving uniqueness
   modulo `T0`;
4. because each affine lift has nonzero degree, it is onto; conjugating the
   unique reflection through that lift produces another reflection, so the
   lift commutes with the reflection;
5. after centering the reflection at zero, this commutation gives
   `2u_P=2u_Q=0`, hence each translation is zero or a half turn;
6. physical commutation says the two affine compositions have equal images
   under `Psi`; their linear coefficients agree and their common nonzero
   degree makes one composition onto, so their constant argument difference
   is a period.  The full period group makes the affine lifts commute exactly
   on the circle.

`common_fixed_points_piecewise_monotone_direct.tex:2182-2300` supplies these
ideas in journal form and is reusable.  The reflection quotient introduced
there is unnecessary: once the normalized path is even and the parity lemma
finds `t` whose two images are `t` or `-t`, one can push directly through the
path, exactly as Lean does.  Removing the quotient also removes an otherwise
unproved assertion that the orbit quotient is an interval.

### 13. The corrected parity argument and final descent are sound

**Manuscript.**  Lemma `lem:parity`, lines 1297--1330, and the final
paragraph.

**Lean.**  `exists_common_reflection_orbit_of_half_translations`,
`CommutingInterval/AffineParity.lean:149`, and
`common_fixed_point_of_original_phase_package`,
`CommutingInterval/OriginalPhase.lean:1628`; the model-to-original descent is
in `PiecewiseLinearB10Scratch.lean:102-125`.

The four translation cases in the current short manuscript are the corrected
degree-sensitive cases and agree with Lean, including negative degrees.  The
earlier blanket half/quarter witnesses would have been false, but they are no
longer present.  Once the affine-lift package has been rigorously obtained,
evenness of the path turns preservation of the common reflection orbit into a
physical common fixed point.  The common strictly increasing coordinate then
pulls it back to the original PL maps.

## Recommended replacement order

The most efficient journal revision is:

1. Replace the short rebuilt-ray proof with the stabilized product-ray formula
   from the direct draft.
2. State one compact common-coding proposition containing fixedness,
   all-depth seed prefixes, occurrence restriction, prolongability,
   generation, metric eigenvectors, and growth.
3. Remove D1, D2, the primitivity proposition, and the six-step return-word
   synopsis from the body.  In the correspondence document, explain that
   these declarations are internal ingredients of Lean's axiom-free proof of
   the cited Durand theorem.
4. Insert the Perron-power lemma and the exact Definition-2 hypothesis check,
   then cite Durand Theorem 1.
5. Replace the return-package proof by the exact tail-extension / least-period
   / scale-integrality / exact-range chain.
6. Insert the direct draft's cross-period globalization proof.
7. Add the missing named rescaled-path lemma for
   `P(Psi(t/C))` and its `Q` analogue.
8. Use the direct reflection-uniqueness and affine-commutation arguments, but
   omit the unnecessary reflection quotient.
9. Retain the current parity proof and direct physical descent.

This route is shorter than the formalized draft's attempted C0--C5 synopsis,
more rigorous, and closely aligned with the formal proof at every interface
that the paper actually consumes.

## Exact late correspondence after the recommended revision

| Paper interface | Retained Lean declaration |
|---|---|
| rebuilt returned ray | `rebuild_returned_unitSpeedRay`; `exists_rebuiltRay_and_seed` |
| common occurring-edge word and metric data | `CommonRayFixedWord`; `directed_edge_substitutions_and_common_ray_word` |
| Perron-powered presentations | `PoweredPerronData`; `commonRay_has_poweredPerronData` |
| Durand--Cobham conclusion | internal C0--C5 chain ending in `exactCoding_word_ultimatelyPeriodic` |
| periodic tail and least-period returns | `periodic_commonRay_produces_returnPathPackage` |
| original affine circle lifts | `original_phase_affine_lifts` |
| common reflection orbit | `exists_common_reflection_orbit_of_half_translations` |
| physical/model common fixed point | `common_fixed_point_of_original_phase_package`; `markovSubstitutions_commonFixedPoint` |
