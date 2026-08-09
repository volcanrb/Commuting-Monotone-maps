# Manuscript revision log

This file records changes discovered while formalizing and then fully
expanding the stronger theorem in
`common_fixed_points_piecewise_monotone_direct.tex`.  It is intentionally
cumulative: older route-specific observations are retained as history, not as
instructions for the current journal proof.  The stronger public theorem's
Lean dependency closure is zero-hole.  The current journal revision uses no
o-minimal input; it does use the broader published Parry--Shultz theorem in
place of the narrower returned-map measure construction carried out internally
in Lean.  Every such published-theorem substitution is identified explicitly
in `MANUSCRIPT_FORMALIZATION_CORRESPONDENCE.md`.

## Authoritative current route

This section is the authoritative status of the journal proof.  Later
sections of this file are a chronological research log; an imperative in a
later historical entry is not a current editorial instruction unless it is
repeated here.

- `common_fixed_points_piecewise_monotone_direct.tex` is the active
  reconstruction source.  At release it is copied byte-for-byte to the
  canonical journal file
  `common_fixed_points_piecewise_monotone_formalized.tex`.
- The paper uses exactly six published inputs: Bogatyi--Frolkina for positive
  entropy; Alsed\`a--Misiurewicz for the compatible constant-slope
  semiconjugacy and branch scaling; the Navas formulations of Kopell,
  Poincar\'e translation number, and Denjoy; Fugate--McLean Corollary 1.5;
  Parry--Shultz (Shultz Propositions 3.6 and 4.3 and Corollaries 4.4 and
  4.6); and Durand Definition 2 and Theorem 1.
- The general reduction in the paper uses real signed nonatomic measures and
  a finite-dimensional compact positive slice followed by Brouwer.  The
  complex-variation eigenvector construction is the internal Lean route, not
  the current journal route.
- The journal proof invokes Durand after checking every substitutive
  hypothesis.  The formal C0--C5 comparison, deep return towers, D2/D3
  decoders, and primitivity machinery are an internal Lean replacement, not
  sections of the paper.
- The weak-lap resolvent, closest-crossing horseshoe, Smith/nerve proof, and
  returned-map eigenmeasure construction remain genuine dependencies of the
  no-project-axiom Lean theorem.  In the paper they are replaced,
  respectively, by the published Bogatyi--Frolkina/Alsed\`a--Misiurewicz,
  Fugate--McLean, and Parry--Shultz inputs.
- O-minimality is neither a dependency of the retained theorem nor part of
  the current manuscript.
- The distribution factors in the current reduction are onto; any historical
  note below saying that the quotient lemma no longer asserts onto-ness is
  superseded.

## Full-exposition review closure (2026-08-09)

The current direct manuscript was reread end to end after the expanded
normalization and reduction were merged.  The review found no remaining
critical, high, or moderate mathematical gap, no lost hypothesis, and no
circular dependency.  In particular:

- the canonical finite quotient, fibre-respect condition, three fixed-count
  minimizations, directed-state permutation, finite arrival, endpoint basin,
  anchored LEO, and germ-determination arguments are now explicit;
- the old weak-resolvent exposition has been removed from the paper and
  replaced by the exact Bogatyi--Frolkina and Alseda--Misiurewicz inputs,
  followed by a complete real branch-transfer, finite-dimensionality, compact
  positive-slice, Brouwer, factor, and plateau-collapse proof;
- vertex composition, transverse preimages, finite postvertex sets, tail
  classes, the global tail relation, slope contradiction, and the common
  Markov set are proved as separate visible stages;
- the common-iterate proof uses Fugate--McLean Corollary 1.5 (journal
  p. 613), with every natural-extension and residual fixed-point step proved;
- the paper invokes Durand directly only after checking the exact
  substitutive boundary, while the correspondence records the Lean C0--C5
  replacement;
- the periodic extension, least-period group, scale integrality,
  cross-period globalization, original-map affine lifts, unique reflection,
  and all four parity cases are written out; and
- a final no-compression pass expanded the one-map dilation chart and made
  both uses of Lusin--Souslin in the preimage-transfer construction explicit.

The referee critique attached to this revision referred to the obsolete short
release manuscript.  Its eight substantive objections were valid for that
text, but none remains in the current direct manuscript.

## Global presentation and dependency changes

- State every external continuum-theory result at the exact topological
  strength used.  In particular, the inverse-limit/arc-like fixed-set theorem
  needs a metrizable setting; the unrestricted topological version originally
  suggested by the prose is false.  The Lean statement uses `MetricSpace`,
  compactness, connectedness, and the explicit arc-like approximation
  hypothesis.
- Separate standard imported research theorems from arguments proved in the
  paper.  The current formal dependency audit isolates the periodic
  homeomorphism fixed-set theorem and Durand--Cobham rather than allowing them
  to remain implicit inside larger paragraphs.
- Make all positivity assumptions explicit.  The Parry--Shultz scale used by
  the dilation and Perron arguments must satisfy `1 < scale`, not merely
  nonnegativity or `scale ≠ 1`.
- Introduce the normalized words `A`, `B`, `R`, and `S`, together with their
  continuity, surjectivity, commutation, finite-fixed-set, and tameness facts,
  as one named finite-arrival context.  This avoids repeatedly recovering
  hidden hypotheses later in the argument.

## Section: common positive iterate

- The periodic-homeomorphism input is exactly Fugate--McLean, Corollary 1.5:
  the fixed set of a periodic homeomorphism of a tree-like continuum is a
  nonempty continuum.  In the Lean development it is isolated at the weaker
  special case actually used: a nonempty compact connected metric arc-like
  space.  It must be proved internally rather than installed as an axiom.
  Nonemptiness has an elementary arc-like approximation proof; connectedness
  is isolated as the finite Smith/nerve argument described below.
- Do not replace that input by the previously suggested
  component/boundary-bumping converse.  That statement was not established by
  the cited paper, and ordinary connected components do not supply compact
  subcontinua in a non-locally-connected arc-like continuum.  Fugate--McLean's
  actual proof of connectedness is Theorem 1.4: construct an invariant
  one-dimensional cover, pass to its nerve graph, lift the null-homotopic map
  to the universal-cover tree, and use the finite-group fixed-set theorem for
  trees (Theorems 1.2--1.3).  Their later Theorem 1.6 proves the one-way
  `no moved pair in a fixed-point-free subcontinuum` result; it is not a proof
  of the discarded converse.
- Do not assert that an arbitrary finite-order action on an arc-like compactum
  admits invariant multiplicity-two refinements merely by saturating a chain
  cover.  Saturation can increase multiplicity by a factor as large as the
  group order.  The safe construction takes an ordinary fine chain cover,
  intersects all its translates to obtain an invariant common refinement,
  uses the full finite nerve, and barycentrically subdivides to regularize the
  simplicial action.
- The primary Fugate--McLean proof was checked directly. Their invariant
  one-dimensional cover is not obtained by naive saturation: it is pulled
  back from a one-dimensional cover of the finite orbit quotient `M/G`, using
  the separate theorem that this quotient is tree-like. They then lift the
  equivariant graph-nerve map to the universal-cover tree and apply the finite
  group fixed-set lemma there. Thus a literal port would require substantial
  quotient-dimension/tree-likeness and covering-space infrastructure. The
  full-nerve Smith route is the current replacement because it keeps those
  otherwise hidden boundaries explicit; it should be abandoned only if a
  complete comparison shows the quotient/graph route is smaller in Lean.
- A single equivariant nerve map which kills ambient reduced homology does not
  by itself give the required fixed-set `H_0` conclusion.  In the chain chase,
  after solving `f(z)=∂c`, the obstruction `(1-T)c` is a target cycle and need
  not come from a source cycle.  The correct Čech-Smith statement is pro-zero:
  use a finite coherent tower of finer invariant nerves, killing the successive
  obstruction at a later stage.  The tower terminates because each nerve is a
  finite bounded complex and the Smith filtration over `ZMod p` is finite.
- The invariant-nerve construction must be one bundled object, not three
  unrelated existential statements.  In particular, an abstract finite
  cyclic chain complex with no realization map (`∃ C, True`), an unconstrained
  pro-zero tower, and a separately chosen fixed `H_0` witness cannot be glued:
  they may refer to different covers and different chain maps.  The corrected
  interface carries at every level the finite invariant open cover, an
  identification of the chain basis with the full barycentric nerve, each
  equivariant cover refinement, and the assertion that the displayed tower
  map realizes that refinement.  When the fixed set is disconnected, the two
  fixed points, their fixed top nerve vertices, the reduced difference cycle,
  and its persistent non-boundary statement are fields of this same tower.
  Arc-likeness is an explicit hypothesis of the bundled existence theorem,
  because it is exactly what makes the ambient refinement maps pro-zero.

## Section: finite arrival

- The endpoint-attraction step has a cleaner proof that avoids first proving
  local derivative monotonicity.  Let `D_n = R^n(J)`.  Finite fixedness gives a
  one-sided neighborhood of a missing endpoint containing no other fixed
  point, so continuity makes the sign of `S(x)-x` constant there.  The
  singleton endpoint fibre and compactness of the opposite closed side imply
  that every sufficiently endpoint-near value has all its preimages in that
  neighborhood.  Choose the extreme point of `D_{n+2}` near the missing
  endpoint and pull it back through `S(D_n)=D_{n+2}`.  Nestedness gives the
  weak inequality toward the endpoint, ruling out the repelling sign.  An
  arbitrary local forward orbit is then strictly monotone; compact monotone
  convergence and continuity force its limit to be the endpoint.  This route
  is both shorter and topological, and cleanly separates attraction from the
  later `C^1` monotonicity/basin-closure argument.
- Explicitly name the two distinct roles of tameness in this section:
  finiteness of `Fix(S)` determines the local sign, while finite-piece `C^1`
  regularity is only needed afterward to obtain a strictly monotone local
  branch and the basin package.
- The diagonal range proof is best ordered backward: first package its
  compactness, connectedness, and nonemptiness; then apply the labelled-phase
  Helly argument to show the common core is the full interval; finally infer
  that the diagonal range itself is the full interval and its increasing
  union is dense.
- In the LEO step, do not claim that an orbit beginning inside the repelling
  gap must cross the opposite fixed endpoint; it may converge to that endpoint
  from below.  Finite arrival instead supplies preimages, strictly below that
  endpoint, of both ambient endpoints under one normalized iterate.  Their
  maximum is a compact interior threshold.  A repelling orbit must cross this
  threshold in finite time (otherwise its monotone limit would be an interior
  fixed point), and the intermediate value theorem then makes the same
  normalized iterate cover the whole interval.  This proves the stated LEO
  conclusion without the false finite endpoint-crossing subclaim.

## Section: Perron arithmetic

- State the weak-Perron input with the positive eigenvector data actually used:
  a natural matrix, a strictly positive real eigenvector, and its eigenvalue.
  This directly proves dominance by a weighted max norm and avoids silently
  invoking irreducibility.
- For peripheral eigenvalues, the formal proof uses equality in the weighted
  triangle inequality to propagate a common phase along every positive
  matrix edge.  A finite pigeonhole argument followed by a factorial power
  kills all possible phases.  This is a more elementary replacement for the
  prose invocation of Frobenius block form and the periodic Perron--Frobenius
  theorem.
- Spell out the arithmetic bridge: an eigenvalue of an integer matrix is
  integral; every algebraic conjugate remains an eigenvalue; strict interior
  conjugates shrink under powers, while factorial powers collapse peripheral
  phases.  The resulting positive power is a Perron number.

## Section: orbit-to-dilation globalization

- The passage from a simultaneous translation chart to local dilation
  factors must retain the strict positivity `0 < d` of the selected deck
  exponent.  Exponentiation gives
  `scaleA * scaleB = lambdaScale ^ d`; the later strict inequality
  `1 < scaleA * scaleB` is false when `d = 0`, and irrationality of the phase
  alone does not exclude that case.
- The same bridge must explicitly retain that the three physical actors fix
  the base point.  The far-left translation chart only controls the open
  punctured side and says nothing about values at its endpoint, whereas a
  `LocalRayScaleAction` evaluates its equivariance law at the ray origin and
  therefore forces `W p = p`, `A p = p`, and `B p = p`.

## Section: constant-slope models

- Isolate the elementary finite-partition calculus for constant-absolute-slope
  maps as its own lemma package.  Refining the inner partition by the
  preimages of the outer partition vertices proves that slopes multiply under
  composition; induction then gives slope `s^n` for the `n`th iterate.  The
  formally stated composition lemma also has a zero-inner-scale case: the
  global distance estimate shows that such an inner map is constant.  This
  edge case should either be stated or positivity should be introduced before
  composition is used.
- The scale bound for an exact model has a short metric proof.  Summing the
  affine estimates across the finitely many partition cells gives
  `dist (T x) (T y) ≤ s * dist x y`; iteration gives the corresponding
  `s^n` bound.  If `s ≤ 1`, the image of the open interval cannot contain
  both endpoints because every pair in the open interval has distance less
  than one, contradicting topological exactness.  This avoids invoking any
  heavier entropy or invariant-measure machinery.
- The common Parry-coordinate lemma should take the already assumed
  commutation `P Q = Q P` as an explicit hypothesis.  There is no reason to
  infer it from the separate relations `P R = R P` and `Q R = R Q`; doing so
  creates an unnecessary and substantially stronger centralizer theorem.
  Conjugating the given commutation directly proves that the two polygonal
  models commute.
- Likewise, preservation of multiplicative independence uses more than
  equality of two absolute slope magnitudes.  It uses the common fixed base
  and the two *positive* affine germs at that base.  Those data make the
  corresponding positive powers agree locally; exactness then globalizes
  the equality.  The formal lemma interface should carry the fixed-base and
  right-germ orientation hypotheses explicitly.

## Section: the repelling right germ

- The existence of a positive `C^1` right-germ representative should be
  proved directly from the selected repelling gap, rather than folded into a
  broad regularity assertion.  Choose the finite-piece `C^1` cell immediately
  to the right of the fixed endpoint `p`.  Since `W(x) > x` on that gap and
  `W(p) = p`, every right secant slope is at least one, so the right limit gives
  `W'(p) ≥ 1`.  Continuity of the derivative then supplies a smaller segment
  on which `W' > 1/2`.  The definable `C^1` derivative has bounded variation
  there, and composition with the Lipschitz restriction of `log` to
  `[1/2,∞)` gives bounded variation of the logarithmic derivative.  This
  exposes exactly where repulsion, finite-piece regularity, and definability
  enter the germ argument.

## Section: Parry transfer and strict-lap geometry

- Keep the strict-lap partition available through the spectral-existence and
  uniqueness arguments.  A `FiniteInjectiveCoverPS` intentionally remembers
  only a finite disjoint measurable injective cover.  That abstraction is
  enough to define the cover-independent set-counting transfer measure, but
  it forgets the closed interval branches and their shared endpoints.
  Those data are needed for the standard compactness proof: first use the
  overlapping closed laps to form the multiplicity transfer whose dual is
  continuous at turns, construct an eigenmeasure there, prove that the
  eigenmeasure has no atoms, and only then remove the endpoint
  multiplicities to recover the set-counting transfer.  Accordingly the
  internal Perron lemmas take the original `RealPartition` and its strict-lap
  proof, while the final public Parry--Shultz theorem retains the manuscript's
  partition-free `HasFiniteStrictMonotonicityLaps` statement.
- Separate the elementary exactness support argument from the transitive
  interval classification.  For any finite injective cover, measurable null
  sets have null forward image under a transfer eigenmeasure.  Hence
  topological exactness alone immediately gives full support.  The general
  transitive theorem additionally needs the classical period-two alternative;
  it should not silently replace transitivity by exactness.
- For existence, follow Chris Preston, *A Note on a Theorem of Parry*,
  arXiv:1008.0818, pp. 11--14 (Lemmas 6--13).  For a closed interval `J`,
  Preston normalizes the generating series of the numbers of laps of `T^n`
  meeting `J`.  The total series diverges at its radius; the errors in
  additivity across one endpoint and in shifting a monotone interval are only
  one geometric series and one initial lap, respectively.  A diagonal limit
  therefore gives an additive interval-length functional with exact branch
  scaling and an `r^m` bound on intervals where `T^m` is monotone.  Integrating
  this functional from the left endpoint produces the constant-slope
  semiconjugacy, and transitivity makes it injective.
- Preston chooses a *minimal* monotonicity partition and writes his cut sets
  as the turning points of the iterates.  Our hypothesis supplies an arbitrary
  strict-lap partition, which may contain redundant same-direction points.
  The formal resolvent consequently uses the intrinsic `genuineTurns T` and
  must prove (from the supplied partition) both its finiteness and the identity
  between turns of `T^n` and the finite union of their first `n` preimages.
  This is the main hypothesis/interface difference from Preston's notation.
  Keep the resulting cut-set finiteness hypothesis explicit in every local
  resolvent comparison.  In Lean, `Set.ncard` is defined to be zero on an
  infinite set, so convergence of the total series cannot be used as a
  surrogate proof that the intrinsic cut sets are finite: an infinite total
  cut set could otherwise collapse to lap count one while a finite local
  intersection has larger `ncard`.  The strict partition proves finiteness
  first; only then is domination of every interval series by the total series
  valid.
  Preston also phrases transitivity via closed invariant sets and invokes the
  exact/semi-exact horseshoe theorem for positivity of entropy; our statement
  uses the open-set hitting formulation, so those equivalences and the
  horseshoe consequence must be proved explicitly rather than assumed.
- In the no-strict-away branch of the Block--Coven/Parry seed construction,
  do not claim that `T^2` itself always has a strict turbulent seed.  A
  half-swapping transitive map obtained from a reflected full tent map has a
  unique fixed point; `T^2` preserves each half and can have only the touching
  seed allowed by the endpoint configuration.  Squaring that touching seed
  gives a strict seed for `T^4`.  The correct statement is therefore that
  *some positive iterate* has a strict turbulent seed (`N=2` in the strict
  branch and `N=4` in the touching half-swap branch).  Only this variable
  positive iterate should be fed to the lap-growth estimate.

## Section: rebuilding the polygonal ray

- The rebuilt-ray statement must retain the orientation of the selected
  germ.  A constant absolute slope and a fixed point do not determine that
  orientation: the full tent map at its interior fixed point has a negative
  right slope, even though it is exact and has constant absolute slope.  The
  Parry-coordinate package therefore needs to record that its distribution
  homeomorphism is increasing (or, equivalently downstream, explicitly carry
  positive right-germ formulas for the transformed actors).
- The first-Markov-edge traversal also needs an expanding return scale.  Once
  `a > 1` is retained, the proof is elementary.  Choose the least Markov
  vertex `q > p`; a tiny portion of the initial linear ray and the return
  identity determine the affine coefficient of `A` on `[p,q]` to be `+a`.
  Any parameter in `[0,q-p]` can then be divided by a sufficiently large
  power of `a`, placed in the initial linear chart, and propagated forward
  while every intermediate point remains in the same Markov edge.  This
  proves literal unit-speed traversal of the whole first edge.
- Record that the Parry distribution coordinate is strictly increasing.
  This is not cosmetic: it transports the already established positive
  right-hand monotonicity germs of the normalized actors to the transformed
  constant-slope models.  Absolute slope without this orientation datum is
  insufficient.
- The clean formal construction starts with the clipped identity chart
  `t ↦ p+t` on a small right interval.  The two positive affine germs
  compose to the product germ with multiplier `ab`; exactness of the product
  supplies the closed-interval covering hypothesis needed to extend that
  germ to an onto ray.  Commutation then globalizes the two individual
  dilation identities.
- For local unit speed, fix a compact parameter interval and divide it by a
  sufficiently large power `(ab)^n` so that it lies in the identity chart.
  Pull the finite constant-slope partition of `R^n` back under the affine
  parameter map `t ↦ p+t/(ab)^n`.  Every pulled-back branch has slope
  `m/(ab)^n` with `|m|=(ab)^n`, hence absolute speed one.  This explicit
  pullback-partition proof is clearer than the manuscript's sentence that
  local finite-piece PL regularity is automatic.

## Section: postvertex finiteness

- The standalone finite-postvertex lemma must retain `1<a` and `1<b`, not
  only multiplicative independence.  The contradiction extracted from the
  rectangular vertex identity can degenerate to `b^r=1`; independence alone
  does not exclude this when `b=1`.  Indeed, the identity map can be
  multiplicatively independent from an expanding scale under the displayed
  definition.  In the actual Parry model both strict inequalities have
  already been proved, so add them to the lemma interface and pass them
  explicitly into the Markov-set construction.

## Superseded first-proof checklist (historical)

The following were open presentation items at this earlier gate. They are not
current tasks: the stronger proof later supplied or replaced each item, as
recorded in the dated sections below.

- The final form of the ray residue/density argument and its simplified fixed
  compact-window proof of exactness.
- The precise imported statement of Durand--Cobham and the reductions needed
  to satisfy its alphabet/growth hypotheses.
- Any normalization/reflection hypotheses that become visible while removing
  the remaining proof-state fields.

## Section: endpoint basin closure

- The fixed-barrier hypothesis must say that the barrier is an interior
  point, not merely a fixed point distinct from the attracting endpoint.
  The weaker statement is false: for
  `S(x)=2x^2-x^3` and `e=0`, every point of `(0,1)` is attracted strictly to
  `0`, the endpoint fibre is `{0}`, and `1` is a distinct fixed point, but the
  closure of the immediate basin is the whole interval.
- The main finite-arrival context supplies the stronger hypothesis.  If an
  ambient endpoint has not appeared at phase zero, it is not in the initial
  selected gap `[p,c]`.  Thus a missing left endpoint forces `0<p<c`, and
  `p` is an interior fixed barrier; a missing right endpoint forces
  `p<c<1`, and `c` is an interior fixed barrier.  The old orientation-free
  `by_cases p=e` choice selected the wrong barrier in one case.  State the
  left/right cases explicitly.
- Local strict monotonicity near the singleton endpoint fibre is a genuine
  one-variable o-minimal monotonicity input.  It does not follow from the
  existing global flat-free finite-lap lemma, because a map can have flat
  cells away from the endpoint.  Isolate the local endpoint version, then
  prove openness, connected-component closure, boundary fixedness, and the
  onto relation internally.

## Section: internal one-variable o-minimal calculus

- The formal development now derives the needed monotonicity theorem from the
  semantic o-minimal interface rather than postulating it.  The three
  definable sets of points that are eventually increasing, constant, or
  decreasing to the right have finite frontiers.  Refining by those frontiers
  gives a finite partition, and continuity upgrades the resulting open-cell
  behavior to strict monotonicity, strict antitonicity, or constancy on each
  closed cell.  Flat-freeness eliminates the constant cells; at an endpoint,
  the range bound eliminates the wrong orientation and the singleton fibre
  eliminates constancy.
- Derivative definability is likewise obtained internally.  Encode nontrivial
  secant slopes by the ordered-field graph operations, then express
  accumulation of those slopes at the diagonal using quantified open boxes.
  On an open `C¹` domain, the slope-limit theorem identifies this first-order
  relation with the graph of `deriv`.  Applying the finite monotonicity
  partition to an affine reparametrization of a compact interval gives finitely
  many monotone, antitone, or constant derivative cells.  Enumerating the
  partition vertices in order and using additivity of extended variation
  proves bounded variation without an additional analytic axiom.

## Section: original-phase globalization

- The local unit-speed match and reflection do not need a regular-value
  argument.  Choose a parameter mapping to the right endpoint.  On the first
  affine edge immediately to its right, unit speed gives slope `±1`; the
  upper range bound rules out `+1`, so this edge is the unit descent.  The
  first edge immediately to the left is similarly forced to be the unit
  ascent.  Translating two right descents gives the local two-path match,
  while pairing the left ascent with the right descent gives the local
  reflection.  This proof uses only the finite PL subdivision, surjectivity,
  range bounds, and unit-speed hypothesis.
- Separate the finite-vertex local matching lemma from cross-period
  globalization.  Once two unit-speed periodic paths agree up to sign and
  translation on one nonempty interval, iterating the common expanding
  dilation gives agreement on intervals whose lengths tend to infinity.
  Reducing their midpoints modulo the two least periods and taking a compact
  subsequential limit yields the global signed translation.  The formal proof
  also shows directly, in both orientations, that each least period is a
  positive period of the other path.
- Likewise separate the local fold from reflection globalization.  Expansion
  makes one local reflected interval longer than a full period; reducing an
  arbitrary parameter into that interval proves the global reflection.
  The product of two reflection symmetries is a translation, so the already
  proved full-period-group lemma gives uniqueness modulo the least period.
- After cross-period comparison supplies the two nonzero integral real
  affine lifts, all remaining steps are elementary and should be displayed:
  center the unique reflection, descend the normalized real path to
  `R/Z`, prove that each translation is `0` or `1/2` by turning it into a
  second reflection, derive exact affine-lift commutation from physical
  commutation and the full period group, and only then invoke the four-case
  parity lemma.  This avoids treating the entire original-phase conclusion
  as a black box.
- The integral affine lifts themselves can also be constructed without a
  separate lift axiom.  For an original actor `P` of slope modulus `C`, the
  return identity `psi(C^L t)=P^L(psi(t))` makes `P^L`, and hence `P`, onto.
  The rescaled path `v(t)=P(psi(t/C))` has a one-sided unit-speed descent at
  a preimage of the right endpoint, so it locally matches `psi`; expanding
  self-similarity globalizes this to `P(psi(t))=psi(Ct+delta)`.  Shifting by
  the least period shows that `C` times that period is another period, and
  the full period-group theorem forces `C` to be a nonzero integer.  Apply
  this separately to `P` and `Q`, then recenter at `gamma/2`.

- The formal interface must not say that an arbitrary continuous
  semiconjugating lift is affine.  A periodic path into an interval folds, and
  at a fold a continuous real parameter lift can switch to the reflected
  branch while preserving the same path-valued semiconjugacy.  The manuscript
  should therefore construct the signed affine formula directly by comparing
  the finite unit-speed periodic paths
  `t ↦ P(psi(t / C))` and `psi`, and likewise for `Q`.  Only those canonical
  affine formulas should be packaged for the subsequent commutation and parity
  argument; no uniqueness claim for all continuous lifts is needed.

- The commutator cannot be measured against an arbitrary recorded positive
  period.  If `P₀` is twice the least path period, a genuine period difference
  can equal `P₀/2` and need not be an integral multiple of `P₀`.  Before the
  affine-lift commutation calculation, construct the least positive period of
  the nonconstant finite unit-speed path and prove that every global period is
  an integer multiple of it.  State all circle quotients and commutator integers
  using this least period, not the initially supplied witness of periodicity.

## Dependency cleanup for the orbit-circle section

The proved Kopell, expanding-fixed-point, Denjoy--Koksma, and orbit-circle
arguments do not use an o-minimal structure or the normalization proof-state
types.  Their former dependency on `Normalization.lean` was only an overly
broad import.  The checked production refactor imports `DynamicsDefs` and the
specific derivative mean-value, power, and shift modules instead; a full Lake
build succeeds and the orbit module's transitive dependency list contains none
of `Normalization`, `Definability`, or `TameLemmas`.  The revised manuscript
should therefore present the orbit-circle dichotomy as a purely local
`C^{1+BV}` theorem and omit all o-minimal discussion from this stronger proof.

## Precisely isolated external inputs

- Keep the proved o-minimal one-variable consequences as named intermediate
  results rather than hiding them inside the elementary interval argument:
  finite fibres and strict laps for flat-free tame maps, endpoint
  monotonicity from singleton fibres, derivative bounded variation on compact
  subintervals, and tame descent through canonical finite quotients.  These
  are now internal consequences of the semantic interface, not external
  axioms.
- State local `C^{1+BV}` Kopell and the lift form of Denjoy explicitly, with
  the exact germ domains, positivity, BV, and irrational translation-number
  assumptions used by the proof.  The direct-limit one-sided orbit-line
  construction is a separate input from those analytic theorems and should
  not be conflated with either one.
- State Durand--Cobham in the substitution form actually consumed by the
  proof: finite source and target alphabets, prolongable generating seeds,
  recurrent occurrence of every retained letter, growing images, dominant
  Perron eigenvalues, multiplicative independence, and letter-to-letter
  codings of the same target word.  This makes the later application a
  literal instantiation rather than an appeal to an underspecified version
  of Cobham's theorem.

## Section: finite postvertex sets

- State the expansion hypotheses `1 < a` and `1 < b` in the finite-postvertex
  lemma itself, not only in its surrounding Parry-coordinate context.  The
  tail-class argument ends with `a^p b^r = a^q`; when `p = q`, its
  contradiction is `1 < b^r`, and multiplicative independence alone does
  not exclude the scale `b = 1`.
- A clean proof avoids choosing compatible representatives in the two
  postvertex sets.  Constant positive absolute slope gives finite fibres, so
  an infinite `A`-orbit remains infinite after applying the commuting map
  `B`.  The rectangular vertex identity says that, unless a `B`-image has
  already returned to the `A`-postvertex set or landed in the finite
  `B`-vertex seed, it is `A`-periodic.  Hence some forward `A`-shift of every
  infinite-orbit `B`-image returns to the `A`-postvertex set.
- Starting from an `A`-vertex with infinite `A`-orbit, iterate that return
  step for `B^n`.  Each stage has an equality
  `A^{s_n} B^n(w) = A^{q_n}(v_n)` with `v_n` in the finite `A`-vertex seed
  and with infinite `A`-orbit.  Pigeonhole two equal `v_i=v_j`; commuting the
  maps gives equality of two mixed iterates on the infinite orbit of this
  vertex.  Their constant-slope formulas agree on a nondegenerate interval,
  exact-centralizer propagation makes them globally equal, and uniqueness
  of the absolute slope yields `a^α b^{j-i}=a^γ`.  Expansion forces
  `α<γ`, so this is the forbidden positive-power relation
  `a^{γ-α}=b^{j-i}`.  Swap `A,B` for the other postvertex set.
- For the common Markov set, first adjoin the finite cross-image corrections
  `B(post(A)) \ (post(A) ∪ post(B))` and its symmetric counterpart.  The
  rectangular identity makes every such correction periodic under the
  opposite map.  Adjoin the corresponding finitely many fixed sets of
  positive iterates; exact-centralizer rigidity proves each fixed set finite,
  and commutation makes their union invariant under both maps.  Finally add
  both intrinsic vertex domains and the chosen common fixed point.  The
  composition formula for intrinsic vertices gives cross-invariance of the
  added domains.
- On an edge containing no intrinsic vertex, refine a constant-slope
  partition by the two edge endpoints.  Extend one affine formula to a
  maximal refined partition endpoint.  At the next cell an opposite signed
  slope would create a genuine turn, while an equal signed slope has the same
  coefficient and continuity gives the same intercept.  Thus maximality
  reaches the other endpoint, proving both affinity and strict monotonicity
  on every Markov edge.
- Equality of positive powers of the *absolute* transformed slopes does not
  by itself give local equality of the transformed maps: the signs and
  affine intercepts of their branches are otherwise unrelated.  The scale
  dependence-to-common-fixed-point step must retain the common fixed base,
  a nondegenerate strictly increasing right branch for each transformed map,
  and continuity of the original root maps.  These data give positive affine
  right germs; their positive iterates have identical formulas when the
  scale powers agree.  Exact-centralizer propagation then makes the iterates
  globally equal, and the common-positive-iterate theorem applies to the
  continuous roots.  Root continuity must be stated explicitly because
  continuity of a positive iterate does not imply continuity of the root.

## Orbit-circle rational bookkeeping

- Isolate one reusable statement: for a physical germ `G` commuting with the
  repelling deck germ `f`, a selected lift translation number `m/n` (`n>0`)
  forces `G^n=f^m` as a signed right germ.  Its proof contains all of the
  genuinely analytic work: Poincare supplies a lift intersection, an integer
  translate moves the finite orbit segment into the physical tail, inverse
  germ calculus handles `m<0`, and local BV Kopell kills the zero-translation
  relative germ.
- The complementary `B` identity needs no second analytic argument.  From
  the exact selected-lift product `A B=T_d` and additivity of translation
  number, `tau(B)=d-m/n=(dn-m)/n`; applying the same reusable statement gives
  `B^n=f^(dn-m)`.  The formal wrapper confirms that the original product-germ
  and `A`--`B` commutation hypotheses are used when constructing the orbit
  model, not again in this algebraic branch.
- The lift intersection must be available arbitrarily far down the physical
  tail, not merely at one unspecified point.  This localization is what puts
  the inverse-germ representatives, the relative map, and the Kopell
  comparison in one common right neighborhood.  A cleaner manuscript proof
  therefore states the power intersection for every sufficiently small
  right neighborhood and then separates: Poincare lift arithmetic, local
  `C^1` germ calculus, and one application of local `C^{1+BV}` Kopell.
- For the irrational branch, the general monotone semiconjugacy construction
  is already independent of Denjoy regularity: equal translation numbers
  produce a degree-one semiconjugacy to the corresponding rotation.  The
  precise Denjoy input is the no-wandering-interval upgrade asserting that,
  under irrationality and `C^{1+BV}` regularity, this semiconjugacy is a unit
  (a circle homeomorphism).  State that smaller core explicitly.
- Separate construction of the direct-limit line from preservation of the
  germ relations.  Once the normalized line and the three regular selected
  lifts exist, two degree-one lifts agreeing on any far-left tail agree
  globally by integer deck equivariance.  Consequently the germ identities
  `AB=BA` and `AB=f^d` immediately become exact lift identities; they do not
  belong inside the difficult direct-limit construction lemma.
- The analytic periodization used to descend a commuting germ needs `C^1`
  regularity only on an open neighborhood of one compact fundamental interval,
  not on all of `R`.  Match the endpoint values and endpoint derivatives,
  periodize the positive derivative, integrate it, and then propagate equality
  down the physical tail by the add-one identity.  Stating global `C^1`
  regularity for the preliminary raw composite is both stronger than needed
  and awkward for extensions that are only canonical near the physical germ.
- Keep the Abel-coordinate construction and the commuting-germ descent as two
  named lemmas.  The former supplies a normalized smooth direct-limit
  coordinate for the repelling germ; the latter is a local three-factor chain
  rule.  On a fundamental interval its logarithmic derivative is the sum of
  the coordinate, commuting-germ, and inverse-coordinate logarithmic
  derivatives, so bounded variation follows term by term before periodizing.
- The positivity assumption `d>0` is needed by the later orbit-circle
  dichotomy, but not by this construction-and-relation upgrade itself.  Keep
  it in the public lemma used downstream for a stable statement, while noting
  that the internal line construction works independently of `d`.

### A self-contained derivative-growth input for Kopell

- The Polterovich--Sodin ingredient needed by the local Kopell argument has
  a short compact-interval proof and need not be cited as a second black box.
  For a nonidentity increasing `C^1` diffeomorphism, choose a moved interior
  point and follow its inverse orbit.  The consecutive inverse-orbit
  intervals are disjoint and their finite length sums telescope to at most
  the ambient interval length.  Hence one interval is arbitrarily short
  relative to the original fundamental interval.  A suitable positive
  iterate maps the short interval onto the original one, so the mean-value
  theorem gives an arbitrarily large derivative.  This argument works in
  either direction of displacement and is now formalized without any
  asymptotic-series machinery.
- Organize the remaining Kopell proof as three independently visible layers:
  the preceding derivative-growth lemma; the bounded-distortion estimate for
  commuting iterates, obtained by summing variation of `log f'` over ordered
  fundamental intervals; and the endpoint limit saying the derivatives of
  each fixed iterate of the second map tend to one along the contracting
  orbit.  Their combination gives a uniform derivative bound contradicting
  derivative growth.
- The ordering direction in the distortion layer must remain explicit.  In
  the contracting orientation the successive fundamental intervals are
  listed from right to left, so their endpoint interleaving is antitone, not
  monotone.  The formal variation bridge therefore accepts either a monotone
  or an antitone interleaving; suppressing this distinction would make the
  contracting witness impossible with the orbit index fixed.

### Separate the topological and analytic halves of Denjoy

- For a monotone degree-one semiconjugacy `H F = R_alpha H`, irrationality
  alone forces `range H` to be dense.  All integral translates of the
  irrational orbit of `H(0)` have representatives in the range; deck
  equivariance lifts density from the circle back to the line.
- A monotone real map with dense range is continuous, and a continuous
  degree-one lift is surjective.  Thus neither bounded variation nor a
  distortion estimate is needed for continuity or surjectivity of `H`.
- The only analytic use of `C^{1+BV}` is injectivity.  If `H(a)=H(b)` with
  `a<b`, monotonicity makes `H` constant on the interval, and irrationality
  makes its distinct forward images disjoint modulo every integer deck
  translation.  State Denjoy's remaining core exactly as exclusion of such a
  forward wandering lift interval; this is cleaner than importing the whole
  conjugacy theorem as one black box.
- Keep irrationality in that analytic statement.  A smooth circle
  diffeomorphism with rational rotation data can have a forward-wandering
  interval converging toward an attracting periodic point, so
  `C^{1+BV}` alone does not exclude the one-sided wandering predicate used
  here.  In the application, irrationality is already supplied by the
  selected translation number and no strengthening of the main result is
  needed.
- The shrinking of a wandering interval needs no measure-theoretic circle
  packing lemma.  Fix `ε>0` and choose a rational grid finer than `ε`.  Every
  forward image of length at least `ε` contains a grid point; disjointness
  modulo deck translations makes its residue modulo the finite grid injective.
  Hence only finitely many such images exist, so their lengths tend to zero.
  This elementary argument is shorter and formalizes more cleanly than
  pushing Haar measure through projected open arcs.

## Periodic homeomorphisms of the natural extension

- Separate nonemptiness from connectedness in the Fugate--McLean input.  A
  compact connected arc-like metric space already gives a fixed point for
  every homeomorphism: interval-valued fine coordinates yield arbitrarily
  small displacement, and a minimum of the displacement function is then
  zero.  Periodicity is not used in this part.
- The genuinely deep input is only that the fixed set of a finite-order
  homeomorphism is preconnected.  That is the step requiring the invariant
  one-dimensional cover, nerve graph, and universal-covering tree.  State it
  separately so the formal proof does not attribute the elementary
  approximate-fixed-point argument to Fugate--McLean.

## Restricting substitutions to the ray alphabet

- Treat occurrence restriction as general symbolic infrastructure.  Infinite
  concatenation sends every letter in `sigma(a)` to an occurrence whenever
  `a` occurs in the input; hence the occurring alphabet of a fixed word is
  closed under `sigma`.  Restrict letter images to that subtype and use a
  coding-naturality lemma to retain the fixed-word equation.
- A prolongable nonerasing substitution strictly lengthens every successive
  seed image, so its `n`-th seed image has length at least `n+1`.  Therefore,
  if those images are the matching prefixes of the ray word, every occurring
  letter lies in some seed image and the retained seed is generating.  This
  makes the deletion of unused Markov edges explicit rather than implicit in
  the invocation of Durand--Cobham.

## Nonprimitive substitutions at the Durand boundary

- Do not infer primitivity or uniform recurrence from prolongability,
  generation, fixedness, growth, and occurrence of every source letter.  The
  substitution `a -> ab`, `b -> bb`, prolongable on `a`, has the generated
  fixed word `a b b b ...`; both letters occur and the seed images grow, but
  `b` never reaches `a`, so the substitution is not primitive and the word is
  not uniformly recurrent.
- The general Durand--Cobham reduction must therefore retain the finite
  reachability digraph.  Letters occurring only finitely often belong to a
  removable finite prefix; the recurrent tail is analyzed through terminal
  growing strongly connected components, with return-word/derived-sequence
  arguments applied only after that componentwise reduction.  Ultimate
  periodicity of the recurrent tail is then reassembled with the discarded
  prefix.
- The standalone Durand signature does not need the stronger equation
  `fixedWord 0 = seed`.  For example, with `z -> z`, `a -> azb`, and
  `b -> bb`, the generating seed is `a`, while `z` followed by the canonical
  fixed point from `a` is another all-letter fixed point and begins with `z`.
  In general, take the first position whose letter image has length greater
  than one.  Fixedness makes every earlier image the corresponding singleton,
  so that finite prefix cancels; the remaining tail is fixed and prolongable
  on its head.  The original prolongable seed occurs in this tail, and the
  new head reaches it, hence is generating.  Thus the existing hypotheses
  give an eventual canonical presentation, which is exactly the
  transient-prefix form needed for ultimate (rather than pure) periodicity.

## Return substitutions only in the aperiodic branch

- A powered return presentation cannot be requested before separating the
  periodic recurrent core.  Take the Fibonacci substitution `a -> ab`,
  `b -> a` and code both source letters to one target letter.  The target and
  its recurrent core are constant, while the source growth is the golden
  ratio.  Every nonempty marker in the constant word has only the one-letter
  return word, so injectivity forces the return alphabet to have rank one.
  Its substitution growth is then an integer image length, whereas no
  positive power of the golden ratio is an integer.  Thus the unqualified
  powered-return boundary is false even though the presentation has a good
  primitive power and the core is linearly recurrent.
- First branch on periodicity of the recurrent core.  A periodic core gives a
  periodic recurrent language through `RecurrentCore.same_language`, and
  syndeticity then gives ultimate periodicity of the original word.  Only in
  the complementary branch should the nested-prefix return refinement and
  powered return substitution be constructed.  This adds an aperiodicity
  hypothesis to the two return-construction lemmas but does not change the
  public Durand--Cobham theorem.

## Primitive-core extraction is not an image-closed SCC restriction

- The original `HasGoodPower` reduction is false even for an aperiodic,
  uniformly recurrent fixed point.  On `{a,b,z}`, take
  `a -> a z b`, `b -> a`, and `z -> z`, with seed `a` and identity coding.
  Its fixed point is the Fibonacci fixed word with `z` inserted between
  consecutive Fibonacci letters, so it is aperiodic and uniformly recurrent
  and its dominant growth is the golden ratio.  Nevertheless `{a,b}` is not
  image-closed because the image of `a` emits `z`; `{z}` has growth one; the
  whole alphabet is not primitive because `z` never reaches `a` or `b`; and
  the iterates of `z` do not grow.  Thus no positive power satisfies the old
  certificate, while the claimed periodic alternative is also false.
- The recurrent reduction must instead construct a fresh primitive
  presentation, normally on a return-word alphabet.  Its certificate records
  the primitive substitution and fixed derived word, a coding onto a word
  whose language is the recurrent language of the original output, and the
  exact powered dominant rate inherited from the original presentation.  The
  SCC graph may be used internally while constructing this presentation, but
  an image-closed SCC of the original alphabet is not the theorem's output.

## Localize the two primitive-core reductions correctly

- Durand's Lemma 13 only says that, for a *growing* substitutive
  presentation whose recurrent factors have bounded gaps, the recurrent
  language is the language of some primitive substitutive word.  Its output
  does not identify the primitive substitution's dominant eigenvalue with a
  power of the growth in the original presentation.  Consequently the Lean
  certificate for Lemma 13 must contain only the recurrent core, primitive
  substitution, fixed point, and coding data; no powered spectral field
  belongs there.
- Powered-growth compatibility is obtained later in Durand's proof.  Theorem
  5 and Corollary 6 first replace the presentation by a non-erasing one while
  preserving an exact positive power of the original dominant rate.  After
  the standard power reduction, Lemma 15 says that either all relevant
  letters have the same growth rate or the output is ultimately periodic.
  In the aperiodic branch this makes the reduced substitution "good", and
  only then may one restrict to a primitive component at the displayed
  dominant growth.
- The corrected formal dependency order is therefore: non-erasing/power
  reduction and Lemma 15's periodic alternative; Lemma 13's primitive
  recurrent-language core on the growing branch; good-substitution spectral
  upgrade; spectral assembly.  The public Durand--Cobham statement is
  unchanged.  The earlier plan incorrectly localized all four steps in a
  single return-alphabet construction boundary.

## Never use `Set.ncard` as the size of a potentially infinite fibre

- In mathlib, `Set.ncard` is defined to be zero on infinite sets.  Consequently,
  a lower bound such as `2 ^ k <= fibre.ncard` is not a valid generic statement
  for a continuous horseshoe: the full fibre may be infinite even though the
  horseshoe supplies many distinct inverse branches.
- State the symbolic horseshoe conclusion by constructing an explicit finite
  set (preferably a `Finset`) of exactly `2 ^ k` distinct preimages.  Only after
  separately proving that the ambient iterate fibre is finite may this be
  compared with the fibre's `ncard`.  This keeps all cardinal arguments valid
  without strengthening the public dynamical hypotheses.
- The same issue occurs earlier in the lap-limit bounds.  The original
  `parryLapLimit_bounds` skeleton used `ncard` estimates for
  `parryCutSet T n` without carrying finiteness; if a cut set were infinite,
  mathlib would make its `ncard` zero and the displayed bound would be
  vacuous or false.  The corrected lemma explicitly assumes
  `∀ n, (parryCutSet T n).Finite`, and every caller supplies this from
  `parryCutSet_finite` before doing any cardinal arithmetic.

## Do not spectrally “upgrade” an arbitrary primitive language model

- Equality of languages does not identify the substitution presentations of
  two points in the same minimal subshift.  In particular, a certificate that
  some primitive fixed point has the recurrent language of `x` cannot simply
  be augmented with the dominant eigenvalue of an unrelated good component.
  The former skeleton
  `durand_goodSubstitution_growthUpgrade reduced languageCore` erased the
  syndeticity and intertwining data needed for this step and was therefore
  stronger than the construction in Durand's proof.
- The corrected interface must construct the compatible primitive core and
  its powered spectral data together (or retain an explicit return-word
  intertwining from the reduced presentation).  If a component fixed point is
  used, the bounded-gap hypothesis must remain available to prove that its
  language is the whole recurrent language.  Spectral compatibility then
  comes from the same component/return construction, not from language
  equality alone.

## A return-presentation certificate must retain primitivity

- Prolongability on a generating letter, occurrence of every source letter,
  and unbounded growth of the seed do not imply that the substitution is
  primitive.  Fixed spacer letters give uniformly recurrent aperiodic
  counterexamples: a growing primitive skeleton can insert a fixed spacer at
  every scale, while that spacer never reaches the growing letters.
- In the nested-marker construction, primitivity follows from choosing the
  later marker so that every earlier return block occurs in every later
  return block.  This fact must be stored explicitly in both the refinement
  certificate and the resulting powered return presentation; downstream
  eigenvalue comparison must consume that field rather than infer it from
  weaker occurrence data.

## Make the one-sided Abel-coordinate construction explicit

- The manuscript should not appeal only to a generic “smooth fundamental
  coordinate.”  On a segment `[a,f(a)]`, choose a strictly increasing
  quadratic seed whose endpoint values are `0,1` and whose endpoint
  derivatives satisfy the exact seam equation
  `psi'(f(a)) * f'(a) = psi'(a)`.  This is precisely what makes the
  dynamically glued coordinate `CÂ¹` across every arrival seam.
- Define the arrival time pointwise as the least iterate entering
  `[a,f(a))`; no uniform arrival bound near the fixed endpoint exists or is
  needed.  Finite arrival follows by taking the monotone limit of a
  hypothetical non-arriving orbit and using positivity of the germ to rule
  out the resulting interior fixed point.
- The logarithmic-derivative BV proof is cleanest as an induction on arrival
  time.  On one pullback interval the cocycle is
  `log Phi' = (log Phi') ∘ f + log f'`; bounded variation then follows from
  monotone pullback, addition, and the germ's BV hypothesis.  Intervals that
  cross `a` are split there and recombined by additivity of variation.
- Surjectivity of the coordinate onto `(-∞,1)` should be stated and proved,
  rather than folded into “standard Abel coordinates.”  Iterating the inverse
  fundamental-segment order isomorphism gives points with coordinates
  `-n`; the intermediate value theorem and the seed segment then fill every
  value below `1`.
- No separate inverse-regularity assumption is required.  The order inverse
  is locally the inverse supplied by the `CÂ¹` inverse-function theorem, its
  derivative is `1 / Phi'`, and
  `log (Phi^{-1})' = -(log Phi') ∘ Phi^{-1}`.  Thus positivity and compact BV
  of the inverse follow directly from the already proved coordinate facts.

## Induce the powered return substitution directly

- Once the primitive recurrent presentation has injective coding and an
  exact positive letter metric, no repeated-derived-sequence pigeonhole is
  needed merely to construct its powered return substitution.  Parse the
  source fixed word into return blocks for its one-letter head marker.
  Substitution carries every return cut to another marker occurrence, so the
  image of each return block has a unique factorization into return blocks.
  These factorizations define a substitution which fixes the derived word.
- Give a return letter the metric length of its decoded return block.  The
  decoding identity makes this metric scale by exactly the same powered
  eigenvalue as the source substitution.  Positivity and scale greater than
  one give unbounded images of every return letter.  Uniform recurrence of
  the derived word then proves primitivity directly: choose a common bounded
  gap for all singleton letters and a common depth at which every image is
  longer than that gap.
- The earlier `ReturnRefinement` plan with two synchronized markers was
  unnecessary for this construction and obscured the actual dependencies.
  Nested markers remain relevant to the independent-scale comparison, but
  not to existence of a powered return presentation.

## Higher-block syndeticity needs the right ambient invariant

- The full higher-block alphabet contains blocks which never occur in the
  fixed word.  It therefore cannot satisfy an `every_letter_occurs` field.
  The intermediate higher-block presentation used in the syndeticity proof
  must retain only fixedness and the positive exact metric (plus the
  distinguished occurring block); occurrence/generation is asserted only
  for states actually selected from the fixed word.
- Replacing a word marker by its set of occurring letters is invalid: equal
  letter supports do not remember order, and a marker can be created across
  every tile boundary even when no individual tile contains it.  A finite
  prefix/suffix signature repairs this only by recreating the higher-block
  construction.  The manuscript should use the higher-block argument
  explicitly and avoid the false support-only shortcut.

## Exact Parry uniqueness is genuinely a BV spectral step

- Exactness makes the backward orbit of a lap endpoint dense, and conformal
  measures are atomless and satisfy iterated conformality on injectivity
  cylinders.  These facts reduce measure equality to equality of cumulative
  masses on backward endpoints, but they do not by themselves determine
  those masses through a finite triangular system: the forward critical
  orbit need not be finite.
- Do not silently assume postcritical finiteness or positive expansivity.
  Shultz's exact-case uniqueness uses uniform convergence of the normalized
  Perron operator on bounded-variation functions.  The revised manuscript
  should state that BV convergence input explicitly before deducing
  uniqueness of the scaled probability.

## Stronger piecewise-monotone reduction: formal-proof corrections

- The Bogatyi--Frolkina and Alsedà--Misiurewicz results are not available in
  mathlib 4.30.  In a no-axiom formalization they cannot remain citation-only
  transitions.  The Lean proof should consume a direct finite covering/lap
  growth certificate from the Bogatyi--Frolkina point configuration, avoiding
  any unnecessary dependence on a particular normalization of topological
  entropy.  The constant-slope step should then be proved either by extending
  the existing lap-resolvent construction to weak monotonicity and a
  non-strict coordinate, or by fully formalizing the compatible
  semiconjugacy theorem.
- The manuscript's compact-slice argument needs an explicit topology.  The
  expanding eigenspace is first shown algebraically finite-dimensional; one
  must then use the inherited variation norm or transport a Euclidean norm
  through a basis before saying that evaluations and normalized transfer are
  continuous and that closed bounded subsets are compact.
- Mathlib 4.30 has no ready Brouwer/Schauder fixed-point theorem in the needed
  form.  The proof-aligned revision should isolate the precise
  finite-dimensional positive-cone fixed-point lemma actually used.  Lean may
  prove that specialized lemma directly or replace it with a positive
  resolvent/Perron construction; the manuscript should follow the cheaper
  kernel route rather than cite an invisible generic fixed-point step.
- The formula `E ↦ sigma(u(E))` for a branch with plateaus is valid for a
  finite atomless signed measure, but it is neither the ordinary pushforward
  nor a stock measure comap.  Its proof must remove the countable set of
  multi-fibre values: images of disjoint source sets are disjoint off that
  set, and atomlessness makes the discarded overlap null.  Endpoint
  assignments in branch partitions must be treated by the same null-set
  argument.
- The existing Lean theorem for definable piecewise-C1 maps does not by itself
  expose the manuscript's piecewise-linear core.  It accepts a supplied
  abstract `OMinimalExpansion`, and the project currently constructs no
  concrete expansion.  The PL core must therefore be factored as a theorem
  independent of that parameter; inserting a nonemptiness assumption would
  weaken the stronger theorem.

- The earlier plan retained Parry--Shultz existence after exactness while
  omitting exact uniqueness.  A cleaner candidate now supersedes that plan:
  topological exactness of `R=(PQ)^L` gives two separated full branches for
  some iterate `R^N`.  Apply the already formalized weak-lap resolvent to
  `R^N=(P^{LN})(Q^{LN})`, then use the generic positive-exponent joint
  eigenspace and exact variation.  Once the exactness-to-iterate-horseshoe
  bridge is kernel-checked, the revised manuscript should omit both Parry
  existence and Parry uniqueness from this stage.
- That bridge is now kernel-checked with only continuity and exactness.  Use two
  fixed separated source intervals `(1/5,2/5)` and `(3/5,4/5)`.  Exactness
  gives positive onto-image times for both; exactness also gives surjectivity of
  the map, so applying the remaining iterate equalizes the two times at their
  sum.  Preimages of the two ambient endpoints in each open interval, ordered
  and closed up, give two strictly separated full branches by IVT.  This proof
  needs neither finite-piece hypotheses nor transitivity/Parry machinery.
- Consequently the PL chapter should use the generic weak-lap resolvent on the
  exact product iterate and omit both Parry--Shultz existence and uniqueness,
  not merely describe this as a possible alternative.

### Replace the normalized-transfer Brouwer step by complex variation

- Work in the finite-dimensional **complex** space of atomless finite
  measures satisfying `T_H z = lambda z`. It is nonzero because the initial
  positive conformal probability embeds into it.
- The commuting branch transfers restrict to complex-linear endomorphisms
  `A,B` with `AB = BA = lambda id`. Algebraic closedness of the complex
  numbers gives a nonzero eigenvector `Az = cz`; the product identity gives
  `c != 0` and `Bz = (lambda/c)z`.
- For an atomless complex measure, branch transfer commutes **exactly** with
  total variation. The proof deletes the countable set of plateau values,
  uses injectivity on the remainder, and uses disjoint assigned source laps
  for exact variation additivity across branches.
- Consequently `|z|` is a nonzero atomless positive simultaneous
  eigenmeasure, with eigenvalues `|c|` and `lambda/|c|`. Normalizing `|z|`
  gives the required probability and the product of the two positive slopes
  is `lambda > 1`.
- This is cleaner than the manuscript's positive slice: it removes the
  inherited-topology, compactness, normalized-map continuity, and Brouwer
  obligations. A mere inequality for variation would not suffice; the
  manuscript should state and prove exact naturality.
- Across finitely many branches, "supported on `D`" must mean that **every
  measurable subset disjoint from `D` has zero vector mass**. Vanishing only
  on the whole complement permits cancellation and is too weak for exact
  variation additivity. The Lean proof restricts the total sum to each
  pairwise-disjoint assigned source cell and then applies variation of
  restriction.
- Finiteness of the total variation of a complex measure is proved through
  the Jordan total variations of its real and imaginary signed parts. It
  should not be silently inferred from a scalar-generic vector-measure
  interface, where total variation need not be finite in that generality.
- A finite weak monotonicity partition already proves global Borel
  measurability: each monotone/antitone restriction is measurable on its
  closed interval cell, and the finitely many measurable cells cover the
  domain. Record this gluing lemma explicitly before invoking global transfer
  naturality.

### Remove superseded first-proof infrastructure

- The stronger manuscript and its Lean import graph should contain no
  `OMinimalExpansion`, definability hypothesis, or general tame-`C^1` layer.
  The inputs after quotient descent are finite piecewise-linear maps, so every
  regularity fact needed by the core should be stated and proved directly for
  that class.
- Reuse an earlier declaration only when its statement and proof are genuinely
  elementary and shorten the PL-only dependency path. Do not reproduce the
  earlier architecture merely for continuity with the old draft.
- Legacy Parry, substitution, Fugate--McLean, and analytic holes are obligations
  for the stronger theorem only if the final minimal PL-core dependency graph
  still reaches them. Otherwise record them as intentionally pruned, and keep
  them outside the stronger root module.
- The single visible Fugate--McLean hole understates its present formalization
  cost.  The algebraic finite-poset nerve and relative Smith chain machinery
  are proved, but the scratch proof still lacks the coherent invariant-cover
  tower produced from arc-likeness and disconnectedness of the fixed set.
  Until that construction is closed, the revised manuscript should not call
  the result an already internal theorem.  The formal proof will either supply
  that tower or replace the citation by a smaller interval/finite-piece lemma
  at the sole rational-branch call site.
- The bounded route audit initially favored a call-site replacement, but the
  completed finite-component audit rules that route out.  The exact canonical
  reduction is available: collapse every nondegenerate fixed component of the
  positive word, descend both factors, retain the finite set of singleton
  fixed components, and lift any quotient common fixed point.  After these
  existing steps, however, the sole new lemma is still common fixedness from
  the *global* equal-positive-powers equation.  That lemma is equivalent to
  the original boundary rather than a finite combinatorial subproblem.
- In particular, arbitrary component actions cannot replace the ambient
  theorem.  On four ordered singleton components the commuting permutations
  `(12)` and `(34)` have equal squares and no common fixed component, and each
  individually extends by linear interpolation to a continuous PL interval
  map.  More elaborate crossing data still do not encode equality on every
  complementary gap.  The revised manuscript must not present the quotient
  reduction as if it solved this final ambient step.
  The selected-gap specialization was tested and rejected: finite arrival
  forces every common-return-invariant interval containing `[p,c]` to be the
  whole ambient interval, while the stated data do not force a different
  nondegenerate component of `Fix(A^[m]) = Fix(B^[n])`, much less one with both
  endpoints fixed by `S`.  A disjunction merely postulating such a component
  hides the original theorem and must not appear in the manuscript.  Use the
  generic finite-piece route next, retaining the ambient-extension constraint.
  That route has now been shown insufficient as a decomposition, so the
  formalization returns to the coherent Smith/nerve tower and expands its
  topological construction into explicit tracked lemmas.

### Use the stronger quotient interface, not an arbitrary-PL black box

- The quotient maps are already onto and live in a common coordinate in which
  every nondegenerate branch has slope `±C` or `±D`, with `C,D > 0` and
  `CD > 1`. The branch scaling argument also collapses every plateau, and a
  common invariant quotient interval pulls back to the original minimal core.
- A specialized constant-slope shortcut was investigated and rejected: the
  later disconnected-phase and fixed-component quotients do not preserve that
  coordinate. The proof must therefore retain an unconditional arbitrary-PL
  core, while keeping its dependency path PL-specific.
- The arbitrary-PL phase and fixed-component quotients are still necessary and
  still destroy the initial constant-slope coordinate.  What changes is only
  the restoration mechanism: after those quotients and the ray argument make
  the returned product exact, an iterate horseshoe plus the weak-lap resolvent
  can reconstruct the common measure without Parry--Shultz.  The proof should
  still say explicitly that it temporarily forgets the stronger coordinate,
  performs the necessary PL quotients, and restores a common coordinate only
  after exactness.
- In the quotient proof, do not cite global injective-set scaling for a whole
  weak monotonicity cell: a cell may contain plateau intervals.  Localize the
  transfer eigenidentity to the **assigned** source cell instead.  The other
  branch summands vanish by disjointness, so every measurable subset of that
  cell has the required image-scaling identity even when the branch is only
  weakly monotone.  Closed-cell endpoint variants then follow from
  atomlessness.  This is also the correct justification for collapsing
  plateaus and for the affine slope computation; the draft's phrase "by the
  single-lap scaling identity" should point to this lemma explicitly.
- Present the final normalization under contradiction. Starting from a
  hypothetical counterexample, pass to the affinely rescaled minimal core and
  derive `False` there; no separate theorem transporting a fixed point back
  through the rescaling is needed. Downstairs the PL theorem gives a common
  fixed coordinate, its fibre is a common invariant closed interval upstairs,
  and minimality makes that fibre all of `[0,1]`. The contradiction is simply
  that the CDF sends the two ambient endpoints to `0` and `1` while the whole
  interval lies in one fibre.

### Markov/postvertex clean-port clarifications

- Topological exactness already forces an interval self-map onto: choose a
  proper nonempty open set whose exact hitting time cannot be zero, then peel
  off the final iterate.  State this once rather than carrying a separate onto
  hypothesis through every postvertex lemma.
- In the vertex-value formula for a composition, the reverse inclusion at an
  inner vertex uses onto-ness of the inner map.  The endpoint reverse
  inclusion is different and needs explicit one-sided germ analysis; it
  should not be hidden under the interior argument.
- Constant-absolute-slope composition is cleanest on the already formalized
  `MonotonicityPartition.compositionRefinement`: on each refined cell the two
  affine formulas compose directly and the absolute slopes multiply.  This
  is substantially shorter than rebuilding a polygonal vertex partition.
- The resulting finite postvertex sets and common invariant Markov hull need
  only PL germs, exactness, finite-piece constant slopes, and elementary orbit
  rectangles.  They do not require the old Polygonal/Normalization import
  layer.

### Small measure-theoretic statement cleanups

- Mathlib's `ProbabilityTheory.cdf` is syntactically defined for an arbitrary
  real measure, but its identification with cumulative mass requires an
  `IsProbabilityMeasure` instance.  Therefore even the left-endpoint CDF lemma
  must receive the probability hypothesis in addition to atomlessness; do not
  infer that hypothesis from the codomain bound built into `cdf`.
- Borel measurability of a monotone-branch image needs a Borel domain and a
  monotone/antitone restriction; continuity is not needed for the mathlib
  Lusin--Souslin lemma used by Lean.
- The Stieltjes `Icc` increment formula remains valid without an explicit
  `a ≤ b` hypothesis: the reversed interval is empty and `ENNReal.ofReal`
  handles the corresponding nonpositive increment.
- Nonnegativity of `lambda` is not needed for the interval-to-Borel uniqueness
  step once scaling is expressed using `ENNReal.ofReal lambda`; it is needed
  later when converting that equality to a real signed-measure eigenidentity.

### Replace strict-turn counts by intrinsic weak-lap counts

- The old `genuineTurns` cut set is not a valid lap counter for the strengthened
  weakly monotone class: an increase--plateau--decrease profile can fail the
  strict-turn predicate at both plateau endpoints. Define the localized count
  as the minimum size of a finite subdivision into closed weakly monotone
  cells instead.
- Adjacent subdivision counts and one-branch shifts are not literally exact;
  their integer defects have absolute value at most one. After summing the
  resolvent and dividing by the divergent total series, these bounded errors
  vanish. State that mechanism rather than importing strict-lap equalities.
- In the proved one-branch estimate, isolate the constant endpoint branch:
  its local count is one while the corresponding open-side count is zero.
  For a nonconstant weakly monotone or antitone branch, factor through its
  image interval and push/pull a minimal subdivision; this gives exact equality
  before the single endpoint correction. This is clearer than treating a
  plateau as a degenerate strict branch.
- A weak branch may have an infinite fibre. For the horseshoe lower bound,
  choose the target in the open horseshoe hull outside the countable union of
  plateau values of **all iterates**. Its iterate fibres are then finite, and
  each minimal weak lap contains at most one selected fibre point.
- Countability of the intrinsic plateau-value set does not require piecewise
  monotonicity (or even continuity): choose one nondegenerate constant open
  interval for each value. Intervals belonging to distinct values are
  disjoint, and a separable interval cannot contain uncountably many disjoint
  nonempty open sets. State this as a standalone order-topological lemma.
- For the regular-fibre estimate, use the closed cells of an attained minimal
  weak-lap subdivision directly. Equality at two distinct points of one weak
  lap forces the map to be constant between them, contradicting regularity.
  The closed cells can overlap at their endpoints, so use the finite-union
  cardinality inequality rather than claiming they form a disjoint partition.
- The small-interval estimate needs a genuine prefix itinerary cell: every
  first `m` image hull must stay inside one weak branch. Merely assuming that
  the final iterate is weakly monotone is false as a replacement, because an
  earlier fold can be erased by a later constant branch.
- The dense-endpoint diagonal argument also needs nonvacuous two-sided
  itinerary neighborhoods (`a<x` and `x<b` away from ambient endpoints). The
  weaker existential statement allowing `a=x=b` says nothing about
  equicontinuity. Record the strict one-sided clauses explicitly.
- Package the diagonal limit before extracting coordinates. The formal proof
  first obtains one cumulative limit on the dense sample set, proves its
  bounds, adjacency, branch scaling, and two-sided smallness there, and only
  then extends it to a global coordinate. When a weak branch image degenerates
  to a point, the scaling equation is the diagonal-value case, not an
  application of an inverse strict branch. This ordering removes the apparent
  circularity between existence of the coordinate and its scaling law.

### Retain the branching data in the BF replacement

- The Bogatyi--Frolkina proof uses De Marr to obtain, after reflection, an
  alternating configuration `x0 < s < x1 < t`. The decisive relation is
  `Q(x0) ≥ x1` (not the reverse inequality), together with `Q(x1) ≤ x0`,
  `P(x0)=x0`, `P(s)=t`, `P(x1)=x1`, `Q(s)=s`, and `Q(t)=t`.
- With the corrected relation, both `[s,x1]` and `[x1,t]` cover `[x0,t]`
  under `H=P∘Q`. After a continuity/no-common-fixed-point trimming argument,
  `H` itself has two strictly separated covering branches. The manuscript
  should present this direct IVT proof and omit the unnecessary generic
  covering-graph/return-path discussion.
- Select the De Marr pair by minimizing the real gap on compact *weak*-sign
  fixed-point sets. The absence of a common fixed point then upgrades both
  weak signs to strict signs. This is the closed-set formulation actually used
  in Lean and avoids pretending that the strict-sign sets are compact.
- State both forward and backward configurations. A silent "after reflection"
  suppresses hypotheses and makes the endpoint-trimming argument harder to
  audit; the two Lean cases are short and symmetric.
- In the forward trimming case, the no-common-fixed-point hypothesis is used
  exactly to rule out `(P ∘ Q)(t)=t`; in the backward case it rules out the
  reflected endpoint equality. The remaining strict margins are four direct
  IVT selections.
- The printed BF incidence matrix is
  `[[2,2,1],[1,1,1],[1,1,2]]` (Perron value `4`), but neither the matrix nor
  its entropy estimate is consumed by the stronger proof. The kernel-checked
  Lean theorem already obtains the binary horseshoe at the first composite
  (`N=1`).

## Plateau-value countability is more general than needed

The formal proof of `intrinsicPlateauValues_countable` does not use finite
piecewise monotonicity.  For an arbitrary continuous interval map, distinct
values that are constant on nondegenerate intervals give pairwise-disjoint
nonempty open intervals, so there can be only countably many of them.  The
revised manuscript should state this as a standalone elementary observation
and invoke it for the iterates, instead of tying countability to a chosen
finite monotonicity partition.

## Use a finite-depth resolvent split, not accumulated branch errors

For the two-sided itinerary-cell estimate, split the local Abel resolvent at a
fixed depth `m`. Every prefix through depth `m` stays inside one genuine weak
itinerary cell and therefore has intrinsic weak-lap count exactly one. The
remaining shifted tail is bounded by `t^m` times the total resolvent. After
normalization this gives the direct bound `m / D(t) + t^m`, which tends to the
required small value by first choosing `m` and then taking `t → 1⁻`. Iterating
the adjacent-branch error estimate is both weaker and needlessly introduces a
geometric constant-branch factor; the revised manuscript should use the
finite-depth split.

## Fibre respect from closed-cell scaling

The transfer partition uses half-open assigned cells, whereas the geometric
quotient works with closed partition cells.  To pass between them, remove the
single possibly unassigned right endpoint; atomlessness makes both that source
singleton and its image null.  This gives the closed-cell scaling law without
silently identifying the two endpoint conventions.

The closed-cell image step must retain the continuity hypothesis on the
interval map. Weak monotonicity alone does not imply that the image of a closed
interval is the closed interval spanned by its endpoint images. In the formal
proof, continuity and weak monotonicity first identify that image interval;
coordinate scaling then gives its Stieltjes mass, and only afterward are the
half-open assigned cell and closed cell compared modulo the null right endpoint
and its null image. Thus the manuscript should state continuity explicitly at
this bridge rather than treating a bare monotonicity partition as sufficient.

For global CDF-fibre respect, cover the source interval between two equal-CDF
points by its finitely many closed monotonicity subcells.  Each subcell image
has measure zero by the local scaling law, hence so does their finite union;
continuity and IVT put the whole interval between the two image values inside
that union.  This is the clean plateau-safe proof that both original maps are
constant modulo CDF fibres.

## Coordinate-image cells and the PL quotient

- Define the quotient partition by applying the distribution coordinate to
  the finite source vertex set and removing duplicate values. The removal of
  duplicates is essential because plateaus can send several consecutive
  source vertices to the same quotient vertex.
- State explicitly the source-cell lemma used by the affine argument: if
  `a < b` are consecutive distinct coordinate-images of source vertices, then
  some adjacent source vertices `c < d` satisfy `theta(c) = a` and
  `theta(d) = b`. A clean proof chooses a preimage of `(a+b)/2`; the source
  cell containing that preimage must have endpoint images `a,b`, by
  monotonicity and adjacency of both vertex sets.
- On that source cell, apply closed-cell transfer scaling to `[c,u]`.
  The increasing orientation gives
  `theta(T(u))-theta(T(c)) = scale*(theta(u)-theta(c))`; the decreasing
  orientation gives the reversed target difference. Intertwining then makes
  the quotient factor affine with slope respectively `scale` or `-scale`.
  This proof needs neither strict source monotonicity nor full support.
- Plateau collapse is most direct at the transfer equation itself. If `T` is
  constant on `[x,y]`, every branch image of its intersection with `[x,y]`
  is contained in one null singleton. The positive transfer eigenvalue then
  forces the whole source interval to have zero measure, so its distribution
  coordinate is constant.
- For a fixed quotient point `y`, construct the upstairs fibre interval from
  the minimum and maximum of the nonempty compact closed fibre
  `{x | theta(x)=y}`. Monotonicity identifies the whole interval between
  those extrema with the fibre, and the intertwining identities make it
  forward invariant under both original maps.

## Arc-like approximation does not encode connectedness

The formal predicate `IsArcLike` records only the arbitrarily fine
interval-valued fibre-cover property.  Taken by itself it also holds for finite
discrete spaces, so connectedness cannot be silently recovered from that
predicate.  The coherent Smith/nerve constructor must explicitly receive the
available `ConnectedSpace` hypothesis.  A four-point discrete periodic action
with two fixed points is a direct counterexample to the version that omitted
it.  The revised manuscript should continue to say “compact connected
arc-like metric space” whenever the periodic fixed-continuum theorem is used.

## The Smith coefficient prime is a theorem hypothesis

The relative Smith/H0 witness is taken over `ZMod p`, so the prime-order step
must carry `Nat.Prime p` explicitly through the tower and non-boundary
statements. Allowing `p = 1` collapses the coefficient ring and makes the two
separated endpoint classes equal, invalidating the witness. The revised proof
should state the prime-order theorem first, use the finite prime-factor
induction separately, and never describe the coefficient as an arbitrary
positive modulus.

The formal skeleton also separates four logically distinct constructions that
the prose should not compress into one "choose a sufficiently fine invariant
cover" sentence: ordinary arc-like pro-zero refinement, cyclic saturation to a
common refinement, equivariant selector construction, and finite coherent
tower assembly. Fixed-set separation/displacement supplies the colouring and
persistent H0 witness only after that ambient tower is available.

The Smith chase does not consume an abstract equality for every composite map
between arbitrary levels.  It uses reflexivity and the bottom-prefix recursion
`map 0 (k+1) = map 0 k ∘ map k (k+1)`.  Stating exactly this coherence avoids
irrelevant dependent transports between the varying cover-index types while
retaining every identity used in the proof.  The finite cover chain still
stores each adjacent equivariant refinement, and its bottom-to-level maps are
their literal recursive composites.  The manuscript should present that
recursive construction instead of claiming a larger categorical tower API.

The displacement neighborhoods must have **disjoint closures**, not merely be
disjoint open sets. If two open neighborhoods have touching closures, a cover
element around a common boundary point can meet both sides no matter how small
its mesh is, so the nerve colouring used by the fixed-H0 witness is unjustified.
In the metric proof, first shrink the normal-separation neighborhoods so their
closures are disjoint, then take the finite intersections over the cyclic
orbit. The invariant cores retain disjoint closures and the compact complement
has a positive minimum displacement.

## The Markov substitution package must retain geometric provenance

The first PL-core skeleton for the irrational branch was under-specified.
`PiecewiseLinearEdgeSubstitutionData` recorded only two substitutions and a
common fixed infinite word.  It did not say that the substitutions were read
from the two Markov maps, that positive edge lengths scale by the two returned
slopes, that the occurring alphabet is complete/generating, or that the word
actually realizes the interval path.  The later syndeticity, periodic-language,
and return-path statements are therefore false for an arbitrary inhabitant of
that structure: identity substitutions fix every infinite word, including
words whose recurrent letters have unbounded gaps, while the separately
stored growth numbers impose no condition on those substitutions.

The revised formal package must carry the provenance through every boundary:

- a finite occurring directed-edge alphabet and its geometric realization;
- the two substitutions induced by the returned maps and their common fixed
  edge itinerary;
- a positive edge-length metric with exact scaling by the two returned
  slopes, together with the occurrence/generation data needed by the
  Durand--Rigo theorem;
- explicit decoding/semiconjugacy equations from substituted edge words to
  interval paths.

Only after those fields are present may the two Durand boundaries be invoked,
and ultimate periodicity may be converted into a periodic return path using
the stored realization equations.  This is a genuine hypothesis correction,
not a stylistic change to the frozen skeleton.

## Boundary 7 scale recovery is reparametrization-invariant

The common CDF construction determines the constant absolute slopes of the two
conjugate models, but it cannot identify their `L`th powers literally with the
numbers stored in `PiecewiseLinearIrrationalExactSystem`.  That earlier
structure retains only a topological parametrization of its ray.  Composing
the ray with the increasing homeomorphism
`t ↦ sign(t) * |t|^c` preserves continuity, surjectivity, dense tails, and both
ray actions while replacing both recorded dilation scales by a common positive
power.  The CDF-model slopes do not change.  This gives a direct countermodel
to the originally frozen literal equalities.

The invariant conclusion—and the only one consumed later—is that the model
slopes are greater than one and that their returned powers are
multiplicatively independent.  The retained ray fields are deliberately too
weak to prove that independence: they provide no local injectivity or
normalized coordinate near the base point.  Instead the formal proof uses the
orientation-preserving right `C1+BV` germs of the two returned source maps.
The increasing CDF coordinate transports these to positive affine germs of
slopes `scaleP^L` and `scaleQ^L`.  A hypothetical equality between positive
powers of those slopes therefore gives equality of positive iterates on a
right neighborhood.  The prepared system's local-eventual-onto property for
the commuting return map globalizes this equality directly: every point is a
common return iterate of a point in that neighborhood, so commutation moves
the local equality to the whole interval.  This yields the forbidden common
positive iterate and contradicts `E.no_positive_iterate`.  Thus no
normalization exponent is chosen
and neither individual ray scale is treated as canonical.  A ray-based proof
would require extra local-injectivity and coordinate-normalization hypotheses
that are intentionally absent from the theorem.  Boundary 7's final data
structure already asks only for the expansion/independence conclusion, so the
repair remains local to the scale-recovery lemmas.

The kernel audit matters here: the first Lean version of this otherwise
correct scale argument still called an obsolete admitted globalizer, so local
type checking hid a transitive `sorryAx`.  The proof-aligned presentation
should state the short direct local-eventual-onto globalization above and not
route this step through the broader historical orbit-circle theorem.

## Boundary 9 audit: exact coding makes the substitutions primitive

The stronger PL manuscript already has the right geometric idea—rebuild the
unit-speed ray after passing to the common constant-slope coordinate—but the
Lean interfaces must distinguish three different scale pairs.  The ray in
`PiecewiseLinearIrrationalExactSystem` carries the earlier orbit-chart scales
`E.scaleA,E.scaleB`; `PiecewiseLinearConstantSlopeSystem` later produces the
Parry-coordinate slopes `M.scaleP,M.scaleQ`; and the returned maps use
`M.scaleP^G.L,M.scaleQ^G.L`.  No field presently identifies the first pair
with either later pair, and such an equality should not be silently assumed.
The Boundary 9 ray must therefore be rebuilt with explicit scale fields and
equalities to the **returned** slopes, exactly as in the manuscript's formula
for `Psi` from the positive germ of `R`.

`ModelsDirectedEdgeSubstitution` is also weaker than its prose description:
its Lean definition says only that a nonempty literal word is a connected
edge path starting at `T(e.source)` and ending at `T(e.target)`.  It does not
say that the word records every intermediate crossing of the actual map on
the source edge.  Consequently topological exactness plus this endpoint-only
predicate does not imply primitivity.  The minimal downstream-safe decoder is:

- for every `n` and every occurring source and target directed edge, if
  `T^n` makes that oriented target crossing inside the oriented source edge,
  then the target letter occurs in `sigma^n(source)`.

A pointwise parametrized realization of each whole edge image is a natural
stronger construction field from which this powered decoder should be proved.
The powered decoder itself is the minimal property consumed later, so it is
worth exposing as a named adapter rather than repeatedly unpacking the
parametrization.

With that correction, exactness does make each induced substitution primitive
on the occurring directed-edge alphabet.  Split the interior of each source
edge into two ordered nonempty open intervals.  Exactness sends each interval
onto the whole unit interval after some iterate; onto-ness lets one pad the
two hitting times to a common time.  Choosing endpoint preimages in the two
ordered intervals realizes either orientation of every target edge.  A finite
maximum over source edges gives one positive depth at which every target
letter occurs in every source image.  Decoder completeness turns this uniform
crossing depth directly into the usual primitive-substitution certificate.

This removes the general Durand--Rigo syndeticity boundary from the PL proof.
The already checked theorem
`Symbolic.Substitution.primitive_fixedPoint_hasLinearFactorGaps` gives linear
factor gaps for the common fixed word, hence uniform recurrence and syndetic
recurrent factors.  It does **not** remove the full Cobham argument: the
primitive two-scale return-word comparison that forces a periodic recurrent
language remains the one honest symbolic boundary.  Positive edge lengths,
exact image-length scaling, growing seed images, and the explicit returned
scale equalities are precisely the growth data needed to extract independent
Perron powers before that comparison.

The separately compiling audit skeleton is
`CommutingInterval/PiecewiseLinearB9Scratch.lean`.  After closing X1 and C0
and replacing the defective constant-family interface by the enriched return
tower, it has exactly fifteen top-level leaves in the following dependency
order:

1. G1: construct the common positive returned germ;
2. G2: rebuild an onto locally unit-speed ray at the returned slopes;
3. G3: select the first positive Markov edge and its initial traversal;
4. D0: construct the two canonical substitutions on the full directed-edge
   alphabet, together with the fixed-word and metric-scaling data;
5. D1: prove that each canonical one-step word records every literal oriented
   crossing of its source edge;
6. D2: prove path-word substitution/concatenation compatibility and propagate
   D1 to a complete decoder for every substitution power;
7. D3: restrict simultaneously to the common occurring alphabet, preserving
   the fixed word, metric realization, and both powered decoders;
8. C1b-L: induce the left powered substitution on every canonical return
   decomposition in the cofinal marker tower;
9. C1b-R: do the same at the right growth scale on those exact shared
   decompositions;
10. C1d: derive the aperiodic linearly-recurrent uniform rank and left/right
    induced-image length bounds;
11. C1e: convert those quantitative bounds into finite codes up to bijective
    relabeling, including the seed, entire derived stream, and substitution;
12. C2: normalize the two repetitions only after choosing a common deeper
    marker and retaining all four nested refinement decoders;
13. C3: build the two nested-return morphisms and their commuting/intertwining
    squares;
14. C4: use aperiodicity to upgrade those squares to compatible positive
    powers with nonzero incidence-matrix bridges;
15. C5: transport primitive Perron eigenvectors across the two bridges and
    obtain the reverse spectral-radius inequalities.

X1 is now proved directly by splitting each source edge at its midpoint,
padding the two exact hitting times with surjectivity, and taking a finite
uniform depth. C0 is also proved: both powered substitutions are relabeled to
finite alphabets over one literal recurrent core, with dominance derived from
the transported positive length eigenvectors. C1a, the shared return
decomposition tower, C1c nested factorization, common-marker alignment, and
the pigeonhole selection are proved reductions to checked APIs rather than
additional leaves.

All other declarations in the scratch file are proved aggregators.  In
particular, D0--D3 are packaged into the exact common-ray coding interface;
uniform crossing plus decoding implies primitivity; primitive fixed words
give linear gaps and syndeticity; and the finite-code pigeonhole selection is
proved directly.  The C-stage inequalities are combined by antisymmetry, and
the resulting equality of positive powers contradicts the stored
multiplicative independence.  Perron-power extraction, ultimately periodic
word construction, periodic-tail globalization, and conversion to the PL
return-path interface are also complete in the audit file.

The C-stage reuses the checked APIs in `SubstitutionPeriodicity` and
`DurandReturnScratch`: recurrent-core extraction, powered return
presentations, return decomposition and decoding, marker alignment, uniform
recurrence of the derived word, and nested return factorization.  The real
remaining mathematical content is therefore C1b-L/R, the C1d--C1e finite
normalized-family bound, and the C2--C5 comparison chain, not a second
reimplementation of those foundational return-word lemmas.

The first C1 proof attempt showed that “finite family” is not by itself enough:
the original scratch structure admitted a constant family at every level and
a one-element code, so its pigeonhole repetition carried no refinement
information. The manuscript must specify the actual tower. Its markers are
nonempty prefixes at position zero with strictly increasing, cofinal lengths;
each scale has an induced powered return presentation at every marker; and for
`i < j` the longer-marker return blocks retain their
`NestedReturnFactorization` into shorter-marker blocks. Uniform
linear-recurrence and aperiodic lower bounds then give the quantitative rank
and normalized-image bounds from which a genuinely finite code follows. Only
repetition in that enriched tower may feed the common-derived-word and
intertwining steps. The enriched Lean C1/C2 skeleton now records each of these
items and has passed the full downstream direct check; the frozen count is the
fifteen leaves listed above.

A further type-level audit exposed one more datum that the tower must retain.
Fixedness, primitivity, and Perron scaling of a return substitution do not by
themselves say that its letter images are the unique parsing of the original
powered substitution on the corresponding return blocks.  At every scale the
tower must therefore name the powered source substitution and store the exact
decoding square
`returnSub(letter).flatMap blocks = source.mapWord (blocks letter)`, together
with the boundary/derived-word tiling facts that make the parsing unique.  The
formal development should isolate this as a generic arbitrary-prefix induced-
return factorization lemma.  The common recurrent-core input must retain both
the original `PoweredPerronData` and the equality identifying its word with the
core word; C1b-L/R should then be choice/packaging lemmas, while the metric,
primitivity, and dominance upgrade remains a separately visible dependency.

The next audit showed that even this exact tower does not justify the proposed
cross-source C3 bridge.  Nested return parsing for one source gives the
same-source identity
`rhoShort.mapWord (theta b) = flatMap theta (rhoLong b)`; four such identities
do not manufacture a morphism intertwining the left and right substitutions.
The old `ReturnMorphismIntertwiningData` was therefore unsound as a proof
boundary: zero or otherwise trivial bridges could satisfy its weak fields.

The revised argument must follow the actual chain in Durand's *A
Generalization of Cobham's Theorem* (Lemma 12 and Propositions 10--11), and
must prove that chain in Lean rather than quote it.  Lemma 12 first passes both
primitive substitutions to one repeated derived system and a common prefix,
then takes one shared positive power of both selected return substitutions so
that every letter image begins with the seed, each
substitution is literally its own induced return substitution, the common
fixed word is nonperiodic, and every letter occurs in every refinement image.
The unpowered selected substitutions do not in general have the begin-seed
property, so omitting this extra exponent is a genuine hypothesis error.  The
same exponent must remain visible in both powered incidence-matrix growths and
in the final multiplicative-dependence arithmetic.
Proposition 10 then constructs, on an infinite exponent subsequence, a single
nonerasing morphism `gamma` and strictly increasing derived exponents `l_p`
with the two exact equations
`Theta^(l_p) ∘ gamma = gamma ∘ Theta^(l_p) = tau^p`.  Proposition 11 converts
those equations, together with its bounded boundary-error matrix argument,
into the comparison of nonzero eigenvalues up to zero and roots of unity.  In
our application the two dominant Perron roots are positive and greater than
one, so the exceptional cases cannot occur; equality of positive powers then
contradicts multiplicative independence.  The formal skeleton should expose
the common-derived-system construction, the finite-morphism pigeonhole, both
matrix directions, and the final Perron specialization as separate lemmas.

The checked body of `durand_poweredReturnPresentation` does not use its
aperiodicity argument. A primitive periodic fixed word can still have a valid
powered return presentation, so the proof should expose an unconditional
constructor and reserve aperiodicity for the return-word lower bound and the
later power-intertwining contradiction where it is genuinely consumed.

Production integration should follow this order:

1. extract the directed-edge, `CommonRayFixedWord`, primitive linear-gap, and
   post-periodicity path APIs needed here into a lightweight module that does
   not import the old `Polygonal` development;
2. add the returned-germ and rebuilt-ray structures/lemmas, with explicit
   returned-scale equalities;
3. implement D0--D3 in order: full canonical coding, one-step literal
   completeness, iteration compatibility, and occurring-alphabet restriction
   preserving the named powered decoder;
4. prove the generic exactness-to-uniform-crossing lemma, then close both
   primitivity and syndeticity aggregators;
5. formalize C1b-L/R, C1d, C1e, then C2--C5 in order, reusing the proved C0,
   marker/decomposition/nested-factorization infrastructure, and finite-family
   pigeonhole/alignment aggregators;
6. use the already checked periodic-word-to-metric-period and periodic-tail
machinery, then replace the false production Boundary 9 declarations
together rather than adapting them one at a time.

## Direct piecewise-monotone eigenmeasure proof

The finite-dimensionality argument is now checked through the embedding into
endpoint cumulative coordinates.  Two details should be made explicit in the
revised manuscript.

First, the transfer partition used formally assigns every internal vertex to
the lap on its right, so a local closed interval `[c_i,x]` is literally a
subset of that assigned lap only when `x < c_{i+1}`.  If `x` is a partition
vertex (including `1`), its cumulative value is already one of the endpoint
coordinates and is zero.  Separating this endpoint case makes the advertised
one-lap scaling argument exact without changing the contraction factor
`2 / lambda^N`.

Second, the statement that a measure is determined by all cumulative values
does not require atomlessness.  On `I = [0,1]`, the anchored closed interval
`[0,x]` is exactly the order ideal `(-∞,x]` in the subtype order.  Equality on
all such order ideals determines each finite Jordan component, hence the real
and imaginary parts of any finite complex measure.  Atomlessness is needed
earlier for the local identity
`sigma([a,b]) = S_sigma(b) - S_sigma(a)`, but not for the final uniqueness
lemma itself.

For the simultaneous-eigenvector step, the formal proof uses a short complex
linear-algebra argument in place of the compact positive-slice/Brouwer
detour.  Complexify the finite-dimensional product eigenspace, choose an
eigenvalue of the restricted `P`-transfer, and restrict the commuting
`Q`-transfer to that nonzero eigenspace.  A second eigenvalue then gives a
common nonzero eigenvector.  Applying the exact returned-product transfer
factorization to this vector yields
`(eigenP * eigenQ)^L = lambda`; since `lambda > 1`, both eigenvalues are
nonzero.  The revised manuscript should adopt this route (and mention
algebraic closedness of `ℂ`) instead of the longer
positive fixed-point construction.  In either version, the exponent `L` in
the returned-word relation must remain explicit until the original scaling
constants are recovered.

The final passage to a positive measure is also now kernel-checked.  Exact
naturality of total variation turns the common complex eigenvector into a
simultaneously scaled atomless positive measure, and normalization preserves
both scaling laws.  Full support is derived only when it is needed: if a
nonempty open set had zero measure, its successive images would remain null
under the exact transfer-eigenidentity, while topological exactness eventually
maps it onto the whole interval, contradicting probability mass one.  This
separates the algebraic joint-eigenmeasure construction from the dynamical
exactness hypothesis and should be reflected in the manuscript's lemma order.

The PL restoration step should not claim that the returned slopes in the
distribution coordinate are literally the dilation constants recorded by the
earlier ray.  The ray package remembers only a continuous surjective
parametrization.  Reparametrizing it by
`t \mapsto sign(t)|t|^c` preserves the ray actions and dense-tail properties
while replacing both recorded dilation constants by a common positive power.
Thus literal equality of either individual constant is not an invariant of
the available data.  The invariant conclusion actually needed later is that
the new one-step slopes exceed one and that their common-return powers are
multiplicatively independent.

The checked proof of that invariant conclusion is cleaner than a comparison
of ray normalizations.  Exactness plus the global Lipschitz estimate for a
finite-piece map of constant absolute slope forces each one-step slope to be
greater than one.  The selected orientation-preserving right `C^1+BV` germs
of the returned maps become increasing germs under the common distribution
homeomorphism, hence positive affine germs with slopes `C^L` and `D^L`.  If
positive powers of these slopes agreed, the corresponding affine germs would
agree on a nondegenerate right interval.  Pulling this equality back through
the common coordinate gives the rational selected-germ relation with
exponents `L m` and `L n`; the already established finite-arrival/LEO germ
determination globalizes it to a forbidden common positive iterate.  This
argument proves precisely the coordinate-invariant independence statement
and does not require adding a metric normalization to the ray package.

## Finite PL fixed sets and canonical quotient descent

The elementary Boundary 1 proofs permit a shorter and more precise
manuscript treatment than an appeal to definability.  On each adjacent affine
cell of a finite PL presentation, the fixed-point equation is affine.  If the
branch is the identity, its fixed set is the whole closed cell; otherwise it
has at most one fixed point.  Filtering the finite lap index to the cells that
actually meet the fixed set therefore writes the global fixed set as a finite
union of closed intervals and singletons.  Overlaps at partition vertices are
harmless, so no disjoint-component decomposition or o-minimal input is needed.

The exact fixed-set formula for a canonical fixed-component quotient is also
stronger than the continuity-based argument suggested by a general quotient
lemma.  A fixed point downstairs has a source representative `x`.  If `x`
lies in a displayed collapsed class, that entire class is fixed by the source
map; if it lies outside the collapsed locus, the exact fibre description says
its fibre is the singleton `{x}`, so the intertwining identity forces `x`
itself to be fixed.  Thus this step needs neither continuity of the source map
nor a fixed-point theorem on an invariant fibre.  In fact, only the assertion
that every displayed collapsed class is a fixed interval is used here; the
maximality and exhaustive-component halves of
`CollapsesExactlyFixedComponents` belong to the construction of the quotient,
not to this descent lemma.

Finally, the minimal-core preservation argument can be phrased entirely in
the same fibre dichotomy.  A common fixed point downstairs either has a
singleton fibre, immediately lifting to a forbidden common fixed point, or a
displayed interval fibre.  Intertwining makes the latter invariant under both
source maps; minimality makes it all of `I`, contradicting the explicit
nonconstancy of the canonical quotient.  This avoids a separate theorem about
inverse images of invariant intervals.  Strict decrease of a finite fixed
count is then just the finite-set fact that an image has strictly smaller
cardinality when the restricted quotient map is not injective.

## Finite directed-state return and positive PL germs

The returned endpoint identities and the orientation statement should be
separated.  Commutation shows that each generator acts as a permutation of
the finite fixed set of `W`; the factorial exponent therefore makes the
returned words `A` and `B` fix both endpoints of the selected gap.  Endpoint
fixation alone does **not** imply that either returned word preserves the
right-hand side of the selected endpoint, so it is not enough to justify a
positive right germ.

The formal proof supplies the missing finite-state argument.  Its states are
pairs consisting of a repelling fixed point of `W` and one available directed
side there.  There are at most twice as many such states as fixed points of
`W`.  If `H ∘ F = W`, `F` commutes with `W`, `F` is continuous, and `W` is
finite PL, then `F` carries every repelling directed state to another one and
`H` carries the target back.  The target side is locally unique, so on the
finite state set this action is injective and hence a permutation.  Applying
this to `P` and `Q` and the factorization `W = P^2 ∘ Q^2` shows that the
canonical factorial exponent returns the selected right-directed state for
both generators.  The left-directed case is obtained by central reflection;
no definability or o-minimal hypothesis is used anywhere in this argument.

Once the directed-side return is stated explicitly, the `C^{1+BV}` conclusion
has a very short PL proof.  Choose the affine cell immediately to the right
of the fixed base point and a second point inside both that cell and the
side-carrying neighborhood.  If the branch is `x ↦ m x + c`, fixing the base
and mapping the second point strictly to its right force `m > 0`.  The same
affine formula is an ambient `C^1` representative, and its logarithmic
derivative is constant, so its variation is zero.  This one lemma applies to
`W` (its repelling state carries itself) and to both returned generators.
The revised manuscript should use this common constructor rather than give
three separate germ calculations.

## Selecting and orienting the fixed gap

The formal B3 proof gives a shorter reason that `Fix(W)` has at least two
points. Continuity supplies one fixed point `r`. Since the normalized
counterexample has no common fixed point, at least one of `P r` and `Q r`
differs from `r`; commutation makes that distinct point fixed by `W`. The exact
finite enumeration of `Fix(W)` then supplies two consecutive fixed points.
On their open gap the sign of `W-id` is constant by the intermediate value
theorem, because a sign change would create another fixed point in the gap.

If that sign points left, central reflection must transport the whole
least-normalized proof state, not merely the chosen interval. The Lean proof
transports finite-piece PL structure, commutation, surjectivity, minimality,
absence of common fixed points, the exact `W`, `R`, and `S` finsets, their
cardinalities, and lexicographic leastness. The normalization exponent is
unchanged because reflection preserves the cardinality of `Fix(W)`; hence the
returned words `R` and `S` conjugate as well. Finally, a common fixed point of
the reflected pair is explicitly pulled back through the involution. A revised
exposition should package this as one reusable reflection-naturality lemma.

## Least-period original phase and terminal parity

The earlier three-stage terminal skeleton forgot two facts needed by its own
conclusion. An arbitrary continuous semiconjugate lift of a folded periodic
path may switch reflected branches at fold points, so it need not be globally
affine. Also, an arbitrary positive period need not generate the full period
group, so a commutator cannot be asserted to be an integral multiple of that
chosen period. These are specification defects rather than missing proof
details.

The existing zero-hole `OriginalPhase` development has the correct interface:
the path is onto, locally finite-piece unit speed, and carries its *least*
positive period; a full-period-group theorem then precedes construction of the
canonical signed affine semiconjugacies. The final reflection/parity argument
works for every positive return exponent and does not require it to be even.
Its only former broad dependency was the constant-absolute-slope definition,
which has now been isolated in `ConstantSlopeDefs` over `DynamicsDefs`.
Consequently the revised manuscript should preserve B9's rich least-period
path package, pass it directly to the checked original-phase theorem, and omit
the arbitrary-lift globalization argument entirely. This route imports no
Polygonal, normalization, definability, tame, or o-minimal material.

## Finite-order fixed sets: production architecture

The Smith/nerve proof is now integrated without a circular import. The
cover-theoretic arc-like predicate is foundational, the prime-order
fixed-continuum theorem lives with the poset-nerve/Smith construction, and the
finite-prime-factor induction lives in `CommonIterate`. The public prime-order,
Fugate--McLean, and arbitrary finite-order theorems all audit to only
`propext`, `Classical.choice`, and `Quot.sound`. The revised manuscript may
therefore present this as an honest theorem boundary; none of the rejected
equal-positive-powers shortcuts should appear.

## Relation to the Boyce--Huneke counterexamples

The revised introduction should make the finite-piece distinction explicit.
Boyce's counterexample does use finite piecewise-linear functions at each
approximation stage, but the commuting maps themselves are uniform limits of
an indefinitely refining sequence. The construction has cross-level
identities of the form `f_n g_{n+1} = g_n f_{n+1}` and obtains exact
commutation only after passage to the limit; the stable partitions become
dense rather than stabilizing at a finite lap partition. Thus the classical
example is not an immediate counterexample to the theorem formalized here.
Avoid saying merely that Boyce and Huneke use “piecewise-linear maps,” since
that can easily be misread as a finite-piece property of the final pair.

## 2026-08-08 — Durand spectral comparison: boundary errors and Perron specialization

- The bounded-error step should be stated with exact word cuts.  A factor of a
  substituted word consists of complete interior substitution tiles plus at
  most one partial tile at each end.  Counting the complete tiles gives the
  matrix term; the two partial tiles give an entrywise uniformly bounded
  residual.  This is cleaner and stronger than referring only to an
  asymptotically negligible boundary contribution.
- The final Perron specialization needs more than the two spectral
  inclusions.  At the selected return level, reconstruct the positive word
  metric from the original edge metric and use primitivity to prove that any
  two positive scaling metrics at that scale are proportional.  Exact
  source/induced-word commutation then makes the return morphism scale this
  metric by a unique positive scalar.
- Prolongability supplies strict growth of that scalar, hence it is greater
  than one.  This explicitly rules out the root-of-unity alternative for the
  corresponding real eigenvalue.  The forward and reverse inclusions can then
  squeeze the two powered Perron growth rates to equality.  The revised
  manuscript should expose these three ingredients instead of hiding them in
  a single appeal to Perron--Frobenius theory.

## 2026-08-08 — finite fixed-component normalization

- Before collapsing the fixed components of `R` and `S`, select a
  `W`-normalized counterexample with globally minimal finite `#Fix(W)`.
  Cardinal nonincrease under the later collapses then forces equality of the
  new and old `W` counts.  This equality—not an informal instruction to
  “restart if the count falls”—is what keeps the factorial return exponent
  unchanged through the three normalization stages.
- Exact descent of fixed points through an interval quotient only requires
  continuity of the map and respect for quotient fibres.  The reusable lemma
  should be stated at that generality; requiring the quotient to collapse the
  fixed components of the very same map is an unnecessarily specialized
  packaging choice.
- Re-minimizing after quotienting, by restricting to an invariant interval
  and affinely rescaling, does not give literal equality of the two fixed
  sets.  The correct statement is an injection from the rescaled fixed set
  into the fixed set before rescaling, which gives exactly the cardinal
  nonincrease used by lexicographic minimality.
- The canonical quotient that collapses all nondegenerate fixed components
  should be constructed explicitly by cumulative removed length.  Its
  continuity, monotonicity, endpoint normalization, fibre description, and
  surjectivity are genuine infrastructure rather than a one-line choice.

## 2026-08-08 — orbit-circle to global-ray interface

- The irrational orbit-circle alternative must retain the full common
  `RightTranslationChart`.  A bare monotone coordinate with two local scale
  equations loses continuity, the physical image conditions, the deck action,
  and the locally strict chart needed to exponentiate and extend the germ.
- At the local orbit-circle stage the two actor scales are positive and
  nonunit, not yet known to exceed one.  Their strict expansion follows only
  after extending the deck germ to a surjective global ray and using
  onto-ness, commutation, and local eventual onto.  The manuscript should not
  assume `scaleA > 1` and `scaleB > 1` prematurely.
- The rational branch first yields signed powers of the repelling deck germ.
  Its negative, zero, and positive sign cases must be eliminated separately;
  it is not immediately an equality of positive iterates of the original two
  actors.
- Package the global irrational branch as one ray-covering object retaining
  the `RayChart`, its local extension, deck and actor actions, local strictness,
  the local-cover witness, and the returned-product identity.  Compact
  tail-core trichotomy, the positive boundary lift, and all five exactness
  conclusions are then generic projections of a single covering theorem.

## 2026-08-08 — Durand Proposition 10 maximal-factorization hypothesis

- The two equations
  `Theta^l gamma = gamma Theta^l = tau^p`, together with increasing `p` and
  `l`, do not imply a uniform bound on the images of `gamma`.  In the
  `Theta = tau^2` model, taking `p_i = 3(i+1)`, `l_i = i+1`, and
  `gamma_i = tau^(i+1)` satisfies those equations while the image lengths are
  unbounded.
- Durand's construction chooses the decoder exponent `l_i` maximally.  The
  revised manuscript must state this maximal two-sided factorization when the
  auxiliary morphisms are introduced; it cannot quantify over an arbitrary
  family of solutions to the equations.
- Separate the proof into the iterated decoder tower, cofinal selection of
  maximal factorizations, and the resulting uniform source/shortest-decoder
  length-ratio estimate.  Only after that ratio estimate should the uniform
  image bound and finite coding of the `gamma_i` be asserted.

## 2026-08-09 — finite-arrival endpoint hypotheses

- A fixed ambient endpoint with singleton fibre is not by itself locally
  attracting; a finite-piece PL map can have such an endpoint repelling.  The
  basin argument also uses the stronger provenance that this particular
  endpoint never occurs in the increasing diagonal images.  Retain the chosen
  endpoint, its never-arrives proof, `S`-fixedness, and singleton fibre as one
  obstruction package, and pass the diagonal-density hypothesis explicitly to
  the basin lemma.
- The terminal-gap exclusion also consumes finite return cover in its
  `p > 0`, `c = 1` case: a covering iterate supplies a preimage of the left
  endpoint, contradicting the strict rightward action of `R = W^d`.  The
  finite-cover hypothesis must therefore appear in that lemma's statement;
  endpoint fixing and local germ data alone are insufficient.  The separate
  `p = 0` case uses the finite generator/state permutations.

## 2026-08-09 — certified phase, orbit-circle, and decoder refinements

- Phase-intersection vertex transitivity does not require injectivity of the
  interval maps.  Work instead with the finite `Z/LZ × Z/LZ` label space:
  translation of labels is a graph automorphism, and the complementary
  `L-1` iterate transports every required intersection.  When the two labels
  coincide, use nonemptiness of the labelled phase interval explicitly rather
  than treating this as an ordinary distinct-vertex adjacency case.
- In the orbit-circle specialization, set
  `d = (2 · #Fix(W))!` and first prove the exact identity `R = W^d`.
  Global commutation of `A`, `B`, and `W` then supplies the three right-germ
  commutations needed by the analytic dichotomy.  The conclusion should retain
  the signed rational deck-power relation or the complete translation chart;
  projecting either branch earlier loses hypotheses used downstream.
- The iterated-decoder part of Durand's Proposition 10 is best stated as an
  explicit tower.  The available cut, marker, and one-step decoder lemmas do
  not by themselves provide a composition theorem, so the formal proof uses
  transparent composition and transport lemmas to build every level while
  preserving both left and right decoder equations.  The manuscript should
  display this tower before making the cofinal maximal choices.
- The terminal-gap argument has two genuinely different cases.  A full
  selected gap is excluded through generator fixed-point and repelling-state
  permutations.  For an internal base with terminal right endpoint, finite
  cover and `R = W^d` produce the contradiction.  Keeping this split explicit
  makes clear exactly where the finite-cover hypothesis enters.

## 2026-08-09 — completed finite arrival, ray globalization, and original phase

- Both the dense-diagonal descent and the endpoint-basin contradiction use the
  same lexicographic fact: no canonical finite interval quotient respected by
  `P` and `Q` may identify two distinct `S`-fixed points.  Prove this once from
  the terminating `W/R/S` normalization and lexicographic minimality, then pass
  it as the callback to both topological arguments.  This removes duplicated
  normalization prose and makes the quotient hypothesis visible.
- The local dilation chart globalizes only after assembling all of the data
  used by the extension theorem: continuity and surjectivity of every actor,
  the `W/A/B` commutations, local strictness of `W`, and the B5 local-cover
  conclusion.  Scale positivity and nontriviality come first; multiplicative
  independence uses the absence of a common fixed point; strict expansion of
  both actor scales is proved only after the global ray is onto.  Presenting
  these in that order avoids the manuscript's former premature `> 1`
  assertion.
- Durand's cofinal maximal factorization is not a bare finite choice.  The
  proof first establishes source/decoder power commutation, parses marker
  prefixes, uses two-sided word cancellation, bounds every admissible decoder
  exponent, and only then chooses the maximum.  The resulting `gamma_k`
  sequence is a direct assembly of the decoder tower and these cofinal maxima;
  the remaining quantitative step is precisely maximality-to-length-ratio.
- Do not project the periodic return path before the original-phase argument.
  Retain `PeriodicReturnPathPackage`, whose path has a least positive period,
  is onto and locally finite-unit-speed, and carries both exact dilation
  returns.  Its path predicate is definitionally equivalent to the one used by
  `OriginalPhase`; the Core and isolated constant-slope predicates are likewise
  definitionally equal.  Thus the final proof is simply the checked affine-lift
  theorem, its parity/common-fixed-point consumer, and coordinate pullback.
  The former arbitrary-lift and nonleast-period records should be removed from
  the revised manuscript rather than repaired.
- In the rational orbit-circle branch, the relation is between signed deck
  powers.  Split on the sign of the first exponent and then on the complementary
  exponent `d n - m`.  Negative cases contradict injectivity/repelling-germ
  behavior, zero cases give a finite-order actor and hence a common fixed
  point, and only the positive/positive case globalizes to equality of positive
  actor iterates.  This sign analysis should replace any sentence that treats
  the rational alternative as immediate positive-power equality.

## 2026-08-09 — singleton tail cores and the maximal-marker estimate

- Excluding a singleton ray-tail core is a local affine-slope argument, not a
  generic consequence of exactness.  At the endpoint of the selected gap,
  split the commuting PL map's right affine germ into zero, negative, and
  positive slope.  Zero would make an onto map locally—and, by the LEO germ
  determination argument, globally—constant; a negative slope contradicts
  the chosen rightward `W` dynamics; and a positive slope gives, by the
  intermediate value theorem, a forbidden `W`-fixed point strictly beyond the
  selected endpoint.  The revised proof should expose this trichotomy and the
  exact point at which onto-ness and LEO are consumed.
- The maximal-factorization length estimate in Durand's argument silently
  uses that the primitive aperiodic source alphabet has at least two letters.
  State this consequence of aperiodicity before the estimate.  The level-`l`
  tower marker is the expanded word `Theta^l(u) … u`; its successive decoded
  blocks therefore give an explicit geometric factor of at least two.  This,
  together with maximality and primitive-source distortion, bounds the source
  prefix against the shortest `Theta^l` image.  Writing the marker explicitly
  is clearer than hiding the factor in an informal growth assertion.
- The corrected B9 proof needs only a dependency-clean collection of primitive
  substitution, return-word, recurrent-language, and dilation-return lemmas.
  It does not need the obsolete general `SubstitutionPeriodicity` aggregators
  (nor any o-minimality material).  The revised manuscript should present the
  specialized chain actually used by the proof and omit those superseded
  detours.
- A local unit-speed radius is an existential germ witness and can always be
  replaced by a smaller positive radius.  It therefore cannot be used to bound
  the length of the first Markov edge.  The geometric coding needs only the
  actual traversal of that edge beginning at time zero; remove the redundant
  radius-bound assertion from the ray-seed package and do not appeal to it in
  prose.
- Once the maximal-factor length-ratio estimate is available, the uniform
  bound on every auxiliary `gamma_k` image is purely algebraic.  Decode a
  `gamma_k` word by `Theta^l`; its decoded length is at least the word length
  times the shortest `Theta^l` letter image.  The source/decoder equation and
  the ratio estimate give the reverse bound, and positivity of that shortest
  image permits cancellation.  Do not describe this final step as a new use
  of linear recurrence; all recurrence work is upstream in the ratio bound.
- The proper nondegenerate ray-tail core is excluded by transporting its exact
  `A`/`B` invariance back to a nondegenerate interval in the normalized model.
  The finite-arrival phase descent then gives a dichotomy: a connected phase
  graph contradicts minimality of the invariant core, while a disconnected
  phase graph yields a respected quotient identifying distinct `S`-fixed
  points, contradicting lexicographic least normalization.  This dependency
  chain should replace any vague appeal to “tail exactness.”
- For a one-sided linearly recurrent word, uniform return-type counting cannot
  start at position zero: a particular return type may make its first
  appearance arbitrarily late.  First choose one common baseline beyond a
  prior occurrence of every member of the finite return family.  From that
  baseline, next-occurrence bounds and the lower bound on return-word lengths
  inject all types into a uniformly bounded set of offsets.  This yields the
  rank bound honestly; the manuscript should not claim uniform initial
  occurrence.
- The iterated first-letter derived-system construction does not itself use
  the nonperiodic-language assumption.  Positive metric expansion supplies
  growing images, hence primitivity and linear recurrence at every step, while
  the nested return factorizations recursively compose the nonempty decoders.
  Keep the aperiodicity hypothesis at the surrounding Durand branch where it
  is needed, but do not cite it as an ingredient of this construction lemma.
- The powered-return-tower interface stores both a distinguished seed and a
  displayed derived fixed word, but currently does not state that the seed is
  the head of that word.  Consequently a finite pigeonhole key cannot safely
  consist of the seed and substitution table alone: the formal proof also
  records the actual derived-word head, then uses primitivity and metric growth
  to recover equality of the relabelled fixed streams.  In the revised
  manuscript either state the intended seed/head relation explicitly or list
  the actual head as part of the finite code, as the Lean proof does.
- The later all-letter powering step shows that the seed/head relation is not
  merely a finite-code convenience.  The concrete tower constructor always
  chooses the derived word's head as its seed, but the abstract record had
  omitted this fact; primitivity, fixedness, prolongability, and generation do
  not recover it (a two-letter Thue--Morse substitution gives a countermodel).
  The corrected interface therefore records `seed_is_head` at every level.
  State that canonical choice explicitly in the manuscript before using a
  common seed for the left and right induced powers.
- Do not set the final common source power to one.  The canonical self-return
  marker is generally a longer word, not the singleton `[seed]`, so
  prolongability alone does not show that the first return letter is the seed.
  Choose a common iterate whose seed image contains `block(seed) ++ marker` as
  a prefix.  The commuting decoder equation and uniqueness of the complete
  return parsing then force every powered induced image to begin with the
  distinguished seed.
- For the simultaneous first-letter repetition step, first realize each
  iterated derived system as a literal return decomposition at one canonical
  cofinal prefix level.  Complete decompositions at the same marker are unique
  up to the alphabet relabeling induced by their literal return blocks.  A
  paired finite-code pigeonhole argument then repeats the left and right
  systems at the same two stages; because every return letter occurs in the
  canonical word, the two a priori relabelings coincide.  This is the precise
  reason one common relabeling transports the word and both substitutions.

## 2026-08-09 — full-alphabet coding and literal edge crossing

- Construct the canonical Markov substitution on the full directed-edge
  alphabet before restricting attention to the recurrent word.  A letter that
  does not occur in the chosen word still needs a substitution image and
  endpoint-compatible geometric model, but no recurrence assertion: choose a
  legal Markov path with the required endpoints and retain the conditional
  image theorem only for occurring letters.  The formal proof exposes a small
  public full-Markov package rather than copying the earlier private
  constructor.  This keeps the manuscript's D0 package honest without
  importing the obsolete symbolic detour.
- The D1 literal-crossing lemma does not use the full-alphabet hypothesis or
  the affine formula stored in D0.  On a strictly monotone source cell, the
  endpoint models place the image path on opposite sides of each target
  subdivision vertex between its endpoint states.  Continuity then forces the
  path to traverse every intervening adjacent oriented edge, even if its
  recorded Markov path later backtracks.  State D1 at this sharper level; it
  makes clear that weak monotonicity has already been upgraded to strictness at
  the selected Markov cells and avoids attributing the crossing conclusion to
  unused coding data.
- For D2, the assertion that every target edge crossed by one source cell
  occurs somewhere in its substitution word is not, by itself, an inductive
  invariant: it forgets the order and the partial intermediate cells needed
  when substitution words are concatenated.  Carry a pointwise parametrized
  realization of the entire literal edge word through the induction.  The
  model path and exact metric-scaling law provide that ordered realization;
  one-step crossing completeness is then a consequence/check, not the sole
  engine of the iteration proof.  The public D2 conclusion need not be
  weakened, but the manuscript should display this stronger private invariant.
- In the successor step of that ordered realization, the end of one decoded
  letter must coincide with the start of the next substituted block.  Local
  realization data alone do not determine this concatenation time.  Use the
  exact word-metric scaling law to identify the total duration of every
  substituted letter image; this is what aligns the block boundary and makes
  the induction compositional.
- The finished D2 proof does not need the separately supplied one-step
  crossing-completeness hypothesis.  The geometric models, affine strictness
  on Markov cells, constant absolute slope, and exact image-metric law already
  construct the stronger ordered one-step realization, from which all powers
  follow.  The existing Lean argument keeps `_oneStep` only to preserve the
  frozen public interface during the port; a proof-aligned manuscript should
  omit it as an independent assumption and derive it as a corollary.
- A reusable symbolic API could expose the finite-word traversal and
  shortest-path lemmas, together with preservation of traversal by
  substitution `mapWord`.  D2 currently proves these locally because the old
  public model predicate records only endpoints and connectivity.
- D3 should be presented as a simultaneous restriction through literal edge
  values, not as a fresh coding construction.  First relabel the full alphabet
  by its underlying directed edges and restrict the common fixed word to the
  finite occurring alphabet.  The restricted substitution images commute with
  the injective inclusion back into the full alphabet; induction transports
  this square to every substitution iterate, and injectivity reflects full
  decoder membership back to the restricted alphabet.  This cleanly preserves
  both powered crossing decoders without any recurrence claim for unused
  letters.

## 2026-08-09 — final journal draft and production audit

- The final public statement is exactly the weak finite-closed-cell theorem:
  each map is continuous and is nondecreasing or nonincreasing on every cell
  of some finite partition. Constant cells and nontrivial plateau subintervals
  are allowed. No strictness, differentiability, definability, nonflatness, or
  entropy hypothesis should be reintroduced in the manuscript.
- The corrected arbitrary-PL theorem is the only downstream theorem required
  by the distribution quotient. The older o-minimal/tame route is not part of
  the stronger proof and has been omitted from the replacement draft.
- The clean public entrypoint imports the corrected acyclic PL assembly.  The
  superseded `Main`/`Assembly` branch was removed during dependency pruning;
  it is not a mathematical dependency of the stronger theorem.
- `common_fixed_points_piecewise_monotone_formalized.tex` is the replacement
  journal draft. It preserves the distinctions among the early orbit-ray
  scales, one-step distribution scales, and returned substitution scales; it
  also includes the ordered D2 invariant, occurrence restriction D3, deep
  seed/head powering, boundary-error comparison, least-period package, and
  original-phase parity pullback.
- The final 40-module public closure contains no executable `sorry`, `admit`,
  or project `axiom`. Lean reports exactly `propext`, `Classical.choice`, and
  `Quot.sound` for the main theorem, so the manuscript must not claim a proof
  in a stricter foundational system than the formal development actually uses.
- A final independent manuscript audit caught two prose errors that were not
  Lean errors. `HasLocalEventualOntoPL W p` is anchored at the selected base:
  it asserts eventual onto for `[p,q]`, not for every arbitrary small interval.
  The scale-independence globalization has been rewritten using exactly this
  anchored image statement.
- The terminal affine-parity lemma needs a degree-sensitive four-case split.
  With one half translation, the witness is the half point for even degree of
  the translated map and the quarter point for odd degree; with two half
  translations, equal even parity uses the half point and equal odd parity
  uses the quarter point. The earlier blanket witnesses were false even though
  the formal `AffineParity` theorem was correct.
- Avoid claiming that a plateau-avoiding sequence of finite resolvent measures
  is atomless merely from that avoidance. The formal argument first obtains a
  continuous limiting coordinate from two-sided smallness and then takes its
  Stieltjes measure; coordinate continuity is the singleton-mass proof.
- The separate correspondence document uses fully qualified declaration
  paths. Strong internal invariants (notably ordered D2 realization and the
  all-iterate D3 intertwining) are identified as proof-body invariants when the
  exported theorem records only the downstream consequence.
- In the C1 return-tower pigeonhole step, the finite code contains only rank,
  seed, head, and a bounded induced-substitution image table. It does not
  contain an infinite derived stream, growing literal decoders, or boundary
  fragments; fixedness and growth recover the stream from the finite code.
- The left and right return systems repeat at their own earlier/later level
  pairs. A single deeper common level aligns those two repetitions. The final
  manuscript now states this order rather than claiming one shared repeated
  pair from the outset.
- The distribution-quotient lemma no longer asserts that the descended factors
  are onto. Onto-ness is derivable from the normalized upstairs maps and the
  surjective coordinate, but it is not used by the reduction and was not a
  named part of the retained quotient interface.
- The orbit-circle proposition now states that one of the rational-deck and
  translation-chart alternatives holds. Their exclusivity is unnecessary:
  the rational alternative is eliminated separately, and the retained
  dichotomy theorem exports a disjunction rather than an exclusivity result.
- All declaration tables, kernel-audit prose, and implementation commentary
  were moved out of the paper into
  `MANUSCRIPT_FORMALIZATION_CORRESPONDENCE.md`. The mathematical paper now
  stands alone as a journal-style argument.
