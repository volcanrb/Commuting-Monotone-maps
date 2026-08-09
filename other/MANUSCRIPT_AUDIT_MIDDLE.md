# Manuscript audit: orbit circle through the common Markov set

## Scope and verdict

This audit covers the mathematical middle of the proof, from the one-sided
orbit-circle construction through the common finite Markov set.  The primary
candidate source is
`common_fixed_points_piecewise_monotone_direct.tex`, especially lines
630--1836.  The corresponding text in
`common_fixed_points_formal_aligned.tex`, lines 735--1941, is almost the same
argument with the notation changed from the PL core to the tame category.

The criticism of the earlier manuscript was substantially justified for the
version it reviewed: that version replaced several long arguments by phrases
such as “Smith refinement,” “finite phase hull,” and “repeated endpoint/germ
incidence.”  The direct manuscript now supplies real proofs of the orbit-line
construction, the common-iterate lemma, dense-tail exactness, the common
coordinate, vertex composition, postvertex finiteness, and the common Markov
set.  Those proofs were not present at comparable resolution in the criticized
draft.  Thus the existence of a rigorous Lean proof did not make the old prose
rigorous; the omitted Lean mathematics had to be restored, and much of it now
has been restored in `direct.tex`.

The direct manuscript is the right base.  It should not, however, be copied
without correction.  The remaining material issues are:

1. the Fugate--McLean result is misidentified as **Corollary 1.5**; the cited
   periodic-homeomorphism result is **Theorem 1.5**;
2. the bridge between the manuscript's `log D` bounded-variation convention
   and the derivative-BV hypothesis in Denjoy's theorem should be explicit;
3. the negative-rational and subunit-scale contradictions need one quantified
   germ-domain induction instead of set-limit shorthand;
4. the proper-tail-core exclusion is valid only together with the full earlier
   quotient/minimality package and must not be transplanted in isolation;
5. the measure-theoretic adjoint of the preimage transfer operator must be
   defined, because the raw preimage-sum operator need not map continuous
   functions to continuous functions at critical values;
6. the vertex/postvertex/Markov arguments need several short intermediate
   claims made explicit, especially the transverse-preimage claim, the
   well-defined action on tail-equivalence classes, the exponent case split,
   and the forward-invariance checks.

On a proof-mass rather than paragraph-count estimate, the current direct text
contains about **86%** of the work in this middle section.  The remaining 14%
is concentrated in the six points above.  This percentage is conditional on
retaining the complete normalization, respected-quotient, and phase-descent
arguments earlier in `direct.tex`.

## Weighted tracker

The weights sum to 100 and estimate the share of the mathematical work in this
middle section, not the number of paragraphs or Lean declarations.

| ID | Proof obligation | Weight | Current status |
|---|---|---:|---|
| M-01 | Regularity and the three classical one-dimensional inputs | 4 | Small hypothesis bridge missing |
| M-02 | Local BV Kopell corollary | 5 | Restore, with two domain/seam sentences |
| M-03 | Direct-limit orbit line and selected lifts | 7 | Substantially proved; representative bookkeeping compressed |
| M-04 | Rational/irrational orbit-circle dichotomy | 7 | Restore; citations and lift normalization are sound |
| M-05 | Exclusion of the rational branch and expanding scales | 6 | Correct idea; quantify the germ induction/limit contradiction |
| M-06 | Common positive iterate | 8 | Substantially complete; correct continuum citation |
| M-07 | Extension of the local dilation to the global ray | 4 | Restore; add one stabilization sentence |
| M-08 | Tail-core extraction and onto invariance | 3 | Complete modulo elementary compactness details |
| M-09 | Exclusion of a singleton tail core | 5 | Cleaner than Lean; expose the nonzero-germ hypothesis |
| M-10 | Exclusion of a proper nondegenerate tail core | 8 | Depends on the full earlier phase-descent package |
| M-11 | Positive boundary lift and exactness of all five maps | 9 | Detailed proof; a few existence/uniformity steps need labels |
| M-12 | Parry--Shultz coordinate and centralizer transfer | 10 | Correct stronger route; define the measure adjoint precisely |
| M-13 | Independence after changing coordinate | 4 | Complete |
| M-14 | Unit-speed polygonal ray | 3 | Complete after the selected-germ formula is cited |
| M-15 | Exact vertex-value composition | 5 | Correct; isolate the transverse-preimage lemma |
| M-16 | Finiteness of both postvertex sets | 8 | Correct core argument; split four compressed claims |
| M-17 | Common forward-invariant Markov set | 4 | Correct construction; spell out invariance and the extra `E(R)` |

## Obligation-by-obligation audit

### M-01. Regularity and cited one-dimensional inputs (weight 4)

**Candidate text.** Direct lines 630--661 and aligned lines 735--766.

**Lean route.** The formal predicates are `HasRightGermC1BV` and the local
regularity fields used by `exists_oneSidedOrbitLineModel` in
`CommutingInterval/OrbitDichotomy.lean:5236`.  The two analytic engines are
`local_c1BV_Kopell_identity_of_accumulating_fixedPoints` at line 1961 and
`denjoy_conjugacy_of_irrational_translationNumber` at line 2234.

**Remaining correction.** The manuscript defines `C^{1+BV}` by bounded
variation of `log Df`, while its quoted Denjoy statement uses bounded variation
of `Df`.  On a compact representative the positive continuous derivative is
bounded above and away from zero; `exp` and `log` are Lipschitz on the relevant
compact ranges, so the two BV conditions are equivalent.  Add this sentence
before invoking Denjoy.  In the PL version the point is immediate because the
selected derivative is locally constant, but the aligned tame version still
needs the bridge.

**Citation requirement.** The Navas citations already have the right form:
Andres Navas, *Groups of Circle Diffeomorphisms*, Theorems 3.1.1 and 4.1.1 and
Propositions 2.2.2--2.2.3.  State each theorem with exactly the regularity used;
do not cite “Denjoy theory” or “Kopell rigidity” generically.

### M-02. Local BV Kopell corollary (weight 5)

**Candidate text.** Direct lines 662--745 (aligned 767--850) is reusable.

**Formal route.** Lean proves the needed accumulating-fixed-point germ result
internally in `OrbitDichotomy.lean:1961`; it then uses it in the signed-power
argument around lines 5499--5666.

**Compressed steps to expose.** When extending the local maps to `[0,1)`, say
explicitly that the chosen `y` is inside a common representative domain and
that the successive fundamental intervals exhaust `[y,1)`.  At a seam, record
the one-line chain-rule cancellation giving the left derivative `Dv(y)` and
right derivative `Dv(u(y))`.  The displayed differentiated commutation identity
then makes these equal.  No new theorem is needed.

### M-03. Direct-limit orbit line (weight 7)

**Candidate text.** Direct lines 774--892 (aligned 879--997) should be restored
essentially verbatim.

**Lean route.** Lean packages the construction as
`OneSidedOrbitLineModel` and proves existence in
`OrbitDichotomy.lean:5236`; the public dichotomy consumes it at lines
5885--5921.

**What the old manuscript omitted.** The quotient relation, ordered topology,
fundamental interval, seam regularity, physical representative at the negative
end, and the distinguished (rather than modulo-integer) lifts were all genuine
mathematics.  The current direct proof now includes them.

**Remaining compression.** Define the equivalence relation as the equivalence
relation generated by the displayed local relation and say that formulas are
evaluated after moving to a sufficiently small representative.  Also justify
`f^{-k}(x) -> 0` by monotonicity and the absence of a punctured-side fixed
point.  These additions prevent domain questions about local inverses.

### M-04. Orbit-circle dichotomy (weight 7)

**Candidate text.** Direct lines 747--946 (aligned 852--1051) is a genuine
proof and is much stronger than the paragraph criticized in the old draft.

**Lean route.** The exact public theorem is `orbit_circle_dichotomy` at
`OrbitDichotomy.lean:5885`.  The rational half is
`rationalTranslationNumber_forces_signed_germ_power` at line 5673 and
`rationalOrbitAlternative_of_model` at line 5713.  The irrational half is
`irrationalOrbitAlternative_of_model` at line 5765, based on the Denjoy theorem
at line 2234.

**Verdict.** Restore.  The manuscript correctly keeps the physical lift, hence
the real translation number rather than only its residue modulo `Z`; it also
uses the exact product lift to force the `B` translation to be `d-alpha`.
This is precisely the hypothesis strength Lean retains.

### M-05. Rational exclusion and dilation scales (weight 6)

**Candidate text.** Direct lines 948--1024 (aligned 1053--1129).

**Lean route.** Lean splits the sign cases into
`negative_signed_germ_power_impossible_plB6` (B6 line 225),
`zero_signed_germ_power_forces_commonFixed_plB6` (line 383), and
`positive_rational_germs_give_commonIterate_plB6` (line 454), and assembles
them in `piecewiseLinear_rationalOrbitAlternative_impossible` (line 516).
Exponentiation is `piecewiseLinear_translationChart_to_localDilation` (line
844).

**Difference from Lean.** The manuscript's shrinking-interval proof for a
negative exponent is cleaner but is not the formal route.  It is valid after
one missing induction: shrink `I_epsilon` so that the signed germ identity and
the local inverse hold there; prove for every `k` that all intermediate images
remain in the nested chart intervals and
`A^{nk}(I_epsilon)=W^{mk}(I_epsilon)`.  Then uniform continuity of the fixed
map `W^q` turns convergence of these intervals to `{p}` into the contradiction
with the constant set `I`.  The identical quantified sentence is needed for
the `0<a<1` scale argument.

### M-06. Common positive iterate (weight 8)

**Candidate text.** Direct lines 1026--1159 (aligned 1131--1264) should be
kept, subject to the citation correction below.

**Lean route.** `naturalExtension_isArcLike` is at
`CommutingInterval/CommonIterate.lean:227`; the homeomorphism result is
`commutingHomeomorphisms_commonFixed_of_equalPositivePowers` at line 1317;
the interval-map theorem is `common_positive_iterate` at line 1614.  Lean's
formal Smith/Fugate substitute culminates in
`primePeriodicHomeomorph_fixedSet_preconnected_of_arcLike` at
`CommutingInterval/SmithFixedSet.lean:4905`.

**Remaining correction.** Both TeX files say “Fugate--McLean, Corollary 1.5.”
The result is cited in the later literature as **Theorem 1.5**, and that is the
number that must appear.  The AMS abstract confirms the exact conclusion: the
fixed set of a periodic homeomorphism of a tree-like continuum is a nonvoid
continuum.

The inverse-limit text should also add one sentence that an inverse limit of
nonempty compact connected spaces with surjective bonding maps is nonempty,
compact, and connected.  The coordinate-fibre estimate then proves arc-like
directly.  State that the manuscript is using the standard epsilon-map
definition of arc-like; since an arc is a finite tree, arc-like implies
tree-like.

**Exact continuum-theory citation.** Use:

> J. B. Fugate and T. B. McLean, “Compact groups of homeomorphisms on
> tree-like continua,” *Trans. Amer. Math. Soc.* **267** (1981), 609--620,
> Theorem 1.5, https://doi.org/10.1090/S0002-9947-1981-0626493-5.

An optional terminology citation is S. B. Nadler, *Continuum Theory: An
Introduction*, Theorem 12.11 (epsilon-map arc-like equals chainable).  Hamilton
is **not required** because the manuscript proves the fixed point of `U|C`
directly by approximate fixed points.  If that direct paragraph is replaced,
then cite O. H. Hamilton, “A fixed point theorem for pseudo-arcs and certain
other metric continua,” *Proc. Amer. Math. Soc.* **2** (1951), 173--174, and
also justify that the fixed subcontinuum has Hamilton's nested-chain form; do
not quote Hamilton as an unexplained blanket fixed-point theorem.

### M-07. Global ray (weight 4)

**Candidate text.** Direct lines 1162--1183 (aligned 1267--1283).

**Lean route.** The generic extension is
`extend_local_germ_to_fullRay` at
`PiecewiseLinearOrbitRaySupport.lean:496`, and actor equivariance is
`localScaleGerm_extends_to_fullRay` at line 607.  The specialization is
`piecewiseLinear_localDilation_to_rayCovering` at B6 line 942.

**Remaining sentence.** If `n` and `n+1` are both sufficiently large, apply
the local identity once to show the two formulas for `Phi(t)` agree; induction
gives stabilization for all larger `n`.  One common `n` on a compact parameter
interval gives continuity and all three equivariance identities.

### M-08. Tail-core extraction (weight 3)

**Candidate text.** Direct lines 1180--1204 (aligned 1285--1309).

**Lean route.** Definitions `tailClosure`, `tailCore`, and `HasDenseTails` are
at `PiecewiseLinearOrbitRaySupport.lean:162--171`.
`commonInvariant_rayTail_extraction` at line 792 proves that every closed tail
is a compact interval and that both actors map the core **onto** itself, not
merely forward into itself.

**Verdict.** The closure bookkeeping in the direct manuscript now matches the
strong Lean conclusion.  Keep the displayed equalities
`A(Omega)=Omega=B(Omega)`.

### M-09. Singleton tail core (weight 5)

**Candidate text.** Direct lines 1206--1227 (aligned 1311--1331).

**Lean route.** Lean proves this via the PL germ sign trichotomy and LEO in
`piecewiseLinear_rayTailCore_not_singleton` at B6 line 1204.

**Cleaner manuscript route.** The current order-theoretic proof is shorter and
appears sound.  It needs three hypotheses named at the point of use: `c != p`
and `R(c)=c` imply that the singleton limit is `q=c`; the selected germs of
`P,Q` have nonzero slope; and commutation maps a repelling source-side germ at
`p` to a repelling target-side germ at `q`, contradicting the attracting sign
of `R-id` on either available side of `q`.  With those sentences this is a
valid cleaner proof, though not Lean's proof script.

### M-10. Proper nondegenerate tail core (weight 8)

**Candidate text.** Direct lines 1229--1264 (aligned 1333--1369).

**Lean route.** `piecewiseLinear_rayTailCore_not_properNondegenerate` at B6
line 1261 invokes
`proper_powerInvariant_interval_impossible_of_phase_descent` at
`PiecewiseLinearFiniteArrivalSupport.lean:1587`.  Fullness and dense tails are
then B6 lines 1297 and 1311.

**Dependency warning.** This proof is not autonomous.  Its phase images,
vertex-transitive intersection graph, respected quotient, preservation of the
counterexample, and strict decrease of the lexicographic fixed-point count all
come from the earlier normalization/quotient package.  The fuller definitions
and proofs in the beginning of `direct.tex` must accompany this paragraph.
Restoring only this tail-core paragraph into a manuscript that still uses the
old undefined “phase hull” terminology would leave the original critique
untouched.

The elementary sublemma that an onto interval selfmap has at least two fixed
points of its square is now proved.  Add only the one-line reason that a unique
fixed point of an onto nondegenerate interval map cannot be an endpoint.

### M-11. Boundary lift and exactness (weight 9)

**Candidate text.** Direct lines 1267--1416 (aligned 1372--1521) is reusable.

**Lean route.** `exists_positiveBoundaryLift` is at
`PiecewiseLinearOrbitRaySupport.lean:1335`; the full package is
`ray_exactness_covering_package` at line 2595.  The PL wrapper is
`piecewiseLinear_denseRay_exactnessPackage` at B6 line 1366, with public
projections for exactness of `P,Q,A,B,R` at B6 lines 1387--1407.

**Remaining explicit claims.** Label or prove the following short points:

1. tail density makes the open preimage `Phi^{-1}(U)` meet arbitrarily late
   tails, so it contains a compact nondegenerate interval mapped into `U`;
2. for `p>0`, choose the component boundary after a positive tail start, which
   guarantees `t_* > 0`;
3. the multiplicative group generated by independent `a,b` is dense after
   taking logarithms, and every tail of the irrational rotation of
   `log a / log(ab)` is dense;
4. the maxima used in the uniform selected-interval step vary continuously by
   the maximum theorem on a fixed compact parameter interval.

The manuscript already contains the substance of all four; giving them names
will make the proof easy to check.

### M-12. Common Parry--Shultz coordinate (weight 10)

**Candidate text.** Direct lines 1418--1567 (aligned 1523--1672).

**Relation to Lean.** This is intentionally **not** the Lean construction.
Lean uses an eventual horseshoe and a finite-dimensional simultaneous
eigenmeasure/resolvent route:
`piecewiseLinear_exactProduct_eventualHorseshoe` (Core line 5237),
`piecewiseLinear_productEigenAdapterData_exists` (5283),
`piecewiseLinear_simultaneousVariationAdapterData_exists` (5346),
`piecewiseLinear_fullSupportDistributionCoordinate_exists` (5373), and
`piecewiseLinear_jointEigenmeasure_commonCoordinate` (6079).

The manuscript correctly replaces that bespoke route by a stronger published
theorem.  Shultz Proposition 3.6 gives the distribution-coordinate conjugacy;
Proposition 4.3 gives existence, atomlessness, full support, and scale
`exp(h_top)`; Corollary 4.6 gives uniqueness in the transitive,
non-essentially-injective case; Corollary 4.4 states Parry's constant-slope
conjugacy.  Exactness supplies transitivity, and the manuscript separately
rules out essential injectivity.

**Actual technical gap.** Define, for a finite Borel measure `nu`,

`int phi d(L_T^* nu) := int (L_T phi) dnu`

for bounded Borel `phi`.  The preimage sum is bounded and Borel because `T`
has finitely many laps.  It need not be continuous at a critical value, so
`L_T^*` should not be introduced merely as the Banach adjoint of an operator
`C(I)->C(I)`.  With this definition, the composition identity, atomicity
calculation, full-support argument, and uniqueness argument in the manuscript
are valid.

**Exact citations.** Keep:

> F. Shultz, “Dimension groups for interval maps II: the transitive case,”
> *Ergodic Theory Dynam. Systems* **27** (2007), 1287--1321, Proposition 3.6,
> Proposition 4.3, and Corollaries 4.4 and 4.6,
> https://arxiv.org/abs/math/0405467.

Parry may be cited historically as W. Parry, “Symbolic dynamics and
transformations of the unit interval,” *Trans. Amer. Math. Soc.* **122**
(1966), 368--378, https://doi.org/10.1090/S0002-9947-1966-0197683-5.  For the
exact uniqueness/full-support form actually used, Shultz is the controlling
citation.

**Do not restore.** The old weak-lap resolvent and exact-horseshoe manuscript
sections are no longer dependencies of this journal proof.  They remain part
of Lean's internal route but should not be reinserted into the paper merely to
mirror formal implementation details.

### M-13. Independence after changing coordinate (weight 4)

**Candidate text.** Direct lines 1569--1588 (aligned 1674--1693).

**Lean route.** `piecewiseLinear_transformedScales_independent` is at Core line
5904 and is stored in the final constant-slope system built at line 6079.

**Verdict.** Complete.  Equality of two positive affine germs gives a local
map equality; exactness of the commuting product globalizes it; the common
positive iterate lemma then contradicts the counterexample.  This retains the
full multiplicative-independence conclusion required later.

### M-14. Unit-speed ray (weight 3)

**Candidate text.** Direct lines 1590--1622 (aligned 1695--1727).

**Formal analogue.** The relevant geometry is rebuilt in
`PiecewiseLinearB9GeometrySupport.lean` using
`extend_local_germ_to_fullRay` and the two actor extensions around lines
588--704.

**Verdict.** Complete.  Constant absolute slope makes every nonconstant affine
piece of the parameter ray have speed one.  State once that flat-freeness
excludes constant pieces in the selected germ used to start the construction.

### M-15. Exact vertex-value composition (weight 5)

**Candidate text.** Direct lines 1624--1678 (aligned 1729--1783).

**Lean route.** `vertexDomain`, `vertexValues`, and genuine turns are defined
in `DynamicsDefs.lean:147--167`.  The public forward inclusion is
`piecewiseLinear_vertexValues_comp` at Core line 6665.  The exact equality with
onto inner map is `vertexValues_comp_of_germs_plCore` at line 6795, and the
rectangular commuting identity is line 6855.

**Remaining lemma.** Isolate: if a continuous onto flat-free finite-piece PL
map crosses an interior level `y`, then some preimage of `y` is transverse
(locally one-to-one).  Choose preimages of 0 and 1 and use a sign-changing
crossing of level `y`; flat-freeness rules out an interval fibre.  Endpoint
levels are attained only at a domain endpoint or a genuine turn.  This closes
the only non-immediate reverse inclusion in the displayed exact formula.

### M-16. Finite postvertex sets (weight 8)

**Candidate text.** Direct lines 1680--1759 (aligned 1785--1864) contains the
right proof, but it should be presented as four claims.

**Lean route.** Postvertex values are defined at Core line 6891.  The
one-sided finiteness theorem is `postvertexPLCore_finite_left` at line 7466;
the symmetric pair is `finite_postvertex_sets_plCore` at line 7675, exposed by
the public A/B results at lines 7751 and 7761.

**Claims to split out.** 

1. The rectangle identity implies
   `B(T_A) subset T_A union Z`, where `Z` is a finite union of eventual
   `A`-cycles.  Include the pigeonhole indices `i<j` and the calculation
   `A^(j-i)(y)=y`.
2. For an infinite `A`-orbit point `w`, the orbit of `B(w)` is infinite;
   otherwise finite-to-one-ness of `B` sends infinitely many distinct points
   into a finite set.  Commutation makes the induced map on the finite set of
   tail-equivalence classes well defined.
3. A cyclic class yields
   `A^p B^r(w)=A^q(w)`; propagation gives infinitely many agreement points.
   A finite common affine partition therefore supplies a nondegenerate
   agreement interval, and exactness globalizes it.
4. From `a^p b^r=a^q` with `r>0`, handle `p<q`, `p=q`, and `p>q` explicitly.
   The first contradicts multiplicative independence; the other two contradict
   `a,b>1` directly (or reduce to independence after cancellation).

These are the mathematical steps hidden by “repeated incidence” in the old
draft.  The direct manuscript now contains all four ideas; splitting them will
make the proof publishable and visibly comparable with Lean.

### M-17. Common finite Markov set (weight 4)

**Candidate text.** Direct lines 1761--1835 (aligned 1866--1940).

**Lean route.** The formal finite invariant hull is
`exists_finite_common_invariant_postvertex_hull_plCore` at Core line 7834;
`PiecewiseLinearMarkovVertexHull` is line 7994;
`piecewiseLinear_exists_markovVertexHull` is line 8010; affine monotone cells
are line 8359; and the public package is line 8399.

**Remaining checks.** After defining `F_A`, explicitly write

`A(F_A) subset F_A` and `B(F_A) subset F_A`,

using forward invariance of `T_A`, the inclusion
`B(T_A) subset T_A union Z_A`, commutation, and preservation of
`Fix(A^r_A)`.  Do the symmetric check for `F_B`.  Then state the four
cross-turn inclusions used to prove invariance of `E(A),E(B),E(R)` modulo
`F_A,F_B`.  These are present in prose but are easy for a referee to miss.

The manuscript includes `E(R)` in `K`, whereas Lean's basic Markov hull only
requires the vertices of `A` and `B`.  This is a valid and useful strengthening
for the later ray argument, not a mismatch, provided the displayed
`A(E(R))`/`B(E(R))` transport is retained.  The correspondence document should
record this as “paper derives a slightly stronger hull,” rather than claiming
literal field-for-field identity with `PiecewiseLinearMarkovVertexHull`.

## Source-restoration decision

### Restore essentially verbatim from `direct.tex`

- the local BV Kopell proof;
- the direct-limit orbit line and selected-lift dichotomy;
- the common-positive-iterate proof;
- the canonical ray, tail closure bookkeeping, and boundary-lift exactness;
- the Parry--Shultz common-coordinate route;
- the definitions of `E(T)`, vertex values, postvertex sets, and the common
  Markov set.

### Restore only together with earlier dependencies

- the singleton and proper tail-core exclusions;
- every appeal to the phase-intersection graph, quotient package, and
  lexicographic descent.

### Correct while restoring

- `Corollary 1.5` to `Theorem 1.5` for Fugate--McLean;
- the `log D` BV / `D` BV bridge;
- quantified germ-domain induction in the negative/subunit arguments;
- the measure-adjoint definition;
- the short intermediate claims in M-15--M-17.

### Do not restore from the obsolete proof route

- o-minimality discussion not used by the strengthened piecewise-linear core;
- the manuscript weak-lap resolvent and exact-horseshoe detour, now replaced in
  the paper by Parry--Shultz;
- Lean-only adapter structures and type-management lemmas.

## Bottom line for the user's question

Yes: the criticized manuscript had omitted substantial mathematical proofs
that existed in Lean.  “Aligned with the formal proof” had meant that the
named statements and dependency order corresponded, not that the prose
contained the arguments.  The newer `common_fixed_points_piecewise_monotone_direct.tex`
repairs most of that omission and is the correct base for the journal draft.
After the explicit corrections above, the middle will be both mathematically
self-contained at journal resolution and accurately related to the zero-axiom
formal development without mentioning Lean in the paper itself.
