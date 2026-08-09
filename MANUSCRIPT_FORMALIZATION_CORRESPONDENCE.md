# Manuscript--formalization correspondence

## Status and source of truth

This is the authoritative correspondence for
`common_fixed_points_piecewise_monotone_direct.tex` and the Lean development
rooted at `CommutingInterval.lean`.

The file `common_fixed_points_piecewise_monotone_direct.tex` is the working
and review source for the current journal manuscript. The file
`common_fixed_points_piecewise_monotone_formalized.tex` is its release mirror:
it is copied from the direct source after a completed revision. If the two
files differ during an in-progress revision, the direct source is
authoritative; after release synchronization they must be byte-identical.
This rule prevents an older release copy from silently determining the
correspondence.

The current direct manuscript has exactly **36 labeled theorem-like
environments** (theorems, propositions, lemmas, and claims). The count does
not include displayed equations. The introductory definition of
finite-piece piecewise monotonicity is intentionally unlabelled and is mapped
separately below. This document supersedes the earlier 35-item map in full.
No labels from that older manuscript topology are current interfaces.

The correspondence records mathematical interfaces, not a claim that the
paper and Lean must use identical proofs internally. When the paper invokes a
standard published theorem in its natural generality, while Lean proves the
needed special case by a longer internal construction, both routes and the
point at which they rejoin are stated explicitly below.

## Proof and trust status

The retained Lean tree is the exact 40-module transitive import closure of the
public theorem. It contains:

- zero executable `sorry` terms;
- zero executable `admit` terms;
- zero project `axiom` declarations; and
- no obsolete definability or o-minimality infrastructure.

The public final theorem is
`CommutingInterval.finitePieceMonotone_common_fixed_point`. The corrected
piecewise-linear theorem and its public alias are
`CommutingInterval.PiecewiseLinearCorrectedAssembly.finitePiecePL_common_fixed_point`
and `CommutingInterval.finitePiecePL_common_fixed_point`.

Release synchronization was completed on 2026-08-09.  The direct source and
the formalized release mirror are byte-identical; each has SHA-256
`55FCB41A42E319FB221AB74E2E9C3D90D3B63FF808BDBEB2F42D701B50609F6B`.

For all three declarations, `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`. These are Lean's standard logical
and quotient foundations. In particular, there is no `sorryAx`, no
project-defined axiom, and no axiom standing for any cited mathematical
paper. Every published theorem used in the manuscript has a proved internal
replacement on the Lean path; the published theorem is not imported into
Lean as an assumption.

## Classification vocabulary

- **Exact public statement**: a stable Lean declaration has the same
  mathematical content, modulo routine encodings such as the subtype
  `[0,1]`, bundled conjunctions, or `Nonempty` packages.
- **Aggregate**: one manuscript result collects several proved Lean
  declarations or structure fields.
- **Structure/field representation**: Lean stores the paper's conjunction as
  fields of a record and proves existence of that record.
- **Internal invariant**: the fact is proved inside a retained theorem, often
  by a source-local `private` declaration, but is not exported under a stable
  public name.
- **Paper alternate route**: the manuscript gives a complete proof through a
  different standard mathematical route and rejoins the Lean dependency
  graph at the stated interface.
- **Published substitution**: the manuscript invokes a published theorem
  whose hypotheses are checked in the paper; Lean proves the needed special
  case without assuming that theorem.

Line numbers are deliberately not used as identifiers because they drift
under cleanup. File names and declaration names are stable and searchable.
Source-local `private` names are identified as such and should not be treated
as public API.

## Basic language and the unlabelled definition

| Manuscript notion | Lean representation | Relationship |
|---|---|---|
| The interval `I=[0,1]` and its selfmaps | `CommutingInterval.I`; `CommutingInterval.IntervalMap` in `CommutingInterval/Defs.lean` | Exact definitions. |
| Fixed points and common fixed points | `CommutingInterval.fixedPoints`; `CommutingInterval.IsFixedPoint`; `CommutingInterval.HasCommonFixedPoint` in `Defs.lean` | Exact definitions. |
| Commutation | mathlib's `Function.Commute` | Exact definition. The paper's product convention is `UV=U\circ V`, read right to left. |
| Finite-piece piecewise monotonicity, including plateaus | `CommutingInterval.IsWeaklyMonotoneOn`, `MonotonicityPartition`, and `FinitePieceMonotone` in `PiecewiseMonotoneDefs.lean` | Exact public definition. Monotonicity is non-strict, so constant pieces are included. |
| Finite-piece piecewise linearity, including slope zero | `CommutingInterval.FinitePiecePL` in `DynamicsDefs.lean` | Exact public definition. |
| Canonical finite interval quotients and fibre respect | `CommutingInterval.CanonicalFiniteIntervalQuotient` and `CommutingInterval.RespectsFibres` in `QuotientDefs.lean` | Exact typed representation of the paper's quotient convention. |
| Signed nonatomic measures and branch transfer | `VectorNoAtoms`, `monotoneBranchImageVector`, `piecewiseMonotoneTransferVector`, and the positive-measure `transferMeasure` in `PiecewiseMonotoneVariation.lean` | Lean is polymorphic over real/complex scalars where useful; the paper uses the real signed-measure specialization. |

## Ordered map of all 36 current manuscript labels

The ordering below is the order of appearance in the direct manuscript. It
is the only current label map.

### Piecewise-linear core, normalization, and orbit circle

| No. | Current manuscript label | Principal Lean counterpart(s) | Classification and exact boundary |
|---:|---|---|---|
| 1 | `thm:main` | `CommutingInterval.finitePieceMonotone_common_fixed_point` in `PiecewiseMonotoneMain.lean` | **Exact public statement.** The hypotheses are precisely continuity, finite non-strict monotonicity partitions for both maps, and commutation; the conclusion is a common fixed point. |
| 2 | `prop:PL-core` | `CommutingInterval.PiecewiseLinearCorrectedAssembly.finitePiecePL_common_fixed_point`; public alias `CommutingInterval.finitePiecePL_common_fixed_point` in `PiecewiseLinearCorrectedAssembly.lean` | **Exact public statement.** Constant affine pieces are allowed. |
| 3 | `lem:pl-finiteness` | `PiecewiseLinearFinitenessPackage`; `finitePiecePL_comp`; `finitePiecePL_iterate`; `finitePiecePL_fixedPoints_finiteUnion`; `finitePiecePL_descendedMap`; `piecewiseLinear_finitenessPackage` in `PiecewiseLinearCore.lean` | **Aggregate.** These declarations give closure, finite-union fixed sets, flat-free finite-to-one behavior, bounded-variation affine germs, and stability under respected finite quotients. |
| 4 | `prop:quotient-package` | `CanonicalFiniteIntervalQuotient` in `QuotientDefs.lean`; `finitePiecePL_descendedMap`, `commute_descendedMap`, `fixedPoints_descendedMap_exact`, and `noCommonFixedPoint_descendedMap_of_minimalCore` in `PiecewiseLinearCore.lean` | **Aggregate.** It collects unique descent, regularity, commutation, onto descent, exact fixed-point descent, invariant-core lifting, fixed-component collapse, and fixed-cardinality descent. The paper proves the component-permutation and endpoint/orientation cases explicitly. |
| 5 | `lem:pl-normalization` | `NormalizedPiecewiseLinearCounterexample`; `LeastNormalizedPiecewiseLinearCounterexample`; `exists_lexLeastNormalizedPiecewiseLinearCounterexample`; `exists_leastNormalizedPiecewiseLinearCounterexample`; and `leastNormalizedPiecewiseLinear_no_respectedQuotient_identifying_S_fixedPoints_b5Prototype` in `PiecewiseLinearCore.lean` | **Aggregate/structure representation.** The three fixed-set minimizations and their dependency order are fields and construction theorems in Lean. |
| 6 | `lem:pl-states` | `PiecewiseLinearDirectedReturnData` and `piecewiseLinear_directedStateReturn` in `PiecewiseLinearCore.lean` | **Exact structure/field representation.** Lean records permutation of repelling directed sides, strict affine germs, fixed selected endpoints, and the one-sided `C^{1+BV}` data. |
| 7 | `lem:local-BV-Kopell` | `CommutingInterval.local_c1BV_Kopell` in `OrbitDichotomy.lean` | **Exact public statement.** The paper may cite Navas for the general bounded-variation Kopell input; Lean proves the one-sided form used here. |
| 8 | `lem:orbit-circle` | `CommutingInterval.orbit_circle_dichotomy` in `OrbitDichotomy.lean` | **Exact public statement.** It supplies the signed rational-power alternative or the normalized irrational translation chart, with selected lifts fixed rather than merely chosen modulo deck translations. |
| 9 | `clm:direct-limit-orbit-line` | `RightOrbitLineEmbedding`, `OneSidedOrbitLineModel`, `exists_oneSidedOrbitLineModel`, `RightTranslationChart`, and the construction consumed by `orbit_circle_dichotomy` in `OrbitDichotomy.lean` | **Aggregate/internal invariant.** The claim is the paper-level geometric package for the orbit-line and its three commuting actions; Lean separates the embedding, regular lift, rational, and irrational records. |
| 10 | `lem:pl-common-iterate` | `CommutingInterval.common_positive_iterate` in `CommonIterate.lean`, with `naturalExtension_isArcLike` and `commutingHomeomorphisms_commonFixed_of_equalPositivePowers` | **Exact public statement.** The manuscript uses Fugate--McLean, Corollary 1.5, p. 613, at the periodic fixed-set step; Lean proves that step internally by its Smith-theory route. |

### Restored coordinate and finite Markov structure

| No. | Current manuscript label | Principal Lean counterpart(s) | Classification and exact boundary |
|---:|---|---|---|
| 11 | `lem:pl-transfer` | Paper route rejoins at `PiecewiseLinearConstantSlopeSystem` and `piecewiseLinear_jointEigenmeasure_commonCoordinate` in `PiecewiseLinearCore.lean` | **Paper alternate route.** The paper derives centralizer eigenmeasures from uniqueness in the Parry--Shultz scaled-measure theorem. Lean reaches the same common constant-slope coordinate through the product-eigenmeasure, simultaneous-variation, and full-support distribution adapters. There is intentionally no retained public Lean declaration with the lemma's literal adjoint-transfer type. |
| 12 | `lem:vertex-composition` | Source-local private `vertexValues_comp_of_germs_plCore`, supported by public `piecewiseLinear_vertexValues_comp`, in `PiecewiseLinearCore.lean` | **Exact internal invariant.** The private result is the germ-level composition identity used by the postvertex proof. |
| 13 | `clm:pl-transverse-preimage` | Elementary subargument inside the postvertex/Markov proof in `PiecewiseLinearCore.lean` | **Paper alternate decomposition.** Onto-ness and absence of flats give a preimage away from turns. There is no stable public declaration with exactly this standalone type; the argument is written out in the manuscript. |
| 14 | `lem:finite-postvertex` | Source-local `finite_postvertex_sets_plCore` and `piecewiseLinear_finitePostvertexSets_core`; public `piecewiseLinear_A_hasFinitePostvertexSet` and `piecewiseLinear_B_hasFinitePostvertexSet` in `PiecewiseLinearCore.lean` | **Aggregate.** The public consequences match the two finite postvertex assertions; the common proof is private implementation. |
| 15 | `clm:pl-postvertex-exceptional` | Source-local `image_postvertex_or_vertex_or_periodic_plCore` and the finite exceptional-set construction inside `postvertexPLCore_finite_left` in `PiecewiseLinearCore.lean` | **Paper alternate decomposition/internal invariant.** The paper exposes the finite exceptional periodic set that Lean keeps inside the finiteness proof. |
| 16 | `clm:pl-tail-class-action` | Source-local `eventually_image_mem_postvertex_of_infinite_orbit_plCore` and the tail-class part of `postvertexPLCore_finite_left` in `PiecewiseLinearCore.lean` | **Paper alternate decomposition/internal invariant.** It is not an extra assumption and is not exported as a separate public theorem. |
| 17 | `clm:pl-tail-relation-global` | The globalized iterate relation proved inside source-local `postvertexPLCore_finite_left` in `PiecewiseLinearCore.lean` | **Internal consequence.** The manuscript isolates the precise relation needed for the slope comparison; Lean proves it in the enclosing private proof. |
| 18 | `clm:pl-tail-slope-contradiction` | Final constant-slope contradiction inside source-local `postvertexPLCore_finite_left` in `PiecewiseLinearCore.lean` | **Internal consequence.** It closes the infinite-tail case using multiplicative independence. |
| 19 | `lem:common-Markov-set` | `PiecewiseLinearCommonMarkovPackage`; `PiecewiseLinearMarkovVertexHull`; `piecewiseLinear_exists_markovVertexHull`; `piecewiseLinear_markovHull_cells`; and `piecewiseLinear_exists_commonMarkovPackage` in `PiecewiseLinearCore.lean` | **Aggregate/structure representation.** The package contains finiteness, both postvertex sets, endpoints and the selected base, forward invariance under both maps, strict affine behavior on adjacent cells, and the literal Markov path property. |
| 20 | `clm:pl-turn-transport` | Source-local turn-composition lemmas, including `genuineTurn_comp_iff_plCore` and `image_postvertex_or_vertex_or_periodic_plCore`, used by `piecewiseLinear_exists_markovVertexHull` in `PiecewiseLinearCore.lean` | **Exact internal aggregate.** The two displayed transport inclusions are the paper's set-level form of these typed turn and vertex facts. |
| 21 | `clm:pl-Markov-invariance` | The `MapsTo` and cell fields of `PiecewiseLinearMarkovVertexHull` and `PiecewiseLinearCommonMarkovPackage`; `piecewiseLinear_markovHull_cells` | **Exact structure/field representation.** This claim records forward invariance and the resulting common Markov partition. |

### Directed-edge coding, periodic return, and original phase

| No. | Current manuscript label | Principal Lean counterpart(s) | Classification and exact boundary |
|---:|---|---|---|
| 22 | `term:prop:common-edge-coding` | `directed_edge_substitutions_and_common_ray_word` in `PiecewiseLinearB9SymbolicSupport.lean`; `FullAlphabetRayCodingData`, `exists_fullAlphabetRayCodingData`, `fullCoding_oneStep_literalCrossingComplete`, `fullCoding_pathWord_iterationCompatible`, `OccurringAlphabetRestrictionData`, and `exists_exactCommonRayCodingData` in `PiecewiseLinearB9Scratch.lean` | **Aggregate/structure representation.** Together these give the common seed, actual occurring alphabet, nonerasing prolongable substitutions, the literal fixed word, all-iterate ordered pointwise realization, prefix identities, and exact metric laws. |
| 23 | `term:lem:perron-power` | `dominant_natMatrix_eigenvalue_has_perron_power` and `weak_perron_eigenvalue_has_perron_power` in `PiecewiseLinearB9SymbolicSupport.lean` | **Exact public statement.** The manuscript supplies the standard Frobenius-block proof and applies it to the two incidence matrices. |
| 24 | `term:prop:periodic-return-path` | `PeriodicReturnPathPackage` in `PiecewiseLinearB9SymbolicSupport.lean`; `periodic_commonRay_produces_returnPathPackage` in `PiecewiseLinearB9Scratch.lean`; `markovSubstitutions_periodicReturnPathPackage` in `PiecewiseLinearB10Scratch.lean` | **Exact structure/field representation.** The package contains the continuous onto periodic unit-speed path, its least positive period/full period group, integral scales, and both global return identities. The paper gets ultimate periodicity directly from Durand; Lean gets it from `exactCoding_word_ultimatelyPeriodic`. |
| 25 | `term:lem:cross-period` | `CommutingInterval.cross_period_globalization` in `OriginalPhase.lean` | **Exact public statement.** It globalizes a local equality between two finite-piece unit-speed periodic surjections and proves the integer cross-period relation. |
| 26 | `term:lem:rescaled-original-path` | Source-local `original_map_has_integral_affine_parameter_lift` and its supporting local-match/descent lemmas, exported through `normalized_real_affine_lifts_of_cross_period` in `OriginalPhase.lean` | **Aggregate/internal stronger route.** Lean proves the needed integer affine lift for both original maps in one typed package; the paper states and proves the reusable one-map lemma. |
| 27 | `term:lem:global-reflection` | `CommutingInterval.unique_reflection_of_expanding_dilation` in `OriginalPhase.lean`, with `unitSpeedPeriodicSurjection_has_local_reflection` | **Exact public statement.** The full hypothesis list includes onto-ness, unit-speed finite-piece behavior, periodicity, the expanding dilation return, and a local reflection. |

### Plateau-safe reduction to the PL core

| No. | Current manuscript label | Principal Lean counterpart(s) | Classification and exact boundary |
|---:|---|---|---|
| 28 | `pm:thm:BF` | Paper: Bogatyi--Frolkina, Theorem 1. Lean replacement: `TwoBranchHorseshoe` and `commuting_noCommonFixedPoint_horseshoe` in `PiecewiseMonotoneHorseshoe.lean`, followed by the weak-lap growth route in `PiecewiseMonotoneResolvent.lean` | **Published substitution.** In the authors' base-two convention the cited theorem gives `h_2(F)+h_2(G) >= h_2(F\circ G) >= log_2(4)=2` for a commuting interval pair without a common fixed point; only strict positivity is needed in the paper. Lean does not assume entropy theory here. |
| 29 | `pm:thm:constant-slope` | Paper: Alseda--Misiurewicz, Theorem A, Lemmas 1.1, 3.1, 4.2, and equation (2). Lean replacement: `weakLapGrowthData_exists`, `weakLapRadiusData_exists`, the compatible-coordinate resolvent construction, and `transferMeasure_eigenprobability_exists_of_horseshoe` in `PiecewiseMonotoneResolvent.lean` | **Published substitution.** The paper invokes the general compatible constant-slope semiconjugacy. Lean proves only the special eigenmeasure/coordinate interface required downstream. |
| 30 | `pm:lem:monotone-image-measure` | `branchPlateauValues_countable` in `PiecewiseMonotoneTransfer.lean`; `monotoneBranchImageVector_apply`, `monotoneBranchImageVector_noAtoms`, `monotoneBranchImageMeasure_apply`, `monotoneBranchImageMeasure_noAtoms`, and `monotoneBranchImageMeasure_isFinite` in `PiecewiseMonotoneVariation.lean` | **Exact aggregate.** Lean's scalar-polymorphic form contains the paper's real signed-measure statement. Countable plateau values make the apparent image-measure formula countably additive. |
| 31 | `pm:lem:composition` | `piecewiseMonotoneTransferVector_independent`, `piecewiseMonotoneTransferVector_comp`, `transferMeasure_independent`, and `transferMeasure_comp` in `PiecewiseMonotoneVariation.lean` | **Exact public aggregate.** Both routes use assigned endpoint cells and the reversed composition law `T_{U\circ T}=T_T\circ T_U`. |
| 32 | `pm:lem:finite-dimensional` | `productEigenspace` and `productEigenspace_finiteDimensional` in `PiecewiseMonotoneEigen.lean` | **Formal specialization.** The paper proves the real signed-measure eigenspace statement for the displayed positive-entropy product `H`. Lean proves the complex product eigenspace finite-dimensional after the product eigenmeasure data have been bundled. This is exactly the specialization Lean consumes, but it is not literally a theorem for an arbitrary unbundled `H`. |
| 33 | `pm:lem:compact-slice` | Paper route has no literal retained counterpart. Lean uses `restrictedTransfers_jointEigenvector`, `jointEigenvector_variation`, and `simultaneousEigenmeasureConstruction_exists` in `PiecewiseMonotoneEigen.lean` | **Paper alternate route.** The manuscript proves compactness of the positive mass-one slice in a finite-dimensional real eigenspace and then applies Brouwer to a normalized positive transfer. Lean instead chooses a common complex eigenvector for the commuting restricted transfers and passes to total variation. Both routes rejoin at simultaneous positive eigenmeasures. |
| 34 | `pm:prop:simultaneous-measure` | `simultaneousEigenprobability_of_productEigenprobability` in `PiecewiseMonotoneEigen.lean`; `MinimalPiecewiseMonotoneCounterexample.simultaneousTransferEigenProbability_exists` in `PiecewiseMonotoneMain.lean` | **Exact outcome.** Both give one atomless probability, positive scales `C,D`, the two transfer eigen-equations, and `C*D=lambda>1`; only the construction route differs. |
| 35 | `pm:lem:fibers` | `SimultaneousTransferEigenProbability.respectsFibres_P`, `.respectsFibres_Q`, `.intertwines_factorP`, `.intertwines_factorQ`, `.continuous_factorP`, `.continuous_factorQ`, and `.factors_commute` in `PiecewiseMonotoneQuotient.lean` | **Aggregate of exact public statements.** Onto-ness of the descended maps follows from the factor identity and onto-ness of the original maps; Lean packages the required data in `CommonPiecewiseLinearQuotientData`. |
| 36 | `pm:lem:PL-quotient` | `SimultaneousTransferEigenProbability.factorP_affineOn_cell`, `.factorQ_affineOn_cell`, `.finitePiecePL_factorP`, `.finitePiecePL_factorQ`, `.coordinate_collapses_plateau_P`, and `.coordinate_collapses_plateau_Q` in `PiecewiseMonotoneQuotient.lean` | **Aggregate of exact public statements.** It includes slope-zero quotient pieces and arbitrary plateau intervals crossing a chosen monotonicity partition. |

## Essential unlabelled bridges

The paper contains several indispensable arguments between labeled results.
They are not omissions. Their principal Lean interfaces are listed here so
that the dependency chain can be followed without treating labels as the
only mathematical content.

| Unlabelled manuscript bridge | Lean counterpart(s) | Role in the final proof |
|---|---|---|
| Minimal common invariant core, nondegeneracy, affine rescaling, and onto-ness of both maps | `exists_minimalCommonInvariantCore`; `PiecewiseMonotoneCounterexample.exists_nondegenerate_minimalCore`; `minimalCommonInvariantCore_mapsOnto`; `PiecewiseMonotoneCounterexample.exists_minimalCounterexample` in `PiecewiseMonotoneReduction.lean` | Normalizes the general reduction and ensures the mass lower bound for the Brouwer map. |
| Fixed-component normalization and selected adjacent fixed gap | `exists_leastNormalizedPiecewiseLinearCounterexample`; `PiecewiseLinearSelectedFixedGap`; `exists_piecewiseLinearSelectedFixedGap` in `PiecewiseLinearCore.lean` | Supplies the finite fixed sets, canonical exponent, chosen repelling side, and lexicographic obstruction to later quotients. |
| Finite arrival, selected-gap covering, and local eventual onto | `HasFiniteSelectedGapCover`; `HasLocalEventualOntoPL`; `PreparedPiecewiseLinearCounterexample`; `piecewiseLinear_finiteArrivalAndLEO` in `PiecewiseLinearCore.lean` | Extends local germ identities globally and rules out subunit return scales. |
| Rational orbit-circle alternative is impossible | `PiecewiseLinearB6.piecewiseLinear_rationalOrbitAlternative_impossible` in `PiecewiseLinearB6Scratch.lean`, using `common_positive_iterate` | Leaves multiplicatively independent expanding scales. |
| Tail-core trichotomy, exclusion of singleton/proper interval cases, and dense tails | `PiecewiseLinearB6.piecewiseLinear_rayTailCore_trichotomy`; `.piecewiseLinear_rayTailCore_not_singleton`; `.piecewiseLinear_rayTailCore_not_properNondegenerate`; `.piecewiseLinear_rayTailCore_eq_univ`; `.piecewiseLinear_ray_hasDenseTails` | Turns the germ ray into a global dense ray. |
| Boundary lift and exactness of `P,Q,A,B,R` | `PiecewiseLinearB6.BoundaryLiftData`; `.ExactnessData`; `.piecewiseLinear_denseRay_exactnessPackage` and its five exactness projections | Supplies flat-freeness, transitivity, globalization of local equality, and the Markov/coding hypotheses. |
| Common Parry coordinate, transformed scales, and their independence | `PiecewiseLinearConstantSlopeSystem`; `piecewiseLinear_jointEigenmeasure_commonCoordinate`; `piecewiseLinear_transformedScales_independent` in `PiecewiseLinearCore.lean` | Rejoins the paper's Parry--Shultz route with the Lean PL pipeline. |
| Rebuilt unit-speed returned ray and first positive Markov seed | `PiecewiseLinearB9Scratch.RebuiltReturnedRayData`; `rebuild_returned_unitSpeedRay`; `RebuiltRaySeedData`; `exists_rebuiltRay_and_seed` | Supplies the literal geometric input for edge substitutions. |
| Restriction from the full directed alphabet to the actually occurring alphabet | `OccurringAlphabetRestrictionData`; `fullCoding_restrictToOccurringAlphabet`; `ExactCommonRayCodingData`; `exists_exactCommonRayCodingData` in `PiecewiseLinearB9Scratch.lean` | Ensures every retained letter occurs and both powered substitutions are generating at the actual head seed. |
| Primitivity/recurrence facts available on the Lean route | `exactCoding_substitutionA_primitive`; `exactCoding_substitutionB_primitive`; `exactCoding_word_hasLinearFactorGaps`; `exactCoding_word_recurrentFactorsSyndetic` | These feed Lean's internal two-scale comparison. The journal proof does not need to reproduce them after it verifies Durand's definition directly. |
| Two-scale periodicity | Paper: Durand, Definition 2 and Theorem 1. Lean: `primitive_twoScale_periodicRecurrentLanguage` and `exactCoding_word_ultimatelyPeriodic`, built from the C0--C5 chain in `PiecewiseLinearB9Scratch.lean` | Produces ultimate periodicity of the common directed-edge word. |
| Periodic tail extension, onto-ness, least period, and integral return scales | `exists_periodic_tail_extension`; `periodic_tail_extension_unit_speed`; `periodic_nonconstant_path_has_least_period`; `path_periodGroup_eq_integer_multiples`; `periodic_tail_range_eq_univ_of_exact`; `PeriodicReturnPathPackage` in `PiecewiseLinearB9SymbolicSupport.lean` | Produces the global polygonal circle path used in the original phase. |
| Real affine lifts of the original maps, exact lift commutation, reflection normalization, and parity | `normalized_real_affine_lifts_of_cross_period`; `original_phase_affine_lifts`; `exists_common_reflection_orbit_of_half_translations`; `common_fixed_point_of_original_phase_package` | Converts the periodic returned system back to a common fixed point of the original `P,Q`. |
| Fixed quotient fibre and final minimality contradiction | `SimultaneousTransferEigenProbability.commonFixedFibre_exists`; `MinimalPiecewiseMonotoneCounterexample.false` in `PiecewiseMonotoneMain.lean` | A common fixed point of the PL factors yields a common invariant fibre; minimality forces that fibre to be the whole interval, contradicting the expanding product scale. |

## Complete route-divergence and published-input ledger

This section is intentionally redundant with the per-label map. It is the
single checklist of every place where the current paper deliberately does
not reproduce the internal Lean route.

### Published theorems used directly in the manuscript

1. **Bogatyi--Frolkina, Theorem 1 (`pm:thm:BF`).** In the authors'
   base-two entropy convention, a commuting interval pair without a common
   fixed point satisfies
   `h_2(F)+h_2(G) >= h_2(F\circ G) >= log_2(4)=2`. The paper checks
   continuity, commutation,
   compact-interval selfmap hypotheses, and absence of a common fixed point.
   Only positivity is used. Lean instead constructs a strict two-branch
   horseshoe and then develops weak-lap growth and resolvents.

2. **Alseda--Misiurewicz, Theorem A, Lemmas 1.1, 3.1, 4.2, and equation
   (2) (`pm:thm:constant-slope`).** The paper checks that the product map is
   continuous, finite-piece weakly monotone, and has positive entropy.
   Compatibility governs collapsed laps; the branch-scaling identity comes
   from the constant-slope factor and equation (2), not from compatibility
   alone. Lean replaces this general theorem by the special weak-lap
   resolvent/eigenprobability construction in `PiecewiseMonotoneResolvent.lean`.

3. **Navas, Propositions 2.2.2 and 2.2.3 and Theorems 3.1.1 and 4.1.1
   (`lem:local-BV-Kopell`, `lem:orbit-circle`).** The paper uses the
   Poincare translation-number criterion, Denjoy's theorem, and the
   bounded-variation Kopell lemma after checking that the chosen one-sided
   maps are orientation-preserving local diffeomorphism germs, have the
   required derivative/log-derivative variation, commute, and use fixed
   normalized lifts. Lean proves the specialized versions in `Kopell.lean`,
   `Denjoy.lean`, `DenjoyKoksma.lean`, and `OrbitDichotomy.lean`.

4. **Fugate--McLean, Corollary 1.5, p. 613
   (`lem:pl-common-iterate`).** The corollary
   says that the fixed set of a periodic homeomorphism of a tree-like
   continuum is a nonempty continuum. The manuscript proves that its natural
   extension is nonempty, compact, connected, arc-like and hence tree-like,
   and that the relevant lift is periodic. Lean proves the required fixed-set
   theorem internally through `PosetNerve.lean`, `PosetNervePrism.lean`, and
   `SmithFixedSet.lean` before consuming it in `CommonIterate.lean`.

5. **Parry--Shultz (`lem:pl-transfer` and the common-coordinate passage).**
   The manuscript uses Parry's conjugacy theorem together with Shultz,
   Propositions 3.6 and 4.3 and Corollaries 4.4 and 4.6. It checks finite laps,
   exactness (hence transitivity), flat-freeness, and non-essential
   injectivity. These yield an atomless full-support scaled probability,
   scale greater than one, uniqueness, and the distribution coordinate. The
   paper then proves the centralizer-transfer lemma in full. Lean instead
   uses the returned-map horseshoe, product-eigen adapter,
   simultaneous-variation adapter, and full-support distribution-coordinate
   chain ending in `piecewiseLinear_jointEigenmeasure_commonCoordinate`.

6. **Durand, Definition 2 and Theorem 1 (between
   `term:lem:perron-power` and `term:prop:periodic-return-path`).** The
   manuscript takes positive substitution powers, verifies nonerasing and
   prolongability at the actual seed, cofinal convergence of seed prefixes to
   the same word, occurrence/generation of every retained letter, identity
   letter coding, Perron dominant eigenvalues, and multiplicative
   independence. Durand then gives ultimate periodicity directly. Lean
   replaces this invocation by the proved C0--C5 return-word and boundary
   error development in `PiecewiseLinearB9Scratch.lean`, culminating in
   `exactCoding_word_ultimatelyPeriodic`. C0--C5 is formal-proof
   infrastructure, not part of the journal argument.

The Boyce and Huneke examples are cited only for historical context and are
not proof inputs.

### Paper-only reorganizations or alternate proofs

1. **`lem:pl-transfer`.** This is a complete paper proof using uniqueness of
   the Parry--Shultz scaled measure. The Lean proof does not export the same
   preimage-adjoint lemma; it reaches the identical common-coordinate
   interface through eigenmeasure adapters.

2. **`clm:pl-transverse-preimage`.** The manuscript isolates the elementary
   onto/flat-free preimage observation. Lean keeps it inside the Markov proof.

3. **The postvertex claims `clm:pl-postvertex-exceptional`,
   `clm:pl-tail-class-action`, `clm:pl-tail-relation-global`, and
   `clm:pl-tail-slope-contradiction`.** The manuscript exposes every logical
   stage of the finite-postvertex proof. Lean packages these stages inside
   private declarations ending in `postvertexPLCore_finite_left`. This is a
   difference of theorem granularity, not a difference of assumptions or
   conclusion.

4. **`term:lem:rescaled-original-path`.** The manuscript states a reusable
   one-map globalization lemma. Lean proves a slightly stronger simultaneous
   typed package for both maps; its key one-map theorem is source-local and
   the public rejoining interface is
   `normalized_real_affine_lifts_of_cross_period`.

5. **`pm:lem:finite-dimensional`.** The manuscript proves the real
   eigenspace result directly with cumulative-distribution coordinates. Lean
   proves the complex, bundled product-eigenspace specialization that its
   next construction needs. Neither statement is being used as an unchecked
   surrogate for the other; each route proves its own required version.

6. **`pm:lem:compact-slice` and Brouwer.** The manuscript's positive
   mass-one slice is proved closed and bounded in a finite-dimensional real
   space, and the normalized positive transfer has a denominator bounded
   below by one; Brouwer produces its fixed point. Lean instead obtains a
   common complex eigenvector for the commuting restricted transfers and
   passes to total variation. The routes rejoin exactly at
   `pm:prop:simultaneous-measure`.

7. **Real signed measures versus scalar-polymorphic Lean measures.** The
   paper writes only the real transfer calculus needed for the Brouwer route.
   Lean proves branch-image and transfer identities for `RCLike` scalars and
   separately specializes to positive measures. This is an encoding
   generalization in Lean, not additional manuscript mathematics.

All other current labeled statements are exact public statements,
aggregates of proved declarations, record-field packages, or explicitly
identified internal invariants in the 36-row map. There is no hidden appeal
to an unpublished theorem.

## End-to-end dependency spine

The final mathematical dependency order is:

1. normalize a hypothetical PL counterexample and select a repelling side;
2. obtain finite arrival/LEO, the orbit-circle dichotomy, expanding
   multiplicatively independent returns, and a dense exact ray;
3. obtain a common constant-slope coordinate and finite common Markov set;
4. code the common ray by two literal metric substitutions;
5. use Perron powers and Durand (the paper route), or C0--C5 (the Lean route),
   to obtain an ultimately periodic edge word;
6. build the least-period onto polygonal path, globalize original-map affine
   lifts and reflection, and use parity to contradict the PL counterexample;
7. on a minimal general piecewise-monotone counterexample, obtain positive
   entropy and one simultaneous atomless conformal measure;
8. descend through its distribution function to commuting finite-piece PL
   maps; and
9. lift the PL common fixed point to a common invariant fibre and contradict
   minimality.

The formal assembly declarations realizing the last steps are:

- `PiecewiseLinearCorrectedAssembly.irrationalExactSystem_commonFixedPoint`;
- `PiecewiseLinearCorrectedAssembly.leastNormalizedPiecewiseLinearCounterexample_false`;
- `PiecewiseLinearCorrectedAssembly.finitePiecePL_common_fixed_point`;
- `CommutingInterval.finitePiecePL_common_fixed_point`;
- `MinimalPiecewiseMonotoneCounterexample.false`; and
- `CommutingInterval.finitePieceMonotone_common_fixed_point`.

No o-minimality or definability assumption occurs anywhere in this spine.
The weak-lap resolvent, Smith-theory, and C0--C5 developments are retained
Lean proofs of interfaces for which the paper uses broader published
theorems; they are not extra hypotheses and need not appear in the journal
body.

## Maintenance checklist

Whenever either manuscript source is revised:

1. extract every `\\label{...}` attached to a theorem, proposition, lemma, or
   claim in `common_fixed_points_piecewise_monotone_direct.tex`;
2. update the ordered map above, keeping its count equal to the extracted
   count;
3. record every new published substitution or paper-only alternate route in
   the divergence ledger;
4. verify that every public Lean name still resolves in the retained import
   closure;
5. re-run the no-hole and `#print axioms` audits; and
6. only then copy the direct source to
   `common_fixed_points_piecewise_monotone_formalized.tex` and verify identical
   hashes.

This document belongs outside the paper. None of its Lean declaration names,
implementation classifications, or proof-route comparisons should appear in
the journal manuscript itself.
