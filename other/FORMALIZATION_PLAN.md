# Formalization plan and progress tracker

## Completion tracker

**Estimated work completion: 100%**  
**Estimated work remaining: 0%**  
**Lean proof holes (`sorry` / `admit`) remaining: 0**  
**Project `axiom` declarations remaining: 0**  
**Known manuscript proof holes remaining: 0**  
**Open review/correspondence/release gates: 0**  
**Unresolved manuscript/formal-statement mismatches: 0**  
**Published inputs awaiting audit: 0 of 6**  
**Retained Lean source files: 40, exactly the public theorem import closure**  
**Kernel dependencies of the final theorem:**
`[propext, Classical.choice, Quot.sound]`  
**Final theorem:**
`CommutingInterval.finitePieceMonotone_common_fixed_point`

The percentage is weighted by estimated work, not by the number of holes.
The kernel proof, dependency cleanup, expanded journal manuscript, independent
proof review, literature audit, correspondence rebuild, and release
synchronization are complete.  Each current manuscript interface was closed
only after a proof-completeness audit verified one of the following:

1. all mathematical definitions and proof steps have been stated in the
   manuscript at journal level; or
2. a precisely stated published theorem is cited, every one of its hypotheses
   is checked in the manuscript, and the deduction of the required result is
   written out.

Lean-specific typing or implementation plumbing is not copied into the paper.
Substantive finite-state, analytic, topological, combinatorial, and rigidity
arguments are.

| Work package | Earned / weight | Status |
|---|---:|---|
| mathematical Lean proof | 45 / 45 | complete |
| exact dependency pruning and kernel audit | 10 / 10 | complete |
| complete journal-level proof exposition | 35 / 35 | all sections expanded; end-to-end adversarial review found no substantive gap |
| established-theorem selection and hypothesis checks | 5 / 5 | all six primary sources and every application audited |
| manuscript/formal correspondence and final validation | 5 / 5 | live 36-label map complete; both manuscript sources are byte-identical and statically clean |
| **Total** | **100 / 100** | **complete** |

### Manuscript proof-completeness work order

The frozen direct manuscript now has 36 labeled theorem-like interfaces,
supplemented by explicit unlabelled bridges for the longer proof stages.  That
current interface list is the fixed release skeleton.  The former 35-item map
belonged to the obsolete compressed manuscript and must not be used as a
progress measure.  An interface is closed only after its prose proof (or exact
published input and hypothesis check) and its current correspondence entry
have both been checked.

| Stage | Items | Mathematical work | Status |
|---:|---:|---|---|
| M1 | current labels 1--6 plus unlabelled bridges | statement, PL finiteness, safe quotients, normalization, directed states, finite arrival, anchored LEO | expanded and manager-reviewed |
| M2 | current labels 7--10 plus unlabelled bridges | local Kopell, orbit circle, direct-limit line, common positive iterate, tail core, exactness | expanded and manager-reviewed |
| M3 | current label 11 plus unlabelled bridges | Parry--Shultz coordinate, scale independence, rebuilt unit-speed ray | expanded and manager-reviewed |
| M4 | current labels 12--21 | vertex composition, postvertex rigidity, common finite Markov set | expanded and manager-reviewed |
| M5 | current labels 22--24 | literal common coding, Perron powers, direct Durand invocation, periodic return path | expanded and manager-reviewed |
| M6 | current labels 25--27 plus unlabelled bridges | cross-period globalization, original-map lifts, reflection, parity | expanded and manager-reviewed |
| M7 | current labels 28--36 plus unlabelled bridges | BF/AM reduction, real branch transfer, Brouwer eigenmeasure, common quotient, final contradiction | expanded and manager-reviewed |
| M8 | all current interfaces | independent proof, source, correspondence, citation, static, and canonical-sync audit | complete |

The two previously known discrepancies are closed:

- the weak-lap resolvent uses infinite convergent resolvents at parameters
  tending to the critical radius, not finite truncations; that internal Lean
  route is now accurately documented in the correspondence, while the paper
  uses the stronger published BF/AM route and contains no resolvent sketch;
- the periodic return path is constructed by a periodic tail extension,
  followed by scale integrality and globalization, not by propagating equality
  backward through a possibly noninjective preperiod; the manuscript now gives
  that construction in full.

The following literature substitutions were checked against their primary
statements, including every manuscript-facing hypothesis and final
cross-reference:

1. Bogatyi--Frolkina's positive-entropy theorem for a commuting interval pair
   without a common fixed point;
2. Alsed\`a--Misiurewicz's compatible constant-slope semiconjugacy theorem;
3. the Navas formulations of Kopell, Poincar\'e translation number, and
   Denjoy used in the orbit-circle reduction;
4. Fugate--McLean's fixed-continuum theorem for periodic homeomorphisms of
   tree-like continua (together with the elementary chainable fixed-point
   consequence);
5. the Parry--Shultz constant-slope/scaled-measure theorem in the exact
   returned-map setting; and
6. Durand's two-scale substitutive periodicity theorem.

The rebuilt correspondence document explicitly distinguishes every stronger
published theorem used by the paper from the narrower route independently
formalized in Lean.

## Historical kernel-completion checklist

These checks record the completed Lean phase before the manuscript was
reopened for full exposition.  They do not supersede the live 100% tracker
above.

- [x] Rebuild the public root after the final source cleanup.
- [x] Re-scan all remaining Lean sources for `sorry`, `admit`, project
  `axiom`, missing imports, and removed o-minimal identifiers.
- [x] Structurally validate the then-current release manuscript and confirm
  that its body contains no implementation rhetoric.  The stronger direct
  rewrite is undergoing a new release audit above.
- [x] Complete the earlier declaration review.  The obsolete 35-item map has
  since been replaced by the live 36-label correspondence.
- [x] Record the earlier 100% kernel milestone.  The current percentage also
  includes the subsequently reopened manuscript work.

## Proof dependency order

The skeleton was written in this dependency order and is now completely
filled. Each row names the mathematical boundary and its principal Lean
module. No row contains a hole.

| Order | Mathematical boundary | Principal module(s) | Status |
|---:|---|---|---|
| 1 | interval maps, finite partitions, weak monotonicity | `Defs`, `PiecewiseMonotoneDefs` | complete |
| 2 | minimal invariant core and direct two-branch horseshoe | `PiecewiseMonotoneReduction`, `PiecewiseMonotoneHorseshoe` | complete |
| 3 | plateau-safe transfer, variation, weak-lap resolvent | `PiecewiseMonotoneTransfer`, `PiecewiseMonotoneVariation`, `PiecewiseMonotoneResolvent` | complete |
| 4 | simultaneous eigenprobability and distribution quotient | `PiecewiseMonotoneEigen`, `PiecewiseMonotoneQuotient` | complete |
| 5 | finite-piece PL normalization and quotient support | `PiecewiseLinearCore`, `PiecewiseLinearQuotientSupport` | complete |
| 6 | common positive iterate via arc-like inverse limits and Smith theory | `ArcLikeDefs`, `PosetNerve`, `PosetNervePrism`, `SmithFixedSet`, `CommonIterate` | complete |
| 7 | orbit circle, global ray, dense tails, and exactness | `OrbitDichotomy`, `PiecewiseLinearOrbitRaySupport`, `PiecewiseLinearB6Scratch` | complete |
| 8 | restored constant-slope metric and finite Markov hull | `PiecewiseLinearCore`, `PiecewiseLinearB9GeometrySupport` | complete |
| 9 | exact directed-edge coding and occurring-alphabet restriction | `SymbolicDefs`, `PiecewiseLinearB9Scratch` | complete |
| 10 | primitive two-scale return-word comparison | `PiecewiseLinearB9SymbolicSupport`, `PiecewiseLinearB9Scratch` | complete |
| 11 | least-period return path, original phase, terminal parity | `OriginalPhase`, `AffineParity`, `PiecewiseLinearB10Scratch` | complete |
| 12 | unconditional PL assembly and weak-monotone reduction | `PiecewiseLinearCorrectedAssembly`, `PiecewiseMonotoneMain` | complete |

## Public theorem skeleton

The final assembly is:

1. Assume commuting finite-piece weakly monotone maps have no common fixed
   point.
2. Restrict to a minimal common invariant interval.
3. Obtain an expanding atomless transfer eigenprobability from the direct
   horseshoe and weak-lap resolvent.
4. Extract a simultaneous eigenprobability for the two commuting transfers.
5. Use its distribution coordinate to produce commuting finite-piece PL
   factors.
6. Apply the unconditional PL common-fixed-point theorem.
7. Lift the common fixed fibre; minimality makes it the whole interval,
   contradicting the distinct endpoint values of the distribution coordinate.

Principal final declarations:

- `CommutingInterval.PiecewiseLinearCorrectedAssembly.finitePiecePL_common_fixed_point`
- `CommutingInterval.finitePiecePL_common_fixed_point`
- `CommutingInterval.MinimalPiecewiseMonotoneCounterexample.false`
- `CommutingInterval.finitePieceMonotone_common_fixed_point`

## Retained Lean source manifest

The following 40 files are exactly the recursive project-import closure of
`CommutingInterval.lean`:

1. `CommutingInterval.lean`
2. `CommutingInterval/AffineParity.lean`
3. `CommutingInterval/ArcLikeDefs.lean`
4. `CommutingInterval/Basic.lean`
5. `CommutingInterval/CommonIterate.lean`
6. `CommutingInterval/ConstantSlopeDefs.lean`
7. `CommutingInterval/Defs.lean`
8. `CommutingInterval/Denjoy.lean`
9. `CommutingInterval/DenjoyKoksma.lean`
10. `CommutingInterval/DynamicsDefs.lean`
11. `CommutingInterval/ExpandingFixedPoints.lean`
12. `CommutingInterval/Kopell.lean`
13. `CommutingInterval/OrbitDichotomy.lean`
14. `CommutingInterval/OriginalPhase.lean`
15. `CommutingInterval/ParryDefs.lean`
16. `CommutingInterval/PiecewiseLinearB10Scratch.lean`
17. `CommutingInterval/PiecewiseLinearB6Scratch.lean`
18. `CommutingInterval/PiecewiseLinearB9GeometrySupport.lean`
19. `CommutingInterval/PiecewiseLinearB9Scratch.lean`
20. `CommutingInterval/PiecewiseLinearB9SymbolicSupport.lean`
21. `CommutingInterval/PiecewiseLinearCore.lean`
22. `CommutingInterval/PiecewiseLinearCorrectedAssembly.lean`
23. `CommutingInterval/PiecewiseLinearEndpointBasinSupport.lean`
24. `CommutingInterval/PiecewiseLinearFiniteArrivalSupport.lean`
25. `CommutingInterval/PiecewiseLinearOrbitRaySupport.lean`
26. `CommutingInterval/PiecewiseLinearQuotientSupport.lean`
27. `CommutingInterval/PiecewiseMonotoneDefs.lean`
28. `CommutingInterval/PiecewiseMonotoneEigen.lean`
29. `CommutingInterval/PiecewiseMonotoneHorseshoe.lean`
30. `CommutingInterval/PiecewiseMonotoneMain.lean`
31. `CommutingInterval/PiecewiseMonotoneQuotient.lean`
32. `CommutingInterval/PiecewiseMonotoneReduction.lean`
33. `CommutingInterval/PiecewiseMonotoneResolvent.lean`
34. `CommutingInterval/PiecewiseMonotoneTransfer.lean`
35. `CommutingInterval/PiecewiseMonotoneVariation.lean`
36. `CommutingInterval/PosetNerve.lean`
37. `CommutingInterval/PosetNervePrism.lean`
38. `CommutingInterval/QuotientDefs.lean`
39. `CommutingInterval/SmithFixedSet.lean`
40. `CommutingInterval/SymbolicDefs.lean`

The filenames containing `Scratch` are retained because they are genuine
dependencies of the certified theorem. Renaming those large production
modules was deliberately excluded from this cleanup: it would provide no
mathematical simplification and would destabilize declaration names used by
the correspondence document.

## Completed deletion record

On 2026-08-09, 46 Lean files outside the public theorem closure were removed.
They comprised 54,180 lines and contained all 31 remaining executable
`sorry`s. The removed files were:

- root exploratory files: `AbelCoordinateScratch`,
  `ContinuumSeparatorScratch`, `CoordinateScratch`, `DistributionScratch`,
  `DurandReturnScratch`, `EquivariantNerveScratch`, `MetricGrowthScratch`,
  `MetricTransportScratch`, `NormScratch`, `OrbitLineScratch`, `ParryScratch`,
  `PrimeFixedScratch`, `PrismScratch`, `Probe`, `RayExactnessScratch`,
  `ReturnInducedScratch`, `Scratch`, and `SmithApiCheck`;
- superseded theorem path: `Assembly`, `Main`, `Definability`,
  `FiniteArrival`, `Normalization`, `ProofStates`, `QuotientLemmas`,
  `RayDynamics`, and `TameLemmas`;
- obsolete transfer, constant-slope, polygonal, and substitution modules:
  `ConstantSlope`, `ParryExistence`, `ParryTransfer`, `Polygonal`,
  `PolygonalRay`, and `SubstitutionPeriodicity`;
- development prototypes and audits: `DurandSyndeticScratch`,
  `PiecewiseLinearB5BasinPrototype`,
  `PiecewiseLinearB5NormalizationPrototype`,
  `PiecewiseLinearB7ScaleIndependencePrototype`,
  `PiecewiseLinearB7Scratch`, `PiecewiseLinearB9C2Prototype`,
  `PiecewiseLinearB9D1Prototype`, `PiecewiseLinearB9D2Prototype`,
  `PiecewiseLinearB9D3Prototype`, `PiecewiseLinearB9DPrototype`,
  `PiecewiseLinearB9GeometryPrototype`, and
  `PiecewiseLinearOrbitRaySupportAudit`;
- the nondependency executable audit module `AxiomAudit` (the reproducible
  temporary-file audit procedure is recorded in `AXIOM_AUDIT.md`).

The unused o-minimal definitions were also removed from the retained
`Defs.lean`; only the interval-map and finite-partition foundations remain.

## Verification record

Completed after pruning:

- [x] Recursive import audit: 40 retained files, 0 missing project imports.
- [x] Clean project build after deleting `.lake/build`:
  `lake build CommutingInterval` — 3,329 jobs, exit code 0.
- [x] Source scan: 0 executable `sorry`, 0 executable `admit`, 0 project
  `axiom` declarations.
- [x] Source scan: no `OMinimalExpansion`, `FinitePieceC1`, or definability
  infrastructure remains.
- [x] Fresh `#print axioms` audit of all three public/corrected final theorems:
  exactly `[propext, Classical.choice, Quot.sound]`.
- [x] Manuscript correspondence section snapshotted before its removal from
  the paper.
- [x] Journal manuscript body stripped of Lean/formalization/API rhetoric.
- [x] Independent end-to-end mathematical review: all eight referee issues
  closed; no critical, high, or moderate gap and no lost hypothesis found.
- [x] Primary-source audit of all six published inputs and every application;
  Fugate--McLean corrected to Corollary 1.5, p. 613.
- [x] Final TeX static audit: 36 theorem-like labels, 133 unique total labels,
  0 missing references or citations, balanced environments/braces/math
  delimiters, strict UTF-8, and no control characters.
- [x] Direct and release manuscript sources synchronized byte-for-byte at
  SHA-256
  `55FCB41A42E319FB221AB74E2E9C3D90D3B63FF808BDBEB2F42D701B50609F6B`.

## Document roles

- `common_fixed_points_piecewise_monotone_direct.tex` is the authoritative
  working and review source for the fully expanded journal paper.
- `common_fixed_points_piecewise_monotone_formalized.tex` is the standalone
  release mirror.  It is copied byte-for-byte from the direct source only
  after the final review gates close.  Its body contains no discussion of
  Lean or implementation details.
- `MANUSCRIPT_FORMALIZATION_CORRESPONDENCE.md` is the separate mapping from
  manuscript definitions, lemmas, propositions, and theorems to fully
  qualified Lean declarations and proof-body invariants.
- `MANUSCRIPT_REVISION_NOTES.md` records mathematical clarifications exposed
  while formalizing the argument.
- `AXIOM_AUDIT.md` records the reproducible kernel-dependency audit.
