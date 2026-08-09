# Audit of the manuscript through finite arrival and LEO

Scope: `common_fixed_points_piecewise_monotone_formalized.tex`, lines 1--584.  This audit compares each displayed definition, lemma, proposition, and theorem in that range with the declarations actually used by the Lean proof.  It is a replacement plan, not a proposed patch to the manuscript.

## Executive verdict

The formal theorem is not obtaining its result by assuming the mathematical steps that the manuscript omits.  The load-bearing steps below are proved in Lean.  The problem is that the manuscript compresses long arguments into a sentence or two, sometimes replaces the formal argument by a different unproved argument, and in several places describes different objects from the ones used in Lean.

The most serious discrepancies are these.

1. The weak-lap construction in manuscript lines 283--290 is not the Lean construction.  Lean uses an **infinite** convergent power series at parameters `t_n < r`, normalizes by the infinite total series, and lets `t_n` increase to the critical radius.  It does not use finite truncations with weights `1,r,...,r^N`.
2. Lean normalizes lexicographically by the concrete triple
   `(#Fix(W), #Fix(R), #Fix(S))`.  There is no undefined complexity of a "chosen positive word" plus "phase components."
3. The bound `2 #Fix(W)` controls repelling **directed sides** (a fixed base point and a choice of left/right side), not fixed/phase components, affine cells, or phase data.
4. Exclusion of a quotient identifying two `S`-fixed points is a lexicographic fixed-count argument.  The manuscript's claim that the interval between extreme identified points is a fixed component is neither the formal proof nor justified as written.
5. Density of the returned gap follows from a connected/disconnected phase-graph dichotomy.  In the connected case, vertex transitivity plus the one-dimensional Helly property and minimality force the full interval.  Only the disconnected case produces a quotient.
6. A missing ambient endpoint first yields an `S`-fixed endpoint with singleton `S`-fibre.  Lean then constructs a separate proper immediate attracting-basin closure and applies phase descent.  It does not split a "terminal fibre" into singleton and interval cases.
7. Anchored LEO uses the global inequality `W(x) > x` on the entire selected gap, a monotone-orbit threshold lemma, and the finite `R = W^d` cover.  Positivity of a short affine germ alone cannot move an arbitrary interval far enough.

Thus the current prose should not be advertised as a proof merely because it follows the same broad route as the formalization.  A formal proof certifies the Lean declarations and their dependency graph; it does not certify a shorter, independently written proof sketch.

## Declaration-by-declaration audit

Status terminology:

- **Exact**: the mathematical statement matches a public Lean theorem or definition.
- **Compressed**: the statement matches, but the written proof omits indispensable mathematical arguments.
- **Mismatch**: the manuscript describes a different construction or a more general result than the retained Lean declaration.

| Manuscript item | Status | Lean counterpart and required correction |
|---|---|---|
| Finite-piece weak monotonicity, lines 62--71 | Exact | `IsWeaklyMonotoneOn`, `MonotonicityPartition`, and `FinitePieceMonotone` in `CommutingInterval/PiecewiseMonotoneDefs.lean:27,31,41`.  Lean packages continuity together with existence of a finite closed-cell partition. |
| Main theorem, lines 76--82 | Exact | `finitePieceMonotone_common_fixed_point`, `CommutingInterval/PiecewiseMonotoneMain.lean:119`. |
| Piecewise-linear core, lines 92--95 | Exact | `FinitePiecePL`, `CommutingInterval/DynamicsDefs.lean:136`, and `finitePiecePL_common_fixed_point`, `CommutingInterval/PiecewiseLinearCorrectedAssembly.lean:211` (root-level alias at line 231). |
| Minimal common invariant core, lines 111--132 | Exact statement; compressed proof | `exists_minimalCommonInvariantCore`, `PiecewiseMonotoneCounterexample.exists_nondegenerate_minimalCore`, `minimalCommonInvariantCore_mapsOnto`, and `PiecewiseMonotoneCounterexample.exists_minimalCounterexample`, `CommutingInterval/PiecewiseMonotoneReduction.lean:152,197,352,441`.  The formal proof uses a chain-intersection lemma and Zorn, then proves that images are compact intervals and invariant.  The claimed "equivalent" minimization of endpoint pairs is not established in the manuscript. |
| Direct two-branch horseshoe, lines 135--173 | Exact conclusion; heavily compressed proof | `TwoBranchHorseshoe` and `commuting_noCommonFixedPoint_horseshoe`, `CommutingInterval/PiecewiseMonotoneHorseshoe.lean:37,1038`.  Lean actually obtains strictly separated branches, stronger than merely disjoint interiors.  The full construction passes through `MinimalFixedCrossingPair`, `marr_configuration_of_commuting_noCommonFixedPoint`, and separate strict-margin trimming lemmas.  Symbolic preimages are `TwoBranchHorseshoe.symbolic_preimages`, `PiecewiseMonotoneResolvent.lean:2179`. |
| Plateau-value removal, lines 177--201 | Essentially exact; statement needs precision | `branchPlateauValues` and `branchPlateauValues_countable`, `PiecewiseMonotoneTransfer.lean:85,88`; vector/positive image measures are `monotoneBranchImageVector` and `monotoneBranchImageMeasure`, `PiecewiseMonotoneVariation.lean:146,349`.  The literal formula is `E -> z(u '' (E intersect D))`, where `D` is a measurable monotone branch.  Complex measures are treated as finite vector measures, and finiteness/no-atoms are separate verified properties. |
| Assigned transfer and transfer calculus, lines 203--249 | Exact statements; compressed proofs | `piecewiseMonotoneTransferVector_apply`, `_independent`, `_comp`, `transferMeasure`, `_noAtoms`, `_independent`, `_comp`, and `variation_transfer_eq_transfer_variation`, `PiecewiseMonotoneVariation.lean:391,481,536,796,808,856,879,1266`; assigned-cell locality is `transferMeasure_apply_of_subset_assignedCell`, `PiecewiseMonotoneEigen.lean:1200`.  Exact variation requires a branch-variation theorem and a disjoint **source-support** theorem, not just deletion of exceptional target values. |
| Weak-lap definition, lines 253--257 | Exact at a high level | The formal objects are `weakLapCountOn` and `weakLapCount` in `PiecewiseMonotoneResolvent.lean`; submultiplicativity and an exponential upper bound are `weakLapCount_submultiplicative` and `weakLapCount_exponential_upper`, lines 1502 and 1630.  These facts must be stated before a radius is introduced. |
| Weak-lap resolvent, lines 259--316 | Major mismatch and major compression | Existence of the eigenprobability is `transferMeasure_eigenprobability_exists_of_horseshoe`, `PiecewiseMonotoneResolvent.lean:4347`.  The actual chain runs through `weakLapGrowthData_exists`, `weakLapRadiusData_exists`, normalized infinite resolvents, itinerary-cell estimates, dense diagonal extraction, a continuous coordinate, and its Stieltjes measure.  The finite-truncation paragraph must be replaced.  The arbitrary eigenspace `E_lambda(T)` in the manuscript is broader than the named retained finite-dimensional result `productEigenspace_finiteDimensional`, `PiecewiseMonotoneEigen.lean:762`, which is stated for packaged returned-product data. |
| Restricted transfers and simultaneous probability, lines 318--352 | Exact conclusion; compressed proof | `productEigenspace`, `restrictedTransferP`, `restrictedTransferQ`, `productEigenspace_finiteDimensional`, and `simultaneousEigenprobability_of_productEigenprobability`, `PiecewiseMonotoneEigen.lean:264,762,1154`.  The manuscript must prove that both transfers preserve the product eigenspace, their restrictions commute and satisfy the product relation, and variation converts the complex joint eigenvector into a positive measure. |
| Distribution quotient, lines 356--402 | Exact conclusion; compressed proof | `DistributionQuotientData` and `canonicalDistributionQuotientData`, `PiecewiseMonotoneQuotient.lean:252,264`; fibre respect at lines 464 and 477; factor/intertwining/continuity/commutation at lines 558--605; affine cells and finite-piece PL at lines 909--948; plateau collapse at lines 1003 and 1014.  The local-to-global fibre proof and conversion from assigned cells to closed cells cannot be skipped. |
| Reduction to the PL core, lines 404--416 | Exact | `CommonPiecewiseLinearQuotientData`, `MinimalPiecewiseMonotoneCounterexample.commonPiecewiseLinearQuotientData_exists`, and `.false`, `PiecewiseMonotoneMain.lean:62,73,92`; the fixed-fibre theorem is `SimultaneousTransferEigenProbability.commonFixedFibre_exists`, `PiecewiseMonotoneQuotient.lean:1032`. |
| PL finiteness and respected quotients, lines 431--454 | Incomplete statement and proof | `PiecewiseLinearFinitenessPackage`, `PiecewiseLinearCore.lean:206`, contains composition, iteration, fixed-component finiteness, no-flat strict laps, descended PL maps, descended commutation, exact fixed-point descent, strict fixed-count drop, and preservation of no-common-fixed-point after quotienting a minimal core.  The four manuscript bullets do not provide enough infrastructure for normalization.  Canonical interval quotients and "respect" must be defined. |
| Least normalized counterexample, lines 456--523 | Major mismatch | The exact objects are `NormalizedPiecewiseLinearCounterexample`, `FixedCountLexLE`, and `LeastNormalizedPiecewiseLinearCounterexample`, `PiecewiseLinearCore.lean:90,105,112`.  Staged normalization is `WNormalized...`, `WRNormalized...`, `WRSNormalized...`, lines 1345, 1352, 1360, culminating in `exists_leastNormalizedPiecewiseLinearCounterexample`, line 1720.  The complexity is only `(#Fix W,#Fix R,#Fix S)`.  Selected-gap orientation is a later result, `exists_piecewiseLinearSelectedFixedGap`, line 2261; returned endpoint fixing is at lines 2431--2452; quotient exclusion is at line 4247.  These should not be folded into a one-paragraph existence proof. |
| Directed-state return, lines 527--551 | Exact aggregate conclusion; incorrect object description and proof | The formal state is a repelling `DirectedSide`: a `W`-fixed base point plus an available left/right side.  It does not record an affine cell or a phase component.  See `IsRepellingDirectedStatePLCore`, `repellingDirectedStatesPLCore_finite`, and `PermutesRepellingDirectedStatesPLCore`, `PiecewiseLinearCore.lean:2465,2492,2486`, followed by `canonicalExponent_carries_repellingState_plCore`, line 3373, and `piecewiseLinear_directedStateReturn`, line 3623.  Positivity of the affine slope requires local injectivity forced by the relation with the repelling map; it is not automatic from recurrence in a finite graph. |
| Finite arrival and LEO, lines 553--584 | Exact statement; proof largely mismatched | `HasFiniteSelectedGapCover`, `HasLocalEventualOntoPL`, and `piecewiseLinear_finiteArrivalAndLEO`, `PiecewiseLinearCore.lean:3637,3644,4871`.  Density uses phase descent (`PiecewiseLinearFiniteArrivalSupport.lean:1212,1284,1382,1474,1678`); endpoint arrival uses singleton fibres and basin closure (`PiecewiseLinearCore.lean:4463,4526,4650`); the finite cover is line 4663; terminal internality is line 4698; LEO is line 4835 and support lines 2596,2641. |

## Numbered hole list and weighted rewrite estimate

The weights measure manuscript-repair effort, not the number of Lean declarations or lines of code.  They total 100 points.

### H01. Minimal-core existence and minimality (2 points)

**Location:** lines 121--125.

The assertion about minimizing endpoints in a compact triangle is not justified: one must show the admissible endpoint set is closed in the appropriate order formulation, and ordinary minimization of two coordinates does not immediately give inclusion minimality.  Use the argument actually formalized: nonempty chains of invariant compact intervals have nonempty invariant interval intersection, then apply Zorn.

**Lean anchors:** `commonInvariantCarriers_chain_lowerBound` and `exists_minimalCommonInvariantCore`, `PiecewiseMonotoneReduction.lean:66,152`.

**Replacement:** state the chain-intersection claim explicitly, prove nonemptiness by compactness and the finite-intersection property, prove invariance pointwise, and invoke Zorn's lemma.  Zorn is a suitable standard citation, but the interval-intersection verification should remain in the paper.

### H02. Onto restriction and affine restart (2 points)

**Location:** lines 127--132.

The idea is correct, but the paper should show that `P(J)` is an interval (continuity), that it is invariant under both generators, and that restriction/rescaling preserves continuity, finite-piece weak monotonicity, commutation, absence of a common fixed point, and core minimality.

**Lean anchors:** `minimalCommonInvariantCore_mapsOnto`, `rescaledCoreMap_continuous`, `noCommonFixedPoint_rescaledCoreMaps`, `rescaledCoreMaps_coreMinimal`, and `.exists_minimalCounterexample`, `PiecewiseMonotoneReduction.lean:209,238,266,352,441`.

### H03. Closest crossing pair (4 points)

**Location:** lines 147--150.

"Choose a closest ordered pair" hides the first substantive argument.  Lean forms compact weak-sign sets inside `Fix(P)`, minimizes the gap, upgrades weak displacement to strict displacement using the no-common-fixed-point hypothesis, and proves that there is no `P`-fixed point strictly between the selected endpoints.  Commutation then sends the selected `P`-fixed points to `P`-fixed points and forces the two crossing inequalities.

**Lean anchors:** `MinimalFixedCrossingPair`, `exists_minimalFixedCrossingPair`, `.no_fixed_P_between`, `.Q_x0_ge_x1`, and `.Q_x1_le_x0`, `PiecewiseMonotoneHorseshoe.lean:320,337,419,446,458`.

**Replacement:** make this a separate lemma with the exact seven properties appearing in the formal structure.

### H04. Alternating configuration and strict branch trimming (3 points)

**Location:** lines 149--166.

One must choose the least or greatest `Q`-fixed point in the crossing gap according to the sign of `P-id`, prove `P(s)` lies strictly outside the gap, and treat the reflected order separately.  The strict horseshoe does not follow merely by saying "trim": Lean uses a preimage of an endpoint and several IVT choices to create four strictly ordered endpoints.

**Lean anchors:** `gap_moves_right`, `gap_moves_left`, `marr_configuration_of_commuting_noCommonFixedPoint`, `strict_horseshoe_of_forward_adjacent_branches`, `strict_horseshoe_of_backward_adjacent_branches`, and `commuting_noCommonFixedPoint_horseshoe`, `PiecewiseMonotoneHorseshoe.lean:476,493,588,707,807,1038`.

**Replacement:** split the current proof into (i) crossing-pair lemma, (ii) forward/backward alternating-configuration lemma, (iii) adjacent covering lemma, and (iv) strict-margin trimming lemma.

### H05. Regular target, symbolic preimages, and lap lower bound (3 points)

**Location:** lines 168--172 and 276--281.

The manuscript jumps from binary inverse itineraries to a lap lower bound.  Lean first chooses a target regular for every iterate (outside all branch plateau/frontier values), proves its iterate fibres are finite, constructs exactly `2^n` chosen preimages, and proves that a regular fibre meets a weak lap at most once.

**Lean anchors:** `exists_regular_target_in_horseshoe`, `iterateFibre_finite_of_regular`, `TwoBranchHorseshoe.symbolic_preimages`, `iterateFibre_ncard_le_weakLapCount`, and `weakLapCount_horseshoe_lower`, `PiecewiseMonotoneResolvent.lean:1905,1993,2179,2050,2290`.

**Replacement:** define "regular target" and state the fibre/lap lemma.  Do not claim finiteness of arbitrary fibres.

### H06. Plateau-safe branch image measures (3 points)

**Location:** lines 177--201.

The statement needs a measurable branch set `D` and the formula `E -> sigma(u(E intersect D))`.  For complex measures, the paper must say that `sigma` is a finite complex/vector measure.  Countable additivity requires: monotone images of Borel subsets of a branch are Borel; overlaps of images of disjoint sets lie in the countable plateau-value set; deleting that set does not change an atomless measure.

**Lean anchors:** `branchPlateauValues_countable`, `measurableSet_image_of_monotoneBranchOn`, `image_inter_image_subset_plateau`, `monotoneBranchImageVector`, `_apply`, `_noAtoms`, and `_isFinite`, `PiecewiseMonotoneTransfer.lean:88,95,103` and `PiecewiseMonotoneVariation.lean:146,210,218,369`.

**Replacement:** restate the lemma on a measurable branch `D`, and prove vector and positive versions together or explicitly explain that the same countable-additivity proof applies.

### H07. Assigned partitions and partition independence (3 points)

**Location:** lines 203--212 and item 1 of the transfer calculus.

The manuscript does not define the endpoint assignment precisely enough for later locality.  It should introduce pairwise disjoint Borel assigned cells covering the interval, distinguish them from their underlying closed cells, and prove that a finite common refinement splits every branch transfer exactly.

**Lean anchors:** `FiniteMonotonePartition`, `MonotonicityPartition.toFiniteMonotonePartition`, `monotoneBranchTransferVector_split`, and `piecewiseMonotoneTransferVector_independent`, `PiecewiseMonotoneTransfer.lean:281` and `PiecewiseMonotoneVariation.lean:408,481`.

### H08. Composition and assigned-cell locality (2 points)

**Location:** lines 220--226 and 234--238.

The order `T_{S o T}=T_T T_S` is correct, but it must be checked on the refinement by inverse images of `S`-cells, including measurability of branch images.  Item 3 should be written as a theorem: if `E` lies in assigned cell `q`, every term indexed by `r != q` is zero and the `q` term is `sigma(T(E))`.

**Lean anchors:** `piecewiseMonotoneTransferVector_comp`, `transferMeasure_comp`, and `transferMeasure_apply_of_subset_assignedCell`, `PiecewiseMonotoneVariation.lean:536,879` and `PiecewiseMonotoneEigen.lean:1200`.

### H09. Exact total variation (3 points)

**Location:** lines 227--248.

Deleting exceptional target values does not by itself prove equality of total variations after summing branches.  The needed facts are exact variation for a single monotone branch, strong support of that branch-transfer measure on its assigned **source** cell, and exact additivity of variation for a finite sum with pairwise disjoint supports.

**Lean anchors:** `variation_monotoneBranchImage`, `monotoneBranchImageVector_hasStrongSupport`, `variation_finsetSum_eq_of_disjoint_support`, `variation_piecewiseMonotoneTransferVector`, and `variation_transfer_eq_transfer_variation`, `PiecewiseMonotoneVariation.lean:1212--1276` (with the supporting lemmas immediately above).

### H10. Weak-lap growth package (3 points)

**Location:** lines 253--281.

Before discussing a critical radius, the paper must prove that the intrinsic weak-lap counts are positive, submultiplicative, exponentially bounded above, and bounded below by `2^n` under a horseshoe.

**Lean anchors:** `weakLapCount_submultiplicative`, `weakLapCount_exponential_upper`, `weakLapCount_horseshoe_lower`, and `WeakLapGrowthData`, `PiecewiseMonotoneResolvent.lean:1502,1630,2290,2315`.

**Replacement:** add a weak-lap growth lemma.  Submultiplicative lap-number estimates are standard in interval dynamics, but because weak cells and plateaus are central here, retain the proof rather than citing the strict piecewise-monotone version.

### H11. Critical radius and infinite normalized resolvents (9 points)

**Location:** lines 283--290.

This paragraph must be replaced, not expanded in place.  Define

`F_t(x,y) = sum_{k>=0} ell(T^k;[x,y]) t^k` and
`S(t) = sum_{k>=0} ell(T^k;I) t^k`.

Let `r` be the positive convergence radius.  The horseshoe bound gives `r <= 1/2`, while the exponential upper bound gives `r>0`.  Submultiplicativity plus maximality of the radius gives

`ell(T^k;I) r^k >= 1` for every `k`.

Choose exactly

`t_n = r (1 - 1/(n+2)^2)`.

Then `0<t_n<r`, `t_n` increases to `r`, every series at `t_n` converges, and the first `n` terms yield

`S(t_n) >= n/2`,

so `S(t_n) -> infinity`.  Normalize by `F_n(x,y)=F_{t_n}(x,y)/S(t_n)`.

**Lean anchors:** `weakLapResolvent`, `weakTotalLapResolvent`, `WeakLapRadiusData`, and `weakLapRadiusData_exists`, `PiecewiseMonotoneResolvent.lean:2337,2342,2348,2426`; the explicit boundary and divergence argument is lines 2518--2676; `weakNormalizedLapResolvent` is line 2691.

### H12. Adjacent and branch defect estimates (4 points)

**Location:** lines 285--291.

The paper needs the actual normalized estimates.  Adjacent additivity has a bounded boundary defect divided by `S(t_n)`.  On a weakly monotone branch, the local series differs from `t_n` times the image-interval series by a bounded endpoint/degree-zero defect, again divided by `S(t_n)`.  State the inequalities before taking limits and explain why `t_n <= r <= 1/2` controls the geometric denominators.

**Lean anchors:** `weakNormalizedLapResolvent_adjacent_error`, `weakNormalizedLapResolvent_adjacent_tendsto_zero`, `weakNormalizedLapResolvent_branch_error`, and `weakNormalizedLapResolvent_branch_tendsto_zero`, `PiecewiseMonotoneResolvent.lean:2759,2825,2854,2980`.

### H13. Itinerary-cell smallness and diagonal extraction (5 points)

**Location:** lines 290--297.

"Compactness of normalized interval-length functions" is too vague and is not the formal argument.  For a depth-`m` weak itinerary cell, Lean proves

`F_n(u,v) <= m/S(t_n) + t_n^m`.

This gives two-sided eventual smallness around every point.  One then extracts a subsequence on a countable dense set and extends convergence to all endpoints using monotonicity plus the two-sided estimate.  Adjacent-error convergence supplies local interval limits.

**Lean anchors:** `weakNormalizedLapResolvent_le_pow_of_weakItineraryCell`, `weakNormalizedLapResolvent_twoSided_eventually_small`, `WeakLapCumulativeLimitData`, `weakLapCumulativeLimitData_exists`, `WeakLapLimitData`, and `weakLapLimitData_exists`, `PiecewiseMonotoneResolvent.lean:3147,3259,3344,3356,3496`.

### H14. Limit coordinate, Stieltjes probability, and eigenidentity (4 points)

**Location:** lines 291--301.

The paper must establish exact adjacent additivity, branch scaling, endpoint normalization, continuity from the two-sided estimate, monotonicity, and surjectivity before introducing the Stieltjes measure.  It then needs the interval-mass formula and a monotone-class/measure-extensionality argument taking branch scaling to the full transfer identity.

**Lean anchors:** `weakLapLimit_adjacent`, `weakLapLimit_scaling`, `weakLapResolventCoordinateData_exists`, `ExpandingCompatibleCoordinate`, `expandingCompatibleCoordinate_of_horseshoe`, `compatibleCoordinate_stieltjes_probability`, `compatibleCoordinate_transferMeasure_eigen`, and `transferMeasure_eigenprobability_exists_of_horseshoe`, `PiecewiseMonotoneResolvent.lean:3591,3616,3737,3973,4000,4028,4090,4347`.

**Suitable standard citation:** the Lebesgue--Stieltjes correspondence between continuous nondecreasing distribution functions and atomless finite Borel measures.  The manuscript should still record the normalization and interval-mass convention used here.

### H15. Finite-dimensionality statement mismatch (3 points)

**Location:** lines 266--272 and 303--315.

The displayed arbitrary space `E_lambda(T)` is not the type of the public Lean theorem cited by the correspondence document.  Lean proves finite-dimensionality for `productEigenspace D`, where `D : PiecewiseMonotoneProductEigenData P Q L` includes the returned product, its finite-piece partition, `lambda>1`, and a positive product eigenprobability.

**Lean anchors:** `productEigenspace`, `ExpandingIterateData`, `cumulativeNormSup_contraction`, `cumulativeEndpointCoordinate_injective`, and `productEigenspace_finiteDimensional`, `PiecewiseMonotoneEigen.lean:264,393,543,728,762`.

**Replacement options:** either (preferred) state only the specialized product-eigenspace lemma in the paper, exactly where it is needed, or add and formalize a genuinely general arbitrary-`T` theorem.  For alignment without new Lean work, use the specialized statement.  The coordinate contraction `2/lambda^N<1` and the fact that cumulative interval values determine an atomless complex measure must be explicit.

### H16. Restricted transfers and a common eigenvector (3 points)

**Location:** lines 318--351.

Before writing `A` and `B`, prove that transfer by each generator preserves the product eigenspace, that the restrictions commute, and that their product has the stated scalar action.  Then a nonzero eigenvector for one restriction is automatically a joint eigenvector because the product scalar is nonzero.  Finally use exact variation naturality and normalize the variation measure.

**Lean anchors:** `transferP_preserves_productEigenspace`, `transferQ_preserves_productEigenspace`, `restrictedTransfers_commute`, `restrictedTransfers_jointEigenvector`, `jointEigenvector_variation`, and `simultaneousEigenprobability_of_productEigenprobability`, `PiecewiseMonotoneEigen.lean:776--1154`.

**Suitable standard citation:** existence of an eigenvalue for an endomorphism of a nonzero finite-dimensional complex vector space (equivalently, the fundamental theorem of algebra).  The invariant-subspace and variation arguments are bespoke and should be proved.

### H17. CDF interval mass and global fibre respect (4 points)

**Location:** lines 356--390.

The coordinate must be accompanied by the exact formula

`mu([x,y]) = theta(y)-theta(x)` for `x<=y`.

To pass from `theta(x)=theta(y)` to `theta(Tx)=theta(Ty)`, Lean first transfers image-scaling from an assigned half-open cell to its underlying closed cell by deleting one endpoint, then covers `[x,y]` by finitely many closed cells, proves every image piece null, and uses the IVT to show that the whole interval between `Tx` and `Ty` is null.

**Lean anchors:** `DistributionQuotientData.interval_mass`, `measure_image_eq_of_transferEigen_on_closedCell`, `coordinate_image_eq_of_coordinate_eq_global`, `.respectsFibres_P`, and `.respectsFibres_Q`, `PiecewiseMonotoneQuotient.lean:252,280,404,464,477`.

### H18. Continuous affine factors and the final reduction (3 points)

**Location:** lines 364--415.

The continuity of the choice-defined descent uses the theorem that a continuous surjection from compact to Hausdorff is a quotient map.  Affineness requires deleting duplicate coordinate images of partition vertices, selecting a preimage in each coordinate cell, and treating increasing and decreasing source cells separately.  Positivity of `C,D` is needed to identify absolute slopes and collapse constant branches.

**Lean anchors:** `coordinateDescent_continuous`, `coordinateDescents_commute`, `RealPartition.coordinateImage`, `factor_affineOn_coordinateImage_cell`, `.factorP_affineOn_cell`, `.factorQ_affineOn_cell`, `.finitePiecePL_factorP`, `.finitePiecePL_factorQ`, and `.commonFixedFibre_exists`, `PiecewiseMonotoneQuotient.lean:511--603,611,702,909--948,1032`.

**Suitable standard citation:** the compact-to-Hausdorff quotient-map theorem.  The affine-slope calculation and fixed-fibre lift should remain self-contained.

### H19. Canonical finite PL quotient infrastructure (5 points)

**Location:** lines 422--454.

The current lemma is not strong enough to support the next paragraph.  The paper must define a canonical monotone quotient collapsing a finite pairwise-disjoint family of nondegenerate closed intervals; define when a map respects quotient fibres; construct the unique descended map; and prove:

1. composition and iteration preserve finite-piece PL;
2. fixed sets of PL maps are finite unions of closed intervals;
3. a respected quotient has PL descended maps and preserves commutation;
4. collapsing exactly the nondegenerate fixed components gives exact fixed-point descent;
5. identifying two points of a finite fixed set strictly drops its cardinality downstairs;
6. after quotienting a minimal counterexample, absence of a common fixed point is preserved, and re-minimalization/affine rescaling does not increase already finite positive-word fixed counts.

**Lean anchors:** `PiecewiseLinearFinitenessPackage`, `finitePiecePL_comp`, `finitePiecePL_iterate`, `finitePiecePL_fixedPoints_finiteUnion`, `finitePiecePL_descendedMap`, `commute_descendedMap`, `noCommonFixedPoint_descendedMap_of_minimalCore`, and `piecewiseLinear_finitenessPackage`, `PiecewiseLinearCore.lean:206,263,287,307,564,806,884,971`; quotient-component support is in `PiecewiseLinearQuotientSupport.lean:1152--1462`.

### H20. Three-stage `W,R,S` normalization (8 points)

**Location:** lines 456--490 and 507--516.

Delete "chosen positive word," "finite phase components," and the undefined "finite quotient complexity."  The exact normalization is:

`W=(P o Q)^2`,

`L=2(2 #Fix(W))!`,

`A=P^L`, `B=Q^L`, `R=A o B`, `S=R^2`.

First collapse nondegenerate fixed components of `W` and re-minimize.  Among all resulting systems minimize `#Fix(W)`.  Next perform the same positive-word fixed-component descent for `R`; minimality of `#Fix(W)` forces its count to remain equal.  Minimize `#Fix(R)`.  Repeat for `S`, and finally choose a lexicographically least normalized system by the triple `(#Fix(W),#Fix(R),#Fix(S))`.

The core descent theorem also proves that all previously finite positive-word fixed counts do not increase; this is why the stages are compatible.

**Lean anchors:** `exists_positiveWordFixedSetFiniteDescent_plCore`, `WNormalizedPiecewiseLinearCounterexample`, `WRNormalizedPiecewiseLinearCounterexample`, `WRSNormalizedPiecewiseLinearCounterexample`, `exists_WNormalizedPiecewiseLinearCounterexample`, `exists_WRNormalizedPiecewiseLinearCounterexample`, `exists_WRSNormalizedPiecewiseLinearCounterexample`, `exists_lexLeastNormalizedPiecewiseLinearCounterexample`, and `exists_leastNormalizedPiecewiseLinearCounterexample`, `PiecewiseLinearCore.lean:1198,1345,1352,1360,1498,1520,1543,1666,1720`.

### H21. Selected fixed gap, reflection, and returned endpoints (3 points)

**Location:** lines 491--500 and 513--517.

Finiteness and nontriviality of `Fix(W)` yield consecutive fixed points with constant sign of `W-id`.  If the sign is leftward, the entire least normalized system is reflected by `x -> 1-x`; this requires checking preservation of normalization and recording that a common fixed point in the reflected system pulls back.  Endpoint fixing by `A` and `B` is a separate finite-permutation argument on `Fix(W)`.

**Lean anchors:** `PiecewiseLinearUnorientedFixedGap`, `exists_piecewiseLinearUnorientedFixedGap`, `piecewiseLinear_orientFixedGap`, `PiecewiseLinearSelectedFixedGap`, and `exists_piecewiseLinearSelectedFixedGap`, `PiecewiseLinearCore.lean:1789,1803,2192,1740,2261`; endpoint return is `canonicalFactorial_return_fixedPoint_plCore` and the four public endpoint lemmas, lines 2335,2431--2452.

**Suitable standard citation:** a permutation of an `m`-element set has order dividing `m!`.  The proof must still explain why `P` and `Q` permute `Fix(W)`.

### H22. Exclusion of quotients identifying `S`-fixed points (5 points)

**Location:** lines 501--503 and 518--522.

The written proof is wrong as a description of the formal argument.  From a canonical quotient respected by `P,Q`, Lean constructs descended maps and re-minimalizes.  Exact fixed-point descent gives

`Fix(W_bar)=pi(Fix(W))`, `Fix(R_bar)=pi(Fix(R))`, and `Fix(S_bar)=pi(Fix(S))`.

Thus the first two counts do not increase and the third strictly drops.  If the `W` count strictly drops, normalize the descended counterexample again and contradict minimality of the first lexicographic coordinate.  If the `W` count is equal, the canonical exponent remains the same; then the `R` count is nonincreasing and the `S` count is strictly smaller, contradicting lexicographic minimality directly.

**Lean anchor:** `leastNormalizedPiecewiseLinear_no_respectedQuotient_identifying_S_fixedPoints_b5Prototype`, `PiecewiseLinearCore.lean:4247--4424`.

### H23. Repelling directed sides and positive affine germs (5 points)

**Location:** lines 527--550.

Replace the manuscript definition of directed state.  A state is a `DirectedSide`: a base point and an available left/right side.  It is repelling for `W` if the base is `W`-fixed and, on a one-sided neighbourhood, `W` stays on that side and moves points away.  There are at most two such states per point of `Fix(W)`, hence at most `2 #Fix(W)`.

Commutation/factorization shows that each generator permutes the repelling states.  The nontrivial step is that if `H o F = W` and `W` is locally strictly increasing on a repelling side, then `F` is locally injective; on a PL cell it is therefore strictly monotone and carries the side to a repelling side.  This rules out slope zero.  The factorial exponent returns the selected right side.  Once a PL map fixes `p` and carries the right side to itself, its local affine slope is strictly positive, producing a literal `C^{1+BV}` germ with zero log-derivative variation.

**Lean anchors:** `IsRepellingDirectedStatePLCore`, `repellingDirectedStatesPLCore_finite`, `repelling_right_local_strictMono_plCore`, `factor_maps_repellingRightState_plCore`, `factor_permutes_repellingDirectedStates_plCore`, `piecewiseLinear_generators_permute_repellingStates`, `canonicalExponent_carries_repellingState_plCore`, `finitePiecePL_rightGermC1BV_of_carries_right`, and `piecewiseLinear_directedStateReturn`, `PiecewiseLinearCore.lean:2465,2492,2548,2610,3193,3238,3373,3497,3623`.

### H24. Phase graph and dense diagonal range (4 points)

**Location:** lines 565--569.

Define labels `PhaseLabel L = ZMod L x ZMod L` and labelled phase intervals

`P^i(Q^j(C))`, `0<=i,j<L`.

When `P^L(C)=C=Q^L(C)`, translations in the two label coordinates are graph automorphisms, so the finite intersection graph is vertex-transitive.  Apply this to the compact interval closure of the increasing diagonal range.  If the graph is connected, vertex transitivity for an interval-intersection graph forces completeness; pairwise-intersecting compact intervals have a common point (one-dimensional Helly), and the phase core gives a nonempty common invariant interval, so minimality forces the range to be all of `I`.  If the graph is disconnected, unions of graph components are disjoint nondegenerate intervals; collapsing them gives a respected quotient identifying two fixed points of `S`, forbidden by H22.

**Lean anchors:** `PhaseLabel`, `labelledPhaseInterval`, `phaseTranslation_graphAutomorphism`, `phaseLabel_graph_vertexTransitive`, `connected_vertexTransitive_intervalGraph_complete_and_Helly`, `periodicInterval_eq_univ_of_connectedPhaseGraph_and_minimalCore`, `disconnectedPhaseGraph_gives_respectedQuotient`, `diagonalRange_iterates_eq_univ_of_phase_descent`, and `diagonalIterates_dense_of_phase_descent`, `PiecewiseLinearFiniteArrivalSupport.lean:259,262,1145,1212,1284,1382,1474,1627,1678`; the public wrapper is `piecewiseLinear_diagonalSelectedGap_dense`, `PiecewiseLinearCore.lean:4429`.

**Suitable standard citation:** Helly's theorem in dimension one, in the elementary form that finitely many compact intervals with pairwise nonempty intersections have nonempty total intersection.  The graph-transitivity-to-completeness argument is special and should be proved.

### H25. Missing endpoint, singleton fibre, and attracting basin (3 points)

**Location:** lines 571--576.

Replace the singleton/interval terminal-fibre split.  If a dense increasing sequence of diagonal intervals never contains an ambient endpoint `e`, onto-ness and density imply that `S=R^2` fixes `e` and `S^{-1}(e)={e}`.  A sequence approaches `e` from the interior.  Finite-piece PL structure and the singleton fibre give local endpoint monotonicity and a proper nondegenerate immediate attracting-basin closure `E`.  The returned powers `A,B` fix `e` and map `E` onto itself.  Phase descent applied to `E` yields either a proper common invariant interval or a quotient forbidden by H22.

**Lean anchors:** `endpoint_singletonFibre_of_neverArrives`, `PiecewiseLinearFiniteArrivalSupport.lean:1771`; `endpointApproachSequence_of_neverArrives`, `local_endpoint_monotonicity_and_basinClosure`, and `canonical_powers_map_endpointBasinClosure_onto`, `PiecewiseLinearEndpointBasinSupport.lean:263,928,1037`; public assembly is `piecewiseLinear_asymptoticEndpoint_singletonFibre`, `_basin_contradiction`, and `_ambientEndpoints_arrive`, `PiecewiseLinearCore.lean:4463,4526,4650`.

### H26. From endpoint arrival to a finite cover and an internal terminal gap (2 points)

**Location:** lines 577--578.

The diagonal images form an increasing sequence of compact intervals.  Take the maximum of the two finite endpoint-arrival times; that image contains both endpoints and hence is all of `I`.  A separate argument is required to prove `c<1`: if `p>0`, the global rightward motion of `R=W^d` prevents any iterate of `[p,c]` from reaching `0`; if `[p,c]=I`, generator actions on fixed points and repelling directed sides force a common fixed endpoint.

**Lean anchors:** `finiteDiagonalCover_of_endpointArrival` and `terminalGap_internal_of_finiteReturnCover`, `PiecewiseLinearFiniteArrivalSupport.lean:2500,2528`; public wrappers `piecewiseLinear_finiteSelectedGapCover_of_endpointArrival` and `piecewiseLinear_selectedTerminalGap_internal`, `PiecewiseLinearCore.lean:4663,4698`.

### H27. Anchored LEO (2 points)

**Location:** lines 580--583.

Do not invoke only the positive right germ.  Given `p<q` and a threshold `r<c`, if no iterate `W^j(q)` reaches `r`, the orbit is strictly increasing and bounded above; its limit is a `W`-fixed point in `(p,c)`, contradicting consecutiveness.  By the IVT, `W^j([p,q])` then contains `[p,r]`.  Choose interior preimages `x_L,x_R<c` of the ambient endpoints under the finite covering map `R^N`, take `r=max(x_L,x_R)`, and use `R=W^d` to conclude that a power of `W` maps `[p,q]` onto `I`.

**Lean anchors:** `iterate_reaches_threshold_in_repelling_gap` and `localEventualOnto_of_finiteReturnCover`, `PiecewiseLinearFiniteArrivalSupport.lean:2596,2641`; `piecewiseLinear_localEventualOnto_of_finiteArrival` and `piecewiseLinear_finiteArrivalAndLEO`, `PiecewiseLinearCore.lean:4835,4871`.

## Reusable-source audit: `common_fixed_points_piecewise_monotone_direct.tex`

The direct draft contains substantially fuller mathematics than the present formal-proof-aligned manuscript.  It is therefore the best source for repairing the prose, but it is not safe to copy wholesale.  The classification below gives the exact editorial treatment required.

### A. Material that can be restored with only notation and presentation edits

1. **Minimal core and onto-ness (direct draft, lines 134--147).**  The chain-intersection/Zorn argument and the proof that each commuting map carries the minimal interval onto itself agree with `exists_minimalCommonInvariantCore` and `minimalCommonInvariantCore_mapsOnto`.
2. **Canonical interval quotients and fixed-point descent (lines 149--222).**  The quotient construction, descended commuting maps, exact fixed-point image formula, strict cardinality drop when two fixed points are identified, and lifting from a fixed-component quotient are the mathematical content of the formal quotient package.  Keep all hypotheses explicit: the quotient fibres are compact intervals, every map respects them, and exact fixed-point descent uses the interval fixed-point theorem inside an invariant fibre.
3. **Canonical normalization data (lines 232--264).**  The definitions
   `W=(P\circ Q)^2`, `L=2(2|Fix(W)|)!`, `A=P^L`, `B=Q^L`, `R=W^{L/2}`, and `S=W^L`
   agree with the retained formalization.
4. **Selected gap and repelling-side definitions (lines 317--335).**  Consecutive `W`-fixed endpoints, rightward motion on the gap, and the fixed-base/available-side definition are the correct mathematical objects.
5. **Finite phase labels and interval-intersection graph (lines 391--405).**  The `Z/LZ x Z/LZ` labels, translations, graph automorphisms, vertex transitivity, and one-dimensional Helly argument are reusable.
6. **Minimal-core reduction in the general piecewise-monotone part (lines 2375--2413), plateau-safe branch measures and transfer composition (lines 2415--2519), and the distribution-function quotient (lines 2697--2817).**  These are substantially closer to the formal declarations than the corresponding compressed passages in the current manuscript, subject to the technical qualifications in C below.

### B. Material that should be restored only after correction to match the retained proof

1. **Normalization (lines 281--302).**  Do not describe an informal indefinite restart algorithm.  Present three finite minimizations: first minimize `|Fix(W)|`; among those systems minimize `|Fix(R)|`; among those minimize `|Fix(S)|`; finally choose the lexicographically least triple.  In the later quotient contradiction, if the first count drops, re-normalize the quotient and contradict the first stage.  If it does not drop, `L` is unchanged, `|Fix(R)|` cannot increase, and `|Fix(S)|` strictly drops.  These are the exact cases used formally.
2. **Return of a directed state (lines 347--358).**  Replace the derivative/chain-rule shortcut.  If `H\circ F=W` and `W` is locally strictly increasing on the repelling side, then `F` is locally injective.  On a sufficiently small PL cell it is consequently strictly monotone and maps the directed side to another repelling side, so its affine slope is nonzero.  The action on at most `2|Fix(W)|` directed states is a permutation; the factorial in `L` returns the state itself.  The extra factor `2` is not an unexplained device for removing orientation reversal.
3. **Density (lines 407--439).**  Remove the auxiliary argument through a connected union `F` and an asserted drop in `|Fix(W)|`.  Apply the connected/disconnected graph dichotomy directly to the closure of the increasing diagonal range.  Connected gives completeness, Helly, a nonempty phase core, and hence the full interval by minimality.  Disconnected gives a respected interval quotient identifying two distinct `S`-fixed points, contradicting normalized minimality.
4. **A missing endpoint (lines 450--561).**  Keep the substantial basin argument, but order it as in the formal proof: failure of arrival implies that the endpoint is `S`-fixed with singleton `S`-fibre; obtain an interior approach sequence; finite-piece PL structure gives a proper immediate-basin closure; `A` and `B` fix the endpoint and map that closure onto itself; phase descent of this interval yields either a forbidden proper common invariant interval or a forbidden quotient.  Delete any terminal-fibre dichotomy saying the fibre may instead be a nondegenerate interval.
5. **Internality of the terminal gap (lines 563--580).**  For `p>0`, use the direct order argument: `R=W^{L/2}` and `W(x)>x` on `(p,c)` imply that returned iterates cannot send `[p,c]` to the left endpoint.  Only the `p=0,c=1` case needs the endpoint-action/repelling-state contradiction.  The draft's second basin/phase-descent argument is unnecessary.
6. **LEO (lines 600--624).**  Choose interior preimages `x_L,x_R<c` of the two ambient endpoints under the finite covering iterate of `R`, put `r=max(x_L,x_R)`, and prove that some `W^j(q)` reaches `r`.  Otherwise the increasing bounded orbit converges to a forbidden `W`-fixed point inside the selected gap.  The IVT gives `[p,r]\subseteq W^j([p,q])`, after which the `R`-iterate covers the full interval.  This is both shorter and exactly formalized.

### C. Technical qualifications in the later reduction

1. **Branch-image measurability (around line 2428).**  State the branch domain `D` and define the branch image measure by `E \mapsto \sigma(u(E\cap D))`.  Supply the monotone-image measurability argument, including removal of the countable plateau-value set.  Do not simply assert that every continuous image of a Borel set is Borel.
2. **Single-lap locality (lines 2481--2484).**  The scaling formula is applied on an *assigned cell* of a fixed finite partition, including a consistent endpoint convention.  “Contained in a monotonicity piece” is not enough to justify the additive transfer decomposition at shared endpoints.
3. **Finite-dimensional eigenspace (lines 2539--2610).**  The direct draft proves a general real signed-measure statement, whereas the retained Lean theorem packages the specialized complex `productEigenspace` attached to the chosen finite partition.  Either add a formal wrapper for the broader statement or state the specialized result in the paper and map it honestly in the correspondence table.
4. **Brouwer construction of a simultaneous probability (lines 2612--2695).**  This is not the retained proof and its continuity argument is incomplete.  An algebraic finite-dimensional subspace does not by itself make every set-evaluation functional continuous in the topology needed for the compact slice; continuity of normalization and of the transfer actions must also be proved.  Prefer the formal route: obtain a common complex eigenvector in the finite-dimensional product eigenspace, then pass to normalized total variation using the exact variation identity.  If the Brouwer route is retained, the topology must be explicitly transported through the finite coordinate embedding and every evaluation/transfer/normalization map used must be proved continuous.

### D. Published-theorem substitutions

The Alsedà--Misiurewicz constant-slope semiconjugacy is a credible journal-facing replacement for the long weak-resolvent construction once positive entropy has been established.  The primary preprint supports the precise two-step use needed here: its Lemma 3.1 supplies an increasing compatible semiconjugacy for a positive-entropy piecewise-monotone map, and Lemma 4.2 converts a compatible scaling functional into the constant-slope factor and explicitly proves the branch scaling identity.  The final manuscript should cite the exact lemmas rather than paraphrase only the article's headline theorem.

The claimed Bogatyi--Frolkina entropy theorem should **not yet be used as a black box**.  The cited title, *A common fixed point of commuting mappings of a tree*, has not yet been checked in primary text for the exact assertion that the required composition has positive entropy under precisely these hypotheses.  A title or secondary snippet is insufficient evidence for that substitution.

The safest shortened architecture is therefore:

1. retain the already formalized closest-crossing-pair/two-branch-horseshoe lemma;
2. invoke the standard theorem that a two-branch interval horseshoe gives entropy at least `log 2` (with an exact source);
3. invoke the exact Alsedà--Misiurewicz lemmas to obtain the compatible constant-slope coordinate;
4. continue with plateau-safe transfer, the simultaneous conformal probability, and the distribution quotient.

This hybrid removes the bespoke weak-lap resolvent from the paper while keeping the crucial positive-entropy input under direct mathematical control.  If proof alignment is intended to mean identity of proof dependencies rather than merely identity of statements and mathematical interfaces, retain the resolvent instead.  In either case the correspondence document must say explicitly which published theorem replaces which formal declarations (in particular the block from the weak-lap radius data through `weakLapExpandingCompatibleCoordinate`).

## Dependency-ordered replacement architecture

The rewrite should follow this order.  This order makes every mathematical dependency available before it is invoked and closely mirrors the proved dependency graph without mentioning Lean in the paper itself.

1. **Basic class and core reduction.**  State finite-piece weak monotonicity, the two fixed-point theorems, the chain-intersection/Zorn minimal-core lemma, onto-ness, and the affine restart.
2. **Direct horseshoe.**  Introduce the closest crossing pair, no-fixed-point gap, forward/backward alternating configurations, adjacent cover, strict-margin trimming, regular targets, symbolic inverse sets, and the weak-lap lower bound.
3. **Plateau-safe transfer.**  Define plateau values on a measurable monotone branch, prove branch image measures, define assigned cells, prove splitting/independence, composition, locality, and exact variation.
4. **Weak-lap resolvent.**  Prove the growth package; define the two infinite series; construct the critical radius and the explicit sequence `t_n`; prove `S(t_n)>=n/2`; prove adjacent/branch errors; prove the itinerary-cell bound and two-sided smallness; perform dense diagonal extraction; construct the additive continuous coordinate; pass to the Stieltjes probability and prove the transfer eigenidentity.
5. **Joint conformal probability.**  Package the product eigenspace, prove its finite dimensionality in the exact specialized form, restrict the generator transfers, obtain a common complex eigenvector, and pass to normalized total variation.
6. **Distribution quotient and reduction.**  Prove the CDF interval-mass formula, closed-cell scaling, global fibre respect, continuous descended factors, exact affine slopes, plateau collapse, the PL property, and the common-fixed-fibre contradiction.
7. **PL quotient toolkit.**  Define canonical finite interval quotients and respect; prove the complete finiteness/exact-descent/cardinality-drop package needed for every restart.
8. **Canonical normalization.**  Define `W,L,A,B,R,S`; perform the `W`, then `R`, then `S` fixed-component descents; choose the lexicographically least count triple; select and orient a consecutive `W`-fixed gap; prove returned endpoint fixing.
9. **Least-count obstruction and directed return.**  Prove that no respected quotient identifies distinct `S`-fixed points.  Define repelling directed sides, prove generator permutation and the `2 #Fix(W)` bound, return the selected right side, and derive positive affine `C^{1+BV}` germs.
10. **Finite arrival.**  Define the finite phase-labelled interval graph.  Prove translation vertex transitivity, the connected Helly/minimal-core case, the disconnected quotient case, and density.  Prove the missing-endpoint singleton-fibre theorem, construct the basin closure, phase-descend it, and obtain finite arrival of both endpoints and a finite returned cover.
11. **Anchored LEO.**  Prove the selected terminal endpoint is internal, prove the orbit-threshold lemma on the whole fixed gap, and combine it with `R=W^d` and the finite cover.

## Citation guidance

The following uses of established results are suitable for citation while retaining the problem-specific arguments in the paper:

- Zorn's lemma for existence of a minimal invariant interval after proving the chain-intersection hypothesis.
- The intermediate value theorem and compactness of closed subsets of the interval; no specialized citation is needed.
- The compact-to-Hausdorff quotient-map theorem for continuity of descended maps.
- The Lebesgue--Stieltjes measure construction for a continuous nondecreasing distribution function.
- Existence of eigenvalues over `C` for finite-dimensional endomorphisms.
- The order of a permutation of an `m`-element set divides `m!`.
- Helly's theorem in dimension one for a finite family of compact intervals.

The horseshoe geometry, plateau-safe transfer calculus, weak-lap boundary estimates, lexicographic quotient descent, repelling-side transport, phase graph dichotomy, endpoint singleton-fibre/basin argument, and anchored LEO threshold argument are bespoke.  They should be proved in the manuscript rather than replaced by generic citations.

## Completion criterion for the early rewrite

This part of the manuscript is aligned with the formal proof only when all 27 holes above are resolved, the finite-truncation resolvent paragraph has been removed, the normalization complexity and directed states have their exact definitions, and the phase/endpoint/LEO arguments follow the proved connected-disconnected, singleton-fibre-basin, and threshold-cover routes.  Merely adding references to the correspondence document would not repair the mathematical paper; the paper must contain the mathematical statements and proofs themselves.
