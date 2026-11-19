# Common periodic points of commuting interval maps

Import `CommutingIntervalSimplified.CommonPeriodicPoints` for the new return-spectrum and common-cycle theorems. Import `CommutingIntervalSimplified` for the finite-piece fixed-point theorem as well. The signed-measure formulation of Lemma 5.1 is in `CommutingInterval.Eigenmeasure`. The numbering below follows the supplied manuscript, including Definition 3.2.

The interval type is `I = Set.Icc (0 : ℝ) 1`. In Lean the return spectrum is a set of natural numbers, with positivity in its membership condition. Thus a finite input `D : Finset ℕ` comes with `∀ d ∈ D, 0 < d`. The empty set satisfies this hypothesis.

## Main results

| Manuscript | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1, prescribed returns | `exists_commuting_maps_prescribed_returns`, `exists_commuting_maps_disjoint_periodicPts` in [CommonReturnRealization](CommutingIntervalSimplified/CommonReturnRealization.lean) | Equality with the set of *all* positive multiples of the chosen periods, and existence of a pair with disjoint periodic-point sets. The nonempty case uses finite cycles. The empty case lifts a fixed exponent through arbitrarily high grades. |
| Theorem 1.2, exchanged intervals | `inverseCommonCycle_of_exchangedOmegaIntervals` in [OmegaCycle](CommutingIntervalSimplified/OmegaCycle.lean) | The finite orbit lies in the fixed set of the composition. Its cyclic ordering records how each generator moves every point, including the wrap-around. |
| Theorem 1.2, zero entropy | `inverseCommonCycle_of_zero_entropy` in [EntropyCycleMain](CommutingIntervalSimplified/EntropyCycleMain.lean) | Either generator may have zero topological entropy. The proof uses Mathlib’s Bowen–Dinaburg topological entropy and a horseshoe obstruction. |
| Theorem 1.3, finite pieces | `finitePieceMonotone_common_fixed_point_simplified` in [Main](CommutingIntervalSimplified/Main.lean) | The pre-existing theorem allows weak monotonicity, including constant branches, and ordinary commutation. |

## The return-spectrum constructions

Section 2 has no separately numbered lemma. [ReturnSpectrum](CommutingIntervalSimplified/ReturnSpectrum.lean) constructs a permutation of alternating cells and identifies its positive return times. [FiniteReturnConstructionGeometry](CommutingIntervalSimplified/FiniteReturnConstructionGeometry.lean) provides the affine sections and matching endpoint decoders. [FiniteReturnConstruction](CommutingIntervalSimplified/FiniteReturnConstruction.lean) solves the continuous recursion. [FiniteReturnRealization](CommutingIntervalSimplified/FiniteReturnRealization.lean) proves the nonempty case.

| Manuscript | Lean declaration or module |
| --- | --- |
| Lemma 3.1, decoder marks | `GradedMarkedCells.beta_projection` in [GradedMarkedCells](CommutingIntervalSimplified/GradedMarkedCells.lean) supplies the integer shift used by `ConcreteProjection.chartMatch` in [GradedConcreteMatch](CommutingIntervalSimplified/GradedConcreteMatch.lean). The side of the shoulder fixes the required core-end value in both charts. |
| Definition 3.2, admissible projections | `DecoderProjection.GridAdmissible` prescribes vertex values and images on the unfolded grid. [GradedChartAdmissibility](CommutingIntervalSimplified/GradedChartAdmissibility.lean) and [GradedChartTransfer](CommutingIntervalSimplified/GradedChartTransfer.lean) connect the grid to the physical thirds of each cell. |
| Lemma 3.3, canonical unfolding | `unfoldMap_unique`, `continuous_unfoldMap`, `unfoldMap_translate`, `unfoldMap_sup_distance`, and `GridAdmissible.unfoldMap_comp` in [DecoderProjection](CommutingIntervalSimplified/DecoderProjection.lean). |
| Lemma 3.4, shoulder descent | `ShoulderMatch` and its endpoint, decoder and composition laws in [DecoderProjectionShoulder](CommutingIntervalSimplified/DecoderProjectionShoulder.lean). [DecoderProjectionChart](CommutingIntervalSimplified/DecoderProjectionChart.lean) combines these with the core. The physical bound uses the chart distance formula in [GradedCellGeometry](CommutingIntervalSimplified/GradedCellGeometry.lean). |
| Proposition 3.5, compatible projections | The uniform contraction in [GradedProjectionFamily](CommutingIntervalSimplified/GradedProjectionFamily.lean) produces the concrete `projection` in [GradedPhysicalProjections](CommutingIntervalSimplified/GradedPhysicalProjections.lean). The section and decoder laws are in [GradedProjectionRealization](CommutingIntervalSimplified/GradedProjectionRealization.lean). Uniqueness of the two composite chart solutions gives `projection_square` in [GradedProjectionSquare](CommutingIntervalSimplified/GradedProjectionSquare.lean). |
| Proposition 3.6, graded decoders | `Pieces.exists_family` in [GradedDecoders](CommutingIntervalSimplified/GradedDecoders.lean) applied to the concrete `GradedMarkedCells.pieces`. `Branches.decoder_square` and `Branches.intertwine` prove graded decoder commutation and intertwining along the two elementary directions. [GradedDiagonal](CommutingIntervalSimplified/GradedDiagonal.lean) supplies the diagonal direction. |
| Corollary 3.7, same-grade maps | `Squares.map_commute`, `Squares.decoder_semiconj` in [GradedReturn](CommutingIntervalSimplified/GradedReturn.lean), together with the successor-core image in [GradedReturnBranches](CommutingIntervalSimplified/GradedReturnBranches.lean) and the explicit topological-interior inclusion `opposite_maps_successor_interior` in [GradedDiagonal](CommutingIntervalSimplified/GradedDiagonal.lean). |

## The finite-piece proof in Section 5

The repository already contained proofs for this section. The additions for Lemmas 5.1 and 5.10 give the signed-measure formulation with its original-partition dimension bound and preserve the numerical degrees of the affine lifts, respectively. The [earlier correspondence](CommutingIntervalSimplified/MANUSCRIPT_CORRESPONDENCE.md) gives a more detailed account of the fixed-point development.

| Manuscript | Lean result and scope |
| --- | --- |
| Lemma 5.1, finite-dimensional eigenmeasures | The new `CommutingInterval.Eigenmeasure.finite_eigenmeasure_space` in [Eigenmeasure](CommutingInterval/Eigenmeasure.lean) treats actual finite nonatomic signed measures. Its probability set is compact in the topology induced by the cumulative function with the uniform norm. The hypothesis giving a positive normalized coordinate is the input from the preceding paragraph of the paper. The strengthened `branchEigenspace_finrank_le_partition_card` in [BranchLength](CommutingIntervalSimplified/BranchLength.lean) bounds the dimension using the original partition vertices. |
| Proposition 5.2, simultaneous reduction | `common_constantSlope_factor_exists` in [Reduction](CommutingIntervalSimplified/Reduction.lean), with the minimal core from [MinimalCore](CommutingIntervalSimplified/MinimalCore.lean). The source of the surjective monotone factor is the normalized minimal invariant interval specified in the manuscript. |
| Lemma 5.3, fixed points of a factor | `fixedPoints_descendExactly_of_monotone_semiconjugacy` in [FactorBase](CommutingIntervalSimplified/FactorBase.lean) gives equality of the two sets. |
| Lemma 5.4, no common return interval | `exists_extremal_normalized_counterexample` in [Extremal](CommutingIntervalSimplified/Extremal.lean) yields `ReturnedPowersIrreducible` for the extremal choice of factors and return powers. |
| Lemma 5.5, independent slopes | `returnedScales_multiplicativelyIndependent` in [Fold](CommutingIntervalSimplified/Fold.lean). |
| Lemma 5.6, critical values | `criticalValues_comp_exact` in [Postcritical](CommutingIntervalSimplified/Postcritical.lean). Only the inner map needs to be onto. The formal critical domain includes endpoints. |
| Lemma 5.7, finite joint critical orbit | `jointPostcriticalSet_finite` in [Postcritical](CommutingIntervalSimplified/Postcritical.lean). |
| Lemma 5.8, substitutive itinerary | `foldItinerary_exists` and `dominantEigenvalue_of_positive_metric_scaling` in [Coding](CommutingIntervalSimplified/Coding.lean) handle the itinerary and spectral radii. The powers that are Perron numbers are provided by the original library's `common_ray_has_perron_powered_presentations` in [PiecewiseLinearB9SymbolicSupport](CommutingInterval/PiecewiseLinearB9SymbolicSupport.lean). The simplified library uses the common positive edge-length metric directly. |
| Lemma 5.9, rigidity of periodic paths | `periodic_local_match_globalizes` and `cross_period_globalization` in [PeriodicPathRigidity](CommutingIntervalSimplified/PeriodicPathRigidity.lean) give the local-match and surjective versions. |
| Lemma 5.10, integer slopes and circle lifts | `normalized_real_affine_lifts_of_cross_period` and `original_phase_affine_lifts` in [PeriodicAffineLifts](CommutingIntervalSimplified/PeriodicAffineLifts.lean) construct the normalized circle actions. The new `original_phase_affine_lifts_with_degrees` keeps the numerical equalities between the integer degrees and the slope magnitudes together with the commuting lifts. |

## Checking

From the repository root, use the pinned Lean toolchain and run `lake build`. The new development can be checked separately with `lake build CommutingIntervalSimplified.CommonPeriodicPoints`.
