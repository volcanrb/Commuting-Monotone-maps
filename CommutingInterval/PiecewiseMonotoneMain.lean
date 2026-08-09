import CommutingInterval.PiecewiseMonotoneQuotient
import CommutingInterval.PiecewiseMonotoneResolvent
import CommutingInterval.PiecewiseLinearCorrectedAssembly

/-!
# Common fixed points for commuting finite-piece piecewise-monotone maps

This file is the final assembly layer for the direct proof.  It consumes the
direct horseshoe/resolvent/eigenmeasure route through the public quotient
interface, applies the unconditional finite-piece PL theorem downstairs, and
uses minimality of the normalized core on the resulting fixed fibre.
-/

noncomputable section

namespace CommutingInterval

open Function Set MeasureTheory

/-! ## Simultaneous positive input on a minimal normalized core -/

/-- The direct composite horseshoe, weak-lap resolvent, and `L = 1` joint
eigenmeasure theorem supply the exact positive input to the quotient. -/
theorem MinimalPiecewiseMonotoneCounterexample.simultaneousTransferEigenProbability_exists
    (C : MinimalPiecewiseMonotoneCounterexample) :
    Nonempty (SimultaneousTransferEigenProbability C.P C.Q) := by
  let PP : MonotonicityPartition C.P :=
    Classical.choice C.finitePiece_P.2
  let PQ : MonotonicityPartition C.Q :=
    Classical.choice C.finitePiece_Q.2
  let PH : MonotonicityPartition (C.P ∘ C.Q) :=
    Classical.choice C.finitePiece_H.2
  obtain ⟨horse⟩ := commuting_noCommonFixedPoint_horseshoe
    C.finitePiece_P.continuous C.finitePiece_Q.continuous
    C.commute C.no_common_fixed_point
  obtain ⟨lambda, μ, hlambda, hprob, hμ, heigen⟩ :=
    transferMeasure_eigenprobability_exists C.finitePiece_H horse PH
  obtain ⟨ν, scaleP, scaleQ, hν, hscaleP, hscaleQ, hνprob,
      heigenP, heigenQ, _hproduct⟩ :=
    simultaneousEigenprobability_of_productEigenprobability
      C.finitePiece_P C.finitePiece_Q C.commute PP PQ PH
      lambda hlambda μ hprob.measure_univ hμ heigen
  exact ⟨{
    finitePiece_P := C.finitePiece_P
    finitePiece_Q := C.finitePiece_Q
    commute := C.commute
    partitionP := PP
    partitionQ := PQ
    measure := ν
    probability := hνprob
    noAtoms := hν
    scaleP := scaleP
    scaleQ := scaleQ
    scaleP_pos := hscaleP
    scaleQ_pos := hscaleQ
    transferP_eigen := heigenP
    transferQ_eigen := heigenQ }⟩

/-! ## The packaged common PL quotient -/

/-- All quotient data consumed by the PL theorem and the fixed-fibre lift. -/
structure CommonPiecewiseLinearQuotientData
    (C : MinimalPiecewiseMonotoneCounterexample) where
  eigen : SimultaneousTransferEigenProbability C.P C.Q
  distribution : DistributionQuotientData eigen.measure
  finitePiecePL_factorP : FinitePiecePL (eigen.factorP distribution)
  finitePiecePL_factorQ : FinitePiecePL (eigen.factorQ distribution)
  factors_commute :
    Commute (eigen.factorP distribution) (eigen.factorQ distribution)

/-- Construct the distribution quotient and record its two commuting
finite-piece PL factors. -/
theorem MinimalPiecewiseMonotoneCounterexample.commonPiecewiseLinearQuotientData_exists
    (C : MinimalPiecewiseMonotoneCounterexample) :
    Nonempty (CommonPiecewiseLinearQuotientData C) := by
  obtain ⟨E⟩ := C.simultaneousTransferEigenProbability_exists
  let X : DistributionQuotientData E.measure :=
    canonicalDistributionQuotientData E.measure E.probability E.noAtoms
  exact ⟨{
    eigen := E
    distribution := X
    finitePiecePL_factorP := E.finitePiecePL_factorP X
    finitePiecePL_factorQ := E.finitePiecePL_factorQ X
    factors_commute := E.factors_commute X }⟩

/-! ## Minimal-core contradiction and public theorem -/

/-- A hypothetical normalized minimal counterexample is impossible: the PL
factors have a common fixed point, whose compact interval fibre is a common
invariant core; minimality makes that fibre all of `I`, contradicting the two
distinct endpoint values of the distribution coordinate. -/
theorem MinimalPiecewiseMonotoneCounterexample.false
    (C : MinimalPiecewiseMonotoneCounterexample) : False := by
  obtain ⟨D⟩ := C.commonPiecewiseLinearQuotientData_exists
  obtain ⟨y, hyP, hyQ⟩ := finitePiecePL_common_fixed_point
    (D.eigen.factorP D.distribution) (D.eigen.factorQ D.distribution)
    D.finitePiecePL_factorP D.finitePiecePL_factorQ D.factors_commute
  obtain ⟨F⟩ :=
    D.eigen.commonFixedFibre_exists D.distribution hyP hyQ
  have hcarrier : F.interval.carrier = Set.univ :=
    C.core_minimal F.interval F.common_invariant
  have hfibre : {x : I | D.distribution.coordinate x = y} = Set.univ :=
    F.carrier_eq.symm.trans hcarrier
  have hleft : D.distribution.coordinate leftEndpoint = y := by
    have := Set.eq_univ_iff_forall.mp hfibre leftEndpoint
    exact this
  have hright : D.distribution.coordinate rightEndpoint = y := by
    have := Set.eq_univ_iff_forall.mp hfibre rightEndpoint
    exact this
  have hend : leftEndpoint = rightEndpoint :=
    D.distribution.left_endpoint.symm.trans
      (hleft.trans (hright.symm.trans D.distribution.right_endpoint))
  have hreal := congrArg Subtype.val hend
  norm_num [leftEndpoint, rightEndpoint] at hreal

/-- **Common fixed-point theorem for weak finite-piece monotone maps.**
Two commuting continuous self-maps of `[0,1]`, each weakly monotone on the
cells of a finite partition, have a common fixed point. -/
theorem finitePieceMonotone_common_fixed_point
    (P Q : IntervalMap)
    (hP : FinitePieceMonotone P) (hQ : FinitePieceMonotone Q)
    (hcomm : Commute P Q) : HasCommonFixedPoint P Q := by
  by_contra hno
  let C0 : PiecewiseMonotoneCounterexample :=
    { P := P
      Q := Q
      finitePiece_P := hP
      finitePiece_Q := hQ
      commute := hcomm
      no_common_fixed_point := hno }
  obtain ⟨C⟩ := C0.exists_minimalCounterexample
  exact C.false

end CommutingInterval
