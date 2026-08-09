import CommutingInterval.PiecewiseLinearB6Scratch
import CommutingInterval.PiecewiseLinearB9Scratch
import CommutingInterval.PiecewiseLinearB10Scratch

/-!
# Unconditional piecewise-linear assembly

This module joins the orbit-ray, directed-edge, two-scale, and original-phase
arguments used by the unconditional theorem.  The declaration order follows
their mathematical dependencies:

1. convert the nonnegative `RayChart` and exactness data into a real-parameter
   irrational-exact system;
2. aggregate the irrational side of the orbit-circle dichotomy;
3. close that branch through directed-edge coding and the original-phase
   calculation;
4. rule out a least normalized PL counterexample, including the signed
   rational branch; and
5. export the unconditional finite-piece PL theorem.
-/

namespace CommutingInterval

open Function Set

noncomputable section

namespace PiecewiseLinearCorrectedAssembly

open PiecewiseLinearB6 PiecewiseLinearB10Scratch

/-! ## Piecewise-linear assembly -/

/-- Convert the checked ray-covering and exactness packages into the record
consumed by the already proved joint-spectral and Markov layers.  The real
parameter representative clamps negative parameters to the ray origin. -/
noncomputable def rayCoveringData_to_irrationalExactSystem
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (T : RayCoveringData G)
    (X : ExactnessData G)
    (hno : ¬PLCommonPositiveIterateAlternative G.P G.Q) :
    PiecewiseLinearIrrationalExactSystem G := by
  let clamp : ℝ → RayParameter := fun t =>
    ⟨max t 0, le_max_right t 0⟩
  let realRay : ℝ → I := fun t => T.ray (clamp t)
  have hclamp_nonneg (t : ℝ) (ht : 0 ≤ t) :
      clamp t = (⟨t, ht⟩ : RayParameter) := by
    apply Subtype.ext
    simp [clamp, max_eq_left ht]
  have hclamp_zero : clamp 0 = rayOrigin := by
    apply Subtype.ext
    change max (0 : ℝ) 0 = 0
    exact max_eq_left le_rfl
  have hclamp_continuous : Continuous clamp := by
    apply Continuous.subtype_mk
    exact continuous_id.max continuous_const
  have hrealRay_continuous : Continuous realRay :=
    T.ray.continuous_toFun.comp hclamp_continuous
  have hrealRay_base : realRay 0 = G.p := by
    change T.ray (clamp 0) = G.p
    rw [hclamp_zero]
    exact T.ray.map_origin
  have hrealRay_surjective : Surjective realRay := by
    intro x
    obtain ⟨t, ht⟩ := T.ray.surjective_toFun x
    refine ⟨(t : ℝ), ?_⟩
    change T.ray (clamp (t : ℝ)) = x
    rw [hclamp_nonneg (t : ℝ) t.property]
    exact ht
  have hrealRay_actionA : ∀ t : ℝ, 0 ≤ t →
      realRay (T.localData.scaleA * t) = G.A (realRay t) := by
    intro t ht
    have hscaled : 0 ≤ T.localData.scaleA * t :=
      mul_nonneg T.actionA.scale_pos.le ht
    change T.ray (clamp (T.localData.scaleA * t)) =
      G.A (T.ray (clamp t))
    rw [hclamp_nonneg _ hscaled, hclamp_nonneg _ ht]
    simpa [scaleRayParameter] using
      (T.actionA.equivariant (⟨t, ht⟩ : RayParameter)).symm
  have hrealRay_actionB : ∀ t : ℝ, 0 ≤ t →
      realRay (T.localData.scaleB * t) = G.B (realRay t) := by
    intro t ht
    have hscaled : 0 ≤ T.localData.scaleB * t :=
      mul_nonneg T.actionB.scale_pos.le ht
    change T.ray (clamp (T.localData.scaleB * t)) =
      G.B (T.ray (clamp t))
    rw [hclamp_nonneg _ hscaled, hclamp_nonneg _ ht]
    simpa [scaleRayParameter] using
      (T.actionB.equivariant (⟨t, ht⟩ : RayParameter)).symm
  have hdense := PiecewiseLinearB6.piecewiseLinear_ray_hasDenseTails T
  have hrealRay_dense : ∀ a : ℝ, Dense (realRay '' Set.Ici a) := by
    intro a
    by_cases ha : 0 ≤ a
    · let start : RayParameter := ⟨a, ha⟩
      have himage : realRay '' Set.Ici a =
          T.ray.toFun '' Set.Ici start := by
        ext x
        constructor
        · rintro ⟨t, ht, htx⟩
          have ht0 : 0 ≤ t := ha.trans ht
          refine ⟨(⟨t, ht0⟩ : RayParameter), ?_, ?_⟩
          · exact ht
          · rw [← htx]
            change T.ray ⟨t, ht0⟩ = T.ray (clamp t)
            rw [hclamp_nonneg t ht0]
        · rintro ⟨t, ht, htx⟩
          refine ⟨(t : ℝ), ?_, ?_⟩
          · exact ht
          · rw [← htx]
            change T.ray (clamp (t : ℝ)) = T.ray t
            rw [hclamp_nonneg (t : ℝ) t.property]
      rw [dense_iff_closure_eq, himage]
      simpa [RayChart.tailClosure, RayChart.tailImage] using hdense start
    · have himage : realRay '' Set.Ici a = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        obtain ⟨t, ht⟩ := T.ray.surjective_toFun x
        refine ⟨(t : ℝ), ?_, ?_⟩
        · exact (lt_of_not_ge ha).le.trans t.property
        · change T.ray (clamp (t : ℝ)) = x
          rw [hclamp_nonneg (t : ℝ) t.property]
          exact ht
      rw [himage]
      exact dense_univ
  exact
    { ray := realRay
      scaleA := T.localData.scaleA
      scaleB := T.localData.scaleB
      one_lt_scaleA := T.one_lt_scaleA
      one_lt_scaleB := T.one_lt_scaleB
      scales_independent := T.scales_independent
      continuous_ray := hrealRay_continuous
      ray_base := hrealRay_base
      ray_onto := hrealRay_surjective
      action_A := hrealRay_actionA
      action_B := hrealRay_actionB
      dense_tails := hrealRay_dense
      exact_P := X.exact_P
      exact_Q := X.exact_Q
      exact_A := X.exact_A
      exact_B := X.exact_B
      exact_R := X.exact_R
      noFlat_P := X.noFlat_P
      noFlat_Q := X.noFlat_Q
      noFlat_R := X.noFlat_R
      no_positive_iterate := hno }

/-- The translation side of the corrected orbit-circle dichotomy supplies
the exact historical record needed by the downstream spectral construction. -/
theorem translationChart_to_irrationalExactSystem
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    (G : PiecewiseLinearSelectedFixedGap source)
    (D : PiecewiseLinearDirectedReturnData G)
    (H : PreparedPiecewiseLinearCounterexample G)
    (chart : TranslationChartData G) :
    Nonempty (PiecewiseLinearIrrationalExactSystem G) := by
  obtain ⟨localData⟩ :=
    PiecewiseLinearB6.piecewiseLinear_translationChart_to_localDilation
      G D chart
  obtain ⟨ray⟩ :=
    PiecewiseLinearB6.piecewiseLinear_localDilation_to_rayCovering
      G D H localData
  have hdense : ray.ray.HasDenseTails :=
    PiecewiseLinearB6.piecewiseLinear_ray_hasDenseTails ray
  obtain ⟨boundary⟩ :=
    PiecewiseLinearB6.piecewiseLinear_exists_positiveBoundaryLift
      ray hdense
  have exactness : ExactnessData G :=
    PiecewiseLinearB6.piecewiseLinear_denseRay_exactnessPackage
      ray hdense boundary
  have hno : ¬PLCommonPositiveIterateAlternative G.P G.Q := by
    rintro ⟨m, n, hm, hn, hpowers⟩
    exact G.noCommonFixed
      (common_positive_iterate ray.continuous_P ray.continuous_Q
        G.system.commute hm hn hpowers)
  exact ⟨rayCoveringData_to_irrationalExactSystem ray exactness hno⟩

/-- Close the irrational branch using the checked common coordinate, common
Markov package, exact directed-edge coding, least-period path, and original
phase theorem. -/
theorem irrationalExactSystem_commonFixedPoint
    {source : LeastNormalizedPiecewiseLinearCounterexample}
    {G : PiecewiseLinearSelectedFixedGap source}
    (E : PiecewiseLinearIrrationalExactSystem G) :
    HasCommonFixedPoint G.P G.Q := by
  obtain ⟨M⟩ := piecewiseLinear_jointEigenmeasure_commonCoordinate E
  obtain ⟨K⟩ := piecewiseLinear_exists_commonMarkovPackage M
  exact PiecewiseLinearB10Scratch.markovSubstitutions_commonFixedPoint M K

/-- A least normalized PL counterexample is impossible: the signed rational
orbit alternative is excluded by the corrected B6 argument, and the
translation alternative is closed by the corrected B9/B10 chain. -/
theorem leastNormalizedPiecewiseLinearCounterexample_false
    (C : LeastNormalizedPiecewiseLinearCounterexample) : False := by
  obtain ⟨G⟩ := exists_piecewiseLinearSelectedFixedGap C
  have D := piecewiseLinear_directedStateReturn G
  have H := piecewiseLinear_finiteArrivalAndLEO G D
  rcases PiecewiseLinearB6.piecewiseLinear_orbitCircle_localDichotomy G D with
    hrat | hirr
  · rcases hrat with ⟨d, alpha, hd, hR, rat⟩
    exact PiecewiseLinearB6.piecewiseLinear_rationalOrbitAlternative_impossible
      G D H hd hR rat
  · obtain ⟨chart⟩ := hirr
    obtain ⟨E⟩ := translationChart_to_irrationalExactSystem G D H chart
    exact G.noCommonFixed (irrationalExactSystem_commonFixedPoint E)

/-- **Corrected unconditional finite-piece PL core.** Every commuting pair of
continuous finite-piece piecewise-linear selfmaps of `[0,1]` has a common
fixed point. -/
theorem finitePiecePL_common_fixed_point
    (P Q : IntervalMap) (hP : FinitePiecePL P) (hQ : FinitePiecePL Q)
    (hcomm : Commute P Q) : HasCommonFixedPoint P Q := by
  by_contra hno
  let C0 : PiecewiseLinearCounterexample :=
    { P := P
      Q := Q
      finitePieceP := hP
      finitePieceQ := hQ
      commute := hcomm
      noCommonFixed := hno }
  obtain ⟨C⟩ := exists_leastNormalizedPiecewiseLinearCounterexample
    piecewiseLinear_finitenessPackage C0
  exact leastNormalizedPiecewiseLinearCounterexample_false C

end PiecewiseLinearCorrectedAssembly

/-- **Public unconditional finite-piece PL theorem.**  This root alias keeps
the historical production API while delegating to the corrected acyclic
assembly. -/
theorem finitePiecePL_common_fixed_point
    (P Q : IntervalMap) (hP : FinitePiecePL P) (hQ : FinitePiecePL Q)
    (hcomm : Commute P Q) : HasCommonFixedPoint P Q :=
  PiecewiseLinearCorrectedAssembly.finitePiecePL_common_fixed_point
    P Q hP hQ hcomm

end

end CommutingInterval
