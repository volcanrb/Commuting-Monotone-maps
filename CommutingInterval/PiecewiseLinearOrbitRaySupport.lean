import CommutingInterval.DynamicsDefs
import CommutingInterval.CommonIterate
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Orbit-ray support for the piecewise-linear theorem

This module contains the generic local-ray extension, tail-core, dense-tail,
boundary-lift, and covering-exactness arguments.
-/

namespace CommutingInterval

open Function Set

/-! ## The parameter ray and local charts -/

/-- The nonnegative real parameter ray. -/
abbrev RayParameter := {t : ℝ // 0 ≤ t}

/-- The origin of the parameter ray. -/
def rayOrigin : RayParameter := ⟨0, le_rfl⟩

/-- Multiplication by a nonnegative scalar on the parameter ray. -/
def scaleRayParameter (a : ℝ) (ha : 0 ≤ a) (t : RayParameter) :
    RayParameter :=
  ⟨a * (t : ℝ), mul_nonneg ha t.property⟩

/-- The relatively open initial parameter segment `[0, radius)`. -/
def rayInitialSegment (radius : ℝ) : Set RayParameter :=
  {t | (t : ℝ) < radius}

/--
A strictly increasing local right-hand chart based at `p`.  The endpoint
hypothesis prevents the selected side from being vacuous.
-/
structure LocalRayChart (p : I) where
  /-- The selected right side exists. -/
  base_lt_rightEndpoint : p < rightEndpoint
  /-- Radius on which the local chart data are valid. -/
  radius : ℝ
  /-- The local parameter interval is nondegenerate. -/
  radius_pos : 0 < radius
  /-- A total representative; only its restriction below `radius` is used. -/
  toFun : RayParameter → I
  /-- Continuity on the local parameter interval. -/
  continuousOn_toFun : ContinuousOn toFun (rayInitialSegment radius)
  /-- The ray origin is sent to the selected base. -/
  map_origin : toFun rayOrigin = p
  /-- The local chart is orientation preserving. -/
  strictMonoOn_toFun : StrictMonoOn toFun (rayInitialSegment radius)
  /-- The local image remains on the selected closed right side. -/
  mapsTo_rightSide : MapsTo toFun (rayInitialSegment radius) (Set.Ici p)

instance {p : I} : CoeFun (LocalRayChart p) (fun _ => RayParameter → I) :=
  ⟨LocalRayChart.toFun⟩

/-- A map acts by multiplication by `a` wherever both local parameters occur. -/
structure LocalRayScaleAction {p : I} (ι : LocalRayChart p)
    (T : IntervalMap) (a : ℝ) : Prop where
  /-- The local multiplier preserves the positive ray. -/
  scale_pos : 0 < a
  /-- The local dilation identity. -/
  equivariant :
    ∀ t : RayParameter,
      t ∈ rayInitialSegment ι.radius →
        scaleRayParameter a scale_pos.le t ∈ rayInitialSegment ι.radius →
          T (ι t) = ι (scaleRayParameter a scale_pos.le t)

/-! ## Global ray charts and scale actions -/

/--
A continuous surjective ray based at `p`, with a nontrivial initial segment
which is still a positively oriented chart of the selected right side.
-/
structure RayChart (p : I) where
  /-- The selected right side exists. -/
  base_lt_rightEndpoint : p < rightEndpoint
  /-- The global ray map. -/
  toFun : RayParameter → I
  /-- The global ray is continuous. -/
  continuous_toFun : Continuous toFun
  /-- The ray begins at `p`. -/
  map_origin : toFun rayOrigin = p
  /-- The ray covers the whole interval. -/
  surjective_toFun : Surjective toFun
  /-- Radius of a nontrivial initial chart interval. -/
  initialRadius : ℝ
  /-- Positivity of the initial radius. -/
  initialRadius_pos : 0 < initialRadius
  /-- The initial chart is orientation preserving. -/
  strictMonoOn_initial : StrictMonoOn toFun (rayInitialSegment initialRadius)
  /-- The initial image lies on the selected closed right side. -/
  mapsTo_initial_rightSide :
    MapsTo toFun (rayInitialSegment initialRadius) (Set.Ici p)

instance {p : I} : CoeFun (RayChart p) (fun _ => RayParameter → I) :=
  ⟨RayChart.toFun⟩

/-- A global interval map acts on a ray chart by multiplication by `a`. -/
structure RayScaleAction {p : I} (Φ : RayChart p)
    (T : IntervalMap) (a : ℝ) : Prop where
  /-- The multiplier preserves the positive ray. -/
  scale_pos : 0 < a
  /-- The global equivariance identity. -/
  equivariant :
    ∀ t : RayParameter,
      T (Φ t) = Φ (scaleRayParameter a scale_pos.le t)

private theorem rayScaleAction_iterate
    {p : I} (Φ : RayChart p) {T : IntervalMap} {a : ℝ}
    (hT_action : RayScaleAction Φ T a) (n : ℕ) (t : RayParameter) :
    iterateMap T n (Φ t) =
      Φ (scaleRayParameter (a ^ n) (pow_nonneg hT_action.scale_pos.le n) t) := by
  induction n with
  | zero =>
      change Φ t = Φ (scaleRayParameter 1 (by positivity) t)
      have ht : scaleRayParameter 1 (by positivity) t = t := by
        apply Subtype.ext
        change 1 * (t : ℝ) = (t : ℝ)
        ring
      exact congrArg Φ.toFun ht.symm
  | succ n ih =>
      rw [iterateMap, Function.iterate_succ_apply']
      change T^[n] (Φ t) = _ at ih
      rw [ih, hT_action.equivariant]
      have hscale :
          scaleRayParameter a hT_action.scale_pos.le
              (scaleRayParameter (a ^ n)
                (pow_nonneg hT_action.scale_pos.le n) t) =
            scaleRayParameter (a ^ (n + 1))
              (pow_nonneg hT_action.scale_pos.le (n + 1)) t := by
        apply Subtype.ext
        change a * (a ^ n * (t : ℝ)) = a ^ (n + 1) * (t : ℝ)
        rw [pow_succ]
        ring
      exact congrArg Φ.toFun hscale

/-- Iterating a ray-scale action raises its parameter multiplier to the same
power. -/
theorem RayScaleAction.iterate_equivariant
    {p : I} {Φ : RayChart p} {T : IntervalMap} {a : ℝ}
    (hT_action : RayScaleAction Φ T a) (n : ℕ) (t : RayParameter) :
    iterateMap T n (Φ t) =
      Φ (scaleRayParameter (a ^ n)
        (pow_nonneg hT_action.scale_pos.le n) t) := by
  exact rayScaleAction_iterate Φ hT_action n t

namespace RayChart

/-- A global ray agrees with a local chart on some nontrivial initial segment. -/
def ExtendsLocal {p : I} (Φ : RayChart p) (ι : LocalRayChart p) : Prop :=
  ∃ radius : ℝ, 0 < radius ∧ radius ≤ ι.radius ∧
    Set.EqOn Φ.toFun ι.toFun (rayInitialSegment radius)

/-- The image of the parameter tail beginning at `start`. -/
def tailImage {p : I} (Φ : RayChart p) (start : RayParameter) : Set I :=
  Φ.toFun '' Set.Ici start

/-- The closed image of a parameter tail. -/
def tailClosure {p : I} (Φ : RayChart p) (start : RayParameter) : Set I :=
  closure (Φ.tailImage start)

/-- The intersection of all closed ray-tail images. -/
def tailCore {p : I} (Φ : RayChart p) : Set I :=
  ⋂ start : RayParameter, Φ.tailClosure start

/-- Every parameter tail has dense image in `I`. -/
def HasDenseTails {p : I} (Φ : RayChart p) : Prop :=
  ∀ start : RayParameter, Φ.tailClosure start = Set.univ

/--
`tstar > 0` is a lift of the base which is accumulated by ray values on the
selected right side.  This is the boundary lift used in the exactness proof.
-/
def IsPositiveBoundaryLift {p : I} (Φ : RayChart p)
    (tstar : RayParameter) : Prop :=
  0 < (tstar : ℝ) ∧ Φ tstar = p ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ t : RayParameter,
        |(t : ℝ) - (tstar : ℝ)| < ε ∧ p < Φ t

end RayChart

private theorem initialChart_Icc_subset_image
    {p : I} (Φ : RayChart p) {ε : ℝ}
    (hεpos : 0 < ε) (hεradius : ε < Φ.initialRadius) :
    let tε : RayParameter := ⟨ε, hεpos.le⟩
    Set.Icc p (Φ tε) ⊆ Φ.toFun '' Set.Icc rayOrigin tε := by
  dsimp only
  let tε : RayParameter := ⟨ε, hεpos.le⟩
  change Set.Icc p (Φ tε) ⊆ Φ.toFun '' Set.Icc rayOrigin tε
  let liftNonneg : ℝ → RayParameter :=
    fun x ↦ ⟨max 0 x, le_max_left 0 x⟩
  have hliftContinuous : Continuous liftNonneg :=
    (continuous_const.max continuous_id).subtype_mk _
  have hliftZero : liftNonneg 0 = rayOrigin := by
    apply Subtype.ext
    change max 0 0 = 0
    simp
  have hliftEpsilon : liftNonneg ε = tε := by
    apply Subtype.ext
    simp [liftNonneg, tε, hεpos.le]
  intro x hx
  have hx' : x ∈ Set.Icc ((Φ.toFun ∘ liftNonneg) 0)
      ((Φ.toFun ∘ liftNonneg) ε) := by
    simpa [Function.comp_apply, hliftZero, hliftEpsilon, Φ.map_origin] using hx
  have himage := intermediate_value_Icc hεpos.le
    (Φ.continuous_toFun.comp hliftContinuous).continuousOn hx'
  obtain ⟨u, hu, hΦu⟩ := himage
  refine ⟨liftNonneg u, ?_, hΦu⟩
  constructor
  · change 0 ≤ max 0 u
    exact le_max_left _ _
  · change max 0 u ≤ ε
    simpa [max_eq_right hu.1] using hu.2

/-- A global ray-scale identity holds on some nontrivial germ at the origin. -/
def HasLocalScaleGerm {p : I} (Φ : RayChart p)
    (T : IntervalMap) (a : ℝ) : Prop :=
  ∃ ha : 0 < a, ∃ radius : ℝ, 0 < radius ∧
    ∀ t : RayParameter,
      (t : ℝ) < radius →
        (scaleRayParameter a ha.le t : ℝ) < radius →
          T (Φ t) = Φ (scaleRayParameter a ha.le t)

/-! ## From local dilation germs to the full ray -/

/-- Divide a ray parameter by a positive power. -/
private noncomputable def descaleRayParameter (lambdaScale : ℝ)
    (hLambdaPos : 0 < lambdaScale)
    (n : ℕ) (t : RayParameter) : RayParameter :=
  ⟨(t : ℝ) / lambdaScale ^ n,
    div_nonneg t.property (pow_pos hLambdaPos n).le⟩

/-- The `n`th representative of the ray obtained by propagating a local
chart with the expanding map. -/
private noncomputable def localRayCandidate {p : I} (ι : LocalRayChart p)
    (W : IntervalMap) (lambdaScale : ℝ) (hLambdaPos : 0 < lambdaScale)
    (n : ℕ) (t : RayParameter) : I :=
  iterateMap W n (ι (descaleRayParameter lambdaScale hLambdaPos n t))

private theorem localRayCandidate_succ_eq
    {W : IntervalMap} {p : I} (ι : LocalRayChart p)
    {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (hlocal : LocalRayScaleAction ι W lambdaScale)
    (n : ℕ) (t : RayParameter)
    (ht : (t : ℝ) < ι.radius * lambdaScale ^ n) :
    localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) (n + 1) t =
      localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) n t := by
  let u := descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) (n + 1) t
  let v := descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) n t
  have hv_radius : (v : ℝ) < ι.radius := by
    change (t : ℝ) / lambdaScale ^ n < ι.radius
    exact (div_lt_iff₀ (pow_pos (zero_lt_one.trans hLambda) n)).2
      (by simpa [mul_comm] using ht)
  have hscale :
      scaleRayParameter lambdaScale hlocal.scale_pos.le u = v := by
    apply Subtype.ext
    change lambdaScale * ((t : ℝ) / lambdaScale ^ (n + 1)) =
      (t : ℝ) / lambdaScale ^ n
    rw [pow_succ]
    field_simp [(zero_lt_one.trans hLambda).ne']
  have hu_radius : (u : ℝ) < ι.radius := by
    have hu_le : (u : ℝ) ≤
        (scaleRayParameter lambdaScale hlocal.scale_pos.le u : ℝ) := by
      change (u : ℝ) ≤ lambdaScale * (u : ℝ)
      nlinarith [u.property]
    rw [hscale] at hu_le
    exact hu_le.trans_lt hv_radius
  unfold localRayCandidate
  rw [iterateMap, Function.iterate_succ_apply']
  change W ((W^[n]) (ι u)) = (W^[n]) (ι v)
  calc
    W ((W^[n]) (ι u)) = (W^[n]) (W (ι u)) :=
      Function.Commute.self_iterate W n (ι u)
    _ = (W^[n]) (ι (scaleRayParameter lambdaScale hlocal.scale_pos.le u)) := by
      rw [hlocal.equivariant u hu_radius (by simpa [hscale] using hv_radius)]
    _ = (W^[n]) (ι v) := congrArg (W^[n]) (congrArg ι.toFun hscale)

private theorem localRayCandidate_eq_of_le
    {W : IntervalMap} {p : I} (ι : LocalRayChart p)
    {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (hlocal : LocalRayScaleAction ι W lambdaScale)
    {n m : ℕ} (hnm : n ≤ m) (t : RayParameter)
    (ht : (t : ℝ) < ι.radius * lambdaScale ^ n) :
    localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) m t =
      localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) n t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction d with
  | zero => rfl
  | succ d ih =>
      have hn_le : n ≤ n + d := Nat.le_add_right n d
      have hpow_le : lambdaScale ^ n ≤ lambdaScale ^ (n + d) :=
        pow_le_pow_right₀ hLambda.le hn_le
      have ht' : (t : ℝ) < ι.radius * lambdaScale ^ (n + d) :=
        ht.trans_le (mul_le_mul_of_nonneg_left hpow_le ι.radius_pos.le)
      rw [Nat.add_succ]
      exact (localRayCandidate_succ_eq ι hLambda hlocal (n + d) t ht').trans
        (ih (Nat.le_add_right n d))

private theorem localRayCandidate_eq_of_admissible
    {W : IntervalMap} {p : I} (ι : LocalRayChart p)
    {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (hlocal : LocalRayScaleAction ι W lambdaScale)
    (n m : ℕ) (t : RayParameter)
    (hn : (t : ℝ) < ι.radius * lambdaScale ^ n)
    (hm : (t : ℝ) < ι.radius * lambdaScale ^ m) :
    localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) n t =
      localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) m t := by
  rcases le_total n m with hnm | hmn
  · exact (localRayCandidate_eq_of_le ι hLambda hlocal hnm t hn).symm
  · exact localRayCandidate_eq_of_le ι hLambda hlocal hmn t hm

private theorem exists_localRayCandidate_index
    {p : I} (ι : LocalRayChart p) {lambdaScale : ℝ}
    (hLambda : 1 < lambdaScale) (t : RayParameter) :
    ∃ n : ℕ, (t : ℝ) < ι.radius * lambdaScale ^ n := by
  let M : ℝ := (t : ℝ) / ι.radius
  obtain ⟨n, hn⟩ :=
    (tendsto_pow_atTop_atTop_of_one_lt hLambda).eventually_gt_atTop M |>.exists
  refine ⟨n, ?_⟩
  have := (div_lt_iff₀ ι.radius_pos).mp hn
  simpa [M, mul_comm] using this

private noncomputable def localRayExtensionIndex
    {p : I} (ι : LocalRayChart p) {lambdaScale : ℝ}
    (hLambda : 1 < lambdaScale) (t : RayParameter) : ℕ :=
  Classical.choose (exists_localRayCandidate_index ι hLambda t)

private theorem localRayExtensionIndex_spec
    {p : I} (ι : LocalRayChart p) {lambdaScale : ℝ}
    (hLambda : 1 < lambdaScale) (t : RayParameter) :
    (t : ℝ) < ι.radius * lambdaScale ^
      localRayExtensionIndex ι hLambda t :=
  Classical.choose_spec (exists_localRayCandidate_index ι hLambda t)

private noncomputable def extendedLocalRay {W : IntervalMap} {p : I}
    (ι : LocalRayChart p) {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (t : RayParameter) : I :=
  localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda)
    (localRayExtensionIndex ι hLambda t) t

private theorem extendedLocalRay_eq_candidate
    {W : IntervalMap} {p : I} (ι : LocalRayChart p)
    {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (hlocal : LocalRayScaleAction ι W lambdaScale)
    (n : ℕ) (t : RayParameter)
    (hn : (t : ℝ) < ι.radius * lambdaScale ^ n) :
    extendedLocalRay (W := W) ι hLambda t =
      localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) n t := by
  unfold extendedLocalRay
  exact localRayCandidate_eq_of_admissible ι hLambda hlocal
    (localRayExtensionIndex ι hLambda t) n t
    (localRayExtensionIndex_spec ι hLambda t) hn

private theorem extendedLocalRay_continuous
    {W : IntervalMap} {p : I} (ι : LocalRayChart p)
    {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (hW_continuous : Continuous W)
    (hlocal : LocalRayScaleAction ι W lambdaScale) :
    Continuous (extendedLocalRay (W := W) ι hLambda) := by
  rw [continuous_iff_continuousAt]
  intro t
  let n := localRayExtensionIndex ι hLambda t
  have ht : (t : ℝ) < ι.radius * lambdaScale ^ n :=
    localRayExtensionIndex_spec ι hLambda t
  have hdescale_continuous : Continuous
      (descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) n) := by
    exact (continuous_subtype_val.div_const _).subtype_mk _
  have hdescale_mem :
      descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) n t ∈
        rayInitialSegment ι.radius := by
    change (t : ℝ) / lambdaScale ^ n < ι.radius
    exact (div_lt_iff₀ (pow_pos (zero_lt_one.trans hLambda) n)).2
      (by simpa [mul_comm] using ht)
  have hlocal_open : IsOpen (rayInitialSegment ι.radius) :=
    isOpen_lt continuous_subtype_val continuous_const
  have hι_at : ContinuousAt ι.toFun
      (descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) n t) :=
    ι.continuousOn_toFun.continuousAt
      (hlocal_open.mem_nhds hdescale_mem)
  have hcand_at : ContinuousAt
      (localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) n) t := by
    change ContinuousAt
      (fun s ↦ iterateMap W n
        (ι (descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) n s))) t
    exact (IntervalMap.continuous_iterate hW_continuous n).continuousAt.comp
      (hι_at.comp hdescale_continuous.continuousAt)
  have hnear : {s : RayParameter |
      (s : ℝ) < ι.radius * lambdaScale ^ n} ∈ nhds t :=
    (isOpen_lt continuous_subtype_val continuous_const).mem_nhds ht
  have heventually :
      extendedLocalRay (W := W) ι hLambda =ᶠ[nhds t]
        localRayCandidate ι W lambdaScale (zero_lt_one.trans hLambda) n :=
    by
      filter_upwards [hnear] with s hs
      exact extendedLocalRay_eq_candidate ι hLambda hlocal n s hs
  exact hcand_at.congr heventually.symm

private theorem extendedLocalRay_eq_local
    {W : IntervalMap} {p : I} (ι : LocalRayChart p)
    {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (hlocal : LocalRayScaleAction ι W lambdaScale)
    {t : RayParameter} (ht : (t : ℝ) < ι.radius / lambdaScale) :
    extendedLocalRay (W := W) ι hLambda t = ι t := by
  have hradius : (t : ℝ) < ι.radius * lambdaScale ^ 0 := by
    simpa using ht.trans (div_lt_self ι.radius_pos hLambda)
  rw [extendedLocalRay_eq_candidate ι hLambda hlocal 0 t hradius]
  change ι (descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) 0 t) = ι t
  apply congrArg ι.toFun
  apply Subtype.ext
  change (t : ℝ) / lambdaScale ^ 0 = (t : ℝ)
  rw [pow_zero, div_one]

private theorem extendedLocalRay_equivariant
    {W : IntervalMap} {p : I} (ι : LocalRayChart p)
    {lambdaScale : ℝ} (hLambda : 1 < lambdaScale)
    (hlocal : LocalRayScaleAction ι W lambdaScale) (t : RayParameter) :
    W (extendedLocalRay (W := W) ι hLambda t) =
      extendedLocalRay (W := W) ι hLambda
        (scaleRayParameter lambdaScale (zero_lt_one.trans hLambda).le t) := by
  let n := localRayExtensionIndex ι hLambda t
  have ht : (t : ℝ) < ι.radius * lambdaScale ^ n :=
    localRayExtensionIndex_spec ι hLambda t
  let scaled :=
    scaleRayParameter lambdaScale (zero_lt_one.trans hLambda).le t
  have hscaled : (scaled : ℝ) < ι.radius * lambdaScale ^ (n + 1) := by
    have hmul := mul_lt_mul_of_pos_left ht (zero_lt_one.trans hLambda)
    simpa [scaled, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [extendedLocalRay_eq_candidate ι hLambda hlocal n t ht,
    extendedLocalRay_eq_candidate ι hLambda hlocal (n + 1) scaled hscaled]
  have hdescale :
      descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) (n + 1) scaled =
        descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) n t := by
    apply Subtype.ext
    change (lambdaScale * (t : ℝ)) / lambdaScale ^ (n + 1) =
      (t : ℝ) / lambdaScale ^ n
    rw [pow_succ]
    field_simp [(zero_lt_one.trans hLambda).ne']
  unfold localRayCandidate
  rw [hdescale]
  simp only [iterateMap, Function.iterate_succ_apply']

private theorem localChart_Icc_subset_image
    {p : I} (ι : LocalRayChart p) {ε : ℝ}
    (hεpos : 0 < ε) (hεradius : ε < ι.radius) :
    let tε : RayParameter := ⟨ε, hεpos.le⟩
    Set.Icc p (ι tε) ⊆ ι.toFun '' Set.Icc rayOrigin tε := by
  dsimp only
  let tε : RayParameter := ⟨ε, hεpos.le⟩
  change Set.Icc p (ι tε) ⊆ ι.toFun '' Set.Icc rayOrigin tε
  let liftNonneg : ℝ → RayParameter :=
    fun x ↦ ⟨max 0 x, le_max_left 0 x⟩
  have hlift_continuous : Continuous liftNonneg :=
    (continuous_const.max continuous_id).subtype_mk _
  have hlift_maps :
      Set.MapsTo liftNonneg (Set.Icc (0 : ℝ) ε)
        (rayInitialSegment ι.radius) := by
    intro u hu
    change max 0 u < ι.radius
    have hmax_le : max 0 u ≤ ε := by
      rw [max_eq_right hu.1]
      exact hu.2
    exact hmax_le.trans_lt hεradius
  have hcomp_continuous : ContinuousOn (ι.toFun ∘ liftNonneg)
      (Set.Icc (0 : ℝ) ε) :=
    ι.continuousOn_toFun.comp hlift_continuous.continuousOn hlift_maps
  have hlift_zero : liftNonneg 0 = rayOrigin := by
    have hval : (liftNonneg 0 : ℝ) = (rayOrigin : ℝ) := by
      change max 0 (0 : ℝ) = 0
      simp
    exact Subtype.ext hval
  have hlift_epsilon : liftNonneg ε = tε := by
    apply Subtype.ext
    simp [liftNonneg, tε, hεpos.le]
  intro x hx
  have hx' : x ∈ Set.Icc ((ι.toFun ∘ liftNonneg) 0)
      ((ι.toFun ∘ liftNonneg) ε) := by
    simpa [Function.comp_apply, hlift_zero, hlift_epsilon, ι.map_origin] using hx
  obtain ⟨u, hu, hιu⟩ :=
    intermediate_value_Icc hεpos.le hcomp_continuous hx'
  refine ⟨liftNonneg u, ?_, hιu⟩
  constructor
  · exact (liftNonneg u).property
  · change max 0 u ≤ ε
    rw [max_eq_right hu.1]
    exact hu.2

/--
An expanding local dilation germ at a fixed endpoint, together with local
eventual covering from that side, extends canonically to a continuous onto
ray carrying the global `W`-scale action.
-/
theorem extend_local_germ_to_fullRay
    {W : IntervalMap} {p : I}
    (ι : LocalRayChart p) (lambdaScale : ℝ)
    (hW_continuous : Continuous W)
    (hW_fixed : IsFixedPoint W p)
    (hW_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn W (Set.Icc p q))
    (hLambda : 1 < lambdaScale)
    (hlocal : LocalRayScaleAction ι W lambdaScale)
    (hlocalCover :
      ∀ q : I, p < q →
        ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ) :
    ∃ Φ : RayChart p,
      Φ.ExtendsLocal ι ∧ RayScaleAction Φ W lambdaScale := by
  let initialRadius : ℝ := ι.radius / lambdaScale
  have hinitial_pos : 0 < initialRadius :=
    div_pos ι.radius_pos (zero_lt_one.trans hLambda)
  have hinitial_lt : initialRadius < ι.radius := by
    exact div_lt_self ι.radius_pos hLambda
  have hinitial_le : initialRadius ≤ ι.radius := hinitial_lt.le
  let ray : RayParameter → I := extendedLocalRay (W := W) ι hLambda
  have hray_continuous : Continuous ray :=
    extendedLocalRay_continuous ι hLambda hW_continuous hlocal
  have hray_local : Set.EqOn ray ι.toFun
      (rayInitialSegment initialRadius) := by
    intro t ht
    exact extendedLocalRay_eq_local ι hLambda hlocal ht
  have horigin_initial : rayOrigin ∈ rayInitialSegment initialRadius := by
    exact hinitial_pos
  have hray_origin : ray rayOrigin = p := by
    exact (hray_local horigin_initial).trans ι.map_origin
  have hray_strict : StrictMonoOn ray (rayInitialSegment initialRadius) := by
    intro x hx y hy hxy
    calc
      ray x = ι x := hray_local hx
      _ < ι y := ι.strictMonoOn_toFun
        (show x ∈ rayInitialSegment ι.radius from hx.trans hinitial_lt)
        (show y ∈ rayInitialSegment ι.radius from hy.trans hinitial_lt) hxy
      _ = ray y := (hray_local hy).symm
  have hray_maps : MapsTo ray (rayInitialSegment initialRadius) (Set.Ici p) := by
    intro t ht
    rw [hray_local ht]
    exact ι.mapsTo_rightSide (ht.trans hinitial_lt)
  have hray_surjective : Function.Surjective ray := by
    let ε : ℝ := initialRadius / 2
    have hεpos : 0 < ε := by
      dsimp [ε]
      linarith
    have hεinitial : ε < initialRadius := by
      dsimp [ε]
      linarith
    have hεradius : ε < ι.radius := hεinitial.trans hinitial_lt
    let tε : RayParameter := ⟨ε, hεpos.le⟩
    have htε_local : tε ∈ rayInitialSegment ι.radius := hεradius
    have horigin_local : rayOrigin ∈ rayInitialSegment ι.radius := ι.radius_pos
    have horigin_lt : rayOrigin < tε := hεpos
    have hp_lt : p < ι tε := by
      calc
        p = ι rayOrigin := ι.map_origin.symm
        _ < ι tε := ι.strictMonoOn_toFun horigin_local htε_local horigin_lt
    obtain ⟨N, hNcover⟩ := hlocalCover (ι tε) hp_lt
    have hlocal_image :
        Set.Icc p (ι tε) ⊆ ι.toFun '' Set.Icc rayOrigin tε :=
      localChart_Icc_subset_image ι hεpos hεradius
    intro x
    have hxcover : x ∈ iterateMap W N '' Set.Icc p (ι tε) := by
      rw [hNcover]
      exact Set.mem_univ x
    obtain ⟨y, hy, hyx⟩ := hxcover
    obtain ⟨t, ht, hιt⟩ := hlocal_image hy
    let u := scaleRayParameter (lambdaScale ^ N)
      (pow_nonneg (zero_lt_one.trans hLambda).le N) t
    have hu_admissible : (u : ℝ) < ι.radius * lambdaScale ^ N := by
      have ht_le : (t : ℝ) ≤ ε := by
        exact ht.2
      have ht_radius : (t : ℝ) < ι.radius := ht_le.trans_lt hεradius
      have hmul := mul_lt_mul_of_pos_left ht_radius
        (pow_pos (zero_lt_one.trans hLambda) N)
      simpa [u, mul_comm] using hmul
    refine ⟨u, ?_⟩
    change extendedLocalRay (W := W) ι hLambda u = x
    rw [extendedLocalRay_eq_candidate ι hLambda hlocal N u hu_admissible]
    have hdescale :
        descaleRayParameter lambdaScale (zero_lt_one.trans hLambda) N u = t := by
      apply Subtype.ext
      change (lambdaScale ^ N * (t : ℝ)) / lambdaScale ^ N = (t : ℝ)
      exact mul_div_cancel_left₀ (t : ℝ)
        (pow_ne_zero N (zero_lt_one.trans hLambda).ne')
    unfold localRayCandidate
    rw [hdescale, hιt, hyx]
  let Φ : RayChart p :=
    { base_lt_rightEndpoint := ι.base_lt_rightEndpoint
      toFun := ray
      continuous_toFun := hray_continuous
      map_origin := hray_origin
      surjective_toFun := hray_surjective
      initialRadius := initialRadius
      initialRadius_pos := hinitial_pos
      strictMonoOn_initial := hray_strict
      mapsTo_initial_rightSide := hray_maps }
  refine ⟨Φ, ?_, ?_⟩
  · exact ⟨initialRadius, hinitial_pos, hinitial_le, hray_local⟩
  · refine ⟨zero_lt_one.trans hLambda, ?_⟩
    intro t
    exact extendedLocalRay_equivariant ι hLambda hlocal t

/--
A commuting map whose physical germ is multiplication by `a` acts by that
same multiplier on the entire canonical ray.  Continuity, commutation, and
expansion of the deck actor propagate the identity globally.
-/
theorem localScaleGerm_extends_to_fullRay
    {p : I} (Φ : RayChart p)
    {W T : IntervalMap} {lambdaScale a : ℝ}
    (hW_continuous : Continuous W)
    (hT_continuous : Continuous T)
    (hcommute : Commute T W)
    (hLambda : 1 < lambdaScale)
    (hW_action : RayScaleAction Φ W lambdaScale)
    (hT_germ : HasLocalScaleGerm Φ T a) :
    RayScaleAction Φ T a := by
  obtain ⟨ha, radius, hradius, hgerm⟩ := hT_germ
  refine ⟨ha, ?_⟩
  intro t
  let M : ℝ := max (t : ℝ) (a * (t : ℝ)) / radius
  obtain ⟨n, hn⟩ :=
    (tendsto_pow_atTop_atTop_of_one_lt hLambda).eventually_gt_atTop M |>.exists
  have hlambdaPos : 0 < lambdaScale := zero_lt_one.trans hLambda
  have hpowPos : 0 < lambdaScale ^ n := pow_pos hlambdaPos n
  have hmax : max (t : ℝ) (a * (t : ℝ)) <
      radius * lambdaScale ^ n := by
    have := (div_lt_iff₀ hradius).mp hn
    simpa [M, mul_comm] using this
  have htBound : (t : ℝ) < radius * lambdaScale ^ n :=
    (le_max_left _ _).trans_lt hmax
  have hatBound : a * (t : ℝ) < radius * lambdaScale ^ n :=
    (le_max_right _ _).trans_lt hmax
  let s : RayParameter :=
    ⟨(t : ℝ) / lambdaScale ^ n,
      div_nonneg t.property hpowPos.le⟩
  have hsRadius : (s : ℝ) < radius := by
    change (t : ℝ) / lambdaScale ^ n < radius
    exact (div_lt_iff₀ hpowPos).2 (by simpa [mul_comm] using htBound)
  have hasRadius :
      (scaleRayParameter a ha.le s : ℝ) < radius := by
    change a * ((t : ℝ) / lambdaScale ^ n) < radius
    rw [show a * ((t : ℝ) / lambdaScale ^ n) =
        (a * (t : ℝ)) / lambdaScale ^ n by ring]
    exact (div_lt_iff₀ hpowPos).2 hatBound
  have hscaleBack :
      scaleRayParameter (lambdaScale ^ n)
          (pow_nonneg hlambdaPos.le n) s = t := by
    apply Subtype.ext
    change lambdaScale ^ n * ((t : ℝ) / lambdaScale ^ n) = (t : ℝ)
    calc
      lambdaScale ^ n * ((t : ℝ) / lambdaScale ^ n) =
          ((t : ℝ) / lambdaScale ^ n) * lambdaScale ^ n := mul_comm _ _
      _ = (t : ℝ) := div_mul_cancel₀ _ hpowPos.ne'
  have hscaleCommute :
      scaleRayParameter (lambdaScale ^ n)
          (pow_nonneg hlambdaPos.le n)
          (scaleRayParameter a ha.le s) =
        scaleRayParameter a ha.le t := by
    apply Subtype.ext
    change lambdaScale ^ n *
        (a * ((t : ℝ) / lambdaScale ^ n)) = a * (t : ℝ)
    field_simp [hpowPos.ne']
  have hWs : iterateMap W n (Φ s) = Φ t := by
    rw [rayScaleAction_iterate Φ hW_action n s, hscaleBack]
  calc
    T (Φ t) = T (iterateMap W n (Φ s)) := congrArg T hWs.symm
    _ = iterateMap W n (T (Φ s)) :=
      (hcommute.iterate_right n).eq (Φ s)
    _ = iterateMap W n (Φ (scaleRayParameter a ha.le s)) := by
      rw [hgerm s hsRadius hasRadius]
    _ = Φ (scaleRayParameter (lambdaScale ^ n)
        (pow_nonneg hlambdaPos.le n)
        (scaleRayParameter a ha.le s)) :=
      rayScaleAction_iterate Φ hW_action n _
    _ = Φ (scaleRayParameter a ha.le t) := congrArg Φ.toFun hscaleCommute

/-! ## The common invariant tail core -/

private theorem rayScaleAction_tailImage
    {p : I} (Φ : RayChart p) {T : IntervalMap} {a : ℝ}
    (hT_action : RayScaleAction Φ T a) (start : RayParameter) :
    T '' Φ.tailImage start =
      Φ.tailImage (scaleRayParameter a hT_action.scale_pos.le start) := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨scaleRayParameter a hT_action.scale_pos.le t, ?_,
      (hT_action.equivariant t).symm⟩
    exact mul_le_mul_of_nonneg_left ht hT_action.scale_pos.le
  · rintro x ⟨u, hu, rfl⟩
    let t : RayParameter :=
      ⟨(u : ℝ) / a, div_nonneg u.property hT_action.scale_pos.le⟩
    have hstart : start ≤ t := by
      change (start : ℝ) ≤ (u : ℝ) / a
      apply (le_div_iff₀ hT_action.scale_pos).2
      change a * (start : ℝ) ≤ (u : ℝ) at hu
      simpa [mul_comm] using hu
    have hscale :
        scaleRayParameter a hT_action.scale_pos.le t = u := by
      apply Subtype.ext
      change a * ((u : ℝ) / a) = (u : ℝ)
      calc
        a * ((u : ℝ) / a) = ((u : ℝ) / a) * a := mul_comm _ _
        _ = (u : ℝ) := div_mul_cancel₀ _ hT_action.scale_pos.ne'
    refine ⟨Φ t, ⟨t, hstart, rfl⟩, ?_⟩
    rw [hT_action.equivariant t, hscale]

private theorem rayScaleAction_tailClosure
    {p : I} (Φ : RayChart p) {T : IntervalMap} {a : ℝ}
    (hT_continuous : Continuous T)
    (hT_action : RayScaleAction Φ T a) (start : RayParameter) :
    T '' Φ.tailClosure start =
      Φ.tailClosure (scaleRayParameter a hT_action.scale_pos.le start) := by
  have himage := rayScaleAction_tailImage Φ hT_action start
  apply Set.Subset.antisymm
  · exact (image_closure_subset_closure_image hT_continuous).trans_eq
      (congrArg closure himage)
  · apply closure_minimal
    · rw [← himage]
      exact Set.image_mono subset_closure
    · exact (isClosed_closure.isCompact.image hT_continuous).isClosed

private theorem rayTailClosure_antitone {p : I} (Φ : RayChart p) :
    Antitone Φ.tailClosure := by
  intro s t hst
  exact closure_mono (Set.image_mono (Set.Ici_subset_Ici.mpr hst))

private theorem rayScaleAction_tailCore
    {p : I} (Φ : RayChart p) {T : IntervalMap} {a : ℝ}
    (hT_continuous : Continuous T)
    (hT_action : RayScaleAction Φ T a) :
    T '' Φ.tailCore = Φ.tailCore := by
  have htailAntitone := rayTailClosure_antitone Φ
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    rw [RayChart.tailCore, Set.mem_iInter]
    intro start
    let pre : RayParameter :=
      ⟨(start : ℝ) / a,
        div_nonneg start.property hT_action.scale_pos.le⟩
    have hscale :
        scaleRayParameter a hT_action.scale_pos.le pre = start := by
      apply Subtype.ext
      change a * ((start : ℝ) / a) = (start : ℝ)
      calc
        a * ((start : ℝ) / a) = ((start : ℝ) / a) * a := mul_comm _ _
        _ = (start : ℝ) := div_mul_cancel₀ _ hT_action.scale_pos.ne'
    have hypre : y ∈ Φ.tailClosure pre :=
      Set.mem_iInter.mp hy pre
    have hyimage : T y ∈ T '' Φ.tailClosure pre := ⟨y, hypre, rfl⟩
    rw [rayScaleAction_tailClosure Φ hT_continuous hT_action pre,
      hscale] at hyimage
    exact hyimage
  · intro x hx
    let E : RayParameter → Set I := fun start ↦
      T ⁻¹' {x} ∩ Φ.tailClosure start
    have hEnonempty : ∀ start, (E start).Nonempty := by
      intro start
      have hxscaled : x ∈ Φ.tailClosure
          (scaleRayParameter a hT_action.scale_pos.le start) :=
        Set.mem_iInter.mp hx _
      rw [← rayScaleAction_tailClosure Φ hT_continuous hT_action start]
        at hxscaled
      obtain ⟨y, hy, hTy⟩ := hxscaled
      exact ⟨y, by simpa [E, hTy] using hy⟩
    have hEdirected : Directed (· ⊇ ·) E := by
      intro s t
      refine ⟨max s t, ?_, ?_⟩
      · exact Set.inter_subset_inter_right _
          (htailAntitone (le_max_left s t))
      · exact Set.inter_subset_inter_right _
          (htailAntitone (le_max_right s t))
    have hEclosed : ∀ start, IsClosed (E start) := by
      intro start
      exact (isClosed_singleton.preimage hT_continuous).inter isClosed_closure
    have hEcompact : ∀ start, IsCompact (E start) := by
      intro start
      exact isCompact_univ.of_isClosed_subset (hEclosed start) (Set.subset_univ _)
    obtain ⟨y, hy⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        E hEdirected hEnonempty hEcompact hEclosed
    refine ⟨y, ?_, ?_⟩
    · rw [RayChart.tailCore, Set.mem_iInter]
      intro start
      exact (Set.mem_iInter.mp hy start).2
    · exact Set.mem_singleton_iff.mp (Set.mem_iInter.mp hy rayOrigin).1

/--
Closed tail images are compact intervals, and the intersection of all of them
is a nonempty compact interval on which both scale actors act onto.  The final
two equalities are stronger than mere forward invariance.
-/
theorem commonInvariant_rayTail_extraction
    {p : I} (Φ : RayChart p)
    (A B : IntervalMap) (a b : ℝ)
    (hA_continuous : Continuous A)
    (hB_continuous : Continuous B)
    (hA_action : RayScaleAction Φ A a)
    (hB_action : RayScaleAction Φ B b) :
    ∃ Ω : ClosedSubinterval,
      (∀ start : RayParameter,
        ∃ C : ClosedSubinterval, C.carrier = Φ.tailClosure start) ∧
      Ω.carrier = Φ.tailCore ∧
      A '' Ω.carrier = Ω.carrier ∧
      B '' Ω.carrier = Ω.carrier ∧
      IsCommonInvariantCore A B Ω := by
  have htailNonempty : ∀ start : RayParameter,
      (Φ.tailClosure start).Nonempty := by
    intro start
    exact ⟨Φ start, subset_closure
      ⟨start, Set.mem_Ici.mpr le_rfl, rfl⟩⟩
  have htailConnected : ∀ start : RayParameter,
      IsConnected (Φ.tailClosure start) := by
    intro start
    let liftNonneg : ℝ → RayParameter :=
      fun x ↦ ⟨max 0 x, le_max_left 0 x⟩
    have hliftContinuous : Continuous liftNonneg :=
      (continuous_const.max continuous_id).subtype_mk _
    have hliftImage :
        liftNonneg '' Set.Ici (start : ℝ) = Set.Ici start := by
      apply Set.Subset.antisymm
      · rintro y ⟨x, hx, rfl⟩
        exact hx.trans (le_max_right 0 x)
      · intro y hy
        refine ⟨(y : ℝ), hy, ?_⟩
        apply Subtype.ext
        simp [liftNonneg, max_eq_right y.property]
    have hdomain : IsConnected (Set.Ici start) := by
      rw [← hliftImage]
      exact isConnected_Ici.image liftNonneg hliftContinuous.continuousOn
    have himage : IsConnected (Φ.toFun '' Set.Ici start) :=
      hdomain.image Φ.toFun Φ.continuous_toFun.continuousOn
    exact himage.closure
  have htailClosed : ∀ start : RayParameter,
      IsClosed (Φ.tailClosure start) := fun _ ↦ isClosed_closure
  have htailCompact : ∀ start : RayParameter,
      IsCompact (Φ.tailClosure start) := by
    intro start
    exact isCompact_univ.of_isClosed_subset (htailClosed start) (Set.subset_univ _)
  have htailIntervals : ∀ start : RayParameter,
      ∃ C : ClosedSubinterval, C.carrier = Φ.tailClosure start := by
    intro start
    have heq : Φ.tailClosure start =
        Set.Icc (sInf (Φ.tailClosure start)) (sSup (Φ.tailClosure start)) :=
      eq_Icc_of_connected_compact (htailConnected start) (htailCompact start)
    have hle : sInf (Φ.tailClosure start) ≤ sSup (Φ.tailClosure start) := by
      have hn := htailNonempty start
      rw [heq] at hn
      exact Set.nonempty_Icc.mp hn
    let C : ClosedSubinterval :=
      { left := sInf (Φ.tailClosure start)
        right := sSup (Φ.tailClosure start)
        left_le_right := hle }
    exact ⟨C, heq.symm⟩
  have hcoreNonempty : Φ.tailCore.Nonempty := by
    exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      Φ.tailClosure (rayTailClosure_antitone Φ).directed_ge
      htailNonempty htailCompact htailClosed
  have hcoreClosed : IsClosed Φ.tailCore :=
    isClosed_iInter htailClosed
  have hcoreCompact : IsCompact Φ.tailCore :=
    isCompact_univ.of_isClosed_subset hcoreClosed (Set.subset_univ _)
  have hcoreOrdConnected : Set.OrdConnected Φ.tailCore := by
    exact Set.ordConnected_iInter fun start ↦
      (htailConnected start).2.ordConnected
  have hcoreConnected : IsConnected Φ.tailCore :=
    ⟨hcoreNonempty, hcoreOrdConnected.isPreconnected⟩
  have hcoreEq : Φ.tailCore =
      Set.Icc (sInf Φ.tailCore) (sSup Φ.tailCore) :=
    eq_Icc_of_connected_compact hcoreConnected hcoreCompact
  have hcoreLe : sInf Φ.tailCore ≤ sSup Φ.tailCore := by
    rw [hcoreEq] at hcoreNonempty
    exact Set.nonempty_Icc.mp hcoreNonempty
  let Ω : ClosedSubinterval :=
    { left := sInf Φ.tailCore
      right := sSup Φ.tailCore
      left_le_right := hcoreLe }
  have hΩcarrier : Ω.carrier = Φ.tailCore := hcoreEq.symm
  have hAeq : A '' Ω.carrier = Ω.carrier := by
    rw [hΩcarrier]
    exact rayScaleAction_tailCore Φ hA_continuous hA_action
  have hBeq : B '' Ω.carrier = Ω.carrier := by
    rw [hΩcarrier]
    exact rayScaleAction_tailCore Φ hB_continuous hB_action
  refine ⟨Ω, htailIntervals, hΩcarrier, hAeq, hBeq, ?_⟩
  constructor
  · intro x hx
    have hximage : A x ∈ A '' Ω.carrier := ⟨x, hx, rfl⟩
    rwa [hAeq] at hximage
  · intro x hx
    have hximage : B x ∈ B '' Ω.carrier := ⟨x, hx, rfl⟩
    rwa [hBeq] at hximage

/-! ## Expanding and independent actor scales -/

/-- A finite-order continuous interval map shares a fixed point with every
commuting continuous interval map. -/
private theorem commonFixed_of_commute_of_positive_iterate_eq_id
    {F G : IntervalMap}
    (hF_continuous : Continuous F) (hG_continuous : Continuous G)
    (hcommute : Commute F G) {k : ℕ} (hk : 0 < k)
    (hpower : iterateMap F k = id) :
    HasCommonFixedPoint F G := by
  have hiterate_injective : Function.Injective (iterateMap F k) := by
    rw [hpower]
    exact Function.injective_id
  have hF_injective : Function.Injective F := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    intro x y hxy
    apply hiterate_injective
    simp only [iterateMap, Function.iterate_succ_apply]
    rw [hxy]
  rcases hF_continuous.strictMono_of_inj hF_injective with hmono | hanti
  · have hF_id : F = id := by
      funext x
      change F x = x
      have hkx : (F^[k]) x = x := by
        change iterateMap F k x = x
        rw [hpower]
        rfl
      rcases lt_trichotomy (F x) x with hlt | heq | hgt
      · have hbad : (F^[k]) x < (F^[0]) x :=
          hmono.strictAnti_iterate_of_map_lt hlt hk
        exfalso
        simpa [hkx] using hbad
      · exact heq
      · have hbad : (F^[0]) x < (F^[k]) x :=
          hmono.strictMono_iterate_of_lt_map hgt hk
        exfalso
        simpa [hkx] using hbad
    exact IntervalMap.hasCommonFixedPoint_of_eq_id hG_continuous hF_id
  · obtain ⟨x, hx⟩ := IntervalMap.exists_fixedPoint hF_continuous
    have hunique : ∀ y : I, IsFixedPoint F y → y = x := by
      intro y hy
      by_contra hyx
      rcases lt_or_gt_of_ne hyx with hyxlt | hxylt
      · have hcontra := hanti hyxlt
        rw [hx, hy] at hcontra
        exact (not_lt_of_ge hyxlt.le) hcontra
      · have hcontra := hanti hxylt
        rw [hx, hy] at hcontra
        exact (not_lt_of_ge hxylt.le) hcontra
    refine ⟨x, hx, ?_⟩
    apply hunique
    calc
      F (G x) = G (F x) := hcommute x
      _ = G x := congrArg G hx

/-- A scale-one action on a surjective ray chart is the identity map. -/
private theorem eq_id_of_rayScaleAction_scale_eq_one
    {p : I} (Φ : RayChart p) {T : IntervalMap} {a : ℝ}
    (hT_action : RayScaleAction Φ T a) (ha : a = 1) :
    T = id := by
  funext x
  obtain ⟨t, rfl⟩ := Φ.surjective_toFun x
  rw [hT_action.equivariant]
  have hscale :
      scaleRayParameter a hT_action.scale_pos.le t = t := by
    apply Subtype.ext
    change a * (t : ℝ) = (t : ℝ)
    rw [ha, one_mul]
  rw [hscale]
  rfl

/--
An onto map commuting with the locally eventually onto deck actor cannot act
on its surjective ray by a nontrivial contraction.  The nontriviality
assumption excludes the scale-one case supplied separately by the irrational
orbit-circle alternative.
-/
theorem globalScale_gt_one_of_onto_commuting_actor
    {p : I} (Φ : RayChart p)
    {W T : IntervalMap} {lambdaScale a : ℝ}
    (hW_continuous : Continuous W)
    (hT_continuous : Continuous T)
    (hT_onto : IsOnto T)
    (hcommute : Commute T W)
    (hLambda : 1 < lambdaScale)
    (hW_action : RayScaleAction Φ W lambdaScale)
    (hT_action : RayScaleAction Φ T a)
    (ha_ne_one : a ≠ 1)
    (hlocalCover :
      ∀ q : I, p < q →
        ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ) :
    1 < a := by
  by_contra ha_not_gt
  have ha_le_one : a ≤ 1 := le_of_not_gt ha_not_gt
  have ha_lt_one : a < 1 := lt_of_le_of_ne ha_le_one ha_ne_one
  let ε : ℝ := Φ.initialRadius / 2
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith [Φ.initialRadius_pos]
  have hεradius : ε < Φ.initialRadius := by
    dsimp [ε]
    linarith [Φ.initialRadius_pos]
  let tε : RayParameter := ⟨ε, hεpos.le⟩
  have horigin_mem : rayOrigin ∈ rayInitialSegment Φ.initialRadius := by
    exact Φ.initialRadius_pos
  have htε_mem : tε ∈ rayInitialSegment Φ.initialRadius := by
    exact hεradius
  have horigin_lt : rayOrigin < tε := by
    exact hεpos
  have hp_lt : p < Φ tε := by
    calc
      p = Φ rayOrigin := Φ.map_origin.symm
      _ < Φ tε := Φ.strictMonoOn_initial horigin_mem htε_mem horigin_lt
  obtain ⟨n, hncover⟩ := hlocalCover (Φ tε) hp_lt
  let g : RayParameter → I := fun t ↦ iterateMap W n (Φ t)
  have hg_continuous : Continuous g :=
    (IntervalMap.continuous_iterate hW_continuous n).comp Φ.continuous_toFun
  have hscale_origin :
      scaleRayParameter (lambdaScale ^ n)
          (pow_nonneg hW_action.scale_pos.le n) rayOrigin = rayOrigin := by
    apply Subtype.ext
    change lambdaScale ^ n * 0 = 0
    ring
  have hg_origin : g rayOrigin = p := by
    dsimp [g]
    rw [rayScaleAction_iterate Φ hW_action n rayOrigin, hscale_origin,
      Φ.map_origin]
  have hright_nhds : Set.Iio rightEndpoint ∈ nhds p :=
    IsOpen.mem_nhds isOpen_Iio Φ.base_lt_rightEndpoint
  have hpreimage_nhds : g ⁻¹' Set.Iio rightEndpoint ∈ nhds rayOrigin := by
    apply hg_continuous.continuousAt
    simpa [hg_origin] using hright_nhds
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp hpreimage_nhds
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hδpos hεpos) ha_lt_one
  have hpow_small : a ^ k * ε < δ := by
    exact (lt_div_iff₀ hεpos).mp hk
  have hchart_cover :
      Set.Icc p (Φ tε) ⊆ Φ.toFun '' Set.Icc rayOrigin tε := by
    exact initialChart_Icc_subset_image Φ hεpos hεradius
  have hright_avoided :
      rightEndpoint ∉
        iterateMap W n '' (iterateMap T k '' Set.Icc p (Φ tε)) := by
    rintro ⟨_, ⟨x, hx, rfl⟩, hright⟩
    obtain ⟨t, ht, htx⟩ := hchart_cover hx
    subst x
    let u : RayParameter :=
      scaleRayParameter (a ^ k) (pow_nonneg hT_action.scale_pos.le k) t
    have hu_le : (u : ℝ) ≤ a ^ k * ε := by
      exact mul_le_mul_of_nonneg_left ht.2
        (pow_nonneg hT_action.scale_pos.le k)
    have hu_dist : dist u rayOrigin < δ := by
      change dist (u : ℝ) 0 < δ
      rw [Real.dist_eq, sub_zero, abs_of_nonneg u.property]
      exact hu_le.trans_lt hpow_small
    have hgu : g u ∈ Set.Iio rightEndpoint :=
      hδball (Metric.mem_ball.mpr hu_dist)
    have hTk : iterateMap T k (Φ t) = Φ u := by
      exact rayScaleAction_iterate Φ hT_action k t
    rw [hTk] at hright
    exact (ne_of_lt hgu) hright
  have hiter_commute : Commute (iterateMap W n) (iterateMap T k) := by
    exact IntervalMap.commute_iterates hcommute.symm n k
  have hswap :
      iterateMap W n '' (iterateMap T k '' Set.Icc p (Φ tε)) =
        iterateMap T k '' (iterateMap W n '' Set.Icc p (Φ tε)) := by
    rw [Set.image_image, Set.image_image]
    exact congrArg (fun f : IntervalMap ↦ f '' Set.Icc p (Φ tε))
      (funext hiter_commute.eq)
  have hTk_univ : iterateMap T k '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, hx⟩ := IntervalMap.surjective_iterate hT_onto k y
    exact ⟨x, Set.mem_univ x, hx⟩
  have hall :
      iterateMap W n '' (iterateMap T k '' Set.Icc p (Φ tε)) =
        Set.univ := by
    rw [hswap, hncover, hTk_univ]
  apply hright_avoided
  rw [hall]
  exact Set.mem_univ rightEndpoint

/--
In the absence of a common fixed point, the two actor scales are nontrivial
and multiplicatively independent.  Surjectivity of the ray turns equality of
scale powers into equality of positive iterates of `P` and `Q`.
-/
theorem scaleFactors_nontrivial_and_multiplicativelyIndependent
    {p : I} (Φ : RayChart p)
    (P Q A B : IntervalMap) (a b : ℝ) (L : ℕ)
    (hP_continuous : Continuous P)
    (hQ_continuous : Continuous Q)
    (hcommute : Commute P Q)
    (hnoCommon : ¬HasCommonFixedPoint P Q)
    (hL : 0 < L)
    (hA : A = iterateMap P L)
    (hB : B = iterateMap Q L)
    (hA_action : RayScaleAction Φ A a)
    (hB_action : RayScaleAction Φ B b) :
    a ≠ 1 ∧ b ≠ 1 ∧ MultiplicativelyIndependent a b := by
  have ha_ne_one : a ≠ 1 := by
    intro ha
    have hA_id : A = id :=
      eq_id_of_rayScaleAction_scale_eq_one Φ hA_action ha
    have hP_power : iterateMap P L = id := hA.symm.trans hA_id
    exact hnoCommon
      (commonFixed_of_commute_of_positive_iterate_eq_id
        hP_continuous hQ_continuous hcommute hL hP_power)
  have hb_ne_one : b ≠ 1 := by
    intro hb
    have hB_id : B = id :=
      eq_id_of_rayScaleAction_scale_eq_one Φ hB_action hb
    have hQ_power : iterateMap Q L = id := hB.symm.trans hB_id
    obtain ⟨x, hxQ, hxP⟩ :=
      commonFixed_of_commute_of_positive_iterate_eq_id
        hQ_continuous hP_continuous hcommute.symm hL hQ_power
    exact hnoCommon ⟨x, hxP, hxQ⟩
  refine ⟨ha_ne_one, hb_ne_one, ?_⟩
  intro m n hm hn hab
  have hAB_power : iterateMap A m = iterateMap B n := by
    funext x
    obtain ⟨t, rfl⟩ := Φ.surjective_toFun x
    rw [rayScaleAction_iterate Φ hA_action m t,
      rayScaleAction_iterate Φ hB_action n t]
    apply congrArg Φ.toFun
    apply Subtype.ext
    change a ^ m * (t : ℝ) = b ^ n * (t : ℝ)
    rw [hab]
  have hPQ_power : iterateMap P (L * m) = iterateMap Q (L * n) := by
    simpa [hA, hB, iterateMap, Function.iterate_mul] using hAB_power
  exact hnoCommon (common_positive_iterate hP_continuous hQ_continuous
    hcommute (Nat.mul_pos hL hm) (Nat.mul_pos hL hn) hPQ_power)

/-! ## Full tail core in the least normalized counterexample -/

/-- A fixed point of an expanding ray actor is either the ray base or belongs
to every closed ray tail. -/
theorem fixedPoint_eq_base_or_mem_tailCore
    {p : I} (Phi : RayChart p) {T : IntervalMap} {a : ℝ}
    (hT_action : RayScaleAction Phi T a) (ha : 1 < a)
    {x : I} (hx : IsFixedPoint T x) :
    x = p ∨ x ∈ Phi.tailCore := by
  obtain ⟨t, ht⟩ := Phi.surjective_toFun x
  by_cases htzero : (t : ℝ) = 0
  · left
    have htOrigin : t = rayOrigin := by
      apply Subtype.ext
      exact htzero
    calc
      x = Phi t := ht.symm
      _ = Phi rayOrigin := congrArg Phi.toFun htOrigin
      _ = p := Phi.map_origin
  · right
    rw [RayChart.tailCore, Set.mem_iInter]
    intro start
    apply subset_closure
    have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property (Ne.symm htzero)
    obtain ⟨n, hn⟩ :=
      pow_unbounded_of_one_lt ((start : ℝ) / (t : ℝ)) ha
    let scaled : RayParameter :=
      scaleRayParameter (a ^ n) (pow_nonneg hT_action.scale_pos.le n) t
    have hstartScaled : start ≤ scaled := by
      change (start : ℝ) ≤ a ^ n * (t : ℝ)
      exact ((div_lt_iff₀ htpos).mp hn).le
    refine ⟨scaled, hstartScaled, ?_⟩
    calc
      Phi scaled = iterateMap T n (Phi t) :=
        (rayScaleAction_iterate Phi hT_action n t).symm
      _ = iterateMap T n x := congrArg (iterateMap T n) ht
      _ = x := Function.iterate_fixed hx n

/-- A continuous self-map carrying a nondegenerate interval onto itself has
two distinct fixed points of its square. -/
theorem exists_two_fixedPoints_square_of_interval_surjection
    (T : IntervalMap) (J : ClosedSubinterval)
    (hT : Continuous T)
    (honto : T '' J.carrier = J.carrier)
    (hJnondegenerate : J.Nondegenerate) :
    ∃ x ∈ J.carrier, ∃ y ∈ J.carrier,
      x ≠ y ∧ IsFixedPoint (iterateMap T 2) x ∧
        IsFixedPoint (iterateMap T 2) y := by
  have hmaps : MapsTo T J.carrier J.carrier := by
    intro x hx
    rw [← honto]
    exact ⟨x, hx, rfl⟩
  obtain ⟨z, hzJ, hzfix⟩ :=
    exists_mem_Icc_isFixedPt_of_mapsTo hT.continuousOn
      J.left_le_right hmaps
  have hzg : IsFixedPoint (iterateMap T 2) z := by
    exact Function.iterate_fixed hzfix 2
  suffices hsecond : ∃ y ∈ J.carrier,
      y ≠ z ∧ IsFixedPoint (iterateMap T 2) y by
    obtain ⟨y, hyJ, hyz, hyfix⟩ := hsecond
    exact ⟨z, hzJ, y, hyJ, hyz.symm, hzg, hyfix⟩
  by_contra hnoSecond
  push Not at hnoSecond
  have hgUnique : ∀ x ∈ J.carrier,
      IsFixedPoint (iterateMap T 2) x → x = z := by
    intro x hxJ hxg
    by_contra hxz
    exact hnoSecond x hxJ hxz hxg
  have hTUnique : ∀ x ∈ J.carrier, IsFixedPoint T x → x = z := by
    intro x hxJ hxT
    exact hgUnique x hxJ (Function.iterate_fixed hxT 2)
  have hgContinuous : Continuous (iterateMap T 2) :=
    hT.iterate 2
  have hgMaps : MapsTo (iterateMap T 2) J.carrier J.carrier := by
    intro x hx
    exact hmaps (hmaps hx)
  have hTleft : J.left ≤ T J.left :=
    (hmaps (Set.left_mem_Icc.mpr J.left_le_right)).1
  have hTright : T J.right ≤ J.right :=
    (hmaps (Set.right_mem_Icc.mpr J.left_le_right)).2
  have hgleft : J.left ≤ iterateMap T 2 J.left :=
    (hgMaps (Set.left_mem_Icc.mpr J.left_le_right)).1
  have hgright : iterateMap T 2 J.right ≤ J.right :=
    (hgMaps (Set.right_mem_Icc.mpr J.left_le_right)).2
  have hTmovesLeft : ∀ x ∈ J.carrier, x < z → x < T x := by
    intro x hxJ hxz
    by_contra hnot
    have hTxle : T x ≤ x := le_of_not_gt hnot
    obtain ⟨w, hw, hwfix⟩ :=
      exists_mem_Icc_isFixedPt hT.continuousOn hxJ.1 hTleft hTxle
    have hwJ : w ∈ J.carrier :=
      ⟨hw.1, hw.2.trans hxJ.2⟩
    have hwz : w = z := hTUnique w hwJ hwfix
    exact (not_le_of_gt hxz) (hwz ▸ hw.2)
  have hTmovesRight : ∀ x ∈ J.carrier, z < x → T x < x := by
    intro x hxJ hzx
    by_contra hnot
    have hxle : x ≤ T x := le_of_not_gt hnot
    obtain ⟨w, hw, hwfix⟩ :=
      exists_mem_Icc_isFixedPt hT.continuousOn hxJ.2 hxle hTright
    have hwJ : w ∈ J.carrier :=
      ⟨hxJ.1.trans hw.1, hw.2⟩
    have hwz : w = z := hTUnique w hwJ hwfix
    exact (not_le_of_gt hzx) (hwz ▸ hw.1)
  have hgmovesLeft : ∀ x ∈ J.carrier, x < z →
      x < iterateMap T 2 x := by
    intro x hxJ hxz
    by_contra hnot
    have hgxle : iterateMap T 2 x ≤ x := le_of_not_gt hnot
    obtain ⟨w, hw, hwfix⟩ :=
      exists_mem_Icc_isFixedPt hgContinuous.continuousOn
        hxJ.1 hgleft hgxle
    have hwJ : w ∈ J.carrier :=
      ⟨hw.1, hw.2.trans hxJ.2⟩
    have hwz : w = z := hgUnique w hwJ hwfix
    exact (not_le_of_gt hxz) (hwz ▸ hw.2)
  have hzltRight : z < J.right := by
    by_contra hnot
    have hrightle : J.right ≤ z := le_of_not_gt hnot
    have hzright : z = J.right := le_antisymm hzJ.2 hrightle
    subst z
    have hleftImage : J.left ∈ T '' J.carrier := by
      rw [honto]
      exact Set.left_mem_Icc.mpr J.left_le_right
    obtain ⟨v, hvJ, hv⟩ := hleftImage
    have hvne : v ≠ J.right := by
      intro hvright
      subst v
      exact hJnondegenerate.ne' (hzfix.symm.trans hv)
    have hvlt : v < J.right := lt_of_le_of_ne hvJ.2 hvne
    have hmove := hTmovesLeft v hvJ hvlt
    rw [hv] at hmove
    exact (not_lt_of_ge hvJ.1) hmove
  have hleftltz : J.left < z := by
    by_contra hnot
    have hzle : z ≤ J.left := le_of_not_gt hnot
    have hzleft : z = J.left := le_antisymm hzle hzJ.1
    subst z
    have hrightImage : J.right ∈ T '' J.carrier := by
      rw [honto]
      exact Set.right_mem_Icc.mpr J.left_le_right
    obtain ⟨u, huJ, hu⟩ := hrightImage
    have hune : u ≠ J.left := by
      intro huleft
      subst u
      exact hJnondegenerate.ne (hzfix.symm.trans hu)
    have hult : J.left < u := lt_of_le_of_ne huJ.1 hune.symm
    have hmove := hTmovesRight u huJ hult
    rw [hu] at hmove
    exact (not_lt_of_ge huJ.2) hmove
  have hrightImage : J.right ∈ T '' J.carrier := by
    rw [honto]
    exact Set.right_mem_Icc.mpr J.left_le_right
  obtain ⟨u, huJ, hu⟩ := hrightImage
  have hultZ : u < z := by
    rcases lt_trichotomy u z with huz | huz | hzu
    · exact huz
    · subst u
      exact (hzltRight.ne (hzfix.symm.trans hu)).elim
    · have hTu : T u < u := hTmovesRight u huJ hzu
      exact ((hu ▸ hTu).trans_le huJ.2).false.elim
  have hleftImage : J.left ∈ T '' J.carrier := by
    rw [honto]
    exact Set.left_mem_Icc.mpr J.left_le_right
  obtain ⟨v, hvJ, hv⟩ := hleftImage
  have hzltV : z < v := by
    rcases lt_trichotomy z v with hzv | hzv | hvz
    · exact hzv
    · subst v
      exact (hleftltz.ne' (hzfix.symm.trans hv)).elim
    · have hvT : v < T v := hTmovesLeft v hvJ hvz
      exact (hvJ.1.trans_lt (hv ▸ hvT)).false.elim
  have hvBetween : v ∈ Set.Icc (T z) (T u) := by
    rw [hzfix, hu]
    exact ⟨hzltV.le, hvJ.2⟩
  obtain ⟨w, hw, hTw⟩ :=
    intermediate_value_Icc' hultZ.le hT.continuousOn hvBetween
  have hwJ : w ∈ J.carrier :=
    ⟨huJ.1.trans hw.1, hw.2.trans hzJ.2⟩
  have hwltZ : w < z := by
    exact lt_of_le_of_ne hw.2 fun hwz ↦ by
      subst w
      exact hzltV.ne (hzfix.symm.trans hTw)
  have hgw : iterateMap T 2 w = J.left := by
    change T (T w) = J.left
    rw [hTw, hv]
  have hwltg := hgmovesLeft w hwJ hwltZ
  rw [hgw] at hwltg
  exact (not_lt_of_ge (huJ.1.trans hw.1)) hwltg
/-- A full tail core is equivalent to density of every individual late tail. -/
theorem denseTails_of_tailCore_eq_univ
    {p : I} (Φ : RayChart p)
    (hfull : Φ.tailCore = Set.univ) :
    Φ.HasDenseTails := by
  intro start
  apply Set.eq_univ_of_forall
  intro x
  have hxcore : x ∈ Φ.tailCore := by
    rw [hfull]
    exact Set.mem_univ x
  exact Set.mem_iInter.mp hxcore start

/-! ## Boundary lifts and exactness -/

/--
Dense tails and an expanding, locally increasing scale actor provide a
positive parameter lift of the base approached through the selected side.
The endpoint and initial monotonicity assumptions are carried by `RayChart`;
the corresponding monotonicity of `R` is stated explicitly.
-/
theorem exists_positiveBoundaryLift
    {p : I} (Φ : RayChart p)
    (R : IntervalMap) (Λ : ℝ)
    (hR_continuous : Continuous R)
    (hR_onto : IsOnto R)
    (hR_fixed : IsFixedPoint R p)
    (hR_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn R (Set.Icc p q))
    (hΛ : 1 < Λ)
    (hR_action : RayScaleAction Φ R Λ)
    (hdense : Φ.HasDenseTails) :
    ∃ tstar : RayParameter, Φ.IsPositiveBoundaryLift tstar := by
  let liftNonneg : ℝ → RayParameter :=
    fun x ↦ ⟨max 0 x, le_max_left 0 x⟩
  have hliftContinuous : Continuous liftNonneg :=
    (continuous_const.max continuous_id).subtype_mk _
  have hlift_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
      liftNonneg x = ⟨x, hx⟩ := by
    apply Subtype.ext
    simp [liftNonneg, hx]
  let ψ : ℝ → I := Φ.toFun ∘ liftNonneg
  have hψContinuous : Continuous ψ :=
    Φ.continuous_toFun.comp hliftContinuous
  have hboundary_of_return :
      ∀ t₀ : RayParameter, 0 < (t₀ : ℝ) → Φ t₀ = p →
        ∃ tstar : RayParameter, Φ.IsPositiveBoundaryLift tstar := by
    intro t₀ ht₀pos hΦt₀
    let δ : ℝ := min Φ.initialRadius (t₀ : ℝ) / 2
    have hminpos : 0 < min Φ.initialRadius (t₀ : ℝ) :=
      lt_min Φ.initialRadius_pos ht₀pos
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    have hδltmin : δ < min Φ.initialRadius (t₀ : ℝ) := by
      dsimp [δ]
      exact div_lt_self hminpos (by norm_num)
    have hδradius : δ < Φ.initialRadius :=
      hδltmin.trans_le (min_le_left _ _)
    have hδt₀ : δ < (t₀ : ℝ) :=
      hδltmin.trans_le (min_le_right _ _)
    let τ : RayParameter := ⟨δ, hδpos.le⟩
    have hτmem : τ ∈ rayInitialSegment Φ.initialRadius := hδradius
    have horiginmem : rayOrigin ∈ rayInitialSegment Φ.initialRadius := by
      exact Φ.initialRadius_pos
    have horiginltτ : rayOrigin < τ := by
      exact hδpos
    have hpΦτ : p < Φ τ := by
      exact Φ.map_origin.symm.trans_lt
        (Φ.strictMonoOn_initial horiginmem hτmem horiginltτ)
    have hψδ : ψ δ = Φ τ := by
      change Φ (liftNonneg δ) = Φ τ
      rw [hlift_of_nonneg δ hδpos.le]
    have hψt₀ : ψ (t₀ : ℝ) = p := by
      change Φ (liftNonneg (t₀ : ℝ)) = p
      rw [hlift_of_nonneg (t₀ : ℝ) t₀.property]
      exact hΦt₀
    let Z : Set ℝ := Set.Icc δ (t₀ : ℝ) ∩ ψ ⁻¹' {p}
    have hZcompact : IsCompact Z :=
      isCompact_Icc.inter_right
        (isClosed_singleton.preimage hψContinuous)
    have hZnonempty : Z.Nonempty := by
      refine ⟨(t₀ : ℝ), ⟨hδt₀.le, le_rfl⟩, ?_⟩
      simpa using hψt₀
    obtain ⟨sstar, hsstarZ, hsstar_min⟩ :=
      hZcompact.exists_isLeast hZnonempty
    have hsstar_bounds : sstar ∈ Set.Icc δ (t₀ : ℝ) := hsstarZ.1
    have hψsstar : ψ sstar = p := by
      simpa using hsstarZ.2
    have hsstar_pos : 0 < sstar := hδpos.trans_le hsstar_bounds.1
    let tstar : RayParameter := ⟨sstar, hsstar_pos.le⟩
    have hΦtstar : Φ tstar = p := by
      change Φ ⟨sstar, hsstar_pos.le⟩ = p
      rw [← hlift_of_nonneg sstar hsstar_pos.le]
      exact hψsstar
    have hδstar : δ < sstar :=
      lt_of_le_of_ne hsstar_bounds.1 fun hδeq ↦ by
        have : ψ δ = p := by simpa [hδeq] using hψsstar
        exact hpΦτ.ne' (hψδ ▸ this)
    have hbefore :
        ∀ {s : ℝ}, δ ≤ s → s < sstar → p < ψ s := by
      intro s hδs hsstar
      by_contra hnot
      have hψsle : ψ s ≤ p := le_of_not_gt hnot
      have hpimage : p ∈ ψ '' Set.Icc δ s :=
        intermediate_value_Icc' hδs hψContinuous.continuousOn
          ⟨hψsle, by simpa [hψδ] using hpΦτ.le⟩
      obtain ⟨r, hr, hψr⟩ := hpimage
      have hrZ : r ∈ Z := by
        refine ⟨⟨hr.1, hr.2.trans (hsstar.le.trans hsstar_bounds.2)⟩, ?_⟩
        simpa using hψr
      exact (not_le_of_gt hsstar) ((hsstar_min hrZ).trans hr.2)
    refine ⟨tstar, hsstar_pos, hΦtstar, ?_⟩
    intro ε hε
    have hlower :
        max δ (sstar - ε) < sstar :=
      max_lt hδstar (sub_lt_self _ hε)
    obtain ⟨s, hs_lower, hs_upper⟩ := exists_between hlower
    have hs_nonneg : 0 ≤ s := by
      exact hδpos.le.trans
        ((le_max_left δ (sstar - ε)).trans hs_lower.le)
    let t : RayParameter := ⟨s, hs_nonneg⟩
    have hδs : δ ≤ s :=
      (le_max_left δ (sstar - ε)).trans hs_lower.le
    have hΦt : Φ t = ψ s := by
      change Φ ⟨s, hs_nonneg⟩ = Φ (liftNonneg s)
      rw [hlift_of_nonneg s hs_nonneg]
    refine ⟨t, ?_, ?_⟩
    · change |s - sstar| < ε
      rw [abs_of_neg (sub_neg.mpr hs_upper)]
      have hs_eps : sstar - ε < s :=
        (le_max_right δ (sstar - ε)).trans_lt hs_lower
      linarith
    · rw [hΦt]
      exact hbefore hδs hs_upper

  let δ₀ : ℝ := Φ.initialRadius / 2
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact div_pos Φ.initialRadius_pos (by norm_num)
  have hδ₀radius : δ₀ < Φ.initialRadius := by
    dsimp [δ₀]
    linarith [Φ.initialRadius_pos]
  let τ₀ : RayParameter := ⟨δ₀, hδ₀pos.le⟩
  have hpΦτ₀ : p < Φ τ₀ := by
    exact Φ.map_origin.symm.trans_lt
      (Φ.strictMonoOn_initial Φ.initialRadius_pos hδ₀radius hδ₀pos)
  by_cases hreturn : ∃ t₀ : RayParameter, 0 < (t₀ : ℝ) ∧ Φ t₀ = p
  · obtain ⟨t₀, ht₀pos, hΦt₀⟩ := hreturn
    exact hboundary_of_return t₀ ht₀pos hΦt₀
  · have hnoReturn : ∀ t : RayParameter, 0 < (t : ℝ) → Φ t ≠ p := by
      intro t ht hΦt
      exact hreturn ⟨t, ht, hΦt⟩
    by_cases hpLeft : p = leftEndpoint
    · have hRpre : ∀ x : I, R x = p → x = p := by
        intro x hRx
        obtain ⟨t, rfl⟩ := Φ.surjective_toFun x
        have hscaled :
            Φ (scaleRayParameter Λ hR_action.scale_pos.le t) = p := by
          rw [← hR_action.equivariant]
          exact hRx
        by_cases htzero : (t : ℝ) = 0
        · have ht : t = rayOrigin := by
            apply Subtype.ext
            exact htzero
          simpa [ht] using Φ.map_origin
        · have htpos : 0 < (t : ℝ) :=
            lt_of_le_of_ne t.property (Ne.symm htzero)
          have hscaledPos :
              0 < (scaleRayParameter Λ hR_action.scale_pos.le t : ℝ) := by
            exact mul_pos hR_action.scale_pos htpos
          exact (hnoReturn _ hscaledPos hscaled).elim

      let δ : ℝ := Φ.initialRadius / (2 * Λ)
      have hΛpos : 0 < Λ := zero_lt_one.trans hΛ
      have hδpos : 0 < δ := by
        dsimp [δ]
        exact div_pos Φ.initialRadius_pos (mul_pos (by norm_num) hΛpos)
      have hΛδ : Λ * δ = Φ.initialRadius / 2 := by
        dsimp [δ]
        field_simp [hΛpos.ne']
      have hΛδradius : Λ * δ < Φ.initialRadius := by
        rw [hΛδ]
        linarith [Φ.initialRadius_pos]
      have hδradius : δ < Φ.initialRadius := by
        have : δ < Λ * δ := by nlinarith
        exact this.trans hΛδradius
      let u : RayParameter := ⟨δ, hδpos.le⟩
      let q₀ : I := Φ u
      have hpq₀ : p < q₀ := by
        exact Φ.map_origin.symm.trans_lt
          (Φ.strictMonoOn_initial Φ.initialRadius_pos hδradius hδpos)
      have hRpush : ∀ x ∈ Set.Ioc p q₀, x < R x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc p q₀ := ⟨hx.1.le, hx.2⟩
        have hximage := initialChart_Icc_subset_image Φ hδpos hδradius hxIcc
        obtain ⟨t, ht, hΦt⟩ := hximage
        have horiginlt : rayOrigin < t :=
          lt_of_le_of_ne ht.1 fun h ↦ by
            have htmap : Φ t = p := h.symm ▸ Φ.map_origin
            exact hx.1.ne' (hΦt.symm.trans htmap)
        have htpos : 0 < (t : ℝ) := horiginlt
        have htscale :
            t < scaleRayParameter Λ hR_action.scale_pos.le t := by
          change (t : ℝ) < Λ * (t : ℝ)
          nlinarith
        have htinitial : t ∈ rayInitialSegment Φ.initialRadius := by
          change (t : ℝ) < Φ.initialRadius
          exact (show (t : ℝ) ≤ δ from ht.2).trans_lt hδradius
        have hscaleinitial :
            scaleRayParameter Λ hR_action.scale_pos.le t ∈
              rayInitialSegment Φ.initialRadius := by
          change Λ * (t : ℝ) < Φ.initialRadius
          exact (mul_le_mul_of_nonneg_left
            (show (t : ℝ) ≤ δ from ht.2) hΛpos.le).trans_lt hΛδradius
        have hstrict :=
          Φ.strictMonoOn_initial htinitial hscaleinitial htscale
        calc
          x = Φ t := hΦt.symm
          _ < Φ (scaleRayParameter Λ hR_action.scale_pos.le t) := hstrict
          _ = R x := by rw [← hR_action.equivariant, hΦt]

      let oneRay : RayParameter := ⟨1, zero_le_one⟩
      let lambdaRay : RayParameter := ⟨Λ, hΛpos.le⟩
      let K : Set I := ψ '' Set.Icc (1 : ℝ) Λ
      let E : Set I := R '' Set.Icc q₀ rightEndpoint
      let S : Set I := K ∪ E
      have hKcompact : IsCompact K :=
        isCompact_Icc.image hψContinuous
      have hEcompact : IsCompact E :=
        isCompact_Icc.image hR_continuous
      have hScompact : IsCompact S := hKcompact.union hEcompact
      have hKnonempty : K.Nonempty := by
        refine ⟨ψ 1, 1, ⟨le_rfl, hΛ.le⟩, rfl⟩
      have hSnonempty : S.Nonempty := hKnonempty.mono Set.subset_union_left
      have hpnotS : p ∉ S := by
        rintro (hpK | hpE)
        · obtain ⟨s, hs, hΦs⟩ := hpK
          have hspos : 0 < s := by
            exact zero_lt_one.trans_le hs.1
          let sr : RayParameter := ⟨s, hspos.le⟩
          have hψs : ψ s = Φ sr := by
            change Φ (liftNonneg s) = Φ sr
            rw [hlift_of_nonneg s hspos.le]
          exact hnoReturn sr hspos (hψs.symm.trans hΦs)
        · obtain ⟨x, hx, hRx⟩ := hpE
          have hxp : x = p := hRpre x hRx
          have : q₀ ≤ p := by simpa [hxp] using hx.1
          exact (not_le_of_gt hpq₀) this
      obtain ⟨m, hmS, hmleast⟩ := hScompact.exists_isLeast hSnonempty
      have hpm : p < m := by
        have hple : p ≤ m := by
          rw [hpLeft]
          exact m.property.1
        exact lt_of_le_of_ne hple fun h ↦ hpnotS (h ▸ hmS)
      have hpmin : p < min m q₀ := lt_min hpm hpq₀
      obtain ⟨v, hpv, hvmin⟩ := exists_between hpmin
      have hvm : v < m := hvmin.trans_le (min_le_left _ _)
      have hvq₀ : v < q₀ := hvmin.trans_le (min_le_right _ _)
      have hKlower : ∀ y ∈ K, v < y := by
        intro y hy
        exact hvm.trans_le (hmleast (Set.mem_union_left E hy))
      have hElower : ∀ y ∈ E, v < y := by
        intro y hy
        exact hvm.trans_le (hmleast (Set.mem_union_right K hy))
      have hback : ∀ x : I, R x < v → x < v := by
        intro x hRxv
        by_cases hxq₀ : x < q₀
        · by_cases hxp : x = p
          · simpa [hxp] using hpv
          · have hpx : p < x := by
              have hple : p ≤ x := by
                rw [hpLeft]
                exact x.property.1
              exact lt_of_le_of_ne hple (Ne.symm hxp)
            exact (hRpush x ⟨hpx, hxq₀.le⟩).trans hRxv
        · have hq₀x : q₀ ≤ x := le_of_not_gt hxq₀
          have hxright : x ≤ rightEndpoint := x.property.2
          have hRxE : R x ∈ E := ⟨x, ⟨hq₀x, hxright⟩, rfl⟩
          exact ((hElower (R x) hRxE).trans hRxv).false.elim
      have hback_iter :
          ∀ n : ℕ, ∀ x : I, iterateMap R n x < v → x < v := by
        intro n
        induction n with
        | zero =>
            intro x hx
            simpa [iterateMap] using hx
        | succ n ih =>
            intro x hx
            apply ih x
            apply hback (iterateMap R n x)
            simpa [iterateMap, Function.iterate_succ_apply'] using hx
      have htailDense : Dense (Φ.tailImage oneRay) :=
        dense_iff_closure_eq.mpr (hdense oneRay)
      obtain ⟨y, hyTail, hyv⟩ := htailDense.exists_mem_open
        isOpen_Iio ⟨p, hpv⟩
      obtain ⟨t, ht, hΦt⟩ := hyTail
      have htone : 1 ≤ (t : ℝ) := ht
      obtain ⟨n, hnlow, hnhigh⟩ := exists_nat_pow_near htone hΛ
      let s : RayParameter :=
        ⟨(t : ℝ) / Λ ^ n,
          div_nonneg t.property (pow_nonneg hΛpos.le n)⟩
      have hone_s : oneRay ≤ s := by
        change 1 ≤ (t : ℝ) / Λ ^ n
        exact (le_div_iff₀ (pow_pos hΛpos n)).2 (by simpa using hnlow)
      have hs_lambda : s ≤ lambdaRay := by
        change (t : ℝ) / Λ ^ n ≤ Λ
        apply (div_le_iff₀ (pow_pos hΛpos n)).2
        rw [← pow_succ']
        exact hnhigh.le
      have hscale :
          scaleRayParameter (Λ ^ n) (pow_nonneg hΛpos.le n) s = t := by
        apply Subtype.ext
        change Λ ^ n * ((t : ℝ) / Λ ^ n) = (t : ℝ)
        field_simp [(pow_pos hΛpos n).ne']
      have hiter : iterateMap R n (Φ s) = Φ t := by
        rw [rayScaleAction_iterate Φ hR_action n s, hscale]
      have hψs : ψ (s : ℝ) = Φ s := by
        change Φ (liftNonneg (s : ℝ)) = Φ s
        rw [hlift_of_nonneg (s : ℝ) s.property]
      have hΦsK : Φ s ∈ K := by
        refine ⟨(s : ℝ), ?_, hψs⟩
        exact ⟨hone_s, hs_lambda⟩
      have hΦs_lt : Φ s < v := by
        apply hback_iter n (Φ s)
        rw [hiter, hΦt]
        exact hyv
      exact ((hKlower (Φ s) hΦsK).trans hΦs_lt).false.elim
    · have hleftp : leftEndpoint < p := by
        have hle : leftEndpoint ≤ p := p.property.1
        exact lt_of_le_of_ne hle (Ne.symm hpLeft)
      have htailDense : Dense (Φ.tailImage τ₀) :=
        dense_iff_closure_eq.mpr (hdense τ₀)
      obtain ⟨y, hyTail, hyp⟩ := htailDense.exists_mem_open
        isOpen_Iio ⟨leftEndpoint, hleftp⟩
      obtain ⟨t, hτ₀t, hΦt⟩ := hyTail
      have hψδ₀ : ψ δ₀ = Φ τ₀ := by
        change Φ (liftNonneg δ₀) = Φ τ₀
        rw [hlift_of_nonneg δ₀ hδ₀pos.le]
      have hψt : ψ (t : ℝ) = Φ t := by
        change Φ (liftNonneg (t : ℝ)) = Φ t
        rw [hlift_of_nonneg (t : ℝ) t.property]
      have hpimage : p ∈ ψ '' Set.Icc δ₀ (t : ℝ) :=
        intermediate_value_Icc' hτ₀t hψContinuous.continuousOn
          ⟨(hψt.trans_lt (hΦt.trans_lt hyp)).le,
            by simpa [hψδ₀] using hpΦτ₀.le⟩
      obtain ⟨r₀, hr₀, hψr₀⟩ := hpimage
      have hr₀pos : 0 < r₀ := hδ₀pos.trans_le hr₀.1
      let t₀ : RayParameter := ⟨r₀, hr₀pos.le⟩
      have hΦt₀ : Φ t₀ = p := by
        change Φ ⟨r₀, hr₀pos.le⟩ = p
        rw [← hlift_of_nonneg r₀ hr₀pos.le]
        exact hψr₀
      exact hboundary_of_return t₀ hr₀pos hΦt₀

/-- Topological exactness rules out every nondegenerate flat interval. -/
theorem noFlatInterval_of_topologicallyExact
    {T : IntervalMap} (hexact : IsTopologicallyExact T) :
    ¬HasFlatInterval T := by
  rintro ⟨J, hJnondegenerate, hJflat⟩
  let U : Set I := Set.Ioo J.left J.right
  have hUopen : IsOpen U := isOpen_Ioo
  have hUnonempty : U.Nonempty := Set.nonempty_Ioo.mpr hJnondegenerate
  obtain ⟨n, hn⟩ := hexact U hUopen hUnonempty
  cases n with
  | zero =>
      have hUuniv : U = Set.univ := by
        simpa [iterateMap] using hn
      have hleftU : J.left ∈ U := by
        rw [hUuniv]
        exact Set.mem_univ J.left
      exact (lt_irrefl J.left hleftU.1)
  | succ n =>
      have hconstant : ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
          iterateMap T (n + 1) x = iterateMap T (n + 1) y := by
        intro x hx y hy
        have hTxy : T x = T y :=
          hJflat ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩
        simpa [iterateMap, Function.iterate_succ_apply] using
          congrArg (T^[n]) hTxy
      have hleftImage : leftEndpoint ∈ iterateMap T (n + 1) '' U := by
        rw [hn]
        exact Set.mem_univ leftEndpoint
      have hrightImage : rightEndpoint ∈ iterateMap T (n + 1) '' U := by
        rw [hn]
        exact Set.mem_univ rightEndpoint
      obtain ⟨x, hxU, hx⟩ := hleftImage
      obtain ⟨y, hyU, hy⟩ := hrightImage
      have hends : leftEndpoint = rightEndpoint := by
        rw [← hx, ← hy]
        exact hconstant hxU hyU
      simpa [leftEndpoint, rightEndpoint] using congrArg Subtype.val hends

private theorem rayScale_log_ratio_irrational
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hindependent : MultiplicativelyIndependent a b) :
    Irrational (Real.log a / Real.log b) := by
  rw [irrational_iff_ne_rational]
  intro r s hs hratio
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hratioPos : 0 < Real.log a / Real.log b := div_pos hloga hlogb
  have hr : r ≠ 0 := by
    intro hr
    have hrcast : (r : ℝ) = 0 := by exact_mod_cast hr
    have hrhs : (r : ℝ) / (s : ℝ) = 0 := by rw [hrcast, zero_div]
    exact (ne_of_gt hratioPos) (hratio.trans hrhs)
  have hcross : (s : ℝ) * Real.log a = (r : ℝ) * Real.log b := by
    field_simp [hlogb.ne', Int.cast_ne_zero.mpr hs] at hratio
    linarith
  have habs : (s.natAbs : ℝ) * Real.log a =
      (r.natAbs : ℝ) * Real.log b := by
    have := congrArg abs hcross
    simpa [abs_mul, abs_of_pos hloga, abs_of_pos hlogb] using this
  have hpows : a ^ s.natAbs = b ^ r.natAbs := by
    have hlogpow : Real.log (a ^ s.natAbs) = Real.log (b ^ r.natAbs) := by
      rw [Real.log_pow, Real.log_pow]
      simpa [mul_comm] using habs
    calc
      a ^ s.natAbs = Real.exp (Real.log (a ^ s.natAbs)) :=
        (Real.exp_log (pow_pos (zero_lt_one.trans ha) _)).symm
      _ = Real.exp (Real.log (b ^ r.natAbs)) := congrArg Real.exp hlogpow
      _ = b ^ r.natAbs := Real.exp_log (pow_pos (zero_lt_one.trans hb) _)
  exact hindependent s.natAbs r.natAbs
    (Int.natAbs_pos.mpr hs) (Int.natAbs_pos.mpr hr) hpows

private theorem exists_zpow_mul_mem_Ioo_of_independent
    {a b l u : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hindependent : MultiplicativelyIndependent a b)
    (hl : 0 < l) (hlu : l < u) :
    ∃ m n : ℤ, a ^ m * b ^ n ∈ Set.Ioo l u := by
  have hirr := rayScale_log_ratio_irrational ha hb hindependent
  have hdense : Dense
      (AddSubgroup.closure {Real.log a, Real.log b} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  have hloglt : Real.log l < Real.log u :=
    Real.strictMonoOn_log hl (hl.trans hlu) hlu
  obtain ⟨x, hxsub, hx⟩ := hdense.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.mpr hloglt)
  change x ∈ AddSubgroup.closure {Real.log a, Real.log b} at hxsub
  rw [AddSubgroup.mem_closure_pair] at hxsub
  obtain ⟨m, n, hmn⟩ := hxsub
  have hexp : Real.exp x = a ^ m * b ^ n := by
    rw [← hmn, zsmul_eq_mul, zsmul_eq_mul, Real.exp_add,
      ← Real.log_zpow, ← Real.log_zpow,
      Real.exp_log (zpow_pos (zero_lt_one.trans ha) _),
      Real.exp_log (zpow_pos (zero_lt_one.trans hb) _)]
  refine ⟨m, n, ?_, ?_⟩
  · rw [← Real.exp_log hl, ← hexp]
    exact Real.exp_lt_exp.mpr hx.1
  · rw [← Real.exp_log (hl.trans hlu), ← hexp]
    exact Real.exp_lt_exp.mpr hx.2

private theorem multiplicativelyIndependent_left_mul
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hindependent : MultiplicativelyIndependent a b) :
    MultiplicativelyIndependent a (a * b) := by
  intro m n hm hn heq
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  by_cases hmn : m ≤ n
  · have hpowle : a ^ m ≤ a ^ n := pow_le_pow_right₀ ha.le hmn
    have halt : a < a * b := by
      nlinarith [mul_pos (zero_lt_one.trans ha) (sub_pos.mpr hb)]
    have hpwlt : a ^ n < (a * b) ^ n :=
      pow_lt_pow_left₀ halt (zero_lt_one.trans ha).le (Nat.ne_of_gt hn)
    exact (hpowle.trans_lt hpwlt).ne heq
  · have hnm : n < m := lt_of_not_ge hmn
    have hfactor : a ^ n * a ^ (m - n) = a ^ m := by
      rw [mul_comm, pow_sub_mul_pow a hnm.le]
    have hcancel : a ^ n * a ^ (m - n) = a ^ n * b ^ n := by
      rw [hfactor, heq, mul_pow]
    have hpoweq : a ^ (m - n) = b ^ n :=
      mul_left_cancel₀ (pow_ne_zero _ ha0) hcancel
    exact hindependent (m - n) n (Nat.sub_pos_of_lt hnm) hn hpoweq

private theorem exists_small_nonzero_log_step
    {a c ε : ℝ} (ha : 1 < a) (hc : 1 < c)
    (hindependent : MultiplicativelyIndependent a c) (hε : 0 < ε) :
    ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
      (n : ℝ) * Real.log a - (k : ℝ) * Real.log c ≠ 0 ∧
      |(n : ℝ) * Real.log a - (k : ℝ) * Real.log c| < ε := by
  let θ : ℝ := Real.log a / Real.log c
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hlogc : 0 < Real.log c := Real.log_pos hc
  have hθ : 0 < θ := div_pos hloga hlogc
  have hirr : Irrational θ := rayScale_log_ratio_irrational ha hc hindependent
  let η : ℝ := min 1 (min θ (ε / Real.log c))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min zero_lt_one (lt_min hθ (div_pos hε hlogc))
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  have hNpos : 0 < N := by
    by_contra hnot
    have hNz : N = 0 := Nat.eq_zero_of_not_pos hnot
    subst N
    norm_num at hN
    exact (not_lt_of_ge
      (min_le_left 1 (min θ (ε / Real.log c)))) hN
  obtain ⟨j, n, hnpos, _hnN, happ⟩ :=
    Real.exists_int_int_abs_mul_sub_le θ hNpos
  have happ_lt : |(n : ℝ) * θ - (j : ℝ)| < η :=
    happ.trans_lt hN
  have hjpos : 0 < j := by
    have hsmallθ : |(n : ℝ) * θ - (j : ℝ)| < θ :=
      happ_lt.trans_le (min_le_of_right_le (min_le_left _ _))
    have hupper := (abs_lt.mp hsmallθ).2
    have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    have : θ ≤ (n : ℝ) * θ := by nlinarith
    exact_mod_cast (show (0 : ℝ) < (j : ℝ) by nlinarith)
  have hncast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnpos.le
  have hjcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hjpos.le
  let D : ℝ := (n : ℝ) * Real.log a - (j : ℝ) * Real.log c
  have hDformula : D = Real.log c * ((n : ℝ) * θ - (j : ℝ)) := by
    dsimp [D, θ]
    field_simp [hlogc.ne']
  have hDsmall : |D| < ε := by
    rw [hDformula, abs_mul, abs_of_pos hlogc]
    have hsmallDiv :
        |(n : ℝ) * θ - (j : ℝ)| < ε / Real.log c :=
      happ_lt.trans_le (min_le_of_right_le (min_le_right _ _))
    exact (lt_div_iff₀' hlogc).mp (by simpa [mul_comm] using hsmallDiv)
  have hDne : D ≠ 0 := by
    intro hDz
    have hratio : θ = (j : ℝ) / (n : ℝ) := by
      dsimp [D] at hDz
      dsimp [θ]
      field_simp [hlogc.ne', Int.cast_ne_zero.mpr hnpos.ne'] at hDz ⊢
      nlinarith
    exact ((irrational_iff_ne_rational θ).mp hirr j n hnpos.ne') hratio
  refine ⟨n.toNat, j.toNat, ?_, ?_, ?_, ?_⟩
  · have hncastInt := Int.toNat_of_nonneg hnpos.le
    omega
  · have hjcastInt := Int.toNat_of_nonneg hjpos.le
    omega
  · simpa [hncast, hjcast, D] using hDne
  · simpa [hncast, hjcast, D] using hDsmall

private theorem exists_large_nat_log_residue
    {a c L U : ℝ} (ha : 1 < a) (hc : 1 < c)
    (hindependent : MultiplicativelyIndependent a c)
    (hL : 0 < L) (hLU : L < U) (hUc : U < Real.log c)
    (N : ℕ) :
    ∃ n k : ℕ, N < k ∧
      L < (n : ℝ) * Real.log a - (k : ℝ) * Real.log c ∧
      (n : ℝ) * Real.log a - (k : ℝ) * Real.log c < U := by
  have hlogc : 0 < Real.log c := Real.log_pos hc
  have hright : 0 < Real.log c - U := sub_pos.mpr hUc
  have hdenom : 0 < (N : ℝ) + 2 := by positivity
  let ε : ℝ := min (U - L)
    (min (L / ((N : ℝ) + 2))
      ((Real.log c - U) / ((N : ℝ) + 2)))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (sub_pos.mpr hLU)
      (lt_min (div_pos hL hdenom) (div_pos hright hdenom))
  obtain ⟨n₀, k₀, hn₀, hk₀, hDne, hDsmall⟩ :=
    exists_small_nonzero_log_step ha hc hindependent hε
  let D : ℝ :=
    (n₀ : ℝ) * Real.log a - (k₀ : ℝ) * Real.log c
  have hDne' : D ≠ 0 := by simpa [D] using hDne
  have hDsmall' : |D| < ε := by simpa [D] using hDsmall
  rcases lt_or_gt_of_ne hDne' with hDneg | hDpos
  · let E : ℝ := -D
    have hEpos : 0 < E := by dsimp [E]; linarith
    have hEgap : E < U - L := by
      have := hDsmall'.trans_le (min_le_left _ _)
      rw [abs_of_neg hDneg] at this
      simpa [E] using this
    have hEleft : E < (Real.log c - U) / ((N : ℝ) + 2) := by
      have := hDsmall'.trans_le
        (min_le_of_right_le (min_le_right _ _))
      rw [abs_of_neg hDneg] at this
      simpa [E] using this
    let q : ℕ := ⌊(Real.log c - U) / E⌋₊ + 1
    have hratio_nonneg : 0 ≤ (Real.log c - U) / E :=
      div_nonneg hright.le hEpos.le
    have hq_lower : Real.log c - U < (q : ℝ) * E := by
      have hfloor := Nat.lt_floor_add_one ((Real.log c - U) / E)
      have hratio_lt : (Real.log c - U) / E < (q : ℝ) := by
        simpa [q, Nat.cast_add, Nat.cast_one] using hfloor
      exact (div_lt_iff₀ hEpos).mp hratio_lt
    have hq_upper : (q : ℝ) * E < Real.log c - L := by
      have hfloor := Nat.floor_le hratio_nonneg
      have hq_le : (q : ℝ) ≤ (Real.log c - U) / E + 1 := by
        dsimp [q]
        push_cast
        linarith
      have hmul_le : (q : ℝ) * E ≤ Real.log c - U + E := by
        have := mul_le_mul_of_nonneg_right hq_le hEpos.le
        field_simp [hEpos.ne'] at this
        nlinarith
      linarith
    have hq_large : N + 1 < q := by
      by_contra hnot
      have hq_le_nat : q ≤ N + 1 := le_of_not_gt hnot
      have hq_le_real : (q : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hq_le_nat
      have hscaled : ((N : ℝ) + 2) * E < Real.log c - U := by
        simpa [mul_comm] using (lt_div_iff₀ hdenom).mp hEleft
      have : (q : ℝ) * E < Real.log c - U := by nlinarith
      exact (not_lt_of_ge hq_lower.le) this
    have hqpos : 0 < q := by omega
    have hprod_one : 1 ≤ q * k₀ := by
      have hq_le_prod := Nat.le_mul_of_pos_right q hk₀
      omega
    have hk_large : N < q * k₀ - 1 := by
      have hq_le_prod := Nat.le_mul_of_pos_right q hk₀
      omega
    have hexpr :
        ((q * n₀ : ℕ) : ℝ) * Real.log a -
            ((q * k₀ - 1 : ℕ) : ℝ) * Real.log c =
          Real.log c - (q : ℝ) * E := by
      rw [Nat.cast_sub hprod_one]
      push_cast
      dsimp [E, D]
      ring
    refine ⟨q * n₀, q * k₀ - 1, hk_large, ?_, ?_⟩
    · rw [hexpr]
      linarith
    · rw [hexpr]
      linarith
  · have hDgap : D < U - L := by
      have := hDsmall'.trans_le (min_le_left _ _)
      rwa [abs_of_pos hDpos] at this
    have hDleft : D < L / ((N : ℝ) + 2) := by
      have := hDsmall'.trans_le
        (min_le_of_right_le (min_le_left _ _))
      rwa [abs_of_pos hDpos] at this
    let q : ℕ := ⌊L / D⌋₊ + 1
    have hratio_nonneg : 0 ≤ L / D := div_nonneg hL.le hDpos.le
    have hq_lower : L < (q : ℝ) * D := by
      have hfloor := Nat.lt_floor_add_one (L / D)
      have hratio_lt : L / D < (q : ℝ) := by
        simpa [q, Nat.cast_add, Nat.cast_one] using hfloor
      exact (div_lt_iff₀ hDpos).mp hratio_lt
    have hq_upper : (q : ℝ) * D < U := by
      have hfloor := Nat.floor_le hratio_nonneg
      have hq_le : (q : ℝ) ≤ L / D + 1 := by
        dsimp [q]
        push_cast
        linarith
      have hmul_le : (q : ℝ) * D ≤ L + D := by
        have := mul_le_mul_of_nonneg_right hq_le hDpos.le
        field_simp [hDpos.ne'] at this
        nlinarith
      linarith
    have hq_large : N < q := by
      by_contra hnot
      have hq_le_nat : q ≤ N := le_of_not_gt hnot
      have hq_le_real : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq_le_nat
      have hscaled : ((N : ℝ) + 2) * D < L := by
        simpa [mul_comm] using (lt_div_iff₀ hdenom).mp hDleft
      have : (q : ℝ) * D < L := by nlinarith
      exact (not_lt_of_ge hq_lower.le) this
    have hk_large : N < q * k₀ :=
      hq_large.trans_le (Nat.le_mul_of_pos_right q hk₀)
    have hexpr :
        ((q * n₀ : ℕ) : ℝ) * Real.log a -
            ((q * k₀ : ℕ) : ℝ) * Real.log c =
          (q : ℝ) * D := by
      push_cast
      dsimp [D]
      ring
    refine ⟨q * n₀, q * k₀, hk_large, ?_, ?_⟩
    · rw [hexpr]
      exact hq_lower
    · rw [hexpr]
      exact hq_upper

/-- Clear the negative exponents in a dense multiplicative approximation by
adding the same natural exponent to both generators. -/
private theorem exists_shifted_nat_scales_mem_Ioo
    {a b l u : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hindependent : MultiplicativelyIndependent a b)
    (hl : 0 < l) (hlu : l < u) :
    ∃ M N K : ℕ,
      a ^ M * b ^ N / (a * b) ^ K ∈ Set.Ioo l u := by
  obtain ⟨r, s, hrs⟩ :=
    exists_zpow_mul_mem_Ioo_of_independent ha hb hindependent hl hlu
  let K : ℕ := r.natAbs + s.natAbs
  have hrK : -r ≤ (K : ℤ) := by
    dsimp [K]
    push_cast
    exact (neg_le_abs r).trans (le_add_of_nonneg_right (abs_nonneg s))
  have hsK : -s ≤ (K : ℤ) := by
    dsimp [K]
    push_cast
    exact (neg_le_abs s).trans (le_add_of_nonneg_left (abs_nonneg r))
  have hrNonneg : 0 ≤ r + (K : ℤ) := by omega
  have hsNonneg : 0 ≤ s + (K : ℤ) := by omega
  let M : ℕ := (r + (K : ℤ)).toNat
  let N : ℕ := (s + (K : ℤ)).toNat
  have hMcast : (M : ℤ) = r + (K : ℤ) := by
    simpa [M] using Int.toNat_of_nonneg hrNonneg
  have hNcast : (N : ℤ) = s + (K : ℤ) := by
    simpa [N] using Int.toNat_of_nonneg hsNonneg
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  have hb0 : b ≠ 0 := (zero_lt_one.trans hb).ne'
  have hpowA : a ^ M = a ^ r * a ^ K := by
    calc
      a ^ M = a ^ (M : ℤ) := (zpow_natCast a M).symm
      _ = a ^ (r + (K : ℤ)) := congrArg (fun e : ℤ ↦ a ^ e) hMcast
      _ = a ^ r * a ^ (K : ℤ) := zpow_add₀ ha0 r K
      _ = a ^ r * a ^ K := by rw [zpow_natCast]
  have hpowB : b ^ N = b ^ s * b ^ K := by
    calc
      b ^ N = b ^ (N : ℤ) := (zpow_natCast b N).symm
      _ = b ^ (s + (K : ℤ)) := congrArg (fun e : ℤ ↦ b ^ e) hNcast
      _ = b ^ s * b ^ (K : ℤ) := zpow_add₀ hb0 s K
      _ = b ^ s * b ^ K := by rw [zpow_natCast]
  refine ⟨M, N, K, ?_⟩
  have hratio : a ^ M * b ^ N / (a * b) ^ K = a ^ r * b ^ s := by
    rw [hpowA, hpowB, mul_pow]
    field_simp [pow_ne_zero K ha0, pow_ne_zero K hb0]
  rwa [hratio]

/-- Once a subinterval covers under an iterate of `W`, every sufficiently
large iterate of a positive iterate `R = W^[d]` covers as well. -/
private theorem eventually_iterate_R_covers_of_W_cover
    {R W : IntervalMap} {d : ℕ} (hd : 0 < d)
    (hR_iterate : R = iterateMap W d) (hW_onto : IsOnto W)
    {S : Set I} (hcover : ∃ n : ℕ, iterateMap W n '' S = Set.univ) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → iterateMap R k '' S = Set.univ := by
  obtain ⟨N, hN⟩ := hcover
  refine ⟨N, fun k hk ↦ ?_⟩
  have hd_one : 1 ≤ d := hd
  have hNdk : N ≤ d * k :=
    hk.trans (by simpa using Nat.mul_le_mul_right k hd_one)
  let m : ℕ := d * k - N
  have hsum : m + N = d * k := Nat.sub_add_cancel hNdk
  apply Set.eq_univ_of_forall
  intro y
  obtain ⟨z, hz⟩ := IntervalMap.surjective_iterate hW_onto m y
  have hzImage : z ∈ iterateMap W N '' S := by
    rw [hN]
    exact Set.mem_univ z
  obtain ⟨x, hxS, hxz⟩ := hzImage
  refine ⟨x, hxS, ?_⟩
  change (W^[N]) x = z at hxz
  change (R^[k]) x = y
  rw [hR_iterate]
  change ((W^[d])^[k]) x = y
  rw [← Function.iterate_mul]
  change (W^[d * k]) x = y
  rw [← hsum, Function.iterate_add_apply, hxz, hz]

private theorem exists_rayParameter_interval_in_open
    {p : I} (Φ : RayChart p) (hdense : Φ.HasDenseTails)
    (start : RayParameter) {U : Set I} (hU : IsOpen U) (hUne : U.Nonempty) :
    ∃ u v : RayParameter, start ≤ u ∧ u < v ∧
      Φ.toFun '' Set.Icc u v ⊆ U := by
  have htailDense : Dense (Φ.tailImage start) :=
    dense_iff_closure_eq.mpr (hdense start)
  obtain ⟨y, hyTail, hyU⟩ := htailDense.exists_mem_open hU hUne
  obtain ⟨u, hstartu, hΦu⟩ := hyTail
  have hpreOpen : IsOpen (Φ.toFun ⁻¹' U) := hU.preimage Φ.continuous_toFun
  have huPre : u ∈ Φ.toFun ⁻¹' U := by simpa [hΦu] using hyU
  rw [Metric.isOpen_iff] at hpreOpen
  obtain ⟨ε, hεpos, hball⟩ := hpreOpen u huPre
  let v : RayParameter :=
    ⟨(u : ℝ) + ε / 2, add_nonneg u.property (div_nonneg hεpos.le (by norm_num))⟩
  have huv : u < v := by
    change (u : ℝ) < (u : ℝ) + ε / 2
    linarith
  refine ⟨u, v, hstartu, huv, ?_⟩
  rintro x ⟨t, ht, rfl⟩
  apply hball
  rw [Metric.mem_ball]
  change dist (t : ℝ) (u : ℝ) < ε
  rw [Real.dist_eq, abs_of_nonneg
    (sub_nonneg.mpr (show (u : ℝ) ≤ (t : ℝ) from ht.1))]
  change (t : ℝ) - (u : ℝ) < ε
  have htv : (t : ℝ) ≤ (u : ℝ) + ε / 2 := ht.2
  linarith

private theorem boundaryLift_selectedInterval
    {p : I} (Φ : RayChart p) {tstar : RayParameter}
    (hboundary : Φ.IsPositiveBoundaryLift tstar)
    {l r : ℝ} (hl : l < (tstar : ℝ)) (hr : (tstar : ℝ) < r) :
    ∃ q : I, p < q ∧
      Set.Icc p q ⊆
        (fun s : ℝ => Φ ⟨max 0 s, le_max_left 0 s⟩) '' Set.Icc l r := by
  let ε : ℝ := min ((tstar : ℝ) - l) (r - (tstar : ℝ))
  have hε : 0 < ε := lt_min (sub_pos.mpr hl) (sub_pos.mpr hr)
  obtain ⟨t, htclose, hpΦt⟩ := hboundary.2.2 ε hε
  have htl : l < (t : ℝ) := by
    have habs := (abs_lt.mp htclose).1
    have hneg : -((tstar : ℝ) - l) ≤ -ε := by
      exact neg_le_neg (min_le_left _ _)
    nlinarith
  have htr : (t : ℝ) < r := by
    have habs := (abs_lt.mp htclose).2
    have hpos : ε ≤ r - (tstar : ℝ) := min_le_right _ _
    nlinarith
  let ψ : ℝ → I := fun s => Φ ⟨max 0 s, le_max_left 0 s⟩
  have hψContinuous : Continuous ψ :=
    Φ.continuous_toFun.comp
      ((continuous_const.max continuous_id).subtype_mk _)
  have htstarNonneg : 0 ≤ (tstar : ℝ) := tstar.property
  have htNonneg : 0 ≤ (t : ℝ) := t.property
  have hψstar : ψ (tstar : ℝ) = p := by
    simpa [ψ, max_eq_right htstarNonneg] using hboundary.2.1
  have hψt : ψ (t : ℝ) = Φ t := by
    change Φ ⟨max 0 (t : ℝ), le_max_left 0 (t : ℝ)⟩ = Φ t
    apply congrArg Φ.toFun
    apply Subtype.ext
    exact max_eq_right htNonneg
  refine ⟨Φ t, hpΦt, ?_⟩
  intro x hx
  have hxui : x ∈ Set.uIcc (ψ (tstar : ℝ)) (ψ (t : ℝ)) := by
    rw [hψstar, hψt, uIcc_of_le hpΦt.le]
    exact hx
  obtain ⟨s, hsui, hψs⟩ :=
    intermediate_value_uIcc hψContinuous.continuousOn hxui
  refine ⟨s, ?_, hψs⟩
  have hsBounds : s ∈ Set.Icc
      (min (tstar : ℝ) (t : ℝ)) (max (tstar : ℝ) (t : ℝ)) := by
    simpa [Set.uIcc] using hsui
  constructor
  · exact lt_min hl htl |>.le.trans hsBounds.1
  · exact hsBounds.2.trans (max_lt hr htr).le

/-- A positive boundary lift remains a positive boundary lift after applying
an expanding actor which fixes the base and is strictly increasing on the
selected side. -/
private theorem positiveBoundaryLift_scale
    {p : I} (Phi : RayChart p) {T : IntervalMap} {c : ℝ}
    (hc : 0 < c) (hT_fixed : IsFixedPoint T p)
    (hT_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q))
    (hT_action : RayScaleAction Phi T c)
    {t : RayParameter} (hboundary : Phi.IsPositiveBoundaryLift t) :
    Phi.IsPositiveBoundaryLift (scaleRayParameter c hc.le t) := by
  refine ⟨?_, ?_, ?_⟩
  · change 0 < c * (t : ℝ)
    exact mul_pos hc hboundary.1
  · calc
      Phi (scaleRayParameter c hc.le t) = T (Phi t) :=
        (hT_action.equivariant t).symm
      _ = T p := congrArg T hboundary.2.1
      _ = p := hT_fixed
  · intro epsilon hepsilon
    obtain ⟨q, hpq, hTstrict⟩ := hT_strictNearBase
    have hopenPre : IsOpen (Phi.toFun ⁻¹' Set.Iio q) :=
      isOpen_Iio.preimage Phi.continuous_toFun
    have htPre : t ∈ Phi.toFun ⁻¹' Set.Iio q := by
      change Phi t < q
      rw [hboundary.2.1]
      exact hpq
    rw [Metric.isOpen_iff] at hopenPre
    obtain ⟨delta, hdelta, hball⟩ := hopenPre t htPre
    let eta : ℝ := min delta (epsilon / c)
    have heta : 0 < eta := lt_min hdelta (div_pos hepsilon hc)
    obtain ⟨s, hsClose, hpPhiS⟩ := hboundary.2.2 eta heta
    have hsPre : s ∈ Phi.toFun ⁻¹' Set.Iio q := by
      apply hball
      rw [Metric.mem_ball]
      change dist (s : ℝ) (t : ℝ) < delta
      rw [Real.dist_eq]
      exact hsClose.trans_le (min_le_left _ _)
    have hPhiS_mem : Phi s ∈ Set.Icc p q := ⟨hpPhiS.le, hsPre.le⟩
    have hp_mem : p ∈ Set.Icc p q := ⟨le_rfl, hpq.le⟩
    have hpTPhiS : p < T (Phi s) := by
      exact hT_fixed.symm.trans_lt (hTstrict hp_mem hPhiS_mem hpPhiS)
    refine ⟨scaleRayParameter c hc.le s, ?_, ?_⟩
    · change |c * (s : ℝ) - c * (t : ℝ)| < epsilon
      rw [← mul_sub, abs_mul, abs_of_pos hc]
      calc
        c * |(s : ℝ) - (t : ℝ)| < c * (epsilon / c) :=
          mul_lt_mul_of_pos_left
            (hsClose.trans_le (min_le_right _ _)) hc
        _ = epsilon := by field_simp [hc.ne']
    · rw [← hT_action.equivariant]
      exact hpTPhiS

/-- Iterated form of `positiveBoundaryLift_scale`. -/
private theorem positiveBoundaryLift_scale_pow
    {p : I} (Phi : RayChart p) {T : IntervalMap} {c : ℝ}
    (hc : 0 < c) (hT_fixed : IsFixedPoint T p)
    (hT_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn T (Set.Icc p q))
    (hT_action : RayScaleAction Phi T c)
    {t : RayParameter} (hboundary : Phi.IsPositiveBoundaryLift t)
    (n : ℕ) :
    Phi.IsPositiveBoundaryLift
      (scaleRayParameter (c ^ n) (pow_nonneg hc.le n) t) := by
  induction n with
  | zero =>
      have heq : scaleRayParameter (c ^ 0) (pow_nonneg hc.le 0) t = t := by
        apply Subtype.ext
        change c ^ 0 * (t : ℝ) = (t : ℝ)
        simp
      rwa [heq]
  | succ n ih =>
      have hstep := positiveBoundaryLift_scale Phi hc hT_fixed
        hT_strictNearBase hT_action ih
      have heq :
          scaleRayParameter c hc.le
              (scaleRayParameter (c ^ n) (pow_nonneg hc.le n) t) =
            scaleRayParameter (c ^ (n + 1))
              (pow_nonneg hc.le (n + 1)) t := by
        apply Subtype.ext
        change c * (c ^ n * (t : ℝ)) = c ^ (n + 1) * (t : ℝ)
        rw [pow_succ]
        ring
      rwa [← heq]

/-- A scale which is multiplicatively independent from the covering scale is
topologically exact.  The proof aligns a fixed boundary-lift window with a
parameter interval lying in the prescribed open set. -/
private theorem rayScale_exact_of_fixed_boundary
    {p : I} (Phi : RayChart p) (C R W : IntervalMap)
    (c Lambda : ℝ) (d : ℕ)
    (hc : 1 < c) (hLambda : 1 < Lambda)
    (hindependent : MultiplicativelyIndependent c Lambda)
    (hC_action : RayScaleAction Phi C c)
    (hR_action : RayScaleAction Phi R Lambda)
    (hdense : Phi.HasDenseTails)
    (tstar : RayParameter) (hboundary : Phi.IsPositiveBoundaryLift tstar)
    (hd : 0 < d) (hR_iterate : R = iterateMap W d)
    (hW_onto : IsOnto W)
    (hlocalCover :
      ∀ q : I, p < q →
        ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ) :
    IsTopologicallyExact C := by
  intro U hU hUne
  have htstarPos : 0 < (tstar : ℝ) := hboundary.1
  have hcPos : 0 < c := zero_lt_one.trans hc
  have hLambdaPos : 0 < Lambda := zero_lt_one.trans hLambda
  let start : RayParameter :=
    ⟨(tstar : ℝ) + 1, add_nonneg tstar.property zero_le_one⟩
  obtain ⟨u, v, hstartu, huv, hPhiUV⟩ :=
    exists_rayParameter_interval_in_open Phi hdense start hU hUne
  have htstar_u : (tstar : ℝ) < (u : ℝ) := by
    have hstartu' : (tstar : ℝ) + 1 ≤ (u : ℝ) := hstartu
    linarith
  have huPos : 0 < (u : ℝ) := htstarPos.trans htstar_u
  have hvPos : 0 < (v : ℝ) := huPos.trans huv
  have hratioOne : 1 ≤ (u : ℝ) / (tstar : ℝ) :=
    (le_div_iff₀ htstarPos).2 (by simpa using htstar_u.le)
  obtain ⟨j, hjlow, hjhigh⟩ := exists_nat_pow_near hratioOne hLambda
  let J : ℕ := j + 1
  let z : ℝ := Lambda ^ J * (tstar : ℝ)
  have hLambdaPowPos : 0 < Lambda ^ J := pow_pos hLambdaPos J
  have hzPos : 0 < z := mul_pos hLambdaPowPos htstarPos
  have huz : (u : ℝ) < z := by
    have := (div_lt_iff₀ htstarPos).1 hjhigh
    simpa [z, J, mul_comm] using this
  have hz_u_le : z / (u : ℝ) ≤ Lambda := by
    have hjscaled : Lambda ^ j * (tstar : ℝ) ≤ (u : ℝ) :=
      (le_div_iff₀ htstarPos).1 hjlow
    apply (div_le_iff₀ huPos).2
    calc
      z = Lambda * (Lambda ^ j * (tstar : ℝ)) := by
        simp [z, J, pow_succ]
        ring
      _ ≤ Lambda * (u : ℝ) :=
        mul_le_mul_of_nonneg_left hjscaled hLambdaPos.le
      _ = Lambda * (u : ℝ) := rfl
  let low : ℝ := max 1 (z / (v : ℝ))
  let high : ℝ := z / (u : ℝ)
  have hzDiv_lt : z / (v : ℝ) < z / (u : ℝ) := by
    apply (div_lt_div_iff₀ hvPos huPos).2
    exact mul_lt_mul_of_pos_left huv hzPos
  have hlowHigh : low < high := by
    apply max_lt
    · exact (lt_div_iff₀ huPos).2 (by simpa [high, z] using huz)
    · simpa [low, high] using hzDiv_lt
  let rhoLo : ℝ := (low + high) / 2
  let rhoHi : ℝ := (rhoLo + high) / 2
  have hlow_rhoLo : low < rhoLo := by dsimp [rhoLo]; linarith
  have hrhoLo_rhoHi : rhoLo < rhoHi := by
    dsimp [rhoHi]
    have : rhoLo < high := by dsimp [rhoLo]; linarith
    linarith
  have hrhoHi_high : rhoHi < high := by
    dsimp [rhoHi]
    have : rhoLo < high := by dsimp [rhoLo]; linarith
    linarith
  have hone_rhoLo : 1 < rhoLo :=
    (le_max_left 1 (z / (v : ℝ))).trans_lt hlow_rhoLo
  have hzv_rhoLo : z / (v : ℝ) < rhoLo :=
    (le_max_right 1 (z / (v : ℝ))).trans_lt hlow_rhoLo
  have hrhoHi_Lambda : rhoHi < Lambda :=
    hrhoHi_high.trans_le (by simpa [high] using hz_u_le)
  have hrhoLoPos : 0 < rhoLo := zero_lt_one.trans hone_rhoLo
  have hrhoHiPos : 0 < rhoHi := hrhoLoPos.trans hrhoLo_rhoHi
  let lowerH : ℝ := rhoHi * (u : ℝ) / Lambda ^ J
  let upperH : ℝ := rhoLo * (v : ℝ) / Lambda ^ J
  have hlowerH_tstar : lowerH < (tstar : ℝ) := by
    apply (div_lt_iff₀ hLambdaPowPos).2
    have hscaled := (lt_div_iff₀ huPos).1 (by simpa [high] using hrhoHi_high)
    dsimp [lowerH, z] at hscaled ⊢
    nlinarith
  have htstar_upperH : (tstar : ℝ) < upperH := by
    apply (lt_div_iff₀ hLambdaPowPos).2
    have hscaled := (div_lt_iff₀ hvPos).1 hzv_rhoLo
    dsimp [upperH, z] at hscaled ⊢
    nlinarith
  obtain ⟨l, hlowerH_l, hl_tstar⟩ := exists_between hlowerH_tstar
  obtain ⟨r, htstar_r, hr_upperH⟩ := exists_between htstar_upperH
  have hlPos : 0 < l := by
    have hlowerHPos : 0 < lowerH :=
      div_pos (mul_pos hrhoHiPos huPos) hLambdaPowPos
    exact hlowerHPos.trans hlowerH_l
  obtain ⟨q, hpq, hboundaryImage⟩ :=
    boundaryLift_selectedInterval Phi hboundary hl_tstar htstar_r
  obtain ⟨N, hcoverR⟩ :=
    eventually_iterate_R_covers_of_W_cover hd hR_iterate hW_onto
      (hlocalCover q hpq)
  have hlogLoPos : 0 < Real.log rhoLo := Real.log_pos hone_rhoLo
  have hlogLoHi : Real.log rhoLo < Real.log rhoHi :=
    Real.strictMonoOn_log hrhoLoPos hrhoHiPos hrhoLo_rhoHi
  have hlogHiLambda : Real.log rhoHi < Real.log Lambda :=
    Real.strictMonoOn_log hrhoHiPos hLambdaPos hrhoHi_Lambda
  obtain ⟨n, k, hNk, hlogLower, hlogUpper⟩ :=
    exists_large_nat_log_residue hc hLambda hindependent hlogLoPos
      hlogLoHi hlogHiLambda N
  let rho : ℝ := c ^ n / Lambda ^ k
  have hrhoPos : 0 < rho := div_pos (pow_pos hcPos n) (pow_pos hLambdaPos k)
  have hlogRho :
      Real.log rho =
        (n : ℝ) * Real.log c - (k : ℝ) * Real.log Lambda := by
    dsimp [rho]
    rw [Real.log_div, Real.log_pow, Real.log_pow] <;> positivity
  have hrhoLo_rho : rhoLo < rho := by
    rw [← Real.exp_log hrhoLoPos, ← Real.exp_log hrhoPos]
    exact Real.exp_lt_exp.mpr (by simpa [hlogRho] using hlogLower)
  have hrho_rhoHi : rho < rhoHi := by
    rw [← Real.exp_log hrhoPos, ← Real.exp_log hrhoHiPos]
    exact Real.exp_lt_exp.mpr (by simpa [hlogRho] using hlogUpper)
  have hcoverLarge :
      iterateMap R (k + J) '' Set.Icc p q = Set.univ := by
    apply hcoverR
    omega
  refine ⟨n, Set.eq_univ_of_forall ?_⟩
  intro y
  have hyCover : y ∈ iterateMap R (k + J) '' Set.Icc p q := by
    rw [hcoverLarge]
    exact Set.mem_univ y
  obtain ⟨x, hxInterval, hRxy⟩ := hyCover
  obtain ⟨s, hsWindow, hPhiS⟩ := hboundaryImage hxInterval
  have hsPos : 0 < s := hlPos.trans_le hsWindow.1
  let ss : RayParameter := ⟨s, hsPos.le⟩
  have hPhiSS : Phi ss = x := by
    simpa [ss, max_eq_right hsPos.le] using hPhiS
  let tval : ℝ := Lambda ^ J * s / rho
  have htvalPos : 0 < tval :=
    div_pos (mul_pos hLambdaPowPos hsPos) hrhoPos
  let t : RayParameter := ⟨tval, htvalPos.le⟩
  have htLower : (u : ℝ) ≤ tval := by
    apply (le_div_iff₀ hrhoPos).2
    have hsLower : lowerH < s := hlowerH_l.trans_le hsWindow.1
    have hscaledLower : rhoHi * (u : ℝ) < Lambda ^ J * s := by
      calc
        rhoHi * (u : ℝ) < s * Lambda ^ J :=
          (div_lt_iff₀ hLambdaPowPos).1 (by simpa [lowerH] using hsLower)
        _ = Lambda ^ J * s := mul_comm _ _
    have hrhoScaled : rho * (u : ℝ) < rhoHi * (u : ℝ) :=
      mul_lt_mul_of_pos_right hrho_rhoHi huPos
    dsimp [tval]
    simpa [mul_comm] using (hrhoScaled.trans hscaledLower).le
  have htUpper : tval ≤ (v : ℝ) := by
    apply (div_le_iff₀ hrhoPos).2
    have hsUpper : s < upperH := hsWindow.2.trans_lt hr_upperH
    have hscaledUpper : Lambda ^ J * s < rhoLo * (v : ℝ) := by
      calc
        Lambda ^ J * s = s * Lambda ^ J := mul_comm _ _
        _ < rhoLo * (v : ℝ) :=
          (lt_div_iff₀ hLambdaPowPos).1 (by simpa [upperH] using hsUpper)
    have hrhoScaled : rhoLo * (v : ℝ) < rho * (v : ℝ) :=
      mul_lt_mul_of_pos_right hrhoLo_rho hvPos
    dsimp [tval]
    simpa [mul_comm] using (hscaledUpper.trans hrhoScaled).le
  have hPhiT_U : Phi t ∈ U := by
    apply hPhiUV
    exact ⟨t, ⟨htLower, htUpper⟩, rfl⟩
  refine ⟨Phi t, hPhiT_U, ?_⟩
  have hscaleEq :
      scaleRayParameter (c ^ n) (pow_nonneg hcPos.le n) t =
        scaleRayParameter (Lambda ^ (k + J))
          (pow_nonneg hLambdaPos.le (k + J)) ss := by
    apply Subtype.ext
    change c ^ n * tval = Lambda ^ (k + J) * s
    dsimp [tval, rho]
    field_simp [pow_ne_zero n hcPos.ne', pow_ne_zero k hLambdaPos.ne', pow_add]
    <;> ring
  calc
    iterateMap C n (Phi t) =
        Phi (scaleRayParameter (c ^ n) (pow_nonneg hcPos.le n) t) :=
      rayScaleAction_iterate Phi hC_action n t
    _ = Phi (scaleRayParameter (Lambda ^ (k + J))
          (pow_nonneg hLambdaPos.le (k + J)) ss) :=
      congrArg Phi.toFun hscaleEq
    _ = iterateMap R (k + J) (Phi ss) :=
      (rayScaleAction_iterate Phi hR_action (k + J) ss).symm
    _ = iterateMap R (k + J) x := congrArg (iterateMap R (k + J)) hPhiSS
    _ = y := hRxy

/-- Exactness passes from a positive iterate back to the original map. -/
private theorem topologicallyExact_of_exact_iterate
    {T S : IntervalMap} {L : ℕ} (hS : S = iterateMap T L)
    (hexact : IsTopologicallyExact S) :
    IsTopologicallyExact T := by
  intro U hU hUne
  obtain ⟨n, hn⟩ := hexact U hU hUne
  refine ⟨L * n, ?_⟩
  simpa [hS, iterateMap, Function.iterate_mul] using hn

/-- The geometric recurrence input needed for exactness of the common
covering scale: some `R`-iterate of every open set contains a selected-side
interval based at `p`. -/
private theorem exists_coveringScale_boundary_interval
    {p : I} (Phi : RayChart p) (A B R : IntervalMap)
    (a b Lambda : ℝ)
    (hA_continuous : Continuous A) (hB_continuous : Continuous B)
    (hA_onto : IsOnto A) (hB_onto : IsOnto B)
    (hA_fixed : IsFixedPoint A p) (hB_fixed : IsFixedPoint B p)
    (hA_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn A (Set.Icc p q))
    (hB_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn B (Set.Icc p q))
    (hA_action : RayScaleAction Phi A a)
    (hB_action : RayScaleAction Phi B b)
    (hR_action : RayScaleAction Phi R Lambda)
    (ha : 1 < a) (hb : 1 < b) (hLambda : Lambda = a * b)
    (hindependent : MultiplicativelyIndependent a b)
    (hdense : Phi.HasDenseTails)
    (tstar : RayParameter) (hboundary : Phi.IsPositiveBoundaryLift tstar) :
    ∀ U : Set I, IsOpen U → U.Nonempty →
      ∃ k : ℕ, ∃ q : I, p < q ∧
        Set.Icc p q ⊆ iterateMap R k '' U := by
  intro U hU hUne
  have haPos : 0 < a := zero_lt_one.trans ha
  have hbPos : 0 < b := zero_lt_one.trans hb
  have hLambdaPos : 0 < Lambda := by
    rw [hLambda]
    exact mul_pos haPos hbPos
  have htstarPos : 0 < (tstar : ℝ) := hboundary.1
  obtain ⟨u, v, htstar_u, huv, hPhiUV⟩ :=
    exists_rayParameter_interval_in_open Phi hdense tstar hU hUne
  have huPos : 0 < (u : ℝ) := htstarPos.trans_le htstar_u
  have hvPos : 0 < (v : ℝ) := huPos.trans huv
  have hratioPos : 0 < (u : ℝ) / (tstar : ℝ) :=
    div_pos huPos htstarPos
  have hratioLt :
      (u : ℝ) / (tstar : ℝ) < (v : ℝ) / (tstar : ℝ) :=
    div_lt_div_of_pos_right huv htstarPos
  obtain ⟨M, N, K, hfactor⟩ :=
    exists_shifted_nat_scales_mem_Ioo ha hb hindependent hratioPos hratioLt
  let factor : ℝ := a ^ M * b ^ N / (a * b) ^ K
  have hfactorPos : 0 < factor := hratioPos.trans hfactor.1
  let tauVal : ℝ := factor * (tstar : ℝ)
  have htauValPos : 0 < tauVal := mul_pos hfactorPos htstarPos
  let tau : RayParameter := ⟨tauVal, htauValPos.le⟩
  have hu_tau : (u : ℝ) < tauVal := by
    apply (div_lt_iff₀ htstarPos).1
    simpa [factor] using hfactor.1
  have htau_v : tauVal < (v : ℝ) := by
    apply (lt_div_iff₀ htstarPos).1
    simpa [factor] using hfactor.2
  have hPhiTauU : Phi tau ∈ U := by
    apply hPhiUV
    exact ⟨tau, ⟨hu_tau.le, htau_v.le⟩, rfl⟩
  have hboundaryB := positiveBoundaryLift_scale_pow Phi hbPos hB_fixed
    hB_strictNearBase hB_action hboundary N
  have hboundaryAB := positiveBoundaryLift_scale_pow Phi haPos hA_fixed
    hA_strictNearBase hA_action hboundaryB M
  let sigma : RayParameter :=
    scaleRayParameter (a ^ M * b ^ N)
      (mul_nonneg (pow_nonneg haPos.le M) (pow_nonneg hbPos.le N)) tstar
  have hboundarySigma : Phi.IsPositiveBoundaryLift sigma := by
    have heq :
        scaleRayParameter (a ^ M) (pow_nonneg haPos.le M)
            (scaleRayParameter (b ^ N) (pow_nonneg hbPos.le N) tstar) =
          sigma := by
      apply Subtype.ext
      change a ^ M * (b ^ N * (tstar : ℝ)) =
        (a ^ M * b ^ N) * (tstar : ℝ)
      ring
    rwa [← heq]
  let scaledTau : RayParameter :=
    scaleRayParameter (Lambda ^ K) (pow_nonneg hLambdaPos.le K) tau
  have hsigma_scaledTau : sigma = scaledTau := by
    apply Subtype.ext
    change (a ^ M * b ^ N) * (tstar : ℝ) =
      Lambda ^ K * tauVal
    dsimp [tauVal, factor]
    rw [hLambda]
    field_simp [pow_ne_zero K (mul_ne_zero haPos.ne' hbPos.ne')]
  have hboundaryScaledTau : Phi.IsPositiveBoundaryLift scaledTau := by
    rw [← hsigma_scaledTau]
    exact hboundarySigma
  let left : ℝ := Lambda ^ K * (u : ℝ)
  let right : ℝ := Lambda ^ K * (v : ℝ)
  have hLambdaPowPos : 0 < Lambda ^ K := pow_pos hLambdaPos K
  have hleft_scaled : left < (scaledTau : ℝ) := by
    change Lambda ^ K * (u : ℝ) < Lambda ^ K * tauVal
    exact mul_lt_mul_of_pos_left hu_tau hLambdaPowPos
  have hscaled_right : (scaledTau : ℝ) < right := by
    change Lambda ^ K * tauVal < Lambda ^ K * (v : ℝ)
    exact mul_lt_mul_of_pos_left htau_v hLambdaPowPos
  obtain ⟨q, hpq, hboundaryWindow⟩ :=
    boundaryLift_selectedInterval Phi hboundaryScaledTau
      hleft_scaled hscaled_right
  refine ⟨K, q, hpq, ?_⟩
  intro x hxInterval
  obtain ⟨s, hsWindow, hPhiS⟩ := hboundaryWindow hxInterval
  have hleftPos : 0 < left := mul_pos hLambdaPowPos huPos
  have hsPos : 0 < s := hleftPos.trans_le hsWindow.1
  let preVal : ℝ := s / Lambda ^ K
  have hpreValPos : 0 < preVal := div_pos hsPos hLambdaPowPos
  let pre : RayParameter := ⟨preVal, hpreValPos.le⟩
  have hu_pre : (u : ℝ) ≤ preVal := by
    apply (le_div_iff₀ hLambdaPowPos).2
    simpa [left, mul_comm] using hsWindow.1
  have hpre_v : preVal ≤ (v : ℝ) := by
    apply (div_le_iff₀ hLambdaPowPos).2
    simpa [right, mul_comm] using hsWindow.2
  have hPhiPreU : Phi pre ∈ U := by
    apply hPhiUV
    exact ⟨pre, ⟨hu_pre, hpre_v⟩, rfl⟩
  refine ⟨Phi pre, hPhiPreU, ?_⟩
  have hscalePre :
      scaleRayParameter (Lambda ^ K) (pow_nonneg hLambdaPos.le K) pre =
        ⟨max 0 s, le_max_left 0 s⟩ := by
    apply Subtype.ext
    change Lambda ^ K * preVal = max 0 s
    rw [max_eq_right hsPos.le]
    dsimp [preVal]
    field_simp [pow_ne_zero K hLambdaPos.ne']
  calc
    iterateMap R K (Phi pre) =
        Phi (scaleRayParameter (Lambda ^ K)
          (pow_nonneg hLambdaPos.le K) pre) :=
      rayScaleAction_iterate Phi hR_action K pre
    _ = Phi ⟨max 0 s, le_max_left 0 s⟩ := congrArg Phi.toFun hscalePre
    _ = x := hPhiS

/-- Boundary recurrence plus the local `W`-covering property gives exactness
of the positive iterate `R = W^[d]`. -/
private theorem coveringScale_exact_of_boundary_recurrence
    {p : I} (R W : IntervalMap) (d : ℕ)
    (hd : 0 < d) (hR_iterate : R = iterateMap W d)
    (hW_onto : IsOnto W)
    (hlocalCover :
      ∀ q : I, p < q →
        ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ)
    (hrecurrence :
      ∀ U : Set I, IsOpen U → U.Nonempty →
        ∃ k : ℕ, ∃ q : I, p < q ∧
          Set.Icc p q ⊆ iterateMap R k '' U) :
    IsTopologicallyExact R := by
  intro U hU hUne
  obtain ⟨k, q, hpq, hinterval⟩ := hrecurrence U hU hUne
  obtain ⟨N, hcoverR⟩ :=
    eventually_iterate_R_covers_of_W_cover hd hR_iterate hW_onto
      (hlocalCover q hpq)
  have hcoverN : iterateMap R N '' Set.Icc p q = Set.univ :=
    hcoverR N le_rfl
  refine ⟨N + k, Set.eq_univ_of_forall ?_⟩
  intro y
  have hyCover : y ∈ iterateMap R N '' Set.Icc p q := by
    rw [hcoverN]
    exact Set.mem_univ y
  obtain ⟨z, hzInterval, hRzy⟩ := hyCover
  obtain ⟨x, hxU, hRxz⟩ := hinterval hzInterval
  refine ⟨x, hxU, ?_⟩
  change (R^[N + k]) x = y
  rw [Function.iterate_add_apply]
  change iterateMap R N (iterateMap R k x) = y
  rw [hRxz, hRzy]

/--
Dense tails, independent expanding scales, a positive boundary lift, and
local eventual covering yield exactness of `R`, `A`, and `B`.  Exactness then
passes from the positive iterates `A = P^L` and `B = Q^L` to `P` and `Q`.
The final nonflatness conclusions are the form consumed by the subsequent
finite-lap and constant-slope reduction.
-/
theorem ray_exactness_covering_package
    {p : I} (Φ : RayChart p)
    (P Q A B R W : IntervalMap)
    (a b Λ : ℝ) (L d : ℕ)
    (hP_continuous : Continuous P)
    (hQ_continuous : Continuous Q)
    (hA_continuous : Continuous A)
    (hB_continuous : Continuous B)
    (hR_continuous : Continuous R)
    (hW_continuous : Continuous W)
    (hP_onto : IsOnto P)
    (hQ_onto : IsOnto Q)
    (hA_onto : IsOnto A)
    (hB_onto : IsOnto B)
    (hR_onto : IsOnto R)
    (hW_onto : IsOnto W)
    (hL : 0 < L) (hd : 0 < d)
    (hA_iterate : A = iterateMap P L)
    (hB_iterate : B = iterateMap Q L)
    (hR_iterate : R = iterateMap W d)
    (hA_fixed : IsFixedPoint A p)
    (hB_fixed : IsFixedPoint B p)
    (hA_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn A (Set.Icc p q))
    (hB_strictNearBase :
      ∃ q : I, p < q ∧ StrictMonoOn B (Set.Icc p q))
    (hA_action : RayScaleAction Φ A a)
    (hB_action : RayScaleAction Φ B b)
    (hR_action : RayScaleAction Φ R Λ)
    (ha : 1 < a) (hb : 1 < b) (hΛ : Λ = a * b)
    (hindependent : MultiplicativelyIndependent a b)
    (hdense : Φ.HasDenseTails)
    (tstar : RayParameter)
    (hboundary : Φ.IsPositiveBoundaryLift tstar)
    (hlocalCover :
      ∀ q : I, p < q →
        ∃ n : ℕ, iterateMap W n '' Set.Icc p q = Set.univ) :
    IsTopologicallyExact R ∧
      IsTopologicallyExact A ∧
      IsTopologicallyExact B ∧
      IsTopologicallyExact P ∧
      IsTopologicallyExact Q ∧
      ¬HasFlatInterval R ∧
      ¬HasFlatInterval A ∧
      ¬HasFlatInterval B ∧
      ¬HasFlatInterval P ∧
      ¬HasFlatInterval Q := by
  have hLambda_gt : 1 < Λ := by
    rw [hΛ]
    have ha_lt : a < a * b := by
      nlinarith [mul_pos (zero_lt_one.trans ha) (sub_pos.mpr hb)]
    exact ha.trans ha_lt
  have hA_independent : MultiplicativelyIndependent a Λ := by
    simpa [hΛ] using
      (multiplicativelyIndependent_left_mul ha hb hindependent)
  have hindependent_symm : MultiplicativelyIndependent b a := by
    intro m n hm hn heq
    exact hindependent n m hn hm heq.symm
  have hB_independent : MultiplicativelyIndependent b Λ := by
    simpa [hΛ, mul_comm] using
      (multiplicativelyIndependent_left_mul hb ha hindependent_symm)
  have hA_exact : IsTopologicallyExact A :=
    rayScale_exact_of_fixed_boundary Φ A R W a Λ d ha hLambda_gt
      hA_independent hA_action hR_action hdense tstar hboundary hd
      hR_iterate hW_onto hlocalCover
  have hB_exact : IsTopologicallyExact B :=
    rayScale_exact_of_fixed_boundary Φ B R W b Λ d hb hLambda_gt
      hB_independent hB_action hR_action hdense tstar hboundary hd
      hR_iterate hW_onto hlocalCover
  have hR_recurrence :=
    exists_coveringScale_boundary_interval Φ A B R a b Λ
      hA_continuous hB_continuous hA_onto hB_onto hA_fixed hB_fixed
      hA_strictNearBase hB_strictNearBase hA_action hB_action hR_action
      ha hb hΛ hindependent hdense tstar hboundary
  have hR_exact : IsTopologicallyExact R :=
    coveringScale_exact_of_boundary_recurrence R W d hd hR_iterate hW_onto
      hlocalCover hR_recurrence
  have hP_exact : IsTopologicallyExact P :=
    topologicallyExact_of_exact_iterate hA_iterate hA_exact
  have hQ_exact : IsTopologicallyExact Q :=
    topologicallyExact_of_exact_iterate hB_iterate hB_exact
  exact ⟨hR_exact, hA_exact, hB_exact, hP_exact, hQ_exact,
    noFlatInterval_of_topologicallyExact hR_exact,
    noFlatInterval_of_topologicallyExact hA_exact,
    noFlatInterval_of_topologicallyExact hB_exact,
    noFlatInterval_of_topologicallyExact hP_exact,
    noFlatInterval_of_topologicallyExact hQ_exact⟩

/-! ## Small public adapters used by the piecewise-linear specialization -/

/-- A local scale action becomes a local scale germ on any global ray which
agrees with the local chart on a nontrivial initial segment. -/
theorem localRayScaleAction_to_hasLocalScaleGerm
    {p : I} {ι : LocalRayChart p} {Φ : RayChart p}
    {T : IntervalMap} {a : ℝ}
    (hext : Φ.ExtendsLocal ι)
    (hact : LocalRayScaleAction ι T a) :
    HasLocalScaleGerm Φ T a := by
  rcases hext with ⟨radius, hradius, hradius_le, hagrees⟩
  refine ⟨hact.scale_pos, radius, hradius, ?_⟩
  intro t ht hscaled
  have ht_local : t ∈ rayInitialSegment ι.radius :=
    lt_of_lt_of_le ht hradius_le
  have hscaled_local :
      scaleRayParameter a hact.scale_pos.le t ∈ rayInitialSegment ι.radius :=
    lt_of_lt_of_le hscaled hradius_le
  have ht_agree : Φ t = ι t := hagrees ht
  have hscaled_agree :
      Φ (scaleRayParameter a hact.scale_pos.le t) =
        ι (scaleRayParameter a hact.scale_pos.le t) :=
    hagrees hscaled
  calc
    T (Φ t) = T (ι t) := congrArg T ht_agree
    _ = ι (scaleRayParameter a hact.scale_pos.le t) :=
      hact.equivariant t ht_local hscaled_local
    _ = Φ (scaleRayParameter a hact.scale_pos.le t) := hscaled_agree.symm

/-- Composition of two actors on the same ray multiplies their scales. -/
theorem rayScaleAction_comp
    {p : I} (Φ : RayChart p) {A B R : IntervalMap} {a b : ℝ}
    (hR : R = A ∘ B)
    (hA : RayScaleAction Φ A a)
    (hB : RayScaleAction Φ B b) :
    RayScaleAction Φ R (a * b) := by
  have hab : 0 < a * b := mul_pos hA.scale_pos hB.scale_pos
  refine ⟨hab, ?_⟩
  intro t
  calc
    R (Φ t) = A (B (Φ t)) := by simp [hR, Function.comp_apply]
    _ = A (Φ (scaleRayParameter b hB.scale_pos.le t)) :=
      congrArg A (hB.equivariant t)
    _ = Φ (scaleRayParameter a hA.scale_pos.le
        (scaleRayParameter b hB.scale_pos.le t)) := hA.equivariant _
    _ = Φ (scaleRayParameter (a * b) hab.le t) := by
      apply congrArg Φ.toFun
      apply Subtype.ext
      dsimp only [scaleRayParameter]
      ring

/-- Fixed increasing right germs compose to an increasing right germ. -/
theorem strictMonoOn_comp_near_fixed
    {A B R : IntervalMap} {p : I}
    (hR : R = A ∘ B)
    (hBp : IsFixedPoint B p)
    (hBcont : Continuous B)
    (hA : ∃ q : I, p < q ∧ StrictMonoOn A (Set.Icc p q))
    (hB : ∃ q : I, p < q ∧ StrictMonoOn B (Set.Icc p q)) :
    ∃ q : I, p < q ∧ StrictMonoOn R (Set.Icc p q) := by
  rcases hA with ⟨qA, hpA, hAstrict⟩
  rcases hB with ⟨qB, hpB, hBstrict⟩
  have hBp_eq : B p = p := hBp
  have hpre : B ⁻¹' Set.Iio qA ∈ nhds p := by
    exact hBcont.continuousAt
      (Iio_mem_nhds (by simpa only [hBp_eq] using hpA))
  obtain ⟨u, hpu, hpu_sub⟩ :=
    exists_Ico_subset_of_mem_nhds hpre ⟨qB, hpB⟩
  obtain ⟨q, hpq, hq⟩ := exists_between (lt_min hpu hpB)
  have hqu : q < u := hq.trans_le (min_le_left _ _)
  have hqB : q < qB := hq.trans_le (min_le_right _ _)
  have hsubB : Set.Icc p q ⊆ Set.Icc p qB := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hqB.le⟩
  have hBmaps : Set.MapsTo B (Set.Icc p q) (Set.Icc p qA) := by
    intro x hx
    constructor
    · have hmono := hBstrict.monotoneOn
      have hpx : p ∈ Set.Icc p qB := ⟨le_rfl, hpB.le⟩
      have h := hmono hpx (hsubB hx) hx.1
      rw [hBp_eq] at h
      exact h
    · have hxin : x ∈ Set.Ico p u := ⟨hx.1, hx.2.trans_lt hqu⟩
      exact (hpu_sub hxin).le
  refine ⟨q, hpq, ?_⟩
  intro x hx y hy hxy
  rw [hR]
  exact hAstrict (hBmaps hx) (hBmaps hy)
    (hBstrict (hsubB hx) (hsubB hy) hxy)

end CommutingInterval
