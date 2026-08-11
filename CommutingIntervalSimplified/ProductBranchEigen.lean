import CommutingIntervalSimplified.WeakLapGrowth
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SumOverResidueClass

/-!
# Weak-lap construction of the initial product eigen-coordinate

This is the standalone replacement for the BF+AM input used in the
simplified manuscript.  A two-branch horseshoe forces exponential weak-lap
growth.  The normalized weak-lap resolvent has a continuous monotone limit
coordinate, and its branch-scaling law is identified directly with the local
branch-length operator.  The later common-coordinate step remains the B6
Brouwer argument; no simultaneous eigenmeasure is used here.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set Filter
open scoped BigOperators Topology NNReal ENNReal

/-! ## Weak-lap growth package -/

-- The complete subdivision, composition, plateau-regularity, and horseshoe
-- growth development is isolated in `WeakLapGrowth`.

/-- Exactly the growth information consumed by the radius construction. -/
structure WeakLapGrowthData (T : IntervalMap) where
  submultiplicative : ∀ m n : ℕ,
    weakLapCount T (m + n) ≤ weakLapCount T m * weakLapCount T n
  upperBase : ℕ
  upperBase_pos : 0 < upperBase
  upper_bound : ∀ n : ℕ, weakLapCount T n ≤ upperBase ^ n
  horse_lower : ∀ n : ℕ, 2 ^ n ≤ weakLapCount T n

theorem weakLapGrowthData_exists {T : IntervalMap}
    (hT : FinitePieceMonotone T) (H : TwoBranchHorseshoe T) :
    Nonempty (WeakLapGrowthData T) := by
  obtain ⟨q, hq, hupper⟩ := weakLapCount_exponential_upper hT
  exact ⟨{
    submultiplicative := weakLapCount_submultiplicative hT
    upperBase := q
    upperBase_pos := hq
    upper_bound := hupper
    horse_lower := weakLapCount_horseshoe_lower hT H }⟩

/-! ## Radius, normalized resolvent, and its limits -/

noncomputable def weakLapResolvent
    (T : IntervalMap) (x y : I) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (weakLapCountOn T n x y : ℝ) * t ^ n

noncomputable def weakTotalLapResolvent
    (T : IntervalMap) (t : ℝ) : ℝ :=
  ∑' n : ℕ, (weakLapCount T n : ℝ) * t ^ n

/-- Samples approach the positive convergence radius from below while the
total resolvent diverges. -/
structure WeakLapRadiusData (T : IntervalMap) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le_half : radius ≤ 1 / 2
  sample : ℕ → ℝ
  sample_pos : ∀ n, 0 < sample n
  sample_lt_radius : ∀ n, sample n < radius
  sample_strictMono : StrictMono sample
  sample_tendsto : Tendsto sample atTop (𝓝 radius)
  series_summable : ∀ n, Summable
    (fun k : ℕ => (weakLapCount T k : ℝ) * sample n ^ k)
  total_tendsto : Tendsto
    (fun n => weakTotalLapResolvent T (sample n)) atTop atTop

/-! ### RL4 internal analytic dependency chain -/

/-- The scalar formal power series whose coefficients are the total weak-lap
counts. -/
private noncomputable def weakLapFormalSeries (T : IntervalMap) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ
    (fun n : ℕ => (weakLapCount T n : ℝ))

/-- A block ratio test for nonnegative submultiplicative coefficients.  This
is the ingredient which turns one contracting coefficient at a positive
block length into convergence of the entire series. -/
private theorem weakSummable_of_submultiplicative_block
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t)
    (hcontract : a N * t ^ N < 1) :
    Summable (fun n : ℕ => a n * t ^ n) := by
  let q := a N * t ^ N
  have hq0 : 0 ≤ q := mul_nonneg (ha N) (pow_nonneg ht N)
  have hblock : ∀ m k : ℕ, a (N * m + k) ≤ a N ^ m * a k := by
    intro m k
    induction m with
    | zero => simp [ha k]
    | succ m ih =>
        calc
          a (N * (m + 1) + k) = a (N + (N * m + k)) := by
            congr 1
            ring
          _ ≤ a N * a (N * m + k) := hsub N (N * m + k)
          _ ≤ a N * (a N ^ m * a k) :=
            mul_le_mul_of_nonneg_left ih (ha N)
          _ = a N ^ (m + 1) * a k := by ring
  have hstride : ∀ k : ℕ,
      Summable (fun m : ℕ => a (N * m + k) * t ^ (N * m + k)) := by
    intro k
    apply Summable.of_nonneg_of_le
      (f := fun m : ℕ => (a k * t ^ k) * q ^ m)
    · intro m
      exact mul_nonneg (ha _) (pow_nonneg ht _)
    · intro m
      calc
        a (N * m + k) * t ^ (N * m + k) ≤
            (a N ^ m * a k) * t ^ (N * m + k) :=
          mul_le_mul_of_nonneg_right (hblock m k) (pow_nonneg ht _)
        _ = (a k * t ^ k) * q ^ m := by
          simp only [q, pow_add, pow_mul, mul_pow]
          ring
    · exact (summable_geometric_of_lt_one hq0 hcontract).mul_left _
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  rw [Finset.sum_indicator_mod N (fun n : ℕ => a n * t ^ n)]
  have hsind (k : ZMod N) : Summable
      ({n : ℕ | (n : ZMod N) = k}.indicator
        (fun n : ℕ => a n * t ^ n)) := by
    rw [← ZMod.natCast_zmod_val k,
      summable_indicator_mod_iff_summable N k.val]
    exact hstride k.val
  have hsum : Summable (fun n : ℕ =>
      ∑ k : ZMod N,
        {m : ℕ | (m : ZMod N) = k}.indicator
          (fun m : ℕ => a m * t ^ m) n) := by
    apply summable_sum (s := Finset.univ)
    intro k _hk
    exact hsind k
  apply hsum.congr
  intro n
  simp only [Finset.sum_apply]

/-- The Cauchy--Hadamard stage of RL4.  Besides locating the finite positive
radius, it records the boundary coefficient inequality needed for divergence
and convergence at every strictly smaller nonnegative parameter. -/
structure WeakLapFormalRadiusData (T : IntervalMap) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_le_half : radius ≤ 1 / 2
  coefficient_boundary : ∀ n : ℕ,
    1 ≤ (weakLapCount T n : ℝ) * radius ^ n
  summable_below : ∀ {s : ℝ}, 0 ≤ s → s < radius →
    Summable (fun n : ℕ => (weakLapCount T n : ℝ) * s ^ n)

/-- Growth bounds produce the complete formal-radius package. -/
private theorem weakLapFormalRadiusData_exists {T : IntervalMap}
    (G : WeakLapGrowthData T) :
    Nonempty (WeakLapFormalRadiusData T) := by
  let a : ℕ → ℝ := fun n => (weakLapCount T n : ℝ)
  let P : FormalMultilinearSeries ℝ ℝ ℝ := weakLapFormalSeries T
  have ha : ∀ n : ℕ, 0 ≤ a n := fun _ => Nat.cast_nonneg _
  have hsub : ∀ m n : ℕ, a (m + n) ≤ a m * a n := by
    intro m n
    have hcast : (weakLapCount T (m + n) : ℝ) ≤
        weakLapCount T m * weakLapCount T n := by
      exact_mod_cast G.submultiplicative m n
    simpa [a] using hcast
  let q : ℝ := G.upperBase
  have hqpos : 0 < q := by
    have hcast : (0 : ℝ) < G.upperBase := by
      exact_mod_cast G.upperBase_pos
    simpa [q] using hcast
  let qinv : ℝ≥0 := ⟨q⁻¹, (inv_pos.mpr hqpos).le⟩
  have hP_lower : (qinv : ℝ≥0∞) ≤ P.radius := by
    apply P.le_radius_of_bound 1
    intro n
    have hupper : a n ≤ q ^ n := by
      have hcast : (weakLapCount T n : ℝ) ≤
          (G.upperBase : ℝ) ^ n := by
        exact_mod_cast G.upper_bound n
      simpa [a, q] using hcast
    dsimp only [P]
    rw [weakLapFormalSeries,
      FormalMultilinearSeries.ofScalars_norm]
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    dsimp [a, qinv]
    dsimp [a] at hupper
    calc
      a n * (q⁻¹) ^ n ≤ q ^ n * (q⁻¹) ^ n :=
        mul_le_mul_of_nonneg_right hupper
          (pow_nonneg (inv_pos.mpr hqpos).le _)
      _ = 1 := by
        rw [← mul_pow]
        simp [hqpos.ne']
  have hqinvpos : 0 < qinv := inv_pos.mpr hqpos
  have hPpos : 0 < P.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr hqinvpos) hP_lower
  let halfNN : ℝ≥0 := ⟨1 / 2, by norm_num⟩
  have hhorseTerm : ∀ n : ℕ,
      1 ≤ ‖P n‖ * (1 / 2 : ℝ) ^ n := by
    intro n
    have hlower : (2 : ℝ) ^ n ≤ a n := by
      have hcast : ((2 ^ n : ℕ) : ℝ) ≤
          (weakLapCount T n : ℝ) := by
        exact_mod_cast G.horse_lower n
      simpa [a] using hcast
    dsimp only [P]
    rw [weakLapFormalSeries,
      FormalMultilinearSeries.ofScalars_norm]
    simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    dsimp [a] at hlower ⊢
    calc
      1 = (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n := by
        rw [← mul_pow]
        norm_num
      _ ≤ a n * (1 / 2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right hlower (pow_nonneg (by norm_num) _)
  have hP_upper : P.radius ≤ (halfNN : ℝ≥0∞) := by
    by_contra hnot
    have hinside : (halfNN : ℝ≥0∞) < P.radius :=
      lt_of_not_ge hnot
    have hs := P.summable_norm_mul_pow hinside
    have hz := hs.tendsto_atTop_zero
    rw [Metric.tendsto_atTop] at hz
    obtain ⟨M, hM⟩ := hz 1 zero_lt_one
    have hsmall := hM M le_rfl
    have hhalf : (halfNN : ℝ) = 1 / 2 := by rfl
    have hnonneg : 0 ≤ ‖P M‖ * (halfNN : ℝ) ^ M :=
      mul_nonneg (norm_nonneg _) (pow_nonneg halfNN.property _)
    have hsmall' : ‖P M‖ * (halfNN : ℝ) ^ M < 1 := by
      simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hsmall
    rw [hhalf] at hsmall'
    exact (not_lt_of_ge (hhorseTerm M)) hsmall'
  have hPneTop : P.radius ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hP_upper
  let radiusNN : ℝ≥0 := P.radius.toNNReal
  let radius : ℝ := radiusNN
  have hcoeRadius : (radiusNN : ℝ≥0∞) = P.radius :=
    ENNReal.coe_toNNReal hPneTop
  have hradiusPos : 0 < radius := by
    have hpos : 0 < radiusNN := by
      rw [← ENNReal.coe_pos, hcoeRadius]
      exact hPpos
    exact_mod_cast hpos
  have hradiusLeHalf : radius ≤ 1 / 2 := by
    have hle : radiusNN ≤ halfNN := by
      exact ENNReal.coe_le_coe.mp (hcoeRadius.trans_le hP_upper)
    exact_mod_cast hle
  have hboundary : ∀ n : ℕ, 1 ≤ a n * radius ^ n := by
    intro n
    cases n with
    | zero =>
        have hzero : (1 : ℝ) ≤ a 0 := by
          have hcast : ((2 ^ 0 : ℕ) : ℝ) ≤
              (weakLapCount T 0 : ℝ) := by
            exact_mod_cast G.horse_lower 0
          simpa [a] using hcast
        simpa using hzero
    | succ n =>
        by_contra hnot
        have hcontract : a (n + 1) * radius ^ (n + 1) < 1 :=
          lt_of_not_ge hnot
        let U : Set ℝ := {s | a (n + 1) * s ^ (n + 1) < 1}
        have hUopen : IsOpen U := by
          exact isOpen_lt
            (continuous_const.mul (continuous_id.pow (n + 1))) continuous_const
        have hrU : radius ∈ U := hcontract
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen radius hrU
        let s := radius + ε / 2
        have hrs : radius < s := by dsimp [s]; linarith
        have hs0 : 0 ≤ s := hradiusPos.le.trans hrs.le
        have hsball : s ∈ Metric.ball radius ε := by
          rw [Metric.mem_ball, Real.dist_eq]
          dsimp [s]
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hscontract : a (n + 1) * s ^ (n + 1) < 1 :=
          hball hsball
        have hsum : Summable (fun k : ℕ => a k * s ^ k) :=
          weakSummable_of_submultiplicative_block a ha hsub
            (Nat.succ_pos n) hs0 hscontract
        let sNN : ℝ≥0 := ⟨s, hs0⟩
        have hsLeRadius : (sNN : ℝ≥0∞) ≤ P.radius := by
          apply P.le_radius_of_summable_norm
          simpa [P, weakLapFormalSeries,
            FormalMultilinearSeries.ofScalars_norm, a] using hsum
        rw [← hcoeRadius] at hsLeRadius
        have hsle : s ≤ radius := by
          exact_mod_cast ENNReal.coe_le_coe.mp hsLeRadius
        exact (not_le_of_gt hrs) hsle
  have hsummableBelow : ∀ {s : ℝ}, 0 ≤ s → s < radius →
      Summable (fun n : ℕ => (weakLapCount T n : ℝ) * s ^ n) := by
    intro s hs0 hslt
    let sNN : ℝ≥0 := ⟨s, hs0⟩
    have hsInside : (sNN : ℝ≥0∞) < P.radius := by
      rw [← hcoeRadius, ENNReal.coe_lt_coe]
      exact hslt
    have hs := P.summable_norm_mul_pow hsInside
    simpa [P, weakLapFormalSeries,
      FormalMultilinearSeries.ofScalars_norm, sNN] using hs
  exact ⟨{
    radius := radius
    radius_pos := hradiusPos
    radius_le_half := hradiusLeHalf
    coefficient_boundary := by simpa [a] using hboundary
    summable_below := hsummableBelow }⟩

/-- A concrete increasing approach to the radius, together with convergence
at each sample and divergence of the normalized total mass. -/
structure WeakLapRadiusApproachData (T : IntervalMap)
    (R : WeakLapFormalRadiusData T) where
  sample : ℕ → ℝ
  sample_pos : ∀ n, 0 < sample n
  sample_lt_radius : ∀ n, sample n < R.radius
  sample_strictMono : StrictMono sample
  sample_tendsto : Tendsto sample atTop (𝓝 R.radius)
  series_summable : ∀ n, Summable
    (fun k : ℕ => (weakLapCount T k : ℝ) * sample n ^ k)
  total_tendsto : Tendsto
    (fun n => weakTotalLapResolvent T (sample n)) atTop atTop

/-- The explicit quadratic approach factor supplies the approach package. -/
private theorem weakLapRadiusApproachData_exists {T : IntervalMap}
    (R : WeakLapFormalRadiusData T) :
    Nonempty (WeakLapRadiusApproachData T R) := by
  let factor : ℕ → ℝ := fun n =>
    1 - 1 / ((n : ℝ) + 2) ^ 2
  let sample : ℕ → ℝ := fun n => R.radius * factor n
  have hfactorPos : ∀ n : ℕ, 0 < factor n := by
    intro n
    dsimp [factor]
    have hden : 1 < ((n : ℝ) + 2) ^ 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [sq_nonneg ((n : ℝ) + 2)]
    have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden
    norm_num at hinv
    rw [one_div]
    exact sub_pos.mpr hinv
  have hfactorLt : ∀ n : ℕ, factor n < 1 := by
    intro n
    dsimp [factor]
    have hinv : 0 < 1 / ((n : ℝ) + 2) ^ 2 := by positivity
    linarith
  have hfactorMono : StrictMono factor := by
    intro m n hmn
    dsimp [factor]
    have hmnCast : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    have hmn' : (m : ℝ) + 2 < (n : ℝ) + 2 := by linarith
    have hsquares : ((m : ℝ) + 2) ^ 2 < ((n : ℝ) + 2) ^ 2 := by
      nlinarith [sq_nonneg ((m : ℝ) + 2),
        sq_nonneg ((n : ℝ) + 2)]
    have hinv := one_div_lt_one_div_of_lt
      (show 0 < ((m : ℝ) + 2) ^ 2 by positivity) hsquares
    linarith
  have hfactorTendsto : Tendsto factor atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2))
        atTop (𝓝 0) := by
      have h := (tendsto_add_atTop_iff_nat 2).2
        (tendsto_one_div_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0))
      simpa [Nat.cast_add] using h
    have hinvSq := hinv.pow 2
    have hone :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (𝓝 1)).sub hinvSq
    simpa [factor, one_div_pow] using hone
  have hsamplePos : ∀ n : ℕ, 0 < sample n := fun n =>
    mul_pos R.radius_pos (hfactorPos n)
  have hsampleLt : ∀ n : ℕ, sample n < R.radius := fun n => by
    dsimp [sample]
    nlinarith [mul_lt_mul_of_pos_left (hfactorLt n) R.radius_pos]
  have hsampleMono : StrictMono sample := by
    intro m n hmn
    dsimp [sample]
    exact mul_lt_mul_of_pos_left (hfactorMono hmn) R.radius_pos
  have hsampleTendsto : Tendsto sample atTop (𝓝 R.radius) := by
    convert tendsto_const_nhds.mul hfactorTendsto using 1 <;> simp [sample]
  have hseries : ∀ n : ℕ, Summable
      (fun k : ℕ => (weakLapCount T k : ℝ) * sample n ^ k) := by
    intro n
    exact R.summable_below (hsamplePos n).le (hsampleLt n)
  have hfactorHalfPow : ∀ n : ℕ, (1 / 2 : ℝ) ≤ factor n ^ n := by
    intro n
    have hbern := one_add_mul_sub_le_pow
      (a := factor n) (by linarith [hfactorPos n]) n
    have hdenpos : 0 < ((n : ℝ) + 2) ^ 2 := by positivity
    have hfrac : (n : ℝ) / ((n : ℝ) + 2) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ hdenpos]
      nlinarith [sq_nonneg ((n : ℝ) + 2)]
    dsimp [factor] at hbern ⊢
    have heq :
        1 + (n : ℝ) * (1 - 1 / ((n : ℝ) + 2) ^ 2 - 1) =
          1 - (n : ℝ) / ((n : ℝ) + 2) ^ 2 := by ring
    rw [heq] at hbern
    nlinarith
  have htotalLower : ∀ n : ℕ,
      (n : ℝ) / 2 ≤ weakTotalLapResolvent T (sample n) := by
    intro n
    have hterm : ∀ k ∈ Finset.range n,
        (1 / 2 : ℝ) ≤ (weakLapCount T k : ℝ) * sample n ^ k := by
      intro k hk
      have hkn : k ≤ n := (Finset.mem_range.mp hk).le
      have hf0 : 0 ≤ factor n := (hfactorPos n).le
      have hf1 : factor n ≤ 1 := (hfactorLt n).le
      have hpow : factor n ^ n ≤ factor n ^ k :=
        pow_le_pow_of_le_one hf0 hf1 hkn
      have hb := R.coefficient_boundary k
      calc
        (1 / 2 : ℝ) ≤ factor n ^ n := hfactorHalfPow n
        _ ≤ factor n ^ k := hpow
        _ = 1 * factor n ^ k := by ring
        _ ≤ ((weakLapCount T k : ℝ) * R.radius ^ k) * factor n ^ k :=
          mul_le_mul_of_nonneg_right hb (pow_nonneg hf0 _)
        _ = (weakLapCount T k : ℝ) * sample n ^ k := by
          simp only [sample, mul_pow]
          ring
    have hfinite : (n : ℝ) / 2 ≤
        ∑ k ∈ Finset.range n,
          (weakLapCount T k : ℝ) * sample n ^ k := by
      calc
        (n : ℝ) / 2 =
            ∑ _k ∈ Finset.range n, (1 / 2 : ℝ) := by
          simp [div_eq_mul_inv]
        _ ≤ _ := Finset.sum_le_sum hterm
    refine hfinite.trans ?_
    unfold weakTotalLapResolvent
    exact (hseries n).sum_le_tsum (Finset.range n)
      (fun k _hk => mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (hsamplePos n).le _))
  have htotalTendsto : Tendsto
      (fun n => weakTotalLapResolvent T (sample n)) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Eventually.of_forall htotalLower)
    simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop
        (by norm_num : (0 : ℝ) < 1 / 2))
  exact ⟨{
    sample := sample
    sample_pos := hsamplePos
    sample_lt_radius := hsampleLt
    sample_strictMono := hsampleMono
    sample_tendsto := hsampleTendsto
    series_summable := hseries
    total_tendsto := htotalTendsto }⟩

/-- Growth bounds determine a positive radius at most `1/2` and a divergent
normalizing sequence. -/
theorem weakLapRadiusData_exists {T : IntervalMap}
    (G : WeakLapGrowthData T) : Nonempty (WeakLapRadiusData T) := by
  obtain ⟨R⟩ := weakLapFormalRadiusData_exists G
  obtain ⟨A⟩ := weakLapRadiusApproachData_exists R
  exact ⟨{
    radius := R.radius
    radius_pos := R.radius_pos
    radius_le_half := R.radius_le_half
    sample := A.sample
    sample_pos := A.sample_pos
    sample_lt_radius := A.sample_lt_radius
    sample_strictMono := A.sample_strictMono
    sample_tendsto := A.sample_tendsto
    series_summable := A.series_summable
    total_tendsto := A.total_tendsto }⟩

noncomputable def weakNormalizedLapResolvent {T : IntervalMap}
    (R : WeakLapRadiusData T) (x y : I) (n : ℕ) : ℝ :=
  weakLapResolvent T x y (R.sample n) /
    weakTotalLapResolvent T (R.sample n)

/-! ### RL5 internal compactness and uniform-itinerary chain -/

/-- The total normalizing resolvent is strictly positive at every sampled
parameter. -/
private theorem weakTotalLapResolvent_pos {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T) (n : ℕ) :
    0 < weakTotalLapResolvent T (R.sample n) := by
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  have hzero : weakLapCount T 0 = 1 := by
    change weakLapCountOf (iterateMap T 0)
      leftEndpoint rightEndpoint = 1
    apply weakLapCountOf_eq_one_of_weaklyMonotoneOn
      (hT.iterate 0) hends
    left
    intro x _hx y _hy hxy
    simpa [iterateMap] using hxy
  unfold weakTotalLapResolvent
  exact (R.series_summable n).tsum_pos
    (fun k => mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (R.sample_pos n).le k)) 0 (by simp [hzero])

/-- Every localized weak-lap series is dominated by the summable total
series. -/
theorem weakLapResolvent_summable {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T)
    (x y : I) (n : ℕ) :
    Summable (fun k : ℕ =>
      (weakLapCountOn T k x y : ℝ) * R.sample n ^ k) := by
  apply Summable.of_nonneg_of_le
    (f := fun k : ℕ => (weakLapCount T k : ℝ) * R.sample n ^ k)
  · intro k
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (R.sample_pos n).le k)
  · intro k
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast weakLapCountOn_le_total hT k x y)
      (pow_nonneg (R.sample_pos n).le k)
  · exact R.series_summable n

/-- Every normalized localized resolvent takes values in `[0,1]`. -/
theorem weakNormalizedLapResolvent_bounds {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T)
    {x y : I} (hxy : x ≤ y) (n : ℕ) :
    0 ≤ weakNormalizedLapResolvent R x y n ∧
      weakNormalizedLapResolvent R x y n ≤ 1 := by
  have hs := weakLapResolvent_summable hT R x y n
  have hnum0 : 0 ≤ weakLapResolvent T x y (R.sample n) := by
    unfold weakLapResolvent
    exact tsum_nonneg fun k =>
      mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (R.sample_pos n).le _)
  have hnumle : weakLapResolvent T x y (R.sample n) ≤
      weakTotalLapResolvent T (R.sample n) := by
    unfold weakLapResolvent weakTotalLapResolvent
    apply hs.tsum_le_tsum _ (R.series_summable n)
    intro k
    apply mul_le_mul_of_nonneg_right _
      (pow_nonneg (R.sample_pos n).le _)
    exact_mod_cast weakLapCountOn_le_total hT k x y
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  constructor
  · exact div_nonneg hnum0 hDpos.le
  · apply (div_le_iff₀ hDpos).2
    simpa using hnumle

/-- Quantitative adjacent-additivity: the only possible discrepancy is one
geometric tail, divided by the diverging total mass. -/
private theorem weakNormalizedLapResolvent_adjacent_error
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y z : I}
    (hxy : x < y) (hyz : y < z) :
    ∀ n : ℕ,
      |weakNormalizedLapResolvent R x z n -
          weakNormalizedLapResolvent R x y n -
          weakNormalizedLapResolvent R y z n| ≤
        (1 / (1 - R.sample n)) /
          weakTotalLapResolvent T (R.sample n) := by
  intro n
  let t := R.sample n
  have ht0 : 0 ≤ t := (R.sample_pos n).le
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  have ht1 : t < 1 := (R.sample_lt_radius n).trans hrlt
  have hsxz := weakLapResolvent_summable hT R x z n
  have hsxy := weakLapResolvent_summable hT R x y n
  have hsyz := weakLapResolvent_summable hT R y z n
  have hsum : HasSum
      (fun k : ℕ =>
        (weakLapCountOn T k x z : ℝ) * t ^ k -
          (weakLapCountOn T k x y : ℝ) * t ^ k -
          (weakLapCountOn T k y z : ℝ) * t ^ k)
      (weakLapResolvent T x z t - weakLapResolvent T x y t -
        weakLapResolvent T y z t) := by
    simpa [weakLapResolvent, t] using
      ((hsxz.hasSum.sub hsxy.hasSum).sub hsyz.hasSum)
  have hraw :
      |weakLapResolvent T x z t - weakLapResolvent T x y t -
          weakLapResolvent T y z t| ≤ 1 / (1 - t) := by
    have hbound := hsum.norm_le_of_bounded
      (hasSum_geometric_of_lt_one ht0 ht1) (fun k => by
        have hcoeff :
            |(weakLapCountOn T k x z : ℝ) -
                weakLapCountOn T k x y -
                weakLapCountOn T k y z| ≤ 1 := by
          exact_mod_cast weakLapCountOn_adjacent_error hT k hxy hyz
        rw [Real.norm_eq_abs]
        have halg :
            (weakLapCountOn T k x z : ℝ) * t ^ k -
                (weakLapCountOn T k x y : ℝ) * t ^ k -
                (weakLapCountOn T k y z : ℝ) * t ^ k =
              ((weakLapCountOn T k x z : ℝ) -
                weakLapCountOn T k x y -
                weakLapCountOn T k y z) * t ^ k := by ring
        rw [halg, abs_mul, abs_of_nonneg (pow_nonneg ht0 k)]
        simpa using mul_le_mul_of_nonneg_right hcoeff (pow_nonneg ht0 k))
    simpa [Real.norm_eq_abs, one_div] using hbound
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  have halg :
      weakLapResolvent T x z (R.sample n) /
            weakTotalLapResolvent T (R.sample n) -
          weakLapResolvent T x y (R.sample n) /
            weakTotalLapResolvent T (R.sample n) -
          weakLapResolvent T y z (R.sample n) /
            weakTotalLapResolvent T (R.sample n) =
        (weakLapResolvent T x z (R.sample n) -
          weakLapResolvent T x y (R.sample n) -
          weakLapResolvent T y z (R.sample n)) /
            weakTotalLapResolvent T (R.sample n) := by ring
  rw [halg, abs_div, abs_of_pos hDpos]
  exact div_le_div_of_nonneg_right (by simpa [t] using hraw) hDpos.le

/-- The normalized adjacent-additivity defect tends to zero. -/
theorem weakNormalizedLapResolvent_adjacent_tendsto_zero
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y z : I}
    (hxy : x < y) (hyz : y < z) :
    Tendsto (fun n =>
      weakNormalizedLapResolvent R x z n -
        weakNormalizedLapResolvent R x y n -
        weakNormalizedLapResolvent R y z n)
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => 1 - R.sample n)
      atTop (nhds (1 - R.radius)) :=
    tendsto_const_nhds.sub R.sample_tendsto
  have hdenne : 1 - R.radius ≠ 0 := by
    linarith [R.radius_le_half]
  have hnumer : Tendsto (fun n : ℕ => 1 / (1 - R.sample n))
      atTop (nhds (1 / (1 - R.radius))) :=
    tendsto_const_nhds.div hden hdenne
  have herror : Tendsto
      (fun n : ℕ => (1 / (1 - R.sample n)) /
        weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
    hnumer.div_atTop R.total_tendsto
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ herror
  intro n
  simpa [Real.norm_eq_abs] using
    weakNormalizedLapResolvent_adjacent_error hT R hxy hyz n

/-! ### RL8 one-branch transport chain -/

/-- Quantitative one-branch resolvent transport.  The geometric error also
covers a genuinely constant first branch. -/
private theorem weakNormalizedLapResolvent_branch_error
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    ∀ n : ℕ,
      |weakNormalizedLapResolvent R x y n -
          R.sample n * weakNormalizedLapResolvent R
            (min (T x) (T y)) (max (T x) (T y)) n| ≤
        (1 / (1 - R.sample n)) /
          weakTotalLapResolvent T (R.sample n) := by
  intro n
  let t := R.sample n
  let u := min (T x) (T y)
  let v := max (T x) (T y)
  have ht0 : 0 ≤ t := (R.sample_pos n).le
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  have ht1 : t < 1 := (R.sample_lt_radius n).trans hrlt
  have hsxy := weakLapResolvent_summable hT R x y n
  have hsuv := weakLapResolvent_summable hT R u v n
  have hzero : weakLapCountOn T 0 x y = 1 := by
    change weakLapCountOf (iterateMap T 0) x y = 1
    apply weakLapCountOf_eq_one_of_weaklyMonotoneOn
      (hT.iterate 0) hxy
    left
    intro a _ha b _hb hab
    simpa [iterateMap] using hab
  have htailxy : Summable (fun k : ℕ =>
      (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1)) := by
    simpa [t] using hsxy.comp_injective Nat.succ_injective
  have htailuv : Summable (fun k : ℕ =>
      (weakLapCountOn T k u v : ℝ) * t ^ (k + 1)) := by
    have hmul := hsuv.mul_left t
    apply hmul.congr
    intro k
    simp only [t, pow_succ]
    ring
  have htailxy_tsum :
      (∑' k : ℕ,
          (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1)) =
        weakLapResolvent T x y t - 1 := by
    have hst : Summable (fun k : ℕ =>
        (weakLapCountOn T k x y : ℝ) * t ^ k) := by
      simpa [t] using hsxy
    rw [weakLapResolvent]
    rw [hst.tsum_eq_zero_add]
    simp [hzero]
  have htailuv_tsum :
      (∑' k : ℕ,
          (weakLapCountOn T k u v : ℝ) * t ^ (k + 1)) =
        t * weakLapResolvent T u v t := by
    calc
      (∑' k : ℕ,
          (weakLapCountOn T k u v : ℝ) * t ^ (k + 1)) =
          ∑' k : ℕ,
            t * ((weakLapCountOn T k u v : ℝ) * t ^ k) := by
        apply tsum_congr
        intro k
        rw [pow_succ]
        ring
      _ = t * ∑' k : ℕ,
          (weakLapCountOn T k u v : ℝ) * t ^ k := tsum_mul_left
      _ = t * weakLapResolvent T u v t := by rfl
  have hsum : HasSum
      (fun k : ℕ =>
        (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1) -
          (weakLapCountOn T k u v : ℝ) * t ^ (k + 1))
      (weakLapResolvent T x y t - 1 -
        t * weakLapResolvent T u v t) := by
    simpa [htailxy_tsum, htailuv_tsum] using
      htailxy.hasSum.sub htailuv.hasSum
  have hgeom : HasSum (fun k : ℕ => t ^ (k + 1))
      (t / (1 - t)) := by
    simpa [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one ht0 ht1).mul_left t
  have htailBound :
      |weakLapResolvent T x y t - 1 -
          t * weakLapResolvent T u v t| ≤ t / (1 - t) := by
    have hbound := hsum.norm_le_of_bounded hgeom (fun k => by
      have hcoeff :
          |(weakLapCountOn T (k + 1) x y : ℝ) -
              weakLapCountOn T k u v| ≤ 1 := by
        exact_mod_cast
          weakLapCountOn_succ_branch_error hT hxy hmono k
      rw [Real.norm_eq_abs]
      have halg :
          (weakLapCountOn T (k + 1) x y : ℝ) * t ^ (k + 1) -
              (weakLapCountOn T k u v : ℝ) * t ^ (k + 1) =
            ((weakLapCountOn T (k + 1) x y : ℝ) -
              weakLapCountOn T k u v) * t ^ (k + 1) := by ring
      rw [halg, abs_mul, abs_of_nonneg (pow_nonneg ht0 (k + 1))]
      simpa using mul_le_mul_of_nonneg_right hcoeff
        (pow_nonneg ht0 (k + 1)))
    simpa [Real.norm_eq_abs] using hbound
  have hraw :
      |weakLapResolvent T x y t - t * weakLapResolvent T u v t| ≤
        1 / (1 - t) := by
    calc
      |weakLapResolvent T x y t - t * weakLapResolvent T u v t| =
          |1 + (weakLapResolvent T x y t - 1 -
            t * weakLapResolvent T u v t)| := by congr 1 <;> ring
      _ ≤ |(1 : ℝ)| +
          |weakLapResolvent T x y t - 1 -
            t * weakLapResolvent T u v t| := abs_add_le _ _
      _ ≤ 1 + t / (1 - t) := by
        simpa using add_le_add_left htailBound 1
      _ = 1 / (1 - t) := by
        field_simp [ne_of_gt (sub_pos.mpr ht1)]
        ring
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  have halg :
      weakLapResolvent T x y (R.sample n) /
            weakTotalLapResolvent T (R.sample n) -
          R.sample n *
            (weakLapResolvent T (min (T x) (T y)) (max (T x) (T y))
              (R.sample n) / weakTotalLapResolvent T (R.sample n)) =
        (weakLapResolvent T x y (R.sample n) -
          R.sample n * weakLapResolvent T (min (T x) (T y))
            (max (T x) (T y)) (R.sample n)) /
              weakTotalLapResolvent T (R.sample n) := by ring
  rw [halg, abs_div, abs_of_pos hDpos]
  exact div_le_div_of_nonneg_right (by simpa [t, u, v] using hraw) hDpos.le

/-- After normalization, the one-branch transport defect tends to zero. -/
theorem weakNormalizedLapResolvent_branch_tendsto_zero
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    Tendsto (fun n =>
      weakNormalizedLapResolvent R x y n -
        R.sample n * weakNormalizedLapResolvent R
          (min (T x) (T y)) (max (T x) (T y)) n)
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ => 1 - R.sample n)
      atTop (nhds (1 - R.radius)) :=
    tendsto_const_nhds.sub R.sample_tendsto
  have hdenne : 1 - R.radius ≠ 0 := by
    linarith [R.radius_le_half]
  have hnumer : Tendsto (fun n : ℕ => 1 / (1 - R.sample n))
      atTop (nhds (1 / (1 - R.radius))) :=
    tendsto_const_nhds.div hden hdenne
  have herror : Tendsto
      (fun n : ℕ => (1 / (1 - R.sample n)) /
        weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
    hnumer.div_atTop R.total_tendsto
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ herror
  intro n
  simpa [Real.norm_eq_abs] using
    weakNormalizedLapResolvent_branch_error hT R hxy hmono n

/-- Every prefix of an `m`-step weak itinerary cell remains weakly
monotone on the original interval. -/
private theorem weakItineraryCell_iterate_weaklyMonotoneOn
    {T : IntervalMap} {m k : ℕ} {x y : I} (hxy : x ≤ y)
    (hcell : IsWeakItineraryCell T m x y) (hk : k ≤ m) :
    IsWeaklyMonotoneOn (iterateMap T k) (Set.Icc x y) := by
  induction k with
  | zero =>
      left
      intro a _ha b _hb hab
      simpa [iterateMap] using hab
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      have hprev := ih (Nat.le_of_lt hklt)
      have hstep := hcell k hklt
      have hmaps : Set.MapsTo (iterateMap T k) (Set.Icc x y)
          (Set.Icc
            (min (iterateMap T k x) (iterateMap T k y))
            (max (iterateMap T k x) (iterateMap T k y))) := by
        intro z hz
        rcases hprev with hinc | hdec
        · have hlower : iterateMap T k x ≤ iterateMap T k z :=
            hinc ⟨le_rfl, hxy⟩ hz hz.1
          have hupper : iterateMap T k z ≤ iterateMap T k y :=
            hinc hz ⟨hxy, le_rfl⟩ hz.2
          exact ⟨(min_le_left _ _).trans hlower,
            hupper.trans (le_max_right _ _)⟩
        · have hlower : iterateMap T k y ≤ iterateMap T k z :=
            hdec hz ⟨hxy, le_rfl⟩ hz.2
          have hupper : iterateMap T k z ≤ iterateMap T k x :=
            hdec ⟨le_rfl, hxy⟩ hz hz.1
          exact ⟨(min_le_right _ _).trans hlower,
            hupper.trans (le_max_left _ _)⟩
      have hcomp := hstep.comp hprev hmaps
      have hiter : T ∘ iterateMap T k = iterateMap T (k + 1) := by
        funext z
        change T ((T^[k]) z) = (T^[k + 1]) z
        rw [Function.iterate_succ_apply]
        exact (Function.Commute.self_iterate T k).eq z
      rw [hiter] at hcomp
      exact hcomp

/-- Once the first `m` iterates form one weak itinerary cell, the remaining
`j` iterates require no more cells there than the global `j`-lap count. -/
private theorem weakLapCountOn_add_le_total_of_iterate_weaklyMonotone
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {m j : ℕ} {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn (iterateMap T m) (Set.Icc x y)) :
    weakLapCountOn T (m + j) x y ≤ weakLapCount T j := by
  let φ : IntervalMap := iterateMap T m
  let F : IntervalMap := iterateMap T j
  have hφ : FinitePieceMonotone φ := hT.iterate m
  have hF : FinitePieceMonotone F := hT.iterate j
  have hcomp : FinitePieceMonotone (F ∘ φ) := hF.comp hφ
  have hiter : iterateMap T (m + j) = F ∘ φ := by
    funext z
    simp only [F, φ, iterateMap, Function.comp_apply,
      Function.iterate_add_apply]
    exact ((Function.Commute.refl T).iterate_iterate m j).eq z
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  have htotalPos : 0 < weakLapCount T j := by
    change 0 < weakLapCountOf F leftEndpoint rightEndpoint
    exact weakLapCountOf_pos hF hends
  rcases hmono with hinc | hdec
  · have hφends : φ x ≤ φ y :=
      hinc ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
    by_cases heq : φ x = φ y
    · have hconst : ∀ z ∈ Set.Icc x y, φ z = φ x := by
        intro z hz
        apply le_antisymm
        · simpa [heq] using hinc hz ⟨hxy.le, le_rfl⟩ hz.2
        · exact hinc ⟨le_rfl, hxy.le⟩ hz hz.1
      have hweakComp :
          IsWeaklyMonotoneOn (F ∘ φ) (Set.Icc x y) := by
        left
        intro a ha b hb _hab
        simp only [Function.comp_apply]
        rw [hconst a ha, hconst b hb]
      have hsource : weakLapCountOn T (m + j) x y = 1 := by
        change weakLapCountOf (iterateMap T (m + j)) x y = 1
        rw [hiter]
        exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
          hcomp hxy hweakComp
      rw [hsource]
      exact htotalPos
    · have hstrict : φ x < φ y := lt_of_le_of_ne hφends heq
      rcases weakLapCountOf_attained hF hstrict with ⟨A, hA⟩
      rcases A.pull_monotoneOn hxy hφ.continuous hinc hstrict with
        ⟨Q, hQ⟩
      change weakLapCountOf (iterateMap T (m + j)) x y ≤
        weakLapCount T j
      rw [hiter]
      calc
        weakLapCountOf (F ∘ φ) x y ≤ Q.cellCount :=
          weakLapCountOf_minimal hcomp hxy Q
        _ = weakLapCountOn T j (φ x) (φ y) := by
          simpa [F, weakLapCountOn] using hQ.trans hA
        _ ≤ weakLapCount T j := weakLapCountOn_le_total hT j _ _
  · have hφends : φ y ≤ φ x :=
      hdec ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy.le
    by_cases heq : φ x = φ y
    · have hconst : ∀ z ∈ Set.Icc x y, φ z = φ x := by
        intro z hz
        apply le_antisymm
        · exact hdec ⟨le_rfl, hxy.le⟩ hz hz.1
        · simpa [heq] using hdec hz ⟨hxy.le, le_rfl⟩ hz.2
      have hweakComp :
          IsWeaklyMonotoneOn (F ∘ φ) (Set.Icc x y) := by
        left
        intro a ha b hb _hab
        simp only [Function.comp_apply]
        rw [hconst a ha, hconst b hb]
      have hsource : weakLapCountOn T (m + j) x y = 1 := by
        change weakLapCountOf (iterateMap T (m + j)) x y = 1
        rw [hiter]
        exact weakLapCountOf_eq_one_of_weaklyMonotoneOn
          hcomp hxy hweakComp
      rw [hsource]
      exact htotalPos
    · have hne : φ y ≠ φ x := fun h => heq h.symm
      have hstrict : φ y < φ x := lt_of_le_of_ne hφends hne
      rcases weakLapCountOf_attained hF hstrict with ⟨A, hA⟩
      rcases A.pull_antitoneOn hxy hφ.continuous hdec hstrict with
        ⟨Q, hQ⟩
      change weakLapCountOf (iterateMap T (m + j)) x y ≤
        weakLapCount T j
      rw [hiter]
      calc
        weakLapCountOf (F ∘ φ) x y ≤ Q.cellCount :=
          weakLapCountOf_minimal hcomp hxy Q
        _ = weakLapCountOn T j (φ y) (φ x) := by
          simpa [F, weakLapCountOn] using hQ.trans hA
        _ ≤ weakLapCount T j := weakLapCountOn_le_total hT j _ _

/-- A genuine `m`-step itinerary cell has normalized mass bounded by the
terminal radius power plus the accumulated finite prefix error. -/
theorem weakNormalizedLapResolvent_le_pow_of_weakItineraryCell
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) {m : ℕ} {x y : I} (hxy : x < y)
    (hcell : IsWeakItineraryCell T m x y) (n : ℕ) :
    weakNormalizedLapResolvent R x y n ≤
      (m : ℝ) / weakTotalLapResolvent T (R.sample n) +
        R.sample n ^ m := by
  let t := R.sample n
  have ht0 : 0 ≤ t := (R.sample_pos n).le
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  have ht1 : t < 1 := (R.sample_lt_radius n).trans hrlt
  have hs := weakLapResolvent_summable hT R x y n
  have hs_t : Summable (fun k : ℕ =>
      (weakLapCountOn T k x y : ℝ) * t ^ k) := by
    simpa [t] using hs
  have htotal_t : Summable (fun k : ℕ =>
      (weakLapCount T k : ℝ) * t ^ k) := by
    simpa [t] using R.series_summable n
  have hprefixCount : ∀ {k : ℕ}, k < m →
      weakLapCountOn T k x y = 1 := by
    intro k hk
    change weakLapCountOf (iterateMap T k) x y = 1
    apply weakLapCountOf_eq_one_of_weaklyMonotoneOn
      (hT.iterate k) hxy
    exact weakItineraryCell_iterate_weaklyMonotoneOn
      hxy.le hcell (Nat.le_of_lt hk)
  have hmmono : IsWeaklyMonotoneOn (iterateMap T m)
      (Set.Icc x y) :=
    weakItineraryCell_iterate_weaklyMonotoneOn hxy.le hcell le_rfl
  have htailCount : ∀ j : ℕ,
      weakLapCountOn T (j + m) x y ≤ weakLapCount T j := by
    intro j
    simpa [Nat.add_comm] using
      weakLapCountOn_add_le_total_of_iterate_weaklyMonotone
        hT hxy hmmono (j := j)
  have htailSource : Summable (fun j : ℕ =>
      (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m)) := by
    apply hs_t.comp_injective
    intro a b hab
    exact Nat.add_right_cancel hab
  have htailCompare : Summable (fun j : ℕ =>
      t ^ m * ((weakLapCount T j : ℝ) * t ^ j)) :=
    htotal_t.mul_left (t ^ m)
  have htailLe :
      (∑' j : ℕ,
          (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m)) ≤
        t ^ m * weakTotalLapResolvent T t := by
    calc
      (∑' j : ℕ,
          (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m)) ≤
          ∑' j : ℕ,
            t ^ m * ((weakLapCount T j : ℝ) * t ^ j) := by
        apply htailSource.tsum_le_tsum _ htailCompare
        intro j
        have hcount :
            (weakLapCountOn T (j + m) x y : ℝ) ≤
              weakLapCount T j := by
          exact_mod_cast htailCount j
        calc
          (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m) ≤
              (weakLapCount T j : ℝ) * t ^ (j + m) :=
            mul_le_mul_of_nonneg_right hcount
              (pow_nonneg ht0 (j + m))
          _ = t ^ m * ((weakLapCount T j : ℝ) * t ^ j) := by
            rw [pow_add]
            ring
      _ = t ^ m * ∑' j : ℕ,
          ((weakLapCount T j : ℝ) * t ^ j) := tsum_mul_left
      _ = t ^ m * weakTotalLapResolvent T t := by rfl
  have hprefixLe :
      (∑ k ∈ Finset.range m,
          (weakLapCountOn T k x y : ℝ) * t ^ k) ≤ (m : ℝ) := by
    calc
      (∑ k ∈ Finset.range m,
          (weakLapCountOn T k x y : ℝ) * t ^ k) =
          ∑ k ∈ Finset.range m, t ^ k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hprefixCount (Finset.mem_range.mp hk)]
        simp
      _ ≤ ∑ _k ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _hk
        exact pow_le_one₀ ht0 ht1.le
      _ = (m : ℝ) := by simp
  have hresLe : weakLapResolvent T x y t ≤
      (m : ℝ) + t ^ m * weakTotalLapResolvent T t := by
    unfold weakLapResolvent
    calc
      (∑' k : ℕ, (weakLapCountOn T k x y : ℝ) * t ^ k) =
          (∑ k ∈ Finset.range m,
              (weakLapCountOn T k x y : ℝ) * t ^ k) +
            ∑' j : ℕ,
              (weakLapCountOn T (j + m) x y : ℝ) * t ^ (j + m) :=
        (hs_t.sum_add_tsum_nat_add m).symm
      _ ≤ (m : ℝ) + t ^ m * weakTotalLapResolvent T t :=
        add_le_add hprefixLe htailLe
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  apply (div_le_iff₀ hDpos).2
  calc
    weakLapResolvent T x y (R.sample n) ≤
        (m : ℝ) + (R.sample n) ^ m *
          weakTotalLapResolvent T (R.sample n) := by
      simpa [t] using hresLe
    _ = ((m : ℝ) / weakTotalLapResolvent T (R.sample n) +
          R.sample n ^ m) * weakTotalLapResolvent T (R.sample n) := by
      field_simp [hDpos.ne']

/-- Around every point, weak-itinerary cells on both sides have uniformly
small normalized mass for all sufficiently late samples. -/
theorem weakNormalizedLapResolvent_twoSided_eventually_small
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) (x : I) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ a b : I,
      a ≤ x ∧ x ≤ b ∧
      (leftEndpoint < x → a < x) ∧
      (x < rightEndpoint → x < b) ∧
      IsWeakItineraryCell T m a x ∧
      IsWeakItineraryCell T m x b ∧
      ∀ᶠ n in atTop,
        (a = x ∨ weakNormalizedLapResolvent R a x n < ε) ∧
        (x = b ∨ weakNormalizedLapResolvent R x b n < ε) := by
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  obtain ⟨m, hmpow⟩ := exists_pow_lt_of_lt_one hε hrlt
  obtain ⟨a, b, hax, hxb, haleft, haright, hcellLeft,
      hcellRight⟩ := exists_twoSided_weakItineraryCell hT m x
  have hsmall : ∀ {u v : I}, u < v →
      IsWeakItineraryCell T m u v →
      ∀ᶠ n : ℕ in atTop,
        weakNormalizedLapResolvent R u v n < ε := by
    intro u v huv hcell
    have hzero : Tendsto
        (fun n : ℕ => (m : ℝ) /
          weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop R.total_tendsto
    have hlim : Tendsto
        (fun n : ℕ => (m : ℝ) /
            weakTotalLapResolvent T (R.sample n) + R.sample n ^ m)
        atTop (nhds (R.radius ^ m)) := by
      simpa using hzero.add (R.sample_tendsto.pow m)
    have hevent : ∀ᶠ n : ℕ in atTop,
        (m : ℝ) / weakTotalLapResolvent T (R.sample n) +
          R.sample n ^ m < ε :=
      (tendsto_order.1 hlim).2 ε hmpow
    filter_upwards [hevent] with n hn
    exact (weakNormalizedLapResolvent_le_pow_of_weakItineraryCell
      hT R huv hcell n).trans_lt hn
  have hleft : ∀ᶠ n : ℕ in atTop,
      a = x ∨ weakNormalizedLapResolvent R a x n < ε := by
    by_cases heq : a = x
    · exact Filter.Eventually.of_forall fun _ => Or.inl heq
    · have hlt : a < x := lt_of_le_of_ne hax heq
      filter_upwards [hsmall hlt hcellLeft] with n hn
      exact Or.inr hn
  have hright : ∀ᶠ n : ℕ in atTop,
      x = b ∨ weakNormalizedLapResolvent R x b n < ε := by
    by_cases heq : x = b
    · exact Filter.Eventually.of_forall fun _ => Or.inl heq
    · have hlt : x < b := lt_of_le_of_ne hxb heq
      filter_upwards [hsmall hlt hcellRight] with n hn
      exact Or.inr hn
  refine ⟨m, a, b, hax, hxb, haleft, haright, hcellLeft,
    hcellRight, ?_⟩
  filter_upwards [hleft, hright] with n hnleft hnright
  exact ⟨hnleft, hnright⟩

/-- Enlarging an interval can only increase its normalized weak-lap
resolvent. -/
private theorem weakNormalizedLapResolvent_mono
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T)
    {a x y b : I} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b)
    (n : ℕ) :
    weakNormalizedLapResolvent R x y n ≤
      weakNormalizedLapResolvent R a b n := by
  have hsxy := weakLapResolvent_summable hT R x y n
  have hsab := weakLapResolvent_summable hT R a b n
  have hnumle : weakLapResolvent T x y (R.sample n) ≤
      weakLapResolvent T a b (R.sample n) := by
    unfold weakLapResolvent
    apply hsxy.tsum_le_tsum _ hsab
    intro k
    apply mul_le_mul_of_nonneg_right _
      (pow_nonneg (R.sample_pos n).le k)
    exact_mod_cast weakLapCountOn_mono hT k hax hxy hyb
  have hDpos := weakTotalLapResolvent_pos hT R n
  simp only [weakNormalizedLapResolvent]
  exact (div_le_div_iff_of_pos_right hDpos).2 hnumle

/-- Compact product diagonalization along a countable dense subset. -/
structure WeakLapDenseDiagonalData
    (T : IntervalMap) (R : WeakLapRadiusData T) where
  densePoint : ℕ → I
  densePoint_dense : DenseRange densePoint
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  limitAtDense : ℕ → ℝ
  tendsto_dense : ∀ j : ℕ,
    Tendsto
      (fun n => weakNormalizedLapResolvent R leftEndpoint (densePoint j)
        (subsequence n))
      atTop (𝓝 (limitAtDense j))

/-- The bounded cumulative resolvents admit one convergent subsequence on a
fixed countable dense subset. -/
private theorem weakLapDenseDiagonalData_exists {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T) :
    Nonempty (WeakLapDenseDiagonalData T R) := by
  let d : ℕ → I := TopologicalSpace.denseSeq I
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq I
  let A : ℕ → (ℕ → Set.Icc (0 : ℝ) 1) := fun n j =>
    ⟨weakNormalizedLapResolvent R leftEndpoint (d j) n,
      weakNormalizedLapResolvent_bounds hT R
        (show leftEndpoint ≤ d j from (d j).property.1) n⟩
  obtain ⟨g, φ, hφ, hAg⟩ := CompactSpace.tendsto_subseq A
  have hdenseLimit : ∀ j : ℕ, Tendsto
      (fun n => weakNormalizedLapResolvent R leftEndpoint (d j) (φ n))
      atTop (nhds ((g j : Set.Icc (0 : ℝ) 1) : ℝ)) := by
    intro j
    have hj := tendsto_pi_nhds.1 hAg j
    have hj' := (continuous_subtype_val.tendsto (g j)).comp hj
    simpa [A, Function.comp_apply] using hj'
  exact ⟨{
    densePoint := d
    densePoint_dense := hdense
    subsequence := φ
    subsequence_strictMono := hφ
    limitAtDense := fun j => ((g j : Set.Icc (0 : ℝ) 1) : ℝ)
    tendsto_dense := hdenseLimit }⟩

/-- Uniform itinerary control upgrades dense-point convergence to the
Cauchy property at every point of the interval. -/
private theorem weakLapCumulative_cauchy_of_denseDiagonal
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (R : WeakLapRadiusData T) (D : WeakLapDenseDiagonalData T R) :
    ∀ x : I, CauchySeq
      (fun n => weakNormalizedLapResolvent R leftEndpoint x
        (D.subsequence n)) := by
  let d : ℕ → I := D.densePoint
  let φ : ℕ → ℕ := D.subsequence
  have hdense : DenseRange d := by
    simpa [d] using D.densePoint_dense
  have hdenseLimit : ∀ j : ℕ, Tendsto
      (fun n => weakNormalizedLapResolvent R leftEndpoint (d j) (φ n))
      atTop (nhds (D.limitAtDense j)) := by
    intro j
    simpa [d, φ] using D.tendsto_dense j
  have hφtop : Tendsto φ atTop atTop := by
    simpa [φ] using D.subsequence_strictMono.tendsto_atTop
  intro x
  by_cases hxl : x = leftEndpoint
  · subst x
    apply Metric.cauchySeq_iff.2
    intro ε hε
    refine ⟨0, ?_⟩
    intro p _hp q _hq
    simp [weakNormalizedLapResolvent, weakLapResolvent,
      weakLapCountOn, weakLapCountOf]
    exact hε
  · have hlx : leftEndpoint < x :=
      lt_of_le_of_ne x.property.1 (Ne.symm hxl)
    apply Metric.cauchySeq_iff.2
    intro ε hε
    let δ : ℝ := ε / 6
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨m, a, b, hax, _hxb, haleft, _haright,
        _hcellLeft, _hcellRight, hsmall⟩ :=
      weakNormalizedLapResolvent_twoSided_eventually_small hT R x hδ
    have hax' : a < x := haleft hlx
    obtain ⟨j, hj⟩ := hdense.exists_mem_open isOpen_Ioo
      (Set.nonempty_Ioo.mpr hax')
    have hleftdj : leftEndpoint < d j :=
      a.property.1.trans_lt hj.1
    have hmassAX : ∀ᶠ n : ℕ in atTop,
        weakNormalizedLapResolvent R a x n < δ := by
      filter_upwards [hsmall] with n hn
      exact hn.1.resolve_left hax'.ne
    have hmassφ : ∀ᶠ n : ℕ in atTop,
        weakNormalizedLapResolvent R (d j) x (φ n) < δ := by
      filter_upwards [hφtop.eventually hmassAX] with n hn
      exact (weakNormalizedLapResolvent_mono hT R
        (a := a) (x := d j) (y := x) (b := x)
        hj.1.le hj.2.le le_rfl (φ n)).trans_lt hn
    have herrBase :=
      weakNormalizedLapResolvent_adjacent_tendsto_zero
        hT R hleftdj hj.2
    have herrComp : Tendsto
        (fun n =>
          weakNormalizedLapResolvent R leftEndpoint x (φ n) -
            weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
            weakNormalizedLapResolvent R (d j) x (φ n))
        atTop (nhds 0) := by
      simpa [Function.comp_apply] using herrBase.comp hφtop
    have herrNorm : Tendsto
        (fun n =>
          |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
            weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
            weakNormalizedLapResolvent R (d j) x (φ n)|)
        atTop (nhds 0) := by
      simpa [Real.norm_eq_abs] using
        tendsto_zero_iff_norm_tendsto_zero.mp herrComp
    have herrφ : ∀ᶠ n : ℕ in atTop,
        |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
            weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
            weakNormalizedLapResolvent R (d j) x (φ n)| < δ :=
      (tendsto_order.1 herrNorm).2 δ hδ
    have hclose : ∀ᶠ n : ℕ in atTop,
        dist (weakNormalizedLapResolvent R leftEndpoint x (φ n))
          (weakNormalizedLapResolvent R leftEndpoint (d j) (φ n)) <
            ε / 3 := by
      filter_upwards [hmassφ, herrφ] with n hmassn herrn
      have hmassNonneg :=
        (weakNormalizedLapResolvent_bounds hT R hj.2.le (φ n)).1
      rw [Real.dist_eq]
      calc
        |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
            weakNormalizedLapResolvent R leftEndpoint (d j) (φ n)| =
            |(weakNormalizedLapResolvent R leftEndpoint x (φ n) -
                weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
                weakNormalizedLapResolvent R (d j) x (φ n)) +
              weakNormalizedLapResolvent R (d j) x (φ n)| := by
          congr 1
          ring
        _ ≤
            |weakNormalizedLapResolvent R leftEndpoint x (φ n) -
                weakNormalizedLapResolvent R leftEndpoint (d j) (φ n) -
                weakNormalizedLapResolvent R (d j) x (φ n)| +
              |weakNormalizedLapResolvent R (d j) x (φ n)| :=
          abs_add_le _ _
        _ < δ + δ := by
          rw [abs_of_nonneg hmassNonneg]
          exact add_lt_add herrn hmassn
        _ = ε / 3 := by dsimp [δ]; ring
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hclose
    obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1
      (hdenseLimit j).cauchySeq (ε / 3) (by linarith)
    refine ⟨max N₁ N₂, ?_⟩
    intro p hp q hq
    have hp₁ : N₁ ≤ p := (le_max_left _ _).trans hp
    have hq₁ : N₁ ≤ q := (le_max_left _ _).trans hq
    have hp₂ : N₂ ≤ p := (le_max_right _ _).trans hp
    have hq₂ : N₂ ≤ q := (le_max_right _ _).trans hq
    calc
      dist (weakNormalizedLapResolvent R leftEndpoint x (φ p))
          (weakNormalizedLapResolvent R leftEndpoint x (φ q)) ≤
          dist (weakNormalizedLapResolvent R leftEndpoint x (φ p))
              (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p)) +
            dist (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p))
              (weakNormalizedLapResolvent R leftEndpoint x (φ q)) :=
        dist_triangle _ _ _
      _ ≤ dist (weakNormalizedLapResolvent R leftEndpoint x (φ p))
              (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p)) +
            (dist (weakNormalizedLapResolvent R leftEndpoint (d j) (φ p))
                (weakNormalizedLapResolvent R leftEndpoint (d j) (φ q)) +
              dist (weakNormalizedLapResolvent R leftEndpoint (d j) (φ q))
                (weakNormalizedLapResolvent R leftEndpoint x (φ q))) := by
        gcongr
        exact dist_triangle _ _ _
      _ < ε / 3 + (ε / 3 + ε / 3) := by
        gcongr
        · exact hN₁ p hp₁
        · exact hN₂ p hp₂ q hq₂
        · simpa [dist_comm] using hN₁ q hq₁
      _ = ε := by ring

/-- One subsequence on which all cumulative normalized resolvents converge. -/
structure WeakLapCumulativeLimitData
    (T : IntervalMap) (R : WeakLapRadiusData T) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  cumulative : I → ℝ
  tendsto_cumulative : ∀ x : I,
    Tendsto
      (fun n => weakNormalizedLapResolvent R leftEndpoint x (subsequence n))
      atTop (𝓝 (cumulative x))

/-- Compact diagonalization and the uniform itinerary estimate give the
cumulative subsequential limit. -/
theorem weakLapCumulativeLimitData_exists {T : IntervalMap}
    (hT : FinitePieceMonotone T) (R : WeakLapRadiusData T) :
    Nonempty (WeakLapCumulativeLimitData T R) := by
  obtain ⟨D⟩ := weakLapDenseDiagonalData_exists hT R
  have hcauchy := weakLapCumulative_cauchy_of_denseDiagonal hT R D
  choose f hf using fun x : I => cauchySeq_tendsto_of_complete (hcauchy x)
  exact ⟨{
    subsequence := D.subsequence
    subsequence_strictMono := D.subsequence_strictMono
    cumulative := f
    tendsto_cumulative := hf }⟩

/-- The localized limiting interval functional. -/
structure WeakLapLimitData
    (T : IntervalMap) (R : WeakLapRadiusData T) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  value : I → I → ℝ
  value_diag : ∀ x : I, value x x = 0
  tendsto_value : ∀ {x y : I}, x < y →
    Tendsto
      (fun n => weakNormalizedLapResolvent R x y (subsequence n))
      atTop (𝓝 (value x y))

/-! ### RL6 adjacent-additivity passage -/

/-- The cumulative limit is normalized to zero at the left endpoint. -/
theorem WeakLapCumulativeLimitData.cumulative_leftEndpoint
    {T : IntervalMap} {R : WeakLapRadiusData T}
    (C : WeakLapCumulativeLimitData T R) :
    C.cumulative leftEndpoint = 0 := by
  apply tendsto_nhds_unique (C.tendsto_cumulative leftEndpoint)
  simpa [weakNormalizedLapResolvent, weakLapResolvent,
    weakLapCountOn, weakLapCountOf] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (nhds 0))

/-- Subtracting the vanishing adjacent-additivity defect identifies the
localized limit with the difference of the two cumulative limits. -/
theorem weakNormalizedLapResolvent_tendsto_localized_of_cumulative
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (C : WeakLapCumulativeLimitData T R)
    {x y : I} (hxy : x < y) :
    Tendsto
      (fun n => weakNormalizedLapResolvent R x y (C.subsequence n))
      atTop (𝓝 (C.cumulative y - C.cumulative x)) := by
  by_cases hxl : x = leftEndpoint
  · subst x
    simpa [C.cumulative_leftEndpoint] using C.tendsto_cumulative y
  · have hlx : leftEndpoint < x :=
      lt_of_le_of_ne x.property.1 (Ne.symm hxl)
    have hdiff : Tendsto
        (fun n =>
          weakNormalizedLapResolvent R leftEndpoint y (C.subsequence n) -
            weakNormalizedLapResolvent R leftEndpoint x (C.subsequence n))
        atTop (nhds (C.cumulative y - C.cumulative x)) :=
      (C.tendsto_cumulative y).sub (C.tendsto_cumulative x)
    have herr : Tendsto
        (fun n =>
          weakNormalizedLapResolvent R leftEndpoint y (C.subsequence n) -
            weakNormalizedLapResolvent R leftEndpoint x (C.subsequence n) -
            weakNormalizedLapResolvent R x y (C.subsequence n))
        atTop (nhds 0) := by
      simpa [Function.comp_apply] using
        (weakNormalizedLapResolvent_adjacent_tendsto_zero
          hT R hlx hxy).comp C.subsequence_strictMono.tendsto_atTop
    have hlim := hdiff.sub herr
    convert hlim using 1 <;> ring

/-- The adjacent-error estimate recovers every localized limit from the
cumulative limit. -/
theorem weakLapLimitData_exists {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (C : WeakLapCumulativeLimitData T R) :
    Nonempty (WeakLapLimitData T R) := by
  exact ⟨{
    subsequence := C.subsequence
    subsequence_strictMono := C.subsequence_strictMono
    value := fun x y => C.cumulative y - C.cumulative x
    value_diag := by intro x; simp
    tendsto_value := by
      intro x y hxy
      exact weakNormalizedLapResolvent_tendsto_localized_of_cumulative
        hT C hxy }⟩

/-! ### RL7 construction of the interval coordinate -/

/-- The weak-lap limit is nonnegative, bounded by one, and normalized on the
whole interval. -/
theorem weakLapLimit_bounds {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) {x y : I} (hxy : x < y) :
    (0 ≤ L.value x y ∧ L.value x y ≤ 1) ∧
      L.value leftEndpoint rightEndpoint = 1 := by
  constructor
  · have htend := L.tendsto_value hxy
    constructor
    · apply ge_of_tendsto' htend
      intro n
      exact (weakNormalizedLapResolvent_bounds hT R hxy.le
        (L.subsequence n)).1
    · apply le_of_tendsto' htend
      intro n
      exact (weakNormalizedLapResolvent_bounds hT R hxy.le
        (L.subsequence n)).2
  · have hends : leftEndpoint < rightEndpoint := by
      norm_num [leftEndpoint, rightEndpoint]
    have hone : ∀ n : ℕ,
        weakNormalizedLapResolvent R leftEndpoint rightEndpoint n = 1 := by
      intro n
      have hnum : weakLapResolvent T leftEndpoint rightEndpoint
          (R.sample n) = weakTotalLapResolvent T (R.sample n) := by
        unfold weakLapResolvent weakTotalLapResolvent weakLapCount
        rfl
      simp only [weakNormalizedLapResolvent, hnum]
      exact div_self (weakTotalLapResolvent_pos hT R n).ne'
    have honeTend : Tendsto
        (fun n => weakNormalizedLapResolvent R leftEndpoint rightEndpoint
          (L.subsequence n)) atTop (nhds 1) := by
      simpa only [hone] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
          atTop (nhds 1))
    exact tendsto_nhds_unique (L.tendsto_value hends) honeTend

/-- Adjacent additivity becomes exact in the weak-lap limit. -/
theorem weakLapLimit_adjacent {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) {x y z : I}
    (hxy : x < y) (hyz : y < z) :
    L.value x z = L.value x y + L.value y z := by
  have hrawLimit : Tendsto
      (fun n => weakNormalizedLapResolvent R x z (L.subsequence n) -
        weakNormalizedLapResolvent R x y (L.subsequence n) -
        weakNormalizedLapResolvent R y z (L.subsequence n))
      atTop (nhds (L.value x z - L.value x y - L.value y z)) :=
    ((L.tendsto_value (hxy.trans hyz)).sub (L.tendsto_value hxy)).sub
      (L.tendsto_value hyz)
  have hrawZero : Tendsto
      (fun n => weakNormalizedLapResolvent R x z (L.subsequence n) -
        weakNormalizedLapResolvent R x y (L.subsequence n) -
        weakNormalizedLapResolvent R y z (L.subsequence n))
      atTop (nhds 0) := by
    simpa [Function.comp_apply] using
      (weakNormalizedLapResolvent_adjacent_tendsto_zero
        hT R hxy hyz).comp L.subsequence_strictMono.tendsto_atTop
  have heq : L.value x z - L.value x y - L.value y z = 0 :=
    tendsto_nhds_unique hrawLimit hrawZero
  linarith

/-- On an `m`-step weak itinerary cell, the limiting mass is at most the
`m`th power of the convergence radius. -/
theorem weakLapLimit_le_pow_of_weakItineraryCell
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R)
    {m : ℕ} {x y : I} (hxy : x < y)
    (hcell : IsWeakItineraryCell T m x y) :
    L.value x y ≤ R.radius ^ m := by
  have hsubTop : Tendsto L.subsequence atTop atTop :=
    L.subsequence_strictMono.tendsto_atTop
  have hzero : Tendsto
      (fun n : ℕ => (m : ℝ) /
        weakTotalLapResolvent T (R.sample n)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop R.total_tendsto
  have hzeroSub : Tendsto
      (fun n : ℕ => (m : ℝ) /
        weakTotalLapResolvent T (R.sample (L.subsequence n)))
      atTop (nhds 0) := by
    simpa [Function.comp_apply] using hzero.comp hsubTop
  have hsampleSub : Tendsto
      (fun n : ℕ => R.sample (L.subsequence n))
      atTop (nhds R.radius) := R.sample_tendsto.comp hsubTop
  have hboundLimit : Tendsto
      (fun n : ℕ => (m : ℝ) /
          weakTotalLapResolvent T (R.sample (L.subsequence n)) +
        R.sample (L.subsequence n) ^ m)
      atTop (nhds (R.radius ^ m)) := by
    simpa using hzeroSub.add (hsampleSub.pow m)
  exact le_of_tendsto_of_tendsto'
    (L.tendsto_value hxy) hboundLimit (fun n =>
      weakNormalizedLapResolvent_le_pow_of_weakItineraryCell
        hT R hxy hcell (L.subsequence n))

/-- Every point has two-sided intervals of arbitrarily small limiting
weak-lap mass, with the endpoint cases represented by degenerate sides. -/
theorem weakLapLimit_twoSided_smallness
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R)
    (x : I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : I, a ≤ x ∧ x ≤ b ∧
      (leftEndpoint < x → a < x) ∧
      (x < rightEndpoint → x < b) ∧
      (a = x ∨ L.value a x < ε) ∧
      (x = b ∨ L.value x b < ε) := by
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  obtain ⟨m, hmpow⟩ := exists_pow_lt_of_lt_one hε hrlt
  obtain ⟨a, b, hax, hxb, haleft, haright, hcellLeft,
      hcellRight⟩ := exists_twoSided_weakItineraryCell hT m x
  refine ⟨a, b, hax, hxb, haleft, haright, ?_, ?_⟩
  · by_cases heq : a = x
    · exact Or.inl heq
    · right
      exact (weakLapLimit_le_pow_of_weakItineraryCell hT L
        (lt_of_le_of_ne hax heq) hcellLeft).trans_lt hmpow
  · by_cases heq : x = b
    · exact Or.inl heq
    · right
      exact (weakLapLimit_le_pow_of_weakItineraryCell hT L
        (lt_of_le_of_ne hxb heq) hcellRight).trans_lt hmpow

/-- The real cumulative coordinate underlying the interval-valued map. -/
def weakLapLimitRealCoordinate {T : IntervalMap} {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) (x : I) : ℝ :=
  if x = leftEndpoint then 0 else L.value leftEndpoint x

theorem weakLapLimitRealCoordinate_leftEndpoint
    {T : IntervalMap} {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) :
    weakLapLimitRealCoordinate L leftEndpoint = 0 := by
  simp [weakLapLimitRealCoordinate]

theorem weakLapLimitRealCoordinate_rightEndpoint
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    weakLapLimitRealCoordinate L rightEndpoint = 1 := by
  have hends : leftEndpoint < rightEndpoint := by
    norm_num [leftEndpoint, rightEndpoint]
  have hrightne : rightEndpoint ≠ leftEndpoint := hends.ne'
  simp [weakLapLimitRealCoordinate, hrightne,
    (weakLapLimit_bounds hT L hends).2]

theorem weakLapLimitRealCoordinate_bounds
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R)
    (x : I) :
    0 ≤ weakLapLimitRealCoordinate L x ∧
      weakLapLimitRealCoordinate L x ≤ 1 := by
  by_cases hxl : x = leftEndpoint
  · subst x
    simp [weakLapLimitRealCoordinate_leftEndpoint]
  · have hlx : leftEndpoint < x :=
      lt_of_le_of_ne x.property.1 (Ne.symm hxl)
    simpa [weakLapLimitRealCoordinate, hxl] using
      (weakLapLimit_bounds hT L hlx).1

theorem weakLapLimitRealCoordinate_interval
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R)
    {x y : I} (hxy : x ≤ y) :
    weakLapLimitRealCoordinate L y - weakLapLimitRealCoordinate L x =
      if x = y then 0 else L.value x y := by
  by_cases hxeq : x = y
  · subst y
    simp
  · have hxy' : x < y := lt_of_le_of_ne hxy hxeq
    by_cases hxl : x = leftEndpoint
    · subst x
      have hyl : y ≠ leftEndpoint := hxy'.ne'
      simp [weakLapLimitRealCoordinate, hyl, hxeq]
    · have hlx : leftEndpoint < x :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxl)
      have hyl : y ≠ leftEndpoint := (hlx.trans hxy').ne'
      have hadd := weakLapLimit_adjacent hT L hlx hxy'
      simp only [weakLapLimitRealCoordinate, if_neg hxl, if_neg hyl,
        if_neg hxeq]
      linarith

theorem weakLapLimitRealCoordinate_monotone
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    Monotone (weakLapLimitRealCoordinate L) := by
  intro x y hxy
  by_cases hxeq : x = y
  · subst y
    exact le_rfl
  · have hxy' : x < y := lt_of_le_of_ne hxy hxeq
    have hnonneg := (weakLapLimit_bounds hT L hxy').1.1
    have hinc := weakLapLimitRealCoordinate_interval hT L hxy
    rw [if_neg hxeq] at hinc
    linarith

theorem weakLapLimitRealCoordinate_continuous
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    Continuous (weakLapLimitRealCoordinate L) := by
  let c : I → ℝ := weakLapLimitRealCoordinate L
  have hcmono : Monotone c := by
    simpa [c] using weakLapLimitRealCoordinate_monotone hT L
  have hc_interval : ∀ {x y : I}, x ≤ y →
      c y - c x = if x = y then 0 else L.value x y := by
    intro x y hxy
    simpa [c] using weakLapLimitRealCoordinate_interval hT L hxy
  change Continuous c
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨a, b, hax, hxb, haleft, haright, hleftMass,
      hrightMass⟩ := weakLapLimit_twoSided_smallness hT L x hε
  have hleftSmall : c x - c a < ε := by
    by_cases haxeq : a = x
    · subst a
      simpa using hε
    · have hmass : L.value a x < ε :=
        hleftMass.resolve_left haxeq
      have hlength := hc_interval hax
      rw [if_neg haxeq] at hlength
      linarith
  have hrightSmall : c b - c x < ε := by
    by_cases hxbeq : x = b
    · subst b
      simpa using hε
    · have hmass : L.value x b < ε :=
        hrightMass.resolve_left hxbeq
      have hlength := hc_interval hxb
      rw [if_neg hxbeq] at hlength
      linarith
  have hnear : ∀ y : I, a ≤ y → y ≤ b →
      dist (c y) (c x) < ε := by
    intro y hay hyb
    rw [Real.dist_eq]
    rcases le_total y x with hyx | hxy
    · rw [abs_of_nonpos (sub_nonpos.mpr (hcmono hyx))]
      have hcay : c a ≤ c y := hcmono hay
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr (hcmono hxy))]
      have hyb' : c y ≤ c b := hcmono hyb
      linarith
  by_cases hxl : x = leftEndpoint
  · subst x
    have hlb : leftEndpoint < b := haright (by
      norm_num [leftEndpoint, rightEndpoint])
    let δ : ℝ := (b : ℝ) - (leftEndpoint : ℝ)
    have hδ : 0 < δ := sub_pos.mpr hlb
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    change dist (y : ℝ) (leftEndpoint : ℝ) < δ at hy
    have hy' : |(y : ℝ) - (leftEndpoint : ℝ)| < δ := by
      simpa [Real.dist_eq] using hy
    have hyb : y ≤ b := by
      have hupp := (abs_lt.mp hy').2
      change (y : ℝ) ≤ (b : ℝ)
      dsimp [δ] at hupp
      linarith
    exact hnear y (hax.trans y.property.1) hyb
  · by_cases hxr : x = rightEndpoint
    · subst x
      have hal : a < rightEndpoint := haleft (by
        norm_num [leftEndpoint, rightEndpoint])
      let δ : ℝ := (rightEndpoint : ℝ) - (a : ℝ)
      have hδ : 0 < δ := sub_pos.mpr hal
      refine ⟨δ, hδ, ?_⟩
      intro y hy
      change dist (y : ℝ) (rightEndpoint : ℝ) < δ at hy
      have hy' : |(y : ℝ) - (rightEndpoint : ℝ)| < δ := by
        simpa [Real.dist_eq] using hy
      have hay : a ≤ y := by
        have hlow := (abs_lt.mp hy').1
        change (a : ℝ) ≤ (y : ℝ)
        dsimp [δ] at hlow
        linarith
      exact hnear y hay (y.property.2.trans hxb)
    · have hlx : leftEndpoint < x :=
        lt_of_le_of_ne x.property.1 (Ne.symm hxl)
      have hxr' : x < rightEndpoint :=
        lt_of_le_of_ne x.property.2 hxr
      have hax' : a < x := haleft hlx
      have hxb' : x < b := haright hxr'
      let δ : ℝ := min ((x : ℝ) - (a : ℝ))
        ((b : ℝ) - (x : ℝ))
      have hδ : 0 < δ :=
        lt_min (sub_pos.mpr hax') (sub_pos.mpr hxb')
      refine ⟨δ, hδ, ?_⟩
      intro y hy
      change dist (y : ℝ) (x : ℝ) < δ at hy
      have hy' : |(y : ℝ) - (x : ℝ)| < δ := by
        simpa [Real.dist_eq] using hy
      have hay : a ≤ y := by
        have hlow := (abs_lt.mp hy').1
        have hδle : δ ≤ (x : ℝ) - (a : ℝ) := min_le_left _ _
        change (a : ℝ) ≤ (y : ℝ)
        linarith
      have hyb : y ≤ b := by
        have hupp := (abs_lt.mp hy').2
        have hδle : δ ≤ (b : ℝ) - (x : ℝ) := min_le_right _ _
        change (y : ℝ) ≤ (b : ℝ)
        linarith
      exact hnear y hay hyb

/-- The subtype-valued version of the cumulative real coordinate. -/
noncomputable def weakLapLimitCoordinate
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) : I → I :=
  fun x => ⟨weakLapLimitRealCoordinate L x,
    weakLapLimitRealCoordinate_bounds hT L x⟩

theorem weakLapLimitCoordinate_continuous
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    Continuous (weakLapLimitCoordinate hT L) := by
  apply Continuous.subtype_mk
  simpa [weakLapLimitCoordinate] using
    weakLapLimitRealCoordinate_continuous hT L

theorem weakLapLimitCoordinate_monotone
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    Monotone (weakLapLimitCoordinate hT L) := by
  intro x y hxy
  change weakLapLimitRealCoordinate L x ≤ weakLapLimitRealCoordinate L y
  exact weakLapLimitRealCoordinate_monotone hT L hxy

theorem weakLapLimitCoordinate_leftEndpoint
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    weakLapLimitCoordinate hT L leftEndpoint = leftEndpoint := by
  apply Subtype.ext
  simpa [weakLapLimitCoordinate] using
    weakLapLimitRealCoordinate_leftEndpoint L

theorem weakLapLimitCoordinate_rightEndpoint
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    weakLapLimitCoordinate hT L rightEndpoint = rightEndpoint := by
  apply Subtype.ext
  simpa [weakLapLimitCoordinate] using
    weakLapLimitRealCoordinate_rightEndpoint hT L

/-- Continuity and the two endpoint values make the interval coordinate
surjective. -/
theorem weakLapLimitCoordinate_surjective
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    Surjective (weakLapLimitCoordinate hT L) := by
  intro y
  have hyvals : y ∈ Set.Icc
      (weakLapLimitCoordinate hT L leftEndpoint)
      (weakLapLimitCoordinate hT L rightEndpoint) := by
    rw [weakLapLimitCoordinate_leftEndpoint,
      weakLapLimitCoordinate_rightEndpoint]
    exact y.property
  rcases intermediate_value_Icc
      (show leftEndpoint ≤ rightEndpoint by
        norm_num [leftEndpoint, rightEndpoint])
      (weakLapLimitCoordinate_continuous hT L).continuousOn hyvals with
    ⟨x, _hx, hxy⟩
  exact ⟨x, hxy⟩

/-- The endpoint-normalized coordinate built from the limiting interval
functional. -/
structure WeakLapResolventCoordinateData
    (T : IntervalMap) (R : WeakLapRadiusData T)
    (L : WeakLapLimitData T R) where
  coordinate : I → I
  continuous_coordinate : Continuous coordinate
  monotone_coordinate : Monotone coordinate
  surjective_coordinate : Surjective coordinate
  endpoint_zero : coordinate leftEndpoint = leftEndpoint
  endpoint_one : coordinate rightEndpoint = rightEndpoint
  interval_length : ∀ {x y : I}, x ≤ y →
    (coordinate y : ℝ) - (coordinate x : ℝ) =
      if x = y then 0 else L.value x y

/-- Additivity, normalization, and two-sided smallness of the limit produce
the continuous monotone coordinate. -/
theorem weakLapResolventCoordinateData_exists
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} (L : WeakLapLimitData T R) :
    Nonempty (WeakLapResolventCoordinateData T R L) := by
  exact ⟨{
    coordinate := weakLapLimitCoordinate hT L
    continuous_coordinate := weakLapLimitCoordinate_continuous hT L
    monotone_coordinate := weakLapLimitCoordinate_monotone hT L
    surjective_coordinate := weakLapLimitCoordinate_surjective hT L
    endpoint_zero := weakLapLimitCoordinate_leftEndpoint hT L
    endpoint_one := weakLapLimitCoordinate_rightEndpoint hT L
    interval_length := by
      intro x y hxy
      change weakLapLimitRealCoordinate L y -
        weakLapLimitRealCoordinate L x =
          if x = y then 0 else L.value x y
      exact weakLapLimitRealCoordinate_interval hT L hxy }⟩

/-- Exact one-branch transport for the limiting interval mass, including
the degenerate target interval produced by a plateau. -/
theorem weakLapLimit_scaling {T : IntervalMap}
    (hT : FinitePieceMonotone T) {R : WeakLapRadiusData T}
    (L : WeakLapLimitData T R) {x y : I} (hxy : x < y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    L.value x y = R.radius *
      L.value (min (T x) (T y)) (max (T x) (T y)) := by
  let u : I := min (T x) (T y)
  let v : I := max (T x) (T y)
  have huv : u ≤ v := min_le_max
  have hsubTop : Tendsto L.subsequence atTop atTop :=
    L.subsequence_strictMono.tendsto_atTop
  have hsampleSub : Tendsto
      (fun n : ℕ => R.sample (L.subsequence n))
      atTop (nhds R.radius) :=
    R.sample_tendsto.comp hsubTop
  have htarget : Tendsto
      (fun n => weakNormalizedLapResolvent R u v (L.subsequence n))
      atTop (nhds (L.value u v)) := by
    by_cases heq : u = v
    · rw [← heq]
      simpa [L.value_diag, weakNormalizedLapResolvent,
        weakLapResolvent, weakLapCountOn, weakLapCountOf] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
          atTop (nhds 0))
    · exact L.tendsto_value (lt_of_le_of_ne huv heq)
  have hrawLimit : Tendsto
      (fun n => weakNormalizedLapResolvent R x y (L.subsequence n) -
        R.sample (L.subsequence n) *
          weakNormalizedLapResolvent R u v (L.subsequence n))
      atTop (nhds (L.value x y - R.radius * L.value u v)) :=
    (L.tendsto_value hxy).sub (hsampleSub.mul htarget)
  have hrawZero : Tendsto
      (fun n => weakNormalizedLapResolvent R x y (L.subsequence n) -
        R.sample (L.subsequence n) *
          weakNormalizedLapResolvent R u v (L.subsequence n))
      atTop (nhds 0) := by
    simpa [u, v, Function.comp_apply] using
      (weakNormalizedLapResolvent_branch_tendsto_zero
        hT R hxy hmono).comp hsubTop
  have heq : L.value x y - R.radius * L.value u v = 0 :=
    tendsto_nhds_unique hrawLimit hrawZero
  simpa [u, v] using sub_eq_zero.mp heq

/-- Transport across one weakly monotone branch becomes exact scaling in the
limit. -/
theorem weakLapResolventCoordinate_branch_scaling
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    {R : WeakLapRadiusData T} {L : WeakLapLimitData T R}
    (D : WeakLapResolventCoordinateData T R L)
    {x y : I} (hxy : x ≤ y)
    (hmono : IsWeaklyMonotoneOn T (Set.Icc x y)) :
    |(D.coordinate (T y) : ℝ) - (D.coordinate (T x) : ℝ)| =
      R.radius⁻¹ *
        |(D.coordinate y : ℝ) - (D.coordinate x : ℝ)| := by
  by_cases heq : x = y
  · subst y
    simp
  · have hxy' : x < y := lt_of_le_of_ne hxy heq
    let u : I := min (T x) (T y)
    let v : I := max (T x) (T y)
    have huv : u ≤ v := min_le_max
    have hsourceLen :
        (D.coordinate y : ℝ) - D.coordinate x = L.value x y := by
      have hlen := D.interval_length hxy
      rw [if_neg heq] at hlen
      exact hlen
    have hsourceAbs :
        |(D.coordinate y : ℝ) - D.coordinate x| = L.value x y := by
      have hcoord : (D.coordinate x : ℝ) ≤ D.coordinate y :=
        D.monotone_coordinate hxy
      rw [abs_of_nonneg (sub_nonneg.mpr hcoord)]
      exact hsourceLen
    have himageLen :
        (D.coordinate v : ℝ) - D.coordinate u = L.value u v := by
      rw [D.interval_length huv]
      by_cases huvEq : u = v
      · rw [huvEq]
        simp [L.value_diag]
      · simp [huvEq]
    have himageAbs :
        |(D.coordinate (T y) : ℝ) - D.coordinate (T x)| =
          L.value u v := by
      rcases le_total (T x) (T y) with hTxy | hTyx
      · have hcoord : (D.coordinate (T x) : ℝ) ≤
            D.coordinate (T y) := D.monotone_coordinate hTxy
        rw [abs_of_nonneg (sub_nonneg.mpr hcoord)]
        simpa [u, v, min_eq_left hTxy, max_eq_right hTxy] using himageLen
      · have hcoord : (D.coordinate (T y) : ℝ) ≤
            D.coordinate (T x) := D.monotone_coordinate hTyx
        rw [abs_of_nonpos (sub_nonpos.mpr hcoord)]
        simpa [u, v, min_eq_right hTyx, max_eq_left hTyx] using himageLen
    have hscale : L.value x y = R.radius * L.value u v := by
      simpa [u, v] using weakLapLimit_scaling hT L hxy' hmono
    rw [himageAbs, hsourceAbs, hscale]
    field_simp [R.radius_pos.ne']

/-! ## The expanding compatible coordinate -/

structure ExpandingCompatibleCoordinate (T : IntervalMap) where
  scale : ℝ
  scale_gt_one : 1 < scale
  coordinate : I → I
  continuous_coordinate : Continuous coordinate
  monotone_coordinate : Monotone coordinate
  surjective_coordinate : Surjective coordinate
  endpoint_zero : coordinate leftEndpoint = leftEndpoint
  endpoint_one : coordinate rightEndpoint = rightEndpoint
  weak_branch_scaling : ∀ {x y : I}, x ≤ y →
    IsWeaklyMonotoneOn T (Set.Icc x y) →
      |(coordinate (T y) : ℝ) - coordinate (T x)| =
        scale * |(coordinate y : ℝ) - coordinate x|

namespace ExpandingCompatibleCoordinate

def realCoordinate {T : IntervalMap}
    (D : ExpandingCompatibleCoordinate T) : I → ℝ :=
  fun x => (D.coordinate x : ℝ)

theorem monotone_realCoordinate {T : IntervalMap}
    (D : ExpandingCompatibleCoordinate T) :
    Monotone D.realCoordinate :=
  D.monotone_coordinate

theorem continuous_realCoordinate {T : IntervalMap}
    (D : ExpandingCompatibleCoordinate T) :
    Continuous D.realCoordinate :=
  continuous_subtype_val.comp D.continuous_coordinate

/-- The compatible coordinate as an element of the normalized branch-length
space. -/
noncomputable def normalizedCoordinate {T : IntervalMap}
    (D : ExpandingCompatibleCoordinate T) :
    NormalizedContinuousCoordinate := by
  refine ⟨⟨D.realCoordinate, D.continuous_realCoordinate⟩, ?_⟩
  change D.realCoordinate leftEndpoint = 0
  rw [realCoordinate, D.endpoint_zero]
  rfl

@[simp] theorem normalizedCoordinate_apply {T : IntervalMap}
    (D : ExpandingCompatibleCoordinate T) (x : I) :
    D.normalizedCoordinate x = (D.coordinate x : ℝ) := rfl

theorem normalizedCoordinate_monotone {T : IntervalMap}
    (D : ExpandingCompatibleCoordinate T) :
    Monotone (fun x : I => D.normalizedCoordinate x) := by
  intro x y hxy
  exact D.monotone_coordinate hxy

theorem normalizedCoordinate_rightEndpoint {T : IntervalMap}
    (D : ExpandingCompatibleCoordinate T) :
    D.normalizedCoordinate rightEndpoint = 1 := by
  change (D.coordinate rightEndpoint : ℝ) = 1
  rw [D.endpoint_one]
  rfl

end ExpandingCompatibleCoordinate

/-- A product horseshoe yields an expanding compatible coordinate. -/
theorem expandingCompatibleCoordinate_of_horseshoe
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (H : TwoBranchHorseshoe T) :
    Nonempty (ExpandingCompatibleCoordinate T) := by
  obtain ⟨G⟩ := weakLapGrowthData_exists hT H
  obtain ⟨R⟩ := weakLapRadiusData_exists G
  obtain ⟨C⟩ := weakLapCumulativeLimitData_exists hT R
  obtain ⟨L⟩ := weakLapLimitData_exists hT C
  obtain ⟨D⟩ := weakLapResolventCoordinateData_exists hT L
  have hrlt : R.radius < 1 :=
    R.radius_le_half.trans_lt (by norm_num)
  exact ⟨{
    scale := R.radius⁻¹
    scale_gt_one := (one_lt_inv₀ R.radius_pos).2 hrlt
    coordinate := D.coordinate
    continuous_coordinate := D.continuous_coordinate
    monotone_coordinate := D.monotone_coordinate
    surjective_coordinate := D.surjective_coordinate
    endpoint_zero := D.endpoint_zero
    endpoint_one := D.endpoint_one
    weak_branch_scaling := by
      intro x y hxy hmono
      exact weakLapResolventCoordinate_branch_scaling hT D hxy hmono }⟩

/-! ## Direct identification with branch length -/

/-- The source-coordinate contribution of one truncated partition lap. -/
noncomputable def sourceBranchContribution
    (p : RealPartition) (S : NormalizedContinuousCoordinate)
    (q : p.LapIndex) (x : I) : ℝ :=
  if (x : ℝ) ≤ q.left then 0
  else coordinateLength (fun z : I => S z)
    q.leftPoint (q.clippedPoint x)

/-- Any real partition is a monotonicity partition for the identity map. -/
def identityMonotonicityPartition (p : RealPartition) :
    MonotonicityPartition (fun x : I => x) where
  partition := p
  weaklyMonotoneOn_cell := by
    intro a b _hab
    left
    intro x _hx y _hy hxy
    exact hxy

/-- A source contribution is literally the branch contribution for the
identity map equipped with the same partition. -/
theorem sourceBranchContribution_eq_identityBranchContribution
    (p : RealPartition) (S : NormalizedContinuousCoordinate)
    (q : p.LapIndex) (x : I) :
    sourceBranchContribution p S q x =
      branchContribution (identityMonotonicityPartition p) S q x := by
  rfl

/-- Across one partition cell, the total truncated source contribution has
the same increment as the coordinate itself. -/
theorem sum_sourceBranchContribution_increment
    (p : RealPartition) (S : NormalizedContinuousCoordinate)
    (hS : Monotone (fun x : I => S x))
    {a b : ℝ} (hab : p.Adjacent a b) {x y : I}
    (hx : x ∈ intervalCell a b) (hy : y ∈ intervalCell a b)
    (hxy : x ≤ y) :
    (∑ q : p.LapIndex, sourceBranchContribution p S q y) -
        (∑ q : p.LapIndex, sourceBranchContribution p S q x) =
      S y - S x := by
  let Q : MonotonicityPartition (fun x : I => x) :=
    identityMonotonicityPartition p
  have hsum : ∀ z : I,
      (∑ q : p.LapIndex, sourceBranchContribution p S q z) =
        branchLengthOnPartition Q S z := by
    intro z
    unfold branchLengthOnPartition
    apply Finset.sum_congr rfl
    intro q _hq
    exact sourceBranchContribution_eq_identityBranchContribution p S q z
  rw [hsum y, hsum x]
  calc
    branchLengthOnPartition Q S y - branchLengthOnPartition Q S x =
        coordinateLength (fun z : I => S z) x y := by
      simpa [Q, identityMonotonicityPartition] using
        branchLengthOnPartition_increment Q S hab hx hy hxy
    _ = S y - S x := by
      rw [coordinateLength_eq_abs_sub_of_monotone _ hS,
        abs_of_nonneg (sub_nonneg.mpr (hS hxy))]

/-- Truncated source-coordinate increments telescope across an ordered real
partition. -/
theorem sum_sourceBranchContribution_eq
    (p : RealPartition) (S : NormalizedContinuousCoordinate)
    (hS : Monotone (fun x : I => S x)) (x : I) :
    ∑ q : p.LapIndex, sourceBranchContribution p S q x = S x := by
  let f : I → ℝ := fun z =>
    ∑ q : p.LapIndex, sourceBranchContribution p S q z
  have hfleft : f leftEndpoint = S leftEndpoint := by
    rw [NormalizedContinuousCoordinate.leftEndpoint_eq_zero S]
    dsimp [f]
    apply Finset.sum_eq_zero
    intro q _hq
    have hnonneg : (0 : ℝ) ≤ q.left :=
      (p.points_subset q.adjacent.1).1
    simp [sourceBranchContribution, hnonneg]
  have hfun : f = fun z : I => S z := by
    apply funext_of_partition_increments p f (fun z : I => S z) hfleft
    intro a b hab x y hx hy hxy
    exact sum_sourceBranchContribution_increment p S hS hab hx hy hxy
  exact congrFun hfun x

/-- If `x` is past a lap's left endpoint, that endpoint precedes the
clipped point. -/
theorem lapIndex_leftPoint_le_clippedPoint_of_not_le
    (p : RealPartition) (q : p.LapIndex) (x : I)
    (hx : ¬(x : ℝ) ≤ q.left) :
    q.leftPoint ≤ q.clippedPoint x := by
  change q.left ≤ min (x : ℝ) q.right
  exact le_min (lt_of_not_ge hx).le q.adjacent.2.2.1.le

/-- The interval from a lap's left endpoint to its clipped point stays in
that lap, so the assigned weak monotonicity applies there. -/
theorem weaklyMonotoneOn_Icc_leftPoint_clippedPoint
    {T : IntervalMap} (P : MonotonicityPartition T)
    (q : P.partition.LapIndex) (x : I) :
    IsWeaklyMonotoneOn T (Set.Icc q.leftPoint (q.clippedPoint x)) := by
  apply (P.weaklyMonotoneOn_cell q.adjacent).mono
  intro z hz
  change q.left ≤ (z : ℝ) ∧ (z : ℝ) ≤ q.right
  constructor
  · exact hz.1
  · calc
      (z : ℝ) ≤ (q.clippedPoint x : ℝ) := hz.2
      _ = min (x : ℝ) q.right := rfl
      _ ≤ q.right := min_le_right _ _

/-- On each lap, compatible branch scaling turns the target contribution
into `scale` times the corresponding source-coordinate contribution. -/
theorem branchContribution_eq_scale_sourceContribution
    {T : IntervalMap} (P : MonotonicityPartition T)
    (D : ExpandingCompatibleCoordinate T)
    (q : P.partition.LapIndex) (x : I) :
    branchContribution P D.normalizedCoordinate q x =
      D.scale * sourceBranchContribution P.partition
        D.normalizedCoordinate q x := by
  by_cases hx : (x : ℝ) ≤ q.left
  · simp [branchContribution, sourceBranchContribution, hx]
  · simp only [branchContribution, sourceBranchContribution, if_neg hx]
    rw [coordinateLength_eq_abs_sub_of_monotone _
        D.normalizedCoordinate_monotone,
      coordinateLength_eq_abs_sub_of_monotone _
        D.normalizedCoordinate_monotone]
    simpa only [ExpandingCompatibleCoordinate.normalizedCoordinate_apply] using
      D.weak_branch_scaling
        (lapIndex_leftPoint_le_clippedPoint_of_not_le P.partition q x hx)
        (weaklyMonotoneOn_Icc_leftPoint_clippedPoint P q x)

/-- The compatible-coordinate scaling law is exactly the eigen-equation for
the canonical branch-length operator. -/
theorem branchLength_eigen_of_expandingCompatibleCoordinate
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (D : ExpandingCompatibleCoordinate T) :
    branchLengthOperator hT D.normalizedCoordinate =
      D.scale • D.normalizedCoordinate := by
  let P := chosenMonotonicityPartition hT
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change branchLength hT D.normalizedCoordinate x =
    D.scale * D.normalizedCoordinate x
  rw [branchLength_eq_onPartition hT P D.normalizedCoordinate]
  change (∑ q : P.partition.LapIndex,
    branchContribution P D.normalizedCoordinate q x) = _
  calc
    (∑ q : P.partition.LapIndex,
        branchContribution P D.normalizedCoordinate q x) =
        ∑ q : P.partition.LapIndex,
          D.scale * sourceBranchContribution P.partition
            D.normalizedCoordinate q x := by
      apply Finset.sum_congr rfl
      intro q _hq
      exact branchContribution_eq_scale_sourceContribution P D q x
    _ = D.scale * ∑ q : P.partition.LapIndex,
        sourceBranchContribution P.partition D.normalizedCoordinate q x := by
      rw [Finset.mul_sum]
    _ = D.scale * D.normalizedCoordinate x := by
      rw [sum_sourceBranchContribution_eq P.partition D.normalizedCoordinate
        D.normalizedCoordinate_monotone x]

/-- The generic product-eigen data consumed by the reduction's R2 wrapper. -/
structure ProductBranchEigenData
    {T : IntervalMap} (hT : FinitePieceMonotone T) where
  rho : ℝ
  one_lt_rho : 1 < rho
  coordinate : NormalizedContinuousCoordinate
  coordinate_monotone : Monotone (fun x : I => coordinate x)
  coordinate_rightEndpoint : coordinate rightEndpoint = 1
  product_eigen : branchLengthOperator hT coordinate = rho • coordinate

/-- Horseshoe plus weak-lap resolvent assemble the initial expanding product
eigen-coordinate, without a measure-theoretic detour. -/
theorem productBranchEigenData_exists_of_horseshoe
    {T : IntervalMap} (hT : FinitePieceMonotone T)
    (H : TwoBranchHorseshoe T) :
    Nonempty (ProductBranchEigenData hT) := by
  obtain ⟨D⟩ := expandingCompatibleCoordinate_of_horseshoe hT H
  exact ⟨{
    rho := D.scale
    one_lt_rho := D.scale_gt_one
    coordinate := D.normalizedCoordinate
    coordinate_monotone := D.normalizedCoordinate_monotone
    coordinate_rightEndpoint := D.normalizedCoordinate_rightEndpoint
    product_eigen := branchLength_eigen_of_expandingCompatibleCoordinate hT D }⟩

end CommutingIntervalSimplified
