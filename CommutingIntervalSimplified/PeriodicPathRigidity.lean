import CommutingIntervalSimplified.PolygonalBase
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Rigidity of expanding periodic polygonal paths

Local affine coincidences of periodic paths satisfying the same expanding
dilation equation globalize.  The locally unit-speed and onto hypotheses then
supply a local coincidence automatically.  The same mechanism globalizes the
reflection visible at a fold maximum.
-/

namespace CommutingIntervalSimplified

open Function Set Filter Topology

noncomputable section

theorem full_period_group_of_least_period
    {ψ : ℝ → I} {P : ℝ} (hψ : IsUnitSpeedPeriodicSurjection ψ P) :
    ∀ r : ℝ, (∀ t : ℝ, ψ (t + r) = ψ t) ↔
      ∃ k : ℤ, r = (k : ℝ) * P := by
  let IsPeriod : ℝ → Prop := fun r => ∀ t : ℝ, ψ (t + r) = ψ t
  have hPpos : 0 < P := hψ.2.2.1
  have hPperiod : IsPeriod P := hψ.2.2.2.1
  have hleast : ∀ r : ℝ, 0 < r → IsPeriod r → P ≤ r :=
    hψ.2.2.2.2.1
  have hadd {a b : ℝ} (ha : IsPeriod a) (hb : IsPeriod b) :
      IsPeriod (a + b) := by
    intro t
    calc
      ψ (t + (a + b)) = ψ ((t + a) + b) := by ring_nf
      _ = ψ (t + a) := hb (t + a)
      _ = ψ t := ha t
  have hneg {a : ℝ} (ha : IsPeriod a) : IsPeriod (-a) := by
    intro t
    have h := ha (t - a)
    convert h.symm using 1 <;> ring
  have hnat : ∀ n : ℕ, IsPeriod ((n : ℝ) * P) := by
    intro n
    induction n with
    | zero => simp [IsPeriod]
    | succ n ih =>
        convert hadd ih hPperiod using 1
        push_cast
        ring
  have hint : ∀ k : ℤ, IsPeriod ((k : ℝ) * P) := by
    intro k
    cases k with
    | ofNat n => exact hnat n
    | negSucc n =>
        convert hneg (hnat (n + 1)) using 1
        push_cast
        ring
  intro r
  constructor
  · intro hr
    let k : ℤ := ⌊r / P⌋
    let s : ℝ := r - (k : ℝ) * P
    have hklo : (k : ℝ) ≤ r / P := by
      exact Int.floor_le (r / P)
    have hkhi : r / P < (k : ℝ) + 1 := by
      exact Int.lt_floor_add_one (r / P)
    have hmullo : (k : ℝ) * P ≤ r :=
      (le_div_iff₀ hPpos).mp (by simpa [mul_comm] using hklo)
    have hmulhi : r < ((k : ℝ) + 1) * P :=
      (div_lt_iff₀ hPpos).mp hkhi
    have hsnonneg : 0 ≤ s := by dsimp [s]; linarith
    have hslt : s < P := by dsimp [s]; linarith
    have hsperiod : IsPeriod s := by
      have := hadd hr (hneg (hint k))
      simpa [s, sub_eq_add_neg] using this
    have hszero : s = 0 := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hspos
        exact (not_le_of_gt hslt) (hleast s hspos hsperiod)
      · exact hsnonneg
    refine ⟨k, ?_⟩
    dsimp [s] at hszero
    linarith
  · rintro ⟨k, rfl⟩
    exact hint k

/-- Every parameter has a nontrivial right neighbourhood on which the path
has a single affine unit-speed formula. -/
theorem unitSpeedPeriodicSurjection_exists_right_affine
    {ψ : ℝ → I} {P : ℝ}
    (hψ : IsUnitSpeedPeriodicSurjection ψ P) (t : ℝ) :
    ∃ r m c : ℝ, t < r ∧ |m| = 1 ∧
      ∀ x ∈ Set.Icc t r, (ψ x : ℝ) = m * x + c := by
  obtain ⟨K, htK, ht1K, _hKmem, hpieces⟩ :=
    hψ.2.2.2.2.2 t (t + 1) (by linarith)
  let upper := K.filter fun z ↦ t < z
  have hupper : upper.Nonempty := by
    refine ⟨t + 1, Finset.mem_filter.mpr ⟨ht1K, by linarith⟩⟩
  obtain ⟨r, hr, hrmin⟩ := upper.exists_min_image id hupper
  have hr' := Finset.mem_filter.mp hr
  have hadj : AdjacentInFinset K t r := by
    refine ⟨htK, hr'.1, hr'.2, ?_⟩
    intro z hz htzr
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, htzr.1⟩
    have hrz : r ≤ z := by simpa using hrmin z hzupper
    exact (not_lt_of_ge hrz) htzr.2
  obtain ⟨m, c, hm, haff⟩ := hpieces hadj
  exact ⟨r, m, c, hr'.2, hm, haff⟩

private theorem unitSpeedPeriodicSurjection_exists_left_affine
    {ψ : ℝ → I} {P : ℝ}
    (hψ : IsUnitSpeedPeriodicSurjection ψ P) (t : ℝ) :
    ∃ l m c : ℝ, l < t ∧ |m| = 1 ∧
      ∀ x ∈ Set.Icc l t, (ψ x : ℝ) = m * x + c := by
  obtain ⟨K, htm1K, htK, _hKmem, hpieces⟩ :=
    hψ.2.2.2.2.2 (t - 1) t (by linarith)
  let lower := K.filter fun z ↦ z < t
  have hlower : lower.Nonempty := by
    refine ⟨t - 1, Finset.mem_filter.mpr ⟨htm1K, by linarith⟩⟩
  obtain ⟨l, hl, hlmax⟩ := lower.exists_max_image id hlower
  have hl' := Finset.mem_filter.mp hl
  have hadj : AdjacentInFinset K l t := by
    refine ⟨hl'.1, htK, hl'.2, ?_⟩
    intro z hz hlzt
    have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hlzt.2⟩
    have hzl : z ≤ l := by simpa using hlmax z hzlower
    exact (not_lt_of_ge hzl) hlzt.1
  obtain ⟨m, c, hm, haff⟩ := hpieces hadj
  exact ⟨l, m, c, hl'.2, hm, haff⟩

/-- Immediately to the right of a parameter attaining the interval maximum,
the unit-speed path descends with slope `-1`. -/
theorem unitSpeedPeriodicSurjection_right_descent_from_max
    {ψ : ℝ → I} {P t : ℝ}
    (hψ : IsUnitSpeedPeriodicSurjection ψ P)
    (hmax : ψ t = rightEndpoint) :
    ∃ r : ℝ, t < r ∧ ∀ x ∈ Set.Icc t r,
      (ψ x : ℝ) = 1 - (x - t) := by
  obtain ⟨r, m, c, htr, hm, haff⟩ :=
    unitSpeedPeriodicSurjection_exists_right_affine hψ t
  have htform := haff t ⟨le_rfl, htr.le⟩
  have hrform := haff r ⟨htr.le, le_rfl⟩
  have htval : (ψ t : ℝ) = 1 := by
    rw [hmax]
    rfl
  have hrbound : (ψ r : ℝ) ≤ 1 := (ψ r).property.2
  have hmneg : m = -1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hm with hmone | hmneg
    · rw [hmone] at htform hrform
      linarith
    · simpa using hmneg
  refine ⟨r, htr, ?_⟩
  intro x hx
  have hxform := haff x hx
  rw [hmneg] at htform hxform
  linarith

private theorem unitSpeedPeriodicSurjection_left_ascent_to_max
    {ψ : ℝ → I} {P t : ℝ}
    (hψ : IsUnitSpeedPeriodicSurjection ψ P)
    (hmax : ψ t = rightEndpoint) :
    ∃ l : ℝ, l < t ∧ ∀ x ∈ Set.Icc l t,
      (ψ x : ℝ) = 1 - (t - x) := by
  obtain ⟨l, m, c, hlt, hm, haff⟩ :=
    unitSpeedPeriodicSurjection_exists_left_affine hψ t
  have hlform := haff l ⟨le_rfl, hlt.le⟩
  have htform := haff t ⟨hlt.le, le_rfl⟩
  have htval : (ψ t : ℝ) = 1 := by
    rw [hmax]
    rfl
  have hlbound : (ψ l : ℝ) ≤ 1 := (ψ l).property.2
  have hmone : m = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hm with hmone | hmneg
    · exact hmone
    · rw [hmneg] at hlform htform
      linarith
  refine ⟨l, hlt, ?_⟩
  intro x hx
  have hxform := haff x hx
  rw [hmone] at htform hxform
  linarith

/-- Cross-period globalization for two unit-speed polygonal path models of
the same expanding interval dynamics. -/
theorem unitSpeedPeriodicSurjections_have_local_match
    {u v : ℝ → I} {Pu Pv : ℝ}
    (hu : IsUnitSpeedPeriodicSurjection u Pu)
    (hv : IsUnitSpeedPeriodicSurjection v Pv) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∃ l r δ : ℝ, l < r ∧
        ∀ t ∈ Set.Icc l r, v t = u ((ε : ℝ) * t + δ) := by
  obtain ⟨tu, htu⟩ := hu.2.1 rightEndpoint
  obtain ⟨tv, htv⟩ := hv.2.1 rightEndpoint
  obtain ⟨ru, htuRu, huFormula⟩ :=
    unitSpeedPeriodicSurjection_right_descent_from_max hu htu
  obtain ⟨rv, htvRv, hvFormula⟩ :=
    unitSpeedPeriodicSurjection_right_descent_from_max hv htv
  let d : ℝ := min (ru - tu) (rv - tv)
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min (sub_pos.mpr htuRu) (sub_pos.mpr htvRv)
  refine ⟨1, Or.inl rfl, tv, tv + d, tu - tv, by linarith, ?_⟩
  intro t ht
  have htV : t ∈ Set.Icc tv rv := by
    constructor
    · exact ht.1
    · have hdle : d ≤ rv - tv := min_le_right _ _
      calc
        t ≤ tv + d := ht.2
        _ ≤ tv + (rv - tv) := by
          simpa [add_comm] using add_le_add_left hdle tv
        _ = rv := by ring
  have htU : t + (tu - tv) ∈ Set.Icc tu ru := by
    constructor
    · linarith [ht.1]
    · have hdle : d ≤ ru - tu := min_le_left _ _
      calc
        t + (tu - tv) ≤ (tv + d) + (tu - tv) := by
          simpa [add_comm] using add_le_add_right ht.2 (tu - tv)
        _ = tu + d := by ring
        _ ≤ tu + (ru - tu) := by
          simpa [add_comm] using add_le_add_left hdle tu
        _ = ru := by ring
  norm_num
  apply Subtype.ext
  have hvf := hvFormula t htV
  have huf := huFormula (t + (tu - tv)) htU
  calc
    (v t : ℝ) = 1 - (t - tv) := hvf
    _ = 1 - ((t + (tu - tv)) - tu) := by ring
    _ = (u (t + (tu - tv)) : ℝ) := huf.symm

theorem cross_period_globalization
    {u v : ℝ → I} {Pu Pv r : ℝ} {T : IntervalMap}
    (hu : IsUnitSpeedPeriodicSurjection u Pu)
    (hv : IsUnitSpeedPeriodicSurjection v Pv)
    (hr : 1 < r)
    (huT : DilationSemiconjugates u r T)
    (hvT : DilationSemiconjugates v r T) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∃ δ : ℝ, (∀ t : ℝ, v t = u ((ε : ℝ) * t + δ)) ∧ Pu = Pv := by
  obtain ⟨ε, hε, l, s, δ₀, hls, hlocal⟩ :=
    unitSpeedPeriodicSurjections_have_local_match hu hv
  have hεsq : (ε : ℝ) * (ε : ℝ) = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have hPupos : 0 < Pu := hu.2.2.1
  have hPvpos : 0 < Pv := hv.2.2.1
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hwidth : 0 < s - l := sub_pos.mpr hls
  have hiteru : ∀ n : ℕ, ∀ t : ℝ,
      u (r ^ n * t) = iterateMap T n (u t) := by
    intro n
    induction n with
    | zero => intro t; simp [iterateMap]
    | succ n ih =>
        intro t
        calc
          u (r ^ (n + 1) * t) = u (r * (r ^ n * t)) := by
            congr 1
            rw [pow_succ]
            ring
          _ = T (u (r ^ n * t)) := huT (r ^ n * t)
          _ = T (iterateMap T n (u t)) := congrArg T (ih t)
          _ = iterateMap T (n + 1) (u t) := by
            simp [iterateMap, Function.iterate_succ_apply']
  have hiterv : ∀ n : ℕ, ∀ t : ℝ,
      v (r ^ n * t) = iterateMap T n (v t) := by
    intro n
    induction n with
    | zero => intro t; simp [iterateMap]
    | succ n ih =>
        intro t
        calc
          v (r ^ (n + 1) * t) = v (r * (r ^ n * t)) := by
            congr 1
            rw [pow_succ]
            ring
          _ = T (v (r ^ n * t)) := hvT (r ^ n * t)
          _ = T (iterateMap T n (v t)) := congrArg T (ih t)
          _ = iterateMap T (n + 1) (v t) := by
            simp [iterateMap, Function.iterate_succ_apply']
  have hscaled : ∀ n : ℕ, ∀ t ∈ Set.Icc (r ^ n * l) (r ^ n * s),
      v t = u ((ε : ℝ) * t + r ^ n * δ₀) := by
    intro n t ht
    have hpowpos : 0 < r ^ n := pow_pos hrpos n
    let z : ℝ := t / r ^ n
    have hz : z ∈ Set.Icc l s := by
      constructor
      · dsimp [z]
        exact (le_div_iff₀ hpowpos).2 (by simpa [mul_comm] using ht.1)
      · dsimp [z]
        exact (div_le_iff₀ hpowpos).2 (by simpa [mul_comm] using ht.2)
    have h := congrArg (iterateMap T n) (hlocal z hz)
    rw [← hiterv n z, ← hiteru n ((ε : ℝ) * z + δ₀)] at h
    convert h using 1 <;> dsimp [z] <;> field_simp <;> ring
  let midpoint : ℕ → ℝ := fun n => r ^ n * ((l + s) / 2)
  let θ : ℕ → ℝ := fun n => toIcoMod hPvpos 0 (midpoint n)
  let η : ℕ → ℝ := fun n =>
    toIcoMod hPupos 0 ((ε : ℝ) * midpoint n + r ^ n * δ₀)
  let phases : ℕ → ℝ × ℝ := fun n => (θ n, η n)
  have hphases : ∀ n,
      phases n ∈ Set.Icc (0 : ℝ) Pv ×ˢ Set.Icc (0 : ℝ) Pu := by
    intro n
    change θ n ∈ Set.Icc (0 : ℝ) Pv ∧ η n ∈ Set.Icc (0 : ℝ) Pu
    constructor
    · dsimp [θ]
      exact ⟨(toIcoMod_mem_Ico hPvpos 0 (midpoint n)).1,
        by simpa using (toIcoMod_mem_Ico hPvpos 0 (midpoint n)).2.le⟩
    · dsimp [η]
      exact ⟨(toIcoMod_mem_Ico hPupos 0
          ((ε : ℝ) * midpoint n + r ^ n * δ₀)).1,
        by simpa using (toIcoMod_mem_Ico hPupos 0
          ((ε : ℝ) * midpoint n + r ^ n * δ₀)).2.le⟩
  obtain ⟨phaseLimit, _hphaseLimit, φ, hφ, hphaseConv⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hphases
  have hθconv : Tendsto (fun n => θ (φ n)) atTop (𝓝 phaseLimit.1) := by
    simpa [phases, Function.comp_def] using
      continuous_fst.continuousAt.tendsto.comp hphaseConv
  have hηconv : Tendsto (fun n => η (φ n)) atTop (𝓝 phaseLimit.2) := by
    simpa [phases, Function.comp_def] using
      continuous_snd.continuousAt.tendsto.comp hphaseConv
  have hpowSubseq : Tendsto (fun n => r ^ φ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).comp hφ.tendsto_atTop
  have hglobalShift : ∀ h : ℝ,
      v (phaseLimit.1 + h) =
        u (phaseLimit.2 + (ε : ℝ) * h) := by
    intro h
    have hlarge : ∀ᶠ n : ℕ in atTop,
        2 * |h| / (s - l) < r ^ φ n :=
      hpowSubseq.eventually_gt_atTop (2 * |h| / (s - l))
    have hinside : ∀ᶠ n : ℕ in atTop,
        midpoint (φ n) + h ∈
          Set.Icc (r ^ φ n * l) (r ^ φ n * s) := by
      filter_upwards [hlarge] with n hn
      have hgrowth : 2 * |h| < r ^ φ n * (s - l) := by
        have := (div_lt_iff₀ hwidth).1 hn
        simpa [mul_comm] using this
      have hpowpos : 0 < r ^ φ n := pow_pos hrpos _
      constructor <;> dsimp [midpoint] <;> nlinarith [neg_abs_le h, le_abs_self h]
    have hperiodV (k : ℤ) : ∀ x : ℝ,
        v (x + (k : ℝ) * Pv) = v x :=
      (full_period_group_of_least_period hv ((k : ℝ) * Pv)).2 ⟨k, rfl⟩
    have hperiodU (k : ℤ) : ∀ x : ℝ,
        u (x + (k : ℝ) * Pu) = u x :=
      (full_period_group_of_least_period hu ((k : ℝ) * Pu)).2 ⟨k, rfl⟩
    have heq : ∀ᶠ n : ℕ in atTop,
        v (θ (φ n) + h) = u (η (φ n) + (ε : ℝ) * h) := by
      filter_upwards [hinside] with n hn
      let zv : ℤ := toIcoDiv hPvpos 0 (midpoint (φ n))
      let zu : ℤ := toIcoDiv hPupos 0
        ((ε : ℝ) * midpoint (φ n) + r ^ φ n * δ₀)
      have hθ : θ (φ n) = midpoint (φ n) - (zv : ℝ) * Pv := by
        dsimp [θ, zv]
        simpa [smul_eq_mul] using
          self_sub_toIcoDiv_zsmul hPvpos 0 (midpoint (φ n))
      have hη : η (φ n) =
          (ε : ℝ) * midpoint (φ n) + r ^ φ n * δ₀ - (zu : ℝ) * Pu := by
        dsimp [η, zu]
        simpa [smul_eq_mul] using
          self_sub_toIcoDiv_zsmul hPupos 0
            ((ε : ℝ) * midpoint (φ n) + r ^ φ n * δ₀)
      calc
        v (θ (φ n) + h) = v (midpoint (φ n) + h) := by
          rw [hθ]
          symm
          convert hperiodV zv (θ (φ n) + h) using 1 <;> rw [hθ] <;> ring
        _ = u ((ε : ℝ) * (midpoint (φ n) + h) + r ^ φ n * δ₀) :=
          hscaled (φ n) (midpoint (φ n) + h) hn
        _ = u (η (φ n) + (ε : ℝ) * h) := by
          convert hperiodU zu (η (φ n) + (ε : ℝ) * h) using 1 <;> rw [hη] <;> ring
    have hvlim : Tendsto (fun n => v (θ (φ n) + h)) atTop
        (𝓝 (v (phaseLimit.1 + h))) :=
      hv.1.continuousAt.tendsto.comp (hθconv.add tendsto_const_nhds)
    have hulim : Tendsto (fun n => u (η (φ n) + (ε : ℝ) * h)) atTop
        (𝓝 (u (phaseLimit.2 + (ε : ℝ) * h))) :=
      hu.1.continuousAt.tendsto.comp (hηconv.add tendsto_const_nhds)
    have heq' : (fun n => u (η (φ n) + (ε : ℝ) * h)) =ᶠ[atTop]
        (fun n => v (θ (φ n) + h)) := by
      filter_upwards [heq] with n hn
      exact hn.symm
    exact tendsto_nhds_unique hvlim (hulim.congr' heq')
  let δ : ℝ := phaseLimit.2 - (ε : ℝ) * phaseLimit.1
  have hglobal : ∀ t : ℝ, v t = u ((ε : ℝ) * t + δ) := by
    intro t
    have := hglobalShift (t - phaseLimit.1)
    calc
      v t = v (phaseLimit.1 + (t - phaseLimit.1)) := by congr 1 <;> ring
      _ = u (phaseLimit.2 + (ε : ℝ) * (t - phaseLimit.1)) := this
      _ = u ((ε : ℝ) * t + δ) := by congr 1 <;> dsimp [δ] <;> ring
  have hPuPeriodOfV : ∀ t : ℝ, v (t + Pu) = v t := by
    intro t
    rw [hglobal, hglobal]
    rcases hε with rfl | rfl
    · convert (full_period_group_of_least_period hu Pu).2 ⟨1, by norm_num⟩
        ((1 : ℝ) * t + δ) using 1 <;> ring
    · convert (full_period_group_of_least_period hu (-Pu)).2 ⟨-1, by norm_num⟩
        ((-1 : ℝ) * t + δ) using 1 <;> ring
  have hPvPeriodOfU : ∀ t : ℝ, u (t + Pv) = u t := by
    intro t
    let x : ℝ := (ε : ℝ) * (t - δ)
    have hx : (ε : ℝ) * x + δ = t := by
      dsimp [x]
      calc
        (ε : ℝ) * ((ε : ℝ) * (t - δ)) + δ =
            ((ε : ℝ) * (ε : ℝ)) * (t - δ) + δ := by ring
        _ = t := by rw [hεsq]; ring
    have hx' : (ε : ℝ) * (x + (ε : ℝ) * Pv) + δ = t + Pv := by
      dsimp [x]
      calc
        (ε : ℝ) * ((ε : ℝ) * (t - δ) + (ε : ℝ) * Pv) + δ =
            ((ε : ℝ) * (ε : ℝ)) * (t - δ + Pv) + δ := by ring
        _ = t + Pv := by rw [hεsq]; ring
    calc
      u (t + Pv) = v (x + (ε : ℝ) * Pv) := by rw [hglobal, hx']
      _ = v x := by
        rcases hε with rfl | rfl
        · simpa using
            ((full_period_group_of_least_period hv Pv).2 ⟨1, by norm_num⟩ x)
        · simpa using
            ((full_period_group_of_least_period hv (-Pv)).2 ⟨-1, by norm_num⟩ x)
      _ = u t := by rw [hglobal, hx]
  have hPu_le : Pu ≤ Pv := hu.2.2.2.2.1 Pv hPvpos hPvPeriodOfU
  have hPv_le : Pv ≤ Pu := hv.2.2.2.2.1 Pu hPupos hPuPeriodOfV
  exact ⟨ε, hε, δ, hglobal, le_antisymm hPu_le hPv_le⟩

/--
The local polygonal input used in the reflection argument.  A regular value
of an onto unit-speed polygonal loop has both an increasing and a decreasing
crossing, and matching those two affine germs produces a local reflection.

This is kept separate from the expansion argument below: it is exactly the
finite-vertex bookkeeping assertion, whereas globalization and uniqueness
use only periodicity and the expanding dilation.
-/
theorem unitSpeedPeriodicSurjection_has_local_reflection
    {ψ : ℝ → I} {P : ℝ} (hψ : IsUnitSpeedPeriodicSurjection ψ P) :
    ∃ l r γ : ℝ, l < r ∧
      ∀ t ∈ Set.Icc l r, ψ (-t + γ) = ψ t := by
  obtain ⟨t₀, ht₀⟩ := hψ.2.1 rightEndpoint
  obtain ⟨l₀, hl₀t, hleft⟩ :=
    unitSpeedPeriodicSurjection_left_ascent_to_max hψ ht₀
  obtain ⟨r₀, htR₀, hright⟩ :=
    unitSpeedPeriodicSurjection_right_descent_from_max hψ ht₀
  let d : ℝ := min (t₀ - l₀) (r₀ - t₀)
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min (sub_pos.mpr hl₀t) (sub_pos.mpr htR₀)
  refine ⟨t₀, t₀ + d, 2 * t₀, by linarith, ?_⟩
  intro t ht
  have htRight : t ∈ Set.Icc t₀ r₀ := by
    constructor
    · exact ht.1
    · have hdle : d ≤ r₀ - t₀ := min_le_right _ _
      calc
        t ≤ t₀ + d := ht.2
        _ ≤ t₀ + (r₀ - t₀) := by
          simpa [add_comm] using add_le_add_left hdle t₀
        _ = r₀ := by ring
  have hrefLeft : -t + 2 * t₀ ∈ Set.Icc l₀ t₀ := by
    constructor
    · have hdle : d ≤ t₀ - l₀ := min_le_left _ _
      have htupper : t ≤ t₀ + d := ht.2
      linarith
    · linarith [ht.1]
  apply Subtype.ext
  have hlf := hleft (-t + 2 * t₀) hrefLeft
  have hrf := hright t htRight
  change (ψ (-t + 2 * t₀) : ℝ) = (ψ t : ℝ)
  rw [hlf, hrf]
  ring

/-- Expanding self-similarity globalizes a local fold and makes the
reflection symmetry unique modulo the least period. -/
theorem unique_reflection_of_expanding_dilation
    {ψ : ℝ → I} {P q : ℝ} {T : IntervalMap}
    (hψ : IsUnitSpeedPeriodicSurjection ψ P)
    (hq : 1 < q) (hsemiconj : DilationSemiconjugates ψ q T) :
    ∃ γ : ℝ,
      (∀ t : ℝ, ψ (-t + γ) = ψ t) ∧
      ∀ δ : ℝ, (∀ t : ℝ, ψ (-t + δ) = ψ t) →
        ∃ k : ℤ, δ = γ + (k : ℝ) * P := by
  obtain ⟨l, r, γ₀, hlr, hreflectLocal⟩ :=
    unitSpeedPeriodicSurjection_has_local_reflection hψ
  have hPpos : 0 < P := hψ.2.2.1
  have hqpos : 0 < q := zero_lt_one.trans hq
  have hscalePos : 0 < r - l := sub_pos.mpr hlr
  obtain ⟨n, hn⟩ :=
    (tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop
      (P / (r - l)) |>.exists
  have hn' : P < q ^ n * (r - l) := by
    have := (div_lt_iff₀ hscalePos).1 hn
    simpa [mul_comm] using this
  let L : ℝ := q ^ n * l
  let R : ℝ := q ^ n * r
  let γ : ℝ := q ^ n * γ₀
  have hLR : L < R := by
    dsimp [L, R]
    exact mul_lt_mul_of_pos_left hlr (pow_pos hqpos n)
  have hlength : P < R - L := by
    dsimp [L, R]
    convert hn' using 1 <;> ring
  have hiterate : ∀ m : ℕ, ∀ t : ℝ,
      ψ (q ^ m * t) = iterateMap T m (ψ t) := by
    intro m
    induction m with
    | zero =>
        intro t
        simp [iterateMap]
    | succ m ih =>
        intro t
        calc
          ψ (q ^ (m + 1) * t) = ψ (q * (q ^ m * t)) := by
            congr 1
            rw [pow_succ]
            ring
          _ = T (ψ (q ^ m * t)) := hsemiconj (q ^ m * t)
          _ = T (iterateMap T m (ψ t)) := congrArg T (ih t)
          _ = iterateMap T (m + 1) (ψ t) := by
            simp [iterateMap, Function.iterate_succ_apply']
  have hreflectScaled : ∀ t ∈ Set.Icc L R, ψ (-t + γ) = ψ t := by
    intro t ht
    let s : ℝ := t / q ^ n
    have hpowpos : 0 < q ^ n := pow_pos hqpos n
    have hs : s ∈ Set.Icc l r := by
      constructor
      · dsimp [s]
        exact (le_div_iff₀ hpowpos).2 (by simpa [L, mul_comm] using ht.1)
      · dsimp [s]
        exact (div_le_iff₀ hpowpos).2 (by simpa [R, mul_comm] using ht.2)
    have hlocal := hreflectLocal s hs
    have hscaled := congrArg (iterateMap T n) hlocal
    rw [← hiterate n (-s + γ₀), ← hiterate n s] at hscaled
    convert hscaled using 1 <;> dsimp [s, γ] <;> field_simp <;> ring
  have hreflect : ∀ t : ℝ, ψ (-t + γ) = ψ t := by
    intro t
    let t' : ℝ := toIcoMod hPpos L t
    have ht'Ico : t' ∈ Set.Ico L (L + P) := toIcoMod_mem_Ico hPpos L t
    have ht'Icc : t' ∈ Set.Icc L R := by
      refine ⟨ht'Ico.1, ?_⟩
      exact ht'Ico.2.le.trans (by linarith)
    let z : ℤ := toIcoDiv hPpos L t
    have ht'eq : t' = t - (z : ℝ) * P := by
      dsimp [t', z]
      simpa [smul_eq_mul] using self_sub_toIcoDiv_zsmul hPpos L t
    have hperiod (k : ℤ) : ∀ x : ℝ, ψ (x + (k : ℝ) * P) = ψ x := by
      exact (full_period_group_of_least_period hψ ((k : ℝ) * P)).2 ⟨k, rfl⟩
    have ht'period : ψ t' = ψ t := by
      rw [ht'eq]
      convert hperiod (-z) t using 1 <;> push_cast <;> ring
    have hreflectedPeriod : ψ (-t + γ) = ψ (-t' + γ) := by
      have hshift : -t + γ = (-t' + γ) + (-(z : ℝ)) * P := by
        rw [ht'eq]
        ring
      rw [hshift]
      simpa using hperiod (-z) (-t' + γ)
    calc
      ψ (-t + γ) = ψ (-t' + γ) := hreflectedPeriod
      _ = ψ t' := hreflectScaled t' ht'Icc
      _ = ψ t := ht'period
  refine ⟨γ, hreflect, ?_⟩
  intro δ hδ
  have hperiodDiff : ∀ t : ℝ, ψ (t + (δ - γ)) = ψ t := by
    intro t
    calc
      ψ (t + (δ - γ)) = ψ (-(-t + γ) + δ) := by congr 1 <;> ring
      _ = ψ (-t + γ) := hδ (-t + γ)
      _ = ψ t := hreflect t
  obtain ⟨k, hk⟩ :=
    (full_period_group_of_least_period hψ (δ - γ)).1 hperiodDiff
  refine ⟨k, ?_⟩
  linarith

private theorem int_multiple_is_period
    {f : ℝ → I} {P : ℝ} (hperiod : ∀ t : ℝ, f (t + P) = f t) :
    ∀ k : ℤ, ∀ t : ℝ, f (t + (k : ℝ) * P) = f t := by
  have hadd {a b : ℝ}
      (ha : ∀ t : ℝ, f (t + a) = f t)
      (hb : ∀ t : ℝ, f (t + b) = f t) :
      ∀ t : ℝ, f (t + (a + b)) = f t := by
    intro t
    calc
      f (t + (a + b)) = f ((t + a) + b) := by congr 1 <;> ring
      _ = f (t + a) := hb (t + a)
      _ = f t := ha t
  have hneg {a : ℝ} (ha : ∀ t : ℝ, f (t + a) = f t) :
      ∀ t : ℝ, f (t - a) = f t := by
    intro t
    have h := ha (t - a)
    convert h.symm using 1 <;> ring
  have hnat : ∀ n : ℕ, ∀ t : ℝ,
      f (t + (n : ℝ) * P) = f t := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
        intro t
        convert hadd ih hperiod t using 1 <;> push_cast <;> ring
  intro k
  cases k with
  | ofNat n => exact hnat n
  | negSucc n =>
      intro t
      convert hneg (hnat (n + 1)) t using 1 <;> push_cast <;> ring

theorem periodic_local_match_globalizes
    {u v : ℝ → I} {Pu Pv r : ℝ} {T : IntervalMap}
    (hucont : Continuous u) (hvcont : Continuous v)
    (hPu : 0 < Pu) (hPv : 0 < Pv)
    (huperiod : ∀ t : ℝ, u (t + Pu) = u t)
    (hvperiod : ∀ t : ℝ, v (t + Pv) = v t)
    (hr : 1 < r)
    (huT : DilationSemiconjugates u r T)
    (hvT : DilationSemiconjugates v r T)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    {l s δ₀ : ℝ} (hls : l < s)
    (hlocal : ∀ t ∈ Set.Icc l s,
      v t = u ((ε : ℝ) * t + δ₀)) :
    ∃ δ : ℝ, ∀ t : ℝ, v t = u ((ε : ℝ) * t + δ) := by
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hwidth : 0 < s - l := sub_pos.mpr hls
  have hiteru : ∀ n : ℕ, ∀ t : ℝ,
      u (r ^ n * t) = iterateMap T n (u t) := by
    intro n
    induction n with
    | zero => intro t; simp [iterateMap]
    | succ n ih =>
        intro t
        calc
          u (r ^ (n + 1) * t) = u (r * (r ^ n * t)) := by
            congr 1
            rw [pow_succ]
            ring
          _ = T (u (r ^ n * t)) := huT (r ^ n * t)
          _ = T (iterateMap T n (u t)) := congrArg T (ih t)
          _ = iterateMap T (n + 1) (u t) := by
            simp [iterateMap, Function.iterate_succ_apply']
  have hiterv : ∀ n : ℕ, ∀ t : ℝ,
      v (r ^ n * t) = iterateMap T n (v t) := by
    intro n
    induction n with
    | zero => intro t; simp [iterateMap]
    | succ n ih =>
        intro t
        calc
          v (r ^ (n + 1) * t) = v (r * (r ^ n * t)) := by
            congr 1
            rw [pow_succ]
            ring
          _ = T (v (r ^ n * t)) := hvT (r ^ n * t)
          _ = T (iterateMap T n (v t)) := congrArg T (ih t)
          _ = iterateMap T (n + 1) (v t) := by
            simp [iterateMap, Function.iterate_succ_apply']
  have hscaled : ∀ n : ℕ, ∀ t ∈ Set.Icc (r ^ n * l) (r ^ n * s),
      v t = u ((ε : ℝ) * t + r ^ n * δ₀) := by
    intro n t ht
    have hpowpos : 0 < r ^ n := pow_pos hrpos n
    let z : ℝ := t / r ^ n
    have hz : z ∈ Set.Icc l s := by
      constructor
      · dsimp [z]
        exact (le_div_iff₀ hpowpos).2 (by simpa [mul_comm] using ht.1)
      · dsimp [z]
        exact (div_le_iff₀ hpowpos).2 (by simpa [mul_comm] using ht.2)
    have h := congrArg (iterateMap T n) (hlocal z hz)
    rw [← hiterv n z, ← hiteru n ((ε : ℝ) * z + δ₀)] at h
    convert h using 1 <;> dsimp [z] <;> field_simp <;> ring
  let midpoint : ℕ → ℝ := fun n => r ^ n * ((l + s) / 2)
  let θ : ℕ → ℝ := fun n => toIcoMod hPv 0 (midpoint n)
  let η : ℕ → ℝ := fun n =>
    toIcoMod hPu 0 ((ε : ℝ) * midpoint n + r ^ n * δ₀)
  let phases : ℕ → ℝ × ℝ := fun n => (θ n, η n)
  have hphases : ∀ n,
      phases n ∈ Set.Icc (0 : ℝ) Pv ×ˢ Set.Icc (0 : ℝ) Pu := by
    intro n
    change θ n ∈ Set.Icc (0 : ℝ) Pv ∧ η n ∈ Set.Icc (0 : ℝ) Pu
    constructor
    · dsimp [θ]
      exact ⟨(toIcoMod_mem_Ico hPv 0 (midpoint n)).1,
        by simpa using (toIcoMod_mem_Ico hPv 0 (midpoint n)).2.le⟩
    · dsimp [η]
      exact ⟨(toIcoMod_mem_Ico hPu 0
          ((ε : ℝ) * midpoint n + r ^ n * δ₀)).1,
        by simpa using (toIcoMod_mem_Ico hPu 0
          ((ε : ℝ) * midpoint n + r ^ n * δ₀)).2.le⟩
  obtain ⟨phaseLimit, _hphaseLimit, φ, hφ, hphaseConv⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hphases
  have hθconv : Tendsto (fun n => θ (φ n)) atTop (𝓝 phaseLimit.1) := by
    simpa [phases, Function.comp_def] using
      continuous_fst.continuousAt.tendsto.comp hphaseConv
  have hηconv : Tendsto (fun n => η (φ n)) atTop (𝓝 phaseLimit.2) := by
    simpa [phases, Function.comp_def] using
      continuous_snd.continuousAt.tendsto.comp hphaseConv
  have hpowSubseq : Tendsto (fun n => r ^ φ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).comp hφ.tendsto_atTop
  have hglobalShift : ∀ h : ℝ,
      v (phaseLimit.1 + h) =
        u (phaseLimit.2 + (ε : ℝ) * h) := by
    intro h
    have hlarge : ∀ᶠ n : ℕ in atTop,
        2 * |h| / (s - l) < r ^ φ n :=
      hpowSubseq.eventually_gt_atTop (2 * |h| / (s - l))
    have hinside : ∀ᶠ n : ℕ in atTop,
        midpoint (φ n) + h ∈
          Set.Icc (r ^ φ n * l) (r ^ φ n * s) := by
      filter_upwards [hlarge] with n hn
      have hgrowth : 2 * |h| < r ^ φ n * (s - l) := by
        have := (div_lt_iff₀ hwidth).1 hn
        simpa [mul_comm] using this
      have hpowpos : 0 < r ^ φ n := pow_pos hrpos _
      constructor <;> dsimp [midpoint] <;>
        nlinarith [neg_abs_le h, le_abs_self h]
    have hperiodV (k : ℤ) : ∀ x : ℝ,
        v (x + (k : ℝ) * Pv) = v x :=
      int_multiple_is_period hvperiod k
    have hperiodU (k : ℤ) : ∀ x : ℝ,
        u (x + (k : ℝ) * Pu) = u x :=
      int_multiple_is_period huperiod k
    have heq : ∀ᶠ n : ℕ in atTop,
        v (θ (φ n) + h) = u (η (φ n) + (ε : ℝ) * h) := by
      filter_upwards [hinside] with n hn
      let zv : ℤ := toIcoDiv hPv 0 (midpoint (φ n))
      let zu : ℤ := toIcoDiv hPu 0
        ((ε : ℝ) * midpoint (φ n) + r ^ φ n * δ₀)
      have hθ : θ (φ n) = midpoint (φ n) - (zv : ℝ) * Pv := by
        dsimp [θ, zv]
        simpa [smul_eq_mul] using
          self_sub_toIcoDiv_zsmul hPv 0 (midpoint (φ n))
      have hη : η (φ n) =
          (ε : ℝ) * midpoint (φ n) + r ^ φ n * δ₀ - (zu : ℝ) * Pu := by
        dsimp [η, zu]
        simpa [smul_eq_mul] using
          self_sub_toIcoDiv_zsmul hPu 0
            ((ε : ℝ) * midpoint (φ n) + r ^ φ n * δ₀)
      calc
        v (θ (φ n) + h) = v (midpoint (φ n) + h) := by
          rw [hθ]
          symm
          convert hperiodV zv (θ (φ n) + h) using 1 <;>
            rw [hθ] <;> ring
        _ = u ((ε : ℝ) * (midpoint (φ n) + h) + r ^ φ n * δ₀) :=
          hscaled (φ n) (midpoint (φ n) + h) hn
        _ = u (η (φ n) + (ε : ℝ) * h) := by
          convert hperiodU zu (η (φ n) + (ε : ℝ) * h) using 1 <;>
            rw [hη] <;> ring
    have hvlim : Tendsto (fun n => v (θ (φ n) + h)) atTop
        (𝓝 (v (phaseLimit.1 + h))) :=
      hvcont.continuousAt.tendsto.comp (hθconv.add tendsto_const_nhds)
    have hulim : Tendsto (fun n => u (η (φ n) + (ε : ℝ) * h)) atTop
        (𝓝 (u (phaseLimit.2 + (ε : ℝ) * h))) :=
      hucont.continuousAt.tendsto.comp (hηconv.add tendsto_const_nhds)
    have heq' : (fun n => u (η (φ n) + (ε : ℝ) * h)) =ᶠ[atTop]
        (fun n => v (θ (φ n) + h)) := by
      filter_upwards [heq] with n hn
      exact hn.symm
    exact tendsto_nhds_unique hvlim (hulim.congr' heq')
  let δ : ℝ := phaseLimit.2 - (ε : ℝ) * phaseLimit.1
  refine ⟨δ, ?_⟩
  intro t
  have h := hglobalShift (t - phaseLimit.1)
  calc
    v t = v (phaseLimit.1 + (t - phaseLimit.1)) := by congr 1 <;> ring
    _ = u (phaseLimit.2 + (ε : ℝ) * (t - phaseLimit.1)) := h
    _ = u ((ε : ℝ) * t + δ) := by congr 1 <;> dsimp [δ] <;> ring


end

end CommutingIntervalSimplified
