import CommutingInterval.ConstantSlopeDefs
import CommutingInterval.AffineParity

/-!
# Original-phase affine lifts and the terminal fixed point

The reflection theorem below explicitly includes the expanding
self-similarity used to globalize a local reflection.  Without that
hypothesis, uniqueness is false for general unit-speed periodic polygonal
paths.
-/

namespace CommutingInterval

open Function Set Filter Topology

noncomputable section

/-- Adjacency inside an arbitrary finite real vertex set. -/
def AdjacentInFinset (K : Finset ℝ) (x y : ℝ) : Prop :=
  x ∈ K ∧ y ∈ K ∧ x < y ∧ ∀ z ∈ K, ¬(x < z ∧ z < y)

/-- A real-parameter path is finite-piece PL with slopes of absolute value
one on the compact parameter interval `[a,b]`. -/
def IsFinitePieceUnitSpeedOn (ψ : ℝ → I) (a b : ℝ) : Prop :=
  ∃ K : Finset ℝ, a ∈ K ∧ b ∈ K ∧
    (∀ x ∈ K, x ∈ Set.Icc a b) ∧
    ∀ ⦃x y : ℝ⦄, AdjacentInFinset K x y →
      ∃ m c : ℝ, |m| = 1 ∧
        ∀ t ∈ Set.Icc x y, (ψ t : ℝ) = m * t + c

/-- A nonconstant, onto, locally polygonal unit-speed path with least
positive period `P`. -/
def IsUnitSpeedPeriodicSurjection (ψ : ℝ → I) (P : ℝ) : Prop :=
  Continuous ψ ∧ Surjective ψ ∧ 0 < P ∧
    (∀ t : ℝ, ψ (t + P) = ψ t) ∧
    (∀ r : ℝ, 0 < r → (∀ t : ℝ, ψ (t + r) = ψ t) → P ≤ r) ∧
    ∀ a b : ℝ, a < b → IsFinitePieceUnitSpeedOn ψ a b

/-- Dilation of the parameter by `r` semiconjugates the path to `T`. -/
def DilationSemiconjugates (ψ : ℝ → I) (r : ℝ) (T : IntervalMap) : Prop :=
  ∀ t : ℝ, ψ (r * t) = T (ψ t)

/-- The periods of a nonconstant continuous path with a least positive
period are precisely the integral multiples of that period. -/
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

private theorem unitSpeedPeriodicSurjection_exists_right_affine
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

private theorem unitSpeedPeriodicSurjection_right_descent_from_max
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

/-- A normalized unit-circle path together with affine lifts of both
original-phase interval maps. -/
structure OriginalPhaseLiftPackage (P Q : IntervalMap) where
  /-- The normalized periodic path. -/
  path : UnitAddCircle → I
  /-- Continuity of the circle path. -/
  continuous_path : Continuous path
  /-- The circle path covers the whole physical interval. -/
  onto_path : Surjective path
  /-- The unique reflection has been translated to `t ↦ -t`. -/
  reflection_factor : ∀ t : UnitAddCircle, path (-t) = path t
  /-- Degree of the first affine lift; its sign records orientation. -/
  degreeP : ℤ
  /-- Degree of the second affine lift. -/
  degreeQ : ℤ
  /-- Translation of the first lift. -/
  translationP : UnitAddCircle
  /-- Translation of the second lift. -/
  translationQ : UnitAddCircle
  /-- Reflection commutation restricts the first translation to a half turn. -/
  translationP_half : translationP = 0 ∨ translationP = circleHalf
  /-- Reflection commutation restricts the second translation to a half turn. -/
  translationQ_half : translationQ = 0 ∨ translationQ = circleHalf
  /-- Physical commutation globalizes to exact commutation of affine lifts. -/
  lifts_commute :
    Function.Commute (affineCircleMap degreeP translationP)
      (affineCircleMap degreeQ translationQ)
  /-- The first affine circle map lifts `P`. -/
  lifts_P : ∀ t : UnitAddCircle,
    P (path t) = path (affineCircleMap degreeP translationP t)
  /-- The second affine circle map lifts `Q`. -/
  lifts_Q : ∀ t : UnitAddCircle,
    Q (path t) = path (affineCircleMap degreeQ translationQ t)

/--
The real-coordinate output of applying cross-period globalization to
`t ↦ P (ψ (t / C))` and `t ↦ Q (ψ (t / D))`.  The center `γ / 2` is chosen
after the expanding reflection has been globalized.  Everything after this
record—period descent, half-turn translations, exact lift commutation, and
the terminal parity argument—is formalized below.
-/
structure NormalizedRealAffineLiftData
    (P Q : IntervalMap) (ψ : ℝ → I) (P₀ γ : ℝ) where
  degreeP : ℤ
  degreeQ : ℤ
  degreeP_ne_zero : degreeP ≠ 0
  degreeQ_ne_zero : degreeQ ≠ 0
  translationP : ℝ
  translationQ : ℝ
  lifts_P : ∀ t : ℝ,
    P (ψ (P₀ * t + γ / 2)) =
      ψ (P₀ * ((degreeP : ℝ) * t + translationP) + γ / 2)
  lifts_Q : ∀ t : ℝ,
    Q (ψ (P₀ * t + γ / 2)) =
      ψ (P₀ * ((degreeQ : ℝ) * t + translationQ) + γ / 2)

private theorem RealPartition.exists_left_cell_originalPhase
    (p : RealPartition) {x : I} (hx : leftEndpoint < x) :
    ∃ a : I, ∃ c d : ℝ, a < x ∧ p.Adjacent c d ∧
      Set.Icc a x ⊆ intervalCell c d := by
  classical
  let lower := p.points.filter fun z ↦ z < (x : ℝ)
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    have hx0 : (0 : ℝ) < x := hx
    simp [lower, p.zero_mem, hx0]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  have ha' := Finset.mem_filter.mp ha
  let aI : I := ⟨a, p.points_subset ha'.1⟩
  have hax : aI < x := ha'.2
  let upper := p.points.filter fun z ↦ a < z
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have ha1 : a < 1 := ha'.2.trans_le x.property.2
    exact Finset.mem_filter.mpr ⟨p.one_mem, ha1⟩
  obtain ⟨d, hd, hdmin⟩ := upper.exists_min_image id hupper
  have hd' := Finset.mem_filter.mp hd
  have hxd : (x : ℝ) ≤ d := by
    apply le_of_not_gt
    intro hdx
    have hdlower : d ∈ lower := Finset.mem_filter.mpr ⟨hd'.1, hdx⟩
    have hda : d ≤ a := by simpa using hamax d hdlower
    exact (not_lt_of_ge hda) hd'.2
  have hadj : p.Adjacent a d := by
    refine ⟨ha'.1, hd'.1, hd'.2, ?_⟩
    intro z hz hazd
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hazd.1⟩
    have hdz : d ≤ z := by simpa using hdmin z hzupper
    exact (not_lt_of_ge hdz) hazd.2
  refine ⟨aI, a, d, hax, hadj, ?_⟩
  intro z hz
  change a ≤ (z : ℝ) ∧ (z : ℝ) ≤ d
  have hzleft : a ≤ (z : ℝ) := hz.1
  have hzright : (z : ℝ) ≤ (x : ℝ) := hz.2
  exact ⟨hzleft, hzright.trans hxd⟩

private theorem RealPartition.exists_right_cell_originalPhase
    (p : RealPartition) {x : I} (hx : x < rightEndpoint) :
    ∃ b : I, ∃ c d : ℝ, x < b ∧ p.Adjacent c d ∧
      Set.Icc x b ⊆ intervalCell c d := by
  classical
  let upper := p.points.filter fun z ↦ (x : ℝ) < z
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have hx1 : (x : ℝ) < 1 := hx
    simp [upper, p.one_mem, hx1]
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have hb' := Finset.mem_filter.mp hb
  let bI : I := ⟨b, p.points_subset hb'.1⟩
  have hxb : x < bI := hb'.2
  let lower := p.points.filter fun z ↦ z < b
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    have hb0 : (0 : ℝ) < b := x.property.1.trans_lt hb'.2
    exact Finset.mem_filter.mpr ⟨p.zero_mem, hb0⟩
  obtain ⟨c, hc, hcmax⟩ := lower.exists_max_image id hlower
  have hc' := Finset.mem_filter.mp hc
  have hcx : c ≤ (x : ℝ) := by
    apply le_of_not_gt
    intro hxc
    have hcupper : c ∈ upper := Finset.mem_filter.mpr ⟨hc'.1, hxc⟩
    have hbc : b ≤ c := by simpa using hbmin c hcupper
    exact (not_lt_of_ge hbc) hc'.2
  have hadj : p.Adjacent c b := by
    refine ⟨hc'.1, hb'.1, hc'.2, ?_⟩
    intro z hz hczb
    have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hczb.2⟩
    have hzc : z ≤ c := by simpa using hcmax z hzlower
    exact (not_lt_of_ge hzc) hczb.1
  refine ⟨bI, c, b, hxb, hadj, ?_⟩
  intro z hz
  exact ⟨hcx.trans hz.1, hz.2⟩

private theorem rescaled_constantSlope_exists_right_affine
    {T : IntervalMap} {S P t : ℝ} {ψ : ℝ → I}
    (hS : 0 < S) (hT : HasConstantAbsoluteSlope T S)
    (hψ : IsUnitSpeedPeriodicSurjection ψ P) :
    ∃ r m c : ℝ, t < r ∧ |m| = 1 ∧
      ∀ x ∈ Set.Icc t r,
        (T (ψ (x / S)) : ℝ) = m * x + c := by
  rcases hT with ⟨_hTcont, partition, hpieces⟩
  let z : ℝ := t / S
  obtain ⟨q, μ, d, hzq, hμ, hψaff⟩ :=
    unitSpeedPeriodicSurjection_exists_right_affine hψ z
  have hSt : S * z = t := by
    dsimp [z]
    field_simp [hS.ne']
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hμ with hμone | hμneg
  · have hψzq : ψ z < ψ q := by
      apply Subtype.coe_lt_coe.mp
      have hzform := hψaff z ⟨le_rfl, hzq.le⟩
      have hqform := hψaff q ⟨hzq.le, le_rfl⟩
      rw [hμone] at hzform hqform
      linarith
    have hzright : ψ z < rightEndpoint :=
      hψzq.trans_le (ψ q).property.2
    obtain ⟨b, c, e, hzb, hce, hsub⟩ :=
      partition.exists_right_cell_originalPhase hzright
    obtain ⟨ν, k, hν, hTaff⟩ := hpieces hce
    let w : ℝ := min (q - z) ((b : ℝ) - (ψ z : ℝ)) / 2
    have hwpos : 0 < w := by
      dsimp [w]
      exact half_pos (lt_min (sub_pos.mpr hzq) (sub_pos.mpr hzb))
    have hwq : w < q - z := by
      dsimp [w]
      have hminpos : 0 < min (q - z) ((b : ℝ) - (ψ z : ℝ)) :=
        lt_min (sub_pos.mpr hzq) (sub_pos.mpr hzb)
      have hle := min_le_left (q - z) ((b : ℝ) - (ψ z : ℝ))
      linarith
    have hwb : w < (b : ℝ) - (ψ z : ℝ) := by
      dsimp [w]
      have hminpos : 0 < min (q - z) ((b : ℝ) - (ψ z : ℝ)) :=
        lt_min (sub_pos.mpr hzq) (sub_pos.mpr hzb)
      have hle := min_le_right (q - z) ((b : ℝ) - (ψ z : ℝ))
      linarith
    let r : ℝ := t + S * w
    have htr : t < r := by
      dsimp [r]
      exact lt_add_of_pos_right t (mul_pos hS hwpos)
    refine ⟨r, ν / S, ν * d + k, htr, ?_, ?_⟩
    · rw [abs_div, hν, abs_of_pos hS, div_self hS.ne']
    · intro x hx
      have hzx : z ≤ x / S := by
        apply (le_div_iff₀ hS).2
        calc
          z * S = t := by simpa [mul_comm] using hSt
          _ ≤ x := hx.1
      have hxr : x / S ≤ z + w := by
        apply (div_le_iff₀ hS).2
        dsimp [r] at hx
        calc
          x ≤ t + S * w := hx.2
          _ = (z + w) * S := by rw [← hSt]; ring
      have hxq : x / S ≤ q := by linarith
      have hxin : x / S ∈ Set.Icc z q := ⟨hzx, hxq⟩
      have hψx := hψaff (x / S) hxin
      rw [hμone] at hψx
      have hψlower : ψ z ≤ ψ (x / S) := by
        apply Subtype.coe_le_coe.mp
        have hψz := hψaff z ⟨le_rfl, hzq.le⟩
        rw [hμone] at hψz
        rw [hψz, hψx]
        linarith
      have hψupper : ψ (x / S) ≤ b := by
        apply Subtype.coe_le_coe.mp
        have hψz := hψaff z ⟨le_rfl, hzq.le⟩
        rw [hμone] at hψz
        rw [hψx]
        linarith [hψz]
      have hcell : ψ (x / S) ∈ intervalCell c e :=
        hsub ⟨hψlower, hψupper⟩
      rw [hTaff _ hcell, hψx]
      field_simp [hS.ne']
      ring
  · have hψqz : ψ q < ψ z := by
      apply Subtype.coe_lt_coe.mp
      have hzform := hψaff z ⟨le_rfl, hzq.le⟩
      have hqform := hψaff q ⟨hzq.le, le_rfl⟩
      rw [hμneg] at hzform hqform
      linarith
    have hzleft : leftEndpoint < ψ z :=
      (ψ q).property.1.trans_lt hψqz
    obtain ⟨b, c, e, hbz, hce, hsub⟩ :=
      partition.exists_left_cell_originalPhase hzleft
    obtain ⟨ν, k, hν, hTaff⟩ := hpieces hce
    let w : ℝ := min (q - z) ((ψ z : ℝ) - (b : ℝ)) / 2
    have hwpos : 0 < w := by
      dsimp [w]
      exact half_pos (lt_min (sub_pos.mpr hzq) (sub_pos.mpr hbz))
    have hwq : w < q - z := by
      dsimp [w]
      have hminpos : 0 < min (q - z) ((ψ z : ℝ) - (b : ℝ)) :=
        lt_min (sub_pos.mpr hzq) (sub_pos.mpr hbz)
      have hle := min_le_left (q - z) ((ψ z : ℝ) - (b : ℝ))
      linarith
    have hwb : w < (ψ z : ℝ) - (b : ℝ) := by
      dsimp [w]
      have hminpos : 0 < min (q - z) ((ψ z : ℝ) - (b : ℝ)) :=
        lt_min (sub_pos.mpr hzq) (sub_pos.mpr hbz)
      have hle := min_le_right (q - z) ((ψ z : ℝ) - (b : ℝ))
      linarith
    let r : ℝ := t + S * w
    have htr : t < r := by
      dsimp [r]
      exact lt_add_of_pos_right t (mul_pos hS hwpos)
    refine ⟨r, -ν / S, ν * d + k, htr, ?_, ?_⟩
    · rw [abs_div, abs_neg, hν, abs_of_pos hS, div_self hS.ne']
    · intro x hx
      have hzx : z ≤ x / S := by
        apply (le_div_iff₀ hS).2
        calc
          z * S = t := by simpa [mul_comm] using hSt
          _ ≤ x := hx.1
      have hxr : x / S ≤ z + w := by
        apply (div_le_iff₀ hS).2
        dsimp [r] at hx
        calc
          x ≤ t + S * w := hx.2
          _ = (z + w) * S := by rw [← hSt]; ring
      have hxq : x / S ≤ q := by linarith
      have hxin : x / S ∈ Set.Icc z q := ⟨hzx, hxq⟩
      have hψx := hψaff (x / S) hxin
      rw [hμneg] at hψx
      have hψupper : ψ (x / S) ≤ ψ z := by
        apply Subtype.coe_le_coe.mp
        have hψz := hψaff z ⟨le_rfl, hzq.le⟩
        rw [hμneg] at hψz
        rw [hψx, hψz]
        linarith
      have hψlower : b ≤ ψ (x / S) := by
        apply Subtype.coe_le_coe.mp
        have hψz := hψaff z ⟨le_rfl, hzq.le⟩
        rw [hμneg] at hψz
        rw [hψx]
        linarith [hψz]
      have hcell : ψ (x / S) ∈ intervalCell c e :=
        hsub ⟨hψlower, hψupper⟩
      rw [hTaff _ hcell, hψx]
      field_simp [hS.ne']
      ring

private theorem rescaled_constantSlope_right_descent_from_max
    {T : IntervalMap} {S P t : ℝ} {ψ : ℝ → I}
    (hS : 0 < S) (hT : HasConstantAbsoluteSlope T S)
    (hψ : IsUnitSpeedPeriodicSurjection ψ P)
    (hmax : T (ψ (t / S)) = rightEndpoint) :
    ∃ r : ℝ, t < r ∧ ∀ x ∈ Set.Icc t r,
      (T (ψ (x / S)) : ℝ) = 1 - (x - t) := by
  obtain ⟨r, m, c, htr, hm, haff⟩ :=
    rescaled_constantSlope_exists_right_affine hS hT hψ (t := t)
  have htform := haff t ⟨le_rfl, htr.le⟩
  have hrform := haff r ⟨htr.le, le_rfl⟩
  have htval : (T (ψ (t / S)) : ℝ) = 1 := by
    rw [hmax]
    rfl
  have hrbound : (T (ψ (r / S)) : ℝ) ≤ 1 :=
    (T (ψ (r / S))).property.2
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

private theorem expanding_periodic_local_match_globalizes
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

private theorem original_map_has_integral_affine_parameter_lift
    {P A : IntervalMap} {L : ℕ} {C a P₀ : ℝ} {ψ : ℝ → I}
    (hL : 0 < L) (hA : A = iterateMap P L)
    (hC : 1 < C) (ha : a = C ^ L)
    (hPslopes : HasConstantAbsoluteSlope P C)
    (hpath : IsUnitSpeedPeriodicSurjection ψ P₀)
    (hreturnA : DilationSemiconjugates ψ a A) :
    ∃ k : ℤ, k ≠ 0 ∧ ∃ δ : ℝ,
      ∀ t : ℝ, P (ψ t) = ψ ((k : ℝ) * t + δ) := by
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hP₀pos : 0 < P₀ := hpath.2.2.1
  have ha_gt : 1 < a := by
    rw [ha]
    exact one_lt_pow₀ hC hL.ne'
  have ha_ne : a ≠ 0 := (zero_lt_one.trans ha_gt).ne'
  have hAonto : Surjective A := by
    intro y
    obtain ⟨t, ht⟩ := hpath.2.1 y
    refine ⟨ψ (t / a), ?_⟩
    calc
      A (ψ (t / a)) = ψ (a * (t / a)) := (hreturnA (t / a)).symm
      _ = ψ t := by
        congr 1
        field_simp [ha_ne]
      _ = y := ht
  have hPonto : Surjective P := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
    subst L
    have hiteronto : Surjective (iterateMap P (n + 1)) := by
      rw [← hA]
      exact hAonto
    have hitercomp : iterateMap P (n + 1) = P ∘ iterateMap P n := by
      funext x
      simp [iterateMap, Function.iterate_succ_apply']
    rw [hitercomp] at hiteronto
    exact Function.Surjective.of_comp hiteronto
  let v : ℝ → I := fun t => P (ψ (t / C))
  have hvcont : Continuous v := by
    exact hPslopes.1.comp (hpath.1.comp (by fun_prop))
  have hvonto : Surjective v := by
    intro y
    obtain ⟨x, hPx⟩ := hPonto y
    obtain ⟨z, hψz⟩ := hpath.2.1 x
    refine ⟨C * z, ?_⟩
    dsimp [v]
    have hquot : C * z / C = z := by field_simp [hCpos.ne']
    rw [hquot, hψz, hPx]
  have hvperiod : ∀ t : ℝ, v (t + C * P₀) = v t := by
    intro t
    dsimp [v]
    have hper := hpath.2.2.2.1 (t / C)
    apply congrArg P
    convert hper using 1 <;> field_simp [hCpos.ne'] <;> ring
  have hvA : DilationSemiconjugates v a A := by
    intro t
    dsimp [v]
    calc
      P (ψ (a * t / C)) = P (ψ (a * (t / C))) := by
        congr 2 <;> ring
      _ = P (A (ψ (t / C))) := congrArg P (hreturnA (t / C))
      _ = A (P (ψ (t / C))) := by
        rw [hA]
        exact Function.Commute.self_iterate P L (ψ (t / C))
  obtain ⟨tv, htv⟩ := hvonto rightEndpoint
  obtain ⟨rv, htvRv, hvFormula⟩ :=
    rescaled_constantSlope_right_descent_from_max
      hCpos hPslopes hpath (t := tv) (by simpa [v] using htv)
  obtain ⟨tu, htu⟩ := hpath.2.1 rightEndpoint
  obtain ⟨ru, htuRu, huFormula⟩ :=
    unitSpeedPeriodicSurjection_right_descent_from_max hpath htu
  let width : ℝ := min (rv - tv) (ru - tu)
  have hwidth : 0 < width := by
    dsimp [width]
    exact lt_min (sub_pos.mpr htvRv) (sub_pos.mpr htuRu)
  have hlocal : ∀ t ∈ Set.Icc tv (tv + width),
      v t = ψ (((1 : ℤ) : ℝ) * t + (tu - tv)) := by
    intro t ht
    have htV : t ∈ Set.Icc tv rv := by
      constructor
      · exact ht.1
      · have hwle : width ≤ rv - tv := min_le_left _ _
        calc
          t ≤ tv + width := ht.2
          _ ≤ rv := by linarith
    have htU : t + (tu - tv) ∈ Set.Icc tu ru := by
      constructor
      · linarith [ht.1]
      · have hwle : width ≤ ru - tu := min_le_right _ _
        linarith [ht.2]
    apply Subtype.ext
    change (v t : ℝ) =
      (ψ (((1 : ℤ) : ℝ) * t + (tu - tv)) : ℝ)
    norm_num
    rw [hvFormula t htV, huFormula (t + (tu - tv)) htU]
    ring
  obtain ⟨δ, hglobal⟩ := expanding_periodic_local_match_globalizes
    hpath.1 hvcont hP₀pos (mul_pos hCpos hP₀pos)
      hpath.2.2.2.1 hvperiod ha_gt hreturnA hvA
      (ε := (1 : ℤ)) (Or.inl rfl) (l := tv) (s := tv + width)
      (δ₀ := tu - tv) (by linarith) hlocal
  have hglobal' : ∀ t : ℝ, v t = ψ (t + δ) := by
    intro t
    simpa using hglobal t
  have hψCperiod : ∀ x : ℝ, ψ (x + C * P₀) = ψ x := by
    intro x
    let t : ℝ := x - δ
    calc
      ψ (x + C * P₀) = ψ ((t + C * P₀) + δ) := by
        congr 1
        dsimp [t]
        ring
      _ = v (t + C * P₀) := (hglobal' (t + C * P₀)).symm
      _ = v t := hvperiod t
      _ = ψ (t + δ) := hglobal' t
      _ = ψ x := by
        congr 1
        dsimp [t]
        ring
  obtain ⟨k, hkperiod⟩ :=
    (full_period_group_of_least_period hpath (C * P₀)).1 hψCperiod
  have hkC : (k : ℝ) = C := by
    nlinarith
  have hk : k ≠ 0 := by
    intro hkzero
    subst k
    norm_num at hkC
    linarith
  refine ⟨k, hk, δ, ?_⟩
  intro t
  have h := hglobal' (C * t)
  dsimp [v] at h
  rw [show C * t / C = t by field_simp [hCpos.ne']] at h
  convert h using 1 <;> rw [hkC] <;> ring

/--
Finite-piece constant-slope bookkeeping for the two rescaled original-phase
paths.  This is the precise technical input left after
`cross_period_globalization`: it records the two nonzero integral affine
lifts, but none of the reflection, commutation, or parity conclusions.
-/
theorem normalized_real_affine_lifts_of_cross_period
    {P Q A B : IntervalMap} {L : ℕ}
    {C D a b P₀ γ : ℝ} {ψ : ℝ → I}
    (hL : 0 < L) (hPQ : Commute P Q)
    (hA : A = iterateMap P L) (hB : B = iterateMap Q L)
    (hC : 1 < C) (hD : 1 < D)
    (ha : a = C ^ L) (hb : b = D ^ L)
    (hPslopes : HasConstantAbsoluteSlope P C)
    (hQslopes : HasConstantAbsoluteSlope Q D)
    (hpath : IsUnitSpeedPeriodicSurjection ψ P₀)
    (hreturnA : DilationSemiconjugates ψ a A)
    (hreturnB : DilationSemiconjugates ψ b B)
    (hreflection : ∀ t : ℝ, ψ (-t + γ) = ψ t) :
    Nonempty (NormalizedRealAffineLiftData P Q ψ P₀ γ) := by
  obtain ⟨k, hk, δP, hliftP⟩ :=
    original_map_has_integral_affine_parameter_lift
      hL hA hC ha hPslopes hpath hreturnA
  obtain ⟨ell, hell, δQ, hliftQ⟩ :=
    original_map_has_integral_affine_parameter_lift
      hL hB hD hb hQslopes hpath hreturnB
  have hP₀pos : 0 < P₀ := hpath.2.2.1
  let τP : ℝ := ((k : ℝ) * (γ / 2) + δP - γ / 2) / P₀
  let τQ : ℝ := ((ell : ℝ) * (γ / 2) + δQ - γ / 2) / P₀
  refine ⟨{
    degreeP := k
    degreeQ := ell
    degreeP_ne_zero := hk
    degreeQ_ne_zero := hell
    translationP := τP
    translationQ := τQ
    lifts_P := ?_
    lifts_Q := ?_ }⟩
  · intro t
    rw [hliftP]
    congr 1
    dsimp [τP]
    field_simp [hP₀pos.ne']
    ring
  · intro t
    rw [hliftQ]
    congr 1
    dsimp [τQ]
    field_simp [hP₀pos.ne']
    ring

private theorem unitCircle_liftIco_apply_of_int_periodic
    {X : Type*} {f : ℝ → X}
    (hperiod : ∀ k : ℤ, ∀ t : ℝ, f (t + (k : ℝ)) = f t)
    (t : ℝ) :
    AddCircle.liftIco (1 : ℝ) 0 f (t : UnitAddCircle) = f t := by
  let t' : ℝ := toIcoMod (by norm_num : (0 : ℝ) < 1) 0 t
  let k : ℤ := toIcoDiv (by norm_num : (0 : ℝ) < 1) 0 t
  have ht'mem : t' ∈ Set.Ico (0 : ℝ) 1 := by
    simpa [t'] using
      toIcoMod_mem_Ico (by norm_num : (0 : ℝ) < 1) 0 t
  have ht'eq : t' = t - (k : ℝ) := by
    dsimp [t', k]
    simpa [smul_eq_mul] using
      (self_sub_toIcoDiv_zsmul (by norm_num : (0 : ℝ) < 1) 0 t).symm
  have hcoe : (t' : UnitAddCircle) = (t : UnitAddCircle) := by
    rw [ht'eq]
    change ((t - (k : ℝ) : ℝ) : UnitAddCircle) = (t : UnitAddCircle)
    rw [sub_eq_add_neg, AddCircle.coe_add]
    simp
  calc
    AddCircle.liftIco (1 : ℝ) 0 f (t : UnitAddCircle) =
        AddCircle.liftIco (1 : ℝ) 0 f (t' : UnitAddCircle) := by
      exact congrArg (AddCircle.liftIco (1 : ℝ) 0 f) hcoe.symm
    _ = f t' := AddCircle.liftIco_zero_coe_apply ht'mem
    _ = f t := by
      rw [ht'eq]
      convert hperiod (-k) t using 1 <;> push_cast <;> ring

private theorem unitCircle_eq_zero_or_half_of_two_mul_eq_int
    (α : ℝ) (m : ℤ) (hα : 2 * α = (m : ℝ)) :
    (α : UnitAddCircle) = 0 ∨ (α : UnitAddCircle) = circleHalf := by
  rcases Int.even_or_odd' m with ⟨k, hk | hk⟩
  · left
    have hreal : α = (k : ℝ) := by
      rw [hk] at hα
      push_cast at hα
      linarith
    rw [hreal]
    simp
  · right
    have hreal : α = (k : ℝ) + 1 / 2 := by
      rw [hk] at hα
      push_cast at hα
      linarith
    rw [hreal]
    simp [circleHalf, AddCircle.coe_add]

/-- Cross-period globalization and reflection uniqueness produce affine
circle lifts of the original (not merely normalized-iterate) maps. -/
theorem original_phase_affine_lifts
    {P Q A B : IntervalMap} {L : ℕ}
    {C D a b P₀ : ℝ} {ψ : ℝ → I}
    (hL : 0 < L) (hPQ : Commute P Q)
    (hA : A = iterateMap P L) (hB : B = iterateMap Q L)
    (hC : 1 < C) (hD : 1 < D)
    (ha : a = C ^ L) (hb : b = D ^ L)
    (hPslopes : HasConstantAbsoluteSlope P C)
    (hQslopes : HasConstantAbsoluteSlope Q D)
    (hpath : IsUnitSpeedPeriodicSurjection ψ P₀)
    (hreturnA : DilationSemiconjugates ψ a A)
    (hreturnB : DilationSemiconjugates ψ b B) :
    Nonempty (OriginalPhaseLiftPackage P Q) := by
  have ha_gt : 1 < a := by
    rw [ha]
    exact one_lt_pow₀ hC hL.ne'
  obtain ⟨γ, hreflection, _hreflectionUnique⟩ :=
    unique_reflection_of_expanding_dilation hpath ha_gt hreturnA
  obtain ⟨Dreal⟩ := normalized_real_affine_lifts_of_cross_period
    hL hPQ hA hB hC hD ha hb hPslopes hQslopes hpath
      hreturnA hreturnB hreflection
  have hP₀pos : 0 < P₀ := hpath.2.2.1
  have hP₀ne : P₀ ≠ 0 := hP₀pos.ne'
  let f : ℝ → I := fun t => ψ (P₀ * t + γ / 2)
  have hfcont : Continuous f := by
    exact hpath.1.comp (by fun_prop)
  have hfperiod (k : ℤ) (t : ℝ) : f (t + (k : ℝ)) = f t := by
    have hper :=
      (full_period_group_of_least_period hpath ((k : ℝ) * P₀)).2 ⟨k, rfl⟩
        (P₀ * t + γ / 2)
    dsimp [f]
    convert hper using 1 <;> ring
  have hfeval (t : ℝ) :
      AddCircle.liftIco (1 : ℝ) 0 f (t : UnitAddCircle) = f t :=
    unitCircle_liftIco_apply_of_int_periodic hfperiod t
  have hffullPeriod {d : ℝ} (hd : ∀ t : ℝ, f (t + d) = f t) :
      ∃ k : ℤ, d = (k : ℝ) := by
    have hψperiod : ∀ x : ℝ, ψ (x + P₀ * d) = ψ x := by
      intro x
      let t : ℝ := (x - γ / 2) / P₀
      have h := hd t
      dsimp [f, t] at h
      convert h using 1 <;> field_simp [hP₀ne] <;> ring
    obtain ⟨k, hk⟩ :=
      (full_period_group_of_least_period hpath (P₀ * d)).1 hψperiod
    refine ⟨k, ?_⟩
    nlinarith
  have hfneg (t : ℝ) : f (-t) = f t := by
    dsimp [f]
    convert hreflection (P₀ * t + γ / 2) using 1 <;> ring
  have hliftP (t : ℝ) :
      P (f t) = f ((Dreal.degreeP : ℝ) * t + Dreal.translationP) := by
    simpa [f] using Dreal.lifts_P t
  have hliftQ (t : ℝ) :
      Q (f t) = f ((Dreal.degreeQ : ℝ) * t + Dreal.translationQ) := by
    simpa [f] using Dreal.lifts_Q t
  have hkne : (Dreal.degreeP : ℝ) ≠ 0 := by exact_mod_cast Dreal.degreeP_ne_zero
  have hℓne : (Dreal.degreeQ : ℝ) ≠ 0 := by exact_mod_cast Dreal.degreeQ_ne_zero
  have hαreflection (y : ℝ) :
      f (-y + 2 * Dreal.translationP) = f y := by
    let x : ℝ := (y - Dreal.translationP) / (Dreal.degreeP : ℝ)
    have hx : (Dreal.degreeP : ℝ) * x + Dreal.translationP = y := by
      dsimp [x]
      field_simp [hkne]
      ring
    have hxneg : (Dreal.degreeP : ℝ) * (-x) + Dreal.translationP =
        -y + 2 * Dreal.translationP := by
      dsimp [x]
      field_simp [hkne]
      ring
    calc
      f (-y + 2 * Dreal.translationP) = P (f (-x)) := by
        rw [hliftP]
        congr 1
        exact hxneg.symm
      _ = P (f x) := congrArg P (hfneg x)
      _ = f y := by rw [hliftP, hx]
  have hαperiod : ∀ t : ℝ,
      f (t + 2 * Dreal.translationP) = f t := by
    intro t
    calc
      f (t + 2 * Dreal.translationP) =
          f (-(-t) + 2 * Dreal.translationP) := by congr 1 <;> ring
      _ = f (-t) := hαreflection (-t)
      _ = f t := hfneg t
  obtain ⟨mα, hmα⟩ := hffullPeriod hαperiod
  have hαhalf :
      (Dreal.translationP : UnitAddCircle) = 0 ∨
        (Dreal.translationP : UnitAddCircle) = circleHalf :=
    unitCircle_eq_zero_or_half_of_two_mul_eq_int Dreal.translationP mα hmα
  have hβreflection (y : ℝ) :
      f (-y + 2 * Dreal.translationQ) = f y := by
    let x : ℝ := (y - Dreal.translationQ) / (Dreal.degreeQ : ℝ)
    have hx : (Dreal.degreeQ : ℝ) * x + Dreal.translationQ = y := by
      dsimp [x]
      field_simp [hℓne]
      ring
    have hxneg : (Dreal.degreeQ : ℝ) * (-x) + Dreal.translationQ =
        -y + 2 * Dreal.translationQ := by
      dsimp [x]
      field_simp [hℓne]
      ring
    calc
      f (-y + 2 * Dreal.translationQ) = Q (f (-x)) := by
        rw [hliftQ]
        congr 1
        exact hxneg.symm
      _ = Q (f x) := congrArg Q (hfneg x)
      _ = f y := by rw [hliftQ, hx]
  have hβperiod : ∀ t : ℝ,
      f (t + 2 * Dreal.translationQ) = f t := by
    intro t
    calc
      f (t + 2 * Dreal.translationQ) =
          f (-(-t) + 2 * Dreal.translationQ) := by congr 1 <;> ring
      _ = f (-t) := hβreflection (-t)
      _ = f t := hfneg t
  obtain ⟨mβ, hmβ⟩ := hffullPeriod hβperiod
  have hβhalf :
      (Dreal.translationQ : UnitAddCircle) = 0 ∨
        (Dreal.translationQ : UnitAddCircle) = circleHalf :=
    unitCircle_eq_zero_or_half_of_two_mul_eq_int Dreal.translationQ mβ hmβ
  have hcomposedLifts (t : ℝ) :
      f ((Dreal.degreeP : ℝ) *
          ((Dreal.degreeQ : ℝ) * t + Dreal.translationQ) +
            Dreal.translationP) =
        f ((Dreal.degreeQ : ℝ) *
          ((Dreal.degreeP : ℝ) * t + Dreal.translationP) +
            Dreal.translationQ) := by
    calc
      f ((Dreal.degreeP : ℝ) *
          ((Dreal.degreeQ : ℝ) * t + Dreal.translationQ) +
            Dreal.translationP) = P (f ((Dreal.degreeQ : ℝ) * t + Dreal.translationQ)) :=
        (hliftP _).symm
      _ = P (Q (f t)) := congrArg P (hliftQ t).symm
      _ = Q (P (f t)) := hPQ (f t)
      _ = Q (f ((Dreal.degreeP : ℝ) * t + Dreal.translationP)) :=
        congrArg Q (hliftP t)
      _ = f ((Dreal.degreeQ : ℝ) *
          ((Dreal.degreeP : ℝ) * t + Dreal.translationP) +
            Dreal.translationQ) := hliftQ _
  let Δ : ℝ :=
    ((Dreal.degreeP : ℝ) * Dreal.translationQ + Dreal.translationP) -
      ((Dreal.degreeQ : ℝ) * Dreal.translationP + Dreal.translationQ)
  have hΔperiod : ∀ y : ℝ, f (y + Δ) = f y := by
    intro y
    let x : ℝ :=
      (y - ((Dreal.degreeQ : ℝ) * Dreal.translationP +
        Dreal.translationQ)) /
          ((Dreal.degreeP : ℝ) * (Dreal.degreeQ : ℝ))
    have hprodne :
        (Dreal.degreeP : ℝ) * (Dreal.degreeQ : ℝ) ≠ 0 := mul_ne_zero hkne hℓne
    calc
      f (y + Δ) = f ((Dreal.degreeP : ℝ) *
          ((Dreal.degreeQ : ℝ) * x + Dreal.translationQ) +
            Dreal.translationP) := by
        congr 1
        dsimp [x, Δ]
        field_simp [hprodne]
        ring
      _ = f ((Dreal.degreeQ : ℝ) *
          ((Dreal.degreeP : ℝ) * x + Dreal.translationP) +
            Dreal.translationQ) := hcomposedLifts x
      _ = f y := by
        congr 1
        dsimp [x]
        field_simp [hprodne]
        ring
  obtain ⟨mΔ, hmΔ⟩ := hffullPeriod hΔperiod
  have htranslationRelation :
      Dreal.degreeP • (Dreal.translationQ : UnitAddCircle) +
          (Dreal.translationP : UnitAddCircle) =
        Dreal.degreeQ • (Dreal.translationP : UnitAddCircle) +
          (Dreal.translationQ : UnitAddCircle) := by
    have hreal :
        (Dreal.degreeP : ℝ) * Dreal.translationQ + Dreal.translationP =
          (Dreal.degreeQ : ℝ) * Dreal.translationP + Dreal.translationQ +
            (mΔ : ℝ) := by
      dsimp [Δ] at hmΔ
      linarith
    calc
      Dreal.degreeP • (Dreal.translationQ : UnitAddCircle) +
          (Dreal.translationP : UnitAddCircle) =
          (((Dreal.degreeP : ℝ) * Dreal.translationQ +
            Dreal.translationP : ℝ) : UnitAddCircle) := by
        rw [← AddCircle.coe_zsmul, ← AddCircle.coe_add]
        congr 1
        ring
      _ = (((Dreal.degreeQ : ℝ) * Dreal.translationP +
            Dreal.translationQ : ℝ) : UnitAddCircle) := by
        rw [hreal, AddCircle.coe_add]
        simp
      _ = Dreal.degreeQ • (Dreal.translationP : UnitAddCircle) +
          (Dreal.translationQ : UnitAddCircle) := by
        rw [← AddCircle.coe_zsmul, ← AddCircle.coe_add]
        congr 1
        ring
  have hliftsCommute :
      Function.Commute
        (affineCircleMap Dreal.degreeP (Dreal.translationP : UnitAddCircle))
        (affineCircleMap Dreal.degreeQ (Dreal.translationQ : UnitAddCircle)) := by
    intro t
    simp only [affineCircleMap]
    calc
      Dreal.degreeP •
            (Dreal.degreeQ • t + (Dreal.translationQ : UnitAddCircle)) +
          (Dreal.translationP : UnitAddCircle) =
          (Dreal.degreeP * Dreal.degreeQ) • t +
            (Dreal.degreeP • (Dreal.translationQ : UnitAddCircle) +
              (Dreal.translationP : UnitAddCircle)) := by
        rw [smul_add, smul_smul]
        abel
      _ = (Dreal.degreeQ * Dreal.degreeP) • t +
            (Dreal.degreeQ • (Dreal.translationP : UnitAddCircle) +
              (Dreal.translationQ : UnitAddCircle)) := by
        rw [mul_comm, htranslationRelation]
      _ = Dreal.degreeQ •
            (Dreal.degreeP • t + (Dreal.translationP : UnitAddCircle)) +
          (Dreal.translationQ : UnitAddCircle) := by
        rw [smul_add, smul_smul]
        abel
  let path : UnitAddCircle → I := AddCircle.liftIco (1 : ℝ) 0 f
  have hpathCont : Continuous path := by
    apply AddCircle.liftIco_zero_continuous
    · simpa using (hfperiod 1 0).symm
    · exact hfcont.continuousOn
  have hpathOnto : Surjective path := by
    intro y
    obtain ⟨x, hx⟩ := hpath.2.1 y
    let t : ℝ := (x - γ / 2) / P₀
    refine ⟨(t : UnitAddCircle), ?_⟩
    change AddCircle.liftIco (1 : ℝ) 0 f (t : UnitAddCircle) = y
    rw [hfeval]
    dsimp [f, t]
    convert hx using 1 <;> field_simp [hP₀ne] <;> ring
  have hpathReflection : ∀ t : UnitAddCircle, path (-t) = path t := by
    intro t
    obtain ⟨x, _hx, rfl⟩ := AddCircle.eq_coe_Ico t
    change AddCircle.liftIco (1 : ℝ) 0 f (-((x : ℝ) : UnitAddCircle)) =
      AddCircle.liftIco (1 : ℝ) 0 f ((x : ℝ) : UnitAddCircle)
    rw [← AddCircle.coe_neg, hfeval, hfeval, hfneg]
  have hcircleLiftP : ∀ t : UnitAddCircle,
      P (path t) =
        path (affineCircleMap Dreal.degreeP
          (Dreal.translationP : UnitAddCircle) t) := by
    intro t
    obtain ⟨x, _hx, rfl⟩ := AddCircle.eq_coe_Ico t
    calc
      P (path ((x : ℝ) : UnitAddCircle)) = P (f x) := by
        dsimp [path]
        rw [hfeval]
      _ = f ((Dreal.degreeP : ℝ) * x + Dreal.translationP) := hliftP x
      _ = path ((((Dreal.degreeP : ℝ) * x + Dreal.translationP : ℝ) :
          UnitAddCircle)) := by
        dsimp [path]
        exact (hfeval _).symm
      _ = path (affineCircleMap Dreal.degreeP
          (Dreal.translationP : UnitAddCircle) ((x : ℝ) : UnitAddCircle)) := by
        congr 1
        rw [affineCircleMap, ← AddCircle.coe_zsmul, ← AddCircle.coe_add]
        congr 1
        ring
  have hcircleLiftQ : ∀ t : UnitAddCircle,
      Q (path t) =
        path (affineCircleMap Dreal.degreeQ
          (Dreal.translationQ : UnitAddCircle) t) := by
    intro t
    obtain ⟨x, _hx, rfl⟩ := AddCircle.eq_coe_Ico t
    calc
      Q (path ((x : ℝ) : UnitAddCircle)) = Q (f x) := by
        dsimp [path]
        rw [hfeval]
      _ = f ((Dreal.degreeQ : ℝ) * x + Dreal.translationQ) := hliftQ x
      _ = path ((((Dreal.degreeQ : ℝ) * x + Dreal.translationQ : ℝ) :
          UnitAddCircle)) := by
        dsimp [path]
        exact (hfeval _).symm
      _ = path (affineCircleMap Dreal.degreeQ
          (Dreal.translationQ : UnitAddCircle) ((x : ℝ) : UnitAddCircle)) := by
        congr 1
        rw [affineCircleMap, ← AddCircle.coe_zsmul, ← AddCircle.coe_add]
        congr 1
        ring
  exact ⟨{
    path := path
    continuous_path := hpathCont
    onto_path := hpathOnto
    reflection_factor := hpathReflection
    degreeP := Dreal.degreeP
    degreeQ := Dreal.degreeQ
    translationP := (Dreal.translationP : UnitAddCircle)
    translationQ := (Dreal.translationQ : UnitAddCircle)
    translationP_half := hαhalf
    translationQ_half := hβhalf
    lifts_commute := hliftsCommute
    lifts_P := hcircleLiftP
    lifts_Q := hcircleLiftQ }⟩

/-- The terminal parity calculation on the reflection quotient gives a
physical common fixed point. -/
theorem common_fixed_point_of_original_phase_package
    {P Q : IntervalMap} (pkg : OriginalPhaseLiftPackage P Q) :
    HasCommonFixedPoint P Q := by
  obtain ⟨t, hPt, hQt⟩ :=
    exists_common_reflection_orbit_of_half_translations
      pkg.degreeP pkg.degreeQ pkg.translationP pkg.translationQ
      pkg.translationP_half pkg.translationQ_half pkg.lifts_commute
  refine ⟨pkg.path t, ?_⟩
  constructor
  · rw [IsFixedPoint, pkg.lifts_P]
    rcases hPt with ht | ht
    · rw [ht]
    · rw [ht]
      exact pkg.reflection_factor t
  · rw [IsFixedPoint, pkg.lifts_Q]
    rcases hQt with ht | ht
    · rw [ht]
    · rw [ht]
      exact pkg.reflection_factor t

end

end CommutingInterval
