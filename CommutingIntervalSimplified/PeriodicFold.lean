import CommutingIntervalSimplified.Defs
import CommutingIntervalSimplified.PeriodicAffineLifts
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# From an eventually periodic two-scale fold to a common fixed point

The proved terminal affine-circle argument consumes an onto periodic
unit-speed path with global dilation identities.  This file records the
remaining eventual-tail globalization as a sequence of explicit interfaces,
then applies the terminal argument without further assumptions.
-/

namespace CommutingIntervalSimplified

open Function Set Filter Topology

noncomputable section

/-! ## Globalizing an eventually periodic tail -/

/-- `period` is the least positive period of a real-parameter path. -/
def IsLeastPositivePeriod (ψ : ℝ → I) (period : ℝ) : Prop :=
  0 < period ∧
    (∀ t : ℝ, ψ (t + period) = ψ t) ∧
    ∀ r : ℝ, 0 < r → (∀ t : ℝ, ψ (t + r) = ψ t) → period ≤ r

/--
The global periodic path obtained by copying an eventually periodic ray tail
backwards.  The agreement field pins the construction to the original fold,
while the remaining fields are exactly the geometric facts needed later.
-/
structure PeriodicTailExtension
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b) where
  path : ℝ → I
  cutoff : ℝ
  cutoff_nonneg : 0 ≤ cutoff
  period : ℝ
  period_pos : 0 < period
  continuous_path : Continuous path
  periodic_path : ∀ t : ℝ, path (t + period) = path t
  finitePieceOn : ∀ x y : ℝ, x < y → IsFinitePieceUnitSpeedOn path x y
  nonconstant_path : ∃ x y : ℝ, path x ≠ path y
  agrees_on_tail : ∀ t : ℝ, cutoff ≤ t → path t = F.ray t

namespace PeriodicTailExtension

variable {A B : IntervalMap} {a b : ℝ} {F : TwoScaleFoldData A B a b}

/-- The first dilation identity holds on the copied tail. -/
theorem eventually_return_A (E : PeriodicTailExtension F) :
    ∀ t : ℝ, E.cutoff ≤ t → E.path (a * t) = A (E.path t) := by
  intro t ht
  have ht0 : 0 ≤ t := E.cutoff_nonneg.trans ht
  have hat : E.cutoff ≤ a * t := by
    calc
      E.cutoff ≤ t := ht
      _ ≤ a * t := by nlinarith [F.one_lt_a]
  rw [E.agrees_on_tail (a * t) hat, E.agrees_on_tail t ht]
  exact F.return_A t ht0

/-- The second dilation identity holds on the copied tail. -/
theorem eventually_return_B (E : PeriodicTailExtension F) :
    ∀ t : ℝ, E.cutoff ≤ t → E.path (b * t) = B (E.path t) := by
  intro t ht
  have ht0 : 0 ≤ t := E.cutoff_nonneg.trans ht
  have hbt : E.cutoff ≤ b * t := by
    calc
      E.cutoff ≤ t := ht
      _ ≤ b * t := by nlinarith [F.one_lt_b]
  rw [E.agrees_on_tail (b * t) hbt, E.agrees_on_tail t ht]
  exact F.return_B t ht0

end PeriodicTailExtension

/-- Translating the parameter of a finite unit-speed subdivision preserves
the subdivision and its slopes. -/
private theorem finitePieceUnitSpeedOn_translate
    {f g : ℝ → I} {a b shift : ℝ}
    (hpieces : IsFinitePieceUnitSpeedOn f (a + shift) (b + shift))
    (heq : ∀ t ∈ Set.Icc a b, g t = f (t + shift)) :
    IsFinitePieceUnitSpeedOn g a b := by
  rcases hpieces with ⟨K, haK, hbK, hKbounds, hlinear⟩
  let K' : Finset ℝ := K.image (fun t => t - shift)
  refine ⟨K', ?_, ?_, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨a + shift, haK, by ring⟩
  · apply Finset.mem_image.mpr
    exact ⟨b + shift, hbK, by ring⟩
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨u, huK, rfl⟩
    have hu := hKbounds u huK
    constructor <;> linarith [hu.1, hu.2]
  · intro x y hxy
    rcases Finset.mem_image.mp hxy.1 with ⟨x', hx'K, hx'eq⟩
    rcases Finset.mem_image.mp hxy.2.1 with ⟨y', hy'K, hy'eq⟩
    have hx' : x' = x + shift := by linarith
    have hy' : y' = y + shift := by linarith
    subst x'
    subst y'
    have hAdj : AdjacentInFinset K (x + shift) (y + shift) := by
      refine ⟨hx'K, hy'K, by linarith [hxy.2.2.1], ?_⟩
      intro z hzK hzbetween
      exact hxy.2.2.2 (z - shift)
        (Finset.mem_image.mpr ⟨z, hzK, rfl⟩)
        ⟨by linarith [hzbetween.1], by linarith [hzbetween.2]⟩
    obtain ⟨m, c, hm, hformula⟩ := hlinear hAdj
    refine ⟨m, m * shift + c, hm, ?_⟩
    intro t ht
    have hxBounds := hKbounds (x + shift) hx'K
    have hyBounds := hKbounds (y + shift) hy'K
    have htAB : t ∈ Set.Icc a b := by
      constructor <;> linarith [hxBounds.1, hyBounds.2, ht.1, ht.2]
    have htShift : t + shift ∈ Set.Icc (x + shift) (y + shift) := by
      constructor <;> linarith [ht.1, ht.2]
    rw [heq t htAB, hformula (t + shift) htShift]
    ring

/-- Eventual periodicity of the fold produces a global periodic tail copy. -/
theorem periodicTailExtension_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (heventual : EventuallyPeriodicOnRay F.ray) :
    Nonempty (PeriodicTailExtension F) := by
  classical
  rcases heventual with ⟨tailStart, P, htailStart, hPpos, hstep⟩
  have hnatPeriod (t : ℝ) (ht : tailStart ≤ t) :
      ∀ n : ℕ, F.ray (t + (n : ℝ) * P) = F.ray t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hnnonneg : 0 ≤ (n : ℝ) * P :=
          mul_nonneg (Nat.cast_nonneg n) hPpos.le
        calc
          F.ray (t + ((n + 1 : ℕ) : ℝ) * P) =
              F.ray ((t + (n : ℝ) * P) + P) := by
            congr 1
            push_cast
            ring
          _ = F.ray (t + (n : ℝ) * P) :=
            hstep _ (ht.trans (le_add_of_nonneg_right hnnonneg))
          _ = F.ray t := ih
  have hexistsShift (t : ℝ) :
      ∃ n : ℕ, tailStart ≤ t + (n : ℝ) * P := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((tailStart - t) / P)
    have hmul : tailStart - t < (n : ℝ) * P :=
      (div_lt_iff₀ hPpos).mp hn
    exact ⟨n, by linarith⟩
  let shiftIndex : ℝ → ℕ := fun t => (hexistsShift t).choose
  have hshiftLate (t : ℝ) :
      tailStart ≤ t + (shiftIndex t : ℝ) * P :=
    (hexistsShift t).choose_spec
  let path : ℝ → I := fun t =>
    F.ray (t + (shiftIndex t : ℝ) * P)
  have hpath_eq_shift (t : ℝ) (n : ℕ)
      (hn : tailStart ≤ t + (n : ℝ) * P) :
      path t = F.ray (t + (n : ℝ) * P) := by
    by_cases hle : shiftIndex t ≤ n
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      calc
        path t = F.ray (t + (shiftIndex t : ℝ) * P) := rfl
        _ = F.ray ((t + (shiftIndex t : ℝ) * P) + (k : ℝ) * P) :=
          (hnatPeriod _ (hshiftLate t) k).symm
        _ = F.ray (t + (n : ℝ) * P) := by
          rw [hk]
          congr 1
          push_cast
          ring
    · have hnle : n ≤ shiftIndex t := Nat.le_of_not_ge hle
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnle
      calc
        path t = F.ray (t + (shiftIndex t : ℝ) * P) := rfl
        _ = F.ray ((t + (n : ℝ) * P) + (k : ℝ) * P) := by
          rw [hk]
          congr 1
          push_cast
          ring
        _ = F.ray (t + (n : ℝ) * P) := hnatPeriod _ hn k
  have hpathContinuous : Continuous path := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt ((tailStart - t) / P)
    have htstrict : tailStart < t + (n : ℝ) * P := by
      have hmul : tailStart - t < (n : ℝ) * P :=
        (div_lt_iff₀ hPpos).mp hn
      linarith
    have htranslate : Continuous (fun s : ℝ => s + (n : ℝ) * P) :=
      continuous_id.add continuous_const
    have hopen : IsOpen {s : ℝ | tailStart < s + (n : ℝ) * P} :=
      isOpen_lt continuous_const htranslate
    have hlocal :
        (fun s : ℝ => F.ray (s + (n : ℝ) * P)) =ᶠ[𝓝 t] path := by
      filter_upwards [hopen.mem_nhds htstrict] with s hs
      exact (hpath_eq_shift s n hs.le).symm
    have hpositive : 0 < t + (n : ℝ) * P :=
      htailStart.trans_lt htstrict
    have hrayAt : ContinuousAt F.ray (t + (n : ℝ) * P) :=
      (F.continuousOn_ray _ (Set.mem_Ici.mpr hpositive.le)).continuousAt
        (Ici_mem_nhds hpositive)
    have hcomp : ContinuousAt
        (F.ray ∘ fun s : ℝ => s + (n : ℝ) * P) t :=
      ContinuousAt.comp (f := fun s : ℝ => s + (n : ℝ) * P)
        hrayAt htranslate.continuousAt
    have hcomp' : ContinuousAt
        (fun s : ℝ => F.ray (s + (n : ℝ) * P)) t := by
      simpa [Function.comp_def] using hcomp
    exact hcomp'.congr hlocal
  have hpathPeriodic : ∀ t : ℝ, path (t + P) = path t := by
    intro t
    obtain ⟨n, hn⟩ := hexistsShift (t + P)
    have hn' : tailStart ≤ t + ((n + 1 : ℕ) : ℝ) * P := by
      convert hn using 1 <;> push_cast <;> ring
    calc
      path (t + P) = F.ray ((t + P) + (n : ℝ) * P) :=
        hpath_eq_shift (t + P) n hn
      _ = F.ray (t + ((n + 1 : ℕ) : ℝ) * P) := by
        congr 1
        push_cast
        ring
      _ = path t := (hpath_eq_shift t (n + 1) hn').symm
  have hagree : ∀ t : ℝ, tailStart ≤ t → path t = F.ray t := by
    intro t ht
    simpa using hpath_eq_shift t 0 (by simpa using ht)
  have hperiodNat (t : ℝ) :
      ∀ n : ℕ, path (t + (n : ℝ) * P) = path t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          path (t + ((n + 1 : ℕ) : ℝ) * P) =
              path ((t + (n : ℝ) * P) + P) := by
            congr 1
            push_cast
            ring
          _ = path (t + (n : ℝ) * P) := hpathPeriodic _
          _ = path t := ih
  have hfinitePiece : ∀ x y : ℝ, x < y →
      IsFinitePieceUnitSpeedOn path x y := by
    intro x y hxy
    obtain ⟨n, hn⟩ := exists_nat_gt ((tailStart - x) / P)
    have hlateX : tailStart ≤ x + (n : ℝ) * P := by
      have hmul : tailStart - x < (n : ℝ) * P :=
        (div_lt_iff₀ hPpos).mp hn
      linarith
    have hpieces := F.locally_unit_speed
      (x + (n : ℝ) * P) (y + (n : ℝ) * P)
      (htailStart.trans hlateX) (by linarith)
    apply finitePieceUnitSpeedOn_translate hpieces
    intro t ht
    calc
      path t = path (t + (n : ℝ) * P) := (hperiodNat t n).symm
      _ = F.ray (t + (n : ℝ) * P) :=
        hagree _ (hlateX.trans (by linarith [ht.1]))
  have hnonconstant : ∃ x y : ℝ, path x ≠ path y := by
    obtain ⟨K, hTK, hTOneK, hKbounds, hlinear⟩ :=
      F.locally_unit_speed tailStart (tailStart + 1) htailStart (by linarith)
    let later : Finset ℝ := K.filter (fun z => tailStart < z)
    have hlater : later.Nonempty := by
      refine ⟨tailStart + 1, ?_⟩
      simp only [later, Finset.mem_filter]
      exact ⟨hTOneK, by linarith⟩
    let y : ℝ := later.min' hlater
    have hyLater : y ∈ later := later.min'_mem hlater
    have hyK : y ∈ K := (Finset.mem_filter.mp hyLater).1
    have hTy : tailStart < y := (Finset.mem_filter.mp hyLater).2
    have hAdjacent : AdjacentInFinset K tailStart y := by
      refine ⟨hTK, hyK, hTy, ?_⟩
      intro z hzK hzBetween
      have hzLater : z ∈ later := by
        simp only [later, Finset.mem_filter]
        exact ⟨hzK, hzBetween.1⟩
      exact (not_lt_of_ge (later.min'_le z hzLater)) hzBetween.2
    obtain ⟨m, c, hm, hformula⟩ := hlinear hAdjacent
    have hmne : m ≠ 0 := by
      intro hmzero
      subst m
      norm_num at hm
    have hvalues : F.ray tailStart ≠ F.ray y := by
      intro heq
      have heqReal : (F.ray tailStart : ℝ) = (F.ray y : ℝ) :=
        congrArg Subtype.val heq
      rw [hformula tailStart ⟨le_rfl, hTy.le⟩,
        hformula y ⟨hTy.le, le_rfl⟩] at heqReal
      have hmul : m * (tailStart - y) = 0 := by linarith
      rcases mul_eq_zero.mp hmul with hmzero | hTyzero
      · exact hmne hmzero
      · exact (ne_of_lt hTy) (sub_eq_zero.mp hTyzero)
    refine ⟨tailStart, y, ?_⟩
    rw [hagree tailStart le_rfl, hagree y hTy.le]
    exact hvalues
  exact ⟨{
    path := path
    cutoff := tailStart
    cutoff_nonneg := htailStart
    period := P
    period_pos := hPpos
    continuous_path := hpathContinuous
    periodic_path := hpathPeriodic
    finitePieceOn := hfinitePiece
    nonconstant_path := hnonconstant
    agrees_on_tail := hagree }⟩

/-- Additive group of all real periods of a path. -/
private def pathPeriodGroup (path : ℝ → I) : AddSubgroup ℝ where
  carrier := {r | ∀ t : ℝ, path (t + r) = path t}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs t
    simpa [add_assoc] using (Eq.trans (hs (t + r)) (hr t))
  neg_mem' := by
    intro r hr t
    have h := (hr (t - r)).symm
    simpa [sub_eq_add_neg, add_assoc] using h

/-- A least positive period generates the whole real period group. -/
private theorem pathPeriodGroup_eq_integer_multiples
    {path : ℝ → I} {P : ℝ}
    (hleast : IsLeastPositivePeriod path P) :
    ∀ r : ℝ, r ∈ pathPeriodGroup path ↔
      ∃ k : ℤ, r = (k : ℝ) * P := by
  intro r
  constructor
  · intro hr
    let k : ℤ := ⌊r / P⌋
    let s : ℝ := r - (k : ℝ) * P
    have hklo : (k : ℝ) ≤ r / P := Int.floor_le (r / P)
    have hkhi : r / P < (k : ℝ) + 1 := Int.lt_floor_add_one (r / P)
    have hmullo : (k : ℝ) * P ≤ r :=
      (le_div_iff₀ hleast.1).mp (by simpa [mul_comm] using hklo)
    have hmulhi : r < ((k : ℝ) + 1) * P :=
      (div_lt_iff₀ hleast.1).mp hkhi
    have hsnonneg : 0 ≤ s := by dsimp [s]; linarith
    have hslt : s < P := by dsimp [s]; linarith
    have hkperiod : (k : ℝ) * P ∈ pathPeriodGroup path := by
      simpa [zsmul_eq_mul] using
        (pathPeriodGroup path).zsmul_mem hleast.2.1 k
    have hsperiod : s ∈ pathPeriodGroup path := by
      simpa [s] using (pathPeriodGroup path).sub_mem hr hkperiod
    have hszero : s = 0 := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hspos
        exact (not_le_of_gt hslt) (hleast.2.2 s hspos hsperiod)
      · exact hsnonneg
    exact ⟨k, by dsimp [s] at hszero; linarith⟩
  · rintro ⟨k, rfl⟩
    simpa [zsmul_eq_mul] using
      (pathPeriodGroup path).zsmul_mem hleast.2.1 k

/-- A nonconstant continuous periodic path has a least positive period. -/
theorem leastPositivePeriod_exists
    {A B : IntervalMap} {a b : ℝ} {F : TwoScaleFoldData A B a b}
    (E : PeriodicTailExtension F) :
    ∃ period₀ : ℝ, IsLeastPositivePeriod E.path period₀ := by
  let S : AddSubgroup ℝ := pathPeriodGroup E.path
  have hSnontrivial : S ≠ ⊥ := by
    intro hS
    have hPzero : E.period = 0 := by
      have hPmem : E.period ∈ S := E.periodic_path
      rw [hS] at hPmem
      simpa using hPmem
    exact E.period_pos.ne' hPzero
  have hnonconstant : ¬ ∀ x y : ℝ, E.path x = E.path y := by
    intro hall
    obtain ⟨x, y, hxy⟩ := E.nonconstant_path
    exact hxy (hall x y)
  have hSnotDense : ¬ Dense (S : Set ℝ) := by
    intro hSdense
    apply hnonconstant
    intro x y
    let Z : Set ℝ := {r | E.path (x + r) = E.path x}
    have hZclosed : IsClosed Z := by
      exact isClosed_eq
        (E.continuous_path.comp (continuous_const.add continuous_id))
        continuous_const
    have hSZ : (S : Set ℝ) ⊆ Z := by
      intro r hr
      exact hr x
    have hyrClosure : y - x ∈ closure (S : Set ℝ) := by
      rw [hSdense.closure_eq]
      exact Set.mem_univ _
    have hyr : y - x ∈ Z := (closure_minimal hSZ hZclosed) hyrClosure
    change E.path (x + (y - x)) = E.path x at hyr
    simpa using hyr.symm
  have hleastExists :
      ∃ P₀ : ℝ, IsLeast {r : ℝ | r ∈ S ∧ 0 < r} P₀ := by
    by_contra hnone
    exact hSnotDense (S.dense_of_no_min hSnontrivial hnone)
  rcases hleastExists with ⟨P₀, ⟨hP₀mem, hP₀pos⟩, hleast⟩
  exact ⟨P₀, hP₀pos, hP₀mem,
    fun r hrpos hrmem => hleast ⟨hrmem, hrpos⟩⟩

/-- Eventual dilation equivariance makes the scaled least period another
period of the path. -/
private theorem scaledLeastPeriod_is_period
    {ψ : ℝ → I} {period r : ℝ} {T : IntervalMap}
    (hperiod : IsLeastPositivePeriod ψ period) (hr : 0 < r)
    (heventual : ∃ cutoff : ℝ,
      ∀ t : ℝ, cutoff ≤ t → ψ (r * t) = T (ψ t)) :
    r * period ∈ pathPeriodGroup ψ := by
  rcases heventual with ⟨cutoff, hreturn⟩
  change ∀ t : ℝ, ψ (t + r * period) = ψ t
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt ((r * cutoff - t) / period)
  have hNPbig : r * cutoff - t < (N : ℝ) * period :=
    (div_lt_iff₀ hperiod.1).mp hN
  let u : ℝ := (t + (N : ℝ) * period) / r
  have hu : cutoff ≤ u := by
    apply (le_div_iff₀ hr).mpr
    dsimp [u]
    nlinarith
  have huP : cutoff ≤ u + period :=
    hu.trans (le_add_of_nonneg_right hperiod.1.le)
  have hru : r * u = t + (N : ℝ) * period := by
    dsimp [u]
    field_simp
  have hlate : ψ (r * u + r * period) = ψ (r * u) := by
    calc
      ψ (r * u + r * period) = ψ (r * (u + period)) := by ring_nf
      _ = T (ψ (u + period)) := hreturn (u + period) huP
      _ = T (ψ u) := congrArg T (hperiod.2.1 u)
      _ = ψ (r * u) := (hreturn u hu).symm
  have hNPperiod : ∀ x : ℝ,
      ψ (x + (N : ℝ) * period) = ψ x := by
    simpa [nsmul_eq_mul] using
      (pathPeriodGroup ψ).nsmul_mem hperiod.2.1 N
  calc
    ψ (t + r * period) =
        ψ ((t + r * period) + (N : ℝ) * period) :=
      (hNPperiod (t + r * period)).symm
    _ = ψ ((t + (N : ℝ) * period) + r * period) := by ring_nf
    _ = ψ (r * u + r * period) := by rw [hru]
    _ = ψ (r * u) := hlate
    _ = ψ (t + (N : ℝ) * period) := by rw [hru]
    _ = ψ t := hNPperiod t

/--
An eventual dilation identity forces its dilation factor to be integral once
the path has been normalized by its least positive period.
-/
theorem dilation_scale_integral_of_eventual
    {ψ : ℝ → I} {period r : ℝ} {T : IntervalMap}
    (hperiod : IsLeastPositivePeriod ψ period) (hr : 0 < r)
    (heventual : ∃ cutoff : ℝ, ∀ t : ℝ, cutoff ≤ t → ψ (r * t) = T (ψ t)) :
    ∃ k : ℤ, r = (k : ℝ) := by
  have hscaledPeriod : r * period ∈ pathPeriodGroup ψ :=
    scaledLeastPeriod_is_period hperiod hr heventual
  obtain ⟨k, hk⟩ :=
    (pathPeriodGroup_eq_integer_multiples hperiod (r * period)).mp
      hscaledPeriod
  refine ⟨k, ?_⟩
  apply mul_right_cancel₀ hperiod.1.ne'
  exact hk

/--
Once the dilation factor is integral, periodicity moves every parameter into
the tail and turns an eventual dilation identity into a global one.
-/
theorem eventual_dilation_globalizes_of_integral_scale
    {ψ : ℝ → I} {period r : ℝ} {T : IntervalMap}
    (hperiod : IsLeastPositivePeriod ψ period)
    (hr_integral : ∃ k : ℤ, r = (k : ℝ))
    (heventual : ∃ cutoff : ℝ, ∀ t : ℝ, cutoff ≤ t → ψ (r * t) = T (ψ t)) :
    DilationSemiconjugates ψ r T := by
  obtain ⟨k, rfl⟩ := hr_integral
  rcases heventual with ⟨cutoff, hreturn⟩
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt ((cutoff - t) / period)
  have hNPbig : cutoff - t < (N : ℝ) * period :=
    (div_lt_iff₀ hperiod.1).mp hN
  have htlate : cutoff ≤ t + (N : ℝ) * period := by linarith
  have hNPperiod : ψ (t + (N : ℝ) * period) = ψ t := by
    have hmem := (pathPeriodGroup ψ).nsmul_mem hperiod.2.1 N
    simpa [pathPeriodGroup, nsmul_eq_mul] using hmem t
  have hkNPperiod :
      ψ ((k : ℝ) * t + (((k * (N : ℤ) : ℤ) : ℝ) * period)) =
        ψ ((k : ℝ) * t) := by
    have hmem :=
      (pathPeriodGroup ψ).zsmul_mem hperiod.2.1 (k * (N : ℤ))
    simpa [pathPeriodGroup, zsmul_eq_mul] using hmem ((k : ℝ) * t)
  calc
    ψ ((k : ℝ) * t) =
        ψ ((k : ℝ) * t + (((k * (N : ℤ) : ℤ) : ℝ) * period)) :=
      hkNPperiod.symm
    _ = ψ ((k : ℝ) * (t + (N : ℝ) * period)) := by
      congr 1
      push_cast
      ring
    _ = T (ψ (t + (N : ℝ) * period)) := hreturn _ htlate
    _ = T (ψ t) := congrArg T hNPperiod

/-- An eventual expanding dilation identity is global. -/
theorem dilationSemiconjugates_of_eventually
    {ψ : ℝ → I} {period r : ℝ} {T : IntervalMap}
    (hperiod : IsLeastPositivePeriod ψ period) (hr : 0 < r)
    (heventual : ∃ cutoff : ℝ, ∀ t : ℝ, cutoff ≤ t → ψ (r * t) = T (ψ t)) :
    DilationSemiconjugates ψ r T := by
  apply eventual_dilation_globalizes_of_integral_scale hperiod
  · exact dilation_scale_integral_of_eventual hperiod hr heventual
  · exact heventual

/-- The range of a nonconstant continuous periodic path is a nondegenerate closed interval. -/
structure PeriodicRangeInterval (ψ : ℝ → I) where
  interval : ClosedSubinterval
  range_eq : Set.range ψ = interval.carrier
  nondegenerate : interval.Nondegenerate

/-- Construct the closed interval which is the range of a periodic tail extension. -/
theorem periodicRangeInterval_exists
    {A B : IntervalMap} {a b : ℝ} {F : TwoScaleFoldData A B a b}
    (E : PeriodicTailExtension F) :
    Nonempty (PeriodicRangeInterval E.path) := by
  have hrangeFundamental :
      Set.range E.path = E.path '' Set.Icc (0 : ℝ) E.period := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      let k : ℤ := ⌊t / E.period⌋
      let s : ℝ := t - (k : ℝ) * E.period
      have hklo : (k : ℝ) ≤ t / E.period := Int.floor_le (t / E.period)
      have hkhi : t / E.period < (k : ℝ) + 1 :=
        Int.lt_floor_add_one (t / E.period)
      have hmullo : (k : ℝ) * E.period ≤ t :=
        (le_div_iff₀ E.period_pos).mp (by simpa [mul_comm] using hklo)
      have hmulhi : t < ((k : ℝ) + 1) * E.period :=
        (div_lt_iff₀ E.period_pos).mp hkhi
      have hsnonneg : 0 ≤ s := by dsimp [s]; linarith
      have hslt : s < E.period := by dsimp [s]; linarith
      refine ⟨s, ⟨hsnonneg, hslt.le⟩, ?_⟩
      have hkperiod : (k : ℝ) * E.period ∈ pathPeriodGroup E.path := by
        simpa [zsmul_eq_mul] using
          (pathPeriodGroup E.path).zsmul_mem E.periodic_path k
      have h := hkperiod s
      have harg : s + (k : ℝ) * E.period = t := by
        dsimp [s]
        ring
      rw [harg] at h
      exact h.symm
    · rintro ⟨t, _ht, rfl⟩
      exact ⟨t, rfl⟩
  have hcompact : IsCompact (Set.range E.path) := by
    rw [hrangeFundamental]
    exact isCompact_Icc.image E.continuous_path
  have hconnected : IsConnected (Set.range E.path) := by
    rw [hrangeFundamental]
    exact (isConnected_Icc E.period_pos.le).image E.path
      E.continuous_path.continuousOn
  have hrangeIcc : Set.range E.path =
      Set.Icc (sInf (Set.range E.path)) (sSup (Set.range E.path)) :=
    eq_Icc_of_connected_compact hconnected hcompact
  have hleftRight :
      sInf (Set.range E.path) ≤ sSup (Set.range E.path) := by
    have hne := hconnected.nonempty
    rw [hrangeIcc] at hne
    exact Set.nonempty_Icc.mp hne
  let J : ClosedSubinterval :=
    { left := sInf (Set.range E.path)
      right := sSup (Set.range E.path)
      left_le_right := hleftRight }
  have hnondegenerate : J.Nondegenerate := by
    change sInf (Set.range E.path) < sSup (Set.range E.path)
    apply lt_of_le_of_ne hleftRight
    intro hends
    obtain ⟨x, y, hxy⟩ := E.nonconstant_path
    have hx : E.path x ∈ Set.Icc
        (sInf (Set.range E.path)) (sSup (Set.range E.path)) := by
      rw [← hrangeIcc]
      exact ⟨x, rfl⟩
    have hy : E.path y ∈ Set.Icc
        (sInf (Set.range E.path)) (sSup (Set.range E.path)) := by
      rw [← hrangeIcc]
      exact ⟨y, rfl⟩
    have hxEq : E.path x = sInf (Set.range E.path) :=
      le_antisymm (by simpa [hends] using hx.2) hx.1
    have hyEq : E.path y = sInf (Set.range E.path) :=
      le_antisymm (by simpa [hends] using hy.2) hy.1
    exact hxy (hxEq.trans hyEq.symm)
  refine ⟨{
    interval := J
    range_eq := ?_
    nondegenerate := hnondegenerate }⟩
  simpa [J, ClosedSubinterval.carrier] using hrangeIcc

/-- A nonzero dilation semiconjugacy carries the path range onto itself. -/
theorem mapsOnto_periodicRange
    {ψ : ℝ → I} {r : ℝ} {T : IntervalMap}
    (hr : r ≠ 0) (hreturn : DilationSemiconjugates ψ r T)
    (R : PeriodicRangeInterval ψ) :
    MapsOntoSubinterval T R.interval := by
  rw [MapsOntoSubinterval, ← R.range_eq]
  ext y
  constructor
  · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨r * t, hreturn t⟩
  · rintro ⟨t, rfl⟩
    refine ⟨ψ (t / r), ⟨t / r, rfl⟩, ?_⟩
    rw [← hreturn]
    congr 1
    field_simp

/--
The complete bridge data required by the already-proved affine-lift theorem.
-/
structure GlobalPeriodicFoldData (A B : IntervalMap) (a b : ℝ) where
  path : ℝ → I
  period : ℝ
  unitSpeedPeriodic : IsUnitSpeedPeriodicSurjection path period
  return_A : DilationSemiconjugates path a A
  return_B : DilationSemiconjugates path b B

/--
Eventual periodicity and returned-power irreducibility produce an onto,
least-period, globally equivariant periodic fold.
-/
theorem globalPeriodicFoldData_of_eventuallyPeriodic
    {P Q A B : IntervalMap} {L : ℕ} {a b : ℝ}
    (hA : A = iterateMap P L) (hB : B = iterateMap Q L)
    (hirreducible : ReturnedPowersIrreducible P Q L)
    (F : TwoScaleFoldData A B a b)
    (heventual : EventuallyPeriodicOnRay F.ray) :
    Nonempty (GlobalPeriodicFoldData A B a b) := by
  obtain ⟨E⟩ := periodicTailExtension_exists F heventual
  obtain ⟨period₀, hperiod₀⟩ := leastPositivePeriod_exists E
  have hreturnA : DilationSemiconjugates E.path a A :=
    dilationSemiconjugates_of_eventually hperiod₀
      (zero_lt_one.trans F.one_lt_a)
      ⟨E.cutoff, E.eventually_return_A⟩
  have hreturnB : DilationSemiconjugates E.path b B :=
    dilationSemiconjugates_of_eventually hperiod₀
      (zero_lt_one.trans F.one_lt_b)
      ⟨E.cutoff, E.eventually_return_B⟩
  obtain ⟨R⟩ := periodicRangeInterval_exists E
  have hmapsA : MapsOntoSubinterval A R.interval :=
    mapsOnto_periodicRange (zero_lt_one.trans F.one_lt_a).ne' hreturnA R
  have hmapsB : MapsOntoSubinterval B R.interval :=
    mapsOnto_periodicRange (zero_lt_one.trans F.one_lt_b).ne' hreturnB R
  have hfull : R.interval.carrier = Set.univ :=
    hirreducible R.interval R.nondegenerate (by simpa [← hA] using hmapsA)
      (by simpa [← hB] using hmapsB)
  have honto : Surjective E.path := by
    intro y
    have hy : y ∈ R.interval.carrier := by rw [hfull]; exact Set.mem_univ y
    rw [← R.range_eq] at hy
    exact hy
  refine ⟨{
    path := E.path
    period := period₀
    unitSpeedPeriodic := ?_
    return_A := hreturnA
    return_B := hreturnB }⟩
  exact ⟨E.continuous_path, honto, hperiod₀.1, hperiod₀.2.1,
    hperiod₀.2.2, E.finitePieceOn⟩

/-! ## The proved terminal step -/

/-- An onto globally equivariant periodic fold forces a common fixed point. -/
theorem common_fixed_point_of_periodic_fold
    {P Q A B : IntervalMap} {L : ℕ}
    {C D a b period : ℝ} {ψ : ℝ → I}
    (hL : 0 < L)
    (hcomm : Function.Commute P Q)
    (hA : A = iterateMap P L)
    (hB : B = iterateMap Q L)
    (hC : 1 < C)
    (hD : 1 < D)
    (ha : a = C ^ L)
    (hb : b = D ^ L)
    (hPslopes : HasConstantAbsoluteSlope P C)
    (hQslopes : HasConstantAbsoluteSlope Q D)
    (hfold : IsUnitSpeedPeriodicSurjection ψ period)
    (hreturnA : DilationSemiconjugates ψ a A)
    (hreturnB : DilationSemiconjugates ψ b B) :
    HasCommonFixedPoint P Q := by
  obtain ⟨package⟩ := original_phase_affine_lifts
    hL hcomm hA hB hC hD ha hb hPslopes hQslopes hfold
      hreturnA hreturnB
  exact common_fixed_point_of_original_phase_package package

/--
Manuscript-facing periodic-fold theorem: an eventually periodic two-scale
fold for an irreducible returned pair gives a common fixed point.
-/
theorem common_fixed_point_of_eventually_periodic_twoScaleFold
    {P Q A B : IntervalMap} {L : ℕ} {C D a b : ℝ}
    (hL : 0 < L)
    (hcomm : Function.Commute P Q)
    (hA : A = iterateMap P L)
    (hB : B = iterateMap Q L)
    (hC : 1 < C)
    (hD : 1 < D)
    (ha : a = C ^ L)
    (hb : b = D ^ L)
    (hPslopes : HasConstantAbsoluteSlope P C)
    (hQslopes : HasConstantAbsoluteSlope Q D)
    (hirreducible : ReturnedPowersIrreducible P Q L)
    (F : TwoScaleFoldData A B a b)
    (heventual : EventuallyPeriodicOnRay F.ray) :
    HasCommonFixedPoint P Q := by
  obtain ⟨G⟩ := globalPeriodicFoldData_of_eventuallyPeriodic
    hA hB hirreducible F heventual
  exact common_fixed_point_of_periodic_fold
    hL hcomm hA hB hC hD ha hb hPslopes hQslopes
      G.unitSpeedPeriodic G.return_A G.return_B

end

end CommutingIntervalSimplified
