import CommutingIntervalSimplified.Base
import CommutingIntervalSimplified.PolygonalBase
import CommutingIntervalSimplified.PeriodicPathRigidity
import CommutingIntervalSimplified.AffineCircle
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Affine circle lifts of a periodic fold

Constant-slope local geometry and periodic-path rigidity lift the original
interval maps to commuting integer-degree affine maps of the parameter
circle.  Reflection symmetry restricts their translations to zero or a half
turn, and the affine-circle parity theorem then gives a common physical fixed
point.
-/

namespace CommutingIntervalSimplified

open Function Set Filter Topology

noncomputable section

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
  obtain ⟨δ, hglobal⟩ := periodic_local_match_globalizes
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
    (hL : 0 < L) (hPQ : Function.Commute P Q)
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
    (hL : 0 < L) (hPQ : Function.Commute P Q)
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

end CommutingIntervalSimplified
