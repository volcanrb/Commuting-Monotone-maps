import CommutingIntervalSimplified.FiniteReturnConstructionGeometry
import CommutingIntervalSimplified.GradedCells
import CommutingIntervalSimplified.GradedShoulderDecoders

/-!
# The folded grid at a grade

Both CRT residues and the quarter number are retained in the label. On
folding, the increasing blocks occupy grid positions congruent to 0 through 3
modulo 8; the decreasing blocks occupy positions congruent to 4 through 7.
This distinguishes cells even across a fold turning point.
-/

namespace CommutingIntervalSimplified.GradedGeometry

open Function Set GradedCells
open scoped NNReal

noncomputable section

def M (v : Grade) : ℕ := 5^v.1 * 7^v.2

theorem M_pos (v : Grade) : 0 < M v := by unfold M; positivity

instance (v : Grade) : NeZero (M v) := ⟨(M_pos v).ne'⟩

def quarterNumber : Quarter ≃ Fin 4 where
  toFun
    | .left => 0
    | .second => 1
    | .third => 2
    | .right => 3
  invFun k := ![Quarter.left, .second, .third, .right] k
  left_inv q := by cases q <;> rfl
  right_inv k := by fin_cases k <;> rfl

def residues (v : Grade) : Fin (M v) ≃ ZMod (5^v.1) × ZMod (7^v.2) :=
  (ZMod.finEquiv (M v)).toEquiv.trans
    (ZMod.chineseRemainder (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _
      (by decide : Nat.Coprime 5 7)))).toEquiv

def residue {v : Grade} (J : Cell v) : Fin (M v) := (residues v).symm (J.five, J.seven)

private def labelEquiv (v : Grade) : Cell v ≃ Fin (M v) × Fin 4 where
  toFun J := (residue J, quarterNumber J.quarter)
  invFun p := ⟨quarterNumber.symm p.2, ((residues v) p.1).1, ((residues v) p.1).2⟩
  left_inv J := by
    apply Cell.ext <;> simp [residue]
  right_inv p := by simp [residue]

def forward {v : Grade} (J : Cell v) : Prop := 2*(residue J).val < M v

instance {v : Grade} (J : Cell v) : Decidable (forward J) := inferInstanceAs (Decidable (2*(residue J).val < M v))

private def gridPos {N : ℕ} (p : Fin N × Fin 4) : Fin (4*N) :=
  ⟨if 2*p.1.val < N then 8*p.1.val + p.2.val else 8*N-1-(8*p.1.val+p.2.val), by
    have := p.1.isLt
    have := p.2.isLt
    split <;> omega⟩

private theorem gridPos_injective (N : ℕ) : Injective (gridPos (N := N)) := by
  rintro ⟨k,q⟩ ⟨l,r⟩ he
  have he' := congrArg Fin.val he
  change (if 2*k.val < N then 8*k.val+q.val else 8*N-1-(8*k.val+q.val)) =
    (if 2*l.val < N then 8*l.val+r.val else 8*N-1-(8*l.val+r.val)) at he'
  have := k.isLt
  have := q.isLt
  have := l.isLt
  have := r.isLt
  apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> split at he' <;> split at he' <;> omega

/-- Bijection between the quarter/CRT labels and the cells in physical order. -/
def indexEquiv (v : Grade) : Cell v ≃ Fin (4*M v) :=
  (labelEquiv v).trans <| Equiv.ofBijective gridPos <|
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨gridPos_injective _, by simp [Nat.mul_comm]⟩

theorem index_val {v : Grade} (J : Cell v) :
    (indexEquiv v J).val = if forward J then 8*(residue J).val + (quarterNumber J.quarter).val
      else 8*M v-1-(8*(residue J).val+(quarterNumber J.quarter).val) := rfl

private def orient {v : Grade} (J : Cell v) (u : I) : I :=
  if forward J then u else unitInterval.symm u

private theorem orient_invol {v : Grade} (J : Cell v) (u : I) : orient J (orient J u) = u := by
  by_cases h : forward J <;> simp [orient, h]

private theorem orient_cont {v : Grade} (J : Cell v) : Continuous (orient J) := by
  change Continuous (fun u => if forward J then u else unitInterval.symm u)
  by_cases h : forward J
  · simpa only [if_pos h] using (continuous_id : Continuous (fun u : I => u))
  · simpa only [if_neg h] using unitInterval.continuous_symm

private theorem npos (v : Grade) : 0 < ((4*M v : ℕ) : ℝ) := by
  exact_mod_cast (Nat.mul_pos (by decide : 0 < 4) (M_pos v))

/-- Affine parametrization in the physical interval, accounting for orientation. -/
def chart {v : Grade} (J : Cell v) (u : I) : I :=
  ⟨((indexEquiv v J).val + (orient J u : ℝ)) / (4*M v : ℕ), by
    have hi : ((indexEquiv v J).val : ℝ)+1 ≤ (4*M v : ℕ) := by exact_mod_cast (indexEquiv v J).isLt
    exact ⟨div_nonneg (add_nonneg (Nat.cast_nonneg _) (orient J u).property.1) (npos v).le,
      (div_le_one (npos v)).mpr (by linarith [(orient J u).property.2])⟩⟩

theorem continuous_chart {v : Grade} (J : Cell v) : Continuous (chart J) :=
  Continuous.subtype_mk ((continuous_const.add (continuous_subtype_val.comp (orient_cont J))).div_const _) _

def physicalCell {v : Grade} (J : Cell v) : Set I := range (chart J)

/-- The chart inverse, clamped continuously at the outer endpoints. -/
def coord {v : Grade} (J : Cell v) (x : I) : I :=
  orient J (projIcc 0 1 zero_le_one (((4*M v : ℕ) : ℝ) * x - (indexEquiv v J).val))

theorem continuous_coord {v : Grade} (J : Cell v) : Continuous (coord J) :=
  (orient_cont J).comp (continuous_projIcc.comp (by fun_prop))

theorem coord_chart {v : Grade} (J : Cell v) (u : I) : coord J (chart J u) = u := by
  have hc : ((4*M v : ℕ) : ℝ) * (chart J u : ℝ) - (indexEquiv v J).val = orient J u := by
    dsimp only [chart]
    rw [mul_div_cancel₀ _ (npos v).ne']
    ring
  unfold coord
  rw [hc, projIcc_of_mem (h := zero_le_one) (orient J u).property]
  exact orient_invol J u

theorem chart_injective {v : Grade} (J : Cell v) : Injective (chart J) :=
  (show LeftInverse (coord J) (chart J) from coord_chart J).injective

theorem cell_closed {v : Grade} (J : Cell v) : IsClosed (physicalCell J) :=
  (isCompact_range (continuous_chart J)).isClosed

theorem physicalCell_eq {v : Grade} (J : Cell v) :
    physicalCell J = EqualCell.cell (indexEquiv v J) := by
  ext x
  let N : ℝ := (4*M v : ℕ)
  let j : ℝ := (indexEquiv v J).val
  change (∃ u, chart J u = x) ↔ j ≤ N*(x : ℝ) ∧ N*(x : ℝ) ≤ j+1
  have hN : N ≠ 0 := (npos v).ne'
  constructor
  · rintro ⟨u, rfl⟩
    change j ≤ N*((j+(orient J u : ℝ))/N) ∧ N*((j+(orient J u : ℝ))/N) ≤ j+1
    rw [mul_div_cancel₀ _ hN]
    constructor <;> linarith [(orient J u).property.1, (orient J u).property.2]
  · rintro ⟨hx, hy⟩
    let t : I := ⟨N*x-j, by constructor <;> linarith⟩
    refine ⟨orient J t, Subtype.ext ?_⟩
    change (j + (orient J (orient J t) : ℝ))/N = x
    rw [orient_invol]
    change (j + (N*(x:ℝ)-j))/N = x
    field_simp
    ring

theorem cover (v : Grade) (x : I) : ∃ J : Cell v, x ∈ physicalCell J := by
  obtain ⟨j,hj⟩ := EqualCell.cover (Nat.mul_pos (by decide : 0 < 4) (M_pos v)) x
  exact ⟨(indexEquiv v).symm j, by simpa only [physicalCell_eq, Equiv.apply_symm_apply] using hj⟩

theorem residue_inj_coords {v : Grade} {J K : Cell v} (h : residue J = residue K) :
    J.five = K.five ∧ J.seven = K.seven := by
  have e := (residues v).symm.injective h
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

theorem chart_val {v : Grade} (J : Cell v) (x : I) :
    (chart J x : ℝ) = ((indexEquiv v J).val + (if forward J then (x : ℝ) else 1 - x)) /
      (4*M v : ℕ) := by
  by_cases h : forward J <;> simp only [chart, orient, h, if_true, if_false, unitInterval.coe_symm_eq]

/-- The affine physical chart agrees with formula (3.1) in unfolded coordinates. -/
theorem chart_eq_fold {v : Grade} (J : Cell v) (u : I) :
    (chart J u : ℝ) = DecoderProjection.fold
      ((2*(residue J).val + ((quarterNumber J.quarter).val + (u : ℝ))/4) / (M v : ℝ)) := by
  let t : ℝ := (2*(residue J).val + ((quarterNumber J.quarter).val + (u : ℝ))/4) / M v
  have hM : (M v : ℝ) ≠ 0 := by exact_mod_cast (M_pos v).ne'
  change (chart J u : ℝ) = DecoderProjection.fold t
  by_cases h : forward J
  · have ht : t = chart J u := by
      rw [chart_val, index_val, if_pos h, if_pos h]
      dsimp only [t]
      push_cast
      field_simp
      ring
    rw [ht, DecoderProjection.fold_eq_self (chart J u).property]
  · have hk := (residue J).isLt
    have hq := (quarterNumber J.quarter).isLt
    have h₁ : 1 ≤ 8 * M v := by omega
    have h₂ : 8*(residue J).val+(quarterNumber J.quarter).val ≤ 8*M v-1 := by omega
    have ht : t = 2*(1 : ℤ) + -(chart J u : ℝ) := by
      rw [chart_val, index_val, if_neg h, if_neg h, Nat.cast_sub h₂, Nat.cast_sub h₁]
      dsimp only [t]
      push_cast
      field_simp
      ring
    rw [ht, DecoderProjection.fold_even_translate, DecoderProjection.fold_neg,
      DecoderProjection.fold_eq_self (chart J u).property]

/-- Every chart scales distances by the reciprocal of the number of cells. -/
theorem chart_dist {v : Grade} (J : Cell v) (x y : I) :
    dist (chart J x) (chart J y) = dist x y / (4*M v : ℕ) := by
  change |(chart J x : ℝ)-(chart J y : ℝ)| = |(x : ℝ)-y| / _
  rw [chart_val, chart_val, ← sub_div, add_sub_add_left_eq_sub, abs_div,
    abs_of_pos (npos v)]
  by_cases h : forward J
  · simp [h]
  · simp only [if_neg h, sub_sub_sub_cancel_left, abs_sub_comm]

theorem chart_lip_one {v : Grade} (J : Cell v) : LipschitzWith 1 (chart J) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [chart_dist, NNReal.coe_one, one_mul]
  exact div_le_self (dist_nonneg) (by exact_mod_cast (show 1 ≤ 4*M v by nlinarith [M_pos v]))

/-- The central section contracts uniformly over the entire grid. -/
theorem section_lip {v : Grade} (J : Cell v) :
    LipschitzWith (1/12 : ℝ≥0) (chart J ∘ GradedShoulderDecoders.sectionCoord) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Function.comp_apply, Function.comp_apply, chart_dist]
  change |(1 + (x : ℝ))/3 - (1 + (y:ℝ))/3| / _ ≤ _ * |(x:ℝ)-y|
  rw [← sub_div, add_sub_add_left_eq_sub, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  apply (div_le_iff₀ (npos v)).mpr
  have hM : (1 : ℝ) ≤ M v := by exact_mod_cast M_pos v
  push_cast
  norm_num
  nlinarith [mul_nonneg (sub_nonneg.mpr hM) (abs_nonneg ((x:ℝ)-y))]

/-- A point interior to a chart belongs to no other closed cell. -/
theorem chart_interior_unique {v : Grade} {J K : Cell v} {u : I}
    (hu₀ : 0 < (u : ℝ)) (hu₁ : (u : ℝ) < 1) (hx : chart K u ∈ physicalCell J) : J = K := by
  rw [physicalCell_eq] at hx
  change ((indexEquiv v J).val : ℝ) ≤ ((4*M v : ℕ) : ℝ) * (chart K u : ℝ) ∧
    ((4*M v : ℕ) : ℝ) * (chart K u : ℝ) ≤ (indexEquiv v J).val+1 at hx
  rw [chart_val, mul_div_cancel₀ _ (npos v).ne'] at hx
  have h₀ : 0 < (if forward K then (u:ℝ) else 1-u) := by split <;> linarith
  have h₁ : (if forward K then (u:ℝ) else 1-u) < 1 := by split <;> linarith
  apply (indexEquiv v).injective
  apply Fin.ext
  apply Nat.le_antisymm
  · by_contra! ht
    have h : ((indexEquiv v K).val : ℝ) + 1 ≤ (indexEquiv v J).val := by exact_mod_cast ht
    linarith [hx.1]
  · by_contra! ht
    have h : ((indexEquiv v J).val : ℝ) + 1 ≤ (indexEquiv v K).val := by exact_mod_cast ht
    linarith [hx.2]

theorem section_unique {v : Grade} {J K : Cell v} {x : I} (hx : x ∈ physicalCell J)
    (hc : x ∈ range (chart K ∘ GradedShoulderDecoders.sectionCoord)) : J = K := by
  obtain ⟨u,rfl⟩ := hc
  apply chart_interior_unique (u := GradedShoulderDecoders.sectionCoord u) _ _ hx
  · change 0 < (1+(u:ℝ))/3
    linarith [u.2.1]
  · change (1+(u:ℝ))/3 < 1
    linarith [u.2.2]

theorem chart_coord {v : Grade} (J : Cell v) {x : I} (hx : x ∈ physicalCell J) :
    chart J (coord J x) = x := by
  obtain ⟨u, rfl⟩ := hx
  rw [coord_chart]

/-- A shared point has an endpoint parameter in each of its two charts. -/
theorem chart_shared_endpoint {v : Grade} {J K : Cell v} (hne : J ≠ K)
    {u w : I} (heq : chart J u = chart K w) :
    (u = leftEndpoint ∨ u = rightEndpoint) ∧ (w = leftEndpoint ∨ w = rightEndpoint) := by
  have endpoints {A B : Cell v} (hab : A ≠ B) {t y : I} (he : chart A t = chart B y) :
      t = leftEndpoint ∨ t = rightEndpoint := by
    by_contra! h
    have h₀ : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (fun e => h.1 (Subtype.ext e.symm))
    have h₁ : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun e => h.2 (Subtype.ext e))
    exact hab (chart_interior_unique h₀ h₁ ⟨y, he.symm⟩).symm
  exact ⟨endpoints hne heq, endpoints hne.symm heq.symm⟩

end
end CommutingIntervalSimplified.GradedGeometry
