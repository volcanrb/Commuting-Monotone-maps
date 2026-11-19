import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Folding sheets and decoder shoulders

In the unfolded coordinate a shoulder is the interval `[β,B+1]`. Its final
unit interval represents the entire ray starting at the integer `B`, with
points identified precisely when their triangular-fold values agree.
-/

namespace CommutingIntervalSimplified.DecoderProjection

open Set
noncomputable section

/-- Distance to the even integers, with values in the closed unit interval. -/
def fold (t : ℝ) : ℝ := ‖(t : AddCircle (2 : ℝ))‖

theorem fold_mem (t : ℝ) : fold t ∈ Icc (0 : ℝ) 1 :=
  ⟨norm_nonneg _, by simpa [fold] using
    AddCircle.norm_le_half_period 2 (x := (t : AddCircle (2 : ℝ))) (by norm_num)⟩

theorem fold_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : fold x = x := by
  obtain ⟨h₀, h₁⟩ := hx
  rw [fold, (AddCircle.norm_coe_eq_abs_iff 2 (by norm_num)).mpr, abs_of_nonneg h₀]
  simpa [abs_of_nonneg h₀] using h₁

theorem fold_abs_sub_le (x y : ℝ) : |fold x - fold y| ≤ |x-y| := by
  refine (abs_norm_sub_norm_le _ _).trans ?_
  change ‖((x-y : ℝ) : AddCircle (2 : ℝ))‖ ≤ ‖x-y‖
  exact QuotientAddGroup.norm_mk_le_norm

theorem continuous_fold : Continuous fold :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    simpa [Real.dist_eq] using fold_abs_sub_le x y).continuous

theorem fold_even_translate (k : ℤ) (x : ℝ) : fold (2*k+x) = fold x := by
  have h : ((2*(k:ℝ) : ℝ) : AddCircle (2 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff 2).mpr ⟨k, by simp [zsmul_eq_mul, mul_comm]⟩
  simp [fold, h]

theorem fold_neg (x : ℝ) : fold (-x) = fold x := by
  simp [fold]

/-- Every real coordinate is an even translate of a signed folded coordinate. -/
theorem exists_even_translate (x : ℝ) :
    ∃ k : ℤ, x = 2*k + fold x ∨ x = 2*k - fold x := by
  let k := round ((2:ℝ)⁻¹*x)
  have h : fold x = |x - (k:ℝ)*2| := AddCircle.norm_eq 2
  refine ⟨k, ?_⟩
  rcases le_total 0 (x-(k:ℝ)*2) with hp | hn
  · left; rw [h, abs_of_nonneg hp]; ring
  · right; rw [h, abs_of_nonpos hn]; ring

/-- Changing to a folded representative preserves the fold after any integral shift. -/
theorem fold_sub_int_fold (x : ℝ) (b : ℤ) :
    fold (fold x-b) = fold (x-b) := by
  obtain ⟨k, hk | hk⟩ := exists_even_translate x
  · conv_rhs => rw [show x-b = 2*k + (fold x-b) by linarith]
    rw [fold_even_translate]
  · have h : x-b = 2*((k-b:ℤ):ℝ) + -(fold x-b) := by push_cast; linarith
    rw [h, fold_even_translate, fold_neg]

/-- The representative of `u` on the sheet beginning at the integer `b`. -/
def onSheet (b : ℤ) (u : ℝ) : ℝ := b + fold (u-b)

theorem onSheet_mem (b : ℤ) (u : ℝ) :
    onSheet b u ∈ Icc (b : ℝ) (b+1) := by
  obtain ⟨hl, hu⟩ := fold_mem (u-b)
  constructor <;> dsimp [onSheet] <;> linarith

theorem onSheet_eq_self {b : ℤ} {u : ℝ} (hu : u ∈ Icc (b : ℝ) (b+1)) :
    onSheet b u = u := by
  have h : u-b ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rw [onSheet, fold_eq_self h]; ring

theorem onSheet_fold (b : ℤ) (u : ℝ) : onSheet b (fold u) = onSheet b u := by
  simp [onSheet, fold_sub_int_fold]

theorem fold_onSheet (b : ℤ) (u : ℝ) : fold (onSheet b u) = fold u := by
  have h := fold_sub_int_fold (u-b) (-b)
  simpa [onSheet, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

theorem onSheet_dist_le (b : ℤ) (u v : ℝ) :
    |onSheet b u - onSheet b v| ≤ |u-v| := by
  simpa [onSheet, add_sub_add_left_eq_sub, sub_sub_sub_cancel_right] using
    fold_abs_sub_le (u-b) (v-b)

theorem sheet_isometry {b : ℤ} {u v : ℝ}
    (hu : u ∈ Icc (b:ℝ) (b+1)) (hv : v ∈ Icc (b:ℝ) (b+1)) :
    |fold u - fold v| = |u-v| := by
  apply le_antisymm (fold_abs_sub_le u v)
  simpa only [onSheet_fold, onSheet_eq_self hu, onSheet_eq_self hv] using
    onSheet_dist_le b (fold u) (fold v)

/-- The ray quotient in unfolded shoulder coordinates. It also extends to the
left of the initial mark by the identity. -/
def quotient (b : ℤ) (t : ℝ) : ℝ := if t < b then t else onSheet b t

theorem quotient_fix {b : ℤ} {t : ℝ} (ht : t ≤ b+1) : quotient b t = t := by
  by_cases h : t < b
  · simp [quotient, h]
  · simp [quotient, h, onSheet_eq_self ⟨le_of_not_gt h, ht⟩]

theorem quotient_tail {b : ℤ} {t : ℝ} (ht : (b:ℝ) ≤ t) :
    quotient b t = onSheet b t := if_neg (not_lt.mpr ht)

theorem fold_quotient (b : ℤ) (t : ℝ) : fold (quotient b t) = fold t := by
  by_cases h : t < b <;> simp [quotient, h, fold_onSheet]

theorem quotient_mem {β : ℝ} {b : ℤ} (hβ : β ≤ b) {t : ℝ} (ht : β ≤ t) :
    quotient b t ∈ Icc β (b+1) := by
  rcases lt_or_ge t (b:ℝ) with h | h
  · simpa [quotient, h] using And.intro ht (show t ≤ b+1 by linarith)
  · rw [quotient_tail h]
    exact ⟨hβ.trans (onSheet_mem b t).1, (onSheet_mem b t).2⟩

theorem quotient_preimage_before_tail {b : ℤ} {t u : ℝ} (hu : u < b) :
    quotient b t = u ↔ t = u := by
  rcases lt_or_ge t (b:ℝ) with h | h
  · simp [quotient, h]
  · rw [quotient_tail h]
    exact iff_of_false (ne_of_gt (hu.trans_le (onSheet_mem b t).1)) (ne_of_gt (hu.trans_le h))

theorem quotient_eq_on_tail {b : ℤ} {t u : ℝ} (ht : (b:ℝ) ≤ t) (hu : (b:ℝ) ≤ u) :
    quotient b t = quotient b u ↔ fold t = fold u := by
  constructor
  · intro h; simpa only [fold_quotient] using congrArg fold h
  · intro h
    rw [quotient_tail ht, quotient_tail hu, ← onSheet_fold b t, ← onSheet_fold b u, h]

theorem quotient_dist_le (b : ℤ) (x y : ℝ) :
    |quotient b x - quotient b y| ≤ |x-y| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm (quotient b y), abs_sub_comm y] using this y x (le_of_not_ge hxy)
  rcases lt_or_ge y (b:ℝ) with hy | hy
  · rw [quotient_fix (by linarith : x ≤ b+1), quotient_fix (by linarith : y ≤ b+1)]
  rcases lt_or_ge x (b:ℝ) with hx | hx
  · have hb := onSheet_mem b y
    have h := onSheet_dist_le b y b
    rw [onSheet_eq_self (b := b) (u := (b:ℝ)) ⟨le_rfl, by linarith⟩,
      abs_of_nonneg (sub_nonneg.mpr hb.1), abs_of_nonneg (sub_nonneg.mpr hy)] at h
    rw [quotient_fix (by linarith : x ≤ b+1), quotient_tail hy,
      abs_of_nonpos (by linarith [hb.1] : x-onSheet b y ≤ 0), abs_of_nonpos (by linarith : x-y ≤ 0)]
    linarith
  · simpa only [quotient_tail hx, quotient_tail hy] using onSheet_dist_le b x y

theorem continuous_quotient (b : ℤ) : Continuous (quotient b) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    simpa [Real.dist_eq] using quotient_dist_le b x y).continuous


/-- Shoulder descent for an unfolded ray map, after translation of its initial mark. -/
def descend (b : ℤ) (R : ℝ → ℝ) (t : ℝ) : ℝ := quotient b (R t)

theorem continuous_descend {R : ℝ → ℝ} (h : Continuous R) (b : ℤ) :
    Continuous (descend b R) := (continuous_quotient b).comp h

theorem descend_decoder {r R : ℝ → ℝ} (h : ∀ t, fold (R t) = r (fold t)) (b : ℤ)
    (t : ℝ) : fold (descend b R t) = r (fold t) := (fold_quotient b _).trans (h t)

/-- Taking the intermediate shoulder quotient before applying a second ray
map preserves the final result. This holds even for unreduced ray coordinates. -/
theorem descend_comp {b c : ℤ} {S s : ℝ → ℝ} (R : ℝ → ℝ)
    (htail : ∀ x : ℝ, b ≤ x → c ≤ S x)
    (hfold : ∀ x, fold (S x) = s (fold x)) :
    descend c S ∘ descend b R = descend c (S ∘ R) := by
  funext t
  change quotient c (S (quotient b (R t))) = quotient c (S (R t))
  rcases lt_or_ge (R t) (b:ℝ) with h | h
  · rw [quotient_fix (by linarith : R t ≤ b+1)]
  · apply (quotient_eq_on_tail (htail _ (by rw [quotient_tail h]; exact (onSheet_mem b _).1))
      (htail _ h)).mpr
    rw [hfold, hfold, fold_quotient]

/-- The even translation attached to two successive initial marks composes
with the second degree. -/
theorem translated_comp {H K : ℝ → ℝ} {d m n : ℤ}
    (hK : ∀ (x : ℝ) (k : ℤ), K (x + 2*k) = K x + 2*d*k) (t : ℝ) :
    K (H t-2*m)-2*n = K (H t)-2*((n+d*m:ℤ):ℝ) := by
  have h := hK (H t-2*m) m
  rw [sub_add_cancel] at h
  push_cast
  linarith

theorem translated_decoder {r H : ℝ → ℝ} (h : ∀ t, fold (H t) = r (fold t)) (m : ℤ) :
    ∀ t, fold (H t-2*m) = r (fold t) := by
  intro t
  have eqn : H t-2*m = 2*((-m:ℤ):ℝ)+H t := by push_cast; ring
  rw [eqn, fold_even_translate, h]

/-- Endpoint verification in unfolded coordinates. The final fold value
uniquely determines its point in the last unit interval. -/
theorem descend_endpoints {b c : ℤ} {β γ : ℝ} {R : ℝ → ℝ}
    (hγ : γ ≤ c) (hstart : R β = γ) (htail : c ≤ R (b+1))
    (hend : fold (R (b+1)) = fold (c+1)) :
    descend c R β = γ ∧ descend c R (b+1) = c+1 := by
  constructor
  · change quotient c (R β) = γ
    rw [hstart, quotient_fix (by linarith : γ ≤ c+1)]
  · change quotient c (R (b+1)) = _
    have h := (quotient_eq_on_tail htail (show (c:ℝ) ≤ c+1 by linarith)).mpr hend
    rwa [quotient_fix (b := c) le_rfl] at h

/-- A shoulder of width at most `1/12` has a parameter interval of length at
least one, so the affine return to physical coordinates contracts by `1/12`. -/
theorem physical_shoulder_bound {b : ℤ} {β slope offset x y δ : ℝ}
    (hβ : β ≤ b) (hwidth : |slope| * (b+1-β) ≤ 1/12) (hδ : |x-y| ≤ δ) :
    |(offset+slope*quotient b x)-(offset+slope*quotient b y)| ≤ (1/12)*δ := by
  have hs : |slope| ≤ 1/12 := by nlinarith [mul_nonneg (abs_nonneg slope) (sub_nonneg.mpr hβ)]
  have he : (offset+slope*quotient b x)-(offset+slope*quotient b y) =
      slope*(quotient b x-quotient b y) := by ring
  rw [he, abs_mul]
  exact mul_le_mul hs ((quotient_dist_le b x y).trans hδ) (abs_nonneg _) (by norm_num)

/-! ## Canonical unfoldings -/

/-- The data at all lifted integer vertices. The finer cell and core endpoint
conditions of admissibility imply this condition. -/
def VertexAgreement (d : ℤ) (r : ℝ → ℝ) : Prop :=
  ∀ (t : ℝ) (k : ℤ), d*t = k → r (fold t) = fold (d*t)

/-- Lift a folded value onto the integer sheet containing its dilated input. -/
def unfoldMap (d : ℤ) (r : ℝ → ℝ) (t : ℝ) : ℝ := onSheet ⌊d*t⌋ (r (fold t))

private theorem floor_sheet (x : ℝ) : x ∈ Icc (⌊x⌋:ℝ) (⌊x⌋+1) :=
  ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩

theorem unfoldMap_vertex {d : ℤ} {r : ℝ → ℝ} {t : ℝ}
    (ht : r (fold t) = fold (d*t)) : unfoldMap d r t = d*t := by
  rw [unfoldMap, ht, onSheet_fold, onSheet_eq_self (floor_sheet _)]

theorem unfoldMap_on_sheet {d b : ℤ} {r : ℝ → ℝ} (hv : VertexAgreement d r)
    {t : ℝ} (ht : d*t ∈ Icc (b:ℝ) (b+1)) :
    unfoldMap d r t = onSheet b (r (fold t)) := by
  rcases lt_or_eq_of_le ht.2 with hl | he
  · rw [unfoldMap, Int.floor_eq_iff.mpr ⟨ht.1, hl⟩]
  · have h := hv t (b+1) (by exact_mod_cast he)
    rw [unfoldMap_vertex h, h, onSheet_fold, onSheet_eq_self ht]

theorem unfoldMap_in_sheet {d b : ℤ} {r : ℝ → ℝ} (hv : VertexAgreement d r)
    {t : ℝ} (ht : d*t ∈ Icc (b:ℝ) (b+1)) : unfoldMap d r t ∈ Icc (b:ℝ) (b+1) := by
  rw [unfoldMap_on_sheet hv ht]
  exact onSheet_mem _ _

theorem fold_unfoldMap {d : ℤ} {r : ℝ → ℝ} (hr : MapsTo r (Icc 0 1) (Icc 0 1))
    (t : ℝ) : fold (unfoldMap d r t) = r (fold t) := by
  rw [unfoldMap, fold_onSheet, fold_eq_self (hr (fold_mem t))]

/-- Admissibility on a projected cell, core, or shoulder places the lift in
that very piece. Each dilated piece is contained in a single integer sheet. -/
theorem unfoldMap_mem_piece {d b : ℤ} {r : ℝ → ℝ} (hv : VertexAgreement d r)
    {piece : Set ℝ} (hpiece : piece ⊆ Icc (b:ℝ) (b+1)) {t : ℝ}
    (ht : d*t ∈ piece) (hr : r (fold t) ∈ fold '' piece) :
    unfoldMap d r t ∈ piece := by
  obtain ⟨y, hy, he⟩ := hr
  rwa [unfoldMap_on_sheet hv (hpiece ht), ← he, onSheet_fold, onSheet_eq_self (hpiece hy)]

/-- The unfolded function is uniquely determined by its folded values and
the requirement to remain in the prescribed sheets. -/
theorem unfoldMap_unique {d : ℤ} {H r : ℝ → ℝ}
    (hfold : ∀ t, fold (H t) = r (fold t))
    (hsheet : ∀ t : ℝ, H t ∈ Icc (⌊d*t⌋:ℝ) (⌊d*t⌋+1)) : H = unfoldMap d r := by
  funext t
  rw [unfoldMap, ← hfold, onSheet_fold, onSheet_eq_self (hsheet _)]

theorem continuous_unfoldMap {d : ℤ} {r : ℝ → ℝ} (hv : VertexAgreement d r)
    (hr : ContinuousOn r (Icc 0 1)) : Continuous (unfoldMap d r) := by
  let sheets (b : ℤ) := Icc (b:ℝ) (b+1)
  have hsheet : LocallyFinite sheets := by
    apply locallyFinite_Icc_of_tendsto tendsto_intCast_atTop_atTop
    exact Filter.tendsto_atBot_add_const_right _ _ (tendsto_intCast_atBot_iff.mpr Filter.tendsto_id)
  let dilate (t : ℝ) : ℝ := d*t
  have hd : Continuous dilate := continuous_const.mul continuous_id
  apply (hsheet.preimage_continuous hd).continuous
  · apply eq_univ_of_forall
    intro t
    exact mem_iUnion.mpr ⟨⌊d*t⌋, floor_sheet _⟩
  · intro b; exact isClosed_Icc.preimage hd
  · intro b
    have hc : Continuous (fun t => r (fold t)) :=
      continuousOn_univ.mp (hr.comp continuous_fold.continuousOn fun x _ => fold_mem x)
    have hlocal : Continuous (fun t => onSheet b (r (fold t))) :=
      continuous_const.add (continuous_fold.comp (hc.sub continuous_const))
    exact hlocal.continuousOn.congr fun t ht => unfoldMap_on_sheet hv ht

/-- Pointwise isometry, including both endpoints of every sheet. -/
theorem unfoldMap_distance {d : ℤ} {r s : ℝ → ℝ}
    (hr : MapsTo r (Icc 0 1) (Icc 0 1)) (hs : MapsTo s (Icc 0 1) (Icc 0 1)) (t : ℝ) :
    |unfoldMap d r t - unfoldMap d s t| = |r (fold t) - s (fold t)| := by
  rw [← fold_unfoldMap (d := d) hr t, ← fold_unfoldMap (d := d) hs t]
  exact (sheet_isometry (onSheet_mem _ _) (onSheet_mem _ _)).symm

theorem unfoldMap_sup_distance {d : ℤ} {r s : ℝ → ℝ}
    (hr : MapsTo r (Icc 0 1) (Icc 0 1)) (hs : MapsTo s (Icc 0 1) (Icc 0 1)) :
    sSup (range fun t => |unfoldMap d r t - unfoldMap d s t|) =
      sSup ((fun x => |r x - s x|) '' Icc 0 1) := by
  congr 1
  ext a
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨fold t, fold_mem t, (unfoldMap_distance hr hs t).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, by simpa only [fold_eq_self hx] using unfoldMap_distance (d := d) hr hs x⟩

theorem unfoldMap_translate (d : ℤ) {r : ℝ → ℝ} (hr : MapsTo r (Icc 0 1) (Icc 0 1))
    (hv : VertexAgreement d r) (t : ℝ) (k : ℤ) :
    unfoldMap d r (t+2*k) = unfoldMap d r t + 2*d*k := by
  let b : ℤ := ⌊d*t⌋
  have hdt : d*t ∈ Icc (b:ℝ) (b+1) := floor_sheet _
  have hshift : d*(t+2*k) ∈ Icc ((b+2*d*k:ℤ):ℝ) (((b+2*d*k:ℤ):ℝ)+1) := by
    constructor <;> push_cast <;> linarith [hdt.1, hdt.2]
  have h₁ := unfoldMap_in_sheet hv hshift
  have h₂ := unfoldMap_in_sheet hv hdt
  let offset := (2:ℝ)*d*k
  have h₂' : unfoldMap d r t + offset ∈ Icc ((b+2*d*k:ℤ):ℝ) (((b+2*d*k:ℤ):ℝ)+1) := by
    constructor <;> push_cast <;> dsimp [offset] <;> linarith [h₂.1, h₂.2]
  have hfold : fold (unfoldMap d r (t+2*k)) = fold (unfoldMap d r t + offset) := by
    have he : unfoldMap d r t + offset = 2*((d*k:ℤ):ℝ)+unfoldMap d r t := by
      dsimp [offset]; push_cast; ring
    rw [he, fold_even_translate, fold_unfoldMap hr, fold_unfoldMap hr,
      add_comm t, fold_even_translate]
  have hd := sheet_isometry h₁ h₂'
  rw [hfold, sub_self, abs_zero, eq_comm, abs_eq_zero, sub_eq_zero] at hd
  exact hd

/-! ## The regular subdivision into cells, cores and shoulders

A cell at grade `v` has three equal pieces. Hence in unfolded coordinates
these pieces are exactly the closed mesh intervals of density `12 * M v`.
-/

/-- Lifted coarse piece with endpoints `i/m` and `(i+1)/m`, for positive `m`. -/
def mesh (m i : ℤ) : Set ℝ := {x | (m:ℝ)*x ∈ Icc (i:ℝ) (i+1)}

theorem mesh_subset_sheet {m : ℤ} (hm : 0 < m) (i : ℤ) :
    mesh m i ⊆ Icc ((i/m:ℤ):ℝ) (((i/m:ℤ):ℝ)+1) := by
  intro x hx
  have hdiv := Int.emod_add_mul_ediv i m
  have h₁ : m * (i/m) ≤ i := by linarith [Int.emod_nonneg i (ne_of_gt hm)]
  have h₂ : i+1 ≤ m*(i/m+1) := by
    have hmod : i%m+1 ≤ m := by have := Int.emod_lt_of_pos i hm; omega
    nlinarith
  have h₁' : (m:ℝ)*((i/m:ℤ):ℝ) ≤ i := by exact_mod_cast h₁
  have h₂' : (i:ℝ)+1 ≤ (m:ℝ)*(((i/m:ℤ):ℝ)+1) := by exact_mod_cast h₂
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  exact ⟨(le_of_mul_le_mul_left (h₁'.trans hx.1) hm'),
    (le_of_mul_le_mul_left (hx.2.trans h₂') hm')⟩

/-- The real-line expression of endpoint agreement and preservation of the folded
cells, cores, and shoulders of a uniform grid. Real representatives need only
be continuous and interval-valued on `[0,1]`. -/
structure GridAdmissible (m d : ℤ) (r : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn r (Icc 0 1)
  mapsTo : MapsTo r (Icc 0 1) (Icc 0 1)
  vertex : ∀ (t : ℝ) (i : ℤ), m*(d*t) = i → r (fold t) = fold (d*t)
  piece : ∀ (t : ℝ) (i : ℤ), d*t ∈ mesh m i → r (fold t) ∈ fold '' mesh m i

namespace GridAdmissible

variable {m d : ℤ} {r : ℝ → ℝ} (h : GridAdmissible m d r)

include h in
theorem unit_vertices : VertexAgreement d r := by
  intro t i ht
  apply h.vertex t (m*i); push_cast; rw [ht]

include h in
theorem lift_piece (hm : 0 < m) {t : ℝ} {i : ℤ} (ht : d*t ∈ mesh m i) :
    unfoldMap d r t ∈ mesh m i :=
  unfoldMap_mem_piece h.unit_vertices (mesh_subset_sheet hm i) ht (h.piece t i ht)

include h in
theorem lift_vertex {t : ℝ} {i : ℤ} (ht : m*(d*t) = i) :
    unfoldMap d r t = d*t := unfoldMap_vertex (h.vertex t i ht)

include h in
/-- Even when an admissible map reverses direction inside a piece, its lift
cannot take a later point back past an earlier vertex. -/
theorem lift_ge_vertex (hm : 0 < m) (hd : 0 < d) {z t : ℝ}
    {i : ℤ} (hz : m*(d*z) = i) (ht : z ≤ t) : d*z ≤ unfoldMap d r t := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hzt : (i:ℝ) ≤ m*(d*t) := by
    rw [← hz]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hd'.le) hm'.le
  have hi := Int.le_floor.mpr hzt
  have hy := h.lift_piece hm (i := ⌊m*(d*t)⌋) (t := t) (floor_sheet _)
  apply le_of_mul_le_mul_left _ hm'
  rw [hz]
  exact le_trans (by exact_mod_cast hi) hy.1

/-- Forgetting subdivision vertices gives an admissible map at any coarser
mesh whose density divides the original density. -/
theorem coarsen {a : ℤ} (ha : 0 < a) (hf : GridAdmissible (a*m) d r) :
    GridAdmissible m d r where
  continuousOn := hf.continuousOn
  mapsTo := hf.mapsTo
  vertex t i hi := hf.vertex t (a*i) (by push_cast; rw [mul_assoc, hi])
  piece t i ht := by
    rcases lt_or_eq_of_le ht.2 with hu | hu
    · let j := ⌊(a:ℝ) * ((m:ℝ)*(d*t))⌋
      have ha' : (0:ℝ) < a := by exact_mod_cast ha
      have hj : d*t ∈ mesh (a*m) j := by
        simpa only [mesh, mem_setOf_eq, Int.cast_mul, mul_assoc] using floor_sheet ((a:ℝ)*((m:ℝ)*(d*t)))
      obtain ⟨y, hy, he⟩ := hf.piece t j hj
      refine ⟨y, ?_, he⟩
      have hlow : (a*i:ℤ) ≤ j := by
        apply Int.le_floor.mpr
        push_cast; exact mul_le_mul_of_nonneg_left ht.1 ha'.le
      have hhigh : j < a*(i+1) := by
        apply Int.floor_lt.mpr
        push_cast; exact mul_lt_mul_of_pos_left hu ha'
      have hl : (a:ℝ)*i ≤ j := by exact_mod_cast hlow
      have hu' : (j:ℝ)+1 ≤ (a:ℝ)*(i+1) := by exact_mod_cast (show j+1 ≤ a*(i+1) by omega)
      have hy' : (a:ℝ)*((m:ℝ)*y) ∈ Icc (j:ℝ) (j+1) := by
        simpa only [mesh, mem_setOf_eq, Int.cast_mul, mul_assoc] using hy
      exact ⟨le_of_mul_le_mul_left (hl.trans hy'.1) ha', le_of_mul_le_mul_left (hy'.2.trans hu') ha'⟩
    · have hi : (↑(a*m):ℝ)*(d*t) = (a*(i+1):ℤ) := by
        push_cast; rw [mul_assoc, hu]
      exact ⟨d*t, ht, (hf.vertex t _ hi).symm⟩

end GridAdmissible

/-- Folding before dilation by an integer does not change the final folded value. -/
theorem fold_mul_fold (d : ℤ) (t : ℝ) : fold (d * fold t) = fold (d*t) := by
  obtain ⟨k, ht | ht⟩ := exists_even_translate t
  · have he : d*t = 2*((d*k:ℤ):ℝ)+d*fold t := by
      push_cast; nlinarith only [congrArg (fun y : ℝ => (d:ℝ)*y) ht]
    rw [he, fold_even_translate]
  · have he : d*t = 2*((d*k:ℤ):ℝ)+ -(d*fold t) := by
      push_cast; nlinarith only [congrArg (fun y : ℝ => (d:ℝ)*y) ht]
    rw [he, fold_even_translate, fold_neg]

namespace GridAdmissible
variable {m d : ℤ} {r : ℝ → ℝ}

/-- Ordinary fold is admissible on every integer mesh. -/
theorem standard (m d : ℤ) : GridAdmissible m d (fun x => fold (d*x)) := by
  exact ⟨(continuous_fold.comp (continuous_const.mul continuous_id)).continuousOn,
    fun _ _ => fold_mem _, fun t _ _ => fold_mul_fold d t, fun t _ ht => ⟨d*t, ht, (fold_mul_fold d t).symm⟩⟩

/-- Composition respects all prescribed pieces and vertices. -/
theorem comp {e : ℤ} {s : ℝ → ℝ}
    (hs : GridAdmissible m e s) (hr : GridAdmissible (m*e) d r) :
    GridAdmissible m (e*d) (s ∘ r) where
  continuousOn := hs.continuousOn.comp hr.continuousOn hr.mapsTo
  mapsTo := hs.mapsTo.comp hr.mapsTo
  vertex t i hi := by
    have h₁ : (↑(m*e):ℝ)*(d*t) = i := by push_cast at hi ⊢; linarith
    have h₂ : (m:ℝ)*(e*(d*t)) = i := by push_cast at hi; linarith
    simp only [Function.comp_apply, hr.vertex t i h₁, hs.vertex _ i h₂, Int.cast_mul, mul_assoc]
  piece t i ht := by
    have h₁ : d*t ∈ mesh (m*e) i := by
      simpa only [mesh, mem_setOf_eq, Int.cast_mul, mul_assoc] using ht
    obtain ⟨y, hy, hy'⟩ := hr.piece t i h₁
    have h₂ : (e:ℝ)*y ∈ mesh m i := by
      simpa only [mesh, mem_setOf_eq, Int.cast_mul, mul_assoc] using hy
    simpa only [Function.comp_apply, ← hy'] using hs.piece y i h₂

/-- The canonical lift of a composite is the composite of its canonical lifts. -/
theorem unfoldMap_comp {e : ℤ} {s : ℝ → ℝ} (hm : 0 < m) (he : 0 < e)
    (hs : GridAdmissible m e s) (hr : GridAdmissible (m*e) d r) :
    unfoldMap (e*d) (s ∘ r) = unfoldMap e s ∘ unfoldMap d r := by
  symm
  apply unfoldMap_unique
  · intro t; simp only [Function.comp_apply, fold_unfoldMap hs.mapsTo, fold_unfoldMap hr.mapsTo]
  · intro t
    have hcoarse : GridAdmissible e d r := coarsen hm hr
    have h₁ : d*t ∈ mesh e ⌊↑(e*d)*t⌋ := by
      simpa only [mesh, mem_setOf_eq, Int.cast_mul, mul_assoc] using floor_sheet ((↑(e*d):ℝ)*t)
    exact unfoldMap_in_sheet hs.unit_vertices (hcoarse.lift_piece he h₁)

end GridAdmissible

end
end CommutingIntervalSimplified.DecoderProjection
