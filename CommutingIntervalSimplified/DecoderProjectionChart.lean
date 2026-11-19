import CommutingIntervalSimplified.DecoderProjectionShoulder
import CommutingIntervalSimplified.GradedShoulderDecoders

/-! # The projection update on a complete normalized cell

On each shoulder we change to the unfolded ray parameter, apply shoulder
descent, and undo the coarse parameterization. On the core we use the
projection of decoder targets in section coordinates. -/

namespace CommutingIntervalSimplified.DecoderProjection

open Set GradedShoulderDecoders
noncomputable section

/-- The shoulder used by the explicit graded decoder, with the identical last sheet. -/
def normalizedShoulder (side : Bool) (β : ℝ) : Shoulder where
  mark := β
  tail := threshold side β
  mark_le := le_threshold side β
  least z hz he := by
    rw [fold_int, fold_int] at he
    have h : z%2 = (threshold side β)%2 := by exact_mod_cast he
    cases side
    · have hp : z = 2*(z/2)+1 := by simp [threshold] at h; omega
      rw [hp] at hz ⊢
      exact threshold_le_odd (by simpa using hz)
    · have hp : z = 2*(z/2) := by simp [threshold] at h; omega
      rw [hp] at hz ⊢
      exact threshold_le_even (by simpa using hz)

namespace Shoulder

def length (J : Shoulder) : ℝ := J.tail+1-J.mark

theorem one_le_length (J : Shoulder) : 1 ≤ J.length := by
  dsimp [length]; linarith [J.mark_le]

theorem length_pos (J : Shoulder) : 0 < J.length := by linarith [J.one_le_length]

def toParameter (J : Shoulder) (u : ℝ) : ℝ := J.mark+u*J.length

def fromParameter (J : Shoulder) (t : ℝ) : ℝ := (t-J.mark)/J.length

@[simp] theorem toParameter_zero (J : Shoulder) : J.toParameter 0 = J.mark := by simp [toParameter]
@[simp] theorem toParameter_one (J : Shoulder) : J.toParameter 1 = J.tail+1 := by simp [toParameter, length]

@[simp] theorem fromParameter_start (J : Shoulder) : J.fromParameter J.mark = 0 := by simp [fromParameter]
@[simp] theorem fromParameter_end (J : Shoulder) : J.fromParameter (J.tail+1) = 1 := by
  change J.length/J.length = 1; exact div_self J.length_pos.ne'

@[simp] theorem to_fromParameter (J : Shoulder) (t : ℝ) : J.toParameter (J.fromParameter t) = t := by
  rw [toParameter, fromParameter, div_mul_cancel₀ _ J.length_pos.ne']; ring

theorem toParameter_mem {J : Shoulder} {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : J.toParameter u ∈ J.parameter := by
  constructor <;> dsimp [toParameter]
  · linarith [mul_nonneg hu.1 J.length_pos.le]
  · have h := mul_le_mul_of_nonneg_right hu.2 J.length_pos.le
    have he : J.mark+J.length = J.tail+1 := by simp [length]
    linarith

theorem fromParameter_mem {J : Shoulder} {t : ℝ} (ht : t ∈ J.parameter) : J.fromParameter t ∈ Icc (0:ℝ) 1 :=
  ⟨div_nonneg (sub_nonneg.mpr ht.1) J.length_pos.le, (div_le_one J.length_pos).mpr (by dsimp [length]; linarith [ht.2])⟩

end Shoulder

theorem shoulder_eq_fold_parameter (side : Bool) (β u : ℝ) :
    shoulder side β u = fold ((normalizedShoulder side β).toParameter u) := by
  dsimp [shoulder, normalizedShoulder, Shoulder.toParameter, Shoulder.length]
  congr 1; ring

theorem normalized_coreValue (side : Bool) (β : ℝ) :
    (normalizedShoulder side β).coreValue = if side then 1 else 0 := by
  have h := shoulder_eq_fold_parameter side β 1
  rw [Shoulder.toParameter_one] at h
  cases side
  · exact h.symm.trans (shoulder_one_left _)
  · exact h.symm.trans (shoulder_one_right _)

/-- All mark data for a full cell. A match determines its integer shifts uniquely. -/
structure ChartMatch (m d : ℤ) (β γ : Bool → ℝ) where
  shift : Bool → ℤ
  matched : ∀ s, ShoulderMatch m d (shift s) (normalizedShoulder s (β s)) (normalizedShoulder s (γ s))

namespace ChartMatch

variable {m d : ℤ} {β γ : Bool → ℝ} (P : ChartMatch m d β γ)
  {r : ℝ → ℝ} (hr : GridAdmissible m d r)

instance : Subsingleton (ChartMatch m d β γ) := ⟨by
  rintro ⟨p, hp⟩ ⟨q,hq⟩
  have he : p = q := by
    funext s
    have h₁ := (hp s).mark
    have h₂ := (hq s).mark
    exact_mod_cast (show ((p s):ℝ) = ((q s):ℝ) by linarith)
  cases he; rfl⟩

/-- The shoulder update in outer-to-inner coordinates on the unit interval. -/
def sideMap (P : ChartMatch m d β γ) (s : Bool) (r : ℝ → ℝ) (u : ℝ) : ℝ :=
  let J := normalizedShoulder s (β s)
  let K := normalizedShoulder s (γ s)
  K.fromParameter (theta K d (P.shift s) r (J.toParameter u))

include hr in
theorem continuous_sideMap (s : Bool) : Continuous (P.sideMap s r) := by
  have ht := ShoulderMatch.continuous (n := P.shift s) (K := normalizedShoulder s (γ s)) hr
  apply Continuous.div_const
  apply Continuous.sub _ continuous_const
  apply ht.comp
  exact continuous_const.add (continuous_id.mul continuous_const)

include hr in
theorem side_endpoints (hm : 0 < m) (hd : 0 < d) (ho : Odd d) (s : Bool) :
    P.sideMap s r 0 = 0 ∧ P.sideMap s r 1 = 1 := by
  have h := (P.matched s).endpoints hr hm hd ho
  simp [sideMap, h.1, h.2]

include hr in
theorem side_mem (hm : 0 < m) (hd : 0 < d) (s : Bool) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    P.sideMap s r u ∈ Icc (0:ℝ) 1 :=
  Shoulder.fromParameter_mem ((P.matched s).mapsTo hr hm hd (Shoulder.toParameter_mem hu))

include hr in
theorem side_decoder (s : Bool) (u : ℝ) : shoulder s (γ s) (P.sideMap s r u) = r (shoulder s (β s) u) := by
  rw [shoulder_eq_fold_parameter, sideMap, Shoulder.to_fromParameter, shoulder_eq_fold_parameter]
  apply ShoulderMatch.decoder hr

include hr in
theorem side_dist_le {s : ℝ → ℝ} (hs : GridAdmissible m d s) {δ : ℝ}
    (hδ : ∀ x ∈ Icc (0:ℝ) 1, |r x-s x| ≤ δ) (side : Bool) (x : ℝ) :
    |P.sideMap side r x-P.sideMap side s x| ≤ δ := by
  let J := normalizedShoulder side (β side)
  let K := normalizedShoulder side (γ side)
  let u := J.toParameter x
  change |(theta K d (P.shift side) r u-K.mark)/K.length - (theta K d (P.shift side) s u-K.mark)/K.length| ≤ _
  rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos K.length_pos, div_le_iff₀ K.length_pos]
  have h₁ := quotient_dist_le K.tail (rayMap d (P.shift side) r u) (rayMap d (P.shift side) s u)
  change |theta K d (P.shift side) r u - theta K d (P.shift side) s u| ≤ _ at h₁
  simp only [rayMap, sub_sub_sub_cancel_right, unfoldMap_distance hr.mapsTo hs.mapsTo] at h₁
  have hu := hδ (fold u) (fold_mem u)
  have hδ' := (abs_nonneg _).trans hu
  exact (h₁.trans hu).trans (le_mul_of_one_le_right hδ' K.one_le_length)

/-- The three formulas making up a projection on the full normalized cell.
The central fold merely extends its argument continuously outside the core. -/
def map (P : ChartMatch m d β γ) (r : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ≤ 1/3 then P.sideMap false r (3*u)/3
  else if 2/3 ≤ u then 1-P.sideMap true r (3*(1-u))/3
  else (1+r (fold (3*u-1)))/3

include hr in
private theorem generators_endpoints (ho : Odd d) : r 0 = 0 ∧ r 1 = 1 := by
  have h₀ := hr.unit_vertices 0 0 (by simp)
  have h₁ := hr.unit_vertices 1 d (by simp)
  have h : fold (d:ℝ) = 1 := by
    simpa [fold_eq_self (show (1:ℝ) ∈ Icc 0 1 by norm_num)] using fold_odd_dilation ho 1 0
  norm_num [fold_eq_self (show (0:ℝ) ∈ Icc 0 1 by norm_num),
    fold_eq_self (show (1:ℝ) ∈ Icc 0 1 by norm_num), h] at h₀ h₁
  exact ⟨h₀, h₁⟩

theorem map_left {u : ℝ} (hu : u ≤ 1/3) : P.map r u = P.sideMap false r (3*u)/3 := if_pos hu

theorem map_right {u : ℝ} (hu : 2/3 ≤ u) : P.map r u = 1-P.sideMap true r (3*(1-u))/3 := by
  rw [map, if_neg (by linarith), if_pos hu]

include hr in
theorem map_section (hm : 0 < m) (hd : 0 < d) (ho : Odd d)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    P.map r ((1+u)/3) = (1+r u)/3 := by
  rcases eq_or_lt_of_le hu.1 with he | hl
  · subst u
    norm_num [map, (P.side_endpoints hr hm hd ho false).2, (generators_endpoints hr ho).1]
  rcases eq_or_lt_of_le hu.2 with he | hh
  · subst u
    norm_num [map, (P.side_endpoints hr hm hd ho true).2, (generators_endpoints hr ho).2]
  · rw [map, if_neg (by linarith), if_neg (by linarith), show 3*((1+u)/3)-1 = u by ring, fold_eq_self hu]

include hr in
theorem continuous_map (hm : 0 < m) (hd : 0 < d) (ho : Odd d) : Continuous (P.map r) := by
  have hc : Continuous (fun t => r (fold t)) :=
    continuousOn_univ.mp (hr.continuousOn.comp continuous_fold.continuousOn fun x _ => fold_mem x)
  apply Continuous.if_le
  · exact ((P.continuous_sideMap hr false).comp (continuous_const.mul continuous_id)).div_const 3
  · apply Continuous.if_le
    · apply continuous_const.sub
      apply Continuous.div_const
      exact (P.continuous_sideMap hr true).comp (continuous_const.mul (continuous_const.sub continuous_id))
    · apply Continuous.div_const
      exact continuous_const.add (hc.comp ((continuous_const.mul continuous_id).sub continuous_const))
    · exact continuous_const
    · exact continuous_id
    · intro x hx
      change 2/3 = x at hx
      subst x
      norm_num [(P.side_endpoints hr hm hd ho true).2, fold_eq_self (show (1:ℝ) ∈ Icc 0 1 by norm_num),
        (generators_endpoints hr ho).2]
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    change x = 1/3 at hx
    subst x
    norm_num [(P.side_endpoints hr hm hd ho false).2, fold_eq_self (show (0:ℝ) ∈ Icc 0 1 by norm_num),
      (generators_endpoints hr ho).1]

include hr in
theorem map_zero (hm : 0 < m) (hd : 0 < d) (ho : Odd d) : P.map r 0 = 0 := by
  norm_num [map, (P.side_endpoints hr hm hd ho false).1]

include hr in
theorem map_one (hm : 0 < m) (hd : 0 < d) (ho : Odd d) : P.map r 1 = 1 := by
  norm_num [map, (P.side_endpoints hr hm hd ho true).1]

include hr in
theorem map_one_third (hm : 0 < m) (hd : 0 < d) (ho : Odd d) : P.map r (1/3) = 1/3 := by
  simpa only [add_zero, (generators_endpoints hr ho).1] using
    P.map_section hr hm hd ho (u := 0) (by norm_num)

include hr in
theorem map_two_thirds (hm : 0 < m) (hd : 0 < d) (ho : Odd d) : P.map r (2/3) = 2/3 := by
  simpa only [(generators_endpoints hr ho).2, one_add_one_eq_two] using
    P.map_section hr hm hd ho (u := 1) (by norm_num)

/-- Each point belongs to one of the three closed parameterized pieces. -/
theorem three_pieces {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (∃ x ∈ Icc (0:ℝ) 1, u = x/3) ∨ (∃ x ∈ Icc (0:ℝ) 1, u = (1+x)/3) ∨
    (∃ x ∈ Icc (0:ℝ) 1, u = 1-x/3) := by
  have h₀ := hu.1; have h₁ := hu.2
  rcases le_or_gt u (1/3) with h | h
  · exact Or.inl ⟨3*u, ⟨by linarith, by linarith⟩, by ring⟩
  rcases le_or_gt (2/3) u with hh | hh
  · exact Or.inr (Or.inr ⟨3*(1-u), ⟨by linarith, by linarith⟩, by ring⟩)
  · exact Or.inr (Or.inl ⟨3*u-1, ⟨by linarith, by linarith⟩, by ring⟩)

theorem map_left_param {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    P.map r (x/3) = P.sideMap false r x/3 := by
  rw [P.map_left (by linarith [hx.2]), show 3*(x/3) = x by ring]

theorem map_right_param {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
    P.map r (1-x/3) = 1-P.sideMap true r x/3 := by
  rw [P.map_right (by linarith [hx.2]), show 3*(1-(1-x/3)) = x by ring]

include hr in
theorem mapsTo (hm : 0 < m) (hd : 0 < d) (ho : Odd d) :
    MapsTo (P.map r) (Icc 0 1) (Icc 0 1) := by
  intro u hu
  rcases three_pieces hu with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
  · rw [P.map_left_param hx]
    have h := P.side_mem hr hm hd false hx
    constructor <;> linarith [h.1, h.2]
  · rw [P.map_section hr hm hd ho hx]
    have h := hr.mapsTo hx
    constructor <;> linarith [h.1, h.2]
  · rw [P.map_right_param hx]
    have h := P.side_mem hr hm hd true hx
    constructor <;> linarith [h.1, h.2]

include hr in
theorem left_third (hm : 0 < m) (hd : 0 < d) {u : ℝ} (hu : u ∈ Icc (0:ℝ) (1/3)) :
    P.map r u ∈ Icc (0:ℝ) (1/3) := by
  rw [P.map_left hu.2]
  have h := P.side_mem hr hm hd false (u := 3*u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  constructor <;> linarith [h.1, h.2]

include hr in
theorem right_third (hm : 0 < m) (hd : 0 < d) {u : ℝ} (hu : u ∈ Icc (2/3:ℝ) 1) :
    P.map r u ∈ Icc (2/3:ℝ) 1 := by
  rw [P.map_right hu.1]
  have h := P.side_mem hr hm hd true (u := 3*(1-u)) ⟨by linarith [hu.2], by linarith [hu.1]⟩
  constructor <;> linarith [h.1, h.2]

include hr in
theorem middle_third (hm : 0 < m) (hd : 0 < d) (ho : Odd d)
    {u : ℝ} (hu : u ∈ Icc (1/3:ℝ) (2/3)) : P.map r u ∈ Icc (1/3:ℝ) (2/3) := by
  have hx : 3*u-1 ∈ Icc (0:ℝ) 1 := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨hl, hh⟩ := hr.mapsTo hx
  have h := P.map_section hr hm hd ho hx
  rw [show (1+(3*u-1))/3 = u by ring] at h
  rw [h]
  constructor <;> linarith

private theorem chartDecoder_left_param {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (a : Bool → ℝ) :
    chartDecoder (a false) (a true) (x/3) = shoulder false (a false) x := by
  rw [chartDecoder_left (by linarith [hx.2]), show 3*(x/3) = x by ring]

private theorem chartDecoder_right_param {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (a : Bool → ℝ) :
    chartDecoder (a false) (a true) (1-x/3) = shoulder true (a true) x := by
  rw [chartDecoder_right (by linarith [hx.2]), show 3*(1-(1-x/3)) = x by ring]

include hr in
theorem map_decoder (hm : 0 < m) (hd : 0 < d) (ho : Odd d)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    chartDecoder (γ false) (γ true) (P.map r u) = r (chartDecoder (β false) (β true) u) := by
  rcases three_pieces hu with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
  · rw [P.map_left_param hx, chartDecoder_left_param (P.side_mem hr hm hd false hx),
      chartDecoder_left_param hx, P.side_decoder hr]
  · rw [P.map_section hr hm hd ho hx, chartDecoder_core _ _ (hr.mapsTo hx), chartDecoder_core _ _ hx]
  · rw [P.map_right_param hx, chartDecoder_right_param (P.side_mem hr hm hd true hx),
      chartDecoder_right_param hx, P.side_decoder hr]

include hr in
theorem map_dist_le {s : ℝ → ℝ} (hs : GridAdmissible m d s) {δ : ℝ}
    (hδ : ∀ x ∈ Icc (0:ℝ) 1, |r x-s x| ≤ δ) (u : ℝ) :
    |P.map r u-P.map s u| ≤ δ/3 := by
  by_cases hl : u ≤ 1/3
  · rw [P.map_left hl, P.map_left hl, ← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ)<3)]
    exact div_le_div_of_nonneg_right (P.side_dist_le hr hs hδ false _) (by norm_num)
  by_cases hh : 2/3 ≤ u
  · rw [P.map_right hh, P.map_right hh, sub_sub_sub_cancel_left, ← sub_div, abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<3), abs_sub_comm]
    exact div_le_div_of_nonneg_right (P.side_dist_le hr hs hδ true _) (by norm_num)
  · simp only [map, if_neg hl, if_neg hh, ← sub_div, add_sub_add_left_eq_sub, abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<3)]
    exact div_le_div_of_nonneg_right (hδ _ (fold_mem _)) (by norm_num)

/-- Mark shifts for two successive substitutions. -/
def comp {e : ℤ} {η : Bool → ℝ} (Q : ChartMatch m e γ η) (P : ChartMatch (m*e) d β γ) :
    ChartMatch m (e*d) β η where
  shift s := Q.shift s + e*P.shift s
  matched s := (Q.matched s).comp (P.matched s)

theorem side_comp {e : ℤ} {η : Bool → ℝ} (Q : ChartMatch m e γ η) (P : ChartMatch (m*e) d β γ)
    {s : ℝ → ℝ} (hs : GridAdmissible m e s) (hr : GridAdmissible (m*e) d r)
    (hm : 0 < m) (he : 0 < e) (ho : Odd e) (side : Bool) (x : ℝ) :
    (Q.comp P).sideMap side (s ∘ r) x = Q.sideMap side s (P.sideMap side r x) := by
  simp only [sideMap, comp, Shoulder.to_fromParameter]
  have h := ShoulderMatch.functorial (n := P.shift side) hm he ho hs hr (Q.matched side)
  exact congrArg (normalizedShoulder side (η side)).fromParameter
    (congrFun h ((normalizedShoulder side (β side)).toParameter x)).symm

theorem map_comp {e : ℤ} {η : Bool → ℝ} (Q : ChartMatch m e γ η) (P : ChartMatch (m*e) d β γ)
    {s : ℝ → ℝ} (hs : GridAdmissible m e s) (hr : GridAdmissible (m*e) d r)
    (hm : 0 < m) (he : 0 < e) (hd : 0 < d) (heodd : Odd e) (hdodd : Odd d)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (Q.comp P).map (s ∘ r) u = Q.map s (P.map r u) := by
  rcases three_pieces hu with ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩
  · rw [(Q.comp P).map_left_param hx, P.map_left_param hx,
      Q.map_left_param (P.side_mem hr (mul_pos hm he) hd false hx), Q.side_comp P hs hr hm he heodd]
  · rw [(Q.comp P).map_section (GridAdmissible.comp hs hr) hm (mul_pos he hd) (heodd.mul hdodd) hx,
      P.map_section hr (mul_pos hm he) hd hdodd hx, Q.map_section hs hm he heodd (hr.mapsTo hx),
      Function.comp_apply]
  · rw [(Q.comp P).map_right_param hx, P.map_right_param hx,
      Q.map_right_param (P.side_mem hr (mul_pos hm he) hd true hx), Q.side_comp P hs hr hm he heodd]

end ChartMatch
end
end CommutingIntervalSimplified.DecoderProjection
