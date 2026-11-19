import CommutingIntervalSimplified.DecoderProjection
import Mathlib.Tactic.FieldSimp

/-!
# Compatible decoder shoulders

This gives the marks and terminal unit intervals in the manuscript's
unfolded shoulder coordinates. It constructs the continuous shoulder map
from an admissible projection of decoder targets and proves endpoint
agreement, decoder commutation, functoriality, and its physical scale bound.
-/

namespace CommutingIntervalSimplified.DecoderProjection

open Set
noncomputable section

/-- Starting mark of the decoder shoulder attached to target cell `(ℓ,k)`. -/
def chartMark (M ℓ k : ℤ) : ℝ := (2*k + ((ℓ:ℝ)+1/3)/4)/M

theorem chartMark_vertex {M : ℤ} (hM : M ≠ 0) (ℓ k : ℤ) :
    (12:ℝ)*M*chartMark M ℓ k = (24*k+3*ℓ+1:ℤ) := by
  have hn : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  simp only [chartMark]
  push_cast; field_simp; ring

/-- The mark lifts differ by twice the difference of their cell residues,
measured in units of the coarse modulus. -/
theorem chartMark_projection {M d k k' n : ℤ} (hM : M ≠ 0) (hd : d ≠ 0) (ℓ : ℤ)
    (hk : k' = k + M*n) :
    d*chartMark (d*M) ℓ k' = chartMark M ℓ k + 2*n := by
  have h₁ : (M:ℝ) ≠ 0 := by exact_mod_cast hM
  have h₂ : (d:ℝ) ≠ 0 := by exact_mod_cast hd
  rw [hk]; simp only [chartMark, Int.cast_mul, Int.cast_add]
  field_simp; ring

theorem fold_int (b : ℤ) : fold (b:ℝ) = ((b%2:ℤ):ℝ) := by
  have h : (b:ℝ) = 2*((b/2:ℤ):ℝ)+((b%2:ℤ):ℝ) := by
    exact_mod_cast (show b = 2*(b/2)+b%2 by omega)
  have hn : 0 ≤ b%2 := by omega
  have hu : b%2 ≤ 1 := by omega
  conv_lhs => rw [h, fold_even_translate, fold_eq_self ⟨by exact_mod_cast hn, by exact_mod_cast hu⟩]

theorem fold_succ_int (b : ℤ) : fold ((b:ℝ)+1) = 1-fold b := by
  rw [← Int.cast_one (R := ℝ), ← Int.cast_add, fold_int, fold_int]
  exact_mod_cast (show (b+1)%2 = 1-b%2 by omega)

theorem fold_odd_dilation {d : ℤ} (hd : Odd d) (b n : ℤ) :
    fold ((d:ℝ)*b-2*n) = fold b := by
  obtain ⟨k, hk⟩ := hd
  have h : (d:ℝ)*b-2*n = 2*((k*b-n:ℤ):ℝ)+(b:ℝ) := by
    rw [hk]; push_cast; ring
  rw [h, fold_even_translate]

/-- The unfolded parameter interval of a shoulder is `[mark,tail+1]`. -/
structure Shoulder where
  mark : ℝ
  tail : ℤ
  mark_le : mark ≤ tail
  least : ∀ z : ℤ, mark ≤ z → fold (z:ℝ) = fold (tail:ℝ) → tail ≤ z

namespace Shoulder

/-- Choose the least integer of the prescribed parity at or above the mark. -/
def ofParity (β : ℝ) (p : ℤ) : Shoulder where
  mark := β
  tail := ⌈β⌉ + (p-⌈β⌉)%2
  mark_le := by
    have h : ⌈β⌉ ≤ ⌈β⌉+(p-⌈β⌉)%2 := by omega
    exact (Int.le_ceil _).trans (by exact_mod_cast h)
  least z hz he := by
    rw [fold_int, fold_int] at he
    have he' : z%2 = (⌈β⌉+(p-⌈β⌉)%2)%2 := by exact_mod_cast he
    have hz' := Int.ceil_le.mpr hz
    omega

/-- Physical endpoints are recovered after affine rescaling of this interval. -/
def parameter (J : Shoulder) : Set ℝ := Icc J.mark (J.tail+1)

def coreValue (J : Shoulder) : ℝ := fold ((J.tail:ℝ)+1)

theorem tail_value_eq {J K : Shoulder} (h : J.coreValue = K.coreValue) :
    fold (J.tail:ℝ) = fold (K.tail:ℝ) := by
  simp only [coreValue, fold_succ_int] at h
  linarith

end Shoulder

/-- The mark and core-end compatibility conditions on a fine and coarse
shoulder. Here `m` is the *decoder target's* coarse mesh density. -/
structure ShoulderMatch (m d n : ℤ) (J K : Shoulder) : Prop where
  mark : d*J.mark = K.mark + 2*n
  vertex : ∃ i : ℤ, m*(d*J.mark) = i
  core : J.coreValue = K.coreValue

/-- In a lifted chart the integral mesh vertex follows from the formula for its
mark and the compatibility of the two cell residues. -/
theorem chartMark_match {M d n k k' : ℤ} (hM : M ≠ 0) (hd : d ≠ 0)
    {ℓ : ℤ} {J K : Shoulder} (hj : J.mark = chartMark (d*M) ℓ k')
    (hk : K.mark = chartMark M ℓ k) (hres : k' = k+M*n)
    (hcore : J.coreValue = K.coreValue) : ShoulderMatch (12*M) d n J K := by
  refine ⟨by rw [hj, hk, chartMark_projection hM hd ℓ hres], ⟨24*k'+3*ℓ+1, ?_⟩, hcore⟩
  rw [hj]
  have h := chartMark_vertex (mul_ne_zero hd hM) ℓ k'
  push_cast at h ⊢
  linarith

/-- The even translation aligns the initial fine mark with the coarse mark. -/
def rayMap (d n : ℤ) (r : ℝ → ℝ) (t : ℝ) : ℝ := unfoldMap d r t - 2*n

/-- Formula for the map on unfolded shoulder parameters. -/
def theta (K : Shoulder) (d n : ℤ) (r : ℝ → ℝ) : ℝ → ℝ :=
  descend K.tail (rayMap d n r)

namespace ShoulderMatch

variable {m d n : ℤ} {r : ℝ → ℝ} {J K : Shoulder} (h : ShoulderMatch m d n J K)
  (hr : GridAdmissible m d r)

include h hr in
theorem ray_start : rayMap d n r J.mark = K.mark := by
  obtain ⟨i, hi⟩ := h.vertex
  rw [rayMap, hr.lift_vertex hi, h.mark]; ring

include h hr in
theorem ray_ge_mark (hm : 0 < m) (hd : 0 < d) {t : ℝ} (ht : J.mark ≤ t) :
    K.mark ≤ rayMap d n r t := by
  obtain ⟨i, hi⟩ := h.vertex
  have hl := hr.lift_ge_vertex hm hd hi ht
  dsimp [rayMap]; linarith [h.mark]

include h hr in
theorem ray_tail (hm : 0 < m) (hd : 0 < d) (hodd : Odd d) {t : ℝ} (ht : J.tail ≤ t) :
    K.tail ≤ rayMap d n r t := by
  have hz : (m:ℝ)*(d*(J.tail:ℝ)) = (m*d*J.tail:ℤ) := by push_cast; ring
  have hstart := h.ray_ge_mark hr hm hd J.mark_le
  rw [rayMap, hr.lift_vertex hz] at hstart
  have hl : K.tail ≤ d*J.tail-2*n := by
    apply K.least
    · simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using hstart
    · push_cast
      exact (fold_odd_dilation hodd _ n).trans (Shoulder.tail_value_eq h.core)
  have hl' : (K.tail:ℝ) ≤ d*(J.tail:ℝ)-2*n := by exact_mod_cast hl
  have hmap := hr.lift_ge_vertex hm hd hz ht
  dsimp [rayMap]; linarith

include h hr in
theorem endpoints (hm : 0 < m) (hd : 0 < d) (hodd : Odd d) :
    theta K d n r J.mark = K.mark ∧ theta K d n r (J.tail+1) = K.tail+1 := by
  apply descend_endpoints K.mark_le (h.ray_start hr)
    (h.ray_tail hr hm hd hodd (show (J.tail:ℝ) ≤ J.tail+1 by linarith))
  have hz : (m:ℝ)*(d*((J.tail:ℝ)+1)) = (m*d*(J.tail+1):ℤ) := by push_cast; ring
  rw [rayMap, hr.lift_vertex hz]
  calc
    _ = fold ((J.tail+1:ℤ):ℝ) := by simpa using fold_odd_dilation hodd (J.tail+1) n
    _ = _ := by simpa [Shoulder.coreValue] using h.core

include h hr in
theorem mapsTo (hm : 0 < m) (hd : 0 < d) : MapsTo (theta K d n r) J.parameter K.parameter :=
  fun _ ht => quotient_mem K.mark_le (h.ray_ge_mark hr hm hd ht.1)

include hr in
theorem decoder (t : ℝ) : fold (theta K d n r t) = r (fold t) :=
  descend_decoder (translated_decoder (fold_unfoldMap hr.mapsTo) n) _ _

include hr in
theorem continuous : Continuous (theta K d n r) :=
  continuous_descend ((continuous_unfoldMap hr.unit_vertices hr.continuousOn).sub continuous_const) _

include hr in
theorem physical_bound {s : ℝ → ℝ} (hs : GridAdmissible m d s)
    {slope offset δ : ℝ} (hwidth : |slope| *(K.tail+1-K.mark) ≤ 1/12)
    (hδ : ∀ x ∈ Icc (0:ℝ) 1, |r x-s x| ≤ δ) (t : ℝ) :
    |(offset+slope*theta K d n r t)-(offset+slope*theta K d n s t)| ≤ (1/12)*δ := by
  apply physical_shoulder_bound K.mark_le hwidth
  simpa only [rayMap, sub_sub_sub_cancel_right, unfoldMap_distance hr.mapsTo hs.mapsTo] using
    (show |unfoldMap d r t - unfoldMap d s t| ≤ δ by rw [unfoldMap_distance hr.mapsTo hs.mapsTo]; exact hδ _ (fold_mem _))

theorem comp {e p : ℤ} {L : Shoulder}
    (h₂ : ShoulderMatch m e p K L) (h₁ : ShoulderMatch (m*e) d n J K) :
    ShoulderMatch m (e*d) (p+e*n) J L := by
  refine ⟨?_, ?_, h₁.core.trans h₂.core⟩
  · push_cast
    rw [mul_assoc, h₁.mark, mul_add, h₂.mark]; ring
  · obtain ⟨i, hi⟩ := h₁.vertex
    exact ⟨i, by push_cast at hi ⊢; linarith⟩

/-- The composition law, including the even translations associated with the
three starting marks and the effect of reducing at the intermediate tail. -/
theorem functorial {e p : ℤ} {s : ℝ → ℝ} {L : Shoulder}
    (hm : 0 < m) (he : 0 < e) (hodd : Odd e)
    (hs : GridAdmissible m e s) (hr : GridAdmissible (m*e) d r)
    (h₂ : ShoulderMatch m e p K L) :
    theta L e p s ∘ theta K d n r = theta L (e*d) (p+e*n) (s ∘ r) := by
  rw [theta, theta, theta, descend_comp _ (fun _ ht => h₂.ray_tail hs hm he hodd ht)
    (translated_decoder (fold_unfoldMap hs.mapsTo) p)]
  congr 1
  funext t
  simp only [Function.comp_apply, rayMap, GridAdmissible.unfoldMap_comp hm he hs hr]
  exact translated_comp (unfoldMap_translate e hs.mapsTo hs.unit_vertices) t

end ShoulderMatch
end
end CommutingIntervalSimplified.DecoderProjection
