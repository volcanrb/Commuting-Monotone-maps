import CommutingIntervalSimplified.ProductHorseshoe
import Mathlib.Dynamics.TopologicalEntropy.NetEntropy

/-!
# Entropy obstruction for interval horseshoes

A separated two-branch horseshoe realizes all binary words. A fixed metric
entourage distinguishes these itineraries at every word length, giving the
Bowen–Dinaburg entropy bound used in the zero-entropy interval argument.
-/

namespace CommutingIntervalSimplified

open Function Set Dynamics
open scoped Uniformity ENNReal

namespace TwoBranchHorseshoe

private def branch {F : IntervalMap} (H : TwoBranchHorseshoe F) : Bool → Set I
  | false => Icc H.a H.b
  | true => Icc H.c H.d

private theorem branch_subset {F : IntervalMap} (H : TwoBranchHorseshoe F) (s : Bool) :
    H.branch s ⊆ Icc H.a H.d := by
  cases s with
  | false => exact Icc_subset_Icc_right (H.b_lt_c.trans H.c_lt_d).le
  | true => exact Icc_subset_Icc_left (H.a_lt_b.trans H.b_lt_c).le

private theorem branch_covers {F : IntervalMap} (H : TwoBranchHorseshoe F) (s : Bool) :
    Icc H.a H.d ⊆ F '' H.branch s := by
  cases s
  · exact H.left_covers
  · exact H.right_covers

/-- Realize a finite word, with time zero corresponding to its first letter. -/
private theorem realize_word {F : IntervalMap} (H : TwoBranchHorseshoe F) :
    ∀ {n : ℕ} (w : Fin n → Bool), ∃ x ∈ Icc H.a H.d,
      ∀ i : Fin n, F^[i.val] x ∈ H.branch (w i) := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨H.a, ⟨le_rfl, (H.a_lt_b.trans (H.b_lt_c.trans H.c_lt_d)).le⟩, fun i => i.elim0⟩
  | succ n ih =>
    intro w
    obtain ⟨y, hy, hit⟩ := ih (fun i => w i.succ)
    obtain ⟨x, hx, hxy⟩ := H.branch_covers (w 0) hy
    refine ⟨x, H.branch_subset _ hx, ?_⟩
    exact Fin.cases hx (fun i => by
      simpa only [Fin.val_succ, iterate_succ_apply, hxy] using hit i)

private theorem separated_letters {F : IntervalMap} (H : TwoBranchHorseshoe F)
    {u v : Bool} {x y : I} (huv : u ≠ v) (hx : x ∈ H.branch u) (hy : y ∈ H.branch v) :
    (H.c : ℝ) - H.b ≤ dist x y := by
  have hsep : (H.b : ℝ) < H.c := H.b_lt_c
  rw [Subtype.dist_eq, Real.dist_eq]
  cases u <;> cases v <;> try contradiction
  · have hxb : (x : ℝ) ≤ H.b := hx.2
    have hcy : (H.c : ℝ) ≤ y := hy.1
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hcx : (H.c : ℝ) ≤ x := hx.1
    have hyb : (y : ℝ) ≤ H.b := hy.2
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The two branches force entropy at least the natural logarithm of two. -/
theorem log_two_le_coverEntropy {F : IntervalMap} (H : TwoBranchHorseshoe F) :
    ENNReal.log 2 ≤ coverEntropy F univ := by
  classical
  let ε := ((H.c : ℝ) - H.b) / 2
  have hbc : (H.b : ℝ) < H.c := H.b_lt_c
  have hε : 0 < ε := by dsimp [ε]; linarith
  let U : Set (I × I) := {p | dist p.1 p.2 < ε}
  refine le_trans ?_ (netEntropyEntourage_le_coverEntropy (T := F) (F := univ)
    (U := U) (Metric.dist_mem_uniformity hε))
  rw [netEntropyEntourage, ← ExpGrowth.expGrowthSup_pow]
  apply ExpGrowth.expGrowthSup_monotone
  intro n
  choose x _ hx using (H.realize_word (n := n))
  have separated (w v : Fin n → Bool) (hne : w ≠ v) :
      ∃ i : Fin n, (H.c : ℝ) - H.b ≤ dist (F^[i.val] (x w)) (F^[i.val] (x v)) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, H.separated_letters hi (hx w i) (hx v i)⟩
  have hinj : Injective x := by
    intro w v hwv
    by_contra hne
    obtain ⟨i, hi⟩ := separated w v hne
    rw [hwv, dist_self] at hi
    linarith
  let E := Finset.univ.image x
  have hE : IsDynNetIn F univ U n (E : Set I) := by
    refine ⟨subset_univ _, ?_⟩
    intro a ha b hb hab
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨i, hi⟩ := separated w v (fun e => hab (congrArg x e))
    apply Set.disjoint_left.mpr
    intro z hwz hvz
    have hw := mem_ball_dynEntourage.mp hwz i.val i.isLt
    have hv := mem_ball_dynEntourage.mp hvz i.val i.isLt
    change dist (F^[i.val] (x w)) (F^[i.val] z) < ε at hw
    change dist (F^[i.val] (x v)) (F^[i.val] z) < ε at hv
    have ht := dist_triangle_right (F^[i.val] (x w)) (F^[i.val] (x v)) (F^[i.val] z)
    dsimp [ε] at hw hv
    linarith
  have hcard : E.card = 2 ^ n := by simp [E, Finset.card_image_of_injective _ hinj]
  have lower := ENat.toENNReal_mono hE.card_le_netMaxcard
  simpa [hcard] using lower

/-- A zero-entropy interval map admits no separated two-branch horseshoe. -/
theorem not_nonempty_of_coverEntropy_zero {F : IntervalMap} (h : coverEntropy F univ = 0) :
    ¬ Nonempty (TwoBranchHorseshoe F) := by
  rintro ⟨H⟩
  have hp : ENNReal.log 1 < ENNReal.log 2 := ENNReal.log_strictMono (by norm_num)
  simpa [h] using (hp.trans_le H.log_two_le_coverEntropy)

end TwoBranchHorseshoe


/-- Sampling a dynamical cover at multiples of `p` bounds the entropy of an
iterate by `p` times the entropy of the original map. -/
theorem coverEntropy_iterate_le {X : Type*} [UniformSpace X] (f : X → X) (S : Set X)
    {p : ℕ} (hp : 0 < p) : coverEntropy f^[p] S ≤ p * coverEntropy f S := by
  apply iSup₂_le
  intro U hU
  have mono : Monotone (fun n => (coverMincard f S U n).toENNReal) :=
    fun _ _ h => ENat.toENNReal_mono (coverMincard_monotone_time f S U h)
  calc
    coverEntropyEntourage f^[p] S U
        ≤ ExpGrowth.expGrowthSup (fun n => (coverMincard f S U (p * n)).toENNReal) := by
          apply ExpGrowth.expGrowthSup_monotone
          intro n
          apply ENat.toENNReal_mono
          apply biInf_mono
          intro s hs
          apply hs.mono_entourage
          rintro ⟨x, y⟩ hxy
          apply mem_dynEntourage.mpr
          intro k hk
          rw [← iterate_mul]
          exact mem_dynEntourage.mp hxy (p * k) (Nat.mul_lt_mul_of_pos_left hk hp)
    _ = p * coverEntropyEntourage f S U := mono.expGrowthSup_comp_mul hp.ne'
    _ ≤ p * coverEntropy f S := by
      gcongr
      exact coverEntropyEntourage_le_coverEntropy f S hU

/-- Positive iterates preserve the vanishing of entropy. -/
theorem coverEntropy_iterate_eq_zero {X : Type*} [UniformSpace X] {f : X → X}
    {S : Set X} (hS : S.Nonempty) (hz : coverEntropy f S = 0) {p : ℕ} (hp : 0 < p) :
    coverEntropy f^[p] S = 0 := by
  exact le_antisymm (by simpa [hz] using coverEntropy_iterate_le f S hp)
    (coverEntropy_nonneg _ hS)

private theorem trim_cover_away {f : IntervalMap} (hf : Continuous f) {a b m s t : I}
    (hst : s < t) (hcov : IntervalCovers f a b s t) (hs : f m ≠ s) (ht : f m ≠ t) :
    ∃ u v : I, u ∈ Icc a b ∧ v ∈ Icc a b ∧ u ≠ m ∧ v ≠ m ∧ u < v ∧
      IntervalCovers f u v s t := by
  obtain ⟨x, hx, hfx⟩ := hcov (left_mem_Icc.mpr hst.le)
  obtain ⟨y, hy, hfy⟩ := hcov (right_mem_Icc.mpr hst.le)
  have hxm : x ≠ m := fun e => hs (e ▸ hfx)
  have hym : y ≠ m := fun e => ht (e ▸ hfy)
  have hxy : x ≠ y := fun e => hst.ne (hfx.symm.trans (e ▸ hfy))
  rcases lt_or_gt_of_ne hxy with h | h
  · exact ⟨x, y, hx, hy, hxm, hym, h,
      intervalCovers_of_endpoints_mono hf h.le hst.le hfx.le hfy.ge⟩
  · exact ⟨y, x, hy, hx, hym, hxm, h,
      intervalCovers_of_endpoints_anti hf h.le hst.le hfx.le hfy.ge⟩

/-- A horseshoe whose intervals share a boundary point yields a separated
horseshoe for the second iterate. -/
theorem separated_horseshoe_of_adjacent_covers {f : IntervalMap} (hf : Continuous f)
    {a b c : I} (hab : a < b) (hbc : b < c)
    (hl : IntervalCovers f a b a c) (hr : IntervalCovers f b c a c) :
    Nonempty (TwoBranchHorseshoe (f ∘ f)) := by
  have hac := hab.trans hbc
  -- Pick a target interval covering the hull on the next step and with
  -- endpoints different from the value at the junction.
  have target : ∃ s t : I, s < t ∧ Icc s t ⊆ Icc a c ∧ IntervalCovers f s t a c ∧
      f b ≠ s ∧ f b ≠ t := by
    rcases lt_trichotomy (f b) b with h | h | h
    · exact ⟨b, c, hbc, Icc_subset_Icc_left hab.le, hr, h.ne, (h.trans hbc).ne⟩
    · exact ⟨a, c, hac, Subset.rfl,
        hl.trans (image_mono (Icc_subset_Icc_right hbc.le)), by simpa only [h] using hab.ne', by simpa only [h] using hbc.ne⟩
    · exact ⟨a, b, hab, Icc_subset_Icc_right hbc.le, hl, (hab.trans h).ne', h.ne'⟩
  obtain ⟨s, t, hst, hsub, hcov, hs, ht⟩ := target
  obtain ⟨u, v, hu, hv, _, hvb, huv, hluv⟩ := trim_cover_away hf hst (hsub.trans hl) hs ht
  obtain ⟨w, z, hw, hz, hwb, _, hwz, hrwz⟩ := trim_cover_away hf hst (hsub.trans hr) hs ht
  have hull : Icc u z ⊆ Icc a c := Icc_subset_Icc hu.1 hz.2
  have refineCover (i j : I) (hij : IntervalCovers f i j s t) :
      IntervalCovers (f ∘ f) i j u z := by
    intro x hx
    obtain ⟨y, hy, hfy⟩ := hcov (hull hx)
    obtain ⟨q, hq, hfq⟩ := hij hy
    exact ⟨q, hq, by simpa [hfq] using hfy⟩
  exact ⟨⟨u, v, w, z, huv, (lt_of_le_of_ne hv.2 hvb).trans (lt_of_le_of_ne hw.1 hwb.symm),
    hwz, refineCover _ _ hluv, refineCover _ _ hrwz⟩⟩

/-- The zero-entropy obstruction also excludes adjacent horseshoes for every
positive iterate of an interval map. -/
theorem not_adjacent_covers_of_coverEntropy_zero {f : IntervalMap} (hf : Continuous f)
    (hz : coverEntropy f univ = 0) {p : ℕ} (hp : 0 < p) {a b c : I}
    (hab : a < b) (hbc : b < c) (hl : IntervalCovers f^[p] a b a c) :
    ¬ IntervalCovers f^[p] b c a c := by
  intro hr
  have hzero := coverEntropy_iterate_eq_zero univ_nonempty hz hp
  have hdouble := coverEntropy_iterate_eq_zero univ_nonempty hzero (show 0 < 2 by decide)
  apply TwoBranchHorseshoe.not_nonempty_of_coverEntropy_zero hdouble
  simpa [Function.iterate_succ] using separated_horseshoe_of_adjacent_covers (hf.iterate p)
    hab hbc hl hr

/-- A commuting pair whose composition has entropy below `log 2` has a
common fixed point. -/
theorem commonFixedPoint_of_product_entropy_lt_log_two {f g : IntervalMap}
    (hf : Continuous f) (hg : Continuous g) (hcomm : Function.Commute f g)
    (hsmall : coverEntropy (f ∘ g) univ < ENNReal.log 2) : HasCommonFixedPoint f g := by
  by_contra hno
  obtain ⟨H⟩ := commuting_noCommonFixedPoint_product_horseshoe hf hg hcomm hno
  exact hsmall.not_ge H.log_two_le_coverEntropy

end CommutingIntervalSimplified
