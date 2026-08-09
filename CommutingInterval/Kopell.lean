import CommutingInterval.DynamicsDefs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Iterate
import Mathlib.Topology.EMetricSpace.BoundedVariation

namespace CommutingInterval

open Filter Function Set
open scoped BigOperators ENNReal Topology

private theorem orderIso_iterate_coe
    {g : ℝ → ℝ} {a b : ℝ} (e : Set.Icc a b ≃o Set.Icc a b)
    (he : ∀ x : Set.Icc a b, (e x : ℝ) = g x) :
    ∀ (n : ℕ) (x : Set.Icc a b),
      ((e^[n]) x : ℝ) = (g^[n]) (x : ℝ) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [he]
      exact congrArg g (ih x)

/-- Elementary Polterovich--Sodin derivative growth on a compact interval.
The order isomorphism records that the ambient map really is an
orientation-preserving self-diffeomorphism of the displayed interval. -/
theorem polterovichSodin_unbounded_iterate_deriv
    {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (e : Set.Icc a b ≃o Set.Icc a b)
    (he : ∀ x : Set.Icc a b, (e x : ℝ) = g x)
    (hiter_cont : ∀ n : ℕ, ContinuousOn (g^[n]) (Set.Icc a b))
    (hiter_diff : ∀ n : ℕ, DifferentiableOn ℝ (g^[n]) (Set.Ioo a b))
    (hnontrivial : ∃ c ∈ Set.Ioo a b, g c ≠ c) :
    ∀ C : ℝ, ∃ n : ℕ, ∃ x ∈ Set.Ioo a b,
      C < deriv (g^[n]) x := by
  intro C
  rcases hnontrivial with ⟨c, hc, hgc⟩
  let cI : Set.Icc a b := ⟨c, hc.1.le, hc.2.le⟩
  have hec_ne : e cI ≠ cI := by
    intro h
    apply hgc
    have := congrArg Subtype.val h
    simpa [cI, he cI] using this
  let z : ℕ → Set.Icc a b := fun n ↦ (e.symm^[n]) cI
  have hcancel (n : ℕ) : (e^[n]) (z n) = cI := by
    exact (Function.LeftInverse.iterate e.apply_symm_apply n) cI
  have hz_mem (n : ℕ) : (z n : ℝ) ∈ Set.Ioo a b := by
    let aI : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
    let bI : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
    have haI_le (x : Set.Icc a b) : aI ≤ x := x.property.1
    have hle_bI (x : Set.Icc a b) : x ≤ bI := x.property.2
    have hinv_a : e.symm aI = aI := by
      apply le_antisymm
      · simpa using e.symm.monotone (haI_le (e aI))
      · exact haI_le _
    have hinv_b : e.symm bI = bI := by
      apply le_antisymm
      · exact hle_bI _
      · simpa using e.symm.monotone (hle_bI (e bI))
    have hzmono : StrictMono (e.symm^[n]) := e.symm.strictMono.iterate n
    have hleft : aI < cI := by
      exact hc.1
    have hright : cI < bI := by
      exact hc.2
    have hleft' := hzmono hleft
    have hright' := hzmono hright
    have hfix_a : (e.symm^[n]) aI = aI :=
      (Function.IsFixedPt.iterate hinv_a n)
    have hfix_b : (e.symm^[n]) bI = bI :=
      (Function.IsFixedPt.iterate hinv_b n)
    constructor
    · rw [hfix_a] at hleft'
      exact hleft'
    · rw [hfix_b] at hright'
      exact hright'
  have himage_lower (k : ℕ) :
      (g^[k + 1]) (z (k + 1) : ℝ) = c := by
    calc
      (g^[k + 1]) (z (k + 1) : ℝ) =
          ((e^[k + 1]) (z (k + 1)) : ℝ) :=
        (orderIso_iterate_coe e he (k + 1) (z (k + 1))).symm
      _ = c := congrArg Subtype.val (hcancel (k + 1))
  have himage_upper (k : ℕ) :
      (g^[k + 1]) (z k : ℝ) = g c := by
    calc
      (g^[k + 1]) (z k : ℝ) = ((e^[k + 1]) (z k) : ℝ) :=
        (orderIso_iterate_coe e he (k + 1) (z k)).symm
      _ = (e ((e^[k]) (z k)) : ℝ) := by
        rw [Function.iterate_succ_apply']
      _ = (e cI : ℝ) := by rw [hcancel k]
      _ = g c := he cI
  rcases lt_or_gt_of_ne hec_ne with hec_lt | hec_gt
  · have hlt_inv : cI < e.symm cI := by
      rw [← e.lt_iff_lt]
      simpa using hec_lt
    have hzmono : StrictMono z :=
      e.symm.strictMono.strictMono_iterate_of_lt_map hlt_inv
    let base : ℝ := c - (e cI : ℝ)
    let D : ℝ := max C 0 + 1
    let δ : ℝ := base / D
    have hbase : 0 < base := by
      change 0 < (cI : ℝ) - (e cI : ℝ)
      exact sub_pos.mpr hec_lt
    have hD : 0 < D := by
      dsimp [D]
      linarith [le_max_right C 0]
    have hδ : 0 < δ := div_pos hbase hD
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b - a) / δ)
    have hsmall : ∃ k < N,
        (z (k + 1) : ℝ) - (z k : ℝ) < δ := by
      by_contra h
      push Not at h
      have hlower :
          ∑ k ∈ Finset.range N, δ ≤
            ∑ k ∈ Finset.range N,
              ((z (k + 1) : ℝ) - (z k : ℝ)) := by
        gcongr with k hk
        exact h k (Finset.mem_range.mp hk)
      have htelescope :
          ∑ k ∈ Finset.range N,
              ((z (k + 1) : ℝ) - (z k : ℝ)) =
            (z N : ℝ) - c := by
        simpa [cI, z] using
          (Finset.sum_range_sub (fun n ↦ (z n : ℝ)) N)
      have hupper : (z N : ℝ) - c ≤ b - a := by
        have hzN := (z N).property
        linarith [hzN.2, hc.1.le]
      have hchoice : b - a < (N : ℝ) * δ := by
        exact (div_lt_iff₀ hδ).mp hN
      have hconst :
          ∑ _k ∈ Finset.range N, δ = (N : ℝ) * δ := by simp
      rw [hconst, htelescope] at hlower
      linarith
    rcases hsmall with ⟨k, hkN, hk⟩
    have hzk : (z k : ℝ) < (z (k + 1) : ℝ) := by
      exact_mod_cast hzmono (Nat.lt_succ_self k)
    obtain ⟨x, hx, hderiv⟩ :=
      exists_deriv_eq_slope (g^[k + 1]) hzk
        ((hiter_cont (k + 1)).mono
          (Set.Icc_subset_Icc (hz_mem k).1.le (hz_mem (k + 1)).2.le))
        ((hiter_diff (k + 1)).mono
          (Set.Ioo_subset_Ioo (hz_mem k).1.le (hz_mem (k + 1)).2.le))
    have hx_ab : x ∈ Set.Ioo a b :=
      ⟨(hz_mem k).1.trans hx.1,
        hx.2.trans (hz_mem (k + 1)).2⟩
    have hlen : 0 < (z (k + 1) : ℝ) - (z k : ℝ) := sub_pos.mpr hzk
    have hD_bound :
        D < base / ((z (k + 1) : ℝ) - (z k : ℝ)) := by
      rw [lt_div_iff₀ hlen]
      have := (lt_div_iff₀ hD).mp hk
      nlinarith
    refine ⟨k + 1, x, hx_ab, ?_⟩
    rw [hderiv, himage_lower, himage_upper]
    have hCD : C < D := by
      dsimp [D]
      linarith [le_max_left C 0]
    have hbase_eq : base = c - g c := by
      dsimp [base]
      rw [he cI]
    rw [hbase_eq] at hD_bound
    exact hCD.trans hD_bound
  · have hinv_lt : e.symm cI < cI := by
      rw [← e.lt_iff_lt]
      simpa using hec_gt
    have hzanti : StrictAnti z :=
      e.symm.strictMono.strictAnti_iterate_of_map_lt hinv_lt
    let base : ℝ := (e cI : ℝ) - c
    let D : ℝ := max C 0 + 1
    let δ : ℝ := base / D
    have hbase : 0 < base := by
      change 0 < (e cI : ℝ) - (cI : ℝ)
      exact sub_pos.mpr hec_gt
    have hD : 0 < D := by
      dsimp [D]
      linarith [le_max_right C 0]
    have hδ : 0 < δ := div_pos hbase hD
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b - a) / δ)
    have hsmall : ∃ k < N,
        (z k : ℝ) - (z (k + 1) : ℝ) < δ := by
      by_contra h
      push Not at h
      have hlower :
          ∑ k ∈ Finset.range N, δ ≤
            ∑ k ∈ Finset.range N,
              ((z k : ℝ) - (z (k + 1) : ℝ)) := by
        gcongr with k hk
        exact h k (Finset.mem_range.mp hk)
      have htelescope :
          ∑ k ∈ Finset.range N,
              ((z k : ℝ) - (z (k + 1) : ℝ)) =
            c - (z N : ℝ) := by
        simpa [cI, z] using
          (Finset.sum_range_sub' (fun n ↦ (z n : ℝ)) N)
      have hupper : c - (z N : ℝ) ≤ b - a := by
        have hzN := (z N).property
        linarith [hzN.1, hc.2.le]
      have hchoice : b - a < (N : ℝ) * δ := by
        exact (div_lt_iff₀ hδ).mp hN
      have hconst :
          ∑ _k ∈ Finset.range N, δ = (N : ℝ) * δ := by simp
      rw [hconst, htelescope] at hlower
      linarith
    rcases hsmall with ⟨k, hkN, hk⟩
    have hzk : (z (k + 1) : ℝ) < (z k : ℝ) := by
      exact_mod_cast hzanti (Nat.lt_succ_self k)
    obtain ⟨x, hx, hderiv⟩ :=
      exists_deriv_eq_slope (g^[k + 1]) hzk
        ((hiter_cont (k + 1)).mono
          (Set.Icc_subset_Icc (hz_mem (k + 1)).1.le (hz_mem k).2.le))
        ((hiter_diff (k + 1)).mono
          (Set.Ioo_subset_Ioo (hz_mem (k + 1)).1.le (hz_mem k).2.le))
    have hx_ab : x ∈ Set.Ioo a b :=
      ⟨(hz_mem (k + 1)).1.trans hx.1,
        hx.2.trans (hz_mem k).2⟩
    have hlen : 0 < (z k : ℝ) - (z (k + 1) : ℝ) := sub_pos.mpr hzk
    have hD_bound :
        D < base / ((z k : ℝ) - (z (k + 1) : ℝ)) := by
      rw [lt_div_iff₀ hlen]
      have := (lt_div_iff₀ hD).mp hk
      nlinarith
    refine ⟨k + 1, x, hx_ab, ?_⟩
    rw [hderiv, himage_upper, himage_lower]
    have hCD : C < D := by
      dsimp [D]
      linarith [le_max_left C 0]
    have hbase_eq : base = g c - c := by
      dsimp [base]
      rw [he cI]
    rw [hbase_eq] at hD_bound
    exact hCD.trans hD_bound

/-- C¹ endpoint-fixed form of the preceding derivative-growth lemma. -/
theorem polterovichSodin_unbounded_iterate_deriv_c1
    {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hgC1 : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 1 g x)
    (hgpos : ∀ x ∈ Set.Icc a b, 0 < deriv g x)
    (hga : g a = a) (hgb : g b = b)
    (hnontrivial : ∃ c ∈ Set.Ioo a b, g c ≠ c) :
    ∀ C : ℝ, ∃ n : ℕ, ∃ x ∈ Set.Ioo a b,
      C < deriv (g^[n]) x := by
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    intro x hx
    exact (hgC1 x hx).continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (Set.Icc a b) := by
    intro x hx
    exact (hgC1 x hx).differentiableAt_one.differentiableWithinAt
  have hgstrict : StrictMonoOn g (Set.Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hgcont
    intro x hx
    exact hgpos x (interior_subset hx)
  have hgmap : MapsTo g (Set.Icc a b) (Set.Icc a b) := by
    intro x hx
    constructor
    · calc
        a = g a := hga.symm
        _ ≤ g x := hgstrict.monotoneOn
          ⟨le_rfl, hab.le⟩ hx hx.1
    · calc
        g x ≤ g b := hgstrict.monotoneOn
          hx ⟨hab.le, le_rfl⟩ hx.2
        _ = b := hgb
  have hgsurj : Set.SurjOn g (Set.Icc a b) (Set.Icc a b) := by
    simpa [hga, hgb] using
      hgcont.surjOn_Icc
        (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)
        (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩)
  let gI : Set.Icc a b → Set.Icc a b :=
    fun x ↦ ⟨g x, hgmap x.property⟩
  have hgIstrict : StrictMono gI := by
    intro x y hxy
    exact hgstrict x.property y.property hxy
  have hgIsurj : Function.Surjective gI := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hgsurj y.property
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  let e : Set.Icc a b ≃o Set.Icc a b :=
    StrictMono.orderIsoOfSurjective gI hgIstrict hgIsurj
  have he (x : Set.Icc a b) : (e x : ℝ) = g x := rfl
  apply polterovichSodin_unbounded_iterate_deriv hab e he
  · exact hgcont.iterate hgmap
  · intro n
    exact (hgdiff.iterate hgmap n).mono Set.Ioo_subset_Icc_self
  · exact hnontrivial

/-- The variation of a function controls the sum of its changes across an ordered,
pairwise disjoint family of intervals.  The points `z (2 * i)` and
`z (2 * i + 1)` are the two endpoints of the `i`-th interval. -/
theorem sum_edist_orderedPairs_le_eVariationOn
    {ell : ℝ → ℝ} {s : Set ℝ} {z : ℕ → ℝ} {n : ℕ}
    (hzmono : Monotone z)
    (hzmem : ∀ j ≤ 2 * n, z j ∈ s) :
    ∑ i ∈ Finset.range n,
        edist (ell (z (2 * i + 1))) (ell (z (2 * i))) ≤
      eVariationOn ell s := by
  let even : Finset ℕ := (Finset.range n).image (fun i ↦ 2 * i)
  let d : ℕ → ℝ≥0∞ := fun j ↦ edist (ell (z (j + 1))) (ell (z j))
  have hinj : Set.InjOn (fun i : ℕ ↦ 2 * i) (Finset.range n) := by
    have hglobal : Function.Injective (fun i : ℕ ↦ 2 * i) := by
      intro i j hij
      dsimp only at hij
      omega
    exact fun ⦃i⦄ hi ⦃j⦄ hj hij ↦ hglobal hij
  have heven : even ⊆ Finset.range (2 * n) := by
    intro j hj
    simp only [even, Finset.mem_image, Finset.mem_range] at hj ⊢
    rcases hj with ⟨i, hi, rfl⟩
    omega
  calc
    ∑ i ∈ Finset.range n,
        edist (ell (z (2 * i + 1))) (ell (z (2 * i))) =
        ∑ j ∈ even, d j := by
          rw [Finset.sum_image hinj]
    _ ≤ ∑ j ∈ Finset.range (2 * n), d j :=
      Finset.sum_le_sum_of_subset heven
    _ ≤ eVariationOn ell s := by
      exact eVariationOn.sum_le_of_monotoneOn_Iic
        (fun _ hi _ hj hij ↦ hzmono hij) hzmem

/-- Real-valued form of `sum_edist_orderedPairs_le_eVariationOn`. -/
theorem sum_abs_orderedPairs_le_variation
    {ell : ℝ → ℝ} {s : Set ℝ} {z : ℕ → ℝ} {n : ℕ}
    (hBV : BoundedVariationOn ell s)
    (hzmono : Monotone z)
    (hzmem : ∀ j ≤ 2 * n, z j ∈ s) :
    ∑ i ∈ Finset.range n,
        |ell (z (2 * i + 1)) - ell (z (2 * i))| ≤
      (eVariationOn ell s).toReal := by
  have hsum := sum_edist_orderedPairs_le_eVariationOn
    (ell := ell) (s := s) hzmono hzmem
  have hreal := ENNReal.toReal_mono hBV hsum
  rw [ENNReal.toReal_sum (fun _ _ ↦ edist_ne_top _ _)] at hreal
  simpa [edist_dist, Real.dist_eq] using hreal

/-- Chain rule expanded along a finite forward orbit. -/
theorem deriv_iterate_eq_prod
    {f : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (hdiff : ∀ i < n, DifferentiableAt ℝ f ((f^[i]) x)) :
    deriv (f^[n]) x =
      ∏ i ∈ Finset.range n, deriv f ((f^[i]) x) := by
  have hmain : ∀ (m : ℕ) (y : ℝ),
      (∀ i < m, DifferentiableAt ℝ f ((f^[i]) y)) →
      DifferentiableAt ℝ (f^[m]) y ∧
        deriv (f^[m]) y =
          ∏ i ∈ Finset.range m, deriv f ((f^[i]) y) := by
    intro m
    induction m with
    | zero =>
        intro y hy
        simp
    | succ m ih =>
        intro y hy
        have him := ih y (fun i hi ↦ hy i (Nat.lt_succ_of_lt hi))
        have houter : DifferentiableAt ℝ f ((f^[m]) y) := hy m (by omega)
        have hcomp : DifferentiableAt ℝ (f ∘ (f^[m])) y :=
          houter.comp y him.1
        constructor
        · rw [Function.iterate_succ']
          exact hcomp
        · rw [Function.iterate_succ']
          rw [deriv_comp y houter him.1, him.2]
          simp only [Finset.prod_range_succ]
          ac_rfl
  exact (hmain n x hdiff).2

/-- The logarithmic derivative distortion of an iterate is the sum of the
one-step logarithmic derivative distortions along the two orbits. -/
theorem log_deriv_iterate_sub_eq_sum
    {f : ℝ → ℝ} {x y : ℝ} {n : ℕ}
    (hdiffx : ∀ i < n, DifferentiableAt ℝ f ((f^[i]) x))
    (hdiffy : ∀ i < n, DifferentiableAt ℝ f ((f^[i]) y))
    (hposx : ∀ i < n, 0 < deriv f ((f^[i]) x))
    (hposy : ∀ i < n, 0 < deriv f ((f^[i]) y)) :
    Real.log (deriv (f^[n]) y) - Real.log (deriv (f^[n]) x) =
      ∑ i ∈ Finset.range n,
        (Real.log (deriv f ((f^[i]) y)) -
          Real.log (deriv f ((f^[i]) x))) := by
  rw [deriv_iterate_eq_prod hdiffy,
    deriv_iterate_eq_prod hdiffx]
  rw [Real.log_prod (fun i hi ↦
      (hposy i (Finset.mem_range.mp hi)).ne'),
    Real.log_prod (fun i hi ↦
      (hposx i (Finset.mem_range.mp hi)).ne')]
  rw [Finset.sum_sub_distrib]

/-- Ordered, pairwise disjoint orbit intervals turn bounded variation of the
logarithmic derivative into a distortion bound for every iterate. -/
theorem log_deriv_iterate_dist_le_variation_of_orderedPairs
    {f : ℝ → ℝ} {x y : ℝ} {s : Set ℝ}
    (hBV : BoundedVariationOn (fun t ↦ Real.log (deriv f t)) s)
    (hdiffx : ∀ i, DifferentiableAt ℝ f ((f^[i]) x))
    (hdiffy : ∀ i, DifferentiableAt ℝ f ((f^[i]) y))
    (hposx : ∀ i, 0 < deriv f ((f^[i]) x))
    (hposy : ∀ i, 0 < deriv f ((f^[i]) y))
    (z : ℕ → ℕ → ℝ)
    (hzmono : ∀ n, Monotone (z n))
    (hzmem : ∀ n j, j ≤ 2 * n → z n j ∈ s)
    (hzpair : ∀ n i, i < n →
      (z n (2 * i) = (f^[i]) x ∧ z n (2 * i + 1) = (f^[i]) y) ∨
      (z n (2 * i) = (f^[i]) y ∧ z n (2 * i + 1) = (f^[i]) x)) :
    ∀ n,
      |Real.log (deriv (f^[n]) y) - Real.log (deriv (f^[n]) x)| ≤
        (eVariationOn (fun t ↦ Real.log (deriv f t)) s).toReal := by
  intro n
  rw [log_deriv_iterate_sub_eq_sum
    (fun i hi ↦ hdiffx i) (fun i hi ↦ hdiffy i)
    (fun i hi ↦ hposx i) (fun i hi ↦ hposy i)]
  calc
    |∑ i ∈ Finset.range n,
        (Real.log (deriv f ((f^[i]) y)) -
          Real.log (deriv f ((f^[i]) x)))| ≤
        ∑ i ∈ Finset.range n,
          |Real.log (deriv f ((f^[i]) y)) -
            Real.log (deriv f ((f^[i]) x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n,
        |Real.log (deriv f (z n (2 * i + 1))) -
          Real.log (deriv f (z n (2 * i)))| := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hzpair n i (Finset.mem_range.mp hi) with h | h
      · rw [h.1, h.2]
      · rw [h.1, h.2, abs_sub_comm]
    _ ≤ (eVariationOn (fun t ↦ Real.log (deriv f t)) s).toReal := by
      exact sum_abs_orderedPairs_le_variation hBV
        (hzmono n) (hzmem n)

/-- Ordered-pair variation bound over an arbitrary linearly ordered domain. -/
theorem sum_abs_orderedPairs_le_variation_generic
    {α : Type*} [LinearOrder α]
    {ell : α → ℝ} {s : Set α} {z : ℕ → α} {n : ℕ}
    (hBV : BoundedVariationOn ell s)
    (hzmono : Monotone z)
    (hzmem : ∀ j ≤ 2 * n, z j ∈ s) :
    ∑ i ∈ Finset.range n,
        |ell (z (2 * i + 1)) - ell (z (2 * i))| ≤
      (eVariationOn ell s).toReal := by
  let even : Finset ℕ := (Finset.range n).image (fun i ↦ 2 * i)
  let delta : ℕ → ℝ≥0∞ := fun j ↦ edist (ell (z (j + 1))) (ell (z j))
  have hinj : Set.InjOn (fun i : ℕ ↦ 2 * i) (Finset.range n) := by
    have hglobal : Function.Injective (fun i : ℕ ↦ 2 * i) := by
      intro i j hij
      dsimp only at hij
      omega
    exact fun ⦃i⦄ hi ⦃j⦄ hj hij ↦ hglobal hij
  have heven : even ⊆ Finset.range (2 * n) := by
    intro j hj
    simp only [even, Finset.mem_image, Finset.mem_range] at hj ⊢
    rcases hj with ⟨i, hi, rfl⟩
    omega
  have hsum :
      ∑ i ∈ Finset.range n,
          edist (ell (z (2 * i + 1))) (ell (z (2 * i))) ≤
        eVariationOn ell s := by
    calc
      ∑ i ∈ Finset.range n,
          edist (ell (z (2 * i + 1))) (ell (z (2 * i))) =
          ∑ j ∈ even, delta j := by
            rw [Finset.sum_image hinj]
      _ ≤ ∑ j ∈ Finset.range (2 * n), delta j :=
        Finset.sum_le_sum_of_subset heven
      _ ≤ eVariationOn ell s := by
        exact eVariationOn.sum_le_of_monotoneOn_Iic
          (fun _ hi _ hj hij ↦ hzmono hij) hzmem
  have hreal := ENNReal.toReal_mono hBV hsum
  rw [ENNReal.toReal_sum (fun _ _ ↦ edist_ne_top _ _)] at hreal
  simpa [edist_dist, Real.dist_eq] using hreal

/-- Bounded variation also controls ordered pairs listed in decreasing order. -/
theorem sum_abs_antitonePairs_le_variation
    {ell : ℝ → ℝ} {s : Set ℝ} {z : ℕ → ℝ} {n : ℕ}
    (hBV : BoundedVariationOn ell s)
    (hzanti : Antitone z)
    (hzmem : ∀ j ≤ 2 * n, z j ∈ s) :
    ∑ i ∈ Finset.range n,
        |ell (z (2 * i + 1)) - ell (z (2 * i))| ≤
      (eVariationOn ell s).toReal := by
  let zDual : ℕ → ℝᵒᵈ := fun j ↦ OrderDual.toDual (z j)
  have hzmono : Monotone zDual := by
    intro i j hij
    exact hzanti hij
  have hzmemDual : ∀ j ≤ 2 * n,
      zDual j ∈ OrderDual.ofDual ⁻¹' s := by
    intro j hj
    exact hzmem j hj
  have hdual := sum_abs_orderedPairs_le_variation_generic
    (ell := ell ∘ OrderDual.ofDual)
    (s := OrderDual.ofDual ⁻¹' s)
    (z := zDual) hBV.ofDual hzmono hzmemDual
  rw [eVariationOn.comp_ofDual] at hdual
  simpa [zDual, Function.comp_def] using hdual

/-- Orientation-neutral bounded-distortion bridge for fundamental intervals:
the intervals may be listed either increasingly or decreasingly. -/
theorem log_deriv_iterate_dist_le_variation_of_orderedPairs_monoOrAnti
    {f : ℝ → ℝ} {x y : ℝ} {s : Set ℝ}
    (hBV : BoundedVariationOn (fun t ↦ Real.log (deriv f t)) s)
    (hdiffx : ∀ i, DifferentiableAt ℝ f ((f^[i]) x))
    (hdiffy : ∀ i, DifferentiableAt ℝ f ((f^[i]) y))
    (hposx : ∀ i, 0 < deriv f ((f^[i]) x))
    (hposy : ∀ i, 0 < deriv f ((f^[i]) y))
    (z : ℕ → ℕ → ℝ)
    (hzord : ∀ n, Monotone (z n) ∨ Antitone (z n))
    (hzmem : ∀ n j, j ≤ 2 * n → z n j ∈ s)
    (hzpair : ∀ n i, i < n →
      (z n (2 * i) = (f^[i]) x ∧ z n (2 * i + 1) = (f^[i]) y) ∨
      (z n (2 * i) = (f^[i]) y ∧ z n (2 * i + 1) = (f^[i]) x)) :
    ∀ n,
      |Real.log (deriv (f^[n]) y) - Real.log (deriv (f^[n]) x)| ≤
        (eVariationOn (fun t ↦ Real.log (deriv f t)) s).toReal := by
  intro n
  rw [log_deriv_iterate_sub_eq_sum
    (fun i hi ↦ hdiffx i) (fun i hi ↦ hdiffy i)
    (fun i hi ↦ hposx i) (fun i hi ↦ hposy i)]
  calc
    |∑ i ∈ Finset.range n,
        (Real.log (deriv f ((f^[i]) y)) -
          Real.log (deriv f ((f^[i]) x)))| ≤
        ∑ i ∈ Finset.range n,
          |Real.log (deriv f ((f^[i]) y)) -
            Real.log (deriv f ((f^[i]) x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n,
        |Real.log (deriv f (z n (2 * i + 1))) -
          Real.log (deriv f (z n (2 * i)))| := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases hzpair n i (Finset.mem_range.mp hi) with h | h
      · rw [h.1, h.2]
      · rw [h.1, h.2, abs_sub_comm]
    _ ≤ (eVariationOn (fun t ↦ Real.log (deriv f t)) s).toReal := by
      rcases hzord n with hmono | hanti
      · exact sum_abs_orderedPairs_le_variation hBV hmono (hzmem n)
      · exact sum_abs_antitonePairs_le_variation hBV hanti (hzmem n)

/-- Differentiate the equality of the two orders of commuting iterates. -/
theorem deriv_commuting_iterates_identity
    {f g : ℝ → ℝ} {x : ℝ} {n k : ℕ}
    (hcomm : Function.Commute f g)
    (hfn_x : DifferentiableAt ℝ (f^[n]) x)
    (hfn_gx : DifferentiableAt ℝ (f^[n]) ((g^[k]) x))
    (hgk_x : DifferentiableAt ℝ (g^[k]) x)
    (hgk_fx : DifferentiableAt ℝ (g^[k]) ((f^[n]) x)) :
    deriv (g^[k]) ((f^[n]) x) * deriv (f^[n]) x =
      deriv (f^[n]) ((g^[k]) x) * deriv (g^[k]) x := by
  have heq : (g^[k]) ∘ (f^[n]) = (f^[n]) ∘ (g^[k]) :=
    funext fun y ↦ ((hcomm.iterate_iterate n k).eq y).symm
  have hderiv := congrArg (fun h : ℝ → ℝ ↦ deriv h x) heq
  change deriv ((g^[k]) ∘ (f^[n])) x =
    deriv ((f^[n]) ∘ (g^[k])) x at hderiv
  rw [deriv_comp x hgk_fx hfn_x, deriv_comp x hfn_gx hgk_x] at hderiv
  exact hderiv

/-- Continuity forces the limit of a sequence of fixed points to be fixed. -/
theorem fixedPoint_of_fixedPoints_tendsto
    {g : ℝ → ℝ} {a : ℝ} {q : ℕ → ℝ}
    (hg : ContinuousAt g a)
    (hq : Tendsto q atTop (𝓝 a))
    (hfix : ∀ i, g (q i) = q i) :
    g a = a := by
  have hgq : Tendsto (fun i ↦ g (q i)) atTop (𝓝 (g a)) :=
    hg.tendsto.comp hq
  have heq : (fun i ↦ g (q i)) = q := funext hfix
  rw [heq] at hgq
  exact tendsto_nhds_unique hgq hq

/-- A differentiable map with nontrivial fixed points accumulating at `a` has
derivative one at `a`. -/
theorem deriv_eq_one_of_fixedPoints_tendsto
    {g : ℝ → ℝ} {a : ℝ} {q : ℕ → ℝ}
    (hg : ContDiffAt ℝ 1 g a)
    (hq : Tendsto q atTop (𝓝 a))
    (hqne : ∀ i, q i ≠ a)
    (hfix : ∀ i, g (q i) = q i) :
    deriv g a = 1 := by
  have hga : g a = a :=
    fixedPoint_of_fixedPoints_tendsto hg.continuousAt hq hfix
  have hqWithin : Tendsto q atTop (𝓝[≠] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hq, Filter.Eventually.of_forall ?_⟩
    intro i
    simpa using hqne i
  have hslope : Tendsto (fun i ↦ slope g a (q i)) atTop (𝓝 (deriv g a)) := by
    simpa [Function.comp_def] using
      hg.differentiableAt_one.hasDerivAt.tendsto_slope.comp hqWithin
  have hslope_one : (fun i ↦ slope g a (q i)) = (fun _ : ℕ ↦ (1 : ℝ)) := by
    funext i
    rw [slope_def_field, hfix i, hga]
    exact div_self (sub_ne_zero.mpr (hqne i))
  rw [hslope_one] at hslope
  exact tendsto_nhds_unique hslope tendsto_const_nhds

/-- A `C¹` map is `C¹` at every finite iterate of a fixed point. -/
theorem contDiffAt_iterate_of_fixed
    {g : ℝ → ℝ} {a : ℝ}
    (hg : ContDiffAt ℝ 1 g a)
    (hfix : g a = a) :
    ∀ k, ContDiffAt ℝ 1 (g^[k]) a := by
  intro k
  induction k with
  | zero =>
      simpa using (contDiffAt_id : ContDiffAt ℝ 1 (id : ℝ → ℝ) a)
  | succ k ih =>
      have hkfix : (g^[k]) a = a := Function.IsFixedPt.iterate hfix k
      have hg_at : ContDiffAt ℝ 1 g ((g^[k]) a) := by
        simpa [hkfix] using hg
      have hcomp : ContDiffAt ℝ 1 (g ∘ (g^[k])) a :=
        hg_at.comp a ih
      rw [Function.iterate_succ']
      exact hcomp

/-- At a fixed point, the derivative of the `k`-th iterate is the `k`-th
power of the derivative. -/
theorem deriv_iterate_at_fixed_eq_pow
    {g : ℝ → ℝ} {a : ℝ}
    (hg : ContDiffAt ℝ 1 g a)
    (hfix : g a = a) :
    ∀ k, deriv (g^[k]) a = (deriv g a) ^ k := by
  intro k
  have hiter (i : ℕ) : (g^[i]) a = a :=
    Function.IsFixedPt.iterate hfix i
  rw [deriv_iterate_eq_prod (fun i hi ↦ by
    simpa [hiter i] using hg.differentiableAt_one)]
  simp [hiter]

/-- If an orbit contracts to a fixed point at which `g' = 1`, then the
derivatives of each fixed iterate of `g` along that orbit tend to one. -/
theorem tendsto_deriv_iterate_along_contraction
    {f g : ℝ → ℝ} {a x : ℝ} {k : ℕ}
    (hg : ContDiffAt ℝ 1 g a)
    (hfix : g a = a)
    (hderiv : deriv g a = 1)
    (horbit : Tendsto (fun n ↦ (f^[n]) x) atTop (𝓝 a)) :
    Tendsto (fun n ↦ deriv (g^[k]) ((f^[n]) x)) atTop (𝓝 1) := by
  have hgk : ContDiffAt ℝ 1 (g^[k]) a :=
    contDiffAt_iterate_of_fixed hg hfix k
  have hderiv_cont : ContinuousAt (deriv (g^[k])) a :=
    (hgk.derivWithin (m := 0) (by norm_num)).continuousAt
  have hlim := hderiv_cont.tendsto.comp horbit
  have hvalue : deriv (g^[k]) a = 1 := by
    rw [deriv_iterate_at_fixed_eq_pow hg hfix k, hderiv]
    simp
  simpa [hvalue] using hlim

/-- Analytic core of the distortion estimate.  The chain-rule identity and
bounded logarithmic distortion force the initial derivative to be at most
`exp V` once the derivatives at the contracted orbit tend to one. -/
theorem scalar_deriv_le_exp_of_chain_logDistortion_tendsto
    {A B C : ℕ → ℝ} {D V : ℝ}
    (hA : Tendsto A atTop (𝓝 1))
    (hApos : ∀ n, 0 < A n)
    (hBpos : ∀ n, 0 < B n)
    (hCpos : ∀ n, 0 < C n)
    (hchain : ∀ n, A n * B n = C n * D)
    (hdist : ∀ n, |Real.log (B n) - Real.log (C n)| ≤ V) :
    D ≤ Real.exp V := by
  have hratio (n : ℕ) : B n / C n ≤ Real.exp V := by
    calc
      B n / C n = Real.exp (Real.log (B n) - Real.log (C n)) := by
        rw [Real.exp_sub, Real.exp_log (hBpos n), Real.exp_log (hCpos n)]
      _ ≤ Real.exp V := Real.exp_le_exp.mpr <|
        (le_abs_self (Real.log (B n) - Real.log (C n))).trans (hdist n)
  have hupper (n : ℕ) : D ≤ A n * Real.exp V := by
    have hD : D = A n * (B n / C n) := by
      calc
        D = C n * D / C n := by
          rw [mul_div_cancel_left₀ D (hCpos n).ne']
        _ = A n * B n / C n := by rw [← hchain n]
        _ = A n * (B n / C n) := by ring
    rw [hD]
    exact mul_le_mul_of_nonneg_left (hratio n) (hApos n).le
  have hlim : Tendsto (fun n ↦ A n * Real.exp V) atTop (𝓝 (Real.exp V)) := by
    simpa using hA.mul_const (Real.exp V)
  exact ge_of_tendsto' hlim hupper

/-- Derivative bound for commuting iterates, with the contraction-limit and
logarithmic distortion estimates exposed as explicit hypotheses. -/
theorem commuting_iterate_deriv_le_exp_of_logDistortion_tendsto
    {f g : ℝ → ℝ} {x : ℝ} {k : ℕ} {V : ℝ}
    (hcomm : Function.Commute f g)
    (hfn_x : ∀ n, DifferentiableAt ℝ (f^[n]) x)
    (hfn_gx : ∀ n, DifferentiableAt ℝ (f^[n]) ((g^[k]) x))
    (hgk_x : DifferentiableAt ℝ (g^[k]) x)
    (hgk_fx : ∀ n, DifferentiableAt ℝ (g^[k]) ((f^[n]) x))
    (hfn_x_pos : ∀ n, 0 < deriv (f^[n]) x)
    (hfn_gx_pos : ∀ n, 0 < deriv (f^[n]) ((g^[k]) x))
    (hgk_fx_pos : ∀ n, 0 < deriv (g^[k]) ((f^[n]) x))
    (hlimit : Tendsto (fun n ↦ deriv (g^[k]) ((f^[n]) x)) atTop (𝓝 1))
    (hdist : ∀ n,
      |Real.log (deriv (f^[n]) x) -
        Real.log (deriv (f^[n]) ((g^[k]) x))| ≤ V) :
    deriv (g^[k]) x ≤ Real.exp V := by
  apply scalar_deriv_le_exp_of_chain_logDistortion_tendsto
    hlimit hgk_fx_pos hfn_x_pos hfn_gx_pos
  · intro n
    exact deriv_commuting_iterates_identity hcomm
      (hfn_x n) (hfn_gx n) hgk_x (hgk_fx n)
  · exact hdist

/-- Endpoint-derived version: an accumulating sequence of fixed points gives
`g'(a) = 1`, and contraction of the `f`-orbit supplies the limit hypothesis
needed by the preceding distortion estimate. -/
theorem commuting_iterate_deriv_le_exp_of_logDistortion_fixedPoints
    {f g : ℝ → ℝ} {a x : ℝ} {q : ℕ → ℝ} {k : ℕ} {V : ℝ}
    (hcomm : Function.Commute f g)
    (hg : ContDiffAt ℝ 1 g a)
    (hq : Tendsto q atTop (𝓝 a))
    (hqne : ∀ i, q i ≠ a)
    (hqfix : ∀ i, g (q i) = q i)
    (horbit : Tendsto (fun n ↦ (f^[n]) x) atTop (𝓝 a))
    (hfn_x : ∀ n, DifferentiableAt ℝ (f^[n]) x)
    (hfn_gx : ∀ n, DifferentiableAt ℝ (f^[n]) ((g^[k]) x))
    (hgk_x : DifferentiableAt ℝ (g^[k]) x)
    (hgk_fx : ∀ n, DifferentiableAt ℝ (g^[k]) ((f^[n]) x))
    (hfn_x_pos : ∀ n, 0 < deriv (f^[n]) x)
    (hfn_gx_pos : ∀ n, 0 < deriv (f^[n]) ((g^[k]) x))
    (hgk_fx_pos : ∀ n, 0 < deriv (g^[k]) ((f^[n]) x))
    (hdist : ∀ n,
      |Real.log (deriv (f^[n]) x) -
        Real.log (deriv (f^[n]) ((g^[k]) x))| ≤ V) :
    deriv (g^[k]) x ≤ Real.exp V := by
  have hga : g a = a :=
    fixedPoint_of_fixedPoints_tendsto hg.continuousAt hq hqfix
  have hderiv : deriv g a = 1 :=
    deriv_eq_one_of_fixedPoints_tendsto hg hq hqne hqfix
  have hlimit :
      Tendsto (fun n ↦ deriv (g^[k]) ((f^[n]) x)) atTop (𝓝 1) :=
    tendsto_deriv_iterate_along_contraction hg hga hderiv horbit
  exact commuting_iterate_deriv_le_exp_of_logDistortion_tendsto
    hcomm hfn_x hfn_gx hgk_x hgk_fx hfn_x_pos hfn_gx_pos hgk_fx_pos
    hlimit hdist

/-- Positive one-step derivatives give positive derivatives for every finite
iterate. -/
theorem deriv_iterate_pos_of_deriv_pos
    {f : ℝ → ℝ}
    (hfdiff : Differentiable ℝ f)
    (hfpos : ∀ x, 0 < deriv f x) :
    ∀ n x, 0 < deriv (f^[n]) x := by
  intro n x
  rw [deriv_iterate_eq_prod (fun i hi ↦ hfdiff ((f^[i]) x))]
  exact Finset.prod_pos fun i hi ↦ hfpos ((f^[i]) x)

/-- Contracting real Kopell core.  The monotone interleavings explicitly
record the sole geometric input: the images under `f` of the fundamental
interval between `x` and `(g^[k]) x` are pairwise ordered and disjoint.

The other assumptions are exactly the global real-function data used by the
bounded-distortion estimate and the compact-interval data used by
Polterovich--Sodin. -/
theorem contracting_kopell_core
    {f g : ℝ → ℝ} {a c d : ℝ} {s : Set ℝ}
    (hcd : c < d)
    (e : Set.Icc c d ≃o Set.Icc c d)
    (he : ∀ x : Set.Icc c d, (e x : ℝ) = g x)
    (hcomm : Function.Commute f g)
    (hfdiff : Differentiable ℝ f)
    (hgdiff : Differentiable ℝ g)
    (hfpos : ∀ x, 0 < deriv f x)
    (hgpos : ∀ x, 0 < deriv g x)
    (hgC1a : ContDiffAt ℝ 1 g a)
    (q : ℕ → ℝ)
    (hq : Tendsto q atTop (𝓝 a))
    (hqne : ∀ i, q i ≠ a)
    (hqfix : ∀ i, g (q i) = q i)
    (horbit : ∀ x ∈ Set.Ioo c d,
      Tendsto (fun n ↦ (f^[n]) x) atTop (𝓝 a))
    (hBV : BoundedVariationOn (fun t ↦ Real.log (deriv f t)) s)
    (hordered : ∀ x ∈ Set.Ioo c d, ∀ k,
      ∃ z : ℕ → ℕ → ℝ,
        (∀ n, Monotone (z n) ∨ Antitone (z n)) ∧
        (∀ n j, j ≤ 2 * n → z n j ∈ s) ∧
        (∀ n i, i < n →
          (z n (2 * i) = (f^[i]) x ∧
            z n (2 * i + 1) = (f^[i]) ((g^[k]) x)) ∨
          (z n (2 * i) = (f^[i]) ((g^[k]) x) ∧
            z n (2 * i + 1) = (f^[i]) x))) :
    ∀ x ∈ Set.Ioo c d, g x = x := by
  by_contra hfixed
  push Not at hfixed
  have hgiter_cont (n : ℕ) : ContinuousOn (g^[n]) (Set.Icc c d) :=
    (hgdiff.iterate n).continuous.continuousOn
  have hgiter_diff (n : ℕ) : DifferentiableOn ℝ (g^[n]) (Set.Ioo c d) :=
    fun x hx ↦ (hgdiff.iterate n x).differentiableWithinAt
  have hgrowth := polterovichSodin_unbounded_iterate_deriv
    hcd e he hgiter_cont hgiter_diff hfixed
  let V : ℝ :=
    (eVariationOn (fun t ↦ Real.log (deriv f t)) s).toReal
  obtain ⟨k, x, hx, hlarge⟩ := hgrowth (Real.exp V)
  rcases hordered x hx k with ⟨z, hzmono, hzmem, hzpair⟩
  have hdist₀ :=
    log_deriv_iterate_dist_le_variation_of_orderedPairs_monoOrAnti
    hBV
    (fun i ↦ hfdiff ((f^[i]) x))
    (fun i ↦ hfdiff ((f^[i]) ((g^[k]) x)))
    (fun i ↦ hfpos ((f^[i]) x))
    (fun i ↦ hfpos ((f^[i]) ((g^[k]) x)))
    z hzmono hzmem hzpair
  have hdist (n : ℕ) :
      |Real.log (deriv (f^[n]) x) -
        Real.log (deriv (f^[n]) ((g^[k]) x))| ≤ V := by
    simpa [V, abs_sub_comm] using hdist₀ n
  have hbound : deriv (g^[k]) x ≤ Real.exp V :=
    commuting_iterate_deriv_le_exp_of_logDistortion_fixedPoints
      hcomm hgC1a hq hqne hqfix (horbit x hx)
      (fun n ↦ hfdiff.iterate n x)
      (fun n ↦ hfdiff.iterate n ((g^[k]) x))
      (hgdiff.iterate k x)
      (fun n ↦ hgdiff.iterate k ((f^[n]) x))
      (fun n ↦ deriv_iterate_pos_of_deriv_pos hfdiff hfpos n x)
      (fun n ↦ deriv_iterate_pos_of_deriv_pos hfdiff hfpos n
        ((g^[k]) x))
      (fun n ↦ deriv_iterate_pos_of_deriv_pos hgdiff hgpos k
        ((f^[n]) x))
      hdist
  exact (not_lt_of_ge hbound) hlarge

/-- Commutation on an invariant set propagates to every pair of positive
iterates on that set. -/
theorem eqOn_iterates_of_commuteOn_mapsTo
    {α : Type*} {f g : α → α} {s : Set α} {n k : ℕ}
    (hcomm : Set.EqOn (f ∘ g) (g ∘ f) s)
    (hfmap : Set.MapsTo f s s)
    (hgmap : Set.MapsTo g s s) :
    Set.EqOn ((f^[n]) ∘ (g^[k])) ((g^[k]) ∘ (f^[n])) s := by
  have hf_comm_giter : ∀ m,
      Set.EqOn (f ∘ (g^[m])) ((g^[m]) ∘ f) s := by
    intro m
    induction m with
    | zero =>
        intro x hx
        simp
    | succ m ih =>
        intro x hx
        simp only [Function.comp_apply, Function.iterate_succ_apply']
        calc
          f (g ((g^[m]) x)) = g (f ((g^[m]) x)) :=
            hcomm (hgmap.iterate m hx)
          _ = g ((g^[m]) (f x)) := congrArg g (ih hx)
  have hiter_comm : ∀ m,
      Set.EqOn ((f^[m]) ∘ (g^[k])) ((g^[k]) ∘ (f^[m])) s := by
    intro m
    induction m with
    | zero =>
        intro x hx
        simp
    | succ m ih =>
        intro x hx
        simp only [Function.comp_apply, Function.iterate_succ_apply']
        calc
          f ((f^[m]) ((g^[k]) x)) = f ((g^[k]) ((f^[m]) x)) :=
            congrArg f (ih hx)
          _ = (g^[k]) (f ((f^[m]) x)) :=
            hf_comm_giter k (hfmap.iterate m hx)
  exact hiter_comm n

/-- Local chain-rule identity.  Global commutation is unnecessary: equality
on an invariant neighborhood of the differentiation point suffices. -/
theorem deriv_commuting_iterates_identity_of_eqOn_nhds
    {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ} {n k : ℕ}
    (hcomm : Set.EqOn (f ∘ g) (g ∘ f) s)
    (hfmap : Set.MapsTo f s s)
    (hgmap : Set.MapsTo g s s)
    (hsx : s ∈ 𝓝 x)
    (hfn_x : DifferentiableAt ℝ (f^[n]) x)
    (hfn_gx : DifferentiableAt ℝ (f^[n]) ((g^[k]) x))
    (hgk_x : DifferentiableAt ℝ (g^[k]) x)
    (hgk_fx : DifferentiableAt ℝ (g^[k]) ((f^[n]) x)) :
    deriv (g^[k]) ((f^[n]) x) * deriv (f^[n]) x =
      deriv (f^[n]) ((g^[k]) x) * deriv (g^[k]) x := by
  have heqOn := eqOn_iterates_of_commuteOn_mapsTo
    (n := n) (k := k) hcomm hfmap hgmap
  have hevent :
      ((f^[n]) ∘ (g^[k])) =ᶠ[𝓝 x] ((g^[k]) ∘ (f^[n])) := by
    filter_upwards [hsx] with y hy
    exact heqOn hy
  have hderiv := hevent.deriv_eq
  rw [deriv_comp x hfn_gx hgk_x,
    deriv_comp x hgk_fx hfn_x] at hderiv
  exact hderiv.symm

/-- Endpoint-derived derivative bound with the exact chain identities exposed,
so no global commutation hypothesis is needed. -/
theorem iterate_deriv_le_exp_of_logDistortion_fixedPoints_of_chain
    {f g : ℝ → ℝ} {a x : ℝ} {q : ℕ → ℝ} {k : ℕ} {V : ℝ}
    (hg : ContDiffAt ℝ 1 g a)
    (hq : Tendsto q atTop (𝓝 a))
    (hqne : ∀ i, q i ≠ a)
    (hqfix : ∀ i, g (q i) = q i)
    (horbit : Tendsto (fun n ↦ (f^[n]) x) atTop (𝓝 a))
    (hfn_x_pos : ∀ n, 0 < deriv (f^[n]) x)
    (hfn_gx_pos : ∀ n, 0 < deriv (f^[n]) ((g^[k]) x))
    (hgk_fx_pos : ∀ n, 0 < deriv (g^[k]) ((f^[n]) x))
    (hchain : ∀ n,
      deriv (g^[k]) ((f^[n]) x) * deriv (f^[n]) x =
        deriv (f^[n]) ((g^[k]) x) * deriv (g^[k]) x)
    (hdist : ∀ n,
      |Real.log (deriv (f^[n]) x) -
        Real.log (deriv (f^[n]) ((g^[k]) x))| ≤ V) :
    deriv (g^[k]) x ≤ Real.exp V := by
  have hga : g a = a :=
    fixedPoint_of_fixedPoints_tendsto hg.continuousAt hq hqfix
  have hderiv : deriv g a = 1 :=
    deriv_eq_one_of_fixedPoints_tendsto hg hq hqne hqfix
  have hlimit :
      Tendsto (fun n ↦ deriv (g^[k]) ((f^[n]) x)) atTop (𝓝 1) :=
    tendsto_deriv_iterate_along_contraction hg hga hderiv horbit
  exact scalar_deriv_le_exp_of_chain_logDistortion_tendsto
    hlimit hgk_fx_pos hfn_x_pos hfn_gx_pos hchain hdist

/-- Local contracting Kopell core: the only commutation datum retained is the
pointwise derivative-chain identity used by distortion. -/
theorem contracting_kopell_core_of_chain
    {f g : ℝ → ℝ} {a c d : ℝ} {s : Set ℝ}
    (hcd : c < d)
    (e : Set.Icc c d ≃o Set.Icc c d)
    (he : ∀ x : Set.Icc c d, (e x : ℝ) = g x)
    (hfdiff : Differentiable ℝ f)
    (hgdiff : Differentiable ℝ g)
    (hfpos : ∀ x, 0 < deriv f x)
    (hgpos : ∀ x, 0 < deriv g x)
    (hgC1a : ContDiffAt ℝ 1 g a)
    (q : ℕ → ℝ)
    (hq : Tendsto q atTop (𝓝 a))
    (hqne : ∀ i, q i ≠ a)
    (hqfix : ∀ i, g (q i) = q i)
    (horbit : ∀ x ∈ Set.Ioo c d,
      Tendsto (fun n ↦ (f^[n]) x) atTop (𝓝 a))
    (hBV : BoundedVariationOn (fun t ↦ Real.log (deriv f t)) s)
    (hordered : ∀ x ∈ Set.Ioo c d, ∀ k,
      ∃ z : ℕ → ℕ → ℝ,
        (∀ n, Monotone (z n) ∨ Antitone (z n)) ∧
        (∀ n j, j ≤ 2 * n → z n j ∈ s) ∧
        (∀ n i, i < n →
          (z n (2 * i) = (f^[i]) x ∧
            z n (2 * i + 1) = (f^[i]) ((g^[k]) x)) ∨
          (z n (2 * i) = (f^[i]) ((g^[k]) x) ∧
            z n (2 * i + 1) = (f^[i]) x)))
    (hchain : ∀ x ∈ Set.Ioo c d, ∀ k n,
      deriv (g^[k]) ((f^[n]) x) * deriv (f^[n]) x =
        deriv (f^[n]) ((g^[k]) x) * deriv (g^[k]) x) :
    ∀ x ∈ Set.Ioo c d, g x = x := by
  by_contra hfixed
  push Not at hfixed
  have hgiter_cont (n : ℕ) : ContinuousOn (g^[n]) (Set.Icc c d) :=
    (hgdiff.iterate n).continuous.continuousOn
  have hgiter_diff (n : ℕ) : DifferentiableOn ℝ (g^[n]) (Set.Ioo c d) :=
    fun x hx ↦ (hgdiff.iterate n x).differentiableWithinAt
  have hgrowth := polterovichSodin_unbounded_iterate_deriv
    hcd e he hgiter_cont hgiter_diff hfixed
  let V : ℝ :=
    (eVariationOn (fun t ↦ Real.log (deriv f t)) s).toReal
  obtain ⟨k, x, hx, hlarge⟩ := hgrowth (Real.exp V)
  rcases hordered x hx k with ⟨z, hzmono, hzmem, hzpair⟩
  have hdist₀ :=
    log_deriv_iterate_dist_le_variation_of_orderedPairs_monoOrAnti
      hBV
      (fun i ↦ hfdiff ((f^[i]) x))
      (fun i ↦ hfdiff ((f^[i]) ((g^[k]) x)))
      (fun i ↦ hfpos ((f^[i]) x))
      (fun i ↦ hfpos ((f^[i]) ((g^[k]) x)))
      z hzmono hzmem hzpair
  have hdist (n : ℕ) :
      |Real.log (deriv (f^[n]) x) -
        Real.log (deriv (f^[n]) ((g^[k]) x))| ≤ V := by
    simpa [V, abs_sub_comm] using hdist₀ n
  have hbound : deriv (g^[k]) x ≤ Real.exp V :=
    iterate_deriv_le_exp_of_logDistortion_fixedPoints_of_chain
      hgC1a hq hqne hqfix (horbit x hx)
      (fun n ↦ deriv_iterate_pos_of_deriv_pos hfdiff hfpos n x)
      (fun n ↦ deriv_iterate_pos_of_deriv_pos hfdiff hfpos n ((g^[k]) x))
      (fun n ↦ deriv_iterate_pos_of_deriv_pos hgdiff hgpos k ((f^[n]) x))
      (hchain x hx k) hdist
  exact (not_lt_of_ge hbound) hlarge

/-- Interleave the endpoints of successively leftward ordered intervals.
Within each pair the larger endpoint is listed first, so the full sequence is
antitone. -/
theorem exists_antitoneInterleaving_of_orderedPairs
    {X Y : ℕ → ℝ} {s : Set ℝ}
    (hsep : ∀ i, max (X (i + 1)) (Y (i + 1)) ≤ min (X i) (Y i))
    (hXmem : ∀ i, X i ∈ s)
    (hYmem : ∀ i, Y i ∈ s) :
    ∃ z : ℕ → ℝ,
      Antitone z ∧
      (∀ j, z j ∈ s) ∧
      (∀ i,
        (z (2 * i) = X i ∧ z (2 * i + 1) = Y i) ∨
        (z (2 * i) = Y i ∧ z (2 * i + 1) = X i)) := by
  let z : ℕ → ℝ := fun j ↦
    if j % 2 = 0 then max (X (j / 2)) (Y (j / 2))
    else min (X (j / 2)) (Y (j / 2))
  refine ⟨z, ?_, ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro j
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · have hmod0 : (2 * i) % 2 = 0 := by omega
      have hmod1 : (2 * i + 1) % 2 = 1 := by omega
      have hdiv0 : (2 * i) / 2 = i := by omega
      have hdiv1 : (2 * i + 1) / 2 = i := by omega
      simp [z, hmod0, hmod1, hdiv0, hdiv1]
    · have hmod1 : (2 * i + 1) % 2 = 1 := by omega
      have hmod2 : (2 * i + 1 + 1) % 2 = 0 := by omega
      have hdiv1 : (2 * i + 1) / 2 = i := by omega
      have hdiv2 : (2 * i + 1 + 1) / 2 = i + 1 := by omega
      simpa [z, hmod1, hmod2, hdiv1, hdiv2] using hsep i
  · intro j
    simp only [z]
    split
    · rcases max_choice (X (j / 2)) (Y (j / 2)) with h | h
      · rw [h]
        exact hXmem _
      · rw [h]
        exact hYmem _
    · rcases min_choice (X (j / 2)) (Y (j / 2)) with h | h
      · rw [h]
        exact hXmem _
      · rw [h]
        exact hYmem _
  · intro i
    have hmod0 : (2 * i) % 2 = 0 := by omega
    have hmod1 : (2 * i + 1) % 2 = 1 := by omega
    have hdiv0 : (2 * i) / 2 = i := by omega
    have hdiv1 : (2 * i + 1) / 2 = i := by omega
    rcases le_total (X i) (Y i) with h | h
    · right
      simp [z, hmod0, hmod1, hdiv0, hdiv1,
        max_eq_right h, min_eq_left h]
    · left
      simp [z, hmod0, hmod1, hdiv0, hdiv1,
        max_eq_left h, min_eq_right h]

/-- Points lying in successive disjoint component images inherit their
leftward separation. -/
theorem orbit_pairs_separated_of_component_images
    {f : ℝ → ℝ} {c d x y : ℝ}
    (hfstrict : StrictMono f)
    (hx : x ∈ Set.Ioo c d)
    (hy : y ∈ Set.Ioo c d)
    (hcomponents : ∀ i, (f^[i + 1]) d ≤ (f^[i]) c) :
    ∀ i,
      max ((f^[i + 1]) x) ((f^[i + 1]) y) ≤
        min ((f^[i]) x) ((f^[i]) y) := by
  intro i
  have hnext :
      max ((f^[i + 1]) x) ((f^[i + 1]) y) < (f^[i + 1]) d := by
    rw [max_lt_iff]
    exact ⟨(hfstrict.iterate (i + 1)) hx.2,
      (hfstrict.iterate (i + 1)) hy.2⟩
  have hprev : (f^[i]) c < min ((f^[i]) x) ((f^[i]) y) := by
    rw [lt_min_iff]
    exact ⟨(hfstrict.iterate i) hx.1, (hfstrict.iterate i) hy.1⟩
  exact hnext.le.trans ((hcomponents i).trans hprev.le)

/-- The concrete antitone witness required by the orientation-neutral
distortion bridge. -/
theorem exists_orderedOrbitInterleaving_of_component_images
    {f : ℝ → ℝ} {c d x y : ℝ} {s : Set ℝ}
    (hfstrict : StrictMono f)
    (hx : x ∈ Set.Ioo c d)
    (hy : y ∈ Set.Ioo c d)
    (hcomponents : ∀ i, (f^[i + 1]) d ≤ (f^[i]) c)
    (hXmem : ∀ i, (f^[i]) x ∈ s)
    (hYmem : ∀ i, (f^[i]) y ∈ s) :
    ∃ z : ℕ → ℕ → ℝ,
      (∀ n, Monotone (z n) ∨ Antitone (z n)) ∧
      (∀ n j, j ≤ 2 * n → z n j ∈ s) ∧
      (∀ n i, i < n →
        (z n (2 * i) = (f^[i]) x ∧
          z n (2 * i + 1) = (f^[i]) y) ∨
        (z n (2 * i) = (f^[i]) y ∧
          z n (2 * i + 1) = (f^[i]) x)) := by
  have hsep := orbit_pairs_separated_of_component_images
    hfstrict hx hy hcomponents
  obtain ⟨w, hwanti, hwmem, hwpair⟩ :=
    exists_antitoneInterleaving_of_orderedPairs hsep hXmem hYmem
  refine ⟨fun _ ↦ w, ?_, ?_, ?_⟩
  · intro n
    exact Or.inr hwanti
  · intro n j hj
    exact hwmem j
  · intro n i hi
    exact hwpair i

/-- Abstract component input giving the left-to-right order of successive
images of a nonfixed component under a map moving toward the endpoint. -/
theorem successive_component_images_ordered
    {f g : ℝ → ℝ} {c d : ℝ}
    (hmove : ∀ i, f ((f^[i]) d) < (f^[i]) d)
    (hfix : ∀ i, g ((f^[i]) d) = (f^[i]) d)
    (hnoFix : ∀ i y, y ∈ Set.Ioo ((f^[i]) c) ((f^[i]) d) → g y ≠ y) :
    ∀ i, (f^[i + 1]) d ≤ (f^[i]) c := by
  intro i
  by_contra hsep
  have hlower : (f^[i]) c < (f^[i + 1]) d := lt_of_not_ge hsep
  have hupper : (f^[i + 1]) d < (f^[i]) d := by
    simpa [Function.iterate_succ_apply'] using hmove i
  exact hnoFix i ((f^[i + 1]) d) ⟨hlower, hupper⟩ (hfix (i + 1))

/-- An ambient map represented by an order isomorphism of `[c,d]` keeps all
of its iterates of an interior point in `(c,d)`. -/
theorem orderIso_iterate_ambient_mem_Ioo
    {g : ℝ → ℝ} {c d x : ℝ}
    (hcd : c < d)
    (e : Set.Icc c d ≃o Set.Icc c d)
    (he : ∀ y : Set.Icc c d, (e y : ℝ) = g y)
    (hx : x ∈ Set.Ioo c d) :
    ∀ k, (g^[k]) x ∈ Set.Ioo c d := by
  let cI : Set.Icc c d := ⟨c, le_rfl, hcd.le⟩
  let dI : Set.Icc c d := ⟨d, hcd.le, le_rfl⟩
  let xI : Set.Icc c d := ⟨x, hx.1.le, hx.2.le⟩
  have hc_le (y : Set.Icc c d) : cI ≤ y := y.property.1
  have hle_d (y : Set.Icc c d) : y ≤ dI := y.property.2
  have hec : e cI = cI := by
    apply le_antisymm
    · have h := e.monotone (hc_le (e.symm cI))
      simpa using h
    · exact hc_le _
  have hed : e dI = dI := by
    apply le_antisymm
    · exact hle_d _
    · have h := e.monotone (hle_d (e.symm dI))
      simpa using h
  have heiter : ∀ (m : ℕ) (y : Set.Icc c d),
      ((e^[m]) y : ℝ) = (g^[m]) (y : ℝ) := by
    intro m
    induction m with
    | zero => intro y; rfl
    | succ m ih =>
        intro y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        rw [he]
        exact congrArg g (ih y)
  intro k
  have hstrict : StrictMono (e^[k]) := e.strictMono.iterate k
  have hleft := hstrict (show cI < xI from hx.1)
  have hright := hstrict (show xI < dI from hx.2)
  rw [Function.IsFixedPt.iterate hec k] at hleft
  rw [Function.IsFixedPt.iterate hed k] at hright
  have hambient := heiter k xI
  constructor
  · rw [← hambient]
    exact hleft
  · rw [← hambient]
    exact hright

/-- A nonfixed component and its pairwise disjoint forward images provide the
orientation-neutral interleaving required by the distortion estimate. -/
theorem exists_orderedOrbitInterleaving_of_nonfixedComponent
    {f g : ℝ → ℝ} {c d x : ℝ} {s : Set ℝ}
    (hcd : c < d)
    (e : Set.Icc c d ≃o Set.Icc c d)
    (he : ∀ y : Set.Icc c d, (e y : ℝ) = g y)
    (hfstrict : StrictMono f)
    (hmove : ∀ i, f ((f^[i]) d) < (f^[i]) d)
    (hfixImages : ∀ i, g ((f^[i]) d) = (f^[i]) d)
    (hnoFixImages : ∀ i y,
      y ∈ Set.Ioo ((f^[i]) c) ((f^[i]) d) → g y ≠ y)
    (hx : x ∈ Set.Ioo c d)
    (hXmem : ∀ i, (f^[i]) x ∈ s)
    (hYmem : ∀ k i, (f^[i]) ((g^[k]) x) ∈ s) :
    ∀ k, ∃ z : ℕ → ℕ → ℝ,
      (∀ n, Monotone (z n) ∨ Antitone (z n)) ∧
      (∀ n j, j ≤ 2 * n → z n j ∈ s) ∧
      (∀ n i, i < n →
        (z n (2 * i) = (f^[i]) x ∧
          z n (2 * i + 1) = (f^[i]) ((g^[k]) x)) ∨
        (z n (2 * i) = (f^[i]) ((g^[k]) x) ∧
          z n (2 * i + 1) = (f^[i]) x)) := by
  intro k
  have hy : (g^[k]) x ∈ Set.Ioo c d :=
    orderIso_iterate_ambient_mem_Ioo hcd e he hx k
  have hcomponents := successive_component_images_ordered
    hmove hfixImages hnoFixImages
  exact exists_orderedOrbitInterleaving_of_component_images
    hfstrict hx hy hcomponents hXmem (hYmem k)

/-- `EqOn` commutation on a common invariant neighborhood is sufficient for
the local contracting core; it supplies all derivative-chain identities. -/
theorem contracting_kopell_core_of_eqOn
    {f g : ℝ → ℝ} {a c d : ℝ} {s A : Set ℝ}
    (hcd : c < d)
    (e : Set.Icc c d ≃o Set.Icc c d)
    (he : ∀ x : Set.Icc c d, (e x : ℝ) = g x)
    (hcomm : Set.EqOn (f ∘ g) (g ∘ f) A)
    (hfmap : Set.MapsTo f A A)
    (hgmap : Set.MapsTo g A A)
    (hA_nhds : ∀ x ∈ Set.Ioo c d, A ∈ 𝓝 x)
    (hfdiff : Differentiable ℝ f)
    (hgdiff : Differentiable ℝ g)
    (hfpos : ∀ x, 0 < deriv f x)
    (hgpos : ∀ x, 0 < deriv g x)
    (hgC1a : ContDiffAt ℝ 1 g a)
    (q : ℕ → ℝ)
    (hq : Tendsto q atTop (𝓝 a))
    (hqne : ∀ i, q i ≠ a)
    (hqfix : ∀ i, g (q i) = q i)
    (horbit : ∀ x ∈ Set.Ioo c d,
      Tendsto (fun n ↦ (f^[n]) x) atTop (𝓝 a))
    (hBV : BoundedVariationOn (fun t ↦ Real.log (deriv f t)) s)
    (hordered : ∀ x ∈ Set.Ioo c d, ∀ k,
      ∃ z : ℕ → ℕ → ℝ,
        (∀ n, Monotone (z n) ∨ Antitone (z n)) ∧
        (∀ n j, j ≤ 2 * n → z n j ∈ s) ∧
        (∀ n i, i < n →
          (z n (2 * i) = (f^[i]) x ∧
            z n (2 * i + 1) = (f^[i]) ((g^[k]) x)) ∨
          (z n (2 * i) = (f^[i]) ((g^[k]) x) ∧
            z n (2 * i + 1) = (f^[i]) x))) :
    ∀ x ∈ Set.Ioo c d, g x = x := by
  apply contracting_kopell_core_of_chain
    hcd e he hfdiff hgdiff hfpos hgpos hgC1a q hq hqne hqfix
    horbit hBV hordered
  intro x hx k n
  exact deriv_commuting_iterates_identity_of_eqOn_nhds
    hcomm hfmap hgmap (hA_nhds x hx)
    (hfdiff.iterate n x)
    (hfdiff.iterate n ((g^[k]) x))
    (hgdiff.iterate k x)
    (hgdiff.iterate k ((f^[n]) x))

/-- Fully local contracting core.  All regularity assumptions are restricted
to the orbit points and compact component where they are used; ambient
extensions need not be differentiable outside a common representative. -/
theorem contracting_kopell_core_localData
    {f g : ℝ → ℝ} {a c d : ℝ} {s : Set ℝ}
    (hcd : c < d)
    (e : Set.Icc c d ≃o Set.Icc c d)
    (he : ∀ x : Set.Icc c d, (e x : ℝ) = g x)
    (hgiter_cont : ∀ n, ContinuousOn (g^[n]) (Set.Icc c d))
    (hgiter_diff : ∀ n, DifferentiableOn ℝ (g^[n]) (Set.Ioo c d))
    (hgC1a : ContDiffAt ℝ 1 g a)
    (q : ℕ → ℝ)
    (hq : Tendsto q atTop (𝓝 a))
    (hqne : ∀ i, q i ≠ a)
    (hqfix : ∀ i, g (q i) = q i)
    (horbit : ∀ x ∈ Set.Ioo c d,
      Tendsto (fun n ↦ (f^[n]) x) atTop (𝓝 a))
    (hBV : BoundedVariationOn (fun t ↦ Real.log (deriv f t)) s)
    (hfstep_diff : ∀ x ∈ Set.Ioo c d, ∀ k i,
      DifferentiableAt ℝ f ((f^[i]) x) ∧
        DifferentiableAt ℝ f ((f^[i]) ((g^[k]) x)))
    (hfstep_pos : ∀ x ∈ Set.Ioo c d, ∀ k i,
      0 < deriv f ((f^[i]) x) ∧
        0 < deriv f ((f^[i]) ((g^[k]) x)))
    (hgiter_pos : ∀ x ∈ Set.Ioo c d, ∀ k n,
      0 < deriv (g^[k]) ((f^[n]) x))
    (hordered : ∀ x ∈ Set.Ioo c d, ∀ k,
      ∃ z : ℕ → ℕ → ℝ,
        (∀ n, Monotone (z n) ∨ Antitone (z n)) ∧
        (∀ n j, j ≤ 2 * n → z n j ∈ s) ∧
        (∀ n i, i < n →
          (z n (2 * i) = (f^[i]) x ∧
            z n (2 * i + 1) = (f^[i]) ((g^[k]) x)) ∨
          (z n (2 * i) = (f^[i]) ((g^[k]) x) ∧
            z n (2 * i + 1) = (f^[i]) x)))
    (hchain : ∀ x ∈ Set.Ioo c d, ∀ k n,
      deriv (g^[k]) ((f^[n]) x) * deriv (f^[n]) x =
        deriv (f^[n]) ((g^[k]) x) * deriv (g^[k]) x) :
    ∀ x ∈ Set.Ioo c d, g x = x := by
  by_contra hfixed
  push Not at hfixed
  have hgrowth := polterovichSodin_unbounded_iterate_deriv
    hcd e he hgiter_cont hgiter_diff hfixed
  let V : ℝ :=
    (eVariationOn (fun t ↦ Real.log (deriv f t)) s).toReal
  obtain ⟨k, x, hx, hlarge⟩ := hgrowth (Real.exp V)
  rcases hordered x hx k with ⟨z, hzord, hzmem, hzpair⟩
  have hdist₀ :=
    log_deriv_iterate_dist_le_variation_of_orderedPairs_monoOrAnti
      hBV
      (fun i ↦ (hfstep_diff x hx k i).1)
      (fun i ↦ (hfstep_diff x hx k i).2)
      (fun i ↦ (hfstep_pos x hx k i).1)
      (fun i ↦ (hfstep_pos x hx k i).2)
      z hzord hzmem hzpair
  have hdist (n : ℕ) :
      |Real.log (deriv (f^[n]) x) -
        Real.log (deriv (f^[n]) ((g^[k]) x))| ≤ V := by
    simpa [V, abs_sub_comm] using hdist₀ n
  have hfiterpos_x (n : ℕ) : 0 < deriv (f^[n]) x := by
    rw [deriv_iterate_eq_prod (fun i hi ↦ (hfstep_diff x hx k i).1)]
    exact Finset.prod_pos fun i hi ↦ (hfstep_pos x hx k i).1
  have hfiterpos_gx (n : ℕ) : 0 < deriv (f^[n]) ((g^[k]) x) := by
    rw [deriv_iterate_eq_prod (fun i hi ↦ (hfstep_diff x hx k i).2)]
    exact Finset.prod_pos fun i hi ↦ (hfstep_pos x hx k i).2
  have hbound : deriv (g^[k]) x ≤ Real.exp V :=
    iterate_deriv_le_exp_of_logDistortion_fixedPoints_of_chain
      hgC1a hq hqne hqfix (horbit x hx)
      hfiterpos_x hfiterpos_gx (hgiter_pos x hx k)
      (hchain x hx k) hdist
  exact (not_lt_of_ge hbound) hlarge

end CommutingInterval
