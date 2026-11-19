import CommutingIntervalSimplified.OmegaCycle
import CommutingIntervalSimplified.EntropyCycle

/-!
# The first division of a minimal zero-entropy set

A gap with endpoints moving towards one another covers itself. Its iterates
reach every relative neighborhood of a point of a minimal set. If two
successive points lie on the same side of the gap, they give an adjacent
horseshoe for an iterate.
-/

namespace CommutingIntervalSimplified

open Function Set Filter Dynamics
open scoped Topology

/-- A minimal compact forward-invariant set inside a given compact
invariant set. The forward omega-limit of every member is the whole set. -/
theorem exists_minimal_orbitOmega {f : IntervalMap} (hf : Continuous f)
    {A : Set I} (hA : IsClosed A) (hne : A.Nonempty) (hinv : MapsTo f A A) :
    ∃ M ⊆ A, IsClosed M ∧ M.Nonempty ∧ MapsTo f M M ∧ ∀ x ∈ M, orbitOmega f x = M := by
  let S : Set (Set I) := {M | IsClosed M ∧ M.Nonempty ∧ MapsTo f M M}
  obtain ⟨M, hMA, hmin⟩ := zorn_superset_nonempty S (fun C hCS hchain hC => by
    refine ⟨⋂₀ C, ⟨isClosed_sInter (fun t ht => (hCS ht).1), ?_, ?_⟩,
      fun _ ht => sInter_subset_of_mem ht⟩
    · letI := hC.coe_sort
      rw [sInter_eq_iInter]
      exact IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
        (fun i j => by
          rcases hchain.total i.prop j.prop with hij | hji
          · exact ⟨i, Subset.rfl, hij⟩
          · exact ⟨j, hji, Subset.rfl⟩) (fun t => (hCS t.prop).2.1)
        (fun t => (hCS t.prop).1.isCompact) (fun t => (hCS t.prop).1)
    · intro x hx
      exact mem_sInter.mpr fun t ht => (hCS ht).2.2 (mem_sInter.mp hx t ht)) A
      (show A ∈ S from ⟨hA, hne, hinv⟩)
  obtain ⟨hM, hMne, hMinv⟩ := hmin.1
  refine ⟨M, hMA, hM, hMne, hMinv, fun x hx => hmin.eq_of_subset ?_
    (orbitOmega_subset_of_invariant hM hMinv hx)⟩
  exact ⟨isClosed_omegaLimit .., nonempty_omegaLimit _ _ _ (singleton_nonempty x),
    orbitOmega_forward hf x⟩

/-- The inverse action on the product fixed set leaves every backward
omega-limit forward-invariant. -/
theorem productFixed_backwardOmega_invariant {f g : IntervalMap} (hf : Continuous f)
    (hc : Function.Commute f g) {x : I} (hx : x ∈ fixedPoints (f ∘ g)) :
    MapsTo f (orbitOmega g x) (orbitOmega g x) := by
  intro y hy
  apply (cluster_iff_mem_orbitOmega ..).mp
  rw [mapClusterPt_iff_frequently]
  intro V hV
  have hfreq := mapClusterPt_iff_frequently.mp ((cluster_iff_mem_orbitOmega ..).mpr hy)
    (f ⁻¹' V) (hf.continuousAt.preimage_mem_nhds hV)
  rw [frequently_atTop] at hfreq ⊢
  intro n
  obtain ⟨m, hm, hhit⟩ := hfreq (n+1)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  refine ⟨k, by omega, ?_⟩
  have hK : f (g (g^[k] x)) = g^[k] x := (prodFixed_maps hc).2.iterate k hx
  change f (g^[k.succ] x) ∈ V at hhit
  rwa [iterate_succ_apply', hK] at hhit

private theorem interval_gap_iterates_cover {f : IntervalMap} {a b : I}
    (h : IntervalCovers f a b a b) (n : ℕ) : IntervalCovers f^[n] a b a b := by
  induction n with
  | zero => simp [IntervalCovers]
  | succ n ih => exact h.comp ih

/-- On a compact minimal set without a fixed point, zero entropy forces
every step to cross one and the same fixed point of the interval map. -/
theorem alternating_cut_of_minimal_zero_entropy {f : IntervalMap} (hf : Continuous f)
    (hzero : coverEntropy f univ = 0) {M : Set I} (hM : IsClosed M) (hne : M.Nonempty)
    (hmap : MapsTo f M M) (hmin : ∀ x ∈ M, orbitOmega f x = M)
    (hfree : ∀ x ∈ M, f x ≠ x) :
    ∃ q : I, f q = q ∧ q ∉ M ∧ ∀ u ∈ M, u < q ↔ q < f u := by
  let down := M ∩ {u | f u ≤ u}
  have hdown : IsClosed down := hM.inter (isClosed_le hf continuous_id)
  obtain ⟨p, hp, hmax⟩ := hM.isCompact.exists_isGreatest hne
  obtain ⟨b, hb, hbmin⟩ := hdown.isCompact.exists_isLeast
    (show down.Nonempty from ⟨p, hp, hmax (hmap hp)⟩)
  obtain ⟨l, hl, hlmin⟩ := hM.isCompact.exists_isLeast hne
  let up := M ∩ ({u | u ≤ f u} ∩ Iic b)
  have hup : IsClosed up := hM.inter ((isClosed_le continuous_id hf).inter isClosed_Iic)
  obtain ⟨a, ha, hamax⟩ := hup.isCompact.exists_isGreatest
    (show up.Nonempty from ⟨l, hl, hlmin (hmap hl), hlmin hb.1⟩)
  have har : a < f a := lt_of_le_of_ne ha.2.1 (Ne.symm (hfree a ha.1))
  have hbl : f b < b := lt_of_le_of_ne hb.2 (hfree b hb.1)
  have hab : a < b := lt_of_le_of_ne ha.2.2 (by rintro rfl; exact hbl.not_gt har)
  have gap {u : I} (hu : u ∈ M) : u ≤ a ∨ b ≤ u := by
    by_cases h : b ≤ u
    · exact Or.inr h
    · refine Or.inl (hamax ⟨hu, ?_, le_of_lt (lt_of_not_ge h)⟩)
      change u ≤ f u
      exact le_of_not_gt fun hfu => h (hbmin ⟨hu, hfu.le⟩)
  have hfa : b ≤ f a := (gap (hmap ha.1)).resolve_left har.not_ge
  have hfb : f b ≤ a := (gap (hmap hb.1)).resolve_right hbl.not_ge
  have cover : IntervalCovers f a b a b :=
    intervalCovers_of_endpoints_anti hf hab.le hab.le hfb hfa
  obtain ⟨q, hq, hfix⟩ := exists_mem_Icc_isFixedPt hf.continuousOn hab.le har.le hbl.le
  have haq : a < q := lt_of_le_of_ne hq.1 (by rintro rfl; exact har.ne' hfix)
  have hqb : q < b := lt_of_le_of_ne hq.2 (by rintro rfl; exact hbl.ne hfix)
  have hit {U : Set I} (hU : IsOpen U) {u : I} (hu : u ∈ M) (huU : u ∈ U) :
      ∃ n : ℕ, f^[n] a ∈ U := by
    have hω : u ∈ orbitOmega f a := hmin a ha.1 ▸ hu
    exact (mapClusterPt_iff_frequently.mp ((cluster_iff_mem_orbitOmega ..).mpr hω)
      U (hU.mem_nhds huU)).exists
  have himg (n : ℕ) : IsPreconnected ((f^[n]) '' Icc a b) :=
    isPreconnected_Icc.image _ (hf.iterate n).continuousOn
  have hcovers (n : ℕ) {r s : I} (h : IntervalCovers f r s a b)
      {j k : I} (hjk : IntervalCovers f^[n] a b j k) : IntervalCovers f^[n+1] r s j k :=
    h.comp hjk
  refine ⟨q, hfix, fun h => (gap h).elim haq.not_ge hqb.not_ge, ?_⟩
  intro u hu
  constructor
  · intro huq
    by_contra! h
    have hua := (gap hu).resolve_right (huq.trans hqb).not_ge
    have hfu := (gap (hmap hu)).resolve_right (h.trans_lt hqb).not_ge
    have hua' : u < a := lt_of_le_of_ne hua (by rintro rfl; exact (hab.trans_le hfa).not_ge hfu)
    obtain ⟨n, hv, hfv⟩ := hit (U := Iio a ∩ f ⁻¹' Iio b)
      (isOpen_Iio.inter (isOpen_Iio.preimage hf)) hu ⟨hua', hfu.trans_lt hab⟩
    let v := f^[n] a
    have hvM := hmap.iterate n ha.1
    have hfva := (gap (hmap hvM)).resolve_right hfv.not_ge
    have c₁ : IntervalCovers f v a a b :=
      intervalCovers_of_endpoints_mono hf hv.le hab.le hfva hfa
    have c₂ : IntervalCovers f^[n] a b v b := (himg n).Icc_subset
      (mem_image_of_mem _ (left_mem_Icc.mpr hab.le))
      (interval_gap_iterates_cover cover n (right_mem_Icc.mpr hab.le))
    exact not_adjacent_covers_of_coverEntropy_zero hf hzero (Nat.succ_pos n)
      hv hab (hcovers n c₁ c₂) (hcovers n cover c₂)
  · intro hqu
    by_contra! h
    have hbu := (gap hu).resolve_left (haq.trans_le h).not_ge
    have hbf := (gap (hmap hu)).resolve_left (haq.trans hqu).not_ge
    have hbu' : b < u := lt_of_le_of_ne hbu (by rintro rfl; exact (hfb.trans_lt hab).not_ge hbf)
    obtain ⟨n, hv, hfv⟩ := hit (U := Ioi b ∩ f ⁻¹' Ioi a)
      (isOpen_Ioi.inter (isOpen_Ioi.preimage hf)) hu ⟨hbu', hab.trans_le hbf⟩
    let v := f^[n] a
    have hvM := hmap.iterate n ha.1
    have hbfv := (gap (hmap hvM)).resolve_left hfv.not_ge
    have c₁ : IntervalCovers f b v a b :=
      intervalCovers_of_endpoints_mono hf hv.le hab.le hfb hbfv
    have c₂ : IntervalCovers f^[n] a b a v := (himg n).Icc_subset
      (interval_gap_iterates_cover cover n (left_mem_Icc.mpr hab.le))
      (mem_image_of_mem _ (left_mem_Icc.mpr hab.le))
    exact not_adjacent_covers_of_coverEntropy_zero hf hzero (Nat.succ_pos n)
      hab hv (hcovers n cover c₂) (hcovers n c₁ c₂)

end CommutingIntervalSimplified
