import CommutingIntervalSimplified.EntropyCycle
import CommutingIntervalSimplified.OmegaCycle

/-!
# Trapping the even iterates below a fixed cut

This is the interval-trapping step in the first level of Ruette's
Proposition 5.24. A zero-entropy map cannot have a two-branch horseshoe.
This forces a trapping interval strictly below a fixed point above the
omega-limit set, provided its maximum moves downward.
-/

namespace CommutingIntervalSimplified

open Function Set Filter
open scoped Topology

private theorem trap_below_first_fixed {F : IntervalMap} (hF : Continuous F)
    {x b q : I} (hb : IsGreatest (orbitOmega F x) b) (hbF : F b < b)
    (hbq : b < q) (hqF : F q = q)
    (hno : ∀ {a m c : I}, a < m → m < c →
      IntervalCovers F a m a c → ¬ IntervalCovers F m c a c) :
    ∃ J : ClosedSubinterval, orbitOmega F x ⊆ J.carrier ∧
      J.right < q ∧ IsForwardInvariant F J := by
  let D := Icc b q ∩ {u | F u = u}
  obtain ⟨d, hd, hleast⟩ := (isCompact_Icc.inter_right (isClosed_eq hF continuous_id)).exists_isLeast
    (show D.Nonempty from ⟨q, ⟨hbq.le, le_rfl⟩, hqF⟩)
  obtain ⟨⟨hbd, hdq⟩, hFd⟩ := hd
  have hbd' : b < d := lt_of_le_of_ne hbd (fun e => hbF.ne (e ▸ hFd))
  have downhill {t : I} (ht : t ∈ Ico b d) : F t < t := by
    by_contra! h
    obtain ⟨y, hy, hfy⟩ := exists_mem_uIcc_isFixedPt hF.continuousOn h hbF.le
    rw [uIcc_comm, uIcc_of_le ht.1] at hy
    exact (hleast (show y ∈ D from ⟨⟨hy.1, (hy.2.trans ht.2.le).trans hdq⟩, hfy⟩)).not_gt
      (hy.2.trans_lt ht.2)
  -- Once the lower bound `l` is chosen, truncate the upper bound at the
  -- maximum of `b` and `F([l,b])`. Points to the right of `b` move down.
  have truncate (l : I) (hl : l ≤ b) (hE : ∀ z ∈ orbitOmega F x, l ≤ z)
      (hlow : ∀ z ∈ Icc l d, l ≤ F z) (hsmall : ∀ z ∈ Icc l b, F z < d) :
      ∃ J : ClosedSubinterval, orbitOmega F x ⊆ J.carrier ∧
        J.right < q ∧ IsForwardInvariant F J := by
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hl) hF.continuousOn
    let r := max b (F t)
    have hbr : b ≤ r := le_max_left ..
    have hrd : r < d := max_lt hbd' (hsmall t ht)
    refine ⟨⟨l, r, hl.trans hbr⟩, fun z hz => ⟨hE z hz, (hb.2 hz).trans hbr⟩,
      hrd.trans_le hdq, ?_⟩
    intro z hz
    refine ⟨hlow z ⟨hz.1, hz.2.trans hrd.le⟩, ?_⟩
    rcases le_total z b with h | h
    · exact ((isMaxOn_iff.mp hmax) z ⟨hz.1, h⟩).trans (le_max_right ..)
    · exact (downhill ⟨h, hz.2.trans_lt hrd⟩).le.trans hz.2
  by_cases hcross : ∃ y ∈ Icc (⊥ : I) b, F y = d
  · obtain ⟨y, hy, hlast⟩ :=
      (isCompact_Icc.inter_right (isClosed_singleton.preimage hF)).exists_isGreatest
        (show (Icc (⊥ : I) b ∩ F ⁻¹' {d}).Nonempty from hcross)
    obtain ⟨⟨_, hyb⟩, hFy : F y = d⟩ := hy
    have hyb' : y < b := lt_of_le_of_ne hyb (by rintro rfl; exact hbF.not_ge (hFy ▸ hbd))
    have low {t : I} (ht : t ∈ Ioo y d) : F t < d := by
      by_cases htb : t ≤ b
      · by_contra! h
        obtain ⟨s, hs, hFs⟩ := (intermediate_value_Icc' htb hF.continuousOn)
          (show d ∈ Icc (F b) (F t) from ⟨hbF.le.trans hbd, h⟩)
        exact (hlast (show s ∈ Icc (⊥ : I) b ∩ F ⁻¹' {d} from ⟨⟨bot_le, hs.2⟩, hFs⟩)).not_gt
          (ht.1.trans_le hs.1)
      · exact (downhill ⟨le_of_not_ge htb, ht.2⟩).trans ht.2
    have high {t : I} (ht : t ∈ Ioo y d) : y < F t := by
      by_contra! h
      exact hno ht.1 ht.2
        (intervalCovers_of_endpoints_anti hF ht.1.le (ht.1.trans ht.2).le h hFy.ge)
        (intervalCovers_of_endpoints_mono hF ht.2.le (ht.1.trans ht.2).le h hFd.ge)
    obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (hyb.trans hbd)) hF.continuousOn
    have bounds {t : I} (ht : t ∈ Icc y d) : F t ∈ Ioc y d := by
      rcases ht.1.eq_or_lt with he | he
      · rw [← he, hFy]; exact ⟨hyb'.trans hbd', le_rfl⟩
      rcases ht.2.eq_or_lt with he' | he'
      · rw [he', hFd]; exact ⟨hyb'.trans hbd', le_rfl⟩
      exact ⟨high ⟨he, he'⟩, (low ⟨he, he'⟩).le⟩
    let w := F u
    have hyw : y < w := (bounds hu).1
    have step : MapsTo F (Icc y d) (Icc w d) := fun t ht =>
      ⟨isMinOn_iff.mp hmin t ht, (bounds ht).2⟩
    have inv : MapsTo F (Icc w d) (Icc w d) := step.mono_left (Icc_subset_Icc_left hyw.le)
    have hcb := (mem_omegaLimit_singleton_iff_mapClusterPt _ _ _ _).mp hb.1
    obtain ⟨n, hn⟩ := (mapClusterPt_iff_frequently.mp hcb (Ioo y d)
      (isOpen_Ioo.mem_nhds ⟨hyb', hbd'⟩)).exists
    have enter : F^[n+1] x ∈ Icc w d := by
      rw [iterate_succ_apply']; exact step (Ioo_subset_Icc_self hn)
    have eventual : ∀ᶠ k : ℕ in atTop, F^[k] x ∈ Icc w d := by
      filter_upwards [eventually_ge_atTop (n+1)] with k hk
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
      rw [Nat.add_comm, iterate_add_apply]
      exact inv.iterate m enter
    have hE : orbitOmega F x ⊆ Icc w d := fun z hz => isClosed_Icc.mem_of_mapClusterPt
      ((mem_omegaLimit_singleton_iff_mapClusterPt _ _ _ _).mp hz) eventual
    exact truncate w (hE hb.1).1 (fun z hz => (hE hz).1) (fun z hz => (inv hz).1)
      (fun z hz => low ⟨hyw.trans_le hz.1, hz.2.trans_lt hbd'⟩)
  · apply truncate ⊥ bot_le (fun _ _ => bot_le) (fun _ _ => bot_le)
    intro z hz
    by_contra! h
    obtain ⟨s, hs, hFs⟩ := (intermediate_value_Icc' hz.2 hF.continuousOn)
      (show d ∈ Icc (F b) (F z) from ⟨hbF.le.trans hbd, h⟩)
    exact hcross ⟨s, ⟨bot_le, hs.2⟩, hFs⟩


/-- If an aperiodic closed invariant set alternates across a fixed cut of a
zero-entropy map, a point of the set lies in the interior of an interval
trapped in a genuinely disjoint two-cycle of closed intervals. -/
theorem exchanged_intervals_of_alternating_cut {f : IntervalMap} (hf : Continuous f)
    (hz : Dynamics.coverEntropy f univ = 0) {K : Set I} (hK : IsClosed K)
    (hne : K.Nonempty) (hmap : MapsTo f K K) (haper : ∀ z ∈ K, z ∉ periodicPts f)
    {q : I} (hq : f q = q) (hflip : ∀ z ∈ K, z < q ↔ q < f z) :
    ∃ L R : ClosedSubinterval, Disjoint L.carrier R.carrier ∧
      MapsTo f L.carrier R.carrier ∧ MapsTo f R.carrier L.carrier ∧
      ∃ u ∈ K, u ∈ Ioo L.left L.right := by
  classical
  let F := f^[2]
  have hF : Continuous F := hf.iterate 2
  have qout : q ∉ K := fun h => haper q h (mk_mem_periodicPts (n := 1) (by decide) hq)
  have leftStep {v : I} (hv : v ∈ K) (hvq : q < v) : f v < q :=
    lt_of_le_of_ne (not_lt.mp (fun h => hvq.not_gt ((hflip v hv).mpr h)))
      (fun h => qout (h ▸ hmap hv))
  let S := K ∩ Iic q
  obtain ⟨x, hx⟩ : S.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    by_cases h : y ≤ q
    · exact ⟨y, hy, h⟩
    · exact ⟨f y, hmap hy, (leftStep hy (lt_of_not_ge h)).le⟩
  have hFS : MapsTo F S S := by
    intro y hy
    have hlt : y < q := lt_of_le_of_ne hy.2 (fun e => qout (e ▸ hy.1))
    exact ⟨hmap (hmap hy.1), (leftStep (hmap hy.1) ((hflip y hy.1).mp hlt)).le⟩
  have hES := orbitOmega_subset_of_invariant (hK.inter isClosed_Iic) hFS hx
  have aperF (u : I) (hu : u ∈ orbitOmega F x) : u ∉ periodicPts F := by
    intro h
    obtain ⟨n, hn, hnF⟩ := mem_periodicPts.mp h
    apply haper u (hES hu).1
    refine mk_mem_periodicPts (mul_pos (show 0 < 2 by decide) hn) ?_
    simpa only [IsPeriodicPt, iterate_mul] using hnF
  have inf : (orbitOmega F x).Infinite := by
    intro hfin
    obtain ⟨u, hu, hper⟩ := finite_orbitOmega_has_periodicPt hF hfin
    exact aperF u hu hper
  obtain ⟨b, hb⟩ := (isClosed_omegaLimit ..).isCompact.exists_isGreatest inf.nonempty
  have hbq : b < q := lt_of_le_of_ne (hES hb.1).2 (fun e => qout (e ▸ (hES hb.1).1))
  have hbF : F b < b := lt_of_le_of_ne (hb.2 (orbitOmega_forward hF x hb.1)) (fun e =>
    aperF b hb.1 (mk_mem_periodicPts (n := 1) (by decide) e))
  have hFq : F q = q := by simp [F, hq]
  obtain ⟨L, hEL, hLq, hinv⟩ := trap_below_first_fixed hF hb hbF hbq hFq
    (fun hab hbc hleft => not_adjacent_covers_of_coverEntropy_zero hf hz (p := 2) (by decide)
      hab hbc hleft)
  let A := f '' L.carrier
  have himage : A = Icc (sInf A) (sSup A) := ContinuousOn.image_Icc L.left_le_right hf.continuousOn
  have hA : A.Nonempty := L.carrier_nonempty.image f
  let R : ClosedSubinterval := ⟨sInf A, sSup A, nonempty_Icc.mp (himage ▸ hA)⟩
  have hR : R.carrier = A := himage.symm
  have step : MapsTo f R.carrier L.carrier := by
    rw [hR]
    rintro _ ⟨t, ht, rfl⟩
    exact hinv ht
  have qnot : q ∉ R.carrier := fun h => hLq.not_ge (hq ▸ (step h).2)
  have hfb : f b ∈ R.carrier := hR ▸ mem_image_of_mem _ (hEL hb.1)
  have qR : q < R.left := lt_of_not_ge (fun h =>
    qnot ⟨h, ((hflip b (hES hb.1).1).mp hbq).le.trans hfb.2⟩)
  refine ⟨L, R, disjoint_left.mpr (fun ⦃_⦄ hv hw => (hv.2.trans_lt (hLq.trans qR)).not_ge hw.1),
    fun t ht => hR ▸ mem_image_of_mem _ ht, step, ?_⟩
  obtain ⟨u, hu, hn⟩ := inf.exists_notMem_finset ({L.left, L.right} : Finset I)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  exact ⟨u, (hES hu).1, lt_of_le_of_ne (hEL hu).1 (Ne.symm hn.1), lt_of_le_of_ne (hEL hu).2 hn.2⟩

end CommutingIntervalSimplified
