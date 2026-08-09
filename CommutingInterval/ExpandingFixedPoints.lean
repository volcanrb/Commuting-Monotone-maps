import CommutingInterval.DynamicsDefs
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Fixed-point accumulation for an expanding commuting interval germ. -/

open Function Set Filter
open scoped Topology

namespace CommutingInterval

theorem expanding_fixed_sequence
    {u v : IntervalMap} {p q : I}
    (gu : RightGermC1Diffeomorphism u p)
    (gv : RightGermC1Diffeomorphism v p)
    (hpq : p < q)
    (hq_u : q ≤ gu.rightEnd) (hq_v : q ≤ gv.rightEnd)
    (hu_fixed : IsFixedPoint u p) (hv_fixed : IsFixedPoint v p)
    (hcomm : Set.EqOn (u ∘ v) (v ∘ u) (Set.Icc p q))
    (hv_has_fixed : ∃ y ∈ Set.Ioc p q, v y = y)
    (hu_expands : ∀ x ∈ Set.Ioc p q, (x : ℝ) < u x) :
    ∃ z : ℕ → I,
      Tendsto (fun n => (z n : ℝ)) atTop (𝓝 (p : ℝ)) ∧
      (∀ n, p < z n) ∧ (∀ n, v (z n) = z n) := by
  rcases hv_has_fixed with ⟨y, hy, hyfix⟩
  have hpy : (p : ℝ) < (y : ℝ) := hy.1
  have hyq : y ≤ q := hy.2
  have hyU : y ≤ gu.rightEnd := hyq.trans hq_u
  have hyV : y ≤ gv.rightEnd := hyq.trans hq_v
  have hUp : gu.extension (p : ℝ) = (p : ℝ) := by
    calc
      gu.extension (p : ℝ) = (u p : ℝ) :=
        (gu.agrees ⟨le_rfl, gu.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hu_fixed
  have hVp : gv.extension (p : ℝ) = (p : ℝ) := by
    calc
      gv.extension (p : ℝ) = (v p : ℝ) :=
        (gv.agrees ⟨le_rfl, gv.base_lt_rightEnd.le⟩).symm
      _ = (p : ℝ) := congrArg Subtype.val hv_fixed
  have hVy : gv.extension (y : ℝ) = (y : ℝ) := by
    calc
      gv.extension (y : ℝ) = (v y : ℝ) :=
        (gv.agrees ⟨hy.1.le, hyV⟩).symm
      _ = (y : ℝ) := congrArg Subtype.val hyfix
  have hUcont : ContinuousOn gu.extension
      (Set.Icc (p : ℝ) (y : ℝ)) :=
    gu.contDiff_one.continuousOn.mono fun _ hx =>
      gu.segment_subset ⟨hx.1, hx.2.trans hyU⟩
  have hVcont : ContinuousOn gv.extension
      (Set.Icc (p : ℝ) (y : ℝ)) :=
    gv.contDiff_one.continuousOn.mono fun _ hx =>
      gv.segment_subset ⟨hx.1, hx.2.trans hyV⟩
  have hUstrict : StrictMonoOn gu.extension
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hUcont
    intro x hx
    exact gu.deriv_pos x
      ⟨(interior_subset hx).1, (interior_subset hx).2.trans hyU⟩
  have hVstrict : StrictMonoOn gv.extension
      (Set.Icc (p : ℝ) (y : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hVcont
    intro x hx
    exact gv.deriv_pos x
      ⟨(interior_subset hx).1, (interior_subset hx).2.trans hyV⟩
  have hVmap : MapsTo gv.extension
      (Set.Icc (p : ℝ) (y : ℝ)) (Set.Icc (p : ℝ) (y : ℝ)) := by
    intro x hx
    constructor
    · rw [← hVp]
      exact hVstrict.monotoneOn ⟨le_rfl, hpy.le⟩ hx hx.1
    · rw [← hVy]
      exact hVstrict.monotoneOn hx ⟨hpy.le, le_rfl⟩ hx.2
  have hUexpands : ∀ x ∈ Set.Ioc (p : ℝ) (y : ℝ),
      x < gu.extension x := by
    intro x hx
    let xI : I := ⟨x, ⟨p.property.1.trans hx.1.le,
      hx.2.trans y.property.2⟩⟩
    have hxIq : xI ∈ Set.Ioc p q := ⟨hx.1, hx.2.trans hyq⟩
    have hxIU : xI ∈ Set.Icc p gu.rightEnd :=
      ⟨hx.1.le, hx.2.trans hyU⟩
    have hagree : (u xI : ℝ) = gu.extension x := gu.agrees hxIU
    simpa [xI, hagree] using hu_expands xI hxIq
  have hUy : (y : ℝ) < gu.extension (y : ℝ) :=
    hUexpands (y : ℝ) ⟨hpy, le_rfl⟩
  have hUmapImage : MapsTo gu.extension
      (Set.Icc (p : ℝ) (y : ℝ))
      (Set.Icc (p : ℝ) (gu.extension (y : ℝ))) := by
    intro x hx
    constructor
    · rw [← hUp]
      exact hUstrict.monotoneOn ⟨le_rfl, hpy.le⟩ hx hx.1
    · exact hUstrict.monotoneOn hx ⟨hpy.le, le_rfl⟩ hx.2
  have hUsurj : Set.SurjOn gu.extension
      (Set.Icc (p : ℝ) (y : ℝ))
      (Set.Icc (p : ℝ) (gu.extension (y : ℝ))) := by
    simpa [hUp] using hUcont.surjOn_Icc
      (show (p : ℝ) ∈ Set.Icc (p : ℝ) (y : ℝ) from ⟨le_rfl, hpy.le⟩)
      (show (y : ℝ) ∈ Set.Icc (p : ℝ) (y : ℝ) from ⟨hpy.le, le_rfl⟩)
  let fI : Set.Icc (p : ℝ) (y : ℝ) →
      Set.Icc (p : ℝ) (gu.extension (y : ℝ)) :=
    fun x => ⟨gu.extension x, hUmapImage x.property⟩
  have hfIstrict : StrictMono fI := by
    intro a b hab
    exact hUstrict a.property b.property hab
  have hfIsurj : Function.Surjective fI := by
    intro b
    obtain ⟨a, ha, hab⟩ := hUsurj b.property
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  let e : Set.Icc (p : ℝ) (y : ℝ) ≃o
      Set.Icc (p : ℝ) (gu.extension (y : ℝ)) :=
    StrictMono.orderIsoOfSurjective fI hfIstrict hfIsurj
  let incl : Set.Icc (p : ℝ) (y : ℝ) →
      Set.Icc (p : ℝ) (gu.extension (y : ℝ)) :=
    fun x => ⟨x, x.property.1, x.property.2.trans hUy.le⟩
  let inv : Set.Icc (p : ℝ) (y : ℝ) →
      Set.Icc (p : ℝ) (y : ℝ) := fun x => e.symm (incl x)
  have heval (x : Set.Icc (p : ℝ) (y : ℝ)) :
      (e x : ℝ) = gu.extension x := rfl
  have hInvEq (x : Set.Icc (p : ℝ) (y : ℝ)) :
      gu.extension (inv x) = (x : ℝ) := by
    calc
      gu.extension (inv x) = (e (inv x) : ℝ) := (heval _).symm
      _ = (incl x : ℝ) := congrArg Subtype.val (e.apply_symm_apply (incl x))
      _ = (x : ℝ) := rfl
  have hInvStrict : StrictMono inv := by
    intro a b hab
    apply e.symm.strictMono
    exact hab
  let pS : Set.Icc (p : ℝ) (y : ℝ) := ⟨p, le_rfl, hpy.le⟩
  let yS : Set.Icc (p : ℝ) (y : ℝ) := ⟨y, hpy.le, le_rfl⟩
  have hInvP : inv pS = pS := by
    apply Subtype.ext
    apply hUstrict.injOn (inv pS).property pS.property
    rw [hInvEq]
    exact hUp.symm
  have hInvContracts (x : Set.Icc (p : ℝ) (y : ℝ))
      (hx : pS < x) : inv x < x := by
    have hpInv : pS < inv x := by
      rw [← hInvP]
      exact hInvStrict hx
    have hexpand := hUexpands (inv x : ℝ)
      ⟨hpInv, (inv x).property.2⟩
    rw [hInvEq] at hexpand
    exact hexpand
  let w : ℕ → Set.Icc (p : ℝ) (y : ℝ) :=
    fun n => (inv^[n]) yS
  have hpw : ∀ n, pS < w n := by
    intro n
    have hstrict := hInvStrict.iterate n (show pS < yS from hpy)
    rw [Function.IsFixedPt.iterate hInvP n] at hstrict
    exact hstrict
  have hwanti : Antitone (fun n => (w n : ℝ)) := by
    apply antitone_nat_of_succ_le
    intro n
    have hrec : w (n + 1) = inv (w n) := by
      simp [w, Function.iterate_succ_apply']
    rw [hrec]
    exact (hInvContracts (w n) (hpw n)).le
  have hwbdd : BddBelow (Set.range fun n => (w n : ℝ)) := by
    exact ⟨p, by rintro _ ⟨n, rfl⟩; exact (w n).property.1⟩
  let L : ℝ := sInf (Set.range fun n => (w n : ℝ))
  have hwlim : Tendsto (fun n => (w n : ℝ)) atTop (𝓝 L) :=
    tendsto_atTop_ciInf hwanti hwbdd
  have hLmem : L ∈ Set.Icc (p : ℝ) (y : ℝ) :=
    isClosed_Icc.mem_of_tendsto hwlim
      (Eventually.of_forall fun n => (w n).property)
  have hshift : Tendsto (fun n => (w (n + 1) : ℝ)) atTop (𝓝 L) :=
    hwlim.comp (tendsto_add_atTop_nat 1)
  have hUcontL : ContinuousAt gu.extension L :=
    (gu.contDiff_one.contDiffAt
      (gu.isOpen_neighborhood.mem_nhds <|
        gu.segment_subset ⟨hLmem.1, hLmem.2.trans hyU⟩)).continuousAt
  have hfshift : Tendsto
      (fun n => gu.extension (w (n + 1) : ℝ)) atTop
      (𝓝 (gu.extension L)) := by
    have hUtend : Tendsto gu.extension (𝓝 L)
        (𝓝 (gu.extension L)) := hUcontL
    exact hUtend.comp hshift
  have hstep : ∀ n, gu.extension (w (n + 1) : ℝ) = (w n : ℝ) := by
    intro n
    rw [show w (n + 1) = inv (w n) by
      simp [w, Function.iterate_succ_apply']]
    exact hInvEq (w n)
  have hfixL : gu.extension L = L := by
    have hfshift' : Tendsto (fun n => (w n : ℝ)) atTop
        (𝓝 (gu.extension L)) := by
      simpa only [hstep] using hfshift
    exact tendsto_nhds_unique hfshift' hwlim
  have hLp : L = (p : ℝ) := by
    apply le_antisymm
    · by_contra hnot
      have hpL : (p : ℝ) < L := lt_of_not_ge hnot
      exact (not_lt_of_ge hfixL.le)
        (hUexpands L ⟨hpL, hLmem.2⟩)
    · exact hLmem.1
  have hwlimp : Tendsto (fun n => (w n : ℝ)) atTop (𝓝 (p : ℝ)) := by
    simpa [hLp] using hwlim
  have hCommAtInv (s : Set.Icc (p : ℝ) (y : ℝ)) :
      gu.extension (gv.extension (inv s)) =
        gv.extension (gu.extension (inv s)) := by
    let tI : I := ⟨(inv s : ℝ),
      ⟨p.property.1.trans (inv s).property.1,
        (inv s).property.2.trans y.property.2⟩⟩
    have htCommon : (inv s : ℝ) ∈ Set.Icc (p : ℝ) (y : ℝ) :=
      (inv s).property
    have hgtCommon := hVmap htCommon
    have hftCommon : gu.extension (inv s : ℝ) ∈
        Set.Icc (p : ℝ) (y : ℝ) := by
      rw [hInvEq]
      exact s.property
    have htU : tI ∈ Set.Icc p gu.rightEnd :=
      ⟨htCommon.1, htCommon.2.trans hyU⟩
    have htV : tI ∈ Set.Icc p gv.rightEnd :=
      ⟨htCommon.1, htCommon.2.trans hyV⟩
    have hUagree : (u tI : ℝ) = gu.extension (inv s) := gu.agrees htU
    have hVagree : (v tI : ℝ) = gv.extension (inv s) := gv.agrees htV
    have hvRangeU : v tI ∈ Set.Icc p gu.rightEnd := by
      constructor
      · exact hgtCommon.1.trans_eq hVagree.symm
      · exact hVagree.trans_le (hgtCommon.2.trans hyU)
    have huRangeV : u tI ∈ Set.Icc p gv.rightEnd := by
      constructor
      · exact hftCommon.1.trans_eq hUagree.symm
      · exact hUagree.trans_le (hftCommon.2.trans hyV)
    have htq : tI ∈ Set.Icc p q :=
      ⟨htCommon.1, htCommon.2.trans hyq⟩
    have hmapComm := congrArg Subtype.val (hcomm htq)
    calc
      gu.extension (gv.extension (inv s)) =
          gu.extension (v tI : ℝ) := congrArg gu.extension hVagree.symm
      _ = (u (v tI) : ℝ) := (gu.agrees hvRangeU).symm
      _ = (v (u tI) : ℝ) := hmapComm
      _ = gv.extension (u tI : ℝ) := gv.agrees huRangeV
      _ = gv.extension (gu.extension (inv s)) :=
        congrArg gv.extension hUagree
  have hwFixedExt : ∀ n, gv.extension (w n : ℝ) = (w n : ℝ) := by
    intro n
    induction n with
    | zero => simpa [w, yS] using hVy
    | succ n ih =>
        have hrec : w (n + 1) = inv (w n) := by
          simp [w, Function.iterate_succ_apply']
        rw [hrec]
        have hcommInv := hCommAtInv (w n)
        have himage : gu.extension (inv (w n)) = (w n : ℝ) := hInvEq (w n)
        have hsameImage : gu.extension (gv.extension (inv (w n))) =
            gu.extension (inv (w n)) := by
          rw [hcommInv, himage, ih]
        exact hUstrict.injOn
          (hVmap (inv (w n)).property) (inv (w n)).property hsameImage
  let z : ℕ → I := fun n =>
    ⟨(w n : ℝ), ⟨p.property.1.trans (w n).property.1,
      (w n).property.2.trans y.property.2⟩⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · simpa [z] using hwlimp
  · intro n
    exact hpw n
  · intro n
    apply Subtype.ext
    change (v (z n) : ℝ) = (w n : ℝ)
    calc
      (v (z n) : ℝ) = gv.extension (w n : ℝ) :=
        gv.agrees ⟨(w n).property.1,
          (w n).property.2.trans hyV⟩
      _ = (w n : ℝ) := hwFixedExt n

end CommutingInterval
