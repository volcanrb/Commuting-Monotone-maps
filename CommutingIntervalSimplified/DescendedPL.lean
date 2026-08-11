import CommutingIntervalSimplified.FactorBase
import CommutingIntervalSimplified.PiecewiseMonotoneBase

/-!
# Piecewise-linear descent through finite interval quotients

A finite-piece PL map respecting the fibres of a canonical finite interval
quotient descends to another finite-piece PL interval map. The proof refines
both source partitions and transports their vertices through the quotient.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set

/-- An affine branch has one of the two weak monotonicity orientations. -/
private theorem affineOn_weaklyMonotoneOn_descendedPL
    {T : IntervalMap} {s : Set I} (h : IsAffineOn T s) :
    IsWeaklyMonotoneOn T s := by
  rcases h with ⟨m, c, hformula⟩
  by_cases hm : 0 ≤ m
  · left
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left
      (Subtype.coe_le_coe.mpr hxy) hm) c
  · right
    intro x hx y hy hxy
    apply Subtype.coe_le_coe.mp
    rw [hformula x hx, hformula y hy]
    simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonpos_left
      (Subtype.coe_le_coe.mpr hxy) (le_of_not_ge hm)) c

/-- Finite-piece PL maps are closed under composition. -/
theorem finitePiecePL_comp_descendedPL
    {T U : IntervalMap} (hT : FinitePiecePL T) (hU : FinitePiecePL U) :
    FinitePiecePL (T ∘ U) := by
  rcases hT with ⟨hTcont, pT, hpT⟩
  rcases hU with ⟨hUcont, pU, hpU⟩
  let wT : MonotonicityPartition T :=
    ⟨pT, fun _ _ hab => affineOn_weaklyMonotoneOn_descendedPL (hpT hab)⟩
  let wU : MonotonicityPartition U :=
    ⟨pU, fun _ _ hab => affineOn_weaklyMonotoneOn_descendedPL (hpU hab)⟩
  refine ⟨hTcont.comp hUcont, wU.compositionRefinement wT, ?_⟩
  intro a b hab
  obtain ⟨aU, bU, hUadj, hsource⟩ :=
    (wU.compositionRefinement_refines wT).adjacent_subset hab
  obtain ⟨mU, cU, hUformula⟩ := hpU hUadj
  obtain ⟨_hUweak, aT, bT, hTadj, hmaps⟩ :=
    wU.composition_cell hUcont wT hab
  obtain ⟨mT, cT, hTformula⟩ := hpT hTadj
  refine ⟨mT * mU, mT * cU + cT, ?_⟩
  intro x hx
  change (T (U x) : ℝ) = _
  rw [hTformula (U x) (hmaps hx), hUformula x (hsource hx)]
  ring


/-- A point which is not a partition vertex lies strictly inside a cell. -/
private theorem RealPartition.exists_adjacent_around_descendedPL
    (p : RealPartition) {x : ℝ} (hxI : x ∈ I)
    (hx : x ∉ p.points) :
    ∃ c d, p.Adjacent c d ∧ c < x ∧ x < d := by
  classical
  let lower := p.points.filter fun z ↦ z ≤ x
  let upper := p.points.filter fun z ↦ x ≤ z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    simp [lower, p.zero_mem, hxI.1]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    simp [upper, p.one_mem, hxI.2]
  obtain ⟨c, hc, hcmax⟩ := lower.exists_max_image id hlower
  obtain ⟨d, hd, hdmin⟩ := upper.exists_min_image id hupper
  have hc' := Finset.mem_filter.mp hc
  have hd' := Finset.mem_filter.mp hd
  have hcx : c < x :=
    lt_of_le_of_ne hc'.2 (fun h ↦ hx (by simpa [h] using hc'.1))
  have hxd : x < d :=
    lt_of_le_of_ne hd'.2 (fun h ↦ hx (by simpa [h] using hd'.1))
  refine ⟨c, d, ⟨hc'.1, hd'.1, hcx.trans hxd, ?_⟩, hcx, hxd⟩
  intro e he hed
  by_cases hex : e ≤ x
  · have helower : e ∈ lower := Finset.mem_filter.mpr ⟨he, hex⟩
    have hec : e ≤ c := by simpa using hcmax e helower
    exact (not_lt_of_ge hec) hed.1
  · have hxe : x ≤ e := (lt_of_not_ge hex).le
    have heupper : e ∈ upper := Finset.mem_filter.mpr ⟨he, hxe⟩
    have hde : d ≤ e := by simpa using hdmin e heupper
    exact (not_lt_of_ge hde) hed.2


theorem finitePiecePL_descendedMap
    (π : CanonicalFiniteIntervalQuotient) (T : IntervalMap)
    (hT : FinitePiecePL T) (hrespect : RespectsFibres π.toFun T) :
    FinitePiecePL (descendedMap π T hrespect) := by
  classical
  let H : IntervalMap := π.toFun ∘ T
  have hH : FinitePiecePL H := by
    dsimp [H]
    exact finitePiecePL_comp_descendedPL π.finitePiecePL_toFun hT
  rcases π.finitePiecePL_toFun.2 with ⟨pπ, hπcells⟩
  rcases hH.2 with ⟨pH, hHcells⟩
  let imageπ : {x : ℝ // x ∈ pπ.points} → ℝ := fun x ↦
    (π (⟨x, pπ.points_subset x.property⟩ : I) : ℝ)
  let imageH : {x : ℝ // x ∈ pH.points} → ℝ := fun x ↦
    (π (⟨x, pH.points_subset x.property⟩ : I) : ℝ)
  let targetPoints : Finset ℝ :=
    pπ.points.attach.image imageπ ∪ pH.points.attach.image imageH
  have hπleft : π leftEndpoint = leftEndpoint := by
    obtain ⟨x, hx⟩ := π.surjective_toFun leftEndpoint
    apply Subtype.ext
    change (π leftEndpoint : ℝ) = 0
    have hmono := π.monotone_toFun
      (show leftEndpoint ≤ x by exact x.property.1)
    have hxreal := congrArg Subtype.val hx
    have hlower := (π leftEndpoint).property.1
    change (π leftEndpoint : ℝ) ≤ (π x : ℝ) at hmono
    change (π x : ℝ) = 0 at hxreal
    linarith
  have hπright : π rightEndpoint = rightEndpoint := by
    obtain ⟨x, hx⟩ := π.surjective_toFun rightEndpoint
    apply Subtype.ext
    change (π rightEndpoint : ℝ) = 1
    have hmono := π.monotone_toFun
      (show x ≤ rightEndpoint by exact x.property.2)
    have hxreal := congrArg Subtype.val hx
    have hupper := (π rightEndpoint).property.2
    change (π x : ℝ) ≤ (π rightEndpoint : ℝ) at hmono
    change (π x : ℝ) = 1 at hxreal
    linarith
  let q : RealPartition :=
    { points := targetPoints
      zero_mem := by
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨⟨0, pπ.zero_mem⟩, Finset.mem_attach _ _, ?_⟩
        dsimp [imageπ]
        exact congrArg Subtype.val hπleft
      one_mem := by
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨⟨1, pπ.one_mem⟩, Finset.mem_attach _ _, ?_⟩
        dsimp [imageπ]
        exact congrArg Subtype.val hπright
      points_subset := by
        intro y hy
        rcases Finset.mem_union.mp hy with hy | hy
        · rcases Finset.mem_image.mp hy with ⟨x, _hx, rfl⟩
          exact (π (⟨x, pπ.points_subset x.property⟩ : I)).property
        · rcases Finset.mem_image.mp hy with ⟨x, _hx, rfl⟩
          exact (π (⟨x, pH.points_subset x.property⟩ : I)).property }
  refine ⟨continuous_descendedMap π hT.1 hrespect, q, ?_⟩
  intro u v huv
  have huvlt : u < v := huv.2.2.1
  let yreal : ℝ := (u + v) / 2
  have hyuv : yreal ∈ Set.Ioo u v := by
    dsimp [yreal]
    constructor <;> linarith
  have hyI : yreal ∈ I :=
    ⟨(q.points_subset huv.1).1.trans hyuv.1.le,
      hyuv.2.le.trans (q.points_subset huv.2.1).2⟩
  let y : I := ⟨yreal, hyI⟩
  obtain ⟨x, hx⟩ := π.surjective_toFun y
  have hπxreal : (π x : ℝ) = yreal := congrArg Subtype.val hx
  have hxnotπ : (x : ℝ) ∉ pπ.points := by
    intro hxp
    have himage : (π x : ℝ) ∈ q.points := by
      change (π x : ℝ) ∈ targetPoints
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      exact ⟨⟨(x : ℝ), hxp⟩, Finset.mem_attach _ _, rfl⟩
    exact huv.2.2.2 (π x : ℝ) himage
      (by simpa [hπxreal] using hyuv)
  have hxnotH : (x : ℝ) ∉ pH.points := by
    intro hxp
    have himage : (π x : ℝ) ∈ q.points := by
      change (π x : ℝ) ∈ targetPoints
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨⟨(x : ℝ), hxp⟩, Finset.mem_attach _ _, rfl⟩
    exact huv.2.2.2 (π x : ℝ) himage
      (by simpa [hπxreal] using hyuv)
  obtain ⟨a, b, hab, hax, hxb⟩ :=
    pπ.exists_adjacent_around_descendedPL x.property hxnotπ
  obtain ⟨m, c, hπformula⟩ := hπcells hab
  let aI : I := ⟨a, pπ.points_subset hab.1⟩
  let bI : I := ⟨b, pπ.points_subset hab.2.1⟩
  have haCell : aI ∈ intervalCell a b := ⟨le_rfl, hab.2.2.1.le⟩
  have hbCell : bI ∈ intervalCell a b := ⟨hab.2.2.1.le, le_rfl⟩
  have hxCell : x ∈ intervalCell a b := ⟨hax.le, hxb.le⟩
  have hπa := hπformula aI haCell
  have hπb := hπformula bI hbCell
  have hπxform := hπformula x hxCell
  have hπaTarget : (π aI : ℝ) ∈ q.points := by
    change (π aI : ℝ) ∈ targetPoints
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨⟨a, hab.1⟩, Finset.mem_attach _ _, rfl⟩
  have hπbTarget : (π bI : ℝ) ∈ q.points := by
    change (π bI : ℝ) ∈ targetPoints
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨⟨b, hab.2.1⟩, Finset.mem_attach _ _, rfl⟩
  have hmne : m ≠ 0 := by
    intro hmzero
    have hπax : (π aI : ℝ) = (π x : ℝ) := by
      rw [hπa, hπxform, hmzero]
      ring
    apply huv.2.2.2 (π aI : ℝ) hπaTarget
    rw [hπax, hπxreal]
    exact hyuv
  have hmnonneg : 0 ≤ m := by
    have hmono := π.monotone_toFun (show aI ≤ x from hax.le)
    change (π aI : ℝ) ≤ (π x : ℝ) at hmono
    rw [hπa, hπxform] at hmono
    nlinarith
  have hm : 0 < m := lt_of_le_of_ne hmnonneg (Ne.symm hmne)
  have hπale : (π aI : ℝ) ≤ u := by
    apply le_of_not_gt
    intro hua
    apply huv.2.2.2 (π aI : ℝ) hπaTarget
    refine ⟨hua, ?_⟩
    have hmono := π.monotone_toFun (show aI ≤ x from hax.le)
    change (π aI : ℝ) ≤ (π x : ℝ) at hmono
    rw [hπxreal] at hmono
    exact hmono.trans_lt hyuv.2
  have hvleπb : v ≤ (π bI : ℝ) := by
    apply le_of_not_gt
    intro hbv
    apply huv.2.2.2 (π bI : ℝ) hπbTarget
    refine ⟨?_, hbv⟩
    have hmono := π.monotone_toFun (show x ≤ bI from hxb.le)
    change (π x : ℝ) ≤ (π bI : ℝ) at hmono
    rw [hπxreal] at hmono
    exact hyuv.1.trans_le hmono
  let xu : ℝ := (u - c) / m
  let xv : ℝ := (v - c) / m
  have haxu : a ≤ xu := by
    dsimp [xu]
    apply (le_div_iff₀ hm).2
    rw [hπa] at hπale
    linarith
  have hxub : xu ≤ b := by
    dsimp [xu]
    apply (div_le_iff₀ hm).2
    rw [hπb] at hvleπb
    linarith
  have haxv : a ≤ xv := by
    dsimp [xv]
    apply (le_div_iff₀ hm).2
    rw [hπa] at hπale
    linarith
  have hxvb : xv ≤ b := by
    dsimp [xv]
    apply (div_le_iff₀ hm).2
    rw [hπb] at hvleπb
    linarith
  have hxult : xu < xv := by
    dsimp [xu, xv]
    exact div_lt_div_of_pos_right (sub_lt_sub_right huvlt c) hm
  have hxuI : xu ∈ I :=
    ⟨(pπ.points_subset hab.1).1.trans haxu,
      hxub.trans (pπ.points_subset hab.2.1).2⟩
  have hxvI : xv ∈ I :=
    ⟨(pπ.points_subset hab.1).1.trans haxv,
      hxvb.trans (pπ.points_subset hab.2.1).2⟩
  have hnoneH : ∀ z ∈ pH.points, ¬(xu < z ∧ z < xv) := by
    intro z hz hbetween
    let zI : I := ⟨z, pH.points_subset hz⟩
    have hzCell : zI ∈ intervalCell a b :=
      ⟨(haxu.trans_lt hbetween.1).le,
        (hbetween.2.trans_le hxvb).le⟩
    have hπz := hπformula zI hzCell
    have hπzTarget : (π zI : ℝ) ∈ q.points := by
      change (π zI : ℝ) ∈ targetPoints
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩
    apply huv.2.2.2 (π zI : ℝ) hπzTarget
    dsimp [xu, xv] at hbetween
    rw [hπz]
    change u < m * z + c ∧ m * z + c < v
    have hleft := (div_lt_iff₀ hm).1 hbetween.1
    have hright := (lt_div_iff₀ hm).1 hbetween.2
    constructor <;> nlinarith
  let xuI : I := ⟨xu, hxuI⟩
  let xvI : I := ⟨xv, hxvI⟩
  obtain ⟨d, e, hde, hsource⟩ :=
    pH.exists_adjacent_superset hxuI hxvI hxult hnoneH
  obtain ⟨r, s, hHformula⟩ := hHcells hde
  refine ⟨r / m, s - r * c / m, ?_⟩
  intro z hz
  have hzpreI : ((z : ℝ) - c) / m ∈ I := by
    have hzlower : xu ≤ ((z : ℝ) - c) / m := by
      dsimp [xu]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.1 c) hm.le
    have hzupper : ((z : ℝ) - c) / m ≤ xv := by
      dsimp [xv]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.2 c) hm.le
    exact ⟨hxuI.1.trans hzlower, hzupper.trans hxvI.2⟩
  let zpre : I := ⟨((z : ℝ) - c) / m, hzpreI⟩
  have hzpreBounds : (zpre : ℝ) ∈ Set.Icc xu xv := by
    constructor
    · dsimp [xu, zpre]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.1 c) hm.le
    · dsimp [xv, zpre]
      exact div_le_div_of_nonneg_right (sub_le_sub_right hz.2 c) hm.le
  have hzpreCell : zpre ∈ intervalCell a b := by
    exact ⟨haxu.trans hzpreBounds.1, hzpreBounds.2.trans hxvb⟩
  have hπpre : π zpre = z := by
    apply Subtype.ext
    have hformula := hπformula zpre hzpreCell
    change (π zpre : ℝ) = (z : ℝ)
    rw [hformula]
    dsimp [zpre]
    field_simp [hm.ne']
    ring
  have hdesc : descendedMap π T hrespect z = H zpre := by
    calc
      descendedMap π T hrespect z =
          descendedMap π T hrespect (π zpre) := by rw [hπpre]
      _ = π (T zpre) := (intertwines_descendedMap π T hrespect zpre).symm
      _ = H zpre := rfl
  calc
    (descendedMap π T hrespect z : ℝ) = (H zpre : ℝ) :=
      congrArg Subtype.val hdesc
    _ = r * (zpre : ℝ) + s := hHformula zpre (hsource hzpreBounds)
    _ = r / m * (z : ℝ) + (s - r * c / m) := by
      dsimp [zpre]
      field_simp [hm.ne']
      ring

end CommutingIntervalSimplified

