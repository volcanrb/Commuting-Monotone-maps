import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Data.ZMod.Basic

namespace CommutingInterval

open Function Set Filter
open scoped Pointwise Topology

/-- Any degree-one monotone semiconjugacy from a circle homeomorphism to an
irrational translation has dense range.  This is the topological half of
the Denjoy upgrade; bounded variation is needed only for injectivity. -/
theorem irrationalTranslation_semiconj_denseRange
    (F : CircleDeg1Liftˣ) (H : CircleDeg1Lift) (alpha : ℝ)
    (hirr : Irrational alpha)
    (hsemiconj : Function.Semiconj H (F : CircleDeg1Lift)
      (CircleDeg1Lift.translate (Multiplicative.ofAdd alpha))) :
    DenseRange H := by
  have horbit : ∀ n : ℤ, ∃ x : ℝ,
      H x = H 0 + (n : ℝ) * alpha := by
    intro n
    induction n using Int.induction_on with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
        rcases ih with ⟨x, hx⟩
        refine ⟨F x, ?_⟩
        calc
          H (F x) = H x + alpha := by
            simpa [CircleDeg1Lift.translate_apply, add_comm] using hsemiconj x
          _ = H 0 + ((n + 1 : ℤ) : ℝ) * alpha := by
            rw [hx]
            push_cast
            ring
    | pred n ih =>
        rcases ih with ⟨x, hx⟩
        let y : ℝ := (CircleDeg1Lift.toOrderIso F).symm x
        have hFy : F y = x := by simp [y]
        have hy := hsemiconj y
        refine ⟨y, ?_⟩
        rw [hFy] at hy
        simp only [CircleDeg1Lift.translate_apply] at hy
        calc
          H y = H x - alpha := by linarith
          _ = H 0 + ((-(n : ℤ) - 1 : ℤ) : ℝ) * alpha := by
            rw [hx]
            push_cast
            ring
  let C := AddCircle (1 : ℝ)
  let r : C := (H 0 : ℝ)
  let abar : C := (alpha : ℝ)
  have habar : DenseRange (fun n : ℤ ↦ n • abar) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa [abar] using hirr
  have haddSurj : Function.Surjective (fun z : C ↦ r + z) := by
    intro z
    exact ⟨z - r, by simp⟩
  have haddCont : Continuous (fun z : C ↦ r + z) := by
    fun_prop
  have horbitDense : DenseRange (fun n : ℤ ↦ r + n • abar) := by
    simpa only [Function.comp_apply] using
      haddSurj.denseRange.comp habar haddCont
  let S : Set C :=
    (fun x : ℝ ↦ (x : C)) '' Set.range H
  have horbitSubset :
      Set.range (fun n : ℤ ↦ r + n • abar) ⊆ S := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨x, hx⟩ := horbit n
    refine ⟨H x, ⟨x, rfl⟩, ?_⟩
    change (H x : C) = r + n • abar
    rw [hx]
    simp [r, abar, C]
  have hSdense : Dense S := horbitDense.mono horbitSubset
  have hpreDense :
      Dense ((fun x : ℝ ↦ (x : C)) ⁻¹' S) := by
    exact QuotientAddGroup.dense_preimage_mk.mpr hSdense
  have hpreSubset :
      (fun x : ℝ ↦ (x : C)) ⁻¹' S ⊆ Set.range H := by
    intro y hy
    rcases hy with ⟨z, ⟨x, rfl⟩, hzy⟩
    have hdiff : y - H x ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      exact QuotientAddGroup.eq_iff_sub_mem.mp hzy.symm
    obtain ⟨k : ℤ, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hdiff
    refine ⟨x + (k : ℝ), ?_⟩
    rw [H.map_add_int]
    have hk' : y - H x = (k : ℝ) := by
      simpa using hk.symm
    linarith
  exact hpreDense.mono hpreSubset

/-- A sequence of nondegenerate real intervals which are pairwise disjoint
after every integral deck translation has lengths tending to zero.  The
proof uses a finite rational grid rather than measure theory. -/
theorem interval_lengths_tendsto_zero_of_disjoint_mod_int
    (l r : ℕ → ℝ)
    (hlt : ∀ n, l n < r n)
    (hdisjoint : ∀ m n : ℕ, m < n → ∀ k : ℤ,
      Disjoint (Set.Ioo (l m) (r m))
        (Set.Ioo (l n + (k : ℝ)) (r n + (k : ℝ)))) :
    Tendsto (fun n => r n - l n) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos : 0 < N := by
    by_contra hNzero
    have : N = 0 := Nat.eq_zero_of_not_pos hNzero
    subst N
    simp only [Nat.cast_zero] at hN
    have hone : 0 < 1 / ε := one_div_pos.mpr hε
    linarith
  let S : Set ℕ := {n | ε ≤ r n - l n}
  let z : S → ℤ := fun x => ⌊(N : ℝ) * l x⌋ + 1
  have hz_lower (x : S) :
      (N : ℝ) * l x < (z x : ℝ) := by
    dsimp [z]
    simpa only [Int.cast_add, Int.cast_one] using
      (Int.lt_floor_add_one ((N : ℝ) * l x))
  have hscaled (x : S) :
      1 < (N : ℝ) * (r x - l x) := by
    have hNreal : 1 / ε < (N : ℝ) := by exact_mod_cast hN
    have hmul : 1 < (N : ℝ) * ε := by
      have := (div_lt_iff₀ hε).mp hNreal
      simpa [one_div] using this
    exact hmul.trans_le (mul_le_mul_of_nonneg_left x.property
      (Nat.cast_nonneg N))
  have hz_upper (x : S) :
      (z x : ℝ) < (N : ℝ) * r x := by
    have hfloor := Int.floor_le ((N : ℝ) * l x)
    have hs := hscaled x
    dsimp [z]
    push_cast
    nlinarith
  have hgrid_mem (x : S) :
      (z x : ℝ) / (N : ℝ) ∈ Set.Ioo (l x) (r x) := by
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    constructor
    · exact (lt_div_iff₀ hNreal).mpr (by simpa [mul_comm] using hz_lower x)
    · exact (div_lt_iff₀ hNreal).mpr (by
        simpa [mul_comm] using hz_upper x)
  letI : NeZero N := ⟨hNpos.ne'⟩
  let φ : S → ZMod N := fun x => (z x : ZMod N)
  have hφ_injective : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    by_contra hval
    rcases lt_or_gt_of_ne hval with hxyval | hyxval
    · have hdvd : (N : ℤ) ∣ z y - z x :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (z x) (z y) N).mp hxy
      obtain ⟨k : ℤ, hk⟩ := hdvd
      have hgrid_eq :
          (z x : ℝ) / (N : ℝ) = (z y : ℝ) / (N : ℝ) - (k : ℝ) := by
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
        have hkR : (z y : ℝ) - (z x : ℝ) = (N : ℝ) * (k : ℝ) := by
          exact_mod_cast hk
        rw [eq_sub_iff_add_eq]
        field_simp [hNne]
        linarith [hkR]
      have hd := hdisjoint x y hxyval (-k)
      rw [Set.disjoint_left] at hd
      apply hd (hgrid_mem x)
      constructor
      · rw [hgrid_eq]
        have := (hgrid_mem y).1
        push_cast
        linarith
      · rw [hgrid_eq]
        have := (hgrid_mem y).2
        push_cast
        linarith
    · have hdvd : (N : ℤ) ∣ z y - z x :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (z x) (z y) N).mp hxy
      obtain ⟨k : ℤ, hk⟩ := hdvd
      have hgrid_eq :
          (z y : ℝ) / (N : ℝ) = (z x : ℝ) / (N : ℝ) + (k : ℝ) := by
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
        have hkR : (z y : ℝ) - (z x : ℝ) = (N : ℝ) * (k : ℝ) := by
          exact_mod_cast hk
        field_simp [hNne]
        linarith [hkR]
      have hd := hdisjoint y x hyxval k
      rw [Set.disjoint_left] at hd
      apply hd (hgrid_mem y)
      constructor
      · rw [hgrid_eq]
        simpa [add_comm] using add_lt_add_right (hgrid_mem x).1 (k : ℝ)
      · rw [hgrid_eq]
        simpa [add_comm] using add_lt_add_right (hgrid_mem x).2 (k : ℝ)
  haveI : Finite S := Finite.of_injective φ hφ_injective
  have hSfinite : S.Finite := Set.finite_coe_iff.mp inferInstance
  obtain ⟨M, hM⟩ := hSfinite.bddAbove
  refine ⟨M + 1, ?_⟩
  intro n hn
  have hn_not : n ∉ S := by
    intro hnS
    have := hM hnS
    omega
  have hnsmall : r n - l n < ε := by
    simpa [S, not_le] using hn_not
  have hnpos : 0 < r n - l n := sub_pos.mpr (hlt n)
  simpa [Real.dist_eq, abs_of_pos hnpos] using hnsmall

/-- A lift interval whose distinct forward images are disjoint modulo every
integer deck translation. -/
def IsForwardWanderingLiftInterval
    (F : CircleDeg1Liftˣ) (a b : ℝ) : Prop :=
  a < b ∧ ∀ m n : ℕ, m < n → ∀ k : ℤ,
    Disjoint
      (Set.Ioo (((F : CircleDeg1Lift) ^ m) a)
        (((F : CircleDeg1Lift) ^ m) b))
      (Set.Ioo (((F : CircleDeg1Lift) ^ n) a + (k : ℝ))
        (((F : CircleDeg1Lift) ^ n) b + (k : ℝ)))

/-- A nondegenerate flat fibre of a semiconjugacy to an irrational
translation is a forward wandering interval. -/
theorem flatFiber_isForwardWanderingLiftInterval
    (F : CircleDeg1Liftˣ) (H : CircleDeg1Lift) (alpha : ℝ)
    (hirr : Irrational alpha)
    (hsemiconj : Function.Semiconj H (F : CircleDeg1Lift)
      (CircleDeg1Lift.translate (Multiplicative.ofAdd alpha)))
    {a b : ℝ} (hab : a < b) (hflat : H a = H b) :
    IsForwardWanderingLiftInterval F a b := by
  have hiter : ∀ n : ℕ, ∀ x : ℝ,
      H (((F : CircleDeg1Lift) ^ n) x) =
        H x + (n : ℝ) * alpha := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ', CircleDeg1Lift.mul_apply]
        calc
          H (F (((F : CircleDeg1Lift) ^ n) x)) =
              alpha + H (((F : CircleDeg1Lift) ^ n) x) := by
            simpa [CircleDeg1Lift.translate_apply] using
              hsemiconj (((F : CircleDeg1Lift) ^ n) x)
          _ = H x + (n + 1 : ℕ) * alpha := by
            rw [ih]
            push_cast
            ring
  refine ⟨hab, ?_⟩
  intro m n hmn k
  rw [Set.disjoint_left]
  intro z hzm hzn
  have hHzm : H z = H a + (m : ℝ) * alpha := by
    apply le_antisymm
    · calc
        H z ≤ H (((F : CircleDeg1Lift) ^ m) b) :=
          H.monotone hzm.2.le
        _ = H b + (m : ℝ) * alpha := hiter m b
        _ = H a + (m : ℝ) * alpha := by rw [hflat]
    · calc
        H a + (m : ℝ) * alpha =
            H (((F : CircleDeg1Lift) ^ m) a) := (hiter m a).symm
        _ ≤ H z := H.monotone hzm.1.le
  have hHzn : H z = H a + (n : ℝ) * alpha + (k : ℝ) := by
    apply le_antisymm
    · calc
        H z ≤ H (((F : CircleDeg1Lift) ^ n) b + (k : ℝ)) :=
          H.monotone hzn.2.le
        _ = H (((F : CircleDeg1Lift) ^ n) b) + (k : ℝ) :=
          H.map_add_int _ k
        _ = H b + (n : ℝ) * alpha + (k : ℝ) := by rw [hiter]
        _ = H a + (n : ℝ) * alpha + (k : ℝ) := by rw [hflat]
    · calc
        H a + (n : ℝ) * alpha + (k : ℝ) =
            H (((F : CircleDeg1Lift) ^ n) a) + (k : ℝ) := by rw [hiter]
        _ = H (((F : CircleDeg1Lift) ^ n) a + (k : ℝ)) :=
          (H.map_add_int _ k).symm
        _ ≤ H z := H.monotone hzn.1.le
  have heq :
      H a + (m : ℝ) * alpha =
        H a + (n : ℝ) * alpha + (k : ℝ) := hHzm.symm.trans hHzn
  let d : ℤ := (n : ℤ) - (m : ℤ)
  have hd : d ≠ 0 := by
    dsimp [d]
    omega
  have halpha : alpha = ((-k : ℤ) : ℝ) / (d : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast hd)).mpr
    dsimp [d]
    push_cast
    linarith
  exact (hirr.ne_rational (-k) d) halpha

end CommutingInterval
