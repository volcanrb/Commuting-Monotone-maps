import CommutingIntervalSimplified.Base
import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Order.Preorder.Finite

/-!
# A common cycle in the fixed set of the composition

For commuting continuous maps of the unit interval, clamping the composition
between the two generators produces a product fixed point between its two
neighbors. A backward orbit accumulating on an orbit trapped by an exchanged
pair cannot have this property. This gives an interval proof of the
omega-limit criterion which does not require a fixed-point index.
-/

namespace CommutingIntervalSimplified

open Function Set Filter
open scoped Topology

/-- The forward omega-limit set of a point under iteration. -/
def orbitOmega (f : IntervalMap) (x : I) : Set I :=
  omegaLimit atTop (fun n : ℕ => f^[n]) {x}

/-- The splitting hypothesis for the fixed set of the composition. -/
def HasExchangedOmegaIntervals (f g : IntervalMap) : Prop :=
  ∀ x ∈ fixedPoints (f ∘ g), (orbitOmega f x).Infinite →
    ∃ L R : ClosedSubinterval, Disjoint L.carrier R.carrier ∧
      MapsTo f L.carrier R.carrier ∧ MapsTo f R.carrier L.carrier ∧
      orbitOmega f x ⊆ L.carrier ∪ R.carrier

/-- A nonempty finite cycle in the product fixed set, with `f` as its
successor map and `g` as its predecessor map, including at the wrap-around. -/
def HasInverseCommonCycle (f g : IntervalMap) : Prop :=
  ∃ x ∈ periodicPts f, (∀ y ∈ periodicOrbit f x, y ∈ fixedPoints (f ∘ g)) ∧
    (periodicOrbit f x).Chain (fun a b => f a = b ∧ g b = a)

/-- A product fixed point which lies between its two images. -/
theorem exists_product_fixed_between {f g : IntervalMap}
    (hf : Continuous f) (hg : Continuous g) (hc : Function.Commute f g) :
    ∃ x ∈ fixedPoints (f ∘ g), x ∈ uIcc (f x) (g x) := by
  let H : IntervalMap := fun x =>
    max (min (f x) (g x)) (min (f (g x)) (max (f x) (g x)))
  obtain ⟨x, hx⟩ := IntervalMap.exists_fixedPoint
    (show Continuous H from (hf.min hg).max ((hf.comp hg).min (hf.max hg)))
  change max (min (f x) (g x)) (min (f (g x)) (max (f x) (g x))) = x at hx
  have hfix₁ (h : x = f x) : f (g x) = g x := (hc x).trans (congrArg g h.symm)
  have hfix₂ (h : x = g x) : f (g x) = f x := congrArg f h.symm
  refine ⟨x, ?_, ?_⟩
  · change f (g x) = x
    grind
  · change min (f x) (g x) ≤ x ∧ x ≤ max (f x) (g x)
    grind

theorem cluster_iff_mem_orbitOmega (f : IntervalMap) (x y : I) :
    MapClusterPt y atTop (fun n : ℕ => f^[n] x) ↔ y ∈ orbitOmega f x :=
  (mem_omegaLimit_singleton_iff_mapClusterPt _ _ _ _).symm

theorem orbitOmega_subset_of_invariant {f : IntervalMap} {K : Set I}
    (hK : IsClosed K) (hmap : MapsTo f K K) {x : I} (hx : x ∈ K) :
    orbitOmega f x ⊆ K := by
  intro y hy
  exact hK.mem_of_mapClusterPt ((cluster_iff_mem_orbitOmega ..).mpr hy)
    (Eventually.of_forall fun n => hmap.iterate n hx)

theorem orbitOmega_forward {f : IntervalMap} (hf : Continuous f) (x : I) :
    MapsTo f (orbitOmega f x) (orbitOmega f x) := by
  intro y hy
  apply (cluster_iff_mem_orbitOmega ..).mp
  have hc := MapClusterPt.continuousAt_comp hf.continuousAt
    ((cluster_iff_mem_orbitOmega ..).mpr hy)
  apply MapClusterPt.of_comp (φ := fun n : ℕ => n + 1) (tendsto_add_atTop_nat 1)
  simpa only [comp_def, iterate_succ_apply'] using hc

theorem finite_orbitOmega_has_periodicPt {f : IntervalMap} (hf : Continuous f)
    {x : I} (hfin : (orbitOmega f x).Finite) :
    ∃ y ∈ orbitOmega f x, y ∈ periodicPts f := by
  obtain ⟨z, hz⟩ := nonempty_omegaLimit atTop (fun n : ℕ => f^[n]) {x} (singleton_nonempty x)
  have horb (n : ℕ) : f^[n] z ∈ orbitOmega f x := (orbitOmega_forward hf x).iterate n hz
  obtain ⟨m, n, hmn, heq⟩ := hfin.exists_lt_map_eq_of_forall_mem horb
  refine ⟨f^[m] z, horb _, mem_periodicPts.mpr ⟨n-m, by omega, ?_⟩⟩
  change f^[n-m] (f^[m] z) = f^[m] z
  rw [← iterate_add_apply, Nat.sub_add_cancel hmn.le]
  exact heq.symm

theorem prodFixed_maps {f g : IntervalMap} (hc : Function.Commute f g) :
    MapsTo f (fixedPoints (f ∘ g)) (fixedPoints (f ∘ g)) ∧
    MapsTo g (fixedPoints (f ∘ g)) (fixedPoints (f ∘ g)) := by
  constructor <;> intro x (hx : f (g x) = x)
  · change f (g (f x)) = f x
    rw [← hc x, hx]
  · change f (g (g x)) = g x
    rw [hc (g x), hx]

/-- A periodic point of the first map in the fixed set of the product
generates the required finite cyclic permutation and its inverse. -/
theorem inverseCommonCycle_of_productFixed_periodic {f g : IntervalMap}
    (hc : Function.Commute f g) {x : I} (hx : x ∈ fixedPoints (f ∘ g))
    (hp : x ∈ periodicPts f) : HasInverseCommonCycle f g := by
  have hiter (n : ℕ) : f^[n] x ∈ fixedPoints (f ∘ g) := (prodFixed_maps hc).1.iterate n hx
  refine ⟨x, hp, ?_, (periodicOrbit_chain' _ hp).mpr ?_⟩
  · intro y hy
    obtain ⟨n, rfl⟩ := (mem_periodicOrbit_iff hp).mp hy
    exact hiter n
  · intro n
    rw [iterate_succ_apply']
    exact ⟨rfl, (hc _).symm.trans (hiter n)⟩

/-- Interchanging the two generators reverses the common cycle. -/
theorem HasInverseCommonCycle.symm {f g : IntervalMap} (h : HasInverseCommonCycle f g)
    (hc : Function.Commute f g) : HasInverseCommonCycle g f := by
  obtain ⟨x, hx, hK, _⟩ := h
  have hfix : IsFixedPt (f ∘ g) x := hK x (self_mem_periodicOrbit hx)
  obtain ⟨n, hn, hp⟩ := mem_periodicPts.mp hx
  have he := hfix.iterate n
  rw [hc.comp_iterate] at he
  change f^[n] (g^[n] x) = x at he
  rw [((hc.iterate_left n).iterate_right n) x, hp.eq] at he
  exact inverseCommonCycle_of_productFixed_periodic hc.symm
    ((hc x).symm.trans hfix) (mem_periodicPts.mpr ⟨n, hn, he⟩)

private theorem enters_exchanged_interiors {f : IntervalMap} {x : I} {L R : ClosedSubinterval}
    (hinf : (orbitOmega f x).Infinite) (hsub : orbitOmega f x ⊆ L.carrier ∪ R.carrier) :
    ∃ n : ℕ, f^[n] x ∈ Ioo L.left L.right ∪ Ioo R.left R.right := by
  classical
  let E : Finset I := {L.left, L.right, R.left, R.right}
  obtain ⟨y, hy, hyE⟩ := hinf.exists_notMem_finset E
  simp only [E, Finset.mem_insert, Finset.mem_singleton, not_or] at hyE
  have hyU : y ∈ Ioo L.left L.right ∪ Ioo R.left R.right := by
    rcases hsub hy with h | h
    · exact Or.inl ⟨lt_of_le_of_ne h.1 (Ne.symm hyE.1), lt_of_le_of_ne h.2 hyE.2.1⟩
    · exact Or.inr ⟨lt_of_le_of_ne h.1 (Ne.symm hyE.2.2.1), lt_of_le_of_ne h.2 hyE.2.2.2⟩
  exact (mapClusterPt_iff_frequently.mp ((cluster_iff_mem_orbitOmega ..).mpr hy) _
    ((isOpen_Ioo.union isOpen_Ioo).mem_nhds hyU)).exists

theorem exchanged_midpoint_outside {f : IntervalMap} {L R : ClosedSubinterval}
    (hd : Disjoint L.carrier R.carrier) (hL : MapsTo f L.carrier R.carrier)
    (hR : MapsTo f R.carrier L.carrier) {u : I} (hu : u ∈ L.carrier ∪ R.carrier) :
    f u ∉ uIcc u (f (f u)) := by
  have sep : L.right < R.left ∨ R.right < L.left := by
    by_contra! h
    have hzL : max L.left R.left ∈ L.carrier :=
      ⟨le_max_left .., max_le L.left_le_right h.1⟩
    have hzR : max L.left R.left ∈ R.carrier :=
      ⟨le_max_right .., max_le h.2 R.left_le_right⟩
    exact disjoint_left.mp hd hzL hzR
  intro hbetween
  rcases hu with hu | hu
  · have hv := hL hu
    have hw := hR hv
    rcases sep with h | h
    · exact (not_lt_of_ge hbetween.2)
        ((max_le hu.2 hw.2).trans_lt (h.trans_le hv.1))
    · exact (not_lt_of_ge hbetween.1)
        ((hv.2.trans_lt h).trans_le (le_min hu.1 hw.1))
  · have hv := hR hu
    have hw := hL hv
    rcases sep with h | h
    · exact (not_lt_of_ge hbetween.1)
        ((hv.2.trans_lt h).trans_le (le_min hu.1 hw.1))
    · exact (not_lt_of_ge hbetween.2)
        ((max_le hu.2 hw.2).trans_lt (h.trans_le hv.1))

/-- A backward limit whose forward orbit enters an exchanged interval pair
forces the two immediate neighbors of the original point to lie on one side. -/
theorem productFixed_not_between_of_backward_enters_exchanged {f g : IntervalMap}
    (hf : Continuous f) (hc : Function.Commute f g) {x y : I}
    (hx : x ∈ fixedPoints (f ∘ g)) (hy : y ∈ orbitOmega g x)
    {L R : ClosedSubinterval} (hd : Disjoint L.carrier R.carrier)
    (hL : MapsTo f L.carrier R.carrier) (hR : MapsTo f R.carrier L.carrier)
    {n : ℕ} (hn : f^[n] y ∈ Ioo L.left L.right ∪ Ioo R.left R.right) :
    x ∉ uIcc (f x) (g x) := by
  let U := Ioo L.left L.right ∪ Ioo R.left R.right
  have hnear : (f^[n]) ⁻¹' U ∈ 𝓝 y :=
    ((isOpen_Ioo.union isOpen_Ioo).preimage (hf.iterate n)).mem_nhds hn
  have hfreq := mapClusterPt_iff_frequently.mp ((cluster_iff_mem_orbitOmega g x y).mpr hy) _ hnear
  obtain ⟨m, hm, hmn⟩ := frequently_atTop.mp hfreq (n+1)
  have hmem : f^[n] (g^[m] x) ∈ L.carrier ∪ R.carrier := by
    rcases hmn with h | h
    · exact Or.inl ⟨h.1.le, h.2.le⟩
    · exact Or.inr ⟨h.1.le, h.2.le⟩
  have hinv : MapsTo f (L.carrier ∪ R.carrier) (L.carrier ∪ R.carrier) :=
    fun _ h => h.elim (fun h => Or.inr (hL h)) (fun h => Or.inl (hR h))
  have htrap := hinv.iterate (m-1-n) hmem
  rw [← iterate_add_apply, show m-1-n+n=m-1 by omega] at htrap
  have hfgx : IsFixedPt (f ∘ g) (g x) := (prodFixed_maps hc).2 hx
  have hcancel : f^[m-1] (g^[m] x) = g x := by
    have he := hfgx.iterate (m-1)
    rw [hc.comp_iterate] at he
    change f^[m-1] (g^[m-1] (g x)) = g x at he
    simpa only [← iterate_succ_apply, show (m-1).succ=m by omega] using he
  rw [hcancel] at htrap
  have hcontra := exchanged_midpoint_outside hd hL hR htrap
  change f (g x) = x at hx
  rw [hx] at hcontra
  exact fun h => hcontra (uIcc_comm (f x) (g x) ▸ h)

/-- The common-cycle theorem under the manuscript's exchanged-interval
hypothesis for infinite omega-limit sets in `Fix(f ∘ g)`. -/
theorem inverseCommonCycle_of_exchangedOmegaIntervals {f g : IntervalMap}
    (hf : Continuous f) (hg : Continuous g) (hc : Function.Commute f g)
    (hsplit : HasExchangedOmegaIntervals f g) : HasInverseCommonCycle f g := by
  obtain ⟨x, hx, hbetween⟩ := exists_product_fixed_between hf hg hc
  have hK : IsClosed (fixedPoints (f ∘ g)) := isClosed_eq (hf.comp hg) continuous_id
  obtain ⟨y, hy⟩ := nonempty_omegaLimit atTop (fun n : ℕ => g^[n]) {x} (singleton_nonempty x)
  have hyK := orbitOmega_subset_of_invariant hK (prodFixed_maps hc).2 hx hy
  by_cases hfin : (orbitOmega f y).Finite
  · obtain ⟨z, hz, hzp⟩ := finite_orbitOmega_has_periodicPt hf hfin
    exact inverseCommonCycle_of_productFixed_periodic hc
      (orbitOmega_subset_of_invariant hK (prodFixed_maps hc).1 hyK hz) hzp
  obtain ⟨L, R, hd, hL, hR, hsub⟩ := hsplit y hyK hfin
  obtain ⟨n, hn⟩ := enters_exchanged_interiors hfin hsub
  exact (productFixed_not_between_of_backward_enters_exchanged hf hc hx hy hd hL hR hn hbetween).elim

end CommutingIntervalSimplified
