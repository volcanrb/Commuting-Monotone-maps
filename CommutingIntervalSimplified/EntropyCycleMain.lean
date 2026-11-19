import CommutingIntervalSimplified.EntropyCycleIntervals
import CommutingIntervalSimplified.OmegaCycleSplitting

/-!
# The common inverse cycle when one generator has zero entropy

For commuting continuous self-maps of the compact unit interval, vanishing
Bowen–Dinaburg topological entropy of either map gives a finite orbit in
the fixed set of the composition on which the two maps act inversely.
-/

namespace CommutingIntervalSimplified

open Function Set Filter Dynamics

private theorem inverseCommonCycle_of_zero_entropy_left {f g : IntervalMap}
    (hf : Continuous f) (hg : Continuous g) (hc : Function.Commute f g)
    (hz : coverEntropy f univ = 0) : HasInverseCommonCycle f g := by
  by_contra hno
  obtain ⟨x, hx, hbetween⟩ := exists_product_fixed_between hf hg hc
  have hK : IsClosed (fixedPoints (f ∘ g)) := isClosed_eq (hf.comp hg) continuous_id
  have hback := orbitOmega_subset_of_invariant hK (prodFixed_maps hc).2 hx
  obtain ⟨M, hMsub, hM, hne, hinv, hmin⟩ := exists_minimal_orbitOmega hf
    (isClosed_omegaLimit ..) (nonempty_omegaLimit atTop (fun n : ℕ => g^[n]) {x}
      (singleton_nonempty x)) (productFixed_backwardOmega_invariant hf hc hx)
  have haper (z : I) (hzM : z ∈ M) : z ∉ periodicPts f := fun hp =>
    hno (inverseCommonCycle_of_productFixed_periodic hc (hback (hMsub hzM)) hp)
  obtain ⟨q, hq, _, hflip⟩ := alternating_cut_of_minimal_zero_entropy hf hz hM hne hinv hmin
    (fun z hzM he => haper z hzM (mk_mem_periodicPts (n := 1) (by decide) he))
  obtain ⟨L, R, hd, hL, hR, y, hy, hinside⟩ :=
    exchanged_intervals_of_alternating_cut hf hz hM hne hinv haper hq hflip
  exact productFixed_not_between_of_backward_enters_exchanged hf hc hx (hMsub hy) hd hL hR
    (n := 0) (Or.inl hinside) hbetween

/-- The zero-entropy clause of the common-cycle theorem, allowing either
commuting generator to have zero topological entropy. -/
theorem inverseCommonCycle_of_zero_entropy {f g : IntervalMap}
    (hf : Continuous f) (hg : Continuous g) (hc : Function.Commute f g)
    (hz : coverEntropy f univ = 0 ∨ coverEntropy g univ = 0) :
    HasInverseCommonCycle f g := by
  rcases hz with hz | hz
  · exact inverseCommonCycle_of_zero_entropy_left hf hg hc hz
  · exact (inverseCommonCycle_of_zero_entropy_left hg hf hc.symm hz).symm hc.symm

end CommutingIntervalSimplified
