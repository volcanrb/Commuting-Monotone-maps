import CommutingIntervalSimplified.Base
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The finite decoder construction

The finite construction in Section 2 of *Common periodic points of commuting
interval maps* uses a pair of colors. The map for a color decodes its own
cells. Its values on the other cells solve a contraction equation in the
uniform metric. The shared endpoint marks guarantee continuous gluing.
-/

namespace CommutingIntervalSimplified

open Function Set
open scoped NNReal BoundedContinuousFunction

/-- Paste interval maps on a locally finite closed cover in the uniform
function space. The compatibility condition includes shared endpoints. -/
theorem exists_glued_interval_map {C : Type*} (cell : C → Set I)
    (hclosed : ∀ j, IsClosed (cell j)) (hfinite : LocallyFinite cell)
    (hcover : ∀ x, ∃ j, x ∈ cell j) (branch : C → I → I)
    (hcont : ∀ j, ContinuousOn (branch j) (cell j))
    (hagree : ∀ j k x, x ∈ cell j → x ∈ cell k → branch j x = branch k x) :
    ∃ f : I →ᵇ I, ∀ j x, x ∈ cell j → f x = branch j x := by
  classical
  let f (x : I) := branch (hcover x).choose x
  have heq (j : C) (x : I) (hx : x ∈ cell j) : f x = branch j x :=
    hagree _ _ _ (hcover x).choose_spec hx
  have hf : Continuous f := hfinite.continuous (iUnion_eq_univ_iff.mpr hcover)
    hclosed (fun j => (hcont j).congr (heq j))
  exact ⟨BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩, heq⟩

/-- A colored finite cover with contracting sections and matching endpoint marks.
The decoder is extended continuously outside its cell for convenience. -/
structure FiniteDecoderSystem (C : Type*) where
  color : C → Bool
  next : C → C
  cell : C → Set I
  cell_closed : ∀ j, IsClosed (cell j)
  cover : ∀ x, ∃ j, x ∈ cell j
  color_next : ∀ j, color (next j) = color j
  sectionMap : C → I → I
  decoder : C → I → I
  decoder_cont : ∀ j, Continuous (decoder j)
  q : ℝ≥0
  q_lt : q < 1
  section_lip : ∀ j, LipschitzWith q (sectionMap j)
  section_mem : ∀ j x, sectionMap j x ∈ cell j
  decode_section : ∀ j x, decoder j (sectionMap j x) = x
  overlap : ∀ {j k x}, j ≠ k → x ∈ cell j → x ∈ cell k →
    color j ≠ color k ∧ decoder j x = sectionMap (next k) leftEndpoint
  cell_unique : ∀ {j k x}, x ∈ cell j → x ∈ range (sectionMap k) → j = k

namespace FiniteDecoderSystem

variable {C : Type*} [Finite C] (S : FiniteDecoderSystem C)

private theorem glue (i : Bool) (opp : C → I → I)
    (hc : ∀ j, Continuous (opp j))
    (hm : ∀ j k x, S.color j = i → S.color k ≠ i → x ∈ S.cell j →
      x ∈ S.cell k → S.decoder j x = opp k x) :
    ∃ f : I →ᵇ I,
      (∀ j, S.color j = i → ∀ x ∈ S.cell j, f x = S.decoder j x) ∧
      (∀ j, S.color j ≠ i → ∀ x ∈ S.cell j, f x = opp j x) := by
  classical
  let branch (j : C) := if S.color j = i then S.decoder j else opp j
  have hbranch (j k : C) (x : I) (hj : x ∈ S.cell j) (hk : x ∈ S.cell k) :
      branch j x = branch k x := by
    by_cases he : j = k
    · subst k; rfl
    have hdiff := (S.overlap he hj hk).1
    by_cases hji : S.color j = i <;> by_cases hki : S.color k = i
    · exact (hdiff (hji.trans hki.symm)).elim
    · simpa [branch, hji, hki] using hm j k x hji hki hj hk
    · simpa [branch, hji, hki] using (hm k j x hki hji hk hj).symm
    · cases h₁ : S.color j <;> cases h₂ : S.color k <;> cases i <;> simp_all
  obtain ⟨f, heq⟩ := exists_glued_interval_map S.cell S.cell_closed
    (locallyFinite_of_finite _) S.cover branch (fun j => by
      dsimp only [branch]; split
      · exact (S.decoder_cont j).continuousOn
      · exact (hc j).continuousOn) hbranch
  refine ⟨f, ?_, ?_⟩
  · intro j hj x hx
    simpa [branch, hj] using heq j x hx
  · intro j hj x hx
    simpa [branch, hj] using heq j x hx

/-- A continuous map with the prescribed decoder branches and the opposite-color
recursion. Both assertions hold also at the shared endpoints. -/
theorem exists_generator (i : Bool) :
    ∃ f : I →ᵇ I,
      (∀ j, S.color j = i → ∀ x ∈ S.cell j, f x = S.decoder j x) ∧
      (∀ j, S.color j ≠ i → ∀ x ∈ S.cell j,
        f x = S.sectionMap (S.next j) (f (S.decoder j x))) := by
  classical
  let A : Set (I →ᵇ I) := {f | ∀ j, S.color j = i → ∀ x ∈ S.cell j, f x = S.decoder j x}
  have hA : IsClosed A := by
    dsimp only [A]
    simp only [setOf_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun x =>
      isClosed_iInter fun _ => isClosed_eq (continuous_eval_const x) continuous_const
  letI : CompleteSpace A := hA.isComplete.completeSpace_coe
  obtain ⟨seed, hseed, _⟩ := S.glue i (fun j _ => S.sectionMap (S.next j) leftEndpoint)
    (fun _ => continuous_const) (fun j k x hj hk hx hy =>
      (S.overlap (j := j) (k := k) (fun h => hk (h ▸ hj)) hx hy).2)
  letI : Nonempty A := ⟨⟨seed, hseed⟩⟩
  have update (u : A) :
      ∃ v : A, ∀ j, S.color j ≠ i → ∀ x ∈ S.cell j,
        v.val x = S.sectionMap (S.next j) (u.val (S.decoder j x)) := by
    obtain ⟨v, hv, hr⟩ := S.glue i
      (fun j x => S.sectionMap (S.next j) (u.val (S.decoder j x)))
      (fun j => (S.section_lip _).continuous.comp (u.val.continuous.comp (S.decoder_cont j))) (by
        intro j k x hj hk hx hy
        have hne : j ≠ k := fun h => hk (h ▸ hj)
        change S.decoder j x = S.sectionMap (S.next k) (u.val (S.decoder k x))
        rw [(S.overlap hne hx hy).2, (S.overlap hne.symm hy hx).2,
          u.property (S.next j) ((S.color_next j).trans hj) _ (S.section_mem _ _),
          S.decode_section])
    exact ⟨⟨v, hv⟩, hr⟩
  let T (u : A) : A := (update u).choose
  have hT (u : A) := (update u).choose_spec
  have hcontract : ContractingWith S.q T := by
    refine ⟨S.q_lt, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    change dist (T u).val (T v).val ≤ (S.q : ℝ) * dist u.val v.val
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro x
    obtain ⟨j, hj⟩ := S.cover x
    by_cases hi : S.color j = i
    · rw [(T u).property j hi x hj, (T v).property j hi x hj, dist_self]
      positivity
    · change dist ((update u).choose.val x) ((update v).choose.val x) ≤ _
      rw [hT u j hi x hj, hT v j hi x hj]
      exact ((S.section_lip _).dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist _) S.q.2)
  let u := hcontract.fixedPoint T
  have hu : T u = u := hcontract.fixedPoint_isFixedPt
  refine ⟨u.val, u.property, ?_⟩
  intro j hj x hx
  calc u.val x = (T u).val x := by rw [hu]
       _ = _ := hT u j hj x hx

/-- The two generators commute, carry the opposite cells into successor cores,
and permute the section fixed points according to their colors. -/
theorem exists_commuting_generators :
    ∃ (F : Bool → I → I) (z : C → I),
      (∀ i, Continuous (F i)) ∧ Function.Commute (F false) (F true) ∧
      (∀ j, MapsTo (F (!S.color j)) (S.cell j) (range (S.sectionMap (S.next j)))) ∧
      (∀ j, F (S.color j) (z j) = z j) ∧
      (∀ j, F (!S.color j) (z j) = z (S.next j)) := by
  classical
  choose F own opp using S.exists_generator
  have decode (j : C) (x : I) : F (S.color j) (S.sectionMap j x) = x := by
    rw [own _ j rfl _ (S.section_mem j x), S.decode_section]
  have inter (j : C) (x : I) : F (!S.color j) (S.sectionMap j x) =
      S.sectionMap (S.next j) (F (!S.color j) x) := by
    rw [opp _ j (by cases S.color j <;> decide) _ (S.section_mem j x), S.decode_section]
  have exch (j : C) (x : I) (hx : x ∈ S.cell j) :
      F (S.color j) (F (!S.color j) x) = F (!S.color j) (F (S.color j) x) := by
    have hsuc (y : I) : F (S.color j) (S.sectionMap (S.next j) y) = y := by
      simpa only [S.color_next] using decode (S.next j) y
    rw [opp _ j (by cases S.color j <;> decide) x hx, own _ j rfl x hx, hsuc]
  have hs (j : C) : ContractingWith S.q (S.sectionMap j) := ⟨S.q_lt, S.section_lip j⟩
  let z (j : C) := (hs j).fixedPoint (S.sectionMap j)
  have hz (j : C) : S.sectionMap j (z j) = z j := (hs j).fixedPoint_isFixedPt
  refine ⟨fun i => F i, z, fun i => (F i).continuous, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨j, hj⟩ := S.cover x
    have h := exch j x hj
    cases hc : S.color j
    · simpa [hc] using h
    · simpa [hc] using h.symm
  · intro j x hx
    exact ⟨F (!S.color j) (S.decoder j x), (opp _ j (by cases S.color j <;> decide) _ hx).symm⟩
  · intro j
    simpa only [hz] using decode j (z j)
  · intro j
    apply (hs (S.next j)).fixedPoint_unique
    exact (inter j (z j)).symm.trans (congrArg _ (hz j))

end FiniteDecoderSystem

end CommutingIntervalSimplified
