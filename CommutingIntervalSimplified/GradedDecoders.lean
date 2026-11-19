import CommutingIntervalSimplified.FiniteReturnConstruction
import CommutingIntervalSimplified.GradedCells
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Continuous decoder families on the grid of grades

The direct and recursive equations of Proposition 3.6 are solved simultaneously
over all grades. A bounded continuous function on the discrete grade space
takes values in the uniform metric space of continuous interval maps. Its
uniform metric therefore controls all grades with a single contraction factor.
-/

namespace CommutingIntervalSimplified.GradedDecoders

open Function Set GradedCells
open scoped NNReal BoundedContinuousFunction

/-- The closed cells, sections and endpoint marks used to paste graded decoders.
Decoders are evaluated only on their own cells and are continuous there. -/
structure Pieces where
  cell : {v : Grade} → Cell v → Set I
  closed : ∀ {v} (J : Cell v), IsClosed (cell J)
  cover : ∀ v x, ∃ J : Cell v, x ∈ cell J
  sectionMap : {v : Grade} → Cell v → I → I
  decoder : {v : Grade} → Cell v → I → I
  decoder_cont : ∀ {v} (J : Cell v), ContinuousOn (decoder J) (cell J)
  section_mem : ∀ {v} (J : Cell v) x, sectionMap J x ∈ cell J
  decode_section : ∀ {v} (J : Cell v) x, decoder J (sectionMap J x) = x
  q : ℝ≥0
  q_lt : q < 1
  lip : ∀ {v} (J : Cell v), LipschitzWith q (sectionMap J)
  mixed_mark : ∀ {v} {J K : Cell v} {x}, x ∈ cell J → x ∈ cell K →
    color J ≠ color K → decoder J x = sectionMap (liftNext (color J) K) leftEndpoint
  same_mark : ∀ {v} {J K : Cell v} {x}, x ∈ cell J → x ∈ cell K →
    color J = color K → decoder J x = decoder K x
  same_lift : ∀ {v} {J K : Cell v} {x}, x ∈ cell J → x ∈ cell K →
    color J = color K → ∀ i, i ≠ color J → liftNext i J = liftNext i K

private theorem color_lift {v : Grade} (J : Cell v) (i : Bool) (h : color J ≠ i) :
    color (liftNext i J) = color J := by
  rcases J with ⟨q, a, b⟩
  cases i <;> cases q <;> simp_all [color, liftNext, fiveCell, sevenCell]

private abbrev Family := Grade →ᵇ (I →ᵇ I)

private noncomputable def pack (f : Grade → I →ᵇ I) : Family :=
  BoundedContinuousFunction.mkOfBound ⟨f, continuous_of_discreteTopology⟩ 1 fun v w =>
    BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr fun x => by
      change |(f v x : ℝ) - (f w x : ℝ)| ≤ 1
      rw [abs_le]
      constructor <;> linarith [(f v x).property.1, (f v x).property.2, (f w x).property.1, (f w x).property.2]

namespace Pieces

variable (S : Pieces)

/-- Paste the finitely many branches at a single grade, including the shared
points of two same-colour cells. -/
private theorem glue (v : Grade) (i : Bool) (opp : Cell v → I → I)
    (hc : ∀ J, ContinuousOn (opp J) (S.cell J))
    (hm : ∀ (J K : Cell v) x, color J = i → color K ≠ i → x ∈ S.cell J →
      x ∈ S.cell K → S.decoder J x = opp K x)
    (hs : ∀ (J K : Cell v) x, color J ≠ i → color K ≠ i → x ∈ S.cell J →
      x ∈ S.cell K → opp J x = opp K x) :
    ∃ f : I →ᵇ I,
      (∀ J : Cell v, color J = i → ∀ x ∈ S.cell J, f x = S.decoder J x) ∧
      (∀ J : Cell v, color J ≠ i → ∀ x ∈ S.cell J, f x = opp J x) := by
  classical
  let branch (J : Cell v) := if color J = i then S.decoder J else opp J
  have agree (J K : Cell v) {x : I} (hx : x ∈ S.cell J) (hy : x ∈ S.cell K) :
      branch J x = branch K x := by
    by_cases hj : color J = i <;> by_cases hk : color K = i
    · simpa [branch, hj, hk] using S.same_mark hx hy (hj.trans hk.symm)
    · simpa [branch, hj, hk] using hm J K x hj hk hx hy
    · simpa [branch, hj, hk] using (hm K J x hk hj hy hx).symm
    · simpa [branch, hj, hk] using hs J K x hj hk hx hy
  obtain ⟨f, heq⟩ := exists_glued_interval_map S.cell S.closed (locallyFinite_of_finite _)
    (S.cover v) branch (fun J => by
      dsimp only [branch]; split
      · exact S.decoder_cont J
      · exact hc J) (fun J K x => agree J K)
  refine ⟨f, ?_, ?_⟩
  · intro J hJ x hx; simpa [branch, hJ] using heq J x hx
  · intro J hJ x hx; simpa [branch, hJ] using heq J x hx

private theorem eq_color_of_ne {a b i : Bool} (ha : a ≠ i) (hb : b ≠ i) : a = b := by
  cases a <;> cases b <;> cases i <;> simp_all

/-- The direct and opposite-colour equations have continuous solutions at
all grades for either choice of decoder colour. -/
theorem exists_family (i : Bool) :
    ∃ D : Grade → I →ᵇ I,
      (∀ v (J : Cell v), color J = i → ∀ x ∈ S.cell J, D v x = S.decoder J x) ∧
      (∀ v (J : Cell v), color J ≠ i → ∀ x ∈ S.cell J, D v x =
        S.sectionMap (liftNext i J) (D (step (color J) v) (S.decoder J x))) := by
  classical
  let A : Set Family := {u | ∀ v (J : Cell v), color J = i → ∀ x ∈ S.cell J,
    u v x = S.decoder J x}
  have hA : IsClosed A := by
    dsimp only [A]
    simp only [setOf_forall]
    exact isClosed_iInter fun v => isClosed_iInter fun J => isClosed_iInter fun _ =>
      isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq
        ((continuous_eval_const x).comp (continuous_eval_const v)) continuous_const
  letI : CompleteSpace A := hA.isComplete.completeSpace_coe
  have seed (v : Grade) := S.glue v i (fun J _ => S.sectionMap (liftNext i J) leftEndpoint)
    (fun _ => continuousOn_const) (by
      intro J K x hj hk hx hy
      subst i
      exact S.mixed_mark hx hy (Ne.symm hk)) (by
      intro J K x hj hk hx hy
      dsimp only
      rw [S.same_lift hx hy (eq_color_of_ne hj hk) i (Ne.symm hj)])
  letI : Nonempty A := ⟨⟨pack (fun v => (seed v).choose), fun v => (seed v).choose_spec.1⟩⟩
  have update (u : A) (v : Grade) := S.glue v i
    (fun J x => S.sectionMap (liftNext i J) (u.val (step (color J) v) (S.decoder J x)))
    (fun J => (S.lip _).continuous.comp_continuousOn
      ((u.val _).continuous.comp_continuousOn (S.decoder_cont J))) (by
      intro J K x hj hk hx hy
      subst i
      have hc : color J ≠ color K := Ne.symm hk
      dsimp only
      rw [S.mixed_mark hx hy hc, S.mixed_mark hy hx hc.symm,
        u.property _ _ (color_lift J _ hc) _ (S.section_mem _ _),
        S.decode_section]) (by
      intro J K x hj hk hx hy
      have h := eq_color_of_ne hj hk
      dsimp only
      rw [S.same_lift hx hy h i (Ne.symm hj), S.same_mark hx hy h, h])
  let T (u : A) : A :=
    ⟨pack (fun v => (update u v).choose), fun v => (update u v).choose_spec.1⟩
  have hT (u : A) (v : Grade) := (update u v).choose_spec.2
  have hcontract : ContractingWith S.q T := by
    refine ⟨S.q_lt, LipschitzWith.of_dist_le_mul fun u w => ?_⟩
    change dist (T u).val (T w).val ≤ (S.q : ℝ) * dist u.val w.val
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro v
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro x
    obtain ⟨J, hx⟩ := S.cover v x
    by_cases h : color J = i
    · rw [(T u).property v J h x hx, (T w).property v J h x hx, dist_self]; positivity
    · change dist ((update u v).choose x) ((update w v).choose x) ≤ _
      rw [hT u v J h x hx, hT w v J h x hx]
      exact ((S.lip _).dist_le_mul _ _).trans <| mul_le_mul_of_nonneg_left
        ((BoundedContinuousFunction.dist_coe_le_dist _).trans
          (BoundedContinuousFunction.dist_coe_le_dist _)) S.q.2
  let u := hcontract.fixedPoint T
  have hu : T u = u := hcontract.fixedPoint_isFixedPt
  refine ⟨u.val, u.property, ?_⟩
  intro v J h x hx
  calc u.val v x = (T u).val v x := by rw [hu]
       _ = _ := hT u v J h x hx

end Pieces
end CommutingIntervalSimplified.GradedDecoders
