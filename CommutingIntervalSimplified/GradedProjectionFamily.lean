import CommutingIntervalSimplified.Base
import CommutingIntervalSimplified.GradedCells
import CommutingIntervalSimplified.DecoderProjection
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Contracting

/-! # Simultaneous construction of admissible projections

The unknown is a family indexed by all grades. One local rule reads one
higher-grade map on each core or shoulder. Agreement at adjacent pieces
gives continuity. The same Lipschitz bound on every branch gives a single
contraction in the uniform metric, even though the number of pieces varies
with the grade. -/

namespace CommutingIntervalSimplified.GradedProjection

open Function Set GradedCells DecoderProjection
open scoped NNReal BoundedContinuousFunction

noncomputable section

abbrev IntervalFunction := I →ᵇ I
abbrev Family := Grade →ᵇ IntervalFunction

/-- Give a bounded interval map a real representative by extending it constantly
past both endpoints. -/
def extend (f : IntervalFunction) (t : ℝ) : ℝ := f (projIcc 0 1 zero_le_one t)

private theorem extend_at (f : IntervalFunction) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    extend f x = (f ⟨x,hx⟩ : ℝ) := by rw [extend, projIcc_of_mem _ hx]

private theorem compact_mesh {m : ℤ} (hm : 0 < m) (i : ℤ) : IsCompact (mesh m i) := by
  have hp : (0:ℝ) < m := by exact_mod_cast hm
  have h : mesh m i = Icc ((i:ℝ)/m) ((i+1)/m) := by
    ext t
    simp only [mesh, mem_setOf_eq, mem_Icc, div_le_iff₀ hp, le_div_iff₀ hp, mul_comm t]
  rw [h]
  exact isCompact_Icc

/-- Admissibility is closed in the uniform topology: it prescribes values on
vertices and membership in compact folded pieces at every other point. -/
theorem closed_admissible (m d : ℤ) (hm : 0 < m) :
    IsClosed {f : IntervalFunction | GridAdmissible m d (extend f)} := by
  let V : Set IntervalFunction := {f | ∀ t (i : ℤ), (m:ℝ)*(d*t) = i →
    extend f (fold t) = fold (d*t)}
  let P : Set IntervalFunction := {f | ∀ t (i : ℤ), (d:ℝ)*t ∈ mesh m i →
    extend f (fold t) ∈ fold '' mesh m i}
  have ev (t : ℝ) : Continuous (fun f : IntervalFunction => extend f t) :=
    continuous_subtype_val.comp (continuous_eval_const _)
  have hV : IsClosed V := by
    simp only [V, setOf_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (ev _) continuous_const
  have hP : IsClosed P := by
    simp only [P, setOf_forall]
    exact isClosed_iInter fun t => isClosed_iInter fun i => isClosed_iInter fun _ =>
      ((compact_mesh hm i).image continuous_fold).isClosed.preimage (ev _)
  have he : {f : IntervalFunction | GridAdmissible m d (extend f)} = V ∩ P := by
    ext f
    constructor
    · intro h
      exact ⟨h.vertex, h.piece⟩
    · rintro ⟨hv,hp⟩
      exact ⟨(continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)).continuousOn,
        fun x _ => (f _).property, hv, hp⟩
  exact he ▸ hV.inter hP

def pack (f : Grade → IntervalFunction) : Family :=
  BoundedContinuousFunction.mkOfBound ⟨f, continuous_of_discreteTopology⟩ 1 fun v w =>
    BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr fun x => by
      change |(f v x : ℝ) - (f w x : ℝ)| ≤ 1
      rw [abs_le]
      constructor <;> linarith [(f v x).property.1, (f v x).property.2,
        (f w x).property.1, (f w x).property.2]

def standardMap (d : ℤ) : IntervalFunction :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ⟨fold (d * (x:ℝ)), fold_mem _⟩,
      Continuous.subtype_mk (continuous_fold.comp (continuous_const.mul continuous_subtype_val)) _⟩

theorem standardMap_admissible (m d : ℤ) : GridAdmissible m d (extend (standardMap d)) := by
  have h := GridAdmissible.standard m d
  refine ⟨(continuous_subtype_val.comp ((standardMap d).continuous.comp continuous_projIcc)).continuousOn,
    fun x _ => ((standardMap d) _).property, ?_, ?_⟩
  · intro t i hi
    rw [extend_at _ _ (fold_mem t)]
    exact h.vertex t i hi
  · intro t i hi
    rw [extend_at _ _ (fold_mem t)]
    exact h.piece t i hi

/-- A local projection rule updates a finite closed cover at each grade.
Its input may vary freely among the admissible maps at the indicated higher
grade. The last two fields control agreement and movement inside grid pieces. -/
structure LocalRule (m : Grade → ℤ) (d : ℤ) where
  Piece : Grade → Type
  finite : ∀ v, Finite (Piece v)
  region : (v : Grade) → Piece v → Set I
  closed_region : ∀ v j, IsClosed (region v j)
  covers : ∀ v x, ∃ j, x ∈ region v j
  sourceGrade : (v : Grade) → Piece v → Grade
  lift : (v : Grade) → (j : Piece v) → IntervalFunction → I → I
  continuousOn : ∀ v j r, GridAdmissible (m (sourceGrade v j)) d (extend r) →
    ContinuousOn (lift v j r) (region v j)
  agrees : ∀ v j k r s, j ≠ k →
    GridAdmissible (m (sourceGrade v j)) d (extend r) →
    GridAdmissible (m (sourceGrade v k)) d (extend s) →
    ∀ x ∈ region v j, x ∈ region v k → lift v j r x = lift v k s x
  q : ℝ≥0
  q_lt : q < 1
  lip : ∀ v j r s,
    GridAdmissible (m (sourceGrade v j)) d (extend r) →
    GridAdmissible (m (sourceGrade v j)) d (extend s) →
    ∀ x ∈ region v j, dist (lift v j r x) (lift v j s x) ≤ q * dist r s
  vertex : ∀ v j r, GridAdmissible (m (sourceGrade v j)) d (extend r) →
    ∀ (t : ℝ) (i : ℤ), (m v : ℝ)*(d*t) = i → ∀ x : I, (x : ℝ) = fold t →
    x ∈ region v j → (lift v j r x : ℝ) = fold (d*t)
  piece : ∀ v j r, GridAdmissible (m (sourceGrade v j)) d (extend r) →
    ∀ (t : ℝ) (i : ℤ), (d : ℝ)*t ∈ mesh (m v) i → ∀ x : I, (x : ℝ) = fold t →
    x ∈ region v j → (lift v j r x : ℝ) ∈ fold '' mesh (m v) i

namespace LocalRule

variable {m : Grade → ℤ} {d : ℤ} (S : LocalRule m d)

def IsSolution (r : Family) : Prop :=
  (∀ v, GridAdmissible (m v) d (extend (r v))) ∧
  ∀ v j x, x ∈ S.region v j → r v x = S.lift v j (r (S.sourceGrade v j)) x

/-- Existence and uniqueness for the core-and-shoulder update. -/
theorem existsUnique_solution (hm : ∀ v, 0 < m v) : ∃! r : Family, S.IsSolution r := by
  classical
  let A : Set Family := {r | ∀ v, GridAdmissible (m v) d (extend (r v))}
  have closedA : IsClosed A := by
    simp only [A, setOf_forall]
    exact isClosed_iInter fun v => (closed_admissible (m v) d (hm v)).preimage (continuous_eval_const v)
  letI : CompleteSpace A := closedA.isComplete.completeSpace_coe
  letI : Nonempty A := ⟨⟨pack (fun _ => standardMap d), fun v => standardMap_admissible _ _⟩⟩
  let idx v x := (S.covers v x).choose
  have mem v x : x ∈ S.region v (idx v x) := (S.covers v x).choose_spec
  let f (r : A) v x := S.lift v (idx v x) (r.val (S.sourceGrade v (idx v x))) x
  have local_eq (r : A) v j x (hx : x ∈ S.region v j) :
      f r v x = S.lift v j (r.val (S.sourceGrade v j)) x := by
    dsimp only [f]
    by_cases h : idx v x = j
    · rw [h]
    · exact S.agrees _ _ _ _ _ h (r.property _) (r.property _) x (mem _ _) hx
  have cont (r : A) v : Continuous (f r v) := by
    letI := S.finite v
    refine (locallyFinite_of_finite (S.region v)).continuous
      (iUnion_eq_univ_iff.mpr (S.covers v)) (S.closed_region v) fun j => ?_
    exact (S.continuousOn v j _ (r.property _)).congr (local_eq r v j)
  let T₀ (r : A) := pack fun v => BoundedContinuousFunction.mkOfCompact ⟨f r v, cont r v⟩
  have admiss (r : A) : T₀ r ∈ A := by
    intro v
    refine ⟨(continuous_subtype_val.comp (((T₀ r) v).continuous.comp continuous_projIcc)).continuousOn,
      fun x _ => (((T₀ r) v) _).property, ?_, ?_⟩
    · intro t i hi
      rw [extend_at _ _ (fold_mem t)]
      exact S.vertex _ _ _ (r.property _) _ _ hi _ rfl (mem _ _)
    · intro t i hi
      rw [extend_at _ _ (fold_mem t)]
      exact S.piece _ _ _ (r.property _) _ _ hi _ rfl (mem _ _)
  let T (r : A) : A := ⟨T₀ r, admiss r⟩
  have hT : ContractingWith S.q T := by
    refine ⟨S.q_lt, LipschitzWith.of_dist_le_mul fun r s => ?_⟩
    change dist (T₀ r) (T₀ s) ≤ (S.q : ℝ) * dist r.val s.val
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro v
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro x
    exact (S.lip _ _ _ _ (r.property _) (s.property _) _ (mem v x)).trans
      (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.dist_coe_le_dist _) S.q.2)
  let sol := hT.fixedPoint T
  have hsol : T sol = sol := hT.fixedPoint_isFixedPt
  refine ⟨sol.val, ⟨sol.property, ?_⟩, ?_⟩
  · intro v j x hx
    calc sol.val v x = (T sol).val v x := by rw [hsol]
         _ = _ := local_eq _ _ _ _ hx
  · rintro r ⟨hr, he⟩
    have fixed : T ⟨r, hr⟩ = ⟨r, hr⟩ := by
      apply Subtype.ext
      ext v x
      exact congrArg Subtype.val (he v (idx v x) x (mem v x)).symm
    exact congrArg Subtype.val (hT.fixedPoint_unique fixed)

end LocalRule
end
end CommutingIntervalSimplified.GradedProjection
