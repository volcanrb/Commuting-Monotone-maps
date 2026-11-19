import CommutingIntervalSimplified.GradedProjectionFamily
import CommutingIntervalSimplified.GradedPhysicalProjections

/-!
# Composition of the degree-five and degree-seven projections

On each grade the two-step projection is the bounded continuous composite.
Its admissibility follows from the mesh composition law. The shifted
recursive input is the corresponding composite one grade higher.
-/

namespace CommutingIntervalSimplified.GradedProjection

open Function Set GradedCells DecoderProjection
open scoped BoundedContinuousFunction

noncomputable section

/-- Compose the second projection at the grade reached by the first edge. -/
def shiftedComp (r s : Family) (shift : Grade → Grade) : Family :=
  pack fun v => (r v).compContinuous (s (shift v)).toContinuousMap

@[simp] theorem shiftedComp_apply (r s : Family) (shift : Grade → Grade) (v : Grade) (x : I) :
    shiftedComp r s shift v x = r v (s (shift v) x) := rfl

theorem extend_compContinuous (a b : IntervalFunction) :
    extend (a.compContinuous b.toContinuousMap) = extend a ∘ extend b := by
  funext t
  let x : I := projIcc 0 1 zero_le_one t
  change (a (b x) : ℝ) = a (projIcc 0 1 zero_le_one (b x : ℝ))
  rw [projIcc_of_mem _ (b x).property]

/-- Piece and vertex conditions for the composite on its joint degree. -/
theorem shiftedComp_admissible {m : Grade → ℤ} {d e : ℤ} {r s : Family}
    {shift : Grade → Grade} (hshift : ∀ v, m (shift v) = m v * d)
    (hr : ∀ v, GridAdmissible (m v) d (extend (r v)))
    (hs : ∀ v, GridAdmissible (m v) e (extend (s v))) (v : Grade) :
    GridAdmissible (m v) (d*e) (extend (shiftedComp r s shift v)) := by
  change GridAdmissible _ _ (extend ((r v).compContinuous (s (shift v)).toContinuousMap))
  rw [extend_compContinuous]
  exact (hr v).comp (hshift v ▸ hs (shift v))

/-- Reducing both CRT coordinates twice agrees with reducing directly
from the fine to the coarse grade. -/
theorem project_project {a b c : Grade} (hab₁ : a.1 ≤ b.1) (hab₂ : a.2 ≤ b.2)
    (hbc₁ : b.1 ≤ c.1) (hbc₂ : b.2 ≤ c.2) (J : Cell c) :
    project hab₁ hab₂ (project hbc₁ hbc₂ J) =
      project (hab₁.trans hbc₁) (hab₂.trans hbc₂) J := by
  apply Cell.ext
  · rfl
  · exact DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow 5 hab₁)
      (pow_dvd_pow 5 hbc₁)) J.five
  · exact DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow 7 hab₂)
      (pow_dvd_pow 7 hbc₂)) J.seven

end
end CommutingIntervalSimplified.GradedProjection

namespace CommutingIntervalSimplified.ConcreteProjection

open Function Set GradedCells GradedGeometry GradedMarkedCells GradedProjection DecoderProjection
open scoped BoundedContinuousFunction

noncomputable section

/-- The full-cell equation written in the affine coordinates of its source
and projected target. -/
def IsChartSolution (w : Grade) (r : Family) : Prop :=
  (∀ v, GridAdmissible (density v) (degree w) (extend (r v))) ∧
    ∀ v (J : Cell (up w v)) (t : I), ∃ u : I,
      r v (chart J t) = chart (down w v J) u ∧
      (u : ℝ) = (chartMatch w v J).map (extend (r (step (color J) v))) t

/-- Uniform contraction gives at most one family satisfying the normalized
chart recursion, including for the combined degree. -/
theorem IsChartSolution.unique {w : Grade} {r s : Family}
    (hr : IsChartSolution w r) (hs : IsChartSolution w s) : r = s := by
  have h : dist r s ≤ dist r s/3 := by
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro v
    apply BoundedContinuousFunction.dist_le_iff_of_nonempty.mpr
    intro x
    obtain ⟨J, t, rfl⟩ := cover (up w v) x
    obtain ⟨a, ha, hae⟩ := hr.2 v J t
    obtain ⟨b, hb, hbe⟩ := hs.2 v J t
    rw [ha, hb]
    refine ((chart_lip_one _).dist_le_mul a b).trans ?_
    simp only [NNReal.coe_one, one_mul]
    change |(a:ℝ)-b| ≤ dist r s/3
    rw [hae, hbe]
    apply ChartMatch.map_dist_le _ (hr.1 _) (hs.1 _)
    intro z _
    exact (BoundedContinuousFunction.dist_coe_le_dist (f := r (step (color J) v))
      (g := s (step (color J) v)) (projIcc 0 1 zero_le_one z)).trans
      (BoundedContinuousFunction.dist_coe_le_dist (step (color J) v))
  exact dist_le_zero.mp (by linarith)

private theorem step_up (i : Bool) (w v : Grade) : step i (up w v) = up w (step i v) := by
  cases i <;> simp [step, up, Nat.add_right_comm]

private theorem compose_normalized {m n o d e D : ℤ} {β γ η β' η' : Bool → ℝ}
    (S : ChartMatch m d γ η) (T : ChartMatch n e β γ) (R : ChartMatch o D β' η')
    (hn : n=m*d) (ho : o=m) (hD : D=d*e) (hβ : β'=β) (hη : η'=η)
    (hm : 0 < m) (hd : 0 < d) (he : 0 < e) (hdo : Odd d) (heo : Odd e)
    {r s : ℝ → ℝ} (hr : GridAdmissible m d r) (hs : GridAdmissible n e s)
    (t : I) : S.map r (T.map s t) = R.map (r ∘ s) t := by
  subst n o D β' η'
  have hR : R = S.comp T := Subsingleton.elim _ _
  rw [hR]
  exact (S.map_comp T hr hs hm hd he hdo heo t.property).symm

private theorem composite_chart_at {w e z v : Grade} {r s : Family}
    (hr : IsChartSolution w r) (hs : IsChartSolution e s)
    (hdeg : degree z=degree w*degree e) (hwo : Odd (degree w)) (heo : Odd (degree e))
    (J : Cell (up e (up w v))) (K : Cell (up z v))
    (hc : color K = color J) (hm : beta K = beta J)
    (hp : down z v K = down w v (down e (up w v) J))
    (hchart : chart K = chart J) (t : I) :
    ∃ u : I, shiftedComp r s (up w) v (chart K t) = chart (down z v K) u ∧
      (u : ℝ) = (chartMatch z v K).map
        (extend (shiftedComp r s (up w) (step (color K) v))) t := by
  let H := down e (up w v) J
  obtain ⟨u, hu, hmu⟩ := hs.2 (up w v) J t
  obtain ⟨y, hy, hmy⟩ := hr.2 v H u
  refine ⟨y, ?_, ?_⟩
  · simpa only [shiftedComp_apply, hp, hchart, hu] using hy
  · rw [hmy, hmu]
    let k := step (color J) v
    have hshift := step_up (color J) w v
    have hn : density (step (color J) (up w v)) = density k * degree w := by
      rw [hshift, density_up]
    have hkc : step (color K) v = k := by rw [hc]
    have ht := compose_normalized (chartMatch w v H) (chartMatch e (up w v) J)
      (chartMatch z v K) hn (congrArg density hkc) hdeg hm (congrArg beta hp)
      (density_pos _) (degree_pos _) (degree_pos _) hwo heo
      (hr.1 k) (hs.1 (step (color J) (up w v))) t
    apply ht.trans
    apply congrArg (fun r₀ => (chartMatch z v K).map r₀ t)
    change _ = GradedProjection.extend ((r (step (color K) v)).compContinuous
      (s (up w (step (color K) v))).toContinuousMap)
    rw [extend_compContinuous, hkc, hshift]

/-- Composing the two elementary solutions in either order gives a joint
degree-35 chart solution. The two recursive input grades agree because
the horizontal and vertical grade increments commute. -/
theorem elementaryComposite {w e : Grade} {r s : Family}
    (hr : IsChartSolution w r) (hs : IsChartSolution e s)
    (hgrades : (w=(1,0) ∧ e=(0,1)) ∨ (w=(0,1) ∧ e=(1,0))) :
    IsChartSolution (1,1) (shiftedComp r s (up w)) := by
  rcases hgrades with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals
    constructor
    · exact shiftedComp_admissible (density_up _) hr.1 hs.1
    · intro v J t
      apply composite_chart_at hr hs (by decide) (by decide) (by decide) J J rfl rfl _ rfl t
      exact (project_project _ _ _ _ J).symm

/-- The elementary projections commute around every grade square. -/
theorem square_of_chartSolutions {r s : Family} (hr : IsChartSolution (1,0) r)
    (hs : IsChartSolution (0,1) s) (v : Grade) (x : I) :
    r v (s (step false v) x) = s v (r (step true v) x) := by
  have he := (elementaryComposite hr hs (Or.inl ⟨rfl, rfl⟩)).unique
    (elementaryComposite hs hr (Or.inr ⟨rfl,rfl⟩))
  exact congrArg (fun F : Family => F v x) he

/-- The constructed projection at each degree satisfies its chart equations. -/
theorem projection_isChartSolution (w : Grade) : IsChartSolution w (projection w) :=
  ⟨projection_admissible w, projection_chart w⟩

/-- The elementary composite is the unique degree-35 projection. -/
theorem projection_diagonal (v : Grade) (x : I) :
    projection (1,0) v (projection (0,1) (step false v) x) = projection (1,1) v x := by
  have h := (elementaryComposite (projection_isChartSolution (1,0))
    (projection_isChartSolution (0,1)) (Or.inl ⟨rfl,rfl⟩)).unique (projection_isChartSolution (1,1))
  exact congrArg (fun F : Family => F v x) h

/-- The physical projections commute around every elementary grade square. -/
theorem projection_square (v : Grade) (x : I) :
    projection (1,0) v (projection (0,1) (step false v) x) =
      projection (0,1) v (projection (1,0) (step true v) x) :=
  square_of_chartSolutions (projection_isChartSolution _) (projection_isChartSolution _) v x

end
end CommutingIntervalSimplified.ConcreteProjection
