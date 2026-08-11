import CommutingIntervalSimplified.BrouwerStandardSimplex

/-!
# Compact-convex fixed points from the standard simplex theorem

This file reduces the compact-convex fixed-point theorem needed by the branch
length argument to `BrouwerSupport.Brouwer`, the vendored standard-simplex
theorem.  The reduction is the classical finite-net/partition-of-unity proof:
tent weights give simplex coordinates, the corresponding convex combination
gives a finite-dimensional approximation, and compactness upgrades arbitrarily
good approximate fixed points to an exact one.
-/

open Set

namespace CommutingIntervalSimplified.BrouwerSupport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty finite strict `ε`-net in `K`, indexed by a positive natural
number so that the vendored standard-simplex theorem applies directly. -/
structure CompactFiniteNet (K : Set E) (ε : ℝ) where
  n : ℕ+
  center : Fin n → E
  center_mem : ∀ i, center i ∈ K
  cover : ∀ x ∈ K, ∃ i, dist x (center i) < ε

/-- Compact nonempty sets admit finite strict nets whose centers remain in the
set.  This is the only compactness input in the approximation construction. -/
theorem compactFiniteNet_exists {K : Set E}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (CompactFiniteNet K ε) := by
  classical
  obtain ⟨t, htK, htfinite, hcover⟩ :=
    finite_cover_balls_of_compact hKcompact hε
  have htne : t.Nonempty := by
    obtain ⟨x, hxK⟩ := hKnonempty
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hxK)
    obtain ⟨hcK, _hxc⟩ := Set.mem_iUnion.mp hc
    exact ⟨c, hcK⟩
  letI : Fintype t := htfinite.fintype
  have hcard : 0 < Fintype.card t :=
    Fintype.card_pos_iff.mpr ⟨⟨htne.choose, htne.choose_spec⟩⟩
  let n : ℕ+ := ⟨Fintype.card t, hcard⟩
  let e : Fin n ≃ t := (Fintype.equivFin t).symm
  refine ⟨{
    n := n
    center := fun i => (e i).1
    center_mem := fun i => htK (e i).2
    cover := ?_
  }⟩
  intro x hxK
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp (hcover hxK)
  obtain ⟨hct, hxc⟩ := Set.mem_iUnion.mp hc
  let c' : t := ⟨c, hct⟩
  refine ⟨e.symm c', ?_⟩
  have he : e (e.symm c') = c' := e.apply_symm_apply c'
  simpa [Metric.mem_ball, he] using hxc

/-- The tent weight of the center `c` at `x`. -/
noncomputable def tentWeight (ε : ℝ) (c x : E) : ℝ :=
  max 0 (ε - dist x c)

theorem tentWeight_nonneg (ε : ℝ) (c x : E) :
    0 ≤ tentWeight ε c x := by
  simp [tentWeight]

theorem tentWeight_pos_iff {ε : ℝ} {c x : E} :
    0 < tentWeight ε c x ↔ dist x c < ε := by
  simp [tentWeight]

theorem tentWeight_continuous (ε : ℝ) (c : E) :
    Continuous (tentWeight ε c) := by
  unfold tentWeight
  fun_prop

/-- Sum of all tent weights in a finite net. -/
noncomputable def tentWeightSum {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (x : E) : ℝ :=
  ∑ i, tentWeight ε (net.center i) x

theorem tentWeightSum_pos {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (x : K) :
    0 < tentWeightSum net x := by
  obtain ⟨i, hi⟩ := net.cover x x.property
  apply Finset.sum_pos'
  · intro j _
    exact tentWeight_nonneg ε (net.center j) x
  · exact ⟨i, Finset.mem_univ i, tentWeight_pos_iff.mpr hi⟩

/-- The normalized tent-weight coordinate attached to a finite net. -/
noncomputable def tentCoordinateData {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (x : K) (i : Fin net.n) : ℝ :=
  tentWeight ε (net.center i) x / tentWeightSum net x

theorem tentCoordinateData_mem_stdSimplex {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (x : K) :
    tentCoordinateData net x ∈ stdSimplex ℝ (Fin net.n) := by
  rw [stdSimplex]
  constructor
  · intro i
    exact div_nonneg (tentWeight_nonneg ε (net.center i) x)
      (tentWeightSum_pos net x).le
  · simp only [tentCoordinateData, ← Finset.sum_div]
    exact div_self (ne_of_gt (tentWeightSum_pos net x))

/-- Continuous partition-of-unity coordinates subordinate to the finite net. -/
noncomputable def netCoordinates {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (x : K) :
    stdSimplex ℝ (Fin net.n) :=
  ⟨tentCoordinateData net x, tentCoordinateData_mem_stdSimplex net x⟩

theorem netCoordinates_continuous {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) :
    Continuous (netCoordinates net) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hnum : Continuous (fun x : K => tentWeight ε (net.center i) x) :=
    (tentWeight_continuous ε (net.center i)).comp continuous_subtype_val
  have hden : Continuous (fun x : K => tentWeightSum net x) := by
    unfold tentWeightSum
    apply continuous_finsetSum
    intro j _
    exact (tentWeight_continuous ε (net.center j)).comp continuous_subtype_val
  exact hnum.div hden (fun x => ne_of_gt (tentWeightSum_pos net x))

/-- Convex combination of the net centers with standard-simplex weights. -/
noncomputable def simplexCombination {n : ℕ+}
    (center : Fin n → E) (p : stdSimplex ℝ (Fin n)) : E :=
  ∑ i, p.1 i • center i

theorem simplexCombination_continuous {n : ℕ+} (center : Fin n → E) :
    Continuous (simplexCombination center) := by
  unfold simplexCombination
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

theorem simplexCombination_mem {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (hKconvex : Convex ℝ K)
    (p : stdSimplex ℝ (Fin net.n)) :
    simplexCombination net.center p ∈ K := by
  apply hKconvex.sum_mem
  · intro i _
    exact p.2.1 i
  · exact p.2.2
  · intro i _
    exact net.center_mem i

/-- The convex-combination map, with its codomain restricted to `K`. -/
noncomputable def netCombination {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (hKconvex : Convex ℝ K)
    (p : stdSimplex ℝ (Fin net.n)) : K :=
  ⟨simplexCombination net.center p, simplexCombination_mem net hKconvex p⟩

theorem netCombination_continuous {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (hKconvex : Convex ℝ K) :
    Continuous (netCombination net hKconvex) := by
  exact (simplexCombination_continuous net.center).subtype_mk
    (simplexCombination_mem net hKconvex)

/-- The simplex self-map obtained by combining centers, applying `f), and
returning to normalized tent coordinates. -/
noncomputable def finiteNetSimplexMap {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (hKconvex : Convex ℝ K)
    (f : E → E) (hf_maps : MapsTo f K K)
    (p : stdSimplex ℝ (Fin net.n)) :
    stdSimplex ℝ (Fin net.n) :=
  netCoordinates net
    ⟨f (netCombination net hKconvex p), hf_maps (netCombination net hKconvex p).property⟩

theorem finiteNetSimplexMap_continuous {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (hKconvex : Convex ℝ K)
    (f : E → E) (hf : ContinuousOn f K) (hf_maps : MapsTo f K K) :
    Continuous (finiteNetSimplexMap net hKconvex f hf_maps) := by
  have hfK : Continuous (fun x : K => (⟨f x, hf_maps x.property⟩ : K)) :=
    hf.restrict.subtype_mk (fun x => hf_maps x.property)
  exact (netCoordinates_continuous net).comp
    (hfK.comp (netCombination_continuous net hKconvex))

/-- Brouwer supplies an exact fixed point of the finite-dimensional
approximation map. -/
theorem finiteNetSimplexMap_exists_fixedPoint {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (hKconvex : Convex ℝ K)
    (f : E → E) (hf : ContinuousOn f K) (hf_maps : MapsTo f K K) :
    ∃ p, finiteNetSimplexMap net hKconvex f hf_maps p = p := by
  exact Brouwer _ (finiteNetSimplexMap_continuous net hKconvex f hf hf_maps)

/-- A convex combination of points all lying within `ε` whenever their
weight is positive lies within `ε` of the reference point. -/
theorem dist_simplexCombination_le {n : ℕ+}
    (center : Fin n → E) (p : stdSimplex ℝ (Fin n))
    (y : E) (ε : ℝ)
    (hnear : ∀ i, 0 < p.1 i → dist y (center i) ≤ ε) :
    dist (simplexCombination center p) y ≤ ε := by
  have hdiff :
      simplexCombination center p - y =
        ∑ i, p.1 i • (center i - y) := by
    calc
      simplexCombination center p - y =
          (∑ i, p.1 i • center i) - (∑ i, p.1 i) • y := by
            rw [p.2.2, one_smul]
            rfl
      _ = ∑ i, (p.1 i • center i - p.1 i • y) := by
            rw [Finset.sum_smul, Finset.sum_sub_distrib]
      _ = ∑ i, p.1 i • (center i - y) := by
            simp only [smul_sub]
  rw [dist_eq_norm, hdiff]
  calc
    ‖∑ i, p.1 i • (center i - y)‖ ≤
        ∑ i, ‖p.1 i • (center i - y)‖ :=
      norm_sum_le Finset.univ _
    _ = ∑ i, p.1 i * dist y (center i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (p.2.1 i),
        dist_comm, dist_eq_norm]
    _ ≤ ∑ i, p.1 i * ε := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : p.1 i = 0
      · simp [hi]
      · exact mul_le_mul_of_nonneg_left
          (hnear i (lt_of_le_of_ne (p.2.1 i) (Ne.symm hi))) (p.2.1 i)
    _ = ε := by
      rw [← Finset.sum_mul, p.2.2, one_mul]

/-- At a simplex fixed point, the associated convex combination is within the
net radius of its image under `f`. -/
theorem finiteNet_fixedPoint_dist_le {K : Set E} {ε : ℝ}
    (net : CompactFiniteNet K ε) (hε : 0 < ε)
    (hKconvex : Convex ℝ K) (f : E → E) (hf_maps : MapsTo f K K)
    (p : stdSimplex ℝ (Fin net.n))
    (hp : finiteNetSimplexMap net hKconvex f hf_maps p = p) :
    dist (f (netCombination net hKconvex p))
      (netCombination net hKconvex p) ≤ ε := by
  change dist (f (simplexCombination net.center p))
      (simplexCombination net.center p) ≤ ε
  rw [dist_comm]
  apply dist_simplexCombination_le net.center p _ ε
  intro i hi
  let yK : K :=
    ⟨f (simplexCombination net.center p),
      hf_maps (simplexCombination_mem net hKconvex p)⟩
  have hcoord :
      tentCoordinateData net yK i = p.1 i := by
    have h := congrArg
      (fun q : stdSimplex ℝ (Fin net.n) => q.1 i) hp
    simpa [finiteNetSimplexMap, netCombination, yK, netCoordinates] using h
  have hcoordpos : 0 < tentCoordinateData net yK i := by
    rw [hcoord]
    exact hi
  have hweightpos : 0 < tentWeight ε (net.center i) yK := by
    apply (div_pos_iff_of_pos_right (tentWeightSum_pos net yK)).mp
    exact hcoordpos
  exact (tentWeight_pos_iff.mp hweightpos).le

/-- Every positive tolerance admits an approximate fixed point in `K`. -/
theorem compactConvex_approximateFixedPoint {K : Set E}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K) (f : E → E)
    (hf : ContinuousOn f K) (hf_maps : MapsTo f K K) :
    ∀ ε : ℝ, 0 < ε → ∃ x ∈ K, dist (f x) x < ε := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  obtain ⟨net⟩ := compactFiniteNet_exists hKcompact hKnonempty hδ
  obtain ⟨p, hp⟩ :=
    finiteNetSimplexMap_exists_fixedPoint net hKconvex f hf hf_maps
  let x : K := netCombination net hKconvex p
  refine ⟨x, x.property, ?_⟩
  have hdist :=
    finiteNet_fixedPoint_dist_le net hδ hKconvex f hf_maps p hp
  change dist (f (netCombination net hKconvex p))
      (netCombination net hKconvex p) < ε
  exact lt_of_le_of_lt hdist (by
    dsimp [δ]
    linarith)

/-- On a compact set, arbitrarily good approximate fixed points yield an exact
fixed point by minimizing `x ↦ dist (f x) x`. -/
theorem fixedPoint_of_approximate {K : Set E}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x ∈ K, dist (f x) x < ε) :
    ∃ x ∈ K, f x = x := by
  have hdist : ContinuousOn (fun x => dist (f x) x) K := by
    rw [continuousOn_iff_continuous_restrict]
    exact hf.restrict.dist continuous_subtype_val
  obtain ⟨p, hpK, hpmin⟩ :=
    hKcompact.exists_isMinOn hKnonempty hdist
  have hpzero : dist (f p) p = 0 := by
    by_contra hne
    have hpos : 0 < dist (f p) p :=
      lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    obtain ⟨x, hxK, hx⟩ := happrox _ hpos
    exact (not_lt_of_ge (hpmin hxK)) hx
  exact ⟨p, hpK, dist_eq_zero.mp hpzero⟩

/-- Compact-convex fixed-point theorem, derived without axioms from the
vendored standard-simplex Brouwer theorem. -/
theorem compactConvex_exists_fixedPoint {K : Set E}
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty) (f : E → E)
    (hf : ContinuousOn f K) (hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  exact fixedPoint_of_approximate hKcompact hKnonempty f hf
    (compactConvex_approximateFixedPoint hKcompact hKnonempty hKconvex f hf hf_maps)

/-- An explicit-set form of `compactConvex_exists_fixedPoint`.  Keeping the
set and map as ordinary arguments avoids expensive dependent inference when
the set itself contains proof parameters. -/
theorem compactConvex_exists_fixedPoint_explicit
    (K : Set E) (f : E → E)
    (hKcompact : IsCompact K) (hKconvex : Convex ℝ K)
    (hKnonempty : K.Nonempty) (hf : ContinuousOn f K)
    (hf_maps : MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  exact compactConvex_exists_fixedPoint hKcompact hKconvex hKnonempty f hf hf_maps

end CommutingIntervalSimplified.BrouwerSupport
