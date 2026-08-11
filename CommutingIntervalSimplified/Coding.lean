import CommutingIntervalSimplified.Defs
import CommutingIntervalSimplified.DurandPrimitiveComparison
import CommutingIntervalSimplified.Postcritical
import CommutingIntervalSimplified.SymbolicBase
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Coding a two-scale fold

This file freezes the complete C1--C8 interface used by the simplified
manuscript.  The construction starts from `TwoScaleFoldData`, builds one
common directed Markov coding for the two return maps, restricts to the
letters which occur in the ray word, applies the growing-substitution form
of Durand's Theorem 9, and converts symbolic ultimate periodicity back to
metric periodicity of the fold.

The statements here deliberately use literal directed-edge words: immediate
backtracking is retained.  No primitive-substitution, Perron-number, or
return-word infrastructure is part of this route.
-/

namespace CommutingIntervalSimplified

open Function Set
open scoped BigOperators

noncomputable section

/-! ## C1: one finite common Markov hull -/

/-- The finite joint postcritical hull, including the initial point of the
fold and carrying a simultaneous Markov partition for both return maps. -/
structure CommonMarkovHullData
    (A B : IntervalMap) {a b : ℝ} (F : TwoScaleFoldData A B a b) where
  vertices : Finset I
  left_mem : leftEndpoint ∈ vertices
  right_mem : rightEndpoint ∈ vertices
  base_mem : F.base ∈ vertices
  postcritical_subset : jointPostcriticalSet A B ⊆ (vertices : Set I)
  criticalA_subset : criticalDomain A ⊆ (vertices : Set I)
  criticalB_subset : criticalDomain B ⊆ (vertices : Set I)
  commonMarkov : IsCommonMarkovSet A B vertices

/-- Constant absolute slope and absence of an intrinsic vertex in the open
interval force one affine, strictly monotone branch on the whole closed
interval.  This is the geometric bridge from the intrinsic postcritical
hull to a literal Markov partition. -/
private theorem constantSlope_affine_strict_on_Icc_of_no_vertex
    {T : IntervalMap} {r : ℝ} (hr : 0 < r)
    (hT : HasConstantAbsoluteSlope T r) {x y : I} (hxy : x < y)
    (hnone : ∀ z ∈ vertexDomain T, ¬(x < z ∧ z < y)) :
    IsAffineOn T (Set.Icc x y) ∧
      IsStrictlyMonotoneOn T (Set.Icc x y) := by
  classical
  rcases hT.2 with ⟨p, hp⟩
  let q : RealPartition :=
    { points := p.points ∪ {(x : ℝ), (y : ℝ)}
      zero_mem := Finset.mem_union_left _ p.zero_mem
      one_mem := Finset.mem_union_left _ p.one_mem
      points_subset := by
        intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · exact p.points_subset hz
        · have hzxy : z = (x : ℝ) ∨ z = (y : ℝ) := by simpa using hz
          rcases hzxy with rfl | rfl
          · exact x.property
          · exact y.property }
  have hxq : (x : ℝ) ∈ q.points := by
    exact Finset.mem_union_right _ (by simp)
  have hyq : (y : ℝ) ∈ q.points := by
    exact Finset.mem_union_right _ (by simp)
  have hqformula {u v : ℝ} (huv : q.Adjacent u v) :
      ∃ m c : ℝ, |m| = r ∧ ∀ z ∈ intervalCell u v,
        (T z : ℝ) = m * (z : ℝ) + c := by
    have huI : u ∈ I := q.points_subset huv.1
    have hvI : v ∈ I := q.points_subset huv.2.1
    have hnonep : ∀ z ∈ p.points, ¬(u < z ∧ z < v) := by
      intro z hz hbetween
      exact huv.2.2.2 z (Finset.mem_union_left _ hz) hbetween
    obtain ⟨c, d, hcd, hsub⟩ :=
      p.exists_adjacent_superset huI hvI huv.2.2.1 hnonep
    obtain ⟨m, k, hm, hformula⟩ := hp hcd
    exact ⟨m, k, hm, fun z hz => hformula z (hsub hz)⟩
  have hxone : (x : ℝ) < 1 :=
    (show (x : ℝ) < (y : ℝ) from hxy).trans_le y.property.2
  have hxright : x < rightEndpoint := by
    change (x : ℝ) < 1
    exact hxone
  obtain ⟨a₀, b₀, hab₀, ha₀x, hxb₀⟩ :=
    q.exists_adjacent_Ico hxright
  have hxa₀ : (x : ℝ) ≤ a₀ := by
    by_contra hnot
    have ha₀ltx : a₀ < (x : ℝ) := lt_of_not_ge hnot
    exact hab₀.2.2.2 (x : ℝ) hxq ⟨ha₀ltx, hxb₀⟩
  have ha₀eq : a₀ = (x : ℝ) := le_antisymm ha₀x hxa₀
  have hb₀y : b₀ ≤ (y : ℝ) := by
    by_contra hnot
    have hyb₀ : (y : ℝ) < b₀ := lt_of_not_ge hnot
    exact hab₀.2.2.2 (y : ℝ) hyq
      ⟨by simpa [ha₀eq] using hxy, hyb₀⟩
  obtain ⟨m, c, hmabs, hformula₀⟩ := hqformula hab₀
  have hmne : m ≠ 0 := by
    intro hm0
    have : |m| = 0 := by rw [hm0, abs_zero]
    linarith
  let good : Finset ℝ := q.points.filter fun z =>
    (x : ℝ) ≤ z ∧ z ≤ (y : ℝ) ∧
      ∀ u : I, (x : ℝ) ≤ (u : ℝ) → (u : ℝ) ≤ z →
        (T u : ℝ) = m * (u : ℝ) + c
  have hb₀good : b₀ ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨hab₀.2.1, hxb₀.le, hb₀y, ?_⟩
    intro u hxu hub
    apply hformula₀
    exact ⟨by simpa [ha₀eq] using hxu, hub⟩
  obtain ⟨g, hg, hgmax⟩ := good.exists_max_image id ⟨b₀, hb₀good⟩
  have hgdata := Finset.mem_filter.mp hg
  have hgq : g ∈ q.points := hgdata.1
  have hxg : (x : ℝ) ≤ g := hgdata.2.1
  have hgy : g ≤ (y : ℝ) := hgdata.2.2.1
  have hglobalg := hgdata.2.2.2
  have hb₀g : b₀ ≤ g := by simpa using hgmax b₀ hb₀good
  have hxglt : (x : ℝ) < g := hxb₀.trans_le hb₀g
  have hg_eq_y : g = (y : ℝ) := by
    apply le_antisymm hgy
    by_contra hnot
    have hgylt : g < (y : ℝ) := lt_of_not_ge hnot
    have hgI : g ∈ I := q.points_subset hgq
    have hgltone : g < 1 := hgylt.trans_le y.property.2
    let gI : I := ⟨g, hgI⟩
    have hgIright : gI < rightEndpoint := by
      change g < 1
      exact hgltone
    obtain ⟨a₁, d, had, ha₁g, hgd⟩ :=
      q.exists_adjacent_Ico hgIright
    have hga₁ : g ≤ a₁ := by
      by_contra hga₁not
      have ha₁ltg : a₁ < g := lt_of_not_ge hga₁not
      exact had.2.2.2 g hgq ⟨ha₁ltg, hgd⟩
    have ha₁eq : a₁ = g := le_antisymm ha₁g hga₁
    have hdy : d ≤ (y : ℝ) := by
      by_contra hdynot
      have hyd : (y : ℝ) < d := lt_of_not_ge hdynot
      exact had.2.2.2 (y : ℝ) hyq
        ⟨by simpa [ha₁eq] using hgylt, hyd⟩
    obtain ⟨m₁, c₁, hm₁abs, hformula₁⟩ := hqformula had
    have hm₁ne : m₁ ≠ 0 := by
      intro hm₁0
      have : |m₁| = 0 := by rw [hm₁0, abs_zero]
      linarith
    let dI : I := ⟨d, q.points_subset had.2.1⟩
    have hxgI : x < gI := hxglt
    have hgdI : gI < dI := by simpa [gI, dI, ha₁eq] using hgd
    have hgyI : gI < y := hgylt
    have hleftMono (hmpos : 0 < m) :
        StrictMonoOn T (Set.Icc x gI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg u hu.1 (by simpa [gI] using hu.2),
        hglobalg v hv.1 (by simpa [gI] using hv.2)]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hleftAnti (hmneg : m < 0) :
        StrictAntiOn T (Set.Icc x gI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg u hu.1 (by simpa [gI] using hu.2),
        hglobalg v hv.1 (by simpa [gI] using hv.2)]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hrightMono (hm₁pos : 0 < m₁) :
        StrictMonoOn T (Set.Icc gI dI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ u ⟨by simpa [gI, ha₁eq] using hu.1,
            by simpa [dI] using hu.2⟩,
        hformula₁ v ⟨by simpa [gI, ha₁eq] using hv.1,
            by simpa [dI] using hv.2⟩]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hrightAnti (hm₁neg : m₁ < 0) :
        StrictAntiOn T (Set.Icc gI dI) := by
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ u ⟨by simpa [gI, ha₁eq] using hu.1,
            by simpa [dI] using hu.2⟩,
        hformula₁ v ⟨by simpa [gI, ha₁eq] using hv.1,
            by simpa [dI] using hv.2⟩]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    have hmEq : m₁ = m := by
      rcases lt_or_gt_of_ne hmne with hmneg | hmpos
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · rw [abs_of_neg hmneg] at hmabs
          rw [abs_of_neg hm₁neg] at hm₁abs
          linarith
        · exfalso
          have hturn : IsGenuineTurn T gI :=
            ⟨x, dI, hxgI, hgdI,
              Or.inr ⟨hleftAnti hmneg, hrightMono hm₁pos⟩⟩
          exact hnone gI (Or.inr hturn) ⟨hxgI, hgyI⟩
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · exfalso
          have hturn : IsGenuineTurn T gI :=
            ⟨x, dI, hxgI, hgdI,
              Or.inl ⟨hleftMono hmpos, hrightAnti hm₁neg⟩⟩
          exact hnone gI (Or.inr hturn) ⟨hxgI, hgyI⟩
        · rw [abs_of_pos hmpos] at hmabs
          rw [abs_of_pos hm₁pos] at hm₁abs
          linarith
    have hglobal_at_g : (T gI : ℝ) = m * g + c := by
      exact hglobalg gI hxg (by simp [gI])
    have hright_at_g : (T gI : ℝ) = m₁ * g + c₁ := by
      apply hformula₁
      constructor
      · simpa [gI, ha₁eq]
      · simpa [gI] using hgd.le
    have hcEq : c₁ = c := by
      rw [hmEq] at hright_at_g
      linarith
    have hdgood : d ∈ good := by
      apply Finset.mem_filter.mpr
      refine ⟨had.2.1, hxg.trans hgd.le, hdy, ?_⟩
      intro u hxu hud
      by_cases hug : (u : ℝ) ≤ g
      · exact hglobalg u hxu hug
      · have hgu : g ≤ (u : ℝ) := (lt_of_not_ge hug).le
        rw [hformula₁ u ⟨by simpa [ha₁eq] using hgu, hud⟩,
          hmEq, hcEq]
    have hdg : d ≤ g := by simpa using hgmax d hdgood
    exact (not_lt_of_ge hdg) hgd
  have hglobal : ∀ u ∈ Set.Icc x y,
      (T u : ℝ) = m * (u : ℝ) + c := by
    intro u hu
    exact hglobalg u hu.1 (by simpa [hg_eq_y] using hu.2)
  constructor
  · exact ⟨m, c, hglobal⟩
  · rcases lt_or_gt_of_ne hmne with hmneg | hmpos
    · right
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobal u hu, hglobal v hv]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith
    · left
      intro u hu v hv huv
      apply Subtype.coe_lt_coe.mp
      rw [hglobal u hu, hglobal v hv]
      have huv' : (u : ℝ) < (v : ℝ) := huv
      nlinarith

/-- The fold base is fixed by both return maps. -/
private theorem TwoScaleFoldData.base_fixed_generators
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b) :
    A F.base = F.base ∧ B F.base = F.base := by
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) F.initial_radius :=
    ⟨le_rfl, F.initial_radius_pos.le⟩
  have hray_zero : F.ray 0 = F.base := by
    apply Subtype.ext
    simpa using F.initial_unit_germ 0 hzero
  constructor
  · simpa [hray_zero] using (F.return_A 0 le_rfl).symm
  · simpa [hray_zero] using (F.return_B 0 le_rfl).symm

/-- Adjoining the fixed fold base to the finite common invariant intrinsic
vertex hull preserves finiteness and invariance. -/
private theorem twoScaleFold_finite_invariant_vertex_hull
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b) :
    ∃ K : Set I, K.Finite ∧ F.base ∈ K ∧
      criticalDomain A ∪ criticalDomain B ⊆ K ∧
      MapsTo A K K ∧ MapsTo B K K := by
  obtain ⟨K, hKfinite, hcrit, hAK, hBK⟩ :=
    finite_common_invariant_postcritical_hull
      F.finitePiece_A F.finitePiece_B F.onto_A F.onto_B
      F.constantSlope_A F.constantSlope_B F.one_lt_a F.one_lt_b
      F.commute F.scales_independent
  let K' : Set I := insert F.base K
  have hfixed := F.base_fixed_generators
  refine ⟨K', hKfinite.insert F.base, Set.mem_insert F.base K, ?_, ?_, ?_⟩
  · intro x hx
    exact Set.mem_insert_of_mem F.base (hcrit hx)
  · intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hxK
    · rw [hfixed.1]
      exact Set.mem_insert F.base K
    · exact Set.mem_insert_of_mem F.base (hAK hxK)
  · intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hxK
    · rw [hfixed.2]
      exact Set.mem_insert F.base K
    · exact Set.mem_insert_of_mem F.base (hBK hxK)

/-- A finite common invariant set containing both intrinsic vertex domains
becomes a common Markov finset for the two constant-slope maps. -/
private theorem commonMarkovHullData_of_finite_invariant_vertex_hull
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (K : Set I) (hKfinite : K.Finite) (hbase : F.base ∈ K)
    (hcrit : criticalDomain A ∪ criticalDomain B ⊆ K)
    (hAK : MapsTo A K K) (hBK : MapsTo B K K) :
    Nonempty (CommonMarkovHullData A B F) := by
  classical
  let vertices : Finset I := hKfinite.toFinset
  have hmem (z : I) : z ∈ vertices ↔ z ∈ K := by
    simp [vertices]
  have hleft : leftEndpoint ∈ vertices := by
    apply (hmem leftEndpoint).2
    apply hcrit
    left
    simp [criticalDomain, vertexDomain]
  have hright : rightEndpoint ∈ vertices := by
    apply (hmem rightEndpoint).2
    apply hcrit
    left
    simp [criticalDomain, vertexDomain]
  have hbase' : F.base ∈ vertices := (hmem F.base).2 hbase
  have hcriticalA : criticalDomain A ⊆ (vertices : Set I) := by
    intro z hz
    exact (hmem z).2 (hcrit (Or.inl hz))
  have hcriticalB : criticalDomain B ⊆ (vertices : Set I) := by
    intro z hz
    exact (hmem z).2 (hcrit (Or.inr hz))
  have hforwardA : ∀ z ∈ vertices, A z ∈ vertices := by
    intro z hz
    exact (hmem (A z)).2 (hAK ((hmem z).1 hz))
  have hforwardB : ∀ z ∈ vertices, B z ∈ vertices := by
    intro z hz
    exact (hmem (B z)).2 (hBK ((hmem z).1 hz))
  have hcells : ∀ ⦃x y : I⦄, FinsetAdjacent vertices x y →
      (IsAffineOn A (Set.Icc x y) ∧
        IsStrictlyMonotoneOn A (Set.Icc x y)) ∧
      (IsAffineOn B (Set.Icc x y) ∧
        IsStrictlyMonotoneOn B (Set.Icc x y)) := by
    intro x y hxy
    have hnoneA : ∀ z ∈ vertexDomain A, ¬(x < z ∧ z < y) := by
      intro z hz hbetween
      exact hxy.2.2.2 z (hcriticalA hz) hbetween
    have hnoneB : ∀ z ∈ vertexDomain B, ¬(x < z ∧ z < y) := by
      intro z hz hbetween
      exact hxy.2.2.2 z (hcriticalB hz) hbetween
    exact ⟨
      constantSlope_affine_strict_on_Icc_of_no_vertex
        (zero_lt_one.trans F.one_lt_a) F.constantSlope_A hxy.2.2.1 hnoneA,
      constantSlope_affine_strict_on_Icc_of_no_vertex
        (zero_lt_one.trans F.one_lt_b) F.constantSlope_B hxy.2.2.1 hnoneB⟩
  refine ⟨{
    vertices := vertices
    left_mem := hleft
    right_mem := hright
    base_mem := hbase'
    postcritical_subset := ?_
    criticalA_subset := hcriticalA
    criticalB_subset := hcriticalB
    commonMarkov := ⟨hleft, hright, hforwardA, hforwardB, hcells⟩ }⟩
  intro z hz
  exact (hmem z).2
    (jointPostcriticalSet_subset_commonHull hcrit hAK hBK hz)

/-- **C1.** The two return maps admit a common finite Markov hull containing
the joint postcritical set and the fold base point. -/
theorem commonMarkovHull_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b) :
    Nonempty (CommonMarkovHullData A B F) := by
  obtain ⟨K, hKfinite, hbase, hcrit, hAK, hBK⟩ :=
    twoScaleFold_finite_invariant_vertex_hull F
  exact commonMarkovHullData_of_finite_invariant_vertex_hull
    F K hKfinite hbase hcrit hAK hBK

/-! ## C2: directed substitutions and the metric law -/

/-- Literal directed-edge substitutions induced by the two return maps on
one common ambient alphabet.  The alphabet is kept as an explicit finite
set so the later occurring-letter restriction has a precise source. -/
structure DirectedSubstitutionPairData
    (A B : IntervalMap) {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F) where
  alphabet : OccurringDirectedAlphabet H.vertices
  alphabet_nonempty : alphabet.Nonempty
  contains_every_directed_edge : ∀ e : DirectedMarkovEdge H.vertices,
    e ∈ alphabet
  substitutionA : Symbolic.Substitution alphabet
  substitutionB : Symbolic.Substitution alphabet
  modelsA : ModelsDirectedEdgeSubstitution A alphabet substitutionA
  modelsB : ModelsDirectedEdgeSubstitution B alphabet substitutionB
  letterLength : alphabet → ℝ
  letterLength_eq_edge : ∀ e, letterLength e = e.1.length
  letterLength_pos : ∀ e, 0 < letterLength e
  scalesA : SubstitutionScalesLetterLengths substitutionA letterLength a
  scalesB : SubstitutionScalesLetterLengths substitutionB letterLength b

/-! ### C2a: finite literal paths in an ordered Markov finset -/

private theorem isLiteralDirectedEdgePath_iff_isChain_coding
    {K : Finset I} (w : LiteralDirectedEdgeWord K) :
    IsLiteralDirectedEdgePath w ↔
      w ≠ [] ∧ List.IsChain (fun e f => e.target = f.source) w := by
  induction w with
  | nil => simp [IsLiteralDirectedEdgePath]
  | cons e w ih =>
      cases w with
      | nil => simp [IsLiteralDirectedEdgePath]
      | cons f rest =>
          simp [IsLiteralDirectedEdgePath, List.isChain_cons_cons, ih]

private theorem literalDirectedEdgePath_append_coding
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x : I}
    (hu : IsLiteralDirectedEdgePath u)
    (hv : IsLiteralDirectedEdgePath v)
    (huEnd : DirectedEdgePathEndsAt u x)
    (hvStart : DirectedEdgePathStartsAt v x) :
    IsLiteralDirectedEdgePath (u ++ v) := by
  rw [isLiteralDirectedEdgePath_iff_isChain_coding] at hu hv ⊢
  refine ⟨List.append_ne_nil_of_left_ne_nil hu.1 v, ?_⟩
  apply hu.2.append hv.2
  rcases huEnd with ⟨init, e, rfl, he⟩
  rcases hvStart with ⟨f, rest, rfl, hf⟩
  intro e' he' f' hf'
  simp at he'
  simp at hf'
  subst e'
  subst f'
  exact he.trans hf.symm

private theorem directedEdgePathStartsAt_append_left_coding
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathStartsAt u x) :
    DirectedEdgePathStartsAt (u ++ v) x := by
  rcases h with ⟨e, rest, rfl, he⟩
  exact ⟨e, rest ++ v, by simp, he⟩

private theorem directedEdgePathEndsAt_append_right_coding
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathEndsAt v x) :
    DirectedEdgePathEndsAt (u ++ v) x := by
  rcases h with ⟨init, e, rfl, he⟩
  exact ⟨u ++ init, e, by simp [List.append_assoc], he⟩

private theorem wordMetricLength_append_coding {α : Type*}
    (length : α → ℝ) (u v : Symbolic.Word α) :
    wordMetricLength length (u ++ v) =
      wordMetricLength length u + wordMetricLength length v := by
  simp [wordMetricLength]

/-- Any two distinct vertices are joined by the unique-direction literal
chain through the intervening vertices, with exact Euclidean length. -/
private theorem exists_literalDirectedEdgePath_between_coding
    {K : Finset I} (hzero : leftEndpoint ∈ K)
    (hone : rightEndpoint ∈ K) {x y : I}
    (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) :
    ∃ w : LiteralDirectedEdgeWord K,
      IsLiteralDirectedEdgePath w ∧
        DirectedEdgePathStartsAt w x ∧
        DirectedEdgePathEndsAt w y ∧
        wordMetricLength DirectedMarkovEdge.length w =
          |(y : ℝ) - (x : ℝ)| := by
  classical
  let between (x y : I) : Finset I :=
    K.filter fun z => min x y < z ∧ z < max x y
  have go : ∀ n : ℕ, ∀ {x y : I},
      x ∈ K → y ∈ K → x ≠ y → (between x y).card = n →
      ∃ w : LiteralDirectedEdgeWord K,
        IsLiteralDirectedEdgePath w ∧
          DirectedEdgePathStartsAt w x ∧
          DirectedEdgePathEndsAt w y ∧
          wordMetricLength DirectedMarkovEdge.length w =
            |(y : ℝ) - (x : ℝ)| := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x y hx hy hxy hcard
        rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
        · by_cases hinterior : (between x y).Nonempty
          · obtain ⟨z, hzBetween⟩ := hinterior
            have hzData := Finset.mem_filter.mp hzBetween
            have hzK : z ∈ K := hzData.1
            have hxz : x < z := by
              simpa [between, min_eq_left hxylt.le, max_eq_right hxylt.le]
                using hzData.2.1
            have hzy : z < y := by
              simpa [between, min_eq_left hxylt.le, max_eq_right hxylt.le]
                using hzData.2.2
            have hsubXZ : between x z ⊂ between x y := by
              have hsubset : between x z ⊆ between x y := by
                intro u hu
                have hu' := Finset.mem_filter.mp hu
                have hxu : x < u := by
                  simpa [min_eq_left hxz.le] using hu'.2.1
                have huz : u < z := by
                  simpa [max_eq_right hxz.le] using hu'.2.2
                apply Finset.mem_filter.mpr
                refine ⟨hu'.1, ?_⟩
                simpa [min_eq_left hxylt.le, max_eq_right hxylt.le] using
                  ⟨hxu, huz.trans hzy⟩
              exact (Finset.ssubset_iff_of_subset hsubset).2
                ⟨z, hzBetween, by
                  intro hzChild
                  have hz' := (Finset.mem_filter.mp hzChild).2.2
                  simpa [max_eq_right hxz.le] using hz'⟩
            have hsubZY : between z y ⊂ between x y := by
              have hsubset : between z y ⊆ between x y := by
                intro u hu
                have hu' := Finset.mem_filter.mp hu
                have hzu : z < u := by
                  simpa [min_eq_left hzy.le] using hu'.2.1
                have huy : u < y := by
                  simpa [max_eq_right hzy.le] using hu'.2.2
                apply Finset.mem_filter.mpr
                refine ⟨hu'.1, ?_⟩
                simpa [min_eq_left hxylt.le, max_eq_right hxylt.le] using
                  ⟨hxz.trans hzu, huy⟩
              exact (Finset.ssubset_iff_of_subset hsubset).2
                ⟨z, hzBetween, by
                  intro hzChild
                  have hz' := (Finset.mem_filter.mp hzChild).2.1
                  simpa [min_eq_left hzy.le] using hz'⟩
            have hcardXZ : (between x z).card < n := by
              rw [← hcard]
              exact Finset.card_lt_card hsubXZ
            have hcardZY : (between z y).card < n := by
              rw [← hcard]
              exact Finset.card_lt_card hsubZY
            obtain ⟨u, huPath, huStart, huEnd, huMetric⟩ :=
              ih (between x z).card hcardXZ hx hzK hxz.ne rfl
            obtain ⟨v, hvPath, hvStart, hvEnd, hvMetric⟩ :=
              ih (between z y).card hcardZY hzK hy hzy.ne rfl
            refine ⟨u ++ v,
              literalDirectedEdgePath_append_coding huPath hvPath huEnd hvStart,
              directedEdgePathStartsAt_append_left_coding huStart,
              directedEdgePathEndsAt_append_right_coding hvEnd, ?_⟩
            have hxzR : (x : ℝ) < (z : ℝ) := hxz
            have hzyR : (z : ℝ) < (y : ℝ) := hzy
            have hxyR : (x : ℝ) < (y : ℝ) := hxylt
            rw [wordMetricLength_append_coding, huMetric, hvMetric,
              abs_of_pos (sub_pos.mpr hxzR), abs_of_pos (sub_pos.mpr hzyR),
              abs_of_pos (sub_pos.mpr hxyR)]
            ring
          · have hnone : ∀ z ∈ K, ¬(x < z ∧ z < y) := by
              intro z hzK hz
              exact hinterior ⟨z, Finset.mem_filter.mpr ⟨hzK, by
                simpa [min_eq_left hxylt.le, max_eq_right hxylt.le] using hz⟩⟩
            let xK : ↥K := ⟨x, hx⟩
            let yK : ↥K := ⟨y, hy⟩
            let e : DirectedMarkovEdge K :=
              ⟨((xK, yK), true), ⟨hx, hy, hxylt, hnone⟩⟩
            refine ⟨[e], by simp [IsLiteralDirectedEdgePath], ?_, ?_, ?_⟩
            · exact ⟨e, [], rfl, by simp [e, DirectedMarkovEdge.source,
                DirectedMarkovEdge.forward, DirectedMarkovEdge.lower, xK]⟩
            · exact ⟨[], e, rfl, by simp [e, DirectedMarkovEdge.target,
                DirectedMarkovEdge.forward, DirectedMarkovEdge.upper, yK]⟩
            · simp [wordMetricLength, e, DirectedMarkovEdge.length,
                DirectedMarkovEdge.lower, DirectedMarkovEdge.upper, xK, yK,
                abs_of_pos (sub_pos.mpr
                  (show (x : ℝ) < (y : ℝ) from hxylt))]
        · by_cases hinterior : (between x y).Nonempty
          · obtain ⟨z, hzBetween⟩ := hinterior
            have hzData := Finset.mem_filter.mp hzBetween
            have hzK : z ∈ K := hzData.1
            have hyz : y < z := by
              simpa [between, min_eq_right hyxlt.le, max_eq_left hyxlt.le]
                using hzData.2.1
            have hzx : z < x := by
              simpa [between, min_eq_right hyxlt.le, max_eq_left hyxlt.le]
                using hzData.2.2
            have hsubXZ : between x z ⊂ between x y := by
              have hsubset : between x z ⊆ between x y := by
                intro u hu
                have hu' := Finset.mem_filter.mp hu
                have hzu : z < u := by
                  simpa [min_eq_right hzx.le] using hu'.2.1
                have hux : u < x := by
                  simpa [max_eq_left hzx.le] using hu'.2.2
                apply Finset.mem_filter.mpr
                refine ⟨hu'.1, ?_⟩
                simpa [min_eq_right hyxlt.le, max_eq_left hyxlt.le] using
                  ⟨hyz.trans hzu, hux⟩
              exact (Finset.ssubset_iff_of_subset hsubset).2
                ⟨z, hzBetween, by
                  intro hzChild
                  have hz' := (Finset.mem_filter.mp hzChild).2.1
                  simpa [min_eq_right hzx.le] using hz'⟩
            have hsubZY : between z y ⊂ between x y := by
              have hsubset : between z y ⊆ between x y := by
                intro u hu
                have hu' := Finset.mem_filter.mp hu
                have hyu : y < u := by
                  simpa [min_eq_right hyz.le] using hu'.2.1
                have huz : u < z := by
                  simpa [max_eq_left hyz.le] using hu'.2.2
                apply Finset.mem_filter.mpr
                refine ⟨hu'.1, ?_⟩
                simpa [min_eq_right hyxlt.le, max_eq_left hyxlt.le] using
                  ⟨hyu, huz.trans hzx⟩
              exact (Finset.ssubset_iff_of_subset hsubset).2
                ⟨z, hzBetween, by
                  intro hzChild
                  have hz' := (Finset.mem_filter.mp hzChild).2.2
                  simpa [max_eq_left hyz.le] using hz'⟩
            have hcardXZ : (between x z).card < n := by
              rw [← hcard]
              exact Finset.card_lt_card hsubXZ
            have hcardZY : (between z y).card < n := by
              rw [← hcard]
              exact Finset.card_lt_card hsubZY
            obtain ⟨u, huPath, huStart, huEnd, huMetric⟩ :=
              ih (between x z).card hcardXZ hx hzK hzx.ne' rfl
            obtain ⟨v, hvPath, hvStart, hvEnd, hvMetric⟩ :=
              ih (between z y).card hcardZY hzK hy hyz.ne' rfl
            refine ⟨u ++ v,
              literalDirectedEdgePath_append_coding huPath hvPath huEnd hvStart,
              directedEdgePathStartsAt_append_left_coding huStart,
              directedEdgePathEndsAt_append_right_coding hvEnd, ?_⟩
            have hzxR : (z : ℝ) < (x : ℝ) := hzx
            have hyzR : (y : ℝ) < (z : ℝ) := hyz
            have hyxR : (y : ℝ) < (x : ℝ) := hyxlt
            rw [wordMetricLength_append_coding, huMetric, hvMetric,
              abs_of_neg (sub_neg.mpr hzxR), abs_of_neg (sub_neg.mpr hyzR),
              abs_of_neg (sub_neg.mpr hyxR)]
            ring
          · have hnone : ∀ z ∈ K, ¬(y < z ∧ z < x) := by
              intro z hzK hz
              exact hinterior ⟨z, Finset.mem_filter.mpr ⟨hzK, by
                simpa [min_eq_right hyxlt.le, max_eq_left hyxlt.le] using hz⟩⟩
            let yK : ↥K := ⟨y, hy⟩
            let xK : ↥K := ⟨x, hx⟩
            let e : DirectedMarkovEdge K :=
              ⟨((yK, xK), false), ⟨hy, hx, hyxlt, hnone⟩⟩
            refine ⟨[e], by simp [IsLiteralDirectedEdgePath], ?_, ?_, ?_⟩
            · exact ⟨e, [], rfl, by simp [e, DirectedMarkovEdge.source,
                DirectedMarkovEdge.forward, DirectedMarkovEdge.upper, xK]⟩
            · exact ⟨[], e, rfl, by simp [e, DirectedMarkovEdge.target,
                DirectedMarkovEdge.forward, DirectedMarkovEdge.lower, yK]⟩
            · simp [wordMetricLength, e, DirectedMarkovEdge.length,
                DirectedMarkovEdge.lower, DirectedMarkovEdge.upper, xK, yK,
                abs_of_neg (sub_neg.mpr
                  (show (y : ℝ) < (x : ℝ) from hyxlt))]
  exact go (between x y).card hx hy hxy rfl

/-! ### C2b: exact metric scaling on one Markov edge -/

private theorem RealPartition.exists_adjacent_straddling_coding
    (partition : RealPartition) {x : ℝ} (hxI : x ∈ I)
    (hxnot : x ∉ partition.points) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ a < x ∧ x < b := by
  classical
  let lower := partition.points.filter fun z => z < x
  let upper := partition.points.filter fun z => x < z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    have hx0 : (0 : ℝ) < x := lt_of_le_of_ne hxI.1 fun h => by
      apply hxnot
      simpa [h] using partition.zero_mem
    simp [lower, partition.zero_mem, hx0]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have hx1 : x < (1 : ℝ) := lt_of_le_of_ne hxI.2 fun h => by
      apply hxnot
      simpa [h] using partition.one_mem
    simp [upper, partition.one_mem, hx1]
  obtain ⟨a, ha, hamax⟩ := lower.exists_max_image id hlower
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨a, b, ⟨ha'.1, hb'.1, ha'.2.trans hb'.2, ?_⟩,
    ha'.2, hb'.2⟩
  intro z hz hzb
  by_cases hzx : z < x
  · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzx⟩
    have hza : z ≤ a := by simpa using hamax z hzlower
    exact (not_lt_of_ge hza) hzb.1
  · have hxz : x < z := lt_of_le_of_ne (le_of_not_gt hzx) fun h => by
      apply hxnot
      simpa [h] using hz
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hxz⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzb.2

/-- The endpoint displacement on one Markov edge has exactly the prescribed
constant-slope magnitude. -/
private theorem markovEdge_image_distance_coding
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (e : DirectedMarkovEdge K) :
    |(T e.target : ℝ) - (T e.source : ℝ)| = scale * e.length := by
  classical
  rcases (hmarkov e.2).1 with ⟨m, c, hmc⟩
  rcases hslope.2 with ⟨partition, hpartition⟩
  obtain ⟨r, hrEdge, hrnot⟩ :=
    (Set.Ioo_infinite
      (show (e.lower : ℝ) < (e.upper : ℝ) from e.2.2.2.1)).exists_notMem_finset
        partition.points
  have hrI : r ∈ I := ⟨e.lower.property.1.trans hrEdge.1.le,
    hrEdge.2.le.trans e.upper.property.2⟩
  obtain ⟨u, v, huv, hur, hrv⟩ :=
    partition.exists_adjacent_straddling_coding hrI hrnot
  rcases hpartition huv with ⟨m', c', hm'abs, hm'c⟩
  have hrmin : r < min v (e.upper : ℝ) := lt_min hrv hrEdge.2
  obtain ⟨s, hrs, hsmin⟩ := exists_between hrmin
  have hsv : s < v := hsmin.trans_le (min_le_left _ _)
  have hsupper : s < (e.upper : ℝ) :=
    hsmin.trans_le (min_le_right _ _)
  let rI : I := ⟨r, hrI⟩
  let sI : I := ⟨s, ⟨e.lower.property.1.trans (hrEdge.1.le.trans hrs.le),
    hsupper.le.trans e.upper.property.2⟩⟩
  have hrMarkov : rI ∈ Set.Icc e.lower e.upper :=
    ⟨hrEdge.1.le, hrEdge.2.le⟩
  have hsMarkov : sI ∈ Set.Icc e.lower e.upper :=
    ⟨hrEdge.1.le.trans hrs.le, hsupper.le⟩
  have hrCell : rI ∈ intervalCell u v := ⟨hur.le, hrv.le⟩
  have hsCell : sI ∈ intervalCell u v :=
    ⟨hur.le.trans hrs.le, hsv.le⟩
  have heqR : m * r + c = m' * r + c' := by
    calc
      m * r + c = (T rI : ℝ) := (hmc rI hrMarkov).symm
      _ = m' * r + c' := hm'c rI hrCell
  have heqS : m * s + c = m' * s + c' := by
    calc
      m * s + c = (T sI : ℝ) := (hmc sI hsMarkov).symm
      _ = m' * s + c' := hm'c sI hsCell
  have hmm' : m = m' := by
    nlinarith
  have hmabs : |m| = scale := by simpa [hmm'] using hm'abs
  have hlowerMem : e.lower ∈ Set.Icc e.lower e.upper :=
    ⟨le_rfl, e.2.2.2.1.le⟩
  have hupperMem : e.upper ∈ Set.Icc e.lower e.upper :=
    ⟨e.2.2.2.1.le, le_rfl⟩
  have hdiff : (T e.upper : ℝ) - (T e.lower : ℝ) =
      m * ((e.upper : ℝ) - (e.lower : ℝ)) := by
    rw [hmc e.upper hupperMem, hmc e.lower hlowerMem]
    ring
  have hforwardDistance :
      |(T e.upper : ℝ) - (T e.lower : ℝ)| = scale * e.length := by
    have hlenpos : 0 < (e.upper : ℝ) - (e.lower : ℝ) :=
      sub_pos.mpr
        (show (e.lower : ℝ) < (e.upper : ℝ) from e.2.2.2.1)
    change |(T e.upper : ℝ) - (T e.lower : ℝ)| =
      scale * ((e.upper : ℝ) - (e.lower : ℝ))
    rw [hdiff, abs_mul, hmabs, abs_of_pos hlenpos]
  cases hdir : e.forward with
  | false =>
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir,
        abs_sub_comm] using hforwardDistance
  | true =>
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir]
        using hforwardDistance

/-! ### C2c: the full substitution of one Markov map -/

private structure FullMarkovSubstitutionData
    (T : IntervalMap) (K : Finset I) (scale : ℝ) where
  substitution : Symbolic.Substitution (DirectedMarkovEdge K)
  path : ∀ e, IsLiteralDirectedEdgePath (substitution e)
  starts : ∀ e, DirectedEdgePathStartsAt (substitution e) (T e.source)
  ends : ∀ e, DirectedEdgePathEndsAt (substitution e) (T e.target)
  metric : SubstitutionScalesLetterLengths substitution
    DirectedMarkovEdge.length scale

private theorem fullMarkovSubstitutionData_exists
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    (hzero : leftEndpoint ∈ K) (hone : rightEndpoint ∈ K)
    (hforward : ∀ x ∈ K, T x ∈ K)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale) :
    Nonempty (FullMarkovSubstitutionData T K scale) := by
  classical
  have himagesDistinct (e : DirectedMarkovEdge K) :
      T e.source ≠ T e.target := by
    have hlowerMem : e.lower ∈ Set.Icc e.lower e.upper :=
      ⟨le_rfl, e.2.2.2.1.le⟩
    have hupperMem : e.upper ∈ Set.Icc e.lower e.upper :=
      ⟨e.2.2.2.1.le, le_rfl⟩
    have hne : T e.lower ≠ T e.upper := by
      rcases (hmarkov e.2).2 with hmono | hanti
      · exact (hmono hlowerMem hupperMem e.2.2.2.1).ne
      · exact (hanti hlowerMem hupperMem e.2.2.2.1).ne'
    cases hdir : e.forward with
    | false =>
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir]
          using hne.symm
    | true =>
        simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hdir]
          using hne
  have hsourceK (e : DirectedMarkovEdge K) : T e.source ∈ K := by
    apply hforward
    cases hdir : e.forward <;>
      simp [DirectedMarkovEdge.source, hdir, DirectedMarkovEdge.lower,
        DirectedMarkovEdge.upper]
  have htargetK (e : DirectedMarkovEdge K) : T e.target ∈ K := by
    apply hforward
    cases hdir : e.forward <;>
      simp [DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.lower,
        DirectedMarkovEdge.upper]
  have hexists (e : DirectedMarkovEdge K) :
      ∃ w : LiteralDirectedEdgeWord K,
        IsLiteralDirectedEdgePath w ∧
          DirectedEdgePathStartsAt w (T e.source) ∧
          DirectedEdgePathEndsAt w (T e.target) ∧
          wordMetricLength DirectedMarkovEdge.length w =
            |(T e.target : ℝ) - (T e.source : ℝ)| :=
    exists_literalDirectedEdgePath_between_coding hzero hone
      (hsourceK e) (htargetK e) (himagesDistinct e)
  let image : DirectedMarkovEdge K → LiteralDirectedEdgeWord K :=
    fun e => Classical.choose (hexists e)
  have himage (e : DirectedMarkovEdge K) :
      IsLiteralDirectedEdgePath (image e) ∧
        DirectedEdgePathStartsAt (image e) (T e.source) ∧
        DirectedEdgePathEndsAt (image e) (T e.target) ∧
        wordMetricLength DirectedMarkovEdge.length (image e) =
          |(T e.target : ℝ) - (T e.source : ℝ)| :=
    Classical.choose_spec (hexists e)
  let substitution : Symbolic.Substitution (DirectedMarkovEdge K) :=
    { image := image
      image_ne_nil := by
        intro e hnil
        have hpath := (himage e).1
        rw [hnil] at hpath
        exact hpath }
  refine ⟨{
    substitution := substitution
    path := fun e => (himage e).1
    starts := fun e => (himage e).2.1
    ends := fun e => (himage e).2.2.1
    metric := ?_ }⟩
  intro e
  change wordMetricLength DirectedMarkovEdge.length (image e) =
    scale * e.length
  rw [(himage e).2.2.2]
  exact markovEdge_image_distance_coding hmarkov hslope e

/-! ### C2d: lift to the common all-directed-edge subtype alphabet -/

private structure FullAlphabetMarkovSubstitutionData
    (T : IntervalMap) (K : Finset I) (scale : ℝ)
    (alphabet : OccurringDirectedAlphabet K) where
  substitution : Symbolic.Substitution alphabet
  models : ModelsDirectedEdgeSubstitution T alphabet substitution
  metric : SubstitutionScalesLetterLengths substitution
    (fun e => e.1.length) scale

private theorem allDirectedEdges_nonempty
    {K : Finset I} (hzero : leftEndpoint ∈ K)
    (hone : rightEndpoint ∈ K) :
    (Finset.univ : OccurringDirectedAlphabet K).Nonempty := by
  have hne : leftEndpoint ≠ rightEndpoint := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num at hval
  obtain ⟨w, hpath, _hstart, _hend, _hmetric⟩ :=
    exists_literalDirectedEdgePath_between_coding
      hzero hone hzero hone hne
  cases w with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons e rest => exact ⟨e, Finset.mem_univ e⟩

private theorem FullMarkovSubstitutionData.liftToAllDirectedEdges
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    (full : FullMarkovSubstitutionData T K scale) :
    Nonempty (FullAlphabetMarkovSubstitutionData T K scale
      (Finset.univ : OccurringDirectedAlphabet K)) := by
  classical
  let alphabet : OccurringDirectedAlphabet K := Finset.univ
  let retain : DirectedMarkovEdge K → alphabet :=
    fun e => ⟨e, Finset.mem_univ e⟩
  let substitution : Symbolic.Substitution alphabet :=
    { image := fun e => (full.substitution e.1).map retain
      image_ne_nil := by
        intro e hnil
        apply full.substitution.image_ne_nil e.1
        simpa using hnil }
  have hgeom (e : alphabet) :
      geometricEdgeWord alphabet (substitution e) =
        full.substitution e.1 := by
    simp only [geometricEdgeWord, substitution, List.map_map]
    change List.map (fun z : DirectedMarkovEdge K => z)
      (full.substitution e.1) = full.substitution e.1
    simp
  have hmodels : ModelsDirectedEdgeSubstitution T alphabet substitution := by
    intro e
    rw [hgeom e]
    exact ⟨full.path e.1, full.starts e.1, full.ends e.1⟩
  have hmetric : SubstitutionScalesLetterLengths substitution
      (fun e : alphabet => e.1.length) scale := by
    intro e
    calc
      wordMetricLength (fun e : alphabet => e.1.length) (substitution e) =
          wordMetricLength DirectedMarkovEdge.length
            (full.substitution e.1) := by
        simp only [wordMetricLength, substitution, List.map_map]
        change (List.map DirectedMarkovEdge.length
          (full.substitution e.1)).sum =
            (List.map DirectedMarkovEdge.length
              (full.substitution e.1)).sum
        rfl
      _ = scale * e.1.length := full.metric e.1
  change Nonempty (FullAlphabetMarkovSubstitutionData T K scale alphabet)
  exact ⟨{
    substitution := substitution
    models := hmodels
    metric := hmetric }⟩

/-- **C2.** The common Markov hull produces the two literal directed-edge
substitutions, and geometric edge length is scaled by `a` and `b`. -/
theorem directedSubstitutionPair_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F) :
    Nonempty (DirectedSubstitutionPairData A B F H) := by
  classical
  have hmarkovA : ∀ ⦃x y : I⦄, FinsetAdjacent H.vertices x y →
      IsAffineOn A (Set.Icc x y) ∧
        IsStrictlyMonotoneOn A (Set.Icc x y) :=
    fun _ _ hxy => (H.commonMarkov.2.2.2.2 hxy).1
  have hmarkovB : ∀ ⦃x y : I⦄, FinsetAdjacent H.vertices x y →
      IsAffineOn B (Set.Icc x y) ∧
        IsStrictlyMonotoneOn B (Set.Icc x y) :=
    fun _ _ hxy => (H.commonMarkov.2.2.2.2 hxy).2
  let fullA : FullMarkovSubstitutionData A H.vertices a :=
    Classical.choice (fullMarkovSubstitutionData_exists
      H.left_mem H.right_mem H.commonMarkov.2.2.1 hmarkovA
      F.constantSlope_A)
  let fullB : FullMarkovSubstitutionData B H.vertices b :=
    Classical.choice (fullMarkovSubstitutionData_exists
      H.left_mem H.right_mem H.commonMarkov.2.2.2.1 hmarkovB
      F.constantSlope_B)
  let liftedA : FullAlphabetMarkovSubstitutionData A H.vertices a
      (Finset.univ : OccurringDirectedAlphabet H.vertices) :=
    Classical.choice fullA.liftToAllDirectedEdges
  let liftedB : FullAlphabetMarkovSubstitutionData B H.vertices b
      (Finset.univ : OccurringDirectedAlphabet H.vertices) :=
    Classical.choice fullB.liftToAllDirectedEdges
  refine ⟨{
    alphabet := Finset.univ
    alphabet_nonempty := allDirectedEdges_nonempty H.left_mem H.right_mem
    contains_every_directed_edge := fun e => Finset.mem_univ e
    substitutionA := liftedA.substitution
    substitutionB := liftedB.substitution
    modelsA := liftedA.models
    modelsB := liftedB.models
    letterLength := fun e => e.1.length
    letterLength_eq_edge := fun _ => rfl
    letterLength_pos := fun e => e.1.length_pos
    scalesA := liftedA.metric
    scalesB := liftedB.metric }⟩

/-! ## C3: fold values and the literal itinerary -/

/-- A genuine fold of a path: on some two-sided neighbourhood the path is
strictly monotone on each side and reverses orientation at the centre. -/
def IsPathFoldAt (ψ : ℝ → I) (t : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ((StrictMonoOn ψ (Set.Icc (t - δ) t) ∧
        StrictAntiOn ψ (Set.Icc t (t + δ))) ∨
      (StrictAntiOn ψ (Set.Icc (t - δ) t) ∧
        StrictMonoOn ψ (Set.Icc t (t + δ))))

/-- The ray word and its exact unit-speed geometric realization.  Local
finiteness of fold times records the no-bounded-accumulation assertion used
when the itinerary is cut into successive directed Markov edges. -/
structure FoldItineraryData
    (A B : IntervalMap) {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H) where
  word : Symbolic.InfiniteWord S.alphabet
  starts_at_base : (occurringEdge S.alphabet (word 0)).source = F.base
  fold_values_markov : ∀ t : ℝ, 0 ≤ t → IsPathFoldAt F.ray t →
    F.ray t ∈ H.vertices
  fold_times_locally_finite : ∀ u v : ℝ, 0 ≤ u → u ≤ v →
    ({t : ℝ | IsPathFoldAt F.ray t} ∩ Set.Icc u v).Finite
  itinerary : HasLiteralUnitSpeedItinerary F.ray
    (occurringEdge S.alphabet) S.letterLength word

/-! ### C3a: local finiteness of genuine path folds -/

private theorem not_isPathFoldAt_of_one_orientation_neighborhood
    {ψ : ℝ → I} {l t r : ℝ} (hlt : l < t) (htr : t < r)
    (horient : StrictMonoOn ψ (Set.Icc l r) ∨
      StrictAntiOn ψ (Set.Icc l r)) :
    ¬IsPathFoldAt ψ t := by
  rintro ⟨δ, hδ, hfold⟩
  let εL := min (t - l) δ / 2
  let εR := min (r - t) δ / 2
  have hεL : 0 < εL := div_pos (lt_min (sub_pos.mpr hlt) hδ) (by norm_num)
  have hεR : 0 < εR := div_pos (lt_min (sub_pos.mpr htr) hδ) (by norm_num)
  have hεLlt : εL < t - l := by
    have hmin := lt_min (sub_pos.mpr hlt) hδ
    have hle := min_le_left (t - l) δ
    dsimp [εL]
    nlinarith
  have hεLδ : εL < δ := by
    have hmin := lt_min (sub_pos.mpr hlt) hδ
    have hle := min_le_right (t - l) δ
    dsimp [εL]
    nlinarith
  have hεRlt : εR < r - t := by
    have hmin := lt_min (sub_pos.mpr htr) hδ
    have hle := min_le_left (r - t) δ
    dsimp [εR]
    nlinarith
  have hεRδ : εR < δ := by
    have hmin := lt_min (sub_pos.mpr htr) hδ
    have hle := min_le_right (r - t) δ
    dsimp [εR]
    nlinarith
  let p := t - εL
  let q := t + εR
  have hpt : p < t := by dsimp [p]; linarith
  have htq : t < q := by dsimp [q]; linarith
  have hpGlobal : p ∈ Set.Icc l r := by
    dsimp [p]
    constructor <;> linarith
  have htGlobal : t ∈ Set.Icc l r := ⟨hlt.le, htr.le⟩
  have hqGlobal : q ∈ Set.Icc l r := by
    dsimp [q]
    constructor <;> linarith
  have hpFold : p ∈ Set.Icc (t - δ) t := by
    dsimp [p]
    constructor <;> linarith
  have htFoldL : t ∈ Set.Icc (t - δ) t := by constructor <;> linarith
  have htFoldR : t ∈ Set.Icc t (t + δ) := by constructor <;> linarith
  have hqFold : q ∈ Set.Icc t (t + δ) := by
    dsimp [q]
    constructor <;> linarith
  rcases horient with hmono | hanti
  · rcases hfold with ⟨_hleftMono, hrightAnti⟩ |
      ⟨hleftAnti, _hrightMono⟩
    · have hinc := hmono htGlobal hqGlobal htq
      have hdec := hrightAnti htFoldR hqFold htq
      exact lt_asymm hinc hdec
    · have hinc := hmono hpGlobal htGlobal hpt
      have hdec := hleftAnti hpFold htFoldL hpt
      exact lt_asymm hinc hdec
  · rcases hfold with ⟨hleftMono, _hrightAnti⟩ |
      ⟨_hleftAnti, hrightMono⟩
    · have hdec := hanti hpGlobal htGlobal hpt
      have hinc := hleftMono hpFold htFoldL hpt
      exact lt_asymm hdec hinc
    · have hdec := hanti htGlobal hqGlobal htq
      have hinc := hrightMono htFoldR hqFold htq
      exact lt_asymm hdec hinc

/-- A genuine fold of a finite-piece unit-speed path in a compact interval
must occur at an endpoint or at one of the finitely many presentation
vertices. -/
private theorem foldTimes_finite_of_finitePieceUnitSpeedOn
    {ψ : ℝ → I} {u v : ℝ} (hpieces : IsFinitePieceUnitSpeedOn ψ u v) :
    ({t : ℝ | IsPathFoldAt ψ t} ∩ Set.Icc u v).Finite := by
  classical
  obtain ⟨vertices, hu, hv, hvertices, hcells⟩ := hpieces
  refine vertices.finite_toSet.subset ?_
  intro t ht
  by_contra htvertices
  have hut : u < t := lt_of_le_of_ne ht.2.1 fun hutEq => by
    apply htvertices
    simpa [hutEq] using hu
  have htv : t < v := lt_of_le_of_ne ht.2.2 fun htvEq => by
    apply htvertices
    simpa [htvEq] using hv
  let lower := vertices.filter fun z => z < t
  let upper := vertices.filter fun z => t < z
  have hlower : lower.Nonempty := by
    refine ⟨u, Finset.mem_filter.mpr ⟨hu, hut⟩⟩
  have hupper : upper.Nonempty := by
    refine ⟨v, Finset.mem_filter.mpr ⟨hv, htv⟩⟩
  obtain ⟨l, hl, hlmax⟩ := lower.exists_max_image id hlower
  obtain ⟨r, hr, hrmin⟩ := upper.exists_min_image id hupper
  have hl' := Finset.mem_filter.mp hl
  have hr' := Finset.mem_filter.mp hr
  have hlr : AdjacentInFinset vertices l r := by
    refine ⟨hl'.1, hr'.1, hl'.2.trans hr'.2, ?_⟩
    intro z hz hzbetween
    by_cases hzt : z < t
    · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzt⟩
      exact (not_lt_of_ge (by simpa using hlmax z hzlower)) hzbetween.1
    · have htz : t < z := lt_of_le_of_ne (le_of_not_gt hzt) fun h => by
        apply htvertices
        simpa [h] using hz
      have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, htz⟩
      exact (not_lt_of_ge (by simpa using hrmin z hzupper)) hzbetween.2
  obtain ⟨m, c, hmabs, hformula⟩ := hcells hlr
  have hmne : m ≠ 0 := by
    intro hm
    rw [hm, abs_zero] at hmabs
    norm_num at hmabs
  have horient : StrictMonoOn ψ (Set.Icc l r) ∨
      StrictAntiOn ψ (Set.Icc l r) := by
    rcases lt_or_gt_of_ne hmne with hmneg | hmpos
    · right
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hformula x hx, hformula y hy]
      have hxy' : x < y := hxy
      nlinarith
    · left
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hformula x hx, hformula y hy]
      have hxy' : x < y := hxy
      nlinarith
  exact not_isPathFoldAt_of_one_orientation_neighborhood
    hl'.2 hr'.2 horient ht.1

private theorem TwoScaleFoldData.fold_times_locally_finite_coding
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b) :
    ∀ u v : ℝ, 0 ≤ u → u ≤ v →
      ({t : ℝ | IsPathFoldAt F.ray t} ∩ Set.Icc u v).Finite := by
  intro u v hu huv
  by_cases huvEq : u = v
  · subst v
    refine (Set.finite_singleton u).subset ?_
    intro t ht
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at ht
    simp only [Set.mem_singleton_iff]
    exact le_antisymm ht.2.2 ht.2.1
  · exact foldTimes_finite_of_finitePieceUnitSpeedOn
      (F.locally_unit_speed u v hu (lt_of_le_of_ne huv huvEq))

/-! ### C3b: every positive fold value is postcritical -/

private theorem TwoScaleFoldData.ray_zero_eq_base_coding
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b) :
    F.ray 0 = F.base := by
  apply Subtype.ext
  simpa using F.initial_unit_germ 0
    ⟨le_rfl, F.initial_radius_pos.le⟩

/-- Iterating the first return identity and scaling back the parameter. -/
private theorem TwoScaleFoldData.returnA_iterate_scale_down
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    F.ray t = iterateMap A n (F.ray (t / a ^ n)) := by
  have ha0 : 0 < a := zero_lt_one.trans F.one_lt_a
  induction n with
  | zero => simp [iterateMap]
  | succ n ih =>
      have hpow : 0 < a ^ (n + 1) := pow_pos ha0 _
      have hsnonneg : 0 ≤ t / a ^ (n + 1) := div_nonneg ht hpow.le
      have hscale : a * (t / a ^ (n + 1)) = t / a ^ n := by
        rw [pow_succ]
        field_simp [ha0.ne', (pow_pos ha0 n).ne']
      have hreturn := F.return_A (t / a ^ (n + 1)) hsnonneg
      rw [hscale] at hreturn
      calc
        F.ray t = iterateMap A n (F.ray (t / a ^ n)) := ih
        _ = iterateMap A n (A (F.ray (t / a ^ (n + 1)))) :=
          congrArg (iterateMap A n) hreturn
        _ = iterateMap A (n + 1) (F.ray (t / a ^ (n + 1))) := by
          exact (Function.iterate_succ_apply A n _).symm

/-- A positive parameter can be scaled strictly into the interior of the
initial unit germ by a positive power of an expanding return scale. -/
private theorem exists_positive_power_scale_down_into_initial_germ
    {a t radius : ℝ} (ha : 1 < a) (ht : 0 < t) (hradius : 0 < radius) :
    ∃ n : ℕ, 0 < n ∧ 0 < t / a ^ n ∧ t / a ^ n < radius := by
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, t / radius < a ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt ha).eventually_gt_atTop _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let n := max N 1
  have hNn : N ≤ n := Nat.le_max_left _ _
  have hn : 0 < n := Nat.zero_lt_one.trans_le (Nat.le_max_right _ _)
  have hbound : t / radius < a ^ n := hN n hNn
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hpow : 0 < a ^ n := pow_pos ha0 n
  refine ⟨n, hn, div_pos ht hpow, ?_⟩
  apply (div_lt_iff₀ hpow).2
  simpa [mul_comm] using (div_lt_iff₀ hradius).1 hbound

/-- Positive affine reparametrization transports a genuine two-sided path
fold in both directions. -/
private theorem isPathFoldAt_positive_rescale_iff
    {ψ : ℝ → I} {scale t : ℝ} (hscale : 0 < scale) :
    IsPathFoldAt (fun u => ψ (scale * u)) (t / scale) ↔
      IsPathFoldAt ψ t := by
  have hscale_ne : scale ≠ 0 := hscale.ne'
  constructor
  · rintro ⟨ε, hε, hfold⟩
    let δ := scale * ε
    have hδ : 0 < δ := mul_pos hscale hε
    have hcenter : scale * (t / scale) = t := by
      field_simp
    have hdelta : δ / scale = ε := by
      dsimp [δ]
      field_simp
    have hleftCenter : t / scale - ε = (t - δ) / scale := by
      rw [← hdelta]
      ring
    have hrightCenter : t / scale + ε = (t + δ) / scale := by
      rw [← hdelta]
      ring
    have hcancel (x : ℝ) : scale * (x / scale) = x := by
      field_simp
    have pullMonoLeft
        (h : StrictMonoOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale - ε) (t / scale))) :
        StrictMonoOn ψ (Set.Icc (t - δ) t) := by
      intro x hx y hy hxy
      have hx' : x / scale ∈ Set.Icc (t / scale - ε) (t / scale) := by
        constructor
        · rw [hleftCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hx.1
        · exact (div_le_div_iff_of_pos_right hscale).2 hx.2
      have hy' : y / scale ∈ Set.Icc (t / scale - ε) (t / scale) := by
        constructor
        · rw [hleftCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hy.1
        · exact (div_le_div_iff_of_pos_right hscale).2 hy.2
      have hxy' : x / scale < y / scale :=
        (div_lt_div_iff_of_pos_right hscale).2 hxy
      have hstrict := h hx' hy' hxy'
      change ψ (scale * (x / scale)) < ψ (scale * (y / scale)) at hstrict
      rw [hcancel x, hcancel y] at hstrict
      exact hstrict
    have pullAntiLeft
        (h : StrictAntiOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale - ε) (t / scale))) :
        StrictAntiOn ψ (Set.Icc (t - δ) t) := by
      intro x hx y hy hxy
      have hx' : x / scale ∈ Set.Icc (t / scale - ε) (t / scale) := by
        constructor
        · rw [hleftCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hx.1
        · exact (div_le_div_iff_of_pos_right hscale).2 hx.2
      have hy' : y / scale ∈ Set.Icc (t / scale - ε) (t / scale) := by
        constructor
        · rw [hleftCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hy.1
        · exact (div_le_div_iff_of_pos_right hscale).2 hy.2
      have hxy' : x / scale < y / scale :=
        (div_lt_div_iff_of_pos_right hscale).2 hxy
      have hstrict := h hx' hy' hxy'
      change ψ (scale * (y / scale)) < ψ (scale * (x / scale)) at hstrict
      rw [hcancel x, hcancel y] at hstrict
      exact hstrict
    have pullMonoRight
        (h : StrictMonoOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale) (t / scale + ε))) :
        StrictMonoOn ψ (Set.Icc t (t + δ)) := by
      intro x hx y hy hxy
      have hx' : x / scale ∈ Set.Icc (t / scale) (t / scale + ε) := by
        constructor
        · exact (div_le_div_iff_of_pos_right hscale).2 hx.1
        · rw [hrightCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hx.2
      have hy' : y / scale ∈ Set.Icc (t / scale) (t / scale + ε) := by
        constructor
        · exact (div_le_div_iff_of_pos_right hscale).2 hy.1
        · rw [hrightCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hy.2
      have hxy' : x / scale < y / scale :=
        (div_lt_div_iff_of_pos_right hscale).2 hxy
      have hstrict := h hx' hy' hxy'
      change ψ (scale * (x / scale)) < ψ (scale * (y / scale)) at hstrict
      rw [hcancel x, hcancel y] at hstrict
      exact hstrict
    have pullAntiRight
        (h : StrictAntiOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale) (t / scale + ε))) :
        StrictAntiOn ψ (Set.Icc t (t + δ)) := by
      intro x hx y hy hxy
      have hx' : x / scale ∈ Set.Icc (t / scale) (t / scale + ε) := by
        constructor
        · exact (div_le_div_iff_of_pos_right hscale).2 hx.1
        · rw [hrightCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hx.2
      have hy' : y / scale ∈ Set.Icc (t / scale) (t / scale + ε) := by
        constructor
        · exact (div_le_div_iff_of_pos_right hscale).2 hy.1
        · rw [hrightCenter]
          exact (div_le_div_iff_of_pos_right hscale).2 hy.2
      have hxy' : x / scale < y / scale :=
        (div_lt_div_iff_of_pos_right hscale).2 hxy
      have hstrict := h hx' hy' hxy'
      change ψ (scale * (y / scale)) < ψ (scale * (x / scale)) at hstrict
      rw [hcancel x, hcancel y] at hstrict
      exact hstrict
    refine ⟨δ, hδ, ?_⟩
    rcases hfold with ⟨hL, hR⟩ | ⟨hL, hR⟩
    · exact Or.inl ⟨pullMonoLeft hL, pullAntiRight hR⟩
    · exact Or.inr ⟨pullAntiLeft hL, pullMonoRight hR⟩
  · rintro ⟨δ, hδ, hfold⟩
    let ε := δ / scale
    have hε : 0 < ε := div_pos hδ hscale
    have hcenter : scale * (t / scale) = t := by field_simp
    have hscaleε : scale * ε = δ := by
      dsimp [ε]
      field_simp
    have hleftCenter : t / scale - ε = (t - δ) / scale := by
      dsimp [ε]
      ring
    have hrightCenter : t / scale + ε = (t + δ) / scale := by
      dsimp [ε]
      ring
    have pushMonoLeft
        (h : StrictMonoOn ψ (Set.Icc (t - δ) t)) :
        StrictMonoOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale - ε) (t / scale)) := by
      intro x hx y hy hxy
      apply h
      · constructor
        · have hx' := hx.1
          rw [hleftCenter] at hx'
          simpa [mul_comm] using (div_le_iff₀ hscale).1 hx'
        · simpa [mul_comm] using (le_div_iff₀ hscale).1 hx.2
      · constructor
        · have hy' := hy.1
          rw [hleftCenter] at hy'
          simpa [mul_comm] using (div_le_iff₀ hscale).1 hy'
        · simpa [mul_comm] using (le_div_iff₀ hscale).1 hy.2
      · exact mul_lt_mul_of_pos_left hxy hscale
    have pushAntiLeft
        (h : StrictAntiOn ψ (Set.Icc (t - δ) t)) :
        StrictAntiOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale - ε) (t / scale)) := by
      intro x hx y hy hxy
      apply h
      · constructor
        · have hx' := hx.1
          rw [hleftCenter] at hx'
          simpa [mul_comm] using (div_le_iff₀ hscale).1 hx'
        · simpa [mul_comm] using (le_div_iff₀ hscale).1 hx.2
      · constructor
        · have hy' := hy.1
          rw [hleftCenter] at hy'
          simpa [mul_comm] using (div_le_iff₀ hscale).1 hy'
        · simpa [mul_comm] using (le_div_iff₀ hscale).1 hy.2
      · exact mul_lt_mul_of_pos_left hxy hscale
    have pushMonoRight
        (h : StrictMonoOn ψ (Set.Icc t (t + δ))) :
        StrictMonoOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale) (t / scale + ε)) := by
      intro x hx y hy hxy
      apply h
      · constructor
        · simpa [mul_comm] using (div_le_iff₀ hscale).1 hx.1
        · have hx' := hx.2
          rw [hrightCenter] at hx'
          simpa [mul_comm] using (le_div_iff₀ hscale).1 hx'
      · constructor
        · simpa [mul_comm] using (div_le_iff₀ hscale).1 hy.1
        · have hy' := hy.2
          rw [hrightCenter] at hy'
          simpa [mul_comm] using (le_div_iff₀ hscale).1 hy'
      · exact mul_lt_mul_of_pos_left hxy hscale
    have pushAntiRight
        (h : StrictAntiOn ψ (Set.Icc t (t + δ))) :
        StrictAntiOn (fun u => ψ (scale * u))
          (Set.Icc (t / scale) (t / scale + ε)) := by
      intro x hx y hy hxy
      apply h
      · constructor
        · simpa [mul_comm] using (div_le_iff₀ hscale).1 hx.1
        · have hx' := hx.2
          rw [hrightCenter] at hx'
          simpa [mul_comm] using (le_div_iff₀ hscale).1 hx'
      · constructor
        · simpa [mul_comm] using (div_le_iff₀ hscale).1 hy.1
        · have hy' := hy.2
          rw [hrightCenter] at hy'
          simpa [mul_comm] using (le_div_iff₀ hscale).1 hy'
      · exact mul_lt_mul_of_pos_left hxy hscale
    refine ⟨ε, hε, ?_⟩
    rcases hfold with ⟨hL, hR⟩ | ⟨hL, hR⟩
    · exact Or.inl ⟨pushMonoLeft hL, pushAntiRight hR⟩
    · exact Or.inr ⟨pushAntiLeft hL, pushMonoRight hR⟩

/-- On the interior of the initial unit germ, a fold of the scaled returned
path is exactly an intrinsic turn of the corresponding map iterate. -/
private theorem TwoScaleFoldData.genuineTurn_iterate_of_positive_fold
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    {t : ℝ} (ht : 0 < t) {n : ℕ} (hn : 0 < n)
    (hsmall : t / a ^ n < F.initial_radius)
    (hfold : IsPathFoldAt F.ray t) :
    IsGenuineTurn (iterateMap A n) (F.ray (t / a ^ n)) := by
  let scale : ℝ := a ^ n
  let u : ℝ := t / scale
  have ha0 : 0 < a := zero_lt_one.trans F.one_lt_a
  have hscale : 0 < scale := pow_pos ha0 n
  have hu : 0 < u := div_pos ht hscale
  have huradius : u < F.initial_radius := hsmall
  have hscaledFold : IsPathFoldAt (fun s => F.ray (scale * s)) u := by
    apply (isPathFoldAt_positive_rescale_iff hscale).2
    simpa [u, scale] using hfold
  obtain ⟨δ, hδ, hfoldScaled⟩ := hscaledFold
  let ε : ℝ := min δ (min u (F.initial_radius - u)) / 2
  have hinner : 0 < min u (F.initial_radius - u) :=
    lt_min hu (sub_pos.mpr huradius)
  have hminpos : 0 < min δ (min u (F.initial_radius - u)) :=
    lt_min hδ hinner
  have hε : 0 < ε := div_pos hminpos (by norm_num)
  have hεδ : ε < δ := by
    have hle := min_le_left δ (min u (F.initial_radius - u))
    dsimp [ε]
    nlinarith
  have hεu : ε < u := by
    have hle := (min_le_right δ (min u (F.initial_radius - u))).trans
      (min_le_left u (F.initial_radius - u))
    dsimp [ε]
    nlinarith
  have hεradius : ε < F.initial_radius - u := by
    have hle := (min_le_right δ (min u (F.initial_radius - u))).trans
      (min_le_right u (F.initial_radius - u))
    dsimp [ε]
    nlinarith
  have hp0 : 0 ≤ u - ε := by linarith
  have hqrad : u + ε ≤ F.initial_radius := by linarith
  have hreturn (s : ℝ) (hs : 0 ≤ s) :
      F.ray (scale * s) = iterateMap A n (F.ray s) := by
    have h := F.returnA_iterate_scale_down n
      (t := scale * s) (mul_nonneg hscale.le hs)
    simpa [scale, hscale.ne'] using h
  have transferMono {p q : ℝ} (hp0 : 0 ≤ p) (hpq : p ≤ q)
      (hqrad : q ≤ F.initial_radius)
      (hpath : StrictMonoOn (fun s => F.ray (scale * s))
        (Set.Icc p q)) :
      StrictMonoOn (iterateMap A n) (Set.Icc (F.ray p) (F.ray q)) := by
    intro x hx y hy hxy
    let sx : ℝ := (x : ℝ) - (F.base : ℝ)
    let sy : ℝ := (y : ℝ) - (F.base : ℝ)
    have hpMem : p ∈ Set.Icc (0 : ℝ) F.initial_radius :=
      ⟨hp0, hpq.trans hqrad⟩
    have hqMem : q ∈ Set.Icc (0 : ℝ) F.initial_radius :=
      ⟨hp0.trans hpq, hqrad⟩
    have hsx : sx ∈ Set.Icc p q := by
      have hpval := F.initial_unit_germ p hpMem
      have hqval := F.initial_unit_germ q hqMem
      have hxL : (F.ray p : ℝ) ≤ (x : ℝ) := hx.1
      have hxR : (x : ℝ) ≤ (F.ray q : ℝ) := hx.2
      rw [hpval] at hxL
      rw [hqval] at hxR
      dsimp [sx]
      constructor <;> linarith
    have hsy : sy ∈ Set.Icc p q := by
      have hpval := F.initial_unit_germ p hpMem
      have hqval := F.initial_unit_germ q hqMem
      have hyL : (F.ray p : ℝ) ≤ (y : ℝ) := hy.1
      have hyR : (y : ℝ) ≤ (F.ray q : ℝ) := hy.2
      rw [hpval] at hyL
      rw [hqval] at hyR
      dsimp [sy]
      constructor <;> linarith
    have hraySx : F.ray sx = x := by
      apply Subtype.ext
      rw [F.initial_unit_germ sx ⟨hp0.trans hsx.1, hsx.2.trans hqrad⟩]
      simp [sx]
    have hraySy : F.ray sy = y := by
      apply Subtype.ext
      rw [F.initial_unit_germ sy ⟨hp0.trans hsy.1, hsy.2.trans hqrad⟩]
      simp [sy]
    have hsxy : sx < sy := by
      dsimp [sx, sy]
      exact sub_lt_sub_right (show (x : ℝ) < (y : ℝ) from hxy) _
    have hstrict := hpath hsx hsy hsxy
    change F.ray (scale * sx) < F.ray (scale * sy) at hstrict
    rw [hreturn sx (hp0.trans hsx.1), hreturn sy (hp0.trans hsy.1),
      hraySx, hraySy] at hstrict
    exact hstrict
  have transferAnti {p q : ℝ} (hp0 : 0 ≤ p) (hpq : p ≤ q)
      (hqrad : q ≤ F.initial_radius)
      (hpath : StrictAntiOn (fun s => F.ray (scale * s))
        (Set.Icc p q)) :
      StrictAntiOn (iterateMap A n) (Set.Icc (F.ray p) (F.ray q)) := by
    intro x hx y hy hxy
    let sx : ℝ := (x : ℝ) - (F.base : ℝ)
    let sy : ℝ := (y : ℝ) - (F.base : ℝ)
    have hpMem : p ∈ Set.Icc (0 : ℝ) F.initial_radius :=
      ⟨hp0, hpq.trans hqrad⟩
    have hqMem : q ∈ Set.Icc (0 : ℝ) F.initial_radius :=
      ⟨hp0.trans hpq, hqrad⟩
    have hsx : sx ∈ Set.Icc p q := by
      have hpval := F.initial_unit_germ p hpMem
      have hqval := F.initial_unit_germ q hqMem
      have hxL : (F.ray p : ℝ) ≤ (x : ℝ) := hx.1
      have hxR : (x : ℝ) ≤ (F.ray q : ℝ) := hx.2
      rw [hpval] at hxL
      rw [hqval] at hxR
      dsimp [sx]
      constructor <;> linarith
    have hsy : sy ∈ Set.Icc p q := by
      have hpval := F.initial_unit_germ p hpMem
      have hqval := F.initial_unit_germ q hqMem
      have hyL : (F.ray p : ℝ) ≤ (y : ℝ) := hy.1
      have hyR : (y : ℝ) ≤ (F.ray q : ℝ) := hy.2
      rw [hpval] at hyL
      rw [hqval] at hyR
      dsimp [sy]
      constructor <;> linarith
    have hraySx : F.ray sx = x := by
      apply Subtype.ext
      rw [F.initial_unit_germ sx ⟨hp0.trans hsx.1, hsx.2.trans hqrad⟩]
      simp [sx]
    have hraySy : F.ray sy = y := by
      apply Subtype.ext
      rw [F.initial_unit_germ sy ⟨hp0.trans hsy.1, hsy.2.trans hqrad⟩]
      simp [sy]
    have hsxy : sx < sy := by
      dsimp [sx, sy]
      exact sub_lt_sub_right (show (x : ℝ) < (y : ℝ) from hxy) _
    have hstrict := hpath hsx hsy hsxy
    change F.ray (scale * sy) < F.ray (scale * sx) at hstrict
    rw [hreturn sx (hp0.trans hsx.1), hreturn sy (hp0.trans hsy.1),
      hraySx, hraySy] at hstrict
    exact hstrict
  let leftPoint : ℝ := u - ε
  let rightPoint : ℝ := u + ε
  have hleft0 : 0 ≤ leftPoint := by dsimp [leftPoint]; linarith
  have hleftRad : leftPoint ≤ F.initial_radius := by
    dsimp [leftPoint]
    linarith
  have hrightRad : rightPoint ≤ F.initial_radius := by
    dsimp [rightPoint]
    linarith
  have hleftSub : Set.Icc leftPoint u ⊆ Set.Icc (u - δ) u := by
    intro s hs
    change u - ε ≤ s ∧ s ≤ u at hs
    change u - δ ≤ s ∧ s ≤ u
    exact ⟨by linarith [hεδ], hs.2⟩
  have hrightSub : Set.Icc u rightPoint ⊆ Set.Icc u (u + δ) := by
    intro s hs
    change u ≤ s ∧ s ≤ u + ε at hs
    change u ≤ s ∧ s ≤ u + δ
    exact ⟨hs.1, by linarith [hεδ]⟩
  let x0 : I := F.ray leftPoint
  let x1 : I := F.ray u
  let x2 : I := F.ray rightPoint
  have hx01 : x0 < x1 := by
    apply Subtype.coe_lt_coe.mp
    rw [F.initial_unit_germ leftPoint
        ⟨hleft0, hleftRad⟩,
      F.initial_unit_germ u ⟨hu.le, huradius.le⟩]
    dsimp [x0, x1, leftPoint]
    linarith
  have hx12 : x1 < x2 := by
    apply Subtype.coe_lt_coe.mp
    rw [F.initial_unit_germ u ⟨hu.le, huradius.le⟩,
      F.initial_unit_germ rightPoint
        ⟨hleft0.trans (by dsimp [leftPoint, rightPoint]; linarith), hrightRad⟩]
    dsimp [x1, x2, rightPoint]
    linarith
  refine ⟨x0, x2, hx01, hx12, ?_⟩
  rcases hfoldScaled with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · exact Or.inl ⟨
      transferMono hleft0 (by dsimp [leftPoint]; linarith) huradius.le
        (hL.mono hleftSub),
      transferAnti hu.le (by dsimp [rightPoint]; linarith) hrightRad
        (hR.mono hrightSub)⟩
  · exact Or.inr ⟨
      transferAnti hleft0 (by dsimp [leftPoint]; linarith) huradius.le
        (hL.mono hleftSub),
      transferMono hu.le (by dsimp [rightPoint]; linarith) hrightRad
        (hR.mono hrightSub)⟩

/-- Intrinsic vertex values of a positive iterate of the first generator
belong to the joint postcritical set. -/
private theorem criticalValues_iterateA_subset_jointPostcriticalSet
    {A B : IntervalMap} {a : ℝ}
    (hA : FinitePiecePL A) (hAonto : IsOnto A)
    (hAslope : HasConstantAbsoluteSlope A a) (ha : 1 < a)
    {n : ℕ} (hn : 0 < n) :
    criticalValues (iterateMap A n) ⊆ jointPostcriticalSet A B := by
  intro y hy
  have hflat : ¬HasFlatInterval A :=
    hAslope.noFlatInterval (zero_lt_one.trans ha)
  rw [criticalValues_iterate_exact hA hflat hAonto hn] at hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  obtain ⟨_hin, y, hycritical, rfl⟩ := Set.mem_iUnion.mp hi
  obtain ⟨x, hx, rfl⟩ := hycritical
  apply Set.mem_iUnion.mpr
  refine ⟨i + 1, Set.mem_iUnion.mpr ⟨0, ?_⟩⟩
  refine ⟨x, Or.inl hx, ?_⟩
  simp [positiveWordMap, iterateMap, Function.iterate_succ_apply]

private theorem TwoScaleFoldData.fold_value_mem_jointPostcriticalSet_of_pos
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    {t : ℝ} (ht : 0 < t) (hfold : IsPathFoldAt F.ray t) :
    F.ray t ∈ jointPostcriticalSet A B := by
  obtain ⟨n, hn, _hu, hsmall⟩ :=
    exists_positive_power_scale_down_into_initial_germ
      F.one_lt_a ht F.initial_radius_pos
  have hturn := F.genuineTurn_iterate_of_positive_fold
    ht hn hsmall hfold
  apply criticalValues_iterateA_subset_jointPostcriticalSet
    F.finitePiece_A F.onto_A F.constantSlope_A F.one_lt_a hn
  refine ⟨F.ray (t / a ^ n), ?_, ?_⟩
  · exact Or.inr hturn
  · exact (F.returnA_iterate_scale_down n ht.le).symm

/-! ### C3c: locally finite Markov hits and the raw edge itinerary -/

private def nonnegativeMarkovHitTimes (K : Finset I) (ψ : ℝ → I) : Set ℝ :=
  {t | 0 ≤ t ∧ ψ t ∈ K}

private theorem markovHitTimes_finite_on_compact
    {K : Finset I} {ψ : ℝ → I} {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v)
    (hpieces : ∀ x y : ℝ, 0 ≤ x → x < y →
      IsFinitePieceUnitSpeedOn ψ x y) :
    (nonnegativeMarkovHitTimes K ψ ∩ Set.Icc u v).Finite := by
  classical
  by_cases huvEq : u = v
  · subst v
    refine (Set.finite_singleton u).subset ?_
    intro t ht
    have htIcc := ht.2
    have : t = u := le_antisymm htIcc.2 htIcc.1
    simpa [this]
  · have huvlt : u < v := lt_of_le_of_ne huv huvEq
    obtain ⟨vertices, huV, hvV, hvertices, hcells⟩ :=
      hpieces u v hu huvlt
    let cellHits (x y : ℝ) : Set ℝ :=
      {t | t ∈ Set.Icc x y ∧ ψ t ∈ K}
    have cellHits_finite {x y : ℝ}
        (hxy : AdjacentInFinset vertices x y) :
        (cellHits x y).Finite := by
      obtain ⟨m, c, hmabs, hformula⟩ := hcells hxy
      have hmne : m ≠ 0 := by
        intro hm
        rw [hm, abs_zero] at hmabs
        norm_num at hmabs
      have fiber_subsingleton (z : I) :
          ({t : ℝ | t ∈ Set.Icc x y ∧ ψ t = z} : Set ℝ).Subsingleton := by
        intro p hp q hq
        have hpFormula := hformula p hp.1
        have hqFormula := hformula q hq.1
        have hpqValue : (ψ p : ℝ) = (ψ q : ℝ) := by
          rw [hp.2, hq.2]
        rw [hpFormula, hqFormula] at hpqValue
        have hmul : m * p = m * q := by linarith
        exact mul_left_cancel₀ hmne hmul
      refine (K.finite_toSet.biUnion fun z _ =>
        (fiber_subsingleton z).finite).subset ?_
      intro t ht
      apply Set.mem_iUnion_of_mem (ψ t)
      apply Set.mem_iUnion_of_mem ht.2
      exact ⟨ht.1, rfl⟩
    let cells : Finset (ℝ × ℝ) :=
      (vertices.product vertices).filter fun p =>
        AdjacentInFinset vertices p.1 p.2
    have allCellHits_finite :
        (⋃ p ∈ (cells : Set (ℝ × ℝ)), cellHits p.1 p.2).Finite := by
      apply cells.finite_toSet.biUnion
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact cellHits_finite hp'.2
    refine (vertices.finite_toSet.union allCellHits_finite).subset ?_
    intro t ht
    by_cases htV : t ∈ vertices
    · exact Or.inl htV
    · right
      have hut : u < t := lt_of_le_of_ne ht.2.1 fun hutEq => by
        apply htV
        simpa [hutEq] using huV
      have htv : t < v := lt_of_le_of_ne ht.2.2 fun htvEq => by
        apply htV
        simpa [htvEq] using hvV
      let lower := vertices.filter fun z => z < t
      let upper := vertices.filter fun z => t < z
      have hlower : lower.Nonempty := by
        exact ⟨u, Finset.mem_filter.mpr ⟨huV, hut⟩⟩
      have hupper : upper.Nonempty := by
        exact ⟨v, Finset.mem_filter.mpr ⟨hvV, htv⟩⟩
      obtain ⟨l, hl, hlmax⟩ := lower.exists_max_image id hlower
      obtain ⟨r, hr, hrmin⟩ := upper.exists_min_image id hupper
      have hl' := Finset.mem_filter.mp hl
      have hr' := Finset.mem_filter.mp hr
      have hlr : AdjacentInFinset vertices l r := by
        refine ⟨hl'.1, hr'.1, hl'.2.trans hr'.2, ?_⟩
        intro z hz hzbetween
        by_cases hzt : z < t
        · have hzlower : z ∈ lower := Finset.mem_filter.mpr ⟨hz, hzt⟩
          exact (not_lt_of_ge (by simpa using hlmax z hzlower)) hzbetween.1
        · have htz : t < z := lt_of_le_of_ne (le_of_not_gt hzt) fun h => by
            apply htV
            simpa [h] using hz
          have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, htz⟩
          exact (not_lt_of_ge (by simpa using hrmin z hzupper)) hzbetween.2
      have hlrcells : (l, r) ∈ cells := by
        change (l, r) ∈ (vertices.product vertices).filter
          (fun p => AdjacentInFinset vertices p.1 p.2)
        exact Finset.mem_filter.mpr
          ⟨Finset.mk_mem_product hl'.1 hr'.1, hlr⟩
      exact Set.mem_iUnion_of_mem (l, r)
        (Set.mem_iUnion_of_mem hlrcells
          ⟨⟨hl'.2.le, hr'.2.le⟩, ht.1.2⟩)

/-! If no genuine fold occurs between the endpoints of a finite unit-speed
presentation, all presentation slopes have the same sign and the path is one
affine unit-speed segment.  The maximal-extension argument is insensitive to
redundant subdivision vertices. -/
private theorem finitePieceUnitSpeedOn_global_affine_of_no_interior_fold
    {ψ : ℝ → I} {u v : ℝ} (huv : u < v)
    (hpieces : IsFinitePieceUnitSpeedOn ψ u v)
    (hnofold : ∀ s : ℝ, u < s → s < v → ¬IsPathFoldAt ψ s) :
    ∃ m c : ℝ, |m| = 1 ∧
      ∀ s ∈ Set.Icc u v, (ψ s : ℝ) = m * s + c := by
  classical
  obtain ⟨vertices, huV, hvV, hvertices, hcells⟩ := hpieces
  let upper := vertices.filter fun z => u < z
  have hupper : upper.Nonempty := by
    exact ⟨v, Finset.mem_filter.mpr ⟨hvV, huv⟩⟩
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have hb' := Finset.mem_filter.mp hb
  have hub : AdjacentInFinset vertices u b := by
    refine ⟨huV, hb'.1, hb'.2, ?_⟩
    intro z hz hzbetween
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hzbetween.1⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzbetween.2
  obtain ⟨m, c, hmabs, hformula₀⟩ := hcells hub
  have hmne : m ≠ 0 := by
    intro hm
    rw [hm, abs_zero] at hmabs
    norm_num at hmabs
  let good : Finset ℝ := vertices.filter fun z =>
    u ≤ z ∧ z ≤ v ∧
      ∀ x : ℝ, u ≤ x → x ≤ z → (ψ x : ℝ) = m * x + c
  have hbv : b ≤ v := (hvertices b hb'.1).2
  have hbgood : b ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨hb'.1, hb'.2.le, hbv, ?_⟩
    intro x hux hxb
    exact hformula₀ x ⟨hux, hxb⟩
  obtain ⟨g, hg, hgmax⟩ := good.exists_max_image id ⟨b, hbgood⟩
  have hgdata := Finset.mem_filter.mp hg
  have hgV : g ∈ vertices := hgdata.1
  have hug : u < g := hb'.2.trans_le (by simpa using hgmax b hbgood)
  have hgv : g ≤ v := hgdata.2.2.1
  have hglobalg := hgdata.2.2.2
  have hg_eq_v : g = v := by
    apply le_antisymm hgv
    by_contra hnot
    have hgvlt : g < v := lt_of_not_ge hnot
    let aboveG := vertices.filter fun z => g < z
    have haboveG : aboveG.Nonempty := by
      exact ⟨v, Finset.mem_filter.mpr ⟨hvV, hgvlt⟩⟩
    obtain ⟨d, hd, hdmin⟩ := aboveG.exists_min_image id haboveG
    have hd' := Finset.mem_filter.mp hd
    have hgd : AdjacentInFinset vertices g d := by
      refine ⟨hgV, hd'.1, hd'.2, ?_⟩
      intro z hz hzbetween
      have hzabove : z ∈ aboveG :=
        Finset.mem_filter.mpr ⟨hz, hzbetween.1⟩
      have hdz : d ≤ z := by simpa using hdmin z hzabove
      exact (not_lt_of_ge hdz) hzbetween.2
    obtain ⟨m₁, c₁, hm₁abs, hformula₁⟩ := hcells hgd
    have hm₁ne : m₁ ≠ 0 := by
      intro hm₁
      rw [hm₁, abs_zero] at hm₁abs
      norm_num at hm₁abs
    have hdv : d ≤ v := (hvertices d hd'.1).2
    have hleftMono (hmpos : 0 < m) :
        StrictMonoOn ψ (Set.Icc u g) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg x hx.1 hx.2, hglobalg y hy.1 hy.2]
      nlinarith
    have hleftAnti (hmneg : m < 0) :
        StrictAntiOn ψ (Set.Icc u g) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg x hx.1 hx.2, hglobalg y hy.1 hy.2]
      nlinarith
    have hrightMono (hm₁pos : 0 < m₁) :
        StrictMonoOn ψ (Set.Icc g d) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ x hx, hformula₁ y hy]
      nlinarith
    have hrightAnti (hm₁neg : m₁ < 0) :
        StrictAntiOn ψ (Set.Icc g d) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ x hx, hformula₁ y hy]
      nlinarith
    have orientation_change_is_fold
        (hleft : StrictMonoOn ψ (Set.Icc u g))
        (hright : StrictAntiOn ψ (Set.Icc g d)) :
        IsPathFoldAt ψ g := by
      let δ : ℝ := min (g - u) (d - g) / 2
      have hmin : 0 < min (g - u) (d - g) :=
        lt_min (sub_pos.mpr hug) (sub_pos.mpr hd'.2)
      have hδ : 0 < δ := div_pos hmin (by norm_num)
      have hδleft : δ < g - u := by
        have hle := min_le_left (g - u) (d - g)
        dsimp [δ]
        nlinarith
      have hδright : δ < d - g := by
        have hle := min_le_right (g - u) (d - g)
        dsimp [δ]
        nlinarith
      refine ⟨δ, hδ, Or.inl ⟨hleft.mono ?_, hright.mono ?_⟩⟩
      · intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩
      · intro x hx
        exact ⟨hx.1, by linarith [hx.2]⟩
    have orientation_change_is_fold'
        (hleft : StrictAntiOn ψ (Set.Icc u g))
        (hright : StrictMonoOn ψ (Set.Icc g d)) :
        IsPathFoldAt ψ g := by
      let δ : ℝ := min (g - u) (d - g) / 2
      have hmin : 0 < min (g - u) (d - g) :=
        lt_min (sub_pos.mpr hug) (sub_pos.mpr hd'.2)
      have hδ : 0 < δ := div_pos hmin (by norm_num)
      have hδleft : δ < g - u := by
        have hle := min_le_left (g - u) (d - g)
        dsimp [δ]
        nlinarith
      have hδright : δ < d - g := by
        have hle := min_le_right (g - u) (d - g)
        dsimp [δ]
        nlinarith
      refine ⟨δ, hδ, Or.inr ⟨hleft.mono ?_, hright.mono ?_⟩⟩
      · intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩
      · intro x hx
        exact ⟨hx.1, by linarith [hx.2]⟩
    have hmEq : m₁ = m := by
      rcases lt_or_gt_of_ne hmne with hmneg | hmpos
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · rw [abs_of_neg hmneg] at hmabs
          rw [abs_of_neg hm₁neg] at hm₁abs
          linarith
        · exact False.elim
            (hnofold g hug hgvlt
              (orientation_change_is_fold' (hleftAnti hmneg)
                (hrightMono hm₁pos)))
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · exact False.elim
            (hnofold g hug hgvlt
              (orientation_change_is_fold (hleftMono hmpos)
                (hrightAnti hm₁neg)))
        · rw [abs_of_pos hmpos] at hmabs
          rw [abs_of_pos hm₁pos] at hm₁abs
          linarith
    have hleft_at_g : (ψ g : ℝ) = m * g + c :=
      hglobalg g hug.le le_rfl
    have hright_at_g : (ψ g : ℝ) = m₁ * g + c₁ :=
      hformula₁ g ⟨le_rfl, hd'.2.le⟩
    have hcEq : c₁ = c := by
      rw [hmEq] at hright_at_g
      linarith
    have hdgood : d ∈ good := by
      apply Finset.mem_filter.mpr
      refine ⟨hd'.1, hug.le.trans hd'.2.le, hdv, ?_⟩
      intro x hux hxd
      by_cases hxg : x ≤ g
      · exact hglobalg x hux hxg
      · rw [hformula₁ x ⟨(lt_of_not_ge hxg).le, hxd⟩, hmEq, hcEq]
    have hdle : d ≤ g := by simpa using hgmax d hdgood
    exact (not_lt_of_ge hdle) hd'.2
  exact ⟨m, c, hmabs, fun x hx =>
    hglobalg x hx.1 (by simpa [hg_eq_v] using hx.2)⟩

/-! A bounded interval-valued path with unit absolute speed on finitely many
affine pieces must reverse orientation on every parameter interval of length
two.  The proof below uses a maximal affine extension, so it does not assume
that the supplied presentation has no redundant vertices. -/
private theorem finitePieceUnitSpeedOn_exists_interior_fold
    {ψ : ℝ → I} {t : ℝ}
    (hpieces : IsFinitePieceUnitSpeedOn ψ t (t + 2)) :
    ∃ s : ℝ, t < s ∧ s < t + 2 ∧ IsPathFoldAt ψ s := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨vertices, htV, hendV, hvertices, hcells⟩ := hpieces
  let upper := vertices.filter fun z => t < z
  have hupper : upper.Nonempty := by
    refine ⟨t + 2, Finset.mem_filter.mpr ⟨hendV, by norm_num⟩⟩
  obtain ⟨b, hb, hbmin⟩ := upper.exists_min_image id hupper
  have hb' := Finset.mem_filter.mp hb
  have htb : AdjacentInFinset vertices t b := by
    refine ⟨htV, hb'.1, hb'.2, ?_⟩
    intro z hz hzbetween
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hzbetween.1⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzbetween.2
  obtain ⟨m, c, hmabs, hformula₀⟩ := hcells htb
  have hmne : m ≠ 0 := by
    intro hm
    rw [hm, abs_zero] at hmabs
    norm_num at hmabs
  let good : Finset ℝ := vertices.filter fun z =>
    t ≤ z ∧ z ≤ t + 2 ∧
      ∀ u : ℝ, t ≤ u → u ≤ z → (ψ u : ℝ) = m * u + c
  have hbend : b ≤ t + 2 := (hvertices b hb'.1).2
  have hbgood : b ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨hb'.1, hb'.2.le, hbend, ?_⟩
    intro u htu hub
    exact hformula₀ u ⟨htu, hub⟩
  obtain ⟨g, hg, hgmax⟩ := good.exists_max_image id ⟨b, hbgood⟩
  have hgdata := Finset.mem_filter.mp hg
  have hgV : g ∈ vertices := hgdata.1
  have htg : t < g := hb'.2.trans_le (by simpa using hgmax b hbgood)
  have hgend : g ≤ t + 2 := hgdata.2.2.1
  have hglobalg := hgdata.2.2.2
  have hg_eq_end : g = t + 2 := by
    apply le_antisymm hgend
    by_contra hnot
    have hgendlt : g < t + 2 := lt_of_not_ge hnot
    let aboveG := vertices.filter fun z => g < z
    have haboveG : aboveG.Nonempty := by
      exact ⟨t + 2, Finset.mem_filter.mpr ⟨hendV, hgendlt⟩⟩
    obtain ⟨d, hd, hdmin⟩ := aboveG.exists_min_image id haboveG
    have hd' := Finset.mem_filter.mp hd
    have hgd : AdjacentInFinset vertices g d := by
      refine ⟨hgV, hd'.1, hd'.2, ?_⟩
      intro z hz hzbetween
      have hzabove : z ∈ aboveG :=
        Finset.mem_filter.mpr ⟨hz, hzbetween.1⟩
      have hdz : d ≤ z := by simpa using hdmin z hzabove
      exact (not_lt_of_ge hdz) hzbetween.2
    obtain ⟨m₁, c₁, hm₁abs, hformula₁⟩ := hcells hgd
    have hm₁ne : m₁ ≠ 0 := by
      intro hm₁
      rw [hm₁, abs_zero] at hm₁abs
      norm_num at hm₁abs
    have hdend : d ≤ t + 2 := (hvertices d hd'.1).2
    have hleftMono (hmpos : 0 < m) :
        StrictMonoOn ψ (Set.Icc t g) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg x hx.1 hx.2, hglobalg y hy.1 hy.2]
      nlinarith
    have hleftAnti (hmneg : m < 0) :
        StrictAntiOn ψ (Set.Icc t g) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hglobalg x hx.1 hx.2, hglobalg y hy.1 hy.2]
      nlinarith
    have hrightMono (hm₁pos : 0 < m₁) :
        StrictMonoOn ψ (Set.Icc g d) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ x hx, hformula₁ y hy]
      nlinarith
    have hrightAnti (hm₁neg : m₁ < 0) :
        StrictAntiOn ψ (Set.Icc g d) := by
      intro x hx y hy hxy
      apply Subtype.coe_lt_coe.mp
      rw [hformula₁ x hx, hformula₁ y hy]
      nlinarith
    have orientation_change_is_fold
        (hleft : StrictMonoOn ψ (Set.Icc t g))
        (hright : StrictAntiOn ψ (Set.Icc g d)) :
        IsPathFoldAt ψ g := by
      let δ : ℝ := min (g - t) (d - g) / 2
      have hmin : 0 < min (g - t) (d - g) :=
        lt_min (sub_pos.mpr htg) (sub_pos.mpr hd'.2)
      have hδ : 0 < δ := div_pos hmin (by norm_num)
      have hδleft : δ < g - t := by
        have hle := min_le_left (g - t) (d - g)
        dsimp [δ]
        nlinarith
      have hδright : δ < d - g := by
        have hle := min_le_right (g - t) (d - g)
        dsimp [δ]
        nlinarith
      refine ⟨δ, hδ, Or.inl ⟨hleft.mono ?_, hright.mono ?_⟩⟩
      · intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩
      · intro x hx
        exact ⟨hx.1, by linarith [hx.2]⟩
    have orientation_change_is_fold'
        (hleft : StrictAntiOn ψ (Set.Icc t g))
        (hright : StrictMonoOn ψ (Set.Icc g d)) :
        IsPathFoldAt ψ g := by
      let δ : ℝ := min (g - t) (d - g) / 2
      have hmin : 0 < min (g - t) (d - g) :=
        lt_min (sub_pos.mpr htg) (sub_pos.mpr hd'.2)
      have hδ : 0 < δ := div_pos hmin (by norm_num)
      have hδleft : δ < g - t := by
        have hle := min_le_left (g - t) (d - g)
        dsimp [δ]
        nlinarith
      have hδright : δ < d - g := by
        have hle := min_le_right (g - t) (d - g)
        dsimp [δ]
        nlinarith
      refine ⟨δ, hδ, Or.inr ⟨hleft.mono ?_, hright.mono ?_⟩⟩
      · intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩
      · intro x hx
        exact ⟨hx.1, by linarith [hx.2]⟩
    have hmEq : m₁ = m := by
      rcases lt_or_gt_of_ne hmne with hmneg | hmpos
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · rw [abs_of_neg hmneg] at hmabs
          rw [abs_of_neg hm₁neg] at hm₁abs
          linarith
        · exact False.elim
            (hnone g htg hgendlt
              (orientation_change_is_fold' (hleftAnti hmneg)
                (hrightMono hm₁pos)))
      · rcases lt_or_gt_of_ne hm₁ne with hm₁neg | hm₁pos
        · exact False.elim
            (hnone g htg hgendlt
              (orientation_change_is_fold (hleftMono hmpos)
                (hrightAnti hm₁neg)))
        · rw [abs_of_pos hmpos] at hmabs
          rw [abs_of_pos hm₁pos] at hm₁abs
          linarith
    have hleft_at_g : (ψ g : ℝ) = m * g + c :=
      hglobalg g htg.le le_rfl
    have hright_at_g : (ψ g : ℝ) = m₁ * g + c₁ :=
      hformula₁ g ⟨le_rfl, hd'.2.le⟩
    have hcEq : c₁ = c := by
      rw [hmEq] at hright_at_g
      linarith
    have hdgood : d ∈ good := by
      apply Finset.mem_filter.mpr
      refine ⟨hd'.1, htg.le.trans hd'.2.le, hdend, ?_⟩
      intro x htx hxd
      by_cases hxg : x ≤ g
      · exact hglobalg x htx hxg
      · rw [hformula₁ x ⟨(lt_of_not_ge hxg).le, hxd⟩, hmEq, hcEq]
    have hdle : d ≤ g := by simpa using hgmax d hdgood
    exact (not_lt_of_ge hdle) hd'.2
  have hglobal : ∀ x ∈ Set.Icc t (t + 2),
      (ψ x : ℝ) = m * x + c := by
    intro x hx
    exact hglobalg x hx.1 (by simpa [hg_eq_end] using hx.2)
  have hstart := hglobal t ⟨le_rfl, by norm_num⟩
  have hend := hglobal (t + 2) ⟨by norm_num, le_rfl⟩
  have hlarge : |(ψ (t + 2) : ℝ) - (ψ t : ℝ)| = 2 := by
    rw [hend, hstart]
    have hmabs' := hmabs
    rw [show m * (t + 2) + c - (m * t + c) = m * 2 by ring,
      abs_mul, hmabs']
    norm_num
  have hbounded : |(ψ (t + 2) : ℝ) - (ψ t : ℝ)| ≤ 1 := by
    rw [abs_le]
    constructor
    · have hend0 := (ψ (t + 2)).property.1
      have hstart1 := (ψ t).property.2
      linarith
    · have hstart0 := (ψ t).property.1
      have hend1 := (ψ (t + 2)).property.2
      linarith
  linarith

/-- If all positive folds occur at Markov vertices, a locally unit-speed
path cannot avoid the finite Markov set forever. -/
private theorem markovHitTimes_unbounded
    {K : Finset I} {ψ : ℝ → I}
    (hleft : leftEndpoint ∈ K) (hright : rightEndpoint ∈ K)
    (hpieces : ∀ x y : ℝ, 0 ≤ x → x < y →
      IsFinitePieceUnitSpeedOn ψ x y)
    (hfold : ∀ t : ℝ, 0 ≤ t → IsPathFoldAt ψ t → ψ t ∈ K) :
    ∀ t : ℝ, 0 ≤ t → ∃ s : ℝ, t < s ∧ s ∈ nonnegativeMarkovHitTimes K ψ := by
  intro t ht
  obtain ⟨s, hts, _hsend, hsfold⟩ :=
    finitePieceUnitSpeedOn_exists_interior_fold
      (hpieces t (t + 2) ht (by norm_num))
  exact ⟨s, hts, ht.trans hts.le, hfold s (ht.trans hts.le) hsfold⟩

private structure NextMarkovHitData
    (K : Finset I) (ψ : ℝ → I) (t : ℝ) where
  next : ℝ
  lt_next : t < next
  next_hit : next ∈ nonnegativeMarkovHitTimes K ψ
  no_hit_between : ∀ s : ℝ, t < s → s < next → ψ s ∉ K

private theorem nextMarkovHitData_exists
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    (ht : t ∈ nonnegativeMarkovHitTimes K ψ)
    (hfinite : ∀ u v : ℝ, 0 ≤ u → u ≤ v →
      (nonnegativeMarkovHitTimes K ψ ∩ Set.Icc u v).Finite)
    (hunbounded : ∀ u : ℝ, 0 ≤ u →
      ∃ v : ℝ, u < v ∧ v ∈ nonnegativeMarkovHitTimes K ψ) :
    Nonempty (NextMarkovHitData K ψ t) := by
  classical
  obtain ⟨v, htv, hvHit⟩ := hunbounded t ht.1
  let candidates : Set ℝ :=
    nonnegativeMarkovHitTimes K ψ ∩ Set.Ioc t v
  have candidates_finite : candidates.Finite := by
    apply (hfinite t v ht.1 htv.le).subset
    intro s hs
    exact ⟨hs.1, hs.2.1.le, hs.2.2⟩
  let candidateFinset : Finset ℝ := candidates_finite.toFinset
  have hvCandidate : v ∈ candidateFinset := by
    simp [candidateFinset, candidates, hvHit, htv]
  obtain ⟨next, hnext, hnextMin⟩ :=
    candidateFinset.exists_min_image id ⟨v, hvCandidate⟩
  have hnextCandidate : next ∈ candidates := by
    simpa [candidateFinset] using hnext
  refine ⟨{
    next := next
    lt_next := hnextCandidate.2.1
    next_hit := hnextCandidate.1
    no_hit_between := ?_ }⟩
  intro s hts hsnext hsK
  have hsHit : s ∈ nonnegativeMarkovHitTimes K ψ :=
    ⟨ht.1.trans hts.le, hsK⟩
  have hnextv : next ≤ v := hnextCandidate.2.2
  have hsCandidate : s ∈ candidateFinset := by
    simp [candidateFinset, candidates, hsHit, hts, hsnext.le.trans hnextv]
  have hnext_le_s : next ≤ s := by
    simpa using hnextMin s hsCandidate
  exact (not_le_of_gt hsnext) hnext_le_s

private structure MarkovRayStepData
    (K : Finset I) (ψ : ℝ → I) (t : ℝ) where
  next : ℝ
  edge : DirectedMarkovEdge K
  next_eq : next = t + edge.length
  source_eq : edge.source = ψ t
  target_eq : edge.target = ψ next
  traversal : TraversesDirectedEdge ψ t edge

/-- Between consecutive Markov hit times there is no fold, hence the path is
one literal traversal of the adjacent directed Markov edge. -/
private theorem markovRayStepData_exists
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    (ht : t ∈ nonnegativeMarkovHitTimes K ψ)
    (hpieces : ∀ x y : ℝ, 0 ≤ x → x < y →
      IsFinitePieceUnitSpeedOn ψ x y)
    (hfold : ∀ r : ℝ, 0 ≤ r → IsPathFoldAt ψ r → ψ r ∈ K)
    (next : NextMarkovHitData K ψ t) :
    Nonempty (MarkovRayStepData K ψ t) := by
  classical
  have hnofold : ∀ r : ℝ, t < r → r < next.next →
      ¬IsPathFoldAt ψ r := by
    intro r htr hrnext hrfold
    exact next.no_hit_between r htr hrnext
      (hfold r (ht.1.trans htr.le) hrfold)
  obtain ⟨m, c, hmabs, hformula⟩ :=
    finitePieceUnitSpeedOn_global_affine_of_no_interior_fold
      next.lt_next (hpieces t next.next ht.1 next.lt_next) hnofold
  have hstart : (ψ t : ℝ) = m * t + c :=
    hformula t ⟨le_rfl, next.lt_next.le⟩
  have hend : (ψ next.next : ℝ) = m * next.next + c :=
    hformula next.next ⟨next.lt_next.le, le_rfl⟩
  have hmne : m ≠ 0 := by
    intro hm
    rw [hm, abs_zero] at hmabs
    norm_num at hmabs
  rcases lt_or_gt_of_ne hmne with hmneg | hmpos
  · have hm : m = -1 := by
      rw [abs_of_neg hmneg] at hmabs
      linarith
    have htarget_source : ψ next.next < ψ t := by
      apply Subtype.coe_lt_coe.mp
      rw [hend, hstart, hm]
      linarith [next.lt_next]
    have hadjacent : FinsetAdjacent K (ψ next.next) (ψ t) := by
      refine ⟨next.next_hit.2, ht.2, htarget_source, ?_⟩
      intro z hzK hzbetween
      let s : ℝ := c - (z : ℝ)
      have hts : t < s := by
        have hzupper : (z : ℝ) < (ψ t : ℝ) := hzbetween.2
        rw [hstart, hm] at hzupper
        dsimp [s]
        linarith
      have hsnext : s < next.next := by
        have hlowerz : (ψ next.next : ℝ) < (z : ℝ) := hzbetween.1
        rw [hend, hm] at hlowerz
        dsimp [s]
        linarith
      have hψs : ψ s = z := by
        apply Subtype.ext
        rw [hformula s ⟨hts.le, hsnext.le⟩, hm]
        dsimp [s]
        ring
      exact next.no_hit_between s hts hsnext (by simpa [hψs] using hzK)
    let sourceK : ↥K := ⟨ψ t, ht.2⟩
    let targetK : ↥K := ⟨ψ next.next, next.next_hit.2⟩
    let edge : DirectedMarkovEdge K :=
      ⟨((targetK, sourceK), false), hadjacent⟩
    have hnextEq : next.next = t + edge.length := by
      dsimp [edge, DirectedMarkovEdge.length, DirectedMarkovEdge.upper,
        DirectedMarkovEdge.lower, sourceK, targetK]
      rw [hstart, hend, hm]
      ring
    have htraversal : TraversesDirectedEdge ψ t edge := by
      intro q hq0 hqlength
      have hqnext : t + q ≤ next.next := by
        rw [hnextEq]
        linarith
      change (ψ (t + q) : ℝ) = (ψ t : ℝ) - q
      rw [hformula (t + q) ⟨by linarith, hqnext⟩, hstart, hm]
      ring
    refine ⟨{
      next := next.next
      edge := edge
      next_eq := hnextEq
      source_eq := ?_
      target_eq := ?_
      traversal := htraversal }⟩
    · simp [edge, DirectedMarkovEdge.source, DirectedMarkovEdge.forward,
        DirectedMarkovEdge.upper, sourceK]
    · simp [edge, DirectedMarkovEdge.target, DirectedMarkovEdge.forward,
        DirectedMarkovEdge.lower, targetK]
  · have hm : m = 1 := by
      rw [abs_of_pos hmpos] at hmabs
      exact hmabs
    have hsource_target : ψ t < ψ next.next := by
      apply Subtype.coe_lt_coe.mp
      rw [hstart, hend, hm]
      linarith [next.lt_next]
    have hadjacent : FinsetAdjacent K (ψ t) (ψ next.next) := by
      refine ⟨ht.2, next.next_hit.2, hsource_target, ?_⟩
      intro z hzK hzbetween
      let s : ℝ := (z : ℝ) - c
      have hts : t < s := by
        have hlowerz : (ψ t : ℝ) < (z : ℝ) := hzbetween.1
        rw [hstart, hm] at hlowerz
        dsimp [s]
        linarith
      have hsnext : s < next.next := by
        have hzupper : (z : ℝ) < (ψ next.next : ℝ) := hzbetween.2
        rw [hend, hm] at hzupper
        dsimp [s]
        linarith
      have hψs : ψ s = z := by
        apply Subtype.ext
        rw [hformula s ⟨hts.le, hsnext.le⟩, hm]
        dsimp [s]
        ring
      exact next.no_hit_between s hts hsnext (by simpa [hψs] using hzK)
    let sourceK : ↥K := ⟨ψ t, ht.2⟩
    let targetK : ↥K := ⟨ψ next.next, next.next_hit.2⟩
    let edge : DirectedMarkovEdge K :=
      ⟨((sourceK, targetK), true), hadjacent⟩
    have hnextEq : next.next = t + edge.length := by
      dsimp [edge, DirectedMarkovEdge.length, DirectedMarkovEdge.upper,
        DirectedMarkovEdge.lower, sourceK, targetK]
      rw [hstart, hend, hm]
      ring
    have htraversal : TraversesDirectedEdge ψ t edge := by
      intro q hq0 hqlength
      have hqnext : t + q ≤ next.next := by
        rw [hnextEq]
        linarith
      change (ψ (t + q) : ℝ) = (ψ t : ℝ) + q
      rw [hformula (t + q) ⟨by linarith, hqnext⟩, hstart, hm]
      ring
    refine ⟨{
      next := next.next
      edge := edge
      next_eq := hnextEq
      source_eq := ?_
      target_eq := ?_
      traversal := htraversal }⟩
    · simp [edge, DirectedMarkovEdge.source, DirectedMarkovEdge.forward,
        DirectedMarkovEdge.lower, sourceK]
    · simp [edge, DirectedMarkovEdge.target, DirectedMarkovEdge.forward,
        DirectedMarkovEdge.upper, targetK]

private structure FullDirectedMarkovItineraryData
    (K : Finset I) (ψ : ℝ → I) (base : I) where
  word : Symbolic.InfiniteWord (DirectedMarkovEdge K)
  starts_at_base : (word 0).source = base
  itinerary : HasLiteralUnitSpeedItinerary ψ id
    DirectedMarkovEdge.length word

/-- Recursive choice of consecutive Markov hit times produces an infinite
literal directed-edge itinerary, with prefix metric lengths equal to the
chosen hit times. -/
private theorem fullDirectedMarkovItineraryData_exists
    {K : Finset I} {ψ : ℝ → I} {base : I}
    (hbase : base ∈ K) (hψzero : ψ 0 = base)
    (hleft : leftEndpoint ∈ K) (hright : rightEndpoint ∈ K)
    (hpieces : ∀ x y : ℝ, 0 ≤ x → x < y →
      IsFinitePieceUnitSpeedOn ψ x y)
    (hfold : ∀ t : ℝ, 0 ≤ t → IsPathFoldAt ψ t → ψ t ∈ K) :
    Nonempty (FullDirectedMarkovItineraryData K ψ base) := by
  classical
  let hitFinite : ∀ u v : ℝ, 0 ≤ u → u ≤ v →
      (nonnegativeMarkovHitTimes K ψ ∩ Set.Icc u v).Finite :=
    fun u v hu huv => markovHitTimes_finite_on_compact hu huv hpieces
  let hitUnbounded : ∀ u : ℝ, 0 ≤ u →
      ∃ v : ℝ, u < v ∧ v ∈ nonnegativeMarkovHitTimes K ψ :=
    markovHitTimes_unbounded hleft hright hpieces hfold
  let Hit := {t : ℝ // t ∈ nonnegativeMarkovHitTimes K ψ}
  have hzeroHit : 0 ∈ nonnegativeMarkovHitTimes K ψ := by
    exact ⟨le_rfl, by simpa [hψzero] using hbase⟩
  let initial : Hit := ⟨0, hzeroHit⟩
  let nextAt (x : Hit) : NextMarkovHitData K ψ x.1 :=
    Classical.choice (nextMarkovHitData_exists x.2 hitFinite hitUnbounded)
  let stepAt (x : Hit) : MarkovRayStepData K ψ x.1 :=
    Classical.choice
      (markovRayStepData_exists x.2 hpieces hfold (nextAt x))
  have edge_target_mem (e : DirectedMarkovEdge K) : e.target ∈ K := by
    cases hdir : e.forward <;>
      simp [DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.lower,
        DirectedMarkovEdge.upper]
  have step_next_hit (x : Hit) :
      (stepAt x).next ∈ nonnegativeMarkovHitTimes K ψ := by
    have hlt : (x : ℝ) < (stepAt x).next := by
      rw [(stepAt x).next_eq]
      linarith [(stepAt x).edge.length_pos]
    constructor
    · exact x.2.1.trans hlt.le
    · rw [← (stepAt x).target_eq]
      exact edge_target_mem (stepAt x).edge
  let advance (x : Hit) : Hit := ⟨(stepAt x).next, step_next_hit x⟩
  let states : ℕ → Hit :=
    Nat.rec initial (fun _ x => advance x)
  have states_zero : states 0 = initial := by rfl
  have states_succ (n : ℕ) : states (n + 1) = advance (states n) := by
    rfl
  let word : Symbolic.InfiniteWord (DirectedMarkovEdge K) :=
    fun n => (stepAt (states n)).edge
  have prefix_eq_state (n : ℕ) :
      prefixMetricLength DirectedMarkovEdge.length word n =
        (states n).1 := by
    induction n with
    | zero => simp [prefixMetricLength, states, initial]
    | succ n ih =>
        rw [prefixMetricLength, Finset.sum_range_succ]
        change prefixMetricLength DirectedMarkovEdge.length word n +
          (stepAt (states n)).edge.length = (states (n + 1)).1
        rw [ih, states_succ]
        change (states n).1 + (stepAt (states n)).edge.length =
          (stepAt (states n)).next
        exact (stepAt (states n)).next_eq.symm
  have hstarts : (word 0).source = base := by
    change (stepAt (states 0)).edge.source = base
    rw [(stepAt (states 0)).source_eq, states_zero]
    simpa [initial] using hψzero
  have hconnect : ∀ n : ℕ,
      (word n).target = (word (n + 1)).source := by
    intro n
    change (stepAt (states n)).edge.target =
      (stepAt (states (n + 1))).edge.source
    rw [(stepAt (states n)).target_eq,
      (stepAt (states (n + 1))).source_eq, states_succ]
  have htraverse : ∀ n : ℕ,
      TraversesDirectedEdge ψ
        (prefixMetricLength DirectedMarkovEdge.length word n) (word n) := by
    intro n
    rw [prefix_eq_state]
    exact (stepAt (states n)).traversal
  exact ⟨{
    word := word
    starts_at_base := hstarts
    itinerary := ⟨fun _ => rfl, hconnect, htraverse⟩ }⟩

private structure AlphabetMarkovItineraryData
    (K : Finset I) (ψ : ℝ → I) (base : I)
    (alphabet : OccurringDirectedAlphabet K) where
  word : Symbolic.InfiniteWord alphabet
  starts_at_base : (occurringEdge alphabet (word 0)).source = base
  itinerary : HasLiteralUnitSpeedItinerary ψ
    (occurringEdge alphabet) (fun e => e.1.length) word

private theorem FullDirectedMarkovItineraryData.liftToAlphabet
    {K : Finset I} {ψ : ℝ → I} {base : I}
    (raw : FullDirectedMarkovItineraryData K ψ base)
    (alphabet : OccurringDirectedAlphabet K)
    (hall : ∀ e : DirectedMarkovEdge K, e ∈ alphabet) :
    Nonempty (AlphabetMarkovItineraryData K ψ base alphabet) := by
  let lifted : Symbolic.InfiniteWord alphabet :=
    fun n => ⟨raw.word n, hall (raw.word n)⟩
  refine ⟨{
    word := lifted
    starts_at_base := ?_
    itinerary := ?_ }⟩
  · change (raw.word 0).source = base
    exact raw.starts_at_base
  · refine ⟨fun _ => rfl, ?_, ?_⟩
    · intro n
      change (raw.word n).target = (raw.word (n + 1)).source
      exact raw.itinerary.2.1 n
    · intro n
      change TraversesDirectedEdge ψ
        (prefixMetricLength DirectedMarkovEdge.length raw.word n)
        (raw.word n)
      exact raw.itinerary.2.2 n

/-- **C3.** All fold values lie in the common Markov hull and cutting at
successive vertex hits gives a literal unit-speed directed-edge itinerary. -/
theorem foldItinerary_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H) :
    Nonempty (FoldItineraryData A B F H S) := by
  have hfoldFinite := F.fold_times_locally_finite_coding
  have hfoldMarkov : ∀ t : ℝ, 0 ≤ t → IsPathFoldAt F.ray t →
      F.ray t ∈ H.vertices := by
    intro t ht hfold
    by_cases ht0 : t = 0
    · subst t
      simpa [F.ray_zero_eq_base_coding] using H.base_mem
    · exact H.postcritical_subset
        (F.fold_value_mem_jointPostcriticalSet_of_pos
          (lt_of_le_of_ne ht (Ne.symm ht0)) hfold)
  let raw : FullDirectedMarkovItineraryData H.vertices F.ray F.base :=
    Classical.choice (fullDirectedMarkovItineraryData_exists
      H.base_mem F.ray_zero_eq_base_coding H.left_mem H.right_mem
      F.locally_unit_speed hfoldMarkov)
  let lifted : AlphabetMarkovItineraryData H.vertices F.ray F.base
      S.alphabet := Classical.choice
    (raw.liftToAlphabet S.alphabet S.contains_every_directed_edge)
  refine ⟨{
    word := lifted.word
    starts_at_base := lifted.starts_at_base
    fold_values_markov := hfoldMarkov
    fold_times_locally_finite := hfoldFinite
    itinerary := ?_ }⟩
  have hlength : S.letterLength = (fun e => e.1.length) :=
    funext S.letterLength_eq_edge
  rw [hlength]
  exact lifted.itinerary

/-! ## C4: the common prolongable fixed word -/

/-! ### C4a: exact metric paths in a finite ordered Markov graph -/

private theorem directedMarkovEdge_length_eq_abs_displacement
    {K : Finset I} (e : DirectedMarkovEdge K) :
    e.length = |(e.target : ℝ) - (e.source : ℝ)| := by
  have hlt : (e.lower : ℝ) < (e.upper : ℝ) := e.2.2.2.1
  cases hdir : e.forward with
  | false =>
      simp only [DirectedMarkovEdge.length, DirectedMarkovEdge.source,
        DirectedMarkovEdge.target, hdir]
      rw [abs_of_neg (sub_neg.mpr hlt)]
      ring
  | true =>
      simp only [DirectedMarkovEdge.length, DirectedMarkovEdge.source,
        DirectedMarkovEdge.target, hdir]
      rw [abs_of_pos (sub_pos.mpr hlt)]

private theorem directedEdgePathStartsAt_cons_iff
    {K : Finset I} {e : DirectedMarkovEdge K}
    {rest : LiteralDirectedEdgeWord K} {x : I} :
    DirectedEdgePathStartsAt (e :: rest) x ↔ e.source = x := by
  constructor
  · rintro ⟨e', rest', heq, hsource⟩
    injection heq with he _
    simpa [he] using hsource
  · intro hsource
    exact ⟨e, rest, rfl, hsource⟩

private theorem directedEdgePathEndsAt_singleton_iff
    {K : Finset I} {e : DirectedMarkovEdge K} {y : I} :
    DirectedEdgePathEndsAt [e] y ↔ e.target = y := by
  constructor
  · rintro ⟨init, last, heq, htarget⟩
    have hlength := congrArg List.length heq
    have hinitLength : init.length = 0 := by
      simpa using hlength
    have hinit : init = [] := List.eq_nil_of_length_eq_zero hinitLength
    subst init
    have heLast : e = last := by simpa using heq
    rw [heLast]
    exact htarget
  · intro htarget
    exact ⟨[], e, rfl, htarget⟩

private theorem directedEdgePathEndsAt_tail_of_cons_cons
    {K : Finset I} {e f : DirectedMarkovEdge K}
    {rest : LiteralDirectedEdgeWord K} {y : I}
    (hend : DirectedEdgePathEndsAt (e :: f :: rest) y) :
    DirectedEdgePathEndsAt (f :: rest) y := by
  rcases hend with ⟨init, last, heq, htarget⟩
  cases init with
  | nil => simp at heq
  | cons first init =>
      simp only [List.cons_append] at heq
      injection heq with _ htail
      exact ⟨init, last, htail, htarget⟩

/-- Every literal directed path has metric length at least the distance
between its displayed endpoints. -/
private theorem literalDirectedEdgePath_endpointDistance_le_metric
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y) :
    |(y : ℝ) - (x : ℝ)| ≤
      wordMetricLength DirectedMarkovEdge.length w := by
  induction w generalizing x y with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons e rest ih =>
      have hsource : e.source = x :=
        directedEdgePathStartsAt_cons_iff.mp hstart
      cases rest with
      | nil =>
          have htarget : e.target = y :=
            directedEdgePathEndsAt_singleton_iff.mp hend
          simp only [wordMetricLength, List.map_cons, List.map_nil,
            List.sum_cons, List.sum_nil, add_zero]
          simpa [hsource, htarget] using
            (directedMarkovEdge_length_eq_abs_displacement e).ge
      | cons f rest =>
          have hpathData : e.target = f.source ∧
              IsLiteralDirectedEdgePath (f :: rest) := by
            simpa [IsLiteralDirectedEdgePath] using hpath
          have htailStart :
              DirectedEdgePathStartsAt (f :: rest) e.target :=
            directedEdgePathStartsAt_cons_iff.mpr hpathData.1.symm
          have htailEnd : DirectedEdgePathEndsAt (f :: rest) y :=
            directedEdgePathEndsAt_tail_of_cons_cons hend
          have htailBound := ih hpathData.2 htailStart htailEnd
          calc
            |(y : ℝ) - (x : ℝ)| =
                |((e.target : ℝ) - (x : ℝ)) +
                  ((y : ℝ) - (e.target : ℝ))| := by ring_nf
            _ ≤ |(e.target : ℝ) - (x : ℝ)| +
                |(y : ℝ) - (e.target : ℝ)| := abs_add_le _ _
            _ ≤ e.length +
                wordMetricLength DirectedMarkovEdge.length (f :: rest) := by
              apply add_le_add
              · simpa [hsource] using
                  (directedMarkovEdge_length_eq_abs_displacement e).ge
              · exact htailBound
            _ = wordMetricLength DirectedMarkovEdge.length
                (e :: f :: rest) := by
              simp [wordMetricLength]

private theorem literalDirectedEdgePath_displacement_sum
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y) :
    (w.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum =
      (y : ℝ) - (x : ℝ) := by
  induction w generalizing x y with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons e rest ih =>
      have hsource : e.source = x :=
        directedEdgePathStartsAt_cons_iff.mp hstart
      cases rest with
      | nil =>
          have htarget : e.target = y :=
            directedEdgePathEndsAt_singleton_iff.mp hend
          simp [hsource, htarget]
      | cons f rest =>
          have hpathData : e.target = f.source ∧
              IsLiteralDirectedEdgePath (f :: rest) := by
            simpa [IsLiteralDirectedEdgePath] using hpath
          have htailStart :
              DirectedEdgePathStartsAt (f :: rest) e.target :=
            directedEdgePathStartsAt_cons_iff.mpr hpathData.1.symm
          have htailEnd : DirectedEdgePathEndsAt (f :: rest) y :=
            directedEdgePathEndsAt_tail_of_cons_cons hend
          rw [List.map_cons, List.sum_cons,
            ih hpathData.2 htailStart htailEnd]
          rw [hsource]
          ring

private theorem wordMetricLength_eq_sum_abs_displacement
    {K : Finset I} (w : LiteralDirectedEdgeWord K) :
    wordMetricLength DirectedMarkovEdge.length w =
      (w.map fun e => |(e.target : ℝ) - (e.source : ℝ)|).sum := by
  induction w with
  | nil => rfl
  | cons e rest ih =>
      simp only [wordMetricLength] at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [directedMarkovEdge_length_eq_abs_displacement, ih]

private theorem list_sum_le_sum_abs (values : List ℝ) :
    values.sum ≤ (values.map abs).sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.sum_cons, List.map_cons]
      exact add_le_add (le_abs_self value) ih

private theorem list_neg_sum_le_sum_abs (values : List ℝ) :
    -values.sum ≤ (values.map abs).sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.sum_cons, List.map_cons]
      have hvalue : -value ≤ |value| := neg_le_abs value
      linarith

private theorem list_forall_nonneg_of_sum_abs_eq_sum
    {values : List ℝ}
    (h : (values.map abs).sum = values.sum) :
    ∀ value ∈ values, 0 ≤ value := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.map_cons, List.sum_cons] at h
      have hrest := list_sum_le_sum_abs rest
      have hvalue : value ≤ |value| := le_abs_self value
      have hvalueEq : |value| = value := by linarith
      have hrestEq : (rest.map abs).sum = rest.sum := by linarith
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact abs_eq_self.mp hvalueEq
      · exact ih hrestEq z hz

private theorem list_forall_nonpos_of_sum_abs_eq_neg_sum
    {values : List ℝ}
    (h : (values.map abs).sum = -values.sum) :
    ∀ value ∈ values, value ≤ 0 := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.map_cons, List.sum_cons] at h
      have hrest := list_neg_sum_le_sum_abs rest
      have hvalue : -value ≤ |value| := neg_le_abs value
      have hvalueEq : |value| = -value := by linarith
      have hrestEq : (rest.map abs).sum = -rest.sum := by linarith
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact abs_eq_neg_self.mp hvalueEq
      · exact ih hrestEq z hz

private theorem directedMarkovEdge_source_mem
    {K : Finset I} (e : DirectedMarkovEdge K) : e.source ∈ K := by
  cases hdir : e.forward <;>
    simp [DirectedMarkovEdge.source, hdir, DirectedMarkovEdge.lower,
      DirectedMarkovEdge.upper]

private theorem directedMarkovEdge_target_mem
    {K : Finset I} (e : DirectedMarkovEdge K) : e.target ∈ K := by
  cases hdir : e.forward <;>
    simp [DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.lower,
      DirectedMarkovEdge.upper]

private theorem directedMarkovEdge_eq_of_source_eq_target_eq
    {K : Finset I} {e f : DirectedMarkovEdge K}
    (hsource : e.source = f.source) (htarget : e.target = f.target) :
    e = f := by
  have heOrder : e.source ≠ e.target := by
    intro h
    have hlen := directedMarkovEdge_length_eq_abs_displacement e
    rw [h, sub_self, abs_zero] at hlen
    exact e.length_pos.ne' hlen
  cases he : e.forward <;> cases hf : f.forward
  · have helower : e.lower = f.lower := by
      simpa [DirectedMarkovEdge.target, he, hf] using htarget
    have heupper : e.upper = f.upper := by
      simpa [DirectedMarkovEdge.source, he, hf] using hsource
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext helower
      · exact Subtype.ext heupper
    · exact he.trans hf.symm
  · have hedec : e.target < e.source := by
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, he] using
        e.2.2.2.1
    have hfinc : f.source < f.target := by
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hf] using
        f.2.2.2.1
    have hbad : e.source < e.target := by
      calc
        e.source = f.source := hsource
        _ < f.target := hfinc
        _ = e.target := htarget.symm
    exact (not_lt_of_ge hedec.le hbad).elim
  · have heinc : e.source < e.target := by
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, he] using
        e.2.2.2.1
    have hfdec : f.target < f.source := by
      simpa [DirectedMarkovEdge.source, DirectedMarkovEdge.target, hf] using
        f.2.2.2.1
    have hbad : e.target < e.source := by
      calc
        e.target = f.target := htarget
        _ < f.source := hfdec
        _ = e.source := hsource.symm
    exact (not_lt_of_ge heinc.le hbad).elim
  · have helower : e.lower = f.lower := by
      simpa [DirectedMarkovEdge.source, he, hf] using hsource
    have heupper : e.upper = f.upper := by
      simpa [DirectedMarkovEdge.target, he, hf] using htarget
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext helower
      · exact Subtype.ext heupper
    · exact he.trans hf.symm

private theorem list_sum_nonneg_of_forall_nonneg
    (values : List ℝ) (hnonneg : ∀ value ∈ values, 0 ≤ value) :
    0 ≤ values.sum := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [List.sum_cons]
      have hv := hnonneg value (by simp)
      have hr := ih (fun z hz => hnonneg z (by simp [hz]))
      linarith

private theorem list_sum_pos_of_forall_pos_of_ne_nil
    {values : List ℝ} (hne : values ≠ [])
    (hpos : ∀ value ∈ values, 0 < value) : 0 < values.sum := by
  induction values with
  | nil => exact (hne rfl).elim
  | cons value rest ih =>
      simp only [List.sum_cons]
      have hv := hpos value (by simp)
      have hrest : 0 ≤ rest.sum :=
        list_sum_nonneg_of_forall_nonneg rest
          (fun z hz => (hpos z (by simp [hz])).le)
      linarith

private theorem edgeDisplacement_sum_pos
    {K : Finset I} {w : LiteralDirectedEdgeWord K} (hne : w ≠ [])
    (hpos : ∀ e ∈ w, 0 < (e.target : ℝ) - (e.source : ℝ)) :
    0 < (w.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
  apply list_sum_pos_of_forall_pos_of_ne_nil
  · simpa using hne
  · intro value hvalue
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvalue
    exact hpos e he

private theorem edgeDisplacement_sum_neg
    {K : Finset I} {w : LiteralDirectedEdgeWord K} (hne : w ≠ [])
    (hneg : ∀ e ∈ w, (e.target : ℝ) - (e.source : ℝ) < 0) :
    (w.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum < 0 := by
  have hpos : 0 <
      ((w.map fun e => (e.source : ℝ) - (e.target : ℝ))).sum := by
    apply list_sum_pos_of_forall_pos_of_ne_nil
    · simpa using hne
    · intro value hvalue
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvalue
      exact sub_pos.mpr (sub_neg.mp (hneg e he))
  have hnegSum :
      (w.map fun e => (e.source : ℝ) - (e.target : ℝ)).sum =
        -(w.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
    clear hne hneg hpos
    induction w with
    | nil => simp
    | cons e rest ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  rw [hnegSum] at hpos
  linarith

private theorem literalDirectedEdgePath_eq_of_positiveDisplacements
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x y : I}
    (huPath : IsLiteralDirectedEdgePath u)
    (hvPath : IsLiteralDirectedEdgePath v)
    (huStart : DirectedEdgePathStartsAt u x)
    (hvStart : DirectedEdgePathStartsAt v x)
    (huEnd : DirectedEdgePathEndsAt u y)
    (hvEnd : DirectedEdgePathEndsAt v y)
    (huPos : ∀ e ∈ u, 0 < (e.target : ℝ) - (e.source : ℝ))
    (hvPos : ∀ e ∈ v, 0 < (e.target : ℝ) - (e.source : ℝ)) :
    u = v := by
  induction u generalizing v x y with
  | nil => simp [IsLiteralDirectedEdgePath] at huPath
  | cons e us ih =>
      cases v with
      | nil => simp [IsLiteralDirectedEdgePath] at hvPath
      | cons f vs =>
          have heSource : e.source = x :=
            directedEdgePathStartsAt_cons_iff.mp huStart
          have hfSource : f.source = x :=
            directedEdgePathStartsAt_cons_iff.mp hvStart
          have hePos := huPos e (by simp)
          have hfPos := hvPos f (by simp)
          have heForward : e.forward = true := by
            cases hdir : e.forward with
            | false =>
                have hdec : (e.target : ℝ) < (e.source : ℝ) := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, hdir] using e.2.2.2.1
                linarith
            | true => rfl
          have hfForward : f.forward = true := by
            cases hdir : f.forward with
            | false =>
                have hdec : (f.target : ℝ) < (f.source : ℝ) := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, hdir] using f.2.2.2.1
                linarith
            | true => rfl
          have heTargetFromX : (x : ℝ) < (e.target : ℝ) := by
            rw [← heSource]
            linarith
          have hfTargetFromX : (x : ℝ) < (f.target : ℝ) := by
            rw [← hfSource]
            linarith
          have heLower : e.lower = x := by
            simpa [DirectedMarkovEdge.source, heForward] using heSource
          have heUpper : e.upper = e.target := by
            simp [DirectedMarkovEdge.target, heForward]
          have hfLower : f.lower = x := by
            simpa [DirectedMarkovEdge.source, hfForward] using hfSource
          have hfUpper : f.upper = f.target := by
            simp [DirectedMarkovEdge.target, hfForward]
          have htarget : e.target = f.target := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have hbetween : f.lower < e.target ∧ e.target < f.upper := by
                rw [hfLower, hfUpper]
                exact ⟨heTargetFromX, hlt⟩
              exact f.2.2.2.2 e.target
                (directedMarkovEdge_target_mem e) hbetween
            · have hbetween : e.lower < f.target ∧ f.target < e.upper := by
                rw [heLower, heUpper]
                exact ⟨hfTargetFromX, hgt⟩
              exact e.2.2.2.2 f.target
                (directedMarkovEdge_target_mem f) hbetween
          have hef : e = f :=
            directedMarkovEdge_eq_of_source_eq_target_eq
              (heSource.trans hfSource.symm) htarget
          subst f
          cases us with
          | nil =>
              cases vs with
              | nil => rfl
              | cons g gs =>
                  have heTarget : e.target = y :=
                    directedEdgePathEndsAt_singleton_iff.mp huEnd
                  have hvData : e.target = g.source ∧
                      IsLiteralDirectedEdgePath (g :: gs) := by
                    simpa [IsLiteralDirectedEdgePath] using hvPath
                  have htailStart :
                      DirectedEdgePathStartsAt (g :: gs) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr hvData.1.symm
                  have htailEnd : DirectedEdgePathEndsAt (g :: gs) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons hvEnd
                  have hsum := literalDirectedEdgePath_displacement_sum
                    hvData.2 htailStart htailEnd
                  have hsumPos := edgeDisplacement_sum_pos
                    (w := g :: gs) (by simp)
                    (fun d hd => hvPos d (by simp [hd]))
                  have hsumZero :
                      (List.map (fun e => (e.target : ℝ) - (e.source : ℝ))
                        (g :: gs)).sum = 0 := by
                    rw [hsum, heTarget]
                    simp
                  linarith
          | cons e' es =>
              cases vs with
              | nil =>
                  have heTarget : e.target = y :=
                    directedEdgePathEndsAt_singleton_iff.mp hvEnd
                  have huData : e.target = e'.source ∧
                      IsLiteralDirectedEdgePath (e' :: es) := by
                    simpa [IsLiteralDirectedEdgePath] using huPath
                  have htailStart :
                      DirectedEdgePathStartsAt (e' :: es) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr huData.1.symm
                  have htailEnd : DirectedEdgePathEndsAt (e' :: es) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons huEnd
                  have hsum := literalDirectedEdgePath_displacement_sum
                    huData.2 htailStart htailEnd
                  have hsumPos := edgeDisplacement_sum_pos
                    (w := e' :: es) (by simp)
                    (fun d hd => huPos d (by simp [hd]))
                  have hsumZero :
                      (List.map (fun e => (e.target : ℝ) - (e.source : ℝ))
                        (e' :: es)).sum = 0 := by
                    rw [hsum, heTarget]
                    simp
                  linarith
              | cons f' fs =>
                  have huData : e.target = e'.source ∧
                      IsLiteralDirectedEdgePath (e' :: es) := by
                    simpa [IsLiteralDirectedEdgePath] using huPath
                  have hvData : e.target = f'.source ∧
                      IsLiteralDirectedEdgePath (f' :: fs) := by
                    simpa [IsLiteralDirectedEdgePath] using hvPath
                  have htailUStart :
                      DirectedEdgePathStartsAt (e' :: es) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr huData.1.symm
                  have htailVStart :
                      DirectedEdgePathStartsAt (f' :: fs) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr hvData.1.symm
                  have htailUEnd : DirectedEdgePathEndsAt (e' :: es) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons huEnd
                  have htailVEnd : DirectedEdgePathEndsAt (f' :: fs) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons hvEnd
                  have htailEq := ih huData.2 hvData.2 htailUStart
                    htailVStart htailUEnd htailVEnd
                    (fun d hd => huPos d (by simp [hd]))
                    (fun d hd => hvPos d (by simp [hd]))
                  rw [htailEq]

private theorem literalDirectedEdgePath_eq_of_negativeDisplacements
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x y : I}
    (huPath : IsLiteralDirectedEdgePath u)
    (hvPath : IsLiteralDirectedEdgePath v)
    (huStart : DirectedEdgePathStartsAt u x)
    (hvStart : DirectedEdgePathStartsAt v x)
    (huEnd : DirectedEdgePathEndsAt u y)
    (hvEnd : DirectedEdgePathEndsAt v y)
    (huNeg : ∀ e ∈ u, (e.target : ℝ) - (e.source : ℝ) < 0)
    (hvNeg : ∀ e ∈ v, (e.target : ℝ) - (e.source : ℝ) < 0) :
    u = v := by
  induction u generalizing v x y with
  | nil => simp [IsLiteralDirectedEdgePath] at huPath
  | cons e us ih =>
      cases v with
      | nil => simp [IsLiteralDirectedEdgePath] at hvPath
      | cons f vs =>
          have heSource : e.source = x :=
            directedEdgePathStartsAt_cons_iff.mp huStart
          have hfSource : f.source = x :=
            directedEdgePathStartsAt_cons_iff.mp hvStart
          have heNeg := huNeg e (by simp)
          have hfNeg := hvNeg f (by simp)
          have heBackward : e.forward = false := by
            cases hdir : e.forward with
            | false => rfl
            | true =>
                have hinc : (e.source : ℝ) < (e.target : ℝ) := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, hdir] using e.2.2.2.1
                linarith
          have hfBackward : f.forward = false := by
            cases hdir : f.forward with
            | false => rfl
            | true =>
                have hinc : (f.source : ℝ) < (f.target : ℝ) := by
                  simpa [DirectedMarkovEdge.source,
                    DirectedMarkovEdge.target, hdir] using f.2.2.2.1
                linarith
          have heTargetBelowX : (e.target : ℝ) < (x : ℝ) := by
            rw [← heSource]
            linarith
          have hfTargetBelowX : (f.target : ℝ) < (x : ℝ) := by
            rw [← hfSource]
            linarith
          have heLower : e.lower = e.target := by
            simp [DirectedMarkovEdge.target, heBackward]
          have heUpper : e.upper = x := by
            simpa [DirectedMarkovEdge.source, heBackward] using heSource
          have hfLower : f.lower = f.target := by
            simp [DirectedMarkovEdge.target, hfBackward]
          have hfUpper : f.upper = x := by
            simpa [DirectedMarkovEdge.source, hfBackward] using hfSource
          have htarget : e.target = f.target := by
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have hbetween : e.lower < f.target ∧ f.target < e.upper := by
                rw [heLower, heUpper]
                exact ⟨hlt, hfTargetBelowX⟩
              exact e.2.2.2.2 f.target
                (directedMarkovEdge_target_mem f) hbetween
            · have hbetween : f.lower < e.target ∧ e.target < f.upper := by
                rw [hfLower, hfUpper]
                exact ⟨hgt, heTargetBelowX⟩
              exact f.2.2.2.2 e.target
                (directedMarkovEdge_target_mem e) hbetween
          have hef : e = f :=
            directedMarkovEdge_eq_of_source_eq_target_eq
              (heSource.trans hfSource.symm) htarget
          subst f
          cases us with
          | nil =>
              cases vs with
              | nil => rfl
              | cons g gs =>
                  have heTarget : e.target = y :=
                    directedEdgePathEndsAt_singleton_iff.mp huEnd
                  have hvData : e.target = g.source ∧
                      IsLiteralDirectedEdgePath (g :: gs) := by
                    simpa [IsLiteralDirectedEdgePath] using hvPath
                  have htailStart :
                      DirectedEdgePathStartsAt (g :: gs) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr hvData.1.symm
                  have htailEnd : DirectedEdgePathEndsAt (g :: gs) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons hvEnd
                  have hsum := literalDirectedEdgePath_displacement_sum
                    hvData.2 htailStart htailEnd
                  have hsumNeg := edgeDisplacement_sum_neg
                    (w := g :: gs) (by simp)
                    (fun d hd => hvNeg d (by simp [hd]))
                  have hsumZero :
                      (List.map (fun e => (e.target : ℝ) - (e.source : ℝ))
                        (g :: gs)).sum = 0 := by
                    rw [hsum, heTarget]
                    simp
                  linarith
          | cons e' es =>
              cases vs with
              | nil =>
                  have heTarget : e.target = y :=
                    directedEdgePathEndsAt_singleton_iff.mp hvEnd
                  have huData : e.target = e'.source ∧
                      IsLiteralDirectedEdgePath (e' :: es) := by
                    simpa [IsLiteralDirectedEdgePath] using huPath
                  have htailStart :
                      DirectedEdgePathStartsAt (e' :: es) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr huData.1.symm
                  have htailEnd : DirectedEdgePathEndsAt (e' :: es) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons huEnd
                  have hsum := literalDirectedEdgePath_displacement_sum
                    huData.2 htailStart htailEnd
                  have hsumNeg := edgeDisplacement_sum_neg
                    (w := e' :: es) (by simp)
                    (fun d hd => huNeg d (by simp [hd]))
                  have hsumZero :
                      (List.map (fun e => (e.target : ℝ) - (e.source : ℝ))
                        (e' :: es)).sum = 0 := by
                    rw [hsum, heTarget]
                    simp
                  linarith
              | cons f' fs =>
                  have huData : e.target = e'.source ∧
                      IsLiteralDirectedEdgePath (e' :: es) := by
                    simpa [IsLiteralDirectedEdgePath] using huPath
                  have hvData : e.target = f'.source ∧
                      IsLiteralDirectedEdgePath (f' :: fs) := by
                    simpa [IsLiteralDirectedEdgePath] using hvPath
                  have htailUStart :
                      DirectedEdgePathStartsAt (e' :: es) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr huData.1.symm
                  have htailVStart :
                      DirectedEdgePathStartsAt (f' :: fs) e.target :=
                    directedEdgePathStartsAt_cons_iff.mpr hvData.1.symm
                  have htailUEnd : DirectedEdgePathEndsAt (e' :: es) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons huEnd
                  have htailVEnd : DirectedEdgePathEndsAt (f' :: fs) y :=
                    directedEdgePathEndsAt_tail_of_cons_cons hvEnd
                  have htailEq := ih huData.2 hvData.2 htailUStart
                    htailVStart htailUEnd htailVEnd
                    (fun d hd => huNeg d (by simp [hd]))
                    (fun d hd => hvNeg d (by simp [hd]))
                  rw [htailEq]

/-- Equality in the path-variation bound eliminates every backtrack.  In a
finite linearly ordered Markov graph, the resulting minimal literal path
between fixed directed endpoints is unique. -/
private theorem literalDirectedEdgePath_eq_of_metricMinimal
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x y : I}
    (huPath : IsLiteralDirectedEdgePath u)
    (hvPath : IsLiteralDirectedEdgePath v)
    (huStart : DirectedEdgePathStartsAt u x)
    (hvStart : DirectedEdgePathStartsAt v x)
    (huEnd : DirectedEdgePathEndsAt u y)
    (hvEnd : DirectedEdgePathEndsAt v y)
    (huMetric : wordMetricLength DirectedMarkovEdge.length u =
      |(y : ℝ) - (x : ℝ)|)
    (hvMetric : wordMetricLength DirectedMarkovEdge.length v =
      |(y : ℝ) - (x : ℝ)|) :
    u = v := by
  rcases lt_trichotomy (x : ℝ) (y : ℝ) with hxy | hxy | hyx
  · have huSum := literalDirectedEdgePath_displacement_sum
      huPath huStart huEnd
    have hvSum := literalDirectedEdgePath_displacement_sum
      hvPath hvStart hvEnd
    have huAbsEq :
        (u.map fun e => |(e.target : ℝ) - (e.source : ℝ)|).sum =
          (u.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
      rw [← wordMetricLength_eq_sum_abs_displacement u, huMetric,
        abs_of_pos (sub_pos.mpr hxy), huSum]
    have hvAbsEq :
        (v.map fun e => |(e.target : ℝ) - (e.source : ℝ)|).sum =
          (v.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
      rw [← wordMetricLength_eq_sum_abs_displacement v, hvMetric,
        abs_of_pos (sub_pos.mpr hxy), hvSum]
    have huNonneg := list_forall_nonneg_of_sum_abs_eq_sum
      (values := u.map fun e => (e.target : ℝ) - (e.source : ℝ))
      (by simpa [List.map_map] using huAbsEq)
    have hvNonneg := list_forall_nonneg_of_sum_abs_eq_sum
      (values := v.map fun e => (e.target : ℝ) - (e.source : ℝ))
      (by simpa [List.map_map] using hvAbsEq)
    have huPos : ∀ e ∈ u,
        0 < (e.target : ℝ) - (e.source : ℝ) := by
      intro e he
      have hnonneg := huNonneg
        ((e.target : ℝ) - (e.source : ℝ)) (by
          exact List.mem_map.mpr ⟨e, he, rfl⟩)
      have hne : (e.target : ℝ) - (e.source : ℝ) ≠ 0 := by
        intro hzero
        have hlength := directedMarkovEdge_length_eq_abs_displacement e
        rw [hzero, abs_zero] at hlength
        exact e.length_pos.ne' hlength
      exact lt_of_le_of_ne hnonneg hne.symm
    have hvPos : ∀ e ∈ v,
        0 < (e.target : ℝ) - (e.source : ℝ) := by
      intro e he
      have hnonneg := hvNonneg
        ((e.target : ℝ) - (e.source : ℝ)) (by
          exact List.mem_map.mpr ⟨e, he, rfl⟩)
      have hne : (e.target : ℝ) - (e.source : ℝ) ≠ 0 := by
        intro hzero
        have hlength := directedMarkovEdge_length_eq_abs_displacement e
        rw [hzero, abs_zero] at hlength
        exact e.length_pos.ne' hlength
      exact lt_of_le_of_ne hnonneg hne.symm
    exact literalDirectedEdgePath_eq_of_positiveDisplacements
      huPath hvPath huStart hvStart huEnd hvEnd huPos hvPos
  · have huNe : u ≠ [] := by
      intro hu
      subst u
      simp [IsLiteralDirectedEdgePath] at huPath
    have huMetricPos : 0 < wordMetricLength DirectedMarkovEdge.length u := by
      apply list_sum_pos_of_forall_pos_of_ne_nil
      · simpa [wordMetricLength] using huNe
      · intro value hvalue
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvalue
        exact e.length_pos
    have huMetricZero :
        wordMetricLength DirectedMarkovEdge.length u = 0 := by
      rw [huMetric, hxy, sub_self, abs_zero]
    linarith
  · have huSum := literalDirectedEdgePath_displacement_sum
      huPath huStart huEnd
    have hvSum := literalDirectedEdgePath_displacement_sum
      hvPath hvStart hvEnd
    have huAbsEq :
        (u.map fun e => |(e.target : ℝ) - (e.source : ℝ)|).sum =
          -(u.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
      rw [← wordMetricLength_eq_sum_abs_displacement u, huMetric,
        abs_of_neg (sub_neg.mpr hyx), huSum]
    have hvAbsEq :
        (v.map fun e => |(e.target : ℝ) - (e.source : ℝ)|).sum =
          -(v.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
      rw [← wordMetricLength_eq_sum_abs_displacement v, hvMetric,
        abs_of_neg (sub_neg.mpr hyx), hvSum]
    have huNonpos := list_forall_nonpos_of_sum_abs_eq_neg_sum
      (values := u.map fun e => (e.target : ℝ) - (e.source : ℝ))
      (by simpa [List.map_map] using huAbsEq)
    have hvNonpos := list_forall_nonpos_of_sum_abs_eq_neg_sum
      (values := v.map fun e => (e.target : ℝ) - (e.source : ℝ))
      (by simpa [List.map_map] using hvAbsEq)
    have huNeg : ∀ e ∈ u,
        (e.target : ℝ) - (e.source : ℝ) < 0 := by
      intro e he
      have hnonpos := huNonpos
        ((e.target : ℝ) - (e.source : ℝ)) (by
          exact List.mem_map.mpr ⟨e, he, rfl⟩)
      have hne : (e.target : ℝ) - (e.source : ℝ) ≠ 0 := by
        intro hzero
        have hlength := directedMarkovEdge_length_eq_abs_displacement e
        rw [hzero, abs_zero] at hlength
        exact e.length_pos.ne' hlength
      exact lt_of_le_of_ne hnonpos hne
    have hvNeg : ∀ e ∈ v,
        (e.target : ℝ) - (e.source : ℝ) < 0 := by
      intro e he
      have hnonpos := hvNonpos
        ((e.target : ℝ) - (e.source : ℝ)) (by
          exact List.mem_map.mpr ⟨e, he, rfl⟩)
      have hne : (e.target : ℝ) - (e.source : ℝ) ≠ 0 := by
        intro hzero
        have hlength := directedMarkovEdge_length_eq_abs_displacement e
        rw [hzero, abs_zero] at hlength
        exact e.length_pos.ne' hlength
      exact lt_of_le_of_ne hnonpos hne
    exact literalDirectedEdgePath_eq_of_negativeDisplacements
      huPath hvPath huStart hvStart huEnd hvEnd huNeg hvNeg

/-! ### C4b: substitution images are the unique minimal image paths -/

/-- The model endpoints and the exact constant-slope metric law make each
substitution image a minimal literal path between the images of the source
edge endpoints. -/
private theorem modeledSubstitutionImage_is_metricMinimal
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {σ : Symbolic.Substitution alphabet} {length : alphabet → ℝ}
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet σ)
    (hlength : ∀ e, length e = e.1.length)
    (hmetric : SubstitutionScalesLetterLengths σ length scale)
    (e : alphabet) :
    IsLiteralDirectedEdgePath (geometricEdgeWord alphabet (σ e)) ∧
      DirectedEdgePathStartsAt (geometricEdgeWord alphabet (σ e))
        (T e.1.source) ∧
      DirectedEdgePathEndsAt (geometricEdgeWord alphabet (σ e))
        (T e.1.target) ∧
      wordMetricLength DirectedMarkovEdge.length
          (geometricEdgeWord alphabet (σ e)) =
        |(T e.1.target : ℝ) - (T e.1.source : ℝ)| := by
  have hmodel := hmodels e
  refine ⟨hmodel.1, hmodel.2.1, hmodel.2.2, ?_⟩
  calc
    wordMetricLength DirectedMarkovEdge.length
        (geometricEdgeWord alphabet (σ e)) =
        wordMetricLength length (σ e) := by
      simp only [wordMetricLength, geometricEdgeWord, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro letter hletter
      exact (hlength letter).symm
    _ = scale * length e := hmetric e
    _ = scale * e.1.length := by rw [hlength e]
    _ = |(T e.1.target : ℝ) - (T e.1.source : ℝ)| :=
      (markovEdge_image_distance_coding hmarkov hslope e.1).symm

/-! ### C4c: parsing substituted one-sided words at block boundaries -/

private theorem mapInfinite_append_stream_coding
    {α : Type*} (σ : Symbolic.Substitution α)
    (finitePrefix : Symbolic.Word α) (word : Symbolic.InfiniteWord α) :
    σ.mapInfinite (finitePrefix ++ₛ word) =
      σ.mapWord finitePrefix ++ₛ σ.mapInfinite word := by
  induction finitePrefix with
  | nil => rfl
  | cons letter rest ih =>
      rw [Stream'.cons_append_stream, σ.mapInfinite_eq_append_first_image,
        Stream'.head_cons, Stream'.tail_cons, ih, σ.mapWord_cons,
        Stream'.append_append_stream]

/-- The first `n` input blocks of an infinite substituted word are exactly
the finite substitution of the first `n` input letters. -/
private theorem mapInfinite_take_substitutionPrefix
    {α : Type*} (σ : Symbolic.Substitution α)
    (word : Symbolic.InfiniteWord α) (n : ℕ) :
    (σ.mapInfinite word).take (σ.mapWord (word.take n)).length =
      σ.mapWord (word.take n) := by
  let image := σ.mapWord (word.take n)
  have hwhole : image ++ₛ σ.mapInfinite (word.drop n) =
      σ.mapInfinite word := by
    calc
      image ++ₛ σ.mapInfinite (word.drop n) =
          σ.mapInfinite (word.take n ++ₛ word.drop n) :=
        (mapInfinite_append_stream_coding σ _ _).symm
      _ = σ.mapInfinite word := by rw [Stream'.append_take_drop]
  rw [← hwhole]
  simpa [image] using Stream'.take_append_of_le_length
    (x := image) (a := σ.mapInfinite (word.drop n))
    (n := image.length) le_rfl

private theorem prefixMetricLength_eq_wordMetricLength_take_coding
    {α : Type*} (length : α → ℝ)
    (word : Symbolic.InfiniteWord α) (n : ℕ) :
    prefixMetricLength length word n =
      wordMetricLength length (word.take n) := by
  induction n with
  | zero => simp [prefixMetricLength, wordMetricLength]
  | succ n ih =>
      rw [prefixMetricLength, Finset.sum_range_succ]
      rw [prefixMetricLength] at ih
      rw [Stream'.take_succ', wordMetricLength, List.map_append,
        List.sum_append, ih]
      simp [wordMetricLength, Stream'.get]

private theorem wordMetricLength_mapWord_of_scales_coding
    {α : Type*} {σ : Symbolic.Substitution α} {length : α → ℝ}
    {scale : ℝ} (hmetric : SubstitutionScalesLetterLengths σ length scale)
    (w : Symbolic.Word α) :
    wordMetricLength length (σ.mapWord w) =
      scale * wordMetricLength length w := by
  induction w with
  | nil => simp [wordMetricLength]
  | cons letter rest ih =>
      rw [Symbolic.Substitution.mapWord_cons,
        wordMetricLength_append_coding, hmetric letter, ih]
      simp [wordMetricLength, mul_add]

/-- Exact letter-length scaling places the `n`-th substituted block boundary
at the scaled metric time of the `n`-th source boundary. -/
private theorem prefixMetricLength_mapInfinite_substitutionBoundary
    {α : Type*} {σ : Symbolic.Substitution α}
    {length : α → ℝ} {scale : ℝ}
    (hmetric : SubstitutionScalesLetterLengths σ length scale)
    (word : Symbolic.InfiniteWord α) (n : ℕ) :
    prefixMetricLength length (σ.mapInfinite word)
        (σ.mapWord (word.take n)).length =
      scale * prefixMetricLength length word n := by
  calc
    prefixMetricLength length (σ.mapInfinite word)
        (σ.mapWord (word.take n)).length =
        wordMetricLength length
          ((σ.mapInfinite word).take (σ.mapWord (word.take n)).length) :=
      prefixMetricLength_eq_wordMetricLength_take_coding _ _ _
    _ = wordMetricLength length (σ.mapWord (word.take n)) := by
      rw [mapInfinite_take_substitutionPrefix]
    _ = scale * wordMetricLength length (word.take n) :=
      wordMetricLength_mapWord_of_scales_coding hmetric _
    _ = scale * prefixMetricLength length word n := by
      rw [prefixMetricLength_eq_wordMetricLength_take_coding]

/-! ### C4d: one returned block and the full returned itinerary -/

private def directedEdgeDisplacement_coding {K : Finset I}
    (e : DirectedMarkovEdge K) : ℝ :=
  (e.target : ℝ) - (e.source : ℝ)

/-- In a literal path, summing the signed displacements before the `i`-th
edge gives the source coordinate of that edge. -/
private theorem literalDirectedEdgePath_source_coordinate_coding
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (i : ℕ) (hi : i < w.length) :
    ((w[i]).source : ℝ) = (x : ℝ) +
      ((w.take i).map directedEdgeDisplacement_coding).sum := by
  induction w generalizing x i with
  | nil => simp at hi
  | cons e rest ih =>
      rcases hstart with ⟨first, tail, heq, hsource⟩
      simp at heq
      rcases heq with ⟨rfl, rfl⟩
      cases i with
      | zero => simpa using congrArg Subtype.val hsource
      | succ i =>
          cases rest with
          | nil => simp at hi
          | cons f tail =>
              have hconnect : e.target = f.source := hpath.1
              have htailPath : IsLiteralDirectedEdgePath (f :: tail) := hpath.2
              have htailStart : DirectedEdgePathStartsAt (f :: tail) e.target :=
                ⟨f, tail, rfl, hconnect.symm⟩
              have hiTail : i < (f :: tail).length := by simpa using hi
              have hcoord := ih htailPath htailStart i hiTail
              simp only [List.getElem_cons_succ, List.take_succ_cons,
                List.map_cons, List.sum_cons]
              rw [hcoord]
              have hsourceR : (e.source : ℝ) = (x : ℝ) :=
                congrArg Subtype.val hsource
              rw [← hsourceR]
              simp [directedEdgeDisplacement_coding]
              ring

private theorem wordMetricLength_take_le_coding
    {α : Type*} {length : α → ℝ} (hlength : ∀ a, 0 ≤ length a)
    (w : List α) (n : ℕ) :
    wordMetricLength length (w.take n) ≤ wordMetricLength length w := by
  calc
    wordMetricLength length (w.take n) ≤
        wordMetricLength length (w.take n) +
          wordMetricLength length (w.drop n) := by
      apply le_add_of_nonneg_right
      exact List.sum_nonneg fun z hz => by
        obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hz
        exact hlength a
    _ = wordMetricLength length (w.take n ++ w.drop n) :=
      (wordMetricLength_append_coding _ _ _).symm
    _ = wordMetricLength length w := by rw [List.take_append_drop]

private theorem metricMinimalPath_forward_displacement_coding
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hxy : x < y) (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|) :
    ∀ e ∈ w, directedEdgeDisplacement_coding e = e.length := by
  have hsum := literalDirectedEdgePath_displacement_sum hpath hstart hend
  have habsEq :
      (w.map fun e => |directedEdgeDisplacement_coding e|).sum =
        (w.map directedEdgeDisplacement_coding).sum := by
    have hdirect :
        (w.map fun e => |(e.target : ℝ) - (e.source : ℝ)|).sum =
          (w.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
      have hxyR : (x : ℝ) < (y : ℝ) := hxy
      rw [← wordMetricLength_eq_sum_abs_displacement w, hmetric,
        abs_of_pos (sub_pos.mpr hxyR), hsum]
    simpa [directedEdgeDisplacement_coding] using hdirect
  have hnonneg := list_forall_nonneg_of_sum_abs_eq_sum
    (values := w.map directedEdgeDisplacement_coding)
    (by simpa [List.map_map] using habsEq)
  intro e he
  have heNonneg := hnonneg (directedEdgeDisplacement_coding e)
    (List.mem_map.mpr ⟨e, he, rfl⟩)
  calc
    directedEdgeDisplacement_coding e =
        |directedEdgeDisplacement_coding e| :=
      (abs_of_nonneg heNonneg).symm
    _ = e.length := by
      simpa [directedEdgeDisplacement_coding] using
        (directedMarkovEdge_length_eq_abs_displacement e).symm

private theorem metricMinimalPath_backward_displacement_coding
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hyx : y < x) (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|) :
    ∀ e ∈ w, directedEdgeDisplacement_coding e = -e.length := by
  have hsum := literalDirectedEdgePath_displacement_sum hpath hstart hend
  have habsEq :
      (w.map fun e => |directedEdgeDisplacement_coding e|).sum =
        -(w.map directedEdgeDisplacement_coding).sum := by
    have hdirect :
        (w.map fun e => |(e.target : ℝ) - (e.source : ℝ)|).sum =
          -(w.map fun e => (e.target : ℝ) - (e.source : ℝ)).sum := by
      have hyxR : (y : ℝ) < (x : ℝ) := hyx
      rw [← wordMetricLength_eq_sum_abs_displacement w, hmetric,
        abs_of_neg (sub_neg.mpr hyxR), hsum]
    simpa [directedEdgeDisplacement_coding] using hdirect
  have hnonpos := list_forall_nonpos_of_sum_abs_eq_neg_sum
    (values := w.map directedEdgeDisplacement_coding)
    (by simpa [List.map_map] using habsEq)
  intro e he
  have heNonpos := hnonpos (directedEdgeDisplacement_coding e)
    (List.mem_map.mpr ⟨e, he, rfl⟩)
  calc
    directedEdgeDisplacement_coding e =
        -|directedEdgeDisplacement_coding e| := by
      rw [abs_of_nonpos heNonpos]
      ring
    _ = -e.length := by
      rw [show |directedEdgeDisplacement_coding e| = e.length by
        simpa [directedEdgeDisplacement_coding] using
          (directedMarkovEdge_length_eq_abs_displacement e).symm]

private theorem directedEdge_forward_of_displacement_eq_length_coding
    {K : Finset I} (e : DirectedMarkovEdge K)
    (h : directedEdgeDisplacement_coding e = e.length) :
    e.forward = true := by
  cases hdir : e.forward with
  | false =>
      have hd : directedEdgeDisplacement_coding e = -e.length := by
        simp [directedEdgeDisplacement_coding, DirectedMarkovEdge.source,
          DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
      rw [hd] at h
      linarith [e.length_pos]
  | true => rfl

private theorem directedEdge_backward_of_displacement_eq_neg_length_coding
    {K : Finset I} (e : DirectedMarkovEdge K)
    (h : directedEdgeDisplacement_coding e = -e.length) :
    e.forward = false := by
  cases hdir : e.forward with
  | false => rfl
  | true =>
      have hd : directedEdgeDisplacement_coding e = e.length := by
        simp [directedEdgeDisplacement_coding, DirectedMarkovEdge.source,
          DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
      rw [hd] at h
      linarith [e.length_pos]

/-- A shortest literal path between two vertices reads the corresponding
straight unit-speed segment, edge by edge. -/
private theorem shortestSegment_get_traversal_coding
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K} {x y : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|)
    (hsegment : ∀ v : ℝ, 0 ≤ v → v ≤ |(y : ℝ) - (x : ℝ)| →
      (ψ (t + v) : ℝ) =
        if x < y then (x : ℝ) + v else (x : ℝ) - v)
    (i : ℕ) (hi : i < w.length) :
    TraversesDirectedEdge ψ
      (t + wordMetricLength DirectedMarkovEdge.length (w.take i)) (w[i]) := by
  have hmetricPos : 0 < wordMetricLength DirectedMarkovEdge.length w := by
    rcases hstart with ⟨first, rest, rfl, _hfirst⟩
    simp only [wordMetricLength, List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg first.length_pos
      (List.sum_nonneg fun z hz => by
        obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hz
        exact e.length_pos.le)
  have hxyne : x ≠ y := by
    intro hxy
    subst y
    rw [hmetric] at hmetricPos
    simp at hmetricPos
  have hiMem : w[i] ∈ w := List.getElem_mem _
  have hcoord := literalDirectedEdgePath_source_coordinate_coding
    hpath hstart i hi
  let pref := wordMetricLength DirectedMarkovEdge.length (w.take i)
  have hprefNonneg : 0 ≤ pref := by
    dsimp [pref, wordMetricLength]
    exact List.sum_nonneg fun z hz => by
      obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hz
      exact e.length_pos.le
  have hstepBound : pref + (w[i]).length ≤
      |(y : ℝ) - (x : ℝ)| := by
    have htake := wordMetricLength_take_le_coding
      (fun e : DirectedMarkovEdge K => e.length_pos.le) w (i + 1)
    rw [List.take_succ_eq_append_getElem hi,
      wordMetricLength_append_coding] at htake
    rw [hmetric] at htake
    simpa [wordMetricLength, pref] using htake
  by_cases hxy : x < y
  · have halign := metricMinimalPath_forward_displacement_coding
      hxy hpath hstart hend hmetric
    have hprefixDisp :
        ((w.take i).map directedEdgeDisplacement_coding).sum = pref := by
      dsimp [pref, wordMetricLength]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      exact halign e (List.mem_of_mem_take he)
    rw [hprefixDisp] at hcoord
    have hdir := directedEdge_forward_of_displacement_eq_length_coding
      w[i] (halign w[i] hiMem)
    have hlower : ((w[i]).lower : ℝ) = (x : ℝ) + pref := by
      simpa [DirectedMarkovEdge.source, hdir] using hcoord
    intro u hu0 hule
    have hv0 : 0 ≤ pref + u := add_nonneg hprefNonneg hu0
    have hvle : pref + u ≤ |(y : ℝ) - (x : ℝ)| := by linarith
    have hs := hsegment (pref + u) hv0 hvle
    rw [hdir]
    change (ψ ((t + pref) + u) : ℝ) = (w[i].lower : ℝ) + u
    calc
      (ψ ((t + pref) + u) : ℝ) = (ψ (t + (pref + u)) : ℝ) := by ring_nf
      _ = (x : ℝ) + (pref + u) := by simpa [hxy] using hs
      _ = (w[i].lower : ℝ) + u := by rw [hlower]; ring
  · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) hxyne.symm
    have halign := metricMinimalPath_backward_displacement_coding
      hyx hpath hstart hend hmetric
    have hprefixDisp :
        ((w.take i).map directedEdgeDisplacement_coding).sum = -pref := by
      calc
        ((w.take i).map directedEdgeDisplacement_coding).sum =
            ((w.take i).map (fun e => -e.length)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro e he
          exact halign e (List.mem_of_mem_take he)
        _ = -pref := by
          dsimp [pref, wordMetricLength]
          induction w.take i with
          | nil => simp
          | cons e rest ih =>
              simp only [List.map_cons, List.sum_cons]
              rw [ih]
              ring
    rw [hprefixDisp] at hcoord
    have hdir := directedEdge_backward_of_displacement_eq_neg_length_coding
      w[i] (halign w[i] hiMem)
    have hupper : ((w[i]).upper : ℝ) = (x : ℝ) - pref := by
      simpa [DirectedMarkovEdge.source, hdir] using hcoord
    intro u hu0 hule
    have hv0 : 0 ≤ pref + u := add_nonneg hprefNonneg hu0
    have hvle : pref + u ≤ |(y : ℝ) - (x : ℝ)| := by linarith
    have hs := hsegment (pref + u) hv0 hvle
    rw [hdir]
    change (ψ ((t + pref) + u) : ℝ) = (w[i].upper : ℝ) - u
    calc
      (ψ ((t + pref) + u) : ℝ) = (ψ (t + (pref + u)) : ℝ) := by ring_nf
      _ = (x : ℝ) - (pref + u) := by simpa [hxy] using hs
      _ = (w[i].upper : ℝ) - u := by rw [hupper]; ring

/-- On one source edge, the return identity and constant-slope Markov
geometry traverse the modeled substitution image literally, at the scaled
source start time. -/
private theorem equivariant_substitutionImage_traversal
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {σ : Symbolic.Substitution alphabet} {length : alphabet → ℝ}
    {ψ : ℝ → I}
    (hscale : 0 < scale)
    (hreturn : ∀ t : ℝ, 0 ≤ t → ψ (scale * t) = T (ψ t))
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet σ)
    (hlength : ∀ e, length e = e.1.length)
    (hmetric : SubstitutionScalesLetterLengths σ length scale)
    {e : alphabet} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hsource : TraversesDirectedEdge ψ t₀ e.1) :
    ∀ j : Fin (σ e).length,
      TraversesDirectedEdge ψ
        (scale * t₀ + wordMetricLength length ((σ e).take j.1))
        (occurringEdge alphabet ((σ e).get j)) := by
  have hlen : 0 < e.1.length := e.1.length_pos
  have hlowerMem : e.1.lower ∈ Set.Icc e.1.lower e.1.upper :=
    ⟨le_rfl, e.1.2.2.2.1.le⟩
  have hupperMem : e.1.upper ∈ Set.Icc e.1.lower e.1.upper :=
    ⟨e.1.2.2.2.1.le, le_rfl⟩
  have hsourceMem : e.1.source ∈ Set.Icc e.1.lower e.1.upper := by
    cases hdir : e.1.forward <;>
      simp [DirectedMarkovEdge.source, hdir, hlowerMem, hupperMem]
  have htargetMem : e.1.target ∈ Set.Icc e.1.lower e.1.upper := by
    cases hdir : e.1.forward <;>
      simp [DirectedMarkovEdge.target, hdir, hlowerMem, hupperMem]
  rcases (hmarkov e.1.2).1 with ⟨m, c, haff⟩
  have hdistance := markovEdge_image_distance_coding hmarkov hslope e.1
  have himageNe : T e.1.source ≠ T e.1.target := by
    intro heq
    have hzero : (0 : ℝ) = scale * e.1.length := by
      simpa [heq] using hdistance
    nlinarith
  have hminimal := modeledSubstitutionImage_is_metricMinimal
    hmarkov hslope hmodels hlength hmetric e
  have hsegment : ∀ v : ℝ, 0 ≤ v →
      v ≤ |(T e.1.target : ℝ) - (T e.1.source : ℝ)| →
      (ψ (scale * t₀ + v) : ℝ) =
        if T e.1.source < T e.1.target then
          (T e.1.source : ℝ) + v else (T e.1.source : ℝ) - v := by
    intro v hv0 hvle
    let u := v / scale
    have hu0 : 0 ≤ u := div_nonneg hv0 hscale.le
    have hule : u ≤ e.1.length := by
      apply (div_le_iff₀ hscale).2
      nlinarith [hvle, hdistance]
    have htplus : 0 ≤ t₀ + u := add_nonneg ht₀ hu0
    have hsourceU := hsource u hu0 hule
    have hψMem : ψ (t₀ + u) ∈ Set.Icc e.1.lower e.1.upper := by
      cases hdir : e.1.forward with
      | false =>
          rw [hdir] at hsourceU
          constructor
          · change (e.1.lower : ℝ) ≤ (ψ (t₀ + u) : ℝ)
            rw [hsourceU]
            dsimp [DirectedMarkovEdge.length] at hule
            linarith
          · change (ψ (t₀ + u) : ℝ) ≤ (e.1.upper : ℝ)
            rw [hsourceU]
            linarith
      | true =>
          rw [hdir] at hsourceU
          constructor
          · change (e.1.lower : ℝ) ≤ (ψ (t₀ + u) : ℝ)
            rw [hsourceU]
            linarith
          · change (ψ (t₀ + u) : ℝ) ≤ (e.1.upper : ℝ)
            rw [hsourceU]
            dsimp [DirectedMarkovEdge.length] at hule
            linarith
    have hdispAffine :
        (T e.1.target : ℝ) - (T e.1.source : ℝ) =
          m * directedEdgeDisplacement_coding e.1 := by
      rw [haff e.1.target htargetMem, haff e.1.source hsourceMem]
      simp [directedEdgeDisplacement_coding]
      ring
    have hψParam : (ψ (t₀ + u) : ℝ) = (e.1.source : ℝ) +
        directedEdgeDisplacement_coding e.1 / e.1.length * u := by
      cases hdir : e.1.forward with
      | false =>
          rw [hdir] at hsourceU
          rw [hsourceU]
          have hd : directedEdgeDisplacement_coding e.1 = -e.1.length := by
            simp [directedEdgeDisplacement_coding, DirectedMarkovEdge.source,
              DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
          rw [hd]
          simp only [DirectedMarkovEdge.source, hdir]
          field_simp [hlen.ne'] <;> ring
      | true =>
          rw [hdir] at hsourceU
          rw [hsourceU]
          have hd : directedEdgeDisplacement_coding e.1 = e.1.length := by
            simp [directedEdgeDisplacement_coding, DirectedMarkovEdge.source,
              DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
          rw [hd]
          simp only [DirectedMarkovEdge.source, hdir]
          field_simp [hlen.ne'] <;> ring
    have hinterp : (T (ψ (t₀ + u)) : ℝ) = (T e.1.source : ℝ) +
        ((T e.1.target : ℝ) - (T e.1.source : ℝ)) /
          e.1.length * u := by
      rw [haff (ψ (t₀ + u)) hψMem, hψParam, hdispAffine,
        haff e.1.source hsourceMem]
      field_simp [hlen.ne'] <;> ring
    have htime : scale * (t₀ + u) = scale * t₀ + v := by
      dsimp [u]
      field_simp [hscale.ne'] <;> ring
    have hscaled : (ψ (scale * t₀ + v) : ℝ) =
        (T e.1.source : ℝ) +
          ((T e.1.target : ℝ) - (T e.1.source : ℝ)) /
            e.1.length * u := by
      calc
        (ψ (scale * t₀ + v) : ℝ) =
            (ψ (scale * (t₀ + u)) : ℝ) := by rw [htime]
        _ = (T (ψ (t₀ + u)) : ℝ) :=
          congrArg Subtype.val (hreturn (t₀ + u) htplus)
        _ = _ := hinterp
    by_cases hinc : T e.1.source < T e.1.target
    · have hincR : (T e.1.source : ℝ) < (T e.1.target : ℝ) := hinc
      have hdelta : (T e.1.target : ℝ) - (T e.1.source : ℝ) =
          scale * e.1.length := by
        rw [← hdistance, abs_of_pos (sub_pos.mpr hincR)]
      simp only [if_pos hinc]
      rw [hscaled, hdelta]
      dsimp [u]
      field_simp [hlen.ne', hscale.ne'] <;> ring
    · have hdec : T e.1.target < T e.1.source :=
        lt_of_le_of_ne (le_of_not_gt hinc) himageNe.symm
      have hdecR : (T e.1.target : ℝ) < (T e.1.source : ℝ) := hdec
      have hdelta : (T e.1.target : ℝ) - (T e.1.source : ℝ) =
          -(scale * e.1.length) := by
        have hd := hdistance
        rw [abs_of_neg (sub_neg.mpr hdecR)] at hd
        linarith
      simp only [if_neg hinc]
      rw [hscaled, hdelta]
      dsimp [u]
      field_simp [hlen.ne', hscale.ne'] <;> ring
  intro j
  have hj : j.1 < (geometricEdgeWord alphabet (σ e)).length := by
    simpa [geometricEdgeWord] using j.2
  have htrav := shortestSegment_get_traversal_coding
    hminimal.1 hminimal.2.1 hminimal.2.2.1 hminimal.2.2.2
    hsegment j.1 hj
  have hpref : wordMetricLength DirectedMarkovEdge.length
      ((geometricEdgeWord alphabet (σ e)).take j.1) =
      wordMetricLength length ((σ e).take j.1) := by
    simp only [geometricEdgeWord, List.map_take, wordMetricLength, List.map_map]
    apply congrArg List.sum
    apply congrArg (List.take j.1)
    apply List.map_congr_left
    intro letter hletter
    exact (hlength letter).symm
  rw [hpref] at htrav
  simpa [geometricEdgeWord, occurringEdge] using htrav

/-- Recursive traversal of a finite literal geometric word. -/
private def TraversesLiteralWord_coding {K : Finset I} (ψ : ℝ → I) :
    ℝ → LiteralDirectedEdgeWord K → Prop
  | _, [] => True
  | t, e :: rest =>
      TraversesDirectedEdge ψ t e ∧
        TraversesLiteralWord_coding ψ (t + e.length) rest

private theorem traversesLiteralWord_append_coding
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {u v : LiteralDirectedEdgeWord K} :
    TraversesLiteralWord_coding ψ t (u ++ v) ↔
      TraversesLiteralWord_coding ψ t u ∧
        TraversesLiteralWord_coding ψ
          (t + wordMetricLength DirectedMarkovEdge.length u) v := by
  induction u generalizing t with
  | nil => simp [TraversesLiteralWord_coding, wordMetricLength]
  | cons e u ih =>
      simp only [List.cons_append, TraversesLiteralWord_coding]
      rw [ih]
      simp [wordMetricLength, add_assoc]
      tauto

private theorem traversesLiteralWord_of_pointwise_coding
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (h : ∀ (i : ℕ) (hi : i < w.length),
      TraversesDirectedEdge ψ
        (t + wordMetricLength DirectedMarkovEdge.length (w.take i)) (w[i])) :
    TraversesLiteralWord_coding ψ t w := by
  induction w generalizing t with
  | nil => trivial
  | cons e rest ih =>
      constructor
      · have hzero := h 0 (by simp)
        simpa [wordMetricLength] using hzero
      · apply ih
        intro i hi
        have hsucc := h (i + 1) (by simpa using hi)
        simpa [wordMetricLength, add_assoc] using hsucc

private theorem traversesLiteralWord_get_coding
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (h : TraversesLiteralWord_coding ψ t w)
    (i : ℕ) (hi : i < w.length) :
    TraversesDirectedEdge ψ
      (t + wordMetricLength DirectedMarkovEdge.length (w.take i)) (w[i]) := by
  induction w generalizing t i with
  | nil => simp at hi
  | cons e rest ih =>
      cases i with
      | zero => simpa [wordMetricLength] using h.1
      | succ i =>
          have hiRest : i < rest.length := by simpa using hi
          have htail := ih h.2 i hiRest
          simpa [wordMetricLength, add_assoc] using htail

private theorem wordMetricLength_geometricEdgeWord_coding
    {K : Finset I} {alphabet : OccurringDirectedAlphabet K}
    {length : alphabet → ℝ} (hlength : ∀ e, length e = e.1.length)
    (w : Symbolic.Word alphabet) :
    wordMetricLength DirectedMarkovEdge.length (geometricEdgeWord alphabet w) =
      wordMetricLength length w := by
  simp only [geometricEdgeWord, wordMetricLength, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro letter hletter
  exact (hlength letter).symm

private theorem itinerary_take_traversal_coding
    {K : Finset I} {alphabet : OccurringDirectedAlphabet K}
    {length : alphabet → ℝ} {ψ : ℝ → I}
    {word : Symbolic.InfiniteWord alphabet}
    (hlength : ∀ e, length e = e.1.length)
    (hitinerary : HasLiteralUnitSpeedItinerary ψ
      (occurringEdge alphabet) length word)
    (n : ℕ) :
    TraversesLiteralWord_coding ψ 0
      (geometricEdgeWord alphabet (word.take n)) := by
  apply traversesLiteralWord_of_pointwise_coding
  intro i hi
  have hiSource : i < n := by simpa [geometricEdgeWord] using hi
  have htrav := hitinerary.2.2 i
  have hedge :
      (geometricEdgeWord alphabet (word.take n))[i] =
        occurringEdge alphabet (word i) := by
    simp [geometricEdgeWord, Stream'.get]
  have hpref :
      wordMetricLength DirectedMarkovEdge.length
          ((geometricEdgeWord alphabet (word.take n)).take i) =
        prefixMetricLength length word i := by
    have htakeSource : (word.take n).take i = word.take i := by
      rw [Stream'.take_take, Nat.min_eq_right hiSource.le]
    have htakeGeom :
        (geometricEdgeWord alphabet (word.take n)).take i =
          geometricEdgeWord alphabet (word.take i) := by
      simp only [geometricEdgeWord]
      rw [← List.map_take, htakeSource]
    rw [htakeGeom, wordMetricLength_geometricEdgeWord_coding hlength]
    exact prefixMetricLength_eq_wordMetricLength_take_coding _ _ _ |>.symm
  rw [hpref, hedge]
  simpa using htrav

private theorem equivariant_geometric_mapWord_traversal_coding
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {σ : Symbolic.Substitution alphabet} {length : alphabet → ℝ}
    {ψ : ℝ → I}
    (hscale : 0 < scale)
    (hreturn : ∀ t : ℝ, 0 ≤ t → ψ (scale * t) = T (ψ t))
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧ IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet σ)
    (hlength : ∀ e, length e = e.1.length)
    (hmetric : SubstitutionScalesLetterLengths σ length scale)
    {w : Symbolic.Word alphabet} {t : ℝ} (ht : 0 ≤ t)
    (htrav : TraversesLiteralWord_coding ψ t
      (geometricEdgeWord alphabet w)) :
    TraversesLiteralWord_coding ψ (scale * t)
      (geometricEdgeWord alphabet (σ.mapWord w)) := by
  induction w generalizing t with
  | nil => simp [Symbolic.Substitution.mapWord, geometricEdgeWord,
      TraversesLiteralWord_coding]
  | cons e rest ih =>
      rw [Symbolic.Substitution.mapWord_cons, geometricEdgeWord,
        List.map_append, traversesLiteralWord_append_coding]
      have hone : TraversesLiteralWord_coding ψ (scale * t)
          (geometricEdgeWord alphabet (σ e)) := by
        apply traversesLiteralWord_of_pointwise_coding
        intro j hj
        let jFin : Fin (σ e).length := ⟨j, by simpa [geometricEdgeWord] using hj⟩
        have hpoint := equivariant_substitutionImage_traversal
          hscale hreturn hmarkov hslope hmodels hlength hmetric ht htrav.1 jFin
        have hpref : wordMetricLength DirectedMarkovEdge.length
            ((geometricEdgeWord alphabet (σ e)).take j) =
            wordMetricLength length ((σ e).take j) := by
          simpa [geometricEdgeWord] using
            (wordMetricLength_geometricEdgeWord_coding hlength
              ((σ e).take j))
        rw [hpref]
        simpa [jFin, geometricEdgeWord] using hpoint
      refine ⟨hone, ?_⟩
      have htail := ih (t := t + e.1.length)
        (add_nonneg ht e.1.length_pos.le) htrav.2
      have himageMetric := hmetric e
      rw [hlength e] at himageMetric
      have hgeometricMetric :=
        wordMetricLength_geometricEdgeWord_coding hlength (σ e)
      change TraversesLiteralWord_coding ψ
        (scale * t + wordMetricLength DirectedMarkovEdge.length
          (geometricEdgeWord alphabet (σ e)))
        (geometricEdgeWord alphabet (σ.mapWord rest))
      rw [hgeometricMetric, himageMetric]
      convert htail using 1 <;> ring

private theorem mapWord_length_ge_length_coding
    {α : Type*} (σ : Symbolic.Substitution α) (w : Symbolic.Word α) :
    w.length ≤ (σ.mapWord w).length := by
  induction w with
  | nil => simp [Symbolic.Substitution.mapWord]
  | cons letter rest ih =>
      rw [Symbolic.Substitution.mapWord_cons, List.length_append,
        List.length_cons]
      have hletter : 1 ≤ (σ letter).length :=
        Nat.one_le_iff_ne_zero.mpr fun hzero =>
          σ.image_ne_nil letter (List.eq_nil_of_length_eq_zero hzero)
      omega

private theorem traversesDirectedEdge_start_coding
    {K : Finset I} {ψ : ℝ → I} {t : ℝ} {e : DirectedMarkovEdge K}
    (h : TraversesDirectedEdge ψ t e) : ψ t = e.source := by
  have hzero := h 0 le_rfl e.length_pos.le
  apply Subtype.ext
  cases hdir : e.forward <;>
    simp [hdir, DirectedMarkovEdge.source] at hzero ⊢ <;> exact hzero

private theorem traversesDirectedEdge_end_coding
    {K : Finset I} {ψ : ℝ → I} {t : ℝ} {e : DirectedMarkovEdge K}
    (h : TraversesDirectedEdge ψ t e) : ψ (t + e.length) = e.target := by
  have hend := h e.length e.length_pos.le le_rfl
  apply Subtype.ext
  cases hdir : e.forward with
  | false =>
      rw [hdir] at hend
      simpa [hdir, DirectedMarkovEdge.target, DirectedMarkovEdge.length]
        using hend
  | true =>
      rw [hdir] at hend
      simpa [hdir, DirectedMarkovEdge.target, DirectedMarkovEdge.length]
        using hend

/-- Parsing the returned blocks and using their exact boundary times yields
a literal itinerary of the same ray for the infinite substituted word. -/
private theorem equivariant_mapInfinite_hasLiteralUnitSpeedItinerary
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {σ : Symbolic.Substitution alphabet} {length : alphabet → ℝ}
    {ψ : ℝ → I} {word : Symbolic.InfiniteWord alphabet}
    (hscale : 0 < scale)
    (hreturn : ∀ t : ℝ, 0 ≤ t → ψ (scale * t) = T (ψ t))
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet σ)
    (hlength : ∀ e, length e = e.1.length)
    (hmetric : SubstitutionScalesLetterLengths σ length scale)
    (hitinerary : HasLiteralUnitSpeedItinerary ψ
      (occurringEdge alphabet) length word) :
    HasLiteralUnitSpeedItinerary ψ (occurringEdge alphabet) length
      (σ.mapInfinite word) := by
  let output := σ.mapInfinite word
  have houtputTraversal : ∀ n : ℕ, TraversesDirectedEdge ψ
      (prefixMetricLength length output n)
      (occurringEdge alphabet (output n)) := by
    intro n
    let inputPrefix := word.take (n + 1)
    let finiteOutput := σ.mapWord inputPrefix
    have hsourceFinite := itinerary_take_traversal_coding
      hlength hitinerary (n + 1)
    have hmapped := equivariant_geometric_mapWord_traversal_coding
      hscale hreturn hmarkov hslope hmodels hlength hmetric
      (t := 0) le_rfl hsourceFinite
    have hlengthLower : inputPrefix.length ≤ finiteOutput.length :=
      mapWord_length_ge_length_coding σ inputPrefix
    have hinputLength : inputPrefix.length = n + 1 := by
      simp [inputPrefix]
    have hnFinite : n < finiteOutput.length := by
      rw [hinputLength] at hlengthLower
      omega
    have hfiniteGet := traversesLiteralWord_get_coding hmapped n (by
      simpa [finiteOutput, geometricEdgeWord] using hnFinite)
    have hwhole : output.take finiteOutput.length = finiteOutput := by
      simpa [output, finiteOutput, inputPrefix] using
        mapInfinite_take_substitutionPrefix σ word (n + 1)
    have hnWhole : n < (output.take finiteOutput.length).length := by
      simpa [hwhole] using hnFinite
    have hprefixEq : finiteOutput.take n = output.take n := by
      have htake := congrArg (List.take n) hwhole
      have hnle : n ≤ finiteOutput.length := hnFinite.le
      simpa [Stream'.take_take, Nat.min_eq_right hnle] using htake.symm
    have hletterEq : finiteOutput[n] = output n := by
      calc
        finiteOutput[n]'hnFinite =
            (output.take finiteOutput.length)[n]'hnWhole :=
          getElem_congr hwhole.symm rfl hnFinite
        _ = output.get n := Stream'.take_get
          (m := n) (n := finiteOutput.length) (a := output) hnWhole
    have hgeomPrefix :
        (geometricEdgeWord alphabet finiteOutput).take n =
          geometricEdgeWord alphabet (output.take n) := by
      simp only [geometricEdgeWord]
      rw [← List.map_take, hprefixEq]
    have hnGeom : n < (geometricEdgeWord alphabet finiteOutput).length := by
      simpa [geometricEdgeWord] using hnFinite
    have hgeomLetter :
        (geometricEdgeWord alphabet finiteOutput)[n]'hnGeom =
          occurringEdge alphabet (output n) := by
      simpa [geometricEdgeWord] using
        congrArg (occurringEdge alphabet) hletterEq
    rw [hgeomPrefix,
      wordMetricLength_geometricEdgeWord_coding hlength,
      ← prefixMetricLength_eq_wordMetricLength_take_coding,
      hgeomLetter] at hfiniteGet
    simpa using hfiniteGet
  refine ⟨hlength, ?_, houtputTraversal⟩
  intro n
  have hcurrent := traversesDirectedEdge_end_coding (houtputTraversal n)
  have hnext := traversesDirectedEdge_start_coding (houtputTraversal (n + 1))
  have hprefSucc : prefixMetricLength length output (n + 1) =
      prefixMetricLength length output n + length (output n) := by
    simp [prefixMetricLength, Finset.sum_range_succ]
  rw [hprefSucc, hlength (output n)] at hnext
  exact hcurrent.symm.trans hnext

/-! ### C4e: uniqueness and fixedness -/

private theorem directedMarkovEdge_eq_of_forward_source_coding
    {K : Finset I} {e f : DirectedMarkovEdge K}
    (he : e.forward = true) (hf : f.forward = true)
    (hsource : e.source = f.source) : e = f := by
  have hlower : e.lower = f.lower := by
    simpa [DirectedMarkovEdge.source, he, hf] using hsource
  have hupper : e.upper = f.upper := by
    apply le_antisymm
    · by_contra hnot
      have hlt : f.upper < e.upper := lt_of_not_ge hnot
      have hbetween : e.lower < f.upper ∧ f.upper < e.upper :=
        ⟨by rw [hlower]; exact f.2.2.2.1, hlt⟩
      exact e.2.2.2.2 f.upper f.1.1.2.property hbetween
    · by_contra hnot
      have hlt : e.upper < f.upper := lt_of_not_ge hnot
      have hbetween : f.lower < e.upper ∧ e.upper < f.upper :=
        ⟨by rw [← hlower]; exact e.2.2.2.1, hlt⟩
      exact f.2.2.2.2 e.upper e.1.1.2.property hbetween
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext hlower
    · exact Subtype.ext hupper
  · exact he.trans hf.symm

private theorem directedMarkovEdge_eq_of_backward_source_coding
    {K : Finset I} {e f : DirectedMarkovEdge K}
    (he : e.forward = false) (hf : f.forward = false)
    (hsource : e.source = f.source) : e = f := by
  have hupper : e.upper = f.upper := by
    simpa [DirectedMarkovEdge.source, he, hf] using hsource
  have hlower : e.lower = f.lower := by
    apply le_antisymm
    · by_contra hnot
      have hlt : f.lower < e.lower := lt_of_not_ge hnot
      have hbetween : f.lower < e.lower ∧ e.lower < f.upper :=
        ⟨hlt, by rw [← hupper]; exact e.2.2.2.1⟩
      exact f.2.2.2.2 e.lower e.1.1.1.property hbetween
    · by_contra hnot
      have hlt : e.lower < f.lower := lt_of_not_ge hnot
      have hbetween : e.lower < f.lower ∧ f.lower < e.upper :=
        ⟨hlt, by rw [hupper]; exact f.2.2.2.1⟩
      exact e.2.2.2.2 f.lower f.1.1.1.property hbetween
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext hlower
    · exact Subtype.ext hupper
  · exact he.trans hf.symm

private theorem traversesDirectedEdge_unique_coding
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {e f : DirectedMarkovEdge K}
    (he : TraversesDirectedEdge ψ t e)
    (hf : TraversesDirectedEdge ψ t f) : e = f := by
  have hsource : e.source = f.source :=
    (traversesDirectedEdge_start_coding he).symm.trans
      (traversesDirectedEdge_start_coding hf)
  cases hedir : e.forward <;> cases hfdir : f.forward
  · exact directedMarkovEdge_eq_of_backward_source_coding hedir hfdir hsource
  · let δ := min e.length f.length / 2
    have hδpos : 0 < δ := div_pos (lt_min e.length_pos f.length_pos) (by norm_num)
    have hδe : δ ≤ e.length := by
      have hminpos : 0 < min e.length f.length :=
        lt_min e.length_pos f.length_pos
      have hminle := min_le_left e.length f.length
      dsimp [δ]
      nlinarith
    have hδf : δ ≤ f.length := by
      have hminpos : 0 < min e.length f.length :=
        lt_min e.length_pos f.length_pos
      have hminle := min_le_right e.length f.length
      dsimp [δ]
      nlinarith
    have heδ := he δ hδpos.le hδe
    have hfδ := hf δ hδpos.le hδf
    rw [hedir] at heδ
    rw [hfdir] at hfδ
    have hsourceR := congrArg Subtype.val hsource
    simp [DirectedMarkovEdge.source, hedir, hfdir] at hsourceR
    linarith
  · let δ := min e.length f.length / 2
    have hδpos : 0 < δ := div_pos (lt_min e.length_pos f.length_pos) (by norm_num)
    have hδe : δ ≤ e.length := by
      have hminpos : 0 < min e.length f.length :=
        lt_min e.length_pos f.length_pos
      have hminle := min_le_left e.length f.length
      dsimp [δ]
      nlinarith
    have hδf : δ ≤ f.length := by
      have hminpos : 0 < min e.length f.length :=
        lt_min e.length_pos f.length_pos
      have hminle := min_le_right e.length f.length
      dsimp [δ]
      nlinarith
    have heδ := he δ hδpos.le hδe
    have hfδ := hf δ hδpos.le hδf
    rw [hedir] at heδ
    rw [hfdir] at hfδ
    have hsourceR := congrArg Subtype.val hsource
    simp [DirectedMarkovEdge.source, hedir, hfdir] at hsourceR
    linarith
  · exact directedMarkovEdge_eq_of_forward_source_coding hedir hfdir hsource

/-- A literal unit-speed directed-edge itinerary of one path is unique once
edge lengths are the genuine positive geometric lengths. -/
private theorem literalUnitSpeedItinerary_unique
    {K : Finset I} {alphabet : OccurringDirectedAlphabet K}
    {length : alphabet → ℝ} {ψ : ℝ → I}
    {u v : Symbolic.InfiniteWord alphabet}
    (hlength : ∀ e, length e = e.1.length)
    (hu : HasLiteralUnitSpeedItinerary ψ
      (occurringEdge alphabet) length u)
    (hv : HasLiteralUnitSpeedItinerary ψ
      (occurringEdge alphabet) length v) :
    u = v := by
  apply funext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hpref : prefixMetricLength length u n =
          prefixMetricLength length v n := by
        simp only [prefixMetricLength]
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih i (Finset.mem_range.mp hi)]
      have huTrav := hu.2.2 n
      have hvTrav := hv.2.2 n
      rw [← hpref] at hvTrav
      apply Subtype.ext
      exact traversesDirectedEdge_unique_coding huTrav hvTrav

/-- A modeled substitution whose return map is equivariant with the ray
fixes its literal itinerary. -/
private theorem substitution_fixed_of_returnEquivariance
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    {alphabet : OccurringDirectedAlphabet K}
    {σ : Symbolic.Substitution alphabet} {length : alphabet → ℝ}
    {ψ : ℝ → I} {word : Symbolic.InfiniteWord alphabet}
    (hscale : 0 < scale)
    (hreturn : ∀ t : ℝ, 0 ≤ t → ψ (scale * t) = T (ψ t))
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hmodels : ModelsDirectedEdgeSubstitution T alphabet σ)
    (hlength : ∀ e, length e = e.1.length)
    (hmetric : SubstitutionScalesLetterLengths σ length scale)
    (hitinerary : HasLiteralUnitSpeedItinerary ψ
      (occurringEdge alphabet) length word) :
    σ.IsFixedPoint word := by
  have hmapped := equivariant_mapInfinite_hasLiteralUnitSpeedItinerary
    hscale hreturn hmarkov hslope hmodels hlength hmetric hitinerary
  exact literalUnitSpeedItinerary_unique hlength hmapped hitinerary

private theorem DirectedSubstitutionPairData.fixedA_of_itinerary
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S) :
    S.substitutionA.IsFixedPoint J.word := by
  apply substitution_fixed_of_returnEquivariance
    (T := A) (scale := a) (ψ := F.ray)
  · exact zero_lt_one.trans F.one_lt_a
  · exact F.return_A
  · intro x y hxy
    exact (H.commonMarkov.2.2.2.2 hxy).1
  · exact F.constantSlope_A
  · exact S.modelsA
  · exact S.letterLength_eq_edge
  · exact S.scalesA
  · exact J.itinerary

private theorem DirectedSubstitutionPairData.fixedB_of_itinerary
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S) :
    S.substitutionB.IsFixedPoint J.word := by
  apply substitution_fixed_of_returnEquivariance
    (T := B) (scale := b) (ψ := F.ray)
  · exact zero_lt_one.trans F.one_lt_b
  · exact F.return_B
  · intro x y hxy
    exact (H.commonMarkov.2.2.2.2 hxy).2
  · exact F.constantSlope_B
  · exact S.modelsB
  · exact S.letterLength_eq_edge
  · exact S.scalesB
  · exact J.itinerary

/-! ### C4f: common prolongability and iterated prefixes -/

/-- Fixedness makes the image of the head begin with the head; exact metric
expansion by a factor greater than one forces its remaining tail to be
nonempty. -/
private theorem prolongableOn_head_of_fixedPoint_and_metricExpansion
    {α : Type*} {σ : Symbolic.Substitution α}
    {word : Symbolic.InfiniteWord α} {length : α → ℝ} {scale : ℝ}
    (hfixed : σ.IsFixedPoint word)
    (hmetric : SubstitutionScalesLetterLengths σ length scale)
    (hlength : ∀ e, 0 < length e) (hscale : 1 < scale) :
    σ.ProlongableOn word.head := by
  obtain ⟨first, tail, himage⟩ :=
    List.exists_cons_of_ne_nil (σ.image_ne_nil word.head)
  have hhead : σ.imageHead word.head = word.head := by
    have hzero := congrFun hfixed 0
    simpa using hzero
  have hfirst : first = word.head := by
    simpa [Symbolic.Substitution.imageHead, himage] using hhead
  subst first
  refine ⟨tail, ?_, himage⟩
  intro htail
  subst tail
  have hmetricHead := hmetric word.head
  simp [wordMetricLength, himage] at hmetricHead
  nlinarith [hlength word.head]

/-- Every iterated image of the head of a fixed one-sided word is the exact
prefix of the corresponding finite length. -/
private theorem fixedPoint_iterateLetter_is_prefix
    {α : Type*} {σ : Symbolic.Substitution α}
    {word : Symbolic.InfiniteWord α}
    (hfixed : σ.IsFixedPoint word) (n : ℕ) :
    word.take (σ.iterateLetter n word.head).length =
      σ.iterateLetter n word.head := by
  exact (Symbolic.iterateLetter_eq_fixedPoint_prefix hfixed n).symm

/-- The return identities make the same ray word a fixed point of both
substitutions.  The displayed prefix equations retain the stronger
prolongable-limit information used in the manuscript. -/
structure CommonFixedCodingData
    (A B : IntervalMap) {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S) where
  seed : S.alphabet
  head_eq_seed : J.word.head = seed
  fixedA : S.substitutionA.IsFixedPoint J.word
  fixedB : S.substitutionB.IsFixedPoint J.word
  prolongableA : S.substitutionA.ProlongableOn seed
  prolongableB : S.substitutionB.ProlongableOn seed
  iterateA_is_prefix : ∀ n : ℕ,
    J.word.take (S.substitutionA.iterateLetter n seed).length =
      S.substitutionA.iterateLetter n seed
  iterateB_is_prefix : ∀ n : ℕ,
    J.word.take (S.substitutionB.iterateLetter n seed).length =
      S.substitutionB.iterateLetter n seed

/-- **C4.** The literal itinerary is the common one-sided fixed word of the
two substitutions, each prolongable on its first directed edge. -/
theorem commonFixedCoding_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S) :
    Nonempty (CommonFixedCodingData A B F H S J) := by
  let seed : S.alphabet := J.word.head
  have hfixedA := S.fixedA_of_itinerary F H J
  have hfixedB := S.fixedB_of_itinerary F H J
  have hprolongableA : S.substitutionA.ProlongableOn seed :=
    prolongableOn_head_of_fixedPoint_and_metricExpansion
      hfixedA S.scalesA S.letterLength_pos F.one_lt_a
  have hprolongableB : S.substitutionB.ProlongableOn seed :=
    prolongableOn_head_of_fixedPoint_and_metricExpansion
      hfixedB S.scalesB S.letterLength_pos F.one_lt_b
  refine ⟨{
    seed := seed
    head_eq_seed := rfl
    fixedA := hfixedA
    fixedB := hfixedB
    prolongableA := hprolongableA
    prolongableB := hprolongableB
    iterateA_is_prefix := ?_
    iterateB_is_prefix := ?_ }⟩
  · intro n
    exact fixedPoint_iterateLetter_is_prefix hfixedA n
  · intro n
    exact fixedPoint_iterateLetter_is_prefix hfixedB n

/-! ## C5: restriction to exactly the occurring letters -/

/-- Simultaneous restriction to the directed edges which actually occur in
the common word.  `range_exactly_occurring` makes this a literal finite-set
model of `Symbolic.Substitution.OccurringAlphabet`; the forgetful equations
state that no substitution block is changed by the restriction. -/
structure OccurringAlphabetCodingData
    (A B : IntervalMap) {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J) where
  alphabet : OccurringDirectedAlphabet H.vertices
  alphabet_nonempty : alphabet.Nonempty
  toAmbient : alphabet → S.alphabet
  toAmbient_injective : Function.Injective toAmbient
  range_exactly_occurring : ∀ letter : S.alphabet,
    (∃ retained : alphabet, toAmbient retained = letter) ↔
      Symbolic.Substitution.OccursInInfiniteWord letter J.word
  substitutionA : Symbolic.Substitution alphabet
  substitutionB : Symbolic.Substitution alphabet
  word : Symbolic.InfiniteWord alphabet
  forget_word : ∀ n : ℕ, toAmbient (word n) = J.word n
  imageA_forget : ∀ letter : alphabet,
    (substitutionA letter).map toAmbient = S.substitutionA (toAmbient letter)
  imageB_forget : ∀ letter : alphabet,
    (substitutionB letter).map toAmbient = S.substitutionB (toAmbient letter)
  fixedA : substitutionA.IsFixedPoint word
  fixedB : substitutionB.IsFixedPoint word
  every_letter_occurs : ∀ letter : alphabet,
    Symbolic.Substitution.OccursInInfiniteWord letter word
  seed : alphabet
  head_eq_seed : word.head = seed
  prolongableA : substitutionA.ProlongableOn seed
  prolongableB : substitutionB.ProlongableOn seed
  letterLength : alphabet → ℝ
  letterLength_eq_ambient : ∀ letter,
    letterLength letter = S.letterLength (toAmbient letter)
  letterLength_pos : ∀ letter, 0 < letterLength letter
  scalesA : SubstitutionScalesLetterLengths substitutionA letterLength a
  scalesB : SubstitutionScalesLetterLengths substitutionB letterLength b
  itinerary : HasLiteralUnitSpeedItinerary F.ray
    (occurringEdge alphabet) letterLength word

/-! ### C5a: occurrence closure in a fixed word -/

/-- If a letter occurs in a fixed word, every letter of its substitution
image also occurs in that word.  The proof uses the exact physical block
given by `mapWord_drop_take_at_fixed`. -/
private theorem occurs_of_mem_image_of_fixedPoint
    {α : Type*} {σ : Symbolic.Substitution α}
    {word : Symbolic.InfiniteWord α} (hfixed : σ.IsFixedPoint word)
    {source output : α}
    (hsource : Symbolic.Substitution.OccursInInfiniteWord source word)
    (houtput : output ∈ σ source) :
    Symbolic.Substitution.OccursInInfiniteWord output word := by
  rcases hsource with ⟨position, hposition⟩
  have hblock := Symbolic.Substitution.mapWord_drop_take_at_fixed
    hfixed position 1
  have hsourceBlock : (word.drop position).take 1 = [source] := by
    rw [Stream'.take_succ]
    simp [Stream'.get, hposition]
  have himage : σ.mapWord [source] = σ source := by
    simp [Symbolic.Substitution.mapWord]
  rw [hsourceBlock, himage] at hblock
  rw [Symbolic.InfiniteFactorAt] at hblock
  have houtput' : output ∈
      (word.drop (σ.mapWord (word.take position)).length).take
        (σ source).length := by
    rw [hblock]
    exact houtput
  rw [List.mem_iff_getElem] at houtput'
  obtain ⟨offset, hoffset, hat⟩ := houtput'
  refine ⟨(σ.mapWord (word.take position)).length + offset, ?_⟩
  simpa using hat

/-! ### C5b: the finite geometric retained alphabet -/

/-- The finite geometric alphabet of precisely the ambient letters occurring
in the common ray word, together with its injective ambient embedding. -/
private structure FiniteRetainedAlphabetData
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S) where
  alphabet : OccurringDirectedAlphabet H.vertices
  alphabet_nonempty : alphabet.Nonempty
  toAmbient : alphabet → S.alphabet
  toAmbient_injective : Function.Injective toAmbient
  edge_forget : ∀ letter : alphabet,
    occurringEdge alphabet letter =
      occurringEdge S.alphabet (toAmbient letter)
  range_exactly_occurring : ∀ letter : S.alphabet,
    (∃ retained : alphabet, toAmbient retained = letter) ↔
      Symbolic.Substitution.OccursInInfiniteWord letter J.word

/-- The occurring ambient letters form a nonempty finite directed-edge
alphabet; forgetting the retained subtype is injective and has exactly the
occurring letters as its range. -/
private theorem finiteRetainedAlphabetData_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S) :
    Nonempty (FiniteRetainedAlphabetData F H S J) := by
  classical
  let liftAmbient : DirectedMarkovEdge H.vertices → S.alphabet :=
    fun edge => ⟨edge, S.contains_every_directed_edge edge⟩
  let alphabet : OccurringDirectedAlphabet H.vertices :=
    Finset.univ.filter fun edge : DirectedMarkovEdge H.vertices =>
      Symbolic.Substitution.OccursInInfiniteWord (liftAmbient edge) J.word
  have hliftAmbient (letter : S.alphabet) :
      liftAmbient letter.1 = letter := by
    apply Subtype.ext
    rfl
  have hheadOccurs :
      Symbolic.Substitution.OccursInInfiniteWord J.word.head J.word := by
    exact ⟨0, rfl⟩
  have hheadMem : (J.word.head).1 ∈ alphabet := by
    simp only [alphabet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hliftAmbient]
    exact hheadOccurs
  refine ⟨{
    alphabet := alphabet
    alphabet_nonempty := ⟨(J.word.head).1, hheadMem⟩
    toAmbient := fun letter => liftAmbient letter.1
    toAmbient_injective := ?_
    edge_forget := ?_
    range_exactly_occurring := ?_ }⟩
  · intro left right heq
    apply Subtype.ext
    exact congrArg (fun letter : S.alphabet => letter.1) heq
  · intro letter
    rfl
  · intro letter
    constructor
    · rintro ⟨retained, hretained⟩
      have hoccurs : Symbolic.Substitution.OccursInInfiniteWord
          (liftAmbient retained.1) J.word := by
        exact (Finset.mem_filter.mp retained.2).2
      rw [hretained] at hoccurs
      exact hoccurs
    · intro hoccurs
      have hedgeMem : letter.1 ∈ alphabet := by
        simp only [alphabet, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hliftAmbient]
        exact hoccurs
      refine ⟨⟨letter.1, hedgeMem⟩, ?_⟩
      exact hliftAmbient letter

/-! ### C5c--f: lifted word, restricted images, and fixedness -/

/-- The common word lifted to the retained alphabet.  Every retained letter
occurs, by the exact range characterization rather than by a later pruning
argument. -/
private structure LiftedRetainedWordData
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (R : FiniteRetainedAlphabetData F H S J) where
  word : Symbolic.InfiniteWord R.alphabet
  forget_word : ∀ n : ℕ, R.toAmbient (word n) = J.word n
  every_letter_occurs : ∀ letter : R.alphabet,
    Symbolic.Substitution.OccursInInfiniteWord letter word

/-- Lift the ambient common word letter by letter to the exact retained
alphabet, preserving all positions and occurrence of every retained letter. -/
private theorem liftedRetainedWordData_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (R : FiniteRetainedAlphabetData F H S J) :
    Nonempty (LiftedRetainedWordData F H S J R) := by
  classical
  have hexists (n : ℕ) : ∃ retained : R.alphabet,
      R.toAmbient retained = J.word n := by
    apply (R.range_exactly_occurring (J.word n)).2
    exact ⟨n, rfl⟩
  let word : Symbolic.InfiniteWord R.alphabet :=
    fun n => Classical.choose (hexists n)
  have hforget (n : ℕ) : R.toAmbient (word n) = J.word n :=
    Classical.choose_spec (hexists n)
  refine ⟨{
    word := word
    forget_word := hforget
    every_letter_occurs := ?_ }⟩
  intro letter
  have hambient : Symbolic.Substitution.OccursInInfiniteWord
      (R.toAmbient letter) J.word :=
    (R.range_exactly_occurring (R.toAmbient letter)).1 ⟨letter, rfl⟩
  rcases hambient with ⟨n, hn⟩
  refine ⟨n, R.toAmbient_injective ?_⟩
  exact (hforget n).trans hn

/-- Occurrence closure lifts every ambient image block to a nonempty word on
the retained alphabet, without changing the block after forgetting. -/
private theorem retainedSubstitution_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (R : FiniteRetainedAlphabetData F H S J)
    (source : Symbolic.Substitution S.alphabet)
    (hfixed : source.IsFixedPoint J.word) :
    ∃ restricted : Symbolic.Substitution R.alphabet,
      ∀ letter : R.alphabet,
        (restricted letter).map R.toAmbient = source (R.toAmbient letter) := by
  classical
  let fallback : R.alphabet :=
    ⟨Classical.choose R.alphabet_nonempty,
      Classical.choose_spec R.alphabet_nonempty⟩
  have hsourceOccurs (letter : R.alphabet) :
      Symbolic.Substitution.OccursInInfiniteWord
        (R.toAmbient letter) J.word :=
    (R.range_exactly_occurring (R.toAmbient letter)).1 ⟨letter, rfl⟩
  have houtputOccurs (letter : R.alphabet) {output : S.alphabet}
      (houtput : output ∈ source (R.toAmbient letter)) :
      Symbolic.Substitution.OccursInInfiniteWord output J.word :=
    occurs_of_mem_image_of_fixedPoint hfixed (hsourceOccurs letter) houtput
  let liftOutput (output : S.alphabet) : R.alphabet :=
    if hoccurs : Symbolic.Substitution.OccursInInfiniteWord output J.word then
      Classical.choose ((R.range_exactly_occurring output).2 hoccurs)
    else fallback
  have hliftOutput {output : S.alphabet}
      (hoccurs : Symbolic.Substitution.OccursInInfiniteWord output J.word) :
      R.toAmbient (liftOutput output) = output := by
    simp only [liftOutput, dif_pos hoccurs]
    exact Classical.choose_spec ((R.range_exactly_occurring output).2 hoccurs)
  let restricted : Symbolic.Substitution R.alphabet :=
    { image := fun letter =>
        (source (R.toAmbient letter)).map liftOutput
      image_ne_nil := fun letter hnil =>
        source.image_ne_nil (R.toAmbient letter)
          (List.map_eq_nil_iff.mp hnil) }
  refine ⟨restricted, ?_⟩
  intro letter
  simp only [restricted, List.map_map]
  calc
    List.map (R.toAmbient ∘ liftOutput) (source (R.toAmbient letter)) =
        List.map id (source (R.toAmbient letter)) := by
      apply List.map_congr_left
      intro output houtput
      change R.toAmbient (liftOutput output) = output
      exact hliftOutput (houtputOccurs letter houtput)
    _ = source (R.toAmbient letter) := by simp

/-- Infinite substitution commutes with an injective letter embedding when
every finite image block commutes with that embedding. -/
private theorem mapInfinite_embedding_naturality
    {α β : Type*} (embed : β → α) (hinjective : Function.Injective embed)
    {source : Symbolic.Substitution α}
    {restricted : Symbolic.Substitution β}
    (himage : ∀ letter : β,
      (restricted letter).map embed = source (embed letter))
    (word : Symbolic.InfiniteWord β) :
    ∀ n : ℕ, embed (restricted.mapInfinite word n) =
      source.mapInfinite (fun k => embed (word k)) n := by
  have hstream :
      Stream'.map embed (restricted.mapInfinite word) =
        source.mapInfinite (Stream'.map embed word) := by
    let Relation : Symbolic.InfiniteWord α → Symbolic.InfiniteWord α → Prop :=
      fun left right =>
        ∃ (pref : Symbolic.Word α) (input : Symbolic.InfiniteWord β),
          left = pref ++ₛ Stream'.map embed (restricted.mapInfinite input) ∧
          right = pref ++ₛ source.mapInfinite (Stream'.map embed input)
    apply Stream'.eq_of_bisim Relation
    · intro left right hrelation
      rcases hrelation with ⟨pref, input, rfl, rfl⟩
      cases pref with
      | cons letter rest =>
          simp only [Stream'.cons_append_stream, Stream'.head_cons,
            Stream'.tail_cons]
          exact ⟨True.intro, ⟨rest, input, rfl, rfl⟩⟩
      | nil =>
          simp only [Stream'.nil_append_stream]
          have hleft :
              Stream'.map embed (restricted.mapInfinite input) =
                List.map embed (restricted input.head) ++ₛ
                  Stream'.map embed (restricted.mapInfinite input.tail) := by
            rw [restricted.mapInfinite_eq_append_first_image,
              Stream'.map_append_stream]
          have hright :
              source.mapInfinite (Stream'.map embed input) =
                source (embed input.head) ++ₛ
                  source.mapInfinite (Stream'.map embed input.tail) := by
            rw [source.mapInfinite_eq_append_first_image]
            rfl
          rw [hleft, hright, himage input.head]
          obtain ⟨letter, rest, hrest⟩ := List.exists_cons_of_ne_nil
            (source.image_ne_nil (embed input.head))
          rw [hrest, Stream'.cons_append_stream, Stream'.head_cons,
            Stream'.tail_cons]
          exact ⟨rfl, ⟨rest, input.tail, rfl, rfl⟩⟩
    · exact ⟨[], word, rfl, rfl⟩
  intro n
  exact congrFun hstream n

/-- Naturality and injectivity descend ambient fixedness to the retained
substitution and lifted word. -/
private theorem restricted_fixedPoint_of_embedding
    {α β : Type*} (embed : β → α) (hinjective : Function.Injective embed)
    {source : Symbolic.Substitution α}
    {restricted : Symbolic.Substitution β}
    {ambientWord : Symbolic.InfiniteWord α}
    {word : Symbolic.InfiniteWord β}
    (himage : ∀ letter : β,
      (restricted letter).map embed = source (embed letter))
    (hword : ∀ n : ℕ, embed (word n) = ambientWord n)
    (hfixed : source.IsFixedPoint ambientWord) :
    restricted.IsFixedPoint word := by
  apply funext
  intro n
  apply hinjective
  calc
    embed (restricted.mapInfinite word n) =
        source.mapInfinite (fun k => embed (word k)) n :=
      mapInfinite_embedding_naturality embed hinjective himage word n
    _ = source.mapInfinite ambientWord n := by
      congr 1
      funext k
      exact hword k
    _ = ambientWord n := congrFun hfixed n
    _ = embed (word n) := (hword n).symm

/-- The two restricted substitutions, with exact forgetful image equations
and descended common fixedness. -/
private structure RestrictedSubstitutionPairData
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J)
    (R : FiniteRetainedAlphabetData F H S J)
    (W : LiftedRetainedWordData F H S J R) where
  substitutionA : Symbolic.Substitution R.alphabet
  substitutionB : Symbolic.Substitution R.alphabet
  imageA_forget : ∀ letter : R.alphabet,
    (substitutionA letter).map R.toAmbient =
      S.substitutionA (R.toAmbient letter)
  imageB_forget : ∀ letter : R.alphabet,
    (substitutionB letter).map R.toAmbient =
      S.substitutionB (R.toAmbient letter)
  fixedA : substitutionA.IsFixedPoint W.word
  fixedB : substitutionB.IsFixedPoint W.word

/-- Restrict both substitutions simultaneously and descend their common
fixed word through the injective retained embedding. -/
private theorem restrictedSubstitutionPairData_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J)
    (R : FiniteRetainedAlphabetData F H S J)
    (W : LiftedRetainedWordData F H S J R) :
    Nonempty (RestrictedSubstitutionPairData F H S J C R W) := by
  let hsubstitutionA :=
    retainedSubstitution_exists F H S J R S.substitutionA C.fixedA
  let hsubstitutionB :=
    retainedSubstitution_exists F H S J R S.substitutionB C.fixedB
  let substitutionA : Symbolic.Substitution R.alphabet :=
    Classical.choose hsubstitutionA
  let substitutionB : Symbolic.Substitution R.alphabet :=
    Classical.choose hsubstitutionB
  have himageA : ∀ letter : R.alphabet,
      (substitutionA letter).map R.toAmbient =
        S.substitutionA (R.toAmbient letter) :=
    Classical.choose_spec hsubstitutionA
  have himageB : ∀ letter : R.alphabet,
      (substitutionB letter).map R.toAmbient =
        S.substitutionB (R.toAmbient letter) :=
    Classical.choose_spec hsubstitutionB
  have hfixedA : substitutionA.IsFixedPoint W.word :=
    restricted_fixedPoint_of_embedding R.toAmbient R.toAmbient_injective
      himageA W.forget_word C.fixedA
  have hfixedB : substitutionB.IsFixedPoint W.word :=
    restricted_fixedPoint_of_embedding R.toAmbient R.toAmbient_injective
      himageB W.forget_word C.fixedB
  exact ⟨{
    substitutionA := substitutionA
    substitutionB := substitutionB
    imageA_forget := himageA
    imageB_forget := himageB
    fixedA := hfixedA
    fixedB := hfixedB }⟩

/-! ### C5g: common seed and prolongability -/

private structure RetainedSeedData
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J)
    (R : FiniteRetainedAlphabetData F H S J)
    (W : LiftedRetainedWordData F H S J R)
    (Q : RestrictedSubstitutionPairData F H S J C R W) where
  seed : R.alphabet
  head_eq_seed : W.word.head = seed
  prolongableA : Q.substitutionA.ProlongableOn seed
  prolongableB : Q.substitutionB.ProlongableOn seed

/-- The ambient common seed lifts to the head of the retained word, and the
two nonempty prolongation tails lift blockwise. -/
private theorem retainedSeedData_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J)
    (R : FiniteRetainedAlphabetData F H S J)
    (W : LiftedRetainedWordData F H S J R)
    (Q : RestrictedSubstitutionPairData F H S J C R W) :
    Nonempty (RetainedSeedData F H S J C R W Q) := by
  have hseed : R.toAmbient W.word.head = C.seed := by
    calc
      R.toAmbient W.word.head = J.word.head := W.forget_word 0
      _ = C.seed := C.head_eq_seed
  have liftProlongable
      (source : Symbolic.Substitution S.alphabet)
      (restricted : Symbolic.Substitution R.alphabet)
      (himage : ∀ letter : R.alphabet,
        (restricted letter).map R.toAmbient = source (R.toAmbient letter))
      (hsource : source.ProlongableOn C.seed) :
      restricted.ProlongableOn W.word.head := by
    obtain ⟨ambientTail, hambientTail, hambientImage⟩ := hsource
    obtain ⟨first, tail, hrestrictedImage⟩ := List.exists_cons_of_ne_nil
      (restricted.image_ne_nil W.word.head)
    have hforgetImage := himage W.word.head
    rw [hrestrictedImage, List.map_cons, hseed, hambientImage] at hforgetImage
    injection hforgetImage with hfirst htail
    have hfirstEq : first = W.word.head :=
      R.toAmbient_injective (hfirst.trans hseed.symm)
    subst first
    refine ⟨tail, ?_, hrestrictedImage⟩
    intro htailNil
    subst tail
    apply hambientTail
    exact htail.symm
  exact ⟨{
    seed := W.word.head
    head_eq_seed := rfl
    prolongableA :=
      liftProlongable S.substitutionA Q.substitutionA
        Q.imageA_forget C.prolongableA
    prolongableB :=
      liftProlongable S.substitutionB Q.substitutionB
        Q.imageB_forget C.prolongableB }⟩

/-! ### C5h: retained metric laws -/

private structure RetainedMetricData
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J)
    (R : FiniteRetainedAlphabetData F H S J)
    (W : LiftedRetainedWordData F H S J R)
    (Q : RestrictedSubstitutionPairData F H S J C R W) where
  letterLength : R.alphabet → ℝ
  letterLength_eq_ambient : ∀ letter,
    letterLength letter = S.letterLength (R.toAmbient letter)
  letterLength_pos : ∀ letter, 0 < letterLength letter
  scalesA : SubstitutionScalesLetterLengths Q.substitutionA letterLength a
  scalesB : SubstitutionScalesLetterLengths Q.substitutionB letterLength b

/-- Forgetful image equations transport the positive geometric length vector
and both exact substitution scaling identities. -/
private theorem retainedMetricData_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J)
    (R : FiniteRetainedAlphabetData F H S J)
    (W : LiftedRetainedWordData F H S J R)
    (Q : RestrictedSubstitutionPairData F H S J C R W) :
    Nonempty (RetainedMetricData F H S J C R W Q) := by
  let letterLength : R.alphabet → ℝ :=
    fun letter => S.letterLength (R.toAmbient letter)
  have hscalesA : SubstitutionScalesLetterLengths
      Q.substitutionA letterLength a := by
    intro source
    calc
      wordMetricLength letterLength (Q.substitutionA source) =
          wordMetricLength S.letterLength
            ((Q.substitutionA source).map R.toAmbient) := by
        simp only [wordMetricLength, letterLength, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro letter hletter
        rfl
      _ = wordMetricLength S.letterLength
          (S.substitutionA (R.toAmbient source)) := by
        rw [Q.imageA_forget]
      _ = a * S.letterLength (R.toAmbient source) :=
        S.scalesA (R.toAmbient source)
      _ = a * letterLength source := rfl
  have hscalesB : SubstitutionScalesLetterLengths
      Q.substitutionB letterLength b := by
    intro source
    calc
      wordMetricLength letterLength (Q.substitutionB source) =
          wordMetricLength S.letterLength
            ((Q.substitutionB source).map R.toAmbient) := by
        simp only [wordMetricLength, letterLength, List.map_map]
        apply congrArg List.sum
        apply List.map_congr_left
        intro letter hletter
        rfl
      _ = wordMetricLength S.letterLength
          (S.substitutionB (R.toAmbient source)) := by
        rw [Q.imageB_forget]
      _ = b * S.letterLength (R.toAmbient source) :=
        S.scalesB (R.toAmbient source)
      _ = b * letterLength source := rfl
  exact ⟨{
    letterLength := letterLength
    letterLength_eq_ambient := fun _ => rfl
    letterLength_pos := fun letter => S.letterLength_pos (R.toAmbient letter)
    scalesA := hscalesA
    scalesB := hscalesB }⟩

/-! ### C5i: geometric itinerary transport -/

/-- The lifted word traverses the same geometric directed edges at the same
prefix times after restriction. -/
private theorem retained_itinerary
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J)
    (R : FiniteRetainedAlphabetData F H S J)
    (W : LiftedRetainedWordData F H S J R)
    (Q : RestrictedSubstitutionPairData F H S J C R W)
    (M : RetainedMetricData F H S J C R W Q) :
    HasLiteralUnitSpeedItinerary F.ray
      (occurringEdge R.alphabet) M.letterLength W.word := by
  refine ⟨?_, ?_, ?_⟩
  · intro letter
    calc
      M.letterLength letter = S.letterLength (R.toAmbient letter) :=
        M.letterLength_eq_ambient letter
      _ = (occurringEdge S.alphabet (R.toAmbient letter)).length :=
        S.letterLength_eq_edge (R.toAmbient letter)
      _ = (occurringEdge R.alphabet letter).length := by
        rw [R.edge_forget]
  · intro n
    have hambient := J.itinerary.2.1 n
    rw [← W.forget_word n, ← W.forget_word (n + 1)] at hambient
    simpa only [R.edge_forget] using hambient
  · intro n
    have hambient := J.itinerary.2.2 n
    have hprefix :
        prefixMetricLength M.letterLength W.word n =
          prefixMetricLength S.letterLength J.word n := by
      simp only [prefixMetricLength]
      apply Finset.sum_congr rfl
      intro k hk
      rw [M.letterLength_eq_ambient, W.forget_word]
    rw [hprefix, R.edge_forget, W.forget_word]
    exact hambient

/-- **C5.** Restrict both substitutions and the ray word to exactly the
letters occurring in that word.  Nonerasing is part of `Substitution`, and
fixedness, common prolongability, metric scaling, and occurrence of every
remaining letter survive the restriction. -/
theorem occurringAlphabetCoding_exists
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    (H : CommonMarkovHullData A B F)
    (S : DirectedSubstitutionPairData A B F H)
    (J : FoldItineraryData A B F H S)
    (C : CommonFixedCodingData A B F H S J) :
    Nonempty (OccurringAlphabetCodingData A B F H S J C) := by
  let R : FiniteRetainedAlphabetData F H S J :=
    Classical.choice (finiteRetainedAlphabetData_exists F H S J)
  let W : LiftedRetainedWordData F H S J R :=
    Classical.choice (liftedRetainedWordData_exists F H S J R)
  let Q : RestrictedSubstitutionPairData F H S J C R W :=
    Classical.choice (restrictedSubstitutionPairData_exists F H S J C R W)
  let D : RetainedSeedData F H S J C R W Q :=
    Classical.choice (retainedSeedData_exists F H S J C R W Q)
  let M : RetainedMetricData F H S J C R W Q :=
    Classical.choice (retainedMetricData_exists F H S J C R W Q)
  refine ⟨{
    alphabet := R.alphabet
    alphabet_nonempty := R.alphabet_nonempty
    toAmbient := R.toAmbient
    toAmbient_injective := R.toAmbient_injective
    range_exactly_occurring := R.range_exactly_occurring
    substitutionA := Q.substitutionA
    substitutionB := Q.substitutionB
    word := W.word
    forget_word := W.forget_word
    imageA_forget := Q.imageA_forget
    imageB_forget := Q.imageB_forget
    fixedA := Q.fixedA
    fixedB := Q.fixedB
    every_letter_occurs := W.every_letter_occurs
    seed := D.seed
    head_eq_seed := D.head_eq_seed
    prolongableA := D.prolongableA
    prolongableB := D.prolongableB
    letterLength := M.letterLength
    letterLength_eq_ambient := M.letterLength_eq_ambient
    letterLength_pos := M.letterLength_pos
    scalesA := M.scalesA
    scalesB := M.scalesB
    itinerary := retained_itinerary F H S J C R W Q M }⟩

/-! ## C6: growing substitutions and their dominant eigenvalues -/

private theorem wordMetricLength_append {α : Type*} (length : α → ℝ)
    (u v : Symbolic.Word α) :
    wordMetricLength length (u ++ v) =
      wordMetricLength length u + wordMetricLength length v := by
  simp [wordMetricLength]

private theorem wordMetricLength_mapWord_of_scales
    {α : Type*} {σ : Symbolic.Substitution α} {length : α → ℝ}
    {scale : ℝ} (hscale : SubstitutionScalesLetterLengths σ length scale)
    (w : Symbolic.Word α) :
    wordMetricLength length (σ.mapWord w) =
      scale * wordMetricLength length w := by
  induction w with
  | nil => simp [wordMetricLength]
  | cons a w ih =>
      rw [Symbolic.Substitution.mapWord_cons, wordMetricLength_append,
        hscale a, ih]
      simp [wordMetricLength, mul_add]

private theorem wordMetricLength_iterateLetter_of_scales
    {α : Type*} {σ : Symbolic.Substitution α} {length : α → ℝ}
    {scale : ℝ} (hscale : SubstitutionScalesLetterLengths σ length scale)
    (seed : α) (n : ℕ) :
    wordMetricLength length (σ.iterateLetter n seed) =
      scale ^ n * length seed := by
  induction n with
  | zero => simp [wordMetricLength]
  | succ n ih =>
      rw [Symbolic.Substitution.iterateLetter_succ,
        wordMetricLength_mapWord_of_scales hscale, ih, pow_succ]
      ring

private theorem wordMetricLength_le_length_mul_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (length : α → ℝ) (hlength : ∀ a, 0 ≤ length a)
    (w : Symbolic.Word α) :
    wordMetricLength length w ≤
      (w.length : ℝ) * ∑ a : α, length a := by
  induction w with
  | nil => simp [wordMetricLength]
  | cons a w ih =>
      have ha : length a ≤ ∑ z : α, length z := by
        exact Finset.single_le_sum (fun z _hz ↦ hlength z) (Finset.mem_univ a)
      simp only [wordMetricLength, List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      have hsum : 0 ≤ ∑ z : α, length z :=
        Finset.sum_nonneg fun z _hz ↦ hlength z
      change (w.map length).sum ≤ (w.length : ℝ) * ∑ z : α, length z at ih
      nlinarith

/-- Metric expansion by a factor greater than one forces the length of every
iterated nonerasing substitution image to tend to infinity. -/
theorem growing_of_positive_metric_scaling
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Symbolic.Substitution α) (length : α → ℝ) (scale : ℝ)
    (hlength : ∀ letter, 0 < length letter)
    (hscale : SubstitutionScalesLetterLengths σ length scale)
    (hone : 1 < scale) :
    σ.IsGrowing := by
  classical
  intro seed bound
  let total : ℝ := ∑ a : α, length a
  have hseed_le : length seed ≤ total := by
    dsimp [total]
    exact Finset.single_le_sum (fun z _hz ↦ (hlength z).le)
      (Finset.mem_univ seed)
  have htotal_pos : 0 < total := (hlength seed).trans_le hseed_le
  have hevent : ∀ᶠ n : ℕ in Filter.atTop,
      ((bound : ℝ) * total) / length seed < scale ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop _
  obtain ⟨n, hn'⟩ := Filter.eventually_atTop.1 hevent
  have hn := hn' n le_rfl
  have hlarge : (bound : ℝ) * total < scale ^ n * length seed := by
    exact (div_lt_iff₀ (hlength seed)).mp hn
  refine ⟨n, le_of_not_gt fun hword ↦ ?_⟩
  have hword_real : ((σ.iterateLetter n seed).length : ℝ) < (bound : ℝ) := by
    exact_mod_cast hword
  have hupper := wordMetricLength_le_length_mul_sum length
    (fun a ↦ (hlength a).le) (σ.iterateLetter n seed)
  rw [wordMetricLength_iterateLetter_of_scales hscale] at hupper
  have hmul := mul_lt_mul_of_pos_right hword_real htotal_pos
  dsimp [total] at htotal_pos hlarge hmul ⊢
  nlinarith

private theorem wordMetricLength_eq_count_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (length : α → ℝ) (w : Symbolic.Word α) :
    wordMetricLength length w =
      ∑ a : α, (w.count a : ℝ) * length a := by
  induction w with
  | nil => simp [wordMetricLength]
  | cons c w ih =>
      rw [wordMetricLength]
      change length c + (w.map length).sum = _
      rw [← wordMetricLength, ih]
      calc
        length c + ∑ a : α, (w.count a : ℝ) * length a =
            (∑ a : α, if a = c then length a else 0) +
              ∑ a : α, (w.count a : ℝ) * length a := by simp
        _ = ∑ a : α,
              ((if a = c then length a else 0) +
                (w.count a : ℝ) * length a) :=
          Finset.sum_add_distrib.symm
        _ = ∑ a : α, ((c :: w).count a : ℝ) * length a := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hac : a = c
          · subst a
            simp [add_mul, add_comm]
          · simp [hac, Ne.symm hac]

private theorem substitution_metric_lengths_give_incidence_identity
    {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Symbolic.Substitution α} {length : α → ℝ} {scale : ℝ}
    (hlength : ∀ a, 0 < length a)
    (hscale : SubstitutionScalesLetterLengths σ length scale) :
    IsPositiveLengthEigenvector σ length scale := by
  refine ⟨hlength, ?_⟩
  intro source
  rw [incidenceTransposeMul]
  simpa [Symbolic.Substitution.incidenceMatrix] using
    (wordMetricLength_eq_count_sum length (σ source)).symm.trans
      (hscale source)

private def NatMatrixEigenvectorEquation
    {α : Type*} [Fintype α]
    (M : Matrix α α ℕ) (v : α → ℝ) (eigenvalue : ℝ) : Prop :=
  ∀ i : α, (∑ j : α, (M i j : ℝ) * v j) = eigenvalue * v i

private theorem positive_eigenvector_isDominant
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (M : Matrix α α ℕ) (v : α → ℝ) (eigenvalue : ℝ)
    (hv : ∀ i, 0 < v i)
    (heigen : NatMatrixEigenvectorEquation M v eigenvalue) :
    IsDominantEigenvalue M eigenvalue := by
  constructor
  · let w : α → ℂ := fun i => (v i : ℂ)
    have hw : w ≠ 0 := by
      intro hzero
      obtain ⟨i⟩ := ‹Nonempty α›
      have hi := congrFun hzero i
      simp only [w, Pi.zero_apply, Complex.ofReal_eq_zero] at hi
      exact (ne_of_gt (hv i)) hi
    refine ⟨w, hw, ?_⟩
    intro i
    have h := congrArg Complex.ofReal (heigen i)
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, w] using h
  · intro z hz
    rcases hz with ⟨w, hw, heigenz⟩
    have hwexists : ∃ k : α, w k ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (funext h)
    obtain ⟨k, hwk⟩ := hwexists
    obtain ⟨i, _hiMem, hiMax⟩ :=
      Finset.univ.exists_max_image (fun j => ‖w j‖ / v j)
        Finset.univ_nonempty
    have hratioK : 0 < ‖w k‖ / v k :=
      div_pos (norm_pos_iff.mpr hwk) (hv k)
    have hratioI : 0 < ‖w i‖ / v i :=
      hratioK.trans_le (hiMax k (Finset.mem_univ k))
    have hwiNorm : 0 < ‖w i‖ := by
      by_contra h
      have : ‖w i‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
      rw [this, zero_div] at hratioI
      exact (lt_irrefl 0) hratioI
    have hwbound (j : α) :
        ‖w j‖ ≤ (‖w i‖ / v i) * v j := by
      exact (div_le_iff₀ (hv j)).mp (hiMax j (Finset.mem_univ j))
    have htriangle :
        ‖z‖ * ‖w i‖ ≤ eigenvalue * ‖w i‖ := by
      calc
        ‖z‖ * ‖w i‖ = ‖z * w i‖ := (norm_mul z (w i)).symm
        _ = ‖∑ j : α, (M i j : ℂ) * w j‖ :=
          congrArg norm (heigenz i).symm
        _ ≤ ∑ j : α, ‖(M i j : ℂ) * w j‖ :=
          norm_sum_le Finset.univ _
        _ = ∑ j : α, (M i j : ℝ) * ‖w j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul]
          simp
        _ ≤ ∑ j : α, (M i j : ℝ) *
            ((‖w i‖ / v i) * v j) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hwbound j) (Nat.cast_nonneg _)
        _ = (‖w i‖ / v i) *
            (∑ j : α, (M i j : ℝ) * v j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (‖w i‖ / v i) * (eigenvalue * v i) := by
          rw [heigen i]
        _ = eigenvalue * ‖w i‖ := by
          field_simp [(ne_of_gt (hv i))]
    exact le_of_mul_le_mul_right htriangle hwiNorm

private def complexification {α : Type*}
    (M : Matrix α α ℕ) : Matrix α α ℂ :=
  M.map (Nat.castRingHom ℂ)

private theorem isComplexEigenvalue_iff_hasEigenvalue
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) (z : ℂ) :
    IsComplexEigenvalue M z ↔
      Module.End.HasEigenvalue (Matrix.toLin' (complexification M)) z := by
  constructor
  · rintro ⟨v, hv, heigen⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
    ext i
    simp only [Matrix.toLin'_apply, Matrix.mulVec, complexification,
      Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    exact heigen i
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    refine ⟨v, hv.2, ?_⟩
    have heigen := Module.End.mem_eigenspace_iff.mp hv.1
    intro i
    have hi := congrFun heigen i
    simpa only [Matrix.toLin'_apply, Matrix.mulVec, complexification,
      Matrix.map_apply, Pi.smul_apply, smul_eq_mul] using hi

private theorem isComplexEigenvalue_transpose_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) (z : ℂ) :
    IsComplexEigenvalue M.transpose z ↔ IsComplexEigenvalue M z := by
  rw [isComplexEigenvalue_iff_hasEigenvalue,
    isComplexEigenvalue_iff_hasEigenvalue,
    Module.End.hasEigenvalue_iff_mem_spectrum,
    Module.End.hasEigenvalue_iff_mem_spectrum,
    Matrix.spectrum_toLin', Matrix.spectrum_toLin',
    Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (complexification M).transpose.charpoly.IsRoot z ↔
    (complexification M).charpoly.IsRoot z
  rw [Matrix.charpoly_transpose]

private theorem dominantEigenvalue_transpose_iff
    {α : Type*} [Fintype α] (M : Matrix α α ℕ) (eigenvalue : ℝ) :
    IsDominantEigenvalue M.transpose eigenvalue ↔
      IsDominantEigenvalue M eigenvalue := by
  classical
  constructor
  · rintro ⟨heigen, hbound⟩
    refine ⟨(isComplexEigenvalue_transpose_iff M _).mp heigen, ?_⟩
    intro z hz
    exact hbound z ((isComplexEigenvalue_transpose_iff M z).mpr hz)
  · rintro ⟨heigen, hbound⟩
    refine ⟨(isComplexEigenvalue_transpose_iff M _).mpr heigen, ?_⟩
    intro z hz
    exact hbound z ((isComplexEigenvalue_transpose_iff M z).mp hz)

/-- A strictly positive geometric length vector satisfying the substitution
metric law identifies the scale as the dominant eigenvalue of the incidence
matrix.  This is the finite nonnegative-matrix (Collatz--Wielandt) step. -/
theorem dominantEigenvalue_of_positive_metric_scaling
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (σ : Symbolic.Substitution α) (length : α → ℝ) (scale : ℝ)
    (hlength : ∀ letter, 0 < length letter)
    (hscale : SubstitutionScalesLetterLengths σ length scale) :
    IsDominantEigenvalue σ.incidenceMatrix scale := by
  have hlengthEigen :=
    substitution_metric_lengths_give_incidence_identity hlength hscale
  have heigen : NatMatrixEigenvectorEquation
      σ.incidenceMatrix.transpose length scale := by
    intro source
    simpa [NatMatrixEigenvectorEquation, incidenceTransposeMul] using
      hlengthEigen.2 source
  have htranspose := positive_eigenvector_isDominant
    σ.incidenceMatrix.transpose length scale hlength heigen
  exact (dominantEigenvalue_transpose_iff σ.incidenceMatrix scale).mp htranspose

/-- Package C5 and the two metric consequences as the exact symbolic input
to Durand's theorem. -/
def commonGrowingFixedWordData
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b)
    {H : CommonMarkovHullData A B F}
    {S : DirectedSubstitutionPairData A B F H}
    {J : FoldItineraryData A B F H S}
    {C : CommonFixedCodingData A B F H S J}
    (R : OccurringAlphabetCodingData A B F H S J C) :
    CommonGrowingFixedWordData R.alphabet := by
  letI : Nonempty R.alphabet := R.alphabet_nonempty.to_subtype
  exact {
    substitutionA := R.substitutionA
    substitutionB := R.substitutionB
    seed := R.seed
    word := R.word
    fixedA := R.fixedA
    fixedB := R.fixedB
    prolongableA := R.prolongableA
    prolongableB := R.prolongableB
    every_letter_occurs := R.every_letter_occurs
    growingA := growing_of_positive_metric_scaling
      R.substitutionA R.letterLength a R.letterLength_pos R.scalesA F.one_lt_a
    growingB := growing_of_positive_metric_scaling
      R.substitutionB R.letterLength b R.letterLength_pos R.scalesB F.one_lt_b
    eigenvalueA := a
    eigenvalueB := b
    letterLength := R.letterLength
    letterLength_pos := R.letterLength_pos
    scalesA := R.scalesA
    scalesB := R.scalesB
    one_lt_eigenvalueA := F.one_lt_a
    one_lt_eigenvalueB := F.one_lt_b
    dominantA := dominantEigenvalue_of_positive_metric_scaling
      R.substitutionA R.letterLength a R.letterLength_pos R.scalesA
    dominantB := dominantEigenvalue_of_positive_metric_scaling
      R.substitutionB R.letterLength b R.letterLength_pos R.scalesB
    eigenvalues_independent := F.scales_independent }

/-! ## C7: Durand's Theorem 9, specialized with explicit hypotheses -/

/--
**Durand, Theorem 9 (specialized form used here).**

Two nonerasing substitutions on one finite alphabet, prolongable on the same
letter and fixing the same one-sided word in which every letter occurs, scale
one common strictly positive letter metric.  If the two scale factors are
greater than one and multiplicatively independent, then their common fixed
word is ultimately periodic.

The nonerasing assumptions are displayed explicitly even though they are
also invariant fields of `Symbolic.Substitution`.  This theorem is the sole
external symbolic periodicity boundary in the simplified proof.
-/
theorem durand_theorem9_specialization
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Symbolic.Substitution α)
    (seed : α) (word : Symbolic.InfiniteWord α)
    (hσ_nonerasing : ∀ letter, σ letter ≠ [])
    (hτ_nonerasing : ∀ letter, τ letter ≠ [])
    (hσ_prolongable : σ.ProlongableOn seed)
    (hτ_prolongable : τ.ProlongableOn seed)
    (hσ_fixed : σ.IsFixedPoint word)
    (hτ_fixed : τ.IsFixedPoint word)
    (hevery : ∀ letter,
      Symbolic.Substitution.OccursInInfiniteWord letter word)
    (letterLength : α → ℝ)
    (hlength : ∀ letter, 0 < letterLength letter)
    (eigenvalueσ eigenvalueτ : ℝ)
    (honeσ : 1 < eigenvalueσ) (honeτ : 1 < eigenvalueτ)
    (hscalesσ : SubstitutionScalesLetterLengths σ letterLength eigenvalueσ)
    (hscalesτ : SubstitutionScalesLetterLengths τ letterLength eigenvalueτ)
    (hindependent :
      MultiplicativelyIndependent eigenvalueσ eigenvalueτ) :
    Symbolic.IsUltimatelyPeriodic word := by
  letI : Nonempty α := ⟨seed⟩
  exact Symbolic.metricTheorem9_synchronized
    ({
      nonerasing := hσ_nonerasing
      prolongable := hσ_prolongable
      fixed := hσ_fixed
      every_letter_occurs := hevery
      growing := growing_of_positive_metric_scaling
        σ letterLength eigenvalueσ hlength hscalesσ honeσ
      one_lt_eigenvalue := honeσ
      dominant := dominantEigenvalue_of_positive_metric_scaling
        σ letterLength eigenvalueσ hlength hscalesσ
      letterLength_pos := hlength
      scales := hscalesσ } :
      Symbolic.MetricGrowingFixedPresentation σ seed word eigenvalueσ
        letterLength)
    ({
      nonerasing := hτ_nonerasing
      prolongable := hτ_prolongable
      fixed := hτ_fixed
      every_letter_occurs := hevery
      growing := growing_of_positive_metric_scaling
        τ letterLength eigenvalueτ hlength hscalesτ honeτ
      one_lt_eigenvalue := honeτ
      dominant := dominantEigenvalue_of_positive_metric_scaling
        τ letterLength eigenvalueτ hlength hscalesτ
      letterLength_pos := hlength
      scales := hscalesτ } :
      Symbolic.MetricGrowingFixedPresentation τ seed word eigenvalueτ
        letterLength)
    hindependent

/-- Apply the explicit Durand specialization to the C6 package. -/
theorem ultimatelyPeriodic_of_commonGrowingFixedWordData
    {α : Type*} [Fintype α] [DecidableEq α]
    (D : CommonGrowingFixedWordData α) :
    Symbolic.IsUltimatelyPeriodic D.word := by
  exact durand_theorem9_specialization
    D.substitutionA D.substitutionB D.seed D.word
    D.substitutionA.image_ne_nil D.substitutionB.image_ne_nil
    D.prolongableA D.prolongableB D.fixedA D.fixedB
    D.every_letter_occurs D.letterLength D.letterLength_pos
    D.eigenvalueA D.eigenvalueB
    D.one_lt_eigenvalueA D.one_lt_eigenvalueB
    D.scalesA D.scalesB D.eigenvalues_independent

/-! ## C8: from the symbolic period to the physical metric period -/

/-- An ultimately periodic literal edge itinerary with positive geometric
letter lengths gives an eventual period measured by the total length of one
period block. -/
theorem eventuallyPeriodicOnRay_of_ultimatelyPeriodic_itinerary
    {K : Finset I} {α : Type*} [Fintype α] [DecidableEq α]
    (ψ : ℝ → I) (edge : α → DirectedMarkovEdge K)
    (length : α → ℝ) (word : Symbolic.InfiniteWord α)
    (hlength : ∀ letter, 0 < length letter)
    (hitinerary : HasLiteralUnitSpeedItinerary ψ edge length word)
    (hperiodic : Symbolic.IsUltimatelyPeriodic word) :
    EventuallyPeriodicOnRay ψ := by
  classical
  rcases hperiodic with ⟨start, period, hperiodPos, hwordPeriod⟩
  let L : ℕ → ℝ := prefixMetricLength length word
  have hLsucc (n : ℕ) : L (n + 1) = L n + length (word n) := by
    simp [L, prefixMetricLength, Finset.sum_range_succ]
  have hLstrict : StrictMono L :=
    strictMono_nat_of_lt_succ fun n => by
      rw [hLsucc]
      exact lt_add_of_pos_right _ (hlength (word n))
  have hLnonneg (n : ℕ) : 0 ≤ L n := by
    dsimp [L, prefixMetricLength]
    exact Finset.sum_nonneg fun i _ => (hlength (word i)).le
  let P : ℝ := L (start + period) - L start
  have hPpos : 0 < P := by
    dsimp [P]
    exact sub_pos.mpr (hLstrict (by omega))
  have hblock (n : ℕ) (hn : start ≤ n) :
      L (n + period) = L n + P := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero =>
        dsimp [P]
        ring
    | succ k ih =>
        have hw := hwordPeriod (start + k) (by omega)
        calc
          L (start + (k + 1) + period) =
              L ((start + k + period) + 1) := by
            congr 1
            omega
          _ = L (start + k + period) + length (word (start + k + period)) :=
            hLsucc _
          _ = (L (start + k) + P) + length (word (start + k)) := by
            rw [ih (by omega), hw]
          _ = (L (start + k) + length (word (start + k))) + P := by ring
          _ = L (start + (k + 1)) + P := by
            rw [show start + (k + 1) = (start + k) + 1 by omega, hLsucc]
  letI : Nonempty α := ⟨word 0⟩
  obtain ⟨shortest, _hshortestMem, hshortest⟩ :=
    Finset.exists_min_image Finset.univ length Finset.univ_nonempty
  let δ : ℝ := length shortest
  have hδpos : 0 < δ := hlength shortest
  have hδle (a : α) : δ ≤ length a :=
    hshortest a (Finset.mem_univ a)
  have hLlower : ∀ n : ℕ, (n : ℝ) * δ ≤ L n := by
    intro n
    induction n with
    | zero => simp [L, prefixMetricLength]
    | succ n ih =>
        rw [hLsucc]
        have hδword := hδle (word n)
        push_cast
        nlinarith
  refine ⟨L start, P, hLnonneg start, hPpos, ?_⟩
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  let upper : ℕ := max (start + 1) N
  have hNupper : N ≤ upper := le_max_right _ _
  have hstartUpper : start < upper :=
    lt_of_lt_of_le (Nat.lt_succ_self start) (le_max_left _ _)
  have htUpper : t < L upper := by
    have htNδ : t < (N : ℝ) * δ := (div_lt_iff₀ hδpos).mp hN
    have hcast : (N : ℝ) ≤ (upper : ℝ) := by exact_mod_cast hNupper
    exact lt_of_lt_of_le htNδ
      ((mul_le_mul_of_nonneg_right hcast hδpos.le).trans (hLlower upper))
  let candidates : Finset ℕ :=
    (Finset.range (upper + 1)).filter (fun n => L n ≤ t)
  have hstartCandidate : start ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ht⟩
  have hcandidates : candidates.Nonempty := ⟨start, hstartCandidate⟩
  let n : ℕ := candidates.max' hcandidates
  have hnCandidate : n ∈ candidates := Finset.max'_mem candidates hcandidates
  have hnRange : n < upper + 1 := by
    simpa using (Finset.mem_filter.mp hnCandidate).1
  have hLn : L n ≤ t := (Finset.mem_filter.mp hnCandidate).2
  have hstartn : start ≤ n := by
    exact Finset.le_max' candidates start hstartCandidate
  have hnUpper : n < upper := by
    have hnle : n ≤ upper := by omega
    apply lt_of_le_of_ne hnle
    intro hEq
    have hLupper : L upper ≤ t := by simpa [hEq] using hLn
    exact (not_lt_of_ge hLupper) htUpper
  have htNext : t < L (n + 1) := by
    apply lt_of_not_ge
    intro hnext
    have hnextCandidate : n + 1 ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hnext⟩
    have := Finset.le_max' candidates (n + 1) hnextCandidate
    omega
  let u : ℝ := t - L n
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hulength : u ≤ length (word n) := by
    rw [hLsucc] at htNext
    dsimp [u]
    linarith
  have huEdge : u ≤ (edge (word n)).length := by
    rw [← hitinerary.1 (word n)]
    exact hulength
  have huEdgePeriod : u ≤ (edge (word (n + period))).length := by
    rw [hwordPeriod n hstartn]
    exact huEdge
  have htraverse := hitinerary.2.2 n u hu0 huEdge
  have htraversePeriod :=
    hitinerary.2.2 (n + period) u hu0 huEdgePeriod
  apply Subtype.ext
  change (ψ (t + P) : ℝ) = (ψ t : ℝ)
  calc
    (ψ (t + P) : ℝ) = (ψ (L (n + period) + u) : ℝ) := by
      have harg : t + P = L (n + period) + u := by
        rw [hblock n hstartn]
        dsimp [u]
        ring
      rw [harg]
    _ = match (edge (word (n + period))).forward with
        | true => ((edge (word (n + period))).lower : ℝ) + u
        | false => ((edge (word (n + period))).upper : ℝ) - u :=
      htraversePeriod
    _ = match (edge (word n)).forward with
        | true => ((edge (word n)).lower : ℝ) + u
        | false => ((edge (word n)).upper : ℝ) - u := by
      rw [hwordPeriod n hstartn]
    _ = (ψ (L n + u) : ℝ) := htraverse.symm
    _ = (ψ t : ℝ) := by
      have harg : L n + u = t := by
        dsimp [u]
        ring
      rw [harg]

/-- **C1--C8.** Every two-scale fold package (whose construction has already
used returned-power irreducibility to obtain its dense range) is eventually
periodic on its physical nonnegative parameter ray. -/
theorem twoScaleFold_eventuallyPeriodic
    {A B : IntervalMap} {a b : ℝ} (F : TwoScaleFoldData A B a b) :
    EventuallyPeriodicOnRay F.ray := by
  let H := Classical.choice (commonMarkovHull_exists F)
  let S := Classical.choice (directedSubstitutionPair_exists F H)
  let J := Classical.choice (foldItinerary_exists F H S)
  let C := Classical.choice (commonFixedCoding_exists F H S J)
  let R := Classical.choice (occurringAlphabetCoding_exists F H S J C)
  have hperiodic : Symbolic.IsUltimatelyPeriodic R.word :=
    ultimatelyPeriodic_of_commonGrowingFixedWordData
      (commonGrowingFixedWordData F R)
  exact eventuallyPeriodicOnRay_of_ultimatelyPeriodic_itinerary
    F.ray (occurringEdge R.alphabet) R.letterLength R.word
    R.letterLength_pos R.itinerary hperiodic

end

end CommutingIntervalSimplified
