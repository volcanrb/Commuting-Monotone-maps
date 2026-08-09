import CommutingInterval.SymbolicDefs
import CommutingInterval.ConstantSlopeDefs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.List
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Symbolic support for the piecewise-linear two-scale argument

This module contains the symbolic and metric ingredients used by the exact
directed-edge coding and return-word comparison.

* The directed-edge, common-ray, Perron-power, word-combinatorics,
  return-factorization, primitive-substitution, and finite-SCC development
  from `DirectedMarkovEdge` through
  `Symbolic.Substitution.exists_sccDecomposition`.  This contiguous range
  is retained because the public B9 APIs
  `directed_edge_substitutions_and_common_ray_word`,
  `common_ray_has_perron_powered_presentations`,
  `Symbolic.exists_nestedReturnFactorization`,
  `Symbolic.Substitution.exists_returnSubstitutionFactorization`, and
  `Symbolic.Substitution.primitive_fixedPoint_hasLinearFactorGaps` depend
  on its internal lemmas.
* The two linearly-recurrent return-word results used in the comparison:
  `linearlyRecurrent_returnWords_finite` and
  `linearlyRecurrent_returnDecomposition`.
* The terminal implication
  `periodicRecurrentLanguage_ultimatelyPeriodic`.
* The metric-period and periodic-tail results from
  `HasEventualMetricPeriod` through
  `PeriodicReturnPathPackage` and
  `product_dilation_returns_on_ray`.

The geometric coding supplies primitivity, the return comparison, and word
periodicity.  The elementary predicates below and
`HasConstantAbsoluteSlope` come from the minimal constant-slope interface.
-/

namespace CommutingInterval

open Function Set Filter Topology
open scoped BigOperators

noncomputable section

/-- Consecutive vertices in a finite subset of the interval.  This is the
small definition formerly supplied by the broad polygonal module. -/
def FinsetAdjacent (K : Finset I) (x y : I) : Prop :=
  x ∈ K ∧ y ∈ K ∧ x < y ∧ ∀ z ∈ K, ¬(x < z ∧ z < y)

/-- A common Markov vertex set for two interval maps.  This is the other
small definition formerly supplied by the broad polygonal module. -/
def IsCommonMarkovSet (A B : IntervalMap) (K : Finset I) : Prop :=
  leftEndpoint ∈ K ∧ rightEndpoint ∈ K ∧
    (∀ x ∈ K, A x ∈ K) ∧ (∀ x ∈ K, B x ∈ K) ∧
    ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      (IsAffineOn A (Set.Icc x y) ∧ IsStrictlyMonotoneOn A (Set.Icc x y)) ∧
      (IsAffineOn B (Set.Icc x y) ∧ IsStrictlyMonotoneOn B (Set.Icc x y))


/-! ## Directed Markov edges and literal paths -/

/--
A directed Markov edge is an adjacent increasing pair of vertices together
with a Boolean orientation.  Thus both orientations are present without
duplicating the proof that the underlying vertices are consecutive.
-/
def DirectedMarkovEdge (K : Finset I) :=
  {data : (↥K × ↥K) × Bool //
    FinsetAdjacent K (data.1.1 : I) (data.1.2 : I)}

noncomputable instance directedMarkovEdgeFinite (K : Finset I) :
    Finite (DirectedMarkovEdge K) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance directedMarkovEdgeFintype (K : Finset I) :
    Fintype (DirectedMarkovEdge K) :=
  Fintype.ofFinite _

noncomputable instance directedMarkovEdgeDecidableEq (K : Finset I) :
    DecidableEq (DirectedMarkovEdge K) :=
  Classical.decEq _

namespace DirectedMarkovEdge

variable {K : Finset I}

/-- The smaller endpoint of the underlying unoriented edge. -/
def lower (e : DirectedMarkovEdge K) : I := e.1.1.1

/-- The larger endpoint of the underlying unoriented edge. -/
def upper (e : DirectedMarkovEdge K) : I := e.1.1.2

/-- Whether the directed edge points from its lower to its upper endpoint. -/
def forward (e : DirectedMarkovEdge K) : Bool := e.1.2

/-- Initial endpoint in the chosen orientation. -/
def source (e : DirectedMarkovEdge K) : I :=
  match e.forward with
  | true => e.lower
  | false => e.upper

/-- Terminal endpoint in the chosen orientation. -/
def target (e : DirectedMarkovEdge K) : I :=
  match e.forward with
  | true => e.upper
  | false => e.lower

/-- The oppositely oriented copy of the same geometric edge. -/
def reverse (e : DirectedMarkovEdge K) : DirectedMarkovEdge K :=
  ⟨(e.1.1, !e.1.2), e.2⟩

/-- Positive Euclidean length of the geometric edge. -/
def length (e : DirectedMarkovEdge K) : ℝ :=
  (e.upper : ℝ) - (e.lower : ℝ)

theorem length_pos (e : DirectedMarkovEdge K) : 0 < e.length := by
  exact sub_pos.mpr e.2.2.2.1

end DirectedMarkovEdge

/-- A literal directed-edge word.  In particular, this is not a quotient by
the cancellation relation `e · e.reverse = 1`. -/
abbrev LiteralDirectedEdgeWord (K : Finset I) :=
  List (DirectedMarkovEdge K)

/-- Consecutive letters in a nonempty literal word meet at their displayed
oriented endpoints.  Immediate backtracking satisfies this predicate and is
retained literally. -/
def IsLiteralDirectedEdgePath {K : Finset I} :
    LiteralDirectedEdgeWord K → Prop
  | [] => False
  | [_] => True
  | e :: f :: rest =>
      e.target = f.source ∧ IsLiteralDirectedEdgePath (f :: rest)

/-- A path starts at the source of its first literal directed edge. -/
def DirectedEdgePathStartsAt {K : Finset I}
    (w : LiteralDirectedEdgeWord K) (x : I) : Prop :=
  ∃ e rest, w = e :: rest ∧ e.source = x

/-- A path ends at the target of its last literal directed edge. -/
def DirectedEdgePathEndsAt {K : Finset I}
    (w : LiteralDirectedEdgeWord K) (x : I) : Prop :=
  ∃ init e, w = init ++ [e] ∧ e.target = x

/-- Exact unit-speed traversal of one oriented edge, beginning at parameter
`t₀`. -/
def TraversesDirectedEdge {K : Finset I} (ψ : ℝ → I) (t₀ : ℝ)
    (e : DirectedMarkovEdge K) : Prop :=
  ∀ u : ℝ, 0 ≤ u → u ≤ e.length →
    (ψ (t₀ + u) : ℝ) =
      match e.forward with
      | true => (e.lower : ℝ) + u
      | false => (e.upper : ℝ) - u

/-- Metric length of a finite word with a prescribed positive letter length. -/
def wordMetricLength {α : Type*} (length : α → ℝ)
    (w : Symbolic.Word α) : ℝ :=
  (w.map length).sum

/-- Metric length of the first `n` letters of an infinite word. -/
def prefixMetricLength {α : Type*} (length : α → ℝ)
    (x : Symbolic.InfiniteWord α) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, length (x i)

/-- A common finite alphabet, embedded in the geometric directed edges. -/
abbrev OccurringDirectedAlphabet (K : Finset I) :=
  Finset (DirectedMarkovEdge K)

/-- Forget that a retained directed edge belongs to the occurring alphabet. -/
def occurringEdge {K : Finset I} (alphabet : OccurringDirectedAlphabet K) :
    alphabet → DirectedMarkovEdge K :=
  fun e => e.1

/-- Convert a word on the retained alphabet to its literal geometric word. -/
def geometricEdgeWord {K : Finset I}
    (alphabet : OccurringDirectedAlphabet K)
    (w : Symbolic.Word alphabet) : LiteralDirectedEdgeWord K :=
  w.map (occurringEdge alphabet)

/--
The image of every retained directed edge is represented by the complete
literal edge path from the image of its source to the image of its target.
There is deliberately no reduced-word or no-backtracking hypothesis.
-/
def ModelsDirectedEdgeSubstitution {K : Finset I}
    (T : IntervalMap) (alphabet : OccurringDirectedAlphabet K)
    (σ : Symbolic.Substitution alphabet) : Prop :=
  ∀ e : alphabet,
    IsLiteralDirectedEdgePath (geometricEdgeWord alphabet (σ e)) ∧
      DirectedEdgePathStartsAt (geometricEdgeWord alphabet (σ e))
        (T e.1.source) ∧
      DirectedEdgePathEndsAt (geometricEdgeWord alphabet (σ e))
        (T e.1.target)

/-- The successive directed letters give a literal unit-speed itinerary of
the nonnegative ray. -/
def HasLiteralUnitSpeedItinerary {K : Finset I} {α : Type*}
    (ψ : ℝ → I) (edge : α → DirectedMarkovEdge K)
    (length : α → ℝ) (x : Symbolic.InfiniteWord α) : Prop :=
  (∀ a, length a = (edge a).length) ∧
    (∀ n : ℕ, (edge (x n)).target = (edge (x (n + 1))).source) ∧
    ∀ n : ℕ, TraversesDirectedEdge ψ (prefixMetricLength length x n) (edge (x n))

/-! ## Ray and common fixed-substitution package -/

/-- Dilation equivariance restricted to the physical nonnegative ray. -/
def DilationReturnsOnRay (ψ : ℝ → I) (scale : ℝ)
    (T : IntervalMap) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ψ (scale * t) = T (ψ t)

/-- Every point of the interval is met at a nonnegative ray parameter. -/
def IsOntoNonnegativeRay (ψ : ℝ → I) : Prop :=
  ∀ y : I, ∃ t : ℝ, 0 ≤ t ∧ ψ t = y

/-- Adjacency in a finite set of real parameter vertices. -/
def AdjacentParameterVertices (K : Finset ℝ) (x y : ℝ) : Prop :=
  x ∈ K ∧ y ∈ K ∧ x < y ∧ ∀ z ∈ K, ¬(x < z ∧ z < y)

/-- A real-parameter path is finite-piece PL of absolute speed one on a
compact parameter interval. -/
def HasFiniteUnitSpeedPiecesOn (ψ : ℝ → I) (a b : ℝ) : Prop :=
  ∃ K : Finset ℝ, a ∈ K ∧ b ∈ K ∧
    (∀ x ∈ K, x ∈ Set.Icc a b) ∧
    ∀ ⦃x y : ℝ⦄, AdjacentParameterVertices K x y →
      ∃ m c : ℝ, |m| = 1 ∧
        ∀ t ∈ Set.Icc x y, (ψ t : ℝ) = m * t + c

/-- Local polygonality and unit speed on every compact part of the
nonnegative ray. -/
def IsLocallyUnitSpeedRay (ψ : ℝ → I) : Prop :=
  Continuous ψ ∧
    ∀ a b : ℝ, 0 ≤ a → a < b → HasFiniteUnitSpeedPiecesOn ψ a b

/-- The transpose-incidence action on a real length vector. -/
def incidenceTransposeMul {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Symbolic.Substitution α) (length : α → ℝ) (source : α) : ℝ :=
  ∑ output : α, (σ.incidenceMatrix output source : ℝ) * length output

/-- A strictly positive geometric length vector with eigenvalue `scale` for
the transpose incidence matrix. -/
def IsPositiveLengthEigenvector {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Symbolic.Substitution α) (length : α → ℝ) (scale : ℝ) : Prop :=
  (∀ a, 0 < length a) ∧
    ∀ source, incidenceTransposeMul σ length source = scale * length source

/-- Each substituted word has the metric length prescribed by the absolute
slope of the corresponding geometric branch. -/
def SubstitutionScalesLetterLengths {α : Type*}
    (σ : Symbolic.Substitution α) (length : α → ℝ) (scale : ℝ) : Prop :=
  ∀ source : α,
    wordMetricLength length (σ source) = scale * length source

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

/-- Counting each output-letter occurrence converts metric image lengths to
the transpose-incidence eigenvector identity. -/
theorem substitution_metric_lengths_give_incidence_identity
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

/-- The iterated images of a generating letter have unbounded length. -/
def LetterImagesGrow {α : Type*} (σ : Symbolic.Substitution α) (seed : α) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ (σ.iterateLetter n seed).length

/--
The two literal substitutions read from the same Markov ray.  The alphabet
is already the occurring alphabet: it is finite by construction and the
`every_letter_occurs` field rules out unused retained letters.
-/
structure CommonRayFixedWord
    (A B : IntervalMap) (K : Finset I) (ψ : ℝ → I) (a b : ℝ) where
  /-- Finite set of directed geometric edges which actually occur. -/
  alphabet : OccurringDirectedAlphabet K
  /-- Explicit nonemptiness of the occurring alphabet. -/
  alphabet_nonempty : alphabet.Nonempty
  /-- Substitution induced by `A`. -/
  substitutionA : Symbolic.Substitution alphabet
  /-- Substitution induced by `B`. -/
  substitutionB : Symbolic.Substitution alphabet
  /-- The positive initial directed edge. -/
  seed : alphabet
  /-- Its common one-sided fixed word. -/
  word : Symbolic.InfiniteWord alphabet
  /-- The retained alphabet is exactly occurring, rather than merely ambient. -/
  every_letter_occurs : ∀ e : alphabet,
    Symbolic.Substitution.OccursInInfiniteWord e word
  /-- The first substitution fixes the displayed ray word. -/
  fixedA : substitutionA.IsFixedPoint word
  /-- The second substitution fixes the same word. -/
  fixedB : substitutionB.IsFixedPoint word
  /-- The initial letter is prolongable for `A`. -/
  prolongableA : substitutionA.ProlongableOn seed
  /-- The initial letter is prolongable for `B`. -/
  prolongableB : substitutionB.ProlongableOn seed
  /-- Every retained letter is generated from the initial letter under `A`. -/
  generatingA : substitutionA.IsGeneratingLetter seed
  /-- Every retained letter is generated from the initial letter under `B`. -/
  generatingB : substitutionB.IsGeneratingLetter seed
  /-- Literal edge images are the `A`-images of the geometric edges. -/
  modelsA : ModelsDirectedEdgeSubstitution A alphabet substitutionA
  /-- Literal edge images are the `B`-images of the geometric edges. -/
  modelsB : ModelsDirectedEdgeSubstitution B alphabet substitutionB
  /-- Positive Euclidean length of each occurring directed edge. -/
  letterLength : alphabet → ℝ
  /-- The abstract length is exactly the underlying Euclidean edge length. -/
  letterLength_eq : ∀ e, letterLength e = e.1.length
  /-- Positivity is kept explicit for the Perron and growth arguments. -/
  letterLength_pos : ∀ e, 0 < letterLength e
  /-- Literal unit-speed itinerary of the whole nonnegative ray. -/
  itinerary : HasLiteralUnitSpeedItinerary ψ (occurringEdge alphabet)
    letterLength word
  /-- Iterated `A`-images are actual prefixes of the common word. -/
  prefixA : ∀ n : ℕ,
    substitutionA.iterateLetter n seed =
      word.take (substitutionA.iterateLetter n seed).length
  /-- Iterated `B`-images are actual prefixes of the same word. -/
  prefixB : ∀ n : ℕ,
    substitutionB.iterateLetter n seed =
      word.take (substitutionB.iterateLetter n seed).length
  /-- Exact metric length of every substituted `A`-prefix. -/
  prefixMetricA : ∀ n : ℕ,
    wordMetricLength letterLength (substitutionA.iterateLetter n seed) =
      a ^ n * letterLength seed
  /-- Exact metric length of every substituted `B`-prefix. -/
  prefixMetricB : ∀ n : ℕ,
    wordMetricLength letterLength (substitutionB.iterateLetter n seed) =
      b ^ n * letterLength seed
  /-- The transpose `A` incidence identity. -/
  imageMetricA : SubstitutionScalesLetterLengths substitutionA letterLength a
  /-- The transpose `B` incidence identity. -/
  imageMetricB : SubstitutionScalesLetterLengths substitutionB letterLength b
  /-- The transpose `A` incidence identity. -/
  lengthEigenA : IsPositiveLengthEigenvector substitutionA letterLength a
  /-- The transpose `B` incidence identity. -/
  lengthEigenB : IsPositiveLengthEigenvector substitutionB letterLength b
  /-- The first prefix family grows without bound. -/
  growthA : LetterImagesGrow substitutionA seed
  /-- The second prefix family grows without bound. -/
  growthB : LetterImagesGrow substitutionB seed
  /-- The first metric scale is expanding. -/
  one_lt_a : 1 < a
  /-- The second metric scale is expanding. -/
  one_lt_b : 1 < b
  /-- Regularity of the underlying ray. -/
  ray_unit_speed : IsLocallyUnitSpeedRay ψ
  /-- The rebuilt ray covers the physical interval. -/
  ray_onto : IsOntoNonnegativeRay ψ
  /-- Dilation by `a` realizes `A` along the ray. -/
  ray_returnA : DilationReturnsOnRay ψ a A
  /-- Dilation by `b` realizes `B` along the ray. -/
  ray_returnB : DilationReturnsOnRay ψ b B

/-! ### Construction skeleton for the common directed-edge coding

The construction is factored into four independently checkable pieces:
finite paths through the ordered Markov vertices, the substitution associated
to one Markov map, the common full-alphabet ray word, and restriction to the
letters which actually occur. -/

/-- Any two distinct Markov vertices are joined by the literal monotone word
of consecutive directed Markov edges.  Its metric length is their Euclidean
distance. -/
private theorem isLiteralDirectedEdgePath_iff_isChain
    {K : Finset I} (w : LiteralDirectedEdgeWord K) :
    IsLiteralDirectedEdgePath w ↔
      w ≠ [] ∧ List.IsChain (fun e f ↦ e.target = f.source) w := by
  induction w with
  | nil => simp [IsLiteralDirectedEdgePath]
  | cons e w ih =>
      cases w with
      | nil => simp [IsLiteralDirectedEdgePath]
      | cons f rest =>
          simp [IsLiteralDirectedEdgePath, List.isChain_cons_cons, ih]

private theorem literalDirectedEdgePath_append
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x : I}
    (hu : IsLiteralDirectedEdgePath u)
    (hv : IsLiteralDirectedEdgePath v)
    (huEnd : DirectedEdgePathEndsAt u x)
    (hvStart : DirectedEdgePathStartsAt v x) :
    IsLiteralDirectedEdgePath (u ++ v) := by
  rw [isLiteralDirectedEdgePath_iff_isChain] at hu hv ⊢
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

private theorem directedEdgePathStartsAt_append_left
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathStartsAt u x) :
    DirectedEdgePathStartsAt (u ++ v) x := by
  rcases h with ⟨e, rest, rfl, he⟩
  exact ⟨e, rest ++ v, by simp, he⟩

private theorem directedEdgePathEndsAt_append_right
    {K : Finset I} {u v : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathEndsAt v x) :
    DirectedEdgePathEndsAt (u ++ v) x := by
  rcases h with ⟨init, e, rfl, he⟩
  exact ⟨u ++ init, e, by simp [List.append_assoc], he⟩

private theorem wordMetricLength_append {α : Type*} (length : α → ℝ)
    (u v : Symbolic.Word α) :
    wordMetricLength length (u ++ v) =
      wordMetricLength length u + wordMetricLength length v := by
  simp [wordMetricLength]

private theorem exists_literalDirectedEdgePath_between
    {K : Finset I} (hzero : leftEndpoint ∈ K) (hone : rightEndpoint ∈ K)
    {x y : I} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) :
    ∃ w : LiteralDirectedEdgeWord K,
      IsLiteralDirectedEdgePath w ∧
        DirectedEdgePathStartsAt w x ∧
        DirectedEdgePathEndsAt w y ∧
        wordMetricLength DirectedMarkovEdge.length w =
          |(y : ℝ) - (x : ℝ)| := by
  classical
  let between (x y : I) : Finset I :=
    K.filter fun z ↦ min x y < z ∧ z < max x y
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
              ih (between x z).card hcardXZ hx hzK hxz.ne
                rfl
            obtain ⟨v, hvPath, hvStart, hvEnd, hvMetric⟩ :=
              ih (between z y).card hcardZY hzK hy hzy.ne
                rfl
            refine ⟨u ++ v,
              literalDirectedEdgePath_append huPath hvPath huEnd hvStart,
              directedEdgePathStartsAt_append_left huStart,
              directedEdgePathEndsAt_append_right hvEnd, ?_⟩
            have hxzR : (x : ℝ) < (z : ℝ) := hxz
            have hzyR : (z : ℝ) < (y : ℝ) := hzy
            have hxyR : (x : ℝ) < (y : ℝ) := hxylt
            rw [wordMetricLength_append, huMetric, hvMetric,
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
                abs_of_pos (sub_pos.mpr (show (x : ℝ) < (y : ℝ) from hxylt))]
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
              ih (between x z).card hcardXZ hx hzK hzx.ne'
                rfl
            obtain ⟨v, hvPath, hvStart, hvEnd, hvMetric⟩ :=
              ih (between z y).card hcardZY hzK hy hyz.ne'
                rfl
            refine ⟨u ++ v,
              literalDirectedEdgePath_append huPath hvPath huEnd hvStart,
              directedEdgePathStartsAt_append_left huStart,
              directedEdgePathEndsAt_append_right hvEnd, ?_⟩
            have hzxR : (z : ℝ) < (x : ℝ) := hzx
            have hyzR : (y : ℝ) < (z : ℝ) := hyz
            have hyxR : (y : ℝ) < (x : ℝ) := hyxlt
            rw [wordMetricLength_append, huMetric, hvMetric,
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
                abs_of_neg (sub_neg.mpr (show (y : ℝ) < (x : ℝ) from hyxlt))]
  exact go (between x y).card hx hy hxy rfl

/-- The full-alphabet substitution carried by one constant-slope Markov map. -/
private structure FullMarkovSubstitution
    (T : IntervalMap) (K : Finset I) (scale : ℝ) where
  substitution : Symbolic.Substitution (DirectedMarkovEdge K)
  path : ∀ e, IsLiteralDirectedEdgePath (substitution e)
  starts : ∀ e, DirectedEdgePathStartsAt (substitution e) (T e.source)
  ends : ∀ e, DirectedEdgePathEndsAt (substitution e) (T e.target)
  metric : SubstitutionScalesLetterLengths substitution
    DirectedMarkovEdge.length scale

private theorem RealPartition.exists_adjacent_straddling
    (partition : RealPartition) {x : ℝ} (hxI : x ∈ I)
    (hxnot : x ∉ partition.points) :
    ∃ a b : ℝ, partition.Adjacent a b ∧ a < x ∧ x < b := by
  classical
  let lower := partition.points.filter fun z ↦ z < x
  let upper := partition.points.filter fun z ↦ x < z
  have hlower : lower.Nonempty := by
    refine ⟨0, ?_⟩
    have hx0 : (0 : ℝ) < x := lt_of_le_of_ne hxI.1 fun h ↦ by
      apply hxnot
      simpa [h] using partition.zero_mem
    simp [lower, partition.zero_mem, hx0]
  have hupper : upper.Nonempty := by
    refine ⟨1, ?_⟩
    have hx1 : x < (1 : ℝ) := lt_of_le_of_ne hxI.2 fun h ↦ by
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
  · have hxz : x < z := lt_of_le_of_ne (le_of_not_gt hzx) fun h ↦ by
      apply hxnot
      simpa [h] using hz
    have hzupper : z ∈ upper := Finset.mem_filter.mpr ⟨hz, hxz⟩
    have hbz : b ≤ z := by simpa using hbmin z hzupper
    exact (not_lt_of_ge hbz) hzb.2

/-- On a Markov edge, the global constant-slope presentation fixes the
absolute endpoint displacement. -/
private theorem markovEdge_image_distance
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
    partition.exists_adjacent_straddling hrI hrnot
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
      sub_pos.mpr (show (e.lower : ℝ) < (e.upper : ℝ) from e.2.2.2.1)
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

/-- The path between the images of each directed edge gives the geometric
substitution for a single Markov map. -/
private theorem exists_fullMarkovSubstitution
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    (hzero : leftEndpoint ∈ K) (hone : rightEndpoint ∈ K)
    (hforward : ∀ x ∈ K, T x ∈ K)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale) :
    Nonempty (FullMarkovSubstitution T K scale) := by
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
    exists_literalDirectedEdgePath_between hzero hone
      (hsourceK e) (htargetK e) (himagesDistinct e)
  let image : DirectedMarkovEdge K → LiteralDirectedEdgeWord K :=
    fun e ↦ Classical.choose (hexists e)
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
        have := (himage e).1
        rw [hnil] at this
        exact this }
  refine ⟨{
    substitution := substitution
    path := fun e ↦ (himage e).1
    starts := fun e ↦ (himage e).2.1
    ends := fun e ↦ (himage e).2.2.1
    metric := ?_ }⟩
  intro e
  change wordMetricLength DirectedMarkovEdge.length (image e) =
    scale * e.length
  rw [(himage e).2.2.2]
  exact markovEdge_image_distance hmarkov hslope e

/-- Public boundary for the full directed Markov substitution, before
letters absent from a chosen ray word are removed.  This deliberately
exposes only the geometric image, path endpoints, and metric law used by
the B9 full-alphabet construction. -/
structure FullDirectedMarkovSubstitution
    (T : IntervalMap) (K : Finset I) (scale : ℝ) where
  substitution : Symbolic.Substitution (DirectedMarkovEdge K)
  path : ∀ e, IsLiteralDirectedEdgePath (substitution e)
  starts : ∀ e, DirectedEdgePathStartsAt (substitution e) (T e.source)
  ends : ∀ e, DirectedEdgePathEndsAt (substitution e) (T e.target)
  metric : SubstitutionScalesLetterLengths substitution
    DirectedMarkovEdge.length scale

/-- Construct the public full directed Markov substitution by repackaging
the dependency-internal canonical constructor. -/
theorem exists_fullDirectedMarkovSubstitution
    {T : IntervalMap} {K : Finset I} {scale : ℝ}
    (hzero : leftEndpoint ∈ K) (hone : rightEndpoint ∈ K)
    (hforward : ∀ x ∈ K, T x ∈ K)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale) :
    Nonempty (FullDirectedMarkovSubstitution T K scale) := by
  obtain ⟨full⟩ := exists_fullMarkovSubstitution
    hzero hone hforward hmarkov hslope
  exact ⟨{
    substitution := full.substitution
    path := full.path
    starts := full.starts
    ends := full.ends
    metric := full.metric }⟩

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

private theorem letterImagesGrow_of_metric_scales
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {σ : Symbolic.Substitution α} {length : α → ℝ} {scale : ℝ}
    (hlength : ∀ a, 0 < length a)
    (hscale : SubstitutionScalesLetterLengths σ length scale)
    (hone : 1 < scale) (seed : α) :
    LetterImagesGrow σ seed := by
  classical
  let M : ℝ := ∑ a : α, length a
  let a₀ : α := Classical.choice inferInstance
  have ha₀le : length a₀ ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun z _hz ↦ (hlength z).le) (Finset.mem_univ a₀)
  have hMpos : 0 < M := (hlength a₀).trans_le ha₀le
  intro N
  have hevent : ∀ᶠ n : ℕ in atTop,
      ((N : ℝ) * M) / length seed < scale ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop _
  obtain ⟨n, hn'⟩ := Filter.eventually_atTop.1 hevent
  have hn := hn' n le_rfl
  have hlarge : (N : ℝ) * M < scale ^ n * length seed := by
    exact (div_lt_iff₀ (hlength seed)).mp hn
  refine ⟨n, le_of_not_gt fun hlen ↦ ?_⟩
  have hlenR : ((σ.iterateLetter n seed).length : ℝ) < (N : ℝ) := by
    exact_mod_cast hlen
  have hupper := wordMetricLength_le_length_mul_sum length
    (fun a ↦ (hlength a).le) (σ.iterateLetter n seed)
  rw [wordMetricLength_iterateLetter_of_scales hscale] at hupper
  dsimp [M] at hMpos ⊢
  have hmul := mul_lt_mul_of_pos_right hlenR hMpos
  nlinarith

private def directedEdgeDisplacement {K : Finset I}
    (e : DirectedMarkovEdge K) : ℝ :=
  (e.target : ℝ) - (e.source : ℝ)

private theorem directedEdgeDisplacement_abs {K : Finset I}
    (e : DirectedMarkovEdge K) :
    |directedEdgeDisplacement e| = e.length := by
  cases hdir : e.forward with
  | false =>
      have hlt : (e.lower : ℝ) < (e.upper : ℝ) := e.2.2.2.1
      simp [directedEdgeDisplacement, DirectedMarkovEdge.source,
        DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.length,
        abs_of_neg (sub_neg.mpr hlt)]
  | true =>
      have hlt : (e.lower : ℝ) < (e.upper : ℝ) := e.2.2.2.1
      simp [directedEdgeDisplacement, DirectedMarkovEdge.source,
        DirectedMarkovEdge.target, hdir, DirectedMarkovEdge.length,
        abs_of_pos (sub_pos.mpr hlt)]

private theorem directedEdgeDisplacement_le_length {K : Finset I}
    (e : DirectedMarkovEdge K) : directedEdgeDisplacement e ≤ e.length := by
  rw [← directedEdgeDisplacement_abs]
  exact le_abs_self _

private theorem directedEdgePathEndsAt_tail
    {K : Finset I} {e f : DirectedMarkovEdge K}
    {rest : LiteralDirectedEdgeWord K} {x : I}
    (h : DirectedEdgePathEndsAt (e :: f :: rest) x) :
    DirectedEdgePathEndsAt (f :: rest) x := by
  rcases h with ⟨init, last, heq, hlast⟩
  cases init with
  | nil => simp at heq
  | cons first init =>
      refine ⟨init, last, ?_, hlast⟩
      simpa using congrArg List.tail heq

private theorem literalDirectedEdgePath_displacement_sum
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y) :
    (w.map directedEdgeDisplacement).sum = (y : ℝ) - (x : ℝ) := by
  induction w generalizing x with
  | nil => simp [IsLiteralDirectedEdgePath] at hpath
  | cons e rest ih =>
      cases rest with
      | nil =>
          rcases hstart with ⟨first, tail, heq, hfirst⟩
          simp at heq
          rcases heq with ⟨rfl, rfl⟩
          rcases hend with ⟨init, last, heq, hlast⟩
          cases init with
          | nil =>
              have helast : e = last := by simpa using heq
              subst last
              simp [directedEdgeDisplacement, hfirst, hlast]
          | cons first init =>
              simp at heq
      | cons f rest =>
          have hlink : e.target = f.source := hpath.1
          have htailPath : IsLiteralDirectedEdgePath (f :: rest) := hpath.2
          rcases hstart with ⟨first, tail, heq, hfirst⟩
          simp at heq
          rcases heq with ⟨rfl, rfl⟩
          have htailStart : DirectedEdgePathStartsAt (f :: rest) e.target :=
            ⟨f, rest, rfl, hlink.symm⟩
          have htailEnd := directedEdgePathEndsAt_tail hend
          have htailSum := ih htailPath htailStart htailEnd
          change directedEdgeDisplacement e +
            (List.map directedEdgeDisplacement (f :: rest)).sum = _
          rw [htailSum]
          simp [directedEdgeDisplacement, hfirst, hlink]

private theorem directedEdgeDisplacement_sum_le_metric
    {K : Finset I} (w : LiteralDirectedEdgeWord K) :
    (w.map directedEdgeDisplacement).sum ≤
      wordMetricLength DirectedMarkovEdge.length w := by
  induction w with
  | nil => simp [wordMetricLength]
  | cons e w ih =>
      simp only [List.map_cons, List.sum_cons, wordMetricLength]
      exact add_le_add (directedEdgeDisplacement_le_length e) ih

private theorem literalDirectedEdgePath_first_forward_of_shortest_right
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hxy : x < y)
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|) :
    ∀ e rest, w = e :: rest → e.forward = true := by
  intro e rest rfl
  by_contra hforward
  have hfalse : e.forward = false := Bool.eq_false_of_not_eq_true hforward
  have hedisp : directedEdgeDisplacement e = -e.length := by
    have hlt : (e.lower : ℝ) < (e.upper : ℝ) := e.2.2.2.1
    simp [directedEdgeDisplacement, DirectedMarkovEdge.source,
      DirectedMarkovEdge.target, hfalse, DirectedMarkovEdge.length]
  have hrestBound := directedEdgeDisplacement_sum_le_metric rest
  have hsum := literalDirectedEdgePath_displacement_sum hpath hstart hend
  have hepos : 0 < e.length := e.length_pos
  have hxyR : (x : ℝ) < (y : ℝ) := hxy
  simp only [List.map_cons, List.sum_cons] at hsum
  rw [hedisp] at hsum
  rw [wordMetricLength] at hmetric
  change e.length + wordMetricLength DirectedMarkovEdge.length rest = _ at hmetric
  rw [abs_of_pos (sub_pos.mpr hxyR)] at hmetric
  linarith

private theorem directedMarkovEdge_eq_of_forward_source
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

private theorem iterateLetter_prefix_of_le_early
    {α : Type*} {σ : Symbolic.Substitution α} {seed : α}
    (hprolong : σ.ProlongableOn seed) {m n : ℕ} (hmn : m ≤ n) :
    σ.iterateLetter m seed <+: σ.iterateLetter n seed := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => simpa using List.prefix_refl (σ.iterateLetter m seed)
  | succ k ih =>
      simpa [Nat.add_assoc] using
        ih.trans (σ.iterateLetter_prefix_succ hprolong (m + k))

/-- The pointwise limit of the nested, unbounded substituted prefixes of a
prolongable letter. -/
private noncomputable def prolongableLimitWord
    {α : Type*} (σ : Symbolic.Substitution α) (seed : α)
    (hgrowth : LetterImagesGrow σ seed) : Symbolic.InfiniteWord α :=
  fun i ↦
    (σ.iterateLetter (Classical.choose (hgrowth (i + 1))) seed)[i]'(
      lt_of_lt_of_le (Nat.lt_succ_self i)
        (Classical.choose_spec (hgrowth (i + 1))))

private theorem iterateLetter_eq_take_prolongableLimitWord
    {α : Type*} {σ : Symbolic.Substitution α} {seed : α}
    (hprolong : σ.ProlongableOn seed)
    (hgrowth : LetterImagesGrow σ seed) (n : ℕ) :
    σ.iterateLetter n seed =
      (prolongableLimitWord σ seed hgrowth).take
        (σ.iterateLetter n seed).length := by
  apply List.ext_getElem
  · simp
  · intro i hi htake
    rw [Stream'.take_get (m := i)
      (n := (σ.iterateLetter n seed).length)
      (a := prolongableLimitWord σ seed hgrowth) htake]
    unfold prolongableLimitWord
    let k := Classical.choose (hgrowth (i + 1))
    have hik : i < (σ.iterateLetter k seed).length :=
      lt_of_lt_of_le (Nat.lt_succ_self i)
        (Classical.choose_spec (hgrowth (i + 1)))
    let N := max n k
    have hnN : σ.iterateLetter n seed <+: σ.iterateLetter N seed :=
      iterateLetter_prefix_of_le_early hprolong (Nat.le_max_left _ _)
    have hkN : σ.iterateLetter k seed <+: σ.iterateLetter N seed :=
      iterateLetter_prefix_of_le_early hprolong (Nat.le_max_right _ _)
    exact (hnN.getElem hi).trans (hkN.getElem hik).symm

private theorem prolongableLimitWord_fixed
    {α : Type*} {σ : Symbolic.Substitution α} {seed : α}
    (hprolong : σ.ProlongableOn seed)
    (hgrowth : LetterImagesGrow σ seed) :
    σ.IsFixedPoint (prolongableLimitWord σ seed hgrowth) := by
  let word := prolongableLimitWord σ seed hgrowth
  apply funext
  intro i
  obtain ⟨m, him⟩ := hgrowth (i + 1)
  have hi : i < (σ.iterateLetter m seed).length :=
    lt_of_lt_of_le (Nat.lt_succ_self i) him
  have hprefix := iterateLetter_eq_take_prolongableLimitWord hprolong hgrowth m
  have hdecomp : σ.iterateLetter m seed ++ₛ
      word.drop (σ.iterateLetter m seed).length = word := by
    calc
      σ.iterateLetter m seed ++ₛ word.drop (σ.iterateLetter m seed).length =
          word.take (σ.iterateLetter m seed).length ++ₛ
            word.drop (σ.iterateLetter m seed).length := by
        exact congrArg
          (fun pref ↦ pref ++ₛ word.drop (σ.iterateLetter m seed).length)
          hprefix
      _ = word := Stream'.append_take_drop _ _
  have hmap : σ.mapInfinite word =
      σ.mapWord (σ.iterateLetter m seed) ++ₛ
        σ.mapInfinite (word.drop (σ.iterateLetter m seed).length) := by
    calc
      σ.mapInfinite word = σ.mapInfinite
          (σ.iterateLetter m seed ++ₛ
            word.drop (σ.iterateLetter m seed).length) :=
        congrArg σ.mapInfinite hdecomp.symm
      _ = _ := Symbolic.Substitution.mapInfinite_append_stream _ _ _
  rw [hmap]
  have hprefixSucc := σ.iterateLetter_prefix_succ hprolong m
  have hiSucc : i < (σ.mapWord (σ.iterateLetter m seed)).length := by
    change i < (σ.iterateLetter (m + 1) seed).length
    exact hi.trans_le hprefixSucc.length_le
  change (σ.mapWord (σ.iterateLetter m seed) ++ₛ
      σ.mapInfinite (word.drop (σ.iterateLetter m seed).length)).get i = word.get i
  rw [Stream'.get_append_left (n := i)
    (x := σ.mapWord (σ.iterateLetter m seed))
    (a := σ.mapInfinite (word.drop (σ.iterateLetter m seed).length)) hiSucc]
  change (σ.iterateLetter (m + 1) seed)[i] = word i
  have hprefixNext :=
    iterateLetter_eq_take_prolongableLimitWord hprolong hgrowth (m + 1)
  have hiNext : i < (σ.iterateLetter (m + 1) seed).length := by
    exact hiSucc
  have hiTake : i <
      (word.take (σ.iterateLetter (m + 1) seed).length).length := by
    simpa using hiNext
  calc
    (σ.iterateLetter (m + 1) seed)[i]'hiNext =
        (word.take (σ.iterateLetter (m + 1) seed).length)[i]'hiTake :=
      getElem_congr hprefixNext rfl hiNext
    _ = word.get i := Stream'.take_get (m := i)
      (n := (σ.iterateLetter (m + 1) seed).length) (a := word)
        hiTake

/-! ### Finite geometric words and dilation of their traversals -/

/-- Recursive traversal of a finite literal word, starting at a prescribed
ray parameter. -/
private def TraversesLiteralWord {K : Finset I} (ψ : ℝ → I) :
    ℝ → LiteralDirectedEdgeWord K → Prop
  | _, [] => True
  | t, e :: rest =>
      TraversesDirectedEdge ψ t e ∧
        TraversesLiteralWord ψ (t + e.length) rest

private theorem traversesLiteralWord_append
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {u v : LiteralDirectedEdgeWord K} :
    TraversesLiteralWord ψ t (u ++ v) ↔
      TraversesLiteralWord ψ t u ∧
        TraversesLiteralWord ψ
          (t + wordMetricLength DirectedMarkovEdge.length u) v := by
  induction u generalizing t with
  | nil => simp [TraversesLiteralWord, wordMetricLength]
  | cons e u ih =>
      simp only [List.cons_append, TraversesLiteralWord]
      rw [ih]
      simp [wordMetricLength, add_assoc]
      tauto

/-- In a literal edge path, the source of the `i`th edge is obtained by
adding the signed displacements of the preceding edges to the initial
vertex. -/
private theorem literalDirectedEdgePath_source_coordinate
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (i : ℕ) (hi : i < w.length) :
    ((w[i]).source : ℝ) = (x : ℝ) +
      ((w.take i).map directedEdgeDisplacement).sum := by
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
              simp [directedEdgeDisplacement]
              ring

private theorem list_sum_le_sum_of_forall_mem
    {α : Type*} {f g : α → ℝ} {w : List α}
    (h : ∀ z ∈ w, f z ≤ g z) :
    (w.map f).sum ≤ (w.map g).sum := by
  induction w with
  | nil => simp
  | cons z w ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (h z (by simp))
        (ih fun q hq ↦ h q (by simp [hq]))

private theorem list_pointwise_eq_of_le_of_sum_eq
    {α : Type*} {f g : α → ℝ} {w : List α}
    (hle : ∀ z ∈ w, f z ≤ g z)
    (hsum : (w.map f).sum = (w.map g).sum) :
    ∀ z ∈ w, f z = g z := by
  induction w with
  | nil => simp
  | cons q w ih =>
      have hqle : f q ≤ g q := hle q (by simp)
      have hrestle : (w.map f).sum ≤ (w.map g).sum :=
        list_sum_le_sum_of_forall_mem
          (fun z hz ↦ hle z (by simp [hz]))
      have hqeq : f q = g q := by
        simp only [List.map_cons, List.sum_cons] at hsum
        linarith
      have hrestEq : (w.map f).sum = (w.map g).sum := by
        simp only [List.map_cons, List.sum_cons, hqeq] at hsum
        exact add_left_cancel hsum
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hqeq
      · exact ih (fun u hu ↦ hle u (by simp [hu])) hrestEq z hz

private theorem list_sum_map_neg {α : Type*} (f : α → ℝ) (w : List α) :
    (w.map (fun z ↦ -f z)).sum = -(w.map f).sum := by
  induction w with
  | nil => simp
  | cons z w ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- Equality in the one-dimensional triangle inequality forces every edge
of a shortest path to point in the common increasing direction. -/
private theorem shortestLiteralPath_forward
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hxy : x < y)
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|) :
    ∀ e ∈ w, directedEdgeDisplacement e = e.length := by
  have hdisp := literalDirectedEdgePath_displacement_sum
    hpath hstart hend
  have hxyR : (x : ℝ) < (y : ℝ) := hxy
  have hsum : (w.map directedEdgeDisplacement).sum =
      (w.map DirectedMarkovEdge.length).sum := by
    calc
      (w.map directedEdgeDisplacement).sum = (y : ℝ) - (x : ℝ) := hdisp
      _ = |(y : ℝ) - (x : ℝ)| :=
        (abs_of_pos (sub_pos.mpr hxyR)).symm
      _ = wordMetricLength DirectedMarkovEdge.length w := hmetric.symm
      _ = (w.map DirectedMarkovEdge.length).sum := rfl
  exact list_pointwise_eq_of_le_of_sum_eq
    (fun e _he ↦ directedEdgeDisplacement_le_length e) hsum

/-- Equality in the one-dimensional triangle inequality forces every edge
of a shortest path to point in the common decreasing direction. -/
private theorem shortestLiteralPath_backward
    {K : Finset I} {w : LiteralDirectedEdgeWord K} {x y : I}
    (hyx : y < x)
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|) :
    ∀ e ∈ w, directedEdgeDisplacement e = -e.length := by
  have hdisp := literalDirectedEdgePath_displacement_sum
    hpath hstart hend
  have hyxR : (y : ℝ) < (x : ℝ) := hyx
  have hnegSum : (w.map (fun e ↦ -directedEdgeDisplacement e)).sum =
      -(w.map directedEdgeDisplacement).sum :=
    list_sum_map_neg directedEdgeDisplacement w
  have hsum : (w.map (fun e ↦ -directedEdgeDisplacement e)).sum =
      (w.map DirectedMarkovEdge.length).sum := by
    calc
      (w.map (fun e ↦ -directedEdgeDisplacement e)).sum =
          -(w.map directedEdgeDisplacement).sum := hnegSum
      _ = -((y : ℝ) - (x : ℝ)) := by rw [hdisp]
      _ = |(y : ℝ) - (x : ℝ)| := by
        rw [abs_of_neg (sub_neg.mpr hyxR)]
      _ = wordMetricLength DirectedMarkovEdge.length w := hmetric.symm
      _ = (w.map DirectedMarkovEdge.length).sum := rfl
  have heach := list_pointwise_eq_of_le_of_sum_eq
    (f := fun e ↦ -directedEdgeDisplacement e)
    (g := DirectedMarkovEdge.length)
    (fun e _he ↦ by
      rw [← directedEdgeDisplacement_abs]
      exact neg_le_abs _) hsum
  intro e he
  have := heach e he
  linarith

private theorem traversesLiteralWord_of_pointwise
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (h : ∀ (i : ℕ) (hi : i < w.length),
      TraversesDirectedEdge ψ
        (t + wordMetricLength DirectedMarkovEdge.length (w.take i)) (w[i])) :
    TraversesLiteralWord ψ t w := by
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

private theorem wordMetricLength_take_le
    {α : Type*} {length : α → ℝ} (hlength : ∀ a, 0 ≤ length a)
    (w : List α) (n : ℕ) :
    wordMetricLength length (w.take n) ≤ wordMetricLength length w := by
  calc
    wordMetricLength length (w.take n) ≤
        wordMetricLength length (w.take n) +
          wordMetricLength length (w.drop n) :=
      le_add_of_nonneg_right
        (List.sum_nonneg fun z hz ↦ by
          obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hz
          exact hlength a)
    _ = wordMetricLength length (w.take n ++ w.drop n) :=
      (wordMetricLength_append length (w.take n) (w.drop n)).symm
    _ = wordMetricLength length w := by rw [List.take_append_drop]

private theorem directedEdge_forward_of_displacement_eq_length
    {K : Finset I} (e : DirectedMarkovEdge K)
    (h : directedEdgeDisplacement e = e.length) : e.forward = true := by
  cases hdir : e.forward with
  | false =>
      have hd : directedEdgeDisplacement e = -e.length := by
        simp [directedEdgeDisplacement, DirectedMarkovEdge.source,
          DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
      have hp := e.length_pos
      rw [hd] at h
      linarith
  | true => rfl

private theorem directedEdge_backward_of_displacement_eq_neg_length
    {K : Finset I} (e : DirectedMarkovEdge K)
    (h : directedEdgeDisplacement e = -e.length) : e.forward = false := by
  cases hdir : e.forward with
  | false => rfl
  | true =>
      have hd : directedEdgeDisplacement e = e.length := by
        simp [directedEdgeDisplacement, DirectedMarkovEdge.source,
          DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
      have hp := e.length_pos
      rw [hd] at h
      linarith

/-- A shortest literal path between two vertices reads the corresponding
straight unit-speed segment. -/
private theorem traversesLiteralWord_of_shortest_segment
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K} {x y : I}
    (hpath : IsLiteralDirectedEdgePath w)
    (hstart : DirectedEdgePathStartsAt w x)
    (hend : DirectedEdgePathEndsAt w y)
    (hmetric : wordMetricLength DirectedMarkovEdge.length w =
      |(y : ℝ) - (x : ℝ)|)
    (hsegment : ∀ v : ℝ, 0 ≤ v → v ≤ |(y : ℝ) - (x : ℝ)| →
      (ψ (t + v) : ℝ) =
        if x < y then (x : ℝ) + v else (x : ℝ) - v) :
    TraversesLiteralWord ψ t w := by
  have hmetricPos : 0 <
      wordMetricLength DirectedMarkovEdge.length w := by
    rcases hstart with ⟨first, rest, rfl, _hfirst⟩
    simp only [wordMetricLength, List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg first.length_pos
      (List.sum_nonneg fun z hz ↦ by
        obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hz
        exact e.length_pos.le)
  have hxyne : x ≠ y := by
    intro hxy
    subst y
    rw [hmetric] at hmetricPos
    simp at hmetricPos
  apply traversesLiteralWord_of_pointwise
  intro i hi
  have hiMem : w[i] ∈ w := List.getElem_mem _
  have hcoord := literalDirectedEdgePath_source_coordinate
    hpath hstart i hi
  let pref := wordMetricLength DirectedMarkovEdge.length (w.take i)
  have hprefNonneg : 0 ≤ pref := by
    dsimp [pref, wordMetricLength]
    exact List.sum_nonneg fun z hz ↦ by
      obtain ⟨e, _he, rfl⟩ := List.mem_map.mp hz
      exact e.length_pos.le
  have hstepBound : pref + (w[i]).length ≤
      |(y : ℝ) - (x : ℝ)| := by
    have htake := wordMetricLength_take_le
      (fun e : DirectedMarkovEdge K ↦ e.length_pos.le) w (i + 1)
    rw [List.take_succ_eq_append_getElem hi,
      wordMetricLength_append] at htake
    rw [hmetric] at htake
    simpa [wordMetricLength, pref] using htake
  by_cases hxy : x < y
  · have halign := shortestLiteralPath_forward hxy hpath hstart hend hmetric
    have hprefixDisp : ((w.take i).map directedEdgeDisplacement).sum = pref := by
      dsimp [pref, wordMetricLength]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      exact halign e (List.mem_of_mem_take he)
    rw [hprefixDisp] at hcoord
    have hdir := directedEdge_forward_of_displacement_eq_length
      w[i] (halign w[i] hiMem)
    have hlower : ((w[i]).lower : ℝ) = (x : ℝ) + pref := by
      simpa [DirectedMarkovEdge.source, hdir] using hcoord
    intro u hu0 hule
    have hv0 : 0 ≤ pref + u := add_nonneg hprefNonneg hu0
    have hvle : pref + u ≤ |(y : ℝ) - (x : ℝ)| :=
      by linarith
    have hs := hsegment (pref + u) hv0 hvle
    rw [hdir]
    change (ψ ((t + pref) + u) : ℝ) = (w[i].lower : ℝ) + u
    calc
      (ψ ((t + pref) + u) : ℝ) = (ψ (t + (pref + u)) : ℝ) := by ring_nf
      _ = (x : ℝ) + (pref + u) := by simpa [hxy] using hs
      _ = (w[i].lower : ℝ) + u := by rw [hlower]; ring
  · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) hxyne.symm
    have halign := shortestLiteralPath_backward hyx hpath hstart hend hmetric
    have hprefixDisp : ((w.take i).map directedEdgeDisplacement).sum = -pref := by
      calc
        ((w.take i).map directedEdgeDisplacement).sum =
            ((w.take i).map (fun e ↦ -e.length)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro e he
          exact halign e (List.mem_of_mem_take he)
        _ = -pref := by
          exact list_sum_map_neg DirectedMarkovEdge.length (w.take i)
    rw [hprefixDisp] at hcoord
    have hdir := directedEdge_backward_of_displacement_eq_neg_length
      w[i] (halign w[i] hiMem)
    have hupper : ((w[i]).upper : ℝ) = (x : ℝ) - pref := by
      simpa [DirectedMarkovEdge.source, hdir] using hcoord
    intro u hu0 hule
    have hv0 : 0 ≤ pref + u := add_nonneg hprefNonneg hu0
    have hvle : pref + u ≤ |(y : ℝ) - (x : ℝ)| :=
      by linarith
    have hs := hsegment (pref + u) hv0 hvle
    rw [hdir]
    change (ψ ((t + pref) + u) : ℝ) = (w[i].upper : ℝ) - u
    calc
      (ψ ((t + pref) + u) : ℝ) = (ψ (t + (pref + u)) : ℝ) := by ring_nf
      _ = (x : ℝ) - (pref + u) := by simpa [hxy] using hs
      _ = (w[i].upper : ℝ) - u := by rw [hupper]; ring

/-- Dilation equivariance sends the traversal of one Markov edge to the
literal substituted path chosen for its image. -/
private theorem fullMarkovSubstitution_image_traversal
    {T : IntervalMap} {K : Finset I} {ψ : ℝ → I} {scale t : ℝ}
    (full : FullMarkovSubstitution T K scale)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hone : 1 < scale)
    (hreturn : DilationReturnsOnRay ψ scale T)
    (ht : 0 ≤ t) {e : DirectedMarkovEdge K}
    (htrav : TraversesDirectedEdge ψ t e) :
    TraversesLiteralWord ψ (scale * t) (full.substitution e) := by
  have hscale : 0 < scale := zero_lt_one.trans hone
  have hlen : 0 < e.length := e.length_pos
  have hlowerMem : e.lower ∈ Set.Icc e.lower e.upper :=
    ⟨le_rfl, e.2.2.2.1.le⟩
  have hupperMem : e.upper ∈ Set.Icc e.lower e.upper :=
    ⟨e.2.2.2.1.le, le_rfl⟩
  have hsourceMem : e.source ∈ Set.Icc e.lower e.upper := by
    cases hdir : e.forward <;>
      simp [DirectedMarkovEdge.source, hdir, hlowerMem, hupperMem]
  have htargetMem : e.target ∈ Set.Icc e.lower e.upper := by
    cases hdir : e.forward <;>
      simp [DirectedMarkovEdge.target, hdir, hlowerMem, hupperMem]
  rcases (hmarkov e.2).1 with ⟨m, c, haff⟩
  have hdistance := markovEdge_image_distance hmarkov hslope e
  have himageNe : T e.source ≠ T e.target := by
    intro heq
    have : (0 : ℝ) = scale * e.length := by
      simpa [heq] using hdistance
    nlinarith
  have hmetric : wordMetricLength DirectedMarkovEdge.length
      (full.substitution e) =
      |(T e.target : ℝ) - (T e.source : ℝ)| := by
    rw [full.metric e]
    exact hdistance.symm
  apply traversesLiteralWord_of_shortest_segment
    (full.path e) (full.starts e) (full.ends e) hmetric
  intro v hv0 hvle
  let u := v / scale
  have hu0 : 0 ≤ u := div_nonneg hv0 hscale.le
  have hule : u ≤ e.length := by
    apply (div_le_iff₀ hscale).2
    nlinarith [hvle, hdistance]
  have htplus : 0 ≤ t + u := add_nonneg ht hu0
  have htravU := htrav u hu0 hule
  have hψMem : ψ (t + u) ∈ Set.Icc e.lower e.upper := by
    cases hdir : e.forward with
    | false =>
        rw [hdir] at htravU
        constructor
        · change (e.lower : ℝ) ≤ (ψ (t + u) : ℝ)
          rw [htravU]
          dsimp [DirectedMarkovEdge.length] at hule
          linarith
        · change (ψ (t + u) : ℝ) ≤ (e.upper : ℝ)
          rw [htravU]
          linarith
    | true =>
        rw [hdir] at htravU
        constructor
        · change (e.lower : ℝ) ≤ (ψ (t + u) : ℝ)
          rw [htravU]
          linarith
        · change (ψ (t + u) : ℝ) ≤ (e.upper : ℝ)
          rw [htravU]
          dsimp [DirectedMarkovEdge.length] at hule
          linarith
  have hdispAffine :
      (T e.target : ℝ) - (T e.source : ℝ) =
        m * directedEdgeDisplacement e := by
    rw [haff e.target htargetMem, haff e.source hsourceMem]
    simp [directedEdgeDisplacement]
    ring
  have hψParam : (ψ (t + u) : ℝ) = (e.source : ℝ) +
      directedEdgeDisplacement e / e.length * u := by
    cases hdir : e.forward with
    | false =>
        rw [hdir] at htravU
        rw [htravU]
        have hd : directedEdgeDisplacement e = -e.length := by
          simp [directedEdgeDisplacement, DirectedMarkovEdge.source,
            DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
        rw [hd]
        simp only [DirectedMarkovEdge.source, hdir]
        field_simp [hlen.ne'] <;> ring
    | true =>
        rw [hdir] at htravU
        rw [htravU]
        have hd : directedEdgeDisplacement e = e.length := by
          simp [directedEdgeDisplacement, DirectedMarkovEdge.source,
            DirectedMarkovEdge.target, DirectedMarkovEdge.length, hdir]
        rw [hd]
        simp only [DirectedMarkovEdge.source, hdir]
        field_simp [hlen.ne'] <;> ring
  have hinterp : (T (ψ (t + u)) : ℝ) = (T e.source : ℝ) +
      ((T e.target : ℝ) - (T e.source : ℝ)) / e.length * u := by
    rw [haff (ψ (t + u)) hψMem, hψParam, hdispAffine,
      haff e.source hsourceMem]
    field_simp [hlen.ne'] <;> ring
  have htime : scale * (t + u) = scale * t + v := by
    dsimp [u]
    field_simp [hscale.ne'] <;> ring
  have hscaled : (ψ (scale * t + v) : ℝ) = (T e.source : ℝ) +
      ((T e.target : ℝ) - (T e.source : ℝ)) / e.length * u := by
    calc
      (ψ (scale * t + v) : ℝ) = (ψ (scale * (t + u)) : ℝ) := by rw [htime]
      _ = (T (ψ (t + u)) : ℝ) :=
        congrArg Subtype.val (hreturn (t + u) htplus)
      _ = _ := hinterp
  by_cases hinc : T e.source < T e.target
  · have hincR : (T e.source : ℝ) < (T e.target : ℝ) := hinc
    have hdelta : (T e.target : ℝ) - (T e.source : ℝ) =
        scale * e.length := by
      rw [← hdistance, abs_of_pos (sub_pos.mpr hincR)]
    simp only [if_pos hinc]
    rw [hscaled, hdelta]
    dsimp [u]
    field_simp [hlen.ne', hscale.ne'] <;> ring
  · have hdec : T e.target < T e.source :=
      lt_of_le_of_ne (le_of_not_gt hinc) himageNe.symm
    have hdecR : (T e.target : ℝ) < (T e.source : ℝ) := hdec
    have hdelta : (T e.target : ℝ) - (T e.source : ℝ) =
        -(scale * e.length) := by
      have := hdistance
      rw [abs_of_neg (sub_neg.mpr hdecR)] at this
      linarith
    simp only [if_neg hinc]
    rw [hscaled, hdelta]
    dsimp [u]
    field_simp [hlen.ne', hscale.ne'] <;> ring

/-- Dilation sends a traversed finite word to its substituted word. -/
private theorem fullMarkovSubstitution_mapWord_traversal
    {T : IntervalMap} {K : Finset I} {ψ : ℝ → I} {scale t : ℝ}
    (full : FullMarkovSubstitution T K scale)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hone : 1 < scale)
    (hreturn : DilationReturnsOnRay ψ scale T)
    (ht : 0 ≤ t) {w : LiteralDirectedEdgeWord K}
    (htrav : TraversesLiteralWord ψ t w) :
    TraversesLiteralWord ψ (scale * t) (full.substitution.mapWord w) := by
  induction w generalizing t with
  | nil => simp [Symbolic.Substitution.mapWord, TraversesLiteralWord]
  | cons e rest ih =>
      rw [Symbolic.Substitution.mapWord_cons,
        traversesLiteralWord_append]
      refine ⟨fullMarkovSubstitution_image_traversal full hmarkov hslope
        hone hreturn ht htrav.1, ?_⟩
      have htail := ih (t := t + e.length)
        (add_nonneg ht e.length_pos.le) htrav.2
      rw [full.metric e]
      convert htail using 1 <;> ring

/-- Every iterated image of the initial edge is the literal traversal of the
corresponding expanding initial segment of the ray. -/
private theorem fullMarkovSubstitution_iterate_traversal
    {T : IntervalMap} {K : Finset I} {ψ : ℝ → I} {scale : ℝ}
    (full : FullMarkovSubstitution T K scale)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hone : 1 < scale)
    (hreturn : DilationReturnsOnRay ψ scale T)
    {seed : DirectedMarkovEdge K}
    (hinitial : TraversesDirectedEdge ψ 0 seed) :
    ∀ n : ℕ, TraversesLiteralWord ψ 0
      (full.substitution.iterateLetter n seed) := by
  intro n
  induction n with
  | zero => simpa [Symbolic.Substitution.iterateLetter,
      TraversesLiteralWord] using hinitial
  | succ n ih =>
      rw [Symbolic.Substitution.iterateLetter_succ]
      simpa using fullMarkovSubstitution_mapWord_traversal full hmarkov
        hslope hone hreturn (t := 0) (le_refl 0) ih

private theorem traversesLiteralWord_get
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {w : LiteralDirectedEdgeWord K}
    (h : TraversesLiteralWord ψ t w) (i : ℕ) (hi : i < w.length) :
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

private theorem wordMetricLength_stream_take_eq_prefix
    {α : Type*} (length : α → ℝ) (word : Symbolic.InfiniteWord α) (n : ℕ) :
    wordMetricLength length (word.take n) =
      prefixMetricLength length word n := by
  induction n with
  | zero => simp [wordMetricLength, prefixMetricLength]
  | succ n ih =>
      rw [← Stream'.concat_take_get (n := n) (s := word),
        wordMetricLength_append, ih]
      simp [wordMetricLength, prefixMetricLength, Finset.sum_range_succ]
      rfl

private theorem traversesDirectedEdge_start
    {K : Finset I} {ψ : ℝ → I} {t : ℝ} {e : DirectedMarkovEdge K}
    (h : TraversesDirectedEdge ψ t e) : ψ t = e.source := by
  have hzero := h 0 (le_refl 0) e.length_pos.le
  apply Subtype.ext
  cases hdir : e.forward <;>
    simp [hdir, DirectedMarkovEdge.source] at hzero ⊢ <;> exact hzero

private theorem traversesDirectedEdge_end
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

private theorem directedMarkovEdge_eq_of_backward_source
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

private theorem traversesDirectedEdge_unique
    {K : Finset I} {ψ : ℝ → I} {t : ℝ}
    {e f : DirectedMarkovEdge K}
    (he : TraversesDirectedEdge ψ t e)
    (hf : TraversesDirectedEdge ψ t f) : e = f := by
  have hsource : e.source = f.source :=
    (traversesDirectedEdge_start he).symm.trans (traversesDirectedEdge_start hf)
  cases hedir : e.forward <;> cases hfdir : f.forward
  · exact directedMarkovEdge_eq_of_backward_source hedir hfdir hsource
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
  · exact directedMarkovEdge_eq_of_forward_source hedir hfdir hsource

/-- The prolongable substitution limit inherits the literal traversal of all
of its growing finite prefixes. -/
private theorem prolongableLimitWord_itinerary
    {T : IntervalMap} {K : Finset I} {ψ : ℝ → I} {scale : ℝ}
    (full : FullMarkovSubstitution T K scale)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hone : 1 < scale)
    (hreturn : DilationReturnsOnRay ψ scale T)
    {seed : DirectedMarkovEdge K}
    (hinitial : TraversesDirectedEdge ψ 0 seed)
    (hprolong : full.substitution.ProlongableOn seed)
    (hgrowth : LetterImagesGrow full.substitution seed) :
    HasLiteralUnitSpeedItinerary ψ id DirectedMarkovEdge.length
      (prolongableLimitWord full.substitution seed hgrowth) := by
  let word := prolongableLimitWord full.substitution seed hgrowth
  have hfinite := fullMarkovSubstitution_iterate_traversal full hmarkov
    hslope hone hreturn hinitial
  have hwordTrav (i : ℕ) : TraversesDirectedEdge ψ
      (prefixMetricLength DirectedMarkovEdge.length word i) (word i) := by
    obtain ⟨m, hm⟩ := hgrowth (i + 1)
    have hi : i < (full.substitution.iterateLetter m seed).length :=
      lt_of_lt_of_le (Nat.lt_succ_self i) hm
    have hprefix := iterateLetter_eq_take_prolongableLimitWord
      hprolong hgrowth m
    have htake : (full.substitution.iterateLetter m seed).take i =
        word.take i := by
      have ht := congrArg (List.take i) hprefix
      simpa [word, List.take_take, Nat.min_eq_right hi.le] using ht
    have hget : (full.substitution.iterateLetter m seed)[i] = word i := by
      have hright : i < (word.take
          (full.substitution.iterateLetter m seed).length).length := by
        simpa using hi
      calc
        (full.substitution.iterateLetter m seed)[i]'hi =
            (word.take (full.substitution.iterateLetter m seed).length)[i]'hright :=
          getElem_congr hprefix rfl hi
        _ = word.get i := Stream'.take_get (m := i)
          (n := (full.substitution.iterateLetter m seed).length)
          (a := word) hright
    have hgetTrav := traversesLiteralWord_get (hfinite m) i hi
    rw [zero_add, htake,
      wordMetricLength_stream_take_eq_prefix] at hgetTrav
    simpa [hget] using hgetTrav
  refine ⟨by simp, ?_, hwordTrav⟩
  intro n
  have hcurrent := traversesDirectedEdge_end (hwordTrav n)
  have hnext := traversesDirectedEdge_start (hwordTrav (n + 1))
  have hprefSucc : prefixMetricLength DirectedMarkovEdge.length word (n + 1) =
      prefixMetricLength DirectedMarkovEdge.length word n +
        (word n).length := by
    simp [prefixMetricLength, Finset.sum_range_succ]
  rw [hprefSucc] at hnext
  exact hcurrent.symm.trans hnext

/-- Two infinite literal unit-speed codings of the same ray are equal once
their first edge agrees. -/
private theorem literalUnitSpeedItinerary_unique
    {K : Finset I} {ψ : ℝ → I}
    {u v : Symbolic.InfiniteWord (DirectedMarkovEdge K)}
    (hu : HasLiteralUnitSpeedItinerary ψ id DirectedMarkovEdge.length u)
    (hv : HasLiteralUnitSpeedItinerary ψ id DirectedMarkovEdge.length v)
    (hzero : u 0 = v 0) : u = v := by
  apply funext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · simpa [hn] using hzero
      · have hpref : prefixMetricLength DirectedMarkovEdge.length u n =
            prefixMetricLength DirectedMarkovEdge.length v n := by
          simp only [prefixMetricLength]
          apply Finset.sum_congr rfl
          intro i hi
          rw [ih i (Finset.mem_range.mp hi)]
        have huTrav := hu.2.2 n
        have hvTrav := hv.2.2 n
        simp only [id_eq] at huTrav hvTrav
        rw [← hpref] at hvTrav
        exact traversesDirectedEdge_unique huTrav hvTrav

private theorem fullMarkovSubstitution_prolongable_of_initial
    {T : IntervalMap} {K : Finset I} {ψ : ℝ → I} {scale : ℝ}
    (full : FullMarkovSubstitution T K scale)
    (hmarkov : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn T (Set.Icc x y) ∧
        IsStrictlyMonotoneOn T (Set.Icc x y))
    (hslope : HasConstantAbsoluteSlope T scale)
    (hone : 1 < scale)
    (hreturn : DilationReturnsOnRay ψ scale T)
    {seed : DirectedMarkovEdge K}
    (hinitial : TraversesDirectedEdge ψ 0 seed) :
    full.substitution.ProlongableOn seed := by
  obtain ⟨first, tail, himage⟩ :=
    List.exists_cons_of_ne_nil (full.substitution.image_ne_nil seed)
  have himageTrav := fullMarkovSubstitution_image_traversal full hmarkov
    hslope hone hreturn (t := 0) (le_refl 0) hinitial
  rw [himage] at himageTrav
  have hfirstTrav : TraversesDirectedEdge ψ 0 first := by
    simpa using himageTrav.1
  have hfirst : first = seed :=
    traversesDirectedEdge_unique hfirstTrav hinitial
  subst first
  refine ⟨tail, ?_, himage⟩
  intro htail
  subst tail
  have hmetric := full.metric seed
  simp [wordMetricLength, himage] at hmetric
  nlinarith [seed.length_pos]

/-- Before deleting unused letters, the two geometric substitutions have the
same full directed-edge ray word and the expected substituted prefixes. -/
private structure FullCommonRayWord
    (A B : IntervalMap) (K : Finset I) (ψ : ℝ → I)
    (a b : ℝ) (ePlus : DirectedMarkovEdge K) where
  substitutionA : FullMarkovSubstitution A K a
  substitutionB : FullMarkovSubstitution B K b
  word : Symbolic.InfiniteWord (DirectedMarkovEdge K)
  fixedA : substitutionA.substitution.IsFixedPoint word
  fixedB : substitutionB.substitution.IsFixedPoint word
  prolongableA : substitutionA.substitution.ProlongableOn ePlus
  prolongableB : substitutionB.substitution.ProlongableOn ePlus
  itinerary : HasLiteralUnitSpeedItinerary ψ id DirectedMarkovEdge.length word
  prefixA : ∀ n : ℕ,
    substitutionA.substitution.iterateLetter n ePlus =
      word.take (substitutionA.substitution.iterateLetter n ePlus).length
  prefixB : ∀ n : ℕ,
    substitutionB.substitution.iterateLetter n ePlus =
      word.take (substitutionB.substitution.iterateLetter n ePlus).length

/-- Dilation equivariance identifies the two full-alphabet substitution
limits with the literal itinerary of the same ray. -/
private theorem exists_fullCommonRayWord
    {A B : IntervalMap} {K : Finset I} {ψ : ℝ → I}
    {p : I} {a b : ℝ} (ePlus : DirectedMarkovEdge K)
    (hK : IsCommonMarkovSet A B K)
    (hp : p ∈ K) (ha : 1 < a) (hb : 1 < b)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (he_forward : ePlus.forward = true)
    (he_source : ePlus.source = p)
    (hinitial : TraversesDirectedEdge ψ 0 ePlus)
    (hray : IsLocallyUnitSpeedRay ψ)
    (hreturnA : DilationReturnsOnRay ψ a A)
    (hreturnB : DilationReturnsOnRay ψ b B) :
    Nonempty (FullCommonRayWord A B K ψ a b ePlus) := by
  classical
  rcases hK with ⟨hzero, honeK, hforwardA, hforwardB, hmarkov⟩
  have hmarkovA : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn A (Set.Icc x y) ∧ IsStrictlyMonotoneOn A (Set.Icc x y) :=
    fun _ _ hxy ↦ (hmarkov hxy).1
  have hmarkovB : ∀ ⦃x y : I⦄, FinsetAdjacent K x y →
      IsAffineOn B (Set.Icc x y) ∧ IsStrictlyMonotoneOn B (Set.Icc x y) :=
    fun _ _ hxy ↦ (hmarkov hxy).2
  let fullA : FullMarkovSubstitution A K a := Classical.choice
    (exists_fullMarkovSubstitution hzero honeK hforwardA hmarkovA hAslope)
  let fullB : FullMarkovSubstitution B K b := Classical.choice
    (exists_fullMarkovSubstitution hzero honeK hforwardB hmarkovB hBslope)
  have hprolongA : fullA.substitution.ProlongableOn ePlus :=
    fullMarkovSubstitution_prolongable_of_initial fullA hmarkovA hAslope
      ha hreturnA hinitial
  have hprolongB : fullB.substitution.ProlongableOn ePlus :=
    fullMarkovSubstitution_prolongable_of_initial fullB hmarkovB hBslope
      hb hreturnB hinitial
  letI : Nonempty (DirectedMarkovEdge K) := ⟨ePlus⟩
  have hgrowthA : LetterImagesGrow fullA.substitution ePlus :=
    letterImagesGrow_of_metric_scales (fun e ↦ e.length_pos)
      fullA.metric ha ePlus
  have hgrowthB : LetterImagesGrow fullB.substitution ePlus :=
    letterImagesGrow_of_metric_scales (fun e ↦ e.length_pos)
      fullB.metric hb ePlus
  let wordA := prolongableLimitWord fullA.substitution ePlus hgrowthA
  let wordB := prolongableLimitWord fullB.substitution ePlus hgrowthB
  have hfixedA : fullA.substitution.IsFixedPoint wordA :=
    prolongableLimitWord_fixed hprolongA hgrowthA
  have hfixedB₀ : fullB.substitution.IsFixedPoint wordB :=
    prolongableLimitWord_fixed hprolongB hgrowthB
  have hitineraryA : HasLiteralUnitSpeedItinerary ψ id
      DirectedMarkovEdge.length wordA :=
    prolongableLimitWord_itinerary fullA hmarkovA hAslope ha hreturnA
      hinitial hprolongA hgrowthA
  have hitineraryB : HasLiteralUnitSpeedItinerary ψ id
      DirectedMarkovEdge.length wordB :=
    prolongableLimitWord_itinerary fullB hmarkovB hBslope hb hreturnB
      hinitial hprolongB hgrowthB
  have hfirstA : wordA 0 = ePlus := by
    have htrav := hitineraryA.2.2 0
    simp only [id_eq] at htrav
    have htrav0 : TraversesDirectedEdge ψ 0 (wordA 0) := by
      simpa [prefixMetricLength] using htrav
    exact traversesDirectedEdge_unique htrav0 hinitial
  have hfirstB : wordB 0 = ePlus := by
    have htrav := hitineraryB.2.2 0
    simp only [id_eq] at htrav
    have htrav0 : TraversesDirectedEdge ψ 0 (wordB 0) := by
      simpa [prefixMetricLength] using htrav
    exact traversesDirectedEdge_unique htrav0 hinitial
  have hword : wordA = wordB :=
    literalUnitSpeedItinerary_unique hitineraryA hitineraryB
      (hfirstA.trans hfirstB.symm)
  have hfixedB : fullB.substitution.IsFixedPoint wordA := by
    rw [hword]
    exact hfixedB₀
  have hprefixA (n : ℕ) : fullA.substitution.iterateLetter n ePlus =
      wordA.take (fullA.substitution.iterateLetter n ePlus).length :=
    iterateLetter_eq_take_prolongableLimitWord hprolongA hgrowthA n
  have hprefixB (n : ℕ) : fullB.substitution.iterateLetter n ePlus =
      wordA.take (fullB.substitution.iterateLetter n ePlus).length := by
    rw [hword]
    exact iterateLetter_eq_take_prolongableLimitWord hprolongB hgrowthB n
  exact ⟨{
    substitutionA := fullA
    substitutionB := fullB
    word := wordA
    fixedA := hfixedA
    fixedB := hfixedB
    prolongableA := hprolongA
    prolongableB := hprolongB
    itinerary := hitineraryA
    prefixA := hprefixA
    prefixB := hprefixB }⟩

/-- The nonnumerical core of the final package, after restricting both
substitutions to the common set of letters occurring in the ray word. -/
private structure CommonMarkovRayCodingCore
    (A B : IntervalMap) (K : Finset I) (ψ : ℝ → I) (a b : ℝ) where
  alphabet : OccurringDirectedAlphabet K
  alphabet_nonempty : alphabet.Nonempty
  substitutionA : Symbolic.Substitution alphabet
  substitutionB : Symbolic.Substitution alphabet
  seed : alphabet
  word : Symbolic.InfiniteWord alphabet
  every_letter_occurs : ∀ e : alphabet,
    Symbolic.Substitution.OccursInInfiniteWord e word
  fixedA : substitutionA.IsFixedPoint word
  fixedB : substitutionB.IsFixedPoint word
  prolongableA : substitutionA.ProlongableOn seed
  prolongableB : substitutionB.ProlongableOn seed
  generatingA : substitutionA.IsGeneratingLetter seed
  generatingB : substitutionB.IsGeneratingLetter seed
  modelsA : ModelsDirectedEdgeSubstitution A alphabet substitutionA
  modelsB : ModelsDirectedEdgeSubstitution B alphabet substitutionB
  itinerary : HasLiteralUnitSpeedItinerary ψ (occurringEdge alphabet)
    (fun e ↦ e.1.length) word
  prefixA : ∀ n : ℕ,
    substitutionA.iterateLetter n seed =
      word.take (substitutionA.iterateLetter n seed).length
  prefixB : ∀ n : ℕ,
    substitutionB.iterateLetter n seed =
      word.take (substitutionB.iterateLetter n seed).length
  imageMetricA : SubstitutionScalesLetterLengths substitutionA
    (fun e ↦ e.1.length) a
  imageMetricB : SubstitutionScalesLetterLengths substitutionB
    (fun e ↦ e.1.length) b

private theorem substitution_iterateLetter_map_of_intertwining
    {α β : Type*} (coding : α → β)
    (source : Symbolic.Substitution α) (target : Symbolic.Substitution β)
    (himage : ∀ a, (source a).map coding = target (coding a))
    (n : ℕ) (a : α) :
    (source.iterateLetter n a).map coding =
      target.iterateLetter n (coding a) := by
  have hmapWord (w : Symbolic.Word α) :
      (source.mapWord w).map coding = target.mapWord (w.map coding) := by
    induction w with
    | nil => simp
    | cons z w ih =>
        calc
          (source.mapWord (z :: w)).map coding =
              ((source z) ++ source.mapWord w).map coding := rfl
          _ = (target (coding z)) ++ target.mapWord (w.map coding) := by
            rw [List.map_append, himage, ih]
          _ = target.mapWord (coding z :: w.map coding) :=
            (Symbolic.Substitution.mapWord_cons target (coding z)
              (w.map coding)).symm
          _ = target.mapWord ((z :: w).map coding) := rfl
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Symbolic.Substitution.iterateLetter_succ,
        Symbolic.Substitution.iterateLetter_succ, hmapWord, ih]

/-- Restriction to occurring letters is simultaneously closed under both
fixed substitutions and makes the initial edge generating for both. -/
private theorem restrict_fullCommonRayWord_to_occurring
    {A B : IntervalMap} {K : Finset I} {ψ : ℝ → I}
    {a b : ℝ} {ePlus : DirectedMarkovEdge K}
    (full : FullCommonRayWord A B K ψ a b ePlus) :
    ∃ core : CommonMarkovRayCodingCore A B K ψ a b,
      core.seed.1 = ePlus := by
  classical
  have hseedAtZero : full.word 0 = ePlus := by
    have hp := full.prefixA 0
    have hleft : 0 <
        (full.substitutionA.substitution.iterateLetter 0 ePlus).length := by simp
    have hright : 0 < (full.word.take
        (full.substitutionA.substitution.iterateLetter 0 ePlus).length).length := by
      simpa using hleft
    have hget :
        (full.substitutionA.substitution.iterateLetter 0 ePlus)[0]'hleft =
          (full.word.take
            (full.substitutionA.substitution.iterateLetter 0 ePlus).length)[0]'hright :=
      getElem_congr hp rfl hleft
    have htake := Stream'.take_get (m := 0)
      (n := (full.substitutionA.substitution.iterateLetter 0 ePlus).length)
      (a := full.word) hright
    exact (hget.trans htake).symm
  let occFinite :=
    Symbolic.Substitution.occurringAlphabet_finite full.word
  let alphabet : OccurringDirectedAlphabet K := occFinite.toFinset
  let q : Symbolic.Substitution.OccurringAlphabet full.word ≃ alphabet :=
    occFinite.subtypeEquivToFinset
  let seedOcc : Symbolic.Substitution.OccurringAlphabet full.word :=
    ⟨ePlus, ⟨0, hseedAtZero⟩⟩
  let seed : alphabet := q seedOcc
  let wordOcc := Symbolic.Substitution.wordOnOccurringAlphabet full.word
  let word : Symbolic.InfiniteWord alphabet := fun n ↦ q (wordOcc n)
  let restrictedA := full.substitutionA.substitution.restrictToOccurringAlphabet
    full.word full.fixedA
  let restrictedB := full.substitutionB.substitution.restrictToOccurringAlphabet
    full.word full.fixedB
  let substitutionA : Symbolic.Substitution alphabet := restrictedA.relabel q
  let substitutionB : Symbolic.Substitution alphabet := restrictedB.relabel q
  have hseedValue : seed.1 = ePlus := rfl
  have hwordValue (n : ℕ) : (word n).1 = full.word n := rfl
  have hwordValues : Stream'.map Subtype.val word = full.word := by
    funext n
    exact hwordValue n
  have himageA (e : alphabet) :
      (substitutionA e).map Subtype.val =
        full.substitutionA.substitution e.1 := by
    have hrestricted :=
      full.substitutionA.substitution.restrictToOccurringAlphabet_image_values
        full.word full.fixedA (q.symm e)
    simpa [substitutionA, restrictedA, Symbolic.Substitution.relabel,
      List.map_map] using hrestricted
  have himageB (e : alphabet) :
      (substitutionB e).map Subtype.val =
        full.substitutionB.substitution e.1 := by
    have hrestricted :=
      full.substitutionB.substitution.restrictToOccurringAlphabet_image_values
        full.word full.fixedB (q.symm e)
    simpa [substitutionB, restrictedB, Symbolic.Substitution.relabel,
      List.map_map] using hrestricted
  let values : Symbolic.LetterCoding alphabet (DirectedMarkovEdge K) :=
    ⟨Subtype.val⟩
  have hfixedA : substitutionA.IsFixedPoint word := by
    have hnatural := Symbolic.LetterCoding.mapInfinite_substitution values
      substitutionA full.substitutionA.substitution himageA word
    have hvalues : values.mapInfinite word = full.word := hwordValues
    rw [hvalues, full.fixedA] at hnatural
    apply funext
    intro n
    apply Subtype.ext
    simpa [values, hwordValue] using congrFun hnatural n
  have hfixedB : substitutionB.IsFixedPoint word := by
    have hnatural := Symbolic.LetterCoding.mapInfinite_substitution values
      substitutionB full.substitutionB.substitution himageB word
    have hvalues : values.mapInfinite word = full.word := hwordValues
    rw [hvalues, full.fixedB] at hnatural
    apply funext
    intro n
    apply Subtype.ext
    simpa [values, hwordValue] using congrFun hnatural n
  have hprolongA : substitutionA.ProlongableOn seed := by
    rcases full.prolongableA with ⟨tail, htail, hfullImage⟩
    obtain ⟨first, rest, himage⟩ :=
      List.exists_cons_of_ne_nil (substitutionA.image_ne_nil seed)
    have hvalues := himageA seed
    rw [himage, hseedValue, hfullImage] at hvalues
    simp only [List.map_cons] at hvalues
    have hparts := List.cons.inj hvalues
    have hfirst : first = seed := by
      apply Subtype.ext
      exact hparts.1.trans hseedValue.symm
    subst first
    refine ⟨rest, ?_, himage⟩
    intro hrest
    subst rest
    simp at hparts
    exact htail hparts.2
  have hprolongB : substitutionB.ProlongableOn seed := by
    rcases full.prolongableB with ⟨tail, htail, hfullImage⟩
    obtain ⟨first, rest, himage⟩ :=
      List.exists_cons_of_ne_nil (substitutionB.image_ne_nil seed)
    have hvalues := himageB seed
    rw [himage, hseedValue, hfullImage] at hvalues
    simp only [List.map_cons] at hvalues
    have hparts := List.cons.inj hvalues
    have hfirst : first = seed := by
      apply Subtype.ext
      exact hparts.1.trans hseedValue.symm
    subst first
    refine ⟨rest, ?_, himage⟩
    intro hrest
    subst rest
    simp at hparts
    exact htail hparts.2
  have htakeValues (n : ℕ) :
      (word.take n).map Subtype.val = full.word.take n := by
    rw [Stream'.map_take]
    exact congrArg (Stream'.take n) hwordValues
  have hiterateA (n : ℕ) (e : alphabet) :
      (substitutionA.iterateLetter n e).map Subtype.val =
        full.substitutionA.substitution.iterateLetter n e.1 :=
    substitution_iterateLetter_map_of_intertwining Subtype.val
      substitutionA full.substitutionA.substitution himageA n e
  have hiterateB (n : ℕ) (e : alphabet) :
      (substitutionB.iterateLetter n e).map Subtype.val =
        full.substitutionB.substitution.iterateLetter n e.1 :=
    substitution_iterateLetter_map_of_intertwining Subtype.val
      substitutionB full.substitutionB.substitution himageB n e
  have hprefixA (n : ℕ) : substitutionA.iterateLetter n seed =
      word.take (substitutionA.iterateLetter n seed).length := by
    apply (List.map_injective_iff.mpr Subtype.val_injective)
    have hiter := hiterateA n seed
    have hlen : (substitutionA.iterateLetter n seed).length =
        (full.substitutionA.substitution.iterateLetter n ePlus).length := by
      simpa [hseedValue] using congrArg List.length hiter
    calc
      (substitutionA.iterateLetter n seed).map Subtype.val =
          full.substitutionA.substitution.iterateLetter n ePlus := by
        simpa [hseedValue] using hiter
      _ = full.word.take
          (full.substitutionA.substitution.iterateLetter n ePlus).length :=
        full.prefixA n
      _ = full.word.take (substitutionA.iterateLetter n seed).length := by
        rw [hlen]
      _ = (word.take (substitutionA.iterateLetter n seed).length).map
          Subtype.val := (htakeValues _).symm
  have hprefixB (n : ℕ) : substitutionB.iterateLetter n seed =
      word.take (substitutionB.iterateLetter n seed).length := by
    apply (List.map_injective_iff.mpr Subtype.val_injective)
    have hiter := hiterateB n seed
    have hlen : (substitutionB.iterateLetter n seed).length =
        (full.substitutionB.substitution.iterateLetter n ePlus).length := by
      simpa [hseedValue] using congrArg List.length hiter
    calc
      (substitutionB.iterateLetter n seed).map Subtype.val =
          full.substitutionB.substitution.iterateLetter n ePlus := by
        simpa [hseedValue] using hiter
      _ = full.word.take
          (full.substitutionB.substitution.iterateLetter n ePlus).length :=
        full.prefixB n
      _ = full.word.take (substitutionB.iterateLetter n seed).length := by
        rw [hlen]
      _ = (word.take (substitutionB.iterateLetter n seed).length).map
          Subtype.val := (htakeValues _).symm
  have hevery (e : alphabet) :
      Symbolic.Substitution.OccursInInfiniteWord e word := by
    have heOcc : e.1 ∈ Symbolic.Substitution.OccurringAlphabet full.word :=
      occFinite.mem_toFinset.mp e.2
    rcases heOcc with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    rw [hwordValue n]
    exact hn
  have hgeneratingA : substitutionA.IsGeneratingLetter seed := by
    intro e
    exact substitutionA.isGeneratingLetter_of_iterateLetter_eq_take
      hprolongA hprefixA e (hevery e)
  have hgeneratingB : substitutionB.IsGeneratingLetter seed := by
    intro e
    exact substitutionB.isGeneratingLetter_of_iterateLetter_eq_take
      hprolongB hprefixB e (hevery e)
  have hmodelsA : ModelsDirectedEdgeSubstitution A alphabet substitutionA := by
    intro e
    have hgeom : geometricEdgeWord alphabet (substitutionA e) =
        full.substitutionA.substitution e.1 := by
      simpa [geometricEdgeWord, occurringEdge] using himageA e
    rw [hgeom]
    exact ⟨full.substitutionA.path e.1, full.substitutionA.starts e.1,
      full.substitutionA.ends e.1⟩
  have hmodelsB : ModelsDirectedEdgeSubstitution B alphabet substitutionB := by
    intro e
    have hgeom : geometricEdgeWord alphabet (substitutionB e) =
        full.substitutionB.substitution e.1 := by
      simpa [geometricEdgeWord, occurringEdge] using himageB e
    rw [hgeom]
    exact ⟨full.substitutionB.path e.1, full.substitutionB.starts e.1,
      full.substitutionB.ends e.1⟩
  have hmetricA : SubstitutionScalesLetterLengths substitutionA
      (fun e ↦ e.1.length) a := by
    intro e
    calc
      wordMetricLength (fun e : alphabet ↦ e.1.length) (substitutionA e) =
          wordMetricLength DirectedMarkovEdge.length
            (full.substitutionA.substitution e.1) := by
        rw [wordMetricLength, wordMetricLength]
        have hv := congrArg
          (fun w : List (DirectedMarkovEdge K) ↦
            (w.map DirectedMarkovEdge.length).sum) (himageA e)
        simpa [List.map_map] using hv
      _ = a * e.1.length := full.substitutionA.metric e.1
  have hmetricB : SubstitutionScalesLetterLengths substitutionB
      (fun e ↦ e.1.length) b := by
    intro e
    calc
      wordMetricLength (fun e : alphabet ↦ e.1.length) (substitutionB e) =
          wordMetricLength DirectedMarkovEdge.length
            (full.substitutionB.substitution e.1) := by
        rw [wordMetricLength, wordMetricLength]
        have hv := congrArg
          (fun w : List (DirectedMarkovEdge K) ↦
            (w.map DirectedMarkovEdge.length).sum) (himageB e)
        simpa [List.map_map] using hv
      _ = b * e.1.length := full.substitutionB.metric e.1
  have hitinerary : HasLiteralUnitSpeedItinerary ψ (occurringEdge alphabet)
      (fun e ↦ e.1.length) word := by
    refine ⟨fun _ ↦ rfl, ?_, ?_⟩
    · intro n
      change (word n).1.target = (word (n + 1)).1.source
      rw [hwordValue n, hwordValue (n + 1)]
      exact full.itinerary.2.1 n
    · intro n
      have htime : prefixMetricLength (fun e : alphabet ↦ e.1.length) word n =
          prefixMetricLength DirectedMarkovEdge.length full.word n := by
        apply Finset.sum_congr rfl
        intro i hi
        change (word i).1.length = (full.word i).length
        rw [hwordValue i]
      change TraversesDirectedEdge ψ
        (prefixMetricLength (fun e : alphabet ↦ e.1.length) word n) (word n).1
      rw [htime, hwordValue n]
      exact full.itinerary.2.2 n
  have halphabet : alphabet.Nonempty := ⟨seed.1, seed.2⟩
  refine ⟨{
    alphabet := alphabet
    alphabet_nonempty := halphabet
    substitutionA := substitutionA
    substitutionB := substitutionB
    seed := seed
    word := word
    every_letter_occurs := hevery
    fixedA := hfixedA
    fixedB := hfixedB
    prolongableA := hprolongA
    prolongableB := hprolongB
    generatingA := hgeneratingA
    generatingB := hgeneratingB
    modelsA := hmodelsA
    modelsB := hmodelsB
    itinerary := hitinerary
    prefixA := hprefixA
    prefixB := hprefixB
    imageMetricA := hmetricA
    imageMetricB := hmetricB }, hseedValue⟩

/--
Directed-edge substitution construction.  The initial edge is supplied
explicitly, so neither availability of the selected side nor its orientation
is hidden in a minimum-choice operation on `K`.
-/
theorem directed_edge_substitutions_and_common_ray_word
    {A B : IntervalMap} {K : Finset I} {ψ : ℝ → I}
    {p : I} {a b : ℝ} (ePlus : DirectedMarkovEdge K)
    (hK : IsCommonMarkovSet A B K)
    (hcomm : Commute A B)
    (hp : p ∈ K)
    (ha : 1 < a) (hb : 1 < b)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (he_forward : ePlus.forward = true)
    (he_source : ePlus.source = p)
    (hinitial : TraversesDirectedEdge ψ 0 ePlus)
    (hray : IsLocallyUnitSpeedRay ψ)
    (honto : IsOntoNonnegativeRay ψ)
    (hreturnA : DilationReturnsOnRay ψ a A)
    (hreturnB : DilationReturnsOnRay ψ b B) :
    ∃ data : CommonRayFixedWord A B K ψ a b,
      data.seed.1 = ePlus := by
  classical
  let full : FullCommonRayWord A B K ψ a b ePlus := Classical.choice
    (exists_fullCommonRayWord ePlus hK hp ha hb hAslope hBslope
      he_forward he_source hinitial hray hreturnA hreturnB)
  obtain ⟨core, hseed⟩ := restrict_fullCommonRayWord_to_occurring full
  let letterLength : core.alphabet → ℝ := fun e ↦ e.1.length
  letI : Nonempty core.alphabet := ⟨core.seed⟩
  have hlengthPos : ∀ e : core.alphabet, 0 < letterLength e :=
    fun e ↦ e.1.length_pos
  have hgrowthA : LetterImagesGrow core.substitutionA core.seed :=
    letterImagesGrow_of_metric_scales hlengthPos core.imageMetricA ha core.seed
  have hgrowthB : LetterImagesGrow core.substitutionB core.seed :=
    letterImagesGrow_of_metric_scales hlengthPos core.imageMetricB hb core.seed
  have hprefixMetricA (n : ℕ) :
      wordMetricLength letterLength
          (core.substitutionA.iterateLetter n core.seed) =
        a ^ n * letterLength core.seed :=
    wordMetricLength_iterateLetter_of_scales core.imageMetricA core.seed n
  have hprefixMetricB (n : ℕ) :
      wordMetricLength letterLength
          (core.substitutionB.iterateLetter n core.seed) =
        b ^ n * letterLength core.seed :=
    wordMetricLength_iterateLetter_of_scales core.imageMetricB core.seed n
  have heigenA : IsPositiveLengthEigenvector core.substitutionA
      letterLength a :=
    substitution_metric_lengths_give_incidence_identity hlengthPos
      core.imageMetricA
  have heigenB : IsPositiveLengthEigenvector core.substitutionB
      letterLength b :=
    substitution_metric_lengths_give_incidence_identity hlengthPos
      core.imageMetricB
  refine ⟨{
    alphabet := core.alphabet
    alphabet_nonempty := core.alphabet_nonempty
    substitutionA := core.substitutionA
    substitutionB := core.substitutionB
    seed := core.seed
    word := core.word
    every_letter_occurs := core.every_letter_occurs
    fixedA := core.fixedA
    fixedB := core.fixedB
    prolongableA := core.prolongableA
    prolongableB := core.prolongableB
    generatingA := core.generatingA
    generatingB := core.generatingB
    modelsA := core.modelsA
    modelsB := core.modelsB
    letterLength := letterLength
    letterLength_eq := fun _ ↦ rfl
    letterLength_pos := hlengthPos
    itinerary := core.itinerary
    prefixA := core.prefixA
    prefixB := core.prefixB
    prefixMetricA := hprefixMetricA
    prefixMetricB := hprefixMetricB
    imageMetricA := core.imageMetricA
    imageMetricB := core.imageMetricB
    lengthEigenA := heigenA
    lengthEigenB := heigenB
    growthA := hgrowthA
    growthB := hgrowthB
    one_lt_a := ha
    one_lt_b := hb
    ray_unit_speed := hray
    ray_onto := honto
    ray_returnA := hreturnA
    ray_returnB := hreturnB }, hseed⟩

/-! ## Perron growth and powered substitutions -/

/-- A complex eigenvalue of a finite nonnegative integral matrix. -/
def IsComplexEigenvalue {α : Type*} [Fintype α]
    (M : Matrix α α ℕ) (z : ℂ) : Prop :=
  ∃ v : α → ℂ, v ≠ 0 ∧
    ∀ i : α, (∑ j : α, (M i j : ℂ) * v j) = z * v i

/-- `λ` is the real dominant eigenvalue (the spectral radius) of `M`. -/
def IsDominantEigenvalue {α : Type*} [Fintype α]
    (M : Matrix α α ℕ) (eigenvalue : ℝ) : Prop :=
  IsComplexEigenvalue M (eigenvalue : ℂ) ∧
    ∀ z : ℂ, IsComplexEigenvalue M z → ‖z‖ ≤ eigenvalue

/--
A Perron number is a real algebraic integer greater than one whose distinct
complex algebraic conjugates have strictly smaller modulus.
-/
def IsPerronNumber (value : ℝ) : Prop :=
  1 < value ∧ IsIntegral ℤ value ∧
    ∀ z : ℂ, IsConjRoot ℚ (value : ℂ) z → z ≠ (value : ℂ) →
      ‖z‖ < value

/-- A real eigenvector equation for a nonnegative integral matrix. -/
def NatMatrixEigenvectorEquation {α : Type*} [Fintype α]
    (M : Matrix α α ℕ) (v : α → ℝ) (eigenvalue : ℝ) : Prop :=
  ∀ i : α, (∑ j : α, (M i j : ℝ) * v j) = eigenvalue * v i

/-- A strictly positive real eigenvector supplies the weighted max norm in
which every complex eigenvalue is bounded by the given real eigenvalue. -/
theorem positive_eigenvector_isDominant
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

/-- The entrywise complexification of a natural matrix. -/
private def complexification {α : Type*}
    (M : Matrix α α ℕ) : Matrix α α ℂ :=
  M.map (Nat.castRingHom ℂ)

/-- The entrywise integral lift used to witness algebraic integrality of
matrix eigenvalues. -/
private def integerification {α : Type*}
    (M : Matrix α α ℕ) : Matrix α α ℤ :=
  M.map (Nat.castRingHom ℤ)

/-- The rational lift used to transport characteristic-polynomial roots
between algebraic conjugates. -/
private def rationalification {α : Type*}
    (M : Matrix α α ℕ) : Matrix α α ℚ :=
  M.map (Nat.castRingHom ℚ)

/-- Our explicit complex eigenvector predicate is the standard
finite-dimensional eigenvalue predicate for the complexified matrix. -/
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

/-- The explicit eigenvalue predicate is spectrum membership for the
complexified matrix. -/
private theorem isComplexEigenvalue_iff_mem_spectrum
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) (z : ℂ) :
    IsComplexEigenvalue M z ↔ z ∈ spectrum ℂ (complexification M) := by
  rw [isComplexEigenvalue_iff_hasEigenvalue,
    Module.End.hasEigenvalue_iff_mem_spectrum,
    Matrix.spectrum_toLin']

/-- A real eigenvalue of a finite natural matrix is an algebraic integer. -/
private theorem natMatrix_real_eigenvalue_isIntegral
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) (x : ℝ)
    (hx : IsComplexEigenvalue M (x : ℂ)) :
    IsIntegral ℤ x := by
  let MI : Matrix α α ℤ := integerification M
  refine ⟨MI.charpoly, Matrix.charpoly_monic MI, ?_⟩
  change Polynomial.aeval x MI.charpoly = 0
  have hspectrum : (x : ℂ) ∈ spectrum ℂ (complexification M) :=
    (isComplexEigenvalue_iff_mem_spectrum M (x : ℂ)).mp hx
  have hroot : (complexification M).charpoly.IsRoot (x : ℂ) :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly).mp hspectrum
  have hmap : MI.charpoly.map (algebraMap ℤ ℂ) =
      (complexification M).charpoly := by
    rw [← Matrix.charpoly_map]
    apply congrArg Matrix.charpoly
    ext i j
    simp [MI, integerification, complexification]
  have hevalC :
      (MI.charpoly.map (algebraMap ℤ ℂ)).eval (x : ℂ) = 0 := by
    rw [hmap]
    exact hroot
  have htransport := Polynomial.map_aeval_eq_aeval_map
    (R := ℤ) (S := ℝ) (T := ℤ) (U := ℂ)
    (φ := RingHom.id ℤ) (ψ := Complex.ofRealHom)
    (by ext n; simp) MI.charpoly x
  have hzero : Complex.ofRealHom (Polynomial.aeval x MI.charpoly) = 0 := by
    rw [htransport]
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using hevalC
  exact Complex.ofReal_injective (by simpa using hzero)

/-- Every rational algebraic conjugate of an eigenvalue of a natural matrix
is again a complex eigenvalue of that same matrix. -/
private theorem natMatrix_conjugate_isComplexEigenvalue
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) {x z : ℂ}
    (hx : IsComplexEigenvalue M x)
    (hz : IsConjRoot ℚ x z) :
    IsComplexEigenvalue M z := by
  let MQ : Matrix α α ℚ := rationalification M
  have hxroot : (complexification M).charpoly.IsRoot x :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mp
      ((isComplexEigenvalue_iff_mem_spectrum M x).mp hx)
  have hmap : MQ.charpoly.map (algebraMap ℚ ℂ) =
      (complexification M).charpoly := by
    rw [← Matrix.charpoly_map]
    apply congrArg Matrix.charpoly
    ext i j
    simp [MQ, rationalification, complexification]
  have hxMQ : Polynomial.aeval x MQ.charpoly = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [hmap]
    exact hxroot
  have hmin_dvd : minpoly ℚ x ∣ MQ.charpoly := minpoly.dvd ℚ x hxMQ
  obtain ⟨q, hq⟩ := hmin_dvd
  have hzmin : ((minpoly ℚ x).map (algebraMap ℚ ℂ)).eval z = 0 := by
    have h := IsConjRoot.aeval_eq_zero hz
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
    exact h
  have hzroot : (MQ.charpoly.map (algebraMap ℚ ℂ)).IsRoot z := by
    rw [hq, Polynomial.map_mul, Polynomial.IsRoot, Polynomial.eval_mul,
      hzmin, zero_mul]
  apply (isComplexEigenvalue_iff_mem_spectrum M z).mpr
  apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
  rwa [← hmap]

/-- Entrywise complexification commutes with natural matrix powers. -/
private theorem complexification_pow
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) (n : ℕ) :
    complexification (M ^ n) = complexification M ^ n := by
  simpa [complexification] using
    Matrix.map_pow M (Nat.castRingHom ℂ) n

/-- Spectral mapping for a positive natural power, expressed through the
custom matrix-eigenvalue predicate used by the substitution package. -/
private theorem isComplexEigenvalue_pow_iff
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) {n : ℕ} (hn : 0 < n) (z : ℂ) :
    IsComplexEigenvalue (M ^ n) z ↔
      ∃ w : ℂ, IsComplexEigenvalue M w ∧ w ^ n = z := by
  rw [isComplexEigenvalue_iff_mem_spectrum, complexification_pow,
    spectrum.map_pow_of_pos _ hn]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (isComplexEigenvalue_iff_mem_spectrum M w).mpr hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (isComplexEigenvalue_iff_mem_spectrum M w).mp hw, rfl⟩

/-- Dominance of a nonnegative integral matrix eigenvalue passes to every
positive natural matrix power. -/
theorem dominantEigenvalue_pow
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℕ) (eigenvalue : ℝ)
    (hdom : IsDominantEigenvalue M eigenvalue)
    {n : ℕ} (hn : 0 < n) :
    IsDominantEigenvalue (M ^ n) (eigenvalue ^ n) := by
  constructor
  · apply (isComplexEigenvalue_pow_iff M hn _).mpr
    refine ⟨(eigenvalue : ℂ), hdom.1, ?_⟩
    norm_cast
  · intro z hz
    rcases (isComplexEigenvalue_pow_iff M hn z).mp hz with ⟨w, hw, rfl⟩
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg w) (hdom.2 w hw) n

/-- Transposition preserves the explicitly presented complex eigenvalues. -/
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

/-! The equality case in the weighted spectral-radius estimate is most
conveniently expressed by an elementary variance identity. -/

private theorem weighted_real_variance
    {α : Type*} [Fintype α]
    (p a : α → ℝ) (A b : ℝ)
    (hp : ∑ j, p j = A) (hb : ∑ j, p j * a j = A * b) :
    ∑ j, p j * (a j - b) ^ 2 =
      (∑ j, p j * (a j) ^ 2) - A * b ^ 2 := by
  calc
    _ = ∑ j, (p j * a j ^ 2 - 2 * b * (p j * a j) + b ^ 2 * p j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ j, p j * a j ^ 2) - 2 * b * (∑ j, p j * a j) +
        b ^ 2 * (∑ j, p j) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ = _ := by rw [hp, hb]; ring

private theorem weighted_complex_variance
    {α : Type*} [Fintype α]
    (p : α → ℝ) (x : α → ℂ) (A : ℝ) (y : ℂ)
    (hp : ∑ j, p j = A)
    (hy : ∑ j, (p j : ℂ) * x j = (A : ℂ) * y) :
    ∑ j, p j * Complex.normSq (x j - y) =
      (∑ j, p j * Complex.normSq (x j)) - A * Complex.normSq y := by
  have hyre : ∑ j, p j * (x j).re = A * y.re := by
    simpa using congrArg Complex.re hy
  have hyim : ∑ j, p j * (x j).im = A * y.im := by
    simpa using congrArg Complex.im hy
  have hre := weighted_real_variance p (fun j => (x j).re) A y.re hp hyre
  have him := weighted_real_variance p (fun j => (x j).im) A y.im hp hyim
  have hre' :
      (∑ j, p j * ((x j).re - y.re) * ((x j).re - y.re)) =
        (∑ j, p j * (x j).re * (x j).re) - A * (y.re * y.re) := by
    simpa only [pow_two, mul_assoc] using hre
  have him' :
      (∑ j, p j * ((x j).im - y.im) * ((x j).im - y.im)) =
        (∑ j, p j * (x j).im * (x j).im) - A * (y.im * y.im) := by
    simpa only [pow_two, mul_assoc] using him
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [mul_assoc] at hre' him' ⊢
  rw [hre', him']
  ring

/-- If a nonnegative weighted mean lies on the same norm sphere as all of
its summands, every summand with positive weight equals that mean. -/
private theorem weighted_extreme
    {α : Type*} [Fintype α]
    (p : α → ℝ) (x : α → ℂ) (A : ℝ) (y : ℂ)
    (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = A)
    (hy : ∑ j, (p j : ℂ) * x j = (A : ℂ) * y)
    (hx : ∀ j, Complex.normSq (x j) ≤ Complex.normSq y)
    {k : α} (hk : 0 < p k) : x k = y := by
  have hvar := weighted_complex_variance p x A y hp hy
  have hsum_le :
      (∑ j, p j * Complex.normSq (x j)) ≤ A * Complex.normSq y := by
    calc
      _ ≤ ∑ j, p j * Complex.normSq y := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hx j) (hp0 j)
      _ = _ := by rw [← Finset.sum_mul, hp]
  have hvar_nonpos :
      (∑ j, p j * Complex.normSq (x j - y)) ≤ 0 := by
    rw [hvar]
    linarith
  have hterm_le :
      p k * Complex.normSq (x k - y) ≤
        ∑ j, p j * Complex.normSq (x j - y) := by
    exact Finset.single_le_sum
      (f := fun j => p j * Complex.normSq (x j - y))
      (fun j _ => mul_nonneg (hp0 j) (Complex.normSq_nonneg _))
      (Finset.mem_univ k)
  have hterm_nonneg : 0 ≤ p k * Complex.normSq (x k - y) :=
    mul_nonneg (hp0 k) (Complex.normSq_nonneg _)
  have hterm_zero : p k * Complex.normSq (x k - y) = 0 :=
    le_antisymm (hterm_le.trans hvar_nonpos) hterm_nonneg
  have hnormzero : Complex.normSq (x k - y) = 0 :=
    (mul_eq_zero.mp hterm_zero).resolve_left hk.ne'
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hnormzero)

/-- A peripheral complex eigenvalue of a natural matrix with a strictly
positive real eigenvector has phase order dividing the factorial of the
matrix size. -/
private theorem peripheral_eigenvalue_factorial_power_eq
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (M : Matrix α α ℕ) (v : α → ℝ) (eigenvalue : ℝ)
    (hv : ∀ i, 0 < v i) (hvalue : 0 < eigenvalue)
    (heigen : NatMatrixEigenvectorEquation M v eigenvalue)
    {z : ℂ} (hz : IsComplexEigenvalue M z)
    (hznorm : ‖z‖ = eigenvalue) :
    z ^ (Fintype.card α).factorial =
      (eigenvalue : ℂ) ^ (Fintype.card α).factorial := by
  rcases hz with ⟨w, hw, heigenz⟩
  let x : α → ℂ := fun i => w i / (v i : ℂ)
  let ζ : ℂ := z / (eigenvalue : ℂ)
  have heigenvalue_ne : (eigenvalue : ℂ) ≠ 0 := by
    exact_mod_cast hvalue.ne'
  have hz_ne : z ≠ 0 := by
    intro hz0
    simp [hz0] at hznorm
    linarith
  have hζ_ne : ζ ≠ 0 := div_ne_zero hz_ne heigenvalue_ne
  have hζ_norm : ‖ζ‖ = 1 := by
    simp only [ζ]
    rw [norm_div, hznorm]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_pos hvalue, div_self hvalue.ne']
  have hζ_normSq : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hζ_norm]
    norm_num
  have hx_ne : x ≠ 0 := by
    intro hx0
    apply hw
    funext i
    have hi := congrFun hx0 i
    simp only [Pi.zero_apply] at hi
    simpa [x, (ne_of_gt (hv i))] using hi
  obtain ⟨i₀, _hi₀mem, hi₀⟩ :=
    Finset.univ.exists_max_image (fun i => Complex.normSq (x i))
      Finset.univ_nonempty
  have hxi₀ : x i₀ ≠ 0 := by
    intro hzero
    apply hx_ne
    funext j
    apply Complex.normSq_eq_zero.mp
    apply le_antisymm
    · simpa [hzero] using hi₀ j (Finset.mem_univ j)
    · exact Complex.normSq_nonneg _
  let IsMax : α → Prop := fun i =>
    ∀ j, Complex.normSq (x j) ≤ Complex.normSq (x i)
  have hi₀max : IsMax i₀ := fun j => hi₀ j (Finset.mem_univ j)
  have hstep (i : α) (hi : IsMax i) :
      ∃ k : α, IsMax k ∧ x k = ζ * x i := by
    have hex : ∃ k : α, 0 < M i k := by
      by_contra hnone
      have hnot : ∀ k : α, ¬ 0 < M i k := fun k hk => hnone ⟨k, hk⟩
      have hrow : ∀ k : α, M i k = 0 := fun k =>
        Nat.eq_zero_of_not_pos (hnot k)
      have h := heigen i
      simp [hrow] at h
      exact h.elim hvalue.ne' (hv i).ne'
    obtain ⟨k, hk⟩ := hex
    let p : α → ℝ := fun j => (M i j : ℝ) * v j
    let A : ℝ := eigenvalue * v i
    have hp0 : ∀ j, 0 ≤ p j := fun j =>
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hv j))
    have hp : ∑ j, p j = A := by
      simpa [p, A] using heigen i
    have hy : ∑ j, (p j : ℂ) * x j = (A : ℂ) * (ζ * x i) := by
      calc
        _ = ∑ j, (M i j : ℂ) * w j := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [p, x]
          push_cast
          field_simp [(ne_of_gt (hv j))]
        _ = z * w i := heigenz i
        _ = (A : ℂ) * (ζ * x i) := by
          simp only [A, ζ, x]
          push_cast
          field_simp [heigenvalue_ne, (ne_of_gt (hv i))]
    have hyMax : ∀ j, Complex.normSq (x j) ≤
        Complex.normSq (ζ * x i) := by
      intro j
      rw [Complex.normSq_mul, hζ_normSq, one_mul]
      exact hi j
    have hpk : 0 < p k := by
      exact mul_pos (by exact_mod_cast hk) (hv k)
    have hkphase : x k = ζ * x i :=
      weighted_extreme p x A (ζ * x i) hp0 hp hy hyMax hpk
    refine ⟨k, ?_, hkphase⟩
    intro j
    calc
      Complex.normSq (x j) ≤ Complex.normSq (x i) := hi j
      _ = Complex.normSq (x k) := by
        rw [hkphase, Complex.normSq_mul, hζ_normSq, one_mul]
  let MaxState := {i : α // IsMax i}
  let nextIndex : MaxState → α := fun i =>
    Classical.choose (hstep i.1 i.2)
  have nextIndex_spec (i : MaxState) :
      IsMax (nextIndex i) ∧ x (nextIndex i) = ζ * x i.1 :=
    Classical.choose_spec (hstep i.1 i.2)
  let next : MaxState → MaxState := fun i =>
    ⟨nextIndex i, (nextIndex_spec i).1⟩
  have hnext (i : MaxState) : x (next i).1 = ζ * x i.1 := by
    exact (nextIndex_spec i).2
  let s₀ : MaxState := ⟨i₀, hi₀max⟩
  have hiterate (n : ℕ) :
      x ((next^[n] s₀).1) = ζ ^ n * x i₀ := by
    induction n with
    | zero => simp [s₀]
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        rw [hnext, ih, pow_succ']
        ring
  let orbit : Fin (Fintype.card α + 1) → α := fun n =>
    (next^[n.1] s₀).1
  obtain ⟨a, b, hab, horbit⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt orbit (by simp)
  have habval : a.1 ≠ b.1 := fun h => hab (Fin.ext h)
  have hrepeat {m n : ℕ} (hmn : m < n)
      (horbit' : (next^[m] s₀).1 = (next^[n] s₀).1) :
      ζ ^ (n - m) = 1 := by
    have hphase := congrArg x horbit'
    rw [hiterate m, hiterate n] at hphase
    have hleft_ne : ζ ^ m * x i₀ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hζ_ne) hxi₀
    apply mul_left_cancel₀ hleft_ne
    calc
      (ζ ^ m * x i₀) * ζ ^ (n - m) = ζ ^ n * x i₀ := by
        rw [mul_assoc, mul_comm (x i₀), ← mul_assoc, ← pow_add,
          Nat.add_comm, Nat.sub_add_cancel hmn.le]
      _ = ζ ^ m * x i₀ := hphase.symm
      _ = (ζ ^ m * x i₀) * 1 := (mul_one _).symm
  have hζfactorial : ζ ^ (Fintype.card α).factorial = 1 := by
    rcases lt_or_gt_of_ne habval with hablt | hbalt
    · have hroot := hrepeat hablt horbit
      have hdpos : 0 < b.1 - a.1 := Nat.sub_pos_of_lt hablt
      have hdle : b.1 - a.1 ≤ Fintype.card α :=
        (Nat.sub_le _ _).trans (Nat.lt_succ_iff.mp b.2)
      obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdle
      rw [hc, pow_mul, hroot, one_pow]
    · have hroot := hrepeat hbalt horbit.symm
      have hdpos : 0 < a.1 - b.1 := Nat.sub_pos_of_lt hbalt
      have hdle : a.1 - b.1 ≤ Fintype.card α :=
        (Nat.sub_le _ _).trans (Nat.lt_succ_iff.mp a.2)
      obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdle
      rw [hc, pow_mul, hroot, one_pow]
  have hdiv :
      z ^ (Fintype.card α).factorial /
          (eigenvalue : ℂ) ^ (Fintype.card α).factorial = 1 := by
    simpa [ζ, div_pow] using hζfactorial
  exact (div_eq_one_iff_eq (pow_ne_zero _ heigenvalue_ne)).mp hdiv

/-- Arithmetic weak-Perron input: an expanding spectral radius witnessed by
a strictly positive eigenvector of a finite nonnegative integral matrix has
a positive power which is a Perron number. -/
theorem dominant_natMatrix_eigenvalue_has_perron_power
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (M : Matrix α α ℕ) (v : α → ℝ) (eigenvalue : ℝ)
    (hv : ∀ i, 0 < v i) (hvalue : 1 < eigenvalue)
    (heigen : NatMatrixEigenvectorEquation M v eigenvalue)
    (hdom : IsDominantEigenvalue M eigenvalue) :
    ∃ u : ℕ, 0 < u ∧ IsPerronNumber (eigenvalue ^ u) := by
  let u := (Fintype.card α).factorial
  have hu : 0 < u := Nat.factorial_pos _
  have hdomPower := dominantEigenvalue_pow M eigenvalue hdom hu
  refine ⟨u, hu, ?_⟩
  refine ⟨one_lt_pow₀ hvalue hu.ne', ?_, ?_⟩
  · exact natMatrix_real_eigenvalue_isIntegral
      (M ^ u) (eigenvalue ^ u) hdomPower.1
  · intro z hzconj hzne
    have hzeigen : IsComplexEigenvalue (M ^ u) z :=
      natMatrix_conjugate_isComplexEigenvalue (M ^ u) hdomPower.1 hzconj
    have hzle : ‖z‖ ≤ eigenvalue ^ u := hdomPower.2 z hzeigen
    apply lt_of_le_of_ne hzle
    intro hzeq
    rcases (isComplexEigenvalue_pow_iff M hu z).mp hzeigen with
      ⟨w, hw, hwpow⟩
    have hpoweq : ‖w‖ ^ u = eigenvalue ^ u := by
      calc
        ‖w‖ ^ u = ‖w ^ u‖ := (norm_pow w u).symm
        _ = ‖z‖ := congrArg norm hwpow
        _ = eigenvalue ^ u := hzeq
    have hwnorm : ‖w‖ = eigenvalue :=
      (pow_left_strictMonoOn₀ hu.ne').injOn (norm_nonneg w)
        (le_trans (by norm_num) hvalue.le) hpoweq
    have hwcollapse := peripheral_eigenvalue_factorial_power_eq
      M v eigenvalue hv (lt_trans (by norm_num) hvalue) heigen hw hwnorm
    have hwcollapse' : w ^ u = (eigenvalue ^ u : ℂ) := by
      simpa [u] using hwcollapse
    have hcast : (eigenvalue : ℂ) ^ u = ((eigenvalue ^ u : ℝ) : ℂ) := by
      norm_cast
    exact hzne (hwpow.symm.trans (hwcollapse'.trans hcast))

/--
Weak Perron--Frobenius input: a strictly positive eigenvector at a real
eigenvalue bigger than one identifies the spectral radius, and a positive
power of that eigenvalue is a Perron number.  The powered matrix statement is
included because it is what Durand's theorem consumes.
-/
theorem weak_perron_eigenvalue_has_perron_power
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (M : Matrix α α ℕ) (v : α → ℝ) (eigenvalue : ℝ)
    (hv : ∀ i, 0 < v i) (hvalue : 1 < eigenvalue)
    (heigen : NatMatrixEigenvectorEquation M v eigenvalue) :
    IsDominantEigenvalue M eigenvalue ∧
      ∃ u : ℕ, 0 < u ∧ IsPerronNumber (eigenvalue ^ u) ∧
        IsDominantEigenvalue (M ^ u) (eigenvalue ^ u) := by
  have hdom := positive_eigenvector_isDominant M v eigenvalue hv heigen
  refine ⟨hdom, ?_⟩
  rcases dominant_natMatrix_eigenvalue_has_perron_power
    M v eigenvalue hv hvalue heigen hdom with ⟨u, hu, hperron⟩
  exact ⟨u, hu, hperron, dominantEigenvalue_pow M eigenvalue hdom hu⟩

/-- Transposition preserves the complex spectrum and hence the dominant
eigenvalue. -/
theorem dominantEigenvalue_transpose_iff
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

namespace Symbolic.Substitution

variable {α : Type*}

/-- Power of a substitution under concatenating composition. -/
def power (σ : Symbolic.Substitution α) : ℕ → Symbolic.Substitution α
  | 0 => Symbolic.Substitution.id
  | n + 1 => σ.comp (power σ n)

@[simp] theorem power_zero (σ : Symbolic.Substitution α) :
    σ.power 0 = Symbolic.Substitution.id := rfl

@[simp] theorem power_succ (σ : Symbolic.Substitution α) (n : ℕ) :
    σ.power (n + 1) = σ.comp (σ.power n) := rfl

@[simp] theorem power_apply (σ : Symbolic.Substitution α) (n : ℕ) (a : α) :
    σ.power n a = σ.iterateLetter n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change σ.mapWord (σ.power n a) = σ.mapWord (σ.iterateLetter n a)
      rw [ih]

/-- Exact metric scaling passes to every substitution power. -/
theorem scalesLetterLengths_power
    {length : α → ℝ} {scale : ℝ}
    (σ : Symbolic.Substitution α)
    (hscale : SubstitutionScalesLetterLengths σ length scale)
    (powerIndex : ℕ) :
    SubstitutionScalesLetterLengths (σ.power powerIndex) length
      (scale ^ powerIndex) := by
  intro source
  rw [power_apply]
  exact wordMetricLength_iterateLetter_of_scales hscale source powerIndex

private theorem mapWord_id (w : Symbolic.Word α) :
    Symbolic.Substitution.id.mapWord w = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

private theorem mapWord_comp (σ τ : Symbolic.Substitution α)
    (w : Symbolic.Word α) :
    (σ.comp τ).mapWord w = σ.mapWord (τ.mapWord w) := by
  induction w with
  | nil => rfl
  | cons a w ih => simp [ih]

private theorem power_mapWord (σ : Symbolic.Substitution α)
    (n : ℕ) (w : Symbolic.Word α) :
    (σ.power n).mapWord w = σ.iterateWord n w := by
  induction n with
  | zero => exact mapWord_id w
  | succ n ih =>
      rw [power_succ, mapWord_comp, ih]
      rfl

private theorem iterateWord_add (σ : Symbolic.Substitution α)
    (m n : ℕ) (w : Symbolic.Word α) :
    σ.iterateWord (m + n) w =
      σ.iterateWord m (σ.iterateWord n w) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simpa only [Nat.succ_add, Symbolic.Substitution.iterateWord_succ]
        using congrArg σ.mapWord ih

private theorem iterateWord_power (σ : Symbolic.Substitution α)
    (n k : ℕ) (w : Symbolic.Word α) :
    (σ.power n).iterateWord k w = σ.iterateWord (n * k) w := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        (σ.power n).iterateWord (k + 1) w =
            (σ.power n).mapWord ((σ.power n).iterateWord k w) := rfl
        _ = σ.iterateWord n ((σ.power n).iterateWord k w) :=
          power_mapWord σ n _
        _ = σ.iterateWord n (σ.iterateWord (n * k) w) :=
          congrArg (σ.iterateWord n) ih
        _ = σ.iterateWord (n + n * k) w :=
          (iterateWord_add σ n (n * k) w).symm
        _ = σ.iterateWord (n * (k + 1)) w := by
          rw [Nat.mul_succ, Nat.add_comm]

private theorem iterateLetter_power (σ : Symbolic.Substitution α)
    (n k : ℕ) (a : α) :
    (σ.power n).iterateLetter k a = σ.iterateLetter (n * k) a := by
  exact iterateWord_power σ n k [a]

private theorem iterateLetter_prefix_of_le
    {σ : Symbolic.Substitution α} {seed : α}
    (hprolong : σ.ProlongableOn seed) {m n : ℕ} (hmn : m ≤ n) :
    σ.iterateLetter m seed <+: σ.iterateLetter n seed := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction k with
  | zero => simpa using List.prefix_refl (σ.iterateLetter m seed)
  | succ k ih =>
      simpa [Nat.add_assoc] using
        ih.trans (σ.iterateLetter_prefix_succ hprolong (m + k))

private theorem count_mapWord_eq_sum [Fintype α] [DecidableEq α]
    (σ : Symbolic.Substitution α) (w : Symbolic.Word α) (a : α) :
    (σ.mapWord w).count a = ∑ b : α, (σ b).count a * w.count b := by
  induction w with
  | nil => simp
  | cons c w ih =>
      rw [Symbolic.Substitution.mapWord_cons, List.count_append, ih]
      calc
        (σ c).count a + ∑ b : α, (σ b).count a * w.count b =
            (∑ b : α, if b = c then (σ b).count a else 0) +
              ∑ b : α, (σ b).count a * w.count b := by simp
        _ = ∑ b : α,
              ((if b = c then (σ b).count a else 0) +
                (σ b).count a * w.count b) :=
          Finset.sum_add_distrib.symm
        _ = ∑ b : α, (σ b).count a * (c :: w).count b := by
          apply Finset.sum_congr rfl
          intro b _
          by_cases hbc : b = c
          · subst b
            simp [Nat.mul_add, Nat.add_comm]
          · simp [hbc, Ne.symm hbc]

private theorem incidenceMatrix_comp [Fintype α] [DecidableEq α]
    (σ τ : Symbolic.Substitution α) :
    (σ.comp τ).incidenceMatrix = σ.incidenceMatrix * τ.incidenceMatrix := by
  ext output source
  simp [Matrix.mul_apply, count_mapWord_eq_sum]

/-- Incidence matrices turn substitution powers into matrix powers. -/
theorem incidenceMatrix_power [Fintype α] [DecidableEq α]
    (σ : Symbolic.Substitution α) (n : ℕ) :
    (σ.power n).incidenceMatrix = σ.incidenceMatrix ^ n := by
  induction n with
  | zero =>
      ext output source
      by_cases h : output = source
      · subst source
        simp [Symbolic.Substitution.incidenceMatrix]
      · simp [Symbolic.Substitution.incidenceMatrix, h, Ne.symm h]
  | succ n ih =>
      rw [power_succ, incidenceMatrix_comp, ih, pow_succ']

/-- A positive power preserves a prolongable generating letter. -/
theorem prolongableOn_power {σ : Symbolic.Substitution α} {seed : α}
    (hprolong : σ.ProlongableOn seed) {n : ℕ} (hn : 0 < n) :
    (σ.power n).ProlongableOn seed := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨initialTail, hinitialTail, hseedImage⟩ := hprolong
  have hprefix : ∀ j : ℕ,
      σ.iterateLetter 1 seed <+: σ.iterateLetter (j + 1) seed := by
    intro j
    induction j with
    | zero => exact List.prefix_refl _
    | succ j ih =>
        exact ih.trans (σ.iterateLetter_prefix_succ
          ⟨initialTail, hinitialTail, hseedImage⟩ (j + 1))
  rcases hprefix k with ⟨laterTail, hlaterTail⟩
  refine ⟨initialTail ++ laterTail,
    List.append_ne_nil_of_left_ne_nil hinitialTail laterTail, ?_⟩
  rw [power_apply]
  change σ.iterateLetter (k + 1) seed = _
  rw [← hlaterTail]
  change σ.mapWord [seed] ++ laterTail = seed :: (initialTail ++ laterTail)
  simp [hseedImage]

/-- A positive power fixes every fixed infinite word. -/
theorem isFixedPoint_power {σ : Symbolic.Substitution α}
    {x : Symbolic.InfiniteWord α} (hfixed : σ.IsFixedPoint x)
    {n : ℕ} (hn : 0 < n) :
    (σ.power n).IsFixedPoint x := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hprevious : (σ.power n).IsFixedPoint x := by
        cases n with
        | zero => exact Symbolic.Substitution.mapInfinite_id x
        | succ n => exact ih (Nat.succ_pos n)
      change (σ.comp (σ.power n)).mapInfinite x = x
      rw [Symbolic.Substitution.mapInfinite_comp]
      change (σ.power n).mapInfinite x = x at hprevious
      change σ.mapInfinite x = x at hfixed
      rw [hprevious, hfixed]

/-- On a prolongable fixed word in which every letter occurs, passing to a
positive power does not lose the generating-letter property. -/
theorem generatingLetter_power_of_occurring_fixed_word
    {σ : Symbolic.Substitution α} {seed : α}
    {x : Symbolic.InfiniteWord α}
    (hprolong : σ.ProlongableOn seed)
    (hfixed : σ.IsFixedPoint x)
    (hgenerate : σ.IsGeneratingLetter seed)
    (hoccurs : ∀ a : α,
      Symbolic.Substitution.OccursInInfiniteWord a x)
    {n : ℕ} (hn : 0 < n) :
    (σ.power n).IsGeneratingLetter seed := by
  intro a
  obtain ⟨k, hk⟩ := hgenerate a
  refine ⟨k, ?_⟩
  rw [iterateLetter_power]
  rcases iterateLetter_prefix_of_le hprolong
      (by nlinarith : k ≤ n * k) with ⟨tail, htail⟩
  rw [← htail]
  exact List.mem_append_left tail hk

/-- Unbounded prefix growth survives passage to a positive substitution
power when the prefixes are nested by prolongability. -/
theorem letterImagesGrow_power
    {σ : Symbolic.Substitution α} {seed : α}
    (hprolong : σ.ProlongableOn seed)
    (hgrow : LetterImagesGrow σ seed)
    {n : ℕ} (hn : 0 < n) :
    LetterImagesGrow (σ.power n) seed := by
  intro N
  obtain ⟨k, hk⟩ := hgrow N
  refine ⟨k, ?_⟩
  rw [iterateLetter_power]
  exact hk.trans (iterateLetter_prefix_of_le hprolong
    (by nlinarith : k ≤ n * k)).length_le

end Symbolic.Substitution

/-- Positive powers of a multiplicatively independent pair remain
multiplicatively independent. -/
theorem multiplicativelyIndependent_powers
    {a b : ℝ} (hind : MultiplicativelyIndependent a b)
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    MultiplicativelyIndependent (a ^ u) (b ^ v) := by
  intro m n hm hn heq
  apply hind (u * m) (v * n) (Nat.mul_pos hu hm) (Nat.mul_pos hv hn)
  simpa [pow_mul] using heq

/-- The powered presentations extracted from the two positive geometric
length eigenvectors. -/
theorem common_ray_has_perron_powered_presentations
    {A B : IntervalMap} {K : Finset I} {ψ : ℝ → I} {a b : ℝ}
    (data : CommonRayFixedWord A B K ψ a b)
    (hind : MultiplicativelyIndependent a b) :
    ∃ u v : ℕ, 0 < u ∧ 0 < v ∧
      IsPerronNumber (a ^ u) ∧ IsPerronNumber (b ^ v) ∧
      MultiplicativelyIndependent (a ^ u) (b ^ v) ∧
      IsDominantEigenvalue
        (data.substitutionA.power u).incidenceMatrix (a ^ u) ∧
      IsDominantEigenvalue
        (data.substitutionB.power v).incidenceMatrix (b ^ v) ∧
      (data.substitutionA.power u).ProlongableOn data.seed ∧
      (data.substitutionB.power v).ProlongableOn data.seed ∧
      (data.substitutionA.power u).IsGeneratingLetter data.seed ∧
      (data.substitutionB.power v).IsGeneratingLetter data.seed ∧
      (data.substitutionA.power u).IsFixedPoint data.word ∧
      (data.substitutionB.power v).IsFixedPoint data.word ∧
      LetterImagesGrow (data.substitutionA.power u) data.seed ∧
      LetterImagesGrow (data.substitutionB.power v) data.seed := by
  letI : Nonempty data.alphabet := data.alphabet_nonempty.to_subtype
  have heigenA : NatMatrixEigenvectorEquation
      data.substitutionA.incidenceMatrix.transpose data.letterLength a := by
    intro source
    simpa [NatMatrixEigenvectorEquation, incidenceTransposeMul] using
      data.lengthEigenA.2 source
  have heigenB : NatMatrixEigenvectorEquation
      data.substitutionB.incidenceMatrix.transpose data.letterLength b := by
    intro source
    simpa [NatMatrixEigenvectorEquation, incidenceTransposeMul] using
      data.lengthEigenB.2 source
  rcases weak_perron_eigenvalue_has_perron_power
      data.substitutionA.incidenceMatrix.transpose data.letterLength a
      data.letterLength_pos data.one_lt_a heigenA with
    ⟨_hdominantA, u, hu, hperronA, hdominantAPowerTranspose⟩
  rcases weak_perron_eigenvalue_has_perron_power
      data.substitutionB.incidenceMatrix.transpose data.letterLength b
      data.letterLength_pos data.one_lt_b heigenB with
    ⟨_hdominantB, v, hv, hperronB, hdominantBPowerTranspose⟩
  have hdominantAPower : IsDominantEigenvalue
      (data.substitutionA.power u).incidenceMatrix (a ^ u) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    apply (dominantEigenvalue_transpose_iff
      (data.substitutionA.incidenceMatrix ^ u) (a ^ u)).mp
    simpa using hdominantAPowerTranspose
  have hdominantBPower : IsDominantEigenvalue
      (data.substitutionB.power v).incidenceMatrix (b ^ v) := by
    rw [Symbolic.Substitution.incidenceMatrix_power]
    apply (dominantEigenvalue_transpose_iff
      (data.substitutionB.incidenceMatrix ^ v) (b ^ v)).mp
    simpa using hdominantBPowerTranspose
  exact ⟨u, v, hu, hv, hperronA, hperronB,
    multiplicativelyIndependent_powers hind hu hv,
    hdominantAPower, hdominantBPower,
    Symbolic.Substitution.prolongableOn_power data.prolongableA hu,
    Symbolic.Substitution.prolongableOn_power data.prolongableB hv,
    Symbolic.Substitution.generatingLetter_power_of_occurring_fixed_word
      data.prolongableA data.fixedA data.generatingA data.every_letter_occurs hu,
    Symbolic.Substitution.generatingLetter_power_of_occurring_fixed_word
      data.prolongableB data.fixedB data.generatingB data.every_letter_occurs hv,
    Symbolic.Substitution.isFixedPoint_power data.fixedA hu,
    Symbolic.Substitution.isFixedPoint_power data.fixedB hv,
    Symbolic.Substitution.letterImagesGrow_power
      data.prolongableA data.growthA hu,
    Symbolic.Substitution.letterImagesGrow_power
      data.prolongableB data.growthB hv⟩

/-! ## Durand--Cobham and the common-word application -/

/-!
The hypotheses below do not imply that either source substitution is
primitive.  For example, `a ↦ ab, b ↦ bb`, prolongable on `a`, generates the
fixed word `a b b b ...`; both letters occur and all seed images grow, but
`b` cannot reach `a`.  Consequently the general proof has to separate the
finite reachability/SCC reduction from the primitive return-word argument.
-/

namespace Symbolic

universe u

/-- A finite word occurs at the indicated position of an infinite word. -/
def InfiniteFactorAt {delta : Type u} (x : InfiniteWord delta)
    (w : Word delta) (start : Nat) : Prop :=
  (x.drop start).take w.length = w

/-- A finite word is a factor of an infinite word. -/
def IsInfiniteFactor {delta : Type u} (x : InfiniteWord delta)
    (w : Word delta) : Prop :=
  ∃ start : Nat, InfiniteFactorAt x w start

/-- Every finite infix of a factor of an infinite word is again a factor. -/
theorem IsInfiniteFactor.of_infix
    {delta : Type u} {x : InfiniteWord delta} {u w : Word delta}
    (hw : IsInfiniteFactor x w) (hu : u <:+: w) :
    IsInfiniteFactor x u := by
  rcases hw with ⟨start, hw⟩
  rcases hu with ⟨left, right, rfl⟩
  let tail := x.drop start
  have hprefix :
      tail.take (left.length + u.length) = left ++ u := by
    calc
      tail.take (left.length + u.length) =
          (tail.take (left ++ u ++ right).length).take
            (left.length + u.length) := by
        simp [Stream'.take_take]
      _ = (left ++ u ++ right).take (left.length + u.length) := by
        rw [hw]
      _ = left ++ u := by simp [← List.append_assoc]
  have hleft : tail.take left.length = left := by
    calc
      tail.take left.length =
          (tail.take (left.length + u.length)).take left.length := by
        simp [Stream'.take_take]
      _ = (left ++ u).take left.length := by rw [hprefix]
      _ = left := by simp
  have hsplit := Stream'.take_add
    (a := tail) (m := left.length) (n := u.length)
  rw [hprefix, hleft] at hsplit
  have htail : (tail.drop left.length).take u.length = u :=
    List.append_cancel_left hsplit.symm
  refine ⟨start + left.length, ?_⟩
  simpa [InfiniteFactorAt, tail, Stream'.drop_drop] using htail

/-- A finite word occurs at arbitrarily late positions. -/
def IsRecurrentFactor {delta : Type u} (x : InfiniteWord delta)
    (w : Word delta) : Prop :=
  ∀ cutoff : Nat, ∃ start : Nat, cutoff ≤ start ∧ InfiniteFactorAt x w start

/-- A letter occurs at arbitrarily late positions. -/
def OccursInfinitelyOften {delta : Type u} (x : InfiniteWord delta)
    (a : delta) : Prop :=
  ∀ cutoff : Nat, ∃ start : Nat, cutoff ≤ start ∧ x start = a

/-- Failure of infinite occurrence is exactly eventual absence. -/
theorem not_occursInfinitelyOften_iff_eventually_absent
    {delta : Type u} {x : InfiniteWord delta} {a : delta} :
    ¬ OccursInfinitelyOften x a ↔
      ∃ cutoff : Nat, ∀ start : Nat, cutoff ≤ start → x start ≠ a := by
  classical
  simp only [OccursInfinitelyOften]
  push_neg
  rfl

/-- A nonrecurrent finite factor has a last possible starting position. -/
theorem not_isRecurrentFactor_iff_eventually_absent
    {delta : Type u} {x : InfiniteWord delta} {w : Word delta} :
    ¬ IsRecurrentFactor x w ↔
      ∃ cutoff : Nat, ∀ start : Nat, cutoff ≤ start →
        ¬ InfiniteFactorAt x w start := by
  classical
  simp only [IsRecurrentFactor]
  push_neg
  rfl

/-- For each fixed factor length, all factors starting sufficiently late are
recurrent.  Finiteness of the alphabet is essential here. -/
theorem eventually_every_fixedLengthFactor_recurrent
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    (x : InfiniteWord delta) (factorLength : Nat) :
    ∃ cutoff : Nat, ∀ start : Nat, cutoff ≤ start →
      IsRecurrentFactor x ((x.drop start).take factorLength) := by
  classical
  have hchoice : ∀ w : Word delta, ∃ cutoff : Nat,
      IsRecurrentFactor x w ∨
        ∀ start : Nat, cutoff ≤ start → ¬ InfiniteFactorAt x w start := by
    intro w
    by_cases hw : IsRecurrentFactor x w
    · exact ⟨0, Or.inl hw⟩
    · obtain ⟨cutoff, hcutoff⟩ :=
        not_isRecurrentFactor_iff_eventually_absent.mp hw
      exact ⟨cutoff, Or.inr hcutoff⟩
  choose bound hbound using hchoice
  let words : Finset (Word delta) :=
    (List.finite_length_eq delta factorLength).toFinset
  let cutoff := words.sup bound
  refine ⟨cutoff, ?_⟩
  intro start hstart
  let w := (x.drop start).take factorLength
  have hwLength : w.length = factorLength := by simp [w]
  have hwMem : w ∈ words := by
    simp [words, hwLength]
  by_contra hnot
  have hboundLe : bound w ≤ cutoff :=
    Finset.le_sup (f := bound) hwMem
  have habsent := (hbound w).resolve_left hnot
  apply habsent start (hboundLe.trans hstart)
  simp [InfiniteFactorAt, w]

/-- Over a finite alphabet all letters outside the recurrent alphabet are
confined to one common finite prefix. -/
theorem eventually_every_letter_occursInfinitelyOften
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    (x : InfiniteWord delta) :
    ∃ cutoff : Nat, ∀ start : Nat, cutoff ≤ start →
      OccursInfinitelyOften x (x start) := by
  classical
  have hchoice : ∀ a : delta, ∃ cutoff : Nat,
      OccursInfinitelyOften x a ∨
        ∀ start : Nat, cutoff ≤ start → x start ≠ a := by
    intro a
    by_cases ha : OccursInfinitelyOften x a
    · exact ⟨0, Or.inl ha⟩
    · obtain ⟨cutoff, hcutoff⟩ :=
        not_occursInfinitelyOften_iff_eventually_absent.mp ha
      exact ⟨cutoff, Or.inr hcutoff⟩
  choose bound hbound using hchoice
  let cutoff := Finset.univ.sup bound
  refine ⟨cutoff, ?_⟩
  intro start hstart
  by_contra hnot
  have hle : bound (x start) ≤ cutoff := by
    exact Finset.le_sup (f := bound) (Finset.mem_univ (x start))
  have habsent := (hbound (x start)).resolve_left hnot
  exact habsent start (hle.trans hstart) rfl

/-- Every interval of a fixed length contains a starting position of `w`. -/
def AppearsWithBoundedGaps {delta : Type u} (x : InfiniteWord delta)
    (w : Word delta) : Prop :=
  ∃ gap : Nat, 0 < gap ∧
    ∀ start : Nat, ∃ offset : Nat, offset ≤ gap ∧
      InfiniteFactorAt x w (start + offset)

/-- The syndeticity conclusion used in the nonprimitive Durand reduction. -/
def RecurrentFactorsSyndetic {delta : Type u} (x : InfiniteWord delta) : Prop :=
  ∀ w : Word delta, IsRecurrentFactor x w → AppearsWithBoundedGaps x w

/-- An occurrence lying in an eventually periodic tail repeats after every
natural multiple of the period. -/
theorem InfiniteFactorAt.add_mul_period
    {delta : Type u} {x : InfiniteWord delta} {w : Word delta}
    {tail period base : Nat}
    (hperiod : ∀ n : Nat, tail ≤ n → x (n + period) = x n)
    (hbase : tail ≤ base) (hfactor : InfiniteFactorAt x w base)
    (multiplier : Nat) :
    InfiniteFactorAt x w (base + multiplier * period) := by
  have hshift : ∀ k n : Nat, tail ≤ n →
      x (n + k * period) = x n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        intro n hn
        calc
          x (n + (k + 1) * period) =
              x ((n + k * period) + period) := by
            simp [Nat.add_mul, Nat.add_assoc]
          _ = x (n + k * period) :=
            hperiod (n + k * period) (hn.trans (Nat.le_add_right _ _))
          _ = x n := ih n hn
  unfold InfiniteFactorAt at hfactor ⊢
  calc
    (x.drop (base + multiplier * period)).take w.length =
        (x.drop base).take w.length := by
      apply List.ext_getElem
      · simp
      · intro index hleft hright
        rw [Stream'.take_get (m := index) (n := w.length)
            (a := x.drop (base + multiplier * period)) hleft,
          Stream'.take_get (m := index) (n := w.length)
            (a := x.drop base) hright]
        simpa [Stream'.get_drop, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using
            hshift multiplier (base + index) (by omega)
    _ = w := hfactor

/-- Every recurrent factor of an ultimately periodic word has bounded gaps. -/
theorem IsUltimatelyPeriodic.recurrentFactorsSyndetic
    {delta : Type u} {x : InfiniteWord delta}
    (hultimatelyPeriodic : IsUltimatelyPeriodic x) :
    RecurrentFactorsSyndetic x := by
  rcases hultimatelyPeriodic with
    ⟨tail, period, hperiodPos, hperiod⟩
  intro word hword
  obtain ⟨base, hbase, hfactor⟩ := hword tail
  refine ⟨base + period, by omega, ?_⟩
  intro start
  have hexists : ∃ multiplier : Nat,
      start ≤ base + multiplier * period := by
    refine ⟨start, ?_⟩
    exact (Nat.le_mul_of_pos_right start hperiodPos).trans
      (Nat.le_add_left _ _)
  let multiplier := Nat.find hexists
  have hmultiplier : start ≤ base + multiplier * period := by
    simpa only [multiplier] using Nat.find_spec hexists
  let position := base + multiplier * period
  refine ⟨position - start, ?_, ?_⟩
  · by_cases hzero : multiplier = 0
    · dsimp only [position]
      rw [hzero]
      simp only [zero_mul, add_zero]
      omega
    · let previous := multiplier - 1
      have hmultiplierEq : multiplier = previous + 1 := by
        dsimp only [previous]
        omega
      have hpreviousLt : previous < multiplier := by omega
      have hpreviousFind : previous < Nat.find hexists := by
        simpa only [multiplier] using hpreviousLt
      have hnotPrevious := Nat.find_min hexists hpreviousFind
      have hpreviousStart : base + previous * period < start :=
        Nat.lt_of_not_ge hnotPrevious
      dsimp only [position]
      rw [hmultiplierEq, Nat.add_mul, one_mul]
      omega
  · have hrepeated := hfactor.add_mul_period hperiod hbase multiplier
    simpa only [position, Nat.add_sub_of_le hmultiplier] using hrepeated

theorem AppearsWithBoundedGaps.isRecurrentFactor
    {delta : Type u} {x : InfiniteWord delta} {w : Word delta}
    (hbounded : AppearsWithBoundedGaps x w) :
    IsRecurrentFactor x w := by
  rcases hbounded with ⟨gap, _hgap, hbounded⟩
  intro cutoff
  rcases hbounded cutoff with ⟨offset, hoffset, hfactor⟩
  exact ⟨cutoff + offset, Nat.le_add_right cutoff offset, hfactor⟩

/-- Factoring after a dropped prefix just translates the occurrence index. -/
theorem infiniteFactorAt_drop_iff
    {delta : Type u} (x : InfiniteWord delta) (w : Word delta)
    (cutoff start : Nat) :
    InfiniteFactorAt (x.drop cutoff) w start ↔
      InfiniteFactorAt x w (cutoff + start) := by
  simp only [InfiniteFactorAt, Stream'.drop_drop]

/-- Deleting a finite prefix does not change which factors are recurrent. -/
theorem isRecurrentFactor_drop_iff
    {delta : Type u} (x : InfiniteWord delta) (w : Word delta)
    (cutoff : Nat) :
    IsRecurrentFactor (x.drop cutoff) w ↔ IsRecurrentFactor x w := by
  constructor
  · intro htail threshold
    rcases htail threshold with ⟨start, hstart, hfactor⟩
    refine ⟨cutoff + start, by omega, ?_⟩
    exact (infiniteFactorAt_drop_iff x w cutoff start).mp hfactor
  · intro hwhole threshold
    rcases hwhole (cutoff + threshold) with
      ⟨start, hstart, hfactor⟩
    have hcutoff : cutoff ≤ start := by omega
    refine ⟨start - cutoff, by omega, ?_⟩
    rw [infiniteFactorAt_drop_iff]
    convert hfactor using 1 <;> omega

/-- Bounded gaps are likewise invariant under deletion of a finite prefix. -/
theorem appearsWithBoundedGaps_drop_iff
    {delta : Type u} (x : InfiniteWord delta) (w : Word delta)
    (cutoff : Nat) :
    AppearsWithBoundedGaps (x.drop cutoff) w ↔
      AppearsWithBoundedGaps x w := by
  constructor
  · rintro ⟨gap, hgap, hbounded⟩
    refine ⟨cutoff + gap, by omega, ?_⟩
    intro start
    by_cases hcutoff : cutoff ≤ start
    · rcases hbounded (start - cutoff) with
        ⟨offset, hoffset, hfactor⟩
      refine ⟨offset, by omega, ?_⟩
      have htranslated :=
        (infiniteFactorAt_drop_iff x w cutoff
          ((start - cutoff) + offset)).mp hfactor
      convert htranslated using 1 <;> omega
    · rcases hbounded 0 with ⟨offset, hoffset, hfactor⟩
      refine ⟨(cutoff - start) + offset, by omega, ?_⟩
      have htranslated :=
        (infiniteFactorAt_drop_iff x w cutoff (0 + offset)).mp hfactor
      convert htranslated using 1 <;> omega
  · rintro ⟨gap, hgap, hbounded⟩
    refine ⟨gap, hgap, ?_⟩
    intro start
    rcases hbounded (cutoff + start) with
      ⟨offset, hoffset, hfactor⟩
    refine ⟨offset, hoffset, ?_⟩
    rw [infiniteFactorAt_drop_iff]
    convert hfactor using 1 <;> omega

/-- Syndeticity of the recurrent language is a finite-tail invariant. -/
theorem recurrentFactorsSyndetic_drop_iff
    {delta : Type u} (x : InfiniteWord delta) (cutoff : Nat) :
    RecurrentFactorsSyndetic (x.drop cutoff) ↔
      RecurrentFactorsSyndetic x := by
  constructor
  · intro htail w hrecurrent
    apply (appearsWithBoundedGaps_drop_iff x w cutoff).mp
    apply htail w
    exact (isRecurrentFactor_drop_iff x w cutoff).mpr hrecurrent
  · intro hwhole w hrecurrent
    apply (appearsWithBoundedGaps_drop_iff x w cutoff).mpr
    apply hwhole w
    exact (isRecurrentFactor_drop_iff x w cutoff).mp hrecurrent

/-- Occurrence of one finite word at a specified position in another. -/
def FiniteFactorAt {delta : Type u} (ambient factor : Word delta)
    (start : Nat) : Prop :=
  start + factor.length ≤ ambient.length ∧
    (ambient.drop start).take factor.length = factor

/-- A finite factor nested in a finite block occurrence gives the translated
occurrence in the ambient infinite word. -/
theorem InfiniteFactorAt.of_finiteFactorAt
    {delta : Type u} {x : InfiniteWord delta}
    {ambient factor : Word delta} {start offset : Nat}
    (hambient : InfiniteFactorAt x ambient start)
    (hfactor : FiniteFactorAt ambient factor offset) :
    InfiniteFactorAt x factor (start + offset) := by
  rcases hfactor with ⟨hfactorWithin, hfactorEq⟩
  have hoffsetLe : offset ≤ ambient.length := by omega
  have hfactorLeDrop : factor.length ≤ (ambient.drop offset).length := by
    simp only [List.length_drop]
    omega
  have hstream :
      ambient ++ₛ (x.drop start).drop ambient.length = x.drop start := by
    calc
      ambient ++ₛ (x.drop start).drop ambient.length =
          (x.drop start).take ambient.length ++ₛ
            (x.drop start).drop ambient.length := by rw [hambient]
      _ = x.drop start :=
        Stream'.append_take_drop ambient.length (x.drop start)
  have hdropped := congrArg (fun stream : InfiniteWord delta =>
    stream.drop offset) hstream
  change Stream'.drop offset
      (ambient ++ₛ (x.drop start).drop ambient.length) =
    Stream'.drop offset (x.drop start) at hdropped
  rw [Stream'.drop_append_of_le_length
    (x := ambient)
    (a := (x.drop start).drop ambient.length)
    (n := offset) hoffsetLe] at hdropped
  have htaken := congrArg (fun stream : InfiniteWord delta =>
    stream.take factor.length) hdropped
  change Stream'.take factor.length
      (ambient.drop offset ++ₛ
        (x.drop start).drop ambient.length) =
    Stream'.take factor.length ((x.drop start).drop offset) at htaken
  have hleft :
      ((ambient.drop offset) ++ₛ
          (x.drop start).drop ambient.length).take factor.length =
        (ambient.drop offset).take factor.length := by
    exact Stream'.take_append_of_le_length
      (x := ambient.drop offset)
      (a := (x.drop start).drop ambient.length)
      (n := factor.length) hfactorLeDrop
  rw [hleft, hfactorEq] at htaken
  rw [InfiniteFactorAt, ← Stream'.drop_drop]
  exact htaken.symm

/-- A factor occurrence nested inside a longer occurrence induces the
corresponding finite-word factor occurrence. -/
theorem finiteFactorAt_of_nested_infiniteFactorAt
    {delta : Type u} {x : InfiniteWord delta}
    {ambient factor : Word delta} {start offset : Nat}
    (hambient : InfiniteFactorAt x ambient start)
    (hfactor : InfiniteFactorAt x factor (start + offset))
    (hwithin : offset + factor.length ≤ ambient.length) :
    FiniteFactorAt ambient factor offset := by
  refine ⟨hwithin, ?_⟩
  have htrunc :
      (x.drop start).take (offset + factor.length) =
        ambient.take (offset + factor.length) := by
    calc
      (x.drop start).take (offset + factor.length) =
          ((x.drop start).take ambient.length).take
            (offset + factor.length) := by
        simp [Stream'.take_take, hwithin]
      _ = ambient.take (offset + factor.length) := by rw [hambient]
  have hleft :
      (x.drop start).take offset = ambient.take offset := by
    calc
      (x.drop start).take offset =
          ((x.drop start).take (offset + factor.length)).take offset := by
        simp [Stream'.take_take]
      _ = (ambient.take (offset + factor.length)).take offset := by
        rw [htrunc]
      _ = ambient.take offset := by simp [List.take_take]
  rw [Stream'.take_add, List.take_add, hleft] at htrunc
  have htail :
      ((x.drop start).drop offset).take factor.length =
        (ambient.drop offset).take factor.length := by
    exact List.append_cancel_left htrunc
  have htranslated :
      ((x.drop start).drop offset).take factor.length = factor := by
    simpa [InfiniteFactorAt, Stream'.drop_drop] using hfactor
  exact htail.symm.trans htranslated

/-- A factor at a valid finite starting index is a list infix. -/
theorem FiniteFactorAt.isInfix
    {delta : Type u} {ambient factor : Word delta} {start : Nat}
    (hfactor : FiniteFactorAt ambient factor start) :
    factor <:+: ambient := by
  refine ⟨ambient.take start, ambient.drop (start + factor.length), ?_⟩
  calc
    ambient.take start ++ factor ++ ambient.drop (start + factor.length) =
        ambient.take start ++
          ((ambient.drop start).take factor.length ++
            (ambient.drop start).drop factor.length) := by
      rw [hfactor.2, List.drop_drop]
      simp [List.append_assoc]
    _ = ambient.take start ++ ambient.drop start := by
      rw [List.take_append_drop]
    _ = ambient := List.take_append_drop _ _

/-- A finite occurrence lying wholly inside a prefix restricts to that
prefix. -/
theorem FiniteFactorAt.of_prefix
    {delta : Type u} {large small factor : Word delta} {start : Nat}
    (hfactor : FiniteFactorAt large factor start)
    (hprefix : small <+: large)
    (hwithin : start + factor.length ≤ small.length) :
    FiniteFactorAt small factor start := by
  rcases hprefix with ⟨suffix, rfl⟩
  rcases hfactor with ⟨_hlarge, hword⟩
  have hstart : start ≤ small.length := by omega
  have hremaining : factor.length ≤ (small.drop start).length := by
    simp only [List.length_drop]
    omega
  rw [List.drop_append_of_le_length hstart,
    List.take_append_of_le_length hremaining] at hword
  exact ⟨hwithin, hword⟩

/-- A prefix of a continuation occurs at the boundary following the left
word. -/
theorem finiteFactorAt_append_length_of_prefix
    {delta : Type u} {left tail factor : Word delta}
    (hprefix : factor <+: tail) :
    FiniteFactorAt (left ++ tail) factor left.length := by
  refine ⟨?_, ?_⟩
  · simpa using Nat.add_le_add_left hprefix.length_le left.length
  · simpa using (List.prefix_iff_eq_take.mp hprefix).symm

/-- A return word from one occurrence of `u` to the next. -/
def IsReturnWord {delta : Type u} (x : InfiniteWord delta)
    (u r : Word delta) : Prop :=
  u ≠ [] ∧ r ≠ [] ∧ IsInfiniteFactor x (r ++ u) ∧
    u <+: r ++ u ∧
    ∀ start : Nat, FiniteFactorAt (r ++ u) u start ↔
      start = 0 ∨ start = r.length

/-- Concatenating return blocks and then the marker still begins with the
marker, including when consecutive occurrences overlap. -/
theorem marker_prefix_flatMap_returnWords
    {delta index : Type*} {x : InfiniteWord delta}
    {marker : Word delta} (blocks : index → Word delta)
    (hreturns : ∀ a : index, IsReturnWord x marker (blocks a)) :
    ∀ letters : Word index,
      marker <+: letters.flatMap blocks ++ marker := by
  intro letters
  induction letters with
  | nil => simp
  | cons a rest ih =>
      have hlift : blocks a ++ marker <+:
          blocks a ++ (rest.flatMap blocks ++ marker) :=
        (List.prefix_append_right_inj (blocks a)).mpr ih
      exact (hreturns a).2.2.2.1.trans (by
        simpa [List.append_assoc] using hlift)

/-- Two return blocks followed by marker-prefixed continuations have the same
length whenever the resulting words agree.  The proof recognizes each block
endpoint as the first positive marker occurrence. -/
theorem returnWord_length_eq_of_append_eq
    {delta : Type u} {x : InfiniteWord delta}
    {marker first second firstTail secondTail : Word delta}
    (hfirst : IsReturnWord x marker first)
    (hsecond : IsReturnWord x marker second)
    (hfirstTail : marker <+: firstTail)
    (hsecondTail : marker <+: secondTail)
    (heq : first ++ firstTail = second ++ secondTail) :
    first.length = second.length := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmarkerLarge :
        FiniteFactorAt (second ++ secondTail) marker first.length := by
      rw [← heq]
      exact finiteFactorAt_append_length_of_prefix hfirstTail
    have hsmallPrefix : second ++ marker <+: second ++ secondTail :=
      (List.prefix_append_right_inj second).mpr hsecondTail
    have hwithin : first.length + marker.length ≤
        (second ++ marker).length := by
      simp only [List.length_append]
      omega
    have hmarkerSmall := hmarkerLarge.of_prefix hsmallPrefix hwithin
    rcases (hsecond.2.2.2.2 first.length).mp hmarkerSmall with
      hzero | hend
    · exact hfirst.2.1 (List.eq_nil_of_length_eq_zero hzero)
    · omega
  · have hmarkerLarge :
        FiniteFactorAt (first ++ firstTail) marker second.length := by
      rw [heq]
      exact finiteFactorAt_append_length_of_prefix hsecondTail
    have hsmallPrefix : first ++ marker <+: first ++ firstTail :=
      (List.prefix_append_right_inj first).mpr hfirstTail
    have hwithin : second.length + marker.length ≤
        (first ++ marker).length := by
      simp only [List.length_append]
      omega
    have hmarkerSmall := hmarkerLarge.of_prefix hsmallPrefix hwithin
    rcases (hfirst.2.2.2.2 second.length).mp hmarkerSmall with
      hzero | hend
    · exact hsecond.2.1 (List.eq_nil_of_length_eq_zero hzero)
    · omega

/-- Return words to one marker form a code: an injective enumeration of
return blocks extends to an injective finite-word decoding. -/
theorem flatMap_returnWords_injective
    {delta index : Type*} {x : InfiniteWord delta}
    {marker : Word delta} {blocks : index → Word delta}
    (hblocks : Function.Injective blocks)
    (hreturns : ∀ a : index, IsReturnWord x marker (blocks a)) :
    Function.Injective (fun letters : Word index => letters.flatMap blocks) := by
  intro left
  induction left with
  | nil =>
      intro right heq
      cases right with
      | nil => rfl
      | cons b rest =>
          exfalso
          have hnonempty := (hreturns b).2.1
          simp only [List.flatMap_nil, List.flatMap_cons] at heq
          exact hnonempty (List.append_eq_nil_iff.mp heq.symm).1
  | cons a rest ih =>
      intro right heq
      cases right with
      | nil =>
          exfalso
          have hnonempty := (hreturns a).2.1
          simp only [List.flatMap_nil, List.flatMap_cons] at heq
          exact hnonempty (List.append_eq_nil_iff.mp heq).1
      | cons b tail =>
          simp only [List.flatMap_cons] at heq
          have hrestPrefix :=
            marker_prefix_flatMap_returnWords blocks hreturns rest
          have htailPrefix :=
            marker_prefix_flatMap_returnWords blocks hreturns tail
          have heqMarker :
              blocks a ++ (rest.flatMap blocks ++ marker) =
                blocks b ++ (tail.flatMap blocks ++ marker) := by
            simpa [List.append_assoc] using
              congrArg (fun word => word ++ marker) heq
          have hlength : (blocks a).length = (blocks b).length :=
            returnWord_length_eq_of_append_eq
              (hreturns a) (hreturns b) hrestPrefix htailPrefix heqMarker
          have hblockEq : blocks a = blocks b := by
            calc
              blocks a = (blocks a ++ rest.flatMap blocks).take
                  (blocks a).length := by simp
              _ = (blocks b ++ tail.flatMap blocks).take
                  (blocks a).length := by rw [heq]
              _ = blocks b := by rw [hlength]; simp
          have hab : a = b := hblocks hblockEq
          subst b
          have htailEq : rest.flatMap blocks = tail.flatMap blocks :=
            List.append_cancel_left heq
          exact congrArg (a :: ·) (ih htailEq)

/-- The block between two consecutive occurrences is a return word. -/
theorem returnWord_between_consecutive_occurrences
    {delta : Type u} {x : InfiniteWord delta} {u : Word delta}
    {first second : Nat}
    (hu : u ≠ []) (hfirst : InfiniteFactorAt x u first)
    (hsecond : InfiniteFactorAt x u second) (hlt : first < second)
    (hconsecutive : ∀ position : Nat,
      first < position → position < second →
        ¬ InfiniteFactorAt x u position) :
    IsReturnWord x u ((x.drop first).take (second - first)) := by
  let returnWord := (x.drop first).take (second - first)
  have hreturnLength : returnWord.length = second - first := by
    simp [returnWord]
  have hreturnNonempty : returnWord ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hreturnLength]
    omega
  have hdrop :
      (x.drop first).drop (second - first) = x.drop second := by
    rw [Stream'.drop_drop]
    congr 1
    omega
  have hblockAt :
      (x.drop first).take (returnWord ++ u).length =
        returnWord ++ u := by
    rw [List.length_append, hreturnLength, Stream'.take_add]
    rw [hdrop, hsecond]
  have hblockFactor : IsInfiniteFactor x (returnWord ++ u) :=
    ⟨first, hblockAt⟩
  have hoverlap : u <+: returnWord ++ u := by
    have hlength : u.length ≤ (returnWord ++ u).length := by simp
    have hprefix := Stream'.take_prefix_take_left
      (a := x.drop first) (m := u.length)
      (n := (returnWord ++ u).length) hlength
    rw [hfirst, hblockAt] at hprefix
    exact hprefix
  refine ⟨hu, hreturnNonempty, hblockFactor, hoverlap, ?_⟩
  intro start
  constructor
  · intro hfinite
    have hstartLe : start ≤ returnWord.length := by
      have hlength :
          start + u.length ≤ returnWord.length + u.length := by
        simpa only [List.length_append] using hfinite.1
      exact Nat.le_of_add_le_add_right hlength
    by_cases hzero : start = 0
    · exact Or.inl hzero
    by_cases hend : start = returnWord.length
    · exact Or.inr hend
    exfalso
    have hwithin : start + u.length ≤ (returnWord ++ u).length :=
      hfinite.1
    have hlocalPrefix :
        (x.drop first).take (start + u.length) =
          (returnWord ++ u).take (start + u.length) := by
      calc
        (x.drop first).take (start + u.length) =
            ((x.drop first).take (returnWord ++ u).length).take
              (start + u.length) := by
          simp [Stream'.take_take, hstartLe]
        _ = (returnWord ++ u).take (start + u.length) := by
          rw [hblockAt]
    have hlocalLeft :
        (x.drop first).take start = (returnWord ++ u).take start := by
      calc
        (x.drop first).take start =
            ((x.drop first).take (start + u.length)).take start := by
          simp [Stream'.take_take]
        _ = ((returnWord ++ u).take (start + u.length)).take start := by
          rw [hlocalPrefix]
        _ = (returnWord ++ u).take start := by
          simp [List.take_take]
    rw [Stream'.take_add, List.take_add, hlocalLeft] at hlocalPrefix
    have htailEq :
        ((x.drop first).drop start).take u.length =
          ((returnWord ++ u).drop start).take u.length :=
      List.append_cancel_left hlocalPrefix
    have htranslated : InfiniteFactorAt x u (first + start) := by
      rw [InfiniteFactorAt, ← Stream'.drop_drop]
      exact htailEq.trans hfinite.2
    apply hconsecutive (first + start) (by omega) (by
      rw [hreturnLength] at hstartLe hend
      omega)
    exact htranslated
  · rintro (rfl | rfl)
    · constructor
      · simpa using hoverlap.length_le
      · simpa using (List.prefix_iff_eq_take.mp hoverlap).symm
    · simp [FiniteFactorAt]

/-- Uniform recurrence, expressed by a bounded-gap condition on every factor. -/
def IsUniformlyRecurrent {delta : Type u} (x : InfiniteWord delta) : Prop :=
  ∀ w : Word delta, IsInfiniteFactor x w → AppearsWithBoundedGaps x w

/-- Linear recurrence with an explicit natural recurrence constant. -/
def IsLinearlyRecurrent {delta : Type u} (x : InfiniteWord delta)
    (constant : Nat) : Prop :=
  0 < constant ∧ IsUniformlyRecurrent x ∧
    ∀ u r : Word delta, IsReturnWord x u r →
      r.length ≤ constant * u.length

/-- A convenient quantitative form of linear recurrence: every nonempty
factor can be found within a distance proportional to its length from any
starting position. -/
def HasLinearFactorGaps {delta : Type u} (x : InfiniteWord delta)
    (constant : Nat) : Prop :=
  0 < constant ∧
    ∀ w : Word delta, w ≠ [] → IsInfiniteFactor x w →
      ∀ start : Nat, ∃ position : Nat,
        start ≤ position ∧
          position ≤ start + constant * w.length ∧
          InfiniteFactorAt x w position

/-- A pointwise coding carries factor occurrences at the same positions. -/
theorem LetterCoding.infiniteFactorAt_mapInfinite
    {source target : Type*} (coding : LetterCoding source target)
    {x : InfiniteWord source} {word : Word source} {start : Nat}
    (hfactor : InfiniteFactorAt x word start) :
    InfiniteFactorAt (coding.mapInfinite x) (coding.mapWord word) start := by
  have hmapped := congrArg (List.map coding) hfactor
  simpa [InfiniteFactorAt, LetterCoding.mapInfinite,
    LetterCoding.mapWord, Stream'.map_take] using hmapped

/-- Linear factor-gap bounds are preserved by a letter-to-letter coding. -/
theorem LetterCoding.hasLinearFactorGaps
    {source target : Type*}
    (coding : LetterCoding source target)
    {sourceWord : InfiniteWord source} {constant : Nat}
    (hlinear : HasLinearFactorGaps sourceWord constant) :
    HasLinearFactorGaps (coding.mapInfinite sourceWord) constant := by
  refine ⟨hlinear.1, ?_⟩
  intro word hword hfactor start
  rcases hfactor with ⟨origin, horigin⟩
  let lift : Word source :=
    (sourceWord.drop origin).take word.length
  have hliftLength : lift.length = word.length := by
    simp [lift]
  have hliftNonempty : lift ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hliftLength]
    exact List.length_pos_of_ne_nil hword
  have hliftAt : InfiniteFactorAt sourceWord lift origin := by
    simp [InfiniteFactorAt, lift]
  have hliftCoding : coding.mapWord lift = word := by
    have hmapped :
        coding.mapWord
            ((sourceWord.drop origin).take word.length) =
          (coding.mapInfinite sourceWord |>.drop origin).take word.length := by
      change ((sourceWord.drop origin).take word.length).map coding =
        ((Stream'.map coding sourceWord).drop origin).take word.length
      rw [Stream'.drop_map]
      exact Stream'.map_take
        (a := sourceWord.drop origin) (n := word.length) coding
    exact hmapped.trans horigin
  rcases hlinear.2 lift hliftNonempty ⟨origin, hliftAt⟩ start with
    ⟨position, hstart, hbound, hposition⟩
  refine ⟨position, hstart, ?_, ?_⟩
  · simpa [hliftLength] using hbound
  · simpa [hliftCoding] using
      (coding.infiniteFactorAt_mapInfinite hposition)

/-- A linear factor-gap estimate implies the return-word formulation of
linear recurrence, with one extra unit in the constant to pass the occurrence
already sitting at the left endpoint. -/
theorem isLinearlyRecurrent_of_hasLinearFactorGaps
    {delta : Type*} {x : InfiniteWord delta} {constant : Nat}
    (hlinear : HasLinearFactorGaps x constant) :
    IsLinearlyRecurrent x (constant + 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro word hfactor
    by_cases hword : word = []
    · subst word
      refine ⟨1, by omega, ?_⟩
      intro start
      exact ⟨0, by omega, by simp [InfiniteFactorAt]⟩
    · refine ⟨constant * word.length, Nat.mul_pos hlinear.1
          (List.length_pos_of_ne_nil hword), ?_⟩
      intro start
      rcases hlinear.2 word hword hfactor start with
        ⟨position, hstart, hbound, hposition⟩
      refine ⟨position - start, by omega, ?_⟩
      convert hposition using 1 <;> omega
  · intro marker returnWord hreturn
    by_contra hbound
    have hlarge :
        constant * marker.length + marker.length < returnWord.length := by
      simpa [Nat.add_mul] using hbound
    rcases hreturn.2.2.1 with ⟨origin, horigin⟩
    have hmarkerFactor : IsInfiniteFactor x marker :=
      (show IsInfiniteFactor x (returnWord ++ marker) from
        ⟨origin, horigin⟩).of_infix hreturn.2.2.2.1.isInfix
    rcases hlinear.2 marker hreturn.1 hmarkerFactor (origin + 1) with
      ⟨position, hpositionLower, hpositionUpper, hposition⟩
    have hmarkerLength : 0 < marker.length :=
      List.length_pos_of_ne_nil hreturn.1
    have horiginLe : origin ≤ position := by omega
    have hwithin :
        (position - origin) + marker.length ≤
          (returnWord ++ marker).length := by
      simp only [List.length_append]
      omega
    have hfinite : FiniteFactorAt (returnWord ++ marker) marker
        (position - origin) := by
      apply finiteFactorAt_of_nested_infiniteFactorAt horigin
      · convert hposition using 1 <;> omega
      · exact hwithin
    rcases (hreturn.2.2.2.2 (position - origin)).mp hfinite with
      hzero | hend
    · omega
    · omega

/-- Once a nonempty factor has appeared, linear recurrence bounds the wait
from any later position to its next occurrence.  The proof chooses the
first occurrence after `start` and the last one before it, so it is valid
for one-sided words without assuming a left-infinite extension. -/
theorem IsLinearlyRecurrent.nextOccurrence
    {delta : Type u} {x : InfiniteWord delta} {constant : Nat}
    (hlinear : IsLinearlyRecurrent x constant)
    {u : Word delta} (hu : u ≠ [])
    {prior start : Nat} (hpriorLe : prior ≤ start)
    (hprior : InfiniteFactorAt x u prior) :
    ∃ position : Nat, start ≤ position ∧
      position ≤ start + constant * u.length ∧
      InfiniteFactorAt x u position := by
  classical
  by_cases hatStart : InfiniteFactorAt x u start
  · exact ⟨start, le_rfl, Nat.le_add_right _ _, hatStart⟩
  have huFactor : IsInfiniteFactor x u := ⟨prior, hprior⟩
  obtain ⟨gap, _hgap, hbounded⟩ := hlinear.2.1 u huFactor
  rcases hbounded start with ⟨offset, _hoffset, hoffsetFactor⟩
  have hexists : ∃ position : Nat,
      start ≤ position ∧ InfiniteFactorAt x u position :=
    ⟨start + offset, Nat.le_add_right _ _, hoffsetFactor⟩
  let next := Nat.find hexists
  have hnextSpec :
      start ≤ next ∧ InfiniteFactorAt x u next :=
    Nat.find_spec hexists
  have hstartLtNext : start < next := by
    rcases hnextSpec.1.eq_or_lt with hEq | hLt
    · exact False.elim (hatStart (hEq ▸ hnextSpec.2))
    · exact hLt
  let earlier : Finset Nat :=
    (Finset.range next).filter (InfiniteFactorAt x u)
  have hpriorMem : prior ∈ earlier := by
    simp only [earlier, Finset.mem_filter, Finset.mem_range]
    exact ⟨hpriorLe.trans_lt hstartLtNext, hprior⟩
  have hearlierNonempty : earlier.Nonempty := ⟨prior, hpriorMem⟩
  let previous := earlier.max' hearlierNonempty
  have hpreviousMem : previous ∈ earlier :=
    earlier.max'_mem hearlierNonempty
  have hpreviousLt : previous < next := by
    exact Finset.mem_range.mp (Finset.mem_filter.mp hpreviousMem).1
  have hpreviousFactor : InfiniteFactorAt x u previous :=
    (Finset.mem_filter.mp hpreviousMem).2
  have hconsecutive : ∀ position : Nat,
      previous < position → position < next →
        ¬ InfiniteFactorAt x u position := by
    intro position hpreviousPosition hpositionNext hpositionFactor
    have hpositionMem : position ∈ earlier := by
      simp only [earlier, Finset.mem_filter, Finset.mem_range]
      exact ⟨hpositionNext, hpositionFactor⟩
    have := earlier.le_max' position hpositionMem
    omega
  have hreturn := returnWord_between_consecutive_occurrences
    hu hpreviousFactor hnextSpec.2 hpreviousLt hconsecutive
  have hreturnBound := hlinear.2.2 u
    ((x.drop previous).take (next - previous)) hreturn
  have hreturnLength :
      ((x.drop previous).take (next - previous)).length =
        next - previous := by simp
  rw [hreturnLength] at hreturnBound
  have hpreviousLeStart : previous ≤ start := by
    by_contra hnot
    have hstartPrevious : start ≤ previous := by omega
    have hpredicate :
        start ≤ previous ∧ InfiniteFactorAt x u previous :=
      ⟨hstartPrevious, hpreviousFactor⟩
    have hminimal := Nat.find_min' hexists hpredicate
    change next ≤ previous at hminimal
    omega
  refine ⟨next, hnextSpec.1, ?_, hnextSpec.2⟩
  omega

/-- The `n`-fold concatenation of a finite word. -/
def wordPower {delta : Type u} (u : Word delta) (n : Nat) : Word delta :=
  (List.replicate n u).flatten

@[simp] theorem wordPower_length {delta : Type u} (u : Word delta) (n : Nat) :
    (wordPower u n).length = n * u.length := by
  simp [wordPower]

theorem wordPower_add {delta : Type u} (u : Word delta) (m n : Nat) :
    wordPower u (m + n) = wordPower u m ++ wordPower u n := by
  unfold wordPower
  rw [List.replicate_add, List.flatten_append]

theorem wordPower_wordPower {delta : Type u} (u : Word delta)
    (m n : Nat) :
    wordPower (wordPower u m) n = wordPower u (n * m) := by
  induction n with
  | zero => simp [wordPower]
  | succ n ih =>
      calc
        wordPower (wordPower u m) (n + 1) =
            wordPower (wordPower u m) n ++ wordPower u m := by
          simpa [wordPower] using
            wordPower_add (wordPower u m) n 1
        _ = wordPower u (n * m) ++ wordPower u m := by rw [ih]
        _ = wordPower u (n * m + m) :=
          (wordPower_add u (n * m) m).symm
        _ = wordPower u ((n + 1) * m) := by rw [Nat.add_mul, one_mul]

theorem wordPower_prefix_of_le {delta : Type u} {u : Word delta}
    {m n : Nat} (hmn : m ≤ n) :
    wordPower u m <+: wordPower u n := by
  rw [← Nat.add_sub_of_le hmn, wordPower_add]
  exact List.prefix_append _ _

/-- A word is `exponent`-power-free when no nonempty factor base occurs to
that power. -/
def IsPowerFree {delta : Type u} (x : InfiniteWord delta)
    (exponent : Nat) : Prop :=
  ∀ base : Word delta, base ≠ [] →
    ¬ IsInfiniteFactor x (wordPower base exponent)

/-- Iterating a self-overlap prefixes the same word by any finite power of
the return block. -/
theorem prefix_wordPower_append_of_prefix
    {delta : Type u} {u r : Word delta}
    (hoverlap : u <+: r ++ u) (n : Nat) :
    u <+: wordPower r n ++ u := by
  induction n with
  | zero => simp [wordPower]
  | succ n ih =>
      apply hoverlap.trans
      have hprepend : r ++ u <+: r ++ (wordPower r n ++ u) :=
        (List.prefix_append_right_inj r).mpr ih
      simpa [wordPower, List.replicate_succ, List.append_assoc] using hprepend

/-- If `u` overlaps its copy after `r`, every power of `r` which is no
longer than `u` is a prefix of `u`. -/
theorem wordPower_prefix_of_overlap
    {delta : Type u} {u r : Word delta} {n : Nat}
    (hoverlap : u <+: r ++ u)
    (hlength : n * r.length ≤ u.length) :
    wordPower r n <+: u := by
  rcases prefix_wordPower_append_of_prefix hoverlap n with
    ⟨suffix, hsuffix⟩
  have hpowerLength : (wordPower r n).length ≤ u.length := by
    simpa using hlength
  apply (List.isPrefix_append_of_length hpowerLength).mp
  rw [hsuffix]
  exact List.prefix_append _ _

/-- A return block shorter than `1 / n` times its marker forces an
`(n+1)`-st power of that block to occur.  This is the finite-word overlap
part of the return-word lower bound. -/
theorem returnWord_power_of_short
    {delta : Type u} {x : InfiniteWord delta}
    {marker returnWord : Word delta} {n : Nat}
    (hreturn : IsReturnWord x marker returnWord)
    (hlength : n * returnWord.length ≤ marker.length) :
    IsInfiniteFactor x (wordPower returnWord (n + 1)) := by
  rcases hreturn with
    ⟨_hmarker, _hreturn, hfactor, hoverlap, _hconsecutive⟩
  have hpowerPrefix : wordPower returnWord n <+: marker :=
    wordPower_prefix_of_overlap hoverlap hlength
  have hprepend :
      returnWord ++ wordPower returnWord n <+: returnWord ++ marker :=
    (List.prefix_append_right_inj returnWord).mpr hpowerPrefix
  have hfullPrefix :
      wordPower returnWord (n + 1) <+: returnWord ++ marker := by
    simpa [wordPower, List.replicate_succ, List.append_assoc] using hprepend
  exact hfactor.of_infix hfullPrefix.isInfix

/-- Every finite power of a word has the word length as a period. -/
theorem wordPower_hasPeriod {delta : Type u} (u : Word delta) (n : Nat) :
    List.HasPeriod (wordPower u n) u.length := by
  induction n using Nat.twoStepInduction with
  | zero => simp [wordPower]
  | one =>
      apply List.hasPeriod_of_length_le
      simp
  | more n _ ih =>
      have hlength : u.length ≤ (wordPower u (n + 1)).length := by
        rw [wordPower_length]
        nlinarith
      have hperiod := ih.take_append u.length u.length
        (wordPower u (n + 1)) (dvd_refl _) hlength
      simpa [wordPower, List.replicate_succ] using hperiod

/-- A factor whose length is one full block of a nonempty finite power is a
cyclic rotation of that block. -/
theorem factor_wordPower_eq_rotate
    {delta : Type u} {base factor : Word delta} {exponent : Nat}
    (hbase : base ≠ []) (hexponent : 0 < exponent)
    (hfactor : factor <:+: wordPower base exponent)
    (hlength : factor.length = base.length) :
    ∃ shift : Nat, factor = base.rotate shift := by
  rcases hfactor with ⟨left, right, hwhole⟩
  refine ⟨left.length, ?_⟩
  apply List.ext_getElem
  · simpa using hlength
  · intro i hiFactor hiRotate
    have hiBase : i < base.length := by simpa [hlength] using hiFactor
    have hbaseLength : 0 < base.length := List.length_pos_of_ne_nil hbase
    have hindex : left.length + i < (wordPower base exponent).length := by
      rw [← hwhole]
      simp only [List.length_append]
      omega
    have hfactorIndex :
        (wordPower base exponent)[left.length + i]? = factor[i]? := by
      rw [← hwhole, List.append_assoc,
        List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
      exact List.getElem?_append_left hiFactor
    have hmod := (wordPower_hasPeriod base exponent).getElem?_mod
      base.length (left.length + i) (wordPower base exponent) hindex
    have hmodLt :
        (left.length + i) % base.length < base.length :=
      Nat.mod_lt _ hbaseLength
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hexponent)
    have hfirst :
        (wordPower base (predecessor + 1))[
            (left.length + i) % base.length]? =
          base[(left.length + i) % base.length]? := by
      simp [wordPower, List.replicate_succ, List.getElem?_append_left,
        hmodLt]
    have hrotate := List.getElem?_rotate
      (l := base) (n := left.length) hiBase
    rw [← Option.some_inj, ← List.getElem?_eq_getElem,
      ← List.getElem?_eq_getElem]
    calc
      factor[i]? =
          (wordPower base (predecessor + 1))[left.length + i]? :=
        hfactorIndex.symm
      _ = (wordPower base (predecessor + 1))[
          (left.length + i) % base.length]? := hmod.symm
      _ = base[(left.length + i) % base.length]? := hfirst
      _ = base[(i + left.length) % base.length]? := by rw [Nat.add_comm]
      _ = (base.rotate left.length)[i]? := hrotate.symm

/-- If every window of one positive length is a rotation of a fixed block,
the whole one-sided word is periodic with that block length. -/
theorem periodic_of_all_windows_rotate
    {delta : Type u} {x : InfiniteWord delta} {base : Word delta}
    (hbase : base ≠ [])
    (hrotate : ∀ start : Nat, ∃ shift : Nat,
      (x.drop start).take base.length = base.rotate shift) :
    IsPeriodic x := by
  have hperiod : 0 < base.length := List.length_pos_of_ne_nil hbase
  refine ⟨base.length, hperiod, ?_⟩
  intro start
  obtain ⟨predecessor, hlength⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hperiod)
  let middle := (x.drop (start + 1)).take predecessor
  have hfrontSplit :
      (x.drop start).take base.length = x start :: middle := by
    rw [hlength, Stream'.take_succ]
    simp [middle, Stream'.head_drop, Stream'.get]
  have hbackSplit :
      (x.drop (start + 1)).take base.length =
        middle ++ [x (start + base.length)] := by
    rw [hlength, Stream'.take_succ']
    simp only [middle]
    congr 2
    rw [Stream'.get_drop]
    congr 1
    omega
  obtain ⟨frontShift, hfront⟩ := hrotate start
  obtain ⟨backShift, hback⟩ := hrotate (start + 1)
  have hpermutation : List.Perm
      ((x.drop start).take base.length)
      ((x.drop (start + 1)).take base.length) := by
    rw [hfront, hback]
    exact (List.rotate_perm base frontShift).trans
      (List.rotate_perm base backShift).symm
  rw [hfrontSplit, hbackSplit] at hpermutation
  have hcomm : List.Perm
      (middle ++ [x (start + base.length)])
      ([x (start + base.length)] ++ middle) :=
    List.perm_append_comm
  have hcons : List.Perm
      (x start :: middle) (x (start + base.length) :: middle) :=
    hpermutation.trans (by simpa using hcomm)
  have hsingle : List.Perm [x start] [x (start + base.length)] :=
    (List.perm_append_right_iff middle).mp (by simpa using hcons)
  exact (List.singleton_perm_singleton.mp hsingle).symm

/-- An `(K+1)`-st power in a linearly recurrent word forces the whole word
to be periodic.  A late copy of the power contains every window of the base
length, because consecutive occurrences are at most `K * length` apart;
the preceding rotation lemma then gives the period. -/
theorem IsLinearlyRecurrent.periodic_of_powerFactor
    {delta : Type u} {x : InfiniteWord delta} {constant : Nat}
    (hlinear : IsLinearlyRecurrent x constant)
    {base : Word delta} (hbase : base ≠ [])
    (hpower : IsInfiniteFactor x (wordPower base (constant + 1))) :
    IsPeriodic x := by
  apply periodic_of_all_windows_rotate hbase
  intro start
  let window := (x.drop start).take base.length
  have hwindowLength : window.length = base.length := by
    simp [window]
  have hwindowNonempty : window ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hwindowLength]
    exact List.length_pos_of_ne_nil hbase
  have hwindowAt : InfiniteFactorAt x window start := by
    simp [InfiniteFactorAt, window]
  obtain ⟨gap, _hgap, hbounded⟩ := hlinear.2.1
    (wordPower base (constant + 1)) hpower
  rcases hbounded start with
    ⟨blockOffset, _hblockOffset, hblockAt⟩
  let blockStart := start + blockOffset
  have hstartBlock : start ≤ blockStart := Nat.le_add_right _ _
  rcases hlinear.nextOccurrence hwindowNonempty hstartBlock hwindowAt with
    ⟨position, hblockPosition, hpositionBound, hpositionFactor⟩
  let localStart := position - blockStart
  have hpositionEq : blockStart + localStart = position := by
    simp [localStart, Nat.add_sub_of_le hblockPosition]
  have hwithin :
      localStart + window.length ≤
        (wordPower base (constant + 1)).length := by
    have hlocalBound : localStart ≤ constant * window.length := by
      dsimp only [localStart]
      omega
    rw [hwindowLength] at hlocalBound
    rw [wordPower_length, hwindowLength, Nat.add_mul]
    simp only [one_mul]
    omega
  have hpositionFactor' :
      InfiniteFactorAt x window (blockStart + localStart) := by
    rw [hpositionEq]
    exact hpositionFactor
  have hfinite := finiteFactorAt_of_nested_infiniteFactorAt
    hblockAt hpositionFactor' hwithin
  exact factor_wordPower_eq_rotate hbase (Nat.succ_pos _)
    hfinite.isInfix hwindowLength

/-- A nonempty finite word which is not a proper power. -/
def IsPrimitiveFiniteWord {delta : Type u} (u : Word delta) : Prop :=
  u ≠ [] ∧
    ∀ v : Word delta, ∀ n : Nat, 1 < n → wordPower v n ≠ u

/-- Every nonempty finite word is a positive power of a primitive word. -/
theorem exists_primitiveRoot {delta : Type u} (word : Word delta)
    (hword : word ≠ []) :
    ∃ root : Word delta, ∃ exponent : Nat,
      IsPrimitiveFiniteWord root ∧ 0 < exponent ∧
        wordPower root exponent = word := by
  have hstrong : ∀ length : Nat, ∀ candidate : Word delta,
      candidate.length = length → candidate ≠ [] →
        ∃ root : Word delta, ∃ exponent : Nat,
          IsPrimitiveFiniteWord root ∧ 0 < exponent ∧
            wordPower root exponent = candidate := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
      intro word hlength hword
      by_cases hprimitive : IsPrimitiveFiniteWord word
      · exact ⟨word, 1, hprimitive, by omega, by simp [wordPower]⟩
      · have hproper : ¬ ∀ base : Word delta, ∀ exponent : Nat,
            1 < exponent → wordPower base exponent ≠ word := by
          intro h
          exact hprimitive ⟨hword, h⟩
        push_neg at hproper
        obtain ⟨base, exponent, hexponent, hpower⟩ := hproper
        have hbase : base ≠ [] := by
          intro hnil
          subst base
          apply hword
          simpa [wordPower] using hpower.symm
        have hbaseLength : base.length < word.length := by
          have hlength := congrArg List.length hpower
          rw [wordPower_length] at hlength
          have hbasePos := List.length_pos_of_ne_nil hbase
          nlinarith
        have hbaseLength' : base.length < length := by
          simpa [hlength] using hbaseLength
        obtain ⟨root, rootExponent, hrootPrimitive,
            hrootExponent, hrootPower⟩ :=
          ih base.length hbaseLength' base rfl hbase
        refine ⟨root, exponent * rootExponent,
          hrootPrimitive, Nat.mul_pos (by omega) hrootExponent, ?_⟩
        calc
          wordPower root (exponent * rootExponent) =
              wordPower (wordPower root rootExponent) exponent :=
            (wordPower_wordPower root rootExponent exponent).symm
          _ = wordPower base exponent := by rw [hrootPower]
          _ = word := hpower
  exact hstrong word.length word rfl hword

/-- Under syndeticity, every recurrent factor occurs inside a sufficiently
long power from a periodic recurrent-language witness. -/
theorem recurrentFactor_isInfix_wordPower
    {delta : Type u} {x : InfiniteWord delta}
    (hsyndetic : RecurrentFactorsSyndetic x)
    {u w : Word delta}
    (hu : IsPrimitiveFiniteWord u)
    (hpowers : ∀ n : Nat, 0 < n →
      IsRecurrentFactor x (wordPower u n))
    (hw : IsRecurrentFactor x w) :
    ∃ n : Nat, w <:+: wordPower u n := by
  rcases hsyndetic w hw with ⟨gap, hgap, hbounded⟩
  let exponent := gap + w.length + 1
  have hexponent : 0 < exponent := by omega
  have huLength : 0 < u.length := List.length_pos_of_ne_nil hu.1
  have hblockLong : gap + w.length ≤ (wordPower u exponent).length := by
    rw [wordPower_length]
    have : exponent ≤ exponent * u.length := by nlinarith
    omega
  rcases hpowers exponent hexponent 0 with
    ⟨blockStart, _hblockStart, hblock⟩
  rcases hbounded blockStart with ⟨offset, hoffset, hword⟩
  have hwithin : offset + w.length ≤ (wordPower u exponent).length := by
    omega
  have hwordLocal : InfiniteFactorAt (x.drop blockStart) w offset :=
    (infiniteFactorAt_drop_iff x w blockStart offset).mpr (by
      convert hword using 1 <;> omega)
  change ((x.drop blockStart).drop offset).take w.length = w at hwordLocal
  have hsplit := Stream'.take_add
    (a := x.drop blockStart) (m := offset) (n := w.length)
  rw [hwordLocal] at hsplit
  have hprefix := Stream'.take_prefix_take_left
    (a := x.drop blockStart)
    (m := offset + w.length)
    (n := (wordPower u exponent).length) hwithin
  change (x.drop blockStart).take (wordPower u exponent).length =
    wordPower u exponent at hblock
  rw [hsplit, hblock] at hprefix
  rcases hprefix with ⟨suffix, hsuffix⟩
  refine ⟨exponent, (x.drop blockStart).take offset, suffix, ?_⟩
  simpa [List.append_assoc] using hsuffix

/-- A periodic recurrent language is witnessed by all powers of one primitive
word occurring recurrently.  Durand's periodic-language lemma turns this into
ultimate periodicity of the original one-sided word. -/
def HasPeriodicRecurrentLanguage {delta : Type u}
    (x : InfiniteWord delta) : Prop :=
  ∃ u : Word delta, IsPrimitiveFiniteWord u ∧
    ∀ n : Nat, 0 < n → IsRecurrentFactor x (wordPower u n)

/-- A periodic word contains every positive power of a primitive period
word. -/
theorem IsPeriodic.hasPrimitivePowerFactors
    {delta : Type u} {x : InfiniteWord delta}
    (hperiodic : IsPeriodic x) :
    ∃ root : Word delta, IsPrimitiveFiniteWord root ∧
      ∀ n : Nat, 0 < n → IsInfiniteFactor x (wordPower root n) := by
  rcases hperiodic with ⟨period, hperiodPos, hperiod⟩
  let block := x.take period
  have hblockNonempty : block ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [block, hperiodPos]
  obtain ⟨root, exponent, hrootPrimitive, hexponent, hrootPower⟩ :=
    exists_primitiveRoot block hblockNonempty
  have hshift : ∀ multiplier index : Nat,
      x (index + multiplier * period) = x index := by
    intro multiplier
    induction multiplier with
    | zero => simp
    | succ multiplier ih =>
        intro index
        calc
          x (index + (multiplier + 1) * period) =
              x ((index + multiplier * period) + period) := by
            simp [Nat.add_mul, Nat.add_assoc]
          _ = x (index + multiplier * period) := hperiod _
          _ = x index := ih index
  have hdropBlock : ∀ multiplier : Nat,
      (x.drop (multiplier * period)).take period = block := by
    intro multiplier
    apply List.ext_getElem
    · simp [block]
    · intro index hleft hright
      rw [Stream'.take_get (m := index) (n := period)
          (a := x.drop (multiplier * period)) hleft,
        Stream'.take_get (m := index) (n := period) (a := x) hright]
      simpa [Stream'.get_drop, Nat.add_comm] using
        hshift multiplier index
  have htakeBlocks : ∀ multiplier : Nat,
      x.take (multiplier * period) = wordPower block multiplier := by
    intro multiplier
    induction multiplier with
    | zero => simp [wordPower]
    | succ multiplier ih =>
        have hsplit := Stream'.take_add
          (a := x) (m := multiplier * period) (n := period)
        rw [ih, hdropBlock multiplier] at hsplit
        calc
          x.take ((multiplier + 1) * period) =
              x.take (multiplier * period + period) := by
            rw [Nat.add_mul, one_mul]
          _ = wordPower block multiplier ++ block := hsplit
          _ = wordPower block (multiplier + 1) := by
            simpa [wordPower] using
              (wordPower_add block multiplier 1).symm
  refine ⟨root, hrootPrimitive, ?_⟩
  intro n _hn
  have hblockFactor : IsInfiniteFactor x (wordPower block n) := by
    refine ⟨0, ?_⟩
    change x.take (wordPower block n).length = wordPower block n
    simpa [block] using htakeBlocks n
  have hrootPrefix : wordPower root n <+: wordPower block n := by
    have hle : n ≤ n * exponent :=
      Nat.le_mul_of_pos_right n hexponent
    rw [← hrootPower, wordPower_wordPower]
    exact wordPower_prefix_of_le hle
  exact hblockFactor.of_infix hrootPrefix.isInfix

/-- A uniformly recurrent word whose language is exactly the recurrent
language of a possibly nonrecurrent substitutive word. -/
structure RecurrentCore {delta : Type u} (x : InfiniteWord delta) where
  word : InfiniteWord delta
  same_language : ∀ w : Word delta,
    IsInfiniteFactor word w ↔ IsRecurrentFactor x w

/-- If every factor of `y` is recurrent in `x`, and the recurrent language of
`x` is syndetic, then `y` already has exactly that recurrent language.  A
bounded-gap occurrence of a recurrent word is forced into one sufficiently
long factor of `y`. -/
theorem infiniteFactors_eq_recurrentFactors_of_subset
    {delta : Type u} {x y : InfiniteWord delta}
    (hsyndetic : RecurrentFactorsSyndetic x)
    (hsubset : ∀ w : Word delta,
      IsInfiniteFactor y w → IsRecurrentFactor x w) :
    ∀ w : Word delta,
      IsInfiniteFactor y w ↔ IsRecurrentFactor x w := by
  intro word
  constructor
  · exact hsubset word
  · intro hrecurrent
    obtain ⟨gap, _hgapPos, hgap⟩ := hsyndetic word hrecurrent
    let ambient := y.take (gap + word.length)
    have hambientFactor : IsInfiniteFactor y ambient := by
      refine ⟨0, ?_⟩
      simp [InfiniteFactorAt, ambient]
    have hambientRecurrent := hsubset ambient hambientFactor
    obtain ⟨start, _hstart, hambientAt⟩ := hambientRecurrent 0
    obtain ⟨offset, hoffset, hwordAt⟩ := hgap start
    have hambientLength : ambient.length = gap + word.length := by
      simp [ambient]
    have hfinite : FiniteFactorAt ambient word offset :=
      finiteFactorAt_of_nested_infiniteFactorAt hambientAt hwordAt (by
        rw [hambientLength]
        omega)
    exact hambientFactor.of_infix hfinite.isInfix

/-- Periodicity of a recurrent core makes the recurrent language of the
original word periodic. -/
theorem RecurrentCore.hasPeriodicRecurrentLanguage
    {delta : Type u} {x : InfiniteWord delta}
    (core : RecurrentCore x) (hperiodic : IsPeriodic core.word) :
    HasPeriodicRecurrentLanguage x := by
  obtain ⟨root, hrootPrimitive, hpowers⟩ :=
    hperiodic.hasPrimitivePowerFactors
  exact ⟨root, hrootPrimitive, fun n hn =>
    (core.same_language (wordPower root n)).mp (hpowers n hn)⟩

/-- The particular recurrent core extracted from a good component, together
with its primitive powered substitution presentation.  Keeping this data is
essential: an arbitrary point with the same minimal language need not itself
be a substitution fixed point. -/
structure PrimitiveRecurrentCore {delta : Type u}
    (growth : Real) (x : InfiniteWord delta) where
  core : RecurrentCore x
  growth_gt_one : 1 < growth
  rank : Nat
  rank_pos : 0 < rank
  substitution : Substitution (Fin rank)
  seed : Fin rank
  fixedWord : InfiniteWord (Fin rank)
  coding : LetterCoding (Fin rank) delta
  coding_injective : Function.Injective coding
  exponent : Nat
  exponent_pos : 0 < exponent
  primitive : ∃ iterate : Nat, 0 < iterate ∧
    ∀ a b : Fin rank, b ∈ substitution.iterateLetter iterate a
  prolongable : substitution.ProlongableOn seed
  generating : substitution.IsGeneratingLetter seed
  fixed : substitution.IsFixedPoint fixedWord
  every_letter_occurs : ∀ a : Fin rank,
    Substitution.OccursInInfiniteWord a fixedWord
  metric : Fin rank → Real
  metric_pos : ∀ a : Fin rank, 0 < metric a
  metric_scales : SubstitutionScalesLetterLengths substitution metric
    (growth ^ exponent)
  images_grow : LetterImagesGrow substitution seed
  dominant : IsDominantEigenvalue substitution.incidenceMatrix
    (growth ^ exponent)
  coding_eq : coding.mapInfinite fixedWord = core.word

/-- A concrete coding of a word by its successive return words. -/
structure ReturnDecomposition {delta : Type u}
    (x : InfiniteWord delta) (marker : Word delta) (rank : Nat) where
  rank_pos : 0 < rank
  marker_ne_nil : marker ≠ []
  marker_at_zero : InfiniteFactorAt x marker 0
  blocks : Fin rank → Word delta
  blocks_injective : Function.Injective blocks
  blocks_are_returns : ∀ a : Fin rank, IsReturnWord x marker (blocks a)
  derived : InfiniteWord (Fin rank)
  cut : Nat → Nat
  cut_zero : cut 0 = 0
  cut_succ : ∀ n : Nat,
    cut (n + 1) = cut n + (blocks (derived n)).length
  block_at_cut : ∀ n : Nat,
    InfiniteFactorAt x (blocks (derived n)) (cut n)

/-- Injective pointwise coding reflects finite factor occurrences. -/
theorem finiteFactorAt_map_iff
    {alpha beta : Type*} {coding : alpha → beta}
    (hcoding : Function.Injective coding)
    {ambient factor : Word alpha} {start : Nat} :
    FiniteFactorAt (ambient.map coding) (factor.map coding) start ↔
      FiniteFactorAt ambient factor start := by
  constructor
  · rintro ⟨hlength, heq⟩
    refine ⟨by simpa using hlength, ?_⟩
    apply (List.map_injective_iff.mpr hcoding)
    simpa using heq
  · rintro ⟨hlength, heq⟩
    refine ⟨by simpa using hlength, ?_⟩
    simpa using congrArg (List.map coding) heq

/-- An injective letter coding preserves the exact return-word condition. -/
theorem IsReturnWord.map_injective
    {alpha beta : Type*} (coding : LetterCoding alpha beta)
    (hcoding : Function.Injective coding)
    {x : InfiniteWord alpha} {marker block : Word alpha}
    (hreturn : IsReturnWord x marker block) :
    IsReturnWord (coding.mapInfinite x)
      (coding.mapWord marker) (coding.mapWord block) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnil
    apply hreturn.1
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa [LetterCoding.mapWord] using this
  · intro hnil
    apply hreturn.2.1
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa [LetterCoding.mapWord] using this
  · obtain ⟨start, hstart⟩ := hreturn.2.2.1
    refine ⟨start, ?_⟩
    simpa [LetterCoding.mapWord, List.map_append] using
      coding.infiniteFactorAt_mapInfinite hstart
  · rcases hreturn.2.2.2.1 with ⟨tail, htail⟩
    refine ⟨tail.map coding, ?_⟩
    simpa [LetterCoding.mapWord, List.map_append] using
      congrArg (List.map coding) htail
  · intro start
    simpa [LetterCoding.mapWord, List.map_append] using
      (finiteFactorAt_map_iff (coding := coding) hcoding
        (ambient := block ++ marker) (factor := marker) (start := start)).trans
          (hreturn.2.2.2.2 start)

/-- Transport a complete return decomposition through an injective
letter-to-letter coding. -/
def ReturnDecomposition.map_injective
    {alpha beta : Type*} (coding : LetterCoding alpha beta)
    (hcoding : Function.Injective coding)
    {x : InfiniteWord alpha} {marker : Word alpha} {rank : Nat}
    (decomposition : ReturnDecomposition x marker rank) :
    ReturnDecomposition (coding.mapInfinite x) (coding.mapWord marker) rank where
  rank_pos := decomposition.rank_pos
  marker_ne_nil := by
    intro hnil
    apply decomposition.marker_ne_nil
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa [LetterCoding.mapWord] using this
  marker_at_zero :=
    coding.infiniteFactorAt_mapInfinite decomposition.marker_at_zero
  blocks := fun a => coding.mapWord (decomposition.blocks a)
  blocks_injective := by
    intro a b hab
    apply decomposition.blocks_injective
    apply (List.map_injective_iff.mpr hcoding)
    exact hab
  blocks_are_returns := fun a =>
    (decomposition.blocks_are_returns a).map_injective coding hcoding
  derived := decomposition.derived
  cut := decomposition.cut
  cut_zero := decomposition.cut_zero
  cut_succ := by
    intro n
    simpa [LetterCoding.mapWord] using decomposition.cut_succ n
  block_at_cut := fun n =>
    coding.infiniteFactorAt_mapInfinite (decomposition.block_at_cut n)

theorem ReturnDecomposition.block_length_pos
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (a : Fin rank) : 0 < (decomposition.blocks a).length :=
  List.length_pos_of_ne_nil (decomposition.blocks_are_returns a).2.1

theorem ReturnDecomposition.cut_lt_succ
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (n : Nat) : decomposition.cut n < decomposition.cut (n + 1) := by
  rw [decomposition.cut_succ]
  exact Nat.lt_add_of_pos_right
    (decomposition.block_length_pos (decomposition.derived n))

theorem ReturnDecomposition.cut_strictMono
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank) :
    StrictMono decomposition.cut :=
  strictMono_nat_of_lt_succ decomposition.cut_lt_succ

theorem ReturnDecomposition.cut_injective
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank) :
    Function.Injective decomposition.cut :=
  decomposition.cut_strictMono.injective

theorem ReturnDecomposition.le_cut
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank) :
    ∀ n : Nat, n ≤ decomposition.cut n := by
  intro n
  induction n with
  | zero => simp [decomposition.cut_zero]
  | succ n ih =>
      have hstep := decomposition.cut_lt_succ n
      omega

theorem ReturnDecomposition.exists_cut_ge
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (position : Nat) :
    ∃ n : Nat, position ≤ decomposition.cut n :=
  ⟨position, decomposition.le_cut position⟩

/-- The finite prefix of the derived sequence decodes to the corresponding
prefix of the original infinite word. -/
theorem ReturnDecomposition.flatMap_take_derived
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank) :
    ∀ n : Nat,
      (decomposition.derived.take n).flatMap decomposition.blocks =
        x.take (decomposition.cut n) := by
  intro n
  induction n with
  | zero => simp [decomposition.cut_zero]
  | succ n ih =>
      rw [Stream'.take_succ', List.flatMap_append, ih,
        decomposition.cut_succ, Stream'.take_add,
        decomposition.block_at_cut]
      simp [Stream'.get]

theorem ReturnDecomposition.cut_add
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (start : Nat) : ∀ count : Nat,
    decomposition.cut (start + count) = decomposition.cut start +
      ((decomposition.derived.drop start).take count |>.flatMap
        decomposition.blocks).length := by
  intro count
  induction count with
  | zero => simp
  | succ count ih =>
      rw [show start + (count + 1) = (start + count) + 1 by omega,
        decomposition.cut_succ, ih, Stream'.take_succ',
        List.flatMap_append, List.length_append]
      simp only [List.flatMap_singleton]
      simp [Stream'.drop, Stream'.get, Nat.add_comm]
      omega

/-- Any finite interval of derived symbols decodes to the corresponding
finite interval between its two cuts. -/
theorem ReturnDecomposition.flatMap_drop_take_derived
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (start count : Nat) :
    ((decomposition.derived.drop start).take count |>.flatMap
        decomposition.blocks) =
      (x.drop (decomposition.cut start)).take
        (((decomposition.derived.drop start).take count |>.flatMap
          decomposition.blocks).length) := by
  have hwhole := decomposition.flatMap_take_derived (start + count)
  rw [Stream'.take_add (a := decomposition.derived)
      (m := start) (n := count),
    List.flatMap_append,
    decomposition.flatMap_take_derived start,
    decomposition.cut_add start count,
    Stream'.take_add (a := x) (m := decomposition.cut start)
      (n := (((decomposition.derived.drop start).take count |>.flatMap
        decomposition.blocks).length))] at hwhole
  exact List.append_cancel_left hwhole

/-- Decoding `count` successive return symbols produces at least `count`
letters, since every return block is nonempty. -/
theorem ReturnDecomposition.decoded_length_ge
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (start : Nat) : ∀ count : Nat,
    count ≤
      (((decomposition.derived.drop start).take count).flatMap
        decomposition.blocks).length := by
  intro count
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Stream'.take_succ', List.flatMap_append, List.length_append]
      simp only [List.flatMap_singleton]
      have hpositive := decomposition.block_length_pos
        ((decomposition.derived.drop start).get count)
      simp only [Stream'.get_drop] at hpositive ⊢
      omega

/-- Although the structure stores only the successive block occurrences,
the return-word overlap condition forces its marker to occur at every cut. -/
theorem ReturnDecomposition.marker_at_cut
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (start : Nat) :
    InfiniteFactorAt x marker (decomposition.cut start) := by
  let letters := (decomposition.derived.drop start).take marker.length
  let decoded := letters.flatMap decomposition.blocks
  have hlength : marker.length ≤ decoded.length := by
    simpa [letters, decoded] using
      decomposition.decoded_length_ge start marker.length
  have hprefix : marker <+: decoded ++ marker := by
    exact marker_prefix_flatMap_returnWords decomposition.blocks
      decomposition.blocks_are_returns letters
  have htake : (decoded ++ marker).take marker.length = marker :=
    (List.prefix_iff_eq_take.mp hprefix).symm
  have hdecodedTake : decoded.take marker.length = marker := by
    rw [List.take_append_of_le_length hlength] at htake
    exact htake
  have hdecode :=
    decomposition.flatMap_drop_take_derived start marker.length
  change decoded =
      (x.drop (decomposition.cut start)).take decoded.length at hdecode
  have htaken := congrArg (List.take marker.length) hdecode
  rw [hdecodedTake] at htaken
  have hstreamTake :
      ((x.drop (decomposition.cut start)).take decoded.length).take
          marker.length =
        (x.drop (decomposition.cut start)).take marker.length := by
    simp [hlength]
  rw [hstreamTake] at htaken
  exact htaken.symm

/-- A return block at a cut is followed there by the next marker. -/
theorem ReturnDecomposition.block_marker_at_cut
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (start : Nat) :
    InfiniteFactorAt x
      (decomposition.blocks (decomposition.derived start) ++ marker)
      (decomposition.cut start) := by
  rw [InfiniteFactorAt, List.length_append, Stream'.take_add,
    decomposition.block_at_cut]
  have hnext := decomposition.marker_at_cut (start + 1)
  rw [InfiniteFactorAt] at hnext
  have hcut := decomposition.cut_succ start
  have hdrop :
      (x.drop (decomposition.cut start)).drop
          (decomposition.blocks (decomposition.derived start)).length =
        x.drop (decomposition.cut (start + 1)) := by
    rw [Stream'.drop_drop, hcut]
  rw [hdrop]
  exact congrArg
    (fun tail => decomposition.blocks (decomposition.derived start) ++ tail)
    hnext

/-- Consecutive cuts really are consecutive marker occurrences. -/
theorem ReturnDecomposition.no_marker_between_cuts
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (start position : Nat)
    (hleft : decomposition.cut start < position)
    (hright : position < decomposition.cut (start + 1)) :
    ¬ InfiniteFactorAt x marker position := by
  intro hposition
  let offset := position - decomposition.cut start
  have hpositionEq : decomposition.cut start + offset = position := by
    simp [offset, Nat.add_sub_of_le (Nat.le_of_lt hleft)]
  have hblockLength :
      (decomposition.blocks (decomposition.derived start)).length =
        decomposition.cut (start + 1) - decomposition.cut start := by
    rw [decomposition.cut_succ]
    omega
  have hoffsetLt :
      offset < (decomposition.blocks (decomposition.derived start)).length := by
    rw [hblockLength]
    dsimp only [offset]
    omega
  have hwithin :
      offset + marker.length ≤
        (decomposition.blocks (decomposition.derived start) ++ marker).length := by
    simp only [List.length_append]
    omega
  have hfinite : FiniteFactorAt
      (decomposition.blocks (decomposition.derived start) ++ marker)
      marker offset := by
    apply finiteFactorAt_of_nested_infiniteFactorAt
      (decomposition.block_marker_at_cut start)
    · rw [hpositionEq]
      exact hposition
    · exact hwithin
  rcases (decomposition.blocks_are_returns
      (decomposition.derived start)).2.2.2.2 offset |>.mp hfinite with
    hzero | hend
  · dsimp only [offset] at hzero
    omega
  · omega

/-- Every marker occurrence belongs to the cut sequence. -/
theorem ReturnDecomposition.marker_occurrence_eq_cut
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    {position : Nat} (hposition : InfiniteFactorAt x marker position) :
    ∃ index : Nat, decomposition.cut index = position := by
  let witness : ∃ index : Nat, position ≤ decomposition.cut index :=
    decomposition.exists_cut_ge position
  let index := Nat.find witness
  have hindex : position ≤ decomposition.cut index := Nat.find_spec witness
  by_cases hzero : index = 0
  · refine ⟨0, ?_⟩
    rw [decomposition.cut_zero]
    rw [hzero, decomposition.cut_zero] at hindex
    omega
  · obtain ⟨previous, hindexEq⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    have hnotPrevious : ¬ position ≤ decomposition.cut previous := by
      intro hle
      have hminimal := Nat.find_min witness hindexEq.symm.le
      exact hminimal hle
    have hpreviousLt : decomposition.cut previous < position := by omega
    have hright : position ≤ decomposition.cut (previous + 1) := by
      simpa [hindexEq] using hindex
    rcases hright.eq_or_lt with heq | hlt
    · exact ⟨previous + 1, heq.symm⟩
    · exact False.elim
        (decomposition.no_marker_between_cuts previous position
          hpreviousLt hlt hposition)

/-- A return block seen at a cut is the block named by the corresponding
derived symbol. -/
theorem ReturnDecomposition.block_eq_of_block_marker_at_cut
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (a : Fin rank) (index : Nat)
    (hat : InfiniteFactorAt x (decomposition.blocks a ++ marker)
      (decomposition.cut index)) :
    decomposition.blocks a =
      decomposition.blocks (decomposition.derived index) := by
  have hmarkerAtEnd : InfiniteFactorAt x marker
      (decomposition.cut index + (decomposition.blocks a).length) := by
    have hfinite : FiniteFactorAt
        (decomposition.blocks a ++ marker) marker
        (decomposition.blocks a).length := by
      simp [FiniteFactorAt]
    exact hat.of_finiteFactorAt hfinite
  obtain ⟨endpoint, hendpoint⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAtEnd
  have hapositive := decomposition.block_length_pos a
  have hendpointGt : index < endpoint := by
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hendpoint]
    omega
  have hnextLe : index + 1 ≤ endpoint := by omega
  have hlengthLe :
      (decomposition.blocks (decomposition.derived index)).length ≤
        (decomposition.blocks a).length := by
    have hcuts := decomposition.cut_strictMono.monotone hnextLe
    rw [decomposition.cut_succ, hendpoint] at hcuts
    omega
  have hreverseLength :
      (decomposition.blocks a).length ≤
        (decomposition.blocks (decomposition.derived index)).length := by
    by_contra hnot
    have hstrict :
        (decomposition.blocks (decomposition.derived index)).length <
          (decomposition.blocks a).length := by omega
    have hnextMarker := decomposition.marker_at_cut (index + 1)
    have hnextPosition :
        decomposition.cut (index + 1) = decomposition.cut index +
          (decomposition.blocks (decomposition.derived index)).length :=
      decomposition.cut_succ index
    have hfinite : FiniteFactorAt
        (decomposition.blocks a ++ marker) marker
        (decomposition.blocks (decomposition.derived index)).length := by
      apply finiteFactorAt_of_nested_infiniteFactorAt hat
      · rw [hnextPosition] at hnextMarker
        exact hnextMarker
      · simp only [List.length_append]
        omega
    rcases (decomposition.blocks_are_returns a).2.2.2.2
        (decomposition.blocks (decomposition.derived index)).length |>.mp
          hfinite with hzero | hend
    · exact (decomposition.block_length_pos
        (decomposition.derived index)).ne' hzero
    · omega
  have hlength :
      (decomposition.blocks a).length =
        (decomposition.blocks (decomposition.derived index)).length := by
    omega
  have haBlock : InfiniteFactorAt x (decomposition.blocks a)
      (decomposition.cut index) := by
    have hfinite : FiniteFactorAt
        (decomposition.blocks a ++ marker) (decomposition.blocks a) 0 := by
      simp [FiniteFactorAt]
    simpa using hat.of_finiteFactorAt hfinite
  have hactualBlock := decomposition.block_at_cut index
  rw [InfiniteFactorAt] at haBlock hactualBlock
  rw [← hlength] at hactualBlock
  exact haBlock.symm.trans hactualBlock

/-- An occurrence of a coded return block aligns with one unique derived
symbol occurrence. -/
theorem ReturnDecomposition.block_marker_occurrence_aligns
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (a : Fin rank) {position : Nat}
    (hat : InfiniteFactorAt x (decomposition.blocks a ++ marker) position) :
    ∃ index : Nat,
      decomposition.cut index = position ∧ decomposition.derived index = a := by
  have hmarkerPrefix := (decomposition.blocks_are_returns a).2.2.2.1
  have hfinite : FiniteFactorAt
      (decomposition.blocks a ++ marker) marker 0 := by
    refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
  have hmarkerAt : InfiniteFactorAt x marker position := by
    simpa using hat.of_finiteFactorAt hfinite
  obtain ⟨index, hindex⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAt
  have hatCut : InfiniteFactorAt x
      (decomposition.blocks a ++ marker) (decomposition.cut index) := by
    rw [hindex]
    exact hat
  have hblock := decomposition.block_eq_of_block_marker_at_cut a index hatCut
  exact ⟨index, hindex,
    decomposition.blocks_injective hblock |>.symm⟩

/-- Uniform recurrence of the decoded word gives bounded gaps for every
letter of its derived return word. -/
theorem ReturnDecomposition.every_letter_bounded_gaps
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (huniform : IsUniformlyRecurrent x) (a : Fin rank) :
    AppearsWithBoundedGaps decomposition.derived [a] := by
  have hreturn := decomposition.blocks_are_returns a
  obtain ⟨gap, hgapPos, hbounded⟩ := huniform
    (decomposition.blocks a ++ marker) hreturn.2.2.1
  refine ⟨gap, hgapPos, ?_⟩
  intro start
  obtain ⟨physicalOffset, hphysicalOffset, hat⟩ :=
    hbounded (decomposition.cut start)
  obtain ⟨index, hcutIndex, hderived⟩ :=
    decomposition.block_marker_occurrence_aligns a hat
  have hstartLe : start ≤ index := by
    by_contra hnot
    have hcutLt := decomposition.cut_strictMono (by omega : index < start)
    rw [hcutIndex] at hcutLt
    omega
  let offset := index - start
  have hindexEq : start + offset = index := by
    simp [offset, Nat.add_sub_of_le hstartLe]
  have hdecodedLower := decomposition.decoded_length_ge start offset
  have hcutAdd := decomposition.cut_add start offset
  have hcutLower : decomposition.cut start + offset ≤
      decomposition.cut index := by
    rw [hindexEq] at hcutAdd
    rw [hcutAdd]
    omega
  have hoffset : offset ≤ gap := by
    rw [hcutIndex] at hcutLower
    omega
  refine ⟨offset, hoffset, ?_⟩
  rw [hindexEq]
  change Stream'.get decomposition.derived index = a at hderived
  simpa [InfiniteFactorAt, Stream'.take_succ] using hderived

/-- Every named return block is actually used by the derived stream. -/
theorem ReturnDecomposition.every_letter_occurs
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (a : Fin rank) :
    Substitution.OccursInInfiniteWord a decomposition.derived := by
  obtain ⟨position, hat⟩ :=
    (decomposition.blocks_are_returns a).2.2.1
  obtain ⟨index, _hcut, hletter⟩ :=
    decomposition.block_marker_occurrence_aligns a hat
  exact ⟨index, hletter⟩

/-- If a concatenation of named return blocks followed by the marker occurs
at a cut, injective return-word decoding recovers that exact derived factor. -/
theorem ReturnDecomposition.derived_factor_of_decoded_marker_at_cut
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank) :
    ∀ (letters : Word (Fin rank)) (start : Nat),
      InfiniteFactorAt x (letters.flatMap decomposition.blocks ++ marker)
        (decomposition.cut start) →
      (decomposition.derived.drop start).take letters.length = letters := by
  intro letters
  induction letters with
  | nil => intro start _; simp
  | cons a rest ih =>
      intro start hat
      have hrestMarker : marker <+:
          rest.flatMap decomposition.blocks ++ marker :=
        marker_prefix_flatMap_returnWords decomposition.blocks
          decomposition.blocks_are_returns rest
      have hfirstPrefix : decomposition.blocks a ++ marker <+:
          (a :: rest).flatMap decomposition.blocks ++ marker := by
        simpa [List.flatMap_cons, List.append_assoc] using
          (List.prefix_append_right_inj
            (decomposition.blocks a)).mpr hrestMarker
      have hfirstFinite : FiniteFactorAt
          ((a :: rest).flatMap decomposition.blocks ++ marker)
          (decomposition.blocks a ++ marker) 0 := by
        refine ⟨by simpa using hfirstPrefix.length_le, ?_⟩
        simpa using (List.prefix_iff_eq_take.mp hfirstPrefix).symm
      have hfirstAt : InfiniteFactorAt x
          (decomposition.blocks a ++ marker) (decomposition.cut start) := by
        simpa using hat.of_finiteFactorAt hfirstFinite
      have hblock :=
        decomposition.block_eq_of_block_marker_at_cut a start hfirstAt
      have hderived : decomposition.derived start = a :=
        (decomposition.blocks_injective hblock).symm
      let tail := rest.flatMap decomposition.blocks ++ marker
      have htailFinite : FiniteFactorAt
          ((a :: rest).flatMap decomposition.blocks ++ marker)
          tail (decomposition.blocks a).length := by
        simp [FiniteFactorAt, tail]
      have htailAt : InfiniteFactorAt x tail
          (decomposition.cut (start + 1)) := by
        have htranslated := hat.of_finiteFactorAt htailFinite
        rw [hblock, ← decomposition.cut_succ] at htranslated
        exact htranslated
      have hrest := ih (start + 1) (by simpa [tail] using htailAt)
      rw [List.length_cons, Stream'.take_succ]
      simp only [Stream'.head_drop, Stream'.get]
      rw [hderived]
      congr 1
      simpa [Stream'.tail_drop] using hrest

/-- The decoding of every finite interval of derived symbols, followed by
the marker, occurs at the corresponding cut. -/
theorem ReturnDecomposition.decoded_marker_at_cut
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (start count : Nat) :
    InfiniteFactorAt x
      (((decomposition.derived.drop start).take count).flatMap
          decomposition.blocks ++ marker)
      (decomposition.cut start) := by
  let letters := (decomposition.derived.drop start).take count
  let decoded := letters.flatMap decomposition.blocks
  have hdecode := decomposition.flatMap_drop_take_derived start count
  change decoded =
      (x.drop (decomposition.cut start)).take decoded.length at hdecode
  have hcut := decomposition.cut_add start count
  change decomposition.cut (start + count) =
      decomposition.cut start + decoded.length at hcut
  have hdrop :
      (x.drop (decomposition.cut start)).drop decoded.length =
        x.drop (decomposition.cut (start + count)) := by
    rw [Stream'.drop_drop, ← hcut]
  rw [InfiniteFactorAt, List.length_append, Stream'.take_add]
  rw [← hdecode, hdrop, decomposition.marker_at_cut]

/-- A derived return word of a uniformly recurrent decoded word is itself
uniformly recurrent. -/
theorem ReturnDecomposition.uniformlyRecurrent_derived
    {delta : Type u} {x : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition x marker rank)
    (huniform : IsUniformlyRecurrent x) :
    IsUniformlyRecurrent decomposition.derived := by
  intro word hword
  obtain ⟨origin, horigin⟩ := hword
  let encoded := word.flatMap decomposition.blocks
  have hactual :
      (decomposition.derived.drop origin).take word.length = word := horigin
  have hencodedAt := decomposition.decoded_marker_at_cut origin word.length
  change InfiniteFactorAt x
      ((((decomposition.derived.drop origin).take word.length).flatMap
          decomposition.blocks) ++ marker)
      (decomposition.cut origin) at hencodedAt
  rw [hactual] at hencodedAt
  change InfiniteFactorAt x (encoded ++ marker)
      (decomposition.cut origin) at hencodedAt
  obtain ⟨gap, hgapPos, hbounded⟩ :=
    huniform (encoded ++ marker) ⟨decomposition.cut origin, hencodedAt⟩
  refine ⟨gap, hgapPos, ?_⟩
  intro start
  obtain ⟨physicalOffset, hphysicalOffset, hat⟩ :=
    hbounded (decomposition.cut start)
  have hmarkerPrefix : marker <+: encoded ++ marker := by
    exact marker_prefix_flatMap_returnWords decomposition.blocks
      decomposition.blocks_are_returns word
  have hmarkerFinite : FiniteFactorAt (encoded ++ marker) marker 0 := by
    refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
  have hmarkerAt : InfiniteFactorAt x marker
      (decomposition.cut start + physicalOffset) := by
    simpa using hat.of_finiteFactorAt hmarkerFinite
  obtain ⟨index, hcutIndex⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAt
  have hstartLe : start ≤ index := by
    by_contra hnot
    have hcutLt := decomposition.cut_strictMono (by omega : index < start)
    rw [hcutIndex] at hcutLt
    omega
  have hatCut : InfiniteFactorAt x (word.flatMap decomposition.blocks ++ marker)
      (decomposition.cut index) := by
    change InfiniteFactorAt x (encoded ++ marker) (decomposition.cut index)
    rw [hcutIndex]
    exact hat
  have hderivedFactor :=
    decomposition.derived_factor_of_decoded_marker_at_cut word index hatCut
  let offset := index - start
  have hindexEq : start + offset = index := by
    simp [offset, Nat.add_sub_of_le hstartLe]
  have hdecodedLower := decomposition.decoded_length_ge start offset
  have hcutAdd := decomposition.cut_add start offset
  have hcutLower : decomposition.cut start + offset ≤
      decomposition.cut index := by
    rw [hindexEq] at hcutAdd
    rw [hcutAdd]
    omega
  have hoffset : offset ≤ gap := by
    rw [hcutIndex] at hcutLower
    omega
  refine ⟨offset, hoffset, ?_⟩
  rw [hindexEq]
  exact hderivedFactor

namespace Substitution

theorem iterateWord_add_for_return
    {delta : Type u} (sigma : Substitution delta)
    (m n : Nat) (word : Word delta) :
    sigma.iterateWord (m + n) word =
      sigma.iterateWord m (sigma.iterateWord n word) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simpa only [Nat.succ_add, iterateWord_succ] using
        congrArg sigma.mapWord ih

theorem length_le_mapWord_for_return
    {delta : Type u} (sigma : Substitution delta) (word : Word delta) :
    word.length ≤ (sigma.mapWord word).length := by
  induction word with
  | nil => simp
  | cons a word ih =>
      rw [mapWord_cons, List.length_append, List.length_cons]
      have ha : 0 < (sigma a).length :=
        List.length_pos_of_ne_nil (sigma.image_ne_nil a)
      omega

theorem length_le_iterateWord_for_return
    {delta : Type u} (sigma : Substitution delta)
    (n : Nat) (word : Word delta) :
    word.length ≤ (sigma.iterateWord n word).length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact ih.trans
        (length_le_mapWord_for_return sigma (sigma.iterateWord n word))

/-- A positive substitution power sends a segment of a fixed word to the
corresponding segment at the substituted prefix length. -/
theorem iterateWord_drop_take_at_fixed_positive
    {delta : Type u} {sigma : Substitution delta}
    {word : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint word)
    {level : Nat} (hlevel : 0 < level) (start count : Nat) :
    InfiniteFactorAt word
      (sigma.iterateWord level ((word.drop start).take count))
      (sigma.iterateWord level (word.take start)).length := by
  let tau := sigma.power level
  let pref := tau.mapWord (word.take start)
  let segment := tau.mapWord ((word.drop start).take count)
  have hfixedTau : tau.IsFixedPoint word := isFixedPoint_power hfixed hlevel
  have hprefixSplit : pref ++ₛ tau.mapInfinite (word.drop start) = word := by
    calc
      pref ++ₛ tau.mapInfinite (word.drop start) =
          tau.mapInfinite (word.take start ++ₛ word.drop start) := by
        exact (tau.mapInfinite_append_stream _ _).symm
      _ = tau.mapInfinite word := by rw [Stream'.append_take_drop]
      _ = word := hfixedTau
  have hsegmentSplit :
      tau.mapInfinite (word.drop start) =
        segment ++ₛ tau.mapInfinite ((word.drop start).drop count) := by
    calc
      tau.mapInfinite (word.drop start) =
          tau.mapInfinite
            ((word.drop start).take count ++ₛ
              (word.drop start).drop count) := by
        rw [Stream'.append_take_drop]
      _ = segment ++ₛ
          tau.mapInfinite ((word.drop start).drop count) :=
        tau.mapInfinite_append_stream _ _
  have htail : word.drop pref.length = tau.mapInfinite (word.drop start) := by
    have hdropped := congrArg (fun stream : InfiniteWord delta =>
      stream.drop pref.length) hprefixSplit
    simpa [Stream'.drop_append_stream] using hdropped.symm
  have htaken :
      (tau.mapInfinite (word.drop start)).take segment.length = segment := by
    rw [hsegmentSplit]
    simpa using Stream'.take_append_of_le_length
      (x := segment)
      (a := tau.mapInfinite ((word.drop start).drop count))
      (n := segment.length) le_rfl
  have hcombined :
      (word.drop pref.length).take segment.length = segment :=
    (congrArg (fun stream : InfiniteWord delta =>
      stream.take segment.length) htail).trans htaken
  change (word.drop
      (sigma.iterateWord level (word.take start)).length).take
        (sigma.iterateWord level ((word.drop start).take count)).length =
      sigma.iterateWord level ((word.drop start).take count)
  simpa [tau, pref, segment, power_mapWord] using hcombined

/-- Physical location of the image of a return cut under a substitution. -/
def substitutedReturnCut
    {alpha : Type*} (sigma : Substitution alpha)
    {fixedWord : InfiniteWord alpha} {marker : Word alpha} {rank : Nat}
    (decomposition : ReturnDecomposition fixedWord marker rank)
    (n : Nat) : Nat :=
  (sigma.mapWord (fixedWord.take (decomposition.cut n))).length

/-- Substituting a return block in a fixed word places its image at the
substituted return cut. -/
theorem map_block_at_substitutedReturnCut
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} (hfixed : sigma.IsFixedPoint fixedWord)
    {marker : Word alpha} {rank : Nat}
    (decomposition : ReturnDecomposition fixedWord marker rank)
    (n : Nat) :
    InfiniteFactorAt fixedWord
      (sigma.mapWord (decomposition.blocks (decomposition.derived n)))
      (substitutedReturnCut sigma decomposition n) := by
  have h := iterateWord_drop_take_at_fixed_positive hfixed
    (level := 1) (by omega)
    (decomposition.cut n)
    (decomposition.blocks (decomposition.derived n)).length
  rw [decomposition.block_at_cut n] at h
  simpa [substitutedReturnCut, iterateWord] using h

/-- For the one-letter head marker, every substituted return cut is again a
marker occurrence. -/
theorem marker_at_substitutedReturnCut
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} (hfixed : sigma.IsFixedPoint fixedWord)
    {rank : Nat}
    (decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank)
    (n : Nat) :
    InfiniteFactorAt fixedWord [fixedWord.head]
      (substitutedReturnCut sigma decomposition n) := by
  have hwhole := iterateWord_drop_take_at_fixed_positive hfixed
    (level := 1) (by omega)
    (decomposition.cut n) 1
  have hsource : (fixedWord.drop (decomposition.cut n)).take 1 =
      [fixedWord.head] := decomposition.marker_at_cut n
  rw [hsource] at hwhole
  have hhead : sigma.imageHead fixedWord.head = fixedWord.head := by
    have hzero := congrFun hfixed 0
    simpa using hzero
  have hprefix : [fixedWord.head] <+: sigma.mapWord [fixedWord.head] := by
    have himage : [fixedWord.head] <+: sigma fixedWord.head := by
      rw [← sigma.imageHead_cons_imageTail, hhead]
      exact List.prefix_append _ _
    simpa using himage
  have hfinite : FiniteFactorAt (sigma.mapWord [fixedWord.head])
      [fixedWord.head] 0 := by
    refine ⟨by simpa using hprefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hprefix).symm
  simpa [substitutedReturnCut, iterateWord] using
    hwhole.of_finiteFactorAt hfinite

theorem substitutedReturnCut_succ
    {alpha : Type*} (sigma : Substitution alpha)
    {fixedWord : InfiniteWord alpha} {marker : Word alpha} {rank : Nat}
    (decomposition : ReturnDecomposition fixedWord marker rank)
    (n : Nat) :
    substitutedReturnCut sigma decomposition (n + 1) =
    substitutedReturnCut sigma decomposition n +
        (sigma.mapWord
          (decomposition.blocks (decomposition.derived n))).length := by
  have hblock := decomposition.block_at_cut n
  rw [InfiniteFactorAt] at hblock
  simp only [substitutedReturnCut, decomposition.cut_succ,
    Stream'.take_add, mapWord_append, List.length_append]
  rw [hblock]

/-- The unique factorization of substituted return blocks into return blocks
for the head marker. -/
structure ReturnSubstitutionFactorization
    {alpha : Type*} (sigma : Substitution alpha)
    {fixedWord : InfiniteWord alpha} {rank : Nat}
    (decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank) where
  factor : Fin rank → Word (Fin rank)
  factor_decodes : ∀ a : Fin rank,
    (factor a).flatMap decomposition.blocks =
      sigma.mapWord (decomposition.blocks a)
  boundary : Nat → Nat
  boundary_zero : boundary 0 = 0
  boundary_cut : ∀ n : Nat,
    decomposition.cut (boundary n) =
      substitutedReturnCut sigma decomposition n
  boundary_succ : ∀ n : Nat,
    boundary (n + 1) = boundary n +
      (factor (decomposition.derived n)).length
  derived_factor_at : ∀ n : Nat,
    InfiniteFactorAt decomposition.derived
      (factor (decomposition.derived n)) (boundary n)

theorem exists_returnSubstitutionFactorization
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} (hfixed : sigma.IsFixedPoint fixedWord)
    {rank : Nat}
    (decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank) :
    Nonempty (ReturnSubstitutionFactorization sigma decomposition) := by
  classical
  let boundary : Nat → Nat := fun n =>
    Classical.choose (decomposition.marker_occurrence_eq_cut
      (marker_at_substitutedReturnCut hfixed decomposition n))
  have hboundaryCut : ∀ n : Nat,
      decomposition.cut (boundary n) =
        substitutedReturnCut sigma decomposition n := by
    intro n
    exact Classical.choose_spec (decomposition.marker_occurrence_eq_cut
      (marker_at_substitutedReturnCut hfixed decomposition n))
  have hsubZero : substitutedReturnCut sigma decomposition 0 = 0 := by
    simp [substitutedReturnCut, decomposition.cut_zero]
  have hboundaryZero : boundary 0 = 0 := by
    apply decomposition.cut_injective
    rw [hboundaryCut, hsubZero, decomposition.cut_zero]
  have hsubStrict : StrictMono (substitutedReturnCut sigma decomposition) := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [substitutedReturnCut_succ]
    exact Nat.lt_add_of_pos_right
      (List.length_pos_of_ne_nil
        (sigma.mapWord_ne_nil
          (decomposition.blocks_are_returns (decomposition.derived n)).2.1))
  have hboundaryStrict : StrictMono boundary := by
    intro left right hlr
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hboundaryCut, hboundaryCut]
    exact hsubStrict hlr
  let factorAt : Nat → Word (Fin rank) := fun n =>
    (decomposition.derived.drop (boundary n)).take
      (boundary (n + 1) - boundary n)
  have hfactorAtDecodes : ∀ n : Nat,
      (factorAt n).flatMap decomposition.blocks =
        sigma.mapWord (decomposition.blocks (decomposition.derived n)) := by
    intro n
    have hboundaryLe : boundary n ≤ boundary (n + 1) :=
      (hboundaryStrict (Nat.lt_succ_self n)).le
    have hdecode := decomposition.flatMap_drop_take_derived
      (boundary n) (boundary (n + 1) - boundary n)
    change (factorAt n).flatMap decomposition.blocks =
      (fixedWord.drop (decomposition.cut (boundary n))).take
        ((factorAt n).flatMap decomposition.blocks).length at hdecode
    have hcutAdd := decomposition.cut_add (boundary n)
      (boundary (n + 1) - boundary n)
    have hboundaryAdd : boundary n + (boundary (n + 1) - boundary n) =
        boundary (n + 1) := Nat.add_sub_of_le hboundaryLe
    rw [hboundaryAdd] at hcutAdd
    change decomposition.cut (boundary (n + 1)) =
      decomposition.cut (boundary n) +
        ((factorAt n).flatMap decomposition.blocks).length at hcutAdd
    have hsubSucc := substitutedReturnCut_succ sigma decomposition n
    rw [hboundaryCut, hboundaryCut] at hcutAdd
    have hlength : ((factorAt n).flatMap decomposition.blocks).length =
        (sigma.mapWord
          (decomposition.blocks (decomposition.derived n))).length := by
      omega
    rw [hboundaryCut, hlength] at hdecode
    exact hdecode.trans
      (map_block_at_substitutedReturnCut hfixed decomposition n)
  let occurrence : Fin rank → Nat := fun a =>
    Classical.choose (decomposition.every_letter_occurs a)
  have hoccurrence : ∀ a : Fin rank,
      decomposition.derived (occurrence a) = a := by
    intro a
    exact Classical.choose_spec (decomposition.every_letter_occurs a)
  let factor : Fin rank → Word (Fin rank) := fun a =>
    factorAt (occurrence a)
  have hfactorDecodes : ∀ a : Fin rank,
      (factor a).flatMap decomposition.blocks =
        sigma.mapWord (decomposition.blocks a) := by
    intro a
    change (factorAt (occurrence a)).flatMap decomposition.blocks = _
    rw [hfactorAtDecodes, hoccurrence]
  have hfactorAt : ∀ n : Nat,
      factor (decomposition.derived n) = factorAt n := by
    intro n
    apply flatMap_returnWords_injective
      decomposition.blocks_injective decomposition.blocks_are_returns
    change (factor (decomposition.derived n)).flatMap decomposition.blocks =
      (factorAt n).flatMap decomposition.blocks
    exact (hfactorDecodes (decomposition.derived n)).trans
      (hfactorAtDecodes n).symm
  have hboundarySucc : ∀ n : Nat,
      boundary (n + 1) = boundary n +
        (factor (decomposition.derived n)).length := by
    intro n
    have hboundaryLe : boundary n ≤ boundary (n + 1) :=
      (hboundaryStrict (Nat.lt_succ_self n)).le
    rw [hfactorAt]
    change boundary (n + 1) = boundary n +
      ((decomposition.derived.drop (boundary n)).take
        (boundary (n + 1) - boundary n)).length
    simp only [Stream'.length_take]
    exact (Nat.add_sub_of_le hboundaryLe).symm
  have hderivedFactorAt : ∀ n : Nat,
      InfiniteFactorAt decomposition.derived
        (factor (decomposition.derived n)) (boundary n) := by
    intro n
    rw [hfactorAt]
    simp [InfiniteFactorAt, factorAt]
  exact ⟨{
    factor := factor
    factor_decodes := hfactorDecodes
    boundary := boundary
    boundary_zero := hboundaryZero
    boundary_cut := hboundaryCut
    boundary_succ := hboundarySucc
    derived_factor_at := hderivedFactorAt }⟩

theorem ReturnSubstitutionFactorization.factor_ne_nil
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} {rank : Nat}
    {decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank}
    (factorization : ReturnSubstitutionFactorization sigma decomposition)
    (a : Fin rank) : factorization.factor a ≠ [] := by
  intro hempty
  have hdecode := factorization.factor_decodes a
  rw [hempty] at hdecode
  simp only [List.flatMap_nil] at hdecode
  exact sigma.mapWord_ne_nil
    (decomposition.blocks_are_returns a).2.1 hdecode.symm

/-- The induced substitution on return blocks. -/
def ReturnSubstitutionFactorization.substitution
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} {rank : Nat}
    {decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank}
    (factorization : ReturnSubstitutionFactorization sigma decomposition) :
    Substitution (Fin rank) where
  image := factorization.factor
  image_ne_nil := factorization.factor_ne_nil

/-- The induced return substitution fixes the derived return word. -/
theorem ReturnSubstitutionFactorization.fixed
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} {rank : Nat}
    {decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank}
    (factorization : ReturnSubstitutionFactorization sigma decomposition) :
    factorization.substitution.IsFixedPoint decomposition.derived := by
  have hboundaryLower : ∀ n : Nat, n ≤ factorization.boundary n := by
    intro n
    induction n with
    | zero => simp [factorization.boundary_zero]
    | succ n ih =>
        rw [factorization.boundary_succ]
        have hpositive : 0 <
            (factorization.factor (decomposition.derived n)).length :=
          List.length_pos_of_ne_nil
            (factorization.factor_ne_nil (decomposition.derived n))
        omega
  have hfiniteTiling : ∀ n : Nat,
      factorization.substitution.mapWord (decomposition.derived.take n) =
        decomposition.derived.take (factorization.boundary n) := by
    intro n
    induction n with
    | zero => simp [factorization.boundary_zero]
    | succ n ih =>
        have hfactorAt := factorization.derived_factor_at n
        change
          (decomposition.derived.drop (factorization.boundary n)).take
              (factorization.factor (decomposition.derived n)).length =
            factorization.factor (decomposition.derived n) at hfactorAt
        change
          (decomposition.derived.drop (factorization.boundary n)).take
              (factorization.factor
                (Stream'.get decomposition.derived n)).length =
            factorization.factor
              (Stream'.get decomposition.derived n) at hfactorAt
        rw [Stream'.take_succ', Substitution.mapWord_append,
          Substitution.mapWord_cons, Substitution.mapWord_nil,
          List.append_nil, ih, factorization.boundary_succ,
          Stream'.take_add]
        change
          decomposition.derived.take (factorization.boundary n) ++
              factorization.factor (Stream'.get decomposition.derived n) =
            decomposition.derived.take (factorization.boundary n) ++
              (decomposition.derived.drop
                (factorization.boundary n)).take
                  (factorization.factor
                    (Stream'.get decomposition.derived n)).length
        rw [hfactorAt]
  rw [Substitution.IsFixedPoint]
  funext position
  let count := position + 1
  have hposition : position < factorization.boundary count := by
    have := hboundaryLower count
    omega
  have hwordLength :
      (factorization.substitution.mapWord
          (decomposition.derived.take count)).length =
        factorization.boundary count := by
    rw [hfiniteTiling]
    simp
  have hmapPrefix :
      (factorization.substitution.mapInfinite decomposition.derived).take
          (factorization.boundary count) =
        factorization.substitution.mapWord
          (decomposition.derived.take count) := by
    rw [← hwordLength]
    calc
      (factorization.substitution.mapInfinite decomposition.derived).take
          (factorization.substitution.mapWord
            (decomposition.derived.take count)).length =
        (factorization.substitution.mapInfinite
          (decomposition.derived.take count ++ₛ
            decomposition.derived.drop count)).take
              (factorization.substitution.mapWord
                (decomposition.derived.take count)).length := by
          rw [Stream'.append_take_drop]
      _ = (factorization.substitution.mapWord
              (decomposition.derived.take count) ++ₛ
            factorization.substitution.mapInfinite
              (decomposition.derived.drop count)).take
                (factorization.substitution.mapWord
                  (decomposition.derived.take count)).length := by
          rw [factorization.substitution.mapInfinite_append_stream]
      _ = factorization.substitution.mapWord
              (decomposition.derived.take count) := by
          simpa using Stream'.take_append_of_le_length
            (x := factorization.substitution.mapWord
              (decomposition.derived.take count))
            (a := factorization.substitution.mapInfinite
              (decomposition.derived.drop count))
            (n := (factorization.substitution.mapWord
              (decomposition.derived.take count)).length) le_rfl
  have hprefix :
      (factorization.substitution.mapInfinite decomposition.derived).take
          (factorization.boundary count) =
        decomposition.derived.take (factorization.boundary count) :=
    hmapPrefix.trans (hfiniteTiling count)
  have hleftIndex : position <
      ((factorization.substitution.mapInfinite decomposition.derived).take
        (factorization.boundary count)).length := by
    simpa using hposition
  have hrightIndex : position <
      (decomposition.derived.take
        (factorization.boundary count)).length := by
    simpa using hposition
  have hleftGet := Stream'.take_get
    (a := factorization.substitution.mapInfinite decomposition.derived)
    (m := position) (n := factorization.boundary count) hleftIndex
  have hrightGet := Stream'.take_get
    (a := decomposition.derived)
    (m := position) (n := factorization.boundary count) hrightIndex
  change Stream'.get
      (factorization.substitution.mapInfinite decomposition.derived) position =
    Stream'.get decomposition.derived position
  rw [← hleftGet, ← hrightGet]
  rw [← Option.some_inj, ← List.getElem?_eq_getElem,
    ← List.getElem?_eq_getElem]
  exact congrArg (fun word => word[position]?) hprefix

/-- Metric length commutes with decoding a word of blocks. -/
theorem wordMetricLength_flatMap
    {alpha beta : Type*} (length : beta → ℝ)
    (blocks : alpha → Word beta) (letters : Word alpha) :
    wordMetricLength (fun a => wordMetricLength length (blocks a)) letters =
      wordMetricLength length (letters.flatMap blocks) := by
  induction letters with
  | nil => simp [wordMetricLength]
  | cons a letters ih =>
      calc
        wordMetricLength
              (fun a => wordMetricLength length (blocks a))
              (a :: letters) =
            wordMetricLength length (blocks a) +
              wordMetricLength
                (fun b => wordMetricLength length (blocks b)) letters := rfl
        _ = wordMetricLength length (blocks a) +
              wordMetricLength length (letters.flatMap blocks) := by rw [ih]
        _ = wordMetricLength length
              (blocks a ++ letters.flatMap blocks) := by
            simp [wordMetricLength, List.sum_append]
        _ = wordMetricLength length
              ((a :: letters).flatMap blocks) := rfl

theorem wordMetricLength_nonneg
    {alpha : Type*} (length : alpha → ℝ)
    (hlength : ∀ a, 0 ≤ length a) (word : Word alpha) :
    0 ≤ wordMetricLength length word := by
  induction word with
  | nil => simp [wordMetricLength]
  | cons a word ih =>
      simp only [wordMetricLength, List.map_cons, List.sum_cons]
      exact add_nonneg (hlength a) (by simpa [wordMetricLength] using ih)

theorem wordMetricLength_pos_of_ne_nil
    {alpha : Type*} (length : alpha → ℝ)
    (hlength : ∀ a, 0 < length a) {word : Word alpha}
    (hword : word ≠ []) :
    0 < wordMetricLength length word := by
  rcases word with _ | ⟨a, word⟩
  · exact False.elim (hword rfl)
  · simp only [wordMetricLength, List.map_cons, List.sum_cons]
    exact add_pos_of_pos_of_nonneg (hlength a)
      (by
        simpa [wordMetricLength] using
          wordMetricLength_nonneg length
            (fun b => (hlength b).le) word)

theorem ReturnSubstitutionFactorization.returnMetric_pos
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} {rank : Nat}
    {decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank}
    (factorization : ReturnSubstitutionFactorization sigma decomposition)
    (length : alpha → ℝ) (hlength : ∀ a, 0 < length a) :
    ∀ a : Fin rank,
      0 < wordMetricLength length (decomposition.blocks a) := by
  intro a
  exact wordMetricLength_pos_of_ne_nil length hlength
    (decomposition.blocks_are_returns a).2.1

/-- Exact metric scaling descends to the induced return substitution. -/
theorem ReturnSubstitutionFactorization.scalesReturnMetric
    {alpha : Type*} {sigma : Substitution alpha}
    {fixedWord : InfiniteWord alpha} {rank : Nat}
    {decomposition : ReturnDecomposition fixedWord [fixedWord.head] rank}
    (factorization : ReturnSubstitutionFactorization sigma decomposition)
    {length : alpha → ℝ} {scale : ℝ}
    (hscale : SubstitutionScalesLetterLengths sigma length scale) :
    SubstitutionScalesLetterLengths factorization.substitution
      (fun a => wordMetricLength length (decomposition.blocks a)) scale := by
  intro a
  change wordMetricLength
      (fun b => wordMetricLength length (decomposition.blocks b))
      (factorization.factor a) =
    scale * wordMetricLength length (decomposition.blocks a)
  rw [wordMetricLength_flatMap, factorization.factor_decodes,
    wordMetricLength_mapWord_of_scales hscale]

/-- A uniformly recurrent fixed word using every letter, together with
unbounded growth of every letter image, forces the substitution to be
primitive. -/
theorem primitive_of_fixed_uniform_all_images_grow
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    {rho : Substitution alpha} {word : InfiniteWord alpha}
    (hfixed : rho.IsFixedPoint word)
    (huniform : IsUniformlyRecurrent word)
    (hoccurs : ∀ a : alpha, OccursInInfiniteWord a word)
    (hgrows : ∀ a : alpha, LetterImagesGrow rho a) :
    ∃ iterate : Nat, 0 < iterate ∧
      ∀ a b : alpha, b ∈ rho.iterateLetter iterate a := by
  classical
  have hletterFactor : ∀ b : alpha, IsInfiniteFactor word [b] := by
    intro b
    obtain ⟨position, hposition⟩ := hoccurs b
    refine ⟨position, ?_⟩
    change (word.drop position).take 1 = [b]
    rw [Stream'.take_succ]
    simp [Stream'.get, hposition]
  have hbounded : ∀ b : alpha, AppearsWithBoundedGaps word [b] := by
    intro b
    exact huniform [b] (hletterFactor b)
  choose gap hgapPos hgap using hbounded
  let commonGap : Nat := Finset.univ.sup gap
  have hgapLe : ∀ b : alpha, gap b ≤ commonGap := by
    intro b
    exact Finset.le_sup (f := gap) (Finset.mem_univ b)
  have hlevelExists : ∀ a : alpha, ∃ level : Nat,
      commonGap + 1 ≤ (rho.iterateLetter level a).length := by
    intro a
    exact hgrows a (commonGap + 1)
  choose level hlevel using hlevelExists
  let commonLevel : Nat := Finset.univ.sup level
  have hlevelLe : ∀ a : alpha, level a ≤ commonLevel := by
    intro a
    exact Finset.le_sup (f := level) (Finset.mem_univ a)
  let iterate := commonLevel + 1
  refine ⟨iterate, by simp [iterate], ?_⟩
  intro a b
  have himageLength : commonGap + 1 ≤
      (rho.iterateLetter iterate a).length := by
    obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le (hlevelLe a)
    have hbase : (rho.iterateLetter (level a) a).length ≤
        (rho.iterateLetter commonLevel a).length := by
      rw [hextra, Nat.add_comm]
      change (rho.iterateWord (level a) [a]).length ≤
        (rho.iterateWord (extra + level a) [a]).length
      rw [iterateWord_add_for_return rho]
      exact length_le_iterateWord_for_return rho extra
        (rho.iterateWord (level a) [a])
    have hnext : (rho.iterateLetter commonLevel a).length ≤
        (rho.iterateLetter iterate a).length := by
      change (rho.iterateWord commonLevel [a]).length ≤
        (rho.iterateWord (commonLevel + 1) [a]).length
      rw [show commonLevel + 1 = 1 + commonLevel by omega,
        iterateWord_add_for_return rho]
      exact length_le_iterateWord_for_return rho 1
        (rho.iterateWord commonLevel [a])
    exact (hlevel a).trans (hbase.trans hnext)
  obtain ⟨sourcePosition, hsourcePosition⟩ := hoccurs a
  have htakeSource : (word.drop sourcePosition).take 1 = [a] := by
    rw [Stream'.take_succ]
    simp [Stream'.get, hsourcePosition]
  have himageAt := iterateWord_drop_take_at_fixed_positive hfixed
    (level := iterate) (by simp [iterate]) sourcePosition 1
  rw [htakeSource] at himageAt
  change InfiniteFactorAt word (rho.iterateLetter iterate a)
    (rho.iterateWord iterate (word.take sourcePosition)).length at himageAt
  let imageStart :=
    (rho.iterateWord iterate (word.take sourcePosition)).length
  obtain ⟨offset, hoffset, hbAt⟩ := hgap b imageStart
  have hwithin : offset + [b].length ≤
      (rho.iterateLetter iterate a).length := by
    simp only [List.length_singleton]
    have : offset + 1 ≤ commonGap + 1 :=
      Nat.add_le_add_right (hoffset.trans (hgapLe b)) 1
    exact this.trans himageLength
  have hbFinite : FiniteFactorAt (rho.iterateLetter iterate a) [b] offset :=
    finiteFactorAt_of_nested_infiniteFactorAt
      (by simpa [imageStart] using himageAt) hbAt hwithin
  exact (List.singleton_infix_iff b _).mp hbFinite.isInfix

/-- Transport only the ambient infinite word of a return decomposition. -/
def castReturnDecompositionWord
    {delta : Type*} {left right : InfiniteWord delta}
    {marker : Word delta} {rank : Nat}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank) :
    ReturnDecomposition right marker rank := by
  subst right
  exact decomposition

@[simp] theorem castReturnDecompositionWord_derived
    {delta : Type*} {left right : InfiniteWord delta}
    {marker : Word delta} {rank : Nat}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank) :
    (castReturnDecompositionWord hword decomposition).derived =
      decomposition.derived := by
  subst right
  rfl

end Substitution

/-- The canonical factorization of return blocks for a longer marker into
return blocks for a prefix marker. -/
structure NestedReturnFactorization
    {delta : Type u} {x : InfiniteWord delta}
    {shortMarker longMarker : Word delta}
    {shortRank longRank : Nat}
    (short : ReturnDecomposition x shortMarker shortRank)
    (long : ReturnDecomposition x longMarker longRank) where
  factor : Fin longRank → Word (Fin shortRank)
  factor_decodes : ∀ b : Fin longRank,
    (factor b).flatMap short.blocks = long.blocks b
  boundary : Nat → Nat
  boundary_zero : boundary 0 = 0
  boundary_cut : ∀ n : Nat, short.cut (boundary n) = long.cut n
  boundary_succ : ∀ n : Nat,
    boundary (n + 1) = boundary n + (factor (long.derived n)).length
  derived_factor_at : ∀ n : Nat,
    InfiniteFactorAt short.derived (factor (long.derived n)) (boundary n)

/-- Every cut for a longer marker is a cut for a prefix marker. -/
theorem ReturnDecomposition.cut_alignment_of_marker_prefix
    {delta : Type u} {x : InfiniteWord delta}
    {shortMarker longMarker : Word delta}
    {shortRank longRank : Nat}
    (short : ReturnDecomposition x shortMarker shortRank)
    (long : ReturnDecomposition x longMarker longRank)
    (hprefix : shortMarker <+: longMarker) (n : Nat) :
    ∃ index : Nat, short.cut index = long.cut n := by
  have hfinite : FiniteFactorAt longMarker shortMarker 0 := by
    refine ⟨by simpa using hprefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hprefix).symm
  have hshortAt : InfiniteFactorAt x shortMarker (long.cut n) := by
    simpa using (long.marker_at_cut n).of_finiteFactorAt hfinite
  exact short.marker_occurrence_eq_cut hshortAt

/-- Nested marker decompositions have a unique return-block factorization;
the boundary equations and tiling of the short derived stream are derived
from the two cut sequences. -/
theorem exists_nestedReturnFactorization
    {delta : Type u} {x : InfiniteWord delta}
    {shortMarker longMarker : Word delta}
    {shortRank longRank : Nat}
    (short : ReturnDecomposition x shortMarker shortRank)
    (long : ReturnDecomposition x longMarker longRank)
    (hprefix : shortMarker <+: longMarker) :
    Nonempty (NestedReturnFactorization short long) := by
  classical
  let boundary : Nat → Nat := fun n =>
    Classical.choose (short.cut_alignment_of_marker_prefix long hprefix n)
  have hboundaryCut : ∀ n : Nat,
      short.cut (boundary n) = long.cut n := by
    intro n
    exact Classical.choose_spec
      (short.cut_alignment_of_marker_prefix long hprefix n)
  have hboundaryZero : boundary 0 = 0 := by
    apply short.cut_injective
    rw [hboundaryCut, long.cut_zero, short.cut_zero]
  have hboundaryStrict : StrictMono boundary := by
    intro left right hlr
    apply (short.cut_strictMono.lt_iff_lt).mp
    rw [hboundaryCut, hboundaryCut]
    exact long.cut_strictMono hlr
  let factorAt : Nat → Word (Fin shortRank) := fun n =>
    (short.derived.drop (boundary n)).take
      (boundary (n + 1) - boundary n)
  have hfactorAtDecodes : ∀ n : Nat,
      (factorAt n).flatMap short.blocks = long.blocks (long.derived n) := by
    intro n
    have hboundaryLe : boundary n ≤ boundary (n + 1) :=
      (hboundaryStrict (Nat.lt_succ_self n)).le
    have hdecode := short.flatMap_drop_take_derived
      (boundary n) (boundary (n + 1) - boundary n)
    change (factorAt n).flatMap short.blocks =
      (x.drop (short.cut (boundary n))).take
        ((factorAt n).flatMap short.blocks).length at hdecode
    have hcutAdd := short.cut_add (boundary n)
      (boundary (n + 1) - boundary n)
    have hboundaryAdd :
        boundary n + (boundary (n + 1) - boundary n) =
          boundary (n + 1) := Nat.add_sub_of_le hboundaryLe
    rw [hboundaryAdd] at hcutAdd
    change short.cut (boundary (n + 1)) = short.cut (boundary n) +
      ((factorAt n).flatMap short.blocks).length at hcutAdd
    have hlength : ((factorAt n).flatMap short.blocks).length =
        (long.blocks (long.derived n)).length := by
      rw [hboundaryCut, hboundaryCut, long.cut_succ] at hcutAdd
      omega
    rw [hboundaryCut, hlength] at hdecode
    exact hdecode.trans (long.block_at_cut n)
  let occurrence : Fin longRank → Nat := fun b =>
    Classical.choose (long.every_letter_occurs b)
  have hoccurrence : ∀ b : Fin longRank,
      long.derived (occurrence b) = b := by
    intro b
    exact Classical.choose_spec (long.every_letter_occurs b)
  let factor : Fin longRank → Word (Fin shortRank) := fun b =>
    factorAt (occurrence b)
  have hfactorDecodes : ∀ b : Fin longRank,
      (factor b).flatMap short.blocks = long.blocks b := by
    intro b
    change (factorAt (occurrence b)).flatMap short.blocks = long.blocks b
    rw [hfactorAtDecodes, hoccurrence]
  have hfactorAt : ∀ n : Nat, factor (long.derived n) = factorAt n := by
    intro n
    apply flatMap_returnWords_injective
      short.blocks_injective short.blocks_are_returns
    change (factor (long.derived n)).flatMap short.blocks =
      (factorAt n).flatMap short.blocks
    exact (hfactorDecodes (long.derived n)).trans
      (hfactorAtDecodes n).symm
  have hboundarySucc : ∀ n : Nat,
      boundary (n + 1) = boundary n + (factor (long.derived n)).length := by
    intro n
    have hboundaryLe : boundary n ≤ boundary (n + 1) :=
      (hboundaryStrict (Nat.lt_succ_self n)).le
    rw [hfactorAt]
    change boundary (n + 1) = boundary n +
      ((short.derived.drop (boundary n)).take
        (boundary (n + 1) - boundary n)).length
    simp only [Stream'.length_take]
    exact (Nat.add_sub_of_le hboundaryLe).symm
  have hderivedFactorAt : ∀ n : Nat,
      InfiniteFactorAt short.derived (factor (long.derived n)) (boundary n) := by
    intro n
    rw [hfactorAt]
    simp [InfiniteFactorAt, factorAt]
  exact ⟨{
    factor := factor
    factor_decodes := hfactorDecodes
    boundary := boundary
    boundary_zero := hboundaryZero
    boundary_cut := hboundaryCut
    boundary_succ := hboundarySucc
    derived_factor_at := hderivedFactorAt }⟩

/-- Injective short-block decoding makes the nested factor word unique. -/
theorem NestedReturnFactorization.factor_unique
    {delta : Type u} {x : InfiniteWord delta}
    {shortMarker longMarker : Word delta}
    {shortRank longRank : Nat}
    {short : ReturnDecomposition x shortMarker shortRank}
    {long : ReturnDecomposition x longMarker longRank}
    (nested : NestedReturnFactorization short long)
    (b : Fin longRank) (letters : Word (Fin shortRank))
    (hdecode : letters.flatMap short.blocks = long.blocks b) :
    letters = nested.factor b := by
  apply flatMap_returnWords_injective
    short.blocks_injective short.blocks_are_returns
  change letters.flatMap short.blocks =
    (nested.factor b).flatMap short.blocks
  exact hdecode.trans (nested.factor_decodes b).symm

/-- Every nested factor word is nonempty. -/
theorem NestedReturnFactorization.factor_ne_nil
    {delta : Type u} {x : InfiniteWord delta}
    {shortMarker longMarker : Word delta}
    {shortRank longRank : Nat}
    {short : ReturnDecomposition x shortMarker shortRank}
    {long : ReturnDecomposition x longMarker longRank}
    (nested : NestedReturnFactorization short long)
    (b : Fin longRank) : nested.factor b ≠ [] := by
  intro hempty
  have hdecode := nested.factor_decodes b
  rw [hempty] at hdecode
  simp only [List.flatMap_nil] at hdecode
  exact (long.blocks_are_returns b).2.1 hdecode.symm

/-- Nested boundaries are strictly increasing. -/
theorem NestedReturnFactorization.boundary_strictMono
    {delta : Type u} {x : InfiniteWord delta}
    {shortMarker longMarker : Word delta}
    {shortRank longRank : Nat}
    {short : ReturnDecomposition x shortMarker shortRank}
    {long : ReturnDecomposition x longMarker longRank}
    (nested : NestedReturnFactorization short long) :
    StrictMono nested.boundary := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [nested.boundary_succ]
  exact Nat.lt_add_of_pos_right
    (List.length_pos_of_ne_nil (nested.factor_ne_nil (long.derived n)))

/-- The powered return substitution carried by a primitive recurrent core. -/
structure PoweredReturnPresentation {delta : Type u}
    (growth : Real) (x : InfiniteWord delta) where
  exponent : Nat
  exponent_pos : 0 < exponent
  marker : Word delta
  rank : Nat
  decomposition : ReturnDecomposition x marker rank
  substitution : Substitution (Fin rank)
  seed : Fin rank
  prolongable : substitution.ProlongableOn seed
  generating : substitution.IsGeneratingLetter seed
  fixed : substitution.IsFixedPoint decomposition.derived
  primitive : ∃ iterate : Nat, 0 < iterate ∧
    ∀ a b : Fin rank, b ∈ substitution.iterateLetter iterate a
  every_letter_occurs : ∀ a : Fin rank,
    Substitution.OccursInInfiniteWord a decomposition.derived
  images_grow : LetterImagesGrow substitution seed
  dominant : IsDominantEigenvalue substitution.incidenceMatrix
    (growth ^ exponent)

/-- Internal certificate for the return-substitution construction.  The
short-marker and long-marker parsings are kept simultaneously: every long
return block has a unique word of short return blocks, those words tile the
short derived stream, and identifying the repeated derived system turns the
factorization into a substitution.  The last fields record exactly the
growth data transported through that intertwining. -/
private structure ReturnRefinement {delta : Type u}
    (growth : Real) (x : InfiniteWord delta) where
  exponent : Nat
  exponent_pos : 0 < exponent
  shortMarker : Word delta
  longMarker : Word delta
  shortRank : Nat
  longRank : Nat
  short : ReturnDecomposition x shortMarker shortRank
  long : ReturnDecomposition x longMarker longRank
  factor : Fin longRank → Word (Fin shortRank)
  factor_decodes : ∀ b : Fin longRank,
    (factor b).flatMap short.blocks = long.blocks b
  boundary : Nat → Nat
  boundary_zero : boundary 0 = 0
  boundary_succ : ∀ n : Nat,
    boundary (n + 1) = boundary n + (factor (long.derived n)).length
  derived_factor_at : ∀ n : Nat,
    InfiniteFactorAt short.derived (factor (long.derived n)) (boundary n)
  identify : Fin longRank ≃ Fin shortRank
  identified_derived : ∀ n : Nat,
    identify (long.derived n) = short.derived n
  returnSubstitution : Substitution (Fin shortRank)
  returnSubstitution_eq : ∀ a : Fin shortRank,
    returnSubstitution a = factor (identify.symm a)
  seed : Fin shortRank
  prolongable : returnSubstitution.ProlongableOn seed
  generating : returnSubstitution.IsGeneratingLetter seed
  primitive : ∃ iterate : Nat, 0 < iterate ∧
    ∀ a b : Fin shortRank,
      b ∈ returnSubstitution.iterateLetter iterate a
  every_letter_occurs : ∀ a : Fin shortRank,
    Substitution.OccursInInfiniteWord a short.derived
  images_grow : LetterImagesGrow returnSubstitution seed
  dominant_transport : IsDominantEigenvalue
    returnSubstitution.incidenceMatrix (growth ^ exponent)

/-- A factor word cannot be empty because it decodes to a nonempty long
return block. -/
private theorem ReturnRefinement.factor_ne_nil
    {delta : Type u} {growth : Real} {x : InfiniteWord delta}
    (refinement : ReturnRefinement growth x)
    (b : Fin refinement.longRank) : refinement.factor b ≠ [] := by
  intro hempty
  have hdecode := refinement.factor_decodes b
  rw [hempty] at hdecode
  simp only [List.flatMap_nil] at hdecode
  exact (refinement.long.blocks_are_returns b).2.1 hdecode.symm

/-- The decoding square in a return refinement is forced by the two defining
equations; it need not be supplied independently by the repeated-scale
construction. -/
private theorem ReturnRefinement.decode_intertwining
    {delta : Type u} {growth : Real} {x : InfiniteWord delta}
    (refinement : ReturnRefinement growth x) :
    ∀ a : Fin refinement.shortRank,
      (refinement.returnSubstitution a).flatMap refinement.short.blocks =
        refinement.long.blocks (refinement.identify.symm a) := by
  intro a
  rw [refinement.returnSubstitution_eq]
  exact refinement.factor_decodes (refinement.identify.symm a)

/-- Once the repeated long derived sequence has been identified with the
short one, its return-word factorization already forces the induced return
substitution to fix the short derived sequence. -/
private theorem ReturnRefinement.fixed
    {delta : Type u} {growth : Real} {x : InfiniteWord delta}
    (refinement : ReturnRefinement growth x) :
    refinement.returnSubstitution.IsFixedPoint refinement.short.derived := by
  have hboundaryLower : ∀ n : Nat, n ≤ refinement.boundary n := by
    intro n
    induction n with
    | zero => simp [refinement.boundary_zero]
    | succ n ih =>
        rw [refinement.boundary_succ]
        have hpositive : 0 <
            (refinement.factor (refinement.long.derived n)).length :=
          List.length_pos_of_ne_nil
            (refinement.factor_ne_nil (refinement.long.derived n))
        omega
  have hfiniteTiling : ∀ n : Nat,
      refinement.returnSubstitution.mapWord
          (refinement.short.derived.take n) =
        refinement.short.derived.take (refinement.boundary n) := by
    intro n
    induction n with
    | zero => simp [refinement.boundary_zero]
    | succ n ih =>
        have hidentified :
            refinement.identify.symm (refinement.short.derived n) =
              refinement.long.derived n := by
          rw [← refinement.identified_derived n]
          exact refinement.identify.symm_apply_apply _
        change refinement.identify.symm
            (Stream'.get refinement.short.derived n) =
          Stream'.get refinement.long.derived n at hidentified
        have hfactorAt := refinement.derived_factor_at n
        change
          (refinement.short.derived.drop (refinement.boundary n)).take
              (refinement.factor (refinement.long.derived n)).length =
            refinement.factor (refinement.long.derived n) at hfactorAt
        change
          (refinement.short.derived.drop (refinement.boundary n)).take
              (refinement.factor
                (Stream'.get refinement.long.derived n)).length =
            refinement.factor
              (Stream'.get refinement.long.derived n) at hfactorAt
        rw [Stream'.take_succ',
          Symbolic.Substitution.mapWord_append,
          Symbolic.Substitution.mapWord_cons,
          Symbolic.Substitution.mapWord_nil, List.append_nil, ih,
          refinement.returnSubstitution_eq, hidentified,
          refinement.boundary_succ, Stream'.take_add]
        change
          refinement.short.derived.take (refinement.boundary n) ++
              refinement.factor
                (Stream'.get refinement.long.derived n) =
            refinement.short.derived.take (refinement.boundary n) ++
              (refinement.short.derived.drop
                (refinement.boundary n)).take
                  (refinement.factor
                    (Stream'.get refinement.long.derived n)).length
        rw [hfactorAt]
  rw [Symbolic.Substitution.IsFixedPoint]
  funext position
  let count := position + 1
  have hposition : position < refinement.boundary count := by
    have := hboundaryLower count
    omega
  have hwordLength :
      (refinement.returnSubstitution.mapWord
          (refinement.short.derived.take count)).length =
        refinement.boundary count := by
    rw [hfiniteTiling]
    simp
  have hmapPrefix :
      (refinement.returnSubstitution.mapInfinite
          refinement.short.derived).take (refinement.boundary count) =
        refinement.returnSubstitution.mapWord
          (refinement.short.derived.take count) := by
    rw [← hwordLength]
    calc
      (refinement.returnSubstitution.mapInfinite
          refinement.short.derived).take
            (refinement.returnSubstitution.mapWord
              (refinement.short.derived.take count)).length =
          (refinement.returnSubstitution.mapInfinite
            (refinement.short.derived.take count ++ₛ
              refinement.short.derived.drop count)).take
                (refinement.returnSubstitution.mapWord
                  (refinement.short.derived.take count)).length := by
            rw [Stream'.append_take_drop]
      _ = (refinement.returnSubstitution.mapWord
              (refinement.short.derived.take count) ++ₛ
            refinement.returnSubstitution.mapInfinite
              (refinement.short.derived.drop count)).take
                (refinement.returnSubstitution.mapWord
                  (refinement.short.derived.take count)).length := by
            rw [refinement.returnSubstitution.mapInfinite_append_stream]
      _ = refinement.returnSubstitution.mapWord
              (refinement.short.derived.take count) := by
            simpa using Stream'.take_append_of_le_length
              (x := refinement.returnSubstitution.mapWord
                (refinement.short.derived.take count))
              (a := refinement.returnSubstitution.mapInfinite
                (refinement.short.derived.drop count))
              (n := (refinement.returnSubstitution.mapWord
                (refinement.short.derived.take count)).length) le_rfl
  have hprefix :
      (refinement.returnSubstitution.mapInfinite
          refinement.short.derived).take (refinement.boundary count) =
        refinement.short.derived.take (refinement.boundary count) :=
    hmapPrefix.trans (hfiniteTiling count)
  have hleftIndex : position <
      ((refinement.returnSubstitution.mapInfinite
        refinement.short.derived).take
          (refinement.boundary count)).length := by
    simpa using hposition
  have hrightIndex : position <
      (refinement.short.derived.take
        (refinement.boundary count)).length := by
    simpa using hposition
  have hleftGet := Stream'.take_get
    (a := refinement.returnSubstitution.mapInfinite
      refinement.short.derived)
    (m := position) (n := refinement.boundary count) hleftIndex
  have hrightGet := Stream'.take_get
    (a := refinement.short.derived)
    (m := position) (n := refinement.boundary count) hrightIndex
  change Stream'.get
      (refinement.returnSubstitution.mapInfinite
        refinement.short.derived) position =
    Stream'.get refinement.short.derived position
  rw [← hleftGet, ← hrightGet]
  rw [← Option.some_inj, ← List.getElem?_eq_getElem,
    ← List.getElem?_eq_getElem]
  exact congrArg (fun word => word[position]?) hprefix

end Symbolic

namespace Symbolic.LetterCoding

/-- Pointwise letter coding commutes with deleting a finite prefix. -/
theorem mapInfinite_drop
    {alpha beta : Type*} (coding : LetterCoding alpha beta)
    (word : InfiniteWord alpha) (cutoff : Nat) :
    coding.mapInfinite (word.drop cutoff) =
      (coding.mapInfinite word).drop cutoff := by
  rfl

end Symbolic.LetterCoding

namespace Symbolic.Substitution

universe u

/-- Reachability in the finite letter-image digraph. -/
def LetterReachable {delta : Type u} (sigma : Substitution delta)
    (source target : delta) : Prop :=
  sigma.OccursFrom source target

/-- Membership in the same strongly connected component. -/
def LettersStronglyConnected {delta : Type u} (sigma : Substitution delta)
    (a b : delta) : Prop :=
  LetterReachable sigma a b ∧ LetterReachable sigma b a

/-- Iteration distributes over concatenation of finite words. -/
@[simp] theorem iterateWord_nil_public {delta : Type u}
    (sigma : Substitution delta) (n : Nat) :
    sigma.iterateWord n [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterateWord_succ, ih, mapWord_nil]

theorem iterateWord_append_public {delta : Type u}
    (sigma : Substitution delta) (n : Nat) (left right : Word delta) :
    sigma.iterateWord n (left ++ right) =
      sigma.iterateWord n left ++ sigma.iterateWord n right := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [iterateWord_succ, ih, mapWord_append]

/-- Addition of iteration counts corresponds to composition. -/
theorem iterateWord_add_public {delta : Type u}
    (sigma : Substitution delta) (m n : Nat) (word : Word delta) :
    sigma.iterateWord (m + n) word =
      sigma.iterateWord m (sigma.iterateWord n word) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simpa only [Nat.succ_add, iterateWord_succ] using
        congrArg sigma.mapWord ih

/-- Substitution iteration preserves finite-word infixes. -/
theorem iterateWord_infix_public {delta : Type u}
    (sigma : Substitution delta) (n : Nat)
    {small large : Word delta} (hfactor : small <:+: large) :
    sigma.iterateWord n small <:+: sigma.iterateWord n large := by
  rcases hfactor with ⟨left, right, rfl⟩
  refine ⟨sigma.iterateWord n left, sigma.iterateWord n right, ?_⟩
  simp only [iterateWord_append_public, List.append_assoc]

/-- If a letter occurs in one iterate, every later image of that letter is
an infix of the correspondingly deeper image of the source letter. -/
theorem iterateLetter_infix_of_mem_iterate {delta : Type u}
    (sigma : Substitution delta) {source letter : delta}
    {first later : Nat}
    (hmem : letter ∈ sigma.iterateLetter first source) :
    sigma.iterateLetter later letter <:+:
      sigma.iterateLetter (later + first) source := by
  have hsingle : [letter] <:+: sigma.iterateLetter first source :=
    (List.singleton_infix_iff letter _).2 hmem
  have himage := sigma.iterateWord_infix_public later hsingle
  change sigma.iterateLetter later letter <:+:
    sigma.iterateWord later (sigma.iterateLetter first source) at himage
  change sigma.iterateWord later [letter] <:+:
    sigma.iterateWord (later + first) [source]
  rw [iterateWord_add_public]
  exact himage

/-- The largest length of a level-`n` letter image on a finite alphabet. -/
def maxIterateLength {delta : Type u} [Fintype delta]
    (sigma : Substitution delta) (n : Nat) : Nat :=
  Finset.univ.sup fun a : delta => (sigma.iterateLetter n a).length

theorem iterateLetter_length_le_maxIterateLength
    {delta : Type u} [Fintype delta]
    (sigma : Substitution delta) (n : Nat) (a : delta) :
    (sigma.iterateLetter n a).length ≤ sigma.maxIterateLength n := by
  exact Finset.le_sup (f := fun b : delta =>
    (sigma.iterateLetter n b).length) (Finset.mem_univ a)

theorem exists_length_eq_maxIterateLength
    {delta : Type u} [Fintype delta] [Nonempty delta]
    (sigma : Substitution delta) (n : Nat) :
    ∃ a : delta,
      (sigma.iterateLetter n a).length = sigma.maxIterateLength n := by
  rcases Finset.exists_mem_eq_sup Finset.univ
      (by simpa using (Finset.univ_nonempty :
        (Finset.univ : Finset delta).Nonempty))
      (fun a : delta => (sigma.iterateLetter n a).length) with
    ⟨a, _ha, hmax⟩
  exact ⟨a, hmax.symm⟩

@[simp] theorem maxIterateLength_zero
    {delta : Type u} [Fintype delta] [Nonempty delta]
    (sigma : Substitution delta) : sigma.maxIterateLength 0 = 1 := by
  obtain ⟨a, ha⟩ := sigma.exists_length_eq_maxIterateLength 0
  simpa using ha.symm

/-- A substituted finite word is at most its number of letters times the
largest substituted letter image. -/
theorem iterateWord_length_le_maxIterateLength
    {delta : Type u} [Fintype delta]
    (sigma : Substitution delta) (n : Nat) (word : Word delta) :
    (sigma.iterateWord n word).length ≤
      sigma.maxIterateLength n * word.length := by
  induction word with
  | nil =>
      have hempty : sigma.iterateWord n [] = [] := by
        induction n with
        | zero => rfl
        | succ n ih => simpa only [iterateWord_succ, ih, mapWord_nil]
      rw [hempty]
      simp
  | cons a word ih =>
      rw [show a :: word = [a] ++ word by rfl,
        iterateWord_append_public, List.length_append]
      change (sigma.iterateLetter n a).length +
          (sigma.iterateWord n word).length ≤ _
      calc
        (sigma.iterateLetter n a).length +
            (sigma.iterateWord n word).length ≤
            sigma.maxIterateLength n +
              sigma.maxIterateLength n * word.length :=
          Nat.add_le_add
            (sigma.iterateLetter_length_le_maxIterateLength n a) ih
        _ = sigma.maxIterateLength n * (word.length + 1) := by
          rw [Nat.mul_succ, Nat.add_comm]

/-- Nonerasing substitution never shortens a finite word. -/
theorem length_le_mapWord {delta : Type u}
    (sigma : Substitution delta) (word : Word delta) :
    word.length ≤ (sigma.mapWord word).length := by
  induction word with
  | nil => simp
  | cons a word ih =>
      rw [mapWord_cons, List.length_append, List.length_cons]
      have ha : 0 < (sigma a).length :=
        List.length_pos_of_ne_nil (sigma.image_ne_nil a)
      omega

/-- Consequently no finite substitution iterate shortens a word. -/
theorem length_le_iterateWord {delta : Type u}
    (sigma : Substitution delta) (n : Nat) (word : Word delta) :
    word.length ≤ (sigma.iterateWord n word).length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact ih.trans (sigma.length_le_mapWord (sigma.iterateWord n word))

/-- Maximal image lengths over a fixed additional number of substitution
steps grow by at most a fixed multiplicative factor. -/
theorem maxIterateLength_add_le
    {delta : Type u} [Fintype delta]
    (sigma : Substitution delta) (base extra : Nat) :
    sigma.maxIterateLength (base + extra) ≤
      sigma.maxIterateLength extra * sigma.maxIterateLength base := by
  apply Finset.sup_le
  intro a _ha
  have hlength := sigma.iterateWord_length_le_maxIterateLength extra
    (sigma.iterateLetter base a)
  have hbase := sigma.iterateLetter_length_le_maxIterateLength base a
  calc
    (sigma.iterateLetter (base + extra) a).length =
        (sigma.iterateWord extra (sigma.iterateLetter base a)).length := by
      change (sigma.iterateWord (base + extra) [a]).length =
        (sigma.iterateWord extra (sigma.iterateWord base [a])).length
      rw [Nat.add_comm, iterateWord_add_public]
    _ ≤ sigma.maxIterateLength extra *
          (sigma.iterateLetter base a).length := hlength
    _ ≤ sigma.maxIterateLength extra *
          sigma.maxIterateLength base := Nat.mul_le_mul_left _ hbase

/-- A primitive substitution fixed point is prolongable on its own first
letter as soon as one (hence every) letter has unbounded iterated images. -/
theorem prolongableOn_head_of_primitive_fixedPoint
    {delta : Type u} [Fintype delta]
    {sigma : Substitution delta} {x : InfiniteWord delta} {seed : delta}
    (hfixed : sigma.IsFixedPoint x)
    (hprimitive : ∃ iterate : Nat, 0 < iterate ∧
      ∀ a b : delta, b ∈ sigma.iterateLetter iterate a)
    (hgrow : LetterImagesGrow sigma seed) :
    sigma.ProlongableOn x.head := by
  have hhead : sigma.imageHead x.head = x.head := by
    have hzero := congrFun hfixed 0
    simpa using hzero
  have hlength : 1 < (sigma x.head).length := by
    by_contra hnot
    have hpositive : 0 < (sigma x.head).length :=
      List.length_pos_of_ne_nil (sigma.image_ne_nil x.head)
    have hone : (sigma x.head).length = 1 := by omega
    have htailLength : (sigma.imageTail x.head).length = 0 := by
      have himageLength := congrArg List.length
        (sigma.imageHead_cons_imageTail x.head)
      simp only [List.length_cons] at himageLength
      rw [hone] at himageLength
      omega
    have htail : sigma.imageTail x.head = [] :=
      List.eq_nil_of_length_eq_zero htailLength
    have himage : sigma x.head = [x.head] := by
      rw [← sigma.imageHead_cons_imageTail, hhead, htail]
    have hiterates : ∀ n : Nat,
        sigma.iterateLetter n x.head = [x.head] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [iterateLetter_succ, ih]
          simpa [himage]
    obtain ⟨primitiveLevel, _hprimitiveLevel, hcontains⟩ := hprimitive
    have hseedMem := hcontains x.head seed
    rw [hiterates primitiveLevel] at hseedMem
    have hseed : seed = x.head := by simpa using hseedMem
    obtain ⟨growthLevel, hgrowthLevel⟩ := hgrow 2
    rw [hseed, hiterates growthLevel] at hgrowthLevel
    simp at hgrowthLevel
  have htail : sigma.imageTail x.head ≠ [] := by
    intro hnil
    rw [← sigma.imageHead_cons_imageTail] at hlength
    simp [hnil] at hlength
  exact ⟨sigma.imageTail x.head, htail, by
    rw [← sigma.imageHead_cons_imageTail, hhead]⟩

/-- Every finite power fixes a substitution-fixed infinite word, including
the zeroth power. -/
theorem isFixedPoint_power_all {delta : Type u}
    {sigma : Substitution delta} {x : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint x) (n : Nat) :
    (sigma.power n).IsFixedPoint x := by
  cases n with
  | zero => exact mapInfinite_id x
  | succ n => exact isFixedPoint_power hfixed (Nat.succ_pos n)

/-- In a fixed point, substituting a finite input segment places it at the
cumulative length of the substituted input prefix preceding that segment. -/
theorem iterateWord_drop_take_at_fixed {delta : Type u}
    {sigma : Substitution delta} {x : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint x)
    (level start count : Nat) :
    InfiniteFactorAt x
      (sigma.iterateWord level ((x.drop start).take count))
      (sigma.iterateWord level (x.take start)).length := by
  let tau := sigma.power level
  let pref := tau.mapWord (x.take start)
  let segment := tau.mapWord ((x.drop start).take count)
  have hfixedTau : tau.IsFixedPoint x :=
    isFixedPoint_power_all hfixed level
  have hprefixSplit : pref ++ₛ tau.mapInfinite (x.drop start) = x := by
    calc
      pref ++ₛ tau.mapInfinite (x.drop start) =
          tau.mapInfinite (x.take start ++ₛ x.drop start) := by
        exact (tau.mapInfinite_append_stream _ _).symm
      _ = tau.mapInfinite x := by rw [Stream'.append_take_drop]
      _ = x := hfixedTau
  have hsegmentSplit :
      tau.mapInfinite (x.drop start) =
        segment ++ₛ tau.mapInfinite ((x.drop start).drop count) := by
    calc
      tau.mapInfinite (x.drop start) =
          tau.mapInfinite
            ((x.drop start).take count ++ₛ
              (x.drop start).drop count) := by
        rw [Stream'.append_take_drop]
      _ = segment ++ₛ
          tau.mapInfinite ((x.drop start).drop count) :=
        tau.mapInfinite_append_stream _ _
  have htail : x.drop pref.length = tau.mapInfinite (x.drop start) := by
    have hdropped := congrArg (fun stream : InfiniteWord delta =>
      stream.drop pref.length) hprefixSplit
    simpa [Stream'.drop_append_stream] using hdropped.symm
  have htaken :
      (tau.mapInfinite (x.drop start)).take segment.length = segment := by
    rw [hsegmentSplit]
    simpa using Stream'.take_append_of_le_length
      (x := segment)
      (a := tau.mapInfinite ((x.drop start).drop count))
      (n := segment.length) le_rfl
  have hcombined :
      (x.drop pref.length).take segment.length = segment :=
    (congrArg (fun stream : InfiniteWord delta =>
      stream.take segment.length) htail).trans htaken
  change (x.drop
      (sigma.iterateWord level (x.take start)).length).take
        (sigma.iterateWord level ((x.drop start).take count)).length =
      sigma.iterateWord level ((x.drop start).take count)
  simpa [tau, pref, segment, power_mapWord] using hcombined

/-- Reachability is reflexive. -/
theorem letterReachable_refl {delta : Type u}
    (sigma : Substitution delta) (a : delta) :
    LetterReachable sigma a a := by
  exact ⟨0, by simp [LetterReachable, OccursFrom, OccursInWord]⟩

/-- Reachability is transitive under concatenating substitution iterates. -/
theorem letterReachable_trans {delta : Type u}
    {sigma : Substitution delta} {a b c : delta}
    (hab : LetterReachable sigma a b)
    (hbc : LetterReachable sigma b c) :
    LetterReachable sigma a c := by
  change (∃ m : Nat, b ∈ sigma.iterateLetter m a) at hab
  change (∃ n : Nat, c ∈ sigma.iterateLetter n b) at hbc
  rcases hab with ⟨m, hm⟩
  rcases hbc with ⟨n, hn⟩
  rcases List.mem_iff_append.mp hm with ⟨left, right, hsplit⟩
  change ∃ iterate : Nat, c ∈ sigma.iterateLetter iterate a
  refine ⟨n + m, ?_⟩
  change c ∈ sigma.iterateWord (n + m) [a]
  rw [iterateWord_add_public sigma n m [a]]
  change c ∈ sigma.iterateWord n (sigma.iterateLetter m a)
  rw [hsplit, iterateWord_append_public,
    show b :: right = [b] ++ right by rfl,
    iterateWord_append_public]
  exact List.mem_append_right _ (List.mem_append_left _ hn)

/-- Membership in the substituted image of a finite word is witnessed by
one source letter of that word. -/
theorem mem_iterateWord_iff
    {delta : Type u} (sigma : Substitution delta)
    (level : Nat) (word : Word delta) (b : delta) :
    b ∈ sigma.iterateWord level word ↔
      ∃ a ∈ word, b ∈ sigma.iterateLetter level a := by
  induction word with
  | nil => simp [iterateWord_nil_public]
  | cons a word ih =>
      change b ∈ sigma.iterateWord level ([a] ++ word) ↔ _
      rw [iterateWord_append_public]
      simp [ih, iterateLetter]

/-- Exact-length reachability composes when iteration counts are added. -/
theorem mem_iterateLetter_add_iff
    {delta : Type u} (sigma : Substitution delta)
    (outer inner : Nat) (a b : delta) :
    b ∈ sigma.iterateLetter (outer + inner) a ↔
      ∃ middle ∈ sigma.iterateLetter inner a,
        b ∈ sigma.iterateLetter outer middle := by
  change b ∈ sigma.iterateWord (outer + inner) [a] ↔ _
  rw [iterateWord_add_public]
  exact sigma.mem_iterateWord_iff outer
    (sigma.iterateWord inner [a]) b

/-- The finite exact-length reachability relation of a substitution. -/
noncomputable def supportRelation
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    (sigma : Substitution delta) (level : Nat) :
    Finset (delta × delta) := by
  classical
  exact Finset.univ.filter fun pair =>
    pair.2 ∈ sigma.iterateLetter level pair.1

@[simp] theorem mem_supportRelation_iff
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    (sigma : Substitution delta) (level : Nat) (a b : delta) :
    (a, b) ∈ sigma.supportRelation level ↔
      b ∈ sigma.iterateLetter level a := by
  classical
  simp [supportRelation]

/-- Equality of exact-length reachability relations is preserved after
adding the same number of outer substitution steps. -/
theorem supportRelation_add_left_congr
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    (sigma : Substitution delta) {first second : Nat}
    (hrelation : sigma.supportRelation first =
      sigma.supportRelation second) (outer : Nat) :
    sigma.supportRelation (outer + first) =
      sigma.supportRelation (outer + second) := by
  classical
  apply Finset.ext
  rintro ⟨a, b⟩
  simp only [mem_supportRelation_iff,
    mem_iterateLetter_add_iff]
  have hpoint : ∀ source target : delta,
      target ∈ sigma.iterateLetter first source ↔
        target ∈ sigma.iterateLetter second source := by
    intro source target
    have hp := Finset.ext_iff.mp hrelation (source, target)
    simpa using hp
  constructor
  · rintro ⟨middle, hmiddle, hb⟩
    exact ⟨middle, (hpoint a middle).mp hmiddle, hb⟩
  · rintro ⟨middle, hmiddle, hb⟩
    exact ⟨middle, (hpoint a middle).mpr hmiddle, hb⟩

/-- Every finite nonerasing substitution has a positive power admitting a
primitive image-closed component.  The proof uses an idempotent power of the
finite support relation and a minimal nonempty invariant subset. -/
theorem exists_power_primitiveComponent_data
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    [Nonempty delta] (sigma : Substitution delta) :
    ∃ powerIndex : Nat, 0 < powerIndex ∧
      ∃ component : Set delta,
        component.Nonempty ∧
          (∀ a ∈ component,
            ∀ b ∈ (sigma.power powerIndex) a, b ∈ component) ∧
          ∃ iterate : Nat, 0 < iterate ∧
            ∀ a ∈ component, ∀ b ∈ component,
              b ∈ (sigma.power powerIndex).iterateLetter iterate a := by
  classical
  obtain ⟨first, second, hne, hrepeat⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun level : Nat => sigma.supportRelation level)
  obtain ⟨early, late, hearlyLate, hrelation⟩ :
      ∃ early late : Nat, early < late ∧
        sigma.supportRelation early = sigma.supportRelation late := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first, second, hlt, hrepeat⟩
    · exact ⟨second, first, hgt, hrepeat.symm⟩
  let period := late - early
  have hperiodPos : 0 < period := by
    dsimp only [period]
    omega
  have hlate : late = early + period := by
    dsimp only [period]
    omega
  have hbase : sigma.supportRelation early =
      sigma.supportRelation (early + period) := by
    rwa [← hlate]
  have hshift : ∀ start : Nat, early ≤ start →
      sigma.supportRelation start =
        sigma.supportRelation (start + period) := by
    intro start hstart
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hstart
    have h := sigma.supportRelation_add_left_congr hbase extra
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  let powerIndex := period * (early + 1)
  have hpowerPos : 0 < powerIndex := by
    dsimp only [powerIndex]
    exact Nat.mul_pos hperiodPos (Nat.succ_pos _)
  have hearlyPower : early ≤ powerIndex := by
    dsimp only [powerIndex]
    nlinarith
  have hmany : ∀ count : Nat,
      sigma.supportRelation powerIndex =
        sigma.supportRelation (powerIndex + period * count) := by
    intro count
    induction count with
    | zero => simp
    | succ count ih =>
        calc
          sigma.supportRelation powerIndex =
              sigma.supportRelation (powerIndex + period * count) := ih
          _ = sigma.supportRelation
              ((powerIndex + period * count) + period) := by
                apply hshift
                exact hearlyPower.trans
                  (Nat.le_add_right powerIndex (period * count))
          _ = sigma.supportRelation
              (powerIndex + period * (count + 1)) := by
                rw [Nat.mul_succ, Nat.add_assoc]
  have hidempotent :
      sigma.supportRelation (powerIndex + powerIndex) =
        sigma.supportRelation powerIndex := by
    have h := (hmany (early + 1)).symm
    simpa [powerIndex, Nat.mul_add, Nat.add_assoc] using h
  let imageSet : delta → Finset delta := fun a =>
    Finset.univ.filter fun b =>
      b ∈ sigma.iterateLetter powerIndex a
  have mem_imageSet (a b : delta) :
      b ∈ imageSet a ↔
        b ∈ sigma.iterateLetter powerIndex a := by
    simp [imageSet]
  let Candidate : Finset delta → Prop := fun component =>
    component.Nonempty ∧
      ∀ a ∈ component, ∀ b ∈ sigma.iterateLetter powerIndex a,
        b ∈ component
  have himageNonempty (a : delta) : (imageSet a).Nonempty := by
    obtain ⟨b, tail, hb⟩ := List.exists_cons_of_ne_nil
      (sigma.iterateLetter_ne_nil powerIndex a)
    refine ⟨b, (mem_imageSet a b).2 ?_⟩
    rw [hb]
    simp
  have himageClosed (a : delta) :
      ∀ b ∈ imageSet a,
        ∀ c ∈ sigma.iterateLetter powerIndex b,
          c ∈ imageSet a := by
    intro b hb c hc
    rw [mem_imageSet] at hb ⊢
    have hcomposed :
        c ∈ sigma.iterateLetter (powerIndex + powerIndex) a :=
      (sigma.mem_iterateLetter_add_iff powerIndex powerIndex a c).2
        ⟨b, hb, hc⟩
    have hpoint := Finset.ext_iff.mp hidempotent (a, c)
    simpa using hpoint.mp (by simpa using hcomposed)
  let initial : delta := Classical.choice (inferInstance : Nonempty delta)
  have hinitial : Candidate (imageSet initial) :=
    ⟨himageNonempty initial, himageClosed initial⟩
  let candidates : Set (Finset delta) := {component | Candidate component}
  have hcandidates : candidates.Nonempty :=
    ⟨imageSet initial, hinitial⟩
  obtain ⟨component, hcomponent, hminimal⟩ :=
    (Set.toFinite candidates).exists_minimal hcandidates
  have hcomponentCandidate : Candidate component := hcomponent
  have himageSubset (a : delta) (ha : a ∈ component) :
      imageSet a ⊆ component := by
    intro b hb
    exact hcomponentCandidate.2 a ha b ((mem_imageSet a b).1 hb)
  have hcomponentSubsetImage (a : delta) (ha : a ∈ component) :
      component ⊆ imageSet a := by
    have himageCandidate : Candidate (imageSet a) :=
      ⟨himageNonempty a, himageClosed a⟩
    exact hminimal himageCandidate (himageSubset a ha)
  refine ⟨powerIndex, hpowerPos, (component : Set delta), ?_⟩
  refine ⟨?_, ?_, 1, by omega, ?_⟩
  · exact hcomponentCandidate.1
  · intro a ha b hb
    rw [power_apply] at hb
    exact hcomponentCandidate.2 a ha b hb
  · intro a ha b hb
    have hmem : b ∈ sigma.iterateLetter powerIndex a :=
      (mem_imageSet a b).1 (hcomponentSubsetImage a ha hb)
    simpa [iterateLetter, iterateWord] using hmem

theorem lettersStronglyConnected_refl {delta : Type u}
    (sigma : Substitution delta) (a : delta) :
    LettersStronglyConnected sigma a a :=
  ⟨letterReachable_refl sigma a, letterReachable_refl sigma a⟩

theorem lettersStronglyConnected_symm {delta : Type u}
    {sigma : Substitution delta} {a b : delta}
    (h : LettersStronglyConnected sigma a b) :
    LettersStronglyConnected sigma b a :=
  ⟨h.2, h.1⟩

theorem lettersStronglyConnected_trans {delta : Type u}
    {sigma : Substitution delta} {a b c : delta}
    (hab : LettersStronglyConnected sigma a b)
    (hbc : LettersStronglyConnected sigma b c) :
    LettersStronglyConnected sigma a c :=
  ⟨letterReachable_trans hab.1 hbc.1,
    letterReachable_trans hbc.2 hab.2⟩

/-- The concrete equivalence class of a letter in the reachability graph. -/
noncomputable def strongComponent {delta : Type u}
    [Fintype delta] [DecidableEq delta]
    (sigma : Substitution delta) (a : delta) : Finset delta := by
  classical
  exact Finset.univ.filter fun b => LettersStronglyConnected sigma a b

@[simp] theorem mem_strongComponent_iff
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    (sigma : Substitution delta) (a b : delta) :
    b ∈ strongComponent sigma a ↔ LettersStronglyConnected sigma a b := by
  classical
  simp [strongComponent]

/-- A nonempty strongly connected collection of letters closed under images. -/
def IsPrimitiveComponent {delta : Type u} (sigma : Substitution delta)
    (component : Set delta) : Prop :=
  component.Nonempty ∧
    (∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component) ∧
    ∃ iterate : Nat, 0 < iterate ∧
      ∀ a ∈ component, ∀ b ∈ component,
        b ∈ sigma.iterateLetter iterate a

/-- Every finite nonerasing substitution has a positive power admitting a
primitive image-closed component. -/
theorem exists_power_primitiveComponent
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    [Nonempty delta] (sigma : Substitution delta) :
    ∃ powerIndex : Nat, 0 < powerIndex ∧
      ∃ component : Set delta,
        IsPrimitiveComponent (sigma.power powerIndex) component := by
  exact sigma.exists_power_primitiveComponent_data

/-- Positivity of a common incidence depth persists at all later depths. -/
theorem primitive_contains_at_later_early
    {delta : Type u} (sigma : Substitution delta)
    {depth later : Nat}
    (hcontains : ∀ a b : delta,
      b ∈ sigma.iterateLetter depth a)
    (hdepth : depth ≤ later) :
    ∀ a b : delta, b ∈ sigma.iterateLetter later a := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  intro a b
  have hnonempty := sigma.iterateLetter_ne_nil extra a
  obtain ⟨c, rest, hc⟩ := List.exists_cons_of_ne_nil hnonempty
  have hcMem : c ∈ sigma.iterateLetter extra a := by
    rw [hc]
    simp
  have hsingle : [c] <:+: sigma.iterateLetter extra a :=
    (List.singleton_infix_iff c _).2 hcMem
  have himage := sigma.iterateWord_infix_public depth hsingle
  have hbSmall : [b] <:+: sigma.iterateLetter depth c :=
    (List.singleton_infix_iff b _).2 (hcontains c b)
  have hbLarge := hbSmall.trans himage
  change [b] <:+:
    sigma.iterateWord depth (sigma.iterateWord extra [a]) at hbLarge
  rw [← iterateWord_add_public sigma depth extra [a]] at hbLarge
  exact (List.singleton_infix_iff b _).1 hbLarge

/-- An image-closed primitive component remains such after every positive
power of the ambient substitution. -/
theorem IsPrimitiveComponent.power
    {delta : Type u} {sigma : Substitution delta}
    {component : Set delta}
    (hcomponent : IsPrimitiveComponent sigma component)
    {powerIndex : Nat} (hpower : 0 < powerIndex) :
    IsPrimitiveComponent (sigma.power powerIndex) component := by
  have hclosedIterate : ∀ level : Nat,
      ∀ source ∈ component,
        ∀ target ∈ sigma.iterateLetter level source,
          target ∈ component := by
    intro level
    induction level with
    | zero =>
        intro source hsource target htarget
        have htargetEq : target = source := by simpa using htarget
        simpa [htargetEq] using hsource
    | succ level ih =>
        intro source hsource target htarget
        rw [iterateLetter_succ] at htarget
        have htarget' : target ∈
            sigma.iterateWord 1 (sigma.iterateLetter level source) := by
          simpa using htarget
        rw [sigma.mem_iterateWord_iff] at htarget'
        obtain ⟨middle, hmiddle, htarget'⟩ := htarget'
        exact hcomponent.2.1 middle
          (ih source hsource middle hmiddle) target (by
            simpa using htarget')
  refine ⟨hcomponent.1, ?_, ?_⟩
  · intro a ha b hb
    rw [power_apply] at hb
    exact hclosedIterate powerIndex a ha b hb
  · obtain ⟨depth, hdepth, hcontains⟩ := hcomponent.2.2
    refine ⟨depth, hdepth, ?_⟩
    intro a ha b hb
    rw [iterateLetter_power]
    have hle : depth ≤ powerIndex * depth := by nlinarith
    obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hle
    have hnonempty := sigma.iterateLetter_ne_nil extra a
    obtain ⟨c, rest, hc⟩ := List.exists_cons_of_ne_nil hnonempty
    have hcMem : c ∈ sigma.iterateLetter extra a := by
      rw [hc]
      simp
    have hcComponent : c ∈ component :=
      hclosedIterate extra a ha c hcMem
    have hsingle : [c] <:+: sigma.iterateLetter extra a :=
      (List.singleton_infix_iff c _).2 hcMem
    have himage := sigma.iterateWord_infix_public depth hsingle
    have hbSmall : [b] <:+: sigma.iterateLetter depth c :=
      (List.singleton_infix_iff b _).2
        (hcontains c hcComponent b hb)
    have hbLarge := hbSmall.trans himage
    change [b] <:+:
      sigma.iterateWord depth (sigma.iterateWord extra [a]) at hbLarge
    rw [← iterateWord_add_public sigma depth extra [a]] at hbLarge
    rw [hextra]
    exact (List.singleton_infix_iff b _).1 hbLarge

/-- If a letter occurring in an iterate has unbounded images, then so does
the source letter. -/
theorem letterImagesGrow_of_mem_iterate
    {delta : Type u} (sigma : Substitution delta)
    {source letter : delta} {first : Nat}
    (hmem : letter ∈ sigma.iterateLetter first source)
    (hgrow : LetterImagesGrow sigma letter) :
    LetterImagesGrow sigma source := by
  intro bound
  obtain ⟨later, hlater⟩ := hgrow bound
  refine ⟨later + first, ?_⟩
  exact hlater.trans
    (sigma.iterateLetter_infix_of_mem_iterate
      (later := later) hmem).length_le

/-- A letter which is non-growing remains non-growing for every positive
power. -/
theorem not_letterImagesGrow_power
    {delta : Type u} (sigma : Substitution delta) {letter : delta}
    (hnongrow : ¬ LetterImagesGrow sigma letter)
    {powerIndex : Nat} (hpower : 0 < powerIndex) :
    ¬ LetterImagesGrow (sigma.power powerIndex) letter := by
  intro hgrowPower
  apply hnongrow
  intro bound
  obtain ⟨level, hlevel⟩ := hgrowPower bound
  refine ⟨powerIndex * level, ?_⟩
  rw [iterateLetter_power] at hlevel
  exact hlevel

/-- Iterating a right-hand non-growing anchor preserves a nonempty
non-growing suffix around the distinguished growing letter. -/
theorem iterateLetter_anchor_right
    {delta : Type u} (sigma : Substitution delta)
    {a : delta} {left right : Word delta}
    (hright : right ≠ [])
    (hnongrow : ∀ b ∈ right, ¬ LetterImagesGrow sigma b)
    (himage : sigma a = left ++ a :: right) :
    ∀ level : Nat, 0 < level →
      ∃ newLeft newRight : Word delta,
        newRight ≠ [] ∧
          (∀ b ∈ newRight, ¬ LetterImagesGrow sigma b) ∧
          sigma.iterateLetter level a =
            newLeft ++ a :: newRight := by
  intro level hlevel
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hlevel)
  induction previous with
  | zero =>
      exact ⟨left, right, hright, hnongrow,
        by simpa [iterateLetter, iterateWord] using himage⟩
  | succ previous ih =>
      obtain ⟨oldLeft, oldRight, holdRight, holdNongrow,
        holdImage⟩ := ih (Nat.succ_pos _)
      let newLeft := sigma.mapWord oldLeft ++ left
      let newRight := right ++ sigma.mapWord oldRight
      have hnewRight : newRight ≠ [] :=
        List.append_ne_nil_of_left_ne_nil hright _
      have hnewNongrow : ∀ b ∈ newRight,
          ¬ LetterImagesGrow sigma b := by
        intro b hb
        simp only [newRight, List.mem_append] at hb
        rcases hb with hb | hb
        · exact hnongrow b hb
        · rw [mapWord] at hb
          obtain ⟨source, hsource, hb⟩ := List.mem_flatMap.mp hb
          intro hbgrow
          exact holdNongrow source hsource
            (sigma.letterImagesGrow_of_mem_iterate
              (first := 1) (by simpa using hb) hbgrow)
      refine ⟨newLeft, newRight, hnewRight, hnewNongrow, ?_⟩
      rw [iterateLetter_succ, holdImage, mapWord_append,
        mapWord_cons, himage]
      simp [newLeft, newRight, List.append_assoc]

/-- Left-hand version of `iterateLetter_anchor_right`. -/
theorem iterateLetter_anchor_left
    {delta : Type u} (sigma : Substitution delta)
    {a : delta} {left right : Word delta}
    (hleft : left ≠ [])
    (hnongrow : ∀ b ∈ left, ¬ LetterImagesGrow sigma b)
    (himage : sigma a = left ++ a :: right) :
    ∀ level : Nat, 0 < level →
      ∃ newLeft newRight : Word delta,
        newLeft ≠ [] ∧
          (∀ b ∈ newLeft, ¬ LetterImagesGrow sigma b) ∧
          sigma.iterateLetter level a =
            newLeft ++ a :: newRight := by
  intro level hlevel
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hlevel)
  induction previous with
  | zero =>
      exact ⟨left, right, hleft, hnongrow,
        by simpa [iterateLetter, iterateWord] using himage⟩
  | succ previous ih =>
      obtain ⟨oldLeft, oldRight, holdLeft, holdNongrow,
        holdImage⟩ := ih (Nat.succ_pos _)
      let newLeft := sigma.mapWord oldLeft ++ left
      let newRight := right ++ sigma.mapWord oldRight
      have hnewLeft : newLeft ≠ [] := by
        apply List.append_ne_nil_of_right_ne_nil
        exact hleft
      have hnewNongrow : ∀ b ∈ newLeft,
          ¬ LetterImagesGrow sigma b := by
        intro b hb
        simp only [newLeft, List.mem_append] at hb
        rcases hb with hb | hb
        · rw [mapWord] at hb
          obtain ⟨source, hsource, hb⟩ := List.mem_flatMap.mp hb
          intro hbgrow
          exact holdNongrow source hsource
            (sigma.letterImagesGrow_of_mem_iterate
              (first := 1) (by simpa using hb) hbgrow)
        · exact hnongrow b hb
      refine ⟨newLeft, newRight, hnewLeft, hnewNongrow, ?_⟩
      rw [iterateLetter_succ, holdImage, mapWord_append,
        mapWord_cons, himage]
      simp [newLeft, newRight, List.append_assoc]

/-- Restrict a substitution to an arbitrary image-closed set of letters. -/
def restrictToClosed {delta : Type u} (sigma : Substitution delta)
    (component : Set delta)
    (hclosed : ∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component) :
    Substitution component where
  image a := (sigma a.1).attach.map fun b =>
    ⟨b.1, hclosed a.1 a.2 b.1 b.2⟩
  image_ne_nil a := by
    apply List.ne_nil_of_length_pos
    simpa using List.length_pos_of_ne_nil (sigma.image_ne_nil a.1)

@[simp] theorem restrictToClosed_image_values
    {delta : Type u} (sigma : Substitution delta)
    (component : Set delta)
    (hclosed : ∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component)
    (a : component) :
    ((sigma.restrictToClosed component hclosed) a).map Subtype.val =
      sigma a.1 := by
  simp only [restrictToClosed, List.map_map]
  change ((sigma a.1).attach.map fun b => b.1) = sigma a.1
  exact List.attach_map_subtype_val _

/-- Forgetting component membership commutes with substitution of a finite
word. -/
theorem restrictToClosed_mapWord_values
    {delta : Type u} (sigma : Substitution delta)
    (component : Set delta)
    (hclosed : ∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component)
    (word : Word component) :
    ((sigma.restrictToClosed component hclosed).mapWord word).map
        Subtype.val =
      sigma.mapWord (word.map Subtype.val) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      simp only [mapWord_cons, List.map_append, List.map_cons, ih,
        restrictToClosed_image_values]

/-- Forgetting component membership commutes with every finite iterate. -/
theorem restrictToClosed_iterateWord_values
    {delta : Type u} (sigma : Substitution delta)
    (component : Set delta)
    (hclosed : ∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component)
    (iterate : Nat) (word : Word component) :
    ((sigma.restrictToClosed component hclosed).iterateWord iterate word).map
        Subtype.val =
      sigma.iterateWord iterate (word.map Subtype.val) := by
  induction iterate with
  | zero => rfl
  | succ iterate ih =>
      rw [iterateWord_succ, iterateWord_succ,
        restrictToClosed_mapWord_values, ih]

@[simp] theorem restrictToClosed_iterateLetter_values
    {delta : Type u} (sigma : Substitution delta)
    (component : Set delta)
    (hclosed : ∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component)
    (iterate : Nat) (a : component) :
    ((sigma.restrictToClosed component hclosed).iterateLetter iterate a).map
        Subtype.val =
      sigma.iterateLetter iterate a.1 := by
  simpa [iterateLetter] using
    sigma.restrictToClosed_iterateWord_values component hclosed iterate [a]

/-- A primitive component becomes a primitive substitution on its subtype. -/
theorem restrictToClosed_primitive
    {delta : Type u} {sigma : Substitution delta}
    {component : Set delta}
    (hcomponent : IsPrimitiveComponent sigma component) :
    ∃ iterate : Nat, 0 < iterate ∧
      ∀ a b : component,
        b ∈ (sigma.restrictToClosed component hcomponent.2.1).iterateLetter
          iterate a := by
  obtain ⟨iterate, hiterate, hcontains⟩ := hcomponent.2.2
  refine ⟨iterate, hiterate, ?_⟩
  intro a b
  have hvalue : b.1 ∈ sigma.iterateLetter iterate a.1 :=
    hcontains a.1 a.2 b.1 b.2
  have hmapped : b.1 ∈
      ((sigma.restrictToClosed component hcomponent.2.1).iterateLetter
        iterate a).map Subtype.val := by
    rw [restrictToClosed_iterateLetter_values]
    exact hvalue
  rcases List.mem_map.mp hmapped with ⟨c, hc, hvalueEq⟩
  have hcb : c = b := Subtype.ext hvalueEq
  simpa [hcb] using hc

/-- Restriction to a closed component preserves unbounded image growth. -/
theorem restrictToClosed_letterImagesGrow
    {delta : Type u} {sigma : Substitution delta}
    {component : Set delta}
    (hclosed : ∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component)
    (a : component) (hgrow : LetterImagesGrow sigma a.1) :
    LetterImagesGrow (sigma.restrictToClosed component hclosed) a := by
  intro bound
  obtain ⟨iterate, hiterate⟩ := hgrow bound
  refine ⟨iterate, ?_⟩
  have hlength := congrArg List.length
    (sigma.restrictToClosed_iterateLetter_values
      component hclosed iterate a)
  simp only [List.length_map] at hlength
  rwa [hlength]

/-- Exact letter-metric scaling is preserved by restriction to an
image-closed alphabet. -/
theorem restrictToClosed_scalesLetterLengths
    {alpha : Type*} (sigma : Substitution alpha)
    (component : Set alpha)
    (hclosed : ∀ a ∈ component, ∀ b ∈ sigma a, b ∈ component)
    (length : alpha → ℝ) (scale : ℝ)
    (hscale : SubstitutionScalesLetterLengths sigma length scale) :
    SubstitutionScalesLetterLengths
      (sigma.restrictToClosed component hclosed)
      (fun a : component => length a.1) scale := by
  intro a
  have hvalues := sigma.restrictToClosed_image_values
    component hclosed a
  have hmetric :
      wordMetricLength (fun b : component => length b.1)
          ((sigma.restrictToClosed component hclosed) a) =
        wordMetricLength length
          (((sigma.restrictToClosed component hclosed) a).map Subtype.val) := by
    simp [wordMetricLength]
  rw [hmetric, hvalues]
  exact hscale a.1

/-- Exact letter-metric scaling is invariant under a bijective alphabet
relabeling. -/
theorem relabel_scalesLetterLengths
    {alpha beta : Type*} (equiv : alpha ≃ beta)
    (sigma : Substitution alpha) (length : alpha → ℝ) (scale : ℝ)
    (hscale : SubstitutionScalesLetterLengths sigma length scale) :
    SubstitutionScalesLetterLengths (sigma.relabel equiv)
      (fun b : beta => length (equiv.symm b)) scale := by
  intro b
  rw [relabel_apply]
  have hmetric :
      wordMetricLength (fun c : beta => length (equiv.symm c))
          ((sigma (equiv.symm b)).map equiv) =
        wordMetricLength length (sigma (equiv.symm b)) := by
    simp [wordMetricLength, List.map_map, Function.comp_def]
  rw [hmetric, hscale]

/-- Once one common iterate of a nonerasing substitution contains every
letter in every image, the same is true at every later depth. -/
theorem primitive_contains_at_later
    {delta : Type u} (sigma : Substitution delta)
    {depth later : Nat}
    (hcontains : ∀ a b : delta,
      b ∈ sigma.iterateLetter depth a)
    (hdepth : depth ≤ later) :
    ∀ a b : delta, b ∈ sigma.iterateLetter later a := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  intro a b
  have hnonempty := sigma.iterateLetter_ne_nil extra a
  obtain ⟨c, rest, hc⟩ := List.exists_cons_of_ne_nil hnonempty
  have hcMem : c ∈ sigma.iterateLetter extra a := by
    rw [hc]
    simp
  have hsingle : [c] <:+: sigma.iterateLetter extra a :=
    (List.singleton_infix_iff c _).2 hcMem
  have himage := sigma.iterateWord_infix_public depth hsingle
  have hbSmall : [b] <:+: sigma.iterateLetter depth c :=
    (List.singleton_infix_iff b _).2 (hcontains c b)
  have hbLarge := hbSmall.trans himage
  change [b] <:+:
    sigma.iterateWord depth (sigma.iterateWord extra [a]) at hbLarge
  rw [← iterateWord_add_public sigma depth extra [a]] at hbLarge
  exact (List.singleton_infix_iff b _).1 hbLarge

/-- Every positive power of a primitive nonerasing substitution is again
primitive. -/
theorem primitive_power
    {delta : Type u} (sigma : Substitution delta)
    (hprimitive : ∃ depth : Nat, 0 < depth ∧
      ∀ a b : delta, b ∈ sigma.iterateLetter depth a)
    {powerIndex : Nat} (hpower : 0 < powerIndex) :
    ∃ depth : Nat, 0 < depth ∧
      ∀ a b : delta,
        b ∈ (sigma.power powerIndex).iterateLetter depth a := by
  obtain ⟨depth, hdepth, hcontains⟩ := hprimitive
  refine ⟨depth, hdepth, ?_⟩
  intro a b
  rw [iterateLetter_power]
  apply sigma.primitive_contains_at_later hcontains
  nlinarith

/-- Primitivity is invariant under a bijective relabeling of the alphabet. -/
theorem relabel_primitive
    {delta epsilon : Type*} (equiv : delta ≃ epsilon)
    (sigma : Substitution delta)
    (hprimitive : ∃ depth : Nat, 0 < depth ∧
      ∀ a b : delta, b ∈ sigma.iterateLetter depth a) :
    ∃ depth : Nat, 0 < depth ∧
      ∀ a b : epsilon,
        b ∈ (sigma.relabel equiv).iterateLetter depth a := by
  obtain ⟨depth, hdepth, hcontains⟩ := hprimitive
  refine ⟨depth, hdepth, ?_⟩
  intro a b
  have hiter := sigma.relabel_iterateLetter equiv depth (equiv.symm a)
  rw [equiv.apply_symm_apply] at hiter
  rw [hiter]
  exact List.mem_map.mpr ⟨equiv.symm b,
    hcontains (equiv.symm a) (equiv.symm b),
    equiv.apply_symm_apply b⟩

/-- Unbounded image growth is invariant under bijective relabeling. -/
theorem relabel_letterImagesGrow
    {delta epsilon : Type*} (equiv : delta ≃ epsilon)
    (sigma : Substitution delta) {seed : delta}
    (hgrow : LetterImagesGrow sigma seed) :
    LetterImagesGrow (sigma.relabel equiv) (equiv seed) := by
  intro bound
  obtain ⟨depth, hdepth⟩ := hgrow bound
  refine ⟨depth, ?_⟩
  rw [sigma.relabel_iterateLetter equiv]
  simpa using hdepth

/-- Pointwise relabeling of an infinite word, restated here because this file
is checked directly rather than through a rebuilt `SymbolicDefs` olean. -/
def relabelInfiniteWordPublic
    {delta epsilon : Type*} (equiv : delta ≃ epsilon)
    (word : InfiniteWord delta) : InfiniteWord epsilon :=
  fun position => equiv (word position)

/-- Relabeling commutes with infinite substitution. -/
theorem relabel_mapInfinite_public
    {delta epsilon : Type*} (equiv : delta ≃ epsilon)
    (sigma : Substitution delta) (word : InfiniteWord delta) :
    relabelInfiniteWordPublic equiv (sigma.mapInfinite word) =
      (sigma.relabel equiv).mapInfinite
        (relabelInfiniteWordPublic equiv word) := by
  let coding : LetterCoding delta epsilon := ⟨equiv⟩
  have h := LetterCoding.mapInfinite_substitution coding sigma
    (sigma.relabel equiv)
    (fun a => by
      simpa [coding, LetterCoding.mapWord] using
        (sigma.relabel_apply_equiv equiv a).symm) word
  simpa [coding, relabelInfiniteWordPublic,
    LetterCoding.mapInfinite] using h

/-- The fixed-point equation is invariant under pointwise relabeling. -/
theorem relabel_isFixedPoint_public_iff
    {delta epsilon : Type*} (equiv : delta ≃ epsilon)
    (sigma : Substitution delta) (word : InfiniteWord delta) :
    (sigma.relabel equiv).IsFixedPoint
        (relabelInfiniteWordPublic equiv word) ↔
      sigma.IsFixedPoint word := by
  constructor
  · intro hfixed
    apply Stream'.ext
    intro position
    apply equiv.injective
    have hposition := congrFun
      (relabel_mapInfinite_public equiv sigma word) position
    rw [hfixed] at hposition
    exact hposition
  · intro hfixed
    rw [IsFixedPoint,
      ← relabel_mapInfinite_public equiv sigma word, hfixed]

/-- The first letter of an iterated image is obtained by iterating the
first-letter map.  The cons form is more useful than a statement involving
`List.head`, since it also records the required nonemptiness. -/
theorem iterateLetter_eq_headIterate_cons
    {delta : Type u} (sigma : Substitution delta) (iterate : Nat)
    (a : delta) :
    ∃ tail : Word delta,
      sigma.iterateLetter iterate a =
        (sigma.imageHead^[iterate] a) :: tail := by
  induction iterate with
  | zero => exact ⟨[], rfl⟩
  | succ iterate ih =>
      obtain ⟨tail, htail⟩ := ih
      rw [iterateLetter_succ, htail, mapWord_cons,
        ← sigma.imageHead_cons_imageTail]
      refine ⟨sigma.imageTail (sigma.imageHead^[iterate] a) ++
        sigma.mapWord tail, ?_⟩
      simp only [Function.iterate_succ_apply']
      rfl

/-- On a finite alphabet, if every letter image grows without bound, some
positive substitution power is prolongable on a letter. -/
theorem exists_prolongable_power_of_all_letters_grow
    {delta : Type u} [Finite delta] [Nonempty delta]
    (sigma : Substitution delta)
    (hgrow : ∀ a : delta, LetterImagesGrow sigma a) :
    ∃ powerIndex : Nat, ∃ seed : delta, 0 < powerIndex ∧
      (sigma.power powerIndex).ProlongableOn seed := by
  classical
  let initial : delta := Classical.choice (inferInstance : Nonempty delta)
  obtain ⟨m, n, hmn, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun level : Nat => sigma.imageHead^[level] initial)
  have horient :
      ∃ early late : Nat, early < late ∧
        sigma.imageHead^[early] initial =
          sigma.imageHead^[late] initial := by
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact ⟨m, n, hlt, heq⟩
    · exact ⟨n, m, hgt, heq.symm⟩
  obtain ⟨early, late, hearlyLate, heqHead⟩ := horient
  let period := late - early
  let seed := sigma.imageHead^[early] initial
  have hperiodPos : 0 < period := by
    dsimp only [period]
    omega
  have hperiodic : sigma.imageHead^[period] seed = seed := by
    dsimp only [period, seed]
    calc
      sigma.imageHead^[late - early]
          (sigma.imageHead^[early] initial) =
          sigma.imageHead^[(late - early) + early] initial := by
            rw [Function.iterate_add_apply]
      _ = sigma.imageHead^[late] initial := by
            congr 2
            omega
      _ = sigma.imageHead^[early] initial := heqHead.symm
  obtain ⟨growthLevel, hgrowthLevel⟩ := hgrow seed 2
  let multiplier := growthLevel + 1
  let powerIndex := period * multiplier
  have hpowerPos : 0 < powerIndex := by
    dsimp only [powerIndex, multiplier]
    exact Nat.mul_pos hperiodPos (Nat.succ_pos _)
  have hlevelPower : growthLevel ≤ powerIndex := by
    dsimp only [powerIndex, multiplier]
    nlinarith
  have hperiodicPower :
      sigma.imageHead^[powerIndex] seed = seed := by
    have hp : Function.IsPeriodicPt sigma.imageHead period seed := hperiodic
    exact hp.mul_const multiplier
  have hlengthPower :
      2 ≤ (sigma.iterateLetter powerIndex seed).length := by
    obtain ⟨extra, hpowerEq⟩ := Nat.exists_eq_add_of_le hlevelPower
    have hlength :
        (sigma.iterateLetter growthLevel seed).length ≤
          (sigma.iterateLetter (growthLevel + extra) seed).length := by
      change (sigma.iterateWord growthLevel [seed]).length ≤
        (sigma.iterateWord (growthLevel + extra) [seed]).length
      rw [Nat.add_comm, iterateWord_add_public]
      exact sigma.length_le_iterateWord extra
        (sigma.iterateWord growthLevel [seed])
    rw [hpowerEq]
    exact hgrowthLevel.trans hlength
  obtain ⟨tail, htail⟩ :=
    sigma.iterateLetter_eq_headIterate_cons powerIndex seed
  rw [hperiodicPower] at htail
  have htailNonempty : tail ≠ [] := by
    intro hnil
    rw [htail, hnil] at hlengthPower
    simp at hlengthPower
  refine ⟨powerIndex, seed, hpowerPos, tail, htailNonempty, ?_⟩
  rw [power_apply, htail]

/-- Unbounded image growth survives every positive substitution power; no
prolongability assumption is needed for this monotonicity statement. -/
theorem letterImagesGrow_power_of_positive
    {delta : Type u} (sigma : Substitution delta) {seed : delta}
    (hgrow : LetterImagesGrow sigma seed)
    {powerIndex : Nat} (hpower : 0 < powerIndex) :
    LetterImagesGrow (sigma.power powerIndex) seed := by
  intro bound
  obtain ⟨level, hlevel⟩ := hgrow bound
  refine ⟨level, ?_⟩
  rw [iterateLetter_power]
  have hle : level ≤ powerIndex * level := by nlinarith
  obtain ⟨extra, hpowerLevel⟩ := Nat.exists_eq_add_of_le hle
  rw [hpowerLevel, Nat.add_comm]
  change bound ≤
    (sigma.iterateWord (extra + level) [seed]).length
  rw [iterateWord_add_public]
  exact hlevel.trans
    (sigma.length_le_iterateWord extra
      (sigma.iterateWord level [seed]))

/-- Recurrence transfers from a word `y` to `x` once arbitrarily long
prefixes of `y` occur as finite factors of `x`. -/
theorem recurrentFactor_of_all_prefixes_factor
    {delta : Type u} {x y : InfiniteWord delta} {word : Word delta}
    (hrecurrent : IsRecurrentFactor y word)
    (hprefix : ∀ length : Nat, IsInfiniteFactor x (y.take length)) :
    IsRecurrentFactor x word := by
  intro cutoff
  obtain ⟨offset, hoffset, hwordAt⟩ := hrecurrent cutoff
  let ambient := y.take (offset + word.length)
  obtain ⟨start, hambientAt⟩ := hprefix (offset + word.length)
  have hambientAtY : InfiniteFactorAt y ambient 0 := by
    simp [InfiniteFactorAt, ambient]
  have hfinite : FiniteFactorAt ambient word offset :=
    finiteFactorAt_of_nested_infiniteFactorAt hambientAtY
      (by simpa using hwordAt) (by simp [ambient])
  exact ⟨start + offset, hoffset.trans (Nat.le_add_left _ _),
    hambientAt.of_finiteFactorAt hfinite⟩

/-- Uniform exponential bounds on the iterated images in one component. -/
def HasExponentialGrowthOn {delta : Type u} (sigma : Substitution delta)
    (component : Set delta) (growth : Real) : Prop :=
  ∃ lower upper : Real, 0 < lower ∧ 0 < upper ∧
    ∀ a ∈ component, ∀ n : Nat,
      lower * growth ^ n ≤ (sigma.iterateLetter n a).length ∧
      (sigma.iterateLetter n a).length ≤ upper * growth ^ n

/-- A positive finite letter metric which scales exactly by `scale` gives
uniform exponential upper and lower bounds for the ordinary lengths of all
letter images. -/
theorem hasExponentialGrowthOn_of_metric_scales
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    (sigma : Symbolic.Substitution alpha) (length : alpha → ℝ)
    (scale : ℝ) (hlength : ∀ a, 0 < length a)
    (hscale : SubstitutionScalesLetterLengths sigma length scale)
    (hscalePos : 0 < scale) :
    HasExponentialGrowthOn sigma Set.univ scale := by
  classical
  let values : Finset ℝ := Finset.univ.image length
  have hvalues : values.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  let minLength : ℝ := values.min' hvalues
  have hminPos : 0 < minLength := by
    have hmem : minLength ∈ values := Finset.min'_mem values hvalues
    rcases Finset.mem_image.mp hmem with ⟨a, _ha, haeq⟩
    rw [← haeq]
    exact hlength a
  have hminLe : ∀ a : alpha, minLength ≤ length a := by
    intro a
    exact Finset.min'_le values (length a)
      (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  let total : ℝ := ∑ a : alpha, length a
  have hlengthLeTotal : ∀ a : alpha, length a ≤ total := by
    intro a
    dsimp only [total]
    exact Finset.single_le_sum (fun b _hb => (hlength b).le)
      (Finset.mem_univ a)
  let initial : alpha := Classical.choice inferInstance
  have htotalPos : 0 < total :=
    (hlength initial).trans_le (hlengthLeTotal initial)
  have hmetricLower : ∀ word : Symbolic.Word alpha,
      (word.length : ℝ) * minLength ≤ wordMetricLength length word := by
    intro word
    induction word with
    | nil => simp [wordMetricLength]
    | cons a word ih =>
        simp only [wordMetricLength, List.map_cons, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        have ha := hminLe a
        have ih' : (word.length : ℝ) * minLength ≤
            (word.map length).sum := by
          simpa [wordMetricLength] using ih
        nlinarith
  have hmetricUpper : ∀ word : Symbolic.Word alpha,
      wordMetricLength length word ≤ (word.length : ℝ) * total := by
    intro word
    induction word with
    | nil => simp [wordMetricLength]
    | cons a word ih =>
        simp only [wordMetricLength, List.map_cons, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        have ha := hlengthLeTotal a
        have ih' : (word.map length).sum ≤
            (word.length : ℝ) * total := by
          simpa [wordMetricLength] using ih
        nlinarith
  refine ⟨minLength / total, total / minLength,
    div_pos hminPos htotalPos, div_pos htotalPos hminPos, ?_⟩
  intro a _ha n
  let word := sigma.iterateLetter n a
  have hmetric : wordMetricLength length word = scale ^ n * length a := by
    have hp := sigma.scalesLetterLengths_power hscale n a
    simpa [word, Symbolic.Substitution.power_apply] using hp
  have hpowNonneg : 0 ≤ scale ^ n := pow_nonneg hscalePos.le _
  have hlowerMetric : minLength * scale ^ n ≤
      wordMetricLength length word := by
    rw [hmetric]
    nlinarith [hminLe a]
  have hlowerCombined : minLength * scale ^ n ≤
      (word.length : ℝ) * total :=
    hlowerMetric.trans (hmetricUpper word)
  have hlower : minLength / total * scale ^ n ≤
      (word.length : ℝ) := by
    calc
      minLength / total * scale ^ n =
          (minLength * scale ^ n) / total := by ring
      _ ≤ (word.length : ℝ) :=
        (div_le_iff₀ htotalPos).2 hlowerCombined
  have hupperMetric : (word.length : ℝ) * minLength ≤
      scale ^ n * total := by
    calc
      (word.length : ℝ) * minLength ≤
          wordMetricLength length word := hmetricLower word
      _ = scale ^ n * length a := hmetric
      _ ≤ scale ^ n * total :=
        mul_le_mul_of_nonneg_left (hlengthLeTotal a) hpowNonneg
  have hupper : (word.length : ℝ) ≤
      total / minLength * scale ^ n := by
    calc
      (word.length : ℝ) ≤ (scale ^ n * total) / minLength :=
        (le_div_iff₀ hminPos).2 hupperMetric
      _ = total / minLength * scale ^ n := by ring
  exact ⟨by simpa [word] using hlower, by simpa [word] using hupper⟩

/-- A positive power with a primitive component at the dominant growth and
with every source letter growing. -/
def HasGoodPower {delta : Type u} (sigma : Substitution delta)
    (growth : Real) : Prop :=
  ∃ powerIndex : Nat, 0 < powerIndex ∧
    ∃ component : Set delta,
      IsPrimitiveComponent (sigma.power powerIndex) component ∧
      HasExponentialGrowthOn (sigma.power powerIndex) component
        (growth ^ powerIndex) ∧
      ∀ a : delta, LetterImagesGrow (sigma.power powerIndex) a

/-- The canonical tail hidden inside an arbitrary all-letter fixed point.
The prefix before `cutoff` consists of singleton-image letters; after it the
fixed point starts on a prolongable generating letter. -/
structure EventualCanonicalTail {delta : Type u}
    (sigma : Substitution delta) (fixedWord : InfiniteWord delta) where
  cutoff : Nat
  inert_prefix : sigma.mapWord (fixedWord.take cutoff) = fixedWord.take cutoff
  tail_fixed : sigma.IsFixedPoint (fixedWord.drop cutoff)
  tail_prolongable : sigma.ProlongableOn (fixedWord cutoff)
  tail_generating : sigma.IsGeneratingLetter (fixedWord cutoff)
  iterates_are_prefixes : ∀ n : Nat,
    sigma.iterateLetter n (fixedWord cutoff) =
      (fixedWord.drop cutoff).take
        (sigma.iterateLetter n (fixedWord cutoff)).length

/-- Cancelling a finite prefix which is fixed by finite substitution leaves
a substitution-fixed tail. -/
theorem fixedPoint_drop_of_mapWord_take_eq
    {delta : Type u} {sigma : Substitution delta}
    {fixedWord : InfiniteWord delta} {cutoff : Nat}
    (hfixed : sigma.IsFixedPoint fixedWord)
    (hprefix : sigma.mapWord (fixedWord.take cutoff) =
      fixedWord.take cutoff) :
    sigma.IsFixedPoint (fixedWord.drop cutoff) := by
  rw [IsFixedPoint] at hfixed ⊢
  apply Stream'.append_right_injective
  calc
    fixedWord.take cutoff ++ₛ sigma.mapInfinite (fixedWord.drop cutoff) =
        sigma.mapWord (fixedWord.take cutoff) ++ₛ
          sigma.mapInfinite (fixedWord.drop cutoff) := by rw [hprefix]
    _ = sigma.mapInfinite
          (fixedWord.take cutoff ++ₛ fixedWord.drop cutoff) :=
      (sigma.mapInfinite_append_stream _ _).symm
    _ = sigma.mapInfinite fixedWord := by
      rw [Stream'.append_take_drop]
    _ = fixedWord := hfixed
    _ = fixedWord.take cutoff ++ₛ fixedWord.drop cutoff :=
      (Stream'.append_take_drop cutoff fixedWord).symm

/-- Iterated images of the first letter of a prolongable fixed point are its
corresponding finite prefixes. -/
theorem iterateLetter_eq_take_of_fixedPoint
    {delta : Type u} {sigma : Substitution delta}
    {seed : delta} {fixedWord : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint fixedWord)
    (hseed : fixedWord.head = seed) :
    ∀ n : Nat, sigma.iterateLetter n seed =
      fixedWord.take (sigma.iterateLetter n seed).length := by
  intro n
  induction n with
  | zero =>
      change [seed] = fixedWord.take 1
      rw [Stream'.take_succ, hseed]
      rfl
  | succ n ih =>
      rw [iterateLetter_succ, ih]
      let image := sigma.mapWord
        (fixedWord.take (sigma.iterateLetter n seed).length)
      have hwhole : image ++ₛ sigma.mapInfinite
          (fixedWord.drop (sigma.iterateLetter n seed).length) = fixedWord := by
        calc
          image ++ₛ sigma.mapInfinite
              (fixedWord.drop (sigma.iterateLetter n seed).length) =
              sigma.mapInfinite
                (fixedWord.take (sigma.iterateLetter n seed).length ++ₛ
                  fixedWord.drop (sigma.iterateLetter n seed).length) :=
            (sigma.mapInfinite_append_stream _ _).symm
          _ = sigma.mapInfinite fixedWord := by
            rw [Stream'.append_take_drop]
          _ = fixedWord := hfixed
      have htake := congrArg (fun stream : InfiniteWord delta =>
        stream.take image.length) hwhole
      change image = fixedWord.take image.length
      have hleft :
          (image ++ₛ sigma.mapInfinite
            (fixedWord.drop (sigma.iterateLetter n seed).length)).take
              image.length = image := by
        simpa using Stream'.take_append_of_le_length
          (x := image)
          (a := sigma.mapInfinite
            (fixedWord.drop (sigma.iterateLetter n seed).length))
          (n := image.length) le_rfl
      exact hleft.symm.trans htake

/-- A fixed point whose first image has length at least two is prolongable on
its first letter. -/
theorem prolongableOn_head_of_fixedPoint
    {delta : Type u} {sigma : Substitution delta}
    {fixedWord : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint fixedWord)
    (hlength : 1 < (sigma fixedWord.head).length) :
    sigma.ProlongableOn fixedWord.head := by
  change sigma.mapInfinite fixedWord = fixedWord at hfixed
  have hhead : sigma.imageHead fixedWord.head = fixedWord.head := by
    have hzero := congrFun hfixed 0
    simpa using hzero
  have htail : sigma.imageTail fixedWord.head ≠ [] := by
    intro hnil
    rw [← sigma.imageHead_cons_imageTail] at hlength
    simp [hnil] at hlength
  refine ⟨sigma.imageTail fixedWord.head, htail, ?_⟩
  rw [← sigma.imageHead_cons_imageTail, hhead]

/-- Every factor of a prolongable fixed point already occurs in some finite
iterate of its first letter. -/
theorem factor_infix_iterateLetter_head
    {delta : Type u} {sigma : Substitution delta}
    {fixedWord : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint fixedWord)
    (hprolong : sigma.ProlongableOn fixedWord.head)
    {word : Word delta} (hfactor : IsInfiniteFactor fixedWord word) :
    ∃ level : Nat,
      word <:+: sigma.iterateLetter level fixedWord.head := by
  rcases hfactor with ⟨start, hstart⟩
  let level := start + word.length
  have hprefix := iterateLetter_eq_take_of_fixedPoint hfixed rfl level
  have hlength : start + word.length ≤
      (sigma.iterateLetter level fixedWord.head).length := by
    exact le_trans (Nat.le_succ (start + word.length))
      (sigma.succ_le_iterateLetter_length hprolong level)
  have hambient : InfiniteFactorAt fixedWord
      (sigma.iterateLetter level fixedWord.head) 0 := by
    simpa [InfiniteFactorAt] using hprefix.symm
  have hfinite : FiniteFactorAt
      (sigma.iterateLetter level fixedWord.head) word start := by
    apply finiteFactorAt_of_nested_infiniteFactorAt hambient
    · simpa using hstart
    · exact hlength
  exact ⟨level, hfinite.isInfix⟩

/-- For a primitive fixed point there is one substitution depth at which
every occurring adjacent pair appears in the image of every letter. -/
theorem exists_uniform_pair_depth
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    {sigma : Substitution delta} {fixedWord : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint fixedWord)
    (hprolong : sigma.ProlongableOn fixedWord.head)
    (hprimitive : ∃ iterate : Nat, 0 < iterate ∧
      ∀ a b : delta, b ∈ sigma.iterateLetter iterate a) :
    ∃ depth : Nat, ∀ a b source : delta,
      IsInfiniteFactor fixedWord [a, b] →
        [a, b] <:+: sigma.iterateLetter depth source := by
  classical
  have hchoice : ∀ a b : delta, ∃ level : Nat,
      IsInfiniteFactor fixedWord [a, b] →
        [a, b] <:+: sigma.iterateLetter level fixedWord.head := by
    intro a b
    by_cases hfactor : IsInfiniteFactor fixedWord [a, b]
    · obtain ⟨level, hlevel⟩ :=
        factor_infix_iterateLetter_head hfixed hprolong hfactor
      exact ⟨level, fun _ => hlevel⟩
    · exact ⟨0, fun h => False.elim (hfactor h)⟩
  choose pairLevel hpairLevel using hchoice
  let commonLevel := Finset.univ.sup fun a : delta =>
    Finset.univ.sup fun b : delta => pairLevel a b
  have hpairAtCommon : ∀ a b : delta,
      IsInfiniteFactor fixedWord [a, b] →
        [a, b] <:+:
          sigma.iterateLetter commonLevel fixedWord.head := by
    intro a b hfactor
    have hinner : pairLevel a b ≤
        Finset.univ.sup (fun c : delta => pairLevel a c) :=
      Finset.le_sup (f := fun c : delta => pairLevel a c)
        (Finset.mem_univ b)
    have houter : Finset.univ.sup (fun c : delta => pairLevel a c) ≤
        commonLevel :=
      Finset.le_sup
        (f := fun c : delta =>
          Finset.univ.sup fun d : delta => pairLevel c d)
        (Finset.mem_univ a)
    have hpref := iterateLetter_prefix_of_le hprolong
      (hinner.trans houter)
    exact (hpairLevel a b hfactor).trans hpref.isInfix
  obtain ⟨primitiveLevel, _hprimitiveLevel, hcontains⟩ := hprimitive
  refine ⟨commonLevel + primitiveLevel, ?_⟩
  intro a b source hfactor
  have hheadMem := hcontains source fixedWord.head
  have hheadImage := sigma.iterateLetter_infix_of_mem_iterate
    (later := commonLevel) hheadMem
  exact (hpairAtCommon a b hfactor).trans hheadImage

/-- If every level-`n` letter image is at least as long as a nonempty factor,
then that factor crosses at most one level-`n` cut and hence lies in the image
of an occurring adjacent pair. -/
theorem factor_infix_iteratePair_of_min_length
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    {sigma : Substitution delta} {fixedWord : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint fixedWord)
    {word : Word delta} (hword : word ≠ [])
    (hfactor : IsInfiniteFactor fixedWord word)
    (level : Nat)
    (hmin : ∀ a : delta,
      word.length ≤ (sigma.iterateLetter level a).length) :
    ∃ a b : delta,
      IsInfiniteFactor fixedWord [a, b] ∧
        word <:+: sigma.iterateWord level [a, b] := by
  classical
  rcases hfactor with ⟨origin, horigin⟩
  let cut : Nat → Nat := fun index =>
    (sigma.iterateWord level (fixedWord.take index)).length
  have hcutZero : cut 0 = 0 := by simp [cut]
  have hcutSucc : ∀ index : Nat,
      cut (index + 1) = cut index +
        (sigma.iterateLetter level (fixedWord index)).length := by
    intro index
    dsimp only [cut]
    rw [Stream'.take_succ', iterateWord_append_public,
      List.length_append]
    rfl
  have hindexLeCut : ∀ index : Nat, index ≤ cut index := by
    intro index
    exact (by simpa [cut] using
      sigma.length_le_iterateWord level (fixedWord.take index))
  let candidates : Finset Nat :=
    (Finset.range (origin + 1)).filter fun index => cut index ≤ origin
  have hzeroMem : 0 ∈ candidates := by
    simp [candidates, hcutZero]
  have hcandidates : candidates.Nonempty := ⟨0, hzeroMem⟩
  let index := candidates.max' hcandidates
  have hindexMem : index ∈ candidates :=
    candidates.max'_mem hcandidates
  have hindexRange : index < origin + 1 :=
    Finset.mem_range.mp (Finset.mem_filter.mp hindexMem).1
  have hcutIndex : cut index ≤ origin :=
    (Finset.mem_filter.mp hindexMem).2
  have horiginBeforeNext : origin < cut (index + 1) := by
    by_contra hnot
    have hnextCut : cut (index + 1) ≤ origin := by omega
    have hnextIndex : index + 1 ≤ origin :=
      (hindexLeCut (index + 1)).trans hnextCut
    have hnextMem : index + 1 ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hnextCut⟩
    have hmax := candidates.le_max' (index + 1) hnextMem
    omega
  have hendBeforeSecond : origin + word.length ≤ cut (index + 2) := by
    have hnextMin := hmin (fixedWord (index + 1))
    rw [show index + 2 = (index + 1) + 1 by omega,
      hcutSucc (index + 1)]
    omega
  let pair : Word delta :=
    [fixedWord index, fixedWord (index + 1)]
  have htakeTwo : (fixedWord.drop index).take 2 = pair := by
    rw [show 2 = Nat.succ 1 by rfl, Stream'.take_succ,
      show 1 = Nat.succ 0 by rfl, Stream'.take_succ]
    simp only [pair, Stream'.head_drop, Stream'.tail_drop',
      Stream'.take_zero, List.cons.injEq, and_true]
    exact ⟨rfl, rfl⟩
  have hpairAt : InfiniteFactorAt fixedWord pair index := by
    simpa [InfiniteFactorAt] using htakeTwo
  have hpairFactor : IsInfiniteFactor fixedWord pair := ⟨index, hpairAt⟩
  let block := sigma.iterateWord level pair
  have hblockAt : InfiniteFactorAt fixedWord block (cut index) := by
    have hraw := iterateWord_drop_take_at_fixed hfixed level index 2
    rw [htakeTwo] at hraw
    simpa [cut, block] using hraw
  have hblockLength : block.length = cut (index + 2) - cut index := by
    have hfirst := hcutSucc index
    have hsecond := hcutSucc (index + 1)
    have hsecond' : cut (index + 2) = cut (index + 1) +
        (sigma.iterateLetter level (fixedWord (index + 1))).length := by
      convert hsecond using 1 <;> omega
    simp only [block, pair, show
      [fixedWord index, fixedWord (index + 1)] =
        [fixedWord index] ++ [fixedWord (index + 1)] by rfl,
      iterateWord_append_public, List.length_append]
    change (sigma.iterateLetter level (fixedWord index)).length +
        (sigma.iterateLetter level (fixedWord (index + 1))).length = _
    omega
  have hwithin : (origin - cut index) + word.length ≤ block.length := by
    rw [hblockLength]
    omega
  have hfinite : FiniteFactorAt block word (origin - cut index) := by
    apply finiteFactorAt_of_nested_infiniteFactorAt hblockAt
    · convert horigin using 1 <;> omega
    · exact hwithin
  exact ⟨fixedWord index, fixedWord (index + 1),
    hpairFactor, hfinite.isInfix⟩

/-- If a word occurs in every letter image at one fixed level, then from any
position one reaches an occurrence after crossing at most one level cut and
one further image block. -/
theorem factor_appears_within_two_maxImages
    {delta : Type u} [Fintype delta] [DecidableEq delta]
    {sigma : Substitution delta} {fixedWord : InfiniteWord delta}
    (hfixed : sigma.IsFixedPoint fixedWord)
    {word : Word delta} (level : Nat)
    (hevery : ∀ a : delta,
      word <:+: sigma.iterateLetter level a) :
    ∀ start : Nat, ∃ position : Nat,
      start ≤ position ∧
        position ≤ start + 2 * sigma.maxIterateLength level ∧
        InfiniteFactorAt fixedWord word position := by
  classical
  intro start
  let cut : Nat → Nat := fun index =>
    (sigma.iterateWord level (fixedWord.take index)).length
  have hcutZero : cut 0 = 0 := by simp [cut]
  have hcutSucc : ∀ index : Nat,
      cut (index + 1) = cut index +
        (sigma.iterateLetter level (fixedWord index)).length := by
    intro index
    dsimp only [cut]
    rw [Stream'.take_succ', iterateWord_append_public,
      List.length_append]
    rfl
  have hindexLeCut : ∀ index : Nat, index ≤ cut index := by
    intro index
    exact (by simpa [cut] using
      sigma.length_le_iterateWord level (fixedWord.take index))
  let candidates : Finset Nat :=
    (Finset.range (start + 1)).filter fun index => cut index ≤ start
  have hzeroMem : 0 ∈ candidates := by
    simp [candidates, hcutZero]
  have hcandidates : candidates.Nonempty := ⟨0, hzeroMem⟩
  let index := candidates.max' hcandidates
  have hindexMem : index ∈ candidates := candidates.max'_mem hcandidates
  have hcutIndex : cut index ≤ start :=
    (Finset.mem_filter.mp hindexMem).2
  have hstartBeforeNext : start < cut (index + 1) := by
    by_contra hnot
    have hnextCut : cut (index + 1) ≤ start := by omega
    have hnextIndex : index + 1 ≤ start :=
      (hindexLeCut (index + 1)).trans hnextCut
    have hnextMem : index + 1 ∈ candidates := by
      simp only [candidates, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hnextCut⟩
    have hmax := candidates.le_max' (index + 1) hnextMem
    omega
  have hnextBound : cut (index + 1) ≤
      start + sigma.maxIterateLength level := by
    have hstep := hcutSucc index
    have himageMax := sigma.iterateLetter_length_le_maxIterateLength
      level (fixedWord index)
    omega
  let source := fixedWord (index + 1)
  rcases hevery source with ⟨left, right, hsplit⟩
  have hfinite : FiniteFactorAt
      (sigma.iterateLetter level source) word left.length := by
    rw [← hsplit]
    simp [FiniteFactorAt]
  have htakeOne : (fixedWord.drop (index + 1)).take 1 = [source] := by
    rw [show 1 = Nat.succ 0 by rfl, Stream'.take_succ]
    simp only [source, Stream'.head_drop, Stream'.take_zero,
      List.cons.injEq, and_true]
    rfl
  have hblockAt : InfiniteFactorAt fixedWord
      (sigma.iterateLetter level source) (cut (index + 1)) := by
    have hraw := iterateWord_drop_take_at_fixed hfixed level (index + 1) 1
    rw [htakeOne] at hraw
    simpa [cut, source] using hraw
  let position := cut (index + 1) + left.length
  have hposition : InfiniteFactorAt fixedWord word position := by
    exact hblockAt.of_finiteFactorAt hfinite
  have hleftBound : left.length ≤ sigma.maxIterateLength level := by
    have himageMax := sigma.iterateLetter_length_le_maxIterateLength
      level source
    exact (Nat.le_add_right left.length word.length).trans
      (hfinite.1.trans himageMax)
  refine ⟨position, by omega, ?_, hposition⟩
  dsimp only [position]
  omega

/-- A primitive substitution fixed point has a uniform linear factor-gap
bound.  The constant is obtained from the finitely many adjacent pairs and a
fixed number of extra substitution levels. -/
theorem primitive_fixedPoint_hasLinearFactorGaps
    {delta : Type u} [Fintype delta] [DecidableEq delta] [Nonempty delta]
    {sigma : Substitution delta} {fixedWord : InfiniteWord delta}
    {seed : delta}
    (hfixed : sigma.IsFixedPoint fixedWord)
    (hprimitive : ∃ iterate : Nat, 0 < iterate ∧
      ∀ a b : delta, b ∈ sigma.iterateLetter iterate a)
    (hgrow : LetterImagesGrow sigma seed) :
    ∃ constant : Nat, HasLinearFactorGaps fixedWord constant := by
  classical
  have hprolong := prolongableOn_head_of_primitive_fixedPoint
    hfixed hprimitive hgrow
  obtain ⟨pairDepth, hpairDepth⟩ :=
    exists_uniform_pair_depth hfixed hprolong hprimitive
  obtain ⟨primitiveLevel, _hprimitiveLevel, hcontains⟩ := hprimitive
  let extra := 1 + primitiveLevel + pairDepth
  let constant := 2 * sigma.maxIterateLength extra
  have hmaxExtraPos : 0 < sigma.maxIterateLength extra := by
    let witness : delta := Classical.choice (inferInstance : Nonempty delta)
    exact (List.length_pos_of_ne_nil
      (sigma.iterateLetter_ne_nil extra witness)).trans_le
        (sigma.iterateLetter_length_le_maxIterateLength extra witness)
  refine ⟨constant, ⟨Nat.mul_pos (by omega) hmaxExtraPos, ?_⟩⟩
  intro word hword hfactor start
  have hwordLength : 0 < word.length := List.length_pos_of_ne_nil hword
  have hscaleExists : ∃ scale : Nat,
      0 < scale ∧ word.length ≤ sigma.maxIterateLength scale := by
    refine ⟨word.length, hwordLength, ?_⟩
    exact (Nat.le_succ word.length).trans
      ((sigma.succ_le_iterateLetter_length hprolong word.length).trans
        (sigma.iterateLetter_length_le_maxIterateLength
          word.length fixedWord.head))
  let scale : Nat :=
    @Nat.find
      (fun n : Nat =>
        0 < n ∧ word.length ≤ sigma.maxIterateLength n)
      (fun _ => Classical.propDecidable _)
      hscaleExists
  have hscaleSpec : 0 < scale ∧
      word.length ≤ sigma.maxIterateLength scale := by
    simpa only [scale] using
      (@Nat.find_spec
        (fun n : Nat =>
          0 < n ∧ word.length ≤ sigma.maxIterateLength n)
        (fun _ => Classical.propDecidable _)
        hscaleExists)
  let previous := scale - 1
  have hscaleEq : scale = previous + 1 := by
    dsimp only [previous]
    omega
  have hpreviousMax : sigma.maxIterateLength previous ≤ word.length := by
    by_cases hzero : previous = 0
    · rw [hzero, sigma.maxIterateLength_zero]
      omega
    · have hpreviousPos : 0 < previous := Nat.pos_of_ne_zero hzero
      have hpreviousLt : previous < scale := by omega
      have hpreviousFind : previous <
          @Nat.find
            (fun n : Nat =>
              0 < n ∧ word.length ≤ sigma.maxIterateLength n)
            (fun _ => Classical.propDecidable _)
            hscaleExists := by
        simpa only [scale] using hpreviousLt
      have hnot := @Nat.find_min
        (fun n : Nat =>
          0 < n ∧ word.length ≤ sigma.maxIterateLength n)
        (fun _ => Classical.propDecidable _)
        hscaleExists previous hpreviousFind
      by_contra hbound
      exact hnot ⟨hpreviousPos, by omega⟩
  obtain ⟨maxLetter, hmaxLetter⟩ :=
    sigma.exists_length_eq_maxIterateLength scale
  have hmin : ∀ a : delta, word.length ≤
      (sigma.iterateLetter (scale + primitiveLevel) a).length := by
    intro a
    have hmem := hcontains a maxLetter
    have hinfix := sigma.iterateLetter_infix_of_mem_iterate
      (later := scale) hmem
    calc
      word.length ≤ sigma.maxIterateLength scale := hscaleSpec.2
      _ = (sigma.iterateLetter scale maxLetter).length := hmaxLetter.symm
      _ ≤ (sigma.iterateLetter (scale + primitiveLevel) a).length :=
        hinfix.length_le
  obtain ⟨leftLetter, rightLetter, hpairFactor, hwordPair⟩ :=
    factor_infix_iteratePair_of_min_length hfixed hword hfactor
      (scale + primitiveLevel) hmin
  let totalDepth := scale + primitiveLevel + pairDepth
  have hevery : ∀ a : delta,
      word <:+: sigma.iterateLetter totalDepth a := by
    intro a
    have hpairImage := hpairDepth leftLetter rightLetter a hpairFactor
    have hiterated := sigma.iterateWord_infix_public
      (scale + primitiveLevel) hpairImage
    have hcombined :
        sigma.iterateWord (scale + primitiveLevel)
            (sigma.iterateLetter pairDepth a) =
          sigma.iterateLetter totalDepth a := by
      dsimp only [totalDepth]
      change sigma.iterateWord (scale + primitiveLevel)
          (sigma.iterateWord pairDepth [a]) =
        sigma.iterateWord (scale + primitiveLevel + pairDepth) [a]
      exact (iterateWord_add_public sigma
        (scale + primitiveLevel) pairDepth [a]).symm
    have htrans := hwordPair.trans hiterated
    rw [hcombined] at htrans
    exact htrans
  rcases factor_appears_within_two_maxImages hfixed totalDepth hevery start with
    ⟨position, hpositionStart, hpositionBound, hposition⟩
  have hdepthEq : totalDepth = previous + extra := by
    dsimp only [totalDepth, extra]
    omega
  have hmaxDepth : sigma.maxIterateLength totalDepth ≤
      sigma.maxIterateLength extra * word.length := by
    rw [hdepthEq]
    exact (sigma.maxIterateLength_add_le previous extra).trans
      (Nat.mul_le_mul_left _ hpreviousMax)
  have hdistance : 2 * sigma.maxIterateLength totalDepth ≤
      constant * word.length := by
    calc
      2 * sigma.maxIterateLength totalDepth ≤
          2 * (sigma.maxIterateLength extra * word.length) :=
        Nat.mul_le_mul_left 2 hmaxDepth
      _ = constant * word.length := by
        dsimp only [constant]
        ring
  exact ⟨position, hpositionStart, by omega, hposition⟩

/-- Every fixed point containing a prolongable generating seed is a finite
singleton-image prefix followed by a canonical fixed point on a (possibly
different) prolongable generating letter. -/
theorem eventualCanonicalTail_of_fixedPoint
    {delta : Type u} (sigma : Substitution delta)
    (seed : delta) (fixedWord : InfiniteWord delta)
    (hprolong : sigma.ProlongableOn seed)
    (hgenerate : sigma.IsGeneratingLetter seed)
    (hfixed : sigma.IsFixedPoint fixedWord)
    (hseedOccurs : OccursInInfiniteWord seed fixedWord) :
    Nonempty (EventualCanonicalTail sigma fixedWord) := by
  obtain ⟨seedTail, hseedTail, hseedImage⟩ := hprolong
  obtain ⟨seedPosition, hseedPosition⟩ := hseedOccurs
  have hseedLength : 1 < (sigma seed).length := by
    rw [hseedImage]
    simp only [List.length_cons]
    exact Nat.succ_lt_succ (List.length_pos_of_ne_nil hseedTail)
  have hexpanding : ∃ position : Nat,
      1 < (sigma (fixedWord position)).length :=
    ⟨seedPosition, by simpa [hseedPosition] using hseedLength⟩
  let cutoff := Nat.find hexpanding
  have hcutoffExpanding :
      1 < (sigma (fixedWord cutoff)).length :=
    Nat.find_spec hexpanding
  have hbefore : ∀ position < cutoff,
      (sigma (fixedWord position)).length = 1 := by
    intro position hposition
    have hnot := Nat.find_min hexpanding hposition
    have hpositive : 0 < (sigma (fixedWord position)).length :=
      List.length_pos_of_ne_nil (sigma.image_ne_nil _)
    omega
  have hprefix : ∀ length : Nat, length ≤ cutoff →
      sigma.mapWord (fixedWord.take length) = fixedWord.take length := by
    intro length hlength
    induction length with
    | zero => rfl
    | succ length ih =>
        have hlengthLt : length < cutoff := by omega
        have ih' := ih (by omega)
        have htailFixed :=
          fixedPoint_drop_of_mapWord_take_eq hfixed ih'
        have himageLength := hbefore length hlengthLt
        have hfirst := sigma.take_mapInfinite_first_image
          (fixedWord.drop length)
        rw [htailFixed] at hfirst
        have hheadDrop : (fixedWord.drop length).head =
            fixedWord.get length := Stream'.head_drop fixedWord length
        have himageLengthGet :
            (sigma (fixedWord.get length)).length = 1 := by
          simpa [Stream'.get] using himageLength
        rw [hheadDrop, himageLengthGet] at hfirst
        have htakeOne : (fixedWord.drop length).take 1 =
            [fixedWord.get length] := by
          rw [Stream'.take_succ]
          simp [hheadDrop]
        rw [htakeOne] at hfirst
        have himage : sigma (fixedWord.get length) =
            [fixedWord.get length] := hfirst.symm
        rw [Stream'.take_succ', mapWord_append, ih']
        simp [himage]
  have hprefixCutoff := hprefix cutoff le_rfl
  have htailFixed : sigma.IsFixedPoint (fixedWord.drop cutoff) :=
    fixedPoint_drop_of_mapWord_take_eq hfixed hprefixCutoff
  have htailProlongable : sigma.ProlongableOn (fixedWord cutoff) := by
    have := prolongableOn_head_of_fixedPoint htailFixed
      (by simpa [Stream'.head_drop] using hcutoffExpanding)
    simpa [Stream'.head_drop] using this
  have hiterates : ∀ n : Nat,
      sigma.iterateLetter n (fixedWord cutoff) =
        (fixedWord.drop cutoff).take
          (sigma.iterateLetter n (fixedWord cutoff)).length := by
    apply iterateLetter_eq_take_of_fixedPoint htailFixed
    exact Stream'.head_drop fixedWord cutoff
  have hcutoffLeSeed : cutoff ≤ seedPosition := by
    apply Nat.find_min' (p := fun position =>
      1 < (sigma (fixedWord position)).length)
    simpa [hseedPosition] using hseedLength
  have hseedOccursTail : OccursInInfiniteWord seed
      (fixedWord.drop cutoff) := by
    refine ⟨seedPosition - cutoff, ?_⟩
    have hdrop := Stream'.get_drop
      (seedPosition - cutoff) cutoff fixedWord
    rw [Nat.add_sub_of_le hcutoffLeSeed] at hdrop
    exact hdrop.trans hseedPosition
  have htailReachesSeed : sigma.OccursFrom (fixedWord cutoff) seed :=
    sigma.isGeneratingLetter_of_iterateLetter_eq_take
      htailProlongable hiterates seed hseedOccursTail
  have htailGenerating : sigma.IsGeneratingLetter (fixedWord cutoff) := by
    intro letter
    exact letterReachable_trans htailReachesSeed (hgenerate letter)
  exact ⟨{
    cutoff := cutoff
    inert_prefix := hprefixCutoff
    tail_fixed := htailFixed
    tail_prolongable := htailProlongable
    tail_generating := htailGenerating
    iterates_are_prefixes := hiterates }⟩

/-- The SCC partition of the finite reachability digraph. -/
structure SCCDecomposition {delta : Type u} [Fintype delta]
    [DecidableEq delta] (sigma : Substitution delta) where
  components : Finset (Finset delta)
  component_nonempty : ∀ component ∈ components, component.Nonempty
  component_connected : ∀ component ∈ components,
    ∀ a ∈ component, ∀ b ∈ component,
      LettersStronglyConnected sigma a b
  component_iff : ∀ a b : delta,
    LettersStronglyConnected sigma a b ↔
      ∃ component ∈ components, a ∈ component ∧ b ∈ component

/-- Every finite substitution reachability graph admits its SCC partition. -/
theorem exists_sccDecomposition
    {delta : Type u} [Fintype delta] [DecidableEq delta] [Nonempty delta]
    (sigma : Substitution delta) :
    Nonempty (SCCDecomposition sigma) := by
  classical
  let componentSet : Finset (Finset delta) :=
    Finset.univ.image (strongComponent sigma)
  refine ⟨{
    components := componentSet
    component_nonempty := ?_
    component_connected := ?_
    component_iff := ?_ }⟩
  · intro component hcomponent
    simp only [componentSet, Finset.mem_image, Finset.mem_univ, true_and]
      at hcomponent
    rcases hcomponent with ⟨representative, rfl⟩
    exact ⟨representative,
      (mem_strongComponent_iff sigma representative representative).2
        (lettersStronglyConnected_refl sigma representative)⟩
  · intro component hcomponent
    simp only [componentSet, Finset.mem_image, Finset.mem_univ, true_and]
      at hcomponent
    rcases hcomponent with ⟨representative, rfl⟩
    intro a ha b hb
    rw [mem_strongComponent_iff] at ha hb
    exact lettersStronglyConnected_trans
      (lettersStronglyConnected_symm ha) hb
  · intro a b
    constructor
    · intro hab
      refine ⟨strongComponent sigma a, ?_, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      · exact (mem_strongComponent_iff sigma a a).2
          (lettersStronglyConnected_refl sigma a)
      · exact (mem_strongComponent_iff sigma a b).2 hab
    · rintro ⟨component, hcomponent, ha, hb⟩
      simp only [componentSet, Finset.mem_image, Finset.mem_univ, true_and]
        at hcomponent
      rcases hcomponent with ⟨representative, rfl⟩
      rw [mem_strongComponent_iff] at ha hb
      exact lettersStronglyConnected_trans
        (lettersStronglyConnected_symm ha) hb

end Symbolic.Substitution

/-- Return words to a prefix form a finite set in a linearly recurrent word. -/
theorem linearlyRecurrent_returnWords_finite
    {gamma : Type*} [Fintype gamma] [DecidableEq gamma]
    {x : Symbolic.InfiniteWord gamma} {constant : Nat}
    (hlinear : Symbolic.IsLinearlyRecurrent x constant)
    {marker : Symbolic.Word gamma}
    (hmarker : Symbolic.InfiniteFactorAt x marker 0)
    (hmarkerNonempty : marker ≠ []) :
    Set.Finite {word : Symbolic.Word gamma |
      Symbolic.IsReturnWord x marker word} := by
  apply (List.finite_length_le gamma (constant * marker.length)).subset
  intro word hword
  exact hlinear.2.2 marker word hword

/-- Consecutive occurrences of a prefix in a linearly recurrent word give a
complete decomposition over the finite alphabet of its return words. -/
theorem linearlyRecurrent_returnDecomposition
    {gamma : Type*} [Fintype gamma] [DecidableEq gamma]
    {x : Symbolic.InfiniteWord gamma} {constant : Nat}
    (hlinear : Symbolic.IsLinearlyRecurrent x constant)
    {marker : Symbolic.Word gamma}
    (hmarker : Symbolic.InfiniteFactorAt x marker 0)
    (hmarkerNonempty : marker ≠ []) :
    ∃ rank : Nat,
      Nonempty (Symbolic.ReturnDecomposition x marker rank) := by
  classical
  have hmarkerFactor : Symbolic.IsInfiniteFactor x marker := ⟨0, hmarker⟩
  obtain ⟨gap, _hgap, hbounded⟩ := hlinear.2.1 marker hmarkerFactor
  have hafter : ∀ start : Nat, ∃ position : Nat,
      start < position ∧ Symbolic.InfiniteFactorAt x marker position := by
    intro start
    rcases hbounded (start + 1) with
      ⟨offset, _hoffset, hfactor⟩
    exact ⟨start + 1 + offset, by omega, hfactor⟩
  let next : Nat → Nat := fun start =>
    @Nat.find
      (fun position : Nat =>
        start < position ∧
          Symbolic.InfiniteFactorAt x marker position)
      (fun _ => Classical.propDecidable _)
      (hafter start)
  have hnext : ∀ start : Nat,
      start < next start ∧
        Symbolic.InfiniteFactorAt x marker (next start) := by
    intro start
    simpa only [next] using
      (@Nat.find_spec
        (fun position : Nat =>
          start < position ∧
            Symbolic.InfiniteFactorAt x marker position)
        (fun _ => Classical.propDecidable _)
        (hafter start))
  let cut : Nat → Nat := fun n =>
    Nat.rec 0 (fun _ previous => next previous) n
  have hcutZero : cut 0 = 0 := rfl
  have hcutSucc : ∀ n : Nat, cut (n + 1) = next (cut n) := by
    intro n
    simp [cut]
  have hcutMarker : ∀ n : Nat,
      Symbolic.InfiniteFactorAt x marker (cut n) := by
    intro n
    induction n with
    | zero => simpa [hcutZero] using hmarker
    | succ n _ =>
        rw [hcutSucc]
        exact (hnext (cut n)).2
  have hcutLt : ∀ n : Nat, cut n < cut (n + 1) := by
    intro n
    rw [hcutSucc]
    exact (hnext (cut n)).1
  let block : Nat → Symbolic.Word gamma := fun n =>
    (x.drop (cut n)).take (cut (n + 1) - cut n)
  have hblockReturn : ∀ n : Nat,
      Symbolic.IsReturnWord x marker (block n) := by
    intro n
    apply Symbolic.returnWord_between_consecutive_occurrences
      hmarkerNonempty (hcutMarker n) (hcutMarker (n + 1)) (hcutLt n)
    intro position hleft hright hposition
    have hpositionNext : position < next (cut n) := by
      rwa [← hcutSucc]
    have hpositionFind : position <
        @Nat.find
          (fun candidate : Nat =>
            cut n < candidate ∧
              Symbolic.InfiniteFactorAt x marker candidate)
          (fun _ => Classical.propDecidable _)
          (hafter (cut n)) := by
      simpa only [next] using hpositionNext
    have hnot := @Nat.find_min
      (fun candidate : Nat =>
        cut n < candidate ∧
          Symbolic.InfiniteFactorAt x marker candidate)
      (fun _ => Classical.propDecidable _)
      (hafter (cut n)) position hpositionFind
    exact False.elim (hnot ⟨hleft, hposition⟩)
  let ReturnType :=
    {word : Symbolic.Word gamma //
      Symbolic.IsReturnWord x marker word}
  have hreturnFinite : Set.Finite
      {word : Symbolic.Word gamma |
        Symbolic.IsReturnWord x marker word} :=
    linearlyRecurrent_returnWords_finite hlinear hmarker hmarkerNonempty
  letI : Fintype ReturnType := hreturnFinite.fintype
  let rank := Fintype.card ReturnType
  let enumerate : ReturnType ≃ Fin rank := Fintype.equivFin ReturnType
  let actual : Nat → ReturnType := fun n => ⟨block n, hblockReturn n⟩
  let derived : Symbolic.InfiniteWord (Fin rank) := fun n => enumerate (actual n)
  let blocks : Fin rank → Symbolic.Word gamma := fun a => (enumerate.symm a).1
  have hblocksActual : ∀ n : Nat, blocks (derived n) = block n := by
    intro n
    simp [blocks, derived, actual]
  have hrankPos : 0 < rank := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨actual 0⟩
  refine ⟨rank, ⟨{
    rank_pos := hrankPos
    marker_ne_nil := hmarkerNonempty
    marker_at_zero := hmarker
    blocks := blocks
    blocks_injective := ?_
    blocks_are_returns := ?_
    derived := derived
    cut := cut
    cut_zero := hcutZero
    cut_succ := ?_
    block_at_cut := ?_ }⟩⟩
  · intro a b hab
    apply enumerate.symm.injective
    apply Subtype.ext
    exact hab
  · intro a
    exact (enumerate.symm a).2
  · intro n
    rw [hblocksActual]
    have hlength : (block n).length = cut (n + 1) - cut n := by
      simp [block]
    rw [hlength]
    exact (Nat.add_sub_of_le (Nat.le_of_lt (hcutLt n))).symm
  · intro n
    rw [hblocksActual]
    simp [Symbolic.InfiniteFactorAt, block]

/-- The power-freeness consequence of aperiodic linear recurrence.  This is
kept in the dependency-clean B9 support because the quantitative return-tower
bound consumes it after the legacy symbolic module has been removed. -/
theorem linearlyRecurrent_aperiodic_powerFree
    {gamma : Type*} [Fintype gamma] [DecidableEq gamma]
    {x : Symbolic.InfiniteWord gamma} {constant : Nat}
    (hlinear : Symbolic.IsLinearlyRecurrent x constant)
    (haperiodic : ¬ Symbolic.IsPeriodic x) :
    Symbolic.IsPowerFree x (constant + 1) := by
  intro base hbase hpower
  exact haperiodic (hlinear.periodic_of_powerFactor hbase hpower)

/-- In a nonperiodic linearly recurrent word, every return word has the lower
length bound needed by the finite return-system count. -/
theorem linearlyRecurrent_returnWord_lowerBound
    {gamma : Type*} [Fintype gamma] [DecidableEq gamma]
    {x : Symbolic.InfiniteWord gamma} {constant : Nat}
    (hlinear : Symbolic.IsLinearlyRecurrent x constant)
    (haperiodic : ¬ Symbolic.IsPeriodic x)
    {marker word : Symbolic.Word gamma}
    (hreturn : Symbolic.IsReturnWord x marker word) :
    marker.length ≤ constant * word.length := by
  by_contra hbound
  have hshort : constant * word.length ≤ marker.length := by omega
  apply (linearlyRecurrent_aperiodic_powerFree hlinear haperiodic)
    word hreturn.2.1
  exact Symbolic.returnWord_power_of_short hreturn hshort

/-- If every recurrent factor has bounded gaps and the recurrent language is
generated by powers of one primitive word, the original sequence has only a
finite transient prefix. -/
theorem periodicRecurrentLanguage_ultimatelyPeriodic
    {gamma : Type*} [Fintype gamma] [DecidableEq gamma]
    {x : Symbolic.InfiniteWord gamma}
    (hsyndetic : Symbolic.RecurrentFactorsSyndetic x)
    (hperiodicLanguage : Symbolic.HasPeriodicRecurrentLanguage x) :
    Symbolic.IsUltimatelyPeriodic x := by
  rcases hperiodicLanguage with ⟨periodWord, hprimitive, hpowers⟩
  let period := periodWord.length
  have hperiodPos : 0 < period :=
    List.length_pos_of_ne_nil hprimitive.1
  obtain ⟨start, hstart⟩ :=
    Symbolic.eventually_every_fixedLengthFactor_recurrent x (period + 1)
  refine ⟨start, period, hperiodPos, ?_⟩
  intro n hn
  let factor := (x.drop n).take (period + 1)
  have hfactorRecurrent : Symbolic.IsRecurrentFactor x factor := by
    simpa [factor] using hstart n hn
  obtain ⟨power, hfactorPower⟩ :=
    Symbolic.recurrentFactor_isInfix_wordPower hsyndetic
      hprimitive hpowers hfactorRecurrent
  have hfactorPeriod : List.HasPeriod factor period := by
    apply (Symbolic.wordPower_hasPeriod periodWord power).infix hfactorPower
  have hget := (List.hasPeriod_iff_getElem?).mp hfactorPeriod 0 (by
    simp [factor, period])
  have hstream : (x.drop n).get 0 = (x.drop n).get period := by
    simpa [factor] using hget
  have hwhole : x.get n = x.get (n + period) := by
    simpa [Stream'.get_drop, Nat.add_comm] using hstream
  exact hwhole.symm

/-! ## From symbolic period to metric period -/

/-- A positive period valid on a sufficiently late metric tail. -/
def HasEventualMetricPeriod (ψ : ℝ → I) (P : ℝ) : Prop :=
  0 < P ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → ψ (t + P) = ψ t

/-- Literal symbolic periodicity gives a genuine metric period by summing
the positive lengths in one repeated block. -/
theorem ultimate_word_period_gives_eventual_metric_period
    {K : Finset I} {α : Type*} [Fintype α]
    {ψ : ℝ → I} {edge : α → DirectedMarkovEdge K}
    {length : α → ℝ} {x : Symbolic.InfiniteWord α}
    (hlength : ∀ a, 0 < length a)
    (hitinerary : HasLiteralUnitSpeedItinerary ψ edge length x)
    (hperiodic : Symbolic.IsUltimatelyPeriodic x) :
    ∃ P : ℝ, HasEventualMetricPeriod ψ P := by
  classical
  rcases hperiodic with ⟨start, period, hperiodPos, hwordPeriod⟩
  let L : ℕ → ℝ := prefixMetricLength length x
  have hLsucc (n : ℕ) : L (n + 1) = L n + length (x n) := by
    simp [L, prefixMetricLength, Finset.sum_range_succ]
  have hLstrict : StrictMono L :=
    strictMono_nat_of_lt_succ fun n => by
      rw [hLsucc]
      exact lt_add_of_pos_right _ (hlength (x n))
  have hLnonneg (n : ℕ) : 0 ≤ L n := by
    dsimp [L, prefixMetricLength]
    exact Finset.sum_nonneg fun i _ => (hlength (x i)).le
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
          _ = L (start + k + period) + length (x (start + k + period)) :=
            hLsucc _
          _ = (L (start + k) + P) + length (x (start + k)) := by
            rw [ih (by omega), hw]
          _ = (L (start + k) + length (x (start + k))) + P := by ring
          _ = L (start + (k + 1)) + P := by
            rw [show start + (k + 1) = (start + k) + 1 by omega, hLsucc]
  letI : Nonempty α := ⟨x 0⟩
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
        have hδxn := hδle (x n)
        push_cast
        nlinarith
  refine ⟨P, hPpos, L start, hLnonneg start, ?_⟩
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
  have hulength : u ≤ length (x n) := by
    rw [hLsucc] at htNext
    dsimp [u]
    linarith
  have huEdge : u ≤ (edge (x n)).length := by
    rw [← hitinerary.1 (x n)]
    exact hulength
  have huEdgePeriod : u ≤ (edge (x (n + period))).length := by
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
    _ = match (edge (x (n + period))).forward with
        | true => ((edge (x (n + period))).lower : ℝ) + u
        | false => ((edge (x (n + period))).upper : ℝ) - u :=
      htraversePeriod
    _ = match (edge (x n)).forward with
        | true => ((edge (x n)).lower : ℝ) + u
        | false => ((edge (x n)).upper : ℝ) - u := by
      rw [hwordPeriod n hstartn]
    _ = (ψ (L n + u) : ℝ) := htraverse.symm
    _ = (ψ t : ℝ) := by
      have harg : L n + u = t := by
        dsimp [u]
        ring
      rw [harg]

/-- A global periodic path which agrees with the original ray sufficiently
far out. -/
def IsPeriodicTailExtension (ray path : ℝ → I) (P : ℝ) : Prop :=
  0 < P ∧ Continuous path ∧
    (∀ t : ℝ, path (t + P) = path t) ∧
    ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → path t = ray t

/-- Eventual metric periodicity gives a well-defined continuous periodic
extension by translating parameters by sufficiently large multiples. -/
theorem exists_periodic_tail_extension
    {ray : ℝ → I} {P : ℝ}
    (hray : Continuous ray)
    (hperiod : HasEventualMetricPeriod ray P) :
    ∃ path : ℝ → I, IsPeriodicTailExtension ray path P := by
  classical
  rcases hperiod with ⟨hPpos, tailStart, htailStart, hstep⟩
  have hnatPeriod (t : ℝ) (ht : tailStart ≤ t) :
      ∀ n : ℕ, ray (t + (n : ℝ) * P) = ray t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hnnonneg : 0 ≤ (n : ℝ) * P :=
          mul_nonneg (Nat.cast_nonneg n) hPpos.le
        calc
          ray (t + ((n + 1 : ℕ) : ℝ) * P) =
              ray ((t + (n : ℝ) * P) + P) := by
            congr 1
            push_cast
            ring
          _ = ray (t + (n : ℝ) * P) :=
            hstep _ (ht.trans (le_add_of_nonneg_right hnnonneg))
          _ = ray t := ih
  have hexistsShift (t : ℝ) :
      ∃ n : ℕ, tailStart ≤ t + (n : ℝ) * P := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((tailStart - t) / P)
    have hmul : tailStart - t < (n : ℝ) * P :=
      (div_lt_iff₀ hPpos).mp hn
    exact ⟨n, by linarith⟩
  let shiftIndex : ℝ → ℕ := fun t => (hexistsShift t).choose
  have hshiftLate (t : ℝ) :
      tailStart ≤ t + (shiftIndex t : ℝ) * P :=
    (hexistsShift t).choose_spec
  let path : ℝ → I := fun t => ray (t + (shiftIndex t : ℝ) * P)
  have hpath_eq_shift (t : ℝ) (n : ℕ)
      (hn : tailStart ≤ t + (n : ℝ) * P) :
      path t = ray (t + (n : ℝ) * P) := by
    by_cases hle : shiftIndex t ≤ n
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      calc
        path t = ray (t + (shiftIndex t : ℝ) * P) := rfl
        _ = ray ((t + (shiftIndex t : ℝ) * P) + (k : ℝ) * P) :=
          (hnatPeriod _ (hshiftLate t) k).symm
        _ = ray (t + (n : ℝ) * P) := by
          rw [hk]
          congr 1
          push_cast
          ring
    · have hnle : n ≤ shiftIndex t := Nat.le_of_not_ge hle
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnle
      calc
        path t = ray (t + (shiftIndex t : ℝ) * P) := rfl
        _ = ray ((t + (n : ℝ) * P) + (k : ℝ) * P) := by
          rw [hk]
          congr 1
          push_cast
          ring
        _ = ray (t + (n : ℝ) * P) := hnatPeriod _ hn k
  have hpathContinuous : Continuous path := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt ((tailStart - t) / P)
    have htstrict : tailStart < t + (n : ℝ) * P := by
      have hmul : tailStart - t < (n : ℝ) * P :=
        (div_lt_iff₀ hPpos).mp hn
      linarith
    have htranslate : Continuous (fun s : ℝ => s + (n : ℝ) * P) :=
      continuous_id.add continuous_const
    have hopen : IsOpen {s : ℝ | tailStart < s + (n : ℝ) * P} :=
      isOpen_lt continuous_const htranslate
    have hlocal :
        (fun s : ℝ => ray (s + (n : ℝ) * P)) =ᶠ[𝓝 t] path := by
      filter_upwards [hopen.mem_nhds htstrict] with s hs
      exact (hpath_eq_shift s n hs.le).symm
    exact (hray.comp htranslate).continuousAt.congr hlocal
  have hpathPeriodic : ∀ t : ℝ, path (t + P) = path t := by
    intro t
    obtain ⟨n, hn⟩ := hexistsShift (t + P)
    have hn' : tailStart ≤ t + ((n + 1 : ℕ) : ℝ) * P := by
      convert hn using 1 <;> push_cast <;> ring
    calc
      path (t + P) = ray ((t + P) + (n : ℝ) * P) :=
        hpath_eq_shift (t + P) n hn
      _ = ray (t + ((n + 1 : ℕ) : ℝ) * P) := by
        congr 1
        push_cast
        ring
      _ = path t := (hpath_eq_shift t (n + 1) hn').symm
  have hagree : ∀ t : ℝ, tailStart ≤ t → path t = ray t := by
    intro t ht
    simpa using hpath_eq_shift t 0 (by simpa using ht)
  exact ⟨path, hPpos, hpathContinuous, hpathPeriodic,
    tailStart, htailStart, hagree⟩

private theorem finiteUnitSpeedPieces_translate
    {f g : ℝ → I} {a b shift : ℝ}
    (hpieces : HasFiniteUnitSpeedPiecesOn f (a + shift) (b + shift))
    (heq : ∀ t ∈ Set.Icc a b, g t = f (t + shift)) :
    HasFiniteUnitSpeedPiecesOn g a b := by
  rcases hpieces with ⟨K, haK, hbK, hKbounds, hlinear⟩
  let K' : Finset ℝ := K.image (fun t => t - shift)
  refine ⟨K', ?_, ?_, ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨a + shift, haK, by ring⟩
  · apply Finset.mem_image.mpr
    exact ⟨b + shift, hbK, by ring⟩
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨u, huK, rfl⟩
    have hu := hKbounds u huK
    constructor
    · linarith [hu.1]
    · linarith [hu.2]
  · intro x y hxy
    have hxImage := hxy.1
    have hyImage := hxy.2.1
    rcases Finset.mem_image.mp hxImage with ⟨x', hx'K, hx'eq⟩
    rcases Finset.mem_image.mp hyImage with ⟨y', hy'K, hy'eq⟩
    have hx' : x' = x + shift := by linarith
    have hy' : y' = y + shift := by linarith
    subst x'
    subst y'
    have hAdj : AdjacentParameterVertices K (x + shift) (y + shift) := by
      refine ⟨hx'K, hy'K, by linarith [hxy.2.2.1], ?_⟩
      intro z hzK hzbetween
      exact hxy.2.2.2 (z - shift)
        (Finset.mem_image.mpr ⟨z, hzK, rfl⟩)
        ⟨by linarith [hzbetween.1], by linarith [hzbetween.2]⟩
    obtain ⟨m, c, hm, hformula⟩ := hlinear hAdj
    refine ⟨m, m * shift + c, hm, ?_⟩
    intro t ht
    have hxBounds := hKbounds (x + shift) hx'K
    have hyBounds := hKbounds (y + shift) hy'K
    have htAB : t ∈ Set.Icc a b := by
      constructor <;> linarith [hxBounds.1, hyBounds.2, ht.1, ht.2]
    have htShift : t + shift ∈ Set.Icc (x + shift) (y + shift) := by
      constructor <;> linarith [ht.1, ht.2]
    rw [heq t htAB]
    rw [hformula (t + shift) htShift]
    ring

/-- Local finite-piece unit speed passes from a late ray tail to its periodic
extension. -/
theorem periodic_tail_extension_unit_speed
    {ray path : ℝ → I} {P : ℝ}
    (hray : IsLocallyUnitSpeedRay ray)
    (hext : IsPeriodicTailExtension ray path P) :
    ∀ a b : ℝ, a < b → HasFiniteUnitSpeedPiecesOn path a b := by
  intro a b hab
  rcases hext.2.2.2 with ⟨tailStart, htailStart, hagree⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((tailStart - a) / P)
  have hPpos := hext.1
  have hlateA : tailStart ≤ a + (n : ℝ) * P := by
    have hmul : tailStart - a < (n : ℝ) * P :=
      (div_lt_iff₀ hPpos).mp hn
    linarith
  have hperiodNat (t : ℝ) :
      ∀ k : ℕ, path (t + (k : ℝ) * P) = path t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          path (t + ((k + 1 : ℕ) : ℝ) * P) =
              path ((t + (k : ℝ) * P) + P) := by
            congr 1
            push_cast
            ring
          _ = path (t + (k : ℝ) * P) := hext.2.2.1 _
          _ = path t := ih
  have hpieces := hray.2 (a + (n : ℝ) * P) (b + (n : ℝ) * P)
    (htailStart.trans hlateA) (by linarith)
  apply finiteUnitSpeedPieces_translate hpieces
  intro t ht
  calc
    path t = path (t + (n : ℝ) * P) := (hperiodNat t n).symm
    _ = ray (t + (n : ℝ) * P) :=
      hagree _ (hlateA.trans (by linarith [ht.1]))

/-! ## Least period, integral scales, and globalization -/

/-- Additive group of all real periods of a path. -/
def pathPeriodGroup (path : ℝ → I) : AddSubgroup ℝ where
  carrier := {r | ∀ t : ℝ, path (t + r) = path t}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs t
    simpa [add_assoc] using (Eq.trans (hs (t + r)) (hr t))
  neg_mem' := by
    intro r hr t
    have h := (hr (t - r)).symm
    simpa [sub_eq_add_neg, add_assoc] using h

/-- The displayed period is the least positive element of the period group. -/
def HasLeastPositivePeriod (path : ℝ → I) (P : ℝ) : Prop :=
  0 < P ∧ P ∈ pathPeriodGroup path ∧
    ∀ r : ℝ, 0 < r → r ∈ pathPeriodGroup path → P ≤ r

/-- A continuous nonconstant path with a positive period has a least positive
period; equivalently its closed period group is nondense cyclic. -/
theorem periodic_nonconstant_path_has_least_period
    {path : ℝ → I} {P : ℝ}
    (hcontinuous : Continuous path)
    (hnonconstant : ¬ ∀ x y : ℝ, path x = path y)
    (hPpos : 0 < P)
    (hP : P ∈ pathPeriodGroup path) :
    ∃ P₀ : ℝ, HasLeastPositivePeriod path P₀ := by
  let S : AddSubgroup ℝ := pathPeriodGroup path
  have hSnontrivial : S ≠ ⊥ := by
    intro hS
    have hPzero : P = 0 := by
      have : P ∈ (⊥ : AddSubgroup ℝ) := by simpa [S, hS] using hP
      simpa using this
    exact hPpos.ne' hPzero
  have hSnotDense : ¬Dense (S : Set ℝ) := by
    intro hSdense
    apply hnonconstant
    intro x y
    let E : Set ℝ := {r | path (x + r) = path x}
    have hEclosed : IsClosed E := by
      exact isClosed_eq
        (hcontinuous.comp (continuous_const.add continuous_id)) continuous_const
    have hSE : (S : Set ℝ) ⊆ E := by
      intro r hr
      exact hr x
    have hyrClosure : y - x ∈ closure (S : Set ℝ) := by
      rw [hSdense.closure_eq]
      exact Set.mem_univ _
    have hyr : y - x ∈ E := (closure_minimal hSE hEclosed) hyrClosure
    change path (x + (y - x)) = path x at hyr
    simpa using hyr.symm
  have hleastExists :
      ∃ P₀ : ℝ, IsLeast {r : ℝ | r ∈ S ∧ 0 < r} P₀ := by
    by_contra hnone
    exact hSnotDense (S.dense_of_no_min hSnontrivial hnone)
  rcases hleastExists with ⟨P₀, ⟨hP₀mem, hP₀pos⟩, hleast⟩
  exact ⟨P₀, hP₀pos, hP₀mem,
    fun r hrpos hrmem => hleast ⟨hrmem, hrpos⟩⟩

/-- The full period group of a path with a least positive period is the
integer span of that period. -/
theorem path_periodGroup_eq_integer_multiples
    {path : ℝ → I} {P : ℝ}
    (hleast : HasLeastPositivePeriod path P) :
    ∀ r : ℝ, r ∈ pathPeriodGroup path ↔
      ∃ k : ℤ, r = (k : ℝ) * P := by
  intro r
  constructor
  · intro hr
    let k : ℤ := ⌊r / P⌋
    let s : ℝ := r - (k : ℝ) * P
    have hklo : (k : ℝ) ≤ r / P := Int.floor_le (r / P)
    have hkhi : r / P < (k : ℝ) + 1 := Int.lt_floor_add_one (r / P)
    have hmullo : (k : ℝ) * P ≤ r :=
      (le_div_iff₀ hleast.1).mp (by simpa [mul_comm] using hklo)
    have hmulhi : r < ((k : ℝ) + 1) * P :=
      (div_lt_iff₀ hleast.1).mp hkhi
    have hsnonneg : 0 ≤ s := by dsimp [s]; linarith
    have hslt : s < P := by dsimp [s]; linarith
    have hkperiod : (k : ℝ) * P ∈ pathPeriodGroup path := by
      simpa [zsmul_eq_mul] using
        (pathPeriodGroup path).zsmul_mem hleast.2.1 k
    have hsperiod : s ∈ pathPeriodGroup path := by
      simpa [s] using (pathPeriodGroup path).sub_mem hr hkperiod
    have hszero : s = 0 := by
      apply le_antisymm
      · apply le_of_not_gt
        intro hspos
        exact (not_le_of_gt hslt) (hleast.2.2 s hspos hsperiod)
      · exact hsnonneg
    exact ⟨k, by dsimp [s] at hszero; linarith⟩
  · rintro ⟨k, rfl⟩
    simpa [zsmul_eq_mul] using
      (pathPeriodGroup path).zsmul_mem hleast.2.1 k

/-- Dilation return for all real parameters. -/
def DilationReturns (path : ℝ → I) (scale : ℝ)
    (T : IntervalMap) : Prop :=
  ∀ t : ℝ, path (scale * t) = T (path t)

/-- Dilation return holding only for all sufficiently large parameters. -/
def EventuallyDilationReturns (path : ℝ → I) (scale : ℝ)
    (T : IntervalMap) : Prop :=
  ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → path (scale * t) = T (path t)

/-- Ray equivariance transfers to eventual equivariance of any periodic tail
extension. -/
theorem periodic_extension_eventually_returns
    {ray path : ℝ → I} {P scale : ℝ} {T : IntervalMap}
    (hscale : 0 < scale)
    (hext : IsPeriodicTailExtension ray path P)
    (hreturn : DilationReturnsOnRay ray scale T) :
    EventuallyDilationReturns path scale T := by
  rcases hext.2.2.2 with ⟨tailStart, htailStart, hagree⟩
  refine ⟨max tailStart (tailStart / scale), ?_⟩
  intro t ht
  have htTail : tailStart ≤ t :=
    le_trans (le_max_left _ _) ht
  have htNonnegative : 0 ≤ t := le_trans htailStart htTail
  have hscaledTail : tailStart ≤ scale * t := by
    have hdiv : tailStart / scale ≤ t :=
      le_trans (le_max_right _ _) ht
    have hmul : tailStart ≤ t * scale :=
      (div_le_iff₀ hscale).mp hdiv
    simpa [mul_comm] using hmul
  rw [hagree (scale * t) hscaledTail, hreturn t htNonnegative,
    hagree t htTail]

/-- Eventual dilation equivariance makes the scaled least period another
period. -/
theorem scaled_least_period_is_period
    {path : ℝ → I} {P scale : ℝ} {T : IntervalMap}
    (hleast : HasLeastPositivePeriod path P)
    (hscale : 0 < scale)
    (hreturn : EventuallyDilationReturns path scale T) :
    scale * P ∈ pathPeriodGroup path := by
  rcases hreturn with ⟨T₀, hreturn⟩
  change ∀ t : ℝ, path (t + scale * P) = path t
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt ((scale * T₀ - t) / P)
  have hNPbig : scale * T₀ - t < (N : ℝ) * P :=
    (div_lt_iff₀ hleast.1).mp hN
  let u : ℝ := (t + (N : ℝ) * P) / scale
  have hu : T₀ ≤ u := by
    apply (le_div_iff₀ hscale).mpr
    dsimp [u]
    nlinarith
  have huP : T₀ ≤ u + P := hu.trans (le_add_of_nonneg_right hleast.1.le)
  have hscaleu : scale * u = t + (N : ℝ) * P := by
    dsimp [u]
    field_simp
  have hlate : path (scale * u + scale * P) = path (scale * u) := by
    calc
      path (scale * u + scale * P) = path (scale * (u + P)) := by ring_nf
      _ = T (path (u + P)) := hreturn (u + P) huP
      _ = T (path u) := congrArg T (hleast.2.1 u)
      _ = path (scale * u) := (hreturn u hu).symm
  have hNPperiod : ∀ x : ℝ,
      path (x + (N : ℝ) * P) = path x := by
    simpa [nsmul_eq_mul] using
      (pathPeriodGroup path).nsmul_mem hleast.2.1 N
  calc
    path (t + scale * P) =
        path ((t + scale * P) + (N : ℝ) * P) :=
      (hNPperiod (t + scale * P)).symm
    _ = path ((t + (N : ℝ) * P) + scale * P) := by ring_nf
    _ = path (scale * u + scale * P) := by rw [hscaleu]
    _ = path (scale * u) := hlate
    _ = path (t + (N : ℝ) * P) := by rw [hscaleu]
    _ = path t := hNPperiod t

/-- If an expanding dilation preserves a periodic path dynamically, its
scale is a positive natural number. -/
theorem expanding_return_scale_is_natural
    {path : ℝ → I} {P scale : ℝ} {T : IntervalMap}
    (hleast : HasLeastPositivePeriod path P)
    (hscale : 1 < scale)
    (hreturn : EventuallyDilationReturns path scale T) :
    ∃ n : ℕ, 1 < n ∧ scale = (n : ℝ) := by
  have hscaledPeriod : scale * P ∈ pathPeriodGroup path :=
    scaled_least_period_is_period hleast (lt_trans zero_lt_one hscale) hreturn
  obtain ⟨k, hk⟩ :=
    (path_periodGroup_eq_integer_multiples hleast (scale * P)).mp hscaledPeriod
  have hscale_eq : scale = (k : ℝ) := by
    apply mul_right_cancel₀ hleast.1.ne'
    exact hk
  have hk_nonneg_real : 0 ≤ (k : ℝ) := by
    rw [← hscale_eq]
    exact hscale.le.trans' zero_le_one
  have hk_nonneg : (0 : ℤ) ≤ k := by exact_mod_cast hk_nonneg_real
  let n : ℕ := k.toNat
  have hncast : (n : ℝ) = (k : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hk_nonneg)
  refine ⟨n, ?_, ?_⟩
  · have hnreal : (1 : ℝ) < (n : ℝ) := by
      rw [hncast, ← hscale_eq]
      exact hscale
    exact_mod_cast hnreal
  · rw [hscale_eq, hncast]

/-- Once the scale is integral, periodic continuation globalizes an eventual
dilation-return identity to all real parameters. -/
theorem eventual_return_global_of_natural_scale
    {path : ℝ → I} {P scale : ℝ} {T : IntervalMap}
    (hleast : HasLeastPositivePeriod path P)
    (hscale : ∃ n : ℕ, 0 < n ∧ scale = (n : ℝ))
    (hreturn : EventuallyDilationReturns path scale T) :
    DilationReturns path scale T := by
  obtain ⟨n, hn, rfl⟩ := hscale
  rcases hreturn with ⟨T₀, hreturn⟩
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt ((T₀ - t) / P)
  have hNPbig : T₀ - t < (N : ℝ) * P :=
    (div_lt_iff₀ hleast.1).mp hN
  have htlate : T₀ ≤ t + (N : ℝ) * P := by linarith
  have hNPperiod : path (t + (N : ℝ) * P) = path t := by
    have hmem := (pathPeriodGroup path).nsmul_mem hleast.2.1 N
    simpa [pathPeriodGroup, nsmul_eq_mul] using hmem t
  have hnNPperiod :
      path ((n : ℝ) * t + ((n * N : ℕ) : ℝ) * P) =
        path ((n : ℝ) * t) := by
    have hmem := (pathPeriodGroup path).nsmul_mem hleast.2.1 (n * N)
    simpa [pathPeriodGroup, nsmul_eq_mul] using hmem ((n : ℝ) * t)
  calc
    path ((n : ℝ) * t) =
        path ((n : ℝ) * t + ((n * N : ℕ) : ℝ) * P) := hnNPperiod.symm
    _ = path ((n : ℝ) * (t + (N : ℝ) * P)) := by
      congr 1
      push_cast
      ring
    _ = T (path (t + (N : ℝ) * P)) := hreturn _ htlate
    _ = T (path t) := congrArg T hNPperiod

/-! ## Tail core and the final periodic return path -/

/-- Physical image of a ray after the cutoff `T`. -/
def rayTailImage (ray : ℝ → I) (T : ℝ) : Set I :=
  ray '' Set.Ici T

/-- Any forward-invariant set with nonempty relative interior is the whole
interval under an exact interval map. -/
theorem forward_invariant_set_eq_univ_of_exact
    {R : IntervalMap} {J : Set I}
    (hexact : IsTopologicallyExact R)
    (hinterior : (interior J).Nonempty)
    (hforward : MapsTo R J J) :
    J = Set.univ := by
  apply Set.Subset.antisymm (Set.subset_univ J)
  obtain ⟨n, hn⟩ := hexact (interior J) isOpen_interior hinterior
  intro y _
  have hy : y ∈ iterateMap R n '' interior J := by
    rw [hn]
    exact Set.mem_univ y
  rcases hy with ⟨x, hx, rfl⟩
  exact hforward.iterate n (interior_subset hx)

/-- A locally unit-speed ray cannot collapse any nontrivial late parameter
interval.  Connectedness of its tail therefore puts a nonempty open order
interval inside the physical tail image. -/
private theorem locallyUnitSpeedRay_tail_interior_nonempty
    {ray : ℝ → I} (hray : IsLocallyUnitSpeedRay ray)
    (T : ℝ) (hT : 0 ≤ T) :
    (interior (rayTailImage ray T)).Nonempty := by
  classical
  rcases hray.2 T (T + 1) hT (by linarith) with
    ⟨K, hTK, hTOneK, _hKbounds, hlinear⟩
  let later : Finset ℝ := K.filter (fun z => T < z)
  have hlater : later.Nonempty := by
    refine ⟨T + 1, ?_⟩
    simp only [later, Finset.mem_filter]
    exact ⟨hTOneK, by linarith⟩
  let y : ℝ := later.min' hlater
  have hyLater : y ∈ later := later.min'_mem hlater
  have hyK : y ∈ K := (Finset.mem_filter.mp hyLater).1
  have hTy : T < y := (Finset.mem_filter.mp hyLater).2
  have hAdjacent : AdjacentParameterVertices K T y := by
    refine ⟨hTK, hyK, hTy, ?_⟩
    intro z hzK hzBetween
    have hzLater : z ∈ later := by
      simp only [later, Finset.mem_filter]
      exact ⟨hzK, hzBetween.1⟩
    exact (not_lt_of_ge (later.min'_le z hzLater)) hzBetween.2
  rcases hlinear hAdjacent with ⟨m, c, hm, hformula⟩
  have hmne : m ≠ 0 := by
    intro hmzero
    subst m
    norm_num at hm
  have hvalues : ray T ≠ ray y := by
    intro heq
    have heqReal : (ray T : ℝ) = (ray y : ℝ) := congrArg Subtype.val heq
    rw [hformula T ⟨le_rfl, hTy.le⟩,
      hformula y ⟨hTy.le, le_rfl⟩] at heqReal
    have hmul : m * (T - y) = 0 := by linarith
    rcases mul_eq_zero.mp hmul with hmzero | hTyzero
    · exact hmne hmzero
    · exact (ne_of_lt hTy) (sub_eq_zero.mp hTyzero)
  have htailPreconnected : IsPreconnected (rayTailImage ray T) := by
    exact Set.ordConnected_Ici.isPreconnected.image ray hray.1.continuousOn
  have hTmem : ray T ∈ rayTailImage ray T :=
    ⟨T, Set.mem_Ici.mpr le_rfl, rfl⟩
  have hymem : ray y ∈ rayTailImage ray T :=
    ⟨y, Set.mem_Ici.mpr hTy.le, rfl⟩
  rcases lt_or_gt_of_ne hvalues with hlt | hgt
  · obtain ⟨z, hz⟩ := exists_between hlt
    refine ⟨z, (interior_maximal ?_ isOpen_Ioo) hz⟩
    intro w hw
    exact htailPreconnected.Icc_subset hTmem hymem ⟨hw.1.le, hw.2.le⟩
  · obtain ⟨z, hz⟩ := exists_between hgt
    refine ⟨z, (interior_maximal ?_ isOpen_Ioo) hz⟩
    intro w hw
    exact htailPreconnected.Icc_subset hymem hTmem ⟨hw.1.le, hw.2.le⟩

/-- The periodic tail image has nonempty interior and is forward invariant
under the product return map. -/
theorem periodic_tail_core_package
    {ray path : ℝ → I} {P scale : ℝ} {R : IntervalMap}
    (hray : IsLocallyUnitSpeedRay ray)
    (hscale : 1 < scale)
    (hext : IsPeriodicTailExtension ray path P)
    (hreturn : DilationReturnsOnRay ray scale R) :
    ∃ T : ℝ, 0 ≤ T ∧
      (interior (rayTailImage ray T)).Nonempty ∧
      MapsTo R (rayTailImage ray T) (rayTailImage ray T) ∧
      Set.range path = rayTailImage ray T := by
  rcases hext.2.2.2 with ⟨tailStart, htailStart, hagree⟩
  have hPpos := hext.1
  have hperiodNat (t : ℝ) :
      ∀ n : ℕ, path (t + (n : ℝ) * P) = path t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          path (t + ((n + 1 : ℕ) : ℝ) * P) =
              path ((t + (n : ℝ) * P) + P) := by
            congr 1
            push_cast
            ring
          _ = path (t + (n : ℝ) * P) := hext.2.2.1 _
          _ = path t := ih
  have hrange : Set.range path = rayTailImage ray tailStart := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, rfl⟩
      obtain ⟨n, hn⟩ := exists_nat_gt ((tailStart - t) / P)
      have hlate : tailStart ≤ t + (n : ℝ) * P := by
        have hmul : tailStart - t < (n : ℝ) * P :=
          (div_lt_iff₀ hPpos).mp hn
        linarith
      refine ⟨t + (n : ℝ) * P, hlate, ?_⟩
      calc
        ray (t + (n : ℝ) * P) = path (t + (n : ℝ) * P) :=
          (hagree _ hlate).symm
        _ = path t := hperiodNat t n
    · rintro z ⟨t, ht, rfl⟩
      exact ⟨t, hagree t ht⟩
  refine ⟨tailStart, htailStart,
    locallyUnitSpeedRay_tail_interior_nonempty hray tailStart htailStart,
    ?_, hrange⟩
  rintro z ⟨t, ht, rfl⟩
  have htTail : tailStart ≤ t := Set.mem_Ici.mp ht
  have ht0 : 0 ≤ t := htailStart.trans htTail
  have hscaledLate : tailStart ≤ scale * t := by
    have hnonneg : 0 ≤ (scale - 1) * t :=
      mul_nonneg (sub_nonneg.mpr hscale.le) ht0
    have htscaled : t ≤ scale * t := by nlinarith
    exact htTail.trans htscaled
  exact ⟨scale * t, hscaledLate, hreturn t ht0⟩

/-- Exactness makes the physical image of the periodic tail, hence the range
of its periodic extension, the whole interval. -/
theorem periodic_tail_range_eq_univ_of_exact
    {ray path : ℝ → I} {P scale : ℝ} {R : IntervalMap}
    (hray : IsLocallyUnitSpeedRay ray)
    (hscale : 1 < scale)
    (hext : IsPeriodicTailExtension ray path P)
    (hreturn : DilationReturnsOnRay ray scale R)
    (hexact : IsTopologicallyExact R) :
    Set.range path = Set.univ := by
  rcases periodic_tail_core_package hray hscale hext hreturn with
    ⟨tailStart, _htailStart, hinterior, hforward, hrange⟩
  rw [hrange]
  exact forward_invariant_set_eq_univ_of_exact hexact hinterior hforward

/-- An onto, finite-piece PL, unit-speed path with least positive period. -/
def IsOntoUnitSpeedPeriodicPath (path : ℝ → I) (P : ℝ) : Prop :=
  Continuous path ∧ Function.Surjective path ∧
    HasLeastPositivePeriod path P ∧
    ∀ a b : ℝ, a < b → HasFiniteUnitSpeedPiecesOn path a b

/-- Final output of Section 6: a least-period unit-speed circle path carrying
the two expanding return maps. -/
structure PeriodicReturnPathPackage
    (A B : IntervalMap) (a b : ℝ) where
  /-- Periodic lift of the circle path. -/
  path : ℝ → I
  /-- Least positive period. -/
  period : ℝ
  /-- Continuity, surjectivity, unit speed, and least-period property. -/
  path_spec : IsOntoUnitSpeedPeriodicPath path period
  /-- The first scale is a natural number strictly bigger than one. -/
  scaleA_natural : ∃ m : ℕ, 1 < m ∧ a = (m : ℝ)
  /-- The second scale is a natural number strictly bigger than one. -/
  scaleB_natural : ∃ n : ℕ, 1 < n ∧ b = (n : ℝ)
  /-- Exact `A` return equation on the periodic lift. -/
  returnA : DilationReturns path a A
  /-- Exact `B` return equation on the periodic lift. -/
  returnB : DilationReturns path b B

/-- The ray return equations combine to the product return equation. -/
theorem product_dilation_returns_on_ray
    {A B R : IntervalMap} {ray : ℝ → I} {a b : ℝ}
    (hb : 0 < b)
    (hA : DilationReturnsOnRay ray a A)
    (hB : DilationReturnsOnRay ray b B)
    (hR : R = A ∘ B) :
    DilationReturnsOnRay ray (a * b) R := by
  intro t ht
  have hbt : 0 ≤ b * t := mul_nonneg (le_of_lt hb) ht
  calc
    ray ((a * b) * t) = ray (a * (b * t)) := by rw [mul_assoc]
    _ = A (ray (b * t)) := hA (b * t) hbt
    _ = A (B (ray t)) := congrArg A (hB t ht)
    _ = R (ray t) := by simp [hR]

end

end CommutingInterval
