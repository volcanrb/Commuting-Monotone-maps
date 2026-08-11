import CommutingIntervalSimplified.Base
import CommutingIntervalSimplified.PolygonalBase
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Stream.Init

/-!
# Standalone symbolic and directed-edge definitions

This module contains only the finite-word, substitution, Markov-edge, metric,
and common-growing-presentation vocabulary used by the simplified C1--C8
coding route.  It deliberately contains no primitive-substitution,
Perron-number, return-word, or recurrence machinery.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

universe u v

/-- A finite word over `α`. -/
abbrev Word (α : Type u) := List α

/-- A one-sided infinite word over `α`. -/
abbrev InfiniteWord (α : Type u) := Stream' α

/-- A substitution with no empty letter image. -/
structure Substitution (α : Type u) where
  /-- The finite image word of a letter. -/
  image : α → Word α
  /-- Every image contains at least one output letter. -/
  image_ne_nil : ∀ a, image a ≠ []

namespace Substitution

variable {α : Type u}

instance : CoeFun (Substitution α) fun _ => α → Word α :=
  ⟨Substitution.image⟩

/-- Extend a substitution from letters to finite words by concatenation. -/
def mapWord (σ : Substitution α) (w : Word α) : Word α :=
  w.flatMap σ

@[simp] theorem mapWord_nil (σ : Substitution α) : σ.mapWord [] = [] :=
  rfl

@[simp] theorem mapWord_cons (σ : Substitution α) (a : α) (w : Word α) :
    σ.mapWord (a :: w) = σ a ++ σ.mapWord w :=
  rfl

@[simp] theorem mapWord_append (σ : Substitution α) (u v : Word α) :
    σ.mapWord (u ++ v) = σ.mapWord u ++ σ.mapWord v := by
  simp [mapWord]

theorem mapWord_prefix {σ : Substitution α} {u v : Word α} (h : u <+: v) :
    σ.mapWord u <+: σ.mapWord v :=
  h.flatMap σ

theorem mapWord_ne_nil (σ : Substitution α) {w : Word α} (hw : w ≠ []) :
    σ.mapWord w ≠ [] := by
  obtain ⟨a, u, rfl⟩ := List.exists_cons_of_ne_nil hw
  simp only [mapWord_cons]
  exact List.append_ne_nil_of_left_ne_nil (σ.image_ne_nil a) _

/-- The `n`-fold substitution action on a finite word. -/
def iterateWord (σ : Substitution α) : ℕ → Word α → Word α
  | 0, w => w
  | n + 1, w => σ.mapWord (σ.iterateWord n w)

/-- The `n`-th substituted image of a single letter. -/
def iterateLetter (σ : Substitution α) (n : ℕ) (a : α) : Word α :=
  σ.iterateWord n [a]

@[simp] theorem iterateWord_zero (σ : Substitution α) (w : Word α) :
    σ.iterateWord 0 w = w :=
  rfl

@[simp] theorem iterateWord_succ (σ : Substitution α) (n : ℕ) (w : Word α) :
    σ.iterateWord (n + 1) w = σ.mapWord (σ.iterateWord n w) :=
  rfl

@[simp] theorem iterateLetter_zero (σ : Substitution α) (a : α) :
    σ.iterateLetter 0 a = [a] :=
  rfl

@[simp] theorem iterateLetter_succ (σ : Substitution α) (n : ℕ) (a : α) :
    σ.iterateLetter (n + 1) a = σ.mapWord (σ.iterateLetter n a) :=
  rfl

theorem iterateWord_ne_nil (σ : Substitution α) (n : ℕ) {w : Word α}
    (hw : w ≠ []) : σ.iterateWord n w ≠ [] := by
  induction n with
  | zero => exact hw
  | succ n ih => exact σ.mapWord_ne_nil ih

theorem iterateLetter_ne_nil (σ : Substitution α) (n : ℕ) (a : α) :
    σ.iterateLetter n a ≠ [] :=
  σ.iterateWord_ne_nil n (by simp)

/-- The identity nonerasing substitution. -/
def id : Substitution α where
  image a := [a]
  image_ne_nil _ := by simp

/-- Composition, with `(σ.comp τ)(a)` meaning first apply `τ`, then `σ`. -/
def comp (σ τ : Substitution α) : Substitution α where
  image a := σ.mapWord (τ a)
  image_ne_nil a := σ.mapWord_ne_nil (τ.image_ne_nil a)

@[simp] theorem id_apply (a : α) : (Substitution.id : Substitution α) a = [a] :=
  rfl

@[simp] theorem comp_apply (σ τ : Substitution α) (a : α) :
    (σ.comp τ) a = σ.mapWord (τ a) :=
  rfl

/-- A letter image starts with its generating letter and has a nonempty tail.
For a nonerasing substitution this is the growing form of prolongability used
for the directed-edge fixed words in the manuscript. -/
def ProlongableOn (σ : Substitution α) (a : α) : Prop :=
  ∃ tail : Word α, tail ≠ [] ∧ σ a = a :: tail

theorem iterateLetter_prefix_succ {σ : Substitution α} {a : α}
    (h : σ.ProlongableOn a) (n : ℕ) :
    σ.iterateLetter n a <+: σ.iterateLetter (n + 1) a := by
  obtain ⟨tail, _, himage⟩ := h
  induction n with
  | zero =>
      simp [iterateLetter, iterateWord, mapWord, himage]
  | succ n ih =>
      simpa only [iterateLetter_succ] using Substitution.mapWord_prefix ih

/-- A letter occurs in a finite word. -/
def OccursInWord (a : α) (w : Word α) : Prop :=
  a ∈ w

/-- The finite set of letters occurring in a finite word. -/
def AlphabetOfWord [DecidableEq α] (w : Word α) : Finset α :=
  w.toFinset

@[simp] theorem mem_alphabetOfWord_iff [DecidableEq α] (a : α) (w : Word α) :
    a ∈ AlphabetOfWord w ↔ OccursInWord a w := by
  simp [AlphabetOfWord, OccursInWord]

/-- A letter is reachable from `seed` if it occurs in some iterated image. -/
def OccursFrom (σ : Substitution α) (seed a : α) : Prop :=
  ∃ n : ℕ, OccursInWord a (σ.iterateLetter n seed)

/-- The alphabet generated by repeated substitution from `seed`. -/
def GeneratedAlphabet (σ : Substitution α) (seed : α) : Set α :=
  {a | σ.OccursFrom seed a}

/-- Every alphabet letter eventually occurs in an image of `seed`. -/
def IsGeneratingLetter (σ : Substitution α) (seed : α) : Prop :=
  ∀ a, σ.OccursFrom seed a

private structure ConcatState (α : Type u) where
  current : α
  blockTail : Word α
  remainingInput : InfiniteWord α

/-- First letter of the nonempty image block. -/
def imageHead (σ : Substitution α) (a : α) : α :=
  (σ a).head (σ.image_ne_nil a)

/-- The part of the image block after its first letter. -/
def imageTail (σ : Substitution α) (a : α) : Word α :=
  (σ a).tail

theorem imageHead_cons_imageTail (σ : Substitution α) (a : α) :
    σ.imageHead a :: σ.imageTail a = σ a :=
  List.cons_head_tail (σ.image_ne_nil a)

private def concatStep (σ : Substitution α) (state : ConcatState α) :
    ConcatState α :=
  match state.blockTail with
  | b :: rest => ⟨b, rest, state.remainingInput⟩
  | [] =>
      let a := state.remainingInput.head
      ⟨σ.imageHead a, σ.imageTail a, state.remainingInput.tail⟩

private def concatRun (σ : Substitution α) (state : ConcatState α) :
    InfiniteWord α :=
  Stream'.corec ConcatState.current (concatStep σ) state

private theorem concatRun_eq_cons (σ : Substitution α) (state : ConcatState α) :
    concatRun σ state =
      Stream'.cons state.current (concatRun σ (concatStep σ state)) :=
  Stream'.corec_eq _ _ _

private theorem take_concatRun_currentBlock (σ : Substitution α)
    (current : α) (blockTail : Word α) (remainingInput : InfiniteWord α) :
    (concatRun σ ⟨current, blockTail, remainingInput⟩).take (blockTail.length + 1) =
      current :: blockTail := by
  induction blockTail generalizing current with
  | nil =>
      rw [concatRun_eq_cons]
      rfl
  | cons next rest ih =>
      rw [concatRun_eq_cons]
      simpa only [List.length_cons, Stream'.take_succ_cons,
        concatStep] using congrArg (current :: ·) (ih next)

private theorem drop_concatRun_currentBlock (σ : Substitution α)
    (current : α) (blockTail : Word α) (remainingInput : InfiniteWord α) :
    (concatRun σ ⟨current, blockTail, remainingInput⟩).drop
        (blockTail.length + 1) =
      concatRun σ
        ⟨σ.imageHead remainingInput.head, σ.imageTail remainingInput.head,
          remainingInput.tail⟩ := by
  induction blockTail generalizing current with
  | nil =>
      rw [concatRun_eq_cons, Stream'.drop_succ, Stream'.tail_cons]
      rfl
  | cons next rest ih =>
      rw [concatRun_eq_cons, List.length_cons, Stream'.drop_succ,
        Stream'.tail_cons]
      simpa only [concatStep] using ih next

/--
The infinite concatenation
`σ(x 0) ++ σ(x 1) ++ σ(x 2) ++ ⋯`.

The current state stores a head letter and the unused tail of its finite image
block.  On exhausting that tail it loads the next (provably nonempty) image.
This makes the definition total precisely because `σ` is nonerasing.
-/
def mapInfinite (σ : Substitution α) (x : InfiniteWord α) : InfiniteWord α :=
  concatRun σ
    ⟨σ.imageHead x.head, σ.imageTail x.head, x.tail⟩

@[simp] theorem mapInfinite_zero (σ : Substitution α) (x : InfiniteWord α) :
    σ.mapInfinite x 0 = σ.imageHead x.head :=
  rfl

theorem take_mapInfinite_first_image (σ : Substitution α) (x : InfiniteWord α) :
    (σ.mapInfinite x).take (σ x.head).length = σ x.head := by
  change
    (concatRun σ ⟨σ.imageHead x.head, σ.imageTail x.head, x.tail⟩).take
        (σ x.head).length = σ x.head
  rw [← imageHead_cons_imageTail]
  simpa using
    take_concatRun_currentBlock σ (σ.imageHead x.head) (σ.imageTail x.head) x.tail

theorem drop_mapInfinite_first_image (σ : Substitution α) (x : InfiniteWord α) :
    (σ.mapInfinite x).drop (σ x.head).length = σ.mapInfinite x.tail := by
  change
    (concatRun σ ⟨σ.imageHead x.head, σ.imageTail x.head, x.tail⟩).drop
        (σ x.head).length = σ.mapInfinite x.tail
  rw [← imageHead_cons_imageTail]
  simpa using
    drop_concatRun_currentBlock σ (σ.imageHead x.head) (σ.imageTail x.head) x.tail

/-- Infinite substitution is the first image block followed by substitution
of the input tail. -/
theorem mapInfinite_eq_append_first_image
    (σ : Substitution α) (x : InfiniteWord α) :
    σ.mapInfinite x = σ x.head ++ₛ σ.mapInfinite x.tail := by
  calc
    σ.mapInfinite x =
        (σ.mapInfinite x).take (σ x.head).length ++ₛ
          (σ.mapInfinite x).drop (σ x.head).length :=
      (Stream'.append_take_drop _ _).symm
    _ = σ x.head ++ₛ σ.mapInfinite x.tail := by
      rw [take_mapInfinite_first_image, drop_mapInfinite_first_image]

/-- A one-sided word is fixed when infinite concatenation of its substituted
letter images reproduces the word pointwise. -/
def IsFixedPoint (σ : Substitution α) (x : InfiniteWord α) : Prop :=
  σ.mapInfinite x = x

theorem isFixedPoint_iff (σ : Substitution α) (x : InfiniteWord α) :
    σ.IsFixedPoint x ↔ ∀ n, σ.mapInfinite x n = x n := by
  constructor
  · intro h n
    exact congrFun h n
  · intro h
    funext n
    exact h n

/-- A letter occurs in a one-sided infinite word. -/
def OccursInInfiniteWord (a : α) (x : InfiniteWord α) : Prop :=
  ∃ n : ℕ, x n = a

/-- The set of letters which actually occur in a one-sided word. -/
def OccurringAlphabet (x : InfiniteWord α) : Set α :=
  {a | OccursInInfiniteWord a x}

theorem mem_occurringAlphabet_iff (x : InfiniteWord α) (a : α) :
    a ∈ OccurringAlphabet x ↔ ∃ n, x n = a :=
  Iff.rfl

/-- Every letter image grows without bound under iteration. -/
def IsGrowing (σ : Substitution α) : Prop :=
  ∀ a : α, ∀ bound : ℕ, ∃ n : ℕ,
    bound ≤ (σ.iterateLetter n a).length

/-- The incidence matrix, with output letters indexing rows. -/
def incidenceMatrix [DecidableEq α] (σ : Substitution α) : Matrix α α ℕ :=
  fun output source => (σ source).count output

@[simp] theorem incidenceMatrix_apply [DecidableEq α]
    (σ : Substitution α) (output source : α) :
    σ.incidenceMatrix output source = (σ source).count output :=
  rfl

end Substitution

/-- A one-sided word is periodic after deleting a finite prefix. -/
def IsUltimatelyPeriodic {α : Type u} (x : InfiniteWord α) : Prop :=
  ∃ start period : ℕ, 0 < period ∧
    ∀ n : ℕ, start ≤ n → x (n + period) = x n

/--
Data witnessing simultaneous restriction of two substitutions to the letters
which actually occur in their common fixed word.
-/
structure OccurrenceAlphabetRestrictionData {α : Type u}
    (sourceA sourceB : Substitution α) (x : InfiniteWord α) where
  substitutionA : Substitution (Substitution.OccurringAlphabet x)
  substitutionB : Substitution (Substitution.OccurringAlphabet x)
  word : InfiniteWord (Substitution.OccurringAlphabet x)
  forget_word : ∀ n : ℕ, (word n).1 = x n
  imageA_forget : ∀ a,
    (substitutionA a).map Subtype.val = sourceA a.1
  imageB_forget : ∀ a,
    (substitutionB a).map Subtype.val = sourceB a.1
  fixedA : substitutionA.IsFixedPoint word
  fixedB : substitutionB.IsFixedPoint word
  every_letter_occurs : ∀ a,
    Substitution.OccursInInfiniteWord a word

end Symbolic

open Function Set
open scoped BigOperators

noncomputable section

/-- Consecutive vertices in a finite subset of the interval.  This is the
small definition formerly supplied by the broad polygonal module. -/
def FinsetAdjacent (K : Finset I) (x y : I) : Prop :=
  x ∈ K ∧ y ∈ K ∧ x < y ∧ ∀ z ∈ K, ¬(x < z ∧ z < y)

/-- An interval map is strict in one of the two orientations on a set. -/
def IsStrictlyMonotoneOn (T : IntervalMap) (s : Set I) : Prop :=
  StrictMonoOn T s ∨ StrictAntiOn T s

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

/-- A complex eigenvalue of a finite nonnegative integral matrix. -/
def IsComplexEigenvalue {α : Type*} [Fintype α]
    (M : Matrix α α ℕ) (z : ℂ) : Prop :=
  ∃ v : α → ℂ, v ≠ 0 ∧
    ∀ i : α, (∑ j : α, (M i j : ℂ) * v j) = z * v i

/-- A real eigenvalue dominates every complex eigenvalue in modulus. -/
def IsDominantEigenvalue {α : Type*} [Fintype α]
    (M : Matrix α α ℕ) (eigenvalue : ℝ) : Prop :=
  IsComplexEigenvalue M (eigenvalue : ℂ) ∧
    ∀ z : ℂ, IsComplexEigenvalue M z → ‖z‖ ≤ eigenvalue

/--
The exact symbolic input required by the growing-substitution periodicity
theorem: two nonerasing growing substitutions, prolongable on the same
letter, fixing the same word in which every alphabet letter occurs, with
multiplicatively independent dominant eigenvalues.
-/
structure CommonGrowingFixedWordData
    (α : Type*) [Fintype α] [DecidableEq α] where
  substitutionA : Symbolic.Substitution α
  substitutionB : Symbolic.Substitution α
  seed : α
  word : Symbolic.InfiniteWord α
  fixedA : substitutionA.IsFixedPoint word
  fixedB : substitutionB.IsFixedPoint word
  prolongableA : substitutionA.ProlongableOn seed
  prolongableB : substitutionB.ProlongableOn seed
  every_letter_occurs : ∀ letter : α,
    Symbolic.Substitution.OccursInInfiniteWord letter word
  growingA : substitutionA.IsGrowing
  growingB : substitutionB.IsGrowing
  eigenvalueA : ℝ
  eigenvalueB : ℝ
  /-- The common geometric length of an occurring coding letter. -/
  letterLength : α → ℝ
  letterLength_pos : ∀ letter : α, 0 < letterLength letter
  scalesA : SubstitutionScalesLetterLengths substitutionA letterLength
    eigenvalueA
  scalesB : SubstitutionScalesLetterLengths substitutionB letterLength
    eigenvalueB
  one_lt_eigenvalueA : 1 < eigenvalueA
  one_lt_eigenvalueB : 1 < eigenvalueB
  dominantA : IsDominantEigenvalue substitutionA.incidenceMatrix eigenvalueA
  dominantB : IsDominantEigenvalue substitutionB.incidenceMatrix eigenvalueB
  eigenvalues_independent :
    MultiplicativelyIndependent eigenvalueA eigenvalueB

end

end CommutingIntervalSimplified
