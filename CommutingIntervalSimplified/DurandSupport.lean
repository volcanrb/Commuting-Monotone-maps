import CommutingIntervalSimplified.SymbolicBase
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.List.Rotate
import Mathlib.Data.Set.Finite.List
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# Generic symbolic support for the metric Durand specialization

This file contains the standalone symbolic theorem used at C7.  Its public
statement is the fixed-point specialization of Durand's Theorem 9: two
nonerasing growing substitutions with multiplicatively independent
dominating eigenvalues cannot fix the same aperiodic one-sided word.

The proof is split at the two genuine published-theorem boundaries:

* growth asymptotics plus multiplicative independence make the recurrent
  language syndetic;
* finiteness and repetition of induced return systems make that recurrent
  language periodic, unless positive powers of the two growth constants are
  equal.

Everything after those two comparison steps is elementary finite-word
combinatorics and is proved here explicitly.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

open Function Set Filter Topology
open scoped BigOperators

noncomputable section

universe u v

/-! ## D0: fixed presentations and their canonical prefixes -/

/-- One of the two purely substitutive presentations in Durand's theorem.
`nonerasing` is displayed because it is a published hypothesis, although it
is also a field of `Substitution`. -/
structure GrowingFixedPresentation {α : Type u}
    [Fintype α] [DecidableEq α]
    (σ : Substitution α) (seed : α) (word : InfiniteWord α)
    (eigenvalue : ℝ) : Prop where
  nonerasing : ∀ letter, σ letter ≠ []
  prolongable : σ.ProlongableOn seed
  fixed : σ.IsFixedPoint word
  every_letter_occurs : ∀ letter,
    Substitution.OccursInInfiniteWord letter word
  growing : σ.IsGrowing
  one_lt_eigenvalue : 1 < eigenvalue
  dominant : IsDominantEigenvalue σ.incidenceMatrix eigenvalue

private theorem mapInfinite_append_stream
    {α : Type u} (σ : Substitution α) (finitePrefix : Word α)
    (word : InfiniteWord α) :
    σ.mapInfinite (finitePrefix ++ₛ word) =
      σ.mapWord finitePrefix ++ₛ σ.mapInfinite word := by
  induction finitePrefix with
  | nil => rfl
  | cons letter rest ih =>
      rw [Stream'.cons_append_stream, σ.mapInfinite_eq_append_first_image,
        Stream'.head_cons, Stream'.tail_cons, ih, σ.mapWord_cons,
        Stream'.append_append_stream]

/-- Iterated images of the head of any fixed point are the corresponding
finite prefixes.  This removes a harmless presentational mismatch: the
published theorem names a prolongable initial letter, whereas a fixed word
itself canonically supplies its head. -/
theorem iterateLetter_eq_fixedPoint_prefix
    {α : Type u} {σ : Substitution α} {word : InfiniteWord α}
    (hfixed : σ.IsFixedPoint word) :
    ∀ n : ℕ, σ.iterateLetter n word.head =
      word.take (σ.iterateLetter n word.head).length := by
  intro n
  induction n with
  | zero =>
      change [word.head] = word.take 1
      rw [Stream'.take_succ]
      rfl
  | succ n ih =>
      rw [Substitution.iterateLetter_succ, ih]
      let image := σ.mapWord
        (word.take (σ.iterateLetter n word.head).length)
      have hwhole : image ++ₛ σ.mapInfinite
          (word.drop (σ.iterateLetter n word.head).length) = word := by
        calc
          image ++ₛ σ.mapInfinite
              (word.drop (σ.iterateLetter n word.head).length) =
              σ.mapInfinite
                (word.take (σ.iterateLetter n word.head).length ++ₛ
                  word.drop (σ.iterateLetter n word.head).length) :=
            (mapInfinite_append_stream σ _ _).symm
          _ = σ.mapInfinite word := by rw [Stream'.append_take_drop]
          _ = word := hfixed
      have htake := congrArg (fun stream : InfiniteWord α =>
        stream.take image.length) hwhole
      change image = word.take image.length
      have hleft :
          (image ++ₛ σ.mapInfinite
            (word.drop (σ.iterateLetter n word.head).length)).take
              image.length = image := by
        simpa using Stream'.take_append_of_le_length
          (x := image)
          (a := σ.mapInfinite
            (word.drop (σ.iterateLetter n word.head).length))
          (n := image.length) le_rfl
      exact hleft.symm.trans htake

/-- Growth rules out a singleton image at the head of a fixed point, so the
head is itself a valid prolongation letter. -/
theorem prolongableOn_head_of_growing_fixedPoint
    {α : Type u} {σ : Substitution α} {word : InfiniteWord α}
    (hfixed : σ.IsFixedPoint word) (hgrowing : σ.IsGrowing) :
    σ.ProlongableOn word.head := by
  have hhead : σ.imageHead word.head = word.head := by
    have hzero := congrFun hfixed 0
    simpa using hzero
  have himageHead : (σ word.head).head (σ.image_ne_nil word.head) = word.head := by
    simpa [Substitution.imageHead] using hhead
  have hlength : 1 < (σ word.head).length := by
    by_contra hnot
    have hle : (σ word.head).length ≤ 1 := Nat.le_of_not_gt hnot
    have hpos : 0 < (σ word.head).length :=
      List.length_pos_of_ne_nil (σ.image_ne_nil word.head)
    have hone : (σ word.head).length = 1 := by omega
    have himage : σ word.head = [word.head] := by
      obtain ⟨letter, hletter⟩ := List.length_eq_one_iff.mp hone
      have hletterEq : letter = word.head := by
        simpa [hletter] using himageHead
      exact hletter.trans (congrArg (fun a => [a]) hletterEq)
    have hiterate : ∀ n : ℕ, σ.iterateLetter n word.head = [word.head] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Substitution.iterateLetter_succ, ih]
          simp [Substitution.mapWord, himage]
    obtain ⟨n, hn⟩ := hgrowing word.head 2
    rw [hiterate n] at hn
    simp at hn
  refine ⟨σ.imageTail word.head, ?_, ?_⟩
  · intro hnil
    rw [← σ.imageHead_cons_imageTail, hnil] at hlength
    simp at hlength
  · rw [← σ.imageHead_cons_imageTail, hhead]

/-! ## D1: recurrent factors and the syndeticity boundary -/

/-- A finite word begins at a specified position of an infinite word. -/
def InfiniteFactorAt {α : Type u} (word : InfiniteWord α)
    (factor : Word α) (start : ℕ) : Prop :=
  (word.drop start).take factor.length = factor

/-- A finite factor of an infinite word. -/
def IsInfiniteFactor {α : Type u} (word : InfiniteWord α)
    (factor : Word α) : Prop :=
  ∃ start : ℕ, InfiniteFactorAt word factor start

/-- A finite word begins at arbitrarily late positions. -/
def IsRecurrentFactor {α : Type u} (word : InfiniteWord α)
    (factor : Word α) : Prop :=
  ∀ cutoff : ℕ, ∃ start : ℕ,
    cutoff ≤ start ∧ InfiniteFactorAt word factor start

/-- Every interval of one fixed length contains a starting position of the
given factor. -/
def AppearsWithBoundedGaps {α : Type u} (word : InfiniteWord α)
    (factor : Word α) : Prop :=
  ∃ gap : ℕ, 0 < gap ∧
    ∀ start : ℕ, ∃ offset : ℕ, offset ≤ gap ∧
      InfiniteFactorAt word factor (start + offset)

/-- Every recurrent factor occurs syndetically. -/
def RecurrentFactorsSyndetic {α : Type u}
    (word : InfiniteWord α) : Prop :=
  ∀ factor : Word α, IsRecurrentFactor word factor →
    AppearsWithBoundedGaps word factor

/-- A nonrecurrent factor is absent beyond one finite cutoff. -/
private theorem not_isRecurrentFactor_iff_eventually_absent
    {α : Type u} {word : InfiniteWord α} {factor : Word α} :
    ¬ IsRecurrentFactor word factor ↔
      ∃ cutoff : ℕ, ∀ start : ℕ, cutoff ≤ start →
        ¬ InfiniteFactorAt word factor start := by
  classical
  simp only [IsRecurrentFactor]
  push_neg
  rfl

/-- For each fixed length, every sufficiently late factor is recurrent. -/
theorem eventually_every_fixedLengthFactor_recurrent
    {α : Type u} [Fintype α] [DecidableEq α]
    (word : InfiniteWord α) (factorLength : ℕ) :
    ∃ cutoff : ℕ, ∀ start : ℕ, cutoff ≤ start →
      IsRecurrentFactor word ((word.drop start).take factorLength) := by
  classical
  have hchoice : ∀ factor : Word α, ∃ cutoff : ℕ,
      IsRecurrentFactor word factor ∨
        ∀ start : ℕ, cutoff ≤ start →
          ¬ InfiniteFactorAt word factor start := by
    intro factor
    by_cases hfactor : IsRecurrentFactor word factor
    · exact ⟨0, Or.inl hfactor⟩
    · obtain ⟨cutoff, hcutoff⟩ :=
        not_isRecurrentFactor_iff_eventually_absent.mp hfactor
      exact ⟨cutoff, Or.inr hcutoff⟩
  choose bound hbound using hchoice
  let words : Finset (Word α) :=
    (List.finite_length_eq α factorLength).toFinset
  let cutoff := words.sup bound
  refine ⟨cutoff, ?_⟩
  intro start hstart
  let factor := (word.drop start).take factorLength
  have hfactorLength : factor.length = factorLength := by simp [factor]
  have hfactorMem : factor ∈ words := by simp [words, hfactorLength]
  by_contra hnot
  have hboundLe : bound factor ≤ cutoff :=
    Finset.le_sup (f := bound) hfactorMem
  have habsent := (hbound factor).resolve_left hnot
  apply habsent start (hboundLe.trans hstart)
  simp [InfiniteFactorAt, factor]


/-- The occurring alphabet of length-`blockLength` windows.  Restricting to
actual factors is essential: the full formal higher-block alphabet would
contain unused letters and would not satisfy Durand's occurrence hypothesis. -/
def OccurringHigherBlock {α : Type u} (word : InfiniteWord α)
    (blockLength : ℕ) :=
  {block : Word α //
    block.length = blockLength ∧ IsInfiniteFactor word block}

noncomputable instance occurringHigherBlockFintype
    {α : Type u} [Fintype α] (word : InfiniteWord α)
    (blockLength : ℕ) :
    Fintype (OccurringHigherBlock word blockLength) := by
  let finiteBlocks :
      ({block : Word α |
        block.length = blockLength ∧ IsInfiniteFactor word block}).Finite :=
    (List.finite_length_eq α blockLength).subset (fun _ h ↦ h.1)
  exact finiteBlocks.fintype

noncomputable instance occurringHigherBlockDecidableEq
    {α : Type u} [Fintype α] (word : InfiniteWord α)
    (blockLength : ℕ) :
    DecidableEq (OccurringHigherBlock word blockLength) :=
  Classical.decEq _

/-- The word of successive occurring windows of a fixed length. -/
def higherBlockWord {α : Type u} (word : InfiniteWord α)
    (blockLength : ℕ) : InfiniteWord (OccurringHigherBlock word blockLength) :=
  fun start =>
    ⟨(word.drop start).take blockLength,
      by simp,
      ⟨start, by simp [InfiniteFactorAt]⟩⟩

/-- A letter appears at arbitrarily late positions. -/
def OccursInfinitelyOften {α : Type u} (word : InfiniteWord α)
    (letter : α) : Prop :=
  ∀ cutoff : ℕ, ∃ start : ℕ, cutoff ≤ start ∧ word start = letter

/-- A letter appears in every sufficiently short forward window. -/
def LetterAppearsWithBoundedGaps {α : Type u}
    (word : InfiniteWord α) (letter : α) : Prop :=
  ∃ gap : ℕ, 0 < gap ∧
    ∀ start : ℕ, ∃ offset : ℕ, offset ≤ gap ∧
      word (start + offset) = letter


/-- A recurrent factor is precisely a recurrent letter of its occurring
higher-block word. -/
theorem recurrentFactor_iff_higherBlockLetter
    {α : Type u} {word : InfiniteWord α} {factor : Word α}
    (hfactor : IsInfiniteFactor word factor) :
    IsRecurrentFactor word factor ↔
      OccursInfinitelyOften (higherBlockWord word factor.length)
        ⟨factor, rfl, hfactor⟩ := by
  constructor
  · intro hrecurrent cutoff
    obtain ⟨start, hstart, hat⟩ := hrecurrent cutoff
    refine ⟨start, hstart, ?_⟩
    apply Subtype.ext
    simpa [higherBlockWord, InfiniteFactorAt] using hat
  · intro hrecurrent cutoff
    obtain ⟨start, hstart, hat⟩ := hrecurrent cutoff
    refine ⟨start, hstart, ?_⟩
    have hvalue := congrArg Subtype.val hat
    simpa [higherBlockWord, InfiniteFactorAt] using hvalue

/-- Bounded gaps for a higher-block letter are exactly bounded gaps for its
underlying factor. -/
theorem higherBlockLetter_boundedGaps_iff
    {α : Type u} {word : InfiniteWord α} {factor : Word α}
    (hfactor : IsInfiniteFactor word factor) :
    LetterAppearsWithBoundedGaps
        (higherBlockWord word factor.length) ⟨factor, rfl, hfactor⟩ ↔
      AppearsWithBoundedGaps word factor := by
  constructor
  · rintro ⟨gap, hgap, hbounded⟩
    refine ⟨gap, hgap, ?_⟩
    intro start
    obtain ⟨offset, hoffset, hat⟩ := hbounded start
    refine ⟨offset, hoffset, ?_⟩
    have hvalue := congrArg Subtype.val hat
    simpa [higherBlockWord, InfiniteFactorAt] using hvalue
  · rintro ⟨gap, hgap, hbounded⟩
    refine ⟨gap, hgap, ?_⟩
    intro start
    obtain ⟨offset, hoffset, hat⟩ := hbounded start
    refine ⟨offset, hoffset, ?_⟩
    apply Subtype.ext
    simpa [higherBlockWord, InfiniteFactorAt] using hat


/-! ## D2: finite return comparison and periodic recurrent language -/

/-- The `n`-fold concatenation of a finite word. -/
def wordPower {α : Type u} (word : Word α) (n : ℕ) : Word α :=
  (List.replicate n word).flatten

@[simp] theorem wordPower_length {α : Type u} (word : Word α) (n : ℕ) :
    (wordPower word n).length = n * word.length := by
  simp [wordPower]

theorem wordPower_add {α : Type u} (word : Word α) (m n : ℕ) :
    wordPower word (m + n) = wordPower word m ++ wordPower word n := by
  unfold wordPower
  rw [List.replicate_add, List.flatten_append]

/-- Every finite power has the base-word length as a period. -/
theorem wordPower_hasPeriod {α : Type u} (word : Word α) (n : ℕ) :
    List.HasPeriod (wordPower word n) word.length := by
  induction n using Nat.twoStepInduction with
  | zero => simp [wordPower]
  | one =>
      apply List.hasPeriod_of_length_le
      simp
  | more n _ ih =>
      have hlength : word.length ≤ (wordPower word (n + 1)).length := by
        rw [wordPower_length]
        nlinarith
      have hperiod := ih.take_append word.length word.length
        (wordPower word (n + 1)) (dvd_refl _) hlength
      simpa [wordPower, List.replicate_succ] using hperiod

/-- A nonempty finite word which is not a proper power. -/
def IsPrimitiveFiniteWord {α : Type u} (word : Word α) : Prop :=
  word ≠ [] ∧
    ∀ base : Word α, ∀ exponent : ℕ, 1 < exponent →
      wordPower base exponent ≠ word

/-- The recurrent language contains every positive power of one primitive
word. -/
def HasPeriodicRecurrentLanguage {α : Type u}
    (word : InfiniteWord α) : Prop :=
  ∃ periodWord : Word α, IsPrimitiveFiniteWord periodWord ∧
    ∀ n : ℕ, 0 < n →
      IsRecurrentFactor word (wordPower periodWord n)

/-- A finite factor begins at a specified position of a finite ambient
word. -/
def FiniteFactorAt {α : Type u} (ambient factor : Word α)
    (start : ℕ) : Prop :=
  start + factor.length ≤ ambient.length ∧
    (ambient.drop start).take factor.length = factor

/-- A finite factor nested in a finite block occurrence gives the translated
occurrence in the ambient infinite word. -/
theorem InfiniteFactorAt.of_finiteFactorAt
    {α : Type u} {word : InfiniteWord α}
    {ambient factor : Word α} {start offset : ℕ}
    (hambient : InfiniteFactorAt word ambient start)
    (hfactor : FiniteFactorAt ambient factor offset) :
    InfiniteFactorAt word factor (start + offset) := by
  rcases hfactor with ⟨hfactorWithin, hfactorEq⟩
  have hoffsetLe : offset ≤ ambient.length := by omega
  have hfactorLeDrop : factor.length ≤ (ambient.drop offset).length := by
    simp only [List.length_drop]
    omega
  have hstream :
      ambient ++ₛ (word.drop start).drop ambient.length = word.drop start := by
    calc
      ambient ++ₛ (word.drop start).drop ambient.length =
          (word.drop start).take ambient.length ++ₛ
            (word.drop start).drop ambient.length := by rw [hambient]
      _ = word.drop start :=
        Stream'.append_take_drop ambient.length (word.drop start)
  have hdropped := congrArg (fun stream : InfiniteWord α =>
    stream.drop offset) hstream
  change Stream'.drop offset
      (ambient ++ₛ (word.drop start).drop ambient.length) =
    Stream'.drop offset (word.drop start) at hdropped
  rw [Stream'.drop_append_of_le_length
    (x := ambient)
    (a := (word.drop start).drop ambient.length)
    (n := offset) hoffsetLe] at hdropped
  have htaken := congrArg (fun stream : InfiniteWord α =>
    stream.take factor.length) hdropped
  change Stream'.take factor.length
      (ambient.drop offset ++ₛ
        (word.drop start).drop ambient.length) =
    Stream'.take factor.length ((word.drop start).drop offset) at htaken
  have hleft :
      (ambient.drop offset ++ₛ
        (word.drop start).drop ambient.length).take factor.length =
      (ambient.drop offset).take factor.length := by
    exact Stream'.take_append_of_le_length
      (x := ambient.drop offset)
      (a := (word.drop start).drop ambient.length)
      (n := factor.length) hfactorLeDrop
  rw [hleft, hfactorEq] at htaken
  rw [InfiniteFactorAt, ← Stream'.drop_drop]
  exact htaken.symm

/-- A nested infinite occurrence induces the corresponding finite occurrence
inside the ambient block. -/
theorem finiteFactorAt_of_nested_infiniteFactorAt
    {α : Type u} {word : InfiniteWord α}
    {ambient factor : Word α} {start offset : ℕ}
    (hambient : InfiniteFactorAt word ambient start)
    (hfactor : InfiniteFactorAt word factor (start + offset))
    (hwithin : offset + factor.length ≤ ambient.length) :
    FiniteFactorAt ambient factor offset := by
  refine ⟨hwithin, ?_⟩
  have htrunc :
      (word.drop start).take (offset + factor.length) =
        ambient.take (offset + factor.length) := by
    calc
      (word.drop start).take (offset + factor.length) =
          ((word.drop start).take ambient.length).take
            (offset + factor.length) := by
        simp [Stream'.take_take, hwithin]
      _ = ambient.take (offset + factor.length) := by rw [hambient]
  have hleft :
      (word.drop start).take offset = ambient.take offset := by
    calc
      (word.drop start).take offset =
          ((word.drop start).take (offset + factor.length)).take offset := by
        simp [Stream'.take_take]
      _ = (ambient.take (offset + factor.length)).take offset := by
        rw [htrunc]
      _ = ambient.take offset := by simp [List.take_take]
  rw [Stream'.take_add, List.take_add, hleft] at htrunc
  have htail :
      ((word.drop start).drop offset).take factor.length =
        (ambient.drop offset).take factor.length :=
    List.append_cancel_left htrunc
  have htranslated :
      ((word.drop start).drop offset).take factor.length = factor := by
    simpa [InfiniteFactorAt, Stream'.drop_drop] using hfactor
  exact htail.symm.trans htranslated

/-- A return word runs from one occurrence of a nonempty marker to the next,
with no intermediate occurrence. -/
def IsReturnWord {α : Type u} (word : InfiniteWord α)
    (marker returnWord : Word α) : Prop :=
  marker ≠ [] ∧ returnWord ≠ [] ∧
    IsInfiniteFactor word (returnWord ++ marker) ∧
    marker <+: returnWord ++ marker ∧
    ∀ start : ℕ, FiniteFactorAt (returnWord ++ marker) marker start ↔
      start = 0 ∨ start = returnWord.length

/-- The block between two consecutive marker occurrences is a return word. -/
theorem returnWord_between_consecutive_occurrences
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {first second : ℕ}
    (hmarker_nonempty : marker ≠ [])
    (hfirst : InfiniteFactorAt word marker first)
    (hsecond : InfiniteFactorAt word marker second)
    (hlt : first < second)
    (hconsecutive : ∀ position : ℕ,
      first < position → position < second →
        ¬ InfiniteFactorAt word marker position) :
    IsReturnWord word marker
      ((word.drop first).take (second - first)) := by
  let returnWord := (word.drop first).take (second - first)
  have hreturnLength : returnWord.length = second - first := by
    simp [returnWord]
  have hreturnNonempty : returnWord ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hreturnLength]
    omega
  have hdrop :
      (word.drop first).drop (second - first) = word.drop second := by
    rw [Stream'.drop_drop]
    congr 1
    omega
  have hblockAt :
      (word.drop first).take (returnWord ++ marker).length =
        returnWord ++ marker := by
    rw [List.length_append, hreturnLength, Stream'.take_add]
    rw [hdrop, hsecond]
  have hblockFactor : IsInfiniteFactor word (returnWord ++ marker) :=
    ⟨first, hblockAt⟩
  have hoverlap : marker <+: returnWord ++ marker := by
    have hlength : marker.length ≤ (returnWord ++ marker).length := by simp
    have hprefix := Stream'.take_prefix_take_left
      (a := word.drop first) (m := marker.length)
      (n := (returnWord ++ marker).length) hlength
    rw [hfirst, hblockAt] at hprefix
    exact hprefix
  refine ⟨hmarker_nonempty, hreturnNonempty, hblockFactor, hoverlap, ?_⟩
  intro start
  constructor
  · intro hfinite
    have hstartLe : start ≤ returnWord.length := by
      have hlength :
          start + marker.length ≤ returnWord.length + marker.length := by
        simpa only [List.length_append] using hfinite.1
      exact Nat.le_of_add_le_add_right hlength
    by_cases hzero : start = 0
    · exact Or.inl hzero
    by_cases hend : start = returnWord.length
    · exact Or.inr hend
    exfalso
    have hlocalPrefix :
        (word.drop first).take (start + marker.length) =
          (returnWord ++ marker).take (start + marker.length) := by
      calc
        (word.drop first).take (start + marker.length) =
            ((word.drop first).take (returnWord ++ marker).length).take
              (start + marker.length) := by
          simp [Stream'.take_take, hstartLe]
        _ = (returnWord ++ marker).take (start + marker.length) := by
          rw [hblockAt]
    have hlocalLeft :
        (word.drop first).take start =
          (returnWord ++ marker).take start := by
      calc
        (word.drop first).take start =
            ((word.drop first).take
              (start + marker.length)).take start := by
          simp [Stream'.take_take]
        _ = ((returnWord ++ marker).take
              (start + marker.length)).take start := by
          rw [hlocalPrefix]
        _ = (returnWord ++ marker).take start := by
          simp [List.take_take]
    rw [Stream'.take_add, List.take_add, hlocalLeft] at hlocalPrefix
    have htailEq :
        ((word.drop first).drop start).take marker.length =
          ((returnWord ++ marker).drop start).take marker.length :=
      List.append_cancel_left hlocalPrefix
    have htranslated : InfiniteFactorAt word marker (first + start) := by
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

/-- Uniform recurrence in the exact bounded-gap form used for return-word
decompositions. -/
def IsUniformlyRecurrent {α : Type u} (word : InfiniteWord α) : Prop :=
  ∀ factor : Word α, IsInfiniteFactor word factor →
    AppearsWithBoundedGaps word factor

theorem AppearsWithBoundedGaps.isRecurrentFactor
    {α : Type u} {word : InfiniteWord α} {factor : Word α}
    (hbounded : AppearsWithBoundedGaps word factor) :
    IsRecurrentFactor word factor := by
  rcases hbounded with ⟨gap, _hgap, hbounded⟩
  intro cutoff
  obtain ⟨offset, _hoffset, hfactor⟩ := hbounded cutoff
  exact ⟨cutoff + offset, Nat.le_add_right cutoff offset, hfactor⟩


/-- The finite set of all return words to one recurrent marker. -/
structure FiniteReturnWordData {α : Type u} [DecidableEq α]
    (word : InfiniteWord α) (marker : Word α) where
  returnWords : Finset (Word α)
  mem_returnWords_iff : ∀ returnWord,
    returnWord ∈ returnWords ↔ IsReturnWord word marker returnWord

/-- **D2b.1 (finite return words).** A nonempty recurrent marker in a
syndetic recurrent language has only finitely many return words. -/
theorem finiteReturnWordData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α} {marker : Word α}
    (hsyndetic : RecurrentFactorsSyndetic word)
    (hmarker : IsRecurrentFactor word marker)
    (hmarker_nonempty : marker ≠ []) :
    Nonempty (FiniteReturnWordData word marker) := by
  classical
  obtain ⟨gap, hgap, hbounded⟩ := hsyndetic marker hmarker
  have hreturnLength : ∀ returnWord : Word α,
      IsReturnWord word marker returnWord →
        returnWord.length ≤ gap + 1 := by
    intro returnWord hreturn
    obtain ⟨base, hblockAt⟩ := hreturn.2.2.1
    obtain ⟨offset, hoffset, hnextMarker⟩ := hbounded (base + 1)
    by_contra hnot
    have hgapLt : gap + 1 < returnWord.length := Nat.lt_of_not_ge hnot
    let localStart := 1 + offset
    have hlocalPos : 0 < localStart := by simp [localStart]
    have hlocalLt : localStart < returnWord.length := by
      dsimp [localStart]
      omega
    have htranslated :
        InfiniteFactorAt word marker (base + localStart) := by
      convert hnextMarker using 1 <;> simp [localStart, Nat.add_assoc]
    have hwithin :
        localStart + marker.length ≤ (returnWord ++ marker).length := by
      simp only [List.length_append]
      omega
    have hfinite := finiteFactorAt_of_nested_infiniteFactorAt
      hblockAt htranslated hwithin
    rcases (hreturn.2.2.2.2 localStart).mp hfinite with hzero | hend
    · omega
    · omega
  let candidates : Finset (Word α) :=
    (List.finite_length_le α (gap + 1)).toFinset.filter
      (fun returnWord => IsReturnWord word marker returnWord)
  refine ⟨{
    returnWords := candidates
    mem_returnWords_iff := ?_ }⟩
  intro returnWord
  simp only [candidates, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · exact fun h ↦ h.2
  · intro hreturn
    exact ⟨hreturnLength returnWord hreturn, hreturn⟩

/-- A concrete tiling of a uniformly recurrent word by its successive
return words to a marker at the origin. -/
structure ReturnDecomposition {α : Type u}
    (word : InfiniteWord α) (marker : Word α) (rank : ℕ) where
  rank_pos : 0 < rank
  marker_ne_nil : marker ≠ []
  marker_at_zero : InfiniteFactorAt word marker 0
  blocks : Fin rank → Word α
  blocks_injective : Function.Injective blocks
  blocks_are_returns : ∀ letter,
    IsReturnWord word marker (blocks letter)
  every_return_is_block : ∀ returnWord,
    IsReturnWord word marker returnWord →
      ∃ letter, blocks letter = returnWord
  derived : InfiniteWord (Fin rank)
  cut : ℕ → ℕ
  cut_zero : cut 0 = 0
  cut_succ : ∀ n,
    cut (n + 1) = cut n + (blocks (derived n)).length
  block_at_cut : ∀ n,
    InfiniteFactorAt word (blocks (derived n)) (cut n)

/-- **D2b.2 (return decomposition).** Enumerating the finite return set and
cutting at successive marker occurrences gives a unique derived word. -/
theorem returnDecomposition_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α} {marker : Word α}
    (huniform : IsUniformlyRecurrent word)
    (hmarker_nonempty : marker ≠ [])
    (hmarker_at_zero : InfiniteFactorAt word marker 0)
    (finiteReturns : FiniteReturnWordData word marker) :
    ∃ rank : ℕ, Nonempty (ReturnDecomposition word marker rank) := by
  classical
  have hmarkerFactor : IsInfiniteFactor word marker := ⟨0, hmarker_at_zero⟩
  obtain ⟨gap, _hgap, hbounded⟩ := huniform marker hmarkerFactor
  have hafter : ∀ start : ℕ, ∃ position : ℕ,
      start < position ∧ InfiniteFactorAt word marker position := by
    intro start
    obtain ⟨offset, _hoffset, hfactor⟩ := hbounded (start + 1)
    exact ⟨start + 1 + offset, by omega, hfactor⟩
  let next : ℕ → ℕ := fun start =>
    @Nat.find
      (fun position : ℕ =>
        start < position ∧ InfiniteFactorAt word marker position)
      (fun _ => Classical.propDecidable _)
      (hafter start)
  have hnext : ∀ start : ℕ,
      start < next start ∧ InfiniteFactorAt word marker (next start) := by
    intro start
    simpa only [next] using
      (@Nat.find_spec
        (fun position : ℕ =>
          start < position ∧ InfiniteFactorAt word marker position)
        (fun _ => Classical.propDecidable _)
        (hafter start))
  let cut : ℕ → ℕ := fun n =>
    Nat.rec 0 (fun _ previous => next previous) n
  have hcutZero : cut 0 = 0 := rfl
  have hcutSucc : ∀ n : ℕ, cut (n + 1) = next (cut n) := by
    intro n
    simp [cut]
  have hcutMarker : ∀ n : ℕ,
      InfiniteFactorAt word marker (cut n) := by
    intro n
    induction n with
    | zero => simpa [hcutZero] using hmarker_at_zero
    | succ n _ =>
        rw [hcutSucc]
        exact (hnext (cut n)).2
  have hcutLt : ∀ n : ℕ, cut n < cut (n + 1) := by
    intro n
    rw [hcutSucc]
    exact (hnext (cut n)).1
  let block : ℕ → Word α := fun n =>
    (word.drop (cut n)).take (cut (n + 1) - cut n)
  have hblockReturn : ∀ n : ℕ,
      IsReturnWord word marker (block n) := by
    intro n
    apply returnWord_between_consecutive_occurrences
      hmarker_nonempty (hcutMarker n) (hcutMarker (n + 1)) (hcutLt n)
    intro position hleft hright hposition
    have hpositionNext : position < next (cut n) := by
      rwa [← hcutSucc]
    have hpositionFind : position <
        @Nat.find
          (fun candidate : ℕ =>
            cut n < candidate ∧
              InfiniteFactorAt word marker candidate)
          (fun _ => Classical.propDecidable _)
          (hafter (cut n)) := by
      simpa only [next] using hpositionNext
    have hnot := @Nat.find_min
      (fun candidate : ℕ =>
        cut n < candidate ∧ InfiniteFactorAt word marker candidate)
      (fun _ => Classical.propDecidable _)
      (hafter (cut n)) position hpositionFind
    exact False.elim (hnot ⟨hleft, hposition⟩)
  let ReturnType :=
    {returnWord : Word α // IsReturnWord word marker returnWord}
  have hreturnFinite : Set.Finite
      {returnWord : Word α | IsReturnWord word marker returnWord} := by
    apply finiteReturns.returnWords.finite_toSet.subset
    intro returnWord hreturn
    exact (finiteReturns.mem_returnWords_iff returnWord).2 hreturn
  letI : Fintype ReturnType := hreturnFinite.fintype
  let rank := Fintype.card ReturnType
  let enumerate : ReturnType ≃ Fin rank := Fintype.equivFin ReturnType
  let actual : ℕ → ReturnType := fun n => ⟨block n, hblockReturn n⟩
  let derived : InfiniteWord (Fin rank) := fun n => enumerate (actual n)
  let blocks : Fin rank → Word α := fun letter => (enumerate.symm letter).1
  have hblocksActual : ∀ n : ℕ, blocks (derived n) = block n := by
    intro n
    simp [blocks, derived, actual]
  have hrankPos : 0 < rank := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨actual 0⟩
  refine ⟨rank, ⟨{
    rank_pos := hrankPos
    marker_ne_nil := hmarker_nonempty
    marker_at_zero := hmarker_at_zero
    blocks := blocks
    blocks_injective := ?_
    blocks_are_returns := ?_
    every_return_is_block := ?_
    derived := derived
    cut := cut
    cut_zero := hcutZero
    cut_succ := ?_
    block_at_cut := ?_ }⟩⟩
  · intro left right heq
    apply enumerate.symm.injective
    apply Subtype.ext
    exact heq
  · intro letter
    exact (enumerate.symm letter).2
  · intro returnWord hreturn
    let retained : ReturnType := ⟨returnWord, hreturn⟩
    refine ⟨enumerate retained, ?_⟩
    simp [blocks, retained]
  · intro n
    rw [hblocksActual]
    have hlength : (block n).length = cut (n + 1) - cut n := by
      simp [block]
    rw [hlength]
    exact (Nat.add_sub_of_le (Nat.le_of_lt (hcutLt n))).symm
  · intro n
    rw [hblocksActual]
    simp [InfiniteFactorAt, block]

/-! ### Generic cut and parsing facts for a return decomposition -/

/-- Concatenating return blocks and then the marker still begins with the
marker.  This remains true when consecutive marker occurrences overlap. -/
theorem marker_prefix_flatMap_returnWords
    {α index : Type*} {word : InfiniteWord α}
    {marker : Word α} (blocks : index → Word α)
    (hreturns : ∀ letter : index,
      IsReturnWord word marker (blocks letter)) :
    ∀ letters : Word index,
      marker <+: letters.flatMap blocks ++ marker := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      have hlift : blocks letter ++ marker <+:
          blocks letter ++ (rest.flatMap blocks ++ marker) :=
        (List.prefix_append_right_inj (blocks letter)).mpr ih
      exact (hreturns letter).2.2.2.1.trans (by
        simpa [List.append_assoc] using hlift)

/-- A finite occurrence wholly contained in a prefix restricts to that
prefix. -/
theorem FiniteFactorAt.of_prefix
    {α : Type u} {large small factor : Word α} {start : ℕ}
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
    {α : Type u} {left tail factor : Word α}
    (hprefix : factor <+: tail) :
    FiniteFactorAt (left ++ tail) factor left.length := by
  refine ⟨?_, ?_⟩
  · simpa using Nat.add_le_add_left hprefix.length_le left.length
  · simpa using (List.prefix_iff_eq_take.mp hprefix).symm

/-- Equal concatenations of return words followed by marker-prefixed tails
have equal first-block lengths. -/
theorem returnWord_length_eq_of_append_eq
    {α : Type u} {word : InfiniteWord α}
    {marker first second firstTail secondTail : Word α}
    (hfirst : IsReturnWord word marker first)
    (hsecond : IsReturnWord word marker second)
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

/-- Return words to one marker form a code. -/
theorem flatMap_returnWords_injective
    {α index : Type*} {word : InfiniteWord α}
    {marker : Word α} {blocks : index → Word α}
    (hblocks : Function.Injective blocks)
    (hreturns : ∀ letter : index,
      IsReturnWord word marker (blocks letter)) :
    Function.Injective (fun letters : Word index =>
      letters.flatMap blocks) := by
  intro left
  induction left with
  | nil =>
      intro right heq
      cases right with
      | nil => rfl
      | cons letter rest =>
          exfalso
          have hnonempty := (hreturns letter).2.1
          simp only [List.flatMap_nil, List.flatMap_cons] at heq
          exact hnonempty (List.append_eq_nil_iff.mp heq.symm).1
  | cons leftLetter leftRest ih =>
      intro right heq
      cases right with
      | nil =>
          exfalso
          have hnonempty := (hreturns leftLetter).2.1
          simp only [List.flatMap_nil, List.flatMap_cons] at heq
          exact hnonempty (List.append_eq_nil_iff.mp heq).1
      | cons rightLetter rightRest =>
          simp only [List.flatMap_cons] at heq
          have hleftPrefix :=
            marker_prefix_flatMap_returnWords blocks hreturns leftRest
          have hrightPrefix :=
            marker_prefix_flatMap_returnWords blocks hreturns rightRest
          have heqMarker :
              blocks leftLetter ++ (leftRest.flatMap blocks ++ marker) =
                blocks rightLetter ++
                  (rightRest.flatMap blocks ++ marker) := by
            simpa [List.append_assoc] using
              congrArg (fun decoded => decoded ++ marker) heq
          have hlength : (blocks leftLetter).length =
              (blocks rightLetter).length :=
            returnWord_length_eq_of_append_eq
              (hreturns leftLetter) (hreturns rightLetter)
              hleftPrefix hrightPrefix heqMarker
          have hblockEq : blocks leftLetter = blocks rightLetter := by
            calc
              blocks leftLetter =
                  (blocks leftLetter ++ leftRest.flatMap blocks).take
                    (blocks leftLetter).length := by simp
              _ = (blocks rightLetter ++ rightRest.flatMap blocks).take
                    (blocks leftLetter).length := by rw [heq]
              _ = blocks rightLetter := by rw [hlength]; simp
          have hletterEq : leftLetter = rightLetter := hblocks hblockEq
          subst rightLetter
          have htailEq : leftRest.flatMap blocks =
              rightRest.flatMap blocks := List.append_cancel_left heq
          exact congrArg (leftLetter :: ·) (ih htailEq)

theorem ReturnDecomposition.block_length_pos
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (letter : Fin rank) : 0 < (decomposition.blocks letter).length :=
  List.length_pos_of_ne_nil
    (decomposition.blocks_are_returns letter).2.1

theorem ReturnDecomposition.cut_lt_succ
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (n : ℕ) : decomposition.cut n < decomposition.cut (n + 1) := by
  rw [decomposition.cut_succ]
  exact Nat.lt_add_of_pos_right
    (decomposition.block_length_pos (decomposition.derived n))

theorem ReturnDecomposition.cut_strictMono
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank) :
    StrictMono decomposition.cut :=
  strictMono_nat_of_lt_succ decomposition.cut_lt_succ

theorem ReturnDecomposition.cut_injective
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank) :
    Function.Injective decomposition.cut :=
  decomposition.cut_strictMono.injective

theorem ReturnDecomposition.le_cut
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank) :
    ∀ n : ℕ, n ≤ decomposition.cut n := by
  intro n
  induction n with
  | zero => simp [decomposition.cut_zero]
  | succ n ih =>
      have hstep := decomposition.cut_lt_succ n
      omega

theorem ReturnDecomposition.exists_cut_ge
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (position : ℕ) : ∃ n : ℕ, position ≤ decomposition.cut n :=
  ⟨position, decomposition.le_cut position⟩

/-- A finite prefix of the derived word decodes exactly to the corresponding
prefix of the original word. -/
theorem ReturnDecomposition.flatMap_take_derived
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank) :
    ∀ n : ℕ,
      (decomposition.derived.take n).flatMap decomposition.blocks =
        word.take (decomposition.cut n) := by
  intro n
  induction n with
  | zero => simp [decomposition.cut_zero]
  | succ n ih =>
      rw [Stream'.take_succ', List.flatMap_append, ih,
        decomposition.cut_succ, Stream'.take_add,
        decomposition.block_at_cut]
      simp [Stream'.get]

theorem ReturnDecomposition.cut_add
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (start : ℕ) : ∀ count : ℕ,
    decomposition.cut (start + count) = decomposition.cut start +
      (((decomposition.derived.drop start).take count).flatMap
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

/-- Every finite interval of derived letters decodes to the corresponding
interval between cuts. -/
theorem ReturnDecomposition.flatMap_drop_take_derived
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (start count : ℕ) :
    ((decomposition.derived.drop start).take count).flatMap
        decomposition.blocks =
      (word.drop (decomposition.cut start)).take
        (((decomposition.derived.drop start).take count).flatMap
          decomposition.blocks).length := by
  have hwhole := decomposition.flatMap_take_derived (start + count)
  rw [Stream'.take_add (a := decomposition.derived)
      (m := start) (n := count),
    List.flatMap_append, decomposition.flatMap_take_derived start,
    decomposition.cut_add start count,
    Stream'.take_add (a := word) (m := decomposition.cut start)
      (n := (((decomposition.derived.drop start).take count).flatMap
        decomposition.blocks).length)] at hwhole
  exact List.append_cancel_left hwhole

theorem ReturnDecomposition.decoded_length_ge
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (start : ℕ) : ∀ count : ℕ,
    count ≤ (((decomposition.derived.drop start).take count).flatMap
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

/-- The return overlap condition forces a marker at every cut. -/
theorem ReturnDecomposition.marker_at_cut
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (start : ℕ) :
    InfiniteFactorAt word marker (decomposition.cut start) := by
  let letters := (decomposition.derived.drop start).take marker.length
  let decoded := letters.flatMap decomposition.blocks
  have hlength : marker.length ≤ decoded.length := by
    simpa [letters, decoded] using
      decomposition.decoded_length_ge start marker.length
  have hprefix : marker <+: decoded ++ marker :=
    marker_prefix_flatMap_returnWords decomposition.blocks
      decomposition.blocks_are_returns letters
  have htake : (decoded ++ marker).take marker.length = marker :=
    (List.prefix_iff_eq_take.mp hprefix).symm
  have hdecodedTake : decoded.take marker.length = marker := by
    rw [List.take_append_of_le_length hlength] at htake
    exact htake
  have hdecode :=
    decomposition.flatMap_drop_take_derived start marker.length
  change decoded =
      (word.drop (decomposition.cut start)).take decoded.length at hdecode
  have htaken := congrArg (List.take marker.length) hdecode
  rw [hdecodedTake] at htaken
  have hstreamTake :
      ((word.drop (decomposition.cut start)).take decoded.length).take
          marker.length =
        (word.drop (decomposition.cut start)).take marker.length := by
    simp [hlength]
  rw [hstreamTake] at htaken
  exact htaken.symm

theorem ReturnDecomposition.block_marker_at_cut
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (start : ℕ) :
    InfiniteFactorAt word
      (decomposition.blocks (decomposition.derived start) ++ marker)
      (decomposition.cut start) := by
  rw [InfiniteFactorAt, List.length_append, Stream'.take_add,
    decomposition.block_at_cut]
  have hnext := decomposition.marker_at_cut (start + 1)
  rw [InfiniteFactorAt] at hnext
  have hcut := decomposition.cut_succ start
  have hdrop :
      (word.drop (decomposition.cut start)).drop
          (decomposition.blocks (decomposition.derived start)).length =
        word.drop (decomposition.cut (start + 1)) := by
    rw [Stream'.drop_drop, hcut]
  rw [hdrop]
  exact congrArg
    (fun tail =>
      decomposition.blocks (decomposition.derived start) ++ tail) hnext

theorem ReturnDecomposition.no_marker_between_cuts
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (start position : ℕ)
    (hleft : decomposition.cut start < position)
    (hright : position < decomposition.cut (start + 1)) :
    ¬ InfiniteFactorAt word marker position := by
  intro hposition
  let offset := position - decomposition.cut start
  have hpositionEq : decomposition.cut start + offset = position := by
    simp [offset, Nat.add_sub_of_le (Nat.le_of_lt hleft)]
  have hblockLength :
      (decomposition.blocks (decomposition.derived start)).length =
        decomposition.cut (start + 1) - decomposition.cut start := by
    rw [decomposition.cut_succ]
    omega
  have hoffsetLt : offset <
      (decomposition.blocks (decomposition.derived start)).length := by
    rw [hblockLength]
    dsimp only [offset]
    omega
  have hwithin : offset + marker.length ≤
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

/-- Every marker occurrence is one of the displayed cuts. -/
theorem ReturnDecomposition.marker_occurrence_eq_cut
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    {position : ℕ} (hposition : InfiniteFactorAt word marker position) :
    ∃ index : ℕ, decomposition.cut index = position := by
  let witness : ∃ index : ℕ, position ≤ decomposition.cut index :=
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

theorem ReturnDecomposition.block_eq_of_block_marker_at_cut
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (letter : Fin rank) (index : ℕ)
    (hat : InfiniteFactorAt word
      (decomposition.blocks letter ++ marker)
      (decomposition.cut index)) :
    decomposition.blocks letter =
      decomposition.blocks (decomposition.derived index) := by
  have hmarkerAtEnd : InfiniteFactorAt word marker
      (decomposition.cut index +
        (decomposition.blocks letter).length) := by
    have hfinite : FiniteFactorAt
        (decomposition.blocks letter ++ marker) marker
        (decomposition.blocks letter).length := by
      simp [FiniteFactorAt]
    exact hat.of_finiteFactorAt hfinite
  obtain ⟨endpoint, hendpoint⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAtEnd
  have hletterPositive := decomposition.block_length_pos letter
  have hendpointGt : index < endpoint := by
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hendpoint]
    omega
  have hnextLe : index + 1 ≤ endpoint := by omega
  have hlengthLe :
      (decomposition.blocks (decomposition.derived index)).length ≤
        (decomposition.blocks letter).length := by
    have hcuts := decomposition.cut_strictMono.monotone hnextLe
    rw [decomposition.cut_succ, hendpoint] at hcuts
    omega
  have hreverseLength :
      (decomposition.blocks letter).length ≤
        (decomposition.blocks (decomposition.derived index)).length := by
    by_contra hnot
    have hstrict :
        (decomposition.blocks (decomposition.derived index)).length <
          (decomposition.blocks letter).length := by omega
    have hnextMarker := decomposition.marker_at_cut (index + 1)
    have hnextPosition : decomposition.cut (index + 1) =
        decomposition.cut index +
          (decomposition.blocks (decomposition.derived index)).length :=
      decomposition.cut_succ index
    have hfinite : FiniteFactorAt
        (decomposition.blocks letter ++ marker) marker
        (decomposition.blocks (decomposition.derived index)).length := by
      apply finiteFactorAt_of_nested_infiniteFactorAt hat
      · rw [hnextPosition] at hnextMarker
        exact hnextMarker
      · simp only [List.length_append]
        omega
    rcases (decomposition.blocks_are_returns letter).2.2.2.2
        (decomposition.blocks (decomposition.derived index)).length |>.mp
          hfinite with hzero | hend
    · exact (decomposition.block_length_pos
        (decomposition.derived index)).ne' hzero
    · omega
  have hlength : (decomposition.blocks letter).length =
      (decomposition.blocks (decomposition.derived index)).length := by
    omega
  have hletterBlock : InfiniteFactorAt word
      (decomposition.blocks letter) (decomposition.cut index) := by
    have hfinite : FiniteFactorAt
        (decomposition.blocks letter ++ marker)
        (decomposition.blocks letter) 0 := by
      simp [FiniteFactorAt]
    simpa using hat.of_finiteFactorAt hfinite
  have hactualBlock := decomposition.block_at_cut index
  rw [InfiniteFactorAt] at hletterBlock hactualBlock
  rw [← hlength] at hactualBlock
  exact hletterBlock.symm.trans hactualBlock

theorem ReturnDecomposition.block_marker_occurrence_aligns
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (letter : Fin rank) {position : ℕ}
    (hat : InfiniteFactorAt word
      (decomposition.blocks letter ++ marker) position) :
    ∃ index : ℕ,
      decomposition.cut index = position ∧
        decomposition.derived index = letter := by
  have hmarkerPrefix :=
    (decomposition.blocks_are_returns letter).2.2.2.1
  have hfinite : FiniteFactorAt
      (decomposition.blocks letter ++ marker) marker 0 := by
    refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
  have hmarkerAt : InfiniteFactorAt word marker position := by
    simpa using hat.of_finiteFactorAt hfinite
  obtain ⟨index, hindex⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAt
  have hatCut : InfiniteFactorAt word
      (decomposition.blocks letter ++ marker)
      (decomposition.cut index) := by
    rw [hindex]
    exact hat
  have hblock :=
    decomposition.block_eq_of_block_marker_at_cut letter index hatCut
  exact ⟨index, hindex,
    decomposition.blocks_injective hblock |>.symm⟩

/-- Every named return block really appears in the derived word. -/
theorem ReturnDecomposition.every_letter_occurs
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (letter : Fin rank) :
    Substitution.OccursInInfiniteWord letter decomposition.derived := by
  obtain ⟨position, hat⟩ :=
    (decomposition.blocks_are_returns letter).2.2.1
  obtain ⟨index, _hcut, hletter⟩ :=
    decomposition.block_marker_occurrence_aligns letter hat
  exact ⟨index, hletter⟩

/-! ### Positive substitution powers and substituted cuts -/

namespace Substitution

variable {α : Type u}

/-- Power under concatenating substitution composition. -/
def power (source : Substitution α) : ℕ → Substitution α
  | 0 => Substitution.id
  | n + 1 => source.comp (power source n)

@[simp] theorem power_zero (source : Substitution α) :
    source.power 0 = Substitution.id := rfl

@[simp] theorem power_succ (source : Substitution α) (n : ℕ) :
    source.power (n + 1) = source.comp (source.power n) := rfl

@[simp] theorem power_apply (source : Substitution α) (n : ℕ) (letter : α) :
    source.power n letter = source.iterateLetter n letter := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change source.mapWord (source.power n letter) =
        source.mapWord (source.iterateLetter n letter)
      rw [ih]

private theorem mapWord_id (letters : Word α) :
    (Substitution.id : Substitution α).mapWord letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih => simp [ih]

private theorem mapWord_comp (source target : Substitution α)
    (letters : Word α) :
    (source.comp target).mapWord letters =
      source.mapWord (target.mapWord letters) := by
  induction letters with
  | nil => rfl
  | cons letter rest ih => simp [ih]

theorem power_mapWord (source : Substitution α) (n : ℕ)
    (letters : Word α) :
    (source.power n).mapWord letters = source.iterateWord n letters := by
  induction n with
  | zero => exact mapWord_id letters
  | succ n ih =>
      rw [power_succ, mapWord_comp, ih]
      rfl

/-- Infinite concatenation respects substitution composition. -/
theorem mapInfinite_comp (source target : Substitution α)
    (word : InfiniteWord α) :
    (source.comp target).mapInfinite word =
      source.mapInfinite (target.mapInfinite word) := by
  let Relation : InfiniteWord α → InfiniteWord α → Prop :=
    fun left right =>
      ∃ (pref : Word α) (input : InfiniteWord α),
        left = pref ++ₛ (source.comp target).mapInfinite input ∧
        right = pref ++ₛ source.mapInfinite (target.mapInfinite input)
  apply Stream'.eq_of_bisim Relation
  · intro left right hrel
    rcases hrel with ⟨pref, input, rfl, rfl⟩
    cases pref with
    | cons letter rest =>
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨rest, input, rfl, rfl⟩⟩
    | nil =>
        simp only [Stream'.nil_append_stream]
        have hleft :
            (source.comp target).mapInfinite input =
              source.mapWord (target input.head) ++ₛ
                (source.comp target).mapInfinite input.tail := by
          rw [mapInfinite_eq_append_first_image]
          rfl
        have hright :
            source.mapInfinite (target.mapInfinite input) =
              source.mapWord (target input.head) ++ₛ
                source.mapInfinite (target.mapInfinite input.tail) := by
          rw [mapInfinite_eq_append_first_image target input,
            mapInfinite_append_stream]
        rw [hleft, hright]
        obtain ⟨letter, rest, hrest⟩ := List.exists_cons_of_ne_nil
          (source.mapWord_ne_nil (target.image_ne_nil input.head))
        rw [hrest, Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨rfl, ⟨rest, input.tail, rfl, rfl⟩⟩
  · exact ⟨[], word, rfl, rfl⟩

@[simp] theorem mapInfinite_id (word : InfiniteWord α) :
    (Substitution.id : Substitution α).mapInfinite word = word := by
  let Relation : InfiniteWord α → InfiniteWord α → Prop :=
    fun left right =>
      ∃ input : InfiniteWord α,
        left = (Substitution.id : Substitution α).mapInfinite input ∧
        right = input
  apply Stream'.eq_of_bisim Relation
  · intro left right hrel
    rcases hrel with ⟨input, hleft, hright⟩
    rw [hleft, hright, mapInfinite_eq_append_first_image, id_apply,
      Stream'.cons_append_stream, ← Stream'.eta input]
    exact ⟨rfl, ⟨input.tail, rfl, rfl⟩⟩
  · exact ⟨word, rfl, rfl⟩

/-- A positive substitution power fixes every fixed infinite word. -/
theorem isFixedPoint_power {source : Substitution α}
    {word : InfiniteWord α} (hfixed : source.IsFixedPoint word)
    {n : ℕ} (hn : 0 < n) :
    (source.power n).IsFixedPoint word := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hprevious : (source.power n).IsFixedPoint word := by
        cases n with
        | zero => exact mapInfinite_id word
        | succ n => exact ih (Nat.succ_pos n)
      change (source.comp (source.power n)).mapInfinite word = word
      rw [mapInfinite_comp]
      change (source.power n).mapInfinite word = word at hprevious
      change source.mapInfinite word = word at hfixed
      rw [hprevious, hfixed]

theorem length_le_mapWord (source : Substitution α) (letters : Word α) :
    letters.length ≤ (source.mapWord letters).length := by
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      rw [mapWord_cons, List.length_append, List.length_cons]
      have hletter : 0 < (source letter).length :=
        List.length_pos_of_ne_nil (source.image_ne_nil letter)
      omega

/-- A substituted finite interval in a fixed word starts after the
substituted prefix. -/
theorem mapWord_drop_take_at_fixed
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word) (start count : ℕ) :
    InfiniteFactorAt word
      (source.mapWord ((word.drop start).take count))
      (source.mapWord (word.take start)).length := by
  let pref := source.mapWord (word.take start)
  let segment := source.mapWord ((word.drop start).take count)
  have hprefixSplit :
      pref ++ₛ source.mapInfinite (word.drop start) = word := by
    calc
      pref ++ₛ source.mapInfinite (word.drop start) =
          source.mapInfinite (word.take start ++ₛ word.drop start) := by
        exact (mapInfinite_append_stream source _ _).symm
      _ = source.mapInfinite word := by rw [Stream'.append_take_drop]
      _ = word := hfixed
  have hsegmentSplit :
      source.mapInfinite (word.drop start) =
        segment ++ₛ source.mapInfinite ((word.drop start).drop count) := by
    calc
      source.mapInfinite (word.drop start) =
          source.mapInfinite
            ((word.drop start).take count ++ₛ
              (word.drop start).drop count) := by
        rw [Stream'.append_take_drop]
      _ = segment ++ₛ
          source.mapInfinite ((word.drop start).drop count) :=
        mapInfinite_append_stream source _ _
  have htail : word.drop pref.length =
      source.mapInfinite (word.drop start) := by
    have hdropped := congrArg (fun stream : InfiniteWord α =>
      stream.drop pref.length) hprefixSplit
    simpa [Stream'.drop_append_stream] using hdropped.symm
  have htaken :
      (source.mapInfinite (word.drop start)).take segment.length =
        segment := by
    rw [hsegmentSplit]
    simpa using Stream'.take_append_of_le_length
      (x := segment)
      (a := source.mapInfinite ((word.drop start).drop count))
      (n := segment.length) le_rfl
  have hcombined :
      (word.drop pref.length).take segment.length = segment :=
    (congrArg (fun stream : InfiniteWord α =>
      stream.take segment.length) htail).trans htaken
  exact hcombined

/-- Physical location of the image of a return cut. -/
def substitutedReturnCut
    (source : Substitution α) {word : InfiniteWord α}
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank)
    (position : ℕ) : ℕ :=
  (source.mapWord (word.take (decomposition.cut position))).length

theorem map_block_at_substitutedReturnCut
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank)
    (position : ℕ) :
    InfiniteFactorAt word
      (source.mapWord
        (decomposition.blocks (decomposition.derived position)))
      (substitutedReturnCut source decomposition position) := by
  have h := mapWord_drop_take_at_fixed hfixed
    (decomposition.cut position)
    (decomposition.blocks (decomposition.derived position)).length
  rw [decomposition.block_at_cut position] at h
  simpa [substitutedReturnCut] using h

theorem substitutedReturnCut_succ
    (source : Substitution α) {word : InfiniteWord α}
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank)
    (position : ℕ) :
    substitutedReturnCut source decomposition (position + 1) =
      substitutedReturnCut source decomposition position +
        (source.mapWord
          (decomposition.blocks
            (decomposition.derived position))).length := by
  have hblock := decomposition.block_at_cut position
  rw [InfiniteFactorAt] at hblock
  simp only [substitutedReturnCut, decomposition.cut_succ,
    Stream'.take_add, mapWord_append, List.length_append]
  rw [hblock]

end Substitution

/-! ### The induced substitution of an arbitrary prefix marker -/

/-- Exact parsing of the image of every return block, together with the
aligned substituted cuts that prove fixedness of the induced word. -/
structure PrefixReturnFactorization
    {α : Type u} (source : Substitution α)
    {word : InfiniteWord α} {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank) where
  factor : Fin rank → Word (Fin rank)
  factor_decodes : ∀ letter,
    (factor letter).flatMap decomposition.blocks =
      source.mapWord (decomposition.blocks letter)
  factor_ne_nil : ∀ letter, factor letter ≠ []
  factor_unique : ∀ letter letters,
    letters.flatMap decomposition.blocks =
      source.mapWord (decomposition.blocks letter) →
    letters = factor letter
  boundary : ℕ → ℕ
  boundary_zero : boundary 0 = 0
  boundary_cut : ∀ position,
    decomposition.cut (boundary position) =
      Substitution.substitutedReturnCut source decomposition position
  boundary_succ : ∀ position,
    boundary (position + 1) = boundary position +
      (factor (decomposition.derived position)).length
  derived_factor_at : ∀ position,
    InfiniteFactorAt decomposition.derived
      (factor (decomposition.derived position)) (boundary position)

def PrefixReturnFactorization.substitution
    {α : Type u} {source : Substitution α}
    {word : InfiniteWord α} {marker : Word α} {rank : ℕ}
    {decomposition : ReturnDecomposition word marker rank}
    (factorization : PrefixReturnFactorization source decomposition) :
    Substitution (Fin rank) where
  image := factorization.factor
  image_ne_nil := factorization.factor_ne_nil

/-- Every substituted return cut is again a marker occurrence. -/
theorem marker_at_substitutedReturnCut_of_prefix
    {α : Type u} {source : Substitution α}
    {word : InfiniteWord α} (hfixed : source.IsFixedPoint word)
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank)
    (position : ℕ) :
    InfiniteFactorAt word marker
      (Substitution.substitutedReturnCut source decomposition position) := by
  have hmappedAtZero :=
    Substitution.mapWord_drop_take_at_fixed hfixed 0 marker.length
  have hmarkerZero : word.take marker.length = marker := by
    simpa [InfiniteFactorAt] using decomposition.marker_at_zero
  simp only [Stream'.drop_zero] at hmappedAtZero
  rw [hmarkerZero] at hmappedAtZero
  have hmappedZero : InfiniteFactorAt word
      (source.mapWord marker) 0 := by
    simpa [InfiniteFactorAt] using hmappedAtZero
  have hmappedEq : word.take (source.mapWord marker).length =
      source.mapWord marker := by
    simpa [InfiniteFactorAt] using hmappedZero
  have hprefix : marker <+: source.mapWord marker := by
    have hlength := source.length_le_mapWord marker
    have hpref := Stream'.take_prefix_take_left
      (a := word) (m := marker.length)
      (n := (source.mapWord marker).length) hlength
    rw [hmarkerZero, hmappedEq] at hpref
    exact hpref
  have hwhole := Substitution.mapWord_drop_take_at_fixed hfixed
    (decomposition.cut position) marker.length
  have hsource :
      (word.drop (decomposition.cut position)).take marker.length = marker :=
    decomposition.marker_at_cut position
  rw [hsource] at hwhole
  have hfinite : FiniteFactorAt (source.mapWord marker) marker 0 := by
    refine ⟨by simpa using hprefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hprefix).symm
  simpa [Substitution.substitutedReturnCut] using
    hwhole.of_finiteFactorAt hfinite

/-- Construct the unique return-block parsing of every source image. -/
theorem prefixReturnFactorization_exists
    {α : Type u} {source : Substitution α}
    {word : InfiniteWord α} (hfixed : source.IsFixedPoint word)
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank) :
    Nonempty (PrefixReturnFactorization source decomposition) := by
  classical
  let boundary : ℕ → ℕ := fun position =>
    Classical.choose (decomposition.marker_occurrence_eq_cut
      (marker_at_substitutedReturnCut_of_prefix
        hfixed decomposition position))
  have hboundaryCut : ∀ position : ℕ,
      decomposition.cut (boundary position) =
        Substitution.substitutedReturnCut
          source decomposition position := by
    intro position
    exact Classical.choose_spec (decomposition.marker_occurrence_eq_cut
      (marker_at_substitutedReturnCut_of_prefix
        hfixed decomposition position))
  have hsubZero : Substitution.substitutedReturnCut
      source decomposition 0 = 0 := by
    simp [Substitution.substitutedReturnCut, decomposition.cut_zero]
  have hboundaryZero : boundary 0 = 0 := by
    apply decomposition.cut_injective
    rw [hboundaryCut, hsubZero, decomposition.cut_zero]
  have hsubStrict : StrictMono
      (Substitution.substitutedReturnCut source decomposition) := by
    apply strictMono_nat_of_lt_succ
    intro position
    rw [Substitution.substitutedReturnCut_succ]
    exact Nat.lt_add_of_pos_right
      (List.length_pos_of_ne_nil
        (source.mapWord_ne_nil
          (decomposition.blocks_are_returns
            (decomposition.derived position)).2.1))
  have hboundaryStrict : StrictMono boundary := by
    intro left right hlr
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hboundaryCut, hboundaryCut]
    exact hsubStrict hlr
  let factorAt : ℕ → Word (Fin rank) := fun position =>
    (decomposition.derived.drop (boundary position)).take
      (boundary (position + 1) - boundary position)
  have hfactorAtDecodes : ∀ position : ℕ,
      (factorAt position).flatMap decomposition.blocks =
        source.mapWord
          (decomposition.blocks (decomposition.derived position)) := by
    intro position
    have hboundaryLe : boundary position ≤ boundary (position + 1) :=
      (hboundaryStrict (Nat.lt_succ_self position)).le
    have hdecode := decomposition.flatMap_drop_take_derived
      (boundary position) (boundary (position + 1) - boundary position)
    change (factorAt position).flatMap decomposition.blocks =
      (word.drop (decomposition.cut (boundary position))).take
        ((factorAt position).flatMap decomposition.blocks).length at hdecode
    have hcutAdd := decomposition.cut_add (boundary position)
      (boundary (position + 1) - boundary position)
    have hboundaryAdd : boundary position +
        (boundary (position + 1) - boundary position) =
        boundary (position + 1) := Nat.add_sub_of_le hboundaryLe
    rw [hboundaryAdd] at hcutAdd
    change decomposition.cut (boundary (position + 1)) =
      decomposition.cut (boundary position) +
        ((factorAt position).flatMap decomposition.blocks).length at hcutAdd
    have hsubSucc := Substitution.substitutedReturnCut_succ
      source decomposition position
    rw [hboundaryCut, hboundaryCut] at hcutAdd
    have hlength :
        ((factorAt position).flatMap decomposition.blocks).length =
          (source.mapWord
            (decomposition.blocks
              (decomposition.derived position))).length := by
      omega
    rw [hboundaryCut, hlength] at hdecode
    exact hdecode.trans
      (Substitution.map_block_at_substitutedReturnCut
        hfixed decomposition position)
  let occurrence : Fin rank → ℕ := fun letter =>
    Classical.choose (decomposition.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin rank,
      decomposition.derived (occurrence letter) = letter := by
    intro letter
    exact Classical.choose_spec
      (decomposition.every_letter_occurs letter)
  let factor : Fin rank → Word (Fin rank) := fun letter =>
    factorAt (occurrence letter)
  have hfactorDecodes : ∀ letter : Fin rank,
      (factor letter).flatMap decomposition.blocks =
        source.mapWord (decomposition.blocks letter) := by
    intro letter
    change (factorAt (occurrence letter)).flatMap decomposition.blocks = _
    rw [hfactorAtDecodes, hoccurrence]
  have hfactorAt : ∀ position : ℕ,
      factor (decomposition.derived position) = factorAt position := by
    intro position
    apply flatMap_returnWords_injective
      decomposition.blocks_injective decomposition.blocks_are_returns
    exact (hfactorDecodes (decomposition.derived position)).trans
      (hfactorAtDecodes position).symm
  have hfactorNonempty : ∀ letter : Fin rank,
      factor letter ≠ [] := by
    intro letter hempty
    have hdecode := hfactorDecodes letter
    rw [hempty] at hdecode
    simp only [List.flatMap_nil] at hdecode
    exact source.mapWord_ne_nil
      (decomposition.blocks_are_returns letter).2.1 hdecode.symm
  have hfactorUnique : ∀ letter : Fin rank,
      ∀ letters : Word (Fin rank),
        letters.flatMap decomposition.blocks =
          source.mapWord (decomposition.blocks letter) →
        letters = factor letter := by
    intro letter letters hdecode
    apply flatMap_returnWords_injective
      decomposition.blocks_injective decomposition.blocks_are_returns
    exact hdecode.trans (hfactorDecodes letter).symm
  have hboundarySucc : ∀ position : ℕ,
      boundary (position + 1) = boundary position +
        (factor (decomposition.derived position)).length := by
    intro position
    have hboundaryLe : boundary position ≤ boundary (position + 1) :=
      (hboundaryStrict (Nat.lt_succ_self position)).le
    rw [hfactorAt]
    change boundary (position + 1) = boundary position +
      ((decomposition.derived.drop (boundary position)).take
        (boundary (position + 1) - boundary position)).length
    simp only [Stream'.length_take]
    exact (Nat.add_sub_of_le hboundaryLe).symm
  have hderivedFactorAt : ∀ position : ℕ,
      InfiniteFactorAt decomposition.derived
        (factor (decomposition.derived position))
        (boundary position) := by
    intro position
    rw [hfactorAt]
    simp [InfiniteFactorAt, factorAt]
  exact ⟨{
    factor := factor
    factor_decodes := hfactorDecodes
    factor_ne_nil := hfactorNonempty
    factor_unique := hfactorUnique
    boundary := boundary
    boundary_zero := hboundaryZero
    boundary_cut := hboundaryCut
    boundary_succ := hboundarySucc
    derived_factor_at := hderivedFactorAt }⟩

/-- The induced return substitution fixes the displayed derived word. -/
theorem PrefixReturnFactorization.fixed
    {α : Type u} {source : Substitution α}
    {word : InfiniteWord α} {marker : Word α} {rank : ℕ}
    {decomposition : ReturnDecomposition word marker rank}
    (factorization : PrefixReturnFactorization source decomposition) :
    factorization.substitution.IsFixedPoint decomposition.derived := by
  have hboundaryLower : ∀ position : ℕ,
      position ≤ factorization.boundary position := by
    intro position
    induction position with
    | zero => simp [factorization.boundary_zero]
    | succ position ih =>
        rw [factorization.boundary_succ]
        have hpositive : 0 <
            (factorization.factor
              (decomposition.derived position)).length :=
          List.length_pos_of_ne_nil
            (factorization.factor_ne_nil
              (decomposition.derived position))
        omega
  have hfiniteTiling : ∀ count : ℕ,
      factorization.substitution.mapWord
          (decomposition.derived.take count) =
        decomposition.derived.take (factorization.boundary count) := by
    intro count
    induction count with
    | zero => simp [factorization.boundary_zero]
    | succ count ih =>
        have hfactorAt := factorization.derived_factor_at count
        change
          (decomposition.derived.drop
            (factorization.boundary count)).take
              (factorization.factor
                (decomposition.derived count)).length =
            factorization.factor
              (decomposition.derived count) at hfactorAt
        rw [Stream'.take_succ', Substitution.mapWord_append,
          Substitution.mapWord_cons, Substitution.mapWord_nil,
          List.append_nil, ih, factorization.boundary_succ,
          Stream'.take_add]
        exact congrArg
          (fun tail => decomposition.derived.take
            (factorization.boundary count) ++ tail) hfactorAt.symm
  rw [Substitution.IsFixedPoint]
  funext position
  let count := position + 1
  have hposition : position < factorization.boundary count := by
    have hbound := hboundaryLower count
    omega
  have hwordLength :
      (factorization.substitution.mapWord
        (decomposition.derived.take count)).length =
      factorization.boundary count := by
    rw [hfiniteTiling]
    simp
  have hmapPrefix :
      (factorization.substitution.mapInfinite
        decomposition.derived).take (factorization.boundary count) =
      factorization.substitution.mapWord
        (decomposition.derived.take count) := by
    rw [← hwordLength]
    calc
      (factorization.substitution.mapInfinite
          decomposition.derived).take
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
            rw [mapInfinite_append_stream]
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
      (factorization.substitution.mapInfinite
        decomposition.derived).take (factorization.boundary count) =
      decomposition.derived.take (factorization.boundary count) :=
    hmapPrefix.trans (hfiniteTiling count)
  have hleftIndex : position <
      ((factorization.substitution.mapInfinite
        decomposition.derived).take
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
      (factorization.substitution.mapInfinite decomposition.derived)
        position = Stream'.get decomposition.derived position
  rw [← hleftGet, ← hrightGet]
  rw [← Option.some_inj, ← List.getElem?_eq_getElem,
    ← List.getElem?_eq_getElem]
  exact congrArg (fun letters => letters[position]?) hprefix

/-! ### Metric form of the incidence intertwining -/

theorem wordMetricLength_eq_count_sum
    {α : Type u} [Fintype α] [DecidableEq α]
    (length : α → ℝ) (letters : Word α) :
    wordMetricLength length letters =
      ∑ letter : α, (letters.count letter : ℝ) * length letter := by
  induction letters with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      rw [wordMetricLength]
      change length head + (tail.map length).sum = _
      rw [← wordMetricLength, ih]
      calc
        length head +
            ∑ letter : α, (tail.count letter : ℝ) * length letter =
          (∑ letter : α, if letter = head then length letter else 0) +
            ∑ letter : α,
              (tail.count letter : ℝ) * length letter := by simp
        _ = ∑ letter : α,
              ((if letter = head then length letter else 0) +
                (tail.count letter : ℝ) * length letter) :=
          Finset.sum_add_distrib.symm
        _ = ∑ letter : α,
              ((head :: tail).count letter : ℝ) * length letter := by
          apply Finset.sum_congr rfl
          intro letter _
          by_cases hletter : letter = head
          · subst letter
            simp [add_mul, add_comm]
          · simp [hletter, Ne.symm hletter]

theorem wordMetricLength_nonneg
    {α : Type u} (length : α → ℝ)
    (hlength : ∀ letter, 0 ≤ length letter) :
    ∀ letters : Word α, 0 ≤ wordMetricLength length letters := by
  intro letters
  induction letters with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      simp only [wordMetricLength, List.map_cons, List.sum_cons]
      exact add_nonneg (hlength head)
        (by simpa [wordMetricLength] using ih)

theorem weight_le_wordMetricLength_of_mem
    {α : Type u} (length : α → ℝ)
    (hlength : ∀ letter, 0 ≤ length letter)
    {letter : α} {letters : Word α} (hmem : letter ∈ letters) :
    length letter ≤ wordMetricLength length letters := by
  induction letters with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [wordMetricLength, List.map_cons, List.sum_cons]
      rcases hmem with rfl | htail
      · exact le_add_of_nonneg_right
          (by simpa [wordMetricLength] using
            wordMetricLength_nonneg length hlength tail)
      · exact (ih htail).trans
          (le_add_of_nonneg_left (hlength head))

theorem wordMetricLength_flatMap
    {α : Type u} {β : Type v} (length : β → ℝ)
    (blocks : α → Word β) (letters : Word α) :
    wordMetricLength
        (fun letter => wordMetricLength length (blocks letter)) letters =
      wordMetricLength length (letters.flatMap blocks) := by
  induction letters with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      calc
        wordMetricLength
              (fun letter => wordMetricLength length (blocks letter))
              (head :: tail) =
            wordMetricLength length (blocks head) +
              wordMetricLength
                (fun letter => wordMetricLength length (blocks letter))
                tail := rfl
        _ = wordMetricLength length (blocks head) +
              wordMetricLength length (tail.flatMap blocks) := by rw [ih]
        _ = wordMetricLength length
              (blocks head ++ tail.flatMap blocks) := by
            simp [wordMetricLength, List.sum_append]
        _ = wordMetricLength length
              ((head :: tail).flatMap blocks) := rfl

theorem wordMetricLength_mapWord_of_scales
    {α : Type u} {source : Substitution α}
    {length : α → ℝ} {scale : ℝ}
    (hscale : SubstitutionScalesLetterLengths source length scale) :
    ∀ letters : Word α,
      wordMetricLength length (source.mapWord letters) =
        scale * wordMetricLength length letters := by
  intro letters
  induction letters with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      rw [Substitution.mapWord_cons]
      simp only [wordMetricLength, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      change wordMetricLength length (source head) +
          wordMetricLength length (source.mapWord tail) =
        scale * (length head + wordMetricLength length tail)
      rw [hscale head, ih]
      ring

theorem scalesLetterLengths_power
    {α : Type u} {source : Substitution α}
    {length : α → ℝ} {scale : ℝ}
    (hscale : SubstitutionScalesLetterLengths source length scale) :
    ∀ exponent : ℕ,
      SubstitutionScalesLetterLengths (source.power exponent)
        length (scale ^ exponent) := by
  intro exponent
  induction exponent with
  | zero =>
      intro letter
      simp [Substitution.power_apply, Substitution.iterateLetter,
        Substitution.iterateWord, wordMetricLength]
  | succ exponent ih =>
      intro letter
      rw [Substitution.power_apply, Substitution.iterateLetter_succ,
        wordMetricLength_mapWord_of_scales hscale]
      have hprevious := ih letter
      rw [Substitution.power_apply] at hprevious
      rw [hprevious, pow_succ']
      ring


/-- The decoding square transports exact source scaling to the induced
return substitution.  This is the transpose-incidence intertwining used in
D2b.3, stated in its more transparent metric form. -/
theorem PrefixReturnFactorization.scalesReturnMetric
    {α : Type u} {source : Substitution α}
    {word : InfiniteWord α} {marker : Word α} {rank : ℕ}
    {decomposition : ReturnDecomposition word marker rank}
    (factorization : PrefixReturnFactorization source decomposition)
    {length : α → ℝ} {scale : ℝ}
    (hscale : SubstitutionScalesLetterLengths source length scale) :
    SubstitutionScalesLetterLengths factorization.substitution
      (fun letter => wordMetricLength length
        (decomposition.blocks letter)) scale := by
  intro letter
  change wordMetricLength
      (fun other => wordMetricLength length (decomposition.blocks other))
      (factorization.factor letter) =
    scale * wordMetricLength length (decomposition.blocks letter)
  calc
    _ = wordMetricLength length
          ((factorization.factor letter).flatMap decomposition.blocks) :=
      wordMetricLength_flatMap length decomposition.blocks _
    _ = wordMetricLength length
          (source.mapWord (decomposition.blocks letter)) := by
      rw [factorization.factor_decodes]
    _ = scale * wordMetricLength length
          (decomposition.blocks letter) :=
      wordMetricLength_mapWord_of_scales hscale _

private def NatMatrixEigenvectorEquation
    {α : Type u} [Fintype α]
    (matrix : Matrix α α ℕ) (vector : α → ℝ)
    (eigenvalue : ℝ) : Prop :=
  ∀ row : α,
    (∑ column : α, (matrix row column : ℝ) * vector column) =
      eigenvalue * vector row

/-- A strictly positive real eigenvector gives a weighted max norm bounding
all complex eigenvalues. -/
theorem positive_eigenvector_isDominant
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (matrix : Matrix α α ℕ) (vector : α → ℝ) (eigenvalue : ℝ)
    (hvector : ∀ row, 0 < vector row)
    (heigen : NatMatrixEigenvectorEquation matrix vector eigenvalue) :
    IsDominantEigenvalue matrix eigenvalue := by
  constructor
  · let complexVector : α → ℂ := fun row => (vector row : ℂ)
    have hcomplexVector : complexVector ≠ 0 := by
      intro hzero
      obtain ⟨row⟩ := ‹Nonempty α›
      have hrow := congrFun hzero row
      simp only [complexVector, Pi.zero_apply,
        Complex.ofReal_eq_zero] at hrow
      exact (ne_of_gt (hvector row)) hrow
    refine ⟨complexVector, hcomplexVector, ?_⟩
    intro row
    have hrow := congrArg Complex.ofReal (heigen row)
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_natCast, complexVector] using hrow
  · intro z hz
    rcases hz with ⟨complexVector, hcomplexVector, heigenz⟩
    have hexists : ∃ row : α, complexVector row ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hcomplexVector (funext hnone)
    obtain ⟨nonzeroRow, hnonzeroRow⟩ := hexists
    obtain ⟨maxRow, _hmaxMem, hmax⟩ :=
      Finset.univ.exists_max_image
        (fun row => ‖complexVector row‖ / vector row)
        Finset.univ_nonempty
    have hratioNonzero : 0 <
        ‖complexVector nonzeroRow‖ / vector nonzeroRow :=
      div_pos (norm_pos_iff.mpr hnonzeroRow) (hvector nonzeroRow)
    have hratioMax : 0 < ‖complexVector maxRow‖ / vector maxRow :=
      hratioNonzero.trans_le (hmax nonzeroRow (Finset.mem_univ _))
    have hmaxNorm : 0 < ‖complexVector maxRow‖ := by
      by_contra hnot
      have hzero : ‖complexVector maxRow‖ = 0 :=
        le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      rw [hzero, zero_div] at hratioMax
      exact (lt_irrefl 0) hratioMax
    have hbound (column : α) :
        ‖complexVector column‖ ≤
          (‖complexVector maxRow‖ / vector maxRow) * vector column :=
      (div_le_iff₀ (hvector column)).mp
        (hmax column (Finset.mem_univ column))
    have htriangle :
        ‖z‖ * ‖complexVector maxRow‖ ≤
          eigenvalue * ‖complexVector maxRow‖ := by
      calc
        ‖z‖ * ‖complexVector maxRow‖ =
            ‖z * complexVector maxRow‖ :=
          (norm_mul z (complexVector maxRow)).symm
        _ = ‖∑ column : α,
            (matrix maxRow column : ℂ) * complexVector column‖ :=
          congrArg norm (heigenz maxRow).symm
        _ ≤ ∑ column : α,
            ‖(matrix maxRow column : ℂ) * complexVector column‖ :=
          norm_sum_le Finset.univ _
        _ = ∑ column : α,
            (matrix maxRow column : ℝ) * ‖complexVector column‖ := by
          apply Finset.sum_congr rfl
          intro column _
          rw [norm_mul]
          simp
        _ ≤ ∑ column : α, (matrix maxRow column : ℝ) *
            ((‖complexVector maxRow‖ / vector maxRow) *
              vector column) := by
          apply Finset.sum_le_sum
          intro column _
          exact mul_le_mul_of_nonneg_left (hbound column)
            (Nat.cast_nonneg _)
        _ = (‖complexVector maxRow‖ / vector maxRow) *
            (∑ column : α,
              (matrix maxRow column : ℝ) * vector column) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro column _
          ring
        _ = (‖complexVector maxRow‖ / vector maxRow) *
            (eigenvalue * vector maxRow) := by rw [heigen maxRow]
        _ = eigenvalue * ‖complexVector maxRow‖ := by
          field_simp [(ne_of_gt (hvector maxRow))]
    exact le_of_mul_le_mul_right htriangle hmaxNorm

private def complexification {α : Type u}
    (matrix : Matrix α α ℕ) : Matrix α α ℂ :=
  matrix.map (Nat.castRingHom ℂ)

private theorem isComplexEigenvalue_iff_hasEigenvalue
    {α : Type u} [Fintype α] [DecidableEq α]
    (matrix : Matrix α α ℕ) (z : ℂ) :
    IsComplexEigenvalue matrix z ↔
      Module.End.HasEigenvalue
        (Matrix.toLin' (complexification matrix)) z := by
  constructor
  · rintro ⟨vector, hvector, heigen⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hvector⟩
    ext row
    simp only [Matrix.toLin'_apply, Matrix.mulVec, complexification,
      Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    exact heigen row
  · intro h
    obtain ⟨vector, hvector⟩ := h.exists_hasEigenvector
    refine ⟨vector, hvector.2, ?_⟩
    have heigen := Module.End.mem_eigenspace_iff.mp hvector.1
    intro row
    have hrow := congrFun heigen row
    simpa only [Matrix.toLin'_apply, Matrix.mulVec, complexification,
      Matrix.map_apply, Pi.smul_apply, smul_eq_mul] using hrow

private theorem isComplexEigenvalue_transpose_iff
    {α : Type u} [Fintype α] [DecidableEq α]
    (matrix : Matrix α α ℕ) (z : ℂ) :
    IsComplexEigenvalue matrix.transpose z ↔
      IsComplexEigenvalue matrix z := by
  rw [isComplexEigenvalue_iff_hasEigenvalue,
    isComplexEigenvalue_iff_hasEigenvalue,
    Module.End.hasEigenvalue_iff_mem_spectrum,
    Module.End.hasEigenvalue_iff_mem_spectrum,
    Matrix.spectrum_toLin', Matrix.spectrum_toLin',
    Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly]
  change (complexification matrix).transpose.charpoly.IsRoot z ↔
    (complexification matrix).charpoly.IsRoot z
  rw [Matrix.charpoly_transpose]

theorem dominantEigenvalue_transpose_iff
    {α : Type u} [Fintype α]
    (matrix : Matrix α α ℕ) (eigenvalue : ℝ) :
    IsDominantEigenvalue matrix.transpose eigenvalue ↔
      IsDominantEigenvalue matrix eigenvalue := by
  classical
  constructor
  · rintro ⟨heigen, hbound⟩
    refine ⟨(isComplexEigenvalue_transpose_iff matrix _).mp heigen, ?_⟩
    intro z hz
    exact hbound z
      ((isComplexEigenvalue_transpose_iff matrix z).mpr hz)
  · rintro ⟨heigen, hbound⟩
    refine ⟨(isComplexEigenvalue_transpose_iff matrix _).mpr heigen, ?_⟩
    intro z hz
    exact hbound z
      ((isComplexEigenvalue_transpose_iff matrix z).mp hz)

/-- Positive return-block weights satisfying the metric scaling law identify
the powered eigenvalue as the induced incidence spectral radius. -/
theorem dominantEigenvalue_of_positive_metric_scaling
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (source : Substitution α) (length : α → ℝ) (scale : ℝ)
    (hlength : ∀ letter, 0 < length letter)
    (hscale : SubstitutionScalesLetterLengths source length scale) :
    IsDominantEigenvalue source.incidenceMatrix scale := by
  have heigenTranspose : NatMatrixEigenvectorEquation
      source.incidenceMatrix.transpose length scale := by
    intro sourceLetter
    have hsource := hscale sourceLetter
    rw [wordMetricLength_eq_count_sum] at hsource
    simpa [Substitution.incidenceMatrix] using hsource
  have htranspose := positive_eigenvector_isDominant
    source.incidenceMatrix.transpose length scale hlength heigenTranspose
  exact (dominantEigenvalue_transpose_iff
    source.incidenceMatrix scale).mp htranspose


/-! ## D3: a periodic recurrent language gives an ultimately periodic tail -/

/-- Under syndeticity, every recurrent factor occurs inside a sufficiently
long power from a periodic recurrent-language witness. -/
theorem recurrentFactor_isInfix_wordPower
    {α : Type u} {word : InfiniteWord α}
    (hsyndetic : RecurrentFactorsSyndetic word)
    {periodWord factor : Word α}
    (hprimitive : IsPrimitiveFiniteWord periodWord)
    (hpowers : ∀ n : ℕ, 0 < n →
      IsRecurrentFactor word (wordPower periodWord n))
    (hfactor : IsRecurrentFactor word factor) :
    ∃ n : ℕ, factor <:+: wordPower periodWord n := by
  rcases hsyndetic factor hfactor with ⟨gap, hgap, hbounded⟩
  let exponent := gap + factor.length + 1
  have hexponent : 0 < exponent := by omega
  have hperiodLength : 0 < periodWord.length :=
    List.length_pos_of_ne_nil hprimitive.1
  have hblockLong :
      gap + factor.length ≤ (wordPower periodWord exponent).length := by
    rw [wordPower_length]
    have : exponent ≤ exponent * periodWord.length := by nlinarith
    omega
  rcases hpowers exponent hexponent 0 with
    ⟨blockStart, _hblockStart, hblock⟩
  rcases hbounded blockStart with ⟨offset, hoffset, hfactorAt⟩
  have hwithin : offset + factor.length ≤
      (wordPower periodWord exponent).length := by
    omega
  have hfactorLocal : InfiniteFactorAt (word.drop blockStart) factor offset :=
    by
      change ((word.drop blockStart).drop offset).take factor.length = factor
      simpa [Stream'.drop_drop, Nat.add_assoc] using hfactorAt
  change ((word.drop blockStart).drop offset).take factor.length = factor at hfactorLocal
  have hsplit := Stream'.take_add
    (a := word.drop blockStart) (m := offset) (n := factor.length)
  rw [hfactorLocal] at hsplit
  have hprefix := Stream'.take_prefix_take_left
    (a := word.drop blockStart)
    (m := offset + factor.length)
    (n := (wordPower periodWord exponent).length) hwithin
  change (word.drop blockStart).take
      (wordPower periodWord exponent).length =
    wordPower periodWord exponent at hblock
  rw [hsplit, hblock] at hprefix
  rcases hprefix with ⟨suffix, hsuffix⟩
  refine ⟨exponent, (word.drop blockStart).take offset, suffix, ?_⟩
  simpa [List.append_assoc] using hsuffix

/-- If every recurrent factor has bounded gaps and the recurrent language is
generated by powers of one primitive word, the original sequence has only a
finite transient prefix. -/
theorem periodicRecurrentLanguage_ultimatelyPeriodic
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (hsyndetic : RecurrentFactorsSyndetic word)
    (hperiodicLanguage : HasPeriodicRecurrentLanguage word) :
    IsUltimatelyPeriodic word := by
  rcases hperiodicLanguage with ⟨periodWord, hprimitive, hpowers⟩
  let period := periodWord.length
  have hperiodPos : 0 < period :=
    List.length_pos_of_ne_nil hprimitive.1
  obtain ⟨start, hstart⟩ :=
    eventually_every_fixedLengthFactor_recurrent word (period + 1)
  refine ⟨start, period, hperiodPos, ?_⟩
  intro n hn
  let factor := (word.drop n).take (period + 1)
  have hfactorRecurrent : IsRecurrentFactor word factor := by
    simpa [factor] using hstart n hn
  obtain ⟨power, hfactorPower⟩ :=
    recurrentFactor_isInfix_wordPower hsyndetic
      hprimitive hpowers hfactorRecurrent
  have hfactorPeriod : List.HasPeriod factor period := by
    apply (wordPower_hasPeriod periodWord power).infix hfactorPower
  have hget := (List.hasPeriod_iff_getElem?).mp hfactorPeriod 0 (by
    simp [factor, period])
  have hstream : (word.drop n).get 0 = (word.drop n).get period := by
    simpa [factor] using hget
  have hwhole : word.get n = word.get (n + period) := by
    simpa [Stream'.get_drop, Nat.add_comm] using hstream
  exact hwhole.symm


end

end Symbolic
end CommutingIntervalSimplified
