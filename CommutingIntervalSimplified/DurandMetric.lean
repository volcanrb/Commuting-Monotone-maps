import CommutingIntervalSimplified.DurandSupport
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Metric specialization of Durand's growing-substitution theorem

This module freezes the replacement for the polynomial--exponential growth
and increasing-local-power skeleton in `Durand.lean`.  The geometric coding
used by this project supplies more information than a general growing
substitution: one strictly positive letter metric is scaled exactly by each
substitution.  The local return systems below therefore use fixed (hence
bounded) source powers.  Strictly increasing exponents occur only later in
Durand's Proposition 10 and never enter the finite-table bound.

The periodic recurrent-language branch is split off before any aperiodic
return-word lower bound or decoder argument.  This is essential for periodic
examples such as the one-letter substitutions `a |-> aa` and `a |-> aaa`.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

open Function Set
open scoped BigOperators

noncomputable section

universe u

/-! ## M0: exact metric presentations -/

/-- A growing fixed presentation together with the positive metric actually
produced by the interval coding. -/
structure MetricGrowingFixedPresentation {α : Type u}
    [Fintype α] [DecidableEq α]
    (σ : Substitution α) (seed : α) (word : InfiniteWord α)
    (eigenvalue : ℝ) (letterLength : α → ℝ) : Prop
    extends GrowingFixedPresentation σ seed word eigenvalue where
  letterLength_pos : ∀ letter, 0 < letterLength letter
  scales : SubstitutionScalesLetterLengths σ letterLength eigenvalue

/-! ## M1: higher blocks and syndetic recurrent factors -/

/-- A finite positive letter metric bounds the metric length of a word by
its ordinary length times the total alphabet weight.  This elementary
comparison is used only to turn exact metric expansion into ordinary word
growth; it does not package the obsolete global growth-bound record. -/
private theorem wordMetricLength_le_length_mul_totalWeight
    {α : Type u} [Fintype α] [DecidableEq α]
    (letterLength : α → ℝ) (hlength : ∀ letter, 0 ≤ letterLength letter) :
    ∀ letters : Word α,
      wordMetricLength letterLength letters ≤
        (letters.length : ℝ) * ∑ letter : α, letterLength letter := by
  intro letters
  induction letters with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      have hhead : letterLength head ≤ ∑ letter : α, letterLength letter :=
        Finset.single_le_sum (fun letter _ => hlength letter)
          (Finset.mem_univ head)
      have htotal : 0 ≤ ∑ letter : α, letterLength letter :=
        Finset.sum_nonneg fun letter _ => hlength letter
      simp only [wordMetricLength, List.map_cons, List.sum_cons,
        List.length_cons, Nat.cast_add, Nat.cast_one]
      change letterLength head + wordMetricLength letterLength tail ≤
        ((tail.length : ℝ) + 1) * ∑ letter : α, letterLength letter
      nlinarith

private def higherBlockFirst
    {α : Type u} {word : InfiniteWord α} {blockLength : ℕ}
    (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength) : α :=
  block.1.head (List.ne_nil_of_length_pos (by simpa [block.2.1]))

/-- The canonical common metric on occurring higher blocks: the weight of a
block is the weight of its first letter.  Naming it independently of either
substitution is what preserves the common-metric hypothesis after passing to
higher blocks. -/
def occurringHigherBlockMetric
    {α : Type u} {word : InfiniteWord α} {blockLength : ℕ}
    (hblockLength : 0 < blockLength) (letterLength : α → ℝ)
    (block : OccurringHigherBlock word blockLength) : ℝ :=
  letterLength (higherBlockFirst hblockLength block)

/-- The occurring higher-block presentation, retaining its positive metric.
The weight of a block is the weight of its first letter; the induced image
has one output block for each position in the image of that first letter. -/
structure MetricHigherBlockPresentationData
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation σ seed word eigenvalue letterLength)
    (blockLength : ℕ) where
  blockLength_pos : 0 < blockLength
  substitution : Substitution (OccurringHigherBlock word blockLength)
  presentation : MetricGrowingFixedPresentation substitution
    (higherBlockWord word blockLength).head
    (higherBlockWord word blockLength) eigenvalue
      (occurringHigherBlockMetric blockLength_pos letterLength)

/-! ### M1.1 internal construction skeleton

The following declarations expose every mathematical step of the standard
boundary-aware higher-block construction.  In particular, fixedness is not
hidden in the final package: the substituted source cuts and their finite
tiling of the higher-block word are displayed explicitly. -/

private def higherBlockRawWindow
    {α : Type u} {word : InfiniteWord α} (source : Substitution α)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength)
    (offset : Fin (source (higherBlockFirst hblockLength block)).length) :
    Word α :=
  ((source.mapWord block.1).drop offset).take blockLength

/-- M1.1a: nonerasing images of the remaining `blockLength - 1` letters
provide enough right context for every displayed window. -/
private theorem higherBlockRawWindow_length
    {α : Type u} {word : InfiniteWord α} (source : Substitution α)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength)
    (offset : Fin (source (higherBlockFirst hblockLength block)).length) :
    (higherBlockRawWindow source hblockLength block offset).length =
      blockLength := by
  rcases block with ⟨block, hblockLengthEq, hoccurs⟩
  cases block with
  | nil => simp at hblockLengthEq; omega
  | cons head tail =>
      have htailLength : tail.length + 1 = blockLength := by
        simpa using hblockLengthEq
      have hoffset : (offset : ℕ) < (source head).length := by
        simpa [higherBlockFirst] using offset.isLt
      have htailImage : tail.length ≤ (source.mapWord tail).length :=
        source.length_le_mapWord tail
      apply List.length_take_of_le
      simp only [higherBlockRawWindow, Substitution.mapWord_cons,
        List.length_drop, List.length_append]
      omega

/-- M1.1b: a raw image window is an actual factor of the fixed word. -/
private theorem higherBlockRawWindow_occurs
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength)
    (offset : Fin (source (higherBlockFirst hblockLength block)).length) :
    IsInfiniteFactor word
      (higherBlockRawWindow source hblockLength block offset) := by
  obtain ⟨position, hblockAt⟩ := block.2.2
  have hsourceBlock :
      (word.drop position).take blockLength = block.1 := by
    simpa [InfiniteFactorAt, block.2.1] using hblockAt
  have hambient :=
    Substitution.mapWord_drop_take_at_fixed P.fixed position blockLength
  rw [hsourceBlock] at hambient
  have hwindowLength :=
    higherBlockRawWindow_length source hblockLength block offset
  have hdropLong : blockLength ≤
      ((source.mapWord block.1).drop (offset : ℕ)).length := by
    rw [higherBlockRawWindow, List.length_take] at hwindowLength
    omega
  have hwithin : (offset : ℕ) +
      (higherBlockRawWindow source hblockLength block offset).length ≤
        (source.mapWord block.1).length := by
    rw [hwindowLength]
    simp only [List.length_drop] at hdropLong
    omega
  have hfinite : FiniteFactorAt (source.mapWord block.1)
      (higherBlockRawWindow source hblockLength block offset) offset := by
    refine ⟨hwithin, ?_⟩
    rw [hwindowLength]
    rfl
  exact ⟨_, InfiniteFactorAt.of_finiteFactorAt hambient hfinite⟩

private def higherBlockImageLetter
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength)
    (offset : Fin (source (higherBlockFirst hblockLength block)).length) :
    OccurringHigherBlock word blockLength :=
  ⟨higherBlockRawWindow source hblockLength block offset,
    higherBlockRawWindow_length source hblockLength block offset,
    higherBlockRawWindow_occurs P hblockLength block offset⟩

private theorem higherBlockFirst_higherBlockWord
    {α : Type u} {word : InfiniteWord α} {blockLength : ℕ}
    (hblockLength : 0 < blockLength) (position : ℕ) :
    higherBlockFirst hblockLength
        (higherBlockWord word blockLength position) = word position := by
  rw [higherBlockFirst, List.head_eq_getElem_zero]
  simp [higherBlockWord]
  rfl

private theorem higherBlockFirst_imageLetter
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength)
    (offset : Fin (source (higherBlockFirst hblockLength block)).length) :
    higherBlockFirst hblockLength
        (higherBlockImageLetter P hblockLength block offset) =
      (source (higherBlockFirst hblockLength block))[(offset : ℕ)]'
        offset.isLt := by
  rcases block with ⟨block, hblockLengthEq, hoccurs⟩
  cases block with
  | nil => simp at hblockLengthEq; omega
  | cons head tail =>
      rw [higherBlockFirst, List.head_eq_getElem_zero]
      simp [higherBlockImageLetter, higherBlockRawWindow,
        higherBlockFirst, Substitution.mapWord_cons]

private def higherBlockInducedImage
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength) :
    Word (OccurringHigherBlock word blockLength) :=
  List.ofFn fun offset => higherBlockImageLetter P hblockLength block offset

/-- M1.1c: the induced image is nonempty, with length exactly the image
length of the first source letter. -/
private theorem higherBlockInducedImage_length
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (block : OccurringHigherBlock word blockLength) :
    (higherBlockInducedImage P hblockLength block).length =
      (source (higherBlockFirst hblockLength block)).length := by
  simp [higherBlockInducedImage]

private def higherBlockInducedSubstitution
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength) :
    Substitution (OccurringHigherBlock word blockLength) where
  image := higherBlockInducedImage P hblockLength
  image_ne_nil block := by
    apply List.ne_nil_of_length_pos
    rw [higherBlockInducedImage_length]
    exact List.length_pos_of_ne_nil
      (source.image_ne_nil (higherBlockFirst hblockLength block))

private def higherBlockSubstitutionCut
    {α : Type u} (source : Substitution α) (word : InfiniteWord α)
    (position : ℕ) : ℕ :=
  (source.mapWord (word.take position)).length

/-- M1.1d: substituted source cuts start at zero and advance by precisely
the image length of the next source letter. -/
private theorem higherBlockSubstitutionCut_zero_succ
    {α : Type u} (source : Substitution α) (word : InfiniteWord α) :
    higherBlockSubstitutionCut source word 0 = 0 ∧
      ∀ position : ℕ,
        higherBlockSubstitutionCut source word (position + 1) =
          higherBlockSubstitutionCut source word position +
            (source (word position)).length := by
  constructor
  · simp [higherBlockSubstitutionCut]
  · intro position
    unfold higherBlockSubstitutionCut
    rw [Stream'.take_succ', Substitution.mapWord_append]
    simp only [Substitution.mapWord_cons, Substitution.mapWord_nil,
      List.append_nil, List.length_append]
    rfl

private theorem higherBlockRawWindow_at_substitutionCut
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (position : ℕ)
    (offset : Fin
      (source (higherBlockFirst hblockLength
        (higherBlockWord word blockLength position))).length) :
    InfiniteFactorAt word
      (higherBlockRawWindow source hblockLength
        (higherBlockWord word blockLength position) offset)
      (higherBlockSubstitutionCut source word position + (offset : ℕ)) := by
  let block := higherBlockWord word blockLength position
  have hambient :=
    Substitution.mapWord_drop_take_at_fixed P.fixed position blockLength
  change InfiniteFactorAt word (source.mapWord block.1)
    (higherBlockSubstitutionCut source word position) at hambient
  have hwindowLength :=
    higherBlockRawWindow_length source hblockLength block offset
  have hdropLong : blockLength ≤
      ((source.mapWord block.1).drop (offset : ℕ)).length := by
    rw [higherBlockRawWindow, List.length_take] at hwindowLength
    omega
  have hwithin : (offset : ℕ) +
      (higherBlockRawWindow source hblockLength block offset).length ≤
        (source.mapWord block.1).length := by
    rw [hwindowLength]
    simp only [List.length_drop] at hdropLong
    omega
  have hfinite : FiniteFactorAt (source.mapWord block.1)
      (higherBlockRawWindow source hblockLength block offset) offset := by
    refine ⟨hwithin, ?_⟩
    rw [hwindowLength]
    rfl
  exact InfiniteFactorAt.of_finiteFactorAt hambient hfinite

/-- M1.1e: the image of the block at source position `position` is exactly
the consecutive higher-block segment beginning at the substituted cut. -/
private theorem higherBlockInducedImage_alignment
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength)
    (position : ℕ) :
    higherBlockInducedImage P hblockLength
        (higherBlockWord word blockLength position) =
      ((higherBlockWord word blockLength).drop
        (higherBlockSubstitutionCut source word position)).take
          (source (word position)).length := by
  let block := higherBlockWord word blockLength position
  change higherBlockInducedImage P hblockLength block = _
  apply List.ext_getElem
  · rw [higherBlockInducedImage_length]
    simp [block, higherBlockFirst_higherBlockWord]
  · intro index hleft hright
    have hsourceIndex : index <
        (source (higherBlockFirst hblockLength block)).length := by
      rw [higherBlockInducedImage_length] at hleft
      exact hleft
    let offset : Fin
        (source (higherBlockFirst hblockLength block)).length :=
      ⟨index, hsourceIndex⟩
    have hat := higherBlockRawWindow_at_substitutionCut
      P hblockLength position offset
    have hwindowLength := higherBlockRawWindow_length
      source hblockLength block offset
    rw [InfiniteFactorAt, hwindowLength] at hat
    have hleftGet :
        (higherBlockInducedImage P hblockLength block)[index]'hleft =
          higherBlockImageLetter P hblockLength block offset := by
      simp [higherBlockInducedImage, offset]
    have hrightGet :
        (((higherBlockWord word blockLength).drop
            (higherBlockSubstitutionCut source word position)).take
              (source (word position)).length)[index]'hright =
          higherBlockWord word blockLength
            (higherBlockSubstitutionCut source word position + index) := by
      simp
      rfl
    rw [hleftGet, hrightGet]
    apply Subtype.ext
    exact hat.symm

private theorem metric_mapInfinite_append_stream
    {β : Type u} (source : Substitution β) (finitePrefix : Word β)
    (stream : InfiniteWord β) :
    source.mapInfinite (finitePrefix ++ₛ stream) =
      source.mapWord finitePrefix ++ₛ source.mapInfinite stream := by
  induction finitePrefix with
  | nil => rfl
  | cons letter rest ih =>
      rw [Stream'.cons_append_stream,
        source.mapInfinite_eq_append_first_image,
        Stream'.head_cons, Stream'.tail_cons, ih,
        Substitution.mapWord_cons, Stream'.append_append_stream]

/-- M1.1f: any nonerasing substitution whose images tile a stream along
successive cuts fixes that stream. -/
private theorem fixedPoint_of_cut_aligned_images
    {β : Type u} (source : Substitution β) (stream : InfiniteWord β)
    (cut : ℕ → ℕ)
    (hcut_zero : cut 0 = 0)
    (hcut_succ : ∀ position : ℕ,
      cut (position + 1) = cut position + (source (stream position)).length)
    (haligned : ∀ position : ℕ,
      source (stream position) =
        (stream.drop (cut position)).take
          (source (stream position)).length) :
    source.IsFixedPoint stream := by
  have hcutLower : ∀ position : ℕ, position ≤ cut position := by
    intro position
    induction position with
    | zero => simp [hcut_zero]
    | succ position ih =>
        rw [hcut_succ]
        have hpositive : 0 < (source (stream position)).length :=
          List.length_pos_of_ne_nil (source.image_ne_nil (stream position))
        omega
  have hfiniteTiling : ∀ count : ℕ,
      source.mapWord (stream.take count) = stream.take (cut count) := by
    intro count
    induction count with
    | zero => simp [hcut_zero]
    | succ count ih =>
        rw [Stream'.take_succ', Substitution.mapWord_append,
          Substitution.mapWord_cons, Substitution.mapWord_nil,
          List.append_nil, ih, hcut_succ, Stream'.take_add]
        exact congrArg (fun tail => stream.take (cut count) ++ tail)
          (haligned count)
  rw [Substitution.IsFixedPoint]
  funext position
  let count := position + 1
  have hposition : position < cut count := by
    have hbound := hcutLower count
    omega
  have hwordLength :
      (source.mapWord (stream.take count)).length = cut count := by
    rw [hfiniteTiling]
    simp
  have hmapPrefix :
      (source.mapInfinite stream).take (cut count) =
        source.mapWord (stream.take count) := by
    rw [← hwordLength]
    calc
      (source.mapInfinite stream).take
          (source.mapWord (stream.take count)).length =
        (source.mapInfinite
          (stream.take count ++ₛ stream.drop count)).take
            (source.mapWord (stream.take count)).length := by
              rw [Stream'.append_take_drop]
      _ = (source.mapWord (stream.take count) ++ₛ
          source.mapInfinite (stream.drop count)).take
            (source.mapWord (stream.take count)).length := by
              rw [metric_mapInfinite_append_stream]
      _ = source.mapWord (stream.take count) := by
          simpa using Stream'.take_append_of_le_length
            (x := source.mapWord (stream.take count))
            (a := source.mapInfinite (stream.drop count))
            (n := (source.mapWord (stream.take count)).length) le_rfl
  have hprefix :
      (source.mapInfinite stream).take (cut count) =
        stream.take (cut count) :=
    hmapPrefix.trans (hfiniteTiling count)
  have hleftIndex : position <
      ((source.mapInfinite stream).take (cut count)).length := by
    simpa using hposition
  have hrightIndex : position < (stream.take (cut count)).length := by
    simpa using hposition
  have hleftGet := Stream'.take_get
    (a := source.mapInfinite stream) (m := position)
    (n := cut count) hleftIndex
  have hrightGet := Stream'.take_get
    (a := stream) (m := position) (n := cut count) hrightIndex
  change Stream'.get (source.mapInfinite stream) position =
    Stream'.get stream position
  rw [← hleftGet, ← hrightGet]
  rw [← Option.some_inj, ← List.getElem?_eq_getElem,
    ← List.getElem?_eq_getElem]
  exact congrArg (fun letters => letters[position]?) hprefix

private theorem higherBlockInduced_fixed
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength) :
    (higherBlockInducedSubstitution P hblockLength).IsFixedPoint
      (higherBlockWord word blockLength) := by
  have hcut := higherBlockSubstitutionCut_zero_succ source word
  refine fixedPoint_of_cut_aligned_images
    (higherBlockInducedSubstitution P hblockLength)
    (higherBlockWord word blockLength)
    (higherBlockSubstitutionCut source word) hcut.1 ?_ ?_
  · intro position
    rw [hcut.2]
    congr 1
    rw [show
      (higherBlockInducedSubstitution P hblockLength)
          (higherBlockWord word blockLength position) =
        higherBlockInducedImage P hblockLength
          (higherBlockWord word blockLength position) from rfl]
    rw [higherBlockInducedImage_length,
      higherBlockFirst_higherBlockWord]
  · intro position
    change higherBlockInducedImage P hblockLength
        (higherBlockWord word blockLength position) = _
    rw [show
      (higherBlockInducedSubstitution P hblockLength)
          (higherBlockWord word blockLength position) =
        higherBlockInducedImage P hblockLength
          (higherBlockWord word blockLength position) from rfl]
    rw [higherBlockInducedImage_length,
      higherBlockFirst_higherBlockWord]
    exact higherBlockInducedImage_alignment P hblockLength position

private abbrev higherBlockInheritedMetric
    {α : Type u} {word : InfiniteWord α} {blockLength : ℕ}
    (hblockLength : 0 < blockLength) (letterLength : α → ℝ)
    (block : OccurringHigherBlock word blockLength) : ℝ :=
  occurringHigherBlockMetric hblockLength letterLength block

/-- M1.1g: the induced image has the same metric length as the source
image of its first letter, and hence scales the inherited metric exactly. -/
private theorem higherBlockInduced_scales
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength) :
    SubstitutionScalesLetterLengths
      (higherBlockInducedSubstitution P hblockLength)
      (higherBlockInheritedMetric hblockLength letterLength) eigenvalue := by
  intro block
  change wordMetricLength
      (higherBlockInheritedMetric hblockLength letterLength)
      (higherBlockInducedImage P hblockLength block) =
    eigenvalue * letterLength (higherBlockFirst hblockLength block)
  rw [← P.scales (higherBlockFirst hblockLength block)]
  simp only [wordMetricLength, higherBlockInducedImage, List.map_ofFn]
  have hfunctions :
      (higherBlockInheritedMetric hblockLength letterLength ∘
          fun offset => higherBlockImageLetter P hblockLength block offset) =
        (fun offset : Fin
            (source (higherBlockFirst hblockLength block)).length =>
          letterLength
            ((source (higherBlockFirst hblockLength block))[(offset : ℕ)]'
              offset.isLt)) := by
    funext offset
    exact congrArg letterLength
      (higherBlockFirst_imageLetter P hblockLength block offset)
  rw [hfunctions]
  exact congrArg List.sum
    (List.ofFn_getElem_eq_map
      (source (higherBlockFirst hblockLength block)) letterLength)

/-- M1.1h: every occurring block occurs as a letter of the displayed
higher-block word. -/
private theorem higherBlock_every_letter_occurs
    {α : Type u} {word : InfiniteWord α} {blockLength : ℕ} :
    ∀ block : OccurringHigherBlock word blockLength,
      Substitution.OccursInInfiniteWord block
        (higherBlockWord word blockLength) := by
  intro block
  obtain ⟨position, hposition⟩ := block.2.2
  refine ⟨position, Subtype.ext ?_⟩
  simpa [higherBlockWord, InfiniteFactorAt, block.2.1] using hposition

/-- M1.1i: exact expansion of a positive metric by a factor greater than
one forces ordinary substitution growth. -/
private theorem growing_of_exact_positive_metric
    {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (source : Substitution β) (metric : β → ℝ) (scale : ℝ)
    (hmetric : ∀ letter, 0 < metric letter)
    (hscales : SubstitutionScalesLetterLengths source metric scale)
    (hone : 1 < scale) :
    source.IsGrowing := by
  intro letter bound
  let total : ℝ := ∑ other : β, metric other
  have hletter_le : metric letter ≤ total := by
    dsimp [total]
    exact Finset.single_le_sum (fun other _ => (hmetric other).le)
      (Finset.mem_univ letter)
  have htotal_pos : 0 < total := (hmetric letter).trans_le hletter_le
  have hiterateMetric (n : ℕ) :
      wordMetricLength metric (source.iterateLetter n letter) =
        scale ^ n * metric letter := by
    have hpower := scalesLetterLengths_power hscales n letter
    simpa [Substitution.power_apply] using hpower
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      ((bound : ℝ) * total) / metric letter < scale ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop _
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventually
  have hlarge := hthreshold threshold le_rfl
  refine ⟨threshold, le_of_not_gt fun htooShort => ?_⟩
  have htooShortReal :
      ((source.iterateLetter threshold letter).length : ℝ) < bound := by
    exact_mod_cast htooShort
  have hmetricUpper := wordMetricLength_le_length_mul_totalWeight metric
    (fun other => (hmetric other).le)
    (source.iterateLetter threshold letter)
  rw [hiterateMetric] at hmetricUpper
  have hlarge' : (bound : ℝ) * total <
      scale ^ threshold * metric letter :=
    (div_lt_iff₀ (hmetric letter)).mp hlarge
  have htooShortProduct :
      ((source.iterateLetter threshold letter).length : ℝ) * total <
        (bound : ℝ) * total :=
    mul_lt_mul_of_pos_right htooShortReal htotal_pos
  nlinarith

/-- M1.1j: assemble the induced fixed, growing, dominant exact-metric
presentation. -/
private theorem higherBlockInducedPresentation
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {blockLength : ℕ} (hblockLength : 0 < blockLength) :
    MetricGrowingFixedPresentation
      (higherBlockInducedSubstitution P hblockLength)
      (higherBlockWord word blockLength).head
      (higherBlockWord word blockLength) eigenvalue
      (higherBlockInheritedMetric hblockLength letterLength) := by
  letI : Nonempty (OccurringHigherBlock word blockLength) :=
    ⟨(higherBlockWord word blockLength).head⟩
  have hmetricPos : ∀ block : OccurringHigherBlock word blockLength,
      0 < higherBlockInheritedMetric hblockLength letterLength block := by
    intro block
    exact P.letterLength_pos (higherBlockFirst hblockLength block)
  have hscales := higherBlockInduced_scales P hblockLength
  have hfixed := higherBlockInduced_fixed P hblockLength
  have hgrowing := growing_of_exact_positive_metric
    (higherBlockInducedSubstitution P hblockLength)
    (higherBlockInheritedMetric hblockLength letterLength)
    eigenvalue hmetricPos hscales P.one_lt_eigenvalue
  have hprolongable :=
    prolongableOn_head_of_growing_fixedPoint hfixed hgrowing
  have hdominant := dominantEigenvalue_of_positive_metric_scaling
    (higherBlockInducedSubstitution P hblockLength)
    (higherBlockInheritedMetric hblockLength letterLength)
    eigenvalue hmetricPos hscales
  exact {
    nonerasing :=
      (higherBlockInducedSubstitution P hblockLength).image_ne_nil
    prolongable := hprolongable
    fixed := hfixed
    every_letter_occurs := higherBlock_every_letter_occurs
    growing := hgrowing
    one_lt_eigenvalue := P.one_lt_eigenvalue
    dominant := hdominant
    letterLength_pos := hmetricPos
    scales := hscales
  }

/-- M1.1: construct the boundary-aware occurring higher-block substitution
and its exact inherited metric scaling. -/
theorem metricHigherBlockPresentationData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation σ seed word eigenvalue letterLength)
    (blockLength : ℕ) (hblockLength : 0 < blockLength) :
    Nonempty (MetricHigherBlockPresentationData P blockLength) := by
  exact ⟨{
    blockLength_pos := hblockLength
    substitution := higherBlockInducedSubstitution P hblockLength
    presentation := higherBlockInducedPresentation P hblockLength
  }⟩

/-! ### M1.2 internal Durand--Rigo syndeticity skeleton

Durand--Rigo prove a stronger theorem for two unrelated substitutive
presentations by first developing ordinary-length Perron asymptotics.  The
interval coding in this project supplies one common positive edge metric,
scaled exactly by both substitutions.  Thus substituted cut coordinates are
exact, and the ordinary Perron layer is neither needed nor asserted here.

The remaining declarations isolate the specialization of Durand--Rigo,
Theorem 17, case 5.5: stabilized image alphabets, persistent avoiding letters,
metric gap bounds, cofinal density of independent powers, and the two
prefix/suffix crossings. -/

/-- A finite word contains no occurrence of the displayed letter. -/
def WordAvoidsLetter {α : Type u} (letter : α) (letters : Word α) : Prop :=
  letter ∉ letters

/-- A half-open interval of a one-sided word contains no displayed letter. -/
def LetterAbsentOnInterval {α : Type u} (word : InfiniteWord α)
    (letter : α) (start intervalLength : ℕ) : Prop :=
  ∀ offset : ℕ, offset < intervalLength → word (start + offset) ≠ letter

/-- M1.2a.1: the finite orbit of every iterated image support is eventually
periodic, uniformly over the finite alphabet. -/
structure IteratedSupportOrbitData {α : Type u}
    [Fintype α] [DecidableEq α] (source : Substitution α) where
  cutoff : ℕ
  period : ℕ
  period_pos : 0 < period
  support_periodic : ∀ letter : α, ∀ n : ℕ, cutoff ≤ n →
    Substitution.AlphabetOfWord (source.iterateLetter (n + period) letter) =
      Substitution.AlphabetOfWord (source.iterateLetter n letter)

private theorem alphabetOfWord_mapWord_eq_of_alphabet_eq
    {α : Type u} [DecidableEq α] (source : Substitution α)
    {left right : Word α}
    (h : Substitution.AlphabetOfWord left =
      Substitution.AlphabetOfWord right) :
    Substitution.AlphabetOfWord (source.mapWord left) =
      Substitution.AlphabetOfWord (source.mapWord right) := by
  ext output
  simp only [Substitution.mem_alphabetOfWord_iff,
    Substitution.OccursInWord, Substitution.mapWord, List.mem_flatMap]
  constructor
  · rintro ⟨input, hinput, houtput⟩
    have hinput' : input ∈ Substitution.AlphabetOfWord left := by
      simpa [Substitution.AlphabetOfWord] using hinput
    have : input ∈ Substitution.AlphabetOfWord right := by
      simpa [h] using hinput'
    exact ⟨input, by
      simpa [Substitution.AlphabetOfWord] using this, houtput⟩
  · rintro ⟨input, hinput, houtput⟩
    have hinput' : input ∈ Substitution.AlphabetOfWord right := by
      simpa [Substitution.AlphabetOfWord] using hinput
    have : input ∈ Substitution.AlphabetOfWord left := by
      simpa [h] using hinput'
    exact ⟨input, by
      simpa [Substitution.AlphabetOfWord] using this, houtput⟩

private theorem iteratedSupport_state_succ_congr
    {α : Type u} [Fintype α] [DecidableEq α]
    (source : Substitution α) {left right : ℕ}
    (h : (fun letter : α => Substitution.AlphabetOfWord
      (source.iterateLetter left letter)) =
      fun letter : α => Substitution.AlphabetOfWord
        (source.iterateLetter right letter)) :
    (fun letter : α => Substitution.AlphabetOfWord
      (source.iterateLetter (left + 1) letter)) =
      fun letter : α => Substitution.AlphabetOfWord
        (source.iterateLetter (right + 1) letter) := by
  funext letter
  rw [Substitution.iterateLetter_succ, Substitution.iterateLetter_succ]
  exact alphabetOfWord_mapWord_eq_of_alphabet_eq source
    (congrFun h letter)

theorem iteratedSupportOrbitData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    (source : Substitution α) :
    Nonempty (IteratedSupportOrbitData source) := by
  let state : ℕ → (α → Finset α) := fun n letter =>
    Substitution.AlphabetOfWord (source.iterateLetter n letter)
  obtain ⟨first, second, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite state
  obtain ⟨cutoff, later, hlt, hstate⟩ :
      ∃ cutoff later : ℕ, cutoff < later ∧ state cutoff = state later := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨first, second, hlt, heq⟩
    · exact ⟨second, first, hgt, heq.symm⟩
  let period := later - cutoff
  have hperiod_pos : 0 < period := Nat.sub_pos_of_lt hlt
  have hcutoff_period : cutoff + period = later := by
    dsimp [period]
    omega
  have hshift : ∀ offset : ℕ,
      state (cutoff + offset) = state (later + offset) := by
    intro offset
    induction offset with
    | zero => simpa using hstate
    | succ offset ih =>
        have hnext := iteratedSupport_state_succ_congr source ih
        simpa [Nat.add_assoc] using hnext
  refine ⟨{
    cutoff := cutoff
    period := period
    period_pos := hperiod_pos
    support_periodic := ?_
  }⟩
  intro letter n hn
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := congrFun (hshift offset) letter
  rw [← hcutoff_period] at h
  simpa [state, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h.symm

/-- A positive power whose positive iterates have stabilized letter support,
together with the exact powered fixed-point and metric laws. -/
structure StableMetricPowerData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength) where
  power : ℕ
  power_pos : 0 < power
  support_stable : ∀ letter : α, ∀ n : ℕ, 0 < n →
    Substitution.AlphabetOfWord
        ((source.power power).iterateLetter n letter) =
      Substitution.AlphabetOfWord ((source.power power) letter)
  fixed : (source.power power).IsFixedPoint word
  scales : SubstitutionScalesLetterLengths (source.power power)
    letterLength (eigenvalue ^ power)
  one_lt_scale : 1 < eigenvalue ^ power

private theorem iterateWord_add_metric
    {α : Type u} (source : Substitution α) (left right : ℕ)
    (letters : Word α) :
    source.iterateWord (left + right) letters =
      source.iterateWord left (source.iterateWord right letters) := by
  induction left with
  | zero => simp
  | succ left ih =>
      simpa only [Nat.succ_add, Substitution.iterateWord_succ]
        using congrArg source.mapWord ih

private theorem iterateWord_power_metric
    {α : Type u} (source : Substitution α) (power iterate : ℕ)
    (letters : Word α) :
    (source.power power).iterateWord iterate letters =
      source.iterateWord (power * iterate) letters := by
  induction iterate with
  | zero => rfl
  | succ iterate ih =>
      calc
        (source.power power).iterateWord (iterate + 1) letters =
            (source.power power).mapWord
              ((source.power power).iterateWord iterate letters) := rfl
        _ = source.iterateWord power
              ((source.power power).iterateWord iterate letters) :=
          Substitution.power_mapWord source power _
        _ = source.iterateWord power
              (source.iterateWord (power * iterate) letters) :=
          congrArg (source.iterateWord power) ih
        _ = source.iterateWord (power + power * iterate) letters :=
          (iterateWord_add_metric source power (power * iterate) letters).symm
        _ = source.iterateWord (power * (iterate + 1)) letters := by
          simp [Nat.mul_succ, Nat.add_comm]

private theorem iterateLetter_power_metric
    {α : Type u} (source : Substitution α) (power iterate : ℕ)
    (letter : α) :
    (source.power power).iterateLetter iterate letter =
      source.iterateLetter (power * iterate) letter :=
  iterateWord_power_metric source power iterate [letter]

private theorem iteratedSupport_periodic_mul
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} (orbit : IteratedSupportOrbitData source)
    (letter : α) {start : ℕ} (hstart : orbit.cutoff ≤ start) :
    ∀ repetitions : ℕ,
      Substitution.AlphabetOfWord
          (source.iterateLetter (start + repetitions * orbit.period) letter) =
        Substitution.AlphabetOfWord (source.iterateLetter start letter) := by
  intro repetitions
  induction repetitions with
  | zero => simp
  | succ repetitions ih =>
      calc
        Substitution.AlphabetOfWord
            (source.iterateLetter
              (start + (repetitions + 1) * orbit.period) letter) =
            Substitution.AlphabetOfWord
              (source.iterateLetter
                ((start + repetitions * orbit.period) + orbit.period) letter) := by
          congr 2
          rw [Nat.succ_mul]
          omega
        _ = Substitution.AlphabetOfWord
              (source.iterateLetter
                (start + repetitions * orbit.period) letter) :=
          orbit.support_periodic letter _ (by omega)
        _ = Substitution.AlphabetOfWord
              (source.iterateLetter start letter) := ih

/-- M1.2a.2: pass from eventual periodic support orbits to one globally
stable positive power. -/
theorem stableMetricPowerData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    (orbit : IteratedSupportOrbitData source) :
    Nonempty (StableMetricPowerData P) := by
  let power := (orbit.cutoff + 1) * orbit.period
  have hperiod_one : 1 ≤ orbit.period := orbit.period_pos
  have hpower_pos : 0 < power := by
    dsimp [power]
    exact Nat.mul_pos (Nat.succ_pos _) orbit.period_pos
  have hcutoff_le_power : orbit.cutoff ≤ power := by
    have hle : orbit.cutoff + 1 ≤ power := by
      dsimp [power]
      exact le_mul_of_one_le_right' hperiod_one
    omega
  refine ⟨{
    power := power
    power_pos := hpower_pos
    support_stable := ?_
    fixed := Substitution.isFixedPoint_power P.fixed hpower_pos
    scales := scalesLetterLengths_power P.scales power
    one_lt_scale := one_lt_pow₀ P.one_lt_eigenvalue hpower_pos.ne'
  }⟩
  intro letter n hn
  obtain ⟨iterate, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [iterateLetter_power_metric, Substitution.power_apply]
  have hperiodic := iteratedSupport_periodic_mul orbit letter
    hcutoff_le_power (iterate * (orbit.cutoff + 1))
  convert hperiodic using 1 <;> dsimp [power] <;> ring_nf

/-- Arbitrarily late physical intervals of every prescribed length avoid the
letter.  Recurrence rules out one fixed infinite terminal gap. -/
def HasArbitrarilyLateAvoidingIntervals {α : Type u}
    (word : InfiniteWord α) (letter : α) : Prop :=
  ∀ minimumStart intervalLength : ℕ, ∃ start : ℕ,
    minimumStart ≤ start ∧
      LetterAbsentOnInterval word letter start intervalLength

/-- M1.2b.1: recurrent but nonsyndetic letters have arbitrarily late,
arbitrarily long avoiding intervals. -/
theorem arbitrarilyLateAvoidingIntervals_of_recurrent_not_boundedGaps
    {α : Type u} {word : InfiniteWord α} {letter : α}
    (hrecurrent : OccursInfinitelyOften word letter)
    (hnotBounded : ¬ LetterAppearsWithBoundedGaps word letter) :
    HasArbitrarilyLateAvoidingIntervals word letter := by
  intro minimumStart intervalLength
  by_cases hlength : intervalLength = 0
  · subst intervalLength
    exact ⟨minimumStart, le_rfl, by
      intro offset hoff
      omega⟩
  · by_contra hnoAvoiding
    apply hnotBounded
    obtain ⟨anchor, hanchorStart, hanchor⟩ := hrecurrent minimumStart
    refine ⟨anchor + intervalLength + 1, by omega, ?_⟩
    intro start
    by_cases hlate : minimumStart ≤ start
    · have hhit : ∃ offset : ℕ, offset < intervalLength ∧
          word (start + offset) = letter := by
        by_contra hnoHit
        apply hnoAvoiding
        refine ⟨start, hlate, ?_⟩
        intro offset hoff heq
        exact hnoHit ⟨offset, hoff, heq⟩
      obtain ⟨offset, hoffset, hat⟩ := hhit
      exact ⟨offset, by omega, hat⟩
    · refine ⟨anchor - start, by omega, ?_⟩
      have hstartAnchor : start ≤ anchor := by omega
      rw [Nat.add_sub_of_le hstartAnchor]
      exact hanchor

/-- Every level and every late source tail supplies a whole powered image
which avoids the target letter. -/
def HasArbitrarilyLateAvoidingImages
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    (stable : StableMetricPowerData P) (target : α) : Prop :=
  ∀ level cutoff : ℕ, ∃ position : ℕ, cutoff ≤ position ∧
    WordAvoidsLetter target
      ((source.power stable.power).iterateLetter level (word position))

private theorem letter_position_of_infiniteFactorAt
    {α : Type u} {word : InfiniteWord α} {factor : Word α}
    {start : ℕ} (hfactor : InfiniteFactorAt word factor start)
    {letter : α} (hletter : letter ∈ factor) :
    ∃ offset : ℕ, offset < factor.length ∧
      word (start + offset) = letter := by
  have hletter' : letter ∈ (word.drop start).take factor.length := by
    rw [hfactor]
    exact hletter
  rw [List.mem_iff_getElem] at hletter'
  obtain ⟨offset, hoffset, hat⟩ := hletter'
  refine ⟨offset, ?_, ?_⟩
  · simpa using hoffset
  · simpa using hat

/-- M1.2b.2: fixed-point tiling plus the uniform ordinary-length upper bound
puts a complete level image inside a sufficiently long avoiding interval. -/
theorem arbitrarilyLateAvoidingImages_of_intervals
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    (stable : StableMetricPowerData P) (target : α)
    (hlate : HasArbitrarilyLateAvoidingIntervals word target) :
    HasArbitrarilyLateAvoidingImages P stable target := by
  intro level cutoff
  let powered := source.power stable.power
  let iterated := powered.power level
  have hfixed : iterated.IsFixedPoint word := by
    by_cases hlevel : level = 0
    · subst level
      change (Substitution.id : Substitution α).mapInfinite word = word
      exact Substitution.mapInfinite_id word
    · exact Substitution.isFixedPoint_power stable.fixed
        (Nat.pos_of_ne_zero hlevel)
  let cellBound : ℕ := ∑ letter : α, (iterated letter).length
  have hcell_le (letter : α) : (iterated letter).length ≤ cellBound := by
    dsimp [cellBound]
    exact Finset.single_le_sum
      (f := fun other : α => (iterated other).length)
      (fun other _ => Nat.zero_le _)
      (Finset.mem_univ letter)
  have hcell_pos : 0 < cellBound := by
    have hseed : 0 < (iterated seed).length :=
      List.length_pos_of_ne_nil (iterated.image_ne_nil seed)
    exact hseed.trans_le (hcell_le seed)
  let boundary : ℕ → ℕ := higherBlockSubstitutionCut iterated word
  have hboundary := higherBlockSubstitutionCut_zero_succ iterated word
  have hboundary_zero : boundary 0 = 0 := hboundary.1
  have hboundary_succ (position : ℕ) :
      boundary (position + 1) = boundary position +
        (iterated (word position)).length := hboundary.2 position
  have hboundary_lower (position : ℕ) : position ≤ boundary position := by
    dsimp [boundary, higherBlockSubstitutionCut]
    simpa using iterated.length_le_mapWord (word.take position)
  have hboundary_strict : StrictMono boundary :=
    strictMono_nat_of_lt_succ fun position => by
      rw [hboundary_succ]
      have hpositive : 0 < (iterated (word position)).length :=
        List.length_pos_of_ne_nil (iterated.image_ne_nil (word position))
      omega
  obtain ⟨intervalStart, hintervalStart, habsent⟩ :=
    hlate (boundary cutoff) (2 * cellBound + 1)
  have hexists : ∃ position : ℕ, intervalStart ≤ boundary position :=
    ⟨intervalStart, hboundary_lower intervalStart⟩
  let position := Nat.find hexists
  have hcross : intervalStart ≤ boundary position :=
    Nat.find_spec hexists
  have hminimal : ∀ previous : ℕ, previous < position →
      boundary previous < intervalStart := by
    intro previous hprevious
    have hnot := Nat.find_min hexists (by simpa [position] using hprevious)
    omega
  have hposition : cutoff ≤ position := by
    by_contra hnot
    have hlt : position < cutoff := by omega
    have := hboundary_strict hlt
    omega
  have hover : boundary position < intervalStart + cellBound := by
    rcases Nat.eq_zero_or_pos position with hzero | hpositive
    · rw [hzero, hboundary_zero] at hcross ⊢
      omega
    · obtain ⟨previous, hpositionEq⟩ :=
        Nat.exists_eq_succ_of_ne_zero hpositive.ne'
      rw [hpositionEq, hboundary_succ]
      have hprevious := hminimal previous (by omega)
      have hlength := hcell_le (word previous)
      omega
  have hend : boundary (position + 1) <
      intervalStart + (2 * cellBound + 1) := by
    rw [hboundary_succ]
    have hlength := hcell_le (word position)
    omega
  have hfactor : InfiniteFactorAt word
      (iterated (word position)) (boundary position) := by
    have h := Substitution.mapWord_drop_take_at_fixed
      hfixed position 1
    have hone : (word.drop position).take 1 = [word position] := by
      rw [show 1 = 0 + 1 by omega, Stream'.take_succ']
      simp only [Stream'.take_zero, List.nil_append]
      change [word (0 + position)] = [word position]
      simp
    rw [hone] at h
    simpa [boundary, higherBlockSubstitutionCut] using h
  have havoids : WordAvoidsLetter target (iterated (word position)) := by
    intro htarget
    obtain ⟨offset, hoffset, hat⟩ :=
      letter_position_of_infiniteFactorAt hfactor htarget
    have hphysicalStart :
        intervalStart ≤ boundary position + offset := by omega
    have hphysicalEnd : boundary position + offset <
        intervalStart + (2 * cellBound + 1) := by
      have hcellEnd : boundary position + offset <
          boundary (position + 1) := by
        rw [hboundary_succ]
        omega
      omega
    let localOffset := boundary position + offset - intervalStart
    have hlocal : localOffset < 2 * cellBound + 1 := by
      dsimp [localOffset]
      omega
    apply habsent localOffset hlocal
    have hadd : intervalStart + localOffset =
        boundary position + offset := by
      dsimp [localOffset]
      exact Nat.add_sub_of_le hphysicalStart
    rw [hadd]
    exact hat
  refine ⟨position, hposition, ?_⟩
  simpa [iterated, powered, Substitution.power_apply] using havoids

/-- A recurrent source letter whose every positive iterate under a stable
power avoids the target letter. -/
structure PersistentAvoidingPowerData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    (stable : StableMetricPowerData P) (target : α) where
  letter : α
  recurrent : OccursInfinitelyOften word letter
  avoids : ∀ level : ℕ, 0 < level →
    WordAvoidsLetter target
      ((source.power stable.power).iterateLetter level letter)

/-- M1.2b.3: finite pigeonhole plus stabilized support turns arbitrarily
late avoiding images into one recurrent persistently avoiding letter. -/
theorem persistentAvoidingPowerData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    (stable : StableMetricPowerData P) (target : α)
    (himages : HasArbitrarilyLateAvoidingImages P stable target) :
    Nonempty (PersistentAvoidingPowerData P stable target) := by
  classical
  let powered := source.power stable.power
  let Good : α → Prop := fun letter =>
    WordAvoidsLetter target (powered letter)
  have hgoodRecurrent : ∃ letter : α,
      OccursInfinitelyOften word letter ∧ Good letter := by
    by_contra hnone
    have hnotBoth (letter : α) :
        ¬ (OccursInfinitelyOften word letter ∧ Good letter) := by
      intro hboth
      exact hnone ⟨letter, hboth⟩
    have hcutoffExists (letter : α) :
        ∃ cutoff : ℕ, Good letter →
          ∀ position : ℕ, cutoff ≤ position → word position ≠ letter := by
      by_cases hgood : Good letter
      · have hnotRecurrent : ¬ OccursInfinitelyOften word letter := by
          intro hrecurrent
          exact hnotBoth letter ⟨hrecurrent, hgood⟩
        simp only [OccursInfinitelyOften, not_forall, not_exists,
          not_and] at hnotRecurrent
        obtain ⟨cutoff, hcutoff⟩ := hnotRecurrent
        exact ⟨cutoff, fun _ => hcutoff⟩
      · exact ⟨0, fun hgood' => (hgood hgood').elim⟩
    choose cutoff hcutoff using hcutoffExists
    let bound : ℕ := ∑ letter : α, cutoff letter
    obtain ⟨position, hposition, havoids⟩ := himages 1 bound
    have hgood : Good (word position) := by
      dsimp [Good, powered]
      simpa [Substitution.iterateLetter, Substitution.iterateWord] using havoids
    have hletterCutoff : cutoff (word position) ≤ bound := by
      dsimp [bound]
      exact Finset.single_le_sum (f := cutoff)
        (fun other _ => Nat.zero_le _) (Finset.mem_univ (word position))
    exact hcutoff (word position) hgood position
      (hletterCutoff.trans hposition) rfl
  obtain ⟨letter, hrecurrent, hgood⟩ := hgoodRecurrent
  refine ⟨{
    letter := letter
    recurrent := hrecurrent
    avoids := ?_
  }⟩
  intro level hlevel htarget
  have htargetAtLevel : target ∈ Substitution.AlphabetOfWord
      (powered.iterateLetter level letter) := by
    simpa [Substitution.AlphabetOfWord] using htarget
  have htargetAtFirst : target ∈ Substitution.AlphabetOfWord
      (powered letter) := by
    rw [← stable.support_stable letter level hlevel]
    exact htargetAtLevel
  apply hgood
  simpa [Substitution.AlphabetOfWord] using htargetAtFirst

/-- The metric coordinate of the boundary preceding a source position. -/
def substitutionBoundary {α : Type u} (source : Substitution α)
    (word : InfiniteWord α) (position : ℕ) : ℕ :=
  (source.mapWord (word.take position)).length

/-- M1.2d.1: positive letter weights make prefix metric coordinate strictly
increasing. -/
theorem prefixMetricLength_strictMono
    {α : Type u} (letterLength : α → ℝ) (word : InfiniteWord α)
    (hlength : ∀ letter, 0 < letterLength letter) :
    StrictMono (prefixMetricLength letterLength word) := by
  apply strictMono_nat_of_lt_succ
  intro position
  simp only [prefixMetricLength, Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (hlength (word position))

private theorem prefixMetricLength_eq_wordMetricLength_take
    {α : Type u} (letterLength : α → ℝ) (word : InfiniteWord α) :
    ∀ position : ℕ,
      prefixMetricLength letterLength word position =
        wordMetricLength letterLength (word.take position) := by
  intro position
  induction position with
  | zero => simp [prefixMetricLength, wordMetricLength]
  | succ position ih =>
      calc
        prefixMetricLength letterLength word (position + 1) =
            prefixMetricLength letterLength word position +
              letterLength (word position) := by
          simp [prefixMetricLength, Finset.sum_range_succ]
        _ = wordMetricLength letterLength (word.take position) +
              letterLength (word position) := by rw [ih]
        _ = wordMetricLength letterLength (word.take (position + 1)) := by
          rw [Stream'.take_succ']
          have hget : Stream'.get word position = word position := rfl
          simp [wordMetricLength, hget]

/-- M1.2d.2: a substituted cut has exactly the scaled source-prefix metric
coordinate. -/
theorem prefixMetricLength_substitutionBoundary
    {α : Type u} {source : Substitution α} {word : InfiniteWord α}
    {letterLength : α → ℝ} {scale : ℝ}
    (hfixed : source.IsFixedPoint word)
    (hscales : SubstitutionScalesLetterLengths source letterLength scale)
    (position : ℕ) :
    prefixMetricLength letterLength word
        (substitutionBoundary source word position) =
      scale * prefixMetricLength letterLength word position := by
  have hprefix : word.take (substitutionBoundary source word position) =
      source.mapWord (word.take position) := by
    have h := Substitution.mapWord_drop_take_at_fixed hfixed 0 position
    simpa [InfiniteFactorAt, substitutionBoundary] using h
  rw [prefixMetricLength_eq_wordMetricLength_take, hprefix,
    wordMetricLength_mapWord_of_scales hscales,
    ← prefixMetricLength_eq_wordMetricLength_take]

/-- Containment of two scaled source cells in their common prefix-metric
coordinate. -/
def ScaledSourceCellContained (coordinate : ℕ → ℝ)
    (innerScale : ℝ) (innerPosition : ℕ)
    (outerScale : ℝ) (outerPosition : ℕ) : Prop :=
  outerScale * coordinate outerPosition ≤
      innerScale * coordinate innerPosition ∧
    innerScale * coordinate (innerPosition + 1) ≤
      outerScale * coordinate (outerPosition + 1)

private theorem substitutionBoundary_succ
    {α : Type u} (source : Substitution α) (word : InfiniteWord α)
    (position : ℕ) :
    substitutionBoundary source word (position + 1) =
      substitutionBoundary source word position +
        (source (word position)).length := by
  simpa [substitutionBoundary, higherBlockSubstitutionCut] using
    (higherBlockSubstitutionCut_zero_succ source word).2 position

private theorem substitutionImage_infiniteFactorAt
    {α : Type u} {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word) (position : ℕ) :
    InfiniteFactorAt word (source (word position))
      (substitutionBoundary source word position) := by
  have h := Substitution.mapWord_drop_take_at_fixed hfixed position 1
  have hone : (word.drop position).take 1 = [word position] := by
    rw [show 1 = 0 + 1 by omega, Stream'.take_succ']
    simp only [Stream'.take_zero, List.nil_append]
    change [word (0 + position)] = [word position]
    simp
  rw [hone] at h
  simpa [substitutionBoundary] using h

/-- M1.2d.3: exact boundary coordinates turn scaled-cell containment into
literal finite-factor containment of the corresponding image words. -/
theorem scaledSourceCellContained_gives_imageEmbedding
    {α : Type u} {inner outer : Substitution α}
    {word : InfiniteWord α} {letterLength : α → ℝ}
    {innerScale outerScale : ℝ}
    (hlength : ∀ letter, 0 < letterLength letter)
    (hinnerFixed : inner.IsFixedPoint word)
    (houterFixed : outer.IsFixedPoint word)
    (hinnerScales : SubstitutionScalesLetterLengths
      inner letterLength innerScale)
    (houterScales : SubstitutionScalesLetterLengths
      outer letterLength outerScale)
    (innerPosition outerPosition : ℕ)
    (hcontained : ScaledSourceCellContained
      (prefixMetricLength letterLength word)
      innerScale innerPosition outerScale outerPosition) :
    ∃ offset : ℕ,
      FiniteFactorAt (outer (word outerPosition))
        (inner (word innerPosition)) offset := by
  let coordinate := prefixMetricLength letterLength word
  let innerStart := substitutionBoundary inner word innerPosition
  let innerEnd := substitutionBoundary inner word (innerPosition + 1)
  let outerStart := substitutionBoundary outer word outerPosition
  let outerEnd := substitutionBoundary outer word (outerPosition + 1)
  have hstrict : StrictMono coordinate :=
    prefixMetricLength_strictMono letterLength word hlength
  have hinnerStartMetric : coordinate innerStart =
      innerScale * coordinate innerPosition := by
    exact prefixMetricLength_substitutionBoundary
      hinnerFixed hinnerScales innerPosition
  have hinnerEndMetric : coordinate innerEnd =
      innerScale * coordinate (innerPosition + 1) := by
    exact prefixMetricLength_substitutionBoundary
      hinnerFixed hinnerScales (innerPosition + 1)
  have houterStartMetric : coordinate outerStart =
      outerScale * coordinate outerPosition := by
    exact prefixMetricLength_substitutionBoundary
      houterFixed houterScales outerPosition
  have houterEndMetric : coordinate outerEnd =
      outerScale * coordinate (outerPosition + 1) := by
    exact prefixMetricLength_substitutionBoundary
      houterFixed houterScales (outerPosition + 1)
  have hstart : outerStart ≤ innerStart := by
    apply hstrict.le_iff_le.mp
    calc
      coordinate outerStart =
          outerScale * coordinate outerPosition := houterStartMetric
      _ ≤ innerScale * coordinate innerPosition := hcontained.1
      _ = coordinate innerStart := hinnerStartMetric.symm
  have hend : innerEnd ≤ outerEnd := by
    apply hstrict.le_iff_le.mp
    calc
      coordinate innerEnd =
          innerScale * coordinate (innerPosition + 1) := hinnerEndMetric
      _ ≤ outerScale * coordinate (outerPosition + 1) := hcontained.2
      _ = coordinate outerEnd := houterEndMetric.symm
  let offset := innerStart - outerStart
  have hstartEq : outerStart + offset = innerStart := by
    dsimp [offset]
    exact Nat.add_sub_of_le hstart
  have hinnerSucc : innerEnd = innerStart +
      (inner (word innerPosition)).length := by
    exact substitutionBoundary_succ inner word innerPosition
  have houterSucc : outerEnd = outerStart +
      (outer (word outerPosition)).length := by
    exact substitutionBoundary_succ outer word outerPosition
  have hwithin : offset + (inner (word innerPosition)).length ≤
      (outer (word outerPosition)).length := by
    omega
  have houterOccurrence :=
    substitutionImage_infiniteFactorAt houterFixed outerPosition
  have hinnerOccurrence :=
    substitutionImage_infiniteFactorAt hinnerFixed innerPosition
  have hinnerTranslated : InfiniteFactorAt word
      (inner (word innerPosition)) (outerStart + offset) := by
    rw [hstartEq]
    exact hinnerOccurrence
  exact ⟨offset,
    finiteFactorAt_of_nested_infiniteFactorAt
      houterOccurrence hinnerTranslated hwithin⟩

/-- Every positive open interval of ratios is hit with both exponents beyond
any prescribed cutoff. -/
def CofinalPowerRatioDense (leftBase rightBase : ℝ) : Prop :=
  ∀ lower upper : ℝ, 0 < lower → lower < upper → ∀ cutoff : ℕ,
    ∃ leftExponent rightExponent : ℕ,
      cutoff ≤ leftExponent ∧ cutoff ≤ rightExponent ∧
        lower < leftBase ^ leftExponent / rightBase ^ rightExponent ∧
        leftBase ^ leftExponent / rightBase ^ rightExponent < upper

/-- M1.2e.1a: if a positive logarithm ratio is rational, clearing its
positive numerator and denominator produces an equality of positive natural
powers.  This is the elementary arithmetic core of `e.1`. -/
theorem positive_power_equality_of_not_irrational_log_ratio
    {leftBase rightBase : ℝ}
    (hleft : 1 < leftBase) (hright : 1 < rightBase)
    (hrational : ¬ Irrational (Real.log leftBase / Real.log rightBase)) :
    ∃ leftExponent rightExponent : ℕ,
      0 < leftExponent ∧ 0 < rightExponent ∧
        leftBase ^ leftExponent = rightBase ^ rightExponent := by
  obtain ⟨ratio, hratio⟩ := exists_rat_of_not_irrational hrational
  have hlogLeft : 0 < Real.log leftBase := Real.log_pos hleft
  have hlogRight : 0 < Real.log rightBase := Real.log_pos hright
  have hratioPosReal : (0 : ℝ) < ratio := by
    rw [← hratio]
    exact div_pos hlogLeft hlogRight
  have hratioPos : (0 : ℚ) < ratio := by exact_mod_cast hratioPosReal
  have hnumPos : 0 < ratio.num := Rat.num_pos.mpr hratioPos
  have hdenPos : 0 < ratio.den := ratio.den_pos
  have hlinear :
      (ratio.den : ℝ) * Real.log leftBase =
        (ratio.num : ℝ) * Real.log rightBase := by
    have hratio' := hratio
    rw [Rat.cast_def] at hratio'
    field_simp [show (ratio.den : ℝ) ≠ 0 by positivity] at hratio'
    nlinarith
  have hnumCast : (ratio.num.natAbs : ℝ) = (ratio.num : ℝ) := by
    calc
      (ratio.num.natAbs : ℝ) =
          ((ratio.num.natAbs : ℤ) : ℝ) := by norm_num
      _ = (ratio.num : ℝ) := by
        rw [Int.natCast_natAbs, abs_of_pos hnumPos]
  refine ⟨ratio.den, ratio.num.natAbs, hdenPos,
    Int.natAbs_pos.mpr hnumPos.ne', ?_⟩
  apply Real.log_injOn_pos (pow_pos (zero_lt_one.trans hleft) _)
    (pow_pos (zero_lt_one.trans hright) _)
  rw [Real.log_pow, Real.log_pow, hnumCast]
  exact hlinear

/-- M1.2e.2a: on the unit additive circle, positive natural multiples of an
irrational real have dense range.  We expose this semigroup form separately
because Mathlib's public theorem is stated for all integer multiples. -/
theorem denseRange_positive_nsmul_addCircle_of_irrational
    {ratio : ℝ} (hirrational : Irrational ratio) :
    DenseRange (fun n : {n : ℕ // 0 < n} =>
      n.1 • (ratio : AddCircle (1 : ℝ))) := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let rotation : AddCircle (1 : ℝ) := ratio
  let positive : AddSubsemigroup (AddCircle (1 : ℝ)) :=
    { carrier := Set.range (fun n : {n : ℕ // 0 < n} => n.1 • rotation)
      add_mem' := by
        rintro _ _ ⟨left, rfl⟩ ⟨right, rfl⟩
        refine ⟨⟨left.1 + right.1, Nat.add_pos_left left.2 _⟩, ?_⟩
        exact add_nsmul rotation left.1 right.1 }
  let closedPositive := positive.topologicalClosure
  have hclosed : IsClosed (closedPositive : Set (AddCircle (1 : ℝ))) :=
    positive.isClosed_topologicalClosure
  have hnonempty : (closedPositive : Set (AddCircle (1 : ℝ))).Nonempty := by
    refine ⟨rotation, positive.le_topologicalClosure ?_⟩
    exact ⟨⟨1, by omega⟩, by simp⟩
  have hcompact : IsCompact (closedPositive : Set (AddCircle (1 : ℝ))) :=
    hclosed.isCompact
  obtain ⟨idempotent, hidempotentMem, hidempotent⟩ :=
    exists_idempotent_in_compact_add_subsemigroup
      continuous_add_const (closedPositive : Set (AddCircle (1 : ℝ)))
      hnonempty hcompact
      (fun _ hx _ hy => closedPositive.add_mem hx hy)
  have hidempotentZero : idempotent = 0 := by
    apply add_left_cancel (a := idempotent)
    simpa using hidempotent
  have hzero : (0 : AddCircle (1 : ℝ)) ∈ closedPositive := by
    simpa [hidempotentZero] using hidempotentMem
  have htranslate : Set.MapsTo (fun x => x - rotation)
      (positive : Set (AddCircle (1 : ℝ)))
      (closedPositive : Set (AddCircle (1 : ℝ))) := by
    rintro _ ⟨⟨n, hn⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    change (k + 1) • rotation - rotation ∈ closedPositive
    rw [succ_nsmul, add_sub_cancel_right]
    by_cases hk : k = 0
    · subst k
      simpa using hzero
    · apply positive.le_topologicalClosure
      exact ⟨⟨k, Nat.pos_of_ne_zero hk⟩, rfl⟩
  have hneg : -rotation ∈ closedPositive := by
    have hzeroClosure :
        (0 : AddCircle (1 : ℝ)) ∈ closure (positive : Set (AddCircle (1 : ℝ))) :=
      hzero
    have hmapped :=
      (htranslate.closure_left (continuous_id.sub continuous_const) hclosed)
        hzeroClosure
    simpa using hmapped
  have hnegMultiples : ∀ n : ℕ, 0 < n → n • (-rotation) ∈ closedPositive := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro _
        by_cases hn : n = 0
        · subst n
          simpa using hneg
        · rw [succ_nsmul]
          exact closedPositive.add_mem (ih (Nat.pos_of_ne_zero hn)) hneg
  have hzsmul : ∀ z : ℤ, z • rotation ∈ closedPositive := by
    intro z
    cases z with
    | ofNat n =>
        cases n with
        | zero => simpa using hzero
        | succ n =>
            have hmem : (n + 1) • rotation ∈ closedPositive := by
              apply positive.le_topologicalClosure
              exact ⟨⟨n + 1, by omega⟩, rfl⟩
            simpa using hmem
    | negSucc n =>
        have hmem := hnegMultiples (n + 1) (by omega)
        have heq : (Int.negSucc n) • rotation = (n + 1) • (-rotation) := by
          have hscalar : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
          rw [hscalar, neg_zsmul, natCast_zsmul, neg_nsmul]
        rwa [heq]
  have hzDense : DenseRange (fun z : ℤ => z • rotation) := by
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa [rotation] using hirrational
  have hclosedDense : Dense (closedPositive : Set (AddCircle (1 : ℝ))) :=
    Dense.mono (by rintro _ ⟨z, rfl⟩; exact hzsmul z) hzDense
  have hclosedEqUniv :
      (closedPositive : Set (AddCircle (1 : ℝ))) = Set.univ := by
    have := hclosedDense.closure_eq
    rwa [hclosed.closure_eq] at this
  change Dense (positive : Set (AddCircle (1 : ℝ)))
  exact dense_iff_closure_eq.mpr hclosedEqUniv

/-- M1.2e.2b: deleting any finite initial segment from the positive orbit of
an irrational circle rotation preserves density. -/
theorem denseRange_cofinal_nsmul_addCircle_of_irrational
    {ratio : ℝ} (hirrational : Irrational ratio) (cutoff : ℕ) :
    DenseRange (fun n : ℕ =>
      (cutoff + n + 1) • (ratio : AddCircle (1 : ℝ))) := by
  let rotation : AddCircle (1 : ℝ) := ratio
  have hpositive :=
    denseRange_positive_nsmul_addCircle_of_irrational hirrational
  have hsuccRange :
      Set.range (fun n : ℕ => (n + 1) • rotation) =
        Set.range (fun n : {n : ℕ // 0 < n} => n.1 • rotation) := by
    ext point
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨⟨n + 1, by omega⟩, rfl⟩
    · rintro ⟨⟨n, hn⟩, rfl⟩
      refine ⟨n - 1, ?_⟩
      change (n - 1 + 1) • rotation = n • rotation
      rw [Nat.sub_add_cancel hn]
  have hsucc : DenseRange (fun n : ℕ => (n + 1) • rotation) := by
    rw [DenseRange, hsuccRange]
    exact hpositive
  let translate : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) :=
    fun point => cutoff • rotation + point
  have htranslateSurjective : Function.Surjective translate := by
    intro point
    refine ⟨point - cutoff • rotation, ?_⟩
    dsimp [translate]
    abel
  have htranslated : DenseRange
      (translate ∘ fun n : ℕ => (n + 1) • rotation) :=
    (Function.Surjective.denseRange htranslateSurjective).comp hsucc
      (by simpa [translate] using
        (continuous_const_add (cutoff • rotation)))
  convert htranslated using 1
  funext n
  dsimp [translate]
  simpa only [Nat.add_assoc] using add_nsmul rotation cutoff (n + 1)

/-- M1.2e.2c: lift cofinally dense positive circle multiples to real
approximations `n * ratio - m`, with both natural coefficients beyond a
prescribed cutoff.  Positivity of `ratio` is exactly what forces the lifted
integer coefficient to be eventually positive. -/
theorem cofinal_nat_sub_approximation_of_irrational
    {ratio : ℝ} (hratio : 0 < ratio) (hirrational : Irrational ratio) :
    ∀ lower upper : ℝ, lower < upper → ∀ cutoff : ℕ,
      ∃ leftCoefficient rightCoefficient : ℕ,
        cutoff ≤ leftCoefficient ∧ cutoff ≤ rightCoefficient ∧
          lower < (leftCoefficient : ℝ) * ratio - rightCoefficient ∧
          (leftCoefficient : ℝ) * ratio - rightCoefficient < upper := by
  intro lower upper hlowerUpper cutoff
  obtain ⟨growthCutoff, hgrowthCutoff⟩ :=
    exists_nat_gt ((upper + cutoff) / ratio)
  let tailCutoff := max cutoff growthCutoff
  have hdense := denseRange_cofinal_nsmul_addCircle_of_irrational
    hirrational tailCutoff
  let arc : Set (AddCircle (1 : ℝ)) :=
    ((↑) : ℝ → AddCircle (1 : ℝ)) '' Set.Ioo lower upper
  have harcOpen : IsOpen arc := by
    exact QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have harcNonempty : arc.Nonempty := by
    let midpoint := (lower + upper) / 2
    refine ⟨(midpoint : AddCircle (1 : ℝ)), midpoint, ?_, rfl⟩
    dsimp [midpoint]
    constructor <;> linarith
  obtain ⟨index, hindex⟩ := hdense.exists_mem_open harcOpen harcNonempty
  obtain ⟨representative, hrepresentative, hcircle⟩ := hindex
  let leftCoefficient := tailCutoff + index + 1
  have hcircleZero :
      ((leftCoefficient • ratio - representative : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_nsmul]
    change leftCoefficient • (ratio : AddCircle (1 : ℝ)) -
      (representative : AddCircle (1 : ℝ)) = 0
    rw [← hcircle, sub_self]
  obtain ⟨rightInteger, hrightInteger⟩ :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcircleZero
  have hrightIntegerReal :
      (rightInteger : ℝ) =
        (leftCoefficient : ℝ) * ratio - representative := by
    simpa [zsmul_eq_mul, nsmul_eq_mul] using hrightInteger
  have hgrowthScaled :
      upper + (cutoff : ℝ) < (growthCutoff : ℝ) * ratio := by
    exact (div_lt_iff₀ hratio).mp hgrowthCutoff
  have hgrowthLeLeft : growthCutoff ≤ leftCoefficient := by
    dsimp [leftCoefficient, tailCutoff]
    omega
  have hgrowthScaledLe :
      (growthCutoff : ℝ) * ratio ≤ (leftCoefficient : ℝ) * ratio := by
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hgrowthLeLeft) hratio.le
  have hcutoffRightReal : (cutoff : ℝ) < (rightInteger : ℝ) := by
    rw [hrightIntegerReal]
    nlinarith [hrepresentative.2]
  have hcutoffRightInt : (cutoff : ℤ) < rightInteger := by
    exact_mod_cast hcutoffRightReal
  have hrightNonneg : 0 ≤ rightInteger :=
    (Int.natCast_nonneg cutoff).trans hcutoffRightInt.le
  have hrightNatCast : (rightInteger.toNat : ℤ) = rightInteger :=
    Int.toNat_of_nonneg hrightNonneg
  have hrightCoefficient : cutoff ≤ rightInteger.toNat := by
    have : (cutoff : ℤ) ≤ (rightInteger.toNat : ℤ) := by
      rw [hrightNatCast]
      exact hcutoffRightInt.le
    exact_mod_cast this
  have hrightCast : (rightInteger.toNat : ℝ) = (rightInteger : ℝ) := by
    calc
      (rightInteger.toNat : ℝ) = ((rightInteger.toNat : ℤ) : ℝ) :=
        (Int.cast_natCast _).symm
      _ = (rightInteger : ℝ) :=
        congrArg (fun value : ℤ => (value : ℝ)) hrightNatCast
  have hcoordinate :
      (leftCoefficient : ℝ) * ratio - rightInteger.toNat = representative := by
    rw [hrightCast, hrightIntegerReal]
    ring
  refine ⟨leftCoefficient, rightInteger.toNat, ?_, hrightCoefficient, ?_, ?_⟩
  · dsimp [leftCoefficient, tailCutoff]
    omega
  · rw [hcoordinate]
    exact hrepresentative.1
  · rw [hcoordinate]
    exact hrepresentative.2

/-- M1.2e.1: multiplicative independence above one makes the logarithm
ratio irrational. -/
theorem irrational_log_ratio_of_multiplicativelyIndependent
    {leftBase rightBase : ℝ}
    (hleft : 1 < leftBase) (hright : 1 < rightBase)
    (hindependent : MultiplicativelyIndependent leftBase rightBase) :
    Irrational (Real.log leftBase / Real.log rightBase) := by
  by_contra hrational
  obtain ⟨leftExponent, rightExponent, hleftExponent,
      hrightExponent, hequal⟩ :=
    positive_power_equality_of_not_irrational_log_ratio
      hleft hright hrational
  exact hindependent leftExponent rightExponent
    hleftExponent hrightExponent hequal

/-- M1.2e.2: irrational logarithmic ratio gives cofinal density of positive
power ratios (the Kronecker/density input in Durand--Rigo, Theorem 18). -/
theorem cofinalPowerRatioDense_of_irrational_log_ratio
    {leftBase rightBase : ℝ}
    (hleft : 1 < leftBase) (hright : 1 < rightBase)
    (hirrational : Irrational (Real.log leftBase / Real.log rightBase)) :
    CofinalPowerRatioDense leftBase rightBase := by
  intro lower upper hlower hlowerUpper cutoff
  have hleftPos : 0 < leftBase := zero_lt_one.trans hleft
  have hrightPos : 0 < rightBase := zero_lt_one.trans hright
  have hlogRight : 0 < Real.log rightBase := Real.log_pos hright
  have hratioPos : 0 < Real.log leftBase / Real.log rightBase :=
    div_pos (Real.log_pos hleft) hlogRight
  obtain ⟨leftExponent, rightExponent, hleftExponent,
      hrightExponent, hlowerLog, hupperLog⟩ :=
    cofinal_nat_sub_approximation_of_irrational hratioPos hirrational
      (Real.log lower / Real.log rightBase)
      (Real.log upper / Real.log rightBase)
      (div_lt_div_iff_of_pos_right hlogRight |>.2
        (Real.strictMonoOn_log hlower (hlower.trans hlowerUpper) hlowerUpper))
      cutoff
  refine ⟨leftExponent, rightExponent, hleftExponent,
    hrightExponent, ?_, ?_⟩
  · rw [← Real.exp_log hlower]
    have hratioExp :
        Real.exp ((leftExponent : ℝ) * Real.log leftBase -
          (rightExponent : ℝ) * Real.log rightBase) =
          leftBase ^ leftExponent / rightBase ^ rightExponent := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log hleftPos, Real.exp_log hrightPos]
    rw [← hratioExp]
    apply Real.exp_lt_exp.mpr
    have hnormalize :
        ((leftExponent : ℝ) *
            (Real.log leftBase / Real.log rightBase) - rightExponent) *
            Real.log rightBase =
          (leftExponent : ℝ) * Real.log leftBase -
            (rightExponent : ℝ) * Real.log rightBase := by
      field_simp [hlogRight.ne']
    exact hnormalize ▸ (div_lt_iff₀ hlogRight).mp hlowerLog
  · rw [← Real.exp_log (hlower.trans hlowerUpper)]
    have hratioExp :
        Real.exp ((leftExponent : ℝ) * Real.log leftBase -
          (rightExponent : ℝ) * Real.log rightBase) =
          leftBase ^ leftExponent / rightBase ^ rightExponent := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log hleftPos, Real.exp_log hrightPos]
    rw [← hratioExp]
    apply Real.exp_lt_exp.mpr
    have hnormalize :
        ((leftExponent : ℝ) *
            (Real.log leftBase / Real.log rightBase) - rightExponent) *
            Real.log rightBase =
          (leftExponent : ℝ) * Real.log leftBase -
            (rightExponent : ℝ) * Real.log rightBase := by
      field_simp [hlogRight.ne']
    exact hnormalize ▸ (lt_div_iff₀ hlogRight).mp hupperLog

/-- Positive powers of independent bases remain independent. -/
theorem multiplicativelyIndependent_pow
    {leftBase rightBase : ℝ}
    (hindependent : MultiplicativelyIndependent leftBase rightBase)
    {leftPower rightPower : ℕ}
    (hleftPower : 0 < leftPower) (hrightPower : 0 < rightPower) :
    MultiplicativelyIndependent (leftBase ^ leftPower)
      (rightBase ^ rightPower) := by
  intro leftExponent rightExponent hleftExponent hrightExponent hequal
  apply hindependent (leftPower * leftExponent) (rightPower * rightExponent)
    (Nat.mul_pos hleftPower hleftExponent)
    (Nat.mul_pos hrightPower hrightExponent)
  simpa [pow_mul] using hequal

/-- M1.2e aggregator: cofinal ratio density for the two stabilized powers. -/
theorem stablePowerRatioDensity
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    (Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength)
    (Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength)
    (stableσ : StableMetricPowerData Pσ)
    (stableτ : StableMetricPowerData Pτ)
    (hindependent : MultiplicativelyIndependent eigenvalueσ eigenvalueτ) :
    CofinalPowerRatioDense (eigenvalueσ ^ stableσ.power)
      (eigenvalueτ ^ stableτ.power) := by
  have hindependentPower := multiplicativelyIndependent_pow hindependent
    stableσ.power_pos stableτ.power_pos
  exact cofinalPowerRatioDense_of_irrational_log_ratio
    stableσ.one_lt_scale stableτ.one_lt_scale
    (irrational_log_ratio_of_multiplicativelyIndependent
      stableσ.one_lt_scale stableτ.one_lt_scale hindependentPower)

/-- A nonempty positive open interval. -/
structure PositiveScaleWindow where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_lt_upper : lower < upper

def PositiveScaleWindow.Contains (window : PositiveScaleWindow)
    (ratio : ℝ) : Prop :=
  window.lower < ratio ∧ ratio < window.upper

/-- For the fixed tiling by one stabilized substitution, every physical
position has a source cell.  The parent assignment is cofinal: positions
escaping to the right cannot remain in finitely many nonempty source cells. -/
structure PoweredFixedTilingParentData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    (stable : StableMetricPowerData P) where
  parentPosition : ℕ → ℕ
  offset : ℕ → ℕ
  parent_le_position : ∀ position, parentPosition position ≤ position
  offset_lt_image : ∀ position,
    offset position <
      ((source.power stable.power) (word (parentPosition position))).length
  position_eq_boundary_add_offset : ∀ position,
    position = substitutionBoundary (source.power stable.power) word
      (parentPosition position) + offset position
  parent_unique : ∀ position candidate,
    substitutionBoundary (source.power stable.power) word candidate ≤ position →
    position < substitutionBoundary (source.power stable.power) word
      (candidate + 1) →
    candidate = parentPosition position
  parent_cofinal : ∀ parentCutoff : ℕ, ∃ positionCutoff : ℕ,
    ∀ position : ℕ, positionCutoff ≤ position →
      parentCutoff ≤ parentPosition position
  position_in_parent_image : ∀ position,
    word position ∈
      (source.power stable.power) (word (parentPosition position))

/-- M1.2f-new.1a: strict substitution boundaries of the nonempty powered
images give the cofinal parent-cell assignment. -/
theorem poweredFixedTilingParentData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    (stable : StableMetricPowerData P) :
    Nonempty (PoweredFixedTilingParentData stable) := by
  classical
  let powered : Substitution α := source.power stable.power
  let boundary : ℕ → ℕ := substitutionBoundary powered word
  have boundary_zero : boundary 0 = 0 := by
    simp [boundary, substitutionBoundary]
  have boundary_succ (position : ℕ) :
      boundary (position + 1) = boundary position +
        (powered (word position)).length := by
    simpa only [boundary] using substitutionBoundary_succ powered word position
  have boundary_lower (position : ℕ) : position ≤ boundary position := by
    dsimp [boundary, substitutionBoundary]
    simpa using powered.length_le_mapWord (word.take position)
  have boundary_strict : StrictMono boundary :=
    strictMono_nat_of_lt_succ fun position => by
      rw [boundary_succ]
      exact Nat.lt_add_of_pos_right
        (List.length_pos_of_ne_nil (powered.image_ne_nil (word position)))
  have cell_exists (position : ℕ) :
      ∃ candidate : ℕ, position < boundary (candidate + 1) := by
    refine ⟨position, ?_⟩
    exact (Nat.lt_succ_self position).trans_le (boundary_lower (position + 1))
  let parentPosition : ℕ → ℕ := fun position => Nat.find (cell_exists position)
  let offset : ℕ → ℕ := fun position =>
    position - boundary (parentPosition position)
  have parent_upper (position : ℕ) :
      position < boundary (parentPosition position + 1) := by
    exact Nat.find_spec (cell_exists position)
  have parent_lower (position : ℕ) :
      boundary (parentPosition position) ≤ position := by
    by_cases hzero : parentPosition position = 0
    · rw [hzero, boundary_zero]
      exact Nat.zero_le position
    · obtain ⟨previous, hparent⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hminimal := Nat.find_min (cell_exists position)
        (show previous < parentPosition position by omega)
      change ¬ position < boundary (previous + 1) at hminimal
      rw [hparent]
      exact Nat.le_of_not_gt hminimal
  have position_eq (position : ℕ) :
      position = boundary (parentPosition position) + offset position := by
    dsimp only [offset]
    exact (Nat.add_sub_of_le (parent_lower position)).symm
  have offset_image_lt (position : ℕ) :
      offset position <
        (powered (word (parentPosition position))).length := by
    have hupper := parent_upper position
    have hsucc := boundary_succ (parentPosition position)
    have heq := position_eq position
    omega
  refine ⟨{
    parentPosition := parentPosition
    offset := offset
    parent_le_position := ?_
    offset_lt_image := ?_
    position_eq_boundary_add_offset := ?_
    parent_unique := ?_
    parent_cofinal := ?_
    position_in_parent_image := ?_
  }⟩
  · intro position
    exact (boundary_lower (parentPosition position)).trans
      (parent_lower position)
  · intro position
    exact offset_image_lt position
  · intro position
    simpa only [boundary, powered] using position_eq position
  · intro position candidate hcandidateLower hcandidateUpper
    have hchosenLower := parent_lower position
    have hchosenUpper := parent_upper position
    change boundary candidate ≤ position at hcandidateLower
    change position < boundary (candidate + 1) at hcandidateUpper
    rcases lt_trichotomy candidate (parentPosition position) with
        hleft | heq | hright
    · have hbound : boundary (candidate + 1) ≤
          boundary (parentPosition position) :=
        boundary_strict.monotone (by omega)
      omega
    · exact heq
    · have hbound : boundary (parentPosition position + 1) ≤
          boundary candidate :=
        boundary_strict.monotone (by omega)
      omega
  · intro parentCutoff
    refine ⟨boundary parentCutoff, ?_⟩
    intro position hposition
    by_contra hnot
    have hparentLt : parentPosition position < parentCutoff := by omega
    have hbound : boundary (parentPosition position + 1) ≤
        boundary parentCutoff :=
      boundary_strict.monotone (by omega)
    exact (Nat.not_lt_of_ge (hbound.trans hposition)) (parent_upper position)
  · intro position
    have himage : InfiniteFactorAt word
        (powered (word (parentPosition position)))
        (boundary (parentPosition position)) := by
      simpa only [powered, boundary] using
        (substitutionImage_infiniteFactorAt stable.fixed
          (parentPosition position))
    let taken : Word α :=
      (word.drop (boundary (parentPosition position))).take
        (powered (word (parentPosition position))).length
    have hoffset := offset_image_lt position
    have htake : offset position < taken.length := by
      simpa only [taken, Stream'.length_take] using hoffset
    have hget : taken[offset position]'htake = word position := by
      calc
        _ = word (boundary (parentPosition position) + offset position) := by
          simp [taken]
          rfl
        _ = word position := congrArg word (position_eq position).symm
    have hmem : word position ∈ taken := by
      rw [List.mem_iff_getElem]
      exact ⟨offset position, htake, hget⟩
    change word position ∈ powered (word (parentPosition position))
    rw [← himage]
    simpa only [taken] using hmem

/-- One letter occurs at cofinally many parent positions of occurrences of the
target, and its first stabilized image contains the target. -/
structure RecurringTargetParentData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    {stable : StableMetricPowerData P} (target : α) where
  letter : α
  position : ℕ → ℕ
  position_strictMono : StrictMono position
  letter_at : ∀ index, word (position index) = letter
  target_mem_first_image :
    target ∈ (source.power stable.power) letter

/-- M1.2f-new.1b: desubstitute arbitrarily late target occurrences through
the fixed powered tiling and apply finite pigeonhole to their parent letters. -/
theorem recurringTargetParentData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    {stable : StableMetricPowerData P} (target : α)
    (tiling : PoweredFixedTilingParentData stable)
    (hrecurrent : OccursInfinitelyOften word target) :
    Nonempty (RecurringTargetParentData (stable := stable) target) := by
  classical
  let powered : Substitution α := source.power stable.power
  have hcofinal : ∃ letter : α, ∀ cutoff : ℕ, ∃ position : ℕ,
      cutoff ≤ position ∧ word position = letter ∧
        target ∈ powered letter := by
    by_contra hnone
    have hcutoffExists (letter : α) :
        ∃ cutoff : ℕ, ∀ position : ℕ, cutoff ≤ position →
          word position = letter → target ∉ powered letter := by
      have hnotCofinal : ¬ ∀ cutoff : ℕ, ∃ position : ℕ,
          cutoff ≤ position ∧ word position = letter ∧
            target ∈ powered letter := by
        intro hletter
        exact hnone ⟨letter, hletter⟩
      simpa only [not_forall, not_exists, not_and] using hnotCofinal
    choose cutoff hcutoff using hcutoffExists
    let parentBound : ℕ := ∑ letter : α, cutoff letter
    obtain ⟨physicalCutoff, hparentLate⟩ :=
      tiling.parent_cofinal parentBound
    obtain ⟨targetPosition, htargetLate, htargetAt⟩ :=
      hrecurrent physicalCutoff
    let parentPosition := tiling.parentPosition targetPosition
    have hletterCutoff : cutoff (word parentPosition) ≤ parentBound := by
      dsimp [parentBound]
      exact Finset.single_le_sum (f := cutoff)
        (fun other _ => Nat.zero_le _) (Finset.mem_univ (word parentPosition))
    have hparentBound : parentBound ≤ parentPosition := by
      exact hparentLate targetPosition htargetLate
    have hnotmem : target ∉ powered (word parentPosition) :=
      hcutoff (word parentPosition) parentPosition
        (hletterCutoff.trans hparentBound) rfl
    apply hnotmem
    have hmem := tiling.position_in_parent_image targetPosition
    change word targetPosition ∈ powered (word parentPosition) at hmem
    simpa only [htargetAt] using hmem
  obtain ⟨letter, hletter⟩ := hcofinal
  let next : ℕ → ℕ := fun cutoff => (hletter cutoff).choose
  have next_spec (cutoff : ℕ) :
      cutoff ≤ next cutoff ∧ word (next cutoff) = letter ∧
        target ∈ powered letter :=
    (hletter cutoff).choose_spec
  let position : ℕ → ℕ := fun index =>
    Nat.rec (next 0) (fun _ previous => next (previous + 1)) index
  have position_zero : position 0 = next 0 := rfl
  have position_succ (index : ℕ) :
      position (index + 1) = next (position index + 1) := by
    rfl
  have position_letter : ∀ index, word (position index) = letter := by
    intro index
    cases index with
    | zero => simpa only [position_zero] using (next_spec 0).2.1
    | succ index =>
        rw [position_succ]
        exact (next_spec (position index + 1)).2.1
  have position_strictMono : StrictMono position :=
    strictMono_nat_of_lt_succ fun index => by
      rw [position_succ]
      exact (Nat.lt_succ_self (position index)).trans_le
        (next_spec (position index + 1)).1
  refine ⟨{
    letter := letter
    position := position
    position_strictMono := position_strictMono
    letter_at := position_letter
    target_mem_first_image := ?_
  }⟩
  simpa only [powered] using (next_spec 0).2.2

/-- M1.2f-new.1c: stabilized support propagates the target occurrence in the
parent's first image to every positive powered image. -/
theorem target_mem_poweredParentImage
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    {stable : StableMetricPowerData P} {target : α}
    (parent : RecurringTargetParentData (stable := stable) target)
    (level : ℕ) (hlevel : 0 < level) :
    target ∈
      ((source.power stable.power).iterateLetter level parent.letter) := by
  have htargetFirst : target ∈ Substitution.AlphabetOfWord
      ((source.power stable.power) parent.letter) := by
    simpa only [Substitution.mem_alphabetOfWord_iff,
      Substitution.OccursInWord] using parent.target_mem_first_image
  have htargetLevel : target ∈ Substitution.AlphabetOfWord
      ((source.power stable.power).iterateLetter level parent.letter) := by
    rw [stable.support_stable parent.letter level hlevel]
    exact htargetFirst
  simpa only [Substitution.mem_alphabetOfWord_iff,
    Substitution.OccursInWord] using htargetLevel

/-- A positive occurrence of the persistent avoiding letter, together with
its exact source-cell metric endpoints and target-free powered images. -/
structure ExactSafeTowerCellData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    {stable : StableMetricPowerData P} {target : α}
    (avoiding : PersistentAvoidingPowerData P stable target) where
  sourcePosition : ℕ
  sourcePosition_pos : 0 < sourcePosition
  letter_at : word sourcePosition = avoiding.letter
  leftEndpoint : ℝ
  rightEndpoint : ℝ
  leftEndpoint_eq : leftEndpoint =
    prefixMetricLength letterLength word sourcePosition
  rightEndpoint_eq : rightEndpoint =
    prefixMetricLength letterLength word (sourcePosition + 1)
  leftEndpoint_pos : 0 < leftEndpoint
  left_lt_right : leftEndpoint < rightEndpoint
  powered_image_avoids : ∀ level : ℕ, 0 < level →
    WordAvoidsLetter target
      ((source.power stable.power).iterateLetter level avoiding.letter)

/-- M1.2f-new.2a: recurrence supplies a positive source occurrence; positive
letter weights identify its strictly positive, nondegenerate metric cell. -/
theorem exactSafeTowerCellData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    {stable : StableMetricPowerData P} {target : α}
    (avoiding : PersistentAvoidingPowerData P stable target) :
    Nonempty (ExactSafeTowerCellData avoiding) := by
  obtain ⟨sourcePosition, hsourcePosition, hletter⟩ := avoiding.recurrent 1
  let coordinate := prefixMetricLength letterLength word
  have hstrict : StrictMono coordinate :=
    prefixMetricLength_strictMono letterLength word P.letterLength_pos
  have hzero : coordinate 0 = 0 := by
    simp [coordinate, prefixMetricLength]
  have hleft_pos : 0 < coordinate sourcePosition := by
    rw [← hzero]
    exact hstrict hsourcePosition
  refine ⟨{
    sourcePosition := sourcePosition
    sourcePosition_pos := hsourcePosition
    letter_at := hletter
    leftEndpoint := coordinate sourcePosition
    rightEndpoint := coordinate (sourcePosition + 1)
    leftEndpoint_eq := rfl
    rightEndpoint_eq := rfl
    leftEndpoint_pos := hleft_pos
    left_lt_right := hstrict (Nat.lt_succ_self sourcePosition)
    powered_image_avoids := avoiding.avoids
  }⟩

/-- Metric coordinates of the recurrent target-parent occurrences escape every
bounded interval. -/
structure RecurrentTargetParentCoordinateData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    {stable : StableMetricPowerData P} {target : α}
    (parent : RecurringTargetParentData (stable := stable) target) where
  coordinate_unbounded : ∀ bound : ℝ, ∃ index : ℕ,
    bound < prefixMetricLength letterLength word (parent.position index)

/-- M1.2f-new.2b: strict growth of recurrent parent positions and the positive
finite alphabet metric give unbounded prefix coordinates. -/
theorem recurrentTargetParentCoordinateData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength}
    {stable : StableMetricPowerData P} {target : α}
    (parent : RecurringTargetParentData (stable := stable) target) :
    Nonempty (RecurrentTargetParentCoordinateData parent) := by
  classical
  letI : Nonempty α := ⟨seed⟩
  obtain ⟨shortest, _hshortest_mem, hshortest⟩ :=
    Finset.exists_min_image Finset.univ letterLength Finset.univ_nonempty
  let minimum : ℝ := letterLength shortest
  have hminimum_pos : 0 < minimum := P.letterLength_pos shortest
  have hminimum_le (letter : α) : minimum ≤ letterLength letter :=
    hshortest letter (Finset.mem_univ letter)
  have hprefix_lower (position : ℕ) :
      minimum * position ≤ prefixMetricLength letterLength word position := by
    rw [show minimum * (position : ℝ) =
        ∑ _index ∈ Finset.range position, minimum by simp [mul_comm]]
    exact Finset.sum_le_sum fun index _hindex => by
      simpa only using hminimum_le (word index)
  refine ⟨{ coordinate_unbounded := ?_ }⟩
  intro bound
  obtain ⟨index, hindex⟩ := exists_nat_gt (bound / minimum)
  have hbound_index : bound < minimum * index := by
    have hmul := mul_lt_mul_of_pos_left hindex hminimum_pos
    rw [mul_div_cancel₀ bound hminimum_pos.ne'] at hmul
    simpa only [mul_comm] using hmul
  have hindex_position : index ≤ parent.position index :=
    parent.position_strictMono.id_le index
  have hminimum_index_le : minimum * index ≤
      minimum * parent.position index :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hindex_position)
      hminimum_pos.le
  exact ⟨index, hbound_index.trans_le
    (hminimum_index_le.trans (hprefix_lower (parent.position index)))⟩

/-- Choose the recurrent target-parent cell late enough that its relative
width is smaller than that of the fixed positive safe source cell. -/
structure LateSafeTargetCellPairData
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    (safe : ExactSafeTowerCellData avoiding)
    (parent : RecurringTargetParentData (stable := stableτ) target) where
  parentIndex : ℕ
  separation :
    safe.leftEndpoint * letterLength parent.letter <
      prefixMetricLength letterLength word (parent.position parentIndex) *
        letterLength avoiding.letter

/-- M1.2f-new.2c: use the unbounded parent coordinate to obtain the strict
cross-multiplied inequality making the containment window nonempty. -/
theorem lateSafeTargetCellPairData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    (safe : ExactSafeTowerCellData avoiding)
    (parent : RecurringTargetParentData (stable := stableτ) target)
    (unbounded : RecurrentTargetParentCoordinateData parent) :
    Nonempty (LateSafeTargetCellPairData safe parent) := by
  let avoidingLength := letterLength avoiding.letter
  let parentLength := letterLength parent.letter
  have havoidingLength : 0 < avoidingLength :=
    Pσ.letterLength_pos avoiding.letter
  obtain ⟨parentIndex, hlarge⟩ := unbounded.coordinate_unbounded
    (safe.leftEndpoint * parentLength / avoidingLength)
  refine ⟨{ parentIndex := parentIndex, separation := ?_ }⟩
  have hscaled := mul_lt_mul_of_pos_right hlarge havoidingLength
  rw [div_mul_cancel₀ _ havoidingLength.ne'] at hscaled
  simpa only [avoidingLength, parentLength] using hscaled

/-- The positive open interval of ratios for which the target-parent source
cell is strictly contained in the safe source cell. -/
structure SafeTargetCellScaleWindowData
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    {safe : ExactSafeTowerCellData avoiding}
    {parent : RecurringTargetParentData (stable := stableτ) target}
    (pair : LateSafeTargetCellPairData safe parent) where
  window : PositiveScaleWindow
  lower_eq : window.lower =
    prefixMetricLength letterLength word
        (parent.position pair.parentIndex + 1) /
      safe.rightEndpoint
  upper_eq : window.upper =
    prefixMetricLength letterLength word
        (parent.position pair.parentIndex) /
      safe.leftEndpoint
  normalized_containment : ∀ ratio, window.Contains ratio →
    ScaledSourceCellContained (prefixMetricLength letterLength word)
      1 (parent.position pair.parentIndex) ratio safe.sourcePosition

/-- M1.2f-new.3a: exact successor-coordinate formulas and the strict width
comparison construct the nonempty ratio window. -/
theorem safeTargetCellScaleWindowData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    {safe : ExactSafeTowerCellData avoiding}
    {parent : RecurringTargetParentData (stable := stableτ) target}
    (pair : LateSafeTargetCellPairData safe parent) :
    Nonempty (SafeTargetCellScaleWindowData pair) := by
  let coordinate := prefixMetricLength letterLength word
  let parentPosition := parent.position pair.parentIndex
  have hstrict : StrictMono coordinate :=
    prefixMetricLength_strictMono letterLength word Pσ.letterLength_pos
  have hcoordinate_zero : coordinate 0 = 0 := by
    simp [coordinate, prefixMetricLength]
  have hcoordinate_succ (position : ℕ) :
      coordinate (position + 1) = coordinate position +
        letterLength (word position) := by
    simp [coordinate, prefixMetricLength, Finset.sum_range_succ]
  have hparent_succ : coordinate (parentPosition + 1) =
      coordinate parentPosition + letterLength parent.letter := by
    rw [hcoordinate_succ]
    exact congrArg (fun letter =>
      coordinate parentPosition + letterLength letter)
      (parent.letter_at pair.parentIndex)
  have hsafe_left_eq : safe.leftEndpoint =
      coordinate safe.sourcePosition := by
    simpa only [coordinate] using safe.leftEndpoint_eq
  have hsafe_right_eq : safe.rightEndpoint =
      coordinate (safe.sourcePosition + 1) := by
    simpa only [coordinate] using safe.rightEndpoint_eq
  have hsafe_right_add : safe.rightEndpoint = safe.leftEndpoint +
      letterLength avoiding.letter := by
    calc
      safe.rightEndpoint = coordinate (safe.sourcePosition + 1) :=
        hsafe_right_eq
      _ = coordinate safe.sourcePosition +
          letterLength (word safe.sourcePosition) :=
        hcoordinate_succ safe.sourcePosition
      _ = safe.leftEndpoint + letterLength avoiding.letter := by
        rw [← hsafe_left_eq, safe.letter_at]
  have hsafe_right_pos : 0 < safe.rightEndpoint :=
    safe.leftEndpoint_pos.trans safe.left_lt_right
  have hparent_succ_pos : 0 < coordinate (parentPosition + 1) := by
    rw [← hcoordinate_zero]
    exact hstrict (Nat.succ_pos parentPosition)
  have hseparation : safe.leftEndpoint * letterLength parent.letter <
      coordinate parentPosition * letterLength avoiding.letter := by
    simpa only [coordinate, parentPosition] using pair.separation
  have hlower_lt_upper :
      coordinate (parentPosition + 1) / safe.rightEndpoint <
        coordinate parentPosition / safe.leftEndpoint := by
    apply (div_lt_div_iff₀ hsafe_right_pos safe.leftEndpoint_pos).2
    rw [hparent_succ, hsafe_right_add]
    nlinarith
  let window : PositiveScaleWindow := {
    lower := coordinate (parentPosition + 1) / safe.rightEndpoint
    upper := coordinate parentPosition / safe.leftEndpoint
    lower_pos := div_pos hparent_succ_pos hsafe_right_pos
    lower_lt_upper := hlower_lt_upper
  }
  refine ⟨{
    window := window
    lower_eq := rfl
    upper_eq := rfl
    normalized_containment := ?_
  }⟩
  intro ratio hratio
  have hlower : coordinate (parentPosition + 1) /
      safe.rightEndpoint < ratio := by
    exact hratio.1
  have hupper : ratio < coordinate parentPosition /
      safe.leftEndpoint := by
    exact hratio.2
  have hleft : ratio * safe.leftEndpoint < coordinate parentPosition :=
    (lt_div_iff₀ safe.leftEndpoint_pos).mp hupper
  have hright : coordinate (parentPosition + 1) <
      ratio * safe.rightEndpoint :=
    (div_lt_iff₀ hsafe_right_pos).mp hlower
  change ratio * coordinate safe.sourcePosition ≤
      1 * coordinate parentPosition ∧
    1 * coordinate (parentPosition + 1) ≤
      ratio * coordinate (safe.sourcePosition + 1)
  rw [← hsafe_left_eq, ← hsafe_right_eq]
  exact ⟨by simpa only [one_mul] using hleft.le,
    by simpa only [one_mul] using hright.le⟩

/-- A cofinal density hit in the safe/target-parent containment window. -/
structure CofinalScaleWindowHitData
    (leftBase rightBase : ℝ) (window : PositiveScaleWindow) where
  leftLevel : ℕ
  rightLevel : ℕ
  leftLevel_pos : 0 < leftLevel
  rightLevel_pos : 0 < rightLevel
  ratio_hit : window.Contains
    (leftBase ^ leftLevel / rightBase ^ rightLevel)

/-- M1.2f-new.3b: cofinal density realizes every positive window with both
exponents positive. -/
theorem cofinalScaleWindowHitData_exists
    {leftBase rightBase : ℝ} {window : PositiveScaleWindow}
    (hdense : CofinalPowerRatioDense leftBase rightBase) :
    Nonempty (CofinalScaleWindowHitData leftBase rightBase window) := by
  obtain ⟨leftLevel, rightLevel, hleftLevel, hrightLevel,
      hlower, hupper⟩ :=
    hdense window.lower window.upper window.lower_pos
      window.lower_lt_upper 1
  exact ⟨{
    leftLevel := leftLevel
    rightLevel := rightLevel
    leftLevel_pos := by omega
    rightLevel_pos := by omega
    ratio_hit := ⟨hlower, hupper⟩
  }⟩

/-- The density hit converted from normalized source coordinates to the exact
powered metric scales. -/
structure PoweredSafeTargetCellContainmentData
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    {safe : ExactSafeTowerCellData avoiding}
    {parent : RecurringTargetParentData (stable := stableτ) target}
    {pair : LateSafeTargetCellPairData safe parent}
    (window : SafeTargetCellScaleWindowData pair) where
  hit : CofinalScaleWindowHitData
    (eigenvalueσ ^ stableσ.power) (eigenvalueτ ^ stableτ.power)
    window.window
  containment :
    ScaledSourceCellContained (prefixMetricLength letterLength word)
      ((eigenvalueτ ^ stableτ.power) ^ hit.rightLevel)
        (parent.position pair.parentIndex)
      ((eigenvalueσ ^ stableσ.power) ^ hit.leftLevel)
        safe.sourcePosition

/-- M1.2f-new.3c: multiply normalized containment by the positive target
scale and use the realized power ratio. -/
theorem poweredSafeTargetCellContainmentData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    {safe : ExactSafeTowerCellData avoiding}
    {parent : RecurringTargetParentData (stable := stableτ) target}
    {pair : LateSafeTargetCellPairData safe parent}
    (window : SafeTargetCellScaleWindowData pair)
    (hit : CofinalScaleWindowHitData
      (eigenvalueσ ^ stableσ.power) (eigenvalueτ ^ stableτ.power)
      window.window) :
    Nonempty (PoweredSafeTargetCellContainmentData window) := by
  let leftScale := (eigenvalueσ ^ stableσ.power) ^ hit.leftLevel
  let rightScale := (eigenvalueτ ^ stableτ.power) ^ hit.rightLevel
  have hrightBasePos : 0 < eigenvalueτ ^ stableτ.power :=
    zero_lt_one.trans stableτ.one_lt_scale
  have hrightScalePos : 0 < rightScale :=
    pow_pos hrightBasePos hit.rightLevel
  have hnormalized :
      ScaledSourceCellContained (prefixMetricLength letterLength word)
        1 (parent.position pair.parentIndex)
        (leftScale / rightScale) safe.sourcePosition := by
    exact window.normalized_containment _ hit.ratio_hit
  have hnormalizedLeft := hnormalized.1
  have hnormalizedRight := hnormalized.2
  change (leftScale / rightScale) *
      prefixMetricLength letterLength word safe.sourcePosition ≤
        1 * prefixMetricLength letterLength word
          (parent.position pair.parentIndex) at hnormalizedLeft
  change 1 * prefixMetricLength letterLength word
      (parent.position pair.parentIndex + 1) ≤
        (leftScale / rightScale) *
          prefixMetricLength letterLength word (safe.sourcePosition + 1)
      at hnormalizedRight
  simp only [one_mul] at hnormalizedLeft hnormalizedRight
  have hcancel (value : ℝ) :
      ((leftScale / rightScale) * value) * rightScale =
        leftScale * value := by
    field_simp [hrightScalePos.ne']
  refine ⟨{ hit := hit, containment := ?_ }⟩
  change leftScale * prefixMetricLength letterLength word safe.sourcePosition ≤
      rightScale * prefixMetricLength letterLength word
        (parent.position pair.parentIndex) ∧
    rightScale * prefixMetricLength letterLength word
        (parent.position pair.parentIndex + 1) ≤
      leftScale * prefixMetricLength letterLength word
        (safe.sourcePosition + 1)
  constructor
  · calc
      leftScale * prefixMetricLength letterLength word safe.sourcePosition =
          ((leftScale / rightScale) *
              prefixMetricLength letterLength word safe.sourcePosition) *
            rightScale := (hcancel _).symm
      _ ≤ prefixMetricLength letterLength word
            (parent.position pair.parentIndex) * rightScale :=
        mul_le_mul_of_nonneg_right hnormalizedLeft hrightScalePos.le
      _ = rightScale * prefixMetricLength letterLength word
            (parent.position pair.parentIndex) := by ring
  · calc
      rightScale * prefixMetricLength letterLength word
            (parent.position pair.parentIndex + 1) =
          prefixMetricLength letterLength word
              (parent.position pair.parentIndex + 1) * rightScale := by ring
      _ ≤ ((leftScale / rightScale) *
              prefixMetricLength letterLength word
                (safe.sourcePosition + 1)) * rightScale :=
        mul_le_mul_of_nonneg_right hnormalizedRight hrightScalePos.le
      _ = leftScale * prefixMetricLength letterLength word
            (safe.sourcePosition + 1) := hcancel _

/-- M1.2f-new.4a: exact substituted boundary coordinates turn the powered
cell containment into a literal embedding of the target-parent image in the
safe image. -/
theorem poweredSafeTargetCellContainment_gives_embedding
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    {safe : ExactSafeTowerCellData avoiding}
    {parent : RecurringTargetParentData (stable := stableτ) target}
    {pair : LateSafeTargetCellPairData safe parent}
    {window : SafeTargetCellScaleWindowData pair}
    (contained : PoweredSafeTargetCellContainmentData window) :
    ∃ offset : ℕ,
      FiniteFactorAt
        ((σ.power stableσ.power).iterateLetter
          contained.hit.leftLevel avoiding.letter)
        ((τ.power stableτ.power).iterateLetter
          contained.hit.rightLevel parent.letter)
        offset := by
  have hinnerFixed :
      ((τ.power stableτ.power).power contained.hit.rightLevel).IsFixedPoint
        word :=
    Substitution.isFixedPoint_power stableτ.fixed
      contained.hit.rightLevel_pos
  have houterFixed :
      ((σ.power stableσ.power).power contained.hit.leftLevel).IsFixedPoint
        word :=
    Substitution.isFixedPoint_power stableσ.fixed
      contained.hit.leftLevel_pos
  have hinnerScales : SubstitutionScalesLetterLengths
      ((τ.power stableτ.power).power contained.hit.rightLevel)
      letterLength
      ((eigenvalueτ ^ stableτ.power) ^ contained.hit.rightLevel) :=
    scalesLetterLengths_power stableτ.scales contained.hit.rightLevel
  have houterScales : SubstitutionScalesLetterLengths
      ((σ.power stableσ.power).power contained.hit.leftLevel)
      letterLength
      ((eigenvalueσ ^ stableσ.power) ^ contained.hit.leftLevel) :=
    scalesLetterLengths_power stableσ.scales contained.hit.leftLevel
  obtain ⟨offset, hfactor⟩ :=
    scaledSourceCellContained_gives_imageEmbedding
      Pσ.letterLength_pos hinnerFixed houterFixed hinnerScales houterScales
      (parent.position pair.parentIndex) safe.sourcePosition
      contained.containment
  refine ⟨offset, ?_⟩
  simpa only [Substitution.power_apply, safe.letter_at,
    parent.letter_at pair.parentIndex] using hfactor

/-- Membership is inherited by the ambient finite word of a finite factor. -/
theorem mem_of_mem_of_finiteFactorAt
    {α : Type u} {outer inner : Word α} {offset : ℕ} {letter : α}
    (hfactor : FiniteFactorAt outer inner offset)
    (hmem : letter ∈ inner) : letter ∈ outer := by
  have hlocal : letter ∈ (outer.drop offset).take inner.length := by
    rw [hfactor.2]
    exact hmem
  exact List.mem_of_mem_drop (List.mem_of_mem_take hlocal)

/-- M1.2f-new.4b: the embedded target-parent image contains the target while
the persistent safe image avoids it, an immediate contradiction. -/
theorem poweredSafeTargetCellContainment_impossible
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength}
    {stableσ : StableMetricPowerData Pσ}
    {stableτ : StableMetricPowerData Pτ} {target : α}
    {avoiding : PersistentAvoidingPowerData Pσ stableσ target}
    {safe : ExactSafeTowerCellData avoiding}
    {parent : RecurringTargetParentData (stable := stableτ) target}
    {pair : LateSafeTargetCellPairData safe parent}
    {window : SafeTargetCellScaleWindowData pair}
    (contained : PoweredSafeTargetCellContainmentData window) : False := by
  obtain ⟨offset, hembedded⟩ :=
    poweredSafeTargetCellContainment_gives_embedding contained
  have htargetInner := target_mem_poweredParentImage parent
    contained.hit.rightLevel contained.hit.rightLevel_pos
  have htargetOuter := mem_of_mem_of_finiteFactorAt hembedded htargetInner
  exact safe.powered_image_avoids contained.hit.leftLevel
    contained.hit.leftLevel_pos htargetOuter

/-- M1.2f-new aggregator: the exact-metric first case of Durand's bounded-gap
argument, with the target-parent cell replacing the unnecessary general
prefix/suffix gap comparison. -/
theorem firstCaseMetricCellContradiction
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ} {letterLength : α → ℝ}
    (Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength)
    (Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength)
    {target : α}
    (stableσ : StableMetricPowerData Pσ)
    (stableτ : StableMetricPowerData Pτ)
    (avoiding : PersistentAvoidingPowerData Pσ stableσ target)
    (hrecurrent : OccursInfinitelyOften word target)
    (hindependent : MultiplicativelyIndependent eigenvalueσ eigenvalueτ) : False := by
  obtain ⟨tiling⟩ := poweredFixedTilingParentData_exists stableτ
  obtain ⟨parent⟩ := recurringTargetParentData_exists
    target tiling hrecurrent
  obtain ⟨safe⟩ := exactSafeTowerCellData_exists avoiding
  obtain ⟨unbounded⟩ := recurrentTargetParentCoordinateData_exists parent
  obtain ⟨pair⟩ := lateSafeTargetCellPairData_exists safe parent unbounded
  obtain ⟨window⟩ := safeTargetCellScaleWindowData_exists pair
  have hdense := stablePowerRatioDensity
    Pσ Pτ stableσ stableτ hindependent
  obtain ⟨hit⟩ := cofinalScaleWindowHitData_exists
    (window := window.window) hdense
  obtain ⟨contained⟩ :=
    poweredSafeTargetCellContainmentData_exists window hit
  exact poweredSafeTargetCellContainment_impossible contained

/-- M1.2: the exact common-metric specialization of Durand's first-case
bounded-gap argument. -/
theorem recurrentLetter_boundedGaps_of_independentMetricGrowth
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLength : α → ℝ}
    (Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength)
    (Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength)
    (hindependent : MultiplicativelyIndependent eigenvalueσ eigenvalueτ)
    (letter : α) (hrecurrent : OccursInfinitelyOften word letter) :
    LetterAppearsWithBoundedGaps word letter := by
  by_contra hnotBounded
  have hlate :=
    arbitrarilyLateAvoidingIntervals_of_recurrent_not_boundedGaps
      hrecurrent hnotBounded
  obtain ⟨orbitσ⟩ := iteratedSupportOrbitData_exists σ
  obtain ⟨orbitτ⟩ := iteratedSupportOrbitData_exists τ
  obtain ⟨stableσ⟩ := stableMetricPowerData_exists Pσ orbitσ
  obtain ⟨stableτ⟩ := stableMetricPowerData_exists Pτ orbitτ
  have himagesσ := arbitrarilyLateAvoidingImages_of_intervals
    Pσ stableσ letter hlate
  obtain ⟨avoidingσ⟩ :=
    persistentAvoidingPowerData_exists Pσ stableσ letter himagesσ
  exact firstCaseMetricCellContradiction
    Pσ Pτ stableσ stableτ avoidingσ hrecurrent hindependent

/-- M1 aggregator: every recurrent factor of a common exact-metric fixed
word is syndetic. -/
theorem recurrentFactorsSyndetic_of_independentMetricGrowth
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLength : α → ℝ}
    (Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLength)
    (Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLength)
    (hindependent : MultiplicativelyIndependent eigenvalueσ eigenvalueτ) :
    RecurrentFactorsSyndetic word := by
  intro factor hrecurrent
  by_cases hempty : factor = []
  · subst factor
    exact ⟨1, by omega, fun start ↦ ⟨0, by omega, by simp [InfiniteFactorAt]⟩⟩
  · have hlength : 0 < factor.length := List.length_pos_of_ne_nil hempty
    obtain ⟨position, _hposition, hfactorAt⟩ := hrecurrent 0
    have hfactor : IsInfiniteFactor word factor := ⟨position, hfactorAt⟩
    obtain ⟨blockσ⟩ :=
      metricHigherBlockPresentationData_exists Pσ factor.length hlength
    obtain ⟨blockτ⟩ :=
      metricHigherBlockPresentationData_exists Pτ factor.length hlength
    have hrecurrentBlock : OccursInfinitelyOften
        (higherBlockWord word factor.length) ⟨factor, rfl, hfactor⟩ :=
      (recurrentFactor_iff_higherBlockLetter hfactor).mp hrecurrent
    have hbounded :=
      recurrentLetter_boundedGaps_of_independentMetricGrowth
        blockσ.presentation blockτ.presentation hindependent
        ⟨factor, rfl, hfactor⟩ hrecurrentBlock
    exact (higherBlockLetter_boundedGaps_iff hfactor).mp hbounded

/-! ## M2: the metric recurrent core and linear recurrence -/

/-- The recurrent core carries both restricted exact-metric presentations,
after the positive source powers needed to stabilize the recurrent component.
The two core metrics are kept separate, although the geometric application
supplies them by restricting one common edge metric. -/
structure MetricCommonRecurrentCoreData
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    (Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ)
    (Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ) where
  rank : ℕ
  rank_pos : 0 < rank
  coreWord : InfiniteWord (Fin rank)
  decode : Fin rank → α
  decoded_language : ∀ factor : Word α,
    IsInfiniteFactor (fun n ↦ decode (coreWord n)) factor ↔
      IsRecurrentFactor word factor
  sourcePowerσ : ℕ
  sourcePowerτ : ℕ
  sourcePowerσ_pos : 0 < sourcePowerσ
  sourcePowerτ_pos : 0 < sourcePowerτ
  substitutionσ : Substitution (Fin rank)
  substitutionτ : Substitution (Fin rank)
  coreLengthσ : Fin rank → ℝ
  coreLengthτ : Fin rank → ℝ
  presentationσ : MetricGrowingFixedPresentation substitutionσ coreWord.head
    coreWord (eigenvalueσ ^ sourcePowerσ) coreLengthσ
  presentationτ : MetricGrowingFixedPresentation substitutionτ coreWord.head
    coreWord (eigenvalueτ ^ sourcePowerτ) coreLengthτ

/-- Quantitative return-word bounds for the aperiodic uniformly recurrent
core.  The lower bound is deliberately unavailable on the periodic branch. -/
structure AperiodicLinearRecurrenceData
    {α : Type u} [Fintype α] [DecidableEq α]
    (word : InfiniteWord α) where
  constant : ℕ
  constant_pos : 0 < constant
  uniformlyRecurrent : IsUniformlyRecurrent word
  return_upper : ∀ {marker returnWord : Word α}, marker ≠ [] →
    IsReturnWord word marker returnWord →
      returnWord.length ≤ constant * marker.length
  return_lower : ∀ {marker returnWord : Word α}, marker ≠ [] →
    IsReturnWord word marker returnWord →
      marker.length ≤ constant * returnWord.length

/-! ## M3: bounded local return systems -/

/-- Cofinal nested nonempty prefixes, with a bounded ratio between
successive marker lengths.  The ratio bound is what makes the connector
tables between adjacent levels finite. -/
structure CofinalMetricMarkerTower {α : Type u}
    [Fintype α] [DecidableEq α]
    (word : InfiniteWord α) where
  marker : ℕ → Word α
  marker_eq_take : ∀ level, marker level = word.take (level + 1)
  marker_ne_nil : ∀ level, marker level ≠ []
  marker_at_zero : ∀ level, InfiniteFactorAt word (marker level) 0
  marker_nested : ∀ level, marker level <+: marker (level + 1)
  marker_length_strictMono : StrictMono (fun level ↦ (marker level).length)
  markerRatioBound : ℕ
  markerRatioBound_pos : 0 < markerRatioBound
  marker_next_length_le : ∀ level,
    (marker (level + 1)).length ≤ markerRatioBound * (marker level).length
  marker_cofinal : ∀ lengthFloor, ∃ level,
    lengthFloor ≤ (marker level).length

/-- M3.1: choose a cofinal prefix tower with controlled successive lengths. -/
theorem cofinalMetricMarkerTower_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    (word : InfiniteWord α) :
    Nonempty (CofinalMetricMarkerTower word) := by
  refine ⟨{
    marker := fun level => word.take (level + 1)
    marker_eq_take := by
      intro level
      rfl
    marker_ne_nil := by
      intro level
      apply List.ne_nil_of_length_pos
      simp
    marker_at_zero := by
      intro level
      simp [InfiniteFactorAt]
    marker_nested := by
      intro level
      exact Stream'.take_prefix_take_left
        (a := word) (m := level + 1) (n := level + 1 + 1) (by omega)
    marker_length_strictMono := by
      intro left right hlr
      simpa using hlr
    markerRatioBound := 2
    markerRatioBound_pos := by omega
    marker_next_length_le := by
      intro level
      simp
    marker_cofinal := by
      intro lengthFloor
      exact ⟨lengthFloor, by simp⟩ }⟩

/-- Any earlier marker in a cofinal tower is a prefix of every later one. -/
theorem CofinalMetricMarkerTower.marker_prefix_of_lt
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α} (markers : CofinalMetricMarkerTower word) :
    ∀ {short long : ℕ}, short < long →
      markers.marker short <+: markers.marker long := by
  intro short long hlt
  induction long with
  | zero => omega
  | succ long ih =>
      by_cases heq : short = long
      · subst short
        exact markers.marker_nested long
      · have hshort : short < long := by omega
        exact (ih hshort).trans (markers.marker_nested long)

/-- Complete return decompositions at every marker level. -/
structure MetricReturnDecompositionTower
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (markers : CofinalMetricMarkerTower word) where
  rank : ℕ → ℕ
  decomposition : ∀ level,
    ReturnDecomposition word (markers.marker level) (rank level)

/-- M3.2: uniform recurrence supplies every level decomposition. -/
theorem metricReturnDecompositionTower_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (linear : AperiodicLinearRecurrenceData word)
    (markers : CofinalMetricMarkerTower word) :
    Nonempty (MetricReturnDecompositionTower markers) := by
  classical
  have hinfinite {factor : Word α}
      (hrecurrent : IsRecurrentFactor word factor) :
      IsInfiniteFactor word factor := by
    obtain ⟨position, _hposition, hfactor⟩ := hrecurrent 0
    exact ⟨position, hfactor⟩
  have hsyndetic : RecurrentFactorsSyndetic word := by
    intro factor hrecurrent
    exact linear.uniformlyRecurrent factor (hinfinite hrecurrent)
  have hexists (level : ℕ) :
      ∃ rank : ℕ, Nonempty
        (ReturnDecomposition word (markers.marker level) rank) := by
    have hmarkerInfinite : IsInfiniteFactor word (markers.marker level) :=
      ⟨0, markers.marker_at_zero level⟩
    have hmarkerRecurrent : IsRecurrentFactor word (markers.marker level) :=
      (linear.uniformlyRecurrent _ hmarkerInfinite).isRecurrentFactor
    obtain ⟨finiteReturns⟩ := finiteReturnWordData_exists hsyndetic
      hmarkerRecurrent (markers.marker_ne_nil level)
    exact returnDecomposition_exists linear.uniformlyRecurrent
      (markers.marker_ne_nil level) (markers.marker_at_zero level)
      finiteReturns
  choose rank hdecomposition using hexists
  let decomposition := fun level => Classical.choice (hdecomposition level)
  exact ⟨{
    rank := rank
    decomposition := decomposition }⟩

/-- Unique parsing of longer-marker return blocks into shorter-marker return
blocks. -/
structure NestedMetricReturnFactorization
    {α : Type u} {word : InfiniteWord α}
    {shortMarker longMarker : Word α} {shortRank longRank : ℕ}
    (short : ReturnDecomposition word shortMarker shortRank)
    (long : ReturnDecomposition word longMarker longRank) where
  factor : Fin longRank → Word (Fin shortRank)
  factor_decodes : ∀ letter,
    (factor letter).flatMap short.blocks = long.blocks letter
  factor_ne_nil : ∀ letter, factor letter ≠ []
  boundary : ℕ → ℕ
  boundary_zero : boundary 0 = 0
  boundary_cut : ∀ position, short.cut (boundary position) = long.cut position
  boundary_succ : ∀ position,
    boundary (position + 1) = boundary position +
      (factor (long.derived position)).length
  derived_factor_at : ∀ position,
    InfiniteFactorAt short.derived (factor (long.derived position))
      (boundary position)

/-- Every cut for the longer marker is a cut for the prefix marker. -/
theorem ReturnDecomposition.cut_alignment_of_marker_prefix
    {α : Type u} {word : InfiniteWord α}
    {shortMarker longMarker : Word α}
    {shortRank longRank : ℕ}
    (short : ReturnDecomposition word shortMarker shortRank)
    (long : ReturnDecomposition word longMarker longRank)
    (hprefix : shortMarker <+: longMarker) (position : ℕ) :
    ∃ index : ℕ, short.cut index = long.cut position := by
  have hfinite : FiniteFactorAt longMarker shortMarker 0 := by
    refine ⟨by simpa using hprefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hprefix).symm
  have hshortAt :
      InfiniteFactorAt word shortMarker (long.cut position) := by
    simpa using (long.marker_at_cut position).of_finiteFactorAt hfinite
  exact short.marker_occurrence_eq_cut hshortAt

/-- M3.3: nested prefix markers have their canonical unique parsing. -/
theorem nestedMetricReturnFactorization_exists
    {α : Type u} {word : InfiniteWord α}
    {shortMarker longMarker : Word α} {shortRank longRank : ℕ}
    (short : ReturnDecomposition word shortMarker shortRank)
    (long : ReturnDecomposition word longMarker longRank)
    (hprefix : shortMarker <+: longMarker) :
    Nonempty (NestedMetricReturnFactorization short long) := by
  classical
  let boundary : ℕ → ℕ := fun position =>
    Classical.choose
      (short.cut_alignment_of_marker_prefix long hprefix position)
  have hboundaryCut : ∀ position : ℕ,
      short.cut (boundary position) = long.cut position := by
    intro position
    exact Classical.choose_spec
      (short.cut_alignment_of_marker_prefix long hprefix position)
  have hboundaryZero : boundary 0 = 0 := by
    apply short.cut_injective
    rw [hboundaryCut, long.cut_zero, short.cut_zero]
  have hboundaryStrict : StrictMono boundary := by
    intro left right hleftRight
    apply (short.cut_strictMono.lt_iff_lt).mp
    rw [hboundaryCut, hboundaryCut]
    exact long.cut_strictMono hleftRight
  let factorAt : ℕ → Word (Fin shortRank) := fun position =>
    (short.derived.drop (boundary position)).take
      (boundary (position + 1) - boundary position)
  have hfactorAtDecodes : ∀ position : ℕ,
      (factorAt position).flatMap short.blocks =
        long.blocks (long.derived position) := by
    intro position
    have hboundaryLe : boundary position ≤ boundary (position + 1) :=
      (hboundaryStrict (Nat.lt_succ_self position)).le
    have hdecode := short.flatMap_drop_take_derived
      (boundary position) (boundary (position + 1) - boundary position)
    change (factorAt position).flatMap short.blocks =
      (word.drop (short.cut (boundary position))).take
        ((factorAt position).flatMap short.blocks).length at hdecode
    have hcutAdd := short.cut_add (boundary position)
      (boundary (position + 1) - boundary position)
    have hboundaryAdd :
        boundary position +
            (boundary (position + 1) - boundary position) =
          boundary (position + 1) :=
      Nat.add_sub_of_le hboundaryLe
    rw [hboundaryAdd] at hcutAdd
    change short.cut (boundary (position + 1)) =
      short.cut (boundary position) +
        ((factorAt position).flatMap short.blocks).length at hcutAdd
    have hlength :
        ((factorAt position).flatMap short.blocks).length =
          (long.blocks (long.derived position)).length := by
      rw [hboundaryCut, hboundaryCut, long.cut_succ] at hcutAdd
      omega
    rw [hboundaryCut, hlength] at hdecode
    exact hdecode.trans (long.block_at_cut position)
  let occurrence : Fin longRank → ℕ := fun letter =>
    Classical.choose (long.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin longRank,
      long.derived (occurrence letter) = letter := by
    intro letter
    exact Classical.choose_spec (long.every_letter_occurs letter)
  let factor : Fin longRank → Word (Fin shortRank) := fun letter =>
    factorAt (occurrence letter)
  have hfactorDecodes : ∀ letter : Fin longRank,
      (factor letter).flatMap short.blocks = long.blocks letter := by
    intro letter
    change (factorAt (occurrence letter)).flatMap short.blocks =
      long.blocks letter
    rw [hfactorAtDecodes, hoccurrence]
  have hfactorAt : ∀ position : ℕ,
      factor (long.derived position) = factorAt position := by
    intro position
    apply flatMap_returnWords_injective
      short.blocks_injective short.blocks_are_returns
    exact (hfactorDecodes (long.derived position)).trans
      (hfactorAtDecodes position).symm
  have hfactorNonempty : ∀ letter : Fin longRank,
      factor letter ≠ [] := by
    intro letter hempty
    have hdecode := hfactorDecodes letter
    rw [hempty] at hdecode
    simp only [List.flatMap_nil] at hdecode
    exact (long.blocks_are_returns letter).2.1 hdecode.symm
  have hboundarySucc : ∀ position : ℕ,
      boundary (position + 1) = boundary position +
        (factor (long.derived position)).length := by
    intro position
    have hboundaryLe : boundary position ≤ boundary (position + 1) :=
      (hboundaryStrict (Nat.lt_succ_self position)).le
    rw [hfactorAt]
    change boundary (position + 1) = boundary position +
      ((short.derived.drop (boundary position)).take
        (boundary (position + 1) - boundary position)).length
    simp only [Stream'.length_take]
    exact (Nat.add_sub_of_le hboundaryLe).symm
  have hderivedFactorAt : ∀ position : ℕ,
      InfiniteFactorAt short.derived
        (factor (long.derived position)) (boundary position) := by
    intro position
    rw [hfactorAt]
    simp [InfiniteFactorAt, factorAt]
  exact ⟨{
    factor := factor
    factor_decodes := hfactorDecodes
    factor_ne_nil := hfactorNonempty
    boundary := boundary
    boundary_zero := hboundaryZero
    boundary_cut := hboundaryCut
    boundary_succ := hboundarySucc
    derived_factor_at := hderivedFactorAt }⟩

/-- One explicitly chosen positive source power induced on a return
decomposition.  Its return metric is transported from the original metric;
dominance is therefore obtained without a left Perron vector. -/
structure FixedPowerDerivedReturnData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {marker : Word α} {rank exponent : ℕ}
    (decomposition : ReturnDecomposition word marker rank) where
  exponent_pos : 0 < exponent
  factorization : PrefixReturnFactorization (source.power exponent) decomposition
  fixed : factorization.substitution.IsFixedPoint decomposition.derived
  every_letter_occurs : ∀ letter,
    Substitution.OccursInInfiniteWord letter decomposition.derived
  returnLength : Fin rank → ℝ
  returnLength_eq : ∀ letter, returnLength letter =
    wordMetricLength letterLength (decomposition.blocks letter)
  returnLength_pos : ∀ letter, 0 < returnLength letter
  scales : SubstitutionScalesLetterLengths factorization.substitution
    returnLength (eigenvalue ^ exponent)
  dominant : IsDominantEigenvalue factorization.substitution.incidenceMatrix
    (eigenvalue ^ exponent)

/-- M3.4: induce any fixed positive source power and transport its metric. -/
private theorem wordMetricLength_pos_of_ne_nil
    {α : Type u} (metric : α → ℝ) (hmetric : ∀ letter, 0 < metric letter)
    {letters : Word α} (hletters : letters ≠ []) :
    0 < wordMetricLength metric letters := by
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hletters
  have htail : 0 ≤ wordMetricLength metric tail :=
    wordMetricLength_nonneg metric (fun letter => (hmetric letter).le) tail
  change 0 < metric head + wordMetricLength metric tail
  linarith [hmetric head]

theorem fixedPowerDerivedReturnData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalue : ℝ} {letterLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed word eigenvalue letterLength)
    {marker : Word α} {rank exponent : ℕ}
    (decomposition : ReturnDecomposition word marker rank)
    (hexponent : 0 < exponent) :
    Nonempty (FixedPowerDerivedReturnData P decomposition
      (exponent := exponent)) := by
  letI : Nonempty (Fin rank) := ⟨⟨0, decomposition.rank_pos⟩⟩
  obtain ⟨factorization⟩ := prefixReturnFactorization_exists
    (Substitution.isFixedPoint_power P.fixed hexponent) decomposition
  let returnLength : Fin rank → ℝ := fun letter =>
    wordMetricLength letterLength (decomposition.blocks letter)
  have hreturnLengthPos : ∀ letter, 0 < returnLength letter := by
    intro letter
    exact wordMetricLength_pos_of_ne_nil letterLength P.letterLength_pos
      (decomposition.blocks_are_returns letter).2.1
  have hscales : SubstitutionScalesLetterLengths factorization.substitution
      returnLength (eigenvalue ^ exponent) :=
    factorization.scalesReturnMetric
      (scalesLetterLengths_power P.scales exponent)
  exact ⟨{
    exponent_pos := hexponent
    factorization := factorization
    fixed := factorization.fixed
    every_letter_occurs := decomposition.every_letter_occurs
    returnLength := returnLength
    returnLength_eq := fun _ => rfl
    returnLength_pos := hreturnLengthPos
    scales := hscales
    dominant := dominantEigenvalue_of_positive_metric_scaling
      factorization.substitution returnLength (eigenvalue ^ exponent)
      hreturnLengthPos hscales }⟩

/-- The sound replacement for `CommonReturnTower`: each side uses one fixed
positive local source power at every marker level. -/
structure BoundedLocalReturnTower
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    (core : MetricCommonRecurrentCoreData Pσ Pτ)
    (markers : CofinalMetricMarkerTower core.coreWord)
    (decompositions : MetricReturnDecompositionTower markers) where
  leftLocalPower : ℕ
  rightLocalPower : ℕ
  leftLocalPower_pos : 0 < leftLocalPower
  rightLocalPower_pos : 0 < rightLocalPower
  left : ∀ level, FixedPowerDerivedReturnData core.presentationσ
    (decompositions.decomposition level) (exponent := leftLocalPower)
  right : ∀ level, FixedPowerDerivedReturnData core.presentationτ
    (decompositions.decomposition level) (exponent := rightLocalPower)
  nested : ∀ {short long}, short < long →
    NestedMetricReturnFactorization
      (decompositions.decomposition short)
      (decompositions.decomposition long)

/-- M3.5: assemble the fixed-power local tower. -/
theorem boundedLocalReturnTower_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    (core : MetricCommonRecurrentCoreData Pσ Pτ)
    (markers : CofinalMetricMarkerTower core.coreWord)
    (decompositions : MetricReturnDecompositionTower markers) :
    Nonempty (BoundedLocalReturnTower core markers decompositions) := by
  have hleft (level : ℕ) : Nonempty
      (FixedPowerDerivedReturnData core.presentationσ
        (decompositions.decomposition level) (exponent := 1)) :=
    fixedPowerDerivedReturnData_exists core.presentationσ
      (decompositions.decomposition level) (by omega)
  have hright (level : ℕ) : Nonempty
      (FixedPowerDerivedReturnData core.presentationτ
        (decompositions.decomposition level) (exponent := 1)) :=
    fixedPowerDerivedReturnData_exists core.presentationτ
      (decompositions.decomposition level) (by omega)
  let left := fun level => Classical.choice (hleft level)
  let right := fun level => Classical.choice (hright level)
  have hnested {short long : ℕ} (hlt : short < long) : Nonempty
      (NestedMetricReturnFactorization
        (decompositions.decomposition short)
        (decompositions.decomposition long)) :=
    nestedMetricReturnFactorization_exists
      (decompositions.decomposition short)
      (decompositions.decomposition long)
      (markers.marker_prefix_of_lt hlt)
  let nested := fun {short long : ℕ} (hlt : short < long) =>
    Classical.choice (hnested hlt)
  exact ⟨{
    leftLocalPower := 1
    rightLocalPower := 1
    leftLocalPower_pos := by omega
    rightLocalPower_pos := by omega
    left := left
    right := right
    nested := nested }⟩

/-- Uniform finite bounds for ranks, fixed-power images, and adjacent-level
connector images. -/
structure BoundedLocalReturnTowerBounds
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    (tower : BoundedLocalReturnTower core markers decompositions) where
  rankBound : ℕ
  imageLengthBound : ℕ
  connectorLengthBound : ℕ
  rank_le : ∀ level, decompositions.rank level ≤ rankBound
  left_image_le : ∀ level letter,
    ((tower.left level).factorization.substitution letter).length ≤
      imageLengthBound
  right_image_le : ∀ level letter,
    ((tower.right level).factorization.substitution letter).length ≤
      imageLengthBound
  connector_image_le : ∀ level letter,
    ((tower.nested (Nat.lt_succ_self level)).factor letter).length ≤
      connectorLengthBound

/-- Once a nonempty factor has appeared, the next occurrence after a later
cut begins within the linear-recurrence return bound. -/
private theorem nextOccurrence
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (linear : AperiodicLinearRecurrenceData word)
    {factor : Word α} (hfactorNonempty : factor ≠ [])
    {prior start : ℕ} (hpriorLe : prior ≤ start)
    (hprior : InfiniteFactorAt word factor prior) :
    ∃ position : ℕ, start ≤ position ∧
      position ≤ start + linear.constant * factor.length ∧
      InfiniteFactorAt word factor position := by
  classical
  by_cases hatStart : InfiniteFactorAt word factor start
  · exact ⟨start, le_rfl, Nat.le_add_right _ _, hatStart⟩
  have hfactor : IsInfiniteFactor word factor := ⟨prior, hprior⟩
  obtain ⟨gap, _hgap, hbounded⟩ :=
    linear.uniformlyRecurrent factor hfactor
  rcases hbounded start with ⟨offset, _hoffset, hoffsetFactor⟩
  have hexists : ∃ position : ℕ,
      start ≤ position ∧ InfiniteFactorAt word factor position :=
    ⟨start + offset, Nat.le_add_right _ _, hoffsetFactor⟩
  let next := Nat.find hexists
  have hnextSpec :
      start ≤ next ∧ InfiniteFactorAt word factor next :=
    Nat.find_spec hexists
  have hstartLtNext : start < next := by
    rcases hnextSpec.1.eq_or_lt with hEq | hLt
    · exact False.elim (hatStart (hEq ▸ hnextSpec.2))
    · exact hLt
  let earlier : Finset ℕ :=
    (Finset.range next).filter (InfiniteFactorAt word factor)
  have hpriorMem : prior ∈ earlier := by
    simp only [earlier, Finset.mem_filter, Finset.mem_range]
    exact ⟨hpriorLe.trans_lt hstartLtNext, hprior⟩
  have hearlierNonempty : earlier.Nonempty := ⟨prior, hpriorMem⟩
  let previous := earlier.max' hearlierNonempty
  have hpreviousMem : previous ∈ earlier :=
    earlier.max'_mem hearlierNonempty
  have hpreviousLt : previous < next :=
    Finset.mem_range.mp (Finset.mem_filter.mp hpreviousMem).1
  have hpreviousFactor : InfiniteFactorAt word factor previous :=
    (Finset.mem_filter.mp hpreviousMem).2
  have hconsecutive : ∀ position : ℕ,
      previous < position → position < next →
        ¬ InfiniteFactorAt word factor position := by
    intro position hpreviousPosition hpositionNext hpositionFactor
    have hpositionMem : position ∈ earlier := by
      simp only [earlier, Finset.mem_filter, Finset.mem_range]
      exact ⟨hpositionNext, hpositionFactor⟩
    have hmax := earlier.le_max' position hpositionMem
    omega
  have hreturn := returnWord_between_consecutive_occurrences
    hfactorNonempty hpreviousFactor hnextSpec.2 hpreviousLt hconsecutive
  have hreturnBound := linear.return_upper hfactorNonempty hreturn
  have hreturnLength :
      ((word.drop previous).take (next - previous)).length =
        next - previous := by simp
  rw [hreturnLength] at hreturnBound
  have hpreviousLeStart : previous ≤ start := by
    by_contra hnot
    have hstartPrevious : start ≤ previous := by omega
    have hpredicate :
        start ≤ previous ∧ InfiniteFactorAt word factor previous :=
      ⟨hstartPrevious, hpreviousFactor⟩
    have hminimal := Nat.find_min' hexists hpredicate
    change next ≤ previous at hminimal
    omega
  exact ⟨next, hnextSpec.1, by omega, hnextSpec.2⟩

/-- Summing the lower return-word estimate over a coded word bounds its
number of return letters by the physical decoded length. -/
private theorem decodedLength_lower
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (linear : AperiodicLinearRecurrenceData word)
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank)
    (letters : Word (Fin rank)) :
    letters.length * marker.length ≤
      linear.constant * (letters.flatMap decomposition.blocks).length := by
  induction letters with
  | nil => simp
  | cons letter tail ih =>
      have hblock : marker.length ≤
          linear.constant * (decomposition.blocks letter).length :=
        linear.return_lower decomposition.marker_ne_nil
          (decomposition.blocks_are_returns letter)
      rw [List.length_cons, List.flatMap_cons, List.length_append,
        Nat.add_mul]
      calc
        tail.length * marker.length + 1 * marker.length ≤
            linear.constant * (tail.flatMap decomposition.blocks).length +
              linear.constant * (decomposition.blocks letter).length :=
          Nat.add_le_add ih (by simpa using hblock)
        _ = linear.constant *
            ((decomposition.blocks letter).length +
              (tail.flatMap decomposition.blocks).length) := by
          simp only [Nat.mul_add]
          omega

/-- A finite upper bound for the length of a one-step substitution image. -/
private def totalImageLength {α : Type u} [Fintype α]
    (source : Substitution α) : ℕ :=
  ∑ letter : α, (source letter).length

/-- Decoding a source word expands ordinary length by at most the total
one-step image bound. -/
private theorem mapWord_length_le_totalImageLength_mul
    {α : Type u} [Fintype α] [DecidableEq α]
    (source : Substitution α) (letters : Word α) :
    (source.mapWord letters).length ≤
      totalImageLength source * letters.length := by
  induction letters with
  | nil => simp
  | cons head tail ih =>
      have hhead : (source head).length ≤ totalImageLength source := by
        dsimp [totalImageLength]
        exact Finset.single_le_sum
          (fun letter _ => Nat.zero_le ((source letter).length))
          (Finset.mem_univ head)
      rw [Substitution.mapWord_cons, List.length_append, List.length_cons]
      calc
        (source head).length + (source.mapWord tail).length ≤
            totalImageLength source +
              totalImageLength source * tail.length :=
          Nat.add_le_add hhead ih
        _ = totalImageLength source * (tail.length + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- The image of an induced return substitution has a level-independent
length bound depending only on the recurrence constant and its fixed source
substitution. -/
private theorem inducedImage_length_le
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (linear : AperiodicLinearRecurrenceData word)
    (source : Substitution α)
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank)
    (factorization : PrefixReturnFactorization source decomposition)
    (letter : Fin rank) :
    (factorization.substitution letter).length ≤
      linear.constant * (totalImageLength source * linear.constant) := by
  have hdecodedLower :=
    decodedLength_lower linear decomposition (factorization.factor letter)
  rw [factorization.factor_decodes] at hdecodedLower
  have hsourceUpper :
      (source.mapWord (decomposition.blocks letter)).length ≤
        totalImageLength source *
          (decomposition.blocks letter).length :=
    mapWord_length_le_totalImageLength_mul source
      (decomposition.blocks letter)
  have hblockUpper : (decomposition.blocks letter).length ≤
      linear.constant * marker.length :=
    linear.return_upper decomposition.marker_ne_nil
      (decomposition.blocks_are_returns letter)
  have hproduct : (factorization.substitution letter).length *
        marker.length ≤
      (linear.constant *
        (totalImageLength source * linear.constant)) * marker.length := by
    change (factorization.factor letter).length * marker.length ≤ _
    calc
      (factorization.factor letter).length * marker.length ≤
          linear.constant *
            (source.mapWord (decomposition.blocks letter)).length :=
        hdecodedLower
      _ ≤ linear.constant *
            (totalImageLength source *
              (decomposition.blocks letter).length) :=
        Nat.mul_le_mul_left _ hsourceUpper
      _ ≤ linear.constant *
            (totalImageLength source *
              (linear.constant * marker.length)) :=
        Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ hblockUpper)
      _ = (linear.constant *
            (totalImageLength source * linear.constant)) * marker.length := by
        simp only [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right hproduct
    (List.length_pos_of_ne_nil decomposition.marker_ne_nil)

/-- Aperiodic linear recurrence bounds the number of distinct return words
to every nonempty marker. -/
private theorem returnRank_le
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (linear : AperiodicLinearRecurrenceData word)
    {marker : Word α} {rank : ℕ}
    (decomposition : ReturnDecomposition word marker rank) :
    rank ≤ linear.constant *
      (linear.constant * (linear.constant + 1)) + 1 := by
  classical
  let occurrence : Fin rank → ℕ := fun letter =>
    Classical.choose (decomposition.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin rank,
      decomposition.derived (occurrence letter) = letter := by
    intro letter
    exact Classical.choose_spec
      (decomposition.every_letter_occurs letter)
  let baseline : ℕ := ∑ letter : Fin rank, occurrence letter
  have hoccurrenceLe : ∀ letter : Fin rank,
      occurrence letter ≤ baseline := by
    intro letter
    dsimp [baseline]
    exact Finset.single_le_sum (fun candidate _ => Nat.zero_le _)
      (Finset.mem_univ letter)
  let offsetBound :=
    linear.constant * (linear.constant * (linear.constant + 1))
  have hnear : ∀ letter : Fin rank,
      ∃ index : ℕ, baseline ≤ index ∧
        index - baseline ≤ offsetBound ∧
        decomposition.derived index = letter := by
    intro letter
    have hpriorCut : decomposition.cut (occurrence letter) ≤
        decomposition.cut baseline :=
      decomposition.cut_strictMono.monotone (hoccurrenceLe letter)
    have hprior : InfiniteFactorAt word
        (decomposition.blocks letter ++ marker)
        (decomposition.cut (occurrence letter)) := by
      have hat := decomposition.block_marker_at_cut (occurrence letter)
      rw [hoccurrence letter] at hat
      exact hat
    have hfactorNonempty : decomposition.blocks letter ++ marker ≠ [] :=
      List.append_ne_nil_of_left_ne_nil
        (decomposition.blocks_are_returns letter).2.1 marker
    obtain ⟨physicalPosition, hphysicalLower, hphysicalUpper,
        hfactor⟩ :=
      nextOccurrence linear hfactorNonempty hpriorCut hprior
    obtain ⟨index, hcutIndex, hderived⟩ :=
      decomposition.block_marker_occurrence_aligns letter hfactor
    have hbaselineIndex : baseline ≤ index := by
      apply decomposition.cut_strictMono.le_iff_le.mp
      rw [hcutIndex]
      exact hphysicalLower
    let offset := index - baseline
    have hindexEq : baseline + offset = index :=
      Nat.add_sub_of_le hbaselineIndex
    have hblockUpper : (decomposition.blocks letter).length ≤
        linear.constant * marker.length :=
      linear.return_upper decomposition.marker_ne_nil
        (decomposition.blocks_are_returns letter)
    have hfactorLength :
        (decomposition.blocks letter ++ marker).length ≤
          (linear.constant + 1) * marker.length := by
      simp only [List.length_append, Nat.add_mul, one_mul]
      exact Nat.add_le_add_right hblockUpper marker.length
    have hcutUpper : decomposition.cut index ≤
        decomposition.cut baseline +
          linear.constant * ((linear.constant + 1) * marker.length) := by
      rw [hcutIndex]
      exact hphysicalUpper.trans
        (Nat.add_le_add_left
          (Nat.mul_le_mul_left linear.constant hfactorLength) _)
    let coded :=
      (decomposition.derived.drop baseline).take offset
    have hcodedLength : coded.length = offset := by
      simp [coded]
    have hdecodedLower :=
      decodedLength_lower linear decomposition coded
    rw [hcodedLength] at hdecodedLower
    have hcutAdd := decomposition.cut_add baseline offset
    rw [hindexEq] at hcutAdd
    have hdecodedUpper : (coded.flatMap decomposition.blocks).length ≤
        linear.constant * ((linear.constant + 1) * marker.length) := by
      change ((decomposition.derived.drop baseline).take offset |>.flatMap
        decomposition.blocks).length ≤ _
      rw [hcutAdd] at hcutUpper
      omega
    have hoffsetProduct : offset * marker.length ≤
        offsetBound * marker.length := by
      calc
        offset * marker.length ≤
            linear.constant *
              (coded.flatMap decomposition.blocks).length :=
          hdecodedLower
        _ ≤ linear.constant *
              (linear.constant *
                ((linear.constant + 1) * marker.length)) :=
          Nat.mul_le_mul_left linear.constant hdecodedUpper
        _ = offsetBound * marker.length := by
          simp only [offsetBound, Nat.mul_assoc]
    have hoffset : offset ≤ offsetBound :=
      Nat.le_of_mul_le_mul_right hoffsetProduct
        (List.length_pos_of_ne_nil decomposition.marker_ne_nil)
    exact ⟨index, hbaselineIndex, by simpa [offset] using hoffset,
      hderived⟩
  let selectedIndex : Fin rank → ℕ := fun letter =>
    Classical.choose (hnear letter)
  have hselectedLower : ∀ letter : Fin rank,
      baseline ≤ selectedIndex letter := by
    intro letter
    exact (Classical.choose_spec (hnear letter)).1
  have hselectedOffset : ∀ letter : Fin rank,
      selectedIndex letter - baseline ≤ offsetBound := by
    intro letter
    exact (Classical.choose_spec (hnear letter)).2.1
  have hselectedDerived : ∀ letter : Fin rank,
      decomposition.derived (selectedIndex letter) = letter := by
    intro letter
    exact (Classical.choose_spec (hnear letter)).2.2
  let encode : Fin rank → Fin (offsetBound + 1) := fun letter =>
    ⟨selectedIndex letter - baseline, by
      have := hselectedOffset letter
      omega⟩
  have hencode : Function.Injective encode := by
    intro leftLetter rightLetter heq
    have hoffsetEq := congrArg Fin.val heq
    have hindexEq : selectedIndex leftLetter =
        selectedIndex rightLetter := by
      have hleft := hselectedLower leftLetter
      have hright := hselectedLower rightLetter
      change selectedIndex leftLetter - baseline =
        selectedIndex rightLetter - baseline at hoffsetEq
      omega
    have hleftDerived := hselectedDerived leftLetter
    have hrightDerived := hselectedDerived rightLetter
    rw [hindexEq] at hleftDerived
    exact hleftDerived.symm.trans hrightDerived
  have hcard := Fintype.card_le_of_injective encode hencode
  simpa [offsetBound] using hcard

/-- The adjacent connector from the next marker level to the current level
is uniformly bounded.  This is the extra estimate required by the finite
coding record: it uses the tower's explicit adjacent marker-ratio bound. -/
private theorem adjacentConnector_length_le
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α}
    (linear : AperiodicLinearRecurrenceData word)
    (markers : CofinalMetricMarkerTower word)
    (decompositions : MetricReturnDecompositionTower markers)
    (level : ℕ)
    (nested : NestedMetricReturnFactorization
      (decompositions.decomposition level)
      (decompositions.decomposition (level + 1)))
    (letter : Fin (decompositions.rank (level + 1))) :
    (nested.factor letter).length ≤
      linear.constant * (linear.constant * markers.markerRatioBound) := by
  let short := decompositions.decomposition level
  let long := decompositions.decomposition (level + 1)
  have hdecodedLower :=
    decodedLength_lower linear short (nested.factor letter)
  rw [nested.factor_decodes] at hdecodedLower
  have hlongUpper : (long.blocks letter).length ≤
      linear.constant * (markers.marker (level + 1)).length :=
    linear.return_upper long.marker_ne_nil
      (long.blocks_are_returns letter)
  have hmarkerUpper : (markers.marker (level + 1)).length ≤
      markers.markerRatioBound * (markers.marker level).length :=
    markers.marker_next_length_le level
  have hproduct : (nested.factor letter).length *
        (markers.marker level).length ≤
      (linear.constant *
        (linear.constant * markers.markerRatioBound)) *
          (markers.marker level).length := by
    calc
      (nested.factor letter).length * (markers.marker level).length ≤
          linear.constant * (long.blocks letter).length :=
        hdecodedLower
      _ ≤ linear.constant *
          (linear.constant * (markers.marker (level + 1)).length) :=
        Nat.mul_le_mul_left _ hlongUpper
      _ ≤ linear.constant *
          (linear.constant *
            (markers.markerRatioBound * (markers.marker level).length)) :=
        Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _ hmarkerUpper)
      _ = (linear.constant *
          (linear.constant * markers.markerRatioBound)) *
            (markers.marker level).length := by
        simp only [Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right hproduct
    (List.length_pos_of_ne_nil short.marker_ne_nil)

/-- M3.6: aperiodic linear recurrence bounds the complete local state. -/
theorem boundedLocalReturnTower_has_uniformBounds
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    (linear : AperiodicLinearRecurrenceData core.coreWord)
    (tower : BoundedLocalReturnTower core markers decompositions) :
    Nonempty (BoundedLocalReturnTowerBounds tower) := by
  let leftSource := core.substitutionσ.power tower.leftLocalPower
  let rightSource := core.substitutionτ.power tower.rightLocalPower
  let rankBound := linear.constant *
    (linear.constant * (linear.constant + 1)) + 1
  let leftImageBound := linear.constant *
    (totalImageLength leftSource * linear.constant)
  let rightImageBound := linear.constant *
    (totalImageLength rightSource * linear.constant)
  let imageLengthBound := leftImageBound + rightImageBound
  let connectorLengthBound := linear.constant *
    (linear.constant * markers.markerRatioBound)
  refine ⟨{
    rankBound := rankBound
    imageLengthBound := imageLengthBound
    connectorLengthBound := connectorLengthBound
    rank_le := ?_
    left_image_le := ?_
    right_image_le := ?_
    connector_image_le := ?_ }⟩
  · intro level
    simpa [rankBound] using
      returnRank_le linear (decompositions.decomposition level)
  · intro level letter
    have hbound := inducedImage_length_le linear leftSource
      (decompositions.decomposition level)
      (tower.left level).factorization letter
    exact hbound.trans (by
      dsimp [imageLengthBound, leftImageBound]
      exact Nat.le_add_right _ _)
  · intro level letter
    have hbound := inducedImage_length_le linear rightSource
      (decompositions.decomposition level)
      (tower.right level).factorization letter
    exact hbound.trans (by
      dsimp [imageLengthBound, rightImageBound]
      exact Nat.le_add_left _ _)
  · intro level letter
    simpa [connectorLengthBound] using
      adjacentConnector_length_le linear markers decompositions level
        (tower.nested (Nat.lt_succ_self level)) letter

/-- Exact equality, up to the canonical finite-alphabet relabelings, of two
complete adjacent-level paired return states.  Unlike a bare table tag, this
records the semantic data later consumed by the self-derived-system step. -/
structure PairedReturnTowerLevelsEquivalent
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    (tower : BoundedLocalReturnTower core markers decompositions)
    (left right : ℕ) where
  currentRelabel : Fin (decompositions.rank left) ≃
    Fin (decompositions.rank right)
  nextRelabel : Fin (decompositions.rank (left + 1)) ≃
    Fin (decompositions.rank (right + 1))
  current_derived_eq : ∀ position,
    currentRelabel ((decompositions.decomposition left).derived position) =
      (decompositions.decomposition right).derived position
  next_derived_eq : ∀ position,
    nextRelabel ((decompositions.decomposition (left + 1)).derived position) =
      (decompositions.decomposition (right + 1)).derived position
  left_image_eq : ∀ letter,
    ((tower.left left).factorization.substitution letter).map currentRelabel =
      (tower.left right).factorization.substitution (currentRelabel letter)
  right_image_eq : ∀ letter,
    ((tower.right left).factorization.substitution letter).map currentRelabel =
      (tower.right right).factorization.substitution (currentRelabel letter)
  connector_image_eq : ∀ letter,
    ((tower.nested (Nat.lt_succ_self left)).factor letter).map currentRelabel =
      (tower.nested (Nat.lt_succ_self right)).factor (nextRelabel letter)

/-- A faithful finite coding of all complete adjacent-level states. -/
structure BoundedLocalReturnTowerFiniteCoding
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    (_bounds : BoundedLocalReturnTowerBounds tower) where
  codeCount : ℕ
  codeCount_pos : 0 < codeCount
  code : ℕ → Fin codeCount
  same_code : ∀ left right, code left = code right →
    PairedReturnTowerLevelsEquivalent tower left right

/-! ### M3.7 finite-code implementation -/

/-- Bounded words used in the private finite-state encoding. -/
private abbrev FiniteBoundedWordFC (alphabet : Type*) (bound : ℕ) :=
  {letters : List alphabet // letters.length ≤ bound}

private noncomputable instance finiteBoundedWordFintypeFC
    (alphabet : Type*) [Fintype alphabet] (bound : ℕ) :
    Fintype (FiniteBoundedWordFC alphabet bound) :=
  (List.finite_length_le alphabet bound).fintype

/-- Embed a bounded word into the common ambient finite alphabet. -/
private def embedBoundedWordFC {rank rankBound bound : ℕ}
    (hrank : rank ≤ rankBound) (letters : List (Fin rank))
    (hlength : letters.length ≤ bound) :
    FiniteBoundedWordFC (Fin rankBound) bound :=
  ⟨letters.map (Fin.castLE hrank), by simpa using hlength⟩

/-- Pad a table whose input and output ranks can differ.  The heterogeneous
form is essential for the connector from level `n+1` to level `n`. -/
private def paddedBoundedHeterogeneousTableFC
    {inputRank outputRank rankBound bound : ℕ}
    (_hinput : inputRank ≤ rankBound)
    (houtput : outputRank ≤ rankBound)
    (table : Fin inputRank → List (Fin outputRank))
    (htable : ∀ letter, (table letter).length ≤ bound) :
    Fin rankBound → FiniteBoundedWordFC (Fin rankBound) bound :=
  fun ambientLetter =>
    if hletter : ambientLetter.val < inputRank then
      embedBoundedWordFC houtput (table ⟨ambientLetter.val, hletter⟩)
        (htable ⟨ambientLetter.val, hletter⟩)
    else
      ⟨[], by simp⟩

/-- Homogeneous specialization for substitution tables. -/
private def paddedBoundedTableFC {rank rankBound bound : ℕ}
    (hrank : rank ≤ rankBound)
    (table : Fin rank → List (Fin rank))
    (htable : ∀ letter, (table letter).length ≤ bound) :
    Fin rankBound → FiniteBoundedWordFC (Fin rankBound) bound :=
  paddedBoundedHeterogeneousTableFC hrank hrank table htable

private theorem paddedBoundedHeterogeneousTable_castLE_FC
    {inputRank outputRank rankBound bound : ℕ}
    (hinput : inputRank ≤ rankBound)
    (houtput : outputRank ≤ rankBound)
    (table : Fin inputRank → List (Fin outputRank))
    (htable : ∀ letter, (table letter).length ≤ bound)
    (letter : Fin inputRank) :
    paddedBoundedHeterogeneousTableFC hinput houtput table htable
        (Fin.castLE hinput letter) =
      embedBoundedWordFC houtput (table letter) (htable letter) := by
  simp [paddedBoundedHeterogeneousTableFC, Fin.castLE, letter.isLt]

/-- Equality of padded tables recovers the original tables up to the
canonical rank equivalences. -/
private theorem paddedBoundedHeterogeneousTable_eq_relabel_FC
    {inputRankLeft inputRankRight outputRankLeft outputRankRight
      rankBound bound : ℕ}
    (hinputLeft : inputRankLeft ≤ rankBound)
    (hinputRight : inputRankRight ≤ rankBound)
    (houtputLeft : outputRankLeft ≤ rankBound)
    (houtputRight : outputRankRight ≤ rankBound)
    (tableLeft : Fin inputRankLeft → List (Fin outputRankLeft))
    (tableRight : Fin inputRankRight → List (Fin outputRankRight))
    (htableLeft : ∀ letter, (tableLeft letter).length ≤ bound)
    (htableRight : ∀ letter, (tableRight letter).length ≤ bound)
    (hinputRank : inputRankLeft = inputRankRight)
    (houtputRank : outputRankLeft = outputRankRight)
    (hpadded :
      paddedBoundedHeterogeneousTableFC hinputLeft houtputLeft tableLeft
          htableLeft =
        paddedBoundedHeterogeneousTableFC hinputRight houtputRight tableRight
          htableRight) :
    ∀ letter,
      (tableLeft letter).map (finCongr houtputRank) =
        tableRight (finCongr hinputRank letter) := by
  intro letter
  apply (List.map_injective_iff.mpr
    (Fin.castLE_injective houtputRight))
  have hinputCast :
      Fin.castLE hinputLeft letter =
        Fin.castLE hinputRight (finCongr hinputRank letter) := by
    apply Fin.ext
    rfl
  have heval := congrFun hpadded (Fin.castLE hinputLeft letter)
  rw [paddedBoundedHeterogeneousTable_castLE_FC] at heval
  rw [hinputCast, paddedBoundedHeterogeneousTable_castLE_FC] at heval
  have hwords := congrArg Subtype.val heval
  calc
    ((tableLeft letter).map (finCongr houtputRank)).map
          (Fin.castLE houtputRight) =
        (tableLeft letter).map (Fin.castLE houtputLeft) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro sourceLetter _
      apply Fin.ext
      rfl
    _ = (tableRight (finCongr hinputRank letter)).map
          (Fin.castLE houtputRight) := by
      simpa [embedBoundedWordFC] using hwords

/-- Complete finite representation of one adjacent-level paired state. -/
private structure PairedAdjacentFiniteCodeFC
    (rankBound imageLengthBound connectorLengthBound : ℕ) where
  currentRank : Fin (rankBound + 1)
  nextRank : Fin (rankBound + 1)
  currentHead : Fin rankBound
  nextHead : Fin rankBound
  currentLeft : Fin rankBound →
    FiniteBoundedWordFC (Fin rankBound) imageLengthBound
  currentRight : Fin rankBound →
    FiniteBoundedWordFC (Fin rankBound) imageLengthBound
  nextLeft : Fin rankBound →
    FiniteBoundedWordFC (Fin rankBound) imageLengthBound
  connector : Fin rankBound →
    FiniteBoundedWordFC (Fin rankBound) connectorLengthBound
  deriving DecidableEq

private abbrev PairedAdjacentFiniteCodeTupleFC
    (rankBound imageLengthBound connectorLengthBound : ℕ) :=
  (Fin (rankBound + 1)) × (Fin (rankBound + 1)) ×
    (Fin rankBound) × (Fin rankBound) ×
    (Fin rankBound → FiniteBoundedWordFC (Fin rankBound) imageLengthBound) ×
    (Fin rankBound → FiniteBoundedWordFC (Fin rankBound) imageLengthBound) ×
    (Fin rankBound → FiniteBoundedWordFC (Fin rankBound) imageLengthBound) ×
    (Fin rankBound → FiniteBoundedWordFC (Fin rankBound) connectorLengthBound)

private def pairedAdjacentFiniteCodeEquivFC
    (rankBound imageLengthBound connectorLengthBound : ℕ) :
    PairedAdjacentFiniteCodeFC rankBound imageLengthBound connectorLengthBound ≃
      PairedAdjacentFiniteCodeTupleFC rankBound imageLengthBound
        connectorLengthBound where
  toFun code := (code.currentRank, code.nextRank, code.currentHead,
    code.nextHead, code.currentLeft, code.currentRight, code.nextLeft,
    code.connector)
  invFun tuple := {
    currentRank := tuple.1
    nextRank := tuple.2.1
    currentHead := tuple.2.2.1
    nextHead := tuple.2.2.2.1
    currentLeft := tuple.2.2.2.2.1
    currentRight := tuple.2.2.2.2.2.1
    nextLeft := tuple.2.2.2.2.2.2.1
    connector := tuple.2.2.2.2.2.2.2 }
  left_inv code := by cases code; rfl
  right_inv tuple := by
    rcases tuple with ⟨a, b, c, d, e, f, g, h⟩
    rfl

private noncomputable instance pairedAdjacentFiniteCodeFintypeFC
    (rankBound imageLengthBound connectorLengthBound : ℕ) :
    Fintype (PairedAdjacentFiniteCodeFC rankBound imageLengthBound
      connectorLengthBound) :=
  Fintype.ofEquiv
    (PairedAdjacentFiniteCodeTupleFC rankBound imageLengthBound
      connectorLengthBound)
    (pairedAdjacentFiniteCodeEquivFC rankBound imageLengthBound
      connectorLengthBound).symm

private def pairedAdjacentFiniteCodeAtFC
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word
      eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word
      eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    (bounds : BoundedLocalReturnTowerBounds tower) (level : ℕ) :
    PairedAdjacentFiniteCodeFC bounds.rankBound bounds.imageLengthBound
      bounds.connectorLengthBound := by
  let currentRankLe := bounds.rank_le level
  let nextRankLe := bounds.rank_le (level + 1)
  exact {
    currentRank := ⟨decompositions.rank level,
      Nat.lt_succ_of_le currentRankLe⟩
    nextRank := ⟨decompositions.rank (level + 1),
      Nat.lt_succ_of_le nextRankLe⟩
    currentHead := Fin.castLE currentRankLe
      (decompositions.decomposition level).derived.head
    nextHead := Fin.castLE nextRankLe
      (decompositions.decomposition (level + 1)).derived.head
    currentLeft := paddedBoundedTableFC currentRankLe
      (tower.left level).factorization.substitution
      (bounds.left_image_le level)
    currentRight := paddedBoundedTableFC currentRankLe
      (tower.right level).factorization.substitution
      (bounds.right_image_le level)
    nextLeft := paddedBoundedTableFC nextRankLe
      (tower.left (level + 1)).factorization.substitution
      (bounds.left_image_le (level + 1))
    connector := paddedBoundedHeterogeneousTableFC nextRankLe currentRankLe
      (tower.nested (Nat.lt_succ_self level)).factor
      (bounds.connector_image_le level) }

/-- Canonical semantic relabelling data recovered from an equal finite
adjacent-state code. -/
private structure PairedAdjacentCodeRelabelDataFC
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word
      eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word
      eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    (bounds : BoundedLocalReturnTowerBounds tower)
    (left right : ℕ) where
  currentRank_eq : decompositions.rank left = decompositions.rank right
  nextRank_eq : decompositions.rank (left + 1) =
    decompositions.rank (right + 1)
  currentHead_eq :
    finCongr currentRank_eq
        (decompositions.decomposition left).derived.head =
      (decompositions.decomposition right).derived.head
  nextHead_eq :
    finCongr nextRank_eq
        (decompositions.decomposition (left + 1)).derived.head =
      (decompositions.decomposition (right + 1)).derived.head
  currentLeft_eq : ∀ letter,
    ((tower.left left).factorization.substitution letter).map
        (finCongr currentRank_eq) =
      (tower.left right).factorization.substitution
        (finCongr currentRank_eq letter)
  currentRight_eq : ∀ letter,
    ((tower.right left).factorization.substitution letter).map
        (finCongr currentRank_eq) =
      (tower.right right).factorization.substitution
        (finCongr currentRank_eq letter)
  nextLeft_eq : ∀ letter,
    ((tower.left (left + 1)).factorization.substitution letter).map
        (finCongr nextRank_eq) =
      (tower.left (right + 1)).factorization.substitution
        (finCongr nextRank_eq letter)
  connector_eq : ∀ letter,
    ((tower.nested (Nat.lt_succ_self left)).factor letter).map
        (finCongr currentRank_eq) =
      (tower.nested (Nat.lt_succ_self right)).factor
        (finCongr nextRank_eq letter)

private theorem pairedAdjacentCodeRelabelData_of_eq_FC
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word
      eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word
      eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    (bounds : BoundedLocalReturnTowerBounds tower)
    (left right : ℕ)
    (hcode : pairedAdjacentFiniteCodeAtFC bounds left =
      pairedAdjacentFiniteCodeAtFC bounds right) :
    Nonempty (PairedAdjacentCodeRelabelDataFC bounds left right) := by
  let currentRankLeLeft := bounds.rank_le left
  let currentRankLeRight := bounds.rank_le right
  let nextRankLeLeft := bounds.rank_le (left + 1)
  let nextRankLeRight := bounds.rank_le (right + 1)
  have hcurrentRank : decompositions.rank left =
      decompositions.rank right := by
    simpa [pairedAdjacentFiniteCodeAtFC] using congrArg
      (fun code => code.currentRank.val) hcode
  have hnextRank : decompositions.rank (left + 1) =
      decompositions.rank (right + 1) := by
    simpa [pairedAdjacentFiniteCodeAtFC] using congrArg
      (fun code => code.nextRank.val) hcode
  have hcurrentHeadAmbient :
      Fin.castLE currentRankLeLeft
          (decompositions.decomposition left).derived.head =
        Fin.castLE currentRankLeRight
          (decompositions.decomposition right).derived.head := by
    simpa [pairedAdjacentFiniteCodeAtFC, currentRankLeLeft,
      currentRankLeRight] using congrArg
        (fun code => code.currentHead) hcode
  have hnextHeadAmbient :
      Fin.castLE nextRankLeLeft
          (decompositions.decomposition (left + 1)).derived.head =
        Fin.castLE nextRankLeRight
          (decompositions.decomposition (right + 1)).derived.head := by
    simpa [pairedAdjacentFiniteCodeAtFC, nextRankLeLeft,
      nextRankLeRight] using congrArg
        (fun code => code.nextHead) hcode
  have hcurrentLeftPadded := congrArg
    (fun code => code.currentLeft) hcode
  have hcurrentRightPadded := congrArg
    (fun code => code.currentRight) hcode
  have hnextLeftPadded := congrArg
    (fun code => code.nextLeft) hcode
  have hconnectorPadded := congrArg
    (fun code => code.connector) hcode
  refine ⟨{
    currentRank_eq := hcurrentRank
    nextRank_eq := hnextRank
    currentHead_eq := ?_
    nextHead_eq := ?_
    currentLeft_eq := ?_
    currentRight_eq := ?_
    nextLeft_eq := ?_
    connector_eq := ?_ }⟩
  · apply Fin.ext
    simpa using congrArg Fin.val hcurrentHeadAmbient
  · apply Fin.ext
    simpa using congrArg Fin.val hnextHeadAmbient
  · apply paddedBoundedHeterogeneousTable_eq_relabel_FC
      currentRankLeLeft currentRankLeRight currentRankLeLeft
      currentRankLeRight _ _ (bounds.left_image_le left)
      (bounds.left_image_le right) hcurrentRank hcurrentRank
    simpa [pairedAdjacentFiniteCodeAtFC, currentRankLeLeft,
      currentRankLeRight] using hcurrentLeftPadded
  · apply paddedBoundedHeterogeneousTable_eq_relabel_FC
      currentRankLeLeft currentRankLeRight currentRankLeLeft
      currentRankLeRight _ _ (bounds.right_image_le left)
      (bounds.right_image_le right) hcurrentRank hcurrentRank
    simpa [pairedAdjacentFiniteCodeAtFC, currentRankLeLeft,
      currentRankLeRight] using hcurrentRightPadded
  · apply paddedBoundedHeterogeneousTable_eq_relabel_FC
      nextRankLeLeft nextRankLeRight nextRankLeLeft nextRankLeRight
      _ _ (bounds.left_image_le (left + 1))
      (bounds.left_image_le (right + 1)) hnextRank hnextRank
    simpa [pairedAdjacentFiniteCodeAtFC, nextRankLeLeft,
      nextRankLeRight] using hnextLeftPadded
  · apply paddedBoundedHeterogeneousTable_eq_relabel_FC
      nextRankLeLeft nextRankLeRight currentRankLeLeft currentRankLeRight
      _ _ (bounds.connector_image_le left)
      (bounds.connector_image_le right) hnextRank hcurrentRank
    simpa [pairedAdjacentFiniteCodeAtFC, currentRankLeLeft,
      currentRankLeRight, nextRankLeLeft, nextRankLeRight] using
        hconnectorPadded

/-- Image-table conjugacy and growth determine a fixed stream pointwise from
its head.  This local form avoids adding a global infinite-word relabelling
API to the metric base module. -/
private theorem fixedPoints_relabel_pointwise_of_growing_FC
    {leftAlphabet rightAlphabet : Type*}
    {leftSource : Substitution leftAlphabet}
    {rightSource : Substitution rightAlphabet}
    {leftWord : InfiniteWord leftAlphabet}
    {rightWord : InfiniteWord rightAlphabet}
    (equiv : leftAlphabet ≃ rightAlphabet)
    (himage : ∀ letter,
      (leftSource letter).map equiv = rightSource (equiv letter))
    (hgrowing : rightSource.IsGrowing)
    (hleftFixed : leftSource.IsFixedPoint leftWord)
    (hrightFixed : rightSource.IsFixedPoint rightWord)
    (hhead : equiv leftWord.head = rightWord.head) :
    ∀ position, equiv (leftWord position) = rightWord position := by
  have hmapWord (letters : Word leftAlphabet) :
      (leftSource.mapWord letters).map equiv =
        rightSource.mapWord (letters.map equiv) := by
    induction letters with
    | nil => rfl
    | cons head tail ih =>
        simp only [Substitution.mapWord_cons, List.map_append,
          List.map_cons]
        rw [himage, ih]
  have hiterateWord (level : ℕ) (letters : Word leftAlphabet) :
      (leftSource.iterateWord level letters).map equiv =
        rightSource.iterateWord level (letters.map equiv) := by
    induction level with
    | zero => rfl
    | succ level ih =>
        rw [Substitution.iterateWord_succ,
          Substitution.iterateWord_succ, hmapWord, ih]
  have hiterateLetter (level : ℕ) (letter : leftAlphabet) :
      (leftSource.iterateLetter level letter).map equiv =
        rightSource.iterateLetter level (equiv letter) := by
    simpa [Substitution.iterateLetter] using hiterateWord level [letter]
  intro position
  obtain ⟨level, hlevel⟩ :=
    hgrowing rightWord.head (position + 1)
  have hpositionRight : position <
      (rightSource.iterateLetter level rightWord.head).length := by
    omega
  have hiterate := hiterateLetter level leftWord.head
  rw [hhead] at hiterate
  have hlength :
      (leftSource.iterateLetter level leftWord.head).length =
        (rightSource.iterateLetter level rightWord.head).length := by
    simpa using congrArg List.length hiterate
  have hpositionLeft : position <
      (leftSource.iterateLetter level leftWord.head).length := by
    omega
  have hleftPrefix :=
    iterateLetter_eq_fixedPoint_prefix hleftFixed level
  have hrightPrefix :=
    iterateLetter_eq_fixedPoint_prefix hrightFixed level
  have hpref :
      (leftWord.take
          (leftSource.iterateLetter level leftWord.head).length).map equiv =
        rightWord.take
          (leftSource.iterateLetter level leftWord.head).length := by
    rw [← hleftPrefix, hiterate, hrightPrefix, hlength]
  have hleftIndex : position <
      (leftWord.take
        (leftSource.iterateLetter level leftWord.head).length).length := by
    simpa using hpositionLeft
  have hrightIndex : position <
      (rightWord.take
        (leftSource.iterateLetter level leftWord.head).length).length := by
    simpa [hlength] using hpositionRight
  have hleftGet := Stream'.take_get
    (a := leftWord) (m := position)
    (n := (leftSource.iterateLetter level leftWord.head).length)
    hleftIndex
  have hrightGet := Stream'.take_get
    (a := rightWord) (m := position)
    (n := (leftSource.iterateLetter level leftWord.head).length)
    hrightIndex
  change equiv (Stream'.get leftWord position) =
    Stream'.get rightWord position
  rw [← hleftGet, ← hrightGet]
  have hget := congrArg (fun letters => letters[position]?) hpref
  simp only [List.getElem?_map] at hget
  rw [List.getElem?_eq_getElem hleftIndex,
    List.getElem?_eq_getElem hrightIndex] at hget
  simpa using hget

private noncomputable def PairedAdjacentCodeRelabelDataFC.toLevelsEquivalent
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word
      eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word
      eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {left right : ℕ}
    (data : PairedAdjacentCodeRelabelDataFC bounds left right) :
    PairedReturnTowerLevelsEquivalent tower left right := by
  let currentRelabel : Fin (decompositions.rank left) ≃
      Fin (decompositions.rank right) := finCongr data.currentRank_eq
  let nextRelabel : Fin (decompositions.rank (left + 1)) ≃
      Fin (decompositions.rank (right + 1)) := finCongr data.nextRank_eq
  have hcurrentWord : ∀ position,
      currentRelabel
          ((decompositions.decomposition left).derived position) =
        (decompositions.decomposition right).derived position := by
    apply fixedPoints_relabel_pointwise_of_growing_FC currentRelabel
      data.currentLeft_eq
    · letI : Nonempty (Fin (decompositions.rank right)) :=
        ⟨(decompositions.decomposition right).derived.head⟩
      exact growing_of_exact_positive_metric
        (tower.left right).factorization.substitution
        (tower.left right).returnLength
        ((eigenvalueσ ^ core.sourcePowerσ) ^ tower.leftLocalPower)
        (tower.left right).returnLength_pos (tower.left right).scales
        (one_lt_pow₀ core.presentationσ.one_lt_eigenvalue
          (Nat.ne_of_gt tower.leftLocalPower_pos))
    · exact (tower.left left).fixed
    · exact (tower.left right).fixed
    · exact data.currentHead_eq
  have hnextWord : ∀ position,
      nextRelabel
          ((decompositions.decomposition (left + 1)).derived position) =
        (decompositions.decomposition (right + 1)).derived position := by
    apply fixedPoints_relabel_pointwise_of_growing_FC nextRelabel
      data.nextLeft_eq
    · letI : Nonempty (Fin (decompositions.rank (right + 1))) :=
        ⟨(decompositions.decomposition (right + 1)).derived.head⟩
      exact growing_of_exact_positive_metric
        (tower.left (right + 1)).factorization.substitution
        (tower.left (right + 1)).returnLength
        ((eigenvalueσ ^ core.sourcePowerσ) ^ tower.leftLocalPower)
        (tower.left (right + 1)).returnLength_pos
        (tower.left (right + 1)).scales
        (one_lt_pow₀ core.presentationσ.one_lt_eigenvalue
          (Nat.ne_of_gt tower.leftLocalPower_pos))
    · exact (tower.left (left + 1)).fixed
    · exact (tower.left (right + 1)).fixed
    · exact data.nextHead_eq
  exact {
    currentRelabel := currentRelabel
    nextRelabel := nextRelabel
    current_derived_eq := hcurrentWord
    next_derived_eq := hnextWord
    left_image_eq := data.currentLeft_eq
    right_image_eq := data.currentRight_eq
    connector_image_eq := data.connector_eq }

/-- M3.7: bounded ranks and word tables give a finite code. -/
theorem boundedLocalReturnTowerBounds_have_finiteCoding
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    (bounds : BoundedLocalReturnTowerBounds tower) :
    Nonempty (BoundedLocalReturnTowerFiniteCoding bounds) := by
  let State := PairedAdjacentFiniteCodeFC bounds.rankBound
    bounds.imageLengthBound bounds.connectorLengthBound
  let stateAt : ℕ → State := pairedAdjacentFiniteCodeAtFC bounds
  have hstateNonempty : Nonempty State := ⟨stateAt 0⟩
  let enumerate : State ≃ Fin (Fintype.card State) :=
    Fintype.equivFin State
  refine ⟨{
    codeCount := Fintype.card State
    codeCount_pos := Fintype.card_pos_iff.mpr hstateNonempty
    code := fun level => enumerate (stateAt level)
    same_code := ?_ }⟩
  intro left right hcode
  have hstateCode : stateAt left = stateAt right :=
    enumerate.injective hcode
  let data := Classical.choice
    (pairedAdjacentCodeRelabelData_of_eq_FC bounds left right hstateCode)
  exact data.toLevelsEquivalent

/-- Two genuinely distinct levels with the same complete adjacent state. -/
structure RepeatedBoundedLocalReturnSystems
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    (coding : BoundedLocalReturnTowerFiniteCoding bounds) where
  earlier : ℕ
  later : ℕ
  earlier_lt_later : earlier < later
  equivalent : PairedReturnTowerLevelsEquivalent tower earlier later

/-- M3.8: finite pigeonhole repetition. -/
theorem boundedLocalReturnTowerFiniteCoding_has_repetition
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    (coding : BoundedLocalReturnTowerFiniteCoding bounds) :
    Nonempty (RepeatedBoundedLocalReturnSystems coding) := by
  obtain ⟨left, right, hne, hcode⟩ :=
    Finite.exists_ne_map_eq_of_infinite coding.code
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨left, right, hlt, coding.same_code left right hcode⟩
  · exact ⟨right, left, hgt, coding.same_code right left hcode.symm⟩

/-! ## M4: Durand Lemma 12 and Proposition 10 -/

/-- A substitution is primitive when one positive power sends every source
letter across every target letter.  This is derived internally from uniform
recurrence and metric growth; it is not an added public hypothesis. -/
def IsPrimitiveSubstitution {α : Type u} [Fintype α]
    (source : Substitution α) : Prop :=
  ∃ power : ℕ, 0 < power ∧ ∀ sourceLetter targetLetter,
    targetLetter ∈ source.iterateLetter power sourceLetter

/-- Pure periodicity of a one-sided word. -/
def IsPeriodicInfiniteWord {α : Type u} (word : InfiniteWord α) : Prop :=
  ∃ period : ℕ, 0 < period ∧ ∀ position,
    word (position + period) = word position

/-- The return-block decoder in the self-derived situation. -/
def returnDecoderSubstitutionMetric
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank) :
    Substitution (Fin rank) where
  image := decomposition.blocks
  image_ne_nil := fun letter ↦
    (decomposition.blocks_are_returns letter).2.1

/-- Exact hypotheses of Durand Proposition 10 after Lemma 12. -/
structure MetricDurandProposition10Input
    {rank : ℕ} (word : InfiniteWord (Fin rank))
    (source : Substitution (Fin rank))
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank) where
  rank_pos : 0 < rank
  seed : Fin rank
  seed_is_head : seed = word.head
  source_fixed : source.IsFixedPoint word
  source_primitive : IsPrimitiveSubstitution source
  source_prolongable : source.ProlongableOn seed
  word_aperiodic : ¬ IsPeriodicInfiniteWord word
  images_begin_seed : ∀ letter, [seed] <+: source letter
  derived_eq : decomposition.derived = word
  induced : PrefixReturnFactorization source decomposition
  induced_eq : induced.substitution = source
  decoder_fixed :
    (returnDecoderSubstitutionMetric decomposition).IsFixedPoint word
  decoder_prolongable :
    (returnDecoderSubstitutionMetric decomposition).ProlongableOn seed
  decoder_generating : ∀ letter, ∃ iterate,
    letter ∈ (returnDecoderSubstitutionMetric decomposition).iterateLetter
      iterate seed
  decoder_primitive :
    IsPrimitiveSubstitution (returnDecoderSubstitutionMetric decomposition)
  decoder_contains_all : ∀ sourceLetter targetLetter,
    targetLetter ∈ decomposition.blocks sourceLetter

/-- Lemma 12 output shared by the two fixed local return towers. -/
structure MetricDurandCommonDerivedSystem
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    (_repetition : RepeatedBoundedLocalReturnSystems coding) where
  rank : ℕ
  rank_pos : 0 < rank
  commonWord : InfiniteWord (Fin rank)
  marker : Word (Fin rank)
  decomposition : ReturnDecomposition commonWord marker rank
  leftSource : Substitution (Fin rank)
  rightSource : Substitution (Fin rank)
  leftInput : MetricDurandProposition10Input commonWord leftSource decomposition
  rightInput : MetricDurandProposition10Input commonWord rightSource decomposition
  leftBasePower : ℕ
  rightBasePower : ℕ
  leftBasePower_pos : 0 < leftBasePower
  rightBasePower_pos : 0 < rightBasePower
  leftMetric : Fin rank → ℝ
  rightMetric : Fin rank → ℝ
  leftMetric_pos : ∀ letter, 0 < leftMetric letter
  rightMetric_pos : ∀ letter, 0 < rightMetric letter
  leftScales : SubstitutionScalesLetterLengths leftSource leftMetric
    (eigenvalueσ ^ leftBasePower)
  rightScales : SubstitutionScalesLetterLengths rightSource rightMetric
    (eigenvalueτ ^ rightBasePower)

/-- Exact `Theta^l gamma = gamma Theta^l = source^p` data.  These are the
strictly increasing cumulative exponents; they are separate from the fixed
local powers in `BoundedLocalReturnTower`. -/
structure MetricDurandPowerEquationFamily
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) where
  sourcePower : ℕ → ℕ
  sourcePower_strictMono : StrictMono sourcePower
  sourcePower_zero_pos : 0 < sourcePower 0
  refinementPower : ℕ → ℕ
  refinementPower_strictMono : StrictMono refinementPower
  refinementPower_zero_pos : 0 < refinementPower 0
  gamma : Substitution (Fin rank)
  theta_comp_gamma : ∀ index,
    ((returnDecoderSubstitutionMetric decomposition).power
      (refinementPower index)).comp gamma = source.power (sourcePower index)
  gamma_comp_theta : ∀ index,
    gamma.comp ((returnDecoderSubstitutionMetric decomposition).power
      (refinementPower index)) = source.power (sourcePower index)

def HasMetricTwoSidedDecoderFactorization
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (_input : MetricDurandProposition10Input word source decomposition)
    (sourceExponent refinementExponent : ℕ) : Prop :=
  ∃ gamma : Substitution (Fin rank),
    ((returnDecoderSubstitutionMetric decomposition).power
      refinementExponent).comp gamma = source.power sourceExponent ∧
    gamma.comp ((returnDecoderSubstitutionMetric decomposition).power
      refinementExponent) = source.power sourceExponent

/-- The exact iterated decoder-return tower used in Proposition 10. -/
structure MetricDurandIteratedDecoderTower
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) where
  towerMarker : ℕ → Word (Fin rank)
  towerDecomposition : ∀ level,
    ReturnDecomposition word (towerMarker level) rank
  marker_zero : towerMarker 0 = marker
  marker_succ : ∀ level,
    towerMarker (level + 1) =
      (returnDecoderSubstitutionMetric decomposition).mapWord
        (towerMarker level) ++ marker
  derived_eq : ∀ level, (towerDecomposition level).derived = word
  blocks_eq : ∀ level letter,
    (towerDecomposition level).blocks letter =
      ((returnDecoderSubstitutionMetric decomposition).power
        (level + 1)) letter

/-- If decoded return blocks followed by the marker occur at a return cut,
injectivity of return-word decoding recovers the exact derived factor. -/
theorem derivedFactor_of_decodedMarkerAtCut
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank) :
    ∀ (letters : Word (Fin rank)) (start : ℕ),
      InfiniteFactorAt word
        (letters.flatMap decomposition.blocks ++ marker)
        (decomposition.cut start) →
      (decomposition.derived.drop start).take letters.length = letters := by
  intro letters
  induction letters with
  | nil => intro start _; simp
  | cons letter rest ih =>
      intro start hat
      have hrestMarker : marker <+:
          rest.flatMap decomposition.blocks ++ marker :=
        marker_prefix_flatMap_returnWords decomposition.blocks
          decomposition.blocks_are_returns rest
      have hfirstPrefix : decomposition.blocks letter ++ marker <+:
          (letter :: rest).flatMap decomposition.blocks ++ marker := by
        simpa [List.flatMap_cons, List.append_assoc] using
          (List.prefix_append_right_inj
            (decomposition.blocks letter)).mpr hrestMarker
      have hfirstFinite : FiniteFactorAt
          ((letter :: rest).flatMap decomposition.blocks ++ marker)
          (decomposition.blocks letter ++ marker) 0 := by
        refine ⟨by simpa using hfirstPrefix.length_le, ?_⟩
        simpa using (List.prefix_iff_eq_take.mp hfirstPrefix).symm
      have hfirstAt : InfiniteFactorAt word
          (decomposition.blocks letter ++ marker)
          (decomposition.cut start) := by
        simpa using hat.of_finiteFactorAt hfirstFinite
      have hblock :=
        decomposition.block_eq_of_block_marker_at_cut letter start hfirstAt
      have hderived : decomposition.derived start = letter :=
        (decomposition.blocks_injective hblock).symm
      let tail := rest.flatMap decomposition.blocks ++ marker
      have htailFinite : FiniteFactorAt
          ((letter :: rest).flatMap decomposition.blocks ++ marker)
          tail (decomposition.blocks letter).length := by
        simp [FiniteFactorAt, tail]
      have htailAt : InfiniteFactorAt word tail
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

/-- Decoding a finite interval of derived symbols and appending the marker
gives an occurrence at the corresponding return cut. -/
theorem decodedMarkerAtCut
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (start count : ℕ) :
    InfiniteFactorAt word
      (((decomposition.derived.drop start).take count).flatMap
          decomposition.blocks ++ marker)
      (decomposition.cut start) := by
  let letters := (decomposition.derived.drop start).take count
  let decoded := letters.flatMap decomposition.blocks
  have hdecode := decomposition.flatMap_drop_take_derived start count
  change decoded =
      (word.drop (decomposition.cut start)).take decoded.length at hdecode
  have hcut := decomposition.cut_add start count
  change decomposition.cut (start + count) =
      decomposition.cut start + decoded.length at hcut
  have hdrop :
      (word.drop (decomposition.cut start)).drop decoded.length =
        word.drop (decomposition.cut (start + count)) := by
    rw [Stream'.drop_drop, ← hcut]
  rw [InfiniteFactorAt, List.length_append, Stream'.take_add]
  rw [← hdecode, hdrop, decomposition.marker_at_cut]

/-- Decoding a return word of the derived stream gives a return word of the
original stream at the composed marker. -/
theorem decodedReturnWord_of_derivedReturnWord
    {α : Type u} {word : InfiniteWord α}
    {marker : Word α} {outerRank : ℕ}
    (outer : ReturnDecomposition word marker outerRank)
    {innerMarker innerBlock : Word (Fin outerRank)}
    (hreturn : IsReturnWord outer.derived innerMarker innerBlock) :
    IsReturnWord word
      (innerMarker.flatMap outer.blocks ++ marker)
      (innerBlock.flatMap outer.blocks) := by
  classical
  let decodedMarker := innerMarker.flatMap outer.blocks
  let decodedBlock := innerBlock.flatMap outer.blocks
  let composedMarker := decodedMarker ++ marker
  have hdecodedBlockNonempty : decodedBlock ≠ [] := by
    intro hempty
    have hinjective := flatMap_returnWords_injective
      outer.blocks_injective outer.blocks_are_returns
    apply hreturn.2.1
    apply hinjective
    simpa [decodedBlock] using hempty
  have hcomposedMarkerNonempty : composedMarker ≠ [] :=
    List.append_ne_nil_of_right_ne_nil decodedMarker outer.marker_ne_nil
  obtain ⟨origin, horigin⟩ := hreturn.2.2.1
  have hfullAt : InfiniteFactorAt word
      (decodedBlock ++ composedMarker) (outer.cut origin) := by
    have hdecoded := decodedMarkerAtCut outer origin
      (innerBlock ++ innerMarker).length
    rw [horigin] at hdecoded
    simpa [decodedBlock, decodedMarker, composedMarker,
      List.flatMap_append, List.append_assoc] using hdecoded
  have hcomposedPrefix : composedMarker <+:
      decodedBlock ++ composedMarker := by
    obtain ⟨tail, htail⟩ := hreturn.2.2.2.1
    have hmarkerTail : marker <+: tail.flatMap outer.blocks ++ marker :=
      marker_prefix_flatMap_returnWords outer.blocks
        outer.blocks_are_returns tail
    have hlift : decodedMarker ++ marker <+:
        decodedMarker ++ (tail.flatMap outer.blocks ++ marker) :=
      (List.prefix_append_right_inj decodedMarker).mpr hmarkerTail
    have hdecodedEq := congrArg (fun letters =>
      letters.flatMap outer.blocks) htail
    have hdecodedEq' :
        decodedMarker ++ tail.flatMap outer.blocks =
          decodedBlock ++ decodedMarker := by
      simpa [decodedBlock, decodedMarker, List.flatMap_append] using hdecodedEq
    have hrightEq :
        decodedMarker ++ (tail.flatMap outer.blocks ++ marker) =
          decodedBlock ++ (decodedMarker ++ marker) := by
      rw [← List.append_assoc, hdecodedEq', List.append_assoc]
    rw [hrightEq] at hlift
    change composedMarker <+: decodedBlock ++ composedMarker at hlift
    exact hlift
  refine ⟨hcomposedMarkerNonempty, hdecodedBlockNonempty,
    ⟨outer.cut origin, hfullAt⟩, hcomposedPrefix, ?_⟩
  intro physicalOffset
  constructor
  · intro hfinite
    have hcomposedAt : InfiniteFactorAt word composedMarker
        (outer.cut origin + physicalOffset) :=
      hfullAt.of_finiteFactorAt hfinite
    have hmarkerPrefix : marker <+: composedMarker :=
      marker_prefix_flatMap_returnWords outer.blocks
        outer.blocks_are_returns innerMarker
    have hmarkerFinite : FiniteFactorAt composedMarker marker 0 := by
      refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
    have hmarkerAt : InfiniteFactorAt word marker
        (outer.cut origin + physicalOffset) := by
      simpa using hcomposedAt.of_finiteFactorAt hmarkerFinite
    obtain ⟨index, hcutIndex⟩ :=
      outer.marker_occurrence_eq_cut hmarkerAt
    have hphysicalOffsetLe : physicalOffset ≤ decodedBlock.length := by
      have hlength := hfinite.1
      change physicalOffset + composedMarker.length ≤
        (decodedBlock ++ composedMarker).length at hlength
      simp only [List.length_append] at hlength
      omega
    have hinnerBlockAt : InfiniteFactorAt outer.derived
        innerBlock origin := by
      have hprefix : innerBlock <+: innerBlock ++ innerMarker :=
        List.prefix_append _ _
      have hfinitePrefix : FiniteFactorAt
          (innerBlock ++ innerMarker) innerBlock 0 := by
        refine ⟨by simpa using hprefix.length_le, ?_⟩
        simpa using (List.prefix_iff_eq_take.mp hprefix).symm
      exact horigin.of_finiteFactorAt hfinitePrefix
    have hcutEnd : outer.cut (origin + innerBlock.length) =
        outer.cut origin + decodedBlock.length := by
      have hcut := outer.cut_add origin innerBlock.length
      rw [hinnerBlockAt] at hcut
      simpa [decodedBlock] using hcut
    have horiginLe : origin ≤ index := by
      by_contra hnot
      have hstrict := outer.cut_strictMono
        (by omega : index < origin)
      rw [hcutIndex] at hstrict
      omega
    have hindexLe : index ≤ origin + innerBlock.length := by
      by_contra hnot
      have hstrict := outer.cut_strictMono
        (by omega : origin + innerBlock.length < index)
      rw [hcutIndex, hcutEnd] at hstrict
      omega
    let derivedOffset := index - origin
    have hindexEq : origin + derivedOffset = index := by
      simp [derivedOffset, Nat.add_sub_of_le horiginLe]
    have hderivedOffsetLe : derivedOffset ≤ innerBlock.length := by
      omega
    have hcomposedAtCut : InfiniteFactorAt word
        (innerMarker.flatMap outer.blocks ++ marker) (outer.cut index) := by
      rw [hcutIndex]
      simpa [decodedMarker, composedMarker] using hcomposedAt
    have hinnerMarkerAt : InfiniteFactorAt outer.derived
        innerMarker index :=
      derivedFactor_of_decodedMarkerAtCut outer innerMarker index
        hcomposedAtCut
    have hinnerMarkerAtOffset : InfiniteFactorAt outer.derived
        innerMarker (origin + derivedOffset) := by
      rw [hindexEq]
      exact hinnerMarkerAt
    have hwithin : derivedOffset + innerMarker.length ≤
        (innerBlock ++ innerMarker).length := by
      simp only [List.length_append]
      omega
    have hinnerFinite : FiniteFactorAt
        (innerBlock ++ innerMarker) innerMarker derivedOffset :=
      finiteFactorAt_of_nested_infiniteFactorAt horigin
        hinnerMarkerAtOffset hwithin
    rcases (hreturn.2.2.2.2 derivedOffset).mp hinnerFinite with
      hzero | hend
    · left
      have hcutIndex' := hcutIndex
      rw [← hindexEq, hzero, Nat.add_zero] at hcutIndex'
      omega
    · right
      have hcutIndex' := hcutIndex
      rw [← hindexEq, hend] at hcutIndex'
      rw [hcutEnd] at hcutIndex'
      change physicalOffset = decodedBlock.length
      omega
  · rintro (rfl | rfl)
    · change FiniteFactorAt
        (decodedBlock ++ composedMarker) composedMarker 0
      refine ⟨by simpa using hcomposedPrefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hcomposedPrefix).symm
    · change FiniteFactorAt
        (decodedBlock ++ composedMarker) composedMarker decodedBlock.length
      simp [FiniteFactorAt]

/-- Conversely, every return word to a composed marker has a unique parsing
as the decoding of a return word to the inner marker.  This is the completeness
field required by the current `ReturnDecomposition` API. -/
theorem encodedReturnWord_of_composedReturnWord
    {α : Type u} {word : InfiniteWord α}
    {marker : Word α} {outerRank : ℕ}
    (outer : ReturnDecomposition word marker outerRank)
    {innerMarker : Word (Fin outerRank)}
    (hinnerMarkerNonempty : innerMarker ≠ [])
    {returnWord : Word α}
    (hreturn : IsReturnWord word
      (innerMarker.flatMap outer.blocks ++ marker) returnWord) :
    ∃ innerBlock : Word (Fin outerRank),
      IsReturnWord outer.derived innerMarker innerBlock ∧
        innerBlock.flatMap outer.blocks = returnWord := by
  classical
  let decodedMarker := innerMarker.flatMap outer.blocks
  let composedMarker := decodedMarker ++ marker
  obtain ⟨origin, hfullAt⟩ := hreturn.2.2.1
  have hcomposedAtStart : InfiniteFactorAt word composedMarker origin := by
    have hcomposedPrefix : composedMarker <+:
        returnWord ++ composedMarker := by
      simpa [decodedMarker, composedMarker] using hreturn.2.2.2.1
    have hfinite : FiniteFactorAt
        (returnWord ++ composedMarker) composedMarker 0 := by
      refine ⟨by simpa using hcomposedPrefix.length_le, ?_⟩
      simpa using
        (List.prefix_iff_eq_take.mp hcomposedPrefix).symm
    simpa [composedMarker] using hfullAt.of_finiteFactorAt hfinite
  have hcomposedAtEnd : InfiniteFactorAt word composedMarker
      (origin + returnWord.length) := by
    have hfinite : FiniteFactorAt
        (returnWord ++ composedMarker) composedMarker returnWord.length := by
      simp [FiniteFactorAt]
    simpa [composedMarker] using hfullAt.of_finiteFactorAt hfinite
  have hmarkerPrefix : marker <+: composedMarker := by
    simpa [decodedMarker, composedMarker] using
      marker_prefix_flatMap_returnWords outer.blocks
        outer.blocks_are_returns innerMarker
  have hmarkerFinite : FiniteFactorAt composedMarker marker 0 := by
    refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
  have hmarkerAtStart : InfiniteFactorAt word marker origin := by
    simpa using hcomposedAtStart.of_finiteFactorAt hmarkerFinite
  have hmarkerAtEnd : InfiniteFactorAt word marker
      (origin + returnWord.length) := by
    simpa using hcomposedAtEnd.of_finiteFactorAt hmarkerFinite
  obtain ⟨first, hfirstCut⟩ :=
    outer.marker_occurrence_eq_cut hmarkerAtStart
  obtain ⟨second, hsecondCut⟩ :=
    outer.marker_occurrence_eq_cut hmarkerAtEnd
  have hfirstLtSecond : first < second := by
    apply (outer.cut_strictMono.lt_iff_lt).mp
    rw [hfirstCut, hsecondCut]
    exact Nat.lt_add_of_pos_right
      (List.length_pos_of_ne_nil hreturn.2.1)
  have hinnerAtFirst : InfiniteFactorAt outer.derived innerMarker first := by
    have hat : InfiniteFactorAt word
        (innerMarker.flatMap outer.blocks ++ marker) (outer.cut first) := by
      rw [hfirstCut]
      simpa [decodedMarker, composedMarker] using hcomposedAtStart
    exact derivedFactor_of_decodedMarkerAtCut outer innerMarker first hat
  have hinnerAtSecond : InfiniteFactorAt outer.derived innerMarker second := by
    have hat : InfiniteFactorAt word
        (innerMarker.flatMap outer.blocks ++ marker) (outer.cut second) := by
      rw [hsecondCut]
      simpa [decodedMarker, composedMarker] using hcomposedAtEnd
    exact derivedFactor_of_decodedMarkerAtCut outer innerMarker second hat
  have hinnerConsecutive : ∀ position : ℕ,
      first < position → position < second →
        ¬ InfiniteFactorAt outer.derived innerMarker position := by
    intro position hfirstPosition hpositionSecond hinnerAt
    have hcomposedAtCut := decodedMarkerAtCut outer position innerMarker.length
    rw [hinnerAt] at hcomposedAtCut
    have hcutLower : origin < outer.cut position := by
      rw [← hfirstCut]
      exact outer.cut_strictMono hfirstPosition
    have hcutUpper : outer.cut position < origin + returnWord.length := by
      rw [← hsecondCut]
      exact outer.cut_strictMono hpositionSecond
    let physicalOffset := outer.cut position - origin
    have htranslated : origin + physicalOffset = outer.cut position := by
      simp [physicalOffset, Nat.add_sub_of_le (Nat.le_of_lt hcutLower)]
    have hoffsetPos : 0 < physicalOffset := by
      dsimp only [physicalOffset]
      omega
    have hoffsetLt : physicalOffset < returnWord.length := by
      dsimp only [physicalOffset]
      omega
    have hcomposedTranslated : InfiniteFactorAt word composedMarker
        (origin + physicalOffset) := by
      rw [htranslated]
      simpa [decodedMarker, composedMarker] using hcomposedAtCut
    have hwithin : physicalOffset + composedMarker.length ≤
        (returnWord ++ composedMarker).length := by
      simp only [List.length_append]
      omega
    have hfinite : FiniteFactorAt
        (returnWord ++ composedMarker) composedMarker physicalOffset :=
      finiteFactorAt_of_nested_infiniteFactorAt hfullAt
        hcomposedTranslated hwithin
    rcases (hreturn.2.2.2.2 physicalOffset).mp (by
      simpa [composedMarker] using hfinite) with hzero | hend
    · omega
    · omega
  let innerBlock := (outer.derived.drop first).take (second - first)
  have hinnerReturn : IsReturnWord outer.derived innerMarker innerBlock := by
    exact returnWord_between_consecutive_occurrences
      hinnerMarkerNonempty hinnerAtFirst hinnerAtSecond hfirstLtSecond
        hinnerConsecutive
  have hcountEnd : first + (second - first) = second := by omega
  have hdecodedLength : (innerBlock.flatMap outer.blocks).length =
      returnWord.length := by
    have hcut := outer.cut_add first (second - first)
    change outer.cut (first + (second - first)) =
      outer.cut first + (innerBlock.flatMap outer.blocks).length at hcut
    rw [hcountEnd, hfirstCut, hsecondCut] at hcut
    omega
  have hreturnAt : InfiniteFactorAt word returnWord origin := by
    have hprefix : returnWord <+: returnWord ++ composedMarker :=
      List.prefix_append _ _
    have hfinite : FiniteFactorAt
        (returnWord ++ composedMarker) returnWord 0 := by
      refine ⟨by simpa using hprefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hprefix).symm
    exact hfullAt.of_finiteFactorAt hfinite
  have hdecode := outer.flatMap_drop_take_derived first (second - first)
  change innerBlock.flatMap outer.blocks =
      (word.drop (outer.cut first)).take
        (innerBlock.flatMap outer.blocks).length at hdecode
  have hdecoded : innerBlock.flatMap outer.blocks = returnWord := by
    rw [hfirstCut, hdecodedLength] at hdecode
    exact hdecode.trans hreturnAt
  exact ⟨innerBlock, hinnerReturn, hdecoded⟩

/-- Compose a return decomposition with a return decomposition of its
derived stream. -/
def composeReturnDecompositions
    {α : Type u} {word : InfiniteWord α}
    {outerMarker : Word α} {outerRank : ℕ}
    (outer : ReturnDecomposition word outerMarker outerRank)
    {innerMarker : Word (Fin outerRank)} {innerRank : ℕ}
    (inner : ReturnDecomposition outer.derived innerMarker innerRank) :
    ReturnDecomposition word
      (innerMarker.flatMap outer.blocks ++ outerMarker) innerRank := by
  exact {
    rank_pos := inner.rank_pos
    marker_ne_nil :=
      List.append_ne_nil_of_right_ne_nil _ outer.marker_ne_nil
    marker_at_zero := by
      have hdecoded := decodedMarkerAtCut outer 0 innerMarker.length
      have hinnerZero : outer.derived.take innerMarker.length =
          innerMarker := by
        simpa [InfiniteFactorAt] using inner.marker_at_zero
      rw [outer.cut_zero, Stream'.drop_zero, hinnerZero] at hdecoded
      exact hdecoded
    blocks := fun letter => (inner.blocks letter).flatMap outer.blocks
    blocks_injective := by
      intro left right heq
      apply inner.blocks_injective
      exact (flatMap_returnWords_injective
        outer.blocks_injective outer.blocks_are_returns) heq
    blocks_are_returns := fun letter =>
      decodedReturnWord_of_derivedReturnWord outer
        (inner.blocks_are_returns letter)
    every_return_is_block := by
      intro returnWord hreturn
      obtain ⟨innerBlock, hinnerReturn, hdecode⟩ :=
        encodedReturnWord_of_composedReturnWord outer
          inner.marker_ne_nil hreturn
      obtain ⟨letter, hletter⟩ :=
        inner.every_return_is_block innerBlock hinnerReturn
      refine ⟨letter, ?_⟩
      change (inner.blocks letter).flatMap outer.blocks = returnWord
      rw [hletter]
      exact hdecode
    derived := inner.derived
    cut := fun position => outer.cut (inner.cut position)
    cut_zero := by rw [inner.cut_zero, outer.cut_zero]
    cut_succ := by
      intro position
      have hinnerBlock := inner.block_at_cut position
      have hcut := outer.cut_add (inner.cut position)
        (inner.blocks (inner.derived position)).length
      rw [hinnerBlock] at hcut
      rw [inner.cut_succ]
      exact hcut
    block_at_cut := by
      intro position
      have hinnerBlock := inner.block_at_cut position
      have hdecode := outer.flatMap_drop_take_derived
        (inner.cut position) (inner.blocks (inner.derived position)).length
      rw [hinnerBlock] at hdecode
      exact hdecode.symm }

/-- Transport only the ambient infinite word of a return decomposition. -/
def castReturnDecompositionWord
    {α : Type u} {left right : InfiniteWord α}
    {marker : Word α} {rank : ℕ}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank) :
    ReturnDecomposition right marker rank := by
  subst right
  exact decomposition

@[simp] theorem castReturnDecompositionWord_derived
    {α : Type u} {left right : InfiniteWord α}
    {marker : Word α} {rank : ℕ}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank) :
    (castReturnDecompositionWord hword decomposition).derived =
      decomposition.derived := by
  subst right
  rfl

@[simp] theorem castReturnDecompositionWord_blocks
    {α : Type u} {left right : InfiniteWord α}
    {marker : Word α} {rank : ℕ}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank)
    (letter : Fin rank) :
    (castReturnDecompositionWord hword decomposition).blocks letter =
      decomposition.blocks letter := by
  subst right
  rfl

/-- Scratch implementation of the production M4 iterated decoder tower. -/
theorem metricDurandProposition10_has_iteratedDecoderTower
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) :
    Nonempty (MetricDurandIteratedDecoderTower input) := by
  let towerMarker : ℕ → Word (Fin rank) := fun level =>
    Nat.rec marker (fun _ previous =>
      previous.flatMap decomposition.blocks ++ marker) level
  let towerDecomposition : ∀ level : ℕ,
      ReturnDecomposition word (towerMarker level) rank := fun level =>
    Nat.rec (motive := fun level =>
        ReturnDecomposition word (towerMarker level) rank)
      decomposition
      (fun _ previous =>
        composeReturnDecompositions decomposition
          (castReturnDecompositionWord input.derived_eq.symm previous)) level
  refine ⟨{
    towerMarker := towerMarker
    towerDecomposition := towerDecomposition
    marker_zero := rfl
    marker_succ := ?_
    derived_eq := ?_
    blocks_eq := ?_ }⟩
  · intro level
    rfl
  · intro level
    induction level with
    | zero => exact input.derived_eq
    | succ level ih =>
        change
          (castReturnDecompositionWord input.derived_eq.symm
            (towerDecomposition level)).derived = word
        simpa using ih
  · intro level letter
    induction level with
    | zero =>
        simp [towerDecomposition, returnDecoderSubstitutionMetric]
    | succ level ih =>
        have hstep : (towerDecomposition (level + 1)).blocks letter =
            ((towerDecomposition level).blocks letter).flatMap
              decomposition.blocks := by
          simp [towerDecomposition, composeReturnDecompositions,
            castReturnDecompositionWord_blocks]
        rw [hstep]
        calc
          ((towerDecomposition level).blocks letter).flatMap
                  decomposition.blocks =
              (returnDecoderSubstitutionMetric decomposition).mapWord
                ((towerDecomposition level).blocks letter) := rfl
          _ = (returnDecoderSubstitutionMetric decomposition).mapWord
                (((returnDecoderSubstitutionMetric decomposition).power
                  (level + 1)) letter) := by rw [ih]
          _ = ((returnDecoderSubstitutionMetric decomposition).power
                ((level + 1) + 1)) letter := by
            simp only [Substitution.power_apply,
              Substitution.iterateLetter_succ]

/-- A source power cut at the greatest available positive decoder power. -/
structure MetricDurandMaximalFactorization
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (sourceExponent : ℕ) where
  refinementExponent : ℕ
  refinementExponent_pos : 0 < refinementExponent
  gamma : Substitution (Fin rank)
  theta_comp_gamma :
    ((returnDecoderSubstitutionMetric decomposition).power
      refinementExponent).comp gamma = source.power sourceExponent
  gamma_comp_theta :
    gamma.comp ((returnDecoderSubstitutionMetric decomposition).power
      refinementExponent) = source.power sourceExponent
  maximal : ¬ HasMetricTwoSidedDecoderFactorization input sourceExponent
    (refinementExponent + 1)

/-! ### M4.3: algebra and exact decoder parsing -/

private theorem substitution_ext
    {α : Type u} (left right : Substitution α)
    (himages : ∀ letter, left letter = right letter) : left = right := by
  cases left with
  | mk leftImage leftNonempty =>
      cases right with
      | mk rightImage rightNonempty =>
          have himage : leftImage = rightImage := by
            funext letter
            exact himages letter
          subst rightImage
          rfl

private theorem substitution_mapWord_comp
    {α : Type u} (outer inner : Substitution α) (letters : Word α) :
    (outer.comp inner).mapWord letters =
      outer.mapWord (inner.mapWord letters) := by
  induction letters with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem substitution_comp_assoc
    {α : Type u} (first second third : Substitution α) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply substitution_ext
  intro letter
  change (first.comp second).mapWord (third letter) =
    first.mapWord ((second.comp third) letter)
  rw [substitution_mapWord_comp]
  rfl

private theorem substitution_comp_id
    {α : Type u} (source : Substitution α) :
    source.comp Substitution.id = source := by
  apply substitution_ext
  intro letter
  simp [Substitution.mapWord]

private theorem substitution_id_comp
    {α : Type u} (source : Substitution α) :
    Substitution.id.comp source = source := by
  apply substitution_ext
  intro letter
  change Substitution.id.mapWord (source letter) = source letter
  have hid : ∀ letters : Word α,
      (Substitution.id : Substitution α).mapWord letters = letters := by
    intro letters
    induction letters with
    | nil => rfl
    | cons head tail ih => simp [ih]
  exact hid (source letter)

private theorem substitution_comp_left_cancel
    {α : Type u} (decoder : Substitution α)
    (hinjective : Function.Injective decoder.mapWord)
    {left right : Substitution α}
    (heq : decoder.comp left = decoder.comp right) : left = right := by
  apply substitution_ext
  intro letter
  apply hinjective
  exact congrArg (fun source : Substitution α => source letter) heq

private theorem substitution_powers_commute
    {α : Type u} {left right : Substitution α}
    (hcommute : left.comp right = right.comp left) :
    ∀ leftPower rightPower : ℕ,
      (left.power leftPower).comp (right.power rightPower) =
        (right.power rightPower).comp (left.power leftPower) := by
  have hright : ∀ rightPower : ℕ,
      left.comp (right.power rightPower) =
        (right.power rightPower).comp left := by
    intro rightPower
    induction rightPower with
    | zero =>
        rw [Substitution.power_zero,
          substitution_comp_id, substitution_id_comp]
    | succ rightPower ih =>
        rw [Substitution.power_succ]
        calc
          left.comp (right.comp (right.power rightPower)) =
              (left.comp right).comp (right.power rightPower) :=
            (substitution_comp_assoc _ _ _).symm
          _ = (right.comp left).comp (right.power rightPower) := by
            rw [hcommute]
          _ = right.comp (left.comp (right.power rightPower)) :=
            substitution_comp_assoc _ _ _
          _ = right.comp ((right.power rightPower).comp left) := by
            rw [ih]
          _ = (right.comp (right.power rightPower)).comp left :=
            (substitution_comp_assoc _ _ _).symm
  intro leftPower rightPower
  induction leftPower with
  | zero =>
      rw [Substitution.power_zero,
        substitution_id_comp, substitution_comp_id]
  | succ leftPower ih =>
      rw [Substitution.power_succ]
      calc
        (left.comp (left.power leftPower)).comp
              (right.power rightPower) =
            left.comp ((left.power leftPower).comp
              (right.power rightPower)) :=
          substitution_comp_assoc _ _ _
        _ = left.comp ((right.power rightPower).comp
              (left.power leftPower)) := by rw [ih]
        _ = (left.comp (right.power rightPower)).comp
              (left.power leftPower) :=
          (substitution_comp_assoc _ _ _).symm
        _ = ((right.power rightPower).comp left).comp
              (left.power leftPower) := by rw [hright]
        _ = (right.power rightPower).comp
              (left.comp (left.power leftPower)) :=
          substitution_comp_assoc _ _ _

private theorem source_commutes_decoder
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) :
    (returnDecoderSubstitutionMetric decomposition).comp source =
      source.comp (returnDecoderSubstitutionMetric decomposition) := by
  apply substitution_ext
  intro letter
  have hdecode := input.induced.factor_decodes letter
  have himage := congrArg (fun substitution : Substitution (Fin rank) =>
    substitution letter) input.induced_eq
  change input.induced.factor letter = source letter at himage
  rw [himage] at hdecode
  exact hdecode

private theorem substitution_iterateWord_prefix
    {α : Type u} (source : Substitution α)
    {small large : Word α} (hprefix : small <+: large) :
    ∀ level : ℕ,
      source.iterateWord level small <+:
        source.iterateWord level large := by
  intro level
  induction level with
  | zero => exact hprefix
  | succ level ih => exact Substitution.mapWord_prefix ih

private theorem substitution_iterateWord_add
    {α : Type u} (source : Substitution α) (left right : ℕ)
    (letters : Word α) :
    source.iterateWord (left + right) letters =
      source.iterateWord left (source.iterateWord right letters) := by
  induction left with
  | zero => simp
  | succ left ih =>
      simpa only [Nat.succ_add, Substitution.iterateWord_succ] using
        congrArg source.mapWord ih

private theorem substitution_iterateWord_infix
    {α : Type u} (source : Substitution α) (level : ℕ)
    {small large : Word α} (hfactor : small <:+: large) :
    source.iterateWord level small <:+:
      source.iterateWord level large := by
  have happend : ∀ left right : Word α,
      source.iterateWord level (left ++ right) =
        source.iterateWord level left ++ source.iterateWord level right := by
    intro left right
    induction level with
    | zero => rfl
    | succ level ih =>
        simp only [Substitution.iterateWord_succ, ih,
          Substitution.mapWord_append]
  rcases hfactor with ⟨left, right, rfl⟩
  refine ⟨source.iterateWord level left,
    source.iterateWord level right, ?_⟩
  simp only [happend, List.append_assoc]

private theorem substitution_iterateLetter_infix_of_mem_iterate
    {α : Type u} (source : Substitution α) {start letter : α}
    {first later : ℕ}
    (hmem : letter ∈ source.iterateLetter first start) :
    source.iterateLetter later letter <:+:
      source.iterateLetter (later + first) start := by
  have hsingle : [letter] <:+: source.iterateLetter first start :=
    (List.singleton_infix_iff letter _).2 hmem
  have himage := substitution_iterateWord_infix source later hsingle
  change source.iterateLetter later letter <:+:
    source.iterateWord later (source.iterateLetter first start) at himage
  change source.iterateWord later [letter] <:+:
    source.iterateWord (later + first) [start]
  rw [substitution_iterateWord_add]
  exact himage

private theorem substitution_succ_le_iterateLetter_length
    {α : Type u} (source : Substitution α) {seed : α}
    (hprolongable : source.ProlongableOn seed) (level : ℕ) :
    level + 1 ≤ (source.iterateLetter level seed).length := by
  have hstrict : ∀ n : ℕ,
      (source.iterateLetter n seed).length <
        (source.iterateLetter (n + 1) seed).length := by
    intro n
    induction n with
    | zero =>
        obtain ⟨tail, htail, himage⟩ := hprolongable
        simp [Substitution.iterateLetter, Substitution.iterateWord,
          himage, List.length_pos_of_ne_nil htail]
    | succ n ih =>
        have hprefix := source.iterateLetter_prefix_succ hprolongable n
        rcases hprefix with ⟨suffix, hsuffix⟩
        have hsuffixNe : suffix ≠ [] := by
          intro hsuffixNil
          subst suffix
          simp only [List.append_nil] at hsuffix
          rw [hsuffix] at ih
          exact (lt_irrefl _) ih
        rw [Substitution.iterateLetter_succ,
          Substitution.iterateLetter_succ, ← hsuffix,
          Substitution.mapWord_append, List.length_append]
        exact Nat.lt_add_of_pos_right
          (List.length_pos_of_ne_nil (source.mapWord_ne_nil hsuffixNe))
  induction level with
  | zero => simp
  | succ level ih =>
      have hstep := hstrict level
      omega

private theorem substitution_iterateLetter_eq_take_of_fixedPoint
    {α : Type u} {source : Substitution α}
    {seed : α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (hseed : word.head = seed) (level : ℕ) :
    source.iterateLetter level seed =
      word.take (source.iterateLetter level seed).length := by
  simpa [hseed] using iterateLetter_eq_fixedPoint_prefix hfixed level

private theorem exists_decoderFactorization_of_images_begin_marker
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank)
    (hderived : decomposition.derived = word)
    (source : Substitution (Fin rank))
    (hfixed : source.IsFixedPoint word)
    (hbegins : ∀ letter : Fin rank, marker <+: source letter) :
    ∃ gamma : Substitution (Fin rank),
      (returnDecoderSubstitutionMetric decomposition).comp gamma = source := by
  classical
  let sourceCut : ℕ → ℕ := fun position =>
    (source.mapWord (word.take position)).length
  have himageAt : ∀ position : ℕ,
      InfiniteFactorAt word (source (word position))
        (sourceCut position) := by
    intro position
    have hraw := Substitution.mapWord_drop_take_at_fixed
      hfixed position 1
    have hone : (word.drop position).take 1 = [word position] := by
      rw [show 1 = 0 + 1 by omega, Stream'.take_succ']
      simp only [Stream'.take_zero, List.nil_append]
      change [word (0 + position)] = [word position]
      simp
    rw [hone] at hraw
    simpa [sourceCut] using hraw
  have hmarkerAt : ∀ position : ℕ,
      InfiniteFactorAt word marker (sourceCut position) := by
    intro position
    have hprefix := hbegins (word position)
    have hfinite : FiniteFactorAt (source (word position)) marker 0 := by
      refine ⟨by simpa using hprefix.length_le, ?_⟩
      simpa using (List.prefix_iff_eq_take.mp hprefix).symm
    exact (himageAt position).of_finiteFactorAt hfinite
  let boundary : ℕ → ℕ := fun position =>
    Classical.choose
      (decomposition.marker_occurrence_eq_cut (hmarkerAt position))
  have hboundaryCut : ∀ position : ℕ,
      decomposition.cut (boundary position) = sourceCut position := by
    intro position
    exact Classical.choose_spec
      (decomposition.marker_occurrence_eq_cut (hmarkerAt position))
  have hsourceCutSucc : ∀ position : ℕ,
      sourceCut (position + 1) = sourceCut position +
        (source (word position)).length := by
    intro position
    change (source.mapWord (word.take (position + 1))).length =
      (source.mapWord (word.take position)).length +
        (source (word position)).length
    rw [Stream'.take_succ', Substitution.mapWord_append,
      List.length_append]
    simp [Stream'.get]
  have hsourceCutStrict : StrictMono sourceCut := by
    apply strictMono_nat_of_lt_succ
    intro position
    rw [hsourceCutSucc]
    exact Nat.lt_add_of_pos_right
      (List.length_pos_of_ne_nil (source.image_ne_nil (word position)))
  have hboundaryStrict : StrictMono boundary := by
    intro left right hlr
    apply (decomposition.cut_strictMono.lt_iff_lt).mp
    rw [hboundaryCut, hboundaryCut]
    exact hsourceCutStrict hlr
  let factorAt : ℕ → Word (Fin rank) := fun position =>
    (decomposition.derived.drop (boundary position)).take
      (boundary (position + 1) - boundary position)
  have hfactorAtDecodes : ∀ position : ℕ,
      (factorAt position).flatMap decomposition.blocks =
        source (word position) := by
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
    have hlength : ((factorAt position).flatMap
        decomposition.blocks).length = (source (word position)).length := by
      rw [hboundaryCut, hboundaryCut, hsourceCutSucc] at hcutAdd
      omega
    rw [hboundaryCut, hlength] at hdecode
    exact hdecode.trans (himageAt position)
  let occurrence : Fin rank → ℕ := fun letter =>
    Classical.choose (decomposition.every_letter_occurs letter)
  have hoccurrence : ∀ letter : Fin rank,
      word (occurrence letter) = letter := by
    intro letter
    have hletter := Classical.choose_spec
      (decomposition.every_letter_occurs letter)
    change decomposition.derived (occurrence letter) = letter at hletter
    exact (congrFun hderived (occurrence letter)).symm.trans hletter
  let factor : Fin rank → Word (Fin rank) := fun letter =>
    factorAt (occurrence letter)
  have hfactorDecodes : ∀ letter : Fin rank,
      (factor letter).flatMap decomposition.blocks = source letter := by
    intro letter
    change (factorAt (occurrence letter)).flatMap decomposition.blocks = _
    rw [hfactorAtDecodes, hoccurrence]
  have hfactorNonempty : ∀ letter : Fin rank, factor letter ≠ [] := by
    intro letter hempty
    have hdecode := hfactorDecodes letter
    rw [hempty] at hdecode
    simp only [List.flatMap_nil] at hdecode
    exact source.image_ne_nil letter hdecode.symm
  let gamma : Substitution (Fin rank) := {
    image := factor
    image_ne_nil := hfactorNonempty }
  refine ⟨gamma, ?_⟩
  apply substitution_ext
  intro letter
  exact hfactorDecodes letter

private theorem factorization_refinement_le_sourceImageLength
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (sourceExponent refinementExponent : ℕ)
    (hfactor : HasMetricTwoSidedDecoderFactorization input
      sourceExponent refinementExponent) :
    refinementExponent ≤
      ((source.power sourceExponent) input.seed).length := by
  rcases hfactor with ⟨gamma, hleft, _hright⟩
  cases refinementExponent with
  | zero => omega
  | succ level =>
      let theta := returnDecoderSubstitutionMetric decomposition
      obtain ⟨firstLetter, tail, hgamma⟩ :=
        List.exists_cons_of_ne_nil (gamma.image_ne_nil input.seed)
      have hseedMem : input.seed ∈
          theta.iterateLetter 1 firstLetter := by
        simpa [theta, Substitution.iterateLetter,
          Substitution.iterateWord, returnDecoderSubstitutionMetric] using
            input.decoder_contains_all firstLetter input.seed
      have hinfix := substitution_iterateLetter_infix_of_mem_iterate theta
        (later := level) hseedMem
      have hseedLength : level + 1 ≤
          (theta.iterateLetter level input.seed).length :=
        substitution_succ_le_iterateLetter_length theta
          input.decoder_prolongable level
      have hletterLength : level + 1 ≤
          (theta.iterateLetter (level + 1) firstLetter).length :=
        hseedLength.trans hinfix.length_le
      have himageLength :
          (theta.iterateLetter (level + 1) firstLetter).length ≤
            ((theta.power (level + 1)).mapWord
              (gamma input.seed)).length := by
        rw [hgamma, Substitution.mapWord_cons,
          List.length_append, Substitution.power_apply]
        omega
      have hleftSeed := congrArg (fun substitution :
        Substitution (Fin rank) => substitution input.seed) hleft
      change (theta.power (level + 1)).mapWord (gamma input.seed) =
        (source.power sourceExponent) input.seed at hleftSeed
      rw [← hleftSeed]
      exact hletterLength.trans himageLength

/-- The explicitly constructed admissible factorization beyond both input
floors, before taking the greatest admissible decoder exponent. -/
private structure CofinalDecoderFactorizationSeed
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (sourceFloor refinementFloor : ℕ) where
  sourceExponent : ℕ
  sourceFloor_lt : sourceFloor < sourceExponent
  refinementExponent : ℕ
  refinementFloor_lt : refinementFloor < refinementExponent
  factorization : HasMetricTwoSidedDecoderFactorization input
    sourceExponent refinementExponent

private theorem cofinalDecoderFactorizationSeed_exists
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (tower : MetricDurandIteratedDecoderTower input)
    (sourceFloor refinementFloor : ℕ) :
    Nonempty (CofinalDecoderFactorizationSeed input
      sourceFloor refinementFloor) := by
  classical
  let level := refinementFloor
  let currentDecomposition := tower.towerDecomposition level
  let theta := returnDecoderSubstitutionMetric decomposition
  let refinementExponent := level + 1
  let sourceDepth := sourceFloor + (tower.towerMarker level).length
  let sourceExponent := sourceDepth + 1
  let poweredSource := source.power sourceExponent
  have hsourceExponent : sourceFloor < sourceExponent := by
    simp [sourceExponent, sourceDepth]
  have hrefinementExponent : refinementFloor < refinementExponent := by
    simp [refinementExponent, level]
  have hmarkerAtZero : word.take (tower.towerMarker level).length =
      tower.towerMarker level := by
    simpa [InfiniteFactorAt, currentDecomposition] using
      (tower.towerDecomposition level).marker_at_zero
  have hseedPrefix : tower.towerMarker level <+:
      source.iterateLetter sourceDepth input.seed := by
    have hsourcePrefix :=
      substitution_iterateLetter_eq_take_of_fixedPoint
        input.source_fixed input.seed_is_head.symm sourceDepth
    have hlength : (tower.towerMarker level).length ≤
        (source.iterateLetter sourceDepth input.seed).length := by
      have hgrowth := substitution_succ_le_iterateLetter_length source
        input.source_prolongable sourceDepth
      simp [sourceDepth] at hgrowth ⊢
      omega
    have htakes := Stream'.take_prefix_take_left
      (a := word) (m := (tower.towerMarker level).length)
      (n := (source.iterateLetter sourceDepth input.seed).length) hlength
    rw [hmarkerAtZero, ← hsourcePrefix] at htakes
    exact htakes
  have hbegins : ∀ letter : Fin rank,
      tower.towerMarker level <+: poweredSource letter := by
    intro letter
    have himagePrefix := substitution_iterateWord_prefix source
      (input.images_begin_seed letter) sourceDepth
    change source.iterateLetter sourceDepth input.seed <+:
      source.iterateWord sourceDepth (source letter) at himagePrefix
    have hright : source.iterateWord sourceDepth (source letter) =
        poweredSource letter := by
      calc
        source.iterateWord sourceDepth (source letter) =
            source.iterateWord sourceDepth
              (source.iterateWord 1 [letter]) := by
          simp [Substitution.iterateWord]
        _ = source.iterateWord (sourceDepth + 1) [letter] :=
          (substitution_iterateWord_add source sourceDepth 1 [letter]).symm
        _ = poweredSource letter := by
          simp [poweredSource, sourceExponent,
            Substitution.power_apply, Substitution.iterateLetter]
    rw [hright] at himagePrefix
    exact hseedPrefix.trans himagePrefix
  have hsourceExponentPos : 0 < sourceExponent := by omega
  have hpoweredFixed : poweredSource.IsFixedPoint word :=
    Substitution.isFixedPoint_power input.source_fixed hsourceExponentPos
  obtain ⟨gamma, hdecoderGamma⟩ :=
    exists_decoderFactorization_of_images_begin_marker currentDecomposition
      (tower.derived_eq level) poweredSource hpoweredFixed hbegins
  have hdecoderEq : returnDecoderSubstitutionMetric currentDecomposition =
      theta.power refinementExponent := by
    apply substitution_ext
    intro letter
    change (tower.towerDecomposition level).blocks letter =
      ((returnDecoderSubstitutionMetric decomposition).power
        (level + 1)) letter
    exact tower.blocks_eq level letter
  have hthetaGamma : (theta.power refinementExponent).comp gamma =
      poweredSource := by
    rw [← hdecoderEq]
    exact hdecoderGamma
  have hthetaInjective : Function.Injective
      (theta.power refinementExponent).mapWord := by
    rw [← hdecoderEq]
    exact flatMap_returnWords_injective
      currentDecomposition.blocks_injective
        currentDecomposition.blocks_are_returns
  have hpowerCommute : (theta.power refinementExponent).comp poweredSource =
      poweredSource.comp (theta.power refinementExponent) := by
    exact substitution_powers_commute
      (source_commutes_decoder input)
      refinementExponent sourceExponent
  have hgammaTheta : gamma.comp (theta.power refinementExponent) =
      poweredSource := by
    apply substitution_comp_left_cancel
      (theta.power refinementExponent) hthetaInjective
    calc
      (theta.power refinementExponent).comp
            (gamma.comp (theta.power refinementExponent)) =
          ((theta.power refinementExponent).comp gamma).comp
            (theta.power refinementExponent) :=
        (substitution_comp_assoc _ _ _).symm
      _ = poweredSource.comp (theta.power refinementExponent) := by
        rw [hthetaGamma]
      _ = (theta.power refinementExponent).comp poweredSource :=
        hpowerCommute.symm
  have hinitial : HasMetricTwoSidedDecoderFactorization input sourceExponent
      refinementExponent := by
    refine ⟨gamma, ?_, ?_⟩
    · simpa [theta, poweredSource] using hthetaGamma
    · simpa [theta, poweredSource] using hgammaTheta
  exact ⟨{
    sourceExponent := sourceExponent
    sourceFloor_lt := hsourceExponent
    refinementExponent := refinementExponent
    refinementFloor_lt := hrefinementExponent
    factorization := hinitial }⟩

private theorem maximalFactorization_extends_seed
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    {sourceExponent initialExponent : ℕ}
    (hinitialPos : 0 < initialExponent)
    (hinitial : HasMetricTwoSidedDecoderFactorization input
      sourceExponent initialExponent) :
    ∃ factorization : MetricDurandMaximalFactorization input sourceExponent,
      initialExponent ≤ factorization.refinementExponent := by
  classical
  let bound := ((source.power sourceExponent) input.seed).length
  have hinitialBound : initialExponent ≤ bound :=
    factorization_refinement_le_sourceImageLength input
      sourceExponent initialExponent hinitial
  let admissible : ℕ → Prop := fun exponent =>
    HasMetricTwoSidedDecoderFactorization input sourceExponent exponent
  let maximalExponent := Nat.findGreatest admissible bound
  have hmaximalAdmissible : admissible maximalExponent :=
    Nat.findGreatest_spec hinitialBound hinitial
  have hinitialLeMaximal : initialExponent ≤ maximalExponent :=
    Nat.le_findGreatest hinitialBound hinitial
  have hmaximal : ¬ HasMetricTwoSidedDecoderFactorization input sourceExponent
      (maximalExponent + 1) := by
    intro hsuccessor
    have hsuccessorBound : maximalExponent + 1 ≤ bound :=
      factorization_refinement_le_sourceImageLength input sourceExponent
        (maximalExponent + 1) hsuccessor
    have hsuccessorLe := Nat.le_findGreatest
      (P := admissible) hsuccessorBound hsuccessor
    omega
  rcases hmaximalAdmissible with ⟨maximalGamma,
    hmaximalLeft, hmaximalRight⟩
  refine ⟨{
    refinementExponent := maximalExponent
    refinementExponent_pos := hinitialPos.trans_le hinitialLeMaximal
    gamma := maximalGamma
    theta_comp_gamma := hmaximalLeft
    gamma_comp_theta := hmaximalRight
    maximal := hmaximal }, hinitialLeMaximal⟩

/-- M4.3: cofinally large maximal two-sided decoder factorizations exist. -/
theorem metricDurandProposition10_has_cofinalMaximalFactorizations
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (tower : MetricDurandIteratedDecoderTower input)
    (sourceFloor refinementFloor : ℕ) :
    ∃ sourceExponent, sourceFloor < sourceExponent ∧
      ∃ factorization : MetricDurandMaximalFactorization input sourceExponent,
        refinementFloor < factorization.refinementExponent := by
  obtain ⟨seed⟩ := cofinalDecoderFactorizationSeed_exists input tower
    sourceFloor refinementFloor
  obtain ⟨factorization, hrefinement⟩ :=
    maximalFactorization_extends_seed input
      (Nat.zero_lt_of_lt seed.refinementFloor_lt) seed.factorization
  refine ⟨seed.sourceExponent, seed.sourceFloor_lt,
    factorization, ?_⟩
  exact seed.refinementFloor_lt.trans_le hrefinement

/-- Preliminary Proposition-10 sequence before the auxiliary morphisms have
been made constant. -/
structure MetricDurandGammaSequence
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) where
  sourcePower : ℕ → ℕ
  sourcePower_strictMono : StrictMono sourcePower
  sourcePower_zero_pos : 0 < sourcePower 0
  refinementPower : ℕ → ℕ
  refinementPower_strictMono : StrictMono refinementPower
  refinementPower_zero_pos : 0 < refinementPower 0
  gammaAt : ℕ → Substitution (Fin rank)
  theta_comp_gammaAt : ∀ index,
    ((returnDecoderSubstitutionMetric decomposition).power
      (refinementPower index)).comp (gammaAt index) =
        source.power (sourcePower index)
  gammaAt_comp_theta : ∀ index,
    (gammaAt index).comp
      ((returnDecoderSubstitutionMetric decomposition).power
        (refinementPower index)) = source.power (sourcePower index)
  refinementPower_maximal : ∀ index,
    ¬ HasMetricTwoSidedDecoderFactorization input (sourcePower index)
      (refinementPower index + 1)

theorem metricDurandProposition10_constructGammaSequence
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) :
    Nonempty (MetricDurandGammaSequence input) := by
  classical
  obtain ⟨tower⟩ := metricDurandProposition10_has_iteratedDecoderTower input
  have hexists (sourceFloor refinementFloor : ℕ) :
      ∃ sourceExponent : ℕ, sourceFloor < sourceExponent ∧
        ∃ factorization : MetricDurandMaximalFactorization input sourceExponent,
          refinementFloor < factorization.refinementExponent :=
    metricDurandProposition10_has_cofinalMaximalFactorizations input tower
      sourceFloor refinementFloor
  let selectedSource (sourceFloor refinementFloor : ℕ) : ℕ :=
    Classical.choose (hexists sourceFloor refinementFloor)
  let selectedFactor (sourceFloor refinementFloor : ℕ) :
      MetricDurandMaximalFactorization input
        (selectedSource sourceFloor refinementFloor) :=
    Classical.choose
      (Classical.choose_spec (hexists sourceFloor refinementFloor)).2
  have hselectedSource : ∀ sourceFloor refinementFloor : ℕ,
      sourceFloor < selectedSource sourceFloor refinementFloor := by
    intro sourceFloor refinementFloor
    exact (Classical.choose_spec (hexists sourceFloor refinementFloor)).1
  have hselectedFactor : ∀ sourceFloor refinementFloor : ℕ,
      refinementFloor <
        (selectedFactor sourceFloor refinementFloor).refinementExponent := by
    intro sourceFloor refinementFloor
    exact Classical.choose_spec
      (Classical.choose_spec (hexists sourceFloor refinementFloor)).2
  let Stage := Σ sourceExponent : ℕ,
    MetricDurandMaximalFactorization input sourceExponent
  let first : Stage :=
    ⟨selectedSource 0 0, selectedFactor 0 0⟩
  let next : Stage → Stage := fun previous =>
    ⟨selectedSource previous.1 previous.2.refinementExponent,
      selectedFactor previous.1 previous.2.refinementExponent⟩
  let stage : ℕ → Stage := fun index =>
    Nat.rec first (fun _ previous => next previous) index
  have hsourceStep : ∀ index : ℕ,
      (stage index).1 < (stage (index + 1)).1 := by
    intro index
    change (stage index).1 <
      selectedSource (stage index).1
        (stage index).2.refinementExponent
    exact hselectedSource _ _
  have hrefinementStep : ∀ index : ℕ,
      (stage index).2.refinementExponent <
        (stage (index + 1)).2.refinementExponent := by
    intro index
    change (stage index).2.refinementExponent <
      (selectedFactor (stage index).1
        (stage index).2.refinementExponent).refinementExponent
    exact hselectedFactor _ _
  exact ⟨{
    sourcePower := fun index => (stage index).1
    sourcePower_strictMono := strictMono_nat_of_lt_succ hsourceStep
    sourcePower_zero_pos := by
      change 0 < selectedSource 0 0
      exact hselectedSource 0 0
    refinementPower := fun index =>
      (stage index).2.refinementExponent
    refinementPower_strictMono :=
      strictMono_nat_of_lt_succ hrefinementStep
    refinementPower_zero_pos := by
      change 0 < (selectedFactor 0 0).refinementExponent
      exact hselectedFactor 0 0
    gammaAt := fun index => (stage index).2.gamma
    theta_comp_gammaAt := fun index =>
      (stage index).2.theta_comp_gamma
    gammaAt_comp_theta := fun index =>
      (stage index).2.gamma_comp_theta
    refinementPower_maximal := fun index =>
      (stage index).2.maximal }⟩

/-- Maximality controls source-image length relative to the shortest
complete decoder image. -/
structure MetricDurandGammaLengthRatioControl
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    (sequence : MetricDurandGammaSequence input) where
  ratioBound : ℕ
  ratioBound_pos : 0 < ratioBound
  minimumLetter : ℕ → Fin rank
  minimumLetter_is_minimum : ∀ index letter,
    (((returnDecoderSubstitutionMetric decomposition).power
      (sequence.refinementPower index)) (minimumLetter index)).length ≤
    (((returnDecoderSubstitutionMetric decomposition).power
      (sequence.refinementPower index)) letter).length
  source_image_length_le : ∀ index letter,
    ((source.power (sequence.sourcePower index)) letter).length ≤
      ratioBound *
        (((returnDecoderSubstitutionMetric decomposition).power
          (sequence.refinementPower index)) (minimumLetter index)).length

/-! ### M4.5: maximality and finite length-ratio control -/

private theorem markerBegins_hasMetricTwoSidedDecoderFactorization
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (tower : MetricDurandIteratedDecoderTower input)
    (sourceExponent level : ℕ)
    (hsourceExponentPos : 0 < sourceExponent)
    (hbegins : ∀ letter : Fin rank,
      tower.towerMarker level <+:
        (source.power sourceExponent) letter) :
    HasMetricTwoSidedDecoderFactorization input sourceExponent (level + 1) := by
  classical
  let localDecomposition := tower.towerDecomposition level
  let theta := returnDecoderSubstitutionMetric decomposition
  let poweredSource := source.power sourceExponent
  have hpoweredFixed : poweredSource.IsFixedPoint word :=
    Substitution.isFixedPoint_power input.source_fixed hsourceExponentPos
  obtain ⟨gamma, hdecoderGamma⟩ :=
    exists_decoderFactorization_of_images_begin_marker localDecomposition
      (tower.derived_eq level) poweredSource hpoweredFixed hbegins
  have hdecoderEq : returnDecoderSubstitutionMetric localDecomposition =
      theta.power (level + 1) := by
    apply substitution_ext
    intro letter
    change (tower.towerDecomposition level).blocks letter =
      ((returnDecoderSubstitutionMetric decomposition).power
        (level + 1)) letter
    exact tower.blocks_eq level letter
  have hthetaGamma : (theta.power (level + 1)).comp gamma =
      poweredSource := by
    rw [← hdecoderEq]
    exact hdecoderGamma
  have hthetaInjective : Function.Injective
      (theta.power (level + 1)).mapWord := by
    rw [← hdecoderEq]
    exact flatMap_returnWords_injective
      localDecomposition.blocks_injective
      localDecomposition.blocks_are_returns
  have hpowerCommute : (theta.power (level + 1)).comp poweredSource =
      poweredSource.comp (theta.power (level + 1)) := by
    exact substitution_powers_commute (source_commutes_decoder input)
      (level + 1) sourceExponent
  have hgammaTheta : gamma.comp (theta.power (level + 1)) =
      poweredSource := by
    apply substitution_comp_left_cancel
      (theta.power (level + 1)) hthetaInjective
    calc
      (theta.power (level + 1)).comp
            (gamma.comp (theta.power (level + 1))) =
          ((theta.power (level + 1)).comp gamma).comp
            (theta.power (level + 1)) :=
        (substitution_comp_assoc _ _ _).symm
      _ = poweredSource.comp (theta.power (level + 1)) := by
        rw [hthetaGamma]
      _ = (theta.power (level + 1)).comp poweredSource :=
        hpowerCommute.symm
  refine ⟨gamma, ?_, ?_⟩
  · simpa [theta, poweredSource] using hthetaGamma
  · simpa [theta, poweredSource] using hgammaTheta

private theorem previousSeed_prefix_sourcePower
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (sourceExponent : ℕ) (hsourceExponentPos : 0 < sourceExponent)
    (letter : Fin rank) :
    source.iterateLetter (sourceExponent - 1) input.seed <+:
      (source.power sourceExponent) letter := by
  obtain ⟨depth, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hsourceExponentPos)
  have himagePrefix := substitution_iterateWord_prefix source
    (input.images_begin_seed letter) depth
  change source.iterateLetter depth input.seed <+:
    source.iterateWord depth (source letter) at himagePrefix
  have hright : source.iterateWord depth (source letter) =
      (source.power (depth + 1)) letter := by
    calc
      source.iterateWord depth (source letter) =
          source.iterateWord depth
            (source.iterateWord 1 [letter]) := by
        simp [Substitution.iterateWord]
      _ = source.iterateWord (depth + 1) [letter] :=
        (substitution_iterateWord_add source depth 1 [letter]).symm
      _ = (source.power (depth + 1)) letter := by
        simp [Substitution.power_apply, Substitution.iterateLetter]
  simpa [hright] using himagePrefix

private theorem two_mul_length_le_mapWord_m45
    {alphabet : Type*} (substitution : Substitution alphabet)
    (himage : ∀ letter, 2 ≤ (substitution letter).length)
    (letters : Word alphabet) :
    2 * letters.length ≤ (substitution.mapWord letters).length := by
  induction letters with
  | nil => simp
  | cons letter tail ih =>
      rw [Substitution.mapWord_cons, List.length_append,
        List.length_cons]
      have hletter := himage letter
      omega

private def expandedTowerMarker_m45
    {alphabet : Type*} (theta : Substitution alphabet)
    (marker : Word alphabet) : ℕ → Word alphabet
  | 0 => marker
  | level + 1 =>
      theta.iterateWord (level + 1) marker ++
        expandedTowerMarker_m45 theta marker level

private theorem mapWord_expandedTowerMarker_append_m45
    {alphabet : Type*} (theta : Substitution alphabet)
    (marker : Word alphabet) (level : ℕ) :
    theta.mapWord (expandedTowerMarker_m45 theta marker level) ++ marker =
      expandedTowerMarker_m45 theta marker (level + 1) := by
  induction level with
  | zero => simp [expandedTowerMarker_m45]
  | succ level ih =>
      simp only [expandedTowerMarker_m45,
        Substitution.mapWord_append, List.append_assoc]
      rw [ih]
      rfl

private theorem towerMarker_eq_expanded_m45
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (tower : MetricDurandIteratedDecoderTower input) (level : ℕ) :
    tower.towerMarker level = expandedTowerMarker_m45
      (returnDecoderSubstitutionMetric decomposition) marker level := by
  induction level with
  | zero => simpa [expandedTowerMarker_m45] using tower.marker_zero
  | succ level ih =>
      rw [tower.marker_succ level, ih,
        mapWord_expandedTowerMarker_append_m45]

private theorem expandedTowerMarker_length_le_m45
    {alphabet : Type*} (theta : Substitution alphabet)
    (marker : Word alphabet)
    (himage : ∀ letter, 2 ≤ (theta letter).length)
    (level : ℕ) :
    (expandedTowerMarker_m45 theta marker level).length ≤
      2 * (theta.iterateWord level marker).length := by
  induction level with
  | zero =>
      simp only [expandedTowerMarker_m45,
        Substitution.iterateWord_zero]
      exact Nat.le_mul_of_pos_left marker.length (by omega)
  | succ level ih =>
      rw [expandedTowerMarker_m45, List.length_append]
      have hdouble := two_mul_length_le_mapWord_m45 theta himage
        (theta.iterateWord level marker)
      have hstep : 2 * (theta.iterateWord level marker).length ≤
          (theta.iterateWord (level + 1) marker).length := by
        simpa only [Substitution.iterateWord_succ] using hdouble
      calc
        (theta.iterateWord (level + 1) marker).length +
              (expandedTowerMarker_m45 theta marker level).length ≤
            (theta.iterateWord (level + 1) marker).length +
              2 * (theta.iterateWord level marker).length :=
          Nat.add_le_add_left ih _
        _ ≤ (theta.iterateWord (level + 1) marker).length +
              (theta.iterateWord (level + 1) marker).length :=
          Nat.add_le_add_left hstep _
        _ = 2 * (theta.iterateWord (level + 1) marker).length := by
          omega

private def maxIterateLength_m45
    {alphabet : Type u} [Fintype alphabet]
    (source : Substitution alphabet) (level : ℕ) : ℕ :=
  Finset.univ.sup fun letter : alphabet =>
    (source.iterateLetter level letter).length

private theorem iterateLetter_length_le_maxIterateLength_m45
    {alphabet : Type u} [Fintype alphabet]
    (source : Substitution alphabet) (level : ℕ) (letter : alphabet) :
    (source.iterateLetter level letter).length ≤
      maxIterateLength_m45 source level := by
  exact Finset.le_sup
    (f := fun other : alphabet =>
      (source.iterateLetter level other).length)
    (Finset.mem_univ letter)

private theorem exists_length_eq_maxIterateLength_m45
    {alphabet : Type u} [Fintype alphabet] [Nonempty alphabet]
    (source : Substitution alphabet) (level : ℕ) :
    ∃ letter : alphabet,
      (source.iterateLetter level letter).length =
        maxIterateLength_m45 source level := by
  rcases Finset.exists_mem_eq_sup Finset.univ
      (by simpa using (Finset.univ_nonempty :
        (Finset.univ : Finset alphabet).Nonempty))
      (fun letter : alphabet =>
        (source.iterateLetter level letter).length) with
    ⟨letter, _hletter, hmax⟩
  exact ⟨letter, hmax.symm⟩

private theorem iterateWord_append_m45
    {alphabet : Type u} (source : Substitution alphabet) (level : ℕ)
    (left right : Word alphabet) :
    source.iterateWord level (left ++ right) =
      source.iterateWord level left ++ source.iterateWord level right := by
  induction level with
  | zero => rfl
  | succ level ih =>
      simp only [Substitution.iterateWord_succ, ih,
        Substitution.mapWord_append]

private theorem iterateWord_length_le_maxIterateLength_m45
    {alphabet : Type u} [Fintype alphabet]
    (source : Substitution alphabet) (level : ℕ) (letters : Word alphabet) :
    (source.iterateWord level letters).length ≤
      maxIterateLength_m45 source level * letters.length := by
  induction letters with
  | nil =>
      have hnil : source.iterateWord level [] = [] := by
        induction level with
        | zero => rfl
        | succ level ih =>
            rw [Substitution.iterateWord_succ, ih]
            rfl
      rw [hnil]
      simp
  | cons letter rest ih =>
      rw [show letter :: rest = [letter] ++ rest by rfl,
        iterateWord_append_m45, List.length_append]
      change (source.iterateLetter level letter).length +
          (source.iterateWord level rest).length ≤ _
      calc
        (source.iterateLetter level letter).length +
            (source.iterateWord level rest).length ≤
            maxIterateLength_m45 source level +
              maxIterateLength_m45 source level * rest.length :=
          Nat.add_le_add
            (iterateLetter_length_le_maxIterateLength_m45
              source level letter) ih
        _ = maxIterateLength_m45 source level * (rest.length + 1) := by
          rw [Nat.mul_succ, Nat.add_comm]

private theorem maxIterateLength_add_le_m45
    {alphabet : Type u} [Fintype alphabet]
    (source : Substitution alphabet) (base extra : ℕ) :
    maxIterateLength_m45 source (base + extra) ≤
      maxIterateLength_m45 source extra *
        maxIterateLength_m45 source base := by
  apply Finset.sup_le
  intro letter _hletter
  have hlength := iterateWord_length_le_maxIterateLength_m45 source
    extra (source.iterateLetter base letter)
  have hbase := iterateLetter_length_le_maxIterateLength_m45
    source base letter
  calc
    (source.iterateLetter (base + extra) letter).length =
        (source.iterateWord extra
          (source.iterateLetter base letter)).length := by
      change (source.iterateWord (base + extra) [letter]).length =
        (source.iterateWord extra
          (source.iterateWord base [letter])).length
      rw [Nat.add_comm, substitution_iterateWord_add]
    _ ≤ maxIterateLength_m45 source extra *
          (source.iterateLetter base letter).length := hlength
    _ ≤ maxIterateLength_m45 source extra *
          maxIterateLength_m45 source base :=
      Nat.mul_le_mul_left _ hbase

private theorem maximality_forces_previousSeed_length_lt_marker
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    (sequence : MetricDurandGammaSequence input)
    (tower : MetricDurandIteratedDecoderTower input)
    (index : ℕ) :
    (source.iterateLetter (sequence.sourcePower index - 1)
        input.seed).length <
      (tower.towerMarker (sequence.refinementPower index)).length := by
  let sourceExponent := sequence.sourcePower index
  let refinementExponent := sequence.refinementPower index
  have hsourceExponentPos : 0 < sourceExponent := by
    have hmono := sequence.sourcePower_strictMono.monotone
      (Nat.zero_le index)
    exact lt_of_lt_of_le sequence.sourcePower_zero_pos hmono
  change (source.iterateLetter (sourceExponent - 1) input.seed).length <
    (tower.towerMarker refinementExponent).length
  by_contra hnot
  have hmarkerLe : (tower.towerMarker refinementExponent).length ≤
      (source.iterateLetter (sourceExponent - 1) input.seed).length := by
    omega
  have hmarkerAtZero :
      word.take (tower.towerMarker refinementExponent).length =
        tower.towerMarker refinementExponent := by
    simpa [InfiniteFactorAt] using
      (tower.towerDecomposition refinementExponent).marker_at_zero
  have hsourcePrefix :=
    substitution_iterateLetter_eq_take_of_fixedPoint
      input.source_fixed input.seed_is_head.symm (sourceExponent - 1)
  have htakes := Stream'.take_prefix_take_left
    (a := word) (m := (tower.towerMarker refinementExponent).length)
    (n := (source.iterateLetter
      (sourceExponent - 1) input.seed).length) hmarkerLe
  rw [hmarkerAtZero, ← hsourcePrefix] at htakes
  have hbegins : ∀ candidate : Fin rank,
      tower.towerMarker refinementExponent <+:
        (source.power sourceExponent) candidate := by
    intro candidate
    exact htakes.trans
      (previousSeed_prefix_sourcePower input sourceExponent
        hsourceExponentPos candidate)
  exact sequence.refinementPower_maximal index
    (markerBegins_hasMetricTwoSidedDecoderFactorization input tower
      sourceExponent refinementExponent hsourceExponentPos hbegins)

private def sourceRatioConstant_m45
    {alphabet : Type u} [Fintype alphabet]
    (source : Substitution alphabet) (primitiveDepth : ℕ) : ℕ :=
  maxIterateLength_m45 source primitiveDepth *
    maxIterateLength_m45 source 1

private def markerRatioConstant_m45
    {alphabet : Type u} [Fintype alphabet]
    (theta : Substitution alphabet) (marker : Word alphabet) : ℕ :=
  2 * maxIterateLength_m45 theta 1 * marker.length

private def lengthRatioConstant_m45
    {alphabet : Type u} [Fintype alphabet]
    (source theta : Substitution alphabet) (marker : Word alphabet)
    (primitiveDepth : ℕ) : ℕ :=
  sourceRatioConstant_m45 source primitiveDepth *
    markerRatioConstant_m45 theta marker

private theorem lengthRatioConstant_pos_m45
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (primitiveDepth : ℕ) :
    0 < lengthRatioConstant_m45 source
      (returnDecoderSubstitutionMetric decomposition) marker primitiveDepth := by
  letI : Nonempty (Fin rank) := ⟨⟨0, input.rank_pos⟩⟩
  let theta := returnDecoderSubstitutionMetric decomposition
  have hsourceMaxPos : ∀ level : ℕ,
      0 < maxIterateLength_m45 source level := by
    intro level
    exact (List.length_pos_of_ne_nil
      (source.iterateLetter_ne_nil level input.seed)).trans_le
        (iterateLetter_length_le_maxIterateLength_m45
          source level input.seed)
  have hthetaMaxPos : ∀ level : ℕ,
      0 < maxIterateLength_m45 theta level := by
    intro level
    exact (List.length_pos_of_ne_nil
      (theta.iterateLetter_ne_nil level input.seed)).trans_le
        (iterateLetter_length_le_maxIterateLength_m45
          theta level input.seed)
  have hmarkerPos : 0 < marker.length :=
    List.length_pos_of_ne_nil decomposition.marker_ne_nil
  dsimp [lengthRatioConstant_m45, sourceRatioConstant_m45,
    markerRatioConstant_m45, theta]
  exact Nat.mul_pos
    (Nat.mul_pos (hsourceMaxPos primitiveDepth) (hsourceMaxPos 1))
    (Nat.mul_pos (Nat.mul_pos (by omega) (hthetaMaxPos 1)) hmarkerPos)

theorem metricDurandMaximalGammaSequence_has_lengthRatioControl
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    (sequence : MetricDurandGammaSequence input) :
    Nonempty (MetricDurandGammaLengthRatioControl sequence) := by
  classical
  letI : Nonempty (Fin rank) := ⟨⟨0, input.rank_pos⟩⟩
  let theta := returnDecoderSubstitutionMetric decomposition
  obtain ⟨tower⟩ := metricDurandProposition10_has_iteratedDecoderTower input
  obtain ⟨primitiveDepth, _hprimitiveDepth, hsourceContains⟩ :=
    input.source_primitive
  have hrankTwo : 2 ≤ rank := by
    by_contra hnot
    have hrankLe : rank ≤ 1 := by omega
    apply input.word_aperiodic
    refine ⟨1, by omega, ?_⟩
    intro position
    apply Fin.ext
    have hleft := (word (position + 1)).isLt
    have hright := (word position).isLt
    omega
  have hthetaImageTwo : ∀ letter : Fin rank,
      2 ≤ (theta letter).length := by
    intro letter
    let zeroLetter : Fin rank := ⟨0, input.rank_pos⟩
    let oneLetter : Fin rank := ⟨1, hrankTwo⟩
    have hzeroMem : zeroLetter ∈ theta letter := by
      simpa [theta, returnDecoderSubstitutionMetric] using
        input.decoder_contains_all letter zeroLetter
    have honeMem : oneLetter ∈ theta letter := by
      simpa [theta, returnDecoderSubstitutionMetric] using
        input.decoder_contains_all letter oneLetter
    have hne : zeroLetter ≠ oneLetter := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [zeroLetter, oneLetter] at hval
    have hsubset : ({zeroLetter, oneLetter} : Finset (Fin rank)) ⊆
        (theta letter).toFinset := by
      intro candidate hcandidate
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcandidate
      simp only [List.mem_toFinset]
      rcases hcandidate with rfl | rfl
      · exact hzeroMem
      · exact honeMem
    have hcard := Finset.card_le_card hsubset
    have hfinsetLength := List.toFinset_card_le (theta letter)
    have hpairCard :
        ({zeroLetter, oneLetter} : Finset (Fin rank)).card = 2 := by
      simp [hne]
    omega
  let minimumLetter : ℕ → Fin rank := fun index =>
    Classical.choose (Finset.exists_min_image Finset.univ
      (fun letter : Fin rank =>
        ((theta.power (sequence.refinementPower index)) letter).length)
      Finset.univ_nonempty)
  have hminimum : ∀ index letter,
      ((theta.power (sequence.refinementPower index))
          (minimumLetter index)).length ≤
        ((theta.power (sequence.refinementPower index)) letter).length := by
    intro index letter
    exact (Classical.choose_spec
      (Finset.exists_min_image Finset.univ
        (fun candidate : Fin rank =>
          ((theta.power (sequence.refinementPower index)) candidate).length)
        Finset.univ_nonempty)).2 letter (Finset.mem_univ letter)
  let sourceConstant := sourceRatioConstant_m45 source primitiveDepth
  let markerConstant := markerRatioConstant_m45 theta marker
  let ratioBound := lengthRatioConstant_m45 source theta marker primitiveDepth
  have hratioBoundPos : 0 < ratioBound := by
    simpa [ratioBound, theta] using
      lengthRatioConstant_pos_m45 input primitiveDepth
  refine ⟨{
    ratioBound := ratioBound
    ratioBound_pos := hratioBoundPos
    minimumLetter := minimumLetter
    minimumLetter_is_minimum := ?_
    source_image_length_le := ?_ }⟩
  · intro index letter
    simpa [theta] using hminimum index letter
  · intro index letter
    let sourceExponent := sequence.sourcePower index
    let refinementExponent := sequence.refinementPower index
    have hsourceExponentPos : 0 < sourceExponent := by
      have hmono := sequence.sourcePower_strictMono.monotone
        (Nat.zero_le index)
      exact lt_of_lt_of_le sequence.sourcePower_zero_pos hmono
    have hrefinementExponentPos : 0 < refinementExponent := by
      have hmono := sequence.refinementPower_strictMono.monotone
        (Nat.zero_le index)
      dsimp [refinementExponent]
      exact lt_of_lt_of_le sequence.refinementPower_zero_pos hmono
    have hpreviousSeedLtMarker :
        (source.iterateLetter (sourceExponent - 1) input.seed).length <
          (tower.towerMarker refinementExponent).length := by
      simpa [sourceExponent, refinementExponent] using
        maximality_forces_previousSeed_length_lt_marker sequence tower index
    obtain ⟨sourceDepth, hsourceExponentEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsourceExponentPos)
    obtain ⟨maxSourceLetter, hmaxSourceLetter⟩ :=
      exists_length_eq_maxIterateLength_m45 source sourceDepth
    have hmaxSourceInfix := substitution_iterateLetter_infix_of_mem_iterate
      source (later := sourceDepth)
      (hsourceContains input.seed maxSourceLetter)
    have hdeeperSourceLength :
        (source.iterateLetter (sourceDepth + primitiveDepth)
          input.seed).length ≤
          maxIterateLength_m45 source primitiveDepth *
            (source.iterateLetter sourceDepth input.seed).length := by
      have hbound := iterateWord_length_le_maxIterateLength_m45 source
        primitiveDepth (source.iterateLetter sourceDepth input.seed)
      calc
        (source.iterateLetter (sourceDepth + primitiveDepth)
              input.seed).length =
            (source.iterateWord primitiveDepth
              (source.iterateLetter sourceDepth input.seed)).length := by
          change (source.iterateWord (sourceDepth + primitiveDepth)
              [input.seed]).length = _
          rw [Nat.add_comm, substitution_iterateWord_add]
          rfl
        _ ≤ maxIterateLength_m45 source primitiveDepth *
              (source.iterateLetter sourceDepth input.seed).length := hbound
    have hmaxSourceDepth : maxIterateLength_m45 source sourceDepth ≤
        maxIterateLength_m45 source primitiveDepth *
          (source.iterateLetter sourceDepth input.seed).length := by
      calc
        maxIterateLength_m45 source sourceDepth =
            (source.iterateLetter sourceDepth maxSourceLetter).length :=
          hmaxSourceLetter.symm
        _ ≤ (source.iterateLetter
              (sourceDepth + primitiveDepth) input.seed).length :=
          hmaxSourceInfix.length_le
        _ ≤ maxIterateLength_m45 source primitiveDepth *
              (source.iterateLetter sourceDepth input.seed).length :=
          hdeeperSourceLength
    have hsourceImageRewrite :
        (source.power sourceExponent) letter =
          source.iterateWord sourceDepth (source letter) := by
      rw [hsourceExponentEq, Substitution.power_apply]
      change source.iterateWord (sourceDepth + 1) [letter] = _
      rw [substitution_iterateWord_add]
      simp [Substitution.iterateWord]
    have hsourceOne : (source letter).length ≤
        maxIterateLength_m45 source 1 := by
      simpa [Substitution.iterateLetter,
        Substitution.iterateWord] using
        iterateLetter_length_le_maxIterateLength_m45 source 1 letter
    have hsourceImagePrevious :
        ((source.power sourceExponent) letter).length ≤
          sourceConstant *
            (source.iterateLetter sourceDepth input.seed).length := by
      rw [hsourceImageRewrite]
      calc
        (source.iterateWord sourceDepth (source letter)).length ≤
            maxIterateLength_m45 source sourceDepth *
              (source letter).length :=
          iterateWord_length_le_maxIterateLength_m45 source
            sourceDepth (source letter)
        _ ≤ (maxIterateLength_m45 source primitiveDepth *
              (source.iterateLetter sourceDepth input.seed).length) *
                maxIterateLength_m45 source 1 :=
          Nat.mul_le_mul hmaxSourceDepth hsourceOne
        _ = sourceConstant *
              (source.iterateLetter sourceDepth input.seed).length := by
          simp only [sourceConstant, sourceRatioConstant_m45, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm]
    have hpreviousSeedLtMarker' :
        (source.iterateLetter sourceDepth input.seed).length <
          (tower.towerMarker refinementExponent).length := by
      simpa [hsourceExponentEq] using hpreviousSeedLtMarker
    have hmarkerExpanded :
        (tower.towerMarker refinementExponent).length ≤
          2 * (theta.iterateWord refinementExponent marker).length := by
      rw [towerMarker_eq_expanded_m45 input tower refinementExponent]
      exact expandedTowerMarker_length_le_m45 theta marker hthetaImageTwo
        refinementExponent
    obtain ⟨previousRefinement, hrefinementExponentEq⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hrefinementExponentPos)
    obtain ⟨maxThetaLetter, hmaxThetaLetter⟩ :=
      exists_length_eq_maxIterateLength_m45 theta previousRefinement
    have hmaxThetaMem : maxThetaLetter ∈
        theta.iterateLetter 1 (minimumLetter index) := by
      simpa [theta, Substitution.iterateLetter,
        Substitution.iterateWord, returnDecoderSubstitutionMetric] using
        input.decoder_contains_all (minimumLetter index) maxThetaLetter
    have hmaxThetaInfix := substitution_iterateLetter_infix_of_mem_iterate
      theta (later := previousRefinement) hmaxThetaMem
    have hmaxPreviousLeMinimum :
        maxIterateLength_m45 theta previousRefinement ≤
          ((theta.power refinementExponent) (minimumLetter index)).length := by
      calc
        maxIterateLength_m45 theta previousRefinement =
            (theta.iterateLetter previousRefinement maxThetaLetter).length :=
          hmaxThetaLetter.symm
        _ ≤ (theta.iterateLetter
              (previousRefinement + 1) (minimumLetter index)).length :=
          hmaxThetaInfix.length_le
        _ = ((theta.power refinementExponent)
              (minimumLetter index)).length := by
          rw [hrefinementExponentEq]
          simp [Substitution.power_apply]
    have hmaxCurrentLeMinimum :
        maxIterateLength_m45 theta refinementExponent ≤
          maxIterateLength_m45 theta 1 *
            ((theta.power refinementExponent)
              (minimumLetter index)).length := by
      rw [hrefinementExponentEq] at hmaxPreviousLeMinimum ⊢
      exact (maxIterateLength_add_le_m45 theta previousRefinement 1).trans
        (Nat.mul_le_mul_left _ hmaxPreviousLeMinimum)
    have hmarkerMinimum : (tower.towerMarker refinementExponent).length ≤
        markerConstant *
          ((theta.power refinementExponent) (minimumLetter index)).length := by
      have hterm := iterateWord_length_le_maxIterateLength_m45 theta
        refinementExponent marker
      calc
        (tower.towerMarker refinementExponent).length ≤
            2 * (theta.iterateWord refinementExponent marker).length :=
          hmarkerExpanded
        _ ≤ 2 * (maxIterateLength_m45 theta refinementExponent *
              marker.length) := Nat.mul_le_mul_left 2 hterm
        _ ≤ 2 * ((maxIterateLength_m45 theta 1 *
              ((theta.power refinementExponent)
                (minimumLetter index)).length) * marker.length) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_right marker.length hmaxCurrentLeMinimum)
        _ = markerConstant *
              ((theta.power refinementExponent)
                (minimumLetter index)).length := by
          simp only [markerConstant, markerRatioConstant_m45, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm]
    change ((source.power sourceExponent) letter).length ≤
      ratioBound *
        ((theta.power refinementExponent) (minimumLetter index)).length
    calc
      ((source.power sourceExponent) letter).length ≤
          sourceConstant *
            (source.iterateLetter sourceDepth input.seed).length :=
        hsourceImagePrevious
      _ ≤ sourceConstant *
            (tower.towerMarker refinementExponent).length :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hpreviousSeedLtMarker')
      _ ≤ sourceConstant *
            (markerConstant *
              ((theta.power refinementExponent)
                (minimumLetter index)).length) :=
        Nat.mul_le_mul_left _ hmarkerMinimum
      _ = ratioBound *
            ((theta.power refinementExponent)
              (minimumLetter index)).length := by
        simp [ratioBound, lengthRatioConstant_m45, sourceConstant,
          markerConstant, Nat.mul_assoc]

structure MetricDurandGammaUniformBounds
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    (sequence : MetricDurandGammaSequence input) where
  imageLengthBound : ℕ
  imageLengthBound_pos : 0 < imageLengthBound
  image_length_le : ∀ index letter,
    (sequence.gammaAt index letter).length ≤ imageLengthBound

/-- Decoding a finite word is at least its number of letters times the
length of a shortest decoder image. -/
private theorem minimumImage_mul_length_le_mapWord
    {alphabet : Type*} (substitution : Substitution alphabet)
    (minimumLetter : alphabet)
    (hminimum : ∀ letter,
      (substitution minimumLetter).length ≤
        (substitution letter).length)
    (finiteWord : Word alphabet) :
    (substitution minimumLetter).length * finiteWord.length ≤
      (substitution.mapWord finiteWord).length := by
  induction finiteWord with
  | nil => simp
  | cons letter tail ih =>
      rw [Substitution.mapWord_cons, List.length_append,
        List.length_cons]
      calc
        (substitution minimumLetter).length * (tail.length + 1) =
            (substitution minimumLetter).length +
              (substitution minimumLetter).length * tail.length := by
          rw [Nat.mul_succ, Nat.add_comm]
        _ ≤ (substitution letter).length +
              (substitution.mapWord tail).length :=
          Nat.add_le_add (hminimum letter) ih

theorem metricDurandGammaSequence_has_uniformBounds
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    (sequence : MetricDurandGammaSequence input) :
    Nonempty (MetricDurandGammaUniformBounds sequence) := by
  classical
  obtain ⟨ratio⟩ :=
    metricDurandMaximalGammaSequence_has_lengthRatioControl sequence
  refine ⟨{
    imageLengthBound := ratio.ratioBound
    imageLengthBound_pos := ratio.ratioBound_pos
    image_length_le := ?_ }⟩
  intro index letter
  let decoder :=
    (returnDecoderSubstitutionMetric decomposition).power
      (sequence.refinementPower index)
  let shortest := ratio.minimumLetter index
  let shortestLength := (decoder shortest).length
  have hshortest : ∀ candidate : Fin rank,
      shortestLength ≤ (decoder candidate).length := by
    intro candidate
    exact ratio.minimumLetter_is_minimum index candidate
  have hshortestPos : 0 < shortestLength := by
    exact List.length_pos_of_ne_nil (decoder.image_ne_nil shortest)
  have hdecodedLower :
      shortestLength * (sequence.gammaAt index letter).length ≤
        (decoder.mapWord (sequence.gammaAt index letter)).length :=
    minimumImage_mul_length_le_mapWord decoder shortest hshortest
      (sequence.gammaAt index letter)
  have hdecodedEq :
      decoder.mapWord (sequence.gammaAt index letter) =
        (source.power (sequence.sourcePower index)) letter := by
    have heq := congrArg
      (fun substitution : Substitution (Fin rank) =>
        substitution letter)
      (sequence.theta_comp_gammaAt index)
    exact heq
  have hcancel : shortestLength *
        (sequence.gammaAt index letter).length ≤
      shortestLength * ratio.ratioBound := by
    calc
      shortestLength * (sequence.gammaAt index letter).length ≤
          (decoder.mapWord (sequence.gammaAt index letter)).length :=
        hdecodedLower
      _ = ((source.power (sequence.sourcePower index)) letter).length := by
        rw [hdecodedEq]
      _ ≤ ratio.ratioBound * shortestLength :=
        ratio.source_image_length_le index letter
      _ = shortestLength * ratio.ratioBound := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_left hcancel hshortestPos

structure MetricDurandFiniteGammaCoding
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    {sequence : MetricDurandGammaSequence input}
    (_bounds : MetricDurandGammaUniformBounds sequence) where
  codeCount : ℕ
  codeCount_pos : 0 < codeCount
  code : ℕ → Fin codeCount
  same_code : ∀ left right, code left = code right →
    sequence.gammaAt left = sequence.gammaAt right

/-- Two substitutions are equal when all letter images agree. -/
private theorem substitution_ext_of_images_eq_m4
    {alphabet : Type*} (left right : Substitution alphabet)
    (himages : ∀ letter, left letter = right letter) :
    left = right := by
  cases left with
  | mk leftImage leftNonempty =>
      cases right with
      | mk rightImage rightNonempty =>
          have himage : leftImage = rightImage := by
            funext letter
            exact himages letter
          subst rightImage
          rfl

/-- A word of bounded length is determined by its bounded table of optional
entries. -/
private theorem word_eq_of_bounded_getElem?_eq_m4
    {alphabet : Type*} {bound : ℕ} {left right : Word alphabet}
    (hleft : left.length ≤ bound) (hright : right.length ≤ bound)
    (htable : ∀ position : Fin bound,
      left[position.1]? = right[position.1]?) :
    left = right := by
  apply List.ext_getElem?
  intro position
  by_cases hposition : position < bound
  · exact htable ⟨position, hposition⟩
  · have hleftOut : left[position]? = none := by
      exact List.getElem?_eq_none (by omega)
    have hrightOut : right[position]? = none := by
      exact List.getElem?_eq_none (by omega)
    rw [hleftOut, hrightOut]

theorem metricDurandGammaBounds_have_finiteCoding
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    {sequence : MetricDurandGammaSequence input}
    (bounds : MetricDurandGammaUniformBounds sequence) :
    Nonempty (MetricDurandFiniteGammaCoding bounds) := by
  classical
  let codeType := Fin rank → Fin bounds.imageLengthBound → Option (Fin rank)
  let encode : ℕ → codeType := fun index letter position ↦
    (sequence.gammaAt index letter)[position.1]?
  let codeEquiv := Fintype.equivFin codeType
  let code : ℕ → Fin (Fintype.card codeType) := fun index ↦
    codeEquiv (encode index)
  have hcard : 0 < Fintype.card codeType := by
    letI : Nonempty codeType := ⟨fun _ _ ↦ none⟩
    exact Fintype.card_pos
  refine ⟨{
    codeCount := Fintype.card codeType
    codeCount_pos := hcard
    code := code
    same_code := ?_ }⟩
  intro left right hcode
  have hencoded : encode left = encode right := by
    apply codeEquiv.injective
    exact hcode
  apply substitution_ext_of_images_eq_m4
  intro letter
  apply word_eq_of_bounded_getElem?_eq_m4
      (bounds.image_length_le left letter)
      (bounds.image_length_le right letter)
  intro position
  exact congrFun (congrFun hencoded letter) position

structure MetricDurandConstantGammaSubsequence
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    {sequence : MetricDurandGammaSequence input}
    {bounds : MetricDurandGammaUniformBounds sequence}
    (_coding : MetricDurandFiniteGammaCoding bounds) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  gamma : Substitution (Fin rank)
  gamma_eq : ∀ stage, sequence.gammaAt (index stage) = gamma

/-- An infinite subset of naturals admits a strictly increasing sequence in
that subset. -/
private theorem infiniteSet_exists_strictMono_mem_m4
    {set : Set ℕ} (hset : set.Infinite) :
    ∃ index : ℕ → ℕ, StrictMono index ∧ ∀ stage, index stage ∈ set := by
  let start : ℕ := Classical.choose hset.nonempty
  let next : ℕ → ℕ := fun previous ↦
    Classical.choose (hset.exists_gt previous)
  have hstartMem : start ∈ set :=
    Classical.choose_spec hset.nonempty
  have hnextMem : ∀ previous, next previous ∈ set := fun previous ↦
    (Classical.choose_spec (hset.exists_gt previous)).1
  have hnextGt : ∀ previous, previous < next previous := fun previous ↦
    (Classical.choose_spec (hset.exists_gt previous)).2
  let index : ℕ → ℕ := fun stage ↦
    Nat.rec start (fun _ previous ↦ next previous) stage
  have hindexMem : ∀ stage, index stage ∈ set := by
    intro stage
    induction stage with
    | zero => exact hstartMem
    | succ stage ih =>
        change next (index stage) ∈ set
        exact hnextMem (index stage)
  have hindexStrict : StrictMono index := by
    apply strictMono_nat_of_lt_succ
    intro stage
    change index stage < next (index stage)
    exact hnextGt (index stage)
  exact ⟨index, hindexStrict, hindexMem⟩

/-- A map from naturals to a finite nonempty type has an infinite fibre. -/
private theorem exists_infinite_fiber_m4
    {codeType : Type*} [Fintype codeType] [Nonempty codeType]
    (code : ℕ → codeType) :
    ∃ value, {index | code index = value}.Infinite := by
  let fiber : codeType → Set ℕ := fun value ↦
    {index | code index = value}
  have hcover : (⋃ value, fiber value) = Set.univ := by
    ext index
    simp [fiber]
  by_contra hnone
  have hfinite : ∀ value, (fiber value).Finite := by
    intro value
    by_contra hinfinite
    exact hnone ⟨value, hinfinite⟩
  have hfiniteUnion : (⋃ value, fiber value).Finite :=
    Set.finite_iUnion hfinite
  rw [hcover] at hfiniteUnion
  exact Set.infinite_univ hfiniteUnion

theorem metricDurandFiniteGammaCoding_has_constantSubsequence
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    {sequence : MetricDurandGammaSequence input}
    {bounds : MetricDurandGammaUniformBounds sequence}
    (coding : MetricDurandFiniteGammaCoding bounds) :
    Nonempty (MetricDurandConstantGammaSubsequence coding) := by
  classical
  let fiber : Fin coding.codeCount → Set ℕ := fun value ↦
    {index | coding.code index = value}
  letI : Nonempty (Fin coding.codeCount) :=
    Fin.pos_iff_nonempty.mp coding.codeCount_pos
  obtain ⟨value, hvalueInfinite⟩ := exists_infinite_fiber_m4 coding.code
  obtain ⟨index, hindexStrict, hindexMem⟩ :=
    infiniteSet_exists_strictMono_mem_m4 hvalueInfinite
  let gamma := sequence.gammaAt (index 0)
  have hgamma : ∀ stage, sequence.gammaAt (index stage) = gamma := by
    intro stage
    apply coding.same_code
    exact (hindexMem stage).trans (hindexMem 0).symm
  exact ⟨{
    index := index
    index_strictMono := hindexStrict
    gamma := gamma
    gamma_eq := hgamma }⟩

/-- M4 aggregator (Durand Proposition 10). -/
theorem metricDurandProposition10_powerEquationFamily
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) :
    Nonempty (MetricDurandPowerEquationFamily input) := by
  obtain ⟨sequence⟩ := metricDurandProposition10_constructGammaSequence input
  obtain ⟨bounds⟩ := metricDurandGammaSequence_has_uniformBounds sequence
  obtain ⟨coding⟩ := metricDurandGammaBounds_have_finiteCoding bounds
  obtain ⟨constant⟩ :=
    metricDurandFiniteGammaCoding_has_constantSubsequence coding
  refine ⟨{
    sourcePower := fun stage ↦ sequence.sourcePower (constant.index stage)
    sourcePower_strictMono :=
      sequence.sourcePower_strictMono.comp constant.index_strictMono
    sourcePower_zero_pos := sequence.sourcePower_zero_pos.trans_le
      (sequence.sourcePower_strictMono.monotone
        (Nat.zero_le (constant.index 0)))
    refinementPower := fun stage ↦
      sequence.refinementPower (constant.index stage)
    refinementPower_strictMono :=
      sequence.refinementPower_strictMono.comp constant.index_strictMono
    refinementPower_zero_pos := sequence.refinementPower_zero_pos.trans_le
      (sequence.refinementPower_strictMono.monotone
        (Nat.zero_le (constant.index 0)))
    gamma := constant.gamma
    theta_comp_gamma := ?_
    gamma_comp_theta := ?_ }⟩
  · intro stage
    rw [← constant.gamma_eq stage]
    exact sequence.theta_comp_gammaAt (constant.index stage)
  · intro stage
    rw [← constant.gamma_eq stage]
    exact sequence.gammaAt_comp_theta (constant.index stage)

/-! ## M5: exact-metric replacement for the spectral comparison -/

structure MetricDurandPowerEquationDifference
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    (equations : MetricDurandPowerEquationFamily input) where
  earlierIndex : ℕ
  laterIndex : ℕ
  index_lt : earlierIndex < laterIndex
  sourceDifference : ℕ
  sourceDifference_pos : 0 < sourceDifference
  sourceDifference_eq : sourceDifference =
    equations.sourcePower laterIndex - equations.sourcePower earlierIndex
  refinementDifference : ℕ
  refinementDifference_pos : 0 < refinementDifference
  refinementDifference_eq : refinementDifference =
    equations.refinementPower laterIndex -
      equations.refinementPower earlierIndex

theorem metricDurandPowerEquationFamily_has_positiveDifference
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    (equations : MetricDurandPowerEquationFamily input) :
    Nonempty (MetricDurandPowerEquationDifference equations) := by
  exact ⟨{
    earlierIndex := 0
    laterIndex := 1
    index_lt := by omega
    sourceDifference := equations.sourcePower 1 - equations.sourcePower 0
    sourceDifference_pos := Nat.sub_pos_of_lt
      (equations.sourcePower_strictMono (by omega))
    sourceDifference_eq := rfl
    refinementDifference :=
      equations.refinementPower 1 - equations.refinementPower 0
    refinementDifference_pos := Nat.sub_pos_of_lt
      (equations.refinementPower_strictMono (by omega))
    refinementDifference_eq := rfl }⟩

/-- The metric of a decoder image, measured in a metric on the return
alphabet. -/
def metricDecoderImageMetric
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank)
    (metric : Fin rank → ℝ) : Fin rank → ℝ :=
  fun letter => wordMetricLength metric
    (returnDecoderSubstitutionMetric decomposition letter)

private theorem wordMetricLength_smul_m5
    {α : Type u} (scalar : ℝ) (metric : α → ℝ) (letters : Word α) :
    wordMetricLength (fun letter => scalar * metric letter) letters =
      scalar * wordMetricLength metric letters := by
  induction letters with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      change scalar * metric head +
          wordMetricLength (fun letter => scalar * metric letter) tail =
        scalar * (metric head + wordMetricLength metric tail)
      rw [ih]
      ring

private theorem wordMetricLength_mono_m5
    {α : Type u} {leftMetric rightMetric : α → ℝ}
    (hle : ∀ letter, leftMetric letter ≤ rightMetric letter)
    (letters : Word α) :
    wordMetricLength leftMetric letters ≤
      wordMetricLength rightMetric letters := by
  induction letters with
  | nil => simp [wordMetricLength]
  | cons head tail ih =>
      change leftMetric head + wordMetricLength leftMetric tail ≤
        rightMetric head + wordMetricLength rightMetric tail
      exact add_le_add (hle head) ih

private theorem wordMetricLength_lt_of_pointwise_le_of_mem_lt_m5
    {α : Type u} {leftMetric rightMetric : α → ℝ}
    (hle : ∀ letter, leftMetric letter ≤ rightMetric letter)
    {strictLetter : α} {letters : Word α}
    (hmem : strictLetter ∈ letters)
    (hstrict : leftMetric strictLetter < rightMetric strictLetter) :
    wordMetricLength leftMetric letters <
      wordMetricLength rightMetric letters := by
  induction letters with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      change leftMetric head + wordMetricLength leftMetric tail <
        rightMetric head + wordMetricLength rightMetric tail
      rcases hmem with rfl | htail
      · linarith [wordMetricLength_mono_m5 hle tail]
      · linarith [ih htail, hle head]

/-- M5m.1: the exact induced-factorization identity says that the return
decoder and the self-derived source commute on every letter image. -/
theorem metricDecoder_commutes_with_source_on_letters
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition) :
    ∀ letter,
      (returnDecoderSubstitutionMetric decomposition).mapWord
          (source letter) =
        source.mapWord (returnDecoderSubstitutionMetric decomposition letter) := by
  intro letter
  have hfactorImage : input.induced.factor letter = source letter := by
    change input.induced.substitution letter = source letter
    rw [input.induced_eq]
  change (source letter).flatMap decomposition.blocks =
    source.mapWord (decomposition.blocks letter)
  rw [← hfactorImage]
  exact input.induced.factor_decodes letter

/-- M5m.2: nonempty decoder images have positive length in every positive
letter metric. -/
theorem metricDecoderImageMetric_pos
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank)
    (metric : Fin rank → ℝ) (hmetric : ∀ letter, 0 < metric letter) :
    ∀ letter, 0 < metricDecoderImageMetric decomposition metric letter := by
  intro letter
  exact wordMetricLength_pos_of_ne_nil metric hmetric
    ((returnDecoderSubstitutionMetric decomposition).image_ne_nil letter)

/-- M5m.3: commutation transports a source scaling law to the metric of
decoder images. -/
theorem metricDecoderImageMetric_scales_source
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    {metric : Fin rank → ℝ} {sourceScale : ℝ}
    (hsourceScales :
      SubstitutionScalesLetterLengths source metric sourceScale) :
    SubstitutionScalesLetterLengths source
      (metricDecoderImageMetric decomposition metric) sourceScale := by
  intro letter
  calc
    wordMetricLength (metricDecoderImageMetric decomposition metric)
        (source letter) =
      wordMetricLength metric
        ((source letter).flatMap
          (returnDecoderSubstitutionMetric decomposition)) :=
      wordMetricLength_flatMap metric
        (returnDecoderSubstitutionMetric decomposition) (source letter)
    _ = wordMetricLength metric
        ((returnDecoderSubstitutionMetric decomposition).mapWord
          (source letter)) := rfl
    _ = wordMetricLength metric
        (source.mapWord
          (returnDecoderSubstitutionMetric decomposition letter)) := by
      rw [metricDecoder_commutes_with_source_on_letters input]
    _ = sourceScale * wordMetricLength metric
        (returnDecoderSubstitutionMetric decomposition letter) :=
      wordMetricLength_mapWord_of_scales hsourceScales _
    _ = sourceScale *
        metricDecoderImageMetric decomposition metric letter := rfl

/-- M5m.4: two strictly positive metrics scaled by one primitive
substitution at the same scale are proportional. -/
theorem primitive_positive_sameScale_metrics_proportional
    {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (source : Substitution β) (hprimitive : IsPrimitiveSubstitution source)
    {leftMetric rightMetric : β → ℝ} {scale : ℝ}
    (hleftMetric : ∀ letter, 0 < leftMetric letter)
    (hrightMetric : ∀ letter, 0 < rightMetric letter)
    (hleftScales :
      SubstitutionScalesLetterLengths source leftMetric scale)
    (hrightScales :
      SubstitutionScalesLetterLengths source rightMetric scale) :
    ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ letter, rightMetric letter = coefficient * leftMetric letter := by
  classical
  obtain ⟨depth, _hdepthPositive, hcontains⟩ := hprimitive
  obtain ⟨pivot, _hpivotMem, hpivotMax⟩ :=
    Finset.univ.exists_max_image
      (fun letter => rightMetric letter / leftMetric letter)
      Finset.univ_nonempty
  let coefficient : ℝ := rightMetric pivot / leftMetric pivot
  have hcoefficientPositive : 0 < coefficient :=
    div_pos (hrightMetric pivot) (hleftMetric pivot)
  have hpointwise : ∀ letter,
      rightMetric letter ≤ coefficient * leftMetric letter := by
    intro letter
    exact (div_le_iff₀ (hleftMetric letter)).mp
      (hpivotMax letter (Finset.mem_univ letter))
  have hpivot :
      rightMetric pivot = coefficient * leftMetric pivot := by
    simp only [coefficient]
    field_simp [(ne_of_gt (hleftMetric pivot))]
  have hleftPower := scalesLetterLengths_power
    hleftScales depth pivot
  have hrightPower := scalesLetterLengths_power
    hrightScales depth pivot
  simp only [Substitution.power_apply] at hleftPower hrightPower
  refine ⟨coefficient, hcoefficientPositive, ?_⟩
  intro letter
  apply le_antisymm (hpointwise letter)
  by_contra hnot
  have hstrict :
      rightMetric letter < coefficient * leftMetric letter :=
    lt_of_not_ge hnot
  have hwordStrict :
      wordMetricLength rightMetric (source.iterateLetter depth pivot) <
        wordMetricLength (fun other => coefficient * leftMetric other)
          (source.iterateLetter depth pivot) :=
    wordMetricLength_lt_of_pointwise_le_of_mem_lt_m5
      hpointwise (hcontains pivot letter) hstrict
  have hwordEqual :
      wordMetricLength rightMetric (source.iterateLetter depth pivot) =
        wordMetricLength (fun other => coefficient * leftMetric other)
          (source.iterateLetter depth pivot) := by
    rw [hrightPower, wordMetricLength_smul_m5, hleftPower, hpivot]
    ring
  exact (ne_of_lt hwordStrict) hwordEqual

/-- A positive metric scale for the common return decoder. -/
structure MetricDecoderScaleData
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank)
    (metric : Fin rank → ℝ) where
  scale : ℝ
  scale_gt_one : 1 < scale
  scales : SubstitutionScalesLetterLengths
    (returnDecoderSubstitutionMetric decomposition) metric scale

/-- M5m.5: primitive same-scale proportionality turns the decoder-image
metric into an actual positive decoder scaling law. -/
theorem metricDurandInput_has_decoderScale
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    (input : MetricDurandProposition10Input word source decomposition)
    (metric : Fin rank → ℝ) (sourceScale : ℝ)
    (hmetric : ∀ letter, 0 < metric letter)
    (hsourceScales :
      SubstitutionScalesLetterLengths source metric sourceScale) :
    Nonempty (MetricDecoderScaleData decomposition metric) := by
  letI : Nonempty (Fin rank) := ⟨⟨0, input.rank_pos⟩⟩
  have hdecoderMetricPos : ∀ letter,
      0 < metricDecoderImageMetric decomposition metric letter :=
    metricDecoderImageMetric_pos decomposition metric hmetric
  have hdecoderMetricScales : SubstitutionScalesLetterLengths source
      (metricDecoderImageMetric decomposition metric) sourceScale :=
    metricDecoderImageMetric_scales_source input hsourceScales
  obtain ⟨decoderScale, hdecoderScalePos, hdecoderScales⟩ :=
    primitive_positive_sameScale_metrics_proportional source
      input.source_primitive hmetric hdecoderMetricPos hsourceScales
      hdecoderMetricScales
  have hscales : SubstitutionScalesLetterLengths
      (returnDecoderSubstitutionMetric decomposition) metric decoderScale := by
    intro letter
    exact hdecoderScales letter
  have hscale_gt_one : 1 < decoderScale := by
    obtain ⟨tail, htailNonempty, himage⟩ := input.decoder_prolongable
    have htailPos : 0 < wordMetricLength metric tail :=
      wordMetricLength_pos_of_ne_nil metric hmetric htailNonempty
    have hseedScale := hscales input.seed
    rw [himage] at hseedScale
    change metric input.seed + wordMetricLength metric tail =
      decoderScale * metric input.seed at hseedScale
    nlinarith [hmetric input.seed]
  exact ⟨{
    scale := decoderScale
    scale_gt_one := hscale_gt_one
    scales := hscales }⟩

/-- M5m.6: two positive metrics for the same decoder give the same positive
decoder scale. -/
theorem metricDecoderScaleData_scale_eq
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {leftMetric rightMetric : Fin rank → ℝ}
    (hleftMetric : ∀ letter, 0 < leftMetric letter)
    (hrightMetric : ∀ letter, 0 < rightMetric letter)
    (left : MetricDecoderScaleData decomposition leftMetric)
    (right : MetricDecoderScaleData decomposition rightMetric) :
    left.scale = right.scale := by
  classical
  letI : Nonempty (Fin rank) := ⟨⟨0, decomposition.rank_pos⟩⟩
  have scale_le_scale
      (firstMetric secondMetric : Fin rank → ℝ)
      (hfirstMetric : ∀ letter, 0 < firstMetric letter)
      (hsecondMetric : ∀ letter, 0 < secondMetric letter)
      (first : MetricDecoderScaleData decomposition firstMetric)
      (second : MetricDecoderScaleData decomposition secondMetric) :
      second.scale ≤ first.scale := by
    obtain ⟨pivot, _hpivotMem, hpivotMax⟩ :=
      Finset.univ.exists_max_image
        (fun letter => secondMetric letter / firstMetric letter)
        Finset.univ_nonempty
    let coefficient : ℝ := secondMetric pivot / firstMetric pivot
    have hcoefficientPos : 0 < coefficient :=
      div_pos (hsecondMetric pivot) (hfirstMetric pivot)
    have hpointwise : ∀ letter,
        secondMetric letter ≤ coefficient * firstMetric letter := by
      intro letter
      exact (div_le_iff₀ (hfirstMetric letter)).mp
        (hpivotMax letter (Finset.mem_univ letter))
    have hpivot :
        secondMetric pivot = coefficient * firstMetric pivot := by
      simp only [coefficient]
      field_simp [(ne_of_gt (hfirstMetric pivot))]
    have hwordLe := wordMetricLength_mono_m5 hpointwise
      (returnDecoderSubstitutionMetric decomposition pivot)
    rw [second.scales pivot,
      wordMetricLength_smul_m5, first.scales pivot, hpivot] at hwordLe
    have hfactorPos : 0 < coefficient * firstMetric pivot :=
      mul_pos hcoefficientPos (hfirstMetric pivot)
    have hwordLe' :
        second.scale * (coefficient * firstMetric pivot) ≤
          first.scale * (coefficient * firstMetric pivot) := by
      calc
        second.scale * (coefficient * firstMetric pivot) ≤
            coefficient * (first.scale * firstMetric pivot) := hwordLe
        _ = first.scale * (coefficient * firstMetric pivot) := by ring
    nlinarith
  apply le_antisymm
  · exact scale_le_scale rightMetric leftMetric hrightMetric hleftMetric
      right left
  · exact scale_le_scale leftMetric rightMetric hleftMetric hrightMetric
      left right

/-- M5m.7: subtracting two exact `Theta^l gamma = source^p` equations
eliminates the fixed auxiliary substitution in any positive exact metric. -/
theorem metricDurandPowerEquationDifference_has_metricGrowthIdentity
    {rank : ℕ} {word : InfiniteWord (Fin rank)}
    {source : Substitution (Fin rank)} {marker : Word (Fin rank)}
    {decomposition : ReturnDecomposition word marker rank}
    {input : MetricDurandProposition10Input word source decomposition}
    {equations : MetricDurandPowerEquationFamily input}
    (difference : MetricDurandPowerEquationDifference equations)
    (metric : Fin rank → ℝ) (hmetric : ∀ letter, 0 < metric letter)
    (sourceScale decoderScale : ℝ)
    (hsourceScale : 0 < sourceScale) (hdecoderScale : 0 < decoderScale)
    (hsourceScales :
      SubstitutionScalesLetterLengths source metric sourceScale)
    (hdecoderScales : SubstitutionScalesLetterLengths
      (returnDecoderSubstitutionMetric decomposition) metric decoderScale) :
    sourceScale ^ difference.sourceDifference =
      decoderScale ^ difference.refinementDifference := by
  let decoder := returnDecoderSubstitutionMetric decomposition
  have equationMetric (index : ℕ) (letter : Fin rank) :
      decoderScale ^ equations.refinementPower index *
          wordMetricLength metric (equations.gamma letter) =
        sourceScale ^ equations.sourcePower index * metric letter := by
    have hdecoderPower := scalesLetterLengths_power
      hdecoderScales (equations.refinementPower index)
    have hsourcePower := scalesLetterLengths_power
      hsourceScales (equations.sourcePower index)
    calc
      decoderScale ^ equations.refinementPower index *
          wordMetricLength metric (equations.gamma letter) =
        wordMetricLength metric
          ((decoder.power (equations.refinementPower index)).mapWord
            (equations.gamma letter)) :=
        (wordMetricLength_mapWord_of_scales hdecoderPower _).symm
      _ = wordMetricLength metric
          (((decoder.power (equations.refinementPower index)).comp
            equations.gamma) letter) := rfl
      _ = wordMetricLength metric
          ((source.power (equations.sourcePower index)) letter) := by
        rw [equations.theta_comp_gamma]
      _ = sourceScale ^ equations.sourcePower index * metric letter :=
        hsourcePower letter
  let letter : Fin rank := ⟨0, input.rank_pos⟩
  let gammaMetric := wordMetricLength metric (equations.gamma letter)
  have hgammaMetric : 0 < gammaMetric :=
    wordMetricLength_pos_of_ne_nil metric hmetric
      (equations.gamma.image_ne_nil letter)
  have hearlier := equationMetric difference.earlierIndex letter
  have hlater := equationMetric difference.laterIndex letter
  have hsourceLt :
      equations.sourcePower difference.earlierIndex <
        equations.sourcePower difference.laterIndex :=
    equations.sourcePower_strictMono difference.index_lt
  have hrefinementLt :
      equations.refinementPower difference.earlierIndex <
        equations.refinementPower difference.laterIndex :=
    equations.refinementPower_strictMono difference.index_lt
  have hsourceAdd :
      equations.sourcePower difference.earlierIndex +
          difference.sourceDifference =
        equations.sourcePower difference.laterIndex := by
    rw [difference.sourceDifference_eq]
    omega
  have hrefinementAdd :
      equations.refinementPower difference.earlierIndex +
          difference.refinementDifference =
        equations.refinementPower difference.laterIndex := by
    rw [difference.refinementDifference_eq]
    omega
  let commonMetric :=
    decoderScale ^ equations.refinementPower difference.earlierIndex *
      gammaMetric
  have hcommonMetric : 0 < commonMetric :=
    mul_pos (pow_pos hdecoderScale _) hgammaMetric
  have hsame :
      decoderScale ^ difference.refinementDifference * commonMetric =
        sourceScale ^ difference.sourceDifference * commonMetric := by
    calc
      decoderScale ^ difference.refinementDifference * commonMetric =
          decoderScale ^ equations.refinementPower difference.laterIndex *
            gammaMetric := by
        dsimp only [commonMetric]
        rw [← mul_assoc, ← pow_add, Nat.add_comm, hrefinementAdd]
      _ = sourceScale ^ equations.sourcePower difference.laterIndex *
          metric letter := hlater
      _ = sourceScale ^ difference.sourceDifference *
          (sourceScale ^ equations.sourcePower difference.earlierIndex *
            metric letter) := by
        rw [← mul_assoc, ← pow_add, Nat.add_comm, hsourceAdd]
      _ = sourceScale ^ difference.sourceDifference * commonMetric := by
        dsimp only [commonMetric, gammaMetric]
        rw [hearlier]
  nlinarith

structure MetricDurandTwoSourcePowerEquationData
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    {repetition : RepeatedBoundedLocalReturnSystems coding}
    (system : MetricDurandCommonDerivedSystem repetition) where
  left : MetricDurandPowerEquationFamily system.leftInput
  right : MetricDurandPowerEquationFamily system.rightInput

theorem metricDurandCommonSystem_has_twoPowerEquationFamilies
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    {repetition : RepeatedBoundedLocalReturnSystems coding}
    (system : MetricDurandCommonDerivedSystem repetition) :
    Nonempty (MetricDurandTwoSourcePowerEquationData system) := by
  obtain ⟨left⟩ := metricDurandProposition10_powerEquationFamily system.leftInput
  obtain ⟨right⟩ := metricDurandProposition10_powerEquationFamily system.rightInput
  exact ⟨left, right⟩

/-- The one decoder scales both transported positive metrics by the same
positive factor. -/
structure MetricCommonDecoderScaleData
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    {repetition : RepeatedBoundedLocalReturnSystems coding}
    (system : MetricDurandCommonDerivedSystem repetition) where
  scale : ℝ
  scale_gt_one : 1 < scale
  left_scales : SubstitutionScalesLetterLengths
    (returnDecoderSubstitutionMetric system.decomposition)
      system.leftMetric scale
  right_scales : SubstitutionScalesLetterLengths
    (returnDecoderSubstitutionMetric system.decomposition)
      system.rightMetric scale

/-- M5m.8: construct the common decoder scale from its two metric scaling
laws and uniqueness of the positive dominant scale. -/
theorem metricDurandCommonSystem_has_commonDecoderScale
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    {repetition : RepeatedBoundedLocalReturnSystems coding}
    (system : MetricDurandCommonDerivedSystem repetition) :
    Nonempty (MetricCommonDecoderScaleData system) := by
  obtain ⟨left⟩ := metricDurandInput_has_decoderScale system.leftInput
    system.leftMetric (eigenvalueσ ^ system.leftBasePower)
      system.leftMetric_pos system.leftScales
  obtain ⟨right⟩ := metricDurandInput_has_decoderScale system.rightInput
    system.rightMetric (eigenvalueτ ^ system.rightBasePower)
      system.rightMetric_pos system.rightScales
  have hscale := metricDecoderScaleData_scale_eq system.leftMetric_pos
    system.rightMetric_pos left right
  refine ⟨{
    scale := left.scale
    scale_gt_one := left.scale_gt_one
    left_scales := left.scales
    right_scales := ?_ }⟩
  rw [hscale]
  exact right.scales

/-- The exact metric replacement for the general spectral comparison: both
source growths are powers of one common decoder scale. -/
structure MetricDurandMetricComparison
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    {repetition : RepeatedBoundedLocalReturnSystems coding}
    {system : MetricDurandCommonDerivedSystem repetition}
    (equations : MetricDurandTwoSourcePowerEquationData system) where
  leftDifference : MetricDurandPowerEquationDifference equations.left
  rightDifference : MetricDurandPowerEquationDifference equations.right
  commonDecoder : MetricCommonDecoderScaleData system
  left_growth_eq :
    (eigenvalueσ ^ system.leftBasePower) ^ leftDifference.sourceDifference =
      commonDecoder.scale ^ leftDifference.refinementDifference
  right_growth_eq :
    (eigenvalueτ ^ system.rightBasePower) ^ rightDifference.sourceDifference =
      commonDecoder.scale ^ rightDifference.refinementDifference

/-- M5m.9: package the two positive differences and apply the metric growth
identity on each side. -/
theorem metricDurandMetricComparison_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    {repetition : RepeatedBoundedLocalReturnSystems coding}
    {system : MetricDurandCommonDerivedSystem repetition}
    (equations : MetricDurandTwoSourcePowerEquationData system) :
    Nonempty (MetricDurandMetricComparison equations) := by
  obtain ⟨leftDifference⟩ :=
    metricDurandPowerEquationFamily_has_positiveDifference equations.left
  obtain ⟨rightDifference⟩ :=
    metricDurandPowerEquationFamily_has_positiveDifference equations.right
  obtain ⟨commonDecoder⟩ :=
    metricDurandCommonSystem_has_commonDecoderScale system
  refine ⟨{
    leftDifference := leftDifference
    rightDifference := rightDifference
    commonDecoder := commonDecoder
    left_growth_eq := ?_
    right_growth_eq := ?_ }⟩
  · exact metricDurandPowerEquationDifference_has_metricGrowthIdentity
      leftDifference system.leftMetric system.leftMetric_pos
        (eigenvalueσ ^ system.leftBasePower) commonDecoder.scale
        (pow_pos (zero_lt_one.trans Pσ.one_lt_eigenvalue) _)
        (zero_lt_one.trans commonDecoder.scale_gt_one)
        system.leftScales commonDecoder.left_scales
  · exact metricDurandPowerEquationDifference_has_metricGrowthIdentity
      rightDifference system.rightMetric system.rightMetric_pos
        (eigenvalueτ ^ system.rightBasePower) commonDecoder.scale
        (pow_pos (zero_lt_one.trans Pτ.one_lt_eigenvalue) _)
        (zero_lt_one.trans commonDecoder.scale_gt_one)
        system.rightScales commonDecoder.right_scales

/-- M5m.10: eliminate the common decoder scale by cross-multiplying the two
positive refinement differences. -/
theorem metricDurandMetricComparison_forces_basePowerEquality
    {α : Type u} [Fintype α] [DecidableEq α]
    {σ τ : Substitution α} {seed : α} {word : InfiniteWord α}
    {eigenvalueσ eigenvalueτ : ℝ}
    {letterLengthσ letterLengthτ : α → ℝ}
    {Pσ : MetricGrowingFixedPresentation σ seed word eigenvalueσ letterLengthσ}
    {Pτ : MetricGrowingFixedPresentation τ seed word eigenvalueτ letterLengthτ}
    {core : MetricCommonRecurrentCoreData Pσ Pτ}
    {markers : CofinalMetricMarkerTower core.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower core markers decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    {repetition : RepeatedBoundedLocalReturnSystems coding}
    {system : MetricDurandCommonDerivedSystem repetition}
    {equations : MetricDurandTwoSourcePowerEquationData system}
    (comparison : MetricDurandMetricComparison equations) :
    ∃ leftPower rightPower : ℕ, 0 < leftPower ∧ 0 < rightPower ∧
      eigenvalueσ ^ leftPower = eigenvalueτ ^ rightPower := by
  let leftPower := system.leftBasePower *
    comparison.leftDifference.sourceDifference *
      comparison.rightDifference.refinementDifference
  let rightPower := system.rightBasePower *
    comparison.rightDifference.sourceDifference *
      comparison.leftDifference.refinementDifference
  refine ⟨leftPower, rightPower, ?_, ?_, ?_⟩
  · exact Nat.mul_pos
      (Nat.mul_pos system.leftBasePower_pos
        comparison.leftDifference.sourceDifference_pos)
      comparison.rightDifference.refinementDifference_pos
  · exact Nat.mul_pos
      (Nat.mul_pos system.rightBasePower_pos
        comparison.rightDifference.sourceDifference_pos)
      comparison.leftDifference.refinementDifference_pos
  · have hleft := congrArg
      (fun value : ℝ ↦ value ^
        comparison.rightDifference.refinementDifference)
      comparison.left_growth_eq
    have hright := congrArg
      (fun value : ℝ ↦ value ^
        comparison.leftDifference.refinementDifference)
      comparison.right_growth_eq
    have htheta :
        (comparison.commonDecoder.scale ^
          comparison.leftDifference.refinementDifference) ^
            comparison.rightDifference.refinementDifference =
        (comparison.commonDecoder.scale ^
          comparison.rightDifference.refinementDifference) ^
            comparison.leftDifference.refinementDifference := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hcombined := hleft.trans (htheta.trans hright.symm)
    simpa only [← pow_mul, Nat.mul_assoc, leftPower, rightPower] using hcombined

end

end Symbolic
end CommutingIntervalSimplified
