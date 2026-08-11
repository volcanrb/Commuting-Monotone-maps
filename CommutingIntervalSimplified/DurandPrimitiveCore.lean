import CommutingIntervalSimplified.DurandMetric

/-!
# Faithful primitive recurrent cores

This module isolates the one-source recurrent-core extraction used by the
primitive-language form of Durand's comparison theorem.  The core alphabet is
not an arbitrary terminal component: it is exactly the set of letters which
occur arbitrarily far out in the displayed source fixed word.  This makes the
connection with the recurrent ambient language part of the definition.

A left core and a right core are extracted independently.  Their ranks,
alphabets, substitutions, and fixed words are never identified.  Only their
decoded finite-factor languages are later proved equal.

## Import architecture

`MetricGrowingFixedPresentation` belongs to the M0 section of
`DurandMetric`, so the final acyclic architecture is

`DurandSupport -> DurandMetric(M0--M1) -> DurandPrimitiveCore
 -> DurandPrimitiveLanguage -> Coding`.

The primitive predicate below deliberately lives under `PrimitiveCore`
rather than relying on the obsolete M2--M5 tail still temporarily present in
`DurandMetric`.  The declarations A1--A10 form the frozen proof skeleton.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

open Function Set
open scoped BigOperators

noncomputable section

universe u

namespace PrimitiveCore

/-- A finite substitution is primitive if one positive common power sends
every source letter across every target letter. -/
def IsPrimitiveSubstitution {α : Type u} [Fintype α]
    (source : Substitution α) : Prop :=
  ∃ power : ℕ, 0 < power ∧ ∀ sourceLetter targetLetter,
    targetLetter ∈ source.iterateLetter power sourceLetter

end PrimitiveCore

/-- Two streams over one ambient alphabet have the same finite-factor
language.  This does not assert equality of the streams. -/
def SameFactorLanguage {α : Type u}
    (left right : InfiniteWord α) : Prop :=
  ∀ factor : Word α,
    IsInfiniteFactor left factor ↔ IsInfiniteFactor right factor

/-- The finite set of letters which occur arbitrarily far out in a word. -/
noncomputable def recurrentLetterFinset
    {α : Type u} [Fintype α] (word : InfiniteWord α) : Finset α := by
  classical
  exact Finset.univ.filter (OccursInfinitelyOften word)

@[simp] theorem mem_recurrentLetterFinset
    {α : Type u} [Fintype α] {word : InfiniteWord α} {letter : α} :
    letter ∈ recurrentLetterFinset word ↔
      OccursInfinitelyOften word letter := by
  classical
  simp [recurrentLetterFinset]

/-- The recurrent alphabet, represented as a finite subtype. -/
abbrev RecurrentLetter
    {α : Type u} [Fintype α] (word : InfiniteWord α) :=
  {letter : α // letter ∈ recurrentLetterFinset word}

/-! ## Records carried between A1--A10 -/

/-- The ambient substitution restricted to its recurrent-letter alphabet.
The exact forgetful intertwining is displayed rather than inferred. -/
structure RecurrentAlphabetRestrictionData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength) where
  recurrent_nonempty : (recurrentLetterFinset sourceWord).Nonempty
  substitution : Substitution (RecurrentLetter sourceWord)
  forget_image : ∀ letter : RecurrentLetter sourceWord,
    (substitution letter).map Subtype.val = source letter.1

/-- One explicit common depth proving that the recurrent restriction is
primitive. -/
structure PrimitiveRecurrentAlphabetData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (restriction : RecurrentAlphabetRestrictionData P) where
  commonDepth : ℕ
  commonDepth_pos : 0 < commonDepth
  every_target_occurs : ∀ sourceLetter targetLetter,
    targetLetter ∈
      restriction.substitution.iterateLetter commonDepth sourceLetter

namespace PrimitiveRecurrentAlphabetData

theorem isPrimitive
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    (data : PrimitiveRecurrentAlphabetData restriction) :
    PrimitiveCore.IsPrimitiveSubstitution restriction.substitution :=
  ⟨data.commonDepth, data.commonDepth_pos, data.every_target_occurs⟩

end PrimitiveRecurrentAlphabetData

/-- A positive prolongable power of the primitive recurrent restriction. -/
structure PoweredRecurrentSubstitutionData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (restriction : RecurrentAlphabetRestrictionData P)
    (hprimitive : PrimitiveRecurrentAlphabetData restriction) where
  sourcePower : ℕ
  sourcePower_pos : 0 < sourcePower
  substitution : Substitution (RecurrentLetter sourceWord)
  substitution_eq_power :
    substitution = restriction.substitution.power sourcePower
  source_image : ∀ letter : RecurrentLetter sourceWord,
    (substitution letter).map Subtype.val =
      (source.power sourcePower) letter.1
  primitive : PrimitiveCore.IsPrimitiveSubstitution substitution
  growing : substitution.IsGrowing
  coreSeed : RecurrentLetter sourceWord
  prolongable : substitution.ProlongableOn coreSeed

/-- The canonical fixed word of a powered recurrent substitution. -/
structure PoweredRecurrentFixedData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    (powered : PoweredRecurrentSubstitutionData restriction hprimitive) where
  coreWord : InfiniteWord (RecurrentLetter sourceWord)
  coreSeed_eq_head : powered.coreSeed = coreWord.head
  fixed : powered.substitution.IsFixedPoint coreWord
  iterates_are_prefixes : ∀ n,
    powered.substitution.iterateLetter n powered.coreSeed =
      coreWord.take
        (powered.substitution.iterateLetter n powered.coreSeed).length
  every_letter_occurs : ∀ letter : RecurrentLetter sourceWord,
    Substitution.OccursInInfiniteWord letter coreWord

/-- The canonical recurrent fixed word together with its exact embedding in
the ambient source word. -/
structure PoweredRecurrentCoreData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    (powered : PoweredRecurrentSubstitutionData restriction hprimitive)
    extends PoweredRecurrentFixedData powered where
  decoded_prefix_factor : ∀ length,
    IsInfiniteFactor sourceWord ((coreWord.take length).map Subtype.val)

/-- The implementation-facing primitive recurrent core for one source. -/
structure MetricPrimitiveRecurrentCoreSide
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength) where
  component : Finset α
  component_nonempty : component.Nonempty
  substitution : Substitution component
  coreWord : InfiniteWord component
  sourcePower : ℕ
  sourcePower_pos : 0 < sourcePower
  source_image : ∀ letter,
    (substitution letter).map Subtype.val =
      (source.power sourcePower) letter.1
  primitive : PrimitiveCore.IsPrimitiveSubstitution substitution
  presentation : MetricGrowingFixedPresentation substitution coreWord.head
    coreWord (sourceScale ^ sourcePower)
      (fun letter => sourceLength letter.1)
  decoded_language : ∀ factor : Word α,
    IsInfiniteFactor (fun n => (coreWord n).1) factor ↔
      IsRecurrentFactor sourceWord factor

namespace MetricPrimitiveRecurrentCoreSide

def decodedWord
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (side : MetricPrimitiveRecurrentCoreSide P) : InfiniteWord α :=
  fun n => (side.coreWord n).1

def poweredScale
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (side : MetricPrimitiveRecurrentCoreSide P) : ℝ :=
  sourceScale ^ side.sourcePower

end MetricPrimitiveRecurrentCoreSide

/-- Paired cores for the actual common-exact-metric specialization.  Both
sources scale the same ambient metric, but their core data remain separate. -/
structure MetricPairedRecurrentCoreData
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength) where
  left : MetricPrimitiveRecurrentCoreSide Pleft
  right : MetricPrimitiveRecurrentCoreSide Pright

/-! ## Frozen A1--A10 theorem skeleton -/

/-- **A1.** Some ambient letter occurs arbitrarily far out, so the recurrent
alphabet is nonempty. -/
theorem recurrentLetterAlphabet_nonempty
    {α : Type u} [Fintype α] [DecidableEq α]
    (word : InfiniteWord α) :
    (recurrentLetterFinset word).Nonempty := by
  classical
  by_contra hempty
  have hnot : ∀ letter : α,
      ¬ OccursInfinitelyOften word letter := by
    intro letter hletter
    exact hempty ⟨letter, mem_recurrentLetterFinset.mpr hletter⟩
  have habsent : ∀ letter : α, ∃ cutoff : ℕ,
      ∀ start : ℕ, cutoff ≤ start → word start ≠ letter := by
    intro letter
    simpa only [OccursInfinitelyOften, not_forall, not_exists,
      not_and, not_le] using hnot letter
  choose cutoff hcutoff using habsent
  let commonCutoff := Finset.univ.sup cutoff
  have hle : cutoff (word commonCutoff) ≤ commonCutoff :=
    Finset.le_sup (f := cutoff) (Finset.mem_univ (word commonCutoff))
  exact hcutoff (word commonCutoff) commonCutoff hle rfl

/-- **A2.** The recurrent alphabet is image-closed.  Nonerasing makes image
boundaries of arbitrarily late source occurrences tend to infinity. -/
private theorem letter_position_of_infiniteFactorAt_core
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

theorem recurrentLetterAlphabet_image_closed
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    {letter target : α}
    (hletter : OccursInfinitelyOften word letter)
    (htarget : target ∈ source letter) :
    OccursInfinitelyOften word target := by
  intro cutoff
  obtain ⟨position, hposition, hat⟩ := hletter cutoff
  let boundary := (source.mapWord (word.take position)).length
  have hboundary_lower : position ≤ boundary := by
    dsimp only [boundary]
    simpa using source.length_le_mapWord (word.take position)
  have hone : (word.drop position).take 1 = [word position] := by
    rw [show 1 = 0 + 1 by omega, Stream'.take_succ']
    simp only [Stream'.take_zero, List.nil_append]
    change [word (0 + position)] = [word position]
    simp
  have himage : InfiniteFactorAt word (source letter) boundary := by
    have h := Substitution.mapWord_drop_take_at_fixed
      hfixed position 1
    rw [hone, hat] at h
    simpa [boundary] using h
  obtain ⟨offset, _hoffset, htargetAt⟩ :=
    letter_position_of_infiniteFactorAt_core himage htarget
  exact ⟨boundary + offset,
    hposition.trans (hboundary_lower.trans (Nat.le_add_right boundary offset)),
    htargetAt⟩

/-- **A3.** Restrict the source substitution to the recurrent alphabet,
preserving its images exactly under the forgetful injection. -/
theorem recurrentAlphabetRestriction_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength) :
    Nonempty (RecurrentAlphabetRestrictionData P) := by
  classical
  let liftImage (letter : RecurrentLetter sourceWord) :
      Word (RecurrentLetter sourceWord) :=
    (source letter.1).attachWith
      (fun target => target ∈ recurrentLetterFinset sourceWord)
      (by
        intro target htarget
        exact mem_recurrentLetterFinset.mpr
          (recurrentLetterAlphabet_image_closed P.fixed
            (mem_recurrentLetterFinset.mp letter.property) htarget))
  let restricted : Substitution (RecurrentLetter sourceWord) := {
    image := liftImage
    image_ne_nil := by
      intro letter
      dsimp only [liftImage]
      simpa using source.image_ne_nil letter.1 }
  refine ⟨{
    recurrent_nonempty := recurrentLetterAlphabet_nonempty sourceWord
    substitution := restricted
    forget_image := ?_ }⟩
  intro letter
  change (liftImage letter).map Subtype.val = source letter.1
  exact List.attachWith_map_subtype_val _

/-- **A4.** Syndetic singleton recurrence and uniform source growth give one
common positive depth at which every recurrent target occurs in the image of
every recurrent source letter. -/
private theorem recurrent_singleton_of_occursInfinitelyOften
    {α : Type u} {word : InfiniteWord α} {letter : α}
    (hletter : OccursInfinitelyOften word letter) :
    IsRecurrentFactor word [letter] := by
  intro cutoff
  obtain ⟨start, hstart, hat⟩ := hletter cutoff
  refine ⟨start, hstart, ?_⟩
  change (word.drop start).take 1 = [letter]
  rw [show 1 = 0 + 1 by omega, Stream'.take_succ']
  simp only [Stream'.take_zero, List.nil_append]
  change [word (0 + start)] = [letter]
  simp [hat]

private theorem map_mapWord_of_letter_intertwining
    {β γ : Type*} (left : Substitution β) (right : Substitution γ)
    (decode : β → γ)
    (hintertwine : ∀ letter, (left letter).map decode = right (decode letter)) :
    ∀ letters : Word β,
      (left.mapWord letters).map decode =
        right.mapWord (letters.map decode) := by
  intro letters
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      simp only [Substitution.mapWord_cons, List.map_append, List.map_cons,
        hintertwine, ih]

private theorem recurrentRestriction_iterate_forget
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (restriction : RecurrentAlphabetRestrictionData P) :
    ∀ (iterate : ℕ) (letter : RecurrentLetter sourceWord),
      (restriction.substitution.iterateLetter iterate letter).map Subtype.val =
        source.iterateLetter iterate letter.1 := by
  intro iterate letter
  induction iterate with
  | zero => rfl
  | succ iterate ih =>
      rw [Substitution.iterateLetter_succ,
        Substitution.iterateLetter_succ,
        map_mapWord_of_letter_intertwining
          restriction.substitution source Subtype.val restriction.forget_image,
        ih]

private theorem iterateLetter_length_mono_core
    {α : Type u} (source : Substitution α) (letter : α) :
    Monotone (fun iterate => (source.iterateLetter iterate letter).length) := by
  apply monotone_nat_of_le_succ
  intro iterate
  rw [Substitution.iterateLetter_succ]
  exact source.length_le_mapWord _

private theorem iterateWord_add_core
    {α : Type u} (source : Substitution α) (left right : ℕ)
    (letters : Word α) :
    source.iterateWord (left + right) letters =
      source.iterateWord left (source.iterateWord right letters) := by
  induction left with
  | zero => simp
  | succ left ih =>
      simpa only [Nat.succ_add, Substitution.iterateWord_succ] using
        congrArg source.mapWord ih

private theorem power_iterateLetter_core
    {α : Type u} (source : Substitution α) (power level : ℕ)
    (letter : α) :
    (source.power power).iterateLetter level letter =
      source.iterateLetter (power * level) letter := by
  change (source.power power).iterateWord level [letter] =
    source.iterateWord (power * level) [letter]
  induction level with
  | zero => rfl
  | succ level ih =>
      rw [Substitution.iterateWord_succ, source.power_mapWord, ih,
        ← iterateWord_add_core]
      simp only [Nat.mul_succ]
      rw [Nat.add_comm]

private theorem iterateLetter_mem_iterateWord_of_mem_core
    {α : Type u} (source : Substitution α) (level : ℕ)
    {letters : Word α} {sourceLetter targetLetter : α}
    (hsource : sourceLetter ∈ letters)
    (htarget : targetLetter ∈ source.iterateLetter level sourceLetter) :
    targetLetter ∈ source.iterateWord level letters := by
  rw [← source.power_mapWord level letters]
  change targetLetter ∈
    List.flatMap (source.power level) letters
  exact List.mem_flatMap.mpr ⟨sourceLetter, hsource, by
    simpa only [Substitution.power_apply] using htarget⟩

private theorem primitive_contains_at_later_core
    {α : Type u} (source : Substitution α)
    {depth later : ℕ}
    (hcontains : ∀ sourceLetter targetLetter,
      targetLetter ∈ source.iterateLetter depth sourceLetter)
    (hdepth : depth ≤ later) :
    ∀ sourceLetter targetLetter,
      targetLetter ∈ source.iterateLetter later sourceLetter := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  intro sourceLetter targetLetter
  obtain ⟨middleLetter, rest, hmiddle⟩ := List.exists_cons_of_ne_nil
    (source.iterateLetter_ne_nil extra sourceLetter)
  have hmiddleMem : middleLetter ∈
      source.iterateLetter extra sourceLetter := by
    rw [hmiddle]
    simp
  have htarget := iterateLetter_mem_iterateWord_of_mem_core source depth
    hmiddleMem (hcontains middleLetter targetLetter)
  change targetLetter ∈
    source.iterateWord depth
      (source.iterateWord extra [sourceLetter]) at htarget
  rw [← iterateWord_add_core] at htarget
  exact htarget

private theorem primitive_power_core
    {α : Type u} [Fintype α] {source : Substitution α}
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source)
    {power : ℕ} (hpower : 0 < power) :
    PrimitiveCore.IsPrimitiveSubstitution (source.power power) := by
  obtain ⟨depth, hdepth, hcontains⟩ := hprimitive
  refine ⟨depth, hdepth, ?_⟩
  intro sourceLetter targetLetter
  rw [power_iterateLetter_core]
  apply primitive_contains_at_later_core source hcontains
  nlinarith

private theorem growing_power_core
    {α : Type u} {source : Substitution α}
    (hgrowing : source.IsGrowing) {power : ℕ} (hpower : 0 < power) :
    (source.power power).IsGrowing := by
  intro letter bound
  obtain ⟨level, hlevel⟩ := hgrowing letter bound
  refine ⟨level, ?_⟩
  rw [power_iterateLetter_core]
  exact hlevel.trans
    (iterateLetter_length_mono_core source letter (by nlinarith))

private theorem iterateLetter_eq_headIterate_cons_core
    {α : Type u} (source : Substitution α) (level : ℕ) (letter : α) :
    ∃ tail : Word α,
      source.iterateLetter level letter =
        (source.imageHead^[level] letter) :: tail := by
  induction level with
  | zero => exact ⟨[], rfl⟩
  | succ level ih =>
      obtain ⟨tail, htail⟩ := ih
      rw [Substitution.iterateLetter_succ, htail,
        Substitution.mapWord_cons,
        ← source.imageHead_cons_imageTail]
      refine ⟨source.imageTail (source.imageHead^[level] letter) ++
        source.mapWord tail, ?_⟩
      simp only [Function.iterate_succ_apply']
      rfl

private theorem exists_prolongable_power_of_growing_core
    {α : Type u} [Finite α] [Nonempty α]
    (source : Substitution α) (hgrowing : source.IsGrowing) :
    ∃ power : ℕ, ∃ seed : α, 0 < power ∧
      (source.power power).ProlongableOn seed := by
  classical
  let initial : α := Classical.choice (inferInstance : Nonempty α)
  obtain ⟨left, right, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun level : ℕ => source.imageHead^[level] initial)
  obtain ⟨early, late, hearlyLate, heqHead⟩ :
      ∃ early late : ℕ, early < late ∧
        source.imageHead^[early] initial =
          source.imageHead^[late] initial := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨left, right, hlt, heq⟩
    · exact ⟨right, left, hgt, heq.symm⟩
  let period := late - early
  let seed := source.imageHead^[early] initial
  have hperiodPos : 0 < period := by
    dsimp only [period]
    omega
  have hperiodic : source.imageHead^[period] seed = seed := by
    dsimp only [period, seed]
    calc
      source.imageHead^[late - early]
          (source.imageHead^[early] initial) =
          source.imageHead^[(late - early) + early] initial := by
            rw [Function.iterate_add_apply]
      _ = source.imageHead^[late] initial := by
            congr 2
            omega
      _ = source.imageHead^[early] initial := heqHead.symm
  obtain ⟨growthLevel, hgrowthLevel⟩ := hgrowing seed 2
  let multiplier := growthLevel + 1
  let power := period * multiplier
  have hpowerPos : 0 < power := by
    dsimp only [power, multiplier]
    exact Nat.mul_pos hperiodPos (Nat.succ_pos _)
  have hlevelPower : growthLevel ≤ power := by
    dsimp only [power, multiplier]
    nlinarith
  have hperiodicPower : source.imageHead^[power] seed = seed := by
    have hp : Function.IsPeriodicPt source.imageHead period seed := hperiodic
    exact hp.mul_const multiplier
  have hlengthPower : 2 ≤
      (source.iterateLetter power seed).length :=
    hgrowthLevel.trans
      (iterateLetter_length_mono_core source seed hlevelPower)
  obtain ⟨tail, htail⟩ :=
    iterateLetter_eq_headIterate_cons_core source power seed
  rw [hperiodicPower] at htail
  have htailNonempty : tail ≠ [] := by
    intro hnil
    rw [htail, hnil] at hlengthPower
    simp at hlengthPower
  exact ⟨power, seed, hpowerPos, tail, htailNonempty, by
    rw [Substitution.power_apply, htail]⟩

theorem recurrentAlphabetRestriction_isPrimitive
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (hsyndetic : RecurrentFactorsSyndetic sourceWord)
    (restriction : RecurrentAlphabetRestrictionData P) :
    Nonempty (PrimitiveRecurrentAlphabetData restriction) := by
  classical
  letI : Nonempty (RecurrentLetter sourceWord) :=
    ⟨⟨restriction.recurrent_nonempty.choose,
      restriction.recurrent_nonempty.choose_spec⟩⟩
  have hgapExists (target : RecurrentLetter sourceWord) :
      ∃ gap : ℕ, 0 < gap ∧ ∀ start : ℕ,
        ∃ offset : ℕ, offset ≤ gap ∧
          InfiniteFactorAt sourceWord [target.1] (start + offset) := by
    exact hsyndetic [target.1]
      (recurrent_singleton_of_occursInfinitelyOften
        (mem_recurrentLetterFinset.mp target.property))
  choose gap hgapPos hgap using hgapExists
  let gapBound : ℕ := ∑ target : RecurrentLetter sourceWord, gap target
  have hgap_le (target : RecurrentLetter sourceWord) :
      gap target ≤ gapBound := by
    dsimp only [gapBound]
    exact Finset.single_le_sum
      (fun other _ => Nat.zero_le (gap other)) (Finset.mem_univ target)
  have hdepthExists (letter : RecurrentLetter sourceWord) :
      ∃ depth : ℕ, 0 < depth ∧
        gapBound + 1 ≤ (source.iterateLetter depth letter.1).length := by
    obtain ⟨iterate, hiterate⟩ := P.growing letter.1 (gapBound + 1)
    refine ⟨iterate + 1, Nat.succ_pos iterate, hiterate.trans ?_⟩
    rw [Substitution.iterateLetter_succ]
    exact source.length_le_mapWord _
  choose depth hdepthPos hdepthBound using hdepthExists
  let commonDepth : ℕ := Finset.univ.sup depth
  have hdepth_le (letter : RecurrentLetter sourceWord) :
      depth letter ≤ commonDepth := by
    exact Finset.le_sup (f := depth) (Finset.mem_univ letter)
  let witness : RecurrentLetter sourceWord := Classical.choice inferInstance
  have hcommonDepth_pos : 0 < commonDepth :=
    (hdepthPos witness).trans_le (hdepth_le witness)
  refine ⟨{
    commonDepth := commonDepth
    commonDepth_pos := hcommonDepth_pos
    every_target_occurs := ?_ }⟩
  intro sourceLetter targetLetter
  have hblockLength : gapBound + 1 ≤
      (source.iterateLetter commonDepth sourceLetter.1).length :=
    (hdepthBound sourceLetter).trans
      (iterateLetter_length_mono_core source sourceLetter.1
        (hdepth_le sourceLetter))
  obtain ⟨position, _hposition, hat⟩ :=
    (mem_recurrentLetterFinset.mp sourceLetter.property) 0
  let boundary :=
    ((source.power commonDepth).mapWord (sourceWord.take position)).length
  have hfixedPower :
      (source.power commonDepth).IsFixedPoint sourceWord :=
    Substitution.isFixedPoint_power P.fixed hcommonDepth_pos
  have hone : (sourceWord.drop position).take 1 = [sourceWord position] := by
    rw [show 1 = 0 + 1 by omega, Stream'.take_succ']
    simp only [Stream'.take_zero, List.nil_append]
    change [sourceWord (0 + position)] = [sourceWord position]
    simp
  have hblockAt : InfiniteFactorAt sourceWord
      (source.iterateLetter commonDepth sourceLetter.1) boundary := by
    have h := Substitution.mapWord_drop_take_at_fixed
      hfixedPower position 1
    rw [hone, hat] at h
    simpa [boundary, Substitution.power_apply] using h
  obtain ⟨offset, hoffset, htargetAt⟩ := hgap targetLetter boundary
  have hwithin : offset + [targetLetter.1].length ≤
      (source.iterateLetter commonDepth sourceLetter.1).length := by
    have htargetGapLe := hgap_le targetLetter
    simp only [List.length_singleton]
    omega
  have hfinite := finiteFactorAt_of_nested_infiniteFactorAt
    hblockAt htargetAt hwithin
  have htargetMem : targetLetter.1 ∈
      source.iterateLetter commonDepth sourceLetter.1 := by
    have hfiniteEq :
        ((source.iterateLetter commonDepth sourceLetter.1).drop offset).take 1 =
          [targetLetter.1] := by
      simpa using hfinite.2
    have hlocal : targetLetter.1 ∈
        ((source.iterateLetter commonDepth sourceLetter.1).drop offset).take 1 := by
      rw [hfiniteEq]
      simp
    exact List.mem_of_mem_drop (List.mem_of_mem_take hlocal)
  have hforget :=
    recurrentRestriction_iterate_forget restriction commonDepth sourceLetter
  rw [← hforget] at htargetMem
  exact (List.mem_map_of_injective Subtype.val_injective).mp htargetMem

/-- **A5a.** Ambient growth transfers through the exact forgetful square to
the recurrent-alphabet restriction. -/
theorem recurrentAlphabetRestriction_isGrowing
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (restriction : RecurrentAlphabetRestrictionData P) :
    restriction.substitution.IsGrowing := by
  intro letter bound
  obtain ⟨level, hlevel⟩ := P.growing letter.1 bound
  refine ⟨level, ?_⟩
  have hforget :=
    recurrentRestriction_iterate_forget restriction level letter
  have hlength := congrArg List.length hforget
  simp only [List.length_map] at hlength
  rw [hlength]
  exact hlevel

/-- **A5b.** A growing primitive substitution has a positive power which is
prolongable on a recurrent letter.  The powered forgetful square is exact. -/
theorem primitiveGrowingRestriction_has_prolongablePower
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (restriction : RecurrentAlphabetRestrictionData P)
    (hprimitive : PrimitiveRecurrentAlphabetData restriction)
    (hgrowing : restriction.substitution.IsGrowing) :
    Nonempty (PoweredRecurrentSubstitutionData restriction hprimitive) := by
  letI : Nonempty (RecurrentLetter sourceWord) :=
    ⟨⟨restriction.recurrent_nonempty.choose,
      restriction.recurrent_nonempty.choose_spec⟩⟩
  obtain ⟨sourcePower, coreSeed, hsourcePower, hprolongable⟩ :=
    exists_prolongable_power_of_growing_core
      restriction.substitution hgrowing
  let powered := restriction.substitution.power sourcePower
  refine ⟨{
    sourcePower := sourcePower
    sourcePower_pos := hsourcePower
    substitution := powered
    substitution_eq_power := rfl
    source_image := ?_
    primitive := primitive_power_core hprimitive.isPrimitive hsourcePower
    growing := growing_power_core hgrowing hsourcePower
    coreSeed := coreSeed
    prolongable := hprolongable
  }⟩
  intro letter
  simpa only [powered, Substitution.power_apply] using
    recurrentRestriction_iterate_forget restriction sourcePower letter

private theorem iterateLetter_prefix_of_le_core
    {α : Type u} {source : Substitution α} {seed : α}
    (hprolongable : source.ProlongableOn seed)
    {left right : ℕ} (hle : left ≤ right) :
    source.iterateLetter left seed <+:
      source.iterateLetter right seed := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simpa using List.prefix_refl (source.iterateLetter left seed)
  | succ extra ih =>
      simpa [Nat.add_assoc] using
        ih.trans (source.iterateLetter_prefix_succ hprolongable (left + extra))

private noncomputable def prolongableLimitWord_core
    {α : Type u} (source : Substitution α) (seed : α)
    (hgrowing : source.IsGrowing) : InfiniteWord α :=
  fun position =>
    (source.iterateLetter
      (Classical.choose (hgrowing seed (position + 1))) seed)[position]'(
        lt_of_lt_of_le (Nat.lt_succ_self position)
          (Classical.choose_spec (hgrowing seed (position + 1))))

private theorem iterateLetter_eq_take_prolongableLimitWord_core
    {α : Type u} {source : Substitution α} {seed : α}
    (hprolongable : source.ProlongableOn seed)
    (hgrowing : source.IsGrowing) (level : ℕ) :
    source.iterateLetter level seed =
      (prolongableLimitWord_core source seed hgrowing).take
        (source.iterateLetter level seed).length := by
  apply List.ext_getElem
  · simp
  · intro position hposition htake
    rw [Stream'.take_get (m := position)
      (n := (source.iterateLetter level seed).length)
      (a := prolongableLimitWord_core source seed hgrowing) htake]
    unfold prolongableLimitWord_core
    let chosenLevel :=
      Classical.choose (hgrowing seed (position + 1))
    have hpositionChosen : position <
        (source.iterateLetter chosenLevel seed).length :=
      lt_of_lt_of_le (Nat.lt_succ_self position)
        (Classical.choose_spec (hgrowing seed (position + 1)))
    let commonLevel := max level chosenLevel
    have hlevelPrefix : source.iterateLetter level seed <+:
        source.iterateLetter commonLevel seed :=
      iterateLetter_prefix_of_le_core hprolongable
        (Nat.le_max_left _ _)
    have hchosenPrefix : source.iterateLetter chosenLevel seed <+:
        source.iterateLetter commonLevel seed :=
      iterateLetter_prefix_of_le_core hprolongable
        (Nat.le_max_right _ _)
    exact (hlevelPrefix.getElem hposition).trans
      (hchosenPrefix.getElem hpositionChosen).symm

private theorem mapInfinite_append_stream_core
    {α : Type u} (source : Substitution α) (finitePrefix : Word α)
    (word : InfiniteWord α) :
    source.mapInfinite (finitePrefix ++ₛ word) =
      source.mapWord finitePrefix ++ₛ source.mapInfinite word := by
  induction finitePrefix with
  | nil => rfl
  | cons letter rest ih =>
      rw [Stream'.cons_append_stream,
        source.mapInfinite_eq_append_first_image,
        Stream'.head_cons, Stream'.tail_cons, ih,
        source.mapWord_cons, Stream'.append_append_stream]

private theorem prolongableLimitWord_fixed_core
    {α : Type u} {source : Substitution α} {seed : α}
    (hprolongable : source.ProlongableOn seed)
    (hgrowing : source.IsGrowing) :
    source.IsFixedPoint
      (prolongableLimitWord_core source seed hgrowing) := by
  let word := prolongableLimitWord_core source seed hgrowing
  apply funext
  intro position
  obtain ⟨level, hlevel⟩ := hgrowing seed (position + 1)
  have hposition : position <
      (source.iterateLetter level seed).length :=
    lt_of_lt_of_le (Nat.lt_succ_self position) hlevel
  have hprefix := iterateLetter_eq_take_prolongableLimitWord_core
    hprolongable hgrowing level
  have hdecomposition :
      source.iterateLetter level seed ++ₛ
          word.drop (source.iterateLetter level seed).length = word := by
    calc
      source.iterateLetter level seed ++ₛ
          word.drop (source.iterateLetter level seed).length =
          word.take (source.iterateLetter level seed).length ++ₛ
            word.drop (source.iterateLetter level seed).length := by
              exact congrArg
                (fun pref => pref ++ₛ
                  word.drop (source.iterateLetter level seed).length)
                hprefix
      _ = word := Stream'.append_take_drop _ _
  have hmapped : source.mapInfinite word =
      source.mapWord (source.iterateLetter level seed) ++ₛ
        source.mapInfinite
          (word.drop (source.iterateLetter level seed).length) := by
    calc
      source.mapInfinite word = source.mapInfinite
          (source.iterateLetter level seed ++ₛ
            word.drop (source.iterateLetter level seed).length) :=
        congrArg source.mapInfinite hdecomposition.symm
      _ = _ := mapInfinite_append_stream_core source _ _
  rw [hmapped]
  have hprefixSucc :=
    source.iterateLetter_prefix_succ hprolongable level
  have hpositionSucc : position <
      (source.mapWord (source.iterateLetter level seed)).length := by
    change position < (source.iterateLetter (level + 1) seed).length
    exact hposition.trans_le hprefixSucc.length_le
  change (source.mapWord (source.iterateLetter level seed) ++ₛ
      source.mapInfinite
        (word.drop (source.iterateLetter level seed).length)).get position =
    word.get position
  rw [Stream'.get_append_left (n := position)
    (x := source.mapWord (source.iterateLetter level seed))
    (a := source.mapInfinite
      (word.drop (source.iterateLetter level seed).length)) hpositionSucc]
  change (source.iterateLetter (level + 1) seed)[position] = word position
  have hprefixNext := iterateLetter_eq_take_prolongableLimitWord_core
    hprolongable hgrowing (level + 1)
  have hpositionTake : position <
      (word.take (source.iterateLetter (level + 1) seed).length).length := by
    simpa using hpositionSucc
  calc
    (source.iterateLetter (level + 1) seed)[position]'hpositionSucc =
        (word.take
          (source.iterateLetter (level + 1) seed).length)[position]'hpositionTake :=
      getElem_congr hprefixNext rfl hpositionSucc
    _ = word.get position := Stream'.take_get (m := position)
      (n := (source.iterateLetter (level + 1) seed).length)
      (a := word) hpositionTake

/-- **A5c.** Form the canonical fixed limit of the prolongable powered
substitution; primitivity makes every recurrent letter occur in it. -/
theorem poweredRecurrentSubstitution_has_fixedData
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    (powered : PoweredRecurrentSubstitutionData restriction hprimitive) :
    Nonempty (PoweredRecurrentFixedData powered) := by
  let coreWord := prolongableLimitWord_core powered.substitution
    powered.coreSeed powered.growing
  have hprefix (level : ℕ) :
      powered.substitution.iterateLetter level powered.coreSeed =
        coreWord.take
          (powered.substitution.iterateLetter level powered.coreSeed).length :=
    iterateLetter_eq_take_prolongableLimitWord_core
      powered.prolongable powered.growing level
  have hfixed : powered.substitution.IsFixedPoint coreWord :=
    prolongableLimitWord_fixed_core powered.prolongable powered.growing
  have hseed : powered.coreSeed = coreWord.head := by
    have hzero := hprefix 0
    simpa [coreWord, Stream'.take_succ'] using hzero
  have hevery (letter : RecurrentLetter sourceWord) :
      Substitution.OccursInInfiniteWord letter coreWord := by
    obtain ⟨depth, _hdepth, hcontains⟩ := powered.primitive
    have hmem := hcontains powered.coreSeed letter
    rw [hprefix depth] at hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨position, hposition, hget⟩ := hmem
    refine ⟨position, ?_⟩
    exact (Stream'.take_get (m := position)
      (n := (powered.substitution.iterateLetter depth
        powered.coreSeed).length) (a := coreWord) hposition).symm.trans hget
  exact ⟨{
    coreWord := coreWord
    coreSeed_eq_head := hseed
    fixed := hfixed
    iterates_are_prefixes := hprefix
    every_letter_occurs := hevery
  }⟩

private theorem poweredRecurrent_iterate_forget
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    (powered : PoweredRecurrentSubstitutionData restriction hprimitive)
    (level : ℕ) (letter : RecurrentLetter sourceWord) :
    (powered.substitution.iterateLetter level letter).map Subtype.val =
      source.iterateLetter (powered.sourcePower * level) letter.1 := by
  rw [powered.substitution_eq_power,
    power_iterateLetter_core]
  exact recurrentRestriction_iterate_forget restriction
    (powered.sourcePower * level) letter

/-- **A5d.** Every finite prefix of the canonical recurrent fixed word,
after forgetting the subtype, occurs in the ambient source fixed word. -/
theorem poweredRecurrentFixed_decodedPrefixFactor
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    {powered : PoweredRecurrentSubstitutionData restriction hprimitive}
    (fixed : PoweredRecurrentFixedData powered) :
    ∀ length,
      IsInfiniteFactor sourceWord
        ((fixed.coreWord.take length).map Subtype.val) := by
  intro length
  obtain ⟨baseLevel, hbaseLevel⟩ :=
    powered.growing powered.coreSeed length
  let level := baseLevel + 1
  have hlength : length ≤
      (powered.substitution.iterateLetter level powered.coreSeed).length :=
    hbaseLevel.trans
      (iterateLetter_length_mono_core powered.substitution
        powered.coreSeed (by dsimp [level]; omega))
  have hcorePrefix : fixed.coreWord.take length <+:
      powered.substitution.iterateLetter level powered.coreSeed := by
    rw [fixed.iterates_are_prefixes]
    exact Stream'.take_prefix_take_left length
      (powered.substitution.iterateLetter level powered.coreSeed).length
      fixed.coreWord hlength
  have hdecodedPrefix : (fixed.coreWord.take length).map Subtype.val <+:
      source.iterateLetter (powered.sourcePower * level)
        powered.coreSeed.1 := by
    have hmapped := hcorePrefix.map Subtype.val
    rw [poweredRecurrent_iterate_forget powered level powered.coreSeed] at hmapped
    exact hmapped
  obtain ⟨sourcePosition, _hsourcePosition, hseedAt⟩ :=
    (mem_recurrentLetterFinset.mp powered.coreSeed.property) 0
  have hexponent : 0 < powered.sourcePower * level :=
    Nat.mul_pos powered.sourcePower_pos (by dsimp [level]; omega)
  have hfixedPower :
      (source.power (powered.sourcePower * level)).IsFixedPoint sourceWord :=
    Substitution.isFixedPoint_power P.fixed hexponent
  have hone : (sourceWord.drop sourcePosition).take 1 =
      [sourceWord sourcePosition] := by
    rw [show 1 = 0 + 1 by omega, Stream'.take_succ']
    simp only [Stream'.take_zero, List.nil_append]
    change [sourceWord (0 + sourcePosition)] = [sourceWord sourcePosition]
    simp
  have himageAt : InfiniteFactorAt sourceWord
      (source.iterateLetter (powered.sourcePower * level)
        powered.coreSeed.1)
      ((source.power (powered.sourcePower * level)).mapWord
        (sourceWord.take sourcePosition)).length := by
    have himage := Substitution.mapWord_drop_take_at_fixed
      hfixedPower sourcePosition 1
    rw [hone, hseedAt] at himage
    simpa only [Substitution.mapWord_cons, Substitution.mapWord_nil,
      List.append_nil, Substitution.power_apply] using himage
  have hfinite : FiniteFactorAt
      (source.iterateLetter (powered.sourcePower * level)
        powered.coreSeed.1)
      ((fixed.coreWord.take length).map Subtype.val) 0 := by
    simpa using
      (finiteFactorAt_append_length_of_prefix
        (left := []) hdecodedPrefix)
  exact ⟨_, himageAt.of_finiteFactorAt hfinite⟩

/-- **A5e.** Package the canonical fixed word and its ambient embedding. -/
theorem poweredRecurrentCoreData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    (powered : PoweredRecurrentSubstitutionData restriction hprimitive) :
    Nonempty (PoweredRecurrentCoreData powered) := by
  obtain ⟨fixed⟩ := poweredRecurrentSubstitution_has_fixedData powered
  exact ⟨{
    toPoweredRecurrentFixedData := fixed
    decoded_prefix_factor :=
      poweredRecurrentFixed_decodedPrefixFactor fixed }⟩

/-- **A6a.** The powered restriction scales the literal pullback of the
ambient common metric by the powered ambient scale. -/
theorem poweredRecurrentCore_scalesRestrictedMetric
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    {powered : PoweredRecurrentSubstitutionData restriction hprimitive}
    (_core : PoweredRecurrentCoreData powered) :
    SubstitutionScalesLetterLengths powered.substitution
      (fun letter => sourceLength letter.1)
      (sourceScale ^ powered.sourcePower) := by
  intro letter
  have hambient := scalesLetterLengths_power
    P.scales powered.sourcePower letter.1
  have hmetric :
      wordMetricLength (fun output => sourceLength output.1)
          (powered.substitution letter) =
        wordMetricLength sourceLength
          ((powered.substitution letter).map Subtype.val) := by
    simp [wordMetricLength, List.map_map, Function.comp_def]
  rw [hmetric, powered.source_image]
  simpa only [Substitution.power_apply] using hambient

/-- **A6b.** Package the powered primitive fixed presentation.  Its metric is
definitionally the pullback of the one shared ambient metric. -/
theorem poweredRecurrentCore_metricPresentation
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    {powered : PoweredRecurrentSubstitutionData restriction hprimitive}
    (core : PoweredRecurrentCoreData powered) :
    MetricGrowingFixedPresentation powered.substitution core.coreWord.head
      core.coreWord (sourceScale ^ powered.sourcePower)
      (fun letter => sourceLength letter.1) := by
  letI : Nonempty (RecurrentLetter sourceWord) :=
    ⟨powered.coreSeed⟩
  have hscales := poweredRecurrentCore_scalesRestrictedMetric core
  have hone : 1 < sourceScale ^ powered.sourcePower :=
    one_lt_pow₀ P.one_lt_eigenvalue
      (Nat.ne_of_gt powered.sourcePower_pos)
  refine {
    nonerasing := powered.substitution.image_ne_nil
    prolongable := ?_
    fixed := core.fixed
    every_letter_occurs := core.every_letter_occurs
    growing := powered.growing
    one_lt_eigenvalue := hone
    dominant := dominantEigenvalue_of_positive_metric_scaling
      powered.substitution (fun letter => sourceLength letter.1)
      (sourceScale ^ powered.sourcePower)
      (fun letter => P.letterLength_pos letter.1) hscales
    letterLength_pos := fun letter => P.letterLength_pos letter.1
    scales := hscales
  }
  simpa only [core.coreSeed_eq_head] using powered.prolongable

/-! ### A7 support: primitive fixed words have bounded factor gaps -/

namespace Substitution

private theorem iterateWord_nil_a7 {β : Type u}
    (source : Substitution β) (level : ℕ) :
    source.iterateWord level [] = [] := by
  induction level with
  | zero => rfl
  | succ level ih =>
      simpa only [Substitution.iterateWord_succ, ih,
        Substitution.mapWord_nil]

private theorem iterateWord_append_a7 {β : Type u}
    (source : Substitution β) (level : ℕ) (left right : Word β) :
    source.iterateWord level (left ++ right) =
      source.iterateWord level left ++ source.iterateWord level right := by
  induction level with
  | zero => rfl
  | succ level ih =>
      simp only [Substitution.iterateWord_succ, ih,
        Substitution.mapWord_append]

private theorem iterateWord_add_a7 {β : Type u}
    (source : Substitution β) (left right : ℕ) (word : Word β) :
    source.iterateWord (left + right) word =
      source.iterateWord left (source.iterateWord right word) := by
  induction left with
  | zero => simp
  | succ left ih =>
      simpa only [Nat.succ_add, Substitution.iterateWord_succ] using
        congrArg source.mapWord ih

private theorem iterateWord_infix_a7 {β : Type u}
    (source : Substitution β) (level : ℕ)
    {small large : Word β} (hfactor : small <:+: large) :
    source.iterateWord level small <:+:
      source.iterateWord level large := by
  rcases hfactor with ⟨left, right, rfl⟩
  refine ⟨source.iterateWord level left,
    source.iterateWord level right, ?_⟩
  simp only [iterateWord_append_a7, List.append_assoc]

private theorem iterateLetter_infix_of_mem_iterate_a7
    {β : Type u} (source : Substitution β)
    {sourceLetter targetLetter : β} {first later : ℕ}
    (hmem : targetLetter ∈ source.iterateLetter first sourceLetter) :
    source.iterateLetter later targetLetter <:+:
      source.iterateLetter (later + first) sourceLetter := by
  have hsingle : [targetLetter] <:+:
      source.iterateLetter first sourceLetter :=
    (List.singleton_infix_iff targetLetter _).2 hmem
  have himage := iterateWord_infix_a7 source later hsingle
  change source.iterateLetter later targetLetter <:+:
    source.iterateWord later
      (source.iterateLetter first sourceLetter) at himage
  change source.iterateWord later [targetLetter] <:+:
    source.iterateWord (later + first) [sourceLetter]
  rw [iterateWord_add_a7]
  exact himage

private def maxIterateLengthA7 {β : Type u} [Fintype β]
    (source : Substitution β) (level : ℕ) : ℕ :=
  Finset.univ.sup fun letter : β =>
    (source.iterateLetter level letter).length

private theorem iterateLetter_length_le_max_a7
    {β : Type u} [Fintype β] (source : Substitution β)
    (level : ℕ) (letter : β) :
    (source.iterateLetter level letter).length ≤
      maxIterateLengthA7 source level := by
  exact Finset.le_sup
    (f := fun other : β =>
      (source.iterateLetter level other).length)
    (Finset.mem_univ letter)

private theorem length_le_mapWord_a7 {β : Type u}
    (source : Substitution β) (word : Word β) :
    word.length ≤ (source.mapWord word).length := by
  induction word with
  | nil => simp
  | cons letter rest ih =>
      rw [Substitution.mapWord_cons, List.length_append,
        List.length_cons]
      have hletter : 0 < (source letter).length :=
        List.length_pos_of_ne_nil (source.image_ne_nil letter)
      omega

private theorem length_le_iterateWord_a7 {β : Type u}
    (source : Substitution β) (level : ℕ) (word : Word β) :
    word.length ≤ (source.iterateWord level word).length := by
  induction level with
  | zero => exact le_rfl
  | succ level ih =>
      exact ih.trans
        (length_le_mapWord_a7 source
          (source.iterateWord level word))

private theorem isFixedPoint_power_all_a7 {β : Type u}
    {source : Substitution β} {word : InfiniteWord β}
    (hfixed : source.IsFixedPoint word) (level : ℕ) :
    (source.power level).IsFixedPoint word := by
  cases level with
  | zero => exact Substitution.mapInfinite_id word
  | succ level =>
      exact Substitution.isFixedPoint_power hfixed (Nat.succ_pos level)

private theorem iterateWord_drop_take_at_fixed_a7 {β : Type u}
    {source : Substitution β} {word : InfiniteWord β}
    (hfixed : source.IsFixedPoint word)
    (level start count : ℕ) :
    InfiniteFactorAt word
      (source.iterateWord level ((word.drop start).take count))
      (source.iterateWord level (word.take start)).length := by
  have h := Substitution.mapWord_drop_take_at_fixed
    (isFixedPoint_power_all_a7 hfixed level) start count
  simpa only [Substitution.power_mapWord] using h

/-- If a factor lies in every level image, the level tiling puts an
occurrence within two maximal image lengths of every starting point. -/
private theorem factor_appears_within_two_maxImages_a7
    {β : Type u} [Fintype β] [DecidableEq β]
    {source : Substitution β} {word : InfiniteWord β}
    (hfixed : source.IsFixedPoint word)
    {factor : Word β} (level : ℕ)
    (hevery : ∀ letter : β,
      factor <:+: source.iterateLetter level letter) :
    ∀ start : ℕ, ∃ position : ℕ,
      start ≤ position ∧
        position ≤ start + 2 * maxIterateLengthA7 source level ∧
        InfiniteFactorAt word factor position := by
  classical
  intro start
  let cut : ℕ → ℕ := fun index =>
    (source.iterateWord level (word.take index)).length
  have hcutZero : cut 0 = 0 := by
    simp [cut, iterateWord_nil_a7]
  have hcutSucc : ∀ index : ℕ,
      cut (index + 1) = cut index +
        (source.iterateLetter level (word index)).length := by
    intro index
    dsimp only [cut]
    rw [Stream'.take_succ', iterateWord_append_a7,
      List.length_append]
    rfl
  have hindexLeCut : ∀ index : ℕ, index ≤ cut index := by
    intro index
    simpa [cut] using
      length_le_iterateWord_a7 source level (word.take index)
  let candidates : Finset ℕ :=
    (Finset.range (start + 1)).filter fun index => cut index ≤ start
  have hzeroMem : 0 ∈ candidates := by simp [candidates, hcutZero]
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
      start + maxIterateLengthA7 source level := by
    have hstep := hcutSucc index
    have himageMax := iterateLetter_length_le_max_a7
      source level (word index)
    omega
  let sourceLetter := word (index + 1)
  rcases hevery sourceLetter with ⟨left, right, hsplit⟩
  have hfinite : FiniteFactorAt
      (source.iterateLetter level sourceLetter) factor left.length := by
    rw [← hsplit]
    simp [FiniteFactorAt]
  have htakeOne : (word.drop (index + 1)).take 1 = [sourceLetter] := by
    rw [show 1 = Nat.succ 0 by rfl, Stream'.take_succ]
    simp only [sourceLetter, Stream'.head_drop, Stream'.take_zero,
      List.cons.injEq, and_true]
    rfl
  have hblockAt : InfiniteFactorAt word
      (source.iterateLetter level sourceLetter) (cut (index + 1)) := by
    have hraw := iterateWord_drop_take_at_fixed_a7
      hfixed level (index + 1) 1
    rw [htakeOne] at hraw
    simpa [cut, sourceLetter] using hraw
  let position := cut (index + 1) + left.length
  have hposition : InfiniteFactorAt word factor position :=
    hblockAt.of_finiteFactorAt hfinite
  have hleftBound : left.length ≤ maxIterateLengthA7 source level := by
    have himageMax := iterateLetter_length_le_max_a7
      source level sourceLetter
    exact (Nat.le_add_right left.length factor.length).trans
      (hfinite.1.trans himageMax)
  refine ⟨position, by omega, ?_, hposition⟩
  dsimp only [position]
  omega

end Substitution

/-- A factor at a valid finite starting index is a list infix. -/
private theorem finiteFactorAt_isInfix_a7
    {β : Type u} {ambient factor : Word β} {start : ℕ}
    (hfactor : FiniteFactorAt ambient factor start) :
    factor <:+: ambient := by
  refine ⟨ambient.take start,
    ambient.drop (start + factor.length), ?_⟩
  calc
    ambient.take start ++ factor ++
        ambient.drop (start + factor.length) =
        ambient.take start ++
          ((ambient.drop start).take factor.length ++
            (ambient.drop start).drop factor.length) := by
      rw [hfactor.2, List.drop_drop]
      simp [List.append_assoc]
    _ = ambient.take start ++ ambient.drop start := by
      rw [List.take_append_drop]
    _ = ambient := List.take_append_drop _ _

/-- Every infix of an infinite factor is again an infinite factor. -/
private theorem isInfiniteFactor_of_infix_a8
    {β : Type u} {word : InfiniteWord β} {small large : Word β}
    (hlarge : IsInfiniteFactor word large) (hsmall : small <:+: large) :
    IsInfiniteFactor word small := by
  rcases hlarge with ⟨start, hlarge⟩
  rcases hsmall with ⟨left, right, rfl⟩
  let tail := word.drop start
  have hprefix :
      tail.take (left.length + small.length) = left ++ small := by
    calc
      tail.take (left.length + small.length) =
          (tail.take (left ++ small ++ right).length).take
            (left.length + small.length) := by
        simp [Stream'.take_take]
      _ = (left ++ small ++ right).take
          (left.length + small.length) := by rw [hlarge]
      _ = left ++ small := by simp [← List.append_assoc]
  have hleft : tail.take left.length = left := by
    calc
      tail.take left.length =
          (tail.take (left.length + small.length)).take left.length := by
        simp [Stream'.take_take]
      _ = (left ++ small).take left.length := by rw [hprefix]
      _ = left := by simp
  have hsplit := Stream'.take_add
    (a := tail) (m := left.length) (n := small.length)
  rw [hprefix, hleft] at hsplit
  have htail : (tail.drop left.length).take small.length = small :=
    List.append_cancel_left hsplit.symm
  refine ⟨start + left.length, ?_⟩
  simpa [InfiniteFactorAt, tail, Stream'.drop_drop] using htail

/-- **A7a.** A fixed word of the primitive powered restriction is uniformly
recurrent. -/
theorem poweredRecurrentCore_uniformlyRecurrent
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    {powered : PoweredRecurrentSubstitutionData restriction hprimitive}
    (core : PoweredRecurrentCoreData powered) :
    IsUniformlyRecurrent core.coreWord := by
  classical
  letI : Nonempty (RecurrentLetter sourceWord) := ⟨powered.coreSeed⟩
  intro factor hfactor
  obtain ⟨origin, horigin⟩ := hfactor
  obtain ⟨factorLevel, hfactorLevel⟩ := powered.growing
    powered.coreSeed (origin + factor.length)
  have hambientAt : InfiniteFactorAt core.coreWord
      (powered.substitution.iterateLetter factorLevel powered.coreSeed) 0 := by
    rw [InfiniteFactorAt]
    simpa only [Stream'.drop_zero] using
      (core.iterates_are_prefixes factorLevel).symm
  have hfinite : FiniteFactorAt
      (powered.substitution.iterateLetter factorLevel powered.coreSeed)
      factor origin :=
    finiteFactorAt_of_nested_infiniteFactorAt hambientAt
      (by simpa using horigin) hfactorLevel
  have hseedFactor : factor <:+:
      powered.substitution.iterateLetter factorLevel powered.coreSeed :=
    finiteFactorAt_isInfix_a7 hfinite
  obtain ⟨primitiveDepth, _hprimitiveDepth, hcontains⟩ :=
    powered.primitive
  let commonLevel := factorLevel + primitiveDepth
  have hevery : ∀ letter : RecurrentLetter sourceWord,
      factor <:+:
        powered.substitution.iterateLetter commonLevel letter := by
    intro letter
    have hseedMem := hcontains letter powered.coreSeed
    have hseedImage :=
      Substitution.iterateLetter_infix_of_mem_iterate_a7
        powered.substitution (later := factorLevel) hseedMem
    exact hseedFactor.trans hseedImage
  let gap := 2 * Substitution.maxIterateLengthA7
    powered.substitution commonLevel
  have hmaxPos : 0 < Substitution.maxIterateLengthA7
      powered.substitution commonLevel := by
    exact (List.length_pos_of_ne_nil
      (powered.substitution.iterateLetter_ne_nil
        commonLevel powered.coreSeed)).trans_le
      (Substitution.iterateLetter_length_le_max_a7
        powered.substitution commonLevel powered.coreSeed)
  refine ⟨gap, Nat.mul_pos (by omega) hmaxPos, ?_⟩
  intro start
  obtain ⟨position, hstart, hbound, hposition⟩ :=
    Substitution.factor_appears_within_two_maxImages_a7
      core.fixed commonLevel hevery start
  refine ⟨position - start, by omega, ?_⟩
  convert hposition using 1 <;> omega

/-- **A7b.** Every decoded core factor is recurrent in the ambient word. -/
theorem poweredRecurrentCore_decodedFactor_recurrent
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    {powered : PoweredRecurrentSubstitutionData restriction hprimitive}
    (core : PoweredRecurrentCoreData powered) :
    ∀ factor : Word α,
      IsInfiniteFactor
          (fun n => ((core.coreWord n : RecurrentLetter sourceWord) : α))
          factor →
        IsRecurrentFactor sourceWord factor := by
  classical
  intro factor hfactor
  obtain ⟨origin, horigin⟩ := hfactor
  let lifted : Word (RecurrentLetter sourceWord) :=
    (core.coreWord.drop origin).take factor.length
  have hliftedAt : InfiniteFactorAt core.coreWord lifted origin := by
    simp [InfiniteFactorAt, lifted]
  have hliftedMap : lifted.map Subtype.val = factor := by
    change ((core.coreWord.drop origin).take factor.length).map
      Subtype.val = factor
    change InfiniteFactorAt (Stream'.map Subtype.val core.coreWord)
      factor origin at horigin
    simpa [InfiniteFactorAt, Stream'.drop_map, Stream'.map_take] using horigin
  have hliftedLength : lifted.length = factor.length := by
    have hlength := congrArg List.length hliftedMap
    simpa using hlength
  have hliftedFactor : IsInfiniteFactor core.coreWord lifted :=
    ⟨origin, hliftedAt⟩
  have hliftedRecurrent : IsRecurrentFactor core.coreWord lifted :=
    (poweredRecurrentCore_uniformlyRecurrent core
      lifted hliftedFactor).isRecurrentFactor
  intro cutoff
  obtain ⟨position, hpositionCutoff, hliftedPosition⟩ :=
    hliftedRecurrent cutoff
  let prefixLength := position + lifted.length
  let decodedPrefix :=
    (core.coreWord.take prefixLength).map Subtype.val
  obtain ⟨ambientStart, hambientStart⟩ :=
    core.decoded_prefix_factor prefixLength
  have hprefixAt : InfiniteFactorAt core.coreWord
      (core.coreWord.take prefixLength) 0 := by
    simp [InfiniteFactorAt]
  have hfiniteCore : FiniteFactorAt
      (core.coreWord.take prefixLength) lifted position := by
    apply finiteFactorAt_of_nested_infiniteFactorAt hprefixAt
    · simpa using hliftedPosition
    · simp [prefixLength]
  have hfiniteDecoded : FiniteFactorAt decodedPrefix factor position := by
    rcases hfiniteCore with ⟨hwithin, heq⟩
    refine ⟨?_, ?_⟩
    · simpa [decodedPrefix, hliftedLength] using hwithin
    · simpa [decodedPrefix, List.map_drop, List.map_take,
        hliftedMap, hliftedLength] using
          congrArg (List.map Subtype.val) heq
  refine ⟨ambientStart + position,
    hpositionCutoff.trans (Nat.le_add_left position ambientStart), ?_⟩
  exact hambientStart.of_finiteFactorAt hfiniteDecoded

/-- **A8.** In a syndetic recurrent language, an infinite sublanguage made
entirely of recurrent factors is exactly the recurrent language. -/
theorem infiniteFactors_eq_recurrentFactors_of_subset
    {α : Type u} [Fintype α] [DecidableEq α]
    {sourceWord coreWord : InfiniteWord α}
    (hsyndetic : RecurrentFactorsSyndetic sourceWord)
    (hsubset : ∀ factor : Word α,
      IsInfiniteFactor coreWord factor →
        IsRecurrentFactor sourceWord factor) :
    ∀ factor : Word α,
      IsInfiniteFactor coreWord factor ↔
        IsRecurrentFactor sourceWord factor := by
  intro factor
  constructor
  · exact hsubset factor
  · intro hrecurrent
    obtain ⟨gap, _hgapPos, hgap⟩ := hsyndetic factor hrecurrent
    let ambient := coreWord.take (gap + factor.length)
    have hambientFactor : IsInfiniteFactor coreWord ambient := by
      refine ⟨0, ?_⟩
      simp [InfiniteFactorAt, ambient]
    have hambientRecurrent := hsubset ambient hambientFactor
    obtain ⟨start, _hstart, hambientAt⟩ := hambientRecurrent 0
    obtain ⟨offset, hoffset, hfactorAt⟩ := hgap start
    have hambientLength : ambient.length = gap + factor.length := by
      simp [ambient]
    have hfinite : FiniteFactorAt ambient factor offset :=
      finiteFactorAt_of_nested_infiniteFactorAt hambientAt hfactorAt (by
        rw [hambientLength]
        omega)
    exact isInfiniteFactor_of_infix_a8 hambientFactor
      (finiteFactorAt_isInfix_a7 hfinite)

/-- **A9.** Assemble the complete one-source primitive recurrent core on its
intrinsic finite subtype.  The decoder is definitionally `Subtype.val`. -/
theorem metricPrimitiveRecurrentCoreSide_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    (P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord) :
    Nonempty (MetricPrimitiveRecurrentCoreSide P) := by
  obtain ⟨restriction⟩ := recurrentAlphabetRestriction_exists P
  obtain ⟨hprimitive⟩ :=
    recurrentAlphabetRestriction_isPrimitive hsyndetic restriction
  have hgrowing := recurrentAlphabetRestriction_isGrowing restriction
  obtain ⟨powered⟩ :=
    primitiveGrowingRestriction_has_prolongablePower
      restriction hprimitive hgrowing
  obtain ⟨core⟩ :=
    poweredRecurrentCoreData_exists powered
  have hmetric := poweredRecurrentCore_metricPresentation core
  have hsubset := poweredRecurrentCore_decodedFactor_recurrent core
  have hlanguage :=
    infiniteFactors_eq_recurrentFactors_of_subset hsyndetic hsubset
  exact ⟨{
    component := recurrentLetterFinset sourceWord
    component_nonempty := restriction.recurrent_nonempty
    substitution := powered.substitution
    coreWord := core.coreWord
    sourcePower := powered.sourcePower
    sourcePower_pos := powered.sourcePower_pos
    source_image := powered.source_image
    primitive := powered.primitive
    presentation := hmetric
    decoded_language := hlanguage }⟩

/-- The powered source scale remains strictly greater than one. -/
theorem MetricPrimitiveRecurrentCoreSide.one_lt_poweredScale
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (side : MetricPrimitiveRecurrentCoreSide P) :
    1 < side.poweredScale := by
  exact one_lt_pow₀ P.one_lt_eigenvalue
    (Nat.ne_of_gt side.sourcePower_pos)

/-- **A10a.** Each side decodes exactly the same recurrent ambient language. -/
theorem MetricPairedRecurrentCoreData.same_decoded_language
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (pair : MetricPairedRecurrentCoreData Pleft Pright) :
    SameFactorLanguage pair.left.decodedWord pair.right.decodedWord := by
  intro factor
  exact (pair.left.decoded_language factor).trans
    (pair.right.decoded_language factor).symm

/-- **A10b.** Pair two separate cores without identifying their finite
alphabets or fixed words. -/
theorem metricPairedRecurrentCoreData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord) :
    Nonempty (MetricPairedRecurrentCoreData Pleft Pright) := by
  obtain ⟨left⟩ := metricPrimitiveRecurrentCoreSide_exists Pleft hsyndetic
  obtain ⟨right⟩ := metricPrimitiveRecurrentCoreSide_exists Pright hsyndetic
  exact ⟨⟨left, right⟩⟩

/-! ## Checked exact-metric helper for the later bridge -/

namespace PrimitiveCore

private theorem wordMetricLength_smul
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

private theorem wordMetricLength_mono
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

private theorem wordMetricLength_lt_of_pointwise_le_of_mem_lt
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
      · linarith [wordMetricLength_mono hle tail]
      · linarith [ih htail, hle head]

/-- Two positive metrics scaled by one primitive substitution at the same
scale are proportional.  This is the checked elementary min-ratio proof. -/
theorem positive_sameScale_metrics_proportional
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
    wordMetricLength_lt_of_pointwise_le_of_mem_lt
      hpointwise (hcontains pivot letter) hstrict
  have hwordEqual :
      wordMetricLength rightMetric (source.iterateLetter depth pivot) =
        wordMetricLength (fun other => coefficient * leftMetric other)
          (source.iterateLetter depth pivot) := by
    rw [hrightPower, wordMetricLength_smul, hleftPower, hpivot]
    ring
  exact (ne_of_lt hwordStrict) hwordEqual

end PrimitiveCore

end
end Symbolic
end CommutingIntervalSimplified
