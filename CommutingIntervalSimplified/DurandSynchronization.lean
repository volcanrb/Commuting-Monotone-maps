import CommutingIntervalSimplified.DurandPrimitiveCore

/-!
# Synchronizing two primitive recurrent cores

This module freezes the standalone synchronization layer used between the
one-source recurrent-core extraction and the same-word primitive comparison.
The key input is that the two ambient substitutions fix the same word and
scale the same strictly positive letter metric.  Equality of scaled prefix
coordinates then forces the two composite substitutions to have the same
letter images.  Their restrictions to the intrinsic recurrent alphabet
therefore commute.

Starting from a fixed word of a prolongable positive power of the left
restriction, we follow its orbit under the right restriction.  Every orbit
word is fixed by the same growing left power.  Finiteness of the alphabet
gives two orbit words with the same head; uniqueness of a growing fixed point
with prescribed head makes them equal and produces a word fixed by positive
powers of both substitutions.

The final record is relabelled once to `Fin rank`.  It has one literal word,
one injective decoder, and one pulled-back positive metric.  It does not
identify independently constructed core words or alphabets.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

open Function Set
open scoped BigOperators

noncomputable section

universe u v

/-! ## S1--S7: exact-cut commutation -/

/-- **S1.** Composition multiplies exact letter-length scales. -/
theorem SubstitutionScalesLetterLengths.comp
    {α : Type u} {left right : Substitution α}
    {letterLength : α → ℝ} {leftScale rightScale : ℝ}
    (hleft : SubstitutionScalesLetterLengths left letterLength leftScale)
    (hright : SubstitutionScalesLetterLengths right letterLength rightScale) :
    SubstitutionScalesLetterLengths (left.comp right) letterLength
      (leftScale * rightScale) := by
  intro letter
  change wordMetricLength letterLength (left.mapWord (right letter)) =
    (leftScale * rightScale) * letterLength letter
  rw [wordMetricLength_mapWord_of_scales hleft, hright letter]
  ring

/-- **S2.** A composite of two substitutions fixing one word fixes that
word. -/
theorem Substitution.IsFixedPoint.comp
    {α : Type u} {left right : Substitution α}
    {word : InfiniteWord α}
    (hleft : left.IsFixedPoint word) (hright : right.IsFixedPoint word) :
    (left.comp right).IsFixedPoint word := by
  change (left.comp right).mapInfinite word = word
  rw [Substitution.mapInfinite_comp, hright, hleft]

/-- **S3.** Two fixed substitutions with the same exact metric scale have
the same cut before every source position. -/
theorem substitutionBoundaries_eq_of_equalScale
    {α : Type u} {left right : Substitution α}
    {word : InfiniteWord α} {letterLength : α → ℝ} {scale : ℝ}
    (hleftFixed : left.IsFixedPoint word)
    (hrightFixed : right.IsFixedPoint word)
    (hleftScales :
      SubstitutionScalesLetterLengths left letterLength scale)
    (hrightScales :
      SubstitutionScalesLetterLengths right letterLength scale)
    (hlength : ∀ letter, 0 < letterLength letter) (position : ℕ) :
    substitutionBoundary left word position =
      substitutionBoundary right word position := by
  apply (prefixMetricLength_strictMono letterLength word hlength).injective
  rw [prefixMetricLength_substitutionBoundary
      hleftFixed hleftScales position,
    prefixMetricLength_substitutionBoundary
      hrightFixed hrightScales position]

/-- **S4.** Equality of the two adjacent cuts identifies the intervening
letter images. -/
theorem substitutionImages_eq_at_position_of_equalScale
    {α : Type u} {left right : Substitution α}
    {word : InfiniteWord α} {letterLength : α → ℝ} {scale : ℝ}
    (hleftFixed : left.IsFixedPoint word)
    (hrightFixed : right.IsFixedPoint word)
    (hleftScales :
      SubstitutionScalesLetterLengths left letterLength scale)
    (hrightScales :
      SubstitutionScalesLetterLengths right letterLength scale)
    (hlength : ∀ letter, 0 < letterLength letter) (position : ℕ) :
    left (word position) = right (word position) := by
  have hstart := substitutionBoundaries_eq_of_equalScale
    hleftFixed hrightFixed hleftScales hrightScales hlength position
  have hend := substitutionBoundaries_eq_of_equalScale
    hleftFixed hrightFixed hleftScales hrightScales hlength (position + 1)
  have hleftSucc :
      substitutionBoundary left word (position + 1) =
        substitutionBoundary left word position +
          (left (word position)).length := by
    unfold substitutionBoundary
    rw [Stream'.take_succ']
    simp only [Substitution.mapWord_append,
      List.length_append]
    change List.length (left.mapWord (word.take position)) +
        List.length (left.mapWord [word position]) =
      List.length (left.mapWord (word.take position)) +
        List.length (left (word position))
    simp [Substitution.mapWord]
  have hrightSucc :
      substitutionBoundary right word (position + 1) =
        substitutionBoundary right word position +
          (right (word position)).length := by
    unfold substitutionBoundary
    rw [Stream'.take_succ']
    simp only [Substitution.mapWord_append,
      List.length_append]
    change List.length (right.mapWord (word.take position)) +
        List.length (right.mapWord [word position]) =
      List.length (right.mapWord (word.take position)) +
        List.length (right (word position))
    simp [Substitution.mapWord]
  have hlengthEq :
      (left (word position)).length = (right (word position)).length := by
    omega
  have hleftAt : InfiniteFactorAt word (left (word position))
      (substitutionBoundary left word position) := by
    have h := Substitution.mapWord_drop_take_at_fixed
      hleftFixed position 1
    simpa [substitutionBoundary, Stream'.take_succ'] using h
  have hrightAt : InfiniteFactorAt word (right (word position))
      (substitutionBoundary right word position) := by
    have h := Substitution.mapWord_drop_take_at_fixed
      hrightFixed position 1
    simpa [substitutionBoundary, Stream'.take_succ'] using h
  rw [InfiniteFactorAt] at hleftAt hrightAt
  rw [hstart, hlengthEq] at hleftAt
  exact hleftAt.symm.trans hrightAt

/-- **S5.** The preceding image equality can be transported from an
occurrence of a named letter. -/
theorem substitutionImages_eq_of_occurs_of_equalScale
    {α : Type u} {left right : Substitution α}
    {word : InfiniteWord α} {letterLength : α → ℝ} {scale : ℝ}
    (hleftFixed : left.IsFixedPoint word)
    (hrightFixed : right.IsFixedPoint word)
    (hleftScales :
      SubstitutionScalesLetterLengths left letterLength scale)
    (hrightScales :
      SubstitutionScalesLetterLengths right letterLength scale)
    (hlength : ∀ letter, 0 < letterLength letter)
    {letter : α} (hoccurs : Substitution.OccursInInfiniteWord letter word) :
    left letter = right letter := by
  obtain ⟨position, hposition⟩ := hoccurs
  rw [← hposition]
  exact substitutionImages_eq_at_position_of_equalScale
    hleftFixed hrightFixed hleftScales hrightScales hlength position

/-- Equality of all letter images determines a substitution. -/
theorem Substitution.ext_image
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

/-- **S6.** If every letter occurs, a common fixed word and one positive
exact metric determine a substitution at a prescribed scale. -/
theorem substitutions_eq_of_commonFixedPositiveMetric
    {α : Type u} {left right : Substitution α}
    {word : InfiniteWord α} {letterLength : α → ℝ} {scale : ℝ}
    (hleftFixed : left.IsFixedPoint word)
    (hrightFixed : right.IsFixedPoint word)
    (hleftScales :
      SubstitutionScalesLetterLengths left letterLength scale)
    (hrightScales :
      SubstitutionScalesLetterLengths right letterLength scale)
    (hlength : ∀ letter, 0 < letterLength letter)
    (hoccurs : ∀ letter, Substitution.OccursInInfiniteWord letter word) :
    left = right := by
  exact Substitution.ext_image left right fun letter =>
    substitutionImages_eq_of_occurs_of_equalScale
      hleftFixed hrightFixed hleftScales hrightScales hlength
        (hoccurs letter)

/-- **S7.** Two substitutions fixing one everywhere-occurring word and
scaling the same positive metric commute.  The two composites have the same
scale because real multiplication is commutative. -/
theorem metricFixedPresentations_commute
    {α : Type u} [Fintype α] [DecidableEq α]
    {left right : Substitution α} {seed : α}
    {word : InfiniteWord α} {leftScale rightScale : ℝ}
    {letterLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation left seed word
      leftScale letterLength)
    (Pright : MetricGrowingFixedPresentation right seed word
      rightScale letterLength) :
    left.comp right = right.comp left := by
  apply substitutions_eq_of_commonFixedPositiveMetric
    (Pleft.fixed.comp Pright.fixed)
    (Pright.fixed.comp Pleft.fixed)
    (SubstitutionScalesLetterLengths.comp Pleft.scales Pright.scales)
  · simpa [mul_comm] using
      SubstitutionScalesLetterLengths.comp Pright.scales Pleft.scales
  · exact Pleft.letterLength_pos
  · exact Pleft.every_letter_occurs

/-- **S8.** The two intrinsic recurrent-alphabet restrictions commute.
Injectivity of `Subtype.val` turns ambient image equality into literal word
equality on the subtype. -/
theorem recurrentAlphabetRestrictions_commute
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (leftRestriction : RecurrentAlphabetRestrictionData Pleft)
    (rightRestriction : RecurrentAlphabetRestrictionData Pright) :
    leftRestriction.substitution.comp rightRestriction.substitution =
      rightRestriction.substitution.comp leftRestriction.substitution := by
  have hleftMapWord (letters : Word (RecurrentLetter sourceWord)) :
      (leftRestriction.substitution.mapWord letters).map Subtype.val =
        leftSource.mapWord (letters.map Subtype.val) := by
    induction letters with
    | nil => rfl
    | cons head tail ih =>
        simp only [Substitution.mapWord_cons, List.map_append,
          List.map_cons, leftRestriction.forget_image, ih]
  have hrightMapWord (letters : Word (RecurrentLetter sourceWord)) :
      (rightRestriction.substitution.mapWord letters).map Subtype.val =
        rightSource.mapWord (letters.map Subtype.val) := by
    induction letters with
    | nil => rfl
    | cons head tail ih =>
        simp only [Substitution.mapWord_cons, List.map_append,
          List.map_cons, rightRestriction.forget_image, ih]
  have hambient := metricFixedPresentations_commute Pleft Pright
  apply Substitution.ext_image
  intro letter
  apply (List.map_injective_iff.mpr Subtype.val_injective)
  calc
    ((leftRestriction.substitution.comp
          rightRestriction.substitution) letter).map Subtype.val =
        leftSource.mapWord (rightSource letter.1) := by
      change (leftRestriction.substitution.mapWord
          (rightRestriction.substitution letter)).map Subtype.val = _
      rw [hleftMapWord, rightRestriction.forget_image]
    _ = rightSource.mapWord (leftSource letter.1) := by
      simpa using congrArg
        (fun source : Substitution α => source letter.1) hambient
    _ = ((rightRestriction.substitution.comp
          leftRestriction.substitution) letter).map Subtype.val := by
      change _ = (rightRestriction.substitution.mapWord
          (leftRestriction.substitution letter)).map Subtype.val
      rw [hrightMapWord, leftRestriction.forget_image]

/-! ## O1--O10: a common word from a finite commuting orbit -/

private theorem Substitution.iterateWord_add_sync
    {α : Type u} (source : Substitution α) (left right : ℕ)
    (letters : Word α) :
    source.iterateWord (left + right) letters =
      source.iterateWord left (source.iterateWord right letters) := by
  induction left with
  | zero => simp
  | succ left ih =>
      simpa only [Nat.succ_add, Substitution.iterateWord_succ] using
        congrArg source.mapWord ih

private theorem Substitution.iterateWord_append_sync
    {α : Type u} (source : Substitution α) (power : ℕ)
    (left right : Word α) :
    source.iterateWord power (left ++ right) =
      source.iterateWord power left ++ source.iterateWord power right := by
  induction power with
  | zero => rfl
  | succ power ih =>
      simp only [Substitution.iterateWord_succ, ih,
        Substitution.mapWord_append]

private theorem Substitution.iterateWord_infix_sync
    {α : Type u} (source : Substitution α) (power : ℕ)
    {small large : Word α} (hfactor : small <:+: large) :
    source.iterateWord power small <:+:
      source.iterateWord power large := by
  rcases hfactor with ⟨left, right, rfl⟩
  refine ⟨source.iterateWord power left,
    source.iterateWord power right, ?_⟩
  simp only [source.iterateWord_append_sync, List.append_assoc]

private theorem Substitution.iterateWord_power_sync
    {α : Type u} (source : Substitution α) (power depth : ℕ)
    (letters : Word α) :
    (source.power power).iterateWord depth letters =
      source.iterateWord (power * depth) letters := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      calc
        (source.power power).iterateWord (depth + 1) letters =
            (source.power power).mapWord
              ((source.power power).iterateWord depth letters) := rfl
        _ = source.iterateWord power
              ((source.power power).iterateWord depth letters) :=
          Substitution.power_mapWord source power _
        _ = source.iterateWord power
              (source.iterateWord (power * depth) letters) :=
          congrArg (source.iterateWord power) ih
        _ = source.iterateWord (power + power * depth) letters :=
          (source.iterateWord_add_sync power (power * depth) letters).symm
        _ = source.iterateWord (power * (depth + 1)) letters := by
          rw [Nat.mul_succ, Nat.add_comm]

private theorem Substitution.iterateLetter_power_sync
    {α : Type u} (source : Substitution α) (power depth : ℕ)
    (letter : α) :
    (source.power power).iterateLetter depth letter =
      source.iterateLetter (power * depth) letter :=
  source.iterateWord_power_sync power depth [letter]

private theorem Substitution.primitive_contains_at_later_sync
    {α : Type u} (source : Substitution α) {depth later : ℕ}
    (hcontains : ∀ sourceLetter targetLetter,
      targetLetter ∈ source.iterateLetter depth sourceLetter)
    (hdepth : depth ≤ later) :
    ∀ sourceLetter targetLetter,
      targetLetter ∈ source.iterateLetter later sourceLetter := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hdepth
  intro sourceLetter targetLetter
  have hnonempty := source.iterateLetter_ne_nil extra sourceLetter
  obtain ⟨middle, tail, hmiddle⟩ := List.exists_cons_of_ne_nil hnonempty
  have hmiddleMem : middle ∈ source.iterateLetter extra sourceLetter := by
    rw [hmiddle]
    simp
  have hsingle : [middle] <:+:
      source.iterateLetter extra sourceLetter :=
    (List.singleton_infix_iff middle _).2 hmiddleMem
  have himage := source.iterateWord_infix_sync depth hsingle
  have htargetSmall : [targetLetter] <:+:
      source.iterateLetter depth middle :=
    (List.singleton_infix_iff targetLetter _).2
      (hcontains middle targetLetter)
  have htargetLarge := htargetSmall.trans himage
  change [targetLetter] <:+:
    source.iterateWord depth
      (source.iterateWord extra [sourceLetter]) at htargetLarge
  rw [← source.iterateWord_add_sync depth extra [sourceLetter]] at htargetLarge
  exact (List.singleton_infix_iff targetLetter _).1 htargetLarge

private theorem Substitution.iterateLetter_length_mono_sync
    {α : Type u} (source : Substitution α) (letter : α) :
    Monotone (fun iterate => (source.iterateLetter iterate letter).length) := by
  apply monotone_nat_of_le_succ
  intro iterate
  rw [Substitution.iterateLetter_succ]
  exact source.length_le_mapWord _

/-- **O1.** Positive powers preserve the primitive common-depth property. -/
theorem PrimitiveCore.IsPrimitiveSubstitution.power
    {α : Type u} [Fintype α]
    {source : Substitution α}
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source)
    {power : ℕ} (hpower : 0 < power) :
    PrimitiveCore.IsPrimitiveSubstitution (source.power power) := by
  obtain ⟨depth, hdepth, hcontains⟩ := hprimitive
  refine ⟨depth, hdepth, ?_⟩
  intro sourceLetter targetLetter
  rw [source.iterateLetter_power_sync]
  apply source.primitive_contains_at_later_sync hcontains
  nlinarith

/-- **O2.** Positive powers of a growing substitution are growing. -/
theorem Substitution.IsGrowing.power
    {α : Type u} {source : Substitution α}
    (hgrowing : source.IsGrowing) {power : ℕ} (hpower : 0 < power) :
    (source.power power).IsGrowing := by
  intro letter bound
  obtain ⟨level, hlevel⟩ := hgrowing letter bound
  refine ⟨level, ?_⟩
  rw [source.iterateLetter_power_sync]
  exact hlevel.trans
    (source.iterateLetter_length_mono_sync letter (by nlinarith))

private theorem Substitution.mapWord_comp_sync
    {α : Type u} (outer inner : Substitution α) (letters : Word α) :
    (outer.comp inner).mapWord letters =
      outer.mapWord (inner.mapWord letters) := by
  induction letters with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem Substitution.mapWord_id_sync
    {α : Type u} (letters : Word α) :
    (Substitution.id : Substitution α).mapWord letters = letters := by
  induction letters with
  | nil => rfl
  | cons head tail ih => simp [ih]

private theorem Substitution.comp_assoc_sync
    {α : Type u} (first second third : Substitution α) :
    (first.comp second).comp third =
      first.comp (second.comp third) := by
  apply Substitution.ext_image
  intro letter
  change (first.comp second).mapWord (third letter) =
    first.mapWord (second.mapWord (third letter))
  exact first.mapWord_comp_sync second (third letter)

private theorem Substitution.id_comp_sync
    {α : Type u} (source : Substitution α) :
    Substitution.id.comp source = source := by
  apply Substitution.ext_image
  intro letter
  exact Substitution.mapWord_id_sync (source letter)

private theorem Substitution.comp_id_sync
    {α : Type u} (source : Substitution α) :
    source.comp Substitution.id = source := by
  apply Substitution.ext_image
  intro letter
  simp [Substitution.mapWord]

private theorem Substitution.power_add_sync
    {α : Type u} (source : Substitution α) (left right : ℕ) :
    source.power (left + right) =
      (source.power left).comp (source.power right) := by
  induction left with
  | zero =>
      simpa using (source.power right).id_comp_sync.symm
  | succ left ih =>
      rw [Nat.succ_add]
      calc
        source.power (left + right + 1) =
            source.comp (source.power (left + right)) := rfl
        _ = source.comp
              ((source.power left).comp (source.power right)) := by
          rw [ih]
        _ = (source.comp (source.power left)).comp
              (source.power right) :=
          (source.comp_assoc_sync (source.power left)
            (source.power right)).symm
        _ = (source.power (left + 1)).comp
              (source.power right) := rfl

private theorem Substitution.commute_right_power_sync
    {α : Type u} {left right : Substitution α}
    (hcommute : left.comp right = right.comp left) :
    ∀ power : ℕ,
      left.comp (right.power power) =
        (right.power power).comp left := by
  intro power
  induction power with
  | zero =>
      rw [Substitution.power_zero, left.comp_id_sync,
        Substitution.id_comp_sync]
  | succ power ih =>
      calc
        left.comp (right.power (power + 1)) =
            left.comp (right.comp (right.power power)) := rfl
        _ = (left.comp right).comp (right.power power) :=
          (left.comp_assoc_sync right (right.power power)).symm
        _ = (right.comp left).comp (right.power power) := by
          rw [hcommute]
        _ = right.comp (left.comp (right.power power)) :=
          right.comp_assoc_sync left (right.power power)
        _ = right.comp ((right.power power).comp left) := by
          rw [ih]
        _ = (right.comp (right.power power)).comp left :=
          (right.comp_assoc_sync (right.power power) left).symm
        _ = (right.power (power + 1)).comp left := rfl

/-- **O3.** Powers of two commuting substitutions still commute. -/
theorem Substitution.powers_commute
    {α : Type u} {left right : Substitution α}
    (hcommute : left.comp right = right.comp left)
    (leftPower rightPower : ℕ) :
    (left.power leftPower).comp (right.power rightPower) =
      (right.power rightPower).comp (left.power leftPower) := by
  induction leftPower with
  | zero =>
      rw [Substitution.power_zero, Substitution.id_comp_sync,
        Substitution.comp_id_sync]
  | succ leftPower ih =>
      have hleftRight := left.commute_right_power_sync hcommute rightPower
      calc
        (left.power (leftPower + 1)).comp (right.power rightPower) =
            (left.comp (left.power leftPower)).comp
              (right.power rightPower) := rfl
        _ = left.comp ((left.power leftPower).comp
              (right.power rightPower)) :=
          left.comp_assoc_sync (left.power leftPower)
            (right.power rightPower)
        _ = left.comp ((right.power rightPower).comp
              (left.power leftPower)) := by rw [ih]
        _ = (left.comp (right.power rightPower)).comp
              (left.power leftPower) :=
          (left.comp_assoc_sync (right.power rightPower)
            (left.power leftPower)).symm
        _ = ((right.power rightPower).comp left).comp
              (left.power leftPower) := by rw [hleftRight]
        _ = (right.power rightPower).comp
              (left.comp (left.power leftPower)) :=
          (right.power rightPower).comp_assoc_sync left
            (left.power leftPower)
        _ = (right.power rightPower).comp
              (left.power (leftPower + 1)) := rfl

/-- **O4.** Applying a commuting substitution to a fixed point produces
another fixed point. -/
theorem Substitution.IsFixedPoint.mapInfinite_of_commute
    {α : Type u} {left right : Substitution α}
    {word : InfiniteWord α}
    (hcommute : left.comp right = right.comp left)
    (hfixed : left.IsFixedPoint word) :
    left.IsFixedPoint (right.mapInfinite word) := by
  change left.mapInfinite (right.mapInfinite word) =
    right.mapInfinite word
  rw [← Substitution.mapInfinite_comp, hcommute,
    Substitution.mapInfinite_comp, hfixed]

/-- **O5.** The whole right-power orbit remains in the fixed-point set of
the commuting left substitution. -/
theorem Substitution.IsFixedPoint.powerOrbit_of_commute
    {α : Type u} {left right : Substitution α}
    {word : InfiniteWord α}
    (hcommute : left.comp right = right.comp left)
    (hfixed : left.IsFixedPoint word) (power : ℕ) :
    left.IsFixedPoint ((right.power power).mapInfinite word) := by
  have hone : left.power 1 = left := by
    change left.comp Substitution.id = left
    exact left.comp_id_sync
  have hpowerCommute := left.powers_commute hcommute 1 power
  rw [hone] at hpowerCommute
  exact hfixed.mapInfinite_of_commute hpowerCommute

/-- **O6.** Two fixed points of one growing substitution with the same head
are equal. -/
theorem fixedPoints_eq_of_head_of_growing
    {α : Type u} {source : Substitution α}
    {leftWord rightWord : InfiniteWord α}
    (hgrowing : source.IsGrowing)
    (hleftFixed : source.IsFixedPoint leftWord)
    (hrightFixed : source.IsFixedPoint rightWord)
    (hhead : leftWord.head = rightWord.head) :
    leftWord = rightWord := by
  apply Stream'.ext
  intro position
  obtain ⟨level, hlevel⟩ :=
    hgrowing leftWord.head (position + 1)
  have hposition : position <
      (source.iterateLetter level leftWord.head).length := by
    omega
  have hleftPrefix :=
    iterateLetter_eq_fixedPoint_prefix hleftFixed level
  have hrightPrefix :=
    iterateLetter_eq_fixedPoint_prefix hrightFixed level
  rw [← hhead] at hrightPrefix
  have hleftGet := Stream'.take_get
    (a := leftWord) (m := position)
    (n := (source.iterateLetter level leftWord.head).length)
    (by simpa [← hleftPrefix] using hposition)
  have hrightGet := Stream'.take_get
    (a := rightWord) (m := position)
    (n := (source.iterateLetter level leftWord.head).length)
    (by simpa [← hrightPrefix] using hposition)
  rw [← hleftGet, ← hrightGet, ← Option.some_inj,
    ← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem,
    ← hleftPrefix, ← hrightPrefix]

private theorem FiniteFactorAt.isInfix_sync
    {α : Type u} {ambient factor : Word α} {start : ℕ}
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

private theorem finiteFactorAt_exists_of_isInfix_sync
    {α : Type u} {ambient factor : Word α}
    (hfactor : factor <:+: ambient) :
    ∃ start, FiniteFactorAt ambient factor start := by
  rcases hfactor with ⟨left, right, hsplit⟩
  refine ⟨left.length, ?_⟩
  rw [← hsplit]
  constructor <;> simp

/-- **O7.** A primitive growing substitution has one finite-factor language
on all of its fixed points. -/
theorem primitiveGrowingFixedPoints_sameFactorLanguage
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {leftWord rightWord : InfiniteWord α}
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source)
    (hgrowing : source.IsGrowing)
    (hleftFixed : source.IsFixedPoint leftWord)
    (hrightFixed : source.IsFixedPoint rightWord) :
    SameFactorLanguage leftWord rightWord := by
  have transfer (firstWord secondWord : InfiniteWord α)
      (hfirstFixed : source.IsFixedPoint firstWord)
      (hsecondFixed : source.IsFixedPoint secondWord) :
      ∀ factor : Word α,
        IsInfiniteFactor firstWord factor →
          IsInfiniteFactor secondWord factor := by
    intro factor hfactor
    obtain ⟨position, hfactorAt⟩ := hfactor
    obtain ⟨level, hlevel⟩ :=
      hgrowing firstWord.head (position + factor.length)
    have hfirstPrefix :=
      iterateLetter_eq_fixedPoint_prefix hfirstFixed level
    have hfirstPrefixAt : InfiniteFactorAt firstWord
        (source.iterateLetter level firstWord.head) 0 := by
      rw [hfirstPrefix]
      simp [InfiniteFactorAt]
    have hfactorFinite : FiniteFactorAt
        (source.iterateLetter level firstWord.head) factor position :=
      finiteFactorAt_of_nested_infiniteFactorAt hfirstPrefixAt
        (by simpa using hfactorAt) hlevel
    obtain ⟨depth, _hdepth, hcontains⟩ := hprimitive
    have hheadMem : firstWord.head ∈
        source.iterateLetter depth secondWord.head :=
      hcontains secondWord.head firstWord.head
    have hsingle : [firstWord.head] <:+:
        source.iterateLetter depth secondWord.head :=
      (List.singleton_infix_iff firstWord.head _).2 hheadMem
    have himage := source.iterateWord_infix_sync level hsingle
    change source.iterateLetter level firstWord.head <:+:
      source.iterateWord level
        (source.iterateLetter depth secondWord.head) at himage
    have hadd :
        source.iterateLetter (level + depth) secondWord.head =
          source.iterateWord level
            (source.iterateLetter depth secondWord.head) := by
      exact source.iterateWord_add_sync level depth [secondWord.head]
    rw [← hadd] at himage
    have hfactorLarge : factor <:+:
        source.iterateLetter (level + depth) secondWord.head :=
      hfactorFinite.isInfix_sync.trans himage
    obtain ⟨newPosition, hfactorLargeAt⟩ :=
      finiteFactorAt_exists_of_isInfix_sync hfactorLarge
    have hsecondPrefix :=
      iterateLetter_eq_fixedPoint_prefix hsecondFixed (level + depth)
    have hsecondPrefixAt : InfiniteFactorAt secondWord
        (source.iterateLetter (level + depth) secondWord.head) 0 := by
      rw [hsecondPrefix]
      simp [InfiniteFactorAt]
    exact ⟨newPosition, by
      simpa using hsecondPrefixAt.of_finiteFactorAt hfactorLargeAt⟩
  intro factor
  exact ⟨transfer leftWord rightWord hleftFixed hrightFixed factor,
    transfer rightWord leftWord hrightFixed hleftFixed factor⟩

/-- **O8.** Every letter occurs in every fixed point of a primitive
substitution. -/
theorem primitiveFixedPoint_everyLetterOccurs
    {α : Type u} [Fintype α]
    {source : Substitution α} {word : InfiniteWord α}
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source)
    (hfixed : source.IsFixedPoint word) :
    ∀ letter, Substitution.OccursInInfiniteWord letter word := by
  obtain ⟨depth, _hdepth, hcontains⟩ := hprimitive
  intro letter
  let image := source.iterateLetter depth word.head
  have himagePrefix := iterateLetter_eq_fixedPoint_prefix hfixed depth
  have hletter : letter ∈ image := hcontains word.head letter
  have hletter' : letter ∈ word.take image.length := by
    rw [← himagePrefix]
    exact hletter
  rw [List.mem_iff_getElem] at hletter'
  obtain ⟨position, hposition, hat⟩ := hletter'
  exact ⟨position, by simpa using hat⟩

/-- Repetition data for the heads of a substitution orbit. -/
structure FiniteHeadOrbitRepetition
    {α : Type u} [Fintype α]
    (source : Substitution α) (word : InfiniteWord α) where
  earlier : ℕ
  later : ℕ
  earlier_lt_later : earlier < later
  heads_eq :
    ((source.power earlier).mapInfinite word).head =
      ((source.power later).mapInfinite word).head

/-- **O9.** Finiteness of the alphabet forces two distinct orbit times to
have the same head. -/
theorem finiteHeadOrbitRepetition_exists
    {α : Type u} [Fintype α]
    (source : Substitution α) (word : InfiniteWord α) :
    Nonempty (FiniteHeadOrbitRepetition source word) := by
  obtain ⟨first, second, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun power : ℕ => ((source.power power).mapInfinite word).head)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨⟨first, second, hlt, heq⟩⟩
  · exact ⟨⟨second, first, hgt, heq.symm⟩⟩

/-- A point on the right orbit which is fixed by the left substitution and
by a positive right power. -/
structure CommonPowerFixedOrbitData
    {α : Type u} [Fintype α] [DecidableEq α]
    (left right : Substitution α) (baseWord : InfiniteWord α) where
  orbitStart : ℕ
  rightPower : ℕ
  rightPower_pos : 0 < rightPower
  commonWord : InfiniteWord α
  commonWord_eq :
    commonWord = (right.power orbitStart).mapInfinite baseWord
  left_fixed : left.IsFixedPoint commonWord
  right_fixed : (right.power rightPower).IsFixedPoint commonWord
  same_language : SameFactorLanguage baseWord commonWord

/-- **O10.** Repeated heads in the commuting orbit give a literal common
fixed word for a positive right power. -/
theorem commonPowerFixedOrbitData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {left right : Substitution α} {baseWord : InfiniteWord α}
    (hleftPrimitive : PrimitiveCore.IsPrimitiveSubstitution left)
    (hleftGrowing : left.IsGrowing)
    (hleftFixed : left.IsFixedPoint baseWord)
    (hcommute : left.comp right = right.comp left) :
    Nonempty (CommonPowerFixedOrbitData left right baseWord) := by
  obtain ⟨repetition⟩ :=
    finiteHeadOrbitRepetition_exists right baseWord
  let commonWord :=
    (right.power repetition.earlier).mapInfinite baseWord
  have hleftEarlier : left.IsFixedPoint commonWord := by
    dsimp only [commonWord]
    exact hleftFixed.powerOrbit_of_commute hcommute repetition.earlier
  have hleftLater : left.IsFixedPoint
      ((right.power repetition.later).mapInfinite baseWord) :=
    hleftFixed.powerOrbit_of_commute hcommute repetition.later
  have horbitEq :
      commonWord = (right.power repetition.later).mapInfinite baseWord := by
    apply fixedPoints_eq_of_head_of_growing hleftGrowing
      hleftEarlier hleftLater
    exact repetition.heads_eq
  let rightPower := repetition.later - repetition.earlier
  have hrightPower : 0 < rightPower := by
    dsimp only [rightPower]
    exact Nat.sub_pos_of_lt repetition.earlier_lt_later
  have hsum : rightPower + repetition.earlier = repetition.later := by
    dsimp only [rightPower]
    omega
  have hrightFixed :
      (right.power rightPower).IsFixedPoint commonWord := by
    change (right.power rightPower).mapInfinite commonWord = commonWord
    dsimp only [commonWord]
    rw [← Substitution.mapInfinite_comp,
      ← right.power_add_sync, hsum]
    exact horbitEq.symm
  have hlanguage : SameFactorLanguage baseWord commonWord :=
    primitiveGrowingFixedPoints_sameFactorLanguage hleftPrimitive
      hleftGrowing hleftFixed hleftEarlier
  exact ⟨{
    orbitStart := repetition.earlier
    rightPower := rightPower
    rightPower_pos := hrightPower
    commonWord := commonWord
    commonWord_eq := rfl
    left_fixed := hleftEarlier
    right_fixed := hrightFixed
    same_language := hlanguage
  }⟩

/-! ## P1--P7: intrinsic synchronized core -/

private theorem recurrentAlphabetRestriction_mapWord_forget
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (restriction : RecurrentAlphabetRestrictionData P) :
    ∀ letters : Word (RecurrentLetter sourceWord),
      (restriction.substitution.mapWord letters).map Subtype.val =
        source.mapWord (letters.map Subtype.val) := by
  intro letters
  induction letters with
  | nil => rfl
  | cons head tail ih =>
      simp only [Substitution.mapWord_cons, List.map_append,
        List.map_cons, restriction.forget_image, ih]

/-- Iterated restricted images still decode to the corresponding ambient
source power. -/
theorem recurrentAlphabetRestriction_power_forget
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    (restriction : RecurrentAlphabetRestrictionData P)
    (power : ℕ) (letter : RecurrentLetter sourceWord) :
    ((restriction.substitution.power power) letter).map Subtype.val =
      (source.power power) letter.1 := by
  simp only [Substitution.power_apply]
  induction power with
  | zero => rfl
  | succ power ih =>
      rw [Substitution.iterateLetter_succ,
        Substitution.iterateLetter_succ,
        recurrentAlphabetRestriction_mapWord_forget restriction, ih]

/-- A primitive growing fixed point with an exact positive expanding metric
is a complete metric presentation. -/
theorem metricGrowingFixedPresentation_of_primitiveFixedScaling
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {word : InfiniteWord α}
    {scale : ℝ} {letterLength : α → ℝ}
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source)
    (hgrowing : source.IsGrowing)
    (hfixed : source.IsFixedPoint word)
    (hlength : ∀ letter, 0 < letterLength letter)
    (hscale :
      SubstitutionScalesLetterLengths source letterLength scale)
    (hone : 1 < scale) :
    MetricGrowingFixedPresentation source word.head word scale letterLength := by
  letI : Nonempty α := ⟨word.head⟩
  exact {
    nonerasing := source.image_ne_nil
    prolongable := prolongableOn_head_of_growing_fixedPoint hfixed hgrowing
    fixed := hfixed
    every_letter_occurs :=
      primitiveFixedPoint_everyLetterOccurs hprimitive hfixed
    growing := hgrowing
    one_lt_eigenvalue := hone
    dominant := dominantEigenvalue_of_positive_metric_scaling
      source letterLength scale hlength hscale
    letterLength_pos := hlength
    scales := hscale
  }

private theorem InfiniteFactorAt.map_sync
    {α : Type u} {β : Type v} (coding : α → β)
    {word : InfiniteWord α} {factor : Word α} {start : ℕ}
    (hfactor : InfiniteFactorAt word factor start) :
    InfiniteFactorAt (fun n => coding (word n))
      (factor.map coding) start := by
  change InfiniteFactorAt (Stream'.map coding word)
    (factor.map coding) start
  unfold InfiniteFactorAt at hfactor ⊢
  have hmapped := congrArg (List.map coding) hfactor
  simpa [Stream'.drop_map, Stream'.map_take] using hmapped

/-- Injective letter coding transports equality of finite-factor
languages in both directions. -/
theorem SameFactorLanguage.map_of_injective
    {α : Type u} {β : Type v}
    {left right : InfiniteWord α} (coding : α → β)
    (hcoding : Injective coding)
    (hlanguage : SameFactorLanguage left right) :
    SameFactorLanguage (fun n => coding (left n))
      (fun n => coding (right n)) := by
  have transfer (first second : InfiniteWord α)
      (hlanguageForward : ∀ factor : Word α,
        IsInfiniteFactor first factor →
          IsInfiniteFactor second factor) :
      ∀ factor : Word β,
        IsInfiniteFactor (fun n => coding (first n)) factor →
          IsInfiniteFactor (fun n => coding (second n)) factor := by
    intro factor hfactor
    obtain ⟨start, hfactorAt⟩ := hfactor
    let lifted := (first.drop start).take factor.length
    have hliftedAt : InfiniteFactorAt first lifted start := by
      simp [InfiniteFactorAt, lifted]
    have hliftedMap : lifted.map coding = factor := by
      change InfiniteFactorAt (Stream'.map coding first)
        factor start at hfactorAt
      simpa [InfiniteFactorAt, lifted, Stream'.drop_map,
        Stream'.map_take] using hfactorAt
    obtain ⟨secondStart, hsecondAt⟩ :=
      hlanguageForward lifted ⟨start, hliftedAt⟩
    refine ⟨secondStart, ?_⟩
    rw [← hliftedMap]
    exact hsecondAt.map_sync coding
  intro factor
  exact ⟨
    transfer left right (fun lifted => (hlanguage lifted).mp) factor,
    transfer right left (fun lifted => (hlanguage lifted).mpr) factor
  ⟩

/-- The synchronized word on the recurrent subtype decodes to exactly the
ambient recurrent language. -/
theorem commonOrbitWord_decodedLanguage
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {sourceScale : ℝ}
    {sourceLength : α → ℝ}
    {P : MetricGrowingFixedPresentation source seed sourceWord
      sourceScale sourceLength}
    {restriction : RecurrentAlphabetRestrictionData P}
    {hprimitive : PrimitiveRecurrentAlphabetData restriction}
    {powered : PoweredRecurrentSubstitutionData restriction hprimitive}
    (core : PoweredRecurrentCoreData powered)
    {right : Substitution (RecurrentLetter sourceWord)}
    (orbit : CommonPowerFixedOrbitData powered.substitution right core.coreWord)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord) :
    ∀ factor : Word α,
      IsInfiniteFactor
          (fun n => ((orbit.commonWord n : RecurrentLetter sourceWord) : α))
          factor ↔
        IsRecurrentFactor sourceWord factor := by
  have hcoreSubset :=
    poweredRecurrentCore_decodedFactor_recurrent core
  have hcoreLanguage :=
    infiniteFactors_eq_recurrentFactors_of_subset hsyndetic hcoreSubset
  have horbitLanguage :=
    orbit.same_language.map_of_injective
      (fun letter : RecurrentLetter sourceWord => (letter : α))
      Subtype.val_injective
  intro factor
  exact (horbitLanguage factor).symm.trans (hcoreLanguage factor)

/-- The synchronized core before the final finite relabelling. -/
structure IntrinsicSynchronizedPrimitiveCoreData
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength) where
  leftPower : ℕ
  rightPower : ℕ
  leftPower_pos : 0 < leftPower
  rightPower_pos : 0 < rightPower
  leftSubstitution : Substitution (RecurrentLetter sourceWord)
  rightSubstitution : Substitution (RecurrentLetter sourceWord)
  word : InfiniteWord (RecurrentLetter sourceWord)
  left_source_image : ∀ letter,
    (leftSubstitution letter).map Subtype.val =
      (leftSource.power leftPower) letter.1
  right_source_image : ∀ letter,
    (rightSubstitution letter).map Subtype.val =
      (rightSource.power rightPower) letter.1
  left_primitive :
    PrimitiveCore.IsPrimitiveSubstitution leftSubstitution
  right_primitive :
    PrimitiveCore.IsPrimitiveSubstitution rightSubstitution
  left_presentation :
    MetricGrowingFixedPresentation leftSubstitution word.head word
      (leftScale ^ leftPower) (fun letter => sourceLength letter.1)
  right_presentation :
    MetricGrowingFixedPresentation rightSubstitution word.head word
      (rightScale ^ rightPower) (fun letter => sourceLength letter.1)
  decoded_language : ∀ factor : Word α,
    IsInfiniteFactor (fun n => (word n).1) factor ↔
      IsRecurrentFactor sourceWord factor

/-- **P5.** Construct the synchronized core on the intrinsic recurrent
alphabet. -/
theorem intrinsicSynchronizedPrimitiveCoreData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord) :
    Nonempty (IntrinsicSynchronizedPrimitiveCoreData Pleft Pright) := by
  obtain ⟨leftRestriction⟩ := recurrentAlphabetRestriction_exists Pleft
  obtain ⟨rightRestriction⟩ := recurrentAlphabetRestriction_exists Pright
  obtain ⟨leftPrimitiveData⟩ :=
    recurrentAlphabetRestriction_isPrimitive hsyndetic leftRestriction
  obtain ⟨rightPrimitiveData⟩ :=
    recurrentAlphabetRestriction_isPrimitive hsyndetic rightRestriction
  have hleftRestrictionGrowing :=
    recurrentAlphabetRestriction_isGrowing leftRestriction
  have hrightRestrictionGrowing :=
    recurrentAlphabetRestriction_isGrowing rightRestriction
  obtain ⟨leftPowered⟩ :=
    primitiveGrowingRestriction_has_prolongablePower
      leftRestriction leftPrimitiveData hleftRestrictionGrowing
  obtain ⟨leftCore⟩ := poweredRecurrentCoreData_exists leftPowered
  have hrestrictionCommute :=
    recurrentAlphabetRestrictions_commute leftRestriction rightRestriction
  have hpoweredCommute :
      leftPowered.substitution.comp rightRestriction.substitution =
        rightRestriction.substitution.comp leftPowered.substitution := by
    rw [leftPowered.substitution_eq_power]
    exact
      (rightRestriction.substitution.commute_right_power_sync
        hrestrictionCommute.symm leftPowered.sourcePower).symm
  obtain ⟨orbit⟩ := commonPowerFixedOrbitData_exists
    leftPowered.primitive leftPowered.growing leftCore.fixed hpoweredCommute
  have hleftScales :
      SubstitutionScalesLetterLengths leftPowered.substitution
        (fun letter : RecurrentLetter sourceWord => sourceLength letter.1)
        (leftScale ^ leftPowered.sourcePower) :=
    poweredRecurrentCore_scalesRestrictedMetric leftCore
  have hleftScaleGt : 1 < leftScale ^ leftPowered.sourcePower :=
    one_lt_pow₀ Pleft.one_lt_eigenvalue
      (Nat.ne_of_gt leftPowered.sourcePower_pos)
  have hleftPresentation :
      MetricGrowingFixedPresentation leftPowered.substitution
        orbit.commonWord.head orbit.commonWord
        (leftScale ^ leftPowered.sourcePower)
        (fun letter : RecurrentLetter sourceWord => sourceLength letter.1) :=
    metricGrowingFixedPresentation_of_primitiveFixedScaling
      leftPowered.primitive leftPowered.growing orbit.left_fixed
      (fun letter => Pleft.letterLength_pos letter.1)
      hleftScales hleftScaleGt
  have hrightPrimitive : PrimitiveCore.IsPrimitiveSubstitution
      (rightRestriction.substitution.power orbit.rightPower) :=
    rightPrimitiveData.isPrimitive.power orbit.rightPower_pos
  have hrightGrowing :
      (rightRestriction.substitution.power orbit.rightPower).IsGrowing :=
    hrightRestrictionGrowing.power orbit.rightPower_pos
  have hrightScales :
      SubstitutionScalesLetterLengths
        (rightRestriction.substitution.power orbit.rightPower)
        (fun letter : RecurrentLetter sourceWord => sourceLength letter.1)
        (rightScale ^ orbit.rightPower) := by
    intro letter
    have hambient := scalesLetterLengths_power
      Pright.scales orbit.rightPower letter.1
    have hmetric :
        wordMetricLength
            (fun output : RecurrentLetter sourceWord =>
              sourceLength output.1)
            ((rightRestriction.substitution.power orbit.rightPower) letter) =
          wordMetricLength sourceLength
            (((rightRestriction.substitution.power orbit.rightPower)
              letter).map Subtype.val) := by
      simp [wordMetricLength, List.map_map, Function.comp_def]
    rw [hmetric,
      recurrentAlphabetRestriction_power_forget
        rightRestriction orbit.rightPower letter]
    simpa only [Substitution.power_apply] using hambient
  have hrightScaleGt : 1 < rightScale ^ orbit.rightPower :=
    one_lt_pow₀ Pright.one_lt_eigenvalue
      (Nat.ne_of_gt orbit.rightPower_pos)
  have hrightPresentation :
      MetricGrowingFixedPresentation
        (rightRestriction.substitution.power orbit.rightPower)
        orbit.commonWord.head orbit.commonWord
        (rightScale ^ orbit.rightPower)
        (fun letter : RecurrentLetter sourceWord => sourceLength letter.1) :=
    metricGrowingFixedPresentation_of_primitiveFixedScaling
      hrightPrimitive hrightGrowing orbit.right_fixed
      (fun letter => Pright.letterLength_pos letter.1)
      hrightScales hrightScaleGt
  have hdecodedLanguage :=
    commonOrbitWord_decodedLanguage leftCore orbit hsyndetic
  exact ⟨{
    leftPower := leftPowered.sourcePower
    rightPower := orbit.rightPower
    leftPower_pos := leftPowered.sourcePower_pos
    rightPower_pos := orbit.rightPower_pos
    leftSubstitution := leftPowered.substitution
    rightSubstitution :=
      rightRestriction.substitution.power orbit.rightPower
    word := orbit.commonWord
    left_source_image := leftPowered.source_image
    right_source_image :=
      recurrentAlphabetRestriction_power_forget
        rightRestriction orbit.rightPower
    left_primitive := leftPowered.primitive
    right_primitive := hrightPrimitive
    left_presentation := hleftPresentation
    right_presentation := hrightPresentation
    decoded_language := hdecodedLanguage
  }⟩

/-! ## R1--R8: one final relabelling to `Fin rank` -/

/-- Relabel a substitution along an equivalence of finite alphabets. -/
def Substitution.relabelEquiv
    {α : Type u} {β : Type v} (source : Substitution α) (equiv : α ≃ β) :
    Substitution β where
  image letter := (source (equiv.symm letter)).map equiv
  image_ne_nil letter hnil :=
    source.image_ne_nil (equiv.symm letter) (List.map_eq_nil_iff.mp hnil)

/-- Relabel an infinite word along an alphabet equivalence. -/
def relabelInfiniteWord
    {α : Type u} {β : Type v} (equiv : α ≃ β)
    (word : InfiniteWord α) : InfiniteWord β :=
  fun position => equiv (word position)

/-- **R1.** Relabelling commutes with finite substitution. -/
theorem Substitution.relabelEquiv_mapWord
    {α : Type u} {β : Type v}
    (source : Substitution α) (equiv : α ≃ β) (letters : Word α) :
    (source.relabelEquiv equiv).mapWord (letters.map equiv) =
      (source.mapWord letters).map equiv := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      simp only [List.map_cons, Substitution.mapWord_cons]
      rw [show source.relabelEquiv equiv (equiv letter) =
          (source letter).map equiv by simp [Substitution.relabelEquiv],
        ih, List.map_append]

/-- **R2.** Relabelling commutes with infinite substitution. -/
theorem Substitution.relabelEquiv_mapInfinite
    {α : Type u} {β : Type v}
    (source : Substitution α) (equiv : α ≃ β)
    (word : InfiniteWord α) :
    (source.relabelEquiv equiv).mapInfinite
        (relabelInfiniteWord equiv word) =
      relabelInfiniteWord equiv (source.mapInfinite word) := by
  let Relation : InfiniteWord β → InfiniteWord β → Prop :=
    fun left right =>
      ∃ (pref : Word β) (input : InfiniteWord α),
        left = pref ++ₛ
          (source.relabelEquiv equiv).mapInfinite
            (relabelInfiniteWord equiv input) ∧
        right = pref ++ₛ
          relabelInfiniteWord equiv (source.mapInfinite input)
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
            (source.relabelEquiv equiv).mapInfinite
                (relabelInfiniteWord equiv input) =
              (source input.head).map equiv ++ₛ
                (source.relabelEquiv equiv).mapInfinite
                  (relabelInfiniteWord equiv input.tail) := by
          rw [(source.relabelEquiv equiv).mapInfinite_eq_append_first_image]
          change
            List.map equiv (source (equiv.symm (equiv input.head))) ++ₛ
                (source.relabelEquiv equiv).mapInfinite
                  (Stream'.tail (Stream'.map equiv input)) =
              List.map equiv (source input.head) ++ₛ
                (source.relabelEquiv equiv).mapInfinite
                  (Stream'.map equiv input.tail)
          rw [equiv.symm_apply_apply, Stream'.tail_map]
        have hright :
            relabelInfiniteWord equiv (source.mapInfinite input) =
              (source input.head).map equiv ++ₛ
                relabelInfiniteWord equiv
                  (source.mapInfinite input.tail) := by
          change Stream'.map equiv (source.mapInfinite input) =
            List.map equiv (source input.head) ++ₛ
              Stream'.map equiv (source.mapInfinite input.tail)
          rw [source.mapInfinite_eq_append_first_image,
            Stream'.map_append_stream]
        rw [hleft, hright]
        have hmapped : (source input.head).map equiv ≠ [] := by
          intro hnil
          exact source.image_ne_nil input.head
            (List.map_eq_nil_iff.mp hnil)
        obtain ⟨letter, rest, hrest⟩ :=
          List.exists_cons_of_ne_nil hmapped
        rw [hrest, Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨rfl, ⟨rest, input.tail, rfl, rfl⟩⟩
  · exact ⟨[], word, rfl, rfl⟩

/-- **R3.** Fixed points transport through relabelling. -/
theorem Substitution.IsFixedPoint.relabelEquiv
    {α : Type u} {β : Type v}
    {source : Substitution α} {word : InfiniteWord α}
    (equiv : α ≃ β) (hfixed : source.IsFixedPoint word) :
    (source.relabelEquiv equiv).IsFixedPoint
      (relabelInfiniteWord equiv word) := by
  change (source.relabelEquiv equiv).mapInfinite
      (relabelInfiniteWord equiv word) = relabelInfiniteWord equiv word
  rw [source.relabelEquiv_mapInfinite, hfixed]

private theorem Substitution.relabelEquiv_iterateWord
    {α : Type u} {β : Type v}
    (source : Substitution α) (equiv : α ≃ β)
    (level : ℕ) (letters : Word α) :
    (source.relabelEquiv equiv).iterateWord level
        (letters.map equiv) =
      (source.iterateWord level letters).map equiv := by
  induction level with
  | zero => rfl
  | succ level ih =>
      rw [Substitution.iterateWord_succ,
        Substitution.iterateWord_succ, ih,
        source.relabelEquiv_mapWord]

private theorem Substitution.relabelEquiv_iterateLetter
    {α : Type u} {β : Type v}
    (source : Substitution α) (equiv : α ≃ β)
    (level : ℕ) (letter : α) :
    (source.relabelEquiv equiv).iterateLetter level (equiv letter) =
      (source.iterateLetter level letter).map equiv := by
  simpa [Substitution.iterateLetter] using
    source.relabelEquiv_iterateWord equiv level [letter]

/-- **R4.** Primitivity transports through relabelling. -/
theorem PrimitiveCore.IsPrimitiveSubstitution.relabelEquiv
    {α : Type u} [Fintype α] {β : Type v} [Fintype β]
    {source : Substitution α} (equiv : α ≃ β)
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source) :
    PrimitiveCore.IsPrimitiveSubstitution (source.relabelEquiv equiv) := by
  obtain ⟨level, hlevel, hcontains⟩ := hprimitive
  refine ⟨level, hlevel, ?_⟩
  intro sourceLetter targetLetter
  have himage := source.relabelEquiv_iterateLetter equiv level
    (equiv.symm sourceLetter)
  rw [equiv.apply_symm_apply] at himage
  rw [himage]
  exact List.mem_map.mpr ⟨equiv.symm targetLetter,
    hcontains (equiv.symm sourceLetter) (equiv.symm targetLetter),
    equiv.apply_symm_apply targetLetter⟩

/-- **R5.** Exact metric scaling transports through relabelling. -/
theorem SubstitutionScalesLetterLengths.relabelEquiv
    {α : Type u} {β : Type v}
    {source : Substitution α} {letterLength : α → ℝ} {scale : ℝ}
    (equiv : α ≃ β)
    (hscale :
      SubstitutionScalesLetterLengths source letterLength scale) :
    SubstitutionScalesLetterLengths (source.relabelEquiv equiv)
      (fun letter => letterLength (equiv.symm letter)) scale := by
  intro letter
  change wordMetricLength
      (fun output => letterLength (equiv.symm output))
      ((source (equiv.symm letter)).map equiv) =
    scale * letterLength (equiv.symm letter)
  have hmetric :
      wordMetricLength (fun output => letterLength (equiv.symm output))
          ((source (equiv.symm letter)).map equiv) =
        wordMetricLength letterLength (source (equiv.symm letter)) := by
    simp [wordMetricLength, List.map_map, Function.comp_def]
  rw [hmetric, hscale]

/-- **R6.** A complete metric presentation transports through
relabelling. -/
theorem MetricGrowingFixedPresentation.relabelEquiv
    {α : Type u} [Fintype α] [DecidableEq α]
    {β : Type v} [Fintype β] [DecidableEq β]
    {source : Substitution α} {seed : α} {word : InfiniteWord α}
    {scale : ℝ} {letterLength : α → ℝ}
    (equiv : α ≃ β)
    (P : MetricGrowingFixedPresentation source seed word scale letterLength) :
    MetricGrowingFixedPresentation (source.relabelEquiv equiv)
      (equiv seed) (relabelInfiniteWord equiv word) scale
      (fun letter => letterLength (equiv.symm letter)) := by
  letI : Nonempty β := ⟨equiv seed⟩
  have hscales :
      SubstitutionScalesLetterLengths (source.relabelEquiv equiv)
        (fun letter => letterLength (equiv.symm letter)) scale :=
    SubstitutionScalesLetterLengths.relabelEquiv equiv P.scales
  refine {
    nonerasing := fun letter =>
      (source.relabelEquiv equiv).image_ne_nil letter
    prolongable := ?_
    fixed := P.fixed.relabelEquiv equiv
    every_letter_occurs := ?_
    growing := ?_
    one_lt_eigenvalue := P.one_lt_eigenvalue
    dominant := dominantEigenvalue_of_positive_metric_scaling
      (source.relabelEquiv equiv)
      (fun letter => letterLength (equiv.symm letter)) scale
      (fun letter => P.letterLength_pos (equiv.symm letter)) hscales
    letterLength_pos := fun letter =>
      P.letterLength_pos (equiv.symm letter)
    scales := hscales
  }
  · obtain ⟨tail, htail, himage⟩ := P.prolongable
    refine ⟨tail.map equiv, ?_, ?_⟩
    · intro hnil
      exact htail (List.map_eq_nil_iff.mp hnil)
    · change (source (equiv.symm (equiv seed))).map equiv =
        equiv seed :: tail.map equiv
      rw [equiv.symm_apply_apply, himage, List.map_cons]
  · intro letter
    obtain ⟨position, hposition⟩ :=
      P.every_letter_occurs (equiv.symm letter)
    refine ⟨position, ?_⟩
    change equiv (word position) = letter
    rw [hposition, equiv.apply_symm_apply]
  · intro letter bound
    obtain ⟨level, hlevel⟩ := P.growing (equiv.symm letter) bound
    refine ⟨level, ?_⟩
    have hrelabeled :=
      source.relabelEquiv_iterateLetter equiv level
        (equiv.symm letter)
    rw [equiv.apply_symm_apply] at hrelabeled
    rw [hrelabeled, List.length_map]
    exact hlevel

/-- **R7.** Relabelling and decoding back by the inverse equivalence leave
the finite-factor language unchanged. -/
theorem relabelInfiniteWord_decode_sameFactorLanguage
    {α : Type u} {β : Type v} (equiv : α ≃ β)
    (word : InfiniteWord α) :
    SameFactorLanguage word
      (fun n => equiv.symm (relabelInfiniteWord equiv word n)) := by
  have hword :
      (fun n => equiv.symm (relabelInfiniteWord equiv word n)) = word := by
    funext position
    simp [relabelInfiniteWord]
  rw [hword]
  intro factor
  rfl

/-- The manuscript-facing synchronized primitive core.  Both substitutions
act on one `Fin rank`, fix one literal word, and scale the literal pullback
of the same ambient metric. -/
structure MetricSynchronizedPrimitiveCoreData
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength) where
  rank : ℕ
  rank_pos : 0 < rank
  decode : Fin rank → α
  decode_injective : Injective decode
  leftPower : ℕ
  rightPower : ℕ
  leftPower_pos : 0 < leftPower
  rightPower_pos : 0 < rightPower
  leftSubstitution : Substitution (Fin rank)
  rightSubstitution : Substitution (Fin rank)
  word : InfiniteWord (Fin rank)
  left_source_image : ∀ letter,
    (leftSubstitution letter).map decode =
      (leftSource.power leftPower) (decode letter)
  right_source_image : ∀ letter,
    (rightSubstitution letter).map decode =
      (rightSource.power rightPower) (decode letter)
  left_primitive :
    PrimitiveCore.IsPrimitiveSubstitution leftSubstitution
  right_primitive :
    PrimitiveCore.IsPrimitiveSubstitution rightSubstitution
  left_presentation :
    MetricGrowingFixedPresentation leftSubstitution word.head word
      (leftScale ^ leftPower) (fun letter => sourceLength (decode letter))
  right_presentation :
    MetricGrowingFixedPresentation rightSubstitution word.head word
      (rightScale ^ rightPower) (fun letter => sourceLength (decode letter))
  decoded_language : ∀ factor : Word α,
    IsInfiniteFactor (fun n => decode (word n)) factor ↔
      IsRecurrentFactor sourceWord factor

namespace MetricSynchronizedPrimitiveCoreData

/-- The two synchronized substitutions commute; this is derived from the
two common-word/common-metric presentations rather than stored as data. -/
theorem commute
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (core : MetricSynchronizedPrimitiveCoreData Pleft Pright) :
    core.leftSubstitution.comp core.rightSubstitution =
      core.rightSubstitution.comp core.leftSubstitution := by
  exact metricFixedPresentations_commute
    core.left_presentation core.right_presentation

/-- Every retained letter occurs in the synchronized common word. -/
theorem every_letter_occurs
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (core : MetricSynchronizedPrimitiveCoreData Pleft Pright) :
    ∀ letter, Substitution.OccursInInfiniteWord letter core.word := by
  exact core.left_presentation.every_letter_occurs

end MetricSynchronizedPrimitiveCoreData

/-- **R8 / future M2 adapter.** This is the sole wrapper needed by the
comparison module: independent M1 presentations and syndeticity are replaced
by one synchronized `Fin`-alphabet primitive core. -/
theorem metricSynchronizedPrimitiveCoreData_exists
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    (Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength)
    (Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength)
    (hsyndetic : RecurrentFactorsSyndetic sourceWord) :
    Nonempty (MetricSynchronizedPrimitiveCoreData Pleft Pright) := by
  obtain ⟨intrinsic⟩ :=
    intrinsicSynchronizedPrimitiveCoreData_exists
      Pleft Pright hsyndetic
  let rank := Fintype.card (RecurrentLetter sourceWord)
  let enumerate : RecurrentLetter sourceWord ≃ Fin rank :=
    Fintype.equivFin (RecurrentLetter sourceWord)
  let decode : Fin rank → α := fun letter => (enumerate.symm letter).1
  have hrank : 0 < rank := by
    dsimp only [rank]
    exact Fintype.card_pos_iff.mpr ⟨intrinsic.word.head⟩
  have hdecodeInjective : Injective decode := by
    intro left right heq
    apply enumerate.symm.injective
    apply Subtype.val_injective
    exact heq
  have hleftSourceImage (letter : Fin rank) :
      ((intrinsic.leftSubstitution.relabelEquiv enumerate) letter).map
          decode =
        (leftSource.power intrinsic.leftPower) (decode letter) := by
    calc
      ((intrinsic.leftSubstitution.relabelEquiv enumerate) letter).map
            decode =
          (intrinsic.leftSubstitution (enumerate.symm letter)).map
            Subtype.val := by
        simp [Substitution.relabelEquiv, decode, List.map_map,
          Function.comp_def]
      _ = (leftSource.power intrinsic.leftPower)
            (enumerate.symm letter).1 :=
        intrinsic.left_source_image (enumerate.symm letter)
      _ = (leftSource.power intrinsic.leftPower) (decode letter) := rfl
  have hrightSourceImage (letter : Fin rank) :
      ((intrinsic.rightSubstitution.relabelEquiv enumerate) letter).map
          decode =
        (rightSource.power intrinsic.rightPower) (decode letter) := by
    calc
      ((intrinsic.rightSubstitution.relabelEquiv enumerate) letter).map
            decode =
          (intrinsic.rightSubstitution (enumerate.symm letter)).map
            Subtype.val := by
        simp [Substitution.relabelEquiv, decode, List.map_map,
          Function.comp_def]
      _ = (rightSource.power intrinsic.rightPower)
            (enumerate.symm letter).1 :=
        intrinsic.right_source_image (enumerate.symm letter)
      _ = (rightSource.power intrinsic.rightPower) (decode letter) := rfl
  have hleftPresentation :
      MetricGrowingFixedPresentation
        (intrinsic.leftSubstitution.relabelEquiv enumerate)
        (enumerate intrinsic.word.head)
        (relabelInfiniteWord enumerate intrinsic.word)
        (leftScale ^ intrinsic.leftPower)
        (fun letter => sourceLength (decode letter)) := by
    simpa only [decode] using
      MetricGrowingFixedPresentation.relabelEquiv
        enumerate intrinsic.left_presentation
  have hrightPresentation :
      MetricGrowingFixedPresentation
        (intrinsic.rightSubstitution.relabelEquiv enumerate)
        (enumerate intrinsic.word.head)
        (relabelInfiniteWord enumerate intrinsic.word)
        (rightScale ^ intrinsic.rightPower)
        (fun letter => sourceLength (decode letter)) := by
    simpa only [decode] using
      MetricGrowingFixedPresentation.relabelEquiv
        enumerate intrinsic.right_presentation
  have hrelabelLanguage :=
    relabelInfiniteWord_decode_sameFactorLanguage enumerate intrinsic.word
  have hdecodedRelabelLanguage :=
    hrelabelLanguage.map_of_injective
      (fun letter : RecurrentLetter sourceWord => (letter : α))
      Subtype.val_injective
  have hdecodedLanguage : ∀ factor : Word α,
      IsInfiniteFactor
          (fun n => decode
            (relabelInfiniteWord enumerate intrinsic.word n)) factor ↔
        IsRecurrentFactor sourceWord factor := by
    intro factor
    have htransport := (hdecodedRelabelLanguage factor).symm.trans
      (intrinsic.decoded_language factor)
    simpa only [decode] using htransport
  exact ⟨{
    rank := rank
    rank_pos := hrank
    decode := decode
    decode_injective := hdecodeInjective
    leftPower := intrinsic.leftPower
    rightPower := intrinsic.rightPower
    leftPower_pos := intrinsic.leftPower_pos
    rightPower_pos := intrinsic.rightPower_pos
    leftSubstitution := intrinsic.leftSubstitution.relabelEquiv enumerate
    rightSubstitution := intrinsic.rightSubstitution.relabelEquiv enumerate
    word := relabelInfiniteWord enumerate intrinsic.word
    left_source_image := hleftSourceImage
    right_source_image := hrightSourceImage
    left_primitive := intrinsic.left_primitive.relabelEquiv enumerate
    right_primitive := intrinsic.right_primitive.relabelEquiv enumerate
    left_presentation := hleftPresentation
    right_presentation := hrightPresentation
    decoded_language := hdecodedLanguage
  }⟩

end
end Symbolic
end CommutingIntervalSimplified
