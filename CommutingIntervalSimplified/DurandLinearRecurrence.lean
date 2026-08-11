import CommutingIntervalSimplified.DurandSynchronization

/-!
# Linear recurrence for the synchronized primitive core

This module is the quantitative M2.2 layer.  It is kept separate from core
extraction and synchronization so the return-word modules can import one
stable interface.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

open Function Set

noncomputable section

universe u

/-- A uniform linear bound for finding any nonempty factor after an arbitrary
starting position. -/
def HasLinearFactorGaps {α : Type u} (word : InfiniteWord α)
    (constant : ℕ) : Prop :=
  0 < constant ∧
    ∀ factor : Word α, factor ≠ [] → IsInfiniteFactor word factor →
      ∀ start : ℕ, ∃ position : ℕ,
        start ≤ position ∧
          position ≤ start + constant * factor.length ∧
          InfiniteFactorAt word factor position

/-- Linear recurrence in the return-word form consumed downstream. -/
def IsLinearlyRecurrent {α : Type u} (word : InfiniteWord α)
    (constant : ℕ) : Prop :=
  0 < constant ∧ IsUniformlyRecurrent word ∧
    ∀ marker returnWord : Word α,
      IsReturnWord word marker returnWord →
        returnWord.length ≤ constant * marker.length

/-! ## Generic finite-factor and substitution support -/

/-- A finite occurrence is in particular a list infix. -/
theorem FiniteFactorAt.isInfix
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

/-- Every infix of an infinite factor is again an infinite factor. -/
theorem IsInfiniteFactor.of_infix
    {α : Type u} {word : InfiniteWord α} {small large : Word α}
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

namespace Substitution

@[simp] private theorem iterateWord_nil_lr {α : Type u}
    (source : Substitution α) (level : ℕ) :
    source.iterateWord level [] = [] := by
  induction level with
  | zero => rfl
  | succ level ih =>
      simpa only [iterateWord_succ, ih, mapWord_nil]

private theorem iterateWord_append_lr {α : Type u}
    (source : Substitution α) (level : ℕ) (left right : Word α) :
    source.iterateWord level (left ++ right) =
      source.iterateWord level left ++ source.iterateWord level right := by
  induction level with
  | zero => rfl
  | succ level ih =>
      simp only [iterateWord_succ, ih, mapWord_append]

private theorem iterateWord_add_lr {α : Type u}
    (source : Substitution α) (outer inner : ℕ) (letters : Word α) :
    source.iterateWord (outer + inner) letters =
      source.iterateWord outer (source.iterateWord inner letters) := by
  induction outer with
  | zero => simp
  | succ outer ih =>
      simpa only [Nat.succ_add, iterateWord_succ] using
        congrArg source.mapWord ih

private theorem iterateWord_infix_lr {α : Type u}
    (source : Substitution α) (level : ℕ)
    {small large : Word α} (hfactor : small <:+: large) :
    source.iterateWord level small <:+:
      source.iterateWord level large := by
  rcases hfactor with ⟨left, right, rfl⟩
  refine ⟨source.iterateWord level left,
    source.iterateWord level right, ?_⟩
  simp only [iterateWord_append_lr, List.append_assoc]

private theorem iterateLetter_infix_of_mem_iterate_lr
    {α : Type u} (source : Substitution α)
    {sourceLetter targetLetter : α} {first later : ℕ}
    (hmem : targetLetter ∈ source.iterateLetter first sourceLetter) :
    source.iterateLetter later targetLetter <:+:
      source.iterateLetter (later + first) sourceLetter := by
  have hsingle : [targetLetter] <:+:
      source.iterateLetter first sourceLetter :=
    (List.singleton_infix_iff targetLetter _).2 hmem
  have himage := iterateWord_infix_lr source later hsingle
  change source.iterateLetter later targetLetter <:+:
    source.iterateWord later
      (source.iterateLetter first sourceLetter) at himage
  change source.iterateWord later [targetLetter] <:+:
    source.iterateWord (later + first) [sourceLetter]
  rw [iterateWord_add_lr]
  exact himage

/-- Largest cardinal length of a level image. -/
private def maxIterateLengthLR {α : Type u} [Fintype α]
    (source : Substitution α) (level : ℕ) : ℕ :=
  Finset.univ.sup fun letter : α =>
    (source.iterateLetter level letter).length

private theorem iterateLetter_length_le_maxIterateLengthLR
    {α : Type u} [Fintype α] (source : Substitution α)
    (level : ℕ) (letter : α) :
    (source.iterateLetter level letter).length ≤
      source.maxIterateLengthLR level := by
  exact Finset.le_sup
    (f := fun other : α =>
      (source.iterateLetter level other).length)
    (Finset.mem_univ letter)

private theorem exists_length_eq_maxIterateLengthLR
    {α : Type u} [Fintype α] [Nonempty α]
    (source : Substitution α) (level : ℕ) :
    ∃ letter : α,
      (source.iterateLetter level letter).length =
        source.maxIterateLengthLR level := by
  rcases Finset.exists_mem_eq_sup Finset.univ
      (by simpa using (Finset.univ_nonempty :
        (Finset.univ : Finset α).Nonempty))
      (fun letter : α =>
        (source.iterateLetter level letter).length) with
    ⟨letter, _hletter, hmax⟩
  exact ⟨letter, hmax.symm⟩

@[simp] private theorem maxIterateLengthLR_zero
    {α : Type u} [Fintype α] [Nonempty α]
    (source : Substitution α) : source.maxIterateLengthLR 0 = 1 := by
  obtain ⟨letter, hletter⟩ :=
    source.exists_length_eq_maxIterateLengthLR 0
  simpa using hletter.symm

private theorem iterateWord_length_le_maxIterateLengthLR
    {α : Type u} [Fintype α]
    (source : Substitution α) (level : ℕ) (letters : Word α) :
    (source.iterateWord level letters).length ≤
      source.maxIterateLengthLR level * letters.length := by
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      rw [show letter :: rest = [letter] ++ rest by rfl,
        iterateWord_append_lr, List.length_append]
      change (source.iterateLetter level letter).length +
          (source.iterateWord level rest).length ≤ _
      calc
        (source.iterateLetter level letter).length +
            (source.iterateWord level rest).length ≤
            source.maxIterateLengthLR level +
              source.maxIterateLengthLR level * rest.length :=
          Nat.add_le_add
            (source.iterateLetter_length_le_maxIterateLengthLR
              level letter) ih
        _ = source.maxIterateLengthLR level * (rest.length + 1) := by
          rw [Nat.mul_succ, Nat.add_comm]

private theorem length_le_iterateWord_lr {α : Type u}
    (source : Substitution α) (level : ℕ) (letters : Word α) :
    letters.length ≤ (source.iterateWord level letters).length := by
  induction level with
  | zero => exact le_rfl
  | succ level ih =>
      exact ih.trans
        (source.length_le_mapWord (source.iterateWord level letters))

private theorem maxIterateLengthLR_add_le
    {α : Type u} [Fintype α]
    (source : Substitution α) (base extra : ℕ) :
    source.maxIterateLengthLR (base + extra) ≤
      source.maxIterateLengthLR extra *
        source.maxIterateLengthLR base := by
  apply Finset.sup_le
  intro letter _hletter
  have hlength := source.iterateWord_length_le_maxIterateLengthLR
    extra (source.iterateLetter base letter)
  have hbase := source.iterateLetter_length_le_maxIterateLengthLR
    base letter
  calc
    (source.iterateLetter (base + extra) letter).length =
        (source.iterateWord extra
          (source.iterateLetter base letter)).length := by
      change (source.iterateWord (base + extra) [letter]).length =
        (source.iterateWord extra
          (source.iterateWord base [letter])).length
      rw [Nat.add_comm, iterateWord_add_lr]
    _ ≤ source.maxIterateLengthLR extra *
          (source.iterateLetter base letter).length := hlength
    _ ≤ source.maxIterateLengthLR extra *
          source.maxIterateLengthLR base := Nat.mul_le_mul_left _ hbase

private theorem iterateLetter_prefix_of_le_lr
    {α : Type u} {source : Substitution α} {seed : α}
    (hprolongable : source.ProlongableOn seed)
    {first later : ℕ} (hle : first ≤ later) :
    source.iterateLetter first seed <+:
      source.iterateLetter later seed := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero =>
      simpa using
        (List.prefix_refl (source.iterateLetter first seed))
  | succ extra ih =>
      simpa [Nat.add_assoc] using
        ih.trans (source.iterateLetter_prefix_succ
          hprolongable (first + extra))

private theorem iterateLetter_length_lt_succ_lr
    {α : Type u} (source : Substitution α) {seed : α}
    (hprolongable : source.ProlongableOn seed) (level : ℕ) :
    (source.iterateLetter level seed).length <
      (source.iterateLetter (level + 1) seed).length := by
  induction level with
  | zero =>
      obtain ⟨tail, htail, himage⟩ := hprolongable
      simp [Substitution.iterateLetter, Substitution.iterateWord,
        himage, List.length_pos_of_ne_nil htail]
  | succ level ih =>
      have hprefix := source.iterateLetter_prefix_succ
        hprolongable level
      rcases hprefix with ⟨suffix, hsuffix⟩
      have hsuffix_ne : suffix ≠ [] := by
        intro hsuffix_nil
        subst suffix
        simp only [List.append_nil] at hsuffix
        rw [hsuffix] at ih
        exact (lt_irrefl _) ih
      rw [iterateLetter_succ, iterateLetter_succ, ← hsuffix,
        mapWord_append, List.length_append]
      exact Nat.lt_add_of_pos_right
        (List.length_pos_of_ne_nil
          (source.mapWord_ne_nil hsuffix_ne))

private theorem succ_le_iterateLetter_length_lr
    {α : Type u} (source : Substitution α) {seed : α}
    (hprolongable : source.ProlongableOn seed) (level : ℕ) :
    level + 1 ≤ (source.iterateLetter level seed).length := by
  induction level with
  | zero => simp
  | succ level ih =>
      have hstep := source.iterateLetter_length_lt_succ_lr
        hprolongable level
      omega

private theorem prolongableOn_head_of_growing_fixedPoint
    {α : Type u} {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (hgrowing : source.IsGrowing) :
    source.ProlongableOn word.head := by
  have hhead : source.imageHead word.head = word.head := by
    have hzero := congrFun hfixed 0
    simpa using hzero
  have hlength : 1 < (source word.head).length := by
    by_contra hnot
    have hpositive : 0 < (source word.head).length :=
      List.length_pos_of_ne_nil (source.image_ne_nil word.head)
    have hone : (source word.head).length = 1 := by omega
    have htailLength : (source.imageTail word.head).length = 0 := by
      have himageLength := congrArg List.length
        (source.imageHead_cons_imageTail word.head)
      simp only [List.length_cons] at himageLength
      rw [hone] at himageLength
      omega
    have htail : source.imageTail word.head = [] :=
      List.eq_nil_of_length_eq_zero htailLength
    have himage : source word.head = [word.head] := by
      rw [← source.imageHead_cons_imageTail, hhead, htail]
    have hiterates : ∀ level : ℕ,
        source.iterateLetter level word.head = [word.head] := by
      intro level
      induction level with
      | zero => rfl
      | succ level ih =>
          rw [iterateLetter_succ, ih]
          simpa [himage]
    obtain ⟨growthLevel, hgrowthLevel⟩ := hgrowing word.head 2
    rw [hiterates growthLevel] at hgrowthLevel
    simp at hgrowthLevel
  have htail : source.imageTail word.head ≠ [] := by
    intro hnil
    rw [← source.imageHead_cons_imageTail] at hlength
    simp [hnil] at hlength
  exact ⟨source.imageTail word.head, htail, by
    rw [← source.imageHead_cons_imageTail, hhead]⟩

private theorem isFixedPoint_power_all_lr
    {α : Type u} {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word) (level : ℕ) :
    (source.power level).IsFixedPoint word := by
  cases level with
  | zero => exact mapInfinite_id word
  | succ level => exact isFixedPoint_power hfixed (Nat.succ_pos level)

private theorem iterateWord_drop_take_at_fixed_lr
    {α : Type u} {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (level start count : ℕ) :
    InfiniteFactorAt word
      (source.iterateWord level ((word.drop start).take count))
      (source.iterateWord level (word.take start)).length := by
  have h := mapWord_drop_take_at_fixed
    (isFixedPoint_power_all_lr hfixed level) start count
  simpa only [power_mapWord] using h

end Substitution

namespace Substitution

/-- Iterated images of the first letter of a fixed point are the
corresponding finite prefixes. -/
private theorem iterateLetter_eq_take_of_fixedPoint_lr
    {α : Type u} {source : Substitution α}
    {seed : α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (hseed : word.head = seed) :
    ∀ level : ℕ, source.iterateLetter level seed =
      word.take (source.iterateLetter level seed).length := by
  intro level
  have hblock := iterateWord_drop_take_at_fixed_lr hfixed level 0 1
  have hone : (word.drop 0).take 1 = [seed] := by
    rw [Stream'.drop_zero, Stream'.take_succ, hseed]
    rfl
  rw [hone] at hblock
  simpa [InfiniteFactorAt] using hblock.symm

/-- Every factor of a growing fixed point occurs in some finite image of
its first letter. -/
private theorem factor_infix_iterateLetter_head_lr
    {α : Type u} {source : Substitution α}
    {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (hprolongable : source.ProlongableOn word.head)
    {factor : Word α} (hfactor : IsInfiniteFactor word factor) :
    ∃ level : ℕ,
      factor <:+: source.iterateLetter level word.head := by
  rcases hfactor with ⟨start, hstart⟩
  let level := start + factor.length
  have hprefix := iterateLetter_eq_take_of_fixedPoint_lr
    hfixed rfl level
  have hlength : start + factor.length ≤
      (source.iterateLetter level word.head).length := by
    exact le_trans (Nat.le_succ (start + factor.length))
      (source.succ_le_iterateLetter_length_lr hprolongable level)
  have hambient : InfiniteFactorAt word
      (source.iterateLetter level word.head) 0 := by
    simpa [InfiniteFactorAt] using hprefix.symm
  have hfinite : FiniteFactorAt
      (source.iterateLetter level word.head) factor start := by
    apply finiteFactorAt_of_nested_infiniteFactorAt hambient
    · simpa using hstart
    · exact hlength
  exact ⟨level, hfinite.isInfix⟩

/-- One depth puts every occurring adjacent pair in every letter image. -/
private theorem exists_uniform_pair_depth_lr
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (hprolongable : source.ProlongableOn word.head)
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source) :
    ∃ depth : ℕ, ∀ left right sourceLetter : α,
      IsInfiniteFactor word [left, right] →
        [left, right] <:+:
          source.iterateLetter depth sourceLetter := by
  classical
  have hchoice : ∀ left right : α, ∃ level : ℕ,
      IsInfiniteFactor word [left, right] →
        [left, right] <:+:
          source.iterateLetter level word.head := by
    intro left right
    by_cases hfactor : IsInfiniteFactor word [left, right]
    · obtain ⟨level, hlevel⟩ :=
        factor_infix_iterateLetter_head_lr
          hfixed hprolongable hfactor
      exact ⟨level, fun _ => hlevel⟩
    · exact ⟨0, fun h => False.elim (hfactor h)⟩
  choose pairLevel hpairLevel using hchoice
  let commonLevel := Finset.univ.sup fun left : α =>
    Finset.univ.sup fun right : α => pairLevel left right
  have hpairAtCommon : ∀ left right : α,
      IsInfiniteFactor word [left, right] →
        [left, right] <:+:
          source.iterateLetter commonLevel word.head := by
    intro left right hfactor
    have hinner : pairLevel left right ≤
        Finset.univ.sup (fun other : α => pairLevel left other) :=
      Finset.le_sup (f := fun other : α => pairLevel left other)
        (Finset.mem_univ right)
    have houter :
        Finset.univ.sup (fun other : α => pairLevel left other) ≤
          commonLevel :=
      Finset.le_sup
        (f := fun other : α =>
          Finset.univ.sup fun target : α => pairLevel other target)
        (Finset.mem_univ left)
    have hpref := source.iterateLetter_prefix_of_le_lr
      hprolongable (hinner.trans houter)
    exact (hpairLevel left right hfactor).trans hpref.isInfix
  obtain ⟨primitiveLevel, _hprimitiveLevel, hcontains⟩ := hprimitive
  refine ⟨commonLevel + primitiveLevel, ?_⟩
  intro left right sourceLetter hfactor
  have hheadMem := hcontains sourceLetter word.head
  have hheadImage := source.iterateLetter_infix_of_mem_iterate_lr
    (later := commonLevel) hheadMem
  exact (hpairAtCommon left right hfactor).trans hheadImage

/-- A factor no longer than every level image lies inside the image of an
occurring adjacent pair. -/
private theorem factor_infix_iteratePair_of_min_length_lr
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    {factor : Word α} (hfactor : IsInfiniteFactor word factor)
    (level : ℕ)
    (hmin : ∀ letter : α,
      factor.length ≤ (source.iterateLetter level letter).length) :
    ∃ left right : α,
      IsInfiniteFactor word [left, right] ∧
        factor <:+: source.iterateWord level [left, right] := by
  classical
  rcases hfactor with ⟨origin, horigin⟩
  let cut : ℕ → ℕ := fun index =>
    (source.iterateWord level (word.take index)).length
  have hcutZero : cut 0 = 0 := by simp [cut]
  have hcutSucc : ∀ index : ℕ,
      cut (index + 1) = cut index +
        (source.iterateLetter level (word index)).length := by
    intro index
    dsimp only [cut]
    rw [Stream'.take_succ', iterateWord_append_lr,
      List.length_append]
    rfl
  have hindexLeCut : ∀ index : ℕ, index ≤ cut index := by
    intro index
    simpa [cut] using
      source.length_le_iterateWord_lr level (word.take index)
  let candidates : Finset ℕ :=
    (Finset.range (origin + 1)).filter fun index => cut index ≤ origin
  have hzeroMem : 0 ∈ candidates := by
    simp [candidates, hcutZero]
  have hcandidates : candidates.Nonempty := ⟨0, hzeroMem⟩
  let index := candidates.max' hcandidates
  have hindexMem : index ∈ candidates := candidates.max'_mem hcandidates
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
  have hendBeforeSecond : origin + factor.length ≤ cut (index + 2) := by
    have hnextMin := hmin (word (index + 1))
    rw [show index + 2 = (index + 1) + 1 by omega,
      hcutSucc (index + 1)]
    omega
  let pair : Word α := [word index, word (index + 1)]
  have htakeTwo : (word.drop index).take 2 = pair := by
    rw [show 2 = Nat.succ 1 by rfl, Stream'.take_succ,
      show 1 = Nat.succ 0 by rfl, Stream'.take_succ]
    simp only [pair, Stream'.head_drop, Stream'.tail_drop',
      Stream'.take_zero, List.cons.injEq, and_true]
    exact ⟨rfl, rfl⟩
  have hpairAt : InfiniteFactorAt word pair index := by
    simpa [InfiniteFactorAt] using htakeTwo
  have hpairFactor : IsInfiniteFactor word pair := ⟨index, hpairAt⟩
  let block := source.iterateWord level pair
  have hblockAt : InfiniteFactorAt word block (cut index) := by
    have hraw := iterateWord_drop_take_at_fixed_lr
      hfixed level index 2
    rw [htakeTwo] at hraw
    simpa [cut, block] using hraw
  have hblockLength : block.length = cut (index + 2) - cut index := by
    have hfirst := hcutSucc index
    have hsecond := hcutSucc (index + 1)
    have hsecond' : cut (index + 2) = cut (index + 1) +
        (source.iterateLetter level (word (index + 1))).length := by
      convert hsecond using 1 <;> omega
    simp only [block, pair, show
      [word index, word (index + 1)] =
        [word index] ++ [word (index + 1)] by rfl,
      iterateWord_append_lr, List.length_append]
    change (source.iterateLetter level (word index)).length +
        (source.iterateLetter level (word (index + 1))).length = _
    omega
  have hwithin :
      (origin - cut index) + factor.length ≤ block.length := by
    rw [hblockLength]
    omega
  have hfinite : FiniteFactorAt block factor (origin - cut index) := by
    apply finiteFactorAt_of_nested_infiniteFactorAt hblockAt
    · convert horigin using 1 <;> omega
    · exact hwithin
  exact ⟨word index, word (index + 1), hpairFactor, by
    simpa [block, pair] using hfinite.isInfix⟩

/-- If a factor occurs in every level image, the next occurrence begins no
farther than two maximal level-image lengths away. -/
private theorem factor_appears_within_two_maxImages_lr
    {α : Type u} [Fintype α] [DecidableEq α]
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    {factor : Word α} (level : ℕ)
    (hevery : ∀ letter : α,
      factor <:+: source.iterateLetter level letter) :
    ∀ start : ℕ, ∃ position : ℕ,
      start ≤ position ∧
        position ≤ start + 2 * source.maxIterateLengthLR level ∧
        InfiniteFactorAt word factor position := by
  classical
  intro start
  let cut : ℕ → ℕ := fun index =>
    (source.iterateWord level (word.take index)).length
  have hcutZero : cut 0 = 0 := by simp [cut]
  have hcutSucc : ∀ index : ℕ,
      cut (index + 1) = cut index +
        (source.iterateLetter level (word index)).length := by
    intro index
    dsimp only [cut]
    rw [Stream'.take_succ', iterateWord_append_lr,
      List.length_append]
    rfl
  have hindexLeCut : ∀ index : ℕ, index ≤ cut index := by
    intro index
    simpa [cut] using
      source.length_le_iterateWord_lr level (word.take index)
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
      start + source.maxIterateLengthLR level := by
    have hstep := hcutSucc index
    have himageMax := source.iterateLetter_length_le_maxIterateLengthLR
      level (word index)
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
    have hraw := iterateWord_drop_take_at_fixed_lr
      hfixed level (index + 1) 1
    rw [htakeOne] at hraw
    simpa [cut, sourceLetter] using hraw
  let position := cut (index + 1) + left.length
  have hposition : InfiniteFactorAt word factor position :=
    hblockAt.of_finiteFactorAt hfinite
  have hleftBound : left.length ≤ source.maxIterateLengthLR level := by
    have himageMax := source.iterateLetter_length_le_maxIterateLengthLR
      level sourceLetter
    exact (Nat.le_add_right left.length factor.length).trans
      (hfinite.1.trans himageMax)
  refine ⟨position, by omega, ?_, hposition⟩
  dsimp only [position]
  omega

end Substitution

/-- **M2.2a.** A primitive growing substitution fixed point has one linear
factor-gap constant. -/
theorem Substitution.primitive_fixedPoint_hasLinearFactorGaps
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (hprimitive : PrimitiveCore.IsPrimitiveSubstitution source)
    (hgrowing : source.IsGrowing) :
    ∃ constant : ℕ, HasLinearFactorGaps word constant := by
  classical
  have hprolongable :=
    source.prolongableOn_head_of_growing_fixedPoint hfixed hgrowing
  obtain ⟨pairDepth, hpairDepth⟩ :=
    source.exists_uniform_pair_depth_lr
      hfixed hprolongable hprimitive
  obtain ⟨primitiveLevel, _hprimitiveLevel, hcontains⟩ := hprimitive
  let extra := 1 + primitiveLevel + pairDepth
  let constant := 2 * source.maxIterateLengthLR extra
  have hmaxExtraPos : 0 < source.maxIterateLengthLR extra := by
    let witness : α := Classical.choice (inferInstance : Nonempty α)
    exact (List.length_pos_of_ne_nil
      (source.iterateLetter_ne_nil extra witness)).trans_le
        (source.iterateLetter_length_le_maxIterateLengthLR extra witness)
  refine ⟨constant, ⟨Nat.mul_pos (by omega) hmaxExtraPos, ?_⟩⟩
  intro factor hfactorNonempty hfactor start
  have hfactorLength : 0 < factor.length :=
    List.length_pos_of_ne_nil hfactorNonempty
  have hscaleExists : ∃ scale : ℕ,
      0 < scale ∧ factor.length ≤ source.maxIterateLengthLR scale := by
    refine ⟨factor.length, hfactorLength, ?_⟩
    exact (Nat.le_succ factor.length).trans
      ((source.succ_le_iterateLetter_length_lr
          hprolongable factor.length).trans
        (source.iterateLetter_length_le_maxIterateLengthLR
          factor.length word.head))
  let scale : ℕ :=
    @Nat.find
      (fun level : ℕ =>
        0 < level ∧ factor.length ≤ source.maxIterateLengthLR level)
      (fun _ => Classical.propDecidable _)
      hscaleExists
  have hscaleSpec : 0 < scale ∧
      factor.length ≤ source.maxIterateLengthLR scale := by
    simpa only [scale] using
      (@Nat.find_spec
        (fun level : ℕ =>
          0 < level ∧ factor.length ≤ source.maxIterateLengthLR level)
        (fun _ => Classical.propDecidable _)
        hscaleExists)
  let previous := scale - 1
  have hscaleEq : scale = previous + 1 := by
    dsimp only [previous]
    omega
  have hpreviousMax :
      source.maxIterateLengthLR previous ≤ factor.length := by
    by_cases hzero : previous = 0
    · rw [hzero, source.maxIterateLengthLR_zero]
      omega
    · have hpreviousPos : 0 < previous := Nat.pos_of_ne_zero hzero
      have hpreviousLt : previous < scale := by omega
      have hpreviousFind : previous <
          @Nat.find
            (fun level : ℕ =>
              0 < level ∧
                factor.length ≤ source.maxIterateLengthLR level)
            (fun _ => Classical.propDecidable _)
            hscaleExists := by
        simpa only [scale] using hpreviousLt
      have hnot := @Nat.find_min
        (fun level : ℕ =>
          0 < level ∧ factor.length ≤ source.maxIterateLengthLR level)
        (fun _ => Classical.propDecidable _)
        hscaleExists previous hpreviousFind
      by_contra hbound
      exact hnot ⟨hpreviousPos, by omega⟩
  obtain ⟨maxLetter, hmaxLetter⟩ :=
    source.exists_length_eq_maxIterateLengthLR scale
  have hmin : ∀ letter : α, factor.length ≤
      (source.iterateLetter (scale + primitiveLevel) letter).length := by
    intro letter
    have hmem := hcontains letter maxLetter
    have hinfix := source.iterateLetter_infix_of_mem_iterate_lr
      (later := scale) hmem
    calc
      factor.length ≤ source.maxIterateLengthLR scale := hscaleSpec.2
      _ = (source.iterateLetter scale maxLetter).length := hmaxLetter.symm
      _ ≤ (source.iterateLetter
          (scale + primitiveLevel) letter).length := hinfix.length_le
  obtain ⟨leftLetter, rightLetter, hpairFactor, hfactorPair⟩ :=
    source.factor_infix_iteratePair_of_min_length_lr
      hfixed hfactor
      (scale + primitiveLevel) hmin
  let totalDepth := scale + primitiveLevel + pairDepth
  have hevery : ∀ letter : α,
      factor <:+: source.iterateLetter totalDepth letter := by
    intro letter
    have hpairImage := hpairDepth
      leftLetter rightLetter letter hpairFactor
    have hiterated := source.iterateWord_infix_lr
      (scale + primitiveLevel) hpairImage
    have hcombined :
        source.iterateWord (scale + primitiveLevel)
            (source.iterateLetter pairDepth letter) =
          source.iterateLetter totalDepth letter := by
      dsimp only [totalDepth]
      change source.iterateWord (scale + primitiveLevel)
          (source.iterateWord pairDepth [letter]) =
        source.iterateWord
          (scale + primitiveLevel + pairDepth) [letter]
      exact (source.iterateWord_add_lr
        (scale + primitiveLevel) pairDepth [letter]).symm
    have htrans := hfactorPair.trans hiterated
    rw [hcombined] at htrans
    exact htrans
  rcases source.factor_appears_within_two_maxImages_lr
      hfixed totalDepth hevery start with
    ⟨position, hpositionStart, hpositionBound, hposition⟩
  have hdepthEq : totalDepth = previous + extra := by
    dsimp only [totalDepth, extra]
    omega
  have hmaxDepth : source.maxIterateLengthLR totalDepth ≤
      source.maxIterateLengthLR extra * factor.length := by
    rw [hdepthEq]
    exact (source.maxIterateLengthLR_add_le previous extra).trans
      (Nat.mul_le_mul_left _ hpreviousMax)
  have hdistance : 2 * source.maxIterateLengthLR totalDepth ≤
      constant * factor.length := by
    calc
      2 * source.maxIterateLengthLR totalDepth ≤
          2 * (source.maxIterateLengthLR extra * factor.length) :=
        Nat.mul_le_mul_left 2 hmaxDepth
      _ = constant * factor.length := by
        dsimp only [constant]
        ring
  exact ⟨position, hpositionStart, by omega, hposition⟩

/-- **M2.2b.** A linear factor-gap estimate gives the return-word form of
linear recurrence, with one extra unit in the constant. -/
theorem isLinearlyRecurrent_of_hasLinearFactorGaps
    {α : Type u} {word : InfiniteWord α} {constant : ℕ}
    (hlinear : HasLinearFactorGaps word constant) :
    IsLinearlyRecurrent word (constant + 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro factor hfactor
    by_cases hfactorEmpty : factor = []
    · subst factor
      refine ⟨1, by omega, ?_⟩
      intro start
      exact ⟨0, by omega, by simp [InfiniteFactorAt]⟩
    · refine ⟨constant * factor.length,
        Nat.mul_pos hlinear.1
          (List.length_pos_of_ne_nil hfactorEmpty), ?_⟩
      intro start
      rcases hlinear.2 factor hfactorEmpty hfactor start with
        ⟨position, hstart, hbound, hposition⟩
      refine ⟨position - start, by omega, ?_⟩
      convert hposition using 1 <;> omega
  · intro marker returnWord hreturn
    by_contra hbound
    have hlarge :
        constant * marker.length + marker.length < returnWord.length := by
      simpa [Nat.add_mul] using hbound
    rcases hreturn.2.2.1 with ⟨origin, horigin⟩
    have hmarkerFactor : IsInfiniteFactor word marker :=
      (show IsInfiniteFactor word (returnWord ++ marker) from
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

private theorem wordPower_wordPower_lr {α : Type u} (word : Word α)
    (inner outer : ℕ) :
    wordPower (wordPower word inner) outer =
      wordPower word (outer * inner) := by
  induction outer with
  | zero => simp [wordPower]
  | succ outer ih =>
      calc
        wordPower (wordPower word inner) (outer + 1) =
            wordPower (wordPower word inner) outer ++
              wordPower word inner := by
          simpa [wordPower] using
            wordPower_add (wordPower word inner) outer 1
        _ = wordPower word (outer * inner) ++
              wordPower word inner := by rw [ih]
        _ = wordPower word (outer * inner + inner) :=
          (wordPower_add word (outer * inner) inner).symm
        _ = wordPower word ((outer + 1) * inner) := by
          rw [Nat.add_mul, one_mul]

private theorem wordPower_prefix_of_le_lr
    {α : Type u} {word : Word α} {first later : ℕ}
    (hle : first ≤ later) :
    wordPower word first <+: wordPower word later := by
  rw [← Nat.add_sub_of_le hle, wordPower_add]
  exact List.prefix_append _ _

/-- Every nonempty finite word is a positive power of a primitive root. -/
private theorem exists_primitiveRoot_lr
    {α : Type u} (word : Word α) (hword : word ≠ []) :
    ∃ root : Word α, ∃ exponent : ℕ,
      IsPrimitiveFiniteWord root ∧ 0 < exponent ∧
        wordPower root exponent = word := by
  have hstrong : ∀ length : ℕ, ∀ candidate : Word α,
      candidate.length = length → candidate ≠ [] →
        ∃ root : Word α, ∃ exponent : ℕ,
          IsPrimitiveFiniteWord root ∧ 0 < exponent ∧
            wordPower root exponent = candidate := by
    intro length
    induction length using Nat.strong_induction_on with
    | h length ih =>
      intro candidate hlength hcandidate
      by_cases hprimitive : IsPrimitiveFiniteWord candidate
      · exact ⟨candidate, 1, hprimitive, by omega,
          by simp [wordPower]⟩
      · have hproper : ¬ ∀ base : Word α, ∀ exponent : ℕ,
            1 < exponent → wordPower base exponent ≠ candidate := by
          intro h
          exact hprimitive ⟨hcandidate, h⟩
        push_neg at hproper
        obtain ⟨base, exponent, hexponent, hpower⟩ := hproper
        have hbase : base ≠ [] := by
          intro hnil
          subst base
          apply hcandidate
          simpa [wordPower] using hpower.symm
        have hbaseLength : base.length < candidate.length := by
          have hlengthPower := congrArg List.length hpower
          rw [wordPower_length] at hlengthPower
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
            (wordPower_wordPower_lr root rootExponent exponent).symm
          _ = wordPower base exponent := by rw [hrootPower]
          _ = candidate := hpower
  exact hstrong word.length word rfl hword

/-- **M2.2c.** A purely periodic infinite word contains every positive power
of one primitive finite root. -/
theorem IsPeriodicInfiniteWord.hasPrimitivePowerFactors
    {α : Type u} {word : InfiniteWord α}
    (hperiodic : IsPeriodicInfiniteWord word) :
    ∃ root : Word α, IsPrimitiveFiniteWord root ∧
      ∀ exponent : ℕ, 0 < exponent →
        IsInfiniteFactor word (wordPower root exponent) := by
  rcases hperiodic with ⟨period, hperiodPos, hperiod⟩
  let block := word.take period
  have hblockNonempty : block ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [block, hperiodPos]
  obtain ⟨root, rootExponent, hrootPrimitive,
      hrootExponent, hrootPower⟩ :=
    exists_primitiveRoot_lr block hblockNonempty
  have hshift : ∀ multiplier index : ℕ,
      word (index + multiplier * period) = word index := by
    intro multiplier
    induction multiplier with
    | zero => simp
    | succ multiplier ih =>
        intro index
        calc
          word (index + (multiplier + 1) * period) =
              word ((index + multiplier * period) + period) := by
            simp [Nat.add_mul, Nat.add_assoc]
          _ = word (index + multiplier * period) := hperiod _
          _ = word index := ih index
  have hdropBlock : ∀ multiplier : ℕ,
      (word.drop (multiplier * period)).take period = block := by
    intro multiplier
    apply List.ext_getElem
    · simp [block]
    · intro index hleft hright
      rw [Stream'.take_get (m := index) (n := period)
          (a := word.drop (multiplier * period)) hleft,
        Stream'.take_get (m := index) (n := period)
          (a := word) hright]
      simpa [Stream'.get_drop, Nat.add_comm] using
        hshift multiplier index
  have htakeBlocks : ∀ multiplier : ℕ,
      word.take (multiplier * period) = wordPower block multiplier := by
    intro multiplier
    induction multiplier with
    | zero => simp [wordPower]
    | succ multiplier ih =>
        have hsplit := Stream'.take_add
          (a := word) (m := multiplier * period) (n := period)
        rw [ih, hdropBlock multiplier] at hsplit
        calc
          word.take ((multiplier + 1) * period) =
              word.take (multiplier * period + period) := by
            rw [Nat.add_mul, one_mul]
          _ = wordPower block multiplier ++ block := hsplit
          _ = wordPower block (multiplier + 1) := by
            simpa [wordPower] using
              (wordPower_add block multiplier 1).symm
  refine ⟨root, hrootPrimitive, ?_⟩
  intro exponent _hexponent
  have hblockFactor :
      IsInfiniteFactor word (wordPower block exponent) := by
    refine ⟨0, ?_⟩
    change word.take (wordPower block exponent).length =
      wordPower block exponent
    simpa [block] using htakeBlocks exponent
  have hrootPrefix :
      wordPower root exponent <+: wordPower block exponent := by
    have hle : exponent ≤ exponent * rootExponent :=
      Nat.le_mul_of_pos_right exponent hrootExponent
    rw [← hrootPower, wordPower_wordPower_lr]
    exact wordPower_prefix_of_le_lr hle
  exact hblockFactor.of_infix hrootPrefix.isInfix

namespace MetricSynchronizedPrimitiveCoreData

/-- **M2.2d.** Periodicity of the synchronized word would make the decoded
ambient recurrent language periodic. -/
theorem not_periodic_of_noPeriodicRecurrentLanguage
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (core : MetricSynchronizedPrimitiveCoreData Pleft Pright)
    (hnotPeriodic : ¬ HasPeriodicRecurrentLanguage sourceWord) :
    ¬ IsPeriodicInfiniteWord core.word := by
  intro hperiodic
  have hdecodedPeriodic : IsPeriodicInfiniteWord
      (fun position => core.decode (core.word position)) := by
    rcases hperiodic with ⟨period, hperiodPos, hperiod⟩
    refine ⟨period, hperiodPos, ?_⟩
    intro position
    exact congrArg core.decode (hperiod position)
  obtain ⟨root, hrootPrimitive, hpowers⟩ :=
    hdecodedPeriodic.hasPrimitivePowerFactors
  apply hnotPeriodic
  refine ⟨root, hrootPrimitive, ?_⟩
  intro exponent hexponent
  exact (core.decoded_language (wordPower root exponent)).mp
    (hpowers exponent hexponent)

end MetricSynchronizedPrimitiveCoreData

/-! ## Power-freeness and the lower return bound -/

/-- Once a nonempty factor has appeared, linear recurrence bounds the wait
from any later position to its next occurrence. -/
theorem IsLinearlyRecurrent.nextOccurrence
    {α : Type u} {word : InfiniteWord α} {constant : ℕ}
    (hlinear : IsLinearlyRecurrent word constant)
    {factor : Word α} (hfactorNonempty : factor ≠ [])
    {prior start : ℕ} (hpriorLe : prior ≤ start)
    (hprior : InfiniteFactorAt word factor prior) :
    ∃ position : ℕ, start ≤ position ∧
      position ≤ start + constant * factor.length ∧
      InfiniteFactorAt word factor position := by
  classical
  by_cases hatStart : InfiniteFactorAt word factor start
  · exact ⟨start, le_rfl, Nat.le_add_right _ _, hatStart⟩
  have hfactor : IsInfiniteFactor word factor := ⟨prior, hprior⟩
  obtain ⟨gap, _hgap, hbounded⟩ := hlinear.2.1 factor hfactor
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
  have hreturnBound := hlinear.2.2 factor
    ((word.drop previous).take (next - previous)) hreturn
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
  refine ⟨next, hnextSpec.1, ?_, hnextSpec.2⟩
  omega

/-- Iterating a self-overlap prefixes the marker by every finite power of
the return block. -/
private theorem prefix_wordPower_append_of_prefix_lr
    {α : Type u} {marker returnWord : Word α}
    (hoverlap : marker <+: returnWord ++ marker) (exponent : ℕ) :
    marker <+: wordPower returnWord exponent ++ marker := by
  induction exponent with
  | zero => simp [wordPower]
  | succ exponent ih =>
      apply hoverlap.trans
      have hprepend : returnWord ++ marker <+:
          returnWord ++ (wordPower returnWord exponent ++ marker) :=
        (List.prefix_append_right_inj returnWord).mpr ih
      simpa [wordPower, List.replicate_succ, List.append_assoc] using hprepend

private theorem wordPower_prefix_of_overlap_lr
    {α : Type u} {marker returnWord : Word α} {exponent : ℕ}
    (hoverlap : marker <+: returnWord ++ marker)
    (hlength : exponent * returnWord.length ≤ marker.length) :
    wordPower returnWord exponent <+: marker := by
  rcases prefix_wordPower_append_of_prefix_lr hoverlap exponent with
    ⟨suffix, hsuffix⟩
  have hpowerLength :
      (wordPower returnWord exponent).length ≤ marker.length := by
    simpa using hlength
  apply (List.isPrefix_append_of_length hpowerLength).mp
  rw [hsuffix]
  exact List.prefix_append _ _

/-- A short return forces a long finite power of the return block. -/
private theorem returnWord_power_of_short_lr
    {α : Type u} {word : InfiniteWord α}
    {marker returnWord : Word α} {exponent : ℕ}
    (hreturn : IsReturnWord word marker returnWord)
    (hlength : exponent * returnWord.length ≤ marker.length) :
    IsInfiniteFactor word (wordPower returnWord (exponent + 1)) := by
  rcases hreturn with
    ⟨_hmarker, _hreturn, hfactor, hoverlap, _hconsecutive⟩
  have hpowerPrefix : wordPower returnWord exponent <+: marker :=
    wordPower_prefix_of_overlap_lr hoverlap hlength
  have hprepend : returnWord ++ wordPower returnWord exponent <+:
      returnWord ++ marker :=
    (List.prefix_append_right_inj returnWord).mpr hpowerPrefix
  have hfullPrefix : wordPower returnWord (exponent + 1) <+:
      returnWord ++ marker := by
    simpa [wordPower, List.replicate_succ, List.append_assoc] using hprepend
  exact hfactor.of_infix hfullPrefix.isInfix

/-- A full-block-length factor of a nonempty finite power is a rotation of
the base block. -/
private theorem factor_wordPower_eq_rotate_lr
    {α : Type u} {base factor : Word α} {exponent : ℕ}
    (hbase : base ≠ []) (hexponent : 0 < exponent)
    (hfactor : factor <:+: wordPower base exponent)
    (hlength : factor.length = base.length) :
    ∃ shift : ℕ, factor = base.rotate shift := by
  rcases hfactor with ⟨left, right, hwhole⟩
  refine ⟨left.length, ?_⟩
  apply List.ext_getElem
  · simpa using hlength
  · intro index hindexFactor hindexRotate
    have hindexBase : index < base.length := by
      simpa [hlength] using hindexFactor
    have hbaseLength : 0 < base.length :=
      List.length_pos_of_ne_nil hbase
    have hindex : left.length + index <
        (wordPower base exponent).length := by
      rw [← hwhole]
      simp only [List.length_append]
      omega
    have hfactorIndex :
        (wordPower base exponent)[left.length + index]? = factor[index]? := by
      rw [← hwhole, List.append_assoc,
        List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left]
      exact List.getElem?_append_left hindexFactor
    have hmod := (wordPower_hasPeriod base exponent).getElem?_mod
      base.length (left.length + index) (wordPower base exponent) hindex
    have hmodLt :
        (left.length + index) % base.length < base.length :=
      Nat.mod_lt _ hbaseLength
    obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hexponent)
    have hfirst :
        (wordPower base (predecessor + 1))[
            (left.length + index) % base.length]? =
          base[(left.length + index) % base.length]? := by
      simp [wordPower, List.replicate_succ,
        List.getElem?_append_left, hmodLt]
    have hrotate := List.getElem?_rotate
      (l := base) (n := left.length) hindexBase
    rw [← Option.some_inj, ← List.getElem?_eq_getElem,
      ← List.getElem?_eq_getElem]
    calc
      factor[index]? =
          (wordPower base (predecessor + 1))[left.length + index]? :=
        hfactorIndex.symm
      _ = (wordPower base (predecessor + 1))[
          (left.length + index) % base.length]? := hmod.symm
      _ = base[(left.length + index) % base.length]? := hfirst
      _ = base[(index + left.length) % base.length]? := by
        rw [Nat.add_comm]
      _ = (base.rotate left.length)[index]? := hrotate.symm

/-- If every window of one positive length is a rotation of one block, the
whole one-sided word has that period. -/
private theorem periodicInfiniteWord_of_all_windows_rotate
    {α : Type u} {word : InfiniteWord α} {base : Word α}
    (hbase : base ≠ [])
    (hrotate : ∀ start : ℕ, ∃ shift : ℕ,
      (word.drop start).take base.length = base.rotate shift) :
    IsPeriodicInfiniteWord word := by
  have hperiod : 0 < base.length := List.length_pos_of_ne_nil hbase
  refine ⟨base.length, hperiod, ?_⟩
  intro start
  obtain ⟨predecessor, hlength⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hperiod)
  let middle := (word.drop (start + 1)).take predecessor
  have hfrontSplit :
      (word.drop start).take base.length = word start :: middle := by
    rw [hlength, Stream'.take_succ]
    simp [middle, Stream'.head_drop, Stream'.get]
  have hbackSplit :
      (word.drop (start + 1)).take base.length =
        middle ++ [word (start + base.length)] := by
    rw [hlength, Stream'.take_succ']
    simp only [middle]
    congr 2
    rw [Stream'.get_drop]
    congr 1
    omega
  obtain ⟨frontShift, hfront⟩ := hrotate start
  obtain ⟨backShift, hback⟩ := hrotate (start + 1)
  have hpermutation : List.Perm
      ((word.drop start).take base.length)
      ((word.drop (start + 1)).take base.length) := by
    rw [hfront, hback]
    exact (List.rotate_perm base frontShift).trans
      (List.rotate_perm base backShift).symm
  rw [hfrontSplit, hbackSplit] at hpermutation
  have hcomm : List.Perm
      (middle ++ [word (start + base.length)])
      ([word (start + base.length)] ++ middle) :=
    List.perm_append_comm
  have hcons : List.Perm
      (word start :: middle)
      (word (start + base.length) :: middle) :=
    hpermutation.trans (by simpa using hcomm)
  have hsingle : List.Perm [word start]
      [word (start + base.length)] :=
    (List.perm_append_right_iff middle).mp (by simpa using hcons)
  exact (List.singleton_perm_singleton.mp hsingle).symm

/-- One `(K+1)`-st power in a linearly recurrent word forces periodicity. -/
private theorem IsLinearlyRecurrent.periodic_of_powerFactor
    {α : Type u} {word : InfiniteWord α} {constant : ℕ}
    (hlinear : IsLinearlyRecurrent word constant)
    {base : Word α} (hbase : base ≠ [])
    (hpower : IsInfiniteFactor word (wordPower base (constant + 1))) :
    IsPeriodicInfiniteWord word := by
  apply periodicInfiniteWord_of_all_windows_rotate hbase
  intro start
  let window := (word.drop start).take base.length
  have hwindowLength : window.length = base.length := by
    simp [window]
  have hwindowNonempty : window ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hwindowLength]
    exact List.length_pos_of_ne_nil hbase
  have hwindowAt : InfiniteFactorAt word window start := by
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
      InfiniteFactorAt word window (blockStart + localStart) := by
    rw [hpositionEq]
    exact hpositionFactor
  have hfinite := finiteFactorAt_of_nested_infiniteFactorAt
    hblockAt hpositionFactor' hwithin
  exact factor_wordPower_eq_rotate_lr hbase (Nat.succ_pos _)
    hfinite.isInfix hwindowLength

/-- **M2.2e.** A return word shorter than the reciprocal linear-recurrence
constant would create a forbidden power and hence force periodicity. -/
theorem linearlyRecurrent_returnWord_lowerBound
    {α : Type u} [Fintype α] [DecidableEq α]
    {word : InfiniteWord α} {constant : ℕ}
    (hlinear : IsLinearlyRecurrent word constant)
    (haperiodic : ¬ IsPeriodicInfiniteWord word)
    {marker returnWord : Word α}
    (hreturn : IsReturnWord word marker returnWord) :
    marker.length ≤ constant * returnWord.length := by
  by_contra hbound
  have hshort : constant * returnWord.length ≤ marker.length := by
    omega
  apply haperiodic
  apply hlinear.periodic_of_powerFactor hreturn.2.1
  exact returnWord_power_of_short_lr hreturn hshort

/-- **M2.2f.** Complete quantitative package for the synchronized core on
the nonperiodic-language branch. -/
theorem metricSynchronizedCore_has_aperiodicLinearRecurrence
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (core : MetricSynchronizedPrimitiveCoreData Pleft Pright)
    (hnotPeriodic : ¬ HasPeriodicRecurrentLanguage sourceWord) :
    Nonempty (AperiodicLinearRecurrenceData core.word) := by
  letI : Nonempty (Fin core.rank) := ⟨⟨0, core.rank_pos⟩⟩
  obtain ⟨factorGapConstant, hfactorGaps⟩ :=
    core.leftSubstitution.primitive_fixedPoint_hasLinearFactorGaps
      core.left_presentation.fixed core.left_primitive
      core.left_presentation.growing
  let recurrenceConstant := factorGapConstant + 1
  have hlinear : IsLinearlyRecurrent core.word recurrenceConstant :=
    isLinearlyRecurrent_of_hasLinearFactorGaps hfactorGaps
  have haperiodic : ¬ IsPeriodicInfiniteWord core.word :=
    core.not_periodic_of_noPeriodicRecurrentLanguage hnotPeriodic
  refine ⟨{
    constant := recurrenceConstant
    constant_pos := hlinear.1
    uniformlyRecurrent := hlinear.2.1
    return_upper := ?_
    return_lower := ?_
  }⟩
  · intro marker returnWord _hmarker hreturn
    exact hlinear.2.2 marker returnWord hreturn
  · intro marker returnWord _hmarker hreturn
    exact linearlyRecurrent_returnWord_lowerBound
      hlinear haperiodic hreturn

end

end Symbolic
end CommutingIntervalSimplified
