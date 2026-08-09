import Mathlib.Data.List.Count
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Stream.Init

/-!
# Finite-alphabet substitutions and one-sided words

This file supplies the symbolic vocabulary used in the Markov/Cobham part of
the commuting-interval argument.  A substitution is nonerasing by definition.
Its action on a one-sided infinite word is implemented by a small state machine
which walks through the current nonempty image block before loading the image
of the next input letter.  Thus no choice of padding letter is involved.

The incidence convention agrees with the manuscript: rows are output letters,
columns are source letters.
-/

namespace CommutingInterval
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

/-- Infinite substitution distributes over a finite prefix. -/
theorem mapInfinite_append_stream (σ : Substitution α)
    (w : Word α) (x : InfiniteWord α) :
    σ.mapInfinite (w ++ₛ x) = σ.mapWord w ++ₛ σ.mapInfinite x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [Stream'.cons_append_stream, mapInfinite_eq_append_first_image,
        Stream'.head_cons, Stream'.tail_cons, ih, mapWord_cons,
        Stream'.append_append_stream]

/-- Infinite concatenation respects substitution composition. -/
theorem mapInfinite_comp (σ τ : Substitution α) (x : InfiniteWord α) :
    (σ.comp τ).mapInfinite x = σ.mapInfinite (τ.mapInfinite x) := by
  let R : InfiniteWord α → InfiniteWord α → Prop := fun left right =>
    ∃ (pref : Word α) (input : InfiniteWord α),
      left = pref ++ₛ (σ.comp τ).mapInfinite input ∧
      right = pref ++ₛ σ.mapInfinite (τ.mapInfinite input)
  apply Stream'.eq_of_bisim R
  · intro left right hrel
    rcases hrel with ⟨pref, input, rfl, rfl⟩
    cases pref with
    | cons a pref =>
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨pref, input, rfl, rfl⟩⟩
    | nil =>
        simp only [Stream'.nil_append_stream]
        have hleft :
            (σ.comp τ).mapInfinite input =
              σ.mapWord (τ input.head) ++ₛ
                (σ.comp τ).mapInfinite input.tail := by
          rw [mapInfinite_eq_append_first_image]
          rfl
        have hright :
            σ.mapInfinite (τ.mapInfinite input) =
              σ.mapWord (τ input.head) ++ₛ
                σ.mapInfinite (τ.mapInfinite input.tail) := by
          rw [mapInfinite_eq_append_first_image τ input,
            mapInfinite_append_stream]
        rw [hleft, hright]
        obtain ⟨a, pref, hpref⟩ := List.exists_cons_of_ne_nil
          (σ.mapWord_ne_nil (τ.image_ne_nil input.head))
        rw [hpref, Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨rfl, ⟨pref, input.tail, rfl, rfl⟩⟩
  · exact ⟨[], x, rfl, rfl⟩

/-- The identity substitution acts identically on infinite words. -/
@[simp] theorem mapInfinite_id (x : InfiniteWord α) :
    (Substitution.id : Substitution α).mapInfinite x = x := by
  let R : InfiniteWord α → InfiniteWord α → Prop := fun left right =>
    ∃ input : InfiniteWord α,
      left = (Substitution.id : Substitution α).mapInfinite input ∧
      right = input
  apply Stream'.eq_of_bisim R
  · intro left right hrel
    rcases hrel with ⟨input, hleft, hright⟩
    rw [hleft, hright, mapInfinite_eq_append_first_image, id_apply,
      Stream'.cons_append_stream, ← Stream'.eta input]
    exact ⟨rfl, ⟨input.tail, rfl, rfl⟩⟩
  · exact ⟨x, rfl, rfl⟩

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

/-- Every letter in the substituted image of an occurring input letter
occurs in the infinite substituted word.  This is the basic stream-index
lemma needed when restricting a fixed word to its actual alphabet. -/
theorem occursInInfiniteWord_mapInfinite_of_mem_image
    (σ : Substitution α) {x : InfiniteWord α} {a b : α}
    (ha : OccursInInfiniteWord a x) (hb : b ∈ σ a) :
    OccursInInfiniteWord b (σ.mapInfinite x) := by
  obtain ⟨n, hn⟩ := ha
  have hhead : (x.drop n).head = a := by
    simpa [Stream'.head_drop] using hn
  have hfirst : b ∈ σ.mapInfinite (x.drop n) := by
    rw [σ.mapInfinite_eq_append_first_image]
    apply Stream'.mem_append_stream_left
    simpa [hhead] using hb
  have hwhole : b ∈ σ.mapInfinite x := by
    rw [← Stream'.append_take_drop n x, σ.mapInfinite_append_stream]
    exact Stream'.mem_append_stream_right _ hfirst
  obtain ⟨k, hk⟩ := (Stream'.mem_iff_exists_get_eq).mp hwhole
  exact ⟨k, hk.symm⟩

/-- The occurring alphabet of a substitution fixed point is closed under
letter images. -/
theorem occurringAlphabet_closed_of_fixed
    (σ : Substitution α) {x : InfiniteWord α}
    (hfixed : σ.IsFixedPoint x) {a b : α}
    (ha : a ∈ OccurringAlphabet x) (hb : b ∈ σ a) :
    b ∈ OccurringAlphabet x := by
  rw [mem_occurringAlphabet_iff] at ha ⊢
  have hout := σ.occursInInfiniteWord_mapInfinite_of_mem_image ha hb
  rw [hfixed] at hout
  exact hout

/-- Restrict a substitution fixing `x` to the subtype of letters which
actually occur in `x`.  Closure is a theorem, rather than an extra field in
the restricted substitution. -/
def restrictToOccurringAlphabet
    (σ : Substitution α) (x : InfiniteWord α)
    (hfixed : σ.IsFixedPoint x) :
    Substitution (OccurringAlphabet x) where
  image a := (σ a.1).attach.map fun b ↦
    ⟨b.1, σ.occurringAlphabet_closed_of_fixed hfixed a.2 b.2⟩
  image_ne_nil a := by
    apply List.ne_nil_of_length_pos
    simpa using List.length_pos_of_ne_nil (σ.image_ne_nil a.1)

@[simp] theorem restrictToOccurringAlphabet_image_values
    (σ : Substitution α) (x : InfiniteWord α)
    (hfixed : σ.IsFixedPoint x) (a : OccurringAlphabet x) :
    ((σ.restrictToOccurringAlphabet x hfixed) a).map Subtype.val = σ a.1 := by
  simp only [restrictToOccurringAlphabet, List.map_map]
  change ((σ a.1).attach.map fun b ↦ b.1) = σ a.1
  exact List.attach_map_subtype_val _

theorem occurringAlphabet_finite [Finite α] (x : InfiniteWord α) :
    (OccurringAlphabet x).Finite :=
  Set.toFinite _

theorem generatedAlphabet_finite [Finite α] (σ : Substitution α) (seed : α) :
    (σ.GeneratedAlphabet seed).Finite :=
  Set.toFinite _

/-! ### Relabeling a substitution along an alphabet equivalence -/

variable {β : Type v}

/-- Conjugate a substitution by an equivalence of alphabets. -/
def relabel (q : α ≃ β) (σ : Substitution α) : Substitution β where
  image b := (σ (q.symm b)).map q
  image_ne_nil b := by
    apply List.ne_nil_of_length_pos
    simpa using List.length_pos_of_ne_nil (σ.image_ne_nil (q.symm b))

@[simp] theorem relabel_apply (q : α ≃ β) (σ : Substitution α) (b : β) :
    (σ.relabel q) b = (σ (q.symm b)).map q :=
  rfl

@[simp] theorem relabel_apply_equiv (q : α ≃ β)
    (σ : Substitution α) (a : α) :
    (σ.relabel q) (q a) = (σ a).map q := by
  change (σ (q.symm (q a))).map q = (σ a).map q
  rw [q.symm_apply_apply]

/-- Forgetting the transported labels recovers the original letter image. -/
theorem map_symm_relabel_apply_equiv (q : α ≃ β)
    (σ : Substitution α) (a : α) :
    ((σ.relabel q) (q a)).map q.symm = σ a := by
  rw [relabel_apply_equiv, List.map_map]
  simpa using List.map_id (σ a)

/-- Relabeling commutes with substitution of a finite word. -/
theorem relabel_mapWord_map (q : α ≃ β) (σ : Substitution α)
    (w : Word α) :
    (σ.relabel q).mapWord (w.map q) = (σ.mapWord w).map q := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp [ih]

/-- Relabeling commutes with every finite substitution iterate. -/
theorem relabel_iterateWord_map (q : α ≃ β) (σ : Substitution α)
    (n : ℕ) (w : Word α) :
    (σ.relabel q).iterateWord n (w.map q) =
      (σ.iterateWord n w).map q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterateWord_succ, iterateWord_succ, ih,
        σ.relabel_mapWord_map]

@[simp] theorem relabel_iterateLetter (q : α ≃ β)
    (σ : Substitution α) (n : ℕ) (a : α) :
    (σ.relabel q).iterateLetter n (q a) =
      (σ.iterateLetter n a).map q := by
  simpa [iterateLetter] using σ.relabel_iterateWord_map q n [a]

theorem relabel_occursFrom_iff (q : α ≃ β)
    (σ : Substitution α) (seed a : α) :
    (σ.relabel q).OccursFrom (q seed) (q a) ↔ σ.OccursFrom seed a := by
  simp only [OccursFrom, OccursInWord, relabel_iterateLetter,
    List.mem_map, q.injective.eq_iff, exists_eq_right]

theorem relabel_isGeneratingLetter_iff (q : α ≃ β)
    (σ : Substitution α) (seed : α) :
    (σ.relabel q).IsGeneratingLetter (q seed) ↔
      σ.IsGeneratingLetter seed := by
  constructor
  · intro h a
    exact (σ.relabel_occursFrom_iff q seed a).mp (h (q a))
  · intro h b
    simpa using
      (σ.relabel_occursFrom_iff q seed (q.symm b)).mpr (h (q.symm b))

theorem relabel_prolongableOn_iff (q : α ≃ β)
    (σ : Substitution α) (seed : α) :
    (σ.relabel q).ProlongableOn (q seed) ↔ σ.ProlongableOn seed := by
  constructor
  · rintro ⟨tail, htail, himage⟩
    have htailMap : tail.map q.symm ≠ [] := by
      apply List.ne_nil_of_length_pos
      simpa using List.length_pos_of_ne_nil htail
    refine ⟨tail.map q.symm, htailMap, ?_⟩
    have hmapped := congrArg (List.map q.symm) himage
    simpa [List.map_map, map_symm_relabel_apply_equiv] using hmapped
  · rintro ⟨tail, htail, himage⟩
    have htailMap : tail.map q ≠ [] := by
      apply List.ne_nil_of_length_pos
      simpa using List.length_pos_of_ne_nil htail
    refine ⟨tail.map q, htailMap, ?_⟩
    simp [himage]

/-- The incidence matrix.  The first index is the output letter (row), and
the second index is the source letter (column). -/
def incidenceMatrix [DecidableEq α] (σ : Substitution α) : Matrix α α ℕ :=
  fun output source => (σ source).count output

@[simp] theorem incidenceMatrix_apply [DecidableEq α]
    (σ : Substitution α) (output source : α) :
    σ.incidenceMatrix output source = (σ source).count output :=
  rfl

end Substitution

/-- A letter-to-letter coding between alphabets. -/
structure LetterCoding (α : Type u) (β : Type v) where
  toFun : α → β

namespace LetterCoding

variable {α : Type u} {β : Type v}

instance : CoeFun (LetterCoding α β) fun _ => α → β :=
  ⟨LetterCoding.toFun⟩

/-- Apply a coding to a finite word. -/
def mapWord (coding : LetterCoding α β) (w : Word α) : Word β :=
  w.map coding

/-- Apply a coding pointwise to a one-sided infinite word. -/
def mapInfinite (coding : LetterCoding α β) (x : InfiniteWord α) :
    InfiniteWord β :=
  fun n => coding (x n)

@[simp] theorem mapWord_nil (coding : LetterCoding α β) : coding.mapWord [] = [] :=
  rfl

@[simp] theorem mapWord_cons (coding : LetterCoding α β) (a : α) (w : Word α) :
    coding.mapWord (a :: w) = coding a :: coding.mapWord w :=
  rfl

@[simp] theorem mapInfinite_apply (coding : LetterCoding α β)
    (x : InfiniteWord α) (n : ℕ) : coding.mapInfinite x n = coding (x n) :=
  rfl

/-- Infinite substitution commutes with a letter coding which intertwines
every finite letter image. -/
theorem mapInfinite_substitution
    (coding : LetterCoding α β)
    (source : Substitution α) (target : Substitution β)
    (himage : ∀ a, coding.mapWord (source a) = target (coding a))
    (x : InfiniteWord α) :
    coding.mapInfinite (source.mapInfinite x) =
      target.mapInfinite (coding.mapInfinite x) := by
  let R : InfiniteWord β → InfiniteWord β → Prop := fun left right ↦
    ∃ (pref : Word β) (input : InfiniteWord α),
      left = pref ++ₛ coding.mapInfinite (source.mapInfinite input) ∧
      right = pref ++ₛ target.mapInfinite (coding.mapInfinite input)
  apply Stream'.eq_of_bisim R
  · intro left right hrel
    rcases hrel with ⟨pref, input, rfl, rfl⟩
    cases pref with
    | cons a pref =>
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨pref, input, rfl, rfl⟩⟩
    | nil =>
        simp only [Stream'.nil_append_stream]
        have hleft :
            coding.mapInfinite (source.mapInfinite input) =
              coding.mapWord (source input.head) ++ₛ
                coding.mapInfinite (source.mapInfinite input.tail) := by
          rw [source.mapInfinite_eq_append_first_image]
          exact Stream'.map_append_stream coding (source input.head)
            (source.mapInfinite input.tail)
        have hright :
            target.mapInfinite (coding.mapInfinite input) =
              target (coding input.head) ++ₛ
                target.mapInfinite (coding.mapInfinite input.tail) := by
          rw [target.mapInfinite_eq_append_first_image]
          rfl
        rw [hleft, hright, himage]
        obtain ⟨a, pref, hpref⟩ := List.exists_cons_of_ne_nil
          (target.image_ne_nil (coding input.head))
        rw [hpref, Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨rfl, ⟨pref, input.tail, rfl, rfl⟩⟩
  · exact ⟨[], x, rfl, rfl⟩

end LetterCoding

namespace Substitution

variable {α : Type u} {β : Type v}

/-- Relabel an infinite word pointwise along an alphabet equivalence. -/
def relabelInfiniteWord (q : α ≃ β) (x : InfiniteWord α) :
    InfiniteWord β :=
  fun n ↦ q (x n)

@[simp] theorem relabelInfiniteWord_apply (q : α ≃ β)
    (x : InfiniteWord α) (n : ℕ) :
    relabelInfiniteWord q x n = q (x n) :=
  rfl

/-- Relabeling commutes with infinite substitution. -/
theorem relabel_mapInfinite (q : α ≃ β) (σ : Substitution α)
    (x : InfiniteWord α) :
    relabelInfiniteWord q (σ.mapInfinite x) =
      (σ.relabel q).mapInfinite (relabelInfiniteWord q x) := by
  let coding : LetterCoding α β := ⟨q⟩
  have h := LetterCoding.mapInfinite_substitution coding σ (σ.relabel q)
    (fun a ↦ by
      simpa [coding, LetterCoding.mapWord] using
        (σ.relabel_apply_equiv q a).symm) x
  simpa [coding, relabelInfiniteWord, LetterCoding.mapInfinite] using h

/-- The fixed-word equation is invariant under alphabet relabeling. -/
theorem relabel_isFixedPoint_iff (q : α ≃ β)
    (σ : Substitution α) (x : InfiniteWord α) :
    (σ.relabel q).IsFixedPoint (relabelInfiniteWord q x) ↔
      σ.IsFixedPoint x := by
  constructor
  · intro hfixed
    apply Stream'.ext
    intro n
    apply q.injective
    have hn := congrFun (σ.relabel_mapInfinite q x) n
    rw [hfixed] at hn
    exact hn
  · intro hfixed
    rw [IsFixedPoint, ← σ.relabel_mapInfinite q x, hfixed]

@[simp] theorem take_relabelInfiniteWord (q : α ≃ β)
    (x : InfiniteWord α) (n : ℕ) :
    (relabelInfiniteWord q x).take n = (x.take n).map q := by
  simpa [relabelInfiniteWord] using (Stream'.map_take (a := x) (n := n) q).symm

/-- A prolongable nonerasing substitution strictly lengthens the iterated
seed word at every step. -/
theorem iterateLetter_length_lt_succ
    (σ : Substitution α) {seed : α}
    (hprolong : σ.ProlongableOn seed) (n : ℕ) :
    (σ.iterateLetter n seed).length <
      (σ.iterateLetter (n + 1) seed).length := by
  induction n with
  | zero =>
      obtain ⟨tail, htail, himage⟩ := hprolong
      simp [iterateLetter, iterateWord, himage,
        List.length_pos_of_ne_nil htail]
  | succ n ih =>
      have hprefix := σ.iterateLetter_prefix_succ hprolong n
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
        (List.length_pos_of_ne_nil (σ.mapWord_ne_nil hsuffix_ne))

/-- The `n`-th seed image of a prolongable substitution has length at least
`n + 1`. -/
theorem succ_le_iterateLetter_length
    (σ : Substitution α) {seed : α}
    (hprolong : σ.ProlongableOn seed) (n : ℕ) :
    n + 1 ≤ (σ.iterateLetter n seed).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := σ.iterateLetter_length_lt_succ hprolong n
      omega

/-- If all iterated seed images are the corresponding prefixes of an
infinite word, prolongability makes the seed generate every letter occurring
in that word. -/
theorem isGeneratingLetter_of_iterateLetter_eq_take
    (σ : Substitution α) {seed : α} {x : InfiniteWord α}
    (hprolong : σ.ProlongableOn seed)
    (hprefix : ∀ n : ℕ,
      σ.iterateLetter n seed =
        x.take (σ.iterateLetter n seed).length) :
    ∀ a, OccursInInfiniteWord a x → σ.OccursFrom seed a := by
  intro a ha
  obtain ⟨k, hk⟩ := ha
  let w := σ.iterateLetter k seed
  have hkw : k < w.length := by
    dsimp [w]
    exact (Nat.lt_succ_self k).trans_le
      (σ.succ_le_iterateLetter_length hprolong k)
  have hkTake : k < (x.take w.length).length := by simpa using hkw
  have hget : (x.take w.length)[k] = a := by
    rw [Stream'.take_get (m := k) (n := w.length) (a := x) hkTake]
    exact hk
  refine ⟨k, ?_⟩
  dsimp [w]
  rw [hprefix k]
  exact hget ▸ (x.take w.length).getElem_mem (n := k) hkTake

/-- The word `x` with its values bundled as members of its occurring
alphabet. -/
def wordOnOccurringAlphabet (x : InfiniteWord α) :
    InfiniteWord (OccurringAlphabet x) :=
  fun n ↦ ⟨x n, n, rfl⟩

@[simp] theorem wordOnOccurringAlphabet_value
    (x : InfiniteWord α) (n : ℕ) :
    (wordOnOccurringAlphabet x n).1 = x n :=
  rfl

/-- Restricting a fixed word and its substitution to the occurring alphabet
preserves the fixed-point equation. -/
theorem restrictToOccurringAlphabet_fixed
    (σ : Substitution α) (x : InfiniteWord α)
    (hfixed : σ.IsFixedPoint x) :
    (σ.restrictToOccurringAlphabet x hfixed).IsFixedPoint
      (wordOnOccurringAlphabet x) := by
  let values : LetterCoding (OccurringAlphabet x) α := ⟨Subtype.val⟩
  have hvalues : values.mapInfinite (wordOnOccurringAlphabet x) = x := rfl
  have hnatural := LetterCoding.mapInfinite_substitution values
    (σ.restrictToOccurringAlphabet x hfixed) σ
    (fun a ↦ σ.restrictToOccurringAlphabet_image_values x hfixed a)
    (wordOnOccurringAlphabet x)
  rw [hvalues, hfixed] at hnatural
  apply Stream'.ext
  intro n
  apply Subtype.ext
  exact congrFun hnatural n

end Substitution

/-- A one-sided word is periodic from its first letter onward. -/
def IsPeriodic {α : Type u} (x : InfiniteWord α) : Prop :=
  ∃ period : ℕ, 0 < period ∧ ∀ n : ℕ, x (n + period) = x n

/-- A one-sided word is periodic after deleting a finite prefix. -/
def IsUltimatelyPeriodic {α : Type u} (x : InfiniteWord α) : Prop :=
  ∃ start period : ℕ, 0 < period ∧
    ∀ n : ℕ, start ≤ n → x (n + period) = x n

theorem IsPeriodic.isUltimatelyPeriodic {α : Type u} {x : InfiniteWord α}
    (hx : IsPeriodic x) : IsUltimatelyPeriodic x := by
  obtain ⟨period, hperiod, hx⟩ := hx
  exact ⟨0, period, hperiod, fun n _ => hx n⟩

end Symbolic
end CommutingInterval
