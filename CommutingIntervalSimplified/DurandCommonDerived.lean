import CommutingIntervalSimplified.DurandLinearRecurrence

/-!
# Common derived system for Durand's comparison

The earlier generic M4.1 statement was too general: it forgot that the two
local return metrics come from one synchronized core.  This module proves the
repaired thirteen-node construction.  The synchronized core is retained
throughout, while all return alphabets are the canonical `Fin` alphabets of
the bounded return tower.
-/

namespace CommutingIntervalSimplified
namespace Symbolic

open Function Set

noncomputable section

universe u

/-- Compatibility adapter from the synchronized primitive core to the generic
return-system records used by the common-derived construction.  Both displayed
metrics are definitionally the pullback of the one ambient exact metric. -/
def MetricSynchronizedPrimitiveCoreData.toReturnCore
    {α : Type u} [Fintype α] [DecidableEq α]
    {leftSource rightSource : Substitution α} {seed : α}
    {sourceWord : InfiniteWord α} {leftScale rightScale : ℝ}
    {sourceLength : α → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (core : MetricSynchronizedPrimitiveCoreData Pleft Pright) :
    MetricCommonRecurrentCoreData Pleft Pright where
  rank := core.rank
  rank_pos := core.rank_pos
  coreWord := core.word
  decode := core.decode
  decoded_language := core.decoded_language
  sourcePowerσ := core.leftPower
  sourcePowerτ := core.rightPower
  sourcePowerσ_pos := core.leftPower_pos
  sourcePowerτ_pos := core.rightPower_pos
  substitutionσ := core.leftSubstitution
  substitutionτ := core.rightSubstitution
  coreLengthσ := fun letter => sourceLength (core.decode letter)
  coreLengthτ := fun letter => sourceLength (core.decode letter)
  presentationσ := core.left_presentation
  presentationτ := core.right_presentation

namespace DurandCommonDerived

/-- All dependent inputs to M4.1, with the synchronized core kept visible.
This is the sound replacement for quantifying over an arbitrary pair of
unrelated metrics in `MetricCommonRecurrentCoreData`. -/
structure CommonDerivedContext
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright) where
  markers : CofinalMetricMarkerTower synchronized.toReturnCore.coreWord
  decompositions : MetricReturnDecompositionTower markers
  tower : BoundedLocalReturnTower synchronized.toReturnCore markers
    decompositions
  bounds : BoundedLocalReturnTowerBounds tower
  coding : BoundedLocalReturnTowerFiniteCoding bounds
  repetition : RepeatedBoundedLocalReturnSystems coding
  notPeriodic : ¬ HasPeriodicRecurrentLanguage sourceWord

/-- 1a auxiliary identity: a complete return decoder reconstructs its
ambient word from the displayed derived stream. -/
theorem returnDecoder_mapInfinite_derived
    {rank : Nat} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank) :
    (returnDecoderSubstitutionMetric decomposition).mapInfinite
      decomposition.derived = word := by
  let decoder := returnDecoderSubstitutionMetric decomposition
  let related : InfiniteWord (Fin rank) -> InfiniteWord (Fin rank) -> Prop :=
    fun left right => exists (pref : Word (Fin rank)) (stage : Nat),
      left = pref ++ₛ decoder.mapInfinite (decomposition.derived.drop stage) ∧
      right = pref ++ₛ word.drop (decomposition.cut stage)
  apply Stream'.eq_of_bisim related
  · intro left right hrelated
    rcases hrelated with ⟨pref, stage, rfl, rfl⟩
    cases pref with
    | cons head tail =>
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨tail, stage, rfl, rfl⟩⟩
    | nil =>
        simp only [Stream'.nil_append_stream]
        let block := decomposition.blocks (decomposition.derived stage)
        have hleft :
            decoder.mapInfinite (decomposition.derived.drop stage) =
              block ++ₛ decoder.mapInfinite
                (decomposition.derived.drop (stage + 1)) := by
          rw [decoder.mapInfinite_eq_append_first_image]
          simp [decoder, returnDecoderSubstitutionMetric, block, Stream'.get]
        have hright :
            word.drop (decomposition.cut stage) =
              block ++ₛ word.drop (decomposition.cut (stage + 1)) := by
          calc
            word.drop (decomposition.cut stage) =
                (word.drop (decomposition.cut stage)).take block.length ++ₛ
                  (word.drop (decomposition.cut stage)).drop block.length :=
              (Stream'.append_take_drop _ _).symm
            _ = block ++ₛ word.drop (decomposition.cut (stage + 1)) := by
              rw [show (word.drop (decomposition.cut stage)).take block.length =
                  block by exact decomposition.block_at_cut stage]
              simp [block, decomposition.cut_succ, Stream'.drop_drop]
        rw [hleft, hright]
        obtain ⟨head, tail, hblock⟩ := List.exists_cons_of_ne_nil
          (decomposition.blocks_are_returns
            (decomposition.derived stage)).2.1
        change block = head :: tail at hblock
        rw [hblock]
        simp only [Stream'.cons_append_stream, Stream'.head_cons,
          Stream'.tail_cons]
        exact ⟨True.intro, ⟨tail, stage + 1, rfl, rfl⟩⟩
  · exact ⟨[], 0, by simp [decoder], by simp [decomposition.cut_zero]⟩

/-- 1a: when the displayed derived stream is the ambient stream, the return
decoder fixes that stream literally. -/
theorem returnDecoder_fixed_derived
    {rank : Nat} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank)
    (hderived : decomposition.derived = word) :
    (returnDecoderSubstitutionMetric decomposition).IsFixedPoint word := by
  have hdecode := returnDecoder_mapInfinite_derived decomposition
  rw [hderived] at hdecode
  exact hdecode

/-- A nonerasing substitution sends a purely periodic stream to a purely
periodic stream, with the decoded period measured in output letters. -/
private theorem mapInfinite_append_stream
    {alphabet : Type*} (substitution : Substitution alphabet)
    (finitePrefix : Word alphabet) (word : InfiniteWord alphabet) :
    substitution.mapInfinite (finitePrefix ++ₛ word) =
      substitution.mapWord finitePrefix ++ₛ substitution.mapInfinite word := by
  induction finitePrefix with
  | nil => rfl
  | cons letter rest ih =>
      rw [Stream'.cons_append_stream,
        substitution.mapInfinite_eq_append_first_image,
        Stream'.head_cons, Stream'.tail_cons, ih,
        substitution.mapWord_cons, Stream'.append_append_stream]

private theorem substitution_mapInfinite_periodic
    {alphabet : Type*} (substitution : Substitution alphabet)
    {word : InfiniteWord alphabet}
    (hperiodic : IsPeriodicInfiniteWord word) :
    IsPeriodicInfiniteWord (substitution.mapInfinite word) := by
  rcases hperiodic with ⟨period, hperiodPos, hperiod⟩
  let periodWord := word.take period
  let decodedPeriod := substitution.mapWord periodWord
  have hperiodWordNonempty : periodWord ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [periodWord, hperiodPos]
  have hdecodedPeriodNonempty : decodedPeriod ≠ [] :=
    substitution.mapWord_ne_nil hperiodWordNonempty
  have hdrop : word.drop period = word := by
    funext position
    calc
      (word.drop period) position = word (period + position) :=
        Stream'.get_drop position period word
      _ = word position := by
        simpa [Nat.add_comm] using hperiod position
  have hself : substitution.mapInfinite word =
      decodedPeriod ++ₛ substitution.mapInfinite word := by
    calc
      substitution.mapInfinite word =
          substitution.mapInfinite (word.take period ++ₛ word.drop period) := by
        rw [Stream'.append_take_drop]
      _ = substitution.mapWord (word.take period) ++ₛ
          substitution.mapInfinite (word.drop period) :=
        mapInfinite_append_stream substitution _ _
      _ = decodedPeriod ++ₛ substitution.mapInfinite word := by
        rw [hdrop]
  refine ⟨decodedPeriod.length,
    List.length_pos_of_ne_nil hdecodedPeriodNonempty, ?_⟩
  intro position
  have hpoint := congrFun hself (decodedPeriod.length + position)
  calc
    substitution.mapInfinite word (position + decodedPeriod.length) =
        substitution.mapInfinite word (decodedPeriod.length + position) := by
      rw [Nat.add_comm]
    _ = (decodedPeriod ++ₛ substitution.mapInfinite word).get
        (decodedPeriod.length + position) := hpoint
    _ = substitution.mapInfinite word position :=
      Stream'.get_append_right position decodedPeriod
        (substitution.mapInfinite word)

private theorem wordPower_wordPower_m4 {α : Type u} (word : Word α)
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

private theorem wordPower_prefix_of_le_m4
    {α : Type u} {word : Word α} {first later : ℕ}
    (hle : first ≤ later) :
    wordPower word first <+: wordPower word later := by
  rw [← Nat.add_sub_of_le hle, wordPower_add]
  exact List.prefix_append _ _

private theorem exists_primitiveRoot_m4
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
            (wordPower_wordPower_m4 root rootExponent exponent).symm
          _ = wordPower base exponent := by rw [hrootPower]
          _ = candidate := hpower
  exact hstrong word.length word rfl hword

private theorem InfiniteFactorAt.map_m4
    {α β : Type*} (coding : α → β)
    {word : InfiniteWord α} {factor : Word α} {start : ℕ}
    (hfactor : InfiniteFactorAt word factor start) :
    InfiniteFactorAt (fun n => coding (word n))
      (factor.map coding) start := by
  change InfiniteFactorAt (Stream'.map coding word)
    (factor.map coding) start
  unfold InfiniteFactorAt at hfactor ⊢
  have hmapped := congrArg (List.map coding) hfactor
  simpa [Stream'.drop_map, Stream'.map_take] using hmapped

private theorem wordPower_flatMap_m4
    {α β : Type*} (word : Word α) (blocks : α → Word β) (exponent : ℕ) :
    (wordPower word exponent).flatMap blocks =
      wordPower (word.flatMap blocks) exponent := by
  induction exponent with
  | zero => simp [wordPower]
  | succ exponent ih =>
      rw [wordPower_add word exponent 1, List.flatMap_append, ih,
        wordPower_add (word.flatMap blocks) exponent 1]
      simp [wordPower]

private theorem wordPower_map_m4
    {α β : Type*} (word : Word α) (coding : α → β) (exponent : ℕ) :
    (wordPower word exponent).map coding =
      wordPower (word.map coding) exponent := by
  induction exponent with
  | zero => simp [wordPower]
  | succ exponent ih =>
      rw [show exponent + 1 = Nat.succ exponent by rfl]
      simp [wordPower, List.map_append, ih]

/-- 1b: periodicity of a return-derived stream produces a periodic recurrent
language in the original ambient word after both decoding maps. -/
theorem derivedPeriodic_gives_ambientPeriodicRecurrentLanguage
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright)
    {marker : Word (Fin synchronized.rank)} {returnRank : ℕ}
    (decomposition : ReturnDecomposition synchronized.word marker returnRank)
    (hperiodic : IsPeriodicInfiniteWord decomposition.derived) :
    HasPeriodicRecurrentLanguage sourceWord := by
  obtain ⟨derivedRoot, hderivedRootPrimitive, hpowers⟩ :=
    hperiodic.hasPrimitivePowerFactors
  let coreBlock := derivedRoot.flatMap decomposition.blocks
  let decodedBlock := coreBlock.map synchronized.decode
  have hcoreBlockNonempty : coreBlock ≠ [] := by
    obtain ⟨head, tail, hroot⟩ :=
      List.exists_cons_of_ne_nil hderivedRootPrimitive.1
    change derivedRoot.flatMap decomposition.blocks ≠ []
    rw [hroot]
    exact List.append_ne_nil_of_left_ne_nil
      (decomposition.blocks_are_returns head).2.1 _
  have hdecodedBlockNonempty : decodedBlock ≠ [] := by
    simpa [decodedBlock] using hcoreBlockNonempty
  have hdecodedPowerFactor : ∀ exponent : ℕ, 0 < exponent →
      IsInfiniteFactor (fun n => synchronized.decode (synchronized.word n))
        (wordPower decodedBlock exponent) := by
    intro exponent hexponent
    rcases hpowers exponent hexponent with ⟨start, hfactor⟩
    have hdecode := decomposition.flatMap_drop_take_derived start
      (wordPower derivedRoot exponent).length
    rw [hfactor, wordPower_flatMap_m4] at hdecode
    have hcoreFactor : InfiniteFactorAt synchronized.word
        (wordPower coreBlock exponent) (decomposition.cut start) := by
      exact hdecode.symm
    have hmapped := InfiniteFactorAt.map_m4 synchronized.decode hcoreFactor
    refine ⟨decomposition.cut start, ?_⟩
    simpa [wordPower_map_m4, decodedBlock] using hmapped
  obtain ⟨primitiveRoot, primitiveExponent, hprimitiveRoot,
      hprimitiveExponent, hprimitivePower⟩ :=
    exists_primitiveRoot_m4 decodedBlock hdecodedBlockNonempty
  refine ⟨primitiveRoot, hprimitiveRoot, ?_⟩
  intro exponent hexponent
  apply (synchronized.decoded_language
    (wordPower primitiveRoot exponent)).mp
  have hlarge := hdecodedPowerFactor exponent hexponent
  have hprefix :
      wordPower primitiveRoot exponent <+:
        wordPower decodedBlock exponent := by
    have hle : exponent ≤ exponent * primitiveExponent :=
      Nat.le_mul_of_pos_right exponent hprimitiveExponent
    rw [← hprimitivePower, wordPower_wordPower_m4]
    exact wordPower_prefix_of_le_m4 hle
  exact hlarge.of_infix hprefix.isInfix

/-- Data retained by the simultaneous first-letter derivation.  Both source
tables are induced through exactly the same sequence of complete return
decompositions. -/
structure IteratedPairedFirstLetterDerivedSystems
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    (context : CommonDerivedContext synchronized) where
  rank : Nat -> Nat
  rank_pos : forall stage, 0 < rank stage
  word : forall stage, InfiniteWord (Fin (rank stage))
  baseRelabel : Fin (rank 0) ≃
    Fin (context.decompositions.rank context.repetition.later)
  base_word_eq : forall position,
    baseRelabel (word 0 position) =
      (context.decompositions.decomposition
        context.repetition.later).derived position
  stepDecomposition : forall stage,
    ReturnDecomposition (word stage) [((word stage).head)] (rank (stage + 1))
  step_word_eq : forall stage,
    (stepDecomposition stage).derived = word (stage + 1)
  compositeDecoder : forall stage, Fin (rank stage) -> Word (Fin (rank 0))
  compositeDecoder_zero : forall letter, compositeDecoder 0 letter = [letter]
  compositeDecoder_succ : forall stage letter,
    compositeDecoder (stage + 1) letter =
      ((stepDecomposition stage).blocks letter).flatMap
        (compositeDecoder stage)
  compositeDecoder_nonempty : forall stage letter,
    compositeDecoder stage letter != []
  leftSubstitution : forall stage, Substitution (Fin (rank stage))
  rightSubstitution : forall stage, Substitution (Fin (rank stage))
  leftFixed : forall stage,
    (leftSubstitution stage).IsFixedPoint (word stage)
  rightFixed : forall stage,
    (rightSubstitution stage).IsFixedPoint (word stage)
  leftPrimitive : forall stage,
    IsPrimitiveSubstitution (leftSubstitution stage)
  rightPrimitive : forall stage,
    IsPrimitiveSubstitution (rightSubstitution stage)
  leftStepFactorization : forall stage,
    PrefixReturnFactorization (leftSubstitution stage)
      (stepDecomposition stage)
  rightStepFactorization : forall stage,
    PrefixReturnFactorization (rightSubstitution stage)
      (stepDecomposition stage)
  left_succ_eq : forall stage,
    leftSubstitution (stage + 1) =
      (leftStepFactorization stage).substitution
  right_succ_eq : forall stage,
    rightSubstitution (stage + 1) =
      (rightStepFactorization stage).substitution
  left_base_eq : forall letter,
    ((leftSubstitution 0) letter).map baseRelabel =
      (context.tower.left context.repetition.later).factorization.substitution
        (baseRelabel letter)
  right_base_eq : forall letter,
    ((rightSubstitution 0) letter).map baseRelabel =
      (context.tower.right context.repetition.later).factorization.substitution
        (baseRelabel letter)

private theorem wordMetricLength_pos_of_ne_nil_A
    {α : Type*} (metric : α → ℝ) (hmetric : ∀ letter, 0 < metric letter)
    {letters : Word α} (hletters : letters ≠ []) :
    0 < wordMetricLength metric letters := by
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hletters
  have htail : 0 ≤ wordMetricLength metric tail :=
    wordMetricLength_nonneg metric (fun letter => (hmetric letter).le) tail
  change 0 < metric head + wordMetricLength metric tail
  exact add_pos_of_pos_of_nonneg (hmetric head) htail

/-- Exact scaling by a positive metric and a factor greater than one forces
ordinary growth of every letter image. -/
private theorem growing_of_exact_positive_metric_A
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    (source : Substitution α) (metric : α → ℝ) (scale : ℝ)
    (hmetric : ∀ letter, 0 < metric letter)
    (hscales : SubstitutionScalesLetterLengths source metric scale)
    (hone : 1 < scale) : source.IsGrowing := by
  classical
  intro letter bound
  let total : ℝ := ∑ other : α, metric other
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
  have hupper : ∀ letters : Word α,
      wordMetricLength metric letters ≤ (letters.length : ℝ) * total := by
    intro letters
    induction letters with
    | nil => simp [wordMetricLength]
    | cons head tail ih =>
        have hhead_le : metric head ≤ total := by
          dsimp [total]
          exact Finset.single_le_sum
            (fun other _ => (hmetric other).le) (Finset.mem_univ head)
        simp only [wordMetricLength, List.map_cons, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        change (tail.map metric).sum ≤
          (tail.length : ℝ) * total at ih
        nlinarith [htotal_pos.le]
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      ((bound : ℝ) * total) / metric letter < scale ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop _
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventually
  have hlarge := hthreshold threshold le_rfl
  refine ⟨threshold, le_of_not_gt fun htooShort => ?_⟩
  have htooShortReal :
      ((source.iterateLetter threshold letter).length : ℝ) < bound := by
    exact_mod_cast htooShort
  have hmetricUpper := hupper (source.iterateLetter threshold letter)
  rw [hiterateMetric] at hmetricUpper
  have hlarge' : (bound : ℝ) * total <
      scale ^ threshold * metric letter :=
    (div_lt_iff₀ (hmetric letter)).mp hlarge
  have htooShortProduct :
      ((source.iterateLetter threshold letter).length : ℝ) * total <
        (bound : ℝ) * total :=
    mul_lt_mul_of_pos_right htooShortReal htotal_pos
  linarith

/-- Uniform recurrence descends through a complete return decomposition. -/
private theorem uniformlyRecurrent_derived_A
    {α : Type u} {word : InfiniteWord α} {marker : Word α}
    {rank : ℕ} (decomposition : ReturnDecomposition word marker rank)
    (huniform : IsUniformlyRecurrent word) :
    IsUniformlyRecurrent decomposition.derived := by
  intro letters hletters
  obtain ⟨origin, horigin⟩ := hletters
  let encoded := letters.flatMap decomposition.blocks
  have hactual :
      (decomposition.derived.drop origin).take letters.length = letters :=
    horigin
  have hencodedAt := decodedMarkerAtCut decomposition origin letters.length
  change InfiniteFactorAt word
      ((((decomposition.derived.drop origin).take letters.length).flatMap
          decomposition.blocks) ++ marker)
      (decomposition.cut origin) at hencodedAt
  rw [hactual] at hencodedAt
  change InfiniteFactorAt word (encoded ++ marker)
      (decomposition.cut origin) at hencodedAt
  obtain ⟨gap, hgapPos, hbounded⟩ :=
    huniform (encoded ++ marker) ⟨decomposition.cut origin, hencodedAt⟩
  refine ⟨gap, hgapPos, ?_⟩
  intro start
  obtain ⟨physicalOffset, hphysicalOffset, hat⟩ :=
    hbounded (decomposition.cut start)
  have hmarkerPrefix : marker <+: encoded ++ marker :=
    marker_prefix_flatMap_returnWords decomposition.blocks
      decomposition.blocks_are_returns letters
  have hmarkerFinite : FiniteFactorAt (encoded ++ marker) marker 0 := by
    refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
  have hmarkerAt : InfiniteFactorAt word marker
      (decomposition.cut start + physicalOffset) := by
    simpa using hat.of_finiteFactorAt hmarkerFinite
  obtain ⟨index, hcutIndex⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAt
  have hstartLe : start ≤ index := by
    by_contra hnot
    have hcutLt := decomposition.cut_strictMono (by omega : index < start)
    rw [hcutIndex] at hcutLt
    omega
  have hatCut : InfiniteFactorAt word
      (letters.flatMap decomposition.blocks ++ marker)
      (decomposition.cut index) := by
    change InfiniteFactorAt word (encoded ++ marker) (decomposition.cut index)
    rw [hcutIndex]
    exact hat
  have hderivedFactor :=
    derivedFactor_of_decodedMarkerAtCut decomposition letters index hatCut
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

private theorem iterateWord_add_A
    {α : Type u} (source : Substitution α) (m n : ℕ)
    (letters : Word α) :
    source.iterateWord (m + n) letters =
      source.iterateWord m (source.iterateWord n letters) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simpa only [Nat.succ_add, Substitution.iterateWord_succ] using
        congrArg source.mapWord ih

private theorem length_le_iterateWord_A
    {α : Type u} (source : Substitution α) (n : ℕ)
    (letters : Word α) :
    letters.length ≤ (source.iterateWord n letters).length := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact ih.trans (source.length_le_mapWord (source.iterateWord n letters))

private theorem iterateWord_drop_take_at_fixed_A
    {α : Type u} {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word) (level start count : ℕ) :
    InfiniteFactorAt word
      (source.iterateWord level ((word.drop start).take count))
      (source.iterateWord level (word.take start)).length := by
  cases level with
  | zero => simpa [Substitution.iterateWord] using
      (show InfiniteFactorAt word ((word.drop start).take count) start by
        simp [InfiniteFactorAt])
  | succ level =>
      have h := Substitution.mapWord_drop_take_at_fixed
        (Substitution.isFixedPoint_power hfixed (Nat.succ_pos level))
        start count
      rw [Substitution.power_mapWord, Substitution.power_mapWord] at h
      exact h

/-- A uniformly recurrent fixed word using every letter, together with
growth of every letter image, forces a common primitive power. -/
theorem primitive_of_fixed_uniform_growing_A
    {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {source : Substitution α} {word : InfiniteWord α}
    (hfixed : source.IsFixedPoint word)
    (huniform : IsUniformlyRecurrent word)
    (hoccurs : ∀ letter : α, Substitution.OccursInInfiniteWord letter word)
    (hgrowing : source.IsGrowing) : IsPrimitiveSubstitution source := by
  classical
  have hletterFactor : ∀ target : α, IsInfiniteFactor word [target] := by
    intro target
    obtain ⟨position, hposition⟩ := hoccurs target
    refine ⟨position, ?_⟩
    change (word.drop position).take 1 = [target]
    rw [Stream'.take_succ]
    simp [Stream'.get, hposition]
  have hbounded : ∀ target : α, AppearsWithBoundedGaps word [target] := by
    intro target
    exact huniform [target] (hletterFactor target)
  choose gap hgapPos hgap using hbounded
  let commonGap : ℕ := Finset.univ.sup gap
  have hgapLe : ∀ target : α, gap target ≤ commonGap := by
    intro target
    exact Finset.le_sup (f := gap) (Finset.mem_univ target)
  have hlevelExists : ∀ sourceLetter : α, ∃ level : ℕ,
      commonGap + 1 ≤ (source.iterateLetter level sourceLetter).length := by
    intro sourceLetter
    exact hgrowing sourceLetter (commonGap + 1)
  choose level hlevel using hlevelExists
  let commonLevel : ℕ := Finset.univ.sup level
  have hlevelLe : ∀ sourceLetter : α, level sourceLetter ≤ commonLevel := by
    intro sourceLetter
    exact Finset.le_sup (f := level) (Finset.mem_univ sourceLetter)
  let iterate := commonLevel + 1
  refine ⟨iterate, by simp [iterate], ?_⟩
  intro sourceLetter targetLetter
  have himageLength : commonGap + 1 ≤
      (source.iterateLetter iterate sourceLetter).length := by
    obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le (hlevelLe sourceLetter)
    have hbase :
        (source.iterateLetter (level sourceLetter) sourceLetter).length ≤
          (source.iterateLetter commonLevel sourceLetter).length := by
      rw [hextra, Nat.add_comm]
      change (source.iterateWord (level sourceLetter) [sourceLetter]).length ≤
        (source.iterateWord (extra + level sourceLetter) [sourceLetter]).length
      rw [iterateWord_add_A source]
      exact length_le_iterateWord_A source extra
        (source.iterateWord (level sourceLetter) [sourceLetter])
    have hnext : (source.iterateLetter commonLevel sourceLetter).length ≤
        (source.iterateLetter iterate sourceLetter).length := by
      change (source.iterateWord commonLevel [sourceLetter]).length ≤
        (source.iterateWord (commonLevel + 1) [sourceLetter]).length
      rw [show commonLevel + 1 = 1 + commonLevel by omega,
        iterateWord_add_A source]
      exact length_le_iterateWord_A source 1
        (source.iterateWord commonLevel [sourceLetter])
    exact (hlevel sourceLetter).trans (hbase.trans hnext)
  obtain ⟨sourcePosition, hsourcePosition⟩ := hoccurs sourceLetter
  have htakeSource : (word.drop sourcePosition).take 1 = [sourceLetter] := by
    rw [Stream'.take_succ]
    simp [Stream'.get, hsourcePosition]
  have himageAt := iterateWord_drop_take_at_fixed_A hfixed iterate
    sourcePosition 1
  rw [htakeSource] at himageAt
  change InfiniteFactorAt word (source.iterateLetter iterate sourceLetter)
    (source.iterateWord iterate (word.take sourcePosition)).length at himageAt
  let imageStart :=
    (source.iterateWord iterate (word.take sourcePosition)).length
  obtain ⟨offset, hoffset, htargetAt⟩ := hgap targetLetter imageStart
  have hwithin : offset + [targetLetter].length ≤
      (source.iterateLetter iterate sourceLetter).length := by
    simp only [List.length_singleton]
    have : offset + 1 ≤ commonGap + 1 :=
      Nat.add_le_add_right (hoffset.trans (hgapLe targetLetter)) 1
    exact this.trans himageLength
  have htargetFinite : FiniteFactorAt
      (source.iterateLetter iterate sourceLetter) [targetLetter] offset :=
    finiteFactorAt_of_nested_infiniteFactorAt
      (by simpa [imageStart] using himageAt) htargetAt hwithin
  exact (List.singleton_infix_iff targetLetter _).mp htargetFinite.isInfix

private structure PairedFirstLetterStageA
    (baseRank : ℕ) (leftScale rightScale : ℝ) where
  rank : ℕ
  rank_pos : 0 < rank
  word : InfiniteWord (Fin rank)
  compositeDecoder : Fin rank → Word (Fin baseRank)
  compositeDecoder_nonempty : ∀ letter, compositeDecoder letter ≠ []
  leftSubstitution : Substitution (Fin rank)
  rightSubstitution : Substitution (Fin rank)
  leftFixed : leftSubstitution.IsFixedPoint word
  rightFixed : rightSubstitution.IsFixedPoint word
  uniform : IsUniformlyRecurrent word
  leftMetric : Fin rank → ℝ
  rightMetric : Fin rank → ℝ
  leftMetric_pos : ∀ letter, 0 < leftMetric letter
  rightMetric_pos : ∀ letter, 0 < rightMetric letter
  leftMetric_scales :
    SubstitutionScalesLetterLengths leftSubstitution leftMetric leftScale
  rightMetric_scales :
    SubstitutionScalesLetterLengths rightSubstitution rightMetric rightScale
  leftPrimitive : IsPrimitiveSubstitution leftSubstitution
  rightPrimitive : IsPrimitiveSubstitution rightSubstitution

private structure PairedFirstLetterStepA
    {baseRank : ℕ} {leftScale rightScale : ℝ}
    (current : PairedFirstLetterStageA baseRank leftScale rightScale) where
  next : PairedFirstLetterStageA baseRank leftScale rightScale
  decomposition : ReturnDecomposition current.word [current.word.head] next.rank
  word_eq : decomposition.derived = next.word
  leftFactorization : PrefixReturnFactorization current.leftSubstitution
    decomposition
  rightFactorization : PrefixReturnFactorization current.rightSubstitution
    decomposition
  left_eq : next.leftSubstitution = leftFactorization.substitution
  right_eq : next.rightSubstitution = rightFactorization.substitution
  decoder_eq : ∀ letter,
    next.compositeDecoder letter =
      (decomposition.blocks letter).flatMap current.compositeDecoder

private theorem pairedFirstLetterStepA_exists
    {baseRank : ℕ} {leftScale rightScale : ℝ}
    (hleftScale : 1 < leftScale) (hrightScale : 1 < rightScale)
    (current : PairedFirstLetterStageA baseRank leftScale rightScale) :
    Nonempty (PairedFirstLetterStepA current) := by
  classical
  letI : Nonempty (Fin current.rank) := ⟨⟨0, current.rank_pos⟩⟩
  let marker : Word (Fin current.rank) := [current.word.head]
  have hmarkerAt : InfiniteFactorAt current.word marker 0 := by
    simp [marker, InfiniteFactorAt, Stream'.take_succ]
  have hmarkerFactor : IsInfiniteFactor current.word marker :=
    ⟨0, hmarkerAt⟩
  have hmarkerBounded := current.uniform marker hmarkerFactor
  have hmarkerRecurrent : IsRecurrentFactor current.word marker :=
    hmarkerBounded.isRecurrentFactor
  have hsyndetic : RecurrentFactorsSyndetic current.word := by
    intro factor hfactor
    apply current.uniform factor
    obtain ⟨start, _hstart, hat⟩ := hfactor 0
    exact ⟨start, hat⟩
  obtain ⟨finiteReturns⟩ := finiteReturnWordData_exists hsyndetic
    hmarkerRecurrent (by simp [marker])
  obtain ⟨nextRank, ⟨decomposition⟩⟩ :=
    returnDecomposition_exists current.uniform (by simp [marker])
      hmarkerAt finiteReturns
  letI : Nonempty (Fin nextRank) := ⟨⟨0, decomposition.rank_pos⟩⟩
  obtain ⟨leftFactorization⟩ :=
    prefixReturnFactorization_exists current.leftFixed decomposition
  obtain ⟨rightFactorization⟩ :=
    prefixReturnFactorization_exists current.rightFixed decomposition
  let leftMetric : Fin nextRank → ℝ := fun letter =>
    wordMetricLength current.leftMetric (decomposition.blocks letter)
  let rightMetric : Fin nextRank → ℝ := fun letter =>
    wordMetricLength current.rightMetric (decomposition.blocks letter)
  have hleftMetricPos : ∀ letter, 0 < leftMetric letter := by
    intro letter
    exact wordMetricLength_pos_of_ne_nil_A current.leftMetric
      current.leftMetric_pos
      (decomposition.blocks_are_returns letter).2.1
  have hrightMetricPos : ∀ letter, 0 < rightMetric letter := by
    intro letter
    exact wordMetricLength_pos_of_ne_nil_A current.rightMetric
      current.rightMetric_pos
      (decomposition.blocks_are_returns letter).2.1
  have hleftScales : SubstitutionScalesLetterLengths
      leftFactorization.substitution leftMetric leftScale :=
    leftFactorization.scalesReturnMetric current.leftMetric_scales
  have hrightScales : SubstitutionScalesLetterLengths
      rightFactorization.substitution rightMetric rightScale :=
    rightFactorization.scalesReturnMetric current.rightMetric_scales
  have huniform : IsUniformlyRecurrent decomposition.derived :=
    uniformlyRecurrent_derived_A decomposition current.uniform
  have hleftGrowing : leftFactorization.substitution.IsGrowing :=
    growing_of_exact_positive_metric_A leftFactorization.substitution
      leftMetric leftScale hleftMetricPos hleftScales hleftScale
  have hrightGrowing : rightFactorization.substitution.IsGrowing :=
    growing_of_exact_positive_metric_A rightFactorization.substitution
      rightMetric rightScale hrightMetricPos hrightScales hrightScale
  have hleftPrimitive : IsPrimitiveSubstitution
      leftFactorization.substitution :=
    primitive_of_fixed_uniform_growing_A leftFactorization.fixed huniform
      decomposition.every_letter_occurs hleftGrowing
  have hrightPrimitive : IsPrimitiveSubstitution
      rightFactorization.substitution :=
    primitive_of_fixed_uniform_growing_A rightFactorization.fixed huniform
      decomposition.every_letter_occurs hrightGrowing
  let nextDecoder : Fin nextRank → Word (Fin baseRank) := fun letter =>
    (decomposition.blocks letter).flatMap current.compositeDecoder
  have hnextDecoderNonempty : ∀ letter, nextDecoder letter ≠ [] := by
    intro letter hempty
    obtain ⟨head, tail, hblock⟩ := List.exists_cons_of_ne_nil
      (decomposition.blocks_are_returns letter).2.1
    have hdecodedHead : current.compositeDecoder head = [] := by
      change (decomposition.blocks letter).flatMap
        current.compositeDecoder = [] at hempty
      rw [hblock, List.flatMap_cons] at hempty
      exact (List.append_eq_nil_iff.mp hempty).1
    exact current.compositeDecoder_nonempty head hdecodedHead
  let next : PairedFirstLetterStageA baseRank leftScale rightScale := {
    rank := nextRank
    rank_pos := decomposition.rank_pos
    word := decomposition.derived
    compositeDecoder := nextDecoder
    compositeDecoder_nonempty := hnextDecoderNonempty
    leftSubstitution := leftFactorization.substitution
    rightSubstitution := rightFactorization.substitution
    leftFixed := leftFactorization.fixed
    rightFixed := rightFactorization.fixed
    uniform := huniform
    leftMetric := leftMetric
    rightMetric := rightMetric
    leftMetric_pos := hleftMetricPos
    rightMetric_pos := hrightMetricPos
    leftMetric_scales := hleftScales
    rightMetric_scales := hrightScales
    leftPrimitive := hleftPrimitive
    rightPrimitive := hrightPrimitive }
  exact ⟨{
    next := next
    decomposition := decomposition
    word_eq := rfl
    leftFactorization := leftFactorization
    rightFactorization := rightFactorization
    left_eq := rfl
    right_eq := rfl
    decoder_eq := fun _ => rfl }⟩

/-- 1c: construct the complete paired first-letter derivation from the
synchronized primitive base. -/
theorem iteratedPairedFirstLetterDerivedSystems_exists
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    (context : CommonDerivedContext synchronized) :
    Nonempty (IteratedPairedFirstLetterDerivedSystems context) := by
  classical
  let baseLevel := context.repetition.later
  let baseRank := context.decompositions.rank baseLevel
  let baseDecomposition := context.decompositions.decomposition baseLevel
  let baseLeft := context.tower.left baseLevel
  let baseRight := context.tower.right baseLevel
  let leftStageScale : ℝ :=
    (leftScale ^ synchronized.leftPower) ^ context.tower.leftLocalPower
  let rightStageScale : ℝ :=
    (rightScale ^ synchronized.rightPower) ^ context.tower.rightLocalPower
  have hleftScale : 1 < leftStageScale := by
    dsimp [leftStageScale]
    exact one_lt_pow₀
      (one_lt_pow₀ Pleft.one_lt_eigenvalue
        (Nat.ne_of_gt synchronized.leftPower_pos))
      (Nat.ne_of_gt context.tower.leftLocalPower_pos)
  have hrightScale : 1 < rightStageScale := by
    dsimp [rightStageScale]
    exact one_lt_pow₀
      (one_lt_pow₀ Pright.one_lt_eigenvalue
        (Nat.ne_of_gt synchronized.rightPower_pos))
      (Nat.ne_of_gt context.tower.rightLocalPower_pos)
  obtain ⟨linear⟩ :=
    metricSynchronizedCore_has_aperiodicLinearRecurrence
      synchronized context.notPeriodic
  have hbaseUniform : IsUniformlyRecurrent baseDecomposition.derived :=
    uniformlyRecurrent_derived_A baseDecomposition linear.uniformlyRecurrent
  letI : Nonempty (Fin baseRank) :=
    ⟨⟨0, baseDecomposition.rank_pos⟩⟩
  have hbaseLeftGrowing : baseLeft.factorization.substitution.IsGrowing :=
    growing_of_exact_positive_metric_A baseLeft.factorization.substitution
      baseLeft.returnLength leftStageScale baseLeft.returnLength_pos
      baseLeft.scales hleftScale
  have hbaseRightGrowing : baseRight.factorization.substitution.IsGrowing :=
    growing_of_exact_positive_metric_A baseRight.factorization.substitution
      baseRight.returnLength rightStageScale baseRight.returnLength_pos
      baseRight.scales hrightScale
  have hbaseLeftPrimitive : IsPrimitiveSubstitution
      baseLeft.factorization.substitution :=
    primitive_of_fixed_uniform_growing_A baseLeft.fixed hbaseUniform
      baseDecomposition.every_letter_occurs hbaseLeftGrowing
  have hbaseRightPrimitive : IsPrimitiveSubstitution
      baseRight.factorization.substitution :=
    primitive_of_fixed_uniform_growing_A baseRight.fixed hbaseUniform
      baseDecomposition.every_letter_occurs hbaseRightGrowing
  let base : PairedFirstLetterStageA baseRank leftStageScale rightStageScale := {
    rank := baseRank
    rank_pos := baseDecomposition.rank_pos
    word := baseDecomposition.derived
    compositeDecoder := fun letter => [letter]
    compositeDecoder_nonempty := by simp
    leftSubstitution := baseLeft.factorization.substitution
    rightSubstitution := baseRight.factorization.substitution
    leftFixed := baseLeft.fixed
    rightFixed := baseRight.fixed
    uniform := hbaseUniform
    leftMetric := baseLeft.returnLength
    rightMetric := baseRight.returnLength
    leftMetric_pos := baseLeft.returnLength_pos
    rightMetric_pos := baseRight.returnLength_pos
    leftMetric_scales := baseLeft.scales
    rightMetric_scales := baseRight.scales
    leftPrimitive := hbaseLeftPrimitive
    rightPrimitive := hbaseRightPrimitive }
  let successor : ∀ current :
      PairedFirstLetterStageA baseRank leftStageScale rightStageScale,
      PairedFirstLetterStepA current := fun current =>
    Classical.choice
      (pairedFirstLetterStepA_exists hleftScale hrightScale current)
  let stages : ℕ →
      PairedFirstLetterStageA baseRank leftStageScale rightStageScale :=
    fun stage => Nat.rec base (fun _ current => (successor current).next) stage
  let rank : ℕ → ℕ := fun stage => (stages stage).rank
  let word : ∀ stage, InfiniteWord (Fin (rank stage)) := fun stage =>
    (stages stage).word
  let baseRelabel : Fin (rank 0) ≃ Fin baseRank := Equiv.refl _
  let stepDecomposition : ∀ stage,
      ReturnDecomposition (word stage) [(word stage).head]
        (rank (stage + 1)) := fun stage =>
    (successor (stages stage)).decomposition
  let compositeDecoder : ∀ stage,
      Fin (rank stage) → Word (Fin (rank 0)) := fun stage =>
    (stages stage).compositeDecoder
  let leftSubstitution : ∀ stage,
      Substitution (Fin (rank stage)) := fun stage =>
    (stages stage).leftSubstitution
  let rightSubstitution : ∀ stage,
      Substitution (Fin (rank stage)) := fun stage =>
    (stages stage).rightSubstitution
  let leftStepFactorization : ∀ stage,
      PrefixReturnFactorization (leftSubstitution stage)
        (stepDecomposition stage) := fun stage =>
    (successor (stages stage)).leftFactorization
  let rightStepFactorization : ∀ stage,
      PrefixReturnFactorization (rightSubstitution stage)
        (stepDecomposition stage) := fun stage =>
    (successor (stages stage)).rightFactorization
  exact ⟨{
    rank := rank
    rank_pos := fun stage => (stages stage).rank_pos
    word := word
    baseRelabel := baseRelabel
    base_word_eq := by
      intro position
      rfl
    stepDecomposition := stepDecomposition
    step_word_eq := by
      intro stage
      exact (successor (stages stage)).word_eq
    compositeDecoder := compositeDecoder
    compositeDecoder_zero := by
      intro letter
      rfl
    compositeDecoder_succ := by
      intro stage letter
      exact (successor (stages stage)).decoder_eq letter
    compositeDecoder_nonempty := by
      intro stage letter
      simpa using (stages stage).compositeDecoder_nonempty letter
    leftSubstitution := leftSubstitution
    rightSubstitution := rightSubstitution
    leftFixed := fun stage => (stages stage).leftFixed
    rightFixed := fun stage => (stages stage).rightFixed
    leftPrimitive := fun stage => (stages stage).leftPrimitive
    rightPrimitive := fun stage => (stages stage).rightPrimitive
    leftStepFactorization := leftStepFactorization
    rightStepFactorization := rightStepFactorization
    left_succ_eq := by
      intro stage
      exact (successor (stages stage)).left_eq
    right_succ_eq := by
      intro stage
      exact (successor (stages stage)).right_eq
    left_base_eq := by
      intro letter
      simp [leftSubstitution, stages, base, baseRelabel, baseLeft, baseLevel]
    right_base_eq := by
      intro letter
      simp [rightSubstitution, stages, base, baseRelabel, baseRight, baseLevel] }⟩

/-- One first-letter stage identified with an actual canonical marker level;
the same relabeling transports the word and both induced source tables. -/
structure FirstLetterCanonicalBaseRealization
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (stage : Nat) where
  level : Nat
  relabel : Fin (systems.rank stage) ≃
    Fin (context.decompositions.rank level)
  word_relabels : forall position,
    relabel (systems.word stage position) =
      (context.decompositions.decomposition level).derived position
  left_relabels : forall letter,
    ((systems.leftSubstitution stage) letter).map relabel =
      (context.tower.left level).factorization.substitution (relabel letter)
  right_relabels : forall letter,
    ((systems.rightSubstitution stage) letter).map relabel =
      (context.tower.right level).factorization.substitution (relabel letter)

private def castPrefixReturnFactorizationWord_A
    {α : Type*} {source : Substitution α}
    {left right : InfiniteWord α} {marker : Word α} {rank : ℕ}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank)
    (factorization : PrefixReturnFactorization source decomposition) :
    PrefixReturnFactorization source
      (castReturnDecompositionWord hword decomposition) := by
  subst right
  exact factorization

@[simp] private theorem castPrefixReturnFactorizationWord_A_substitution
    {α : Type*} {source : Substitution α}
    {left right : InfiniteWord α} {marker : Word α} {rank : ℕ}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank)
    (factorization : PrefixReturnFactorization source decomposition) :
    (castPrefixReturnFactorizationWord_A hword decomposition
      factorization).substitution = factorization.substitution := by
  subst right
  rfl

private theorem mapWord_flatMap_blocks_A
    {sourceAlphabet returnAlphabet : Type*}
    (source : Substitution sourceAlphabet)
    (induced : Substitution returnAlphabet)
    (blocks : returnAlphabet → Word sourceAlphabet)
    (hletter : ∀ letter,
      (induced letter).flatMap blocks = source.mapWord (blocks letter)) :
    ∀ letters : Word returnAlphabet,
      (induced.mapWord letters).flatMap blocks =
        source.mapWord (letters.flatMap blocks) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      rw [Substitution.mapWord_cons, List.flatMap_append, hletter,
        List.flatMap_cons, Substitution.mapWord_append, ih]

private theorem composedFactor_decodes_A
    {α : Type*} {word : InfiniteWord α}
    {outerMarker : Word α} {outerRank : ℕ}
    (outer : ReturnDecomposition word outerMarker outerRank)
    {source : Substitution α}
    {outerSubstitution : Substitution (Fin outerRank)}
    (houter : ∀ letter,
      (outerSubstitution letter).flatMap outer.blocks =
        source.mapWord (outer.blocks letter))
    {innerMarker : Word (Fin outerRank)} {innerRank : ℕ}
    (inner : ReturnDecomposition outer.derived innerMarker innerRank)
    (factorization : PrefixReturnFactorization outerSubstitution inner)
    (letter : Fin innerRank) :
    (factorization.substitution letter).flatMap
        (composeReturnDecompositions outer inner).blocks =
      source.mapWord
        ((composeReturnDecompositions outer inner).blocks letter) := by
  change (factorization.factor letter).flatMap
      (fun innerLetter => (inner.blocks innerLetter).flatMap outer.blocks) =
    source.mapWord ((inner.blocks letter).flatMap outer.blocks)
  rw [← List.flatMap_assoc, factorization.factor_decodes]
  exact mapWord_flatMap_blocks_A source outerSubstitution outer.blocks
    houter (inner.blocks letter)

private structure FirstLetterPhysicalStageA
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : ℝ}
    {sourceLength : alphabet → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (stage : ℕ) where
  marker : Word (Fin synchronized.rank)
  decomposition : ReturnDecomposition synchronized.word marker
    (systems.rank stage)
  derived_eq : decomposition.derived = systems.word stage
  left_decodes : ∀ letter,
    ((systems.leftSubstitution stage) letter).flatMap decomposition.blocks =
      (synchronized.leftSubstitution.power
        context.tower.leftLocalPower).mapWord
          (decomposition.blocks letter)
  right_decodes : ∀ letter,
    ((systems.rightSubstitution stage) letter).flatMap decomposition.blocks =
      (synchronized.rightSubstitution.power
        context.tower.rightLocalPower).mapWord
          (decomposition.blocks letter)

private def firstLetterPhysicalBase_A
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : ℝ}
    {sourceLength : alphabet → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context) :
    FirstLetterPhysicalStageA systems 0 := by
  classical
  let level := context.repetition.later
  let canonical := context.decompositions.decomposition level
  let relabeled : ReturnDecomposition synchronized.word
      (context.markers.marker level) (systems.rank 0) := {
    rank_pos := systems.rank_pos 0
    marker_ne_nil := canonical.marker_ne_nil
    marker_at_zero := canonical.marker_at_zero
    blocks := fun letter => canonical.blocks (systems.baseRelabel letter)
    blocks_injective := canonical.blocks_injective.comp
      systems.baseRelabel.injective
    blocks_are_returns := fun letter =>
      canonical.blocks_are_returns (systems.baseRelabel letter)
    every_return_is_block := by
      intro returnWord hreturn
      obtain ⟨target, htarget⟩ :=
        canonical.every_return_is_block returnWord hreturn
      refine ⟨systems.baseRelabel.symm target, ?_⟩
      simpa using htarget
    derived := systems.word 0
    cut := canonical.cut
    cut_zero := canonical.cut_zero
    cut_succ := by
      intro position
      rw [canonical.cut_succ, ← systems.base_word_eq position]
      rfl
    block_at_cut := by
      intro position
      simpa [systems.base_word_eq position] using
        canonical.block_at_cut position }
  refine {
    marker := context.markers.marker level
    decomposition := relabeled
    derived_eq := rfl
    left_decodes := ?_
    right_decodes := ?_ }
  · intro letter
    change ((systems.leftSubstitution 0) letter).flatMap
        (fun current => canonical.blocks (systems.baseRelabel current)) =
      (synchronized.leftSubstitution.power
          context.tower.leftLocalPower).mapWord
        (canonical.blocks (systems.baseRelabel letter))
    rw [← List.flatMap_map, systems.left_base_eq]
    exact (context.tower.left level).factorization.factor_decodes
      (systems.baseRelabel letter)
  · intro letter
    change ((systems.rightSubstitution 0) letter).flatMap
        (fun current => canonical.blocks (systems.baseRelabel current)) =
      (synchronized.rightSubstitution.power
          context.tower.rightLocalPower).mapWord
        (canonical.blocks (systems.baseRelabel letter))
    rw [← List.flatMap_map, systems.right_base_eq]
    exact (context.tower.right level).factorization.factor_decodes
      (systems.baseRelabel letter)

private def firstLetterPhysicalSucc_A
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : ℝ}
    {sourceLength : alphabet → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (stage : ℕ) (current : FirstLetterPhysicalStageA systems stage) :
    FirstLetterPhysicalStageA systems (stage + 1) := by
  classical
  let inner := castReturnDecompositionWord current.derived_eq.symm
    (systems.stepDecomposition stage)
  let leftFactorization := castPrefixReturnFactorizationWord_A
    current.derived_eq.symm (systems.stepDecomposition stage)
      (systems.leftStepFactorization stage)
  let rightFactorization := castPrefixReturnFactorizationWord_A
    current.derived_eq.symm (systems.stepDecomposition stage)
      (systems.rightStepFactorization stage)
  let composed := composeReturnDecompositions current.decomposition inner
  refine {
    marker := [(systems.word stage).head].flatMap
      current.decomposition.blocks ++ current.marker
    decomposition := composed
    derived_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }
  · change inner.derived = systems.word (stage + 1)
    rw [castReturnDecompositionWord_derived]
    exact systems.step_word_eq stage
  · intro letter
    rw [systems.left_succ_eq stage]
    have hfactorization : leftFactorization.substitution =
        (systems.leftStepFactorization stage).substitution := by
      simp [leftFactorization]
    rw [← hfactorization]
    change (leftFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_A current.decomposition
      current.left_decodes inner leftFactorization letter
  · intro letter
    rw [systems.right_succ_eq stage]
    have hfactorization : rightFactorization.substitution =
        (systems.rightStepFactorization stage).substitution := by
      simp [rightFactorization]
    rw [← hfactorization]
    change (rightFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_A current.decomposition
      current.right_decodes inner rightFactorization letter

private def firstLetterPhysicalStages_A
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : ℝ}
    {sourceLength : alphabet → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context) :
    ∀ stage, FirstLetterPhysicalStageA systems stage
  | 0 => firstLetterPhysicalBase_A systems
  | stage + 1 => firstLetterPhysicalSucc_A systems stage
      (firstLetterPhysicalStages_A systems stage)

private structure SameMarkerReturnRelabelingA
    {α : Type*} {word : InfiniteWord α} {marker : Word α}
    {leftRank rightRank : ℕ}
    (left : ReturnDecomposition word marker leftRank)
    (right : ReturnDecomposition word marker rightRank) where
  relabel : Fin leftRank ≃ Fin rightRank
  blocks_eq : ∀ letter,
    right.blocks (relabel letter) = left.blocks letter
  word_eq : ∀ position,
    relabel (left.derived position) = right.derived position

private theorem sameMarkerReturnRelabelingA_exists
    {α : Type*} {word : InfiniteWord α} {marker : Word α}
    {leftRank rightRank : ℕ}
    (left : ReturnDecomposition word marker leftRank)
    (right : ReturnDecomposition word marker rightRank) :
    Nonempty (SameMarkerReturnRelabelingA left right) := by
  classical
  have hexistsRight : ∀ letter : Fin leftRank,
      ∃ target : Fin rightRank,
        right.blocks target = left.blocks letter := by
    intro letter
    obtain ⟨target, htarget⟩ := right.every_return_is_block
      (left.blocks letter) (left.blocks_are_returns letter)
    exact ⟨target, htarget⟩
  let toFun : Fin leftRank → Fin rightRank := fun letter =>
    Classical.choose (hexistsRight letter)
  have hblocks : ∀ letter,
      right.blocks (toFun letter) = left.blocks letter := by
    intro letter
    exact Classical.choose_spec (hexistsRight letter)
  have htoFunInjective : Function.Injective toFun := by
    intro leftLetter rightLetter heq
    apply left.blocks_injective
    rw [← hblocks leftLetter, ← hblocks rightLetter, heq]
  have htoFunSurjective : Function.Surjective toFun := by
    intro target
    obtain ⟨source, hsource⟩ := left.every_return_is_block
      (right.blocks target) (right.blocks_are_returns target)
    refine ⟨source, ?_⟩
    apply right.blocks_injective
    rw [hblocks source, hsource]
  let relabel : Fin leftRank ≃ Fin rightRank :=
    Equiv.ofBijective toFun ⟨htoFunInjective, htoFunSurjective⟩
  have hblocksRelabel : ∀ letter,
      right.blocks (relabel letter) = left.blocks letter := hblocks
  have hcuts : ∀ position, left.cut position = right.cut position := by
    intro position
    induction position with
    | zero => rw [left.cut_zero, right.cut_zero]
    | succ position ih =>
        have hleftAt := left.block_marker_at_cut position
        have hleftAtRight : InfiniteFactorAt word
            (left.blocks (left.derived position) ++ marker)
            (right.cut position) := by
          rw [← ih]
          exact hleftAt
        have hat : InfiniteFactorAt word
            (right.blocks (relabel (left.derived position)) ++ marker)
            (right.cut position) := by
          rw [hblocksRelabel]
          exact hleftAtRight
        have hblock := right.block_eq_of_block_marker_at_cut
          (relabel (left.derived position)) position hat
        have hletter : relabel (left.derived position) =
            right.derived position := right.blocks_injective hblock
        rw [left.cut_succ, right.cut_succ, ih, ← hletter,
          hblocksRelabel]
  have hword : ∀ position,
      relabel (left.derived position) = right.derived position := by
    intro position
    have hleftAt := left.block_marker_at_cut position
    have hleftAtRight : InfiniteFactorAt word
        (left.blocks (left.derived position) ++ marker)
        (right.cut position) := by
      rw [← hcuts position]
      exact hleftAt
    have hat : InfiniteFactorAt word
        (right.blocks (relabel (left.derived position)) ++ marker)
        (right.cut position) := by
      rw [hblocksRelabel]
      exact hleftAtRight
    have hblock := right.block_eq_of_block_marker_at_cut
      (relabel (left.derived position)) position hat
    exact right.blocks_injective hblock
  exact ⟨{
    relabel := relabel
    blocks_eq := hblocksRelabel
    word_eq := hword }⟩

private def castReturnDecompositionMarker_A
    {α : Type*} {word : InfiniteWord α}
    {left right : Word α} {rank : ℕ}
    (hmarker : left = right)
    (decomposition : ReturnDecomposition word left rank) :
    ReturnDecomposition word right rank := by
  subst right
  exact decomposition

@[simp] private theorem castReturnDecompositionMarker_A_blocks
    {α : Type*} {word : InfiniteWord α}
    {left right : Word α} {rank : ℕ}
    (hmarker : left = right)
    (decomposition : ReturnDecomposition word left rank) :
    (castReturnDecompositionMarker_A hmarker decomposition).blocks =
      decomposition.blocks := by
  subst right
  rfl

@[simp] private theorem castReturnDecompositionMarker_A_derived
    {α : Type*} {word : InfiniteWord α}
    {left right : Word α} {rank : ℕ}
    (hmarker : left = right)
    (decomposition : ReturnDecomposition word left rank) :
    (castReturnDecompositionMarker_A hmarker decomposition).derived =
      decomposition.derived := by
  subst right
  rfl

private theorem firstLetterPhysical_has_canonicalRealization_A
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : ℝ}
    {sourceLength : alphabet → ℝ}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (hmarkerEq : ∀ level,
      context.markers.marker level = synchronized.word.take (level + 1))
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (stage : ℕ) (physical : FirstLetterPhysicalStageA systems stage) :
    Nonempty (FirstLetterCanonicalBaseRealization systems stage) := by
  classical
  let level := physical.marker.length - 1
  have hmarkerLengthPositive : 0 < physical.marker.length :=
    List.length_pos_of_ne_nil physical.decomposition.marker_ne_nil
  have hlevelLength : level + 1 = physical.marker.length := by
    dsimp [level]
    omega
  have hphysicalMarker : synchronized.word.take physical.marker.length =
      physical.marker := by
    simpa [InfiniteFactorAt] using physical.decomposition.marker_at_zero
  have hmarker : context.markers.marker level = physical.marker := by
    rw [hmarkerEq, hlevelLength]
    exact hphysicalMarker
  let canonical : ReturnDecomposition synchronized.word physical.marker
      (context.decompositions.rank level) :=
    castReturnDecompositionMarker_A hmarker
      (context.decompositions.decomposition level)
  let comparison := Classical.choice
    (sameMarkerReturnRelabelingA_exists physical.decomposition canonical)
  let relabel := comparison.relabel
  have hword : ∀ position,
      relabel (systems.word stage position) =
        (context.decompositions.decomposition level).derived position := by
    intro position
    rw [← physical.derived_eq]
    have hcomparison := comparison.word_eq position
    change relabel (physical.decomposition.derived position) =
      canonical.derived position at hcomparison
    simpa [canonical] using hcomparison
  have hblocks : ∀ current,
      (context.decompositions.decomposition level).blocks
          (relabel current) = physical.decomposition.blocks current := by
    intro current
    have hcomparison := comparison.blocks_eq current
    change canonical.blocks (relabel current) =
      physical.decomposition.blocks current at hcomparison
    simpa [canonical] using hcomparison
  have hleft : ∀ letter,
      ((systems.leftSubstitution stage) letter).map relabel =
        (context.tower.left level).factorization.substitution
          (relabel letter) := by
    intro letter
    apply flatMap_returnWords_injective
      (context.decompositions.decomposition level).blocks_injective
      (context.decompositions.decomposition level).blocks_are_returns
    change (((systems.leftSubstitution stage) letter).map relabel).flatMap
        (context.decompositions.decomposition level).blocks =
      ((context.tower.left level).factorization.factor
        (relabel letter)).flatMap
          (context.decompositions.decomposition level).blocks
    rw [List.flatMap_map]
    simp_rw [hblocks]
    change ((systems.leftSubstitution stage) letter).flatMap
        physical.decomposition.blocks = _
    rw [physical.left_decodes letter, ← hblocks letter,
      (context.tower.left level).factorization.factor_decodes]
    rfl
  have hright : ∀ letter,
      ((systems.rightSubstitution stage) letter).map relabel =
        (context.tower.right level).factorization.substitution
          (relabel letter) := by
    intro letter
    apply flatMap_returnWords_injective
      (context.decompositions.decomposition level).blocks_injective
      (context.decompositions.decomposition level).blocks_are_returns
    change (((systems.rightSubstitution stage) letter).map relabel).flatMap
        (context.decompositions.decomposition level).blocks =
      ((context.tower.right level).factorization.factor
        (relabel letter)).flatMap
          (context.decompositions.decomposition level).blocks
    rw [List.flatMap_map]
    simp_rw [hblocks]
    change ((systems.rightSubstitution stage) letter).flatMap
        physical.decomposition.blocks = _
    rw [physical.right_decodes letter, ← hblocks letter,
      (context.tower.right level).factorization.factor_decodes]
    rfl
  exact ⟨{
    level := level
    relabel := relabel
    word_relabels := hword
    left_relabels := hleft
    right_relabels := hright }⟩

/-- 1d: every abstract first-letter stage has a physical prefix marker and a
canonical base realization, including both exact source equations. -/
theorem firstLetterStages_have_canonicalBaseRealizations
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context) :
    forall stage, Nonempty (FirstLetterCanonicalBaseRealization systems stage) := by
  intro stage
  exact firstLetterPhysical_has_canonicalRealization_A
    context.markers.marker_eq_take systems stage
      (firstLetterPhysicalStages_A systems stage)

/-- Two first-letter stages whose word and both source tables repeat under
one alphabet relabeling. -/
structure SimultaneousFirstLetterRepetition
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context) where
  earlier : Nat
  later : Nat
  earlier_lt_later : earlier < later
  relabel : Fin (systems.rank earlier) ≃ Fin (systems.rank later)
  word_relabels : forall position,
    relabel (systems.word earlier position) = systems.word later position
  left_relabels : forall letter,
    ((systems.leftSubstitution earlier) letter).map relabel =
      systems.leftSubstitution later (relabel letter)
  right_relabels : forall letter,
    ((systems.rightSubstitution earlier) letter).map relabel =
      systems.rightSubstitution later (relabel letter)

private theorem wordRelabeling_trans_m4
    {α β γ : Type*}
    {left : Nat → α} {middle : Nat → β} {right : Nat → γ}
    (first : α ≃ β) (second : β ≃ γ)
    (hfirst : ∀ position, first (left position) = middle position)
    (hsecond : ∀ position, second (middle position) = right position) :
    ∀ position, (first.trans second) (left position) = right position := by
  intro position
  rw [Equiv.trans_apply, hfirst, hsecond]

private theorem wordRelabeling_symm_m4
    {α β : Type*} {left : Nat → α} {right : Nat → β}
    (relabel : α ≃ β)
    (h : ∀ position, relabel (left position) = right position) :
    ∀ position, relabel.symm (right position) = left position := by
  intro position
  rw [← h position]
  simp

private theorem substitutionRelabeling_trans_m4
    {α β γ : Type*}
    {left : Substitution α} {middle : Substitution β}
    {right : Substitution γ}
    (first : α ≃ β) (second : β ≃ γ)
    (hfirst : ∀ letter, (left letter).map first = middle (first letter))
    (hsecond : ∀ letter, (middle letter).map second = right (second letter)) :
    ∀ letter, (left letter).map (first.trans second) =
      right ((first.trans second) letter) := by
  intro letter
  rw [show (left letter).map (first.trans second) =
      ((left letter).map first).map second by simp [List.map_map]]
  rw [hfirst, hsecond]
  rfl

private theorem substitutionRelabeling_symm_m4
    {α β : Type*} {left : Substitution α} {right : Substitution β}
    (relabel : α ≃ β)
    (h : ∀ letter, (left letter).map relabel = right (relabel letter)) :
    ∀ letter, (right letter).map relabel.symm =
      left (relabel.symm letter) := by
  intro letter
  have hmapped := congrArg (List.map relabel.symm)
    (h (relabel.symm letter))
  simpa [List.map_map] using hmapped.symm

/-- 1e: the finite canonical paired code repeats along the infinite
first-letter derivation. -/
theorem pairedFiniteCoding_has_simultaneousFirstLetterRepetition
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (realization : forall stage,
      FirstLetterCanonicalBaseRealization systems stage) :
    Nonempty (SimultaneousFirstLetterRepetition systems) := by
  classical
  let encode : Nat → Fin context.coding.codeCount := fun stage =>
    context.coding.code (realization stage).level
  obtain ⟨first, second, hne, hcode⟩ :=
    Finite.exists_ne_map_eq_of_infinite encode
  have construct : ∀ earlier later : Nat, earlier < later →
      encode earlier = encode later →
      Nonempty (SimultaneousFirstLetterRepetition systems) := by
    intro earlier later hearlierLater hsameCode
    let earlierRealization := realization earlier
    let laterRealization := realization later
    have hphysicalCode :
        context.coding.code earlierRealization.level =
          context.coding.code laterRealization.level := by
      simpa [encode, earlierRealization, laterRealization] using hsameCode
    let physical := context.coding.same_code earlierRealization.level
      laterRealization.level hphysicalCode
    let relabel : Fin (systems.rank earlier) ≃ Fin (systems.rank later) :=
      (earlierRealization.relabel.trans physical.currentRelabel).trans
        laterRealization.relabel.symm
    have hwordFirst : ∀ position,
        (earlierRealization.relabel.trans physical.currentRelabel)
            (systems.word earlier position) =
          (context.decompositions.decomposition
            laterRealization.level).derived position :=
      wordRelabeling_trans_m4 earlierRealization.relabel
        physical.currentRelabel earlierRealization.word_relabels
        physical.current_derived_eq
    have hwordToLater : ∀ position,
        laterRealization.relabel.symm
            ((context.decompositions.decomposition
              laterRealization.level).derived position) =
          systems.word later position :=
      wordRelabeling_symm_m4 laterRealization.relabel
        laterRealization.word_relabels
    have hword : ∀ position,
        relabel (systems.word earlier position) = systems.word later position :=
      wordRelabeling_trans_m4
        (earlierRealization.relabel.trans physical.currentRelabel)
        laterRealization.relabel.symm hwordFirst hwordToLater
    have hleftFirst : ∀ letter,
        ((systems.leftSubstitution earlier) letter).map
            (earlierRealization.relabel.trans physical.currentRelabel) =
          (context.tower.left laterRealization.level).factorization.substitution
            ((earlierRealization.relabel.trans physical.currentRelabel)
              letter) :=
      substitutionRelabeling_trans_m4 earlierRealization.relabel
        physical.currentRelabel earlierRealization.left_relabels
        physical.left_image_eq
    have hleftToLater : ∀ letter,
        ((context.tower.left
          laterRealization.level).factorization.substitution letter).map
            laterRealization.relabel.symm =
          systems.leftSubstitution later
            (laterRealization.relabel.symm letter) :=
      substitutionRelabeling_symm_m4 laterRealization.relabel
        laterRealization.left_relabels
    have hleft : ∀ letter,
        ((systems.leftSubstitution earlier) letter).map relabel =
          systems.leftSubstitution later (relabel letter) :=
      substitutionRelabeling_trans_m4
        (earlierRealization.relabel.trans physical.currentRelabel)
        laterRealization.relabel.symm hleftFirst hleftToLater
    have hrightFirst : ∀ letter,
        ((systems.rightSubstitution earlier) letter).map
            (earlierRealization.relabel.trans physical.currentRelabel) =
          (context.tower.right laterRealization.level).factorization.substitution
            ((earlierRealization.relabel.trans physical.currentRelabel)
              letter) :=
      substitutionRelabeling_trans_m4 earlierRealization.relabel
        physical.currentRelabel earlierRealization.right_relabels
        physical.right_image_eq
    have hrightToLater : ∀ letter,
        ((context.tower.right
          laterRealization.level).factorization.substitution letter).map
            laterRealization.relabel.symm =
          systems.rightSubstitution later
            (laterRealization.relabel.symm letter) :=
      substitutionRelabeling_symm_m4 laterRealization.relabel
        laterRealization.right_relabels
    have hright : ∀ letter,
        ((systems.rightSubstitution earlier) letter).map relabel =
          systems.rightSubstitution later (relabel letter) :=
      substitutionRelabeling_trans_m4
        (earlierRealization.relabel.trans physical.currentRelabel)
        laterRealization.relabel.symm hrightFirst hrightToLater
    exact ⟨{
      earlier := earlier
      later := later
      earlier_lt_later := hearlierLater
      relabel := relabel
      word_relabels := hword
      left_relabels := hleft
      right_relabels := hright }⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact construct first second hlt hcode
  · exact construct second first hgt hcode.symm

private theorem finiteFactorAt_map_iff_m4f
    {α β : Type*} {coding : α → β} (hcoding : Function.Injective coding)
    {ambient factor : Word α} {start : Nat} :
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

private theorem IsReturnWord.map_injective_m4f
    {α β : Type*} (coding : α → β) (hcoding : Function.Injective coding)
    {word : InfiniteWord α} {marker block : Word α}
    (hreturn : IsReturnWord word marker block) :
    IsReturnWord (fun n => coding (word n))
      (marker.map coding) (block.map coding) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnil
    apply hreturn.1
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa using this
  · intro hnil
    apply hreturn.2.1
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa using this
  · obtain ⟨start, hstart⟩ := hreturn.2.2.1
    refine ⟨start, ?_⟩
    simpa [List.map_append] using InfiniteFactorAt.map_m4 coding hstart
  · rcases hreturn.2.2.2.1 with ⟨tail, htail⟩
    refine ⟨tail.map coding, ?_⟩
    simpa [List.map_append] using congrArg (List.map coding) htail
  · intro start
    simpa [List.map_append] using
      (finiteFactorAt_map_iff_m4f (coding := coding) hcoding
        (ambient := block ++ marker) (factor := marker)
        (start := start)).trans (hreturn.2.2.2.2 start)

private def mapReturnDecompositionEquiv_m4f
    {α β : Type*} (relabel : α ≃ β)
    {word : InfiniteWord α} {marker : Word α} {rank : Nat}
    (decomposition : ReturnDecomposition word marker rank) :
    ReturnDecomposition (fun n => relabel (word n))
      (marker.map relabel) rank where
  rank_pos := decomposition.rank_pos
  marker_ne_nil := by
    intro hnil
    apply decomposition.marker_ne_nil
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa using this
  marker_at_zero := InfiniteFactorAt.map_m4 relabel
    decomposition.marker_at_zero
  blocks := fun letter => (decomposition.blocks letter).map relabel
  blocks_injective := by
    intro left right heq
    apply decomposition.blocks_injective
    exact (List.map_injective_iff.mpr relabel.injective) heq
  blocks_are_returns := fun letter =>
    IsReturnWord.map_injective_m4f relabel relabel.injective
      (decomposition.blocks_are_returns letter)
  every_return_is_block := by
    intro returnWord hreturn
    let pulled := returnWord.map relabel.symm
    have hpulled : IsReturnWord word marker pulled := by
      have hmapped := IsReturnWord.map_injective_m4f relabel.symm
        relabel.symm.injective hreturn
      simpa [pulled, List.map_map] using hmapped
    obtain ⟨letter, hletter⟩ :=
      decomposition.every_return_is_block pulled hpulled
    refine ⟨letter, ?_⟩
    have hmapped := congrArg (List.map relabel) hletter
    simpa [pulled, List.map_map] using hmapped
  derived := decomposition.derived
  cut := decomposition.cut
  cut_zero := decomposition.cut_zero
  cut_succ := by intro position; simpa using decomposition.cut_succ position
  block_at_cut := fun position =>
    InfiniteFactorAt.map_m4 relabel (decomposition.block_at_cut position)

private theorem mapWord_flatMap_blocks_m4f
    {α β : Type*} (source : Substitution α)
    (induced : Substitution β) (blocks : β → Word α)
    (hletter : ∀ letter,
      (induced letter).flatMap blocks = source.mapWord (blocks letter)) :
    ∀ letters : Word β,
      (induced.mapWord letters).flatMap blocks =
        source.mapWord (letters.flatMap blocks) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      rw [Substitution.mapWord_cons, List.flatMap_append,
        hletter, List.flatMap_cons, Substitution.mapWord_append, ih]

private def castPrefixReturnFactorizationWord_m4f
    {α : Type*} {source : Substitution α}
    {left right : InfiniteWord α} {marker : Word α} {rank : ℕ}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank)
    (factorization : PrefixReturnFactorization source decomposition) :
    PrefixReturnFactorization source
      (castReturnDecompositionWord hword decomposition) := by
  subst right
  exact factorization

@[simp] private theorem castPrefixReturnFactorizationWord_m4f_substitution
    {α : Type*} {source : Substitution α}
    {left right : InfiniteWord α} {marker : Word α} {rank : ℕ}
    (hword : left = right)
    (decomposition : ReturnDecomposition left marker rank)
    (factorization : PrefixReturnFactorization source decomposition) :
    (castPrefixReturnFactorizationWord_m4f hword decomposition
      factorization).substitution = factorization.substitution := by
  subst right
  rfl

private theorem composedFactor_decodes_m4f
    {α : Type*} {word : InfiniteWord α}
    {outerMarker : Word α} {outerRank : ℕ}
    (outer : ReturnDecomposition word outerMarker outerRank)
    {source : Substitution α}
    {outerSubstitution : Substitution (Fin outerRank)}
    (houter : ∀ letter,
      (outerSubstitution letter).flatMap outer.blocks =
        source.mapWord (outer.blocks letter))
    {innerMarker : Word (Fin outerRank)} {innerRank : ℕ}
    (inner : ReturnDecomposition outer.derived innerMarker innerRank)
    (factorization : PrefixReturnFactorization outerSubstitution inner)
    (letter : Fin innerRank) :
    (factorization.substitution letter).flatMap
        (composeReturnDecompositions outer inner).blocks =
      source.mapWord
        ((composeReturnDecompositions outer inner).blocks letter) := by
  change (factorization.factor letter).flatMap
      (fun innerLetter => (inner.blocks innerLetter).flatMap outer.blocks) =
    source.mapWord ((inner.blocks letter).flatMap outer.blocks)
  rw [← List.flatMap_assoc, factorization.factor_decodes]
  exact mapWord_flatMap_blocks_m4f source outerSubstitution outer.blocks
    houter (inner.blocks letter)

private theorem mapWord_relabels_m4f
    {α β : Type*} {left : Substitution α} {right : Substitution β}
    (relabel : α ≃ β)
    (hletter : ∀ letter, (left letter).map relabel =
      right (relabel letter)) :
    ∀ letters : Word α,
      (left.mapWord letters).map relabel =
        right.mapWord (letters.map relabel) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.map_cons]
      rw [Substitution.mapWord_cons, Substitution.mapWord_cons,
        List.map_append, hletter, ih]

private theorem flatMap_relabels_blocks_m4f
    {α β γ δ : Type*} (sourceRelabel : α → β)
    (returnRelabel : γ → δ) (leftBlocks : γ → Word α)
    (rightBlocks : δ → Word β)
    (hblocks : ∀ letter,
      rightBlocks (returnRelabel letter) =
        (leftBlocks letter).map sourceRelabel) :
    ∀ letters : Word γ,
      (letters.map returnRelabel).flatMap rightBlocks =
        (letters.flatMap leftBlocks).map sourceRelabel := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [hblocks, ih]

private structure FirstLetterIntervalDecompositionM4F
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet → Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (startStage endStage : Nat) where
  marker : Word (Fin (systems.rank startStage))
  decomposition : ReturnDecomposition (systems.word startStage) marker
    (systems.rank endStage)
  derived_eq : decomposition.derived = systems.word endStage
  left_decodes : ∀ letter,
    ((systems.leftSubstitution endStage) letter).flatMap
        decomposition.blocks =
      (systems.leftSubstitution startStage).mapWord
        (decomposition.blocks letter)
  right_decodes : ∀ letter,
    ((systems.rightSubstitution endStage) letter).flatMap
        decomposition.blocks =
      (systems.rightSubstitution startStage).mapWord
        (decomposition.blocks letter)

private def firstLetterInterval_one_m4f
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet → Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (startStage : Nat) :
    FirstLetterIntervalDecompositionM4F systems startStage
      (startStage + 1) where
  marker := [(systems.word startStage).head]
  decomposition := systems.stepDecomposition startStage
  derived_eq := systems.step_word_eq startStage
  left_decodes := by
    intro letter
    rw [systems.left_succ_eq startStage]
    exact (systems.leftStepFactorization startStage).factor_decodes letter
  right_decodes := by
    intro letter
    rw [systems.right_succ_eq startStage]
    exact (systems.rightStepFactorization startStage).factor_decodes letter

private def firstLetterInterval_succ_m4f
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet → Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    {startStage endStage : Nat}
    (current : FirstLetterIntervalDecompositionM4F systems
      startStage endStage) :
    FirstLetterIntervalDecompositionM4F systems startStage
      (endStage + 1) := by
  classical
  let inner := castReturnDecompositionWord current.derived_eq.symm
    (systems.stepDecomposition endStage)
  let leftFactorization := castPrefixReturnFactorizationWord_m4f
    current.derived_eq.symm (systems.stepDecomposition endStage)
      (systems.leftStepFactorization endStage)
  let rightFactorization := castPrefixReturnFactorizationWord_m4f
    current.derived_eq.symm (systems.stepDecomposition endStage)
      (systems.rightStepFactorization endStage)
  let composed := composeReturnDecompositions current.decomposition inner
  refine {
    marker := [(systems.word endStage).head].flatMap
      current.decomposition.blocks ++ current.marker
    decomposition := composed
    derived_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }
  · change inner.derived = systems.word (endStage + 1)
    rw [castReturnDecompositionWord_derived]
    exact systems.step_word_eq endStage
  · intro letter
    rw [systems.left_succ_eq endStage]
    have hfactorization : leftFactorization.substitution =
        (systems.leftStepFactorization endStage).substitution := by
      simp [leftFactorization]
    rw [← hfactorization]
    change (leftFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_m4f current.decomposition
      current.left_decodes inner leftFactorization letter
  · intro letter
    rw [systems.right_succ_eq endStage]
    have hfactorization : rightFactorization.substitution =
        (systems.rightStepFactorization endStage).substitution := by
      simp [rightFactorization]
    rw [← hfactorization]
    change (rightFactorization.substitution letter).flatMap composed.blocks = _
    exact composedFactor_decodes_m4f current.decomposition
      current.right_decodes inner rightFactorization letter

private def firstLetterInterval_m4f
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet → Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context)
    (startStage : Nat) :
    ∀ extraSteps : Nat,
      FirstLetterIntervalDecompositionM4F systems startStage
        (startStage + (extraSteps + 1))
  | 0 => by
      simpa using firstLetterInterval_one_m4f systems startStage
  | extraSteps + 1 => by
      simpa [Nat.add_assoc] using
        firstLetterInterval_succ_m4f systems
          (firstLetterInterval_m4f systems startStage extraSteps)

private def castFirstLetterIntervalEnd_m4f
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet → Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {startStage leftEnd rightEnd : Nat}
    (hend : leftEnd = rightEnd)
    (interval : FirstLetterIntervalDecompositionM4F systems
      startStage leftEnd) :
    FirstLetterIntervalDecompositionM4F systems startStage rightEnd := by
  subst rightEnd
  exact interval

/-- A literal self-return decomposition at the shifted repeated stage, with
both local source tables commuting through its decoder. -/
structure PairedFirstLetterSelfReturn
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context) where
  stage : Nat
  marker : Word (Fin (systems.rank stage))
  decomposition : ReturnDecomposition (systems.word stage) marker
    (systems.rank stage)
  derived_eq : decomposition.derived = systems.word stage
  left_decodes : forall letter,
    ((systems.leftSubstitution stage) letter).flatMap decomposition.blocks =
      (systems.leftSubstitution stage).mapWord (decomposition.blocks letter)
  right_decodes : forall letter,
    ((systems.rightSubstitution stage) letter).flatMap decomposition.blocks =
      (systems.rightSubstitution stage).mapWord (decomposition.blocks letter)

/-- 1f: shift a simultaneous stage repetition once and compose the intervening
return decompositions to obtain a literal self-return. -/
theorem simultaneousFirstLetterRepetition_has_selfReturn
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (repetition : SimultaneousFirstLetterRepetition systems) :
    Nonempty (PairedFirstLetterSelfReturn systems) := by
  classical
  let extraSteps := repetition.later - repetition.earlier - 1
  have hend : repetition.earlier + (extraSteps + 1) =
      repetition.later := by
    have hlt := repetition.earlier_lt_later
    dsimp [extraSteps]
    omega
  let raw := firstLetterInterval_m4f systems repetition.earlier extraSteps
  let interval := castFirstLetterIntervalEnd_m4f hend raw
  have hword :
      (fun position => repetition.relabel
        (systems.word repetition.earlier position)) =
        systems.word repetition.later := by
    funext position
    exact repetition.word_relabels position
  let mapped := mapReturnDecompositionEquiv_m4f repetition.relabel
    interval.decomposition
  let selfDecomposition := castReturnDecompositionWord hword mapped
  have hselfBlocks : ∀ letter,
      selfDecomposition.blocks letter =
        (interval.decomposition.blocks letter).map repetition.relabel := by
    intro letter
    simp [selfDecomposition, mapped, mapReturnDecompositionEquiv_m4f]
  refine ⟨{
    stage := repetition.later
    marker := interval.marker.map repetition.relabel
    decomposition := selfDecomposition
    derived_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }⟩
  · change selfDecomposition.derived = systems.word repetition.later
    rw [castReturnDecompositionWord_derived]
    change interval.decomposition.derived = systems.word repetition.later
    exact interval.derived_eq
  · intro letter
    calc
      ((systems.leftSubstitution repetition.later) letter).flatMap
          selfDecomposition.blocks =
          (((systems.leftSubstitution repetition.later) letter).flatMap
            interval.decomposition.blocks).map repetition.relabel := by
              simpa using
                flatMap_relabels_blocks_m4f repetition.relabel id
                  interval.decomposition.blocks selfDecomposition.blocks
                  (fun current => by simpa using hselfBlocks current)
                  ((systems.leftSubstitution repetition.later) letter)
      _ = ((systems.leftSubstitution repetition.earlier).mapWord
            (interval.decomposition.blocks letter)).map
              repetition.relabel := by
          rw [interval.left_decodes]
      _ = (systems.leftSubstitution repetition.later).mapWord
            ((interval.decomposition.blocks letter).map
              repetition.relabel) :=
          mapWord_relabels_m4f repetition.relabel
            repetition.left_relabels
            (interval.decomposition.blocks letter)
      _ = (systems.leftSubstitution repetition.later).mapWord
            (selfDecomposition.blocks letter) := by
          rw [hselfBlocks]
  · intro letter
    calc
      ((systems.rightSubstitution repetition.later) letter).flatMap
          selfDecomposition.blocks =
          (((systems.rightSubstitution repetition.later) letter).flatMap
            interval.decomposition.blocks).map repetition.relabel := by
              simpa using
                flatMap_relabels_blocks_m4f repetition.relabel id
                  interval.decomposition.blocks selfDecomposition.blocks
                  (fun current => by simpa using hselfBlocks current)
                  ((systems.rightSubstitution repetition.later) letter)
      _ = ((systems.rightSubstitution repetition.earlier).mapWord
            (interval.decomposition.blocks letter)).map
              repetition.relabel := by
          rw [interval.right_decodes]
      _ = (systems.rightSubstitution repetition.later).mapWord
            ((interval.decomposition.blocks letter).map
              repetition.relabel) :=
          mapWord_relabels_m4f repetition.relabel
            repetition.right_relabels
            (interval.decomposition.blocks letter)
      _ = (systems.rightSubstitution repetition.later).mapWord
            (selfDecomposition.blocks letter) := by
          rw [hselfBlocks]

private theorem ReturnDecomposition.uniformlyRecurrent_derived_clusterD
    {delta : Type u} {word : InfiniteWord delta} {marker : Word delta}
    {rank : Nat} (decomposition : ReturnDecomposition word marker rank)
    (huniform : IsUniformlyRecurrent word) :
    IsUniformlyRecurrent decomposition.derived := by
  intro factor hfactor
  obtain ⟨origin, horigin⟩ := hfactor
  let encoded := factor.flatMap decomposition.blocks
  have hactual :
      (decomposition.derived.drop origin).take factor.length = factor :=
    horigin
  have hencodedAt := decodedMarkerAtCut decomposition origin factor.length
  change InfiniteFactorAt word
      ((((decomposition.derived.drop origin).take factor.length).flatMap
          decomposition.blocks) ++ marker)
      (decomposition.cut origin) at hencodedAt
  rw [hactual] at hencodedAt
  change InfiniteFactorAt word (encoded ++ marker)
      (decomposition.cut origin) at hencodedAt
  obtain ⟨gap, hgapPos, hbounded⟩ :=
    huniform (encoded ++ marker) ⟨decomposition.cut origin, hencodedAt⟩
  refine ⟨gap, hgapPos, ?_⟩
  intro start
  obtain ⟨physicalOffset, hphysicalOffset, hat⟩ :=
    hbounded (decomposition.cut start)
  have hmarkerPrefix : marker <+: encoded ++ marker :=
    marker_prefix_flatMap_returnWords decomposition.blocks
      decomposition.blocks_are_returns factor
  have hmarkerFinite : FiniteFactorAt (encoded ++ marker) marker 0 := by
    refine ⟨by simpa using hmarkerPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hmarkerPrefix).symm
  have hmarkerAt : InfiniteFactorAt word marker
      (decomposition.cut start + physicalOffset) := by
    simpa using hat.of_finiteFactorAt hmarkerFinite
  obtain ⟨index, hcutIndex⟩ :=
    decomposition.marker_occurrence_eq_cut hmarkerAt
  have hstartLe : start ≤ index := by
    by_contra hnot
    have hcutLt := decomposition.cut_strictMono (by omega : index < start)
    rw [hcutIndex] at hcutLt
    omega
  have hatCut : InfiniteFactorAt word
      (factor.flatMap decomposition.blocks ++ marker)
      (decomposition.cut index) := by
    change InfiniteFactorAt word (encoded ++ marker) (decomposition.cut index)
    rw [hcutIndex]
    exact hat
  have hderivedFactor :=
    derivedFactor_of_decodedMarkerAtCut decomposition factor index hatCut
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

/-- Uniform recurrence is reflected through an injective alphabet coding
when the coded streams agree pointwise. -/
private theorem uniformlyRecurrent_of_equiv
    {alpha beta : Type*} (equiv : alpha ≃ beta)
    {left : InfiniteWord alpha} {right : InfiniteWord beta}
    (hword : forall position, equiv (left position) = right position)
    (hright : IsUniformlyRecurrent right) :
    IsUniformlyRecurrent left := by
  have hstream : Stream'.map equiv left = right := by
    funext position
    exact hword position
  intro factor hfactor
  have hmappedFactor : IsInfiniteFactor right (factor.map equiv) := by
    obtain ⟨start, hstart⟩ := hfactor
    have hmappedAt : InfiniteFactorAt (Stream'.map equiv left)
        (factor.map equiv) start := by
      unfold InfiniteFactorAt at hstart ⊢
      have hmapped := congrArg (List.map equiv) hstart
      simpa [Stream'.drop_map, Stream'.map_take] using hmapped
    rw [hstream] at hmappedAt
    exact ⟨start, hmappedAt⟩
  obtain ⟨gap, hgapPos, hbounded⟩ :=
    hright (factor.map equiv) hmappedFactor
  refine ⟨gap, hgapPos, ?_⟩
  intro start
  obtain ⟨offset, hoffset, hat⟩ := hbounded start
  refine ⟨offset, hoffset, ?_⟩
  rw [← hstream] at hat
  unfold InfiniteFactorAt at hat ⊢
  have hinverse := congrArg (List.map equiv.symm) hat
  simpa [Stream'.drop_map, Stream'.map_take, List.map_map] using hinverse

/-- Every abstract first-letter derived stage is uniformly recurrent. -/
private theorem firstLetterStage_uniformlyRecurrent
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    (systems : IteratedPairedFirstLetterDerivedSystems context) :
    forall stage, IsUniformlyRecurrent (systems.word stage) := by
  intro stage
  induction stage with
  | zero =>
      obtain ⟨linear⟩ :=
        metricSynchronizedCore_has_aperiodicLinearRecurrence synchronized
          context.notPeriodic
      have hderived :=
        ReturnDecomposition.uniformlyRecurrent_derived_clusterD
          (context.decompositions.decomposition context.repetition.later)
          linear.uniformlyRecurrent
      exact uniformlyRecurrent_of_equiv systems.baseRelabel
        systems.base_word_eq hderived
  | succ stage ih =>
      have hderived :=
        ReturnDecomposition.uniformlyRecurrent_derived_clusterD
          (systems.stepDecomposition stage) ih
      rw [systems.step_word_eq stage] at hderived
      exact hderived

/-! ## Growth and primitivity of the self-return decoder -/

private theorem iterateWord_add_clusterD
    {alpha : Type*} (source : Substitution alpha)
    (left right : Nat) (letters : Word alpha) :
    source.iterateWord (left + right) letters =
      source.iterateWord left (source.iterateWord right letters) := by
  induction left with
  | zero => simp
  | succ left ih =>
      simpa only [Nat.succ_add, Substitution.iterateWord_succ] using
        congrArg source.mapWord ih

private theorem iterateWord_append_clusterD
    {alpha : Type*} (source : Substitution alpha) (level : Nat) :
    forall left right : Word alpha,
      source.iterateWord level (left ++ right) =
        source.iterateWord level left ++ source.iterateWord level right := by
  intro left right
  induction level with
  | zero => rfl
  | succ level ih =>
      simp only [Substitution.iterateWord_succ, ih,
        Substitution.mapWord_append]

private theorem iterateWord_infix_clusterD
    {alpha : Type*} (source : Substitution alpha) (level : Nat)
    {small large : Word alpha} (hfactor : small <:+: large) :
    source.iterateWord level small <:+:
      source.iterateWord level large := by
  rcases hfactor with ⟨left, right, rfl⟩
  refine ⟨source.iterateWord level left,
    source.iterateWord level right, ?_⟩
  simp only [iterateWord_append_clusterD, List.append_assoc]

private theorem length_le_iterateWord_clusterD
    {alpha : Type*} (source : Substitution alpha)
    (level : Nat) (letters : Word alpha) :
    letters.length ≤ (source.iterateWord level letters).length := by
  induction level with
  | zero => exact le_rfl
  | succ level ih =>
      exact ih.trans
        (source.length_le_mapWord (source.iterateWord level letters))

private theorem succ_le_iterateLetter_length_clusterD
    {alpha : Type*} (source : Substitution alpha) {seed : alpha}
    (hprolongable : source.ProlongableOn seed) (level : Nat) :
    level + 1 ≤ (source.iterateLetter level seed).length := by
  have hstrict : forall n : Nat,
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

private theorem prolongableOn_head_of_fixedPoint_clusterD
    {alpha : Type*} {source : Substitution alpha}
    {word : InfiniteWord alpha}
    (hfixed : source.IsFixedPoint word)
    (hlength : 1 < (source word.head).length) :
    source.ProlongableOn word.head := by
  have hhead : source.imageHead word.head = word.head := by
    have hzero := congrFun hfixed 0
    simpa using hzero
  have htail : source.imageTail word.head ≠ [] := by
    intro hnil
    rw [← source.imageHead_cons_imageTail] at hlength
    simp [hnil] at hlength
  refine ⟨source.imageTail word.head, htail, ?_⟩
  rw [← source.imageHead_cons_imageTail, hhead]

private theorem returnBlocks_begin_head
    {rank : Nat} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank) :
    forall letter, [word.head] <+: decomposition.blocks letter := by
  intro letter
  obtain ⟨markerHead, markerTail, hmarker⟩ :=
    List.exists_cons_of_ne_nil decomposition.marker_ne_nil
  obtain ⟨blockHead, blockTail, hblock⟩ :=
    List.exists_cons_of_ne_nil
      (decomposition.blocks_are_returns letter).2.1
  have hmarkerHead : markerHead = word.head := by
    have hzero := decomposition.marker_at_zero
    rw [InfiniteFactorAt, Stream'.drop_zero, hmarker,
      List.length_cons, Stream'.take_succ] at hzero
    exact (List.cons.inj hzero).1.symm
  have hblockHead : blockHead = markerHead := by
    obtain ⟨tail, hprefix⟩ :=
      (decomposition.blocks_are_returns letter).2.2.2.1
    have hheads := congrArg List.head? hprefix
    simpa [hmarker, hblock] using hheads.symm
  rw [hblock, hblockHead, hmarkerHead]
  exact List.prefix_append _ _

/-- A nonconstant fixed word and a common first letter in every image force
unbounded growth of every image. -/
private theorem allLetterGrowth_of_fixed_nonconstant_beginHead
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {source : Substitution alpha} {word : InfiniteWord alpha}
    (hfixed : source.IsFixedPoint word)
    (hnonconstant : exists position, word position ≠ word.head)
    (hbegin : forall letter, [word.head] <+: source letter) :
    source.IsGrowing := by
  classical
  have hheadLength : 1 < (source word.head).length := by
    by_contra hnot
    have hpositive : 0 < (source word.head).length :=
      List.length_pos_of_ne_nil (source.image_ne_nil word.head)
    have hone : (source word.head).length = 1 := by omega
    have hheadImage : source word.head = [word.head] := by
      obtain ⟨tail, htail⟩ := hbegin word.head
      have htailLength := congrArg List.length htail
      simp only [List.length_singleton, List.length_append] at htailLength
      have : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [this] using htail.symm
    let firstDifferent := Nat.find hnonconstant
    have hfirstDifferent := Nat.find_spec hnonconstant
    have hbefore : ∀ position, position < firstDifferent →
        word position = word.head := by
      intro position hposition
      by_contra hne
      exact (Nat.find_min hnonconstant hposition) hne
    have hprefix : word.take firstDifferent =
        List.replicate firstDifferent word.head := by
      apply List.ext_getElem
      · simp
      · intro position hleft hright
        rw [Stream'.take_get (a := word) (m := position)
          (n := firstDifferent) (by simpa using hleft)]
        simp only [List.getElem_replicate]
        exact hbefore position (by simpa using hleft)
    have hmappedPrefix : source.mapWord (word.take firstDifferent) =
        word.take firstDifferent := by
      rw [hprefix]
      induction firstDifferent with
      | zero => simp
      | succ position ih =>
          simp [List.replicate_succ, hheadImage, ih]
    have hat := Substitution.mapWord_drop_take_at_fixed
      hfixed firstDifferent 1
    have htake : (word.drop firstDifferent).take 1 =
        [word firstDifferent] := by
      rw [Stream'.take_succ]
      simp [Stream'.get]
    rw [htake] at hat
    have hstart :
        (source.mapWord (word.take firstDifferent)).length =
          firstDifferent := by
      rw [hmappedPrefix]
      simp
    have himageAt : InfiniteFactorAt word
        (source (word firstDifferent)) firstDifferent := by
      rw [hstart] at hat
      simpa [Substitution.mapWord] using hat
    have hheadAt : word firstDifferent = word.head := by
      have hprefixImage := hbegin (word firstDifferent)
      have hfinite : FiniteFactorAt
          (source (word firstDifferent)) [word.head] 0 := by
        refine ⟨by simpa using hprefixImage.length_le, ?_⟩
        simpa using (List.prefix_iff_eq_take.mp hprefixImage).symm
      have hoccurs := himageAt.of_finiteFactorAt hfinite
      simpa [InfiniteFactorAt, Stream'.take_succ] using hoccurs
    exact hfirstDifferent hheadAt
  have hprolong : source.ProlongableOn word.head :=
    prolongableOn_head_of_fixedPoint_clusterD hfixed hheadLength
  have hheadGrow : forall bound, exists depth,
      bound ≤ (source.iterateLetter depth word.head).length := by
    intro bound
    exact ⟨bound,
      (Nat.le_succ bound).trans
        (succ_le_iterateLetter_length_clusterD source hprolong bound)⟩
  intro letter bound
  obtain ⟨depth, hdepth⟩ := hheadGrow bound
  refine ⟨depth + 1, hdepth.trans ?_⟩
  have hinfix := iterateWord_infix_clusterD source depth
    (hbegin letter).isInfix
  have hlength := hinfix.length_le
  have hcommute : source.iterateWord depth (source letter) =
      source.mapWord (source.iterateWord depth [letter]) := by
    calc
      source.iterateWord depth (source letter) =
          source.iterateWord depth (source.iterateWord 1 [letter]) := by
        simp [Substitution.iterateWord]
      _ = source.iterateWord (depth + 1) [letter] :=
        (iterateWord_add_clusterD source depth 1 [letter]).symm
      _ = source.iterateWord (1 + depth) [letter] := by
        rw [Nat.add_comm]
      _ = source.iterateWord 1
          (source.iterateWord depth [letter]) :=
        iterateWord_add_clusterD source 1 depth [letter]
      _ = source.mapWord (source.iterateWord depth [letter]) := by rfl
  rw [hcommute] at hlength
  simpa [Substitution.iterateLetter] using hlength

private theorem isFixedPoint_power_all_clusterD
    {alpha : Type*} {source : Substitution alpha}
    {word : InfiniteWord alpha}
    (hfixed : source.IsFixedPoint word) (level : Nat) :
    (source.power level).IsFixedPoint word := by
  cases level with
  | zero => exact Substitution.mapInfinite_id word
  | succ level =>
      exact Substitution.isFixedPoint_power hfixed (Nat.succ_pos level)

private theorem iterateWord_drop_take_at_fixed_clusterD
    {alpha : Type*} {source : Substitution alpha}
    {word : InfiniteWord alpha}
    (hfixed : source.IsFixedPoint word)
    (level start count : Nat) :
    InfiniteFactorAt word
      (source.iterateWord level ((word.drop start).take count))
      (source.iterateWord level (word.take start)).length := by
  have h := Substitution.mapWord_drop_take_at_fixed
    (isFixedPoint_power_all_clusterD hfixed level) start count
  simpa only [Substitution.power_mapWord] using h

private theorem FiniteFactorAt.isInfix_clusterD
    {alpha : Type*} {ambient factor : Word alpha} {start : Nat}
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

/-- The standard bounded-gap criterion: a uniformly recurrent fixed point
using every letter, together with growth of every image, makes the
substitution primitive. -/
private theorem primitive_of_fixed_uniform_all_images_grow
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    {source : Substitution alpha} {word : InfiniteWord alpha}
    (hfixed : source.IsFixedPoint word)
    (huniform : IsUniformlyRecurrent word)
    (hoccurs : forall letter : alpha,
      Substitution.OccursInInfiniteWord letter word)
    (hgrows : source.IsGrowing) :
    IsPrimitiveSubstitution source := by
  classical
  have hletterFactor : forall target : alpha,
      IsInfiniteFactor word [target] := by
    intro target
    obtain ⟨position, hposition⟩ := hoccurs target
    refine ⟨position, ?_⟩
    change (word.drop position).take 1 = [target]
    rw [Stream'.take_succ]
    simp [Stream'.get, hposition]
  have hbounded : forall target : alpha,
      AppearsWithBoundedGaps word [target] := by
    intro target
    exact huniform [target] (hletterFactor target)
  choose gap hgapPos hgap using hbounded
  let commonGap : Nat := Finset.univ.sup gap
  have hgapLe : forall target : alpha, gap target ≤ commonGap := by
    intro target
    exact Finset.le_sup (f := gap) (Finset.mem_univ target)
  have hlevelExists : forall sourceLetter : alpha, exists level : Nat,
      commonGap + 1 ≤
        (source.iterateLetter level sourceLetter).length := by
    intro sourceLetter
    exact hgrows sourceLetter (commonGap + 1)
  choose level hlevel using hlevelExists
  let commonLevel : Nat := Finset.univ.sup level
  have hlevelLe : forall sourceLetter : alpha,
      level sourceLetter ≤ commonLevel := by
    intro sourceLetter
    exact Finset.le_sup (f := level) (Finset.mem_univ sourceLetter)
  let iterate := commonLevel + 1
  refine ⟨iterate, by simp [iterate], ?_⟩
  intro sourceLetter targetLetter
  have himageLength : commonGap + 1 ≤
      (source.iterateLetter iterate sourceLetter).length := by
    obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le
      (hlevelLe sourceLetter)
    have hbase :
        (source.iterateLetter (level sourceLetter) sourceLetter).length ≤
          (source.iterateLetter commonLevel sourceLetter).length := by
      rw [hextra, Nat.add_comm]
      change (source.iterateWord (level sourceLetter) [sourceLetter]).length ≤
        (source.iterateWord (extra + level sourceLetter)
          [sourceLetter]).length
      rw [iterateWord_add_clusterD source]
      exact length_le_iterateWord_clusterD source extra
        (source.iterateWord (level sourceLetter) [sourceLetter])
    have hnext : (source.iterateLetter commonLevel sourceLetter).length ≤
        (source.iterateLetter iterate sourceLetter).length := by
      change (source.iterateWord commonLevel [sourceLetter]).length ≤
        (source.iterateWord (commonLevel + 1) [sourceLetter]).length
      rw [show commonLevel + 1 = 1 + commonLevel by omega,
        iterateWord_add_clusterD source]
      exact length_le_iterateWord_clusterD source 1
        (source.iterateWord commonLevel [sourceLetter])
    exact (hlevel sourceLetter).trans (hbase.trans hnext)
  obtain ⟨sourcePosition, hsourcePosition⟩ := hoccurs sourceLetter
  have htakeSource : (word.drop sourcePosition).take 1 = [sourceLetter] := by
    rw [Stream'.take_succ]
    simp [Stream'.get, hsourcePosition]
  have himageAt := iterateWord_drop_take_at_fixed_clusterD hfixed
    iterate sourcePosition 1
  rw [htakeSource] at himageAt
  change InfiniteFactorAt word
      (source.iterateLetter iterate sourceLetter)
      (source.iterateWord iterate (word.take sourcePosition)).length
    at himageAt
  let imageStart :=
    (source.iterateWord iterate (word.take sourcePosition)).length
  obtain ⟨offset, hoffset, htargetAt⟩ :=
    hgap targetLetter imageStart
  have hwithin : offset + [targetLetter].length ≤
      (source.iterateLetter iterate sourceLetter).length := by
    simp only [List.length_singleton]
    have : offset + 1 ≤ commonGap + 1 :=
      Nat.add_le_add_right (hoffset.trans (hgapLe targetLetter)) 1
    exact this.trans himageLength
  have htargetFinite : FiniteFactorAt
      (source.iterateLetter iterate sourceLetter) [targetLetter] offset :=
    finiteFactorAt_of_nested_infiniteFactorAt
      (by simpa [imageStart] using himageAt) htargetAt hwithin
  exact (List.singleton_infix_iff targetLetter _).mp
    (FiniteFactorAt.isInfix_clusterD htargetFinite)

/-- 1g: except for the tautological rank-one case, uniform recurrence and
aperiodicity make the self-return decoder primitive. -/
theorem selfReturnDecoder_primitive_or_rankOne
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (self : PairedFirstLetterSelfReturn systems) :
    systems.rank self.stage = 1 ∨
      IsPrimitiveSubstitution
        (returnDecoderSubstitutionMetric self.decomposition) := by
  classical
  by_cases hrank : systems.rank self.stage = 1
  · exact Or.inl hrank
  · right
    have hrankLarge : 1 < systems.rank self.stage := by
      have := systems.rank_pos self.stage
      omega
    letI : Nonempty (Fin (systems.rank self.stage)) :=
      ⟨⟨0, systems.rank_pos self.stage⟩⟩
    let decoder := returnDecoderSubstitutionMetric self.decomposition
    have hfixed : decoder.IsFixedPoint (systems.word self.stage) :=
      returnDecoder_fixed_derived self.decomposition self.derived_eq
    have hbegin : forall letter,
        [(systems.word self.stage).head] <+: decoder letter := by
      intro letter
      exact returnBlocks_begin_head self.decomposition letter
    obtain ⟨other, hother⟩ := Fintype.exists_ne_of_one_lt_card
      (by simpa using hrankLarge) (systems.word self.stage).head
    obtain ⟨position, hposition⟩ :=
      self.decomposition.every_letter_occurs other
    have hwordPosition : systems.word self.stage position = other := by
      rw [← self.derived_eq]
      exact hposition
    have hnonconstant : exists position,
        systems.word self.stage position ≠
          (systems.word self.stage).head :=
      ⟨position, by rw [hwordPosition]; exact hother⟩
    have hgrow : decoder.IsGrowing :=
      allLetterGrowth_of_fixed_nonconstant_beginHead
        hfixed hnonconstant hbegin
    exact primitive_of_fixed_uniform_all_images_grow hfixed
      (firstLetterStage_uniformlyRecurrent systems self.stage)
      (by
        intro letter
        rw [← self.derived_eq]
        exact self.decomposition.every_letter_occurs letter)
      hgrow

/-- A self-return iterate whose every decoder block contains every letter. -/
structure AllLetterPairedFirstLetterSelfReturn
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {self : PairedFirstLetterSelfReturn systems} where
  marker : Word (Fin (systems.rank self.stage))
  decomposition : ReturnDecomposition (systems.word self.stage) marker
    (systems.rank self.stage)
  derived_eq : decomposition.derived = systems.word self.stage
  left_decodes : forall letter,
    ((systems.leftSubstitution self.stage) letter).flatMap
        decomposition.blocks =
      (systems.leftSubstitution self.stage).mapWord
        (decomposition.blocks letter)
  right_decodes : forall letter,
    ((systems.rightSubstitution self.stage) letter).flatMap
        decomposition.blocks =
      (systems.rightSubstitution self.stage).mapWord
        (decomposition.blocks letter)
  contains_all : forall sourceLetter targetLetter,
    targetLetter ∈ decomposition.blocks sourceLetter

private theorem mapWord_flatMap_blocks
    {sourceAlphabet returnAlphabet : Type*}
    (source : Substitution sourceAlphabet)
    (induced : Substitution returnAlphabet)
    (blocks : returnAlphabet -> Word sourceAlphabet)
    (hletter : forall letter,
      (induced letter).flatMap blocks = source.mapWord (blocks letter)) :
    forall letters : Word returnAlphabet,
      (induced.mapWord letters).flatMap blocks =
        source.mapWord (letters.flatMap blocks) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      rw [Substitution.mapWord_cons, List.flatMap_append,
        hletter, List.flatMap_cons, Substitution.mapWord_append, ih]

/-- The `(level+1)`-fold composite of one literal self-return. -/
private structure IteratedPairedFirstLetterSelfReturn
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (self : PairedFirstLetterSelfReturn systems) (level : Nat) where
  marker : Word (Fin (systems.rank self.stage))
  decomposition : ReturnDecomposition (systems.word self.stage)
    marker (systems.rank self.stage)
  derived_eq : decomposition.derived = systems.word self.stage
  blocks_eq : forall letter,
    decomposition.blocks letter =
      ((returnDecoderSubstitutionMetric self.decomposition).power
        (level + 1)) letter
  left_decodes : forall letter,
    ((systems.leftSubstitution self.stage) letter).flatMap
        decomposition.blocks =
      (systems.leftSubstitution self.stage).mapWord
        (decomposition.blocks letter)
  right_decodes : forall letter,
    ((systems.rightSubstitution self.stage) letter).flatMap
        decomposition.blocks =
      (systems.rightSubstitution self.stage).mapWord
        (decomposition.blocks letter)

private def iteratedSelfReturn_zero
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (self : PairedFirstLetterSelfReturn systems) :
    IteratedPairedFirstLetterSelfReturn self 0 where
  marker := self.marker
  decomposition := self.decomposition
  derived_eq := self.derived_eq
  blocks_eq := by
    intro letter
    simp [returnDecoderSubstitutionMetric, Substitution.power_apply,
      Substitution.iterateLetter, Substitution.iterateWord]
  left_decodes := self.left_decodes
  right_decodes := self.right_decodes

private def iteratedSelfReturn_succ
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (self : PairedFirstLetterSelfReturn systems) (level : Nat)
    (current : IteratedPairedFirstLetterSelfReturn self level) :
    IteratedPairedFirstLetterSelfReturn self (level + 1) := by
  rcases current with
    ⟨currentMarker, currentDecomposition, currentDerivedEq,
      currentBlocksEq, currentLeftDecodes, currentRightDecodes⟩
  let inner := castReturnDecompositionWord self.derived_eq.symm
    currentDecomposition
  let composed := composeReturnDecompositions self.decomposition inner
  refine {
    marker := currentMarker.flatMap self.decomposition.blocks ++ self.marker
    decomposition := composed
    derived_eq := ?_
    blocks_eq := ?_
    left_decodes := ?_
    right_decodes := ?_ }
  · change inner.derived = systems.word self.stage
    rw [castReturnDecompositionWord_derived]
    exact currentDerivedEq
  · intro letter
    change (inner.blocks letter).flatMap self.decomposition.blocks = _
    rw [castReturnDecompositionWord_blocks, currentBlocksEq]
    change (returnDecoderSubstitutionMetric self.decomposition).mapWord
        (((returnDecoderSubstitutionMetric self.decomposition).power
          (level + 1)) letter) = _
    simp only [Substitution.power_apply,
      Substitution.iterateLetter_succ]
  · intro letter
    change ((systems.leftSubstitution self.stage) letter).flatMap
        (fun currentLetter =>
          (inner.blocks currentLetter).flatMap self.decomposition.blocks) = _
    rw [← List.flatMap_assoc]
    have hinnerBlocks : forall currentLetter,
        inner.blocks currentLetter =
          currentDecomposition.blocks currentLetter :=
      castReturnDecompositionWord_blocks self.derived_eq.symm
        currentDecomposition
    have hinnerBlocksFun : inner.blocks = currentDecomposition.blocks :=
      funext hinnerBlocks
    rw [hinnerBlocksFun, currentLeftDecodes]
    change _ = (systems.leftSubstitution self.stage).mapWord
      ((inner.blocks letter).flatMap self.decomposition.blocks)
    rw [hinnerBlocks]
    exact mapWord_flatMap_blocks
      (systems.leftSubstitution self.stage)
      (systems.leftSubstitution self.stage)
      self.decomposition.blocks self.left_decodes
      (currentDecomposition.blocks letter)
  · intro letter
    change ((systems.rightSubstitution self.stage) letter).flatMap
        (fun currentLetter =>
          (inner.blocks currentLetter).flatMap self.decomposition.blocks) = _
    rw [← List.flatMap_assoc]
    have hinnerBlocks : forall currentLetter,
        inner.blocks currentLetter =
          currentDecomposition.blocks currentLetter :=
      castReturnDecompositionWord_blocks self.derived_eq.symm
        currentDecomposition
    have hinnerBlocksFun : inner.blocks = currentDecomposition.blocks :=
      funext hinnerBlocks
    rw [hinnerBlocksFun, currentRightDecodes]
    change _ = (systems.rightSubstitution self.stage).mapWord
      ((inner.blocks letter).flatMap self.decomposition.blocks)
    rw [hinnerBlocks]
    exact mapWord_flatMap_blocks
      (systems.rightSubstitution self.stage)
      (systems.rightSubstitution self.stage)
      self.decomposition.blocks self.right_decodes
      (currentDecomposition.blocks letter)

private def iteratedSelfReturn
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (self : PairedFirstLetterSelfReturn systems) :
    forall level, IteratedPairedFirstLetterSelfReturn self level
  | 0 => iteratedSelfReturn_zero self
  | level + 1 => iteratedSelfReturn_succ self level
      (iteratedSelfReturn self level)

/-- 1h: iterate the self-return decoder to a common all-letter depth. -/
theorem selfReturn_has_allLetterIterate
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (self : PairedFirstLetterSelfReturn systems)
    (hdecoder : systems.rank self.stage = 1 ∨
      IsPrimitiveSubstitution
        (returnDecoderSubstitutionMetric self.decomposition)) :
    Nonempty (AllLetterPairedFirstLetterSelfReturn (self := self)) := by
  classical
  rcases hdecoder with hrank | hprimitive
  · refine ⟨{
      marker := self.marker
      decomposition := self.decomposition
      derived_eq := self.derived_eq
      left_decodes := self.left_decodes
      right_decodes := self.right_decodes
      contains_all := ?_ }⟩
    intro sourceLetter targetLetter
    obtain ⟨blockHead, blockTail, hblock⟩ :=
      List.exists_cons_of_ne_nil
        (self.decomposition.blocks_are_returns sourceLetter).2.1
    have htarget : targetLetter = blockHead := by
      apply Fin.eq_of_val_eq
      have htargetLt := targetLetter.isLt
      have hheadLt := blockHead.isLt
      omega
    rw [htarget, hblock]
    simp
  · obtain ⟨power, hpowerPos, hcontains⟩ := hprimitive
    let level := power - 1
    have hlevel : level + 1 = power := by
      dsimp [level]
      omega
    let iterated := iteratedSelfReturn self level
    rcases iterated with
      ⟨marker, decomposition, derivedEq, blocksEq, leftDecodes,
        rightDecodes⟩
    refine ⟨{
      marker := marker
      decomposition := decomposition
      derived_eq := derivedEq
      left_decodes := leftDecodes
      right_decodes := rightDecodes
      contains_all := ?_ }⟩
    intro sourceLetter targetLetter
    rw [blocksEq, hlevel]
    simpa [Substitution.power_apply] using
      hcontains sourceLetter targetLetter

/-- The all-letter self-return transported to a canonical base marker level. -/
structure CanonicalAllLetterSelfReturn
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    (self : PairedFirstLetterSelfReturn systems) where
  level : Nat
  relabel : Fin (systems.rank self.stage) ≃
    Fin (context.decompositions.rank level)
  word_relabels : forall position,
    relabel (systems.word self.stage position) =
      (context.decompositions.decomposition level).derived position
  left_relabels : forall letter,
    ((systems.leftSubstitution self.stage) letter).map relabel =
      (context.tower.left level).factorization.substitution (relabel letter)
  right_relabels : forall letter,
    ((systems.rightSubstitution self.stage) letter).map relabel =
      (context.tower.right level).factorization.substitution (relabel letter)
  marker : Word (Fin (context.decompositions.rank level))
  decomposition : ReturnDecomposition
    (context.decompositions.decomposition level).derived marker
    (context.decompositions.rank level)
  derived_eq : decomposition.derived =
    (context.decompositions.decomposition level).derived
  left_decodes : forall letter,
    ((context.tower.left level).factorization.substitution letter).flatMap
        decomposition.blocks =
      (context.tower.left level).factorization.substitution.mapWord
        (decomposition.blocks letter)
  right_decodes : forall letter,
    ((context.tower.right level).factorization.substitution letter).flatMap
        decomposition.blocks =
      (context.tower.right level).factorization.substitution.mapWord
        (decomposition.blocks letter)
  contains_all : forall sourceLetter targetLetter,
    targetLetter ∈ decomposition.blocks sourceLetter

private theorem finiteFactorAt_map_iff_m4i
    {α β : Type*} {coding : α → β} (hcoding : Function.Injective coding)
    {ambient factor : Word α} {start : Nat} :
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

private theorem IsReturnWord.map_injective_m4i
    {α β : Type*} (coding : α → β) (hcoding : Function.Injective coding)
    {word : InfiniteWord α} {marker block : Word α}
    (hreturn : IsReturnWord word marker block) :
    IsReturnWord (fun n => coding (word n))
      (marker.map coding) (block.map coding) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hnil
    apply hreturn.1
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa using this
  · intro hnil
    apply hreturn.2.1
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa using this
  · obtain ⟨start, hstart⟩ := hreturn.2.2.1
    refine ⟨start, ?_⟩
    simpa [List.map_append] using
      InfiniteFactorAt.map_m4 coding hstart
  · rcases hreturn.2.2.2.1 with ⟨tail, htail⟩
    refine ⟨tail.map coding, ?_⟩
    simpa [List.map_append] using congrArg (List.map coding) htail
  · intro start
    simpa [List.map_append] using
      (finiteFactorAt_map_iff_m4i (coding := coding) hcoding
        (ambient := block ++ marker) (factor := marker)
        (start := start)).trans (hreturn.2.2.2.2 start)

private def mapReturnDecompositionEquiv_m4i
    {α β : Type*} (relabel : α ≃ β)
    {word : InfiniteWord α} {marker : Word α} {rank : Nat}
    (decomposition : ReturnDecomposition word marker rank) :
    ReturnDecomposition (fun n => relabel (word n))
      (marker.map relabel) rank where
  rank_pos := decomposition.rank_pos
  marker_ne_nil := by
    intro hnil
    apply decomposition.marker_ne_nil
    apply List.eq_nil_of_length_eq_zero
    have := congrArg List.length hnil
    simpa using this
  marker_at_zero := InfiniteFactorAt.map_m4 relabel
    decomposition.marker_at_zero
  blocks := fun letter => (decomposition.blocks letter).map relabel
  blocks_injective := by
    intro left right heq
    apply decomposition.blocks_injective
    exact (List.map_injective_iff.mpr relabel.injective) heq
  blocks_are_returns := fun letter =>
    IsReturnWord.map_injective_m4i relabel relabel.injective
      (decomposition.blocks_are_returns letter)
  every_return_is_block := by
    intro returnWord hreturn
    let pulled := returnWord.map relabel.symm
    have hpulled : IsReturnWord word marker pulled := by
      have hmapped := IsReturnWord.map_injective_m4i relabel.symm
        relabel.symm.injective hreturn
      simpa [pulled, List.map_map] using hmapped
    obtain ⟨letter, hletter⟩ :=
      decomposition.every_return_is_block pulled hpulled
    refine ⟨letter, ?_⟩
    have hmapped := congrArg (List.map relabel) hletter
    simpa [pulled, List.map_map] using hmapped
  derived := decomposition.derived
  cut := decomposition.cut
  cut_zero := decomposition.cut_zero
  cut_succ := by
    intro position
    simpa using decomposition.cut_succ position
  block_at_cut := fun position =>
    InfiniteFactorAt.map_m4 relabel (decomposition.block_at_cut position)

private def reindexReturnDecomposition_m4i
    {α : Type*} {word : InfiniteWord α} {marker : Word α}
    {leftRank rightRank : Nat} (relabel : Fin leftRank ≃ Fin rightRank)
    (decomposition : ReturnDecomposition word marker leftRank) :
    ReturnDecomposition word marker rightRank where
  rank_pos := by
    have witness := relabel ⟨0, decomposition.rank_pos⟩
    exact Nat.zero_lt_of_lt witness.isLt
  marker_ne_nil := decomposition.marker_ne_nil
  marker_at_zero := decomposition.marker_at_zero
  blocks := fun letter => decomposition.blocks (relabel.symm letter)
  blocks_injective := by
    intro left right heq
    apply relabel.symm.injective
    exact decomposition.blocks_injective heq
  blocks_are_returns := fun letter =>
    decomposition.blocks_are_returns (relabel.symm letter)
  every_return_is_block := by
    intro returnWord hreturn
    obtain ⟨letter, hletter⟩ :=
      decomposition.every_return_is_block returnWord hreturn
    exact ⟨relabel letter, by simpa using hletter⟩
  derived := fun position => relabel (decomposition.derived position)
  cut := decomposition.cut
  cut_zero := decomposition.cut_zero
  cut_succ := by intro position; simpa using decomposition.cut_succ position
  block_at_cut := by intro position; simpa using decomposition.block_at_cut position

@[simp] private theorem reindexReturnDecomposition_blocks_m4i
    {α : Type*} {word : InfiniteWord α} {marker : Word α}
    {leftRank rightRank : Nat} (relabel : Fin leftRank ≃ Fin rightRank)
    (decomposition : ReturnDecomposition word marker leftRank)
    (letter : Fin rightRank) :
    (reindexReturnDecomposition_m4i relabel decomposition).blocks letter =
      decomposition.blocks (relabel.symm letter) := rfl

@[simp] private theorem reindexReturnDecomposition_derived_m4i
    {α : Type*} {word : InfiniteWord α} {marker : Word α}
    {leftRank rightRank : Nat} (relabel : Fin leftRank ≃ Fin rightRank)
    (decomposition : ReturnDecomposition word marker leftRank)
    (position : Nat) :
    (reindexReturnDecomposition_m4i relabel decomposition).derived position =
      relabel (decomposition.derived position) := rfl

private theorem mapWord_relabels_m4i
    {α β : Type*} {left : Substitution α} {right : Substitution β}
    (relabel : α ≃ β)
    (hletter : ∀ letter, (left letter).map relabel =
      right (relabel letter)) :
    ∀ letters : Word α,
      (left.mapWord letters).map relabel =
        right.mapWord (letters.map relabel) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.map_cons]
      rw [Substitution.mapWord_cons, Substitution.mapWord_cons,
        List.map_append, hletter, ih]

private theorem flatMap_relabels_blocks_m4i
    {α β γ δ : Type*} (sourceRelabel : α → β)
    (returnRelabel : γ → δ) (leftBlocks : γ → Word α)
    (rightBlocks : δ → Word β)
    (hblocks : ∀ letter,
      rightBlocks (returnRelabel letter) =
        (leftBlocks letter).map sourceRelabel) :
    ∀ letters : Word γ,
      (letters.map returnRelabel).flatMap rightBlocks =
        (letters.flatMap leftBlocks).map sourceRelabel := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [hblocks, ih]

/-- 1i: transport the all-letter self-return through its canonical base
realization. -/
theorem allLetterSelfReturn_has_canonicalBaseRealization
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {self : PairedFirstLetterSelfReturn systems}
    (realization : FirstLetterCanonicalBaseRealization systems self.stage)
    (all : AllLetterPairedFirstLetterSelfReturn (self := self)) :
    Nonempty (CanonicalAllLetterSelfReturn (self := self)) := by
  classical
  have hword : (fun position =>
      realization.relabel (systems.word self.stage position)) =
      (context.decompositions.decomposition realization.level).derived := by
    funext position
    exact realization.word_relabels position
  let mapped := mapReturnDecompositionEquiv_m4i realization.relabel
    (AllLetterPairedFirstLetterSelfReturn.decomposition
      (self := self) all)
  let casted := castReturnDecompositionWord hword mapped
  let decomposition := reindexReturnDecomposition_m4i
    realization.relabel casted
  have hblocks : ∀ letter,
      decomposition.blocks (realization.relabel letter) =
        ((AllLetterPairedFirstLetterSelfReturn.decomposition
          (self := self) all).blocks letter).map realization.relabel := by
    intro letter
    simp [decomposition, casted, mapped,
      mapReturnDecompositionEquiv_m4i]
  have hderived : decomposition.derived =
      (context.decompositions.decomposition realization.level).derived := by
    funext position
    rw [reindexReturnDecomposition_derived_m4i,
      castReturnDecompositionWord_derived]
    change realization.relabel
      ((AllLetterPairedFirstLetterSelfReturn.decomposition
        (self := self) all).derived position) = _
    rw [AllLetterPairedFirstLetterSelfReturn.derived_eq
      (self := self) all, realization.word_relabels]
  refine ⟨{
    level := realization.level
    relabel := realization.relabel
    word_relabels := realization.word_relabels
    left_relabels := realization.left_relabels
    right_relabels := realization.right_relabels
    marker := (AllLetterPairedFirstLetterSelfReturn.marker
      (self := self) all).map realization.relabel
    decomposition := decomposition
    derived_eq := hderived
    left_decodes := ?_
    right_decodes := ?_
    contains_all := ?_ }⟩
  · intro letter
    let oldLetter := realization.relabel.symm letter
    have hletter : realization.relabel oldLetter = letter :=
      realization.relabel.apply_symm_apply letter
    rw [← hletter]
    calc
      ((context.tower.left realization.level).factorization.substitution
          (realization.relabel oldLetter)).flatMap decomposition.blocks =
          ((systems.leftSubstitution self.stage oldLetter).map
            realization.relabel).flatMap decomposition.blocks := by
        rw [realization.left_relabels]
      _ = ((systems.leftSubstitution self.stage oldLetter).flatMap
            (AllLetterPairedFirstLetterSelfReturn.decomposition
              (self := self) all).blocks).map realization.relabel :=
        flatMap_relabels_blocks_m4i realization.relabel
          realization.relabel
          (AllLetterPairedFirstLetterSelfReturn.decomposition
            (self := self) all).blocks decomposition.blocks hblocks _
      _ = ((systems.leftSubstitution self.stage).mapWord
            ((AllLetterPairedFirstLetterSelfReturn.decomposition
              (self := self) all).blocks oldLetter)).map
              realization.relabel := by
        rw [AllLetterPairedFirstLetterSelfReturn.left_decodes
          (self := self) all]
      _ = (context.tower.left
            realization.level).factorization.substitution.mapWord
            (((AllLetterPairedFirstLetterSelfReturn.decomposition
              (self := self) all).blocks oldLetter).map
                realization.relabel) :=
        mapWord_relabels_m4i realization.relabel
          realization.left_relabels _
      _ = (context.tower.left
            realization.level).factorization.substitution.mapWord
            (decomposition.blocks (realization.relabel oldLetter)) := by
        rw [hblocks]
  · intro letter
    let oldLetter := realization.relabel.symm letter
    have hletter : realization.relabel oldLetter = letter :=
      realization.relabel.apply_symm_apply letter
    rw [← hletter]
    calc
      ((context.tower.right realization.level).factorization.substitution
          (realization.relabel oldLetter)).flatMap decomposition.blocks =
          ((systems.rightSubstitution self.stage oldLetter).map
            realization.relabel).flatMap decomposition.blocks := by
        rw [realization.right_relabels]
      _ = ((systems.rightSubstitution self.stage oldLetter).flatMap
            (AllLetterPairedFirstLetterSelfReturn.decomposition
              (self := self) all).blocks).map realization.relabel :=
        flatMap_relabels_blocks_m4i realization.relabel
          realization.relabel
          (AllLetterPairedFirstLetterSelfReturn.decomposition
            (self := self) all).blocks decomposition.blocks hblocks _
      _ = ((systems.rightSubstitution self.stage).mapWord
            ((AllLetterPairedFirstLetterSelfReturn.decomposition
              (self := self) all).blocks oldLetter)).map
              realization.relabel := by
        rw [AllLetterPairedFirstLetterSelfReturn.right_decodes
          (self := self) all]
      _ = (context.tower.right
            realization.level).factorization.substitution.mapWord
            (((AllLetterPairedFirstLetterSelfReturn.decomposition
              (self := self) all).blocks oldLetter).map
                realization.relabel) :=
        mapWord_relabels_m4i realization.relabel
          realization.right_relabels _
      _ = (context.tower.right
            realization.level).factorization.substitution.mapWord
            (decomposition.blocks (realization.relabel oldLetter)) := by
        rw [hblocks]
  · intro sourceLetter targetLetter
    rw [← realization.relabel.apply_symm_apply sourceLetter, hblocks]
    exact List.mem_map.mpr
      ⟨realization.relabel.symm targetLetter,
        AllLetterPairedFirstLetterSelfReturn.contains_all
          (self := self) all _ _,
        realization.relabel.apply_symm_apply _⟩

/-- A common positive power of both selected local sources satisfying every
source-side field of the two Proposition-10 inputs. -/
structure CanonicalCommonSourcePower
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {self : PairedFirstLetterSelfReturn systems}
    (canonical : CanonicalAllLetterSelfReturn (self := self)) where
  commonPower : Nat
  commonPower_pos : 0 < commonPower
  seed : Fin (context.decompositions.rank
    (CanonicalAllLetterSelfReturn.level (self := self) canonical))
  seed_is_head : seed =
    (context.decompositions.decomposition
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).derived.head
  leftInduced : PrefixReturnFactorization
    ((context.tower.left
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower)
      (CanonicalAllLetterSelfReturn.decomposition (self := self) canonical)
  rightInduced : PrefixReturnFactorization
    ((context.tower.right
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower)
      (CanonicalAllLetterSelfReturn.decomposition (self := self) canonical)
  left_induced_eq : leftInduced.substitution =
    (context.tower.left
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower
  right_induced_eq : rightInduced.substitution =
    (context.tower.right
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower
  left_power_fixed :
    ((context.tower.left
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower).IsFixedPoint
      (context.decompositions.decomposition
        (CanonicalAllLetterSelfReturn.level (self := self) canonical)).derived
  right_power_fixed :
    ((context.tower.right
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower).IsFixedPoint
      (context.decompositions.decomposition
        (CanonicalAllLetterSelfReturn.level (self := self) canonical)).derived
  left_power_primitive : IsPrimitiveSubstitution
    ((context.tower.left
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower)
  right_power_primitive : IsPrimitiveSubstitution
    ((context.tower.right
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower)
  left_power_prolongable :
    ((context.tower.left
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower).ProlongableOn seed
  right_power_prolongable :
    ((context.tower.right
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
        commonPower).ProlongableOn seed
  left_images_begin_seed : forall letter,
    [seed] <+:
      ((context.tower.left
        (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
          commonPower) letter
  right_images_begin_seed : forall letter,
    [seed] <+:
      ((context.tower.right
        (CanonicalAllLetterSelfReturn.level (self := self) canonical)).factorization.substitution.power
          commonPower) letter

private theorem growing_of_exact_positive_metric_m4j
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (source : Substitution α) (metric : α → Real) (scale : Real)
    (hmetric : ∀ letter, 0 < metric letter)
    (hscales : SubstitutionScalesLetterLengths source metric scale)
    (hone : 1 < scale) : source.IsGrowing := by
  intro letter bound
  let total : Real := ∑ other : α, metric other
  have hletterLe : metric letter ≤ total := by
    dsimp [total]
    exact Finset.single_le_sum (fun other _ => (hmetric other).le)
      (Finset.mem_univ letter)
  have htotalPos : 0 < total := (hmetric letter).trans_le hletterLe
  have hiterateMetric (n : Nat) :
      wordMetricLength metric (source.iterateLetter n letter) =
        scale ^ n * metric letter := by
    have hpower := scalesLetterLengths_power hscales n letter
    simpa [Substitution.power_apply] using hpower
  have heventually : ∀ᶠ n : Nat in Filter.atTop,
      ((bound : Real) * total) / metric letter < scale ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hone).eventually_gt_atTop _
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.1 heventually
  have hlarge := hthreshold threshold le_rfl
  refine ⟨threshold, le_of_not_gt fun htooShort => ?_⟩
  have htooShortReal :
      ((source.iterateLetter threshold letter).length : Real) < bound := by
    exact_mod_cast htooShort
  have hmetricUpperAll (letters : Word α) :
      wordMetricLength metric letters ≤ (letters.length : Real) * total := by
    induction letters with
    | nil => simp [wordMetricLength]
    | cons head tail ih =>
        change (List.map metric tail).sum ≤
          (tail.length : Real) * total at ih
        have hheadLe : metric head ≤ total := by
          dsimp [total]
          exact Finset.single_le_sum (fun other _ => (hmetric other).le)
            (Finset.mem_univ head)
        have htotalNonneg : 0 ≤ total := htotalPos.le
        simp only [wordMetricLength, List.map_cons, List.sum_cons,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith
  have hmetricUpper := hmetricUpperAll
    (source.iterateLetter threshold letter)
  rw [hiterateMetric] at hmetricUpper
  have hlarge' : (bound : Real) * total <
      scale ^ threshold * metric letter :=
    (div_lt_iff₀ (hmetric letter)).mp hlarge
  have htooShortProduct :
      ((source.iterateLetter threshold letter).length : Real) * total <
        (bound : Real) * total :=
    mul_lt_mul_of_pos_right htooShortReal htotalPos
  nlinarith

private theorem iterateLetter_prefix_of_le_m4j
    {α : Type*} {source : Substitution α} {seed : α}
    (hprolongable : source.ProlongableOn seed)
    {earlier later : Nat} (hle : earlier ≤ later) :
    source.iterateLetter earlier seed <+:
      source.iterateLetter later seed := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction extra with
  | zero => simp
  | succ extra ih =>
      simpa [Nat.add_assoc] using ih.trans
        (source.iterateLetter_prefix_succ hprolongable (earlier + extra))

private theorem mapWord_id_m4j
    {α : Type*} (letters : Word α) :
    (Substitution.id : Substitution α).mapWord letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih => simp [ih]

private theorem mapWord_comp_m4j
    {α : Type*} (left right : Substitution α) (letters : Word α) :
    (left.comp right).mapWord letters =
      left.mapWord (right.mapWord letters) := by
  induction letters with
  | nil => rfl
  | cons letter rest ih => simp [ih]

private theorem power_mapWord_m4j
    {α : Type*} (source : Substitution α) :
    ∀ power letters,
      (source.power power).mapWord letters = source.iterateWord power letters
  | 0, letters => mapWord_id_m4j letters
  | power + 1, letters => by
      rw [Substitution.power_succ, mapWord_comp_m4j, power_mapWord_m4j]
      rfl

private theorem mapWord_flatMap_blocks_m4j
    {α β : Type*} (source : Substitution α)
    (induced : Substitution β) (blocks : β → Word α)
    (hletter : ∀ letter,
      (induced letter).flatMap blocks = source.mapWord (blocks letter)) :
    ∀ letters : Word β,
      (induced.mapWord letters).flatMap blocks =
        source.mapWord (letters.flatMap blocks) := by
  intro letters
  induction letters with
  | nil => simp
  | cons letter rest ih =>
      rw [Substitution.mapWord_cons, List.flatMap_append,
        hletter, List.flatMap_cons, Substitution.mapWord_append, ih]

private theorem substitution_ext_m4j
    {α : Type*} (left right : Substitution α)
    (himages : ∀ letter, left letter = right letter) : left = right := by
  cases left with
  | mk leftImage leftNonempty =>
      cases right with
      | mk rightImage rightNonempty =>
          have himage : leftImage = rightImage := funext himages
          subst rightImage
          rfl

private theorem decodingEquation_power_m4j
    {α : Type*} (source : Substitution α) (blocks : α → Word α)
    (hdecode : ∀ letter,
      (source letter).flatMap blocks = source.mapWord (blocks letter)) :
    ∀ power letter,
      ((source.power power) letter).flatMap blocks =
        (source.power power).mapWord (blocks letter) := by
  intro power letter
  rw [Substitution.power_apply, power_mapWord_m4j]
  induction power with
  | zero =>
      simp [Substitution.iterateLetter, Substitution.iterateWord]
  | succ power ih =>
      change (source.mapWord
          (source.iterateLetter power letter)).flatMap blocks =
        source.mapWord (source.iterateWord power (blocks letter))
      rw [mapWord_flatMap_blocks_m4j source source blocks hdecode, ih]

private theorem returnBlocks_begin_head_m4j
    {rank : Nat} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank) :
    ∀ letter, [word.head] <+: decomposition.blocks letter := by
  intro letter
  obtain ⟨markerHead, markerTail, hmarker⟩ :=
    List.exists_cons_of_ne_nil decomposition.marker_ne_nil
  obtain ⟨blockHead, blockTail, hblock⟩ :=
    List.exists_cons_of_ne_nil
      (decomposition.blocks_are_returns letter).2.1
  have hmarkerHead : markerHead = word.head := by
    have hzero := decomposition.marker_at_zero
    rw [InfiniteFactorAt, Stream'.drop_zero, hmarker,
      List.length_cons, Stream'.take_succ] at hzero
    exact (List.cons.inj hzero).1.symm
  have hblockHead : blockHead = markerHead := by
    obtain ⟨tail, hprefix⟩ :=
      (decomposition.blocks_are_returns letter).2.2.2.1
    have hheads := congrArg List.head? hprefix
    simpa [hmarker, hblock] using hheads.symm
  rw [hblock, hblockHead, hmarkerHead]
  exact List.prefix_append _ _

private structure SelfReturnSourcePowerM4J
    {rank : Nat} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank)
    (source : Substitution (Fin rank)) (power : Nat) where
  induced : PrefixReturnFactorization (source.power power) decomposition
  induced_eq : induced.substitution = source.power power
  images_begin_head : ∀ letter, [word.head] <+: (source.power power) letter

private theorem selfReturn_has_sourcePower_m4j
    {rank : Nat} {word : InfiniteWord (Fin rank)}
    {marker : Word (Fin rank)}
    (decomposition : ReturnDecomposition word marker rank)
    (hderived : decomposition.derived = word)
    (source : Substitution (Fin rank))
    (hfixed : source.IsFixedPoint word)
    (hdecode : ∀ letter,
      (source letter).flatMap decomposition.blocks =
        source.mapWord (decomposition.blocks letter))
    {power : Nat} (hpower : 0 < power)
    (hlong : (decomposition.blocks word.head ++ marker).length ≤
      (source.iterateLetter power word.head).length) :
    Nonempty (SelfReturnSourcePowerM4J decomposition source power) := by
  classical
  have hdecodePower := decodingEquation_power_m4j source
    decomposition.blocks hdecode
  have hpowerFixed : (source.power power).IsFixedPoint word :=
    Substitution.isFixedPoint_power hfixed hpower
  obtain ⟨factorization⟩ :=
    prefixReturnFactorization_exists hpowerFixed decomposition
  have hinduced : factorization.substitution = source.power power := by
    apply substitution_ext_m4j
    intro letter
    exact (factorization.factor_unique letter _
      (hdecodePower power letter)).symm
  have hblockMarkerAtZero := decomposition.block_marker_at_cut 0
  rw [decomposition.cut_zero, hderived] at hblockMarkerAtZero
  change InfiniteFactorAt word
      (decomposition.blocks word.head ++ marker) 0 at hblockMarkerAtZero
  have hblockMarkerTake :
      word.take (decomposition.blocks word.head ++ marker).length =
        decomposition.blocks word.head ++ marker := by
    simpa [InfiniteFactorAt] using hblockMarkerAtZero
  have hseedIterateTake := iterateLetter_eq_fixedPoint_prefix hfixed power
  have hblockMarkerSeedPrefix :
      decomposition.blocks word.head ++ marker <+:
        source.iterateLetter power word.head := by
    have htakes := Stream'.take_prefix_take_left
      (a := word)
      (m := (decomposition.blocks word.head ++ marker).length)
      (n := (source.iterateLetter power word.head).length) hlong
    rw [hblockMarkerTake, ← hseedIterateTake] at htakes
    exact htakes
  have hblockMarkerImagePrefix : ∀ letter,
      decomposition.blocks word.head ++ marker <+:
        (source.power power).mapWord (decomposition.blocks letter) := by
    intro letter
    have hblockBegins : [word.head] <+:
        decomposition.blocks letter :=
      returnBlocks_begin_head_m4j decomposition letter
    have himage := Substitution.mapWord_prefix
      (σ := source.power power) hblockBegins
    have hseedPrefix : source.iterateLetter power word.head <+:
        (source.power power).mapWord (decomposition.blocks letter) := by
      simpa [Substitution.power_apply] using himage
    exact hblockMarkerSeedPrefix.trans hseedPrefix
  refine ⟨{
    induced := factorization
    induced_eq := hinduced
    images_begin_head := ?_ }⟩
  intro letter
  obtain ⟨position, hposition⟩ :=
    decomposition.every_letter_occurs letter
  have hfactorAt := factorization.derived_factor_at position
  change InfiniteFactorAt decomposition.derived
      (factorization.substitution (decomposition.derived position))
      (factorization.boundary position) at hfactorAt
  rw [hposition, hinduced] at hfactorAt
  have htaken :
      (decomposition.derived.drop
        (factorization.boundary position)).take
          ((source.power power) letter).length =
        (source.power power) letter := by
    simpa [InfiniteFactorAt] using hfactorAt
  have hdecoded := decodedMarkerAtCut decomposition
    (factorization.boundary position) ((source.power power) letter).length
  rw [htaken] at hdecoded
  have hdecodedPrefix : decomposition.blocks word.head ++ marker <+:
      ((source.power power) letter).flatMap decomposition.blocks := by
    rw [hdecodePower power letter]
    exact hblockMarkerImagePrefix letter
  have hfullPrefix : decomposition.blocks word.head ++ marker <+:
      ((source.power power) letter).flatMap decomposition.blocks ++ marker :=
    hdecodedPrefix.trans (List.prefix_append _ _)
  have hfinite : FiniteFactorAt
      (((source.power power) letter).flatMap decomposition.blocks ++ marker)
      (decomposition.blocks word.head ++ marker) 0 := by
    refine ⟨by simpa using hfullPrefix.length_le, ?_⟩
    simpa using (List.prefix_iff_eq_take.mp hfullPrefix).symm
  have hblockAt := hdecoded.of_finiteFactorAt hfinite
  have hblockEq := decomposition.block_eq_of_block_marker_at_cut
    word.head (factorization.boundary position) hblockAt
  have hseedAtBoundary : word.head =
      decomposition.derived (factorization.boundary position) :=
    decomposition.blocks_injective hblockEq
  obtain ⟨imageHead, imageTail, himage⟩ :=
    List.exists_cons_of_ne_nil ((source.power power).image_ne_nil letter)
  have hfactorHead :
      decomposition.derived (factorization.boundary position) = imageHead := by
    rw [InfiniteFactorAt, himage, List.length_cons,
      Stream'.take_succ] at hfactorAt
    simpa [Stream'.head_drop, Stream'.get] using
      (List.cons.inj hfactorAt).1
  have hseedHead : word.head = imageHead :=
    hseedAtBoundary.trans hfactorHead
  rw [himage, hseedHead]
  simp

/-- 1j: choose one common depth making both local sources primitive,
prolongable, seed-prefixed, and literally induced on the self-return. -/
theorem canonicalAllLetterSelfReturn_has_commonSourcePower
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {self : PairedFirstLetterSelfReturn systems}
    (canonical : CanonicalAllLetterSelfReturn (self := self)) :
    Nonempty (CanonicalCommonSourcePower canonical) := by
  classical
  let level := CanonicalAllLetterSelfReturn.level (self := self) canonical
  let baseDecomposition := context.decompositions.decomposition level
  let selectedWord := baseDecomposition.derived
  let selectedRank := context.decompositions.rank level
  let selectedSeed := selectedWord.head
  let canonicalRelabel :=
    CanonicalAllLetterSelfReturn.relabel (self := self) canonical
  let leftLocal := (context.tower.left level).factorization.substitution
  let rightLocal := (context.tower.right level).factorization.substitution
  letI : Nonempty (Fin selectedRank) := ⟨selectedSeed⟩
  have hleftFixed : leftLocal.IsFixedPoint selectedWord :=
    (context.tower.left level).fixed
  have hrightFixed : rightLocal.IsFixedPoint selectedWord :=
    (context.tower.right level).fixed
  have hleftScale :
      1 < (leftScale ^ synchronized.leftPower) ^
        context.tower.leftLocalPower :=
    one_lt_pow₀ synchronized.left_presentation.one_lt_eigenvalue
      (Nat.ne_of_gt context.tower.leftLocalPower_pos)
  have hrightScale :
      1 < (rightScale ^ synchronized.rightPower) ^
        context.tower.rightLocalPower :=
    one_lt_pow₀ synchronized.right_presentation.one_lt_eigenvalue
      (Nat.ne_of_gt context.tower.rightLocalPower_pos)
  have hleftGrow : leftLocal.IsGrowing :=
    growing_of_exact_positive_metric_m4j leftLocal
      (context.tower.left level).returnLength
      ((leftScale ^ synchronized.leftPower) ^
        context.tower.leftLocalPower)
      (context.tower.left level).returnLength_pos
      (context.tower.left level).scales hleftScale
  have hrightGrow : rightLocal.IsGrowing :=
    growing_of_exact_positive_metric_m4j rightLocal
      (context.tower.right level).returnLength
      ((rightScale ^ synchronized.rightPower) ^
        context.tower.rightLocalPower)
      (context.tower.right level).returnLength_pos
      (context.tower.right level).scales hrightScale
  have hleftProlongable : leftLocal.ProlongableOn selectedSeed := by
    exact prolongableOn_head_of_growing_fixedPoint hleftFixed hleftGrow
  have hrightProlongable : rightLocal.ProlongableOn selectedSeed := by
    exact prolongableOn_head_of_growing_fixedPoint hrightFixed hrightGrow
  let selfDecomposition :=
    CanonicalAllLetterSelfReturn.decomposition (self := self) canonical
  let selfMarker := CanonicalAllLetterSelfReturn.marker
    (self := self) canonical
  let coverLength :=
    (selfDecomposition.blocks selectedSeed ++ selfMarker).length
  have hcoverLarge : 1 < coverLength := by
    have hblock := selfDecomposition.block_length_pos selectedSeed
    have hmarker : 0 < selfMarker.length := by
      change 0 < (CanonicalAllLetterSelfReturn.marker
        (self := self) canonical).length
      exact List.length_pos_of_ne_nil selfDecomposition.marker_ne_nil
    dsimp only [coverLength]
    rw [List.length_append]
    omega
  obtain ⟨leftDepth, hleftDepth⟩ :=
    hleftGrow selectedSeed coverLength
  obtain ⟨rightDepth, hrightDepth⟩ :=
    hrightGrow selectedSeed coverLength
  have hleftDepthPos : 0 < leftDepth := by
    by_contra hnot
    have hzero : leftDepth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hleftDepth
    simp [Substitution.iterateLetter] at hleftDepth
    omega
  have hrightDepthPos : 0 < rightDepth := by
    by_contra hnot
    have hzero : rightDepth = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hrightDepth
    simp [Substitution.iterateLetter] at hrightDepth
    omega
  let commonPower := max leftDepth rightDepth
  have hcommonPowerPos : 0 < commonPower := by
    dsimp [commonPower]
    omega
  have hleftLong : coverLength ≤
      (leftLocal.iterateLetter commonPower selectedSeed).length :=
    hleftDepth.trans
      (iterateLetter_prefix_of_le_m4j hleftProlongable
        (Nat.le_max_left leftDepth rightDepth)).length_le
  have hrightLong : coverLength ≤
      (rightLocal.iterateLetter commonPower selectedSeed).length :=
    hrightDepth.trans
      (iterateLetter_prefix_of_le_m4j hrightProlongable
        (Nat.le_max_right leftDepth rightDepth)).length_le
  obtain ⟨leftPowered⟩ := selfReturn_has_sourcePower_m4j
    selfDecomposition
    (CanonicalAllLetterSelfReturn.derived_eq (self := self) canonical)
    leftLocal hleftFixed
    (CanonicalAllLetterSelfReturn.left_decodes (self := self) canonical)
    hcommonPowerPos hleftLong
  obtain ⟨rightPowered⟩ := selfReturn_has_sourcePower_m4j
    selfDecomposition
    (CanonicalAllLetterSelfReturn.derived_eq (self := self) canonical)
    rightLocal hrightFixed
    (CanonicalAllLetterSelfReturn.right_decodes (self := self) canonical)
    hcommonPowerPos hrightLong
  have hleftRelabel :
      (systems.leftSubstitution self.stage).relabelEquiv canonicalRelabel =
        leftLocal := by
    apply substitution_ext_m4j
    intro letter
    change ((systems.leftSubstitution self.stage)
      (canonicalRelabel.symm letter)).map canonicalRelabel = leftLocal letter
    simpa [Substitution.relabelEquiv, canonicalRelabel, leftLocal, level] using
      (CanonicalAllLetterSelfReturn.left_relabels (self := self) canonical
        (canonicalRelabel.symm letter))
  have hrightRelabel :
      (systems.rightSubstitution self.stage).relabelEquiv canonicalRelabel =
        rightLocal := by
    apply substitution_ext_m4j
    intro letter
    change ((systems.rightSubstitution self.stage)
      (canonicalRelabel.symm letter)).map canonicalRelabel = rightLocal letter
    simpa [Substitution.relabelEquiv, canonicalRelabel, rightLocal, level] using
      (CanonicalAllLetterSelfReturn.right_relabels (self := self) canonical
        (canonicalRelabel.symm letter))
  have hleftPrimitive : IsPrimitiveSubstitution leftLocal := by
    change PrimitiveCore.IsPrimitiveSubstitution leftLocal
    rw [← hleftRelabel]
    exact PrimitiveCore.IsPrimitiveSubstitution.relabelEquiv canonicalRelabel
      (systems.leftPrimitive self.stage)
  have hrightPrimitive : IsPrimitiveSubstitution rightLocal := by
    change PrimitiveCore.IsPrimitiveSubstitution rightLocal
    rw [← hrightRelabel]
    exact PrimitiveCore.IsPrimitiveSubstitution.relabelEquiv canonicalRelabel
      (systems.rightPrimitive self.stage)
  have hleftPowerPrimitive :
      IsPrimitiveSubstitution (leftLocal.power commonPower) := by
    change PrimitiveCore.IsPrimitiveSubstitution
      (leftLocal.power commonPower)
    exact (show PrimitiveCore.IsPrimitiveSubstitution leftLocal from
      hleftPrimitive).power hcommonPowerPos
  have hrightPowerPrimitive :
      IsPrimitiveSubstitution (rightLocal.power commonPower) := by
    change PrimitiveCore.IsPrimitiveSubstitution
      (rightLocal.power commonPower)
    exact (show PrimitiveCore.IsPrimitiveSubstitution rightLocal from
      hrightPrimitive).power hcommonPowerPos
  have hleftPowerFixed :
      (leftLocal.power commonPower).IsFixedPoint selectedWord :=
    Substitution.isFixedPoint_power hleftFixed hcommonPowerPos
  have hrightPowerFixed :
      (rightLocal.power commonPower).IsFixedPoint selectedWord :=
    Substitution.isFixedPoint_power hrightFixed hcommonPowerPos
  have hleftPowerProlongable :
      (leftLocal.power commonPower).ProlongableOn selectedSeed := by
    exact prolongableOn_head_of_growing_fixedPoint hleftPowerFixed
      (hleftGrow.power hcommonPowerPos)
  have hrightPowerProlongable :
      (rightLocal.power commonPower).ProlongableOn selectedSeed := by
    exact prolongableOn_head_of_growing_fixedPoint hrightPowerFixed
      (hrightGrow.power hcommonPowerPos)
  exact ⟨{
    commonPower := commonPower
    commonPower_pos := hcommonPowerPos
    seed := selectedSeed
    seed_is_head := rfl
    leftInduced := leftPowered.induced
    rightInduced := rightPowered.induced
    left_induced_eq := leftPowered.induced_eq
    right_induced_eq := rightPowered.induced_eq
    left_power_fixed := hleftPowerFixed
    right_power_fixed := hrightPowerFixed
    left_power_primitive := hleftPowerPrimitive
    right_power_primitive := hrightPowerPrimitive
    left_power_prolongable := hleftPowerProlongable
    right_power_prolongable := hrightPowerProlongable
    left_images_begin_seed := leftPowered.images_begin_head
    right_images_begin_seed := rightPowered.images_begin_head }⟩

/-- The selected left and right local return metrics are both the same actual
metric length of the same return block. -/
structure SelectedLocalSourcesActualReturnMetric
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {self : PairedFirstLetterSelfReturn systems}
    {canonical : CanonicalAllLetterSelfReturn (self := self)}
    (powering : CanonicalCommonSourcePower canonical) where
  metric : Fin (context.decompositions.rank
    (CanonicalAllLetterSelfReturn.level (self := self) canonical)) -> Real
  metric_eq : forall letter, metric letter =
    wordMetricLength (fun coreLetter =>
      sourceLength (synchronized.decode coreLetter))
      ((context.decompositions.decomposition
        (CanonicalAllLetterSelfReturn.level (self := self) canonical)).blocks
          letter)
  metric_pos : forall letter, 0 < metric letter
  left_returnLength_eq : forall letter,
    (context.tower.left
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).returnLength
        letter = metric letter
  right_returnLength_eq : forall letter,
    (context.tower.right
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)).returnLength
        letter = metric letter

/-- 1k: both `returnLength_eq` fields reduce to the same synchronized ambient
metric, with strict positivity inherited from nonempty return blocks. -/
theorem selectedLocalSources_share_actualReturnMetric
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    {context : CommonDerivedContext synchronized}
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {self : PairedFirstLetterSelfReturn systems}
    {canonical : CanonicalAllLetterSelfReturn (self := self)}
    (powering : CanonicalCommonSourcePower canonical) :
    Nonempty (SelectedLocalSourcesActualReturnMetric powering) := by
  let metric : Fin (context.decompositions.rank
      (CanonicalAllLetterSelfReturn.level (self := self) canonical)) -> Real :=
    fun letter =>
      wordMetricLength (fun coreLetter =>
        sourceLength (synchronized.decode coreLetter))
        ((context.decompositions.decomposition
          (CanonicalAllLetterSelfReturn.level (self := self) canonical)).blocks
            letter)
  have hmetricPos : forall letter, 0 < metric letter := by
    intro letter
    obtain ⟨head, tail, hblock⟩ := List.exists_cons_of_ne_nil
      ((context.decompositions.decomposition
        (CanonicalAllLetterSelfReturn.level (self := self) canonical)).blocks_are_returns
          letter).2.1
    have hhead : 0 < sourceLength (synchronized.decode head) :=
      synchronized.left_presentation.letterLength_pos head
    have htail : 0 <= wordMetricLength
        (fun coreLetter => sourceLength (synchronized.decode coreLetter))
        tail :=
      wordMetricLength_nonneg _
        (fun coreLetter =>
          (synchronized.left_presentation.letterLength_pos coreLetter).le)
        tail
    dsimp [metric]
    rw [hblock]
    change 0 < sourceLength (synchronized.decode head) +
      wordMetricLength
        (fun coreLetter => sourceLength (synchronized.decode coreLetter)) tail
    exact add_pos_of_pos_of_nonneg hhead htail
  refine ⟨{
    metric := metric
    metric_eq := fun _ => rfl
    metric_pos := hmetricPos
    left_returnLength_eq := ?_
    right_returnLength_eq := ?_ }⟩
  · intro letter
    calc
      (context.tower.left
          (CanonicalAllLetterSelfReturn.level (self := self) canonical)).returnLength
            letter =
          wordMetricLength synchronized.toReturnCore.coreLengthσ
            ((context.decompositions.decomposition
              (CanonicalAllLetterSelfReturn.level (self := self) canonical)).blocks
                letter) :=
        (context.tower.left
          (CanonicalAllLetterSelfReturn.level (self := self) canonical)).returnLength_eq
            letter
      _ = metric letter := rfl
  · intro letter
    calc
      (context.tower.right
          (CanonicalAllLetterSelfReturn.level (self := self) canonical)).returnLength
            letter =
          wordMetricLength synchronized.toReturnCore.coreLengthτ
            ((context.decompositions.decomposition
              (CanonicalAllLetterSelfReturn.level (self := self) canonical)).blocks
                letter) :=
        (context.tower.right
          (CanonicalAllLetterSelfReturn.level (self := self) canonical)).returnLength_eq
            letter
      _ = metric letter := rfl

/-- Fully assembled Proposition-10 package before forgetting its construction
witnesses. -/
structure CommonDerivedSystemProposition10Package
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    (context : CommonDerivedContext synchronized) where
  system : MetricDurandCommonDerivedSystem context.repetition

/-- 1l: package the common self-return, both source powers, aperiodicity,
decoder data, and the single actual return metric into the production output. -/
theorem commonDerivedSystem_proposition10Package
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    {synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright}
    (context : CommonDerivedContext synchronized)
    {systems : IteratedPairedFirstLetterDerivedSystems context}
    {self : PairedFirstLetterSelfReturn systems}
    {canonical : CanonicalAllLetterSelfReturn (self := self)}
    (powering : CanonicalCommonSourcePower canonical)
    (actualMetric : SelectedLocalSourcesActualReturnMetric powering) :
    Nonempty (CommonDerivedSystemProposition10Package context) := by
  classical
  let level := CanonicalAllLetterSelfReturn.level (self := self) canonical
  let baseDecomposition := context.decompositions.decomposition level
  let rank := context.decompositions.rank level
  let commonWord := baseDecomposition.derived
  let decomposition :=
    CanonicalAllLetterSelfReturn.decomposition (self := self) canonical
  let commonPower :=
    CanonicalCommonSourcePower.commonPower (self := self) powering
  let chosenSeed := CanonicalCommonSourcePower.seed (self := self) powering
  let metric :=
    SelectedLocalSourcesActualReturnMetric.metric (self := self) actualMetric
  let leftLocal := (context.tower.left level).factorization.substitution
  let rightLocal := (context.tower.right level).factorization.substitution
  let leftPowered := leftLocal.power commonPower
  let rightPowered := rightLocal.power commonPower
  let decoder := returnDecoderSubstitutionMetric decomposition
  have hwordAperiodic : ¬ IsPeriodicInfiniteWord commonWord := by
    intro hperiodic
    apply context.notPeriodic
    exact derivedPeriodic_gives_ambientPeriodicRecurrentLanguage
      synchronized baseDecomposition hperiodic
  have hdecoderFixed : decoder.IsFixedPoint commonWord := by
    exact returnDecoder_fixed_derived decomposition
      (CanonicalAllLetterSelfReturn.derived_eq (self := self) canonical)
  have hdecoderPrimitive : IsPrimitiveSubstitution decoder := by
    refine ⟨1, by omega, ?_⟩
    intro sourceLetter targetLetter
    simpa [Substitution.iterateLetter, Substitution.iterateWord,
      Substitution.mapWord, decoder, returnDecoderSubstitutionMetric] using
      (CanonicalAllLetterSelfReturn.contains_all (self := self) canonical
        sourceLetter targetLetter)
  have hdecoderGenerating : ∀ targetLetter, ∃ iterate,
      targetLetter ∈ decoder.iterateLetter iterate chosenSeed := by
    intro targetLetter
    refine ⟨1, ?_⟩
    simpa [Substitution.iterateLetter, Substitution.iterateWord,
      Substitution.mapWord, decoder, returnDecoderSubstitutionMetric] using
      (CanonicalAllLetterSelfReturn.contains_all (self := self) canonical
        chosenSeed targetLetter)
  have hrankGtOne : 1 < rank := by
    by_contra hnot
    have hle : rank ≤ 1 := Nat.le_of_not_gt hnot
    apply hwordAperiodic
    refine ⟨1, by omega, ?_⟩
    intro position
    apply Fin.ext
    have hleft := (commonWord (position + 1)).isLt
    have hright := (commonWord position).isLt
    omega
  obtain ⟨otherLetter, hotherLetter⟩ :=
    Fintype.exists_ne_of_one_lt_card
      (by simpa [rank] using hrankGtOne) chosenSeed
  have mem_eq_of_length_le_one
      (letters : List (Fin rank)) (hlength : letters.length ≤ 1) :
      ∀ {left right : Fin rank},
        left ∈ letters → right ∈ letters → left = right := by
    cases letters with
    | nil => simp
    | cons head tail =>
        cases tail with
        | nil => simp
        | cons next rest => simp at hlength
  have hdecoderSeedLength : 1 < (decoder chosenSeed).length := by
    by_contra hnot
    have hle := Nat.le_of_not_gt hnot
    have hequal := mem_eq_of_length_le_one (decoder chosenSeed) hle
      (CanonicalAllLetterSelfReturn.contains_all (self := self) canonical
        chosenSeed chosenSeed)
      (CanonicalAllLetterSelfReturn.contains_all (self := self) canonical
        chosenSeed otherLetter)
    exact hotherLetter hequal.symm
  have hdecoderProlongable : decoder.ProlongableOn chosenSeed := by
    obtain ⟨first, tail, himage⟩ :=
      List.exists_cons_of_ne_nil (decoder.image_ne_nil chosenSeed)
    have hhead : decoder.imageHead commonWord.head = commonWord.head := by
      have hzero := congrFun hdecoderFixed 0
      simpa using hzero
    have hfirst : first = chosenSeed := by
      have hseedHead : decoder.imageHead chosenSeed = chosenSeed := by
        simpa [chosenSeed,
          CanonicalCommonSourcePower.seed_is_head (self := self) powering] using
          hhead
      simpa [Substitution.imageHead, himage] using hseedHead
    subst first
    refine ⟨tail, ?_, himage⟩
    intro htail
    subst tail
    simp [himage] at hdecoderSeedLength
  let leftInput : MetricDurandProposition10Input commonWord leftPowered
      decomposition := {
    rank_pos := baseDecomposition.rank_pos
    seed := chosenSeed
    seed_is_head :=
      CanonicalCommonSourcePower.seed_is_head (self := self) powering
    source_fixed :=
      CanonicalCommonSourcePower.left_power_fixed (self := self) powering
    source_primitive :=
      CanonicalCommonSourcePower.left_power_primitive (self := self) powering
    source_prolongable :=
      CanonicalCommonSourcePower.left_power_prolongable (self := self) powering
    word_aperiodic := hwordAperiodic
    images_begin_seed :=
      CanonicalCommonSourcePower.left_images_begin_seed (self := self) powering
    derived_eq :=
      CanonicalAllLetterSelfReturn.derived_eq (self := self) canonical
    induced := CanonicalCommonSourcePower.leftInduced (self := self) powering
    induced_eq :=
      CanonicalCommonSourcePower.left_induced_eq (self := self) powering
    decoder_fixed := hdecoderFixed
    decoder_prolongable := hdecoderProlongable
    decoder_generating := hdecoderGenerating
    decoder_primitive := hdecoderPrimitive
    decoder_contains_all :=
      CanonicalAllLetterSelfReturn.contains_all (self := self) canonical }
  let rightInput : MetricDurandProposition10Input commonWord rightPowered
      decomposition := {
    rank_pos := baseDecomposition.rank_pos
    seed := chosenSeed
    seed_is_head :=
      CanonicalCommonSourcePower.seed_is_head (self := self) powering
    source_fixed :=
      CanonicalCommonSourcePower.right_power_fixed (self := self) powering
    source_primitive :=
      CanonicalCommonSourcePower.right_power_primitive (self := self) powering
    source_prolongable :=
      CanonicalCommonSourcePower.right_power_prolongable (self := self) powering
    word_aperiodic := hwordAperiodic
    images_begin_seed :=
      CanonicalCommonSourcePower.right_images_begin_seed (self := self) powering
    derived_eq :=
      CanonicalAllLetterSelfReturn.derived_eq (self := self) canonical
    induced := CanonicalCommonSourcePower.rightInduced (self := self) powering
    induced_eq :=
      CanonicalCommonSourcePower.right_induced_eq (self := self) powering
    decoder_fixed := hdecoderFixed
    decoder_prolongable := hdecoderProlongable
    decoder_generating := hdecoderGenerating
    decoder_primitive := hdecoderPrimitive
    decoder_contains_all :=
      CanonicalAllLetterSelfReturn.contains_all (self := self) canonical }
  let leftBasePower :=
    synchronized.leftPower * context.tower.leftLocalPower *
      commonPower
  let rightBasePower :=
    synchronized.rightPower * context.tower.rightLocalPower *
      commonPower
  have hleftBasePowerPos : 0 < leftBasePower := by
    exact Nat.mul_pos
      (Nat.mul_pos synchronized.leftPower_pos
        context.tower.leftLocalPower_pos)
      (CanonicalCommonSourcePower.commonPower_pos (self := self) powering)
  have hrightBasePowerPos : 0 < rightBasePower := by
    exact Nat.mul_pos
      (Nat.mul_pos synchronized.rightPower_pos
        context.tower.rightLocalPower_pos)
      (CanonicalCommonSourcePower.commonPower_pos (self := self) powering)
  have hleftMetricEq : metric =
      (context.tower.left level).returnLength := by
    funext letter
    exact (SelectedLocalSourcesActualReturnMetric.left_returnLength_eq
      (self := self) actualMetric letter).symm
  have hrightMetricEq : metric =
      (context.tower.right level).returnLength := by
    funext letter
    exact (SelectedLocalSourcesActualReturnMetric.right_returnLength_eq
      (self := self) actualMetric letter).symm
  have hleftScales : SubstitutionScalesLetterLengths leftPowered
      metric (leftScale ^ leftBasePower) := by
    rw [hleftMetricEq]
    have hpower := scalesLetterLengths_power
      (context.tower.left level).scales commonPower
    simpa [leftPowered, leftLocal, leftBasePower, pow_mul,
      Nat.mul_assoc] using hpower
  have hrightScales : SubstitutionScalesLetterLengths rightPowered
      metric (rightScale ^ rightBasePower) := by
    rw [hrightMetricEq]
    have hpower := scalesLetterLengths_power
      (context.tower.right level).scales commonPower
    simpa [rightPowered, rightLocal, rightBasePower, pow_mul,
      Nat.mul_assoc] using hpower
  refine ⟨{
    system := {
      rank := rank
      rank_pos := baseDecomposition.rank_pos
      commonWord := commonWord
      marker := CanonicalAllLetterSelfReturn.marker (self := self) canonical
      decomposition := decomposition
      leftSource := leftPowered
      rightSource := rightPowered
      leftInput := leftInput
      rightInput := rightInput
      leftBasePower := leftBasePower
      rightBasePower := rightBasePower
      leftBasePower_pos := hleftBasePowerPos
      rightBasePower_pos := hrightBasePowerPos
      leftMetric := metric
      rightMetric := metric
      leftMetric_pos :=
        SelectedLocalSourcesActualReturnMetric.metric_pos
          (self := self) actualMetric
      rightMetric_pos :=
        SelectedLocalSourcesActualReturnMetric.metric_pos
          (self := self) actualMetric
      leftScales := hleftScales
      rightScales := hrightScales } }⟩

/-- 1m: repaired public M4.1 aggregator.  Its dependent tower inputs are
formed from `synchronized.toReturnCore`, not from an arbitrary unrelated pair
of recurrent-core metrics. -/
theorem repeatedBoundedLocalSystems_have_commonDerivedSystem
    {alphabet : Type u} [Fintype alphabet] [DecidableEq alphabet]
    {leftSource rightSource : Substitution alphabet} {seed : alphabet}
    {sourceWord : InfiniteWord alphabet} {leftScale rightScale : Real}
    {sourceLength : alphabet -> Real}
    {Pleft : MetricGrowingFixedPresentation leftSource seed sourceWord
      leftScale sourceLength}
    {Pright : MetricGrowingFixedPresentation rightSource seed sourceWord
      rightScale sourceLength}
    (synchronized : MetricSynchronizedPrimitiveCoreData Pleft Pright)
    {markers : CofinalMetricMarkerTower synchronized.toReturnCore.coreWord}
    {decompositions : MetricReturnDecompositionTower markers}
    {tower : BoundedLocalReturnTower synchronized.toReturnCore markers
      decompositions}
    {bounds : BoundedLocalReturnTowerBounds tower}
    {coding : BoundedLocalReturnTowerFiniteCoding bounds}
    (repetition : RepeatedBoundedLocalReturnSystems coding)
    (hnotPeriodic : ¬ HasPeriodicRecurrentLanguage sourceWord) :
    Nonempty (MetricDurandCommonDerivedSystem repetition) := by
  let context : CommonDerivedContext synchronized := {
    markers := markers
    decompositions := decompositions
    tower := tower
    bounds := bounds
    coding := coding
    repetition := repetition
    notPeriodic := hnotPeriodic }
  obtain ⟨systems⟩ := iteratedPairedFirstLetterDerivedSystems_exists context
  let realization : forall stage,
      FirstLetterCanonicalBaseRealization systems stage :=
    fun stage => Classical.choice
      (firstLetterStages_have_canonicalBaseRealizations systems stage)
  obtain ⟨stageRepetition⟩ :=
    pairedFiniteCoding_has_simultaneousFirstLetterRepetition
      systems realization
  obtain ⟨self⟩ :=
    simultaneousFirstLetterRepetition_has_selfReturn stageRepetition
  have hdecoder := selfReturnDecoder_primitive_or_rankOne self
  obtain ⟨all⟩ := selfReturn_has_allLetterIterate self hdecoder
  obtain ⟨canonical⟩ :=
    allLetterSelfReturn_has_canonicalBaseRealization
      (realization self.stage) all
  obtain ⟨powering⟩ :=
    canonicalAllLetterSelfReturn_has_commonSourcePower canonical
  obtain ⟨actualMetric⟩ :=
    selectedLocalSources_share_actualReturnMetric powering
  obtain ⟨package⟩ :=
    commonDerivedSystem_proposition10Package context powering actualMetric
  exact ⟨package.system⟩

end DurandCommonDerived
end
end Symbolic
end CommutingIntervalSimplified
