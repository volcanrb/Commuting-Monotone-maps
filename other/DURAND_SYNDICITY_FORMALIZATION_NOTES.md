# Durand--Rigo syndeticity formalization notes

- Because `DurandPresentation.coding` is injective and every target letter
  occurs in the output, `coding_eq` makes the coding bijective.  Both source
  presentations can therefore be relabeled onto the common target alphabet;
  the manuscript should state this reduction explicitly.
- The first higher-block draft used all formal blocks `A^n`.  That does not
  preserve the strengthened invariant that every presentation letter occurs
  in the fixed word (nor generation of the entire alphabet).  One must either
  restrict to an occurring-block subtype and prove closure, or use the weaker
  fixed-metric presentation adopted by the Lean proof, which intentionally
  makes no occurrence/generation claim about unused formal blocks.
- A direct nonempty-word marker does not reduce to stabilization of ordinary
  support: the marker may be created across two image boundaries even when
  each individual letter image avoids it.  The finite prefix/suffix signature
  needed to repair this is precisely higher-block context, so the proof keeps
  the manuscript's higher-block reduction but states its weaker invariant
  correctly.
- Exact scaling of a positive letter metric immediately gives uniform upper
  and lower ordinary-length bounds for every letter image.  This is cleaner
  than repeatedly invoking coarse growth-type notation.
- The manuscript's growth lemma hides a separate finite-matrix step: after a
  positive power kills peripheral periods, normalized ordinary letter-image
  lengths have positive limits.  The formal proof exposes this as
  `exists_power_hasPositiveLengthLimits`.
- Endpoint conventions matter: negating `AppearsWithBoundedGaps` yields a
  window avoiding the marker only after accounting for the marker length.
  The formal proof isolates that conversion in
  `exists_arbitrarily_long_avoiding_window`.
