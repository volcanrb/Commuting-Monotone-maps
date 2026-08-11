import CommutingIntervalSimplified.Base

/-!
# Arc-like spaces

This module isolates the cover-theoretic definition of an arc-like space so
that the fixed-set argument and the inverse-limit development can depend on
it without forming an import cycle.
-/

namespace CommutingIntervalSimplified

open Set

/-- Cover-theoretic definition of an arc-like space: every open cover admits
a continuous interval-valued map whose point fibres refine that cover.  The
map is not required to be onto, so the degenerate one-point continuum is
included. -/
def IsArcLike (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X),
    (∀ U ∈ 𝒰, IsOpen U) → Set.univ ⊆ ⋃₀ 𝒰 →
      ∃ f : X → I, Continuous f ∧
        ∀ y : I, ∃ U ∈ 𝒰, f ⁻¹' {y} ⊆ U

end CommutingIntervalSimplified
