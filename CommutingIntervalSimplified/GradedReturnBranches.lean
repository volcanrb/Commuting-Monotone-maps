import CommutingIntervalSimplified.GradedReturn
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# From decoder branch equations to the graded no-return theorem

The direct and opposite-colour equations for the decoder already imply
the decoder square. Compatibility of the local sections and local decoders
with projections implies global intertwining: the error either vanishes on
a direct branch or shrinks by the uniform section contraction factor on an opposite branch.
-/

namespace CommutingIntervalSimplified.GradedReturn

open Function Set GradedCells

/-- The local geometric inputs to the recursion in Section 3. Each projection
respects the cells, intertwines the local decoders, and carries sections to
sections at the projected labels. -/
structure Branches (X : Type*) [MetricSpace X] where
  decoder : Grade → Bool → X → X
  projection : Grade → Bool → X → X
  cell : ∀ {v}, Cell v → Set X
  core : ∀ {v}, Cell v → Set X
  sectionMap : ∀ {v}, Cell v → X → X
  localDecoder : ∀ {v}, Cell v → X → X
  cover : ∀ v x, ∃ J : Cell v, x ∈ cell J
  core_subset : ∀ {v} (J : Cell v), core J ⊆ cell J
  cell_unique : ∀ {v x} {J K : Cell v}, x ∈ cell J → x ∈ core K → J = K
  section_mem : ∀ {v} (J : Cell v) t, sectionMap J t ∈ core J
  leftInverse : ∀ {v} (J : Cell v), LeftInverse (localDecoder J) (sectionMap J)
  q : ℝ
  q_nonneg : 0 ≤ q
  q_lt : q < 1
  section_dist : ∀ {v} (J : Cell v) x y,
    dist (sectionMap J x) (sectionMap J y) ≤ q * dist x y
  direct : ∀ {v} (J : Cell v) {x}, x ∈ cell J → decoder v (color J) x = localDecoder J x
  opposite : ∀ {v} (J : Cell v) i, color J ≠ i → ∀ {x}, x ∈ cell J →
    decoder v i x = sectionMap (liftNext i J) (decoder (step (color J) v) i (localDecoder J x))
  projection_square : ∀ v i j x,
    projection v i (projection (step i v) j x) = projection v j (projection (step j v) i x)
  projection_cell : ∀ v j K, MapsTo (projection v j) (cell K) (cell (parent v j K))
  projection_decoder : ∀ v j K {x}, x ∈ cell K →
    localDecoder (parent v j K) (projection v j x) =
      projection (step (color K) v) j (localDecoder K x)
  projection_section : ∀ v j K t, projection v j (sectionMap K t) =
    sectionMap (parent v j K) (projection (step (color K) v) j t)

namespace Branches

variable {X : Type*} [MetricSpace X] (B : Branches X)

private theorem lift_color {v : Grade} {i : Bool} (J : Cell v) (h : color J ≠ i) :
    color (liftNext i J) = color J := by
  rcases J with ⟨q, a, b⟩
  cases i <;> cases q <;> simp_all [color, liftNext, sevenCell, fiveCell]

private theorem step_swap (i j : Bool) (v : Grade) : step i (step j v) = step j (step i v) := by
  cases i <;> cases j <;> rfl

private theorem projection_lift_same (v : Grade) (i : Bool) (J : Cell v)
    (h : color J ≠ i) (t : X) :
    B.projection v i (B.sectionMap (liftNext i J) t) =
      B.sectionMap (next J) (B.projection (step (color J) v) i t) := by
  rw [B.projection_section, parent_liftNext i J h, lift_color J h]

private theorem projection_lift_across (v : Grade) (j i : Bool) (K : Cell (step j v))
    (h : color K ≠ i) (t : X) :
    B.projection (step i v) j (B.sectionMap (liftNext i K) t) =
      B.sectionMap (liftNext i (parent v j K)) (B.projection (step i (step (color K) v)) j t) := by
  cases i <;> cases j <;> (
    calc
      _ = _ := by first
        | exact B.projection_section (step false v) false (liftNext false K) t
        | exact B.projection_section (step false v) true (liftNext false K) t
        | exact B.projection_section (step true v) false (liftNext true K) t
        | exact B.projection_section (step true v) true (liftNext true K) t
      _ = _ := by
        erw [lift_color K h, step_swap (color K)]
        congr 1
        exact project_liftNext_natural _ _ _ K)

private theorem square_on_cell {v : Grade} (J : Cell v) {x} (hx : x ∈ B.cell J)
    (j : Bool) (hne : color J ≠ j) :
    B.decoder (step j v) (color J) (B.decoder v j x) =
      B.decoder (step (color J) v) j (B.decoder v (color J) x) := by
  rw [B.direct J hx, B.opposite J j hne hx]
  let t := B.decoder (step (color J) v) j (B.localDecoder J x)
  change B.decoder (step j v) (color J) (B.sectionMap (liftNext j J) t) = t
  rw [← lift_color J hne, B.direct (liftNext j J) (B.core_subset _ (B.section_mem _ t))]
  exact B.leftInverse _ _

/-- The graded decoder square follows from cancellation of the outer
opposite-colour section by its own decoder. -/
theorem decoder_square (v : Grade) (i j : Bool) (x : X) :
    B.decoder (step j v) i (B.decoder v j x) = B.decoder (step i v) j (B.decoder v i x) := by
  by_cases hij : i = j
  · subst j; rfl
  obtain ⟨J, hx⟩ := B.cover v x
  by_cases hi : color J = i
  · subst i
    exact B.square_on_cell J hx j hij
  · have hj : color J = j := by cases h : color J <;> cases i <;> cases j <;> simp_all
    subst j
    exact (B.square_on_cell J hx i hi).symm

private theorem intertwining_error (diam : ∀ x y : X, dist x y ≤ 1) (n : ℕ) :
    ∀ v i j x, dist (B.decoder v i (B.projection v j x))
      (B.projection (step i v) j (B.decoder (step j v) i x)) ≤ B.q ^ n := by
  induction n with
  | zero =>
    intro v i j x
    simpa using diam (B.decoder v i (B.projection v j x))
      (B.projection (step i v) j (B.decoder (step j v) i x))
  | succ n ih =>
    intro v i j x
    obtain ⟨K, hx⟩ := B.cover (step j v) x
    have hx' := B.projection_cell v j K hx
    have hc := color_parent v j K
    by_cases hi : color K = i
    · subst i
      rw [← hc, B.direct _ hx', hc, B.direct K hx, B.projection_decoder v j K hx, dist_self]
      exact pow_nonneg B.q_nonneg _
    · rw [B.opposite (parent v j K) i (by simpa only [hc] using hi) hx',
        B.opposite K i hi hx, B.projection_lift_across v j i K hi,
        B.projection_decoder v j K hx, hc, step_swap (color K) j v]
      calc
        _ ≤ _ := B.section_dist _ _ _
        _ ≤ B.q * B.q ^ n :=
          mul_le_mul_of_nonneg_left (ih (step (color K) v) i j (B.localDecoder K x)) B.q_nonneg
        _ = _ := (pow_succ' _ _).symm

/-- The decoder commutes with each elementary projection. The diameter bound
is satisfied by the usual metric on the unit interval. -/
theorem intertwine (diam : ∀ x y : X, dist x y ≤ 1) (v : Grade) (i j : Bool) (x : X) :
    B.decoder v i (B.projection v j x) = B.projection (step i v) j (B.decoder (step j v) i x) := by
  apply dist_le_zero.mp
  apply ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one B.q_nonneg B.q_lt)
  intro n
  exact B.intertwining_error diam n v i j x

/-- Assemble the three squares from the local geometric equations. -/
def squares (diam : ∀ x y : X, dist x y ≤ 1) : Squares X where
  decoder := B.decoder
  projection := B.projection
  decoder_square := B.decoder_square
  projection_square := B.projection_square
  intertwine := B.intertwine diam

/-- Projecting the opposite-colour branch places the image strictly inside
the successor cell. -/
def atlas (diam : ∀ x y : X, dist x y ≤ 1) : Atlas (B.squares diam) where
  cells v := {
    color := color
    next := next
    cell := B.cell
    core := B.core
    cover := B.cover v
    core_subset := B.core_subset
    cell_unique := B.cell_unique
    color_next := color_next
    opposite_maps := by
      intro J x hx
      have h : color J ≠ !color J := by cases color J <;> decide
      change B.projection v _ (B.decoder v _ x) ∈ B.core (next J)
      rw [B.opposite J _ h hx, B.projection_lift_same _ _ J h]
      exact B.section_mem _ _ }
  label_color _ _ := rfl
  label_next _ := rfl
  projection_cell v i K := ⟨parent v i K, color_parent v i K, B.projection_cell v i K⟩

/-- The two explicit composites at grade zero have disjoint sets of periodic
points as soon as their branch and projection equations have been realized. -/
theorem disjoint_periodicPts (diam : ∀ x y : X, dist x y ≤ 1) :
    periodicPts (B.projection (0, 0) false ∘ B.decoder (0, 0) false) ∩
      periodicPts (B.projection (0, 0) true ∘ B.decoder (0, 0) true) = ∅ :=
  (commonReturnExponents_eq_empty_iff _ _).mp (B.atlas diam).commonReturnExponents_eq_empty

end Branches

end CommutingIntervalSimplified.GradedReturn
