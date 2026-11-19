import CommutingIntervalSimplified.GradedDecoders
import CommutingIntervalSimplified.GradedReturnBranches

/-!
# The graded realization theorem

From the marked cells, local sections and decoders, and the elementary
projections satisfying Proposition 3.5, construct two continuous interval
maps with disjoint periodic-point sets. The global decoder families, their
commutation, and the obstruction to common periodicity are conclusions.
-/

namespace CommutingIntervalSimplified.GradedRealization

open Function Set GradedCells GradedDecoders GradedReturn

/-- The two projection families of Proposition 3.5 for given local pieces. -/
structure CompatibleProjections (P : Pieces) where
  map : Grade → Bool → I → I
  continuous_map : ∀ v i, Continuous (map v i)
  map_cell : ∀ v i K, MapsTo (map v i) (P.cell K) (P.cell (parent v i K))
  map_section : ∀ v i K t, map v i (P.sectionMap K t) =
    P.sectionMap (parent v i K) (map (step (color K) v) i t)
  map_decoder : ∀ v i K {x}, x ∈ P.cell K →
    P.decoder (parent v i K) (map v i x) = map (step (color K) v) i (P.decoder K x)
  square : ∀ v x, map v false (map (step false v) true x) =
    map v true (map (step true v) false x)

/-- The simultaneous continuous decoder constructed by Banach's theorem for
the indicated elementary direction. -/
noncomputable def chosenDecoder (P : Pieces) (v : Grade) (i : Bool) :
    BoundedContinuousFunction I I :=
  (P.exists_family i).choose v

/-- Assemble the actual decoder family and projection families into the
branch equations used for the same-grade dynamics. -/
noncomputable def branchesOfPieces (P : Pieces) (R : CompatibleProjections P)
    (hsep : ∀ {v} {J K : Cell v} {t}, P.sectionMap K t ∈ P.cell J → J = K) :
    Branches I where
    decoder := fun v i x => chosenDecoder P v i x
    projection := R.map
    cell := P.cell
    core := fun J => range (P.sectionMap J)
    sectionMap := P.sectionMap
    localDecoder := P.decoder
    cover := P.cover
    core_subset := by
      rintro v J x ⟨t, rfl⟩
      exact P.section_mem J t
    cell_unique := by
      rintro v x J K hx ⟨t, rfl⟩
      exact hsep hx
    section_mem := fun _ t => ⟨t, rfl⟩
    leftInverse := P.decode_section
    q := P.q
    q_nonneg := P.q.2
    q_lt := P.q_lt
    section_dist := fun J => (P.lip J).dist_le_mul
    direct := fun {v} J {x} hx => (P.exists_family (color J)).choose_spec.1 v J rfl x hx
    opposite := fun {v} J i hi {x} hx => (P.exists_family i).choose_spec.2 v J hi x hx
    projection_square := by
      intro v i j x
      cases i <;> cases j
      · rfl
      · exact R.square v x
      · exact (R.square v x).symm
      · rfl
    projection_cell := R.map_cell
    projection_decoder := R.map_decoder
    projection_section := R.map_section

theorem interval_dist_le_one (x y : I) : dist x y ≤ 1 := by
    change |(x : ℝ) - (y : ℝ)| ≤ 1
    rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]

/-- The empty-spectrum conclusion of Section 3, conditional on realization
of its local geometric pieces and projections. In the separation assumption
the section of every cell lies in that cell's interior. -/
theorem exists_commuting_disjoint_periodicPts (P : Pieces) (R : CompatibleProjections P)
    (hsep : ∀ {v} {J K : Cell v} {t}, P.sectionMap K t ∈ P.cell J → J = K) :
    ∃ f g : IntervalMap, Continuous f ∧ Continuous g ∧ Function.Commute f g ∧
      periodicPts f ∩ periodicPts g = ∅ := by
  let B := branchesOfPieces P R hsep
  let diam := interval_dist_le_one
  refine ⟨(B.squares diam).map (0, 0) false, (B.squares diam).map (0, 0) true,
    (R.continuous_map _ _).comp (chosenDecoder P _ _).continuous,
    (R.continuous_map _ _).comp (chosenDecoder P _ _).continuous,
    (B.squares diam).map_commute (0, 0) false true, B.disjoint_periodicPts diam⟩

end CommutingIntervalSimplified.GradedRealization
