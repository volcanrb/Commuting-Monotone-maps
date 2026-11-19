import CommutingIntervalSimplified.GradedRealization
import CommutingIntervalSimplified.GradedConcreteMatch
import CommutingIntervalSimplified.GradedProjectionFamily

/-! # Projection identities in physical interval coordinates -/

namespace CommutingIntervalSimplified.ConcreteProjection

open Set GradedCells GradedGeometry GradedMarkedCells GradedShoulderDecoders
open DecoderProjection GradedProjection GradedRealization

noncomputable section

private theorem odd_degree (w : Grade) : Odd (degree w) := by
  change Odd ((5 ^ w.1 * 7 ^ w.2 : ℕ) : ℤ)
  exact_mod_cast ((show Odd (5 : ℕ) by decide).pow).mul ((show Odd (7 : ℕ) by decide).pow)

private theorem extend_unit (f : IntervalFunction) (x : I) : extend f x = (f x : ℝ) := by
  rw [extend, projIcc_of_mem _ x.property]

/-- The normalized update equation for the family of geometric projections. -/
def ChartEquations (R : Grade → Family) : Prop :=
  ∀ w v (J : Cell (up w v)) (u : I), ∃ a : I,
    R w v (chart J u) = chart (down w v J) a ∧
      (a : ℝ) = (chartMatch w v J).map (extend (R w (step (color J) v))) u

private theorem maps_cell {R : Grade → Family} (hR : ChartEquations R) (w v : Grade)
    (J : Cell (up w v)) : MapsTo (R w v) (physicalCell J) (physicalCell (down w v J)) := by
  rintro x ⟨u, rfl⟩
  obtain ⟨a, ha, _⟩ := hR w v J u
  exact ⟨a, ha.symm⟩

private theorem maps_section {R : Grade → Family} (hR : ChartEquations R)
    (hadm : ∀ w v, GridAdmissible (density v) (degree w) (extend (R w v)))
    (w v : Grade) (J : Cell (up w v)) (u : I) :
    R w v (sectionMap J u) =
      sectionMap (down w v J) (R w (step (color J) v) u) := by
  obtain ⟨a,ha,hval⟩ := hR w v J (sectionCoord u)
  change R w v (chart J (sectionCoord u)) = chart _ _
  rw [ha]
  apply congrArg (chart _)
  apply Subtype.ext
  have hs := (chartMatch w v J).map_section (hadm _ _) (density_pos _)
    (degree_pos _) (odd_degree w) u.property
  change (a : ℝ) = (1 + (R w (step (color J) v) u : ℝ)) / 3
  exact hval.trans (hs.trans (by rw [extend_unit]))

private theorem maps_decoder {R : Grade → Family} (hR : ChartEquations R)
    (hadm : ∀ w v, GridAdmissible (density v) (degree w) (extend (R w v)))
    (w v : Grade) (J : Cell (up w v)) {x : I} (hx : x ∈ physicalCell J) :
    localDecoder (down w v J) (R w v x) = R w (step (color J) v) (localDecoder J x) := by
  obtain ⟨u,rfl⟩ := hx
  obtain ⟨a,ha,hval⟩ := hR w v J u
  rw [ha, localDecoder_chart, localDecoder_chart]
  apply Subtype.ext
  change chartDecoder _ _ (a : ℝ) = _
  rw [hval, ← extend_unit]
  exact (chartMatch w v J).map_decoder (hadm _ _) (density_pos _)
    (degree_pos _) (odd_degree w) u.property

private def axis : Bool → Grade
  | false => (1, 0)
  | true => (0, 1)

/-- In the two elementary directions the chart equations give every
hypothesis of the graded realization theorem. -/
def compatibleOfChart (R : Grade → Family) (hR : ChartEquations R)
    (hadm : ∀ w v, GridAdmissible (density v) (degree w) (extend (R w v)))
    (hsquare : ∀ v x, R (1, 0) v (R (0, 1) (step false v) x) =
      R (0, 1) v (R (1, 0) (step true v) x)) : CompatibleProjections pieces where
  map v i := R (axis i) v
  continuous_map v i := (R (axis i) v).continuous
  map_cell v i K := by
    cases i
    · exact maps_cell hR (1, 0) v K
    · exact maps_cell hR (0, 1) v K
  map_section v i K t := by
    cases i
    · exact maps_section hR hadm (1, 0) v K t
    · exact maps_section hR hadm (0, 1) v K t
  map_decoder v i K x hx := by
    cases i
    · exact maps_decoder hR hadm (1, 0) v K hx
    · exact maps_decoder hR hadm (0, 1) v K hx
  square := hsquare

end
end CommutingIntervalSimplified.ConcreteProjection
