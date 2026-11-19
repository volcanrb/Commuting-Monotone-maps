import CommutingIntervalSimplified.GradedShoulderDecoders
import CommutingIntervalSimplified.GradedCellGeometry
import CommutingIntervalSimplified.GradedDecoders
import CommutingIntervalSimplified.GradedMarkProjection
import CommutingIntervalSimplified.GradedProjectionGrades

/-! # Local decoders on the folded physical cells

The unfolded mark belongs to a specific successor cell in the target grade.
Composing the normalized decoder with the inverse cell coordinate gives the
continuous physical decoder, with the prescribed affine section as a right inverse.
-/

namespace CommutingIntervalSimplified.GradedMarkedCells

open Set GradedCells GradedGeometry GradedShoulderDecoders DecoderProjection
noncomputable section

/-- Unfolded coordinate of the left end of the central third of cell `H`. -/
def markCoordinate {v : Grade} (H : Cell v) : ℝ :=
  (2*(residue H).val + (((quarterNumber H.quarter).val : ℝ) + 1/3)/4) / M v

def beta {v : Grade} (J : Cell v) (side : Bool) : ℝ := markCoordinate (markCell J side)

/-- Every unfolded mark is a subdivision vertex at the target grade. -/
theorem markCoordinate_vertex {v : Grade} (H : Cell v) :
    ∃ z : ℤ, (ConcreteProjection.density v : ℝ) * markCoordinate H = z := by
  refine ⟨24*(residue H).val + 3*(quarterNumber H.quarter).val + 1, ?_⟩
  have hv : (M v : ℝ) ≠ 0 := by exact_mod_cast (M_pos v).ne'
  unfold ConcreteProjection.density markCoordinate
  push_cast
  field_simp
  ring

theorem markCoordinate_projection {u v : Grade} (ha : u.1 ≤ v.1) (hb : u.2 ≤ v.2)
    {d : ℕ} (hd : M v = d * M u) (H : Cell v) :
    ∃ n : ℤ, (d:ℝ)*markCoordinate H = markCoordinate (project ha hb H) + 2*n := by
  obtain ⟨n, hn⟩ := residue_project_turns ha hb H
  have h₀ : (M u : ℝ) ≠ 0 := by exact_mod_cast (M_pos u).ne'
  have hd₀ : d ≠ 0 := fun h => (M_pos v).ne' (by simpa [h] using hd)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd₀
  refine ⟨n, ?_⟩
  unfold markCoordinate
  rw [hn, hd]
  change _ = (2 * ((residue (project ha hb H)).val : ℝ) +
    ((quarterNumber H.quarter).val + 1/3)/4) / M u + _
  push_cast
  field_simp
  ring

/-- Lemma 3.1. The two marks differ by an even integral shift after dilation,
for either shoulder of every cell and any grade increment. -/
theorem beta_projection (w v : Grade) (J : Cell (ConcreteProjection.up w v)) (side : Bool) :
    ∃ n : ℤ, (ConcreteProjection.degree w : ℝ)*beta J side =
      beta (ConcreteProjection.down w v J) side + 2*n := by
  let c := color J
  have h₁ : (step c v).1 ≤ (step c (ConcreteProjection.up w v)).1 := by
    cases c <;> simp [step]
  have h₂ : (step c v).2 ≤ (step c (ConcreteProjection.up w v)).2 := by
    cases c <;> simp [step]
  have hu : step c (ConcreteProjection.up w v) = ConcreteProjection.up w (step c v) := by
    cases c <;> simp [step, ConcreteProjection.up, Nat.add_right_comm]
  have hM : M (step c (ConcreteProjection.up w v)) = M w * M (step c v) := by
    rw [hu, ConcreteProjection.M_up, Nat.mul_comm]
  obtain ⟨n, hn⟩ := markCoordinate_projection h₁ h₂ hM (markCell J side)
  refine ⟨n, ?_⟩
  have hp := project_mark (u := v) (v := ConcreteProjection.up w v)
    (Nat.le_add_right ..) (Nat.le_add_right ..) J side
  change (project h₁ h₂ (markCell J side)) = markCell (ConcreteProjection.down w v J) side at hp
  rw [hp] at hn
  simpa only [ConcreteProjection.degree, Int.cast_natCast, beta] using hn

def sectionMap {v : Grade} (J : Cell v) : I → I := chart J ∘ sectionCoord

def localDecoder {v : Grade} (J : Cell v) : I → I :=
  decoder (beta J false) (beta J true) ∘ coord J

theorem continuous_localDecoder {v : Grade} (J : Cell v) : Continuous (localDecoder J) :=
  (continuous_decoder _ _).comp (continuous_coord J)

theorem section_mem {v : Grade} (J : Cell v) (x : I) : sectionMap J x ∈ physicalCell J :=
  mem_range_self (sectionCoord x)

theorem decode_section {v : Grade} (J : Cell v) : Function.LeftInverse (localDecoder J) (sectionMap J) := by
  intro x
  simpa only [localDecoder, sectionMap, Function.comp_apply, coord_chart] using
    (decoder_section (beta J false) (beta J true) x)

theorem localDecoder_chart {v : Grade} (J : Cell v) (u : I) :
    localDecoder J (chart J u) = decoder (beta J false) (beta J true) u := by
  simp [localDecoder, coord_chart]

private def normalizedEnd (side : Bool) : I := if side then rightEndpoint else leftEndpoint

theorem endpoint_value {v : Grade} (J : Cell v) (side : Bool) :
    (localDecoder J (chart J (normalizedEnd side)) : ℝ) = fold (beta J side) := by
  rw [localDecoder_chart]
  cases side
  · exact chartDecoder_zero _ _
  · exact chartDecoder_one _ _

@[simp] theorem fold_markCoordinate {v : Grade} (J : Cell v) :
    fold (markCoordinate J) = (sectionMap J leftEndpoint : ℝ) := by
  rw [sectionMap, Function.comp_apply, chart_eq_fold]
  simp [markCoordinate, sectionCoord]

theorem localDecoder_endpoint {v : Grade} (J : Cell v) (side : Bool) :
    localDecoder J (chart J (normalizedEnd side)) = sectionMap (markCell J side) leftEndpoint := by
  apply Subtype.ext
  rw [endpoint_value, beta, fold_markCoordinate]

private def EndAgreement {v : Grade} (J K : Cell v) (s t : Bool) : Prop :=
  (color J = color K → beta J s = beta K t ∧
    ∀ i, i ≠ color J → liftNext i J = liftNext i K) ∧
  (color J ≠ color K → markCell J s = liftNext (color J) K ∧
    markCell K t = liftNext (color K) J)

private theorem EndAgreement.symm {v : Grade} {J K : Cell v} {s t : Bool}
    (h : EndAgreement J K s t) : EndAgreement K J t s := by
  refine ⟨fun e => ⟨(h.1 e.symm).1.symm, fun i hi => ((h.1 e.symm).2 i (e ▸ hi)).symm⟩,
    fun ne => (h.2 (Ne.symm ne)).symm⟩

private theorem successive_quarters {v : Grade} {J K : Cell v} (hr : residue J = residue K)
    (hq : (quarterNumber J.quarter).val+1 = (quarterNumber K.quarter).val) :
    EndAgreement J K true false := by
  obtain ⟨h₅,h₇⟩ := residue_inj_coords hr
  rcases J with ⟨q,a,b⟩
  rcases K with ⟨r,c,d⟩
  cases h₅; cases h₇
  cases q <;> cases r <;> simp_all [quarterNumber, EndAgreement, color, markCell, liftNext] <;> rfl

private theorem same_end_left {v : Grade} {J K : Cell v} (hj : J.quarter = .left)
    (hk : K.quarter = .left) : EndAgreement J K false false := by
  rcases J with ⟨q,a,b⟩; rcases K with ⟨r,c,d⟩
  cases hj; cases hk
  refine ⟨fun _ => ⟨rfl, fun i hi => ?_⟩, fun ne => (ne rfl).elim⟩
  cases i <;> rfl

private theorem same_end_right {v : Grade} {J K : Cell v} (hj : J.quarter = .right)
    (hk : K.quarter = .right) : EndAgreement J K true true := by
  rcases J with ⟨q,a,b⟩; rcases K with ⟨r,c,d⟩
  cases hj; cases hk
  refine ⟨fun _ => ⟨rfl, fun i hi => ?_⟩, fun ne => (ne rfl).elim⟩
  cases i <;> rfl

private theorem ordered_end_agreement {v : Grade} {J K : Cell v}
    (h : (indexEquiv v J).val+1 = (indexEquiv v K).val) :
    EndAgreement J K (if forward J then true else false) (if forward K then false else true) := by
  classical
  rw [index_val, index_val] at h
  have ar := (residue J).isLt
  have br := (residue K).isLt
  have aq := (quarterNumber J.quarter).isLt
  have bq := (quarterNumber K.quarter).isLt
  by_cases f : forward J <;> by_cases g : forward K <;>
    simp only [f, g, if_true, if_false] at h ⊢
  · exact successive_quarters (Fin.ext (by omega)) (by omega)
  · apply same_end_right <;> apply quarterNumber.injective <;> apply Fin.ext <;>
      change _ = 3 <;> omega
  · apply same_end_left <;> apply quarterNumber.injective <;> apply Fin.ext <;>
      change _ = 0 <;> omega
  · exact (successive_quarters (J := K) (K := J) (Fin.ext (by omega)) (by omega)).symm

private theorem ordered_touch {v : Grade} {J K : Cell v} {u t : I}
    (hlt : (indexEquiv v J).val < (indexEquiv v K).val) (he : chart J u = chart K t) :
    (indexEquiv v J).val+1 = (indexEquiv v K).val ∧
    u = normalizedEnd (if forward J then true else false) ∧
    t = normalizedEnd (if forward K then false else true) := by
  have hN : ((4*M v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos (by decide : 0 < 4) (M_pos v)).ne'
  have e := congrArg Subtype.val he
  change (chart J u : ℝ) = (chart K t : ℝ) at e
  rw [chart_val, chart_val, div_left_inj' hN] at e
  have gap : ((indexEquiv v J).val : ℝ)+1 ≤ (indexEquiv v K).val := by
    exact_mod_cast hlt
  have U₀ := u.2.1; have U₁ := u.2.2
  have T₀ := t.2.1; have T₁ := t.2.2
  by_cases f : forward J <;> by_cases g : forward K <;>
    simp only [f, g, if_true, if_false] at e ⊢ <;>
    refine ⟨?_, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    first | exact_mod_cast (show ((indexEquiv v J).val : ℝ)+1 = (indexEquiv v K).val by linarith)
          | change (u:ℝ) = 0; linarith
          | change (u:ℝ) = 1; linarith
          | change (t:ℝ) = 0; linarith
          | change (t:ℝ) = 1; linarith

private def PointAgreement {v : Grade} (J K : Cell v) (x : I) : Prop :=
  (color J = color K → localDecoder J x = localDecoder K x ∧
    ∀ i, i ≠ color J → liftNext i J = liftNext i K) ∧
  (color J ≠ color K → localDecoder J x = sectionMap (liftNext (color J) K) leftEndpoint ∧
    localDecoder K x = sectionMap (liftNext (color K) J) leftEndpoint)

private theorem PointAgreement.symm {v : Grade} {J K : Cell v} {x : I}
    (h : PointAgreement J K x) : PointAgreement K J x := by
  refine ⟨fun e => ⟨(h.1 e.symm).1.symm, fun i hi => ((h.1 e.symm).2 i (e ▸ hi)).symm⟩,
    fun ne => (h.2 (Ne.symm ne)).symm⟩

private theorem ordered_point_agreement {v : Grade} {J K : Cell v} {x : I}
    (hlt : (indexEquiv v J).val < (indexEquiv v K).val)
    (hx : x ∈ physicalCell J) (hy : x ∈ physicalCell K) : PointAgreement J K x := by
  obtain ⟨u,hu⟩ := hx
  obtain ⟨t,ht⟩ := hy
  obtain ⟨hadj, hju, hkt⟩ := ordered_touch hlt (hu.trans ht.symm)
  have h := ordered_end_agreement hadj
  rw [hju] at hu; rw [hkt] at ht
  refine ⟨fun eq => ⟨?_, (h.1 eq).2⟩, fun ne => ⟨?_, ?_⟩⟩
  · apply Subtype.ext
    calc (localDecoder J x : ℝ) = fold (beta J _) := hu ▸ endpoint_value J _
         _ = fold (beta K _) := congrArg fold (h.1 eq).1
         _ = (localDecoder K x : ℝ) := ht ▸ (endpoint_value K _).symm
  · rw [← hu, localDecoder_endpoint, (h.2 ne).1]
  · rw [← ht, localDecoder_endpoint, (h.2 ne).2]

private theorem point_agreement {v : Grade} {J K : Cell v} {x : I}
    (hx : x ∈ physicalCell J) (hy : x ∈ physicalCell K) : PointAgreement J K x := by
  rcases lt_trichotomy (indexEquiv v J).val (indexEquiv v K).val with h | h | h
  · exact ordered_point_agreement h hx hy
  · obtain rfl := (indexEquiv v).injective (Fin.ext h)
    exact ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩, fun ne => (ne rfl).elim⟩
  · exact (ordered_point_agreement h hy hx).symm

/-- The concrete folded cells and marked triangular decoders satisfy every
input of the simultaneous Banach construction. -/
def pieces : GradedDecoders.Pieces where
  cell := physicalCell
  closed := cell_closed
  cover := cover
  sectionMap := sectionMap
  decoder := localDecoder
  decoder_cont J := (continuous_localDecoder J).continuousOn
  section_mem := section_mem
  decode_section J := decode_section J
  q := 1 / 12
  q_lt := by norm_num
  lip := GradedGeometry.section_lip
  mixed_mark hx hy hne := ((point_agreement hx hy).2 hne).1
  same_mark hx hy h := ((point_agreement hx hy).1 h).1
  same_lift hx hy h := ((point_agreement hx hy).1 h).2

/-- Continuous decoder families solving the graded branch recursion for the
actual cells and sections, at every grade. -/
theorem exists_decoders :
    ∃ D : Grade → Bool → I → I, (∀ v i, Continuous (D v i)) ∧
      (∀ {v} (J : Cell v) {x}, x ∈ physicalCell J → D v (color J) x = localDecoder J x) ∧
      (∀ {v} (J : Cell v) i, color J ≠ i → ∀ {x}, x ∈ physicalCell J →
        D v i x = sectionMap (liftNext i J) (D (step (color J) v) i (localDecoder J x))) := by
  choose D own opp using pieces.exists_family
  exact ⟨fun v i => D i v, fun v i => (D i v).continuous,
    fun {v} J {x} hx => own _ v J rfl x hx, fun {v} J i hi {x} hx => opp i v J hi x hx⟩


end
end CommutingIntervalSimplified.GradedMarkedCells
