import CommutingIntervalSimplified.GradedCells
import CommutingIntervalSimplified.ReturnSpectrum

/-!
# Lifting common return points through the graded construction

For the labels and successor of Section 3, the decoder and projection squares
give commuting endomorphisms on each grade. A common periodic point belongs
to the interior of a single cell. Decoding it preserves both its colour and
its common exponent. Iterating this lift forces the exponent to be divisible
by arbitrarily large powers of five or seven.

The last theorem takes the geometric data of the construction as hypotheses.
-/

namespace CommutingIntervalSimplified.GradedReturn

open Function Set GradedCells

variable {X : Type*}

/-- The three square identities for the graded decoders and projections. -/
structure Squares (X : Type*) where
  decoder : Grade → Bool → X → X
  projection : Grade → Bool → X → X
  decoder_square : ∀ v i j x,
    decoder (step j v) i (decoder v j x) = decoder (step i v) j (decoder v i x)
  projection_square : ∀ v i j x,
    projection v i (projection (step i v) j x) =
      projection v j (projection (step j v) i x)
  intertwine : ∀ v i j x,
    decoder v i (projection v j x) = projection (step i v) j (decoder (step j v) i x)

namespace Squares

/-- The same-grade endomorphism obtained by decoding and projecting back. -/
def map (S : Squares X) (v : Grade) (i : Bool) : X → X :=
  S.projection v i ∘ S.decoder v i

/-- Decoding lifts the orbit of either generator to the next grade. -/
theorem decoder_semiconj (S : Squares X) (v : Grade) (i j : Bool) :
    Semiconj (S.decoder v i) (S.map v j) (S.map (step i v) j) := by
  intro x
  change S.decoder v i (S.projection v j (S.decoder v j x)) = _
  rw [S.intertwine, S.decoder_square]
  rfl

/-- Corollary 3.7, commutation at each grade. -/
theorem map_commute (S : Squares X) (v : Grade) (i j : Bool) :
    Function.Commute (S.map v i) (S.map v j) := by
  intro x
  calc
    S.map v i (S.map v j x) =
        S.projection v i (S.projection (step i v) j (S.decoder (step i v) j
          (S.decoder v i x))) := congrArg (S.projection v i) (S.decoder_semiconj v i j x)
    _ = S.projection v j (S.projection (step j v) i (S.decoder (step i v) j
          (S.decoder v i x))) := S.projection_square _ _ _ _
    _ = S.map v j (S.map v i x) := congrArg (S.projection v j) (S.intertwine v j i _).symm

end Squares

/-- The geometric data used in the no-return argument. Each grade has the
manuscript's labelled cells and successor. A projection carries each fine
cell into a coarse cell of the same colour. -/
structure Atlas (S : Squares X) where
  cells : ∀ v, ReturnCells (S.map v) (Cell v)
  label_color : ∀ v J, (cells v).color J = color J
  label_next : ∀ v, (cells v).next = next
  projection_cell : ∀ v i K, ∃ J,
    (cells v).color J = (cells (step i v)).color K ∧
    MapsTo (S.projection v i) ((cells (step i v)).cell K) ((cells v).cell J)

namespace Atlas

variable {S : Squares X} (A : Atlas S)

/-- The union of all closed cells of a given colour. -/
def colorSet (v : Grade) (i : Bool) : Set X :=
  {x | ∃ J, (A.cells v).color J = i ∧ x ∈ (A.cells v).cell J}

private theorem opposite_invariant (v : Grade) (c : Bool) :
    MapsTo (S.map v (!c)) (A.colorSet v c) (A.colorSet v c) := by
  rintro x ⟨J, hJ, hx⟩
  refine ⟨(A.cells v).next J, (A.cells v).color_next J |>.trans hJ, ?_⟩
  apply (A.cells v).core_subset
  simpa only [← hJ] using (A.cells v).opposite_maps J hx

/-- A common periodic point lifts to the next grade of its own colour. The
point keeps the *same* exponent for both generators. -/
theorem lift_common {v : Grade} {n : ℕ} (hn : 0 < n) {x : X}
    (hx : ∀ j, IsPeriodicPt (S.map v j) n x) {c : Bool} (hxcolor : x ∈ A.colorSet v c) :
    (∀ j, IsPeriodicPt (S.map (step c v) j) n (S.decoder v c x)) ∧
    S.decoder v c x ∈ A.colorSet (step c v) c := by
  refine ⟨fun j => (hx j).map (S.decoder_semiconj v c j), ?_⟩
  obtain ⟨J, hc, hxJ⟩ := hxcolor
  obtain ⟨K, hK⟩ := (A.cells (step c v)).cover (S.decoder v c x)
  refine ⟨K, ?_, hK⟩
  by_contra hne
  have hKopp : (A.cells (step c v)).color K = !c := by
    cases c <;> cases h : (A.cells _).color K <;> simp_all
  obtain ⟨L, hLcolor, hLmap⟩ := A.projection_cell v c K
  have himage : S.map v c x ∈ A.colorSet v (!c) :=
    ⟨L, hLcolor.trans hKopp, hLmap hK⟩
  have hinv : MapsTo (S.map v c) (A.colorSet v (!c)) (A.colorSet v (!c)) := by
    simpa using A.opposite_invariant v (!c)
  have hreturn : (S.map v c)^[n - 1] (S.map v c x) = x := by
    rw [← iterate_succ_apply, show (n - 1).succ = n by omega]
    exact hx c
  have hother := hinv.iterate (n - 1) himage
  rw [hreturn] at hother
  obtain ⟨L', hL', hxL'⟩ := hother
  have hcore := (A.cells v).mem_core_of_common hn (hx false) (hx true) hxJ
  have heq := (A.cells v).cell_unique hxL' hcore
  rw [heq, hc] at hL'
  cases c <;> contradiction

private def ray (c : Bool) (r : ℕ) : Grade :=
  if c then (0, r) else (r, 0)

private theorem ray_step (c : Bool) (r : ℕ) : step c (ray c r) = ray c (r + 1) := by
  cases c <;> rfl

private theorem exponent_dvd {v : Grade} {c : Bool} {x : X} {n : ℕ} (hn : 0 < n)
    (hx : ∀ j, IsPeriodicPt (S.map v j) n x) (hxc : x ∈ A.colorSet v c) :
    cycleLength c v ∣ n := by
  obtain ⟨J, hc, hxJ⟩ := hxc
  have hperiod := (A.cells v).cell_periodic_of_common hn (hx false) (hx true) hxJ
  rw [A.label_next] at hperiod
  rw [A.label_color] at hc
  rw [← hc]
  exact cycleLength_dvd_of_isPeriodicPt hn hperiod

/-- Section 3.5. For every realization of the graded construction, the
pair at grade zero has no positive common return exponent. -/
theorem commonReturnExponents_eq_empty (A : Atlas S) :
    commonReturnExponents (S.map (0, 0) false) (S.map (0, 0) true) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro n ⟨hn, x, hf, hg⟩
  obtain ⟨J, hxJ⟩ := (A.cells (0, 0)).cover x
  let c := (A.cells (0, 0)).color J
  have hlift : ∀ r : ℕ, ∃ y : X, (∀ j, IsPeriodicPt (S.map (ray c r) j) n y) ∧
      y ∈ A.colorSet (ray c r) c := by
    intro r
    induction r with
    | zero =>
      have hzero : ray c 0 = (0, 0) := by cases c <;> rfl
      rw [hzero]
      exact ⟨x, fun j => by cases j <;> assumption, J, rfl, hxJ⟩
    | succ r ih =>
      obtain ⟨y, hy, hyc⟩ := ih
      rw [← ray_step]
      exact ⟨_, A.lift_common hn hy hyc⟩
  obtain ⟨y, hy, hyc⟩ := hlift n
  have hle := Nat.le_of_dvd hn (A.exponent_dvd hn hy hyc)
  have hlt : n < cycleLength c (ray c n) := by
    cases c <;> exact Nat.lt_pow_self (by decide)
  exact (Nat.not_lt_of_ge hle) hlt

end Atlas

end CommutingIntervalSimplified.GradedReturn
