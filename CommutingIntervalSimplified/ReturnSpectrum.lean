import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Common return exponents

The two-colour cell argument in Sections 2 and 3 works for arbitrary self-maps.
A cell may meet another cell at a boundary point. Its designated interior
can meet only its own cell, which suffices to recover the successor's period.
-/

namespace CommutingIntervalSimplified

open Function Set

variable {X C : Type*}

/-- Positive exponents at which the two iterates fix the same point. -/
def commonReturnExponents (f g : X → X) : Set ℕ :=
  {n | 0 < n ∧ ∃ x, IsPeriodicPt f n x ∧ IsPeriodicPt g n x}

/-- A pair of maps moves each closed cell into the interior of its successor
under the generator of the opposite colour. -/
structure ReturnCells (F : Bool → X → X) (C : Type*) where
  color : C → Bool
  next : C → C
  cell : C → Set X
  core : C → Set X
  cover : ∀ x, ∃ J, x ∈ cell J
  core_subset : ∀ J, core J ⊆ cell J
  cell_unique : ∀ {x J K}, x ∈ cell J → x ∈ core K → J = K
  color_next : ∀ J, color (next J) = color J
  opposite_maps : ∀ J, MapsTo (F (!(color J))) (cell J) (core (next J))

/-- Taking a common multiple synchronizes two positive return times. -/
theorem mem_periodicPts_inter_iff {f g : X → X} {x : X} :
    x ∈ periodicPts f ∩ periodicPts g ↔
      ∃ n > 0, IsPeriodicPt f n x ∧ IsPeriodicPt g n x := by
  constructor
  · rintro ⟨⟨p, hp, hf⟩, ⟨q, hq, hg⟩⟩
    exact ⟨p * q, Nat.mul_pos hp hq, hf.mul_const q, hg.const_mul p⟩
  · rintro ⟨n, hn, hf, hg⟩
    exact ⟨⟨n, hn, hf⟩, ⟨n, hn, hg⟩⟩

theorem commonReturnExponents_eq_empty_iff (f g : X → X) :
    commonReturnExponents f g = ∅ ↔ periodicPts f ∩ periodicPts g = ∅ := by
  simp only [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h x hx
    obtain ⟨n, hn, hf, hg⟩ := mem_periodicPts_inter_iff.mp hx
    exact h n ⟨hn, x, hf, hg⟩
  · rintro h n ⟨hn, x, hf, hg⟩
    exact h x (mem_periodicPts_inter_iff.mpr ⟨n, hn, hf, hg⟩)

theorem commonReturnExponents_mul {f g : X → X} {n k : ℕ}
    (hn : n ∈ commonReturnExponents f g) (hk : 0 < k) :
    k * n ∈ commonReturnExponents f g := by
  obtain ⟨hn, x, hf, hg⟩ := hn
  exact ⟨Nat.mul_pos hk hn, x, hf.const_mul k, hg.const_mul k⟩

namespace ReturnCells

variable {F : Bool → X → X} (R : ReturnCells F C)

@[simp] theorem color_iterate (J : C) (n : ℕ) :
    R.color (R.next^[n] J) = R.color J := by
  induction n with
  | zero => rfl
  | succ n ih => rwa [iterate_succ_apply', R.color_next]

/-- One positive iterate already lies in the designated interior. -/
theorem iterate_mem_core (J : C) {x : X} (hx : x ∈ R.cell J) (n : ℕ) :
    (F (!(R.color J)))^[n + 1] x ∈ R.core (R.next^[n + 1] J) := by
  induction n with
  | zero => exact R.opposite_maps J hx
  | succ n ih =>
    rw [iterate_succ_apply' (F (!(R.color J))) (n+1) x, iterate_succ_apply' R.next (n+1) J]
    have h := R.opposite_maps (R.next^[n+1] J) (R.core_subset _ ih)
    simpa only [R.color_iterate] using h

private theorem common_mem_final_core {n : ℕ} (hn : 0 < n) {x : X}
    (hf : IsPeriodicPt (F false) n x) (hg : IsPeriodicPt (F true) n x)
    {J : C} (hx : x ∈ R.cell J) : x ∈ R.core (R.next^[n] J) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h : IsPeriodicPt (F (!(R.color J))) (k+1) x := by
    cases R.color J <;> assumption
  simpa only [h.eq] using R.iterate_mem_core J hx k

theorem cell_periodic_of_common {n : ℕ} (hn : 0 < n) {x : X}
    (hf : IsPeriodicPt (F false) n x) (hg : IsPeriodicPt (F true) n x)
    {J : C} (hx : x ∈ R.cell J) : IsPeriodicPt R.next n J :=
  (R.cell_unique hx (R.common_mem_final_core hn hf hg hx)).symm

theorem mem_core_of_common {n : ℕ} (hn : 0 < n) {x : X}
    (hf : IsPeriodicPt (F false) n x) (hg : IsPeriodicPt (F true) n x)
    {J : C} (hx : x ∈ R.cell J) : x ∈ R.core J := by
  simpa only [(R.cell_periodic_of_common hn hf hg hx).eq] using
    R.common_mem_final_core hn hf hg hx

/-- Marked points fixed by the own-colour branch and carried to the successor
by the opposite branch realize every successor period. -/
theorem mem_commonReturnExponents_iff (z : C → X)
    (own : ∀ J, F (R.color J) (z J) = z J)
    (opposite : ∀ J, F (!(R.color J)) (z J) = z (R.next J)) (n : ℕ) :
    n ∈ commonReturnExponents (F false) (F true) ↔
      0 < n ∧ ∃ J, IsPeriodicPt R.next n J := by
  constructor
  · rintro ⟨hn, x, hf, hg⟩
    obtain ⟨J, hx⟩ := R.cover x
    exact ⟨hn, J, R.cell_periodic_of_common hn hf hg hx⟩
  · rintro ⟨hn, J, hJ⟩
    have orbit (k : ℕ) : (F (!(R.color J)))^[k] (z J) = z (R.next^[k] J) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iterate_succ_apply', ih, iterate_succ_apply' R.next]
        simpa only [R.color_iterate] using opposite (R.next^[k] J)
    have ha := (show IsFixedPt (F (R.color J)) (z J) from own J).isPeriodicPt n
    have hb : IsPeriodicPt (F (!(R.color J))) n (z J) :=
      (orbit n).trans (congrArg z hJ.eq)
    refine ⟨hn, z J, ?_⟩
    cases h : R.color J <;> simp only [h, Bool.not_true, Bool.not_false] at ha hb <;>
      exact ⟨by assumption, by assumption⟩

/-- The two marked-point laws follow from the decoder section and the
intertwining identity at the unique fixed point of each section. -/
theorem marked_point_laws (s : C → X → X) (z : C → X)
    (fixed : ∀ J, s J (z J) = z J)
    (unique : ∀ J x, s J x = x → x = z J)
    (section_law : ∀ J x, F (R.color J) (s J x) = x)
    (intertwine : ∀ J x, F (!(R.color J)) (s J x) =
      s (R.next J) (F (!(R.color J)) x)) :
    (∀ J, F (R.color J) (z J) = z J) ∧
      ∀ J, F (!(R.color J)) (z J) = z (R.next J) := by
  constructor
  · intro J
    simpa only [fixed] using section_law J (z J)
  · intro J
    apply unique
    simpa only [fixed] using (intertwine J (z J)).symm

end ReturnCells

/-- Assign one cycle of length `d` for each `d ∈ D` to each of the two
colours. Even and odd indices alternate along the resulting `2*m` cells. -/
theorem exists_alternatingSuccessor (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d)
    (hne : D.Nonempty) :
    ∃ m > 0, ∃ P : Equiv.Perm (Fin (2*m)),
      (∀ j, (P j).val % 2 = j.val % 2) ∧
        ∀ n, (∃ j, IsPeriodicPt P n j) ↔ ∃ d ∈ D, d ∣ n := by
  classical
  letI (d : D) : NeZero d.val := ⟨(hpos _ d.property).ne'⟩
  let S := (d : D) × ZMod d.val
  let m := Fintype.card S
  let e : S × Fin 2 ≃ Fin (2*m) :=
    ((Equiv.prodCongr (Fintype.equivFin S) (Equiv.refl (Fin 2))).trans
      finProdFinEquiv).trans (finCongr (Nat.mul_comm m 2))
  let spin : Equiv.Perm S :=
    Equiv.sigmaCongrRight fun d => Equiv.addRight (1 : ZMod d.val)
  let P := e.symm.trans ((Equiv.prodCongr spin (Equiv.refl (Fin 2))).trans e)
  have step (s : S) (b : Fin 2) : P (e (s, b)) = e (spin s, b) := by simp [P]
  have iter (n : ℕ) (d : D) (a : ZMod d.val) (b : Fin 2) :
      (P : Fin (2*m) → Fin (2*m))^[n] (e (⟨d,a⟩, b)) =
        e (⟨d, a + n⟩, b) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply', ih, step]
      change e (⟨d,(a + n) + 1⟩, b) = _
      simp [add_assoc]
  obtain ⟨d₀, h₀⟩ := hne
  haveI : Nonempty S := ⟨⟨⟨d₀, h₀⟩, 0⟩⟩
  refine ⟨m, Fintype.card_pos, P, ?_, ?_⟩
  · intro j
    obtain ⟨⟨s,b⟩, rfl⟩ := e.surjective j
    rw [step]
    change (b.val + 2 * _) % 2 = (b.val + 2 * _) % 2
    simp
  · intro n
    constructor
    · rintro ⟨j, hj⟩
      obtain ⟨⟨⟨d,a⟩, b⟩, rfl⟩ := e.surjective j
      have heq := e.injective ((iter n d a b).symm.trans hj.eq)
      have ha : a + (n : ZMod d.val) = a :=
        (show Injective (Sigma.mk (β := fun d : D => ZMod d.val) d) from sigma_mk_injective) (congrArg Prod.fst heq)
      exact ⟨d.val, d.property, (ZMod.natCast_eq_zero_iff _ _).mp (add_eq_left.mp ha)⟩
    · rintro ⟨d, hd, hdvd⟩
      let t : D := ⟨d, hd⟩
      refine ⟨e (⟨t,0⟩, 0), ?_⟩
      change P^[n] _ = _
      rw [iter, (ZMod.natCast_eq_zero_iff n d).mpr hdvd, add_zero]

end CommutingIntervalSimplified
