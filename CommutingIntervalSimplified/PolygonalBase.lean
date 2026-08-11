import CommutingIntervalSimplified.Base

/-!
# Periodic polygonal paths

This file gives the standalone path vocabulary used by the periodic-rigidity
and periodic-fold arguments.  It depends only on the simplified base API and
Mathlib through that API.
-/

namespace CommutingIntervalSimplified

open Function Set

noncomputable section

/-- Two vertices are adjacent in a finite set of real parameters. -/
def AdjacentInFinset (vertices : Finset ℝ) (x y : ℝ) : Prop :=
  x ∈ vertices ∧ y ∈ vertices ∧ x < y ∧
    ∀ z ∈ vertices, ¬ (x < z ∧ z < y)

/--
A path is finite-piece affine with slopes of absolute value one on the
compact parameter interval `[a,b]`.
-/
def IsFinitePieceUnitSpeedOn (ψ : ℝ → I) (a b : ℝ) : Prop :=
  ∃ vertices : Finset ℝ,
    a ∈ vertices ∧
      b ∈ vertices ∧
      (∀ x ∈ vertices, x ∈ Set.Icc a b) ∧
      ∀ ⦃x y : ℝ⦄, AdjacentInFinset vertices x y →
        ∃ m c : ℝ, |m| = 1 ∧
          ∀ t ∈ Set.Icc x y, (ψ t : ℝ) = m * t + c

/--
A continuous onto locally polygonal unit-speed path with least positive
period `period`.
-/
def IsUnitSpeedPeriodicSurjection (ψ : ℝ → I) (period : ℝ) : Prop :=
  Continuous ψ ∧
    Surjective ψ ∧
    0 < period ∧
    (∀ t : ℝ, ψ (t + period) = ψ t) ∧
    (∀ r : ℝ, 0 < r → (∀ t : ℝ, ψ (t + r) = ψ t) → period ≤ r) ∧
    ∀ a b : ℝ, a < b → IsFinitePieceUnitSpeedOn ψ a b

namespace IsUnitSpeedPeriodicSurjection

variable {ψ : ℝ → I} {period : ℝ}

/-- A periodic unit-speed surjection is continuous. -/
theorem continuous (hψ : IsUnitSpeedPeriodicSurjection ψ period) : Continuous ψ :=
  hψ.1

/-- A periodic unit-speed surjection is onto the physical interval. -/
theorem surjective (hψ : IsUnitSpeedPeriodicSurjection ψ period) : Surjective ψ :=
  hψ.2.1

/-- Its designated least period is positive. -/
theorem period_pos (hψ : IsUnitSpeedPeriodicSurjection ψ period) : 0 < period :=
  hψ.2.2.1

/-- Its designated period is indeed a period. -/
theorem periodic (hψ : IsUnitSpeedPeriodicSurjection ψ period) :
    ∀ t : ℝ, ψ (t + period) = ψ t :=
  hψ.2.2.2.1

/-- Every positive period is at least the designated least period. -/
theorem least_positive_period (hψ : IsUnitSpeedPeriodicSurjection ψ period) :
    ∀ r : ℝ, 0 < r → (∀ t : ℝ, ψ (t + r) = ψ t) → period ≤ r :=
  hψ.2.2.2.2.1

/-- The path has a finite unit-speed affine subdivision on every compact interval. -/
theorem finitePieceOn (hψ : IsUnitSpeedPeriodicSurjection ψ period)
    {a b : ℝ} (hab : a < b) : IsFinitePieceUnitSpeedOn ψ a b :=
  hψ.2.2.2.2.2 a b hab

end IsUnitSpeedPeriodicSurjection

/-- Dilation of the parameter by `r` semiconjugates the path to `T`. -/
def DilationSemiconjugates (ψ : ℝ → I) (r : ℝ) (T : IntervalMap) : Prop :=
  ∀ t : ℝ, ψ (r * t) = T (ψ t)

end

end CommutingIntervalSimplified
