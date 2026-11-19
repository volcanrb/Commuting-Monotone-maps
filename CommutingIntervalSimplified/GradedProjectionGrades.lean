import CommutingIntervalSimplified.GradedCellGeometry

/-! # Grade arithmetic for the elementary and composite projections -/

namespace CommutingIntervalSimplified.ConcreteProjection

open GradedCells GradedGeometry

abbrev up (w v : Grade) : Grade := (v.1 + w.1, v.2 + w.2)

def down (w v : Grade) : Cell (up w v) → Cell v :=
  project (Nat.le_add_right ..) (Nat.le_add_right ..)

def degree (w : Grade) : ℤ := M w
def density (v : Grade) : ℤ := 12 * (M v : ℤ)

theorem density_pos (v : Grade) : 0 < density v := by
  unfold density
  have hp := M_pos v
  positivity

theorem degree_pos (w : Grade) : 0 < degree w := by
  unfold degree
  exact_mod_cast M_pos w

theorem degree_odd (w : Grade) : Odd (degree w) := by
  simp only [degree, M, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact (show Odd (5:ℤ) by decide).pow.mul (show Odd (7:ℤ) by decide).pow

@[simp] theorem down_color (w v : Grade) (J : Cell (up w v)) : color (down w v J) = color J := rfl

theorem M_up (w v : Grade) : M (up w v) = M v * M w := by
  simp only [M, pow_add]
  ring

theorem density_up (w v : Grade) : density (up w v) = density v * degree w := by
  simp only [degree, density, M_up, Nat.cast_mul, mul_assoc]

end CommutingIntervalSimplified.ConcreteProjection
