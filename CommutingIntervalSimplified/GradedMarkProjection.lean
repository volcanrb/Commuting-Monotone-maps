import CommutingIntervalSimplified.GradedCellGeometry

/-! # Reduction of the unfolded cell residue

The physical chart uses one integer residue modulo the product of two prime
powers. Reducing both CRT coordinates sends this integer to its ordinary
remainder modulo the coarse mesh density.
-/

namespace CommutingIntervalSimplified.GradedGeometry

open GradedCells

private theorem finEquiv_eq_cast {n : ℕ} [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    exact (Nat.mod_eq_of_lt i.isLt).symm

theorem residue_coordinates {v : Grade} (J : Cell v) :
    ((residue J).val : ZMod (5 ^ v.1)) = J.five ∧
    ((residue J).val : ZMod (7 ^ v.2)) = J.seven := by
  have h := (residues v).apply_symm_apply (J.five, J.seven)
  change ZMod.chineseRemainder (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _
    (by decide : Nat.Coprime 5 7))) (ZMod.finEquiv (M v) (residue J)) = _ at h
  rw [finEquiv_eq_cast] at h
  erw [map_natCast] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem residue_project_mod {u v : Grade} (ha : u.1 ≤ v.1) (hb : u.2 ≤ v.2)
    (J : Cell v) : (residue (project ha hb J)).val = (residue J).val % M u := by
  let K := project ha hb J
  have hf := congrArg (ZMod.castHom (pow_dvd_pow 5 ha) (ZMod (5 ^ u.1)))
    (residue_coordinates J).1
  have hs := congrArg (ZMod.castHom (pow_dvd_pow 7 hb) (ZMod (7 ^ u.2)))
    (residue_coordinates J).2
  rw [map_natCast] at hf hs
  have hm : (residue K).val ≡ (residue J).val [MOD M u] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _
      (by decide : Nat.Coprime 5 7)))).mp
      ⟨(ZMod.natCast_eq_natCast_iff _ _ _).mp ((residue_coordinates K).1.trans hf.symm),
       (ZMod.natCast_eq_natCast_iff _ _ _).mp ((residue_coordinates K).2.trans hs.symm)⟩
  exact (Nat.mod_eq_of_lt (residue K).isLt).symm.trans hm

/-- The fine residue differs from the coarse residue by an integral number
of turns in the coarse unfolded chart. -/
theorem residue_project_turns {u v : Grade} (ha : u.1 ≤ v.1) (hb : u.2 ≤ v.2)
    (J : Cell v) : ∃ m : ℕ, (residue J).val = (residue (project ha hb J)).val + M u * m := by
  refine ⟨(residue J).val / M u, ?_⟩
  rw [residue_project_mod]
  exact (Nat.mod_add_div _ _).symm

end CommutingIntervalSimplified.GradedGeometry
