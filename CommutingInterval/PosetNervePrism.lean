import CommutingInterval.PosetNerve

open CategoryTheory CategoryTheory.SimplicialObject
open SimplexCategory Simplicial Opposite

namespace CommutingInterval.PosetNerve

universe u

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

private def mixedObjMonotone (f k : P →o Q) (hf : ∀ x, f x ≤ k x)
    {n : ℕ} (i : Fin (n + 1)) (q : ComposableArrows P n) :
    Monotone (fun j : Fin (n + 2) =>
      if j ≤ i.castSucc then f (q.obj (i.predAbove j))
      else k (q.obj (i.predAbove j))) := by
  intro a b hab
  change (if a ≤ i.castSucc then f (q.obj (i.predAbove a))
    else k (q.obj (i.predAbove a))) ≤
      (if b ≤ i.castSucc then f (q.obj (i.predAbove b))
      else k (q.obj (i.predAbove b)))
  by_cases ha : a ≤ i.castSucc
  · by_cases hb : b ≤ i.castSucc
    · simp only [if_pos ha, if_pos hb]
      exact f.monotone (q.monotone (i.predAboveOrderHom.monotone hab))
    · simp only [if_pos ha, if_neg hb]
      exact (f.monotone (q.monotone
        (i.predAboveOrderHom.monotone hab))).trans (hf _)
  · have hb : ¬b ≤ i.castSucc := fun hb => ha (hab.trans hb)
    simp only [if_neg ha, if_neg hb]
    exact k.monotone (q.monotone (i.predAboveOrderHom.monotone hab))

private noncomputable def mixedArrow (f k : P →o Q)
    (hf : ∀ x, f x ≤ k x) {n : ℕ} (i : Fin (n + 1))
    (q : ComposableArrows P n) : ComposableArrows Q (n + 1) where
  obj j := if j ≤ i.castSucc then f (q.obj (i.predAbove j))
    else k (q.obj (i.predAbove j))
  map h := homOfLE (mixedObjMonotone f k hf i q (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private noncomputable def nerveOrderHomotopy (f k : P →o Q)
    (hf : ∀ x, f x ≤ k x) :
    Homotopy (nerveOrderHom P Q f) (nerveOrderHom P Q k) where
  h i := TypeCat.ofHom (mixedArrow f k hf i)
  h_zero_comp_δ_zero n := by
    ext q j
    change (mixedArrow f k hf (0 : Fin (n + 1)) q).obj
      ((0 : Fin (n + 2)).succAbove j) = k (q.obj j)
    simp [mixedArrow, Fin.predAbove, Fin.succAbove]
  h_last_comp_δ_last n := by
    ext q j
    change (mixedArrow f k hf (Fin.last n) q).obj
      ((Fin.last (n + 1)).succAbove j) = f (q.obj j)
    have hj : j ≤ Fin.last n := Fin.le_last j
    have hj' : j.castSucc ≤ (Fin.last n).castSucc :=
      Fin.castSucc_le_castSucc_iff.mpr hj
    simp [mixedArrow, Fin.succAbove_last_apply,
      Fin.predAbove_castSucc_of_le _ _ hj, hj']
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    ext q a
    change (mixedArrow f k hf j.succ q).obj (i.castSucc.succAbove a) =
      (mixedArrow f k hf j ((CategoryTheory.nerve P).δ i q)).obj a
    simp only [mixedArrow, CategoryTheory.nerve.δ_obj]
    have hside : i.castSucc.succAbove a ≤ j.succ.castSucc ↔
        a ≤ j.castSucc := by
      by_cases hai : a < i
      · rw [Fin.succAbove_of_castSucc_lt _ _
          (Fin.castSucc_lt_castSucc_iff.mpr hai)]
        constructor
        · intro _
          exact hai.le.trans hij
        · intro haj
          simp only [Fin.le_iff_val_le_val, Fin.val_castSucc,
            Fin.val_succ] at haj ⊢
          omega
      · rw [Fin.succAbove_of_le_castSucc _ _
          (Fin.castSucc_le_castSucc_iff.mpr (Fin.not_lt.mp hai))]
        simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
        omega
    have hindex :
        j.succ.predAbove (i.castSucc.succAbove a) =
          i.succAbove (j.predAbove a) := by
      have h := SimplexCategory.δ_comp_σ_of_le hij
      simpa [SimplexCategory.δ, SimplexCategory.σ] using
        congrArg (fun e => e.toOrderHom a) h
    rw [hindex]
    by_cases hs : a ≤ j.castSucc
    · rw [if_pos hs, if_pos (hside.mpr hs)]
    · rw [if_neg hs, if_neg (fun h => hs (hside.mp h))]
  h_succ_comp_δ_castSucc_succ j := by
    ext q a
    change (mixedArrow f k hf j.succ q).obj
        (j.castSucc.succ.succAbove a) =
      (mixedArrow f k hf j.castSucc q).obj
        (j.castSucc.succ.succAbove a)
    simp only [mixedArrow]
    have hside :
        j.castSucc.succ.succAbove a ≤ j.succ.castSucc ↔
          j.castSucc.succ.succAbove a ≤ j.castSucc.castSucc := by
      by_cases ha : a ≤ j.castSucc
      · rw [Fin.succAbove_of_succ_le _ _
          (Fin.succ_le_succ_iff.mpr ha)]
        simp only [Fin.le_iff_val_le_val, Fin.val_castSucc,
          Fin.val_succ] at ha ⊢
        omega
      · have hpa : j.castSucc.succ ≤ a.castSucc := by
          simp only [Fin.le_iff_val_le_val, Fin.val_succ,
            Fin.val_castSucc] at ha ⊢
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ hpa]
        simp only [Fin.le_iff_val_le_val, Fin.val_succ,
          Fin.val_castSucc] at ha ⊢
        omega
    have hleft :
        j.succ.predAbove (j.castSucc.succ.succAbove a) = a := by
      have h := SimplexCategory.δ_comp_σ_self (i := j.succ)
      have ha := congrArg (fun e => e.toOrderHom a) h
      change j.succ.predAbove ((j.succ).castSucc.succAbove a) = a at ha
      simpa only [Fin.succ_castSucc] using ha
    have hright :
        j.castSucc.predAbove (j.castSucc.succ.succAbove a) = a := by
      have h := SimplexCategory.δ_comp_σ_succ (i := j.castSucc)
      have ha := congrArg (fun e => e.toOrderHom a) h
      change j.castSucc.predAbove (j.castSucc.succ.succAbove a) = a at ha
      exact ha
    rw [hleft, hright]
    by_cases hs : j.castSucc.succ.succAbove a ≤ j.castSucc.castSucc
    · rw [if_pos hs, if_pos (hside.mpr hs)]
    · rw [if_neg hs, if_neg (fun h => hs (hside.mp h))]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    ext q a
    change (mixedArrow f k hf j.castSucc q).obj (i.succ.succAbove a) =
      (mixedArrow f k hf j ((CategoryTheory.nerve P).δ i q)).obj a
    simp only [mixedArrow, CategoryTheory.nerve.δ_obj]
    have hside : i.succ.succAbove a ≤ j.castSucc.castSucc ↔
        a ≤ j.castSucc := by
      by_cases hai : a ≤ i
      · rw [Fin.succAbove_of_succ_le _ _
          (Fin.succ_le_succ_iff.mpr hai)]
        simp only [Fin.castSucc_le_castSucc_iff]
      · have hia : i.succ ≤ a.castSucc := by
          simp only [Fin.le_iff_val_le_val, Fin.val_succ,
            Fin.val_castSucc] at hai ⊢
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ hia]
        simp only [Fin.succ_le_castSucc_iff]
        constructor
        · intro haj
          exact (hai (haj.le.trans hji.le)).elim
        · intro haj
          exact (hai (haj.trans hji.le)).elim
    have hindex :
        j.castSucc.predAbove (i.succ.succAbove a) =
          i.succAbove (j.predAbove a) := by
      have h := SimplexCategory.δ_comp_σ_of_gt hji
      simpa [SimplexCategory.δ, SimplexCategory.σ] using
        congrArg (fun e => e.toOrderHom a) h
    rw [hindex]
    by_cases hs : a ≤ j.castSucc
    · rw [if_pos hs, if_pos (hside.mpr hs)]
    · rw [if_neg hs, if_neg (fun h => hs (hside.mp h))]
  h_comp_σ_castSucc_of_le i j hij := by
    ext q a
    change (mixedArrow f k hf j q).obj (i.castSucc.predAbove a) =
      (mixedArrow f k hf j.succ ((CategoryTheory.nerve P).σ i q)).obj a
    simp only [mixedArrow, CategoryTheory.nerve.σ_obj]
    have hside : i.castSucc.predAbove a ≤ j.castSucc ↔
        a ≤ j.succ.castSucc := by
      by_cases ha : i.castSucc.castSucc < a
      · rw [Fin.predAbove_of_castSucc_lt _ _ ha,
          Fin.pred_le_iff]
        simp only [Fin.succ_castSucc]
      · have ha' : a ≤ i.castSucc.castSucc := Fin.not_lt.mp ha
        rw [Fin.predAbove_of_le_castSucc _ _ ha']
        have hij' : i.castSucc.castSucc ≤ j.castSucc.castSucc :=
          Fin.castSucc_le_castSucc_iff.mpr
            (Fin.castSucc_le_castSucc_iff.mpr hij)
        constructor
        · intro _
          simpa only [Fin.succ_castSucc] using
            ha'.trans (hij'.trans j.castSucc.castSucc_le_succ)
        · intro _
          exact (Fin.castPred_le_iff _).2 (ha'.trans hij')
    have hindex :
        j.predAbove (i.castSucc.predAbove a) =
          i.predAbove (j.succ.predAbove a) := by
      have h := SimplexCategory.σ_comp_σ hij
      simpa [SimplexCategory.σ] using
        congrArg (fun e => e.toOrderHom a) h
    rw [hindex]
    by_cases hs : a ≤ j.succ.castSucc
    · rw [if_pos hs, if_pos (hside.mpr hs)]
    · rw [if_neg hs, if_neg (fun h => hs (hside.mp h))]
  h_comp_σ_succ_of_lt i j hji := by
    ext q a
    change (mixedArrow f k hf j q).obj (i.succ.predAbove a) =
      (mixedArrow f k hf j.castSucc ((CategoryTheory.nerve P).σ i q)).obj a
    simp only [mixedArrow, CategoryTheory.nerve.σ_obj]
    have hside : i.succ.predAbove a ≤ j.castSucc ↔
        a ≤ j.castSucc.castSucc := by
      by_cases ha : i.succ.castSucc < a
      · rw [Fin.predAbove_of_castSucc_lt _ _ ha,
          Fin.pred_le_iff]
        have hbound : j.castSucc.succ ≤ i.succ.castSucc := by
          simpa only [Fin.succ_castSucc] using
            Fin.succ_le_succ_iff.mpr
              (Fin.castSucc_le_castSucc_iff.mpr hji)
        constructor
        · intro haj
          exact (Fin.not_le.mpr ha (haj.trans hbound)).elim
        · intro haj
          exact (Fin.not_le.mpr ha
            (haj.trans (j.castSucc.castSucc_le_succ.trans hbound))).elim
      · rw [Fin.predAbove_of_le_castSucc _ _ (Fin.not_lt.mp ha),
          Fin.castPred_le_iff]
    have hindex :
        j.predAbove (i.succ.predAbove a) =
          i.predAbove (j.castSucc.predAbove a) := by
      have h := SimplexCategory.σ_comp_σ hji
      symm
      simpa [SimplexCategory.σ] using
        congrArg (fun e => e.toOrderHom a) h
    rw [hindex]
    by_cases hs : a ≤ j.castSucc.castSucc
    · rw [if_pos hs, if_pos (hside.mpr hs)]
    · rw [if_neg hs, if_neg (fun h => hs (hside.mp h))]

/-- Pointwise-comparable order maps induce the standard simplicial prism
between their categorical nerve maps. -/
noncomputable def nerveOrderHomotopy_of_le (f k : P →o Q)
    (hf : ∀ x, f x ≤ k x) :
    Homotopy (nerveOrderHom P Q f) (nerveOrderHom P Q k) :=
  nerveOrderHomotopy f k hf

end CommutingInterval.PosetNerve


