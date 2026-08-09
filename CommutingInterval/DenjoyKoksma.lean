import CommutingInterval.Denjoy
import CommutingInterval.Kopell
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Data.ZMod.Units

/-!
# The finite Denjoy--Koksma estimate used by the interval argument

This file isolates the arithmetic and ordered-variation part of Denjoy's
inequality.  The proof uses a monotone semiconjugacy and finite rational grids;
it does not invoke invariant measures or an ergodic theorem.
-/

namespace CommutingInterval

open Function Set Filter
open scoped BigOperators Topology

/-- A good rational approximation places the first `q` positive rotation
times, after deck translations, one in each cell of the uniform `q`-grid. -/
structure GoodRotationCoding (alpha : ℝ) (q : ℕ) where
  q_pos : 0 < q
  time : Equiv.Perm (Fin q)
  deck : Fin q → ℤ
  cell_mem : ∀ k : Fin q,
    (k : ℝ) / q <
        (((time k : Fin q) : ℕ) + 1 : ℝ) * alpha - deck k ∧
      (((time k : Fin q) : ℕ) + 1 : ℝ) * alpha - deck k <
        ((k : ℕ) + 1 : ℝ) / q

/-- Arithmetic closest-return coding for a reduced good approximation. -/
theorem exists_goodRotationCoding
    {alpha : ℝ} {p : ℤ} {q : ℕ}
    (hq : 0 < q)
    (hcop : Nat.Coprime p.natAbs q)
    (hne : alpha ≠ (p : ℝ) / q)
    (happrox : |alpha - (p : ℝ) / q| < 1 / (q : ℝ) ^ 2) :
    Nonempty (GoodRotationCoding alpha q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hcopInt : IsCoprime p (q : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using hcop
  let u : (ZMod q)ˣ := ZMod.unitOfIsCoprime p hcopInt
  let mulU : ZMod q ≃ ZMod q :=
    { toFun := fun z ↦ z * (u : ZMod q)
      invFun := fun z ↦ z * (u⁻¹ : (ZMod q)ˣ)
      left_inv := fun z ↦ by simp
      right_inv := fun z ↦ by simp }
  let delta : ℝ := alpha - (p : ℝ) / q
  have hdelta_ne : delta ≠ 0 := sub_ne_zero.mpr hne
  let eps : ℤ := if 0 < delta then 0 else -1
  let cellPerm : Equiv.Perm (Fin q) :=
    (ZMod.finEquiv q).toEquiv.trans <|
      (Equiv.addRight (1 : ZMod q)).trans <|
        mulU.trans <|
          (Equiv.addRight (eps : ZMod q)).trans
            (ZMod.finEquiv q).symm.toEquiv
  let time : Equiv.Perm (Fin q) := cellPerm.symm
  have hcongr' (k : Fin q) :
      (ZMod.finEquiv q (time k) + 1) * (p : ZMod q) + (eps : ZMod q) =
        ZMod.finEquiv q k := by
    have hk := cellPerm.apply_symm_apply k
    change (ZMod.finEquiv q).symm
      ((ZMod.finEquiv q (time k) + 1) * (u : ZMod q) + (eps : ZMod q)) = k at hk
    have hk' := congrArg (fun z : Fin q ↦ ZMod.finEquiv q z) hk
    simpa [u] using hk'
  have hcongr (k : Fin q) :
      ((((time k : ℕ) + 1 : ℤ) * p + eps : ℤ) : ZMod q) =
        ((((k : ℕ) : ℤ)) : ZMod q) := by
    have hfin (i : Fin q) : ZMod.finEquiv q i = (i : ZMod q) := by
      cases q with
      | zero => simp at hq
      | succ n =>
          apply Fin.ext
          simpa [ZMod.finEquiv] using
            (ZMod.val_natCast_of_lt i.isLt).symm
    simpa [hfin] using hcongr' k
  have hdvd (k : Fin q) :
      (q : ℤ) ∣ (((time k : ℕ) + 1 : ℤ) * p + eps - (k : ℕ)) := by
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub
      ((k : ℕ) : ℤ)
      (((time k : ℕ) + 1 : ℤ) * p + eps) q).mp (hcongr k).symm
  let deck : Fin q → ℤ := fun k ↦ Classical.choose (hdvd k)
  have hdeck (k : Fin q) :
      (((time k : ℕ) + 1 : ℤ) * p + eps - (k : ℕ)) =
        (q : ℤ) * deck k := by
    exact Classical.choose_spec (hdvd k)
  refine ⟨⟨hq, time, deck, ?_⟩⟩
  intro k
  let j : ℕ := (time k : ℕ) + 1
  have hjcast : (j : ℝ) = ((time k : ℕ) : ℝ) + 1 := by simp [j]
  rw [← hjcast]
  have hjpos : 0 < j := by simp [j]
  have hjle : j ≤ q := by
    dsimp [j]
    omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hjqR : (j : ℝ) ≤ q := by exact_mod_cast hjle
  have hsmall : (j : ℝ) * |delta| < 1 / (q : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left happrox hjR
    have hnonneg : (0 : ℝ) ≤ 1 / (q : ℝ) ^ 2 := by positivity
    calc
      (j : ℝ) * |delta| < (j : ℝ) * (1 / (q : ℝ) ^ 2) := by
        simpa [delta] using hmul
      _ ≤ (q : ℝ) * (1 / (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hjqR hnonneg
      _ = 1 / (q : ℝ) := by field_simp
  have hdeckR :
      (j : ℝ) * (p : ℝ) + (eps : ℝ) - (k : ℝ) =
        (q : ℝ) * (deck k : ℝ) := by
    exact_mod_cast hdeck k
  have halpha : alpha = (p : ℝ) / q + delta := by
    simp [delta]
  have hsplit : (((k : ℕ) + 1 : ℝ) / (q : ℝ)) =
      (k : ℝ) / (q : ℝ) + 1 / (q : ℝ) := by
    ring
  by_cases hdelta : 0 < delta
  · have heps : eps = 0 := by simp [eps, hdelta]
    have hjdelta_pos : 0 < (j : ℝ) * delta := mul_pos hjR hdelta
    have hjdelta_lt : (j : ℝ) * delta < 1 / (q : ℝ) := by
      simpa [abs_of_pos hdelta] using hsmall
    have hcoord :
        (j : ℝ) * alpha - deck k =
          (k : ℝ) / q + (j : ℝ) * delta := by
      rw [halpha]
      rw [heps] at hdeckR
      field_simp [hqR.ne'] at hdeckR ⊢
      ring_nf at hdeckR ⊢
      linarith
    constructor
    · rw [hcoord]
      linarith
    · rw [hcoord]
      rw [hsplit]
      linarith
  · have hdelta_neg : delta < 0 := lt_of_le_of_ne (le_of_not_gt hdelta) hdelta_ne
    have heps : eps = -1 := by simp [eps, hdelta]
    have hjdelta_neg : (j : ℝ) * delta < 0 := mul_neg_of_pos_of_neg hjR hdelta_neg
    have hjdelta_lower : -(1 / (q : ℝ)) < (j : ℝ) * delta := by
      have := hsmall
      rw [abs_of_neg hdelta_neg] at this
      linarith
    have hcoord :
        (j : ℝ) * alpha - deck k =
          ((k : ℕ) + 1 : ℝ) / q + (j : ℝ) * delta := by
      rw [halpha]
      rw [heps] at hdeckR
      field_simp [hqR.ne'] at hdeckR ⊢
      ring_nf at hdeckR ⊢
      linarith
    constructor
    · rw [hcoord]
      rw [hsplit]
      linarith
    · rw [hcoord]
      linarith

/-- A chosen right inverse of a surjective degree-one monotone lift, normalized
with `fract` so that it itself commutes with integral deck translations. -/
noncomputable def degreeOneSection
    (H : CircleDeg1Lift) (hsurj : Function.Surjective H) : ℝ → ℝ :=
  fun s ↦ Classical.choose (hsurj (Int.fract s)) + (⌊s⌋ : ℝ)

theorem degreeOneSection_rightInverse
    (H : CircleDeg1Lift) (hsurj : Function.Surjective H) :
    Function.RightInverse (degreeOneSection H hsurj) H := by
  intro s
  rw [degreeOneSection, H.map_add_int]
  rw [Classical.choose_spec (hsurj (Int.fract s))]
  simp only [Int.fract]
  ring

theorem degreeOneSection_strictMono
    (H : CircleDeg1Lift) (hsurj : Function.Surjective H) :
    StrictMono (degreeOneSection H hsurj) := by
  intro s t hst
  apply lt_of_not_ge
  intro hge
  have := H.monotone hge
  rw [degreeOneSection_rightInverse H hsurj,
    degreeOneSection_rightInverse H hsurj] at this
  exact (not_le_of_gt hst) this

theorem degreeOneSection_add_int
    (H : CircleDeg1Lift) (hsurj : Function.Surjective H)
    (s : ℝ) (k : ℤ) :
    degreeOneSection H hsurj (s + k) =
      degreeOneSection H hsurj s + k := by
  simp only [degreeOneSection, Int.fract_add_intCast,
    Int.floor_add_intCast, Int.cast_add]
  ring

/-- The logarithmic derivative of a differentiable degree-one lift is
one-periodic. -/
theorem logDeriv_periodic_of_circleDeg1Lift
    (F : CircleDeg1Lift) (hFdiff : Differentiable ℝ F) :
    Function.Periodic (fun x : ℝ ↦ Real.log (deriv F x)) 1 := by
  intro x
  apply congrArg Real.log
  have hfun : (fun y : ℝ ↦ F (y + 1)) = (fun y : ℝ ↦ F y + 1) := by
    funext y
    exact F.map_add_one y
  have hderiv := congrArg (fun g : ℝ → ℝ ↦ deriv g x) hfun
  simpa only [deriv_comp_add_const, deriv_add_const] using hderiv

/-- A one-periodic BV function has at most twice its one-period variation on
any interval of length one.  The factor two avoids choosing where the interval
crosses the integral deck cut. -/
theorem periodic_bv_window_bound
    {ell : ℝ → ℝ}
    (hperiod : Function.Periodic ell 1)
    (hBV : BoundedVariationOn ell (Set.Icc (0 : ℝ) 1))
    (a : ℝ) :
    BoundedVariationOn ell (Set.Icc a (a + 1)) ∧
      (eVariationOn ell (Set.Icc a (a + 1))).toReal ≤
        2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
  have hshift (m : ℤ) :
      eVariationOn ell (Set.Icc (m : ℝ) ((m : ℝ) + 1)) =
        eVariationOn ell (Set.Icc (0 : ℝ) 1) := by
    let φ : ℝ → ℝ := fun x ↦ x + (m : ℝ)
    have hφmono : MonotoneOn φ (Set.Icc (0 : ℝ) 1) := by
      intro x _ y _ hxy
      dsimp [φ]
      linarith
    have himage : φ '' Set.Icc (0 : ℝ) 1 =
        Set.Icc (m : ℝ) ((m : ℝ) + 1) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        constructor <;> dsimp [φ] <;> linarith [hx.1, hx.2]
      · intro hy
        refine ⟨y - (m : ℝ), ?_, ?_⟩
        · constructor <;> linarith [hy.1, hy.2]
        · dsimp [φ]
          ring
    have hcomp : ell ∘ φ = ell := by
      funext x
      simpa [φ, Function.comp_apply] using (hperiod.int_mul m) x
    have hvar := eVariationOn.comp_eq_of_monotoneOn
      (t := Set.Icc (0 : ℝ) 1) ell φ hφmono
    rw [hcomp, himage] at hvar
    exact hvar.symm
  let m : ℤ := ⌊a⌋
  have hma : (m : ℝ) ≤ a := by
    simpa [m] using Int.floor_le a
  have ham : a < (m : ℝ) + 1 := by
    simpa [m] using Int.lt_floor_add_one a
  have hsub : Set.Icc a (a + 1) ⊆
      Set.Icc (m : ℝ) ((m : ℝ) + 2) := by
    intro x hx
    constructor
    · exact hma.trans hx.1
    · linarith [hx.2, ham]
  have hadd := eVariationOn.Icc_add_Icc ell
    (s := Set.univ) (a := (m : ℝ)) (b := (m : ℝ) + 1)
    (c := (m : ℝ) + 2) (by linarith) (by linarith) (by simp)
  simp only [Set.univ_inter] at hadd
  have hm0 := hshift m
  have hm1 :
      eVariationOn ell (Set.Icc ((m : ℝ) + 1) ((m : ℝ) + 2)) =
        eVariationOn ell (Set.Icc (0 : ℝ) 1) := by
    convert hshift (m + 1) using 1 <;> norm_num [Int.cast_add] <;> ring
  have hwhole :
      eVariationOn ell (Set.Icc (m : ℝ) ((m : ℝ) + 2)) =
        eVariationOn ell (Set.Icc (0 : ℝ) 1) +
          eVariationOn ell (Set.Icc (0 : ℝ) 1) := by
    calc
      eVariationOn ell (Set.Icc (m : ℝ) ((m : ℝ) + 2)) =
          eVariationOn ell (Set.Icc (m : ℝ) ((m : ℝ) + 1)) +
            eVariationOn ell (Set.Icc ((m : ℝ) + 1) ((m : ℝ) + 2)) := hadd.symm
      _ = eVariationOn ell (Set.Icc (0 : ℝ) 1) +
            eVariationOn ell (Set.Icc (0 : ℝ) 1) := by rw [hm0, hm1]
  have hwholeBV :
      BoundedVariationOn ell (Set.Icc (m : ℝ) ((m : ℝ) + 2)) := by
    rw [BoundedVariationOn, hwhole]
    exact ENNReal.add_ne_top.mpr ⟨hBV, hBV⟩
  refine ⟨hwholeBV.mono hsub, ?_⟩
  calc
    (eVariationOn ell (Set.Icc a (a + 1))).toReal ≤
        (eVariationOn ell (Set.Icc (m : ℝ) ((m : ℝ) + 2))).toReal :=
      ENNReal.toReal_mono hwholeBV (eVariationOn.mono ell hsub)
    _ = (eVariationOn ell (Set.Icc (0 : ℝ) 1) +
          eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by rw [hwhole]
    _ = (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal +
          (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal :=
      ENNReal.toReal_add hBV hBV
    _ = 2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by ring

/-- Variation bound for two finite rows of points that interlace from left to
right.  Extending the interlaced row constantly after its final endpoint lets
us use the general ordered-pairs estimate without any indexing artifacts. -/
private theorem interlaced_sum_abs_le_window_variation
    {ell : ℝ → ℝ} {q : ℕ} (hq : 0 < q)
    (a b : Fin q → ℝ) (hi : ℝ)
    (hab : ∀ k, a k ≤ b k)
    (hnext : ∀ (k : ℕ) (hk : k + 1 < q),
      b ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ a ⟨k + 1, hk⟩)
    (hlast : ∀ (k : ℕ) (hk : k < q), ¬k + 1 < q → b ⟨k, hk⟩ ≤ hi)
    (hBV : BoundedVariationOn ell
      (Set.Icc (a ⟨0, hq⟩) hi)) :
    (∑ k : Fin q, |ell (b k) - ell (a k)|) ≤
      (eVariationOn ell (Set.Icc (a ⟨0, hq⟩) hi)).toReal := by
  let a' : ℕ → ℝ := fun k ↦ if hk : k < q then a ⟨k, hk⟩ else hi
  let b' : ℕ → ℝ := fun k ↦ if hk : k < q then b ⟨k, hk⟩ else hi
  let z : ℕ → ℝ := fun j ↦ if Even j then a' (j / 2) else b' (j / 2)
  have zeven (k : ℕ) : z (2 * k) = a' k := by
    simp [z]
  have zodd (k : ℕ) : z (2 * k + 1) = b' k := by
    simp only [z, if_neg (Nat.not_even_two_mul_add_one k)]
    congr 1
    omega
  have hzmono : Monotone z := monotone_nat_of_le_succ fun j ↦ by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · rw [zeven, zodd]
      by_cases hk : k < q
      · simpa [a', b', hk] using hab ⟨k, hk⟩
      · simp [a', b', hk]
    · rw [zodd]
      have heq : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [heq, zeven]
      by_cases hk1 : k + 1 < q
      · have hk : k < q := by omega
        simpa [a', b', hk, hk1] using hnext k hk1
      · by_cases hk : k < q
        · simpa [a', b', hk, hk1] using hlast k hk hk1
        · simp [a', b', hk, hk1]
  have hz0 : z 0 = a ⟨0, hq⟩ := by simp [z, a', hq]
  have hzlast : z (2 * q) = hi := by simp [z, a']
  have hzmem : ∀ j ≤ 2 * q, z j ∈ Set.Icc (a ⟨0, hq⟩) hi := by
    intro j hj
    constructor
    · rw [← hz0]
      exact hzmono (Nat.zero_le j)
    · rw [← hzlast]
      exact hzmono hj
  have hsum := sum_abs_orderedPairs_le_variation hBV hzmono hzmem
  rw [Finset.sum_range] at hsum
  simp_rw [zodd, zeven] at hsum
  simpa [a', b'] using hsum

/-- The actual `q`-term orbit sum differs from the uniform grid sum based at
its semiconjugacy coordinate by at most one window variation. -/
theorem orbitSum_sub_gridSum_le
    (F : CircleDeg1Liftˣ) (H : CircleDeg1Lift) (alpha : ℝ)
    (hsemiconj : Function.Semiconj H (F : CircleDeg1Lift)
      (CircleDeg1Lift.translate (Multiplicative.ofAdd alpha)))
    (hsurj : Function.Surjective H)
    {ell : ℝ → ℝ}
    (hperiod : Function.Periodic ell 1)
    (hBV : BoundedVariationOn ell (Set.Icc (0 : ℝ) 1))
    {q : ℕ} (coding : GoodRotationCoding alpha q) (x : ℝ) :
    |(∑ j ∈ Finset.Icc 1 q, ell (((F : CircleDeg1Lift) ^ j) x)) -
        ∑ k : Fin q,
          ell (degreeOneSection H hsurj (H x + (k : ℝ) / q))| ≤
      2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
  let K : ℝ → ℝ := degreeOneSection H hsurj
  let a : Fin q → ℝ := fun k ↦ K (H x + (k : ℝ) / q)
  let b : Fin q → ℝ := fun k ↦
    ((F : CircleDeg1Lift) ^ ((coding.time k : ℕ) + 1)) x - coding.deck k
  let hi : ℝ := K (H x + 1)
  have horbitH (n : ℕ) :
      H (((F : CircleDeg1Lift) ^ n) x) = (n : ℝ) * alpha + H x := by
    rw [CircleDeg1Lift.coe_pow]
    simpa [CircleDeg1Lift.translate_iterate,
      CircleDeg1Lift.translate_apply] using
        (hsemiconj.iterate_right n) x
  have haH (k : Fin q) : H (a k) = H x + (k : ℝ) / q := by
    exact degreeOneSection_rightInverse H hsurj _
  have hbH (k : Fin q) :
      H (b k) = H x +
        ((((coding.time k : Fin q) : ℕ) + 1 : ℝ) * alpha - coding.deck k) := by
    dsimp [b]
    rw [H.map_sub_int, horbitH]
    push_cast
    ring
  have hbetween (k : Fin q) :
      a k < b k ∧
        b k < K (H x + (((k : ℕ) + 1 : ℝ) / q)) := by
    have hcell := coding.cell_mem k
    have hlower : H (a k) < H (b k) := by
      rw [haH, hbH]
      linarith [hcell.1]
    have hupperH : H (b k) <
        H (K (H x + (((k : ℕ) + 1 : ℝ) / q))) := by
      rw [hbH, degreeOneSection_rightInverse H hsurj]
      linarith [hcell.2]
    constructor
    · apply lt_of_not_ge
      intro hba
      exact (not_le_of_gt hlower) (H.monotone hba)
    · apply lt_of_not_ge
      intro hab'
      exact (not_le_of_gt hupperH) (H.monotone hab')
  have hab : ∀ k, a k ≤ b k := fun k ↦ (hbetween k).1.le
  have hnext : ∀ (k : ℕ) (hk : k + 1 < q),
      b ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ a ⟨k + 1, hk⟩ := by
    intro k hk
    simpa [a, K] using (hbetween ⟨k, Nat.lt_of_succ_lt hk⟩).2.le
  have hlast : ∀ (k : ℕ) (hk : k < q), ¬k + 1 < q →
      b ⟨k, hk⟩ ≤ hi := by
    intro k hk hklast
    have hkq : k + 1 = q := by omega
    apply (hbetween ⟨k, hk⟩).2.le.trans_eq
    dsimp [hi]
    congr 2
    have hkqR : (k : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hkq
    rw [hkqR]
    exact div_self (by exact_mod_cast coding.q_pos.ne')
  have hhi : hi = a ⟨0, coding.q_pos⟩ + 1 := by
    simpa [hi, a, K] using
      degreeOneSection_add_int H hsurj (H x) 1
  have hwindow := periodic_bv_window_bound hperiod hBV (a ⟨0, coding.q_pos⟩)
  have hwindowBV : BoundedVariationOn ell
      (Set.Icc (a ⟨0, coding.q_pos⟩) hi) := by
    rw [hhi]
    exact hwindow.1
  have hinterlace := interlaced_sum_abs_le_window_variation
    coding.q_pos a b hi hab hnext hlast hwindowBV
  have hvarWindow :
      (eVariationOn ell (Set.Icc (a ⟨0, coding.q_pos⟩) hi)).toReal ≤
        2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
    rw [hhi]
    exact hwindow.2
  let fsum : ℕ → ℝ := fun j ↦ ell (((F : CircleDeg1Lift) ^ j) x)
  have hIcc : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by
    ext j
    simp
  have hpositiveSum :
      (∑ j ∈ Finset.Icc 1 q, fsum j) =
        ∑ i : Fin q, fsum ((i : ℕ) + 1) := by
    rw [hIcc, ← Finset.sum_Ico_add fsum 0 q 1,
      Nat.Ico_zero_eq_range, Finset.sum_range]
    simp only [add_comm]
  have hpermute :
    (∑ i : Fin q, fsum ((i : ℕ) + 1)) =
        ∑ k : Fin q, fsum ((coding.time k : ℕ) + 1) := by
    symm
    exact Equiv.sum_comp coding.time
      (fun i : Fin q ↦ fsum ((i : ℕ) + 1))
  have hdeckPeriod (k : Fin q) :
      fsum ((coding.time k : ℕ) + 1) = ell (b k) := by
    dsimp [fsum, b]
    simpa using
      ((hperiod.sub_int_mul_eq (x :=
        ((F : CircleDeg1Lift) ^ ((coding.time k : ℕ) + 1)) x)
        (coding.deck k)).symm)
  have horbitSum :
      (∑ j ∈ Finset.Icc 1 q,
          ell (((F : CircleDeg1Lift) ^ j) x)) =
        ∑ k : Fin q, ell (b k) := by
    change (∑ j ∈ Finset.Icc 1 q, fsum j) = _
    rw [hpositiveSum, hpermute]
    exact Finset.sum_congr rfl fun k _ ↦ hdeckPeriod k
  rw [horbitSum]
  change |(∑ k : Fin q, ell (b k)) - (∑ k : Fin q, ell (a k))| ≤ _
  calc
    |(∑ k : Fin q, ell (b k)) - (∑ k : Fin q, ell (a k))| =
        |∑ k : Fin q, (ell (b k) - ell (a k))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k : Fin q, |ell (b k) - ell (a k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (eVariationOn ell
          (Set.Icc (a ⟨0, coding.q_pos⟩) hi)).toReal := hinterlace
    _ ≤ 2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := hvarWindow

/-- Uniform `q`-grid sums based at two phases differ by at most one window
variation. -/
theorem gridSum_sub_gridSum_le
    (H : CircleDeg1Lift) (hsurj : Function.Surjective H)
    {ell : ℝ → ℝ}
    (hperiod : Function.Periodic ell 1)
    (hBV : BoundedVariationOn ell (Set.Icc (0 : ℝ) 1))
    {q : ℕ} (hq : 0 < q) (s t : ℝ) :
    |(∑ k : Fin q,
          ell (degreeOneSection H hsurj (s + (k : ℝ) / q))) -
        ∑ k : Fin q,
          ell (degreeOneSection H hsurj (t + (k : ℝ) / q))| ≤
      2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
  let K : ℝ → ℝ := degreeOneSection H hsurj
  let G : ℝ → ℝ := fun v ↦ ∑ k : Fin q, ell (K (v + (k : ℝ) / q))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcycle (g : ℕ → ℝ) (hend : g q = g 0) :
      (∑ k ∈ Finset.range q, g (k + 1)) =
        ∑ k ∈ Finset.range q, g k := by
    rw [Finset.range_eq_Ico]
    calc
      (∑ k ∈ Finset.Ico 0 q, g (k + 1)) =
          ∑ k ∈ Finset.Ico 1 (q + 1), g k :=
        by simpa [add_comm] using Finset.sum_Ico_add g 0 q 1
      _ = (∑ k ∈ Finset.Ico 1 q, g k) + g q :=
        Finset.sum_Ico_succ_top (by omega) g
      _ = g 0 + ∑ k ∈ Finset.Ico 1 q, g k := by rw [hend]; ring
      _ = ∑ k ∈ Finset.Ico 0 q, g k :=
        (Finset.sum_eq_sum_Ico_succ_bot hq g).symm
  have hGperiod : Function.Periodic G (1 / (q : ℝ)) := by
    intro v
    let g : ℕ → ℝ := fun k ↦ ell (K (v + (k : ℝ) / q))
    have hend : g q = g 0 := by
      dsimp [g]
      calc
        ell (K (v + (q : ℝ) / q)) = ell (K (v + 1)) := by
          rw [div_self hqR.ne']
        _ = ell (K v + 1) := by
          congr 1
          simpa [K] using degreeOneSection_add_int H hsurj v 1
        _ = ell (K v) := hperiod (K v)
        _ = ell (K (v + (((0 : ℕ) : ℝ)) / q)) := by norm_num
    have hcyc := hcycle g hend
    change (∑ k : Fin q, ell (K
      (v + 1 / (q : ℝ) + (k : ℝ) / q))) =
        ∑ k : Fin q, ell (K (v + (k : ℝ) / q))
    rw [Finset.sum_range, Finset.sum_range] at hcyc
    calc
      (∑ k : Fin q, ell (K
          (v + 1 / (q : ℝ) + (k : ℝ) / q))) =
          ∑ k : Fin q, g ((k : ℕ) + 1) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [g]
        apply congrArg (fun y : ℝ ↦ ell (K y))
        push_cast
        ring
      _ = ∑ k : Fin q, g (k : ℕ) := hcyc
      _ = ∑ k : Fin q, ell (K (v + (k : ℝ) / q)) := by rfl
  let r : ℤ := ⌊(q : ℝ) * (t - s)⌋
  let u : ℝ := t - (r : ℝ) / q
  have hrle : (r : ℝ) ≤ (q : ℝ) * (t - s) := by
    simpa [r] using Int.floor_le ((q : ℝ) * (t - s))
  have hrupper : (q : ℝ) * (t - s) < (r : ℝ) + 1 := by
    simpa [r] using Int.lt_floor_add_one ((q : ℝ) * (t - s))
  have hsu : s ≤ u := by
    have hdiv : (r : ℝ) / q ≤ t - s := by
      apply (div_le_iff₀ hqR).2
      nlinarith
    dsimp [u]
    linarith
  have hus : u < s + 1 / (q : ℝ) := by
    have hdiv : t - s < ((r : ℝ) + 1) / q := by
      apply (lt_div_iff₀ hqR).2
      nlinarith
    have hsplit : ((r : ℝ) + 1) / q =
        (r : ℝ) / q + 1 / (q : ℝ) := by ring
    rw [hsplit] at hdiv
    dsimp [u]
    linarith
  have hGt : G t = G u := by
    have ht : t = u + (r : ℝ) * (1 / (q : ℝ)) := by
      dsimp [u]
      ring
    rw [ht]
    exact (hGperiod.int_mul r) u
  let a : Fin q → ℝ := fun k ↦ K (s + (k : ℝ) / q)
  let b : Fin q → ℝ := fun k ↦ K (u + (k : ℝ) / q)
  let hi : ℝ := K (s + 1)
  have hKstrict : StrictMono K := degreeOneSection_strictMono H hsurj
  have hab : ∀ k, a k ≤ b k := by
    intro k
    apply hKstrict.monotone
    dsimp [a, b]
    linarith
  have hnext : ∀ (k : ℕ) (hk : k + 1 < q),
      b ⟨k, Nat.lt_of_succ_lt hk⟩ ≤ a ⟨k + 1, hk⟩ := by
    intro k hk
    apply hKstrict.monotone
    dsimp [a, b]
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hsplit : ((k : ℝ) + 1) / (q : ℝ) =
        (k : ℝ) / (q : ℝ) + 1 / (q : ℝ) := by ring
    rw [hsplit]
    linarith [hus]
  have hlast : ∀ (k : ℕ) (hk : k < q), ¬k + 1 < q →
      b ⟨k, hk⟩ ≤ hi := by
    intro k hk hklast
    have hkq : k + 1 = q := by omega
    apply hKstrict.monotone
    dsimp [b, hi]
    have hkqR : (k : ℝ) + 1 = (q : ℝ) := by exact_mod_cast hkq
    have hkfrac : (k : ℝ) / q = 1 - 1 / (q : ℝ) := by
      apply (eq_sub_iff_add_eq).2
      calc
        (k : ℝ) / q + 1 / (q : ℝ) = ((k : ℝ) + 1) / q := by ring
        _ = 1 := by rw [hkqR, div_self hqR.ne']
    rw [hkfrac]
    linarith [hus]
  have hhi : hi = a ⟨0, hq⟩ + 1 := by
    simpa [hi, a, K] using degreeOneSection_add_int H hsurj s 1
  have hwindow := periodic_bv_window_bound hperiod hBV (a ⟨0, hq⟩)
  have hwindowBV : BoundedVariationOn ell (Set.Icc (a ⟨0, hq⟩) hi) := by
    rw [hhi]
    exact hwindow.1
  have hinterlace := interlaced_sum_abs_le_window_variation
    hq a b hi hab hnext hlast hwindowBV
  have hvarWindow :
      (eVariationOn ell (Set.Icc (a ⟨0, hq⟩) hi)).toReal ≤
        2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
    rw [hhi]
    exact hwindow.2
  change |G s - G t| ≤ _
  rw [hGt]
  change |(∑ k : Fin q, ell (a k)) - (∑ k : Fin q, ell (b k))| ≤ _
  calc
    |(∑ k : Fin q, ell (a k)) - (∑ k : Fin q, ell (b k))| =
        |∑ k : Fin q, (ell (b k) - ell (a k))| := by
      rw [← abs_neg, neg_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ k : Fin q, |ell (b k) - ell (a k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ (eVariationOn ell (Set.Icc (a ⟨0, hq⟩) hi)).toReal := hinterlace
    _ ≤ 2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := hvarWindow

/-- Finite Denjoy inequality at the denominator of any reduced good rational
approximation. -/
theorem logDeriv_iterate_bound_of_goodRational
    (F : CircleDeg1Liftˣ)
    (hC1 : ContDiff ℝ 1 (F : CircleDeg1Lift))
    (hpos : ∀ x : ℝ, 0 < deriv (F : CircleDeg1Lift) x)
    (hBV : BoundedVariationOn
      (fun x : ℝ ↦ Real.log (deriv (F : CircleDeg1Lift) x))
      (Set.Icc (0 : ℝ) 1))
    (hirr : Irrational (F : CircleDeg1Lift).translationNumber)
    {r : ℚ}
    (hgood : |(F : CircleDeg1Lift).translationNumber - (r : ℝ)| <
      1 / (r.den : ℝ) ^ 2) :
    ∀ x : ℝ,
      |Real.log (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) x)| ≤
        6 * (eVariationOn
          (fun x : ℝ ↦ Real.log (deriv (F : CircleDeg1Lift) x))
          (Set.Icc (0 : ℝ) 1)).toReal := by
  let alpha : ℝ := (F : CircleDeg1Lift).translationNumber
  let R : CircleDeg1Liftˣ :=
    CircleDeg1Lift.translate (Multiplicative.ofAdd alpha)
  have htranslation :
      (F : CircleDeg1Lift).translationNumber =
        (R : CircleDeg1Lift).translationNumber := by
    simp [R, alpha, CircleDeg1Lift.translationNumber_translate]
  obtain ⟨H, hsemiconj⟩ :=
    CircleDeg1Lift.units_semiconj_of_translationNumber_eq htranslation
  have hsemiconj' : Function.Semiconj H (F : CircleDeg1Lift)
      (CircleDeg1Lift.translate (Multiplicative.ofAdd alpha)) := by
    simpa [R] using hsemiconj
  have hirrAlpha : Irrational alpha := by simpa [alpha] using hirr
  have hHdense : DenseRange H :=
    irrationalTranslation_semiconj_denseRange F H alpha hirrAlpha hsemiconj'
  have hHcont : Continuous H := H.monotone.continuous_of_denseRange hHdense
  have hHsurj : Function.Surjective H := H.continuous_iff_surjective.mp hHcont
  have hne : alpha ≠ (r.num : ℝ) / r.den := by
    simpa [Rat.cast_def] using hirrAlpha.ne_rat r
  have happrox : |alpha - (r.num : ℝ) / r.den| < 1 / (r.den : ℝ) ^ 2 := by
    simpa [alpha, Rat.cast_def] using hgood
  obtain ⟨coding⟩ := exists_goodRotationCoding
    r.den_pos r.reduced hne happrox
  let ell : ℝ → ℝ := fun y ↦ Real.log (deriv (F : CircleDeg1Lift) y)
  have hFdiff : Differentiable ℝ (F : CircleDeg1Lift) :=
    hC1.differentiable (by norm_num)
  have hellPeriod : Function.Periodic ell 1 :=
    logDeriv_periodic_of_circleDeg1Lift (F : CircleDeg1Lift) hFdiff
  have horbit (y : ℝ) :
      |(∑ j ∈ Finset.Icc 1 r.den,
          ell (((F : CircleDeg1Lift) ^ j) y)) -
        ∑ k : Fin r.den,
          ell (degreeOneSection H hHsurj
            (H y + (k : ℝ) / r.den))| ≤
        2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal :=
    orbitSum_sub_gridSum_le F H alpha hsemiconj' hHsurj
      hellPeriod hBV coding y
  have hgrid (s t : ℝ) :
      |(∑ k : Fin r.den,
          ell (degreeOneSection H hHsurj (s + (k : ℝ) / r.den))) -
        ∑ k : Fin r.den,
          ell (degreeOneSection H hHsurj (t + (k : ℝ) / r.den))| ≤
        2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal :=
    gridSum_sub_gridSum_le H hHsurj hellPeriod hBV r.den_pos s t
  have hlogIter (w : ℝ) :
      Real.log (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) w) =
        ∑ i ∈ Finset.range r.den,
          ell (((F : CircleDeg1Lift) ^ i) w) := by
    rw [deriv_iterate_eq_prod (fun _ _ ↦ hFdiff.differentiableAt)]
    rw [Real.log_prod (fun i _ ↦
      (hpos ((((F : CircleDeg1Lift) : ℝ → ℝ)^[i]) w)).ne')]
    simp only [ell, CircleDeg1Lift.coe_pow]
  have hIcc : Finset.Icc 1 r.den = Finset.Ico 1 (r.den + 1) := by
    ext j
    simp
  have hpositiveSum (y : ℝ) :
      (∑ j ∈ Finset.Icc 1 r.den,
          ell (((F : CircleDeg1Lift) ^ j) y)) =
        Real.log (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) (F y)) := by
    calc
      (∑ j ∈ Finset.Icc 1 r.den,
          ell (((F : CircleDeg1Lift) ^ j) y)) =
          ∑ i : Fin r.den,
            ell (((F : CircleDeg1Lift) ^ ((i : ℕ) + 1)) y) := by
        rw [hIcc, ← Finset.sum_Ico_add
          (fun j ↦ ell (((F : CircleDeg1Lift) ^ j) y)) 0 r.den 1,
          Nat.Ico_zero_eq_range, Finset.sum_range]
        simp only [add_comm]
      _ = ∑ i : Fin r.den,
          ell (((F : CircleDeg1Lift) ^ (i : ℕ)) (F y)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply congrArg ell
        rw [pow_succ]
        rfl
      _ = ∑ i ∈ Finset.range r.den,
          ell (((F : CircleDeg1Lift) ^ i) (F y)) := by
        rw [Finset.sum_range]
      _ = Real.log
          (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) (F y)) :=
        (hlogIter (F y)).symm
  have hiterCont : Continuous
      (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) :=
    hFdiff.continuous.iterate r.den
  have hiterDiff : Differentiable ℝ
      (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) :=
    hFdiff.iterate r.den
  obtain ⟨z, _hz, hzSlope⟩ := exists_deriv_eq_slope
    (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) (by norm_num : (0 : ℝ) < 1)
      hiterCont.continuousOn hiterDiff.differentiableOn
  have hiterMapOne :
      (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) 1 =
        (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) 0 + 1 := by
    rw [← CircleDeg1Lift.coe_pow]
    simpa using ((F : CircleDeg1Lift) ^ r.den).map_add_one 0
  have hzDeriv :
      deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) z = 1 := by
    rw [hzSlope, hiterMapOne]
    ring
  have hzLog :
      Real.log (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) z) = 0 := by
    rw [hzDeriv, Real.log_one]
  intro x
  let xpre : ℝ := (F⁻¹ : CircleDeg1Liftˣ) x
  let zpre : ℝ := (F⁻¹ : CircleDeg1Liftˣ) z
  let S : ℝ → ℝ := fun y ↦ ∑ j ∈ Finset.Icc 1 r.den,
    ell (((F : CircleDeg1Lift) ^ j) y)
  let A : ℝ → ℝ := fun y ↦ ∑ k : Fin r.den,
    ell (degreeOneSection H hHsurj (H y + (k : ℝ) / r.den))
  have hFxpre : F xpre = x := by simp [xpre]
  have hFzpre : F zpre = z := by simp [zpre]
  have hSx : S xpre =
      Real.log (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) x) := by
    simpa [S, hFxpre] using hpositiveSum xpre
  have hSz : S zpre = 0 := by
    rw [show S zpre = Real.log
      (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[r.den]) z) by
        simpa [S, hFzpre] using hpositiveSum zpre]
    exact hzLog
  have hSxA : |S xpre - A xpre| ≤
      2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
    simpa [S, A] using horbit xpre
  have hAA : |A xpre - A zpre| ≤
      2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
    simpa [A] using hgrid (H xpre) (H zpre)
  have hSzA : |A zpre - S zpre| ≤
      2 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
    simpa [S, A, abs_sub_comm] using horbit zpre
  rw [← hSx]
  have hdecomp : S xpre =
      (S xpre - A xpre) + (A xpre - A zpre) + (A zpre - S zpre) := by
    rw [hSz]
    ring
  rw [hdecomp]
  calc
    |(S xpre - A xpre) + (A xpre - A zpre) + (A zpre - S zpre)| ≤
        |(S xpre - A xpre) + (A xpre - A zpre)| +
          |A zpre - S zpre| := abs_add_le _ _
    _ ≤ (|S xpre - A xpre| + |A xpre - A zpre|) +
          |A zpre - S zpre| := by gcongr; exact abs_add_le _ _
    _ ≤ 6 * (eVariationOn ell (Set.Icc (0 : ℝ) 1)).toReal := by
      linarith

/-- Irrational reals admit a sequence of good rational approximations whose
reduced denominators tend to infinity. -/
theorem exists_goodRationalApproximants_den_tendsto
    {alpha : ℝ} (hirr : Irrational alpha) :
    ∃ r : ℕ → ℚ,
      Tendsto (fun n ↦ (r n).den) atTop atTop ∧
        ∀ n, |alpha - (r n : ℝ)| < 1 / ((r n).den : ℝ) ^ 2 := by
  let S : Set ℚ :=
    {q : ℚ | |alpha - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}
  have hSinf : S.Infinite := by
    simpa [S] using
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hirr
  have hboundedDen (N : ℕ) :
      {q : ℚ | q ∈ S ∧ q.den < N}.Finite := by
    let f : ℚ → ℤ × ℕ := fun q ↦ (q.num, q.den)
    let T : Set ℚ := {q : ℚ | q ∈ S ∧ q.den < N}
    have hinj : Function.Injective f := by
      intro a b hab
      simp only [f, Prod.mk_inj] at hab
      rw [← Rat.num_div_den a, ← Rat.num_div_den b, hab.1, hab.2]
    have himage : f '' T ⊆
        ⋃ (y : ℕ) (_ : y ∈ Set.Ico 1 N),
          Set.Icc (⌈(alpha - 1) * (y : ℝ)⌉)
              (⌊(alpha + 1) * (y : ℝ)⌋) ×ˢ ({y} : Set ℕ) := by
      intro nq hnq
      rcases hnq with ⟨q, hqT, rfl⟩
      have hqgood := hqT.1
      change |alpha - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 at hqgood
      have hdenpos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      have hdenone : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
      have hrecip : 1 / (q.den : ℝ) ^ 2 ≤ 1 := by
        rw [div_le_one₀ (sq_pos_of_pos hdenpos)]
        nlinarith
      have hclose : |alpha - (q : ℝ)| < 1 := hqgood.trans_le hrecip
      rcases abs_sub_lt_iff.mp hclose with ⟨hleft, hright⟩
      have qlower : alpha - 1 < (q : ℝ) := by linarith
      have qupper : (q : ℝ) < alpha + 1 := by linarith
      have hnum : (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := by
        exact_mod_cast (Rat.mul_den_eq_num q).symm
      have hnumLower : (alpha - 1) * (q.den : ℝ) < (q.num : ℝ) := by
        calc
          (alpha - 1) * (q.den : ℝ) < (q : ℝ) * (q.den : ℝ) :=
            mul_lt_mul_of_pos_right qlower hdenpos
          _ = (q.num : ℝ) := hnum.symm
      have hnumUpper : (q.num : ℝ) < (alpha + 1) * (q.den : ℝ) := by
        calc
          (q.num : ℝ) = (q : ℝ) * (q.den : ℝ) := hnum
          _ < (alpha + 1) * (q.den : ℝ) :=
            mul_lt_mul_of_pos_right qupper hdenpos
      have hnLower : ⌈(alpha - 1) * (q.den : ℝ)⌉ ≤ q.num :=
        Int.ceil_le.mpr hnumLower.le
      have hnUpper : q.num ≤ ⌊(alpha + 1) * (q.den : ℝ)⌋ :=
        Int.le_floor.mpr hnumUpper.le
      simp_rw [Set.mem_iUnion]
      refine ⟨q.den, ⟨q.pos, hqT.2⟩, ?_⟩
      simp only [Set.prod_singleton, Set.mem_image, Set.mem_Icc]
      exact ⟨q.num, ⟨hnLower, hnUpper⟩, rfl⟩
    change T.Finite
    refine (Set.Finite.subset ?_ himage).of_finite_image hinj.injOn
    exact Set.Finite.biUnion (Set.finite_Ico 1 N) fun y _ ↦
      Set.Finite.prod (Set.finite_Icc
        (⌈(alpha - 1) * (y : ℝ)⌉)
        (⌊(alpha + 1) * (y : ℝ)⌋)) (Set.finite_singleton y)
  have hexists (N : ℕ) : ∃ q ∈ S, N ≤ q.den := by
    by_contra hnone
    have hsub : S ⊆ {q : ℚ | q ∈ S ∧ q.den < N} := by
      intro q hq
      refine ⟨hq, Nat.lt_of_not_ge ?_⟩
      intro hden
      exact hnone ⟨q, hq, hden⟩
    exact hSinf ((hboundedDen N).subset hsub)
  let r : ℕ → ℚ := fun n ↦ Classical.choose (hexists n)
  have hrmem (n : ℕ) : r n ∈ S :=
    (Classical.choose_spec (hexists n)).1
  have hrden (n : ℕ) : n ≤ (r n).den :=
    (Classical.choose_spec (hexists n)).2
  refine ⟨r, ?_, ?_⟩
  · apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hrden n)
  · intro n
    exact hrmem n

/-- The complete return-time logarithmic derivative estimate, in the generic
`CircleDeg1Lift` language used by the orbit-line module. -/
theorem exists_logDeriv_bound_at_returnTimes
    (F : CircleDeg1Liftˣ)
    (hC1 : ContDiff ℝ 1 (F : CircleDeg1Lift))
    (hpos : ∀ x : ℝ, 0 < deriv (F : CircleDeg1Lift) x)
    (hBV : BoundedVariationOn
      (fun x : ℝ ↦ Real.log (deriv (F : CircleDeg1Lift) x))
      (Set.Icc (0 : ℝ) 1))
    (hirr : Irrational (F : CircleDeg1Lift).translationNumber) :
    ∃ q : ℕ → ℕ, Tendsto q atTop atTop ∧
      ∃ V : ℝ, ∀ n : ℕ, ∀ x : ℝ,
        |Real.log (deriv (((F : CircleDeg1Lift) : ℝ → ℝ)^[q n]) x)| ≤ V := by
  obtain ⟨r, hrden, hrgood⟩ :=
    exists_goodRationalApproximants_den_tendsto hirr
  refine ⟨fun n ↦ (r n).den, hrden,
    6 * (eVariationOn
      (fun x : ℝ ↦ Real.log (deriv (F : CircleDeg1Lift) x))
      (Set.Icc (0 : ℝ) 1)).toReal, ?_⟩
  intro n x
  exact logDeriv_iterate_bound_of_goodRational
    F hC1 hpos hBV hirr (hrgood n) x

end CommutingInterval
