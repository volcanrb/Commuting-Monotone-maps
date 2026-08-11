import CommutingIntervalSimplified.Defs
import CommutingIntervalSimplified.PiecewiseMonotoneBase
import CommutingIntervalSimplified.FactorBase
import CommutingIntervalSimplified.ConstantSlopeDynamics
import CommutingIntervalSimplified.IntrinsicTurns

/-!
# The finite joint postcritical set

This file follows the proof of manuscript Lemma `lem:finite-postcritical`.
The declarations are deliberately split at the mathematical load-bearing
points: exact intrinsic-vertex composition, the rectangular identity, the
tail-class argument, the affine-slope contradiction, and construction of a
finite common invariant hull.
-/

noncomputable section

namespace CommutingIntervalSimplified

open Function Set
open scoped BigOperators

/-! ## Truncated and full one-generator postcritical sets -/

/-- The first `m` forward images of the intrinsic vertex-value set. -/
def truncatedPostcriticalSet (T : IntervalMap) (m : ℕ) : Set I :=
  ⋃ i : ℕ, ⋃ (_hi : i < m), iterateMap T i '' criticalValues T

/-- The complete forward orbit of the intrinsic vertex-value set. -/
def oneGeneratorPostcriticalSet (T : IntervalMap) : Set I :=
  ⋃ i : ℕ, iterateMap T i '' criticalValues T

/-- The forward orbit of one point. -/
def forwardOrbit (T : IntervalMap) (x : I) : Set I :=
  Set.range fun n : ℕ ↦ iterateMap T n x

/-- Two points have tails which meet under iteration by `T`. -/
def TailEquivalent (T : IntervalMap) (x y : I) : Prop :=
  ∃ p q : ℕ, iterateMap T p x = iterateMap T q y

theorem tailEquivalent_refl (T : IntervalMap) (x : I) :
    TailEquivalent T x x := by
  exact ⟨0, 0, rfl⟩

theorem tailEquivalent_symm {T : IntervalMap} {x y : I}
    (h : TailEquivalent T x y) : TailEquivalent T y x := by
  rcases h with ⟨p, q, hpq⟩
  exact ⟨q, p, hpq.symm⟩

/-- A commuting map carries an `A`-tail class into an `A`-tail class. -/
theorem tailEquivalent_image_of_commute
    {A B : IntervalMap} (hcomm : Function.Commute A B)
    {x y : I} (hxy : TailEquivalent A x y) :
    TailEquivalent A (B x) (B y) := by
  rcases hxy with ⟨p, q, hpq⟩
  refine ⟨p, q, ?_⟩
  calc
    iterateMap A p (B x) = B (iterateMap A p x) :=
      hcomm.iterate_left p x
    _ = B (iterateMap A q y) := congrArg B hpq
    _ = iterateMap A q (B y) := (hcomm.iterate_left q y).symm

/-! ## Exact genuine-vertex composition -/

/-- Positive constant absolute slope rules out nondegenerate flat intervals. -/
theorem noFlatInterval_of_constantSlope
    {T : IntervalMap} {s : ℝ} (hs : 0 < s)
    (hT : HasConstantAbsoluteSlope T s) : ¬HasFlatInterval T := by
  exact hT.noFlatInterval hs

/-- Intrinsic endpoint-and-turn sets are finite for flat-free finite-piece PL maps. -/
theorem criticalDomain_finite
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hflat : ¬HasFlatInterval T) : (criticalDomain T).Finite := by
  exact vertexDomain_finite_of_finitePiecePL_noFlat hT hflat

/-- Intrinsic vertex-value sets are finite. -/
theorem criticalValues_finite
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hflat : ¬HasFlatInterval T) : (criticalValues T).Finite := by
  exact (criticalDomain_finite hT hflat).image T

/-- Exact intrinsic endpoint-and-turn composition, including endpoint fibres. -/
theorem criticalDomain_comp_exact
    {U T : IntervalMap}
    (hU : FinitePiecePL U) (hT : FinitePiecePL T)
    (hUflat : ¬HasFlatInterval U) (hTflat : ¬HasFlatInterval T) :
    criticalDomain (U ∘ T) =
      criticalDomain T ∪ T ⁻¹' criticalDomain U := by
  exact vertexDomain_comp_exact_of_finitePiecePL_noFlat
    hU hT hUflat hTflat

/--
The manuscript identity
`V(U ∘ T) = V(U) ∪ U(V(T))` for an onto inner map.
-/
theorem criticalValues_comp_exact
    {U T : IntervalMap}
    (hU : FinitePiecePL U) (hT : FinitePiecePL T)
    (hUflat : ¬HasFlatInterval U) (hTflat : ¬HasFlatInterval T)
    (hTonto : IsOnto T) :
    criticalValues (U ∘ T) =
      criticalValues U ∪ U '' criticalValues T := by
  exact vertexValues_comp_exact_of_finitePiecePL_noFlat
    hU hT hUflat hTflat hTonto

/-! The following elementary closure facts are kept local to this module.
They let the exact two-map composition theorem be iterated without adding
another public foundation layer. -/

private theorem finitePiecePL_comp_postcritical
    {U T : IntervalMap} (hU : FinitePiecePL U) (hT : FinitePiecePL T) :
    FinitePiecePL (U ∘ T) := by
  rcases hU with ⟨hUcont, pU, hpU⟩
  rcases hT with ⟨hTcont, pT, hpT⟩
  let wU : MonotonicityPartition U :=
    ⟨pU, fun _ _ hab => (hpU hab).isWeaklyMonotoneOn⟩
  let wT : MonotonicityPartition T :=
    ⟨pT, fun _ _ hab => (hpT hab).isWeaklyMonotoneOn⟩
  refine ⟨hUcont.comp hTcont, wT.compositionRefinement wU, ?_⟩
  intro a b hab
  obtain ⟨aT, bT, hTadj, hsource⟩ :=
    (wT.compositionRefinement_refines wU).adjacent_subset hab
  obtain ⟨mT, cT, hTformula⟩ := hpT hTadj
  obtain ⟨_hTweak, aU, bU, hUadj, hmaps⟩ :=
    wT.composition_cell hTcont wU hab
  obtain ⟨mU, cU, hUformula⟩ := hpU hUadj
  refine ⟨mU * mT, mU * cT + cU, ?_⟩
  intro x hx
  change (U (T x) : ℝ) = _
  rw [hUformula (T x) (hmaps hx), hTformula x (hsource hx)]
  ring

private theorem finitePiecePL_iterate_postcritical
    {T : IntervalMap} (hT : FinitePiecePL T) (n : ℕ) :
    FinitePiecePL (iterateMap T n) := by
  induction n with
  | zero =>
      refine ⟨continuous_id, RealPartition.trivial, ?_⟩
      intro a b _hab
      refine ⟨1, 0, ?_⟩
      intro x _hx
      simp [iterateMap]
  | succ n ih =>
      have hmap : iterateMap T (n + 1) = T ∘ iterateMap T n := by
        funext x
        exact Function.iterate_succ_apply' T n x
      rw [hmap]
      exact finitePiecePL_comp_postcritical hT ih

/-- Composition of continuous interval maps cannot create a flat interval
when neither factor has one. -/
private theorem noFlatInterval_comp_postcritical
    {U T : IntervalMap} (hUflat : ¬HasFlatInterval U)
    (hTflat : ¬HasFlatInterval T) (hTcont : Continuous T) :
    ¬HasFlatInterval (U ∘ T) := by
  rintro ⟨J, hJ, hcomp⟩
  have hnotconstant : ¬(∀ {x : I}, x ∈ J.carrier →
      ∀ {y : I}, y ∈ J.carrier → T x = T y) := by
    intro hconstant
    exact hTflat ⟨J, hJ, hconstant⟩
  push Not at hnotconstant
  obtain ⟨x, hx, y, hy, hxy⟩ := hnotconstant
  let K : ClosedSubinterval :=
    { left := min (T x) (T y)
      right := max (T x) (T y)
      left_le_right := min_le_max }
  have hK : K.Nondegenerate := by
    exact min_lt_max.mpr hxy
  have himage : Set.OrdConnected (T '' J.carrier) :=
    ((Set.ordConnected_Icc.isPreconnected.image T
      hTcont.continuousOn).ordConnected)
  have hKsubset : K.carrier ⊆ T '' J.carrier := by
    intro z hz
    change z ∈ Set.Icc (min (T x) (T y)) (max (T x) (T y)) at hz
    rcases le_total (T x) (T y) with hle | hle
    · exact (Set.ordConnected_iff.mp himage
        (T x) ⟨x, hx, rfl⟩ (T y) ⟨y, hy, rfl⟩ hle)
        (by simpa [min_eq_left hle, max_eq_right hle] using hz)
    · exact (Set.ordConnected_iff.mp himage
        (T y) ⟨y, hy, rfl⟩ (T x) ⟨x, hx, rfl⟩ hle)
        (by simpa [min_eq_right hle, max_eq_left hle] using hz)
  apply hUflat
  refine ⟨K, hK, ?_⟩
  intro z hz w hw
  obtain ⟨z₀, hz₀, rfl⟩ := hKsubset hz
  obtain ⟨w₀, hw₀, rfl⟩ := hKsubset hw
  simpa [Function.comp_apply] using hcomp hz₀ hw₀

private theorem noFlatInterval_id_postcritical :
    ¬HasFlatInterval (id : IntervalMap) := by
  rintro ⟨J, hJ, hflat⟩
  have heq := hflat J.left_mem_carrier J.right_mem_carrier
  exact hJ.ne (by simpa using heq)

private theorem noFlatInterval_iterate_postcritical
    {T : IntervalMap} (hTcont : Continuous T)
    (hTflat : ¬HasFlatInterval T) (n : ℕ) :
    ¬HasFlatInterval (iterateMap T n) := by
  induction n with
  | zero => simpa [iterateMap] using noFlatInterval_id_postcritical
  | succ n ih =>
      have hmap : iterateMap T (n + 1) = T ∘ iterateMap T n := by
        funext x
        exact Function.iterate_succ_apply' T n x
      rw [hmap]
      exact noFlatInterval_comp_postcritical hTflat ih
        (IntervalMap.continuous_iterate hTcont n)

private theorem truncatedPostcriticalSet_succ
    (T : IntervalMap) (n : ℕ) :
    truncatedPostcriticalSet T (n + 1) =
      truncatedPostcriticalSet T n ∪
        iterateMap T n '' criticalValues T := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hin, hxi⟩ := Set.mem_iUnion.mp hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hin) with hil | rfl
    · left
      apply Set.mem_iUnion.mpr
      refine ⟨i, Set.mem_iUnion.mpr ⟨hil, hxi⟩⟩
    · exact Or.inr hxi
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hin, hxi⟩ := Set.mem_iUnion.mp hi
      apply Set.mem_iUnion.mpr
      refine ⟨i, Set.mem_iUnion.mpr ⟨hin.trans_le (Nat.le_succ n), hxi⟩⟩
    · apply Set.mem_iUnion.mpr
      refine ⟨n, Set.mem_iUnion.mpr ⟨Nat.lt_succ_self n, hx⟩⟩

/-- Vertex values of an iterate are exactly its truncated postcritical set. -/
theorem criticalValues_iterate_exact
    {T : IntervalMap} (hT : FinitePiecePL T)
    (hflat : ¬HasFlatInterval T) (honto : IsOnto T)
    {m : ℕ} (hm : 0 < m) :
    criticalValues (iterateMap T m) = truncatedPostcriticalSet T m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hmzero : m = 0
      · subst m
        simp [truncatedPostcriticalSet, iterateMap]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
        have hmap : iterateMap T (m + 1) = iterateMap T m ∘ T := by
          funext x
          exact Function.iterate_succ_apply T m x
        calc
          criticalValues (iterateMap T (m + 1)) =
              criticalValues (iterateMap T m ∘ T) :=
            congrArg criticalValues hmap
          _ = criticalValues (iterateMap T m) ∪
                iterateMap T m '' criticalValues T :=
            criticalValues_comp_exact
              (finitePiecePL_iterate_postcritical hT m) hT
              (noFlatInterval_iterate_postcritical hT.continuous hflat m)
              hflat honto
          _ = truncatedPostcriticalSet T m ∪
                iterateMap T m '' criticalValues T := by rw [ih hmpos]
          _ = truncatedPostcriticalSet T (m + 1) :=
            (truncatedPostcriticalSet_succ T m).symm

/-! ## The rectangle and difference identities -/

/-- The rectangular vertex identity obtained from `A^m B^n = B^n A^m`. -/
theorem postcritical_rectangle
    {A B : IntervalMap}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAflat : ¬HasFlatInterval A) (hBflat : ¬HasFlatInterval B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hcomm : Function.Commute A B)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    truncatedPostcriticalSet A m ∪
        iterateMap A m '' truncatedPostcriticalSet B n =
      truncatedPostcriticalSet B n ∪
        iterateMap B n '' truncatedPostcriticalSet A m := by
  have hAvertices :
      criticalValues (iterateMap A m) = truncatedPostcriticalSet A m :=
    criticalValues_iterate_exact hA hAflat hAonto hm
  have hBvertices :
      criticalValues (iterateMap B n) = truncatedPostcriticalSet B n :=
    criticalValues_iterate_exact hB hBflat hBonto hn
  have hleft := criticalValues_comp_exact
    (finitePiecePL_iterate_postcritical hA m)
    (finitePiecePL_iterate_postcritical hB n)
    (noFlatInterval_iterate_postcritical hA.continuous hAflat m)
    (noFlatInterval_iterate_postcritical hB.continuous hBflat n)
    (IntervalMap.surjective_iterate hBonto n)
  have hright := criticalValues_comp_exact
    (finitePiecePL_iterate_postcritical hB n)
    (finitePiecePL_iterate_postcritical hA m)
    (noFlatInterval_iterate_postcritical hB.continuous hBflat n)
    (noFlatInterval_iterate_postcritical hA.continuous hAflat m)
    (IntervalMap.surjective_iterate hAonto m)
  rw [hAvertices, hBvertices] at hleft hright
  have hmaps : iterateMap A m ∘ iterateMap B n =
      iterateMap B n ∘ iterateMap A m := by
    funext x
    exact IntervalMap.commute_iterates hcomm m n x
  exact hleft.symm.trans ((congrArg criticalValues hmaps).trans hright)

/-- The one-step difference inclusion used in the tail-class argument. -/
theorem postcritical_difference
    {A B : IntervalMap}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAflat : ¬HasFlatInterval A) (hBflat : ¬HasFlatInterval B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hcomm : Function.Commute A B)
    {m : ℕ} (hm : 0 < m) :
    B '' truncatedPostcriticalSet A m \ truncatedPostcriticalSet A m ⊆
      iterateMap A m '' criticalValues B := by
  have hrectangle := postcritical_rectangle hA hB hAflat hBflat
    hAonto hBonto hcomm hm (n := 1) (by omega)
  have hBone : truncatedPostcriticalSet B 1 = criticalValues B := by
    simpa [truncatedPostcriticalSet, iterateMap] using
      (truncatedPostcriticalSet_succ B 0)
  have hBiterate : iterateMap B 1 = B := by
    funext x
    simp [iterateMap]
  rw [hBone, hBiterate] at hrectangle
  intro x hx
  have hxright :
      x ∈ criticalValues B ∪ B '' truncatedPostcriticalSet A m :=
    Or.inr hx.1
  have hxleft :
      x ∈ truncatedPostcriticalSet A m ∪
        iterateMap A m '' criticalValues B := by
    rw [hrectangle]
    exact hxright
  exact hxleft.resolve_left hx.2

/-! ## Tail classes and the affine-slope contradiction -/

/-- A positive constant-slope finite-piece PL map has finite fibres. -/
theorem finite_fibres_of_constantSlope
    {T : IntervalMap} {s : ℝ} (hs : 0 < s)
    (hT : HasConstantAbsoluteSlope T s) (y : I) :
    (T ⁻¹' {y}).Finite := by
  change {x : I | T x ∈ ({y} : Set I)}.Finite
  simpa only [Set.mem_singleton_iff] using hT.finite_fibre hs y

/-- The full one-generator postcritical set is the union of the forward
orbits of its finitely many intrinsic vertex-value seeds. -/
private theorem oneGeneratorPostcriticalSet_eq_biUnion_forwardOrbit
    (T : IntervalMap) :
    oneGeneratorPostcriticalSet T =
      ⋃ x ∈ criticalValues T, forwardOrbit T x := by
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    obtain ⟨x, hx, hxy⟩ := hn
    subst y
    exact Set.mem_iUnion.mpr ⟨x,
      Set.mem_iUnion.mpr ⟨hx, ⟨n, rfl⟩⟩⟩
  · intro hy
    obtain ⟨x, hy⟩ := Set.mem_iUnion.mp hy
    obtain ⟨hx, horbit⟩ := Set.mem_iUnion.mp hy
    obtain ⟨n, hny⟩ := horbit
    subst y
    exact Set.mem_iUnion.mpr ⟨n, ⟨x, hx, rfl⟩⟩

/-- A finite tail together with a finite forward orbit from that tail makes
the complete forward orbit finite. -/
private theorem forwardOrbit_finite_of_tail
    {T : IntervalMap} {x : I} {k : ℕ}
    (htail : (forwardOrbit T (iterateMap T k x)).Finite) :
    (forwardOrbit T x).Finite := by
  classical
  let K : Finset I := (Finset.range k).image fun n ↦ iterateMap T n x
  apply (K.finite_toSet.union htail).subset
  rintro y ⟨n, rfl⟩
  by_cases hnk : n < k
  · exact Or.inl (Finset.mem_image.mpr
      ⟨n, Finset.mem_range.mpr hnk, rfl⟩)
  · right
    refine ⟨n - k, ?_⟩
    change (T^[n - k]) ((T^[k]) x) = (T^[n]) x
    rw [← Function.iterate_add_apply]
    congr 1
    omega

/-- Every forward tail of an infinite forward orbit is infinite. -/
private theorem forwardOrbit_iterate_infinite
    {T : IntervalMap} {x : I}
    (hx : (forwardOrbit T x).Infinite) (k : ℕ) :
    (forwardOrbit T (iterateMap T k x)).Infinite := by
  intro htail
  exact hx (forwardOrbit_finite_of_tail htail)

/-- A positive-period point has finite forward orbit. -/
private theorem forwardOrbit_finite_of_periodic
    {T : IntervalMap} {x : I} {d : ℕ} (hd : 0 < d)
    (hperiodic : iterateMap T d x = x) :
    (forwardOrbit T x).Finite := by
  classical
  let K : Finset I := (Finset.range d).image fun n ↦ iterateMap T n x
  apply K.finite_toSet.subset
  rintro y ⟨n, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨n % d, Finset.mem_range.mpr (Nat.mod_lt n hd), ?_⟩
  exact (show Function.IsPeriodicPt T d x from hperiodic).iterate_mod_apply n

/-- Commutation identifies the orbit of an image with the image of the
original orbit. -/
private theorem forwardOrbit_image_of_commute
    {A B : IntervalMap} (hcomm : Function.Commute A B) (x : I) :
    forwardOrbit A (B x) = B '' forwardOrbit A x := by
  ext y
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨iterateMap A n x, ⟨n, rfl⟩,
      (hcomm.iterate_left n x).symm⟩
  · rintro ⟨z, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, hcomm.iterate_left n x⟩

/-- A finite-to-one commuting map sends an infinite forward orbit to an
infinite forward orbit. -/
private theorem forwardOrbit_image_infinite_of_commute
    {A B : IntervalMap} (hcomm : Function.Commute A B)
    (hBfibres : ∀ y : I, (B ⁻¹' {y}).Finite) {x : I}
    (hx : (forwardOrbit A x).Infinite) :
    (forwardOrbit A (B x)).Infinite := by
  rw [forwardOrbit_image_of_commute hcomm x]
  intro himage
  apply hx
  apply Set.Finite.of_finite_fibers B himage
  intro y _hy
  exact (hBfibres y).subset Set.inter_subset_right

/-- A truncated postcritical set lies in the full postcritical set. -/
private theorem truncatedPostcriticalSet_subset_oneGenerator
    (T : IntervalMap) (m : ℕ) :
    truncatedPostcriticalSet T m ⊆ oneGeneratorPostcriticalSet T := by
  intro x hx
  obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_hi, hx⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

/-- A point in the full postcritical set belongs to a positive truncation. -/
private theorem exists_positive_truncation_of_mem_postcritical
    {T : IntervalMap} {x : I}
    (hx : x ∈ oneGeneratorPostcriticalSet T) :
    ∃ m : ℕ, 0 < m ∧ x ∈ truncatedPostcriticalSet T m := by
  obtain ⟨i, v, hv, hiv⟩ := Set.mem_iUnion.mp hx
  refine ⟨i + 1, by omega, ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, Set.mem_iUnion.mpr ⟨by omega, ?_⟩⟩
  exact ⟨v, hv, hiv⟩

/-- If a postcritical point has infinite `A`-orbit, then its image under the
commuting finite-to-one map `B` is again `A`-postcritical.  Otherwise the
rectangle difference formula supplies preimages from the same finite seed
set at arbitrarily large depths, forcing periodicity. -/
private theorem image_mem_postcritical_of_infiniteOrbit
    {A B : IntervalMap}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAflat : ¬HasFlatInterval A) (hBflat : ¬HasFlatInterval B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hcomm : Function.Commute A B)
    (hVBfinite : (criticalValues B).Finite)
    (hBfibres : ∀ y : I, (B ⁻¹' {y}).Finite)
    {x : I} (hxpost : x ∈ oneGeneratorPostcriticalSet A)
    (hxinfinite : (forwardOrbit A x).Infinite) :
    B x ∈ oneGeneratorPostcriticalSet A := by
  classical
  have hBxinfinite : (forwardOrbit A (B x)).Infinite :=
    forwardOrbit_image_infinite_of_commute hcomm hBfibres hxinfinite
  by_contra hBxpost
  obtain ⟨m₀, hm₀pos, hxm₀⟩ :=
    exists_positive_truncation_of_mem_postcritical hxpost
  let N : ℕ → ℕ := fun k ↦ m₀ + k
  have hNpos (k : ℕ) : 0 < N k := by
    dsimp [N]
    omega
  have hxN (k : ℕ) : x ∈ truncatedPostcriticalSet A (N k) := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxm₀
    obtain ⟨him₀, hiimage⟩ := Set.mem_iUnion.mp hi
    apply Set.mem_iUnion.mpr
    refine ⟨i, Set.mem_iUnion.mpr ⟨?_, hiimage⟩⟩
    dsimp [N]
    omega
  have hpreimage (k : ℕ) :
      B x ∈ iterateMap A (N k) '' criticalValues B := by
    apply postcritical_difference hA hB hAflat hBflat
      hAonto hBonto hcomm (hNpos k)
    constructor
    · exact ⟨x, hxN k, rfl⟩
    · intro htruncated
      exact hBxpost
        (truncatedPostcriticalSet_subset_oneGenerator A (N k) htruncated)
  let pick : ℕ → {v // v ∈ criticalValues B} := fun k ↦
    ⟨Classical.choose (hpreimage k),
      (Classical.choose_spec (hpreimage k)).1⟩
  have hpick (k : ℕ) : iterateMap A (N k) (pick k) = B x :=
    (Classical.choose_spec (hpreimage k)).2
  letI : Finite {v // v ∈ criticalValues B} := hVBfinite.to_subtype
  obtain ⟨k, l, hklne, hpickeq⟩ :=
    Finite.exists_ne_map_eq_of_infinite pick
  have hperiodic_of_ordered {k l : ℕ} (hkl : k < l)
      (hpickeq : pick k = pick l) :
      ∃ d : ℕ, 0 < d ∧ iterateMap A d (B x) = B x := by
    refine ⟨l - k, Nat.sub_pos_of_lt hkl, ?_⟩
    change (A^[l - k]) (B x) = B x
    calc
      (A^[l - k]) (B x) =
          (A^[l - k]) ((A^[N k]) (pick k)) :=
        congrArg (A^[l - k]) (hpick k).symm
      _ = (A^[l - k + N k]) (pick k) :=
        (Function.iterate_add_apply A (l - k) (N k) (pick k)).symm
      _ = (A^[N l]) (pick l) := by
        have hexp : l - k + N k = N l := by
          dsimp [N]
          omega
        rw [hexp, hpickeq]
      _ = B x := hpick l
  rcases lt_or_gt_of_ne hklne with hkl | hlk
  · obtain ⟨d, hd, hperiodic⟩ :=
      hperiodic_of_ordered hkl hpickeq
    exact hBxinfinite (forwardOrbit_finite_of_periodic hd hperiodic)
  · obtain ⟨d, hd, hperiodic⟩ :=
      hperiodic_of_ordered hlk hpickeq.symm
    exact hBxinfinite (forwardOrbit_finite_of_periodic hd hperiodic)

/--
If the `A`-postcritical set were infinite, finitely many seed tails and the
action of `B` on their tail classes would produce a periodic tail class.
-/
theorem infinite_postcritical_yields_tail_cycle
    {A B : IntervalMap} {a b : ℝ}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (ha : 1 < a) (hb : 1 < b)
    (hcomm : Function.Commute A B)
    (hinfinite : (oneGeneratorPostcriticalSet A).Infinite) :
    ∃ w : I, w ∈ oneGeneratorPostcriticalSet A ∧
      (forwardOrbit A w).Infinite ∧
      ∃ r p q : ℕ, 0 < r ∧
        iterateMap A p (iterateMap B r w) = iterateMap A q w := by
  classical
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hAflat : ¬HasFlatInterval A := hAslope.noFlatInterval ha0
  have hBflat : ¬HasFlatInterval B := hBslope.noFlatInterval hb0
  have hVAfinite : (criticalValues A).Finite :=
    criticalValues_finite hA hAflat
  have hVBfinite : (criticalValues B).Finite :=
    criticalValues_finite hB hBflat
  have hBfibres : ∀ y : I, (B ⁻¹' {y}).Finite :=
    finite_fibres_of_constantSlope hb0 hBslope
  have hseed : ∃ w : I, w ∈ criticalValues A ∧
      (forwardOrbit A w).Infinite := by
    by_contra hseed
    apply hinfinite
    rw [oneGeneratorPostcriticalSet_eq_biUnion_forwardOrbit]
    apply hVAfinite.biUnion
    intro w hw
    by_contra hwfinite
    exact hseed ⟨w, hw, hwfinite⟩
  obtain ⟨w₀, hw₀vertex, hw₀orbit⟩ := hseed
  have hw₀post : w₀ ∈ oneGeneratorPostcriticalSet A := by
    apply Set.mem_iUnion.mpr
    exact ⟨0, ⟨w₀, hw₀vertex, by simp [iterateMap]⟩⟩
  have hstates : ∀ n : ℕ,
      iterateMap B n w₀ ∈ oneGeneratorPostcriticalSet A ∧
        (forwardOrbit A (iterateMap B n w₀)).Infinite := by
    intro n
    induction n with
    | zero =>
        simpa [iterateMap] using And.intro hw₀post hw₀orbit
    | succ n ih =>
        have hpost :
            B (iterateMap B n w₀) ∈ oneGeneratorPostcriticalSet A :=
          image_mem_postcritical_of_infiniteOrbit
            hA hB hAflat hBflat hAonto hBonto hcomm
            hVBfinite hBfibres ih.1 ih.2
        have horbit :
            (forwardOrbit A (B (iterateMap B n w₀))).Infinite :=
          forwardOrbit_image_infinite_of_commute hcomm hBfibres ih.2
        have hstep : iterateMap B (n + 1) w₀ =
            B (iterateMap B n w₀) := by
          exact Function.iterate_succ_apply' B n w₀
        rw [hstep]
        exact ⟨hpost, horbit⟩
  have hrepresent : ∀ n : ℕ, ∃ k : ℕ, ∃ v : I,
      v ∈ criticalValues A ∧
        iterateMap A k v = iterateMap B n w₀ := by
    intro n
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hstates n).1
    obtain ⟨v, hv, hkv⟩ := hk
    exact ⟨k, v, hv, hkv⟩
  choose exponent seed hseedVertex hseedRep using hrepresent
  let stateSeed : ℕ → {v // v ∈ criticalValues A} := fun n ↦
    ⟨seed n, hseedVertex n⟩
  letI : Finite {v // v ∈ criticalValues A} := hVAfinite.to_subtype
  obtain ⟨i, j, hijne, hseedEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite stateSeed
  have hordered {i j : ℕ} (hij : i < j)
      (hseedEq : stateSeed i = stateSeed j) :
      ∃ w : I, w ∈ oneGeneratorPostcriticalSet A ∧
        (forwardOrbit A w).Infinite ∧
        ∃ r p q : ℕ, 0 < r ∧
          iterateMap A p (iterateMap B r w) = iterateMap A q w := by
    let w : I := iterateMap B i w₀
    refine ⟨w, (hstates i).1, (hstates i).2,
      j - i, exponent i, exponent j, Nat.sub_pos_of_lt hij, ?_⟩
    have hseedValue : seed i = seed j := congrArg Subtype.val hseedEq
    change (A^[exponent i]) ((B^[j - i]) ((B^[i]) w₀)) =
      (A^[exponent j]) ((B^[i]) w₀)
    calc
      (A^[exponent i]) ((B^[j - i]) ((B^[i]) w₀)) =
          (A^[exponent i]) ((B^[j - i + i]) w₀) :=
        congrArg (A^[exponent i])
          (Function.iterate_add_apply B (j - i) i w₀).symm
      _ = (A^[exponent i]) ((B^[j]) w₀) := by
        have hj : j - i + i = j := by omega
        rw [hj]
      _ = (A^[exponent i]) ((A^[exponent j]) (seed j)) :=
        congrArg (A^[exponent i]) (hseedRep j).symm
      _ = (A^[exponent i + exponent j]) (seed j) :=
        (Function.iterate_add_apply A (exponent i) (exponent j)
          (seed j)).symm
      _ = (A^[exponent j + exponent i]) (seed i) := by
        rw [Nat.add_comm (exponent i) (exponent j), hseedValue]
      _ = (A^[exponent j]) ((A^[exponent i]) (seed i)) :=
        Function.iterate_add_apply A (exponent j) (exponent i) (seed i)
      _ = (A^[exponent j]) ((B^[i]) w₀) :=
        congrArg (A^[exponent j]) (hseedRep i)
  rcases lt_or_gt_of_ne hijne with hij | hji
  · exact hordered hij hseedEq
  · exact hordered hji hseedEq.symm

/--
Equality on an infinite `A`-orbit forces equality of the absolute affine
slopes on one common affine cell.
-/
private theorem constantSlope_scale_eq_of_eqOn_infinite
    {F G : IntervalMap} {f g : ℝ}
    (hF : HasConstantAbsoluteSlope F f)
    (hG : HasConstantAbsoluteSlope G g)
    {S : Set I} (hS : S.Infinite) (heq : Set.EqOn F G S) :
    f = g := by
  classical
  rcases hF with ⟨_hFcont, pF, hpF⟩
  rcases hG with ⟨_hGcont, pG, hpG⟩
  let p : RealPartition := pF.commonRefinement pG
  have hpFref : p.Refines pF := by
    dsimp [p]
    exact RealPartition.commonRefinement_refines_left pF pG
  have hpGref : p.Refines pG := by
    dsimp [p]
    exact RealPartition.commonRefinement_refines_right pF pG
  have hinfiniteCell : ∃ q : p.LapIndex,
      (S ∩ q.assignedCell).Infinite := by
    by_contra hnone
    apply hS
    have hpieces : ∀ q : p.LapIndex,
        (S ∩ q.assignedCell).Finite := by
      intro q
      by_contra hq
      exact hnone ⟨q, hq⟩
    have hunion :
        (⋃ q : p.LapIndex, S ∩ q.assignedCell).Finite :=
      Set.finite_iUnion hpieces
    apply hunion.subset
    intro x hxS
    have hxcover : x ∈ ⋃ q : p.LapIndex, q.assignedCell := by
      rw [RealPartition.iUnion_assignedCells p]
      exact Set.mem_univ x
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxcover
    exact Set.mem_iUnion.mpr ⟨q, ⟨hxS, hxq⟩⟩
  obtain ⟨q, hqInfinite⟩ := hinfiniteCell
  obtain ⟨x, hx⟩ := hqInfinite.nonempty
  have hnotSubset : ¬(S ∩ q.assignedCell ⊆ ({x} : Set I)) := by
    intro hsub
    exact hqInfinite ((Set.finite_singleton x).subset hsub)
  obtain ⟨y, hy, hyne⟩ := Set.not_subset.mp hnotSubset
  have hyx : y ≠ x := by simpa using hyne
  obtain ⟨aF, bF, hFadj, hsubF⟩ :=
    hpFref.adjacent_subset q.adjacent
  obtain ⟨aG, bG, hGadj, hsubG⟩ :=
    hpGref.adjacent_subset q.adjacent
  obtain ⟨mF, cF, hmF, hFformula⟩ := hpF hFadj
  obtain ⟨mG, cG, hmG, hGformula⟩ := hpG hGadj
  have hxCell : x ∈ q.closedCell :=
    q.assignedCell_subset_closedCell hx.2
  have hyCell : y ∈ q.closedCell :=
    q.assignedCell_subset_closedCell hy.2
  have hxF : x ∈ intervalCell aF bF := hsubF hxCell
  have hyF : y ∈ intervalCell aF bF := hsubF hyCell
  have hxG : x ∈ intervalCell aG bG := hsubG hxCell
  have hyG : y ∈ intervalCell aG bG := hsubG hyCell
  have heqx : (F x : ℝ) = (G x : ℝ) :=
    congrArg Subtype.val (heq hx.1)
  have heqy : (F y : ℝ) = (G y : ℝ) :=
    congrArg Subtype.val (heq hy.1)
  rw [hFformula x hxF, hGformula x hxG] at heqx
  rw [hFformula y hyF, hGformula y hyG] at heqy
  have hxyne : (x : ℝ) ≠ (y : ℝ) := by
    intro hxy
    exact hyx (Subtype.ext hxy.symm)
  have hm : mF = mG := by
    rcases lt_or_gt_of_ne hxyne with hxy | hyx'
    · nlinarith
    · nlinarith
  calc
    f = |mF| := hmF.symm
    _ = |mG| := congrArg abs hm
    _ = g := hmG

theorem tail_cycle_forces_scale_equation
    {A B : IntervalMap} {a b : ℝ}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (ha : 0 < a) (hb : 0 < b)
    (hcomm : Function.Commute A B)
    {w : I} (horbit : (forwardOrbit A w).Infinite)
    {r p q : ℕ}
    (hcycle : iterateMap A p (iterateMap B r w) = iterateMap A q w) :
    a ^ p * b ^ r = a ^ q := by
  let F : IntervalMap := iterateMap A p ∘ iterateMap B r
  let G : IntervalMap := iterateMap A q
  have hFA : Function.Commute F A := by
    dsimp [F]
    exact (Function.Commute.iterate_self A p).comp_left
      (hcomm.symm.iterate_left r)
  have hGA : Function.Commute G A := by
    dsimp [G]
    exact Function.Commute.iterate_self A q
  have hpoint : F w = G w := by
    simpa [F, G, Function.comp_apply] using hcycle
  have heqOrbit : Set.EqOn F G (forwardOrbit A w) := by
    rintro z ⟨k, rfl⟩
    change F ((A^[k]) w) = G ((A^[k]) w)
    rw [(hFA.iterate_right k).eq, (hGA.iterate_right k).eq, hpoint]
  have hApslope :
      HasConstantAbsoluteSlope (iterateMap A p) (a ^ p) :=
    hAslope.iterateMap ha p
  have hBrslope :
      HasConstantAbsoluteSlope (iterateMap B r) (b ^ r) :=
    hBslope.iterateMap hb r
  have hFslope : HasConstantAbsoluteSlope F (a ^ p * b ^ r) := by
    dsimp [F]
    exact HasConstantAbsoluteSlope.comp_of_pos
      (pow_pos hb r) hApslope hBrslope
  have hGslope : HasConstantAbsoluteSlope G (a ^ q) := by
    simpa [G] using hAslope.iterateMap ha q
  exact constantSlope_scale_eq_of_eqOn_infinite
    hFslope hGslope horbit heqOrbit

/-- Multiplicative independence excludes the scale equation of a tail cycle. -/
theorem mixed_scale_equation_impossible
    {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hind : MultiplicativelyIndependent a b)
    {r p q : ℕ} (hr : 0 < r) :
    a ^ p * b ^ r ≠ a ^ q := by
  intro heq
  have hapos : 0 < a ^ p := pow_pos (zero_lt_one.trans ha) p
  have hbr : 1 < b ^ r := one_lt_pow₀ hb (Nat.ne_of_gt hr)
  have hpq : p < q := by
    apply (pow_lt_pow_iff_right₀ ha).mp
    calc
      a ^ p < a ^ p * b ^ r := lt_mul_of_one_lt_right hapos hbr
      _ = a ^ q := heq
  have hq : p + (q - p) = q := Nat.add_sub_of_le hpq.le
  have hcancel : b ^ r = a ^ (q - p) := by
    apply mul_left_cancel₀ (pow_ne_zero p (ne_of_gt (zero_lt_one.trans ha)))
    calc
      a ^ p * b ^ r = a ^ q := heq
      _ = a ^ (p + (q - p)) := congrArg (a ^ ·) hq.symm
      _ = a ^ p * a ^ (q - p) := pow_add a p (q - p)
  exact hind (q - p) r (Nat.sub_pos_of_lt hpq) hr hcancel.symm

/-- Each one-generator postcritical set is finite. -/
theorem oneGeneratorPostcriticalSet_finite
    {A B : IntervalMap} {a b : ℝ}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (ha : 1 < a) (hb : 1 < b)
    (hcomm : Function.Commute A B)
    (hind : MultiplicativelyIndependent a b) :
    (oneGeneratorPostcriticalSet A).Finite := by
  by_contra hinfinite
  obtain ⟨w, _hw, horbit, r, p, q, hr, hcycle⟩ :=
    infinite_postcritical_yields_tail_cycle hA hB hAonto hBonto
      hAslope hBslope ha hb hcomm hinfinite
  have hscale : a ^ p * b ^ r = a ^ q :=
    tail_cycle_forces_scale_equation hA hB hAslope hBslope
      (lt_trans zero_lt_one ha) (lt_trans zero_lt_one hb)
      hcomm horbit hcycle
  exact (mixed_scale_equation_impossible ha hb hind hr) hscale

/-! ## Cross transport and a finite common invariant hull -/

/-- A point newly entering the `A`-postcritical set under `B` is `A`-periodic. -/
theorem cross_postcritical_point_periodic
    {A B : IntervalMap}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAflat : ¬HasFlatInterval A) (hBflat : ¬HasFlatInterval B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hcomm : Function.Commute A B)
    {x : I}
    (hx : x ∈ B '' oneGeneratorPostcriticalSet A \
      oneGeneratorPostcriticalSet A) :
    ∃ r : ℕ, 0 < r ∧ iterateMap A r x = x := by
  classical
  obtain ⟨y, hyPost, rfl⟩ := hx.1
  have hnotPost : B y ∉ oneGeneratorPostcriticalSet A := hx.2
  have hVBfinite : (criticalValues B).Finite :=
    criticalValues_finite hB hBflat
  obtain ⟨m₀, hm₀pos, hym₀⟩ :=
    exists_positive_truncation_of_mem_postcritical hyPost
  let N : ℕ → ℕ := fun k ↦ m₀ + k
  have hNpos (k : ℕ) : 0 < N k := by
    dsimp [N]
    omega
  have hyN (k : ℕ) : y ∈ truncatedPostcriticalSet A (N k) := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hym₀
    obtain ⟨him₀, hiimage⟩ := Set.mem_iUnion.mp hi
    apply Set.mem_iUnion.mpr
    refine ⟨i, Set.mem_iUnion.mpr ⟨?_, hiimage⟩⟩
    dsimp [N]
    omega
  have hpreimage (k : ℕ) :
      B y ∈ iterateMap A (N k) '' criticalValues B := by
    apply postcritical_difference hA hB hAflat hBflat
      hAonto hBonto hcomm (hNpos k)
    constructor
    · exact ⟨y, hyN k, rfl⟩
    · intro htruncated
      exact hnotPost
        (truncatedPostcriticalSet_subset_oneGenerator A (N k) htruncated)
  let pick : ℕ → {v // v ∈ criticalValues B} := fun k ↦
    ⟨Classical.choose (hpreimage k),
      (Classical.choose_spec (hpreimage k)).1⟩
  have hpick (k : ℕ) : iterateMap A (N k) (pick k) = B y :=
    (Classical.choose_spec (hpreimage k)).2
  letI : Finite {v // v ∈ criticalValues B} := hVBfinite.to_subtype
  obtain ⟨k, l, hklne, hpickeq⟩ :=
    Finite.exists_ne_map_eq_of_infinite pick
  have hperiodic_of_ordered {k l : ℕ} (hkl : k < l)
      (hpickeq : pick k = pick l) :
      ∃ r : ℕ, 0 < r ∧ iterateMap A r (B y) = B y := by
    refine ⟨l - k, Nat.sub_pos_of_lt hkl, ?_⟩
    change (A^[l - k]) (B y) = B y
    calc
      (A^[l - k]) (B y) =
          (A^[l - k]) ((A^[N k]) (pick k)) :=
        congrArg (A^[l - k]) (hpick k).symm
      _ = (A^[l - k + N k]) (pick k) :=
        (Function.iterate_add_apply A (l - k) (N k) (pick k)).symm
      _ = (A^[N l]) (pick l) := by
        have hexp : l - k + N k = N l := by
          dsimp [N]
          omega
        rw [hexp, hpickeq]
      _ = B y := hpick l
  rcases lt_or_gt_of_ne hklne with hkl | hlk
  · exact hperiodic_of_ordered hkl hpickeq
  · exact hperiodic_of_ordered hlk hpickeq.symm

/-- Turns of one generator are transported into its own turns or the other's postcritical set. -/
private theorem criticalValues_subset_oneGeneratorPostcriticalSet
    (T : IntervalMap) :
    criticalValues T ⊆ oneGeneratorPostcriticalSet T := by
  intro x hx
  apply Set.mem_iUnion.mpr
  exact ⟨0, ⟨x, hx, by simp [iterateMap]⟩⟩

theorem criticalDomain_transport
    {A B : IntervalMap}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAflat : ¬HasFlatInterval A) (hBflat : ¬HasFlatInterval B)
    (hcomm : Function.Commute A B) :
    B '' criticalDomain A ⊆
        criticalDomain A ∪ oneGeneratorPostcriticalSet B ∧
      A '' criticalDomain B ⊆
        criticalDomain B ∪ oneGeneratorPostcriticalSet A := by
  have hmaps : B ∘ A = A ∘ B := by
    funext x
    exact (hcomm x).symm
  have hdomains :
      criticalDomain A ∪ A ⁻¹' criticalDomain B =
        criticalDomain B ∪ B ⁻¹' criticalDomain A := by
    rw [← criticalDomain_comp_exact hB hA hBflat hAflat,
      ← criticalDomain_comp_exact hA hB hAflat hBflat, hmaps]
  constructor
  · rintro y ⟨x, hxA, rfl⟩
    have hx : x ∈ criticalDomain A ∪ A ⁻¹' criticalDomain B :=
      Or.inl hxA
    rw [hdomains] at hx
    rcases hx with hxB | hBxA
    · right
      apply criticalValues_subset_oneGeneratorPostcriticalSet B
      exact ⟨x, hxB, rfl⟩
    · exact Or.inl hBxA
  · rintro y ⟨x, hxB, rfl⟩
    have hx : x ∈ criticalDomain B ∪ B ⁻¹' criticalDomain A :=
      Or.inl hxB
    rw [← hdomains] at hx
    rcases hx with hxA | hAxB
    · right
      apply criticalValues_subset_oneGeneratorPostcriticalSet A
      exact ⟨x, hxA, rfl⟩
    · exact Or.inl hAxB

/-- Every positive iterate of an expanding constant-slope map has a finite
fixed-point set. -/
theorem fixedPoints_positiveIterate_finite_of_constantSlope
    {T : IntervalMap} {s : ℝ}
    (hT : HasConstantAbsoluteSlope T s) (hs : 1 < s)
    {r : ℕ} (hr : 0 < r) :
    (fixedPoints (iterateMap T r)).Finite := by
  exact hT.iterateMap_fixedPoints_finite hs r hr

/-- A multiple of a period is again a period. -/
private theorem iterate_eq_of_period_dvd
    {T : IntervalMap} {x : I} {d r : ℕ}
    (hperiod : iterateMap T d x = x) (hdr : d ∣ r) :
    iterateMap T r x = x := by
  obtain ⟨k, rfl⟩ := hdr
  change (T^[d]) x = x at hperiod
  change (T^[d * k]) x = x
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ]
      rw [Function.iterate_add_apply, hperiod]
      exact ih

/-- The full forward orbit of the critical-value seeds is forward invariant
under its defining map. -/
private theorem oneGeneratorPostcriticalSet_mapsTo_self
    (T : IntervalMap) :
    MapsTo T (oneGeneratorPostcriticalSet T)
      (oneGeneratorPostcriticalSet T) := by
  intro x hx
  obtain ⟨n, v, hv, hnv⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨n + 1, ⟨v, hv, ?_⟩⟩
  change (T^[n + 1]) v = T x
  rw [Function.iterate_succ_apply']
  exact congrArg T hnv

/-- Enlarge one finite postcritical set by one finite fixed set so that it is
invariant under both the defining map and a commuting map. -/
private theorem finite_common_invariant_postcritical_extension
    {A B : IntervalMap} {a : ℝ}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAflat : ¬HasFlatInterval A) (hBflat : ¬HasFlatInterval B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hcomm : Function.Commute A B)
    (hpostfinite : (oneGeneratorPostcriticalSet A).Finite)
    (hAslope : HasConstantAbsoluteSlope A a) (ha : 1 < a) :
    ∃ K : Set I, K.Finite ∧
      oneGeneratorPostcriticalSet A ⊆ K ∧
      MapsTo A K K ∧ MapsTo B K K := by
  classical
  let cross : Set I :=
    B '' oneGeneratorPostcriticalSet A \ oneGeneratorPostcriticalSet A
  have hcrossfinite : cross.Finite := by
    apply (hpostfinite.image B).subset
    exact Set.diff_subset
  have hcrossPeriodic : ∀ x : {x // x ∈ cross},
      ∃ r : ℕ, 0 < r ∧ iterateMap A r x = x := by
    intro x
    exact cross_postcritical_point_periodic hA hB hAflat hBflat
      hAonto hBonto hcomm x.property
  choose period hperiodPos hperiodFix using hcrossPeriodic
  letI : Fintype {x // x ∈ cross} := hcrossfinite.fintype
  let r : ℕ := ∏ x : {x // x ∈ cross}, period x
  have hr : 0 < r := by
    dsimp [r]
    exact Finset.prod_pos fun x _hx ↦ hperiodPos x
  have hcrossFix : cross ⊆ fixedPoints (iterateMap A r) := by
    intro x hx
    let x' : {x // x ∈ cross} := ⟨x, hx⟩
    have hdvd : period x' ∣ r := by
      dsimp [r]
      exact Finset.dvd_prod_of_mem (fun y ↦ period y)
        (Finset.mem_univ x')
    change iterateMap A r x = x
    exact iterate_eq_of_period_dvd (hperiodFix x') hdvd
  have hfixfinite : (fixedPoints (iterateMap A r)).Finite :=
    fixedPoints_positiveIterate_finite_of_constantSlope hAslope ha hr
  let K : Set I :=
    oneGeneratorPostcriticalSet A ∪ fixedPoints (iterateMap A r)
  refine ⟨K, hpostfinite.union hfixfinite, ?_, ?_, ?_⟩
  · exact Set.subset_union_left
  · intro x hx
    rcases hx with hxpost | hxfix
    · exact Or.inl (oneGeneratorPostcriticalSet_mapsTo_self A hxpost)
    · right
      change iterateMap A r (A x) = A x
      change iterateMap A r x = x at hxfix
      calc
        iterateMap A r (A x) = A (iterateMap A r x) :=
          Function.Commute.iterate_self A r x
        _ = A x := congrArg A hxfix
  · intro x hx
    rcases hx with hxpost | hxfix
    · by_cases hBxpost : B x ∈ oneGeneratorPostcriticalSet A
      · exact Or.inl hBxpost
      · right
        apply hcrossFix
        exact ⟨⟨x, hxpost, rfl⟩, hBxpost⟩
    · right
      change iterateMap A r (B x) = B x
      change iterateMap A r x = x at hxfix
      calc
        iterateMap A r (B x) = B (iterateMap A r x) :=
          hcomm.iterate_left r x
        _ = B x := congrArg B hxfix

/--
The two finite postcritical sets can be enlarged by finitely many periodic
cross-images to a finite set invariant under both generators and containing
both intrinsic critical-domain sets.
-/
theorem finite_common_invariant_postcritical_hull
    {A B : IntervalMap} {a b : ℝ}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (ha : 1 < a) (hb : 1 < b)
    (hcomm : Function.Commute A B)
    (hind : MultiplicativelyIndependent a b) :
    ∃ K : Set I, K.Finite ∧
      criticalDomain A ∪ criticalDomain B ⊆ K ∧
      MapsTo A K K ∧ MapsTo B K K := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hAflat : ¬HasFlatInterval A := hAslope.noFlatInterval ha0
  have hBflat : ¬HasFlatInterval B := hBslope.noFlatInterval hb0
  have hpostA : (oneGeneratorPostcriticalSet A).Finite :=
    oneGeneratorPostcriticalSet_finite hA hB hAonto hBonto
      hAslope hBslope ha hb hcomm hind
  have hindsymm : MultiplicativelyIndependent b a := by
    intro m n hm hn heq
    exact hind n m hn hm heq.symm
  have hpostB : (oneGeneratorPostcriticalSet B).Finite :=
    oneGeneratorPostcriticalSet_finite hB hA hBonto hAonto
      hBslope hAslope hb ha hcomm.symm hindsymm
  obtain ⟨KA, hKAfinite, hpostAKA, hAKA, hBKA⟩ :=
    finite_common_invariant_postcritical_extension
      hA hB hAflat hBflat hAonto hBonto hcomm hpostA hAslope ha
  obtain ⟨KB, hKBfinite, hpostBKB, hBKB, hAKB⟩ :=
    finite_common_invariant_postcritical_extension
      hB hA hBflat hAflat hBonto hAonto hcomm.symm hpostB hBslope hb
  have hcriticalA : (criticalDomain A).Finite :=
    criticalDomain_finite hA hAflat
  have hcriticalB : (criticalDomain B).Finite :=
    criticalDomain_finite hB hBflat
  have htransport :=
    criticalDomain_transport hA hB hAflat hBflat hcomm
  let K : Set I :=
    (criticalDomain A ∪ criticalDomain B) ∪ (KA ∪ KB)
  refine ⟨K,
    (hcriticalA.union hcriticalB).union (hKAfinite.union hKBfinite),
    ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl hx
  · intro x hx
    rcases hx with (hxA | hxB) | (hxKA | hxKB)
    · right
      left
      apply hpostAKA
      apply criticalValues_subset_oneGeneratorPostcriticalSet A
      exact ⟨x, hxA, rfl⟩
    · have hAx := htransport.2 ⟨x, hxB, rfl⟩
      rcases hAx with hAxB | hAxPost
      · exact Or.inl (Or.inr hAxB)
      · exact Or.inr (Or.inl (hpostAKA hAxPost))
    · exact Or.inr (Or.inl (hAKA hxKA))
    · exact Or.inr (Or.inr (hAKB hxKB))
  · intro x hx
    rcases hx with (hxA | hxB) | (hxKA | hxKB)
    · have hBx := htransport.1 ⟨x, hxA, rfl⟩
      rcases hBx with hBxA | hBxPost
      · exact Or.inl (Or.inl hBxA)
      · exact Or.inr (Or.inr (hpostBKB hBxPost))
    · right
      right
      apply hpostBKB
      apply criticalValues_subset_oneGeneratorPostcriticalSet B
      exact ⟨x, hxB, rfl⟩
    · exact Or.inr (Or.inl (hBKA hxKA))
    · exact Or.inr (Or.inr (hBKB hxKB))

/-- Every positive commuting word carries the critical sets into a common invariant hull. -/
theorem jointPostcriticalSet_subset_commonHull
    {A B : IntervalMap} {K : Set I}
    (hcrit : criticalDomain A ∪ criticalDomain B ⊆ K)
    (hAK : MapsTo A K K) (hBK : MapsTo B K K) :
    jointPostcriticalSet A B ⊆ K := by
  have hAiterate (m : ℕ) : MapsTo (iterateMap A m) K K := by
    intro x hx
    induction m with
    | zero => simpa [iterateMap] using hx
    | succ m ih =>
        simpa only [iterateMap, Function.iterate_succ_apply'] using hAK ih
  have hBiterate (n : ℕ) : MapsTo (iterateMap B n) K K := by
    intro x hx
    induction n with
    | zero => simpa [iterateMap] using hx
    | succ n ih =>
        simpa only [iterateMap, Function.iterate_succ_apply'] using hBK ih
  intro y hy
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  obtain ⟨x, hx, rfl⟩ := hn
  exact hAiterate m (hBiterate n (hcrit hx))

/-! ## Final manuscript lemma -/

/-- **Finite joint postcritical set.** -/
theorem jointPostcriticalSet_finite
    {A B : IntervalMap} {a b : ℝ}
    (hA : FinitePiecePL A) (hB : FinitePiecePL B)
    (hAonto : IsOnto A) (hBonto : IsOnto B)
    (hAslope : HasConstantAbsoluteSlope A a)
    (hBslope : HasConstantAbsoluteSlope B b)
    (ha : 1 < a) (hb : 1 < b)
    (hcomm : Function.Commute A B)
    (hind : MultiplicativelyIndependent a b) :
    (jointPostcriticalSet A B).Finite := by
  obtain ⟨K, hKfinite, hcrit, hAK, hBK⟩ :=
    finite_common_invariant_postcritical_hull hA hB hAonto hBonto
      hAslope hBslope ha hb hcomm hind
  exact hKfinite.subset
    (jointPostcriticalSet_subset_commonHull hcrit hAK hBK)

end CommutingIntervalSimplified
