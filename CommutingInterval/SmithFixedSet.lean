import CommutingInterval.ArcLikeDefs
import CommutingInterval.PosetNerve
import CommutingInterval.PosetNervePrism
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

namespace CommutingInterval

open Function Set

/-!
# Fixed sets of prime-order homeomorphisms of arc-like continua

This file proves the full-nerve Smith theorem while retaining all higher nerve
simplices.  It uses a finite free augmented chain complex over `ZMod p`, with
a basis permuted by the cyclic action.
-/

/-- A finite, bounded, augmented chain complex freely based in each degree,
with a cyclic permutation action on the basis.  Barycentric subdivision of a
finite invariant nerve has this form and makes the action regular. -/
structure FiniteCyclicAugmentedComplex (p : ℕ) where
  Basis : ℕ → Type
  basisFintype : ∀ n, Fintype (Basis n)
  basisDecidableEq : ∀ n, DecidableEq (Basis n)
  boundary : ∀ n,
    (Basis (n + 1) →₀ ZMod p) →ₗ[ZMod p] (Basis n →₀ ZMod p)
  augment : (Basis 0 →₀ ZMod p) →ₗ[ZMod p] ZMod p
  actionBasis : ∀ n, Equiv.Perm (Basis n)
  actionBasis_periodic : ∀ n, actionBasis n ^ p = 1
  action : ∀ n,
    (Basis n →₀ ZMod p) ≃ₗ[ZMod p] (Basis n →₀ ZMod p)
  action_single : ∀ n (b : Basis n) (r : ZMod p),
    action n (Finsupp.single b r) = Finsupp.single (actionBasis n b) r
  action_periodic : ∀ n, (action n : (Basis n →₀ ZMod p) →
      (Basis n →₀ ZMod p))^[p] = id
  boundary_boundary : ∀ n c, boundary n (boundary (n + 1) c) = 0
  augment_boundary : ∀ c, augment (boundary 0 c) = 0
  boundary_equivariant : ∀ n c,
    boundary n (action (n + 1) c) = action n (boundary n c)
  augment_equivariant : ∀ c, augment (action 0 c) = augment c
  regular_boundary : ∀ n (b : Basis (n + 1)), actionBasis (n + 1) b = b →
    ∀ a ∈ (boundary n (Finsupp.single b 1)).support,
      actionBasis n a = a
  bounded : ∃ N, ∀ n, N < n → IsEmpty (Basis n)

attribute [instance] FiniteCyclicAugmentedComplex.basisFintype
attribute [instance] FiniteCyclicAugmentedComplex.basisDecidableEq

/-- The regular augmented complex of the barycentric nerve of a finite poset.
All simplicial identities are transported from mathlib's normalized chains;
the concrete basis is the strict chains in the poset. -/
private noncomputable def finiteCyclicAugmentedComplexOfPoset
    (p : ℕ) (P : Type) [PartialOrder P] [Fintype P]
    (e : P ≃o P) (he : (e.toEquiv : Equiv.Perm P) ^ p = 1) :
    FiniteCyclicAugmentedComplex p where
  Basis := PosetNerve.strictChains P
  basisFintype := fun n ↦ by
    classical
    unfold PosetNerve.strictChains
    infer_instance
  basisDecidableEq := fun _ ↦ Classical.decEq _
  boundary := PosetNerve.strictBoundary P (ZMod p)
  augment := PosetNerve.strictAugment P (ZMod p)
  actionBasis := PosetNerve.strictChainEquiv P e
  actionBasis_periodic := fun n ↦
    PosetNerve.strictChainEquiv_periodic P e n p he
  action := PosetNerve.strictAction P (ZMod p) e
  action_single := fun n b r ↦ PosetNerve.strictAction_single P (ZMod p) e n b r
  action_periodic := fun n ↦
    PosetNerve.strictAction_periodic P (ZMod p) e n p he
  boundary_boundary := fun n c ↦
    PosetNerve.strictBoundary_boundary P (ZMod p) n c
  augment_boundary := fun c ↦
    PosetNerve.strictAugment_boundary P (ZMod p) c
  boundary_equivariant := fun n c ↦
    PosetNerve.strictBoundary_action P (ZMod p) e n c
  augment_equivariant := fun c ↦
    PosetNerve.strictAugment_action P (ZMod p) e c
  regular_boundary := fun n b hb a ha ↦
    PosetNerve.strictRegularBoundary P (ZMod p) e n b hb a ha
  bounded := PosetNerve.strictChains_bounded P

private abbrev FiniteCyclicAugmentedComplex.Chain
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) (n : ℕ) :=
  C.Basis n →₀ ZMod p

/-- Chains supported only on simplices fixed basiswise.  For a regular
barycentric action these are exactly the chains of the fixed subcomplex, not
merely invariant orbit-sum chains. -/
private def FiniteCyclicAugmentedComplex.IsFixedChain
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) {n : ℕ}
    (c : C.Chain n) : Prop :=
  ∀ b ∈ c.support, C.actionBasis n b = b

private def FiniteCyclicAugmentedComplex.IsReducedCycle
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) :
    ∀ n, C.Chain n → Prop
  | 0, c => C.augment c = 0
  | n + 1, c => C.boundary n c = 0

private def FiniteCyclicAugmentedComplex.IsBoundary
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) (n : ℕ)
    (c : C.Chain n) : Prop :=
  ∃ w : C.Chain (n + 1), C.boundary n w = c

/-- Equivariant augmentation-preserving chain map.  The fixed-support clause
is the algebraic form of restricting a regular equivariant simplicial map to
fixed subcomplexes. -/
structure FiniteCyclicAugmentedComplex.Hom
    {p : ℕ} (C D : FiniteCyclicAugmentedComplex p) where
  map : ∀ n, C.Chain n →ₗ[ZMod p] D.Chain n
  map_boundary : ∀ n c, map n (C.boundary n c) = D.boundary n (map (n + 1) c)
  map_augment : ∀ c, D.augment (map 0 c) = C.augment c
  map_equivariant : ∀ n c, map n (C.action n c) = D.action n (map n c)
  map_fixed : ∀ n c, C.IsFixedChain c → D.IsFixedChain (map n c)

/-- All induced maps on reduced homology vanish, phrased without quotient
modules: every reduced cycle maps to an actual boundary. -/
private def FiniteCyclicAugmentedComplex.Hom.KillsReducedHomology
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p} (f : C.Hom D) : Prop :=
  ∀ n (z : C.Chain n), C.IsReducedCycle n z → D.IsBoundary n (f.map n z)

/-- An augmentation-preserving chain map after forgetting all cyclic-action
data.  Ordinary (non-equivariant) cover refinements naturally induce these
maps, so this is the comparison layer between the arc-like refinement and its
later equivariant cyclic saturation. -/
private structure FiniteCyclicAugmentedComplex.UnderlyingHom
    {p : ℕ} (C D : FiniteCyclicAugmentedComplex p) where
  map : ∀ n, C.Chain n →ₗ[ZMod p] D.Chain n
  map_boundary : ∀ n c, map n (C.boundary n c) = D.boundary n (map (n + 1) c)
  map_augment : ∀ c, D.augment (map 0 c) = C.augment c

private def FiniteCyclicAugmentedComplex.Hom.toUnderlyingHom
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p} (f : C.Hom D) :
    C.UnderlyingHom D where
  map := f.map
  map_boundary := f.map_boundary
  map_augment := f.map_augment

private def FiniteCyclicAugmentedComplex.UnderlyingHom.KillsReducedHomology
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p}
    (f : C.UnderlyingHom D) : Prop :=
  ∀ n (z : C.Chain n), C.IsReducedCycle n z → D.IsBoundary n (f.map n z)

/-- A chain homotopy in precisely the augmented/reduced range used below.
The operator is recorded explicitly; the displayed identity says that on a
reduced cycle the difference of the two maps is the boundary of its prism. -/
private structure FiniteCyclicAugmentedComplex.UnderlyingHom.ReducedChainHomotopy
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p}
    (f g : C.UnderlyingHom D) where
  prism : ∀ n, C.Chain n →ₗ[ZMod p] D.Chain (n + 1)
  boundary_prism : ∀ n (z : C.Chain n), C.IsReducedCycle n z →
    D.boundary n (prism n z) = f.map n z - g.map n z

private noncomputable def FiniteCyclicAugmentedComplex.UnderlyingHom.comp
    {p : ℕ} {C D E : FiniteCyclicAugmentedComplex p}
    (g : D.UnderlyingHom E) (f : C.UnderlyingHom D) :
    C.UnderlyingHom E where
  map := fun n ↦ (g.map n).comp (f.map n)
  map_boundary := by
    intro n c
    simp only [LinearMap.comp_apply]
    rw [f.map_boundary, g.map_boundary]
  map_augment := by
    intro c
    simp only [LinearMap.comp_apply]
    rw [g.map_augment, f.map_augment]

private theorem FiniteCyclicAugmentedComplex.UnderlyingHom.map_reducedCycle
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p}
    (f : C.UnderlyingHom D) {n : ℕ} {z : C.Chain n}
    (hz : C.IsReducedCycle n z) : D.IsReducedCycle n (f.map n z) := by
  cases n with
  | zero =>
      change D.augment (f.map 0 z) = 0
      rw [f.map_augment]
      exact hz
  | succ n =>
      change D.boundary n (f.map (n + 1) z) = 0
      rw [← f.map_boundary, hz, map_zero]

private theorem FiniteCyclicAugmentedComplex.UnderlyingHom.comp_kills_of_left_kills
    {p : ℕ} {C D E : FiniteCyclicAugmentedComplex p}
    (g : D.UnderlyingHom E) (f : C.UnderlyingHom D)
    (hg : g.KillsReducedHomology) : (g.comp f).KillsReducedHomology := by
  intro n z hz
  exact hg n (f.map n z) (f.map_reducedCycle hz)

private theorem FiniteCyclicAugmentedComplex.UnderlyingHom.kills_of_reducedChainHomotopy
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p}
    {f g : C.UnderlyingHom D} (hf : f.KillsReducedHomology)
    (H : f.ReducedChainHomotopy g) : g.KillsReducedHomology := by
  intro n z hz
  obtain ⟨w, hw⟩ := hf n z hz
  refine ⟨w - H.prism n z, ?_⟩
  rw [map_sub, hw, H.boundary_prism n z hz]
  abel

/-- The same full barycentric nerve, equipped with the trivial cyclic action.
It is the chain complex naturally attached to an ordinary finite cover. -/
private noncomputable def finiteTrivialAugmentedComplexOfPoset
    (p : ℕ) (P : Type) [PartialOrder P] [Fintype P] :
    FiniteCyclicAugmentedComplex p :=
  finiteCyclicAugmentedComplexOfPoset p P (OrderIso.refl P) (by
    show (1 : Equiv.Perm P) ^ p = 1
    exact one_pow p)

/-- The underlying augmented chain map induced by a monotone map of finite
posets, with no equivariance assertion. -/
private noncomputable def posetStrictUnderlyingHom
    {p : ℕ} {P Q : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q] (f : P →o Q) :
    (finiteTrivialAugmentedComplexOfPoset p P).UnderlyingHom
      (finiteTrivialAugmentedComplexOfPoset p Q) where
  map := fun n ↦ PosetNerve.strictChainMap P Q (ZMod p) f n
  map_boundary := fun n c ↦
    PosetNerve.strictChainMap_boundary P Q (ZMod p) f n c
  map_augment := fun c ↦
    PosetNerve.strictChainMap_augment P Q (ZMod p) f c

/-- Reduced cycles in the normalized strict nerve, stated independently of
any action placed on that nerve. -/
private def PosetNerve.StrictIsReducedCycle
    (P : Type) [PartialOrder P] (p : ℕ) :
    ∀ n, (PosetNerve.strictChains P n →₀ ZMod p) → Prop
  | 0, z => PosetNerve.strictAugment P (ZMod p) z = 0
  | n + 1, z => PosetNerve.strictBoundary P (ZMod p) n z = 0

private def PosetNerve.StrictMapKillsReducedHomology
    {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (p : ℕ) (f : P →o Q) : Prop :=
  ∀ n (z : PosetNerve.strictChains P n →₀ ZMod p),
    PosetNerve.StrictIsReducedCycle P p n z →
      ∃ w : PosetNerve.strictChains Q (n + 1) →₀ ZMod p,
        PosetNerve.strictBoundary Q (ZMod p) n w =
          PosetNerve.strictChainMap P Q (ZMod p) f n z

/-- An explicit normalized prism between strict nerve maps. -/
private structure PosetNerve.StrictReducedChainHomotopy
    {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (p : ℕ) (f g : P →o Q) where
  prism : ∀ n,
    (PosetNerve.strictChains P n →₀ ZMod p) →ₗ[ZMod p]
      (PosetNerve.strictChains Q (n + 1) →₀ ZMod p)
  boundary_prism : ∀ n (z : PosetNerve.strictChains P n →₀ ZMod p),
    PosetNerve.StrictIsReducedCycle P p n z →
      PosetNerve.strictBoundary Q (ZMod p) n (prism n z) =
        PosetNerve.strictChainMap P Q (ZMod p) f n z -
          PosetNerve.strictChainMap P Q (ZMod p) g n z

private noncomputable def PosetNerve.StrictReducedChainHomotopy.refl
    {p : ℕ} {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) : PosetNerve.StrictReducedChainHomotopy p f f where
  prism := fun n ↦ 0
  boundary_prism := by
    intro n z _
    simp

private noncomputable def PosetNerve.StrictReducedChainHomotopy.trans
    {p : ℕ} {P Q : Type} [PartialOrder P] [PartialOrder Q]
    {f g k : P →o Q}
    (H : PosetNerve.StrictReducedChainHomotopy p f g)
    (K : PosetNerve.StrictReducedChainHomotopy p g k) :
    PosetNerve.StrictReducedChainHomotopy p f k where
  prism := fun n ↦ H.prism n + K.prism n
  boundary_prism := by
    intro n z hz
    simp only [LinearMap.add_apply, map_add,
      H.boundary_prism n z hz, K.boundary_prism n z hz]
    abel

/-- Pointwise-comparable order maps induce a simplicial homotopy of their
categorical nerves.  This is the combinatorial prism before passing to free
modules or normalized chains. -/
private noncomputable def nerveOrderHomotopy_of_le
    {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (f k : P →o Q) (hf : ∀ x, f x ≤ k x) :
    CategoryTheory.SimplicialObject.Homotopy
      (PosetNerve.nerveOrderHom P Q f)
      (PosetNerve.nerveOrderHom P Q k) := by
  exact PosetNerve.nerveOrderHomotopy_of_le f k hf

/-- A simplicial homotopy of nerves descends from the alternating free chain
complex to the normalized chain complex.  Keeping this transport separate
isolates the Dold--Kan splitting API from the concrete strict-chain basis. -/
private noncomputable def posetNerve_normalizedChainHomotopy
    {R P Q : Type} [CommRing R] [PartialOrder P] [PartialOrder Q]
    {f g : P →o Q}
    (H : CategoryTheory.SimplicialObject.Homotopy
      (PosetNerve.nerveOrderHom P Q f)
      (PosetNerve.nerveOrderHom P Q g)) :
    _root_.Homotopy
      (SSet.normalizedChainComplexMap (PosetNerve.nerveOrderHom P Q f)
        (ModuleCat.of R R))
      (SSet.normalizedChainComplexMap (PosetNerve.nerveOrderHom P Q g)
        (ModuleCat.of R R)) := by
  exact ((H.sSetChainComplexMap (ModuleCat.of R R)).compLeft
    ((CategoryTheory.nerve P).fromNormalizedChainComplex
      (ModuleCat.of R R))).compRight
        ((CategoryTheory.nerve Q).toNormalizedChainComplex
          (ModuleCat.of R R))

/-- Transport a normalized categorical chain homotopy through the strict-chain
basis equivalences and retain exactly the reduced-cycle identity used below. -/
private theorem posetNerve_strictReducedChainHomotopy_of_nerveHomotopy
    {p : ℕ} {P Q : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q] {f g : P →o Q}
    (H : CategoryTheory.SimplicialObject.Homotopy
      (PosetNerve.nerveOrderHom P Q f)
      (PosetNerve.nerveOrderHom P Q g)) :
    Nonempty (PosetNerve.StrictReducedChainHomotopy p f g) := by
  let K := posetNerve_normalizedChainHomotopy (R := ZMod p) H
  refine ⟨{
    prism := fun n ↦
      (PosetNerve.strictBasisLinearEquiv Q (ZMod p) (n + 1)).symm.toLinearMap.comp
        ((K.hom n (n + 1)).hom.comp
          (PosetNerve.strictBasisLinearEquiv P (ZMod p) n).toLinearMap)
    boundary_prism := ?_ }⟩
  intro n z hz
  apply (PosetNerve.strictBasisLinearEquiv Q (ZMod p) n).injective
  rw [PosetNerve.strictBasisLinearEquiv_boundary,
    map_sub,
    PosetNerve.strictBasisLinearEquiv_chainMap,
    PosetNerve.strictBasisLinearEquiv_chainMap]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  cases n with
  | zero =>
      have hc := K.comm 0
      rw [dNext_eq_zero K.hom 0 (by simp), zero_add,
        prevD_eq K.hom (j' := 1) (by simp)] at hc
      have hcz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hc)
        (PosetNerve.strictBasisLinearEquiv P (ZMod p) 0 z)
      simp only [ModuleCat.hom_add, LinearMap.add_apply,
        ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hcz ⊢
      rw [eq_sub_iff_add_eq]
      exact hcz.symm
  | succ n =>
      change PosetNerve.strictBoundary P (ZMod p) n z = 0 at hz
      have hz' :
          ((((CategoryTheory.nerve P).normalizedChainComplex
            (ModuleCat.of (ZMod p) (ZMod p))).d (n + 1) n).hom)
              (PosetNerve.strictBasisLinearEquiv P (ZMod p) (n + 1) z) = 0 := by
        calc
          _ = PosetNerve.strictBasisLinearEquiv P (ZMod p) n
              (PosetNerve.strictBoundary P (ZMod p) n z) :=
            (PosetNerve.strictBasisLinearEquiv_boundary P (ZMod p) n z).symm
          _ = 0 := by rw [hz, map_zero]
      have hc := K.comm (n + 1)
      rw [dNext_eq K.hom (i' := n) (by simp),
        prevD_eq K.hom (j' := n + 2) (by simp)] at hc
      have hcz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hc)
        (PosetNerve.strictBasisLinearEquiv P (ZMod p) (n + 1) z)
      simp only [ModuleCat.hom_add, LinearMap.add_apply,
        ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
        hz', map_zero, zero_add] at hcz
      rw [eq_sub_iff_add_eq]
      exact hcz.symm

/-- The missing normalized-prism API for `PosetNerve`: two monotone maps with
a pointwise common upper bound induce reduced-chain-homotopic strict nerve
maps.  This is kept explicit instead of hiding contiguity inside the
equivariant refinement constructor. -/
private theorem posetNerve_strictReducedChainHomotopy_of_commonUpperBound
    {p : ℕ} {P Q : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q]
    (f g k : P →o Q) (hf : ∀ x, f x ≤ k x) (hg : ∀ x, g x ≤ k x) :
    Nonempty (PosetNerve.StrictReducedChainHomotopy p f g) := by
  obtain ⟨Hfk⟩ := posetNerve_strictReducedChainHomotopy_of_nerveHomotopy
    (p := p) (nerveOrderHomotopy_of_le f k hf)
  obtain ⟨Hgk⟩ := posetNerve_strictReducedChainHomotopy_of_nerveHomotopy
    (p := p) (nerveOrderHomotopy_of_le g k hg)
  refine ⟨{
    prism := fun n ↦ Hfk.prism n - Hgk.prism n
    boundary_prism := ?_ }⟩
  intro n z hz
  simp only [LinearMap.sub_apply, map_sub,
    Hfk.boundary_prism n z hz, Hgk.boundary_prism n z hz]
  abel

/-- Functoriality of the normalized strict-chain map.  This is separate from
the prism lemma because the former compares a composite refinement with a
composite chain map, while the latter compares two different choices carried
by the same cover refinement. -/
private theorem posetNerve_strictChainMap_comp
    {p : ℕ} {P Q R : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q] [PartialOrder R] [Fintype R]
    (f : P →o Q) (g : Q →o R) (n : ℕ) :
    PosetNerve.strictChainMap P R (ZMod p) (g.comp f) n =
      (PosetNerve.strictChainMap Q R (ZMod p) g n).comp
        (PosetNerve.strictChainMap P Q (ZMod p) f n) := by
  classical
  apply LinearMap.ext
  intro c
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      simp only [map_add, LinearMap.comp_apply, ih, add_left_inj]
      by_cases hcomp : StrictMono (fun j ↦ g (f (q.1 j)))
      · have hf : StrictMono (fun j ↦ f (q.1 j)) := by
          intro i j hij
          have hle : f (q.1 i) ≤ f (q.1 j) :=
            f.monotone (q.2 hij).le
          exact lt_of_le_of_ne hle fun heq ↦
            (hcomp hij).ne (congrArg g heq)
        let qf := PosetNerve.strictChainImage P Q f q hf
        have hg : StrictMono (fun j ↦ g (qf.1 j)) := hcomp
        have himage :
            PosetNerve.strictChainImage Q R g qf hg =
              PosetNerve.strictChainImage P R (g.comp f) q hcomp := by
          apply Subtype.ext
          rfl
        rw [PosetNerve.strictChainMap_single_of_strict P R (ZMod p)
          (g.comp f) n q r hcomp,
          PosetNerve.strictChainMap_single_of_strict P Q (ZMod p)
            f n q r hf,
          PosetNerve.strictChainMap_single_of_strict Q R (ZMod p)
            g n qf r hg, himage]
      · rw [PosetNerve.strictChainMap_single_of_not_strict P R (ZMod p)
          (g.comp f) n q r hcomp]
        by_cases hf : StrictMono (fun j ↦ f (q.1 j))
        · let qf := PosetNerve.strictChainImage P Q f q hf
          have hng : ¬ StrictMono (fun j ↦ g (qf.1 j)) := by
            intro hg
            exact hcomp hg
          rw [PosetNerve.strictChainMap_single_of_strict P Q (ZMod p)
            f n q r hf,
            PosetNerve.strictChainMap_single_of_not_strict Q R (ZMod p)
              g n qf r hng]
        · rw [PosetNerve.strictChainMap_single_of_not_strict P Q (ZMod p)
            f n q r hf, map_zero]

private theorem posetNerve_strictChainMap_id
    {P : Type} [PartialOrder P] [Fintype P]
    (p n : ℕ) (c : PosetNerve.strictChains P n →₀ ZMod p) :
    PosetNerve.strictChainMap P P (ZMod p) OrderHom.id n c = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      rw [map_add, ih]
      have hs : StrictMono (fun j : Fin (n + 1) ↦ OrderHom.id (q.1 j)) := q.2
      rw [PosetNerve.strictChainMap_single_of_strict P P (ZMod p)
        OrderHom.id n q r hs]
      congr 2

private theorem posetNerve_strictChainMap_preserves_reducedCycle
    {p : ℕ} {P Q : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q] (f : P →o Q) {n : ℕ}
    {z : PosetNerve.strictChains P n →₀ ZMod p}
    (hz : PosetNerve.StrictIsReducedCycle P p n z) :
    PosetNerve.StrictIsReducedCycle Q p n
      (PosetNerve.strictChainMap P Q (ZMod p) f n z) := by
  cases n with
  | zero =>
      change PosetNerve.strictAugment Q (ZMod p)
        (PosetNerve.strictChainMap P Q (ZMod p) f 0 z) = 0
      rw [PosetNerve.strictChainMap_augment]
      exact hz
  | succ n =>
      change PosetNerve.strictBoundary Q (ZMod p) n
        (PosetNerve.strictChainMap P Q (ZMod p) f (n + 1) z) = 0
      rw [← PosetNerve.strictChainMap_boundary, hz, map_zero]

private theorem PosetNerve.StrictMapKillsReducedHomology.comp
    {p : ℕ} {P Q R : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q] [PartialOrder R] [Fintype R]
    {f : P →o Q} {g : Q →o R}
    (hg : PosetNerve.StrictMapKillsReducedHomology p g) :
    PosetNerve.StrictMapKillsReducedHomology p (g.comp f) := by
  intro n z hz
  obtain ⟨w, hw⟩ := hg n
    (PosetNerve.strictChainMap P Q (ZMod p) f n z)
    (posetNerve_strictChainMap_preserves_reducedCycle f hz)
  refine ⟨w, ?_⟩
  rw [posetNerve_strictChainMap_comp]
  exact hw

private theorem PosetNerve.StrictMapKillsReducedHomology.of_reducedChainHomotopy
    {p : ℕ} {P Q : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q] {f g : P →o Q}
    (hf : PosetNerve.StrictMapKillsReducedHomology p f)
    (H : PosetNerve.StrictReducedChainHomotopy p f g) :
    PosetNerve.StrictMapKillsReducedHomology p g := by
  intro n z hz
  obtain ⟨w, hw⟩ := hf n z hz
  refine ⟨w - H.prism n z, ?_⟩
  rw [map_sub, hw, H.boundary_prism n z hz]
  abel

/-- The Smith difference operator `1-T`. -/
private noncomputable def FiniteCyclicAugmentedComplex.tau
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) (n : ℕ) :
    C.Chain n →ₗ[ZMod p] C.Chain n :=
  LinearMap.id - (C.action n).toLinearMap

/-- Membership in the `j`th Smith image `im(1-T)^j`. -/
private def FiniteCyclicAugmentedComplex.InSmithImage
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) {n : ℕ}
    (j : ℕ) (c : C.Chain n) : Prop :=
  c ∈ LinearMap.range ((C.tau n) ^ j)

/-- The cyclic norm `1 + T + ⋯ + T^(p-1)`.  The alternating Smith
diagram chase only needs the two operators `1-T` and the norm, avoiding an
unnecessary identification of the norm with `(1-T)^(p-1)`. -/
private noncomputable def FiniteCyclicAugmentedComplex.smithNorm
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) (n : ℕ) :
    C.Chain n →ₗ[ZMod p] C.Chain n :=
  ∑ k ∈ Finset.range p, (C.action n).toLinearMap ^ k

private def FiniteCyclicAugmentedComplex.InSmithNorm
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) {n : ℕ}
    (c : C.Chain n) : Prop :=
  c ∈ LinearMap.range (C.smithNorm n)

/-- A fixed basis coordinate is unchanged by the permutation action. -/
private theorem smith_action_coeff_of_fixedBasis
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b = b)
    (c : C.Chain n) : C.action n c b = c b := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a r c ha hr ih =>
      rw [map_add, C.action_single, Finsupp.add_apply, Finsupp.add_apply, ih]
      have hab : C.actionBasis n a = b ↔ a = b := by
        constructor
        · intro h
          apply (C.actionBasis n).injective
          simpa [hb] using h
        · rintro rfl
          exact hb
      simp only [Finsupp.single_apply]
      by_cases h : a = b
      · simp [h, hb]
      · have h' : C.actionBasis n a ≠ b := by simpa [hab]
        simp [h, h']

/-- Iterating the chain action iterates its permutation of the basis. -/
private theorem smith_action_pow_single
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n k : ℕ} (b : C.Basis n) (r : ZMod p) :
    ((C.action n).toLinearMap ^ k) (Finsupp.single b r) =
      Finsupp.single (((C.actionBasis n) ^ k) b) r := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      change ((C.action n).toLinearMap ^ k)
        (C.action n (Finsupp.single b r)) = _
      rw [C.action_single, ih]
      rfl

/-- The linear permutation action has period `p`. -/
private theorem smith_action_pow_periodic
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p) (n : ℕ) :
    (C.action n).toLinearMap ^ p = 1 := by
  apply Finsupp.lhom_ext
  intro b r
  rw [smith_action_pow_single C]
  rw [C.actionBasis_periodic n]
  simp

/-- The norm is invariant under the cyclic action. -/
private theorem smith_action_norm
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) :
    C.action n (C.smithNorm n c) = C.smithNorm n c := by
  simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply]
  rw [map_sum]
  have hstep : ∀ k : ℕ,
      C.action n (((C.action n).toLinearMap ^ k) c) =
        ((C.action n).toLinearMap ^ (k + 1)) c := by
    intro k
    rw [pow_succ', Module.End.mul_apply]
    rfl
  simp_rw [hstep]
  apply add_right_cancel (b := c)
  have hshift :
      (∑ k ∈ Finset.range p,
          ((C.action n).toLinearMap ^ (k + 1)) c) + c =
        ∑ k ∈ Finset.range (p + 1),
          ((C.action n).toLinearMap ^ k) c := by
    simpa using (Finset.sum_range_succ'
      (fun k ↦ ((C.action n).toLinearMap ^ k) c) p).symm
  rw [hshift]
  rw [Finset.sum_range_succ]
  simp [smith_action_pow_periodic C n, add_comm]

/-- Coefficients transform contragrediently under the basis permutation. -/
private theorem smith_action_coeff_actionBasis
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (b : C.Basis n) :
    C.action n c (C.actionBasis n b) = c b := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a r c ha hr ihc =>
      rw [map_add, C.action_single, Finsupp.add_apply, Finsupp.add_apply, ihc]
      have hab : C.actionBasis n a = C.actionBasis n b ↔ a = b :=
        (C.actionBasis n).injective.eq_iff
      simp only [Finsupp.single_apply]
      by_cases h : a = b
      · simp [h]
      · simp [h, hab]

/-- One-step coefficient constancy for an invariant permutation chain. -/
private theorem smith_invariant_coeff_actionBasis
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (hc : C.tau n c = 0)
    (b : C.Basis n) : c (C.actionBasis n b) = c b := by
  have hact : C.action n c = c := by
    exact (sub_eq_zero.mp (by
      simpa [FiniteCyclicAugmentedComplex.tau] using hc)).symm
  rw [← smith_action_coeff_actionBasis C c b]
  exact congrFun (congrArg DFunLike.coe hact.symm) (C.actionBasis n b)

/-- An invariant chain has constant coefficients around every basis orbit. -/
private theorem smith_invariant_coeff_iterate
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (hc : C.tau n c = 0)
    (b : C.Basis n) (k : ℕ) :
    c (((C.actionBasis n) ^ k) b) = c b := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      change c (((C.actionBasis n) ^ k) (C.actionBasis n b)) = c b
      rw [ih, smith_invariant_coeff_actionBasis C c hc b]

/-- A nonfixed basis orbit has exactly prime period `p`. -/
private theorem smith_basisOrbit_injective
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b ≠ b) :
    Set.InjOn (fun k : ℕ ↦ ((C.actionBasis n) ^ k) b) (Set.Iio p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hper : Function.IsPeriodicPt (C.actionBasis n) p b := by
    change ((C.actionBasis n) ^ p) b = b
    rw [C.actionBasis_periodic n]
    rfl
  have hmin : Function.minimalPeriod (C.actionBasis n) b = p :=
    Function.minimalPeriod_eq_prime hper hb
  simpa [hmin] using
    (Function.iterate_injOn_Iio_minimalPeriod (f := C.actionBasis n) (x := b))

/-- Every positive Smith power has zero coefficient on fixed basis vectors. -/
private theorem smith_tau_pow_coeff_fixed
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b = b)
    (j : ℕ) (hj : 0 < j) (c : C.Chain n) :
    ((C.tau n) ^ j) c b = 0 := by
  induction j generalizing c with
  | zero => exact False.elim (Nat.lt_asymm hj hj)
  | succ j ih =>
      rw [pow_succ, Module.End.mul_apply]
      cases j with
      | zero =>
          simp only [pow_zero, Module.End.one_apply,
            FiniteCyclicAugmentedComplex.tau, LinearMap.sub_apply,
            LinearMap.id_apply]
          change c b - C.action n c b = 0
          rw [smith_action_coeff_of_fixedBasis C b hb]
          exact sub_self _
      | succ j =>
          exact ih (Nat.succ_pos j) (C.tau n c)

/-- The norm of one free-orbit basis vector has its original coefficient at
that vector. -/
private theorem smith_norm_single_self
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b ≠ b)
    (r : ZMod p) : C.smithNorm n (Finsupp.single b r) b = r := by
  classical
  simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply]
  change (Finsupp.applyAddHom b)
      (∑ k ∈ Finset.range p,
        ((C.action n).toLinearMap ^ k) (Finsupp.single b r)) = r
  rw [map_sum]
  simp_rw [smith_action_pow_single C]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkp : k < p := Finset.mem_range.mp hk
    have hne : ((C.actionBasis n) ^ k) b ≠ b := by
      intro heq
      exact hk0 ((smith_basisOrbit_injective hp C b hb) hkp hp.pos heq)
    change (Finsupp.single (((C.actionBasis n) ^ k) b) r) b = 0
    rw [Finsupp.single_apply, if_neg hne]
  · simp [hp.pos]

/-- Every orbit norm is invariant, hence killed by `1-T`. -/
private theorem smith_tau_norm_zero
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) :
    C.tau n (C.smithNorm n c) = 0 := by
  simp [FiniteCyclicAugmentedComplex.tau, smith_action_norm]

/-- The norm is also unchanged when the action is applied before it. -/
private theorem smith_norm_action
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) :
    C.smithNorm n (C.action n c) = C.smithNorm n c := by
  simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply]
  have hstep : ∀ k : ℕ,
      ((C.action n).toLinearMap ^ k) (C.action n c) =
        ((C.action n).toLinearMap ^ (k + 1)) c := by
    intro k
    rw [pow_succ, Module.End.mul_apply]
    rfl
  simp_rw [hstep]
  apply add_right_cancel (b := c)
  have hshift :
      (∑ k ∈ Finset.range p,
          ((C.action n).toLinearMap ^ (k + 1)) c) + c =
        ∑ k ∈ Finset.range (p + 1),
          ((C.action n).toLinearMap ^ k) c := by
    simpa using (Finset.sum_range_succ'
      (fun k ↦ ((C.action n).toLinearMap ^ k) c) p).symm
  rw [hshift, Finset.sum_range_succ]
  simp [smith_action_pow_periodic C n, add_comm]

/-- The norm kills every `1-T` image. -/
private theorem smith_norm_tau_zero
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) :
    C.smithNorm n (C.tau n c) = 0 := by
  simp [FiniteCyclicAugmentedComplex.tau, map_sub, smith_norm_action]

/-- The norm of a basis-fixed singleton is zero in characteristic `p`. -/
private theorem smith_norm_single_fixed_zero
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b = b)
    (r : ZMod p) : C.smithNorm n (Finsupp.single b r) = 0 := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  letI : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.ne_one
  simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply]
  have hpow : ∀ k : ℕ, ((C.actionBasis n) ^ k) b = b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        change ((C.actionBasis n) ^ k) (C.actionBasis n b) = b
        rw [hb, ih]
  simp_rw [smith_action_pow_single C, hpow]
  rw [Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
  rw [CharP.cast_eq_zero (ZMod p) p]
  simp

/-- The support of an orbit norm peeled from an invariant chain stays inside
the original support. -/
private theorem smith_norm_single_support_subset
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (hc : C.tau n c = 0)
    (b : C.Basis n) (hb : b ∈ c.support) :
    (C.smithNorm n (Finsupp.single b (c b))).support ⊆ c.support := by
  classical
  intro a ha
  apply Finsupp.mem_support_iff.mpr
  intro hca
  have hcb : c b ≠ 0 := Finsupp.mem_support_iff.mp hb
  have hne : ∀ k : ℕ, ((C.actionBasis n) ^ k) b ≠ a := by
    intro k heq
    have horbit := smith_invariant_coeff_iterate C c hc b k
    rw [heq, hca] at horbit
    exact hcb horbit.symm
  have hzero : C.smithNorm n (Finsupp.single b (c b)) a = 0 := by
    simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply]
    change (Finsupp.applyAddHom a)
      (∑ k ∈ Finset.range p,
        ((C.action n).toLinearMap ^ k) (Finsupp.single b (c b))) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    rw [smith_action_pow_single C]
    simp [hne k]
  exact Finsupp.mem_support_iff.mp ha hzero

private theorem smith_fixedChain_add_single
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} {c : C.Chain n} (hc : C.IsFixedChain c)
    (b : C.Basis n) (hb : C.actionBasis n b = b) (r : ZMod p) :
    C.IsFixedChain (c + Finsupp.single b r) := by
  intro a ha
  by_cases hab : a = b
  · simpa [hab] using hb
  · apply hc a
    apply Finsupp.mem_support_iff.mpr
    have hne := Finsupp.mem_support_iff.mp ha
    simpa [hab] using hne

/-- Every invariant chain splits into a fixed-basis chain and a norm-image
chain.  This is orbitwise constancy of coefficients. -/
private theorem smith_kernel_split_fixed
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (hctau : C.tau n c = 0) :
    ∃ cf ck : C.Chain n,
      C.IsFixedChain cf ∧ C.InSmithNorm ck ∧ c = cf + ck := by
  classical
  induction hcard : c.support.card using Nat.strong_induction_on generalizing c with
  | h m ih =>
      by_cases hc0 : c = 0
      · subst c
        exact ⟨0, 0, by simp [FiniteCyclicAugmentedComplex.IsFixedChain],
          ⟨0, by simp⟩, by simp⟩
      · have hsne : c.support.Nonempty := by
          simpa [Finset.nonempty_iff_ne_empty, Finsupp.support_eq_empty] using hc0
        obtain ⟨b, hb⟩ := hsne
        by_cases hbfix : C.actionBasis n b = b
        · let o : C.Chain n := Finsupp.single b (c b)
          let c' : C.Chain n := c - o
          have hotau : C.tau n o = 0 := by
            simp [o, FiniteCyclicAugmentedComplex.tau, C.action_single, hbfix]
          have hc'tau : C.tau n c' = 0 := by
            simp [c', map_sub, hctau, hotau]
          have hosub : o.support ⊆ c.support := by
            intro a ha
            have haeq : a = b := by
              by_contra hab
              exact Finsupp.mem_support_iff.mp ha (by simp [o, hab])
            simpa [haeq] using hb
          have hc'sub : c'.support ⊆ c.support := by
            intro a ha
            by_contra hac
            have hca : c a = 0 := by simpa [Finsupp.mem_support_iff] using hac
            have hoa : o a = 0 := by
              by_contra hao
              exact hac (hosub (Finsupp.mem_support_iff.mpr hao))
            exact Finsupp.mem_support_iff.mp ha (by simp [c', hca, hoa])
          have hcbnot : b ∉ c'.support := by
            simp [c', o]
          have hc'ss : c'.support ⊂ c.support := by
            exact Finset.ssubset_iff_subset_ne.mpr ⟨hc'sub, fun heq ↦
              hcbnot (heq.symm ▸ hb)⟩
          have hlt : c'.support.card < m := by
            rw [← hcard]
            exact Finset.card_lt_card hc'ss
          obtain ⟨cf, ck, hcf, hck, hc'eq⟩ := ih _ hlt c' hc'tau rfl
          refine ⟨cf + o, ck, ?_, hck, ?_⟩
          · exact smith_fixedChain_add_single C hcf b hbfix (c b)
          · have hco : c = c' + o := by simp [c']
            rw [hco, hc'eq]
            ac_rfl
        · let o : C.Chain n := C.smithNorm n (Finsupp.single b (c b))
          let c' : C.Chain n := c - o
          have hotau : C.tau n o = 0 := smith_tau_norm_zero C _
          have hc'tau : C.tau n c' = 0 := by
            simp [c', map_sub, hctau, hotau]
          have hosub : o.support ⊆ c.support :=
            smith_norm_single_support_subset C c hctau b hb
          have hc'sub : c'.support ⊆ c.support := by
            intro a ha
            by_contra hac
            have hca : c a = 0 := by simpa [Finsupp.mem_support_iff] using hac
            have hoa : o a = 0 := by
              by_contra hao
              exact hac (hosub (Finsupp.mem_support_iff.mpr hao))
            exact Finsupp.mem_support_iff.mp ha (by simp [c', hca, hoa])
          have hcbnot : b ∉ c'.support := by
            simp [Finsupp.mem_support_iff, c', o,
              smith_norm_single_self hp C b hbfix (c b)]
          have hc'ss : c'.support ⊂ c.support := by
            exact Finset.ssubset_iff_subset_ne.mpr ⟨hc'sub, fun heq ↦
              hcbnot (heq.symm ▸ hb)⟩
          have hlt : c'.support.card < m := by
            rw [← hcard]
            exact Finset.card_lt_card hc'ss
          obtain ⟨cf, ck, hcf, hck, hc'eq⟩ := ih _ hlt c' hc'tau rfl
          refine ⟨cf, ck + o, hcf, ?_, ?_⟩
          · exact (C.smithNorm n).range.add_mem hck
              ⟨Finsupp.single b (c b), rfl⟩
          · have hco : c = c' + o := by simp [c']
            rw [hco, hc'eq]
            ac_rfl

/-- Dually, a norm-killed chain splits into fixed support and an image of
`1-T`.  On every free orbit this is the elementary zero-sum telescoping
identity. -/
private theorem smith_action_coeff_symm
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (b : C.Basis n) :
    C.action n c b = c ((C.actionBasis n).symm b) := by
  simpa using smith_action_coeff_actionBasis C c ((C.actionBasis n).symm b)

private theorem smith_action_pow_coeff_symm
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n k : ℕ} (c : C.Chain n) (b : C.Basis n) :
    ((C.action n).toLinearMap ^ k) c b =
      c (((C.actionBasis n).symm ^ k) b) := by
  induction k generalizing c b with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih]
      change C.action n c (((C.actionBasis n).symm ^ k) b) = _
      rw [smith_action_coeff_symm C]
      rw [pow_succ']
      rfl

private theorem smith_norm_coeff
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (b : C.Basis n) :
    C.smithNorm n c b =
      ∑ k ∈ Finset.range p, c (((C.actionBasis n).symm ^ k) b) := by
  classical
  simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply]
  change (Finsupp.applyAddHom b)
      (∑ k ∈ Finset.range p, ((C.action n).toLinearMap ^ k) c) = _
  rw [map_sum]
  change (∑ k ∈ Finset.range p,
    ((C.action n).toLinearMap ^ k) c b) = _
  simp_rw [smith_action_pow_coeff_symm C]

private theorem smith_basisOrbit_symm_injective
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b ≠ b) :
    Set.InjOn (fun k : ℕ ↦ ((C.actionBasis n).symm ^ k) b) (Set.Iio p) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hper : Function.IsPeriodicPt (C.actionBasis n).symm p b := by
    change ((C.actionBasis n).symm ^ p) b = b
    have hs : (C.actionBasis n).symm ^ p = 1 := by
      simpa using congrArg Equiv.symm (C.actionBasis_periodic n)
    rw [hs]
    rfl
  have hb' : (C.actionBasis n).symm b ≠ b := by
    intro h
    apply hb
    have h' := congrArg (C.actionBasis n) h
    simpa using h'.symm
  have hmin : Function.minimalPeriod (C.actionBasis n).symm b = p :=
    Function.minimalPeriod_eq_prime hper hb'
  simpa [hmin] using
    (Function.iterate_injOn_Iio_minimalPeriod
      (f := (C.actionBasis n).symm) (x := b))

private noncomputable def smithOrbitPart
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (c : C.Chain n) : C.Chain n :=
  ∑ k ∈ Finset.range p,
    Finsupp.single (((C.actionBasis n).symm ^ k) b)
      (c (((C.actionBasis n).symm ^ k) b))

private theorem smith_orbitPart_self
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b ≠ b)
    (c : C.Chain n) : smithOrbitPart C b c b = c b := by
  classical
  unfold smithOrbitPart
  change (Finsupp.applyAddHom b)
      (∑ k ∈ Finset.range p,
        Finsupp.single (((C.actionBasis n).symm ^ k) b)
          (c (((C.actionBasis n).symm ^ k) b))) = c b
  rw [map_sum, Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkp : k < p := Finset.mem_range.mp hk
    have hne : ((C.actionBasis n).symm ^ k) b ≠ b := by
      intro heq
      exact hk0 ((smith_basisOrbit_symm_injective hp C b hb) hkp hp.pos heq)
    change (Finsupp.single (((C.actionBasis n).symm ^ k) b)
      (c (((C.actionBasis n).symm ^ k) b))) b = 0
    rw [Finsupp.single_apply, if_neg hne]
  · simp [hp.pos]

private theorem smith_orbitPart_support_subset
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (c : C.Chain n) :
    (smithOrbitPart C b c).support ⊆ c.support := by
  classical
  intro a ha
  apply Finsupp.mem_support_iff.mpr
  intro hca
  have hzero : smithOrbitPart C b c a = 0 := by
    unfold smithOrbitPart
    change (Finsupp.applyAddHom a)
      (∑ k ∈ Finset.range p,
        Finsupp.single (((C.actionBasis n).symm ^ k) b)
          (c (((C.actionBasis n).symm ^ k) b))) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases heq : ((C.actionBasis n).symm ^ k) b = a
    · subst a
      simp [hca]
    · change (Finsupp.single (((C.actionBasis n).symm ^ k) b)
        (c (((C.actionBasis n).symm ^ k) b))) a = 0
      rw [Finsupp.single_apply, if_neg heq]
  exact Finsupp.mem_support_iff.mp ha hzero

/-- A zero-norm free-orbit block is a `1-T` image.  The preimage uses suffix
sums around the orbit; the last coefficient closes because the total orbit
sum is zero. -/
private theorem smith_orbitPart_in_tau
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (b : C.Basis n) (hb : C.actionBasis n b ≠ b)
    (c : C.Chain n) (hcnorm : C.smithNorm n c = 0) :
    C.InSmithImage 1 (smithOrbitPart C b c) := by
  classical
  let σ := C.actionBasis n
  let a : ℕ → C.Basis n := fun k ↦ (σ.symm ^ k) b
  let r : ℕ → ZMod p := fun k ↦ c (a k)
  let s : ℕ → ZMod p := fun k ↦ ∑ j ∈ Finset.Ico k p, r j
  let x : C.Chain n :=
    ∑ k ∈ Finset.range p, Finsupp.single (a k) (s k)
  have hinvperiodic : σ.symm ^ p = 1 := by
    simpa [σ] using congrArg Equiv.symm (C.actionBasis_periodic n)
  have hinj : Set.InjOn a (Set.Iio p) := by
    simpa [a, σ] using smith_basisOrbit_symm_injective hp C b hb
  have hsum : ∑ k ∈ Finset.range p, r k = 0 := by
    have h := congrArg (fun z : C.Chain n ↦ z b) hcnorm
    simpa [smith_norm_coeff, r, a, σ] using h
  have hinvSucc : ∀ k, σ.symm (a k) = a (k + 1) := by
    intro k
    simp only [a]
    rw [pow_succ']
    rfl
  have hsigmaSucc : ∀ k, σ (a (k + 1)) = a k := by
    intro k
    rw [← hinvSucc]
    simp
  have hsigmaWrap : σ (a 0) = a (p - 1) := by
    have hmul : σ.symm ^ (p - 1) * σ.symm = 1 := by
      rw [← pow_succ]
      rw [Nat.sub_add_cancel hp.one_le, hinvperiodic]
    have hpow : σ.symm ^ (p - 1) = σ := by
      simpa using eq_inv_of_mul_eq_one_left hmul
    simp [a, hpow]
  have hinvWrap : σ.symm (a (p - 1)) = a 0 := by
    rw [hinvSucc]
    simp [a, Nat.sub_add_cancel hp.one_le, hinvperiodic]
  have hsigma_mem : ∀ k, k < p →
      ∃ j, j < p ∧ σ (a k) = a j := by
    intro k hk
    rcases k with _ | k
    · exact ⟨p - 1, Nat.sub_lt hp.pos Nat.zero_lt_one, hsigmaWrap⟩
    · exact ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk, hsigmaSucc k⟩
  have hcoeff : ∀ (v : ℕ → ZMod p) k, k < p →
      (∑ j ∈ Finset.range p, Finsupp.single (a j) (v j)) (a k) = v k := by
    intro v k hk
    change (Finsupp.applyAddHom (a k))
      (∑ j ∈ Finset.range p, Finsupp.single (a j) (v j)) = v k
    rw [map_sum, Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      have hjp := Finset.mem_range.mp hj
      have hne : a j ≠ a k := fun h ↦ hjk (hinj hjp hk h)
      change (Finsupp.single (a j) (v j)) (a k) = 0
      rw [Finsupp.single_apply, if_neg hne]
    · simp [hk]
  have hcoeff_out : ∀ (v : ℕ → ZMod p) y,
      (¬ ∃ k, k < p ∧ a k = y) →
      (∑ k ∈ Finset.range p, Finsupp.single (a k) (v k)) y = 0 := by
    intro v y hy
    change (Finsupp.applyAddHom y)
      (∑ k ∈ Finset.range p, Finsupp.single (a k) (v k)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : a k ≠ y := fun h ↦
      hy ⟨k, Finset.mem_range.mp hk, h⟩
    change (Finsupp.single (a k) (v k)) y = 0
    rw [Finsupp.single_apply, if_neg hne]
  refine ⟨x, ?_⟩
  simp only [pow_one]
  apply Finsupp.ext
  intro y
  simp only [FiniteCyclicAugmentedComplex.tau, LinearMap.sub_apply,
    LinearMap.id_apply]
  change x y - C.action n x y = smithOrbitPart C b c y
  rw [show C.action n x =
      ∑ k ∈ Finset.range p, Finsupp.single (σ (a k)) (s k) by
    simp only [x, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact C.action_single n (a k) (s k)]
  change
    (∑ k ∈ Finset.range p, Finsupp.single (a k) (s k)) y -
      (∑ k ∈ Finset.range p, Finsupp.single (σ (a k)) (s k)) y =
        (∑ k ∈ Finset.range p, Finsupp.single (a k) (r k)) y
  by_cases hy : ∃ k, k < p ∧ a k = y
  · obtain ⟨k, hkp, rfl⟩ := hy
    rw [hcoeff s k hkp, hcoeff r k hkp]
    by_cases hlast : k = p - 1
    · subst k
      have hsecond :
          (∑ j ∈ Finset.range p,
            Finsupp.single (σ (a j)) (s j)) (a (p - 1)) = s 0 := by
        change (Finsupp.applyAddHom (a (p - 1)))
          (∑ j ∈ Finset.range p,
            Finsupp.single (σ (a j)) (s j)) = s 0
        rw [map_sum, Finset.sum_eq_single 0]
        · simp [hsigmaWrap]
        · intro j hj hj0
          have hjp := Finset.mem_range.mp hj
          have hne : σ (a j) ≠ a (p - 1) := by
            intro heq
            have haj : a j = a 0 := by
              apply σ.injective
              simpa [hsigmaWrap] using heq
            exact hj0 (hinj hjp hp.pos haj)
          change (Finsupp.single (σ (a j)) (s j)) (a (p - 1)) = 0
          rw [Finsupp.single_apply, if_neg hne]
        · simp [hp.pos]
      rw [hsecond]
      have hs0 : s 0 = 0 := by simpa [s] using hsum
      have hsq : s (p - 1) = r (p - 1) := by
        rw [show s (p - 1) = ∑ j ∈ Finset.Ico (p - 1) p, r j by rfl]
        have hIco : Finset.Ico (p - 1) p = {p - 1} := by
          ext j
          simp only [Finset.mem_Ico, Finset.mem_singleton]
          omega
        rw [hIco]
        simp
      rw [hs0, hsq, sub_zero]
    · have hklt : k < p - 1 := by
          exact lt_of_le_of_ne (Nat.le_sub_one_of_lt hkp) hlast
      have hk1p : k + 1 < p := by omega
      have hsecond :
          (∑ j ∈ Finset.range p,
            Finsupp.single (σ (a j)) (s j)) (a k) = s (k + 1) := by
        change (Finsupp.applyAddHom (a k))
          (∑ j ∈ Finset.range p,
            Finsupp.single (σ (a j)) (s j)) = s (k + 1)
        rw [map_sum, Finset.sum_eq_single (k + 1)]
        · simp [hsigmaSucc]
        · intro j hj hjne
          have hjp := Finset.mem_range.mp hj
          have hne : σ (a j) ≠ a k := by
            intro heq
            have haj : a j = a (k + 1) := by
              apply σ.injective
              simpa [hsigmaSucc] using heq
            exact hjne (hinj hjp hk1p haj)
          change (Finsupp.single (σ (a j)) (s j)) (a k) = 0
          rw [Finsupp.single_apply, if_neg hne]
        · simp [hk1p]
      rw [hsecond]
      have hk_le : k ≤ p := hkp.le.trans (Nat.le_refl p)
      have hks_le : k + 1 ≤ p := Nat.succ_le_of_lt hkp
      rw [show s k = (∑ j ∈ Finset.range p, r j) -
          ∑ j ∈ Finset.range k, r j by
        simp [s, Finset.sum_Ico_eq_sub r hk_le]]
      rw [show s (k + 1) = (∑ j ∈ Finset.range p, r j) -
          ∑ j ∈ Finset.range (k + 1), r j by
        simp [s, Finset.sum_Ico_eq_sub r hks_le]]
      rw [Finset.sum_range_succ]
      abel
  · rw [hcoeff_out s y hy, hcoeff_out r y hy]
    have hyσ : ¬ ∃ k, k < p ∧ σ (a k) = y := by
      rintro ⟨k, hkp, hk⟩
      obtain ⟨j, hjp, hj⟩ := hsigma_mem k hkp
      exact hy ⟨j, hjp, hj.symm.trans hk⟩
    have hzero :
        (∑ k ∈ Finset.range p,
          Finsupp.single (σ (a k)) (s k)) y = 0 := by
      change (Finsupp.applyAddHom y)
        (∑ k ∈ Finset.range p,
          Finsupp.single (σ (a k)) (s k)) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro k hk
      have hne : σ (a k) ≠ y := fun h ↦
        hyσ ⟨k, Finset.mem_range.mp hk, h⟩
      change (Finsupp.single (σ (a k)) (s k)) y = 0
      rw [Finsupp.single_apply, if_neg hne]
    rw [hzero, sub_zero]

private theorem smith_norm_kernel_split_fixed
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (hcnorm : C.smithNorm n c = 0) :
    ∃ cf ck : C.Chain n,
      C.IsFixedChain cf ∧ C.InSmithImage 1 ck ∧ c = cf + ck := by
  classical
  induction hcard : c.support.card using Nat.strong_induction_on generalizing c with
  | h m ih =>
      by_cases hc0 : c = 0
      · subst c
        exact ⟨0, 0, by simp [FiniteCyclicAugmentedComplex.IsFixedChain],
          ⟨0, by simp⟩, by simp⟩
      · have hsne : c.support.Nonempty := by
          simpa [Finset.nonempty_iff_ne_empty, Finsupp.support_eq_empty] using hc0
        obtain ⟨b, hb⟩ := hsne
        by_cases hbfix : C.actionBasis n b = b
        · let o : C.Chain n := Finsupp.single b (c b)
          let c' : C.Chain n := c - o
          have honorm : C.smithNorm n o = 0 :=
            smith_norm_single_fixed_zero hp C b hbfix (c b)
          have hc'norm : C.smithNorm n c' = 0 := by
            simp [c', map_sub, hcnorm, honorm]
          have hosub : o.support ⊆ c.support := by
            intro a ha
            have haeq : a = b := by
              by_contra hab
              exact Finsupp.mem_support_iff.mp ha (by simp [o, hab])
            simpa [haeq] using hb
          have hc'sub : c'.support ⊆ c.support := by
            intro a ha
            by_contra hac
            have hca : c a = 0 := by simpa [Finsupp.mem_support_iff] using hac
            have hoa : o a = 0 := by
              by_contra hao
              exact hac (hosub (Finsupp.mem_support_iff.mpr hao))
            exact Finsupp.mem_support_iff.mp ha (by simp [c', hca, hoa])
          have hcbnot : b ∉ c'.support := by simp [c', o]
          have hc'ss : c'.support ⊂ c.support := by
            exact Finset.ssubset_iff_subset_ne.mpr ⟨hc'sub, fun heq ↦
              hcbnot (heq.symm ▸ hb)⟩
          have hlt : c'.support.card < m := by
            rw [← hcard]
            exact Finset.card_lt_card hc'ss
          obtain ⟨cf, ck, hcf, hck, hc'eq⟩ := ih _ hlt c' hc'norm rfl
          refine ⟨cf + o, ck, ?_, hck, ?_⟩
          · exact smith_fixedChain_add_single C hcf b hbfix (c b)
          · have hco : c = c' + o := by simp [c']
            rw [hco, hc'eq]
            ac_rfl
        · let o : C.Chain n := smithOrbitPart C b c
          let c' : C.Chain n := c - o
          have hoi : C.InSmithImage 1 o :=
            smith_orbitPart_in_tau hp C b hbfix c hcnorm
          rcases hoi with ⟨xo, hxo⟩
          have hxo' : C.tau n xo = o := by simpa using hxo
          have honorm : C.smithNorm n o = 0 := by
            rw [← hxo']
            exact smith_norm_tau_zero C xo
          have hc'norm : C.smithNorm n c' = 0 := by
            simp [c', map_sub, hcnorm, honorm]
          have hosub : o.support ⊆ c.support :=
            smith_orbitPart_support_subset C b c
          have hc'sub : c'.support ⊆ c.support := by
            intro a ha
            by_contra hac
            have hca : c a = 0 := by simpa [Finsupp.mem_support_iff] using hac
            have hoa : o a = 0 := by
              by_contra hao
              exact hac (hosub (Finsupp.mem_support_iff.mpr hao))
            exact Finsupp.mem_support_iff.mp ha (by simp [c', hca, hoa])
          have hcbnot : b ∉ c'.support := by
            simp [Finsupp.mem_support_iff, c', o,
              smith_orbitPart_self hp C b hbfix c]
          have hc'ss : c'.support ⊂ c.support := by
            exact Finset.ssubset_iff_subset_ne.mpr ⟨hc'sub, fun heq ↦
              hcbnot (heq.symm ▸ hb)⟩
          have hlt : c'.support.card < m := by
            rw [← hcard]
            exact Finset.card_lt_card hc'ss
          obtain ⟨cf, ck, hcf, hck, hc'eq⟩ := ih _ hlt c' hc'norm rfl
          refine ⟨cf, ck + o, hcf, ?_, ?_⟩
          · exact ((C.tau n) ^ 1).range.add_mem hck ⟨xo, hxo⟩
          · have hco : c = c' + o := by simp [c']
            rw [hco, hc'eq]
            ac_rfl

/-- The top Smith image has no nonzero fixed-basis chain. -/
private theorem smith_topImage_disjoint_fixed
    {p : ℕ} (hp : Nat.Prime p) (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n)
    (hci : C.InSmithImage (p - 1) c) (hcf : C.IsFixedChain c) :
    c = 0 := by
  rcases hci with ⟨x, rfl⟩
  apply Finsupp.ext
  intro b
  by_cases hbzero : ((C.tau n) ^ (p - 1)) x b = 0
  · simpa [hbzero]
  · have hbmem : b ∈ (((C.tau n) ^ (p - 1)) x).support :=
      Finsupp.mem_support_iff.mpr hbzero
    have hbfix := hcf b hbmem
    exact False.elim (hbzero
      (smith_tau_pow_coeff_fixed C b hbfix (p - 1)
        (Nat.sub_pos_of_lt hp.one_lt) x))

/-- Boundary commutes with every power of the Smith operator. -/
private theorem smith_boundary_image
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n j : ℕ} (c : C.Chain (n + 1))
    (hc : C.InSmithImage j c) :
    C.InSmithImage j (C.boundary n c) := by
  rcases hc with ⟨x, rfl⟩
  refine ⟨C.boundary n x, ?_⟩
  have htau : ∀ y : C.Chain (n + 1),
      C.boundary n (C.tau (n + 1) y) =
        C.tau n (C.boundary n y) := by
    intro y
    simp only [FiniteCyclicAugmentedComplex.tau, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub]
    congr 1
    simpa using C.boundary_equivariant n y
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      rw [← htau]
      exact ih (C.tau (n + 1) x)

private theorem smith_boundary_tau_eq
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain (n + 1)) :
    C.boundary n (C.tau (n + 1) c) =
      C.tau n (C.boundary n c) := by
  simp only [FiniteCyclicAugmentedComplex.tau, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub]
  congr 1
  exact C.boundary_equivariant n c

/-- Equivariant chain maps preserve every Smith image. -/
private theorem smith_map_image
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p} (f : C.Hom D)
    {n j : ℕ} (c : C.Chain n) (hc : C.InSmithImage j c) :
    D.InSmithImage j (f.map n c) := by
  rcases hc with ⟨x, rfl⟩
  refine ⟨f.map n x, ?_⟩
  have htau : ∀ y : C.Chain n,
      f.map n (C.tau n y) = D.tau n (f.map n y) := by
    intro y
    simp only [FiniteCyclicAugmentedComplex.tau, LinearMap.sub_apply,
      LinearMap.id_apply, map_sub]
    congr 1
    simpa using f.map_equivariant n y
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      rw [← htau]
      exact ih (C.tau n x)

private theorem smith_map_tau_eq
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p} (f : C.Hom D)
    {n : ℕ} (c : C.Chain n) :
    f.map n (C.tau n c) = D.tau n (f.map n c) := by
  simp only [FiniteCyclicAugmentedComplex.tau, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub]
  congr 1
  exact f.map_equivariant n c

private theorem smith_fixedChain_add
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} {c d : C.Chain n}
    (hc : C.IsFixedChain c) (hd : C.IsFixedChain d) :
    C.IsFixedChain (c + d) := by
  intro b hb
  by_cases hcb : c b = 0
  · apply hd b
    apply Finsupp.mem_support_iff.mpr
    have := Finsupp.mem_support_iff.mp hb
    simpa [hcb] using this
  · exact hc b (Finsupp.mem_support_iff.mpr hcb)

private theorem smith_fixedChain_smul
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} {c : C.Chain n} (hc : C.IsFixedChain c)
    (r : ZMod p) : C.IsFixedChain (r • c) := by
  intro b hb
  apply hc b
  apply Finsupp.mem_support_iff.mpr
  intro hcb
  exact Finsupp.mem_support_iff.mp hb (by simp [hcb])

private theorem smith_fixedChain_sub
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} {c d : C.Chain n}
    (hc : C.IsFixedChain c) (hd : C.IsFixedChain d) :
    C.IsFixedChain (c - d) := by
  rw [sub_eq_add_neg, ← neg_one_smul (ZMod p) d]
  exact smith_fixedChain_add C hc (smith_fixedChain_smul C hd (-1))

private theorem smith_action_eq_of_fixedChain
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (hc : C.IsFixedChain c) :
    C.action n c = c := by
  classical
  apply Finsupp.ext
  intro b
  by_cases hbfix : C.actionBasis n b = b
  · exact smith_action_coeff_of_fixedBasis C b hbfix c
  · have hcb : c b = 0 := by
      by_contra h
      exact hbfix (hc b (Finsupp.mem_support_iff.mpr h))
    rw [smith_action_coeff_symm C, hcb]
    have hcsymm : c ((C.actionBasis n).symm b) = 0 := by
      by_contra h
      have hsfix := hc ((C.actionBasis n).symm b)
        (Finsupp.mem_support_iff.mpr h)
      have := congrArg (C.actionBasis n) hsfix
      exact hbfix (by simpa using this)
    exact hcsymm

private theorem smith_tau_fixed_zero
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (hc : C.IsFixedChain c) :
    C.tau n c = 0 := by
  simp [FiniteCyclicAugmentedComplex.tau,
    smith_action_eq_of_fixedChain C c hc]

/-- Regularity makes fixed-support chains a subcomplex. -/
private theorem smith_boundary_fixed
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain (n + 1)) (hc : C.IsFixedChain c) :
    C.IsFixedChain (C.boundary n c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp [FiniteCyclicAugmentedComplex.IsFixedChain]
  | single_add b r c hbnot hr ih =>
      have hbmem : b ∈ (Finsupp.single b r + c).support := by
        apply Finsupp.mem_support_iff.mpr
        have hcb : c b = 0 := by
          by_contra hcb
          exact hbnot (Finsupp.mem_support_iff.mpr hcb)
        simpa [hcb] using hr
      have hbfix := hc b hbmem
      have hc' : C.IsFixedChain c := by
        intro a ha
        apply hc a
        apply Finsupp.mem_support_iff.mpr
        have hane := Finsupp.mem_support_iff.mp ha
        have hab : a ≠ b := by
          intro hab
          subst a
          exact hbnot (Finsupp.mem_support_iff.mpr hane)
        simpa [hab] using hane
      have ih' := ih hc'
      rw [map_add]
      apply smith_fixedChain_add C
      · rw [show Finsupp.single b r = r • Finsupp.single b 1 by simp]
        rw [map_smul]
        apply smith_fixedChain_smul C
        intro a ha
        exact C.regular_boundary n b hbfix a ha
      · exact ih'

private theorem smith_norm_coeff_fixed_zero
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n) (b : C.Basis n)
    (hb : C.actionBasis n b = b) : C.smithNorm n c b = 0 := by
  classical
  rw [smith_norm_coeff]
  have hbsymm : (C.actionBasis n).symm b = b := by
    apply (C.actionBasis n).injective
    simpa using hb.symm
  have hpow : ∀ k : ℕ, ((C.actionBasis n).symm ^ k) b = b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        change ((C.actionBasis n).symm ^ k) ((C.actionBasis n).symm b) = b
        rw [hbsymm, ih]
  simp_rw [hpow]
  rw [Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
  rw [ZMod.natCast_self]
  simp

private theorem smith_tauImage_disjoint_fixed
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n)
    (hci : C.InSmithImage 1 c) (hcf : C.IsFixedChain c) : c = 0 := by
  rcases hci with ⟨x, rfl⟩
  apply Finsupp.ext
  intro b
  by_cases hbzero : ((C.tau n) ^ 1) x b = 0
  · simpa [hbzero]
  · have hbmem : b ∈ (((C.tau n) ^ 1) x).support :=
      Finsupp.mem_support_iff.mpr hbzero
    have hbfix := hcf b hbmem
    exact False.elim (hbzero
      (smith_tau_pow_coeff_fixed C b hbfix 1 Nat.zero_lt_one x))

private theorem smith_normImage_disjoint_fixed
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain n)
    (hci : C.InSmithNorm c) (hcf : C.IsFixedChain c) : c = 0 := by
  rcases hci with ⟨x, rfl⟩
  apply Finsupp.ext
  intro b
  by_cases hbzero : C.smithNorm n x b = 0
  · simpa [hbzero]
  · have hbmem : b ∈ (C.smithNorm n x).support :=
      Finsupp.mem_support_iff.mpr hbzero
    exact False.elim (hbzero
      (smith_norm_coeff_fixed_zero C x b (hcf b hbmem)))

private theorem smith_boundary_norm_eq
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain (n + 1)) :
    C.boundary n (C.smithNorm (n + 1) c) =
      C.smithNorm n (C.boundary n c) := by
  have hpow : ∀ k : ℕ,
      C.boundary n (((C.action (n + 1)).toLinearMap ^ k) c) =
        ((C.action n).toLinearMap ^ k) (C.boundary n c) := by
    intro k
    induction k generalizing c with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        rw [ih]
        congr 1
        exact C.boundary_equivariant n _
  simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact hpow k

private theorem smith_map_norm_eq
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p} (f : C.Hom D)
    {n : ℕ} (c : C.Chain n) :
    f.map n (C.smithNorm n c) = D.smithNorm n (f.map n c) := by
  have hpow : ∀ k : ℕ,
      f.map n (((C.action n).toLinearMap ^ k) c) =
        ((D.action n).toLinearMap ^ k) (f.map n c) := by
    intro k
    induction k generalizing c with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        rw [ih]
        congr 1
        exact f.map_equivariant n _
  simp only [FiniteCyclicAugmentedComplex.smithNorm, LinearMap.sum_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact hpow k

private theorem smith_boundary_norm
    {p : ℕ} (C : FiniteCyclicAugmentedComplex p)
    {n : ℕ} (c : C.Chain (n + 1)) (hc : C.InSmithNorm c) :
    C.InSmithNorm (C.boundary n c) := by
  rcases hc with ⟨x, rfl⟩
  exact ⟨C.boundary n x, (smith_boundary_norm_eq C x).symm⟩

private theorem smith_map_norm
    {p : ℕ} {C D : FiniteCyclicAugmentedComplex p} (f : C.Hom D)
    {n : ℕ} (c : C.Chain n) (hc : C.InSmithNorm c) :
    D.InSmithNorm (f.map n c) := by
  rcases hc with ⟨x, rfl⟩
  exact ⟨f.map n x, (smith_map_norm_eq f x).symm⟩

/-!
The tempting one-map statement is deliberately *not* asserted: from
`f z = ∂c`, the Smith obstruction `(1-T)c` is a cycle in the target, not
generally the image of a source cycle.  It must be killed after passing to a
later refinement.  The finite tower below is the constructive form of the
usual pro-zero Čech argument.
-/

/-- The alternating exact pair `(1-T), norm` raises chain degree once at each
ambient-zero stage.  A complex bounded above by `N` therefore needs exactly
`N+1` refinement stages for the relative `H₀` chase. -/
private def smithH0TowerLength (_p N : ℕ) : ℕ := N + 1

/-- A coherent inverse tower of finite cyclic augmented complexes.  Larger
indices are finer, and `map n m` goes from level `m` to level `n`. -/
structure FiniteCyclicAugmentedTower (p : ℕ) where
  level : ℕ → FiniteCyclicAugmentedComplex p
  map : ∀ n m, n ≤ m → (level m).Hom (level n)
  map_refl : ∀ n q (c : (level n).Chain q),
    (map n n le_rfl).map q c = c
  map_zero_succ : ∀ k q (c : (level (k + 1)).Chain q),
    (map 0 (k + 1) (Nat.zero_le _)).map q c =
      (map 0 k (Nat.zero_le _)).map q
        ((map k (k + 1) (Nat.le_succ k)).map q c)

/-- Every adjacent refinement map through the required finite segment kills
all ambient reduced homology. -/
private def FiniteCyclicAugmentedTower.SmithAcyclicThrough
    {p : ℕ} (S : FiniteCyclicAugmentedTower p) (L : ℕ) : Prop :=
  ∀ i, i < L →
    (S.map i (i + 1) (Nat.le_succ i)).KillsReducedHomology

/-- Mutual obstruction chase for the alternating exact pair `1-T, norm`.
At height `k`, a degree-`d` obstruction reaches degree `d+k` at the bottom;
if that is above the bound, its top-to-bottom image bounds within the same
Smith image. -/
private theorem relative_smith_obstruction_chase
    {p N L : ℕ} (hp : Nat.Prime p)
    (S : FiniteCyclicAugmentedTower p)
    (hbottom : ∀ n, N < n → IsEmpty ((S.level 0).Basis n))
    (hacyclic : S.SmithAcyclicThrough L) :
    ∀ k, k ≤ L →
      (∀ d (z : (S.level k).Chain d), N < d + k →
        (S.level k).IsReducedCycle d z →
        (S.level k).InSmithImage 1 z →
        ∃ w : (S.level 0).Chain (d + 1),
          (S.level 0).InSmithImage 1 w ∧
          (S.level 0).boundary d w =
            (S.map 0 k (Nat.zero_le _)).map d z) ∧
      (∀ d (z : (S.level k).Chain d), N < d + k →
        (S.level k).IsReducedCycle d z →
        (S.level k).InSmithNorm z →
        ∃ w : (S.level 0).Chain (d + 1),
          (S.level 0).InSmithNorm w ∧
          (S.level 0).boundary d w =
            (S.map 0 k (Nat.zero_le _)).map d z) := by
  intro k
  induction k with
  | zero =>
      intro hkL
      constructor
      · intro d z hNd hzcycle hzimage
        letI : IsEmpty ((S.level 0).Basis d) := hbottom d hNd
        have hz0 : z = 0 := by
          apply Finsupp.ext
          intro b
          exact isEmptyElim b
        refine ⟨0, ⟨0, by simp⟩, ?_⟩
        rw [hz0]
        simp [S.map_refl]
      · intro d z hNd hzcycle hznorm
        letI : IsEmpty ((S.level 0).Basis d) := hbottom d hNd
        have hz0 : z = 0 := by
          apply Finsupp.ext
          intro b
          exact isEmptyElim b
        refine ⟨0, ⟨0, by simp⟩, ?_⟩
        rw [hz0]
        simp [S.map_refl]
  | succ k ih =>
      intro hkL
      have hkltL : k < L := Nat.lt_of_succ_le hkL
      have ihk := ih (Nat.le_trans (Nat.le_succ k) hkL)
      let f := S.map k (k + 1) (Nat.le_succ k)
      let g := S.map 0 k (Nat.zero_le k)
      let h := S.map 0 (k + 1) (Nat.zero_le (k + 1))
      constructor
      · intro d z hNdk hzcycle hzimage
        obtain ⟨c, hc⟩ := (hacyclic k hkltL) d z hzcycle
        let y : (S.level k).Chain (d + 1) :=
          (S.level k).smithNorm (d + 1) c
        have hynorm : (S.level k).InSmithNorm y := ⟨c, rfl⟩
        have hycycle : (S.level k).IsReducedCycle (d + 1) y := by
          change (S.level k).boundary d y = 0
          rw [show (S.level k).boundary d y =
              (S.level k).smithNorm d ((S.level k).boundary d c) by
            exact smith_boundary_norm_eq (S.level k) c]
          rw [hc]
          have hfimage := smith_map_image f z hzimage
          rcases hfimage with ⟨q, hq⟩
          rw [← hq]
          exact smith_norm_tau_zero (S.level k) q
        obtain ⟨e, henorm, he⟩ := ihk.2 (d + 1) y (by omega)
          hycycle hynorm
        rcases henorm with ⟨q, hq⟩
        let u : (S.level 0).Chain (d + 1) :=
          g.map (d + 1) c - (S.level 0).boundary (d + 1) q
        have hnormeq :
            (S.level 0).smithNorm (d + 1)
                ((S.level 0).boundary (d + 1) q) =
              (S.level 0).smithNorm (d + 1) (g.map (d + 1) c) := by
          calc
            (S.level 0).smithNorm (d + 1)
                ((S.level 0).boundary (d + 1) q) =
                (S.level 0).boundary (d + 1)
                  ((S.level 0).smithNorm (d + 2) q) :=
              (smith_boundary_norm_eq (S.level 0) q).symm
            _ = (S.level 0).boundary (d + 1) e := by
              simpa [Nat.add_assoc] using
                congrArg ((S.level 0).boundary (d + 1)) hq
            _ = g.map (d + 1) y := he
            _ = (S.level 0).smithNorm (d + 1) (g.map (d + 1) c) :=
              smith_map_norm_eq g c
        have hunorm : (S.level 0).smithNorm (d + 1) u = 0 := by
          dsimp [u]
          rw [map_sub, hnormeq, sub_self]
        obtain ⟨cf, ck, hcf, hck, hueq⟩ :=
          smith_norm_kernel_split_fixed hp (S.level 0) u hunorm
        have huboundary :
            (S.level 0).boundary d u = h.map d z := by
          calc
            (S.level 0).boundary d u =
                (S.level 0).boundary d (g.map (d + 1) c) -
                  (S.level 0).boundary d
                    ((S.level 0).boundary (d + 1) q) := by
              dsimp [u]
              rw [map_sub]
            _ = g.map d ((S.level k).boundary d c) - 0 := by
              rw [← g.map_boundary, (S.level 0).boundary_boundary]
            _ = g.map d (f.map d z) := by rw [hc, sub_zero]
            _ = h.map d z := by
              exact (S.map_zero_succ k d z).symm
        have htimage : (S.level 0).InSmithImage 1 (h.map d z) :=
          smith_map_image h z hzimage
        have hckboundary : (S.level 0).InSmithImage 1
            ((S.level 0).boundary d ck) :=
          smith_boundary_image (S.level 0) ck hck
        have hcfboundary : (S.level 0).IsFixedChain
            ((S.level 0).boundary d cf) :=
          smith_boundary_fixed (S.level 0) cf hcf
        have hdecomp : h.map d z =
            (S.level 0).boundary d cf + (S.level 0).boundary d ck := by
          rw [← huboundary, hueq, map_add]
        have hcfrange : (S.level 0).InSmithImage 1
            ((S.level 0).boundary d cf) := by
          have heq : (S.level 0).boundary d cf =
              h.map d z - (S.level 0).boundary d ck := by
            rw [hdecomp]
            abel
          rw [heq]
          exact ((S.level 0).tau d ^ 1).range.sub_mem htimage hckboundary
        have hcfzero : (S.level 0).boundary d cf = 0 :=
          smith_tauImage_disjoint_fixed (S.level 0) _ hcfrange hcfboundary
        refine ⟨ck, hck, ?_⟩
        rw [hdecomp, hcfzero, zero_add]
      · intro d z hNdk hzcycle hznorm
        obtain ⟨c, hc⟩ := (hacyclic k hkltL) d z hzcycle
        let y : (S.level k).Chain (d + 1) := (S.level k).tau (d + 1) c
        have hyimage : (S.level k).InSmithImage 1 y :=
          ⟨c, by simp [y]⟩
        have hycycle : (S.level k).IsReducedCycle (d + 1) y := by
          change (S.level k).boundary d y = 0
          rw [show (S.level k).boundary d y =
              (S.level k).tau d ((S.level k).boundary d c) by
            exact smith_boundary_tau_eq (S.level k) c]
          rw [hc]
          have hfnorm := smith_map_norm f z hznorm
          rcases hfnorm with ⟨q, hq⟩
          rw [← hq]
          exact smith_tau_norm_zero (S.level k) q
        obtain ⟨e, heimage, he⟩ := ihk.1 (d + 1) y (by omega)
          hycycle hyimage
        rcases heimage with ⟨q, hq⟩
        let u : (S.level 0).Chain (d + 1) :=
          g.map (d + 1) c - (S.level 0).boundary (d + 1) q
        have htaueq :
            (S.level 0).tau (d + 1)
                ((S.level 0).boundary (d + 1) q) =
              (S.level 0).tau (d + 1) (g.map (d + 1) c) := by
          calc
            (S.level 0).tau (d + 1)
                ((S.level 0).boundary (d + 1) q) =
                (S.level 0).boundary (d + 1)
                  ((S.level 0).tau (d + 2) q) :=
              (smith_boundary_tau_eq (S.level 0) q).symm
            _ = (S.level 0).boundary (d + 1) e := by
              have hq' : (S.level 0).tau (d + 2) q = e := by
                simpa [Nat.add_assoc] using hq
              rw [hq']
            _ = g.map (d + 1) y := he
            _ = (S.level 0).tau (d + 1) (g.map (d + 1) c) :=
              smith_map_tau_eq g c
        have hutau : (S.level 0).tau (d + 1) u = 0 := by
          dsimp [u]
          rw [map_sub, htaueq, sub_self]
        obtain ⟨cf, ck, hcf, hck, hueq⟩ :=
          smith_kernel_split_fixed hp (S.level 0) u hutau
        have huboundary :
            (S.level 0).boundary d u = h.map d z := by
          calc
            (S.level 0).boundary d u =
                (S.level 0).boundary d (g.map (d + 1) c) -
                  (S.level 0).boundary d
                    ((S.level 0).boundary (d + 1) q) := by
              dsimp [u]
              rw [map_sub]
            _ = g.map d ((S.level k).boundary d c) - 0 := by
              rw [← g.map_boundary, (S.level 0).boundary_boundary]
            _ = g.map d (f.map d z) := by rw [hc, sub_zero]
            _ = h.map d z := by
              exact (S.map_zero_succ k d z).symm
        have htnorm : (S.level 0).InSmithNorm (h.map d z) :=
          smith_map_norm h z hznorm
        have hckboundary : (S.level 0).InSmithNorm
            ((S.level 0).boundary d ck) :=
          smith_boundary_norm (S.level 0) ck hck
        have hcfboundary : (S.level 0).IsFixedChain
            ((S.level 0).boundary d cf) :=
          smith_boundary_fixed (S.level 0) cf hcf
        have hdecomp : h.map d z =
            (S.level 0).boundary d cf + (S.level 0).boundary d ck := by
          rw [← huboundary, hueq, map_add]
        have hcfrange : (S.level 0).InSmithNorm
            ((S.level 0).boundary d cf) := by
          have heq : (S.level 0).boundary d cf =
              h.map d z - (S.level 0).boundary d ck := by
            rw [hdecomp]
            abel
          rw [heq]
          exact (S.level 0).smithNorm d |>.range.sub_mem htnorm hckboundary
        have hcfzero : (S.level 0).boundary d cf = 0 :=
          smith_normImage_disjoint_fixed (S.level 0) _ hcfrange hcfboundary
        refine ⟨ck, hck, ?_⟩
        rw [hdecomp, hcfzero, zero_add]

/-- Finite relative Smith `H₀` lemma.  The bottom complex is bounded in
degree `N`; after `N+1` ambient pro-zero stages, the alternating exact pair
`1-T, norm` forces the top-to-bottom map on regular fixed reduced `H₀` to
vanish. -/
private theorem relative_smith_H0_tower
    {p N : ℕ} (hp : Nat.Prime p)
    (S : FiniteCyclicAugmentedTower p)
    (hbottom : ∀ n, N < n → IsEmpty ((S.level 0).Basis n))
    (hacyclic : S.SmithAcyclicThrough (smithH0TowerLength p N))
    (z : (S.level (smithH0TowerLength p N)).Chain 0)
    (hzfixed : (S.level (smithH0TowerLength p N)).IsFixedChain z)
    (hzaug : (S.level (smithH0TowerLength p N)).augment z = 0) :
    ∃ w : (S.level 0).Chain 1, (S.level 0).IsFixedChain w ∧
      (S.level 0).boundary 0 w =
        (S.map 0 (smithH0TowerLength p N) (Nat.zero_le _)).map 0 z := by
  let f := S.map N (N + 1) (Nat.le_succ N)
  let g := S.map 0 N (Nat.zero_le N)
  let h := S.map 0 (N + 1) (Nat.zero_le (N + 1))
  have hzcycle : (S.level (N + 1)).IsReducedCycle 0 z := by
    simpa [smithH0TowerLength] using hzaug
  obtain ⟨c, hc⟩ := (hacyclic N (by simp [smithH0TowerLength])) 0 z
    hzcycle
  have hfzfixed : (S.level N).IsFixedChain (f.map 0 z) :=
    f.map_fixed 0 z (by simpa [smithH0TowerLength] using hzfixed)
  let y : (S.level N).Chain 1 := (S.level N).tau 1 c
  have hyimage : (S.level N).InSmithImage 1 y := ⟨c, by simp [y]⟩
  have hycycle : (S.level N).IsReducedCycle 1 y := by
    change (S.level N).boundary 0 y = 0
    rw [show (S.level N).boundary 0 y =
        (S.level N).tau 0 ((S.level N).boundary 0 c) by
      exact smith_boundary_tau_eq (S.level N) c]
    rw [hc]
    exact smith_tau_fixed_zero (S.level N) (f.map 0 z) hfzfixed
  have hchase :=
    (relative_smith_obstruction_chase hp S hbottom hacyclic N
      (by simp [smithH0TowerLength])).1
  obtain ⟨e, heimage, he⟩ := hchase 1 y (by omega) hycycle hyimage
  rcases heimage with ⟨q, hq⟩
  have hq' : (S.level 0).tau 2 q = e := by simpa using hq
  let u : (S.level 0).Chain 1 :=
    g.map 1 c - (S.level 0).boundary 1 q
  have htaueq :
      (S.level 0).tau 1 ((S.level 0).boundary 1 q) =
        (S.level 0).tau 1 (g.map 1 c) := by
    calc
      (S.level 0).tau 1 ((S.level 0).boundary 1 q) =
          (S.level 0).boundary 1 ((S.level 0).tau 2 q) :=
        (smith_boundary_tau_eq (S.level 0) q).symm
      _ = (S.level 0).boundary 1 e := by rw [hq']
      _ = g.map 1 y := he
      _ = (S.level 0).tau 1 (g.map 1 c) := smith_map_tau_eq g c
  have hutau : (S.level 0).tau 1 u = 0 := by
    dsimp [u]
    rw [map_sub, htaueq, sub_self]
  obtain ⟨cf, ck, hcf, hck, hueq⟩ :=
    smith_kernel_split_fixed hp (S.level 0) u hutau
  have huboundary : (S.level 0).boundary 0 u = h.map 0 z := by
    calc
      (S.level 0).boundary 0 u =
          (S.level 0).boundary 0 (g.map 1 c) -
            (S.level 0).boundary 0 ((S.level 0).boundary 1 q) := by
        dsimp [u]
        rw [map_sub]
      _ = g.map 0 ((S.level N).boundary 0 c) - 0 := by
        rw [← g.map_boundary, (S.level 0).boundary_boundary]
      _ = g.map 0 (f.map 0 z) := by rw [hc, sub_zero]
      _ = h.map 0 z := by
        exact (S.map_zero_succ N 0 z).symm
  have htargetFixed : (S.level 0).IsFixedChain (h.map 0 z) :=
    h.map_fixed 0 z (by simpa [smithH0TowerLength] using hzfixed)
  have hcfboundary : (S.level 0).IsFixedChain
      ((S.level 0).boundary 0 cf) :=
    smith_boundary_fixed (S.level 0) cf hcf
  have hckboundaryNorm : (S.level 0).InSmithNorm
      ((S.level 0).boundary 0 ck) :=
    smith_boundary_norm (S.level 0) ck hck
  have hdecomp : h.map 0 z =
      (S.level 0).boundary 0 cf + (S.level 0).boundary 0 ck := by
    rw [← huboundary, hueq, map_add]
  have hckboundaryFixed : (S.level 0).IsFixedChain
      ((S.level 0).boundary 0 ck) := by
    have heq : (S.level 0).boundary 0 ck =
        h.map 0 z - (S.level 0).boundary 0 cf := by
      rw [hdecomp]
      abel
    rw [heq]
    exact smith_fixedChain_sub (S.level 0) htargetFixed hcfboundary
  have hckzero : (S.level 0).boundary 0 ck = 0 :=
    smith_normImage_disjoint_fixed (S.level 0) _
      hckboundaryNorm hckboundaryFixed
  refine ⟨cf, hcf, ?_⟩
  have hfinal : (S.level 0).boundary 0 cf = h.map 0 z := by
    have hh : h.map 0 z = (S.level 0).boundary 0 cf := by
      simpa [hckzero] using hdecomp
    exact hh.symm
  simpa [h, smithH0TowerLength] using hfinal

/-! ## Topological realization obligations -/

/-- A finite open cover together with the permutation induced by a periodic
homeomorphism.  Keeping the cover in the data prevents the algebraic tower
from becoming detached from the topology it is meant to approximate. -/
private structure FiniteInvariantCover
    {X : Type*} [TopologicalSpace X] (V : X ≃ₜ X) (p : ℕ) where
  Index : Type
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  set : Index → Set X
  isOpen_set : ∀ i, IsOpen (set i)
  nonempty_set : ∀ i, (set i).Nonempty
  covers : Set.univ ⊆ ⋃ i, set i
  action : Equiv.Perm Index
  action_periodic : action ^ p = 1
  equivariant : ∀ i, V '' set i = set (action i)

attribute [instance] FiniteInvariantCover.indexFintype
attribute [instance] FiniteInvariantCover.indexDecidableEq

/-- An ordinary finite open cover.  This intentionally carries no action:
arc-likeness first produces such a cover, and equivariance is imposed only by
the separate cyclic common-refinement construction below. -/
private structure FiniteOpenCover (X : Type*) [TopologicalSpace X] where
  Index : Type
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  set : Index → Set X
  isOpen_set : ∀ i, IsOpen (set i)
  nonempty_set : ∀ i, (set i).Nonempty
  covers : Set.univ ⊆ ⋃ i, set i

attribute [instance] FiniteOpenCover.indexFintype
attribute [instance] FiniteOpenCover.indexDecidableEq

/-- Forget the action on an invariant cover without changing its indexed open
sets. -/
private def FiniteInvariantCover.toOpenCover
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : FiniteOpenCover X where
  Index := U.Index
  indexFintype := U.indexFintype
  indexDecidableEq := U.indexDecidableEq
  set := U.set
  isOpen_set := U.isOpen_set
  nonempty_set := U.nonempty_set
  covers := U.covers

private def FiniteOpenCover.IsNerveFace
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X)
    (s : Finset U.Index) : Prop :=
  s.Nonempty ∧ (⋂ i ∈ s, U.set i).Nonempty

private def FiniteOpenCover.NerveFace
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X) :=
  {s : Finset U.Index // U.IsNerveFace s}

private instance FiniteOpenCover.nerveFacePartialOrder
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X) :
    PartialOrder U.NerveFace := by
  unfold FiniteOpenCover.NerveFace
  infer_instance

private noncomputable instance FiniteOpenCover.nerveFaceFintype
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X) :
    Fintype U.NerveFace := by
  classical
  unfold FiniteOpenCover.NerveFace
  infer_instance

private noncomputable instance FiniteOpenCover.nerveFaceDecidableEq
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X) :
    DecidableEq U.NerveFace := Classical.decEq _

private noncomputable def FiniteOpenCover.smithComplex
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X) (p : ℕ) :
    FiniteCyclicAugmentedComplex p :=
  finiteTrivialAugmentedComplexOfPoset p U.NerveFace

/-- A nonequivariant refinement between ordinary finite covers. -/
private structure FiniteOpenCover.Refinement
    {X : Type*} [TopologicalSpace X]
    (fine coarse : FiniteOpenCover X) where
  indexMap : fine.Index → coarse.Index
  subordinate : ∀ i, fine.set i ⊆ coarse.set (indexMap i)

private noncomputable def FiniteOpenCover.Refinement.faceOrderHom
    {X : Type*} [TopologicalSpace X] {fine coarse : FiniteOpenCover X}
    (r : fine.Refinement coarse) : fine.NerveFace →o coarse.NerveFace where
  toFun s := ⟨s.1.image r.indexMap, by
    refine ⟨s.2.1.image r.indexMap, ?_⟩
    rcases s.2.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter] at hx ⊢
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact r.subordinate i (hx i hi)⟩
  monotone' := by
    intro a b hab
    exact Finset.image_mono r.indexMap hab

private noncomputable def FiniteOpenCover.Refinement.underlyingHom
    {X : Type*} [TopologicalSpace X] {fine coarse : FiniteOpenCover X}
    {p : ℕ} (r : fine.Refinement coarse) :
    (fine.smithComplex p).UnderlyingHom (coarse.smithComplex p) :=
  posetStrictUnderlyingHom r.faceOrderHom

private def FiniteOpenCover.Refinement.trans
    {X : Type*} [TopologicalSpace X]
    {fine middle coarse : FiniteOpenCover X}
    (r : fine.Refinement middle) (s : middle.Refinement coarse) :
    fine.Refinement coarse where
  indexMap := s.indexMap ∘ r.indexMap
  subordinate := fun i ↦ (r.subordinate i).trans (s.subordinate (r.indexMap i))

private theorem FiniteOpenCover.Refinement.faceOrderHom_trans
    {X : Type*} [TopologicalSpace X]
    {fine middle coarse : FiniteOpenCover X}
    (r : fine.Refinement middle) (s : middle.Refinement coarse) :
    (r.trans s).faceOrderHom = s.faceOrderHom.comp r.faceOrderHom := by
  apply OrderHom.ext
  funext a
  apply Subtype.ext
  simp [FiniteOpenCover.Refinement.faceOrderHom,
    FiniteOpenCover.Refinement.trans, Finset.image_image, Function.comp_def]

/-- Two refinement choices are contiguous when the union of their images of
every source nerve face is again a target nerve face. -/
private def FiniteOpenCover.Refinement.Contiguous
    {X : Type*} [TopologicalSpace X] {fine coarse : FiniteOpenCover X}
    (r s : fine.Refinement coarse) : Prop :=
  ∀ a : fine.NerveFace,
    coarse.IsNerveFace (a.1.image r.indexMap ∪ a.1.image s.indexMap)

private theorem FiniteOpenCover.Refinement.contiguous
    {X : Type*} [TopologicalSpace X] {fine coarse : FiniteOpenCover X}
    (r s : fine.Refinement coarse) : r.Contiguous s := by
  intro a
  refine ⟨a.2.1.image r.indexMap |>.mono Finset.subset_union_left, ?_⟩
  rcases a.2.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact r.subordinate i (hx i hi)
  · rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact s.subordinate i (hx i hi)

private noncomputable def FiniteOpenCover.Refinement.commonUpperFaceOrderHom
    {X : Type*} [TopologicalSpace X] {fine coarse : FiniteOpenCover X}
    {r s : fine.Refinement coarse} (h : r.Contiguous s) :
    fine.NerveFace →o coarse.NerveFace where
  toFun a := ⟨a.1.image r.indexMap ∪ a.1.image s.indexMap, h a⟩
  monotone' := by
    intro a b hab
    exact Finset.union_subset_union
      (Finset.image_mono r.indexMap hab) (Finset.image_mono s.indexMap hab)

/-- Cover contiguity is converted into the explicit normalized-prism
homotopy.  The real algebraic content is isolated in
`posetStrictUnderlyingHom_reducedChainHomotopy_of_commonUpperBound`. -/
private theorem FiniteOpenCover.Refinement.contiguous_reducedChainHomotopy
    {X : Type*} [TopologicalSpace X] {fine coarse : FiniteOpenCover X}
    {p : ℕ} {r s : fine.Refinement coarse} (h : r.Contiguous s) :
    Nonempty (PosetNerve.StrictReducedChainHomotopy p
      r.faceOrderHom s.faceOrderHom) := by
  let k := r.commonUpperFaceOrderHom h
  have hr : ∀ a, r.faceOrderHom a ≤ k a := by
    intro a
    exact Finset.subset_union_left
  have hs : ∀ a, s.faceOrderHom a ≤ k a := by
    intro a
    exact Finset.subset_union_right
  exact posetNerve_strictReducedChainHomotopy_of_commonUpperBound
    r.faceOrderHom s.faceOrderHom k hr hs

private def FiniteInvariantCover.IsNerveFace
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (s : Finset U.Index) : Prop :=
  s.Nonempty ∧ (⋂ i ∈ s, U.set i).Nonempty

/-- The finite face poset of the full nerve. -/
private def FiniteInvariantCover.NerveFace
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) :=
  {s : Finset U.Index // U.IsNerveFace s}

private instance FiniteInvariantCover.nerveFacePartialOrder
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : PartialOrder U.NerveFace := by
  unfold FiniteInvariantCover.NerveFace
  infer_instance

private noncomputable instance FiniteInvariantCover.nerveFaceFintype
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : Fintype U.NerveFace := by
  classical
  unfold FiniteInvariantCover.NerveFace
  infer_instance

private noncomputable instance FiniteInvariantCover.nerveFaceDecidableEq
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : DecidableEq U.NerveFace :=
  Classical.decEq _

private theorem FiniteInvariantCover.isNerveFace_image_action
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) {s : Finset U.Index}
    (hs : U.IsNerveFace s) : U.IsNerveFace (s.image U.action) := by
  classical
  refine ⟨hs.1.image U.action, ?_⟩
  rcases hs.2 with ⟨x, hx⟩
  refine ⟨V x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro j hj
  rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
  rw [← U.equivariant i]
  exact ⟨x, hx i hi, rfl⟩

private theorem FiniteInvariantCover.isNerveFace_image_action_symm
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) {s : Finset U.Index}
    (hs : U.IsNerveFace s) : U.IsNerveFace (s.image U.action.symm) := by
  classical
  refine ⟨hs.1.image U.action.symm, ?_⟩
  rcases hs.2 with ⟨x, hx⟩
  refine ⟨V.symm x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro j hj
  rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
  have hximage : x ∈ V '' U.set (U.action.symm i) := by
    rw [U.equivariant, U.action.apply_symm_apply]
    exact hx i hi
  rcases hximage with ⟨y, hy, hyx⟩
  simpa [← hyx] using hy

private noncomputable def FiniteInvariantCover.faceActionEquiv
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : Equiv.Perm U.NerveFace where
  toFun s := ⟨s.1.image U.action, U.isNerveFace_image_action s.2⟩
  invFun s :=
    ⟨s.1.image U.action.symm, U.isNerveFace_image_action_symm s.2⟩
  left_inv s := by
    apply Subtype.ext
    simp [Finset.image_image]
  right_inv s := by
    apply Subtype.ext
    simp [Finset.image_image]

private noncomputable def FiniteInvariantCover.faceActionOrderIso
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : U.NerveFace ≃o U.NerveFace where
  toEquiv := U.faceActionEquiv
  map_rel_iff' := by
    intro a b
    change a.1.image U.action ⊆ b.1.image U.action ↔ a.1 ⊆ b.1
    exact Finset.image_subset_image_iff U.action.injective

private theorem FiniteInvariantCover.faceActionOrderIso_pow_apply
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (k : ℕ) (s : U.NerveFace) :
    ((((U.faceActionOrderIso).toEquiv : Equiv.Perm U.NerveFace) ^ k) s).1 =
      s.1.image (U.action ^ k) := by
  classical
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      change (((U.faceActionOrderIso.toEquiv : Equiv.Perm U.NerveFace) ^ k)
        (U.faceActionOrderIso s)).1 = _
      rw [ih]
      simp [FiniteInvariantCover.faceActionOrderIso,
        FiniteInvariantCover.faceActionEquiv, Finset.image_image,
        Function.comp_def]

private theorem FiniteInvariantCover.faceActionOrderIso_periodic
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) :
    (U.faceActionOrderIso.toEquiv : Equiv.Perm U.NerveFace) ^ p = 1 := by
  apply Equiv.ext
  intro s
  apply Subtype.ext
  rw [U.faceActionOrderIso_pow_apply, U.action_periodic]
  simp

/-- The ordered barycentric `n`-simplices of the full nerve: nonempty nerve
faces in a strictly increasing inclusion chain. -/
private def FiniteInvariantCover.BarycentricBasis
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (n : ℕ) :=
  {q : Fin (n + 1) → Finset U.Index //
    (∀ j, U.IsNerveFace (q j)) ∧
      ∀ i j, i < j → q i ⊂ q j}

private noncomputable def FiniteInvariantCover.smithComplex
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : FiniteCyclicAugmentedComplex p :=
  finiteCyclicAugmentedComplexOfPoset p U.NerveFace
    U.faceActionOrderIso U.faceActionOrderIso_periodic

private noncomputable def FiniteInvariantCover.strictChainsEquivBarycentricBasis
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (n : ℕ) :
    PosetNerve.strictChains U.NerveFace n ≃ U.BarycentricBasis n where
  toFun q :=
    ⟨fun j ↦ (q.1 j).1,
      ⟨fun j ↦ (q.1 j).2, fun i j hij ↦ q.2 hij⟩⟩
  invFun q :=
    ⟨fun j ↦ ⟨q.1 j, q.2.1 j⟩,
      fun i j hij ↦ q.2.2 i j hij⟩
  left_inv q := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

/-- In degree zero the two vertices occurring in the boundary of a strict
one-simplex are comparable nerve faces.  This is the only boundary-level
realization fact needed by the fixed-`H₀` separator below. -/
private theorem FiniteInvariantCover.strictBoundary_zero_support_comparable
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p)
    (b : PosetNerve.strictChains U.NerveFace 1)
    (a a' : PosetNerve.strictChains U.NerveFace 0)
    (ha : a ∈ (PosetNerve.strictBoundary U.NerveFace (ZMod p) 0
      (Finsupp.single b 1)).support)
    (ha' : a' ∈ (PosetNerve.strictBoundary U.NerveFace (ZMod p) 0
      (Finsupp.single b 1)).support) :
    ((U.strictChainsEquivBarycentricBasis 0 a).1 0 ⊆
        (U.strictChainsEquivBarycentricBasis 0 a').1 0) ∨
      ((U.strictChainsEquivBarycentricBasis 0 a').1 0 ⊆
        (U.strictChainsEquivBarycentricBasis 0 a).1 0) := by
  classical
  rw [PosetNerve.strictBoundary_single] at ha ha'
  have haFace := Finsupp.support_finsetSum ha
  have haFace' := Finsupp.support_finsetSum ha'
  rw [Finset.mem_biUnion] at haFace haFace'
  obtain ⟨i, -, hai⟩ := haFace
  obtain ⟨i', -, hai'⟩ := haFace'
  have hae : a = PosetNerve.strictChainFace U.NerveFace b i := by
    by_contra hne
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne] at hai
  have hae' : a' = PosetNerve.strictChainFace U.NerveFace b i' := by
    by_contra hne
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne] at hai'
  subst a
  subst a'
  fin_cases i <;> fin_cases i'
  · exact Or.inl (by rfl)
  · exact Or.inr (b.2 (by decide)).le
  · exact Or.inl (b.2 (by decide)).le
  · exact Or.inl (by rfl)

/-- A refinement is subordinate and equivariant on cover indices. -/
private structure FiniteInvariantCover.Refinement
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (fine coarse : FiniteInvariantCover V p) where
  indexMap : fine.Index → coarse.Index
  subordinate : ∀ i, fine.set i ⊆ coarse.set (indexMap i)
  equivariant : ∀ i, indexMap (fine.action i) = coarse.action (indexMap i)

private def FiniteInvariantCover.Refinement.refl
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : U.Refinement U where
  indexMap := id
  subordinate := fun _ ↦ Subset.rfl
  equivariant := fun _ ↦ rfl

private def FiniteInvariantCover.Refinement.trans
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine middle coarse : FiniteInvariantCover V p}
    (r : fine.Refinement middle) (s : middle.Refinement coarse) :
    fine.Refinement coarse where
  indexMap := s.indexMap ∘ r.indexMap
  subordinate := fun i ↦ (r.subordinate i).trans (s.subordinate (r.indexMap i))
  equivariant := by
    intro i
    simp only [Function.comp_apply, r.equivariant, s.equivariant]

private def FiniteInvariantCover.refinementBetween
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : ℕ → FiniteInvariantCover V p)
    (step : ∀ n, (U (n + 1)).Refinement (U n)) :
    ∀ i j, i ≤ j → (U j).Refinement (U i)
  | 0, 0, _ => FiniteInvariantCover.Refinement.refl (U 0)
  | 0, j + 1, _ =>
      (step j).trans (refinementBetween U step 0 j (Nat.zero_le j))
  | i + 1, 0, h => (Nat.not_succ_le_zero i h).elim
  | i + 1, j + 1, h =>
      refinementBetween (fun n => U (n + 1)) (fun n => step (n + 1))
        i j (Nat.le_of_succ_le_succ h)
termination_by i j _ => i + j

private theorem FiniteInvariantCover.Refinement.ext_indexMap
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    {r s : fine.Refinement coarse} (h : r.indexMap = s.indexMap) : r = s := by
  cases r
  cases s
  simp_all

private theorem FiniteInvariantCover.refinementBetween_refl
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : ℕ → FiniteInvariantCover V p)
    (step : ∀ n, (U (n + 1)).Refinement (U n)) (i : ℕ) :
    FiniteInvariantCover.refinementBetween U step i i le_rfl =
      FiniteInvariantCover.Refinement.refl (U i) := by
  induction i generalizing U with
  | zero => simp [FiniteInvariantCover.refinementBetween]
  | succ i ih =>
      simpa [FiniteInvariantCover.refinementBetween] using
        ih (U := fun n => U (n + 1)) (step := fun n => step (n + 1))

private theorem FiniteInvariantCover.refinementBetween_succ
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : ℕ → FiniteInvariantCover V p)
    (step : ∀ n, (U (n + 1)).Refinement (U n)) (i : ℕ) :
    FiniteInvariantCover.refinementBetween U step i (i + 1)
        (Nat.le_succ i) = step i := by
  induction i generalizing U with
  | zero =>
      apply FiniteInvariantCover.Refinement.ext_indexMap
      simp [FiniteInvariantCover.refinementBetween,
        FiniteInvariantCover.Refinement.trans,
        FiniteInvariantCover.Refinement.refl]
  | succ i ih =>
      simpa [FiniteInvariantCover.refinementBetween] using
        ih (U := fun n => U (n + 1)) (step := fun n => step (n + 1))

private theorem FiniteInvariantCover.refinementBetween_zero_succ
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : ℕ → FiniteInvariantCover V p)
    (step : ∀ n, (U (n + 1)).Refinement (U n)) (k : ℕ) :
    FiniteInvariantCover.refinementBetween U step 0 (k + 1)
        (Nat.zero_le _) =
      (FiniteInvariantCover.refinementBetween U step k (k + 1)
          (Nat.le_succ k)).trans
        (FiniteInvariantCover.refinementBetween U step 0 k
          (Nat.zero_le _)) := by
  rw [FiniteInvariantCover.refinementBetween]
  rw [FiniteInvariantCover.refinementBetween_succ]

/-- Forgetting equivariance turns an invariant refinement into an ordinary
cover refinement on the same indexed sets. -/
private def FiniteInvariantCover.Refinement.toOpenRefinement
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    (r : fine.Refinement coarse) :
    fine.toOpenCover.Refinement coarse.toOpenCover where
  indexMap := r.indexMap
  subordinate := r.subordinate

/-- A cover refinement induces the monotone map on full-nerve face posets. -/
private noncomputable def FiniteInvariantCover.Refinement.faceOrderHom
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    (r : fine.Refinement coarse) : fine.NerveFace →o coarse.NerveFace where
  toFun s := ⟨s.1.image r.indexMap, by
    refine ⟨s.2.1.image r.indexMap, ?_⟩
    rcases s.2.2 with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter] at hx ⊢
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact r.subordinate i (hx i hi)⟩
  monotone' := by
    intro a b hab
    exact Finset.image_mono r.indexMap hab

private theorem FiniteInvariantCover.Refinement.faceOrderHom_refl
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) :
    (FiniteInvariantCover.Refinement.refl U).faceOrderHom = OrderHom.id := by
  apply OrderHom.ext
  funext a
  apply Subtype.ext
  simp [FiniteInvariantCover.Refinement.faceOrderHom,
    FiniteInvariantCover.Refinement.refl]

private theorem FiniteInvariantCover.Refinement.faceOrderHom_trans
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine middle coarse : FiniteInvariantCover V p}
    (r : fine.Refinement middle) (s : middle.Refinement coarse) :
    (r.trans s).faceOrderHom = s.faceOrderHom.comp r.faceOrderHom := by
  apply OrderHom.ext
  funext a
  apply Subtype.ext
  simp [FiniteInvariantCover.Refinement.faceOrderHom,
    FiniteInvariantCover.Refinement.trans, Finset.image_image,
    Function.comp_def]

private theorem FiniteInvariantCover.Refinement.faceOrderHom_action
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    (r : fine.Refinement coarse) (s : fine.NerveFace) :
    r.faceOrderHom (fine.faceActionOrderIso s) =
      coarse.faceActionOrderIso (r.faceOrderHom s) := by
  classical
  apply Subtype.ext
  change (s.1.image fine.action).image r.indexMap =
    (s.1.image r.indexMap).image coarse.action
  simp [Finset.image_image, Function.comp_def, r.equivariant]

/-- The canonical equivariant augmented chain map carried by a refinement. -/
private noncomputable def FiniteInvariantCover.Refinement.smithHom
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    (r : fine.Refinement coarse) : fine.smithComplex.Hom coarse.smithComplex where
  map := fun n ↦ PosetNerve.strictChainMap fine.NerveFace coarse.NerveFace
    (ZMod p) r.faceOrderHom n
  map_boundary := fun n c ↦
    PosetNerve.strictChainMap_boundary fine.NerveFace coarse.NerveFace
      (ZMod p) r.faceOrderHom n c
  map_augment := fun c ↦
    PosetNerve.strictChainMap_augment fine.NerveFace coarse.NerveFace
      (ZMod p) r.faceOrderHom c
  map_equivariant := fun n c ↦
    PosetNerve.strictChainMap_action fine.NerveFace coarse.NerveFace
      (ZMod p) r.faceOrderHom fine.faceActionOrderIso
      coarse.faceActionOrderIso r.faceOrderHom_action n c
  map_fixed := fun n c hc ↦
    PosetNerve.strictChainMap_fixedSupport fine.NerveFace coarse.NerveFace
      (ZMod p) r.faceOrderHom fine.faceActionOrderIso
      coarse.faceActionOrderIso r.faceOrderHom_action n c hc

/-- The pro-zero assertion is insensitive to forgetting the cyclic action;
both sides are literally the same normalized strict-chain map and boundary. -/
private theorem FiniteInvariantCover.Refinement.smithHom_kills_iff_strictMap
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    (r : fine.Refinement coarse) :
    r.smithHom.KillsReducedHomology ↔
      PosetNerve.StrictMapKillsReducedHomology p r.faceOrderHom := by
  constructor
  · intro h n z hz
    have hz' : fine.smithComplex.IsReducedCycle n z := by
      cases n with
      | zero => exact hz
      | succ n => exact hz
    obtain ⟨w, hw⟩ := h n z hz'
    refine ⟨w, ?_⟩
    simpa only [FiniteInvariantCover.smithComplex,
      finiteCyclicAugmentedComplexOfPoset,
      FiniteInvariantCover.Refinement.smithHom,
      FiniteCyclicAugmentedComplex.IsBoundary] using hw
  · intro h n z hz
    have hz' : PosetNerve.StrictIsReducedCycle fine.NerveFace p n z := by
      cases n with
      | zero => exact hz
      | succ n => exact hz
    obtain ⟨w, hw⟩ := h n z hz'
    refine ⟨w, ?_⟩
    simpa only [FiniteInvariantCover.smithComplex,
      finiteCyclicAugmentedComplexOfPoset,
      FiniteInvariantCover.Refinement.smithHom,
      FiniteCyclicAugmentedComplex.IsBoundary] using hw

/-- A chain complex is explicitly identified with the barycentric full nerve
of its cover, including compatibility of the cyclic basis actions. -/
private structure FiniteInvariantCover.NerveRealization
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (C : FiniteCyclicAugmentedComplex p) where
  basisEquiv : ∀ n, C.Basis n ≃ U.BarycentricBasis n
  action_compat : ∀ n (b : C.Basis n) (j : Fin (n + 1)),
    (basisEquiv n (C.actionBasis n b)).1 j =
      ((basisEquiv n b).1 j).image U.action
  augment_single : ∀ (b : C.Basis 0) (r : ZMod p),
    C.augment (Finsupp.single b r) = r
  boundary_zero_support_comparable :
    ∀ (b : C.Basis 1) (a a' : C.Basis 0),
      a ∈ (C.boundary 0 (Finsupp.single b 1)).support →
      a' ∈ (C.boundary 0 (Finsupp.single b 1)).support →
      ((basisEquiv 0 a).1 0 ⊆ (basisEquiv 0 a').1 0) ∨
        ((basisEquiv 0 a').1 0 ⊆ (basisEquiv 0 a).1 0)

/-- Every invariant cover carries the canonical regular augmented complex of
the barycentric subdivision of its full nerve. -/
private noncomputable def FiniteInvariantCover.canonicalNerveRealization
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) : U.NerveRealization U.smithComplex where
  basisEquiv := U.strictChainsEquivBarycentricBasis
  action_compat := by
    intro n b j
    rfl
  augment_single := by
    intro b r
    exact PosetNerve.strictAugment_single U.NerveFace (ZMod p) b r
  boundary_zero_support_comparable := by
    intro b a a' ha ha'
    exact U.strictBoundary_zero_support_comparable b a a' ha ha'

/-- The tower chain map is the normalized barycentric map induced by the
displayed refinement.  A nonzero image basis simplex has exactly the
indexwise image chain; this is the coherence needed by the fixed witness. -/
private def FiniteInvariantCover.RealizesRefinementMap
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    {Cfine Ccoarse : FiniteCyclicAugmentedComplex p}
    (Rfine : fine.NerveRealization Cfine)
    (Rcoarse : coarse.NerveRealization Ccoarse)
    (r : fine.Refinement coarse) (f : Cfine.Hom Ccoarse) : Prop :=
  ∀ n (b : Cfine.Basis n) (a : Ccoarse.Basis n),
    a ∈ (f.map n (Finsupp.single b 1)).support →
      ∀ j : Fin (n + 1),
        (Rcoarse.basisEquiv n a).1 j =
          ((Rfine.basisEquiv n b).1 j).image r.indexMap

private theorem FiniteInvariantCover.Refinement.canonical_realizes_smithHom
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {fine coarse : FiniteInvariantCover V p}
    (r : fine.Refinement coarse) :
    FiniteInvariantCover.RealizesRefinementMap
      fine.canonicalNerveRealization coarse.canonicalNerveRealization
      r r.smithHom := by
  intro n b a ha j
  have h := PosetNerve.strictChainMap_single_support
    fine.NerveFace coarse.NerveFace (ZMod p) r.faceOrderHom n b 1 a ha j
  exact congrArg Subtype.val h

/-- One coherent inverse system of invariant covers and their realized full
barycentric nerves.  Every algebraic transition map is tied to a displayed
equivariant cover refinement. -/
private structure ArcLikeSmithNerveTower
    {X : Type*} [TopologicalSpace X] (V : X ≃ₜ X) (p : ℕ) where
  N : ℕ
  tower : FiniteCyclicAugmentedTower p
  cover : ℕ → FiniteInvariantCover V p
  realization : ∀ i, (cover i).NerveRealization (tower.level i)
  refinement : ∀ i j, i ≤ j → (cover j).Refinement (cover i)
  map_realizes : ∀ i j (h : i ≤ j),
    FiniteInvariantCover.RealizesRefinementMap
      (realization j) (realization i) (refinement i j h) (tower.map i j h)
  bottom_bounded : ∀ n, N < n → IsEmpty ((tower.level 0).Basis n)
  ambient_proZero :
    tower.SmithAcyclicThrough (smithH0TowerLength p N)

/-- The disconnected fixed set supplies two actual fixed points and two fixed
top nerve vertices.  Their difference is the reduced cycle, and its
top-to-bottom image is not a boundary in the fixed-support subcomplex. -/
private structure ArcLikeSmithNerveTower.PersistentFixedH0Witness
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (P : ArcLikeSmithNerveTower V p) where
  leftPoint : X
  rightPoint : X
  left_fixed : V leftPoint = leftPoint
  right_fixed : V rightPoint = rightPoint
  topLeft : (P.tower.level (smithH0TowerLength p P.N)).Basis 0
  topRight : (P.tower.level (smithH0TowerLength p P.N)).Basis 0
  topLeft_fixed :
    (P.tower.level (smithH0TowerLength p P.N)).actionBasis 0 topLeft = topLeft
  topRight_fixed :
    (P.tower.level (smithH0TowerLength p P.N)).actionBasis 0 topRight = topRight
  left_carried : ∀ i ∈ ((P.realization (smithH0TowerLength p P.N)).basisEquiv
      0 topLeft).1 0,
    leftPoint ∈ (P.cover (smithH0TowerLength p P.N)).set i
  right_carried : ∀ i ∈ ((P.realization (smithH0TowerLength p P.N)).basisEquiv
      0 topRight).1 0,
    rightPoint ∈ (P.cover (smithH0TowerLength p P.N)).set i
  z : (P.tower.level (smithH0TowerLength p P.N)).Chain 0
  z_eq : z = Finsupp.single topLeft 1 - Finsupp.single topRight 1
  z_fixed : (P.tower.level (smithH0TowerLength p P.N)).IsFixedChain z
  z_reduced : (P.tower.level (smithH0TowerLength p P.N)).augment z = 0
  persistent : ¬ ∃ w : (P.tower.level 0).Chain 1,
    (P.tower.level 0).IsFixedChain w ∧
      (P.tower.level 0).boundary 0 w =
        (P.tower.map 0 (smithH0TowerLength p P.N) (Nat.zero_le _)).map 0 z

/-- A compact separation of the disconnected fixed set.  Keeping both sides
as compact subsets of the ambient space is what later permits a uniform
small-mesh invariant nerve separation. -/
private structure PeriodicFixedSetSeparation
    {X : Type*} [TopologicalSpace X] (V : X ≃ₜ X) where
  left : Set X
  right : Set X
  left_compact : IsCompact left
  right_compact : IsCompact right
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disjoint : Disjoint left right
  fixed_eq : {x : X | V x = x} = left ∪ right

/-- The geometric carrier of a full-nerve face. -/
private def FiniteInvariantCover.nerveFaceCarrier
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (s : U.NerveFace) : Set X :=
  ⋂ i ∈ s.1, U.set i

/-- A two-colouring of the fixed part of the barycentric nerve which is
constant along comparable fixed faces and detects the two compact pieces of
the fixed-set separation.  This is the exact cover-level input used by the
persistent fixed-`H₀` calculation. -/
private structure FiniteInvariantCover.FixedNerveH0Separation
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (S : PeriodicFixedSetSeparation V) where
  side : U.NerveFace → Bool
  side_eq_of_le : ∀ {a b : U.NerveFace},
    U.faceActionOrderIso a = a → U.faceActionOrderIso b = b →
      a ≤ b → side a = side b
  left_side : ∀ a : U.NerveFace,
    U.faceActionOrderIso a = a →
      (U.nerveFaceCarrier a ∩ S.left).Nonempty → side a = false
  right_side : ∀ a : U.NerveFace,
    U.faceActionOrderIso a = a →
      (U.nerveFaceCarrier a ∩ S.right).Nonempty → side a = true

/-- The nerve face represented by a realized degree-zero basis vector. -/
private def FiniteInvariantCover.NerveRealization.vertexFace
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {U : FiniteInvariantCover V p} {C : FiniteCyclicAugmentedComplex p}
    (R : U.NerveRealization C) (b : C.Basis 0) : U.NerveFace :=
  ⟨(R.basisEquiv 0 b).1 0, (R.basisEquiv 0 b).2.1 0⟩

/-- The coefficient sum over vertices on the right side of the fixed-nerve
two-colouring.  Making this a linear map keeps the final non-boundary
calculation independent of support normal forms. -/
private noncomputable def FiniteInvariantCover.FixedNerveH0Separation.sideLinear
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    {U : FiniteInvariantCover V p} {C : FiniteCyclicAugmentedComplex p}
    {S : PeriodicFixedSetSeparation V}
    (hsep : U.FixedNerveH0Separation S) (R : U.NerveRealization C) :
    C.Chain 0 →ₗ[ZMod p] ZMod p :=
  Finsupp.lsum (ZMod p) fun b ↦
    if hsep.side (R.vertexFace b) = true then LinearMap.id else 0

/-- Invariant disjoint neighbourhoods of the two fixed pieces, together with
a displacement threshold which forces every sufficiently almost-fixed point
into one of them.  Compactness supplies the positive threshold; finite
periodicity supplies invariant neighbourhoods. -/
private structure PeriodicFixedSetSeparation.DisplacementNeighborhoods
    {X : Type*} [MetricSpace X] {V : X ≃ₜ X}
    (S : PeriodicFixedSetSeparation V) where
  leftNeighborhood : Set X
  rightNeighborhood : Set X
  left_open : IsOpen leftNeighborhood
  right_open : IsOpen rightNeighborhood
  left_mem : S.left ⊆ leftNeighborhood
  right_mem : S.right ⊆ rightNeighborhood
  disjoint : Disjoint leftNeighborhood rightNeighborhood
  closure_disjoint :
    Disjoint (closure leftNeighborhood) (closure rightNeighborhood)
  left_invariant : V '' leftNeighborhood = leftNeighborhood
  right_invariant : V '' rightNeighborhood = rightNeighborhood
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  near_fixed : ∀ x, dist (V x) x < epsilon →
    x ∈ leftNeighborhood ∨ x ∈ rightNeighborhood

/-- A cover is fine enough for the fixed-face colouring argument when every
fixed face has displacement below the threshold and no single cover element
meets both invariant neighbourhoods. -/
private structure FiniteInvariantCover.FixedFaceDisplacementMesh
    {X : Type*} [MetricSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (S : PeriodicFixedSetSeparation V)
    (D : S.DisplacementNeighborhoods) where
  fixedCarrier_smallDisplacement : ∀ (a : U.NerveFace),
    U.faceActionOrderIso a = a → ∀ x ∈ U.nerveFaceCarrier a,
      dist (V x) x < D.epsilon
  cover_does_not_cross : ∀ i : U.Index,
    ¬ ((U.set i ∩ D.leftNeighborhood).Nonempty ∧
      (U.set i ∩ D.rightNeighborhood).Nonempty)

/-- An anchored common refinement of all translates of an ordinary cover.
The projection indexed by `k` witnesses subordination to the `k`th translate;
the anchor rotates with the cover action.  Duplicating the geometric
intersections by the anchor is what removes stabilizer obstructions to an
equivariant refinement choice. -/
private structure FiniteOpenCover.CyclicCommonRefinement
    {X : Type*} [TopologicalSpace X] (base : FiniteOpenCover X)
    (V : X ≃ₜ X) (p : ℕ) (hp : Nat.Prime p) where
  fine : FiniteInvariantCover V p
  projection : Fin p → fine.Index → base.Index
  subordinate_translate : ∀ k i,
    fine.set i ⊆ ((V ^ k.1 : X ≃ₜ X) : X → X) ''
      base.set (projection k i)
  projection_action : ∀ k i,
    projection (finRotate p k) (fine.action i) = projection k i
  anchor : fine.Index → Fin p
  anchor_action : ∀ i, anchor (fine.action i) = finRotate p (anchor i)

/-- The zero-translate projection of a cyclic common refinement. -/
private def FiniteOpenCover.CyclicCommonRefinement.toBase
    {X : Type*} [TopologicalSpace X] {base : FiniteOpenCover X}
    {V : X ≃ₜ X} {p : ℕ} {hp : Nat.Prime p}
    (S : base.CyclicCommonRefinement V p hp) :
    S.fine.toOpenCover.Refinement base where
  indexMap := S.projection ⟨0, hp.pos⟩
  subordinate := by
    intro i x hx
    have h := S.subordinate_translate ⟨0, hp.pos⟩ i hx
    simpa using h

/-- The finite segment of invariant covers needed by the relative Smith
chase.  Each successor is an explicitly displayed equivariant refinement and
its canonical nerve map is ambient pro-zero. -/
private structure FiniteSmithNerveCoverChain
    {X : Type*} [TopologicalSpace X] (V : X ≃ₜ X) (p N : ℕ) where
  cover : Fin (smithH0TowerLength p N + 1) → FiniteInvariantCover V p
  refinement : ∀ i : Fin (smithH0TowerLength p N),
    (cover i.succ).Refinement (cover i.castSucc)
  step_acyclic : ∀ i : Fin (smithH0TowerLength p N),
    (refinement i).smithHom.KillsReducedHomology
  bottom_bounded : ∀ n, N < n →
    IsEmpty (((cover 0).smithComplex).Basis n)

/-! ### Dependency-ordered topological realization skeleton -/

/-- Disconnectedness of the compact fixed set yields two nonempty disjoint
compact pieces covering it. -/
private theorem disconnectedFix_exists_compactSeparation
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (V : X ≃ₜ X)
    (hdisc : ¬ IsPreconnected {x : X | V x = x}) :
    Nonempty (PeriodicFixedSetSeparation V) := by
  let F : Set X := {x : X | V x = x}
  have hFclosed : IsClosed F :=
    isClosed_eq V.continuous continuous_id
  have hsep : ∃ u v : Set X,
      IsClosed u ∧ IsClosed v ∧ F ⊆ u ∪ v ∧ Disjoint u v ∧
        ¬ F ⊆ u ∧ ¬ F ⊆ v := by
    have hnot : ¬ IsPreconnected F := by simpa [F] using hdisc
    rw [isPreconnected_iff_subset_of_fully_disjoint_closed hFclosed] at hnot
    push_neg at hnot
    exact hnot
  rcases hsep with ⟨u, v, hu, hv, hcover, huv, hnotu, hnotv⟩
  refine ⟨{
    left := F ∩ u
    right := F ∩ v
    left_compact := (hFclosed.inter hu).isCompact
    right_compact := (hFclosed.inter hv).isCompact
    left_nonempty := ?_
    right_nonempty := ?_
    disjoint := ?_
    fixed_eq := ?_ }⟩
  · rcases Set.not_subset.mp hnotv with ⟨x, hxF, hxv⟩
    have hxu : x ∈ u := (hcover hxF).resolve_right hxv
    exact ⟨x, hxF, hxu⟩
  · rcases Set.not_subset.mp hnotu with ⟨x, hxF, hxu⟩
    have hxv : x ∈ v := (hcover hxF).resolve_left hxu
    exact ⟨x, hxF, hxv⟩
  · exact huv.mono inter_subset_right inter_subset_right
  · change F = (F ∩ u) ∪ (F ∩ v)
    apply Set.Subset.antisymm
    · intro x hxF
      rcases hcover hxF with hxu | hxv
      · exact Or.inl ⟨hxF, hxu⟩
      · exact Or.inr ⟨hxF, hxv⟩
    · rintro x (⟨hxF, _⟩ | ⟨hxF, _⟩) <;> exact hxF

/-- Compactness separates the two fixed pieces by invariant open
neighbourhoods and gives a positive lower bound for displacement on their
complement. -/
private theorem periodicFixedSetSeparation_exists_displacementNeighborhoods
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) (S : PeriodicFixedSetSeparation V) :
    Nonempty S.DisplacementNeighborhoods := by
  classical
  obtain ⟨A₀, B₀, hA₀open, hB₀open, hleftA₀, hrightB₀, hA₀B₀⟩ :=
    normal_separation S.left_compact.isClosed S.right_compact.isClosed S.disjoint
  obtain ⟨L₀, hL₀open, hleftL₀, hclosureL₀⟩ :=
    normal_exists_closure_subset S.left_compact.isClosed hA₀open hleftA₀
  obtain ⟨R₀, hR₀open, hrightR₀, hclosureR₀⟩ :=
    normal_exists_closure_subset S.right_compact.isClosed hB₀open hrightB₀
  have hclosureL₀R₀ : Disjoint (closure L₀) (closure R₀) :=
    hA₀B₀.mono hclosureL₀ hclosureR₀
  let invariantCore (O : Set X) : Set X :=
    ⋂ k : Fin p, ((V ^ k.1 : X ≃ₜ X) : X → X) ⁻¹' O
  have mem_invariantCore (O : Set X) (x : X) :
      x ∈ invariantCore O ↔
        ∀ k : Fin p, (V ^ k.1 : X ≃ₜ X) x ∈ O := by
    simp [invariantCore]
  have invariantCore_open (O : Set X) (hO : IsOpen O) :
      IsOpen (invariantCore O) := by
    dsimp only [invariantCore]
    exact isOpen_iInter_of_finite fun k ↦
      hO.preimage (V ^ k.1).continuous
  have fixed_pow (x : X) (hx : V x = x) :
      ∀ n : ℕ, (V ^ n : X ≃ₜ X) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, hx, ih]
  have left_fixed {x : X} (hx : x ∈ S.left) : V x = x := by
    have hx' : x ∈ {y : X | V y = y} := by
      rw [S.fixed_eq]
      exact Or.inl hx
    exact hx'
  have right_fixed {x : X} (hx : x ∈ S.right) : V x = x := by
    have hx' : x ∈ {y : X | V y = y} := by
      rw [S.fixed_eq]
      exact Or.inr hx
    exact hx'
  have left_mem_core : S.left ⊆ invariantCore L₀ := by
    intro x hx
    rw [mem_invariantCore]
    intro k
    rw [fixed_pow x (left_fixed hx) k.1]
    exact hleftL₀ hx
  have right_mem_core : S.right ⊆ invariantCore R₀ := by
    intro x hx
    rw [mem_invariantCore]
    intro k
    rw [fixed_pow x (right_fixed hx) k.1]
    exact hrightR₀ hx
  have core_subset (O : Set X) : invariantCore O ⊆ O := by
    intro x hx
    have hzero := (mem_invariantCore O x).1 hx ⟨0, hp.pos⟩
    simpa using hzero
  have core_forward (O : Set X) :
      V '' invariantCore O ⊆ invariantCore O := by
    rintro y ⟨x, hx, rfl⟩
    rw [mem_invariantCore]
    intro k
    by_cases hk : k.1 + 1 < p
    · have hnext := (mem_invariantCore O x).1 hx
          ⟨k.1 + 1, hk⟩
      simpa [pow_succ] using hnext
    · have hkp : k.1 + 1 = p := by omega
      have hzero := (mem_invariantCore O x).1 hx ⟨0, hp.pos⟩
      have hwrap : (V ^ (k.1 + 1) : X ≃ₜ X) x ∈ O := by
        simpa [hkp, hperiodic] using hzero
      simpa [pow_succ] using hwrap
  have core_invariant (O : Set X) :
      V '' invariantCore O = invariantCore O := by
    apply Set.Subset.antisymm (core_forward O)
    intro x hx
    let y : X := (V ^ (p - 1) : X ≃ₜ X) x
    have pow_mem : ∀ n : ℕ, (V ^ n : X ≃ₜ X) x ∈ invariantCore O := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
          apply core_forward O
          exact ⟨(V ^ n : X ≃ₜ X) x, ih, by simp [pow_succ']⟩
    refine ⟨y, pow_mem (p - 1), ?_⟩
    have hpdecomp : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
    change V ((V ^ (p - 1) : X ≃ₜ X) x) = x
    rw [← show (V ^ (p - 1 + 1) : X ≃ₜ X) x =
      V ((V ^ (p - 1) : X ≃ₜ X) x) by simp [pow_succ']]
    rw [hpdecomp, hperiodic]
    rfl
  let L := invariantCore L₀
  let R := invariantCore R₀
  have hLopen : IsOpen L := invariantCore_open L₀ hL₀open
  have hRopen : IsOpen R := invariantCore_open R₀ hR₀open
  have hleftL : S.left ⊆ L := left_mem_core
  have hrightR : S.right ⊆ R := right_mem_core
  have hLR : Disjoint L R :=
    hclosureL₀R₀.mono
      ((core_subset L₀).trans subset_closure)
      ((core_subset R₀).trans subset_closure)
  have hclosureLR : Disjoint (closure L) (closure R) :=
    hclosureL₀R₀.mono
      (closure_mono (core_subset L₀))
      (closure_mono (core_subset R₀))
  have hLinvariant : V '' L = L := core_invariant L₀
  have hRinvariant : V '' R = R := core_invariant R₀
  let C : Set X := (L ∪ R)ᶜ
  have hCcompact : IsCompact C :=
    (hLopen.union hRopen).isClosed_compl.isCompact
  have hdispContinuous : Continuous (fun x : X ↦ dist (V x) x) :=
    V.continuous.dist continuous_id
  by_cases hCne : C.Nonempty
  · obtain ⟨x₀, hx₀C, hx₀min⟩ :=
      hCcompact.exists_isMinOn hCne hdispContinuous.continuousOn
    have hx₀ne : V x₀ ≠ x₀ := by
      intro hx₀fixed
      have hx₀fixedSet : x₀ ∈ {x : X | V x = x} := hx₀fixed
      have hx₀union : x₀ ∈ L ∪ R := by
        rw [S.fixed_eq] at hx₀fixedSet
        rcases hx₀fixedSet with hxleft | hxright
        · exact Or.inl (hleftL hxleft)
        · exact Or.inr (hrightR hxright)
      exact hx₀C hx₀union
    refine ⟨{
      leftNeighborhood := L
      rightNeighborhood := R
      left_open := hLopen
      right_open := hRopen
      left_mem := hleftL
      right_mem := hrightR
      disjoint := hLR
      closure_disjoint := hclosureLR
      left_invariant := hLinvariant
      right_invariant := hRinvariant
      epsilon := dist (V x₀) x₀
      epsilon_pos := dist_pos.mpr hx₀ne
      near_fixed := ?_ }⟩
    intro x hsmall
    by_contra hout
    have hxC : x ∈ C := by
      exact hout
    exact (not_lt_of_ge (hx₀min hxC)) hsmall
  · refine ⟨{
      leftNeighborhood := L
      rightNeighborhood := R
      left_open := hLopen
      right_open := hRopen
      left_mem := hleftL
      right_mem := hrightR
      disjoint := hLR
      closure_disjoint := hclosureLR
      left_invariant := hLinvariant
      right_invariant := hRinvariant
      epsilon := 1
      epsilon_pos := zero_lt_one
      near_fixed := ?_ }⟩
    intro x _
    by_contra hout
    apply hCne
    exact ⟨x, hout⟩

/-- A sufficiently fine cyclically saturated open cover has small
displacement on every fixed nerve-face carrier and no element crosses the two
chosen neighbourhoods. -/
private theorem displacementNeighborhoods_exists_invariantMeshCover
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) (S : PeriodicFixedSetSeparation V)
    (D : S.DisplacementNeighborhoods) :
    ∃ U : FiniteInvariantCover V p,
      Nonempty (U.FixedFaceDisplacementMesh S D) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  let O : X → Set X := fun x ↦
    Metric.ball x (D.epsilon / 2) ∩
      if x ∈ closure D.leftNeighborhood then
        (closure D.rightNeighborhood)ᶜ
      else
        (closure D.leftNeighborhood)ᶜ
  have hOopen (x : X) : IsOpen (O x) := by
    dsimp only [O]
    apply Metric.isOpen_ball.inter
    split_ifs
    · exact isClosed_closure.isOpen_compl
    · exact isClosed_closure.isOpen_compl
  have hxO (x : X) : x ∈ O x := by
    refine ⟨Metric.mem_ball_self (half_pos D.epsilon_pos), ?_⟩
    dsimp only [O]
    split_ifs with hxleft
    · intro hxright
      exact D.closure_disjoint.le_bot ⟨hxleft, hxright⟩
    · exact hxleft
  have hOsmall (x : X) {y z : X} (hy : y ∈ O x) (hz : z ∈ O x) :
      dist y z < D.epsilon := by
    have hy' : dist y x < D.epsilon / 2 := Metric.mem_ball.mp hy.1
    have hz' : dist x z < D.epsilon / 2 := by
      simpa [dist_comm] using Metric.mem_ball.mp hz.1
    calc
      dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
      _ < D.epsilon / 2 + D.epsilon / 2 := add_lt_add hy' hz'
      _ = D.epsilon := by ring
  have hOdoesNotCross (x : X) :
      ¬ ((O x ∩ D.leftNeighborhood).Nonempty ∧
        (O x ∩ D.rightNeighborhood).Nonempty) := by
    dsimp only [O]
    split_ifs with hxleft
    · rintro ⟨_, ⟨z, hzO, hzright⟩⟩
      exact hzO.2 (subset_closure hzright)
    · rintro ⟨⟨y, hyO, hyleft⟩, _⟩
      exact hyO.2 (subset_closure hyleft)
  let B : X → Set X := fun x ↦
    ⋂ k : Fin p,
      ((V ^ k.1 : X ≃ₜ X) : X → X) ⁻¹'
        O ((V ^ k.1 : X ≃ₜ X) x)
  have hBopen (x : X) : IsOpen (B x) := by
    dsimp only [B]
    exact isOpen_iInter_of_finite fun k ↦
      (hOopen ((V ^ k.1 : X ≃ₜ X) x)).preimage
        (V ^ k.1).continuous
  have hxB (x : X) : x ∈ B x := by
    dsimp only [B]
    rw [Set.mem_iInter]
    intro k
    exact hxO ((V ^ k.1 : X ≃ₜ X) x)
  have hBtranslateSubset (x : X) (k : Fin p) :
      (V ^ k.1 : X ≃ₜ X) '' B x ⊆
        O ((V ^ k.1 : X ≃ₜ X) x) := by
    rintro y ⟨z, hzB, rfl⟩
    have hz := Set.mem_iInter.mp hzB k
    exact hz
  have hBcover : Set.univ ⊆ ⋃ x : X, B x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxB x⟩
  obtain ⟨centers, hcenters⟩ :=
    isCompact_univ.elim_finite_subcover B hBopen hBcover
  let Center := Fin centers.card
  let centerPoint : Center → X := fun j ↦
    ((centers.equivFin).symm j).1
  let coverSet : ZMod p × Center → Set X := fun i ↦
    (V ^ i.1.val : X ≃ₜ X) '' B (centerPoint i.2)
  have hcoverSetOpen (i : ZMod p × Center) : IsOpen (coverSet i) := by
    exact (V ^ i.1.val : X ≃ₜ X).isOpenMap _
      (hBopen (centerPoint i.2))
  have hcoverSetNonempty (i : ZMod p × Center) :
      (coverSet i).Nonempty := by
    exact ⟨(V ^ i.1.val : X ≃ₜ X) (centerPoint i.2),
      ⟨centerPoint i.2, hxB (centerPoint i.2), rfl⟩⟩
  have hcoverSetSmall (i : ZMod p × Center) {y z : X}
      (hy : y ∈ coverSet i) (hz : z ∈ coverSet i) :
      dist y z < D.epsilon :=
    hOsmall _
      (hBtranslateSubset (centerPoint i.2)
        ⟨i.1.val, ZMod.val_lt _⟩ hy)
      (hBtranslateSubset (centerPoint i.2)
        ⟨i.1.val, ZMod.val_lt _⟩ hz)
  have hcoverSetDoesNotCross (i : ZMod p × Center) :
      ¬ ((coverSet i ∩ D.leftNeighborhood).Nonempty ∧
        (coverSet i ∩ D.rightNeighborhood).Nonempty) := by
    rintro ⟨⟨y, hy, hyleft⟩, ⟨z, hz, hzright⟩⟩
    apply hOdoesNotCross
      ((V ^ i.1.val : X ≃ₜ X) (centerPoint i.2))
    exact ⟨
      ⟨y, hBtranslateSubset (centerPoint i.2)
        ⟨i.1.val, ZMod.val_lt _⟩ hy, hyleft⟩,
      ⟨z, hBtranslateSubset (centerPoint i.2)
        ⟨i.1.val, ZMod.val_lt _⟩ hz, hzright⟩⟩
  let rotate : Equiv.Perm (ZMod p × Center) :=
    Equiv.prodCongr (Equiv.addRight 1) (Equiv.refl Center)
  have hrotatePeriodic : rotate ^ p = 1 := by
    apply Equiv.ext
    intro i
    rw [Equiv.Perm.coe_pow]
    have hiter : ∀ n : ℕ,
        rotate^[n] i = (i.1 + n, i.2) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih]
          apply Prod.ext
          · change i.1 + (n : ZMod p) + 1 =
              i.1 + ((n + 1 : ℕ) : ZMod p)
            rw [Nat.cast_add, Nat.cast_one]
            abel
          · rfl
    simpa using hiter p
  have hpowerRotate (k : ZMod p) :
      V * (V ^ k.val : X ≃ₜ X) = V ^ (k + 1).val := by
    by_cases hk : k.val + 1 < p
    · have hval : (k + 1).val = k.val + 1 := by
        simpa [ZMod.val_one p] using
          (ZMod.val_add_of_lt (a := k) (b := (1 : ZMod p))
            (by simpa [ZMod.val_one p] using hk))
      rw [hval, pow_succ']
    · have hkEq : k.val + 1 = p := by
        have hklt := ZMod.val_lt k
        omega
      have hval : (k + 1).val = 0 := by
        rw [ZMod.val_add_of_le]
        · simp [ZMod.val_one p, hkEq]
        · simpa [ZMod.val_one p, hkEq]
      rw [hval, pow_zero]
      calc
        V * V ^ k.val = V ^ (k.val + 1) := (pow_succ' V k.val).symm
        _ = V ^ p := by rw [hkEq]
        _ = 1 := hperiodic
  have hcoverSetEquivariant (i : ZMod p × Center) :
      V '' coverSet i = coverSet (rotate i) := by
    have hfun : (fun x : X ↦ V ((V ^ i.1.val : X ≃ₜ X) x)) =
        fun x : X ↦ (V ^ (i.1 + 1).val : X ≃ₜ X) x := by
      funext x
      exact congrArg (fun e : X ≃ₜ X ↦ e x) (hpowerRotate i.1)
    simpa [coverSet, rotate, Set.image_image] using
      congrArg (fun f : X → X ↦ f '' B (centerPoint i.2)) hfun
  let U : FiniteInvariantCover V p := {
    Index := ZMod p × Center
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    set := coverSet
    isOpen_set := hcoverSetOpen
    nonempty_set := hcoverSetNonempty
    covers := by
      intro x _
      have hx := hcenters (Set.mem_univ x)
      rcases Set.mem_iUnion.mp hx with ⟨c, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hc, hxc⟩
      apply Set.mem_iUnion.mpr
      let j : Center := centers.equivFin ⟨c, hc⟩
      refine ⟨((0 : ZMod p), j), ?_⟩
      have hj : centerPoint j = c := by
        simp [centerPoint, j]
      exact ⟨x, by simpa [hj] using hxc, by simp [coverSet]⟩
    action := rotate
    action_periodic := hrotatePeriodic
    equivariant := hcoverSetEquivariant }
  have hUsetSmall : ∀ (i : U.Index) {y z : X},
      y ∈ U.set i → z ∈ U.set i → dist y z < D.epsilon := by
    change ∀ (i : ZMod p × Center) {y z : X},
      y ∈ coverSet i → z ∈ coverSet i → dist y z < D.epsilon
    exact fun i _ _ hy hz ↦ hcoverSetSmall i hy hz
  have hUsetDoesNotCross : ∀ i : U.Index,
      ¬ ((U.set i ∩ D.leftNeighborhood).Nonempty ∧
        (U.set i ∩ D.rightNeighborhood).Nonempty) := by
    change ∀ i : ZMod p × Center,
      ¬ ((coverSet i ∩ D.leftNeighborhood).Nonempty ∧
        (coverSet i ∩ D.rightNeighborhood).Nonempty)
    exact hcoverSetDoesNotCross
  refine ⟨U, ⟨{
    fixedCarrier_smallDisplacement := ?_
    cover_does_not_cross := ?_ }⟩⟩
  · intro a ha x hxa
    obtain ⟨i, hi⟩ := a.2.1
    have hface : a.1.image U.action = a.1 :=
      congrArg Subtype.val ha
    have hactioni : U.action i ∈ a.1 := by
      rw [← hface]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have hxi : x ∈ U.set i := by
      simpa only [FiniteInvariantCover.nerveFaceCarrier,
        Set.mem_iInter] using (show ∀ j, j ∈ a.1 → x ∈ U.set j from by
          simpa only [FiniteInvariantCover.nerveFaceCarrier,
            Set.mem_iInter] using hxa) i hi
    have hxaction : x ∈ U.set (U.action i) := by
      have hxa' := hxa
      simp only [FiniteInvariantCover.nerveFaceCarrier,
        Set.mem_iInter] at hxa'
      exact hxa' (U.action i) hactioni
    have hVxi : V x ∈ U.set (U.action i) := by
      rw [← U.equivariant i]
      exact ⟨x, hxi, rfl⟩
    exact hUsetSmall (U.action i) hVxi hxaction
  · intro i
    exact hUsetDoesNotCross i

/-- The displacement mesh admits a coherent two-colouring of all fixed
barycentric faces.  Comparability preserves the colour because the finer
carrier is contained in the coarser one and no cover element crosses the two
neighbourhoods. -/
private theorem fixedFaceDisplacementMesh_exists_fixedNerveH0Separation
    {X : Type*} [MetricSpace X] {V : X ≃ₜ X} {p : ℕ}
    (S : PeriodicFixedSetSeparation V) (D : S.DisplacementNeighborhoods)
    (U : FiniteInvariantCover V p)
    (hmesh : U.FixedFaceDisplacementMesh S D) :
    Nonempty (U.FixedNerveH0Separation S) := by
  classical
  have carrier_mono {a b : U.NerveFace} (hab : a ≤ b) :
      U.nerveFaceCarrier b ⊆ U.nerveFaceCarrier a := by
    intro x hxb
    simp only [FiniteInvariantCover.nerveFaceCarrier, Set.mem_iInter] at hxb ⊢
    intro i hi
    exact hxb i (hab hi)
  have no_cross (a : U.NerveFace) :
      ¬ ((U.nerveFaceCarrier a ∩ D.leftNeighborhood).Nonempty ∧
        (U.nerveFaceCarrier a ∩ D.rightNeighborhood).Nonempty) := by
    rintro ⟨⟨x, hxa, hxl⟩, ⟨y, hya, hyr⟩⟩
    obtain ⟨i, hi⟩ := a.2.1
    apply hmesh.cover_does_not_cross i
    constructor
    · refine ⟨x, ?_, hxl⟩
      simp only [FiniteInvariantCover.nerveFaceCarrier,
        Set.mem_iInter] at hxa
      exact hxa i hi
    · refine ⟨y, ?_, hyr⟩
      simp only [FiniteInvariantCover.nerveFaceCarrier,
        Set.mem_iInter] at hya
      exact hya i hi
  have classified (a : U.NerveFace)
      (ha : U.faceActionOrderIso a = a) :
      (U.nerveFaceCarrier a ∩ D.leftNeighborhood).Nonempty ∨
        (U.nerveFaceCarrier a ∩ D.rightNeighborhood).Nonempty := by
    obtain ⟨x, hx⟩ := a.2.2
    rcases D.near_fixed x
        (hmesh.fixedCarrier_smallDisplacement a ha x hx) with hxl | hxr
    · exact Or.inl ⟨x, hx, hxl⟩
    · exact Or.inr ⟨x, hx, hxr⟩
  let side : U.NerveFace → Bool := fun a ↦
    decide (U.nerveFaceCarrier a ∩ D.rightNeighborhood).Nonempty
  refine ⟨{
    side := side
    side_eq_of_le := ?_
    left_side := ?_
    right_side := ?_ }⟩
  · intro a b ha hb hab
    rcases classified b hb with hbl | hbr
    · have hal :
          (U.nerveFaceCarrier a ∩ D.leftNeighborhood).Nonempty := by
        rcases hbl with ⟨x, hxb, hxl⟩
        exact ⟨x, carrier_mono hab hxb, hxl⟩
      have hnbr :
          ¬ (U.nerveFaceCarrier b ∩ D.rightNeighborhood).Nonempty :=
        fun hbr ↦ no_cross b ⟨hbl, hbr⟩
      have hnar :
          ¬ (U.nerveFaceCarrier a ∩ D.rightNeighborhood).Nonempty :=
        fun har ↦ no_cross a ⟨hal, har⟩
      simp [side, hnbr, hnar]
    · have har :
          (U.nerveFaceCarrier a ∩ D.rightNeighborhood).Nonempty := by
        rcases hbr with ⟨x, hxb, hxr⟩
        exact ⟨x, carrier_mono hab hxb, hxr⟩
      simp [side, hbr, har]
  · intro a _ hleft
    have hal :
        (U.nerveFaceCarrier a ∩ D.leftNeighborhood).Nonempty := by
      rcases hleft with ⟨x, hxa, hxl⟩
      exact ⟨x, hxa, D.left_mem hxl⟩
    have hnar :
        ¬ (U.nerveFaceCarrier a ∩ D.rightNeighborhood).Nonempty :=
      fun har ↦ no_cross a ⟨hal, har⟩
    simp [side, hnar]
  · intro a _ hright
    have har :
        (U.nerveFaceCarrier a ∩ D.rightNeighborhood).Nonempty := by
      rcases hright with ⟨x, hxa, hxr⟩
      exact ⟨x, hxa, D.right_mem hxr⟩
    simp [side, har]

/-- A compact fixed-set separation admits a finite invariant cover whose
fixed barycentric nerve faces carry a coherent two-colouring. -/
private theorem periodicFixedSetSeparation_exists_invariantNerveCover
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) (S : PeriodicFixedSetSeparation V) :
    ∃ U : FiniteInvariantCover V p,
      Nonempty (U.FixedNerveH0Separation S) := by
  obtain ⟨D⟩ := periodicFixedSetSeparation_exists_displacementNeighborhoods
    V hp hperiodic S
  obtain ⟨U, ⟨hmesh⟩⟩ :=
    displacementNeighborhoods_exists_invariantMeshCover
      V hp hperiodic S D
  exact ⟨U,
    fixedFaceDisplacementMesh_exists_fixedNerveH0Separation S D U hmesh⟩

/-- Finite target-side data extracted from the fibre formulation of
arc-likeness.  Every member of the interval cover pulls back inside one member
of the prescribed cover of `X`. -/
private structure FiniteOpenCover.IntervalTargetSubordination
    {X : Type*} [TopologicalSpace X] (coarse : FiniteOpenCover X) where
  map : X → I
  continuous_map : Continuous map
  target : FiniteOpenCover I
  indexMap : target.Index → coarse.Index
  preimage_subordinate : ∀ i, map ⁻¹' target.set i ⊆ coarse.set (indexMap i)

/-- The full nerve is the path with `n+1` ordered vertices: its nonempty
simplices are exactly vertices and consecutive edges. -/
private def FiniteOpenCover.IsPathNerve
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X) : Prop :=
  ∃ n : ℕ, ∃ e : U.Index ≃ Fin (n + 1),
    ∀ s : Finset U.Index, U.IsNerveFace s ↔
      (∃ i : Fin (n + 1), s = {e.symm i}) ∨
      (∃ i : Fin n, s = {e.symm i.castSucc, e.symm i.succ})

/-- An explicit filling operator for all reduced cycles in a normalized strict
poset nerve. -/
private structure PosetNerve.StrictReducedContraction
    (p : ℕ) (P : Type) [PartialOrder P] where
  fill : ∀ n,
    (PosetNerve.strictChains P n →₀ ZMod p) →ₗ[ZMod p]
      (PosetNerve.strictChains P (n + 1) →₀ ZMod p)
  boundary_fill : ∀ n (z : PosetNerve.strictChains P n →₀ ZMod p),
    PosetNerve.StrictIsReducedCycle P p n z →
      PosetNerve.strictBoundary P (ZMod p) n (fill n z) = z

/-- Compactness thickens the fibrewise subordination supplied by
`IsArcLike` to a finite open cover on the target interval. -/
private theorem arcLike_exists_intervalTargetSubordination
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (harc : IsArcLike X) (coarse : FiniteOpenCover X) :
    Nonempty coarse.IntervalTargetSubordination := by
  classical
  let coverFamily : Set (Set X) := Set.range coarse.set
  have hcoverOpen : ∀ U ∈ coverFamily, IsOpen U := by
    rintro U ⟨i, rfl⟩
    exact coarse.isOpen_set i
  have hcover : Set.univ ⊆ ⋃₀ coverFamily := by
    intro x _
    have hx := coarse.covers (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    exact Set.mem_sUnion_of_mem hxi ⟨i, rfl⟩
  obtain ⟨f, hf, hfiber⟩ := harc coverFamily hcoverOpen hcover
  have hfiber' (y : I) :
      ∃ i : coarse.Index, f ⁻¹' {y} ⊆ coarse.set i := by
    obtain ⟨U, ⟨i, rfl⟩, hi⟩ := hfiber y
    exact ⟨i, hi⟩
  let fiberIndex : I → coarse.Index := fun y ↦ Classical.choose (hfiber' y)
  have hfiberIndex (y : I) :
      f ⁻¹' {y} ⊆ coarse.set (fiberIndex y) :=
    Classical.choose_spec (hfiber' y)
  let targetSet : I → Set I := fun y ↦
    (f '' (coarse.set (fiberIndex y))ᶜ)ᶜ
  have htargetOpen (y : I) : IsOpen (targetSet y) := by
    dsimp only [targetSet]
    exact ((coarse.isOpen_set (fiberIndex y)).isClosed_compl.isCompact.image hf)
      |>.isClosed.isOpen_compl
  have hyTarget (y : I) : y ∈ targetSet y := by
    change y ∉ f '' (coarse.set (fiberIndex y))ᶜ
    rintro ⟨x, hxout, hxy⟩
    apply hxout
    apply hfiberIndex y
    simpa using hxy
  have htargetSubordinate (y : I) :
      f ⁻¹' targetSet y ⊆ coarse.set (fiberIndex y) := by
    intro x hx
    by_contra hxout
    exact hx ⟨x, hxout, rfl⟩
  have htargetCover : Set.univ ⊆ ⋃ y : I, targetSet y := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, hyTarget y⟩
  obtain ⟨centers, hcenters⟩ :=
    isCompact_univ.elim_finite_subcover targetSet htargetOpen htargetCover
  let Center := Fin centers.card
  let centerPoint : Center → I := fun j ↦ ((centers.equivFin).symm j).1
  let target : FiniteOpenCover I := {
    Index := Center
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    set := fun j ↦ targetSet (centerPoint j)
    isOpen_set := fun j ↦ htargetOpen (centerPoint j)
    nonempty_set := fun j ↦ ⟨centerPoint j, hyTarget (centerPoint j)⟩
    covers := by
      intro y _
      have hy := hcenters (Set.mem_univ y)
      rcases Set.mem_iUnion.mp hy with ⟨c, hy⟩
      rcases Set.mem_iUnion.mp hy with ⟨hc, hyc⟩
      apply Set.mem_iUnion.mpr
      let j : Center := centers.equivFin ⟨c, hc⟩
      refine ⟨j, ?_⟩
      have hj : centerPoint j = c := by simp [centerPoint, j]
      simpa [hj] using hyc }
  refine ⟨{
    map := f
    continuous_map := hf
    target := target
    indexMap := fun j ↦ fiberIndex (centerPoint j)
    preimage_subordinate := fun j ↦
      htargetSubordinate (centerPoint j) }⟩

/-- Refine a subordinate target cover by a consecutive interval chain, pull
it back, and discard empty pullbacks.  Connectedness of the image forces the
occupied indices to remain consecutive and every adjacent pair to meet. -/
private theorem intervalTargetSubordination_exists_pathNerveRefinement
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (coarse : FiniteOpenCover X)
    (A : coarse.IntervalTargetSubordination) :
    ∃ fine : FiniteOpenCover X, ∃ r : fine.Refinement coarse,
      fine.IsPathNerve := by
  classical
  letI : ConnectedSpace X := hconnected
  let realMap : X → ℝ := fun x ↦ (A.map x : ℝ)
  have hrealMap : Continuous realMap :=
    continuous_subtype_val.comp A.continuous_map
  let K : Set ℝ := realMap '' Set.univ
  have hKconnected : IsConnected K :=
    isConnected_univ.image realMap hrealMap.continuousOn
  have hKcompact : IsCompact K := isCompact_univ.image hrealMap
  let a : ℝ := sInf K
  let b : ℝ := sSup K
  have hKeq : K = Set.Icc a b := by
    simpa [a, b] using eq_Icc_of_connected_compact hKconnected hKcompact
  have hKnonempty : K.Nonempty := hKconnected.nonempty
  have hab : a ≤ b := by
    rw [hKeq] at hKnonempty
    exact Set.nonempty_Icc.mp hKnonempty
  have hKunit : K ⊆ (I : Set ℝ) := by
    rintro y ⟨x, -, rfl⟩
    exact (A.map x).2
  let rangedMap : X → Set.Icc a b := fun x ↦
    ⟨realMap x, by
      rw [← hKeq]
      exact ⟨x, Set.mem_univ x, rfl⟩⟩
  have hrangedMap : Continuous rangedMap :=
    hrealMap.subtype_mk _
  by_cases heq : a = b
  · let x₀ : X := Classical.choice inferInstance
    let y₀ : I := A.map x₀
    have hreal_const (x : X) : realMap x = a := by
      have hx : realMap x ∈ Set.Icc a b := by
        rw [← hKeq]
        exact ⟨x, Set.mem_univ x, rfl⟩
      exact le_antisymm (by simpa [heq] using hx.2) hx.1
    have hmap_const (x : X) : A.map x = y₀ := by
      apply Subtype.ext
      exact (hreal_const x).trans (hreal_const x₀).symm
    have hy₀ := A.target.covers (Set.mem_univ y₀)
    rcases Set.mem_iUnion.mp hy₀ with ⟨i₀, hy₀i⟩
    let fine : FiniteOpenCover X := {
      Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      set := fun _ ↦ Set.univ
      isOpen_set := fun _ ↦ isOpen_univ
      nonempty_set := fun _ ↦ Set.univ_nonempty
      covers := fun _ _ ↦ Set.mem_iUnion.mpr ⟨0, Set.mem_univ _⟩ }
    let r : fine.Refinement coarse := {
      indexMap := fun _ ↦ A.indexMap i₀
      subordinate := by
        intro _ x _
        apply A.preimage_subordinate i₀
        simpa [hmap_const x] using hy₀i }
    refine ⟨fine, r, 0, Equiv.refl (Fin 1), ?_⟩
    intro s
    constructor
    · intro hs
      left
      refine ⟨0, ?_⟩
      change s = {(0 : Fin 1)}
      have hzero : (0 : Fin 1) ∈ s := by
        rcases hs.1 with ⟨j, hj⟩
        simpa [Fin.eq_zero j] using hj
      apply Finset.ext
      intro j
      have hj : j = (0 : Fin 1) := Fin.eq_zero j
      subst j
      simp [hzero]
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨by simp, ?_⟩
        refine ⟨x₀, ?_⟩
        simp [fine]
      · exact Fin.elim0 i
  · have hlt : a < b := lt_of_le_of_ne hab heq
    let includeRange : Set.Icc a b → I := fun z ↦
      ⟨z.1, hKunit (by
        rw [hKeq]
        exact z.2)⟩
    have hincludeRange : Continuous includeRange :=
      continuous_subtype_val.subtype_mk _
    let e : Set.Icc a b ≃ₜ I := iccHomeoI a b hlt
    let q : X → I := fun x ↦ e (rangedMap x)
    have hq : Continuous q := e.continuous.comp hrangedMap
    let embed : I → I := fun u ↦ includeRange (e.symm u)
    have hembed : Continuous embed :=
      hincludeRange.comp e.symm.continuous
    have hembed_q (x : X) : embed (q x) = A.map x := by
      apply Subtype.ext
      simp [embed, q, includeRange, rangedMap, realMap]
    have hqsurj : Function.Surjective q := by
      intro u
      have huK : ((e.symm u : Set.Icc a b) : ℝ) ∈ K := by
        rw [hKeq]
        exact (e.symm u).2
      rcases huK with ⟨x, -, hx⟩
      refine ⟨x, ?_⟩
      change e (rangedMap x) = u
      rw [← e.apply_symm_apply u]
      congr 1
      apply Subtype.ext
      exact hx
    let paramSet : A.target.Index → Set I := fun i ↦
      embed ⁻¹' A.target.set i
    have hparamOpen (i : A.target.Index) : IsOpen (paramSet i) :=
      (A.target.isOpen_set i).preimage hembed
    have hparamCover : Set.univ ⊆ ⋃ i, paramSet i := by
      intro u _
      have hu := A.target.covers (Set.mem_univ (embed u))
      rcases Set.mem_iUnion.mp hu with ⟨i, hui⟩
      exact Set.mem_iUnion.mpr ⟨i, hui⟩
    obtain ⟨δ, hδ, hball⟩ :=
      lebesgue_number_lemma_of_metric isCompact_univ hparamOpen hparamCover
    let step : ℝ := δ / 2
    have hstep : 0 < step := half_pos hδ
    let t : ℕ → I := Set.Icc.addNSMul zero_le_one step
    have htzero : t 0 = 0 := by
      simpa [t] using Set.Icc.addNSMul_zero (h := zero_le_one) (δ := step)
    have htmono : Monotone t := by
      simpa [t] using Set.Icc.monotone_addNSMul
        (h := zero_le_one) hstep.le
    obtain ⟨m, hm⟩ := Set.Icc.addNSMul_eq_right
      (h := zero_le_one) hstep
    have hexistsTerminal : ∃ m : ℕ, t m = 1 :=
      ⟨m, by simpa [t] using hm m le_rfl⟩
    let M : ℕ := Nat.find hexistsTerminal
    have htM : t M = 1 := by
      simpa [M] using Nat.find_spec hexistsTerminal
    have hMpos : 0 < M := by
      by_contra hM
      have hMzero : M = 0 := Nat.eq_zero_of_not_pos hM
      have : (0 : I) = 1 := by simpa [hMzero, htzero] using htM
      exact zero_ne_one this
    have htstrict {n : ℕ} (hn : n < M) : t n < t (n + 1) := by
      have htne : t n ≠ 1 := by
        simpa [M] using Nat.find_min hexistsTerminal hn
      have hnlt : n • step < (1 : ℝ) := by
        rw [← not_le]
        intro hn
        apply htne
        simpa [t, Set.Icc.addNSMul] using
          (projIcc_eq_one.mpr hn)
      have hnnonneg : 0 ≤ n • step := nsmul_nonneg hstep.le n
      have hsuccnonneg : 0 ≤ (n + 1) • step := nsmul_nonneg hstep.le (n + 1)
      have hinc : n • step < (n + 1) • step := by
        rw [succ_nsmul']
        exact lt_add_of_pos_left _ hstep
      change (t n : ℝ) < (t (n + 1) : ℝ)
      simp only [t, Set.Icc.addNSMul, Set.coe_projIcc]
      simp only [zero_add]
      rw [max_eq_right (le_min zero_le_one hnnonneg),
        max_eq_right (le_min zero_le_one hsuccnonneg),
        min_eq_right hnlt.le]
      exact lt_min hnlt hinc
    have hcellBall (n : ℕ) :
        Set.Icc (t n) (t (n + 1)) ⊆ Metric.ball (t n) δ := by
      intro u hu
      rw [Metric.mem_ball]
      have habs := Set.Icc.abs_sub_addNSMul_le
        (h := zero_le_one) hstep.le n hu
      simpa [t, step, Subtype.dist_eq, Real.dist_eq] using
        habs.trans_lt (half_lt_self hδ)
    have hcellTarget (n : ℕ) :
        ∃ i : A.target.Index, Set.Icc (t n) (t (n + 1)) ⊆ paramSet i := by
      obtain ⟨i, hi⟩ := hball (t n) (Set.mem_univ _)
      exact ⟨i, (hcellBall n).trans hi⟩
    let cellIndex : ℕ → A.target.Index := fun n ↦
      Classical.choose (hcellTarget n)
    have hcellIndex (n : ℕ) :
        Set.Icc (t n) (t (n + 1)) ⊆ paramSet (cellIndex n) :=
      Classical.choose_spec (hcellTarget n)
    have hMne : M ≠ 0 := Nat.ne_of_gt hMpos
    obtain ⟨N, hMN⟩ := Nat.exists_eq_succ_of_ne_zero hMne
    have htend : t (N + 1) = 1 := by simpa [hMN] using htM
    have htstrict' {n : ℕ} (hn : n < N + 1) : t n < t (n + 1) := by
      apply htstrict
      simpa [hMN] using hn
    let cut (n : ℕ) : ℝ := ((t n : ℝ) + (t (n + 1) : ℝ)) / 2
    have hcut_left {n : ℕ} (hn : n < N + 1) :
        (t n : ℝ) < cut n := by
      have hs := htstrict' hn
      change (t n : ℝ) < (t (n + 1) : ℝ) at hs
      dsimp [cut]
      linarith
    have hcut_right {n : ℕ} (hn : n < N + 1) :
        cut n < (t (n + 1) : ℝ) := by
      have hs := htstrict' hn
      change (t n : ℝ) < (t (n + 1) : ℝ) at hs
      dsimp [cut]
      linarith
    have hcut_mono : Monotone cut := by
      intro i j hij
      have h₀ := htmono hij
      have h₁ := htmono (Nat.succ_le_succ hij)
      change (t i : ℝ) ≤ (t j : ℝ) at h₀
      change (t (i + 1) : ℝ) ≤ (t (j + 1) : ℝ) at h₁
      dsimp [cut]
      linarith
    let cellSet (i : Fin (N + 1)) : Set I :=
      paramSet (cellIndex i.val) ∩
        {u | i.val = 0 ∨ cut (i.val - 1) < (u : ℝ)} ∩
        {u | i.val = N ∨ (u : ℝ) < cut (i.val + 1)}
    have hcellSetOpen (i : Fin (N + 1)) : IsOpen (cellSet i) := by
      have hlower : IsOpen {u : I | i.val = 0 ∨ cut (i.val - 1) < (u : ℝ)} := by
        by_cases hi : i.val = 0
        · simp [hi]
        · simpa [hi] using
            (isOpen_lt continuous_const continuous_subtype_val)
      have hupper : IsOpen {u : I | i.val = N ∨ (u : ℝ) < cut (i.val + 1)} := by
        by_cases hi : i.val = N
        · simp [hi]
        · simpa [hi] using
            (isOpen_lt continuous_subtype_val continuous_const)
      exact ((hparamOpen (cellIndex i.val)).inter hlower).inter hupper
    have hclosedCell_subset (i : Fin (N + 1)) :
        Set.Icc (t i.val) (t (i.val + 1)) ⊆ cellSet i := by
      intro u hu
      have hlower : i.val = 0 ∨ cut (i.val - 1) < (u : ℝ) := by
        by_cases hi : i.val = 0
        · exact Or.inl hi
        · right
          have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi
          have hpred : i.val - 1 + 1 = i.val :=
            Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)
          have hc := hcut_right (n := i.val - 1) (by omega)
          rw [hpred] at hc
          exact hc.trans_le hu.1
      have hupper : i.val = N ∨ (u : ℝ) < cut (i.val + 1) := by
        by_cases hi : i.val = N
        · exact Or.inl hi
        · right
          have hiN : i.val < N := by omega
          have hu' : (u : ℝ) ≤ (t (i.val + 1) : ℝ) := hu.2
          exact hu'.trans_lt (hcut_left (n := i.val + 1) (by omega))
      exact ⟨⟨hcellIndex i.val hu, hlower⟩, hupper⟩
    have hexistsCell (u : I) :
        ∃ i : Fin (N + 1), u ∈ Set.Icc (t i.val) (t (i.val + 1)) := by
      have hex : ∃ n : ℕ, u ≤ t (n + 1) := ⟨N, by simpa [htend] using u.2.2⟩
      let n : ℕ := Nat.find hex
      have hnle : n ≤ N :=
        Nat.find_min' hex (by simpa [htend] using u.2.2)
      refine ⟨⟨n, Nat.lt_succ_iff.mpr hnle⟩, ?_, Nat.find_spec hex⟩
      by_cases hn : n = 0
      · simpa [hn, htzero] using u.2.1
      · have hpred : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_ne_zero hn) Nat.one_pos
        have hnot := Nat.find_min hex hpred
        have : ¬ u ≤ t n := by simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using hnot
        exact le_of_lt (lt_of_not_ge this)
    let fine : FiniteOpenCover X := {
      Index := Fin (N + 1)
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      set := fun i ↦ q ⁻¹' cellSet i
      isOpen_set := fun i ↦ (hcellSetOpen i).preimage hq
      nonempty_set := by
        intro i
        obtain ⟨x, hx⟩ := hqsurj (t i.val)
        refine ⟨x, ?_⟩
        change q x ∈ cellSet i
        rw [hx]
        apply hclosedCell_subset i
        exact ⟨le_rfl, htmono (Nat.le_succ _)⟩
      covers := by
        intro x _
        obtain ⟨i, hi⟩ := hexistsCell (q x)
        exact Set.mem_iUnion.mpr ⟨i, hclosedCell_subset i hi⟩ }
    let r : fine.Refinement coarse := {
      indexMap := fun i ↦ A.indexMap (cellIndex i.val)
      subordinate := by
        intro i x hx
        apply A.preimage_subordinate (cellIndex i.val)
        have hxparam : q x ∈ paramSet (cellIndex i.val) := hx.1.1
        change embed (q x) ∈ A.target.set (cellIndex i.val) at hxparam
        simpa [hembed_q x] using hxparam }
    have hfar {i j : Fin (N + 1)} (hij : i.val + 2 ≤ j.val) :
        ¬ (fine.set i ∩ fine.set j).Nonempty := by
      rintro ⟨x, hxi, hxj⟩
      have hiN : i.val ≠ N := by omega
      have hjzero : j.val ≠ 0 := by omega
      have hiupper : (q x : ℝ) < cut (i.val + 1) := hxi.2.resolve_left hiN
      have hjlower : cut (j.val - 1) < (q x : ℝ) := hxj.1.2.resolve_left hjzero
      have hcuts : cut (i.val + 1) ≤ cut (j.val - 1) :=
        hcut_mono (by omega)
      linarith
    have hadjacent (i : Fin N) :
        (fine.set i.castSucc ∩ fine.set i.succ).Nonempty := by
      obtain ⟨x, hx⟩ := hqsurj (t (i.val + 1))
      refine ⟨x, ?_, ?_⟩
      · change q x ∈ cellSet i.castSucc
        rw [hx]
        apply hclosedCell_subset i.castSucc
        exact ⟨htmono (Nat.le_succ _), le_rfl⟩
      · change q x ∈ cellSet i.succ
        rw [hx]
        apply hclosedCell_subset i.succ
        exact ⟨le_rfl, htmono (Nat.le_succ _)⟩
    have hsingleton (i : Fin (N + 1)) : fine.IsNerveFace {i} := by
      refine ⟨by simp, ?_⟩
      rcases fine.nonempty_set i with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa using hx
    have hedge (i : Fin N) :
        fine.IsNerveFace {i.castSucc, i.succ} := by
      refine ⟨by simp, ?_⟩
      rcases hadjacent i with ⟨x, hxi, hxj⟩
      refine ⟨x, ?_⟩
      simp only [Set.mem_iInter]
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact hxi
      · exact hxj
    refine ⟨fine, r, N, Equiv.refl (Fin (N + 1)), ?_⟩
    intro s
    constructor
    · intro hs
      rcases hs.2 with ⟨x, hx⟩
      have hxmem (j : Fin (N + 1)) (hj : j ∈ s) : x ∈ fine.set j := by
        have hx' : ∀ j, j ∈ s → x ∈ fine.set j := by
          simpa only [Set.mem_iInter] using hx
        exact hx' j hj
      let i : Fin (N + 1) := s.min' hs.1
      have hi : i ∈ s := s.min'_mem hs.1
      have himin (j : Fin (N + 1)) (hj : j ∈ s) : i ≤ j :=
        s.min'_le j hj
      have hmember (j : Fin (N + 1)) (hj : j ∈ s) :
          j = i ∨ j.val = i.val + 1 := by
        have hle : i.val ≤ j.val := himin j hj
        have hclose : j.val ≤ i.val + 1 := by
          by_contra hnot
          have hfarij : i.val + 2 ≤ j.val := by omega
          exact hfar hfarij ⟨x, hxmem i hi, hxmem j hj⟩
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          have hneval : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
          omega
      by_cases hextra : ∃ j ∈ s, j ≠ i
      · rcases hextra with ⟨j, hj, hji⟩
        have hjval : j.val = i.val + 1 := (hmember j hj).resolve_left hji
        have hiN : i.val < N := by omega
        let k : Fin N := ⟨i.val, hiN⟩
        right
        refine ⟨k, ?_⟩
        change s = {k.castSucc, k.succ}
        have hki : k.castSucc = i := Fin.ext rfl
        have hkj : k.succ = j := Fin.ext (by simpa [k] using hjval.symm)
        rw [hki, hkj]
        apply Finset.Subset.antisymm
        · intro z hz
          rcases hmember z hz with rfl | hzval
          · simp
          · have hzj : z = j := Fin.ext (hzval.trans hjval.symm)
            simp [hzj]
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hi
          · exact hj
      · left
        refine ⟨i, ?_⟩
        change s = {i}
        apply Finset.Subset.antisymm
        · intro j hj
          have : j = i := by
            by_contra hji
            exact hextra ⟨j, hj, hji⟩
          simp [this]
        · intro j hj
          simp only [Finset.mem_singleton] at hj
          subst j
          exact hi
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · change fine.IsNerveFace {i}
        exact hsingleton i
      · change fine.IsNerveFace {i.castSucc, i.succ}
        exact hedge i

/-- The barycentric full nerve of a finite path has an explicit normalized
reduced-chain contraction. -/
private theorem pathNerve_exists_identity_constant_reducedChainHomotopy
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X)
    (hpath : U.IsPathNerve) (p : ℕ) :
    ∃ v : U.NerveFace, Nonempty (PosetNerve.StrictReducedChainHomotopy p
      (OrderHom.id : U.NerveFace →o U.NerveFace)
      (OrderHom.const U.NerveFace v)) := by
  classical
  obtain ⟨N, e, hface⟩ := hpath
  let clipIndex (m : ℕ) (i : U.Index) : U.Index :=
    e.symm ⟨min (e i).val m,
      (min_le_left (e i).val m).trans_lt (e i).isLt⟩
  have clipIndex_of_le {m : ℕ} (hm : m ≤ N) (i : U.Index)
      (hi : m ≤ (e i).val) :
      clipIndex m i = e.symm ⟨m, Nat.lt_succ_of_le hm⟩ := by
    apply e.injective
    simp [clipIndex, min_eq_right hi]
  have clipIndex_of_ge (m : ℕ) (i : U.Index)
      (hi : (e i).val ≤ m) : clipIndex m i = i := by
    apply e.injective
    simp [clipIndex, min_eq_left hi]
  let clipFace (m : ℕ) (hm : m ≤ N) : U.NerveFace →o U.NerveFace := {
    toFun := fun a ↦ ⟨a.1.image (clipIndex m), by
      rw [hface]
      rcases (hface a.1).mp a.2 with ⟨i, hai⟩ | ⟨i, hai⟩
      · left
        exact ⟨⟨min i.val m,
          (min_le_left i.val m).trans_lt i.isLt⟩, by
            rw [hai]
            simp [clipIndex]⟩
      · by_cases him : i.val < m
        · right
          refine ⟨i, ?_⟩
          have hi₀ : clipIndex m (e.symm i.castSucc) = e.symm i.castSucc := by
            apply clipIndex_of_ge
            simpa using him.le
          have hi₁ : clipIndex m (e.symm i.succ) = e.symm i.succ := by
            apply clipIndex_of_ge
            simp only [Equiv.apply_symm_apply, Fin.val_succ]
            omega
          rw [hai]
          simp [hi₀, hi₁]
        · left
          let j : Fin (N + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
          refine ⟨j, ?_⟩
          have hi₀ : clipIndex m (e.symm i.castSucc) = e.symm j := by
            apply clipIndex_of_le hm
            simpa using Nat.le_of_not_gt him
          have hi₁ : clipIndex m (e.symm i.succ) = e.symm j := by
            apply clipIndex_of_le hm
            simp only [Equiv.apply_symm_apply, Fin.val_succ]
            omega
          rw [hai]
          simp [hi₀, hi₁] ⟩
    monotone' := by
      intro a b hab
      exact Finset.image_mono _ hab }
  have clip_contiguous (m : ℕ) (hm : m < N) :
      ∀ a : U.NerveFace,
        U.IsNerveFace
          ((clipFace (m + 1) (Nat.succ_le_of_lt hm) a).1 ∪
            (clipFace m hm.le a).1) := by
    intro a
    rw [hface]
    change
      (∃ i : Fin (N + 1),
        a.1.image (clipIndex (m + 1)) ∪ a.1.image (clipIndex m) =
          {e.symm i}) ∨
      ∃ i : Fin N,
        a.1.image (clipIndex (m + 1)) ∪ a.1.image (clipIndex m) =
          {e.symm i.castSucc, e.symm i.succ}
    rcases (hface a.1).mp a.2 with ⟨i, hai⟩ | ⟨i, hai⟩
    · by_cases hi : i.val ≤ m
      · left
        refine ⟨i, ?_⟩
        have h₀ : clipIndex m (e.symm i) = e.symm i := by
          apply clipIndex_of_ge
          simpa
        have h₁ : clipIndex (m + 1) (e.symm i) = e.symm i := by
          apply clipIndex_of_ge
          simpa using hi.trans (Nat.le_succ m)
        rw [hai]
        simp [clipFace, h₀, h₁]
      · right
        let j : Fin N := ⟨m, hm⟩
        refine ⟨j, ?_⟩
        have hi' : m + 1 ≤ i.val := by omega
        have h₀ : clipIndex m (e.symm i) = e.symm j.castSucc := by
          apply clipIndex_of_le hm.le
          simpa using (show m ≤ i.val by omega)
        have h₁ : clipIndex (m + 1) (e.symm i) = e.symm j.succ := by
          apply clipIndex_of_le (Nat.succ_le_of_lt hm)
          simpa using hi'
        rw [hai]
        simp [clipFace, h₀, h₁, Finset.pair_comm]
    · by_cases hi : i.val < m
      · right
        refine ⟨i, ?_⟩
        have h₀ : clipIndex m (e.symm i.castSucc) = e.symm i.castSucc := by
          apply clipIndex_of_ge
          simpa using hi.le
        have h₁ : clipIndex m (e.symm i.succ) = e.symm i.succ := by
          apply clipIndex_of_ge
          simp only [Equiv.apply_symm_apply, Fin.val_succ]
          omega
        have h₂ : clipIndex (m + 1) (e.symm i.castSucc) = e.symm i.castSucc := by
          apply clipIndex_of_ge
          simpa using hi.le.trans (Nat.le_succ m)
        have h₃ : clipIndex (m + 1) (e.symm i.succ) = e.symm i.succ := by
          apply clipIndex_of_ge
          simp only [Equiv.apply_symm_apply, Fin.val_succ]
          omega
        rw [hai]
        simp [clipFace, h₀, h₁, h₂, h₃]
      · right
        let j : Fin N := ⟨m, hm⟩
        refine ⟨j, ?_⟩
        have hmi : m ≤ i.val := Nat.le_of_not_gt hi
        have h₀ : clipIndex m (e.symm i.castSucc) = e.symm j.castSucc := by
          apply clipIndex_of_le hm.le
          simpa using hmi
        have h₁ : clipIndex m (e.symm i.succ) = e.symm j.castSucc := by
          apply clipIndex_of_le hm.le
          simp only [Equiv.apply_symm_apply, Fin.val_succ]
          omega
        have h₃ : clipIndex (m + 1) (e.symm i.succ) =
            e.symm j.succ := by
          apply clipIndex_of_le (Nat.succ_le_of_lt hm)
          simp only [Equiv.apply_symm_apply, Fin.val_succ]
          omega
        by_cases him : i.val = m
        · have h₂ : clipIndex (m + 1) (e.symm i.castSucc) =
              e.symm j.castSucc := by
            rw [clipIndex_of_ge]
            · apply congrArg e.symm
              apply Fin.ext
              simpa [j] using him
            · simp only [Equiv.apply_symm_apply, Fin.val_castSucc]
              omega
          rw [hai]
          simp [clipFace, h₀, h₁, h₂, h₃, Finset.pair_comm]
        · have h₂ : clipIndex (m + 1) (e.symm i.castSucc) =
              e.symm j.succ := by
            apply clipIndex_of_le (Nat.succ_le_of_lt hm)
            simp only [Equiv.apply_symm_apply, Fin.val_castSucc]
            omega
          rw [hai]
          simp [clipFace, h₀, h₁, h₂, h₃, Finset.pair_comm]
  have clip_step (m : ℕ) (hm : m < N) : Nonempty
      (PosetNerve.StrictReducedChainHomotopy p
        (clipFace (m + 1) (Nat.succ_le_of_lt hm)) (clipFace m hm.le)) := by
    let upper : U.NerveFace →o U.NerveFace := {
      toFun := fun a ↦ ⟨(clipFace (m + 1) (Nat.succ_le_of_lt hm) a).1 ∪
        (clipFace m hm.le a).1, clip_contiguous m hm a⟩
      monotone' := by
        intro a b hab
        exact Finset.union_subset_union
          (Finset.image_mono _ hab) (Finset.image_mono _ hab) }
    exact posetNerve_strictReducedChainHomotopy_of_commonUpperBound
      (clipFace (m + 1) (Nat.succ_le_of_lt hm)) (clipFace m hm.le) upper
      (fun _ ↦ Finset.subset_union_left)
      (fun _ ↦ Finset.subset_union_right)
  have clip_to_zero : ∀ m : ℕ, ∀ hm : m ≤ N, Nonempty
      (PosetNerve.StrictReducedChainHomotopy p
        (clipFace m hm) (clipFace 0 (Nat.zero_le N))) := by
    intro m
    induction m with
    | zero =>
        intro hm
        exact ⟨PosetNerve.StrictReducedChainHomotopy.refl _⟩
    | succ m ih =>
        intro hm
        have hmlt : m < N := Nat.lt_of_succ_le hm
        obtain ⟨Hs⟩ := clip_step m hmlt
        obtain ⟨H₀⟩ := ih (Nat.le_of_succ_le hm)
        exact ⟨Hs.trans H₀⟩
  let rootIndex : U.Index := e.symm 0
  have hrootFace : U.IsNerveFace {rootIndex} := by
    rw [hface]
    exact Or.inl ⟨0, rfl⟩
  let root : U.NerveFace := ⟨{rootIndex}, hrootFace⟩
  have hclipTop : clipFace N le_rfl = (OrderHom.id : U.NerveFace →o U.NerveFace) := by
    apply OrderHom.ext
    funext a
    apply Subtype.ext
    have hindex : clipIndex N = id := by
      funext i
      apply clipIndex_of_ge
      omega
    simp [clipFace, hindex]
  have hclipZero : clipFace 0 (Nat.zero_le N) = OrderHom.const U.NerveFace root := by
    apply OrderHom.ext
    funext a
    apply Subtype.ext
    have hindex : clipIndex 0 = fun _ ↦ rootIndex := by
      funext i
      apply clipIndex_of_le (Nat.zero_le N)
      exact Nat.zero_le _
    change Finset.image (clipIndex 0) a.1 = {rootIndex}
    rw [hindex, Finset.image_const a.2.1]
  obtain ⟨H⟩ := clip_to_zero N le_rfl
  refine ⟨root, ?_⟩
  rw [hclipTop, hclipZero] at H
  exact ⟨H⟩

/-- A constant poset map annihilates every reduced normalized strict chain. -/
private theorem posetNerve_strictChainMap_const_eq_zero_of_reducedCycle
    {p : ℕ} {P Q : Type} [PartialOrder P] [Fintype P]
    [PartialOrder Q] [Fintype Q] (q : Q) {n : ℕ}
    (z : PosetNerve.strictChains P n →₀ ZMod p)
    (hz : PosetNerve.StrictIsReducedCycle P p n z) :
    PosetNerve.strictChainMap P Q (ZMod p) (OrderHom.const P q) n z = 0 := by
  classical
  cases n with
  | zero =>
      change PosetNerve.strictAugment P (ZMod p) z = 0 at hz
      let q₀ : PosetNerve.strictChains Q 0 :=
        ⟨fun _ ↦ q, by
          intro i j hij
          omega⟩
      have hmap_all (c : PosetNerve.strictChains P 0 →₀ ZMod p) :
          PosetNerve.strictChainMap P Q (ZMod p) (OrderHom.const P q) 0 c =
            Finsupp.single q₀ (PosetNerve.strictAugment P (ZMod p) c) := by
        induction c using Finsupp.induction with
        | zero => simp
        | single_add a r z ha hr ih =>
            have hs : StrictMono
                (fun j : Fin 1 ↦ (OrderHom.const P q) (a.1 j)) := by
              intro i j hij
              omega
            have himage :
                PosetNerve.strictChainImage P Q (OrderHom.const P q) a hs = q₀ := by
              apply Subtype.ext
              funext j
              rfl
            rw [map_add, PosetNerve.strictChainMap_single_of_strict
              P Q (ZMod p) (OrderHom.const P q) 0 a r hs,
              himage, ih, map_add, PosetNerve.strictAugment_single]
            exact (Finsupp.single_add q₀ r
              (PosetNerve.strictAugment P (ZMod p) z)).symm
      rw [hmap_all z, hz, Finsupp.single_zero]
  | succ n =>
      clear hz
      induction z using Finsupp.induction with
      | zero => simp
      | single_add a r z ha hr ih =>
          have hnot : ¬ StrictMono
              (fun j : Fin (n + 2) ↦ (OrderHom.const P q) (a.1 j)) := by
            intro hs
            let one : Fin (n + 2) := ⟨1, by omega⟩
            have hlt := hs (show (0 : Fin (n + 2)) < one by simp [one])
            exact (lt_irrefl q) hlt
          rw [map_add, PosetNerve.strictChainMap_single_of_not_strict
            P Q (ZMod p) (OrderHom.const P q) (n + 1) a r hnot,
            ih, zero_add]

private theorem pathNerve_exists_strictReducedContraction
    {X : Type*} [TopologicalSpace X] (U : FiniteOpenCover X)
    (hpath : U.IsPathNerve) (p : ℕ) :
    Nonempty (PosetNerve.StrictReducedContraction p U.NerveFace) := by
  obtain ⟨v, ⟨H⟩⟩ :=
    pathNerve_exists_identity_constant_reducedChainHomotopy U hpath p
  refine ⟨{
    fill := H.prism
    boundary_fill := ?_ }⟩
  intro n z hz
  rw [H.boundary_prism n z hz,
    posetNerve_strictChainMap_id p n z,
    posetNerve_strictChainMap_const_eq_zero_of_reducedCycle v z hz,
    sub_zero]

/-- An explicit reduced contraction makes the identity map kill reduced
homology. -/
private theorem PosetNerve.StrictReducedContraction.kills
    {p : ℕ} {P : Type} [PartialOrder P] [Fintype P]
    (C : PosetNerve.StrictReducedContraction p P) :
    PosetNerve.StrictMapKillsReducedHomology p (OrderHom.id : P →o P) := by
  intro n z hz
  refine ⟨C.fill n z, ?_⟩
  rw [C.boundary_fill n z hz,
    posetNerve_strictChainMap_id p n z]

/-- A refinement out of a path-nerve cover kills reduced homology, since its
source cycles first bound and chain maps preserve boundaries. -/
private theorem FiniteOpenCover.Refinement.kills_of_pathNerve
    {X : Type*} [TopologicalSpace X] {fine coarse : FiniteOpenCover X}
    {p : ℕ} (r : fine.Refinement coarse) (hpath : fine.IsPathNerve) :
    PosetNerve.StrictMapKillsReducedHomology p r.faceOrderHom := by
  obtain ⟨C⟩ := pathNerve_exists_strictReducedContraction fine hpath p
  have hid := C.kills
  intro n z hz
  obtain ⟨w, hw⟩ := hid n z hz
  refine ⟨PosetNerve.strictChainMap fine.NerveFace coarse.NerveFace
    (ZMod p) r.faceOrderHom (n + 1) w, ?_⟩
  rw [← PosetNerve.strictChainMap_boundary, hw,
    posetNerve_strictChainMap_id]

/-- The nonequivariant arc-like step: for any finite open cover, an ordinary
finer cover has a canonical full-nerve map which kills all reduced homology.
Connectedness is needed exactly in degree zero. -/
private theorem arcLike_exists_plainNerveRefinement_killingReducedHomology
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (coarse : FiniteOpenCover X) {p : ℕ} :
    ∃ fine : FiniteOpenCover X, ∃ r : fine.Refinement coarse,
      PosetNerve.StrictMapKillsReducedHomology p r.faceOrderHom := by
  obtain ⟨A⟩ := arcLike_exists_intervalTargetSubordination harc coarse
  obtain ⟨fine, r, hpath⟩ :=
    intervalTargetSubordination_exists_pathNerveRefinement
      hconnected coarse A
  exact ⟨fine, r, r.kills_of_pathNerve hpath⟩

/-- Intersecting the finitely many translates of an ordinary cover and
duplicating each geometric intersection by a rotating anchor produces the
anchored invariant common refinement. -/
private theorem finiteOpenCover_exists_cyclicCommonRefinement
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) (base : FiniteOpenCover X) :
    Nonempty (base.CyclicCommonRefinement V p hp) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  let E : Fin p ≃+* ZMod p := ZMod.finEquiv p
  let geometricSet (c : ZMod p → base.Index) : Set X :=
    ⋂ k : ZMod p,
      (V ^ k.val : X ≃ₜ X) '' base.set (c k)
  have geometricSet_open (c : ZMod p → base.Index) :
      IsOpen (geometricSet c) := by
    dsimp only [geometricSet]
    exact isOpen_iInter_of_finite fun k ↦
      (V ^ k.val : X ≃ₜ X).isOpenMap _ (base.isOpen_set (c k))
  have power_add_one (k : ZMod p) :
      V * (V ^ k.val : X ≃ₜ X) = V ^ (k + 1).val := by
    by_cases hk : k.val + 1 < p
    · have hval : (k + 1).val = k.val + 1 := by
        simpa [ZMod.val_one p] using
          (ZMod.val_add_of_lt (a := k) (b := (1 : ZMod p))
            (by simpa [ZMod.val_one p] using hk))
      rw [hval, pow_succ']
    · have hkEq : k.val + 1 = p := by
        have hklt := ZMod.val_lt k
        omega
      have hval : (k + 1).val = 0 := by
        rw [ZMod.val_add_of_le]
        · simp [ZMod.val_one p, hkEq]
        · simpa [ZMod.val_one p, hkEq]
      rw [hval, pow_zero]
      calc
        V * V ^ k.val = V ^ (k.val + 1) := (pow_succ' V k.val).symm
        _ = V ^ p := by rw [hkEq]
        _ = 1 := hperiodic
  have image_power_add_one (k : ZMod p) (A : Set X) :
      V '' ((V ^ k.val : X ≃ₜ X) '' A) =
        (V ^ (k + 1).val : X ≃ₜ X) '' A := by
    have hfun : (fun x : X ↦ V ((V ^ k.val : X ≃ₜ X) x)) =
        fun x : X ↦ (V ^ (k + 1).val : X ≃ₜ X) x := by
      funext x
      exact congrArg (fun e : X ≃ₜ X ↦ e x) (power_add_one k)
    simpa [Set.image_image] using congrArg (fun f : X → X ↦ f '' A) hfun
  let shift : Equiv.Perm (ZMod p → base.Index) := {
    toFun := fun c k ↦ c (k - 1)
    invFun := fun c k ↦ c (k + 1)
    left_inv := by
      intro c
      funext k
      congr 1
      ring
    right_inv := by
      intro c
      funext k
      congr 1
      ring }
  have geometricSet_shift (c : ZMod p → base.Index) :
      V '' geometricSet c = geometricSet (shift c) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [show V x ∈ geometricSet (shift c) ↔
          ∀ z : ZMod p, V x ∈
            (V ^ z.val : X ≃ₜ X) '' base.set (shift c z) by
        simp [geometricSet]]
      intro z
      let w : ZMod p := z - 1
      have hxw := Set.mem_iInter.mp hx w
      have himage : V x ∈ V ''
          ((V ^ w.val : X ≃ₜ X) '' base.set (c w)) :=
        ⟨x, hxw, rfl⟩
      rw [image_power_add_one] at himage
      have hwz : w + 1 = z := by
        dsimp only [w]
        ring
      simpa [shift, hwz] using himage
    · intro hy
      let x : X := V.symm y
      refine ⟨x, ?_, V.apply_symm_apply y⟩
      rw [show x ∈ geometricSet c ↔
          ∀ w : ZMod p, x ∈
            (V ^ w.val : X ≃ₜ X) '' base.set (c w) by
        simp [geometricSet]]
      intro w
      have hyw := Set.mem_iInter.mp hy (w + 1)
      have hshift : shift c (w + 1) = c w := by
        change c (w + 1 - 1) = c w
        congr 1
        ring
      have hyimage : y ∈
          (V ^ (w + 1).val : X ≃ₜ X) '' base.set (c w) := by
        simpa [hshift] using hyw
      rw [← image_power_add_one] at hyimage
      rcases hyimage with ⟨x', hx', hVx'⟩
      have hx'eq : x' = x := by
        dsimp only [x]
        rw [← hVx']
        exact (V.symm_apply_apply x').symm
      simpa [hx'eq] using hx'
  let RawIndex := ZMod p × (ZMod p → base.Index)
  let rawAction : Equiv.Perm RawIndex :=
    Equiv.prodCongr (Equiv.addRight 1) shift
  have rawAction_periodic : rawAction ^ p = 1 := by
    apply Equiv.ext
    intro q
    rw [Equiv.Perm.coe_pow]
    have hiter : ∀ n : ℕ, rawAction^[n] q =
        (q.1 + n, fun z ↦ q.2 (z - n)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih]
          apply Prod.ext
          · change q.1 + (n : ZMod p) + 1 =
              q.1 + ((n + 1 : ℕ) : ZMod p)
            rw [Nat.cast_add, Nat.cast_one]
            abel
          · funext z
            change q.2 (z - 1 - (n : ZMod p)) =
              q.2 (z - ((n + 1 : ℕ) : ZMod p))
            congr 1
            rw [Nat.cast_add, Nat.cast_one]
            ring
    simpa using hiter p
  let GoodIndex := {q : RawIndex // (geometricSet q.2).Nonempty}
  let indexAction : Equiv.Perm GoodIndex := {
    toFun := fun i ↦ ⟨rawAction i.1, by
      have hi : (V '' geometricSet i.1.2).Nonempty := i.2.image V
      rw [geometricSet_shift] at hi
      simpa [rawAction] using hi⟩
    invFun := fun i ↦ ⟨rawAction.symm i.1, by
      let q : RawIndex := rawAction.symm i.1
      have hq : rawAction q = i.1 := rawAction.apply_symm_apply i.1
      have hi : (geometricSet (shift q.2)).Nonempty := by
        have hchoice : shift q.2 = i.1.2 := congrArg Prod.snd hq
        simpa [hchoice] using i.2
      rw [← geometricSet_shift] at hi
      rcases hi with ⟨_, x, hx, _⟩
      exact ⟨x, by simpa [q] using hx⟩⟩
    left_inv := by
      intro i
      apply Subtype.ext
      exact rawAction.symm_apply_apply i.1
    right_inv := by
      intro i
      apply Subtype.ext
      exact rawAction.apply_symm_apply i.1 }
  have indexAction_periodic : indexAction ^ p = 1 := by
    apply Equiv.ext
    intro i
    rw [Equiv.Perm.coe_pow]
    apply Subtype.ext
    have hval : ∀ n : ℕ, (indexAction^[n] i).1 = rawAction^[n] i.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          change rawAction ((indexAction^[n] i).1) =
            rawAction (rawAction^[n] i.1)
          exact congrArg rawAction ih
    rw [hval]
    have hraw := congrArg (fun e : Equiv.Perm RawIndex ↦ e i.1)
      rawAction_periodic
    simpa using hraw
  have E_rotate (k : Fin p) : E (finRotate p k) = E k + 1 := by
    rw [finRotate_apply]
    simpa using map_add E k (1 : Fin p)
  have E_val (k : Fin p) : (E k).val = k.1 := by
    change (ZMod.finEquiv p k).val = k.1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
    rfl
  have choose_base (x : X) (k : ZMod p) :
      ∃ i : base.Index,
        (V ^ k.val : X ≃ₜ X).symm x ∈ base.set i := by
    have hx := base.covers (Set.mem_univ ((V ^ k.val : X ≃ₜ X).symm x))
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact ⟨i, hi⟩
  choose choice hchoice using choose_base
  have point_mem_geometricSet (x : X) : x ∈ geometricSet (choice x) := by
    rw [show x ∈ geometricSet (choice x) ↔
        ∀ k : ZMod p, x ∈
          (V ^ k.val : X ≃ₜ X) '' base.set (choice x k) by
      simp [geometricSet]]
    intro k
    exact ⟨(V ^ k.val : X ≃ₜ X).symm x, hchoice x k,
      (V ^ k.val : X ≃ₜ X).apply_symm_apply x⟩
  let fine : FiniteInvariantCover V p := {
    Index := GoodIndex
    indexFintype := inferInstance
    indexDecidableEq := inferInstance
    set := fun i ↦ geometricSet i.1.2
    isOpen_set := fun i ↦ geometricSet_open i.1.2
    nonempty_set := fun i ↦ i.2
    covers := by
      intro x _
      apply Set.mem_iUnion.mpr
      exact ⟨⟨((0 : ZMod p), choice x), ⟨x, point_mem_geometricSet x⟩⟩,
        point_mem_geometricSet x⟩
    action := indexAction
    action_periodic := indexAction_periodic
    equivariant := by
      intro i
      exact geometricSet_shift i.1.2 }
  refine ⟨{
    fine := fine
    projection := fun k i ↦ i.1.2 (E k)
    subordinate_translate := ?_
    projection_action := ?_
    anchor := fun i ↦ E.symm i.1.1
    anchor_action := ?_ }⟩
  · intro k i x hx
    have hxk := Set.mem_iInter.mp hx (E k)
    simpa [E_val k] using hxk
  · intro k i
    change (indexAction i).1.2 (E (finRotate p k)) = i.1.2 (E k)
    rw [E_rotate]
    change i.1.2 (E k + 1 - 1) = i.1.2 (E k)
    congr 1
    ring
  · intro i
    change E.symm ((indexAction i).1.1) =
      finRotate p (E.symm i.1.1)
    apply E.injective
    rw [E_rotate, E.apply_symm_apply]
    rw [E.apply_symm_apply]
    change (rawAction i.1).1 = i.1.1 + 1
    rfl

/-- The rotating anchor removes the stabilizer obstruction and selects an
equivariant refinement of the original invariant cover.  Its underlying
ordinary map is contiguous to the nonequivariant composite through the base
cover. -/
private theorem cyclicCommonRefinement_exists_equivariantSelection
    {X : Type*} [MetricSpace X] {V : X ≃ₜ X} {p : ℕ}
    (hp : Nat.Prime p) (coarse : FiniteInvariantCover V p)
    (base : FiniteOpenCover X)
    (a : base.Refinement coarse.toOpenCover)
    (S : base.CyclicCommonRefinement V p hp) :
    ∃ r : S.fine.Refinement coarse,
      (S.toBase.trans a).Contiguous r.toOpenRefinement := by
  classical
  have coarse_equivariant_pow (n : ℕ) (i : coarse.Index) :
      (V ^ n : X ≃ₜ X) '' coarse.set i =
        coarse.set ((coarse.action ^ n) i) := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (V ^ (n + 1) : X ≃ₜ X) '' coarse.set i =
              V '' ((V ^ n : X ≃ₜ X) '' coarse.set i) := by
            rw [pow_succ', Set.image_image]
            rfl
          _ = V '' coarse.set ((coarse.action ^ n) i) := by rw [ih]
          _ = coarse.set (coarse.action ((coarse.action ^ n) i)) :=
            coarse.equivariant _
          _ = coarse.set ((coarse.action ^ (n + 1)) i) := by
            simp [pow_succ']
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  have action_rotate (k : Fin (n + 1)) (i : coarse.Index) :
      (coarse.action ^ (finRotate (n + 1) k).1) i =
        coarse.action ((coarse.action ^ k.1) i) := by
    by_cases hk : k = Fin.last n
    · subst k
      have hperiod := congrArg (fun e : Equiv.Perm coarse.Index ↦ e i)
        coarse.action_periodic
      simpa [finRotate_last, pow_succ'] using hperiod.symm
    · rw [coe_finRotate_of_ne_last hk]
      simp [pow_succ']
  let rIndex : S.fine.Index → coarse.Index := fun i ↦
    (coarse.action ^ (S.anchor i).1)
      (a.indexMap (S.projection (S.anchor i) i))
  have rSubordinate (i : S.fine.Index) :
      S.fine.set i ⊆ coarse.set (rIndex i) := by
    intro x hx
    rcases S.subordinate_translate (S.anchor i) i hx with
      ⟨y, hybase, hyx⟩
    have hycoarse : y ∈ coarse.set
        (a.indexMap (S.projection (S.anchor i) i)) :=
      a.subordinate _ hybase
    have hximage : x ∈ (V ^ (S.anchor i).1 : X ≃ₜ X) ''
        coarse.set (a.indexMap (S.projection (S.anchor i) i)) :=
      ⟨y, hycoarse, hyx⟩
    rw [coarse_equivariant_pow] at hximage
    exact hximage
  have rEquivariant (i : S.fine.Index) :
      rIndex (S.fine.action i) = coarse.action (rIndex i) := by
    change (coarse.action ^ (S.anchor (S.fine.action i)).1)
        (a.indexMap
          (S.projection (S.anchor (S.fine.action i)) (S.fine.action i))) = _
    rw [S.anchor_action, S.projection_action]
    exact action_rotate (S.anchor i)
      (a.indexMap (S.projection (S.anchor i) i))
  let r : S.fine.Refinement coarse := {
    indexMap := rIndex
    subordinate := rSubordinate
    equivariant := rEquivariant }
  refine ⟨r, ?_⟩
  intro face
  refine ⟨face.2.1.image (S.toBase.trans a).indexMap |>.mono
      Finset.subset_union_left, ?_⟩
  rcases face.2.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  simp only [Set.mem_iInter] at hx ⊢
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact (S.toBase.trans a).subordinate i (hx i hi)
  · rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact r.subordinate i (hx i hi)

/-- Arc-likeness supplies one finer invariant full nerve whose equivariant
refinement map kills every reduced ambient homology class.  The proof now
exhibits the ordinary acyclic map, cyclic saturation, equivariant selection,
and normalized contiguity prism separately. -/
private theorem arcLike_exists_smithAcyclic_invariantRefinement
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X)
    (harc : IsArcLike X) (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) (coarse : FiniteInvariantCover V p) :
    ∃ fine : FiniteInvariantCover V p,
      ∃ r : fine.Refinement coarse,
        r.smithHom.KillsReducedHomology := by
  obtain ⟨base, a, ha⟩ :=
    arcLike_exists_plainNerveRefinement_killingReducedHomology
      hconnected harc coarse.toOpenCover
  obtain ⟨S⟩ := finiteOpenCover_exists_cyclicCommonRefinement
    V hp hperiodic base
  obtain ⟨r, hcont⟩ :=
    cyclicCommonRefinement_exists_equivariantSelection hp coarse base a S
  have hplain : PosetNerve.StrictMapKillsReducedHomology p
      (S.toBase.trans a).faceOrderHom := by
    rw [FiniteOpenCover.Refinement.faceOrderHom_trans]
    exact ha.comp
  obtain ⟨H⟩ :=
    FiniteOpenCover.Refinement.contiguous_reducedChainHomotopy hcont
  have heq : PosetNerve.StrictMapKillsReducedHomology p
      r.toOpenRefinement.faceOrderHom :=
    hplain.of_reducedChainHomotopy H
  exact ⟨S.fine, r, r.smithHom_kills_iff_strictMap.mpr heq⟩

/-- Finite choice recursion of the preceding one-step refinement, together
with a dimension bound for the bottom full nerve. -/
private theorem arcLike_exists_finiteSmithNerveCoverChain_over
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X)
    (harc : IsArcLike X) (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) (bottom : FiniteInvariantCover V p) :
    ∃ N : ℕ, ∃ C : FiniteSmithNerveCoverChain V p N,
      C.cover 0 = bottom := by
  classical
  let nextCover (U : FiniteInvariantCover V p) :
      FiniteInvariantCover V p :=
    Classical.choose (arcLike_exists_smithAcyclic_invariantRefinement
      hconnected harc V hp hperiodic U)
  have nextCover_spec (U : FiniteInvariantCover V p) :
      ∃ r : (nextCover U).Refinement U,
        r.smithHom.KillsReducedHomology :=
    Classical.choose_spec (arcLike_exists_smithAcyclic_invariantRefinement
      hconnected harc V hp hperiodic U)
  let nextRefinement (U : FiniteInvariantCover V p) :
      (nextCover U).Refinement U := Classical.choose (nextCover_spec U)
  have nextRefinement_acyclic (U : FiniteInvariantCover V p) :
      (nextRefinement U).smithHom.KillsReducedHomology :=
    Classical.choose_spec (nextCover_spec U)
  let coverNat : ℕ → FiniteInvariantCover V p :=
    Nat.rec bottom (fun _ U ↦ nextCover U)
  obtain ⟨N, hN⟩ := bottom.smithComplex.bounded
  let C : FiniteSmithNerveCoverChain V p N := {
    cover := fun i ↦ coverNat i.1
    refinement := fun i ↦ by
      change (coverNat (i.1 + 1)).Refinement (coverNat i.1)
      simpa [coverNat] using nextRefinement (coverNat i.1)
    step_acyclic := fun i ↦ by
      change (nextRefinement (coverNat i.1)).smithHom.KillsReducedHomology
      exact nextRefinement_acyclic (coverNat i.1)
    bottom_bounded := by
      intro n hn
      simpa [coverNat] using hN n hn }
  exact ⟨N, C, by rfl⟩

/-- A finite acyclic cover chain extends constantly after its last level;
composite refinements and strict nerve maps give all tower maps and their
coherence fields. -/
private theorem finiteSmithNerveCoverChain_exists_tower
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p N : ℕ}
    (C : FiniteSmithNerveCoverChain V p N) :
    ∃ P : ArcLikeSmithNerveTower V p, P.cover 0 = C.cover 0 := by
  classical
  let L : ℕ := smithH0TowerLength p N
  let clip (n : ℕ) : Fin (L + 1) :=
    ⟨min n L, by omega⟩
  let coverNat (n : ℕ) : FiniteInvariantCover V p := C.cover (clip n)
  let stepPackage (n : ℕ) :
      {r : (coverNat (n + 1)).Refinement (coverNat n) //
        n < L → r.smithHom.KillsReducedHomology} := by
    by_cases hn : n < L
    · have hnEq : coverNat n = C.cover ⟨n, by omega⟩ := by
        apply congrArg C.cover
        apply Fin.ext
        simp [coverNat, clip, min_eq_left hn.le]
      have hsuccEq : coverNat (n + 1) = C.cover ⟨n + 1, by omega⟩ := by
        apply congrArg C.cover
        apply Fin.ext
        simp [coverNat, clip, min_eq_left (Nat.succ_le_iff.mpr hn)]
      rw [hnEq, hsuccEq]
      exact ⟨C.refinement ⟨n, hn⟩, fun _ ↦ C.step_acyclic ⟨n, hn⟩⟩
    · have hnL : L ≤ n := Nat.le_of_not_gt hn
      let r : (coverNat (n + 1)).Refinement (coverNat n) := by
        simpa [coverNat, clip, min_eq_right hnL,
          min_eq_right (hnL.trans (Nat.le_succ n))] using
            FiniteInvariantCover.Refinement.refl
              (C.cover ⟨L, by omega⟩)
      exact ⟨r, fun h ↦ (hn h).elim⟩
  let stepNat (n : ℕ) :
      (coverNat (n + 1)).Refinement (coverNat n) := (stepPackage n).1
  have stepNat_acyclic (n : ℕ) (hn : n < L) :
      (stepNat n).smithHom.KillsReducedHomology :=
    (stepPackage n).2 hn
  let between (i j : ℕ) (h : i ≤ j) :
      (coverNat j).Refinement (coverNat i) :=
    FiniteInvariantCover.refinementBetween coverNat stepNat i j h
  have between_refl (i : ℕ) :
      between i i le_rfl = FiniteInvariantCover.Refinement.refl (coverNat i) := by
    exact FiniteInvariantCover.refinementBetween_refl coverNat stepNat i
  have between_succ (i : ℕ) :
      between i (i + 1) (Nat.le_succ i) = stepNat i := by
    exact FiniteInvariantCover.refinementBetween_succ coverNat stepNat i
  have between_zero_succ (k : ℕ) :
      between 0 (k + 1) (Nat.zero_le _) =
        (between k (k + 1) (Nat.le_succ k)).trans
          (between 0 k (Nat.zero_le _)) := by
    exact FiniteInvariantCover.refinementBetween_zero_succ coverNat stepNat k
  let tower : FiniteCyclicAugmentedTower p := {
    level := fun i ↦ (coverNat i).smithComplex
    map := fun i j h ↦ (between i j h).smithHom
    map_refl := by
      intro i q c
      rw [between_refl]
      change PosetNerve.strictChainMap _ _ (ZMod p)
          (FiniteInvariantCover.Refinement.refl (coverNat i)).faceOrderHom q c = c
      rw [FiniteInvariantCover.Refinement.faceOrderHom_refl]
      exact posetNerve_strictChainMap_id p q c
    map_zero_succ := by
      intro k q c
      rw [between_zero_succ k]
      change PosetNerve.strictChainMap _ _ (ZMod p)
          (((between k (k + 1) (Nat.le_succ k)).trans
            (between 0 k (Nat.zero_le _))).faceOrderHom) q c = _
      rw [FiniteInvariantCover.Refinement.faceOrderHom_trans]
      have hcomp := posetNerve_strictChainMap_comp
        (p := p) (between k (k + 1) (Nat.le_succ k)).faceOrderHom
          (between 0 k (Nat.zero_le _)).faceOrderHom q
      exact LinearMap.congr_fun hcomp c }
  let P : ArcLikeSmithNerveTower V p := {
    N := N
    tower := tower
    cover := coverNat
    realization := fun i ↦ (coverNat i).canonicalNerveRealization
    refinement := between
    map_realizes := fun _ _ _ ↦
      FiniteInvariantCover.Refinement.canonical_realizes_smithHom _
    bottom_bounded := by
      intro n hn
      simpa [tower, coverNat, clip, L] using C.bottom_bounded n hn
    ambient_proZero := by
      intro i hi
      change (between i (i + 1) (Nat.le_succ i)).smithHom.KillsReducedHomology
      rw [between_succ]
      exact stepNat_acyclic i hi }
  refine ⟨P, ?_⟩
  rfl

/-- Iterating the preceding refinement and composing its canonical nerve
maps gives a coherent infinite tower, constant after the finite Smith range.
The bottom cover is retained definitionally up to the displayed equality. -/
private theorem arcLike_exists_smithNerveTower_over
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X)
    (harc : IsArcLike X) (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) (bottom : FiniteInvariantCover V p) :
    ∃ P : ArcLikeSmithNerveTower V p, P.cover 0 = bottom := by
  obtain ⟨N, C, hCbottom⟩ :=
    arcLike_exists_finiteSmithNerveCoverChain_over
      hconnected harc V hp hperiodic bottom
  obtain ⟨P, hPbottom⟩ := finiteSmithNerveCoverChain_exists_tower C
  exact ⟨P, hPbottom.trans hCbottom⟩

/-- A fixed point determines a basis vertex of the barycentric full nerve:
take the face of all cover elements containing that point.  The vertex is
fixed basiswise and every index in its face carries the point. -/
private theorem fixedPoint_exists_fixed_carried_nerveVertex
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (C : FiniteCyclicAugmentedComplex p)
    (R : U.NerveRealization C) {x : X} (hx : V x = x) :
    ∃ b : C.Basis 0,
      C.actionBasis 0 b = b ∧
        ∀ i ∈ (R.basisEquiv 0 b).1 0, x ∈ U.set i := by
  classical
  let s : Finset U.Index := Finset.univ.filter fun i ↦ x ∈ U.set i
  have hsne : s.Nonempty := by
    have hxcov := U.covers (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hxcov with ⟨i, hxi⟩
    exact ⟨i, by simp [s, hxi]⟩
  have hsface : U.IsNerveFace s := by
    refine ⟨hsne, ⟨x, ?_⟩⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsaction : s.image U.action = s := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
      have hxi : x ∈ U.set i := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← U.equivariant i]
      exact ⟨x, hxi, hx⟩
    · intro hj
      have hxj : x ∈ U.set j := (Finset.mem_filter.mp hj).2
      let i := U.action.symm j
      have hximage : x ∈ V '' U.set i := by
        rw [U.equivariant i]
        simpa [i] using hxj
      rcases hximage with ⟨y, hyi, hyx⟩
      have hyx' : y = x := by
        apply V.injective
        rw [hyx, hx]
      subst y
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, by simp [i]⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyi⟩
  let q : U.BarycentricBasis 0 :=
    ⟨fun _ ↦ s, ⟨fun _ ↦ hsface, by
      intro i j hij
      fin_cases i
      fin_cases j
      simp at hij⟩⟩
  let b : C.Basis 0 := (R.basisEquiv 0).symm q
  have hbq : R.basisEquiv 0 b = q := (R.basisEquiv 0).apply_symm_apply q
  refine ⟨b, ?_, ?_⟩
  · apply (R.basisEquiv 0).injective
    apply Subtype.ext
    funext j
    rw [R.action_compat, hbq]
    change s.image U.action = s
    exact hsaction
  · intro i hi
    rw [hbq] at hi
    exact (Finset.mem_filter.mp hi).2

/-- If every support vertex of a zero-chain has one colour, its side-linear
value is either zero (left) or the ordinary augmentation (right). -/
private theorem fixedNerveH0Separation_sideLinear_eq_of_support_side
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (C : FiniteCyclicAugmentedComplex p)
    (R : U.NerveRealization C) (S : PeriodicFixedSetSeparation V)
    (hsep : U.FixedNerveH0Separation S) (q : Bool) (c : C.Chain 0)
    (hc : ∀ b ∈ c.support, hsep.side (R.vertexFace b) = q) :
    hsep.sideLinear R c = if q = true then C.augment c else 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add b r c hbnot hr ih =>
      have hbmem : b ∈ (Finsupp.single b r + c).support := by
        apply Finsupp.mem_support_iff.mpr
        have hcb : c b = 0 := by
          by_contra hcb
          exact hbnot (Finsupp.mem_support_iff.mpr hcb)
        simpa [hcb] using hr
      have hbside := hc b hbmem
      have hc' : ∀ a ∈ c.support,
          hsep.side (R.vertexFace a) = q := by
        intro a ha
        apply hc a
        apply Finsupp.mem_support_iff.mpr
        have hane := Finsupp.mem_support_iff.mp ha
        have hab : a ≠ b := by
          intro hab
          subst a
          exact hbnot (Finsupp.mem_support_iff.mpr hane)
        simpa [Finsupp.single_apply, hab] using hane
      rw [map_add, map_add, ih hc']
      cases q <;>
        simp [FiniteInvariantCover.FixedNerveH0Separation.sideLinear,
          hbside, R.augment_single]

/-- A fixed-support one-chain has zero signed/right-side augmentation on its
boundary.  Regularity makes every boundary vertex fixed, and comparable fixed
vertices have the same colour. -/
private theorem fixedNerveH0Separation_sideLinear_boundary_fixed
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (U : FiniteInvariantCover V p) (C : FiniteCyclicAugmentedComplex p)
    (R : U.NerveRealization C) (S : PeriodicFixedSetSeparation V)
    (hsep : U.FixedNerveH0Separation S)
    (w : C.Chain 1) (hw : C.IsFixedChain w) :
    hsep.sideLinear R (C.boundary 0 w) = 0 := by
  classical
  have hfaceFixed (a : C.Basis 0)
      (ha : C.actionBasis 0 a = a) :
      U.faceActionOrderIso (R.vertexFace a) = R.vertexFace a := by
    apply Subtype.ext
    change ((R.basisEquiv 0 a).1 0).image U.action =
      (R.basisEquiv 0 a).1 0
    rw [← R.action_compat, ha]
  have hsingleOne (b : C.Basis 1)
      (hb : C.actionBasis 1 b = b) :
      hsep.sideLinear R (C.boundary 0 (Finsupp.single b 1)) = 0 := by
    by_cases hne :
        (C.boundary 0 (Finsupp.single b 1)).support.Nonempty
    · obtain ⟨a₀, ha₀⟩ := hne
      let q := hsep.side (R.vertexFace a₀)
      have hside : ∀ a ∈ (C.boundary 0 (Finsupp.single b 1)).support,
          hsep.side (R.vertexFace a) = q := by
        intro a ha
        have hafix : C.actionBasis 0 a = a :=
          C.regular_boundary 0 b hb a ha
        have ha₀fix : C.actionBasis 0 a₀ = a₀ :=
          C.regular_boundary 0 b hb a₀ ha₀
        rcases R.boundary_zero_support_comparable b a a₀ ha ha₀ with
          hle | hle
        · exact hsep.side_eq_of_le (hfaceFixed a hafix)
            (hfaceFixed a₀ ha₀fix) hle
        · exact (hsep.side_eq_of_le (hfaceFixed a₀ ha₀fix)
            (hfaceFixed a hafix) hle).symm
      rw [fixedNerveH0Separation_sideLinear_eq_of_support_side
        U C R S hsep q (C.boundary 0 (Finsupp.single b 1)) hside]
      simp [C.augment_boundary]
    · have hempty : (C.boundary 0 (Finsupp.single b 1)).support = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hzero : C.boundary 0 (Finsupp.single b 1) = 0 :=
        Finsupp.support_eq_empty.mp hempty
      rw [hzero, map_zero]
  have hsingle (b : C.Basis 1) (r : ZMod p)
      (hb : C.actionBasis 1 b = b) :
      hsep.sideLinear R (C.boundary 0 (Finsupp.single b r)) = 0 := by
    have hscale : Finsupp.single b r = r • Finsupp.single b (1 : ZMod p) := by
      ext a
      simp [Finsupp.single_apply]
    rw [hscale, map_smul, map_smul, hsingleOne b hb, smul_zero]
  induction w using Finsupp.induction with
  | zero => simp
  | single_add b r c hbnot hr ih =>
      have hbmem : b ∈ (Finsupp.single b r + c).support := by
        apply Finsupp.mem_support_iff.mpr
        have hcb : c b = 0 := by
          by_contra hcb
          exact hbnot (Finsupp.mem_support_iff.mpr hcb)
        simpa [hcb] using hr
      have hbfix := hw b hbmem
      have hcfix : C.IsFixedChain c := by
        intro a ha
        apply hw a
        apply Finsupp.mem_support_iff.mpr
        have hane := Finsupp.mem_support_iff.mp ha
        have hab : a ≠ b := by
          intro hab
          subst a
          exact hbnot (Finsupp.mem_support_iff.mpr hane)
        simpa [Finsupp.single_apply, hab] using hane
      rw [map_add, map_add, hsingle b r hbfix, ih hcfix, add_zero]

/-- A fixed top vertex carried by a fixed point maps only to fixed bottom
vertices of the corresponding colour.  This is where the tower's displayed
refinement and `map_realizes` coherence are used. -/
private theorem towerMap_fixedCarriedVertex_support_side
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (P : ArcLikeSmithNerveTower V p)
    (S : PeriodicFixedSetSeparation V)
    (hsep : (P.cover 0).FixedNerveH0Separation S)
    {x : X}
    {a : (P.tower.level (smithH0TowerLength p P.N)).Basis 0}
    (ha : (P.tower.level (smithH0TowerLength p P.N)).actionBasis 0 a = a)
    (hax : ∀ i ∈ ((P.realization (smithH0TowerLength p P.N)).basisEquiv
      0 a).1 0,
      x ∈ (P.cover (smithH0TowerLength p P.N)).set i)
    (q : Bool)
    (hqx : (q = false ∧ x ∈ S.left) ∨ (q = true ∧ x ∈ S.right)) :
    ∀ c ∈ ((P.tower.map 0 (smithH0TowerLength p P.N) (Nat.zero_le _)).map 0
      (Finsupp.single a 1)).support,
      (P.tower.level 0).actionBasis 0 c = c ∧
        hsep.side ((P.realization 0).vertexFace c) = q := by
  classical
  intro c hc
  let L := smithH0TowerLength p P.N
  let f := P.tower.map 0 L (Nat.zero_le _)
  have hsingle : (P.tower.level L).IsFixedChain
      (Finsupp.single a 1) := by
    intro d hd
    have hda : d = a := by
      by_contra hne
      rw [Finsupp.mem_support_iff] at hd
      exact hd (Finsupp.single_eq_of_ne hne)
    simpa [hda] using ha
  have hcfix : (P.tower.level 0).actionBasis 0 c = c :=
    f.map_fixed 0 (Finsupp.single a 1) hsingle c hc
  have hfacefix : (P.cover 0).faceActionOrderIso
      ((P.realization 0).vertexFace c) =
        (P.realization 0).vertexFace c := by
    apply Subtype.ext
    change (((P.realization 0).basisEquiv 0 c).1 0).image
      (P.cover 0).action = ((P.realization 0).basisEquiv 0 c).1 0
    rw [← (P.realization 0).action_compat, hcfix]
  have hcarrier : x ∈ (P.cover 0).nerveFaceCarrier
      ((P.realization 0).vertexFace c) := by
    simp only [FiniteInvariantCover.nerveFaceCarrier, Set.mem_iInter]
    intro j hj
    have hreal := P.map_realizes 0 L (Nat.zero_le _) 0 a c hc (0 : Fin 1)
    change j ∈ ((P.realization 0).basisEquiv 0 c).1 0 at hj
    rw [hreal] at hj
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    exact (P.refinement 0 L (Nat.zero_le _)).subordinate i (hax i hi)
  refine ⟨hcfix, ?_⟩
  rcases hqx with ⟨hq, hxleft⟩ | ⟨hq, hxright⟩
  · rw [hq]
    exact hsep.left_side _ hfacefix ⟨x, hcarrier, hxleft⟩
  · rw [hq]
    exact hsep.right_side _ hfacefix ⟨x, hcarrier, hxright⟩

/-- Combining the support-side lemma with augmentation preservation computes
the side-linear value of a carried fixed top vertex. -/
private theorem towerMap_fixedCarriedVertex_sideLinear
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (P : ArcLikeSmithNerveTower V p)
    (S : PeriodicFixedSetSeparation V)
    (hsep : (P.cover 0).FixedNerveH0Separation S)
    {x : X}
    {a : (P.tower.level (smithH0TowerLength p P.N)).Basis 0}
    (ha : (P.tower.level (smithH0TowerLength p P.N)).actionBasis 0 a = a)
    (hax : ∀ i ∈ ((P.realization (smithH0TowerLength p P.N)).basisEquiv
      0 a).1 0,
      x ∈ (P.cover (smithH0TowerLength p P.N)).set i)
    (q : Bool)
    (hqx : (q = false ∧ x ∈ S.left) ∨ (q = true ∧ x ∈ S.right)) :
    hsep.sideLinear (P.realization 0)
        ((P.tower.map 0 (smithH0TowerLength p P.N) (Nat.zero_le _)).map 0
          (Finsupp.single a 1)) =
      if q = true then 1 else 0 := by
  let f := P.tower.map 0 (smithH0TowerLength p P.N) (Nat.zero_le _)
  have hsupp : ∀ c ∈ (f.map 0 (Finsupp.single a 1)).support,
      hsep.side ((P.realization 0).vertexFace c) = q := by
    intro c hc
    exact (towerMap_fixedCarriedVertex_support_side
      P S hsep ha hax q hqx c hc).2
  rw [fixedNerveH0Separation_sideLinear_eq_of_support_side
    (P.cover 0) (P.tower.level 0) (P.realization 0) S hsep q
      (f.map 0 (Finsupp.single a 1)) hsupp]
  rw [f.map_augment, (P.realization (smithH0TowerLength p P.N)).augment_single]

/-- The bottom nerve two-colouring prevents a fixed one-chain from bounding
the refined difference of a left-carried and a right-carried fixed vertex. -/
private theorem fixedNerveH0Separation_pointDifference_not_boundary
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (hp : Nat.Prime p)
    (P : ArcLikeSmithNerveTower V p)
    (S : PeriodicFixedSetSeparation V)
    (hsep : (P.cover 0).FixedNerveH0Separation S)
    {x y : X} (hx : x ∈ S.left) (hy : y ∈ S.right)
    {a b : (P.tower.level (smithH0TowerLength p P.N)).Basis 0}
    (ha : (P.tower.level (smithH0TowerLength p P.N)).actionBasis 0 a = a)
    (hb : (P.tower.level (smithH0TowerLength p P.N)).actionBasis 0 b = b)
    (hax : ∀ i ∈ ((P.realization (smithH0TowerLength p P.N)).basisEquiv
      0 a).1 0,
      x ∈ (P.cover (smithH0TowerLength p P.N)).set i)
    (hby : ∀ i ∈ ((P.realization (smithH0TowerLength p P.N)).basisEquiv
      0 b).1 0,
      y ∈ (P.cover (smithH0TowerLength p P.N)).set i) :
    ¬ ∃ w : (P.tower.level 0).Chain 1,
      (P.tower.level 0).IsFixedChain w ∧
      (P.tower.level 0).boundary 0 w =
          (P.tower.map 0 (smithH0TowerLength p P.N) (Nat.zero_le _)).map 0
            (Finsupp.single a 1 - Finsupp.single b 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  rintro ⟨w, hwfixed, hwboundary⟩
  have hboundarySide :=
    fixedNerveH0Separation_sideLinear_boundary_fixed
      (P.cover 0) (P.tower.level 0) (P.realization 0) S hsep w hwfixed
  have hleft := towerMap_fixedCarriedVertex_sideLinear
    P S hsep ha hax false (Or.inl ⟨rfl, hx⟩)
  have hright := towerMap_fixedCarriedVertex_sideLinear
    P S hsep hb hby true (Or.inr ⟨rfl, hy⟩)
  rw [hwboundary, map_sub, map_sub, hleft, hright] at hboundarySide
  have hneg : (-1 : ZMod p) = 0 := by simpa using hboundarySide
  have hval := congrArg ZMod.val (neg_eq_zero.mp hneg)
  rw [ZMod.val_one p, ZMod.val_zero] at hval
  omega

/-- The canonical fixed vertices and their difference cycle assemble the
persistent witness required by the relative Smith lemma. -/
private theorem persistentFixedH0Witness_of_fixedNerveSeparation
    {X : Type*} [TopologicalSpace X] {V : X ≃ₜ X} {p : ℕ}
    (hp : Nat.Prime p)
    (P : ArcLikeSmithNerveTower V p)
    (S : PeriodicFixedSetSeparation V)
    (hsep : (P.cover 0).FixedNerveH0Separation S) :
    Nonempty P.PersistentFixedH0Witness := by
  let L := smithH0TowerLength p P.N
  obtain ⟨x, hx⟩ := S.left_nonempty
  obtain ⟨y, hy⟩ := S.right_nonempty
  have hxfix : V x = x := by
    have : x ∈ {z : X | V z = z} := by
      rw [S.fixed_eq]
      exact Or.inl hx
    exact this
  have hyfix : V y = y := by
    have : y ∈ {z : X | V z = z} := by
      rw [S.fixed_eq]
      exact Or.inr hy
    exact this
  obtain ⟨a, hafix, hax⟩ :=
    fixedPoint_exists_fixed_carried_nerveVertex
      (P.cover L) (P.tower.level L) (P.realization L) hxfix
  obtain ⟨b, hbfix, hby⟩ :=
    fixedPoint_exists_fixed_carried_nerveVertex
      (P.cover L) (P.tower.level L) (P.realization L) hyfix
  let z : (P.tower.level L).Chain 0 :=
    Finsupp.single a 1 - Finsupp.single b 1
  have hsingleFixed (c : (P.tower.level L).Basis 0)
      (hc : (P.tower.level L).actionBasis 0 c = c) :
      (P.tower.level L).IsFixedChain (Finsupp.single c 1) := by
    intro d hd
    have hdc : d = c := by
      by_contra hne
      rw [Finsupp.mem_support_iff] at hd
      exact hd (Finsupp.single_eq_of_ne hne)
    simpa [hdc] using hc
  have hzfixed : (P.tower.level L).IsFixedChain z := by
    exact smith_fixedChain_sub (P.tower.level L)
      (hsingleFixed a hafix) (hsingleFixed b hbfix)
  have hzreduced : (P.tower.level L).augment z = 0 := by
    dsimp [z]
    rw [map_sub, (P.realization L).augment_single,
      (P.realization L).augment_single, sub_self]
  refine ⟨{
    leftPoint := x
    rightPoint := y
    left_fixed := hxfix
    right_fixed := hyfix
    topLeft := a
    topRight := b
    topLeft_fixed := hafix
    topRight_fixed := hbfix
    left_carried := hax
    right_carried := hby
    z := z
    z_eq := rfl
    z_fixed := by simpa [L] using hzfixed
    z_reduced := by simpa [L] using hzreduced
    persistent := by
      simpa [L, z] using
        fixedNerveH0Separation_pointDifference_not_boundary
          hp P S hsep hx hy hafix hbfix hax hby }⟩

/-- Correct bundled topological boundary.  Arc-likeness constructs the
ambient pro-zero refinement tower, while disconnectedness constructs the
fixed witness in that very same realized tower. -/
private theorem arcLike_disconnectedFix_smithNerveTower
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1)
    (hdisc : ¬ IsPreconnected {x : X | V x = x}) :
    ∃ P : ArcLikeSmithNerveTower V p, Nonempty P.PersistentFixedH0Witness := by
  obtain ⟨S⟩ := disconnectedFix_exists_compactSeparation V hdisc
  obtain ⟨U, ⟨hUsep⟩⟩ :=
    periodicFixedSetSeparation_exists_invariantNerveCover
      V hp hperiodic S
  obtain ⟨P, hPbottom⟩ :=
    arcLike_exists_smithNerveTower_over hconnected harc V hp hperiodic U
  have hPsep : (P.cover 0).FixedNerveH0Separation S := by
    rw [hPbottom]
    exact hUsep
  exact ⟨P, persistentFixedH0Witness_of_fixedNerveSeparation hp P S hPsep⟩

/-- Prime-order fixed-continuum theorem after the finite relative Smith
lemma and the invariant full-nerve construction. -/
theorem primePeriodicHomeomorph_fixedSet_preconnected_of_arcLike
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (hconnected : ConnectedSpace X) (harc : IsArcLike X)
    (V : X ≃ₜ X) {p : ℕ} (hp : Nat.Prime p)
    (hperiodic : V ^ p = 1) :
    IsPreconnected {x : X | V x = x} := by
  by_contra hdisc
  obtain ⟨P, ⟨W⟩⟩ :=
    arcLike_disconnectedFix_smithNerveTower
      hconnected harc V hp hperiodic hdisc
  apply W.persistent
  exact relative_smith_H0_tower hp P.tower P.bottom_bounded
    P.ambient_proZero W.z W.z_fixed W.z_reduced

end CommutingInterval
