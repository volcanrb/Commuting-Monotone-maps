import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Supported

open CategoryTheory CategoryTheory.Limits Simplicial

namespace CommutingIntervalSimplified.PosetNerve

/-!
Normalized chains on the category nerve of a finite poset, presented in the
concrete basis of strict chains.  The categorical normalized complex supplies
`d² = 0`; the explicit alternating-face formula supplies augmentation,
equivariance, and regularity for order-automorphism actions.
-/

universe u

variable (P : Type u) [PartialOrder P]

noncomputable def strictChains (n : ℕ) :=
  {q : Fin (n + 1) → P // StrictMono q}

noncomputable def strictChainsEquivNonDegenerate (n : ℕ) :
    strictChains P n ≃ (CategoryTheory.nerve P).nonDegenerate n where
  toFun q := by
    let F := q.2.monotone.functor
    refine ⟨(show ComposableArrows P n from F), ?_⟩
    rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
    exact q.2
  invFun s :=
    ⟨fun j ↦ s.1.obj j,
      (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.1).mp s.2⟩
  left_inv q := by
    apply Subtype.ext
    funext j
    rfl
  right_inv s := by
    apply Subtype.ext
    apply ComposableArrows.ext (fun j ↦ rfl)
    intro j hj
    subsingleton

def strictChainFace {n : ℕ} (q : strictChains P (n + 1))
    (i : Fin (n + 2)) : strictChains P n :=
  ⟨fun j ↦ q.1 (i.succAbove j),
    q.2.comp (Fin.strictMono_succAbove i)⟩

theorem strictChainsEquivNonDegenerate_face {n : ℕ}
    (q : strictChains P (n + 1)) (i : Fin (n + 2)) :
    strictChainsEquivNonDegenerate P n (strictChainFace P q i) =
      ⟨(CategoryTheory.nerve P).δ i
          (strictChainsEquivNonDegenerate P (n + 1) q).1,
        (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).2
          (q.2.comp (Fin.strictMono_succAbove i))⟩ := by
  apply Subtype.ext
  apply ComposableArrows.ext (fun j ↦ rfl)
  intro j hj
  subsingleton

theorem strictChainsEquivNonDegenerate_face_val {n : ℕ}
    (q : strictChains P (n + 1)) (i : Fin (n + 2)) :
    (CategoryTheory.nerve P).δ i
        (strictChainsEquivNonDegenerate P (n + 1) q).1 =
      (strictChainsEquivNonDegenerate P n (strictChainFace P q i)).1 := by
  exact congrArg Subtype.val
    (strictChainsEquivNonDegenerate_face P q i).symm

end CommutingIntervalSimplified.PosetNerve

namespace CommutingIntervalSimplified.PosetNerve

open ModuleCat

universe v

variable {X : SSet} (R : Type v) [Ring R]

noncomputable def normalizedBasisIso (n : ℕ) :
    ModuleCat.of R (DirectSum (X.nonDegenerate n) (fun _ ↦ R)) ≅
      (X.normalizedChainComplex (ModuleCat.of R R)).X n := by
  classical
  let c₁ : Cofan (fun _ : X.nonDegenerate n ↦ ModuleCat.of R R) :=
    ModuleCat.coproductCocone (fun _ : X.nonDegenerate n ↦ ModuleCat.of R R)
  let c₂ : Cofan (fun _ : X.nonDegenerate n ↦ ModuleCat.of R R) :=
    X.cofanNormalizedChainComplex (ModuleCat.of R R) n
  let P : IsColimit c₁ :=
    ModuleCat.coproductCoconeIsColimit
      (fun _ : X.nonDegenerate n ↦ ModuleCat.of R R)
  let Q : IsColimit c₂ :=
    X.isColimitCofanNormalizedChainComplex (ModuleCat.of R R) n
  let e : c₁.pt ≅ c₂.pt :=
    IsColimit.coconePointUniqueUpToIso P Q
  simpa [c₁, c₂] using e

noncomputable def normalizedBasisLinearEquiv (n : ℕ) :
    (X.nonDegenerate n →₀ R) ≃ₗ[R]
      (X.normalizedChainComplex (ModuleCat.of R R)).X n := by
  classical
  exact (finsuppLEquivDirectSum R R (X.nonDegenerate n)).trans
    (normalizedBasisIso (X := X) R n).toLinearEquiv

theorem normalizedBasisLinearEquiv_single (n : ℕ)
    (b : X.nonDegenerate n) (r : R) :
    normalizedBasisLinearEquiv (X := X) R n (Finsupp.single b r) =
      (X.ιNormalizedChainComplex (R := ModuleCat.of R R) b.1).hom r := by
  classical
  simp only [normalizedBasisLinearEquiv, LinearEquiv.trans_apply,
    finsuppLEquivDirectSum_single, CategoryTheory.Iso.toLinearEquiv_apply]
  change (normalizedBasisIso (X := X) R n).hom.hom
      (DirectSum.lof R (X.nonDegenerate n) (fun _ ↦ R) b r) = _
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (ModuleCat.coproductCoconeIsColimit
      (fun _ : X.nonDegenerate n ↦ ModuleCat.of R R))
    (X.isColimitCofanNormalizedChainComplex (ModuleCat.of R R) n)
    ⟨b⟩
  simpa [normalizedBasisIso] using
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) r

end CommutingIntervalSimplified.PosetNerve

namespace CommutingIntervalSimplified.PosetNerve

universe u

variable (P : Type u) [PartialOrder P]
variable (R : Type u) [CommRing R]

noncomputable def strictBasisLinearEquiv (n : ℕ) :
    (strictChains P n →₀ R) ≃ₗ[R]
      ((CategoryTheory.nerve P).normalizedChainComplex
        (ModuleCat.of R R)).X n := by
  classical
  exact (Finsupp.domLCongr (strictChainsEquivNonDegenerate P n)).trans
    (normalizedBasisLinearEquiv (X := CategoryTheory.nerve P) R n)

theorem strictBasisLinearEquiv_single (n : ℕ)
    (q : strictChains P n) (r : R) :
    strictBasisLinearEquiv P R n (Finsupp.single q r) =
      ((CategoryTheory.nerve P).ιNormalizedChainComplex
        (R := ModuleCat.of R R)
        (strictChainsEquivNonDegenerate P n q).1).hom r := by
  classical
  rw [strictBasisLinearEquiv]
  simp only [LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  exact normalizedBasisLinearEquiv_single R n
    (strictChainsEquivNonDegenerate P n q) r

noncomputable def strictBoundary (n : ℕ) :
    (strictChains P (n + 1) →₀ R) →ₗ[R] (strictChains P n →₀ R) :=
  (strictBasisLinearEquiv P R n).symm.toLinearMap.comp
    (((((CategoryTheory.nerve P).normalizedChainComplex
      (ModuleCat.of R R)).d (n + 1) n).hom).comp
        (strictBasisLinearEquiv P R (n + 1)).toLinearMap)

theorem strictBasisLinearEquiv_boundary (n : ℕ)
    (c : strictChains P (n + 1) →₀ R) :
    strictBasisLinearEquiv P R n (strictBoundary P R n c) =
      (((CategoryTheory.nerve P).normalizedChainComplex
        (ModuleCat.of R R)).d (n + 1) n).hom
        (strictBasisLinearEquiv P R (n + 1) c) := by
  simp [strictBoundary]

theorem strictBoundary_boundary (n : ℕ)
    (c : strictChains P (n + 2) →₀ R) :
    strictBoundary P R n (strictBoundary P R (n + 1) c) = 0 := by
  apply (strictBasisLinearEquiv P R n).injective
  rw [strictBasisLinearEquiv_boundary, strictBasisLinearEquiv_boundary]
  change ((((CategoryTheory.nerve P).normalizedChainComplex
    (ModuleCat.of R R)).d (n + 2) (n + 1)) ≫
      ((CategoryTheory.nerve P).normalizedChainComplex
        (ModuleCat.of R R)).d (n + 1) n).hom
        (strictBasisLinearEquiv P R (n + 2) c) = _
  rw [HomologicalComplex.d_comp_d]
  rfl

theorem strictBoundary_single (n : ℕ)
    (q : strictChains P (n + 1)) (r : R) :
    strictBoundary P R n (Finsupp.single q r) =
      ∑ i : Fin (n + 2),
        Finsupp.single (strictChainFace P q i)
          (((-1 : ℤ) ^ (i : ℕ)) • r) := by
  classical
  apply (strictBasisLinearEquiv P R n).injective
  rw [strictBasisLinearEquiv_boundary, strictBasisLinearEquiv_single]
  rw [map_sum]
  simp_rw [strictBasisLinearEquiv_single]
  have h := (CategoryTheory.nerve P).ιNormalizedChainComplex_d
    (R := ModuleCat.of R R)
    (strictChainsEquivNonDegenerate P (n + 1) q).1
  have hr := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) r
  refine hr.trans ?_
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_zsmul, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [strictChainsEquivNonDegenerate_face_val]
  exact ((((CategoryTheory.nerve P).ιNormalizedChainComplex
    (R := ModuleCat.of R R)
    (strictChainsEquivNonDegenerate P n
      (strictChainFace P q i)).1).hom).toAddMonoidHom.map_zsmul
      ((-1 : ℤ) ^ (i : ℕ)) r).symm

noncomputable def strictAugment :
    (strictChains P 0 →₀ R) →ₗ[R] R :=
  Finsupp.lsum R (fun _ ↦ LinearMap.id)

@[simp]
theorem strictAugment_single (q : strictChains P 0) (r : R) :
    strictAugment P R (Finsupp.single q r) = r := by
  classical
  simp [strictAugment]

theorem strictAugment_boundary (c : strictChains P 1 →₀ R) :
    strictAugment P R (strictBoundary P R 0 c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      rw [map_add, map_add, ih, add_zero, strictBoundary_single]
      simp [Fin.sum_univ_two]

def strictChainEquiv (e : P ≃o P) (n : ℕ) :
    strictChains P n ≃ strictChains P n where
  toFun q := ⟨fun j ↦ e (q.1 j), e.strictMono.comp q.2⟩
  invFun q := ⟨fun j ↦ e.symm (q.1 j), e.symm.strictMono.comp q.2⟩
  left_inv q := by
    apply Subtype.ext
    funext j
    simp
  right_inv q := by
    apply Subtype.ext
    funext j
    simp

@[simp]
theorem strictChainEquiv_apply (e : P ≃o P) (n : ℕ)
    (q : strictChains P n) (j : Fin (n + 1)) :
    (strictChainEquiv P e n q).1 j = e (q.1 j) := rfl

theorem strictChainEquiv_face (e : P ≃o P) {n : ℕ}
    (q : strictChains P (n + 1)) (i : Fin (n + 2)) :
    strictChainEquiv P e n (strictChainFace P q i) =
      strictChainFace P (strictChainEquiv P e (n + 1) q) i := by
  apply Subtype.ext
  rfl

noncomputable def strictAction (e : P ≃o P) (n : ℕ) :
    (strictChains P n →₀ R) ≃ₗ[R] (strictChains P n →₀ R) := by
  classical
  exact Finsupp.domLCongr (strictChainEquiv P e n)

@[simp]
theorem strictAction_single (e : P ≃o P) (n : ℕ)
    (q : strictChains P n) (r : R) :
    strictAction P R e n (Finsupp.single q r) =
      Finsupp.single (strictChainEquiv P e n q) r := by
  classical
  simp [strictAction]

theorem strictBoundary_action (e : P ≃o P) (n : ℕ)
    (c : strictChains P (n + 1) →₀ R) :
    strictBoundary P R n (strictAction P R e (n + 1) c) =
      strictAction P R e n (strictBoundary P R n c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      rw [map_add, map_add, map_add, map_add, ih]
      congr 1
      rw [strictAction_single, strictBoundary_single, strictBoundary_single,
        map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [strictAction_single, strictChainEquiv_face]

theorem strictAugment_action (e : P ≃o P)
    (c : strictChains P 0 →₀ R) :
    strictAugment P R (strictAction P R e 0 c) = strictAugment P R c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      rw [map_add, map_add, map_add, ih, strictAction_single]
      simp

theorem strictRegularBoundary (e : P ≃o P) (n : ℕ)
    (q : strictChains P (n + 1))
    (hq : strictChainEquiv P e (n + 1) q = q)
    (a : strictChains P n)
    (ha : a ∈ (strictBoundary P R n (Finsupp.single q 1)).support) :
    strictChainEquiv P e n a = a := by
  classical
  rw [strictBoundary_single] at ha
  have ha' := Finsupp.support_finsetSum ha
  rw [Finset.mem_biUnion] at ha'
  obtain ⟨i, hi, hai⟩ := ha'
  have hai_eq : a = strictChainFace P q i := by
    by_contra hne
    simp [Finsupp.mem_support_iff, Finsupp.single_apply, hne] at hai
  subst a
  rw [strictChainEquiv_face, hq]

theorem strictChains_bounded [Fintype P] :
    ∃ N : ℕ, ∀ n : ℕ, N < n → IsEmpty (strictChains P n) := by
  refine ⟨Fintype.card P, ?_⟩
  intro n hn
  refine ⟨fun q ↦ ?_⟩
  have hcard : n + 1 ≤ Fintype.card P := by
    simpa using Fintype.card_le_of_injective q.1 q.2.injective
  omega

theorem strictChainEquiv_pow_apply (e : P ≃o P) (n k : ℕ)
    (q : strictChains P n) (j : Fin (n + 1)) :
    (((strictChainEquiv P e n) ^ k) q).1 j =
      ((e.toEquiv : Equiv.Perm P) ^ k) (q.1 j) := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      change (((strictChainEquiv P e n) ^ k)
          (strictChainEquiv P e n q)).1 j =
        ((e.toEquiv : Equiv.Perm P) ^ k) (e (q.1 j))
      exact ih (strictChainEquiv P e n q)

theorem strictChainEquiv_periodic (e : P ≃o P) (n p : ℕ)
    (he : (e.toEquiv : Equiv.Perm P) ^ p = 1) :
    (strictChainEquiv P e n) ^ p = 1 := by
  apply Equiv.ext
  intro q
  apply Subtype.ext
  funext j
  rw [strictChainEquiv_pow_apply, he]
  rfl

theorem strictAction_pow_single (e : P ≃o P) (n k : ℕ)
    (q : strictChains P n) (r : R) :
    ((strictAction P R e n).toLinearMap ^ k) (Finsupp.single q r) =
      Finsupp.single (((strictChainEquiv P e n) ^ k) q) r := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply]
      change ((strictAction P R e n).toLinearMap ^ k)
        (strictAction P R e n (Finsupp.single q r)) = _
      rw [strictAction_single, ih]
      rfl

theorem strictAction_pow_periodic (e : P ≃o P) (n p : ℕ)
    (he : (e.toEquiv : Equiv.Perm P) ^ p = 1) :
    (strictAction P R e n).toLinearMap ^ p = 1 := by
  apply Finsupp.lhom_ext
  intro q r
  rw [strictAction_pow_single, strictChainEquiv_periodic P e n p he]
  simp

theorem strictAction_iterate_eq_pow (e : P ≃o P) (n k : ℕ)
    (c : strictChains P n →₀ R) :
    ((strictAction P R e n : _ → _)^[k]) c =
      ((strictAction P R e n).toLinearMap ^ k) c := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, pow_succ, Module.End.mul_apply]
      exact ih (strictAction P R e n c)

theorem strictAction_periodic (e : P ≃o P) (n p : ℕ)
    (he : (e.toEquiv : Equiv.Perm P) ^ p = 1) :
    (strictAction P R e n : (strictChains P n →₀ R) → _)^[p] = id := by
  funext c
  rw [strictAction_iterate_eq_pow,
    strictAction_pow_periodic P R e n p he]
  rfl

end CommutingIntervalSimplified.PosetNerve

namespace CommutingIntervalSimplified.PosetNerve

universe u

variable (P Q : Type u) [PartialOrder P] [PartialOrder Q]
variable (R : Type u) [CommRing R]

noncomputable def nerveOrderHom (f : P →o Q) :
    CategoryTheory.nerve P ⟶ CategoryTheory.nerve Q :=
  CategoryTheory.nerveMap f.monotone.functor

def strictChainImage {n : ℕ} (f : P →o Q) (q : strictChains P n)
    (h : StrictMono (fun j ↦ f (q.1 j))) : strictChains Q n :=
  ⟨fun j ↦ f (q.1 j), h⟩

theorem nerveOrderHom_obj {n : ℕ} (f : P →o Q)
    (q : (CategoryTheory.nerve P) _⦋n⦌) (j : Fin (n + 1)) :
    ((ConcreteCategory.hom ((nerveOrderHom P Q f).app
      (Opposite.op ⦋n⦌))) q).obj j = f (q.obj j) := rfl

theorem nerveOrderHom_strictChainsEquiv {n : ℕ} (f : P →o Q)
    (q : strictChains P n) (h : StrictMono (fun j ↦ f (q.1 j))) :
    (ConcreteCategory.hom ((nerveOrderHom P Q f).app
        (Opposite.op ⦋n⦌)))
        (strictChainsEquivNonDegenerate P n q).1 =
      (strictChainsEquivNonDegenerate Q n (strictChainImage P Q f q h)).1 := by
  apply ComposableArrows.ext (fun j ↦ rfl)
  intro j hj
  subsingleton

noncomputable def strictChainMap (f : P →o Q) (n : ℕ) :
    (strictChains P n →₀ R) →ₗ[R] (strictChains Q n →₀ R) :=
  (strictBasisLinearEquiv Q R n).symm.toLinearMap.comp
    (((SSet.normalizedChainComplexMap (nerveOrderHom P Q f)
      (ModuleCat.of R R)).f n).hom.comp
        (strictBasisLinearEquiv P R n).toLinearMap)

theorem strictBasisLinearEquiv_chainMap (f : P →o Q) (n : ℕ)
    (c : strictChains P n →₀ R) :
    strictBasisLinearEquiv Q R n (strictChainMap P Q R f n c) =
      ((SSet.normalizedChainComplexMap (nerveOrderHom P Q f)
        (ModuleCat.of R R)).f n).hom
        (strictBasisLinearEquiv P R n c) := by
  simp [strictChainMap]

theorem strictChainMap_single_of_strict (f : P →o Q) (n : ℕ)
    (q : strictChains P n) (r : R)
    (h : StrictMono (fun j ↦ f (q.1 j))) :
    strictChainMap P Q R f n (Finsupp.single q r) =
      Finsupp.single (strictChainImage P Q f q h) r := by
  classical
  apply (strictBasisLinearEquiv Q R n).injective
  rw [strictBasisLinearEquiv_chainMap, strictBasisLinearEquiv_single,
    strictBasisLinearEquiv_single]
  have hm := SSet.ι_normalizedChainComplexMap_f
    (nerveOrderHom P Q f) (ModuleCat.of R R)
    (strictChainsEquivNonDegenerate P n q).1
  have hmr := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hm) r
  change ((SSet.normalizedChainComplexMap (nerveOrderHom P Q f)
      (ModuleCat.of R R)).f n).hom
      (((CategoryTheory.nerve P).ιNormalizedChainComplex
        (R := ModuleCat.of R R)
        (strictChainsEquivNonDegenerate P n q).1).hom r) = _
  rw [← nerveOrderHom_strictChainsEquiv P Q f q h]
  exact hmr

theorem strictChainMap_single_of_not_strict (f : P →o Q) (n : ℕ)
    (q : strictChains P n) (r : R)
    (h : ¬ StrictMono (fun j ↦ f (q.1 j))) :
    strictChainMap P Q R f n (Finsupp.single q r) = 0 := by
  classical
  apply (strictBasisLinearEquiv Q R n).injective
  rw [strictBasisLinearEquiv_chainMap, strictBasisLinearEquiv_single, map_zero]
  let x : (CategoryTheory.nerve Q) _⦋n⦌ :=
    (ConcreteCategory.hom ((nerveOrderHom P Q f).app
      (Opposite.op ⦋n⦌)))
      (strictChainsEquivNonDegenerate P n q).1
  have hxnot : x ∉ (CategoryTheory.nerve Q).nonDegenerate n := by
    rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
    exact h
  have hxdeg : x ∈ (CategoryTheory.nerve Q).degenerate n :=
    ((CategoryTheory.nerve Q).mem_degenerate_iff_notMem_nonDegenerate x).2 hxnot
  have hxzero := (CategoryTheory.nerve Q).ιNormalizedChainComplex_eq_zero
    (R := ModuleCat.of R R) x hxdeg
  have hm := SSet.ι_normalizedChainComplexMap_f
    (nerveOrderHom P Q f) (ModuleCat.of R R)
    (strictChainsEquivNonDegenerate P n q).1
  have hmr := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hm) r
  change ((SSet.normalizedChainComplexMap (nerveOrderHom P Q f)
      (ModuleCat.of R R)).f n).hom
      (((CategoryTheory.nerve P).ιNormalizedChainComplex
        (R := ModuleCat.of R R)
        (strictChainsEquivNonDegenerate P n q).1).hom r) = 0
  calc
    _ = ((CategoryTheory.nerve Q).ιNormalizedChainComplex
        (R := ModuleCat.of R R) x).hom r := hmr
    _ = 0 := by rw [hxzero]; rfl

theorem strictChainMap_boundary (f : P →o Q) (n : ℕ)
    (c : strictChains P (n + 1) →₀ R) :
    strictChainMap P Q R f n (strictBoundary P R n c) =
      strictBoundary Q R n (strictChainMap P Q R f (n + 1) c) := by
  apply (strictBasisLinearEquiv Q R n).injective
  rw [strictBasisLinearEquiv_chainMap, strictBasisLinearEquiv_boundary,
    strictBasisLinearEquiv_boundary, strictBasisLinearEquiv_chainMap]
  let F := SSet.normalizedChainComplexMap (nerveOrderHom P Q f)
    (ModuleCat.of R R)
  change ((((CategoryTheory.nerve P).normalizedChainComplex
      (ModuleCat.of R R)).d (n + 1) n ≫ F.f n).hom)
        (strictBasisLinearEquiv P R (n + 1) c) =
    ((F.f (n + 1) ≫ ((CategoryTheory.nerve Q).normalizedChainComplex
      (ModuleCat.of R R)).d (n + 1) n).hom)
        (strictBasisLinearEquiv P R (n + 1) c)
  rw [F.comm]

theorem strictChainMap_augment (f : P →o Q)
    (c : strictChains P 0 →₀ R) :
    strictAugment Q R (strictChainMap P Q R f 0 c) =
      strictAugment P R c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      have hs : StrictMono (fun j : Fin 1 ↦ f (q.1 j)) := by
        intro i j hij
        omega
      rw [map_add, map_add, map_add, ih,
        strictChainMap_single_of_strict P Q R f 0 q r hs]
      simp

theorem strictChainMap_single_support (f : P →o Q) (n : ℕ)
    (q : strictChains P n) (r : R) (a : strictChains Q n)
    (ha : a ∈ (strictChainMap P Q R f n (Finsupp.single q r)).support) :
    ∀ j : Fin (n + 1), a.1 j = f (q.1 j) := by
  classical
  by_cases hs : StrictMono (fun j ↦ f (q.1 j))
  · rw [strictChainMap_single_of_strict P Q R f n q r hs] at ha
    have haeq : a = strictChainImage P Q f q hs := by
      by_contra hne
      simp [Finsupp.mem_support_iff, hne] at ha
    subst a
    intro j
    rfl
  · rw [strictChainMap_single_of_not_strict P Q R f n q r hs] at ha
    simp at ha

theorem strictChainMap_action (f : P →o Q) (eP : P ≃o P) (eQ : Q ≃o Q)
    (hcomm : ∀ x, f (eP x) = eQ (f x)) (n : ℕ)
    (c : strictChains P n →₀ R) :
    strictChainMap P Q R f n (strictAction P R eP n c) =
      strictAction Q R eQ n (strictChainMap P Q R f n c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      rw [map_add, map_add, map_add, map_add, ih]
      congr 1
      rw [strictAction_single]
      by_cases hs : StrictMono (fun j ↦ f (q.1 j))
      · have hse : StrictMono
            (fun j ↦ f ((strictChainEquiv P eP n q).1 j)) := by
          intro i j hij
          change f (eP (q.1 i)) < f (eP (q.1 j))
          rw [hcomm, hcomm]
          exact eQ.strictMono (hs hij)
        rw [strictChainMap_single_of_strict P Q R f n _ r hse,
          strictChainMap_single_of_strict P Q R f n q r hs,
          strictAction_single]
        congr 1
        apply Subtype.ext
        funext j
        exact hcomm (q.1 j)
      · have hse : ¬ StrictMono
            (fun j ↦ f ((strictChainEquiv P eP n q).1 j)) := by
          intro hse
          apply hs
          intro i j hij
          have hlt := eQ.symm.strictMono (hse hij)
          simpa [hcomm] using hlt
        rw [strictChainMap_single_of_not_strict P Q R f n _ r hse,
          strictChainMap_single_of_not_strict P Q R f n q r hs]
        simp

theorem strictChainMap_fixedSupport (f : P →o Q)
    (eP : P ≃o P) (eQ : Q ≃o Q)
    (hcomm : ∀ x, f (eP x) = eQ (f x)) (n : ℕ)
    (c : strictChains P n →₀ R)
    (hc : ∀ q ∈ c.support, strictChainEquiv P eP n q = q) :
    ∀ a ∈ (strictChainMap P Q R f n c).support,
      strictChainEquiv Q eQ n a = a := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add q r c hq hr ih =>
      have hcq : c q = 0 := by
        simpa [Finsupp.mem_support_iff] using hq
      have hqmem : q ∈ (Finsupp.single q r + c).support := by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_eq_same, hcq, add_zero]
        exact hr
      have hqfixed : strictChainEquiv P eP n q = q := hc q hqmem
      have hcfixed : ∀ b ∈ c.support,
          strictChainEquiv P eP n b = b := by
        intro b hb
        apply hc b
        rw [Finsupp.mem_support_iff] at hb ⊢
        by_cases hbq : b = q
        · subst b
          exact (hb hcq).elim
        · simpa [Finsupp.single_apply, hbq] using hb
      intro a ha
      rw [map_add] at ha
      have ha' := Finsupp.support_add ha
      rw [Finset.mem_union] at ha'
      rcases ha' with hasingle | hac
      · have haimage := strictChainMap_single_support P Q R f n q r a hasingle
        apply Subtype.ext
        funext j
        change eQ (a.1 j) = a.1 j
        have hqpoint := congrArg (fun z : strictChains P n ↦ z.1 j) hqfixed
        change eP (q.1 j) = q.1 j at hqpoint
        rw [haimage j, ← hcomm, hqpoint]
      · exact ih hcfixed a hac

end CommutingIntervalSimplified.PosetNerve
