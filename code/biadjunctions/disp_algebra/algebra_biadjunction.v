(**
Lifting biadjunctions to biadjunctions of algebras
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Unitors.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.CategoryTheory.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.CategoryTheory.Bicategories.Modifications.Modification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBiadjunction.

Require Import biadjunctions.disp_algebra.algebra_pseudofunctor.

Local Open Scope cat.

Local Arguments lassociator {_ _ _ _ _ _ _ _}.
Local Arguments rassociator {_ _ _ _ _ _ _ _}.

Definition algebra_lift_pstrans
           {B₁ B₂ : bicat}
           {H₁ : psfunctor B₁ B₁} {H₂ : psfunctor B₂ B₂}
           {F₁ F₂ : psfunctor B₁ B₂}
           (α : pstrans F₁ F₂)
           (FF₁ : disp_psfunctor (disp_alg_bicat H₁) (disp_alg_bicat H₂) F₁)
           (FF₂ : disp_psfunctor (disp_alg_bicat H₁) (disp_alg_bicat H₂) F₂)
  : UU
  := ∏ (x : B₁)
       (xx : disp_alg_bicat H₁ x),
     FF₁ _ xx -->[ α x ] FF₂ _ xx.

Definition algebra_lift_pstrans_nat
           {B₁ B₂ : bicat}
           {H₁ : psfunctor B₁ B₁} {H₂ : psfunctor B₂ B₂}
           {F₁ F₂ : psfunctor B₁ B₂}
           {α : pstrans F₁ F₂}
           {FF₁ : disp_psfunctor (disp_alg_bicat H₁) (disp_alg_bicat H₂) F₁}
           {FF₂ : disp_psfunctor (disp_alg_bicat H₁) (disp_alg_bicat H₂) F₂}
           (αα : algebra_lift_pstrans α FF₁ FF₂)
  : UU
  := ∏ (x y : B₁)
       (f : B₁ ⟦ x, y ⟧)
       (xx : (disp_alg_bicat H₁) x)
       (yy : (disp_alg_bicat H₁) y)
       (ff : xx -->[ f] yy),
     (αα x xx;; disp_psfunctor_mor _ _ _ FF₂ ff)
       ==>[ psnaturality_of α f ]
       (disp_psfunctor_mor _ _ _ FF₁ ff;; αα y yy).

Section LiftPseudotransformation.
  Context {B₁ B₂ : bicat}
          {H₁ : psfunctor B₁ B₁} {H₂ : psfunctor B₂ B₂}
          {F₁ F₂ : psfunctor B₁ B₂}
          (α : pstrans F₁ F₂)
          {FF₁ : disp_psfunctor (disp_alg_bicat H₁) (disp_alg_bicat H₂) F₁}
          {FF₂ : disp_psfunctor (disp_alg_bicat H₁) (disp_alg_bicat H₂) F₂}.

  Variable (αα : algebra_lift_pstrans α FF₁ FF₂)
           (ααnat : algebra_lift_pstrans_nat αα).

  Definition disp_alg_pstrans
    : disp_pstrans FF₁ FF₂ α.
  Proof.
    use make_disp_pstrans.
    - apply disp_2cells_isaprop_alg.
    - apply disp_locally_groupoid_alg.
    - exact αα.
    - exact ααnat.
  Defined.
End LiftPseudotransformation.

Section LiftBiadjunction.
  Context {B₁ B₂ : bicat}
          {H₁ : psfunctor B₁ B₁} {H₂ : psfunctor B₂ B₂}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L)
          (γ₁ : pstrans (ps_comp H₂ L) (ps_comp L H₁))
          (γ₂ : pstrans (ps_comp H₁ (pr11 R)) (ps_comp (pr11 R) H₂)).

  Local Notation "'LL'" := (disp_alg_psfunctor L γ₁).
  Local Notation "'RR'" := (disp_alg_psfunctor R γ₂).

  Definition lift_unit_type
    : UU.
  Proof.
    refine (∏ (x : B₁), invertible_2cell
                          _
                          (# H₁ _ · (γ₂ (L x) · #R(γ₁ x)))).
    - exact (biadj_unit R (H₁ x)).
    - exact (biadj_unit R x).
  Defined.

  Variable (ηH : lift_unit_type).
      
  Definition unit_of_lifted_biadj
    : algebra_lift_pstrans
        (biadj_unit R)
        (disp_pseudo_id (disp_alg_bicat H₁))
        (disp_pseudo_comp
           _ _ _ _ _
           LL (disp_alg_psfunctor R γ₂)).
  Proof.
    intros x xx ; cbn.
    use tpair.
    - refine ((psnaturality_of (biadj_unit R) xx)^-1 • _).
      refine (ηH x ▹ _ • _).
      refine (rassociator • (_ ◃ _)).
      refine (rassociator • (_ ◃ _)).
      exact (psfunctor_comp R (γ₁ x) (#L xx)).
    - simpl.
      is_iso.
      + apply ηH.
      + apply psfunctor_comp.
  Defined.

  Variable (ηHnat : algebra_lift_pstrans_nat unit_of_lifted_biadj).

  Definition lift_counit_type
    : UU.
  Proof.
    refine (∏ (x : B₂), invertible_2cell
                          (γ₁ (R x) · #L(γ₂ x) · _)
                          (# H₂ _)).
    - exact (biadj_counit R (H₂ x)).
    - exact (biadj_counit R x).
  Defined.

  Variable (εH : lift_counit_type).

  Definition counit_of_lifted_biadj
    : algebra_lift_pstrans
        (biadj_counit R)
        (disp_pseudo_comp
           _ _ _ _ _
           (disp_alg_psfunctor R γ₂) LL)
        (disp_pseudo_id (disp_alg_bicat H₂)).
  Proof.
    intros x xx ; cbn.
    use tpair.
    - refine (_ • (εH x ▹ xx)).
      refine (rassociator • _ • lassociator • lassociator).
      refine (_ ◃ _).
      refine (_ • (_ ◃ (psnaturality_of (biadj_counit R) xx)^-1)).
      refine (_ • rassociator).
      refine (_ ▹ _).
      exact ((psfunctor_comp L (γ₂ x) (#R xx))^-1).
    - simpl.
      is_iso.
      apply εH.
  Defined.

  Variable (εHnat : algebra_lift_pstrans_nat counit_of_lifted_biadj).

  Definition lifted_alg_unit
    : disp_pstrans
        (disp_pseudo_id (disp_alg_bicat H₁))
        (disp_pseudo_comp
           _ _ _ _ _
           LL (disp_alg_psfunctor R γ₂)) (biadj_unit R).
  Proof.
    simple refine (disp_alg_pstrans (biadj_unit R) _ _).
    - exact unit_of_lifted_biadj.
    - exact ηHnat.
  Defined.

  Definition lifted_alg_counit
    : disp_pstrans
        (disp_pseudo_comp
           _ _ _ _ _
           (disp_alg_psfunctor R γ₂) LL) (disp_pseudo_id (disp_alg_bicat H₂)) 
        (biadj_counit R).
  Proof.
    simple refine (disp_alg_pstrans (biadj_counit R) _ _).
    - exact counit_of_lifted_biadj.
    - exact εHnat.
  Defined.
  
  Definition lift_triangle_l
    : UU
    := ∏ (x : B₁) (xx : disp_alg_bicat H₁ x),
       _ ◃ (invertible_modcomponent_of (pr12 R) x)
         • pr1 (@id_disp _ (disp_alg_bicat H₂) _ _)
       =
       (pr1 (id_disp _
            ;; ((disp_alg_psfunctor_mor L γ₁ (unit_of_lifted_biadj x xx))
            ;; (id_disp _
            ;; (counit_of_lifted_biadj (L x) (γ₁ x · (# L)%Cat xx)
            ;; id_disp _))))%mor_disp)
       • (##H₂ (pr1 (invertible_modcomponent_of (pr12 R) x)) ▹ _).

  Definition lift_triangle_r
    : UU
    := ∏ (x : B₂) (xx : disp_alg_bicat H₂ x),
       _ ◃ (invertible_modcomponent_of (pr22 R) x)
       • pr1 (@id_disp _ (disp_alg_bicat H₁) _ _)
       =
       pr1 (id_disp _
           ;; ((unit_of_lifted_biadj (R x) (γ₂ x · (# R)%Cat xx)
           ;; (id_disp _
           ;; (disp_alg_psfunctor_mor R γ₂ (counit_of_lifted_biadj x xx)
           ;; id_disp _)))))%mor_disp
       • (##H₁ (invertible_modcomponent_of (pr22 R) x) ▹ _).

  Variable (ml : lift_triangle_l)
           (mr : lift_triangle_r).
  
  Definition lift_algebra_biadjunction
    : disp_left_biadj_data _ _ R LL.
  Proof.
    use tpair.
    - use tpair.
      + exact RR.
      + split.
        * exact lifted_alg_unit.
        * exact lifted_alg_counit.
    - split.
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_alg.
        * apply disp_locally_groupoid_alg.
        * exact ml.
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_alg.
        * apply disp_locally_groupoid_alg.
        * exact mr.
  Defined.
End LiftBiadjunction.
