(**
Conditions to lift a biadjunction to a displayed biadjunction to a dependent product.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
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
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBiadjunction.

Local Open Scope cat.

Section LiftPseudofunctor.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          {I : UU}
          {D₁ : I → disp_bicat B₁}
          {D₂ : I → disp_bicat B₂}
          (FF : ∏ (i : I), disp_psfunctor (D₁ i) (D₂ i) F)
          (D₂_locally_prop : ∏ (i : I), disp_2cells_isaprop (D₂ i))
          (D₂_locally_groupoid : ∏ (i : I), disp_locally_groupoid (D₂ i)).

  Definition disp_depprod_psfunctor
    : disp_psfunctor (disp_depprod_bicat I D₁) (disp_depprod_bicat I D₂) F.
  Proof.
    use make_disp_psfunctor.
    - apply disp_2cells_isaprop_depprod.
      exact D₂_locally_prop.
    - apply disp_locally_groupoid_depprod.
      exact D₂_locally_groupoid.
    - exact (λ x xx i, FF i x (xx i)).
    - exact (λ x y f xx yy ff i, pr121 (FF i) _ _ _ _ _ (ff i)).
    - exact (λ x y f g α xx yy ff gg αα i, pr1 (pr221 (FF i)) _ _ _ _ _ _ _ _ _ (αα i)).
    - refine (λ x xx, _).
      exact (λ i, pr12 (pr221 (FF i)) _ (xx i)).
    - refine (λ x y z f g xx yy zz ff gg, _).
      exact (λ i, pr22 (pr221 (FF i)) _ _ _ _ _ _ _ _ (ff i) (gg i)).
  Defined.
End LiftPseudofunctor.

Section LiftBiadjunction.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L)
          {I : UU}
          {D₁ : I → disp_bicat B₁}
          {D₂ : I → disp_bicat B₂}
          (LL : ∏ (i : I), disp_psfunctor (D₁ i) (D₂ i) L)
          (RR : ∏ (i : I), disp_left_biadj_data
                             _ _
                             R
                             (LL i))
          (D₁_locally_prop : ∏ (i : I), disp_2cells_isaprop (D₁ i))
          (D₁_locally_groupoid : ∏ (i : I), disp_locally_groupoid (D₁ i))
          (D₂_locally_prop : ∏ (i : I), disp_2cells_isaprop (D₂ i))
          (D₂_locally_groupoid : ∏ (i : I), disp_locally_groupoid (D₂ i)).
  
  Definition disp_fullsub_biadjunction
    : disp_left_biadj_data
        _ _
        R
        (disp_depprod_psfunctor L LL D₂_locally_prop D₂_locally_groupoid).
  Proof.
    use tpair.
    - use tpair.
      + exact (disp_depprod_psfunctor
                 R (λ i, pr11 (RR i))
                 D₁_locally_prop D₁_locally_groupoid).
      + split.
        * use make_disp_pstrans.
          ** apply disp_2cells_isaprop_depprod.
             exact D₁_locally_prop.
          ** apply disp_locally_groupoid_depprod.
             exact D₁_locally_groupoid.
          ** exact (λ x xx i, pr121 (RR i) _ (xx i)).
          ** exact (λ x y f xx yy ff i, pr21 (pr121 (RR i)) _ _ _ _ _ (ff i)).
        * use make_disp_pstrans.
          ** apply disp_2cells_isaprop_depprod.
             exact D₂_locally_prop.
          ** apply disp_locally_groupoid_depprod.
             exact D₂_locally_groupoid.
          ** exact (λ x xx i, pr221 (RR i) _ (xx i)).
          ** exact (λ x y f xx yy ff i, pr21 (pr221 (RR i)) _ _ _ _ _ (ff i)).
    - split.
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_depprod.
          exact D₂_locally_prop.
        * apply disp_locally_groupoid_depprod.
          exact D₂_locally_groupoid.
        * exact (λ x xx i, pr1 (pr12 (RR i)) _ (xx i)).
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_depprod.
          exact D₁_locally_prop.
        * apply disp_locally_groupoid_depprod.
          exact D₁_locally_groupoid.
        * exact (λ x xx i, pr1 (pr22 (RR i)) _ (xx i)).
  Defined.
End LiftBiadjunction.
