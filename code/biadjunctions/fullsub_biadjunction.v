(**
Conditions to obtain a displayed biadjunction between full subbicategories.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.

Local Open Scope cat.

Section LiftPseudofunctor.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          (P₁ : B₁ → UU) (P₂ : B₂ → UU)
          (HP : ∏ (x : B₁), P₁ x → P₂ (F x)).

  Definition disp_fullsub_psfunctor
    : disp_psfunctor (disp_fullsubbicat _ P₁) (disp_fullsubbicat _ P₂) F.
  Proof.
    use make_disp_psfunctor.
    - apply disp_2cells_isaprop_fullsubbicat.
    - apply disp_locally_groupoid_fullsubbicat.
    - exact HP.
    - exact (λ _ _ _ _ _ _, tt).
    - exact (λ _ _ _ _ _ _ _ _ _ _, tt).
    - exact (λ _ _, tt).
    - exact (λ _ _ _ _ _ _ _ _ _ _, tt).
  Defined.
End LiftPseudofunctor.

Section LiftBiadjunction.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L)
          (P₁ : B₁ → UU) (P₂ : B₂ → UU)
          (HP₁ : ∏ (x : B₁), P₁ x → P₂ (L x))
          (HP₂ : ∏ (x : B₂), P₂ x → P₁ (R x)).

  Local Notation "'η'" := (biadj_unit (pr1 R)).
  Local Notation "'ε'" := (biadj_counit R).
  
  Definition disp_fullsub_biadjunction
    : disp_left_biadj_data _ _ R (disp_fullsub_psfunctor L _ _ HP₁).
  Proof.
    use tpair.
    - use tpair.
      + exact (disp_fullsub_psfunctor R _ _ HP₂).
      + split.
        * use make_disp_pstrans.
          ** apply disp_2cells_isaprop_fullsubbicat.
          ** apply disp_locally_groupoid_fullsubbicat.
          ** exact (λ _ _, tt).
          ** exact (λ _ _ _ _ _ _, tt).
        * use make_disp_pstrans.
          ** apply disp_2cells_isaprop_fullsubbicat.
          ** apply disp_locally_groupoid_fullsubbicat.
          ** exact (λ _ _, tt).
          ** exact (λ _ _ _ _ _ _, tt).
    - split.
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_fullsubbicat.
        * apply disp_locally_groupoid_fullsubbicat.
        * exact (λ _ _, tt).
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_fullsubbicat.
        * apply disp_locally_groupoid_fullsubbicat.
        * exact (λ _ _, tt).
  Defined.
End LiftBiadjunction.
