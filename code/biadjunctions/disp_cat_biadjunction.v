(**
Conditions to lift a biadjunction between bicategories to a displayed biadjunction between
displayed bicategories obtained from displayed categories.
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

Local Open Scope cat.

Section LiftPseudofunctor.
  Context {B₁ B₂ : bicat}
          (F : psfunctor B₁ B₂)
          {D₁ : disp_cat_data B₁}
          {D₂ : disp_cat_data B₂}
          (FFobj :  ∏ (x : B₁), D₁ x → D₂ (F x))
          (FFmor :  ∏ (x y : B₁)
                      (f : B₁ ⟦ x, y ⟧)
                      (xx : D₁ x) (yy : D₁ y),
                    xx -->[ f] yy → FFobj x xx -->[ # F f] FFobj y yy).

  Definition disp_cell_unit_psfunctor
    : disp_psfunctor (disp_cell_unit_bicat D₁) (disp_cell_unit_bicat D₂) F.
  Proof.
    use make_disp_psfunctor.
    - apply disp_2cells_isaprop_cell_unit_bicat.
    - apply disp_locally_groupoid_cell_unit_bicat.
    - exact FFobj.
    - exact FFmor.
    - exact (λ _ _ _ _ _ _ _ _ _ _, tt).
    - exact (λ _ _, tt).
    - exact (λ _ _ _ _ _ _ _ _ _ _, tt).
  Defined.
End LiftPseudofunctor.

Section LiftBiadjunction.
  Context {B₁ B₂ : bicat}
          {L : psfunctor B₁ B₂}
          (R : left_biadj_data L)
          {D₁ : disp_cat_data B₁}
          {D₂ : disp_cat_data B₂}
          (LLobj :  ∏ (x : B₁), D₁ x → D₂ (L x))
          (LLmor :  ∏ (x y : B₁)
                      (f : B₁ ⟦ x, y ⟧)
                      (xx : D₁ x) (yy : D₁ y),
                    xx -->[ f] yy → LLobj x xx -->[ # L f] LLobj y yy)
          (RRobj :  ∏ (x : B₂), D₂ x → D₁ (R x))
          (RRmor :  ∏ (x y : B₂)
                      (f : B₂ ⟦ x, y ⟧)
                      (xx : D₂ x) (yy : D₂ y),
                    xx -->[ f] yy → RRobj x xx -->[ # R f] RRobj y yy).

  Definition lift_unit_law
    : UU.
  Proof.
    refine (∏ (x : B₁) (xx : D₁ x),
            xx -->[ _ ] RRobj (L x) (LLobj x xx)).
    exact (biadj_unit R x).
  Defined.

  Definition lift_counit_law
    : UU.
  Proof.
    refine (∏ (x : B₂) (xx : D₂ x), LLobj (R x) (RRobj x xx) -->[ _ ] xx).
    exact (biadj_counit R x).
  Defined.

  Variable (ηη : lift_unit_law) (εε : lift_counit_law).
  
  Definition disp_cell_unit_biadjunction
    : disp_left_biadj_data _ _ R (disp_cell_unit_psfunctor L LLobj LLmor).
  Proof.
    use tpair.
    - use tpair.
      + exact (disp_cell_unit_psfunctor R RRobj RRmor).
      + split.
        * use make_disp_pstrans.
          ** apply disp_2cells_isaprop_cell_unit_bicat.
          ** apply disp_locally_groupoid_cell_unit_bicat.
          ** exact ηη.
          ** exact (λ _ _ _ _ _ _, tt).
        * use make_disp_pstrans.
          ** apply disp_2cells_isaprop_cell_unit_bicat.
          ** apply disp_locally_groupoid_cell_unit_bicat.
          ** exact εε.
          ** exact (λ _ _ _ _ _ _, tt).
    - split.
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_cell_unit_bicat.
        * apply disp_locally_groupoid_cell_unit_bicat.
        * exact (λ _ _, tt).
      + use make_disp_invmodification.
        * apply disp_2cells_isaprop_cell_unit_bicat.
        * apply disp_locally_groupoid_cell_unit_bicat.
        * exact (λ _ _, tt).
  Defined.
End LiftBiadjunction.
