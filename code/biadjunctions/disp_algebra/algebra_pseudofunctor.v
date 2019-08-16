(* Lifting pseudofunctors to pseudofunctors on algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
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
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBuilders.

Local Open Scope cat.

Local Arguments lassociator {_ _ _ _ _ _ _ _}.
Local Arguments rassociator {_ _ _ _ _ _ _ _}.

Section LiftPseudofunctor.
  Context {B₁ B₂ : bicat}
          {H₁ : psfunctor B₁ B₁} {H₂ : psfunctor B₂ B₂}
          (F : psfunctor B₁ B₂)
          (γ : pstrans (ps_comp H₂ F) (ps_comp F H₁)).

  Definition disp_alg_psfunctor_mor
    : ∏ {x y : B₁}
        {f : B₁ ⟦ x, y ⟧}
        {xx : B₁ ⟦ H₁ x, x ⟧} {yy : B₁ ⟦ H₁ y, y ⟧},
      invertible_2cell (xx · f) (# H₁ f · yy)
      →
      mor_disp
        (D := disp_alg_bicat H₂)
        (γ x · #F xx)
        (γ y · #F yy)
        (#F f).
  Proof.
    intros x y f xx yy ff.
    use tpair.
    - exact (rassociator
               • (γ x ◃ ((psfunctor_comp F xx f)
                           • ##F ff
                           • (psfunctor_comp F (#H₁ f) yy)^-1))
               • lassociator
               • (psnaturality_of γ f ▹ #F yy)
               • rassociator).
    - cbn.
      is_iso.
      + apply (psfunctor_comp F xx f).
      + apply psfunctor_is_iso.
      + apply (psnaturality_of γ f).
  Defined.

  Definition disp_alg_psfunctor_cell
             {a b : B₁}
             {f g : B₁ ⟦ a, b ⟧}
             {x : f ==> g}
             {aa : B₁ ⟦ H₁ a, a ⟧}
             {bb : B₁ ⟦ H₁ b, b ⟧}
             {ff : invertible_2cell (aa · f) (# H₁ f · bb)}
             {gg : invertible_2cell (aa · g) (# H₁ g · bb)}
             (xx : alg_disp_cat_2cell H₁ a b f g x aa bb ff gg)
    : alg_disp_cat_2cell
        _ _ _ _ _ (## F x) _ _
        (disp_alg_psfunctor_mor ff)
        (disp_alg_psfunctor_mor gg).
  Proof.
    unfold alg_disp_cat_2cell ; cbn.
    etrans.
    {
      rewrite !vassocr.
      rewrite <- lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply idpath.
    }
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    apply maponpaths.
    rewrite <- rwhisker_rwhisker_alt.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    apply maponpaths_2.
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      rewrite rwhisker_vcomp.
      apply maponpaths.
      apply (!(psnaturality_natural γ _ _ _ _ x)).
    }
    rewrite <- rwhisker_vcomp.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    apply maponpaths_2.
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    rewrite <- rwhisker_lwhisker.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    apply maponpaths_2.
    rewrite !lwhisker_vcomp.
    apply maponpaths.
    cbn.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    rewrite <- psfunctor_lwhisker.
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    apply maponpaths.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    use vcomp_move_L_Mp.
    { is_iso. }
    cbn.
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    rewrite <- psfunctor_rwhisker.
    etrans.
    {
      apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite vcomp_lid.
      apply id2_left.
    }
    rewrite <- !psfunctor_vcomp.
    apply maponpaths.
    exact (!xx).
  Qed.
  
  Definition disp_alg_psfunctor_identitor
             {a : B₁}
             (aa : disp_alg_bicat H₁ a)
    : alg_disp_cat_2cell
        _ _ _ _ _
        (psfunctor_id F a) _ _
        (id_disp (D := disp_alg_bicat H₂) (γ a · # F aa))
        (disp_alg_psfunctor_mor (id_disp aa)).
  Proof.
    unfold alg_disp_cat_2cell ; simpl.
    etrans.
    {
      do 4 (refine (vassocr _ _ _ @ _) ; apply maponpaths_2).
      refine (!_).
      apply lwhisker_lwhisker_rassociator.
    }
    rewrite <- runitor_triangle.
    rewrite linvunitor_assoc.
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (vassocl _ _ _ @ _).
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      repeat (refine (vassocl _ _ _ @ _)).
      rewrite <- rwhisker_rwhisker_alt.
      apply idpath.
    }
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      do 2 apply maponpaths.
      rewrite psfunctor_vcomp.
      apply idpath.
    }
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    etrans.
    {
      do 4 apply maponpaths.
      exact (pstrans_id_alt γ a).
    }
    cbn.
    rewrite <- !lwhisker_vcomp.
    rewrite <- !rwhisker_vcomp.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    do 2 apply maponpaths_2.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    apply maponpaths_2.
    rewrite !lwhisker_vcomp.
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    etrans.
    {
      apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      etrans.
      {
        apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        apply idpath.
      }
      rewrite <- rwhisker_lwhisker.
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite <- rwhisker_lwhisker.
      repeat (refine (vassocl _ _ _ @ _)).
      rewrite runitor_rwhisker.
      apply idpath.
    }
    rewrite !lwhisker_vcomp.
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    apply maponpaths.
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    etrans.
    {
      do 3 apply maponpaths_2.
      repeat (refine (vassocr _ _ _ @ _)).
      apply maponpaths_2.
      repeat (refine (vassocr _ _ _ @ _)).
      apply maponpaths_2.
      repeat (refine (vassocr _ _ _ @ _)).
      etrans.
      {
        apply maponpaths.
        apply psfunctor_vcomp.
      }
      repeat (refine (vassocr _ _ _ @ _)).
      apply maponpaths_2.
      exact (!(psfunctor_runitor F aa)).
    }
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    etrans.
    {
      do 4 apply maponpaths.
      rewrite psfunctor_lunitor.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite rwhisker_vcomp.
        rewrite vcomp_lid.
        rewrite id2_rwhisker, id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- psfunctor_rwhisker.
      rewrite !vassocl.
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite !vassocr.
        rewrite vcomp_lid.
        rewrite id2_left.
        apply idpath.
      }
      rewrite !vassocr.
      rewrite <- psfunctor_vcomp.
      rewrite rwhisker_vcomp.
      rewrite vcomp_rinv.
      rewrite id2_rwhisker.
      rewrite psfunctor_id2.
      apply id2_left.
    }
    rewrite <- psfunctor_vcomp.
    rewrite linvunitor_lunitor.
    rewrite psfunctor_id2.
    apply id2_right.
  Qed.

  Definition disp_alg_psfunctor_compositor
             {x y z : B₁}
             {f : B₁ ⟦ x, y ⟧} {g : B₁ ⟦ y, z ⟧}
             {xx : disp_alg_bicat H₁ x}
             {yy : disp_alg_bicat H₁ y}
             {zz : (disp_alg_bicat H₁) z}
             (ff : xx -->[ f] yy) (gg : yy -->[ g] zz)
    : disp_2cells
        (psfunctor_comp F f g)
        (disp_alg_psfunctor_mor ff;; disp_alg_psfunctor_mor gg)
        (disp_alg_psfunctor_mor (ff;; gg)%mor_disp).
  Proof.
    cbn. unfold alg_disp_cat_2cell.
    cbn.
    etrans.
    {
      etrans.
      {
        repeat (refine (vassocr _ _ _ @ _)).
        apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        rewrite <- lwhisker_lwhisker_rassociator.
        apply idpath.
      }
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    refine (!_).
    etrans.
    {
      do 5 (repeat (refine (vassocr _ _ _ @ _)) ; apply maponpaths_2).
      etrans.
      {
        apply maponpaths.
        rewrite !vassocl.
        rewrite <- rwhisker_vcomp.
        apply idpath.
      }
      repeat (refine (vassocr _ _ _ @ _)).
      apply maponpaths_2.
      rewrite <- lassociator_lassociator.
      repeat (refine (vassocl _ _ _ @ _)).
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_right.
      apply idpath.
    }
    refine (!_).
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    rewrite lwhisker_vcomp.
    etrans.
    {
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply maponpaths.
        exact (pstrans_comp_alt γ f g).
      }
      simpl.
      apply maponpaths.
      rewrite <- !rwhisker_vcomp.
      repeat (refine (vassocl _ _ _ @ _)).
      do 6 apply maponpaths.
      etrans.
      {
        repeat (refine (vassocl _ _ _ @ _)).
        apply maponpaths.
        rewrite rwhisker_rwhisker_alt.
        apply idpath.
      }
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite rwhisker_rwhisker_alt.
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    do 2 apply maponpaths_2.
    use vcomp_move_R_Mp.
    { is_iso. }
    use vcomp_move_R_Mp.
    { is_iso. }
    simpl.
    refine (!_).
    etrans.
    {
      etrans.
      {
        do 3 apply maponpaths_2.
        apply maponpaths.
        refine (!_).
        apply (lwhisker_vcomp _ _ rassociator).
      }
      repeat (refine (vassocl _ _ _ @ _)).
      do 4 apply maponpaths.
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        repeat (refine (vassocr _ _ _ @ _)).
        rewrite <- lassociator_lassociator.
        repeat (refine (vassocl _ _ _ @ _)).
        rewrite rwhisker_vcomp.
        rewrite lassociator_rassociator.
        rewrite id2_rwhisker.
        rewrite id2_right.
        apply idpath.
      }
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      apply id2_left.
    }
    repeat (refine (_ @ vassocr _ _ _)).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          etrans.
          {
            refine (!_).
            apply rwhisker_vcomp.
          }
          etrans.
          {
            apply maponpaths_2.
            apply maponpaths.
            refine (!_).
            apply lwhisker_vcomp.
          }
          etrans.
          {
            apply maponpaths.
            refine (!_).
            apply rwhisker_vcomp.
          }
          rewrite <- !lwhisker_vcomp.
          rewrite <- !rwhisker_vcomp.
          apply idpath.
        }
        repeat (refine (vassocr _ _ _ @ _)).
        apply idpath.
      }
      etrans.
      {
        do 3 apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        do 3 apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        apply idpath.
      }
      rewrite <- rwhisker_lwhisker.
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite <- rwhisker_lwhisker.
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite <- rwhisker_lwhisker.
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    use vcomp_move_R_pM.
    { is_iso. }
    simpl.
    refine (!_).
    etrans.
    {
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite lwhisker_vcomp.
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths_2.
      apply maponpaths.
      etrans.
      {
        repeat (refine (vassocr _ _ _ @ _)).
        apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        apply maponpaths_2.
        apply (!(psfunctor_rassociator F xx f g)).
      }
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    rewrite <- lwhisker_vcomp.
    repeat (refine (vassocl _ _ _ @ _)).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        repeat (refine (vassocr _ _ _ @ _)).
        rewrite <- psfunctor_vcomp.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths.
          repeat (refine (vassocr _ _ _ @ _) ; apply maponpaths_2).
          apply rassociator_lassociator.
        }
        rewrite id2_left.
        rewrite !psfunctor_vcomp.
        apply idpath.
      }
      repeat (refine (vassocr _ _ _ @ _)).
      etrans.
      {
        apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _) ; apply maponpaths_2).
        apply psfunctor_rwhisker.
      }
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    rewrite <- lwhisker_vcomp.
    repeat (refine (vassocl _ _ _ @ _)).
    apply maponpaths.
    use vcomp_move_L_pM.
    { is_iso. }
    simpl.
    etrans.
    {
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite lwhisker_vcomp.
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths_2.
      apply maponpaths.
      etrans.
      {
        repeat (refine (vassocr _ _ _ @ _)).
        do 4 apply maponpaths_2.
        apply (psfunctor_rassociator F (#H₁ f) yy g).
      }
      repeat (refine (vassocl _ _ _ @ _)).
      etrans.
      {
        do 2 apply maponpaths.
        repeat (refine (vassocr _ _ _ @ _)).
        rewrite psfunctor_lwhisker.
        repeat (refine (vassocl _ _ _ @ _)).
        apply idpath.
      }
      assert
      ((## F ((pr222 (pr1 H₁)) _ _ _ f g ▹ _))
         • (psfunctor_comp F _ zz)^-1
       =
       ((psfunctor_comp F _ zz)^-1)
         • (## F ((pr222 (pr1 H₁)) _ _ _ f g) ▹ _))
        as q.
      {
        use vcomp_move_R_Mp.
        { is_iso. }
        simpl.
        rewrite !vassocl.
        use vcomp_move_L_pM.
        { is_iso. }
        apply (psfunctor_rwhisker F zz (pr222 (pr1 H₁) _ _ _ f g)).
      }
      etrans.
      {
        do 5 apply maponpaths.
        exact q.
      }
      clear q.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 5 apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        repeat (refine (_ @ lwhisker_vcomp _ _ _) ; apply maponpaths_2).
        apply idpath.
      }
      repeat (refine (vassocl _ _ _ @ _)).
      rewrite rwhisker_lwhisker.
      apply idpath.
    }
    repeat (refine (vassocr _ _ _ @ _)).
    repeat (refine (_ @ vassocl _ _ _)).
    apply maponpaths_2.
    use vcomp_move_L_Mp.
    { is_iso. }
    simpl.
    repeat (refine (_ @ vassocr _ _ _)).
    repeat (refine (vassocl _ _ _ @ _)).
    etrans.
    {
      do 7 apply maponpaths.
      refine (vassocr _ _ _ @ _).
      apply lassociator_lassociator.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      rewrite <- !lwhisker_vcomp.
      rewrite <- !rwhisker_vcomp.
      repeat (refine (vassocr _ _ _ @ _)).
      etrans.
      {
        do 2 apply maponpaths_2.
        repeat (refine (vassocr _ _ _ @ _)).
        apply idpath.
      } 
      rewrite <- rwhisker_lwhisker.
      repeat (refine (vassocl _ _ _ @ _)).
      apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite <- rwhisker_lwhisker.
      apply idpath.
    }
    etrans.
    {
      repeat (refine (vassocr _ _ _ @ _)).
      rewrite !lwhisker_vcomp.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      etrans.
      {
        do 3 apply maponpaths.
        repeat (refine (vassocr _ _ _ @ _)).
        do 3 apply maponpaths_2.
        apply rassociator_rassociator.
      }
      etrans.
      {
        do 3 apply maponpaths.
        repeat (refine (vassocl _ _ _ @ _)).
        apply idpath.
      }
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          repeat (refine (vassocr _ _ _ @ _)).
          do 4 apply maponpaths_2.
          apply rwhisker_rwhisker_alt.
        }
        repeat (refine (vassocl _ _ _ @ _)).
        apply idpath.
      }
      repeat (refine (vassocr _ _ _ @ _)).        
      etrans.
      {
        do 5 apply maponpaths_2.
        refine (vassocl _ _ _ @ _).
        rewrite rwhisker_hcomp.
        rewrite <- inverse_pentagon_5.
        rewrite <- lwhisker_hcomp.
        apply idpath.
      }
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    repeat (refine (vassocl _ _ _ @ _)).
    repeat (refine (_ @ vassocr _ _ _)).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        repeat (refine (vassocl _ _ _ @ _)).
        apply idpath.
      }
      refine (!_).
      apply lwhisker_vcomp.
    }
    repeat (refine (vassocl _ _ _ @ _)).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      etrans.
      {
        repeat (repeat (refine (vassocl _ _ _ @ _)) ; apply maponpaths).
        apply idpath.
      }
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        rewrite rwhisker_vcomp.
        rewrite <- psfunctor_vcomp.
        rewrite vcomp_rinv.
        rewrite psfunctor_id2.
        rewrite id2_rwhisker.
        apply idpath.
      }
      apply id2_right.
    }
    refine (!_).
    repeat (refine (vassocr _ _ _ @ _)).
    use vcomp_move_R_Mp.
    { is_iso. }
    simpl.
    refine (!_).
    etrans.
    {
      repeat (repeat (refine (vassocl _ _ _ @ _)) ; apply maponpaths).
      apply idpath.
    }
    etrans.
    {
      repeat (refine (vassocl _ _ _ @ _)).
      rewrite rwhisker_rwhisker_alt.
      do 2 apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      apply maponpaths_2.
      rewrite rwhisker_hcomp.
      repeat (refine (vassocl _ _ _ @ _)).
      rewrite <- inverse_pentagon_5.
      rewrite <- lwhisker_hcomp.
      apply idpath.
    }
    etrans.
    {
      repeat (refine (vassocr _ _ _ @ _)).
      do 2 apply maponpaths_2.
      apply lwhisker_vcomp.
    }
    etrans.
    {
      apply maponpaths_2.
      repeat (refine (vassocr _ _ _ @ _)).
      apply maponpaths_2.
      apply lwhisker_vcomp.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      do 2 (apply maponpaths ; repeat (refine (vassocl _ _ _ @ _))).
      apply maponpaths.
      repeat (refine (vassocr _ _ _ @ _)).
      etrans.
      {
        repeat (repeat (refine (vassocr _ _ _ @ _)) ; apply maponpaths_2).
        apply idpath.
      }
      apply psfunctor_lassociator_alt.
    }
    etrans.
    {
      rewrite !lwhisker_vcomp.
      rewrite lwhisker_lwhisker.
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    repeat (refine (_ @ vassocr _ _ _)).      
    apply maponpaths.
    etrans.
    {
      rewrite <- vcomp_whisker.
      repeat (refine (vassocl _ _ _ @ _)).
      apply idpath.
    }
    apply maponpaths.
    use vcomp_move_L_pM.
    { is_iso. }
    simpl.
    rewrite <- lwhisker_lwhisker.
    apply maponpaths_2.
    do 2 apply maponpaths.
    repeat (refine (vassocr _ _ _ @ _)).
    apply idpath.
  Qed.
  
  Definition disp_alg_psfunctor
    : disp_psfunctor (disp_alg_bicat H₁) (disp_alg_bicat H₂) F.
  Proof.
    use make_disp_psfunctor.
    - apply disp_2cells_isaprop_alg.
    - apply disp_locally_groupoid_alg.
    - exact (λ x f, γ x · #F f).
    - exact @disp_alg_psfunctor_mor.
    - exact @disp_alg_psfunctor_cell.
    - exact @disp_alg_psfunctor_identitor.
    - exact @disp_alg_psfunctor_compositor.
  Defined.
End LiftPseudofunctor.
