(** The naturality condition for the unit pseudotransformation *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.

Require Import signature.hit_signature.
Require Import prelude.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import biadjunctions.all.
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_path_groupoid.
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_gquot.

Local Open Scope cat.

Definition poly_path_groupoid_gquot_functor
           (P : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
           z
  : (pr1 ((poly_path_groupoid P) (gquot_functor_obj G₂)))
      (poly_map P (gcl G₂) (poly_map P (pr1 F) z))
    =
    (pr1 ((pr111 (poly_path_groupoid P)) (gquot_functor_obj G₂)))
      (poly_map P (gquot_functor_map F) (poly_map P (gcl G₁) z)).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Definition prealg_unit_comp_help
           (P : poly_code)
           {G : grpd_bicat}
           (z : poly_act P (pr1 G))
  : gcl (poly_act_groupoid P G) z
    =
    ((poly_gquot P)
       G
       (pr1 (poly_path_groupoid
               P (gquot_functor_obj G))
            (poly_map P (gcl G) z))).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + exact (maponpaths gquot_inl_grpd (IHP₁ z)).
    + exact (maponpaths gquot_inr_grpd (IHP₂ z)).
  - exact (maponpaths
             (λ z, prod_gquot_comp (pr1 z) (dirprod_pr2 z))
             (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z)))).
Defined.

Section LiftUnit.
  Variable (P : poly_code).

  Local Arguments poly_act_compose _ {_ _ _ _} _ _.
  Local Arguments poly_act_functor_composition_data _ {_ _ _} _ _.
  Local Arguments poly_act_nat_trans_data _ {_ _ _ _} _.

  Definition prealg_unit_nat_trans_comp
             {G : grpd_bicat}
             (hG : (disp_alg_bicat ⦃ P ⦄) G)
    : nat_trans_data
        ((disp_pseudo_id (disp_alg_bicat ⦃ P ⦄)) G hG ∙ gquot_unit G)
        (# ⦃ P ⦄ (gquot_unit G)
           ∙ (disp_pseudo_comp
                gquot_psfunctor path_groupoid (disp_alg_bicat ⦃ P ⦄)
                (disp_alg_bicat (⟦ P ⟧)) (disp_alg_bicat ⦃ P ⦄) (prealg_gquot P)
                (prealg_path_groupoid P)) G hG)
    := λ z, maponpaths (gquot_functor_map hG) (prealg_unit_comp_help P z).

  Definition prealg_unit_is_nat_trans
             {G : grpd_bicat}
             (hG : (disp_alg_bicat ⦃ P ⦄) G)
    : is_nat_trans _ _ (prealg_unit_nat_trans_comp hG).
  Proof.
    intros z₁ z₂ g.
    cbn.
    unfold prealg_unit_nat_trans_comp.
    unfold prealg_gquot_map.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathscomp _ _ _)).
    }
    refine (!(maponpathscomp0 _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      assert (gcleq G (# (pr1 hG) g) = maponpaths (gquot_functor_map hG) (gcleq _ g))
        as H.
      {
        refine (!_).
        exact (gquot_rec_beta_gcleq
                 (poly_act_groupoid P G)
                 _ _ _ _ _ _ _ _
                 g).
      }
      exact H.
    }
    refine (!(maponpathscomp0 _ _ _) @ _).
    apply maponpaths.
    simpl.
    clear hG.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - induction g.
      exact (pathscomp0rid _ @ ge _ _).
    - refine (pathscomp0rid _ @ !_).
      apply gquot_rec_beta_gcleq.
    - induction z₁ as [z₁ | z₁], z₂ as [z₂ | z₂].
      + specialize (IHP₁ z₁ z₂ g) ; clear IHP₂ ; simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (maponpathscomp inl _ _ @ _).
          exact (!(maponpathscomp _ gquot_inl_grpd _)).
        }
        refine (!(maponpathscomp0 _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (!IHP₁).
        }
        refine (maponpathscomp0 _ _ _ @ _).
        apply maponpaths_2.
        apply gquot_rec_beta_gcleq.
      + exact (fromempty g).
      + exact (fromempty g).
      + specialize (IHP₂ z₁ z₂ g) ; clear IHP₁ ; simpl.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (maponpathscomp inr _ _ @ _).
          exact (!(maponpathscomp _ gquot_inr_grpd _)).
        }
        refine (!(maponpathscomp0 _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          exact (!IHP₂).
        }
        refine (maponpathscomp0 _ _ _ @ _).
        apply maponpaths_2.
        apply gquot_rec_beta_gcleq.
    - simpl.
      specialize (IHP₁ (pr1 z₁) (pr1 z₂) (pr1 g)).
      specialize (IHP₂ (pr2 z₁) (pr2 z₂) (pr2 g)).
      apply TODO.
  Qed.

  Definition prealg_unit_nat_trans
             {G : grpd_bicat}
             (hG : (disp_alg_bicat ⦃ P ⦄) G)
    : (disp_pseudo_id (disp_alg_bicat ⦃ P ⦄)) G hG ∙ gquot_unit G
      ⟹
      # ⦃ P ⦄ (gquot_unit G)
      ∙ (disp_pseudo_comp
           gquot_psfunctor path_groupoid (disp_alg_bicat ⦃ P ⦄)
           (disp_alg_bicat (⟦ P ⟧)) (disp_alg_bicat ⦃ P ⦄) (prealg_gquot P)
           (prealg_path_groupoid P)) G hG.
  Proof.
    use make_nat_trans.
    - exact (prealg_unit_nat_trans_comp hG).
    - exact (prealg_unit_is_nat_trans hG).
  Defined.

  Definition prealg_unit_natural_lem₁_inl
             {G₁ G₂ : grpd_bicat}
             {F : grpd_bicat ⟦ G₁, G₂ ⟧}
             (P₁ P₂ : poly_code)
             (z : poly_act P₁ (pr1 G₁))
             {q : gquot (poly_act_groupoid P₁ G₁)}
             (p : gcl (poly_act_groupoid P₁ G₁) z = q)
    : maponpaths
        (gquot_functor_map (poly_act_functor (P₁ + P₂) G₁ G₂ F))
        (maponpaths gquot_inl_grpd p)
    @ gquot_inl_grpd_gquot_functor F q
    =
    maponpaths
      gquot_inl_grpd
      (maponpaths (gquot_functor_map (poly_act_functor P₁ G₁ G₂ F))
                  p).
  Proof.
    induction p.
    apply idpath.
  Qed.

  Definition prealg_unit_natural_lem₁_inr
             {G₁ G₂ : grpd_bicat}
             {F : grpd_bicat ⟦ G₁, G₂ ⟧}
             (P₁ P₂ : poly_code)
             (z : poly_act P₂ (pr1 G₁))
             {q : gquot (poly_act_groupoid P₂ G₁)}
             (p : gcl (poly_act_groupoid P₂ G₁) z = q)
    : maponpaths
        (gquot_functor_map (poly_act_functor (P₁ + P₂) G₁ G₂ F))
        (maponpaths gquot_inr_grpd p)
      @ gquot_inr_grpd_gquot_functor F q
      =
      maponpaths
        gquot_inr_grpd
        (maponpaths (gquot_functor_map (poly_act_functor P₂ G₁ G₂ F))
                    p).
  Proof.
    induction p.
    apply idpath.
  Qed.

  Definition prealg_unit_natural_lem₁
             {G₁ G₂ : grpd_bicat}
             (F : grpd_bicat ⟦ G₁, G₂ ⟧)
             (z : poly_act P (pr1 G₁))
    : maponpaths
        (gquot_functor_map (poly_act_functor P G₁ G₂ F))
        (prealg_unit_comp_help P z)
    @ pr1 (psnaturality_of (poly_gquot P) F)
        ((pr1 ((poly_path_groupoid P)
                 (gquot_psfunctor G₁)))
           (poly_map P (gcl G₁) z))
    @ maponpaths
        (poly_gquot P G₂)
        ((pr11 (psnaturality_of (poly_path_groupoid P) (# gquot_psfunctor F)))
           (poly_map P (gcl G₁) z))
    =
    prealg_unit_comp_help P (poly_map P (pr1 F) z)
    @ maponpaths (poly_gquot P G₂) (poly_path_groupoid_gquot_functor P F z).
  Proof.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - exact (idpath (idpath (gcl (poly_act_groupoid (C A) G₂) z))).
    - apply idpath.
    - induction z as [z | z].
      + refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (maponpathscomp
                    inl
                    (sum_gquot (poly_gquot P₁) (poly_gquot P₂) G₂)
                    (poly_path_groupoid_gquot_functor P₁ F z)
                  @ _).
          exact (!(maponpathscomp
                     _
                     gquot_inl_grpd
                     _)).
        }
        refine (!(maponpathscomp0
                    gquot_inl_grpd
                    (prealg_unit_comp_help P₁ (poly_map P₁ (pr1 F) z))
                    _) @ _).
        refine (maponpaths (maponpaths gquot_inl_grpd) (!(IHP₁ z)) @ _).
        etrans.
        {
          exact (maponpathscomp0 gquot_inl_grpd _ _).
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          refine (maponpathscomp
                    inl
                    (sum_gquot (poly_gquot P₁) (poly_gquot P₂) G₂)
                    ((pr11 (psnaturality_of
                              (poly_path_groupoid P₁)
                              (gquot_functor_map F)))
                       (poly_map P₁ (gcl G₁) z))
                  @ _).
          exact (!(maponpathscomp
                     _
                     gquot_inl_grpd
                     _)).
        }
        etrans.
        {
          apply maponpaths.
          refine (!(path_assoc
                      (gquot_inl_grpd_gquot_functor
                         F
                         (poly_gquot
                            P₁ G₁
                            ((pr1 ((poly_path_groupoid P₁) (gquot_functor_obj G₁)))
                               (poly_map P₁ (gcl G₁) z))))
                      (maponpaths
                         gquot_inl_grpd
                         (pr1 (psnaturality_of (poly_gquot P₁) F)
                              ((pr1 ((poly_path_groupoid P₁)
                                       (gquot_functor_obj G₁)))
                                 (poly_map P₁ (gcl G₁) z))))
                      _)
                   @ _).
          apply maponpaths.
          exact (!(maponpathscomp0 _ _ _)).
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply prealg_unit_natural_lem₁_inl.
      + refine (!_).
        etrans.
        {
          apply maponpaths.
          refine (maponpathscomp
                    inr
                    (sum_gquot (poly_gquot P₁) (poly_gquot P₂) G₂)
                    (poly_path_groupoid_gquot_functor P₂ F z)
                  @ _).
          exact (!(maponpathscomp
                     _
                     gquot_inr_grpd
                     _)).
        }
        refine (!(maponpathscomp0
                    gquot_inr_grpd
                    (prealg_unit_comp_help P₂ (poly_map P₂ (pr1 F) z))
                    _) @ _).
        refine (maponpaths (maponpaths gquot_inr_grpd) (!(IHP₂ z)) @ _).
        etrans.
        {
          exact (maponpathscomp0 gquot_inr_grpd _ _).
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          simpl.
          refine (maponpathscomp
                    inr
                    (sum_gquot (poly_gquot P₁) (poly_gquot P₂) G₂)
                    ((pr11 (psnaturality_of
                              (poly_path_groupoid P₂)
                              (gquot_functor_map F)))
                       (poly_map P₂ (gcl G₁) z))
                  @ _).
          exact (!(maponpathscomp
                     _
                     gquot_inr_grpd
                     _)).
        }
        etrans.
        {
          apply maponpaths.
          refine (!(path_assoc
                      (gquot_inr_grpd_gquot_functor
                         F
                         (poly_gquot
                            P₂ G₁
                            ((pr1 ((poly_path_groupoid P₂) (gquot_functor_obj G₁)))
                               (poly_map P₂ (gcl G₁) z))))
                      (maponpaths
                         gquot_inr_grpd
                         (pr1 (psnaturality_of (poly_gquot P₂) F)
                              ((pr1 ((poly_path_groupoid P₂)
                                       (gquot_functor_obj G₁)))
                                 (poly_map P₂ (gcl G₁) z))))
                      _)
                   @ _).
          apply maponpaths.
          exact (!(maponpathscomp0 _ _ _)).
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply prealg_unit_natural_lem₁_inr.
    - apply TODO.
  Time Qed.
  
  Definition prealg_unit_natural_lem₂
             {G₁ G₂ : grpd_bicat}
             {F : grpd_bicat ⟦ G₁, G₂ ⟧}
             {hG₁ : (disp_alg_bicat ⦃ P ⦄) G₁}
             {hG₂ : (disp_alg_bicat ⦃ P ⦄) G₂}
             (hF : hG₁ -->[ F] hG₂)
             (z : poly_act P (pr1 G₁))
    : maponpaths
        (gquot_functor_map F)
        (maponpaths
           (gquot_functor_map hG₁)
           (prealg_unit_comp_help P z))
      @ prealg_path_groupoid_mor_comp
          P (prealg_gquot_inv_cell P hF) (poly_map P (gcl G₁) z)
      =
      gcleq G₂ (pr11 hF z)
      @ maponpaths
          (gquot_functor_map hG₂)
          (prealg_unit_comp_help P (poly_map P (pr1 F) z))
      @ maponpaths
          (λ (q : poly_act P (gquot G₂)),
             gquot_functor_map hG₂ (poly_gquot P G₂ q))
          (poly_path_groupoid_gquot_functor P F z).
  Proof.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp _ (gquot_functor_map hG₂) _)).
      }
      exact (!(maponpathscomp0
                 (gquot_functor_map hG₂)
                 (prealg_unit_comp_help P (poly_map P (pr1 F) z))
                 (maponpaths
                    ((poly_gquot P) G₂)
                    (poly_path_groupoid_gquot_functor P F z)))).
    }
    refine (!_).
    etrans.
    {
      refine (maponpaths (λ z, _ @ (_ @ z)) _).
      exact (!(maponpathscomp (poly_gquot P G₂) (gquot_functor_map hG₂) _)).
    }
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (!(maponpathscomp0 (gquot_functor_map hG₂) _ _)).
    }
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp.
      }
      exact (homotsec_natural'
               (prealg_gquot_help P F hF)
               (prealg_unit_comp_help P z)).
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp
                 (gquot_functor_map (poly_act_functor P G₁ G₂ F))
                 (gquot_functor_map hG₂)
                 _)).
    }
    refine (!(maponpathscomp0 (gquot_functor_map hG₂) _ _) @ _).
    apply maponpaths.
    exact (prealg_unit_natural_lem₁ F z).
  Qed.

  Definition prealg_unit_natural_lem₃
             {G₁ G₂ : grpd_bicat}
             (F : grpd_bicat ⟦ G₁, G₂ ⟧)
             (z : poly_act P (pr1 G₁))
    : poly_path_groupoid_gquot_functor P F z
    @ # (poly_path_groupoid
           P (gquot_functor_obj G₂) : _ ⟶ _)
        (poly_act_compose
           P
           (@poly_act_functor_composition_data
              P G₁ (one_type_to_groupoid (gquot_functor_obj G₁))
              (one_type_to_groupoid (gquot_functor_obj G₂)) (gquot_unit_functor G₁)
              (function_to_functor (gquot_functor_map F)) z)
           (poly_act_nat_trans_data P (gquot_unit_nat_trans G₁ G₂ F) z))
      =
      # (poly_path_groupoid P (gquot_functor_obj G₂) : _ ⟶ _)
        (@poly_act_functor_composition_data
           P G₁ G₂
           (one_type_to_groupoid (gquot_functor_obj G₂))
           F (gquot_unit_functor G₂) z).
  Proof.
    induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    - exact (idpath (idpath z)).
    - exact (idpath _).
    - induction z as [z | z].
      + exact (!(maponpathscomp0 inl _ _) @ maponpaths (maponpaths inl) (IHP₁ z)).
      + exact (!(maponpathscomp0 inr _ _) @ maponpaths (maponpaths inr) (IHP₂ z)).
    - exact (pathsdirprod_concat _ _ _ _
              @ maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
              @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
  Qed.
  
  Definition prealg_unit_natural
             {G₁ G₂ : grpd_bicat}
             {F : grpd_bicat ⟦ G₁, G₂ ⟧}
             {hG₁ : (disp_alg_bicat ⦃ P ⦄) G₁}
             {hG₂ : (disp_alg_bicat ⦃ P ⦄) G₂}
             (hF : hG₁ -->[ F] hG₂)
             (z : poly_act P (pr1 G₁))
    : (gcleq G₂ (pr11 hF z) @ prealg_unit_nat_trans_comp hG₂ (poly_map P (pr1 F) z))
    @ maponpaths (prealg_gquot_map P G₂ hG₂)
        (# ((poly_path_groupoid P) (gquot_functor_obj G₂) : _ ⟶ _)
           (@poly_act_functor_composition_data
              P G₁ G₂
              (one_type_to_groupoid (gquot_functor_obj G₂))
              F (gquot_unit_functor G₂) z))
    =
    ((maponpaths (gquot_functor_map F) (prealg_unit_nat_trans_comp hG₁ z)
    @ prealg_path_groupoid_mor_comp P
        (prealg_gquot_inv_cell P hF)
        (poly_map P (gcl G₁) z))
    @ maponpaths
        (prealg_gquot_map P G₂ hG₂)
        (# ((poly_path_groupoid P) (gquot_functor_obj G₂) : _ ⟶ _)
           (@poly_act_functor_composition_data
              P G₁ (one_type_to_groupoid (gquot_functor_obj G₁))
              (one_type_to_groupoid (gquot_functor_obj G₂)) (gquot_unit_functor G₁)
              (function_to_functor (gquot_functor_map F)) z)))
    @ maponpaths
        (prealg_gquot_map P G₂ hG₂)
        (# ((poly_path_groupoid P) (gquot_functor_obj G₂) : _ ⟶ _)
           (poly_act_nat_trans_data
              P (gquot_unit_nat_trans G₁ G₂ F) z)).
  Proof.
    refine (!_).
    etrans.
    {
      do 2 refine (!(path_assoc _ _ _) @ _).
      do 2 apply maponpaths.
      refine (!(maponpathscomp0 (prealg_gquot_map P G₂ hG₂) _ _) @ _).
      apply maponpaths.
      refine (!(functor_comp ((poly_path_groupoid P) (gquot_functor_obj G₂)) _ _)).        
    }
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (prealg_unit_natural_lem₂ hF z).
    }
    refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    simpl.
    unfold prealg_gquot_map.
    simpl.
    cbn.
    refine (!(maponpathscomp0
                (λ q, gquot_functor_map hG₂ ((poly_gquot P) G₂ q))
                _
                _)
             @ _).
    apply maponpaths.
    exact (prealg_unit_natural_lem₃ F z).
  Qed.

  Definition prealg_unit
    : disp_pstrans
        (disp_pseudo_id (disp_alg_bicat ⦃ P ⦄))
        (disp_pseudo_comp
           gquot_psfunctor path_groupoid (disp_alg_bicat ⦃ P ⦄)
           (disp_alg_bicat (⟦ P ⟧)) (disp_alg_bicat ⦃ P ⦄) (prealg_gquot P)
           (prealg_path_groupoid P)) gquot_unit.
  Proof.
    use make_disp_pstrans.
    - apply disp_2cells_isaprop_alg.
    - apply disp_locally_groupoid_alg.
    - intros G hG.
      use make_invertible_2cell.
      + exact (prealg_unit_nat_trans hG).
      + apply grpd_bicat_is_invertible_2cell.
    - abstract
        (intros G₁ G₂ F hG₁ hG₂ hF ;
         use nat_trans_eq ; [ apply homset_property | ] ;
         intro z ;
         refine (maponpaths
                   (λ z, z @ _)
                   (pathscomp0rid
                      ((gcleq G₂ (pr11 hF z) @ idpath _)
                         @ prealg_unit_nat_trans_comp hG₂ (poly_map P (pr1 F) z))
                      @ maponpaths (λ z, z @ _)
                      (pathscomp0rid _))
                   @ _) ;
         refine (!_) ;
         refine (maponpaths
                   (λ z, (z @ _) @ _)
                   (pathscomp0rid
                      ((maponpaths
                          (gquot_functor_map F)
                          (prealg_unit_nat_trans_comp hG₁ z)
                          @ idpath _)
                         @ prealg_path_groupoid_mor_comp
                             P
                             (prealg_gquot_inv_cell P hF)
                             (poly_map P (gcl G₁) z)))
                   @ maponpaths
                       (λ z, ((z @ _) @ _) @ _)
                       (pathscomp0rid _)
                   @ _) ;
         exact (!(prealg_unit_natural hF z))).
  Defined.
End LiftUnit.
