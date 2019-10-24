Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

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
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_path_groupoid.
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_gquot.

Local Open Scope cat.

Definition poly_gquot_is_gcl
           (P : poly_code)
           {X : one_types}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : poly_gquot P (one_type_to_groupoid X) z
    =
    gcl (⦃ P ⦄ (one_type_to_groupoid X))
        (poly_map P (gquot_counit_map X) z).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + abstract
        (intros a₁ a₂ g ;
         induction g ;
         apply map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                   _
                   (idpath _)
                   _) ;
           [ refine (maponpaths
                       (maponpaths _)
                       (!(ge _ _)))
           | exact (pathscomp0rid _ @ ge _ _)]).
    + exact (λ _, gtrunc _ _ _).
  - induction z as [z | z].
    + exact (maponpaths gquot_inl_grpd (IHP₁ z)).
    + exact (maponpaths gquot_inr_grpd (IHP₂ z)).
  - exact (maponpaths
             (λ z, prod_gquot_comp (pr1 z) (dirprod_pr2 z))
             (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z)))).
Defined.

Definition poly_path_groupoid_poly_map
           (P : poly_code)
           {X : one_types}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : pr1 (pr111 (poly_path_groupoid P) X) (poly_map P (gquot_counit_map X) z)
    =
    poly_map P (gquot_counit_map X) z.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + abstract
        (intros a₁ a₂ g ;
         induction g ;
         apply map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                   _
                   (idpath _)
                   _) ;
         [ refine (maponpaths
                     (maponpaths _)
                     (!(ge _ _)))
         | apply idpath ]).
    + exact (λ _, one_type_isofhlevel _ _ _).
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Definition poly_act_morphism_counit_pg
           {P : poly_code}
           {X Y : one_types}
           (f : one_types ⟦ X, Y ⟧)
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : poly_act_morphism
      P
      (one_type_to_groupoid Y)
      (poly_map
         P f
         (poly_map P (gquot_counit_map X) z))
      (poly_map
         P (gquot_counit_map Y)
         (poly_map
            P (gquot_functor_map
                 (function_to_functor f)) z)).
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + abstract
        (intros a₁ a₂ g ;
         induction g ;
         apply map_PathOver ;
         simpl ;
         rewrite ge ;
         simpl ;
         apply idpath).
    + exact (λ _, one_type_isofhlevel _ _ _).
  - induction z as [z | z].
    + exact (IHP₁ z).
    + exact (IHP₂ z).
  - exact (IHP₁ (pr1 z) ,, IHP₂ (pr2 z)).
Defined.

Local Definition psnaturality_help
      {P : poly_code}
      {X Y : one_types}
      {f : one_types ⟦ X, Y ⟧}
      (z : poly_act P (gquot (one_type_to_groupoid X)))
  : gquot_functor_map
      (poly_act_functor
         P
         (function_to_functor f))
      ((poly_gquot P) (one_type_to_groupoid X) z)
    =
    poly_gquot
      P (one_type_to_groupoid Y)
      (poly_map P (gquot_functor_map (function_to_functor f)) z)
  := pr1 (psnaturality_of (poly_gquot P) (function_to_functor f)) z.

Definition poly_act_identity_one_type_to_groupoid
           {P : poly_code}
           {X Y : one_types}
           (f : one_types ⟦ X, Y ⟧)
           (a : poly_act_groupoid P (one_type_to_groupoid X))
  : @poly_act_identity P (one_type_to_groupoid Y) (poly_map P f a)
    =
    poly_act_functor_morphisms
      P
      (function_to_functor f)
      (@poly_act_identity P (one_type_to_groupoid X) a).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction a as [a | a].
    + exact (IHP₁ a).
    + exact (IHP₂ a).
  - exact (pathsdirprod (IHP₁ (pr1 a)) (IHP₂ (pr2 a))).
Qed.

Definition prod_gquot_comp_gquot_functor_map
           {P₁ P₂ : poly_code}
           {X Y : one_types}
           (f : one_types ⟦ X, Y ⟧)
  : ∏ (z₁ : gquot (poly_act_groupoid P₁ (one_type_to_groupoid X)))
      (z₂ : gquot (poly_act_groupoid P₂ (one_type_to_groupoid X))),
    prod_gquot_comp
      (gquot_functor_map
         (poly_act_functor P₁ (function_to_functor f))
         z₁)
      (gquot_functor_map
         (poly_act_functor P₂ (function_to_functor f))
         z₂)
    =
    gquot_functor_map
      (poly_act_functor
         (P₁ * P₂) (function_to_functor f))
      (prod_gquot_comp z₁ z₂)
  := λ z₁ z₂, !(prod_gquot_data_comp_nat_help
                  (one_type_to_groupoid X) (one_type_to_groupoid Y)
                  (function_to_functor f)
                  z₁ z₂).

Definition prealg_counit_equation_lem₁_help_prod₁
           {P₁ P₂ : poly_code}
           {X Y : one_types}
           (f : one_types ⟦ X, Y ⟧)
           (z : poly_act (P₁ * P₂) (gquot (one_type_to_groupoid X)))
  : maponpaths
      (λ z0,
       gquot_functor_map
         (poly_act_functor
            (P₁ * P₂)
            (function_to_functor f))
         z0)
      (! maponpaths
         (λ z0, prod_gquot_comp (pr1 z0) (pr2 z0))
         (pathsdirprod
            (poly_gquot_is_gcl P₁ (pr1 z))
            (poly_gquot_is_gcl P₂ (pr2 z))))
    =
    maponpaths
      (λ z, prod_gquot_comp (pr1 z) (pr2 z))
      (pathsdirprod
         (maponpaths
            (λ z0,
             gquot_functor_map
               (poly_act_functor
                  P₁
                  (function_to_functor f)) z0)
            (! poly_gquot_is_gcl P₁ (pr1 z)))
         (maponpaths
            (λ z0,
             gquot_functor_map
               (poly_act_functor
                  P₂
                  (function_to_functor f)) z0)
            (! poly_gquot_is_gcl P₂ (pr2 z))))
    @ prod_gquot_comp_gquot_functor_map
        f
        (poly_gquot P₁ (one_type_to_groupoid X) (pr1 z))
        (poly_gquot P₂ (one_type_to_groupoid X) (pr2 z)).
Proof.
  pose (homotsec2_natural
          (prod_gquot_comp_gquot_functor_map f)
          (!(poly_gquot_is_gcl P₁ (pr1 z)))
          (!(poly_gquot_is_gcl P₂ (pr2 z))))
    as p.
  refine (_ @ p @ _).
  - etrans.
    {
      apply maponpaths.
      refine (!(maponpathsinv0
                  (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                  (pathsdirprod _ _))
               @ _).
      apply maponpaths.
      apply pathsdirprod_inv.
    }
    refine (_ @ !(pathscomp0lid _)).
    exact (maponpathscomp
             (λ z, prod_gquot_comp (pr1 z) (pr2 z))
             _
             (pathsdirprod
                (! poly_gquot_is_gcl P₁ (pr1 z))
                (! poly_gquot_is_gcl P₂ (pr2 z)))).
  - apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_pathsdirprod.
    }
    exact (maponpathscomp
             (dirprodf _ _)
             (λ z, prod_gquot_comp (pr1 z) (pr2 z))
             (pathsdirprod _ _)).
Qed.

Definition prealg_counit_equation_lem₁_help_prod₂
           {P₁ P₂ : poly_code}
           {X Y : one_types}
           (f : one_types ⟦ X, Y ⟧)
           (z : poly_act (P₁ * P₂) (gquot (one_type_to_groupoid X)))
  : psnaturality_help z
    =
    !(prod_gquot_comp_gquot_functor_map
        f
        (poly_gquot P₁ (one_type_to_groupoid X) (pr1 z))
        (poly_gquot P₂ (one_type_to_groupoid X) (pr2 z)))
    @ maponpaths
        (λ z, prod_gquot_comp (pr1 z) (pr2 z))
        (pathsdirprod
           (psnaturality_help (pr1 z))
           (psnaturality_help (pr2 z))).
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths.
    pose (uncurry_ap
            prod_gquot_comp
            (@psnaturality_help _ _ _ f (pr1 z))
            (@psnaturality_help _ _ _ f (pr2 z)))
      as h.
    unfold uncurry in h.
    exact h.
  }
  refine (path_assoc _ _ _ @ _).
  refine (_ @ !(path_assoc _ _ _)).
  do 2 apply maponpaths_2.
  apply pathsinv0inv0.
Qed.

Definition prealg_counit_equation_lem₁
           {P : poly_code}
           {X Y : one_types}
           {f : one_types ⟦ X, Y ⟧}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : (maponpaths
       (λ z0,
        gquot_functor_map
          (poly_act_functor
             P
             (function_to_functor f)) z0)
       (! poly_gquot_is_gcl P z)
       @ psnaturality_help z)
      @ poly_gquot_is_gcl P (poly_map P (gquot_functor_map (function_to_functor f)) z)
    =
    gcleq
      (poly_act_groupoid P (one_type_to_groupoid Y))
      (poly_act_morphism_counit_pg f z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (!(ge _ _)).
    - revert z.
      use gquot_ind_prop.
      + intro a.
        exact (!(ge _ _)).
      + exact (λ _, one_type_isofhlevel _ _ _ _ _).
    - induction z as [z | z].
      + refine (_
                @ maponpaths (maponpaths gquot_inl_grpd) (IHP₁ z)
                @ gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
        refine (!_).
        etrans.
        {
          exact (maponpathscomp0 _ _ _).
        }
        apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp0
                   gquot_inl_grpd
                   (maponpaths
                      (λ z0,
                       gquot_functor_map
                         (poly_act_functor
                            P₁
                            (function_to_functor f)) z0)
                      (! poly_gquot_is_gcl P₁ z))
                   (psnaturality_help z)).
        }
        refine (!_).
        etrans.
        {
          exact (path_assoc
                   _
                   (gquot_inl_grpd_gquot_functor
                      (function_to_functor f)
                      (poly_gquot P₁ (one_type_to_groupoid X) z))
                   (maponpaths
                      gquot_inl_grpd
                      (psnaturality_help z))).
        }
        apply maponpaths_2.
        pose (homotsec_natural'
                (@gquot_inl_grpd_gquot_functor
                   P₁ P₂ _ _
                   (function_to_functor f))
                 (! poly_gquot_is_gcl P₁ z))
          as h.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 gquot_inl_grpd (poly_gquot_is_gcl P₁ z))).
          }
          exact (maponpathscomp
                   gquot_inl_grpd
                   (λ z0,
                    gquot_functor_map
                      (poly_act_functor
                         (P₁ + P₂)
                         (function_to_functor f)) z0)
                   (! poly_gquot_is_gcl P₁ z)).
        }
        refine (!_).
        etrans.
        {
          exact (maponpathscomp
                   (λ z0 ,
                    gquot_functor_map
                      (poly_act_functor
                         P₁ (function_to_functor f))
                      z0)
                   gquot_inl_grpd
                   (! poly_gquot_is_gcl P₁ z)).
        }
        exact (!h).
      + refine (_
                @ maponpaths (maponpaths gquot_inr_grpd) (IHP₂ z)
                @ gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
        refine (!_).
        etrans.
        {
          exact (maponpathscomp0 _ _ _).
        }
        apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp0
                   gquot_inr_grpd
                   (maponpaths
                      (λ z0,
                       gquot_functor_map
                         (poly_act_functor
                            P₂
                            (function_to_functor f)) z0)
                      (! poly_gquot_is_gcl P₂ z))
                   (psnaturality_help z)).
        }
        refine (!_).
        etrans.
        {
          exact (path_assoc
                   _
                   (gquot_inr_grpd_gquot_functor
                      (function_to_functor f)
                      (poly_gquot P₂ (one_type_to_groupoid X) z))
                   (maponpaths
                      gquot_inr_grpd
                      (psnaturality_help z))).
        }
        apply maponpaths_2.
        pose (homotsec_natural'
                (@gquot_inr_grpd_gquot_functor
                   P₁ P₂ _ _
                   (function_to_functor f))
                 (! poly_gquot_is_gcl P₂ z))
          as h.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 gquot_inr_grpd (poly_gquot_is_gcl P₂ z))).
          }
          exact (maponpathscomp
                   gquot_inr_grpd
                   (λ z0,
                    gquot_functor_map
                      (poly_act_functor
                         (P₁ + P₂)
                         (function_to_functor f)) z0)
                   (! poly_gquot_is_gcl P₂ z)).
        }
        refine (!_).
        etrans.
        {
          exact (maponpathscomp
                   (λ z0 ,
                    gquot_functor_map
                      (poly_act_functor
                         P₂  (function_to_functor f))
                      z0)
                   gquot_inr_grpd
                   (! poly_gquot_is_gcl P₂ z)).
        }
        exact (!h).
    - specialize (IHP₁ (pr1 z)).
      specialize (IHP₂ (pr2 z)).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (prealg_counit_equation_lem₁_help_prod₂ f z).
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (prealg_counit_equation_lem₁_help_prod₁ f z).
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          refine (!(path_assoc _ _ _) @ _).
          apply maponpaths.
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          apply pathsinv0r.
        }
        exact (!(maponpathscomp0
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod
                      (maponpaths
                         (λ z0,
                          gquot_functor_map
                            (poly_act_functor
                               P₁ (function_to_functor f)) z0)
                         (! poly_gquot_is_gcl P₁ (pr1 z)))
                      (maponpaths
                         (λ z0,
                          gquot_functor_map
                            (poly_act_functor
                               P₂ (function_to_functor f)) z0)
                         (! poly_gquot_is_gcl P₂ (pr2 z))))
                   (pathsdirprod
                      (psnaturality_help (pr1 z))
                      (psnaturality_help (pr2 z))))).
      }
      etrans.
      {
        exact (!(maponpathscomp0
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod
                      (maponpaths
                         (λ z0,
                          gquot_functor_map
                            (poly_act_functor
                               P₁
                               (function_to_functor f))
                            z0)
                         (! poly_gquot_is_gcl P₁ (pr1 z)))
                      (maponpaths
                         (λ z0,
                          gquot_functor_map
                            (poly_act_functor
                               P₂
                               (function_to_functor f))
                            z0)
                         (! poly_gquot_is_gcl P₂ (pr2 z)))
                    @
                    pathsdirprod
                        (psnaturality_help (pr1 z))
                        (psnaturality_help (pr2 z)))
                   (pathsdirprod
                      (poly_gquot_is_gcl
                         P₁ (poly_map P₁ (gquot_functor_map (function_to_functor f))
                                      (pr1 z)))
                      (poly_gquot_is_gcl
                         P₂ (poly_map P₂ (gquot_functor_map (function_to_functor f))
                                      (pr2 z)))))).
      }
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply pathsdirprod_concat.
        }
        etrans.
        {
          apply pathsdirprod_concat.
        }
        etrans.
        {
          apply maponpaths.
          exact IHP₂.
        }
        apply maponpaths_2.
        exact IHP₁.
      }
      etrans.
      {
        pose (uncurry_ap
                prod_gquot_comp
                (gcleq (poly_act_groupoid P₁ (one_type_to_groupoid Y))
                       (poly_act_morphism_counit_pg f (pr1 z)))
                (gcleq (poly_act_groupoid P₂ (one_type_to_groupoid Y))
                       (poly_act_morphism_counit_pg f (pr2 z))))
          as h.
        unfold uncurry in h.
        exact h.
      }
      etrans.
      {
        apply maponpaths_2.
        exact (gquot_double_rec'_beta_l_gcleq
                 (poly_act_groupoid P₁ (one_type_to_groupoid Y))
                 (poly_act_groupoid P₂ (one_type_to_groupoid Y))
                 _ _ _ _ _ _ _ _ _ _ _
                 (poly_act_morphism_counit_pg f (pr1 z))).
      }
      etrans.
      {
        apply maponpaths.
        exact (gquot_double_rec'_beta_r_gcleq
                 (poly_act_groupoid P₁ (one_type_to_groupoid Y))
                 (poly_act_groupoid P₂ (one_type_to_groupoid Y))
                 _ _ _ _ _ _ _ _ _ _ _
                 (poly_act_morphism_counit_pg f (pr2 z))).
      }
      refine (!(gconcat _ _ _) @ _).
      apply maponpaths.
      use pathsdirprod.
      + apply poly_act_id_right.
      + apply poly_act_id_left.
Qed.

Definition prealg_counit_equation_lem₂
           {P : poly_code}
           {X Y : one_types}
           {f : one_types ⟦ X, Y ⟧}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : (pr11 (psnaturality_of (poly_path_groupoid P) f))
      (poly_map P (gquot_counit_map X) z)
  @ # (poly_path_groupoid P Y : _ ⟶ _) (poly_act_morphism_counit_pg f z)
  @ poly_path_groupoid_poly_map
      P (poly_map P (gquot_functor_map (function_to_functor f)) z)
  @ poly_comp P (gquot_functor_map (function_to_functor f)) (gquot_counit_map Y) z
  =
  maponpaths (poly_map P f) (poly_path_groupoid_poly_map P z)
  @ poly_comp P (gquot_counit_map X) f z
  @ poly_homot P (gquot_counit_naturality f) z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_prop.
    + exact (λ _, idpath _).
    + exact (λ _, one_type_isofhlevel _ _ _ _ _).
  - induction z as [z | z]
    ; [ specialize (IHP₁ z) ; clear IHP₂ | specialize (IHP₂ z) ; clear IHP₁ ].
    + simpl.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp0 inl _ _)).
          }
          exact (!(maponpathscomp0 inl _ _)).
        }
        exact (!(maponpathscomp0 inl _ _)).
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp0 inl _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply coprodf_path_maponpaths_inl.
        }
        exact (!(maponpathscomp0 inl _ _)).
      }
      apply maponpaths.
      exact (!IHP₁).
    + simpl.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp0 inr _ _)).
          }
          exact (!(maponpathscomp0 inr _ _)).
        }
        exact (!(maponpathscomp0 inr _ _)).
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp0 inr _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          apply coprodf_path_maponpaths_inr.
        }
        exact (!(maponpathscomp0 inr _ _)).
      }
      apply maponpaths.
      exact (!IHP₂).
  - simpl.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_concat.
      }
      etrans.
      {
        apply maponpaths_2.
        refine (!(maponpaths_pathsdirprod _ _ _ _)).
      }
      apply pathsdirprod_concat.
    }
    refine (!_).
    exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
           @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
Qed.

Section LiftCounit.
  Variable (P : poly_code).

  Definition prealg_counit_comp
             {X : one_types}
             (hX : (disp_alg_bicat (⟦ P ⟧)) X)
             (z : poly_act P (gquot (one_type_to_groupoid X)))
    : gquot_counit_map
        X
        (gquot_functor_map
           (prealg_path_groupoid_map P X hX)
           (poly_gquot
              P
              (one_type_to_groupoid X)
              z))
      =
      hX (poly_map P (gquot_counit_map X) z)
    := maponpaths
         (λ z, gquot_counit_map
                 X
                 ((gquot_functor_map (prealg_path_groupoid_map P X hX) z)))
         (poly_gquot_is_gcl P z)
     @ maponpaths
         hX
         (poly_path_groupoid_poly_map P z).

  Definition prealg_counit_equation
             {X Y : one_types}
             {f : one_types ⟦ X, Y ⟧}
             {hX : (disp_alg_bicat (⟦ P ⟧)) X}
             {hY : (disp_alg_bicat (⟦ P ⟧)) Y}
             (hf : hX -->[ f] hY)
             (z : poly_act P (gquot (one_type_to_groupoid X)))
    : (maponpaths
         f
         (prealg_counit_comp hX z)
     @ pr1 hf (poly_map P (gquot_counit_map X) z))
     @ maponpaths
         hY
         (poly_comp P (gquot_counit_map X) f z
          @ poly_homot P (gquot_counit_naturality f) z)
     =
     gquot_counit_naturality
       f
       (gquot_functor_map
          (prealg_path_groupoid_map P X hX)
          (poly_gquot P (one_type_to_groupoid X) z))
     @ (maponpaths
          (gquot_counit_map Y)
          (prealg_gquot_cell P (prealg_mor_inv P hf) z)
        @ prealg_counit_comp
            hY
            (poly_map P (gquot_functor_map (function_to_functor f)) z))
     @ maponpaths
         hY
         (poly_comp
            P (gquot_functor_map (function_to_functor f))
            (gquot_counit_map Y) z).
  Proof.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (!(maponpathscomp0 hY _ _)).
    }
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp _ (gquot_counit_map Y) _)).
      }
      exact (!(maponpathscomp0 (gquot_counit_map Y) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply (maponpathscomp0 (gquot_counit_map Y)).
    }
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply (maponpathscomp0 (gquot_counit_map Y)).
      }
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply (maponpathscomp hX f).
      }
      exact (homotsec_natural' (pr1 hf) (poly_path_groupoid_poly_map P z)).
    }
    etrans.
    {
      apply maponpaths_2 ; do 2 apply maponpaths.
      exact (!(maponpathscomp (poly_map P f) hY _)).
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (!(maponpathscomp0 hY _ _)).
    }
    pose (homotsec_natural'
             (λ q, gquot_counit_naturality
                     f
                     (gquot_functor_map
                        (prealg_path_groupoid_map P X hX)
                        q))
             (poly_gquot_is_gcl P z))
      as h.
    unfold funcomp in h.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        exact (maponpathscomp
                 (λ z0,
                  gquot_counit_map
                    X
                    (gquot_functor_map (prealg_path_groupoid_map P X hX) z0))
              f _).
      }
      refine (!(pathscomp0rid _) @ _).
      exact h.
    }
    clear h.
    refine (!(path_assoc _ _ _) @ _).
    do 3 refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp
                 (λ q, gquot_functor_map
                         (function_to_functor f)
                         (gquot_functor_map
                            (prealg_path_groupoid_map P X hX)
                            q))
                 (gquot_counit_map Y)
                 (poly_gquot_is_gcl P z))).
    }
    refine (!_).
    etrans.
    {
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply maponpaths_2.
      exact (!(maponpathscomp0 _ _ _)).
    }
    pose (homotsec_natural
            (prealg_gquot_help P (# path_groupoid f) (prealg_mor_inv P hf))
            (!(poly_gquot_is_gcl P z)))
      as h.
    etrans.
    {
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        exact h.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply path_assoc.
      }
      etrans.
      {
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        apply pathsinv0inv0.
      }
      apply maponpaths.
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths_2.
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths_2.
      apply gquot_rec_beta_gcleq.
    }
    clear h.
    do 2 refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    do 3 refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp0 _ _ _)).
      }
      exact (!(maponpathscomp0 _ _ _)).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (!(maponpathscomp
                   (λ z0,
                    (gquot_functor_map
                       (poly_act_functor
                          P (function_to_functor f)) z0))
                   (gquot_functor_map (prealg_path_groupoid_map P Y hY))
                   (! poly_gquot_is_gcl P z))).
      }
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp0 _ _ _)).
      }
      exact (!(maponpathscomp0 _ _ _)).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (prealg_counit_equation_lem₁ z).
        }
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp0 hY _ _)).
      }
      exact (!(maponpathscomp0 hY _ _)).
    }
    apply maponpaths.
    exact (prealg_counit_equation_lem₂ z).
  Qed.
    
  Definition prealg_counit
    : disp_pstrans
        (disp_pseudo_comp
           gquot_biadj_data
           gquot_psfunctor
           _
           _
           _
           (prealg_path_groupoid P)
           (prealg_gquot P))
        (disp_pseudo_id (disp_alg_bicat (⟦ P ⟧)))
        (biadj_counit gquot_biadj_data).
  Proof.
    use make_disp_pstrans.
    - apply disp_2cells_isaprop_alg.
    - apply disp_locally_groupoid_alg.
    - intros X hX.
      use make_invertible_2cell.
      + exact (prealg_counit_comp hX).
      + apply one_type_2cell_iso.
    - abstract
        (intros X Y f hX hY hf ;
         use funextsec ;
         intro z ;
         refine (maponpaths
                   (λ z, _ @ (z @ _))
                   (pathscomp0rid _
                    @ maponpaths
                        (λ z, z @ _)
                        (pathscomp0rid _))
                   @ _) ;
         refine (!_) ;      
         refine (maponpaths
                   (λ z, (z @ _) @ _)
                   (pathscomp0rid _
                    @ maponpaths (λ z, z @ _) (pathscomp0rid _))
                   @ _) ;
         refine (!(path_assoc _ _ _) @ _) ;
         refine (maponpaths
                   (λ z,
                    (maponpaths f (prealg_counit_comp hX _)
                     @ (pr1 hf (poly_map P (gquot_counit_map X) _)))
                     @ z)
                   (!(maponpathscomp0 hY _ _))
                   @ _
                ) ;
         exact (prealg_counit_equation hf z)).
  Defined.
End LiftCounit.
