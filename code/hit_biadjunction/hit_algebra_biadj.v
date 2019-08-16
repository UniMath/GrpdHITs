Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Invertible_2cells.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Adjunctions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.BicategoryLaws.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.OneTypes.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.CategoryTheory.Bicategories.PseudoFunctors.Display.Compositor.
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
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBiadjunction.

Require Import syntactical_signature.hit_signature.
Require Import prelude.basics.
Require Import prelude.cubical_methods.
Require Import prelude.constant.
Require Import prelude.grpd_bicat.
Require Import path_groupoid.path_groupoid.
Require Import path_groupoid.path_groupoid_commute.
Require Import semantic_signature.one_types_polynomials.
Require Import semantic_signature.groupoid_polynomials.
Require Import semantic_signature.one_types_endpoints.
Require Import semantic_signature.groupoid_endpoints.
Require Import biadjunction.disp_algebra.algebra_biadjunction.
Require Import biadjunction.disp_algebra.algebra_pseudofunctor.
Require Import biadjunction.disp_cat_biadjunction.
Require Import groupoid_quotient.gquot_biadjunction.
Require Import groupoid_quotient.gquot.
Require Import groupoid_quotient.gquot_principles.
Require Import groupoid_quotient.gquot_functor.
Require Import groupoid_quotient.gquot_commute.

Local Open Scope cat.

(** Lift of the unit *)
Definition ηη_comp
           (P : poly_code)
           {G : groupoid}
           (x : (⦃ P ⦄ G : groupoid))
  : gcl (poly_act_groupoid P G) x
    =
    (poly_gquot P G)
      (pr1 (poly_path_groupoid P (gquot_functor_obj G))
           (poly_map P (gcl G) x)).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths gquot_inl_grpd (IHP₁ x)).
    + exact (maponpaths gquot_inr_grpd (IHP₂ x)).
  - exact (maponpaths
             (λ z, gquot_prod_comp (pr1 z) (pr2 z))
             (pathsdirprod (IHP₁ (pr1 x))
                           (IHP₂ (pr2 x)))).
Defined.

Definition ηη_is_nat
           {P : poly_code}
           {G : groupoid}
           {x y : ⦃ P ⦄ G : groupoid}
           (f : (⦃ P ⦄ G : groupoid) ⟦ x, y ⟧)
  : gcleq (poly_act_groupoid P G) f @ ηη_comp P y
  =
  ηη_comp P x
  @ maponpaths
      ((poly_gquot P) G)
      (# ((poly_path_groupoid P) (gquot_functor_obj G) : _ ⟶ _)
         (poly_act_functor_morphisms
            P G (one_type_to_groupoid (gquot_functor_obj G))
            (gquot_unit_functor G) x y f)).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - cbn in *.
    induction f.
    refine (pathscomp0rid _ @ _).
    apply ge.
  - cbn in *.
    refine (pathscomp0rid _ @ !_).
    apply gquot_rec_beta_gcleq.
  - induction x as [x | x], y as [y | y].
    + clear IHP₂.
      specialize (IHP₁ x y f).
      simpl in * ; cbn in *.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          refine (maponpathscomp
                    inl
                    (gquot_sum_data_comp (poly_gquot P₁) (poly_gquot P₂) G) _
                    @ _).
          exact (!(maponpathscomp
                     (poly_gquot P₁ G)
                     gquot_inl_grpd _)).
        }
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        exact (!IHP₁).
      }
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths_2.
      apply gquot_rec_beta_gcleq.
    + exact (fromempty f).
    + exact (fromempty f).
    + clear IHP₁.
      specialize (IHP₂ x y f).
      simpl in * ; cbn in *.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          refine (maponpathscomp
                    inr
                    (gquot_sum_data_comp (poly_gquot P₁) (poly_gquot P₂) G) _
                    @ _).
          exact (!(maponpathscomp
                     (poly_gquot P₂ G)
                     gquot_inr_grpd _)).
        }
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        exact (!IHP₂).
      }
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths_2.
      apply gquot_rec_beta_gcleq.
  - refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        simpl.
        cbn.
        apply (maponpaths_pathsdirprod_precompose
                 gquot_prod_comp
                 (λ z, poly_gquot P₁ G z)
                 (λ z, poly_gquot P₂ G z)
              ).
      }
      refine (!(maponpathscomp0
                  (λ z, gquot_prod_comp (pr1 z) (pr2 z))
                  (pathsdirprod
                     (ηη_comp P₁ (pr1 x))
                     (ηη_comp P₂ (pr2 x)))
                  (pathsdirprod
                     _
                     _
               )) @ _).
      etrans.
      {
        apply maponpaths.
        refine (pathsdirprod_concat _ _ _ _ @ _).
        etrans.
        {
          exact (!(maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 x) (pr1 y) (pr1 f)))).
        }
        etrans.
        {
          exact (!(maponpaths (pathsdirprod _) (IHP₂ (pr2 x) (pr2 y) (pr2 f)))).
        }
        exact (!(pathsdirprod_concat _ _ _ _)).
      }
      exact (maponpathscomp0 (λ z, gquot_prod_comp (pr1 z) (pr2 z)) _ _).
    }
    refine (maponpaths (λ z, z @ _) _).
    etrans.
    {
      exact (uncurry_ap
               gquot_prod_comp
               (gcleq (poly_act_groupoid P₁ G) (pr1 f))
               (gcleq (poly_act_groupoid P₂ G) (pr2 f))).
    }
    etrans.
    {
      refine (maponpaths (λ z, z @ _) _).
      exact (gquot_double_rec'_beta_l_gcleq
               (poly_act_groupoid P₁ G)
               _ _ _ _ _ _ _ _ _ _ _ _ (pr1 f)).
    }
    etrans.
    {
      apply maponpaths.
      exact (gquot_double_rec'_beta_r_gcleq
               (poly_act_groupoid P₁ G)
               _ _ _ _ _ _ _ _ _ _ _ _ _).
    }
    refine (!(gconcat _ _ _) @ _).
    apply maponpaths.
    apply pathsdirprod.
    + apply poly_act_id_right.
    + apply poly_act_id_left.
Qed.

Definition ηη
           (P : poly_code)
  : lift_unit_type gquot_biadj_data (poly_gquot P) (poly_path_groupoid P).
Proof.
  intro G.
  use make_invertible_2cell.
  + use make_nat_trans.
    * exact (ηη_comp P).
    * intros x y f.
      exact (ηη_is_nat f).
  + apply grpd_bicat_is_invertible_2cell.
Defined.

(** Lemmata for lifting the counit *)
Definition gquot_counit_map_gquot_inl_grpd
           (P₁ P₂ : poly_code)
           (X : one_type)
  : ∏ (z : gquot (poly_act_groupoid P₁ (path_groupoid X))),
    gquot_counit_map
      ((⟦ P₁ + P₂ ⟧) X)
      (gquot_functor_map
         ((poly_path_groupoid (P₁ + P₂)) X)
         (gquot_inl_grpd z))
    =
    inl
      (gquot_counit_map
         ((⟦ P₁ ⟧) X)
         (gquot_functor_map
            ((poly_path_groupoid P₁) X)
            z)).
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ p;
       apply map_path_over;
       refine (pathscomp0rid _ @ _ @ !(pathscomp0lid _));
       refine (!(maponpathscomp
                   (λ z, gquot_functor_map
                           ((poly_path_groupoid (P₁ + P₂)) X)
                           (gquot_inl_grpd z))
                   (gquot_counit_map ((⟦ P₁ + P₂ ⟧) X))
                   (gcleq (poly_act_groupoid P₁ (path_groupoid X)) p)) @ _);
       refine (maponpaths
                 (maponpaths (gquot_counit_map ((⟦ P₁ + P₂ ⟧) X)))
                 (!(maponpathscomp
                      gquot_inl_grpd
                      (gquot_functor_map ((poly_path_groupoid (P₁ + P₂)) X))
                      (gcleq (poly_act_groupoid P₁ (path_groupoid X)) p)))
                 @ _);
       refine (maponpaths
                 (λ z, maponpaths _ (maponpaths _ z))
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (maponpaths
                 (λ z, maponpaths _ z)
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _);
       refine (!_);
       refine (!(maponpathscomp
                   (gquot_functor_map ((poly_path_groupoid P₁) X))
                   (λ z, inl(gquot_counit_map ((⟦ P₁ ⟧) X) z))
                   (gcleq (poly_act_groupoid P₁ (path_groupoid X)) p)) @ _);
       refine (!(maponpathscomp
                   (gquot_counit_map ((⟦ P₁ ⟧) X))
                   inl
                   _)
                @ _);
       refine (maponpaths
                 (λ z, maponpaths _ (maponpaths _ z))
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       exact (maponpaths
                (λ z, maponpaths _ z)
                (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))).
  - intro x.
    exact (one_type_isofhlevel _ _ _).
Defined.

Definition gquot_counit_map_gquot_inr_grpd
           (P₁ P₂ : poly_code)
           (X : one_type)
  : ∏ (z : gquot (poly_act_groupoid P₂ (path_groupoid X))),
    gquot_counit_map
      ((⟦ P₁ + P₂ ⟧) X)
      (gquot_functor_map
         ((poly_path_groupoid (P₁ + P₂)) X)
         (gquot_inr_grpd z))
    =
    inr
      (gquot_counit_map
         ((⟦ P₂ ⟧) X)
         (gquot_functor_map
            ((poly_path_groupoid P₂) X)
            z)).
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ p;
       apply map_path_over;
       refine (pathscomp0rid _ @ _ @ !(pathscomp0lid _));
       refine (!(maponpathscomp
                   (λ z, gquot_functor_map
                           ((poly_path_groupoid (P₁ + P₂)) X)
                           (gquot_inr_grpd z))
                   (gquot_counit_map ((⟦ P₁ + P₂ ⟧) X))
                   (gcleq (poly_act_groupoid P₂ (path_groupoid X)) p)) @ _);
       refine (maponpaths
                 (maponpaths (gquot_counit_map ((⟦ P₁ + P₂ ⟧) X)))
                 (!(maponpathscomp
                      gquot_inr_grpd
                      (gquot_functor_map ((poly_path_groupoid (P₁ + P₂)) X))
                      (gcleq (poly_act_groupoid P₂ (path_groupoid X)) p)))
                 @ _);
       refine (maponpaths
                 (λ z, maponpaths _ (maponpaths _ z))
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (maponpaths
                 (λ z, maponpaths _ z)
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _);
       refine (!_);
       refine (!(maponpathscomp
                   (gquot_functor_map ((poly_path_groupoid P₂) X))
                   (λ z, inr(gquot_counit_map ((⟦ P₂ ⟧) X) z))
                   (gcleq (poly_act_groupoid P₂ (path_groupoid X)) p)) @ _);
       refine (!(maponpathscomp
                   (gquot_counit_map ((⟦ P₂ ⟧) X))
                   inr
                   _)
                @ _);
       refine (maponpaths
                 (λ z, maponpaths _ (maponpaths _ z))
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       exact (maponpaths
                (λ z, maponpaths _ z)
                (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))).
  - intro x.
    exact (one_type_isofhlevel _ _ _).
Defined.

Definition gquot_counit_map_gquot_pair
           (P₁ P₂ : poly_code)
           (X : one_type)
  : ∏ (z₁ : gquot (poly_act_groupoid P₁ (path_groupoid X)))
      (z₂ : gquot (poly_act_groupoid P₂ (path_groupoid X))),
    gquot_counit_map
      ((⟦ P₁ * P₂ ⟧) X)
      (gquot_functor_map
         ((poly_path_groupoid (P₁ * P₂)) X)
         (gquot_prod_comp z₁ z₂))
    =
    make_dirprod
      (gquot_counit_map
         ((⟦ P₁ ⟧) X)
         (gquot_functor_map
            ((poly_path_groupoid P₁) X)
            z₁))
      (gquot_counit_map
         ((⟦ P₂ ⟧) X)
         (gquot_functor_map
            ((poly_path_groupoid P₂) X)
            z₂)).
Proof.
  use gquot_double_ind_set.
  - intros a b.
    exact (one_type_isofhlevel _ _ _).
  - intros a b.
    apply idpath.
  - abstract
      (intros a b₁ b₂ g;
       apply map_path_over;
       refine (pathscomp0rid _ @ _ @ !(pathscomp0lid _));
       refine (!(maponpathscomp
                   (λ z,
                    gquot_functor_map
                      ((poly_path_groupoid (P₁ * P₂)) X)
                      (gquot_prod_comp
                         (gcl (poly_act_groupoid P₁ (path_groupoid X)) a) z))
                   (gquot_counit_map ((⟦ P₁ * P₂ ⟧) X))
                   (gcleq (poly_act_groupoid P₂ (path_groupoid X)) g))
                @ _);
       refine (maponpaths
                 (maponpaths (gquot_counit_map _))
                 (!(maponpathscomp
                      _
                      _
                      _))
                 @ _);
       refine (maponpaths
                 (λ z, maponpaths _ (maponpaths _ z))
                 (gquot_double_rec'_beta_r_gcleq
                    _ (poly_act_groupoid P₂ (path_groupoid X))
                    _ _ _ _ _ _ _ _ _ _ _ g)
                 @ _);
       refine (maponpaths
                 (maponpaths _)
                 (gquot_rec_beta_gcleq
                    (poly_act_groupoid (P₁ * P₂) (path_groupoid X))
                    _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (gquot_rec_beta_gcleq
                 ((ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)) X)
                 _ _ _ _ _ _ _ _ _ @ _);
       refine (!_);
       refine (!(maponpathscomp
                   (gquot_functor_map ((poly_path_groupoid P₂) X))
                   (λ z,
                    make_dirprod
                      (gquot_counit_map
                         ((⟦ P₁ ⟧) X)
                         (gquot_functor_map
                            ((poly_path_groupoid P₁) X)
                            (gcl (poly_act_groupoid P₁ (path_groupoid X)) a)))
                      (gquot_counit_map ((⟦ P₂ ⟧) X) z))
                   (gcleq (poly_act_groupoid P₂ (path_groupoid X)) g))
                @ _);
       refine (!(maponpathscomp
                   (gquot_counit_map ((⟦ P₂ ⟧) X))
                   (λ z,
                    make_dirprod
                      (gquot_counit_map
                         ((⟦ P₁ ⟧) X)
                         (gquot_functor_map
                            ((poly_path_groupoid P₁) X)
                            (gcl (poly_act_groupoid P₁ (path_groupoid X)) a)))
                      z)
                   _)
                @ _);
       refine (maponpaths
                 (λ z, maponpaths _ (maponpaths _ z))
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (maponpaths
                 (maponpaths _)
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (maponpaths_make_dirprod_left _ _ @ _);
       refine (maponpaths (λ z, pathsdirprod z _) _);
       apply (!(pr12 (poly_path_groupoid P₁ X) _))).
  - abstract
      (intros a₁ a₂ b g;
       apply map_path_over;
       refine (pathscomp0rid _ @ _ @ !(pathscomp0lid _));
       refine (!(maponpathscomp
                   (λ z,
                    gquot_functor_map
                      ((poly_path_groupoid (P₁ * P₂)) X)
                      (gquot_prod_comp
                         z
                         (gcl (poly_act_groupoid P₂ (path_groupoid X)) b)))
                   (gquot_counit_map ((⟦ P₁ * P₂ ⟧) X))
                   (gcleq (poly_act_groupoid P₁ (path_groupoid X)) g))
                @ _);
       refine (maponpaths
                 (maponpaths (gquot_counit_map _))
                 (!(maponpathscomp
                      (λ z, gquot_prod_comp
                              z
                              (gcl (poly_act_groupoid P₂ (path_groupoid X)) b))
                      (gquot_functor_map ((poly_path_groupoid (P₁ * P₂)) X))
                      _))
                 @ _);
       refine (maponpaths
                 (λ z, maponpaths _ (maponpaths _ z))
                 (gquot_double_rec'_beta_l_gcleq
                    _ (poly_act_groupoid P₂ (path_groupoid X))
                    _ _ _ _ _ _ _ _ _ _ _ g)
                 @ _);
       refine (maponpaths
                 (maponpaths _)
                 (gquot_rec_beta_gcleq
                    (poly_act_groupoid (P₁ * P₂) (path_groupoid X))
                    _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (gquot_rec_beta_gcleq
                 ((ps_comp path_groupoid (⟦ P₁ * P₂ ⟧)) X)
                 _ _ _ _ _ _ _ _ _ @ _);
       refine (!_);
       refine (!(maponpathscomp
                   (gquot_functor_map ((poly_path_groupoid P₁) X))
                   (λ z,
                    make_dirprod
                      (gquot_counit_map ((⟦ P₁ ⟧) X) z)
                      (gquot_counit_map
                         ((⟦ P₂ ⟧) X)
                         (gquot_functor_map
                            ((poly_path_groupoid P₂) X)
                            (gcl (poly_act_groupoid P₂ (path_groupoid X)) b))))
                   (gcleq (poly_act_groupoid P₁ (path_groupoid X)) g))
                @ _);
       refine (!(maponpathscomp
                   (gquot_counit_map ((⟦ P₁ ⟧) X))
                   (λ z,
                    make_dirprod
                      z
                      (gquot_counit_map
                         ((⟦ P₂ ⟧) X)
                         (gquot_functor_map
                            ((poly_path_groupoid P₂) X)
                            (gcl (poly_act_groupoid P₂ (path_groupoid X)) b))))
                   _)
                @ _);
       refine (maponpaths
                 _
                 (maponpaths
                    _ (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)) @ _);
       refine (maponpaths
                 _
                 (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _);
       refine (maponpaths_make_dirprod_right _ _ @ _);
       simpl;
       apply maponpaths;
       apply (!(pr12 (poly_path_groupoid P₂ X) _))).
Defined.
  
(* Lift of the counit *)
Definition algebra_biadjunction_lift_counit_type_path
           (P : poly_code)
           {X : one_type}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : gquot_counit_map
      (⟦ P ⟧ X)
      (gquot_functor_map
         ((poly_path_groupoid P) X) ((poly_gquot P) (one_type_to_groupoid X) z))
    =
    poly_map P (gquot_counit_map X) z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (idpath z).
  - revert z.
    use gquot_ind_set.
    + exact idpath.
    + abstract
        (intros a₁ a₂ p ;
         induction p ;
         apply map_path_over ;
         unfold square ;
         rewrite ge ;
         apply idpath).
    + intro.
      exact (one_type_isofhlevel X _ _).
  - induction z as [z | z].
    + refine (_ @ maponpaths inl (IHP₁ z)).
      exact (gquot_counit_map_gquot_inl_grpd
               P₁ P₂ X
               (poly_gquot P₁ (one_type_to_groupoid X) z)).
    + refine (_ @ maponpaths inr (IHP₂ z)).
      exact (gquot_counit_map_gquot_inr_grpd
               P₁ P₂ X
               (poly_gquot P₂ (one_type_to_groupoid X) z)).
  - refine (_ @ pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
    exact (gquot_counit_map_gquot_pair
             P₁ P₂ X
             (poly_gquot P₁ (one_type_to_groupoid X) (pr1 z))
             (poly_gquot P₂ (one_type_to_groupoid X) (pr2 z))).
Defined.

Definition algebra_biadjunction_lift_counit_type
           (P : poly_code)
  : lift_counit_type gquot_biadj_data (poly_gquot P) (poly_path_groupoid P).
Proof.
  intro X.
  use make_invertible_2cell.
  + exact (algebra_biadjunction_lift_counit_type_path P).
  + apply one_type_2cell_iso.
Defined.

(** The naturality condition for the pseudotransformations *)
Definition TODO {A : UU} : A.
Admitted.

(** Lemmata *)
Section LiftUnitHelp.
  Local Arguments idpath {_ _}.
  Local Notation "'ap'" := maponpaths.
  Local Notation "'GQ₀'" := gquot_functor_obj.
  Local Notation "'GQ₁'" := gquot_functor_map.
  Local Notation "'GQ₂'" := gquot_functor_cell.
  Local Notation "'GQC'" := gquot_functor_composition.
  Local Notation "'PA₀'" := poly_act.
  Local Notation "'PA₁'" := poly_map.
  Local Notation "'PA₂'" := poly_act_nat_trans_data.
  Local Notation "'PAC'" := poly_act_functor_composition_data.
  
  Definition lift_unit_pstrans
             (P : poly_code)
             (x y : groupoid)
             (f : x ⟶ y)
             (z : poly_act P (pr1 x))
  : PA₁ P (GQ₁ f) (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))
    =
    pr1 ((poly_path_groupoid P) (GQ₀ y)) (PA₁ P (gcl y) (PA₁ P f z)).
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact idpath.
    - exact idpath.
    - induction z as [z | z].
      + exact (maponpaths inl (IHP₁ z)).
      + exact (maponpaths inr (IHP₂ z)).
    - apply pathsdirprod.
      + exact (IHP₁ (pr1 z)).
      + exact (IHP₂ (pr2 z)).
  Defined.    

  Definition lift_unit_pstrans_eq
             {P : poly_code}
             {x y : groupoid}
             (f : x ⟶ y)
             (z : poly_act P (pr1 x))
    : pr11
        (psnaturality_of (poly_path_groupoid P) (GQ₁ f))
        (PA₁ P (gcl x) z)
    @ # (pr1 ((poly_path_groupoid P) (GQ₀ y)))
          (poly_act_functor_composition_data
             P x (one_type_to_groupoid (gquot_functor_obj x))
             (one_type_to_groupoid (gquot_functor_obj y)) (gquot_unit_functor x)
             (function_to_functor (gquot_functor_map f)) z)
    @ # (pr1 ((poly_path_groupoid P) (gquot_functor_obj y)))
          (poly_act_nat_trans_data
             P x (one_type_to_groupoid (gquot_functor_obj y))
             (gquot_unit_functor x ∙ function_to_functor (gquot_functor_map f))
             (f ∙ gquot_unit_functor y) (gquot_unit_nat_trans x y f) z)
    =
    lift_unit_pstrans P x y f z
    @ # (pr1 ((poly_path_groupoid P) (gquot_functor_obj y)))
           (poly_act_functor_composition_data
              P x y (one_type_to_groupoid (gquot_functor_obj y)) f
              (gquot_unit_functor y) z).
  Proof.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (@idpath _ (@idpath _ z)).
    - apply idpath.
    - induction z as [z | z].
      + simpl.
        refine (_ @ maponpathscomp0 _ _ _).
        refine (maponpaths (λ z, _ @ z) (!(maponpathscomp0 _ _ _)) @ _).
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        apply (IHP₁ z).
      + simpl.
        refine (_ @ maponpathscomp0 _ _ _).
        refine (maponpaths (λ z, _ @ z) (!(maponpathscomp0 _ _ _)) @ _).
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        apply (IHP₂ z).
    - simpl.
      refine (_ @ !(pathsdirprod_concat _ _ _ _)).
      refine (maponpaths (λ z, _ @ z) (pathsdirprod_concat _ _ _ _) @ _).
      refine (pathsdirprod_concat _ _ _ _ @ _).
      etrans.
      {
        exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))).
      }
      exact (maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
  Qed.

  Local Definition lift_unit_help₁
        (P : poly_code)
        {x y : groupoid}
        (f : x ⟶ y)
        (xx : (⦃ P ⦄ x : groupoid) ⟶ x)
        (z : poly_act P (pr1 x))
    : ap
        (GQ₁ f ∘ GQ₁ xx)%functions (ηη_comp P z)
    @ GQC
        xx f
        ((poly_gquot P) x ((pr1 ((poly_path_groupoid P) (GQ₀ x)))
                             (PA₁ P (gcl x) z)))
      =
      ap (GQ₁ (xx ∙ f)) (ηη_comp P z).
  Proof.
    induction (ηη_comp P z).
    apply idpath.
  Qed.

  Local Definition lift_unit_help₂
        (P : poly_code)
        {x y : groupoid}
        {f : x ⟶ y}
        {xx : (⦃ P ⦄ x : groupoid) ⟶ x}
        {yy : (⦃ P ⦄ y : groupoid) ⟶ y}
        (ff : xx ∙ f ⟹ # ⦃ P ⦄ f ∙ yy)
        (z : poly_act P (pr1 x))
    : ap (GQ₁ (xx ∙ f)) (ηη_comp P z)
    @ GQ₂ ff ((poly_gquot P) x ((pr1 ((poly_path_groupoid P) (GQ₀ x))) (PA₁ P (gcl x) z)))
    =
    gcleq y (pr1 ff z) @ ap (GQ₁ (poly_act_functor P x y f ∙ yy)) (ηη_comp P z).
  Proof.
    induction (ηη_comp P z).
    exact (!(pathscomp0rid _)).
  Qed.
  
  Local Definition lift_unit_help₃
        (P : poly_code)
        {x y : groupoid}
        {f : x ⟶ y}
        {xx : (⦃ P ⦄ x : groupoid) ⟶ x}
        {yy : (⦃ P ⦄ y : groupoid) ⟶ y}
        (ff : xx ∙ f ⟹ # ⦃ P ⦄ f ∙ yy)
        (z : poly_act P (pr1 x))
    : ap (GQ₁ (poly_act_functor P x y f ∙ yy)) (ηη_comp P z)
    @ ! GQC (poly_act_functor P x y f) yy
            ((poly_gquot P) x ((pr1 ((poly_path_groupoid P) (GQ₀ x))) (PA₁ P (gcl x) z)))
    = ap (GQ₁ yy) (ap (GQ₁ (poly_act_functor P x y f)) (ηη_comp P z)).
  Proof.
    induction (ηη_comp P z).
    apply idpath.
  Qed.

  Local Definition psnaturality_PPG_help
        (P : poly_code)
        {X Y : one_type}
        (f : X → Y)
        (z : PA₀ P X)
    : PA₁ P f (pr1 (poly_path_groupoid P X) z)
      =
      pr1 (poly_path_groupoid P Y) (PA₁ P f z)
    := pr11 (psnaturality_of (poly_path_groupoid P) f) z.

  Local Definition psnaturality_PGQ_help
        (P : poly_code)
        {G₁ G₂ : groupoid}
        (F : G₁ ⟶ G₂)
        (z : PA₀ P (gquot G₁))
    : GQ₁ (poly_act_functor P G₁ G₂ F) ((poly_gquot P) G₁ z)
      =
      (poly_gquot P) G₂ (PA₁ P (GQ₁ F) z)
    := pr1 (psnaturality_of (poly_gquot P) F) z.

  Definition maponpaths_homot
             {A B : UU}
             {f g : A → B}
             (e : f ~ g)
             {a₁ a₂ : A}
             (p : a₁ = a₂)
    : ap f p = e a₁ @ ap g p @ !(e a₂).
  Proof.
    induction p.
    exact (!(pathsinv0r _)).
  Qed.

  Local Definition lift_unit_help₄
        (P : poly_code)
        {x y : groupoid}
        (f : x ⟶ y)
        (z : poly_act P (pr1 x))           
    : ap (GQ₁ (poly_act_functor P x y f))
         (ηη_comp P z)
    @ psnaturality_PGQ_help
        P f ((pr1 ((poly_path_groupoid P) (GQ₀ x))) (PA₁ P (gcl x) z))
    @ ap ((poly_gquot P) y) (lift_unit_pstrans P x y f z)
    =
    ηη_comp P (PA₁ P f z).
  Proof.
    (*
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact (@idpath _ (@idpath _ ((gcl (poly_act_groupoid (C A) y) z)))).
    - apply idpath.
    - induction z as [z | z].
      + refine (_ @ ap (ap gquot_inl_grpd) (IHP₁ z)).
        refine (!_).
        etrans.
        {
          refine (maponpathscomp0 _ _ _ @ _).
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          refine (maponpathscomp inl (gquot_sum (poly_gquot P₁) (poly_gquot P₂) y) _ @ _).
          exact (!(maponpathscomp (poly_gquot P₁ y)
                               (@gquot_inl_grpd P₁ P₂ _)
                               (lift_unit_pstrans P₁ x y f z))).
        }
        refine (path_assoc _ _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)). 
        apply maponpaths_2.
        refine (path_assoc
                  _
                  (gquot_inl_grpd_gquot_functor
                     f
                     (poly_gquot
                        P₁
                        x
                        (pr11 ((poly_path_groupoid P₁) (GQ₀ x))
                              (PA₁ P₁ (gcl x) z))))
                  (ap gquot_inl_grpd
                      (psnaturality_PGQ_help
                         P₁
                         f
                         _))
                  @ _).
        apply maponpaths_2.
        simpl.
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (maponpathscomp
                   gquot_inl_grpd
                   (GQ₁ (poly_act_functor (P₁ + P₂) x y f))
                   (ηη_comp P₁ z)).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths_homot (gquot_inl_grpd_gquot_functor f) (ηη_comp P₁ z)).
        }
        simpl.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(maponpathscomp
                     (λ z0, GQ₁ (poly_act_functor P₁ x y f) z0)
                     gquot_inl_grpd
                     (ηη_comp P₁ z))).
        }
        refine (_ @ pathscomp0rid _).
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
      + refine (_ @ ap (ap gquot_inr_grpd) (IHP₂ z)).
        refine (!_).
        etrans.
        {
          refine (maponpathscomp0 _ _ _ @ _).
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (!_).
        etrans.
        {
          do 2 apply maponpaths.
          refine (maponpathscomp inr (gquot_sum (poly_gquot P₁) (poly_gquot P₂) y) _ @ _).
          exact (!(maponpathscomp (poly_gquot P₂ y)
                                  (@gquot_inr_grpd P₁ P₂ _)
                                  (lift_unit_pstrans P₂ x y f z))).
        }
        refine (path_assoc _ _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)). 
        apply maponpaths_2.
        refine (path_assoc
                  _
                  (gquot_inr_grpd_gquot_functor
                     f
                     (poly_gquot
                        P₂
                        x
                        (pr11 ((poly_path_groupoid P₂) (GQ₀ x))
                              (PA₁ P₂ (gcl x) z))))
                  (ap gquot_inr_grpd
                      (psnaturality_PGQ_help
                         P₂
                         f
                         _))
                  @ _).
        apply maponpaths_2.
        simpl.
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (maponpathscomp
                   gquot_inr_grpd
                   (GQ₁ (poly_act_functor (P₁ + P₂) x y f))
                   (ηη_comp P₂ z)).
        }
        etrans.
        {
          apply maponpaths_2.
          exact (maponpaths_homot (gquot_inr_grpd_gquot_functor f) (ηη_comp P₂ z)).
        }
        simpl.
        etrans.
        {
          do 2 apply maponpaths_2.
          exact (!(maponpathscomp
                     (λ z0, GQ₁ (poly_act_functor P₂ x y f) z0)
                     gquot_inr_grpd
                     (ηη_comp P₂ z))).
        }
        refine (_ @ pathscomp0rid _).
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        apply pathsinv0l.
    - refine (!_).
      etrans.
      {
        exact (ap (λ l, ap (λ z, gquot_prod_comp (pr1 z) (pr2 z))
                           (pathsdirprod
                              l
                              (ηη_comp P₂ (PA₁ P₂ f (pr2 z)))))
                  (!(IHP₁ (pr1 z)))).
      }
      etrans.
      {
        exact (ap (λ r, ap (λ z, gquot_prod_comp (pr1 z) (pr2 z))
                           (pathsdirprod
                              (ap (GQ₁ (poly_act_functor P₁ x y f)) (ηη_comp P₁ (pr1 z)) @
                                  psnaturality_PGQ_help P₁ f
                                  ((pr1 ((poly_path_groupoid P₁) (GQ₀ x))) (PA₁ P₁ (gcl x) (pr1 z))) @
                                  ap ((poly_gquot P₁) y) (lift_unit_pstrans P₁ x y f (pr1 z)))
                              r))
                  (!(IHP₂ (pr2 z)))).
      }*)
      apply TODO.
  Qed.
             
  Definition algebra_biadjunction_lift_unit_pstrans_nat_lem
             (P : poly_code)
             {x y : groupoid}
             {f : x ⟶ y}
             {xx : (⦃ P ⦄ x : groupoid) ⟶ x}
             {yy : (⦃ P ⦄ y : groupoid) ⟶ y}
             (ff : xx ∙ f ⟹ # ⦃ P ⦄ f ∙ yy)
             (z : poly_act P (pr1 x))
    : (gcleq y (pr1 ff z)
    @ ap (GQ₁ yy) (ηη_comp P (PA₁ P f z)))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (# (pr1 ((poly_path_groupoid P) (GQ₀ y)))
            (PAC P x y (one_type_to_groupoid (GQ₀ y)) f (gquot_unit_functor y) z))
    =
    ((ap (GQ₁ f) (ap (GQ₁ xx) (ηη_comp P z))
    @ (((GQC xx f
             (poly_gquot P x (pr1 ((poly_path_groupoid P) (GQ₀ x))
                                  (PA₁ P (gcl x) z)))
    @ GQ₂ ff (poly_gquot P x
                         (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))))
    @ ! GQC (poly_act_functor P x y f) yy
            ((poly_gquot P) x (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))))
    @ ap (GQ₁ yy)
         (psnaturality_PGQ_help
            P f
            (pr1 ((poly_path_groupoid P) (GQ₀ x)) (PA₁ P (gcl x) z))))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (psnaturality_PPG_help P (GQ₁ f) (PA₁ P (gcl x) z)))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (# (pr1 ((poly_path_groupoid P) (GQ₀ y)))
            (PAC P x (one_type_to_groupoid (GQ₀ x)) (one_type_to_groupoid (GQ₀ y))
                 (gquot_unit_functor x) (function_to_functor (GQ₁ f)) z)))
    @ ap (λ x0, GQ₁ yy ((poly_gquot P) y x0))
         (# (pr1 ((poly_path_groupoid P) (GQ₀ y)))
            (PA₂ P x (one_type_to_groupoid (GQ₀ y))
                 (gquot_unit_functor x ∙ function_to_functor (GQ₁ f))
                 (f ∙ gquot_unit_functor y)
                 (gquot_unit_nat_trans x y f) z)).
  Proof.
    refine (!_).
    etrans.
    {
      do 2 refine (!(path_assoc _ _ _) @ _).  
      apply maponpaths.
      do 4 refine (!(path_assoc _ _ _) @ _).
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp0
                    (λ w : PA₀ P (gquot y), GQ₁ yy ((poly_gquot P) y w))
                    _ _)).
      }
      exact (!(maponpathscomp0
                    (λ w : PA₀ P (gquot y), GQ₁ yy ((poly_gquot P) y w))
                    _ _)).
    }
    etrans.
    {
      do 5 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (lift_unit_pstrans_eq f z).
      }
      exact ((maponpathscomp0
                 (λ w : PA₀ P (gquot y), GQ₁ yy ((poly_gquot P) y w))
                 _ _)).
    }
    do 5 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    do 4 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp ((poly_gquot P) y) (GQ₁ yy) _)).
      }
      exact (!(maponpathscomp0 (GQ₁ yy) _ _)).
    }
    do 3 refine (path_assoc _ _ _ @ _).
    etrans.
    {
      do 3 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp (GQ₁ xx) (GQ₁ f) (ηη_comp P z)).
      }
      exact (lift_unit_help₁ P f xx z).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (lift_unit_help₂ P ff z).
    }
    do 2 refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (lift_unit_help₃ P ff z).
    }
    etrans.
    {
      exact (!(maponpathscomp0
                 (GQ₁ yy)
                 (ap (GQ₁ (poly_act_functor P x y f)) (ηη_comp P z))
                 _)).
    }
    apply maponpaths.
    exact (lift_unit_help₄ P f z).
  Qed.

  Definition algebra_biadjunction_lift_unit_pstrans_nat
             (P : poly_code)
    : algebra_lift_pstrans_nat
        (unit_of_lifted_biadj
           gquot_biadj_data (poly_gquot P) (poly_path_groupoid P)
           (ηη P)).
  Proof.
    intros x y f xx yy ff.
    use nat_trans_eq.
    { apply homset_property. }
    intro z.
    Transparent ps_comp.
    simpl.
    cbn.
    unfold homotcomp, funhomotsec, invhomot, homotfun.
    cbn.
    rewrite !pathscomp0rid.
    exact (algebra_biadjunction_lift_unit_pstrans_nat_lem P (pr1 ff) z).
  Qed.
End LiftUnitHelp.

Definition algebra_biadjunction_lift_counit_pstrans_nat
           (P : poly_code)
  : algebra_lift_pstrans_nat
      (counit_of_lifted_biadj
         gquot_biadj_data (poly_gquot P) (poly_path_groupoid P)
         (algebra_biadjunction_lift_counit_type P)).
Proof.
  apply TODO.
Qed.

(* ALSO TODO: MODIFICATIONS *)
Definition algebra_biadjunction
           (P : poly_code)
  : disp_left_biadj_data
      (disp_alg_bicat ⦃ P ⦄)
      (disp_alg_bicat (⟦ P ⟧))
      gquot_biadj_data
      (disp_alg_psfunctor _ (poly_gquot P)).
Proof.
  use lift_algebra_biadjunction.
  - exact (poly_path_groupoid P).
  - exact (algebra_biadjunction_lift_unit_type P).
  - exact (algebra_biadjunction_lift_unit_pstrans_nat P).
  - exact (algebra_biadjunction_lift_counit_type P).
  - exact (algebra_biadjunction_lift_counit_pstrans_nat P).
Defined.

Definition test2
           {P : poly_code}
           (X : one_type)
           (x : poly_act P X)
  : pr1 (poly_path_groupoid P X) x = x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (idpath x).
  - exact (idpath x).
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x)).
    + exact (maponpaths inr (IHP₂ x)).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Defined.

Definition test3
           {A S : poly_code}
           (e : endpoint A S I)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (x : poly_act S (pr1 X : one_type))
  : pr1
      (sem_endpoint_grpd
         e
         (total_psfunctor
            _ _ path_groupoid
            (disp_alg_psfunctor path_groupoid (poly_path_groupoid A)) X)) x
    =
    (sem_endpoint_one_types e) X x.
Proof.
  induction e ; try reflexivity.
  - admit.
  - admit.
  - apply (maponpaths (pr2 X)).
    exact (test2 (pr1 X) x).
Admitted.

Definition yolo
           (P : poly_code)
           (X : one_type)
           {x y : poly_act P X}
           (q : poly_act_morphism P (one_type_to_groupoid X) x y)
  : x = y.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact q.
  - exact q.
  - induction x as [x | x], y as [y | y].
    + exact (maponpaths inl (IHP₁ x y q)).
    + exact (fromempty q).
    + exact (fromempty q).
    + exact (maponpaths inr (IHP₂ x y q)).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 q)) (IHP₂ _ _ (pr2 q))).
Defined.

Section Wf.
  Context {A S : poly_code}
          (l r : endpoint A S I).
  
  Local Notation "'D1'" := (add_cell_disp_cat
                              (disp_alg_bicat (⦃ A ⦄))
                              (⦃ S ⦄)
                              (⦃ I ⦄)
                              (sem_endpoint_grpd l)
                              (sem_endpoint_grpd r)).

  Local Notation "'D2'" := (add_cell_disp_cat
                              (disp_alg_bicat (⟦ A ⟧))
                              (⟦ S ⟧)
                              (⟦ I ⟧)
                              (sem_endpoint_one_types l)
                              (sem_endpoint_one_types r)).

  Definition test
    : disp_psfunctor
        D2
        D1
        (total_psfunctor _ _ _ (disp_alg_psfunctor _ (poly_path_groupoid A))).
  Proof.
    use disp_cell_unit_psfunctor.
    - intros X p.
      use make_nat_trans.
      + exact (λ x, test3 l x @ p x @ !(test3 r x)).
      + (* intros x y q.
        simpl in q.
        cbn.
        pose (@apd _ _ p x y (yolo _ _ q)) as p0. *)
        apply TODO.
    - intros x y f xx yy ff.
      simpl.
      use nat_trans_eq.
      { admit. }
      intro z.
      cbn.
      simpl in z.
      simpl in ff.
      cbn in ff.
      pose (eqtohomot ff z) as p.
      unfold homotcomp, homotfun, funhomotsec in p.
      cbn in xx, yy.
      unfold homotsec in xx, yy.
      cbn in p.
      simpl in p.
      admit.
  Admitted.

  Definition test_alt
    : disp_psfunctor
        D1
        D2
        (total_psfunctor _ _ _ (disp_alg_psfunctor _ (poly_gquot A))).
  Proof.
    use disp_cell_unit_psfunctor.
    - intros X p x.
      pose (λ z, pr1 p z) as a.
      simpl in a, x.
      refine (_ @ pr1 
      pose (λ z, pr1 p z) as q.
      simpl in *.
      cbn in q.
      cbn in n.
      Check (p x).
