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
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
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
Require Import hit_biadjunction.gquot_natural.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import biadjunctions.all.
Require Import hit_biadjunction.hit_prealgebra_biadj_unit_counit.

Local Open Scope cat.

Definition poly_part_of_left_triangle
           {P : poly_code}
           {G : grpd_bicat}
           (z : poly_act P (gquot G))
  : (pr1 ((pr111 (poly_path_groupoid P)) (gquot_functor_obj G)))
      (poly_map
         P (gquot_counit_map (gquot_functor_obj G))
         (poly_map
            P (λ x, x)
            (poly_map
               P (gquot_functor_map (gquot_unit G))
               (poly_map P (λ x, x) z))))
    =
    z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + abstract
        (intros a₁ a₂ g ;
         use map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   (!(maponpaths
                        (maponpaths _)
                        (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                      @ _)
                      @ maponpathscomp
                          (gquot_functor_map (gquot_unit G))
                          (gquot_counit_map _)
                          (gcleq G g))
                   (!(maponpathsidfun _))
                   (idpath _)
                   (vrefl _)) ;
         apply gquot_rec_beta_gcleq).
    + exact (λ _, gtrunc _ _ _).
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ _) (IHP₂ _)).
Defined.

Local Definition step₁
      {P : poly_code}
      {G : grpd_bicat}
      (z : poly_act P (gquot G))
  : poly_path_groupoid_poly_map
      P
      (poly_map
         P (λ x, x)
         (poly_map
            P (gquot_functor_map (gquot_unit G))
            (poly_map P (λ x, x) z)))
  @ poly_id
      P (gquot G)
      (poly_map
         P (gquot_counit_map (gquot_functor_obj G))
         (poly_map
            P (λ x, x)
            (poly_map
               P (gquot_functor_map (gquot_unit G))
               (poly_map P (λ x, x) z))))
  @ poly_comp
      P (gquot_counit_map (gquot_functor_obj G)) (λ x, x)
      (poly_map
         P (λ x, x)
         (poly_map
            P (gquot_functor_map (gquot_unit G))
            (poly_map P (λ x, x) z)))
  @ poly_comp
      P (λ x, x) (λ x, gquot_counit_map (gquot_functor_obj G) x)
      (poly_map
         P (gquot_functor_map (gquot_unit G))
         (poly_map
            P (λ x, x) z))
  @ poly_comp
      P (gquot_functor_map (gquot_unit G))
      (λ x, gquot_counit_map (gquot_functor_obj G) x)
      (poly_map P (λ x, x) z)
  @ poly_comp
      P (λ x, x)
      (λ x,
       gquot_counit_map
         (gquot_functor_obj G)
         (gquot_functor_map (gquot_unit G) x))
      z
  @ poly_homot P (gquot_biadj_triangle_l_data_cell G) z
  =
  poly_part_of_left_triangle z
  @ poly_id P (gquot G) z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_prop.
    + exact (λ _, idpath _).
    + exact (λ _, gtrunc _ _ _ _ _).
  - induction z as [z | z].
    + clear IHP₂ ; specialize (IHP₁ z).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                exact (!(maponpathscomp0
                           inl
                           (poly_comp
                              P₁ (λ x, x)
                              (λ x,
                               gquot_counit_map
                                 (gquot_functor_obj G)
                                 (gquot_functor_map (gquot_unit G) x))
                              z)
                           (poly_homot P₁ (gquot_biadj_triangle_l_data_cell G) z))).
              }
              exact (!(maponpathscomp0 inl _ _)).
            }
            exact (!(maponpathscomp0 inl _ _)).
          }
          exact (!(maponpathscomp0 inl _ _)).
        }
        exact (!(maponpathscomp0 inl _ _)).
      }
      etrans.
      {
        exact (!(maponpathscomp0 inl _ _)).
      }
      refine (_ @ maponpathscomp0 inl _ _).
      refine (maponpaths (maponpaths inl) _).
      exact IHP₁.
    + clear IHP₁ ; specialize (IHP₂ z).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              etrans.
              {
                apply maponpaths.
                exact (!(maponpathscomp0
                           inr
                           (poly_comp
                              P₂ (λ x, x)
                              (λ x,
                               gquot_counit_map
                                 (gquot_functor_obj G)
                                 (gquot_functor_map (gquot_unit G) x))
                              z)
                           (poly_homot P₂ (gquot_biadj_triangle_l_data_cell G) z))).
              }
              exact (!(maponpathscomp0 inr _ _)).
            }
            exact (!(maponpathscomp0 inr _ _)).
          }
          exact (!(maponpathscomp0 inr _ _)).
        }
        exact (!(maponpathscomp0 inr _ _)).
      }
      etrans.
      {
        exact (!(maponpathscomp0 inr _ _)).
      }
      refine (_ @ maponpathscomp0 inr _ _).
      refine (maponpaths (maponpaths inr) _).
      exact IHP₂.
  - etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
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
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply pathsdirprod_concat.
    }
    refine (_ @ !(pathsdirprod_concat _ _ _ _)).
    exact (maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
           @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
Qed.

Definition left_triangle_help_lem
           {P : poly_code}
           {G : grpd_bicat}
           {a₁ a₂ : poly_act_groupoid P G}
           (g : poly_act_groupoid P G ⟦ a₁, a₂ ⟧)
  : ! prealg_unit_comp_help P a₁ @ gcleq (poly_act_groupoid P G) g
    =
    maponpaths
      ((poly_gquot P) G)
      (# ((poly_path_groupoid P) (gquot_functor_obj G) : _ ⟶ _)
         (# (@poly_act_functor
               P G (one_type_to_groupoid (gquot_functor_obj G))
               (gquot_unit_functor G)) g))
    @ ! prealg_unit_comp_help P a₂.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - induction g.
    apply ge.
  - exact (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _) @ !(pathscomp0rid _)).
  - induction a₁ as [a₁ | a₁], a₂ as [a₂ | a₂].
    + clear IHP₂ ; specialize (IHP₁ a₁ a₂ g).
      refine (_ @ maponpaths (maponpaths gquot_inl_grpd) IHP₁ @ _).
      * refine (_ @ !(maponpathscomp0 _ _ _)).
        etrans.
        {
          apply maponpaths_2.
          exact (!(maponpathsinv0
                     gquot_inl_grpd
                     (prealg_unit_comp_help P₁ a₁))).
        }
        apply maponpaths.
        exact (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)).
      * refine (maponpathscomp0 _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply maponpathsinv0.
        }
        apply maponpaths_2.
        refine (!_).
        apply maponpaths_sum_gquot_inl.
    + exact (fromempty g).
    + exact (fromempty g).
    + clear IHP₁ ; specialize (IHP₂ a₁ a₂ g).
      refine (_ @ maponpaths (maponpaths gquot_inr_grpd) IHP₂ @ _).
      * refine (_ @ !(maponpathscomp0 _ _ _)).
        etrans.
        {
          apply maponpaths_2.
          exact (!(maponpathsinv0
                     gquot_inr_grpd
                     (prealg_unit_comp_help P₂ a₁))).
        }
        apply maponpaths.
        exact (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)).
      * refine (maponpathscomp0 _ _ _ @ _).
        etrans.
        {
          apply maponpaths.
          apply maponpathsinv0.
        }
        apply maponpaths_2.
        refine (!_).
        apply maponpaths_sum_gquot_inr.
  - specialize (IHP₁ _ _ (pr1 g)).
    specialize (IHP₂ _ _ (pr2 g)).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathsinv0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (prealg_unit_comp_help P₁ (pr1 a₂))
                    (prealg_unit_comp_help P₂ (pr2 a₂))))).
    }
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp
                 (dirprodf (poly_gquot P₁ G) (poly_gquot P₂ G))
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 _)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      exact (!(maponpaths_pathsdirprod _ _ _ _)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply pathsdirprod_inv.
    }
    etrans.
    {
      exact (!(maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (maponpaths
                       ((poly_gquot P₁) G)
                       (# (pr1 ((poly_path_groupoid P₁)
                                  (gquot_functor_obj G)))
                          (@poly_act_functor_morphisms
                             P₁ G (one_type_to_groupoid (gquot_functor_obj G))
                             (gquot_unit_functor G)
                             (pr1 a₁) (pr1 a₂) (pr1 g))))
                    (maponpaths
                       ((poly_gquot P₂) G)
                       (# (pr1 ((poly_path_groupoid P₂) (gquot_functor_obj G)))
                          (@poly_act_functor_morphisms
                             P₂ G (one_type_to_groupoid (gquot_functor_obj G))
                             (gquot_unit_functor G)
                             (pr2 a₁) (pr2 a₂) (pr2 g)))))
                 (pathsdirprod
                    (! prealg_unit_comp_help P₁ (pr1 a₂))
                    (! prealg_unit_comp_help P₂ (pr2 a₂))))).
    }
    etrans.
    {
      apply maponpaths.
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!IHP₂).
      }
      apply maponpaths_2.
      exact (!IHP₁).
    }
    etrans.
    {
      apply maponpaths.
      exact (!(pathsdirprod_concat _ _ _ _)).
    }    
    etrans.
    {
      exact (maponpathscomp0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod _ _)
               (pathsdirprod
                  (gcleq (poly_act_groupoid P₁ G) (pr1 g))
                  (gcleq (poly_act_groupoid P₂ G) (pr2 g)))).
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (!(pathsdirprod_inv _ _)).
      }
      exact (maponpathsinv0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod _ _)).
    }    
    apply maponpaths.
    pose (uncurry_ap
            prod_gquot_comp
            (gcleq (poly_act_groupoid P₁ G) (pr1 g))
            (gcleq (poly_act_groupoid P₂ G) (pr2 g)))
      as h.
    unfold uncurry in h.
    refine (h @ _).
    etrans.
    {
      apply maponpaths.
      exact (gquot_double_rec'_beta_r_gcleq _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      apply maponpaths_2.
      exact (gquot_double_rec'_beta_l_gcleq _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    }
    refine (!(gconcat _ _ _) @ _).
    apply maponpaths.
    exact (pathsdirprod
             (poly_act_id_right _)
             (poly_act_id_left _)).
Qed.

Definition left_triangle_help_square
           {P : poly_code}
           {G : grpd_bicat}
           (hG : (disp_alg_bicat ⦃ P ⦄) G)
           {a₁ a₂ : poly_act_groupoid P G}
           (g : poly_act_groupoid P G ⟦ a₁, a₂ ⟧)
  : square
      (! maponpaths
           (gquot_counit_map (gquot_functor_obj G))
           (gcleq
              (one_type_to_groupoid (gquot_functor_obj G))
              (prealg_unit_nat_trans_comp P hG a₂)))
      (maponpaths
         (λ z,
          gquot_counit_map
            (gquot_functor_obj G)
            (gquot_functor_map
               (prealg_path_groupoid_map
                  P (gquot_functor_obj G) (prealg_gquot_map P G hG))
               (gquot_functor_map
                  (@poly_act_functor
                     P G (one_type_to_groupoid (gquot_functor_obj G))
                     (gquot_unit_functor G))
                  z)))
         (gcleq (poly_act_groupoid P G) g))
      (maponpaths (gquot_functor_map hG) (gcleq (poly_act_groupoid P G) g))
      (! maponpaths
           (gquot_counit_map (gquot_functor_obj G))
           (gcleq (one_type_to_groupoid (gquot_functor_obj G))
                  (prealg_unit_nat_trans_comp P hG a₁))).
Proof.
  refine (whisker_square
            (maponpaths
               (λ z, ! z)
               (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)))
            _
            (idpath _)
            (maponpaths
               (λ z, ! z)
               (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)))
            _).
  - refine (_ @ maponpathscomp
              (λ z,
               gquot_functor_map
                 (prealg_path_groupoid_map
                    P (gquot_functor_obj G) (prealg_gquot_map P G hG))
                 (gquot_functor_map
                    (@poly_act_functor
                       P G
                       (one_type_to_groupoid (gquot_functor_obj G))
                       (gquot_unit_functor G)) z))
              (gquot_counit_map (gquot_functor_obj G))
              (gcleq (poly_act_groupoid P G) g)).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        exact (!(maponpathscomp _ _ _)).
      }
      etrans.
      {
        apply maponpaths.
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp
                 (poly_gquot P G)
                 (gquot_functor_map hG)
                 _)).
    }
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathsinv0 (gquot_functor_map hG) (prealg_unit_comp_help P a₂))).
    }
    etrans.
    {
      refine (!_).
      exact (maponpathscomp0
               (gquot_functor_map hG)
               _
               (! prealg_unit_comp_help P a₂)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathsinv0 (gquot_functor_map hG) (prealg_unit_comp_help P a₁))).
    }
    etrans.
    {
      refine (!_).
      exact (maponpathscomp0
               (gquot_functor_map hG)
               (! prealg_unit_comp_help P a₁)
               (gcleq (poly_act_groupoid P G) g)).
    }
    apply maponpaths.
    exact (left_triangle_help_lem g).
Qed.

Definition left_triangle_help
           {P : poly_code}
           {G : grpd_bicat}
           (hG : (disp_alg_bicat ⦃ P ⦄) G)
  : ∏ (z : gquot (poly_act_groupoid P G)),
    gquot_counit_map
      (gquot_functor_obj G)
      (gquot_functor_map
         (prealg_path_groupoid_map
            P (gquot_functor_obj G)
            (prealg_gquot_map P G hG))
         (gquot_functor_map
            (@poly_act_functor
               P G
               (one_type_to_groupoid (gquot_functor_obj G))
               (gquot_unit_functor G))
            z))
    =
    gquot_functor_map hG z.
Proof.
  use gquot_ind_set.
  - exact (λ a, !(maponpaths
                    (gquot_counit_map (gquot_functor_obj G))
                    (gcleq (one_type_to_groupoid (gquot_functor_obj G))
                           (prealg_unit_nat_trans_comp P hG a)))).
  - abstract
      (intros a₁ a₂ g ;
       use map_PathOver ; simpl ;
       exact (left_triangle_help_square hG g)).
  - exact (λ _, gtrunc _ _ _).
Defined.  

Definition step₂
           {P : poly_code}
           {G : grpd_bicat}
           (hG : (disp_alg_bicat ⦃ P ⦄) G)
  : ∏ (z : gquot (poly_act_groupoid P G)),
    maponpaths
      (gquot_counit_map (gquot_functor_obj G))
      (prealg_gquot_help
         P (gquot_unit G)
         (make_invertible_2cell
            (grpd_bicat_is_invertible_2cell (prealg_unit_nat_trans P hG)))
         z)
    @ left_triangle_help hG z
    =
    gquot_biadj_triangle_l_data_cell
      G (gquot_functor_map hG z).
Proof.
  use gquot_ind_prop.
  - intro a.
    simpl.
    apply pathsinv0r.
  - exact (λ _, gtrunc _ _ _ _ _).
Qed.

Local Definition step₃_help
      {P : poly_code}
      {G : grpd_bicat}
      (z : poly_act P (gquot G))
  : gquot_functor_map
      (@poly_act_functor
         P G
         (one_type_to_groupoid (gquot_functor_obj G)) (gquot_unit_functor G))
      ((poly_gquot P) G z)
    =
    gcl (poly_act_groupoid P (one_type_to_groupoid (gquot_functor_obj G)))
        (poly_map
           P (gquot_counit_map (gquot_functor_obj G))
           (poly_map
              P (λ x, x)
              (poly_map P (gquot_functor_map (gquot_unit G))
                        (poly_map P (λ x, x) z)))).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + intro.
      apply idpath.
    + abstract
        (intros a₁ a₂ g ;
         apply map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   (!(maponpaths
                        (maponpaths _)
                        _
                        @ _)
                      @ maponpathscomp _ _ _)
                   (!(maponpaths
                        (maponpaths _)
                        (_ @ _))
                      @ maponpathscomp _ _ _)
                   (idpath _)
                   _) ;
         [ exact (gquot_rec_beta_gcleq G _ _ _ _ _ _ _ _ g)
         | exact (gquot_rec_beta_gcleq
                    (poly_act_groupoid I G)
                    _ _ _ _ _ _ _ _ g)
         | exact (!(maponpathscomp (gquot_functor_map _) (gquot_counit_map _) _))
         | refine (maponpaths
                  (maponpaths _)
                  (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                @ _) ;
           apply gquot_rec_beta_gcleq
         | refine (pathscomp0rid _ @ _) ;
           simpl ;
           induction (gcleq G g) ;
           exact (ge _ _) ]).
    + exact (λ _, gtrunc _ _ _).
  - induction z as [z | z].
    + refine (_ @ maponpaths gquot_inl_grpd (IHP₁ z)).
      pose (@gquot_inl_grpd_gquot_functor
              P₁ P₂
              _ _
              (gquot_unit G)
              (poly_gquot P₁ G z)
           )
        as h.
      simpl in h.
      exact h.
    + refine (_ @ maponpaths gquot_inr_grpd (IHP₂ z)).
      pose (@gquot_inr_grpd_gquot_functor
              P₁ P₂
              _ _
              (gquot_unit G)
              (poly_gquot P₂ G z)
           )
        as h.
      simpl in h.
      exact h.
  - etrans.
    {
      exact (prod_gquot_data_comp_nat_help
               _ _
               (gquot_unit G)
               ((poly_gquot P₁) G (pr1 z))
               ((poly_gquot P₂) G (pr2 z))).
    }
    exact (maponpaths
             (λ z, prod_gquot_comp z _)
             (IHP₁ (pr1 z))
           @ maponpaths
               (prod_gquot_comp _)
               (IHP₂ (pr2 z))).
Defined.

Definition step₃_prod
           {P₁ P₂ : poly_code}
           {G : grpd_bicat}
           (z : poly_act (P₁ * P₂) (gquot G))
           (IHP₁ : pr1 (psnaturality_of (poly_gquot P₁) (gquot_unit G)) (pr1 z)
                 @ maponpaths
                     (λ x,
                      (poly_gquot P₁)
                        (one_type_to_groupoid (gquot_functor_obj G))
                        (poly_map P₁ (gquot_functor_map (gquot_unit G)) x))
                     (poly_id P₁ (gquot G) (pr1 z))
                 @ maponpaths
                     ((poly_gquot P₁) (one_type_to_groupoid (gquot_functor_obj G)))
                     (poly_id
                        P₁ (gquot (one_type_to_groupoid (gquot_functor_obj G)))
                        (poly_map
                           P₁ (gquot_functor_map (gquot_unit G))
                           (poly_map P₁ (λ x, x) (pr1 z))))
                 @ poly_gquot_is_gcl P₁
                     (poly_map
                        P₁
                        (λ x, x)
                        (poly_map
                           P₁ (gquot_functor_map (gquot_unit G))
                           (poly_map P₁ (λ x, x) (pr1 z))))
                   =
                   step₃_help (pr1 z))
           (IHP₂ : pr1 (psnaturality_of (poly_gquot P₂) (gquot_unit G)) (pr2 z)
                 @ maponpaths
                     (λ x,
                      (poly_gquot P₂)
                        (one_type_to_groupoid (gquot_functor_obj G))
                        (poly_map P₂ (gquot_functor_map (gquot_unit G)) x))
                     (poly_id P₂ (gquot G) (pr2 z))
                 @ maponpaths
                     ((poly_gquot P₂) (one_type_to_groupoid (gquot_functor_obj G)))
                     (poly_id
                        P₂ (gquot (one_type_to_groupoid (gquot_functor_obj G)))
                        (poly_map
                           P₂ (gquot_functor_map (gquot_unit G))
                           (poly_map P₂ (λ x, x) (pr2 z))))
                 @ poly_gquot_is_gcl P₂
                 (poly_map
                    P₂
                    (λ x, x)
                    (poly_map
                       P₂ (gquot_functor_map (gquot_unit G))
                       (poly_map P₂ (λ x, x) (pr2 z))))
                 =
                 step₃_help (pr2 z))
  : prod_gquot_data_comp_nat
      (poly_gquot P₁) (poly_gquot P₂) G
      (one_type_to_groupoid (gquot_functor_obj G)) (gquot_unit G) z
  @ maponpaths
      (λ x,
       (prod_gquot (poly_gquot P₁) (poly_gquot P₂))
         (one_type_to_groupoid (gquot_functor_obj G))
         (poly_map P₁ (gquot_functor_map (gquot_unit G)) (pr1 x)
          ,, poly_map P₂ (gquot_functor_map (gquot_unit G)) (pr2 x)))
      (pathsdirprod (poly_id P₁ (gquot G) (pr1 z)) (poly_id P₂ (gquot G) (pr2 z)))
  @ maponpaths
      ((prod_gquot (poly_gquot P₁) (poly_gquot P₂))
         (one_type_to_groupoid (gquot_functor_obj G)))
      (pathsdirprod
         (poly_id
            P₁ (gquot (one_type_to_groupoid (gquot_functor_obj G)))
            (poly_map
               P₁ (gquot_functor_map (gquot_unit G))
               (poly_map P₁ (λ x, x) (pr1 z))))
         (poly_id
            P₂ (gquot (one_type_to_groupoid (gquot_functor_obj G)))
            (poly_map
               P₂ (gquot_functor_map (gquot_unit G))
               (poly_map P₂ (λ x, x) (pr2 z)))))
  @ maponpaths
      (λ z0, prod_gquot_comp (pr1 z0) (pr2 z0))
      (pathsdirprod
         (poly_gquot_is_gcl
            P₁
            (poly_map
               P₁ (λ x, x)
               (poly_map
                  P₁ (gquot_functor_map (gquot_unit G))
                  (poly_map P₁ (λ x, x) (pr1 z)))))
         (poly_gquot_is_gcl
            P₂
            (poly_map
               P₂ (λ x, x)
               (poly_map
                  P₂ (gquot_functor_map (gquot_unit G))
                  (poly_map P₂ (λ x : gquot G, x) (pr2 z))))))
  =
  prod_gquot_data_comp_nat_help
    G (one_type_to_groupoid (gquot_functor_obj G)) 
    (gquot_unit G) ((poly_gquot P₁) G (pr1 z)) ((poly_gquot P₂) G (pr2 z))
  @ maponpaths
      (λ z0,
       prod_gquot_comp
         z0
         (gquot_functor_map
            (@poly_act_functor
               P₂ G (one_type_to_groupoid (gquot_functor_obj G))
               (gquot_unit_functor G)) ((poly_gquot P₂) G (pr2 z)))) 
      (step₃_help (pr1 z))
  @ maponpaths
      (prod_gquot_comp
         (gcl (poly_act_groupoid P₁ (one_type_to_groupoid (gquot_functor_obj G)))
              (poly_map
                 P₁ (gquot_counit_map (gquot_functor_obj G))
                 (poly_map
                    P₁ (λ x, x)
                    (poly_map P₁ (gquot_functor_map (gquot_unit G))
                              (poly_map P₁ (λ x, x) (pr1 z)))))))
      (step₃_help (pr2 z)).
Proof.
  refine (!(path_assoc _ _ _) @ _).
  apply maponpaths.
  etrans.
  {
    apply maponpaths_2.
    pose (uncurry_ap
            prod_gquot_comp
            (gquot_commute_prod.IHP₁_help (poly_gquot P₁) (gquot_unit G) (pr1 z))
            (gquot_commute_prod.IHP₂_help (poly_gquot P₂) (gquot_unit G) (pr2 z)))
      as h.
    unfold uncurry in h.
    exact (!h).
  }
  etrans.
  {
    apply maponpaths.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp
                 (dirprodf
                    (λ x,
                     (poly_gquot P₁)
                       (one_type_to_groupoid (gquot_functor_obj G))
                       (poly_map P₁ (gquot_functor_map (gquot_unit G)) x))
                    (λ x,
                     (poly_gquot P₂)
                       (one_type_to_groupoid (gquot_functor_obj G))
                       (poly_map P₂ (gquot_functor_map (gquot_unit G)) x)))
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (poly_id P₁ (gquot G) (pr1 z))
                    (poly_id P₂ (gquot G) (pr2 z))))).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        exact (!(maponpathscomp
                   (dirprodf
                      (poly_gquot P₁ (one_type_to_groupoid (gquot_functor_obj G)))
                      (poly_gquot P₂ (one_type_to_groupoid (gquot_functor_obj G))))
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod _ _))).
      }
      apply maponpaths.
      exact (!(maponpaths_pathsdirprod _ _ _ _)).
    }
    exact (!(maponpathscomp0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod _ _)
               (pathsdirprod _ _))).
  }
  etrans.
  {
    apply maponpaths.
    apply maponpaths_2.
    apply maponpaths.
    apply pathsdirprod_concat.
  }
  refine (path_assoc _ _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    exact (!(maponpathscomp0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod _ _)
               (pathsdirprod _ _))).
  }
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    apply pathsdirprod_concat.
  }
  etrans.
  {
    exact (!(maponpathscomp0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod _ _)
               (pathsdirprod
                  (poly_gquot_is_gcl
                     P₁
                     (poly_map
                        P₁ (λ x, x)
                        (poly_map
                           P₁ (gquot_functor_map (gquot_unit G))
                           (poly_map P₁ (λ x, x) (pr1 z)))))
                  (poly_gquot_is_gcl
                     P₂
                     (poly_map
                        P₂ (λ x, x)
                        (poly_map
                           P₂ (gquot_functor_map (gquot_unit G))
                           (poly_map P₂ (λ x, x) (pr2 z)))))))).
  }
  etrans.
  {
    apply maponpaths.
    apply pathsdirprod_concat.
  }
  refine (!_).
  etrans.
  {
    pose (uncurry_ap
            prod_gquot_comp
            (step₃_help (pr1 z))
            (step₃_help (pr2 z)))
      as h.
    unfold uncurry in h.
    exact (!h).
  }
  apply maponpaths.
  refine (!_).
  use paths_pathsdirprod.
  - refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(path_assoc _ _ _)).
    }
    exact IHP₁.
  - refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(path_assoc _ _ _)).
    }
    exact IHP₂.
Qed.

Definition step₃
           {P : poly_code}
           {G : grpd_bicat}
           (z : poly_act P (gquot G))
  : pr1 (psnaturality_of (poly_gquot P) (gquot_unit G)) z
  @ maponpaths
      (λ x, (poly_gquot P)
              (one_type_to_groupoid (gquot_functor_obj G))
              (poly_map P (gquot_functor_map (gquot_unit G)) x))
      (poly_id P (gquot G) z)
  @ maponpaths
      ((poly_gquot P) (one_type_to_groupoid (gquot_functor_obj G)))
      (poly_id
         P (gquot (one_type_to_groupoid (gquot_functor_obj G)))
         (poly_map
            P (gquot_functor_map (gquot_unit G))
            (poly_map P (λ x, x) z)))
  @ poly_gquot_is_gcl
      P
      (poly_map
         P (λ x, x)
         (poly_map
            P (gquot_functor_map (gquot_unit G))
            (poly_map P (λ x, x) z)))
    = step₃_help z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_prop.
    + intro.
      apply idpath.
    + exact (λ _, gtrunc _ _ _ _ _).
  - induction z as [z | z].
    + clear IHP₂ ; specialize (IHP₁ z).
      refine (!(path_assoc
                  (gquot_inl_grpd_gquot_functor
                     (gquot_unit G)
                     ((poly_gquot P₁) G z))
                  (maponpaths
                     gquot_inl_grpd
                     (pr1 (psnaturality_of (poly_gquot P₁) (gquot_unit G)) z))
                  _) @ _).
      transitivity (@gquot_inl_grpd_gquot_functor
                      P₁ P₂
                      _ _
                      (gquot_unit G)
                      ((poly_gquot P₁) G z)
                    @ maponpaths gquot_inl_grpd (step₃_help z)).
      2: apply idpath.
      apply maponpaths.
      refine (_ @ maponpaths (maponpaths gquot_inl_grpd) IHP₁ @ _).
      * refine (!_).
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (path_assoc _ _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_sum_gquot_inl.
        }
        apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp inl _ (poly_id P₁ (gquot G) z)).
        }
        refine (!_).
        exact (maponpathscomp _ gquot_inl_grpd (poly_id P₁ (gquot G) z)).
      * apply idpath.
    + clear IHP₁ ; specialize (IHP₂ z).
      refine (!(path_assoc
                  (gquot_inr_grpd_gquot_functor
                     (gquot_unit G)
                     ((poly_gquot P₂) G z))
                  (maponpaths
                     gquot_inr_grpd
                     (pr1 (psnaturality_of (poly_gquot P₂) (gquot_unit G)) z))
                  _) @ _).
      transitivity (@gquot_inr_grpd_gquot_functor
                      P₁ P₂
                      _ _
                      (gquot_unit G)
                      ((poly_gquot P₂) G z)
                    @ maponpaths gquot_inr_grpd (step₃_help z)).
      2: apply idpath.
      apply maponpaths.
      refine (_ @ maponpaths (maponpaths gquot_inr_grpd) IHP₂ @ _).
      * refine (!_).
        etrans.
        {
          apply maponpathscomp0.
        }
        apply maponpaths.
        etrans.
        {
          apply maponpathscomp0.
        }
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp0.
        }
        refine (path_assoc _ _ _ @ _).
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          apply maponpaths_sum_gquot_inr.
        }
        apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp inr _ (poly_id P₂ (gquot G) z)).
        }
        refine (!_).
        exact (maponpathscomp _ gquot_inr_grpd (poly_id P₂ (gquot G) z)).
      * apply idpath.
  - specialize (IHP₁ (pr1 z)).
    specialize (IHP₂ (pr2 z)).
    exact (step₃_prod z IHP₁ IHP₂).
Qed.

Definition step₄_help
           {P : poly_code}
           {G : grpd_bicat}
           (a : poly_act_groupoid P G)
  : poly_act_morphism
      P
      (one_type_to_groupoid (gquot_functor_obj G)) 
      (poly_map P (gcl G) a)
      (poly_map
         P (gquot_counit_map (gquot_functor_obj G))
         (poly_map
            P (λ x, x)
            (poly_map
               P (gquot_functor_map (gquot_unit G))
               (poly_map
                  P (λ x, x)
                  (gquot_poly (gcl (poly_act_groupoid P G) a)))))).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction a as [a | a].
    + exact (IHP₁ a).
    + exact (IHP₂ a).
  - exact (IHP₁ (pr1 a) ,, IHP₂ (pr2 a)).
Defined.

Definition step₄_lem₁
           {P : poly_code}
           {G : grpd_bicat}
           (a : poly_act_groupoid P G)
  : maponpaths
      (gquot_functor_map
         (@poly_act_functor
            P G (one_type_to_groupoid (gquot_functor_obj G))
            (gquot_unit G)))
      (! poly_gquot_gquot_poly_comp P a)
  @ step₃_help (gquot_poly (gcl (poly_act_groupoid P G) a))
  =
  gcleq
    (poly_act_groupoid P (one_type_to_groupoid (gquot_functor_obj G)))
    (step₄_help a).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (!(ge _ _)).
  - exact (!(ge _ _)).
  - induction a as [a | a].
    + refine (_ @ maponpaths (maponpaths gquot_inl_grpd) (IHP₁ a) @ _).
      * refine (!_).
        etrans.
        {
          apply maponpathscomp0.
        }
        simpl.
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp
                   (gquot_functor_map
                      (@poly_act_functor
                         P₁ G
                         (one_type_to_groupoid (gquot_functor_obj G))
                         (gquot_unit G)))
                   gquot_inl_grpd
                   (! poly_gquot_gquot_poly_comp P₁ a)).
        }        
        pose (maponpaths_paths'
                (@gquot_inl_grpd_gquot_functor P₁ P₂ _ _ (gquot_unit G))
                (! poly_gquot_gquot_poly_comp P₁ a))
          as p.
        refine (p @ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathsinv0
                     gquot_inl_grpd
                     (poly_gquot_gquot_poly_comp P₁ a))).
        }
        exact (maponpathscomp
                 gquot_inl_grpd
                 (gquot_functor_map
                    (@poly_act_functor
                       (P₁ + P₂) G
                       (one_type_to_groupoid (gquot_functor_obj G))
                       (gquot_unit G)))
                 (! poly_gquot_gquot_poly_comp P₁ a)).
      * apply gquot_rec_beta_gcleq.
    + refine (_ @ maponpaths (maponpaths gquot_inr_grpd) (IHP₂ a) @ _).
      * refine (!_).
        etrans.
        {
          apply maponpathscomp0.
        }
        simpl.
        refine (_ @ !(path_assoc _ _ _)).
        apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp
                   (gquot_functor_map
                      (@poly_act_functor
                         P₂ G
                         (one_type_to_groupoid (gquot_functor_obj G))
                         (gquot_unit G)))
                   gquot_inr_grpd
                   (! poly_gquot_gquot_poly_comp P₂ a)).
        }        
        pose (maponpaths_paths'
                (@gquot_inr_grpd_gquot_functor P₁ P₂ _ _ (gquot_unit G))
                (! poly_gquot_gquot_poly_comp P₂ a))
          as p.
        refine (p @ _).
        apply maponpaths_2.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathsinv0
                     gquot_inr_grpd
                     (poly_gquot_gquot_poly_comp P₂ a))).
        }
        exact (maponpathscomp
                 gquot_inr_grpd
                 (gquot_functor_map
                    (@poly_act_functor
                       (P₁ + P₂) G
                       (one_type_to_groupoid (gquot_functor_obj G))
                       (gquot_unit G)))
                 (! poly_gquot_gquot_poly_comp P₂ a)).
      * apply gquot_rec_beta_gcleq.
  - specialize (IHP₁ (pr1 a)).
    specialize (IHP₂ (pr2 a)).
    etrans.
    {
      do 2 refine (maponpaths (λ z, _ @ z) _).
      pose (uncurry_ap
              prod_gquot_comp
              (step₃_help (gquot_poly (gcl (poly_act_groupoid P₁ G) (pr1 a))))
              (step₃_help (gquot_poly (gcl (poly_act_groupoid P₂ G) (pr2 a)))))
        as h.
      unfold uncurry in h.
      exact (!h).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths_2.
      do 2 apply maponpaths.
      pose (uncurry_ap
              prod_gquot_comp
              (poly_gquot_gquot_poly_comp P₁ (pr1 a))
              (poly_gquot_gquot_poly_comp P₂ (pr2 a)))
        as h.
      unfold uncurry in h.
      exact (!h).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpaths.
      etrans.
      {
        exact (!(maponpathsinv0
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod
                      (poly_gquot_gquot_poly_comp P₁ (pr1 a))
                      (poly_gquot_gquot_poly_comp P₂ (pr2 a))))).
      }
      apply maponpaths.
      apply pathsdirprod_inv.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (maponpathscomp
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (gquot_functor_map
                  (@poly_act_functor
                     (P₁ * P₂) G
                     (one_type_to_groupoid (gquot_functor_obj G))
                     (gquot_unit G)))
               (pathsdirprod
                  (! poly_gquot_gquot_poly_comp P₁ (pr1 a))
                  (! poly_gquot_gquot_poly_comp P₂ (pr2 a)))).
    }
    etrans.
    {
      pose (maponpaths_paths'
              (λ z, prod_gquot_data_comp_nat_help
                      G (one_type_to_groupoid (gquot_functor_obj G)) 
                      (gquot_unit G)
                      (pr1 z) (pr2 z))
              (pathsdirprod
                 (! poly_gquot_gquot_poly_comp P₁ (pr1 a))
                 (! poly_gquot_gquot_poly_comp P₂ (pr2 a))))
        as h.
      apply maponpaths_2.
      exact (!h).
    }
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp
                 (dirprodf
                    (gquot_functor_map
                       (@poly_act_functor
                          P₁ G (one_type_to_groupoid (gquot_functor_obj G))
                          (gquot_unit G)))
                    (gquot_functor_map
                       (@poly_act_functor
                          P₂ G (one_type_to_groupoid (gquot_functor_obj G))
                          (gquot_unit G))))
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (! poly_gquot_gquot_poly_comp P₁ (pr1 a))
                    (! poly_gquot_gquot_poly_comp P₂ (pr2 a))))).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    etrans.
    {
      exact (!(maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (maponpaths
                       (gquot_functor_map
                          (@poly_act_functor
                             P₁ G
                             (one_type_to_groupoid (gquot_functor_obj G))
                             (gquot_unit G)))
                       (! poly_gquot_gquot_poly_comp P₁ (pr1 a)))
                    (maponpaths
                       (gquot_functor_map
                          (@poly_act_functor
                             P₂ G
                             (one_type_to_groupoid (gquot_functor_obj G))
                             (gquot_unit G)))
                       (! poly_gquot_gquot_poly_comp P₂ (pr2 a))))
                 (pathsdirprod
                    (step₃_help
                       (gquot_poly (gcl (poly_act_groupoid P₁ G) (pr1 a))))
                    (step₃_help
                       (gquot_poly (gcl (poly_act_groupoid P₂ G) (pr2 a))))))).
    }
    etrans.
    {
      apply maponpaths.
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact IHP₂.
      }
      apply maponpaths_2.
      exact IHP₁.
    }
    clear IHP₁ IHP₂.
    etrans.
    {
      pose (uncurry_ap
              prod_gquot_comp
              (gcleq
                 (poly_act_groupoid
                    P₁ (one_type_to_groupoid (gquot_functor_obj G)))
                 (step₄_help (pr1 a)))
              (gcleq
                 (poly_act_groupoid
                    P₂ (one_type_to_groupoid (gquot_functor_obj G)))
                 (step₄_help (pr2 a))))
        as h.
      unfold uncurry in h.
      exact h.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (gquot_double_rec'_beta_l_gcleq _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      apply maponpaths.
      exact (gquot_double_rec'_beta_r_gcleq _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    }
    refine (!(gconcat _ _ _) @ _).
    apply maponpaths.
    simpl.
    exact (pathsdirprod
             (poly_act_id_right _)
             (poly_act_id_left _)).
Qed.

Definition step₄_lem₂
           {P : poly_code}
           {G : grpd_bicat}
           (a : poly_act_groupoid P G)
  : maponpaths
      (poly_gquot P G)
      (# ((poly_path_groupoid P) (gquot_functor_obj G) : _ ⟶ _) (step₄_help a))
  =
  ! prealg_unit_comp_help P a
  @ ! (maponpaths
         (poly_gquot P G)
         (poly_part_of_left_triangle (gquot_poly (gcl (poly_act_groupoid P G) a)))
          @ poly_gquot_gquot_poly_comp P a).
Proof.
  refine (_ @ pathscomp_inv _ _).
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction a as [a | a].
    + specialize (IHP₁ a) ; clear IHP₂.
      refine (_ @ maponpaths (maponpaths gquot_inl_grpd) IHP₁ @ _) ; clear IHP₁.
      * exact (maponpaths_sum_gquot_inl _).
      * etrans.
        {
          apply maponpathsinv0.
        }
        apply maponpaths.
        refine (!_).
        etrans.
        {
          refine (maponpaths (λ z, (z @ _) @ _) _).
          exact (maponpaths_sum_gquot_inl _).
        }
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (!(maponpathscomp0
                     gquot_inl_grpd
                     _
                     (poly_gquot_gquot_poly_comp P₁ a))).
        }
        exact (!(maponpathscomp0 gquot_inl_grpd _ _)).
    + specialize (IHP₂ a) ; clear IHP₁.
      refine (_ @ maponpaths (maponpaths gquot_inr_grpd) IHP₂ @ _) ; clear IHP₂.
      * exact (maponpaths_sum_gquot_inr _).
      * etrans.
        {
          apply maponpathsinv0.
        }
        apply maponpaths.
        refine (!_).
        etrans.
        {
          refine (maponpaths (λ z, (z @ _) @ _) _).
          exact (maponpaths_sum_gquot_inr _).
        }
        etrans.
        {
          refine (maponpaths (λ z, z @ _) _).
          exact (!(maponpathscomp0
                     gquot_inr_grpd
                     _
                     (poly_gquot_gquot_poly_comp P₂ a))).
        }
        exact (!(maponpathscomp0 gquot_inr_grpd _ _)).
  - specialize (IHP₁ (pr1 a)).
    specialize (IHP₂ (pr2 a)).
    etrans.
    {
      exact (!(maponpathscomp
                 (dirprodf (poly_gquot P₁ G) (poly_gquot P₂ G))
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (# (pr1 ((poly_path_groupoid P₁)
                               (gquot_functor_obj G))) (step₄_help (pr1 a)))
                    (# (pr1 ((poly_path_groupoid P₂)
                               (gquot_functor_obj G))) (step₄_help (pr2 a)))))).
    }
    etrans.
    {
      apply maponpaths.
      exact (!(maponpaths_pathsdirprod _ _ _ _)).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact IHP₂.
      }
      apply maponpaths_2.
      exact IHP₁.
    }
    clear IHP₁ IHP₂.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (pathscomp_inv _ _).
      }
      etrans.
      {
        apply maponpaths_2.
        exact (pathscomp_inv _ _).
      }      
      exact (!(pathsdirprod_concat _ _ _ _)).
    }
    etrans.
    {
      exact (maponpathscomp0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod _ _)
               (pathsdirprod _ _)).
    }
    refine (!_).
    etrans.
    {
      apply pathscomp_inv.
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        exact (!(maponpathsinv0
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod
                      (prealg_unit_comp_help P₁ (pr1 a))
                      (prealg_unit_comp_help P₂ (pr2 a))))).
      }
      apply maponpaths.
      apply pathsdirprod_inv.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply pathsdirprod_inv.
      }
      exact (maponpathsinv0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod
                  (maponpaths
                     ((poly_gquot P₁) G)
                     (poly_part_of_left_triangle
                        (gquot_poly (gcl (poly_act_groupoid P₁ G) (pr1 a))))
                   @ poly_gquot_gquot_poly_comp P₁ (pr1 a))
                  (maponpaths
                     ((poly_gquot P₂) G)
                     (poly_part_of_left_triangle
                        (gquot_poly (gcl (poly_act_groupoid P₂ G) (pr2 a))))
                   @ poly_gquot_gquot_poly_comp P₂ (pr2 a)))).
    }
    refine (maponpaths (λ z, ! z) _).
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply pathsdirprod_concat.
      }
      exact (maponpathscomp0
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod
                  (maponpaths
                     (poly_gquot P₁ G)
                     (poly_part_of_left_triangle
                        (gquot_poly (gcl (poly_act_groupoid P₁ G) (pr1 a)))))
                  (maponpaths
                     (poly_gquot P₂ G)
                     (poly_part_of_left_triangle
                        (gquot_poly (gcl (poly_act_groupoid P₂ G) (pr2 a))))))
               (pathsdirprod
                  (poly_gquot_gquot_poly_comp P₁ (pr1 a))
                  (poly_gquot_gquot_poly_comp P₂ (pr2 a)))).
    }
    simpl.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_pathsdirprod.
      }
      exact (maponpathscomp
               (dirprodf ((poly_gquot P₁) G) ((poly_gquot P₂) G))
               (λ z, prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod
                  (poly_part_of_left_triangle
                     (gquot_poly (gcl (poly_act_groupoid P₁ G) (pr1 a))))
                  (poly_part_of_left_triangle
                     (gquot_poly (gcl (poly_act_groupoid P₂ G) (pr2 a)))))).
    }
    apply maponpaths.
    pose (uncurry_ap
            prod_gquot_comp
            (poly_gquot_gquot_poly_comp P₁ (pr1 a))
            (poly_gquot_gquot_poly_comp P₂ (pr2 a)))
      as h.
    unfold uncurry in h.
    exact h.
Qed.

Definition step₄_lemma
           {P : poly_code}
           {G : grpd_bicat}
           (hG : (disp_alg_bicat ⦃ P ⦄) G)
  : ∏ (q : gquot (poly_act_groupoid P G)),
    left_triangle_help hG q
    =
    maponpaths
      (gquot_counit_map (gquot_functor_obj G))
      (maponpaths
         (gquot_functor_map
            (prealg_path_groupoid_map
               P (gquot_functor_obj G) (prealg_gquot_map P G hG)))
         (maponpaths
            (gquot_functor_map
               (@poly_act_functor
                  P G
                  (one_type_to_groupoid (gquot_functor_obj G))
                  (gquot_unit G)))
            (!(poly_gquot_gquot_poly q))))
    @ maponpaths
        (gquot_counit_map (gquot_functor_obj G))
        (maponpaths
           (gquot_functor_map
              (prealg_path_groupoid_map
                 P (gquot_functor_obj G) (prealg_gquot_map P G hG)))
           (step₃_help (gquot_poly q)))
    @ maponpaths
        (prealg_gquot_map P G hG)
        (poly_part_of_left_triangle (gquot_poly q))
    @ maponpaths (gquot_functor_map hG) (poly_gquot_gquot_poly q).
Proof.
  use gquot_ind_prop.
  - intro a.
    etrans.
    {
      refine (maponpaths (λ z, !z) _).
      exact (gquot_rec_beta_gcleq
               (one_type_to_groupoid (gquot_functor_obj G))
               _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      unfold prealg_unit_nat_trans_comp.
      exact (!(maponpathsinv0 (gquot_functor_map hG) (prealg_unit_comp_help P a))).
    }
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact (!(maponpathscomp
                 (poly_gquot P G)
                 (gquot_functor_map hG)
                 _)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      exact (!(maponpathscomp0
                 (gquot_functor_map hG)
                 (maponpaths
                    (poly_gquot P G)
                    (poly_part_of_left_triangle
                       (gquot_poly (gcl (poly_act_groupoid P G) a))))
                 (poly_gquot_gquot_poly_comp P a))).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp
                 (gquot_functor_map
                    (prealg_path_groupoid_map
                       P
                       (gquot_functor_obj G)
                       (prealg_gquot_map P G hG)))
                 (gquot_counit_map (gquot_functor_obj G))
                 (maponpaths
                    (gquot_functor_map
                       (@poly_act_functor
                          P G (one_type_to_groupoid (gquot_functor_obj G))
                          (gquot_unit_functor G))) (! poly_gquot_gquot_poly_comp P a))).
      }
      etrans.
      {
        apply maponpaths.
        exact (maponpathscomp
                 (gquot_functor_map
                    (prealg_path_groupoid_map
                       P
                       (gquot_functor_obj G)
                       (prealg_gquot_map P G hG)))
                 (gquot_counit_map (gquot_functor_obj G))
                 (step₃_help (gquot_poly (gcl (poly_act_groupoid P G) a)))).
      }
      exact (!(maponpathscomp0
                 _
                 (maponpaths
                    (gquot_functor_map
                       (@poly_act_functor
                          P G (one_type_to_groupoid (gquot_functor_obj G))
                          (gquot_unit_functor G)))
                    (! poly_gquot_gquot_poly_comp P a))
                 (step₃_help (gquot_poly (gcl (poly_act_groupoid P G) a))))).
    }
    use hornRotation_rr.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathsinv0
                 (gquot_functor_map hG)
                 (maponpaths
                    (poly_gquot P G)
                    (poly_part_of_left_triangle
                       (gquot_poly (gcl (poly_act_groupoid P G) a)))
                  @ poly_gquot_gquot_poly_comp P a))).
    }
    etrans.
    {
      exact (!(maponpathscomp0 (gquot_functor_map hG) _ _)).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (step₄_lem₁ a).
    }
    etrans.
    {
      exact (!(maponpathscomp
                 (gquot_functor_map
                    (prealg_path_groupoid_map
                       P (gquot_functor_obj G)
                       (prealg_gquot_map P G hG)))
                 (gquot_counit_map (gquot_functor_obj G))
                 (gcleq (poly_act_groupoid
                           P (one_type_to_groupoid (gquot_functor_obj G)))
                        (step₄_help a)))).
    }
    etrans.
    {
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      exact (!(maponpathscomp (poly_gquot P G) (gquot_functor_map hG) _)).
    }
    apply maponpaths.
    exact (step₄_lem₂ a).
  - exact (λ _, gtrunc _ _ _ _ _).
Qed.

Definition step₄
           {P : poly_code}
           {G : grpd_bicat}
           (hG : (disp_alg_bicat ⦃ P ⦄) G)
           (z : poly_act P (gquot G))
  : maponpaths
      (gquot_counit_map (gquot_functor_obj G))
      (maponpaths
         (gquot_functor_map
            (prealg_path_groupoid_map
               P (gquot_functor_obj G) (prealg_gquot_map P G hG)))
         (step₃_help z))
    @ maponpaths
        (prealg_gquot_map P G hG)
        (poly_part_of_left_triangle z)
    =
    left_triangle_help hG ((poly_gquot P) G z).
Proof.
  refine (_ @ !(step₄_lemma hG _)).
  pose (maponpaths_paths
          (λ z, maponpaths
                  (gquot_counit_map (gquot_functor_obj G))
                  (maponpaths
                     (gquot_functor_map
                        (prealg_path_groupoid_map
                           P (gquot_functor_obj G) (prealg_gquot_map P G hG)))
                     (step₃_help z))
                  @ maponpaths
                  (prealg_gquot_map P G hG)
                  (poly_part_of_left_triangle z))
          (gquot_poly_poly_gquot z))
    as h.
  refine (!h @ _) ; clear h.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply maponpathscomp.
  }
  etrans.
  {
    apply maponpaths_2.
    exact (maponpathscomp _ (λ _ , _) _).
  }
  assert (! poly_gquot_gquot_poly ((poly_gquot P) G z)
          =
          maponpaths ((poly_gquot P) G) (! gquot_poly_poly_gquot z))
    as X.
  {
    etrans.
    {
      apply maponpaths.
      exact (!(maponpaths_gquot_poly_poly_gquot P z)).
    }
    refine (!_).
    apply maponpathsinv0.
  }
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      exact X.
    }
    exact (maponpathscomp _ (λ _, _) _).
  }
  apply maponpaths.
  refine (_ @ path_assoc _ _ _).
  do 2 apply maponpaths.
  etrans.
  {
    apply maponpaths.
    refine (!_).
    apply maponpaths_gquot_poly_poly_gquot.
  }
  exact (maponpathscomp
           (poly_gquot P G)
           (gquot_functor_map hG)
           _).
Qed.

Definition algebra_disp_biadjunction_left_triangle
           (P : poly_code)
  : disp_left_biadj_left_triangle
      (disp_alg_bicat ⦃ P ⦄)
      (disp_alg_bicat (⟦ P ⟧))
      (algebra_disp_biadjunction_unit_counit P)
      (pr12 gquot_biadj_data).
Proof.
  use make_disp_invmodification.
  - apply disp_2cells_isaprop_alg.
  - apply disp_locally_groupoid_alg.
  - intros G hG.
    use funextsec.
    intro z.
    refine (!_).
    etrans.
    {
      do 2 refine (maponpaths (λ z, z @ _) _).
      refine (pathscomp0rid _ @ _).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (pathscomp0rid _).
      }
      refine (maponpaths (λ z, _ @ z) _).
      refine (maponpaths (λ z, z @ _) _).
      refine (pathscomp0rid _ @ _).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (pathscomp0rid _).
      }
      refine (maponpaths (λ z, _ @ z) _).
      refine (maponpaths (λ z, z @ _) _).
      refine (pathscomp0rid _ @ _).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (pathscomp0rid _).
      }
      refine (maponpaths (λ z, _ @ z) _).
      refine (maponpaths (λ z, z @ _) _).
      refine (pathscomp0rid _ @ _).
      refine (maponpaths (λ z, z @ _) _).
      exact (pathscomp0rid _).
    }
    etrans.
    {
      do 2 refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      do 2 refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      do 2 refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      do 2 refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathsidfun
                 (prealg_counit_comp
                    P (prealg_gquot_map P G hG)
                    (poly_map
                       P (λ x, x)
                       (poly_map P (gquot_functor_map _)
                                 (poly_map P (λ x : gquot G, x) z))))).
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              exact (!(maponpathscomp0 (prealg_gquot_map P G hG) _ _)).
            }
            exact (!(maponpathscomp0 (prealg_gquot_map P G hG) _ _)).
          }
          exact (!(maponpathscomp0 (prealg_gquot_map P G hG) _ _)).
        }
        exact (!(maponpathscomp0 (prealg_gquot_map P G hG) _ _)).
      }
      exact (!(maponpathscomp0 (prealg_gquot_map P G hG) _ _)).
    }
    etrans.
    {
      do 3 apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (!(maponpathscomp0 (prealg_gquot_map P G hG) _ _)).
    }
    etrans.
    {
      do 4 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (step₁ z).
      }
      exact (maponpathscomp0 (prealg_gquot_map P G hG) _ _).
    }
    do 4 refine (path_assoc _ _ _ @ _).
    refine (maponpaths (λ z, z @ _) _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp
                   (λ q,
                    gquot_functor_map
                      (prealg_path_groupoid_map
                         P
                         (gquot_psfunctor G)
                         (prealg_gquot_map P G hG))
                      q)
                   (gquot_counit_map (gquot_psfunctor G))
                   _)).
      }
      do 3 refine (maponpaths (λ z, z @ _) _).
      exact (!(maponpathscomp
                 (gquot_functor_map (gquot_unit G))
                 (gquot_counit_map (gquot_psfunctor G))
                 _)).
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        do 2 refine (maponpaths (λ z,z @ _) _).
        exact (!(maponpathscomp0
                   (gquot_counit_map (gquot_functor_obj G))
                   _ _)).
      }
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (!(maponpathscomp0
                   (gquot_counit_map (gquot_functor_obj G))
                   _ _)).
      }
      exact (!(maponpathscomp0
                 (gquot_counit_map (gquot_functor_obj G))
                 _ _)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      unfold prealg_gquot_map.
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp
                   (poly_gquot P (one_type_to_groupoid (gquot_functor_obj G)))
                   (λ q,
                    gquot_functor_map
                      (prealg_path_groupoid_map
                         P (gquot_functor_obj G)
                         (λ x, gquot_functor_map hG ((poly_gquot P) G x))) q)
                   _)).
      }
      refine (!(maponpathscomp0
                  (λ q,
                   gquot_functor_map
                     (prealg_path_groupoid_map
                        P (gquot_functor_obj G)
                        (λ x, gquot_functor_map hG ((poly_gquot P) G x))) q)
                  (maponpaths
                     (poly_gquot P (one_type_to_groupoid (gquot_functor_obj G)))
                     (poly_id
                        P (gquot (one_type_to_groupoid (gquot_functor_obj G)))
                        (poly_map
                           P (gquot_functor_map (gquot_unit G))
                           (poly_map P (λ x, x) z))))
                  (poly_gquot_is_gcl
                     P
                     (poly_map
                        P (λ x, x)
                        (poly_map
                           P (gquot_functor_map (gquot_unit G))
                           (poly_map P (λ x : gquot G, x) z)))))).
    }
    pose (homotsec_natural'
            (prealg_gquot_cell
               P
               (make_invertible_2cell
                  (grpd_bicat_is_invertible_2cell (prealg_unit_nat_trans P hG))))
            (poly_id P (gquot G) z))
      as s.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp
                 (prealg_gquot_map P G hG)
                 (gquot_functor_map (gquot_unit G))
                 (poly_id P (gquot G) z)).
      }
      exact s.
    }
    clear s.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp
                   (λ x,
                    poly_gquot
                      P (one_type_to_groupoid (gquot_functor_obj G))
                      (poly_map P (gquot_functor_map (gquot_unit G)) x))
                   (λ q,
                    gquot_functor_map
                      (prealg_path_groupoid_map
                         P (gquot_functor_obj G)
                         (λ x, gquot_functor_map hG ((poly_gquot P) G x))) q)
                   (poly_id P (gquot G) z))).
      }
      exact (!(maponpathscomp0
                 (λ q,
                    gquot_functor_map
                      (prealg_path_groupoid_map
                         P (gquot_functor_obj G)
                         (λ x, gquot_functor_map hG ((poly_gquot P) G x))) q)
                 (maponpaths
                    (λ x,
                     poly_gquot
                       P (one_type_to_groupoid (gquot_functor_obj G))
                       (poly_map
                          P (gquot_functor_map (gquot_unit G)) x))
                    (poly_id P (gquot G) z))
                 (maponpaths
                    (poly_gquot P (one_type_to_groupoid (gquot_functor_obj G)))
                    (poly_id
                       P (gquot (one_type_to_groupoid (gquot_functor_obj G)))
                       (poly_map P (gquot_functor_map (gquot_unit G))
                                 (poly_map P (λ x : gquot G, x) z)))
                  @ poly_gquot_is_gcl P
                  (poly_map
                     P (λ x, x)
                     (poly_map P (gquot_functor_map (gquot_unit G))
                               (poly_map P (λ x, x) z)))))).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      exact (!(maponpathscomp0
                 (gquot_functor_map
                    (prealg_path_groupoid_map
                       P (gquot_functor_obj G) (prealg_gquot_map P G hG)))
                 (pr1 (psnaturality_of (poly_gquot P) (gquot_unit G)) z)
                 (maponpaths
                    (λ x,
                     (poly_gquot P)
                       (one_type_to_groupoid (gquot_functor_obj G))
                       (poly_map
                          P (gquot_functor_map (gquot_unit G)) x))
                    (poly_id P (gquot G) z)
               @ maponpaths
                   ((poly_gquot P) (one_type_to_groupoid (gquot_functor_obj G)))
                   (poly_id
                      P (gquot (one_type_to_groupoid (gquot_functor_obj G)))
                      (poly_map
                         P (gquot_functor_map (gquot_unit G))
                         (poly_map P (λ x, x) z)))
               @ poly_gquot_is_gcl
                   P
                   (poly_map
                      P (λ x, x)
                      (poly_map
                         P (gquot_functor_map (gquot_unit G))
                         (poly_map P (λ x, x) z)))))).
    }
    etrans.
    {
      apply maponpaths_2.
      exact (maponpathscomp0
               (gquot_counit_map (gquot_functor_obj G))
               (prealg_gquot_help
                  P (gquot_unit G)
                  (make_invertible_2cell
                     (grpd_bicat_is_invertible_2cell
                        (prealg_unit_nat_trans P hG)))
                  ((poly_gquot P) G z))
               (maponpaths
                  (gquot_functor_map
                     (prealg_path_groupoid_map
                        P (gquot_functor_obj G) (prealg_gquot_map P G hG)))
                  (pr1 (psnaturality_of (poly_gquot P) (gquot_unit G)) z
            @ maponpaths
                (λ x,
                 (poly_gquot P)
                   (one_type_to_groupoid (gquot_functor_obj G))
                   (poly_map P (gquot_functor_map (gquot_unit G)) x))
                (poly_id P (gquot G) z)
            @ maponpaths
                ((poly_gquot P) (one_type_to_groupoid (gquot_functor_obj G)))
                (poly_id
                   P (gquot (one_type_to_groupoid (gquot_functor_obj G)))
                   (poly_map
                      P (gquot_functor_map (gquot_unit G))
                      (poly_map P (λ x, x) z)))
            @ poly_gquot_is_gcl
                P
                (poly_map
                   P (λ x, x)
                   (poly_map
                      P (gquot_functor_map (gquot_unit G))
                      (poly_map P (λ x, x) z)))))).
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (_ @ step₂ hG (poly_gquot P G z)).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths.
      exact (step₃ z).
    }
    exact (step₄ hG z).
Qed.
