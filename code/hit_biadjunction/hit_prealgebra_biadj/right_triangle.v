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
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import biadjunctions.all.
Require Import hit_biadjunction.hit_prealgebra_biadj_unit_counit.

Local Open Scope cat.

Local Arguments make_nat_trans {_ _ _ _} _ {_}.

Local Arguments poly_act_functor_identity_data {_ _}.
Local Arguments poly_act_functor_composition_data {_ _ _ _ _ _ _}.
Local Arguments poly_act_functor_morphisms _ {_ _} _ {_ _} _.

(* Steps for proof *)
Definition step₁_help
           {P : poly_code}
           {x : one_type}
           (z : poly_act P x)
  : poly_act_morphism
      P (one_type_to_groupoid x) (poly_map P (λ a : x, a) z)
      (poly_map
         P (gquot_counit_map x)
         ((pr1 ((poly_path_groupoid P) (gquot_functor_obj (one_type_to_groupoid x))))
            (poly_map
               P (λ a : gquot (one_type_to_groupoid x), a)
               (poly_map
                  P (gcl (one_type_to_groupoid x)) (poly_map P (λ a : x, a) z))))).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (idpath z).
  - exact (idpath z).
  - induction z as [z | z].
    + exact (IHP₁ z).
    + exact (IHP₂ z).
  - exact (IHP₁ (pr1 z) ,, IHP₂ (pr2 z)).
Defined.
  
Definition step₁
           {P : poly_code}
           {x : one_type}
           (z : poly_act P x)
  : (prealg_unit_comp_help
       P (poly_map P (λ a : pr1 (gquot_biadj_data x), a) z)
  @ maponpaths
      ((poly_gquot P) (one_type_to_groupoid x))
      (# (pr1 ((poly_path_groupoid P)
                 (gquot_functor_obj (one_type_to_groupoid x))))
         (@poly_act_functor_identity_data
            P
            (one_type_to_groupoid (gquot_functor_obj (one_type_to_groupoid x)))
            (poly_map
               P (gcl (one_type_to_groupoid x))
               (poly_map P (λ a : pr1 (gquot_biadj_data x), a) z)))))
  @ poly_gquot_is_gcl
      P
      ((pr1 ((poly_path_groupoid P)
               (gquot_functor_obj (one_type_to_groupoid x))))
      (poly_map
         P (λ a : gquot (one_type_to_groupoid x), a)
         (poly_map
            P (gcl (one_type_to_groupoid x))
            (poly_map
               P (λ a : pr1 (gquot_biadj_data x), a) z))))
  =
  gcleq (poly_act_groupoid P (gquot_biadj_data x)) (step₁_help z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (!(ge _ _)).
  - exact (!(ge _ _)).
  - induction z as [z | z].
    + specialize (IHP₁ z) ; clear IHP₂.
      simpl.
      refine (_ @ maponpaths (maponpaths gquot_inl_grpd) IHP₁ @ _) ; clear IHP₁.
      * refine (!(path_assoc _ _ _) @ _).
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (!(path_assoc _ _ _)).
          }
          exact (maponpathscomp0 _ _ _).
        }
        apply maponpaths.
        etrans.
        {
          exact (maponpathscomp0 _ _ _).
        }
        apply maponpaths_2.
        refine (!_).
        apply maponpaths_sum_gquot_inl.
      * apply gquot_rec_beta_gcleq.
    + specialize (IHP₂ z) ; clear IHP₁.
      simpl.
      refine (_ @ maponpaths (maponpaths gquot_inr_grpd) IHP₂ @ _) ; clear IHP₂.
      * refine (!(path_assoc _ _ _) @ _).
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (!(path_assoc _ _ _)).
          }
          exact (maponpathscomp0 _ _ _).
        }
        apply maponpaths.
        etrans.
        {
          exact (maponpathscomp0 _ _ _).
        }
        apply maponpaths_2.
        refine (!_).
        apply maponpaths_sum_gquot_inr.
      * apply gquot_rec_beta_gcleq.
  - specialize (IHP₁ (pr1 z)).
    specialize (IHP₂ (pr2 z)).
    etrans.
    {
      simpl.
      apply maponpaths_2.
      apply maponpaths.
      exact (!(maponpathscomp
                 (dirprodf
                    (poly_gquot P₁ (one_type_to_groupoid x))
                    (poly_gquot P₂ (one_type_to_groupoid x)))
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod _ _))).
    }
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (@prealg_unit_comp_help
                       P₁
                       (one_type_to_groupoid x)
                       (poly_map P₁ (λ a, a) (pr1 z)))
                    (@prealg_unit_comp_help
                       P₂
                       (one_type_to_groupoid x)
                       (poly_map P₂ (λ a, a) (pr2 z))))
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
                 (pathsdirprod
                    (@prealg_unit_comp_help
                       P₁
                       (one_type_to_groupoid x)
                       (poly_map P₁ (λ a, a) (pr1 z))
                     @ _)
                    (@prealg_unit_comp_help
                       P₂
                       (one_type_to_groupoid x)
                       (poly_map P₂ (λ a, a) (pr2 z))
                     @ _))
                 (pathsdirprod
                    (poly_gquot_is_gcl
                       P₁
                       ((pr1 ((poly_path_groupoid P₁)
                                (gquot_functor_obj (one_type_to_groupoid x))))
                          (poly_map
                             P₁ (λ a, a)
                             (poly_map
                                P₁ (gcl (one_type_to_groupoid x))
                                (poly_map P₁ (λ a : x, a) (pr1 z))))))
                    (poly_gquot_is_gcl
                       P₂
                       ((pr1 ((poly_path_groupoid P₂)
                                (gquot_functor_obj (one_type_to_groupoid x))))
                          (poly_map
                             P₂ (λ a, a)
                             (poly_map
                                P₂ (gcl (one_type_to_groupoid x))
                                (poly_map P₂ (λ a : x, a) (pr2 z))))))))).
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
        apply IHP₂.
      }
      apply maponpaths_2.
      apply IHP₁.
    }
    pose (uncurry_ap
            prod_gquot_comp
            (gcleq (poly_act_groupoid
                      P₁ (gquot_biadj_data x)) (step₁_help (pr1 z)))
            (gcleq (poly_act_groupoid
                      P₂ (gquot_biadj_data x)) (step₁_help (pr2 z))))
      as h.
    unfold uncurry in h.
    refine (h @ _).
    clear h IHP₁ IHP₂.
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
    exact (pathsdirprod
             (poly_act_id_right _)
             (poly_act_id_left _)).
Qed.

Definition step₂_help
           {P : poly_code}
           {x : one_type}
           (z : poly_act P x)
  : poly_act_morphism
      P
      (one_type_to_groupoid (gquot_functor_obj (one_type_to_groupoid x)))
      ((pr1 ((poly_path_groupoid P) (gquot_functor_obj (one_type_to_groupoid x))))
         (poly_map
            P (λ a : gquot (one_type_to_groupoid x), a)
            (poly_map
               P (gcl (one_type_to_groupoid x)) (poly_map P (λ a, a) z))))
      (poly_map
         P (λ a : gquot (one_type_to_groupoid x), a)
         (poly_map
            P (gcl (one_type_to_groupoid x)) (poly_map P (λ a, a) z))).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + exact (IHP₁ z).
    + exact (IHP₂ z).
  - exact (IHP₁ (pr1 z) ,, IHP₂ (pr2 z)).
Defined.

Definition step₂
           {P : poly_code}
           {x : one_type}
           (z : poly_act P x)
  : poly_path_groupoid_poly_map
      P
      ((pr1 ((poly_path_groupoid P)
               (gquot_functor_obj (one_type_to_groupoid x))))
         (poly_map
            P (λ a : gquot (one_type_to_groupoid x), a)
            (poly_map
               P (gcl (one_type_to_groupoid x)) (poly_map P (λ a, a) z))))
   @ (pr11 (psnaturality_of
              (poly_path_groupoid P)
              (gquot_counit_map x)))
     (poly_map
        P (λ a, a)
        (poly_map
           P (gcl (one_type_to_groupoid x))
           (poly_map P (λ a, a) z)))
    =
    # ((poly_path_groupoid P) x : _ ⟶ _)
      (poly_act_functor_morphisms
         P
         (function_to_functor (gquot_counit x))
         (step₂_help z)).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - simpl.
    apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + specialize (IHP₁ z) ; clear IHP₂.
      exact (!(maponpathscomp0 inl _ _) @ maponpaths (maponpaths inl) IHP₁).
    + specialize (IHP₂ z) ; clear IHP₁.
      exact (!(maponpathscomp0 inr _ _) @ maponpaths (maponpaths inr) IHP₂).
  - exact (pathsdirprod_concat _ _ _ _
           @ maponpaths (λ z, pathsdirprod z _) (IHP₁ (pr1 z))
           @ maponpaths (pathsdirprod _) (IHP₂ (pr2 z))).
Qed.

Definition algebra_disp_biadjunction_right_triangle
           (P : poly_code)
  : disp_left_biadj_right_triangle
      (disp_alg_bicat ⦃ P ⦄)
      (disp_alg_bicat (⟦ P ⟧))
      (algebra_disp_biadjunction_unit_counit P)
      (pr22 gquot_biadj_data).
Proof.
  use make_disp_invmodification.
  - apply disp_2cells_isaprop_alg.
  - apply disp_locally_groupoid_alg.
  - intros x xx.
    use nat_trans_eq.
    { apply homset_property. }
    intro z.
    refine (!_).
    etrans.
    {
      do 2 refine (maponpaths (λ z, z @ _) _).
      refine (pathscomp0rid _ @ _).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (pathscomp0rid
                 (maponpaths
                    (gquot_counit_map x)
                    (gcleq
                       (one_type_to_groupoid x)
                       (maponpaths
                          xx
                          (# ((poly_path_groupoid P) x : _ ⟶ _)
                             (poly_act_functor_identity_data z)))))).
      }
      refine (maponpaths (λ z, _ @ z) _).
      refine (maponpaths (λ z, z @ _) _).
      etrans.
      {
        refine (pathscomp0rid (_ @ _)).
      }      
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (pathscomp0rid
                 (maponpaths
                    (gquot_counit_map x)
                    (prealg_unit_nat_trans_comp
                       P
                       (prealg_path_groupoid_map P x xx)
                       (poly_map P (λ a, a) z)))).
      }
      refine (maponpaths (λ z, _ @ z) _).
      refine (maponpaths (λ z, z @ _) _).
      refine (pathscomp0rid _ @ _).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        exact (pathscomp0rid
                 (maponpaths
                    (gquot_counit_map x)
                    (maponpaths
                       (prealg_gquot_map
                          P
                          (one_type_to_groupoid x)
                          (prealg_path_groupoid_map P x xx))
                       (# ((poly_path_groupoid P)
                             (gquot_functor_obj (one_type_to_groupoid x)) : _ ⟶ _)
                          (@poly_act_functor_identity_data
                             P
                             (one_type_to_groupoid
                                (gquot_functor_obj (one_type_to_groupoid x)))
                             (poly_map
                                P
                                (gcl (one_type_to_groupoid x))
                                (poly_map
                                   P
                                   (λ a, a)
                                   z))))))).
      }
      refine (maponpaths (λ z, _ @ z) _).
      refine (maponpaths (λ z, z @ _) _).
      refine (pathscomp0rid _ @ _).
      refine (maponpaths (λ z, z @ _) _).
      exact (pathscomp0rid _).
    }    
    etrans.
    {
      do 3 apply maponpaths_2.
      exact (gquot_rec_beta_gcleq (one_type_to_groupoid x) _ _ _ _ _ _ _ _ _).
    }
    do 2 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      do 3 apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc
                (maponpaths
                   (gquot_counit_map x)
                   (prealg_unit_nat_trans_comp
                      P (prealg_path_groupoid_map P x xx)
                      (poly_map P (λ a, a) z))
                 @ maponpaths (gquot_counit_map x) _)
                     (prealg_counit_comp P xx _)
                _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (maponpathscomp
                 (gquot_functor_map (prealg_path_groupoid_map P x xx))
                 (gquot_counit_map x)
                 (prealg_unit_comp_help P (poly_map P (λ a, a) z))).
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp
                     (poly_gquot P (one_type_to_groupoid x))
                     (gquot_functor_map (prealg_path_groupoid_map P x xx))
                     _)).
        }
        exact (maponpathscomp
                 (gquot_functor_map (prealg_path_groupoid_map P x xx))
                 (gquot_counit_map x)
                 (maponpaths
                    _
                    (# (pr1 ((poly_path_groupoid P)
                               (gquot_functor_obj (one_type_to_groupoid x))))
                       (@poly_act_functor_identity_data
                          P
                          (one_type_to_groupoid
                             (gquot_functor_obj (one_type_to_groupoid x)))
                          (poly_map
                             P
                             (gcl (one_type_to_groupoid x))
                             (poly_map P (λ a, a) z)))))).
      }
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp0
                   (λ x0,
                    gquot_counit_map
                      x
                      (gquot_functor_map
                         (prealg_path_groupoid_map P x xx) x0))
                   (prealg_unit_comp_help P (poly_map P (λ a, a) z))
                   _)).
      }
      etrans.
      {
        exact (!(maponpathscomp0
                   (λ x0,
                    gquot_counit_map
                      x
                      (gquot_functor_map
                         (prealg_path_groupoid_map P x xx)
                         x0))
                   (prealg_unit_comp_help
                      P
                      (poly_map P (λ a, a) z)
                    @ maponpaths
                        ((poly_gquot P) (one_type_to_groupoid x))
                        (# (pr1 ((poly_path_groupoid P)
                                   (gquot_functor_obj (one_type_to_groupoid x))))
                           (@poly_act_functor_identity_data
                              P
                              (one_type_to_groupoid
                                 (gquot_functor_obj (one_type_to_groupoid x)))
                              (poly_map
                                 P (gcl (one_type_to_groupoid x))
                                 (poly_map P (λ a : pr1 (gquot_biadj_data x), a) z)))))
                   (poly_gquot_is_gcl
                      P
                      ((pr1 ((poly_path_groupoid P)
                               (gquot_functor_obj (one_type_to_groupoid x))))
                         (poly_map P (λ a : gquot (one_type_to_groupoid x), a)
                                   (poly_map
                                      P
                                      (gcl (one_type_to_groupoid x))
                                      (poly_map P (λ a, a) z))))))).
      }
      etrans.
      {
        apply maponpaths.
        apply step₁.
      }
      etrans.
      {
        exact (!(maponpathscomp
                   (gquot_functor_map (prealg_path_groupoid_map P x xx))
                   (gquot_counit_map x)
                   (gcleq
                      (poly_act_groupoid P (gquot_biadj_data x))
                      (step₁_help z)))).
      }
      etrans.
      {
        apply maponpaths.
        exact (gquot_rec_beta_gcleq
                 (poly_act_groupoid P (gquot_biadj_data x))
                 _ _ _ _ _ _ _ _ _).
      }
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      apply maponpaths.
      do 7 apply maponpaths_2.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 6 apply maponpaths_2.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 5 apply maponpaths_2.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 4 apply maponpaths_2.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 3 apply maponpaths_2.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathscomp0 xx _ _)).
    }
    etrans.
    {
      exact (!(maponpathscomp0 xx _ _)).
    }
    refine (maponpaths (maponpaths xx) _).
    clear xx.
    etrans.
    {
      apply maponpaths.
      do 6 apply maponpaths_2.
      etrans.
      {
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        exact (step₂ z).
      }
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 5 apply maponpaths_2.
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 4 apply maponpaths_2.
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 3 apply maponpaths_2.
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    etrans.
    {
      exact (!(functor_comp ((poly_path_groupoid P) x) _ _)).
    }
    apply maponpaths.
    induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    + apply idpath.
    + apply idpath.
    + induction z as [z | z].
      * apply IHP₁.
      * apply IHP₂.
    + apply (pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.
