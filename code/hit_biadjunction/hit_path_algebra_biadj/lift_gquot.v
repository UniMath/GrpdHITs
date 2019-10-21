(**
Groupoid quotient when adding a 2-cell to the algebra structure
 *)
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
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
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
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.groupoid_endpoints.
Require Import biadjunctions.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import hit_biadjunction.hit_prealgebra_biadj.

Local Open Scope cat.

(** Necessary for computing endpoints wrt `gquot` *)
Definition gquot_endpoint_help_constr
           {A : poly_code}
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           {a₁ a₂ : poly_act_groupoid A (pr1 G)}
           (g : a₁ --> a₂)
  : @PathOver
      _ _ _
      (λ z,
       sem_endpoint_one_types
         constr
         (total_prealg_gquot A G)
         (gquot_poly z)
       =
       gquot_poly (gquot_functor_map (sem_endpoint_grpd constr G) z))
      (maponpaths
         (gquot_functor_map (pr2 G))
         (poly_gquot_gquot_poly (gcl (poly_act_groupoid A (pr1 G)) a₁)))
      (maponpaths
         (gquot_functor_map (pr2 G))
         (poly_gquot_gquot_poly (gcl (poly_act_groupoid A (pr1 G)) a₂)))
      (gcleq (poly_act_groupoid A (pr1 G)) g).
Proof.
  apply map_PathOver.
  refine (whisker_square
            (idpath _)
            _
            _
            (idpath _)
            _).
  - refine (!_).
    etrans.
    {
      exact (!(maponpathscomp
                 (λ z, poly_gquot A (pr1 G) (gquot_poly z))
                 (gquot_functor_map (pr2 G))
                 _)).
    }
    apply maponpaths.
    exact (maponpaths_homot
             poly_gquot_gquot_poly
             (gcleq (poly_act_groupoid A (pr1 G)) g)).
  - refine (!_).
    etrans.
    {
      exact (!(maponpathscomp
                 (gquot_functor_map (sem_endpoint_grpd_data_functor constr G))
                 (gquot_id (pr1 G))
                 (gcleq (poly_act_groupoid A (pr1 G)) g))).
    }
    etrans.
    {
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - simpl.
    unfold square.
    etrans.
    {
      refine (!_).        
      exact (maponpathscomp0
               (gquot_functor_map (pr2 G))
               _
               (poly_gquot_gquot_poly_comp A a₂)).
    }
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0l.
      }
      apply pathscomp0rid.
    }
    etrans.
    {
      etrans.
      {
        do 2 apply maponpaths.
        apply maponpathsidfun.
      }
      etrans.
      {
        exact (maponpathscomp0
                 (gquot_functor_map (pr2 G))
                 (poly_gquot_gquot_poly (gcl (poly_act_groupoid A (pr1 G)) a₁))
                 (gcleq (poly_act_groupoid A (pr1 G)) g)).
      }
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    apply idpath.
Qed.

Definition gquot_endpoint_help_pair
           {A P Q R : poly_code}
           {e₁ : endpoint A P Q}
           {e₂ : endpoint A P R}
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (IHe₁ : ∏ (z : gquot (poly_act_groupoid P (pr1 G))),
                   (sem_endpoint_one_types e₁) ((total_prealg_gquot A) G) (gquot_poly z)
                   =
                   gquot_poly (gquot_functor_map ((sem_endpoint_grpd e₁) G) z))
           (IHe₂ : ∏ (z : gquot (poly_act_groupoid P (pr1 G))),
                   (sem_endpoint_one_types e₂) ((total_prealg_gquot A) G) (gquot_poly z)
                   =
                   gquot_poly (gquot_functor_map ((sem_endpoint_grpd e₂) G) z))
           {a₁ a₂ : poly_act_groupoid P (pr1 G)}
           (g : poly_act_groupoid P (pr1 G) ⟦ a₁, a₂ ⟧)
  : @PathOver
      _ _ _
      (λ z,
       (sem_endpoint_one_types (pair e₁ e₂)) (total_prealg_gquot A G) (gquot_poly z)
       =
       gquot_poly (gquot_functor_map (sem_endpoint_grpd (pair e₁ e₂) G) z))
      ((λ z,
        pathsdirprod
          (IHe₁ (gcl (poly_act_groupoid P (pr1 G)) z))
          (IHe₂ (gcl (poly_act_groupoid P (pr1 G)) z))) a₁)
      ((λ z,
        pathsdirprod
          (IHe₁ (gcl (poly_act_groupoid P (pr1 G)) z))
          (IHe₂ (gcl (poly_act_groupoid P (pr1 G)) z))) a₂)
      (gcleq (poly_act_groupoid P (pr1 G)) g).
Proof.
  apply map_PathOver.
  refine (whisker_square
            (idpath _)
            (_ @ maponpathscomp _ _ _)                 
            (_ @ maponpathscomp _ _ _)                 
            (idpath _)
            _).
  - refine (!_).
    exact (maponpaths_prod_path
             (sem_endpoint_one_types e₁ (total_prealg_gquot A G))
             (sem_endpoint_one_types e₂ (total_prealg_gquot A G))
             _).
  - refine (!_).
    apply maponpaths
    ; exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - unfold square.
    simpl.
    etrans.
    {
      apply pathsdirprod_concat.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      apply pathsdirprod_concat.
    }
    apply paths_pathsdirprod.
    * pose (homotsec_natural'
              IHe₁
              (gcleq (poly_act_groupoid P (pr1 G)) g))
        as h.
      simpl in h.
      refine (_ @ !h @ _).
      ** apply maponpaths.
         refine (!_).
         etrans.
         {
           refine (!_).
           exact (maponpathscomp
                    (gquot_functor_map ((sem_endpoint_grpd e₁) G))
                    gquot_poly
                    (gcleq (poly_act_groupoid P (pr1 G)) g)).
         }
         apply maponpaths.
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      ** apply maponpaths_2.
         refine (!_).
         apply maponpathscomp.
    * pose (homotsec_natural'
              IHe₂
              (gcleq (poly_act_groupoid P (pr1 G)) g))
        as h.
      simpl in h.
      refine (_ @ !h @ _).
      ** apply maponpaths.
         refine (!_).
         etrans.
         {
           refine (!_).
           exact (maponpathscomp
                    (gquot_functor_map ((sem_endpoint_grpd e₂) G))
                    gquot_poly
                    (gcleq (poly_act_groupoid P (pr1 G)) g)).
         }
         apply maponpaths.
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      ** apply maponpaths_2.
         refine (!_).
         apply maponpathscomp.
Qed.

Definition gquot_endpoint_help_comp
           {A P Q R : poly_code}
           {e₁ : endpoint A P Q}
           {e₂ : endpoint A Q R}
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (IHe₁ : ∏ (z : gquot (poly_act_groupoid P (pr1 G))),
                   (sem_endpoint_one_types e₁)
                     ((total_prealg_gquot A) G) (gquot_poly z)
                   =
                   gquot_poly
                     (gquot_functor_map ((sem_endpoint_grpd e₁) G) z))
           (IHe₂ : ∏ (z : gquot (poly_act_groupoid Q (pr1 G))),
                   (sem_endpoint_one_types e₂)
                     ((total_prealg_gquot A) G) (gquot_poly z)
                   =
                   gquot_poly (gquot_functor_map ((sem_endpoint_grpd e₂) G) z))
           {a₁ a₂ : poly_act_groupoid P (pr1 G)}
           (g : poly_act_groupoid P (pr1 G) ⟦ a₁, a₂ ⟧)
  : @PathOver
      _
      (gcl (poly_act_groupoid P (pr1 G)) a₁)
      (gcl (poly_act_groupoid P (pr1 G)) a₂)
      (λ q,
       (sem_endpoint_one_types (comp e₁ e₂))
         (gquot_functor_obj (pr1 G),, prealg_gquot_map A (pr1 G) (pr2 G)) 
         (gquot_poly q)
       =
       gquot_poly (gquot_functor_map ((sem_endpoint_grpd (comp e₁ e₂)) G) q))
      (maponpaths
         (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))
         (IHe₁ (gcl (poly_act_groupoid P (pr1 G)) a₁))
       @ IHe₂
           (gcl
              (poly_act_groupoid Q (pr1 G))
              (sem_endpoint_UU e₁ (λ z, pr12 G z) a₁)))
      (maponpaths
         (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))
         (IHe₁ (gcl (poly_act_groupoid P (pr1 G)) a₂))
       @ IHe₂
           (gcl
              (poly_act_groupoid Q (pr1 G))
              (sem_endpoint_UU e₁ (λ z, pr12 G z) a₂)))
      (gcleq (poly_act_groupoid P (pr1 G)) g).
Proof.
  use map_PathOver.
  refine (whisker_square
            (idpath _)
            (idpath _)
            _
            (idpath _)
            _).
  - refine (_ @ maponpathscomp _ _ _).
    refine (!_).
    apply maponpaths.
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - unfold square.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      simpl.
      pose (homotsec_natural'
              IHe₂
              (gcleq
                 (poly_act_groupoid Q (pr1 G))
                 (sem_endpoint_grpd_data_functor_morphism e₁ (pr2 G) g)))
        as h.
      simpl in h.
      refine (_ @ !h).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        refine (!_).
        exact (maponpathscomp
                 (gquot_functor_map ((sem_endpoint_grpd e₂) G))
                 gquot_poly
                 (gcleq
                    (poly_act_groupoid Q (pr1 G))
                    (sem_endpoint_grpd_data_functor_morphism e₁ (pr2 G) g))).
      }
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp.
      }
      refine (!_).
      apply (maponpathscomp0
               (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))).
    }
    etrans.
    {
      apply maponpaths.
      pose (homotsec_natural'
              IHe₁
              (gcleq
                 (poly_act_groupoid P (pr1 G))
                 g))
        as h.
      refine (_ @ !h).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        refine (!_).
        exact (maponpathscomp
                 (gquot_functor_map ((sem_endpoint_grpd e₁) G))
                 gquot_poly
                 (gcleq (poly_act_groupoid P (pr1 G)) g)).
      }
      apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      apply (maponpathscomp0
               (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))).

    }
    apply maponpaths_2.
    apply (maponpathscomp
             (λ z,
              (sem_endpoint_one_types e₁) ((total_prealg_gquot A) G) (gquot_poly z))
             (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))).
Qed.

Definition gquot_endpoint_help
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
  : ∏ (z : gquot (poly_act_groupoid S (pr1 G))),
    sem_endpoint_one_types e (total_prealg_gquot A G) (gquot_poly z)
    =
    gquot_poly (gquot_functor_map (sem_endpoint_grpd e G) z).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ]
  ; use gquot_ind_set
  ; try (exact (λ _, poly_act_hlevel _ (make_one_type _ (gtrunc _)) _ _)).
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(maponpathsidfun
                      (maponpaths
                         gquot_poly
                         (gcleq (poly_act_groupoid P (pr1 G)) g)))
                  @ maponpathscomp _ _ _)
                      (maponpaths
                         (maponpaths gquot_poly)
                         (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                  @ maponpathscomp _ _ _)
                 (idpath _)
                 _) ;
       apply pathscomp0rid).
  - exact (λ a,
           maponpaths
             (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))
             (IHe₁ (gcl (⦃ P ⦄ (pr1 G)) a))
           @ IHe₂ (gcl _ _)).
  - exact (λ _ _ g, gquot_endpoint_help_comp IHe₁ IHe₂ g).
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (maponpathscomp _ _ _)
                 (maponpaths
                    (maponpaths (gquot_sum gquot_poly gquot_poly))
                    (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                  @ maponpathscomp _ _ _)
                 (idpath _)
                 _) ;
       refine (pathscomp0rid _ @ _) ;
       refine (!_) ;
       refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _) ;
       refine (!_) ;
       exact (maponpathscomp gquot_poly inl _)).
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (maponpathscomp _ _ _)
                 (maponpaths
                    (maponpaths (gquot_sum gquot_poly gquot_poly))
                    (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                  @ maponpathscomp _ _ _)
                 (idpath _)
                 _) ;
       refine (pathscomp0rid _ @ _) ;
       refine (!_) ;
       refine (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _ @ _) ;
       refine (!_) ;
       exact (maponpathscomp gquot_poly inr _)).
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (_ @ maponpathscomp _ _ _)
                 (_ @ maponpathscomp _ _ _)
                 (idpath _)
                 _) ;
         [ refine (!_) ;
           refine (maponpaths
                     _
                     (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                   @ _) ;
           apply maponpaths_pr1_pathsdirprod
         | refine (!_) ;
           apply maponpaths ;
           exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
         | apply pathscomp0rid ]).
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (_ @ maponpathscomp _ _ _)
                 (_ @ maponpathscomp _ _ _)
                 (idpath _)
                 _) ;
       [ refine (!_) ;
         refine (maponpaths
                   _
                   (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _) ;
         exact (maponpaths_pr2_pathsdirprod
                  (maponpaths
                     gquot_poly
                     (gcleq (poly_act_groupoid P (pr1 G)) (pr1 g)))
                  (maponpaths
                     gquot_poly
                     (gcleq (poly_act_groupoid Q (pr1 G)) (pr2 g))))
       | refine (!_) ;
         apply maponpaths ;
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
       | apply pathscomp0rid ]).
  - exact (λ z, pathsdirprod (IHe₁ _) (IHe₂ _)).
  - abstract
      (intros a₁ a₂ g ;
       exact (gquot_endpoint_help_pair IHe₁ IHe₂ g)).
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (_ @ maponpathscomp _ _ _)
                 (_ @ maponpathscomp _ _ _)
                 (idpath _)
                 _) ;
       [ exact (!(maponpaths_for_constant_function _ _))
       | refine (!_) ;
         refine (maponpaths _ _ @ _) ;
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
       | apply idpath]).
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ h ; apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (_ @ maponpathscomp _ _ _)
                 (_ @ maponpathscomp _ _ _)
                 (idpath _)
                 _) ;
       [ refine (!_) ;
         apply maponpaths ;
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
       | refine (!_) ;
         refine (maponpaths _ _ @ _) ;
         exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
       | apply pathscomp0rid]).
  - exact (λ a,
           maponpaths
             (gquot_functor_map (pr2 G))
             (poly_gquot_gquot_poly _)).
  - abstract
      (intros a₁ a₂ g ;
       exact (gquot_endpoint_help_constr g)).
Defined.

Definition gquot_endpoint
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (z : poly_act S (gquot (pr1 G)))
  : sem_endpoint_one_types e (total_prealg_gquot A G) z
    =
    gquot_poly
      (gquot_functor_map
         (sem_endpoint_grpd e G)
         (poly_gquot S (pr1 G) z))
  := maponpaths
       ((sem_endpoint_one_types e) ((total_prealg_gquot A) G))
       (!(gquot_poly_poly_gquot z))
     @ gquot_endpoint_help e (poly_gquot S (pr1 G) z).

(** Lemmata *)
Definition gquot_functor_map_poly_gquot
           {P : poly_code}
           {G₁ G₂ : groupoid}
           {F : G₁ ⟶ G₂}
           (z : poly_act P (gquot G₁))
  : gquot_functor_map (poly_act_functor P F) ((poly_gquot P) G₁ z)
    =
    (poly_gquot P) G₂ (poly_map P (gquot_functor_map F) z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + abstract
        (intros a₁ a₂ g ;
         apply map_PathOver ;
         refine (whisker_square
                   (idpath _)
                   (_ @ maponpathscomp _ _ _)
                   (_ @ maponpathscomp _ _ _)
                   (idpath _)
                   _) ;
         [ refine (!_) ;
           refine (maponpaths _ _ @ _) ;
           exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
         | refine (!_) ;
           refine (maponpaths _ _ @ _) ;
           exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
         | apply pathscomp0rid]).
    + exact (λ _, gtrunc _ _ _).
  - induction z as [z | z].
    + refine (_ @ maponpaths gquot_inl_grpd (IHP₁ z)).
      exact (gquot_inl_grpd_gquot_functor F (poly_gquot P₁ G₁ z)).
    + refine (_ @ maponpaths gquot_inr_grpd (IHP₂ z)).
      exact (gquot_inr_grpd_gquot_functor F (poly_gquot P₂ G₁ z)).
  - refine (_ @ maponpaths (prod_gquot_comp _) (IHP₂ (pr2 z))).
    refine (_ @ maponpaths (λ z, prod_gquot_comp z _) (IHP₁ (pr1 z))).
    exact (prod_gquot_data_comp_nat_help
             _ _ F
             ((poly_gquot P₁) G₁ (pr1 z))
             ((poly_gquot P₂) G₁ (pr2 z))).
Defined.

Definition gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor
           {A S T : poly_code}
           (e : endpoint A S T)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (F : G₁ --> G₂)
           (a : poly_act_groupoid S (pr1 G₁))
  : poly_act_groupoid T (pr1 G₂)
    ⟦ poly_map T (pr11 F) (sem_endpoint_UU e (λ z, pr12 G₁ z) a) ,
      sem_endpoint_UU e (λ z, pr12 G₂ z) (poly_map S (pr11 F) a) ⟧.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - apply poly_act_identity.
  - exact (poly_act_compose
             (IHe₂ _)
             (#(sem_endpoint_grpd e₂ G₂ : _ ⟶ _) (IHe₁ a))).
  - apply poly_act_identity.
  - apply poly_act_identity.
  - apply poly_act_identity.
  - apply poly_act_identity.
  - exact (IHe₁ a ,, IHe₂ a).
  - apply idpath.
  - apply idpath.
  - exact (pr112 F a).
Defined.

Definition gquot_functor_map_gquot_poly_sem_endpoint_grpd_nat
           {A S T : poly_code}
           (e : endpoint A S T)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (F : G₁ --> G₂)
           {a₁ a₂ : poly_act_groupoid S (pr1 G₁)}
           (g : poly_act_groupoid S (pr1 G₁) ⟦ a₁, a₂ ⟧)
  : # (poly_act_functor T (pr1 F))
       (# (sem_endpoint_grpd e G₁ : _ ⟶ _) g)
    · gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e F a₂
    =
    gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e F a₁
    · # (sem_endpoint_grpd e G₂ : _ ⟶ _) (# (poly_act_functor S (pr1 F)) g).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ h | ].
  - exact (poly_act_id_right _ @ !(poly_act_id_left _)).
  - simpl ; cbn.
    simpl in IHe₁, IHe₂ ; cbn in IHe₁, IHe₂.
    etrans.
    {
      apply poly_act_assoc.
    }
    etrans.
    {
      apply maponpaths_2.
      apply IHe₂.
    }
    clear IHe₂.
    etrans.
    {
      refine (!(poly_act_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply (functor_comp (sem_endpoint_grpd e₂ _)).
      }
      apply maponpaths.
      apply IHe₁.
    }
    etrans.
    {
      apply maponpaths.
      apply (functor_comp (sem_endpoint_grpd e₂ _)).
    }
    refine (poly_act_assoc _ _ _ @ _).
    apply idpath.
  - exact (poly_act_id_right _ @ !(poly_act_id_left _)).
  - exact (poly_act_id_right _ @ !(poly_act_id_left _)).
  - exact (poly_act_id_right _ @ !(poly_act_id_left _)).
  - exact (poly_act_id_right _ @ !(poly_act_id_left _)).
  - exact (pathsdirprod (IHe₁ _ _ _) (IHe₂ _ _ _)).
  - apply idpath.
  - apply pathscomp0rid.
  - exact (nat_trans_ax (pr12 F) _ _ g).
Qed.

Definition gquot_functor_map_gquot_poly_sem_endpoint_grpd_help_po
           {A S : poly_code}
           (e : endpoint A S I)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           {F : G₁ --> G₂}
           {a₁ a₂ : poly_act_groupoid S (pr1 G₁)}
           (g : poly_act_groupoid S (pr1 G₁) ⟦ a₁, a₂ ⟧)
  : @PathOver
      _
      (gcl (poly_act_groupoid S (pr1 G₁)) a₁)
      (gcl (poly_act_groupoid S (pr1 G₁)) a₂)
      (λ q,
       gquot_functor_map
         (pr1 F)
         (gquot_id
            (pr1 G₁)
            (gquot_functor_map ((sem_endpoint_grpd e) G₁) q))
       =
       gquot_id
         (pr1 G₂)
         (gquot_functor_map
            ((sem_endpoint_grpd e) G₂)
            (gquot_functor_map (poly_act_functor S (pr1 F)) q)))
    (gcleq (pr1 G₂) (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e F a₁))
    (gcleq (pr1 G₂) (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e F a₂))
    (gcleq (poly_act_groupoid S (pr1 G₁)) g).
Proof.
  use map_PathOver.
  refine (whisker_square
            (idpath _)
            _
            _
            (idpath _)
            _).
  - refine (_
              @ maponpathscomp
              _
              (λ z, gquot_functor_map (pr1 F) (gquot_id (pr1 G₁) z))
              _).
    refine (!_).
    refine (maponpaths
              (maponpaths (λ z, gquot_functor_map (pr1 F) (gquot_id (pr1 G₁) z)))
              (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
              @ _).
    refine (!_).
    refine (_ @ maponpathscomp _ _ _).
    refine (!_).
    refine (maponpaths
              (maponpaths _)
              (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
              @ _).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - refine (_
              @ maponpathscomp
              (gquot_functor_map (poly_act_functor S (pr1 F)))
              (λ z, gquot_id
                      (pr1 G₂)
                      (gquot_functor_map
                         (sem_endpoint_grpd e G₂)
                         z))
              _).
    refine (!_).
    refine (maponpaths
              (maponpaths
                 (λ z, gquot_id
                         (pr1 G₂)
                         (gquot_functor_map
                            (sem_endpoint_grpd e G₂)
                            z)))
              (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
              @ _).
    refine (!_).
    refine (_ @ maponpathscomp _ _ _).
    refine (!_).
    refine (maponpaths
              (maponpaths _)
              (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
              @ _).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - unfold square.
    refine (!(gconcat _ _ _) @ _ @ gconcat _ _ _).
    apply maponpaths.
    exact (gquot_functor_map_gquot_poly_sem_endpoint_grpd_nat e F g).
Qed.

Definition gquot_functor_map_gquot_poly_sem_endpoint_grpd_help
           {A S : poly_code}
           (e : endpoint A S I)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           {F : G₁ --> G₂}
  : ∏ (z : gquot (poly_act_groupoid S (pr1 G₁))),
    gquot_functor_map
      (pr1 F)
      (gquot_poly
         (gquot_functor_map
            (sem_endpoint_grpd e G₁)
            z))
    =
    gquot_id
      (pr1 G₂)
      (gquot_functor_map
         (sem_endpoint_grpd e G₂)
         (gquot_functor_map
            (#⦃ S ⦄ (pr1 F))
            z)).
Proof.
  use gquot_ind_set.
  - intros a.
    apply gcleq.
    exact (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e F a).
  - exact (λ _ _ g, gquot_functor_map_gquot_poly_sem_endpoint_grpd_help_po e g).
  - exact (λ _, gtrunc _ _ _).
Defined.

Definition gquot_functor_map_gquot_poly_sem_endpoint_grpd
           {A S : poly_code}
           (e : endpoint A S I)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           {F : G₁ --> G₂}
           (z : poly_act S (gquot (pr1 G₁)))
  : gquot_functor_map
      (pr1 F)
      (gquot_poly
         (gquot_functor_map
            ((sem_endpoint_grpd e) G₁)
            ((poly_gquot S) (pr1 G₁) z)))
    =
    gquot_poly
      (gquot_functor_map
         ((sem_endpoint_grpd e) G₂)
         ((poly_gquot S) (pr1 G₂) (poly_map S (gquot_functor_map (pr1 F)) z))).
Proof.
  refine (gquot_functor_map_gquot_poly_sem_endpoint_grpd_help e _ @ _).
  do 2 apply maponpaths.
  apply gquot_functor_map_poly_gquot.
Defined.



Definition gquot_poly_gquot_functor_map_help
           {P : poly_code}
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
           (a : poly_act_groupoid P G₁)
  : gquot_poly (gcl (poly_act_groupoid P G₂) (poly_map P F a))
    =
    poly_map
      P
      (gquot_functor_map F)
      (gquot_poly (gcl (poly_act_groupoid P G₁) a)).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction a as [a | a].
    + exact (maponpaths inl (IHP₁ a)).
    + exact (maponpaths inr (IHP₂ a)).
  - exact (pathsdirprod (IHP₁ (pr1 a)) (IHP₂ (pr2 a))).
Defined.

Definition gquot_poly_gquot_functor_map_po
           {P : poly_code}
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
           (a₁ a₂ : poly_act_groupoid P G₁)
           (g : poly_act_groupoid P G₁ ⟦ a₁, a₂ ⟧)
  : @PathOver
      _
      (gcl (poly_act_groupoid P G₁) a₁)
      (gcl (poly_act_groupoid P G₁) a₂)
      (λ q,
       gquot_poly (gquot_functor_map (poly_act_functor P F) q)
       =
       poly_map P (gquot_functor_map F) (gquot_poly q))
      (gquot_poly_gquot_functor_map_help F a₁)
      (gquot_poly_gquot_functor_map_help F a₂)
      (gcleq (poly_act_groupoid P G₁) g).
Proof.
  use map_PathOver.
  refine (whisker_square
            (idpath _)
            (_ @ maponpathscomp _ gquot_poly _)
            (maponpathscomp gquot_poly _ _)
            (idpath _)
            _).
  {
    apply maponpaths.
    refine (!_).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  }
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - simpl in *.
    induction g.
    unfold square ; simpl.
    refine (pathscomp0rid _ @ !_).
    etrans.
    {
      do 2 apply maponpaths.
      apply ge.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply ge.
    }
    apply idpath.
  - simpl.
    refine (whisker_square
              (idpath _)
              (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
              _
              (idpath _)
              _).
    + refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    + apply pathscomp0rid.
  - induction a₁ as [a₁ | a₁], a₂ as [a₂ | a₂].
    + simpl.
      refine (whisker_square
                (idpath _)
                _
                _
                (idpath _)
                _).
      * refine (!_).
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      * refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
        }
        simpl.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply maponpathscomp.
        }
        apply coprodf_path_maponpaths_inl.
      * simpl.
        unfold square.
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply maponpathscomp.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          apply maponpathscomp0.
        }
        apply maponpaths.
        refine (!_).
        exact (IHP₁ _ _ g).
    + exact (fromempty g).
    + exact (fromempty g).
    + simpl.
      refine (whisker_square
                (idpath _)
                _
                _
                (idpath _)
                _).
      * refine (!_).
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      * refine (!_).
        etrans.
        {
          apply maponpaths.
          exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
        }
        simpl.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply maponpathscomp.
        }
        apply coprodf_path_maponpaths_inr.
      * simpl.
        unfold square.
        etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply maponpathscomp.
          }
          refine (!_).
          apply maponpathscomp0.
        }
        refine (!_).
        etrans.
        {
          refine (!_).
          apply maponpathscomp0.
        }
        apply maponpaths.
        refine (!_).
        exact (IHP₂ _ _ g).
  - simpl.
    refine (whisker_square
              (idpath _)
              _
              _
              (idpath _)
              _).
    + refine (!_).
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    + refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      refine (!_).
      apply maponpaths_pathsdirprod.
    + exact (pathsdirprod_concat _ _ _ _
             @ paths_pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _)
             @ !(pathsdirprod_concat _ _ _ _)).
Qed.

Definition gquot_poly_gquot_functor_map
           {P : poly_code}
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
  : ∏ (q : gquot (poly_act_groupoid P G₁)),
    gquot_poly (gquot_functor_map (poly_act_functor P F) q)
    =
    poly_map P (gquot_functor_map F) (gquot_poly q).
Proof.
  use gquot_ind_set.
  - exact (λ a, gquot_poly_gquot_functor_map_help F a).
  - exact (gquot_poly_gquot_functor_map_po F).
  - exact (λ x, poly_act_hlevel P (gquot_functor_obj _) _ _).
Defined.

Definition maponpaths_gquot_poly_poly_gquot_inv_inl
           (P₁ P₂ : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
  : ∏ (z : gquot (poly_act_groupoid P₁ G₁)),
    (maponpaths
       (gquot_sum gquot_poly gquot_poly)
       (gquot_inl_grpd_gquot_functor F z)
    @ inl_gquot_poly P₁ P₂ (gquot_functor_map (poly_act_functor P₁ F) z))
    @ maponpaths inl (gquot_poly_gquot_functor_map F z)
    =
    gquot_poly_gquot_functor_map F (gquot_inl_grpd z)
    @ maponpaths
        (coprodf
           (poly_map P₁ (gquot_functor_map F))
           (poly_map P₂ (gquot_functor_map F)))
        (inl_gquot_poly P₁ P₂ z).
Proof.
  use gquot_ind_prop.
  - exact (λ _, !(pathscomp0rid _)).
  - exact (λ _, poly_act_hlevel (P₁ + P₂) (make_one_type _ (gtrunc _)) _ _ _ _).
Qed.

Definition maponpaths_gquot_poly_poly_gquot_inv_inr
           (P₁ P₂ : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
  : ∏ (z : gquot (poly_act_groupoid P₂ G₁)),
    (maponpaths
       (gquot_sum gquot_poly gquot_poly)
       (gquot_inr_grpd_gquot_functor F z)
    @ inr_gquot_poly P₁ P₂ (gquot_functor_map (poly_act_functor P₂ F) z))
    @ maponpaths inr (gquot_poly_gquot_functor_map F z)
    =
    gquot_poly_gquot_functor_map F (gquot_inr_grpd z)
    @ maponpaths
        (coprodf
           (poly_map P₁ (gquot_functor_map F))
           (poly_map P₂ (gquot_functor_map F)))
        (inr_gquot_poly P₁ P₂ z).
Proof.
  use gquot_ind_prop.
  - exact (λ _, !(pathscomp0rid _)).
  - exact (λ _, poly_act_hlevel (P₁ + P₂) (make_one_type _ (gtrunc _)) _ _ _ _).
Qed.

Definition maponpaths_gquot_poly_poly_gquot_pair
           (P₁ P₂ : poly_code)
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
  : ∏ (z₁ : gquot (poly_act_groupoid P₁ G₁))
      (z₂ : gquot (poly_act_groupoid P₂ G₁)),
    (maponpaths
       (gquot_prod gquot_poly gquot_poly)
       (prod_gquot_data_comp_nat_help G₁ G₂ F z₁ z₂)
    @ gquot_poly_pair
        P₁ P₂
        (gquot_functor_map (poly_act_functor P₁ F) z₁)
        (gquot_functor_map (poly_act_functor P₂ F) z₂))
    @ pathsdirprod
        (gquot_poly_gquot_functor_map F z₁)
        (gquot_poly_gquot_functor_map F z₂)
    =
    gquot_poly_gquot_functor_map
      F
      (prod_gquot_comp z₁ z₂)
    @ maponpaths
        (dirprodf
           (poly_map P₁ (gquot_functor_map F))
           (poly_map P₂ (gquot_functor_map F)))
        (gquot_poly_pair P₁ P₂ z₁ z₂).
Proof.
  use gquot_double_ind_prop.
  - exact (λ _ _, poly_act_hlevel (P₁ * P₂) (make_one_type _ (gtrunc _)) _ _ _ _).
  - exact (λ _ _, !(pathscomp0rid _)).
Qed.    

Definition maponpaths_gquot_poly_poly_gquot_inv
           {P : poly_code}
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
           (z : poly_act P (gquot G₁))
  : maponpaths (poly_map P (gquot_functor_map F)) (! gquot_poly_poly_gquot z)
    =
    ! gquot_poly_poly_gquot (poly_map P (gquot_functor_map F) z)
    @ maponpaths gquot_poly (! gquot_functor_map_poly_gquot z)
    @ gquot_poly_gquot_functor_map F ((poly_gquot P) G₁ z).
Proof.
  use path_inv_rotate_rl.
  etrans.
  {
    apply maponpaths.
    apply maponpathsinv0.
  }
  use path_inv_rotate_lr.
  refine (_ @ path_assoc _ _ _).
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply maponpathsinv0.
  }
  use path_inv_rotate_ll.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (idpath (idpath z)).
  - revert z.
    use gquot_ind_prop.
    + intro a.
      apply idpath.
    + exact (λ _, gtrunc _ _ _ _ _).
  - induction z as [z | z].
    + clear IHP₂.
      etrans.
      {
        apply maponpaths.
        exact (maponpathscomp0
                 (coprodf
                    (poly_map P₁ (gquot_functor_map F))
                    (poly_map P₂ (gquot_functor_map F)))
                 (inl_gquot_poly P₁ P₂ (poly_gquot P₁ G₁ z))
                 (maponpaths inl (gquot_poly_poly_gquot z))).
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply coprodf_path_maponpaths_inl.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp0
                 (gquot_sum gquot_poly gquot_poly)
                 (gquot_inl_grpd_gquot_functor F ((poly_gquot P₁) G₁ z))
                 (maponpaths gquot_inl_grpd (gquot_functor_map_poly_gquot z))).
      }
      specialize (IHP₁ z).
      refine (!(path_assoc
                  (maponpaths
                     (gquot_sum gquot_poly gquot_poly)
                     (gquot_inl_grpd_gquot_functor F ((poly_gquot P₁) G₁ z)))
                  (maponpaths
                     (gquot_sum gquot_poly gquot_poly)
                     (maponpaths
                        gquot_inl_grpd
                        (gquot_functor_map_poly_gquot z)))
                  (gquot_poly_poly_gquot
                     (poly_map (P₁ + P₂) (gquot_functor_map F) (inl z))))
              @ _).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc
                  (maponpaths
                     (gquot_sum gquot_poly gquot_poly)
                     (maponpaths
                        gquot_inl_grpd
                        (gquot_functor_map_poly_gquot z)))
                  (inl_gquot_poly
                     P₁ P₂
                     ((poly_gquot P₁)
                        G₂
                        (poly_map P₁ (gquot_functor_map F) z)))
                  (maponpaths
                     inl
                     (gquot_poly_poly_gquot (poly_map P₁ (gquot_functor_map F) z)))
                @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply (maponpathscomp
                   gquot_inl_grpd
                   (gquot_sum gquot_poly gquot_poly)
                   (gquot_functor_map_poly_gquot z)).
        }
        exact (homotsec_natural'
                 (@inl_gquot_poly P₁ P₂ G₂)
                 (gquot_functor_map_poly_gquot z)).
      }
      etrans.
      {
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply maponpathscomp.
        }
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 inl).
        }
        etrans.
        {
          apply maponpaths.
          exact (!IHP₁).
        }
        apply (maponpathscomp0 inl).
      }
      do 2 refine (path_assoc _ _ _ @ _).
      refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      exact (maponpaths_gquot_poly_poly_gquot_inv_inl P₁ P₂ F _).
    + clear IHP₁.
      etrans.
      {
        apply maponpaths.
        exact (maponpathscomp0
                 (coprodf
                    (poly_map P₁ (gquot_functor_map F))
                    (poly_map P₂ (gquot_functor_map F)))
                 (inr_gquot_poly P₁ P₂ (poly_gquot P₂ G₁ z))
                 (maponpaths inr (gquot_poly_poly_gquot z))).
      }
      etrans.
      {
        do 2 apply maponpaths.
        apply coprodf_path_maponpaths_inr.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp0
                 (gquot_sum gquot_poly gquot_poly)
                 (gquot_inr_grpd_gquot_functor F ((poly_gquot P₂) G₁ z))
                 (maponpaths gquot_inr_grpd (gquot_functor_map_poly_gquot z))).
      }
      specialize (IHP₂ z).
      refine (!(path_assoc
                  (maponpaths
                     (gquot_sum gquot_poly gquot_poly)
                     (gquot_inr_grpd_gquot_functor F ((poly_gquot P₂) G₁ z)))
                  (maponpaths
                     (gquot_sum gquot_poly gquot_poly)
                     (maponpaths
                        gquot_inr_grpd
                        (gquot_functor_map_poly_gquot z)))
                  (gquot_poly_poly_gquot
                     (poly_map (P₁ + P₂) (gquot_functor_map F) (inr z))))
               @ _).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc
                  (maponpaths
                     (gquot_sum gquot_poly gquot_poly)
                     (maponpaths
                        gquot_inr_grpd
                        (gquot_functor_map_poly_gquot z)))
                  (inr_gquot_poly
                     P₁ P₂
                     ((poly_gquot P₂)
                        G₂
                        (poly_map P₂ (gquot_functor_map F) z)))
                  (maponpaths
                     inr
                     (gquot_poly_poly_gquot (poly_map P₂ (gquot_functor_map F) z)))
                @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply (maponpathscomp
                   gquot_inr_grpd
                   (gquot_sum gquot_poly gquot_poly)
                   (gquot_functor_map_poly_gquot z)).
        }
        exact (homotsec_natural'
                 (@inr_gquot_poly P₁ P₂ G₂)
                 (gquot_functor_map_poly_gquot z)).
      }
      etrans.
      {
        apply maponpaths.
        refine (!(path_assoc _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply maponpathscomp.
        }
        etrans.
        {
          refine (!_).
          apply (maponpathscomp0 inr).
        }
        etrans.
        {
          apply maponpaths.
          exact (!IHP₂).
        }
        apply (maponpathscomp0 inr).
      }
      do 2 refine (path_assoc _ _ _ @ _).
      refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      exact (maponpaths_gquot_poly_poly_gquot_inv_inr P₁ P₂ F _).
  - specialize (IHP₁ (pr1 z)).
    specialize (IHP₂ (pr2 z)).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        exact (maponpathscomp0
                 (dirprodf
                    (poly_map P₁ (gquot_functor_map F))
                    (poly_map P₂ (gquot_functor_map F)))
                 (gquot_poly_pair
                    P₁ P₂
                    ((poly_gquot P₁) G₁ (pr1 z))
                    ((poly_gquot P₂) G₁ (pr2 z)))
                 (pathsdirprod
                    (gquot_poly_poly_gquot (pr1 z))
                    (gquot_poly_poly_gquot (pr2 z)))).
      }
      apply maponpaths.
      refine (!_).
      exact (maponpaths_pathsdirprod
               (poly_map P₁ (gquot_functor_map F))
               (poly_map P₂ (gquot_functor_map F))
               (gquot_poly_poly_gquot (pr1 z))
               (gquot_poly_poly_gquot (pr2 z))).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!(path_assoc
                  (prod_gquot_data_comp_nat_help
                     G₁ G₂ F
                     ((poly_gquot P₁) G₁ (pr1 z))
                     ((poly_gquot P₂) G₁ (pr2 z)))
                  (maponpaths
                     (λ q,
                      prod_gquot_comp
                        q
                        (gquot_functor_map
                           (poly_act_functor P₂ F)
                           ((poly_gquot P₂) G₁ (pr2 z))))
                     (gquot_functor_map_poly_gquot (pr1 z)))
                  (maponpaths
                     (λ q,
                      prod_gquot_comp
                        _
                        q)
                     (gquot_functor_map_poly_gquot (pr2 z))))
              @ _).
      apply maponpaths.
      pose (uncurry_ap
              prod_gquot_comp
              (@gquot_functor_map_poly_gquot _ _ _ F (pr1 z))
              (@gquot_functor_map_poly_gquot _ _ _ F (pr2 z)))
        as h.
      unfold uncurry in h.
      exact (!h).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp0.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp
                 (λ x, prod_gquot_comp (pr1 x) (pr2 x))
                 (gquot_prod gquot_poly gquot_poly)
                 (pathsdirprod
                    (gquot_functor_map_poly_gquot (pr1 z))
                    (gquot_functor_map_poly_gquot (pr2 z)))).
      }
      pose (homotsec2_natural
              (λ a b, gquot_poly_pair P₁ P₂ a b)
              (@gquot_functor_map_poly_gquot _ _ _ F (pr1 z))
              (@gquot_functor_map_poly_gquot _ _ _ F (pr2 z)))
        as h.
      exact (!h).
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpaths_pathsdirprod
                   gquot_poly
                   gquot_poly
                   (gquot_functor_map_poly_gquot (pr1 z))
                   (gquot_functor_map_poly_gquot (pr2 z)))).
      }
      etrans.
      {
        apply pathsdirprod_concat.
      }
      exact (!(paths_pathsdirprod IHP₁ IHP₂)).
    }
    clear IHP₁ IHP₂.
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply pathsdirprod_concat.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    exact (maponpaths_gquot_poly_poly_gquot_pair P₁ P₂ F _ _).
Qed.

Definition sem_endpoint_UU_natural_gquot_endpoint_help_gcl_constr
           {P : poly_code}
           {G₁ G₂ : groupoid}
           (F : G₁ ⟶ G₂)
           (a : poly_act P (pr1 G₁))
  : (maponpaths
       (poly_gquot P G₂)
       (gquot_poly_gquot_functor_map_help F a)
    @ !(pr1 (psnaturality_of (poly_gquot P) F)
            (gquot_poly (gcl (poly_act_groupoid P G₁) a))))
    @ maponpaths
        (gquot_functor_map (poly_act_functor P F))
        (poly_gquot_gquot_poly_comp P a)
    =
    poly_gquot_gquot_poly_comp P (poly_map P (pr1 F) a).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction a as [a | a].
    + refine (_ @ maponpaths (maponpaths gquot_inl_grpd) (IHP₁ a)).
      clear IHP₁ IHP₂.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          exact (!(path_assoc _ _ _)).
        }
        apply maponpathscomp0.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp
                   inl
                   (sum_gquot (poly_gquot P₁) (poly_gquot P₂) G₂)
                   (gquot_poly_gquot_functor_map_help F a)).
        }
        exact (!(maponpathscomp
                   (poly_gquot P₁ G₂)
                   gquot_inl_grpd
                   (gquot_poly_gquot_functor_map_help F a))).
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply (maponpathscomp0 gquot_inl_grpd).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (pathscomp_inv
                 (gquot_inl_grpd_gquot_functor
                    F
                    ((poly_gquot P₁)
                       G₁
                       (gquot_poly (gcl (poly_act_groupoid P₁ G₁) a))))
                 (maponpaths
                    gquot_inl_grpd
                    (pr1 (psnaturality_of (poly_gquot P₁) F)
                         (gquot_poly (gcl (poly_act_groupoid P₁ G₁) a))))).
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathsinv0 gquot_inl_grpd).
      }
      apply maponpaths.
      refine (_ @ pathscomp0rid _).
      refine (!_).      
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply (maponpathscomp
                   (gquot_functor_map (poly_act_functor P₁ F))
                   gquot_inl_grpd).
        }
        pose (homotsec_natural'
                (invhomot (@gquot_inl_grpd_gquot_functor P₁ P₂ _ _ F))
                (poly_gquot_gquot_poly_comp P₁ a))
          as h.
        exact h.
      }
      apply maponpaths.
      refine (!_).
      exact (maponpathscomp
               gquot_inl_grpd
               (gquot_functor_map (poly_act_functor (P₁ + P₂) F))
               (poly_gquot_gquot_poly_comp P₁ a)).
    + refine (_ @ maponpaths (maponpaths gquot_inr_grpd) (IHP₂ a)).
      clear IHP₁ IHP₂.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          exact (!(path_assoc _ _ _)).
        }
        apply maponpathscomp0.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths_2.
        etrans.
        {
          exact (maponpathscomp
                   inr
                   (sum_gquot (poly_gquot P₁) (poly_gquot P₂) G₂)
                   (gquot_poly_gquot_functor_map_help F a)).
        }
        exact (!(maponpathscomp
                   (poly_gquot P₂ G₂)
                   gquot_inr_grpd
                   (gquot_poly_gquot_functor_map_help F a))).
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply (maponpathscomp0 gquot_inr_grpd).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (pathscomp_inv
                 (gquot_inr_grpd_gquot_functor
                    F
                    ((poly_gquot P₂)
                       G₁
                       (gquot_poly (gcl (poly_act_groupoid P₂ G₁) a))))
                 (maponpaths
                    gquot_inr_grpd
                    (pr1 (psnaturality_of (poly_gquot P₂) F)
                         (gquot_poly (gcl (poly_act_groupoid P₂ G₁) a))))).
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathsinv0 gquot_inr_grpd).
      }
      apply maponpaths.
      refine (_ @ pathscomp0rid _).
      refine (!_).      
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply (maponpathscomp
                   (gquot_functor_map (poly_act_functor P₂ F))
                   gquot_inr_grpd).
        }
        pose (homotsec_natural'
                (invhomot (@gquot_inr_grpd_gquot_functor P₁ P₂ _ _ F))
                (poly_gquot_gquot_poly_comp P₂ a))
          as h.
        exact h.
      }
      apply maponpaths.
      refine (!_).
      exact (maponpathscomp
               gquot_inr_grpd
               (gquot_functor_map (poly_act_functor (P₁ + P₂) F))
               (poly_gquot_gquot_poly_comp P₂ a)).
  - etrans.
    {
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
      apply maponpaths_2.
      do 2 apply maponpaths.
      refine (maponpaths (λ z, _ @ z) _).
      pose (uncurry_ap
              prod_gquot_comp
              (gquot_commute_prod.IHP₁_help
                 (poly_gquot P₁) F
                 (gquot_poly (gcl (poly_act_groupoid P₁ G₁) (pr1 a))))
              (gquot_commute_prod.IHP₂_help
                 (poly_gquot P₂) F
                 (gquot_poly (gcl (poly_act_groupoid P₂ G₁) (pr2 a)))))
        as h.
      unfold uncurry in h.
      exact (!h).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply pathscomp_inv.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          refine (!_).
          exact (maponpathsinv0
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod
                      (gquot_commute_prod.IHP₁_help
                         (poly_gquot P₁) F
                         (gquot_poly (gcl (poly_act_groupoid P₁ G₁) (pr1 a))))
                      (gquot_commute_prod.IHP₂_help
                         (poly_gquot P₂) F
                         (gquot_poly (gcl (poly_act_groupoid P₂ G₁) (pr2 a)))))).
        }
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp
                   (dirprodf
                      (poly_gquot P₁ G₂)
                      (poly_gquot P₂ G₂))
                   (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                   (pathsdirprod
                      (gquot_poly_gquot_functor_map_help F (pr1 a))
                      (gquot_poly_gquot_functor_map_help F (pr2 a))))).
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
        refine (!_).
        exact (maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (maponpaths
                       (poly_gquot P₁ G₂)
                       (gquot_poly_gquot_functor_map_help F (pr1 a)))
                    (maponpaths
                       (poly_gquot P₂ G₂)
                       (gquot_poly_gquot_functor_map_help F (pr2 a))))
                 (pathsdirprod
                    (! gquot_commute_prod.IHP₁_help (poly_gquot P₁) F
                       (gquot_poly (gcl (poly_act_groupoid P₁ G₁) (pr1 a))))
                    (! gquot_commute_prod.IHP₂_help (poly_gquot P₂) F
                       (gquot_poly (gcl (poly_act_groupoid P₂ G₁) (pr2 a)))))).
      }
      apply maponpaths.
      apply pathsdirprod_concat.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (maponpathscomp
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (gquot_functor_map (poly_act_functor (P₁ * P₂) F))
                 (pathsdirprod
                    (poly_gquot_gquot_poly_comp P₁ (pr1 a))
                    (poly_gquot_gquot_poly_comp P₂ (pr2 a)))).
      }
      pose (homotsec_natural'
              (λ z, ! prod_gquot_data_comp_nat_help G₁ G₂ F (pr1 z) (pr2 z))
              (pathsdirprod
                 (poly_gquot_gquot_poly_comp P₁ (pr1 a))
                 (poly_gquot_gquot_poly_comp P₂ (pr2 a))))
        as h.
      exact (!h).
    }
    etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathscomp
                 (dirprodf
                    (gquot_functor_map (poly_act_functor P₁ F))
                    (gquot_functor_map (poly_act_functor P₂ F)))
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod
                    (poly_gquot_gquot_poly_comp P₁ (pr1 a))
                    (poly_gquot_gquot_poly_comp P₂ (pr2 a))))).
    }
    etrans.
    {
      do 2 apply maponpaths.
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    etrans.
    {
      exact (!(maponpathscomp0
                 (λ z, prod_gquot_comp (pr1 z) (pr2 z))
                 (pathsdirprod _ _)
                 (pathsdirprod
                    (maponpaths
                       (gquot_functor_map (poly_act_functor P₁ F))
                       (poly_gquot_gquot_poly_comp P₁ (pr1 a)))
                    (maponpaths
                       (gquot_functor_map (poly_act_functor P₂ F))
                       (poly_gquot_gquot_poly_comp P₂ (pr2 a)))))).
    }
    refine (!_).
    etrans.
    {
      pose (uncurry_ap
              prod_gquot_comp
              (poly_gquot_gquot_poly_comp P₁ (poly_map P₁ (pr1 F) (pr1 a)))
              (poly_gquot_gquot_poly_comp P₂ (poly_map P₂ (pr1 F) (pr2 a))))
        as h.
      unfold uncurry in h.
      exact (!h).
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply pathsdirprod_concat.
    }
    exact (paths_pathsdirprod (IHP₁ (pr1 a)) (IHP₂ (pr2 a))).
Qed.

Definition sem_endpoint_UU_natural_gquot_endpoint_help_gcl
           {A S T : poly_code}
           (e : endpoint A S T)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (F : total_bicat (disp_alg_bicat ⦃ A ⦄) ⟦ G₁, G₂ ⟧)
           (a : poly_act_groupoid S (pr1 G₁))
  : gquot_endpoint_help
      e
      (gcl (poly_act_groupoid S (pr1 G₂)) (poly_map S (pr11 F) a))
    =
    maponpaths
      (sem_endpoint_UU e (prealg_gquot_map A (pr1 G₂) (pr2 G₂)))
      (gquot_poly_gquot_functor_map_help (pr1 F) a)
    @ !(sem_endpoint_UU_natural
          e (prealg_gquot_cell A (pr2 F))
          (gquot_poly (gcl (poly_act_groupoid S (pr1 G₁)) a)))
    @ maponpaths
        (poly_map T (gquot_functor_map (pr1 F)))
        (gquot_endpoint_help
           e
           (gcl (poly_act_groupoid S (pr1 G₁)) a))
    @ !(gquot_poly_gquot_functor_map_help (pr1 F) (sem_endpoint_UU e (pr12 G₁) a))
    @ maponpaths
        gquot_poly
        (gcleq
           (poly_act_groupoid T (pr1 G₂))
           (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e F a)).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathsidfun.
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply pathsinv0r.
    }
    refine (pathscomp0lid _ @ _).
    etrans.
    {
      apply maponpaths.
      apply ge.
    }
    apply idpath.
  - etrans.
    {
      exact (maponpaths
               (λ z,
                maponpaths
                  (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G₂) (pr2 G₂)))
                  z
                @ gquot_endpoint_help
                    e₂
                    (gcl
                       (poly_act_groupoid Q (pr1 G₂))
                       (sem_endpoint_UU
                          e₁
                          (pr12 G₂)
                          (poly_map P (pr11 F) a))))
               (IHe₁ a)).
    }
    clear IHe₁.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpathscomp.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (pathscomp_inv
               (sem_endpoint_UU_natural
                  e₂
                  (prealg_gquot_cell A (pr2 F))
                  (sem_endpoint_UU
                     e₁
                     (λ x,
                      gquot_functor_map
                        (pr2 G₁)
                        (poly_gquot A (pr1 G₁) x))
                     (gquot_poly (gcl (poly_act_groupoid P (pr1 G₁)) a))))
               (maponpaths
                  (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G₂) (pr2 G₂)))
                  (sem_endpoint_UU_natural
                     e₁
                     (prealg_gquot_cell A (pr2 F))
                     (gquot_poly (gcl (poly_act_groupoid P (pr1 G₁)) a))))).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_2.
      refine (!_).
      apply maponpathsinv0.
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    specialize (IHe₂ (sem_endpoint_UU e₁ (pr12 G₁) a)).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp.
      }
      exact (homotsec_natural'
               (gquot_endpoint_help e₂)
               (gcleq
                  (poly_act_groupoid Q (pr1 G₂))
                  (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e₁ F a))).
    }
    do 2 refine (path_assoc _ _ _ @ _).
    refine (!_).
    etrans.
    {
      do 3 apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (gconcat
                 (poly_act_groupoid R (pr1 G₂))
                 (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor
                    e₂
                    F
                    (sem_endpoint_UU e₁ (pr12 G₁) a))
                 (sem_endpoint_grpd_data_functor_morphism
                    e₂
                    (pr2 G₂)
                    (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e₁ F a))).
      }
      apply maponpathscomp0.
    }
    do 3 refine (path_assoc _ _ _ @ _).
    etrans.
    {
      do 3 apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (maponpathscomp0
                 (poly_map R (gquot_functor_map (pr1 F)))
                 (maponpaths
                    (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G₁) (pr2 G₁)))
                    (gquot_endpoint_help e₁ (gcl (poly_act_groupoid P (pr1 G₁)) a)))
                 (gquot_endpoint_help
                    e₂
                    (gcl (poly_act_groupoid Q (pr1 G₁))
                         (sem_endpoint_UU e₁ (pr12 G₁) a)))).
      }
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        exact (maponpathscomp
                 (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G₁) (pr2 G₁)))
                 (poly_map R (gquot_functor_map (pr1 F)))
                 (gquot_endpoint_help e₁ (gcl (poly_act_groupoid P (pr1 G₁)) a))).
      }
      refine (!_).
      exact (homotsec_natural'
               (invhomot (sem_endpoint_UU_natural e₂ (prealg_gquot_cell A (pr2 F))))
               (gquot_endpoint_help e₁ (gcl (poly_act_groupoid P (pr1 G₁)) a))).
    }
    do 4 refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    do 2 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp.
    }
    apply maponpaths.
    unfold invhomot.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathsinv0.
    }
    refine (!_).
    use path_inv_rotate_rl.
    etrans.
    {
      do 4 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      do 3 refine (!(path_assoc _ _ _) @ _).
      exact (!IHe₂).
    }
    clear IHe₂.
    apply maponpaths.
    refine (!_).
    etrans.
    {
      refine (!_).
      exact (maponpathscomp
               (gquot_functor_map ((sem_endpoint_grpd e₂) G₂))
               gquot_poly
               (gcleq
                  (poly_act_groupoid Q (pr1 G₂))
                  (gquot_functor_map_gquot_poly_sem_endpoint_grpd_mor e₁ F a))).
    }
    apply maponpaths.
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (!(maponpathsinv0 inl _)).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp0 inl _ _)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0r.
    }
    refine (pathscomp0lid _ @ _).
    etrans.
    {
      apply maponpaths.
      apply ge.
    }
    apply idpath.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact (!(maponpathsinv0 inr _)).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp0 inr _ _)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0r.
    }
    refine (pathscomp0lid _ @ _).
    etrans.
    {
      apply maponpaths.
      apply ge.
    }
    apply idpath.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_pr1_pathsdirprod.
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply pathsinv0r.
    }
    refine (pathscomp0lid _ @ _).
    etrans.
    {
      apply maponpaths.
      apply ge.
    }
    apply idpath.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_pr2_pathsdirprod.
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      apply pathsinv0r.
    }
    refine (pathscomp0lid _ @ _).
    etrans.
    {
      apply maponpaths.
      apply ge.
    }
    apply idpath.
  - etrans.
    {
          exact (paths_pathsdirprod (IHe₁ a) (IHe₂ a)).
    }
    clear IHe₁ IHe₂.
    refine (!_).
    etrans.
    {
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
              exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
            }
            etrans.
            {
              apply maponpaths_2.
              apply pathsdirprod_inv.
            }
            apply pathsdirprod_concat.
          }
          etrans.
          {
            apply maponpaths_2.
            refine (!_).
            apply maponpaths_pathsdirprod.
          }
          apply pathsdirprod_concat.
        }
        etrans.
        {
          apply maponpaths_2.
          apply pathsdirprod_inv.
        }
        apply pathsdirprod_concat.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_prod_path.
      }
      apply pathsdirprod_concat.
    }
    apply idpath.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_for_constant_function.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply ge.
    }
    apply idpath.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply ge.
    }
    apply idpath.
  - refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      apply pathscomp_inv.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (maponpathsinv0 (gquot_functor_map (pr2 G₂))).
      }
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathscomp
                   (poly_gquot A (pr1 G₂))
                   (gquot_functor_map (pr2 G₂))
                   (gquot_poly_gquot_functor_map_help (pr1 F) a))).
      }
      refine (!_).
      apply (maponpathscomp0 (gquot_functor_map (pr2 G₂))).
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (maponpathscomp
                 (gquot_functor_map (pr2 G₁))
                 (gquot_functor_map (pr1 F))
                 (poly_gquot_gquot_poly_comp A a)).
      }
      etrans.
      {
        pose (homotsec_natural'
                (invhomot (prealg_gquot_help A (pr1 F) (pr2 F)))
                (poly_gquot_gquot_poly_comp A a))
          as h.
        exact (!h).
      }
      unfold invhomot.
      apply maponpaths_2.
      refine (!_).
      apply maponpathscomp.
    }
    etrans.
    {
      do 2 apply maponpaths.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      apply pathsinv0l.
    }
    etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    etrans.
    {
      refine (!_).
      exact (maponpathscomp0
               (gquot_functor_map (pr2 G₂))
               _
               (maponpaths
                  (gquot_functor_map (poly_act_functor A (pr1 F)))
                  (poly_gquot_gquot_poly_comp A a))).
    }
    exact (maponpaths
             (maponpaths (gquot_functor_map (pr2 G₂)))
             (sem_endpoint_UU_natural_gquot_endpoint_help_gcl_constr (pr1 F) a)).
Qed.

Definition sem_endpoint_UU_natural_gquot_endpoint_help
           {A S : poly_code}
           (e : endpoint A S I)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (F : total_bicat (disp_alg_bicat ⦃ A ⦄) ⟦ G₁, G₂ ⟧)
  : ∏ (q : gquot (poly_act_groupoid S (pr1 G₁))),
    gquot_endpoint_help
      e
      (gquot_functor_map
         (poly_act_functor S (pr1 F))
         q)
    =
    maponpaths
      (sem_endpoint_UU e (prealg_gquot_map A (pr1 G₂) (pr2 G₂)))
      (gquot_poly_gquot_functor_map (pr1 F) q)
    @ !(@sem_endpoint_UU_natural
          _ _ _ e
          _ _
          (prealg_gquot_map A (pr1 G₁) (pr2 G₁))
          (prealg_gquot_map A (pr1 G₂) (pr2 G₂))
          (gquot_functor_map (pr1 F))
          (prealg_gquot_cell A (pr2 F))
          (gquot_poly q))
    @ maponpaths
        (gquot_functor_map (pr1 F))
        (gquot_endpoint_help e q)
    @ gquot_functor_map_gquot_poly_sem_endpoint_grpd_help e q.
Proof.
  use gquot_ind_prop.
  - intros a.
    refine (sem_endpoint_UU_natural_gquot_endpoint_help_gcl e F a @ _).
    do 3 apply maponpaths.
    cbn.
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - exact (λ _, gtrunc _ _ _ _ _).
Qed.  

Definition sem_endpoint_UU_natural_gquot_endpoint
           {A S : poly_code}
           (e : endpoint A S I)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (F : total_bicat (disp_alg_bicat ⦃ A ⦄) ⟦ G₁, G₂ ⟧)
           (z : poly_act S (gquot (pr1 G₁)))
  : sem_endpoint_UU_natural e (prealg_gquot_cell A (pr2 F)) z
    @ gquot_endpoint e (poly_map S (gquot_functor_map (pr1 F)) z)
    =
    maponpaths (gquot_functor_map (pr1 F)) (gquot_endpoint e z)
    @ gquot_functor_map_gquot_poly_sem_endpoint_grpd e z.
Proof.
  unfold gquot_endpoint, gquot_functor_map_gquot_poly_sem_endpoint_grpd.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    apply maponpathscomp0.
  }
  etrans.
  {
    
    do 2 apply maponpaths_2.
    apply maponpathscomp.
  }
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpathscomp.
  }
  
  refine (path_assoc _ _ _ @ _).
  refine (!_).
  use path_rotate_lr.

  assert (gquot_endpoint_help
            e
            ((poly_gquot S) (pr1 G₂) (poly_map S (gquot_functor_map (pr1 F)) z))
          @ !(maponpaths
                (gquot_poly ∘ gquot_functor_map ((sem_endpoint_grpd e) G₂))%functions
                (gquot_functor_map_poly_gquot z))
          =
          maponpaths
            (sem_endpoint_UU
               e
               (prealg_gquot_map A (pr1 G₂) (pr2 G₂)) ∘ gquot_poly)%functions
            (!gquot_functor_map_poly_gquot _)
            @ gquot_endpoint_help e _)
    as X.
  {
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathsinv0
                 (gquot_poly ∘ gquot_functor_map ((sem_endpoint_grpd e) G₂))%functions
                 (gquot_functor_map_poly_gquot z))).
    }
    pose (@homotsec_natural'
            _ _ _ _
            (@gquot_endpoint_help _ _ _ e G₂))
      as h.
    refine (!_).
    apply h.
  }

  refine (!(path_assoc _ _ _) @ _).
  etrans.
  {
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    exact X.
  }
  clear X.

  do 2 refine (path_assoc _ _ _ @ _).

  etrans.
  {
    apply maponpaths.
    exact (sem_endpoint_UU_natural_gquot_endpoint_help e F _).
  }
  do 3 refine (path_assoc _ _ _ @ _).
  do 2 apply maponpaths_2.
  etrans.
  {
    apply maponpaths_2.
    do 2 refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathscomp gquot_poly).
      }
      refine (!_).
      apply (maponpathscomp0 (sem_endpoint_UU e (prealg_gquot_map A (pr1 G₂) (pr2 G₂)))).
    }
    refine (!_).
    apply (maponpathscomp0 (sem_endpoint_UU e (prealg_gquot_map A (pr1 G₂) (pr2 G₂)))).
  }
  use path_inv_rotate_lr.
  refine (!_).
  etrans.
  {
    pose (@homotsec_natural'
            _ _ _ _
            (@sem_endpoint_UU_natural
               _ _ _ e
               _ _
               (prealg_gquot_map A (pr1 G₁) (pr2 G₁))
               (prealg_gquot_map A (pr1 G₂) (pr2 G₂))
               (gquot_functor_map (pr1 F))
               (prealg_gquot_cell A (pr2 F))
         ))
      as h.
    cbn in h.
    apply h.
  }
  apply maponpaths.
  etrans.
  {
    refine (!_).
    apply maponpathscomp.
  }
  apply maponpaths.
  exact (maponpaths_gquot_poly_poly_gquot_inv (pr1 F) z).
Qed.
  
Definition sem_endpoint_UU_natural_gquot_endpoint'
           {A S : poly_code}
           (e : endpoint A S I)
           {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (F : total_bicat (disp_alg_bicat ⦃ A ⦄) ⟦ G₁, G₂ ⟧)
           (z : poly_act S (gquot (pr1 G₁)))
  : maponpaths (gquot_functor_map (pr1 F)) (! gquot_endpoint e z)
    @ pr1 (psnaturality_of (sem_endpoint_one_types e) (# (total_prealg_gquot A) F)) z
    =
    gquot_functor_map_gquot_poly_sem_endpoint_grpd e z
    @ ! gquot_endpoint e (poly_map S (gquot_functor_map (pr1 F)) z).
Proof.
  refine (!_).
  use hornRotation.  
  refine (_ @ path_assoc _ _ _).
  refine (!_).
  etrans.
  {
    do 2 apply maponpaths.
    apply pathsinv0inv0.
  }
  etrans.
  {
    apply maponpaths.
    exact (sem_endpoint_UU_natural_gquot_endpoint e F z).
  }
  refine (path_assoc _ _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      exact (!(maponpathscomp0 (gquot_functor_map (pr1 F)) _ _)).
    }
    apply maponpaths.
    apply pathsinv0l.
  }
  apply idpath.
Qed.

Section LiftGquot.
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

  Definition lift_gquot_add2cell_obj
             (G : total_bicat (disp_alg_bicat ⦃ A ⦄))
             (p : pr1 (sem_endpoint_grpd l G) ⟹ pr1 (sem_endpoint_grpd r G))
             (z : poly_act S (gquot (pr1 G)))
    : sem_endpoint_one_types
        l
        (total_prealg_gquot A G)
        z
      =
      sem_endpoint_one_types
        r
        (total_prealg_gquot A G)
        z
    := gquot_endpoint l z
     @ maponpaths
         gquot_poly
         (gquot_functor_cell p (poly_gquot S (pr1 G) z))
     @ !(gquot_endpoint r z).

  Definition lift_gquot_add2cell_mor_lem
             {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
             {F : G₁ --> G₂}
             {hG₁ : pr1 ((sem_endpoint_grpd l) G₁) ⟹ pr1 ((sem_endpoint_grpd r) G₁)}
             {hG₂ : pr1 ((sem_endpoint_grpd l) G₂) ⟹ pr1 ((sem_endpoint_grpd r) G₂)}
             (hF : @mor_disp _ D1 _ _ hG₁ hG₂ F)
    : ∏ (z : gquot (poly_act_groupoid S (pr1 G₁))),
      maponpaths
        (gquot_functor_map (pr1 F))
        (maponpaths
           gquot_poly
           (gquot_functor_cell hG₁ z))
      @ gquot_functor_map_gquot_poly_sem_endpoint_grpd_help
          r
          z
      =
      gquot_functor_map_gquot_poly_sem_endpoint_grpd_help
        l
        z
      @ maponpaths
          (gquot_id (pr1 G₂))
          (gquot_functor_cell
             hG₂
             (gquot_functor_map
                (poly_act_functor S (pr1 F))
                z)).
  Proof.
    use gquot_ind_prop.
    - intro.
      simpl.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
        }
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      etrans.
      {
        refine (!_).
        apply gconcat.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      etrans.
      {
        refine (!_).
        apply gconcat.
      }
      cbn in hF.
      apply maponpaths.
      refine (!_).
      exact (nat_trans_eq_pointwise hF a).
    - exact (λ _, gtrunc _ _ _ _ _).
  Qed.
    
  Definition lift_gquot_add2cell_mor
             {G₁ G₂ : total_bicat (disp_alg_bicat ⦃ A ⦄)}
             {F : G₁ --> G₂}
             {hG₁ : pr1 ((sem_endpoint_grpd l) G₁) ⟹ pr1 ((sem_endpoint_grpd r) G₁)}
             {hG₂ : pr1 ((sem_endpoint_grpd l) G₂) ⟹ pr1 ((sem_endpoint_grpd r) G₂)}
             (hF : @mor_disp _ D1 _ _ hG₁ hG₂ F)
             (z : poly_act S (gquot (pr1 G₁)))
    : maponpaths
        (gquot_functor_map (pr1 F))
        (lift_gquot_add2cell_obj G₁ hG₁ z)
    @ pr1 (psnaturality_of
             (sem_endpoint_one_types r)
             (# (total_prealg_gquot A) F))
      z
    =
    pr1 (psnaturality_of
           (sem_endpoint_one_types l)
           (# (total_prealg_gquot A) F))
      z
    @ lift_gquot_add2cell_obj G₂ hG₂ (poly_map S (gquot_functor_map (pr1 F)) z).
  Proof.
    unfold lift_gquot_add2cell_obj.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        exact (maponpathscomp0 (gquot_functor_map (pr1 F)) _ _).
      }
      apply maponpaths.
      exact (maponpathscomp0 (gquot_functor_map (pr1 F)) _ _).
    }
    etrans.
    {
      repeat (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
      apply idpath.
    }
    etrans.
    {
      do 2 apply maponpaths.
      exact (sem_endpoint_UU_natural_gquot_endpoint' r F z).
    }
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      refine (path_assoc _ _ _ @ _) ; apply maponpaths_2.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      repeat (refine (path_assoc _ _ _ @ _) ; apply maponpaths_2).
      apply idpath.
    }
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      exact (sem_endpoint_UU_natural_gquot_endpoint l F z).
    }
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _) ; apply maponpaths.
      apply idpath.
    }
    refine (!_).
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _) ; apply maponpaths.
      apply idpath.
    }
    apply maponpaths.
    unfold gquot_functor_map_gquot_poly_sem_endpoint_grpd.
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (lift_gquot_add2cell_mor_lem hF _).
    }
    refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
    apply maponpaths.
    etrans.
    {
      exact (!(maponpathscomp0 (gquot_id (pr1 G₂)) _ _)).
    }
    refine (!_).
    etrans.
    {
      exact (!(maponpathscomp0 (gquot_id (pr1 G₂)) _ _)).
    }
    apply maponpaths.
    exact (homotsec_natural'
             (gquot_functor_cell hG₂)
             (gquot_functor_map_poly_gquot z)).
  Qed.

  Definition lift_gquot_add2cell
    : disp_psfunctor
        D1 D2
        (total_psfunctor
           _ _
           gquot_psfunctor
           (prealg_gquot A)).
  Proof.
    use disp_cell_unit_psfunctor.
    - exact lift_gquot_add2cell_obj.
    - abstract
        (intros G₁ G₂ F hG₁ hG₂ hF ;
         use funextsec ;
         exact (lift_gquot_add2cell_mor hF)).
  Defined.
End LiftGquot.
