(**
Biadjunction when adding a 2-cell to the algebra structure
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

Local Definition TODO {A : UU} : A.
Admitted.

(** General lemmata *)
Definition gquot_functor_map_inl_grpd
           {P Q : poly_code}
           {G : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P G)),
    gquot_inl_grpd z
    =
    gquot_functor_map (inl_grpd_transformation_data_comp P Q G) z.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; simpl ;
       use map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 (idpath _)
                 _) ;
       apply vrefl).
  - exact (λ _, gtrunc _ _ _).
Defined.

Definition gquot_functor_map_inr_grpd
           {P Q : poly_code}
           {G : groupoid}
  : ∏ (z : gquot (poly_act_groupoid Q G)),
    gquot_inr_grpd z
    =
    gquot_functor_map (inr_grpd_transformation_data_comp P Q G) z.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; simpl ;
       use map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 (idpath _)
                 _) ;
       apply vrefl).
  - exact (λ _, gtrunc _ _ _).
Defined.

Definition gquot_functor_map_pr1
           {P Q : poly_code}
           {G : groupoid}
  : ∏ (x : gquot (poly_act_groupoid P G))
      (y : gquot (poly_act_groupoid Q G)),
    x
    =
    gquot_functor_map
      (pr1_grpd_transformation_data_comp P Q G)
      (prod_gquot_comp x y).
Proof.
  use gquot_double_ind_set.
  - exact (λ _ _, gtrunc _ _ _).
  - exact (λ _ _, idpath _).
  - abstract
      (intros a b₁ b₂ g ;
       use map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(maponpaths_for_constant_function _ _))
                 _
                 (idpath _)
                 _) ;
       [ refine (_ @ maponpathscomp _ _ _) ;
         refine (!_) ;
         refine (maponpaths
                   (maponpaths _)
                   (gquot_double_rec'_beta_r_gcleq
                      (poly_act_groupoid P G)
                      (poly_act_groupoid Q G)
                      _ _ _ _ _ _ _ _ _ _ a g)
                   @ _) ;
         exact (gquot_rec_beta_gcleq
                  (poly_act_groupoid (P * Q) G)
                  _ _ _ _ _ _ _ _ _)
       | exact (!(ge _ _)) ]).
  - abstract
      (intros a₁ a₂ b g ;
       use map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(maponpathsidfun _))
                 _
                 (idpath _)
                 _) ;
       [ refine (_ @ maponpathscomp
                      (λ z, prod_gquot_comp z (gcl (poly_act_groupoid Q G) b))
                   (gquot_functor_map (pr1_grpd_transformation_data_comp P Q G)) _) ;
        refine (!_) ;
        refine (maponpaths
                  (maponpaths _)
                  (gquot_double_rec'_beta_l_gcleq
                     (poly_act_groupoid P G)
                     (poly_act_groupoid Q G)
                     _ _ _ _ _ _ _ _ _ _ _ _)
                  @ _) ;
        exact (gquot_rec_beta_gcleq
                 (poly_act_groupoid (P * Q) G)
                 _ _ _ _ _ _ _ _ _)
       | exact (pathscomp0rid _ @ !(pathscomp0lid _)) ]).
Defined.

Definition gquot_functor_map_pr2
           {P Q : poly_code}
           {G : groupoid}
  : ∏ (x : gquot (poly_act_groupoid P G))
      (y : gquot (poly_act_groupoid Q G)),
    y
    =
    gquot_functor_map
      (pr2_grpd_transformation_data_comp P Q G)
      (prod_gquot_comp x y).
Proof.
  use gquot_double_ind_set.
  - exact (λ _ _, gtrunc _ _ _).
  - exact (λ _ _, idpath _).
  - apply TODO.
  - apply TODO.
Defined.

Definition gquot_functor_map_const
           {P : poly_code}
           {T : one_type}
           (t : T)
           {G : groupoid}
  : ∏ (z : gquot (poly_act_groupoid P G)),
    gcl (poly_act_groupoid (C T) G) t
    =
    gquot_functor_map (constant_functor ⦃ P ⦄ t G) z.
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ;
       use map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(maponpaths_for_constant_function _ _))
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 (idpath _)
                 (!_)) ;
       exact (ge _ _)).
  - exact (λ _, gtrunc _ _ _).
Defined.

Definition gquot_functor_pair
           {A P Q R : poly_code}
           (e₁ : endpoint A P Q)
           (e₂ : endpoint A P R)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
  : ∏ (z : gquot (poly_act_groupoid P (pr1 G))),
    (gquot_poly
       (gquot_functor_map
          (sem_endpoint_grpd e₁ G)
          z))
    ,,
    gquot_poly
      (gquot_functor_map
         (sem_endpoint_grpd e₂ G)
         z)
    =
    gquot_poly
      (gquot_functor_map
         (sem_endpoint_grpd (pair e₁ e₂) G)
         z).
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ;
       apply map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 _
                 _
                 (idpath _)
                 _) ;
         [ refine (!_ @ !(maponpaths_pair
                            (λ z, gquot_poly
                                    (gquot_functor_map (sem_endpoint_grpd e₁ G) z))
                            (λ z, gquot_poly
                                    (gquot_functor_map (sem_endpoint_grpd e₂ G) z))
                            (gcleq (poly_act_groupoid P (pr1 G)) g))) ;
           refine (maponpaths
                     (λ z, pathsdirprod z _)
                     (!(maponpathscomp _ _ _)
                       @ maponpaths
                       (maponpaths _)
                       _
                     )
                     @ _) ;
           [ exact (gquot_rec_beta_gcleq
                      (poly_act_groupoid P (pr1 G))
                      _ _ _ _ _ _ _ _
                      g)
           | refine (maponpaths
                       (pathsdirprod _)
                       (!(maponpathscomp _ _ _)
                         @ maponpaths
                         (maponpaths _)
                         _
                    )) ;
             exact (gquot_rec_beta_gcleq
                      (poly_act_groupoid P (pr1 G))
                      _ _ _ _ _ _ _ _
                      g) ]
         | refine (_ @ maponpathscomp _ _ _) ;
           refine (!_) ;
           exact (maponpaths
                    (maponpaths _)
                    (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
         | refine (pathscomp0rid _ @ _ @ !(pathscomp0lid _)) ;
           refine (!_) ;
           exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)]).
  - intro.
    exact (isofhleveldirprod
             3
             _ _
             (poly_act_hlevel Q (make_one_type _ (gtrunc _)))
             (poly_act_hlevel R (make_one_type _ (gtrunc _)))
             _ _).
Defined.

Definition gquot_functor_map_constr
           {A : poly_code}
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
  : ∏ (z : gquot (poly_act_groupoid A (pr1 G))),
    gquot_functor_map (pr2 G) z
    =
    gquot_poly
      (gquot_functor_map
         (sem_endpoint_grpd constr G)
         z).
Proof.
  use gquot_ind_set.
  - exact (λ _, idpath _).
  - abstract
      (intros a₁ a₂ g ; simpl ;
       use map_PathOver ;
       refine (whisker_square
                 (idpath _)
                 (!(gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _))
                 _
                 (idpath _)
                 _) ;
       [ refine (_ @ maponpathscomp _ _ _) ;
         refine (!_) ;
         refine (maponpaths
                   (maponpaths _)
                   (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _)
                 @ _) ;
         apply gquot_rec_beta_gcleq
       | apply pathscomp0rid]).
  - exact (λ _, gtrunc _ _ _).
Defined.

Definition gquot_functor_comp
           {A P Q R : poly_code}
           (e₁ : endpoint A P Q)
           (e₂ : endpoint A Q R)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
  : ∏ (z : gquot (poly_act_groupoid P (pr1 G))),
    gquot_functor_map
      (sem_endpoint_grpd e₂ G)
      ((poly_gquot Q)
         (pr1 G)
         (gquot_poly
            (gquot_functor_map
               (sem_endpoint_grpd e₁ G)
               z)))
    =
    gquot_functor_map
      (pr111 (sem_endpoint_grpd e₁) G ∙ pr111 (sem_endpoint_grpd e₂) G)
      z.
Proof.
  use gquot_ind_set.
  - intro a.
    exact (maponpaths
             (gquot_functor_map _)
             (poly_gquot_gquot_poly _ _)).
  - intros a₁ a₂ g ; simpl.
    apply TODO.
  - intro x.
    exact (gtrunc _ _ _).
Defined.

Definition gquot_endpoint
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (z : poly_act S (gquot (pr1 G)))
  : (sem_endpoint_one_types e) ((total_prealg_gquot A) G) z
    =
    gquot_poly
      (gquot_functor_map
         (sem_endpoint_grpd e G)
         (poly_gquot S (pr1 G) z)).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - (* Identity *)
    refine (!(gquot_poly_poly_gquot _ z) @ _).
    apply maponpaths.
    exact (gquot_functor_identity _ _).
  - (* Composition *)
    simpl.
    cbn.
    etrans.
    {
      apply maponpaths.
      apply IHe₁.
    }
    refine (IHe₂ _ @ _).
    apply maponpaths.
    exact (gquot_functor_comp e₁ e₂ (poly_gquot P (pr1 G) z)).
  - (* Left inclusion *)
    refine (!(gquot_poly_poly_gquot (P + Q) (inl z)) @ _).
    apply maponpaths.
    exact (gquot_functor_map_inl_grpd _).
  - (* Right inclusion *)
    refine (!(gquot_poly_poly_gquot (P + Q) (inr z)) @ _).
    apply maponpaths.
    exact (gquot_functor_map_inr_grpd _).
  - (* Left projection *)
    refine (!(gquot_poly_poly_gquot P (pr1 z)) @ _).
    apply maponpaths.
    exact (gquot_functor_map_pr1
             (poly_gquot P (pr1 G) (pr1 z))
             (poly_gquot Q (pr1 G) (pr2 z))).
  - (* Right projection *)
    refine (!(gquot_poly_poly_gquot Q (pr2 z)) @ _).
    apply maponpaths.
    exact (gquot_functor_map_pr2
             (poly_gquot P (pr1 G) (pr1 z))
             (poly_gquot Q (pr1 G) (pr2 z))).
  - (* Pairing *)
    refine (pathsdirprod (IHe₁ z) (IHe₂ z) @ _).
    exact (gquot_functor_pair e₁ e₂ _).
  - (* Constant *)
    refine (!(gquot_poly_poly_gquot (C T) t) @ _).
    apply maponpaths.
    exact (gquot_functor_map_const t (poly_gquot P (pr1 G) z)).
  - (* Constant map *)
    apply idpath.
  - (* Constructor *)
    exact (gquot_functor_map_constr (poly_gquot A (pr1 G) z)).
Defined.

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
    apply TODO.
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
    - intros G₁ G₂ F hG₁ hG₂ hF.
      use funextsec.
      exact (lift_gquot_add2cell_mor hF).
  Defined.
End LiftGquot.
