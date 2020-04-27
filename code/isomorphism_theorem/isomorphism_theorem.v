(** The first isomorphism theorem for algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Adjunctions.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_homotopies.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.one_types_adjoint_equivalence.
Require Import displayed_algebras.globe_over_lem.
Require Import displayed_algebras.constant_display.
Require Import displayed_algebras.total_algebra.
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.
Require Import isomorphism_theorem.congruence_mapping.
Require Import isomorphism_theorem.image.

Local Open Scope cat.

Definition poly_act_rel_to_eq
           {P : poly_code}
           {X Y : UU}
           (f : X → Y)
           {x y : poly_act P X}
           (p : poly_act_rel P (λ z₁ z₂, f z₁ = f z₂) x y)
  : poly_map P f x = poly_map P f y.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact p.
  - exact p.
  - induction x as [x | x], y as [y | y].
    + exact (maponpaths inl (IHP₁ _ _ p)).
    + exact (fromempty p).
    + exact (fromempty p).
    + exact (maponpaths inr (IHP₂ _ _ p)).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 p)) (IHP₂ _ _ (pr2 p))).
Defined.

Definition poly_act_rel_to_eq_identity
           {P : poly_code}
           {X Y : UU}
           (f : X → Y)
           (x : poly_act P X)
  : poly_act_rel_to_eq f (poly_act_rel_identity _ _ (λ z, idpath _) x)
    =
    idpath _.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (IHP₁ x)).
    + exact (maponpaths (maponpaths inr) (IHP₂ x)).
  - exact (paths_pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Qed.

Definition poly_act_rel_to_eq_comp
           {P : poly_code}
           {X Y : UU}
           (f : X → Y)
           {x y z : poly_act P X}
           (p : poly_act_rel P (λ z₁ z₂, f z₁ = f z₂) x y)
           (q : poly_act_rel P (λ z₁ z₂, f z₁ = f z₂) y z)
  : poly_act_rel_to_eq
      f
      (poly_act_rel_comp
         _
         _
         (λ _ _ _ r₁ r₂, r₁ @ r₂)
         p
         q)
    =
    poly_act_rel_to_eq f p @ poly_act_rel_to_eq f q.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x], y as [y | y].
    + induction z as [z | z].
      * exact (maponpaths _ (IHP₁ _ _ _ p q) @ maponpathscomp0 _ _ _).
      * exact (fromempty q).
    + exact (fromempty p).
    + exact (fromempty p).
    + induction z as [z | z].
      * exact (fromempty q).
      * exact (maponpaths _ (IHP₂ _ _ _ p q) @ maponpathscomp0 _ _ _).
  - exact (paths_pathsdirprod
             (IHP₁ _ _ _ (pr1 p) (pr1 q))
             (IHP₂ _ _ _ (pr2 p) (pr2 q))
           @ !(pathsdirprod_concat _ _ _ _)).
Qed.

Section FirstIsomorphismTheorem.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_one_types Σ}
          (f : X --> Y).

  (**
     Step 1: we define a congruence relation on `X`
     We identitify `x` and `y` if `f x = f y`.
   *)
  Definition congruence_relation_groupoid_for_image
    : congruence_relation_groupoid X.
  Proof.
    use make_congruence_relation_groupoid.
    - exact (λ x y, alg_map_carrier f x = alg_map_carrier f y).
    - exact (λ _ _, one_type_isofhlevel (pr111 Y) _ _).
    - exact (λ _, idpath _).
    - exact (λ _ _ p, !p).
    - exact (λ _ _ _ p q, p @ q).
    - exact (λ _ _ _, idpath _).
    - exact (λ _ _ _, pathscomp0rid _).
    - exact (λ _ _ _ _ _ _ _, path_assoc _ _ _).
    - exact (λ _ _ _, pathsinv0l _).
    - exact (λ _ _ _, pathsinv0r _).
  Defined.

  Definition congruence_relation_ops_for_image
    : congruence_relation_ops X.
  Proof.
    use make_congruence_relation_ops.
    - exact congruence_relation_groupoid_for_image.
    - simpl.
      intros x y p.
      refine (alg_map_commute f x
              @ maponpaths (alg_constr Y) (poly_act_rel_to_eq (alg_map_carrier f) p)
              @ !(alg_map_commute f y)).
    - abstract
        (intro x ; simpl ;
         refine (path_assoc _ _ _ @ _) ;
         use path_inv_rotate_lr ; simpl ;
         refine (_ @ pathscomp0rid _) ;
         apply maponpaths ;
         refine (_ @ maponpaths_idpath) ;
         apply maponpaths ;
         apply poly_act_rel_to_eq_identity).
    - abstract
        (simpl ; intros x y z p q ;
         refine (_ @ path_assoc _ _ _) ;
         apply maponpaths ;
         do 2 refine (_ @ !(path_assoc _ _ _)) ;
         apply maponpaths_2 ;
         refine (!_) ;
         etrans ;
         [ apply maponpaths_2 ;
           refine (!(path_assoc _ _ _) @ _) ;
           refine (maponpaths (λ z, _ @ z) (pathsinv0l _) @ _) ;
           apply pathscomp0rid
         | refine (!(maponpathscomp0 _ _ _) @ _) ;
           apply maponpaths ;
           refine (!_) ;
           apply poly_act_rel_to_eq_comp ]).
  Defined.

  Definition eq_to_cong_rel_image
             {x₁ x₂ : alg_carrier X}
             (p : x₁ = x₂)
    : eq_to_cong_rel
        congruence_relation_groupoid_for_image
        p
      =
      maponpaths
        (alg_map_carrier f)
        p.
  Proof.
    induction p.
    apply idpath.
  Qed.

  Definition congruence_relation_for_image_morphism
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_map P (alg_map_carrier f) x
                  =
                  poly_map P (alg_map_carrier f) y)
    : poly_act_morphism
        P
        (make_groupoid_algebra_carrier congruence_relation_ops_for_image)
        x
        y.
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - exact p.
    - exact p.
    - induction x as [x | x], y as [y | y].
      + exact (IHP₁
                 x y
                 (ii1_injectivity
                    (poly_map P₁ (alg_map_carrier f) x)
                    (poly_map P₁ (alg_map_carrier f) y)
                    p)).
      + exact (negpathsii1ii2 _ _ p).
      + exact (negpathsii2ii1 _ _ p).
      + exact (IHP₂
                 x y
                 (ii2_injectivity
                    (poly_map P₂ (alg_map_carrier f) x)
                    (poly_map P₂ (alg_map_carrier f) y)
                    p)).
    - exact (IHP₁ _ _ (maponpaths pr1 p)
             ,,
             IHP₂ _ _ (maponpaths dirprod_pr2 p)).
  Defined.

  Definition congruence_relation_for_image_morphism_idpath
             {P : poly_code}
             (x : poly_act P (alg_carrier X))
    : congruence_relation_for_image_morphism
        (idpath (poly_map P (alg_map_carrier f) x))
      =
      @poly_act_identity
        _
        (make_groupoid_algebra_carrier congruence_relation_groupoid_for_image)
        x.
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x].
      + apply IHP₁.
      + apply IHP₂.
    - exact (pathsdirprod (IHP₁ _) (IHP₂ _)).
  Qed.

  Definition congruence_relation_for_image_morphism_inv
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_map P (alg_map_carrier f) x
                  =
                  poly_map P (alg_map_carrier f) y)
    : congruence_relation_for_image_morphism (!p)
      =
      poly_act_inverse (congruence_relation_for_image_morphism p).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - exact (!(pathscomp0rid _)).
    - induction x as [x | x], y as [y | y].
      + simpl.
        refine (_ @ IHP₁ _ _ _).
        apply maponpaths.
        apply ii1_injectivity_inv.
      + induction (negpathsii1ii2 _ _ p).
      + induction (negpathsii2ii1 _ _ p).
      + simpl.
        refine (_ @ IHP₂ _ _ _).
        apply maponpaths.
        apply ii2_injectivity_inv.
    - simpl.
      refine (pathsdirprod (_ @ IHP₁ _ _ _) (_ @ IHP₂ _ _ _))
      ; apply maponpaths.
      + exact (maponpathsinv0 pr1 p).
      + exact (maponpathsinv0 dirprod_pr2 p).
  Qed.

  Definition congruence_relation_for_image_morphism_concat
             {P : poly_code}
             {x y z : poly_act P (alg_carrier X)}
             (p : poly_map P (alg_map_carrier f) x
                  =
                  poly_map P (alg_map_carrier f) y)
             (q : poly_map P (alg_map_carrier f) y
                  =
                  poly_map P (alg_map_carrier f) z)
    : congruence_relation_for_image_morphism (p @ q)
      =
      poly_act_compose
        (congruence_relation_for_image_morphism p)
        (congruence_relation_for_image_morphism q).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x], y as [y | y].
      + induction z as [z | z].
        * simpl.
          refine (_ @ IHP₁ _ _ _ _ _).
          apply maponpaths.
          apply ii1_injectivity_concat.
        * induction (negpathsii1ii2 _ _ q).
      + induction (negpathsii1ii2 _ _ p).
      + induction (negpathsii2ii1 _ _ p).
      + induction z as [z | z].
        * induction (negpathsii2ii1 _ _ q).
        * simpl.
          refine (_ @ IHP₂ _ _ _ _ _).
          apply maponpaths.
          apply ii2_injectivity_concat.
    - simpl.
      refine (pathsdirprod (_ @ IHP₁ _ _ _ _ _) (_ @ IHP₂ _ _ _ _ _))
      ; apply maponpaths.
      + exact (maponpathscomp0 pr1 p q).
      + exact (maponpathscomp0 dirprod_pr2 p q).
  Qed.
  
  Definition congruence_relation_for_image_path
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_act_morphism
                    P
                    (make_groupoid_algebra_carrier congruence_relation_ops_for_image)
                    x
                    y)
    : poly_map P (alg_map_carrier f) x
      =
      poly_map P (alg_map_carrier f) y
    := poly_act_rel_to_eq _ p.

  Definition congruence_relation_for_image_morphism_path
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_act_morphism
                    P
                    (make_groupoid_algebra_carrier congruence_relation_ops_for_image)
                    x
                    y)
    : congruence_relation_for_image_morphism
        (congruence_relation_for_image_path p)
      =
      p.
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x], y as [y | y].
      + simpl.
        etrans.
        {
          apply maponpaths.
          apply ii1_injectivity_inl.
        }
        apply IHP₁.
      + induction p.
      + induction p.
      + simpl.
        etrans.
        {
          apply maponpaths.
          apply ii2_injectivity_inr.
        }
        apply IHP₂.
    - simpl.
      apply pathsdirprod.
      + refine (_  @ IHP₁ _ _ _).
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      + refine (_  @ IHP₂ _ _ _).
        apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
  Qed.

  Definition congruence_relation_for_image_path_morphism
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_map P (alg_map_carrier f) x
                  =
                  poly_map P (alg_map_carrier f) y)
    : congruence_relation_for_image_path
        (congruence_relation_for_image_morphism p)
      =
      p.
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x], y as [y | y].
      + simpl.
        etrans.
        {
          apply maponpaths.
          apply IHP₁.
        }
        apply inl_ii1_injectivity.
      + induction (negpathsii1ii2 _ _ p).
      + induction (negpathsii2ii1 _ _ p).        
      + simpl.
        etrans.
        {
          apply maponpaths.
          apply IHP₂.
        }
        apply inr_ii2_injectivity.
    - exact (paths_pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _) @ !(pathsdirprod_eta p)).
  Qed.

  Definition congruence_relation_for_image_morphism_functor
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             {x y : poly_act P (alg_carrier X)}
             (p : poly_map P (alg_map_carrier f) x
                  =
                  poly_map P (alg_map_carrier f) y)
    : sem_endpoint_grpd_data_functor_morphism
        e
        (make_groupoid_algebra_operations congruence_relation_ops_for_image)
        (congruence_relation_for_image_morphism p)
      =
      congruence_relation_for_image_morphism
        (sem_endpoint_UU_natural e (alg_map_commute f) x
         @ maponpaths (sem_endpoint_UU e (alg_constr Y)) p
         @ !(sem_endpoint_UU_natural e (alg_map_commute f) y)).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | C₁ C₂ g | ].
    - simpl.
      apply maponpaths.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      apply maponpathsidfun.
    - simpl.
      etrans.
      {
        apply maponpaths.
        apply IHe₁.
      }
      clear IHe₁.
      refine (IHe₂ _ _ _ @ _).
      apply maponpaths.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathscomp_inv.
          }
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 _ _)).
          }
          etrans.
          {
            apply maponpaths_2.
            exact (!(maponpathscomp _ _ _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact (!(maponpathscomp0 _ _ _)).
      }
      apply idpath.
    - simpl.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply pathscomp0rid.
      }
      apply ii1_injectivity_inl.
    - simpl.
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply pathscomp0rid.
      }
      apply ii2_injectivity_inr.
    - simpl.
      apply maponpaths.
      exact (!(pathscomp0rid _)).
    - simpl.
      apply maponpaths.
      exact (!(pathscomp0rid _)).
    - simpl.
      apply pathsdirprod.
      + refine (IHe₁ _ _ _ @ _).
        apply maponpaths.
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
                apply pathsdirprod_inv.
              }
              etrans.
              {
                apply maponpaths_2.
                apply maponpaths_prod_path.
              }
              apply pathsdirprod_concat.
            }
            apply pathsdirprod_concat.
          }
          apply maponpaths_pr1_pathsdirprod.
        }
        apply idpath.
      + refine (IHe₂ _ _ _ @ _).
        apply maponpaths.
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
                apply pathsdirprod_inv.
              }
              etrans.
              {
                apply maponpaths_2.
                apply maponpaths_prod_path.
              }
              apply pathsdirprod_concat.
            }
            apply pathsdirprod_concat.
          }
          apply maponpaths_pr2_pathsdirprod.
        }
        apply idpath.
    - simpl.
      refine (_ @ !(pathscomp0rid _)).
      exact (!(maponpaths_for_constant_function _ _)).
    - simpl.
      exact (!(pathscomp0rid _)).
    - simpl ; cbn.
      apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply congruence_relation_for_image_path_morphism.
  Qed.
      
  Local Lemma lem₁
        {P : poly_code}
        {x y : poly_act P (alg_carrier X)}
        (p : poly_map P (alg_map_carrier f) x
             =
             poly_map P (alg_map_carrier f) y)
    : poly_act_rel_to_eq
        (alg_map_carrier f)
        (congruence_relation_for_image_morphism p)
      =
      p.
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x], y as [y | y].
      + simpl in IHP₁ ; simpl.
        etrans.
        {
          apply maponpaths.
          apply IHP₁.
        }
        apply inl_ii1_injectivity.
      + induction (negpathsii1ii2 _ _ p).
      + induction (negpathsii2ii1 _ _ p).
      + simpl in IHP₁ ; simpl.
        etrans.
        {
          apply maponpaths.
          apply IHP₂.
        }
        apply inr_ii2_injectivity.
    - exact (paths_pathsdirprod
               (IHP₁ _ _ (maponpaths pr1 p))
               (IHP₂ _ _ (maponpaths dirprod_pr2 p))
             @ !(pathsdirprod_eta p)).
  Qed.

  Local Lemma lem₂
        {P : poly_code}
        {x y : poly_act P (alg_carrier X)}
        (p : poly_act_morphism
               P
               (make_groupoid_algebra_carrier congruence_relation_ops_for_image)
               x y)
    : congruence_relation_for_image_morphism (poly_act_rel_to_eq (alg_map_carrier f) p)
      =
      p.
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - apply idpath.
    - apply idpath.
    - induction x as [x | x], y as [y | y].
      + simpl.
        etrans.
        {
          apply maponpaths.
          apply ii1_injectivity_inl.
        }
        apply IHP₁.
      + induction p.
      + induction p.
      + simpl.
        etrans.
        {
          apply maponpaths.
          apply ii2_injectivity_inr.
        }
        apply IHP₂.
    - simpl.
      apply pathsdirprod.
      + etrans.
        {
          apply maponpaths.
          apply maponpaths_pr1_pathsdirprod.
        }
        apply IHP₁.
      + etrans.
        {
          apply maponpaths.
          apply maponpaths_pr2_pathsdirprod.
        }
        apply IHP₂.
  Qed.

  Definition congruence_relation_for_image_endpoint
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             {x y : poly_act P (alg_carrier X)}
             (p : poly_act_morphism
                    P
                    (make_groupoid_algebra_carrier
                       congruence_relation_groupoid_for_image)
                    x y)
    : sem_endpoint_grpd_data_functor_morphism
        e
        (make_groupoid_algebra_operations congruence_relation_ops_for_image)
        p
      =
      congruence_relation_for_image_morphism
        (sem_endpoint_UU_natural
           e
           (alg_map_commute f)
           x
         @ maponpaths
             (sem_endpoint_UU e (alg_constr Y))
             (poly_act_rel_to_eq _ p)
         @ !(sem_endpoint_UU_natural
               e
               (alg_map_commute f)
               y)).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | C₁ C₂ g | ].
    - simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        apply maponpathsidfun.
      }
      apply lem₂.
    - simpl.
      refine (IHe₂ _ _ _ @ _) ; clear IHe₂.
      apply maponpaths.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        apply pathscomp_inv.
      }
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathsinv0 _ _)).
        }
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp _ _ _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply IHe₁.
      }
      clear IHe₁.
      etrans.
      {
        apply lem₁.
      }
      apply path_assoc.
    - simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply pathscomp0rid.
        }
        apply ii1_injectivity_inl.
      }
      apply lem₂.
    - simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply pathscomp0rid.
        }
        apply ii2_injectivity_inr.
      }
      apply lem₂.
    - simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        apply maponpaths_pr1_pathsdirprod.
      }
      apply lem₂.
    - simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        apply maponpaths_pr2_pathsdirprod.
      }
      apply lem₂.
    - simpl.
      refine (pathsdirprod _ _).
      + refine (IHe₁ _ _ _ @ _).
        apply maponpaths.
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
                apply pathsdirprod_inv.
              }
              etrans.
              {
                apply maponpaths_2.
                apply maponpaths_prod_path.
              }
              apply pathsdirprod_concat.
            }
            apply pathsdirprod_concat.
          }
          apply maponpaths_pr1_pathsdirprod.
        }
        apply idpath.
      + refine (IHe₂ _ _ _ @ _).
        apply maponpaths.
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
                apply pathsdirprod_inv.
              }
              etrans.
              {
                apply maponpaths_2.
                apply maponpaths_prod_path.
              }
              apply pathsdirprod_concat.
            }
            apply pathsdirprod_concat.
          }
          apply maponpaths_pr2_pathsdirprod.
        }
        apply idpath.
    - simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_for_constant_function.
      }
      apply idpath.
    - exact (!(pathscomp0rid _)).
    - apply idpath.
  Qed.

  Definition congruence_relation_for_image_is_congruence_is_nat
    : is_congruence_relation_nat congruence_relation_ops_for_image.
  Proof.
    intros j x y p.
    cbn ; cbn in p.
    etrans.
    {
      apply maponpaths_2.
      exact (congruence_relation_for_image_endpoint (path_left Σ j) p).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (congruence_relation_for_image_endpoint (path_right Σ j) p).
    }
    etrans.
    {
      apply maponpaths_2.
      apply eq_to_cong_rel_image.
    }    
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (alg_map_path f j x).
    }
    refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
    apply maponpaths.
    refine (path_assoc _ _ _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply eq_to_cong_rel_image.
    }
    use path_inv_rotate_rr.
    do 2 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (alg_map_path f j y).
      }
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0l.
    }
    simpl.
    apply homotsec_natural'.
  Qed.
  
  Definition congruence_relation_nat_for_image
    : congruence_relation_nat X.
  Proof.
    use make_congruence_relation_nat.
    - exact congruence_relation_ops_for_image.
    - exact congruence_relation_for_image_is_congruence_is_nat.
  Defined.

  Definition congruence_relation_homot_endpoint
             {Q T TR : poly_code}
             {al ar : endpoint (point_constr Σ) Q TR}
             {sl sr : endpoint (point_constr Σ) Q T}
             (h : homot_endpoint
                    (path_left Σ) (path_right Σ)
                    al ar
                    sl sr)
             (x : poly_act Q (alg_carrier X))
             (p : poly_act_morphism
                    TR
                    (make_groupoid_algebra_carrier congruence_relation_groupoid_for_image)
                    (sem_endpoint_UU al (alg_constr X) x)
                    (sem_endpoint_UU ar (alg_constr X) x))
    : sem_homot_endpoint_grpd
        h
        (make_groupoid_prealgebra congruence_relation_nat_for_image)
        (make_groupoid_path_algebra_path congruence_relation_nat_for_image)
        x
        p
      =
      congruence_relation_for_image_morphism
        (sem_endpoint_UU_natural sl (alg_map_commute f) x
         @ sem_homot_endpoint_UU
             h
             (alg_carrier Y)
             (alg_constr Y)
             (alg_path Y)
             _
             (!(sem_endpoint_UU_natural al (alg_map_commute f) x)
              @ congruence_relation_for_image_path p
              @ sem_endpoint_UU_natural ar (alg_map_commute f) x)
         @ !(sem_endpoint_UU_natural sr (alg_map_commute f) x)).
  Proof.
    induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                    | T₁ T₂ e₁ e₂ e₃ h IHh
                    | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                    | P R e₁ e₂ | P R e₁ e₂
                    | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                    | P₁ P₂ P₃ e₁ e₂ e₃
                    | Z z T e | j e | ].
    - (* identity *)
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply congruence_relation_for_image_morphism_idpath.
    - (* symmetry *)
      refine (maponpaths poly_act_inverse IHh @ _).
      refine (!(congruence_relation_for_image_morphism_inv _) @ _).
      apply maponpaths.
      refine (pathscomp_inv _ _ @ _).
      refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      refine (pathscomp_inv _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0inv0.
    - (* transitivity *)
      refine (maponpaths (poly_act_compose _) IHh₂ @ _).
      refine (maponpaths (λ z, poly_act_compose z _) IHh₁ @ _).
      etrans.
      {
        refine (!_).
        apply congruence_relation_for_image_morphism_concat.
      }
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
      apply maponpaths.
      etrans.
      {
        refine (path_assoc _ _ _ @ _) ; apply maponpaths_2.
        apply pathsinv0l.
      }
      apply idpath.
    - (* ap with endpoint *)
      refine (maponpaths
                (sem_endpoint_grpd_data_functor_morphism
                   e₃
                   (make_groupoid_algebra_operations congruence_relation_ops_for_image))
                IHh
              @ _).
      clear IHh.
      refine (congruence_relation_for_image_morphism_functor _ _ @ _).
      apply maponpaths.
      refine (_ @ path_assoc _ _ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply pathscomp_inv.
          }
          refine (path_assoc _ _ _ @ _).
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0
                       (sem_endpoint_UU e₃ prealg_constr)
                       (sem_endpoint_UU_natural e₂ (alg_map_commute f) x))).
          }
          exact (!(maponpathscomp0
                     (sem_endpoint_UU e₃ (alg_constr Y))
                     _
                     (!(sem_endpoint_UU_natural e₂ (alg_map_commute f) x)))).
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        exact (!(maponpathscomp0 _ _ _)).
      }
      apply idpath.
    - (* associativity *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          refine (!(path_assoc _ _ _) @ _).
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp _ _ _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        apply pathsinv0r.
      }
      apply congruence_relation_for_image_morphism_idpath.
    - (* left identity *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply pathscomp0rid.
        }
        apply pathsinv0r.
      }
      apply congruence_relation_for_image_morphism_idpath.
    - (* right identity *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathsidfun.
        }
        apply pathsinv0r.
      }
      apply congruence_relation_for_image_morphism_idpath.
    - (* first projection *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths_pr1_pathsdirprod.
        }
        apply pathsinv0r.
      }
      apply congruence_relation_for_image_morphism_idpath.
    - (* second projection *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          apply maponpaths_pr2_pathsdirprod.
        }
        apply pathsinv0r.
      }
      apply congruence_relation_for_image_morphism_idpath.
    - (* pair of endpoints *)
      use pathsdirprod.
      + refine (IHh₁ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply pathsdirprod_inv.
            }
            apply pathsdirprod_concat.
          }
          apply pathsdirprod_concat.
        }
        apply maponpaths_pr1_pathsdirprod.
      + refine (IHh₂ @ _).
        apply maponpaths.
        refine (!_).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply pathsdirprod_inv.
            }
            apply pathsdirprod_concat.
          }
          apply pathsdirprod_concat.
        }
        apply maponpaths_pr2_pathsdirprod.
    - (* composition before pair *)
      simpl.
      apply pathsdirprod.
      + refine (!_).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply pathsdirprod_inv.
            }
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                apply maponpaths_prod_path.
              }
              apply pathsdirprod_concat.
            }
            apply pathsdirprod_concat.
          }
          etrans.
          {
            apply maponpaths_pr1_pathsdirprod.
          }
          apply pathsinv0r.
        }
        apply congruence_relation_for_image_morphism_idpath.
      + refine (!_).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths.
              apply pathsdirprod_inv.
            }
            etrans.
            {
              apply maponpaths_2.
              etrans.
              {
                apply maponpaths.
                apply maponpaths_prod_path.
              }
              apply pathsdirprod_concat.
            }
            apply pathsdirprod_concat.
          }
          etrans.
          {
            apply maponpaths_pr2_pathsdirprod.
          }
          apply pathsinv0r.
        }
        apply congruence_relation_for_image_morphism_idpath.
    - (* composition with constant *)
      simpl.
      refine (!_).
      refine (pathscomp0rid _ @ _).
      apply maponpaths_for_constant_function.
    - (* path constructor *)
      simpl.
      cbn.
      unfold make_groupoid_path_algebra_nat_trans_data.
      etrans.
      {
        apply (eq_to_cong_rel_image (alg_path X j (sem_endpoint_UU e _ x))).
      }
      refine (_ @ !(path_assoc _ _ _)).
      use path_inv_rotate_rr.
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply alg_map_path.
      }
      refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
      apply maponpaths.
      refine (!_).
      apply homotsec_natural'.
    - (* path argument *)
      simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          refine (path_assoc _ _ _ @ _) ; apply maponpaths_2.
          apply pathsinv0r.
        }
        simpl.
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          apply pathsinv0r.
        }
        apply pathscomp0rid.
      }
      apply congruence_relation_for_image_morphism_path.
  Qed.
  
  Definition congruence_relation_for_image_is_congruence
    : is_congruence_relation congruence_relation_nat_for_image.
  Proof.
    intros j x p.
    etrans.
    {
      apply congruence_relation_homot_endpoint.
    }
    refine (!_).
    etrans.
    {
      apply congruence_relation_homot_endpoint.
    }
    do 2 apply maponpaths.
    apply maponpaths_2.
    refine (!_).
    apply alg_homot.
  Qed.
  
  Definition congruence_relation_for_image
    : congruence_relation X.
  Proof.
    use make_congruence_relation.
    - exact congruence_relation_nat_for_image.
    - exact congruence_relation_for_image_is_congruence.
  Defined.

  (** Notation for the quotient *)
  Local Notation "'X/R'" := (quotient_of_congruence congruence_relation_for_image).
  
  (**
     Step 2: Define a map from the quotient to `im f`.
   *)
  Definition map_gquot_to_image_on_path
             {a b : alg_carrier X}
             (p : alg_map_carrier f a = alg_map_carrier f b)
    : image_inj_comp f a = image_inj_comp f b.
  Proof.
    use PathOverToTotalPath'.
    - exact p.
    - abstract
        (simpl ;
         apply PathOver_path_hprop ;
         intro ;
         apply ishinh).
  Defined.

  Definition map_gquot_to_image_on_identity
             (a : alg_carrier X)
    : map_gquot_to_image_on_path (cong_rel_id congruence_relation_for_image a)
      =
      idpath _.
  Proof.
    refine (_ @ !(PathOverToTotalPath'_eta _)).
    use globe_over_to_homot.
    - apply idpath.
    - apply path_globe_over_hset.
      intro.
      apply isasetaprop.
      apply ishinh.
  Qed.

  Definition map_gquot_to_image_on_concat
             {a₁ a₂ a₃ : alg_carrier X}
             (g₁ : alg_map_carrier f a₁ = alg_map_carrier f a₂)
             (g₂ : alg_map_carrier f a₂ = alg_map_carrier f a₃)
    : map_gquot_to_image_on_path
        (cong_rel_comp congruence_relation_groupoid_for_image g₁ g₂)
      =
      map_gquot_to_image_on_path g₁ @ map_gquot_to_image_on_path g₂.
  Proof.
    refine (_ @ !(PathOverToTotalPath'_comp _ _)).
    refine (_ @ !(PathOverToTotalPath'_eta _)).
    use globe_over_to_homot.
    - unfold globe.
      unfold cong_rel_comp.
      simpl.
      refine (!_).
      apply (@maponpaths_pr1_PathOverToTotalPath' _ _ (_ ,, _) (_ ,, _)).
    - apply path_globe_over_hset.
      intro.
      apply isasetaprop.
      apply ishinh.
  Qed.

  Definition map_gquot_to_image_on_commute_lem
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_act_rel
                    P
                    (λ z₁ z₂, alg_map_carrier f z₁ = alg_map_carrier f z₂)
                    x y)
    : !(poly_comp P (image_inj_comp f) pr1 x)
      @ maponpaths (poly_pr1 P) (poly_rel_to_eq_fun (@map_gquot_to_image_on_path) p)
      =
      poly_act_rel_to_eq (alg_map_carrier f) p
      @ !(poly_comp P (image_inj_comp f) pr1 y).
  Proof.
    induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
    - refine (_ @ !(pathscomp0rid _)).
      apply maponpathsidfun.
    - refine (_ @ !(pathscomp0rid _)).
      unfold map_gquot_to_image_on_path.
      apply (@maponpaths_pr1_PathOverToTotalPath' _ _ (_ ,, _) (_ ,, _)).
    - induction x as [x | x], y as [y | y].
      + etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            exact (!(maponpathsinv0 inl (poly_comp P₁ (image_inj_comp f) pr1 x))).
          }
          etrans.
          {
            apply maponpaths.
            refine (maponpathscomp
                      inl
                      (coprodf (poly_pr1 P₁) (poly_pr1 P₂))
                      _
                    @ _).
            exact (!(maponpathscomp (poly_pr1 P₁) inl _)).
          }
          exact (!(maponpathscomp0 inl _ _)).
        }
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 inl _)).
          }
          exact (!(maponpathscomp0 inl _ _)).
        }
        apply maponpaths.
        exact (!(IHP₁ _ _ _)).
      + induction p.
      + induction p.
      + etrans.
        {
          etrans.
          {
            apply maponpaths_2.
            exact (!(maponpathsinv0 inr (poly_comp P₂ (image_inj_comp f) pr1 x))).
          }
          etrans.
          {
            apply maponpaths.
            refine (maponpathscomp
                      inr
                      (coprodf (poly_pr1 P₁) (poly_pr1 P₂))
                      _
                    @ _).
            exact (!(maponpathscomp (poly_pr1 P₂) inr _)).
          }
          exact (!(maponpathscomp0 inr _ _)).
        }
        refine (!_).
        etrans.
        {
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathsinv0 inr _)).
          }
          exact (!(maponpathscomp0 inr _ _)).
        }
        apply maponpaths.
        exact (!(IHP₂ _ _ _)).
    - etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          apply pathsdirprod_inv.
        }
        etrans.
        {
          apply maponpaths.
          exact (!(maponpaths_pathsdirprod _ _ _ _)).
        }
        apply pathsdirprod_concat.
      }
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply pathsdirprod_inv.
        }
        apply pathsdirprod_concat.
      }
      refine (!_).
      exact (paths_pathsdirprod (IHP₁ _ _ _) (IHP₂ _ _ _)).
  Qed.
  
  Definition map_gquot_to_image_on_commute
             {x y : poly_act (point_constr Σ) (alg_carrier X)}
             (p : poly_act_rel
                    (point_constr Σ)
                    (λ z₁ z₂, alg_map_carrier f z₁ = alg_map_carrier f z₂)
                    x y)
    : map_gquot_to_image_on_path (cong_rel_ops congruence_relation_ops_for_image x y p)
      @ alg_map_commute (image_inj f) y
      =
      alg_map_commute (image_inj f) x
      @ maponpaths
          (alg_constr (image f))
          (poly_rel_to_eq_fun (@map_gquot_to_image_on_path) p).
  Proof.
    refine (PathOverToTotalPath'_comp _ _ @ _ @ !(PathOverToTotalPath'_eta _)).
    use globe_over_to_homot
    ; [
      | apply path_globe_over_hset ;
        intro ;
        apply isasetaprop ;
        apply ishinh ].
    refine (!_).
    etrans.
    {
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths_2.
      cbn -[PathOverToTotalPath'].
      unfold image_inj_preserves_point.
      apply (@maponpaths_pr1_PathOverToTotalPath' _ _ (_ ,, _) (_ ,, _)).
    }
    etrans.
    {
      apply maponpaths.
      apply (maponpathscomp (alg_constr (image f)) pr1).
    }
    unfold funcomp, image_inj_preserves_point_pr1.
    cbn.
    refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
    apply maponpaths.
    refine (_ @ path_assoc _ _ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0l.
    }
    simpl.
    refine (!(maponpathscomp0 _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathscomp _ _ _)).
    }
    refine (!(maponpathscomp0 _ _ _) @ _).
    apply maponpaths.
    exact (map_gquot_to_image_on_commute_lem p).
  Qed.

  Definition maponpaths_pr1_sem_endpoint_UU_natural
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (alg_carrier X))
    : maponpaths
         (poly_pr1 Q)
         (sem_endpoint_UU_natural e (alg_map_commute (image_inj f)) x)
      =
      poly_comp _ _ _ _
      @ sem_endpoint_UU_natural e (alg_map_commute f) x
      @ maponpaths
          (sem_endpoint_UU e (alg_constr Y))
          (!(poly_comp P (image_inj_comp f) pr1 x))
      @ total_algebra.pr1_endpoint
          (image_disp_alg f)
          e
          (poly_map P (image_inj_comp f) x).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q R e₁ IHe₁ e₂ IHe₂
                    | P T t | C₁ C₂ g | ].
    - refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        apply maponpathsidfun.
      }
      apply pathsinv0r.
    - refine (maponpathscomp0
                (poly_pr1 R)
                (sem_endpoint_UU_natural
                   e₂
                   (alg_map_commute (image_inj f))
                   (sem_endpoint_UU e₁ prealg_constr x))
                (maponpaths
                   (sem_endpoint_UU e₂ (total_algebra.operation (image_disp_alg f)))
                   (sem_endpoint_UU_natural e₁ (alg_map_commute (image_inj f)) x))
                @ _).
      etrans.
      {
        apply maponpaths_2.
        apply IHe₂.
      }
      clear IHe₂.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      refine (!_).
      refine (!(path_assoc
                  (sem_endpoint_UU_natural
                     e₂
                     (alg_map_commute f)
                     (sem_endpoint_UU e₁ prealg_constr x))
                  (maponpaths
                     (sem_endpoint_UU e₂ prealg_constr)
                     (sem_endpoint_UU_natural e₁ (alg_map_commute f) x))
                  _)
              @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      refine (path_assoc
                _
                (maponpaths
                   (sem_endpoint_UU e₂ (alg_constr Y))
                   (total_algebra.pr1_endpoint
                      (image_disp_alg f)
                      e₁
                      (poly_map P (image_inj_comp f) x)))
                (total_algebra.pr1_endpoint
                   (image_disp_alg f) e₂
                   (sem_endpoint_UU
                      e₁
                      (total_algebra.operation (image_disp_alg f))
                      (poly_map P (image_inj_comp f) x)))
                @ _).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            exact (!(maponpathscomp _ _ _)).
          }
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (_ @ path_assoc _ _ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpathsinv0.
      }
      refine (!_).
      use path_inv_rotate_rl.
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!(maponpathscomp0 _ _ _) @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (!(path_assoc _ _ _)).
        }
        exact (!(IHe₁ x)).
      }
      clear IHe₁.
      etrans.
      {
        apply maponpaths_2.
        apply (maponpathscomp
                 (poly_pr1 Q)
                 (sem_endpoint_UU e₂ (alg_constr Y))).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpathscomp.
      }
      unfold funcomp.
      refine (!_).
      apply (homotsec_natural'
               (total_algebra.pr1_endpoint (image_disp_alg f) e₂)).
    - refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply pathscomp0rid.
        }
        exact (!(maponpathscomp0 inl _ _)).
      }
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply idpath.
    - refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths.
          apply pathscomp0rid.
        }
        exact (!(maponpathscomp0 inr _ _)).
      }
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply idpath.
    - refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        refine (maponpathsinv0
                  pr1
                  (pathsdirprod
                     (poly_comp P (image_inj_comp f) pr1 (pr1 x))
                     (poly_comp Q (image_inj_comp f) pr1 (pr2 x))) @ _).
        apply maponpaths.
        apply maponpaths_pr1_pathsdirprod.
      }
      apply pathsinv0r.
    - refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (pathscomp0rid _ @ _).
        refine (maponpathsinv0
                  dirprod_pr2
                  (pathsdirprod
                     (poly_comp P (image_inj_comp f) pr1 (pr1 x))
                     (poly_comp Q (image_inj_comp f) pr1 (pr2 x))) @ _).
        apply maponpaths.
        apply maponpaths_pr2_pathsdirprod.
      }
      apply pathsinv0r.
    - refine (!(maponpaths_pathsdirprod
                  (poly_pr1 Q) (poly_pr1 R)
                  (sem_endpoint_UU_natural e₁ (alg_map_commute (image_inj f)) x)
                  (sem_endpoint_UU_natural e₂ (alg_map_commute (image_inj f)) x))
              @ _).
      refine (!_).
      etrans.
      {
        etrans.
        {
          refine (maponpaths (λ z, _ @ z) _).
          etrans.
          {
            refine (maponpaths (λ z, _ @ z) _).
            etrans.
            {
              refine (maponpaths (λ z, z @ _) _).
              apply (maponpaths_prod_path
                       (sem_endpoint_UU e₁ (alg_constr Y))
                       (sem_endpoint_UU e₂ (alg_constr Y))).
            }
            exact (pathsdirprod_concat
                     (maponpaths
                        (sem_endpoint_UU e₁ (alg_constr Y))
                        (!(poly_comp P (image_inj_comp f) pr1 x)))
                     (total_algebra.pr1_endpoint
                        (image_disp_alg f)
                        e₁
                        (poly_map P (image_inj_comp f) x))
                     (maponpaths
                        (sem_endpoint_UU e₂ (alg_constr Y))
                        (!(poly_comp P (image_inj_comp f) pr1 x)))
                     (total_algebra.pr1_endpoint
                        (image_disp_alg f)
                        e₂
                        (poly_map P (image_inj_comp f) x))).
          }
          apply (pathsdirprod_concat
                   (sem_endpoint_UU_natural e₁ (alg_map_commute f) x)
                   _
                   (sem_endpoint_UU_natural e₂ (alg_map_commute f) x)).
        }
        apply (pathsdirprod_concat
                 (poly_comp
                    Q
                    (alg_map_carrier (image_inj f)) pr1
                    (sem_endpoint_UU e₁ prealg_constr x))
                 _
                 (poly_comp
                    R
                    (alg_map_carrier (image_inj f)) pr1
                    (sem_endpoint_UU e₂ prealg_constr x))).
      }
      refine (!_).
      exact (paths_pathsdirprod (IHe₁ _) (IHe₂ _)).
    - refine (!_).
      refine (pathscomp0rid _ @ _).
      apply maponpaths_for_constant_function.
    - apply idpath.
    - refine (!_).
      etrans.
      {
        refine (maponpaths (λ z, _ @ z) _).
        apply maponpaths.
        apply pathscomp0rid.
      }
      refine (!_).
      exact (maponpaths_pr1_PathOverToTotalPath' (image_inj_preserves_point_pr1 f x) _).
  Qed.

  Definition map_gquot_to_image_path
             {j : path_label Σ}
             (x : poly_act (path_source Σ j) (alg_carrier X))
    : sem_endpoint_UU_natural (path_left Σ j) (alg_map_commute (image_inj f)) x
      @ alg_path
          (image f)
          j
          (poly_map (path_source Σ j) (alg_map_carrier (image_inj f)) x)
      =
      map_gquot_to_image_on_path
        (make_groupoid_path_algebra_nat_trans_data congruence_relation_nat_for_image j x)
      @ sem_endpoint_UU_natural (path_right Σ j) (alg_map_commute (image_inj f)) x.
  Proof.
    refine (PathOverToTotalPath'_eta _ @ _ @ !(PathOverToTotalPath'_eta _)).
    use globe_over_to_homot
    ; [
      | apply path_globe_over_hset ;
        intro ;
        apply isasetaprop ;
        apply ishinh ]
    ; unfold globe.
    refine (maponpathscomp0 _ _ _ @ _ @ !(maponpathscomp0 _ _ _)).
    etrans.
    {
      apply maponpaths.
      apply (maponpaths_pr1_PathOverToTotalPath'
               (!(total_algebra.pr1_endpoint
                    (image_disp_alg f)
                    (path_left Σ j)
                    (poly_map (path_source Σ j) (image_inj_comp f) x))
                @ alg_path
                    Y j
                    (poly_pr1
                       (path_source Σ j)
                       (poly_map (path_source Σ j) (image_inj_comp f) x))
                @ total_algebra.pr1_endpoint
                    (image_disp_alg f)
                    (path_right Σ j)
                    (poly_map (path_source Σ j) (image_inj_comp f) x))).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      unfold map_gquot_to_image_on_path.
      apply maponpaths_pr1_PathOverToTotalPath'.
    }
    etrans.
    {
      apply maponpaths.
      refine (maponpaths_pr1_sem_endpoint_UU_natural (path_right Σ j) x @ _).
      apply pathscomp0lid.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (maponpaths_pr1_sem_endpoint_UU_natural (path_left Σ j) x @ _).
      apply pathscomp0lid.
    }
    etrans.
    {
      do 2 (refine (!(path_assoc _ _ _) @ _) ; apply maponpaths).
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0r.
      }
      apply pathscomp0lid.
    }
    do 2 refine (path_assoc _ _ _ @ _ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths_2.
      apply eq_to_cong_rel_image.
    }
    etrans.
    {
      apply maponpaths_2.
      apply (alg_map_path f j x).
    }
    refine (!(path_assoc _ _ _) @ _ @ path_assoc _ _ _).
    apply maponpaths.
    refine (!_).
    apply homotsec_natural'.
  Qed.
  
  Definition map_gquot_to_image
    : X/R --> image f.
  Proof.
    use factor_through_gquot.
    - exact (image_inj f).
    - exact @map_gquot_to_image_on_path.
    - exact map_gquot_to_image_on_identity.
    - exact @map_gquot_to_image_on_concat.
    - exact @map_gquot_to_image_on_commute.
    - exact @map_gquot_to_image_path.
  Defined.

  (**
     Step 3: Show this map is a left adjoint equivalence
   *)
  Section FiberMapGQuot.
    Variable (x : alg_carrier X).

    Definition inverse_image_map_gquot
      : hfiber
          (alg_map_carrier map_gquot_to_image)
          (alg_map_carrier f x,, hinhpr (x,, idpath (alg_map_carrier f x)))
      := gcl (make_groupoid_algebra_carrier congruence_relation_for_image) x
         ,,
         idpath _.

    Definition inverse_image_map_gquot_all_path_base
      : ∏ (z : alg_carrier X/R),
        alg_map_carrier
          map_gquot_to_image
          z
        =
        alg_map_carrier f x
        ,,
        hinhpr (x,, idpath (alg_map_carrier f x))
        →
        z
        =
        gcl (make_groupoid_algebra_carrier congruence_relation_for_image) x.
    Proof.
      use gquot_ind_set ; simpl.
      - exact (λ a p,
               gcleq
                 (make_groupoid_algebra_carrier congruence_relation_groupoid_for_image)
                 (maponpaths pr1 p)).
      - abstract
          (simpl ;
           intros a₁ a₂ g ;
           apply PathOver_arrow ;
           intro p ;
           apply map_PathOver ;
           unfold square ;
           rewrite maponpathsidfun ;
           rewrite maponpaths_for_constant_function ;
           rewrite pathscomp0rid ;
           refine (!(gconcat _ _ _) @ _) ;
           apply maponpaths ;
           unfold transportb ;
           rewrite transportf_paths_FlFr ;
           rewrite maponpaths_for_constant_function ;
           rewrite pathscomp0rid ;
           rewrite maponpathsinv0 ;
           rewrite pathsinv0inv0 ;
           rewrite maponpathscomp0 ;
           refine (!_) ;
           apply maponpaths_2 ;
           refine (maponpaths
                     (maponpaths pr1)
                     (factor_through_gquot_gcleq
                        congruence_relation_for_image
                        (image f)
                        _ _ _ _ _ _
                        g)
                   @ _) ;
           apply maponpaths_pr1_PathOverToTotalPath).
      - intro.
        use funspace_isaset.
        exact (gtrunc _ _ _).
    Defined.

    Definition inverse_image_map_gquot_all_path_fib
      : ∏ (z : alg_carrier X/R)
          (p : alg_map_carrier map_gquot_to_image z
               =
               alg_map_carrier f x,, hinhpr (x,, idpath (alg_map_carrier f x))),
        maponpaths
          (alg_map_carrier map_gquot_to_image)
          (inverse_image_map_gquot_all_path_base z p)
        =
        p.
    Proof.
      use gquot_ind_prop.
      - intros a p.
        simpl.
        etrans.
        {
          exact (factor_through_gquot_gcleq
                   congruence_relation_for_image
                   (image f)
                   _ _ _ _ _ _
                   _).
        }
        refine (_ @ !(PathOverToTotalPath'_eta _)).
        unfold PathOverToTotalPath'.
        use globe_over_to_homot.
        * apply idpath.
        * use path_globe_over_hset.
          intro.
          apply isasetaprop.
          simpl.
          exact (pr2 (ishinh _)).
      - intro ; simpl.
        use impred_isaprop ; intro ; simpl.
        exact (one_type_isofhlevel _ _ _ _ _).
    Qed.
        
    Definition inverse_image_map_gquot_all_path
               (t : hfiber
                      (alg_map_carrier map_gquot_to_image)
                      (alg_map_carrier f x,, hinhpr (x,, idpath (alg_map_carrier f x))))
      : t = inverse_image_map_gquot.
    Proof.
      induction t as [z p].
      use PathOverToTotalPath.
      - exact (inverse_image_map_gquot_all_path_base z p).
      - abstract
          (use map_PathOver ;
           unfold square ;
           refine (pathscomp0rid _ @ _) ;
           refine (!_) ;
           refine (maponpaths (λ z, _ @ z) (maponpaths_for_constant_function _ _) @ _) ;
           refine (pathscomp0rid _ @ _) ;
           refine (!_) ;
           exact (inverse_image_map_gquot_all_path_fib z p)).
    Qed.
  End FiberMapGQuot.
  
  Definition map_gquot_to_image_is_adjequiv
    : left_adjoint_equivalence map_gquot_to_image.
  Proof.
    use isweq_to_hit_algebra_adjequiv.
    intro y.
    induction y as [y p].
    simpl in p.
    revert p.
    use (squash_rec
           (λ p, make_hProp
                   (iscontr (hfiber (alg_map_carrier map_gquot_to_image) (y,, p)))
                   _)).
    - apply isapropiscontr.
    - intro x ; simpl.
      induction x as [x p].
      induction p ; simpl.
      use make_iscontr.
      + exact (inverse_image_map_gquot x).
      + exact (inverse_image_map_gquot_all_path x).
  Defined.
End FirstIsomorphismTheorem.
