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
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.
Require Import isomorphism_theorem.congruence_mapping.
Require Import isomorphism_theorem.image.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

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

  Definition congruence_relation_for_image_is_congruence
    : is_congruence_relation congruence_relation_nat_for_image.
  Proof.
    apply TODO.
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
  Definition map_gquot_to_image
    : X/R --> image f.
  Proof.
    use factor_through_gquot.
    - exact (image_inj f).
    - simpl ; cbn.
      unfold image_inj_comp.
      intros a b p.
      use PathOverToTotalPath.
      + exact p.
      + apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
    - apply TODO.
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
