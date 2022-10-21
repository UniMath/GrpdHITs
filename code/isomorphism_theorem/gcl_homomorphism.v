(** Congruence relation of algebras *)
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
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import hit_biadjunction.hit_algebra_biadj.lift_gquot.
Require Import hit_biadjunction.hit_path_algebra_biadj.lift_gquot.
Require Import hit_biadjunction.hit_path_algebra_biadj.counit.
Require Import hit_biadjunction.hit_path_algebra_biadj.unit.
Require Import hit_biadjunction.hit_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.

Local Open Scope cat.

Definition poly_gquot_poly_map
           {P : poly_code}
           {G : groupoid}
           (x : poly_act P G)
  : gcl (poly_act_groupoid P G) (x)
    =
    poly_gquot
      P
      _
      (poly_map
         P
         (gcl G)
         x).
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths gquot_inl_grpd (IHP₁ x)).
    + exact (maponpaths gquot_inr_grpd (IHP₂ x)).
  - exact (maponpaths
             (λ z, prod_gquot_comp z _)
             (IHP₁ _)
           @ maponpaths
               (prod_gquot_comp _)
               (IHP₂ _)).
Defined.

Definition poly_gquot_poly_map_lem
           {P : poly_code}
           {G : groupoid}
           (x : poly_act P G)
  : poly_map_gcl_is_gquot_poly x
    @ maponpaths gquot_poly (poly_gquot_poly_map x)
    @ gquot_poly_poly_gquot _
    =
    idpath _.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + simpl.
      refine (_ @ maponpaths_idpath).
      refine (_ @ maponpaths (maponpaths inl) (IHP₁ x)).
      refine (!_).
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp
                 gquot_inl_grpd
                 (gquot_sum gquot_poly gquot_poly)
                 (poly_gquot_poly_map _)).
      }
      unfold funcomp.
      etrans.
      {
        exact (homotsec_natural'
                 (inl_gquot_poly P₁ P₂)
                 (poly_gquot_poly_map _)).
      }
      simpl.
      refine (!_).
      apply maponpathscomp.
    + simpl.
      refine (_ @ maponpaths_idpath).
      refine (_ @ maponpaths (maponpaths inr) (IHP₂ x)).
      refine (!_).
      refine (maponpathscomp0 _ _ _ @ _).
      apply maponpaths.
      refine (maponpathscomp0 _ _ _ @ _).
      refine (_ @ !(path_assoc _ _ _)).
      apply maponpaths_2.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp
                 gquot_inr_grpd
                 (gquot_sum gquot_poly gquot_poly)
                 (poly_gquot_poly_map _)).
      }
      unfold funcomp.
      etrans.
      {
        exact (homotsec_natural'
                 (inr_gquot_poly P₁ P₂)
                 (poly_gquot_poly_map _)).
      }
      simpl.
      refine (!_).
      apply maponpathscomp.
  - refine (_ @ paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
    refine (_ @ pathsdirprod_concat _ _ _ _).
    apply maponpaths.
    refine (_ @ pathsdirprod_concat _ _ _ _).
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp0
                 (gquot_prod gquot_poly gquot_poly)
                 (maponpaths
                    (λ z, prod_gquot_comp z (gcl (poly_act_groupoid P₂ G) (pr2 x)))
                    (poly_gquot_poly_map (pr1 x)))
                 (maponpaths
                    (prod_gquot_comp (poly_gquot P₁ G (poly_map P₁ (gcl G) (pr1 x))))
                    (poly_gquot_poly_map (pr2 x)))).
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      apply maponpaths_2.
      exact (maponpathscomp
               (prod_gquot_comp (poly_gquot P₁ G (poly_map P₁ (gcl G) (pr1 x))))
               (gquot_prod gquot_poly gquot_poly)
               (poly_gquot_poly_map _)).
    }
    unfold funcomp.
    etrans.
    {
      apply maponpaths.
      exact (homotsec_natural'
               (λ z, gquot_poly_pair
                       P₁ P₂
                       (poly_gquot P₁ G (poly_map P₁ (gcl G) (pr1 x)))
                       z)
               (poly_gquot_poly_map _)).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp
                 (λ z, prod_gquot_comp z (gcl (poly_act_groupoid P₂ G) (pr2 x)))
                 (gquot_prod gquot_poly gquot_poly)
                 (poly_gquot_poly_map _)).
      }
      unfold funcomp.
      exact (homotsec_natural'
               (λ z, gquot_poly_pair
                       P₁ P₂
                       z
                       (gcl (poly_act_groupoid P₂ G) (pr2 x)))
               (poly_gquot_poly_map _)).
    }
    simpl.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathscomp.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (maponpathscomp
               gquot_poly
               (λ z, z ,, gquot_poly (gcl (poly_act_groupoid P₂ G) (pr2 x)))
               (poly_gquot_poly_map (pr1 x))).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_make_dirprod_right.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpaths_make_dirprod_left.
    }
    refine (pathsdirprod_concat _ _ _ _ @ _).
    simpl.
    apply maponpaths_2.
    apply pathscomp0rid.
Qed.
    
Section MapToCongruence.
  Context {Σ : hit_signature}
          (X : hit_algebra_one_types Σ)
          (R : congruence_relation X).

  Definition congruence_gcl_map
    : alg_carrier X → alg_carrier (quotient_of_congruence R)
    := gcl (make_groupoid_algebra_carrier R).

  Definition congruence_gcl_preserves_point
    : preserves_point congruence_gcl_map
    := λ x,
       maponpaths
         (gquot_functor_map
            (make_groupoid_algebra_operations R))
         (@poly_gquot_poly_map
            _
            (alg_carrier_grpd (make_groupoid_algebra R))
            x).

  Definition congruence_gcl_prealg
    : pr11 X --> pr11 (quotient_of_congruence R).
  Proof.
    use one_types_homotopies.make_hit_prealgebra_mor.
    - exact congruence_gcl_map.
    - exact congruence_gcl_preserves_point.
  Defined.

  Definition gcl_sem_endpoint_UU_natural_lem
             {P Q : poly_code}
             (e : endpoint (point_constr Σ) P Q)
             (x : poly_act P (alg_carrier X))
    : sem_endpoint_UU_natural e congruence_gcl_preserves_point x
      =
      @poly_map_gcl_is_gquot_poly
        Q
        (make_groupoid_algebra_carrier R)
        (sem_endpoint_UU e prealg_constr x)
      @ !(gquot_endpoint_help
            e
            (gcl (poly_act_groupoid P (pr1 (make_groupoid_prealgebra R))) x))
      @ maponpaths
          _
          (maponpaths
             gquot_poly
             (poly_gquot_poly_map _)
           @ gquot_poly_poly_gquot
             (poly_map P (gcl (make_groupoid_algebra_carrier R)) x)).
  Proof.
    induction e as [P | P Q Q' e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q
                    | P Q Q' e₁ IHe₁ e₂ IHe₂
                    | P T t | Z₁ Z₂ g | ].
    - simpl.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply maponpathsidfun.
      }
      exact (@poly_gquot_poly_map_lem P (make_groupoid_algebra_carrier R) x).
    - simpl.
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
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp_inv.
      }
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpathsinv0 _ _)).
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply (maponpathscomp
                 (sem_endpoint_UU e₁ _)
                 (sem_endpoint_UU e₂ _)).
      }
      refine (!(maponpathscomp0 (sem_endpoint_UU e₂ _) _ _) @ _).
      refine (_ @ maponpathscomp0 (sem_endpoint_UU e₂ _) _ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        apply IHe₁.
      }
      clear IHe₁.
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (_ @ pathscomp0lid _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      pose (maponpaths
              (λ z, !(poly_map_gcl_is_gquot_poly _) @ z)
              (@poly_gquot_poly_map_lem
                 Q
                 (make_groupoid_algebra_carrier R)
                 (sem_endpoint_UU e₁ prealg_constr x))).
      simpl in p.
      rewrite !path_assoc, pathsinv0l, pathscomp0rid in p.
      simpl in p.
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        exact p.
      }
      apply pathsinv0l.
    - simpl.
      refine (!_).
      refine (!(maponpathscomp0 inl _ _) @ _ @ maponpaths_idpath).
      apply maponpaths.
      exact (@poly_gquot_poly_map_lem P (make_groupoid_algebra_carrier R) x).
    - simpl.
      refine (!_).
      refine (!(maponpathscomp0 inr _ _) @ _ @ maponpaths_idpath).
      apply maponpaths.
      exact (@poly_gquot_poly_map_lem Q (make_groupoid_algebra_carrier R) x).
    - refine (!(poly_gquot_poly_map_lem _) @ _).
      apply maponpaths.
      refine (_ @ !(pathscomp0lid _)).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc
                  (maponpaths
                     (gquot_prod gquot_poly gquot_poly)
                     (maponpaths
                        (λ z,
                         prod_gquot_comp
                           z
                           (gcl
                              (poly_act_groupoid Q (make_groupoid_algebra_carrier R))
                              (pr2 x)))
                        (poly_gquot_poly_map _)
                        @ maponpaths
                        (prod_gquot_comp
                           (poly_gquot
                              P
                              (make_groupoid_algebra_carrier R)
                              (poly_map
                                 P
                                 (gcl (make_groupoid_algebra_carrier R))
                                 (pr1 x))))
                        (poly_gquot_poly_map _)))
                  (gquot_poly_pair
                     P Q
                     (poly_gquot
                        P
                        (make_groupoid_algebra_carrier R)
                        (poly_map
                           P
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr1 x)))
                     (poly_gquot
                        Q
                        (make_groupoid_algebra_carrier R)
                        (poly_map
                           Q
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr2 x))))
                  (pathsdirprod
                     (gquot_poly_poly_gquot
                        (poly_map
                           P
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr1 x)))
                     (gquot_poly_poly_gquot
                        (poly_map
                           Q
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr2 x)))) @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathscomp0.
        }
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpathscomp.
          }
          unfold funcomp.
          exact (homotsec_natural'
                   (gquot_poly_pair
                      P Q
                      (poly_gquot
                         P
                         (make_groupoid_algebra_carrier R)
                         (poly_map P (gcl (make_groupoid_algebra_carrier R)) (pr1 x))))
                   (poly_gquot_poly_map _)).
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          exact (maponpathscomp
                   (λ z, prod_gquot_comp z _)
                   (gquot_prod gquot_poly gquot_poly)
                   (poly_gquot_poly_map _)).
        }
        unfold funcomp.
        exact (homotsec_natural'
                 (λ z,
                  gquot_poly_pair
                    P Q
                    z
                    (gcl (poly_act_groupoid Q (make_groupoid_algebra_carrier R)) (pr2 x)))
                 (poly_gquot_poly_map _)).
      }
      etrans.
      {
        apply maponpaths.
        do 2 refine (!(path_assoc _ _ _) @ _).
        refine (pathscomp0lid _ @ _).
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              refine (!_).
              apply (maponpathscomp
                       gquot_poly
                       (λ z, z ,, gquot_poly
                               (gcl (poly_act_groupoid Q (make_groupoid_algebra_carrier R))
                                    (pr2 x)))).
            }
            apply maponpaths_make_dirprod_right.
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              refine (!_).
              apply (maponpathscomp
                       gquot_poly
                       (λ z, gquot_poly
                               (poly_gquot
                                  P (make_groupoid_algebra_carrier R)
                                  (poly_map
                                     P
                                     (gcl (make_groupoid_algebra_carrier R))
                                     (pr1 x)))
                               ,, z)).
            }
            apply maponpaths_make_dirprod_left.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      refine (maponpaths_pr1_pathsdirprod _ _ @ _).
      refine (!(path_assoc _ _ _) @ _).
      apply idpath.
    - refine (!(poly_gquot_poly_map_lem _) @ _).
      apply maponpaths.
      refine (_ @ !(pathscomp0lid _)).
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc
                  (maponpaths
                     (gquot_prod gquot_poly gquot_poly)
                     (maponpaths
                        (λ z,
                         prod_gquot_comp
                           z
                           (gcl
                              (poly_act_groupoid Q (make_groupoid_algebra_carrier R))
                              (pr2 x)))
                        (poly_gquot_poly_map _)
                        @ maponpaths
                        (prod_gquot_comp
                           (poly_gquot
                              P
                              (make_groupoid_algebra_carrier R)
                              (poly_map
                                 P
                                 (gcl (make_groupoid_algebra_carrier R))
                                 (pr1 x))))
                        (poly_gquot_poly_map _)))
                  (gquot_poly_pair
                     P Q
                     (poly_gquot
                        P
                        (make_groupoid_algebra_carrier R)
                        (poly_map
                           P
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr1 x)))
                     (poly_gquot
                        Q
                        (make_groupoid_algebra_carrier R)
                        (poly_map
                           Q
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr2 x))))
                  (pathsdirprod
                     (gquot_poly_poly_gquot
                        (poly_map
                           P
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr1 x)))
                     (gquot_poly_poly_gquot
                        (poly_map
                           Q
                           (gcl (make_groupoid_algebra_carrier R))
                           (pr2 x)))) @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          apply maponpathscomp0.
        }
        refine (!(path_assoc _ _ _) @ _).
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            apply maponpathscomp.
          }
          unfold funcomp.
          exact (homotsec_natural'
                   (gquot_poly_pair
                      P Q
                      (poly_gquot
                         P
                         (make_groupoid_algebra_carrier R)
                         (poly_map P (gcl (make_groupoid_algebra_carrier R)) (pr1 x))))
                   (poly_gquot_poly_map _)).
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths_2.
          exact (maponpathscomp
                   (λ z, prod_gquot_comp z _)
                   (gquot_prod gquot_poly gquot_poly)
                   (poly_gquot_poly_map _)).
        }
        unfold funcomp.
        exact (homotsec_natural'
                 (λ z,
                  gquot_poly_pair
                    P Q
                    z
                    (gcl (poly_act_groupoid Q (make_groupoid_algebra_carrier R)) (pr2 x)))
                 (poly_gquot_poly_map _)).
      }
      etrans.
      {
        apply maponpaths.
        do 2 refine (!(path_assoc _ _ _) @ _).
        refine (pathscomp0lid _ @ _).
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths_2.
            etrans.
            {
              refine (!_).
              apply (maponpathscomp
                       gquot_poly
                       (λ z, z ,, gquot_poly
                               (gcl (poly_act_groupoid Q (make_groupoid_algebra_carrier R))
                                    (pr2 x)))).
            }
            apply maponpaths_make_dirprod_right.
          }
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              refine (!_).
              apply (maponpathscomp
                       gquot_poly
                       (λ z, gquot_poly
                               (poly_gquot
                                  P (make_groupoid_algebra_carrier R)
                                  (poly_map
                                     P
                                     (gcl (make_groupoid_algebra_carrier R))
                                     (pr1 x)))
                               ,, z)).
            }
            apply maponpaths_make_dirprod_left.
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_concat.
      }
      refine (maponpaths_pr2_pathsdirprod _ _ @ _).
      refine (!(path_assoc _ _ _) @ _).
      apply idpath.
    - simpl.
      refine (paths_pathsdirprod (IHe₁ _) (IHe₂ _) @ _).
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      apply maponpaths.
      refine (!(pathsdirprod_concat _ _ _ _) @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply pathsdirprod_inv.
      }
      apply maponpaths.
      refine (!_).
      apply maponpaths_prod_path.
    - simpl.
      refine (!_).
      apply maponpaths_for_constant_function.
    - apply idpath.
    - simpl ; unfold congruence_gcl_preserves_point.
      refine (!_).
      etrans.
      {
        etrans.
        {
          apply maponpaths_2.
          exact (!(maponpathsinv0
                     (gquot_functor_map (make_groupoid_algebra_operations R))
                     (poly_gquot_gquot_poly_comp (point_constr Σ) _))).
        }
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (maponpathscomp
                   (poly_gquot (point_constr Σ) (make_groupoid_algebra_carrier R))
                   (gquot_functor_map (make_groupoid_algebra_operations R))).
        }
        exact (!(maponpathscomp0
                   (gquot_functor_map (make_groupoid_algebra_operations R))
                   (!(poly_gquot_gquot_poly_comp (point_constr Σ) _))
                   _)).
      }
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply maponpathscomp0.
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          apply maponpathscomp.
        }
        etrans.
        {
          refine (!_).
          exact (maponpaths_homotsec
                   (invhomot (poly_gquot_gquot_poly))
                   (poly_gquot_poly_map _)).
        }
        unfold invhomot.
        apply maponpaths_2.
        apply maponpathsidfun.
      }
      refine (!(path_assoc _ _ _) @ _ @ pathscomp0rid _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply maponpaths_gquot_poly_poly_gquot.
      }
      apply pathsinv0l.
  Qed.        

  Definition gcl_sem_endpoint_UU_natural
             {P : poly_code}
             (e : endpoint (point_constr Σ) P I)
             (x : poly_act P (alg_carrier X))
    : sem_endpoint_UU_natural e congruence_gcl_preserves_point x
      =
      maponpaths
        gquot_poly
        (maponpaths
           (gquot_functor_map (sem_endpoint_grpd e (make_groupoid_prealgebra R)))
           (@poly_gquot_poly_map P (make_groupoid_algebra_carrier R) x))
      @ !(@gquot_endpoint
            _ _ _
            e
            (make_groupoid_prealgebra R)
            (poly_map P (gcl (make_groupoid_algebra_carrier R)) x)).
  Proof.
    unfold gquot_endpoint.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply pathscomp_inv.
    }
    refine (path_assoc _ _ _ @ _).
    use path_inv_rotate_lr.
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp
                 (gquot_functor_map
                    (sem_endpoint_grpd e (make_groupoid_prealgebra R)))
                 gquot_poly
                 (poly_gquot_poly_map _)).
      }
      unfold funcomp.
      exact (@homotsec_natural'
               _ _ _ _
               (invhomot (@gquot_endpoint_help _ _ _ e (make_groupoid_prealgebra R)))
               _ _
               (@poly_gquot_poly_map P (make_groupoid_algebra_carrier R) x)).
    }
    unfold invhomot.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathscomp.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpathsinv0.
    }
    use path_inv_rotate_lr.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathscomp0.
    }
    refine (!_).
    exact (gcl_sem_endpoint_UU_natural_lem e x).
  Qed.

  Definition maponpaths_gcl_eq_to_cong_rel
             {x₁ x₂ : alg_carrier X}
             (p : x₁ = x₂)
    : gcleq
        (make_groupoid_algebra_carrier R)
        (eq_to_cong_rel R p)
      =
      maponpaths
        (gcl (make_groupoid_algebra_carrier R))
        p.
  Proof.
    induction p ; simpl.
    apply ge.
  Qed.
  
  Definition congruence_gcl_preserves_path
    : preserves_path _ (prealg_map_commute congruence_gcl_prealg).
  Proof.
    intros i x.
    cbn.
    unfold lift_gquot_add2cell_obj, congruence_gcl_map.
    etrans.
    {
      apply maponpaths.
      pose (gcl_sem_endpoint_UU_natural (path_right Σ i) x) as p.
      refine (p @ _).
      apply pathscomp0lid.
    }
    refine (path_assoc _ _ _ @ _).
    do 2 refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        pose (gcl_sem_endpoint_UU_natural (path_left Σ i) x) as p.
        refine (p @ _).
        apply pathscomp0lid.
      }
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
      refine (!_).
      exact (maponpathscomp0
               gquot_poly
               (maponpaths
                  (gquot_functor_map
                     (sem_endpoint_grpd
                        (path_left Σ i)
                        (make_groupoid_prealgebra R)))
                  (poly_gquot_poly_map _))
               _).
    }
    etrans.
    {
      apply maponpaths.
      apply homotsec_natural'.
    }
    simpl.
    etrans.
    {
      exact (maponpathscomp0
               (gquot_id _)
               (gcleq
                  (poly_act_groupoid I (make_groupoid_algebra_carrier R))
                  (make_groupoid_path_algebra_nat_trans_data R i x))
               _).
    }
    apply maponpaths_2.
    etrans.
    {
      apply gquot_rec_beta_gcleq.
    }
    apply maponpaths_gcl_eq_to_cong_rel.
  Qed.
  
  Definition congruence_gcl
    : X --> quotient_of_congruence R.
  Proof.
    use make_algebra_map.
    use make_hit_path_alg_map.
    - exact congruence_gcl_prealg.
    - exact congruence_gcl_preserves_path.
  Defined.
End MapToCongruence.
