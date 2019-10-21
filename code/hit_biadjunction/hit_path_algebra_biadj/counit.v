(**
Counit of biadjunction when adding a 2-cell to the algebra structure
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
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
Require Import hit_path_algebra_biadj.lift_gquot.
Require Import hit_path_algebra_biadj.lift_path_groupoid.

Local Open Scope cat.

Definition gquot_poly_gcl
           (P : poly_code)
           {X : one_type}
           (z : poly_act P X)
  : gquot_poly (gcl (poly_act_groupoid P (one_type_to_groupoid X)) z)
    =
    poly_map P (gcl (one_type_to_groupoid X)) z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Definition poly_map_gcl_gquot_counit_map
           (P : poly_code)
           {X : one_type}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : poly_map
      P (gcl (one_type_to_groupoid X))
      (poly_map P (gquot_counit_map X) z)
    =
    z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - simpl.
    revert z.
    use gquot_ind_set.
    + exact (λ _, idpath _).
    + abstract
        (intros a₁ a₂ g ;
         simpl in * ;
         induction g ;
         rewrite ge ;
         apply identityPathOver).
    + exact (λ _, gtrunc _ _ _).
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Definition poly_map_gquot_counit_map_gcl
           (P : poly_code)
           {X : one_type}
           (z : poly_act P (one_type_to_groupoid X))
  : poly_map
      P (gquot_counit_map X)
      (poly_map P (gcl (one_type_to_groupoid X)) z)
    =
    z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + exact (maponpaths inl (IHP₁ z)).
    + exact (maponpaths inr (IHP₂ z)).
  - exact (pathsdirprod (IHP₁ (pr1 z)) (IHP₂ (pr2 z))).
Defined.

Definition poly_map_gquot_counit_map_gquot_poly
           {P : poly_code}
           {X : one_type}
           (z : poly_act P X)
  : poly_act_morphism
      P (one_type_to_groupoid X)
      (poly_map
         P (gquot_counit_map X)
         (gquot_poly
            (gcl (poly_act_groupoid P (one_type_to_groupoid X)) z)))
      z.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + exact (IHP₁ z).
    + exact (IHP₂ z).
  - exact (IHP₁ (pr1 z) ,, IHP₂ (pr2 z)).
Defined.

Definition maponpaths_poly_map_gcl_gquot_counit_map
           {P : poly_code}
           {X : one_type}
           (z : poly_act P (gquot (one_type_to_groupoid X)))
  : maponpaths
      (poly_map P (gquot_counit_map X))
      (poly_map_gcl_gquot_counit_map P z)
    =
    poly_map_gquot_counit_map_gcl P (poly_map P (gquot_counit_map X) z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - revert z.
    use gquot_ind_prop.
    + exact (λ _, idpath _).
    + exact (λ _, one_type_isofhlevel _ _ _ _ _).
  - induction z as [z | z].
    + simpl.
      etrans.
      {
        apply coprodf_path_maponpaths_inl.
      }
      apply maponpaths.
      apply IHP₁.
    + simpl.
      etrans.
      {
        apply coprodf_path_maponpaths_inr.
      }
      apply maponpaths.
      apply IHP₂.
  - simpl.
    etrans.
    {
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition maponpaths_poly_map_gquot_counit_map_gcl
           {P : poly_code}
           {X : one_type}
           (a : poly_act P X)
  : maponpaths
      (poly_map P (gcl (one_type_to_groupoid X)))
      (poly_map_gquot_counit_map_gcl P a)
    =
    poly_map_gcl_gquot_counit_map
      P
      (poly_map P (gcl (one_type_to_groupoid X)) a).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction a as [a | a].
    + simpl.
      etrans.
      {
        apply coprodf_path_maponpaths_inl.
      }
      apply maponpaths.
      apply IHP₁.
    + simpl.
      etrans.
      {
        apply coprodf_path_maponpaths_inr.
      }
      apply maponpaths.
      apply IHP₂.
  - simpl.
    etrans.
    {
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition poly_gquot_is_gcl_poly_gquot_gquot_poly_comp
           {P : poly_code}
           {X : one_types}
           (z : poly_act_groupoid P (one_type_to_groupoid X))
  : !(poly_gquot_is_gcl
        P
        (gquot_poly (gcl (poly_act_groupoid P (one_type_to_groupoid X))
                         z)))
    @ poly_gquot_gquot_poly_comp P z
    =
    gcleq (⦃ P ⦄ (one_type_to_groupoid X))
          (poly_map_gquot_counit_map_gquot_poly z).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (!(ge _ _)).
  - exact (!(ge _ _)).
  - induction z as [z | z].
    + simpl.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        exact (maponpathsinv0
                 gquot_inl_grpd
                 (poly_gquot_is_gcl
                    P₁
                    (gquot_poly
                       (gcl (poly_act_groupoid P₁ (one_type_to_groupoid X))
                            z)))).
      }
      etrans.
      {
        refine (!_).
        exact (maponpathscomp0
                 gquot_inl_grpd
                 (!(poly_gquot_is_gcl
                      P₁
                      (gquot_poly
                         (gcl (poly_act_groupoid P₁ (one_type_to_groupoid X))
                              z))))
                 (poly_gquot_gquot_poly_comp P₁ z)).
      }
      etrans.
      {
        apply maponpaths.
        exact (IHP₁ z).
      }
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    + simpl.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        exact (maponpathsinv0
                 gquot_inr_grpd
                 (poly_gquot_is_gcl
                    P₂
                    (gquot_poly
                       (gcl (poly_act_groupoid P₂ (one_type_to_groupoid X))
                            z)))).
      }
      etrans.
      {
        refine (!_).
        exact (maponpathscomp0
                 gquot_inr_grpd
                 (!(poly_gquot_is_gcl
                      P₂
                      (gquot_poly
                         (gcl (poly_act_groupoid P₂ (one_type_to_groupoid X))
                              z))))
                 (poly_gquot_gquot_poly_comp P₂ z)).
      }
      etrans.
      {
        apply maponpaths.
        exact (IHP₂ z).
      }
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  - simpl ; cbn.
    etrans.
    {
      apply maponpaths.
      pose (uncurry_ap
              prod_gquot_comp
              (poly_gquot_gquot_poly_comp P₁ (pr1 z))
              (poly_gquot_gquot_poly_comp P₂ (pr2 z)))
        as h.
      unfold uncurry in h.
      exact (!h).
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (maponpathsinv0
               (λ z0, prod_gquot_comp (pr1 z0) (dirprod_pr2 z0))
               (pathsdirprod
                  (poly_gquot_is_gcl
                     P₁
                     (gquot_poly
                        (gcl (poly_act_groupoid P₁ (one_type_to_groupoid X))
                             (pr1 z))))
                  (poly_gquot_is_gcl
                     P₂
                     (gquot_poly
                        (gcl (poly_act_groupoid P₂ (one_type_to_groupoid X))
                             (pr2 z)))))).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply pathsdirprod_inv.
    }
    etrans.
    {
      refine (!_).
      exact (maponpathscomp0
               (λ z0, prod_gquot_comp (pr1 z0) (dirprod_pr2 z0))
               (pathsdirprod
                  (!(poly_gquot_is_gcl
                       P₁
                       (gquot_poly
                          (gcl (poly_act_groupoid P₁ (one_type_to_groupoid X))
                               (pr1 z)))))
                  (!(poly_gquot_is_gcl
                       P₂
                       (gquot_poly
                          (gcl (poly_act_groupoid P₂ (one_type_to_groupoid X))
                               (pr2 z))))))
               (pathsdirprod
                  (poly_gquot_gquot_poly_comp P₁ (pr1 z))
                  (poly_gquot_gquot_poly_comp P₂ (pr2 z)))).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply pathsdirprod_concat.
      }
      exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
    }
    etrans.
    {
      simpl.
      pose (uncurry_ap
              prod_gquot_comp
              (gcleq
                 (poly_act_groupoid P₁ (one_type_to_groupoid X))
                 (poly_map_gquot_counit_map_gquot_poly (pr1 z)))
              (gcleq
                 (poly_act_groupoid P₂ (one_type_to_groupoid X))
                 (poly_map_gquot_counit_map_gquot_poly (pr2 z))))
        as h.
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
    refine (pathsdirprod _ _).
    + apply poly_act_id_right.
    + apply poly_act_id_left.
Qed.


Definition poly_map_gcl_sem_endpoint_one_types
           {A S T : poly_code}
           (e : endpoint A S T)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (z : poly_act S (gquot (one_type_to_groupoid (pr1 X))))
  : poly_map
      T
      (gcl (one_type_to_groupoid (pr1 X)))
      ((sem_endpoint_one_types e)
         X (poly_map S (gquot_counit_map (pr1 X)) z))
    =
    sem_endpoint_UU
      e
      (prealg_gquot_map
         A (one_type_to_groupoid (pr1 X))
         (prealg_path_groupoid_map A (pr1 X) (pr2 X))) z.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - exact (poly_map_gcl_gquot_counit_map P z).
  - simpl.
    refine (_ @ IHe₂ (sem_endpoint_UU
                        e₁
                        (prealg_gquot_map
                           A (one_type_to_groupoid (pr1 X))
                           (prealg_path_groupoid_map A (pr1 X) (pr2 X))) z)).
    refine (maponpaths (poly_map R (gcl (one_type_to_groupoid (pr1 X)))) _).
    refine (maponpaths (sem_endpoint_one_types e₂ X) _).
    refine (!_ @ maponpaths (poly_map Q (gquot_counit_map (pr1 X))) (IHe₁ _)).
    exact (poly_map_gquot_counit_map_gcl
             Q
             ((sem_endpoint_one_types e₁) X (poly_map P (gquot_counit_map (pr1 X)) z))).
  - exact (maponpaths inl (poly_map_gcl_gquot_counit_map P z)).
  - exact (maponpaths inr (poly_map_gcl_gquot_counit_map Q z)).
  - exact (poly_map_gcl_gquot_counit_map P (pr1 z)).
  - exact (poly_map_gcl_gquot_counit_map Q (pr2 z)).
  - exact (pathsdirprod (IHe₁ z) (IHe₂ z)).
  - apply idpath.
  - apply idpath.
  - simpl ; cbn.
    pose ((maponpaths (gquot_functor_map (prealg_path_groupoid_map A (pr1 X) (pr2 X)))
                      (poly_gquot_is_gcl A z)))
      as h.
    cbn in h.
    refine (gcleq _ _ @ !h).
    cbn.
    apply maponpaths.
    exact (!(poly_path_groupoid_poly_map A z)).
Defined.

Definition sem_endpoint_UU_prealg_path_groupoid_map
          {A S : poly_code}
          (l r : endpoint A S I)
          {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
          (pX : (sem_endpoint_one_types l X) ~ (sem_endpoint_one_types r X))
          (z : poly_act S (gquot (one_type_to_groupoid (pr1 X))))
  : sem_endpoint_UU
      l
      (prealg_gquot_map
         A (one_type_to_groupoid (pr1 X))
         (prealg_path_groupoid_map A (pr1 X) (pr2 X)))
      z
    =
    sem_endpoint_UU
      r
      (prealg_gquot_map
         A (one_type_to_groupoid (pr1 X))
         (prealg_path_groupoid_map A (pr1 X) (pr2 X))) z
  := !(poly_map_gcl_sem_endpoint_one_types l z)
     @ gcleq
         (one_type_to_groupoid (pr1 X))
         (pX (poly_map S (gquot_counit_map (pr1 X)) z))
     @ poly_map_gcl_sem_endpoint_one_types r z.

Definition sem_endpoint_UU_poly_map_gquot_poly
           {A S T : poly_code}
           (e : endpoint A S T)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (z : poly_act_groupoid S (one_type_to_groupoid (pr1 X)))
  : sem_endpoint_UU
      e (pr2 X)
      (poly_map
         S (gquot_counit_map (pr1 X))
         (gquot_poly
            (gcl (poly_act_groupoid S (one_type_to_groupoid (pr1 X)))
                 z)))
    =
    sem_endpoint_UU
      e (λ z, pr2 X (pr1 ((poly_path_groupoid A) (pr1 X)) z))
      z.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - exact (maponpaths (poly_map P (gquot_counit_map (pr1 X))) (gquot_poly_gcl P z)
           @ poly_map_gquot_counit_map_gcl P z).
  - simpl.
    refine (_ @ IHe₂ _).
    apply maponpaths.
    refine (IHe₁ _ @ !_).
    exact (maponpaths
            (poly_map Q (gquot_counit_map (pr1 X)))
            (gquot_poly_gcl
               Q
               (sem_endpoint_UU
                  e₁
                  (λ z0, pr2 X ((pr1 ((poly_path_groupoid A) (pr1 X))) z0)) z))
          @ poly_map_gquot_counit_map_gcl
              Q
              (sem_endpoint_UU
                 e₁
                 (λ z0, pr2 X ((pr1 ((poly_path_groupoid A) (pr1 X))) z0))
                 z)).
  - apply maponpaths.
    exact (maponpaths (poly_map P (gquot_counit_map (pr1 X))) (gquot_poly_gcl P z)
           @ poly_map_gquot_counit_map_gcl P z).
  - apply maponpaths.
    exact (maponpaths (poly_map _ (gquot_counit_map (pr1 X))) (gquot_poly_gcl _ _)
           @ poly_map_gquot_counit_map_gcl _ _).
  - exact (maponpaths (poly_map _ (gquot_counit_map (pr1 X))) (gquot_poly_gcl _ _)
           @ poly_map_gquot_counit_map_gcl _ _).
  - exact (maponpaths (poly_map _ (gquot_counit_map (pr1 X))) (gquot_poly_gcl _ _)
           @ poly_map_gquot_counit_map_gcl _ _).
  - exact (pathsdirprod (IHe₁ z) (IHe₂ z)).
  - apply idpath.
  - apply idpath.
  - exact (maponpaths
             (pr2 X)
             ((maponpaths
                 (poly_map A (gquot_counit_map (pr1 X)))
                 (gquot_poly_gcl A z)
               @ poly_map_gquot_counit_map_gcl A z)
               @ !(poly_path_groupoid_is_id z))).
Defined.

Definition sem_endpoint_UU_poly_map_gquot_poly_is_path
           {A S T : poly_code}
           (e : endpoint A S T)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (z : poly_act_groupoid S (one_type_to_groupoid (pr1 X)))
  : sem_endpoint_UU_poly_map_gquot_poly e z
    =
    maponpaths
      (sem_endpoint_UU e (pr2 X))
      (maponpaths
         (poly_map S (gquot_counit_map (pr1 X)))
         (gquot_poly_gcl S z)
       @ poly_map_gquot_counit_map_gcl S z)
      @ !path_groupoid_endpoint e z.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpathsidfun.
  - simpl ; cbn.
    etrans.
    {
      apply maponpaths.
      apply IHe₂.
    }
    refine (path_assoc _ _ _ @ _).
    refine (!_).
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
      refine (!_).
      apply maponpathsinv0.
    }
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (maponpathscomp
               _
               (sem_endpoint_UU e₂ (pr2 X))
               _).
    }
    etrans.
    {
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
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths_2.
      apply IHe₁.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      do 2 apply maponpaths.
      apply pathsinv0l.
    }
    apply maponpaths.
    apply pathscomp0rid.
  - simpl ; cbn.
    refine (!_).
    apply pathscomp0rid.
  - simpl ; cbn.
    refine (!_).
    apply pathscomp0rid.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply pathscomp0rid.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpaths_pathsdirprod _ _ _ _)).
      }
      apply pathsdirprod_concat.
    }
    apply maponpaths_pr1_pathsdirprod.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply pathscomp0rid.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (!(maponpaths_pathsdirprod _ _ _ _)).
      }
      apply pathsdirprod_concat.
    }
    apply maponpaths_pr2_pathsdirprod.
  - simpl ; cbn.
    refine (paths_pathsdirprod (IHe₁ z) (IHe₂ z) @ _).
    etrans.
    {
      refine (!_).
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply pathsdirprod_inv.
    }
    apply maponpaths_2.
    refine (!_).
    apply maponpaths_prod_path.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpaths_for_constant_function.
  - apply idpath.
  - simpl ; cbn.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathsinv0.
    }
    refine (!_).
    apply maponpathscomp0.
Qed.

Definition gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem
           {A P : poly_code}
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (a : poly_act_groupoid P (one_type_to_groupoid (pr1 X)))
  : maponpaths
      (poly_map P (gcl (one_type_to_groupoid (pr1 X))))
      (! (maponpaths
            (poly_map P (gquot_counit_map (pr1 X)))
            (gquot_poly_gcl P a)
          @ poly_map_gquot_counit_map_gcl P a))
    @ poly_map_gcl_gquot_counit_map
        P
        (gquot_poly
           (gcl (poly_act_groupoid P (one_type_to_groupoid (pr1 X))) a))
    @ idpath _
    =
    ! gquot_poly_gcl P a.
Proof.
  etrans.
  {
    apply maponpaths.
    apply pathscomp0rid.
  }
  etrans.
  {
    apply maponpaths_2.
    apply maponpaths.
    etrans.
    {
      apply pathscomp_inv.
    }
    apply maponpaths.
    refine (!_).
    apply maponpathsinv0.
  }
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
    exact (homotsec_natural'
             (poly_map_gcl_gquot_counit_map P)
             (! gquot_poly_gcl P a)).
  }
  etrans.
  {
    do 2 apply maponpaths.
    apply maponpathsidfun.
  }
  refine (path_assoc _ _ _ @ _).
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpathsinv0.
      }
      apply maponpaths.
      apply maponpaths_poly_map_gquot_counit_map_gcl.
    }
    apply pathsinv0l.
  }
  apply idpath.
Qed.

Definition maponpaths_gcl
           {X : one_type}
           {x y : X}
           (p : x = y)
  : maponpaths
      (gcl (one_type_to_groupoid X))
      p
    =
    gcleq (one_type_to_groupoid X) p.
Proof.
  induction p.
  exact (!(ge _ _)).
Qed.

Definition gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem₂
           {P : poly_code}
           {X : one_type}
           (z : poly_act_groupoid P (one_type_to_groupoid X))
  : poly_path_groupoid_is_id z
  @ ! (maponpaths
         (poly_map P (gquot_counit_map X))
         (gquot_poly_gcl P z)
       @ poly_map_gquot_counit_map_gcl P z)
  @ !(poly_path_groupoid_poly_map
        P
        (gquot_poly
           (gcl (poly_act_groupoid P (one_type_to_groupoid X))
                z)))
  @ # (poly_path_groupoid P X : _ ⟶ _)
         (poly_map_gquot_counit_map_gquot_poly z)
  =
  idpath _.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction z as [z | z].
    + simpl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply coprodf_path_maponpaths_inl.
            }
            exact (!(maponpathscomp0 _ _ _)).
          }
          exact (!(maponpathsinv0 _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (!(maponpathsinv0 _ _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      etrans.
      {
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (_ @ maponpaths_idpath).
      apply maponpaths.
      apply IHP₁.
    + simpl.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths_2.
          etrans.
          {
            apply maponpaths.
            etrans.
            {
              apply maponpaths_2.
              apply coprodf_path_maponpaths_inr.
            }
            exact (!(maponpathscomp0 _ _ _)).
          }
          exact (!(maponpathsinv0 _ _)).
        }
        etrans.
        {
          apply maponpaths.
          apply maponpaths_2.
          exact (!(maponpathsinv0 _ _)).
        }
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathscomp0 _ _ _)).
        }
        exact (!(maponpathscomp0 _ _ _)).
      }
      etrans.
      {
        exact (!(maponpathscomp0 _ _ _)).
      }
      refine (_ @ maponpaths_idpath).
      apply maponpaths.
      apply IHP₂.
  - simpl.
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths_2.
            exact (!(maponpaths_pathsdirprod _ _ _ _)).
          }
          apply pathsdirprod_concat.
        }
        apply pathsdirprod_inv.
      }
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply pathsdirprod_inv.
      }
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply pathsdirprod_concat.
    }
    exact (paths_pathsdirprod (IHP₁ _) (IHP₂ _)).
Qed.

Definition gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly
           {A S T : poly_code}
           (e : endpoint A S T)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (a : poly_act_groupoid S (one_type_to_groupoid (pr1 X)))
  : @gquot_endpoint_help
      A S T e
      (one_type_to_groupoid (pr1 X)
       ,, prealg_path_groupoid_map A (pr1 X) (pr2 X))
      (gcl (poly_act_groupoid S (one_type_to_groupoid (pr1 X))) a)
    =
    !(poly_map_gcl_sem_endpoint_one_types
        e
        (gquot_poly
           (gcl (poly_act_groupoid S (one_type_to_groupoid (pr1 X))) a)))
     @ maponpaths
         (poly_map T (gcl (one_type_to_groupoid (pr1 X))))
         (sem_endpoint_UU_poly_map_gquot_poly e a)
     @ !(gquot_poly_gcl T _).
Proof.
  use path_inv_rotate_rl.
  use path_rotate_rl.
  etrans.
  {
    apply maponpaths_2.
    refine (!_).
    apply maponpathsinv0.
  }
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - exact (gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem a).
  - simpl ; cbn.
    refine (_ @ IHe₂ _) ; clear IHe₂ ; specialize (IHe₁ a).
    refine (_ @ !(path_assoc _ _ _)).
    do 2 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!_).
      apply (homotsec_natural'
               (poly_map_gcl_sem_endpoint_one_types e₂)).
    }
    do 2 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (maponpathscomp
               (λ z, (sem_endpoint_one_types e₂)
                       X
                       (poly_map Q (gquot_counit_map (pr1 X)) z))
               (poly_map R (gcl (one_type_to_groupoid (pr1 X))))).
    }
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      apply maponpathscomp0.
    }
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply (maponpathscomp
               (poly_map Q (gquot_counit_map (pr1 X)))
               (sem_endpoint_one_types e₂ X)).
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      etrans.
      {
        apply pathscomp_inv.
      }
      apply maponpaths.
      refine (!_).
      apply maponpathsinv0.
    }
    do 2 refine (!(path_assoc _ _ _) @ _).
    refine (_ @ pathscomp0rid _).
    apply maponpaths.
    etrans.
    {
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      apply maponpathscomp0.
    }
    refine (_ @ maponpaths_idpath).
    apply maponpaths.
    etrans.
    {
      apply maponpaths_2.
      apply pathscomp_inv.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply pathsinv0inv0.
    }
    do 2 refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathsidfun.
      }
      refine (!_).
      exact (homotsec_natural'
               (poly_map_gquot_counit_map_gcl Q)
               (!(sem_endpoint_UU_poly_map_gquot_poly e₁ a))).
    }
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply pathsinv0r.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply maponpathscomp.
      }
      etrans.
      {
        apply maponpaths.
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      apply maponpathscomp0.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply IHe₁.
    }
    etrans.
    {
      etrans.
      {
        refine (!_).
        apply maponpathscomp0.
      }
      apply maponpaths.
      apply pathsinv0r.
    }
    apply idpath.
  - etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      apply maponpathsinv0.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (coprodf_path_maponpaths_inl
               (poly_map P (gcl (one_type_to_groupoid (pr1 X))))
               (poly_map Q (gcl (one_type_to_groupoid (pr1 X))))
               (!(maponpaths
                     (poly_map P (gquot_counit_map (pr1 X))) (gquot_poly_gcl P a)
                  @ poly_map_gquot_counit_map_gcl P a))).
    }
    etrans.
    {
      refine (!_).
      apply (maponpathscomp0 inl).
    }
    refine (!_).
    etrans.
    {
      refine (!_).
      apply (maponpathsinv0 inl).
    }
    refine (!_).
    apply maponpaths.
    refine (_ @ gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem a).
    apply maponpaths.
    exact (!(pathscomp0rid _)).
  - etrans.
    {
      apply maponpaths.
      apply pathscomp0rid.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      apply maponpathsinv0.
    }
    etrans.
    {
      apply maponpaths_2.
      exact (coprodf_path_maponpaths_inr
               (poly_map P (gcl (one_type_to_groupoid (pr1 X))))
               (poly_map Q (gcl (one_type_to_groupoid (pr1 X))))
               (!(maponpaths
                     (poly_map Q (gquot_counit_map (pr1 X))) (gquot_poly_gcl Q a)
                  @ poly_map_gquot_counit_map_gcl Q a))).
    }
    etrans.
    {
      refine (!_).
      apply (maponpathscomp0 inr).
    }
    refine (!_).
    etrans.
    {
      refine (!_).
      apply (maponpathsinv0 inr).
    }
    refine (!_).
    apply maponpaths.
    refine (_ @ gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem a).
    apply maponpaths.
    exact (!(pathscomp0rid _)).
  - exact (gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem (pr1 a)).
  - exact (gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem (pr2 a)).
  - etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.        
        apply (pathsdirprod_inv
                 (sem_endpoint_UU_poly_map_gquot_poly e₁ a)
                 (sem_endpoint_UU_poly_map_gquot_poly e₂ a)).
      }
      refine (!_).
      apply (maponpaths_pathsdirprod
               (poly_map Q (gcl (one_type_to_groupoid (pr1 X))))
               (poly_map R (gcl (one_type_to_groupoid (pr1 X))))
               (!(sem_endpoint_UU_poly_map_gquot_poly e₁ a))
               (!(sem_endpoint_UU_poly_map_gquot_poly e₂ a))).
    }
    refine (!_).
    etrans.
    {
      apply (pathsdirprod_inv
               (gquot_poly_gcl Q _)
               (gquot_poly_gcl R _)).
    }
    refine (!_).
    etrans.
    {
      simpl.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_concat.
      }
      apply pathsdirprod_concat.
    }
    exact (paths_pathsdirprod (IHe₁ _) (IHe₂ _)).
  - apply idpath.
  - apply idpath.
  - simpl ; cbn.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply maponpathsinv0.
      }
      apply maponpaths.
      etrans.
      {
        apply pathscomp_inv.
      }
      apply maponpaths_2.
      apply pathsinv0inv0.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_gcl.
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply gconcat.
      }
      apply maponpaths.
      refine (!_).
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathsinv0
                 (gquot_functor_map (prealg_path_groupoid_map A (pr1 X) (pr2 X)))
                 (poly_gquot_is_gcl
                    A
                    (gquot_poly
                       (gcl (poly_act_groupoid
                               A
                               (one_type_to_groupoid (pr1 X))) a)))).
      }
      etrans.
      {
        refine (!_).
        exact (maponpathscomp0
                 (gquot_functor_map
                    (prealg_path_groupoid_map A (pr1 X) (pr2 X)))
                 (! poly_gquot_is_gcl A
                    (gquot_poly
                       (gcl (poly_act_groupoid
                               A
                               (one_type_to_groupoid (pr1 X))) a)))
                 (poly_gquot_gquot_poly_comp A a)).
      }
      apply maponpaths.
      exact (poly_gquot_is_gcl_poly_gquot_gquot_poly_comp a).
    }
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
    refine (_ @ ge _ _).
    apply maponpaths.
    refine (_ @ maponpaths_idpath).
    etrans.
    {
      refine (!_).
      simpl.
      apply maponpathscomp0.
    }
    apply maponpaths.
    do 2 refine (!(path_assoc _ _ _) @ _).
    exact (gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly_lem₂ a).
Qed.

Definition maponpaths_poly_map_gcl_sem_endpoint_one_types
           {A S T : poly_code}
           (e : endpoint A S T)
           {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
           (z : poly_act S (gquot (one_type_to_groupoid (pr1 X))))
  : maponpaths
      (poly_map T (gquot_counit_map (pr1 X)))
      (poly_map_gcl_sem_endpoint_one_types e z)
    @ sem_endpoint_UU_natural e (prealg_counit_comp A (pr2 X)) z
    =
    poly_map_gquot_counit_map_gcl T _.
Proof.
  cbn.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - simpl ; cbn.
    etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpaths_poly_map_gcl_gquot_counit_map.
  - simpl.
    etrans.
    {
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      apply IHe₂.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathsidfun _)).
      }
      refine (!_).
      exact (homotsec_natural'
               (poly_map_gquot_counit_map_gcl R)
               (maponpaths
                  (sem_endpoint_UU e₂ (pr2 X))
                  (sem_endpoint_UU_natural e₁ (prealg_counit_comp A (pr2 X)) z))).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpathscomp.
        }
        unfold funcomp.
        apply (maponpathscomp
                 _
                 (λ x,
                  poly_map
                    R (gquot_counit_map (pr1 X))
                    (poly_map R (gcl (one_type_to_groupoid (pr1 X))) x))).
      }
      etrans.
      {
        apply maponpaths.
        apply (maponpathscomp
                 _
                 (λ x,
                  poly_map
                    R (gquot_counit_map (pr1 X))
                    (poly_map R (gcl (one_type_to_groupoid (pr1 X))) x))).
      }
      etrans.
      {
        refine (!_).
        refine (maponpathscomp0
                  (λ x,
                   poly_map
                     R (gquot_counit_map (pr1 X))
                     (poly_map
                        R (gcl (one_type_to_groupoid (pr1 X)))
                        (sem_endpoint_UU e₂ (pr2 X) x)))
                  _
                  _).
      }
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      apply IHe₁.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0l.
    }
    apply idpath.
  - simpl ; cbn.
    etrans.
    {
      apply pathscomp0rid.
    }
    etrans.
    {
      apply coprodf_path_maponpaths_inl.
    }
    apply maponpaths.
    apply maponpaths_poly_map_gcl_gquot_counit_map.
  - simpl ; cbn.
    etrans.
    {
      apply pathscomp0rid.
    }
    etrans.
    {
      apply coprodf_path_maponpaths_inr.
    }
    apply maponpaths.
    apply maponpaths_poly_map_gcl_gquot_counit_map.
  - etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpaths_poly_map_gcl_gquot_counit_map.
  - etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpaths_poly_map_gcl_gquot_counit_map.
  - simpl ; cbn.
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply maponpaths_pathsdirprod.
    }
    refine (pathsdirprod_concat _ _ _ _ @ _).
    apply paths_pathsdirprod.
    + apply IHe₁.
    + apply IHe₂.
  - apply idpath.
  - apply idpath.
  - simpl ; cbn.
    unfold prealg_counit_comp.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      refine (!_).
      apply (maponpathscomp
               (gquot_functor_map (prealg_path_groupoid_map A (pr1 X) (pr2 X)))
               (gquot_counit_map (pr1 X))).
    }
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      exact (maponpathscomp0
               (gquot_counit_map (pr1 X))
               (gcleq _ _ @ ! _)
               (maponpaths
                  (gquot_functor_map (prealg_path_groupoid_map A (pr1 X) (pr2 X)))
                  (poly_gquot_is_gcl A z))).
    }
    etrans.
    {
      apply maponpaths_2.
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
      apply maponpaths_2.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      refine (!_).
      apply (maponpathscomp0 (pr2 X)).
    }
    etrans.
    {
      apply maponpaths.
      apply pathsinv0l.
    }
    apply idpath.
Qed.
    
Section LiftAdd2CellUnit.
  Context {A S : poly_code}
          (l r : endpoint A S I).

  Definition add2cell_lift_counit_equation_lem₁
             {X : total_bicat (disp_alg_bicat (⟦ A ⟧))}
             (pX : (sem_endpoint_one_types l X) ~ (sem_endpoint_one_types r X))
    : ∏ (z : gquot (poly_act_groupoid S (one_type_to_groupoid (pr1 X)))),
      ((@gquot_endpoint_help
          A S I l
          (one_type_to_groupoid (pr1 X)
           ,, prealg_path_groupoid_map A (pr1 X) (pr2 X))
          z)
      @ maponpaths
          (gquot_id (one_type_to_groupoid (pr1 X)))
          (gquot_functor_cell
             (path_alg_path_groupoid_ob l r pX)
             z))
      @ !(@gquot_endpoint_help
            A S I r
            (one_type_to_groupoid (pr1 X)
             ,, prealg_path_groupoid_map A (pr1 X) (pr2 X))
            z)
      =
      sem_endpoint_UU_prealg_path_groupoid_map l r pX (gquot_poly z).
  Proof.
    use gquot_ind_prop.
    - intro a.
      unfold sem_endpoint_UU_prealg_path_groupoid_map.
      cbn.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
      }
      unfold path_alg_path_groupoid_ob_comp.
      etrans.
      {
        do 2 apply maponpaths_2.        
        exact (gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly l a).
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        apply maponpaths.
        apply pathscomp0rid.
      }
      do 2 refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        do 3 apply maponpaths.
        exact (gquot_endpoint_help_sem_endpoint_UU_poly_map_gquot_poly r a).
      }
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          do 2 apply maponpaths.
          apply pathscomp0rid.
        }
        etrans.
        {
          apply pathscomp_inv.
        }
        apply maponpaths.
        apply pathsinv0inv0.
      }
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          apply maponpaths_gcl.
        }
        refine (!_).
        apply ginv.
      }
      simpl ; cbn.
      etrans.
      {
        do 2 apply maponpaths_2.
        apply maponpaths_gcl.
      }
      etrans.
      {
        apply maponpaths_2.
        cbn.
        exact (!(gconcat _ _ _)).
      }
      etrans.
      {
        exact (!(gconcat _ _ _)).
      }
      cbn.
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathscomp0rid.
      }
      pose (q := maponpaths
                   (poly_map S (gquot_counit_map (pr1 X)))
                   (gquot_poly_gcl S a)
                 @ poly_map_gquot_counit_map_gcl S a).
      refine (_ @ !(homotsec_natural pX (!q))).
      cbn.
      unfold q.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        apply pathsinv0inv0.
      }
      refine (!_).
      etrans.
      {
        do 2 apply maponpaths.
        exact (sem_endpoint_UU_poly_map_gquot_poly_is_path r a).
      }
      etrans.
      {
        do 2 apply maponpaths_2.
        exact (sem_endpoint_UU_poly_map_gquot_poly_is_path l a).
      }
      do 2 refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        apply pathscomp_inv.
      }
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        do 2 apply maponpaths.
        refine (!_).
        apply maponpathsinv0.
      }
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        do 2 refine (path_assoc _ _ _ @ _).
        do 2 apply maponpaths_2.
        apply pathsinv0l.
      }
      do 2 refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        do 2 apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    - exact (λ _, gtrunc _ _ _ _ _).
  Qed.
  
  Definition add2cell_lift_counit_equation
             (X : total_bicat (disp_alg_bicat (⟦ A ⟧)))
             (pX : homotsec
                     (sem_endpoint_one_types l X)
                     (sem_endpoint_one_types r X))
             (z : poly_act
                    S
                    (pr1 ((total_prealg_gquot A) ((prealg_biadjunction A) X))
                     : one_type))
    : maponpaths
        (gquot_counit_map (pr1 X))
        (lift_gquot_add2cell_obj
           l r
           (one_type_to_groupoid (pr1 X),, prealg_path_groupoid_map A (pr1 X) (pr2 X))
           (path_alg_path_groupoid_ob l r pX) z)
      @ sem_endpoint_UU_natural r (prealg_counit_comp A (pr2 X)) z
      =
      sem_endpoint_UU_natural l (prealg_counit_comp A (pr2 X)) z
      @ pX (poly_map S (gquot_counit_map (pr1 X)) z).
  Proof.
    unfold lift_gquot_add2cell_obj.
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(path_assoc _ _ _)).
    }
    etrans.
    {
      do 2 apply maponpaths.
      unfold gquot_endpoint.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          exact (pathscomp_inv _ _).
        }
        apply maponpaths.
        etrans.
        {
          refine (!_).
          apply maponpathsinv0.
        }
        apply maponpaths.
        apply pathsinv0inv0.
      }
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
        apply maponpathscomp.
      }
      apply (homotsec_natural'
               (sem_endpoint_UU_natural r (prealg_counit_comp A (pr2 X)))).
    }
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths_2.
        etrans.
        {
          apply maponpathscomp.
        }
        unfold funcomp.
        apply (maponpathsinv0
                 (λ x,
                  gquot_counit_map
                    (pr1 X)
                    ((sem_endpoint_one_types l)
                       ((total_prealg_gquot A)
                          (one_type_to_groupoid (pr1 X)
                           ,, prealg_path_groupoid_map A (pr1 X) (pr2 X)))
                          x))
                 (gquot_poly_poly_gquot z)).
      }
      apply idpath.
    }
    refine (!(path_assoc _ _ _) @ _).
    use path_inv_rotate_ll.
    etrans.
    {
      do 3 refine (path_assoc _ _ _ @ _).
      do 2 apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply maponpathscomp0.
      }
      refine (!_).
      apply maponpathscomp0.
    }
    etrans.
    {
      do 2 apply maponpaths_2.
      apply maponpaths.
      exact (add2cell_lift_counit_equation_lem₁ pX _).
    }
    refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        exact (homotsec_natural'
                 (sem_endpoint_UU_natural l (prealg_counit_comp A (pr2 X)))
                 (gquot_poly_poly_gquot z)).
      }
      apply maponpaths.
      refine (!_).
      apply maponpathscomp.

    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        exact (homotsec_natural'
                 pX
                 (maponpaths
                    (poly_map S (gquot_counit_map (pr1 X)))
                    (gquot_poly_poly_gquot z))).
      }
      apply maponpaths.
      apply maponpathscomp.
    }
    refine (path_assoc _ _ _ @ _).
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    cbn.
    unfold sem_endpoint_UU_prealg_path_groupoid_map.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths.
      apply maponpathscomp0.
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths_2.
      apply maponpathsinv0.
    }
    apply path_inv_rotate_ll.
    refine (!_).
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (maponpaths_poly_map_gcl_sem_endpoint_one_types l _).
    }
    simpl.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (maponpaths_poly_map_gcl_sem_endpoint_one_types r _).
    }
    refine (pathscomp0rid _ @ _).
    exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
  Qed.

  Definition add2cell_lift_counit
    : lift_counit_law
        (prealg_biadjunction A)
        (lift_gquot_add2cell l r)
        (@path_alg_path_groupoid_ob A S l r).
  Proof.
    intros X pX.
    use funextsec.
    intro z.
    exact (add2cell_lift_counit_equation X pX z).
  Qed.
End LiftAdd2CellUnit.
