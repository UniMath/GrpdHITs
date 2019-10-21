(**
The unit of the biadjunction when adding a 2-cell to the algebra structure
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

Definition poly_map_gcl_is_gquot_poly
           {P : poly_code}
           {G : groupoid}
           (x : poly_act P G)
  : poly_map P (gcl G) x
    =
    gquot_poly (gcl (poly_act_groupoid P G) x).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x)).
    + exact (maponpaths inr (IHP₂ x)).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Defined.

Definition poly_map_sem_endpoint_UU_gquot_poly
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (x : poly_act S (pr11 G))
  : poly_map
      T
      (gcl (pr1 G))
      (sem_endpoint_UU e (λ z, pr12 G z) x)
    =
    sem_endpoint_UU
      e
      (prealg_gquot_map A (pr1 G) (pr2 G))
      (gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x)).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - exact (poly_map_gcl_is_gquot_poly x).
  - exact (IHe₂ (sem_endpoint_UU e₁ (λ z, (pr12 G) z) x)
           @ maponpaths
               (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))
               (!(poly_map_gcl_is_gquot_poly
                    (sem_endpoint_UU e₁ (λ z, (pr12 G) z) x))
                @ IHe₁ x)).
  - exact (maponpaths inl (poly_map_gcl_is_gquot_poly x)).
  - exact (maponpaths inr (poly_map_gcl_is_gquot_poly x)).
  - exact (poly_map_gcl_is_gquot_poly (pr1 x)).
  - exact (poly_map_gcl_is_gquot_poly (pr2 x)).
  - exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  - exact (idpath _).
  - exact (idpath _).
  - refine (maponpaths (gquot_functor_map (pr2 G)) (prealg_unit_comp_help A x)
            @ _).
    refine (maponpaths
              (λ z, gquot_functor_map (pr2 G) (poly_gquot A (pr1 G) z))
              _).
    refine (poly_path_groupoid_is_id _ @ _).
    exact (poly_map_gcl_is_gquot_poly x).
Defined.

Definition poly_map_sem_endpoint_UU
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (x : poly_act S (pr11 G))
  : poly_map
      T
      (gcl (pr1 G))
      (sem_endpoint_UU e (λ z, pr12 G z) x)
    =
    sem_endpoint_UU
      e
      (prealg_gquot_map A (pr1 G) (pr2 G))
      (poly_map S (gcl (pr1 G)) x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - exact (idpath _).
  - exact (IHe₂ (sem_endpoint_UU e₁ (λ z, (pr12 G) z) x)
           @ maponpaths
               (sem_endpoint_UU e₂ (prealg_gquot_map A (pr1 G) (pr2 G)))
               (IHe₁ x)).
  - exact (idpath _).
  - exact (idpath _).
  - exact (idpath _).
  - exact (idpath _).
  - exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  - exact (idpath _).
  - exact (idpath _).
  - refine (maponpaths (gquot_functor_map (pr2 G)) (prealg_unit_comp_help A x)
            @ _).
    refine (maponpaths
              (λ z, gquot_functor_map (pr2 G) (poly_gquot A (pr1 G) z))
              _).
    apply poly_path_groupoid_is_id.
Defined.

Definition is_poly_map_sem_endpoint_UU_help
           {P : poly_code}
           {G : groupoid}
           (x : poly_act P (pr1 G))
  : poly_act_morphism_path_groupoid
      (@poly_act_identity
         P (one_type_to_groupoid (gquot_functor_obj G))
         (poly_map P (gcl G) x))
    =
    idpath (poly_map P (gcl G) x).
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (IHP₁ x)).
    + exact (maponpaths (maponpaths inr) (IHP₂ x)).
  - exact (paths_pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Qed.
  
Definition is_poly_map_sem_endpoint_UU
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (x : poly_act S (pr11 G))
  : poly_act_morphism_path_groupoid
      (sem_endpoint_grpd_natural_data
         e
         ((biadj_unit
             (total_left_biadj_unit_counit
                (disp_alg_bicat ⦃ A ⦄) (disp_alg_bicat (⟦ A ⟧))
                (algebra_disp_biadjunction_unit_counit A))) G)
         x)
    @ @path_groupoid_endpoint
        _ _ _
        e
        ((total_prealg_gquot A) G) (poly_map S (gcl (pr1 G)) x)
    =
    poly_map_sem_endpoint_UU e x.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - etrans.
    {
      apply pathscomp0rid.
    }
    exact (is_poly_map_sem_endpoint_UU_help x).
  - simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (!(IHe₂ _)).
    }
    clear IHe₂.
    etrans.
    {
      do 2 apply maponpaths.
      exact (!(IHe₁ _)).
    }
    clear IHe₁.
    refine (_ @ !(path_assoc _ _ _)).
    etrans.
    {
      apply maponpaths.
      apply maponpathscomp0.
    }
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      pose (homotsec_natural'
               (path_groupoid_endpoint e₂)
               (poly_act_morphism_path_groupoid
                  (sem_endpoint_grpd_natural_data
                     e₁
                     ((biadj_unit
                         (total_left_biadj_unit_counit
                            (disp_alg_bicat ⦃ A ⦄) 
                            (disp_alg_bicat (⟦ A ⟧))
                            (algebra_disp_biadjunction_unit_counit A))) G) x)))
        as h.
      simpl in h.
      exact (!h).
    }
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      exact (poly_act_morphism_path_groupoid_compose
               (sem_endpoint_grpd_natural_data
                  e₂
                  ((biadj_unit
                      (total_left_biadj_unit_counit
                         (disp_alg_bicat ⦃ A ⦄) 
                         (disp_alg_bicat (⟦ A ⟧))
                         (algebra_disp_biadjunction_unit_counit A))) G)
                  (sem_endpoint_UU e₁ (λ z, (pr12 G) z) x))
               (sem_endpoint_grpd_data_functor_morphism
                  e₂
                  (prealg_path_groupoid_map
                     A (gquot_functor_obj (pr1 G))
                     (prealg_gquot_map A (pr1 G) (pr2 G)))
                  (sem_endpoint_grpd_natural_data
                     e₁
                     ((biadj_unit
                         (total_left_biadj_unit_counit
                            (disp_alg_bicat ⦃ A ⦄) 
                            (disp_alg_bicat (⟦ A ⟧))
                            (algebra_disp_biadjunction_unit_counit A))) G) x))).
    }
    apply maponpaths.
    refine (!_).
    apply poly_act_morphism_path_groupoid_functor.
  - etrans.
    {
      apply pathscomp0rid.
    }
    exact (maponpaths (maponpaths inl) (is_poly_map_sem_endpoint_UU_help x)).
  - etrans.
    {
      apply pathscomp0rid.
    }
    exact (maponpaths (maponpaths inr) (is_poly_map_sem_endpoint_UU_help x)).
  - etrans.
    {
      apply pathscomp0rid.
    }
    exact (is_poly_map_sem_endpoint_UU_help (pr1 x)).
  - etrans.
    {
      apply pathscomp0rid.
    }
    exact (is_poly_map_sem_endpoint_UU_help (pr2 x)).
  - refine (pathsdirprod_concat _ _ _ _ @ _).
    exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
  - apply idpath.
  - apply idpath.
  - apply idpath.
Qed.

Definition poly_map_sem_endpoint_UU_is_gquot_poly
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (x : poly_act S (pr11 G))
  : poly_map_sem_endpoint_UU e x
    =
    poly_map_sem_endpoint_UU_gquot_poly e x
    @ maponpaths
        (sem_endpoint_UU e (prealg_gquot_map A (pr1 G) (pr2 G)))
        (! poly_map_gcl_is_gquot_poly x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpathsidfun.
    }
    apply pathsinv0r.
  - simpl.
    refine (_ @ path_assoc _ _ _).
    etrans.
    {
      apply maponpaths_2.
      apply IHe₂.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathscomp.
    }
    refine (!(maponpathscomp0 _ _ _) @ _).
    refine (!_).
    apply maponpaths.
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    apply IHe₁.
  - simpl.
    refine (!_).
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths.
      apply pathsinv0r.
    }
    apply idpath.
  - simpl.
    refine (!_).
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths.
      apply pathsinv0r.
    }
    apply idpath.
  - simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      apply maponpaths_pr1_pathsdirprod.
    }
    apply pathsinv0r.
  - simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      apply maponpaths_pr2_pathsdirprod.
    }
    apply pathsinv0r.
  - simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_prod_path.
    }
    etrans.
    {
      apply pathsdirprod_concat.
    }
    refine (!_).
    exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
  - simpl.
    refine (!_).
    apply maponpaths_for_constant_function.
  - simpl.
    apply idpath.
  - simpl.
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      apply (maponpathscomp0
               (λ z, gquot_functor_map (pr2 G) ((poly_gquot A) (pr1 G) z))).
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        refine (!_).
        apply (maponpathscomp0
                 (λ z, gquot_functor_map (pr2 G) ((poly_gquot A) (pr1 G) z))).
      }
      apply maponpaths.
      apply pathsinv0r.
    }
    apply pathscomp0rid.
Qed.

Definition poly_map_gcl_is_gquot_poly_is_gquot_endpoint_help_constr
           {P : poly_code}
           {G : groupoid}
           (x : poly_act P (pr1 G))
  : (prealg_unit_comp_help P x
     @ maponpaths
         (poly_gquot P G)
         (@poly_path_groupoid_is_id P (gquot_functor_obj G) (poly_map P (gcl G) x)
          @ poly_map_gcl_is_gquot_poly x))
  @ poly_gquot_gquot_poly (gcl (poly_act_groupoid P G) x)
  =
  idpath _.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + simpl.
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        refine (!_).
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpathscomp. 
        }
        refine (!_).
        exact (maponpathscomp
                 (poly_gquot P₁ G)
                 gquot_inl_grpd
                 _).
      }
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathscomp0
                 gquot_inl_grpd
                 (prealg_unit_comp_help P₁ x)).
      }
      etrans.
      {
        refine (!_).
        exact (maponpathscomp0
                 gquot_inl_grpd
                 (prealg_unit_comp_help P₁ x @ _)
                 (poly_gquot_gquot_poly_comp P₁ x)).
      }
      etrans.
      {
        apply maponpaths.
        apply IHP₁.
      }
      apply idpath.
    + simpl.
      etrans.
      {
        apply maponpaths_2.
        do 2 apply maponpaths.
        refine (!_).
        apply maponpathscomp0.
      }
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        etrans.
        {
          apply maponpathscomp. 
        }
        refine (!_).
        exact (maponpathscomp
                 (poly_gquot P₂ G)
                 gquot_inr_grpd
                 _).
      }
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathscomp0
                 gquot_inr_grpd
                 (prealg_unit_comp_help P₂ x)).
      }
      etrans.
      {
        refine (!_).
        exact (maponpathscomp0
                 gquot_inr_grpd
                 (prealg_unit_comp_help P₂ x @ _)
                 (poly_gquot_gquot_poly_comp P₂ x)).
      }
      etrans.
      {
        apply maponpaths.
        apply IHP₂.
      }
      apply idpath.
  - simpl.
    etrans.
    {
      apply maponpaths_2.
      do 2 apply maponpaths.
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      exact (maponpathscomp
               (dirprodf (poly_gquot P₁ G) (poly_gquot P₂ G))
               (λ z, prod_gquot_comp (pr1 z) (dirprod_pr2 z))
               (pathsdirprod _ _)).
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
      refine (!_).
      exact (maponpathscomp0
               (λ z,
                prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod
                  (prealg_unit_comp_help P₁ (pr1 x))
                  (prealg_unit_comp_help P₂ (pr2 x)))
               (pathsdirprod _ _)).
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      apply pathsdirprod_concat.
    }
    etrans.
    {
      apply maponpaths.
      pose (uncurry_ap
              prod_gquot_comp
              (poly_gquot_gquot_poly_comp P₁ (pr1 x))
              (poly_gquot_gquot_poly_comp P₂ (pr2 x)))
        as h.
      unfold uncurry in h.
      exact (!h).
    }
    etrans.
    {
      refine (!_).
      exact (maponpathscomp0
               (λ z,
                prod_gquot_comp (pr1 z) (pr2 z))
               (pathsdirprod
                  (prealg_unit_comp_help P₁ (pr1 x) @ _)
                  (prealg_unit_comp_help P₂ (pr2 x) @ _))
               (pathsdirprod
                  (poly_gquot_gquot_poly_comp P₁ (pr1 x))
                  (poly_gquot_gquot_poly_comp P₂ (pr2 x)))).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply pathsdirprod_concat.
      }
      exact (paths_pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
    }
    apply idpath.
Qed.
  
Definition poly_map_gcl_is_gquot_poly_is_gquot_endpoint_help
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (x : poly_act S (pr11 G))
  : poly_map_sem_endpoint_UU_gquot_poly e x
    @ gquot_endpoint_help e (gcl (poly_act_groupoid S (pr1 G)) x)
    =
    poly_map_gcl_is_gquot_poly (sem_endpoint_UU e (λ z, (pr12 G) z) x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ].
  - apply pathscomp0rid.
  - simpl.
    refine (_ @ IHe₂ _).
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (_ @ pathscomp0lid _).
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths.
      do 2 apply maponpaths_2.
      apply maponpaths.
      exact (!(IHe₁ _)).
    }
    refine (_ @ maponpaths_idpath).
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    apply pathsinv0l.
  - apply pathscomp0rid.
  - apply pathscomp0rid.
  - apply pathscomp0rid.
  - apply pathscomp0rid.
  - simpl.
    etrans.
    {
      apply pathsdirprod_concat.
    }
    exact (paths_pathsdirprod (IHe₁ x) (IHe₂ x)).
  - apply idpath.
  - apply idpath.
  - simpl.
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths.
      refine (!_).
      apply (maponpathscomp
               (poly_gquot A (pr1 G))
               (gquot_functor_map (pr2 G))).
    }
    etrans.
    {
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        exact (maponpathscomp0
                 (gquot_functor_map (pr2 G))
                 (prealg_unit_comp_help A x)
                 _).
      }
      refine (!_).
      exact (maponpathscomp0
               (gquot_functor_map (pr2 G))
               (prealg_unit_comp_help A x @ _)
               (poly_gquot_gquot_poly (gcl (poly_act_groupoid A (pr1 G)) x))).
    }
    refine (_ @ maponpaths_idpath).
    apply maponpaths.
    apply poly_map_gcl_is_gquot_poly_is_gquot_endpoint_help_constr.
Qed.

Definition poly_map_gcl_is_gquot_poly_is_gquot_endpoint
           {A S T : poly_code}
           (e : endpoint A S T)
           {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
           (x : poly_act S (pr11 G))
  : (poly_map_sem_endpoint_UU_gquot_poly e x
  @ gquot_endpoint e (gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x)))
  @ maponpaths
      (λ z, gquot_poly
              (gquot_functor_map (sem_endpoint_grpd_data_functor e G) z))
      (poly_gquot_gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x))
  =
  poly_map_gcl_is_gquot_poly (sem_endpoint_UU e (λ z, (pr12 G) z) x).
Proof.
  unfold gquot_endpoint.
  refine (!(path_assoc _ _ _) @ _).
  etrans.
  {
    apply maponpaths.
    pose (homotsec_natural'
            (gquot_endpoint_help e)
            (poly_gquot_gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x)))
      as h.
    refine (!(path_assoc _ _ _) @ _).
    simpl in h.
    apply maponpaths.
    exact (!h).
  }
  etrans.
  {
    apply maponpaths.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply maponpathscomp.
    }
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_poly_gquot_gquot_poly.
    }
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    apply maponpaths.
    apply pathsinv0l.
  }
  exact (poly_map_gcl_is_gquot_poly_is_gquot_endpoint_help e x).
Qed.

Section LiftAdd2CellUnit.
  Context {A S : poly_code}
          (l r : endpoint A S I).

  Definition add2cell_lift_unit_lem₂
             {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
             (pG : sem_endpoint_grpd_data_functor_data l G
                   ⟹
                   sem_endpoint_grpd_data_functor_data r G)
             (x : poly_act S (pr11 G))
    : gcleq (pr1 G) (pr1 pG x)
      @ poly_map_sem_endpoint_UU_gquot_poly r x
      =
      poly_map_sem_endpoint_UU_gquot_poly l x
      @ lift_gquot_add2cell_obj
          l r G pG
          (gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x)).
  Proof.
    unfold lift_gquot_add2cell_obj.
    pose (homotsec_natural
            (λ z,
             maponpaths
               gquot_poly
               (@gquot_functor_cell
                  _ _
                  (sem_endpoint_grpd_data_functor l G)
                  (sem_endpoint_grpd_data_functor r G)
                  pG
                  z))
            (! poly_gquot_gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x)))
      as h.
    simpl in h.
    refine (!_).
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      exact h.
    }
    clear h.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpaths_2.
      exact (gquot_rec_beta_gcleq _ _ _ _ _ _ _ _ _ _).
    }
    etrans.
    {
      do 2 apply maponpaths.
      do 2 apply maponpaths_2.
      apply maponpaths.
      apply pathsinv0inv0.
    }
    etrans.
    {
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact (poly_map_gcl_is_gquot_poly_is_gquot_endpoint l x).
    }
    etrans.
    {
      apply maponpaths_2.
      apply pathscomp0lid.
    }
    etrans.
    {
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathsinv0
                 (λ z,
                  gquot_id
                    (pr1 G)
                    (gquot_functor_map (sem_endpoint_grpd_data_functor r G) z))
                 (poly_gquot_gquot_poly (gcl (poly_act_groupoid S (pr1 G)) x))).
      }
      refine (!_).
      apply pathscomp_inv.
    }
    use path_inv_rotate_lr.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      exact (poly_map_gcl_is_gquot_poly_is_gquot_endpoint r x).
    }
    apply pathscomp0rid.
  Qed.

  Definition add2cell_lift_unit_lem₁
             {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
             (pG : sem_endpoint_grpd_data_functor_data l G
                   ⟹
                   sem_endpoint_grpd_data_functor_data r G)
             (x : poly_act S (pr11 G))
    : gcleq (pr1 G) (pr1 pG x)
      @ poly_map_sem_endpoint_UU r x
      =
      poly_map_sem_endpoint_UU l x
      @ lift_gquot_add2cell_obj l r G pG (poly_map S (gcl (pr1 G)) x).
  Proof.
    etrans.
    {
      apply maponpaths.
      exact (poly_map_sem_endpoint_UU_is_gquot_poly r x).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      exact (poly_map_sem_endpoint_UU_is_gquot_poly l x).
    }
    refine (!_).
    refine (path_assoc _ _ _ @ _).
    etrans.
    {
      apply maponpaths_2.
      exact (add2cell_lift_unit_lem₂ pG x).
    }
    rewrite <- !path_assoc.
    apply maponpaths.
    exact (!homotsec_natural'
            (lift_gquot_add2cell_obj l r G pG)
            (!(poly_map_gcl_is_gquot_poly x))).        
  Qed.

  Definition add2cell_lift_unit_law
             {G : total_bicat (disp_alg_bicat ⦃ A ⦄)}
             (pG : sem_endpoint_grpd_data_functor_data l G
                   ⟹
                   sem_endpoint_grpd_data_functor_data r G)
             (x : poly_act S (pr11 G))
    : gcleq (pr1 G) (pr1 pG x)
      @ sem_endpoint_grpd_natural_data
          r
          (biadj_unit
              (total_left_biadj_unit_counit
                 (disp_alg_bicat ⦃ A ⦄) (disp_alg_bicat (⟦ A ⟧))
                 (algebra_disp_biadjunction_unit_counit A)) G)
          x
      =
      sem_endpoint_grpd_natural_data
        l
        (biadj_unit
           (total_left_biadj_unit_counit
              (disp_alg_bicat ⦃ A ⦄) (disp_alg_bicat (⟦ A ⟧))
              (algebra_disp_biadjunction_unit_counit A)) G)
        x
      @ @path_alg_path_groupoid_ob_comp
          _ _ l r
          ((total_prealg_gquot A) G)
          (lift_gquot_add2cell_obj l r G pG)
          (poly_map S (gcl (pr1 G)) x).
  Proof.
    unfold path_alg_path_groupoid_ob_comp.
    refine (!_).
    do 2 refine (path_assoc _ _ _ @ _).
    etrans.
    {
      do 2 apply maponpaths_2.
      exact (is_poly_map_sem_endpoint_UU l x).
    }
    use path_inv_rotate_lr.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (is_poly_map_sem_endpoint_UU r x).
    }
    exact (add2cell_lift_unit_lem₁ pG x).
  Qed.
  
  Definition add2cell_lift_unit
    : lift_unit_law
        (prealg_biadjunction A)
        (lift_gquot_add2cell l r)
        (@path_alg_path_groupoid_ob A S l r).
  Proof.
    intros G pG.
    use nat_trans_eq.
    { apply homset_property. }
    intro x.
    exact (add2cell_lift_unit_law pG x).
  Qed.
End LiftAdd2CellUnit.
