(**
Biadjunction when adding a 2-cell to the algebra structure
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
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
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
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
Require Import algebra.one_types_homotopies.
Require Import algebra.groupoid_homotopies.
Require Import biadjunctions.all.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import hit_biadjunction.gquot_natural.
Require Import hit_biadjunction.hit_prealgebra_biadj.
Require Import hit_biadjunction.hit_path_algebra_biadj.

Local Open Scope cat.

(** Necessary operation *)
Definition poly_act_morphism_to_path
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
  : x = y → poly_act_morphism P G x y.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (λ p, p).
  - exact (λ p, pr1 (@idtoiso G _ _ p)).
  - induction x as [x | x], y as [y | y].
    + exact (λ p, IHP₁ x y (ii1_injectivity _ _ p)).
    + exact (λ p, fromempty (negpathsii1ii2 _ _ p)).
    + exact (λ p, fromempty (negpathsii2ii1 _ _ p)).
    + exact (λ p, IHP₂ x y (ii2_injectivity _ _ p)).
  - exact (λ p, IHP₁ _ _ (maponpaths pr1 p) ,, IHP₂ _ _ (maponpaths dirprod_pr2 p)).
Defined.

(** Lemmata *)
Definition poly_act_morphism_to_path_idpath
           {P : poly_code}
           {X : groupoid}
           (x : poly_act P X)
  : poly_act_morphism_to_path (idpath x) = poly_act_identity x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Qed.

Definition poly_act_compose_poly_act_morphism_to_path
           {P : poly_code}
           {X : groupoid}
           {x y z : poly_act P X}
           (p : x = y) (q : y = z)
  : poly_act_compose
      (poly_act_morphism_to_path p)
      (poly_act_morphism_to_path q)
    =
    poly_act_morphism_to_path (p @ q).
Proof.
  induction p ; induction q.
  simpl.
  etrans.
  {
    apply maponpaths.
    apply poly_act_morphism_to_path_idpath.
  }
  apply poly_act_id_right.
Qed.
  
Definition ii1_injectivity_maponpaths_inl
           {A B : UU}
           {x y : A}
           (p : x = y)
  : @ii1_injectivity A B x y (maponpaths inl p) = p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition ii2_injectivity_maponpaths_inr
           {A B : UU}
           {x y : B}
           (p : x = y)
  : @ii2_injectivity A B x y (maponpaths inr p) = p.
Proof.
  induction p.
  apply idpath.
Defined.

Definition poly_act_morphism_to_path_path_groupoid
           {X : one_type}
           {x y : poly_act I (one_type_to_groupoid X)}
           (g : x = y)
  : poly_act_morphism_to_path g = g.
Proof.
  induction g.
  apply idpath.
Qed.

Definition poly_act_morphism_to_path_poly_act_groupoid
           {P : poly_code}
           {X : one_type}
           {x y : poly_act P (one_type_to_groupoid X)}
           (g : poly_act_morphism P (one_type_to_groupoid X) x y)
  : poly_act_morphism_to_path (poly_act_groupoid_to_path g) = g.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - induction g.
    apply idpath.
  - induction x as [x | x], y as [y |y].
    + refine (_ @ IHP₁ _ _ g).
      simpl.
      etrans.
      {
        apply maponpaths.
        apply ii1_injectivity_maponpaths_inl.
      }
      apply idpath.
    + exact (fromempty g).
    + exact (fromempty g).
    + refine (_ @ IHP₂ _ _ g).
      simpl.
      etrans.
      {
        apply maponpaths.
        apply ii2_injectivity_maponpaths_inr.
      }
      apply idpath.    
  - simpl.
    etrans.
    {
      do 2 apply maponpaths.
      apply maponpaths_pr2_pathsdirprod.
    }
    etrans.
    {
      apply maponpaths_2 ; apply maponpaths.
      apply maponpaths_pr1_pathsdirprod.
    }
    exact (pathsdirprod (IHP₁ _ _ (pr1 g)) (IHP₂ _ _ (pr2 g))).
Qed.

Definition path_groupoid_path_arg
           {Σ : hit_signature}
           {X : hit_path_algebra_one_types Σ}
           {P Q : poly_code}
           {l r : endpoint (point_constr Σ) P Q}
           {z : poly_act P (pr11 X : one_type)}
           (p : pr1 (sem_endpoint_grpd
                       l
                       (pr1 (hit_path_algebra_biadjunction Σ X)))
                       z
                -->
                pr1 (sem_endpoint_grpd
                       r
                       (pr1 (hit_path_algebra_biadjunction Σ X)))
                       z)
  : sem_endpoint_one_types l (pr1 X) z
    =
    sem_endpoint_one_types r (pr1 X) z.
Proof.
  refine (!(path_groupoid_endpoint _ _) @ _ @ path_groupoid_endpoint _ _).
  apply poly_act_groupoid_to_path.
  exact p.
Defined.

(* NEEDS TO BE CHANGED *)

Definition poly_path_groupoid_poly_act_morphism_to_path
           {A P Q : poly_code}
           {X : one_type}
           {a₁ a₂ : poly_act P (path_groupoid X : groupoid)}
           (c : poly_act A X → X)
           (e : endpoint A P Q)
           (w : a₁ = a₂)
  : sem_endpoint_grpd_data_functor_morphism
      e
      (prealg_path_groupoid_map A X c)
      (poly_act_morphism_to_path w)
    =
    poly_act_morphism_to_path
      (maponpaths
         (sem_endpoint_UU e _)
         w).
Proof.
  induction w.
  etrans.
  {
    apply maponpaths.
    exact (poly_act_morphism_to_path_idpath _).
  }
  simpl.
  etrans.
  {
    exact (functor_id
             (sem_endpoint_grpd e (path_groupoid X ,, prealg_path_groupoid_map A X c))
             a₁).
  }
  exact (!(poly_act_morphism_to_path_idpath (sem_endpoint_UU e _ a₁))).
Qed.
    
(*
Definition poly_path_groupoid_poly_act_morphism_to_path
           {P : poly_code}
           {X : one_type}
           {a₁ a₂ : poly_act P (path_groupoid X : groupoid)}
           (w : a₁ = a₂)
  : # ((poly_path_groupoid P) X : _ ⟶ _) (poly_act_morphism_to_path w)
    =
    maponpaths (pr1 ((poly_path_groupoid P) X)) w.
Proof.
  induction w.
  etrans.
  {
    apply maponpaths.
    exact (poly_act_morphism_to_path_idpath _).
  }
  exact (functor_id (poly_path_groupoid P X) _).
Qed.
 *)

Definition poly_act_morphism_to_path_inv
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (p : x = y)
  : poly_act_morphism_to_path (! p)
    =
    poly_act_inverse (poly_act_morphism_to_path p).
Proof.
  induction p.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply idpath.
  - simpl.
    refine (_ @ id_left _).
    rewrite (iso_inv_after_iso (make_iso (id₁ x) _)).
    apply idpath.
  - induction x as [x  | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
Qed.

Definition sem_homot_endpoint_grpd_one_type
           (Σ : hit_signature)
           {X : hit_path_algebra_one_types Σ}
           {Q TR T : poly_code}
           {al ar : endpoint (point_constr Σ) Q TR}
           {l r : endpoint (point_constr Σ) Q T}
           (h : homot_endpoint
                  (path_left Σ) (path_right Σ)
                  al ar l r)
           (z : poly_act Q (pr11 X : one_type))
           (p : pr1 (sem_endpoint_grpd
                       al
                       (pr1 ((hit_path_algebra_biadjunction Σ) X)))
                    z
                -->
                pr1 (sem_endpoint_grpd
                       ar
                       (pr1 (hit_path_algebra_biadjunction Σ X)))
                    z)
  : sem_homot_endpoint_grpd
      h
      (pr1 ((hit_path_algebra_biadjunction Σ) X))
      (pr2 ((hit_path_algebra_biadjunction Σ) X))
      z
      p
    =
    poly_act_morphism_to_path
      (path_groupoid_endpoint
         l z
       @ sem_homot_endpoint_one_types
           h
           (pr1 X)
           (pr2 X)
           z
           (path_groupoid_path_arg p)
       @ !(path_groupoid_endpoint r z)).
Proof.
  induction h as [T e | T e₁ e₂ h IHh | T e₁ e₂ e₃ h₁ IHh₁ h₂ IHh₂
                  | T₁ T₂ e₁ e₂ e₃
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | P R e₁ e₂ | P R e₁ e₂
                  | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                  | P₁ P₂ P₃ e₁ e₂ e₃
                  | W w T e
                  | j e | ].

  - refine (!_).
    etrans.
    {
      apply maponpaths.
      apply pathsinv0r.
    }
    exact (poly_act_morphism_to_path_idpath _).
  - refine (maponpaths _ IHh
            @ !(poly_act_morphism_to_path_inv
                  (path_groupoid_endpoint e₁ z
                   @ sem_homot_endpoint_one_types
                       h (pr1 X) (pr2 X) z
                       (path_groupoid_path_arg p)
                   @ ! path_groupoid_endpoint e₂ z))
              @ maponpaths poly_act_morphism_to_path _).
    etrans.
    {
      apply pathscomp_inv.
    }
    refine (_ @ !(path_assoc _ _ _)).
    apply maponpaths_2.
    etrans.
    {
      apply pathscomp_inv.
    }
    apply maponpaths_2.
    apply pathsinv0inv0.
  - refine (maponpaths (λ z, poly_act_compose z _) IHh₁ @ _).
    refine (maponpaths (λ z, poly_act_compose _ z) IHh₂ @ _).
    etrans.
    {
      apply poly_act_compose_poly_act_morphism_to_path.
    }
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!(path_assoc _ _ _) @ _).
    refine (_ @ path_assoc _ _ _).
    apply maponpaths.
    do 2 refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (_ @ pathscomp0lid _).
    apply maponpaths_2.
    apply pathsinv0l.
  - simpl.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply pathscomp_inv.
        }
        apply maponpaths_2.
        exact (!(maponpathsinv0 (sem_endpoint_UU e₃ (pr21 X)) _)).
      }
      do 2 refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths_2.
        refine (!_).
        apply (maponpathscomp0 (sem_endpoint_UU e₃ (pr21 X))).
      }
      refine (!_).
      apply (maponpathscomp0 (sem_endpoint_UU e₃ (pr21 X))).
    }
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact IHh.
    }
    clear IHh.
    etrans.
    {
      apply poly_path_groupoid_poly_act_morphism_to_path.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      etrans.
      {
        apply maponpathscomp0.
      }
      apply maponpaths_2.
      apply maponpathscomp0.
    }
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact (!(path_assoc _ _ _)).
      }
      apply maponpaths_2.
      apply path_assoc.
    }
    etrans.
    {
      pose (homotsec_natural'
              (λ z, path_groupoid_endpoint e₃ z)
              (path_groupoid_endpoint e₁ z))
        as q.
      cbn in q.
      do 2 apply maponpaths_2.
      exact (!q).
    }
    do 2 refine (!(path_assoc _ _ _) @ _).
    refine (!_).
    etrans.
    {
      apply maponpathscomp0.
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      pose (homotsec_natural'
              (λ z, !(path_groupoid_endpoint e₃ z))
              (!(path_groupoid_endpoint e₂ z)))
        as q.
      cbn in q.
      exact q.
    }
    do 2 refine (path_assoc _ _ _ @ _).
    refine (!_).
    etrans.
    {
      apply maponpathscomp0.
    }
    apply maponpaths_2.
    refine (!_).
    etrans.
    {
      apply maponpaths_2.
      refine (!_).
      apply (homotsec_natural'
               (λ z, path_groupoid_endpoint e₃ z)
               (sem_homot_endpoint_one_types h (pr1 X) (pr2 X) z (path_groupoid_path_arg p))).
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      apply pathsinv0r.
    }
    apply pathscomp0rid.
  - refine (!_).
    etrans.
    {
      apply maponpaths.
      simpl.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathscomp_inv.
      }
      etrans.
      {
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          apply maponpaths.
          etrans.
          {
            apply maponpaths.
            apply maponpathscomp0.
          }
          apply pathscomp_inv.
        }
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        etrans.
        {
          do 2 apply maponpaths.
          apply maponpathscomp.
        }
        apply pathsinv0r.
      }
      apply maponpaths_2.
      apply pathscomp0lid.
    }
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        refine (path_assoc _ _ _ @ _).
        etrans.
        {
          apply maponpaths_2.
          apply pathsinv0r.
        }
        apply pathscomp0lid.
      }
      apply pathsinv0r.
    }
    exact (poly_act_morphism_to_path_idpath _).
  - refine (!_).
    etrans.
    {
      refine (maponpaths (poly_act_morphism_to_path) _).
      etrans.
      {
        apply maponpaths_2.
        apply pathscomp0rid.
      }
      apply pathsinv0r.
    }
    exact (poly_act_morphism_to_path_idpath _).
  - refine (!_).
    etrans.
    {
      refine (maponpaths (poly_act_morphism_to_path) _).
      etrans.
      {
        refine (maponpaths (λ z, z @ _) _).
        apply maponpathsidfun.
      }
      apply pathsinv0r.
    }
    exact (poly_act_morphism_to_path_idpath _).
  - simpl.
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
    apply poly_act_morphism_to_path_idpath.
  - simpl.
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
    apply poly_act_morphism_to_path_idpath.
  - refine (pathsdirprod (IHh₁ @ !_) (IHh₂ @ !_)).
    + apply maponpaths.
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
    + apply maponpaths.
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
  - simpl.
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
            apply maponpaths_2.
            etrans.
            {
              apply maponpaths.
              apply maponpaths_prod_path.
            }
            apply pathsdirprod_concat.
          }
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply pathsdirprod_concat.
        }
        apply maponpaths_pr1_pathsdirprod.
      }
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply poly_act_morphism_to_path_idpath.
    + refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
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
          etrans.
          {
            apply maponpaths.
            apply pathsdirprod_inv.
          }
          apply pathsdirprod_concat.
        }
        apply maponpaths_pr2_pathsdirprod.
      }
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply poly_act_morphism_to_path_idpath.
  - simpl.
    refine (!_).
    etrans.
    {
      apply pathscomp0rid.
    }
    apply maponpaths_for_constant_function.
  - refine (!_).
    etrans.
    {
      apply poly_act_morphism_to_path_path_groupoid.
    }
    pose (homotsec_natural
            (pr2 X j)
            (path_groupoid_endpoint e z))
      as h.
    etrans.
    {
      apply maponpaths.
      apply maponpaths_2.
      exact h.
    }
    clear h.
    etrans.
    {
      simpl.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      etrans.
      {
        refine (!_).
        apply maponpathscomp0.
      }
      apply maponpaths.
      apply pathsinv0r.
    }
    etrans.
    {
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
      apply maponpaths.
      refine (!(path_assoc _ _ _) @ _).
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
        refine (!_).
        apply (maponpathsinv0 (sem_endpoint_UU (path_right Σ j) (pr21 X))).
      }
      etrans.
      {
        refine (!_).
        apply (maponpathscomp0 (sem_endpoint_UU (path_right Σ j) (pr21 X))).
      }
      apply maponpaths.
      apply pathsinv0r.
    }
    apply idpath.
    (*
  - refine (!_).
    etrans.
    {
      apply poly_act_morphism_to_path_path_groupoid.
    }
    simpl.
    etrans.
    {
      apply maponpaths_2.
      exact (!(maponpathscomp0 (pr21 X) _ _)).
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply pathscomp_inv.
        }
        etrans.
        {
          apply maponpaths_2.
          refine (!_).
          apply (maponpathsinv0 (pr21 X)).
        }
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply (maponpathsinv0 (pr21 X)).
        }
        exact (!(maponpathscomp0 (pr21 X) _ _)).
      }
      exact (!(maponpathscomp0 (pr21 X) _ _)).
    }
    etrans.
    {
      exact (!(maponpathscomp0 (pr21 X) _ _)).
    }
    apply maponpaths.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact IHh.
    }
    clear IHh.
    etrans.
    {
      exact (poly_path_groupoid_poly_act_morphism_to_path _).
    }
    refine (!_).
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      refine (!(path_assoc _ _ _) @ _).
      pose (homotsec_natural'
              (λ z, (poly_path_groupoid_is_id z))
              (path_groupoid_endpoint el z
               @ sem_homot_endpoint_one_types
                   h
                   (pr1 X) (pr2 X)
                   z
                   (path_groupoid_path_arg p)))
        as q.
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathsidfun _)).
      }
      exact (!q).
    }
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        pose (homotsec_natural'
                (λ z, (poly_path_groupoid_is_id z))
                (!(path_groupoid_endpoint er z)))
          as q.
        etrans.
        {
          apply maponpaths.
          exact (!(maponpathsidfun _)).
        }
        exact (!q).
      }
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    }
    etrans.
    {
      refine (!_).
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths.
      refine (!_).
      apply path_assoc.
    }
    apply idpath.
     *)
  - refine (!_).
    etrans.
    {
      refine (maponpaths (poly_act_morphism_to_path) _).
      simpl.
      unfold path_groupoid_path_arg.
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        refine (path_assoc _ _ _ @ _).
        apply maponpaths_2.
        apply pathsinv0r.
      }
      refine (!(path_assoc _ _ _) @ _).
      refine (pathscomp0lid _ @ _).
      refine (!(path_assoc _ _ _) @ _).
      etrans.
      {
        apply maponpaths.
        apply pathsinv0r.
      }
      apply pathscomp0rid.
    }
    exact (poly_act_morphism_to_path_poly_act_groupoid _).
Qed.

Definition path_groupoid_is_hit_algebra
           (Σ : hit_signature)
           (X : hit_path_algebra_one_types Σ)
  : is_hit_algebra_one_types Σ X
    →
    is_hit_algebra_grpd Σ (hit_path_algebra_biadjunction Σ X).
Proof.
  intros HX i z p.
  specialize (HX i z (path_groupoid_path_arg p)).
  refine (sem_homot_endpoint_grpd_one_type _ _ _ _
          @ _
          @ !(sem_homot_endpoint_grpd_one_type _ _ _ _)).
  rewrite HX.
  apply idpath.
Qed.
