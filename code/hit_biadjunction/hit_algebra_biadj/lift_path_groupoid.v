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

Local Definition TODO {A : UU} : A.
Admitted.

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
  - exact (λ p, pr1 (idtoiso p)).
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
           {X : one_type}
           (x : poly_act P (one_type_to_groupoid X))
  : poly_act_morphism_to_path (idpath x) = poly_act_identity _ _ x.
Proof.
  induction P as [ A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - apply idpath.
  - apply idpath.
  - induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (pathsdirprod (IHP₁ (pr1 x)) (IHP₂ (pr2 x))).
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
                ⟹
                pr1 (sem_endpoint_grpd
                       r
                       (pr1 (hit_path_algebra_biadjunction Σ X))))
  : sem_endpoint_one_types l (pr1 X) z
    =
    sem_endpoint_one_types r (pr1 X) z.
Proof.
  refine (!(path_groupoid_endpoint _ _) @ _ @ path_groupoid_endpoint _ _).
  apply poly_act_groupoid_to_path.
  exact (pr1 p z).
Defined.

Definition poly_act_morphism_to_path_inv
           {P : poly_code}
           {G : groupoid}
           {x y : poly_act P G}
           (p : x = y)
  : poly_act_morphism_to_path (! p)
    =
    poly_act_inverse P _ _ _ (poly_act_morphism_to_path p).
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

Local Arguments poly_act_compose _ _ {_ _ _} _ _.

Definition sem_homot_endpoint_grpd_one_type
           (Σ : hit_signature)
           {X : hit_path_algebra_one_types Σ}
           {Q TR T : poly_code}
           {al ar : endpoint (point_constr Σ) Q TR}
           {l r : endpoint (point_constr Σ) Q T}
           (h : homot_endpoint
                  (path_left Σ) (path_right Σ)
                  al ar l r)
           (p : pr1 (sem_endpoint_grpd
                       al
                       (pr1 ((hit_path_algebra_biadjunction Σ) X)))
                ⟹
                pr1 (sem_endpoint_grpd
                       ar
                       (pr1 (hit_path_algebra_biadjunction Σ X))))
           (z : poly_act Q (pr11 X : one_type))
  : sem_homot_endpoint_grpd
      h
      (pr1 ((hit_path_algebra_biadjunction Σ) X))
      (pr2 ((hit_path_algebra_biadjunction Σ) X))
      p
      z
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
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | T₁ T₂ e₁ e₂ e₃ e₄ h IHh | T₁ T₂ e₁ e₂ e₃ e₄ h IHh
                  | T₁ T₂ e₁ e₂ e₃ e₄ h₁ IHh₁ h₂ IHh₂
                  | T₁ T₂ e₁ e₂ | T₁ T₂ e₁ e₂
                  | j e | el er | ].
  - refine (!_).
    etrans.
    {
      apply maponpaths.
      apply pathsinv0r.
    }
    exact (poly_act_morphism_to_path_idpath _).
  - refine (_ @ maponpaths _ IHh
              @ !(poly_act_morphism_to_path_inv
                    (path_groupoid_endpoint e₁ z
                     @ sem_homot_endpoint_one_types
                         h (pr1 X) (pr2 X) z
                         (path_groupoid_path_arg p)
                     @ ! path_groupoid_endpoint e₂ z))
              @ maponpaths poly_act_morphism_to_path _).
    + simpl.
      cbn.
      apply poly_act_id_right.
    + etrans.
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
  - apply TODO.
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
        apply maponpaths.
        etrans.
        {
          refine (!_).
          apply maponpathsinv0.
        }
        apply maponpaths.
        apply pathscomp_inv.
      }
      refine (!(maponpathscomp0 _ _ _) @ _).
      apply maponpaths.
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply pathsinv0r.
      }
      apply pathscomp0lid.
    }
    etrans.
    {
      apply maponpaths.
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          refine (!_).
          apply maponpathsinv0.
        }
        exact (maponpathscomp _ _ _).
      }
      refine (!(maponpathscomp0
                  (λ q, _)
                  _
                  _) @ _).
      apply maponpaths.
      apply pathsinv0r.
    }
    exact (poly_act_morphism_to_path_idpath _).
  - refine (!_).
    etrans.
    {
      refine (maponpaths (poly_act_morphism_to_path) _).
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
        refine (pathscomp0rid (maponpaths (λ z0, z0) (path_groupoid_endpoint e z)) @ _).
        apply maponpathsidfun.
      }
      apply pathsinv0r.
    }
    exact (poly_act_morphism_to_path_idpath _).
  - refine (maponpaths pr1 IHh @ _).
    refine (maponpaths poly_act_morphism_to_path _).
    etrans.
    {
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_pr1_pathsdirprod.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths ; apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      apply maponpaths_pr1_pathsdirprod.
    }
    apply idpath.
  - refine (maponpaths dirprod_pr2 IHh @ _).
    refine (maponpaths poly_act_morphism_to_path _).
    etrans.
    {
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths_2.
      apply maponpaths_pr2_pathsdirprod.
    }
    etrans.
    {
      apply maponpaths.
      apply maponpathscomp0.
    }
    etrans.
    {
      apply maponpaths ; apply maponpaths.
      etrans.
      {
        apply maponpaths.
        apply pathsdirprod_inv.
      }
      apply maponpaths_pr2_pathsdirprod.
    }
    apply idpath.
  - apply TODO.
  - refine (!_).
    etrans.
    {
      refine (maponpaths poly_act_morphism_to_path _).
      etrans.
      {
        apply maponpaths_2.
        exact (pathscomp0rid (maponpaths inl (path_groupoid_endpoint e₁ z))).
      }
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (pathscomp0rid (maponpaths inl (path_groupoid_endpoint e₂ z))).
        }
        exact (!(maponpathsinv0 inl (path_groupoid_endpoint e₂ z))).
      }
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp0
                   inl
                   (sem_homot_endpoint_one_types
                      h (pr1 X) (pr2 X) z
                      (path_groupoid_path_arg p))
                   (! path_groupoid_endpoint e₂ z))).
      }
      exact (!(maponpathscomp0 inl _ _)).
    }
    etrans.
    {
      refine (maponpaths
                (λ z, @poly_act_morphism_to_path
                        T₁
                        (one_type_to_groupoid (pr11 X))
                        _ _
                        z) _).
      apply ii1_injectivity_maponpaths_inl.
    }
    exact (!IHh).
  - refine (!_).
    etrans.
    {
      refine (maponpaths poly_act_morphism_to_path _).
      etrans.
      {
        apply maponpaths_2.
        exact (pathscomp0rid (maponpaths inr (path_groupoid_endpoint e₁ z))).
      }
      etrans.
      {
        do 2 apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (pathscomp0rid (maponpaths inr (path_groupoid_endpoint e₂ z))).
        }
        exact (!(maponpathsinv0 inr (path_groupoid_endpoint e₂ z))).
      }
      etrans.
      {
        apply maponpaths.
        exact (!(maponpathscomp0
                   inr
                   (sem_homot_endpoint_one_types
                      h (pr1 X) (pr2 X) z
                      (path_groupoid_path_arg p))
                   (! path_groupoid_endpoint e₂ z))).
      }
      exact (!(maponpathscomp0 inr _ _)).
    }
    etrans.
    {
      refine (maponpaths
                (λ z, @poly_act_morphism_to_path
                        T₂
                        (one_type_to_groupoid (pr11 X))
                        _ _
                        z) _).
      apply ii2_injectivity_maponpaths_inr.
    }
    exact (!IHh).
  - apply TODO.
  - apply TODO.
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
Time Qed.

Definition path_groupoid_is_hit_algebra
           (Σ : hit_signature)
           (X : hit_path_algebra_one_types Σ)
  : is_hit_algebra_one_types Σ X
    →
    is_hit_algebra_grpd Σ (hit_path_algebra_biadjunction Σ X).
Proof.
  intros HX i p z.
  specialize (HX i z (path_groupoid_path_arg p)).
  refine (sem_homot_endpoint_grpd_one_type _ _ _ _
          @ _
          @ !(sem_homot_endpoint_grpd_one_type _ _ _ _)).
  rewrite HX.
  apply idpath.
Qed.
