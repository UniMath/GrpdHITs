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
  induction h ; apply TODO.
Qed.

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
