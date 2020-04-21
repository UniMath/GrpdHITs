Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Transformations.Examples.Unitality.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Modifications.Modification.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.
Require Import existence.hit_existence.
Require Import existence.initial_algebra.
Require Import examples.free_algebra.
Require Import free_alg_biadj.free_alg_functor.
Require Import free_alg_biadj.free_alg_unit.
Require Import free_alg_biadj.free_alg_counit.
Require Import free_alg_biadj.free_alg_biadjunction_unit_counit.
Require Import free_alg_biadj.free_alg_left_triangle.
Require Import free_alg_biadj.free_alg_right_triangle.

Local Open Scope cat.

Definition free_alg_biadj
           (Σ : hit_signature)
  : left_biadj_data (free_alg_psfunctor Σ).
Proof.
  use make_biadj_data.
  - exact (free_alg_unit_counit Σ).
  - exact (free_alg_left_triangle Σ).
  - exact (free_alg_right_triangle Σ).
Defined.





(* Definition of coherent biadjunctions *)
Definition biadj_unit_ob
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₁)
  : x --> R(L x).
Proof.
  pose (biadj_unit R x) as f.
  simpl in f.
  exact f.
Defined.

Definition biadj_counit_ob
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₂)
  : L(R x) --> x.
Proof.
  pose (biadj_counit R x) as f.
  simpl in f.
  exact f.
Defined.

Definition biadj_left_triangle_ob
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₁)
  : invertible_2cell
      (#L (biadj_unit (pr1 R) x) · biadj_counit (pr1 R) (L x))
      (id₁ (L x)).
Proof.
  pose (invertible_modcomponent_of (biadj_triangle_l R) x) as p.    
  use make_invertible_2cell.
  - refine (_ • p).
    cbn.
    exact ((_ ◃ (rinvunitor _ • linvunitor _)) • linvunitor _).
  - simpl.
    is_iso.
    apply p.
Defined.

Definition biadj_left_triangle_inv_ob
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₁)
  : id₁ (L x)
    ==>
    #L (biadj_unit (pr1 R) x) · biadj_counit (pr1 R) (L x)
  := (biadj_left_triangle_ob L R x)^-1.

Definition biadj_right_triangle_ob
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₂)
  : invertible_2cell
      (biadj_unit (pr1 R) (pr1 R x) · # (pr1 R) (biadj_counit (pr1 R) x))
      (id₁ (pr1 R x)).
Proof.
  pose (invertible_modcomponent_of (biadj_triangle_r R) x) as p.
  use make_invertible_2cell.
  - refine (_ • p).
    cbn.
    exact ((_ ◃ (rinvunitor _ • linvunitor _)) • linvunitor _).
  - simpl.
    is_iso.
    apply p.
Defined.

Definition biadj_right_triangle_inv_ob
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₂)
  : id₁ (pr1 R x)
    ==>
    biadj_unit (pr1 R) (pr1 R x) · # (pr1 R) (biadj_counit (pr1 R) x)
  := (biadj_right_triangle_ob L R x)^-1.

Definition test
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₂)
  : id₁ (L(R x)) · biadj_counit_ob L R x
    ==>
    id₁ (L(R x)) · biadj_counit_ob L R x.
Proof.
  exact (((psfunctor_id L (R x)
            • ## L (biadj_right_triangle_inv_ob L R x)
            • (psfunctor_comp L _ _)^-1)
             ▹ _)
          • rassociator _ _ _
          • (_ ◃ ((psnaturality_of
                     (biadj_counit R)
                     (biadj_counit_ob L R x))^-1))
          • lassociator _ _ _
          • (biadj_left_triangle_ob L R (R x) ▹ _)).
Defined.

Definition test2
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
           (x : B₁)
  : biadj_unit_ob L R x · id₁ (R(L x))
    ==>
    biadj_unit_ob L R x · id₁ (R(L x)).
Proof.
  exact ((_ ◃ biadj_right_triangle_inv_ob L R (L x))
         • lassociator _ _ _
         • ((psnaturality_of
               (biadj_unit R)
               (biadj_unit (pr1 R) x))^-1 ▹ _)
         • rassociator _ _ _
         • (_ ◃ (psfunctor_comp R _ _
                 • ##R (biadj_left_triangle_ob L R x)
                 • (psfunctor_id R (L x))^-1))).
Defined.

Definition is_coherent_biadj
           {B₁ B₂ : bicat}
           (L : psfunctor B₁ B₂)
           (R : left_biadj_data L)
  : UU
  := (∏ (x : B₁), test2 L R x = id₂ _)
     ×
     (∏ (x : B₂), test L R x = id₂ _).

Definition coherent_biadj
           (B₁ B₂ : bicat)
  : UU
  := ∑ (L : psfunctor B₁ B₂)
       (R : left_biadj_data L),
     is_coherent_biadj L R.
