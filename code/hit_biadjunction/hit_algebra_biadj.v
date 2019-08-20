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

Definition hit_path_algebra_gquot
           (Σ : hit_signature)
  : psfunctor (hit_path_algebra_grpd Σ) (hit_path_algebra_one_types Σ).
Proof.
  use total_psfunctor.
  - exact (total_psfunctor
             _ _
             gquot_psfunctor
             (disp_alg_psfunctor gquot_psfunctor (poly_gquot _))).
  - use disp_depprod_psfunctor.
    + intro i.
      exact (lift_gquot_add2cell (path_left Σ i) (path_right Σ i)).
    + intro i.
      apply disp_2cells_isaprop_add_cell.
    + intro i.
      apply disp_locally_groupoid_add_cell.
Defined.

Definition hit_path_algebra_biadjunction
           (Σ : hit_signature)
  := total_left_biadj_data
       _
       _
       (disp_depprod_biadjunction
          (total_left_biadj_data _ _ (algebra_biadjunction (point_constr Σ)))
          (λ (i : path_label Σ), lift_gquot_add2cell (path_left Σ i) (path_right Σ i))
          (λ i, add2cell_biadjunction (path_left Σ i) (path_right Σ i))
          (λ i, disp_2cells_isaprop_add_cell _ _ _ _ _)
          (λ i, disp_locally_groupoid_add_cell _ _ _ _ _)
          (λ i, disp_2cells_isaprop_add_cell _ _ _ _ _)
          (λ i, disp_locally_groupoid_add_cell _ _ _ _ _)).

Definition path_groupoid_is_hit_algebra
           (Σ : hit_signature)
           (X : hit_path_algebra_one_types Σ)
  : is_hit_algebra_one_types Σ X
    →
    is_hit_algebra_grpd Σ (hit_path_algebra_biadjunction Σ X).
Proof.
  intros HX i p z.
  specialize (HX i z).
  apply TODO.
Qed.

Definition gquot_is_hit_algebra
           (Σ : hit_signature)
           (X : hit_path_algebra_grpd Σ)
  : is_hit_algebra_grpd Σ X
    →
    is_hit_algebra_one_types Σ (hit_path_algebra_gquot Σ X).
Proof.
  intros HX i z p.
  specialize (HX i).
  simpl in z.
  apply TODO.
Qed.

Definition hit_algebra_biadjunction
           (Σ : hit_signature)
  := total_left_biadj_data
       _
       _
       (disp_fullsub_biadjunction
          (hit_path_algebra_biadjunction Σ)
          (is_hit_algebra_grpd Σ)
          (is_hit_algebra_one_types Σ)
          (gquot_is_hit_algebra Σ)
          (path_groupoid_is_hit_algebra Σ)).
