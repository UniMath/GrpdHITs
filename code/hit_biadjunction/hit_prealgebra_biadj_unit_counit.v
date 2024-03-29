Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Morphisms.Adjunctions.
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
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.gquot_commute.
Require Import algebra.one_types_polynomials.
Require Import algebra.groupoid_polynomials.
Require Import biadjunctions.all.
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_path_groupoid.
Require Export hit_biadjunction.hit_prealgebra_biadj.lift_gquot.
Require Export hit_biadjunction.hit_prealgebra_biadj.unit.
Require Export hit_biadjunction.hit_prealgebra_biadj.counit.

Local Open Scope cat.

Definition algebra_disp_biadjunction_unit_counit
           (P : poly_code)
  : disp_left_biadj_unit_counit
      (disp_alg_bicat ⦃ P ⦄)
      (disp_alg_bicat (⟦ P ⟧))
      gquot_biadj_data
      (prealg_gquot P).
Proof.
  use tpair.
  - exact (prealg_path_groupoid P).
  - split.
    + exact (prealg_unit P).
    + exact (prealg_counit P).
Defined.

(** Useful lemmata *)
Definition maponpaths_sum_gquot_inl
           {P₁ P₂ : poly_code}
           {G : groupoid}
           {a b : poly_act P₁ (gquot G)}
           (p : a = b)
  : maponpaths
      ((sum_gquot (poly_gquot P₁) (poly_gquot P₂)) G)
      (maponpaths inl p)
    =
    maponpaths
      gquot_inl_grpd
      (maponpaths
         (poly_gquot P₁ G)
         p).
Proof.
  induction p.
  apply idpath.
Qed.

Definition maponpaths_sum_gquot_inr
           {P₁ P₂ : poly_code}
           {G : groupoid}
           {a b : poly_act P₂ (gquot G)}
           (p : a = b)
  : maponpaths
      ((sum_gquot (poly_gquot P₁) (poly_gquot P₂)) G)
      (maponpaths inr p)
    =
    maponpaths
      gquot_inr_grpd
      (maponpaths
         (poly_gquot P₂ G)
         p).
Proof.
  induction p.
  apply idpath.
Qed.
