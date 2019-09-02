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
Require Export hit_biadjunction.hit_prealgebra_biadj_unit_counit.
Require Import hit_biadjunction.hit_prealgebra_biadj.left_triangle.
Require Import hit_biadjunction.hit_prealgebra_biadj.right_triangle.

Local Open Scope cat.

Definition prealg_disp_biadjunction
           (P : poly_code)
  : disp_left_biadj_data
      (disp_alg_bicat ⦃ P ⦄)
      (disp_alg_bicat (⟦ P ⟧))
      gquot_biadj_data
      (prealg_gquot P).
Proof.
  use tpair.
  - exact (algebra_disp_biadjunction_unit_counit P).
  - split.
    + exact (algebra_disp_biadjunction_left_triangle P).
    + exact (algebra_disp_biadjunction_right_triangle P).
Defined.

Definition total_prealg_gquot
           (P : poly_code)
  : psfunctor
      (total_bicat (disp_alg_bicat ⦃ P ⦄))
      (total_bicat (disp_alg_bicat (⟦ P ⟧)))
  := total_psfunctor
       (disp_alg_bicat ⦃ P ⦄)
       (disp_alg_bicat (⟦ P ⟧))
       gquot_psfunctor
       (prealg_gquot P).

Definition total_prealg_path_groupoid
           (P : poly_code)
  : psfunctor
      (total_bicat (disp_alg_bicat (⟦ P ⟧)))
      (total_bicat (disp_alg_bicat ⦃ P ⦄))
  := total_psfunctor
       (disp_alg_bicat (⟦ P ⟧))
       (disp_alg_bicat ⦃ P ⦄)
       path_groupoid
       (prealg_path_groupoid P).

Definition prealg_biadjunction
           (P : poly_code)
  : left_biadj_data (total_prealg_gquot P)
  := total_left_biadj_data _ _ (prealg_disp_biadjunction P).
