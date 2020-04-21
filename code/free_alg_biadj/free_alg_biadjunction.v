Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Import DispBicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Identity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

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
