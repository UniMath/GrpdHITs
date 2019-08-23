(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Colimits.Initial.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.FullSub.
Require Import UniMath.Bicategories.DisplayedBicats.DispPseudofunctor.
Require Import UniMath.Bicategories.DisplayedBicats.DispTransformation.
Require Import UniMath.Bicategories.DisplayedBicats.DispModification.
Require Import UniMath.Bicategories.DisplayedBicats.DispBuilders.
Require Import UniMath.Bicategories.DisplayedBicats.DispBiadjunction.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import existence.initial_algebra.
Require Import existence.initial_groupoid_algebra.
Require Import hit_biadjunction.hit_algebra_biadj.

Local Open Scope cat.

Definition hit_existence
           (Σ : hit_signature)
  : ∑ (X : hit_algebra_one_types Σ), is_HIT Σ X.
Proof.
  eexists.
  apply initial_algebra_is_HIT.
  apply (biadj_preserves_unique_maps
           (hit_algebra_biadjunction Σ)
           (pr2 (is_univalent_2_hit_algebra_one_types Σ))
           (initial_groupoid_algebra Σ)
           (initial_groupoid_algebra_is_initial Σ)
        ).
Defined.

(** Note: this evaluates to
```
make_one_type
  (gquot (pr111 (initial_groupoid_algebra Σ)))
  (gtrunc (pr111 (initial_groupoid_algebra Σ)))
```
*)
Definition hit_carrier
           (Σ : hit_signature)
  : one_type
  := pr1 (pr111 (hit_existence Σ)).

Definition hit_path_space
           (Σ : hit_signature)
           (x y : pr111 (initial_groupoid_algebra Σ) : groupoid)
  : gcl _ x = gcl _ y ≃ x --> y.
Proof.
  use make_weq.
  - exact (encode_gquot (pr111 (initial_groupoid_algebra Σ)) (gcl _ x) (gcl _ y)).
  - apply encode_gquot_isweq.
Defined.
