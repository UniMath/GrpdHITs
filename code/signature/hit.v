(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.

Local Definition TODO {A : Type} : A.
Admitted.

Definition is_HIT
           (Σ : hit_signature)
           (X : hit_algebra_one_types Σ)
  : UU.
Proof.
  apply TODO.
Defined.

Definition is_initial
           (Σ : hit_signature)
           (X : hit_algebra_one_types Σ)
  : UU
  := is_biinitial (pr2 (is_univalent_2_hit_algebra_one_types Σ)) X.
