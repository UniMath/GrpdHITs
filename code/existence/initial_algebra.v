(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.

Local Definition TODO {A : Type} : A.
Admitted.

Definition initial_algebra_is_HIT
           (Σ : hit_signature)
           (X : hit_algebra_one_types Σ)
  : is_initial Σ X → is_HIT Σ X.
Proof.
  apply TODO.
Defined.
