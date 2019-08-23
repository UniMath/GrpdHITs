(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.

Local Definition TODO {A : Type} : A.
Admitted.

Definition initial_groupoid_algebra
           (Σ : hit_signature)
  : hit_algebra_grpd Σ.
Proof.
  apply TODO.
Defined.

Definition initial_groupoid_algebra_is_initial
           (Σ : hit_signature)
  : unique_maps (initial_groupoid_algebra Σ).
Proof.
  apply TODO.
Defined.
