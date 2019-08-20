(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.

Definition unit_one_type
  : one_type
  := make_one_type unit (hlevelntosn _ _ (hlevelntosn _ _ isapropunit)).

Definition circle_point_constr
  : poly_code
  := C unit_one_type.

Inductive circle_paths : Type :=
| loop : circle_paths.

Inductive circle_homots : Type := .

Definition circle_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact circle_point_constr.
  - exact circle_paths.
  - exact (λ _, C unit_one_type).
  - exact (λ _, constr).
  - exact (λ _, constr).
  - exact circle_homots.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
Defined.
