(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.
(*
Definition unit_one_type
  : one_type
  := make_one_type unit (hlevelntosn _ _ (hlevelntosn _ _ isapropunit)).
*)
Definition set_trunc_point_constr
           (A : one_type)
  : poly_code
  := C A.

Inductive set_trunc_paths : Type := .

Inductive set_trunc_homots : Type :=
| is_trunc : set_trunc_homots.

Definition set_trunc_signature
           (A : one_type)
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact (set_trunc_point_constr A).
  - exact set_trunc_paths.
  - intro x ; induction x.
  - intro x ; induction x.
  - intro x ; induction x.
  - exact set_trunc_homots.
  - exact (λ _, I * I).
  - exact (λ _, I * I).
  - exact (λ _, pair (π₁ _ _) (π₁ _ _)).
  - exact (λ _, pair (π₂ _ _) (π₂ _ _)).
  - exact (λ _, π₁ _ _).
  - exact (λ _, π₂ _ _).
  - refine (λ _, _).
    exact (path_pr1
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (path_arg _ _ _ _ _ _ _ _ _)).
  - refine (λ _, _).
    exact (path_pr2
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             (path_arg _ _ _ _ _ _ _ _ _)).
Defined.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import algebra.one_types_homotopies.
Require Import prelude.all.

Local Open Scope cat.

Section SetTruncAlgebraProjections.
  Variable (A : one_type)
           (X : hit_algebra_one_types (set_trunc_signature A)).

  Definition set_trunc_carrier
    : one_type
    := pr111 X.

  Definition set_trunc_base
    : A → set_trunc_carrier
    := pr211 X.

  Definition set_trunc_surface
    : ∏ (a b : set_trunc_carrier) (p q : a = b), p = q
    := λ a b p q,
       !(maponpaths_pr1_pathsdirprod p q)
        @ pr2 X is_trunc (a ,, b) (pathsdirprod p q)
        @ maponpaths_pr2_pathsdirprod p q.
End SetTruncAlgebraProjections.
