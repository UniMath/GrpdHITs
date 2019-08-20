(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.

Definition unit_one_type
  : one_type
  := make_one_type unit (hlevelntosn _ _ (hlevelntosn _ _ isapropunit)).

Definition mod2_point_constr
  : poly_code
  := C unit_one_type + I.

Inductive mod2_paths : Type :=
| mod : mod2_paths.

Inductive mod2_homots : Type :=
| is_trunc : mod2_homots.

Definition mod2_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact mod2_point_constr.
  - exact mod2_paths.
  - exact (λ _, I).
  - exact (λ _, comp ((comp (ι₂ _ _) constr))
                     (comp (ι₂ _ _) constr)).
  - exact (λ _, id_e _ _).
  - exact mod2_homots.
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

Section Mod2AlgebraProjections.
  Variable (X : hit_algebra_one_types mod2_signature).

  Definition mod2_carrier
    : one_type
    := pr111 X.

  Definition mod2_Z
    : mod2_carrier
    := pr211 X (inl tt).

  Definition mod2_S
    : mod2_carrier → mod2_carrier
    := λ x, pr211 X (inr x).

  Definition mod2_mod
    : ∏ (x : mod2_carrier), mod2_S (mod2_S x) = x
    := pr21 X mod.

  Definition mod2_set_trunc
    : ∏ (a b : mod2_carrier) (p q : a = b), p = q
    := λ a b p q,
       !(maponpaths_pr1_pathsdirprod p q)
        @ pr2 X is_trunc (a ,, b) (pathsdirprod p q)
        @ maponpaths_pr2_pathsdirprod p q.
End Mod2AlgebraProjections.
