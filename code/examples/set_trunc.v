(** Here we define the signature for the set truncation *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.

Local Open Scope cat.

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
    exact (path_pr1 path_arg).
  - refine (λ _, _).
    exact (path_pr2 path_arg).
Defined.

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

Section SetTruncInduction.
  Context (A : one_type)
          (X : hit_algebra_one_types (set_trunc_signature A))
          (Y : alg_carrier X → one_type)
          (Ybase : ∏ (a : A), Y (set_trunc_base A X a))
          (Yisaset : ∏ (x : alg_carrier X), isaset (Y x)).
  
  Definition make_set_trunc_disp_algebra
    : disp_algebra X.
  Proof.
    use make_disp_algebra.
    - exact Y.
    - intros x xx.
      exact (Ybase x).
    - intros j x y.
      induction j.
    - intro j.
      induction j.
      intros z zz p pp.
      apply path_globe_over_hset.
      exact Yisaset.
  Defined.

  Variable (HX : is_HIT _ X).

  (** Induction principle *)
  Definition set_trunc_ind_disp_algebra_map
    : disp_algebra_map make_set_trunc_disp_algebra
    := HX make_set_trunc_disp_algebra.

  Definition set_trunc_ind
    : ∏ (x : alg_carrier X), Y x
    := pr1 set_trunc_ind_disp_algebra_map.

  Definition set_trunc_ind_base
             (a : A)
    : set_trunc_ind (set_trunc_base A X a) = Ybase a
    := pr12 set_trunc_ind_disp_algebra_map a.
End SetTruncInduction.
