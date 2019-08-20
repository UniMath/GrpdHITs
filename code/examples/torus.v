(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import signature.hit_signature.

Definition unit_one_type
  : one_type
  := make_one_type unit (hlevelntosn _ _ (hlevelntosn _ _ isapropunit)).

Definition torus_point_constr
  : poly_code
  := C unit_one_type.

Inductive torus_paths : Type :=
| p_left : torus_paths
| p_right : torus_paths.

Inductive torus_homots : Type :=
| com : torus_homots.

Definition torus_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact torus_point_constr.
  - exact torus_paths.
  - exact (λ _, C unit_one_type).
  - exact (λ _, constr).
  - exact (λ _, constr).
  - exact torus_homots.
  - exact (λ _, C unit_one_type).
  - exact (λ _, C unit_one_type).
  - refine (λ _, c _ _).
    exact tt.
  - refine (λ _, c _ _).
    exact tt.
  - exact (λ _, comp (id_e torus_point_constr (C unit_one_type)) constr).
  - exact (λ _, comp (id_e torus_point_constr (C unit_one_type)) constr).
  - refine (λ _, _).
    exact (trans_e
             _ _ _ _ _ _ _ _ _ _ _ _ _
             (path_constr
                _ _ _ _ _ _ _ _ _
                p_left
                _
             )
             (path_constr
                _ _
                (λ _, C unit_one_type)
                (λ _, constr)
                _ _ _ _ _
                p_right
                _
          )).
  - refine (λ _, _).
    exact (trans_e
             _ _ _ _ _ _ _ _ _ _ _ _ _
             (path_constr
                _ _ _ _ _ _ _ _ _
                p_right
                _
             )
             (path_constr
                _ _
                (λ _, C unit_one_type)
                (λ _, constr)
                _ _ _ _ _
                p_left
                _
          )).
Defined.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import algebra.one_types_homotopies.

Local Open Scope cat.

Section TorusAlgebraProjections.
  Variable (X : hit_algebra_one_types torus_signature).

  Definition torus_carrier
    : one_type
    := pr111 X.

  Definition torus_base
    : torus_carrier
    := pr211 X tt.

  Definition torus_path_left
    : torus_base = torus_base
    := pr21 X p_left tt.

  Definition torus_path_right
    : torus_base = torus_base
    := pr21 X p_right tt.

  Definition torus_surface
    : torus_path_left @ torus_path_right
      =
      torus_path_right @ torus_path_left
    := pr2 X com tt (idpath tt).
End TorusAlgebraProjections.
