(** Here we define the signature for the torus *)
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

Definition torus_point_constr
  : poly_code
  := C unit_one_type.

Inductive torus_paths : UU :=
| p_left : torus_paths
| p_right : torus_paths.

Inductive torus_homots : UU :=
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
             (path_constr
                p_left
                _
             )
             (@path_constr
                _ _
                (λ _, C unit_one_type)
                (λ _, constr)
                _ _ _ _ _
                p_right
                _
          )).
  - refine (λ _, _).
    exact (trans_e
             (path_constr
                p_right
                _
             )
             (@path_constr
                _ _
                (λ _, C unit_one_type)
                (λ _, constr)
                _ _ _ _ _
                p_left
                _
          )).
Defined.

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

Section TorusInduction.
  Context {X : hit_algebra_one_types torus_signature}
          (Y : alg_carrier X → one_type)
          (Ybase : Y (torus_base X))
          (Yleft : @PathOver _ _ _ Y Ybase Ybase (torus_path_left X))
          (Yright : @PathOver _ _ _ Y Ybase Ybase (torus_path_right X))
          (Ysurface : globe_over
                        Y
                        (torus_surface X)
                        (composePathOver Yleft Yright)
                        (composePathOver Yright Yleft)).

  Definition make_torus_disp_algebra
    : disp_algebra X.
  Proof.
    use make_disp_algebra.
    - exact Y.
    - intros x xx.
      induction x.
      exact Ybase.
    - intros j x y.
      induction j.
      + induction x.
        exact Yleft.
      + induction x.
        exact Yright.
    - abstract
        (intros j z zz p pp ;
         induction j ; induction z ; induction zz ;
         assert (p = idpath tt) as PS ; try apply isapropunit ;
         unfold torus_surface in Ysurface ;
         rewrite <- PS in Ysurface ;
         exact Ysurface).
  Defined.

  Variable (HX : is_HIT torus_signature X).

  (** Induction principle *)
  Definition torus_ind_disp_algebra_map
    : disp_algebra_map make_torus_disp_algebra
    := HX make_torus_disp_algebra.

  Definition torus_ind
    : ∏ (x : alg_carrier X), Y x
    := pr1 torus_ind_disp_algebra_map.

  Definition torus_ind_base
    : torus_ind (torus_base X) = Ybase
    := pr12 torus_ind_disp_algebra_map tt.

  Definition torus_ind_path_left
    : PathOver_square
        _ _
        (apd (pr1 torus_ind_disp_algebra_map) (torus_path_left X))
        Yleft
        torus_ind_base
        torus_ind_base
    := pr22 torus_ind_disp_algebra_map p_left tt.

  Definition torus_ind_path_right
    : PathOver_square
        _ _
        (apd (pr1 torus_ind_disp_algebra_map) (torus_path_right X))
        Yright
        torus_ind_base
        torus_ind_base
    := pr22 torus_ind_disp_algebra_map p_right tt.
End TorusInduction.
