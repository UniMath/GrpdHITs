(** Here we define the signature for the circle *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.
Require Import initial_grpd_alg.W_poly.
Require Import initial_grpd_alg.initial_groupoid_algebra.
Require Import existence.hit_existence.

Local Open Scope cat.

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

(** Projections of circle algebra *)
Definition circle_base
           (X : hit_algebra_one_types circle_signature)
  : alg_carrier X
  := alg_constr X tt.

Definition circle_loop
           (X : hit_algebra_one_types circle_signature)
  : circle_base X = circle_base X
  := alg_path X loop tt.

Section CircleInduction.
  Context {X : hit_algebra_one_types circle_signature}
          (Y : alg_carrier X → one_type)
          (Ybase : Y (circle_base X))
          (Yloop : @PathOver _ _ _ Y Ybase Ybase (circle_loop X)).
  
  Definition make_circle_disp_algebra
    : disp_algebra X.
  Proof.
    use make_disp_algebra.
    - exact Y.
    - intros x xx.
      induction x.
      exact Ybase.
    - intros j x y.
      induction j.
      induction x.
      exact Yloop.
    - intro j.
      induction j.
  Defined.

  Variable (HX : is_HIT circle_signature X).

  (** Induction principle *)
  Definition circle_ind_disp_algebra_map
    : disp_algebra_map make_circle_disp_algebra
    := HX make_circle_disp_algebra.

  Definition circle_ind
    : ∏ (x : alg_carrier X), Y x
    := pr1 circle_ind_disp_algebra_map.

  Definition circle_ind_base
    : circle_ind (circle_base X) = Ybase
    := pr12 circle_ind_disp_algebra_map tt.

  Definition circle_ind_loop
    : PathOver_square
        (apd (pr1 circle_ind_disp_algebra_map) (circle_loop X))
        Yloop
        circle_ind_base
        circle_ind_base
    := pr22 circle_ind_disp_algebra_map loop tt.
End CircleInduction.

Definition circle
  := pr1 (hit_existence circle_signature).

Definition circle_path_space_base
  : UU
  := ((pr111 (initial_groupoid_algebra circle_signature) : groupoid)
        ⟦ poly_initial_alg circle_point_constr tt
        , poly_initial_alg circle_point_constr tt ⟧).

Definition circle_is_path_space
  : circle_base circle = circle_base circle
    ≃
    circle_path_space_base
  := hit_path_space
       circle_signature
       (poly_initial_alg circle_point_constr tt)
       (poly_initial_alg circle_point_constr tt).

(*
Definition TODO {A : UU} : A.
Admitted.

Definition circle_path_space_ab_gp
  : abgr.
Proof.
  use make_abgr.
  - use make_setwithbinop.
    + use make_hSet.
      * exact circle_path_space_base.
      * apply isasetsetquot.
    + exact (λ x y, initial_groupoid_algebra_carrier_comp _ x y).
  - use make_isabgrop.
    + use make_isgrop.
      * use make_ismonoidop.
        ** intros ? ? ?.
           refine (!_).
           apply initial_groupoid_algebra_carrier_assoc.
        ** simple refine (_ ,, (_ ,, _)).
           *** apply initial_groupoid_algebra_carrier_id.
           *** intro x.
               apply initial_groupoid_algebra_carrier_right_unit.
           *** intro x.
               apply initial_groupoid_algebra_carrier_left_unit.
      * simple refine (_ ,, (_ ,, _)).
        ** apply initial_groupoid_algebra_carrier_inv.
        ** intro.
           apply initial_groupoid_algebra_carrier_left_inv.
        ** intro.
           apply initial_groupoid_algebra_carrier_right_inv.
    + use (setquotunivprop _ (λ _, make_hProp _ _)).
      { apply TODO. }
      intro x.
      use (setquotunivprop _ (λ _, make_hProp _ _)).
      { apply TODO. }
      intro y.
      apply iscompsetquotpr.
      apply hinhpr.
      cbn.
      unfold initial_alg_comp.
      cbn.
      apply TODO.
Defined.

Definition test
           (G : abgr)
  : circle_path_space_ab_gp
    →
    G.
Proof.
  use setquotuniv.
  - intro z.
    induction z ; simpl in *.
    + apply TODO.
    + apply TODO.
    + apply TODO.
    + apply TODO.
    + apply TODO.
    + apply TODO.
    + apply TODO.
    + apply TODO.
  - apply TODO.
Defined.

Definition test'
           (G : abgr)
           (f g : circle_path_space_ab_gp → G)
  : f ~ g.
Proof.
  use (setquotunivprop _ (λ _, make_hProp _ _)).
  - apply TODO.
  - intro z.
    simpl.
    simpl in z.
    induction z.
 *)
