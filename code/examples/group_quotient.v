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

Definition TODO {A : UU} : A.
Admitted.

Definition prod_one_type
           (A B : one_type)
  : one_type.
Proof.
  refine (make_one_type (A × B) _).
  apply isofhleveldirprod.
  - apply A.
  - apply B.
Defined.

Definition comp_constant
           {A P Q : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {TR : poly_code}
           {al ar : endpoint A P TR}
           {X : one_type}
           (e : endpoint A P Q)
           (x : X)
  : homot_endpoint
      l
      r
      al
      ar
      (comp e (c Q x))
      (c P x).
Proof.
  apply TODO.
Defined.

Section GroupQuotient.
  Variable (G : gr).

  Definition carrier_G : one_type.
  Proof.
    refine (make_one_type G _).
    apply hlevelntosn ; apply (pr11 G).
  Defined.

  Definition mult_G : prod_one_type carrier_G carrier_G → carrier_G.
  Proof.
    cbn ; intros x.
    exact (@op G (pr1 x) (pr2 x)).
  Defined.

  Definition group_quot_point_constr
    : poly_code
    := C unit_one_type.

  Inductive group_quot_homots : UU :=
  | group_quot_ident : group_quot_homots
  | group_quot_comp : group_quot_homots.

  Definition group_quot_path_label
    : UU
    := unit.

  Definition group_quot_path_arg
    : group_quot_path_label → poly_code
    := λ _, C carrier_G.

  Definition group_quot_base_ep
             (P : poly_code)
    : endpoint group_quot_point_constr P I
    := comp (c P (tt : unit_one_type)) constr.

  Definition group_quot_homot_point_arg
    : group_quot_homots → poly_code.
  Proof.
    intro j ; induction j.
    - exact (C unit_one_type).
    - exact (C (prod_one_type carrier_G carrier_G)).
  Defined.

  Definition group_quot_homot_path_arg_poly
    : group_quot_homots → poly_code
    := λ _, C unit_one_type.
 
  Definition group_quot_homot_path_arg_lr
             (j : group_quot_homots)
    : endpoint
        group_quot_point_constr
        (group_quot_homot_point_arg j)
        (group_quot_homot_path_arg_poly j).
  Proof.
    exact (@c _ _ unit_one_type tt).
  Defined.

  Definition group_quot_homot_lr_endpoint
             (j : group_quot_homots)
    : endpoint group_quot_point_constr (group_quot_homot_point_arg j) I.
  Proof.
    induction j.
    - exact (group_quot_base_ep _).
    - exact (group_quot_base_ep _).
  Defined.

  Definition group_quot_loop_hp
             {P Q : poly_code}
             {al ar : endpoint group_quot_point_constr P Q}
             (g : endpoint group_quot_point_constr P (C carrier_G))
    : homot_endpoint
        (λ j0, group_quot_base_ep (group_quot_path_arg j0))
        (λ j0, group_quot_base_ep (group_quot_path_arg j0))
        al ar
        (group_quot_base_ep P) (group_quot_base_ep P).
  Proof.
    simple refine
           (trans_e
              _
              (trans_e
                 (path_constr tt g)
                 _)).
    - cbn.
      unfold group_quot_base_ep.
      refine (trans_e
                _
                (inv_e (comp_assoc _ _ _))).
      apply ap_constr.
      apply inv_e.
      apply comp_constant.
    - cbn.
      unfold group_quot_base_ep.
      refine (trans_e
                (comp_assoc _ _ _)
                _).
      apply ap_constr.
      apply comp_constant.
  Defined.

  Local Notation "p ~ q" := (homot_endpoint _ _ _ _ p q).

  Definition group_quot_homot_left
             (j : group_quot_homots)
    : homot_endpoint
        (λ j0, group_quot_base_ep (group_quot_path_arg j0))
        (λ j0, group_quot_base_ep (group_quot_path_arg j0))
        (group_quot_homot_path_arg_lr j) (group_quot_homot_path_arg_lr j)
        (group_quot_homot_lr_endpoint j) (group_quot_homot_lr_endpoint j).
  Proof.
    induction j.
    - (* unit *)
      apply group_quot_loop_hp.
      apply c.
      exact (unel G).
    - (* multiplication *)
      apply group_quot_loop_hp.
      exact (fmap mult_G).
  Defined.

  Definition group_quot_homot_right
             (j : group_quot_homots)
    : homot_endpoint
        (λ j0, group_quot_base_ep (group_quot_path_arg j0))
        (λ j0, group_quot_base_ep (group_quot_path_arg j0))
        (group_quot_homot_path_arg_lr j) (group_quot_homot_path_arg_lr j)
        (group_quot_homot_lr_endpoint j) (group_quot_homot_lr_endpoint j).
  Proof.
    induction j.
    - (* unit *)
      apply refl_e.
    - (* multiplication *)
      refine (trans_e (group_quot_loop_hp (fmap _)) (group_quot_loop_hp (fmap _))).
      + exact pr1.
      + exact pr2.
  Defined.
  
  Definition group_quot_signature
    : hit_signature.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
    - exact group_quot_point_constr.
    - exact group_quot_path_label.
    - exact group_quot_path_arg.
    - exact (λ _, group_quot_base_ep _).
    - exact (λ _, group_quot_base_ep _).
    - exact group_quot_homots.
    - exact group_quot_homot_point_arg.
    - exact group_quot_homot_path_arg_poly.
    - exact group_quot_homot_path_arg_lr.
    - exact group_quot_homot_path_arg_lr.
    - exact group_quot_homot_lr_endpoint.
    - exact group_quot_homot_lr_endpoint.
    - exact group_quot_homot_left.
    - exact group_quot_homot_right.
  Defined.

  (** Projections of circle algebra *)
  Section AlgebraProjections.
    Variable (X : hit_algebra_one_types group_quot_signature).
    
    Definition group_quot_base
      : alg_carrier X
      := alg_constr X tt.

    Definition group_quot_loop
               (g : G)
      : group_quot_base = group_quot_base
      := alg_path X tt g.
    End AlgebraProjections.
  (*
  Section GroupQuotInduction.
    Context {X : hit_algebra_one_types group_quot_signature}
            (Y : alg_carrier X → one_type)
            (Ybase : Y (group_quot_base X))
            (* (Yloop : @PathOver _ _ _ Y Ybase Ybase (circle_loop X)) *).

    (*
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
     *)
    
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
        _
        _
        (apd (pr1 circle_ind_disp_algebra_map) (circle_loop X))
        Yloop
        circle_ind_base
        circle_ind_base
        := pr22 circle_ind_disp_algebra_map loop tt.
    End CircleInduction.
   *)
End GroupQuotient.

(*
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
*)
