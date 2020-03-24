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

Section GroupQuotient.
  Variable (G : gr).

  Definition group_quot_point_constr
    := C unit_one_type.

  Inductive group_quot_homots : UU :=
  | group_quot_ident : group_quot_homots
  | group_quot_comp : group_quot_homots.

  Definition TODO {A : UU} : A.
  Admitted.

  Definition group_quot_signature
    : hit_signature.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
    - exact group_quot_point_constr.
    - exact unit.
    - refine (λ _, C (make_one_type G _)).
      apply hlevelntosn ; apply (pr11 G).
    - intro ; simpl.
      refine (comp (c _ _) constr).
      exact tt.
    - intro ; simpl.
      refine (comp (c _ _) constr).
      exact tt.
    - exact group_quot_homots.
    - intro x ; induction x.
      + exact (C unit_one_type).
      + refine (C (make_one_type G _) * C (make_one_type G _))
        ; apply hlevelntosn ; apply (pr11 G).
    - exact (λ _, C unit_one_type).
    - exact (λ _, @c _ _ unit_one_type tt).
    - exact (λ _, @c _ _ unit_one_type tt).
    - intro x ; induction x.
      + refine (comp (c _ _) constr).
        exact tt.
      + refine (comp (c _ _) constr).
        exact tt.
    - intro x ; induction x.
      + refine (comp (c _ _) constr).
        exact tt.
      + refine (comp (c _ _) constr).
        exact tt.
    - intro x ; induction x.
      + simpl.
        simple refine
               (trans_e
                  (trans_e
                     _
                     (path_constr tt (c _ _)))
                  _).
        * simpl.
          refine (trans_e
                    _
                    (inv_e (comp_assoc _ _ _))).
          apply ap_constr.
          apply inv_e.
          Print homot_endpoint.
          Check comp.

                  Check refl_e.

        homot_endpoint
          (λ _ : unit,
                 comp
                   (c
                      (C
                         (make_one_type (pr1 G)
                                        (λ (t1 t2 : pr1 G) (t0 t3 : t1 = t2), isapropifcontr ((pr211 G) t1 t2 t0 t3))))
                      tt)
                   constr)
          (λ _ : unit,
                 comp
                   (c
                      (C
                         (make_one_type
                            (pr1 G)
                            (λ (t1 t2 : pr1 G) (t0 t3 : t1 = t2), isapropifcontr ((pr211 G) t1 t2 t0 t3))))
                      tt) constr)
          (c (C unit_one_type) tt)
          (c (C unit_one_type) tt)
          constr
          (comp
             (c (C unit_one_type) ?Goal0)
             (comp
                (c
                   (C
                      (make_one_type
                         (pr1 G)
                         (λ (t1 t2 : pr1 G) (t0 t3 : t1 = t2), isapropifcontr ((pr211 G) t1 t2 t0 t3))))
                   tt) constr))

          apply TODO.
        * exact (unel G).
        exact (trans_e
                 (trans_e
                    (inv_e (comp_id_l _))
                    (path_constr (unel G) (id_e _ _)))
                 (comp_id_l _)).
      + simpl.
        Check (path_constr).
        Check (trans_e
                 (path_constr (π₁ _ _) (id_e _ _))
                 (path_constr (π₂ _ _) (id_e _ _))).
               _).
        apply TODO.
    - intro x ; induction x.
      + apply refl_e.
      + apply TODO.
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
      := alg_path X g tt.
    End AlgebraProjections.

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
