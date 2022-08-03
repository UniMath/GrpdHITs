(**
Here we define the signature for the group quotient.
We also derive its usual elimination principle.

Given a group `G`, we define the group quotient as follows
HIT group_quot G :=
| base : group_quot G
| loop : ∏ (g : G), base = base
| loop_e : loop e = idpath base
| loop_m : ∏ (g₁ g₂ : G), loop (g₁ · g₂) = loop g₁ @ loop g₂
In addition, this type is 1-truncated.
 *)
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
Require Import displayed_algebras.globe_over_lem.
Require Import existence.hit_existence.

Local Open Scope cat.

Definition prod_one_type
           (A B : one_type)
  : one_type.
Proof.
  refine (make_one_type (A × B) _).
  apply isofhleveldirprod.
  - apply A.
  - apply B.
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
      apply ap_e.
      apply inv_e.
      apply comp_constant.
    - cbn.
      unfold group_quot_base_ep.
      refine (trans_e
                (comp_assoc _ _ _)
                _).
      apply ap_e.
      apply comp_constant.
  Defined.

  (*
  Local Notation "p ~ q" := (homot_endpoint _ _ _ _ p q).
   *)
  
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

    Definition group_quot_loop_unit
      : group_quot_loop (unel G) = idpath group_quot_base.
    Proof.
      exact (!(pathscomp0rid _) @ alg_homot X group_quot_ident tt (idpath tt)).
    Qed.

    Definition group_quot_loop_mult
               (g₁ g₂ : G)
      : group_quot_loop (op g₁ g₂)
        =
        group_quot_loop g₁ @ group_quot_loop g₂.
    Proof.
      refine (!(pathscomp0rid _) @ alg_homot X group_quot_comp (g₁ ,, g₂) (idpath tt) @ _).
      simpl.
      etrans.
      {
        apply maponpaths.
        apply pathscomp0rid.
      }
      apply maponpaths_2.
      apply pathscomp0rid.
    Qed.
    End AlgebraProjections.

  Section GroupQuotInduction.
    Context {X : hit_algebra_one_types group_quot_signature}
            (Y : alg_carrier X → one_type)
            (Ybase : Y (group_quot_base X))
            (Yloop : ∏ (g : G),
                     @PathOver _ _ _ (group_quot_loop X g) Y Ybase Ybase)
            (Yunit : globe_over
                       Y
                       (group_quot_loop_unit X)
                       (Yloop (unel G))
                       (identityPathOver Ybase))
            (Ycomp : ∏ (g₁ g₂ : G),
                     globe_over
                       Y
                       (group_quot_loop_mult X g₁ g₂)
                       (Yloop (op g₁ g₂))
                       (composePathOver (Yloop g₁) (Yloop g₂))).

    Local Definition make_group_quot_disp_algebra_op
      : ∏ (x : unit), unit → Y (alg_constr X x).
    Proof.
      intros x xx.
      induction x.
      exact Ybase.
    Defined.

    Local Definition make_group_quot_disp_algebra_path
      : ∏ (j : path_label group_quot_signature)
          (x : pr1 G),
        pr1 G
        →
        @PathOver _ _ _ (alg_path X j x) Y Ybase Ybase.
    Proof.
      intros j x y.
      induction j.
      exact (Yloop x).
    Defined.
    
    Local Definition make_group_quot_disp_algebra_unit
          (z : unit)
          (p : tt = tt)
      : globe_over
          Y
          (alg_homot X group_quot_ident z p)
          (composePathOver
             (composePathOver
                (identityPathOver _)
                (identityPathOver _))
             (composePathOver
                (Yloop 1%multmonoid)
                (composePathOver
                   (identityPathOver _)
                   (identityPathOver _)))) 
          (identityPathOver _).
    Proof.
      refine (globe_over_move_globe_one_type _ _).
      { apply (pr111 X). }
      exact
      (concat_globe_over
         (globe_over_compose_left'
            _
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_left _))
               (globe_over_id_right _)))
         (concat_globe_over
            (globe_over_compose_right
               _
               (globe_over_id_left _))
            (concat_globe_over
               (globe_over_id_left _)
               Yunit))).
    Qed.

    Definition make_group_quot_disp_algebra_comp
               (g₁ g₂ : G)
               (p : tt = tt)
      : globe_over
          Y
          (pr2 X group_quot_comp (g₁ ,, g₂) p)
          (composePathOver
             (composePathOver
                (identityPathOver _)
                (identityPathOver _))
             (composePathOver
                (Yloop (op g₁ g₂))
                (composePathOver
                   (identityPathOver _)
                   (identityPathOver _))))
          (composePathOver
             (composePathOver
                (composePathOver
                   (identityPathOver _)
                   (identityPathOver _))
                (composePathOver
                   (Yloop g₁)
                   (composePathOver
                      (identityPathOver _)
                      (identityPathOver _))))
             (composePathOver
                (composePathOver
                   (identityPathOver _)
                   (identityPathOver _))
                (composePathOver
                   (Yloop g₂)
                   (composePathOver
                      (identityPathOver _)
                      (identityPathOver _))))).
    Proof.
      refine (globe_over_move_globe_one_type _ _).
      { apply (pr111 X). }
      refine
      (concat_globe_over
         (globe_over_compose_left'
            _
            (concat_globe_over
               (globe_over_compose_left'
                  _
                  (globe_over_id_right _))
               (globe_over_id_right _)))
         (concat_globe_over
            (globe_over_compose_right
               _
               (globe_over_id_right _))
            (concat_globe_over
               (globe_over_id_left _)
               (concat_globe_over
                  (Ycomp g₁ g₂)
                  (inv_globe_over
                     (concat_globe_over
                        (globe_over_compose_left'
                           _
                           (concat_globe_over
                              (globe_over_compose_left'
                                 _
                                 (concat_globe_over
                                    (globe_over_compose_left'
                                       _
                                       (globe_over_id_right _))
                                    (globe_over_id_right _)))
                              (concat_globe_over
                                 (globe_over_compose_right
                                    _
                                    (globe_over_id_right _))
                                 (globe_over_id_left _))))
                        (globe_over_compose_right
                           _
                           (concat_globe_over
                              (globe_over_compose_left'
                                 _
                                 (concat_globe_over
                                    (globe_over_compose_left'
                                       _
                                       (globe_over_id_right _))
                                    (globe_over_id_right _)))
                              (concat_globe_over
                                 (globe_over_compose_right
                                    _
                                    (globe_over_id_right _))
                                 (globe_over_id_left _)))))))))).
    Qed.

    Definition make_group_quot_disp_algebra
      : disp_algebra X.
    Proof.
      use make_disp_algebra.
      - exact Y.
      - exact make_group_quot_disp_algebra_op.
      - exact make_group_quot_disp_algebra_path.
      - intros j z zz p_arg pp_arg.
        induction j.
        + apply make_group_quot_disp_algebra_unit.
        + apply make_group_quot_disp_algebra_comp.
    Defined.
    
    Variable (HX : is_HIT group_quot_signature X).

    (** Induction principle *)
    Definition group_quot_ind_disp_algebra_map
      : disp_algebra_map make_group_quot_disp_algebra
      := HX make_group_quot_disp_algebra.

    Definition group_quot_ind
      : ∏ (x : alg_carrier X), Y x
      := pr1 group_quot_ind_disp_algebra_map.

    Definition group_quot_ind_base
      : group_quot_ind (group_quot_base X) = Ybase
      := pr12 group_quot_ind_disp_algebra_map tt.

    Definition group_quot_ind_loop
               (g : G)
      : PathOver_square
          _
          (idpath _)
          (apd
             (pr1 group_quot_ind_disp_algebra_map)
             (group_quot_loop X g))
          (Yloop g)
          group_quot_ind_base
          group_quot_ind_base.
    Proof.
      pose (pr22 group_quot_ind_disp_algebra_map tt g).
      simpl in p.
      rewrite pathscomp0rid in p.
      exact p.
    Qed.
  End GroupQuotInduction.
End GroupQuotient.

Definition group_quot (G : gr)
  := pr1 (hit_existence (group_quot_signature G)).
