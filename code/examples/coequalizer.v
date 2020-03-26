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

Section HomotopyCoeq.
  Context (A B : one_type)
          (f g : A → B).
  
  Definition coeq_point_constr
    : poly_code
    := C B.

  Definition coeq_signature
    : hit_signature.
  Proof.
    simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
    - exact coeq_point_constr.
    - exact unit.
    - exact (λ _, C A).
    - exact (λ _, comp (fmap f) constr).
    - exact (λ _, comp (fmap g) constr).
    - exact empty.
    - exact fromempty.
    - exact fromempty.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
    - intro x ; induction x.
  Defined.

  (** Projections of coeq algebra *)
  Section CoeqProjections.
    Variable (X : hit_algebra_one_types coeq_signature).

    Definition coeq_base
      : B → alg_carrier X
      := alg_constr X.

    Definition coeq_loop
               (a : A)
      : coeq_base (f a) = coeq_base (g a)
      := alg_path X tt a.
  End CoeqProjections.

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
