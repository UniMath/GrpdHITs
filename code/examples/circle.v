(**
Here we define the signature for the circle

The circle is the following HIT:
HIT circle :=
| base : circle
| loop : base = base
We look at the 1-truncation.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.NumberSystems.Integers.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Core.Isos.
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

Inductive circle_paths : UU :=
| loop : circle_paths.

Definition circle_signature
  : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact circle_point_constr.
  - exact circle_paths.
  - exact (λ _, C unit_one_type).
  - exact (λ _, constr).
  - exact (λ _, constr).
  - exact empty.
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


(*
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


(**
Initial groupoid algebra for the circle constructed in a special way.
We will use this conclude that the fundamental group of the circle is the integers
 *)
Definition TODO {A : UU} : A.
Admitted.

Definition circle_initial_algebra_precategory_data
  : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact unit. 
    + exact (λ _ _, hz).
  - exact (λ _, hzzero). 
  - exact (λ _ _ _, hzplus).
Defined.

Definition circle_initial_algebra_is_precategory
  : is_precategory circle_initial_algebra_precategory_data.
Proof.
  use make_is_precategory.
  - exact (λ _ _, hzplusl0).
  - exact (λ _ _, hzplusr0).
  - exact (λ _ _ _ _ x y z, ! hzplusassoc x y z).
  - exact (λ _ _ _ _, hzplusassoc).
Qed.

Definition circle_initial_algebra_precategory
  : precategory.
Proof.
  use make_precategory.
  - exact circle_initial_algebra_precategory_data.
  - exact circle_initial_algebra_is_precategory.
Defined.

Definition circle_initial_algebra_homsets
  : has_homsets circle_initial_algebra_precategory.
Proof.
  intros x y.
  apply isasetsetquot.
Qed.

Definition circle_initial_algebra_category
  : category.
Proof.
  use make_category.
  - exact circle_initial_algebra_precategory.
  - exact circle_initial_algebra_homsets.
Defined.

Definition circle_initial_algebra_is_pregroupoid
  : is_pregroupoid circle_initial_algebra_category.
Proof.
  intros tt1 tt2 z.
  use is_iso_qinv.
  - exact (hzsign z).
  - split.
    + exact (hzrminus z).
    + exact (hzlminus z).
Defined.

Definition circle_initial_algebra
  : groupoid.
Proof.
  use make_groupoid.
  - exact circle_initial_algebra_category.
  - exact circle_initial_algebra_is_pregroupoid.
Defined.
