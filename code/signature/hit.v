(** Here we define the notion of a HIT *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Univalence.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import displayed_algebras.displayed_algebra.

Definition is_HIT
           (Σ : hit_signature)
           (X : hit_algebra_one_types Σ)
  : UU
  := ∏ (Y : disp_algebra X), disp_algebra_map Y.

Section SetInduction.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}
          (HX : is_HIT Σ X)
          (Y : alg_carrier X → UU)
          (Yisaset : ∏ (x : alg_carrier X), isaset (Y x))
          (c : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
               poly_dact_UU (point_constr Σ) Y x
               →
               Y (alg_constr X x))
          (p : ∏ (j : path_label Σ)
                 (x : poly_act (path_source Σ j) (alg_carrier X))
                 (y : poly_dact_UU (path_source Σ j) Y x),
               @PathOver
                 _ _ _
                 (alg_path X j x)
                 Y
                 (endpoint_dact_UU _ Y (path_left Σ j) c y)
                 (endpoint_dact_UU _ Y (path_right Σ j) c y)).

  Definition set_disp_algebra
    : disp_algebra X.
  Proof.
    use make_disp_algebra.
    - intro x.
      refine (make_one_type (Y x) _).
      apply hlevelntosn.
      apply Yisaset.
    - exact c.
    - exact p.
    - intros j z zz p_arg pp_arg.
      apply path_globe_over_hset.
      exact Yisaset.
  Defined.
      
  Definition hit_ind_set
    := HX set_disp_algebra.
End SetInduction.

Section PropInduction.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}
          (HX : is_HIT Σ X)
          (Y : alg_carrier X → UU)
          (Yisaprop : ∏ (x : alg_carrier X), isaprop (Y x))
          (c : ∏ (x : poly_act (point_constr Σ) (alg_carrier X)),
               poly_dact_UU (point_constr Σ) Y x
               →
               Y (alg_constr X x)).

  Definition prop_disp_algebra
    : disp_algebra X.
  Proof.
    use make_disp_algebra.
    - intro x.
      refine (make_one_type (Y x) _).
      do 2 apply hlevelntosn.
      apply Yisaprop.
    - exact c.
    - intros j x y.
      apply path_to_PathOver.
      apply Yisaprop.
    - intros j z zz p_arg pp_arg.
      apply path_globe_over_hset.
      intro.
      apply isasetaprop.
      apply Yisaprop.
  Defined.
      
  Definition hit_ind_prop
    := HX prop_disp_algebra.
End PropInduction.

Definition is_initial
           (Σ : hit_signature)
           (X : hit_algebra_one_types Σ)
  : UU
  := is_biinitial X.
