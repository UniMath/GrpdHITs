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

  (** Builder for coequalizer algebra *)
  Section CoeqAlgebraBuilder.
    Context {X : one_type}
            (base : B → X)
            (loop : ∏ (a : A), base (f a) = base (g a)).

    Local Definition make_coeq_path_algebra
      : hit_path_algebra_one_types coeq_signature.
    Proof.
      use make_hit_path_algebra.
      - use make_hit_prealgebra.
        + exact X.
        + apply one_type_isofhlevel.
        + exact base.
      - intro j.
        exact loop.
    Defined.

    Local Definition make_coeq_is_algebra
      : is_hit_algebra_one_types coeq_signature make_coeq_path_algebra.
    Proof.
      intros j; induction j.
    Qed.
    
    Definition make_coeq_algebra
      : hit_algebra_one_types coeq_signature.
    Proof.
      use make_algebra.
      - exact make_coeq_path_algebra.
      - exact make_coeq_is_algebra.
    Defined.
  End CoeqAlgebraBuilder.

  (** Projections for the 1-cells *)
  Section CoeqMapProjections.
    Context {X Y : hit_algebra_one_types coeq_signature}
            (φ : X --> Y).

    Definition coeq_map
      : alg_carrier X → alg_carrier Y
      := pr111 φ.

    Definition coeq_map_base
               (b : B)
      : coeq_map (coeq_base X b) = coeq_base Y b
      := pr1 (pr211 φ) b.    
  End CoeqMapProjections.

  (** Builder for the 1-cells *)
  Section CoeqMapBuilder.
    Context {X Y : hit_algebra_one_types coeq_signature}
            (φ : alg_carrier X → alg_carrier Y)
            (φ_base : ∏ (b : B), φ (coeq_base X b) = coeq_base Y b)
            (φ_loop : ∏ (a : A),
                      maponpaths φ (coeq_loop X a) @ φ_base (g a)
                      =
                      φ_base (f a) @ coeq_loop Y a).
    
    Definition make_coeq_map
      : X --> Y.
    Proof.
      use make_algebra_map.
      use make_hit_path_alg_map.
      - use make_hit_prealgebra_mor.
        + exact φ.
        + exact φ_base.
      - intros j a.
        induction j.
        refine (path_assoc _ _ _ @ _).
        refine (pathscomp0rid _ @ _).
        refine (_ @ maponpaths (λ x, x @ (pr21 Y) tt a) (!(pathscomp0rid _))).
        exact (φ_loop a).
    Defined.
  End CoeqMapBuilder.
  
  (** Projections for the 2-cells *)
  Section CoeqCellProjections.
  End CoeqCellProjections.

  (** Builder for the 2-cells *)
  Section CoeqCellBuilder.

  End CoeqCellBuilder.
  
  (** Coeq induction *)
  Section CoeqInduction.
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

  (** The coequalizer *)
  Definition circle
    := pr1 (hit_existence circle_signature).

  (** Mapping principle for coequalizer *)
