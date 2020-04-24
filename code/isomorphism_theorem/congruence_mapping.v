(** Congruence relation of algebras *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.whiskering.

Require Import UniMath.Bicategories.Core.Bicat.
Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Examples.Groupoids.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
Require Import UniMath.Bicategories.PseudoFunctors.Biadjunction.
Require Import UniMath.Bicategories.Colimits.Initial.

Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import hit_biadjunction.path_groupoid_commute.
Require Import hit_biadjunction.hit_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_path_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.
Require Import existence.initial_algebra.
Require Import isomorphism_theorem.congruence_relation.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.



Definition poly_rel_to_eq_fun
           {P : poly_code}
           {X Y : UU}
           {f : X → Y}
           {R : X → X → UU}
           (fR : ∏ (a b : X), R a b → f a = f b)
           {x y : poly_act P X}
           (p : poly_act_rel P R x y)
  : poly_map P f x = poly_map P f y.
Proof.
  induction P as [ T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact p.
  - exact (fR _ _ p).
  - induction x as [x | x], y as [y | y] ; simpl in *.
    + exact (maponpaths inl (IHP₁ x y p)).
    + exact (fromempty p).
    + exact (fromempty p).
    + exact (maponpaths inr (IHP₂ x y p)).
  - exact (pathsdirprod (IHP₁ _ _ (pr1 p)) (IHP₂ _ _ (pr2 p))).
Defined.

(** Mapping principle for the quotient *)
Section MapToQuotientFromCongruence.
  Context {Σ : hit_signature}
          {X : hit_algebra_one_types Σ}
          (R : congruence_relation X)
          (Y : hit_algebra_one_types Σ).

  Definition quotient_of_congruence_map
             (F : make_groupoid_algebra R
                  -->
                  hit_algebra_biadjunction Σ Y)
    : quotient_of_congruence R --> Y
    := biadj_left_hom
         (hit_algebra_biadjunction Σ)
         (make_groupoid_algebra R)
         Y
         F.

  Variable (f : X --> Y)
           (fR : ∏ (a b : alg_carrier X),
                 cong_rel_carrier R a b
                 →
                 alg_map_carrier f a = alg_map_carrier f b)
           (fRid : ∏ (a : alg_carrier X),
                   fR a a (cong_rel_id R a)
                   =
                   idpath _)
           (fRcomp : ∏ (a₁ a₂ a₃ : alg_carrier X)
                       (g₁ : cong_rel_carrier R a₁ a₂)
                       (g₂ : cong_rel_carrier R a₂ a₃),
                     fR a₁ a₃ (cong_rel_comp R g₁ g₂)
                     =
                     fR a₁ a₂ g₁ @ fR a₂ a₃ g₂).
  
  Definition factor_through_gquot_grpd_data
    : functor_data
        (alg_carrier_grpd (make_groupoid_algebra R))
        (alg_carrier_grpd (hit_algebra_biadjunction Σ Y)).
  Proof.
    use make_functor_data.
    - exact (alg_map_carrier f).
    - exact fR.
  Defined.

  Definition factor_through_gquot_grpd_is_functor
    : is_functor factor_through_gquot_grpd_data.
  Proof.
    split.
    - exact fRid.
    - exact fRcomp.
  Qed.
  
  Definition factor_through_gquot_grpd_carrier
    : alg_carrier_grpd (make_groupoid_algebra R)
      ⟶
      alg_carrier_grpd (hit_algebra_biadjunction Σ Y).
  Proof.
    use make_functor.
    - exact factor_through_gquot_grpd_data.
    - exact factor_through_gquot_grpd_is_functor.
  Defined.

  Definition factor_through_gquot_grpd_op_data
    : nat_trans_data
        (prealg_constr_grpd (pr11 (make_groupoid_algebra R))
         ∙ factor_through_gquot_grpd_carrier)
        (# ⦃ point_constr Σ ⦄ factor_through_gquot_grpd_carrier
         ∙ prealg_constr_grpd (pr11 (hit_algebra_biadjunction Σ Y))).
  Proof.
    intro x ; cbn.
    refine (alg_map_commute f x @ _).
    refine (maponpaths (alg_constr Y) _).
    refine (!_).
    apply poly_path_groupoid_is_id.
  Defined.

  Definition yolo
             {P : poly_code}
             {x y : poly_act P (alg_carrier X)}
             (p : poly_act_rel P (R) x y)
    : UU.
             poly_rel_to_eq_fun fR p @
  ! poly_path_groupoid_is_id (poly_map (point_constr Σ) (alg_map_carrier f) y) =
  ! poly_path_groupoid_is_id (poly_map (point_constr Σ) (alg_map_carrier f) x) @
  # (poly_path_groupoid (point_constr Σ) (pr111 Y))
    (poly_act_functor_morphisms (point_constr Σ) factor_through_gquot_grpd_carrier p)

  
  Definition factor_through_gquot_grpd_op_is_nat_trans
    : is_nat_trans _ _ factor_through_gquot_grpd_op_data.
  Proof.
    intros x y p ; cbn ; unfold factor_through_gquot_grpd_op_data.
    refine (!_).
    refine (!(path_assoc _ _ _) @ _).
    etrans.
    {
      apply maponpaths.
      exact (!(maponpathscomp0 (alg_constr Y) _ _)).
    }
    cbn in p.
    unfold poly_act_morphism in p.
    unfold precategory_morphisms in p.
    pose (q := p : poly_act_rel (point_constr Σ) (cong_rel_carrier R) x y).

    assert (fR (alg_constr X x) (alg_constr X y) (cong_rel_ops R x y p)
            @ alg_map_commute f y
            =
            alg_map_commute f x
            @ maponpaths (alg_constr Y) (poly_rel_to_eq_fun fR p))
      as H.
    {
      apply TODO.
    }
    refine (!_).
    etrans.
    {
      refine (path_assoc _ _ _ @ _).
      apply maponpaths_2.
      exact H.
    }
    refine (!(path_assoc _ _ _) @ _).
    apply maponpaths.
    refine (!(maponpathscomp0 (alg_constr Y) _ _) @ _).
    apply maponpaths.
    simpl in x, y.
    apply TODO.
  Qed.
      
  Definition factor_through_gquot_grpd_op
    : prealg_constr_grpd (pr11 (make_groupoid_algebra R))
      ∙ factor_through_gquot_grpd_carrier
      ⟹
      # ⦃ point_constr Σ ⦄ factor_through_gquot_grpd_carrier
      ∙ prealg_constr_grpd (pr11 (hit_algebra_biadjunction Σ Y)).
  Proof.
    use make_nat_trans.
    - exact factor_through_gquot_grpd_op_data.
    - exact factor_through_gquot_grpd_op_is_nat_trans.
  Defined.

  Definition factor_through_gquot_grpd_prealg
    : pr11 (make_groupoid_algebra R)
      -->
      pr11 (hit_algebra_biadjunction Σ Y).
  Proof.
    use make_hit_prealgebra_mor.
    - exact factor_through_gquot_grpd_carrier.
    - exact factor_through_gquot_grpd_op.
  Defined.

  Definition factor_through_gquot_grpd
    : make_groupoid_algebra R
      -->
      hit_algebra_biadjunction Σ Y.
  Proof.
    use make_algebra_map_grpd.
    use make_hit_path_alg_map_grpd.
    - exact factor_through_gquot_grpd_prealg.
    - apply TODO.
  Defined.

  Definition factor_through_gquot
    : quotient_of_congruence R --> Y.
  Proof.
    use quotient_of_congruence_map.
    exact factor_through_gquot_grpd.
  Defined.
End MapToQuotientFromCongruence.
