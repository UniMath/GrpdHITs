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

Require Import prelude.all.
Require Import signature.hit_signature.
Require Import signature.hit.
Require Import algebra.one_types_polynomials.
Require Import algebra.one_types_endpoints.
Require Import algebra.one_types_homotopies.
Require Import algebra.groupoid_polynomials.
Require Import algebra.groupoid_endpoints.
Require Import algebra.groupoid_homotopies.
Require Import hit_biadjunction.hit_algebra_biadj.lift_gquot.
Require Import hit_biadjunction.hit_algebra_biadj.lift_path_groupoid.
Require Import hit_biadjunction.hit_algebra_biadj.

Local Open Scope cat.

Definition TODO {A : UU} : A.
Admitted.

Section CongruenceRelation.
  Context {Σ : hit_signature}
          (X : hit_algebra_one_types Σ).

  (** Definition of congruence relation *)
  Definition congruence_relation
    : UU.
  Proof.
    apply TODO.
  Defined.

  (** Projections *)
  Section Projections.
    Variable (R : congruence_relation).

    (** Projections involving the carrier (groupoid structure *)
    Section ProjectionsCarrier.

      Definition cong_rel_carrier : alg_carrier X → alg_carrier X → hSet.
      Proof.
        pose R.
        apply TODO.
      Defined.
       
      Definition cong_rel_id
                 (x : alg_carrier X)
        : cong_rel_carrier x x.
      Proof.
        apply TODO.
      Defined.

      Definition eq_to_cong_rel
                 {x y : alg_carrier X}
                 (p : x = y)
        : cong_rel_carrier x y.
      Proof.
        induction p.
        exact (cong_rel_id x).
      Defined.

      Definition cong_rel_inv
                 {x y : alg_carrier X}
                 (r : cong_rel_carrier x y)
        : cong_rel_carrier y x.
      Proof.
        apply TODO.
      Defined.

      Definition cong_rel_comp
                 {x y z : alg_carrier X}
                 (r1 : cong_rel_carrier x y)
                 (r2 : cong_rel_carrier y z)
        : cong_rel_carrier x z.
      Proof.
        apply TODO.
      Defined.

      Definition cong_rel_lid
                 {x y : alg_carrier X}
                 (r : cong_rel_carrier x y)
        : cong_rel_comp (cong_rel_id x) r = r.
      Proof.
        apply TODO.
      Defined.

      Definition cong_rel_rid
                 {x y : alg_carrier X}
                 (r : cong_rel_carrier x y)
        : cong_rel_comp r (cong_rel_id y) = r.
      Proof.
        apply TODO.
      Defined.
      
      Definition cong_rel_assoc
                 {x y z w : alg_carrier X}
                 (r1 : cong_rel_carrier x y)
                 (r2 : cong_rel_carrier y z)
                 (r3 : cong_rel_carrier z w)
        : cong_rel_comp r1 (cong_rel_comp r2 r3)
          = cong_rel_comp (cong_rel_comp r1 r2) r3.
      Proof.
        apply TODO.
      Defined.

      Definition cong_rel_linv
                 {x y : alg_carrier X}
                 (r : cong_rel_carrier x y)
        : cong_rel_comp (cong_rel_inv r) r = cong_rel_id y.
      Proof.
        apply TODO.
      Defined.

      Definition cong_rel_rinv
                 {x y : alg_carrier X}
                 (r : cong_rel_carrier x y)
        : cong_rel_comp r (cong_rel_inv r) = cong_rel_id x.
      Proof.
        apply TODO.
      Defined.
      
    End ProjectionsCarrier.

    (** Projections involving the operation (functor) *)
    Section ProjectionsOperation.

      Definition cong_rel_ops
                 (x y : poly_act (point_constr Σ) (alg_carrier X))
                 (r : poly_act_rel (point_constr Σ) cong_rel_carrier x y)
      : cong_rel_carrier (alg_constr X x) (alg_constr X y).
      Proof.
        apply TODO.
      Defined.

      Definition cong_rel_ops_idax
                 (x : poly_act (point_constr Σ) (alg_carrier X))
        : cong_rel_ops x x (poly_act_rel_identity _ _ cong_rel_id x)
          = cong_rel_id (alg_constr X x).
      Proof.
        apply TODO.
      Qed.

      Definition cong_rel_ops_compax
                 (x y z : poly_act (point_constr Σ) (alg_carrier X))
                 (r1 : poly_act_rel (point_constr Σ) cong_rel_carrier x y)
                 (r2 : poly_act_rel (point_constr Σ) cong_rel_carrier y z)
        : cong_rel_ops
            x z
            (poly_act_rel_comp (point_constr Σ) _ (λ x y z r1 r2, cong_rel_comp r1 r2) r1 r2)
          = cong_rel_comp (cong_rel_ops x y r1) (cong_rel_ops y z r2).
      Proof.
        apply TODO.
      Qed.

    End ProjectionsOperation.

    (** Projections involving the path (natural transformation) *)
    Section ProjectionsPath.
    End ProjectionsPath.

    (** Projections involving the 2-paths (equality) *)
    Section ProjectionsHomot.
    End ProjectionsHomot.
  End Projections.

  Section MakeGroupoidAlgebraFromCongruence.
    Variable (R : congruence_relation).

    Definition make_groupoid_algebra_carrier_precategory_data
      : precategory_data.
    Proof.
      use make_precategory_data.
      - use make_precategory_ob_mor.
        + exact (alg_carrier X).
        + exact (cong_rel_carrier R).
      - exact (cong_rel_id R).
      - exact (@cong_rel_comp R).
    Defined.

    Definition make_groupoid_algebra_carrier_is_precategory
      : is_precategory make_groupoid_algebra_carrier_precategory_data.
    Proof.
      use make_is_precategory.
      - exact (@cong_rel_lid R).
      - exact (@cong_rel_rid R).
      - exact (@cong_rel_assoc R).
      - intros.
        refine (!_).
        apply cong_rel_assoc.
    Qed.
    
    Definition make_groupoid_algebra_carrier_precategory
      : precategory.
    Proof.
      use make_precategory.
      - exact make_groupoid_algebra_carrier_precategory_data.
      - exact make_groupoid_algebra_carrier_is_precategory.
    Defined.

    Definition make_groupoid_algebra_carrier_has_homsets
      : has_homsets make_groupoid_algebra_carrier_precategory.
    Proof.
      intros x y.
      apply (cong_rel_carrier R).
    Qed.
    
    Definition make_groupoid_algebra_carrier_category
      : category.
    Proof.
      use make_category.
      - exact make_groupoid_algebra_carrier_precategory.
      - exact make_groupoid_algebra_carrier_has_homsets.
    Defined.

    Definition make_groupoid_algebra_carrier_is_pregroupoid
      : is_pregroupoid make_groupoid_algebra_carrier_category.
    Proof.
      intros x y f.
      use is_iso_qinv.
      - exact (cong_rel_inv R f).
      - split.
        + exact (cong_rel_rinv R f).
        + exact (cong_rel_linv R f).
    Defined.
    
    Definition make_groupoid_algebra_carrier
      : groupoid.
    Proof.
      use make_groupoid.
      - exact make_groupoid_algebra_carrier_category.
      - exact make_groupoid_algebra_carrier_is_pregroupoid.
    Defined.

    Definition make_groupoid_algebra_operations_functor_data
      : functor_data
          (⦃ point_constr Σ ⦄ make_groupoid_algebra_carrier : groupoid)
          make_groupoid_algebra_carrier.
    Proof.
      use make_functor_data.
      - exact (alg_constr X).
      - exact (cong_rel_ops R).
    Defined.

    Definition make_groupoid_algebra_operations_is_functor
      : is_functor make_groupoid_algebra_operations_functor_data.
    Proof.
      split.
      - exact (cong_rel_ops_idax R).
      - exact (cong_rel_ops_compax R).
    Qed.
    
    Definition make_groupoid_algebra_operations
      : (⦃ point_constr Σ ⦄ make_groupoid_algebra_carrier : groupoid)
        ⟶
        make_groupoid_algebra_carrier.
    Proof.
      use make_functor.
      - exact make_groupoid_algebra_operations_functor_data.
      - exact make_groupoid_algebra_operations_is_functor.
    Defined.

    Definition make_groupoid_prealgebra
      : hit_prealgebra_grpd Σ.
    Proof.
      use make_hit_prealgebra_grpd.
      - exact make_groupoid_algebra_carrier.
      - exact make_groupoid_algebra_operations.
    Defined.

    Definition make_groupoid_path_algebra_nat_trans_data
               (j : path_label Σ)
      : nat_trans_data
          (sem_endpoint_grpd_data_functor (path_left Σ j) make_groupoid_prealgebra)
          (sem_endpoint_grpd_data_functor (path_right Σ j) make_groupoid_prealgebra).
    Proof.
      intro x ; cbn.
      apply eq_to_cong_rel.
      exact (alg_path X j x).
    Defined.

    Definition make_groupoid_path_algebra_is_nat_trans
               (j : path_label Σ)
      : is_nat_trans
          _ _
          (make_groupoid_path_algebra_nat_trans_data j).
    Proof.
      intros x y f.
      simpl ; cbn ; cbn in x, y, f
      ; unfold make_groupoid_path_algebra_nat_trans_data.
      apply TODO.
    Qed.

    Definition make_groupoid_path_algebra_path
               (j : path_label Σ)
      : sem_endpoint_grpd_data_functor
          (path_left Σ j)
          make_groupoid_prealgebra
        ⟹
        sem_endpoint_grpd_data_functor
          (path_right Σ j)
          make_groupoid_prealgebra.
    Proof.
      use make_nat_trans.
      - exact (make_groupoid_path_algebra_nat_trans_data j).
      - exact (make_groupoid_path_algebra_is_nat_trans j).
    Defined.

    Definition make_groupoid_path_algebra
      : hit_path_algebra_grpd Σ.
    Proof.
      use make_hit_path_algebra_grpd.
      - exact make_groupoid_prealgebra.
      - exact make_groupoid_path_algebra_path.
    Defined.

    Definition make_groupoid_algebra_is_hit_algebra
      : is_hit_algebra_grpd Σ make_groupoid_path_algebra.
    Proof.
      intros j x p.
      cbn in p.
      pose (alg_homot X j x) as q.
      cbn.
      cbn in q.
      unfold sem_homot_endpoint_one_types in q.
      unfold sem_homot_endpoint_grpd.
      refine ( _ @ p0 _ @ _).
      apply TODO.
    Qed.
    
    Definition make_groupoid_algebra
      : hit_algebra_grpd Σ.
    Proof.
      use make_algebra_grpd.
      - exact make_groupoid_path_algebra.
      - exact make_groupoid_algebra_is_hit_algebra.
    Defined.
  End MakeGroupoidAlgebraFromCongruence.

  Definition quotient_of_congruence
             (R : congruence_relation)
    : hit_algebra_one_types Σ
    := _ ,, gquot_is_hit_algebra Σ _ (pr2 (make_groupoid_algebra R)).

  Definition quotient_of_congruence_map
             (R : congruence_relation)
             (Y : hit_algebra_one_types Σ)
             (F : make_groupoid_algebra R
                  -->
                  hit_algebra_biadjunction Σ Y)
    : quotient_of_congruence R --> Y
    := biadj_left_hom
         (hit_algebra_biadjunction Σ)
         (make_groupoid_algebra R)
         Y
         F.
  (*
  Definition test
             (R : congruence_relation)
             (Y : hit_algebra_one_types Σ)
    : make_groupoid_algebra R
      -->
      hit_algebra_biadjunction Σ Y.
  Proof.
    use make_algebra_map_grpd.
    use make_hit_path_alg_map_grpd.
    - use make_hit_prealgebra_mor.
      + apply TODO.
      + apply TODO.
    - apply TODO.
  Defined.
   *)
End CongruenceRelation.
